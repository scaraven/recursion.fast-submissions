//! lvm2 W32 G0: the Skip pass's point/product core at K = 16 (SKIP = 3: 38 mixed points per half, 3 lane-products)
//! and K = 32 (SKIP = 2: 10 per half, 4 lane-products by Karatsuba), in one style with 128-bit PCLMULQDQ, over
//! pre-embedded blocks: a dev (v4p tier, no VPCLMULQDQ/GFNI) timing of the clmul-bound core alone.

use std::time::Instant;

use super::bench::Data;
use super::*;

/// The 27 points of `{0, 1, inf}^3` of 8 values (`v[b0 + 2 b1 + 4 b2]`), ternary index `t0 + 3 t1 + 9 t2`; the mixed
/// ones (a digit at infinity) are the 19 that are not binary.
#[inline(always)]
fn ext3(v: &[u64]) -> [u64; 27] {
    // One variable at a time: the value at infinity is the sum of the two others (19 XORs).
    let mut a = [0u64; 12];
    for r in 0..4 {
        a[3 * r] = v[2 * r];
        a[3 * r + 1] = v[2 * r + 1];
        a[3 * r + 2] = v[2 * r] ^ v[2 * r + 1];
    }
    // a[t0 + 3 (b1 + 2 b2)]
    let mut b = [0u64; 18];
    for b2 in 0..2 {
        for t0 in 0..3 {
            let (x, y) = (a[t0 + 3 * (2 * b2)], a[t0 + 3 * (1 + 2 * b2)]);
            b[t0 + 3 * (3 * b2)] = x;
            b[t0 + 3 * (1 + 3 * b2)] = y;
            b[t0 + 3 * (2 + 3 * b2)] = x ^ y;
        }
    }
    // b[t0 + 3 t1 + 9 b2]
    let mut out = [0u64; 27];
    for i in 0..9 {
        out[i] = b[i];
        out[9 + i] = b[9 + i];
        out[18 + i] = b[i] ^ b[9 + i];
    }
    out
}

#[test]
fn ext3_matches_definition() {
    let v: [u64; 8] = std::array::from_fn(|i| 0x1234_5678_9abc_def1u64.rotate_left(7 * i as u32) ^ i as u64);
    let e = ext3(&v);
    for i in 0..27 {
        let d = [i % 3, i / 3 % 3, i / 9];
        let want = (0..8).filter(|&b| (0..3).all(|k| d[k] == 2 || d[k] == (b >> k & 1))).fold(0, |acc, b| acc ^ v[b]);
        assert_eq!(e[i], want);
    }
}

const MIXED3: [usize; 19] = {
    let mut m = [0usize; 19];
    let mut n = 0;
    let mut i = 0;
    while i < 27 {
        if i % 3 == 2 || i / 3 % 3 == 2 || i / 9 == 2 {
            m[n] = i;
            n += 1;
        }
        i += 1;
    }
    m
};

pub struct Pre {
    pub e16: Vec<Vec<u64>>,
    pub e32: Vec<Vec<u64>>,
}

/// K = 16 embeddings (leanVM's RMFE, 24 bits) and K = 32 ones (53 bits) of every block position.
pub fn pre(d: &Data) -> Pre {
    let rm = &crate::lv::keccak_gkr::rmfe::RMFE;
    let e16 = d
        .blocks
        .iter()
        .map(|b| {
            (0..BITS * 32)
                .map(|i| {
                    let (j, q) = (i / 32, i % 32);
                    // W32-P: leanVM's 24-bit RMFE left with the K = 16 protocol; the K16 timing core only needs
                    // 24-bit operands of the same shape
                    rm.embed((b[BLOCK_WORDS * j + q / 4] >> (16 * (q % 4))) as u16 as u32) & 0xff_ffff
                })
                .collect()
        })
        .collect();
    let e32 = d
        .blocks
        .iter()
        .map(|b| (0..BITS * PACKS).map(|i| embed(pack(b, i / PACKS, i % PACKS))).collect())
        .collect();
    Pre { e16, e32 }
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2"))]
mod core_ {
    use core::arch::x86_64::*;

    use super::*;

    #[inline(always)]
    fn x(a: __m128i, b: __m128i) -> __m128i {
        unsafe { _mm_xor_si128(a, b) }
    }

    /// K = 16: 2 halves x 2 groups x 19 points, 2 words a slot.
    #[inline(never)]
    pub fn skip16(e: &[u64], w: &[[u64; 2]], acc: &mut [[__m128i; 2]; 76]) {
        unsafe {
            for a in acc.iter_mut() {
                *a = [_mm_setzero_si128(); 2];
            }
            for r in 0..5 {
                for z in 0..64 {
                    let js = row_positions(r, z);
                    let wv: [__m128i; 5] = std::array::from_fn(|x| _mm_set_epi64x(w[js[x]][1] as i64, w[js[x]][0] as i64));
                    for g in 0..4 {
                        let ex: [[u64; 27]; 5] = std::array::from_fn(|x| ext3(&e[32 * js[x] + 8 * g..][..8]));
                        for (pi, &p) in MIXED3.iter().enumerate() {
                            let s = &mut acc[19 * g + pi];
                            for xx in 0..5 {
                                let (b, c) = (ex[(xx + 1) % 5][p], ex[(xx + 2) % 5][p]);
                                let prod = _mm_clmulepi64_si128::<0x00>(_mm_cvtsi64_si128(b as i64), _mm_cvtsi64_si128(c as i64));
                                s[0] = x(s[0], _mm_clmulepi64_si128::<0x00>(prod, wv[xx]));
                                s[1] = x(s[1], _mm_clmulepi64_si128::<0x10>(prod, wv[xx]));
                            }
                        }
                    }
                }
            }
        }
    }

    /// K = 32: 2 halves x 2 groups x 5 points, Karatsuba (3 words a slot).
    #[inline(never)]
    pub fn skip32(e: &[u64], w: &[[u64; 2]], acc: &mut [[__m128i; 3]; SLOTS]) {
        unsafe {
            for a in acc.iter_mut() {
                *a = [_mm_setzero_si128(); 3];
            }
            for r in 0..5 {
                for z in 0..64 {
                    let js = row_positions(r, z);
                    let wv: [__m128i; 5] = std::array::from_fn(|x| _mm_set_epi64x(w[js[x]][1] as i64, w[js[x]][0] as i64));
                    let ws: [__m128i; 5] = std::array::from_fn(|x| _mm_cvtsi64_si128((w[js[x]][0] ^ w[js[x]][1]) as i64));
                    for g in 0..4 {
                        let ex: [[u64; 5]; 5] = std::array::from_fn(|x| mixed(e[PACKS * js[x] + 4 * g..][..4].try_into().unwrap()));
                        for p in 0..POINTS {
                            let s = &mut acc[5 * g + p];
                            for xx in 0..5 {
                                let (b, c) = (ex[(xx + 1) % 5][p], ex[(xx + 2) % 5][p]);
                                let prod = _mm_clmulepi64_si128::<0x00>(_mm_cvtsi64_si128(b as i64), _mm_cvtsi64_si128(c as i64));
                                let m = x(prod, _mm_unpackhi_epi64(prod, prod));
                                s[0] = x(s[0], _mm_clmulepi64_si128::<0x00>(prod, wv[xx]));
                                s[1] = x(s[1], _mm_clmulepi64_si128::<0x11>(prod, wv[xx]));
                                s[2] = x(s[2], _mm_clmulepi64_si128::<0x00>(m, ws[xx]));
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn get32(s: &[__m128i; 3]) -> [u64; 4] {
        let u = |v: __m128i| -> u128 { unsafe { core::mem::transmute(v) } };
        let (p0, p1, m) = (u(s[0]), u(s[1]), u(s[2]));
        let mid = m ^ p0 ^ p1;
        let lo = p0 ^ (mid << 64);
        let hi = p1 ^ (mid >> 64);
        [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64]
    }

    pub fn zero2() -> [[__m128i; 2]; 76] {
        unsafe { [[_mm_setzero_si128(); 2]; 76] }
    }
    pub fn zero3() -> [[__m128i; 3]; SLOTS] {
        unsafe { [[_mm_setzero_si128(); 3]; SLOTS] }
    }
    pub fn lo(v: __m128i) -> u64 {
        unsafe { _mm_cvtsi128_si64(v) as u64 }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2"))]
pub fn bench(log_n: usize, reps: usize, _which: &str) -> i32 {
    let nb = ((1usize << log_n) / 512).max(1);
    let d = super::bench::data(nb, 0x5732);
    let p = pre(&d);
    let inst = nb * 512 * reps;
    println!("w32 bench (dev core, PCLMULQDQ xmm, pre-embedded): 2^{log_n} instances ({nb} blocks) x {reps} reps, one thread");
    let mut a16 = core_::zero2();
    let t = Instant::now();
    let mut sink = 0;
    for _ in 0..reps {
        for e in &p.e16 {
            core_::skip16(e, &d.w, &mut a16);
            sink ^= core_::lo(a16[0][0]);
        }
    }
    let t16 = t.elapsed().as_secs_f64();
    let mut a32 = core_::zero3();
    let t = Instant::now();
    for _ in 0..reps {
        for e in &p.e32 {
            core_::skip32(e, &d.w, &mut a32);
            sink ^= core_::lo(a32[0][0]);
        }
    }
    let t32 = t.elapsed().as_secs_f64();
    let ns = |t: f64| 1e9 * t / inst as f64;
    println!("K16-S3 core {:8.3} ns/instance-layer", ns(t16));
    println!("W32-S2 core {:8.3} ns/instance-layer  ratio {:.3}  (sink {sink:x})", ns(t32), t32 / t16);
    0
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2"))]
pub fn check(d: &Data, refs_skip: &[[[u64; 4]; SLOTS]]) -> i32 {
    let p = pre(d);
    let mut a = core_::zero3();
    let mut ok = true;
    for (e, r) in p.e32.iter().zip(refs_skip) {
        core_::skip32(e, &d.w, &mut a);
        // slot order of the dev core: 5 g' + p with g' = 2 h + g, the same as 10 h + 5 g + p.
        ok &= (0..SLOTS).all(|i| core_::get32(&a[i]) == r[i]);
    }
    println!("dev skip32 core vs skip_ref: {}", if ok { "OK" } else { "FAIL" });
    i32::from(!ok)
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2")))]
pub fn bench(_: usize, _: usize, _: &str) -> i32 {
    eprintln!("w32: no PCLMULQDQ in this build");
    2
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "sse2")))]
pub fn check(_: &Data, _: &[[[u64; 4]; SLOTS]]) -> i32 {
    0
}
