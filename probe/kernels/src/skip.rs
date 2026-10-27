//! Zerocheck prover, rounds 1 and 2, over bit-packed witness columns (item 4), ported from Flock
//! `crates/flock-core/src/zerocheck/univariate_skip_optimized.rs` (+ `kernels/`),
//! `ntt/inv_table.rs` and `zerocheck/multilinear.rs` (`fold_pair_run`).
//!
//! Round 1 (univariate skip, k_skip = 6, 64-point domain): per 2^13-bit window and per "medium"
//! position (16 per window), 8 rows of 64 bits of `a` and `b` are mapped to their 64 LDE values
//! in GF(2^8) by the collapsed byte table (`InvNttTableByteSingleGf8`), multiplied lane-wise in
//! GF(2^8), accumulated as `sum_k x^k y_k`; `c`'s 64 bytes are bit-transposed; then the convert
//! table (gamma^b phi_8(v), 64 KiB) lifts each lane to GF(2^128) and one product by `eq_lo`
//! accumulates it (`accumulate_convert_with_s_hat_v`: AB plus two C banks, which also yields the
//! ring-switch `s_hat_v` of the c-claim).
//!
//! Variants: `flock-zen3` is what Flock compiles to on a CPU without AVX-512/GFNI (SSE2 table
//! apply, scalar GF(2^8) products, the scalar "branchy" bit transpose, scalar PCLMULQDQ
//! products); `avx2` is the ymm rewrite (bit-serial GF(2^8) products in ymm since there is no
//! GFNI, unpack-based transpose, VPCLMULQDQ-256 products).
//!
//! The tables here are synthetic (random, with Flock's sizes, layouts and F2-linear structure):
//! the kernels' cost does not depend on their values. The two variants are checked against each
//! other on the same tables.
use crate::gf::*;
use crate::{par_for, quick, report, Rng};
use std::arch::x86_64::*;

const N_CHUNKS: usize = 8;
const N_MED: usize = 16;

pub struct Tables {
    t0: Vec<u8>,       // 256 x 64, 64-aligned start at t0_off
    t0_off: usize,
    convert: Vec<F128>, // 16 x 256
    fold: Vec<F128>,    // 8 x 256 (round-2 Lagrange fold table)
}

impl Tables {
    pub fn new(rng: &mut Rng) -> Tables {
        let mut t0 = vec![0u8; 256 * 64 + 63];
        let t0_off = (64 - (t0.as_ptr() as usize & 63)) & 63;
        let cols: Vec<Vec<u8>> = (0..8).map(|_| rng.bytes(64)).collect();
        for w in 1..256usize {
            let low = w & w.wrapping_neg();
            for i in 0..64 {
                t0[t0_off + w * 64 + i] = t0[t0_off + (w ^ low) * 64 + i] ^ cols[low.trailing_zeros() as usize][i];
            }
        }
        let lin = |rng: &mut Rng, tables: usize| {
            let mut v = vec![F128::ZERO; tables * 256];
            for j in 0..tables {
                let g: Vec<F128> = rng.fvec(8);
                for w in 1..256usize {
                    let low = w & w.wrapping_neg();
                    v[j * 256 + w] = v[j * 256 + (w ^ low)] + g[low.trailing_zeros() as usize];
                }
            }
            v
        };
        let convert = lin(rng, 16);
        let fold = lin(rng, 8);
        Tables { t0, t0_off, convert, fold }
    }
    #[inline(always)]
    fn t0p(&self) -> *const u8 {
        unsafe { self.t0.as_ptr().add(self.t0_off) }
    }
}

pub struct Inputs {
    pub m: usize,
    pub a: Vec<u8>,
    pub b: Vec<u8>,
    pub c: Vec<u8>,
    pub eq_lo: Vec<F128>,
    pub eq_hi: Vec<F128>,
    pub n_lo: usize,
}
impl Inputs {
    pub fn new(m: usize, rng: &mut Rng) -> Inputs {
        let n = 1usize << (m - 3);
        let n_outer = m - 13;
        let n_lo = n_outer / 2;
        Inputs {
            m,
            a: rng.bytes(n),
            b: rng.bytes(n),
            c: rng.bytes(n),
            eq_lo: rng.fvec(1 << n_lo),
            eq_hi: rng.fvec(1 << (n_outer - n_lo)),
            n_lo,
        }
    }
}

/// Borrowed round-1 inputs (packed a, b, c; eq split).
pub struct View<'a> {
    pub m: usize,
    pub a: &'a [u8],
    pub b: &'a [u8],
    pub c: &'a [u8],
    pub eq_lo: &'a [F128],
    pub eq_hi: &'a [F128],
    pub n_lo: usize,
}
impl Inputs {
    pub fn view(&self) -> View<'_> {
        View { m: self.m, a: &self.a, b: &self.b, c: &self.c, eq_lo: &self.eq_lo, eq_hi: &self.eq_hi, n_lo: self.n_lo }
    }
}
/// eq split sizes for round 1 at m: (n_lo, n_hi).
pub fn r1_split(m: usize) -> (usize, usize) {
    let n_outer = m - 13;
    (n_outer / 2, n_outer - n_outer / 2)
}

pub type R1 = Vec<F128>; // 3 x 64: res_ab, res_c0, res_c1

// ------------------------------------------------------------ GF(2^8) scalar (Flock software)
#[inline(always)]
fn clmul8(a: u8, b: u8) -> u16 {
    let b16 = b as u16;
    let mut acc = 0u16;
    for i in 0..8 {
        if (a >> i) & 1 != 0 {
            acc ^= b16 << i;
        }
    }
    acc
}
#[inline(always)]
fn gf8_reduce(p: u16) -> u8 {
    let h = p >> 8;
    let t = (p & 0xff) ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4);
    let h2 = t >> 8;
    ((t & 0xff) ^ h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4)) as u8
}

// ------------------------------------------------------------ Flock Zen-3 path
/// `InvNttTableByteSingleGf8::apply_x86_unchecked` (SSE2).
#[inline(always)]
unsafe fn apply_sse(t0: *const u8, bytes: *const u8, out: &mut [u8; 64]) {
    let op = out.as_mut_ptr();
    let row0 = t0.add(*bytes as usize * 64);
    for c in 0..4 {
        _mm_storeu_si128(op.add(c * 16) as *mut __m128i, _mm_loadu_si128(row0.add(c * 16) as *const __m128i));
    }
    for b in 1..8usize {
        let rb = t0.add(*bytes.add(b) as usize * 64);
        for c in 0..4usize {
            let sc = c ^ (b >> 1);
            let mut v = _mm_loadu_si128(rb.add(sc * 16) as *const __m128i);
            if b & 1 != 0 {
                v = _mm_shuffle_epi32::<0x4E>(v);
            }
            let d = op.add(c * 16) as *mut __m128i;
            _mm_storeu_si128(d, _mm_xor_si128(_mm_loadu_si128(d), v));
        }
    }
}

fn bit_transpose_scalar(input: &[u8; 64], output: &mut [u8; 64]) {
    output.fill(0);
    for (bi, &ib) in input.iter().enumerate() {
        let (xs, bc) = (bi / 8, bi % 8);
        for t in 0..8 {
            if (ib >> t) & 1 != 0 {
                output[bc * 8 + t] |= 1u8 << xs;
            }
        }
    }
}

#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn x_hi_flock(t: &Tables, inp: &View, x_hi: usize, res: &mut [F128]) {
    let (mut pab, mut pc0, mut pc1) = ([F128::ZERO; 64], [F128::ZERO; 64], [F128::ZERO; 64]);
    let mut chunk_ab = [[0u8; 64]; N_MED];
    let mut chunk_c = [[0u8; 64]; N_MED];
    let (mut a_col, mut b_col) = ([0u8; 64], [0u8; 64]);
    let t0 = t.t0p();
    for xlo in 0..(1usize << inp.n_lo) {
        let x_outer = xlo | (x_hi << inp.n_lo);
        let base = x_outer << 10;
        for bm in 0..N_MED {
            let bb = base + bm * N_CHUNKS * 8;
            let mut acc = [0u16; 64];
            for k in 0..8 {
                let off = bb + k * N_CHUNKS;
                apply_sse(t0, inp.a.as_ptr().add(off), &mut a_col);
                apply_sse(t0, inp.b.as_ptr().add(off), &mut b_col);
                for lane in 0..64 {
                    let y = gf8_reduce(clmul8(a_col[lane], b_col[lane])) as u16;
                    acc[lane] ^= y << k;
                }
            }
            for lane in 0..64 {
                chunk_ab[bm][lane] = gf8_reduce(acc[lane]);
            }
            let cin: &[u8; 64] = inp.c[bb..bb + 64].try_into().unwrap();
            bit_transpose_scalar(cin, &mut chunk_c[bm]);
        }
        let eq = inp.eq_lo[xlo];
        for lane in 0..64 {
            let (mut cab, mut c0, mut c1) = (F128::ZERO, F128::ZERO, F128::ZERO);
            for bm in 0..N_MED {
                let tb = bm * 256;
                let cv = chunk_c[bm][lane] as usize;
                cab += t.convert[tb + chunk_ab[bm][lane] as usize];
                c0 += t.convert[tb + (cv & 0x55)];
                c1 += t.convert[tb + (cv & 0xaa)];
            }
            pab[lane] += mul_pclmul(cab, eq);
            pc0[lane] += mul_pclmul(c0, eq);
            pc1[lane] += mul_pclmul(c1, eq);
        }
    }
    let eh = inp.eq_hi[x_hi];
    for lane in 0..64 {
        res[lane] += mul_pclmul(eh, pab[lane]);
        res[64 + lane] += mul_pclmul(eh, pc0[lane]);
        res[128 + lane] += mul_pclmul(eh, pc1[lane]);
    }
}

/// Portable variant of the same (development VM only).
fn x_hi_portable(t: &Tables, inp: &View, x_hi: usize, res: &mut [F128]) {
    let (mut pab, mut pc0, mut pc1) = ([F128::ZERO; 64], [F128::ZERO; 64], [F128::ZERO; 64]);
    let mut chunk_ab = [[0u8; 64]; N_MED];
    let mut chunk_c = [[0u8; 64]; N_MED];
    let (mut a_col, mut b_col) = ([0u8; 64], [0u8; 64]);
    let t0 = t.t0p();
    for xlo in 0..(1usize << inp.n_lo) {
        let base = (xlo | (x_hi << inp.n_lo)) << 10;
        for bm in 0..N_MED {
            let bb = base + bm * 64;
            let mut acc = [0u16; 64];
            for k in 0..8 {
                unsafe {
                    apply_sse(t0, inp.a.as_ptr().add(bb + k * 8), &mut a_col);
                    apply_sse(t0, inp.b.as_ptr().add(bb + k * 8), &mut b_col);
                }
                for lane in 0..64 {
                    acc[lane] ^= (gf8_reduce(clmul8(a_col[lane], b_col[lane])) as u16) << k;
                }
            }
            for lane in 0..64 {
                chunk_ab[bm][lane] = gf8_reduce(acc[lane]);
            }
            bit_transpose_scalar(inp.c[bb..bb + 64].try_into().unwrap(), &mut chunk_c[bm]);
        }
        let eq = inp.eq_lo[xlo];
        for lane in 0..64 {
            let (mut cab, mut c0, mut c1) = (F128::ZERO, F128::ZERO, F128::ZERO);
            for bm in 0..N_MED {
                let cv = chunk_c[bm][lane] as usize;
                cab += t.convert[bm * 256 + chunk_ab[bm][lane] as usize];
                c0 += t.convert[bm * 256 + (cv & 0x55)];
                c1 += t.convert[bm * 256 + (cv & 0xaa)];
            }
            pab[lane] += mul_portable(cab, eq);
            pc0[lane] += mul_portable(c0, eq);
            pc1[lane] += mul_portable(c1, eq);
        }
    }
    let eh = inp.eq_hi[x_hi];
    for lane in 0..64 {
        res[lane] += mul_portable(eh, pab[lane]);
        res[64 + lane] += mul_portable(eh, pc0[lane]);
        res[128 + lane] += mul_portable(eh, pc1[lane]);
    }
}

// ------------------------------------------------------------ AVX2 + VPCLMULQDQ-256 path
/// The table apply, 64 output bytes in two ymm (port of `apply_x86_avx512_register_unchecked`).
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn apply_y(t0: *const u8, bytes: *const u8) -> (__m256i, __m256i) {
    let r0 = t0.add(*bytes as usize * 64);
    let mut o0 = _mm256_load_si256(r0 as *const __m256i);
    let mut o1 = _mm256_load_si256(r0.add(32) as *const __m256i);
    macro_rules! step {
        ($b:literal) => {{
            let rb = t0.add(*bytes.add($b) as usize * 64);
            let v0 = _mm256_load_si256(rb as *const __m256i);
            let v1 = _mm256_load_si256(rb.add(32) as *const __m256i);
            // output chunk c (16 B) reads source chunk c ^ (b >> 1); odd b swaps 64-bit halves
            let (s0, s1) = match ($b >> 1, $b & 1) {
                (0, _) => (v0, v1),
                (1, 0) => (_mm256_permute4x64_epi64::<0x4E>(v0), _mm256_permute4x64_epi64::<0x4E>(v1)),
                (1, _) => (_mm256_permute4x64_epi64::<0x1B>(v0), _mm256_permute4x64_epi64::<0x1B>(v1)),
                (2, 0) => (v1, v0),
                (2, _) => (_mm256_shuffle_epi32::<0x4E>(v1), _mm256_shuffle_epi32::<0x4E>(v0)),
                (_, 0) => (_mm256_permute4x64_epi64::<0x4E>(v1), _mm256_permute4x64_epi64::<0x4E>(v0)),
                (_, _) => (_mm256_permute4x64_epi64::<0x1B>(v1), _mm256_permute4x64_epi64::<0x1B>(v0)),
            };
            let (s0, s1) = if $b == 1 { (_mm256_shuffle_epi32::<0x4E>(v0), _mm256_shuffle_epi32::<0x4E>(v1)) } else { (s0, s1) };
            o0 = _mm256_xor_si256(o0, s0);
            o1 = _mm256_xor_si256(o1, s1);
        }};
    }
    step!(1);
    step!(2);
    step!(3);
    step!(4);
    step!(5);
    step!(6);
    step!(7);
    (o0, o1)
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn xtime_y(p: __m256i) -> __m256i {
    let z = _mm256_setzero_si256();
    let m = _mm256_and_si256(_mm256_cmpgt_epi8(z, p), _mm256_set1_epi8(0x1B));
    _mm256_xor_si256(_mm256_add_epi8(p, p), m)
}
/// 32 GF(2^8) products (AES polynomial), bit-serial over b (no GFNI on Zen 3).
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn gf8mul_y(a: __m256i, b: __m256i) -> __m256i {
    let mut bb = b;
    let mut p = _mm256_blendv_epi8(_mm256_setzero_si256(), a, bb);
    for _ in 1..8 {
        bb = _mm256_add_epi8(bb, bb);
        p = xtime_y(p);
        p = _mm256_blendv_epi8(p, _mm256_xor_si256(p, a), bb);
    }
    p
}

/// 64-byte bit transpose (same map as `bit_transpose_64bytes_scalar`): 8x8 byte transpose by
/// unpacks, then the three masked bit-swap rounds (Flock's AVX-512 kernel) on ymm.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn bit_transpose_y(inp: *const u8, out: *mut u8) {
    let x0 = _mm_loadu_si128(inp as *const __m128i);
    let x1 = _mm_loadu_si128(inp.add(16) as *const __m128i);
    let x2 = _mm_loadu_si128(inp.add(32) as *const __m128i);
    let x3 = _mm_loadu_si128(inp.add(48) as *const __m128i);
    let y0 = _mm_unpacklo_epi8(x0, _mm_srli_si128::<8>(x0));
    let y1 = _mm_unpacklo_epi8(x1, _mm_srli_si128::<8>(x1));
    let y2 = _mm_unpacklo_epi8(x2, _mm_srli_si128::<8>(x2));
    let y3 = _mm_unpacklo_epi8(x3, _mm_srli_si128::<8>(x3));
    let z0 = _mm_unpacklo_epi16(y0, y1);
    let z1 = _mm_unpackhi_epi16(y0, y1);
    let z2 = _mm_unpacklo_epi16(y2, y3);
    let z3 = _mm_unpackhi_epi16(y2, y3);
    let o0 = _mm_unpacklo_epi32(z0, z2);
    let o1 = _mm_unpackhi_epi32(z0, z2);
    let o2 = _mm_unpacklo_epi32(z1, z3);
    let o3 = _mm_unpackhi_epi32(z1, z3);
    let mut a = _mm256_set_m128i(o1, o0);
    let mut b = _mm256_set_m128i(o3, o2);
    macro_rules! swap {
        ($v:ident, $s:literal, $m:expr) => {{
            let mask = _mm256_set1_epi64x($m as i64);
            let t = _mm256_and_si256(_mm256_xor_si256($v, _mm256_srli_epi64::<$s>($v)), mask);
            $v = _mm256_xor_si256($v, _mm256_xor_si256(t, _mm256_slli_epi64::<$s>(t)));
        }};
    }
    swap!(a, 7, 0x00AA00AA00AA00AAu64);
    swap!(b, 7, 0x00AA00AA00AA00AAu64);
    swap!(a, 14, 0x0000CCCC0000CCCCu64);
    swap!(b, 14, 0x0000CCCC0000CCCCu64);
    swap!(a, 28, 0x00000000F0F0F0F0u64);
    swap!(b, 28, 0x00000000F0F0F0F0u64);
    _mm256_storeu_si256(out as *mut __m256i, a);
    _mm256_storeu_si256(out.add(32) as *mut __m256i, b);
}

#[repr(C, align(64))]
struct A64([[u8; 64]; N_MED]);

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq,sse4.1")]
unsafe fn x_hi_avx2(t: &Tables, inp: &View, x_hi: usize, res: &mut [F128]) {
    let mut part = [F128::ZERO; 192]; // pab | pc0 | pc1
    let mut chunk_ab = A64([[0u8; 64]; N_MED]);
    let mut chunk_c = A64([[0u8; 64]; N_MED]);
    let t0 = t.t0p();
    let cv = t.convert.as_ptr();
    for xlo in 0..(1usize << inp.n_lo) {
        let base = (xlo | (x_hi << inp.n_lo)) << 10;
        for bm in 0..N_MED {
            let bb = base + bm * 64;
            let (mut s0, mut s1) = (_mm256_setzero_si256(), _mm256_setzero_si256());
            for k in (0..8).rev() {
                let (a0, a1) = apply_y(t0, inp.a.as_ptr().add(bb + k * 8));
                let (b0, b1) = apply_y(t0, inp.b.as_ptr().add(bb + k * 8));
                s0 = _mm256_xor_si256(xtime_y(s0), gf8mul_y(a0, b0));
                s1 = _mm256_xor_si256(xtime_y(s1), gf8mul_y(a1, b1));
            }
            _mm256_store_si256(chunk_ab.0[bm].as_mut_ptr() as *mut __m256i, s0);
            _mm256_store_si256(chunk_ab.0[bm].as_mut_ptr().add(32) as *mut __m256i, s1);
            bit_transpose_y(inp.c.as_ptr().add(bb), chunk_c.0[bm].as_mut_ptr());
        }
        let eq = bcast_y(inp.eq_lo[xlo]);
        let mut lane = 0;
        while lane < 64 {
            let mut acc = [_mm_setzero_si128(); 6];
            for bm in 0..N_MED {
                let tb = cv.add(bm * 256);
                for j in 0..2 {
                    let vab = chunk_ab.0[bm][lane + j] as usize;
                    let vc = chunk_c.0[bm][lane + j] as usize;
                    acc[j] = _mm_xor_si128(acc[j], _mm_load_si128(tb.add(vab) as *const __m128i));
                    acc[2 + j] = _mm_xor_si128(acc[2 + j], _mm_load_si128(tb.add(vc & 0x55) as *const __m128i));
                    acc[4 + j] = _mm_xor_si128(acc[4 + j], _mm_load_si128(tb.add(vc & 0xaa) as *const __m128i));
                }
            }
            for g in 0..3 {
                let v = mul_y(_mm256_set_m128i(acc[2 * g + 1], acc[2 * g]), eq);
                let p = part.as_mut_ptr().add(64 * g + lane);
                st_y(p, _mm256_xor_si256(ld_y(p), v));
            }
            lane += 2;
        }
    }
    let eh = bcast_y(inp.eq_hi[x_hi]);
    let mut i = 0;
    while i < 192 {
        let p = res.as_mut_ptr().add(i);
        st_y(p, _mm256_xor_si256(ld_y(p), mul_y(eh, ld_y(part.as_ptr().add(i)))));
        i += 2;
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum R1Kern {
    Portable,
    FlockZen3,
    Avx2,
}
impl R1Kern {
    fn name(self) -> &'static str {
        match self {
            R1Kern::Portable => "portable",
            R1Kern::FlockZen3 => "flock-zen3(SSE2 apply, scalar F8, scalar transpose, pclmul)",
            R1Kern::Avx2 => "avx2+vpclmul256(ymm apply, bit-serial F8, unpack transpose)",
        }
    }
    fn all(c: Cpu) -> Vec<R1Kern> {
        let mut v = vec![];
        if c.pclmul {
            v.push(R1Kern::FlockZen3);
        } else {
            v.push(R1Kern::Portable);
        }
        if c.ymm {
            v.push(R1Kern::Avx2);
        }
        v
    }
}

pub fn round1(t: &Tables, inp: &View, k: R1Kern, threads: usize) -> R1 {
    round1_lim(t, inp, k, threads, usize::MAX)
}
/// Round 1 over the first `lim` x_hi blocks only (a padded witness: the rest is zero).
pub fn round1_lim(t: &Tables, inp: &View, k: R1Kern, threads: usize, lim: usize) -> R1 {
    let n_hi = inp.m - 13 - inp.n_lo;
    let nx = (1usize << n_hi).min(lim);
    let parts: Vec<std::sync::Mutex<Vec<F128>>> = (0..nx).map(|_| std::sync::Mutex::new(vec![F128::ZERO; 192])).collect();
    par_for(threads, nx, |x| {
        let mut r = parts[x].lock().unwrap();
        match k {
            R1Kern::Portable => x_hi_portable(t, inp, x, &mut r),
            R1Kern::FlockZen3 => unsafe { x_hi_flock(t, inp, x, &mut r) },
            R1Kern::Avx2 => unsafe { x_hi_avx2(t, inp, x, &mut r) },
        }
    });
    let mut out = vec![F128::ZERO; 192];
    for p in parts {
        let p = p.into_inner().unwrap();
        for i in 0..192 {
            out[i] += p[i];
        }
    }
    out
}

// ------------------------------------------------------------ round 2: fused fold at z + message
/// Inputs: the packed rows of a and b (8 bytes = 64 bits per row), `eq_lo` over the low pair
/// bits, `eq_hi` over the rest. Outputs the folded a, b (one F128 per row) and (P(1), P(inf)).
pub struct R2 {
    pub a_out: Vec<F128>,
    pub b_out: Vec<F128>,
    pub p1: F128,
    pub pinf: F128,
}

#[inline(always)]
unsafe fn fold_row(tab: *const F128, row: *const u8) -> F128 {
    let mut acc = F128::ZERO;
    for j in 0..8 {
        acc += *tab.add(j * 256 + *row.add(j) as usize);
    }
    acc
}

pub fn r2_split(m: usize) -> (usize, usize) {
    let pbits = m - 7; // pairs = 2^(m-7)
    let n_lo = pbits.min(10);
    (n_lo, pbits - n_lo)
}

#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn r2_block_flock(tab: &[F128], a: &[u8], b: &[u8], eq_lo: &[F128], hi: usize, n_lo: usize, ao: *mut F128, bo: *mut F128) -> (F128, F128) {
    let tp = tab.as_ptr();
    let (mut p1, mut pi) = ([0u64; 4], [0u64; 4]);
    for lo in 0..(1usize << n_lo) {
        let pair = lo | (hi << n_lo);
        let (x0, x1) = (2 * pair, 2 * pair + 1);
        let a0 = fold_row(tp, a.as_ptr().add(x0 * 8));
        let b0 = fold_row(tp, b.as_ptr().add(x0 * 8));
        let a1 = fold_row(tp, a.as_ptr().add(x1 * 8));
        let b1 = fold_row(tp, b.as_ptr().add(x1 * 8));
        *ao.add(x0) = a0;
        *ao.add(x1) = a1;
        *bo.add(x0) = b0;
        *bo.add(x1) = b1;
        let e = eq_lo[lo];
        let u = mul_unreduced_pclmul(e, mul_pclmul(a1, b1));
        let v = mul_unreduced_pclmul(e, mul_pclmul(a0 + a1, b0 + b1));
        for k in 0..4 {
            p1[k] ^= u[k];
            pi[k] ^= v[k];
        }
    }
    (reduce(p1[0], p1[1], p1[2], p1[3]), reduce(pi[0], pi[1], pi[2], pi[3]))
}

fn r2_block_portable(tab: &[F128], a: &[u8], b: &[u8], eq_lo: &[F128], hi: usize, n_lo: usize, ao: *mut F128, bo: *mut F128) -> (F128, F128) {
    let tp = tab.as_ptr();
    let (mut p1, mut pi) = (F128::ZERO, F128::ZERO);
    for lo in 0..(1usize << n_lo) {
        let pair = lo | (hi << n_lo);
        let (x0, x1) = (2 * pair, 2 * pair + 1);
        unsafe {
            let a0 = fold_row(tp, a.as_ptr().add(x0 * 8));
            let b0 = fold_row(tp, b.as_ptr().add(x0 * 8));
            let a1 = fold_row(tp, a.as_ptr().add(x1 * 8));
            let b1 = fold_row(tp, b.as_ptr().add(x1 * 8));
            *ao.add(x0) = a0;
            *ao.add(x1) = a1;
            *bo.add(x0) = b0;
            *bo.add(x1) = b1;
            p1 += mul_portable(eq_lo[lo], mul_portable(a1, b1));
            pi += mul_portable(eq_lo[lo], mul_portable(a0 + a1, b0 + b1));
        }
    }
    (p1, pi)
}

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq,sse4.1")]
unsafe fn r2_block_ymm(tab: &[F128], a: &[u8], b: &[u8], eq_lo: &[F128], hi: usize, n_lo: usize, ao: *mut F128, bo: *mut F128) -> (F128, F128) {
    let tp = tab.as_ptr();
    let mut w1 = Wide2::zero();
    let mut wi = Wide2::zero();
    let mut lo = 0;
    while lo < (1usize << n_lo) {
        let pair = lo | (hi << n_lo);
        let x0 = 2 * pair; // rows x0..x0+4 = two pairs
        let mut f = [_mm_setzero_si128(); 8]; // a0 a1 a2 a3 b0 b1 b2 b3
        for j in 0..8 {
            let t = tp.add(j * 256);
            for r in 0..4 {
                f[r] = _mm_xor_si128(f[r], _mm_load_si128(t.add(*a.as_ptr().add((x0 + r) * 8 + j) as usize) as *const __m128i));
                f[4 + r] = _mm_xor_si128(f[4 + r], _mm_load_si128(t.add(*b.as_ptr().add((x0 + r) * 8 + j) as usize) as *const __m128i));
            }
        }
        let av01 = _mm256_set_m128i(f[1], f[0]);
        let av23 = _mm256_set_m128i(f[3], f[2]);
        let bv01 = _mm256_set_m128i(f[5], f[4]);
        let bv23 = _mm256_set_m128i(f[7], f[6]);
        st_y(ao.add(x0), av01);
        st_y(ao.add(x0 + 2), av23);
        st_y(bo.add(x0), bv01);
        st_y(bo.add(x0 + 2), bv23);
        let a1 = _mm256_set_m128i(f[3], f[1]);
        let b1 = _mm256_set_m128i(f[7], f[5]);
        let as_ = _mm256_set_m128i(_mm_xor_si128(f[2], f[3]), _mm_xor_si128(f[0], f[1]));
        let bs_ = _mm256_set_m128i(_mm_xor_si128(f[6], f[7]), _mm_xor_si128(f[4], f[5]));
        let eq = ld_y(eq_lo.as_ptr().add(lo));
        w1.mac(eq, mul_y(a1, b1));
        wi.mac(eq, mul_y(as_, bs_));
        lo += 2;
    }
    (w1.reduce_sum(), wi.reduce_sum())
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum R2Kern {
    Portable,
    FlockZen3,
    Ymm,
}

pub fn round2(t: &Tables, m: usize, a: &[u8], b: &[u8], eq_lo: &[F128], eq_hi: &[F128], k: R2Kern, threads: usize, out: &mut R2) {
    round2_lim(t, m, a, b, eq_lo, eq_hi, k, threads, out, usize::MAX)
}
pub fn round2_lim(t: &Tables, m: usize, a: &[u8], b: &[u8], eq_lo: &[F128], eq_hi: &[F128], k: R2Kern, threads: usize, out: &mut R2, lim: usize) {
    let (n_lo, n_hi0) = r2_split(m);
    let nh = (1usize << n_hi0).min(lim);
    let ao = crate::SyncPtr(out.a_out.as_mut_ptr());
    let bo = crate::SyncPtr(out.b_out.as_mut_ptr());
    let res: Vec<std::sync::Mutex<(F128, F128)>> = (0..nh).map(|_| std::sync::Mutex::new((F128::ZERO, F128::ZERO))).collect();
    par_for(threads, nh, |hi| {
        let (ao, bo) = (ao, bo);
        let (p1, pi) = match k {
            R2Kern::Portable => r2_block_portable(&t.fold, a, b, eq_lo, hi, n_lo, ao.0, bo.0),
            R2Kern::FlockZen3 => unsafe { r2_block_flock(&t.fold, a, b, eq_lo, hi, n_lo, ao.0, bo.0) },
            R2Kern::Ymm => unsafe { r2_block_ymm(&t.fold, a, b, eq_lo, hi, n_lo, ao.0, bo.0) },
        };
        *res[hi].lock().unwrap() = (mul(eq_hi[hi], p1), mul(eq_hi[hi], pi));
    });
    out.p1 = F128::ZERO;
    out.pinf = F128::ZERO;
    for r in res {
        let (x, y) = r.into_inner().unwrap();
        out.p1 += x;
        out.pinf += y;
    }
}

pub fn selftest(c: Cpu, rng: &mut Rng) -> Result<(), String> {
    let t = Tables::new(rng);
    let inp = Inputs::new(17, rng);
    let reference = round1(&t, &inp.view(), R1Kern::Portable, 1);
    for k in R1Kern::all(c) {
        for th in [1, 3] {
            if round1(&t, &inp.view(), k, th) != reference {
                return Err(format!("round1 {} mismatch (threads {th})", k.name()));
            }
        }
    }
    // transpose check against the scalar map
    if c.ymm {
        let x: [u8; 64] = rng.bytes(64).try_into().unwrap();
        let mut o1 = [0u8; 64];
        let mut o2 = [0u8; 64];
        bit_transpose_scalar(&x, &mut o1);
        unsafe { bit_transpose_y(x.as_ptr(), o2.as_mut_ptr()) };
        if o1 != o2 {
            return Err("bit transpose mismatch".into());
        }
    }
    let m = 15;
    let rows = 1usize << (m - 6);
    let (n_lo, n_hi) = r2_split(m);
    let (eq_lo, eq_hi) = (rng.fvec(1 << n_lo), rng.fvec(1 << n_hi));
    let mut r_ref = R2 { a_out: vec![F128::ZERO; rows], b_out: vec![F128::ZERO; rows], p1: F128::ZERO, pinf: F128::ZERO };
    round2(&t, m, &inp.a, &inp.b, &eq_lo, &eq_hi, R2Kern::Portable, 1, &mut r_ref);
    let mut ks = vec![];
    if c.pclmul {
        ks.push(R2Kern::FlockZen3);
    }
    if c.ymm {
        ks.push(R2Kern::Ymm);
    }
    for k in ks {
        let mut r = R2 { a_out: vec![F128::ZERO; rows], b_out: vec![F128::ZERO; rows], p1: F128::ZERO, pinf: F128::ZERO };
        round2(&t, m, &inp.a, &inp.b, &eq_lo, &eq_hi, k, 3, &mut r);
        if r.a_out != r_ref.a_out || r.b_out != r_ref.b_out || r.p1 != r_ref.p1 || r.pinf != r_ref.pinf {
            return Err(format!("round2 {k:?} mismatch"));
        }
    }
    Ok(())
}

pub fn bench(c: Cpu, threads: &[usize]) {
    let mut rng = Rng(11);
    let t = Tables::new(&mut rng);
    let m = if quick() { 18 } else { 24 }; // 2^(m-14) compressions
    let inp = Inputs::new(m, &mut rng);
    let comps = (1usize << (m - 14)) as f64;
    for k in R1Kern::all(c) {
        for &th in threads {
            let secs = crate::best(3, || {
                std::hint::black_box(round1(&t, &inp.view(), k, th));
            });
            report("zerocheck-round1-skip", k.name(), th, &format!("m={m}"), comps, secs, "compression");
        }
    }
    let rows = 1usize << (m - 6);
    let (n_lo, n_hi) = r2_split(m);
    let (eq_lo, eq_hi) = (rng.fvec(1 << n_lo), rng.fvec(1 << n_hi));
    let mut out = R2 { a_out: vec![F128::ZERO; rows], b_out: vec![F128::ZERO; rows], p1: F128::ZERO, pinf: F128::ZERO };
    let mut ks = vec![];
    if c.pclmul {
        ks.push((R2Kern::FlockZen3, "flock-zen3(scalar fold, pclmul, F256Unreduced)"));
    } else {
        ks.push((R2Kern::Portable, "portable"));
    }
    if c.ymm {
        ks.push((R2Kern::Ymm, "ymm-vpclmul(fold 2 pairs, Wide2 MAC)"));
    }
    for (k, name) in ks {
        for &th in threads {
            let secs = crate::best(3, || round2(&t, m, &inp.a, &inp.b, &eq_lo, &eq_hi, k, th, &mut out));
            report("zerocheck-round2-fold+msg", name, th, &format!("m={m}"), comps, secs, "compression");
        }
    }
}
