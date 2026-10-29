//! Hot-loop kernels with run-time tier dispatch (B-9, blueprint §8.2):
//!
//! * tier 2 — portable (4-bit-window carry-less products) or scalar `pclmulqdq` (`field.rs`): the
//!   reference;
//! * tier 1 — AVX2 + VPCLMULQDQ-256 (`ymm`): two F elements per register; the F product is
//!   Karatsuba over the 64-bit limbs (3 carry-less products), `c₀ = p₀ + β·red(p₁)` with
//!   `β = x^63` as a shift pair, and one carry-less product per 128 → 64-bit reduction (the
//!   overflow of ≤ 4 bits folded by shifts);
//! * `ymm-sim` — the same kernel bodies with the 256-bit carry-less product emulated by two
//!   128-bit `pclmulqdq` (for testing the tier-1 code on a CPU without VPCLMULQDQ, e.g. under
//!   `qemu-x86_64 -cpu max`); never chosen automatically.
//!
//! The round-1 window kernel (AVX2 only: table apply, bit-serial GF(2^8) products, unpack
//! transpose) is a port of the phase-0 probe's `x_hi_avx2` (`probe/kernels/src/skip.rs`, itself
//! the ymm rewrite of Flock's `apply_x86_avx512_register_unchecked` / `bit_transpose_64bytes`;
//! MIT/Apache-2.0, `../LICENSE-flock`), with the GF(2^8) reduction constant of A.1's field.
//! `FLOCK_TIER=portable|pclmul|ymm|ymm-sim` forces a tier.

use crate::field::{FAcc, B64, F};
use std::sync::atomic::{AtomicU8, Ordering};

static TIER: AtomicU8 = AtomicU8::new(0); // 0 undecided, 1 portable, 2 pclmul, 3 ymm, 4 ymm-sim

pub fn hw_ymm() -> bool {
    std::arch::is_x86_feature_detected!("avx2")
        && std::arch::is_x86_feature_detected!("vpclmulqdq")
        && std::arch::is_x86_feature_detected!("pclmulqdq")
        && std::arch::is_x86_feature_detected!("sse4.1")
}
pub fn hw_avx2() -> bool {
    std::arch::is_x86_feature_detected!("avx2")
}

#[cold]
fn init_tier() -> u8 {
    let want = std::env::var("FLOCK_TIER").unwrap_or_default();
    let t = match want.as_str() {
        "portable" => 1,
        "pclmul" if crate::field::hw_pclmul() => 2,
        "ymm" if hw_ymm() => 3,
        "ymm-sim" if crate::field::hw_pclmul() && hw_avx2() => 4,
        _ => {
            if hw_ymm() {
                3
            } else if crate::field::hw_pclmul() {
                2
            } else {
                1
            }
        }
    };
    crate::field::set_pclmul(t >= 2);
    TIER.store(t, Ordering::Relaxed);
    t
}

#[inline(always)]
pub fn tier() -> u8 {
    match TIER.load(Ordering::Relaxed) {
        0 => init_tier(),
        t => t,
    }
}
pub fn set_tier(t: u8) {
    crate::field::set_pclmul(t >= 2);
    TIER.store(t, Ordering::Relaxed);
}

pub fn tier_name() -> &'static str {
    match tier() {
        1 => "portable",
        2 => "pclmul",
        3 => "ymm",
        _ => "ymm-sim",
    }
}

// ---------------------------------------------------------------- dispatched kernels

/// `top[i] += bot[i]·t; bot[i] += top[i]` (the additive-NTT butterfly).
pub fn butterfly(top: &mut [F], bot: &mut [F], t: B64) {
    match tier() {
        3 => unsafe { ymm::butterfly(top, bot, t) },
        4 => unsafe { ymm_sim::butterfly(top, bot, t) },
        _ => butterfly_ref(top, bot, t),
    }
}
pub fn butterfly_ref(top: &mut [F], bot: &mut [F], t: B64) {
    for (a, b) in top.iter_mut().zip(bot.iter_mut()) {
        let u = *a + b.mulb(t);
        *a = u;
        *b = *b + u;
    }
}

/// `out[i] = t[2i] + s (t[2i] + t[2i+1])`.
pub fn fold(t: &[F], s: F, out: &mut [F]) {
    match tier() {
        3 => unsafe { ymm::fold(t, s, out) },
        4 => unsafe { ymm_sim::fold(t, s, out) },
        _ => fold_ref(t, s, out),
    }
}
pub fn fold_ref(t: &[F], s: F, out: &mut [F]) {
    for (i, o) in out.iter_mut().enumerate() {
        *o = t[2 * i] + s * (t[2 * i] + t[2 * i + 1]);
    }
}

/// `(Σ_l lo[l] a(2l+1) b(2l+1), Σ_l lo[l] (a(2l)+a(2l+1)) (b(2l)+b(2l+1)))`.
pub fn zc_inner(a: &[F], b: &[F], lo: &[F]) -> (F, F) {
    match tier() {
        3 => unsafe { ymm::zc_inner(a, b, lo) },
        4 => unsafe { ymm_sim::zc_inner(a, b, lo) },
        _ => zc_inner_ref(a, b, lo),
    }
}
pub fn zc_inner_ref(a: &[F], b: &[F], lo: &[F]) -> (F, F) {
    let (mut i1, mut ii) = (FAcc::default(), FAcc::default());
    for l in 0..lo.len() {
        let (a0, a1, b0, b1) = (a[2 * l], a[2 * l + 1], b[2 * l], b[2 * l + 1]);
        i1.mac(lo[l], a1 * b1);
        ii.mac(lo[l], (a0 + a1) * (b0 + b1));
    }
    (i1.reduce(), ii.reduce())
}

/// `Σ_i a[i] b[i]`.
pub fn dot(a: &[F], b: &[F]) -> F {
    match tier() {
        3 => unsafe { ymm::dot(a, b) },
        4 => unsafe { ymm_sim::dot(a, b) },
        _ => {
            let mut acc = FAcc::default();
            for (x, y) in a.iter().zip(b.iter()) {
                acc.mac(*x, *y);
            }
            acc.reduce()
        }
    }
}

/// K-fold `out[i] = t[2i] + s (t[2i] + t[2i+1])`.
pub fn kfold(t: &[crate::field::K], s: crate::field::K, out: &mut [crate::field::K]) {
    match tier() {
        3 => unsafe { ymm::kfold(t, s, out) },
        4 => unsafe { ymm_sim::kfold(t, s, out) },
        _ => {
            for (i, o) in out.iter_mut().enumerate() {
                *o = t[2 * i] + s * (t[2 * i] + t[2 * i + 1]);
            }
        }
    }
}
/// `out[i] = g[2i] + s (g[2i] + g[2i+1])` from F values.
pub fn kfold_f(g: &[F], s: crate::field::K, out: &mut [crate::field::K]) {
    match tier() {
        3 => unsafe { ymm::kfold_f(g, s, out) },
        4 => unsafe { ymm_sim::kfold_f(g, s, out) },
        _ => {
            for (i, o) in out.iter_mut().enumerate() {
                *o = crate::field::K::f(g[2 * i]) + s.mulf(g[2 * i] + g[2 * i + 1]);
            }
        }
    }
}
pub fn round_kk(w: &[crate::field::K], g: &[crate::field::K]) -> [crate::field::K; 3] {
    match tier() {
        3 => unsafe { ymm::round_kk(w, g) },
        4 => unsafe { ymm_sim::round_kk(w, g) },
        _ => {
            let mut r = [crate::field::K::ZERO; 3];
            for i in 0..w.len() / 2 {
                let (w0, w1, g0, g1) = (w[2 * i], w[2 * i + 1], g[2 * i], g[2 * i + 1]);
                r[0] += w0 * g0;
                r[1] += w1 * g1;
                r[2] += (w0 + w1) * (g0 + g1);
            }
            r
        }
    }
}
pub fn round_kf(w: &[crate::field::K], g: &[F]) -> [crate::field::K; 3] {
    match tier() {
        3 => unsafe { ymm::round_kf(w, g) },
        4 => unsafe { ymm_sim::round_kf(w, g) },
        _ => {
            let mut a = [crate::field::KAcc::default(); 3];
            for i in 0..w.len() / 2 {
                let (w0, w1, g0, g1) = (w[2 * i], w[2 * i + 1], g[2 * i], g[2 * i + 1]);
                a[0].mac_f(w0, g0);
                a[1].mac_f(w1, g1);
                a[2].mac_f(w0 + w1, g0 + g1);
            }
            [a[0].reduce(), a[1].reduce(), a[2].reduce()]
        }
    }
}
pub fn round_ff(w: &[F], g: &[F]) -> [F; 3] {
    match tier() {
        3 => unsafe { ymm::round_ff(w, g) },
        4 => unsafe { ymm_sim::round_ff(w, g) },
        _ => {
            let mut a = [FAcc::default(); 3];
            for i in 0..w.len() / 2 {
                let (w0, w1, g0, g1) = (w[2 * i], w[2 * i + 1], g[2 * i], g[2 * i + 1]);
                a[0].mac(w0, g0);
                a[1].mac(w1, g1);
                a[2].mac(w0 + w1, g0 + g1);
            }
            [a[0].reduce(), a[1].reduce(), a[2].reduce()]
        }
    }
}

/// The x₆ zerocheck round from bits (`zerocheck::round_x6`'s inner loop).
pub fn x6_inner(t: &[F], a: &[u8], b: &[u8], p0: usize, w: &[F]) -> (F, F) {
    match tier() {
        3 => unsafe { ymm::x6_inner(t, a, b, p0, w) },
        4 => unsafe { ymm_sim::x6_inner(t, a, b, p0, w) },
        _ => {
            let fr = crate::zerocheck::fold_row;
            let (mut i1, mut ii) = (FAcc::default(), FAcc::default());
            for (l, wl) in w.iter().enumerate() {
                let p = p0 + l;
                let (x0, x1) = (16 * p, 16 * p + 8);
                let (a0, a1, b0, b1) = (fr(t, &a[x0..x0 + 8]), fr(t, &a[x1..x1 + 8]), fr(t, &b[x0..x0 + 8]), fr(t, &b[x1..x1 + 8]));
                i1.mac(*wl, a1 * b1);
                ii.mac(*wl, (a0 + a1) * (b0 + b1));
            }
            (i1.reduce(), ii.reduce())
        }
    }
}
pub fn x6_fold(t: &[F], a: &[u8], p0: usize, s: F, out: &mut [F]) {
    match tier() {
        3 => unsafe { ymm::x6_fold(t, a, p0, s, out) },
        4 => unsafe { ymm_sim::x6_fold(t, a, p0, s, out) },
        _ => {
            let fr = crate::zerocheck::fold_row;
            for (i, o) in out.iter_mut().enumerate() {
                let p = p0 + i;
                let (x0, x1) = (fr(t, &a[16 * p..16 * p + 8]), fr(t, &a[16 * p + 8..16 * p + 16]));
                *o = x0 + s * (x0 + x1);
            }
        }
    }
}

/// `acc[i] += x[i]·c` (also `out = x·c` on a zeroed `acc`).
pub fn axpy(acc: &mut [F], x: &[F], c: F) {
    match tier() {
        3 => unsafe { ymm::axpy(acc, x, c) },
        4 => unsafe { ymm_sim::axpy(acc, x, c) },
        _ => {
            for (a, y) in acc.iter_mut().zip(x.iter()) {
                *a += *y * c;
            }
        }
    }
}

/// `acc[l] ^= (c.lo ⊗ x_l, c.hi ⊗ x_l)` unreduced (the consistency-weight accumulation).
pub fn xmac(acc: &mut [[u128; 2]], x: &[B64], c: F) {
    match tier() {
        3 => unsafe { ymm::xmac(acc, x, c) },
        4 => unsafe { ymm_sim::xmac(acc, x, c) },
        _ => {
            for (a, xl) in acc.iter_mut().zip(x.iter()) {
                a[0] ^= crate::field::clmul(c.lo, xl.0);
                a[1] ^= crate::field::clmul(c.hi, xl.0);
            }
        }
    }
}

/// `out[i] += phi_apply(t, e[i])` (pass 6; `ringswitch::weight_table`).
pub fn phi_add(t: &[F], e: &[F], out: &mut [F]) {
    if tier() >= 3 {
        unsafe { r1::phi_add(t, e, out) }
    } else {
        for (o, x) in out.iter_mut().zip(e) {
            *o += crate::ringswitch::phi_apply(t, *x);
        }
    }
}

/// `out[l] += phi_apply(t, e[l])` for `l ∈ idx` (distinct indices).
pub fn phi_add_idx(t: &[F], e: &[F], idx: &[u32], out: &mut [F]) {
    assert!(idx.iter().all(|&l| (l as usize) < e.len().min(out.len())));
    if tier() >= 3 {
        unsafe { r1::phi_add_idx(t, e, idx, out) }
    } else {
        for &l in idx {
            out[l as usize] += crate::ringswitch::phi_apply(t, e[l as usize]);
        }
    }
}

/// `row[i] ^= Σ_p q[offs[p] + i]` for `i < row.len()` (`ringswitch::weight_table_rows`).
pub fn xor_rows(q: &[F], offs: &[usize; 16], row: &mut [F]) {
    let n = row.len();
    assert!(offs.iter().all(|&o| o + n <= q.len()));
    if tier() >= 3 {
        unsafe { r1::xor_rows(q, offs, row) }
    } else {
        for (i, r) in row.iter_mut().enumerate() {
            let mut a = q[offs[0] + i];
            for o in &offs[1..] {
                a += q[o + i];
            }
            *r += a;
        }
    }
}

/// One 8-block stripe of `lincheck::partial_fold`: `acc[64 wi + j] += t[Σ_r 2^r · bit j of
/// z[r·256 + wi]]`.
pub fn pf_stripe(z: &[u64], t: &[F; 256], acc: &mut [F]) {
    if tier() >= 3 {
        unsafe { r1::pf_stripe(z, t, acc) }
    } else {
        pf_stripe_ref(z, t, acc)
    }
}

pub fn pf_stripe_ref(z: &[u64], t: &[F; 256], acc: &mut [F]) {
    for wi in 0..256 {
        for byte in 0..8 {
            let mut x = 0u64;
            for r in 0..8 {
                x |= ((z[r * 256 + wi] >> (8 * byte)) & 0xFF) << (8 * r);
            }
            let y = crate::lincheck::transpose8(x);
            let p = wi * 64 + byte * 8;
            for tt in 0..8 {
                acc[p + tt] += t[((y >> (8 * tt)) & 0xFF) as usize];
            }
        }
    }
}

/// One round-1 window (`zerocheck::window_portable` is the reference).
pub fn round1_window(sk: &crate::skipdom::Skip, a: &[u8], b: &[u8], z: &[u8], out: &mut [F; 192]) {
    if tier() >= 3 {
        unsafe { r1::window(sk, a, b, z, out) }
    } else {
        crate::zerocheck::window_portable(sk, a, b, z, out)
    }
}

// ---------------------------------------------------------------- the ymm kernels

#[inline]
#[target_feature(enable = "avx2,pclmulqdq,sse4.1")]
unsafe fn clmul_sim<const I: i32>(a: std::arch::x86_64::__m256i, b: std::arch::x86_64::__m256i) -> std::arch::x86_64::__m256i {
    use std::arch::x86_64::*;
    let lo = _mm_clmulepi64_si128::<I>(_mm256_castsi256_si128(a), _mm256_castsi256_si128(b));
    let hi = _mm_clmulepi64_si128::<I>(_mm256_extracti128_si256::<1>(a), _mm256_extracti128_si256::<1>(b));
    _mm256_set_m128i(hi, lo)
}

#[inline]
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq,sse4.1")]
unsafe fn clmul_hw<const I: i32>(a: std::arch::x86_64::__m256i, b: std::arch::x86_64::__m256i) -> std::arch::x86_64::__m256i {
    std::arch::x86_64::_mm256_clmulepi64_epi128::<I>(a, b)
}

macro_rules! ymm_kernels {
    ($m:ident, $feat:literal, $cl:ident) => {
        pub mod $m {
            use super::$cl as cl;
            use crate::field::{B64, F};
            use std::arch::x86_64::*;

            #[inline(always)]
            unsafe fn ld(p: *const F) -> __m256i {
                _mm256_loadu_si256(p as *const __m256i)
            }
            #[inline(always)]
            unsafe fn st(p: *mut F, v: __m256i) {
                _mm256_storeu_si256(p as *mut __m256i, v)
            }
            #[inline(always)]
            unsafe fn bcast(a: F) -> __m256i {
                _mm256_set_epi64x(a.hi as i64, a.lo as i64, a.hi as i64, a.lo as i64)
            }

            /// Reduce the 128-bit value of each lane to its low qword (the high qword is garbage).
            #[inline]
            #[target_feature(enable = $feat)]
            pub unsafe fn red(v: __m256i) -> __m256i {
                let r = _mm256_set_epi64x(0, 0x1B, 0, 0x1B);
                let t = cl::<0x01>(v, r); // v.hi · (x^4 + x^3 + x + 1), ≤ 68 bits
                let th = _mm256_bsrli_epi128::<8>(t);
                let u = _mm256_xor_si256(
                    _mm256_xor_si256(th, _mm256_slli_epi64::<1>(th)),
                    _mm256_xor_si256(_mm256_slli_epi64::<3>(th), _mm256_slli_epi64::<4>(th)),
                );
                _mm256_xor_si256(_mm256_xor_si256(v, t), u)
            }

            /// Two F products: lanes `[x₀ x₁]·[y₀ y₁]`.
            #[inline]
            #[target_feature(enable = $feat)]
            pub unsafe fn mul(x: __m256i, y: __m256i) -> __m256i {
                let p0 = cl::<0x00>(x, y);
                let p1 = cl::<0x11>(x, y);
                let xk = _mm256_xor_si256(x, _mm256_shuffle_epi32::<0x4E>(x));
                let yk = _mm256_xor_si256(y, _mm256_shuffle_epi32::<0x4E>(y));
                let pm = cl::<0x00>(xk, yk);
                let r1 = red(p1);
                // β·r1 = x^63 r1 = (r1 << 63, r1 >> 1) as a 128-bit value
                let b = _mm256_unpacklo_epi64(_mm256_slli_epi64::<63>(r1), _mm256_srli_epi64::<1>(r1));
                let c0 = red(_mm256_xor_si256(p0, b));
                let c1 = red(_mm256_xor_si256(pm, p0));
                _mm256_unpacklo_epi64(c0, c1)
            }

            /// Unreduced accumulator of F products: the per-lane sums of `p₀, p₁, p_m`.
            #[derive(Clone, Copy)]
            pub struct Acc {
                p0: __m256i,
                p1: __m256i,
                pm: __m256i,
            }
            impl Acc {
                #[inline(always)]
                pub unsafe fn zero() -> Acc {
                    Acc { p0: _mm256_setzero_si256(), p1: _mm256_setzero_si256(), pm: _mm256_setzero_si256() }
                }
                #[inline]
                #[target_feature(enable = $feat)]
                pub unsafe fn mac(&mut self, x: __m256i, y: __m256i) {
                    self.p0 = _mm256_xor_si256(self.p0, cl::<0x00>(x, y));
                    self.p1 = _mm256_xor_si256(self.p1, cl::<0x11>(x, y));
                    let xk = _mm256_xor_si256(x, _mm256_shuffle_epi32::<0x4E>(x));
                    let yk = _mm256_xor_si256(y, _mm256_shuffle_epi32::<0x4E>(y));
                    self.pm = _mm256_xor_si256(self.pm, cl::<0x00>(xk, yk));
                }
                /// The sum of both lanes, reduced.
                #[target_feature(enable = $feat)]
                pub unsafe fn sum(&self) -> F {
                    let q = |v: __m256i| -> u128 {
                        let mut w = [0u64; 4];
                        _mm256_storeu_si256(w.as_mut_ptr() as *mut __m256i, v);
                        ((w[1] ^ w[3]) as u128) << 64 | (w[0] ^ w[2]) as u128
                    };
                    let (c0, c1) = crate::field::combine_f(q(self.p0), q(self.p1), q(self.pm));
                    F { lo: c0, hi: c1 }
                }
            }

            #[target_feature(enable = $feat)]
            pub unsafe fn butterfly(top: &mut [F], bot: &mut [F], t: B64) {
                let n = top.len();
                let tv = _mm256_set_epi64x(0, t.0 as i64, 0, t.0 as i64);
                let r = _mm256_set_epi64x(0, 0x1B, 0, 0x1B);
                let mut i = 0;
                while i + 2 <= n {
                    let a = ld(top.as_ptr().add(i));
                    let b = ld(bot.as_ptr().add(i));
                    // b·t per limb: p = b₀t, q = b₁t (128 bits each), reduced together
                    let p = cl::<0x00>(b, tv);
                    let q = cl::<0x01>(b, tv);
                    let h = _mm256_unpackhi_epi64(p, q);
                    let l = _mm256_unpacklo_epi64(p, q);
                    let t1 = cl::<0x00>(h, r);
                    let t2 = cl::<0x01>(h, r);
                    let th = _mm256_unpackhi_epi64(t1, t2);
                    let tl = _mm256_unpacklo_epi64(t1, t2);
                    let u = _mm256_xor_si256(
                        _mm256_xor_si256(th, _mm256_slli_epi64::<1>(th)),
                        _mm256_xor_si256(_mm256_slli_epi64::<3>(th), _mm256_slli_epi64::<4>(th)),
                    );
                    let bt = _mm256_xor_si256(_mm256_xor_si256(l, tl), u);
                    let na = _mm256_xor_si256(a, bt);
                    st(top.as_mut_ptr().add(i), na);
                    st(bot.as_mut_ptr().add(i), _mm256_xor_si256(b, na));
                    i += 2;
                }
                if i < n {
                    super::butterfly_ref(&mut top[i..], &mut bot[i..], t);
                }
            }

            #[target_feature(enable = $feat)]
            pub unsafe fn fold(t: &[F], s: F, out: &mut [F]) {
                let n = out.len();
                let sv = bcast(s);
                let mut i = 0;
                while i + 2 <= n {
                    let x = ld(t.as_ptr().add(2 * i)); // t[2i], t[2i+1]
                    let y = ld(t.as_ptr().add(2 * i + 2)); // t[2i+2], t[2i+3]
                    let e = _mm256_permute2x128_si256::<0x20>(x, y); // t[2i], t[2i+2]
                    let o = _mm256_permute2x128_si256::<0x31>(x, y); // t[2i+1], t[2i+3]
                    let d = _mm256_xor_si256(e, o);
                    st(out.as_mut_ptr().add(i), _mm256_xor_si256(e, mul(d, sv)));
                    i += 2;
                }
                if i < n {
                    out[i] = t[2 * i] + s * (t[2 * i] + t[2 * i + 1]);
                }
            }

            #[target_feature(enable = $feat)]
            pub unsafe fn zc_inner(a: &[F], b: &[F], lo: &[F]) -> (F, F) {
                let n = lo.len();
                let (mut i1, mut ii) = (Acc::zero(), Acc::zero());
                let mut l = 0;
                while l + 2 <= n {
                    let xa = ld(a.as_ptr().add(2 * l));
                    let ya = ld(a.as_ptr().add(2 * l + 2));
                    let xb = ld(b.as_ptr().add(2 * l));
                    let yb = ld(b.as_ptr().add(2 * l + 2));
                    let (a0, a1) = (_mm256_permute2x128_si256::<0x20>(xa, ya), _mm256_permute2x128_si256::<0x31>(xa, ya));
                    let (b0, b1) = (_mm256_permute2x128_si256::<0x20>(xb, yb), _mm256_permute2x128_si256::<0x31>(xb, yb));
                    let w = ld(lo.as_ptr().add(l));
                    i1.mac(w, mul(a1, b1));
                    ii.mac(w, mul(_mm256_xor_si256(a0, a1), _mm256_xor_si256(b0, b1)));
                    l += 2;
                }
                let (mut r1, mut ri) = (i1.sum(), ii.sum());
                if l < n {
                    let (x, y) = super::zc_inner_ref(&a[2 * l..], &b[2 * l..], &lo[l..]);
                    r1 += x;
                    ri += y;
                }
                (r1, ri)
            }

            #[target_feature(enable = $feat)]
            pub unsafe fn dot(a: &[F], b: &[F]) -> F {
                let n = a.len().min(b.len());
                let mut acc = Acc::zero();
                let mut i = 0;
                while i + 2 <= n {
                    acc.mac(ld(a.as_ptr().add(i)), ld(b.as_ptr().add(i)));
                    i += 2;
                }
                let mut r = acc.sum();
                if i < n {
                    r += a[i] * b[i];
                }
                r
            }

            /// Per-lane reduced sums.
            #[target_feature(enable = $feat)]
            pub unsafe fn acc_lanes(a: &Acc) -> [F; 2] {
                let q = |v: __m256i| -> [u128; 2] {
                    let mut w = [0u64; 4];
                    _mm256_storeu_si256(w.as_mut_ptr() as *mut __m256i, v);
                    [(w[1] as u128) << 64 | w[0] as u128, (w[3] as u128) << 64 | w[2] as u128]
                };
                let (p0, p1, pm) = (q(a.p0), q(a.p1), q(a.pm));
                let mut o = [F::ZERO; 2];
                for l in 0..2 {
                    let (c0, c1) = crate::field::combine_f(p0[l], p1[l], pm[l]);
                    o[l] = F { lo: c0, hi: c1 };
                }
                o
            }

            #[inline(always)]
            unsafe fn ldk(p: *const crate::field::K) -> __m256i {
                _mm256_loadu_si256(p as *const __m256i)
            }
            #[inline(always)]
            unsafe fn swap(x: __m256i) -> __m256i {
                _mm256_permute2x128_si256::<0x01>(x, x)
            }

            /// `s·d` for a constant K element `s` and `d = [D₀ D₁]`: `c₀ = S₀D₀ + (αS₁)D₁`,
            /// `c₁ = S₁D₀ + (S₀+S₁)D₁`, with `ca = [S₀, αS₁]`, `cb = [S₁, S₀+S₁]` (two products).
            #[inline]
            #[target_feature(enable = $feat)]
            unsafe fn kmul_c(d: __m256i, ca: __m256i, cb: __m256i) -> __m256i {
                let x = mul(d, ca);
                let y = mul(d, cb);
                let r0 = _mm256_xor_si256(x, swap(x));
                let r1 = _mm256_xor_si256(y, swap(y));
                _mm256_blend_epi32::<0xF0>(r0, r1)
            }

            /// `out[i] = t[2i] + s (t[2i] + t[2i+1])` over K.
            #[target_feature(enable = $feat)]
            pub unsafe fn kfold(t: &[crate::field::K], s: crate::field::K, out: &mut [crate::field::K]) {
                let as1 = s.b.mul_alpha();
                let ss = s.a + s.b;
                let ca = _mm256_set_epi64x(as1.hi as i64, as1.lo as i64, s.a.hi as i64, s.a.lo as i64);
                let cb = _mm256_set_epi64x(ss.hi as i64, ss.lo as i64, s.b.hi as i64, s.b.lo as i64);
                for i in 0..out.len() {
                    let x = ldk(t.as_ptr().add(2 * i));
                    let y = ldk(t.as_ptr().add(2 * i + 1));
                    let r = kmul_c(_mm256_xor_si256(x, y), ca, cb);
                    _mm256_storeu_si256(out.as_mut_ptr().add(i) as *mut __m256i, _mm256_xor_si256(x, r));
                }
            }

            /// `out[i] = K(g[2i]) + s (g[2i] + g[2i+1])`, `g` over F.
            #[target_feature(enable = $feat)]
            pub unsafe fn kfold_f(g: &[F], s: crate::field::K, out: &mut [crate::field::K]) {
                let s01 = _mm256_set_epi64x(s.b.hi as i64, s.b.lo as i64, s.a.hi as i64, s.a.lo as i64);
                for i in 0..out.len() {
                    let (a, b) = (g[2 * i], g[2 * i + 1]);
                    let d = a + b;
                    let r = mul(s01, bcast(d));
                    let base = _mm256_set_epi64x(0, 0, a.hi as i64, a.lo as i64);
                    _mm256_storeu_si256(out.as_mut_ptr().add(i) as *mut __m256i, _mm256_xor_si256(base, r));
                }
            }

            /// The round message `[Σ w₀g₀, Σ w₁g₁, Σ (w₀+w₁)(g₀+g₁)]` over K × K.
            #[target_feature(enable = $feat)]
            pub unsafe fn round_kk(w: &[crate::field::K], g: &[crate::field::K]) -> [crate::field::K; 3] {
                let mut a01 = [Acc::zero(); 3];
                let mut am = [Acc::zero(); 3];
                for i in 0..w.len() / 2 {
                    let (w0, w1) = (ldk(w.as_ptr().add(2 * i)), ldk(w.as_ptr().add(2 * i + 1)));
                    let (g0, g1) = (ldk(g.as_ptr().add(2 * i)), ldk(g.as_ptr().add(2 * i + 1)));
                    let xs = [(w0, g0), (w1, g1), (_mm256_xor_si256(w0, w1), _mm256_xor_si256(g0, g1))];
                    for j in 0..3 {
                        let (x, y) = xs[j];
                        a01[j].mac(x, y);
                        am[j].mac(_mm256_xor_si256(x, swap(x)), _mm256_xor_si256(y, swap(y)));
                    }
                }
                let mut o = [crate::field::K::ZERO; 3];
                for j in 0..3 {
                    let p = acc_lanes(&a01[j]);
                    let pm = acc_lanes(&am[j])[0];
                    o[j] = crate::field::K { a: p[0] + p[1].mul_alpha(), b: pm + p[0] };
                }
                o
            }

            /// The round message over K weights × F values.
            #[target_feature(enable = $feat)]
            pub unsafe fn round_kf(w: &[crate::field::K], g: &[F]) -> [crate::field::K; 3] {
                let mut a = [Acc::zero(); 3];
                for i in 0..w.len() / 2 {
                    let (w0, w1) = (ldk(w.as_ptr().add(2 * i)), ldk(w.as_ptr().add(2 * i + 1)));
                    let (g0, g1) = (g[2 * i], g[2 * i + 1]);
                    a[0].mac(w0, bcast(g0));
                    a[1].mac(w1, bcast(g1));
                    a[2].mac(_mm256_xor_si256(w0, w1), bcast(g0 + g1));
                }
                let mut o = [crate::field::K::ZERO; 3];
                for j in 0..3 {
                    let l = acc_lanes(&a[j]);
                    o[j] = crate::field::K { a: l[0], b: l[1] };
                }
                o
            }

            /// The round message over F × F (as `[g(0), g(1), g(∞)]` in F).
            #[target_feature(enable = $feat)]
            pub unsafe fn round_ff(w: &[F], g: &[F]) -> [F; 3] {
                let mut a = [Acc::zero(); 3];
                let n = w.len() / 2;
                let mut i = 0;
                while i + 2 <= n {
                    let (x, y) = (ld(w.as_ptr().add(2 * i)), ld(w.as_ptr().add(2 * i + 2)));
                    let (w0, w1) = (_mm256_permute2x128_si256::<0x20>(x, y), _mm256_permute2x128_si256::<0x31>(x, y));
                    let (x, y) = (ld(g.as_ptr().add(2 * i)), ld(g.as_ptr().add(2 * i + 2)));
                    let (g0, g1) = (_mm256_permute2x128_si256::<0x20>(x, y), _mm256_permute2x128_si256::<0x31>(x, y));
                    a[0].mac(w0, g0);
                    a[1].mac(w1, g1);
                    a[2].mac(_mm256_xor_si256(w0, w1), _mm256_xor_si256(g0, g1));
                    i += 2;
                }
                let mut o = [a[0].sum(), a[1].sum(), a[2].sum()];
                if i < n {
                    o[0] += w[2 * i] * g[2 * i];
                    o[1] += w[2 * i + 1] * g[2 * i + 1];
                    o[2] += (w[2 * i] + w[2 * i + 1]) * (g[2 * i] + g[2 * i + 1]);
                }
                o
            }

            /// The x₆ round from bits: rows folded at λ by the 8 × 256 table `t` (pairs `lo…lo+n`).
            #[target_feature(enable = $feat)]
            pub unsafe fn x6_inner(t: &[F], a: &[u8], b: &[u8], p0: usize, w: &[F]) -> (F, F) {
                let tp = t.as_ptr() as *const __m128i;
                let row = |src: &[u8], x: usize| -> __m128i {
                    let r = src.as_ptr().add(8 * x);
                    let mut v = _mm_load_si128(tp.add(*r as usize));
                    for j in 1..8 {
                        v = _mm_xor_si128(v, _mm_load_si128(tp.add(j * 256 + *r.add(j) as usize)));
                    }
                    v
                };
                let (mut i1, mut ii) = (Acc::zero(), Acc::zero());
                let n = w.len();
                let mut l = 0;
                while l + 2 <= n {
                    let p = p0 + l;
                    let (a0, a1, a2, a3) = (row(a, 2 * p), row(a, 2 * p + 1), row(a, 2 * p + 2), row(a, 2 * p + 3));
                    let (b0, b1, b2, b3) = (row(b, 2 * p), row(b, 2 * p + 1), row(b, 2 * p + 2), row(b, 2 * p + 3));
                    let av = _mm256_set_m128i(a3, a1);
                    let bv = _mm256_set_m128i(b3, b1);
                    let asum = _mm256_set_m128i(_mm_xor_si128(a2, a3), _mm_xor_si128(a0, a1));
                    let bsum = _mm256_set_m128i(_mm_xor_si128(b2, b3), _mm_xor_si128(b0, b1));
                    let wv = ld(w.as_ptr().add(l));
                    i1.mac(wv, mul(av, bv));
                    ii.mac(wv, mul(asum, bsum));
                    l += 2;
                }
                let (mut r1, mut ri) = (i1.sum(), ii.sum());
                if l < n {
                    let p = p0 + l;
                    let f = |x: __m128i| -> F { let mut o = F::ZERO; _mm_storeu_si128(&mut o as *mut F as *mut __m128i, x); o };
                    let (a0, a1, b0, b1) = (f(row(a, 2 * p)), f(row(a, 2 * p + 1)), f(row(b, 2 * p)), f(row(b, 2 * p + 1)));
                    r1 += w[l] * (a1 * b1);
                    ri += w[l] * ((a0 + a1) * (b0 + b1));
                }
                (r1, ri)
            }

            /// `out[i] = A(2(p0+i)) + s (A(2(p0+i)) + A(2(p0+i)+1))`, rows folded at λ by `t`.
            #[target_feature(enable = $feat)]
            pub unsafe fn x6_fold(t: &[F], a: &[u8], p0: usize, s: F, out: &mut [F]) {
                let tp = t.as_ptr() as *const __m128i;
                let row = |x: usize| -> __m128i {
                    let r = a.as_ptr().add(8 * x);
                    let mut v = _mm_load_si128(tp.add(*r as usize));
                    for j in 1..8 {
                        v = _mm_xor_si128(v, _mm_load_si128(tp.add(j * 256 + *r.add(j) as usize)));
                    }
                    v
                };
                let sv = bcast(s);
                let n = out.len();
                let mut i = 0;
                while i + 2 <= n {
                    let p = p0 + i;
                    let e = _mm256_set_m128i(row(2 * p + 2), row(2 * p));
                    let o = _mm256_set_m128i(row(2 * p + 3), row(2 * p + 1));
                    st(out.as_mut_ptr().add(i), _mm256_xor_si256(e, mul(_mm256_xor_si256(e, o), sv)));
                    i += 2;
                }
                if i < n {
                    let p = p0 + i;
                    let f = |x: __m128i| -> F { let mut o = F::ZERO; _mm_storeu_si128(&mut o as *mut F as *mut __m128i, x); o };
                    let (x0, x1) = (f(row(2 * p)), f(row(2 * p + 1)));
                    out[i] = x0 + s * (x0 + x1);
                }
            }

            /// `acc[i] += x[i]·c`.
            #[target_feature(enable = $feat)]
            pub unsafe fn axpy(acc: &mut [F], x: &[F], c: F) {
                let cv = bcast(c);
                let n = acc.len();
                let mut i = 0;
                while i + 2 <= n {
                    let p = acc.as_mut_ptr().add(i);
                    st(p, _mm256_xor_si256(ld(p), mul(ld(x.as_ptr().add(i)), cv)));
                    i += 2;
                }
                if i < n {
                    acc[i] += x[i] * c;
                }
            }

            /// `acc[l] ^= [c.lo ⊗ x_l | c.hi ⊗ x_l]` (unreduced 128-bit products, one ymm per `l`).
            #[target_feature(enable = $feat)]
            pub unsafe fn xmac(acc: &mut [[u128; 2]], x: &[B64], c: F) {
                let cv = _mm256_set_epi64x(0, c.hi as i64, 0, c.lo as i64);
                for l in 0..acc.len() {
                    let xv = _mm256_set1_epi64x(x[l].0 as i64);
                    let p = acc.as_mut_ptr().add(l) as *mut __m256i;
                    _mm256_storeu_si256(p, _mm256_xor_si256(_mm256_loadu_si256(p), cl::<0x00>(cv, xv)));
                }
            }

            /// Products of pairs (tests).
            #[target_feature(enable = $feat)]
            pub unsafe fn mul_pairs(x: [F; 2], y: [F; 2]) -> [F; 2] {
                let mut o = [F::ZERO; 2];
                st(o.as_mut_ptr(), mul(ld(x.as_ptr()), ld(y.as_ptr())));
                o
            }
        }
    };
}

ymm_kernels!(ymm, "avx2,vpclmulqdq,pclmulqdq,sse4.1", clmul_hw);
ymm_kernels!(ymm_sim, "avx2,pclmulqdq,sse4.1", clmul_sim);

// ---------------------------------------------------------------- round 1 (AVX2)

pub mod r1 {
    use crate::field::F;
    use crate::skipdom::Skip;
    use std::arch::x86_64::*;

    /// The table apply, 64 output bytes in two ymm (output byte `i` reads `t0[byte_b][i ⊕ 8b]`).
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn apply(t0: *const u8, bytes: *const u8) -> (__m256i, __m256i) {
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
                    (0, _) => (_mm256_shuffle_epi32::<0x4E>(v0), _mm256_shuffle_epi32::<0x4E>(v1)),
                    (1, 0) => (_mm256_permute4x64_epi64::<0x4E>(v0), _mm256_permute4x64_epi64::<0x4E>(v1)),
                    (1, _) => (_mm256_permute4x64_epi64::<0x1B>(v0), _mm256_permute4x64_epi64::<0x1B>(v1)),
                    (2, 0) => (v1, v0),
                    (2, _) => (_mm256_shuffle_epi32::<0x4E>(v1), _mm256_shuffle_epi32::<0x4E>(v0)),
                    (_, 0) => (_mm256_permute4x64_epi64::<0x4E>(v1), _mm256_permute4x64_epi64::<0x4E>(v0)),
                    (_, _) => (_mm256_permute4x64_epi64::<0x1B>(v1), _mm256_permute4x64_epi64::<0x1B>(v0)),
                };
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
    unsafe fn xtime(p: __m256i, poly: __m256i) -> __m256i {
        let m = _mm256_and_si256(_mm256_cmpgt_epi8(_mm256_setzero_si256(), p), poly);
        _mm256_xor_si256(_mm256_add_epi8(p, p), m)
    }
    /// 32 GF(2^8) products, bit-serial over `b` (no GFNI on Zen 3).
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn gf8mul(a: __m256i, b: __m256i, poly: __m256i) -> __m256i {
        let mut bb = b;
        let mut p = _mm256_blendv_epi8(_mm256_setzero_si256(), a, bb);
        for _ in 1..8 {
            bb = _mm256_add_epi8(bb, bb);
            p = xtime(p, poly);
            p = _mm256_blendv_epi8(p, _mm256_xor_si256(p, a), bb);
        }
        p
    }

    /// 64-byte bit transpose: output byte `8b + t`, bit `k` = bit `t` of input byte `8k + b`.
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn bit_transpose(inp: *const u8, out: *mut u8) {
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
    struct A64([[u8; 64]; 16]);

    /// `out[i] ^= Σ_p t[p·256 + bytes(e[i])_p]` (16 byte tables of F; `ringswitch::phi_apply` added
    /// into `out`), two elements interleaved (pass 6).
    #[target_feature(enable = "avx2")]
    pub unsafe fn phi_add(t: &[F], e: &[F], out: &mut [F]) {
        debug_assert!(t.len() >= 16 * 256 && out.len() == e.len());
        let tp = t.as_ptr() as *const __m128i;
        let n = e.len();
        let eb = e.as_ptr() as *const u8;
        let op = out.as_mut_ptr() as *mut __m128i;
        let mut i = 0;
        while i + 2 <= n {
            let (b0, b1) = (eb.add(16 * i), eb.add(16 * i + 16));
            let mut v0 = _mm_load_si128(tp.add(*b0 as usize));
            let mut v1 = _mm_load_si128(tp.add(*b1 as usize));
            for p in 1..16 {
                v0 = _mm_xor_si128(v0, _mm_load_si128(tp.add(p * 256 + *b0.add(p) as usize)));
                v1 = _mm_xor_si128(v1, _mm_load_si128(tp.add(p * 256 + *b1.add(p) as usize)));
            }
            _mm_store_si128(op.add(i), _mm_xor_si128(_mm_load_si128(op.add(i)), v0));
            _mm_store_si128(op.add(i + 1), _mm_xor_si128(_mm_load_si128(op.add(i + 1)), v1));
            i += 2;
        }
        if i < n {
            out[i] += crate::ringswitch::phi_apply(t, e[i]);
        }
    }

    /// `row[i] ^= Σ_p q[offs[p] + i]`, two elements per ymm.
    #[target_feature(enable = "avx2")]
    pub unsafe fn xor_rows(q: &[F], offs: &[usize; 16], row: &mut [F]) {
        let n = row.len();
        let qp = q.as_ptr();
        let rp = row.as_mut_ptr();
        let mut i = 0;
        while i + 2 <= n {
            let ld = |p: usize| _mm256_loadu_si256(qp.add(offs[p] + i) as *const __m256i);
            let mut a = _mm256_xor_si256(ld(0), ld(1));
            let mut b = _mm256_xor_si256(ld(2), ld(3));
            for p in (4..16).step_by(2) {
                a = _mm256_xor_si256(a, ld(p));
                b = _mm256_xor_si256(b, ld(p + 1));
            }
            let o = rp.add(i) as *mut __m256i;
            _mm256_storeu_si256(o, _mm256_xor_si256(_mm256_loadu_si256(o), _mm256_xor_si256(a, b)));
            i += 2;
        }
        while i < n {
            let mut a = *qp.add(offs[0] + i);
            for o in &offs[1..] {
                a += *qp.add(o + i);
            }
            *rp.add(i) += a;
            i += 1;
        }
    }

    /// `phi_add` at the positions `idx` only: `out[l] ^= Φ-tables(e[l])` for `l ∈ idx`.
    #[target_feature(enable = "avx2")]
    pub unsafe fn phi_add_idx(t: &[F], e: &[F], idx: &[u32], out: &mut [F]) {
        let tp = t.as_ptr() as *const __m128i;
        let eb = e.as_ptr() as *const u8;
        let op = out.as_mut_ptr() as *mut __m128i;
        let n = idx.len();
        let mut i = 0;
        while i + 2 <= n {
            let (l0, l1) = (idx[i] as usize, idx[i + 1] as usize);
            debug_assert!(l0 < e.len() && l1 < e.len() && l0 < out.len() && l1 < out.len());
            let (b0, b1) = (eb.add(16 * l0), eb.add(16 * l1));
            let mut v0 = _mm_load_si128(tp.add(*b0 as usize));
            let mut v1 = _mm_load_si128(tp.add(*b1 as usize));
            for p in 1..16 {
                v0 = _mm_xor_si128(v0, _mm_load_si128(tp.add(p * 256 + *b0.add(p) as usize)));
                v1 = _mm_xor_si128(v1, _mm_load_si128(tp.add(p * 256 + *b1.add(p) as usize)));
            }
            _mm_store_si128(op.add(l0), _mm_xor_si128(_mm_load_si128(op.add(l0)), v0));
            _mm_store_si128(op.add(l1), _mm_xor_si128(_mm_load_si128(op.add(l1)), v1));
            i += 2;
        }
        if i < n {
            let l = idx[i] as usize;
            out[l] += crate::ringswitch::phi_apply(t, e[l]);
        }
    }

    /// One stripe of 8 blocks of `lincheck::partial_fold` (pass 6): for every word `wi < 256` and
    /// bit `j < 64`, `acc[64 wi + j] ^= t[Σ_r 2^r · bit j of z[r·256 + wi]]`; the 8-bit indices of a
    /// word come from one 64-byte bit transpose.
    #[target_feature(enable = "avx2")]
    pub unsafe fn pf_stripe(z: &[u64], t: &[F; 256], acc: &mut [F]) {
        debug_assert!(z.len() >= 7 * 256 + 256 && acc.len() >= 256 * 64);
        let mut buf = A64([[0u8; 64]; 16]);
        let tp = t.as_ptr() as *const __m128i;
        let ap = acc.as_mut_ptr() as *mut __m128i;
        let zp = z.as_ptr();
        for wi in 0..256 {
            let w = buf.0[0].as_mut_ptr() as *mut u64;
            for r in 0..8 {
                *w.add(r) = *zp.add(r * 256 + wi);
            }
            bit_transpose(buf.0[0].as_ptr(), buf.0[1].as_mut_ptr());
            let idx = &buf.0[1];
            let a = ap.add(64 * wi);
            for j in 0..64 {
                let p = a.add(j);
                _mm_store_si128(p, _mm_xor_si128(_mm_load_si128(p), _mm_load_si128(tp.add(idx[j] as usize))));
            }
        }
    }

    /// The c-side table pair (pass 6): `conv2[bm·256 + v] = (conv[v & 0x55], conv[v & 0xAA])`, one
    /// 32-byte load for both banks.
    fn conv2(sk: &Skip) -> &'static Vec<[F; 2]> {
        static T: std::sync::OnceLock<Vec<[F; 2]>> = std::sync::OnceLock::new();
        T.get_or_init(|| (0..16 * 256).map(|i| { let (bm, v) = (i / 256, i % 256); [sk.conv[bm * 256 + (v & 0x55)], sk.conv[bm * 256 + (v & 0xAA)]] }).collect())
    }

    #[target_feature(enable = "avx2")]
    pub unsafe fn window(sk: &Skip, a: &[u8], b: &[u8], z: &[u8], out: &mut [F; 192]) {
        let poly = _mm256_set1_epi8((crate::field::gf8_poly() & 0xFF) as u8 as i8);
        let mut chunk_ab = A64([[0u8; 64]; 16]);
        let mut chunk_c = A64([[0u8; 64]; 16]);
        let t0 = sk.t0p();
        for bm in 0..16 {
            let bb = bm * 64;
            let (mut s0, mut s1) = (_mm256_setzero_si256(), _mm256_setzero_si256());
            for k in (0..8).rev() {
                let (a0, a1) = apply(t0, a.as_ptr().add(bb + k * 8));
                let (b0, b1) = apply(t0, b.as_ptr().add(bb + k * 8));
                s0 = _mm256_xor_si256(xtime(s0, poly), gf8mul(a0, b0, poly));
                s1 = _mm256_xor_si256(xtime(s1, poly), gf8mul(a1, b1, poly));
            }
            _mm256_store_si256(chunk_ab.0[bm].as_mut_ptr() as *mut __m256i, s0);
            _mm256_store_si256(chunk_ab.0[bm].as_mut_ptr().add(32) as *mut __m256i, s1);
            bit_transpose(z.as_ptr().add(bb), chunk_c.0[bm].as_mut_ptr());
        }
        let cv = sk.conv.as_ptr();
        let c2 = conv2(sk).as_ptr();
        for lane in 0..64 {
            let (mut cab, mut c01) = (_mm_setzero_si128(), _mm256_setzero_si256());
            for bm in 0..16 {
                let vab = chunk_ab.0[bm][lane] as usize;
                let vc = chunk_c.0[bm][lane] as usize;
                cab = _mm_xor_si128(cab, _mm_load_si128(cv.add(bm * 256 + vab) as *const __m128i));
                c01 = _mm256_xor_si256(c01, _mm256_loadu_si256(c2.add(bm * 256 + vc) as *const __m256i));
            }
            _mm_storeu_si128(out.as_mut_ptr().add(lane) as *mut __m128i, cab);
            _mm_storeu_si128(out.as_mut_ptr().add(64 + lane) as *mut __m128i, _mm256_castsi256_si128(c01));
            _mm_storeu_si128(out.as_mut_ptr().add(128 + lane) as *mut __m128i, _mm256_extracti128_si256::<1>(c01));
        }
    }
}

// ---------------------------------------------------------------- self-test

/// Every kernel of every available tier against the portable reference, on random inputs.
pub fn selftest() -> Result<String, String> {
    let mut s = 0x0123_4567_89AB_CDEFu64;
    let mut rnd = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let base = tier();
    let mut tiers = vec![];
    if crate::field::hw_pclmul() {
        tiers.push(2u8);
    }
    if hw_ymm() {
        tiers.push(3);
    }
    if crate::field::hw_pclmul() && hw_avx2() {
        tiers.push(4);
    }
    let n = 37;
    let mut fv = |n: usize| -> Vec<F> { (0..n).map(|_| F::new(rnd(), rnd())).collect() };
    let a = fv(2 * n);
    let b = fv(2 * n);
    let lo = fv(n);
    let xs = fv(200);
    let sc = fv(1)[0];
    let tw = B64(fv(1)[0].lo);
    let wbytes: Vec<u8> = fv(192).iter().flat_map(|x| x.to_bytes()).collect();
    let (wa, wb, wz) = (&wbytes[..1024], &wbytes[1024..2048], &wbytes[2048..3072]);
    set_tier(1);
    let mut top_r = a[..n].to_vec();
    let mut bot_r = b[..n].to_vec();
    butterfly(&mut top_r, &mut bot_r, tw);
    let mut fold_r = vec![F::ZERO; n];
    fold(&a, sc, &mut fold_r);
    let zr = zc_inner(&a, &b, &lo);
    let dr = dot(&a, &b);
    let sk = crate::skipdom::skip();
    let mut w_r = [F::ZERO; 192];
    round1_window(sk, wa, wb, wz, &mut w_r);
    let ka: Vec<crate::field::K> = a.chunks(2).map(|c| crate::field::K { a: c[0], b: c[1] }).collect();
    let kb: Vec<crate::field::K> = b.chunks(2).map(|c| crate::field::K { a: c[0], b: c[1] }).collect();
    let ks = crate::field::K { a: sc, b: lo[0] };
    let mut kf_r = vec![crate::field::K::ZERO; n / 2];
    kfold(&ka[..n], ks, &mut kf_r);
    let mut kff_r = vec![crate::field::K::ZERO; n];
    kfold_f(&a, ks, &mut kff_r);
    let (rkk, rkf, rff) = (round_kk(&ka, &kb), round_kf(&ka, &b[..n]), round_ff(&a, &b));
    let xb: Vec<B64> = b.iter().map(|x| B64(x.lo)).collect();
    let mut xm_r = vec![[0u128; 2]; n];
    xmac(&mut xm_r, &xb, sc);
    let mut ax_r = a.clone();
    axpy(&mut ax_r, &b, sc);
    let x6t = crate::zerocheck::fold_tables(sc);
    let x6r = x6_inner(&x6t, &wbytes[..1024], &wbytes[1024..2048], 3, &lo[..33]);
    let mut x6f = vec![F::ZERO; 33];
    x6_fold(&x6t, &wbytes[..1024], 5, sc, &mut x6f);
    let pt = crate::ringswitch::phi_tables(&lo[..7], sc);
    let mut ph_r = b[..33].to_vec();
    phi_add(&pt, &a[..33], &mut ph_r);
    let zw: Vec<u64> = (0..2048).map(|i| a[i % a.len()].lo ^ b[(7 * i) % b.len()].hi.rotate_left(i as u32)).collect();
    let pft: [F; 256] = std::array::from_fn(|i| xs[i % 200] + lo[i % lo.len()]);
    let mut pf_r = vec![F::ZERO; 16384];
    pf_stripe(&zw, &pft, &mut pf_r);
    let mut tested = vec![];
    let mut fail = None;
    for &t in &tiers {
        set_tier(t);
        let name = tier_name();
        let mut top = a[..n].to_vec();
        let mut bot = b[..n].to_vec();
        butterfly(&mut top, &mut bot, tw);
        let mut fo = vec![F::ZERO; n];
        fold(&a, sc, &mut fo);
        let mut w = [F::ZERO; 192];
        round1_window(sk, wa, wb, wz, &mut w);
        let mut prod_ok = true;
        for i in 0..100 {
            let (x, y) = ([xs[2 * i % 200], xs[(2 * i + 1) % 200]], [xs[(3 * i + 7) % 200], xs[(5 * i + 1) % 200]]);
            let want = [x[0].mul_soft(y[0]), x[1].mul_soft(y[1])];
            let got = match t {
                3 => unsafe { ymm::mul_pairs(x, y) },
                4 => unsafe { ymm_sim::mul_pairs(x, y) },
                _ => [x[0] * y[0], x[1] * y[1]],
            };
            prod_ok &= got == want;
        }
        let checks = [
            ("butterfly", top == top_r && bot == bot_r),
            ("fold", fo == fold_r),
            ("zc_inner", zc_inner(&a, &b, &lo) == zr),
            ("dot", dot(&a, &b) == dr),
            ("round-1 window", w == w_r),
            ("F product", prod_ok),
            ("kfold", { let mut o = vec![crate::field::K::ZERO; n / 2]; kfold(&ka[..n], ks, &mut o); o == kf_r }),
            ("kfold_f", { let mut o = vec![crate::field::K::ZERO; n]; kfold_f(&a, ks, &mut o); o == kff_r }),
            ("round_kk", round_kk(&ka, &kb) == rkk),
            ("round_kf", round_kf(&ka, &b[..n]) == rkf),
            ("round_ff", round_ff(&a, &b) == rff),
            ("xmac", { let mut o = vec![[0u128; 2]; n]; xmac(&mut o, &xb, sc); o == xm_r }),
            ("axpy", { let mut o = a.clone(); axpy(&mut o, &b, sc); o == ax_r }),
            ("x6_inner", x6_inner(&x6t, &wbytes[..1024], &wbytes[1024..2048], 3, &lo[..33]) == x6r),
            ("x6_fold", { let mut o = vec![F::ZERO; 33]; x6_fold(&x6t, &wbytes[..1024], 5, sc, &mut o); o == x6f }),
            ("phi_add", { let mut o = b[..33].to_vec(); phi_add(&pt, &a[..33], &mut o); o == ph_r }),
            ("phi_add_idx", { let mut o = b[..33].to_vec(); let idx: Vec<u32> = (0..33).collect(); phi_add_idx(&pt, &a[..33], &idx, &mut o); o == ph_r }),
            ("pf_stripe", { let mut o = vec![F::ZERO; 16384]; pf_stripe(&zw, &pft, &mut o); o == pf_r }),
        ];
        if let Some((k, _)) = checks.iter().find(|c| !c.1) {
            fail = Some(format!("{name}: {k}"));
            break;
        }
        tested.push(name);
    }
    set_tier(base);
    match fail {
        Some(e) => Err(e),
        None => Ok(format!("tier={} checked=[{}]", tier_name(), tested.join(","))),
    }
}

#[cfg(test)]
mod pass6_tests {
    use super::*;
    /// The AVX2 table kernels (round-1 window with `conv2`, `phi_add`, `pf_stripe`) against their
    /// portable references, whenever the machine has AVX2 (they need no carry-less multiply).
    #[test]
    fn avx2_table_kernels_match() {
        if !hw_avx2() {
            return;
        }
        let mut s = 0x9E37_79B9_7F4A_7C15u64;
        let mut rnd = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        let fv = |n: usize, r: &mut dyn FnMut() -> u64| -> Vec<F> { (0..n).map(|_| F::new(r(), r())).collect() };
        let sk = crate::skipdom::skip();
        for _ in 0..4 {
            let wb: Vec<u8> = (0..3072).map(|_| rnd() as u8).collect();
            let (mut w0, mut w1) = ([F::ZERO; 192], [F::ZERO; 192]);
            crate::zerocheck::window_portable(sk, &wb[..1024], &wb[1024..2048], &wb[2048..], &mut w0);
            unsafe { r1::window(sk, &wb[..1024], &wb[1024..2048], &wb[2048..], &mut w1) };
            assert_eq!(w0, w1, "round-1 window");
            let rpp = fv(7, &mut rnd);
            let t = crate::ringswitch::phi_tables(&rpp, F::new(rnd(), rnd()));
            let e = fv(1023, &mut rnd);
            let o0: Vec<F> = fv(1023, &mut rnd);
            let mut o1 = o0.clone();
            unsafe { r1::phi_add(&t, &e, &mut o1) };
            for i in 0..e.len() {
                assert_eq!(o1[i], o0[i] + crate::ringswitch::phi_apply(&t, e[i]), "phi_add {i}");
            }
            let idx: Vec<u32> = (0..1023).filter(|i| i % 3 != 1).collect();
            let mut o2 = o0.clone();
            unsafe { r1::phi_add_idx(&t, &e, &idx, &mut o2) };
            for i in 0..e.len() {
                let want = if i % 3 != 1 { o0[i] + crate::ringswitch::phi_apply(&t, e[i]) } else { o0[i] };
                assert_eq!(o2[i], want, "phi_add_idx {i}");
            }
            let z: Vec<u64> = (0..2048).map(|_| rnd()).collect();
            let pt: [F; 256] = std::array::from_fn(|_| F::new(rnd(), rnd()));
            let a0 = fv(16384, &mut rnd);
            let (mut a1, mut a2) = (a0.clone(), a0.clone());
            pf_stripe_ref(&z, &pt, &mut a1);
            unsafe { r1::pf_stripe(&z, &pt, &mut a2) };
            assert!(a1 == a2, "pf_stripe");
        }
    }
}
