// lvm2 PFAST-K: four E2 elements to a 512-bit register, for the E2 arm of the local rounds.
//! `F128` values four to a register in their memory layout (`[c0, c1]` per 128-bit lane), with the
//! unreduced product kept as Karatsuba's three carry-less products `[P0, P1, M]` per lane, as
//! [`F128::mul_unreduced`] keeps them, so a sum of products reduces once; the reduction folds each
//! 128-bit word by `0x1B` twice (`gf2_64::reduce`'s value).

use core::arch::x86_64::*;

use crate::lv::primitives::field::{F128, F128Unreduced};

/// Four elements, element `i` in 128-bit lane `i`.
#[derive(Clone, Copy)]
pub struct E2x4(__m512i);

/// Four unreduced sums of products: `P0`, `P1` and `M` of element `i` in lane `i` of each register.
#[derive(Clone, Copy)]
pub struct E2x4U([__m512i; 3]);

/// Each lane's two words swapped.
#[inline(always)]
fn swap(a: __m512i) -> __m512i {
    // SAFETY: AVX-512F is enabled at compile time (the module's cfg).
    unsafe { _mm512_shuffle_epi32::<0x4e>(a) }
}

/// The low word of each lane reduced: `lo ^ hi * 0x1B` folded twice (the second fold takes the first's
/// at most 4 bits past `x^63`, its product at most 8 bits).
#[inline(always)]
fn reduce_lanes(x: __m512i) -> __m512i {
    // SAFETY: AVX-512F and VPCLMULQDQ are enabled at compile time (the module's cfg).
    unsafe {
        let r = _mm512_set1_epi64(crate::lv::primitives::field::gf2_64::R64 as i64);
        let t = _mm512_clmulepi64_epi128::<0x01>(x, r);
        let u = _mm512_clmulepi64_epi128::<0x01>(t, r);
        _mm512_ternarylogic_epi64(x, t, u, 0x96)
    }
}

impl E2x4 {
    /// Elements `v[0..4]`.
    #[inline(always)]
    pub fn load(v: &[F128]) -> Self {
        assert!(v.len() >= 4);
        // SAFETY: AVX-512F; `v` holds four `repr(C)` pairs of words, 64 bytes.
        unsafe { Self(_mm512_loadu_si512(v.as_ptr().cast())) }
    }

    #[inline(always)]
    pub fn splat(x: F128) -> Self {
        // SAFETY: AVX-512F.
        unsafe { Self(_mm512_broadcast_i32x4(_mm_set_epi64x(x.c1 as i64, x.c0 as i64))) }
    }

    #[inline(always)]
    pub fn to_array(self) -> [F128; 4] {
        let mut out = [F128::ZERO; 4];
        // SAFETY: AVX-512F; `out` is 64 bytes of `repr(C)` pairs of words.
        unsafe { _mm512_storeu_si512(out.as_mut_ptr().cast(), self.0) };
        out
    }

    /// The even and the odd elements of `a` then `b`: `([a0, a2, b0, b2], [a1, a3, b1, b3])`.
    #[inline(always)]
    pub fn even_odd(a: Self, b: Self) -> (Self, Self) {
        // SAFETY: AVX-512F.
        unsafe {
            let even = _mm512_setr_epi64(0, 1, 4, 5, 8, 9, 12, 13);
            let odd = _mm512_setr_epi64(2, 3, 6, 7, 10, 11, 14, 15);
            (
                Self(_mm512_permutex2var_epi64(a.0, even, b.0)),
                Self(_mm512_permutex2var_epi64(a.0, odd, b.0)),
            )
        }
    }

    #[inline(always)]
    pub fn add(self, b: Self) -> Self {
        // SAFETY: AVX-512F.
        unsafe { Self(_mm512_xor_si512(self.0, b.0)) }
    }

    /// The three Karatsuba products of each lane: `a0 b0`, `a1 b1`, `(a0 + a1)(b0 + b1)`.
    #[inline(always)]
    pub fn mul_unreduced(self, b: Self) -> E2x4U {
        // SAFETY: AVX-512F and VPCLMULQDQ.
        unsafe {
            let (sa, sb) = (_mm512_xor_si512(self.0, swap(self.0)), _mm512_xor_si512(b.0, swap(b.0)));
            E2x4U([
                _mm512_clmulepi64_epi128::<0x00>(self.0, b.0),
                _mm512_clmulepi64_epi128::<0x11>(self.0, b.0),
                _mm512_clmulepi64_epi128::<0x00>(sa, sb),
            ])
        }
    }

    #[inline(always)]
    pub fn mul(self, b: Self) -> Self {
        self.mul_unreduced(b).reduce()
    }
}

impl E2x4U {
    #[inline(always)]
    pub fn zero() -> Self {
        // SAFETY: AVX-512F.
        unsafe { Self([_mm512_setzero_si512(); 3]) }
    }

    #[inline(always)]
    pub fn xor(self, b: Self) -> Self {
        // SAFETY: AVX-512F.
        unsafe { Self(std::array::from_fn(|k| _mm512_xor_si512(self.0[k], b.0[k]))) }
    }

    /// Each lane as `F128Unreduced::reduce` does: `c0 = reduce(P0 + P1)`, `c1 = reduce(M + P0 + P1 + x P1)`.
    #[inline(always)]
    pub fn reduce(self) -> E2x4 {
        let [p0, p1, m] = self.0;
        // SAFETY: AVX-512F.
        unsafe {
            let s = _mm512_xor_si512(p0, p1);
            // `x P1` on each 128-bit lane (P1 has at most 127 bits).
            let x_p1 = _mm512_or_si512(_mm512_slli_epi64::<1>(p1), _mm512_bslli_epi128::<8>(_mm512_srli_epi64::<63>(p1)));
            let c1 = _mm512_ternarylogic_epi64(m, s, x_p1, 0x96);
            E2x4(_mm512_unpacklo_epi64(reduce_lanes(s), reduce_lanes(c1)))
        }
    }

    /// The sum of the four lanes, as one unreduced accumulator.
    #[inline(always)]
    pub fn sum(self) -> F128Unreduced {
        let p: [u128; 3] = self.0.map(|v| {
            let mut lanes = [0u128; 4];
            // SAFETY: AVX-512F; `lanes` is 64 bytes.
            unsafe { _mm512_storeu_si512(lanes.as_mut_ptr().cast(), v) };
            lanes[0] ^ lanes[1] ^ lanes[2] ^ lanes[3]
        });
        F128Unreduced::from_products(p)
    }
}
