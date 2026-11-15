// lvm2 E2-K (roll 7, ARCH-7 §2): the 128-bit field of the GKR front, and the field interface the Keccak GKR's
// passes are generic over.
//! `E2 = F128 = K[X] / (X^2 + xX + 1)` over `K = GF(2^64)` (`x` the generator of `K`), and [`Ext`], the field
//! interface the Keccak GKR's layer passes are written against: `W` words a weight, `E3 = F192` at `W = 3` (the
//! entry's field until roll 7) and `E2` at `W = 2`.
//!
//! A product is Karatsuba's three carry-less products `P0 = a0 b0`, `P1 = a1 b1`, `M = (a0 + a1)(b0 + b1)`
//! (NOTE-FIELD §5: three is the minimum for width 2), then
//!
//! ```text
//!     (a0 + a1 X)(b0 + b1 X) = (P0 + P1) + (M + P0 + P1 + x P1) X        (X^2 = xX + 1)
//! ```
//!
//! and one `K` reduction per coefficient. The three products are kept apart until the reduction
//! ([`F128Unreduced`]), so a sum of products is three XORs a term and one fold at the end.
//!
//! `X^2 + xX + 1` is irreducible over `K` (LIT-F §2.3; the self-test checks it: the Frobenius `a -> a^(2^64)`
//! sends `X` to the other root `X + x`, which happens if and only if `X` is not in `K`). Its roots are `X` and
//! `X + x`, so the norm of `a0 + a1 X` is
//! `a0^2 + x a0 a1 + a1^2`, and `a^-1 = (a0 + x a1 + a1 X) / N(a)`.

use std::fmt::Debug;
use std::iter::Sum;
use std::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

use super::gf2_64::{mul_wide, reduce as reduce64};
use super::{F64, F192, F192Unreduced};

/// An element `c0 + c1 X`; bit `i` of each coefficient is its coefficient of `x^i`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct F128 {
    pub c0: u64,
    pub c1: u64,
}

/// The three Karatsuba products of a sum of products, unreduced: `P0`, `P1` and `M` as 128-bit polynomials.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128Unreduced {
    p: [u128; 3],
}

impl F128 {
    pub const ZERO: Self = Self { c0: 0, c1: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0 };
    /// The element `X`.
    pub const X: Self = Self { c0: 0, c1: 1 };

    #[inline]
    pub const fn new(c0: u64, c1: u64) -> Self {
        Self { c0, c1 }
    }

    #[inline]
    pub fn mul_unreduced(self, b: Self) -> F128Unreduced {
        F128Unreduced {
            p: [
                mul_wide(self.c0, b.c0),
                mul_wide(self.c1, b.c1),
                mul_wide(self.c0 ^ self.c1, b.c0 ^ b.c1),
            ],
        }
    }

    /// `(a0 + a1 X)^2 = a0^2 + a1^2 (xX + 1) = (a0^2 + a1^2) + x a1^2 X`.
    #[inline]
    pub fn square(self) -> Self {
        let (s0, s1) = (super::gf2_64::square_wide(self.c0), super::gf2_64::square_wide(self.c1));
        F128Unreduced { p: [s0, s1, s0 ^ s1] }.reduce()
    }

    /// Multiplicative inverse through the norm; `ZERO.inv() == ZERO`.
    pub fn inv(self) -> Self {
        let (a0, a1) = (F64(self.c0), F64(self.c1));
        let norm = a0 * a0 + F64::G * a0 * a1 + a1 * a1;
        let n = norm.inv();
        Self {
            c0: ((a0 + F64::G * a1) * n).0,
            c1: (a1 * n).0,
        }
    }

    pub fn pow(self, mut e: u128) -> Self {
        let (mut acc, mut b) = (Self::ONE, self);
        while e > 0 {
            if e & 1 == 1 {
                acc *= b;
            }
            b = b.square();
            e >>= 1;
        }
        acc
    }

    #[inline]
    pub fn mul_base(self, k: F64) -> Self {
        self.mul_base_unreduced(k).reduce()
    }

    /// The mixed product by `k ∈ K`: two products, held as `P0` and `M + P1` (so `c1` reduces to `a1 k`).
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> F128Unreduced {
        let (p0, p1) = (mul_wide(self.c0, k.0), mul_wide(self.c1, k.0));
        // c0 = P0 + P1 must be a0 k and c1 = M + P0 + P1 + x P1 must be a1 k: take P1 = 0, M = P0 + a1 k.
        F128Unreduced { p: [p0, 0, p0 ^ p1] }
    }
}

impl F128Unreduced {
    pub const ZERO: Self = Self { p: [0; 3] };

    #[inline]
    pub fn reduce(self) -> F128 {
        let [p0, p1, m] = self.p;
        // P1 is a sum of products of two 64-bit polynomials (degree <= 126), so x P1 fits 128 bits.
        F128 {
            c0: reduce64(p0 ^ p1),
            c1: reduce64(m ^ p0 ^ p1 ^ (p1 << 1)),
        }
    }
}

impl From<F128> for F128Unreduced {
    #[inline]
    fn from(e: F128) -> Self {
        // P0 = c0, P1 = 0, M = c0 + c1 gives (c0, c1).
        Self {
            p: [e.c0 as u128, 0, (e.c0 ^ e.c1) as u128],
        }
    }
}

impl BitXor for F128Unreduced {
    type Output = Self;
    #[inline]
    fn bitxor(mut self, rhs: Self) -> Self {
        self ^= rhs;
        self
    }
}

impl BitXorAssign for F128Unreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        for (a, b) in self.p.iter_mut().zip(rhs.p) {
            *a ^= b;
        }
    }
}

impl Add for F128 {
    type Output = Self;
    #[inline]
    fn add(self, o: Self) -> Self {
        Self {
            c0: self.c0 ^ o.c0,
            c1: self.c1 ^ o.c1,
        }
    }
}

impl AddAssign for F128 {
    #[inline]
    fn add_assign(&mut self, o: Self) {
        *self = *self + o;
    }
}

impl Mul for F128 {
    type Output = Self;
    #[inline]
    fn mul(self, o: Self) -> Self {
        self.mul_unreduced(o).reduce()
    }
}

impl MulAssign for F128 {
    #[inline]
    fn mul_assign(&mut self, o: Self) {
        *self = *self * o;
    }
}

impl Sum for F128 {
    fn sum<I: Iterator<Item = Self>>(it: I) -> Self {
        it.fold(Self::ZERO, |a, b| a + b)
    }
}

impl<'a> Sum<&'a F128> for F128 {
    fn sum<I: Iterator<Item = &'a Self>>(it: I) -> Self {
        it.fold(Self::ZERO, |a, b| a + *b)
    }
}

impl From<F64> for F128 {
    #[inline]
    fn from(k: F64) -> Self {
        Self { c0: k.0, c1: 0 }
    }
}

// ------------------------------------------------------------------------------------------------
// The interface the Keccak GKR's passes are generic over.
// ------------------------------------------------------------------------------------------------

/// A deferred-reduction accumulator of a field [`Ext`].
pub trait Unreduced<F>: Copy + Default + Send + Sync + BitXor<Output = Self> + BitXorAssign {
    const ZERO: Self;
    fn reduce(self) -> F;
}

impl Unreduced<F192> for F192Unreduced {
    const ZERO: Self = F192Unreduced::ZERO;
    #[inline(always)]
    fn reduce(self) -> F192 {
        F192Unreduced::reduce(self)
    }
}

impl Unreduced<F128> for F128Unreduced {
    const ZERO: Self = F128Unreduced::ZERO;
    #[inline(always)]
    fn reduce(self) -> F128 {
        F128Unreduced::reduce(self)
    }
}

/// An extension of `K` of `W` words, as the Keccak GKR's layer passes use it: `F192` (E3, `W = 3`) or `F128`
/// (E2, `W = 2`). Limb `k` is the coefficient of the `k`-th power of the extension's generator; `K` is limb 0.
///
/// The transcript stays `F192`-valued in roll 7's phase G0: a challenge is the transcript's E answer cut to its
/// first `W` lanes ([`Ext::from_challenge`], ARCH-7 §2.2), and a scalar is sent as an E scalar with the high
/// lanes zero ([`Ext::to_scalar`]). E2-P replaces the latter with 16-byte scalars.
pub trait Ext<const W: usize>:
    Copy
    + Default
    + Debug
    + PartialEq
    + Eq
    + Send
    + Sync
    + 'static
    + Add<Output = Self>
    + AddAssign
    + Mul<Output = Self>
    + MulAssign
    + Sum
    + for<'a> Sum<&'a Self>
    + From<F64>
{
    type Unreduced: Unreduced<Self>;
    const ZERO: Self;
    const ONE: Self;
    /// `E3` or `E2`, for logs.
    const NAME: &'static str;

    fn to_limbs(self) -> [u64; W];
    fn from_limbs(limbs: [u64; W]) -> Self;
    fn mul_unreduced(self, rhs: Self) -> Self::Unreduced;
    fn mul_base(self, k: F64) -> Self;
    fn mul_base_unreduced(self, k: F64) -> Self::Unreduced;
    fn square(self) -> Self;
    fn inv(self) -> Self;
    /// The challenge an E answer gives: its first `W` lanes.
    fn from_challenge(c: F192) -> Self;
    /// The E scalar the transcript carries for `self`.
    fn to_scalar(self) -> F192;

    /// `eq(r, .)`, little-endian (variable `k` is bit `k`).
    fn eq_table(r: &[Self]) -> Vec<Self> {
        let mut out = vec![Self::ZERO; 1 << r.len()];
        out[0] = Self::ONE;
        for (i, &rk) in r.iter().enumerate() {
            let half = 1usize << i;
            let (lo, hi) = out[..2 * half].split_at_mut(half);
            for (l, h) in lo.iter_mut().zip(hi) {
                let p = *l * rk;
                *h = p;
                *l += p;
            }
        }
        out
    }

    /// `[x^0, .., x^(n-1)]`.
    fn powers(x: Self, n: usize) -> Vec<Self> {
        let mut out = Vec::with_capacity(n);
        let mut p = Self::ONE;
        for _ in 0..n {
            out.push(p);
            p *= x;
        }
        out
    }

    /// A polynomial at `x`, by Horner, constant first.
    #[inline]
    fn poly_eval(coeffs: &[Self], x: Self) -> Self {
        coeffs.iter().rev().fold(Self::ZERO, |acc, &c| acc * x + c)
    }
}

impl Ext<3> for F192 {
    type Unreduced = F192Unreduced;
    const ZERO: Self = F192::ZERO;
    const ONE: Self = F192::ONE;
    const NAME: &'static str = "E3";

    #[inline(always)]
    fn to_limbs(self) -> [u64; 3] {
        F192::to_limbs(self)
    }
    #[inline(always)]
    fn from_limbs(limbs: [u64; 3]) -> Self {
        F192::from_limbs(limbs)
    }
    #[inline(always)]
    fn mul_unreduced(self, rhs: Self) -> F192Unreduced {
        F192::mul_unreduced(self, rhs)
    }
    #[inline(always)]
    fn mul_base(self, k: F64) -> Self {
        F192::mul_base(self, k)
    }
    #[inline(always)]
    fn mul_base_unreduced(self, k: F64) -> F192Unreduced {
        F192::mul_base_unreduced(self, k)
    }
    #[inline(always)]
    fn square(self) -> Self {
        F192::square(self)
    }
    #[inline(always)]
    fn inv(self) -> Self {
        F192::inv(self)
    }
    #[inline(always)]
    fn from_challenge(c: F192) -> Self {
        c
    }
    #[inline(always)]
    fn to_scalar(self) -> F192 {
        self
    }
    fn eq_table(r: &[Self]) -> Vec<Self> {
        crate::lv::primitives::multilinear::eq_table(r)
    }
    fn powers(x: Self, n: usize) -> Vec<Self> {
        super::powers(x, n)
    }
    #[inline]
    fn poly_eval(coeffs: &[Self], x: Self) -> Self {
        crate::lv::primitives::multilinear::poly_eval(coeffs, x)
    }
}

impl Ext<2> for F128 {
    type Unreduced = F128Unreduced;
    const ZERO: Self = F128::ZERO;
    const ONE: Self = F128::ONE;
    const NAME: &'static str = "E2";

    #[inline(always)]
    fn to_limbs(self) -> [u64; 2] {
        [self.c0, self.c1]
    }
    #[inline(always)]
    fn from_limbs(limbs: [u64; 2]) -> Self {
        Self::new(limbs[0], limbs[1])
    }
    #[inline(always)]
    fn mul_unreduced(self, rhs: Self) -> F128Unreduced {
        F128::mul_unreduced(self, rhs)
    }
    #[inline(always)]
    fn mul_base(self, k: F64) -> Self {
        F128::mul_base(self, k)
    }
    #[inline(always)]
    fn mul_base_unreduced(self, k: F64) -> F128Unreduced {
        F128::mul_base_unreduced(self, k)
    }
    #[inline(always)]
    fn square(self) -> Self {
        F128::square(self)
    }
    #[inline(always)]
    fn inv(self) -> Self {
        F128::inv(self)
    }
    #[inline(always)]
    fn from_challenge(c: F192) -> Self {
        Self::new(c.c0, c.c1)
    }
    #[inline(always)]
    fn to_scalar(self) -> F192 {
        F192::new(self.c0, self.c1, 0)
    }
}

/// The self-test of `E2` (`kat::field` style): field laws on a fixed pseudo-random sample, `a^(2^128) = a`,
/// inverses, squares and mixed products against the plain product. Panics on a failure.
pub fn self_check() {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut rnd = || F128::new(next(), next());
    // X is a root of X^2 + xX + 1, and not in K: the Frobenius moves it to the other root (irreducibility).
    assert_eq!(F128::X * F128::X, F128::new(1, 2));
    assert_eq!(F128::X.pow(1u128 << 64), F128::new(2, 1), "X^2 + xX + 1 is irreducible over K");
    for _ in 0..64 {
        let (a, b, c) = (rnd(), rnd(), rnd());
        assert_eq!(a * b, b * a);
        assert_eq!((a * b) * c, a * (b * c));
        assert_eq!(a * (b + c), a * b + a * c);
        assert_eq!(a.square(), a * a);
        assert_eq!(a.pow(1u128 << 127).square(), a, "a^(2^128) = a");
        if a != F128::ZERO {
            assert_eq!(a * a.inv(), F128::ONE);
        }
        let k = F64(b.c0);
        assert_eq!(a.mul_base(k), a * F128::from(k));
        assert_eq!((a.mul_unreduced(b) ^ c.mul_base_unreduced(k) ^ F128Unreduced::from(b)).reduce(), a * b + c * F128::from(k) + b);
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn e2_self_check() {
        super::self_check();
    }
}
