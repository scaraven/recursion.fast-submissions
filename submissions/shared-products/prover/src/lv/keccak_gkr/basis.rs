// Vendored from leanVM 0b850750 `crates/keccak_gkr/src/basis.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! A field element as a binary polynomial in a challenge `s`, and back.
//!
//! In the power basis of `s`, a sum of bits weighted by powers of `s` is the bits themselves, and
//! multiplying it by a weight is a carry-less product. So the prover moves its weights into that
//! basis once, accumulates unreduced polynomials in `s`, and evaluates each total at `s` at the end.

use crate::lv::primitives::field::Ext;
use crate::lv::primitives::field::gf2_64::mul_wide;

fn xor<const W: usize>(a: &mut [u64; W], b: &[u64; W]) {
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}

/// The transpose of a `64W x 64W` bit matrix, a row `W` words: bit `c` of row `r` becomes bit `r`
/// of row `c` (lvm2 R9-KG, W-generic for E2-K).
fn transpose_sq<const W: usize>(m: &[[u64; W]]) -> Vec<[u64; W]> {
    let mut out = vec![[0u64; W]; 64 * W];
    for rb in 0..W {
        for cb in 0..W {
            let mut block: [u64; 64] = std::array::from_fn(|i| m[64 * rb + i][cb]);
            crate::lv::keccak_gkr::witness::transpose64(&mut block);
            for (j, &w) in block.iter().enumerate() {
                out[64 * cb + j][rb] = w;
            }
        }
    }
    out
}

/// The map from a field element to its coefficients on `1, s, ..., s^(64W - 1)` (lvm2 E2-K: any [`Ext`] of `W`
/// words).
pub struct PowerBasis<const W: usize> {
    tables: Vec<[[u64; W]; 256]>,
}

impl<const W: usize> PowerBasis<W> {
    /// `None` when `s` lies in a proper subfield, where its powers do not span the field.
    ///
    /// lvm2 R9-KG: the same tables as leanVM's bit-by-bit build (the inverse is unique): the two
    /// `64W x 64W` bit transposes are `W^2` 64 x 64 block transposes each, and the elimination works
    /// on whole rows. [`Self::with_top`] also returns `s^(64W)`, the last power it walks to.
    pub fn new<F: Ext<W>>(s: F) -> Option<Self> {
        Self::with_top(s).map(|(basis, _)| basis)
    }

    /// [`Self::new`] and `s^(64W)`.
    pub fn with_top<F: Ext<W>>(s: F) -> Option<(Self, F)> {
        let n = 64 * W;
        // Row `b` of `powers` is `s^b`; its transpose has bit `r` of every power in row `r`.
        let mut powers = vec![[0u64; W]; n];
        let mut power = F::ONE;
        for p in powers.iter_mut() {
            *p = power.to_limbs();
            power *= s;
        }
        let bits = transpose_sq(&powers);
        // Gauss-Jordan on `[bits | identity]`.
        let mut rows: Vec<([u64; W], [u64; W])> = (0..n)
            .map(|r| {
                let mut id = [0u64; W];
                id[r / 64] = 1 << (r % 64);
                (bits[r], id)
            })
            .collect();
        for b in 0..n {
            let (word, bit) = (b / 64, b % 64);
            let pivot = (b..n).find(|&r| rows[r].0[word] >> bit & 1 == 1)?;
            rows.swap(b, pivot);
            let (pa, pi) = rows[b];
            // Branch-free: a row takes the pivot row under an all-ones mask (the pivot row's own is zero).
            for (r, row) in rows.iter_mut().enumerate() {
                let mask = (0u64.wrapping_sub(row.0[word] >> bit & 1)) & !(0u64.wrapping_sub(u64::from(r == b)));
                for (x, y) in row.0.iter_mut().zip(&pa) {
                    *x ^= y & mask;
                }
                for (x, y) in row.1.iter_mut().zip(&pi) {
                    *x ^= y & mask;
                }
            }
        }
        // Row `b` of the inverse is coefficient `b` as a function of the element's bits; its
        // transpose's row `r` is the coefficients bit `r` contributes.
        let inverse: Vec<[u64; W]> = rows.iter().map(|row| row.1).collect();
        let columns = transpose_sq(&inverse);
        let tables = (0..8 * W)
            .map(|k| {
                let mut t = [[0u64; W]; 256];
                for byte in 1..256usize {
                    let low = byte.trailing_zeros() as usize;
                    t[byte] = t[byte & (byte - 1)];
                    xor(&mut t[byte], &columns[8 * k + low]);
                }
                t
            })
            .collect();
        Some((Self { tables }, power))
    }

    pub fn to_poly<F: Ext<W>>(&self, a: F) -> [u64; W] {
        let a = a.to_limbs();
        let mut p = [0u64; W];
        for (k, table) in self.tables.iter().enumerate() {
            xor(&mut p, &table[(a[k / 8] >> (8 * (k % 8))) as usize & 0xff]);
        }
        p
    }
}

/// The sum of every subset of eight weights, indexed by the byte whose bits pick it.
pub fn byte_sums<T: Copy + Default + std::ops::Add<Output = T>>(weights: &[T; 8]) -> [T; 256] {
    let mut t = [T::default(); 256];
    for (bit, &w) in weights.iter().enumerate() {
        for byte in 1usize << bit..2 << bit {
            t[byte] = t[byte - (1 << bit)] + w;
        }
    }
    t
}

/// Evaluation at `s` of binary polynomials of at most `8 * n_bytes` coefficients.
pub struct PolyEval<F, const W: usize> {
    tables: Vec<[F; 256]>,
}

impl<F: Ext<W>, const W: usize> PolyEval<F, W> {
    pub fn new(s: F, n_bytes: usize) -> Self {
        Self {
            tables: F::powers(s, 8 * n_bytes)
                .as_chunks::<8>()
                .0
                .iter()
                .map(byte_sums)
                .collect(),
        }
    }

    /// lvm2 R9-KG: the polynomial's bytes are `words`' (at most the table's), so one table of the
    /// largest size serves every shorter polynomial.
    #[inline]
    pub fn eval(&self, words: &[u64]) -> F {
        let mut acc = F::ZERO;
        for (k, table) in self.tables.iter().take(8 * words.len()).enumerate() {
            acc += table[(words[k / 8] >> (8 * (k % 8))) as usize & 0xff];
        }
        acc
    }
}

/// The polynomial whose word `i` starts `acc[i]`.
#[inline(always)]
pub fn carry<const N: usize, const M: usize>(acc: &[u128; N]) -> [u64; M] {
    let mut out = [0u64; M];
    for (i, &x) in acc.iter().enumerate() {
        out[i] ^= x as u64;
        out[i + 1] ^= (x >> 64) as u64;
    }
    out
}

/// `acc += a * b`, on binary polynomials.
#[inline(always)]
pub fn add_mul<const A: usize, const B: usize, const N: usize>(acc: &mut [u64; N], a: &[u64; A], b: &[u64; B]) {
    for (i, &a) in a.iter().enumerate() {
        for (k, &b) in b.iter().enumerate() {
            let p = mul_wide(a, b);
            acc[i + k] ^= p as u64;
            acc[i + k + 1] ^= (p >> 64) as u64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lv::primitives::field::F192;
    use crate::lv::primitives::test_rng::Rng;

    #[test]
    fn power_basis_round_trips_and_products_are_carryless() {
        let mut rng = Rng::new(11);
        let s = rng.ext();
        let basis = PowerBasis::new(s).expect("a generic element");
        let eval = PolyEval::new(s, 40);
        for _ in 0..50 {
            let (a, b) = (rng.ext(), rng.next_u64());
            let pa = basis.to_poly(a);
            assert_eq!(eval.eval(&[pa[0], pa[1], pa[2], 0, 0]), a);
            let acc: [u128; 3] = std::array::from_fn(|k| mul_wide(pa[k], b));
            let product: [u64; 4] = carry(&acc);
            let pb = eval.eval(&[b, 0, 0, 0, 0]);
            assert_eq!(eval.eval(&[product[0], product[1], product[2], product[3], 0]), a * pb);
        }
        assert!(PowerBasis::new(F192::ONE).is_none());
    }
}
