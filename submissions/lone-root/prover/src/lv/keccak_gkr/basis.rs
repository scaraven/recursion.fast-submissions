// Vendored from leanVM 0b850750 `crates/keccak_gkr/src/basis.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! A field element as a binary polynomial in a challenge `s`, and back.
//!
//! In the power basis of `s`, a sum of bits weighted by powers of `s` is the bits themselves, and
//! multiplying it by a weight is a carry-less product. So the prover moves its weights into that
//! basis once, accumulates unreduced polynomials in `s`, and evaluates each total at `s` at the end.

use crate::lv::primitives::field::gf2_64::mul_wide;
use crate::lv::primitives::field::{F192, powers};

fn xor3(a: &mut [u64; 3], b: &[u64; 3]) {
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}

/// The transpose of a 192 x 192 bit matrix, a row three words: bit `c` of row `r` becomes bit `r`
/// of row `c`.
fn transpose192(m: &[[u64; 3]; 192]) -> [[u64; 3]; 192] {
    let mut out = [[0u64; 3]; 192];
    for rb in 0..3 {
        for cb in 0..3 {
            let mut block: [u64; 64] = std::array::from_fn(|i| m[64 * rb + i][cb]);
            crate::lv::keccak_gkr::witness::transpose64(&mut block);
            for (j, &w) in block.iter().enumerate() {
                out[64 * cb + j][rb] = w;
            }
        }
    }
    out
}

/// The map from a field element to its coefficients on `1, s, ..., s^191`.
pub struct PowerBasis {
    tables: Vec<[[u64; 3]; 256]>,
}

impl PowerBasis {
    /// `None` when `s` lies in a proper subfield, where its powers do not span the field.
    ///
    /// lvm2 R9-KG: the same tables as leanVM's bit-by-bit build (the inverse is unique): the two
    /// 192 x 192 bit transposes are nine 64 x 64 block transposes each, and the elimination works
    /// on whole rows. Also returns `s^192`, the last power it walks to.
    pub fn new(s: F192) -> Option<Self> {
        Self::with_top(s).map(|(basis, _)| basis)
    }

    /// [`Self::new`] and `s^192`.
    pub fn with_top(s: F192) -> Option<(Self, F192)> {
        // Row `b` of `powers` is `s^b`; its transpose has bit `r` of every power in row `r`.
        let mut powers = [[0u64; 3]; 192];
        let mut power = F192::ONE;
        for p in powers.iter_mut() {
            *p = power.to_limbs();
            power *= s;
        }
        let bits = transpose192(&powers);
        // Gauss-Jordan on `[bits | identity]`, a row a `[u64; 6]`.
        let mut rows: Vec<[u64; 6]> = (0..192)
            .map(|r| {
                let mut row = [0u64; 6];
                row[..3].copy_from_slice(&bits[r]);
                row[3 + r / 64] = 1 << (r % 64);
                row
            })
            .collect();
        for b in 0..192 {
            let (word, bit) = (b / 64, b % 64);
            let pivot = (b..192).find(|&r| rows[r][word] >> bit & 1 == 1)?;
            rows.swap(b, pivot);
            let pr = rows[b];
            // Branch-free: a row takes the pivot row under an all-ones mask (the pivot row's own is zero).
            for (r, row) in rows.iter_mut().enumerate() {
                let mask = (0u64.wrapping_sub(row[word] >> bit & 1)) & !(0u64.wrapping_sub(u64::from(r == b)));
                for (x, y) in row.iter_mut().zip(&pr) {
                    *x ^= y & mask;
                }
            }
        }
        // Row `b` of the inverse is coefficient `b` as a function of the element's bits; its
        // transpose's row `r` is the coefficients bit `r` contributes.
        let inverse: Vec<[u64; 3]> = rows.iter().map(|row| [row[3], row[4], row[5]]).collect();
        let columns = transpose192(inverse.as_slice().try_into().expect("192 rows"));
        let tables = (0..24)
            .map(|k| {
                let mut t = [[0u64; 3]; 256];
                for byte in 1..256usize {
                    let low = byte.trailing_zeros() as usize;
                    t[byte] = t[byte & (byte - 1)];
                    xor3(&mut t[byte], &columns[8 * k + low]);
                }
                t
            })
            .collect();
        Some((Self { tables }, power))
    }

    pub fn to_poly(&self, a: F192) -> [u64; 3] {
        let a = a.to_limbs();
        let mut p = [0u64; 3];
        for (k, table) in self.tables.iter().enumerate() {
            xor3(&mut p, &table[(a[k / 8] >> (8 * (k % 8))) as usize & 0xff]);
        }
        p
    }
}

/// The sum of every subset of eight weights, indexed by the byte whose bits pick it.
pub fn byte_sums(weights: &[F192; 8]) -> [F192; 256] {
    let mut t = [F192::ZERO; 256];
    for (bit, &w) in weights.iter().enumerate() {
        for byte in 1usize << bit..2 << bit {
            t[byte] = t[byte - (1 << bit)] + w;
        }
    }
    t
}

/// Evaluation at `s` of binary polynomials of at most `8 * n_bytes` coefficients.
pub struct PolyEval {
    tables: Vec<[F192; 256]>,
}

impl PolyEval {
    pub fn new(s: F192, n_bytes: usize) -> Self {
        Self {
            tables: powers(s, 8 * n_bytes)
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
    pub fn eval(&self, words: &[u64]) -> F192 {
        let mut acc = F192::ZERO;
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
