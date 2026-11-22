// Vendored from leanVM 0b850750 + the pr/all crate diff (04fba039b..edd857be9) `crates/keccak_gkr/src/protocol.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The claims the layers pass along, and what forming the next one takes.
//!
//! A [`Claim`] is a weighted sum of the bits of one state per segment. With `bit(y, j, i)` the
//! bit at position `j` of instance `i` of pack `y`, the claimed value is
//!
//! ```text
//!     sum over segments, packs y, positions j, instances i of
//!         eq(point, (y, segment)) * weights[j] * mu[i] * bit(y, j, i)
//! ```
//!
//! One layer turns a claim on the states after a round into a claim on the states before it.
//!
//! lvm2 E2-K: generic over the field of the weights and challenges ([`Ext`]): `F192` (E3) or `F128` (E2).

use std::iter::Sum;
use std::ops::{AddAssign, Mul};

use crate::lv::primitives::field::{Ext, F64, F192};

use crate::lv::keccak_gkr::keccak::{BITS, along};
use crate::lv::keccak_gkr::rmfe::{EMBED_BITS, PACK, RMFE};
use crate::lv::keccak_gkr::witness::Shape;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim<F = F192> {
    pub value: F,
    /// The weight of each instance of a pack.
    pub mu: [F; PACK],
    /// A pack index, then a segment index.
    pub point: Vec<F>,
    /// The weight of each bit position.
    pub weights: Vec<F>,
}

/// The instance weights of a claim made at the polynomial point `s`: the value at `s` of each
/// unit vector's embedding.
pub fn mu_at<F: Ext<W>, const W: usize>(s: F) -> [F; PACK] {
    let powers = F::powers(s, EMBED_BITS);
    std::array::from_fn(|i| {
        (0..EMBED_BITS)
            .filter(|b| RMFE.emb[i] >> b & 1 == 1)
            .map(|b| powers[b])
            .sum()
    })
}

pub fn dot<T: Copy + Mul<Output = T> + Sum>(a: &[T], b: &[T]) -> T {
    a.iter().zip(b).map(|(&x, &y)| x * y).sum()
}

/// The weights of the claim a layer leaves on the state before `chi`.
///
/// The layer ends with `t[k] = sum_j eq[j] * T[j + k]` for `k` in `0..3`, which `beta` batches
/// into one weighted sum of `T`.
pub fn chi_weights<T: Copy + Default + AddAssign + Mul<Output = T>>(eq: &[T], beta: T) -> Vec<T> {
    let mut out = vec![T::default(); BITS];
    let beta2 = beta * beta;
    for j in 0..BITS {
        out[j] += eq[j];
        out[along(j, 1)] += beta * eq[j];
        out[along(j, 2)] += beta2 * eq[j];
    }
    out
}

/// The claim the layers start from, once its challenges are drawn, valued at zero: a random
/// combination of the output lanes as words, bit `z` of a word weighing `x^z`.
pub fn first_claim<F: Ext<W>, const W: usize>(shape: Shape, r_low: &[F], point: Vec<F>, r_lane: &[F]) -> Claim<F> {
    let mu: [F; PACK] = F::eq_table(r_low).try_into().expect("five low variables");
    assert_eq!(point.len(), shape.y_vars());
    let lanes = F::eq_table(r_lane);
    Claim {
        value: F::ZERO,
        mu,
        point,
        weights: (0..BITS)
            .map(|j| lanes[j / 64] * F::from(F64(1 << (j % 64))))
            .collect(),
    }
}

/// lvm2 E2-K: a span name by field, so that E3's and E2's passes time apart (`LVM_PROF=1`).
#[inline(always)]
pub const fn tag<const W: usize>(e3: &'static str, e2: &'static str) -> &'static str {
    if W == 3 { e3 } else { e2 }
}
