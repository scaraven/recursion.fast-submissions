//! E2F (lvm2 S1, stage S2GF): the front's field-generic helpers and the E2 pieces of the opening's claims.
//!
//! The front (tape GKR, wire, KS GKR, KS link) runs over [`Ext`]: `F192` (E3, the S2GM bytes) or `F128` (E2 = K[X]/(X²
//! + xX + 1)). Its claims on `C_main` leave it in three forms:
//! - an E3 point claim (a public binary point, or the E3 front);
//! - an **E2 word claim** `Σ_b c·eq(z, b)·q(b) = a`, `z ∈ E2^m`, `c, a ∈ E2` (several terms may share a value): with
//!   `eq(z, b) = w₀(b) + w₁(b)·X` it is the two K-linear claims `(re, a.re)` then `(im, a.im)`, in place, the weight of
//!   coordinate `h` being `coord_h(c·eq(z, ·))` (`LvmTensorSwitch.tensorSwitch_E2`);
//! - a **row switch** (E2-S-switch §2) of 64 E2 bit slices at `z`: rows `t_j = Σ_i bit_j(s_i)·x^i`, `j = i + 64h`, 7 E3
//!   samples `r''`, `ρ_j = eq(r'', j)`; the claim `Σ_u W(u)·q(u) = Σ_j ρ_j t_j` with `W(u) = Σ_j ρ_j·bit_j(eq(z, u))`.
//!
//! All three E2 weights are `Φ(eq(z, ·))` for an F₂-linear `Φ : E2 → E3`, given by its 128 values on the bit basis
//! (bit `j < 64` of limb 0 is `x^j`, bit `64 + j` is `x^j·X`): an [`E2Term`].

use crate::lv::primitives::field::{Ext, F64, F128, F192};

pub(crate) use crate::lv::pcs::ring_switch::E2Fold;

/// `Φ : E2 → E3`, F₂-linear, by its values on E2's 128 bit-basis elements.
pub type Phi = [F192; 128];

/// The `j`-th bit-basis element of E2.
#[inline]
pub fn e2_basis(j: usize) -> F128 {
    if j < 64 { F128::new(1u64 << j, 0) } else { F128::new(0, 1u64 << (j - 64)) }
}

/// `Φ(a)`.
#[inline]
pub fn phi_apply(phi: &Phi, a: F128) -> F192 {
    let mut acc = F192::ZERO;
    for (limb, word) in [a.c0, a.c1].into_iter().enumerate() {
        let mut bits = word;
        while bits != 0 {
            acc += phi[64 * limb + bits.trailing_zeros() as usize];
            bits &= bits - 1;
        }
    }
    acc
}

/// `a ↦ coord_h(c·a)` embedded in E3 (`K ⊂ E3`, limb 0): a word claim's coordinate `h` with coefficient `c`.
pub fn coord_phi(c: F128, h: usize) -> Phi {
    std::array::from_fn(|j| {
        let p = c * e2_basis(j);
        F192::new(if h == 0 { p.c0 } else { p.c1 }, 0, 0)
    })
}

/// `a ↦ Φ(m·a)`.
pub fn phi_compose(phi: &Phi, m: F128) -> Phi {
    std::array::from_fn(|j| phi_apply(phi, m * e2_basis(j)))
}

/// `a ↦ λ·Φ(a)`.
pub fn phi_scale(phi: &Phi, lambda: F192) -> Phi {
    phi.map(|v| lambda * v)
}

/// E2's coordinate `h` of `a`, in E3.
#[inline]
pub fn coord(a: F128, h: usize) -> F192 {
    F192::new(if h == 0 { a.c0 } else { a.c1 }, 0, 0)
}

/// One term of an E2 claim's weight: `Φ(eq(point, ·))` on the aligned block `[offset, offset + 2^|point|)`.
#[derive(Clone, Debug)]
pub struct E2Term {
    pub offset: usize,
    pub point: Vec<F128>,
    pub phi: Phi,
    /// `Φ` is K-linear (a word claim's coordinate; then `Φ(1)`, `Φ(X)` determine it and the opening takes the cheap
    /// four-claim form, `basis::E6Term`); a row switch's `Φ` is only F₂-linear (an E2 ring)
    pub klin: bool,
}

/// The row switch (E2-S-switch §2): from the 64 E2 slices and the 7 E3 ring-map samples `r''`, the map
/// `Φ(β_j) = ρ_j = eq(r'', j)` (bit `k` of `j` against `r''_k`) and the target `σ = Σ_j ρ_j t_j`,
/// `t_j = Σ_i bit_j(s_i)·x^i`.
pub fn row_switch(slices: &[F128], r2: &[F192]) -> (Phi, F192) {
    assert_eq!(slices.len(), 64);
    assert_eq!(r2.len(), 7);
    let rho = crate::lv::primitives::multilinear::eq_table(r2);
    let phi: Phi = std::array::from_fn(|j| rho[j]);
    let mut sigma = F192::ZERO;
    for (j, &rj) in rho.iter().enumerate() {
        let t: u64 = slices
            .iter()
            .enumerate()
            .fold(0u64, |t, (i, s)| t | (((if j < 64 { s.c0 } else { s.c1 }) >> (j % 64)) & 1) << i);
        sigma += rj.mul_base(F64(t));
    }
    (phi, sigma)
}

/// `eq(r, k)` for `k < len` (the generic [`crate::lvm::link::eq_prefix`]).
pub fn eq_prefix<F: Ext<W>, const W: usize>(r: &[F], len: usize) -> Vec<F> {
    let nv = r.len();
    let mut out = vec![F::ZERO; len];
    let mut k = 0usize;
    while k < len {
        let mut b = if k == 0 { nv } else { (k.trailing_zeros() as usize).min(nv) };
        while (1usize << b) > len - k {
            b -= 1;
        }
        let mut hi = F::ONE;
        for t in b..nv {
            hi *= if (k >> t) & 1 == 1 { r[t] } else { F::ONE + r[t] };
        }
        let lo = F::eq_table(&r[..b]);
        for (j, x) in lo.iter().enumerate() {
            out[k + j] = hi * *x;
        }
        k += 1 << b;
    }
    out
}

/// `lt̃_m(x) = Σ_{k < m} eq(x, k)` (the generic [`crate::lvm::link::lt_mle`]).
pub fn lt_mle<F: Ext<W>, const W: usize>(x: &[F], m: usize) -> F {
    let mut total = F::ZERO;
    let mut above = F::ONE;
    for t in (0..x.len()).rev() {
        if (m >> t) & 1 == 1 {
            total += above * (F::ONE + x[t]);
            above *= x[t];
        } else {
            above *= F::ONE + x[t];
        }
    }
    if m >> x.len() != 0 { F::ONE } else { total }
}

/// `eq(a, b) = Π (1 + a_t + b_t)` (characteristic 2).
pub fn eq_eval<F: Ext<W>, const W: usize>(a: &[F], b: &[F]) -> F {
    a.iter().zip(b).map(|(&x, &y)| F::ONE + x + y).fold(F::ONE, |p, t| p * t)
}

/// `eq(r, ·)` on a boolean point `x` (bits of `x`, low first).
pub fn eq_at_index<F: Ext<W>, const W: usize>(r: &[F], x: usize) -> F {
    r.iter().enumerate().fold(F::ONE, |p, (t, &v)| p * if (x >> t) & 1 == 1 { v } else { F::ONE + v })
}

/// Bit weights as byte tables: `t[b][v] = Σ_{j<8} w[8b + j]·bit_j(v)`.
pub fn byte_tables<F: Ext<W>, const W: usize>(w: &[F; 64]) -> Vec<[F; 256]> {
    (0..8)
        .map(|b| {
            let mut t = [F::ZERO; 256];
            for v in 1..256usize {
                let low = v & v.wrapping_neg();
                t[v] = t[v ^ low] + w[8 * b + low.trailing_zeros() as usize];
            }
            t
        })
        .collect()
}

#[inline]
pub fn bitdot<F: Ext<W>, const W: usize>(t: &[[F; 256]], x: u64) -> F {
    let mut acc = F::ZERO;
    for (b, tb) in t.iter().enumerate() {
        acc += tb[((x >> (8 * b)) & 255) as usize];
    }
    acc
}

/// `out[q] = Σ_y bit_q(words[y])·eq[y]` for the 64 bits `q`.
pub fn fold_1b_rows<F: Ext<W>, const W: usize>(words: &[F64], eq: &[F]) -> [F; 64] {
    assert_eq!(words.len(), eq.len());
    if let Some(e3) = as_e3::<F, W>(eq) {
        return crate::lv::pcs::ring_switch::fold_1b_rows(words, e3).map(from_e3::<F, W>);
    }
    crate::lv::parallel::fold_reduce(
        words.len(),
        || [F::ZERO; 64],
        |acc, i| {
            let w = eq[i];
            let mut bits = words[i].0;
            while bits != 0 {
                acc[bits.trailing_zeros() as usize] += w;
                bits &= bits - 1;
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    )
}

/// `v` as `F192` values when `F` is `F192`.
#[inline]
pub fn as_e3<F: Ext<W>, const W: usize>(v: &[F]) -> Option<&[F192]> {
    (std::any::TypeId::of::<F>() == std::any::TypeId::of::<F192>())
        // SAFETY: `F` is `F192`, so the slice's type is unchanged.
        .then(|| unsafe { std::slice::from_raw_parts(v.as_ptr().cast::<F192>(), v.len()) })
}

/// An E3 value as `F` when `F` is `F192`.
#[inline]
pub fn from_e3<F: Ext<W>, const W: usize>(x: F192) -> F {
    debug_assert!(W == 3, "an E3 value as F192");
    let l = x.to_limbs();
    F::from_limbs(std::array::from_fn(|k| l[k]))
}

/// `F` as `F128` when `F` is `F128` (`W = 2`).
#[inline]
pub fn to_e2<F: Ext<W>, const W: usize>(x: F) -> F128 {
    assert_eq!(W, 2, "an E2 value");
    let l = x.to_limbs();
    F128::new(l[0], l[1])
}

/// `F` as the E3 value of an E3 front (`W = 3`).
#[inline]
pub fn to_e3<F: Ext<W>, const W: usize>(x: F) -> F192 {
    assert_eq!(W, 3, "an E3 value");
    let l = x.to_limbs();
    F192::new(l[0], l[1], l[2])
}

/// The root OOD pin's answer (S2GF, `LvmE2FPin`): `Σ_u eq(z, u)·C(u)` over the committed `2^|z|`-word table whose
/// first `words.len()` words are `words` (the rest zero), `z_0` the index's least significant variable. `even`: the
/// table is the small shape's physical one, word `2w` = `words[w]` and the odd words zero.
pub fn pin_value(z: &[F192], words: &[F64], even: bool) -> F192 {
    let (lead, z) = if even { (F192::ONE + z[0], &z[1..]) } else { (F192::ONE, z) };
    assert!(words.len() <= 1 << z.len());
    let lo_vars = z.len().min(12);
    let (eq_lo, eq_hi) = (
        crate::lv::primitives::multilinear::eq_table(&z[..lo_vars]),
        crate::lv::primitives::multilinear::eq_table(&z[lo_vars..]),
    );
    let block = 1usize << lo_vars;
    let n_blocks = words.len().div_ceil(block);
    let total = crate::lv::parallel::fold_reduce(
        n_blocks,
        || crate::lv::primitives::field::F192Unreduced::ZERO,
        |acc, h| {
            let ws = &words[h * block..((h + 1) * block).min(words.len())];
            let mut inner = crate::lv::primitives::field::F192Unreduced::ZERO;
            for (e, &w) in eq_lo.iter().zip(ws) {
                if w.0 != 0 {
                    inner ^= e.mul_base_unreduced(w);
                }
            }
            *acc ^= eq_hi[h].mul_unreduced(inner.reduce());
        },
        |a, b| a ^ b,
    );
    lead * total.reduce()
}
