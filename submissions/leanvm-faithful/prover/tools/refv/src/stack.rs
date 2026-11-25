//! FORMAT6 §6.1 (the commitment and its OOD claim) and §6.5 (the ring-switch group and the `λ₀` batch of the
//! stack claims, `L:lib.rs:117` `verify_stacked_opening`).

use crate::arith::{eq_eval, powers};
use crate::chain::VChain;
use crate::shape::Shape;
use crate::{Digest, E, Part, Reject, Res, require};

/// A claim on the stack: its weight at a stack point (row variables low, slot variables high) and its value.
pub type StackClaim<'a> = (Box<dyn Fn(&[E]) -> E + 'a>, E);

pub struct Commit {
    pub cap0: Vec<Digest>,
    pub z0: Vec<E>,
    pub y0: E,
}

/// §6.1: `CAP(0)` · `B` · `G(g_ood[0])`, `D(M−1)` → `z₀ ∈ E^M` · `E(1)` → `y₀`. Claim 0: `q̃(z₀) = y₀`.
pub fn commit(ch: &mut VChain, sh: &Shape) -> Res<Commit> {
    ch.phase(Part::Commit);
    let l0 = &sh.levels[0];
    let cap0 = ch.read_cap(l0.lv)?;
    ch.bind()?;
    let z0 = ch.group(l0.grind_ood, sh.stack_log)?;
    let y0 = ch.read_e(1)?[0];
    Ok(Commit { cap0, z0, y0 })
}

impl Commit {
    /// Claim 0, the OOD claim: weight `eq(z₀, ·)`.
    pub fn claim(&self) -> StackClaim<'static> {
        let z = self.z0.clone();
        (Box::new(move |x| eq_eval(&z, x)), self.y0)
    }
}

/// The two ring-switch maps (`f₀ … f₇`, `g₀ … g₇` each) and `λ₀`.
pub struct Maps {
    pub tree_f: Vec<E>,
    pub tree_g: Vec<E>,
    pub sponge_f: Vec<E>,
    pub sponge_g: Vec<E>,
    pub lambda0: E,
}

/// §6.5: `B`, then the group `G(g_batch)`, `D(32)`: tree map (the ground draw is `f₀`), sponge map, then `λ₀`.
pub fn maps(ch: &mut VChain, sh: &Shape) -> Res<Maps> {
    ch.phase(Part::Batch);
    ch.bind()?;
    let v = ch.group(sh.grind_batch, 33)?;
    Ok(Maps {
        tree_f: v[0..8].to_vec(),
        tree_g: v[8..16].to_vec(),
        sponge_f: v[16..24].to_vec(),
        sponge_g: v[24..32].to_vec(),
        lambda0: v[32],
    })
}

/// FORMAT6 v2.2 §6.5 placement: a claim on a block of `2^μ` words at stack offset `off·2^μ` has weight
/// `eq(bits(off), x[μ..M])·W(x[..μ])`, the bits of `off` low first (`L:lib.rs` walk step 7, `Placement::eq_above`).
/// The tree block is the whole stack (`μ = M`, no selector); `SP` is `μ = 19`, `off = 35` (claims 15, 16).
pub fn placed<'a>(off: u64, mu: usize, w: impl Fn(&[E]) -> E + 'a) -> impl Fn(&[E]) -> E + 'a {
    move |x: &[E]| {
        let sel = x[mu..].iter().enumerate().fold(E::new(1, 0), |acc, (k, &xi)| {
            acc * if off >> k & 1 == 1 { xi } else { E::new(1, 0) + xi }
        });
        sel * w(&x[..mu])
    }
}

/// The batch: claim `k` has coefficient `λ₀^k`; the target and the basis WHIR evaluates at its terminal point.
/// Rejects more than `J₀` claims.
pub fn batch<'a>(sh: &Shape, lambda0: E, claims: Vec<StackClaim<'a>>) -> Res<(E, Box<dyn Fn(&[E]) -> E + 'a>)> {
    require(claims.len() <= sh.j0, Reject::StackedClaims)?;
    let scales = powers(lambda0, claims.len());
    let target = claims.iter().zip(&scales).fold(E::new(0, 0), |acc, ((_, v), &s)| acc + s * *v);
    let basis = move |x: &[E]| claims.iter().zip(&scales).fold(E::new(0, 0), |acc, ((w, _), &s)| acc + s * w(x));
    Ok((target, Box::new(basis)))
}
