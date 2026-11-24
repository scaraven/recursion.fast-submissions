//! FORMAT6 §6.6: the opening, `L:whir.rs:229` `verify_whir` with the v6 items. Changes from leanVM, all FORMAT6's:
//! caps instead of roots (`CAP(i+1)` absorbed after the high part, then a bind `B`), a nonce on every group (leanVM
//! grinds only where its numerator needs it), the PoW on the top bits of lane 2, frozen per-level grinds and query
//! counts (`Shape`), and the level-0 leaf as the 46 occupied lanes. The checks themselves are leanVM's.

use crate::arith::{FoldRound, eq_eval, fold_row, induced_weight, multilinear_eval, novel_eval, poly_eval, powers};
use crate::chain::VChain;
use crate::merkle::{lanes_e, lanes0, open, positions};
use crate::shape::Shape;
use crate::{Digest, E, K, Part, Reject, Res, require};
use verifier::Subspace;

/// A claim glued into the running claim at level `fold_start` (`L:whir.rs:207`).
struct Glued {
    scalar: E,
    fold_start: usize,
    weight_at: Box<dyn Fn(&[E]) -> E>,
}

/// What the walk leaves for the KAT checkpoints.
#[derive(Clone, Debug, Default)]
pub struct Trail {
    pub alphas: Vec<E>,
    pub positions: Vec<Vec<usize>>,
    pub claim_end: E,
}

/// Verify `Σ_b basis(b)·q(b) = target` against `cap0`, the committed stack `q` (`M` variables, slot bits high).
pub fn verify(ch: &mut VChain, sh: &Shape, target: E, cap0: Vec<Digest>, basis: &dyn Fn(&[E]) -> E) -> Res<Trail> {
    let n_levels = sh.levels.len();
    let mut claim = target;
    let mut alphas: Vec<E> = Vec::new();
    let mut glued: Vec<Glued> = Vec::new();
    let mut cap = cap0;
    let mut trail = Trail::default();

    for (i, l) in sh.levels.iter().enumerate() {
        ch.phase(Part::Level(i));
        // `ℓ` fold rounds: `E(4)` (`v_G, v_F, t₀, t₁`) · `G(g_fold)` → `α` · `D(1)` → `β`.
        let mut rounds = Vec::with_capacity(l.fold);
        for _ in 0..l.fold {
            let t = ch.read_e(4)?;
            let alpha = ch.ground(l.grind_fold)?;
            let beta = ch.draw()?;
            let r = FoldRound { alpha, beta };
            claim = r.next_claim(claim, &t);
            alphas.push(alpha);
            rounds.push(r);
        }
        let mu = sh.stack_log - alphas.len();
        assert_eq!(mu, l.log_msg_cols as usize);
        let sub = Subspace::new(mu);
        let lanes_of = |leaf: &[u8]| if i == 0 { lanes0(leaf, sh.lanes) } else { lanes_e(leaf) };

        if i + 1 == n_levels {
            // `E(final)` · `G(g_q)`, `D(d−1)` → positions · `OPEN` · `tail` plain rounds `R(2, g_tail)`.
            let folded = ch.read_e(sh.final_coeffs)?;
            let pos = positions(ch, l)?;
            for &p in &pos {
                let leaf = open(ch, i, l, &cap, p)?;
                let x = K(p as u64);
                let v = fold_row(lanes_of(leaf), x, &rounds);
                require(v == novel_eval(&folded, &sub.at(x)), Reject::FinalQuery)?;
            }
            trail.positions.push(pos);
            ch.phase(Part::Tail);
            let mut tail = Vec::with_capacity(sh.tail_rounds);
            for _ in 0..sh.tail_rounds {
                // plain mode: `c₀, c₂` sent, `c₁ = claim + c₂` (`L:transcript.rs:221`).
                let m = ch.read_e(2)?;
                let r = ch.ground(sh.grind_tail)?;
                claim = poly_eval(&[m[0], claim + m[1], m[1]], r);
                tail.push(r);
            }
            // Each glued claim at the terminal point: the alphas drawn after it, then the tail (`L:whir.rs:281`).
            let point = [&alphas[..], &tail].concat();
            let f0 = sh.levels[0].fold;
            let mut weight = basis(&[&point[f0..], &point[..f0]].concat());
            for g in &glued {
                weight += g.scalar * (g.weight_at)(&point[g.fold_start..]);
            }
            let terminal = weight * multilinear_eval(&folded[..1 << mu], &tail);
            require(terminal == claim, Reject::Terminal)?;
            trail.alphas = alphas;
            trail.claim_end = claim;
            return Ok(trail);
        }

        // `E(ℓ)` the high part · `CAP(i+1)` · `B` · `G(g_ood[i+1])`, `D(ν−1)` → `z` · `E(1)` → `y` ·
        // `G(g_q[i])`, `D(d−1)` → positions · `D(1)` → `λ` · `OPEN(i)` (v2.2: the OOD grind is level i+1's).
        let next = &sh.levels[i + 1];
        let high = ch.read_e(l.fold)?;
        let next_cap = ch.read_cap(next.lv)?;
        ch.bind()?;
        let z = ch.group(next.grind_ood, mu)?;
        let y = ch.read_e(1)?[0];
        let pos = positions(ch, l)?;
        let lambda = ch.draw()?;
        let qw = powers(lambda, pos.len());
        let mut batched = E::new(0, 0);
        for (&p, &w) in pos.iter().zip(&qw) {
            let leaf = open(ch, i, l, &cap, p)?;
            let x = K(p as u64);
            let what = sub.at(x);
            let correction = novel_eval(&high, &what) * what[mu];
            batched += w * (fold_row(lanes_of(leaf), x, &rounds) + correction);
        }
        // The OOD claim takes `λ`, the query batch `λ²` times its own powers of `λ` (`L:whir.rs:330`).
        claim += lambda * y;
        glued.push(Glued { scalar: lambda, fold_start: alphas.len(), weight_at: Box::new(move |x| eq_eval(&z, x)) });
        claim += lambda * lambda * batched;
        let queries: Vec<u64> = pos.iter().map(|&p| p as u64).collect();
        glued.push(Glued {
            scalar: lambda * lambda,
            fold_start: alphas.len(),
            weight_at: Box::new(move |x| induced_weight(mu, &queries, &qw, x)),
        });
        trail.positions.push(pos);
        cap = next_cap;
    }
    unreachable!("the final level returns")
}
