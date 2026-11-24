//! FORMAT6 v2.4 §6.4b, the verifier's side on refv's types (dev only, feature `verify`; `tools/r3v` puts it in
//! refv's `Stubs::rest` slot after §6.4a). The arithmetic is the Lean's (`Lvm6MbProg.lean`, normative):
//! - [`walk`] is `lvmBusProgG μ`: `e2SampleN gAB 5`, `verifyGkrGrandProductsG μ` (`gkrLayersG`, `gkrStepG`: `λ`,
//!   the eq-mode rounds, three children of `2^step` values, `claim = Σ_s λ^s·Π children_s`, `y`), `count ≠ 0`;
//!   leanVM's native `verify_gkr_grand_products` (`crates/verifier/src/bus.rs:36-76`) with PARAM's grinds.
//! - [`claims`] is `mbClaimsG`: `busFinalG` (`sideBlocksG`, `stackBlocksG`, `sidesG`, `bucketG`), `mbPartsG`,
//!   `mbValueG`, recomputed from the table descriptions alone (no prover form is trusted).

use r3mb::tables::{MbCol, MbTab, cpoly};
use r3mb::{G_AB, G_LAM, G_RD, G_Y, G_Y_LAST};
use crate::arith::{eq_eval, eq_table, multilinear_eval, poly_eval};
use crate::chain::VChain;
use crate::stack::{Maps, StackClaim};
use crate::vs::Deferred;
use crate::{E, Reject};

const ZERO: E = E::new(0, 0);
const ONE: E = E::new(1, 0);

/// Which check of §6.4b rejected (refv's `Reject::MiniBus`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MbCheck {
    /// Step `k`: `claim ≠ Σ_s λ^s·Π children_s`.
    Layer(usize),
    /// `count = 0`.
    CountZero,
}

/// Why §6.4b rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MbReject {
    /// The chain (`BODY` short, PoW, trace).
    Chain(Reject),
    /// Step `k`: `claim ≠ Σ_s λ^s·Π children_s` (Lean `gkrStepG`'s `require`).
    Layer(usize),
    /// `count = 0` (Lean `lvmBusProgG`'s `require`).
    CountZero,
}

impl From<Reject> for MbReject {
    fn from(r: Reject) -> Self {
        MbReject::Chain(r)
    }
}

/// Into refv's rejection: the chain's as itself, a check as `Reject::MiniBus`.
impl From<MbReject> for Reject {
    fn from(r: MbReject) -> Self {
        match r {
            MbReject::Chain(r) => r,
            MbReject::Layer(k) => Reject::MiniBus(MbCheck::Layer(k)),
            MbReject::CountZero => Reject::MiniBus(MbCheck::CountZero),
        }
    }
}

/// What the bus phase read (Lean `LBusG`), and the count root.
#[derive(Clone, Debug)]
pub struct Walked {
    pub alphas: Vec<E>,
    pub beta: E,
    pub point: Vec<E>,
    pub values: [E; 3],
    pub count: E,
}

/// **`lvmBusProgG μ`** on the chain.
pub fn walk(ch: &mut VChain, mu: usize) -> Result<Walked, MbReject> {
    let ab = ch.group(G_AB, 5)?;
    let roots = ch.read_e(2)?;
    let (shared, count) = (roots[0], roots[1]);
    let mut values = vec![shared, shared, count];
    let mut point: Vec<E> = Vec::new();
    let mut layer = mu;
    let mut k = 0;
    while layer > 0 {
        // `gkrLayersG`: one level when the remaining depth is odd, two otherwise
        let step = if layer % 2 == 1 { 1 } else { 2 };
        let lam = ch.group(G_LAM, 1)?[0];
        let mut claim = poly_eval(&values, lam);
        // `sumcheckE2 gRd claim (2^step + 1) point`: eq mode, message `c₁ … c_{2^step}`, `c₀ = claim + r·Σ`
        let mut rounds = Vec::with_capacity(point.len());
        for &r in &point {
            let tail = ch.read_e(1 << step)?;
            let c0 = claim + r * tail.iter().fold(ZERO, |a, &x| a + x);
            let c = ch.ground(G_RD)?;
            claim = poly_eval(&[vec![c0], tail].concat(), c);
            rounds.push(c);
        }
        let children: Vec<Vec<E>> = (0..3).map(|_| ch.read_e(1 << step)).collect::<Result<_, _>>()?;
        let products: Vec<E> = children.iter().map(|c| c.iter().fold(ONE, |a, &x| a * x)).collect();
        if claim != poly_eval(&products, lam) {
            return Err(MbReject::Layer(k));
        }
        let last = layer == step;
        let y = ch.group(if last { G_Y_LAST } else { G_Y }, step)?;
        values = children.iter().map(|c| multilinear_eval(c, &y)).collect();
        point = [y, rounds].concat();
        layer -= step;
        k += 1;
    }
    if count == ZERO {
        return Err(MbReject::CountZero);
    }
    Ok(Walked { alphas: ab[..4].to_vec(), beta: ab[4], point, values: [values[0], values[1], values[2]], count })
}

/// A claim of §6.4 on the stack (Lean `sumClaimG` on `C_main`, here the stack): `Σ_parts coef·eq_above(⟨τ, at⟩)·
/// eq(ζ.take τ, ·)` and its value.
#[derive(Clone, Debug)]
pub struct VClaim {
    /// `(coefficient, stack offset of the column's word 0, τ)`.
    pub parts: Vec<(E, usize, usize)>,
    pub zeta: Vec<E>,
    pub value: E,
}

impl VClaim {
    /// The weight at a stack point `x` (25 coordinates, row variables low): `Σ coef·eq(bits(at ≫ τ), x[τ..])·
    /// eq(ζ[..τ], x[..τ])` (FORMAT6 §6.5 placement).
    pub fn weight(&self, x: &[E]) -> E {
        self.parts.iter().fold(ZERO, |acc, &(k, at, tau)| {
            let sel = x[tau..].iter().enumerate().fold(ONE, |a, (b, &xi)| a * if (at >> tau) >> b & 1 == 1 { xi } else { ONE + xi });
            acc + k * sel * eq_eval(&self.zeta[..tau], &x[..tau])
        })
    }

    pub fn stack_claim(self) -> StackClaim<'static> {
        let v = self.value;
        (Box::new(move |x| self.weight(x)), v)
    }
}

fn kg(k: primitives::field::F64) -> E {
    E::new(k.0, 0)
}

/// A block of a side (Lean `VBlockG`): its table, `κ`, its form `(column or None, coefficient)` at unit weight.
struct VBlock {
    tab: usize,
    kappa: usize,
    form: Vec<(Option<usize>, E)>,
}

/// Lean `leafFormG eqα β k cnt`: `β + Σ_i eq(α, i)·coord_i` with `coord = ⟨sep, addr, cnt, val…⟩`.
fn leaf_form(eqa: &[E], beta: E, coords: &[r3mb::leaf::Coord]) -> Vec<(Option<usize>, E)> {
    let mut f = vec![(None, beta)];
    for (i, c) in coords.iter().enumerate() {
        f.extend(cpoly(c).into_iter().map(|(k, col)| (col, eqa[i] * kg(k))));
    }
    f
}

/// **`mbClaimsG`**: the three claims (push, pull, count) of what the bus phase read.
pub fn claims(tabs: &[MbTab], w: &Walked) -> Vec<VClaim> {
    let eqa = eq_table(&w.alphas);
    let zeta = &w.point;
    let mu = zeta.len();
    // `sideBlocksG`: per table, push = reads (count g·c) then seeds (count 1); pull = reads then finalizes; count =
    // the reads' count columns (unit weight, no β)
    let mut sides: [Vec<VBlock>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for (j, t) in tabs.iter().enumerate() {
        for f in t.flushes() {
            let s = if f.side == r3mb::tables::Side::Push { 0 } else { 1 };
            sides[s].push(VBlock { tab: j, kappa: t.tau, form: leaf_form(&eqa, w.beta, &f.coords) });
            if let Some(c) = f.count {
                sides[2].push(VBlock { tab: j, kappa: t.tau, form: vec![(Some(c), ONE)] });
            }
        }
    }
    (0..3)
        .map(|s| {
            // `stackBlocksG`: stable by κ descending, offsets end to end; `sidesG`: each block's `eqAboveG ⟨κ, off⟩ ζ`
            let mut order: Vec<usize> = (0..sides[s].len()).collect();
            order.sort_by_key(|&i| std::cmp::Reverse(sides[s][i].kappa));
            let mut weight = vec![ZERO; sides[s].len()];
            let mut off = 0usize;
            for i in order {
                let b = &sides[s][i];
                let sel: Vec<E> = (0..mu - b.kappa).map(|k| E::new(((off >> b.kappa) >> k & 1) as u64, 0)).collect();
                weight[i] = eq_eval(&sel, &zeta[b.kappa..]);
                off += 1 << b.kappa;
            }
            // `busFinalG`'s total: `v + 1 + Σ_b w_b`
            let total = weight.iter().fold(w.values[s] + ONE, |a, &x| a + x);
            let mut parts = Vec::new();
            let mut value = total;
            for (j, t) in tabs.iter().enumerate() {
                // `bucketG`: table `j`'s terms at their block weights
                let terms: Vec<(Option<usize>, E)> = sides[s]
                    .iter()
                    .zip(&weight)
                    .filter(|(b, _)| b.tab == j)
                    .flat_map(|(b, &wb)| b.form.iter().map(move |&(c, k)| (c, wb * k)))
                    .collect();
                let coef = |c: Option<usize>| terms.iter().filter(|m| m.0 == c).fold(ZERO, |a, m| a + m.1);
                let pt = &zeta[..t.tau];
                // `constG`: the constant terms and the fixed columns at their extensions
                value += coef(None);
                for (c, col) in t.cols.iter().enumerate() {
                    if let MbCol::Fix(v) = col {
                        let k = coef(Some(c));
                        if k != ZERO {
                            let ext: Vec<E> = v.iter().map(|&x| kg(x)).collect();
                            value += k * multilinear_eval(&ext, pt);
                        }
                    }
                }
                // `mbPartsG`: every committed column the side names, in column order
                for c in t.side_cols(s) {
                    let MbCol::Com { at } = t.cols[c] else { unreachable!() };
                    parts.push((coef(Some(c)), at, t.tau));
                }
            }
            VClaim { parts, zeta: zeta.clone(), value }
        })
        .collect()
}

/// **§6.4b** on the chain (right after §6.4a; the fingerprint's ground query is then 40 bytes): every check, then
/// claims 50–52 as `Deferred`s (their weights need no ring map).
pub fn verify(ch: &mut VChain, tabs: &[MbTab]) -> Result<Vec<Deferred>, MbReject> {
    Ok(verify_claims(ch, tabs)?.into_iter().map(|c| Box::new(move |_: &Maps| c.stack_claim()) as Deferred).collect())
}

/// [`verify`], the claims as [`VClaim`]s.
pub fn verify_claims(ch: &mut VChain, tabs: &[MbTab]) -> Result<Vec<VClaim>, MbReject> {
    r3mb::tables::check_static(tabs);
    let w = walk(ch, r3mb::tables::depth(tabs))?;
    Ok(claims(tabs, &w))
}
