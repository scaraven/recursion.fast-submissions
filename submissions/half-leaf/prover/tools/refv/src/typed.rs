//! FORMAT6 v2.4 §6.4a, the verifier's side on refv's types (dev only, feature `verify`): rows 1–12 read from the
//! chain with every check of the table and of Lean `typedProgE` up to the mini-bus, in its order:
//! - row 3: `final = A·B + C` (`zeroProgE`);
//! - row 7: `final = (v_A + γv_B + γ²(v_D + v_W))·(Σ region values + virt(r_y))` (`wireProgE`);
//! - row 9: `final = kern(r_y, r)·v_R` (`relayProgE`);
//! - row 12: `h(0) = accIn.y`, `h(1) = Σ_o eq(κ, o)·v_o`, `Φ_Q(line(t)) = h(t)` (`accProgE`), so that
//!   `accOut = (line(t), h(t))` holds at `Φ_Q`: §T's native accumulator check `Φ_Q(accOut.pt) = accOut.y`.
//!
//! Returns stack claims 46–49 (§6.4's claims 1–4) as [`crate::vs::Deferred`]s. The arithmetic is independent of the
//! prover's: `Φ_Q` entry by entry (43 factors), the region weights as products of `eq`s per region.

use primitives::field::F128;
use crate::arith::{eq_eval, poly_eval};
use crate::chain::VChain;
use crate::stack::{Maps, StackClaim, placed};
use crate::vs::Deferred;
use crate::{E, Reject};

use r3typed::circuit::{Circuit, PHI_VARS, REC_OFF, REC_VARS, Src, TReg, X_VARS, Y_VARS};
use r3typed::prove::{G_GAMMA, G_KAPPA, G_T, G_TAU, G_WIRE, G_ZERO};

/// Which check of §6.4a rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TyCheck {
    /// Row 3: the zerocheck's final claim is not `A·B + C`.
    Zerocheck,
    /// Row 7: the wiring's final claim.
    Wiring,
    /// Row 9: the relayout's final claim.
    Relayout,
    /// Row 12: `h(0) ≠ accIn.y`.
    AccIn,
    /// Row 12: `h(1) ≠ Σ_o eq(κ, o)·v_o`.
    AccOwn,
    /// Row 12: `Φ_Q(line(t)) ≠ h(t)`.
    AccPhi,
}

/// A rejection: by the chain (`BODY`, a nonce, the trace) or by a check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TyReject {
    Chain(Reject),
    Check(TyCheck),
}

/// Into refv's rejection: the chain's as itself, a check as `Reject::Typed`.
impl From<TyReject> for Reject {
    fn from(r: TyReject) -> Self {
        match r {
            TyReject::Chain(r) => r,
            TyReject::Check(c) => Reject::Typed(c),
        }
    }
}

impl From<Reject> for TyReject {
    fn from(r: Reject) -> Self {
        TyReject::Chain(r)
    }
}

pub type TyRes<T> = Result<T, TyReject>;

fn req(ok: bool, c: TyCheck) -> TyRes<()> {
    if ok { Ok(()) } else { Err(TyReject::Check(c)) }
}

pub fn to_f(e: E) -> F128 {
    F128::new(e.c0, e.c1)
}

pub fn to_e(f: F128) -> E {
    E::new(f.c0, f.c1)
}

fn to_fs(v: &[E]) -> Vec<F128> {
    v.iter().map(|&e| to_f(e)).collect()
}

/// What §6.4a leaves on the verifier's side.
#[derive(Clone, Debug)]
pub struct TyVOut {
    pub tau: Vec<E>,
    pub r_x: Vec<E>,
    pub abc: Vec<E>,
    pub gamma: E,
    pub r_y: Vec<E>,
    pub mats: Vec<E>,
    pub regions: Vec<E>,
    pub r: Vec<E>,
    pub v_r: E,
    pub kappa: Vec<E>,
    pub h: Vec<E>,
    pub t: E,
    /// `accOut = (line(t), h(t))`.
    pub acc_pt: Vec<E>,
    pub acc_y: E,
    /// The circuit's regions (the claims' weights).
    regs: Vec<TReg>,
}

/// `n` rounds of `count = 3` coefficients from `claim` (Lean `sumcheckE2`): eq mode reads `c₁, c₂` and derives
/// `c₀ = claim + r·(c₁ + c₂)`, plain mode reads `c₀, c₂` and derives `c₁ = claim + c₂`; each round `G(g)`; the next
/// claim is the round polynomial at the challenge.
fn rounds(ch: &mut VChain, mut claim: E, eq: &[Option<E>], g: u32) -> TyRes<(Vec<E>, E)> {
    let mut pt = Vec::with_capacity(eq.len());
    for &mode in eq {
        let m = ch.read_e(2)?;
        let poly = match mode {
            Some(r) => vec![claim + r * (m[0] + m[1]), m[0], m[1]],
            None => vec![m[0], claim + m[1], m[1]],
        };
        let c = ch.ground(g)?;
        pt.push(c);
        claim = poly_eval(&poly, c);
    }
    Ok((pt, claim))
}

/// §6.4a on the chain. `pub_words` are `PUB`'s lanes ([`r3typed::witness::pub_lanes`] of `HDR`), `acc_pt`, `acc_y`
/// are `HDR.accIn`.
pub fn verify_typed(ch: &mut VChain, circ: &Circuit, pub_words: &[u64], acc_pt: &[E], acc_y: E) -> TyRes<TyVOut> {
    assert_eq!(acc_pt.len(), PHI_VARS);
    // rows 1–3
    let tau = (0..X_VARS).map(|_| ch.ground(G_TAU)).collect::<Result<Vec<E>, _>>()?;
    let modes: Vec<Option<E>> = tau.iter().map(|&t| Some(t)).collect();
    let (r_x, fin) = rounds(ch, E::new(0, 0), &modes, G_ZERO)?;
    let abc = ch.read_e(3)?;
    req(fin == abc[0] * abc[1] + abc[2], TyCheck::Zerocheck)?;

    // rows 4–7
    let gamma = ch.ground(G_GAMMA)?;
    let g2 = gamma * gamma;
    let start = abc[0] + gamma * abc[1] + g2 * abc[2];
    let (r_y, fin) = rounds(ch, start, &vec![None; Y_VARS], G_WIRE)?;
    let mats = ch.read_e(4)?;
    let regions = ch.read_e(4)?;
    let ry_f = to_fs(&r_y);
    let virt = to_e(circ.virt(&ry_f, pub_words));
    let wg = mats[0] + gamma * mats[1] + g2 * (mats[2] + mats[3]);
    let zr = E::sum(regions.iter().copied()) + virt;
    req(fin == wg * zr, TyCheck::Wiring)?;

    // rows 8–9
    let (r, fin) = rounds(ch, regions[1], &vec![None; REC_VARS], G_WIRE)?;
    let v_r = ch.read_e(1)?[0];
    let kern = to_e(circ.relay_kern(&ry_f, &to_fs(&r)));
    req(fin == kern * v_r, TyCheck::Relayout)?;

    // rows 10–12
    let kappa = vec![ch.ground(G_KAPPA)?, ch.ground(G_KAPPA)?];
    let h = ch.read_e(PHI_VARS + 1)?;
    let t = ch.ground(G_T)?;
    let one = E::new(1, 0);
    let eqk = [(one + kappa[0]) * (one + kappa[1]), kappa[0] * (one + kappa[1]), (one + kappa[0]) * kappa[1], kappa[0] * kappa[1]];
    let own = (0..4).fold(E::new(0, 0), |a, o| a + eqk[o] * mats[o]);
    let b: Vec<E> = kappa.iter().chain(&r_x).chain(&r_y).copied().collect();
    let line: Vec<E> = acc_pt.iter().zip(&b).map(|(&a, &b)| a + t * (a + b)).collect();
    let ht = poly_eval(&h, t);
    req(h[0] == acc_y, TyCheck::AccIn)?;
    req(E::sum(h.iter().copied()) == own, TyCheck::AccOwn)?;
    req(to_e(circ.phi_q_direct(&to_fs(&line))) == ht, TyCheck::AccPhi)?;

    Ok(TyVOut { tau, r_x, abc, gamma, r_y, mats, regions, r, v_r, kappa, h, t, acc_pt: line, acc_y: ht, regs: circ.regs.clone() })
}

impl TyVOut {
    /// Stack claims 46–49 (weight at a 25-variable stack point, value), §6.4's order.
    pub fn stack_claims(&self) -> Vec<StackClaim<'static>> {
        let r = self.r.clone();
        let mut v: Vec<StackClaim<'static>> = vec![(Box::new(placed(REC_OFF as u64, REC_VARS, move |x: &[E]| eq_eval(&r, x))), self.v_r)];
        for (s, val) in [(Src::Sigma, self.regions[2]), (Src::Com, self.regions[0]), (Src::Ks, self.regions[3])] {
            let c = Circuit { regs: self.regs.clone(), ents: Vec::new(), outs: Vec::new(), qlt: Vec::new() };
            let ry = to_fs(&self.r_y);
            v.push((Box::new(move |x: &[E]| to_e(c.region_weight_at(s, &ry, &to_fs(x)))), val));
        }
        v
    }

    /// [`Self::stack_claims`] as `crate::vs::Stubs::rest`'s deferred claims (no ring map needed).
    pub fn deferred(&self) -> Vec<Deferred> {
        self.stack_claims()
            .into_iter()
            .map(|c| Box::new(move |_: &Maps| c) as Deferred)
            .collect()
    }

    /// §T's native accumulator check `Φ_Q(accOut.pt) = accOut.y` (`V_S`'s last check).
    pub fn acc_ok(&self, circ: &Circuit) -> bool {
        to_e(circ.phi_q_direct(&to_fs(&self.acc_pt))) == self.acc_y
    }
}
