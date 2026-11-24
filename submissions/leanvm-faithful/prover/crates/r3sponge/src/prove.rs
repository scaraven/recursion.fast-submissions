//! FORMAT6 v2.4 §6.3 on the v6 transcript: caller (C1, C2), the core (leanVM's `Witness::prove` at `κ_s = 13`), the
//! link (L1–L3), and the stack claims 15, 16, 17–45 of §6.5 in that order.
//!
//! The link (Lean `ksLinkProgE2 13 xl rows`; season 1's `lvm::link::prove_ks`, ported to `F128`): with `ω_l =
//! eq(λ, l)`, the summand `Sc(ρ, k)·Y^ω(k) + eq(ρ, k)·(in^ω(k) + Msg^ω(k))`, `Sc(ρ, k) = [k+1 ∈ rows]·eq(ρ, k+1)`, sums
//! to 0 over `k < 2^13` exactly when every row's input is `cont·Y(x−1) + Msg` (characteristic 2; `LvmE2VKS.contShiftF_eq`).
//! Thirteen plain degree-2 rounds (`c₀, c₂` sent, `c₁ = claim + c₂`) bind `k` to `ρ'`; then `Y^ω, in^ω, M^ω, X^ω` at
//! `ρ'`, with `Msg^ω(ρ') = M + sel·X`, `sel = Π_{j ≥ xl} ρ'_j` (the rows from `split` are the top `2^xl` rows).

use keccak_gkr::{Opening, OutputClaim, WordOpening};
use primitives::field::{F64, F128};
use primitives::multilinear::{eq_table, mle_eval, poly_eval};
use primitives::transcript::ProverState;
use r3core::claim::PClaim;
use r3core::layout::{MSG_LANES, SLOT_SP, SP_LOG, SP_MU, SP_OFF, SP_ROWS, SPLIT, XL, idx, m_idx, sp_idx, x_idx, y_idx, y_off, Y_MU};

use crate::witness::{SpongeWitness, msg_word, region_block, sp_block};

const LANES: usize = 25;
/// FORMAT6 §6.3: every caller and link group has numerator 1 (`G(1)`); the shift rounds are `R(2, 2)`.
pub const G_POINT: u32 = 1;
/// The link's lane point `λ ∈ E^5`.
pub const LANE_BITS: usize = 5;

/// A dev tamper (tests): one prover message of §6.3 off by one, the prover going on with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tamper {
    None,
    /// `v₇` (C2), also handed to the core as the output claim.
    V7,
    /// `c₀` of shift round `k` (L2).
    LinkRound(usize),
    /// `vals[j]` (L3: 0 `Y`, 1 `in`, 2 `M`, 3 `X`).
    Vals(usize),
}

fn flip(x: F128, on: bool) -> F128 {
    if on { x + F128::ONE } else { x }
}

/// What §6.3 leaves.
pub struct SpongeOut {
    /// C1: the instance point `r ∈ E^13`.
    pub r: Vec<F128>,
    /// C2: `v_l = Ỹ_l(r)` (as sent).
    pub v: [F128; LANES],
    /// The core's middle opening on `SP` (claim 16): point `(r, slot)` (19 coordinates), value `c_out`.
    pub outputs: WordOpening,
    /// The core's input opening on `SP` (claim 15): the 64 slices at `(low, pack, slot)` (19 coordinates).
    pub inputs: Opening,
    /// L1: `ρ ∈ E^13`, `λ ∈ E^5`.
    pub rho: Vec<F128>,
    pub lambda: Vec<F128>,
    /// L2: `ρ'`.
    pub rho_p: Vec<F128>,
    /// L3: `Y, in, M, X` (as sent).
    pub vals: [F128; 4],
    /// Stack claims 15, 16, 17–41, 42–45 (§6.5's order; 31 claims).
    pub claims: Vec<PClaim>,
}

/// §6.3 on `ps` (a v6 state), after the tree batch's `E(64)`. `stack` is the whole `2^25`-word stack, with `SP`
/// and `Y` written by `w`'s [`SpongeWitness::generate`].
pub fn prove_sponge(ps: &mut ProverState, w: &SpongeWitness, stack: &[F64]) -> SpongeOut {
    prove_sponge_with(ps, w, stack, Tamper::None)
}

/// `ρ`-style point of `n` coordinates, one `G(1)` group each.
fn point_groups(ps: &mut ProverState, n: usize) -> Vec<F128> {
    (0..n)
        .map(|_| {
            ps.grind(G_POINT);
            ps.sample()
        })
        .collect()
}

/// [`prove_sponge`] with a [`Tamper`].
pub fn prove_sponge_with(ps: &mut ProverState, w: &SpongeWitness, stack: &[F64], tamper: Tamper) -> SpongeOut {
    assert!(ps.chain().is_some(), "§6.3 runs on the v6 transcript");
    // C1: r₀ … r₁₂, one G(1) each.
    let r = point_groups(ps, SP_LOG);
    // C2: v_l = Ỹ_l(r).
    let mut v: [F128; LANES] = std::array::from_fn(|l| mle_eval(&stack[y_idx(0, l)..][..SP_ROWS], &r));
    v[7] = flip(v[7], tamper == Tamper::V7);
    ps.add_scalars(&v);
    // The core: leanVM's reduction on the SP block (rows 6–10 of §6.2 at κ_s = 13).
    let openings = tracing::info_span!("sponge core")
        .in_scope(|| w.keccak.prove(ps, sp_block(stack), &OutputClaim { instance: r.clone(), lanes: v }));
    let outputs = openings.outputs.expect("two segments: the middle state is committed");
    let inputs = openings.inputs;
    // L1: ρ ∈ E^13, λ ∈ E^5, one G(1) each.
    let chal = point_groups(ps, SP_LOG + LANE_BITS);
    let (rho, lambda) = (chal[..SP_LOG].to_vec(), chal[SP_LOG..].to_vec());
    let om = eq_table(&lambda);
    let eqr = eq_table(&rho);
    // L2's tables, all off the stack.
    let comb = |n: usize, word: &dyn Fn(usize) -> u64| -> F128 {
        (0..n).fold(F128::ZERO, |a, l| a + om[l].mul_base(F64(word(l))))
    };
    let yw: Vec<F128> = parallel::map_collect(SP_ROWS, |k| comb(LANES, &|l| stack[y_idx(k, l)].0));
    let inw: Vec<F128> = parallel::map_collect(SP_ROWS, |k| comb(LANES, &|l| stack[sp_idx(k, l)].0));
    let msgw: Vec<F128> = parallel::map_collect(SP_ROWS, |k| comb(MSG_LANES, &|l| msg_word(stack, k, l)));
    let sc: Vec<F128> = (0..SP_ROWS).map(|k| if k + 1 < SP_ROWS && w.cont[k + 1] { eqr[k + 1] } else { F128::ZERO }).collect();
    let rest: Vec<F128> = inw.iter().zip(&msgw).map(|(&a, &b)| a + b).collect();
    let (rho_p, fin) = shift_sumcheck(ps, [sc, yw, eqr, rest], tamper);
    // L3: Y, in, M, X at ρ'.
    let eq1 = eq_table(&rho_p);
    let eqx = eq_table(&rho_p[..XL]);
    let y = fin[1];
    let in_v = inw.iter().zip(&eq1).fold(F128::ZERO, |a, (&t, &e)| a + t * e);
    let m_v = (0..SPLIT).fold(F128::ZERO, |a, x| a + eq1[x] * msgw[x]);
    let x_v = (0..1 << XL).fold(F128::ZERO, |a, i| a + eqx[i] * msgw[SPLIT + i]);
    let sel: F128 = rho_p[XL..].iter().copied().product();
    assert_eq!(fin[3], in_v + m_v + sel * x_v, "in + Msg at ρ' splits into the M and X values");
    let mut vals = [y, in_v, m_v, x_v];
    for (j, val) in vals.iter_mut().enumerate() {
        *val = flip(*val, tamper == Tamper::Vals(j));
    }
    ps.add_scalars(&vals);
    let claims = claims(&r, &v, &outputs, &inputs, &rho_p, &om, &eq1, &eqx, &vals);
    SpongeOut { r, v, outputs, inputs, rho, lambda, rho_p, vals, claims }
}

/// L2: 13 plain rounds of `Σ_k a·b + c·d` from claim 0, variable 0 first (season 1's `sumcheck2`): `(ρ', final
/// table values)`.
fn shift_sumcheck(ps: &mut ProverState, mut t: [Vec<F128>; 4], tamper: Tamper) -> (Vec<F128>, [F128; 4]) {
    let mut claim = F128::ZERO;
    let mut point = Vec::with_capacity(SP_LOG);
    for round in 0..SP_LOG {
        let half = t[0].len() / 2;
        let (mut c0, mut c2) = (F128::ZERO, F128::ZERO);
        for j in 0..half {
            for (a, b) in [(&t[0], &t[1]), (&t[2], &t[3])] {
                c0 += a[2 * j] * b[2 * j];
                c2 += (a[2 * j] + a[2 * j + 1]) * (b[2 * j] + b[2 * j + 1]);
            }
        }
        let c0 = flip(c0, tamper == Tamper::LinkRound(round));
        let coeffs = [c0, claim + c2, c2];
        ps.add_round_poly(&coeffs, false);
        let ch = ps.sample();
        claim = poly_eval(&coeffs, ch);
        for v in t.iter_mut() {
            *v = (0..half).map(|j| v[2 * j] + ch * (v[2 * j] + v[2 * j + 1])).collect();
        }
        point.push(ch);
    }
    (point, [t[0][0], t[1][0], t[2][0], t[3][0]])
}

/// The block `(off, μ)` holding stack indices `lo ..= last`, and the base index of the block.
fn block_of(lo: usize, last: usize) -> (usize, usize, usize) {
    let (off, mu) = region_block(lo, last + 1);
    (off, mu, off << mu)
}

/// Claim 42's block: slot 36's words `x + 2^13·l`, `l < 25` (`(72, 18)` at P18).
pub fn block_y() -> (usize, usize, usize) {
    block_of(y_idx(0, 0), y_idx(SP_ROWS - 1, LANES - 1))
}

/// Claim 44's block: `STREAM` words `17x + l`, `x < split`, `l < 17` (`(132, 17)`).
pub fn block_m() -> (usize, usize, usize) {
    block_of(m_idx(0, 0), m_idx(SPLIT - 1, MSG_LANES - 1))
}

/// Claim 45's block: `X`'s words (`layout::x_idx`, STUB placement; `(592, 15)`).
pub fn block_x() -> (usize, usize, usize) {
    block_of(x_idx(0, 0), x_idx((1 << XL) - 1, MSG_LANES - 1))
}

#[allow(clippy::too_many_arguments)]
fn claims(
    r: &[F128],
    v: &[F128; LANES],
    outputs: &WordOpening,
    inputs: &Opening,
    rho_p: &[F128],
    om: &[F128],
    eq1: &[F128],
    eqx: &[F128],
    vals: &[F128; 4],
) -> Vec<PClaim> {
    assert_eq!((inputs.point.len(), outputs.point.len()), (SP_MU, SP_MU));
    assert_eq!((rho_p.len(), r.len()), (SP_LOG, Y_MU));
    let mut c = vec![
        PClaim::ring("15 sponge ring", SP_OFF, inputs.point.clone(), inputs.slices.clone(), 1),
        PClaim::point("16 sponge c_out", SP_OFF, outputs.point.clone(), outputs.value),
    ];
    for (l, &vl) in v.iter().enumerate() {
        c.push(PClaim::point(format!("{} sponge Y{l}(r)", 17 + l), y_off(l), r.to_vec(), vl));
    }
    let (om, eq1, eqx) = (om.to_vec(), eq1.to_vec(), eqx.to_vec());
    // 42: Σ_{l<25} eq(λ, l)·Ỹ_l(ρ') = Y.
    let (off, mu, base) = block_y();
    {
        let (om, eq1) = (om.clone(), eq1.clone());
        c.push(PClaim::dense("42 link Y", off, mu, vals[0], move |s, w| {
            for l in 0..LANES {
                let sl = s * om[l];
                for (x, &e) in eq1.iter().enumerate() {
                    w[y_idx(x, l) - base] += sl * e;
                }
            }
        }));
    }
    // 43: Σ_{l<25} eq(λ, l)·sp̃(ρ', slot l) = in (block SP).
    {
        let (om, eq1) = (om.clone(), eq1.clone());
        let base = idx(SLOT_SP, 0);
        c.push(PClaim::dense("43 link in", SP_OFF, SP_MU, vals[1], move |s, w| {
            for l in 0..LANES {
                let sl = s * om[l];
                for (x, &e) in eq1.iter().enumerate() {
                    w[sp_idx(x, l) - base] += sl * e;
                }
            }
        }));
    }
    // 44: Σ_{l<17} eq(λ, l)·Σ_{x<split} eq(ρ', x)·M(x, l) = M.
    let (off, mu, base) = block_m();
    {
        let (om, eq1) = (om.clone(), eq1.clone());
        c.push(PClaim::dense("44 link M", off, mu, vals[2], move |s, w| {
            for l in 0..MSG_LANES {
                let sl = s * om[l];
                for (x, &e) in eq1.iter().enumerate().take(SPLIT) {
                    w[m_idx(x, l) - base] += sl * e;
                }
            }
        }));
    }
    // 45: Σ_{l<17} eq(λ, l)·X̃_l(ρ'.take xl) = X.
    let (off, mu, base) = block_x();
    c.push(PClaim::dense("45 link X", off, mu, vals[3], move |s, w| {
        for l in 0..MSG_LANES {
            let sl = s * om[l];
            for (i, &e) in eqx.iter().enumerate() {
                w[x_idx(i, l) - base] += sl * e;
            }
        }
    }));
    assert_eq!(c.len(), 31);
    c
}
