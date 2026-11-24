//! FORMAT6 v2.4 §6.3, `V_S`'s side, on refv's chain.
//!
//! - C1, C2: 13 × `G(1)` → `r`; `E(25)` → `v`.
//! - The core: leanVM's `verify_keccak` (`L:keccak.rs:239`) at `log_steps = 13`, depth 12, on the chain: `G(3)`,
//!   `D(5)` → `r_seg`, `r_lane`; `E(1)` → `c_st`; 12 × `verify_layer`; the middle opening (6 plain rounds, `E(1)`,
//!   check `weights[0]·c_out = value`, middle lane `l` at slot `25 + l`); the input opening (4 + 6 plain rounds,
//!   `E(64)`, check `μ̃(low)·Σ_z row_z·s_z = value`). `verify_layer`, `sumcheck`, `instance_weights` and the round
//!   constants are copied from R2's `tools/refv/src/tree.rs` (private there; R2 transcribed them from
//!   `L:keccak.rs:104-197` with FORMAT6's grinds).
//! - The link (`ksLinkProgE2 13 xl rows`): 18 × `G(1)` → `ρ`, `λ`; 13 plain `R(2, 2)` from 0 → `ρ'`, final; `E(4)`
//!   → `Y, in, M, X`; check `final = Sc(ρ, ρ')·Y + eq(ρ, ρ')·(in + M + sel·X)`, `Sc = contShiftF rows` (`Σ_{i ∈ rows}
//!   eq(ρ, i)·eq(ρ', i − 1)`), `sel = Π_{j ≥ xl} ρ'_j` (`selXF`).
//!
//! A §6.3 check rejects as `Reject::Sponge(SpongeCheck)` (moved into refv from `r3sponge::verify` by R1; the code
//! encoding inside `TreeCheck::Layer` is gone).

use r3core::layout::{
    MSG_LANES, SP_LOG, SP_MU, SP_OFF, SPLIT, XL, idx, m_idx, sp_idx, x_idx, y_idx, y_off, SLOT_SP, Y_MU,
};
use crate::arith::{ONE, ZERO, dot, eq_eval, eq_table, multilinear_eval, poly_eval, ring_coefficients, ring_target, ring_weight};
use crate::chain::{Stats, VChain};
use crate::stack::{Maps, StackClaim, placed};
use crate::vs::Deferred;
use crate::{E, K, Reject, Res};
use verifier::keccak::{BITS, EMBED_BITS, LANE_BITS, PACK, PRODUCT_BITS, RMFE_EMBED, RMFE_PROJECT, along, linear_transpose};

use r3sponge::prove::{block_m, block_x, block_y};

const PACK_BITS: usize = 4;
const STATE_LANES: usize = 25;
const DEPTH: usize = 12;
const SEGMENTS: usize = 2;
const SLOT_BITS: usize = 6;
/// leanVM's middle lane `l` at slot `MID + l`.
const MID: usize = 25;
/// FORMAT6 §6.2/§6.3 grinds.
const G_POINT: u32 = 1;
const G_LANE: u32 = 3;
const G_S: u32 = 6;
const G_ROUND: u32 = 2;
const G_BETA: u32 = 2;

/// Keccak-f's round constants (FIPS 202; copied from R2's `crate::tree`).
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
    0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// Which check of §6.3 rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpongeCheck {
    /// The core's product polynomial (layer `step`).
    Product(usize),
    /// The core's position sumcheck terminal (layer `step`).
    Layer(usize),
    /// The core's middle opening.
    Middle,
    /// The core's input opening.
    Input,
    /// L3.
    Link,
}

/// The §6.3 check a rejection is, if it is one.
pub fn sponge_check(r: &Reject) -> Option<SpongeCheck> {
    if let Reject::Sponge(c) = r { Some(*c) } else { None }
}

fn req(ok: bool, c: SpongeCheck) -> Res<()> {
    if ok { Ok(()) } else { Err(Reject::Sponge(c)) }
}

struct Claim {
    value: E,
    mu: Vec<E>,
    point: Vec<E>,
    weights: Vec<E>,
}

/// `n` sumcheck rounds of `count` coefficients, eq mode per entry, each round's grind `G(2)` (R2's `crate::tree::sumcheck`).
fn sumcheck(ch: &mut VChain, mut claim: E, count: usize, eq: &[Option<E>]) -> Res<(Vec<E>, E)> {
    let mut point = Vec::with_capacity(eq.len());
    for &r in eq {
        let poly = match r {
            None => {
                let c0 = ch.read_e(1)?[0];
                let tail = ch.read_e(count - 2)?;
                [vec![c0, claim + E::sum(tail.iter().copied())], tail].concat()
            }
            Some(r) => {
                let tail = ch.read_e(count - 1)?;
                [vec![claim + r * E::sum(tail.iter().copied())], tail].concat()
            }
        };
        let c = ch.ground(G_ROUND)?;
        point.push(c);
        claim = poly_eval(&poly, c);
    }
    Ok((point, claim))
}

/// `L:keccak.rs:104` `instance_weights` (R2's copy).
fn instance_weights(s: E) -> Vec<E> {
    let mut powers = [ONE; EMBED_BITS];
    for b in 1..EMBED_BITS {
        powers[b] = powers[b - 1] * s;
    }
    RMFE_EMBED.iter().map(|&e| E::sum((0..EMBED_BITS).filter(|b| e >> b & 1 == 1).map(|b| powers[b]))).collect()
}

/// `L:keccak.rs:117` `verify_layer`, on the chain (R2's `crate::tree::verify_layer`, its rejections §6.3's).
fn verify_layer(ch: &mut VChain, pack_bits: usize, step: usize, claim: &Claim) -> Res<Claim> {
    let product = ch.read_e(PRODUCT_BITS)?;
    let projected = E::sum((0..PRODUCT_BITS).map(|c| {
        E::sum((0..PACK).filter(|&i| RMFE_PROJECT[i] >> c & 1 == 1).map(|i| claim.mu[i])) * product[c]
    }));
    let segments = eq_table(&claim.point[pack_bits..]);
    let mut iota = ZERO;
    for (segment, &weight) in segments.iter().enumerate().take(SEGMENTS) {
        let constant = RC[DEPTH * (segment + 1) - step - 1];
        iota += weight * E::sum((0..64).filter(|z| constant >> z & 1 == 1).map(|z| claim.weights[z]));
    }
    req(projected + iota * E::sum(claim.mu.iter().copied()) == claim.value, SpongeCheck::Product(step))?;

    let s = ch.ground(G_S)?;
    let mu = instance_weights(s);
    let kappa = E::sum(mu.iter().copied());
    let value = poly_eval(&product, s);
    let equalities: Vec<_> = claim.point.iter().copied().map(Some).collect();
    let (point, value) = sumcheck(ch, value, 3, &equalities)?;
    let (local, value) = sumcheck(ch, value, 4, &[None; 11])?;
    let t = ch.read_e(3)?;
    let (eq_z, eq_lane) = (eq_table(&local[..6]), eq_table(&local[6..]));
    let at_local = E::sum(claim.weights.chunks(64).zip(&eq_lane).map(|(lane, &e)| e * dot(&eq_z, lane)));
    req(at_local * (kappa * t[0] + (kappa + t[1]) * t[2]) == value, SpongeCheck::Layer(step))?;

    let beta = ch.ground(G_BETA)?;
    let lane_weights: [E; STATE_LANES] = std::array::from_fn(|lane| {
        let shifted = |k| eq_lane[along(64 * lane, k) / 64];
        eq_lane[lane] + beta * (shifted(4) + beta * shifted(3))
    });
    let weights: Vec<E> = (0..BITS).map(|j| lane_weights[j / 64] * eq_z[j % 64]).collect();
    Ok(Claim { value: t[0] + beta * (t[1] + beta * t[2]), mu, point, weights: linear_transpose(&weights) })
}

/// Counters of one sub-phase (C, the core, L), from refv's per-part `Stats`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PartCount {
    pub body: usize,
    pub queries: usize,
    pub nonces: usize,
    pub draws: usize,
    /// Every chain query's length, in order.
    pub lengths: Vec<usize>,
}

fn snap(ch: &VChain) -> Stats {
    ch.stats.get(&ch.part()).cloned().unwrap_or_default()
}

fn delta(a: &Stats, b: &Stats) -> PartCount {
    PartCount {
        body: b.body - a.body,
        queries: b.queries - a.queries,
        nonces: b.nonces - a.nonces,
        draws: b.draws - a.draws,
        lengths: b.chain_lengths[a.chain_lengths.len()..].to_vec(),
    }
}

/// What §6.3 leaves, `V_S`'s side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpongeV {
    pub r: Vec<E>,
    pub v: Vec<E>,
    /// Claim 16: `sp̃((r, slot)) = c_out`.
    pub c_out_point: Vec<E>,
    pub c_out: E,
    /// Claim 15: the 64 slices of `SP` at `slice_point`.
    pub slice_point: Vec<E>,
    pub slices: Vec<E>,
    pub rho: Vec<E>,
    pub lambda: Vec<E>,
    pub rho_p: Vec<E>,
    /// `Y, in, M, X`.
    pub vals: Vec<E>,
    /// Caller, core, link.
    pub counts: [PartCount; 3],
}

/// `G(1)` per coordinate.
fn point_groups(ch: &mut VChain, n: usize) -> Res<Vec<E>> {
    (0..n).map(|_| ch.ground(G_POINT)).collect()
}

/// `contShiftF rows ρ ρ' = Σ_{i ∈ rows} eq(ρ, i)·eq(ρ', i − 1)` (`LvmE2VProgKS.contShiftF`; `0 ∉ rows`).
pub fn cont_shift(rows: &[usize], rho: &[E], rho_p: &[E]) -> E {
    let (a, b) = (eq_table(rho), eq_table(rho_p));
    E::sum(rows.iter().map(|&i| {
        assert!(i >= 1, "0 ∉ contRows");
        a[i] * b[i - 1]
    }))
}

/// §6.3 on the chain, right after the tree batch's `E(64)`. `rows` is `contRows` (a `Shape` constant,
/// [`r3sponge::cont_rows`]).
pub fn verify(ch: &mut VChain, rows: &[usize]) -> Res<SpongeV> {
    let s0 = snap(ch);
    // C1, C2.
    let r = point_groups(ch, SP_LOG)?;
    let v = ch.read_e(STATE_LANES)?;
    let s1 = snap(ch);
    // The core (`L:keccak.rs:239` `verify_keccak`, one segment bit, two segments).
    let pack_bits = SP_LOG - PACK_BITS;
    let seg = ch.group(G_LANE, 1 + LANE_BITS)?;
    let (r_seg, r_lane) = (seg[0], &seg[1..]);
    let point = [&r[PACK_BITS..], &[r_seg][..]].concat();
    let lanes = eq_table(r_lane);
    let weights: Vec<E> = (0..BITS).map(|j| lanes[j / 64] * E::from(K(1 << (j % 64)))).collect();
    let last = r_seg * dot(&lanes[..STATE_LANES], &v);
    let committed = ch.read_e(1)?[0];
    let first = Claim { value: committed + last, mu: eq_table(&r[..PACK_BITS]), point, weights };
    let mut claim = verify_layer(ch, pack_bits, 0, &first)?;
    for step in 1..DEPTH {
        claim = verify_layer(ch, pack_bits, step, &claim)?;
    }
    // The middle opening (`open(first, 1, 1, committed)`).
    let (slot, value) = sumcheck(ch, committed, 3, &[None; SLOT_BITS])?;
    let eq_slot = eq_table(&slot);
    let w0 = E::sum((0..STATE_LANES).map(|l| (ONE + r_seg) * eq_slot[MID + l] * first.weights[64 * l]));
    let c_out = ch.read_e(1)?[0];
    req(w0 * c_out == value, SpongeCheck::Middle)?;
    let c_out_point = [&r[..], &slot].concat();
    // The input opening: 4 instance rounds, `open(claim, 0, 2, ·)`.
    let (low, value) = sumcheck(ch, claim.value, 3, &[None; PACK_BITS])?;
    let (slot2, value) = sumcheck(ch, value, 3, &[None; SLOT_BITS])?;
    let segs = eq_table(&claim.point[pack_bits..]);
    let eq_slot2 = eq_table(&slot2);
    let mut row = [ZERO; 64];
    for (m, &sm) in segs.iter().enumerate().take(SEGMENTS) {
        for (lane, w) in claim.weights.chunks(64).enumerate() {
            let scale = sm * eq_slot2[STATE_LANES * m + lane];
            for (o, &wz) in row.iter_mut().zip(w) {
                *o += scale * wz;
            }
        }
    }
    let slices = ch.read_e(64)?;
    req(multilinear_eval(&claim.mu, &low) * dot(&row, &slices) == value, SpongeCheck::Input)?;
    let slice_point = [&low[..], &claim.point[..pack_bits], &slot2[..]].concat();
    let s2 = snap(ch);
    // The link.
    let chal = point_groups(ch, SP_LOG + 5)?;
    let (rho, lambda) = (chal[..SP_LOG].to_vec(), chal[SP_LOG..].to_vec());
    let (rho_p, fin) = sumcheck(ch, ZERO, 3, &[None; SP_LOG])?;
    let vals = ch.read_e(4)?;
    let sel = rho_p[XL..].iter().fold(ONE, |a, &x| a * x);
    let rhs = cont_shift(rows, &rho, &rho_p) * vals[0] + eq_eval(&rho, &rho_p) * (vals[1] + vals[2] + sel * vals[3]);
    req(fin == rhs, SpongeCheck::Link)?;
    let s3 = snap(ch);
    Ok(SpongeV {
        r,
        v,
        c_out_point,
        c_out,
        slice_point,
        slices,
        rho,
        lambda,
        rho_p,
        vals,
        counts: [delta(&s0, &s1), delta(&s1, &s2), delta(&s2, &s3)],
    })
}

/// `eq(z, bits(v))`, the bits of `v` low first.
fn eq_bits(z: &[E], v: usize) -> E {
    z.iter().enumerate().fold(ONE, |acc, (k, &x)| acc * if v >> k & 1 == 1 { x } else { ONE + x })
}

fn boxed(f: impl Fn(&[E]) -> E + 'static) -> Box<dyn Fn(&[E]) -> E> {
    Box::new(f)
}

impl SpongeV {
    /// Claims 15, 16, 17–41, 42–45 of §6.5 (15 needs the sponge map), each placed on its block.
    pub fn deferred(&self) -> Vec<Deferred> {
        let mut d: Vec<Deferred> = Vec::new();
        let sp_off = SP_OFF as u64;
        // 15: the ring-switched input opening on SP.
        let (pt, s) = (self.slice_point.clone(), self.slices.clone());
        d.push(Box::new(move |m: &Maps| {
            let c = ring_coefficients(&m.sponge_f, &m.sponge_g);
            let target = ring_target(&s, &m.sponge_f, &m.sponge_g);
            (boxed(placed(sp_off, SP_MU, move |x: &[E]| ring_weight(&pt, x, &c))), target)
        }));
        // 16: c_out.
        let (pt, val) = (self.c_out_point.clone(), self.c_out);
        d.push(Box::new(move |_: &Maps| (boxed(placed(sp_off, SP_MU, move |x: &[E]| eq_eval(&pt, x))), val)));
        // 17 + l: Ỹ_l(r) = v_l.
        for l in 0..STATE_LANES {
            let (r, vl) = (self.r.clone(), self.v[l]);
            d.push(Box::new(move |_: &Maps| {
                (boxed(placed(y_off(l) as u64, Y_MU, move |x: &[E]| eq_eval(&r, x))), vl)
            }));
        }
        let om = eq_table(&self.lambda);
        let rho_p = self.rho_p.clone();
        // 42: eq(ρ', x)·eq(λ, l), l < 25, on Y's words x + 2^13·l.
        {
            let (off, mu, base) = block_y();
            assert!((0..STATE_LANES).all(|l| y_idx(0, l) - base == l << SP_LOG && y_idx(5, l) - base == 5 + (l << SP_LOG)));
            let (om, rp, val) = (om.clone(), rho_p.clone(), self.vals[0]);
            d.push(Box::new(move |_: &Maps| {
                let w = move |x: &[E]| {
                    eq_eval(&rp, &x[..SP_LOG])
                        * E::sum((0..STATE_LANES).map(|l| om[l] * eq_bits(&x[SP_LOG..mu], l)))
                };
                (boxed(placed(off as u64, mu, w)), val)
            }));
        }
        // 43: the same form on SP's input slots.
        {
            let base = idx(SLOT_SP, 0);
            assert!((0..STATE_LANES).all(|l| sp_idx(3, l) - base == 3 + (l << SP_LOG)));
            let (om, rp, val) = (om.clone(), rho_p.clone(), self.vals[1]);
            d.push(Box::new(move |_: &Maps| {
                let w = move |x: &[E]| {
                    eq_eval(&rp, &x[..SP_LOG])
                        * E::sum((0..STATE_LANES).map(|l| om[l] * eq_bits(&x[SP_LOG..SP_MU], l)))
                };
                (boxed(placed(sp_off, SP_MU, w)), val)
            }));
        }
        // 44: STREAM words 17x + l, x < split, l < 17 (dense table: not a tensor).
        {
            let (off, mu, base) = block_m();
            let (om, rp, val) = (om.clone(), rho_p.clone(), self.vals[2]);
            d.push(Box::new(move |_: &Maps| {
                let eq1 = eq_table(&rp);
                let mut t = vec![ZERO; 1 << mu];
                for x in 0..SPLIT {
                    for (l, &o) in om.iter().enumerate().take(MSG_LANES) {
                        t[m_idx(x, l) - base] += o * eq1[x];
                    }
                }
                (boxed(placed(off as u64, mu, move |x: &[E]| multilinear_eval(&t, x))), val)
            }));
        }
        // 45: X(i, l) at x_idx(i, l) (STUB placement: word l·2^xl + i of its block).
        {
            let (off, mu, base) = block_x();
            assert!((0..MSG_LANES).all(|l| x_idx(7, l) - base == 7 + (l << XL)));
            let (rp, val) = (rho_p, self.vals[3]);
            d.push(Box::new(move |_: &Maps| {
                let w = move |x: &[E]| {
                    eq_eval(&rp[..XL], &x[..XL]) * E::sum((0..MSG_LANES).map(|l| om[l] * eq_bits(&x[XL..mu], l)))
                };
                (boxed(placed(off as u64, mu, w)), val)
            }));
        }
        assert_eq!(d.len(), 31);
        d
    }
}

/// A `StackClaim` of a deferred claim (re-export for callers that batch them).
pub type Claim6 = StackClaim<'static>;
