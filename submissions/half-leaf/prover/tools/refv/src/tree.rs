//! FORMAT6 §6.2 (frozen since v2.1; FORMAT6 v2.2): the tree batch, `V_S`'s side (WP R2; BLUEPRINT §2.3 v3).
//!
//! Rows 1–5 are the tree's start (`δ`, `ρ`, `D⁰`, `D¹`, `u`, `o₄ … o₂₄`), rows 6–9 are leanVM's `verify_keccak`
//! (`L:keccak.rs`) unchanged except that the middle state sits at slot `8 + l`, and row 10 is the tree's input
//! opening: the constants off the claim with the post-layer `r'_seg`, 4 low row bits, the top row bit, 6 slot bits,
//! the 64 slices, the final check with `W(z)`. The arithmetic of `verify_layer` is transcribed from
//! `L:keccak.rs:117-197` (its public helpers `linear_transpose`, `along`, the RMFE constants are used as they are);
//! the grinds are FORMAT6's (`G(6)` for `s`, `G(2)` for every round and `β`, `G(3)` for `r_seg`), not leanVM's.
//!
//! [`verify`] returns the claims of §6.5 (1 the ring-switch claim, 2 `c_out`, 3–10 wiring, 11–14 root) as points and
//! values; [`TreeStub`] plugs them into [`crate::vs::verify_pi`]'s stub slot.

use crate::arith::{ONE, ZERO, dot, eq_eval, eq_table, multilinear_eval, poly_eval, ring_coefficients, ring_target, ring_weight};
use crate::chain::VChain;
use crate::stack::{Commit, Maps, StackClaim};
use crate::vs::{Deferred, Stubs};
use crate::{Digest, E, K, Reject, Res, require};
use verifier::keccak::{BITS, EMBED_BITS, LANE_BITS, PACK, PRODUCT_BITS, RMFE_EMBED, RMFE_PROJECT, along, linear_transpose};

const PACK_BITS: usize = 4;
const STATE_LANES: usize = 25;
const DEPTH: usize = 12;
const SEGMENTS: usize = 2;
const SLOT_BITS: usize = 6;
/// Middle lane `l` at slot `MID + l`.
pub const MID: usize = 8;
/// FORMAT6 §6.2's grinds.
const G_RHO: u32 = 5;
const G_U: u32 = 1;
const G_LANE: u32 = 3;
const G_S: u32 = 6;
const G_ROUND: u32 = 2;
const G_BETA: u32 = 2;
/// `c^P`, `c^L` as (lane, bit).
const CP_BITS: [(usize, usize); 4] = [(0, 2), (0, 6), (8, 8), (16, 63)];
const CL_BITS: [(usize, usize); 4] = [(0, 3), (0, 6), (4, 8), (16, 63)];

/// Keccak-f's round constants (FIPS 202).
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
    0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// Which check of §6.2 rejected (inside [`Reject::Tree`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeCheck {
    /// Row 8: the product polynomial does not carry the claim (layer `step`).
    Product(usize),
    /// Row 8: the position sumcheck's terminal (layer `step`).
    Layer(usize),
    /// Row 9: `weights[0]·c_out ≠ value`.
    Middle,
    /// Row 10: `μ̃(ϱ_low)·Σ W(z)·s_z ≠ value`.
    Input,
}

struct Claim {
    value: E,
    mu: Vec<E>,
    point: Vec<E>,
    weights: Vec<E>,
}

/// A point claim `q̃(point) = value` on the stack (row variables low, slot variables high).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointClaim {
    pub point: Vec<E>,
    pub value: E,
}

/// What §6.2 leaves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeOut {
    pub delta: [u64; 4],
    pub rho: Vec<E>,
    pub u: E,
    /// `o₀ … o₂₄`.
    pub o: Vec<E>,
    /// Claim 2: `q̃((u, ρ), ϱ) = c_out`.
    pub c_out: PointClaim,
    /// Claims 3–10 (slot 0 … 7) and 11–14 (root, slot 4 … 7 of row 0).
    pub wiring: Vec<PointClaim>,
    pub root: Vec<PointClaim>,
    /// The 64 slice claims at one stack point (claim 1 before ring switching).
    pub slice_point: Vec<E>,
    pub slices: Vec<E>,
}

fn bits_of(x: usize, n: usize) -> Vec<E> {
    (0..n).map(|b| E::new((x >> b & 1) as u64, 0)).collect()
}

/// `n` sumcheck rounds of `count` coefficients, eq mode per `eq` (`L:transcript.rs` `sumcheck_round_poly`, the
/// normalized form), each round's grind `G(2)`.
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

/// `L:keccak.rs:104` `instance_weights`.
fn instance_weights(s: E) -> Vec<E> {
    let mut powers = [ONE; EMBED_BITS];
    for b in 1..EMBED_BITS {
        powers[b] = powers[b - 1] * s;
    }
    RMFE_EMBED.iter().map(|&e| E::sum((0..EMBED_BITS).filter(|b| e >> b & 1 == 1).map(|b| powers[b]))).collect()
}

/// `L:keccak.rs:117` `verify_layer`, on the chain.
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
    require(projected + iota * E::sum(claim.mu.iter().copied()) == claim.value, Reject::Tree(TreeCheck::Product(step)))?;

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
    require(at_local * (kappa * t[0] + (kappa + t[1]) * t[2]) == value, Reject::Tree(TreeCheck::Layer(step)))?;

    let beta = ch.ground(G_BETA)?;
    let lane_weights: [E; STATE_LANES] = std::array::from_fn(|lane| {
        let shifted = |k| eq_lane[along(64 * lane, k) / 64];
        eq_lane[lane] + beta * (shifted(4) + beta * shifted(3))
    });
    let weights: Vec<E> = (0..BITS).map(|j| lane_weights[j / 64] * eq_z[j % 64]).collect();
    Ok(Claim { value: t[0] + beta * (t[1] + beta * t[2]), mu, point, weights: linear_transpose(&weights) })
}

/// `pw(o, z)` = `weights_{64o+z+8}` (`z < 56`), `weights_{64(o+1)+z−56}` (`z ≥ 56`).
fn pull_back(w: &[E], o: usize, z: usize) -> E {
    if z < 56 { w[64 * o + z + 8] } else { w[64 * (o + 1) + z - 56] }
}

/// §6.2 rows 1–10 at batch `κ = log_blocks + 1` (P18: 19). `h` is the header's root.
pub fn verify(ch: &mut VChain, log_blocks: usize, h: &Digest) -> Res<TreeOut> {
    let kappa = log_blocks + 1;
    let pack_bits = kappa - PACK_BITS;
    // 1–4.
    let dk = ch.read_k(4)?;
    let delta: [u64; 4] = [dk[0], dk[1], dk[2], dk[3]];
    let rho = ch.group(G_RHO, kappa - 1)?;
    let d = ch.read_e(8)?;
    let u = ch.ground(G_U)?;
    // 5. o₀ … o₃ are V's: (1+u)·D⁰_m + u·D¹_m.
    let mut o: Vec<E> = (0..4).map(|m| (ONE + u) * d[m] + u * d[4 + m]).collect();
    o.extend(ch.read_e(21)?);
    let instance = [&[u][..], &rho].concat();
    // 6–7. leanVM's start (`L:keccak.rs:247`), one segment bit.
    let segment = ch.group(G_LANE, 1 + LANE_BITS)?;
    let (r_seg, r_lane) = (segment[0], &segment[1..]);
    let point = [&instance[PACK_BITS..], &[r_seg][..]].concat();
    let lanes = eq_table(r_lane);
    let weights: Vec<E> = (0..BITS).map(|j| lanes[j / 64] * E::from(K(1 << (j % 64)))).collect();
    let last = r_seg * dot(&lanes[..STATE_LANES], &o);
    let committed = ch.read_e(1)?[0];
    let first = Claim { value: committed + last, mu: eq_table(&instance[..PACK_BITS]), point, weights };
    // 8.
    let mut claim = verify_layer(ch, pack_bits, 0, &first)?;
    for step in 1..DEPTH {
        claim = verify_layer(ch, pack_bits, step, &claim)?;
    }
    // 9. `open(first, 1, 1, c_st)` with slot 8 + l.
    let (slot, value) = sumcheck(ch, committed, 3, &[None; SLOT_BITS])?;
    let eq_slot = eq_table(&slot);
    let seg0 = ONE + r_seg;
    let w0 = E::sum((0..STATE_LANES).map(|l| seg0 * eq_slot[MID + l] * first.weights[64 * l]));
    let word = ch.read_e(1)?[0];
    require(w0 * word == value, Reject::Tree(TreeCheck::Middle))?;
    let c_out = PointClaim { point: [&instance[..], &slot].concat(), value: word };
    // 10. The input opening.
    let (r_pack, r_seg2) = (&claim.point[..pack_bits], claim.point[pack_bits]);
    let (r_mid, r_top) = (&r_pack[..pack_bits - 1], r_pack[pack_bits - 1]);
    let mubar = E::sum(claim.mu.iter().copied());
    let cset = |bits: &[(usize, usize)]| E::sum(bits.iter().map(|&(l, b)| claim.weights[64 * l + b]));
    let value = claim.value + (ONE + r_seg2) * mubar * ((ONE + r_top) * cset(&CP_BITS) + r_top * cset(&CL_BITS));
    let (low, value) = sumcheck(ch, value, 3, &[None; PACK_BITS])?;
    let (rest, value) = sumcheck(ch, value, 3, &[None; 1 + SLOT_BITS])?;
    let (rho_top, rho_slot) = (rest[0], &rest[1..]);
    let s = ch.read_e(64)?;
    let eq_o = eq_table(rho_slot);
    let (a_p, a_l) = ((ONE + r_top) * (ONE + rho_top), r_top * rho_top);
    let e_tt = a_p + a_l;
    let w = &claim.weights;
    let big_w: Vec<E> = (0..64)
        .map(|z| {
            let mut acc = ZERO;
            for o in 0..8 {
                let pl = if o < 4 { a_l * pull_back(w, o, z) } else { ZERO };
                acc += eq_o[o] * (ONE + r_seg2) * (a_p * pull_back(w, o, z) + pl);
            }
            for l in 0..STATE_LANES {
                acc += eq_o[MID + l] * r_seg2 * e_tt * w[64 * l + z];
            }
            acc
        })
        .collect();
    require(multilinear_eval(&claim.mu, &low) * dot(&big_w, &s) == value, Reject::Tree(TreeCheck::Input))?;
    let slice_point = [&low[..], r_mid, &rest[..]].concat();
    // Claims 3–14.
    let eq0 = rho.iter().fold(ONE, |acc, &r| acc * (ONE + r));
    let row = [&rho[..], &[ZERO][..]].concat();
    let mut wiring = Vec::new();
    for m in 0..4 {
        wiring.push(PointClaim { point: [&row[..], &bits_of(m, SLOT_BITS)].concat(), value: d[m] + eq0 * E::from(K(delta[m])) });
    }
    for m in 0..4 {
        wiring.push(PointClaim { point: [&row[..], &bits_of(4 + m, SLOT_BITS)].concat(), value: d[4 + m] });
    }
    let root = (0..4)
        .map(|m| PointClaim {
            point: [vec![ZERO; kappa], bits_of(4 + m, SLOT_BITS)].concat(),
            value: E::from(K(u64::from_le_bytes(h[8 * m..8 * m + 8].try_into().unwrap()))),
        })
        .collect();
    Ok(TreeOut { delta, rho, u, o, c_out, wiring, root, slice_point, slices: s })
}

impl PointClaim {
    pub fn stack_claim(&self) -> StackClaim<'static> {
        let p = self.point.clone();
        (Box::new(move |x| eq_eval(&p, x)), self.value)
    }
}

impl TreeOut {
    /// Claims 1–14 of §6.5, claim 1 (the ring switch) needing the tree map.
    pub fn deferred(&self) -> Vec<Deferred> {
        let (point, s) = (self.slice_point.clone(), self.slices.clone());
        let mut v: Vec<Deferred> = vec![Box::new(move |m: &Maps| {
            let c = ring_coefficients(&m.tree_f, &m.tree_g);
            let target = ring_target(&s, &m.tree_f, &m.tree_g);
            (Box::new(move |x: &[E]| ring_weight(&point, x, &c)) as Box<dyn Fn(&[E]) -> E>, target)
        })];
        for pc in std::iter::once(&self.c_out).chain(&self.wiring).chain(&self.root) {
            let pc = pc.clone();
            v.push(Box::new(move |_: &Maps| pc.stack_claim()));
        }
        v
    }
}

/// §6.2 in `verify_pi`'s `Stubs::tree` slot (the sponge batch and §T still stubbed).
pub struct TreeStub {
    pub h: Digest,
    pub out: Option<TreeOut>,
}

impl Stubs for TreeStub {
    fn tree<'a>(&mut self, ch: &mut VChain<'a>, sh: &crate::shape::Shape, _c: &Commit) -> Res<Vec<Deferred>> {
        let out = verify(ch, sh.log_blocks as usize, &self.h)?;
        let d = out.deferred();
        self.out = Some(out);
        Ok(d)
    }
}

// ------------------------------------------------------------------------------------------- dev: §6.2 alone

/// What [`verify_tree_pi`] leaves: §6.2's claims, `λ₀` and the tree map, the counters.
pub struct TreeReport {
    pub out: TreeOut,
    pub maps: Maps,
    pub body: usize,
    pub queries: usize,
    pub tree_body: usize,
    pub tree_queries: usize,
    pub tree_nonces: usize,
}

/// A dev proof that stops after §6.5's group: `HDR ‖ §6.1 ‖ §6.2 ‖ (B, G(g_batch), D(32))`. Every item is checked as
/// in the full `V_S`; the stack claims are left to the caller (who has the committed stack).
pub fn verify_tree_pi(
    sh: &crate::shape::Shape,
    vk: &Digest,
    c: &Digest,
    pi: &[u8],
    ask: &mut dyn crate::chain::Ask,
) -> Res<TreeReport> {
    let (h, hdr_bytes, body) = crate::hdr::parse(sh, pi)?;
    crate::hdr::vk_ok(vk, &h)?;
    crate::hdr::statement_ok(c, &h)?;
    let mut ch = VChain::start(ask, hdr_bytes, body)?;
    crate::stack::commit(&mut ch, sh)?;
    ch.phase(crate::Part::Tree);
    let out = verify(&mut ch, sh.log_blocks as usize, &h.h)?;
    let maps = crate::stack::maps(&mut ch, sh)?;
    let (stats, _) = ch.finish()?;
    let t = stats.get(&crate::Part::Tree).cloned().unwrap_or_default();
    let total = |f: fn(&crate::chain::Stats) -> usize| stats.values().map(f).sum::<usize>();
    Ok(TreeReport {
        out,
        maps,
        body: total(|s| s.body),
        queries: total(|s| s.queries),
        tree_body: t.body,
        tree_queries: t.queries,
        tree_nonces: t.nonces,
    })
}

/// Native evaluation of the claims on a committed stack (`q[s·2^κ + r]`, `2^(κ+6)` words): a dev oracle in place of
/// the PCS, as TOY2's. Returns the names of the claims that fail.
pub fn check_claims(out: &TreeOut, q: &[u64]) -> Vec<String> {
    let n = q.len() / 64;
    let kappa = n.trailing_zeros() as usize;
    assert_eq!(64 << kappa, q.len());
    let split = |p: &[E]| (eq_table(&p[..kappa]), eq_table(&p[kappa..]));
    // `Σ_s eq_s · Σ_r eq_r · q` and the 64 slices `Σ eq · bit z of q`, rows on the pool.
    let mle = |p: &[E]| -> E {
        let (er, es) = split(p);
        let per_slot: Vec<E> = parallel::map_collect(64, |s| {
            if es[s] == ZERO {
                return ZERO;
            }
            let col = &q[s * n..(s + 1) * n];
            E::sum(col.iter().zip(&er).filter(|(w, _)| **w != 0).map(|(&w, &e)| e * K(w)))
        });
        E::sum(per_slot.iter().zip(&es).map(|(&v, &e)| v * e))
    };
    let mut fails = Vec::new();
    if mle(&out.c_out.point) != out.c_out.value {
        fails.push("c_out".into());
    }
    for (m, pc) in out.wiring.iter().enumerate() {
        if mle(&pc.point) != pc.value {
            fails.push(format!("wiring{m}"));
        }
    }
    for (m, pc) in out.root.iter().enumerate() {
        if mle(&pc.point) != pc.value {
            fails.push(format!("root{m}"));
        }
    }
    let (er, es) = split(&out.slice_point);
    let per_slot: Vec<[E; 64]> = parallel::map_collect(64, |s| {
        let mut acc = [ZERO; 64];
        for (r, &w) in q[s * n..(s + 1) * n].iter().enumerate() {
            let mut w = w;
            while w != 0 {
                let z = w.trailing_zeros() as usize;
                acc[z] += er[r];
                w &= w - 1;
            }
        }
        acc.map(|a| a * es[s])
    });
    let got: Vec<E> = (0..64).map(|z| E::sum(per_slot.iter().map(|a| a[z]))).collect();
    if got != out.slices {
        fails.push("slices".into());
    }
    fails
}
