//! S2 (BLUEPRINT2 §2.2): the CH link is gone (the chain is wired inside the tape, `lvm::wire`); the KS link and the
//! helpers it shares with the wiring stay. v1's text follows for the KS link.
//!
//! The two links (BLUEPRINT §4.1–4.2; the schedule's `CHlink`/`KSlink` phases, WP-0's [model] shapes), as sent
//! to WP-11a/WP-8 (docs/lvm/stages/WP-15a.md). Each is one degree-2 sumcheck over the rows whose target is
//! public, followed by the column values at its point; `verify_*` replays the verifier's arithmetic (a test
//! oracle; the Lean `V_S` is normative).
//!
//! **CH** (`in_{k} = Pad43(Y_{k−1})` for `1 ≤ k < N`). Challenges `ρ ∈ E^logN, λ ∈ E^3, ζ ∈ E^6`;
//! `ω(l,p) = eq(λ,l)·eq(ζ,p)` on `in` lanes `l < 8`. Summand `S(ρ,k)·g(k) + E'(ρ,k)·h_Y(k)`, target
//! `C(ω)·(1 + eq(ρ,1⃗))`; then the 64 `in` slices at `(ρ', λ, 0,0,0)`, a ring switch, a 2-round sumcheck over the
//! `Y` lane bits, the 64 `Y` slices at `(ρ', μ, 1,0,1,1)` (slot `52 + m`), a ring switch, 5 unused lane samples.
//! The constant lanes 8–24 of `in` become 17 word claims at `(ρ', slot l)`.
//!
//! **KS** (`in_i = cont_i·Y_{i−1} + [l<17]·Msg_i`). Challenges `ρ ∈ E^ks, λ ∈ E^5`, `ω_l = eq(λ,l)`. Summand
//! `Sc(ρ,k)·Y^ω(k) + eq(ρ,k)·(in^ω(k) + Msg^ω(k))`, target 0; then `Y^ω, in^ω, M^ω, X^ω` at `ρ'`. KS14 (roll 7,
//! CR-DES §2): `Msg` is `M` on rows `< ks_split` (15,360) and `X` above, see [`prove_ks`].
//! R11 (M′, S2GM): every claim is on `C_main`: `M_l` is the stream block's column `l` (`S + l·2^14`) and `X_l` its
//! rows from `ks_split` (`Layout::x`), so `M^ω`'s top correction and `X^ω` weigh the same words.

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::primitives::field::{F64, F192};
use crate::lv::primitives::multilinear::eq_table;
use crate::lvm::params::{LANE_BITS, LANES, RING_STAGES, REC_STREAM_COLS};
use crate::lvm::tables::{Layout, Sponge};

/// A claim on a commitment, prover side: either a combination of aligned point evaluations with one value
/// (`Σ_t coeff_t · f̃_{offset_t}(point_t) = value`), or a ring-switched claim on the 64 bit slices of the
/// aligned block at `offset` at `point`, with its own map challenges. CR-P (SH2-Z, `lvm::shape::relocate`): a ring
/// claim moved to the small stack has the weight `Φ(scale · eq(point, ·))` and loses `Σ Φ(u)·z` over `tail`.
#[derive(Clone, Debug)]
pub enum Claim {
    Point { terms: Vec<(usize, Vec<F192>, F192)>, value: F192 },
    Ring { offset: usize, point: Vec<F192>, slices: Vec<F192>, map: [F192; RING_STAGES], scale: F192, tail: Vec<(F192, F64)> },
}

impl Claim {
    pub fn point(offset: usize, point: Vec<F192>, value: F192) -> Self {
        Claim::Point { terms: vec![(offset, point, F192::ONE)], value }
    }
    /// A ring claim on the aligned block at `offset` (scale 1, no tail).
    pub fn ring(offset: usize, point: Vec<F192>, slices: Vec<F192>, map: [F192; RING_STAGES]) -> Self {
        Claim::Ring { offset, point, slices, map, scale: F192::ONE, tail: Vec::new() }
    }
}

fn e(x: u64) -> F192 {
    F192::new(x, 0, 0)
}

/// Bit weights as byte tables: `t[b][v] = Σ_{j<8} w[8b + j]·bit_j(v)`.
pub fn byte_tables(w: &[F192; 64]) -> Vec<[F192; 256]> {
    (0..8)
        .map(|b| {
            let mut t = [F192::ZERO; 256];
            for v in 1..256usize {
                let low = v & v.wrapping_neg();
                t[v] = t[v ^ low] + w[8 * b + low.trailing_zeros() as usize];
            }
            t
        })
        .collect()
}

#[inline]
pub fn bitdot(t: &[[F192; 256]], x: u64) -> F192 {
    let mut acc = F192::ZERO;
    for (b, tb) in t.iter().enumerate() {
        acc += tb[((x >> (8 * b)) & 255) as usize];
    }
    acc
}

/// R9-TY: rounds and folds of at most this many pairs run on the calling thread (the KS link's 2^13 rows: 13 rounds
/// of 5 pool dispatches each cost more than their ≈ 0.6 ms of products; the same sums).
const SERIAL_HALF: usize = 1 << 12;

/// One round of a degree-2 sumcheck of `Σ_k a(k)b(k) + c(k)d(k)`, variable 0 first: `(q(0), q₂)`.
fn round(t: [&[F192]; 4]) -> (F192, F192) {
    let half = t[0].len() / 2;
    if half <= SERIAL_HALF {
        let [a, b, c, d] = t;
        let mut acc = (F192::ZERO, F192::ZERO);
        for j in 0..half {
            let (a0, a1, b0, b1) = (a[2 * j], a[2 * j + 1], b[2 * j], b[2 * j + 1]);
            let (c0, c1, d0, d1) = (c[2 * j], c[2 * j + 1], d[2 * j], d[2 * j + 1]);
            acc.0 += a0 * b0 + c0 * d0;
            acc.1 += (a0 + a1) * (b0 + b1) + (c0 + c1) * (d0 + d1);
        }
        return acc;
    }
    crate::lv::parallel::fold_reduce(
        half,
        || (F192::ZERO, F192::ZERO),
        |acc, j| {
            let [a, b, c, d] = t;
            let (a0, a1, b0, b1) = (a[2 * j], a[2 * j + 1], b[2 * j], b[2 * j + 1]);
            let (c0, c1, d0, d1) = (c[2 * j], c[2 * j + 1], d[2 * j], d[2 * j + 1]);
            acc.0 += a0 * b0 + c0 * d0;
            acc.1 += (a0 + a1) * (b0 + b1) + (c0 + c1) * (d0 + d1);
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

fn fold(v: &mut Vec<F192>, r: F192) {
    let half = v.len() / 2;
    if half <= SERIAL_HALF {
        let next: Vec<F192> = (0..half).map(|j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1])).collect();
        *v = next;
        return;
    }
    let next: Vec<F192> = crate::lv::parallel::map_collect(half, |j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1]));
    *v = next;
}

/// The plain degree-2 sumcheck of `Σ a·b + c·d` from `claim`: sends `(c₀, c₂)` per round (the Lean
/// `sumcheck _ 3`), returns the point and the final claim.
pub fn sumcheck2(ps: &mut ProverState, mut t: [Vec<F192>; 4], mut claim: F192) -> (Vec<F192>, F192, [F192; 4]) {
    let n = t[0].len().trailing_zeros() as usize;
    let mut point = Vec::with_capacity(n);
    for _ in 0..n {
        let (c0, c2) = round([&t[0], &t[1], &t[2], &t[3]]);
        let c1 = claim + c2; // q(0) + q(1) = c1 + c2 in characteristic 2
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        for v in t.iter_mut() {
            fold(v, r);
        }
        point.push(r);
    }
    (point, claim, [t[0][0], t[1][0], t[2][0], t[3][0]])
}

/// `lt̃_m(x) = Σ_{k < m} eq(x, k)`, `O(μ)`.
pub fn lt_mle(x: &[F192], m: usize) -> F192 {
    let mut total = F192::ZERO;
    let mut above = F192::ONE; // Π_{s > t} eq(x_s, m_s)
    for t in (0..x.len()).rev() {
        if (m >> t) & 1 == 1 {
            total += above * (F192::ONE + x[t]);
            above *= x[t];
        } else {
            above *= F192::ONE + x[t];
        }
    }
    if m >> x.len() != 0 { F192::ONE } else { total }
}

/// `eq(r, k)` for `k < len` only: the tensor's prefix, at `O(len + log)` products.
pub fn eq_prefix(r: &[F192], len: usize) -> Vec<F192> {
    // high variables first: the prefix of length `len` is a union of aligned blocks
    let nv = r.len();
    let mut out = vec![F192::ZERO; len];
    let mut k = 0usize;
    while k < len {
        // the largest aligned block at k that fits
        let mut b = if k == 0 { nv } else { (k.trailing_zeros() as usize).min(nv) };
        while (1usize << b) > len - k {
            b -= 1;
        }
        // eq(r, k + j) = eq(r_high, k >> b) · eq(r_low, j)
        let mut hi = F192::ONE;
        for t in b..nv {
            hi *= if (k >> t) & 1 == 1 { r[t] } else { F192::ONE + r[t] };
        }
        let lo = eq_table(&r[..b]);
        for (j, x) in lo.iter().enumerate() {
            out[k + j] = hi * *x;
        }
        k += 1 << b;
    }
    out
}

/// The KS sponge link's structured kernel table `Sc(ρ, k) = eq(ρ, k + 1)·cont_{k+1}`.
pub fn ks_kernel(eqr: &[F192], cont: &[bool]) -> Vec<F192> {
    let n = eqr.len();
    (0..n).map(|k| if k + 1 < n && cont[k + 1] { eqr[k + 1] } else { F192::ZERO }).collect()
}

/// Prove the KS link (the `KSlink` phase). Returns `[Y^ω, in^ω, M^ω, X^ω]` claims (Lean order).
pub fn prove_ks(ps: &mut ProverState, lay: &Layout, ks: &Sponge) -> Vec<Claim> {
    let kl = lay.ks_log;
    let n = 1usize << kl;
    let mut tp = std::time::Instant::now();
    let chal = ps.sample_vec(kl + LANE_BITS);
    crate::lvm::stream::part("ksl sample", &mut tp);
    let (rho, lam) = (&chal[..kl], &chal[kl..]);
    let om = eq_table(lam);
    let eqr = eq_table(rho);
    let sc = ks_kernel(&eqr, &ks.cont);
    let comb = |w: &[u64]| -> F192 { w.iter().zip(&om).map(|(&x, &o)| o.mul_base(F64(x))).sum() };
    let yw: Vec<F192> = crate::lv::parallel::map_collect(n, |k| comb(&ks.outputs[k]));
    let rest: Vec<F192> = crate::lv::parallel::map_collect(n, |k| comb(&ks.inputs[k]) + comb(&ks.msg[k]));
    crate::lvm::stream::part("ksl tabs", &mut tp);
    let (rho1, _f, fin) = sumcheck2(ps, [sc, yw, eqr, rest], F192::ZERO);
    crate::lvm::stream::part("ksl sc", &mut tp);
    let eq1 = eq_table(&rho1);
    let at = |f: &(dyn Fn(usize) -> F192 + Sync)| -> F192 {
        crate::lv::parallel::fold_reduce(n, || F192::ZERO, |acc, k| *acc += eq1[k] * f(k), |a, b| a + b)
    };
    let y = at(&|k| comb(&ks.outputs[k]));
    let inw = at(&|k| comb(&ks.inputs[k]));
    // KS14 (CR-DES §2): rows `< split` absorb `M` (C_rec, `2^rec` rows: its weight is `eq(ρ'_{<rec}, ·)` on rows
    // `< split` only), rows `≥ split` absorb `X` (`2^x_log` rows, weight `eq(ρ'_{<x_log}, ·)`); the message at `ρ'` is
    // `selM·mw + selX·xw`, `selM = Π_{rec ≤ t < ks}(1 + ρ'_t)`, `selX = Π_{x_log ≤ t < ks} ρ'_t` (P8: `1 + ρ'₁₃`, `ρ'₁₃`)
    // (KS13, roll 8: `ks_log < rec_log`; M's weight is on its first `2^ks_log` rows, `LvmDecideV0.ksLink14`: `r` below is
    // `min(rec, ks)`, so KS14 and v1 are unchanged)
    let (r, xl, split) = (lay.rec_log.min(kl), lay.x_log, lay.ks_split);
    let eq_m = eq_table(&rho1[..r]);
    let eq_x = eq_table(&rho1[..xl]);
    let mw: F192 = (0..split).map(|i| eq_m[i] * comb(&ks.msg[i])).sum();
    let xw: F192 = (0..1usize << xl).map(|i| eq_x[i] * comb(&ks.msg[split + i])).sum();
    let sel_m: F192 = rho1[r..kl].iter().map(|&t| F192::ONE + t).product();
    let sel_x: F192 = rho1[xl..kl].iter().copied().product();
    assert!(fin[3] == inw + sel_m * mw + sel_x * xw, "KS link: in + Msg at ρ' splits into the M and X claims");
    crate::lvm::stream::part("ksl evals", &mut tp);
    ps.add_scalars(&[y, inw, mw, xw]);
    crate::lvm::stream::part("ksl add", &mut tp);
    let y_terms = (0..LANES).map(|l| (lay.ks_y(l), rho1.clone(), om[l])).collect();
    let in_terms = (0..LANES).map(|l| (lay.ks_slot(l), rho1.clone(), om[l])).collect();
    // M's weight: `eq(ρ'_{<rec}, ·)` less its top `2^rec − split` rows (KS14: the aligned block `[split, 2^rec)`, where
    // `eq(ρ'_{<rec}, split + i) = eq(ρ'_{<x_log}, i)·Π_{x_log ≤ t < rec} ρ'_t`; in characteristic 2, less is plus)
    let mut m_terms: Vec<(usize, Vec<F192>, F192)> = (0..REC_STREAM_COLS).map(|l| (lay.rec_col(l), rho1[..r].to_vec(), om[l])).collect();
    if split < 1 << r {
        assert_eq!(split, (1usize << r) - (1usize << xl), "the top block of M is X's size");
        let top: F192 = rho1[xl..r].iter().copied().product();
        m_terms.extend((0..REC_STREAM_COLS).map(|l| (lay.rec_col(l) + split, rho1[..xl].to_vec(), om[l] * top)));
    }
    let x_terms = (0..REC_STREAM_COLS).map(|l| (lay.x(l), rho1[..xl].to_vec(), om[l])).collect();
    vec![
        Claim::Point { terms: y_terms, value: y },
        Claim::Point { terms: in_terms, value: inw },
        Claim::Point { terms: m_terms, value: mw },
        Claim::Point { terms: x_terms, value: xw },
    ]
}
