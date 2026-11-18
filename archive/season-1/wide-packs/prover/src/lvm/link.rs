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

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::{Ext, F64, F192};
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
    /// E2F (S2GF, `lvm::front`): `Σ_t Σ_b Φ_t(eq(z_t, b))·q(o_t + b) = value`, `z_t ∈ E2^m`: a coordinate of an E2 word
    /// claim, or a row switch.
    E2 { terms: Vec<crate::lvm::front::E2Term>, value: F192 },
}

impl Claim {
    pub fn point(offset: usize, point: Vec<F192>, value: F192) -> Self {
        Claim::Point { terms: vec![(offset, point, F192::ONE)], value }
    }
    /// E2F: the claims of a word claim of the front's field `F`, `Σ_t c_t·f̃_{o_t}(z_t) = a`: at E3 one point claim, at E2
    /// its two coordinates in place, `re` first (`front`).
    pub fn word<F: crate::lv::primitives::field::Ext<W>, const W: usize>(terms: Vec<(usize, Vec<F>, F)>, a: F) -> Vec<Self> {
        use crate::lvm::front::{E2Term, coord, coord_phi, to_e2, to_e3};
        if W == 3 {
            let terms = terms.into_iter().map(|(o, p, c)| (o, p.into_iter().map(to_e3).collect(), to_e3(c))).collect();
            return vec![Claim::Point { terms, value: to_e3(a) }];
        }
        let terms: Vec<(usize, Vec<crate::lv::primitives::field::F128>, crate::lv::primitives::field::F128)> =
            terms.into_iter().map(|(o, p, c)| (o, p.into_iter().map(to_e2).collect(), to_e2(c))).collect();
        (0..2)
            .map(|h| Claim::E2 {
                terms: terms.iter().map(|(o, p, c)| E2Term { offset: *o, point: p.clone(), phi: coord_phi(*c, h), klin: true }).collect(),
                value: coord(to_e2(a), h),
            })
            .collect()
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
fn round<F: Ext<W>, const W: usize>(t: [&[F]; 4]) -> (F, F) {
    let half = t[0].len() / 2;
    if half <= SERIAL_HALF {
        let [a, b, c, d] = t;
        let mut acc = (F::ZERO, F::ZERO);
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
        || (F::ZERO, F::ZERO),
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

fn fold<F: Ext<W>, const W: usize>(v: &mut Vec<F>, r: F) {
    let half = v.len() / 2;
    if half <= SERIAL_HALF {
        let next: Vec<F> = (0..half).map(|j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1])).collect();
        *v = next;
        return;
    }
    let next: Vec<F> = crate::lv::parallel::map_collect(half, |j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1]));
    *v = next;
}

/// The plain degree-2 sumcheck of `Σ a·b + c·d` from `claim`: sends `(c₀, c₂)` per round (the Lean
/// `sumcheck _ 3`), returns the point and the final claim (E2F: in the front's field, challenges of group `c = 2`).
pub fn sumcheck2<F: Ext<W>, const W: usize>(ps: &mut ProverState, mut t: [Vec<F>; 4], mut claim: F) -> (Vec<F>, F, [F; 4]) {
    let n = t[0].len().trailing_zeros() as usize;
    let mut point = Vec::with_capacity(n);
    for _ in 0..n {
        let (c0, c2) = round([&t[0], &t[1], &t[2], &t[3]]);
        let c1 = claim + c2; // q(0) + q(1) = c1 + c2 in characteristic 2
        ps.add_round_poly_ext(&[c0, c1, c2], false);
        let r = ps.challenge::<F, W>(Grp::C2);
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
pub fn ks_kernel<F: Ext<W>, const W: usize>(eqr: &[F], cont: &[bool]) -> Vec<F> {
    let n = eqr.len();
    (0..n).map(|k| if k + 1 < n && cont[k + 1] { eqr[k + 1] } else { F::ZERO }).collect()
}

/// Prove the KS link (the `KSlink` phase). Returns `[Y^ω, in^ω, M^ω, X^ω]` claims (Lean order; E2F: at E2 each word
/// claim is its two coordinate claims in place, [`Claim::word`]).
pub fn prove_ks<F: Ext<W>, const W: usize>(ps: &mut ProverState, lay: &Layout, ks: &Sponge) -> Vec<Claim> {
    let kl = lay.ks_log;
    let n = 1usize << kl;
    let mut tp = std::time::Instant::now();
    let chal = ps.challenges::<F, W>(Grp::C1, kl + LANE_BITS);
    crate::lvm::stream::part("ksl sample", &mut tp);
    let (rho, lam) = (&chal[..kl], &chal[kl..]);
    let om = F::eq_table(lam);
    let eqr = F::eq_table(rho);
    let sc = ks_kernel(&eqr, &ks.cont);
    let comb = |w: &[u64]| -> F { w.iter().zip(&om).map(|(&x, &o)| o.mul_base(F64(x))).sum() };
    let yw: Vec<F> = crate::lv::parallel::map_collect(n, |k| comb(&ks.outputs[k]));
    let rest: Vec<F> = crate::lv::parallel::map_collect(n, |k| comb(&ks.inputs[k]) + comb(&ks.msg[k]));
    crate::lvm::stream::part("ksl tabs", &mut tp);
    let (rho1, _f, fin) = sumcheck2(ps, [sc, yw, eqr, rest], F::ZERO);
    crate::lvm::stream::part("ksl sc", &mut tp);
    let eq1 = F::eq_table(&rho1);
    let at = |f: &(dyn Fn(usize) -> F + Sync)| -> F {
        crate::lv::parallel::fold_reduce(n, || F::ZERO, |acc, k| *acc += eq1[k] * f(k), |a, b| a + b)
    };
    let y = at(&|k| comb(&ks.outputs[k]));
    let inw = at(&|k| comb(&ks.inputs[k]));
    // KS14 (CR-DES §2): rows `< split` absorb `M` (C_rec, `2^rec` rows: its weight is `eq(ρ'_{<rec}, ·)` on rows
    // `< split` only), rows `≥ split` absorb `X` (`2^x_log` rows, weight `eq(ρ'_{<x_log}, ·)`); the message at `ρ'` is
    // `selM·mw + selX·xw`, `selM = Π_{rec ≤ t < ks}(1 + ρ'_t)`, `selX = Π_{x_log ≤ t < ks} ρ'_t` (P8: `1 + ρ'₁₃`, `ρ'₁₃`)
    // (KS13, roll 8: `ks_log < rec_log`; M's weight is on its first `2^ks_log` rows, `LvmDecideV0.ksLink14`: `r` below is
    // `min(rec, ks)`, so KS14 and v1 are unchanged)
    let (r, xl, split) = (lay.rec_log.min(kl), lay.x_log, lay.ks_split);
    let eq_m = F::eq_table(&rho1[..r]);
    let eq_x = F::eq_table(&rho1[..xl]);
    let mw: F = (0..split).map(|i| eq_m[i] * comb(&ks.msg[i])).sum();
    let xw: F = (0..1usize << xl).map(|i| eq_x[i] * comb(&ks.msg[split + i])).sum();
    let sel_m: F = rho1[r..kl].iter().map(|&t| F::ONE + t).fold(F::ONE, |a, b| a * b);
    let sel_x: F = rho1[xl..kl].iter().copied().fold(F::ONE, |a, b| a * b);
    assert!(fin[3] == inw + sel_m * mw + sel_x * xw, "KS link: in + Msg at ρ' splits into the M and X claims");
    crate::lvm::stream::part("ksl evals", &mut tp);
    ps.add_ext(&[y, inw, mw, xw]);
    crate::lvm::stream::part("ksl add", &mut tp);
    let y_terms = (0..LANES).map(|l| (lay.ks_y(l), rho1.clone(), om[l])).collect();
    let in_terms = (0..LANES).map(|l| (lay.ks_slot(l), rho1.clone(), om[l])).collect();
    // M's weight: `eq(ρ'_{<rec}, ·)` less its top `2^rec − split` rows (KS14: the aligned block `[split, 2^rec)`, where
    // `eq(ρ'_{<rec}, split + i) = eq(ρ'_{<x_log}, i)·Π_{x_log ≤ t < rec} ρ'_t`; in characteristic 2, less is plus)
    let mut m_terms: Vec<(usize, Vec<F>, F)> = (0..REC_STREAM_COLS).map(|l| (lay.rec_col(l), rho1[..r].to_vec(), om[l])).collect();
    if split < 1 << r {
        assert_eq!(split, (1usize << r) - (1usize << xl), "the top block of M is X's size");
        let top: F = rho1[xl..r].iter().copied().fold(F::ONE, |a, b| a * b);
        m_terms.extend((0..REC_STREAM_COLS).map(|l| (lay.rec_col(l) + split, rho1[..xl].to_vec(), om[l] * top)));
    }
    let x_terms = (0..REC_STREAM_COLS).map(|l| (lay.x(l), rho1[..xl].to_vec(), om[l])).collect();
    let (yc, ic, mc, xc) = (Claim::word(y_terms, y), Claim::word(in_terms, inw), Claim::word(m_terms, mw), Claim::word(x_terms, xw));
    if W == 3 {
        return [yc, ic, mc, xc].concat();
    }
    // E2F (S2GF, E2F-V 18:01): the spec's `ordM r m = r.take 2 ++ m.dropLast ++ r.drop 2 ++ [m.last]` on the split
    // claims: Y_re, Y_im, in_re, in_im, X_re, M_re, M_im, X_im
    let [y0, y1]: [Claim; 2] = yc.try_into().expect("two");
    let [i0, i1]: [Claim; 2] = ic.try_into().expect("two");
    let [m0, m1]: [Claim; 2] = mc.try_into().expect("two");
    let [x0, x1]: [Claim; 2] = xc.try_into().expect("two");
    vec![y0, y1, i0, i1, x0, m0, m1, x1]
}
