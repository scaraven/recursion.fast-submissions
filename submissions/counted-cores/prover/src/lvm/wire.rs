//! S2's chain wiring (BLUEPRINT2 §1.2 T3–T4; docs/lvm2/stages/T-P1.md, Conventions C.5–C.6).
//!
//! The tape's GKR ends with a claim on the virtual input state, `C_in = Σ_i ι(i)·⟨ω, in(i)⟩` with
//! `ι(i) = eq(ρ, i ≫ 4)·μ[i & 15]`. On the chain, `in(0) = Pad43(s)`, `in(i) = Pad43(D[i − 1])` for `1 ≤ i ≤ m`
//! (`m = n − 1`) and `in(i) = 0` beyond, so `C_in = const + Σ_x K_ch(x)·G_D(x)` with
//! `const = ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i=1}^{m} ι(i)`, `K_ch(x) = ι(x + 1)·[x + 1 ≤ m]` and
//! `G_D(x) = Σ_{p<256} ω(8 + p)·bit_p(D[x])`. One degree-2 sumcheck over `x` (low bit first) ends at `σ`; the prover
//! sends `g_D = G̃_D(σ)`, and a 2-round slot sumcheck over the lane `l` reduces it to the 64 bit slices of the `D`
//! block at `(σ, τ)`, a ring-switched claim on `C_main`.
//!
//! The prover works on the live prefix (`x < n`): `K_ch` vanishes past it and `G_D` is the constant `G_D(z*)` (dead
//! rows hold `z*[0..4)`), a tail that folds to itself. The verifier's closed forms (`k_ch_mle`, `iota_prefix_sum`,
//! `lt_mle`) are asserted against the prover's tables on every proof.

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::keccak_gkr::Claim as GkrClaim;
use crate::lv::primitives::field::{Ext, F64, F128, F192, Unreduced};
use crate::lvm::front::{E2Term, bitdot, byte_tables, eq_eval, eq_prefix, fold_1b_rows, lt_mle, row_switch, to_e2, to_e3};
use crate::lvm::link::Claim;
use crate::lvm::params::{LANES, PAD_SHIFT, RING_STAGES};
use crate::lvm::tables::{Chain, Layout};
/// lvm2 W32: a pack is `PACK = 32` instances, `PB = 5` low instance bits (`LvmVCore.packBits`).
use crate::lv::keccak_gkr::rmfe::{PACK, PACK_BITS as PB};
use crate::oracle::Digest;

/// `⟨ω, v⟩ = Σ_j ω(j)·bit_j(v)`, `j = 64·lane + z`.
pub fn omega_dot<F: Ext<W>, const W: usize>(omega: &[F], v: &[u64; LANES]) -> F {
    let mut acc = F::ZERO;
    for (l, &w) in v.iter().enumerate() {
        let mut bits = w;
        while bits != 0 {
            acc += omega[64 * l + bits.trailing_zeros() as usize];
            bits &= bits - 1;
        }
    }
    acc
}

/// `ι(i) = eq(ρ, i ≫ 5)·μ[i & 31]` for `i < len`.
pub fn iota_table<F: Ext<W>, const W: usize>(rho: &[F], mu: &[F; PACK], len: usize) -> Vec<F> {
    let packs = eq_prefix(rho, len.div_ceil(PACK).min(1 << rho.len()));
    (0..len).map(|i| packs[i >> PB] * mu[i & (PACK - 1)]).collect()
}

/// `Σ_{i<t} ι(i)` in closed form (`t ≤ 2^(|ρ| + 5)`): whole packs by `lt̃`, the partial pack by its `μ` prefix.
pub fn iota_prefix_sum<F: Ext<W>, const W: usize>(rho: &[F], mu: &[F; PACK], t: usize) -> F {
    let (q, r) = (t >> PB, t & (PACK - 1));
    let total: F = mu.iter().copied().sum();
    let mut s = lt_mle(rho, q) * total;
    if r > 0 {
        let bits: Vec<F> = (0..rho.len()).map(|k| if (q >> k) & 1 == 1 { F::ONE } else { F::ZERO }).collect();
        s += eq_eval(rho, &bits) * mu[..r].iter().copied().sum::<F>();
    }
    s
}

/// `K̃_ch(σ) = Σ_{x < 2^w} eq(σ, x)·ι(x + 1)·[x + 1 ≤ m]` (BLUEPRINT2's `MS_w^0(σ; m)`): the low five bits as one
/// digit of 32 values (`μ` is not a tensor), then a carry × comparison automaton over bits `5 … w − 1`, low first;
/// accept: no carry out, `x + 1 ≤ m`.
pub fn k_ch_mle<F: Ext<W>, const W: usize>(sigma: &[F], rho: &[F], mu: &[F; PACK], m: usize) -> F {
    let w = sigma.len();
    assert_eq!(rho.len() + PB, w);
    // st[carry][cmp], cmp: 0 lt, 1 eq, 2 gt (of y = x + 1 against m, on the bits so far)
    let mut st = [[F::ZERO; 3]; 2];
    let e4 = F::eq_table(&sigma[..PB]);
    let m4 = m & (PACK - 1);
    for d in 0..PACK {
        let y = (d + 1) & (PACK - 1);
        let c = usize::from(d == PACK - 1);
        let cmp = if y < m4 { 0 } else if y == m4 { 1 } else { 2 };
        st[c][cmp] += e4[d] * mu[y];
    }
    for k in PB..w {
        let mk = (m >> k) & 1;
        let mut nx = [[F::ZERO; 3]; 2];
        for c in 0..2 {
            for cmp in 0..3 {
                let v = st[c][cmp];
                if v == F::ZERO {
                    continue;
                }
                for xb in 0..2usize {
                    let yb = xb ^ c;
                    let wx = if xb == 1 { sigma[k] } else { F::ONE + sigma[k] };
                    let wy = if yb == 1 { rho[k - PB] } else { F::ONE + rho[k - PB] };
                    let ncmp = if yb < mk { 0 } else if yb > mk { 2 } else { cmp };
                    nx[xb & c][ncmp] += v * wx * wy;
                }
            }
        }
        st = nx;
    }
    st[0][0] + st[0][1]
}

/// The verifier's constant of the wiring identity: `ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i=1}^{m} ι(i)`.
pub fn wire_const<F: Ext<W>, const W: usize>(fin: &GkrClaim<F>, s: &Digest, n: usize) -> F {
    let iota0 = eq_eval(&fin.point, &vec![F::ZERO; fin.point.len()]) * fin.mu[0];
    let c43 = crate::keccak::chain_block(&[0u8; 32]);
    let pad_s = crate::keccak::chain_block(s);
    iota0 * omega_dot(&fin.weights, &pad_s) + omega_dot(&fin.weights, &c43) * (iota_prefix_sum(&fin.point, &fin.mu, n) + iota0)
}

/// One round of `Σ a·b` (degree 2), variable 0 first: `(q(0), q₂)`.
fn round_ab<F: Ext<W>, const W: usize>(a: &[F], b: &[F]) -> (F, F) {
    let half = a.len() / 2;
    crate::lv::parallel::fold_reduce(
        half,
        || (F::ZERO, F::ZERO),
        |acc, j| {
            let (a0, a1, b0, b1) = (a[2 * j], a[2 * j + 1], b[2 * j], b[2 * j + 1]);
            acc.0 += a0 * b0;
            acc.1 += (a0 + a1) * (b0 + b1);
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

fn fold<F: Ext<W>, const W: usize>(v: &[F], r: F) -> Vec<F> {
    crate::lv::parallel::map_collect(v.len() / 2, |j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1]))
}

/// The sumcheck of `Σ_{x<2^vars} a(x)·b(x)` from `claim`, with `a` zero and `b` the constant `b_tail` past the stored
/// prefixes (equal lengths). Sends `(c₀, c₂)` per round (E2F: in the front's field, challenges of group `c = 2`).
/// Returns `σ`, the final claim, `ã(σ)` and `b̃(σ)` (exact: a constant tail folds to itself).
pub fn sumcheck_ab_live<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    mut a: Vec<F>,
    mut b: Vec<F>,
    b_tail: F,
    mut claim: F,
    vars: usize,
) -> (Vec<F>, F, F, F) {
    assert_eq!(a.len(), b.len());
    let mut point = Vec::with_capacity(vars);
    for _ in 0..vars {
        let m = a.len().max(1);
        let m2 = m + (m & 1);
        a.resize(m2, F::ZERO);
        b.resize(m2, b_tail);
        let (c0, c2) = round_ab(&a, &b);
        let c1 = claim + c2;
        ps.add_round_poly_ext(&[c0, c1, c2], false);
        let r = ps.challenge::<F, W>(Grp::C2);
        claim = c0 + r * (c1 + r * c2);
        a = fold(&a, r);
        b = fold(&b, r);
        point.push(r);
    }
    (point, claim, a[0], b[0])
}

/// T3 and T4 (the `Wire` phase). `fin` is the tape GKR's input claim; returns the `D` ring claim on `C_main` (E2F: at
/// E2 the row switch, `lvm::front`: 64 E2 slices, then 7 plain E3 samples).
#[allow(clippy::too_many_arguments)]
pub fn prove_wire<F: Ext<W>, const W: usize>(ps: &mut ProverState, lay: &Layout, ch: &Chain, cmain: &[F64], fin: &GkrClaim<F>, s: &Digest, n: usize, dense: bool) -> Claim {
    let ln = lay.log_n;
    let big = 1usize << ln;
    assert!(n >= 1 && n <= big);
    let m = n - 1;
    let (rho, mu, omega) = (&fin.point[..], &fin.mu, &fin.weights[..]);
    assert_eq!(rho.len() + PB, ln);
    let live = if dense { big } else { n };

    // ---- T3: the wiring sumcheck
    let iota = iota_table(rho, mu, (live + 1).min(big));
    let k: Vec<F> = (0..live).map(|x| if x + 1 <= m { iota[x + 1] } else { F::ZERO }).collect();
    let w: Vec<[F; 64]> = (0..4).map(|l| std::array::from_fn(|z| omega[PAD_SHIFT + 64 * l + z])).collect();
    let tw: Vec<Vec<[F; 256]>> = w.iter().map(byte_tables).collect();
    let g_of = |d: &[u64; 4]| -> F { (0..4).map(|l| bitdot(&tw[l], d[l])).sum() };
    let g: Vec<F> = crate::lv::parallel::map_collect(live, |x| g_of(&ch.y[x]));
    let g_tail = g_of(&ch.y[big - 1]); // a dead row (z*), or a live one when n = 2^log_n (then no tail is read)
    let c = wire_const(fin, s, n);
    let (sigma, fin_claim, k_s, g_s) = sumcheck_ab_live(ps, k, g, g_tail, fin.value + c, ln);
    assert!(k_s == k_ch_mle(&sigma, rho, mu, m), "K̃_ch(σ) in closed form");
    assert!(fin_claim == k_s * g_s, "the wiring identity C_in = const + Σ K_ch·G_D");
    ps.add_ext(&[g_s]);

    // ---- T4: the D slot reduction (2 rounds over the lane), the 64 slices, the ring switch
    let eqs: Vec<F> = if dense { F::eq_table(&sigma) } else { eq_prefix(&sigma, n) };
    let lt: F = eqs[..n].iter().copied().sum();
    assert!(lt == lt_mle(&sigma, n), "lt̃_n(σ) in closed form");
    let bmat: Vec<[F; 64]> = (0..4)
        .map(|l| {
            // SH2-Z: the buffer holds D's rows < 2^d_log; the dense reference reads every row (z* above) from the walk
            let mut v = if live <= 1 << lay.d_log {
                fold_1b_rows(&cmain[lay.d(l)..][..live], &eqs[..live])
            } else {
                let col: Vec<F64> = ch.y[..live].iter().map(|y| F64(y[l])).collect();
                fold_1b_rows(&col, &eqs[..live])
            };
            if !dense && n < big {
                let zl = ch.y[big - 1][l];
                for (q, v) in v.iter_mut().enumerate() {
                    if (zl >> q) & 1 == 1 {
                        *v += F::ONE + lt;
                    }
                }
            }
            v
        })
        .collect();
    let mut a: Vec<Vec<F>> = w.iter().map(|v| v.to_vec()).collect();
    let mut b: Vec<Vec<F>> = bmat.iter().map(|v| v.to_vec()).collect();
    let mut claim = g_s;
    let mut tau = Vec::new();
    for _ in 0..2 {
        let half = a.len() / 2;
        let (mut c0, mut c2) = (F::ZERO, F::ZERO);
        for j in 0..half {
            for q in 0..64 {
                let (a0, a1, b0, b1) = (a[2 * j][q], a[2 * j + 1][q], b[2 * j][q], b[2 * j + 1][q]);
                c0 += a0 * b0;
                c2 += (a0 + a1) * (b0 + b1);
            }
        }
        let c1 = claim + c2;
        ps.add_round_poly_ext(&[c0, c1, c2], false);
        let r = ps.challenge::<F, W>(Grp::C2);
        claim = c0 + r * (c1 + r * c2);
        let f = |v: &Vec<Vec<F>>| -> Vec<Vec<F>> {
            (0..half).map(|j| (0..64).map(|q| v[2 * j][q] + r * (v[2 * j][q] + v[2 * j + 1][q])).collect()).collect()
        };
        a = f(&a);
        b = f(&b);
        tau.push(r);
    }
    let slices = b[0].clone();
    assert!(claim == (0..64).map(|q| a[0][q] * slices[q]).sum::<F>(), "the slot reduction's final");
    ps.add_ext(&slices);
    let point = [&sigma[..], &tau[..]].concat();
    if W == 3 {
        let map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
        return Claim::ring(lay.d_off, point.into_iter().map(to_e3).collect(), slices.into_iter().map(to_e3).collect(), map);
    }
    let r2 = ps.sample_vec(ROW_SWITCH_STAGES);
    let slices: Vec<F128> = slices.into_iter().map(to_e2).collect();
    let (phi, sigma_t) = row_switch(&slices, &r2);
    Claim::E2 { terms: vec![E2Term { offset: lay.d_off, point: point.into_iter().map(to_e2).collect(), phi, klin: false }], value: sigma_t }
}

/// E2F (S2GF): the row switch's E3 ring-map samples (`2^7` rows).
pub const ROW_SWITCH_STAGES: usize = 7;

/// Dev checks (`lvm-prover s2check`; the crate's `cargo test` does not build with the vendored modules).
pub mod check {
    use super::*;
    use crate::lv::primitives::multilinear::eq_table;
    fn rnd(seed: &mut u64) -> F192 {
        let mut x = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        F192::new(x(), x(), x())
    }
    pub fn closed_forms_match_brute_force() {
        let mut seed = 0x1234_5678_9abc_def1u64;
        let w = 8;
        let sigma: Vec<F192> = (0..w).map(|_| rnd(&mut seed)).collect();
        let rho: Vec<F192> = (0..w - PB).map(|_| rnd(&mut seed)).collect();
        let mu: [F192; PACK] = std::array::from_fn(|_| rnd(&mut seed));
        let iota = iota_table(&rho, &mu, 1 << w);
        let es = eq_table(&sigma);
        for m in [0usize, 1, 2, 15, 16, 17, 31, 32, 33, 100, 255] {
            let brute: F192 = (0..(1usize << w)).filter(|&x| x + 1 <= m).map(|x| es[x] * iota[x + 1]).sum();
            assert_eq!(k_ch_mle(&sigma, &rho, &mu, m), brute, "K_ch at m = {m}");
        }
        for t in [0usize, 1, 15, 16, 17, 31, 32, 33, 100, 256] {
            let brute: F192 = iota[..t].iter().copied().sum();
            assert_eq!(iota_prefix_sum(&rho, &mu, t), brute, "prefix at t = {t}");
        }
    }
}

// ------------------------------------------------------------------------------------- U-TAPE (stage S2GU, E2)
//
// The tape has `2^21` rows (`ρ ∈ F^17`): the chain half `i < 2^20` as S2GT, the sponge half `2^20 + j` (`j < 2^hs`,
// `hs = ks_log` = 13: KS13's rows; `j ≥ 2^hs` void). On `x < 2^20` (COMMON T3, T-W's `wireProg` without the M/X split):
//   `T(x) = K_ch(x)·G_D(x) + K_ks(x)·G_Y(x) + I_ks(x)·G_M(x)`,
// `K_ch(x) = ι(x + 1)·[x + 1 ≤ m]`, `K_ks(x) = [x < 2^hs − 1]·cont_{x+1}·ι(2^20 + x + 1)`, `I_ks(x) = [x < 2^hs]·ι(2^20 + x)`;
// `G_Y` (all 1600 bits of `Y[x]`) and `G_M` (the 1088 rate bits of `Msg[x]`) are periodic mod `2^hs`. The final check
// is `claim = K̃_ch(σ)·g_D + e'·(K̃_ks(σ')·g_Y + Ĩ_ks(σ')·g_M)`, `σ' = σ_{<hs}`, `e' = Π_{k=hs}^{19}(1 − σ_k)`; then
// the slot reductions `D` (2 rounds), `Y` (5: the `Y` block, 32 slots of `2^hs`), `M` (5: the stream block `S`'s 32
// columns at row point `(σ', 0)`), each with its 64 slices and the row switch.

/// A product term `a·b` of a sumcheck: `a` is zero past its prefix; `b` is the constant `Some(c)` past it, or (`None`)
/// periodic with the prefix's length, a power of two (an extension constant in the high variables).
pub struct Term<F> {
    pub a: Vec<F>,
    pub b: Vec<F>,
    pub tail: Option<F>,
}

/// The sumcheck of `Σ_{x<2^vars} Σ_t a_t(x)·b_t(x)` from `claim` (degree 2, `(c₀, c₁, c₂)` per round, variable 0
/// first, challenges of group `c = 2`). Returns `σ` and the final claim; each term's tables end folded to one entry,
/// `ã_t(σ)` and `b̃_t(σ)`.
pub fn sumcheck_terms<F: Ext<W>, const W: usize>(ps: &mut ProverState, terms: &mut [Term<F>], mut claim: F, vars: usize) -> (Vec<F>, F) {
    let mut point = Vec::with_capacity(vars);
    for _ in 0..vars {
        let (mut c0, mut c2) = (F::ZERO, F::ZERO);
        for t in terms.iter_mut() {
            assert_eq!(t.a.len(), t.b.len());
            let m = t.a.len();
            if m & 1 == 1 {
                let bt = match t.tail {
                    Some(c) => c,
                    None => {
                        assert_eq!(m, 1, "a periodic table has a power-of-two prefix");
                        t.b[0]
                    }
                };
                t.a.push(F::ZERO);
                t.b.push(bt);
            }
            let (x0, x2) = round_ab(&t.a, &t.b);
            c0 += x0;
            c2 += x2;
        }
        let c1 = claim + c2;
        ps.add_round_poly_ext(&[c0, c1, c2], false);
        let r = ps.challenge::<F, W>(Grp::C2);
        claim = c0 + r * (c1 + r * c2);
        for t in terms.iter_mut() {
            t.a = fold(&t.a, r);
            t.b = fold(&t.b, r);
        }
        point.push(r);
    }
    (point, claim)
}

/// A slot reduction (T-W's `slotProg`) at the front's field: `claim = Σ_{o,z} A(o, z)·B(o, z)` over `2^b` slots `o`
/// and 64 bits `z`; `b` degree-2 rounds over the slot bits (low first, group `c = 2`), the 64 slices `B̃(τ, ·)` (sent),
/// then (E2) the row switch's 7 plain samples. Asserts the final `claim = Σ_z Ã(τ, z)·B̃(τ, z)`. Returns `τ` and the
/// slices; the caller makes the claim.
pub fn slot_reduce<F: Ext<W>, const W: usize>(ps: &mut ProverState, mut a: Vec<[F; 64]>, mut b: Vec<[F; 64]>, mut claim: F) -> (Vec<F>, Vec<F>) {
    assert!(a.len().is_power_of_two() && a.len() == b.len());
    let mut tau = Vec::new();
    while a.len() > 1 {
        let half = a.len() / 2;
        let (mut c0, mut c2) = (F::Unreduced::ZERO, F::Unreduced::ZERO);
        for j in 0..half {
            for q in 0..64 {
                let (a0, a1, b0, b1) = (a[2 * j][q], a[2 * j + 1][q], b[2 * j][q], b[2 * j + 1][q]);
                c0 ^= a0.mul_unreduced(b0);
                c2 ^= (a0 + a1).mul_unreduced(b0 + b1);
            }
        }
        let (c0, c2) = (c0.reduce(), c2.reduce());
        let c1 = claim + c2;
        ps.add_round_poly_ext(&[c0, c1, c2], false);
        let r = ps.challenge::<F, W>(Grp::C2);
        claim = c0 + r * (c1 + r * c2);
        let f = |v: &Vec<[F; 64]>| -> Vec<[F; 64]> {
            (0..half).map(|j| std::array::from_fn(|q| v[2 * j][q] + r * (v[2 * j][q] + v[2 * j + 1][q]))).collect()
        };
        a = f(&a);
        b = f(&b);
        tau.push(r);
    }
    let slices = b[0].to_vec();
    // (a dev tamper of a committed word, `LVM_TYPED_TAMPER`, breaks it; V_S must reject the proof)
    assert!(
        claim == (0..64).map(|q| a[0][q] * slices[q]).sum::<F>() || std::env::var_os("LVM_TYPED_TAMPER").is_some(),
        "the slot reduction's final"
    );
    ps.add_ext(&slices);
    (tau, slices)
}

/// The row switch's claim (E2: 7 plain samples, `lvm::front::row_switch`; E3: v1's ring with 6 samples) on the
/// aligned block at `offset`, at `point`, from the 64 slices.
fn switch_claim<F: Ext<W>, const W: usize>(ps: &mut ProverState, offset: usize, point: Vec<F>, slices: Vec<F>) -> Claim {
    if W == 3 {
        let map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
        return Claim::ring(offset, point.into_iter().map(to_e3).collect(), slices.into_iter().map(to_e3).collect(), map);
    }
    let r2 = ps.sample_vec(ROW_SWITCH_STAGES);
    let slices: Vec<F128> = slices.into_iter().map(to_e2).collect();
    let (phi, sigma_t) = row_switch(&slices, &r2);
    Claim::E2 { terms: vec![E2Term { offset, point: point.into_iter().map(to_e2).collect(), phi, klin: false }], value: sigma_t }
}

fn eq1<F: Ext<W>, const W: usize>(a: F, b: F) -> F {
    a * b + (F::ONE + a) * (F::ONE + b)
}

/// `c_sp = Π_{k=hs−5}^{w−6}(1 − ρ_k)·ρ_{w−5}`: `ι(2^w + y) = c_sp·eq(ρ_{<hs−5}, y ≫ 5)·μ[y & 31]` for `y < 2^hs`
/// (`|ρ| = w − 4`).
fn c_sp<F: Ext<W>, const W: usize>(rho: &[F], w: usize, hs: usize) -> F {
    let mut c = rho[w - PB];
    for &r in &rho[hs - PB..w - PB] {
        c *= F::ONE + r;
    }
    c
}

/// The runs of `cont` (`[a, b]`, every row of it continuing).
pub fn cont_runs(cont: &[bool]) -> Vec<(usize, usize)> {
    let mut runs = Vec::new();
    let mut x = 1usize;
    while x < cont.len() {
        if cont[x] {
            let a = x;
            while x + 1 < cont.len() && cont[x + 1] {
                x += 1;
            }
            runs.push((a, x));
        }
        x += 1;
    }
    runs
}

/// The verifier's closed forms of the sponge kernels at `σ' ∈ F^hs` (`ρ ∈ F^(w−3)`), as `hs`-variable MLEs:
/// `(K̃_ks(σ'), Ĩ_ks(σ'))`. `K̃_ks` is `c_sp` times a sum of `MS` differences over `cont`'s runs (T-K's `kksE`: `k_ch_mle`
/// on `hs` bits, `MS(b) − MS(a − 1)` per run `[a, b]`); `Ĩ_ks = c_sp·(Σ_d eq(σ'_{<5}, d)·μ[d])·Π_{k=5}^{hs−1} eq(ρ_{k−5}, σ'_k)`
/// (T-K's `ikEval`).
pub fn sponge_kernels_u<F: Ext<W>, const W: usize>(sig: &[F], rho: &[F], mu: &[F; PACK], w: usize, cont: &[bool]) -> (F, F) {
    let hs = sig.len();
    assert_eq!(rho.len() + PB - 1, w);
    assert_eq!(cont.len(), 1 << hs);
    let c = c_sp(rho, w, hs);
    let rs = &rho[..hs - PB];
    let mut kks = F::ZERO;
    for (a, b) in cont_runs(cont) {
        kks += k_ch_mle(sig, rs, mu, b) + k_ch_mle(sig, rs, mu, a - 1);
    }
    let e4 = F::eq_table(&sig[..PB]);
    let mut ik: F = (0..PACK).map(|d| e4[d] * mu[d]).sum::<F>() * c;
    for k in PB..hs {
        ik *= eq1(rho[k - PB], sig[k]);
    }
    (c * kks, ik)
}

/// What S2GU's `Wire` phase leaves on `C_main`: the `D`, `Y` and `M` row-switch claims (UT-V's order: D, Y, M).
pub struct WireU {
    pub d: Claim,
    pub y: Claim,
    pub m: Claim,
}

/// S2GU's T3 and T4 (COMMON; at E2 with `F = F128`). `ch` holds `2^20` digest rows (`z*` past `n`); `ks` KS13's rows;
/// `fin` the tape's input claim (`|ρ| = 17`). `dense` builds every table over `2^20` rows from `C_main` (the oracle).
#[allow(clippy::too_many_arguments)]
pub fn prove_wire_u<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    lay: &Layout,
    ch: &Chain,
    ks: &crate::lvm::tables::Sponge,
    cmain: &[F64],
    fin: &GkrClaim<F>,
    s: &Digest,
    n: usize,
    dense: bool,
) -> WireU {
    use crate::lvm::params::REC_STREAM_COLS;
    let w = lay.log_n;
    let hs = lay.ks_log;
    let big = 1usize << w;
    let nh = 1usize << hs;
    assert!(n >= 1 && n <= big && nh <= big && ks.outputs.len() == nh);
    let m = n - 1;
    let (rho, mu, omega) = (&fin.point[..], &fin.mu, &fin.weights[..]);
    assert_eq!(rho.len() + PB - 1, w, "ι is over w + 1 = 21 bits");
    let live = if dense { big } else { n };

    // ---- the tables
    // (ι over 21 bits; for i < 2^20 its top coordinate's factor (1 − ρ_16) is in `eq_prefix`)
    let iota = iota_table(rho, mu, (live + 1).min(big));
    let k_ch: Vec<F> = (0..live).map(|x| if x + 1 <= m { iota[x + 1] } else { F::ZERO }).collect();
    let csp = c_sp(rho, w, hs);
    let packs = F::eq_table(&rho[..hs - PB]);
    let iota_sp = |y: usize| -> F { if y < nh { csp * packs[y >> PB] * mu[y & (PACK - 1)] } else { F::ZERO } };
    let k_ks: Vec<F> = (0..nh).map(|x| if x + 1 < nh && ks.cont[x + 1] { iota_sp(x + 1) } else { F::ZERO }).collect();
    let i_ks: Vec<F> = (0..nh).map(iota_sp).collect();
    let wd: Vec<[F; 64]> = (0..4).map(|l| std::array::from_fn(|z| omega[PAD_SHIFT + 64 * l + z])).collect();
    let tw_d: Vec<Vec<[F; 256]>> = wd.iter().map(byte_tables).collect();
    let wl: Vec<[F; 64]> = (0..LANES).map(|l| std::array::from_fn(|z| omega[64 * l + z])).collect();
    let tw: Vec<Vec<[F; 256]>> = wl.iter().map(byte_tables).collect();
    let g_d_of = |d: [u64; 4]| -> F { (0..4).map(|l| bitdot(&tw_d[l], d[l])).sum() };
    let g_of = |v: &[u64]| -> F { v.iter().enumerate().map(|(l, &x)| bitdot(&tw[l], x)).sum() };
    let word = |o: usize| cmain[o].0;
    let mut terms: Vec<Term<F>> = if dense {
        // every table over 2^20 rows, read from C_main (D's rows past the buffer's from the walk), the periodic
        // extensions written out
        let pad = |mut v: Vec<F>| -> Vec<F> {
            v.resize(big, F::ZERO);
            v
        };
        let held = 1usize << lay.d_log;
        let g_d: Vec<F> = crate::lv::parallel::map_collect(big, |x| {
            g_d_of(std::array::from_fn(|l| if x < held { word(lay.d(l) + x) } else { ch.y[x][l] }))
        });
        let g_y: Vec<F> = crate::lv::parallel::map_collect(big, |x| {
            let v: Vec<u64> = (0..LANES).map(|l| word(lay.y_off + (l << hs) + (x & (nh - 1)))).collect();
            g_of(&v)
        });
        let g_m: Vec<F> = crate::lv::parallel::map_collect(big, |x| {
            let v: Vec<u64> = (0..REC_STREAM_COLS).map(|l| word(lay.rec_col(l) + (x & (nh - 1)))).collect();
            g_of(&v)
        });
        vec![
            Term { a: k_ch, b: g_d, tail: None },
            Term { a: pad(k_ks), b: g_y, tail: None },
            Term { a: pad(i_ks), b: g_m, tail: None },
        ]
    } else {
        let g_d: Vec<F> = crate::lv::parallel::map_collect(live, |x| g_d_of(ch.y[x]));
        let g_tail = g_d_of(ch.y[big - 1]); // a dead row (z*), or a live one when n = 2^w (then no tail is read)
        let g_y: Vec<F> = crate::lv::parallel::map_collect(nh, |x| g_of(&ks.outputs[x]));
        let g_m: Vec<F> = crate::lv::parallel::map_collect(nh, |x| g_of(&ks.msg[x]));
        vec![
            Term { a: k_ch, b: g_d, tail: Some(g_tail) },
            Term { a: k_ks, b: g_y, tail: None },
            Term { a: i_ks, b: g_m, tail: None },
        ]
    };

    // ---- T3
    let c = wire_const(fin, s, n);
    let (sigma, fin_claim) = sumcheck_terms(ps, &mut terms, fin.value + c, w);
    let sig_s = &sigma[..hs];
    let mut e_s = F::ONE;
    for &x in &sigma[hs..w] {
        e_s *= F::ONE + x;
    }
    let kch = k_ch_mle(&sigma, &rho[..w - PB], mu, m) * (F::ONE + rho[w - PB]);
    let (kks, iks) = sponge_kernels_u(sig_s, rho, mu, w, &ks.cont);
    assert!(terms[0].a[0] == kch, "K̃_ch(σ) in closed form");
    assert!(terms[1].a[0] == e_s * kks, "K̃_ks(σ) = e'·K̃_ks(σ') in closed form");
    assert!(terms[2].a[0] == e_s * iks, "Ĩ_ks(σ) = e'·Ĩ_ks(σ') in closed form");
    let (g_d, g_y, g_m) = (terms[0].b[0], terms[1].b[0], terms[2].b[0]);
    // (a dev tamper of a committed word, `LVM_TYPED_TAMPER`, breaks it; V_S must reject the proof)
    assert!(
        fin_claim == kch * g_d + e_s * (kks * g_y + iks * g_m) || std::env::var_os("LVM_TYPED_TAMPER").is_some(),
        "the wiring identity's final check"
    );
    ps.add_ext(&[g_d, g_y, g_m]);
    drop(terms);

    // ---- T4: D (2 slot rounds; the D block at (σ, τ))
    let eqs: Vec<F> = if dense { F::eq_table(&sigma) } else { eq_prefix(&sigma, n) };
    let lt: F = eqs[..n].iter().copied().sum();
    assert!(lt == lt_mle(&sigma, n), "lt̃_n(σ) in closed form");
    let bd: Vec<[F; 64]> = (0..4)
        .map(|l| {
            // SH2-Z: the buffer holds D's rows < 2^d_log; the dense reference reads every row (z* above) from the walk
            let mut v = if live <= 1 << lay.d_log {
                fold_1b_rows(&cmain[lay.d(l)..][..live], &eqs[..live])
            } else {
                let col: Vec<F64> = ch.y[..live].iter().map(|y| F64(y[l])).collect();
                fold_1b_rows(&col, &eqs[..live])
            };
            if !dense && n < big {
                let zl = ch.y[big - 1][l];
                for (q, v) in v.iter_mut().enumerate() {
                    if (zl >> q) & 1 == 1 {
                        *v += F::ONE + lt;
                    }
                }
            }
            v
        })
        .collect();
    let (tau_d, sl_d) = slot_reduce(ps, wd, bd, g_d);
    let d = switch_claim(ps, lay.d_off, [&sigma[..], &tau_d[..]].concat(), sl_d);

    // ---- Y (5 slot rounds over the Y block's 32 slots of 2^hs rows at σ'; weights ω on lanes 0–24)
    let eh = F::eq_table(sig_s);
    let ys = 1usize << crate::lvm::params::UT_Y_SLOTS_LOG;
    let y_a: Vec<[F; 64]> = (0..ys).map(|o| if o < LANES { wl[o] } else { [F::ZERO; 64] }).collect();
    let y_b: Vec<[F; 64]> = (0..ys).map(|o| fold_1b_rows(&cmain[lay.y_off + (o << hs)..][..nh], &eh)).collect();
    let (tau_y, sl_y) = slot_reduce(ps, y_a, y_b, g_y);
    let y = switch_claim(ps, lay.y_off, [sig_s, &tau_y[..]].concat(), sl_y);

    // ---- M (5 slot rounds over the stream block's 32 columns of 2^rec rows at (σ', 0); weights ω on lanes 0–16)
    let ms = 1usize << crate::lvm::params::UT_M_SLOTS_LOG;
    assert_eq!(lay.rec_log, hs + 1, "S's columns: 2^(hs + 1) rows");
    let m_a: Vec<[F; 64]> = (0..ms).map(|o| if o < REC_STREAM_COLS { wl[o] } else { [F::ZERO; 64] }).collect();
    let m_b: Vec<[F; 64]> = (0..ms).map(|o| fold_1b_rows(&cmain[lay.rec_col(o)..][..nh], &eh)).collect();
    let (tau_m, sl_m) = slot_reduce(ps, m_a, m_b, g_m);
    let mc = switch_claim(ps, lay.s_off, [sig_s, &[F::ZERO], &tau_m[..]].concat(), sl_m);
    WireU { d, y, m: mc }
}

/// U-TAPE dev check: the sponge kernels' closed forms against brute force on a small tape (`w = 9`, `hs = 7`), in E2.
pub fn check_sponge_kernels_u() {
    let mut seed = 0x0bad_cafe_1234_5677u64;
    let mut rnd = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let a = seed;
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        F128 { c0: a, c1: seed }
    };
    let (w, hs) = (9usize, 7usize);
    let sig: Vec<F128> = (0..hs).map(|_| rnd()).collect();
    let rho: Vec<F128> = (0..w + 1 - PB).map(|_| rnd()).collect();
    let mu: [F128; PACK] = std::array::from_fn(|_| rnd());
    let mut cont = vec![false; 1 << hs];
    for i in [1usize, 2, 3, 17, 40, 41, 42, 43, 70, 127] {
        cont[i] = true;
    }
    // ι over w + 1 bits, at 2^w + y
    let iota = iota_table(&rho, &mu, 2 << w);
    let es = F128::eq_table(&sig);
    let nh = 1usize << hs;
    let kks: F128 = (0..nh).filter(|&x| x + 1 < nh && cont[x + 1]).map(|x| es[x] * iota[(1 << w) + x + 1]).sum();
    let iks: F128 = (0..nh).map(|x| es[x] * iota[(1 << w) + x]).sum();
    assert!(sponge_kernels_u(&sig, &rho, &mu, w, &cont) == (kks, iks), "sponge kernels (E2)");
    let sw: Vec<F128> = (0..w).map(|_| rnd()).collect();
    let ew = F128::eq_table(&sw);
    for m in [0usize, 1, 17, 300, 511] {
        let brute: F128 = (0..1usize << w).filter(|&x| x + 1 <= m).map(|x| ew[x] * iota[x + 1]).sum();
        assert!(k_ch_mle(&sw, &rho[..w - PB], &mu, m) * (F128::ONE + rho[w - PB]) == brute, "K_ch at m = {m}");
    }
    // the KS13 runs at P20 S2GU: [1, B − 1], [8080, 8110] (COMMON)
    let p = crate::lvm::params::p20();
    let c = crate::lvm::tables::cont_column(p.ks_log, p.rec_rows_log, crate::lvm::prove::sponge_blocks(&p));
    println!("cont runs at P20 (stage {:?}): {:?}", std::env::var("LVM_STAGE").ok(), cont_runs(&c));
}
