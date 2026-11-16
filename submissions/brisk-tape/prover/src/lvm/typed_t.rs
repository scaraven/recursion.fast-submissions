//! E2F (lvm2 S2, stage S2GT; `ref/s2gt.py` + amendments 1–2, E2F-T's `LvmE2TProg`/`LvmE2TWiring`): the typed phases
//! at E2 with the swapped split.
//!
//! The matrices are S2GF's (`o' = m + 4s`, E3 coefficients: `Typed`'s entries), re-tagged by `splitEnt`: an entry with
//! coefficient `c = c₀ + c₁y + c₂y²` becomes, for each nonzero `c_j`, the entry `m + 4j` with the E2 coefficient
//! `c_j·X^s`. At a slot the relation is read in `E3 ⊗_K E2 = E2[y]/(y³ + y + 1)`: `A_j = M_{4j}`, `B_j = M_{1+4j}`,
//! `C_j = M_{2+4j} + M_{3+4j}`, `rel_k = (A ⊗ B)_k + C_k` (`mulY3`), batched as `Σ_k ω^k rel_k`.
//! Transcript (all E2, 16-byte scalars, a nonce before every challenge, the separator before the first): `τ` (20, `g`
//! 1 each), `ω` (`g` 2), 20 equality-mode rounds (`g` 2), the nine values; `γ` (`g` 4), 21 rounds (`g` 2), 12 matrix
//! values, 4 region values; the relayout, 19 rounds (`g` 2), `v_R`; A23: `κ` (4, `g` 1 each), `h` (46), `t` (`g` 6),
//! the zero scalar. Every typed word claim is split re/im in place (`Claim::word`).

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::{Ext, F64, F128, F128Unreduced, F192};
use crate::lvm::acc::Acc;
use crate::lvm::link::Claim;
use crate::lvm::typed::{Ent, OC_MASK, OC_SHIFT, Typed, interp_fixed};
use crate::lvm::typed_phi::PhiK;
use crate::lvm::typed_prove::{SFLAT_LOG, TData, TReg, Tamper, TypedOut, sflat_inv};

/// `Φ_Q`'s variables at S2GT: 4 selector bits, `x` (20), `y` (21).
pub const PHI_VARS_T: usize = 45;

#[inline]
fn e3(x: F128) -> F192 {
    F192::new(x.c0, x.c1, 0)
}

#[inline]
fn e2(x: F192) -> F128 {
    debug_assert_eq!(x.c2, 0);
    F128::new(x.c0, x.c1)
}

/// The split of an S2GF entry (tag `o' = m + 4s`, E3 coefficient `c`): per nonzero E3 coordinate `j` of `c`, the
/// S2GT tag `m + 4j` and the E2 coefficient `c_j·X^s`.
#[inline]
fn split(o: u32, c: F192) -> impl Iterator<Item = (usize, F128)> {
    let (m, s) = ((o & 3) as usize, (o >> 2) as usize);
    let l = c.to_limbs();
    (0..3).filter(move |&j| l[j] != 0).map(move |j| (m + 4 * j, if s == 0 { F128::new(l[j], 0) } else { F128::new(0, l[j]) }))
}

/// The nine-value row of an S2GT tag `m + 4j`: `A_j` = `j`, `B_j` = `3 + j`, `C_j` = `6 + j`.
#[inline]
fn row9(t: usize) -> usize {
    let (m, j) = (t & 3, t >> 2);
    match m {
        0 => j,
        1 => 3 + j,
        _ => 6 + j,
    }
}

/// `(A ⊗ B)_k` in `E2[y]/(y³ + y + 1)` (`LvmE2TWiring.mulY3`): `[c₀ + c₃, c₁ + c₃ + c₄, c₂ + c₄]` of the product's
/// coefficients `c_i`. PFAST-T: by Karatsuba's six products (`P_i = a_i b_i`, `P_ij = (a_i + a_j)(b_i + b_j)`), unreduced,
/// one reduction per output: `[P₀ + P₁ + P₂ + P₁₂, P₀ + P₀₁ + P₁₂, P₀ + P₁ + P₀₂]` (the same field values).
#[inline]
fn mul_y3(a: [F128; 3], b: [F128; 3]) -> [F128; 3] {
    let (p0, p1, p2) = (a[0].mul_unreduced(b[0]), a[1].mul_unreduced(b[1]), a[2].mul_unreduced(b[2]));
    let p01 = (a[0] + a[1]).mul_unreduced(b[0] + b[1]);
    let p02 = (a[0] + a[2]).mul_unreduced(b[0] + b[2]);
    let p12 = (a[1] + a[2]).mul_unreduced(b[1] + b[2]);
    [(p0 ^ p1 ^ p2 ^ p12).reduce(), (p0 ^ p01 ^ p12).reduce(), (p0 ^ p1 ^ p02).reduce()]
}

/// `Σ_k ω^k·((A ⊗ B)_k + C_k)` of nine values (`ω⁰ = 1`: one reduction for the sum).
#[inline]
fn rel(v: &[F128; 9], om: [F128; 3]) -> F128 {
    debug_assert_eq!(om[0], F128::ONE);
    let p = mul_y3([v[0], v[1], v[2]], [v[3], v[4], v[5]]);
    (F128Unreduced::from(p[0] + v[6]) ^ om[1].mul_unreduced(p[1] + v[7]) ^ om[2].mul_unreduced(p[2] + v[8])).reduce()
}

/// The coefficient of an S2GF compact code (`oc`): `1` or the coefficient table's.
#[inline]
fn coef(b1: &Typed, oc: u32) -> F192 {
    if oc >> OC_SHIFT == 0 { F192::ONE } else { b1.coefs[(oc >> OC_SHIFT) as usize] }
}

/// The slots of the live prefix (even, at least 2) whose `A_j, B_j` the zerocheck reads.
fn ab_slots(b1: &Typed) -> usize {
    let n = b1.x_live.max(2).next_multiple_of(2).min(1usize << b1.x_log);
    assert_eq!(b1.row_ptr[n] as usize, b1.ent.len(), "no entry past the live prefix of slots");
    n
}

/// `A_j, B_j` at slot `x` (`C` is the honest prover's `A ⊗ B`).
#[inline]
fn ab6_row(b1: &Typed, z: &[F64], x: usize) -> [F128; 6] {
    let mut acc = [F128::ZERO; 6];
    for e in &b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize] {
        if e.o & 3 >= 2 {
            continue;
        }
        for (t, c) in split(e.o as u32, e.c) {
            acc[row9(t)] += c.mul_base(z[e.y as usize]);
        }
    }
    acc
}

/// The nine values per slot over the live prefix with `C_j = (D_j + W_j)z` from the matrices (the general path: a
/// witness that may fail the relation, e.g. the dev tampers `res`/`e2word`), slot-major.
fn abc9(b1: &Typed, z: &[F64]) -> Vec<[F128; 9]> {
    let n = b1.x_live.max(2).next_multiple_of(2).min(1usize << b1.x_log);
    assert_eq!(b1.row_ptr[n] as usize, b1.ent.len(), "no entry past the live prefix of slots");
    crate::lv::parallel::map_collect(n, |x| {
        let mut acc = [F128::ZERO; 9];
        for e in &b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize] {
            for (t, c) in split(e.o as u32, e.c) {
                acc[row9(t)] += c.mul_base(z[e.y as usize]);
            }
        }
        acc
    })
}

/// A dev self-check failed: fatal unless a dev mode expects it (`LVM_E2F_DEVPUB=1`: an older blob's witness;
/// `LVM_TYPED_TAMPER`: a tampered witness or value, which V_S must reject).
fn dev_check(ok: bool, what: &str) {
    if !ok {
        let devpub = std::env::var("LVM_E2F_DEVPUB").is_ok_and(|v| v == "1");
        assert!(devpub || std::env::var_os("LVM_TYPED_TAMPER").is_some(), "{what}");
        eprintln!("lvm: LVM_E2F_DEVPUB/LVM_TYPED_TAMPER: {what} fails (sent anyway)");
    }
}

/// `Σ_{j<n} f(j)` of two E2 sums, unreduced, on the pool.
fn sum2(n: usize, f: impl Fn(usize, &mut [F128Unreduced; 2]) + Sync) -> [F128; 2] {
    const CH: usize = 1 << 11;
    let parts: Vec<[F128Unreduced; 2]> = crate::lv::parallel::map_collect(n.div_ceil(CH), |ci| {
        let mut acc = [F128Unreduced::ZERO; 2];
        for j in ci * CH..((ci + 1) * CH).min(n) {
            f(j, &mut acc);
        }
        acc
    });
    let acc = parts.iter().fold([F128Unreduced::ZERO; 2], |a, b| [a[0] ^ b[0], a[1] ^ b[1]]);
    acc.map(|a| a.reduce())
}

/// (dev, `lvm-prover e2tzc N LIVE`) The fast zerocheck against the general one on a random honest table over `n`
/// variables (`C = A ⊗ B` on the first `live` slots, zero after): the two transcripts' bytes, `r_x` and the nine values
/// must be equal. Returns the number of proof bytes compared.
pub fn zc_selftest(n: usize, live: usize, seed: u64) -> usize {
    let mut rng = crate::lvm::typed::Rng::new(seed);
    let mut e = || {
        let x = rng.e();
        F128::new(x.c0, x.c1)
    };
    let ab: Vec<[F128; 6]> = (0..live).map(|_| std::array::from_fn(|_| e())).collect();
    let t9: Vec<[F128; 9]> = ab
        .iter()
        .map(|v| {
            let c = mul_y3([v[0], v[1], v[2]], [v[3], v[4], v[5]]);
            [v[0], v[1], v[2], v[3], v[4], v[5], c[0], c[1], c[2]]
        })
        .collect();
    let hdr = vec![0u8; 8 + 1000]; // (a seed length no other query has)
    let (mut p1, mut p2) = (ProverState::seeded(&hdr), ProverState::seeded(&hdr));
    // τ and ω as `prove_t` takes them (the separator first)
    let tau: Vec<F128> = p1.challenges::<F128, 2>(Grp::C1, n);
    let om = p1.challenge::<F128, 2>(Grp::C2);
    assert!(p2.challenges::<F128, 2>(Grp::C1, n) == tau && p2.challenge::<F128, 2>(Grp::C2) == om);
    let (r1, v1) = zerocheck_t(&mut p1, ab.len(), |x| ab[x], &tau, om);
    let (r2, v2) = zerocheck_t_plain(&mut p2, t9, &tau, om);
    assert!(r1 == r2 && v1 == v2 && p1.body == p2.body && p1.trace == p2.trace, "the S2GT zerochecks: fast = general");
    p1.body.len()
}

/// (dev, `LVM_TYPED_SUBLAPS=1`) A sub-phase lap: wall, process CPU and E2 nonce-search wall since the last lap.
fn tsub(name: &str, grind_s: f64) {
    thread_local! {
        static ON: bool = std::env::var_os("LVM_TYPED_SUBLAPS").is_some();
        static LAST: std::cell::Cell<Option<(std::time::Instant, f64, f64)>> = const { std::cell::Cell::new(None) };
    }
    if !ON.with(|o| *o) {
        return;
    }
    let (now, c) = (std::time::Instant::now(), crate::lv::tracing::cpu_now().0);
    if let Some((t, c0, g0)) = LAST.with(|l| l.get()) {
        eprintln!("lvm: T-sub {name:<14} wall {:.4} cpu {:.4} grind {:.4}", (now - t).as_secs_f64(), c - c0, grind_s - g0);
    }
    LAST.with(|l| l.set(Some((now, c, grind_s))));
}

/// `Σ_k ω^k·(A ⊗ B)_k` (the relation without `C`: its degree-2 part).
#[inline]
fn rel_ab(a: [F128; 3], b: [F128; 3], om: [F128; 3]) -> F128 {
    debug_assert_eq!(om[0], F128::ONE);
    let p = mul_y3(a, b);
    (F128Unreduced::from(p[0]) ^ om[1].mul_unreduced(p[1]) ^ om[2].mul_unreduced(p[2])).reduce()
}

/// `eq(r, q)` at boolean `q` by two tables (`eq(r^{<L}, q mod 2^L)·eq(r^{≥L}, q ≫ L)`, as [`eqp`]): the fold
/// `e[2j] + e[2j + 1]` of `eq(r₀ ‖ r, ·)` is `eq(r, j)` exactly, so a round's weights need no folded vector.
struct EqW {
    lo: Vec<F128>,
    hi: Vec<F128>,
    l: usize,
}

impl EqW {
    fn new(r: &[F128]) -> EqW {
        const L: usize = 10;
        if r.len() <= L + 2 {
            EqW { lo: F128::eq_table(r), hi: Vec::new(), l: r.len() }
        } else {
            EqW { lo: F128::eq_table(&r[..L]), hi: F128::eq_table(&r[L..]), l: L }
        }
    }

    #[inline]
    fn at(&self, q: usize) -> F128 {
        if self.hi.is_empty() { self.lo[q] } else { self.hi[q >> self.l] * self.lo[q & ((1 << self.l) - 1)] }
    }
}

/// The zerocheck at E2 (honest: `C = A ⊗ B` on the cube, so round 0 sums `q(∞)` only and `C` is folded from the
/// products in round 0's fold). Every round reads only the live prefix (the rows are zero past it). Returns `r_x` and
/// the nine values at it. PFAST-T: each round's fold is fused with the next round's sums (one pass a round, the
/// folded table written once at its padded length), and the next round's weights `eq(τ^{≥i+2}, ·)` come from
/// [`EqW`] (no serial fold of the weight vector).
/// (PFAST-T: the rows `A_j, B_j` of the `nslots` live slots come from `row`, built in round 0's pass.)
fn zerocheck_t(ps: &mut ProverState, nslots: usize, row: impl Fn(usize) -> [F128; 6] + Sync, tau: &[F128], om: F128) -> (Vec<F128>, [F128; 9]) {
    let n = tau.len();
    let full = 1usize << n;
    let oms = [F128::ONE, om, om * om];
    let mut len = nslots;
    assert!(n >= 1 && len % 2 == 0 && len <= full, "a zerocheck over at least one variable");
    let a3 = |v: &[F128], o: usize| [v[o], v[o + 1], v[o + 2]];
    let e = EqW::new(&tau[1..]);
    tsub("zc eqp", ps.e2_grind_s);
    // round 0: q(0) = q(1) = 0; the rows are built and stored in the same pass
    let er = &e;
    let mut ab: Vec<[F128; 6]> = Vec::with_capacity(len);
    let pa = crate::lv::parallel::SendPtr(ab.as_mut_ptr());
    let [_, qi0] = sum2(len / 2, |j, acc| {
        let (x, y) = (row(2 * j), row(2 * j + 1));
        // SAFETY: slots 2j and 2j + 1 belong to pair j's task only, written once; 2j + 1 < len.
        unsafe {
            pa.add(2 * j).write(x);
            pa.add(2 * j + 1).write(y);
        }
        let d: [F128; 6] = std::array::from_fn(|k| x[k] + y[k]);
        acc[1] ^= er.at(j).mul_unreduced(rel_ab(a3(&d, 0), a3(&d, 3), oms));
    });
    // SAFETY: the pairs j < len / 2 wrote every slot of 0..len (len even).
    unsafe { ab.set_len(len) };
    let mut sums = [F128::ZERO, qi0];
    tsub("zc r0sum", ps.e2_grind_s);
    let (mut p, mut claim) = (F128::ONE, F128::ZERO);
    let mut r = Vec::with_capacity(n);
    let mut t: Vec<[F128; 9]> = Vec::new();
    for i in 0..n {
        let [q0, qi] = sums;
        let t1 = F128::ONE + tau[i];
        let q1 = (claim + p * t1 * q0) * (p * tau[i]).inv();
        let l = q0 + q1 + qi;
        let g = [p * t1 * q0, p * (t1 * l + q0), p * (t1 * qi + l), p * qi];
        ps.add_round_poly_ext::<F128, 2>(&[q0, l, qi], true);
        let ri = ps.challenge::<F128, 2>(Grp::C2);
        r.push(ri);
        claim = F128::poly_eval(&g, ri);
        p *= F128::ONE + tau[i] + ri;
        tsub("zc chal", ps.e2_grind_s);
        let half = len / 2;
        let f = |u: F128, v: F128| u + ri * (u + v);
        // the folded slot j < half: from `A, B` (and `C = A ⊗ B`) in round 0, from the nine values after
        let (abr, tr) = (&ab, &t);
        let fold = |j: usize| -> [F128; 9] {
            if i == 0 {
                let (x, y) = (&abr[2 * j], &abr[2 * j + 1]);
                let (cx, cy) = (mul_y3(a3(x, 0), a3(x, 3)), mul_y3(a3(y, 0), a3(y, 3)));
                std::array::from_fn(|k| if k < 6 { f(x[k], y[k]) } else { f(cx[k - 6], cy[k - 6]) })
            } else {
                let (x, y) = (&tr[2 * j], &tr[2 * j + 1]);
                std::array::from_fn(|k| f(x[k], y[k]))
            }
        };
        if i + 1 == n {
            let vals = fold(0);
            assert!(claim == p * rel(&vals, oms), "the S2GT zerocheck's final claim");
            return (r, vals);
        }
        // the next round over the live prefix (odd length: a zero partner), its sums with the fold
        let len2 = (half + (half & 1)).max(2);
        let w = EqW::new(&tau[i + 2..]);
        let mut nt: Vec<[F128; 9]> = Vec::with_capacity(len2);
        let pt = crate::lv::parallel::SendPtr(nt.as_mut_ptr());
        let wr = &w;
        sums = sum2(len2 / 2, |q, acc| {
            let mut v = [[F128::ZERO; 9]; 2];
            for (k, vk) in v.iter_mut().enumerate() {
                let j = 2 * q + k;
                if j < half {
                    *vk = fold(j);
                }
                // SAFETY: slot j < len2 belongs to pair q's task only, written once.
                unsafe { pt.add(j).write(*vk) };
            }
            let (lo, hi) = (&v[0], &v[1]);
            let wq = wr.at(q);
            let d: [F128; 6] = std::array::from_fn(|k| lo[k] + hi[k]);
            acc[0] ^= wq.mul_unreduced(rel(lo, oms));
            acc[1] ^= wq.mul_unreduced(rel_ab(a3(&d, 0), a3(&d, 3), oms));
        });
        // SAFETY: the pairs q < len2 / 2 wrote every slot of 0..len2.
        unsafe { nt.set_len(len2) };
        t = nt;
        len = len2;
        tsub("zc foldsum", ps.e2_grind_s);
    }
    unreachable!("the last round returns")
}

/// The general zerocheck at E2: the plain rounds on the nine values with `C = (D + W)z` (every round sums `q(0)` and
/// `q(∞)`; the rounds assume the claim 0, so a witness that fails the relation fails V's final check). The same
/// messages as [`zerocheck_t`] on an honest witness.
fn zerocheck_t_plain(ps: &mut ProverState, mut t: Vec<[F128; 9]>, tau: &[F128], om: F128) -> (Vec<F128>, [F128; 9]) {
    let n = tau.len();
    let oms = [F128::ONE, om, om * om];
    assert!(n >= 1 && t.len() <= 1usize << n, "a zerocheck over at least one variable");
    t.resize(1usize << n, [F128::ZERO; 9]);
    let a3 = |v: &[F128; 9], o: usize| [v[o], v[o + 1], v[o + 2]];
    let mut e = eqp(&tau[1..]);
    let (mut p, mut claim) = (F128::ONE, F128::ZERO);
    let mut r = Vec::with_capacity(n);
    for i in 0..n {
        let (tr, er) = (&t, &e);
        let [q0, qi] = sum2(t.len() / 2, |j, acc| {
            let (lo, hi) = (&tr[2 * j], &tr[2 * j + 1]);
            let d: [F128; 9] = std::array::from_fn(|k| lo[k] + hi[k]);
            acc[0] ^= er[j].mul_unreduced(rel(lo, oms));
            acc[1] ^= er[j].mul_unreduced(rel_ab(a3(&d, 0), a3(&d, 3), oms));
        });
        let t1 = F128::ONE + tau[i];
        let q1 = (claim + p * t1 * q0) * (p * tau[i]).inv();
        let l = q0 + q1 + qi;
        let g = [p * t1 * q0, p * (t1 * l + q0), p * (t1 * qi + l), p * qi];
        ps.add_round_poly_ext::<F128, 2>(&[q0, l, qi], true);
        let ri = ps.challenge::<F128, 2>(Grp::C2);
        r.push(ri);
        claim = F128::poly_eval(&g, ri);
        p *= F128::ONE + tau[i] + ri;
        let tr = &t;
        t = crate::lv::parallel::map_collect(tr.len() / 2, |j| std::array::from_fn(|k| tr[2 * j][k] + ri * (tr[2 * j][k] + tr[2 * j + 1][k])));
        if i + 1 < n {
            e = (0..e.len() / 2).map(|j| e[2 * j] + e[2 * j + 1]).collect();
        }
    }
    let vals = t[0];
    dev_check(claim == p * rel(&vals, oms), "the S2GT general zerocheck's final claim");
    (r, vals)
}

/// `eq(r, ·)` at E2 on the pool (the same values as `F128::eq_table`): `out[h·2^L + l] = eq(r^{≥L}, h)·eq(r^{<L}, l)`.
fn eqp(r: &[F128]) -> Vec<F128> {
    const L: usize = 10;
    if r.len() <= L + 2 {
        return F128::eq_table(r);
    }
    let (lo, hi) = (F128::eq_table(&r[..L]), F128::eq_table(&r[L..]));
    // (written once by the pool: no serial zero fill of the table first)
    let mut out: Vec<F128> = Vec::with_capacity(1usize << r.len());
    let po = crate::lv::parallel::SendPtr(out.as_mut_ptr());
    crate::lv::parallel::for_each(hi.len(), |h| {
        for (k, &l) in lo.iter().enumerate() {
            // SAFETY: row h's slots h·2^L + k belong to task h only, written once.
            unsafe { po.add((h << L) + k).write(hi[h] * l) };
        }
    });
    // SAFETY: the rows h < 2^(|r| − L) wrote every slot.
    unsafe { out.set_len(1usize << r.len()) };
    out
}

/// `z̃[..2^|r|](r)` at an E2 point on the pool (`K` words times E2 weights, unreduced per row of `2^10`).
fn mle_t(z: &[F64], r: &[F128]) -> F128 {
    let lo_n = r.len().min(10);
    let (lo, hi) = (F128::eq_table(&r[..lo_n]), F128::eq_table(&r[lo_n..]));
    let parts: Vec<F128> = crate::lv::parallel::map_collect(hi.len(), |h| {
        let mut a = F128Unreduced::ZERO;
        for (w, &x) in lo.iter().zip(&z[h << lo_n..(h + 1) << lo_n]) {
            a ^= w.mul_base_unreduced(x);
        }
        hi[h] * a.reduce()
    });
    parts.into_iter().sum()
}

/// The wiring's weight per compact code: `Σ_{(tag, c) ∈ split(code)} γ^{row9(tag)}·c`.
fn code_weights(b1: &Typed, gp: &[F128]) -> Vec<F128> {
    crate::lv::parallel::map_collect(b1.coefs.len() << OC_SHIFT, |oc| {
        let oc = oc as u32;
        split(oc & OC_MASK, coef(b1, oc)).map(|(t, c)| gp[row9(t)] * c).sum()
    })
}

/// Per compact code (`o | coefficient index << OC_SHIFT`): the code's split parts `(tag, E2 coefficient)`.
fn code_parts(b1: &Typed) -> Vec<Vec<(usize, F128)>> {
    (0..(b1.coefs.len() << OC_SHIFT) as u32).map(|oc| split(oc & OC_MASK, coef(b1, oc)).collect()).collect()
}

/// `u(y) = Σ_x eq(r_x, x)·Σ_{tag} γ^{row9(tag)}·M_tag(x, y)` (A_j at `γ^j`, B_j at `γ^{3+j}`, C_j at `γ^{6+j}`): one
/// E2 weight per compact code.
fn wiring_u_t(b1: &Typed, rx: &[F128], gamma: F128) -> Vec<F128> {
    // (PFAST-T: `eq(r_x, x)` from two small tables per entry, no 2^20 table to build and gather from)
    let ex = EqW::new(rx);
    let wt = code_weights(b1, &F128::powers(gamma, 9));
    let ny = 1usize << b1.y_log;
    let live = b1.y_live.min(ny);
    // (the whole cube in one pass, zero past the live prefix: no serial resize of the vector)
    crate::lv::parallel::map_collect(ny, |y| {
        if y >= live {
            return F128::ZERO;
        }
        let mut acc = F128Unreduced::ZERO;
        for &(x, oc) in &b1.cc[b1.col_ptr[y] as usize..b1.col_ptr[y + 1] as usize] {
            acc ^= ex.at(x as usize).mul_unreduced(wt[oc as usize]);
        }
        acc.reduce()
    })
}

/// The plain degree-2 sumcheck of `Σ_y u(y)·z(y)` at E2 from `claim` (`g` 2 a round; round 0 by `K` products on `z`).
/// Returns the point and the final `u`, `z`. `z` covers `u`'s cube (both callers pass full-length words). `live`: `u`
/// and `z` are zero from word `live` on, so every round reads only the live prefix (the folds of zeros are zero).
/// Each round's fold is fused with the next round's sums (one pass a round).
fn sumcheck_uz(ps: &mut ProverState, u: Vec<F128>, z: &[F64], mut claim: F128, live: usize) -> (Vec<F128>, F128, F128) {
    let n = u.len().trailing_zeros() as usize;
    assert!(n >= 1 && z.len() >= u.len() && live <= u.len());
    let z = &z[..u.len()];
    #[cfg(feature = "selfcheck")]
    {
        assert!(u[live..].iter().all(|x| *x == F128::ZERO) && z[live..].iter().all(|x| *x == F64::ZERO), "zero past the live prefix");
    }
    // the live prefix at a round: even, at least 2
    let mut len = live.max(2).next_multiple_of(2).min(u.len());
    let uu = &u;
    let mut sums = sum2(len / 2, |j, acc| {
        let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], z[2 * j], z[2 * j + 1]);
        acc[0] ^= u0.mul_base_unreduced(z0);
        acc[1] ^= (u0 + u1).mul_base_unreduced(F64(z0.0 ^ z1.0));
    });
    tsub("uz r0sum", ps.e2_grind_s);
    let mut cur: Option<(Vec<F128>, Vec<F128>)> = None;
    let mut r = Vec::with_capacity(n);
    for i in 0..n {
        // plain round: g(0) + g(1) = claim, so g₁ = claim + g₂ (characteristic 2)
        let [g0, g2] = sums;
        let g = [g0, claim + g2, g2];
        ps.add_round_poly_ext::<F128, 2>(&g, false);
        let ri = ps.challenge::<F128, 2>(Grp::C2);
        r.push(ri);
        claim = F128::poly_eval(&g, ri);
        tsub("uz chal", ps.e2_grind_s);
        let half = len / 2;
        let len2 = if i + 1 < n { half.max(2).next_multiple_of(2) } else { half };
        // (no serial zero fill: the pairs write every slot below len2, zero from half on)
        let (mut nu, mut nz): (Vec<F128>, Vec<F128>) = (Vec::with_capacity(len2), Vec::with_capacity(len2));
        let (pu, pz) = (crate::lv::parallel::SendPtr(nu.as_mut_ptr()), crate::lv::parallel::SendPtr(nz.as_mut_ptr()));
        let cr = &cur;
        let fold = |j: usize| -> (F128, F128) {
            match cr {
                None => {
                    let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], z[2 * j], z[2 * j + 1]);
                    (u0 + ri * (u0 + u1), ri.mul_base(F64(z0.0 ^ z1.0)) + F128::new(z0.0, 0))
                }
                Some((cu, cz)) => {
                    let (u0, u1, z0, z1) = (cu[2 * j], cu[2 * j + 1], cz[2 * j], cz[2 * j + 1]);
                    (u0 + ri * (u0 + u1), z0 + ri * (z0 + z1))
                }
            }
        };
        sums = sum2(len2.div_ceil(2), |q, acc| {
            let mut v = [(F128::ZERO, F128::ZERO); 2];
            for (k, vk) in v.iter_mut().enumerate() {
                let j = 2 * q + k;
                if j < half {
                    *vk = fold(j);
                }
                if j < len2 {
                    // SAFETY: slot j belongs to pair q's task only, written once; j < len2.
                    unsafe {
                        pu.add(j).write(vk.0);
                        pz.add(j).write(vk.1);
                    }
                }
            }
            acc[0] ^= v[0].0.mul_unreduced(v[0].1);
            acc[1] ^= (v[0].0 + v[1].0).mul_unreduced(v[0].1 + v[1].1);
        });
        // SAFETY: the pairs q < ⌈len2 / 2⌉ wrote every slot of 0..len2.
        unsafe {
            nu.set_len(len2);
            nz.set_len(len2);
        }
        tsub("uz foldsum", ps.e2_grind_s);
        cur = Some((nu, nz));
        len = len2;
    }
    let (cu, cz) = cur.expect("at least one round");
    // (dev: `LVM_E2F_DEVPUB=1` runs an older blob whose relation fails at the header's cells; a tamper)
    dev_check(claim == cu[0] * cz[0], "an S2GT plain sumcheck's final claim");
    (r, cu[0], cz[0])
}

/// `M̃_tag(r_x, r_y)` for the twelve S2GT tags (`m + 4j`).
fn mat_vals12(b1: &Typed, cp: &[Vec<(usize, F128)>], rx: &[F128], ry: &[F128]) -> [F128; 12] {
    let (ex, ey) = (eqp(rx), eqp(ry));
    let ny = (1usize << b1.y_log).min(b1.y_live);
    let parts: Vec<[F128Unreduced; 12]> = crate::lv::parallel::map_collect(ny.div_ceil(1 << 10), |ci| {
        let mut acc = [F128Unreduced::ZERO; 12];
        for y in ci << 10..((ci + 1) << 10).min(ny) {
            for &(x, oc) in &b1.cc[b1.col_ptr[y] as usize..b1.col_ptr[y + 1] as usize] {
                let w = ex[x as usize] * ey[y];
                for &(t, c) in &cp[oc as usize] {
                    acc[t] ^= if c == F128::ONE { F128Unreduced::from(w) } else { w.mul_unreduced(c) };
                }
            }
        }
        acc
    });
    std::array::from_fn(|t| parts.iter().fold(F128Unreduced::ZERO, |a, p| a ^ p[t]).reduce())
}

/// The twelve `M̃_tag(r_x, r_y)` by the class kernels (`b1.phik_t` at the point `0⁴ ‖ r_x ‖ r_y`, the selector bits
/// zero), else (or when some `r_y,k = 1`) the plain evaluator. `LVM_TYPED_MATSCHK=1` (dev): both, equal.
fn mats_t(b1: &Typed, rx: &[F128], ry: &[F128]) -> [F128; 12] {
    let plain = || mat_vals12(b1, &code_parts(b1), rx, ry);
    let Some(pk) = b1.phik_t.as_ref().filter(|_| ry.iter().all(|&v| v != F128::ONE)) else { return plain() };
    let pt: Vec<F128> = [&[F128::ZERO; 4][..], rx, ry].concat();
    let m = pk.mats(std::slice::from_ref(&pt));
    let v: [F128; 12] = std::array::from_fn(|t| m[t]);
    if std::env::var("LVM_TYPED_MATSCHK").is_ok_and(|x| x == "1") {
        assert_eq!(v, plain(), "the S2GT matrix values: kernels = plain");
        eprintln!("lvm: LVM_TYPED_MATSCHK: the 12 matrix values by the kernels = the plain evaluator's");
    }
    v
}

/// `eq(r, x)` at a boolean point.
fn eq_at(r: &[F128], x: usize) -> F128 {
    crate::lvm::front::eq_at_index(r, x)
}

/// `Σ_{(base, log)} eq(r^{≥log}, base ≫ log)·z̃[base..](r^{<log})`.
fn reg_value(z: &[F64], r: &[F128], regs: &[(usize, usize)]) -> F128 {
    regs.iter()
        .map(|&(base, log)| eq_at(&r[log..], base >> log) * mle_t(&z[base..base + (1 << log)], &r[..log]))
        .sum()
}

/// A region claim at E2, split re/im (`regClaimT`).
fn reg_claim(regs: &[TReg], ry: &[F128], value: F128) -> Vec<Claim> {
    Claim::word(regs.iter().map(|g| (g.off, ry[..g.log].to_vec(), eq_at(&ry[g.log..], g.base >> g.log))).collect(), value)
}

/// `eq(κ, tag)` over the 4 selector bits (16 entries; tags 12–15 unused).
fn eq_sel(k: &[F128]) -> Vec<F128> {
    F128::eq_table(k)
}

/// S2GT's split matrices as a `Typed` for [`PhiK`] at E2: per slot, every S2GF entry's split entries in order (tag
/// `m + 4j`, the E2 coefficient `c_j·X^s` stored as `(c₀, c₁, 0)`, coefficient table `[1]`). Only the fields `PhiK::new`
/// reads are filled (no CSC, no compact form).
fn split_typed(b1: &Typed) -> Typed {
    let nx = 1usize << b1.x_log;
    let mut row_ptr = Vec::with_capacity(nx + 1);
    row_ptr.push(0u32);
    let mut ent = Vec::with_capacity(b1.ent.len());
    for x in 0..nx {
        for e in &b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize] {
            ent.extend(split(e.o as u32, e.c).map(|(t, c)| Ent { y: e.y, o: t as u8, c: e3(c) }));
        }
        row_ptr.push(ent.len() as u32);
    }
    Typed {
        x_log: b1.x_log,
        y_log: b1.y_log,
        ell: b1.ell.clone(),
        row_ptr,
        ent,
        col_ptr: Vec::new(),
        cent: Vec::new(),
        coefs: vec![F192::ONE],
        cc: Vec::new(),
        ab_ptr: Vec::new(),
        ab: Vec::new(),
        x_live: b1.x_live,
        y_live: b1.y_live,
        ky: Vec::new(),
        ey: Vec::new(),
        one_y: b1.one_y,
        committed: 0,
        dense: 0,
        virt: 0,
        slot_tag: b1.slot_tag.clone(),
        tags: b1.tags.clone(),
        rowb: Vec::new(),
        report: String::new(),
        phik: None,
        phik_t: None,
    }
}

/// The class-kernel evaluator of S2GT's `Φ_Q` at E2 points (4 selector bits): `PhiK` over [`split_typed`].
pub fn phik_t(b1: &Typed) -> PhiK<F128> {
    PhiK::new_sel(&split_typed(b1), 4)
}

/// `Φ_Q` at S2GT at E2 points `κ ‖ x ‖ y` (45 coordinates): `Σ_tag eq(κ, tag)·M̃_tag(x, y)`, by `b1.phik_t` when built.
/// (The kernels' tables need `1 + r_y,k ≠ 0`; a point with some `r_y,k = 1` takes the plain evaluator.)
pub fn phi_t(b1: &Typed, pts: &[Vec<F128>]) -> Vec<F128> {
    let kernel_ok = pts.iter().all(|p| p[4 + b1.x_log..].iter().all(|&v| v != F128::ONE));
    match &b1.phik_t {
        Some(pk) if kernel_ok => pk.eval(pts),
        _ => phi_t_plain(b1, pts),
    }
}

/// [`phi_t`] by the plain sparse evaluator (the reference `lvm-prover phit` checks the kernels against).
pub fn phi_t_plain(b1: &Typed, pts: &[Vec<F128>]) -> Vec<F128> {
    let cp = code_parts(b1);
    pts.iter()
        .map(|pt| {
            let (k, rest) = pt.split_at(4);
            let (px, py) = rest.split_at(b1.x_log);
            let m = mat_vals12(b1, &cp, px, py);
            let es = eq_sel(k);
            (0..12).map(|t| es[t] * m[t]).sum()
        })
        .collect()
}

/// `Φ_Q(0)` at S2GT (step 1's `acc_in.y`).
pub fn phi0_t(b1: &Typed) -> F192 {
    e3(phi_t(b1, &[vec![F128::ZERO; 4 + b1.x_log + b1.y_log]])[0])
}

/// **The typed phases at S2GT** (`typedProgT` without the mini-bus): returns the outgoing accumulator (E2 values
/// embedded `(c0, c1, 0)`) and the typed claims split re/im (relayout, `σ′`, committed regions, `KS` aliases).
/// `general`: a witness that may fail the relation (the dev tampers): the plain zerocheck on `C = (D + W)z`.
#[allow(clippy::too_many_arguments)]
pub fn prove_t(ps: &mut ProverState, b1: &Typed, z: &[F64], td: &TData, sblk: &[F64], s_off: usize, acc_in: &Acc, general: bool) -> TypedOut {
    let mut stages = Vec::new();
    let mut t0 = std::time::Instant::now();
    let mut lap = |n: &'static str, st: &mut Vec<(&'static str, f64)>| {
        st.push((n, t0.elapsed().as_secs_f64()));
        t0 = std::time::Instant::now();
    };
    // 1. zerocheck: τ (20, each its own nonce), ω, the rounds, the nine values
    tsub("start", ps.e2_grind_s);
    let tau: Vec<F128> = ps.challenges::<F128, 2>(Grp::C1, b1.x_log);
    let om = ps.challenge::<F128, 2>(Grp::C2);
    tsub("zc tau", ps.e2_grind_s);
    // (`LVM_TYPED_PLAINZC=1`, dev: the general zerocheck on an honest witness, byte-identical to the fast one)
    let general = general || std::env::var("LVM_TYPED_PLAINZC").is_ok_and(|v| v == "1");
    let (rx, vals) = if general {
        zerocheck_t_plain(ps, abc9(b1, z), &tau, om)
    } else {
        zerocheck_t(ps, ab_slots(b1), |x| ab6_row(b1, z, x), &tau, om)
    };
    ps.add_ext(&vals);
    lap("zerocheck", &mut stages);
    // 2. wiring: γ (g 4), Σ_k γ^k v_k, 21 rounds, 12 matrix values, 4 region values
    tsub("zc end", ps.e2_grind_s);
    let gamma = ps.challenge::<F128, 2>(Grp::Bits(4));
    tsub("w gamma", ps.e2_grind_s);
    let claim0: F128 = vals.iter().enumerate().map(|(k, &v)| (0..k).fold(F128::ONE, |a, _| a * gamma) * v).sum();
    // (`LVM_TYPED_SUBLAPS=1`, dev: the wiring's parts' wall times)
    let sub = std::env::var_os("LVM_TYPED_SUBLAPS").is_some();
    let mut ts = std::time::Instant::now();
    let mut sl = |n: &str| {
        if sub {
            eprintln!("lvm: S2GT wiring {n} {:.4} s", ts.elapsed().as_secs_f64());
        }
        ts = std::time::Instant::now();
    };
    let u = wiring_u_t(b1, &rx, gamma);
    sl("u");
    tsub("w u", ps.e2_grind_s);
    let (ry, _, _) = sumcheck_uz(ps, u, z, claim0, b1.y_live.min(1usize << b1.y_log));
    sl("rounds");
    // PFAST-T: A23's line points `a + t·(a + κ ‖ r_x ‖ r_y)` (t = 2..45) need `κ` only in their selector weights:
    // their twelve matrix values take one kernel batch here with the wiring's point `0⁴ ‖ r_x ‖ r_y` (first), and A23
    // weighs them by `eq(κ-part, ·)` (the same field values as `phi_t` and `mats_t`; either path where the kernels
    // cannot take some point).
    let a: Vec<F128> = acc_in.pt.iter().map(|&x| e2(x)).collect();
    assert_eq!(a.len(), PHI_VARS_T, "acc_in has 45 coordinates at S2GT");
    let xy: Vec<F128> = [&rx[..], &ry].concat();
    let np = PHI_VARS_T;
    let pre: Option<Vec<F128>> = b1.phik_t.as_ref().and_then(|pk| {
        let mut pts: Vec<Vec<F128>> = Vec::with_capacity(np);
        pts.push([&[F128::ZERO; 4][..], &xy].concat());
        for j in 2..=PHI_VARS_T as u64 {
            let t = F128::new(j, 0);
            pts.push((0..PHI_VARS_T).map(|c| if c < 4 { F128::ZERO } else { a[c] + t * (a[c] + xy[c - 4]) }).collect());
        }
        let ok = pts.iter().all(|p| p[4 + b1.x_log..].iter().all(|&v| v != F128::ONE));
        ok.then(|| pk.mats(&pts))
    });
    let v: [F128; 12] = match &pre {
        Some(m) => {
            let v: [F128; 12] = std::array::from_fn(|t| m[t * np]);
            if std::env::var("LVM_TYPED_MATSCHK").is_ok_and(|x| x == "1") {
                assert_eq!(v, mat_vals12(b1, &code_parts(b1), &rx, &ry), "the S2GT matrix values: kernels = plain");
                eprintln!("lvm: LVM_TYPED_MATSCHK: the 12 matrix values by the kernels = the plain evaluator's");
            }
            v
        }
        None => mats_t(b1, &rx, &ry),
    };
    sl("mats");
    tsub("w mats", ps.e2_grind_s);
    let rr = |g: &[TReg]| g.iter().map(|g| (g.base, g.log)).collect::<Vec<_>>();
    let v_com = reg_value(z, &ry, &rr(&td.com));
    let mut v_s = reg_value(z, &ry, &[(td.sflat, SFLAT_LOG)]);
    let v_sig = reg_value(z, &ry, &rr(&td.sig));
    let v_ks = reg_value(z, &ry, &rr(&td.ks));
    sl("regions");
    tsub("w regions", ps.e2_grind_s);
    let tm = crate::lvm::typed_prove::tamper();
    if tm == Tamper::Vs {
        v_s += F128::ONE;
        eprintln!("lvm: LVM_TYPED_TAMPER=vs: v_S moved");
    }
    ps.add_ext(&v);
    ps.add_ext(&[v_com, v_s, v_sig, v_ks]);
    lap("wiring", &mut stages);
    // 3. relayout: K(sflatWord p) = eq(r_y, S_flat + p) on S's 2^19 words
    let nr = sblk.len().trailing_zeros() as usize;
    assert_eq!(nr, SFLAT_LOG);
    let w_hi = eq_at(&ry[SFLAT_LOG..], td.sflat >> SFLAT_LOG);
    // (PFAST-T: `w_hi·eq(r_y^{<19}, ·)` from two small tables, `w_hi` folded into the high one: no 2^19 table)
    let mut e = EqW::new(&ry[..SFLAT_LOG]);
    if e.hi.is_empty() {
        e.lo.iter_mut().for_each(|v| *v = w_hi * *v);
    } else {
        e.hi.iter_mut().for_each(|v| *v = w_hi * *v);
    }
    let k: Vec<F128> = crate::lv::parallel::map_collect(1usize << nr, |c| e.at(sflat_inv(c)));
    tsub("rl k", ps.e2_grind_s);
    let (rl, _, v_r) = sumcheck_uz(ps, k, sblk, v_s, 1 << nr);
    ps.add_ext(&[v_r]);
    lap("relayout", &mut stages);
    // 4. A23 at Φ_Q (45 variables): κ (4), h (46), t (g 6), the zero scalar
    tsub("rl end", ps.e2_grind_s);
    let kappa: Vec<F128> = ps.challenges::<F128, 2>(Grp::C1, 4);
    tsub("acc kappa", ps.e2_grind_s);
    let es = eq_sel(&kappa);
    let y_own: F128 = (0..12).map(|t| es[t] * v[t]).sum();
    let b: Vec<F128> = [&kappa[..], &rx, &ry].concat();
    let line = |t: F128| -> Vec<F128> { a.iter().zip(&b).map(|(&x, &y)| x + t * (x + y)).collect() };
    let mut ys = vec![e2(acc_in.y), y_own];
    match &pre {
        // `Φ_Q(line(t)) = Σ_o eq(line(t)^{<4}, o)·M̃_o(line(t)^{≥4})` (`PhiK::eval`), the matrix values from the batch
        Some(m) => ys.extend((2..=PHI_VARS_T as u64).enumerate().map(|(q, j)| {
            let t = F128::new(j, 0);
            let eo = F128::eq_table(&(0..4).map(|c| a[c] + t * (a[c] + kappa[c])).collect::<Vec<_>>());
            (0..m.len() / np).map(|o| eo[o] * m[o * np + q + 1]).sum::<F128>()
        })),
        None => {
            let pts: Vec<Vec<F128>> = (2..=PHI_VARS_T as u64).map(|j| line(F128::new(j, 0))).collect();
            ys.extend(phi_t(b1, &pts));
        }
    }
    tsub("acc phi", ps.e2_grind_s);
    // interpolation at the K points 0..45 is K-linear on the values: E2 values embedded in E3 interpolate exactly
    let mut h: Vec<F128> = interp_fixed(&ys.iter().map(|&x| e3(x)).collect::<Vec<_>>()).into_iter().map(e2).collect();
    // (dev tampers: `h1` moves one coefficient, so `h(1)` fails; `h2` two, the sum kept: only `Φ_Q` catches it)
    match tm {
        Tamper::H1 => h[7] += F128::ONE,
        Tamper::H2 => {
            h[7] += F128::ONE;
            h[9] += F128::ONE;
        }
        _ => {}
    }
    if matches!(tm, Tamper::H1 | Tamper::H2) {
        eprintln!("lvm: LVM_TYPED_TAMPER={tm:?}: h moved");
    }
    ps.add_ext(&h);
    let tt = ps.challenge::<F128, 2>(Grp::Bits(6));
    ps.add_ext(&[F128::ZERO]);
    let acc_out = Acc { pt: line(tt).into_iter().map(e3).collect(), y: e3(F128::poly_eval(&h, tt)) };
    tsub("acc end", ps.e2_grind_s);
    lap("acc", &mut stages);
    let main_claims = [
        Claim::word(vec![(s_off, rl.clone(), F128::ONE)], v_r),
        reg_claim(&td.sig, &ry, v_sig),
        reg_claim(&td.com, &ry, v_com),
        reg_claim(&td.ks, &ry, v_ks),
    ]
    .concat();
    TypedOut { acc_out, main_claims, rx: rx.iter().map(|&x| e3(x)).collect(), ry: ry.iter().map(|&x| e3(x)).collect(), v: [e3(v[0]), e3(v[1]), e3(v[2]), e3(v[3])], stages }
}

/// **`accOutOf` of an S2GT child** from its trace: the pin's `pin` samples, then the typed phases at E2 (one trace
/// entry per challenge, its query `st ‖ pending ‖ nonce`; the separator first). `κ ‖ r_x ‖ r_y` and `t` are the
/// challenges' lanes 0–1, `h` the 46 E2 scalars pending in `t`'s query.
pub fn acc_out_of_t(acc_in: &Acc, tr: &[(Vec<u8>, crate::oracle::Digest)], pin: usize) -> Acc {
    let lane = |b: &[u8], i: usize| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
    let ans = |e: usize| F128::new(lane(&tr[e].1, 0), lane(&tr[e].1, 1));
    // entries: q0, seed, the pin's samples, the separator, τ (20), ω, 20 zerocheck rounds, γ, 21 wiring rounds, 19
    // relayout rounds, κ (4), t
    let first = 2 + pin + 1;
    let (xv, yv) = (20usize, 21usize);
    let rx: Vec<F128> = (0..xv).map(|i| ans(first + xv + 1 + i)).collect();
    let g_at = first + xv + 1 + xv;
    let ry: Vec<F128> = (0..yv).map(|i| ans(g_at + 1 + i)).collect();
    let k_at = g_at + 1 + yv + SFLAT_LOG;
    let kappa: Vec<F128> = (0..4).map(|i| ans(k_at + i)).collect();
    let t_at = k_at + 4;
    let t = ans(t_at);
    let q = &tr[t_at].0;
    let h: Vec<F128> = (0..PHI_VARS_T + 1).map(|i| F128::new(lane(&q[32 + 16 * i..], 0), lane(&q[32 + 16 * i..], 1))).collect();
    assert_eq!(q.len(), 32 + 16 * (PHI_VARS_T + 1) + 8, "t's query holds h (46 E2 scalars) and the nonce");
    let b: Vec<F128> = [&kappa[..], &rx, &ry].concat();
    let a: Vec<F128> = acc_in.pt.iter().map(|&x| e2(x)).collect();
    Acc { pt: a.iter().zip(&b).map(|(&x, &y)| e3(x + t * (x + y))).collect(), y: e3(F128::poly_eval(&h, t)) }
}
