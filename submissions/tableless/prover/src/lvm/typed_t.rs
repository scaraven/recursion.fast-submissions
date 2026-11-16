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

/// `A_j, B_j` at slot `x` (`C` is the honest prover's `A ⊗ B`). PFAST-ZC: a split part `c_j·X^s·z` is the `K`
/// product `c_j·z` in coordinate `s` (one carry-less product, none when `c_j = 1`), summed unreduced per coordinate
/// and reduced once (the same values as [`ab6_row_ref`]).
#[inline]
fn ab6_row(b1: &Typed, z: &[F64], x: usize) -> [F128; 6] {
    use crate::lv::primitives::field::gf2_64::{mul_wide, reduce};
    let mut acc = [[0u128; 2]; 6];
    for e in &b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize] {
        let m = (e.o & 3) as usize;
        if m >= 2 {
            continue;
        }
        let s = (e.o >> 2 != 0) as usize;
        let zv = z[e.y as usize].0;
        for (j, l) in [e.c.c0, e.c.c1, e.c.c2].into_iter().enumerate() {
            if l != 0 {
                acc[3 * m + j][s] ^= if l == 1 { zv as u128 } else { mul_wide(l, zv) };
            }
        }
    }
    std::array::from_fn(|k| F128::new(reduce(acc[k][0]), reduce(acc[k][1])))
}

/// [`ab6_row`] by the split parts' E2 products (the reference `LVM_ZC_STATS=1` checks it against).
fn ab6_row_ref(b1: &Typed, z: &[F64], x: usize) -> [F128; 6] {
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

/// (dev, `LVM_ZC_STATS=1`) The structure of the rows `A_j, B_j`: per coordinate, the rows where it is nonzero and
/// where it is outside `K`; the entries' split parts by `(j, s)`.
fn ab_stats(b1: &Typed, z: &[F64]) {
    let n = ab_slots(b1);
    let (mut nz, mut nk) = ([0usize; 6], [0usize; 6]);
    let mut all_k = 0usize;
    let mut only0 = 0usize;
    for x in 0..n {
        let r = ab6_row(b1, z, x);
        assert_eq!(r, ab6_row_ref(b1, z, x), "the S2GT rows: fast = reference");
        for k in 0..6 {
            nz[k] += (r[k] != F128::ZERO) as usize;
            nk[k] += (r[k].c1 != 0) as usize;
        }
        all_k += r.iter().all(|v| v.c1 == 0) as usize;
        only0 += (r[1] == F128::ZERO && r[2] == F128::ZERO && r[4] == F128::ZERO && r[5] == F128::ZERO) as usize;
    }
    // per aligned chunk of 2^k slots (= a slot of round k's table): the chunks with only j = 0 rows, and with all in K too
    let rows: Vec<[F128; 6]> = (0..n).map(|x| ab6_row(b1, z, x)).collect();
    let mut ch = String::new();
    for k in [0usize, 1, 2, 3, 4, 6, 8, 11] {
        let (mut c0, mut ck, mut nc) = (0usize, 0usize, 0usize);
        for c in rows.chunks(1 << k) {
            nc += 1;
            let j0 = c.iter().all(|r| r[1] == F128::ZERO && r[2] == F128::ZERO && r[4] == F128::ZERO && r[5] == F128::ZERO);
            c0 += j0 as usize;
            ck += (j0 && c.iter().all(|r| r.iter().all(|v| v.c1 == 0))) as usize;
        }
        ch += &format!(" 2^{k}: {nc} j0 {c0} j0K {ck};");
    }
    eprintln!("lvm: ZC-STATS chunks{ch}");
    let mut parts = [[0usize; 2]; 3];
    let mut ones = 0usize;
    let mut small = 0usize;
    for e in &b1.ent {
        if e.o & 3 >= 2 {
            continue;
        }
        for (t, c) in split(e.o as u32, e.c) {
            parts[t >> 2][(c.c1 != 0) as usize] += 1;
            ones += (c == F128::ONE) as usize;
        }
    }
    for x in 0..n.min(1 << 16) {
        for e in &b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize] {
            small += (z[e.y as usize].0 < 1 << 16) as usize;
        }
    }
    eprintln!("lvm: ZC-STATS slots {n}: nonzero {nz:?} outside K {nk:?}; rows all in K {all_k}, rows with only j=0 {only0}; split parts [j][s] {parts:?}, coefficient 1 {ones}; small z (<2^16, first 2^16 slots) {small}");
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
        // (MBL: `LVM_MBL_TAMPER` too: the node's child is a tampered S2GL proof)
        assert!(devpub || std::env::var_os("LVM_TYPED_TAMPER").is_some() || std::env::var_os("LVM_MBL_TAMPER").is_some(), "{what}");
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
    // (PFAST-ZC: runs of rows with only their j = 0 coordinates, some in K, as the S2GT rows have)
    let ab: Vec<[F128; 6]> = (0..live)
        .map(|x| {
            let mut v: [F128; 6] = std::array::from_fn(|_| e());
            // (chunks of 2^8 rows: j = 0 only in two of three (but one row in 512), in K in every other (but one row
            // in 1024); smaller chunks see the runs of 2^8)
            if (x >> 8) % 3 != 1 && x % 512 != 300 {
                for k in [1, 2, 4, 5] {
                    v[k] = F128::ZERO;
                }
                if (x >> 8) % 2 == 0 && x % 1024 != 77 {
                    v[0].c1 = 0;
                    v[3].c1 = 0;
                }
            }
            v
        })
        .collect();
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
    // PFAST-ZC: the plain sumcheck `Σ u·z` with rounds 0 and 1 merged = one pass a round (live prefixes `live` and
    // `live − 6` when there is room)
    for lv in [live, live.saturating_sub(6).max(1)] {
        let u: Vec<F128> = (0..1usize << n).map(|x| if x < lv { e() } else { F128::ZERO }).collect();
        let zk: Vec<F64> = (0..1usize << n).map(|x| if x < lv { F64(e().c0) } else { F64::ZERO }).collect();
        let claim: F128 = u.iter().zip(&zk).map(|(a, b)| a.mul_base(*b)).sum();
        let (mut q1, mut q2) = (ProverState::seeded(&hdr), ProverState::seeded(&hdr));
        // (the separator and a first challenge, as `prove_t`'s transcript has before)
        assert!(q1.challenge::<F128, 2>(Grp::C2) == q2.challenge::<F128, 2>(Grp::C2));
        let a = sumcheck_uz_m(&mut q1, n, |x| u[x], &zk, claim, lv, true);
        let b = sumcheck_uz_m(&mut q2, n, |x| u[x], &zk, claim, lv, false);
        assert!(a == b && q1.body == q2.body && q1.trace == q2.trace, "the S2GT plain sumchecks: merged = one pass a round");
    }
    // (dev, `LVM_ZC_BENCH=K`: K timed runs of the fast zerocheck, rows from the table)
    if let Some(k) = std::env::var("LVM_ZC_BENCH").ok().and_then(|v| v.parse::<usize>().ok()) {
        let mut ts = Vec::with_capacity(k);
        for _ in 0..k {
            let mut p3 = ProverState::seeded(&hdr);
            let tau: Vec<F128> = p3.challenges::<F128, 2>(Grp::C1, n);
            let om = p3.challenge::<F128, 2>(Grp::C2);
            let t0 = std::time::Instant::now();
            let (r3, v3) = zerocheck_t(&mut p3, ab.len(), |x| ab[x], &tau, om);
            ts.push(t0.elapsed().as_secs_f64());
            assert!(r3 == r1 && v3 == v1);
        }
        ts.sort_by(f64::total_cmp);
        eprintln!("lvm: ZC-BENCH n {n} live {live}: min {:.4} med {:.4} max {:.4} s ({k} runs)", ts[0], ts[k / 2], ts[k - 1]);
    }
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

    /// `eq(r^{<L}, q mod 2^L)` (all of `eq(r, q)` when there is no high table).
    #[inline]
    fn lo_at(&self, q: usize) -> F128 {
        self.lo[q & ((1 << self.l) - 1)]
    }
}

/// `Σ_{q<n} eq(r, q)·f(q)` of two E2 values per `q` on the pool (`w = eq(r, ·)`), by blocks of `2^10` (the low
/// table's length when there is a high one): `eq(r^{≥10}, block)·Σ_q eq(r^{<10}, q mod 2^10)·f(q)` (unreduced inside a
/// block), one product a term fewer than `w.at(q)·f(q)`.
fn sum2w(n: usize, w: &EqW, f: impl Fn(usize) -> [F128; 2] + Sync) -> [F128; 2] {
    const CH: usize = 1 << 10;
    debug_assert!(w.hi.is_empty() || w.l == 10);
    let parts: Vec<[F128; 2]> = crate::lv::parallel::map_collect(n.div_ceil(CH), |ci| {
        let mut acc = [F128Unreduced::ZERO; 2];
        for q in ci * CH..((ci + 1) * CH).min(n) {
            let v = f(q);
            let wl = w.lo_at(q);
            acc[0] ^= wl.mul_unreduced(v[0]);
            acc[1] ^= wl.mul_unreduced(v[1]);
        }
        let a = acc.map(|a| a.reduce());
        if w.hi.is_empty() { a } else { a.map(|x| w.hi[(ci * CH) >> w.l] * x) }
    });
    parts.iter().fold([F128::ZERO; 2], |a, b| [a[0] + b[0], a[1] + b[1]])
}

/// PFAST-ZC: the log2 of a zerocheck chunk, in level-0 slots (round `i`'s table: `2^(ZG − i)` slots a chunk).
const ZG: usize = 8;

/// Whether a row has only its `j = 0` coordinates (`A₁ = A₂ = B₁ = B₂ = 0`, so `C = (A₀B₀, 0, 0)`).
#[inline]
fn j0_row(r: &[F128; 6]) -> bool {
    r[1] == F128::ZERO && r[2] == F128::ZERO && r[4] == F128::ZERO && r[5] == F128::ZERO
}

/// One zerocheck round's message from its sums `[q(0), q(∞)]` (the factor `eq(τ_i, ·)` and the product `p` of the
/// earlier rounds' factors apart), the challenge; updates `p` and the claim.
fn zc_round(ps: &mut ProverState, ti: F128, [q0, qi]: [F128; 2], p: &mut F128, claim: &mut F128) -> F128 {
    let t1 = F128::ONE + ti;
    let q1 = (*claim + *p * t1 * q0) * (*p * ti).inv();
    let l = q0 + q1 + qi;
    let gp = [*p * t1 * q0, *p * (t1 * l + q0), *p * (t1 * qi + l), *p * qi];
    ps.add_round_poly_ext::<F128, 2>(&[q0, l, qi], true);
    let ri = ps.challenge::<F128, 2>(Grp::C2);
    *claim = F128::poly_eval(&gp, ri);
    *p *= F128::ONE + ti + ri;
    ri
}

/// The zerocheck at E2 by chunks (PFAST-ZC): the same rounds and values as [`zerocheck_t_flat`]. Most rows have only
/// their `j = 0` coordinates (`A₀, B₀`; then `C = (A₀B₀, 0, 0)`), in long runs of slots: round 0's pass flags each
/// aligned chunk of `2^g` slots (`g = min(ZG, n − 1)`) whose rows all do, and the tables of rounds `2..g` keep
/// `(A₀, B₀, C₀)` per slot (48 bytes) plus the other six values only in the chunks not flagged (a folded slot of a
/// flagged chunk has only `j = 0` values too: the folds are coordinatewise). A flagged slot folds by three products
/// (from round 2's table on) and a flagged pair's sums are `A₀B₀ + C₀` and `(A₀ + A₀')(B₀ + B₀')` (`ω⁰ = 1`). From
/// round `g` on (a chunk is one slot) the nine-value table of [`zerocheck_t_flat`]. Rounds 0 and 1 take one pass
/// over the rows (round 1's sums as degree-2 polynomials in `r₀`), and one pass folds the rows 4 to 1 into round 2's
/// table. `LVM_ZC_FLAT=1` (dev), or
/// fewer than 4 variables: the flat zerocheck.
fn zerocheck_t(ps: &mut ProverState, nslots: usize, row: impl Fn(usize) -> [F128; 6] + Sync, tau: &[F128], om: F128) -> (Vec<F128>, [F128; 9]) {
    let n = tau.len();
    if n < 4 || std::env::var("LVM_ZC_FLAT").is_ok_and(|v| v == "1") {
        return zerocheck_t_flat(ps, nslots, row, tau, om);
    }
    let g = ZG.min(n - 1);
    let oms = [F128::ONE, om, om * om];
    let len0 = nslots;
    assert!(len0 % 2 == 0 && len0 <= 1usize << n, "a zerocheck's live prefix: even, in the cube");
    let a3 = |v: &[F128], o: usize| [v[o], v[o + 1], v[o + 2]];
    // `Q(v) = Σ_k ω^k (A ⊗ B)_k` of six values (`A₀B₀` when only j = 0)
    let qab = |v: &[F128; 6], j0: bool| if j0 { v[0] * v[3] } else { rel_ab(a3(v, 0), a3(v, 3), oms) };
    let e = EqW::new(&tau[2..]);
    tsub("zc eqp", ps.e2_grind_s);
    // rounds 0 and 1 from one pass: per chunk its rows, its flag, `(A₀, B₀)` per slot (the other four values only in a
    // chunk not flagged) and, per quad of rows `s₀..s₃` (zero past the live prefix), `Q` of `s₀ + s₁`, `s₂ + s₃`,
    // `s₀ + s₂`, `s₁ + s₃`, `s₀ + s₁ + s₂ + s₃` weighted by `eq(τ^{≥2}, quad)`
    let cs = 1usize << g;
    let nch = len0.div_ceil(cs);
    let mut m0: Vec<[F128; 2]> = Vec::with_capacity(len0);
    // (written only in the chunks not flagged; its length stays 0, every read is of a written slot)
    let mut x0: Vec<[F128; 4]> = Vec::with_capacity(len0);
    let (pm0, px0) = (crate::lv::parallel::SendPtr(m0.as_mut_ptr()), crate::lv::parallel::SendPtr(x0.as_mut_ptr()));
    let er = &e;
    let parts: Vec<(u8, [F128; 5])> = crate::lv::parallel::map_collect(nch, |c| {
        let (lo, hi) = (c * cs, ((c + 1) * cs).min(len0));
        let mut buf = [[F128::ZERO; 6]; 1 << ZG];
        let (mut j0, mut kk) = (true, true);
        for x in lo..hi {
            let r = row(x);
            j0 &= j0_row(&r);
            kk &= r[0].c1 == 0 && r[3].c1 == 0;
            buf[x - lo] = r;
            // SAFETY: slot x < len0 belongs to chunk c's task only, written once.
            unsafe {
                pm0.add(x).write([r[0], r[3]]);
            }
        }
        if !j0 {
            for x in lo..hi {
                let r = &buf[x - lo];
                // SAFETY: as above.
                unsafe { px0.add(x).write([r[1], r[2], r[4], r[5]]) };
            }
        }
        let mut acc = [F128Unreduced::ZERO; 5];
        // (a chunk starts at a multiple of 4 slots; the buffer is zero past the live prefix)
        for q in (lo / 4)..hi.div_ceil(4) {
            let s = &buf[4 * q - lo..4 * q - lo + 4];
            let add = |a: &[F128; 6], b: &[F128; 6]| -> [F128; 6] { std::array::from_fn(|k| a[k] + b[k]) };
            let (s01, s23, s02, s13) = (add(&s[0], &s[1]), add(&s[2], &s[3]), add(&s[0], &s[2]), add(&s[1], &s[3]));
            let s0123 = add(&s01, &s23);
            let wq = er.lo_at(q);
            for (k, v) in [s01, s23, s02, s13, s0123].iter().enumerate() {
                // (`A₀, B₀ ∈ K`: `Q` is a `K` product)
                acc[k] ^= if j0 && kk { wq.mul_base_unreduced(F64(v[0].c0) * F64(v[3].c0)) } else { wq.mul_unreduced(qab(v, j0)) };
            }
        }
        // (the chunk's quads share their high weight: 2^(g−2) divides the low table's length)
        let a = acc.map(|a| a.reduce());
        (j0 as u8 + (j0 && kk) as u8, if er.hi.is_empty() { a } else { a.map(|x| er.hi[(lo / 4) >> er.l] * x) })
    });
    // SAFETY: the chunks c < nch wrote every slot of 0..len0.
    unsafe { m0.set_len(len0) };
    // per chunk: 0 (some row with j > 0), 1 (only j = 0), 2 (only j = 0, `A₀, B₀ ∈ K`)
    let jk: Vec<u8> = parts.iter().map(|p| p.0).collect();
    let jf: Vec<bool> = jk.iter().map(|&k| k > 0).collect();
    let [s01, s23, s02, s13, s0123]: [F128; 5] = std::array::from_fn(|k| parts.iter().map(|p| p.1[k]).sum());
    // a chunk past the live ones holds zeros only (flagged)
    let flag = |c: usize| c >= nch || jf[c];
    tsub("zc r01sum", ps.e2_grind_s);
    let (mut p, mut claim) = (F128::ONE, F128::ZERO);
    let mut r = Vec::with_capacity(n);
    // round 0: q(0) = q(1) = 0 (honest), q(∞) over the pairs `eq(τ₁, 0)·(s₀ + s₁) ‖ eq(τ₁, 1)·(s₂ + s₃)`
    let r0 = zc_round(ps, tau[0], [F128::ZERO, (F128::ONE + tau[1]) * s01 + tau[1] * s23], &mut p, &mut claim);
    // round 1 as degree-2 polynomials in r₀: `rel(fold(s₀, s₁)) = (r₀ + r₀²)·Q(s₀ + s₁)` (C = A ⊗ B on the cube), and
    // `Q(u + r₀v) = (1 + r₀)·Q(u) + r₀·Q(u + v) + (r₀ + r₀²)·Q(v)` (u = s₀ + s₂, v = s₀ + s₁ + s₂ + s₃)
    let rr = r0 + r0 * r0;
    let r1 = zc_round(ps, tau[1], [rr * s01, (F128::ONE + r0) * s02 + r0 * s13 + rr * s0123], &mut p, &mut claim);
    r.extend([r0, r1]);
    tsub("zc chal", ps.e2_grind_s);
    // round 2's table: the rows folded 4 to 1 by `eq(r₀ r₁, ·)` (the same values as two folds), by chunks (g ≥ 3)
    let half0 = len0 / 2;
    let len1 = (half0 + (half0 & 1)).max(2);
    let half1 = len1 / 2;
    let mut len = (half1 + (half1 & 1)).max(2);
    let r01 = r0 * r1;
    let f4 = |a: F128, b: F128, c: F128, d: F128| a + r0 * (a + b) + r1 * (a + c) + r01 * (a + b + c + d);
    const Z: F128 = F128::ZERO;
    let m0r = &m0;
    let x0r = &x0;
    // a row's nine values (zero past the live prefix)
    let row9 = |x: usize, fl: bool| -> [F128; 9] {
        if x >= len0 {
            return [Z; 9];
        }
        let a = m0r[x];
        if fl {
            return [a[0], Z, Z, a[1], Z, Z, a[0] * a[1], Z, Z];
        }
        // SAFETY: slot x of a chunk not flagged: round 0's pass wrote it.
        let xx = unsafe { x0r.as_ptr().add(x).read() };
        let (aa, bb) = ([a[0], xx[0], xx[1]], [a[1], xx[2], xx[3]]);
        let c = mul_y3(aa, bb);
        [aa[0], aa[1], aa[2], bb[0], bb[1], bb[2], c[0], c[1], c[2]]
    };
    let mut sums;
    let mut sm: Vec<[F128; 3]> = Vec::with_capacity(len);
    let mut sx: Vec<[F128; 6]> = Vec::with_capacity(len);
    {
        let w = EqW::new(&tau[3..]);
        let (pm, px) = (crate::lv::parallel::SendPtr(sm.as_mut_ptr()), crate::lv::parallel::SendPtr(sx.as_mut_ptr()));
        let sh = g - 2;
        sums = sum2w(len / 2, &w, |q| {
            let mut v = [[Z; 9]; 2];
            let mut fl = [true; 2];
            for (k, vk) in v.iter_mut().enumerate() {
                let j = 2 * q + k;
                fl[k] = flag(j >> sh);
                if 4 * j < len0 {
                    *vk = if fl[k] && jk.get(j >> sh) == Some(&2) {
                        // (`K` rows: `r·k` products, `K` products for `C₀`)
                        let s: [[u64; 2]; 4] = std::array::from_fn(|t| if 4 * j + t < len0 { [m0r[4 * j + t][0].c0, m0r[4 * j + t][1].c0] } else { [0; 2] });
                        let fk = |v: [u64; 4]| F128::new(v[0], 0) + r0.mul_base(F64(v[0] ^ v[1])) + r1.mul_base(F64(v[0] ^ v[2])) + r01.mul_base(F64(v[0] ^ v[1] ^ v[2] ^ v[3]));
                        let c: [u64; 4] = std::array::from_fn(|t| (F64(s[t][0]) * F64(s[t][1])).0);
                        [fk([s[0][0], s[1][0], s[2][0], s[3][0]]), Z, Z, fk([s[0][1], s[1][1], s[2][1], s[3][1]]), Z, Z, fk(c), Z, Z]
                    } else if fl[k] {
                        let s: [[F128; 2]; 4] = std::array::from_fn(|t| if 4 * j + t < len0 { m0r[4 * j + t] } else { [Z; 2] });
                        let a = f4(s[0][0], s[1][0], s[2][0], s[3][0]);
                        let b = f4(s[0][1], s[1][1], s[2][1], s[3][1]);
                        let c = f4(s[0][0] * s[0][1], s[1][0] * s[1][1], s[2][0] * s[2][1], s[3][0] * s[3][1]);
                        [a, Z, Z, b, Z, Z, c, Z, Z]
                    } else {
                        let s: [[F128; 9]; 4] = std::array::from_fn(|t| row9(4 * j + t, false));
                        std::array::from_fn(|k| f4(s[0][k], s[1][k], s[2][k], s[3][k]))
                    };
                }
                // SAFETY: slot j < len belongs to pair q's task only, written once (in `sx` only when its chunk is not
                // flagged).
                unsafe {
                    pm.add(j).write([vk[0], vk[3], vk[6]]);
                    if !fl[k] {
                        px.add(j).write([vk[1], vk[2], vk[4], vk[5], vk[7], vk[8]]);
                    }
                }
            }
            let (lo, hi) = (&v[0], &v[1]);
            if fl[0] && fl[1] {
                [lo[0] * lo[3] + lo[6], (lo[0] + hi[0]) * (lo[3] + hi[3])]
            } else {
                let d: [F128; 6] = std::array::from_fn(|k| lo[k] + hi[k]);
                [rel(lo, oms), rel_ab(a3(&d, 0), a3(&d, 3), oms)]
            }
        });
        // SAFETY: the pairs q < len / 2 wrote every slot of 0..len of `sm`.
        unsafe { sm.set_len(len) };
    }
    drop((m0, x0));
    tsub("zc foldsum", ps.e2_grind_s);
    // rounds 2.. : the table of round i by chunks for i < g (`sm`: (A₀, B₀, C₀); `sx`: (A₁, A₂, B₁, B₂, C₁, C₂) in the
    // chunks not flagged, its length 0), nine values for i ≥ g
    let mut t: Vec<[F128; 9]> = Vec::new();
    for i in 2..n {
        let ri = zc_round(ps, tau[i], sums, &mut p, &mut claim);
        r.push(ri);
        tsub("zc chal", ps.e2_grind_s);
        let half = len / 2;
        let f = |u: F128, v: F128| u + ri * (u + v);
        let (smr, sxr, tr) = (&sm, &sx, &t);
        let nine = |j: usize| -> [F128; 9] {
            if i >= g {
                return tr[j];
            }
            let a = smr[j];
            if flag(j >> (g - i)) {
                return [a[0], Z, Z, a[1], Z, Z, a[2], Z, Z];
            }
            // SAFETY: slot j of a chunk not flagged: the previous round's pass wrote it.
            let x = unsafe { sxr.as_ptr().add(j).read() };
            [a[0], x[0], x[1], a[1], x[2], x[3], a[2], x[4], x[5]]
        };
        let fold9 = |j: usize| -> [F128; 9] {
            let (x, y) = (nine(2 * j), nine(2 * j + 1));
            std::array::from_fn(|k| f(x[k], y[k]))
        };
        if i + 1 == n {
            let vals = fold9(0);
            assert!(claim == p * rel(&vals, oms), "the S2GT zerocheck's final claim");
            return (r, vals);
        }
        // the next round over the live prefix (odd length: a zero partner), its sums with the fold
        let len2 = (half + (half & 1)).max(2);
        let w = EqW::new(&tau[i + 2..]);
        let wr = &w;
        if i < g {
            // round i + 1's table: by chunks (i + 1 < g) or nine values (i + 1 = g); slot j's chunk is its sources'
            let out9 = i + 1 == g;
            let sh = g - i - 1;
            let (mut nm, mut nx, mut nt): (Vec<[F128; 3]>, Vec<[F128; 6]>, Vec<[F128; 9]>) =
                if out9 { (Vec::new(), Vec::new(), Vec::with_capacity(len2)) } else { (Vec::with_capacity(len2), Vec::with_capacity(len2), Vec::new()) };
            let (pm, px, pt) = (crate::lv::parallel::SendPtr(nm.as_mut_ptr()), crate::lv::parallel::SendPtr(nx.as_mut_ptr()), crate::lv::parallel::SendPtr(nt.as_mut_ptr()));
            sums = sum2w(len2 / 2, wr, |q| {
                let mut v = [[Z; 9]; 2];
                let mut fl = [true; 2];
                for (k, vk) in v.iter_mut().enumerate() {
                    let j = 2 * q + k;
                    fl[k] = flag(j >> sh);
                    if j < half {
                        *vk = if fl[k] {
                            let (x, y) = (smr[2 * j], smr[2 * j + 1]);
                            [f(x[0], y[0]), Z, Z, f(x[1], y[1]), Z, Z, f(x[2], y[2]), Z, Z]
                        } else {
                            fold9(j)
                        };
                    }
                    // SAFETY: slot j < len2 belongs to pair q's task only, written once (in `nx` only when its chunk is
                    // not flagged).
                    unsafe {
                        if out9 {
                            pt.add(j).write(*vk);
                        } else {
                            pm.add(j).write([vk[0], vk[3], vk[6]]);
                            if !fl[k] {
                                px.add(j).write([vk[1], vk[2], vk[4], vk[5], vk[7], vk[8]]);
                            }
                        }
                    }
                }
                let (lo, hi) = (&v[0], &v[1]);
                if fl[0] && fl[1] {
                    [lo[0] * lo[3] + lo[6], (lo[0] + hi[0]) * (lo[3] + hi[3])]
                } else {
                    let d: [F128; 6] = std::array::from_fn(|k| lo[k] + hi[k]);
                    [rel(lo, oms), rel_ab(a3(&d, 0), a3(&d, 3), oms)]
                }
            });
            // SAFETY: the pairs q < len2 / 2 wrote every slot of 0..len2 (of `nm` or `nt`).
            unsafe {
                if out9 {
                    nt.set_len(len2);
                } else {
                    nm.set_len(len2);
                }
            }
            sm = nm;
            sx = nx;
            t = nt;
        } else {
            let mut nt: Vec<[F128; 9]> = Vec::with_capacity(len2);
            let pt = crate::lv::parallel::SendPtr(nt.as_mut_ptr());
            sums = sum2w(len2 / 2, wr, |q| {
                let mut v = [[Z; 9]; 2];
                for (k, vk) in v.iter_mut().enumerate() {
                    let j = 2 * q + k;
                    if j < half {
                        *vk = fold9(j);
                    }
                    // SAFETY: slot j < len2 belongs to pair q's task only, written once.
                    unsafe { pt.add(j).write(*vk) };
                }
                let (lo, hi) = (&v[0], &v[1]);
                let d: [F128; 6] = std::array::from_fn(|k| lo[k] + hi[k]);
                [rel(lo, oms), rel_ab(a3(&d, 0), a3(&d, 3), oms)]
            });
            // SAFETY: the pairs q < len2 / 2 wrote every slot of 0..len2.
            unsafe { nt.set_len(len2) };
            t = nt;
        }
        len = len2;
        tsub("zc foldsum", ps.e2_grind_s);
    }
    unreachable!("the last round returns")
}

/// The zerocheck at E2 (honest: `C = A ⊗ B` on the cube, so round 0 sums `q(∞)` only and `C` is folded from the
/// products in round 0's fold). Every round reads only the live prefix (the rows are zero past it). Returns `r_x` and
/// the nine values at it. PFAST-T: each round's fold is fused with the next round's sums (one pass a round, the
/// folded table written once at its padded length), and the next round's weights `eq(τ^{≥i+2}, ·)` come from
/// [`EqW`] (no serial fold of the weight vector).
/// (PFAST-T: the rows `A_j, B_j` of the `nslots` live slots come from `row`, built in round 0's pass.)
fn zerocheck_t_flat(ps: &mut ProverState, nslots: usize, row: impl Fn(usize) -> [F128; 6] + Sync, tau: &[F128], om: F128) -> (Vec<F128>, [F128; 9]) {
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
/// E2 weight per compact code. PFAST-ZC: as a function of `y < y_live` ([`sumcheck_uz`] tabulates it on the live prefix).
fn wiring_u_t<'a>(b1: &'a Typed, rx: &[F128], gamma: F128) -> impl Fn(usize) -> F128 + Sync + 'a {
    // (PFAST-T: `eq(r_x, x)` from two small tables per entry, no 2^20 table to build and gather from)
    let ex = EqW::new(rx);
    let wt = code_weights(b1, &F128::powers(gamma, 9));
    move |y: usize| {
        let mut acc = F128Unreduced::ZERO;
        for &(x, oc) in &b1.cc[b1.col_ptr[y] as usize..b1.col_ptr[y + 1] as usize] {
            acc ^= ex.at(x as usize).mul_unreduced(wt[oc as usize]);
        }
        acc.reduce()
    }
}

/// The plain degree-2 sumcheck of `Σ_y u(y)·z(y)` at E2 from `claim` (`g` 2 a round; round 0 by `K` products on `z`).
/// Returns the point and the final `u`, `z`. `z` covers the cube `2^n` (both callers pass full-length words). `live`: `u`
/// and `z` are zero from word `live` on, so every round reads only the live prefix (the folds of zeros are zero).
/// Each round's fold is fused with the next round's sums (one pass a round).
/// PFAST-ZC: `u` is a function, evaluated once per live word (`u(y)`, `y < live`; zero past it) into a table of the
/// live prefix (no zeros written past it).
fn sumcheck_uz(ps: &mut ProverState, n: usize, u: impl Fn(usize) -> F128 + Sync, z: &[F64], claim: F128, live: usize) -> (Vec<F128>, F128, F128) {
    let merged = !std::env::var("LVM_UZ_FLAT").is_ok_and(|v| v == "1");
    sumcheck_uz_m(ps, n, u, z, claim, live, merged)
}

/// [`sumcheck_uz`], rounds 0 and 1 from one pass when `merged` (and n ≥ 3), else one pass a round.
fn sumcheck_uz_m(ps: &mut ProverState, n: usize, ufn: impl Fn(usize) -> F128 + Sync, z: &[F64], mut claim: F128, live: usize, merged: bool) -> (Vec<F128>, F128, F128) {
    let nn = 1usize << n;
    assert!(n >= 1 && z.len() >= nn && live <= nn);
    let z = &z[..nn];
    #[cfg(feature = "selfcheck")]
    {
        assert!(z[live..].iter().all(|x| *x == F64::ZERO), "zero past the live prefix");
    }
    // the live prefix at a round: even, at least 2
    let len0 = live.max(2).next_multiple_of(2).min(nn);
    // `u` on the live prefix, one word a task (its own pass: in round 0's, by blocks of words, it was slower)
    let u: Vec<F128> = crate::lv::parallel::map_collect(len0, |k| if k < live { ufn(k) } else { F128::ZERO });
    tsub("uz u", ps.e2_grind_s);
    let uu = &u;
    let mut r = Vec::with_capacity(n);
    // PFAST-ZC: rounds 0 and 1 from one pass over the words (n ≥ 3; `LVM_UZ_FLAT=1`, dev: one pass a round). Per
    // quad of words `4q + k` the eight products `u_k z_k` (k < 3), `(u₀ + u₁)(z₀ + z₁)`, `(u₂ + u₃)(z₂ + z₃)`,
    // `(u₀ + u₂)(z₀ + z₂)`, `(u₁ + u₃)(z₁ + z₃)`, `(Σu)(Σz)`: round 0's sums, and round 1's as degree-2 polynomials in
    // `r₀` (their values at 0, 1 and ∞); then one pass folds the words by `(r₀, r₁)` (`eq(r₀ r₁, ·)`, the same values as
    // two folds) with round 2's sums.
    let kx = |a: F64, b: F64| F64(a.0 ^ b.0);
    // a word of `u` and of `z`, zero past the live prefix
    let at = |k: usize| -> (F128, F64) { if k < len0 { (uu[k], z[k]) } else { (F128::ZERO, F64::ZERO) } };
    let p0 = if n >= 3 && merged {
        const CHQ: usize = 1 << 10;
        let nq = len0.div_ceil(4);
        let parts: Vec<[F128Unreduced; 8]> = crate::lv::parallel::map_collect(nq.div_ceil(CHQ), |ci| {
            let mut s = [F128Unreduced::ZERO; 8];
            for q in ci * CHQ..((ci + 1) * CHQ).min(nq) {
                let ((u0, z0), (u1, z1), (u2, z2), (u3, z3)) = (at(4 * q), at(4 * q + 1), at(4 * q + 2), at(4 * q + 3));
                s[0] ^= u0.mul_base_unreduced(z0);
                s[1] ^= u1.mul_base_unreduced(z1);
                s[2] ^= u2.mul_base_unreduced(z2);
                s[3] ^= (u0 + u1).mul_base_unreduced(kx(z0, z1));
                s[4] ^= (u2 + u3).mul_base_unreduced(kx(z2, z3));
                s[5] ^= (u0 + u2).mul_base_unreduced(kx(z0, z2));
                s[6] ^= (u1 + u3).mul_base_unreduced(kx(z1, z3));
                s[7] ^= (u0 + u1 + u2 + u3).mul_base_unreduced(kx(kx(z0, z1), kx(z2, z3)));
            }
            s
        });
        let s: [F128; 8] = std::array::from_fn(|k| parts.iter().fold(F128Unreduced::ZERO, |a, p| a ^ p[k]).reduce());
        Some(s)
    } else {
        None
    };
    let (i0, mut cur, mut sums, mut len): (usize, Option<(Vec<F128>, Vec<F128>)>, [F128; 2], usize) = if let Some([sa, sb, sc, sd, se, sf, sg, sh]) = p0 {
        tsub("uz r01sum", ps.e2_grind_s);
        let mut round = |g0: F128, g2: F128| -> F128 {
            let g = [g0, claim + g2, g2];
            ps.add_round_poly_ext::<F128, 2>(&g, false);
            let ri = ps.challenge::<F128, 2>(Grp::C2);
            claim = F128::poly_eval(&g, ri);
            ri
        };
        let r0 = round(sa + sc, sd + se);
        // a degree-2 polynomial from its values at 0, 1, ∞: `P(0)(1 + r) + P(1)r + P(∞)(r + r²)`
        let (a0, a2) = (F128::ONE + r0, r0 + r0 * r0);
        let r1 = round(sa * a0 + sb * r0 + sd * a2, sf * a0 + sg * r0 + sh * a2);
        r.extend([r0, r1]);
        tsub("uz chal", ps.e2_grind_s);
        // round 2's tables: the live prefix of round 1 is even and at least 2 (n ≥ 3), round 2's too
        let half1 = len0.div_ceil(2).max(2).next_multiple_of(2) / 2;
        let len2 = half1.max(2).next_multiple_of(2);
        let r01 = r0 * r1;
        let fold4 = |j: usize| -> (F128, F128) {
            let ((u0, z0), (u1, z1), (u2, z2), (u3, z3)) = (at(4 * j), at(4 * j + 1), at(4 * j + 2), at(4 * j + 3));
            let uf = u0 + r0 * (u0 + u1) + r1 * (u0 + u2) + r01 * (u0 + u1 + u2 + u3);
            let zf = F128::new(z0.0, 0) + r0.mul_base(kx(z0, z1)) + r1.mul_base(kx(z0, z2)) + r01.mul_base(kx(kx(z0, z1), kx(z2, z3)));
            (uf, zf)
        };
        let (mut nu, mut nz): (Vec<F128>, Vec<F128>) = (Vec::with_capacity(len2), Vec::with_capacity(len2));
        let (pu, pz) = (crate::lv::parallel::SendPtr(nu.as_mut_ptr()), crate::lv::parallel::SendPtr(nz.as_mut_ptr()));
        let sums2 = sum2(len2 / 2, |q, acc| {
            let mut v = [(F128::ZERO, F128::ZERO); 2];
            for (k, vk) in v.iter_mut().enumerate() {
                let j = 2 * q + k;
                if 4 * j < len0 {
                    *vk = fold4(j);
                }
                // SAFETY: slot j < len2 belongs to pair q's task only, written once.
                unsafe {
                    pu.add(j).write(vk.0);
                    pz.add(j).write(vk.1);
                }
            }
            acc[0] ^= v[0].0.mul_unreduced(v[0].1);
            acc[1] ^= (v[0].0 + v[1].0).mul_unreduced(v[0].1 + v[1].1);
        });
        // SAFETY: the pairs q < len2 / 2 wrote every slot of 0..len2.
        unsafe {
            nu.set_len(len2);
            nz.set_len(len2);
        }
        tsub("uz foldsum", ps.e2_grind_s);
        (2, Some((nu, nz)), sums2, len2)
    } else {
        let sums0 = sum2(len0 / 2, |j, acc| {
            let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], z[2 * j], z[2 * j + 1]);
            acc[0] ^= u0.mul_base_unreduced(z0);
            acc[1] ^= (u0 + u1).mul_base_unreduced(F64(z0.0 ^ z1.0));
        });
        tsub("uz r0sum", ps.e2_grind_s);
        (0, None, sums0, len0)
    };
    for i in i0..n {
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
    if std::env::var("LVM_ZC_STATS").is_ok_and(|v| v == "1") {
        ab_stats(b1, z);
    }
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
    let (ry, _, _) = sumcheck_uz(ps, b1.y_log, u, z, claim0, b1.y_live.min(1usize << b1.y_log));
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
    let k = |c: usize| e.at(sflat_inv(c));
    tsub("rl k", ps.e2_grind_s);
    let (rl, _, v_r) = sumcheck_uz(ps, nr, k, sblk, v_s, 1 << nr);
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
