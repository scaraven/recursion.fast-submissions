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
use crate::lvm::typed_prove::{SFLAT_LOG, TData, TReg, TypedOut, sflat_inv};

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

/// `(A ⊗ B)_k` in `E2[y]/(y³ + y + 1)` (`LvmE2TWiring.mulY3`).
#[inline]
fn mul_y3(a: [F128; 3], b: [F128; 3]) -> [F128; 3] {
    let t = a[1] * b[2] + a[2] * b[1];
    let a2b2 = a[2] * b[2];
    [a[0] * b[0] + t, a[0] * b[1] + a[1] * b[0] + t + a2b2, a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + a2b2]
}

/// `Σ_k ω^k·((A ⊗ B)_k + C_k)` of nine values.
#[inline]
fn rel(v: &[F128; 9], om: [F128; 3]) -> F128 {
    let p = mul_y3([v[0], v[1], v[2]], [v[3], v[4], v[5]]);
    (0..3).map(|k| om[k] * (p[k] + v[6 + k])).sum()
}

/// The coefficient of an S2GF compact code (`oc`): `1` or the coefficient table's.
#[inline]
fn coef(b1: &Typed, oc: u32) -> F192 {
    if oc >> OC_SHIFT == 0 { F192::ONE } else { b1.coefs[(oc >> OC_SHIFT) as usize] }
}

/// `A_j, B_j` per slot over the live prefix (`C` is the honest prover's `A ⊗ B`), slot-major.
fn ab6(b1: &Typed, z: &[F64]) -> Vec<[F128; 6]> {
    let n = b1.x_live.max(2).next_multiple_of(2).min(1usize << b1.x_log);
    assert_eq!(b1.row_ptr[n] as usize, b1.ent.len(), "no entry past the live prefix of slots");
    crate::lv::parallel::map_collect(n, |x| {
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
    })
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

/// `Σ_k ω^k·(A ⊗ B)_k` (the relation without `C`: its degree-2 part).
#[inline]
fn rel_ab(a: [F128; 3], b: [F128; 3], om: [F128; 3]) -> F128 {
    let p = mul_y3(a, b);
    om[0] * p[0] + om[1] * p[1] + om[2] * p[2]
}

/// The zerocheck at E2 (honest: `C = A ⊗ B` on the cube, so round 0 sums `q(∞)` only and `C` is folded from the
/// products in round 0's fold). Every round reads only the live prefix (the rows are zero past it). Returns `r_x` and
/// the nine values at it.
fn zerocheck_t(ps: &mut ProverState, ab: Vec<[F128; 6]>, tau: &[F128], om: F128) -> (Vec<F128>, [F128; 9]) {
    let n = tau.len();
    let full = 1usize << n;
    let oms = [F128::ONE, om, om * om];
    let mut len = ab.len();
    assert!(n >= 1 && len % 2 == 0 && len <= full, "a zerocheck over at least one variable");
    let a3 = |v: &[F128; 6], o: usize| [v[o], v[o + 1], v[o + 2]];
    let mut e = F128::eq_table(&tau[1..]);
    // round 0: q(0) = q(1) = 0
    let (abr, er) = (&ab, &e);
    let [_, qi0] = sum2(len / 2, |j, acc| {
        let (x, y) = (&abr[2 * j], &abr[2 * j + 1]);
        let d: [F128; 6] = std::array::from_fn(|k| x[k] + y[k]);
        acc[1] ^= er[j].mul_unreduced(rel_ab(a3(&d, 0), a3(&d, 3), oms));
    });
    let mut sums = [F128::ZERO, qi0];
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
        let half = len / 2;
        let f = |u: F128, v: F128| u + ri * (u + v);
        t = if i == 0 {
            let abr = &ab;
            crate::lv::parallel::map_collect(half, |j| {
                let (x, y) = (&abr[2 * j], &abr[2 * j + 1]);
                let (cx, cy) = (mul_y3(a3(x, 0), a3(x, 3)), mul_y3(a3(y, 0), a3(y, 3)));
                std::array::from_fn(|k| if k < 6 { f(x[k], y[k]) } else { f(cx[k - 6], cy[k - 6]) })
            })
        } else {
            let tr = &t;
            crate::lv::parallel::map_collect(half, |j| std::array::from_fn(|k| f(tr[2 * j][k], tr[2 * j + 1][k])))
        };
        if i + 1 == n {
            break;
        }
        // the next round over the live prefix (odd length: a zero partner)
        len = (half + (half & 1)).max(2);
        t.resize(len, [F128::ZERO; 9]);
        e = (0..e.len() / 2).map(|j| e[2 * j] + e[2 * j + 1]).collect();
        let (tr, er) = (&t, &e);
        sums = sum2(len / 2, |j, acc| {
            let (lo, hi) = (&tr[2 * j], &tr[2 * j + 1]);
            let w = er[j];
            let d: [F128; 6] = std::array::from_fn(|k| lo[k] + hi[k]);
            acc[0] ^= w.mul_unreduced(rel(lo, oms));
            acc[1] ^= w.mul_unreduced(rel_ab(a3(&d, 0), a3(&d, 3), oms));
        });
    }
    let vals = t[0];
    assert!(claim == p * rel(&vals, oms), "the S2GT zerocheck's final claim");
    (r, vals)
}

/// Per compact code (`o | coefficient index << OC_SHIFT`): the code's split parts `(tag, E2 coefficient)`.
fn code_parts(b1: &Typed) -> Vec<Vec<(usize, F128)>> {
    (0..(b1.coefs.len() << OC_SHIFT) as u32).map(|oc| split(oc & OC_MASK, coef(b1, oc)).collect()).collect()
}

/// `u(y) = Σ_x eq(r_x, x)·Σ_{tag} γ^{row9(tag)}·M_tag(x, y)` (A_j at `γ^j`, B_j at `γ^{3+j}`, C_j at `γ^{6+j}`): one
/// E2 weight per compact code.
fn wiring_u_t(b1: &Typed, cp: &[Vec<(usize, F128)>], rx: &[F128], gamma: F128) -> Vec<F128> {
    let ex = F128::eq_table(rx);
    let gp = F128::powers(gamma, 9);
    let wt: Vec<F128> = cp.iter().map(|ps| ps.iter().map(|&(t, c)| gp[row9(t)] * c).sum()).collect();
    let ny = 1usize << b1.y_log;
    let live = b1.y_live.min(ny);
    let mut u: Vec<F128> = crate::lv::parallel::map_collect(live, |y| {
        let mut acc = F128Unreduced::ZERO;
        for &(x, oc) in &b1.cc[b1.col_ptr[y] as usize..b1.col_ptr[y + 1] as usize] {
            acc ^= ex[x as usize].mul_unreduced(wt[oc as usize]);
        }
        acc.reduce()
    });
    u.resize(ny, F128::ZERO);
    u
}

/// The plain degree-2 sumcheck of `Σ_y u(y)·z(y)` at E2 from `claim` (`g` 2 a round; round 0 by `K` products on `z`).
/// Returns the point and the final `u`, `z`. `z` covers `u`'s cube (both callers pass full-length words).
fn sumcheck_uz(ps: &mut ProverState, mut u: Vec<F128>, z: &[F64], mut claim: F128) -> (Vec<F128>, F128, F128) {
    let n = u.len().trailing_zeros() as usize;
    assert!(n >= 1 && z.len() >= u.len());
    let mut zz: Vec<F128> = Vec::new();
    let mut r = Vec::with_capacity(n);
    for i in 0..n {
        let half = u.len() / 2;
        let (uu, zr) = (&u, &zz);
        let [g0, g2] = if i == 0 {
            sum2(half, |j, acc| {
                let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], z[2 * j], z[2 * j + 1]);
                acc[0] ^= u0.mul_base_unreduced(z0);
                acc[1] ^= (u0 + u1).mul_base_unreduced(F64(z0.0 ^ z1.0));
            })
        } else {
            sum2(half, |j, acc| {
                let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], zr[2 * j], zr[2 * j + 1]);
                acc[0] ^= u0.mul_unreduced(z0);
                acc[1] ^= (u0 + u1).mul_unreduced(z0 + z1);
            })
        };
        // plain round: g(0) + g(1) = claim, so g₁ = claim + g₂ (characteristic 2)
        let g = [g0, claim + g2, g2];
        ps.add_round_poly_ext::<F128, 2>(&g, false);
        let ri = ps.challenge::<F128, 2>(Grp::C2);
        r.push(ri);
        claim = F128::poly_eval(&g, ri);
        let next: Vec<(F128, F128)> = if i == 0 {
            crate::lv::parallel::map_collect(half, |j| {
                let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], z[2 * j], z[2 * j + 1]);
                (u0 + ri * (u0 + u1), ri.mul_base(F64(z0.0 ^ z1.0)) + F128::new(z0.0, 0))
            })
        } else {
            crate::lv::parallel::map_collect(half, |j| {
                let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], zr[2 * j], zr[2 * j + 1]);
                (u0 + ri * (u0 + u1), z0 + ri * (z0 + z1))
            })
        };
        (u, zz) = next.into_iter().unzip();
    }
    if claim != u[0] * zz[0] {
        // (dev: `LVM_E2F_DEVPUB=1` runs an older blob whose relation fails at the header's cells)
        assert!(std::env::var("LVM_E2F_DEVPUB").is_ok_and(|v| v == "1"), "the S2GT plain sumcheck's final claim");
        eprintln!("lvm: LVM_E2F_DEVPUB: an S2GT sumcheck's final claim fails (an older blob's witness)");
    }
    (r, u[0], zz[0])
}

/// `M̃_tag(r_x, r_y)` for the twelve S2GT tags (`m + 4j`).
fn mat_vals12(b1: &Typed, cp: &[Vec<(usize, F128)>], rx: &[F128], ry: &[F128]) -> [F128; 12] {
    let (ex, ey) = (F128::eq_table(rx), F128::eq_table(ry));
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

/// `eq(r, x)` at a boolean point.
fn eq_at(r: &[F128], x: usize) -> F128 {
    crate::lvm::front::eq_at_index(r, x)
}

/// `Σ_{(base, log)} eq(r^{≥log}, base ≫ log)·z̃[base..](r^{<log})`.
fn reg_value(z: &[F64], r: &[F128], regs: &[(usize, usize)]) -> F128 {
    regs.iter()
        .map(|&(base, log)| {
            let e = F128::eq_table(&r[..log]);
            let s: F128 = e.iter().zip(&z[base..base + (1 << log)]).map(|(e, w)| e.mul_base(*w)).sum();
            eq_at(&r[log..], base >> log) * s
        })
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
pub fn prove_t(ps: &mut ProverState, b1: &Typed, z: &[F64], td: &TData, sblk: &[F64], s_off: usize, acc_in: &Acc) -> TypedOut {
    let mut stages = Vec::new();
    let mut t0 = std::time::Instant::now();
    let mut lap = |n: &'static str, st: &mut Vec<(&'static str, f64)>| {
        st.push((n, t0.elapsed().as_secs_f64()));
        t0 = std::time::Instant::now();
    };
    // 1. zerocheck: τ (20, each its own nonce), ω, the rounds, the nine values
    let tau: Vec<F128> = ps.challenges::<F128, 2>(Grp::C1, b1.x_log);
    let om = ps.challenge::<F128, 2>(Grp::C2);
    let (rx, vals) = zerocheck_t(ps, ab6(b1, z), &tau, om);
    ps.add_ext(&vals);
    lap("zerocheck", &mut stages);
    // 2. wiring: γ (g 4), Σ_k γ^k v_k, 21 rounds, 12 matrix values, 4 region values
    let gamma = ps.challenge::<F128, 2>(Grp::Bits(4));
    let claim0: F128 = vals.iter().enumerate().map(|(k, &v)| (0..k).fold(F128::ONE, |a, _| a * gamma) * v).sum();
    let cp = code_parts(b1);
    let u = wiring_u_t(b1, &cp, &rx, gamma);
    let (ry, _, _) = sumcheck_uz(ps, u, z, claim0);
    let v = mat_vals12(b1, &cp, &rx, &ry);
    let rr = |g: &[TReg]| g.iter().map(|g| (g.base, g.log)).collect::<Vec<_>>();
    let v_com = reg_value(z, &ry, &rr(&td.com));
    let v_s = reg_value(z, &ry, &[(td.sflat, SFLAT_LOG)]);
    let v_sig = reg_value(z, &ry, &rr(&td.sig));
    let v_ks = reg_value(z, &ry, &rr(&td.ks));
    ps.add_ext(&v);
    ps.add_ext(&[v_com, v_s, v_sig, v_ks]);
    lap("wiring", &mut stages);
    // 3. relayout: K(sflatWord p) = eq(r_y, S_flat + p) on S's 2^19 words
    let nr = sblk.len().trailing_zeros() as usize;
    assert_eq!(nr, SFLAT_LOG);
    let w_hi = eq_at(&ry[SFLAT_LOG..], td.sflat >> SFLAT_LOG);
    let e = F128::eq_table(&ry[..SFLAT_LOG]);
    let k: Vec<F128> = crate::lv::parallel::map_collect(1usize << nr, |c| w_hi * e[sflat_inv(c)]);
    let (rl, _, v_r) = sumcheck_uz(ps, k, sblk, v_s);
    ps.add_ext(&[v_r]);
    lap("relayout", &mut stages);
    // 4. A23 at Φ_Q (45 variables): κ (4), h (46), t (g 6), the zero scalar
    let kappa: Vec<F128> = ps.challenges::<F128, 2>(Grp::C1, 4);
    let es = eq_sel(&kappa);
    let y_own: F128 = (0..12).map(|t| es[t] * v[t]).sum();
    let b: Vec<F128> = [&kappa[..], &rx, &ry].concat();
    let a: Vec<F128> = acc_in.pt.iter().map(|&x| e2(x)).collect();
    assert_eq!(a.len(), PHI_VARS_T, "acc_in has 45 coordinates at S2GT");
    let line = |t: F128| -> Vec<F128> { a.iter().zip(&b).map(|(&x, &y)| x + t * (x + y)).collect() };
    let pts: Vec<Vec<F128>> = (2..=PHI_VARS_T as u64).map(|j| line(F128::new(j, 0))).collect();
    let mut ys = vec![e2(acc_in.y), y_own];
    ys.extend(phi_t(b1, &pts));
    // interpolation at the K points 0..45 is K-linear on the values: E2 values embedded in E3 interpolate exactly
    let h: Vec<F128> = interp_fixed(&ys.iter().map(|&x| e3(x)).collect::<Vec<_>>()).into_iter().map(e2).collect();
    ps.add_ext(&h);
    let tt = ps.challenge::<F128, 2>(Grp::Bits(6));
    ps.add_ext(&[F128::ZERO]);
    let acc_out = Acc { pt: line(tt).into_iter().map(e3).collect(), y: e3(F128::poly_eval(&h, tt)) };
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
