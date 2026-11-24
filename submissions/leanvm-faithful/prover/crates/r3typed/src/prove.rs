//! FORMAT6 v2.4 §6.4a, prover side: rows 1–12 on the v6 transcript, exactly (Lean `Lvm6.Ty.typedProgE` up to the
//! mini-bus: `zeroProgE`, `wireProgE`, `relayProgE`, `accProgE`), and §6.4's claims 1–4 (stack claims 46–49).
//!
//! | # | Items | here |
//! |---|---|---|
//! | 1 | 20 × `G(1)` | `τ` |
//! | 2 | 20 × `R(2, 2)` eq mode (`c₁, c₂`) | [`zerocheck`] on `eq(τ, x)·(A·B + C)(x)`, normalized (the next claim is `q(c)`) |
//! | 3 | `E(3)` | `A, B, C` at `r_x` |
//! | 4 | `G(2)` | `γ` |
//! | 5 | 21 × `R(2, 2)` plain (`c₀, c₂`) | [`product_sumcheck`] on `u(y)·z(y)`, `u = Σ_o g_o·M̃_o(r_x, ·)`, `g = (1, γ, γ², γ²)` |
//! | 6 | `E(4)` | `v_A, v_B, v_D, v_W = M̃_o(r_x, r_y)` |
//! | 7 | `E(4)` | `v_com, v_S, v_σ, v_KS`: `Σ_{y ∈ s} eq(r_y, y)·z(y)` |
//! | 8 | 19 × `R(2, 2)` plain | [`product_sumcheck`] on `K(w)·S(w)`, `K(sflatW(y)) = eq(r_y, y)`, `S` = `C_rec`'s window |
//! | 9 | `E(1)` | `v_R = S̃(r)` |
//! | 10 | 2 × `G(1)` | `κ` |
//! | 11 | `E(44)` | `h = Φ_Q ∘ line`, `line(t) = a + t·(a + b)`, `a = accIn.pt`, `b = κ ‖ r_x ‖ r_y` |
//! | 12 | `G(6)` | `t`; `accOut = (line(t), h(t))` |

use fiat_shamir::{ProverState, Search};
use primitives::field::{F64, F128, F128x8, Prod8};
use primitives::multilinear::{eq_table, poly_eval};
use r3core::claim::PClaim;

use crate::circuit::{Circuit, PHI_VARS, REC_BASE, REC_OFF, REC_VARS, Src, X_VARS, Y_VARS, mat_weights};
use crate::witness::{TypedWitness, mat_z};

/// FORMAT6 §6.4a's grinds (PARAM `g(c) = ⌈log₂(8c/7)⌉`; Lean `gTau … gT`).
pub const G_TAU: u32 = 1;
pub const G_ZERO: u32 = 2;
pub const G_GAMMA: u32 = 2;
pub const G_WIRE: u32 = 2;
pub const G_KAPPA: u32 = 1;
pub const G_T: u32 = 6;

/// An accumulator `(pt, y)`: the claim `Φ_Q(pt) = y` (A23; `HDR.accIn`, `accOut`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Acc {
    pub pt: Vec<F128>,
    pub y: F128,
}

impl Acc {
    /// The honest `accIn` at `b = 0` (FORMAT6 §2.1): `(0^43, Φ_Q(0^43))`.
    pub fn leaf(circ: &Circuit) -> Acc {
        let pt = vec![F128::ZERO; PHI_VARS];
        Acc { y: circ.phi_q(&pt), pt }
    }

    /// `pt` then `y` as `HDR`'s `accIn` scalars (`fs6::schedule::header`'s `acc_in`).
    pub fn to_hdr(&self) -> Vec<fs6::E> {
        self.pt.iter().chain([&self.y]).map(|e| e.to_limbs()).collect()
    }

    pub fn from_hdr(v: &[fs6::E]) -> Acc {
        assert_eq!(v.len(), PHI_VARS + 1);
        Acc { pt: v[..PHI_VARS].iter().map(|&e| F128::from_limbs(e)).collect(), y: F128::from_limbs(v[PHI_VARS]) }
    }
}

/// What §6.4a leaves.
pub struct TypedOut {
    /// Stack claims 46–49 in §6.4's order: the relayout's point claim on `C_rec`'s window, `σ′`'s region claim,
    /// the committed block's (`T`), the `KS` aliases'.
    pub claims: Vec<PClaim>,
    pub acc_out: Acc,
    pub tau: Vec<F128>,
    pub r_x: Vec<F128>,
    /// `A, B, C` at `r_x`.
    pub abc: [F128; 3],
    pub gamma: F128,
    pub r_y: Vec<F128>,
    /// `v_A, v_B, v_D, v_W`.
    pub mats: [F128; 4],
    /// `v_com, v_S, v_σ, v_KS`.
    pub regions: [F128; 4],
    /// The relayout's point `r ∈ E^19` and `v_R`.
    pub r: Vec<F128>,
    pub v_r: F128,
    pub kappa: [F128; 2],
    /// `h₀ … h₄₃`.
    pub h: Vec<F128>,
    pub t: F128,
    /// Seconds per phase: zerocheck (rows 1–3), wiring (4–7), relayout (8–9), A23 (10–12), claims.
    pub times: Vec<(&'static str, f64)>,
}

/// A test hook: add `delta` to the `index`-th scalar §6.4a sends (of 176, in `BODY` order), grinding on the
/// altered bytes, so that a verifier must reject by a check rather than by a nonce.
#[derive(Clone, Copy, Debug)]
pub struct Tamper {
    pub index: usize,
    pub delta: F128,
}

struct Tx<'a, S> {
    ps: &'a mut ProverState<F128, S>,
    sent: usize,
    tamper: &'a [Tamper],
}

impl<S: Search> Tx<'_, S> {
    fn send(&mut self, x: F128) {
        let x = self.tamper.iter().filter(|t| t.index == self.sent).fold(x, |x, t| x + t.delta);
        self.sent += 1;
        self.ps.add_scalar(x);
    }

    /// `G(g)`: the nonce, the ground draw.
    fn ground(&mut self, g: u32) -> F128 {
        self.ps.grind(g);
        self.ps.sample()
    }
}

/// §6.4a, rows 1–12. `stack` is the committed stack (`T` written by [`crate::witness::witness`]); `acc_in` is
/// `HDR.accIn`.
pub fn prove_typed<S: Search>(ps: &mut ProverState<F128, S>, w: &TypedWitness, stack: &[F64], acc_in: &Acc) -> TypedOut {
    prove_typed_with(ps, w, stack, acc_in, &[])
}

#[doc(hidden)]
pub fn prove_typed_with<S: Search>(
    ps: &mut ProverState<F128, S>,
    w: &TypedWitness,
    stack: &[F64],
    acc_in: &Acc,
    tamper: &[Tamper],
) -> TypedOut {
    let circ = w.circ;
    assert_eq!(acc_in.pt.len(), PHI_VARS);
    let mut tx = Tx { ps, sent: 0, tamper };
    let mut times = Vec::new();
    let mut clock = std::time::Instant::now();
    let mut lap = |name: &'static str| {
        times.push((name, clock.elapsed().as_secs_f64()));
        clock = std::time::Instant::now();
    };

    // rows 1–3: the zerocheck
    let tau: Vec<F128> = (0..X_VARS).map(|_| tx.ground(G_TAU)).collect();
    let [ma, mb, md, mw] = mat_z(circ, &w.z);
    let mc: Vec<F128> = md.iter().zip(&mw).map(|(&d, &w)| d + w).collect();
    let (r_x, abc) = zerocheck(&mut tx, ma, mb, mc, &tau);
    tx.send(abc[0]);
    tx.send(abc[1]);
    tx.send(abc[2]);

    lap("zerocheck");

    // rows 4–7: the wiring
    let gamma = tx.ground(G_GAMMA);
    let g = mat_weights(gamma);
    let eqx = eq_table(&r_x);
    let mut u = vec![F128::ZERO; 1 << Y_VARS];
    for e in &circ.ents {
        u[e.y as usize] += g[e.o as usize] * e.c * eqx[e.x as usize];
    }
    let z: Vec<F128> = w.z.iter().map(|&k| F128::from(k)).collect();
    let claim = abc[0] + gamma * abc[1] + g[2] * abc[2];
    let (r_y, _) = product_sumcheck(&mut tx, u, z, claim, G_WIRE);
    let eqy = eq_table(&r_y);
    let mut mats = [F128::ZERO; 4];
    for e in &circ.ents {
        mats[e.o as usize] += e.c * eqx[e.x as usize] * eqy[e.y as usize];
    }
    drop(eqx);
    let reg_val = |s: Src| {
        circ.regs_of(s).fold(F128::ZERO, |a, r| {
            (r.base..r.base + r.len()).fold(a, |a, y| a + eqy[y].mul_base(w.z[y]))
        })
    };
    let regions = [reg_val(Src::Com), reg_val(Src::Sflat), reg_val(Src::Sigma), reg_val(Src::Ks)];
    mats.iter().chain(&regions).for_each(|&v| tx.send(v));

    lap("wiring");

    // rows 8–9: the relayout
    let mut k = vec![F128::ZERO; 1 << REC_VARS];
    for r in circ.regs_of(Src::Sflat) {
        for i in 0..r.len() {
            k[r.off + i] += eqy[r.base + i];
        }
    }
    drop(eqy);
    let s: Vec<F128> = stack[REC_BASE..REC_BASE + (1 << REC_VARS)].iter().map(|&k| F128::from(k)).collect();
    let (r, v_r) = product_sumcheck(&mut tx, k, s, regions[1], G_WIRE);
    tx.send(v_r);

    lap("relayout");

    // rows 10–12: A23
    let kappa = [tx.ground(G_KAPPA), tx.ground(G_KAPPA)];
    let b: Vec<F128> = kappa.iter().chain(&r_x).chain(&r_y).copied().collect();
    let line = |t: F128| -> Vec<F128> { acc_in.pt.iter().zip(&b).map(|(&a, &b)| a + t * (a + b)).collect() };
    let xs: Vec<F128> = (0..=PHI_VARS as u64).map(|i| F128::new(i, 0)).collect();
    // R5 (PATCHES.md): the 44 points in one pass over `Q`'s entries (was `phi_q` point by point).
    let ys: Vec<F128> = circ.phi_q_many(&xs.iter().map(|&t| line(t)).collect::<Vec<_>>());
    let h = interpolate(&xs, &ys);
    debug_assert_eq!(h[0], acc_in.y, "accIn is not on Φ_Q");
    h.iter().for_each(|&c| tx.send(c));
    let t = tx.ground(G_T);
    let acc_out = Acc { pt: line(t), y: poly_eval(&h, t) };
    assert_eq!(tx.sent, 176, "§6.4a sends 176 scalars");

    lap("a23");
    let claims = claims(circ, &r_y, &regions, &r, v_r);
    lap("claims");
    if std::env::var_os("LVM6_R5_LAPS").is_some() {
        eprintln!("r5 typed laps {times:?}"); // dev (R5): §6.4a's sub-phases
    }
    TypedOut { claims, acc_out, tau, r_x, abc, gamma, r_y, mats, regions, r, v_r, kappa, h, t, times }
}

/// §6.4's claims 1–4 (stack claims 46–49).
pub fn claims(circ: &Circuit, r_y: &[F128], regions: &[F128; 4], r: &[F128], v_r: F128) -> Vec<PClaim> {
    let mut v = vec![PClaim::point("46 typed relayout (C_rec)", REC_OFF, r.to_vec(), v_r)];
    for (label, s, val) in [
        ("47 typed sigma' region (C_rec)", Src::Sigma, regions[2]),
        ("48 typed committed region (T)", Src::Com, regions[0]),
        ("49 typed KS aliases region", Src::Ks, regions[3]),
    ] {
        v.push(region_claim(circ, label, s, r_y, val));
    }
    v
}

/// A region claim (Lean `regClaimE`) as a dense weight on the smallest aligned block holding its targets: the
/// weight on the stack is the same as on the window.
fn region_claim(circ: &Circuit, label: &str, s: Src, r_y: &[F128], value: F128) -> PClaim {
    if circ.regs_of(s).next().is_none() {
        // no region of `s` (CD's typed blob has no `sigma`, no `ks` yet): the zero weight, value `0` when honest
        return PClaim::dense(label, REC_BASE, 0, value, |_, _: &mut [F128]| {});
    }
    let (off, mu) = circ.region_block(s);
    let regs: Vec<_> = circ.regs_of(s).copied().collect();
    let ry = r_y.to_vec();
    PClaim::dense(label, off, mu, value, move |scale, wt: &mut [F128]| {
        for g in &regs {
            let hi = scale * crate::circuit::eq_bits(&ry[g.log..], g.base >> g.log);
            let lo = eq_table(&ry[..g.log]);
            let at = g.stack_idx(0) - (off << mu);
            for (i, &e) in lo.iter().enumerate() {
                wt[at + i] += hi * e;
            }
        }
    })
}

/// `Σ` over chunks of `n` items of `f(lo, hi)`, on the pool.
fn psum<const N: usize>(n: usize, f: impl Fn(usize, usize) -> [F128; N] + Sync) -> [F128; N] {
    const CH: usize = 1 << 12;
    parallel::map_reduce(
        n.div_ceil(CH),
        || [F128::ZERO; N],
        |c| f(c * CH, ((c + 1) * CH).min(n)),
        |a, b| std::array::from_fn(|i| a[i] + b[i]),
    )
}

/// `v[j] = v[2j] + r·(v[2j] + v[2j+1])`. R6: eight outputs at a time in leanVM's `F128x8` (the even and odd
/// entries of sixteen), a pool task per 4,096 outputs; the same field elements.
fn fold(v: &mut Vec<F128>, r: F128) {
    let half = v.len() / 2;
    if !PACKED || half % 8 != 0 {
        let out = parallel::map_collect(half, |j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1]));
        *v = out;
        return;
    }
    let mut out = vec![F128::ZERO; half];
    let rr = F128x8::splat(r);
    let src: &[F128] = v;
    parallel::chunks_mut(&mut out, FOLD_CHUNK, |c, out| {
        let src = &src[2 * c * FOLD_CHUNK..][..2 * out.len()];
        for (o, s) in out.as_chunks_mut::<8>().0.iter_mut().zip(src.as_chunks::<16>().0) {
            let (e, d) = pair8(s);
            *o = (e + rr * (e + d)).to_array();
        }
    });
    *v = out;
}

/// R6: the `F128x8` paths where leanVM's eight-lane kernel is the wide multiplier (AVX-512 with VPCLMULQDQ, the
/// evaluation tier); elsewhere the scalar loops as before (the portable `F128x8` is slower there).
const PACKED: bool = cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"));

/// Outputs a task of [`fold`] writes.
const FOLD_CHUNK: usize = 1 << 12;

/// The even and odd entries of sixteen: `(v[2j], v[2j+1])` for `j < 8`, as `F128x8`.
#[inline(always)]
fn pair8(s: &[F128; 16]) -> (F128x8, F128x8) {
    let (lo, hi) = s.split_at(8);
    F128x8::even_odd(F128x8::from_array(lo.try_into().unwrap()), F128x8::from_array(hi.try_into().unwrap()))
}

/// Eight consecutive entries from `at`.
#[inline(always)]
fn load8(v: &[F128], at: usize) -> F128x8 {
    F128x8::from_array(v[at..at + 8].try_into().unwrap())
}

/// A zero sum of unreduced products.
#[inline(always)]
fn zero8() -> Prod8 {
    F128x8::splat(F128::ZERO).mul_unreduced(F128x8::splat(F128::ZERO))
}

/// Rows 1–2: the zerocheck of `Σ_x eq(τ, x)·(A(x)·B(x) + C(x)) = 0`, eq-mode rounds over `x`'s variables (low
/// first), message `c₁, c₂` of `q(X) = Σ_{x'} eq(τ_{>i}, x')·(A·B + C)(r_{<i}, X, x')`; returns `r_x` and
/// `Ã(r_x), B̃(r_x), C̃(r_x)`.
fn zerocheck<S: Search>(tx: &mut Tx<S>, mut a: Vec<F128>, mut b: Vec<F128>, mut c: Vec<F128>, tau: &[F128]) -> (Vec<F128>, [F128; 3]) {
    let mut claim = F128::ZERO;
    let mut rs = Vec::with_capacity(tau.len());
    for i in 0..tau.len() {
        let eqt = eq_table(&tau[i + 1..]);
        let [c0, c1, c2] = psum(a.len() / 2, |lo, hi| {
            let mut s = [F128::ZERO; 3];
            // R6: eight pairs at a time in `F128x8`, the `eq` products summed unreduced (the same sums).
            let mid = if PACKED { lo + (hi - lo) / 8 * 8 } else { lo };
            let mut acc = [zero8(), zero8(), zero8()];
            for j in (lo..mid).step_by(8) {
                let (a0, a1) = pair8(a[2 * j..2 * j + 16].try_into().unwrap());
                let (b0, b1) = pair8(b[2 * j..2 * j + 16].try_into().unwrap());
                let (x0, x1) = pair8(c[2 * j..2 * j + 16].try_into().unwrap());
                let (da, db) = (a0 + a1, b0 + b1);
                let e = load8(&eqt, j);
                acc[0] ^= e.mul_unreduced(a0 * b0 + x0);
                acc[1] ^= e.mul_unreduced(da * b0 + a0 * db + x0 + x1);
                acc[2] ^= e.mul_unreduced(da * db);
            }
            for (s, acc) in s.iter_mut().zip(acc) {
                *s += acc.reduce();
            }
            for j in mid..hi {
                let (a0, a1, b0, b1, x0, x1) = (a[2 * j], a[2 * j + 1], b[2 * j], b[2 * j + 1], c[2 * j], c[2 * j + 1]);
                let (da, db) = (a0 + a1, b0 + b1);
                let e = eqt[j];
                s[0] += e * (a0 * b0 + x0);
                s[1] += e * (da * b0 + a0 * db + x0 + x1);
                s[2] += e * (da * db);
            }
            s
        });
        debug_assert_eq!(c0 + tau[i] * (c1 + c2), claim, "zerocheck round {i}");
        tx.send(c1);
        tx.send(c2);
        let r = tx.ground(G_ZERO);
        claim = poly_eval(&[c0, c1, c2], r);
        rs.push(r);
        fold(&mut a, r);
        fold(&mut b, r);
        fold(&mut c, r);
    }
    debug_assert_eq!(claim, a[0] * b[0] + c[0]);
    (rs, [a[0], b[0], c[0]])
}

/// Plain rounds of `Σ u(w)·s(w) = claim`, variables low first, message `c₀, c₂` (`c₁ = claim + c₂`), each with
/// `G(g)`; returns the point and `s̃(point)`.
fn product_sumcheck<S: Search>(tx: &mut Tx<S>, mut u: Vec<F128>, mut s: Vec<F128>, mut claim: F128, g: u32) -> (Vec<F128>, F128) {
    assert_eq!(u.len(), s.len());
    let n = u.len().trailing_zeros() as usize;
    let mut rs = Vec::with_capacity(n);
    for i in 0..n {
        let [c0, c2] = psum(u.len() / 2, |lo, hi| {
            let mut t = [F128::ZERO; 2];
            // R6: eight pairs at a time in `F128x8`, summed unreduced (the same sums).
            let mid = if PACKED { lo + (hi - lo) / 8 * 8 } else { lo };
            let mut acc = [zero8(), zero8()];
            for j in (lo..mid).step_by(8) {
                let (u0, u1) = pair8(u[2 * j..2 * j + 16].try_into().unwrap());
                let (s0, s1) = pair8(s[2 * j..2 * j + 16].try_into().unwrap());
                acc[0] ^= u0.mul_unreduced(s0);
                acc[1] ^= (u0 + u1).mul_unreduced(s0 + s1);
            }
            for (t, acc) in t.iter_mut().zip(acc) {
                *t += acc.reduce();
            }
            for j in mid..hi {
                let (u0, u1, s0, s1) = (u[2 * j], u[2 * j + 1], s[2 * j], s[2 * j + 1]);
                t[0] += u0 * s0;
                t[1] += (u0 + u1) * (s0 + s1);
            }
            t
        });
        let c1 = claim + c2;
        debug_assert_eq!(c0 + (c0 + c1 + c2), claim, "product sumcheck round {i}");
        tx.send(c0);
        tx.send(c2);
        let r = tx.ground(g);
        claim = poly_eval(&[c0, c1, c2], r);
        rs.push(r);
        fold(&mut u, r);
        fold(&mut s, r);
    }
    debug_assert_eq!(claim, u[0] * s[0]);
    (rs, s[0])
}

/// The coefficients (constant first) of the polynomial of degree `< n` through `(xs_i, ys_i)` (Newton's divided
/// differences; the `xs` distinct).
pub fn interpolate(xs: &[F128], ys: &[F128]) -> Vec<F128> {
    let n = xs.len();
    let mut d = ys.to_vec();
    for k in 1..n {
        for i in (k..n).rev() {
            d[i] = (d[i] + d[i - 1]) * (xs[i] + xs[i - k]).inv();
        }
    }
    // Horner on the Newton form: p = d_{n-1}; p = p·(X − x_k) + d_k
    let mut p = vec![F128::ZERO; n];
    for k in (0..n).rev() {
        // p ← p·(X + x_k) + d_k
        let mut q = vec![F128::ZERO; n];
        for (j, &c) in p.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            if j + 1 < n {
                q[j + 1] += c;
            }
            q[j] += c * xs[k];
        }
        q[0] += d[k];
        p = q;
    }
    p
}

// ------------------------------------------------------------------------------------- accOut from a signed proof

/// Where §6.4a sits in a proof of `P18` (FORMAT6 §6's fixed schedule, from `fs6::schedule::fixed_parts`): its first
/// `BODY` byte (offset in `π`, `HDR` included) and the trace index of its first query (`q₀` and the seed are
/// entries 0 and 1).
pub fn typed_position() -> (usize, usize) {
    let sh = &fs6::params::P18;
    let (mut body, mut queries, mut pending, mut in_group) = (sh.hdr_len(), 2, 0, false);
    for (name, items) in fs6::schedule::fixed_parts(sh, true) {
        if name == "6.4ty" {
            return (body, queries);
        }
        let (t, p) = fs6::schedule::tally_from(sh, &items, pending, in_group).expect("the fixed schedule");
        body += t.body;
        queries += t.queries;
        pending = p;
        for it in &items {
            match it {
                fs6::schedule::Item::G(_) => in_group = true,
                fs6::schedule::Item::B => in_group = false,
                _ => {}
            }
        }
    }
    panic!("no §6.4a in the schedule")
}

/// `accOut = (line(accIn.pt → κ ‖ r_x ‖ r_y, t), h(t))` of a child proof, from its signed proof alone: `accIn` from
/// `HDR` (offset 120), `h₀ … h₄₃` from `BODY`, `κ`, `r_x`, `r_y`, `t` the `χ`s of its trace's answers (no check:
/// the parent's circuit and the child's `V_S` check them).
pub fn acc_out_from_proof(pi: &[u8], tr: &fs6::Trace) -> Acc {
    let (body, q) = typed_position();
    let acc_in = Acc::from_hdr(&(0..=PHI_VARS).map(|k| fs6::codec::get_e(&pi[120 + 16 * k..])).collect::<Vec<_>>());
    let answers: Vec<fs6::Digest> = tr[q..q + 84].iter().map(|(_, a)| *a).collect();
    acc_out_from_typed(&acc_in, &pi[body..], &answers)
}

/// [`acc_out_from_proof`] on §6.4a's own bytes: `body` from §6.4a's first byte on, `answers` its 84 draws' answers.
pub fn acc_out_from_typed(acc_in: &Acc, body: &[u8], answers: &[fs6::Digest]) -> Acc {
    use fs6::schedule::Item;
    let items = fs6::schedule::typed_phases(&fs6::params::P18);
    // the offset of the `E(44)` item (`h`) and the draws' order: τ (20), zerocheck (20), γ, wiring (21),
    // relayout (19), κ (2), t
    let (mut off, mut h_off, mut draws) = (0, None, 0);
    for it in &items {
        match *it {
            Item::E(n) => {
                if n == PHI_VARS + 1 {
                    h_off = Some(off);
                }
                off += 16 * n;
            }
            Item::G(_) => {
                off += 8;
                draws += 1;
            }
            _ => panic!("§6.4a has only E and G items"),
        }
    }
    assert_eq!((draws, answers.len()), (84, 84));
    let h_off = h_off.expect("h");
    let chi = |i: usize| F128::from_limbs(fs6::codec::chi(&answers[i]));
    let h: Vec<F128> = (0..=PHI_VARS).map(|k| F128::from_limbs(fs6::codec::get_e(&body[h_off + 16 * k..]))).collect();
    let (x0, y0) = (2 * X_VARS, 2 * X_VARS + 1);
    let r0 = y0 + Y_VARS + REC_VARS;
    let b: Vec<F128> = [chi(r0), chi(r0 + 1)].into_iter().chain((x0 - X_VARS..x0).map(chi)).chain((y0..y0 + Y_VARS).map(chi)).collect();
    let t = chi(r0 + 2);
    assert_eq!(r0 + 3, 84);
    Acc { pt: acc_in.pt.iter().zip(&b).map(|(&a, &b)| a + t * (a + b)).collect(), y: poly_eval(&h, t) }
}
