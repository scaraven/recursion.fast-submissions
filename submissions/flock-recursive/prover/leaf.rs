//! The leaf proof (`L32`, `P30`-leaf; blueprint rev. 3.9 §1.1, §2.3, A.3, A.4, A.9): prover and
//! native verifier, phase for phase in A.4's item order, `π` in A.3's eighteen fields.
//!
//! Phases (one item sequence for every kind, sized by `m* = 32`; a smaller `m` fills it with
//! dummies, the node-only phases Lr and E are zero for a leaf): seed, stmt, cap₀; **Z** (Z1 point,
//! Z2 univariate skip `P^z ‖ P^{ab}`, Z3 `26` degree-3 rounds of `eq(r,·)·a_λ·b_λ` ("skipping c",
//! rev. 3.8), Z end `â ‖ b̂`; the c-claim `ẑ(r, λ) = P^z*(λ)` goes to ring switching); **Lc** (α, 14
//! degree-2 rounds on the chain kind's folded column, L3 the 8 per-kind values, β); **Sh** (τ, θ,
//! κ_s; one 28-round sumcheck: block rounds, then 10 collapse rounds over the positions `< 1024`);
//! Lr (zero); **RS** (`J_z = 4` claims' slices, `r″`, κ; `v_RS = Σ κ^j T_j` with `Φ_{r″}`); E (zero);
//! B′; **P** (Ligerito, `ligerito.rs`). The verifier runs every check as a flag and asks every item
//! whatever the proof (as `gen` does); the finals (A.9) follow the skeleton.

use crate::blake2s::{leaf_stmt, Digest};
use crate::circuit::Circuit;
use crate::field::{FAcc, F, K};
use crate::lincheck;
use crate::mle::{eq_at_int, eq_f, eq_table, shift_mle};
use crate::oracle::Oracle;
use crate::params::{self as pp, leaf_kind_byte, M_STAR};
use crate::ringswitch;
use crate::skipdom::{lagrange_weights, skip};
use crate::sumcheck::{coeffs_f, eval2_f, fold_f, prove_pairs};
use crate::transcript::{Fs, ItemRec, Reader, Writer};
use crate::witness::Witness;
use crate::zerocheck;
use crate::{ligerito, par};
use std::time::Instant;

/// Phase timings of one proof (seconds).
#[derive(Default, Debug, Clone)]
pub struct Times {
    pub phases: Vec<(&'static str, f64)>,
}
impl Times {
    fn mark(&mut self, name: &'static str, t: &mut Instant) {
        if std::env::var_os("FLOCK_VERBOSE").is_some() {
            eprintln!("phase {name} {:.3}", t.elapsed().as_secs_f64());
        }
        self.phases.push((name, t.elapsed().as_secs_f64()));
        *t = Instant::now();
    }
    pub fn total(&self) -> f64 {
        self.phases.iter().map(|x| x.1).sum()
    }
    pub fn report(&self) -> String {
        self.phases.iter().map(|(n, s)| format!("{n}={s:.3}")).collect::<Vec<_>>().join(" ")
    }
}

/// `hdr = kindByte ‖ m ‖ 0^14 ‖ pub` (§1.1; a leaf's `pub` is its start `s`).
pub fn header(m: usize, s: &Digest) -> Vec<u8> {
    let mut h = vec![0u8; pp::HDR_LEN];
    h[0] = leaf_kind_byte(m);
    h[1] = m as u8;
    h[16..48].copy_from_slice(s);
    h
}

/// `stmt = tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64` (§1.1, the statement hash's padded message blocks).
pub fn stmt_bytes(n: u64, h: &Digest) -> Vec<u8> {
    let mut v = vec![0u8; 128];
    v[0] = crate::blake2s::TAG_LEAF;
    v[1..33].copy_from_slice(h);
    v[33..41].copy_from_slice(&n.to_le_bytes());
    v
}

/// The packed polynomial: the witness words as F elements (`f[y]` = bits `128y … 128y + 127`).
pub fn packed(z: &[u64]) -> &[F] {
    unsafe { std::slice::from_raw_parts(z.as_ptr() as *const F, z.len() / 2) }
}

/// `P^e(σ) = Σ_{p ∈ E, p mod 64 = σ} eq(r_hi, ⌊p/64⌋)` on `S` (`Σ_blk eq(r_blk, ·) = 1`).
fn pe_on_s(r_hi: &[F]) -> [F; 64] {
    let mut pe = [F::ZERO; 64];
    for &p in crate::circuit::e_positions() {
        pe[p & 63] += eq_at_int(r_hi, (p >> 6) as u64);
    }
    pe
}

/// **Z2's values** (`targetS`, `lagrangeS vals λ pe`, rev. 3.8): the message is `P^z` on `Λ` (64)
/// then `P^{ab}` on `Λ₀ … Λ₆₂` (63); `P^z*(λ)` by Lagrange on `Λ`; `P^{ab}|_S := P^z|_S + P^e|_S`,
/// `P^{ab}*(λ)` through the 127 nodes `S ∪ Λ₀…₆₂`. Returns `(P^{ab}*(λ), P^z*(λ))`: Z3's first claim
/// and the c-claim `ẑ(r, λ)`.
pub fn z2_value(pz: &[F], pab: &[F], r: &[F], lambda: F) -> (F, F) {
    assert_eq!((pz.len(), pab.len()), (64, 63));
    let sk = skip();
    let wl = lagrange_weights(&sk.l_pts, lambda);
    let mut pzl = F::ZERO;
    for i in 0..64 {
        pzl += wl[i] * pz[i];
    }
    let pe = pe_on_s(&r[..8]);
    let mut vals = vec![F::ZERO; 127];
    for sg in 0..64 {
        let mut v = F::ZERO;
        for i in 0..64 {
            v += pz[i].mulb(sk.phi8[sk.ms[sg][i] as usize]);
        }
        vals[sg] = v + pe[sg];
    }
    vals[64..].copy_from_slice(pab);
    let w = lagrange_weights(&sk.sl_pts[..127], lambda);
    let mut pabl = F::ZERO;
    for i in 0..127 {
        pabl += w[i] * vals[i];
    }
    (pabl, pzl)
}

/// `eq(θ, σ)` for the 256 slot positions `σ` of a digest (θ has 10 coordinates; `σ < 256`).
fn theta_eq(theta: &[F]) -> Vec<F> {
    let mut e = eq_table(theta);
    e.truncate(256);
    e
}

/// The θ byte tables: `T[p][v] = Σ_{i: v_i} eq(θ, 8p + i)` (32 × 256).
fn theta_tables(eq_theta: &[F]) -> Vec<F> {
    let mut t = vec![F::ZERO; 32 * 256];
    for p in 0..32 {
        for v in 1..256usize {
            let low = v & v.wrapping_neg();
            t[p * 256 + v] = t[p * 256 + (v ^ low)] + eq_theta[8 * p + low.trailing_zeros() as usize];
        }
    }
    t
}

/// `Σ_{σ<256} eq(θ, σ) z[blk, base + σ]` for every block (`base` a multiple of 8).
fn slot_collapse(z: &[u64], t: &[F], base: usize) -> Vec<F> {
    let bytes = Witness::bytes(z);
    let nb = z.len() / 256;
    par::collect_vec(nb, 1 << 10, |b| {
        let o = b * 2048 + base / 8;
        let mut acc = F::ZERO;
        for p in 0..32 {
            acc += t[p * 256 + bytes[o + p] as usize];
        }
        acc
    })
}

/// `Z(j) = Σ_blk eq(τ, blk) z[blk, j]` for `j < 64·words` (by blocks, F per set bit).
fn partial_fold_prefix(z: &[u64], tau: &[F], words: usize) -> Vec<F> {
    let e = eq_table(tau);
    let nb = z.len() / 256;
    let parts = par::map_chunks(nb, 64, |lo, hi| {
        let mut acc = vec![F::ZERO; 64 * words];
        for b in lo..hi {
            let w = e[b];
            for wi in 0..words {
                let mut x = z[b * 256 + wi];
                while x != 0 {
                    let t = x.trailing_zeros() as usize;
                    acc[64 * wi + t] += w;
                    x &= x - 1;
                }
            }
        }
        acc
    });
    let mut out = vec![F::ZERO; 64 * words];
    for p in parts {
        for i in 0..out.len() {
            out[i] += p[i];
        }
    }
    out
}

/// The slot weights of the collapse over the positions `< 1024`: `Out` (`h_out`, 256…511) and `In`
/// (the chain block's `d`, 520…775), `slotW_s(θ, pos) = Σ_σ eq(θ, σ)[pos = base_s + σ]`.
fn slot_weights(eq_theta: &[F]) -> (Vec<F>, Vec<F>) {
    let mut wo = vec![F::ZERO; 1024];
    let mut wi = vec![F::ZERO; 1024];
    for k in 0..256 {
        wo[pp::OUT_BASE + k] = eq_theta[k];
        wi[pp::D_BASE + k] = eq_theta[k];
    }
    (wo, wi)
}

/// `Σ_{σ<256} eq(θ, σ) bit_σ(d)`.
fn digest_mle(d: &[u8], eq_theta: &[F]) -> F {
    let mut s = F::ZERO;
    for j in 0..256 {
        if (d[j / 8] >> (j % 8)) & 1 == 1 {
            s += eq_theta[j];
        }
    }
    s
}

fn dot(a: &[F], b: &[F]) -> F {
    let mut acc = FAcc::default();
    for (x, y) in a.iter().zip(b.iter()) {
        acc.mac(*x, *y);
    }
    acc.reduce()
}

/// RS claim 0's inner weights (Z's quirky claim `ẑ(r, λ)`, `eqZ λ ρ₁`): `w_(σ,b) = L^S_σ(λ)
/// eq(ρ₁, b)`, `v = σ + 64 b` (bit 6's coordinate is the pinned `ρ₁ = r₀`, rev. 3.9).
fn claim_weights_z(rp0: F, lambda: F) -> Vec<F> {
    let l = lagrange_weights(&skip().s_pts, lambda);
    let mut w = vec![F::ZERO; 128];
    for sg in 0..64 {
        w[sg] = l[sg] * (F::ONE + rp0);
        w[64 + sg] = l[sg] * rp0;
    }
    w
}

/// The packed (outer) points of the leaf's RS claims (A.9 `finRS`): 0, Z's `ẑ(r, λ)`: `r₁ …`
/// (`ρ₂ … ρ₇, r_out`); 1, Lc's `β`-batched claim (a leaf: `ẑ(r_k, r′_blk)`): `(r_k,7…13, r′_blk)`;
/// 2, Sh's one claim `ẑ(r_pos, r_blk)`: `(r_pos,7…9, 0⁴, r_blk)`.
fn claim_points(r: &[F], rp: &[F], tl: &[F], tpp: &[F], taup: &[F]) -> [Vec<F>; 3] {
    let a: Vec<F> = r[1..].to_vec();
    let mut b: Vec<F> = tl[7..14].to_vec();
    b.extend_from_slice(&rp[8..]);
    let mut c: Vec<F> = tpp[7..10].to_vec();
    c.extend_from_slice(&[F::ZERO; 4]);
    c.extend_from_slice(taup);
    [a, b, c]
}

/// `Σ_{y_in} eq(hi_in, y_in) Z(128 y_in + v)` for `v < 128` (a claim's partials from a partial fold).
fn partials_from_fold(z: &[F], hi_in: &[F]) -> Vec<F> {
    let e = eq_table(hi_in);
    let mut sv = vec![F::ZERO; 128];
    for (yi, ey) in e.iter().enumerate() {
        crate::simd::axpy(&mut sv, &z[128 * yi..128 * yi + 128], *ey);
    }
    sv
}

/// `n` dummy rounds of `bytes`-byte messages: zero message, squeeze ignored.
fn dummy_rounds(wr: &mut Writer, f: usize, n: usize, bytes: usize) {
    let z = vec![0u8; bytes];
    for _ in 0..n {
        wr.send(f, &z);
        wr.fs.squeeze();
    }
}

/// A leaf of `m` committed bits proves `chainEnd s n = h` (`n = 2^(m−14)`); `c = leafStmt h n`.
pub fn leaf_c(s: &Digest, m: usize) -> Digest {
    let n = pp::leaf_n(m);
    leaf_stmt(&crate::blake2s::chain_end(s, n), n)
}

/// The leaf prover: `π` (`piSize` bytes) and the phase timings. `o` answers every query.
pub fn prove(o: &dyn Oracle, circ: &Circuit, vk: &Digest, s: &Digest, m: usize) -> (Vec<u8>, Times) {
    prove_logged(o, circ, vk, s, m, false).0
}

/// `prove`, and the Fiat–Shamir items the prover asked (if `log`).
pub fn prove_logged(o: &dyn Oracle, circ: &Circuit, vk: &Digest, s: &Digest, m: usize, log: bool) -> ((Vec<u8>, Times), Option<Vec<ItemRec>>) {
    assert!((25..=M_STAR).contains(&m), "leaf shapes m = 25 … 32");
    let mut tm = Times::default();
    let mut t = Instant::now();
    let n = pp::leaf_n(m);
    let w = crate::witness::leaf_witness_fast(circ, s, m);
    tm.mark("witness", &mut t);
    let c = leaf_stmt(&w.h, n);
    let hdr = header(m, s);
    let f = packed(&w.z);
    let c0 = ligerito::commit0(o, f, m);
    tm.mark("commit0", &mut t);
    let mut wr = Writer::new(Fs::seed(o, vk, &c, &hdr, log), &hdr);
    wr.fs.phase = "stmt";
    wr.send(pp::F_STMT, &stmt_bytes(n, &w.h));
    wr.fs.phase = "cap0";
    let capb = ligerito::cap_slot(0, c0.tree.cap());
    wr.send(pp::F_CAPS, &capb);

    // ---- Z
    let sk = skip();
    wr.fs.phase = "Z1";
    let co = wr.fs.coords(pp::Z1_SQ);
    let r_out = &co[..m - 13];
    let mut r: Vec<F> = sk.rho.to_vec();
    r.extend_from_slice(r_out);
    let (ab, bb, zb) = (Witness::bytes(&w.a), Witness::bytes(&w.b), Witness::bytes(&w.z));
    let r1 = zerocheck::round1(ab, bb, zb, r_out);
    let pz = zerocheck::pz_on_lambda(&r1);
    let mut msg = pz.to_vec();
    msg.extend_from_slice(&r1.pab[..63]);
    msg.push(F::ZERO);
    wr.fs.phase = "Z2";
    wr.send_f(pp::F_Z2, &msg);
    let lambda = wr.fs.chal_f();
    let (mut claim, pz_l) = z2_value(&pz, &r1.pab[..63], &r, lambda);
    // the c-claim ẑ(r, λ): its slices from round 1's banks (bank_b = eq(ρ₁, b)·Σ_y eq(r₁…, y) z(y, ·))
    let (i0, i1) = ((F::ONE + sk.rho[0]).inv(), sk.rho[0].inv());
    let mut s0v = vec![F::ZERO; 128];
    for sg in 0..64 {
        s0v[sg] = r1.bank[0][sg] * i0;
        s0v[64 + sg] = r1.bank[1][sg] * i1;
    }
    debug_assert_eq!(dot(&claim_weights_z(r[0], lambda), &s0v), pz_l);
    tm.mark("zc_round1", &mut t);
    // Z3: Gruen's form on eq(r,·)·a_λ·b_λ; the message is g's coefficients, g(X) = P·(1 + r_k + X)·H(X)
    wr.fs.phase = "Z3";
    let tabs = zerocheck::fold_tables(lambda);
    let mut pref = F::ONE;
    let mut sz = Vec::with_capacity(m - 6);
    let (mut ta, mut tb) = (Vec::new(), Vec::new());
    for k in 0..m - 6 {
        let (h1, hi) = if k == 0 { zerocheck::round_x6(&tabs, ab, bb, &r[1..]) } else { zerocheck::round_tab(&ta, &tb, &r[k + 1..]) };
        let h0 = zerocheck::h0_from_claim(claim, r[k], h1);
        wr.send_f(pp::F_Z3, &zerocheck::zc_coeffs(pref, r[k], h0, h1, hi));
        let x = wr.fs.chal_f();
        claim = eval2_f([h0, h1, hi], x);
        pref *= F::ONE + r[k] + x;
        sz.push(x);
        if k == 0 {
            ta = zerocheck::fold_x6(&tabs, ab, x);
            tb = zerocheck::fold_x6(&tabs, bb, x);
            tm.mark("zc_round2", &mut t);
        } else {
            ta = fold_f(&ta, x);
            tb = fold_f(&tb, x);
        }
    }
    dummy_rounds(&mut wr, pp::F_Z3, pp::Z3_ROUNDS - (m - 6), 48);
    let (va, vb) = (ta[0], tb[0]);
    debug_assert_eq!(claim, va * vb);
    drop((ta, tb));
    wr.fs.phase = "Zend";
    wr.send_f(pp::F_ZEND, &[va, vb]);
    tm.mark("zc_tail", &mut t);

    // ---- Lc
    wr.fs.phase = "L1";
    let alpha = wr.fs.chal_f();
    wr.fs.phase = "L2";
    let eta = lincheck::eta(circ, lambda, &sz[..8], alpha);
    let zf = lincheck::partial_fold(&w.z, &sz[8..]);
    let zf_keep = zf.clone();
    let (tl, fin) = prove_pairs(vec![(eta, zf)], &mut |g| {
        wr.send_f(pp::F_L2, &coeffs_f(g));
        wr.fs.chal_f()
    });
    let v_chain = fin[0].1;
    wr.fs.phase = "L3";
    let mut vk7 = vec![F::ZERO; pp::L3_KINDS];
    vk7[0] = v_chain;
    wr.send_f(pp::F_L2, &vk7);
    wr.fs.phase = "L3β";
    let _beta = wr.fs.chal_f();
    tm.mark("lincheck", &mut t);

    // ---- Sh: block rounds, then the collapse, one sumcheck
    wr.fs.phase = "S1";
    let co = wr.fs.coords(pp::S1_SQ);
    let (tau, theta, kap_s) = (&co[..m - 14], &co[pp::S1_THETA..pp::S1_THETA + pp::THETA_LEN], co[pp::S1_KAPPA]);
    let eqt = theta_eq(theta);
    let tt = theta_tables(&eqt);
    let out = slot_collapse(&w.z, &tt, pp::OUT_BASE);
    let inn = slot_collapse(&w.z, &tt, pp::D_BASE);
    let e1 = eq_table(tau);
    let mut e2 = vec![F::ZERO; e1.len()];
    e2[0] = kap_s;
    e2[1..].copy_from_slice(&e1[..e1.len() - 1]);
    wr.fs.phase = "S2";
    let (taup, fin) = prove_pairs(vec![(e1, out), (e2, inn)], &mut |g| {
        wr.send_f(pp::F_S2, &coeffs_f(g));
        wr.fs.chal_f()
    });
    let (wout_b, win_b) = (fin[0].0, fin[1].0);
    let (wo, wi) = slot_weights(&eqt);
    let wsl: Vec<F> = wo.iter().zip(wi.iter()).map(|(a, b)| wout_b * *a + win_b * *b).collect();
    let zs = partial_fold_prefix(&w.z, &taup, 16);
    let zs_keep = zs.clone();
    let (tpp, _) = prove_pairs(vec![(wsl, zs)], &mut |g| {
        wr.send_f(pp::F_S2, &coeffs_f(g));
        wr.fs.chal_f()
    });
    dummy_rounds(&mut wr, pp::F_S2, pp::S2_ROUNDS - (m - 4), 48);
    tm.mark("shift", &mut t);

    if std::env::var_os("FLOCK_NODE_SHAPE").is_some() {
        if crate::nodeshape::preload().is_some() {
            // the node's E2, E4 and Lr on the dumped node circuit (timing only)
            let (e2, e4, lr) = crate::nodeshape::run(f, F::from_bytes(&wr.fs.st[..16])).unwrap();
            tm.phases.push(("node_E2", e2));
            tm.phases.push(("node_E4", e4));
            tm.phases.push(("node_Lr", lr));
            t = Instant::now();
        } else {
            node_surrogate(f, &mut wr.fs);
            tm.mark("node_extra", &mut t);
        }
    }

    // ---- Lr (node only): zero for a leaf
    wr.fs.phase = "Lr1";
    wr.fs.squeezes(pp::LR1_SQ);
    wr.fs.phase = "Lr2";
    dummy_rounds(&mut wr, pp::F_LR, pp::LR_ROUNDS, 48);
    wr.fs.phase = "Lrend";
    wr.send(pp::F_LREND, &[0u8; 48]);
    wr.fs.phase = "Lr3";
    wr.fs.squeeze();

    // ---- E (node only): zero for a leaf (rev. 3.13: E before RS; E4 the 23-round lincheck)
    wr.fs.phase = "E1";
    wr.fs.squeezes(pp::E1_SQ);
    wr.fs.phase = "E2";
    dummy_rounds(&mut wr, pp::F_E, pp::E2_ROUNDS, 48);
    wr.fs.phase = "Eend";
    wr.send(pp::F_EEND, &[0u8; 48]);
    wr.fs.phase = "E3";
    wr.fs.squeeze();
    wr.fs.phase = "E4";
    dummy_rounds(&mut wr, pp::F_E, pp::E4_ROUNDS, 48);
    wr.fs.phase = "E4end";
    wr.send(pp::F_E, &[0u8; pp::E4END_LEN]);

    // ---- RS: J_z = 4 claims' slices (a leaf's fourth, Lr's, is zero)
    let his = claim_points(&r, &sz, &tl, &tpp, &taup);
    let s1v = partials_from_fold(&zf_keep, &tl[7..14]);
    let s2v = partials_from_fold(&zs_keep, &tpp[7..10]);
    debug_assert_eq!(s1v, ringswitch::partials(&w.z, &his[1]));
    debug_assert_eq!(s2v, ringswitch::partials(&w.z, &his[2]));
    debug_assert_eq!(dot(&eq_table(&tl[..7]), &s1v), v_chain);
    let mut msg = s0v.clone();
    msg.extend_from_slice(&s1v);
    msg.extend_from_slice(&s2v);
    msg.extend_from_slice(&[F::ZERO; 128]);
    wr.fs.phase = "RS0";
    wr.send_f(pp::F_RS0, &msg);
    wr.fs.phase = "RS1";
    let ch = wr.fs.coords(pp::RS1_SQ);
    let (rpp, kap) = (&ch[..7], ch[7]);
    let parts = [&s0v, &s1v, &s2v];
    let (coef, v_rs) = rs_batch(&parts, rpp, kap);
    let wt = ringswitch::weight_table(&[(&his[0][..], coef[0]), (&his[1][..], coef[1]), (&his[2][..], coef[2])], rpp);
    tm.mark("ringswitch", &mut t);
    wr.fs.phase = "B'";
    wr.fs.squeeze();

    // ---- P
    ligerito::prove(m, f, wt, v_rs, c0, &mut wr);
    tm.mark("ligerito", &mut t);
    let log = wr.fs.log.take();
    ((wr.finish(), tm), log)
}

/// The RS batching: the coefficients `κ^j` and `v_RS = Σ_j κ^j T_j`, `T_j = Σ_v b_v Φ_{r″}(s_{j,v})`.
fn rs_batch(parts: &[&Vec<F>], rpp: &[F], kap: F) -> (Vec<F>, F) {
    let mut coef = Vec::with_capacity(parts.len());
    let mut c = F::ONE;
    let mut v = F::ZERO;
    for s in parts {
        coef.push(c);
        v += c * ringswitch::switched(s, rpp);
        c *= kap;
    }
    (coef, v)
}

/// Timing surrogate of the node's element phases (P2 prototype, not part of the proof; rev. 3
/// §2.3 E, Lr): E1, a degree-3 zerocheck over `2^20` rows (`A·B − C`); Lr, the same over `2^15`
/// rows; E2 batched into the Ligerito weight (rev. 3.4), one pass over the packed polynomial.
/// Challenges are drawn from a local hash chain, not the transcript.
fn node_surrogate(f: &[F], fs: &mut Fs) {
    let st = fs.st;
    let mut x = F::from_bytes(&st[..16]);
    let mut next = || {
        x = x * x + F::new(0x9E37_79B9_7F4A_7C15, 3);
        x
    };
    for rows in [(1usize << 20).min(f.len() / 4), 1 << 15] {
        let lg = rows.trailing_zeros() as usize;
        let (mut a, mut b, mut c): (Vec<F>, Vec<F>, Vec<F>) = (f[..rows].to_vec(), f[rows..2 * rows].to_vec(), f[2 * rows..3 * rows].to_vec());
        let r: Vec<F> = (0..lg).map(|_| next()).collect();
        for k in 0..lg {
            let (h1, hi) = zerocheck::round_tab(&a, &b, &r[k + 1..]);
            let cs = crate::simd::dot(&c, &c[..]);
            std::hint::black_box((h1, hi, cs));
            let s = next();
            a = fold_f(&a, s);
            b = fold_f(&b, s);
            c = fold_f(&c, s);
        }
    }
    let t = Instant::now();
    let mut w: Vec<F> = crate::par::uninit_vec(f.len());
    crate::par::for_each_chunk_mut(&mut w, 1 << 14, |off, ch| {
        for (i, x) in ch.iter_mut().enumerate() {
            *x = f[off + i] + F::new((off + i) as u64, 1);
        }
    });
    std::hint::black_box(&w);
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("  node_extra E2 {:.3}", t.elapsed().as_secs_f64());
    }
}

/// One F sumcheck round as `gen`'s `roundOpsF` checks it; returns the challenge. A real round of
/// degree 2 checks `c₁ + c₂ = claim`; degree 3 completes `c₃ = claim + c₁ + c₂`; the next claim is
/// `g(r)`. A dummy round's message must be zero and keeps the claim.
fn v_round(rd: &mut Reader, f: usize, deg: usize, real: bool, claim: &mut F) -> F {
    let c = rd.recv_f(f, 3);
    let r = rd.fs.chal_f();
    if !real {
        rd.check(c.iter().all(|x| x.is_zero()));
        return r;
    }
    if deg == 3 {
        let c3 = *claim + c[1] + c[2];
        *claim = c[0] + r * (c[1] + r * (c[2] + r * c3));
    } else {
        rd.check(c[1] + c[2] == *claim);
        *claim = c[0] + r * (c[1] + r * c[2]);
    }
    r
}

/// `n` rounds from `claim`: the challenges of the real ones (the first `real`).
fn v_rounds(rd: &mut Reader, f: usize, deg: usize, n: usize, real: usize, claim: &mut F) -> Vec<F> {
    let mut rs = Vec::with_capacity(real);
    for j in 0..n {
        let r = v_round(rd, f, deg, j < real, claim);
        if j < real {
            rs.push(r);
        }
    }
    rs
}

/// The native verifier `V vk c π` of a leaf kind (`'L'`, `m = 32`; `'P'`, `m = 30`; and the native
/// test shapes `'P'`, `m = 25 … 29`).
pub fn verify(o: &dyn Oracle, circ: &Circuit, vk: &Digest, c: &Digest, pi: &[u8]) -> bool {
    verify_logged(o, circ, vk, c, pi, false).0
}

/// `verify`, and the items asked (if `log`). A `π` of another length, or with another kind byte or
/// `m`, is rejected with no query; otherwise every item of A.4 is asked whatever `π` holds.
pub fn verify_logged(o: &dyn Oracle, circ: &Circuit, vk: &Digest, c: &Digest, pi: &[u8], log: bool) -> (bool, Option<Vec<ItemRec>>) {
    if pi.len() != pp::PI_SIZE {
        return (false, None);
    }
    let m = pi[1] as usize;
    if !(25..=M_STAR).contains(&m) || pi[0] != leaf_kind_byte(m) {
        return (false, None);
    }
    let hdr = &pi[..48];
    let mut rd = Reader::new(Fs::seed(o, vk, c, hdr, log), pi);
    rd.check(hdr[2..16].iter().all(|&x| x == 0));
    let s: Digest = hdr[16..48].try_into().unwrap();
    rd.fs.phase = "stmt";
    let st = rd.recv(pp::F_STMT, 128);
    let h: Digest = st[1..33].try_into().unwrap();
    let n = u64::from_le_bytes(st[33..41].try_into().unwrap());
    rd.check(st[0] == crate::blake2s::TAG_LEAF && n == pp::leaf_n(m) && st[41..].iter().all(|&x| x == 0));
    rd.check(leaf_stmt(&h, n) == *c);
    rd.fs.phase = "cap0";
    let cap0 = ligerito::read_cap_slot(&mut rd, 0, ligerito::cap_log(m, 0));

    // ---- Z
    let sk = skip();
    rd.fs.phase = "Z1";
    let co = rd.fs.coords(pp::Z1_SQ);
    let mut r: Vec<F> = sk.rho.to_vec();
    r.extend_from_slice(&co[..m - 13]);
    rd.fs.phase = "Z2";
    let msg = rd.recv_f(pp::F_Z2, 128);
    rd.check(msg[127].is_zero());
    let lambda = rd.fs.chal_f();
    let (mut c_z, pz_l) = z2_value(&msg[..64], &msg[64..127], &r, lambda);
    rd.fs.phase = "Z3";
    let rp = v_rounds(&mut rd, pp::F_Z3, 3, pp::Z3_ROUNDS, m - 6, &mut c_z);
    rd.fs.phase = "Zend";
    let v = rd.recv_f(pp::F_ZEND, 2);
    let (va, vb) = (v[0], v[1]);

    // ---- Lc (free first claim, bound by finLc (i))
    rd.fs.phase = "L1";
    let alpha = rd.fs.chal_f();
    rd.fs.phase = "L2";
    let mut c_l = va + alpha * vb;
    let tl = v_rounds(&mut rd, pp::F_L2, 2, pp::L2_ROUNDS, pp::L2_ROUNDS, &mut c_l);
    rd.fs.phase = "L3";
    let vkind = rd.recv_f(pp::F_L2, pp::L3_KINDS);
    rd.fs.phase = "L3β";
    let beta = rd.fs.chal_f();

    // ---- Sh (free first claim, bound by finSh (i))
    rd.fs.phase = "S1";
    let co = rd.fs.coords(pp::S1_SQ);
    let (tau, theta, kap_s) = (&co[..m - 14], &co[pp::S1_THETA..pp::S1_THETA + pp::THETA_LEN], co[pp::S1_KAPPA]);
    let eqt = theta_eq(theta);
    let ones = (1u64 << (m - 14)) - 1;
    let mut c_s = eq_at_int(tau, ones) * digest_mle(&h, &eqt) + kap_s * digest_mle(&s, &eqt);
    rd.fs.phase = "S2";
    let rs2 = v_rounds(&mut rd, pp::F_S2, 2, pp::S2_ROUNDS, m - 4, &mut c_s);
    let (taup, tpp) = (&rs2[..m - 14], &rs2[m - 14..]);

    // ---- Lr (node only): zero
    let mut zero = F::ZERO;
    rd.fs.phase = "Lr1";
    rd.fs.squeezes(pp::LR1_SQ);
    rd.fs.phase = "Lr2";
    v_rounds(&mut rd, pp::F_LR, 3, pp::LR_ROUNDS, 0, &mut zero);
    rd.fs.phase = "Lrend";
    let e = rd.recv(pp::F_LREND, 48);
    rd.check(e.iter().all(|&x| x == 0));
    rd.fs.phase = "Lr3";
    rd.fs.squeeze();

    // ---- E (node only): zero (E before RS, rev. 3.13)
    rd.fs.phase = "E1";
    rd.fs.squeezes(pp::E1_SQ);
    rd.fs.phase = "E2";
    v_rounds(&mut rd, pp::F_E, 3, pp::E2_ROUNDS, 0, &mut zero);
    rd.fs.phase = "Eend";
    let e = rd.recv(pp::F_EEND, 48);
    rd.check(e.iter().all(|&x| x == 0));
    rd.fs.phase = "E3";
    rd.fs.squeeze();
    rd.fs.phase = "E4";
    v_rounds(&mut rd, pp::F_E, 2, pp::E4_ROUNDS, 0, &mut zero);
    rd.fs.phase = "E4end";
    let e4 = rd.recv(pp::F_E, pp::E4END_LEN);
    // finE (v): f̂(r′) = α₄ (zero for a leaf) and the zero half
    rd.check(e4.iter().all(|&x| x == 0));

    // ---- RS
    rd.fs.phase = "RS0";
    let sv = rd.recv_f(pp::F_RS0, pp::RS_CLAIMS * 128);
    rd.fs.phase = "RS1";
    let ch = rd.fs.coords(pp::RS1_SQ);
    let (rpp, kap) = (ch[..7].to_vec(), ch[7]);
    rd.fs.phase = "B'";
    rd.fs.squeeze();

    // ---- the finals (A.9), on the transcript values
    // finRS: the claims' values from the slices (the column check); a leaf's fourth (Lr) is zero
    let part = |j: usize| &sv[128 * j..128 * (j + 1)];
    let az = dot(&claim_weights_z(r[0], lambda), part(0));
    let al = dot(&eq_table(&tl[..7]), part(1));
    let ash = dot(&eq_table(&tpp[..7]), part(2));
    rd.check(part(3).iter().all(|x| x.is_zero()));
    let parts: Vec<Vec<F>> = (0..3).map(|j| part(j).to_vec()).collect();
    let (coef, v_rs) = rs_batch(&parts.iter().collect::<Vec<_>>(), &rpp, kap);
    // finZ: eq(r, r′)·â·b̂ = c_Z; the c-claim α_Z = P^z*(λ)
    rd.check(eq_f(&r, &rp) * va * vb == c_z);
    rd.check(az == pz_l);
    // finLc: (ii) the walk with the chain kind's rows, (iii) Σ β^i v_i = Lc's RS value
    let eta = lincheck::eta(circ, lambda, &rp[..8], alpha);
    rd.check(c_l == vkind[0] * dot(&eta, &eq_table(&tl)));
    let mut vb_sum = F::ZERO;
    for v in vkind.iter().rev() {
        vb_sum = vb_sum * beta + *v;
    }
    rd.check(vb_sum == al);
    // finSh: c_Sh = (w_out + w_in)·ẑ_Sh (one claim, rev. 3.8)
    let (wo, wi) = slot_weights(&eqt);
    let ep = eq_table(tpp);
    let zeros = vec![F::ZERO; m - 14];
    let w_out = eq_f(tau, taup) * dot(&wo, &ep);
    let w_in = (shift_mle(tau, taup, F::ONE) + kap_s * eq_f(&zeros, taup)) * dot(&wi, &ep);
    rd.check(c_s == (w_out + w_in) * ash);

    // ---- P (finB′: Ligerito's first claim is v_RS; finP, finPf inside; Ŵ by rsWeight, 3 points)
    let his = claim_points(&r, &rp, &tl, tpp, taup);
    let w0 = |pt: &[K]| -> K { ringswitch::rs_weight(&[(&his[0][..], coef[0]), (&his[1][..], coef[1]), (&his[2][..], coef[2])], &rpp, pt) };
    ligerito::verify(m, &cap0, v_rs, &mut rd, &w0);
    assert!(rd.all_read());
    let log = rd.fs.log.take();
    (rd.ok, log)
}
