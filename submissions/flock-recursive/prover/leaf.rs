//! The leaf proof (blueprint rev. 2 §1.1, §2.3, §4.1) as P1 implements it: prover and native
//! verifier, phase for phase in the same order (P1-RESULT §4 lists every choice that differs from
//! rev. 2). Phases: commit; Z (skip + `m − 6` rounds); Lc (14 rounds); Sh + IO (block shift with
//! both endpoints, then a 10-round collapse of the two digest slots); R (three claims, batched into
//! the Ligerito weight); P (Ligerito, five levels).

use crate::blake2s::{leaf_stmt, Digest};
use crate::circuit::Circuit;
use crate::field::{FAcc, F, K};
use crate::lincheck;
use crate::mle::{eq_at_int, eq_f, eq_table, shift_mle};
use crate::oracle::Oracle;
use crate::params::{self, KIND_LEAF};
use crate::ringswitch;
use crate::skipdom::{lagrange_weights, skip};
use crate::sumcheck::{eval2_f, fold_f, prove_pairs};
use crate::transcript::{Fs, Reader, Writer};
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

pub fn header(m: usize, s: &Digest) -> Vec<u8> {
    let mut h = vec![0u8; params::HDR_LEN];
    h[0] = KIND_LEAF;
    h[1] = m as u8;
    h[16..48].copy_from_slice(s);
    h
}
pub fn stmt_fields(n: u64, h: &Digest) -> Vec<u8> {
    let mut v = Vec::with_capacity(48);
    v.extend_from_slice(&n.to_le_bytes());
    v.extend_from_slice(h);
    v.extend_from_slice(&[0u8; 8]);
    v
}

/// The packed polynomial: the witness words as F elements (`f[y]` = bits `128y … 128y + 127`).
pub fn packed(z: &[u64]) -> &[F] {
    unsafe { std::slice::from_raw_parts(z.as_ptr() as *const F, z.len() / 2) }
}

/// `(P^{ab}(λ), P^z(λ))` from the values on `Λ`: `P^z` by Lagrange on `Λ`; `P^{ab}` by Lagrange on
/// `S ∪ Λ` with `P^{ab}|_S = P^z|_S + P^e|_S` (`e` = the block's public target `E`).
pub fn skip_eval(pab: &[F], pz: &[F], r: &[F], lambda: F) -> (F, F) {
    let sk = skip();
    let wl = lagrange_weights(&sk.l_pts, lambda);
    let mut pzl = F::ZERO;
    for i in 0..64 {
        pzl += wl[i] * pz[i];
    }
    // P^z on S from its values on Λ (GF(2^8) Lagrange coefficients), plus P^e
    // P^e on S: Σ over the target's 1-positions p of eq(r₀…₇, ⌊p/64⌋) at σ = p mod 64
    let mut pe = [F::ZERO; 64];
    for &p in crate::circuit::e_positions() {
        pe[p & 63] += eq_at_int(&r[..8], (p >> 6) as u64);
    }
    let mut vals = vec![F::ZERO; 128];
    for sg in 0..64 {
        let mut v = F::ZERO;
        for i in 0..64 {
            v += pz[i].mulb(sk.phi8[sk.ms[sg][i] as usize]);
        }
        vals[sg] = v + pe[sg];
    }
    vals[64..].copy_from_slice(pab);
    let w = lagrange_weights(&sk.sl_pts, lambda);
    let mut pabl = F::ZERO;
    for i in 0..128 {
        pabl += w[i] * vals[i];
    }
    (pabl, pzl)
}

/// The θ byte tables: `T[p][v] = Σ_{i: v_i} eq(θ, 8p + i)` (32 × 256).
fn theta_tables(theta: &[F]) -> Vec<F> {
    let e = eq_table(theta);
    let mut t = vec![F::ZERO; 32 * 256];
    for p in 0..32 {
        for v in 1..256usize {
            let low = v & v.wrapping_neg();
            t[p * 256 + v] = t[p * 256 + (v ^ low)] + e[8 * p + low.trailing_zeros() as usize];
        }
    }
    t
}

/// `Σ_{j<256} eq(θ, j) z[blk, base + j]` for every block (`base` a multiple of 8).
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

/// `Z(j) = Σ_blk eq(τ, blk) z[blk, j]` for `j < 64·words` (by blocks, F per set bit, byte tables).
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

/// The inner weight of the slot collapse: `W(j) = [256 ≤ j < 512] eq(θ, j − 256) + μ [520 ≤ j <
/// 776] eq(θ, j − 520)` over `j < 1024`.
fn slot_weight(theta: &[F], mu: F) -> Vec<F> {
    let e = eq_table(theta);
    let mut w = vec![F::ZERO; 1024];
    for k in 0..256 {
        w[params::OUT_BASE + k] += e[k];
        w[params::D_BASE + k] += e[k] * mu;
    }
    w
}

fn digest_mle(d: &Digest, theta: &[F]) -> F {
    let e = eq_table(theta);
    let mut s = F::ZERO;
    for j in 0..256 {
        if (d[j / 8] >> (j % 8)) & 1 == 1 {
            s += e[j];
        }
    }
    s
}

/// The leaf prover: returns `π` and the phase timings. `o` answers every query (Merkle and FS).
pub fn prove(o: &dyn Oracle, circ: &Circuit, vk: &Digest, s: &Digest, m: usize) -> (Vec<u8>, Times) {
    let mut tm = Times::default();
    let mut t = Instant::now();
    let n = params::leaf_n(m);
    let w = crate::witness::leaf_witness_fast(circ, s, m);
    tm.mark("witness", &mut t);
    let c = leaf_stmt(&w.h, n);
    let hdr = header(m, s);
    let f = packed(&w.z);
    let c0 = ligerito::commit0(o, f, m);
    tm.mark("commit0", &mut t);
    let mut wr = Writer { fs: Fs::seed(o, vk, &c, &hdr), pi: hdr.clone() };
    wr.send(&stmt_fields(n, &w.h));
    let mut capb = Vec::new();
    for d in c0.tree.cap() {
        capb.extend_from_slice(d);
    }
    wr.send(&capb);

    // ---- Z
    let sk = skip();
    let r_out = wr.fs.chal_fs(m - 13);
    let mut r: Vec<F> = sk.rho.to_vec();
    r.extend_from_slice(&r_out);
    let (ab, bb, zb) = (Witness::bytes(&w.a), Witness::bytes(&w.b), Witness::bytes(&w.z));
    let r1 = zerocheck::round1(ab, bb, zb, &r_out);
    let pz = zerocheck::pz_on_lambda(&r1);
    let mut msg = r1.pab.to_vec();
    msg.extend_from_slice(&pz);
    wr.send_f(&msg);
    let lambda = wr.fs.chal_f();
    let (mut claim, pz_l) = skip_eval(&r1.pab, &pz, &r, lambda);
    tm.mark("zc_round1", &mut t);
    let tabs = zerocheck::fold_tables(lambda);
    let (h1, hi) = zerocheck::round_x6(&tabs, ab, bb, &r[1..]);
    let h0 = zerocheck::h0_from_claim(claim, r[0], h1);
    wr.send_f(&[h0, h1, hi]);
    let s1 = wr.fs.chal_f();
    claim = eval2_f([h0, h1, hi], s1);
    let mut sz = vec![s1];
    let mut ta = zerocheck::fold_x6(&tabs, ab, s1);
    let mut tb = zerocheck::fold_x6(&tabs, bb, s1);
    tm.mark("zc_round2", &mut t);
    for k in 1..m - 6 {
        let (h1, hi) = zerocheck::round_tab(&ta, &tb, &r[k + 1..]);
        let h0 = zerocheck::h0_from_claim(claim, r[k], h1);
        wr.send_f(&[h0, h1, hi]);
        let sk_ = wr.fs.chal_f();
        claim = eval2_f([h0, h1, hi], sk_);
        sz.push(sk_);
        ta = fold_f(&ta, sk_);
        tb = fold_f(&tb, sk_);
    }
    let (va, vb) = (ta[0], tb[0]);
    debug_assert_eq!(claim, va * vb);
    wr.send_f(&[va, vb]);
    tm.mark("zc_tail", &mut t);

    // ---- Lc
    let alpha = wr.fs.chal_f();
    let (s_in, s_out) = (&sz[..8], &sz[8..]);
    let eta = lincheck::eta(circ, lambda, s_in, alpha);
    let zf = lincheck::partial_fold(&w.z, s_out);
    let zf_keep = zf.clone();
    let (tl, fin) = prove_pairs(vec![(eta, zf)], &mut |g| {
        wr.send_f(&g);
        wr.fs.chal_f()
    });
    let vz = fin[0].1;
    wr.send_f(&[vz]);
    tm.mark("lincheck", &mut t);

    // ---- Sh + IO
    let ch = wr.fs.chal_fs(8 + (m - 14) + 1);
    let (theta, tau, kap_s) = (&ch[..8], &ch[8..8 + m - 14], ch[8 + m - 14]);
    let tt = theta_tables(theta);
    let out = slot_collapse(&w.z, &tt, params::OUT_BASE);
    let inn = slot_collapse(&w.z, &tt, params::D_BASE);
    let e1 = eq_table(tau);
    let mut e2 = vec![F::ZERO; e1.len()];
    e2[0] = kap_s;
    e2[1..].copy_from_slice(&e1[..e1.len() - 1]);
    let (taup, fin) = prove_pairs(vec![(e1, out), (e2, inn)], &mut |g| {
        wr.send_f(&g);
        wr.fs.chal_f()
    });
    let (vo, vi) = (fin[0].1, fin[1].1);
    wr.send_f(&[vo, vi]);
    let mu = wr.fs.chal_f();
    let zs = partial_fold_prefix(&w.z, &taup, 16);
    let zs_keep = zs.clone();
    let (tpp, fin) = prove_pairs(vec![(slot_weight(theta, mu), zs)], &mut |g| {
        wr.send_f(&g);
        wr.fs.chal_f()
    });
    let vc = fin[0].1;
    wr.send_f(&[vc]);
    tm.mark("shift_io", &mut t);

    if std::env::var_os("FLOCK_NODE_SHAPE").is_some() {
        node_surrogate(f, &mut wr.fs);
        tm.mark("node_extra", &mut t);
    }

    // ---- R
    let his = claim_points(&r, &tl, &sz[8..], &tpp, &taup);
    let e_r1 = F::ONE + sk.rho[0];
    let (i0, i1) = (e_r1.inv(), sk.rho[0].inv());
    let mut sa = vec![F::ZERO; 128];
    for sg in 0..64 {
        sa[sg] = r1.bank[0][sg] * i0;
        sa[64 + sg] = r1.bank[1][sg] * i1;
    }
    // claims (b) and (c) share their block coordinates with the partial folds already made
    // (lincheck at s_out, shift collapse at τ'): s_v = Σ_{y_in} eq(hi_in, y_in) Z(128 y_in + v)
    let from_fold = |z: &[F], hi_in: &[F]| -> Vec<F> {
        let e = eq_table(hi_in);
        let mut sv = vec![F::ZERO; 128];
        for (yi, ey) in e.iter().enumerate() {
            crate::simd::axpy(&mut sv, &z[128 * yi..128 * yi + 128], *ey);
        }
        sv
    };
    let sbv = from_fold(&zf_keep, &tl[7..14]);
    let scv = from_fold(&zs_keep, &tpp[7..10]);
    debug_assert_eq!(sbv, ringswitch::partials(&w.z, &his[1]));
    tm.mark("rs_partials", &mut t);
    debug_assert_eq!(dot(&claim_weights_a(&r, lambda), &sa), pz_l);
    debug_assert_eq!(dot(&eq_table(&tl[..7]), &sbv), vz);
    debug_assert_eq!(dot(&eq_table(&tpp[..7]), &scv), vc);
    let mut msg = sa.clone();
    msg.extend_from_slice(&sbv);
    msg.extend_from_slice(&scv);
    wr.send_f(&msg);
    let ch = wr.fs.chal_fs(8);
    let (rpp, kap) = (&ch[..7], ch[7]);
    let beta = ringswitch::target(&sa, rpp) + kap * ringswitch::target(&sbv, rpp) + kap * kap * ringswitch::target(&scv, rpp);
    let wt = ringswitch::weight_table(&[&his[0], &his[1], &his[2]], rpp, kap);
    tm.mark("ringswitch", &mut t);

    // ---- P
    ligerito::prove(m, f, wt, beta, c0, &mut wr);
    tm.mark("ligerito", &mut t);
    (wr.pi, tm)
}

/// Timing surrogate of the node's element phases (P2 prototype, not part of the proof; rev. 3
/// §2.3 E, Lr): E1, a degree-3 zerocheck over `2^20` rows (`A·B − C`); E2, a degree-2 sumcheck over
/// the packed polynomial (`2^(m−7)` F) against a weight table; Lr, the same over `2^15` rows.
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
    if std::env::var_os("FLOCK_E2_BATCHED").is_some() {
        // E2's claim batched into the Ligerito weight (as ring switching is): one pass adding a
        // template weight to W
        let mut w: Vec<F> = crate::par::uninit_vec(f.len());
        crate::par::for_each_chunk_mut(&mut w, 1 << 14, |off, ch| {
            for (i, x) in ch.iter_mut().enumerate() {
                *x = f[off + i] + F::new((off + i) as u64, 1);
            }
        });
        std::hint::black_box(&w);
    } else {
        let wt: Vec<F> = f.iter().map(|v| *v + F::ONE).collect();
        let (pt, _) = prove_pairs(vec![(wt, f.to_vec())], &mut |g| {
            std::hint::black_box(g);
            next()
        });
        std::hint::black_box(pt);
    }
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("  node_extra E2 {:.3}", t.elapsed().as_secs_f64());
    }
}

fn dot(a: &[F], b: &[F]) -> F {
    let mut acc = FAcc::default();
    for (x, y) in a.iter().zip(b.iter()) {
        acc.mac(*x, *y);
    }
    acc.reduce()
}

/// Claim (a)'s weights `w_(σ,b) = L^S_σ(λ) eq₁(ρ₁, b)` (`v = σ + 64 b`).
fn claim_weights_a(r: &[F], lambda: F) -> Vec<F> {
    let l = lagrange_weights(&skip().s_pts, lambda);
    let mut w = vec![F::ZERO; 128];
    for sg in 0..64 {
        w[sg] = l[sg] * (F::ONE + r[0]);
        w[64 + sg] = l[sg] * r[0];
    }
    w
}

/// The packed points of the three claims: (a) `(ρ₂…ρ₇, r_out)`, (b) `(t₇…t₁₃, s_out)`,
/// (c) `(t″₇…t″₉, 0, 0, 0, 0, τ′)`.
fn claim_points(r: &[F], tl: &[F], s_out: &[F], tpp: &[F], taup: &[F]) -> Vec<Vec<F>> {
    let a: Vec<F> = r[1..].to_vec();
    let mut b: Vec<F> = tl[7..14].to_vec();
    b.extend_from_slice(s_out);
    let mut c: Vec<F> = tpp[7..10].to_vec();
    c.extend_from_slice(&[F::ZERO; 4]);
    c.extend_from_slice(taup);
    vec![a, b, c]
}

/// The native verifier `V vk c π` of a leaf (P1's protocol). `None` = reject.
pub fn verify(o: &dyn Oracle, circ: &Circuit, vk: &Digest, c: &Digest, pi: &[u8]) -> Option<()> {
    if pi.len() < 96 || pi[0] != KIND_LEAF || pi[2] != 0 || pi[3..16].iter().any(|&x| x != 0) {
        return None;
    }
    let m = pi[1] as usize;
    if !(25..=32).contains(&m) {
        return None;
    }
    let hdr = &pi[..48];
    let mut rd = Reader { fs: Fs::seed(o, vk, c, hdr), pi, off: 48 };
    let st = rd.recv(48)?;
    let n = u64::from_le_bytes(st[..8].try_into().unwrap());
    let h: Digest = st[8..40].try_into().unwrap();
    let s: Digest = hdr[16..48].try_into().unwrap();
    if n != params::leaf_n(m) || st[40..48].iter().any(|&x| x != 0) || leaf_stmt(&h, n) != *c {
        return None;
    }
    let cap0b = rd.recv(32 << params::ladder(m)[0].cap_log)?;
    let cap0: Vec<Digest> = cap0b.chunks_exact(32).map(|d| d.try_into().unwrap()).collect();

    // ---- Z
    let sk = skip();
    let r_out = rd.fs.chal_fs(m - 13);
    let mut r: Vec<F> = sk.rho.to_vec();
    r.extend_from_slice(&r_out);
    let pp = rd.recv_f(128)?;
    let lambda = rd.fs.chal_f();
    let (mut claim, pz_l) = skip_eval(&pp[..64], &pp[64..], &r, lambda);
    let mut sz = Vec::with_capacity(m - 6);
    for k in 0..m - 6 {
        let g = rd.recv_f(3)?;
        if (F::ONE + r[k]) * g[0] + r[k] * g[1] != claim {
            return None;
        }
        let x = rd.fs.chal_f();
        claim = eval2_f([g[0], g[1], g[2]], x);
        sz.push(x);
    }
    let v = rd.recv_f(2)?;
    let (va, vb) = (v[0], v[1]);
    if claim != va * vb {
        return None;
    }

    // ---- Lc
    let alpha = rd.fs.chal_f();
    let mut claim = va + alpha * vb;
    let mut tl = Vec::with_capacity(14);
    for _ in 0..14 {
        let g = rd.recv_f(3)?;
        if g[0] + g[1] != claim {
            return None;
        }
        let x = rd.fs.chal_f();
        claim = eval2_f([g[0], g[1], g[2]], x);
        tl.push(x);
    }
    let vz = rd.recv_f(1)?[0];
    let eta = lincheck::eta(circ, lambda, &sz[..8], alpha);
    let et = eq_table(&tl);
    if claim != dot(&eta, &et) * vz {
        return None;
    }

    // ---- Sh + IO
    let ch = rd.fs.chal_fs(8 + (m - 14) + 1);
    let (theta, tau, kap_s) = (&ch[..8], &ch[8..8 + m - 14], ch[8 + m - 14]);
    let ones = (1u64 << (m - 14)) - 1;
    let mut claim = eq_at_int(tau, ones) * digest_mle(&h, theta) + kap_s * digest_mle(&s, theta);
    let mut taup = Vec::with_capacity(m - 14);
    for _ in 0..m - 14 {
        let g = rd.recv_f(3)?;
        if g[0] + g[1] != claim {
            return None;
        }
        let x = rd.fs.chal_f();
        claim = eval2_f([g[0], g[1], g[2]], x);
        taup.push(x);
    }
    let v = rd.recv_f(2)?;
    let (vo, vi) = (v[0], v[1]);
    let zeros = vec![F::ZERO; m - 14];
    let e2 = shift_mle(tau, &taup, F::ONE) + kap_s * eq_f(&zeros, &taup);
    if claim != eq_f(tau, &taup) * vo + e2 * vi {
        return None;
    }
    let mu = rd.fs.chal_f();
    let mut claim = vo + mu * vi;
    let mut tpp = Vec::with_capacity(10);
    for _ in 0..10 {
        let g = rd.recv_f(3)?;
        if g[0] + g[1] != claim {
            return None;
        }
        let x = rd.fs.chal_f();
        claim = eval2_f([g[0], g[1], g[2]], x);
        tpp.push(x);
    }
    let vc = rd.recv_f(1)?[0];
    let wsl = slot_weight(theta, mu);
    if claim != dot(&wsl, &eq_table(&tpp)) * vc {
        return None;
    }

    // ---- R
    let his = claim_points(&r, &tl, &sz[8..], &tpp, &taup);
    let sv = rd.recv_f(384)?;
    let (sa, sbv, scv) = (&sv[..128], &sv[128..256], &sv[256..]);
    if dot(&claim_weights_a(&r, lambda), sa) != pz_l || dot(&eq_table(&tl[..7]), sbv) != vz || dot(&eq_table(&tpp[..7]), scv) != vc {
        return None;
    }
    let ch = rd.fs.chal_fs(8);
    let (rpp, kap) = (ch[..7].to_vec(), ch[7]);
    let beta = ringswitch::target(sa, &rpp) + kap * ringswitch::target(sbv, &rpp) + kap * kap * ringswitch::target(scv, &rpp);

    // ---- P
    let w0 = |pt: &[K]| -> K {
        ringswitch::mbp(&his[0], pt, &rpp) + ringswitch::mbp(&his[1], pt, &rpp).mulf(kap) + ringswitch::mbp(&his[2], pt, &rpp).mulf(kap * kap)
    };
    ligerito::verify(m, &cap0, beta, &mut rd, &w0)?;
    if rd.off != pi.len() {
        return None;
    }
    Some(())
}
