//! The Ligerito opening (blueprint rev. 2 §2.2, §2.3 P; paper App. C), prover and verifier.
//!
//! Level `i` holds an F-valued polynomial `gᵢ` over `μᵢ` variables, laid out as `2^rowsᵢ` lanes
//! (its low variables) × `kᵢ` columns, committed as the interleaved novel-basis RS code of rate
//! `1/2^(i+1)`. The running claim is `Σ_x Wᵢ(x) gᵢ(x) = claim`. **P1** fold rounds: `rowsᵢ`
//! degree-2 rounds with K challenges `sᵢ` (3 K coefficients each). The folded K-vector `f'(c) =
//! ĝᵢ(sᵢ, c)` becomes `gᵢ₊₁` by the coordinate split (A.2: F index `2c + b` = coordinate `b`).
//! Then the next commitment (cap absorbed) or, after the last level, the final K-message in the
//! clear; `tᵢ` positions (A.4 P2: the `m* = 32` count of squeezes, every index opened, duplicates
//! included); columns and Merkle paths (Q: the column query, then `sibᵢ*` node queries, a smaller
//! `m`'s missing depths as dummies `0^64` with zero sibling slots); P3, `κ_c ∈ F^9` from 5 squeezes
//! (rev. 3.8); for `i <` last the batched claim `claim + Σ_q eq(κ_c, bits₉(q)) y_q` with `y_q = Σ_r
//! eq(sᵢ, r) Cᵢ[r, p_q]` (A.9 `finP`), whose weight is `Wᵢ₊₁(b, c) = U(b)·[Ŵᵢ(sᵢ, c) + Σ_q
//! eq(κ_c, bits₉(q)) X_c(D[p_q])]`, `U(0) = 1, U(1) = u`. At
//! the last level the verifier checks `y_q = Enc(final)[p_q]` directly, then Pf's 7 final rounds
//! reduce `Σ_c Ŵ(s, c) final(c)` over the final message padded to `2^7` (weight and message zero
//! beyond the kind's `2^(m−25)`) to one point, where it evaluates every weight once
//! (`weight_eval`). Messages go to A.3's fields: P1 rounds, caps, the final message, columns,
//! siblings, Pf rounds.

use crate::blake2s::Digest;
use crate::field::{KAcc, B64, F, K};
use crate::transcript::k_bytes;
use crate::merkle::Tree;
use crate::mle::{eq_table_k, mle_k};
use crate::ntt::{what_at, xhat, xrow, Ntt};
use crate::params::{self as pp, ladder, Level, CAP_LOG, LEVELS, LOG_INV_RATE};
use crate::par;
use crate::sumcheck::{coeffs_k, eval2_k};
use crate::transcript::{Reader, Writer};

/// The commitment of level 0 (made before the PIOP).
pub struct Commit0 {
    pub cw: Vec<F>,
    pub tree: Tree,
}

pub fn commit0(o: &dyn crate::oracle::Oracle, f: &[F], m: usize) -> Commit0 {
    let lv = ladder(m)[0];
    let ntt = Ntt::new(lv.code_log);
    let mut cw = Vec::new();
    ntt.encode(f, 1 << lv.rows_log, LOG_INV_RATE[0], &mut cw);
    let tree = Tree::commit(o, 0, &cw, 1 << lv.rows_log, lv.cap_log);
    Commit0 { cw, tree }
}

/// `U(b)·x`: `b = 0` → `x`, `b = 1` → `u x`.
#[inline(always)]
fn mul_u(x: K) -> K {
    // u (a + b u) = α b + (a + b) u
    K { a: x.b.mul_alpha(), b: x.a + x.b }
}

/// `Û(β) = 1 + β (1 + u)`.
fn u_hat(beta: K) -> K {
    K::ONE + beta + mul_u(beta)
}

/// One degree-2 round over the low variable of `Σ W g` (both K).
fn round_kk(w: &[K], g: &[K]) -> [K; 3] {
    let n = w.len() / 2;
    let parts = par::map_chunks(n, 1 << 11, |lo, hi| crate::simd::round_kk(&w[2 * lo..2 * hi], &g[2 * lo..2 * hi]));
    let mut r = [K::ZERO; 3];
    for p in parts {
        for j in 0..3 {
            r[j] += p[j];
        }
    }
    r
}

fn fold_k(t: &[K], s: K) -> Vec<K> {
    let mut out: Vec<K> = par::uninit_vec(t.len() / 2);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| crate::simd::kfold(&t[2 * off..2 * (off + ch.len())], s, ch));
    out
}

/// Fold both tables at `s` and, if `msg`, compute the next round's message on the folded tables
/// block by block while they are in cache.
fn fold_msg(w: &Tab, g: &FTab, s: K, msg: bool) -> (Vec<K>, Vec<K>, [K; 3]) {
    let n = match g {
        FTab::F(x) => x.len() / 2,
        FTab::K(x) => x.len() / 2,
    };
    let mut wo: Vec<K> = par::uninit_vec(n);
    let mut go: Vec<K> = par::uninit_vec(n);
    let (pw, pg) = (par::SyncPtr(wo.as_mut_ptr()), par::SyncPtr(go.as_mut_ptr()));
    let blk = 2048usize.min(n);
    let parts = par::map_chunks(n.div_ceil(blk), 1, |lo, hi| {
        let (pw, pg) = (pw, pg);
        let mut r = [K::ZERO; 3];
        for b in lo..hi {
            let (a, e) = (b * blk, ((b + 1) * blk).min(n));
            let (wo, go) = unsafe { (std::slice::from_raw_parts_mut(pw.0.add(a), e - a), std::slice::from_raw_parts_mut(pg.0.add(a), e - a)) };
            match w {
                Tab::F(x) => crate::simd::kfold_f(&x[2 * a..2 * e], s, wo),
                Tab::K(x) => crate::simd::kfold(&x[2 * a..2 * e], s, wo),
            }
            match g {
                FTab::F(x) => crate::simd::kfold_f(&x[2 * a..2 * e], s, go),
                FTab::K(x) => crate::simd::kfold(&x[2 * a..2 * e], s, go),
            }
            if msg {
                let m = crate::simd::round_kk(wo, go);
                for j in 0..3 {
                    r[j] += m[j];
                }
            }
        }
        r
    });
    let mut r = [K::ZERO; 3];
    for p in parts {
        for j in 0..3 {
            r[j] += p[j];
        }
    }
    (wo, go, r)
}

enum FTab<'a> {
    F(&'a [F]),
    K(&'a [K]),
}

fn fold_kf(g: &[F], s: K) -> Vec<K> {
    let mut out: Vec<K> = par::uninit_vec(g.len() / 2);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| crate::simd::kfold_f(&g[2 * off..2 * (off + ch.len())], s, ch));
    out
}

/// The weight and polynomial of a level's first round: `W` F or K, `g` F.
enum Tab {
    F(Vec<F>),
    K(Vec<K>),
}

/// Rounds over `nrounds` low variables of `Σ W g` with W given as `Tab`, g given as F (first
/// round) — returns the folded `(W, g)` as K tables and the challenges.
fn rounds(w: Tab, g: &[F], nrounds: usize, wr: &mut Writer, claim: &mut K) -> (Vec<K>, Vec<K>, Vec<K>) {
    // first round: g F-valued
    let n = g.len() / 2;
    let msg: [K; 3] = match &w {
        Tab::F(wf) => {
            let parts = par::map_chunks(n, 1 << 12, |lo, hi| crate::simd::round_ff(&wf[2 * lo..2 * hi], &g[2 * lo..2 * hi]));
            let mut r = [F::ZERO; 3];
            for p in parts {
                for j in 0..3 {
                    r[j] += p[j];
                }
            }
            [K::f(r[0]), K::f(r[1]), K::f(r[2])]
        }
        Tab::K(wk) => {
            let parts = par::map_chunks(n, 1 << 12, |lo, hi| crate::simd::round_kf(&wk[2 * lo..2 * hi], &g[2 * lo..2 * hi]));
            let mut r = [K::ZERO; 3];
            for p in parts {
                for j in 0..3 {
                    r[j] += p[j];
                }
            }
            r
        }
    };
    debug_assert_eq!(msg[0] + msg[1], *claim);
    wr.send_k(pp::F_P1, &coeffs_k(msg));
    let s = wr.fs.chal_k();
    *claim = eval2_k(msg, s);
    let mut ch = vec![s];
    let (mut wk, mut gk, mut nmsg) = fold_msg(&w, &FTab::F(g), s, nrounds > 1);
    for r in 1..nrounds {
        let msg = nmsg;
        debug_assert_eq!(msg, round_kk(&wk, &gk));
        debug_assert_eq!(msg[0] + msg[1], *claim);
        wr.send_k(pp::F_P1, &coeffs_k(msg));
        let s = wr.fs.chal_k();
        *claim = eval2_k(msg, s);
        ch.push(s);
        let (a, b, c) = fold_msg(&Tab::K(wk), &FTab::K(&gk), s, r + 1 < nrounds);
        wk = a;
        gk = b;
        nmsg = c;
    }
    (wk, gk, ch)
}

/// `K` vector as its F coordinates (index `2c + b`).
fn split(v: &[K]) -> Vec<F> {
    let mut o = Vec::with_capacity(2 * v.len());
    for x in v {
        o.push(x.a);
        o.push(x.b);
    }
    o
}

/// `Σ_q κ_q X_c(D[p_q])` for every `c < 2^bits` (F), with `X_c = X_lo(c_lo) X_hi(c_hi)` and
/// unreduced accumulation (two carry-less products per (q, c)).
fn consistency_weights(ps: &[u64], kap: &[F], bits: usize) -> Vec<F> {
    let blo = bits.min(10);
    let bhi = bits - blo;
    let mut xlo = Vec::with_capacity(ps.len() << blo);
    let mut xhi = Vec::with_capacity(ps.len() << bhi);
    let mut row = Vec::new();
    for &p in ps {
        xrow(p, blo, &mut row);
        xlo.extend_from_slice(&row);
        // the high factor: Π_{v ≥ blo} Ŵ_v(p)^{c_v}
        let mut h = vec![B64::ONE];
        for v in blo..bits {
            let wv = what_at(v, p);
            let n = h.len();
            for j in 0..n {
                let x = h[j].mul(wv);
                h.push(x);
            }
        }
        xhi.extend_from_slice(&h);
    }
    let nlo = 1usize << blo;
    let nhi = 1usize << bhi;
    let t = ps.len();
    let blocks: Vec<Vec<F>> = par::map_chunks(nhi, 1, |a, b| {
        let mut out = Vec::with_capacity((b - a) * nlo);
        let mut acc = vec![[0u128; 2]; nlo];
        for ch in a..b {
            acc.iter_mut().for_each(|x| *x = [0, 0]);
            for q in 0..t {
                let c = kap[q].mulb(xhi[q * nhi + ch]);
                crate::simd::xmac(&mut acc, &xlo[q * nlo..(q + 1) * nlo], c);
            }
            for l in 0..nlo {
                out.push(F { lo: crate::field::red(acc[l][0]), hi: crate::field::red(acc[l][1]) });
            }
        }
        out
    });
    blocks.concat()
}

fn column_fold(col: &[F], e: &[K]) -> K {
    let mut acc = KAcc::default();
    for (x, w) in col.iter().zip(e.iter()) {
        acc.mac_f(*w, *x);
    }
    acc.reduce()
}

/// The cap of level `i` in its A.3 slot (`2^capᵢ*` digests; a test shape's smaller cap zero-padded).
pub fn cap_slot(i: usize, cap: &[Digest]) -> Vec<u8> {
    let mut b = vec![0u8; 32 << CAP_LOG[i]];
    for (j, d) in cap.iter().enumerate() {
        b[32 * j..32 * j + 32].copy_from_slice(d);
    }
    b
}

/// The cap depth of level `i` for `m` committed bits.
pub fn cap_log(m: usize, i: usize) -> usize {
    ladder(m)[i].cap_log
}

/// Read (and absorb) level `i`'s cap slot from the caps field: its first `2^cl` digests; the rest
/// must be zero.
pub fn read_cap_slot(rd: &mut Reader, i: usize, cl: usize) -> Vec<Digest> {
    let b = rd.recv(pp::F_CAPS, 32 << CAP_LOG[i]);
    rd.check(b[32 << cl..].iter().all(|&x| x == 0));
    b[..32 << cl].chunks_exact(32).map(|d| d.try_into().unwrap()).collect()
}

/// The consistency coefficients `eq(κ_c, bits₉(q))`, `q < t` (A.9 `finP`).
fn kappa_coeffs(kc: &[F], t: usize) -> Vec<F> {
    let mut e = crate::mle::eq_table(kc);
    e.truncate(t);
    e
}

/// The prover: `Σ_y W(y) f(y) = claim` with `f` committed in `c0` (cap₀ already absorbed).
pub fn prove(m: usize, f: &[F], w0: Vec<F>, claim0: F, c0: Commit0, wr: &mut Writer) {
    let lad = ladder(m);
    let mut claim = K::f(claim0);
    let mut wtab = Tab::F(w0);
    let mut g: Vec<F> = f.to_vec();
    let mut cw = c0.cw;
    let mut tree = c0.tree;
    let verbose = std::env::var_os("FLOCK_VERBOSE").is_some();
    let mut tt = std::time::Instant::now();
    let mut lap = |name: &str, i: usize| {
        if verbose {
            eprintln!("  ligerito level {i} {name} {:.3}", tt.elapsed().as_secs_f64());
        }
        tt = std::time::Instant::now();
    };
    for i in 0..LEVELS {
        let lv = lad[i];
        let rows = 1usize << lv.rows_log;
        wr.fs.phase = "P1";
        let (wk, fk, s) = rounds(wtab, &g, lv.rows_log, wr, &mut claim);
        lap("rounds", i);
        let last = i + 1 == LEVELS;
        wr.fs.phase = "C";
        let (ncw, ntree) = if !last {
            let nl = lad[i + 1];
            let gn = split(&fk);
            let ntt = Ntt::new(nl.code_log);
            let mut ncw = Vec::new();
            ntt.encode(&gn, 1 << nl.rows_log, LOG_INV_RATE[i + 1], &mut ncw);
            let t = Tree::commit(wr.fs.o, (i + 1) as u8, &ncw, 1 << nl.rows_log, nl.cap_log);
            wr.send(pp::F_CAPS, &cap_slot(i + 1, t.cap()));
            lap("encode+merkle", i);
            (ncw, Some((t, gn)))
        } else {
            let mut fin = fk.clone();
            fin.resize(pp::FINAL_ELEMS, K::ZERO);
            wr.send(pp::F_FINAL, &k_bytes(&fin));
            (Vec::new(), None)
        };
        wr.fs.phase = "P2";
        let ps = wr.fs.positions(pp::STAR_SQ[i], lv.queries, lv.code_log);
        let es = eq_table_k(&s);
        let sib = lv.code_log - lv.cap_log;
        if sib < pp::STAR_SIB[i] {
            // the level's dummy node query `0^64` (asked by the verifier at the missing depths),
            // asked once here so that the trace replay finds it in the prover's table
            let mut q = Vec::with_capacity(72);
            crate::merkle::node_query(i as u8, &[0u8; 32], &[0u8; 32], &mut q);
            wr.fs.o.ask(&q);
        }
        let mut ys = Vec::with_capacity(ps.len());
        for &p in &ps {
            let col = &cw[p as usize * rows..(p as usize + 1) * rows];
            for x in col {
                wr.put(pp::F_COLS, &x.to_bytes());
            }
            wr.put(pp::F_COLS, &[0u8; pp::COL_PAD]);
            for d in tree.path(p as usize) {
                wr.put(pp::F_SIBS, &d);
            }
            wr.put(pp::F_SIBS, &vec![0u8; 32 * (pp::STAR_SIB[i] - sib)]);
            ys.push(column_fold(col, &es));
        }
        lap("open", i);
        wr.fs.phase = "P3";
        let kc = wr.fs.coords(pp::P3_SQ);
        match ntree {
            Some((t, gn)) => {
                let kq = kappa_coeffs(&kc[..pp::KAPPA_C], ps.len());
                for q in 0..ps.len() {
                    claim += ys[q].mulf(kq[q]);
                }
                let cons = consistency_weights(&ps, &kq, lv.msg_log);
                let base: Vec<K> = par::collect_vec(wk.len(), 1 << 12, |c| wk[c] + K::f(cons[c]));
                let mut wn = Vec::with_capacity(2 * base.len());
                for b in &base {
                    wn.push(*b);
                    wn.push(mul_u(*b));
                }
                wtab = Tab::K(wn);
                lap("weights", i);
                g = gn;
                cw = ncw;
                tree = t;
            }
            None => {
                // Pf: the final rounds over the message and weight padded to 2^7
                wr.fs.phase = "Pf";
                let mut wk = wk;
                let mut fk = fk;
                wk.resize(pp::FINAL_ELEMS, K::ZERO);
                fk.resize(pp::FINAL_ELEMS, K::ZERO);
                while fk.len() > 1 {
                    let msg = round_kk(&wk, &fk);
                    debug_assert_eq!(msg[0] + msg[1], claim);
                    wr.send_k(pp::F_PF, &coeffs_k(msg));
                    let s = wr.fs.chal_k();
                    claim = eval2_k(msg, s);
                    wk = fold_k(&wk, s);
                    fk = fold_k(&fk, s);
                }
                debug_assert_eq!(claim, wk[0] * fk[0]);
                return;
            }
        }
    }
}

// ---------------------------------------------------------------- verifier

/// What the verifier keeps per level for the final weight evaluation.
struct LevelRec {
    s: Vec<K>,
    kappa: Vec<F>,
    ps: Vec<u64>,
}

/// `Ŵᵢ(pt)` by the recursion; `w0` evaluates level 0's weight (the ring-switch MBP).
fn weight_eval(i: usize, pt: &[K], recs: &[LevelRec], w0: &dyn Fn(&[K]) -> K) -> K {
    if i == 0 {
        return w0(pt);
    }
    let r = &recs[i - 1];
    let mut inner: Vec<K> = r.s.clone();
    inner.extend_from_slice(&pt[1..]);
    let mut v = weight_eval(i - 1, &inner, recs, w0);
    let kq = kappa_coeffs(&r.kappa, r.ps.len());
    for (q, &p) in r.ps.iter().enumerate() {
        v += xhat(p, &pt[1..]).mulf(kq[q]);
    }
    u_hat(pt[0]) * v
}

/// One K round (`roundOpsK`): `c₁ + c₂ = claim`, next claim `c₀ + r(c₁ + r c₂)`.
fn v_round_k(rd: &mut Reader, f: usize, claim: &mut K) -> K {
    let g = rd.recv_k(f, 3);
    let x = rd.fs.chal_k();
    rd.check(g[1] + g[2] == *claim);
    *claim = g[0] + x * (g[1] + x * g[2]);
    x
}

/// The verifier of `Σ_y W(y) f(y) = claim0` against the level-0 cap; `w0(pt)` evaluates `Ŵ`. Every
/// check goes to `rd.ok`; every item is asked.
pub fn verify(m: usize, cap0: &[Digest], claim0: F, rd: &mut Reader, w0: &dyn Fn(&[K]) -> K) {
    let lad = ladder(m);
    let mut claim = K::f(claim0);
    let mut cap: Vec<Digest> = cap0.to_vec();
    let mut recs: Vec<LevelRec> = Vec::new();
    let zero = [0u8; 32];
    for i in 0..LEVELS {
        let lv: Level = lad[i];
        let rows = 1usize << lv.rows_log;
        rd.fs.phase = "P1";
        let mut s = Vec::with_capacity(lv.rows_log);
        for _ in 0..lv.rows_log {
            s.push(v_round_k(rd, pp::F_P1, &mut claim));
        }
        let last = i + 1 == LEVELS;
        rd.fs.phase = "C";
        let mut fin: Vec<K> = Vec::new();
        let mut next_cap = Vec::new();
        if !last {
            next_cap = read_cap_slot(rd, i + 1, lad[i + 1].cap_log);
        } else {
            fin = rd.recv_k(pp::F_FINAL, pp::FINAL_ELEMS);
            let real = 1usize << lv.msg_log;
            let pad_zero = fin[real..].iter().all(|x| *x == K::ZERO);
            rd.check(pad_zero);
        }
        rd.fs.phase = "P2";
        let ps = rd.fs.positions(pp::STAR_SQ[i], lv.queries, lv.code_log);
        rd.fs.phase = "Q";
        let es = eq_table_k(&s);
        let mut ys = Vec::with_capacity(ps.len());
        let sib = lv.code_log - lv.cap_log;
        for &p in &ps {
            let cb = rd.take(pp::F_COLS, 16 * rows + pp::COL_PAD);
            let col: Vec<F> = cb[..16 * rows].chunks_exact(16).map(F::from_bytes).collect();
            let mut cur = rd.fs.ask_col(i, cb);
            for d in 0..pp::STAR_SIB[i] {
                let sd: Digest = rd.take(pp::F_SIBS, 32).try_into().unwrap();
                if d < sib {
                    cur = if (p >> d) & 1 == 0 { rd.fs.ask_node(i, d, &cur, &sd) } else { rd.fs.ask_node(i, d, &sd, &cur) };
                } else {
                    rd.check(sd == zero);
                    rd.fs.ask_node(i, d, &zero, &zero);
                }
            }
            let ok = cur == cap[(p >> sib) as usize];
            rd.check(ok);
            ys.push(column_fold(&col, &es));
        }
        rd.fs.phase = "P3";
        let kc = rd.fs.coords(pp::P3_SQ)[..pp::KAPPA_C].to_vec();
        if !last {
            let kq = kappa_coeffs(&kc, ps.len());
            for q in 0..ps.len() {
                claim += ys[q].mulf(kq[q]);
            }
            recs.push(LevelRec { s, kappa: kc, ps });
            cap = next_cap;
        } else {
            // finP 4: the direct consistency against the final message (its real part)
            let real = &fin[..1usize << lv.msg_log];
            let mut row = Vec::new();
            for (qn, &p) in ps.iter().enumerate() {
                xrow(p, lv.msg_log, &mut row);
                let mut e = K::ZERO;
                for c in 0..real.len() {
                    e += real[c].mulb(row[c]);
                }
                rd.check(e == ys[qn]);
            }
            // Pf and finPf
            rd.fs.phase = "Pf";
            let mut sf = Vec::new();
            for _ in 0..pp::PF_ROUNDS {
                sf.push(v_round_k(rd, pp::F_PF, &mut claim));
            }
            let fv = mle_k(&fin, &sf);
            let mut pt = s.clone();
            pt.extend_from_slice(&sf[..lv.msg_log]);
            let mut wv = weight_eval(i, &pt, &recs, w0);
            for x in &sf[lv.msg_log..] {
                wv = wv * (K::ONE + *x);
            }
            rd.check(claim == wv * fv);
        }
    }
}
