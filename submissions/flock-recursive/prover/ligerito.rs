//! The Ligerito opening (blueprint rev. 2 §2.2, §2.3 P; paper App. C), prover and verifier.
//!
//! Level `i` holds an F-valued polynomial `gᵢ` over `μᵢ` variables, laid out as `2^rowsᵢ` lanes
//! (its low variables) × `kᵢ` columns, committed as the interleaved novel-basis RS code of rate
//! `1/2^(i+1)`. The running claim is `Σ_x Wᵢ(x) gᵢ(x) = claim`. **P1** fold rounds: `rowsᵢ`
//! degree-2 rounds with K challenges `sᵢ` (3 K coefficients each). The folded K-vector `f'(c) =
//! ĝᵢ(sᵢ, c)` becomes `gᵢ₊₁` by the coordinate split (A.2: F index `2c + b` = coordinate `b`).
//! Then the next commitment (cap absorbed) or, after the last level, the final K-message in the
//! clear; `tᵢ` positions; columns and Merkle paths; for `i <` last, `κ_c ∈ F^9` and the batched
//! claim `eq(κ_c, 0)·claim + Σ_q eq(κ_c, q+1) y_q` with `y_q = Σ_r eq(sᵢ, r) Cᵢ[r, p_q]`, whose
//! weight is `Wᵢ₊₁(b, c) = U(b)·[eq(κ_c, 0) Ŵᵢ(sᵢ, c) + Σ_q eq(κ_c, q+1) X_c(D[p_q])]`, `U(0) = 1,
//! U(1) = u`. At the last level the verifier checks `y_q = Enc(final)[p_q]` directly, then
//! `log k₅` final rounds reduce `Σ_c Ŵ(s, c) final(c)` to one point (**P1 choice**: the verifier
//! then evaluates every weight once, by the recursion `weight_eval`).

use crate::blake2s::Digest;
use crate::field::{KAcc, B64, F, K};
use crate::merkle::{col_query, node_query, Tree};
use crate::mle::{eq_at_int, eq_table, eq_table_k};
use crate::ntt::{what_at, xhat, xrow, Ntt};
use crate::params::{ladder, Level, KAPPA_C, LEVELS, LOG_INV_RATE};
use crate::par;
use crate::sumcheck::eval2_k;
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
    wr.send_k(&msg);
    let s = wr.fs.chal_k();
    *claim = eval2_k(msg, s);
    let mut ch = vec![s];
    let (mut wk, mut gk, mut nmsg) = fold_msg(&w, &FTab::F(g), s, nrounds > 1);
    for r in 1..nrounds {
        let msg = nmsg;
        debug_assert_eq!(msg, round_kk(&wk, &gk));
        debug_assert_eq!(msg[0] + msg[1], *claim);
        wr.send_k(&msg);
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

fn put_digests(wr: &mut Writer, ds: &[Digest]) {
    for d in ds {
        wr.put(d);
    }
}

/// The prover: `Σ_y W(y) f(y) = claim` with `f` committed in `c0`.
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
        let (wk, fk, s) = rounds(wtab, &g, lv.rows_log, wr, &mut claim);
        lap("rounds", i);
        let last = i + 1 == LEVELS;
        let (ncw, ntree) = if !last {
            let nl = lad[i + 1];
            let gn = split(&fk);
            let ntt = Ntt::new(nl.code_log);
            let mut ncw = Vec::new();
            ntt.encode(&gn, 1 << nl.rows_log, LOG_INV_RATE[i + 1], &mut ncw);
            let t = Tree::commit(wr.fs.o, (i + 1) as u8, &ncw, 1 << nl.rows_log, nl.cap_log);
            let mut capb = Vec::with_capacity(32 * t.cap().len());
            for d in t.cap() {
                capb.extend_from_slice(d);
            }
            wr.send(&capb);
            lap("encode+merkle", i);
            (ncw, Some((t, gn)))
        } else {
            wr.send_k(&fk);
            (Vec::new(), None)
        };
        let ps = wr.fs.positions(lv.queries, lv.code_log);
        let es = eq_table_k(&s);
        let mut ys = Vec::with_capacity(ps.len());
        for &p in &ps {
            let col = &cw[p as usize * rows..(p as usize + 1) * rows];
            for x in col {
                wr.put(&x.to_bytes());
            }
            put_digests(wr, &tree.path(p as usize));
            ys.push(column_fold(col, &es));
        }
        lap("open", i);
        match ntree {
            Some((t, gn)) => {
                let kap = wr.fs.chal_fs(KAPPA_C);
                let ek = eq_table(&kap);
                let kq: Vec<F> = (0..ps.len()).map(|q| ek[q + 1]).collect();
                claim = claim.mulf(ek[0]);
                for q in 0..ps.len() {
                    claim += ys[q].mulf(kq[q]);
                }
                let cons = consistency_weights(&ps, &kq, lv.msg_log);
                let e0 = ek[0];
                let base: Vec<K> = par::collect_vec(wk.len(), 1 << 12, |c| wk[c].mulf(e0) + K::f(cons[c]));
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
                // final rounds over the clear message
                let mut wk = wk;
                let mut fk = fk;
                while fk.len() > 1 {
                    let msg = round_kk(&wk, &fk);
                    debug_assert_eq!(msg[0] + msg[1], claim);
                    wr.send_k(&msg);
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
    let ek = |j: u64| eq_at_int(&r.kappa, j);
    let mut v = weight_eval(i - 1, &inner, recs, w0).mulf(ek(0));
    for (q, &p) in r.ps.iter().enumerate() {
        v += xhat(p, &pt[1..]).mulf(ek(q as u64 + 1));
    }
    u_hat(pt[0]) * v
}

/// The verifier of `Σ_y W(y) f(y) = claim0` against the level-0 cap; `w0(pt)` evaluates `Ŵ`.
/// Returns `None` on any failure.
pub fn verify(m: usize, cap0: &[Digest], claim0: F, rd: &mut Reader, w0: &dyn Fn(&[K]) -> K) -> Option<()> {
    let lad = ladder(m);
    let mut claim = K::f(claim0);
    let mut cap: Vec<Digest> = cap0.to_vec();
    let mut recs: Vec<LevelRec> = Vec::new();
    for i in 0..LEVELS {
        let lv: Level = lad[i];
        let rows = 1usize << lv.rows_log;
        let mut s = Vec::with_capacity(lv.rows_log);
        for _ in 0..lv.rows_log {
            let g = rd.recv_k(3)?;
            if g[0] + g[1] != claim {
                return None;
            }
            let x = rd.fs.chal_k();
            claim = eval2_k([g[0], g[1], g[2]], x);
            s.push(x);
        }
        let last = i + 1 == LEVELS;
        let mut fin: Vec<K> = Vec::new();
        let mut next_cap = Vec::new();
        if !last {
            let nl = lad[i + 1];
            let b = rd.recv(32 << nl.cap_log)?;
            next_cap = b.chunks_exact(32).map(|d| d.try_into().unwrap()).collect();
        } else {
            fin = rd.recv_k(1 << lv.msg_log)?;
        }
        let ps = rd.fs.positions(lv.queries, lv.code_log);
        let es = eq_table_k(&s);
        let mut ys = Vec::with_capacity(ps.len());
        let mut q = Vec::new();
        let levelb = i as u8;
        let depth = lv.code_log;
        for &p in &ps {
            let cb = rd.take(16 * rows)?;
            let col: Vec<F> = cb.chunks_exact(16).map(F::from_bytes).collect();
            q.clear();
            col_query(levelb, &col, &mut q);
            let mut cur = rd.fs.o.ask(&q);
            for d in 0..depth - lv.cap_log {
                let sib: Digest = rd.take(32)?.try_into().unwrap();
                q.clear();
                if (p >> d) & 1 == 0 {
                    node_query(levelb, &cur, &sib, &mut q);
                } else {
                    node_query(levelb, &sib, &cur, &mut q);
                }
                cur = rd.fs.o.ask(&q);
            }
            if cur != cap[(p >> (depth - lv.cap_log)) as usize] {
                return None;
            }
            ys.push(column_fold(&col, &es));
        }
        if !last {
            let kap = rd.fs.chal_fs(KAPPA_C);
            let ek = eq_table(&kap);
            claim = claim.mulf(ek[0]);
            for qn in 0..ps.len() {
                claim += ys[qn].mulf(ek[qn + 1]);
            }
            recs.push(LevelRec { s, kappa: kap, ps });
            cap = next_cap;
        } else {
            // direct consistency against the clear message
            let mut row = Vec::new();
            for (qn, &p) in ps.iter().enumerate() {
                xrow(p, lv.msg_log, &mut row);
                let mut e = K::ZERO;
                for c in 0..fin.len() {
                    e += fin[c].mulb(row[c]);
                }
                if e != ys[qn] {
                    return None;
                }
            }
            let mut sf = Vec::new();
            for _ in 0..lv.msg_log {
                let g = rd.recv_k(3)?;
                if g[0] + g[1] != claim {
                    return None;
                }
                let x = rd.fs.chal_k();
                claim = eval2_k([g[0], g[1], g[2]], x);
                sf.push(x);
            }
            let fv = crate::mle::mle_k(&fin, &sf);
            let mut pt = s.clone();
            pt.extend_from_slice(&sf);
            let wv = weight_eval(i, &pt, &recs, w0);
            if claim != wv * fv {
                return None;
            }
            return Some(());
        }
    }
    None
}
