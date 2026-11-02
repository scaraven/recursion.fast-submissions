//! Sumcheck pieces shared by the phases. The provers compute a degree-2 round as `(g(0), g(1),
//! g(∞))`; the message is the coefficients `c₀ ‖ c₁ ‖ c₂` of `g(X) = c₀ + c₁X + c₂X²` (A.2, `gen`'s
//! `roundOpsF`/`roundOpsK`), checked `c₁ + c₂ = claim` (that is `g(0) + g(1) = claim`) and evaluated
//! `c₀ + r(c₁ + r c₂)`. A degree-3 round sends `c₀ ‖ c₁ ‖ c₂` and the verifier completes
//! `c₃ = claim + c₁ + c₂`. Variables are bound low bit first.

use crate::field::{F, K};
use crate::par;

pub fn eval2_f(g: [F; 3], x: F) -> F {
    g[0] + (g[0] + g[1] + g[2]) * x + g[2] * x * x
}
pub fn eval2_k(g: [K; 3], x: K) -> K {
    g[0] + (g[0] + g[1] + g[2]) * x + g[2] * x * x
}

/// `(g(0), g(1), g(∞))` → the message `(c₀, c₁, c₂)`.
pub fn coeffs_f(g: [F; 3]) -> [F; 3] {
    [g[0], g[0] + g[1] + g[2], g[2]]
}
pub fn coeffs_k(g: [K; 3]) -> [K; 3] {
    [g[0], g[0] + g[1] + g[2], g[2]]
}

/// The message of one round of `Σ_x Σ_t P_t(x) Q_t(x)` over the low variable.
pub fn msg_pairs(pairs: &[(&[F], &[F])]) -> [F; 3] {
    let n = pairs[0].0.len() / 2;
    // P2: the vector kernel per chunk (`round_ff`; the same sums)
    let parts = par::map_chunks(n, 1 << 12, |lo, hi| {
        let mut g = [F::ZERO; 3];
        for (p, q) in pairs {
            let r = crate::simd::round_ff(&p[2 * lo..2 * hi], &q[2 * lo..2 * hi]);
            for j in 0..3 {
                g[j] += r[j];
            }
        }
        g
    });
    let mut g = [F::ZERO; 3];
    for x in parts {
        for j in 0..3 {
            g[j] += x[j];
        }
    }
    g
}

/// `t'[i] = t[2i] + s (t[2i] + t[2i+1])`.
/// `fold_f` of a table whose entries `≥ live` are zero: the output's entries `≥ ⌈live/2⌉` are zero
/// and are written as such without a product.
pub fn fold_f_live(t: &[F], s: F, live: usize) -> Vec<F> {
    let n = t.len() / 2;
    let lo = live.div_ceil(2).min(n);
    let mut out: Vec<F> = par::uninit_vec(n);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| {
        let k = lo.saturating_sub(off).min(ch.len());
        crate::simd::fold(&t[2 * off..2 * (off + k)], s, &mut ch[..k]);
        ch[k..].iter_mut().for_each(|x| *x = F::ZERO);
    });
    out
}

/// `fold_f` that writes zeros for zero input stretches without reading them twice (pass 12: the
/// node's E2 tables over the M rows, whose slots end in holes; same result as `fold_f`).
pub fn fold_f_sparse(t: &[F], s: F) -> Vec<F> {
    let n = t.len() / 2;
    let mut out: Vec<F> = par::uninit_vec(n);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| {
        for (i, sub) in ch.chunks_mut(1 << 10).enumerate() {
            let o = off + (i << 10);
            let src = &t[2 * o..2 * (o + sub.len())];
            if src.iter().all(|x| x.is_zero()) {
                sub.iter_mut().for_each(|x| *x = F::ZERO);
            } else {
                crate::simd::fold(src, s, sub);
            }
        }
    });
    out
}

pub fn fold_f(t: &[F], s: F) -> Vec<F> {
    let n = t.len() / 2;
    let mut out: Vec<F> = par::uninit_vec(n);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| {
        crate::simd::fold(&t[2 * off..2 * (off + ch.len())], s, ch);
    });
    out
}

/// Run the rounds of `Σ_x Σ_t P_t(x) Q_t(x) = claim` to the end, with `chal(msg) -> s` (the
/// transcript step). Returns the challenges and the fully folded `(P_t, Q_t)` values.
pub fn prove_pairs(mut tabs: Vec<(Vec<F>, Vec<F>)>, chal: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, Vec<(F, F)>) {
    let mut pt = Vec::new();
    while tabs[0].0.len() > 1 {
        let g = {
            let refs: Vec<(&[F], &[F])> = tabs.iter().map(|(p, q)| (&p[..], &q[..])).collect();
            msg_pairs(&refs)
        };
        let s = chal(g);
        pt.push(s);
        for (p, q) in tabs.iter_mut() {
            *p = fold_f(p, s);
            *q = fold_f(q, s);
        }
    }
    (pt, tabs.iter().map(|(p, q)| (p[0], q[0])).collect())
}

/// `prove_pairs` for one pair `(P, Q)` where `P` is zero outside a few regions (the node's E4: `W`
/// lives on the M slots, the L bits, the one cell and the link cells; pass 10): `prove_pairs_support`
/// with one table pair. The messages and challenges are `prove_pairs`'s (test
/// `pair_support_same_messages`), and so is the final pair. `Q` is borrowed (no copy).
pub fn prove_pair_support(p: Vec<F>, q: &[F], a: usize, chal: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, (F, F)) {
    let (pt, fin) = prove_pairs_support(vec![p], &[Q::Tab(q)], a, chal);
    (pt, fin[0])
}

/// The dense side of a pair in `prove_pairs_support`: a table, or `scale·eq(pt, ·)` in closed form
/// (never materialized: within a chunk it is a small eq table times the chunk's high factor).
pub enum Q<'a> {
    Tab(&'a [F]),
    Eq(&'a [F], F),
}

/// The maximal runs `(first, count)` of consecutive chunks in the ascending list `live`.
fn runs_of(live: &[u32]) -> Vec<(usize, usize)> {
    let mut r: Vec<(usize, usize)> = Vec::new();
    for &c in live {
        match r.last_mut() {
            Some((f, n)) if *f + *n == c as usize => *n += 1,
            _ => r.push((c as usize, 1)),
        }
    }
    r
}

/// Runs cut into work items of about `2^16` table entries at chunk size `cs` (for `par::map_chunks`).
fn split_runs(runs: &[(usize, usize)], cs: usize) -> Vec<(usize, usize)> {
    let per = ((1usize << 16) / cs).max(1);
    let mut v = Vec::with_capacity(runs.len());
    for &(f, n) in runs {
        let mut o = 0;
        while o < n {
            let k = per.min(n - o);
            v.push((f + o, k));
            o += k;
        }
    }
    v
}

/// `prove_pairs` for several pairs `(P_t, Q_t)`, `P_t` zero outside a few regions (the node's E4 with
/// RSV2's child term: `(W, f)` and `(G, κ_E⁴·eq(p_y, ·))`). The tables are cut into aligned chunks of
/// `2^a` entries; a chunk where `P_t` is zero adds nothing to the first `a` rounds' messages and its
/// `P_t` stays zero, so in those rounds only each pair's live chunks are summed and folded, run by
/// run of consecutive live chunks with the vector kernels (P2: `round_ff`, `fold`; for a closed-form
/// `Q = h_c·le` on chunk `c` the chunk's message is `h_c·round_ff(P, le)`, as the message is linear in
/// `Q`). A dead chunk's `Q` enters after round `a` as `Σ_l eq(r_{<a}, l) Q[2^a c + l]`; the remaining
/// rounds are `prove_pairs`'s. The messages and challenges are `prove_pairs`'s (test
/// `pairs_support_same_messages`), and so are the final pairs. P2: E4 passes a small `a` (the link
/// and arena₁ cells make most `2^12` chunks live, few `2^4` ones).
pub fn prove_pairs_support(ps: Vec<Vec<F>>, qs: &[Q], a: usize, chal: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, Vec<(F, F)>) {
    let n = ps[0].len();
    let nv = n.trailing_zeros() as usize;
    let np = ps.len();
    assert!(qs.len() == np && ps.iter().all(|p| p.len() == n) && n.is_power_of_two());
    for q in qs {
        match q {
            Q::Tab(t) => assert_eq!(t.len(), n),
            Q::Eq(pt, _) => assert_eq!(pt.len(), nv),
        }
    }
    let a = a.min(nv);
    let sp = crate::prof::span("sc.live");
    let lives: Vec<Vec<u32>> = ps.iter().map(|p| par::map_chunks(n >> a, 64, |lo, hi| (lo..hi).filter(|&c| p[c << a..(c + 1) << a].iter().any(|x| !x.is_zero())).map(|c| c as u32).collect::<Vec<u32>>()).concat()).collect();
    let runs: Vec<Vec<(usize, usize)>> = lives.iter().map(|l| runs_of(l)).collect();
    drop(sp);
    let sp = crate::prof::span("sc.rounds");
    let mut pt: Vec<F> = Vec::with_capacity(nv);
    let mut pk: Vec<Vec<F>> = ps;
    let mut qk: Vec<Vec<F>> = vec![Vec::new(); np];
    // a closed-form Q's chunk factors `eq(pt[a..], c)` and its running prefix `Π_{t<k} eq(pt_t, s_t)`
    let hi_eq: Vec<Option<Vec<F>>> = qs.iter().map(|q| if let Q::Eq(p, sc) = q { Some(crate::mle::eq_table_scaled(&p[a..], *sc)) } else { None }).collect();
    let mut pre: Vec<F> = vec![F::ONE; np];
    for k in 0..a {
        let cs = 1usize << (a - k);
        let mut msg = [F::ZERO; 3];
        for t in 0..np {
            let pr: &[F] = &pk[t];
            let le: Option<Vec<F>> = if let Q::Eq(p, _) = &qs[t] { Some(crate::mle::eq_table_scaled(&p[k..a], pre[t])) } else { None };
            let qr: &[F] = match &qs[t] {
                Q::Tab(q) if k == 0 => q,
                _ => &qk[t],
            };
            let items = split_runs(&runs[t], cs);
            let _sp = crate::prof::span(if le.is_some() { "sc.msg_eq" } else { "sc.msg_tab" });
            let parts = par::map_chunks(items.len(), 1, |lo, hi| {
                let mut g = [F::ZERO; 3];
                for &(f, nc) in &items[lo..hi] {
                    match (&le, &hi_eq[t]) {
                        (Some(le), Some(he)) => {
                            for c in f..f + nc {
                                let r = crate::simd::round_ff(&pr[c * cs..(c + 1) * cs], le);
                                let h = he[c];
                                for j in 0..3 {
                                    g[j] += h * r[j];
                                }
                            }
                        }
                        _ => {
                            let r = crate::simd::round_ff(&pr[f * cs..(f + nc) * cs], &qr[f * cs..(f + nc) * cs]);
                            for j in 0..3 {
                                g[j] += r[j];
                            }
                        }
                    }
                }
                g
            });
            for g in parts {
                for j in 0..3 {
                    msg[j] += g[j];
                }
            }
        }
        let s = chal(msg);
        pt.push(s);
        let half = cs / 2;
        for t in 0..np {
            let mut pn: Vec<F> = par::uninit_vec(pk[t].len() / 2);
            let pp = par::SyncPtr(pn.as_mut_ptr());
            let tab = matches!(qs[t], Q::Tab(_));
            let mut qn: Vec<F> = if tab { par::uninit_vec(pk[t].len() / 2) } else { Vec::new() };
            let qp = par::SyncPtr(qn.as_mut_ptr());
            let (pr, qr): (&[F], &[F]) = (&pk[t], match &qs[t] {
                Q::Tab(q) if k == 0 => q,
                _ => &qk[t],
            });
            let items = split_runs(&runs[t], cs);
            let _sp = crate::prof::span(if tab { "sc.fold_tab" } else { "sc.fold_eq" });
            par::map_chunks(items.len(), 1, |lo, hi| {
                let (pp, qp) = (pp, qp);
                for &(f, nc) in &items[lo..hi] {
                    // SAFETY: the runs are disjoint, so their output ranges are
                    let po = unsafe { std::slice::from_raw_parts_mut(pp.0.add(f * half), nc * half) };
                    crate::simd::fold(&pr[f * cs..(f + nc) * cs], s, po);
                    if tab {
                        let qo = unsafe { std::slice::from_raw_parts_mut(qp.0.add(f * half), nc * half) };
                        crate::simd::fold(&qr[f * cs..(f + nc) * cs], s, qo);
                    }
                }
            });
            pk[t] = pn;
            qk[t] = qn;
            if let Q::Eq(p, _) = &qs[t] {
                pre[t] *= (F::ONE + p[k]) * (F::ONE + s) + p[k] * s;
            }
        }
    }
    drop(sp);
    let sp = crate::prof::span("sc.dead");
    let nc = n >> a;
    let ea = crate::mle::eq_table(&pt[..a]);
    for t in 0..np {
        let mut alive = vec![false; nc];
        for &c in &lives[t] {
            alive[c as usize] = true;
        }
        match &qs[t] {
            Q::Tab(q) => {
                if a == 0 {
                    qk[t] = q.to_vec();
                }
                let (pp, qp) = (par::SyncPtr(pk[t].as_mut_ptr()), par::SyncPtr(qk[t].as_mut_ptr()));
                let alive = &alive;
                par::map_chunks(nc, 1 << 10, |lo, hi| {
                    let (pp, qp) = (pp, qp);
                    for c in lo..hi {
                        if !alive[c] {
                            // SAFETY: each worker writes its own entries `c`
                            unsafe {
                                *pp.0.add(c) = F::ZERO;
                                *qp.0.add(c) = crate::simd::dot(&ea, &q[c << a..(c + 1) << a]);
                            }
                        }
                    }
                });
            }
            Q::Eq(..) => {
                // the folded eq: `pre·eq(pt[a..], c)` for every chunk
                let he = hi_eq[t].as_ref().unwrap();
                qk[t] = par::collect_vec(nc, 1 << 12, |c| pre[t] * he[c]);
                for c in 0..nc {
                    if !alive[c] {
                        pk[t][c] = F::ZERO;
                    }
                }
            }
        }
    }
    drop(sp);
    let _sp = crate::prof::span("sc.tail");
    let (rest, fin) = prove_pairs(pk.into_iter().zip(qk).collect(), chal);
    pt.extend(rest);
    (pt, fin)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `prove_pairs_support` (two pairs, each with its own dead chunks; one closed-form eq side)
    /// sends `prove_pairs`'s messages and ends at its final pairs (E1).
    #[test]
    fn pairs_support_same_messages() {
        let nv = 16usize;
        let n = 1usize << nv;
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let mut rf = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            F::new(s, s.rotate_left(21))
        };
        let p1: Vec<F> = (0..n).map(|i| if (i >> 10) % 3 == 0 { rf() } else { F::ZERO }).collect();
        let p2: Vec<F> = (0..n).map(|i| if (i >> 10) % 5 == 1 { rf() } else { F::ZERO }).collect();
        let q1: Vec<F> = (0..n).map(|_| rf()).collect();
        let pt: Vec<F> = (0..nv).map(|_| rf()).collect();
        let sc = rf();
        let q2 = crate::mle::eq_table_scaled(&pt, sc);
        let mut ch = |seed: u64| {
            let mut x = seed;
            move |g: [F; 3]| {
                x = x.wrapping_mul(6364136223846793005).wrapping_add(1);
                F::new(x ^ g[0].lo, g[2].hi ^ x.rotate_left(7))
            }
        };
        let (r1, f1) = prove_pairs(vec![(p1.clone(), q1.clone()), (p2.clone(), q2.clone())], &mut ch(5));
        for a in [0usize, 1, 2, 4, 6, 10, 12] {
            let (r2, f2) = prove_pairs_support(vec![p1.clone(), p2.clone()], &[Q::Tab(&q1), Q::Eq(&pt, sc)], a, &mut ch(5));
            assert_eq!(r1, r2, "a = {a}");
            assert_eq!(f1, f2, "a = {a}");
        }
    }
    /// `prove_pair_support` sends `prove_pairs`'s messages on a `P` with dead chunks.
    #[test]
    fn pair_support_same_messages() {
        let mut s = 3u64;
        let mut rnd = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let n = 1 << 14;
        let q: Vec<F> = (0..n).map(|_| F::new(rnd(), rnd())).collect();
        let p: Vec<F> = (0..n).map(|i| if (i >> 9) % 3 == 1 || i == 77 { F::new(rnd(), rnd()) } else { F::ZERO }).collect();
        let run = |sup: bool| {
            let mut msgs = Vec::new();
            let mut x = F::new(5, 1);
            let mut chal = |g: [F; 3]| {
                msgs.push(g);
                x = x * x + g[0] + g[2];
                x
            };
            let pt = if sup { prove_pair_support(p.clone(), &q, 8, &mut chal) } else { let (pt, fin) = prove_pairs(vec![(p.clone(), q.clone())], &mut chal); (pt, fin[0]) };
            (pt, msgs)
        };
        let (a, b) = (run(true), run(false));
        let d = (0..a.1.len()).find(|&i| a.1[i] != b.1[i]);
        assert!(a == b, "first differing message {d:?} of {}", a.1.len());
    }
}
