//! Sumcheck pieces shared by the phases. The provers compute a degree-2 round as `(g(0), g(1),
//! g(∞))`; the message is the coefficients `c₀ ‖ c₁ ‖ c₂` of `g(X) = c₀ + c₁X + c₂X²` (A.2, `gen`'s
//! `roundOpsF`/`roundOpsK`), checked `c₁ + c₂ = claim` (that is `g(0) + g(1) = claim`) and evaluated
//! `c₀ + r(c₁ + r c₂)`. A degree-3 round sends `c₀ ‖ c₁ ‖ c₂` and the verifier completes
//! `c₃ = claim + c₁ + c₂`. Variables are bound low bit first.

use crate::field::{FAcc, F, K};
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
    let parts = par::map_chunks(n, 1 << 12, |lo, hi| {
        let (mut a0, mut a1, mut ai) = (FAcc::default(), FAcc::default(), FAcc::default());
        for (p, q) in pairs {
            for i in lo..hi {
                let (p0, p1, q0, q1) = (p[2 * i], p[2 * i + 1], q[2 * i], q[2 * i + 1]);
                a0.mac(p0, q0);
                a1.mac(p1, q1);
                ai.mac(p0 + p1, q0 + q1);
            }
        }
        (a0, a1, ai)
    });
    let (mut a0, mut a1, mut ai) = (FAcc::default(), FAcc::default(), FAcc::default());
    for (x, y, z) in parts {
        a0.add(&x);
        a1.add(&y);
        ai.add(&z);
    }
    [a0.reduce(), a1.reduce(), ai.reduce()]
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
/// lives on the M slots, the L bits and the one cell; pass 10). The tables are cut into aligned
/// chunks of `2^a` entries. In the first `a` rounds a chunk where `P` is zero adds nothing to a
/// message and its `P` stays zero, so only the live chunks are summed and folded. A dead chunk's
/// `Q` still enters the later rounds (paired with a live entry, through `(P₀ + P₁)(Q₀ + Q₁)` and the
/// folds), so after round `a` it is computed directly as `Σ_l eq(r_{<a}, l) Q[2^a c + l]`; the
/// remaining rounds are `prove_pairs`'s. The messages and challenges are `prove_pairs`'s (test
/// `pair_support_same_messages`), and so is the final pair. `Q` is borrowed (no copy).
pub fn prove_pair_support(p: Vec<F>, q: &[F], a: usize, chal: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, (F, F)) {
    let n = p.len();
    assert!(q.len() == n && n.is_power_of_two());
    let a = a.min(n.trailing_zeros() as usize);
    let live: Vec<u32> = par::map_chunks(n >> a, 64, |lo, hi| (lo..hi).filter(|&c| p[c << a..(c + 1) << a].iter().any(|x| !x.is_zero())).map(|c| c as u32).collect::<Vec<u32>>()).concat();
    let mut pt = Vec::with_capacity(n.trailing_zeros() as usize);
    let (mut pk, mut qk): (Vec<F>, Vec<F>) = (p, Vec::new());
    for k in 0..a {
        let cs = 1usize << (a - k);
        let (pr, qr): (&[F], &[F]) = (&pk, if k == 0 { q } else { &qk });
        let parts = par::map_chunks(live.len(), 1, |lo, hi| {
            let (mut a0, mut a1, mut ai) = (FAcc::default(), FAcc::default(), FAcc::default());
            for &c in &live[lo..hi] {
                let b = c as usize * cs;
                for i in (b..b + cs).step_by(2) {
                    let (p0, p1, q0, q1) = (pr[i], pr[i + 1], qr[i], qr[i + 1]);
                    a0.mac(p0, q0);
                    a1.mac(p1, q1);
                    ai.mac(p0 + p1, q0 + q1);
                }
            }
            (a0, a1, ai)
        });
        let (mut a0, mut a1, mut ai) = (FAcc::default(), FAcc::default(), FAcc::default());
        for (x, y, z) in parts {
            a0.add(&x);
            a1.add(&y);
            ai.add(&z);
        }
        let s = chal([a0.reduce(), a1.reduce(), ai.reduce()]);
        pt.push(s);
        let half = cs / 2;
        let mut pn: Vec<F> = par::uninit_vec(pr.len() / 2);
        let mut qn: Vec<F> = par::uninit_vec(pr.len() / 2);
        let (pp, qp) = (par::SyncPtr(pn.as_mut_ptr()), par::SyncPtr(qn.as_mut_ptr()));
        par::map_chunks(live.len(), 1, |lo, hi| {
            let (pp, qp) = (pp, qp);
            for &c in &live[lo..hi] {
                let c = c as usize;
                // SAFETY: the live chunks are distinct, so their output ranges are disjoint
                let (po, qo) = unsafe { (std::slice::from_raw_parts_mut(pp.0.add(c * half), half), std::slice::from_raw_parts_mut(qp.0.add(c * half), half)) };
                crate::simd::fold(&pr[c * cs..(c + 1) * cs], s, po);
                crate::simd::fold(&qr[c * cs..(c + 1) * cs], s, qo);
            }
        });
        pk = pn;
        qk = qn;
    }
    // one entry per chunk now: a dead one is `P = 0` and `Q`'s fold over its chunk
    let nc = n >> a;
    if a == 0 {
        qk = q.to_vec();
    }
    let mut alive = vec![false; nc];
    for &c in &live {
        alive[c as usize] = true;
    }
    let ea = crate::mle::eq_table(&pt[..a]);
    let (pp, qp) = (par::SyncPtr(pk.as_mut_ptr()), par::SyncPtr(qk.as_mut_ptr()));
    par::run(par::threads().min(nc), &|w| {
        let (pp, qp) = (pp, qp);
        for c in (w * nc / par::threads().min(nc))..((w + 1) * nc / par::threads().min(nc)) {
            if !alive[c] {
                // SAFETY: each worker writes its own entries `c`
                unsafe {
                    *pp.0.add(c) = F::ZERO;
                    *qp.0.add(c) = crate::simd::dot(&ea, &q[c << a..(c + 1) << a]);
                }
            }
        }
    });
    let (rest, fin) = prove_pairs(vec![(pk, qk)], chal);
    pt.extend(rest);
    (pt, fin[0])
}

/// The dense side of a pair in `prove_pairs_support`: a table, or `scale·eq(pt, ·)` in closed form
/// (never materialized: within a chunk it is a small eq table times the chunk's high factor).
pub enum Q<'a> {
    Tab(&'a [F]),
    Eq(&'a [F], F),
}

/// `prove_pair_support` for several pairs `(P_t, Q_t)`, `P_t` zero outside a few regions (the node's
/// E4 with RSV2's child term: `(W, f)` and `(G, κ_E⁴·eq(p_y, ·))`): each pair's own live chunks (where
/// its `P_t` is nonzero) are summed and folded in the first `a` rounds, its dead ones enter after
/// round `a` as `prove_pair_support`'s; the messages and challenges are `prove_pairs`'s.
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
    let lives: Vec<Vec<u32>> = ps.iter().map(|p| par::map_chunks(n >> a, 64, |lo, hi| (lo..hi).filter(|&c| p[c << a..(c + 1) << a].iter().any(|x| !x.is_zero())).map(|c| c as u32).collect::<Vec<u32>>()).concat()).collect();
    let mut pt: Vec<F> = Vec::with_capacity(nv);
    let mut pk: Vec<Vec<F>> = ps;
    let mut qk: Vec<Vec<F>> = vec![Vec::new(); np];
    // a closed-form Q's chunk factors `eq(pt[a..], c)` and its running prefix `Π_{t<k} eq(pt_t, s_t)`
    let hi_eq: Vec<Option<Vec<F>>> = qs.iter().map(|q| if let Q::Eq(p, sc) = q { Some(crate::mle::eq_table_scaled(&p[a..], *sc)) } else { None }).collect();
    let mut pre: Vec<F> = vec![F::ONE; np];
    for k in 0..a {
        let cs = 1usize << (a - k);
        let (mut a0, mut a1, mut ai) = (FAcc::default(), FAcc::default(), FAcc::default());
        for t in 0..np {
            let live = &lives[t];
            let pr: &[F] = &pk[t];
            let le: Option<Vec<F>> = if let Q::Eq(p, _) = &qs[t] { Some(crate::mle::eq_table_scaled(&p[k..a], pre[t])) } else { None };
            let qr: &[F] = match &qs[t] {
                Q::Tab(q) if k == 0 => q,
                _ => &qk[t],
            };
            let parts = par::map_chunks(live.len(), 1, |lo, hi| {
                let (mut a0, mut a1, mut ai) = (FAcc::default(), FAcc::default(), FAcc::default());
                for &c in &live[lo..hi] {
                    let b = c as usize * cs;
                    match (&le, &hi_eq[t]) {
                        (Some(le), Some(he)) => {
                            let h = he[c as usize];
                            for i in (0..cs).step_by(2) {
                                let (p0, p1, q0, q1) = (pr[b + i], pr[b + i + 1], h * le[i], h * le[i + 1]);
                                a0.mac(p0, q0);
                                a1.mac(p1, q1);
                                ai.mac(p0 + p1, q0 + q1);
                            }
                        }
                        _ => {
                            for i in (b..b + cs).step_by(2) {
                                let (p0, p1, q0, q1) = (pr[i], pr[i + 1], qr[i], qr[i + 1]);
                                a0.mac(p0, q0);
                                a1.mac(p1, q1);
                                ai.mac(p0 + p1, q0 + q1);
                            }
                        }
                    }
                }
                (a0, a1, ai)
            });
            for (x, y, z) in parts {
                a0.add(&x);
                a1.add(&y);
                ai.add(&z);
            }
        }
        let s = chal([a0.reduce(), a1.reduce(), ai.reduce()]);
        pt.push(s);
        let half = cs / 2;
        for t in 0..np {
            let live = &lives[t];
            let mut pn: Vec<F> = par::uninit_vec(pk[t].len() / 2);
            let pp = par::SyncPtr(pn.as_mut_ptr());
            let tab = matches!(qs[t], Q::Tab(_));
            let mut qn: Vec<F> = if tab { par::uninit_vec(pk[t].len() / 2) } else { Vec::new() };
            let qp = par::SyncPtr(qn.as_mut_ptr());
            let (pr, qr): (&[F], &[F]) = (&pk[t], match &qs[t] {
                Q::Tab(q) if k == 0 => q,
                _ => &qk[t],
            });
            par::map_chunks(live.len(), 1, |lo, hi| {
                let (pp, qp) = (pp, qp);
                for &c in &live[lo..hi] {
                    let c = c as usize;
                    // SAFETY: the live chunks are distinct, so their output ranges are disjoint
                    let po = unsafe { std::slice::from_raw_parts_mut(pp.0.add(c * half), half) };
                    crate::simd::fold(&pr[c * cs..(c + 1) * cs], s, po);
                    if tab {
                        let qo = unsafe { std::slice::from_raw_parts_mut(qp.0.add(c * half), half) };
                        crate::simd::fold(&qr[c * cs..(c + 1) * cs], s, qo);
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
                par::run(par::threads().min(nc), &|w| {
                    let (pp, qp) = (pp, qp);
                    for c in (w * nc / par::threads().min(nc))..((w + 1) * nc / par::threads().min(nc)) {
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
        for a in [0usize, 6, 10, 12] {
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
