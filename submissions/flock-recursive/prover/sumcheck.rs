//! Degree-2 sumcheck pieces shared by the phases. A round message is `(g(0), g(1), g(∞))` (three
//! coefficients, blueprint §2.3), checked `g(0) + g(1) = claim` and evaluated at the challenge
//! `g(X) = g(0) + (g(0) + g(1) + g(∞))X + g(∞)X²`. Variables are bound low bit first.

use crate::field::{FAcc, F, K};
use crate::par;

pub fn eval2_f(g: [F; 3], x: F) -> F {
    g[0] + (g[0] + g[1] + g[2]) * x + g[2] * x * x
}
pub fn eval2_k(g: [K; 3], x: K) -> K {
    g[0] + (g[0] + g[1] + g[2]) * x + g[2] * x * x
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
pub fn fold_f(t: &[F], s: F) -> Vec<F> {
    let n = t.len() / 2;
    let mut out = vec![F::ZERO; n];
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
