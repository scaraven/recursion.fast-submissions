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
