//! Ring switching (blueprint §2.3 R, paper App. B.2–B.3), for several claims at once. A claim on
//! the bit witness is `Σ_v w_v s_v = value` with `s_v = Σ_y e(y) z(y, v)` (`y` the packed index,
//! `v < 128` the bit inside the F element, `e = eq(hi, ·)`); the prover sends every claim's `s_v`;
//! after `r″ ∈ F^7` and `κ`, each `s_v` is decomposed over F₂ and recombined (`ŝ_u`, a 128 × 128 bit
//! transpose), and the claims become one linear claim on the packed polynomial
//! `Σ_y W(y) f(y) = Σ_j κ^j Σ_u eq(r″, u) ŝ⁽ʲ⁾_u` with `W(y) = Σ_j κ^j Φ(e_j(y))`, `Φ(b_u) = eq(r″, u)`.
//! **P1 choice**: that claim is the input of the Ligerito opening directly (its weight `Ŵ` is
//! evaluated by the verifier at Ligerito's final point by the width-128 matrix branching program),
//! instead of rev. 2's separate `m − 7`-round R sumcheck to an `f̂(r_f)` claim.

use crate::field::{FAcc, B64, F, K};
use crate::mle::eq_table;
use crate::par;

pub struct Claim {
    /// coordinates of the packed variables `y₀ … y_{m−8}` (bit-index variables `x₇ …`)
    pub hi: Vec<F>,
    /// the weights `w_v` of the partials
    pub w: Vec<F>,
    pub value: F,
}

/// `s_v = Σ_y eq(hi, y) bit_v(f[y])`, by 16 byte-tables per chunk (four Russians).
pub fn partials(z: &[u64], hi: &[F]) -> Vec<F> {
    let ny = z.len() / 2;
    assert_eq!(ny, 1 << hi.len());
    let nlo = hi.len().min(10);
    let elo = eq_table(&hi[..nlo]);
    let ehi = eq_table(&hi[nlo..]);
    let bytes = crate::witness::Witness::bytes(z);
    let parts = par::map_chunks(ehi.len(), 1, |a, b| {
        let mut acc = vec![F::ZERO; 16 * 256];
        let mut e = vec![F::ZERO; elo.len()];
        for h in a..b {
            if ehi[h].is_zero() {
                continue;
            }
            e.iter_mut().for_each(|x| *x = F::ZERO);
            crate::simd::axpy(&mut e, &elo, ehi[h]);
            for l in 0..elo.len() {
                if elo[l].is_zero() {
                    continue;
                }
                let y = l | (h << nlo);
                let fb = &bytes[16 * y..16 * y + 16];
                let el = e[l];
                for p in 0..16 {
                    acc[p * 256 + fb[p] as usize] += el;
                }
            }
        }
        acc
    });
    let mut acc = vec![F::ZERO; 16 * 256];
    for p in parts {
        for i in 0..acc.len() {
            acc[i] += p[i];
        }
    }
    let mut s = vec![F::ZERO; 128];
    for p in 0..16 {
        for val in 1..256usize {
            let a = acc[p * 256 + val];
            for i in 0..8 {
                if (val >> i) & 1 == 1 {
                    s[8 * p + i] += a;
                }
            }
        }
    }
    s
}

/// `ŝ_u = Σ_v bit_u(s_v) b_v` (the 128 × 128 bit transpose).
pub fn recombine(s: &[F]) -> Vec<F> {
    let mut out = vec![F::ZERO; 128];
    for (v, sv) in s.iter().enumerate() {
        for u in 0..128 {
            if sv.bit(u) {
                if v < 64 {
                    out[u].lo |= 1u64 << v;
                } else {
                    out[u].hi |= 1u64 << (v - 64);
                }
            }
        }
    }
    out
}

/// `Σ_u eq(r″, u) ŝ_u` (the batched target of one claim).
pub fn target(s: &[F], rpp: &[F]) -> F {
    let e = eq_table(rpp);
    let sh = recombine(s);
    let mut acc = FAcc::default();
    for u in 0..128 {
        acc.mac(e[u], sh[u]);
    }
    acc.reduce()
}

/// `Φ` as 16 byte tables scaled by `c`: `T[p][val] = c Σ_{i: val_i} eq(r″, 8p + i)`.
pub fn phi_tables(rpp: &[F], c: F) -> Vec<F> {
    let e = eq_table(rpp);
    let mut t = vec![F::ZERO; 16 * 256];
    for p in 0..16 {
        for val in 1..256usize {
            let low = val & val.wrapping_neg();
            t[p * 256 + val] = t[p * 256 + (val ^ low)] + e[8 * p + low.trailing_zeros() as usize] * c;
        }
    }
    t
}

#[inline(always)]
pub fn phi_apply(t: &[F], x: F) -> F {
    let b = x.to_bytes();
    let mut acc = F::ZERO;
    for p in 0..16 {
        acc += t[p * 256 + b[p] as usize];
    }
    acc
}

/// The prover's weight table `W(y) = Σ_j κ^j Φ(eq(hi_j, y))`.
pub fn weight_table(his: &[&[F]], rpp: &[F], kappa: F) -> Vec<F> {
    let mu = his[0].len();
    let mut tabs = Vec::new();
    let mut c = F::ONE;
    for _ in his {
        tabs.push(phi_tables(rpp, c));
        c *= kappa;
    }
    let nlo = mu.min(10);
    let splits: Vec<(Vec<F>, Vec<F>)> = his.iter().map(|h| (eq_table(&h[..nlo]), eq_table(&h[nlo..]))).collect();
    let nhi = 1usize << (mu - nlo);
    let mut out = vec![F::ZERO; 1 << mu];
    par::for_each_chunk_mut(&mut out, 1 << nlo, |off, ch| {
        let mut e = vec![F::ZERO; 1 << nlo];
        for (bi, blk) in ch.chunks_mut(1 << nlo).enumerate() {
            let h = (off >> nlo) + bi;
            debug_assert!(h < nhi);
            for (j, (elo, ehi)) in splits.iter().enumerate() {
                if ehi[h].is_zero() {
                    continue;
                }
                e.iter_mut().for_each(|x| *x = F::ZERO);
                crate::simd::axpy(&mut e, elo, ehi[h]);
                for l in 0..blk.len() {
                    if !elo[l].is_zero() {
                        blk[l] += phi_apply(&tabs[j], e[l]);
                    }
                }
            }
        }
    });
    out
}

/// The verifier's `B̂(pt) = Σ_u eq(r″, u) a_u` for the claim with point `hi`, by the width-128 matrix
/// branching program over `K ⊗ F`: start `a = e₀` (the element 1), each layer
/// `a ← (1 + pt_i) a + a·hi_i` (the second term multiplies the F factor by `hi_i`: an F₂-matrix).
pub fn mbp(hi: &[F], pt: &[K], rpp: &[F]) -> K {
    assert_eq!(hi.len(), pt.len());
    let mut a = vec![K::ZERO; 128];
    a[0] = K::ONE;
    let mut nxt = vec![K::ZERO; 128];
    for (h, p) in hi.iter().zip(pt.iter()) {
        let sc = K::ONE + *p;
        for u in 0..128 {
            nxt[u] = a[u] * sc;
        }
        if !h.is_zero() {
            for u in 0..128 {
                if a[u] == K::ZERO {
                    continue;
                }
                // b_u · h as an F element: its set bits u' receive a_u
                let bu = if u < 64 { F::new(1u64 << u, 0) } else { F::new(0, 1u64 << (u - 64)) };
                let v = bu * *h;
                let mut lo = v.lo;
                while lo != 0 {
                    let t = lo.trailing_zeros() as usize;
                    nxt[t] += a[u];
                    lo &= lo - 1;
                }
                let mut hb = v.hi;
                while hb != 0 {
                    let t = hb.trailing_zeros() as usize;
                    nxt[64 + t] += a[u];
                    hb &= hb - 1;
                }
            }
        }
        std::mem::swap(&mut a, &mut nxt);
    }
    let e = eq_table(rpp);
    let mut r = K::ZERO;
    for u in 0..128 {
        r += a[u].mulf(e[u]);
    }
    r
}

/// `x` as a BF64 if it is one (tests).
pub fn _b(x: F) -> Option<B64> {
    (x.hi == 0).then_some(B64(x.lo))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mle::eq_table_k;
    fn rnd(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }
    /// `B̂` by the MBP equals the MLE of the prover's table, and the batched identity holds.
    #[test]
    fn mbp_and_identity() {
        let mut s = 77u64;
        let mu = 5;
        let mut rf = || F::new(rnd(&mut s), rnd(&mut s));
        let hi: Vec<F> = (0..mu).map(|i| if i == 2 { F::ZERO } else { rf() }).collect();
        let rpp: Vec<F> = (0..7).map(|_| rf()).collect();
        let w = weight_table(&[&hi], &rpp, F::ONE);
        let pt: Vec<K> = (0..mu).map(|_| K { a: rf(), b: rf() }).collect();
        let eq = eq_table_k(&pt);
        let mut want = K::ZERO;
        for y in 0..(1 << mu) {
            want += eq[y].mulf(w[y]);
        }
        assert_eq!(mbp(&hi, &pt, &rpp), want);
        // identity: Σ_y W(y) f(y) = target(s)
        let z: Vec<u64> = (0..(2usize << mu)).map(|_| rnd(&mut s)).collect();
        let sv = partials(&z, &hi);
        let mut lhs = F::ZERO;
        for y in 0..(1 << mu) {
            lhs += w[y] * F::new(z[2 * y], z[2 * y + 1]);
        }
        assert_eq!(lhs, target(&sv, &rpp));
    }
}
