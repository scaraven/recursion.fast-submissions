//! Ring switching (blueprint rev. 3.9 §2.3 step 6, A.9 `finRS`; `FRRingSwitch`), for several
//! claims at once. A claim on the bit witness is `Σ_v w_v s_v = value` with `s_v = Σ_y g(y) z(y, v)`
//! (`y` the packed index, `v < 128` the bit inside the F element, `g = eq(hi, ·)` the outer weight);
//! the prover sends every claim's slices `s_v`; after `r″ ∈ F^7` and `κ` each claim is switched:
//! `T = Σ_v b_v Φ_{r″}(s_v)` (`b_v` the packing basis, `Φ_{r″}(a) = Σ_{k<128} c_k a^{2^k}` the staged
//! Frobenius map `a ← a + r″_p a^{2^{2^{6−p}}}`, `p = 0 … 6`; `FRRingSwitch.Phi`, `rsT`), true when
//! `Σ_y Φ(g(y)) f(y) = T`. The batched claim `Σ_y W(y) f(y) = Σ_j κ^j T_j`, `W = Σ_j κ^j Φ∘g_j`, is
//! Ligerito's input; the verifier evaluates `Ŵ(ρ) = Σ_j κ^j Σ_k c_k eq(hi_j^{2^k}, ρ)` at the final
//! point (`rs_weight`, the op `rsWeight`; `FRRingSwitch.weightEval`). Rev. 3.9 replaces the
//! tensor-algebra form (`Σ_u eq(r″, u) ŝ_u`, the MBP) of P1–rev. 3.8.

use crate::field::{B64, F, K};
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

/// The packing basis (A.7): `b_v` has the one bit `v` set.
pub fn basis(v: usize) -> F {
    if v < 64 {
        F::new(1u64 << v, 0)
    } else {
        F::new(0, 1u64 << (v - 64))
    }
}

/// `Φ_{r″}(a)`: the stages `a ← a + r″_p · a^{2^{2^{6−p}}}`, `p = 0 … 6` (`phiApply`).
pub fn phi(rpp: &[F], mut a: F) -> F {
    for (p, f) in rpp.iter().enumerate() {
        let mut x = a;
        for _ in 0..1usize << (rpp.len() - 1 - p) {
            x = x.sq();
        }
        a += *f * x;
    }
    a
}

/// The coefficients `c_k` of `Φ_{r″}(a) = Σ_{k<128} c_k a^{2^k}` (`phiTable`).
pub fn phi_coeffs(rpp: &[F]) -> Vec<F> {
    let mut t = vec![F::ONE];
    for f in rpp.iter().rev() {
        let n = t.len();
        let mut fp = *f;
        for e in 0..n {
            let x = t[e] * fp;
            t.push(x);
            fp = fp.sq();
        }
    }
    t
}

/// The switched claim `T = Σ_v b_v Φ_{r″}(s_v)` (`rsT`).
pub fn switched(s: &[F], rpp: &[F]) -> F {
    let mut acc = F::ZERO;
    for (v, sv) in s.iter().enumerate() {
        acc += basis(v) * phi(rpp, *sv);
    }
    acc
}

/// `Φ` as 16 byte tables scaled by `c`: `T[p][val] = c Σ_{i: val_i} Φ(b_{8p+i})` (`Φ` is `F₂`-linear).
pub fn phi_tables(rpp: &[F], c: F) -> Vec<F> {
    let img: Vec<F> = (0..128).map(|v| phi(rpp, basis(v)) * c).collect();
    let mut t = vec![F::ZERO; 16 * 256];
    for p in 0..16 {
        for val in 1..256usize {
            let low = val & val.wrapping_neg();
            t[p * 256 + val] = t[p * 256 + (val ^ low)] + img[8 * p + low.trailing_zeros() as usize];
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

/// The prover's weight table `W(y) = Σ_j c_j Φ(eq(hi_j, y))` for the claims `(hi_j, c_j)` (rev. 3.7:
/// `c_j = κ^j`; claims at the same point are merged by adding their coefficients).
pub fn weight_table(claims: &[(&[F], F)], rpp: &[F]) -> Vec<F> {
    let his: Vec<&[F]> = claims.iter().map(|c| c.0).collect();
    let mu = his[0].len();
    let tabs: Vec<Vec<F>> = claims.iter().map(|c| phi_tables(rpp, c.1)).collect();
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

/// `Ŵ(ρ) = Σ_j c_j Σ_k c_k(r″) eq(hi_j^{2^k}, ρ)` for the claims `(hi_j, c_j)` (`rsWeight`).
pub fn rs_weight(claims: &[(&[F], F)], rpp: &[F], rho: &[K]) -> K {
    let ck = phi_coeffs(rpp);
    let mut out = K::ZERO;
    for (hi, cj) in claims {
        let mut p = hi.to_vec();
        let mut acc = K::ZERO;
        for c in &ck {
            acc += crate::mle::eq_fk(&p, rho).mulf(*c);
            p.iter_mut().for_each(|x| *x = x.sq());
        }
        out += acc.mulf(*cj);
    }
    out
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
    /// `Φ`'s coefficient table agrees with the stages; `Ŵ` by `rs_weight` is the MLE of the
    /// prover's table; the switched claim is true for honest slices.
    #[test]
    fn rs_weight_and_identity() {
        let mut s = 77u64;
        let mu = 5;
        let mut rf = || F::new(rnd(&mut s), rnd(&mut s));
        let rpp: Vec<F> = (0..7).map(|_| rf()).collect();
        let a = rf();
        let ck = phi_coeffs(&rpp);
        assert_eq!(ck.len(), 128);
        let mut x = a;
        let mut want = F::ZERO;
        for c in &ck {
            want += *c * x;
            x = x.sq();
        }
        assert_eq!(phi(&rpp, a), want);
        let hi: Vec<F> = (0..mu).map(|i| if i == 2 { F::ZERO } else { rf() }).collect();
        let kap = rf();
        let w = weight_table(&[(&hi[..], kap)], &rpp);
        let pt: Vec<K> = (0..mu).map(|_| K { a: rf(), b: rf() }).collect();
        let eq = eq_table_k(&pt);
        let mut want = K::ZERO;
        for y in 0..(1 << mu) {
            want += eq[y].mulf(w[y]);
        }
        assert_eq!(rs_weight(&[(&hi[..], kap)], &rpp, &pt), want);
        let z: Vec<u64> = (0..(2usize << mu)).map(|_| rnd(&mut s)).collect();
        let sv = partials(&z, &hi);
        let mut lhs = F::ZERO;
        for y in 0..(1 << mu) {
            lhs += w[y] * F::new(z[2 * y], z[2 * y + 1]);
        }
        assert_eq!(lhs, kap * switched(&sv, &rpp));
    }
}
