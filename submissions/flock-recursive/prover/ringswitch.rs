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
    let cl: Vec<(&[F], F, Option<&[F]>)> = claims.iter().map(|c| (c.0, c.1, None)).collect();
    weight_table_kf(&cl, rpp)
}

/// `weight_table` with an optional per-block factor per claim (a node's Lc claim, revision 3.16:
/// the outer weight `eq(hi, y)·kf(y >> 7)`, `kf` per block of 128 packed elements; `Φ` is only
/// `F₂`-linear, so the factor multiplies `eq` before `Φ`). By row tables (`weight_table_rows`).
pub fn weight_table_kf(claims: &[(&[F], F, Option<&[F]>)], rpp: &[F]) -> Vec<F> {
    let lo = std::env::var("FLOCK_RS_LO").ok().and_then(|x| x.parse().ok()).unwrap_or(ROW_LO);
    weight_table_rows(claims, rpp, lo)
}

/// The low variables of a row in `weight_table_rows` (64 elements, 1 KiB; pass 11, was 4).
pub const ROW_LO: usize = 6;

/// **The weight table by row tables** (pass 10). Split `y = l + 2^lo·h` (`l < 2^lo`): a claim's
/// entry is `c Φ(e_lo(l)·e_hi(h))` with `e_lo = eq(hi[..lo], ·)`, `e_hi = eq(hi[lo..], ·)` (times
/// `kf` per block). `a ↦ c Φ(e_lo(l)·a)` is `F₂`-linear, so with the 16 bytes `β_p` of `e_hi(h)`
/// the row `W(·, h)` is `Σ_p Q[p][β_p][·]`, where `Q[p][β][l] = Σ_{i ∈ β} c Φ(e_lo(l)·b_{8p+i})`
/// (16 · 256 rows of `2^lo` elements per claim, built from `128 · 2^lo` values of `Φ`). Every
/// output element is 16 row entries per claim read in order, where `weight_table_kf_ref` reads 16
/// scattered entries of a 64 KiB table (one cache line each) and needs a product per element.
/// Rows with `e_hi(h) = 0` (the shift claim's zero coordinates) are skipped.
pub fn weight_table_rows(claims: &[(&[F], F, Option<&[F]>)], rpp: &[F], lo: usize) -> Vec<F> {
    let mu = claims[0].0.len();
    let lo = lo.min(mu).min(7);
    let nl = 1usize << lo;
    // the claims' tables in parallel (each `16·256·2^lo` elements)
    let tabs: Vec<(Vec<F>, Vec<F>)> = par::collect_vec(claims.len(), 1, |ci| {
        let (hi, c, kf) = &claims[ci];
        {
            assert_eq!(hi.len(), mu);
            let elo = eq_table(&hi[..lo]);
            let mut ehi = eq_table(&hi[lo..]);
            if let Some(kf) = kf {
                // a block (128 elements) is 2^(7 − lo) rows
                let sh = 7 - lo;
                par::for_each_chunk_mut(&mut ehi, 1 << 12, |off, ch| {
                    for (i, x) in ch.iter_mut().enumerate() {
                        *x *= kf[(off + i) >> sh];
                    }
                });
            }
            let t = phi_tables(rpp, *c);
            let mut q = vec![F::ZERO; 16 * 256 * nl];
            for (l, el) in elo.iter().enumerate() {
                if el.is_zero() {
                    continue;
                }
                let img: Vec<F> = (0..128).map(|v| phi_apply(&t, *el * basis(v))).collect();
                for p in 0..16 {
                    for val in 1..256usize {
                        let low = val & val.wrapping_neg();
                        q[(p * 256 + val) * nl + l] = q[(p * 256 + (val ^ low)) * nl + l] + img[8 * p + low.trailing_zeros() as usize];
                    }
                }
            }
            (q, ehi)
        }
    });
    let mut out: Vec<F> = par::uninit_vec(1 << mu);
    par::for_each_chunk_mut(&mut out, nl.max(1 << 10), |off, ch| {
        let mut offs = [0usize; 16];
        for (bi, row) in ch.chunks_mut(nl).enumerate() {
            let h = (off >> lo) + bi;
            row.iter_mut().for_each(|x| *x = F::ZERO);
            for (q, ehi) in &tabs {
                let e = ehi[h];
                if e.is_zero() {
                    continue;
                }
                let b = e.to_bytes();
                for p in 0..16 {
                    offs[p] = (p * 256 + b[p] as usize) * nl;
                }
                crate::simd::xor_rows(q, &offs, row);
            }
        }
    });
    out
}

/// The reference weight table (pass 6–9): per element `e = e_lo·e_hi`, then `Φ` by 16 byte tables.
pub fn weight_table_kf_ref(claims: &[(&[F], F, Option<&[F]>)], rpp: &[F]) -> Vec<F> {
    let his: Vec<&[F]> = claims.iter().map(|c| c.0).collect();
    let mu = his[0].len();
    let tabs: Vec<Vec<F>> = claims.iter().map(|c| phi_tables(rpp, c.1)).collect();
    let nlo = mu.min(10);
    let splits: Vec<(Vec<F>, Vec<F>)> = his.iter().map(|h| (eq_table(&h[..nlo]), eq_table(&h[nlo..]))).collect();
    let nhi = 1usize << (mu - nlo);
    // the positions where elo_j ≠ 0 (Φ(0) = 0: the others add nothing)
    let nz: Vec<Vec<u32>> = splits.iter().map(|(elo, _)| (0..elo.len() as u32).filter(|&l| !elo[l as usize].is_zero()).collect()).collect();
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("  weight_table nonzero lo entries {:?} of {}", nz.iter().map(|v| v.len()).collect::<Vec<_>>(), 1usize << nlo);
    }
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
                if 4 * nz[j].len() < e.len() {
                    // a sparse elo (the shift claim: 64 of 1,024): the products at its support only
                    for &l in &nz[j] {
                        e[l as usize] = elo[l as usize] * ehi[h];
                    }
                } else {
                    e.iter_mut().for_each(|x| *x = F::ZERO);
                    crate::simd::axpy(&mut e, elo, ehi[h]);
                }
                if let Some(kf) = claims[j].2 {
                    // y = (h << nlo) | l, block y >> 7
                    for &l in &nz[j] {
                        e[l as usize] *= kf[((h << nlo) | l as usize) >> 7];
                    }
                }
                if blk.len() == e.len() {
                    crate::simd::phi_add_idx(&tabs[j], &e, &nz[j], blk);
                } else {
                    let idx: Vec<u32> = nz[j].iter().copied().filter(|&l| (l as usize) < blk.len()).collect();
                    crate::simd::phi_add_idx(&tabs[j], &e, &idx, blk);
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

// ---------------------------------------------------------------- the direct open (lever G1)
//
// Ligerito's level 0 folds the `DLO = 6` low variables `l` of the packed index `y = l + 64h` first
// (`ROW_LOG[0]`). A claim's weight is `W_j(l, h) = c_j Φ(eqlo(l)·ehi(h))` with `eqlo = eq(hi[..6], ·)`
// and `ehi = eq(hi[6..], ·)` (times the node's `kf(h >> 1)`), and `Φ` is `F₂`-linear, so
// `W_j(l, h) = Σ_β bit_β(ehi(h)) Wst[β, l]` with `Wst[β, l] = c_j Φ(eqlo(l)·b_β)`. Hence
// `Σ_h W_j(l, h) g(l′, h) = Σ_β Wst[β, l] A[β, l′]` with the banked statistic
// `A[β, l′] = Σ_h bit_β(ehi(h)) f(l′, h)`, the bit transpose of `M_{l′}[γ] = Σ_h ehi(h) bit_γ(f(l′, h))`,
// which is the block partial fold `Z(t) = Σ_blk eblk(blk) z(blk, t)` (`t = 128 y_in + γ`) read at
// `y_in = l′ + 64 b₆` and combined over `b₆` by `eq(hi[6], b₆)`. The 6 rounds then run on 128 banks
// of 64 entries per claim (`ligerito::rounds_direct`), never touching `W`'s 2^(m−7) entries; after
// them the folded weight is `wk[h] = Σ_j Ψ_j(ehi_j(h))`, `Ψ_j(b_β) = W̃st[β](s)` (16 byte tables),
// and `f` is folded once by `eq(s, ·)` (one 64 → 1 pass). Every quantity is the field element the
// table path computes, so `π` is unchanged (Flock `docs/yukon-optimizations.tex` §directopen,
// §directopenrefine, §statsladder; re-derived for this weight).

/// The variables of level 0 that the direct open folds (`params::ROW_LOG[0]`).
pub const DLO: usize = 6;

/// One claim of the direct open.
pub struct DClaim {
    /// `wst[64β + l] = c Φ(eqlo(l)·b_β)`.
    pub wst: Vec<F>,
    /// `a[64β + l] = Σ_h bit_β(ehi(h)) f(l, h)`.
    pub a: Vec<F>,
    /// The coordinates of `h` (`hi[6..]`).
    pub hh: Vec<F>,
    /// The per-block factor (`kf[h >> 1]`), if any.
    pub kf: Option<Vec<F>>,
    /// `k₀ ≤ DLO`: `hi[k₀..DLO] = 0`, so `W` lives on `l < 2^k₀` and `A` is kept for those `l`
    /// only (Sh's claim: `k₀ = 3`, its block fold is the shift's 16-word prefix `zs`). Rounds
    /// `r ≥ k₀` take this claim's message from `f` directly (`ligerito::rounds_direct`).
    pub k0: usize,
}

/// The level-0 weight of the direct open: the claims and the sparse point weights `(y, p)` (a node's
/// public cells).
pub struct Direct {
    pub claims: Vec<DClaim>,
    pub cells: Vec<(usize, F)>,
}

/// The direct open is the default; `FLOCK_NO_OPEN_DIRECT=1` (or `set_direct(false)` on the calling
/// thread) restores the weight table (`weight_table_kf`), for A/B runs and tests.
pub fn direct_on() -> bool {
    static ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let env = *ENV.get_or_init(|| std::env::var_os("FLOCK_NO_OPEN_DIRECT").is_none());
    DIRECT.with(|d| d.get().unwrap_or(env))
}

thread_local! {
    static DIRECT: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

/// Force the direct open on or off on this thread (tests).
pub fn set_direct(on: Option<bool>) {
    DIRECT.with(|d| d.set(on));
}

/// A claim of the direct open from its point `hi` (`μ` coordinates), coefficient `c`, per-block
/// factor `kf`, and its block fold `zf` (`Z(t)` at `hi[7..]`, times `kf`, for `t < zf.len()`; the
/// positions `≥ 8192` are needed only when `hi[6] ≠ 0`).
pub fn dclaim(hi: &[F], c: F, kf: Option<&[F]>, zf: &[F], rpp: &[F]) -> DClaim {
    assert!(hi.len() > DLO + 1 && zf.len() >= 128 && zf.len().is_power_of_two());
    let e6 = [F::ONE + hi[DLO], hi[DLO]];
    assert!(zf.len() >= 1 << 14 || e6[1].is_zero(), "dclaim: the block fold misses y_in ≥ 64");
    // a fold shorter than 64 elements: the claim must vanish beyond them (`hi[k₀..DLO] = 0`)
    let k0 = (zf.len() / 128).trailing_zeros().min(DLO as u32) as usize;
    assert!(hi[k0..DLO].iter().all(|x| x.is_zero()), "dclaim: the block fold misses y_in ≥ 2^k0");
    let eqlo = eq_table(&hi[..DLO]);
    let t = phi_tables(rpp, c);
    // per l: the column `Wst[·, l]` and the column `A[·, l]` (the bit transpose of `M_l`)
    let cols: Vec<(Vec<F>, Vec<F>)> = par::collect_vec(64, 1, |l| {
        let mut w = vec![F::ZERO; 128];
        if !eqlo[l].is_zero() {
            for (b, x) in w.iter_mut().enumerate() {
                *x = phi_apply(&t, eqlo[l] * basis(b));
            }
        }
        let mut ml = [F::ZERO; 128];
        for (b6, e) in e6.iter().enumerate() {
            if e.is_zero() || l >> k0 != 0 {
                continue;
            }
            let o = 128 * (l + 64 * b6);
            for (g, x) in ml.iter_mut().enumerate() {
                *x += *e * zf[o + g];
            }
        }
        let mut a = vec![F::ZERO; 128];
        for (g, x) in ml.iter().enumerate() {
            let (gw, gb) = (g >> 6, 1u64 << (g & 63));
            for (wi, mut word) in [x.lo, x.hi].into_iter().enumerate() {
                while word != 0 {
                    let b = 64 * wi + word.trailing_zeros() as usize;
                    if gw == 0 {
                        a[b].lo ^= gb;
                    } else {
                        a[b].hi ^= gb;
                    }
                    word &= word - 1;
                }
            }
        }
        (w, a)
    });
    let mut wst = vec![F::ZERO; 128 * 64];
    let mut a = vec![F::ZERO; 128 * 64];
    for (l, (w, x)) in cols.iter().enumerate() {
        for b in 0..128 {
            wst[64 * b + l] = w[b];
            a[64 * b + l] = x[b];
        }
    }
    DClaim { wst, a, hh: hi[DLO..].to_vec(), kf: kf.map(|k| k.to_vec()), k0 }
}

/// `Ψ`'s 16 byte tables for the bank weights `w` (`Ψ(b_β) = w[β·stride]`, `β < 128`).
pub fn psi_tables(w: &[K], stride: usize) -> Vec<K> {
    let mut t = vec![K::ZERO; 16 * 256];
    for p in 0..16 {
        for val in 1..256usize {
            let low = val & val.wrapping_neg();
            t[p * 256 + val] = t[p * 256 + (val ^ low)] + w[(8 * p + low.trailing_zeros() as usize) * stride];
        }
    }
    t
}

#[inline(always)]
pub fn psi_apply(t: &[K], e: F) -> K {
    let b = e.to_bytes();
    let mut acc = K::ZERO;
    for p in 0..16 {
        acc += t[p * 256 + b[p] as usize];
    }
    acc
}

/// `ehi(h) = eq(hh, h)·kf(h >> 1)` by split tables.
pub struct Ehi<'a> {
    lo: Vec<F>,
    hi: Vec<F>,
    nlo: usize,
    kf: Option<&'a [F]>,
}
impl<'a> Ehi<'a> {
    pub fn new(c: &'a DClaim) -> Ehi<'a> {
        let nlo = c.hh.len().min(10);
        Ehi { lo: eq_table(&c.hh[..nlo]), hi: eq_table(&c.hh[nlo..]), nlo, kf: c.kf.as_deref() }
    }
    #[inline(always)]
    pub fn at(&self, h: usize) -> F {
        let eh = self.hi[h >> self.nlo];
        if eh.is_zero() {
            return F::ZERO;
        }
        let e = self.lo[h & ((1 << self.nlo) - 1)] * eh;
        match self.kf {
            Some(k) => e * k[h >> 1],
            None => e,
        }
    }
}

/// The folded weight `wk[h] = Σ_j Ψ_j(ehi_j(h)) + Σ_{cells at h} cw` (`nh` entries): `ws[j]` are claim
/// `j`'s 128 folded bank weights `W̃st[β](s)`, `cw` the cells' folded weights `(h, value)`.
pub fn folded_weight(claims: &[DClaim], ws: &[&[K]], cells: &[(usize, K)], nh: usize) -> Vec<K> {
    let mut wk: Vec<K> = par::uninit_vec(nh);
    par::for_each_chunk_mut(&mut wk, 1 << 12, |_, ch| ch.iter_mut().for_each(|x| *x = K::ZERO));
    for (c, w) in claims.iter().zip(ws.iter()) {
        assert_eq!(1usize << c.hh.len(), nh);
        let t = psi_tables(w, 1);
        let eh = Ehi::new(c);
        par::for_each_chunk_mut(&mut wk, 1 << 12, |off, ch| {
            for (i, x) in ch.iter_mut().enumerate() {
                let e = eh.at(off + i);
                if !e.is_zero() {
                    *x += psi_apply(&t, e);
                }
            }
        });
    }
    for &(h, v) in cells {
        wk[h] += v;
    }
    wk
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

    /// The direct open's identities (lever G1) against the weight table: the banked statistics give
    /// `Σ_h W(l, h) f(l′, h)` for every `(l, l′)`, and `folded_weight` is `W` folded at `s` (a dense
    /// claim, one with a per-block factor, one with zero coordinates, and that one from the 16-word
    /// prefix fold as Sh's).
    #[test]
    fn direct_open_identities() {
        let mut s = 123u64;
        let mut rf = || F::new(rnd(&mut s), rnd(&mut s));
        let mu = 18; // m = 25: 2^11 blocks of 128 elements
        let rpp: Vec<F> = (0..7).map(|_| rf()).collect();
        let h0: Vec<F> = (0..mu).map(|_| rf()).collect();
        let h1: Vec<F> = (0..mu).map(|_| rf()).collect();
        let h2: Vec<F> = (0..mu).map(|i| if (3..7).contains(&i) { F::ZERO } else { rf() }).collect();
        let kf: Vec<F> = (0..1usize << (mu - 7)).map(|_| rf()).collect();
        let cs = [rf(), rf(), rf()];
        let mut s2 = 99u64;
        let z: Vec<u64> = (0..(2usize << mu)).map(|i| if (i >> 8) % 5 == 3 { 0 } else { rnd(&mut s2) }).collect();
        let nb = z.len() / 256;
        let f: Vec<F> = (0..1usize << mu).map(|y| F::new(z[2 * y], z[2 * y + 1])).collect();
        // block folds: Z at hi[7..] (times kf for claim 1), over the whole block or its first half
        let fold = |hb: &[F], kf: Option<&[F]>, nw: usize| -> Vec<F> {
            let e = crate::mle::eq_table(hb);
            let mut out = vec![F::ZERO; 64 * nw];
            for b in 0..nb {
                let w = e[b] * kf.map_or(F::ONE, |k| k[b]);
                for t in 0..64 * nw {
                    if (z[256 * b + t / 64] >> (t % 64)) & 1 == 1 {
                        out[t] += w;
                    }
                }
            }
            out
        };
        assert!(crate::lincheck::partial_fold(&z, &h0[7..], nb) == fold(&h0[7..], None, 256));
        let dc = [
            dclaim(&h0, cs[0], None, &fold(&h0[7..], None, 256), &rpp),
            dclaim(&h1, cs[1], Some(&kf[..]), &fold(&h1[7..], Some(&kf[..]), 256), &rpp),
            dclaim(&h2, cs[2], None, &fold(&h2[7..], None, 128), &rpp),
        ];
        // Sh's form: the 16-word prefix fold (`k₀ = 3`) keeps the same `Wst` and `A` on `l < 8`
        let d3 = dclaim(&h2, cs[2], None, &fold(&h2[7..], None, 16), &rpp);
        assert!(d3.k0 == 3 && dc[2].k0 == DLO && d3.wst == dc[2].wst);
        assert!((0..128 * 64).all(|i| if i % 64 < 8 { d3.a[i] == dc[2].a[i] } else { d3.a[i].is_zero() }));
        let cl: Vec<(&[F], F, Option<&[F]>)> = vec![(&h0[..], cs[0], None), (&h1[..], cs[1], Some(&kf[..])), (&h2[..], cs[2], None)];
        for j in 0..3 {
            let w = weight_table_kf_ref(&cl[j..j + 1], &rpp);
            for (l, lp) in [(0usize, 0usize), (5, 5), (3, 40), (63, 1), (7, 9), (2, 33)] {
                let mut want = F::ZERO;
                for h in 0..(1usize << (mu - 6)) {
                    want += w[64 * h + l] * f[64 * h + lp];
                }
                let mut got = F::ZERO;
                for b in 0..128 {
                    got += dc[j].wst[64 * b + l] * dc[j].a[64 * b + lp];
                }
                assert_eq!(got, want, "claim {j} (l, l') = ({l}, {lp})");
            }
            // the folded weight at a K point
            let sp: Vec<K> = (0..6).map(|_| K { a: rf(), b: rf() }).collect();
            let es = crate::mle::eq_table_k(&sp);
            let ws: Vec<K> = (0..128).map(|b| (0..64).fold(K::ZERO, |a, l| a + es[l].mulf(dc[j].wst[64 * b + l]))).collect();
            let cells = [(5usize, K { a: rf(), b: rf() })];
            let wk = folded_weight(&dc[j..j + 1], &[&ws[..]], &cells, 1 << (mu - 6));
            for h in 0..(1usize << (mu - 6)) {
                let mut want = (0..64).fold(K::ZERO, |a, l| a + es[l].mulf(w[64 * h + l]));
                if h == 5 {
                    want += cells[0].1;
                }
                assert_eq!(wk[h], want, "claim {j} h {h}");
            }
        }
    }

    /// The row-table weight table equals the reference (dense, sparse, and a per-block factor) at
    /// every row width; E4's slices by the block fold equal `partials`.
    #[test]
    fn weight_rows_and_fold_slices() {
        let mut s = 91u64;
        let mut rf = || F::new(rnd(&mut s), rnd(&mut s));
        let mu = 11;
        let rpp: Vec<F> = (0..7).map(|_| rf()).collect();
        let h0: Vec<F> = (0..mu).map(|_| rf()).collect();
        let h1: Vec<F> = (0..mu).map(|_| rf()).collect();
        let h2: Vec<F> = (0..mu).map(|i| if (3..7).contains(&i) { F::ZERO } else { rf() }).collect();
        let kf: Vec<F> = (0..1usize << (mu - 7)).map(|_| rf()).collect();
        let cs = [rf(), rf(), rf()];
        let cl: Vec<(&[F], F, Option<&[F]>)> = vec![(&h0[..], cs[0], None), (&h1[..], cs[1], Some(&kf[..])), (&h2[..], cs[2], None)];
        let want = weight_table_kf_ref(&cl, &rpp);
        for lo in 0..=7 {
            assert!(weight_table_rows(&cl, &rpp, lo) == want, "lo = {lo}");
        }
        // 2^4 blocks of 128 elements, 256 words each
        let z: Vec<u64> = (0..(256usize << 4)).map(|_| rnd(&mut s)).collect();
        let r: Vec<F> = (0..11).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
        let fold = crate::leaf::partials_from_fold(&crate::lincheck::partial_fold(&z, &r[7..], 16), &r[..7]);
        assert!(fold == partials(&z, &r));
    }
}
