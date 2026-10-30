//! The revision 4.1 node's verifier ops, natively, in their specification form (S-CN4's
//! `targetSNode4S`, `shiftMask4S`, `linkWAll4S`; S-T2's `rsWeightS4`; the matrices' MLEs `evalM`,
//! `evalL` over the dumped rows). Sums over the node's blocks, not the closed forms the Lean
//! computes; KAT against the Lean's computed ops (`logs/P2/r41p8/nodeops-kat.txt`, probe
//! `NodeOpsKat.lean`). The prover reads its tables from the same definitions.

use crate::field::{F, K};
use crate::mfill::{KindTab, Proto, SLOT};
use crate::mle::eq_table;
use crate::node::{bk_at, BK, FAMS, NK};

/// `ptA n a`: the first `n` entries, zero padded.
pub fn pt(n: usize, a: &[F]) -> Vec<F> {
    (0..n).map(|i| a.get(i).copied().unwrap_or(F::ZERO)).collect()
}

/// `nbN ν`: the block coordinates.
pub fn nb(k: NK) -> usize {
    k.m() - 14
}

/// **`shiftMask4S`**: `(Σ_{y linked} eq(τ,y) eq(r,y), Σ_{y linked} eq(τ,y) eq(r,y+1), eq(r,0) +
/// eq(r, chLen₀))` on `nb` coordinates.
pub fn shift_mask4(k: NK, tau: &[F], r: &[F]) -> [F; 3] {
    let n = nb(k);
    let (et, er) = (eq_table(&pt(n, tau)), eq_table(&pt(n, r)));
    let (mut a, mut b) = (F::ZERO, F::ZERO);
    for y in 0..1usize << n {
        if k.chain_lk(y) {
            a += et[y] * er[y];
            b += et[y] * er[y + 1];
        }
    }
    [a, b, er[0] + er[k.ch_len(0)]]
}

/// The masked successor table of the node's Sh (`chainLk4`): `e2[y + 1] = eq(τ, y)` for linked
/// `y`, the start term `κ_s` at both chains' first blocks, zero elsewhere (the prover's `In` table).
pub fn shift_in_table(k: NK, tau: &[F], kap_s: F) -> Vec<F> {
    let et = eq_table(&pt(nb(k), tau));
    let mut e2 = vec![F::ZERO; et.len()];
    for y in 0..et.len() - 1 {
        if k.chain_lk(y) {
            e2[y + 1] = et[y];
        }
    }
    e2[0] += kap_s;
    e2[k.ch_len(0)] += kap_s;
    e2
}

/// The pinned coordinates `ρ` (A.2) then `r[0]`: the 8 position coordinates of `targetS`.
fn z_lo(r: &[F]) -> Vec<F> {
    let mut v = crate::skipdom::skip().rho.to_vec();
    v.push(r.first().copied().unwrap_or(F::ZERO));
    v
}

/// A kind's target bits on the positions `< 1216` (19 words), by `BK::target`'s regions: `h₀`
/// (`0 … 255`), the pinned message bytes (`512 … 1023`), the counter `t` (`1024 … 1087`), `fin`
/// (`1088 … 1119`), zeros, and the constant (`1152`). Equal to `target_words_ref` (test).
pub fn target_words(bk: BK) -> [u64; 19] {
    let mut w = [0u64; 19];
    if bk == BK::Free {
        return w;
    }
    if bk.h0_pin() {
        let h0 = crate::blake2s::h0();
        for i in 0..4 {
            w[i] = h0[2 * i] as u64 | (h0[2 * i + 1] as u64) << 32;
        }
    }
    for p in 0..64 {
        if let Some(b) = bk.msg_pin(p) {
            w[8 + p / 8] |= (b as u64) << (8 * (p % 8));
        }
    }
    let (t, fin) = bk.ctr();
    w[16] = t;
    if fin {
        w[17] = 0xFFFF_FFFF;
    }
    w[18] = 1;
    w
}

/// `target_words` position by position (the reference).
pub fn target_words_ref(bk: BK) -> [u64; 19] {
    let mut w = [0u64; 19];
    if bk != BK::Free {
        for p in 0..19 * 64 {
            if bk.target(p) == Some(true) {
                w[p / 64] |= 1 << (p % 64);
            }
        }
    }
    w
}

/// **`targetSNode4S`**: `P^e(σ) = Σ_{blk, hi} eq(zLo, hi) eq(r_blk, blk) E(blk, σ + 64 hi)`. Per word
/// `hi` and byte `p` of the targets, `T[hi][p][β] = Σ_{blk: byte p of word hi is β} eq(r_blk, blk)`
/// (one pass over the blocks, in parallel), then `P^e(8p + i) = Σ_{hi, β ∋ i} eq(zLo, hi) T[hi][p][β]`.
pub fn target_s_node4(k: NK, r: &[F]) -> Vec<F> {
    let n = nb(k);
    let rb: Vec<F> = (0..n).map(|l| r.get(1 + l).copied().unwrap_or(F::ZERO)).collect();
    let (eb, eh) = (eq_table(&rb), eq_table(&z_lo(r)));
    let parts = crate::par::map_chunks(k.h_end(), 1 << 12, |lo, hi| {
        let mut t = vec![F::ZERO; 19 * 8 * 256];
        for blk in lo..hi {
            let tw = target_words(bk_at(k, blk));
            let x = eb[blk];
            for (h, &word) in tw.iter().enumerate() {
                let mut wd = word;
                let mut p = 0;
                while wd != 0 {
                    let b = (wd & 0xFF) as usize;
                    if b != 0 {
                        t[(h * 8 + p) * 256 + b] += x;
                    }
                    wd >>= 8;
                    p += 1;
                }
            }
        }
        t
    });
    let mut t = vec![F::ZERO; 19 * 8 * 256];
    for q in parts {
        for (a, b) in t.iter_mut().zip(q.iter()) {
            *a += *b;
        }
    }
    let mut pe = vec![F::ZERO; 64];
    for h in 0..19 {
        for p in 0..8 {
            for b in 1..256usize {
                let x = t[(h * 8 + p) * 256 + b];
                if x.is_zero() {
                    continue;
                }
                let c = x * eh[h];
                for i in 0..8 {
                    if (b >> i) & 1 == 1 {
                        pe[(8 * p + i) % 64] += c;
                    }
                }
            }
        }
    }
    pe
}

/// `slotWL pos L θ r_pos`: `Σ_{s<L} eq(θ, s) eq(r_pos, pos(s))` (10 coordinates each).
fn slot_wl(pos: &dyn Fn(usize) -> usize, l: usize, eth: &[F], erp: &[F]) -> F {
    (0..l).fold(F::ZERO, |a, s| a + eth[s] * erp[pos(s)])
}

/// **`linkWAll4S`**: the eight families' weights at `tt = τ ‖ θ`, `rr = r_blk ‖ r_pos`.
pub fn link_w_all4(k: NK, tt: &[F], rr: &[F]) -> Vec<F> {
    let n = nb(k);
    let get = |a: &[F], i: usize| a.get(i).copied().unwrap_or(F::ZERO);
    let (et, eb) = (eq_table(&pt(n, tt)), eq_table(&pt(n, rr)));
    let eth = eq_table(&(0..10).map(|l| get(tt, n + l)).collect::<Vec<_>>());
    let erp = eq_table(&(0..10).map(|l| get(rr, n + l)).collect::<Vec<_>>());
    FAMS.iter()
        .map(|f| {
            let bits = 8 * f.len;
            let sw_src = slot_wl(&|s| 512 + 8 * f.off + s, bits, &eth, &erp);
            let mut acc = F::ZERO;
            for sg in 0..2 {
                for t in 0..f.n {
                    let src = k.wots_b(sg) + (f.src)(t);
                    let g = (f.mir)(t);
                    let mir = k.wm_b(sg) + g / 4;
                    let sw_mir = slot_wl(&|s| 256 * (g % 4) + f.mbo + s, bits, &eth, &erp);
                    acc += et[src] * (eb[src] * sw_src + eb[mir] * sw_mir);
                }
            }
            acc
        })
        .collect()
}

/// **`kf4`**: the kind factor `β^(index − 1)` of block `t` (`free`: `β^7`).
pub fn kf4(k: NK, beta: F, t: usize) -> F {
    let i = bk_at(k, t).idx() - 1;
    (0..i).fold(F::ONE, |a, _| a * beta)
}

fn eq_k(a: K, b: K) -> K {
    K::ONE + a + b
}

/// The node's blocks as maximal runs of one kind: `(start, end, BK::idx)`, covering `[0, 2^nb)`.
pub fn kind_runs(k: NK) -> Vec<(usize, usize, usize)> {
    let mut v: Vec<(usize, usize, usize)> = Vec::new();
    for t in 0..k.blocks() {
        let i = bk_at(k, t).idx();
        match v.last_mut() {
            Some(r) if r.2 == i && r.1 == t => r.1 = t + 1,
            _ => v.push((t, t + 1, i)),
        }
    }
    v
}

/// `Σ_{t < b} Π_l f_l(t_l)` for a product function on `n` bits (`f0`, `f1` the factor's values at
/// 0 and 1, `low[l] = Π_{l' < l} (f0 + f1)`).
fn prefix_k(f0: &[K], f1: &[K], low: &[K], b: usize) -> K {
    let n = f0.len();
    if b >> n != 0 {
        return low[n];
    }
    let (mut acc, mut hi) = (K::ZERO, K::ONE);
    for l in (0..n).rev() {
        if (b >> l) & 1 == 1 {
            acc += hi * f0[l] * low[l];
            hi = hi * f1[l];
        } else {
            hi = hi * f0[l];
        }
    }
    acc
}

/// **`rsWeightS4`**: `Σ_j κ^j Σ_{k<128} c_k(r″)·w_j^{(k)}(ρ)` with claim 2 (index 1) weighted by
/// `kf4` at `β^(2^k)` over the block coordinates (`kwSL4`), the others by `eq`. Claim 2's block sum
/// `Σ_t kf(t) eq(q′, t) eq(ρ′, t)` is taken per run of one kind (`kind_runs`), each run by two prefix
/// sums of the product function (`O(runs · nb)` per stage, not `O(2^nb)`).
pub fn rs_weight4(k: NK, rpp: &[F], pts: &[Vec<K>], kap: F, beta: F, rho: &[K]) -> K {
    let ck = crate::ringswitch::phi_coeffs(rpp);
    let n = rho.len() - 7;
    let runs = kind_runs(k);
    let mut out = K::ZERO;
    let mut kj = F::ONE;
    for (j, p) in pts.iter().enumerate() {
        let mut q = p.clone();
        // the kind factors β^(i−1), i = 1 … 8, raised to 2^k alongside the stages
        let mut kf: Vec<F> = (0..9).map(|i| (1..i).fold(F::ONE, |a, _| a * beta)).collect();
        let mut acc = K::ZERO;
        for c in &ck {
            let e = if j == 1 {
                let mut hi = K::ONE;
                for l in 0..7 {
                    hi = hi * eq_k(q[l], rho[l]);
                }
                let f1: Vec<K> = (0..n).map(|l| q[7 + l] * rho[7 + l]).collect();
                let f0: Vec<K> = (0..n).map(|l| (K::ONE + q[7 + l]) * (K::ONE + rho[7 + l])).collect();
                let mut low = vec![K::ONE; n + 1];
                for l in 0..n {
                    low[l + 1] = low[l] * (f0[l] + f1[l]);
                }
                let mut s = K::ZERO;
                for &(a, b, i) in &runs {
                    s += (prefix_k(&f0, &f1, &low, b) + prefix_k(&f0, &f1, &low, a)).mulf(kf[i]);
                }
                hi * s
            } else {
                let mut e = K::ONE;
                for (a, b) in q.iter().zip(rho.iter()) {
                    e = e * eq_k(*a, *b);
                }
                e
            };
            acc += e.mulf(*c);
            q.iter_mut().for_each(|x| *x = x.sq());
            if j == 1 {
                kf.iter_mut().for_each(|x| *x = x.sq());
            }
        }
        out += acc.mulf(kj);
        kj *= kap;
    }
    out
}

/// Split eq tables for points over many cells: `eq(x, c) = lo[c mod 2^12]·hi[c >> 12]`.
pub struct EqSplit {
    lo: Vec<F>,
    hi: Vec<F>,
}
impl EqSplit {
    pub fn new(x: &[F]) -> EqSplit {
        let s = x.len().min(12);
        EqSplit { lo: eq_table(&x[..s]), hi: eq_table(&x[s..]) }
    }
    pub fn at(&self, c: usize) -> F {
        let s = self.lo.len().trailing_zeros();
        let (l, h) = (c & (self.lo.len() - 1), c >> s);
        if h >= self.hi.len() { F::ZERO } else { self.lo[l] * self.hi[h] }
    }
}

/// **`evalM τ σ`**: `(Ã, B̃, C̃)(τ, σ)` over the node's M rows (`nodeIRows4`: every slot's prototype
/// rows moved, then its link rows); rows on `τ`'s coordinates, absolute cells on `σ`'s.
pub fn eval_m(kt: &KindTab, protos: &[Proto; 2], tau: &[F], sigma: &[F]) -> [F; 3] {
    const W: usize = 20; // SLOT = 2^20
    if tau.len() < W || sigma.len() < W || kt.one_cell % SLOT != 0 {
        return eval_m_ref(kt, protos, tau, sigma);
    }
    // a slot's rows are `v·2^20 + local` and its cells `one + v·2^20 + local` (`one` a multiple of
    // 2^20): `eq(τ, row) = eq(τ_{<20}, local)·eq(τ_{≥20}, v)`, the same for the cells, so a row
    // costs one table entry per term (no product for a coefficient 1) and one product per matrix
    let (lt, ls) = (eq_table(&tau[..W]), eq_table(&sigma[..W]));
    let (ht, hs) = (eq_table(&tau[W..]), eq_table(&sigma[W..]));
    let ob = kt.one_cell >> W;
    let mut out = [F::ZERO; 3];
    for (v, &(pi, ..)) in kt.slots.iter().enumerate() {
        let p = &protos[pi];
        let base = pi * SLOT;
        let parts = crate::par::map_chunks(p.rows.len(), 4096, |lo, hi| {
            let mut o = [crate::field::FAcc::default(), crate::field::FAcc::default(), crate::field::FAcc::default()];
            for i in lo..hi {
                let rw = lt[p.rows.idx[i] as usize - base];
                let rg = p.rows.rng[i];
                for m in 0..3 {
                    let mut s = F::ZERO;
                    for t in rg[m] as usize..rg[m + 1] as usize {
                        s += p.rows.cmul(t, ls[p.rows.cells[t] as usize - base]);
                    }
                    o[m].mac(rw, s);
                }
            }
            o.map(|x| x.reduce())
        });
        let fac = ht[v] * hs[ob + v];
        for o in parts {
            for m in 0..3 {
                out[m] += fac * o[m];
            }
        }
    }
    let (et, es) = (EqSplit::new(tau), EqSplit::new(sigma));
    let o = links_val(kt, &et, &es);
    for m in 0..3 {
        out[m] += o[m];
    }
    out
}

/// The kind table's link rows' `(Ã, B̃, C̃)` at `(et, es)` (E1b: in parallel).
fn links_val(kt: &KindTab, et: &EqSplit, es: &EqSplit) -> [F; 3] {
    let l = &kt.links;
    let lv = kt.links_eval(&|c| es.at(c));
    let parts = crate::par::map_chunks(l.len(), 1 << 14, |lo, hi| {
        let mut o = [crate::field::FAcc::default(), crate::field::FAcc::default(), crate::field::FAcc::default()];
        for i in lo..hi {
            let rw = et.at(l.idx[i] as usize);
            for m in 0..3 {
                o[m].mac(rw, lv[i][m]);
            }
        }
        o.map(|x| x.reduce())
    });
    let mut out = [F::ZERO; 3];
    for o in parts {
        for m in 0..3 {
            out[m] += o[m];
        }
    }
    out
}

/// **`evalMX4`** (RSV2's stacked call): the row point `τ = p_x[0..23) ‖ s[0..9)`, the column point
/// `σ` (25 entries); `Σ_{k<3} ⟨s_k, (Ã, B̃, C̃)_{κ_k}(p_x, σ)⟩` over `κ = N2, N4, N8` (`κ.ix`), each kind
/// read at its own coordinates (`ptOf`: the first `logM κ` row and `logM κ + 2` column entries); a
/// kind with zero coefficients is skipped. Every slot of every kind is its prototype's rows moved by
/// `v·2^20` (rows and cells), and the low 20 coordinates of both points are the same for every kind,
/// so each prototype's sum at `(eq(τ_{<20}), eq(σ_{<20}))` is computed once (`eval_m`'s per-slot sum)
/// and every slot takes it times `eq(τ_{≥20}, v)·eq(σ_{≥20}, one/2^20 + v)`; then each kind's link
/// rows. `eval_mx_ref`: `eval_m` per kind.
pub fn eval_mx(kts: &[&KindTab; 3], protos: &[Proto; 2], tau: &[F], sigma: &[F]) -> F {
    const W: usize = 20;
    assert_eq!(tau.len(), 32);
    let (lt, ls) = (eq_table(&tau[..W]), eq_table(&sigma[..W]));
    let po: [std::sync::OnceLock<[F; 3]>; 2] = [std::sync::OnceLock::new(), std::sync::OnceLock::new()];
    let proto_sum = |pi: usize| -> [F; 3] {
        let p = &protos[pi];
        let base = pi * SLOT;
        let parts = crate::par::map_chunks(p.rows.len(), 4096, |lo, hi| {
            let mut o = [crate::field::FAcc::default(), crate::field::FAcc::default(), crate::field::FAcc::default()];
            for i in lo..hi {
                let rw = lt[p.rows.idx[i] as usize - base];
                let rg = p.rows.rng[i];
                for m in 0..3 {
                    let mut s = F::ZERO;
                    for t in rg[m] as usize..rg[m + 1] as usize {
                        s += p.rows.cmul(t, ls[p.rows.cells[t] as usize - base]);
                    }
                    o[m].mac(rw, s);
                }
            }
            o.map(|x| x.reduce())
        });
        let mut out = [F::ZERO; 3];
        for o in parts {
            for m in 0..3 {
                out[m] += o[m];
            }
        }
        out
    };
    let mut x = F::ZERO;
    for (k, kt) in kts.iter().enumerate() {
        let s = &tau[23 + 3 * k..26 + 3 * k];
        if s.iter().all(|v| v.is_zero()) {
            continue;
        }
        let lm = kt.log_m;
        if kt.one_cell % SLOT != 0 {
            let r = eval_m_ref(kt, protos, &tau[..lm], &sigma[..lm + 2]);
            x += s[0] * r[0] + s[1] * r[1] + s[2] * r[2];
            continue;
        }
        let (ht, hs) = (eq_table(&tau[W..lm]), eq_table(&sigma[W..lm + 2]));
        let ob = kt.one_cell >> W;
        let mut out = [F::ZERO; 3];
        for (v, &(pi, ..)) in kt.slots.iter().enumerate() {
            let o = po[pi].get_or_init(|| proto_sum(pi));
            let fac = ht[v] * hs[ob + v];
            for m in 0..3 {
                out[m] += fac * o[m];
            }
        }
        let (et, es) = (EqSplit::new(&tau[..lm]), EqSplit::new(&sigma[..lm + 2]));
        let o = links_val(kt, &et, &es);
        for m in 0..3 {
            out[m] += o[m];
        }
        x += s[0] * out[0] + s[1] * out[1] + s[2] * out[2];
    }
    x
}

/// `eval_mx` with `eval_m` per kind (the reference).
pub fn eval_mx_ref(kts: &[&KindTab; 3], protos: &[Proto; 2], tau: &[F], sigma: &[F]) -> F {
    let mut x = F::ZERO;
    for (k, kt) in kts.iter().enumerate() {
        let s = &tau[23 + 3 * k..26 + 3 * k];
        let lm = kt.log_m;
        let r = eval_m(kt, protos, &tau[..lm], &sigma[..lm + 2]);
        x += s[0] * r[0] + s[1] * r[1] + s[2] * r[2];
    }
    x
}

/// `eval_m` term by term with the split eq tables (the reference).
pub fn eval_m_ref(kt: &KindTab, protos: &[Proto; 2], tau: &[F], sigma: &[F]) -> [F; 3] {
    let (et, es) = (EqSplit::new(tau), EqSplit::new(sigma));
    let mut out = [F::ZERO; 3];
    for (v, &(pi, ..)) in kt.slots.iter().enumerate() {
        let p = &protos[pi];
        let base = pi * SLOT;
        let parts = crate::par::map_chunks(p.rows.len(), 4096, |lo, hi| {
            let mut o = [F::ZERO; 3];
            for i in lo..hi {
                let rw = et.at(p.rows.idx[i] as usize - base + v * SLOT);
                let rg = p.rows.rng[i];
                for m in 0..3 {
                    let mut s = F::ZERO;
                    for t in rg[m] as usize..rg[m + 1] as usize {
                        s += p.rows.coef(t) * es.at(kt.one_cell + p.rows.cells[t] as usize - base + v * SLOT);
                    }
                    o[m] += rw * s;
                }
            }
            o
        });
        for o in parts {
            for m in 0..3 {
                out[m] += o[m];
            }
        }
    }
    let l = &kt.links;
    for i in 0..l.len() {
        let rw = et.at(l.idx[i] as usize);
        let rg = l.rng[i];
        for m in 0..3 {
            let mut s = F::ZERO;
            for t in rg[m] as usize..rg[m + 1] as usize {
                s += l.coef(t) * es.at(l.cells[t] as usize);
            }
            out[m] += rw * s;
        }
    }
    out
}

/// **`evalL τ σ`** over `lRows4` (row `j` = the `j`-th declared bit, slot-major: `b · (one − b) =
/// 0`): `(Σ_j eq(τ,j) eq(σ,b_j), Σ_j eq(τ,j)(eq(σ,one) − eq(σ,b_j)), 0)`.
pub fn eval_l(k: NK, tau: &[F], sigma: &[F]) -> [F; 3] {
    let (et, es) = (EqSplit::new(tau), EqSplit::new(sigma));
    let one = es.at(k.one_cell());
    let (mut a, mut b) = (F::ZERO, F::ZERO);
    let mut j = 0;
    for v in 0..k.vslots() {
        for i in 0..8220 {
            let c = k.l_base() * 128 + v * (1 << 14) + 299 + i;
            let (rw, cw) = (et.at(j), es.at(c));
            a += rw * cw;
            b += rw * (one + cw);
            j += 1;
        }
    }
    [a, b, F::ZERO]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `target_words` equals the position-by-position reference on every block of every kind;
    /// the factorized `eval_m` equals `eval_m_ref` on the node data at a random point.
    #[test]
    fn fast_target_and_eval_m() {
        for k in [NK::N2, NK::N4, NK::N8] {
            for blk in 0..k.blocks() {
                let bk = bk_at(k, blk);
                assert_eq!(target_words(bk), target_words_ref(bk), "{k:?} block {blk}");
            }
        }
        if crate::plan::BLOB.len() < 16 && crate::mfill::find_dirs().is_none() {
            return;
        }
        let nd = crate::plan::node_data();
        let mut s = 7u64;
        let mut rf = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            F::new(s, s.rotate_left(17) ^ 0x55)
        };
        for k in [NK::N2, NK::N4] {
            let kt = nd.kind_tab(k);
            let tau: Vec<F> = (0..k.log_m()).map(|_| rf()).collect();
            let sigma: Vec<F> = (0..k.m() - 7).map(|_| rf()).collect();
            assert_eq!(eval_m(&kt, &nd.protos, &tau, &sigma), eval_m_ref(&kt, &nd.protos, &tau, &sigma), "{k:?}");
        }
    }

    fn kat_f(s: usize, i: usize) -> F {
        let b: Vec<u8> = (0..16).map(|j| ((37 * s + 11 * j + 5 * i + 1) % 256) as u8).collect();
        F::from_bytes(&b)
    }
    fn kat_af(s: usize, n: usize) -> Vec<F> {
        (0..n).map(|i| kat_f(s, i)).collect()
    }
    fn kat_ak(s: usize, n: usize) -> Vec<K> {
        (0..n).map(|i| K { a: kat_f(s, 2 * i), b: kat_f(s + 100, 2 * i + 1) }).collect()
    }
    fn hx(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    /// The native ops against the Lean's computed ops (S-CN4b `targetSNode4I`, `shiftMask4I`,
    /// `linkWAll4I`; S-T2 `rsWeightF4`) at the probe's points.
    #[test]
    fn node_ops_match_lean() {
        let Some(p) = crate::kat::find_up("logs/P2/r41p8/nodeops-kat.txt") else { return };
        let text = std::fs::read_to_string(p).unwrap();
        let mut n = 0;
        for line in text.lines() {
            let t: Vec<&str> = line.split(' ').collect();
            let k = match t[1] {
                "N2" => NK::N2,
                "N4" => NK::N4,
                _ => NK::N8,
            };
            let s: usize = t[2].parse().unwrap();
            let nbk = nb(k);
            let got: Vec<String> = match t[0] {
                "targetS" => target_s_node4(k, &kat_af(s, nbk + 1)).iter().map(|x| hx(&x.to_bytes())).collect(),
                "shiftMask" => shift_mask4(k, &kat_af(s, 18), &kat_af(s + 10, 18)).iter().map(|x| hx(&x.to_bytes())).collect(),
                "linkWAll" => link_w_all4(k, &kat_af(s, nbk + 10), &kat_af(s + 20, nbk + 10)).iter().map(|x| hx(&x.to_bytes())).collect(),
                "rsWeight" => {
                    let m = k.m() - 7;
                    let ps: Vec<Vec<K>> = (0..4).map(|j| kat_ak(s + 30 + j, m)).collect();
                    vec![hx(&rs_weight4(k, &kat_af(s + 40, 7), &ps, kat_f(s, 77), kat_f(s, 78), &kat_ak(s + 50, m)).to_bytes())]
                }
                _ => continue,
            };
            assert_eq!(got.join(" "), t[3..].join(" "), "{} {} {s}", t[0], t[1]);
            n += 1;
        }
        assert!(n >= 24, "{n} lines");
    }

    /// `eval_mx` (prototype sums shared by every slot and kind) equals `eval_m` per kind, on random
    /// 32/25-entry points with every support (E1).
    #[test]
    fn eval_mx_matches_ref() {
        let nd = crate::plan::node_data();
        let kts = nd.kind_tabs();
        let kr = [&*kts[0], &*kts[1], &*kts[2]];
        let mut s = 0x1234_5678_9abc_def0u64;
        let mut rf = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            F::new(s, s.rotate_left(29) ^ 0xa5)
        };
        for sup in [1usize, 2, 4, 7] {
            let mut tau: Vec<F> = (0..32).map(|_| rf()).collect();
            for k in 0..3 {
                if sup >> k & 1 == 0 {
                    tau[23 + 3 * k..26 + 3 * k].iter_mut().for_each(|x| *x = F::ZERO);
                }
            }
            let sigma: Vec<F> = (0..25).map(|_| rf()).collect();
            assert_eq!(eval_mx(&kr, &nd.protos, &tau, &sigma), eval_mx_ref(&kr, &nd.protos, &tau, &sigma), "support {sup}");
        }
    }

    /// The layout's figures against S-E12a's (`hEnd_eq`) and the dump's `node-N*.txt` headers.
    #[test]
    fn layout_figures() {
        // revision 4.4.1 at rev44 (`FRNodeKinds4.hEnd_eq`, A1′'s `hUsed_eq`: spacers, L1)
        assert_eq!([NK::N2, NK::N4, NK::N8].map(|k| k.h_end()), [74017, 122501, 195228]);
        assert_eq!([NK::N2, NK::N4, NK::N8].map(|k| k.h_used()), [74015, 122497, 195220]);
        assert_eq!(NK::N8.l_base(), 195328);
        assert_eq!(NK::N4.l_base(), 122624);
        assert_eq!(NK::N4.one_cell(), 25165824);
        assert_eq!(NK::N4.cells4(), vec![25165824, 5, 6, 7, 132, 3102213, 3102214, 15680002, 15680003]);
        assert_eq!([1, 2, 3, 4].map(crate::node::agg_l), [24236, 48474, 72712, 96950]);
        // (−) the previous node's last block does not link to the aggregate's first
        assert!(!NK::N4.chain_lk(crate::node::C_LEN - 1) && NK::N4.chain_lk(crate::node::C_LEN));
    }
}
