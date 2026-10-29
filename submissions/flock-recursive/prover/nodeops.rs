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

/// A kind's target bits on the positions `< 1216` (19 words).
pub fn target_words(bk: BK) -> [u64; 19] {
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

/// **`targetSNode4S`**: `P^e(σ) = Σ_{blk, hi} eq(zLo, hi) eq(r_blk, blk) E(blk, σ + 64 hi)`.
pub fn target_s_node4(k: NK, r: &[F]) -> Vec<F> {
    let n = nb(k);
    let rb: Vec<F> = (0..n).map(|l| r.get(1 + l).copied().unwrap_or(F::ZERO)).collect();
    let (eb, eh) = (eq_table(&rb), eq_table(&z_lo(r)));
    // blocks by their kind and target (the counters differ per stream block)
    let mut w: std::collections::HashMap<BK, F> = std::collections::HashMap::new();
    for blk in 0..k.h_end() {
        let bk = bk_at(k, blk);
        if bk != BK::Free {
            *w.entry(bk).or_insert(F::ZERO) += eb[blk];
        }
    }
    let mut pe = vec![F::ZERO; 64];
    for (bk, x) in w {
        let tw = target_words(bk);
        for (hi, &word) in tw.iter().enumerate() {
            let mut m = word;
            let c = x * eh[hi];
            while m != 0 {
                let j = m.trailing_zeros() as usize;
                pe[j] += c;
                m &= m - 1;
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

/// **`rsWeightS4`**: `Σ_j κ^j Σ_{k<128} c_k(r″)·w_j^{(k)}(ρ)` with claim 2 (index 1) weighted by
/// `kf4` at `β^(2^k)` over the block coordinates (`kwSL4`), the others by `eq`.
pub fn rs_weight4(k: NK, rpp: &[F], pts: &[Vec<K>], kap: F, beta: F, rho: &[K]) -> K {
    let ck = crate::ringswitch::phi_coeffs(rpp);
    let n = rho.len() - 7;
    // the kind factor per block at β, then Frobenius powers alongside the points
    let nbk = 1usize << n;
    let mut kf: Vec<F> = (0..nbk).map(|t| kf4(k, beta, t)).collect();
    let mut out = K::ZERO;
    let mut kj = F::ONE;
    for (j, p) in pts.iter().enumerate() {
        let mut q = p.clone();
        let mut acc = K::ZERO;
        for c in &ck {
            let e = if j == 1 {
                let mut hi = K::ONE;
                for l in 0..7 {
                    hi = hi * eq_k(q[l], rho[l]);
                }
                // Σ_t kf(t) eq(q′, t) eq(ρ′, t)
                let mut tab = vec![K::ONE; nbk];
                let mut len = 1usize;
                for l in (0..n).rev() {
                    let (a, b) = (q[7 + l], rho[7 + l]);
                    let (e1, e0) = (a * b, (K::ONE + a) * (K::ONE + b));
                    for i in (0..len).rev() {
                        let v = tab[i];
                        tab[2 * i] = v * e0;
                        tab[2 * i + 1] = v * e1;
                    }
                    len *= 2;
                }
                let mut s = K::ZERO;
                for t in 0..nbk {
                    s += tab[t].mulf(kf[t]);
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
        if j == 1 {
            kf = (0..nbk).map(|t| kf4(k, beta, t)).collect();
        }
        out += acc.mulf(kj);
        kj *= kap;
    }
    out
}

/// Split eq tables for points over many cells: `eq(x, c) = lo[c mod 2^12]·hi[c >> 12]`.
struct EqSplit {
    lo: Vec<F>,
    hi: Vec<F>,
}
impl EqSplit {
    fn new(x: &[F]) -> EqSplit {
        let s = x.len().min(12);
        EqSplit { lo: eq_table(&x[..s]), hi: eq_table(&x[s..]) }
    }
    fn at(&self, c: usize) -> F {
        let s = self.lo.len().trailing_zeros();
        let (l, h) = (c & (self.lo.len() - 1), c >> s);
        if h >= self.hi.len() { F::ZERO } else { self.lo[l] * self.hi[h] }
    }
}

/// **`evalM τ σ`**: `(Ã, B̃, C̃)(τ, σ)` over the node's M rows (`nodeIRows4`: every slot's prototype
/// rows moved, then its link rows); rows on `τ`'s coordinates, absolute cells on `σ`'s.
pub fn eval_m(kt: &KindTab, protos: &[Proto; 2], tau: &[F], sigma: &[F]) -> [F; 3] {
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
                        s += p.rows.coefs[t] * es.at(kt.one_cell + p.rows.cells[t] as usize - base + v * SLOT);
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
                s += l.coefs[t] * es.at(l.cells[t] as usize);
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

    /// The layout's figures against S-E12a's (`hEnd_eq`) and the dump's `node-N*.txt` headers.
    #[test]
    fn layout_figures() {
        assert_eq!([NK::N2, NK::N4, NK::N8].map(|k| k.h_end()), [70957, 117593, 187548]);
        assert_eq!(NK::N4.h_used(), 117589);
        assert_eq!(NK::N4.l_base(), 117760);
        assert_eq!(NK::N4.one_cell(), 25165824);
        assert_eq!(NK::N4.cells4(), vec![25165824, 5, 6, 7, 132, 2965509, 2965510, 15051778, 15051779]);
        // (−) the previous node's last block does not link to the aggregate's first
        assert!(!NK::N4.chain_lk(crate::node::C_LEN - 1) && NK::N4.chain_lk(crate::node::C_LEN));
    }
}
