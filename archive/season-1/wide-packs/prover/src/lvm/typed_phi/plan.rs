//! PFAST-PQ: the K1 and point kernels of [`PhiK`] regrouped by their repeated work.
//!
//! A group (K1's `k1_key`, the points' `(o, x ≫ 10, y ≫ 11)`) sums `H·Σ_runs lo(u)·Σ_{run} c·lo(v)`: `H` the high
//! halves (and K1's pattern), `u` a run's outer coordinate, `v` its entries' inner one. The program repeats itself:
//! most runs' inner lists `[(v low, c)]` occur many times, so
//! - every distinct inner list's sum `S = Σ c·lo(v)` is computed once per batch of points ([`Plan::lists`]);
//! - a group's runs with the same list share one product: `(Σ lo(u))·S` (a group's *terms*);
//! - groups with the same terms (their low parts equal, only `H` differs) share their sum ([`Plan::sigs`]), each
//!   instance then multiplies by its own `H`.
//!
//! The same field sums regrouped by distributivity (exact), so the matrix values are the kernels' values.
use std::collections::HashMap;
use std::ops::Range;

use super::{CHUNKS, Chunk, NONE, OM, OS, PhiF, PhiK, Tabs, k1_key, pass_cost};
use crate::lv::primitives::field::Unreduced;

/// A multiply-rotate hasher for the plan's keys (lists of small integers; no adversary): the default SipHash dominated
/// the plan's build.
#[derive(Default, Clone, Copy)]
struct Fx(u64);

impl std::hash::Hasher for Fx {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for c in bytes.chunks(8) {
            let mut b = [0u8; 8];
            b[..c.len()].copy_from_slice(c);
            self.write_u64(u64::from_le_bytes(b));
        }
    }
    #[inline]
    fn write_u32(&mut self, v: u32) {
        self.write_u64(v as u64);
    }
    #[inline]
    fn write_u64(&mut self, v: u64) {
        self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
    #[inline]
    fn write_usize(&mut self, v: usize) {
        self.write_u64(v as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

type FxMap<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<Fx>>;

/// Outer factor tables: `x.lo[t]` for `t ≤ xs`, `y.lo[0]`, the unit.
pub(super) const TAB_Y: u32 = 0x40;
pub(super) const TAB_ONE: u32 = 0x41;

/// A group instance: matrix `o`, high halves `x.hi[hj][hx]`, `y.hi[0][hy]`, K1's pattern (or `NONE`).
#[derive(Clone, Copy)]
pub(super) struct Inst {
    pub o: u32,
    pub hj: u32,
    pub hx: u32,
    pub hy: u32,
    pub pat: u32,
}

pub(super) struct Plan {
    /// inner lists' entries `(row, coefficient index)`; list `l` is `lent[lptr[l]..lptr[l + 1]]`, its rows in
    /// `x.lo[0]` if `lside[l]`, else in `y.lo[0]`
    pub lent: Vec<(u32, u32)>,
    pub lptr: Vec<u32>,
    pub lside: Vec<bool>,
    /// terms: list `tlist[t]`, outer factors `refs[rptr[t]..rptr[t + 1]]` (`table << 16 | row`)
    pub tlist: Vec<u32>,
    pub rptr: Vec<u32>,
    pub refs: Vec<u32>,
    /// signatures: terms `tptr[s]..tptr[s + 1]`, instances `inst[iptr[s]..iptr[s + 1]]`
    pub tptr: Vec<u32>,
    pub inst: Vec<Inst>,
    pub iptr: Vec<u32>,
    /// work split (static cost): list ranges, signature ranges
    pub lch: Vec<Range<usize>>,
    pub sch: Vec<Range<usize>>,
    /// the automaton's passes in about [`CHUNKS`] items of their own
    pub auto: Vec<Chunk>,
    pub report: String,
}

/// One group as built: its instance and its runs `(outer factor, inner list)`.
type Group = (Inst, Vec<(u32, bool, Vec<(u32, u32)>)>);

impl Plan {
    pub(super) fn new<F: PhiF>(pk: &PhiK<F>) -> Plan {
        let (xs, ys) = (10.min(pk.x_log), 11.min(pk.y_log));
        let (xm, ym) = ((1u32 << xs) - 1, (1u32 << ys) - 1);
        let mut groups: Vec<Group> = Vec::new();
        // K1: outer x at level ℓ (`x.lo[ℓ]`, the unit when ℓ > xs), inner y0 in `y.lo[0]`
        let k1 = &pk.k1e;
        let mut i = 0;
        while i < k1.len() {
            let key = k1_key(&k1[i], xs, ys);
            let ell = key.2 as usize;
            let mut runs = Vec::new();
            let mut j = i;
            while j < k1.len() && k1_key(&k1[j], xs, ys) == key {
                let x = k1[j].x;
                let mut run = Vec::new();
                while j < k1.len() && k1[j].x == x && k1_key(&k1[j], xs, ys) == key {
                    run.push((k1[j].y0 & ym, k1[j].c));
                    j += 1;
                }
                let r = if ell <= xs { (ell as u32) << 16 | (x & ((1 << (xs - ell)) - 1)) } else { TAB_ONE << 16 };
                runs.push((r, false, run));
            }
            let hj = if ell <= xs { 0 } else { ell - xs } as u32;
            groups.push((Inst { o: key.0 as u32, hj, hx: key.3, hy: key.4, pat: key.1 }, runs));
            i = j;
        }
        // points: x-major (outer x in `x.lo[0]`, inner y) and y-major (outer y, inner x in `x.lo[0]`)
        for (v, ymaj) in [(&pk.pt, false), (&pk.pty, true)] {
            let grp = |e: &(u32, u32, u32)| (e.2 & OM, e.0 >> xs, e.1 >> ys);
            let outer = |e: &(u32, u32, u32)| if ymaj { e.1 } else { e.0 };
            let mut i = 0;
            while i < v.len() {
                let g = grp(&v[i]);
                let mut runs = Vec::new();
                let mut j = i;
                while j < v.len() && grp(&v[j]) == g {
                    let u = outer(&v[j]);
                    let mut run = Vec::new();
                    while j < v.len() && grp(&v[j]) == g && outer(&v[j]) == u {
                        let inner = if ymaj { v[j].0 & xm } else { v[j].1 & ym };
                        run.push((inner, v[j].2 >> OS));
                        j += 1;
                    }
                    let r = if ymaj { TAB_Y << 16 | (u & ym) } else { u & xm };
                    runs.push((r, ymaj, run));
                }
                groups.push((Inst { o: g.0, hj: 0, hx: g.1, hy: g.2, pat: NONE }, runs));
                i = j;
            }
        }
        // distinct lists (ids in first use), terms per group, distinct signatures
        let mut lid: FxMap<(bool, Vec<(u32, u32)>), u32> = FxMap::default();
        let (mut lent, mut lptr, mut lside) = (Vec::new(), vec![0u32], Vec::new());
        let mut sid: FxMap<Vec<(u32, Vec<u32>)>, u32> = FxMap::default();
        let mut sigs: Vec<Vec<(u32, Vec<u32>)>> = Vec::new();
        let mut insts: Vec<(u32, Inst)> = Vec::new();
        let (mut n_runs, mut n_ent) = (0usize, 0usize);
        for (inst, runs) in groups {
            n_runs += runs.len();
            let mut lr: Vec<(u32, u32)> = Vec::with_capacity(runs.len());
            for (r, side, run) in runs {
                n_ent += run.len();
                let l = *lid.entry((side, run)).or_insert_with_key(|(side, run)| {
                    lent.extend_from_slice(run);
                    lptr.push(lent.len() as u32);
                    lside.push(*side);
                    lside.len() as u32 - 1
                });
                lr.push((l, r));
            }
            // terms: the runs by list, their outer factors sorted
            lr.sort_unstable();
            let mut terms: Vec<(u32, Vec<u32>)> = Vec::new();
            for (l, r) in lr {
                match terms.last_mut() {
                    Some(t) if t.0 == l => t.1.push(r),
                    _ => terms.push((l, vec![r])),
                }
            }
            let s = *sid.entry(terms).or_insert_with_key(|terms| {
                sigs.push(terms.clone());
                sigs.len() as u32 - 1
            });
            insts.push((s, inst));
        }
        insts.sort_by_key(|e| e.0);
        let (mut tlist, mut rptr, mut refs, mut tptr) = (Vec::new(), vec![0u32], Vec::new(), vec![0u32]);
        for terms in &sigs {
            for (l, rs) in terms {
                tlist.push(*l);
                refs.extend_from_slice(rs);
                rptr.push(refs.len() as u32);
            }
            tptr.push(tlist.len() as u32);
        }
        let mut iptr = vec![0u32; sigs.len() + 1];
        for &(s, _) in &insts {
            iptr[s as usize + 1] += 1;
        }
        for s in 0..sigs.len() {
            iptr[s + 1] += iptr[s];
        }
        let inst: Vec<Inst> = insts.into_iter().map(|e| e.1).collect();
        // the work split: lists by entries (+ a reduction), signatures by outer factors, products and instances
        let lcost = |l: usize| (lptr[l + 1] - lptr[l]) as usize + 4;
        let scost = |s: usize| {
            let (t0, t1) = (tptr[s] as usize, tptr[s + 1] as usize);
            (rptr[t1] - rptr[t0]) as usize + 4 * (t1 - t0) + 4 + 3 * (iptr[s + 1] - iptr[s]) as usize
        };
        let cut = |n: usize, cost: &dyn Fn(usize) -> usize| -> Vec<Range<usize>> {
            let total: usize = (0..n).map(cost).sum();
            let target = (total / CHUNKS).max(1);
            let (mut out, mut lo, mut acc) = (Vec::new(), 0usize, 0usize);
            for k in 0..n {
                acc += cost(k);
                if acc >= target {
                    out.push(lo..k + 1);
                    (lo, acc) = (k + 1, 0);
                }
            }
            if lo < n {
                out.push(lo..n);
            }
            out
        };
        let lch = cut(lside.len(), &lcost);
        let auto = cut(pk.passes.len(), &|i| pass_cost(&pk.shapes[pk.passes[i].shape as usize], &pk.passes[i], &pk.mem)).into_iter().map(Chunk::Auto).collect();
        let sch = cut(sigs.len(), &scost);
        let lcost_all: usize = (0..lside.len()).map(lcost).sum();
        let scost_all: usize = (0..sigs.len()).map(scost).sum();
        let report = format!(
            "; plan: {} groups, {n_runs} runs ({n_ent} entries) -> {} lists ({} entries), {} signatures ({} terms, {} outer factors); \
             products per point: lists {lcost_all} signatures {scost_all}",
            inst.len(),
            lside.len(),
            lent.len(),
            sigs.len(),
            tlist.len(),
            refs.len()
        );
        Plan { lent, lptr, lside, tlist, rptr, refs, tptr, inst, iptr, lch, sch, auto, report }
    }
}

impl<F: PhiF> PhiK<F> {
    /// The outer factor `r` (`table << 16 | row`) at the batch's points.
    #[inline(always)]
    pub(super) fn outer<'a>(tb: &'a Tabs<F>, r: u32, np: usize, one: &'a [F]) -> &'a [F] {
        let (t, row) = (r >> 16, (r & 0xFFFF) as usize);
        match t {
            TAB_ONE => one,
            TAB_Y => &tb.y.lo[0][row * np..][..np],
            _ => &tb.x.lo[t as usize][row * np..][..np],
        }
    }

    /// The inner lists `r`'s sums into `s` (`(l − r.start)·np + p`).
    pub(super) fn plan_lists<const N: usize>(&self, tb: &Tabs<F>, r: Range<usize>, s: &mut [F]) {
        let np = if N == 0 { tb.np } else { N };
        let pl = self.plan.as_ref().unwrap();
        let mut acc = vec![F::UZ; np];
        let mut plain = vec![F::ZERO; np];
        for (k, l) in r.enumerate() {
            let tab = if pl.lside[l] { &tb.x.lo[0] } else { &tb.y.lo[0] };
            let mut prod = false;
            for &(row, c) in &pl.lent[pl.lptr[l] as usize..pl.lptr[l + 1] as usize] {
                let v = &tab[row as usize * np..][..np];
                if c == 0 {
                    for p in 0..np {
                        plain[p] += v[p];
                    }
                } else {
                    let c = self.coefs[c as usize];
                    prod = true;
                    for p in 0..np {
                        acc[p] ^= v[p].mul_unreduced(c);
                    }
                }
            }
            let d = &mut s[k * np..][..np];
            for p in 0..np {
                d[p] = if prod { acc[p].reduce() + plain[p] } else { plain[p] };
                acc[p] = F::UZ;
                plain[p] = F::ZERO;
            }
        }
    }

    /// The signatures `r`: each one's sum from its terms (`s`: every list's sum, list-major), then its instances.
    pub(super) fn plan_sigs<const N: usize>(&self, tb: &Tabs<F>, s: &[F], r: Range<usize>, out: &mut [F]) {
        let np = if N == 0 { tb.np } else { N };
        let pl = self.plan.as_ref().unwrap();
        let one = vec![F::ONE; np];
        let mut acc = vec![F::UZ; np];
        let mut u = vec![F::ZERO; np];
        for sg in r {
            for t in pl.tptr[sg] as usize..pl.tptr[sg + 1] as usize {
                for &rf in &pl.refs[pl.rptr[t] as usize..pl.rptr[t + 1] as usize] {
                    let o = Self::outer(tb, rf, np, &one);
                    for p in 0..np {
                        u[p] += o[p];
                    }
                }
                let sl = &s[pl.tlist[t] as usize * np..][..np];
                for p in 0..np {
                    acc[p] ^= u[p].mul_unreduced(sl[p]);
                    u[p] = F::ZERO;
                }
            }
            let g: Vec<F> = acc.iter().map(|a| a.reduce()).collect();
            acc.iter_mut().for_each(|a| *a = F::UZ);
            for it in &pl.inst[pl.iptr[sg] as usize..pl.iptr[sg + 1] as usize] {
                let hx = &tb.x.hi[it.hj as usize][it.hx as usize * np..][..np];
                let hy = &tb.y.hi[0][it.hy as usize * np..][..np];
                let d = &mut out[it.o as usize * np..][..np];
                if it.pat == NONE {
                    for p in 0..np {
                        d[p] += g[p] * hx[p] * hy[p];
                    }
                } else {
                    let pt = &tb.pat[it.pat as usize * np..][..np];
                    for p in 0..np {
                        d[p] += g[p] * hx[p] * hy[p] * pt[p];
                    }
                }
            }
        }
    }
}
