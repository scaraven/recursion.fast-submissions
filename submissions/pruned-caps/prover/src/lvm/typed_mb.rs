//! B1-IE (lvm2 roll 8): the mini-bus's tables (B1-Q's `LvmQTypedMB.mbT`): `capTpl`'s `readd`s, the only reads left
//! on a bus, against seeds of the cap regions only (`2^13` leaves at P20). WP-9's memory checking: a read with count
//! column `c` pulls `⟨g^3, addr, c, val⟩` and pushes `⟨g^3, addr, g·c, val⟩`; a seed pushes `⟨g^3, addr, 1, val⟩` and
//! pulls `⟨g^3, addr, fin, val⟩` (`Tab.flushes`: reads' pulls, their pushes, seeds, finalizes).
//! - **Seeds** (`mbArrs`): `InArr.tab` of `2^4` stream cells `base + 17x` (values: `C_rec` words, pre-placed), the
//!   finalize column (`g^{reads}`, written at its placement), the fixed address column `g^{base + 17x}`.
//! - **Reads** (`capReads`, `readTab`): per `capTpl` `readd` row, `2^ℓ` rows: the address column (the `readd`'s
//!   address cells' words, pre-placed in `C_main`'s typed region), the value column (its result cells' words), the
//!   count column (written at its placement).
//!
//! The honest counts: the reads in table order, row order; the `k`-th read of a cell has count `g^k`, its seed's
//! finalize is `g^{m}` for `m` reads.
use std::collections::HashMap;

use crate::lv::leanvm_core::leaf::Coord;
use crate::lv::primitives::field::{F64, g_pow};
use crate::lvm::loopir::{Compiled, Ty, unflat};
use crate::lvm::m3::{FlushW, InArr, TableW};

/// A seed array: `2^tau` cells `base + stride·x`, values at `val` (`C_rec` or `C_main` offset), finalize at `fin`.
#[derive(Clone, Debug)]
pub struct MbSeed {
    pub base: usize,
    pub stride: usize,
    pub tau: usize,
    pub val: (bool, usize),
    pub fin: (bool, usize),
}

/// A read table: a `readd` row over its `2^tau` iterations; address, value and count columns at `wa`, `wv`, `cnt`
/// (commitment offsets). `blk`, `row` (dev specs only): the row, whose cells give the columns; else (B1-IX's blob)
/// the address and value columns are read from the commitment, where `z` put them.
#[derive(Clone, Debug)]
pub struct MbRead {
    pub blk: usize,
    pub row: usize,
    pub tau: usize,
    pub wa: (bool, usize),
    pub wv: (bool, usize),
    pub cnt: (bool, usize),
}

#[derive(Clone, Debug, Default)]
pub struct MbSpec {
    pub seeds: Vec<MbSeed>,
    pub reads: Vec<MbRead>,
}

impl MbSpec {
    /// `S base stride tau valRec valOff finRec finOff` and `R blk row tau waRec waOff wvRec wvOff cntRec cntOff`.
    pub fn parse(text: &str) -> MbSpec {
        let mut m = MbSpec::default();
        for l in text.lines() {
            let t: Vec<&str> = l.split_whitespace().collect();
            let n = |i: usize| -> usize { t[i].parse().unwrap_or_else(|_| panic!("mb spec: {l:?}")) };
            match t.first() {
                Some(&"S") => m.seeds.push(MbSeed { base: n(1), stride: n(2), tau: n(3), val: (n(4) == 1, n(5)), fin: (n(6) == 1, n(7)) }),
                Some(&"R") => m.reads.push(MbRead { blk: n(1), row: n(2), tau: n(3), wa: (n(4) == 1, n(5)), wv: (n(6) == 1, n(7)), cnt: (n(8) == 1, n(9)) }),
                None => {}
                Some(x) => panic!("mb spec: line tag {x:?}"),
            }
        }
        m
    }

    /// Every committed column `(table, column, (rec, off), written)` (seeds: value checked, finalize written; reads:
    /// address and value checked, count written).
    pub fn columns(&self) -> Vec<(usize, usize, (bool, usize), bool, usize)> {
        let mut v = Vec::new();
        for (i, s) in self.seeds.iter().enumerate() {
            v.push((i, 0, s.val, false, s.tau));
            v.push((i, 1, s.fin, true, s.tau));
        }
        let ns = self.seeds.len();
        for (i, r) in self.reads.iter().enumerate() {
            v.push((ns + i, 0, r.wa, false, r.tau));
            v.push((ns + i, 1, r.wv, false, r.tau));
            v.push((ns + i, 2, r.cnt, true, r.tau));
        }
        v
    }
}

/// The address cell and the result cell of `readd` row `t` of block `b` at iteration `jf`.
fn read_cells(c: &Compiled, b: usize, t: usize, jf: usize) -> (usize, usize) {
    let blk = &c.q.blocks[b];
    let l = &c.lay[b];
    let a = blk.tpl[t].args[0].at(&unflat(&blk.dims, jf));
    (a, l.start[0] + l.tw[0] * jf + l.rank[t][0])
}

/// **The mini-bus's tables** on the run's cells `kc` (the seeds' values are the stream cells' inputs, which are
/// `C_rec`'s words there).
pub fn tables(m: &MbSpec, c: &Compiled, kc: &[F64]) -> Vec<TableW> {
    tables_with(m, c, kc, None)
}

/// [`tables`]; with `com` (`(rec, off, len) ↦` the commitment's words, big-layout offsets) the read tables' address and
/// value columns are the commitment's (B1-IX's blob gives no rows: `blk = usize::MAX`).
pub fn tables_with(m: &MbSpec, c: &Compiled, kc: &[F64], com: Option<&dyn Fn(bool, usize, usize) -> Vec<F64>>) -> Vec<TableW> {
    // the seeded cells by address
    let mut by_addr: HashMap<u64, usize> = HashMap::new();
    for s in &m.seeds {
        for x in 0..1usize << s.tau {
            let cell = s.base + s.stride * x;
            by_addr.insert(c.g(cell).0, cell);
        }
    }
    let mut reads: HashMap<usize, usize> = HashMap::new();
    let g = g_pow(1);
    let mut rt: Vec<TableW> = Vec::with_capacity(m.reads.len());
    let sep = Coord::Const(crate::lvm::loopir::sep(Ty::K));
    for (ri, r) in m.reads.iter().enumerate() {
        let n = 1usize << r.tau;
        let (mut ad, mut va, mut cn) = (Vec::with_capacity(n), Vec::with_capacity(n), Vec::with_capacity(n));
        let cols = match (r.blk, com) {
            (usize::MAX, Some(f)) => Some((f(r.wa.0, r.wa.1, n), f(r.wv.0, r.wv.1, n))),
            (usize::MAX, None) => panic!("a read table without its row needs the commitment's columns"),
            _ => {
                assert!(matches!(c.q.blocks[r.blk].tpl[r.row].op, crate::lvm::loopir::Op::Readd(..)), "a mini-bus read is a readd row");
                assert_eq!(c.lay[r.blk].size, n, "a read table has its block's iterations");
                None
            }
        };
        for jf in 0..n {
            let (addr, val) = match &cols {
                Some((a, v)) => (a[jf], v[jf]),
                None => {
                    let (a, res) = read_cells(c, r.blk, r.row, jf);
                    (kc[a], kc[res])
                }
            };
            let cell = *by_addr.get(&addr.0).unwrap_or_else(|| panic!("a cap read's target is seeded (read table {ri}, iteration {jf})"));
            let k = reads.entry(cell).or_insert(0);
            cn.push(c.g(*k));
            *k += 1;
            ad.push(addr);
            va.push(val);
        }
        rt.push(TableW {
            tau: r.tau,
            cols: vec![ad, va, cn],
            com: vec![true; 3],
            cons: Vec::new(),
            flushes: vec![
                FlushW { push: false, coords: vec![sep.clone(), Coord::Col(0), Coord::Col(2), Coord::Col(1)], count: Some(2) },
                FlushW { push: true, coords: vec![sep.clone(), Coord::Col(0), Coord::GCol(2, 1), Coord::Col(1)], count: None },
            ],
            pre: vec![(0, r.wa.0, r.wa.1, false), (1, r.wv.0, r.wv.1, false), (2, r.cnt.0, r.cnt.1, true)],
            hdr: false,
        });
    }
    let _ = g;
    let mut out: Vec<TableW> = m
        .seeds
        .iter()
        .map(|s| {
            let n = 1usize << s.tau;
            let vals = vec![(0..n).map(|x| kc[s.base + s.stride * x]).collect()];
            let fin = (0..n).map(|x| c.g(reads.get(&(s.base + s.stride * x)).copied().unwrap_or(0))).collect();
            let mut t = InArr { ty: Ty::K, tau: s.tau, base: s.base, stride: s.stride, vals, fin, pre: vec![Some(s.val)], public: false }.table();
            t.pre.push((1, s.fin.0, s.fin.1, true));
            t
        })
        .collect();
    out.extend(rt);
    out
}

/// MBL G0-2 (dev): the three trees' final leaf claims `Ṽ_push(ζ)`, `Ṽ_pull(ζ)`, `Ṽ_count(ζ)` from the IDENTITY (MBL
/// COMMON), independently of `leaf.rs`'s forms: per side, the blocks (seeds then reads; push/pull one per table, count
/// one per read) stacked largest-first at aligned offsets, `μ` the push side's depth;
/// `Ṽ_s(ζ) = (1 + Σ_b eq(ζ_hi, sel_b)) + Σ_b eq(ζ_hi, sel_b)·(β_s + Σ_i w_{s,i}·coord_i~(ζ[..τ_b]))`,
/// `w = eq(α⃗, ·)` (push, pull; count: `w = [1, 0, …]`, `β = 0`), the committed columns' MLEs from `C_main`'s words
/// at their placements (`tabs`' `pre`), a seed's address column in closed form
/// `g^base·Π_k((1 + ζ_k) + ζ_k·g^(stride·2^k))`. Returns the three values and how many placed words differ from the
/// tables' own columns.
pub fn lin_identity(m: &MbSpec, tabs: &[TableW], cmain: &[F64], zeta: &[crate::lv::primitives::field::F192], alphas: &[crate::lv::primitives::field::F192], beta: crate::lv::primitives::field::F192) -> ([crate::lv::primitives::field::F192; 3], usize) {
    use crate::lv::primitives::field::F192;
    let one = F192::ONE;
    // the MLE, least significant variable first
    let mle = |v: &[F64], r: &[F192]| -> F192 {
        assert_eq!(v.len(), 1 << r.len());
        let mut cur: Vec<F192> = v.iter().map(|&x| F192::from(x)).collect();
        for &rk in r {
            cur = cur.chunks(2).map(|p| p[0] + rk * (p[1] + p[0])).collect();
        }
        cur[0]
    };
    let eqb = |r: &[F192], x: usize| -> F192 { r.iter().enumerate().fold(one, |a, (k, &rk)| a * if (x >> k) & 1 == 1 { rk } else { one + rk }) };
    assert_eq!(tabs.len(), m.seeds.len() + m.reads.len(), "the tables are the seeds, then the reads");
    let mut bad = 0usize;
    // committed column `c` of table `t` at `ζ[..τ]`, from C_main's words at its placement
    let mut col = |t: usize, c: usize, tau: usize| -> F192 {
        let (_, rec, o, _) = *tabs[t].pre.iter().find(|x| x.0 == c).expect("every mini-bus column is pre-placed");
        assert!(!rec, "a mini-bus column is C_main's");
        let w = &cmain[o..o + (1 << tau)];
        bad += w.iter().zip(&tabs[t].cols[c]).filter(|(a, b)| a != b).count();
        mle(w, &zeta[..tau])
    };
    let sep = F192::from(crate::lvm::loopir::sep(Ty::K));
    let g = g_pow(1);
    // per side: (τ, slot values)
    let mut sides: [Vec<(usize, Vec<F192>)>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for (i, s) in m.seeds.iter().enumerate() {
        assert_eq!(tabs[i].tau, s.tau);
        let r = &zeta[..s.tau];
        let addr = (0..s.tau).fold(F192::from(g_pow(s.base)), |a, k| a * ((one + r[k]) + r[k].mul_base(g_pow(s.stride << k))));
        let (val, fin) = (col(i, 0, s.tau), col(i, 1, s.tau));
        sides[0].push((s.tau, vec![sep, addr, one, val]));
        sides[1].push((s.tau, vec![sep, addr, fin, val]));
    }
    for (j, rd) in m.reads.iter().enumerate() {
        let t = m.seeds.len() + j;
        assert_eq!(tabs[t].tau, rd.tau);
        let (a, v, n) = (col(t, 0, rd.tau), col(t, 1, rd.tau), col(t, 2, rd.tau));
        sides[0].push((rd.tau, vec![sep, a, n.mul_base(g), v]));
        sides[1].push((rd.tau, vec![sep, a, n, v]));
        sides[2].push((rd.tau, vec![n]));
    }
    let offsets = |blks: &[(usize, Vec<F192>)]| -> (Vec<usize>, usize) {
        let mut ord: Vec<usize> = (0..blks.len()).collect();
        ord.sort_by(|&a, &b| blks[b].0.cmp(&blks[a].0).then(a.cmp(&b)));
        let mut off = vec![0; blks.len()];
        let mut at = 0usize;
        for i in ord {
            assert_eq!(at % (1 << blks[i].0), 0, "aligned");
            off[i] = at;
            at += 1 << blks[i].0;
        }
        (off, at)
    };
    let mu = offsets(&sides[0]).1.next_power_of_two().trailing_zeros() as usize;
    assert_eq!(mu, zeta.len(), "the GKR point has the push side's depth");
    let w_fp: Vec<F192> = (0..16).map(|i| eqb(alphas, i)).collect();
    let out: [F192; 3] = std::array::from_fn(|s| {
        let (off, total) = offsets(&sides[s]);
        assert!(total <= 1 << mu);
        let (w, b) = if s == 2 { ((0..16).map(|i| if i == 0 { one } else { F192::ZERO }).collect::<Vec<_>>(), F192::ZERO) } else { (w_fp.clone(), beta) };
        let mut v = one;
        for (bi, (tau, co)) in sides[s].iter().enumerate() {
            let e = eqb(&zeta[*tau..], off[bi] >> tau);
            v += e; // padding mass: 1 + Σ_b eq(ζ_hi, sel_b)
            v += e * co.iter().zip(&w).fold(b, |a, (&c, &wi)| a + wi * c);
        }
        v
    });
    (out, bad)
}
