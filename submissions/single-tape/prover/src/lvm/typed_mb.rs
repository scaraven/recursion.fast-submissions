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
