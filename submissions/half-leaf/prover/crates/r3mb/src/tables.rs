//! The mini-bus's tables, as the Lean states them (`LvmM3Tab.Tab`; FORMAT6 §6.4's claims 50–52 range over them):
//! a table of `2^τ` rows has columns (committed at a stack offset, or fixed: verifier-known), **reads** (a key and
//! the read-count column) and **seeds** (a key and the finalize-count column), no constraint. A key is a
//! separator, an address and value limbs. Season 1's memory checking (WP-9, `LvmM3Inst.Tab.flushes`): a read with
//! count column `c` pulls `⟨sep, addr, c, val⟩` and pushes `⟨sep, addr, g·c, val⟩`; a seed pushes
//! `⟨sep, addr, 1, val⟩` and pulls `⟨sep, addr, fin, val⟩`; the count tree multiplies every read's count.
//!
//! **The swappable interface.** A real table set (CD's generator, TY's typed memory `T`) is a `Vec<MbTab>` and its
//! committed columns' values ([`crate::MbWitness`]); [`crate::stub`] builds one until then. The static conditions
//! the prover and the verifier assume are [`MbTab::check_static`]'s: roll #32's tableless form (`mbLinB6`: every
//! key coordinate and count a constant or one column with a coefficient `g^k`), committed columns aligned inside
//! the mini-bus region of the stack, and the walk's depth [`crate::MINI_DEPTH`].

use crate::leaf::Coord;
use primitives::field::{F64, g_pow};

/// A column (Lean `ColSrc`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MbCol {
    /// Committed: row `x` is stack word `at + x` (`2^τ | at`; r3mb writes the columns inside `MB_LO..MB_HI`, the
    /// others are the typed witness's `T` or `STREAM` words, R7). In v6's one stack a window
    /// claim is a stack claim, so Lean's `com false off` is this with `at` the stack offset.
    Com { at: usize },
    /// Fixed (verifier-known): row `x` is `values[x]`; it enters the claims' values through its multilinear
    /// extension (Lean `mleFixG`), never as a claim.
    Fix(Vec<F64>),
}

/// A column not placed yet ([`crate::m3::place`] places it).
pub const UNPLACED: usize = usize::MAX;

/// A key (Lean `Key`): separator, address, value limbs. Each coordinate is a `Coord` restricted to `Const`, `Col`,
/// `GCol` and `Sum`s of those (Lean `CPoly` with every monomial of at most one column, `cpolyLinB`; a coefficient
/// `g^k` is `GCol(_, k)`).
#[derive(Clone, Debug)]
pub struct MbKey {
    pub sep: F64,
    pub addr: Coord,
    pub val: Vec<Coord>,
}

/// A table (Lean `Tab` with `cons = []`).
#[derive(Clone, Debug)]
pub struct MbTab {
    pub tau: usize,
    pub cols: Vec<MbCol>,
    /// `(key, read-count column)`.
    pub reads: Vec<(MbKey, usize)>,
    /// `(key, finalize-count column)`.
    pub seeds: Vec<(MbKey, usize)>,
}

/// The separator of `K` cells (`g^3`) and of `E` cells (`g^4`) (Lean `Key.sep`).
pub fn sep_of(limbs: usize) -> F64 {
    match limbs {
        1 => g_pow(3),
        2 => g_pow(4),
        _ => panic!("a cell has one (K) or two (E) limbs"),
    }
}

/// A coordinate as Lean's `CPoly`: `(coefficient, None)` for a constant, `(coefficient, Some(column))` for a column.
pub fn cpoly(c: &Coord) -> Vec<(F64, Option<usize>)> {
    match c {
        Coord::Const(v) => vec![(*v, None)],
        Coord::Col(i) => vec![(F64::ONE, Some(*i))],
        Coord::GCol(i, k) => vec![(g_pow(*k as usize), Some(*i))],
        Coord::Sum(cs) => cs.iter().flat_map(cpoly).collect(),
        Coord::Prod(..) | Coord::Index | Coord::Public(_) => {
            panic!("mbLinB6: a mini-bus coordinate is a constant or one column")
        }
    }
}

/// Which side a flush sits on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Push,
    Pull,
}

/// A flush: its side, its tuple `⟨sep, addr, cnt, val…⟩`, and (a read's pull) the count column the count tree takes.
#[derive(Clone, Debug)]
pub struct Flush {
    pub side: Side,
    pub coords: Vec<Coord>,
    pub count: Option<usize>,
}

impl MbKey {
    /// `⟨sep, addr, cnt, val…⟩` (Lean `Key.vec`: separator, address, count, value limbs).
    pub fn tuple(&self, cnt: Coord) -> Vec<Coord> {
        [vec![Coord::Const(self.sep), self.addr.clone(), cnt], self.val.clone()].concat()
    }

    /// The columns the key names (Lean `sideColsG`'s `keyCols`).
    pub fn cols(&self) -> Vec<usize> {
        std::iter::once(&self.addr).chain(&self.val).flat_map(cpoly).filter_map(|m| m.1).collect()
    }
}

impl MbTab {
    pub fn width(&self) -> usize {
        self.cols.len()
    }

    /// The flushes in Lean's order (`LvmM3Inst.Tab.flushes`): the reads' pulls (each carrying its count column for
    /// the count tree), the reads' pushes (`g·c`), the seeds (count `1`), the finalizes. Per side this is Lean's
    /// `sideBlocksG` order: push = reads then seeds, pull = reads then finalizes, count = reads.
    pub fn flushes(&self) -> Vec<Flush> {
        let mut f = Vec::new();
        for (k, c) in &self.reads {
            f.push(Flush { side: Side::Pull, coords: k.tuple(Coord::Col(*c)), count: Some(*c) });
        }
        for (k, c) in &self.reads {
            f.push(Flush { side: Side::Push, coords: k.tuple(Coord::GCol(*c, 1)), count: None });
        }
        for (k, _) in &self.seeds {
            f.push(Flush { side: Side::Push, coords: k.tuple(Coord::Const(F64::ONE)), count: None });
        }
        for (k, c) in &self.seeds {
            f.push(Flush { side: Side::Pull, coords: k.tuple(Coord::Col(*c)), count: None });
        }
        f
    }

    /// The committed columns side `s` (0 push, 1 pull, 2 count) names, in column order (Lean `sideColsG` filtered
    /// to committed columns, as `mbPartsG` does).
    pub fn side_cols(&self, s: usize) -> Vec<usize> {
        let keys: Vec<usize> = self.reads.iter().chain(&self.seeds).flat_map(|(k, _)| k.cols()).collect();
        let reads: Vec<usize> = self.reads.iter().map(|r| r.1).collect();
        let named: Vec<usize> = match s {
            0 => [keys, reads].concat(),
            1 => [keys, reads, self.seeds.iter().map(|x| x.1).collect()].concat(),
            2 => reads,
            _ => panic!("three sides"),
        };
        (0..self.width()).filter(|c| named.contains(c) && matches!(self.cols[*c], MbCol::Com { .. })).collect()
    }

    /// The static conditions (panics: a table set violating them is a generator bug, not an input): no more than
    /// sixteen coordinates (`BUS_BITS`), every coordinate linear (`mbLinB6`), every column index in range, the
    /// height at most `2^13`, fixed columns of `2^τ` values, committed columns aligned blocks of the stack.
    pub fn check_static(&self) {
        assert!(self.tau <= 13, "a mini-bus table has at most 2^13 rows (FORMAT6 §T)");
        for (k, c) in self.reads.iter().chain(&self.seeds) {
            assert!(3 + k.val.len() <= 1 << verifier::layout::BUS_BITS, "a tuple has at most 16 coordinates");
            for col in k.cols().into_iter().chain([*c]) {
                assert!(col < self.width(), "a key or count names a column of its table");
            }
            let _ = cpoly(&k.addr);
            k.val.iter().for_each(|v| drop(cpoly(v)));
        }
        for col in &self.cols {
            match col {
                MbCol::Fix(v) => assert_eq!(v.len(), 1 << self.tau, "a fixed column has 2^τ values"),
                MbCol::Com { at } => {
                    assert!(*at != UNPLACED, "every committed column is placed");
                    assert_eq!(at % (1 << self.tau), 0, "a committed column is an aligned block");
                    assert!(at + (1 << self.tau) <= r3core::layout::LANES << r3core::layout::ROW_LOG, "a mini-bus column lies in the committed lanes");
                }
            }
        }
    }
}

/// The walk's depth of a table set: `⌈log₂ Σ 2^τ⌉` over the push side's blocks (one per read and per seed).
pub fn depth(tabs: &[MbTab]) -> usize {
    let total: usize = tabs.iter().map(|t| (t.reads.len() + t.seeds.len()) << t.tau).sum();
    crate::log2_ceil_usize(total)
}

/// Every table's static conditions, no two committed columns overlapping, and depth [`crate::MINI_DEPTH`].
pub fn check_static(tabs: &[MbTab]) {
    let mut spans: Vec<(usize, usize)> = Vec::new();
    for t in tabs {
        t.check_static();
        for c in &t.cols {
            if let MbCol::Com { at } = c {
                spans.push((*at, at + (1 << t.tau)));
            }
        }
    }
    spans.sort_unstable();
    // a column may alias another (the same block, as season 1's seeds alias stream columns), never overlap it partly
    spans.dedup();
    assert!(spans.windows(2).all(|w| w[0].1 <= w[1].0), "committed columns do not overlap");
    assert_eq!(depth(tabs), crate::MINI_DEPTH, "FORMAT6 §6.4b walks depth 12 (6 two-level steps)");
}
