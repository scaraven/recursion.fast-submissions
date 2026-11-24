//! Season 1's `lvm/typed_mb.rs` (B1-IE, `archive/season-1/wide-packs/prover/src/lvm/typed_mb.rs`) ported from
//! F192 to F128 and from LoopIR cells to plain arrays: the mini-bus's tables as WP-9's memory checking over seed
//! arrays and read tables, with the honest counts.
//! - **Seeds** (`InArr`): `2^τ` cells `base + stride·x` of one memory (`K`: one limb, separator `g^3`; `E`: two
//!   limbs, `g^4`); columns: the value limbs (committed), the finalize column (committed, `g^{reads}`), the fixed
//!   address column `g^{base + stride·x}`.
//! - **Reads**: `2^τ` rows, each reading one seeded cell; columns: the address (committed), the value limbs
//!   (committed), the count (committed, written by [`tables`]).
//!
//! The honest counts: the reads in table order, row order; the `k`-th read of a cell has count `g^k`, its seed's
//! finalize is `g^m` for `m` reads. Then per cell push `{1, g, …, g^m}` = pull `{1, …, g^{m−1}, g^m}`.
//! Every committed column is left [`UNPLACED`] for [`crate::m3::place`] (S1: pre-placed in `C_main`/`C_rec`).

use std::collections::HashMap;

use crate::leaf::Coord;
use crate::tables::{MbCol, MbKey, MbTab, UNPLACED, sep_of};
use primitives::field::{F64, g_pow};

/// A seed array.
#[derive(Clone, Debug)]
pub struct MbSeed {
    pub limbs: usize,
    pub base: usize,
    pub stride: usize,
    pub tau: usize,
    /// `vals[l][x]`: limb `l` of cell `base + stride·x`.
    pub vals: Vec<Vec<F64>>,
}

/// A read table of one memory: row `x` reads the cell at address `addr[x]` (a seeded cell's `g^{cell}`), value
/// `vals[·][x]`.
#[derive(Clone, Debug)]
pub struct MbRead {
    pub limbs: usize,
    pub tau: usize,
    pub addr: Vec<F64>,
    pub vals: Vec<Vec<F64>>,
}

#[derive(Clone, Debug, Default)]
pub struct MbSpec {
    pub seeds: Vec<MbSeed>,
    pub reads: Vec<MbRead>,
}

/// The address column `g^(base + stride·x)`, `x < 2^tau` (S1 `InArr::addr`).
pub fn seed_addr(base: usize, stride: usize, tau: usize) -> Vec<F64> {
    let step = g_pow(stride);
    let mut a = g_pow(base);
    (0..1usize << tau)
        .map(|_| {
            let v = a;
            a = a * step;
            v
        })
        .collect()
}

/// **The mini-bus's tables** of `m` (seeds first, then reads) and every column's values (`values[t][c]`; a fixed
/// column's are its description's). Committed columns are [`UNPLACED`].
pub fn tables(m: &MbSpec) -> (Vec<MbTab>, Vec<Vec<Vec<F64>>>) {
    tables_skipping(m, &[])
}

/// [`tables`], where the read rows `(read table, row)` in `zero` get count `0` and leave their cell's counter alone
/// (dev only: an honest-looking witness whose count tree's product is zero, for the verifier's `count ≠ 0` check;
/// such a row's push `⟨…, g·0, …⟩` and pull `⟨…, 0, …⟩` are the same tuple, so the bus still balances).
pub fn tables_skipping(m: &MbSpec, zero: &[(usize, usize)]) -> (Vec<MbTab>, Vec<Vec<Vec<F64>>>) {
    tables_with(m, zero, true)
}

/// [`tables`]' shapes without the reads' targets checked (the verifier's tables: no values).
pub fn tables_unchecked(m: &MbSpec) -> (Vec<MbTab>, Vec<Vec<Vec<F64>>>) {
    tables_with(m, &[], false)
}

fn tables_with(m: &MbSpec, zero: &[(usize, usize)], honest: bool) -> (Vec<MbTab>, Vec<Vec<Vec<F64>>>) {
    // the seeded cells by (separator, address)
    let mut seeded: HashMap<(u64, u64), (usize, usize)> = HashMap::new();
    for (i, s) in m.seeds.iter().enumerate() {
        assert_eq!(s.vals.len(), s.limbs);
        for (x, a) in seed_addr(s.base, s.stride, s.tau).into_iter().enumerate() {
            let old = seeded.insert((sep_of(s.limbs).0, a.0), (i, x));
            assert!(old.is_none(), "a cell is seeded once");
        }
    }
    let mut reads: Vec<Vec<u64>> = m.seeds.iter().map(|s| vec![0; 1 << s.tau]).collect();
    let mut tabs = Vec::new();
    let mut values = Vec::new();
    let mut rt = Vec::new();
    let mut rv = Vec::new();
    for (ri, r) in m.reads.iter().enumerate() {
        let n = 1usize << r.tau;
        assert!(r.addr.len() == n && r.vals.len() == r.limbs && r.vals.iter().all(|v| v.len() == n));
        let mut cn = Vec::with_capacity(n);
        for x in 0..n {
            if !honest {
                cn.push(F64::ZERO);
                continue;
            }
            let &(i, cell) = seeded
                .get(&(sep_of(r.limbs).0, r.addr[x].0))
                .unwrap_or_else(|| panic!("a read's target is seeded (read table {ri}, row {x})"));
            if zero.contains(&(ri, x)) {
                cn.push(F64::ZERO);
                continue;
            }
            let k = &mut reads[i][cell];
            cn.push(g_pow(*k as usize));
            *k += 1;
        }
        let lim = r.limbs;
        let key = MbKey { sep: sep_of(lim), addr: Coord::Col(0), val: (1..=lim).map(Coord::Col).collect() };
        rt.push(MbTab {
            tau: r.tau,
            cols: vec![MbCol::Com { at: UNPLACED }; lim + 2],
            reads: vec![(key, lim + 1)],
            seeds: Vec::new(),
        });
        rv.push([vec![r.addr.clone()], r.vals.clone(), vec![cn]].concat());
    }
    for (i, s) in m.seeds.iter().enumerate() {
        let lim = s.limbs;
        let fin: Vec<F64> = reads[i].iter().map(|&k| g_pow(k as usize)).collect();
        let addr = seed_addr(s.base, s.stride, s.tau);
        let key = MbKey { sep: sep_of(lim), addr: Coord::Col(lim + 1), val: (0..lim).map(Coord::Col).collect() };
        tabs.push(MbTab {
            tau: s.tau,
            cols: [vec![MbCol::Com { at: UNPLACED }; lim + 1], vec![MbCol::Fix(addr.clone())]].concat(),
            reads: Vec::new(),
            seeds: vec![(key, lim)],
        });
        values.push([s.vals.clone(), vec![fin, addr]].concat());
    }
    tabs.extend(rt);
    values.extend(rv);
    (tabs, values)
}
