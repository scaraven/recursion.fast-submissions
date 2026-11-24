//! R7: the mini-bus's real tables from the blob's `MINIBUS` section (`r3typed::circuit::MbExport`, EXPORT.md;
//! MBT's `mbT6`): seed arrays over `STREAM` cells (value columns = `C_rec` words) and read tables over the circuit's
//! cap `readd` cells (address and value columns = `T` words), with the finalize and count columns at the stated
//! stack words (inside `MB_LO..MB_HI`, r3mb's). Tables and columns as [`crate::typed_mb::tables`] builds them
//! (seeds first, then reads); the committed columns at the export's stack indices instead of [`crate::m3::place`]'s.

use primitives::field::F64;
use r3typed::circuit::MbExport;

use crate::prove::MbWitness;
use crate::tables::{MbCol, MbTab};
use crate::typed_mb::{MbRead, MbSeed, MbSpec, tables};

/// The stack indices of every table's committed columns, in [`tables`]' column order: a seed table `[v…, fin]`
/// (its fixed address column last), a read table `[addr, v…, cnt]`.
fn columns(m: &MbExport) -> Vec<Vec<usize>> {
    let seeds = m.seeds.iter().map(|(limbs, _, _, _, v, fin)| {
        assert_eq!(v.len(), *limbs);
        [v.clone(), vec![*fin]].concat()
    });
    let reads = m.reads.iter().map(|(limbs, _, addr, v, cnt)| {
        assert_eq!(v.len(), *limbs);
        [vec![*addr], v.clone(), vec![*cnt]].concat()
    });
    seeds.chain(reads).collect()
}

/// `m`'s tables with their columns placed (for the verifier: no values needed; the fixed address columns are the
/// seeds' `g^(base + stride·x)`).
pub fn tables_of(m: &MbExport) -> Vec<MbTab> {
    let spec = spec_of(m, &|_, n| vec![F64::ZERO; n], true);
    let (mut tabs, _) = crate::typed_mb::tables_unchecked(&spec);
    place(&mut tabs, m);
    crate::tables::check_static(&tabs);
    tabs
}

/// The witness of `m`'s tables on `stack` (the typed witness and `STREAM` already written): the seeds' and reads'
/// values read from the stack, the honest counts and finalizes computed.
pub fn witness_of(m: &MbExport, stack: &[F64]) -> MbWitness {
    let spec = spec_of(m, &|at, n| stack[at..at + n].to_vec(), false);
    if std::env::var_os("LVM6_MB_DIAG").is_some() {
        diag(&spec);
    }
    let (mut tabs, values) = tables(&spec);
    place(&mut tabs, m);
    MbWitness::new(tabs, values)
}

fn spec_of(m: &MbExport, read: &dyn Fn(usize, usize) -> Vec<F64>, _shape_only: bool) -> MbSpec {
    let seeds = m
        .seeds
        .iter()
        .map(|&(limbs, base, stride, tau, ref v, _)| MbSeed { limbs, base, stride, tau, vals: v.iter().map(|&c| read(c, 1 << tau)).collect() })
        .collect();
    let reads = m
        .reads
        .iter()
        .map(|&(limbs, tau, addr, ref v, _)| MbRead { limbs, tau, addr: read(addr, 1 << tau), vals: v.iter().map(|&c| read(c, 1 << tau)).collect() })
        .collect();
    MbSpec { seeds, reads }
}

fn place(tabs: &mut [MbTab], m: &MbExport) {
    let cols = columns(m);
    assert_eq!(tabs.len(), cols.len());
    for (t, at) in tabs.iter_mut().zip(cols) {
        let mut it = at.into_iter();
        for c in t.cols.iter_mut() {
            if let MbCol::Com { at } = c {
                *at = it.next().expect("a stack index per committed column");
            }
        }
        assert!(it.next().is_none(), "as many stack indices as committed columns");
    }
}

/// The mini-bus tables in use: the blob's `MINIBUS` section if it has one, else the stub's (seed `seed`).
pub fn tables_in_use(seed: u64) -> Vec<MbTab> {
    match r3typed::circuit::minibus() {
        Some(m) => tables_of(m),
        None => crate::stub::stub_witness(seed).tabs,
    }
}

/// The mini-bus witness in use on `stack`: the blob's tables, else the stub's (which also writes its columns).
pub fn witness_in_use(seed: u64, stack: &[F64]) -> MbWitness {
    match r3typed::circuit::minibus() {
        Some(m) => witness_of(m, stack),
        None => crate::stub::stub_witness(seed),
    }
}

/// Dev (R7, `LVM6_MB_DIAG`): every read row whose value is not its cell's seeded value (cell = the address's
/// exponent), with the cells holding the read value, if any.
fn diag(spec: &MbSpec) {
    use crate::typed_mb::seed_addr;
    let mut cell_of = std::collections::HashMap::new();
    let mut val_cells: std::collections::HashMap<u64, Vec<usize>> = std::collections::HashMap::new();
    let mut val_of = std::collections::HashMap::new();
    for s in &spec.seeds {
        for (x, a) in seed_addr(s.base, s.stride, s.tau).into_iter().enumerate() {
            let cell = s.base + s.stride * x;
            cell_of.insert(a.0, cell);
            val_of.insert(cell, s.vals[0][x].0);
            val_cells.entry(s.vals[0][x].0).or_default().push(cell);
        }
    }
    let (mut bad, mut n) = (0, 0);
    for (k, r) in spec.reads.iter().enumerate() {
        for x in 0..1usize << r.tau {
            n += 1;
            let Some(&cell) = cell_of.get(&r.addr[x].0) else {
                eprintln!("mb diag: read {k} row {x}: address not seeded");
                continue;
            };
            let v = r.vals[0][x].0;
            if v != val_of[&cell] {
                bad += 1;
                if bad <= 12 || std::env::var_os("LVM6_MB_DIAG_ALL").is_some() {
                    eprintln!("mb diag: read {k} row {x}: cell {cell} seeded {:#x} read {v:#x} (cells with that value: {:?})", val_of[&cell], val_cells.get(&v).map(|c| &c[..c.len().min(4)]));
                }
            }
        }
    }
    eprintln!("mb diag: {bad} of {n} reads differ from their cell's seed");
}
