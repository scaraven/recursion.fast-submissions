//! B1-P (lvm2 roll 8, `docs/lvm2/design/B-DES.md` §1.1–§1.3, `stages/B1-G0.md`): the typed bus-free backend's
//! prover, from B1-P5's probe (`lvm2/B1P5` 99af264c, `lvm/b1.rs`). Dev path (`lvm-prover typed …`); the shipped
//! proving path does not call it until G2 (the bus path is the byte-identity oracle).
//!
//! - **y-space** (`2^y_log` words, `K`-valued): per loop block and result type a region of `2^(w + ℓ)` words per
//!   limb (`2^w` ≥ the block's committed writers of that type, `2^ℓ` its iterations; word `(rank << ℓ) | jf`),
//!   then the virtual regions: the `K` input cells, the `E` input cells' limbs, the constant 1. Regions are
//!   powers of two, placed largest first (so aligned). `loadE` cells are virtual (no word): an operand naming
//!   one is the three entries `1, Y, Y²` on its `K` arguments' words. `assert0` writes nothing. (B1-K's layout dump,
//!   binary-chunked, replaces this placement at INT; the kernels below take any layout with iteration bits low.)
//! - **x-space** (`2^x_log` slots): per block `2^(c + ℓ)` slots, slot `(crow << ℓ) | jf`, one per row instance
//!   with a constraint: `muladd`, `lin`, `assert0`, and the `readd`s whose argument is public-derived (QLT: their
//!   address is static, a `D` operand). `capTpl`'s `readd`s go to the mini-bus: their result word is committed but
//!   they have no slot.
//! - **matrices** `A, B, D, W` over `E`: `(Az)(x)·(Bz)(x) + (Dz)(x) + (Wz)(x) = 0` per slot.
//! - **protocol** (B-DES §1.2): zerocheck (degree 3, `x_log` rounds; the honest prover's `Cz = Az∘Bz`), `a*, b*, c*`;
//!   `γ`; wiring sumcheck (degree 2, `y_log` rounds) on `u(y) = Σ_x eq(r_x, x)·(M_A + γM_B + γ²M_{D+W})(x, y)`;
//!   `v_o = M̃_o(r_x, r_y)`; `κ ∈ E²`; the A23 line polynomial `h` of `Φ_Q(o, x, y)` (`2 + x_log + y_log` variables)
//!   through the incoming accumulator point and `(κ, r_x, r_y)`; `t`. `v_o` and `h` come from the class kernels
//!   ([`super::typed_phi::PhiK`]). Challenges from a seeded RNG here (the FS order is B1-V's `typedProg`).

use std::collections::HashMap;
use std::time::Instant;

use crate::lv::primitives::field::{F64, F192, F192Unreduced};
use crate::lv::primitives::multilinear::{eq_table, mle_eval_par, poly_eval};
use crate::lvm::loopir::{ArrKind, Compiled, M3Spec, Op, Run, Ty, unflat};
use crate::lvm::typed_phi::PhiK;

// ---------------------------------------------------------------- inputs

/// The assembled inputs of one build (`in_k` before the BITS fixpoint, `in_e`) and the header lanes it was given.
pub struct Inputs {
    pub in_k: Vec<F64>,
    pub in_e: Vec<F192>,
    pub hdr: Vec<u64>,
}

/// `LVM_TYPED_DUMP`: `nK, K words, nE, 3·nE limbs, nH, header lanes`, u64 LE, one file per build.
pub fn dump_inputs(dir: &std::path::Path, in_k: &[F64], in_e: &[F192], hdr: &[u64]) {
    let mut v: Vec<u64> = vec![in_k.len() as u64];
    v.extend(in_k.iter().map(|x| x.0));
    v.push(in_e.len() as u64);
    for e in in_e {
        v.extend(e.to_limbs());
    }
    v.push(hdr.len() as u64);
    v.extend(hdr);
    let ns = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_nanos());
    let path = dir.join(format!("in-{}-{ns}.bin", std::process::id()));
    let b: Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
    if let Err(e) = std::fs::write(&path, b) {
        eprintln!("lvm: LVM_TYPED_DUMP {}: {e}", path.display());
    }
}

pub fn read_inputs(path: &str) -> Inputs {
    let b = std::fs::read(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let w: Vec<u64> = b.chunks(8).map(|x| u64::from_le_bytes(x.try_into().unwrap())).collect();
    let nk = w[0] as usize;
    let in_k = w[1..1 + nk].iter().map(|&x| F64(x)).collect();
    let ne = w[1 + nk] as usize;
    let o = 2 + nk;
    let in_e = (0..ne).map(|i| F192::new(w[o + 3 * i], w[o + 3 * i + 1], w[o + 3 * i + 2])).collect();
    let o = o + 3 * ne;
    let nh = w[o] as usize;
    let hdr = w[o + 1..o + 1 + nh].to_vec();
    Inputs { in_k, in_e, hdr }
}

/// The `col` closure of `stream::build_q_tables` served from dumped inputs (aliased arrays' values).
pub fn col_of<'a>(spec: &'a M3Spec, inp: &'a Inputs) -> impl Fn(bool, usize, usize) -> Vec<F64> + 'a {
    let mut at: HashMap<(bool, usize), (usize, usize)> = HashMap::new();
    for (i, a) in spec.arrs.iter().enumerate() {
        if a.kind == ArrKind::Aliased {
            for (l, &(r, o)) in a.val.iter().enumerate() {
                at.insert((r, o), (i, l));
            }
        }
    }
    move |r, o, n| {
        let &(i, l) = at.get(&(r, o)).expect("an aliased array's placement");
        let a = &spec.arrs[i];
        (0..n)
            .map(|x| {
                let e = a.base + a.stride * x;
                match a.ty {
                    Ty::K => inp.in_k[e],
                    Ty::E => F64(inp.in_e[e].to_limbs()[l]),
                }
            })
            .collect()
    }
}

/// The node program's run on the assembled inputs: `stream::build_q_tables`'s BITS fixpoint (copied; the
/// tables are not built). Returns the run (its `kc` holds the final inputs).
pub fn run_fixpoint(c: &Compiled, spec: &M3Spec, inp: &Inputs) -> Run {
    let mut in_k = inp.in_k.clone();
    let in_e = &inp.in_e;
    let mut runs = 0;
    loop {
        let run = c.interp(&in_k, in_e);
        runs += 1;
        let mut changed = false;
        for (bi, b) in spec.bits.iter().enumerate() {
            for x in 0..b.n {
                let w = match spec.free.iter().find(|f| f.0 == bi) {
                    Some(&(_, 0, cell)) => crate::lvm::m3::free_checksum(&in_k[cell..cell + 4]),
                    Some(&(_, k, _)) => panic!("free word kind {k}"),
                    None => run.kc[b.wc[x]].0,
                };
                for (j, o) in b.outs.iter().enumerate() {
                    let e = b.oc[j][x];
                    let v = F64(o.word(w));
                    if in_k[e] != v {
                        in_k[e] = v;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            return run;
        }
        assert!(runs < 64, "the BITS outputs settle");
    }
}

// ---------------------------------------------------------------- layout and matrices

pub const MA: u8 = 0;
pub const MB: u8 = 1;
pub const MD: u8 = 2;
pub const MW: u8 = 3;
const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug)]
pub struct Ent {
    pub y: u32,
    pub o: u8,
    pub c: F192,
}

#[derive(Clone, Copy, Debug)]
pub struct CEnt {
    pub x: u32,
    pub o: u8,
    pub c: F192,
}

/// `Y^m`.
fn ypow(m: usize) -> F192 {
    [F192::ONE, F192::Y, F192::Y * F192::Y][m]
}

fn log2c(n: usize) -> u32 {
    if n <= 1 { 0 } else { usize::BITS - (n - 1).leading_zeros() }
}

/// What a template row is in B.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowB {
    /// A constraint row (slot `crow`), writing a committed word or nothing.
    Con(u32),
    /// `loadE`: virtual.
    LoadE,
    /// `capTpl`'s `readd`: mini-bus (committed result word, no slot).
    CapRead,
}

pub struct Typed {
    pub x_log: usize,
    pub y_log: usize,
    /// Per block, `ℓ` (log iterations).
    pub ell: Vec<u8>,
    /// CSR by slot.
    pub row_ptr: Vec<u32>,
    pub ent: Vec<Ent>,
    /// CSC by word.
    pub col_ptr: Vec<u32>,
    pub cent: Vec<CEnt>,
    /// The compact CSC (`x`, `o | coefficient index << 2`) and the `A`/`B` rows (CSR, `y`, same code), with the
    /// coefficient table (index 0 = 1): 8-byte entries for the memory-bound passes.
    pub coefs: Vec<F192>,
    pub cc: Vec<(u32, u32)>,
    pub ab_ptr: Vec<u32>,
    pub ab: Vec<(u32, u32)>,
    /// The used prefixes of the slot and word cubes (the rest is zero).
    pub x_live: usize,
    pub y_live: usize,
    /// The word of every `K` cell (inputs: their virtual region).
    pub ky: Vec<u32>,
    /// The words of every `E` cell's limbs (`NONE` for a `loadE` cell).
    pub ey: Vec<[u32; 3]>,
    pub one_y: u32,
    /// Committed words (the padded result regions), dense result words, virtual words.
    pub committed: usize,
    pub dense: usize,
    pub virt: usize,
    /// Slot → (block, template row) tag (diagnostics), `NONE` on padding.
    pub slot_tag: Vec<u32>,
    pub tags: Vec<(usize, usize)>,
    pub rowb: Vec<Vec<RowB>>,
    pub report: String,
    /// The class-kernel evaluator of `Φ_Q` ([`PhiK`]), if built.
    pub phik: Option<PhiK>,
}

impl Typed {
    /// Layout and matrices of the program (static; the `run` only resolves the QLT `readd`s' public addresses).
    pub fn new(c: &Compiled, spec: &M3Spec, run: &Run, hdr_len: usize) -> Typed {
        let q = &c.q;
        let [nk, ne] = q.n_in;
        // public K input cells (QLT, header)
        let mut public = vec![false; nk];
        // (only the PUBX constants: a header lane changes per proof, so a readd it addresses is not static)
        for a in spec.arrs.iter().filter(|a| a.kind == ArrKind::Public) {
            for x in 0..1usize << a.tau {
                public[a.base + a.stride * x] = a.sel.get(x).is_none_or(|&i| i >= hdr_len);
            }
        }
        // public-derived K cells (in the interpreter's order): public inputs, and `lin`/`muladd` K results of
        // public-derived K operands. A `readd` whose argument is public-derived reads a static (public) address:
        // QLT's 9 reads per entry (α, β and the `lin`-computed α·g^i, β·g^i); `capTpl`'s are data-dependent.
        let mut pubd = vec![false; c.cells[0]];
        pubd[..nk].copy_from_slice(&public);
        for (b, blk) in q.blocks.iter().enumerate() {
            let lay = &c.lay[b];
            for jf in 0..lay.size {
                let j = unflat(&blk.dims, jf);
                for (t, r) in blk.tpl.iter().enumerate() {
                    if r.writes() == Some(Ty::K) {
                        let cell = lay.start[0] + lay.tw[0] * jf + lay.rank[t][0];
                        pubd[cell] = matches!(r.op, Op::MulAdd | Op::Lin(..)) && r.args.iter().all(|a| a.ty == Ty::K && pubd[a.at(&j)]);
                    }
                }
            }
        }
        // per block: row kinds, committed ranks per type, constraint rows
        let mut rowb: Vec<Vec<RowB>> = Vec::new();
        let mut wrank: Vec<Vec<u32>> = Vec::new();
        let mut nw: Vec<[usize; 2]> = Vec::new();
        let mut nc: Vec<usize> = Vec::new();
        let (mut n_cap, mut n_static, mut n_loade, mut n_assert) = (0usize, 0usize, 0usize, 0usize);
        for (b, blk) in q.blocks.iter().enumerate() {
            let size = c.lay[b].size;
            let (mut rk, mut cnt, mut ncon) = (Vec::new(), [0usize; 2], 0usize);
            let mut rb = Vec::new();
            for r in &blk.tpl {
                let kind = match r.op {
                    Op::LoadE => {
                        n_loade += size;
                        RowB::LoadE
                    }
                    Op::Readd(..) => {
                        let mut j = vec![0usize; blk.dims.len()];
                        let stat = (0..size).all(|jf| {
                            for (jk, v) in j.iter_mut().zip(unflat(&blk.dims, jf)) {
                                *jk = v;
                            }
                            let e = r.args[0].at(&j);
                            r.args[0].ty == Ty::K && pubd[e]
                        });
                        if stat {
                            n_static += size;
                            ncon += 1;
                            RowB::Con(ncon as u32 - 1)
                        } else {
                            n_cap += size;
                            RowB::CapRead
                        }
                    }
                    Op::FixMul => panic!("B1-P: fixmul rows are not in the node program"),
                    Op::Assert0 => {
                        n_assert += size;
                        ncon += 1;
                        RowB::Con(ncon as u32 - 1)
                    }
                    _ => {
                        ncon += 1;
                        RowB::Con(ncon as u32 - 1)
                    }
                };
                let w = match (r.writes(), kind) {
                    (Some(t), k) if k != RowB::LoadE => {
                        let i = if t == Ty::K { 0 } else { 1 };
                        cnt[i] += 1;
                        cnt[i] as u32 - 1
                    }
                    _ => NONE,
                };
                rk.push(w);
                rb.push(kind);
            }
            rowb.push(rb);
            wrank.push(rk);
            nw.push(cnt);
            nc.push(ncon);
        }
        // y regions: (size, key) key = (block, type, limb) or virtual
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        enum Reg {
            Res(usize, usize, usize),
            InK,
            InE(usize),
            One,
        }
        let mut regs: Vec<(usize, Reg)> = Vec::new();
        let mut dense = 0usize;
        for b in 0..q.blocks.len() {
            let l = c.lay[b].lsize;
            for t in 0..2 {
                if nw[b][t] > 0 {
                    let sz = 1usize << (log2c(nw[b][t]) + l);
                    for m in 0..[1, 3][t] {
                        regs.push((sz, Reg::Res(b, t, m)));
                    }
                    dense += nw[b][t] * c.lay[b].size * [1, 3][t];
                }
            }
        }
        let committed: usize = regs.iter().map(|r| r.0).sum();
        if nk > 0 {
            regs.push((nk.next_power_of_two(), Reg::InK));
        }
        for m in 0..3 {
            if ne > 0 {
                regs.push((ne.next_power_of_two(), Reg::InE(m)));
            }
        }
        regs.push((1, Reg::One));
        let virt = nk + 3 * ne + 1;
        regs.sort_by(|a, b| b.0.cmp(&a.0));
        let mut off = 0usize;
        let mut base: HashMap<Reg, usize> = HashMap::new();
        for &(sz, k) in &regs {
            base.insert(k, off);
            off += sz;
        }
        let y_log = log2c(off) as usize;
        // x regions
        let mut xr: Vec<(usize, usize)> = (0..q.blocks.len()).filter(|&b| nc[b] > 0).map(|b| (1usize << (log2c(nc[b]) + c.lay[b].lsize), b)).collect();
        xr.sort_by(|a, b| b.0.cmp(&a.0));
        let mut xbase = vec![usize::MAX; q.blocks.len()];
        let mut xo = 0usize;
        for &(sz, b) in &xr {
            xbase[b] = xo;
            xo += sz;
        }
        let x_log = log2c(xo) as usize;
        // cell → word maps
        let mut ky = vec![NONE; c.cells[0]];
        let mut ey = vec![[NONE; 3]; c.cells[1]];
        let mut le: HashMap<usize, (usize, usize, usize)> = HashMap::new();
        for e in 0..nk {
            ky[e] = (base[&Reg::InK] + e) as u32;
        }
        for e in 0..ne {
            ey[e] = std::array::from_fn(|m| (base[&Reg::InE(m)] + e) as u32);
        }
        for (b, blk) in q.blocks.iter().enumerate() {
            let lay = &c.lay[b];
            for (t, r) in blk.tpl.iter().enumerate() {
                let Some(ty) = r.writes() else { continue };
                let ti = if ty == Ty::K { 0 } else { 1 };
                for jf in 0..lay.size {
                    let cell = lay.start[ti] + lay.tw[ti] * jf + lay.rank[t][ti];
                    if rowb[b][t] == RowB::LoadE {
                        le.insert(cell, (b, t, jf));
                        continue;
                    }
                    let w = ((wrank[b][t] as usize) << lay.lsize) + jf;
                    if ti == 0 {
                        ky[cell] = (base[&Reg::Res(b, 0, 0)] + w) as u32;
                    } else {
                        ey[cell] = std::array::from_fn(|m| (base[&Reg::Res(b, 1, m)] + w) as u32);
                    }
                }
            }
        }
        let one_y = base[&Reg::One] as u32;
        // Readd tables (static resolution)
        let mut dl: HashMap<(usize, u32), HashMap<u64, usize>> = HashMap::new();
        // entries per block (blocks in x order), slot tags
        let mut tags: Vec<(usize, usize)> = Vec::new();
        let mut slot_tag = vec![NONE; 1 << x_log];
        let mut row_cnt = vec![0u32; 1 << x_log];
        let mut ents: Vec<(u32, Ent)> = Vec::new();
        let mut k_with_e = 0usize;
        let resolve = |ty: Ty, cell: usize, w: F192, o: u8, out: &mut Vec<(u32, Ent)>, x: u32| {
            fn go(c: &Compiled, ky: &[u32], ey: &[[u32; 3]], le: &HashMap<usize, (usize, usize, usize)>, ty: Ty, cell: usize, w: F192, o: u8, out: &mut Vec<(u32, Ent)>, x: u32) {
                match ty {
                    Ty::K => {
                        let y = ky[cell];
                        assert!(y != NONE, "a K operand's word");
                        out.push((x, Ent { y, o, c: w }));
                    }
                    Ty::E => {
                        if let Some(&(b, t, jf)) = le.get(&cell) {
                            let r = &c.q.blocks[b].tpl[t];
                            let j = unflat(&c.q.blocks[b].dims, jf);
                            for m in 0..3 {
                                go(c, ky, ey, le, r.args[m].ty, r.args[m].at(&j), w * ypow(m), o, out, x);
                            }
                        } else {
                            let ys = ey[cell];
                            assert!(ys[0] != NONE, "an E operand's words");
                            for m in 0..3 {
                                out.push((x, Ent { y: ys[m], o, c: w * ypow(m) }));
                            }
                        }
                    }
                }
            }
            assert!(cell < c.cells[if ty == Ty::K { 0 } else { 1 }], "an operand inside its memory");
            go(c, &ky, &ey, &le, ty, cell, w, o, out, x)
        };
        for (b, blk) in q.blocks.iter().enumerate() {
            if xbase[b] == usize::MAX {
                continue;
            }
            let lay = &c.lay[b];
            let mut j = vec![0usize; blk.dims.len()];
            for (t, r) in blk.tpl.iter().enumerate() {
                let RowB::Con(crow) = rowb[b][t] else { continue };
                tags.push((b, t));
                let tag = tags.len() as u32 - 1;
                if r.ty == Ty::K && r.args.iter().any(|a| a.ty == Ty::E) && r.writes().is_some() {
                    k_with_e += lay.size;
                }
                for jf in 0..lay.size {
                    for (jk, v) in j.iter_mut().zip(unflat(&blk.dims, jf)) {
                        *jk = v;
                    }
                    let x = (xbase[b] + ((crow as usize) << lay.lsize) + jf) as u32;
                    slot_tag[x as usize] = tag;
                    let n0 = ents.len();
                    let one = F192::ONE;
                    match r.op {
                        Op::MulAdd => {
                            resolve(r.args[0].ty, r.args[0].at(&j), one, MA, &mut ents, x);
                            resolve(r.args[1].ty, r.args[1].at(&j), one, MB, &mut ents, x);
                            resolve(r.args[2].ty, r.args[2].at(&j), one, MD, &mut ents, x);
                        }
                        Op::Lin(k, k2) => {
                            resolve(r.args[0].ty, r.args[0].at(&j), one, MD, &mut ents, x);
                            if k != F64::ZERO {
                                resolve(r.args[1].ty, r.args[1].at(&j), F192::from(k), MD, &mut ents, x);
                            }
                            if k2 != F64::ZERO {
                                ents.push((x, Ent { y: one_y, o: MD, c: F192::from(k2) }));
                            }
                        }
                        Op::Assert0 => {
                            resolve(r.args[0].ty, r.args[0].at(&j), one, MA, &mut ents, x);
                            resolve(r.args[1].ty, r.args[1].at(&j), one, MB, &mut ents, x);
                        }
                        Op::Readd(lo, m) => {
                            let alpha = run.kc[r.args[0].at(&j)].0;
                            let tab = dl.entry((lo, m)).or_insert_with(|| (0..1usize << m).rev().map(|i| (c.g(lo + i).0, lo + i)).collect());
                            let e = *tab.get(&alpha).expect("a QLT readd's static cell");
                            resolve(r.ty, e, one, MD, &mut ents, x);
                        }
                        _ => unreachable!(),
                    }
                    if let Some(ty) = r.writes() {
                        let ti = if ty == Ty::K { 0 } else { 1 };
                        let cell = lay.start[ti] + lay.tw[ti] * jf + lay.rank[t][ti];
                        resolve(ty, cell, one, MW, &mut ents, x);
                    }
                    row_cnt[x as usize] = (ents.len() - n0) as u32;
                }
            }
        }
        // CSR (stable by slot)
        let mut row_ptr = vec![0u32; (1 << x_log) + 1];
        for x in 0..1usize << x_log {
            row_ptr[x + 1] = row_ptr[x] + row_cnt[x];
        }
        let mut ent = vec![Ent { y: 0, o: 0, c: F192::ZERO }; ents.len()];
        {
            let mut fill = row_ptr.clone();
            for &(x, e) in &ents {
                ent[fill[x as usize] as usize] = e;
                fill[x as usize] += 1;
            }
        }
        drop(ents);
        // CSC
        let ny = 1usize << y_log;
        let mut col_ptr = vec![0u32; ny + 1];
        for e in &ent {
            col_ptr[e.y as usize + 1] += 1;
        }
        for y in 0..ny {
            col_ptr[y + 1] += col_ptr[y];
        }
        let mut cent = vec![CEnt { x: 0, o: 0, c: F192::ZERO }; ent.len()];
        {
            let mut fill = col_ptr.clone();
            for x in 0..1usize << x_log {
                for e in &ent[row_ptr[x] as usize..row_ptr[x + 1] as usize] {
                    cent[fill[e.y as usize] as usize] = CEnt { x: x as u32, o: e.o, c: e.c };
                    fill[e.y as usize] += 1;
                }
            }
        }
        let slots: usize = row_cnt.iter().filter(|&&n| n > 0).count();
        let by_o: Vec<usize> = (0..4).map(|o| ent.iter().filter(|e| e.o == o).count()).collect();
        let nontriv = ent.iter().filter(|e| e.c != F192::ONE && e.c != F192::Y && e.c != F192::Y * F192::Y).count();
        let report = format!(
            "b1 layout: x_log {x_log} (slots used {slots}, padded {xo}), y_log {y_log} (committed padded {committed}, dense {dense}, virtual {virt}, total {off}); \
             nnz {} (A {} B {} D {} W {}; coef not 1/Y/Y² {nontriv}); rows: loadE {n_loade} (virtual), cap readd {n_cap} (mini-bus), static readd {n_static}, assert0 {n_assert}; \
             K rows with E operands {k_with_e}",
            ent.len(), by_o[0], by_o[1], by_o[2], by_o[3]
        );
        let mut b1 = Typed {
            x_log,
            y_log,
            ell: c.lay.iter().map(|l| l.lsize as u8).collect(),
            row_ptr,
            ent,
            col_ptr,
            cent,
            coefs: Vec::new(),
            cc: Vec::new(),
            ab_ptr: Vec::new(),
            ab: Vec::new(),
            x_live: xo,
            y_live: off,
            ky,
            ey,
            one_y,
            committed,
            dense,
            virt,
            slot_tag,
            tags,
            rowb,
            report,
            phik: None,
        };
        b1.compact();
        b1
    }

    /// B1-IE: the matrices from their entries `(x, Ent)` (B1-K's layout, `lvm::typed_lay::entries`), with the
    /// slot and word cubes of `2^x_log`, `2^y_log`, their used prefixes, the word `1`, and the (pseudo-block, row)
    /// tags of the slots with `ℓ` per pseudo-block (what the class kernels group by).
    #[allow(clippy::too_many_arguments)]
    pub fn from_ents(
        x_log: usize,
        y_log: usize,
        ents: Vec<(u32, Ent)>,
        x_live: usize,
        y_live: usize,
        one_y: u32,
        ell: Vec<u8>,
        slot_tag: Vec<u32>,
        tags: Vec<(usize, usize)>,
    ) -> Typed {
        let nx = 1usize << x_log;
        let mut row_ptr = vec![0u32; nx + 1];
        for &(x, _) in &ents {
            row_ptr[x as usize + 1] += 1;
        }
        for x in 0..nx {
            row_ptr[x + 1] += row_ptr[x];
        }
        let mut ent = vec![Ent { y: 0, o: 0, c: F192::ZERO }; ents.len()];
        {
            let mut fill = row_ptr.clone();
            for &(x, e) in &ents {
                ent[fill[x as usize] as usize] = e;
                fill[x as usize] += 1;
            }
        }
        drop(ents);
        let ny = 1usize << y_log;
        let mut col_ptr = vec![0u32; ny + 1];
        for e in &ent {
            col_ptr[e.y as usize + 1] += 1;
        }
        for y in 0..ny {
            col_ptr[y + 1] += col_ptr[y];
        }
        let mut cent = vec![CEnt { x: 0, o: 0, c: F192::ZERO }; ent.len()];
        {
            let mut fill = col_ptr.clone();
            for x in 0..nx {
                for e in &ent[row_ptr[x] as usize..row_ptr[x + 1] as usize] {
                    cent[fill[e.y as usize] as usize] = CEnt { x: x as u32, o: e.o, c: e.c };
                    fill[e.y as usize] += 1;
                }
            }
        }
        let by_o: Vec<usize> = (0..4).map(|o| ent.iter().filter(|e| e.o == o).count()).collect();
        let report = format!("b1 layout (B1-K): x_log {x_log} (live {x_live}), y_log {y_log} (live {y_live}); nnz {} (A {} B {} D {} W {})", ent.len(), by_o[0], by_o[1], by_o[2], by_o[3]);
        let mut b1 = Typed {
            x_log,
            y_log,
            ell,
            row_ptr,
            ent,
            col_ptr,
            cent,
            coefs: Vec::new(),
            cc: Vec::new(),
            ab_ptr: Vec::new(),
            ab: Vec::new(),
            x_live,
            y_live,
            ky: Vec::new(),
            ey: Vec::new(),
            one_y,
            committed: 0,
            dense: 0,
            virt: 0,
            slot_tag,
            tags,
            rowb: Vec::new(),
            report,
            phik: None,
        };
        b1.compact();
        b1
    }

    /// A copy whose entry `i` names word `y2` (a tampered matrix; the CSC rebuilt).
    pub fn clone_with_entry(&self, i: usize, y2: u32) -> Typed {
        let mut ent = self.ent.clone();
        ent[i].y = y2;
        let ny = 1usize << self.y_log;
        let mut col_ptr = vec![0u32; ny + 1];
        for e in &ent {
            col_ptr[e.y as usize + 1] += 1;
        }
        for y in 0..ny {
            col_ptr[y + 1] += col_ptr[y];
        }
        let mut cent = vec![CEnt { x: 0, o: 0, c: F192::ZERO }; ent.len()];
        let mut fill = col_ptr.clone();
        for x in 0..1usize << self.x_log {
            for e in &ent[self.row_ptr[x] as usize..self.row_ptr[x + 1] as usize] {
                cent[fill[e.y as usize] as usize] = CEnt { x: x as u32, o: e.o, c: e.c };
                fill[e.y as usize] += 1;
            }
        }
        Typed {
            x_log: self.x_log,
            y_log: self.y_log,
            ell: self.ell.clone(),
            row_ptr: self.row_ptr.clone(),
            ent,
            col_ptr,
            cent,
            coefs: Vec::new(),
            cc: Vec::new(),
            ab_ptr: Vec::new(),
            ab: Vec::new(),
            x_live: self.x_live,
            y_live: self.y_live,
            ky: Vec::new(),
            ey: Vec::new(),
            one_y: self.one_y,
            committed: self.committed,
            dense: self.dense,
            virt: self.virt,
            slot_tag: self.slot_tag.clone(),
            tags: self.tags.clone(),
            rowb: Vec::new(),
            report: String::new(),
            phik: None,
        }
        .compacted()
    }

    fn compacted(mut self) -> Typed {
        self.compact();
        self
    }

    /// Build the compact CSC and the `A`/`B` CSR from `ent`/`cent`.
    fn compact(&mut self) {
        let mut idx: HashMap<[u64; 3], u32> = HashMap::new();
        let mut coefs = vec![F192::ONE];
        idx.insert(F192::ONE.to_limbs(), 0);
        let mut code = |o: u8, c: F192| -> u32 {
            let k = *idx.entry(c.to_limbs()).or_insert_with(|| {
                coefs.push(c);
                coefs.len() as u32 - 1
            });
            (k << 2) | o as u32
        };
        self.cc = self.cent.iter().map(|e| (e.x, code(e.o, e.c))).collect();
        let nx = 1usize << self.x_log;
        let mut ab_ptr = vec![0u32; nx + 1];
        let mut ab = Vec::new();
        for x in 0..nx {
            for e in &self.ent[self.row_ptr[x] as usize..self.row_ptr[x + 1] as usize] {
                if e.o == MA || e.o == MB {
                    ab.push((e.y, code(e.o, e.c)));
                }
            }
            ab_ptr[x + 1] = ab.len() as u32;
        }
        self.coefs = coefs;
        self.ab_ptr = ab_ptr;
        self.ab = ab;
        self.cent = Vec::new();
    }

    /// `(Az, Bz)` per slot, from the compact `A`/`B` rows (the used prefix; zero beyond).
    pub fn ab_vals(&self, z: &[F64]) -> [Vec<F192>; 2] {
        let n = 1usize << self.x_log;
        let mut out: [Vec<F192>; 2] = std::array::from_fn(|_| scratch(n));
        let live = self.x_live;
        for v in out.iter_mut() {
            v[live..(live + 4).min(n)].fill(F192::ZERO);
        }
        let (pa, pb) = (Out(out[0].as_mut_ptr()), Out(out[1].as_mut_ptr()));
        crate::lv::parallel::for_each(live.div_ceil(CH), |ci| {
            for x in ci * CH..((ci + 1) * CH).min(live) {
                let mut acc = [F192Unreduced::ZERO; 2];
                for &(y, oc) in &self.ab[self.ab_ptr[x] as usize..self.ab_ptr[x + 1] as usize] {
                    let k = (oc >> 2) as usize;
                    let v = z[y as usize];
                    if k == 0 {
                        acc[(oc & 3) as usize] ^= F192Unreduced::from(F192::from(v));
                    } else {
                        acc[(oc & 3) as usize] ^= self.coefs[k].mul_base_unreduced(v);
                    }
                }
                // SAFETY: slot x belongs to this task only.
                unsafe {
                    *pa.p().add(x) = acc[0].reduce();
                    *pb.p().add(x) = acc[1].reduce();
                }
            }
        });
        out
    }

    /// The results-only witness `z` (committed regions) with the virtual regions filled (the prover holds them).
    pub fn witness(&self, run: &Run) -> Vec<F64> {
        // every cell has its own word (the layout is injective on cells), so the cell chunks write disjoint words
        let mut z = vec![F64::ZERO; 1 << self.y_log];
        let pz = crate::lv::parallel::SendPtr(z.as_mut_ptr());
        const C: usize = 1 << 14;
        let (nk, ne) = (self.ky.len(), self.ey.len());
        crate::lv::parallel::for_each(nk.div_ceil(C) + ne.div_ceil(C), |ci| {
            let pz = pz;
            if ci < nk.div_ceil(C) {
                for e in ci * C..((ci + 1) * C).min(nk) {
                    let y = self.ky[e];
                    if y != NONE {
                        // SAFETY: word y is this cell's alone (above); y < 2^y_log
                        unsafe { *pz.0.add(y as usize) = run.kc[e] };
                    }
                }
            } else {
                let ci = ci - nk.div_ceil(C);
                for e in ci * C..((ci + 1) * C).min(ne) {
                    let ys = self.ey[e];
                    if ys[0] != NONE {
                        let l = run.ec[e].to_limbs();
                        for m in 0..3 {
                            // SAFETY: as above
                            unsafe { *pz.0.add(ys[m] as usize) = F64(l[m]) };
                        }
                    }
                }
            }
        });
        z[self.one_y as usize] = F64::ONE;
        z
    }

    /// `(Az, Bz, (D+W)z)` per slot.
    pub fn abc(&self, z: &[F64]) -> [Vec<F192>; 3] {
        let n = 1usize << self.x_log;
        let mut out: [Vec<F192>; 3] = std::array::from_fn(|_| vec![F192::ZERO; n]);
        let [a, b, c] = &mut out;
        let (pa, pb, pc) = (crate::lv::parallel::SendPtr(a.as_mut_ptr()), crate::lv::parallel::SendPtr(b.as_mut_ptr()), crate::lv::parallel::SendPtr(c.as_mut_ptr()));
        let chunk = 1usize << 12;
        crate::lv::parallel::for_each(n.div_ceil(chunk), |ci| {
            for x in ci * chunk..((ci + 1) * chunk).min(n) {
                let mut acc = [F192Unreduced::ZERO; 3];
                for e in &self.ent[self.row_ptr[x] as usize..self.row_ptr[x + 1] as usize] {
                    let k = if e.o >= MD { 2 } else { e.o as usize };
                    acc[k] ^= e.c.mul_base_unreduced(z[e.y as usize]);
                }
                // SAFETY: slot x belongs to this task only.
                unsafe {
                    *pa.add(x) = acc[0].reduce();
                    *pb.add(x) = acc[1].reduce();
                    *pc.add(x) = acc[2].reduce();
                }
            }
        });
        out
    }

    /// Slots where the relation fails, by (block, template row): `(tag, count, first slot)`.
    pub fn check(&self, abc: &[Vec<F192>; 3]) -> Vec<(u32, usize, usize)> {
        let mut bad: HashMap<u32, (usize, usize)> = HashMap::new();
        for x in 0..1usize << self.x_log {
            if !(abc[0][x] * abc[1][x] + abc[2][x]).is_zero() {
                let e = bad.entry(self.slot_tag[x]).or_insert((0, x));
                e.0 += 1;
            }
        }
        let mut v: Vec<_> = bad.into_iter().map(|(t, (n, x))| (t, n, x)).collect();
        v.sort();
        v
    }
}

// ---------------------------------------------------------------- sumchecks

/// B1-IE: where the backend's sumchecks get their challenges: a seeded RNG (B1-P's dev toy) or the Fiat–Shamir
/// transcript (the shipped path: the round polynomials sent as V_S reads them, `LvmDecideSumcheck.sumcheck`).
pub trait Chal {
    /// An equality-mode round (`sumcheckRoundPoly count claim (some τ_i)`): `q` constant first, without the `eq`
    /// factor; `q₁ … q_d` are sent (the claim fixes `q₀`).
    fn eq_round(&mut self, q: &[F192]) -> F192;
    /// A plain round: `g` constant first; every coefficient but `g₁` is sent.
    fn round(&mut self, g: &[F192]) -> F192;
}

impl Chal for Rng {
    fn eq_round(&mut self, _q: &[F192]) -> F192 {
        self.e()
    }
    fn round(&mut self, _g: &[F192]) -> F192 {
        self.e()
    }
}

impl Chal for crate::lv::fiat_shamir::transcript::ProverState {
    fn eq_round(&mut self, q: &[F192]) -> F192 {
        self.add_round_poly(q, true);
        self.sample()
    }
    fn round(&mut self, g: &[F192]) -> F192 {
        self.add_round_poly(g, false);
        self.sample()
    }
}

pub struct Rng(u64);
impl Rng {
    pub fn new(s: u64) -> Self {
        Rng(s ^ 0x9E37_79B9_7F4A_7C15)
    }
    pub fn u(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn e(&mut self) -> F192 {
        F192::new(self.u(), self.u(), self.u())
    }
}

const SER: usize = 1 << 12;

/// Σ over pairs `j < n` of `f(j)` (three unreduced sums), on the pool when large.
fn sum3(n: usize, f: impl Fn(usize, &mut [F192Unreduced; 3]) + Sync) -> [F192; 3] {
    if n < SER {
        let mut acc = [F192Unreduced::ZERO; 3];
        for j in 0..n {
            f(j, &mut acc);
        }
        return acc.map(|a| a.reduce());
    }
    let chunk = 1usize << 10;
    let acc = crate::lv::parallel::map_reduce(
        n.div_ceil(chunk),
        || [F192Unreduced::ZERO; 3],
        |ci| {
            let mut acc = [F192Unreduced::ZERO; 3];
            for j in ci * chunk..((ci + 1) * chunk).min(n) {
                f(j, &mut acc);
            }
            acc
        },
        |a, b| [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2]],
    );
    acc.map(|a| a.reduce())
}

/// `v'[j] = v[2j] + r·(v[2j] + v[2j+1])`.
fn fold(v: &[F192], r: F192) -> Vec<F192> {
    let n = v.len() / 2;
    if n < SER {
        return (0..n).map(|j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1])).collect();
    }
    crate::lv::parallel::map_collect(n.div_ceil(1 << 10), |ci| (ci << 10..((ci + 1) << 10).min(n)).map(|j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1])).collect::<Vec<_>>())
        .concat()
}

fn fold_k(v: &[F64], r: F192) -> Vec<F192> {
    let n = v.len() / 2;
    crate::lv::parallel::map_collect(n.div_ceil(1 << 10), |ci| {
        (ci << 10..((ci + 1) << 10).min(n)).map(|j| F192::from(v[2 * j]) + r.mul_base(v[2 * j] + v[2 * j + 1])).collect::<Vec<_>>()
    })
    .concat()
}

pub struct Zc {
    /// Per round, `g`'s coefficients (degree 3, constant first).
    pub rounds: Vec<[F192; 4]>,
    pub r: Vec<F192>,
    pub a: F192,
    pub b: F192,
    pub c: F192,
}

/// Raw output pointer for the fused passes (each task writes its own range).
#[derive(Clone, Copy)]
struct Out(*mut F192);
unsafe impl Send for Out {}
unsafe impl Sync for Out {}
impl Out {
    #[inline(always)]
    fn p(self) -> *mut F192 {
        self.0
    }
}

const CH: usize = 1 << 10;

/// A buffer the caller overwrites before reading (no memset: these passes are memory-bound). Every read is of a
/// slot written in this proof: the fused passes read only the live prefix, whose tail is zero-filled.
#[allow(clippy::uninit_vec)]
fn scratch(n: usize) -> Vec<F192> {
    let mut v = Vec::with_capacity(n);
    // SAFETY: F192 is three u64 (every bit pattern valid); see above for the reads.
    unsafe { v.set_len(n) };
    v
}

/// The zerocheck prover: `Σ_x eq(τ, x)·(a·b + c)(x) = 0`, variable 0 first. `g_i(X) = P·(1 + τ_i + X)·q_i(X)`,
/// `q_i` from three sums per pair (`q(0)`, `q(1)`, `q(∞)`) against `eq(τ_{>i}, ·)`. Each round after the first is
/// one fused pass: fold the quads of round `i` with `r_i`, shrink the `eq` table, and sum round `i + 1`.
pub fn zerocheck<C: Chal + ?Sized>(abc: [Vec<F192>; 3], tau: &[F192], rng: &mut C) -> Zc {
    let [mut a, mut b, mut c] = abc;
    let n = tau.len();
    assert_eq!(a.len(), 1 << n);
    let mut e = eq_table(&tau[1..]);
    let (mut a2, mut b2, mut c2, mut e2) = (vec![F192::ZERO; a.len() / 2], vec![F192::ZERO; a.len() / 2], vec![F192::ZERO; a.len() / 2], vec![F192::ZERO; e.len() / 2]);
    let mut p = F192::ONE;
    let (mut rounds, mut r) = (Vec::with_capacity(n), Vec::with_capacity(n));
    // q(1) is not summed: g(0) + g(1) = claim gives it (`LVM_B1_Q1=1` sums it, the toy's tamper diagnostics)
    let direct = std::env::var_os("LVM_B1_Q1").is_some();
    let pair = |a0: F192, a1: F192, b0: F192, b1: F192, c0: F192, c1: F192, ew: F192, acc: &mut [F192Unreduced; 3]| {
        acc[0] ^= ew.mul_unreduced(a0 * b0 + c0);
        if direct {
            acc[1] ^= ew.mul_unreduced(a1 * b1 + c1);
        }
        acc[2] ^= ew.mul_unreduced((a0 + a1) * (b0 + b1));
    };
    let (aa, bb, cc, ee) = (&a, &b, &c, &e);
    let mut sums = sum3(a.len() / 2, |j, acc| pair(aa[2 * j], aa[2 * j + 1], bb[2 * j], bb[2 * j + 1], cc[2 * j], cc[2 * j + 1], ee[j], acc));
    let mut len = a.len();
    let mut claim = F192::ZERO;
    for i in 0..n {
        let t1 = F192::ONE + tau[i];
        let [q0, q1, qi] = sums;
        // g(0) + g(1) = P·((1 + τ_i)·q0 + τ_i·q1) = claim
        let q1 = if direct { q1 } else { (claim + p * t1 * q0) * (p * tau[i]).inv() };
        let l = q0 + q1 + qi;
        let g = [p * t1 * q0, p * (t1 * l + q0), p * (t1 * qi + l), p * qi];
        rounds.push(g);
        let ri = rng.eq_round(&[q0, l, qi]);
        r.push(ri);
        claim = poly_eval(&g, ri);
        p *= F192::ONE + tau[i] + ri;
        if len == 2 {
            let f = |v: &[F192]| v[0] + ri * (v[0] + v[1]);
            return Zc { rounds, r, a: f(&a), b: f(&b), c: f(&c) };
        }
        // fused: fold quads into the next buffers, shrink eq, sum the next round
        let quads = len / 4;
        let (oa, ob, oc, oe) = (Out(a2.as_mut_ptr()), Out(b2.as_mut_ptr()), Out(c2.as_mut_ptr()), Out(e2.as_mut_ptr()));
        let (aa, bb, cc, ee) = (&a, &b, &c, &e);
        let body = |j: usize, acc: &mut [F192Unreduced; 3]| {
            let f = |v: &[F192], k: usize| v[k] + ri * (v[k] + v[k + 1]);
            let (na0, na1, nb0, nb1, nc0, nc1) = (f(aa, 4 * j), f(aa, 4 * j + 2), f(bb, 4 * j), f(bb, 4 * j + 2), f(cc, 4 * j), f(cc, 4 * j + 2));
            let ne = ee[2 * j] + ee[2 * j + 1];
            // SAFETY: quad j writes slots 2j, 2j+1 (and j of eq) of the next buffers only.
            unsafe {
                *oa.p().add(2 * j) = na0;
                *oa.p().add(2 * j + 1) = na1;
                *ob.p().add(2 * j) = nb0;
                *ob.p().add(2 * j + 1) = nb1;
                *oc.p().add(2 * j) = nc0;
                *oc.p().add(2 * j + 1) = nc1;
                if j < ee.len() / 2 {
                    *oe.p().add(j) = ne;
                }
            }
            pair(na0, na1, nb0, nb1, nc0, nc1, if ee.len() >= 2 { ne } else { F192::ONE }, acc);
        };
        sums = sum3(quads, body);
        std::mem::swap(&mut a, &mut a2);
        std::mem::swap(&mut b, &mut b2);
        std::mem::swap(&mut c, &mut c2);
        len /= 2;
        a.truncate(len);
        b.truncate(len);
        c.truncate(len);
        if e.len() >= 2 {
            std::mem::swap(&mut e, &mut e2);
            e.truncate(len / 2);
        }
    }
    unreachable!()
}

/// The honest prover's zerocheck: `c = a·b` on the cube, so round 0 has `q(0) = q(1) = 0` and sums `q(∞)` only;
/// `c` is folded from the products in round 0's fused pass. Only the used prefix `live` of the cube is read (the
/// rest of `a`, `b` is zero).
pub fn zerocheck_fast<C: Chal + ?Sized>(ab: [Vec<F192>; 2], tau: &[F192], live: usize, rng: &mut C) -> Zc {
    let [mut a, mut b] = ab;
    let n = tau.len();
    let full = a.len();
    assert_eq!(full, 1 << n);
    let livel = |i: usize| -> usize { (full >> i).min((((live + (1 << i) - 1) >> i) + 3) & !3) };
    let mut e = eq_table(&tau[1..]);
    let (mut a2, mut b2, mut c, mut c2, mut e2) = (scratch(full / 2), scratch(full / 2), scratch(full / 2), scratch(full / 4), scratch(e.len() / 2));
    let (mut rounds, mut r) = (Vec::with_capacity(n), Vec::with_capacity(n));
    let mut p = F192::ONE;
    let mut claim = F192::ZERO;
    let mut len = full;
    // round 0: q(∞) only
    let (aa, bb, ee) = (&a, &b, &e);
    let [_, _, qi0] = sum3(livel(0) / 2, |j, acc| acc[2] ^= ee[j].mul_unreduced((aa[2 * j] + aa[2 * j + 1]) * (bb[2 * j] + bb[2 * j + 1])));
    let mut sums = [F192::ZERO, F192::ZERO, qi0];
    for i in 0..n {
        let t1 = F192::ONE + tau[i];
        let [q0, _, qi] = sums;
        let q1 = (claim + p * t1 * q0) * (p * tau[i]).inv();
        let l = q0 + q1 + qi;
        let g = [p * t1 * q0, p * (t1 * l + q0), p * (t1 * qi + l), p * qi];
        rounds.push(g);
        let ri = rng.eq_round(&[q0, l, qi]);
        r.push(ri);
        claim = poly_eval(&g, ri);
        p *= F192::ONE + tau[i] + ri;
        if len == 2 {
            let f = |v: &[F192]| v[0] + ri * (v[0] + v[1]);
            let cv = if i == 0 { let (c0, c1) = (a[0] * b[0], a[1] * b[1]); c0 + ri * (c0 + c1) } else { f(&c) };
            return Zc { rounds, r, a: f(&a), b: f(&b), c: cv };
        }
        let li = livel(i);
        let (oa, ob, oc, oe) = (Out(a2.as_mut_ptr()), Out(b2.as_mut_ptr()), Out(if i == 0 { c.as_mut_ptr() } else { c2.as_mut_ptr() }), Out(e2.as_mut_ptr()));
        let (aa, bb, cc, ee) = (&a, &b, &c, &e);
        let first = i == 0;
        // the eq table is shrunk two entries past the live quads: the next round's boundary pair reads them
        let nq = li / 4;
        let ne_n = ee.len() / 2;
        sums = sum3(nq.max(ne_n), |j, acc| {
            if j >= nq {
                // SAFETY: as below (eq only).
                unsafe { *oe.p().add(j) = ee[2 * j] + ee[2 * j + 1] };
                return;
            }
            let f = |v: &[F192], k: usize| v[k] + ri * (v[k] + v[k + 1]);
            let (na0, na1, nb0, nb1) = (f(aa, 4 * j), f(aa, 4 * j + 2), f(bb, 4 * j), f(bb, 4 * j + 2));
            let (nc0, nc1) = if first {
                let cp = |k: usize| {
                    let (c0, c1) = (aa[k] * bb[k], aa[k + 1] * bb[k + 1]);
                    c0 + ri * (c0 + c1)
                };
                (cp(4 * j), cp(4 * j + 2))
            } else {
                (f(cc, 4 * j), f(cc, 4 * j + 2))
            };
            let ne = if ee.len() >= 2 { ee[2 * j] + ee[2 * j + 1] } else { F192::ONE };
            // SAFETY: quad j writes slots 2j, 2j+1 (and j of eq) of the next buffers only.
            unsafe {
                *oa.p().add(2 * j) = na0;
                *oa.p().add(2 * j + 1) = na1;
                *ob.p().add(2 * j) = nb0;
                *ob.p().add(2 * j + 1) = nb1;
                *oc.p().add(2 * j) = nc0;
                *oc.p().add(2 * j + 1) = nc1;
                if j < ne_n {
                    *oe.p().add(j) = ne;
                }
            }
            acc[0] ^= ne.mul_unreduced(na0 * nb0 + nc0);
            acc[2] ^= ne.mul_unreduced((na0 + na1) * (nb0 + nb1));
        });
        std::mem::swap(&mut a, &mut a2);
        std::mem::swap(&mut b, &mut b2);
        if !first {
            std::mem::swap(&mut c, &mut c2);
        }
        len /= 2;
        a.truncate(len);
        b.truncate(len);
        c.truncate(len);
        for k in li / 2..livel(i + 1) {
            a[k] = F192::ZERO;
            b[k] = F192::ZERO;
            c[k] = F192::ZERO;
        }
        if first {
            c2.truncate(len / 2);
        }
        if e.len() >= 2 {
            std::mem::swap(&mut e, &mut e2);
            e.truncate(len / 2);
        }
    }
    unreachable!()
}

/// Split `eq` tables: `eq(r, x) = hi[x >> 10]·lo[x & 1023]` (cache-resident, no gather from a 2^n table).
fn eq_split(r: &[F192]) -> (Vec<F192>, Vec<F192>) {
    let l = r.len().min(10);
    (eq_table(&r[..l]), eq_table(&r[l..]))
}

/// `u(y) = Σ_x eq(r_x, x)·(M_A + γM_B + γ²M_{D+W})(x, y)` from the CSC, with split `eq(r_x)`.
pub fn wiring_u(b1: &Typed, rx: &[F192], gamma: F192) -> Vec<F192> {
    let (xl, xh) = eq_split(rx);
    let g2 = gamma * gamma;
    let ny = 1usize << b1.y_log;
    let mut u = scratch(ny);
    let live = b1.y_live.min(ny);
    u[live..(live + 4).min(ny)].fill(F192::ZERO);
    let ou = Out(u.as_mut_ptr());
    crate::lv::parallel::for_each(live.div_ceil(CH), |ci| {
        for y in ci * CH..((ci + 1) * CH).min(live) {
            let (s, t) = (b1.col_ptr[y] as usize, b1.col_ptr[y + 1] as usize);
            if s == t {
                // SAFETY: word y belongs to this task only.
                unsafe { *ou.p().add(y) = F192::ZERO };
                continue;
            }
            let mut acc = [F192Unreduced::ZERO; 3];
            for &(x, oc) in &b1.cc[s..t] {
                let o = (oc & 3) as u8;
                let k = if o >= MD { 2 } else { o as usize };
                let (l, h) = (xl[x as usize & 1023], xh[x as usize >> 10]);
                if oc >> 2 == 0 {
                    acc[k] ^= l.mul_unreduced(h);
                } else {
                    acc[k] ^= (l * h).mul_unreduced(b1.coefs[(oc >> 2) as usize]);
                }
            }
            // SAFETY: word y belongs to this task only.
            unsafe { *ou.p().add(y) = acc[0].reduce() + gamma * acc[1].reduce() + g2 * acc[2].reduce() };
        }
    });
    u
}

pub struct Wr {
    pub rounds: Vec<[F192; 3]>,
    pub r: Vec<F192>,
    pub u: F192,
    pub z: F192,
}

/// The wiring sumcheck prover: `Σ_y u(y)·z(y)`, variable 0 first, degree 2; rounds after the first fused
/// (fold the quads, sum the next round).
pub fn wiring<C: Chal + ?Sized>(u: Vec<F192>, z: &[F64], claim0: F192, live: usize, rng: &mut C) -> Wr {
    let n = u.len().trailing_zeros() as usize;
    let full = u.len();
    // the used prefix at round i, a multiple of 4 (zero beyond; a gap of ≤ 2 is zero-filled after each pass)
    let livel = |i: usize| -> usize { (full >> i).min((((live + (1 << i) - 1) >> i) + 3) & !3) };
    let direct = std::env::var_os("LVM_B1_Q1").is_some();
    let mut claim = claim0;
    let (mut rounds, mut r) = (Vec::with_capacity(n), Vec::with_capacity(n));
    let (uu, zz) = (&u, z);
    let [p0, p1, pi] = sum3(livel(0) / 2, |j, acc| {
        let (u0, u1, z0, z1) = (uu[2 * j], uu[2 * j + 1], zz[2 * j], zz[2 * j + 1]);
        acc[0] ^= u0.mul_base_unreduced(z0);
        if direct {
            acc[1] ^= u1.mul_base_unreduced(z1);
        }
        acc[2] ^= (u0 + u1).mul_base_unreduced(z0 + z1);
    });
    let p1 = if direct { p1 } else { claim + p0 };
    let g = [p0, p0 + p1 + pi, pi];
    rounds.push(g);
    let r0 = rng.round(&g);
    r.push(r0);
    claim = poly_eval(&g, r0);
    // round 0's fold (z from K) fused with round 1's sums
    let half = u.len() / 2;
    let (mut un, mut zn) = (scratch(half), scratch(half));
    let (ou, oz) = (Out(un.as_mut_ptr()), Out(zn.as_mut_ptr()));
    let mut sums = sum3(livel(0) / 4, |j, acc| {
        let fu = |k: usize| uu[k] + r0 * (uu[k] + uu[k + 1]);
        let fz = |k: usize| F192::from(zz[k]) + r0.mul_base(zz[k] + zz[k + 1]);
        let (u0, u1, z0, z1) = (fu(4 * j), fu(4 * j + 2), fz(4 * j), fz(4 * j + 2));
        // SAFETY: quad j writes 2j, 2j+1 only.
        unsafe {
            *ou.p().add(2 * j) = u0;
            *ou.p().add(2 * j + 1) = u1;
            *oz.p().add(2 * j) = z0;
            *oz.p().add(2 * j + 1) = z1;
        }
        acc[0] ^= u0.mul_unreduced(z0);
        if direct {
            acc[1] ^= u1.mul_unreduced(z1);
        }
        acc[2] ^= (u0 + u1).mul_unreduced(z0 + z1);
    });
    drop(u);
    let (mut u, mut ze) = (un, zn);
    for k in livel(0) / 2..livel(1) {
        u[k] = F192::ZERO;
        ze[k] = F192::ZERO;
    }
    let (mut u2, mut z2) = (scratch(half / 2), scratch(half / 2));
    let mut len = half;
    for i in 1..n {
        let [p0, p1, pi] = sums;
        let p1 = if direct { p1 } else { claim + p0 };
        let g = [p0, p0 + p1 + pi, pi];
        rounds.push(g);
        let ri = rng.round(&g);
        r.push(ri);
        claim = poly_eval(&g, ri);
        if len == 2 {
            return Wr { rounds, r, u: u[0] + ri * (u[0] + u[1]), z: ze[0] + ri * (ze[0] + ze[1]) };
        }
        let (ou, oz) = (Out(u2.as_mut_ptr()), Out(z2.as_mut_ptr()));
        let (uu, zz) = (&u, &ze);
        let li = livel(i);
        sums = sum3(li / 4, |j, acc| {
            let f = |v: &[F192], k: usize| v[k] + ri * (v[k] + v[k + 1]);
            let (u0, u1, z0, z1) = (f(uu, 4 * j), f(uu, 4 * j + 2), f(zz, 4 * j), f(zz, 4 * j + 2));
            // SAFETY: quad j writes 2j, 2j+1 only.
            unsafe {
                *ou.p().add(2 * j) = u0;
                *ou.p().add(2 * j + 1) = u1;
                *oz.p().add(2 * j) = z0;
                *oz.p().add(2 * j + 1) = z1;
            }
            acc[0] ^= u0.mul_unreduced(z0);
            if direct {
                acc[1] ^= u1.mul_unreduced(z1);
            }
            acc[2] ^= (u0 + u1).mul_unreduced(z0 + z1);
        });
        std::mem::swap(&mut u, &mut u2);
        std::mem::swap(&mut ze, &mut z2);
        len /= 2;
        u.truncate(len);
        ze.truncate(len);
        for k in li / 2..livel(i + 1) {
            u[k] = F192::ZERO;
            ze[k] = F192::ZERO;
        }
    }
    unreachable!()
}

/// `M̃_o(r_x, r_y)` for the four matrices (prover: CSC, split `eq` tables).
pub fn mat_vals(b1: &Typed, rx: &[F192], ry: &[F192]) -> [F192; 4] {
    let (xl, xh) = eq_split(rx);
    let (yl, yh) = eq_split(ry);
    let ny = 1usize << b1.y_log;
    let live = b1.y_live.min(ny);
    let acc = crate::lv::parallel::map_reduce(
        live.div_ceil(CH),
        || [F192Unreduced::ZERO; 4],
        |ci| {
            let mut tot = [F192Unreduced::ZERO; 4];
            for y in ci * CH..((ci + 1) * CH).min(live) {
                let (s, t) = (b1.col_ptr[y] as usize, b1.col_ptr[y + 1] as usize);
                if s == t {
                    continue;
                }
                let mut acc = [F192Unreduced::ZERO; 4];
                let mut used = [false; 4];
                for &(x, oc) in &b1.cc[s..t] {
                    let (l, h) = (xl[x as usize & 1023], xh[x as usize >> 10]);
                    let o = (oc & 3) as usize;
                    used[o] = true;
                    if oc >> 2 == 0 {
                        acc[o] ^= l.mul_unreduced(h);
                    } else {
                        acc[o] ^= (l * h).mul_unreduced(b1.coefs[(oc >> 2) as usize]);
                    }
                }
                let ew = yl[y & 1023] * yh[y >> 10];
                for o in 0..4 {
                    if used[o] {
                        tot[o] ^= acc[o].reduce().mul_unreduced(ew);
                    }
                }
            }
            tot
        },
        |a, b| std::array::from_fn(|o| a[o] ^ b[o]),
    );
    acc.map(|a| a.reduce())
}

// ---------------------------------------------------------------- Φ_Q and the accumulator line

/// `eq(κ, o)` for the selector bits `o = o0 + 2·o1` (A = 0, B = 1, D = 2, W = 3).
pub fn eq_o(k: &[F192]) -> [F192; 4] {
    std::array::from_fn(|o| {
        let f = |i: usize| if (o >> i) & 1 == 1 { k[i] } else { F192::ONE + k[i] };
        f(0) * f(1)
    })
}

/// Brute force `Φ_Q(pt)` (`pt = κ ++ px ++ py`): full `eq` tables, every entry, serial. The toy verifier's
/// reference (independent of the prover's evaluators).
pub fn phi_brute(b1: &Typed, pt: &[F192]) -> F192 {
    let (k, rest) = pt.split_at(2);
    let (px, py) = rest.split_at(b1.x_log);
    let eo = eq_o(k);
    let v = mat_brute(b1, px, py);
    (0..4).map(|o| eo[o] * v[o]).sum()
}

pub fn mat_brute(b1: &Typed, px: &[F192], py: &[F192]) -> [F192; 4] {
    let ex = crate::lv::primitives::multilinear::eq_table_serial(px);
    let ey = crate::lv::primitives::multilinear::eq_table_serial(py);
    let mut v = [F192::ZERO; 4];
    for x in 0..1usize << b1.x_log {
        for e in &b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize] {
            v[e.o as usize] += e.c * ex[x] * ey[e.y as usize];
        }
    }
    v
}

/// `Φ_Q` at many points, prover side: per point the split `eq` tables (low 10 bits, high bits) of `x` and `y`,
/// laid out point-minor; one pass over the CSR for all points, parallel over blocks of 1024 slots.
pub fn phi_multi(b1: &Typed, pts: &[Vec<F192>]) -> Vec<F192> {
    let np = pts.len();
    let lo = 10usize;
    let split = |p: &[F192]| -> (Vec<F192>, Vec<F192>) { (eq_table(&p[..lo]), eq_table(&p[lo..])) };
    let mut exl = vec![F192::ZERO; np << lo];
    let mut exh = vec![F192::ZERO; np << (b1.x_log - lo)];
    let mut eyl = vec![F192::ZERO; np << lo];
    let mut eyh = vec![F192::ZERO; np << (b1.y_log - lo)];
    let mut eo = vec![[F192::ZERO; 4]; np];
    for (p, pt) in pts.iter().enumerate() {
        let (k, rest) = pt.split_at(2);
        let (px, py) = rest.split_at(b1.x_log);
        eo[p] = eq_o(k);
        let (a, b) = split(px);
        for (i, v) in a.into_iter().enumerate() {
            exl[i * np + p] = v;
        }
        for (i, v) in b.into_iter().enumerate() {
            exh[i * np + p] = v;
        }
        let (a, b) = split(py);
        for (i, v) in a.into_iter().enumerate() {
            eyl[i * np + p] = v;
        }
        for (i, v) in b.into_iter().enumerate() {
            eyh[i * np + p] = v;
        }
    }
    let nhi = 1usize << (b1.x_log - lo);
    let tot = crate::lv::parallel::map_reduce(
        nhi,
        || vec![F192::ZERO; 4 * np],
        |xh| {
            let mut r = vec![F192Unreduced::ZERO; 4 * np];
            let mut s = vec![F192Unreduced::ZERO; 4 * np];
            let mut any = false;
            for xl in 0..1usize << lo {
                let x = (xh << lo) | xl;
                let (st, en) = (b1.row_ptr[x] as usize, b1.row_ptr[x + 1] as usize);
                if st == en {
                    continue;
                }
                any = true;
                let mut used = [false; 4];
                for e in &b1.ent[st..en] {
                    let (yl, yh) = ((e.y as usize) & ((1 << lo) - 1), (e.y as usize) >> lo);
                    let (l, h) = (&eyl[yl * np..(yl + 1) * np], &eyh[yh * np..(yh + 1) * np]);
                    let so = &mut s[e.o as usize * np..(e.o as usize + 1) * np];
                    used[e.o as usize] = true;
                    if e.c == F192::ONE {
                        for p in 0..np {
                            so[p] ^= l[p].mul_unreduced(h[p]);
                        }
                    } else {
                        for p in 0..np {
                            so[p] ^= (l[p] * h[p]).mul_unreduced(e.c);
                        }
                    }
                }
                let xw = &exl[xl * np..(xl + 1) * np];
                for o in 0..4 {
                    if used[o] {
                        for p in 0..np {
                            let v = s[o * np + p].reduce();
                            r[o * np + p] ^= v.mul_unreduced(xw[p]);
                            s[o * np + p] = F192Unreduced::ZERO;
                        }
                    }
                }
            }
            let mut out = vec![F192::ZERO; 4 * np];
            if any {
                let xw = &exh[xh * np..(xh + 1) * np];
                for o in 0..4 {
                    for p in 0..np {
                        out[o * np + p] = r[o * np + p].reduce() * xw[p];
                    }
                }
            }
            out
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    );
    (0..np).map(|p| (0..4).map(|o| eo[p][o] * tot[o * np + p]).sum()).collect()
}

/// The accumulator step: `h` through `(a, v_prev)` and `(b, y_own)`, then `t`.
pub struct AccStep {
    pub h: Vec<F192>,
    pub t: F192,
    pub pt: Vec<F192>,
    pub y: F192,
    pub secs_eval: f64,
}

/// The polynomial of degree `< n` through `(j, ys[j])`, `j = 0 .. n` (the nodes `F192::new(j, 0, 0)`), by Newton's
/// divided differences with the node inverses computed once (`acc::interpolate` inverts in its inner loop).
pub fn interp_fixed(ys: &[F192]) -> Vec<F192> {
    let n = ys.len();
    let xs: Vec<F192> = (0..n as u64).map(|j| F192::new(j, 0, 0)).collect();
    // inv[j][i] = (x_i + x_{i−j})^{-1}: in characteristic 2, x_i + x_{i−j} is the node of i ^ (i − j)
    let mut need: Vec<u64> = Vec::new();
    for j in 1..n {
        for i in j..n {
            need.push((i ^ (i - j)) as u64);
        }
    }
    need.sort_unstable();
    need.dedup();
    let invs: HashMap<u64, F192> = need.iter().map(|&d| (d, F192::new(d, 0, 0).inv())).collect();
    let mut dd = ys.to_vec();
    for j in 1..n {
        for i in (j..n).rev() {
            dd[i] = (dd[i] + dd[i - 1]) * invs[&((i ^ (i - j)) as u64)];
        }
    }
    let mut c = vec![F192::ZERO; n];
    c[0] = dd[n - 1];
    for i in (0..n - 1).rev() {
        // c ← c·(X − x_i) + dd[i]
        let mut nc = vec![F192::ZERO; n];
        for k in 0..n - 1 {
            nc[k + 1] += c[k];
            nc[k] += c[k] * xs[i];
        }
        nc[0] += dd[i];
        c = nc;
    }
    c
}

pub fn acc_step(b1: &Typed, a: &[F192], v_prev: F192, b: &[F192], y_own: F192, rng: &mut Rng) -> AccStep {
    let d = a.len();
    let xs: Vec<F192> = (0..=d as u64).map(|j| F192::new(j, 0, 0)).collect();
    let pts: Vec<Vec<F192>> = xs[2..].iter().map(|&x| crate::lvm::acc::line(a, b, x)).collect();
    let t0 = Instant::now();
    let mut ys = vec![v_prev, y_own];
    ys.extend(match &b1.phik {
        Some(pk) => pk.eval(&pts),
        None => phi_multi(b1, &pts),
    });
    let secs_eval = t0.elapsed().as_secs_f64();
    let h = interp_fixed(&ys);
    let t = rng.e();
    let pt = crate::lvm::acc::line(a, b, t);
    let y = poly_eval(&h, t);
    AccStep { h, t, pt, y, secs_eval }
}

// ---------------------------------------------------------------- the whole backend

pub struct Proof {
    pub zc: Zc,
    pub gamma: F192,
    pub wr: Wr,
    pub v: [F192; 4],
    pub kappa: [F192; 2],
    pub acc: AccStep,
    pub tau: Vec<F192>,
    pub secs: [f64; 6],
}

/// Prove with `b1`'s matrices on `z`, from the accumulator `(a, v_prev)`. Times: abc, zerocheck, u, wiring
/// sumcheck, matrix values, h.
pub fn prove(b1: &Typed, z: &[F64], a: &[F192], v_prev: F192, rng: &mut Rng) -> Proof {
    let t = Instant::now();
    // default: the honest prover's `c = a·b` (Spartan's `Cz = Az∘Bz`): only `Az`, `Bz` are built and round 0
    // sums `q(∞)` alone; `LVM_B1_Q1=1`: `(D+W)z` built and every sum taken (the toy's tamper diagnostics)
    let general = std::env::var_os("LVM_B1_Q1").is_some();
    let (abc, ab) = if general { (Some(b1.abc(z)), None) } else { (None, Some(b1.ab_vals(z))) };
    let s0 = t.elapsed().as_secs_f64();
    let tau: Vec<F192> = (0..b1.x_log).map(|_| rng.e()).collect();
    let zc = match (abc, ab) {
        (Some(abc), _) => zerocheck(abc, &tau, rng),
        (_, Some(ab)) => zerocheck_fast(ab, &tau, b1.x_live, rng),
        _ => unreachable!(),
    };
    let s1 = t.elapsed().as_secs_f64();
    let gamma = rng.e();
    let u = wiring_u(b1, &zc.r, gamma);
    let s2 = t.elapsed().as_secs_f64();
    let wr = wiring(u, z, zc.a + gamma * zc.b + gamma * gamma * zc.c, b1.y_live, rng);
    let s3 = t.elapsed().as_secs_f64();
    // `v_o = M̃_o(r_x, r_y)`: by the class kernels when built (one point), else from the CSC
    let v = match &b1.phik {
        Some(pk) => {
            let pt: Vec<F192> = [&[F192::ZERO, F192::ZERO][..], &zc.r, &wr.r].concat();
            let m = pk.mats(std::slice::from_ref(&pt));
            [m[0], m[1], m[2], m[3]]
        }
        None => mat_vals(b1, &zc.r, &wr.r),
    };
    let s4 = t.elapsed().as_secs_f64();
    let kappa = [rng.e(), rng.e()];
    let eo = eq_o(&kappa);
    let y_own: F192 = (0..4).map(|o| eo[o] * v[o]).sum();
    let b: Vec<F192> = [&kappa[..], &zc.r, &wr.r].concat();
    let acc = acc_step(b1, a, v_prev, &b, y_own, rng);
    let s5 = t.elapsed().as_secs_f64();
    Proof { zc, gamma, wr, v, kappa, acc, tau, secs: [s0, s1 - s0, s2 - s1, s3 - s2, s4 - s3, s5 - s4] }
}

/// The toy verifier (B-DES §1.2) with brute-force `M̃`, `z̃` and `Φ_Q`. `Err(check)` names the first failing
/// check.
pub fn verify(b1: &Typed, z_true: &[F64], pf: &Proof, a: &[F192], v_prev: F192, brute_m: bool) -> Result<(), String> {
    // zerocheck
    let mut claim = F192::ZERO;
    for (i, g) in pf.zc.rounds.iter().enumerate() {
        if poly_eval(g, F192::ZERO) + poly_eval(g, F192::ONE) != claim {
            return Err(format!("zerocheck round {i}: g(0) + g(1) ≠ claim"));
        }
        claim = poly_eval(g, pf.zc.r[i]);
    }
    let eqt: F192 = pf.tau.iter().zip(&pf.zc.r).map(|(&t, &r)| F192::ONE + t + r).product();
    if claim != eqt * (pf.zc.a * pf.zc.b + pf.zc.c) {
        return Err("zerocheck final: eq(τ, r_x)·(a*·b* + c*)".into());
    }
    // wiring
    let g2 = pf.gamma * pf.gamma;
    let mut claim = pf.zc.a + pf.gamma * pf.zc.b + g2 * pf.zc.c;
    for (i, g) in pf.wr.rounds.iter().enumerate() {
        if poly_eval(g, F192::ZERO) + poly_eval(g, F192::ONE) != claim {
            return Err(format!("wiring round {i}: g(0) + g(1) ≠ claim"));
        }
        claim = poly_eval(g, pf.wr.r[i]);
    }
    let v = pf.v;
    let u_star = v[0] + pf.gamma * v[1] + g2 * (v[2] + v[3]);
    if claim != u_star * pf.wr.z {
        return Err("wiring final: (v_A + γv_B + γ²(v_D + v_W))·z̃(r_y)".into());
    }
    // the brute-force references: z̃(r_y) (the C_main claim and the virtual regions), M̃_o(r_x, r_y)
    if mle_eval_par(z_true, &pf.wr.r) != pf.wr.z {
        return Err("z̃(r_y) ≠ the committed words' extension".into());
    }
    let mv = mat_brute(b1, &pf.zc.r, &pf.wr.r);
    if brute_m && mv != v {
        return Err(format!("M̃_o(r_x, r_y) ≠ v_o (o = {:?})", (0..4).filter(|&o| mv[o] != v[o]).collect::<Vec<_>>()));
    }
    // accumulator
    let h = &pf.acc.h;
    if h.len() != a.len() + 1 {
        return Err("h has D + 1 coefficients".into());
    }
    if poly_eval(h, F192::ZERO) != v_prev {
        return Err("acc: h(0) ≠ acc_in.y".into());
    }
    let eo = eq_o(&pf.kappa);
    let y_own: F192 = (0..4).map(|o| eo[o] * v[o]).sum();
    if poly_eval(h, F192::ONE) != y_own {
        return Err("acc: h(1) ≠ Σ eq(κ, o)·v_o".into());
    }
    let b: Vec<F192> = [&pf.kappa[..], &pf.zc.r, &pf.wr.r].concat();
    let pt = crate::lvm::acc::line(a, &b, pf.acc.t);
    if phi_brute(b1, &pt) != poly_eval(h, pf.acc.t) {
        return Err("acc: Φ_Q(line(t)) ≠ h(t)".into());
    }
    Ok(())
}

/// `F192` product throughput on one thread (independent products, 4 chains), ns per product.
pub fn fe_bench() -> f64 {
    let mut rng = Rng::new(7);
    let a: Vec<F192> = (0..1 << 12).map(|_| rng.e()).collect();
    let b: Vec<F192> = (0..1 << 12).map(|_| rng.e()).collect();
    let reps = 2000;
    let t = Instant::now();
    let mut acc = F192::ZERO;
    for _ in 0..reps {
        for i in 0..a.len() {
            acc += a[i] * b[i];
        }
    }
    std::hint::black_box(acc);
    t.elapsed().as_secs_f64() * 1e9 / (reps * a.len()) as f64
}
