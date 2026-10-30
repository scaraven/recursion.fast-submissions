//! The node's M region (BLUEPRINT §4.3–4.4, A.7; S-E12b–d and INT-9 node dump, `logs/INT-9/nodedump/`):
//! the loader of the dumped prototype rows (`mrows-p{π}`), register forms (`mregs-p{π}`),
//! auxiliary imports (`maux-p{π}`) and per-kind slot tables (`node-N*.txt`), and the **slot fill**:
//! the prototype program run on the slot's child (`ir::run_regs`, at the slot's kind index), its
//! registers written at their cells, the auxiliary imports, then every other cell by a forward row
//! solve (each row `(Az)(Bz) = Cz` with one unknown cell is linear in it unless the cell is in both
//! `A` and `B`), the rest zero; then every row is checked.
//!
//! Everything is read from the dump: a re-dump (INT-8's uniform `gen4`, S-E12e's `shiftMask`
//! templates) is a reload. The dump must carry, or sit next to, the prototype programs whose
//! registers `mregs` numbers (`proto-p{π}.txt`, `IRDump8`'s mux format; `FLOCK_PROTO_DIR`).

use crate::field::F;
use crate::ir::V;
use std::path::Path;

/// A prototype's region: `2^20` cells and rows (`slotM4`).
pub const SLOT: usize = 1 << 20;

/// E1b: the arena and replay placement of `FRNodeRows4ArenaPlace` / `FRNodeRows4Defs` (e447823; region-
/// relative cells and rows). Arena₁ `[AR_A1, AR_A1 + AR_N)` holds the slot's segment stream (rows
/// `AR_R1 + e`, link rows to H), the bits `[AR_BT, AR_BT + AR_NB)` (rows `AR_RB + j`: `b·b = b`), the ask
/// templates' rows from `AR_R2`.
pub const AR_A1: usize = 290_816;
pub const AR_N: usize = 96_944;
pub const AR_BT: usize = 389_120;
pub const AR_NB: usize = 16_384;
pub const AR_R2: usize = 720_896;
pub const AR_R2N: usize = 154_368;
pub const AR_R1: usize = AR_R2 + AR_R2N;
pub const AR_RB: usize = 972_288;
/// `N4s.repB`: a replay template's local `j` is the dump's cell `REP_B + j`.
pub const REP_B: u64 = 1 << 40;
/// SEG-R2: a segment slot's replay row `k` (band B from `repSegB`, then band A from `repA`).
pub fn seg_row(k: usize) -> usize {
    if k < 27_136 { 988_672 + k } else { 688_128 + (k - 27_136) }
}
/// A region-local cell in one of SEG-R2's three local bands.
pub fn is_seg_local(l: usize) -> bool {
    (277_402..290_816).contains(&l) || (405_504..441_152).contains(&l) || (1_003_010..1_015_728).contains(&l)
}
/// SEG-R2's `segCell`: a segment slot's replay local `j` in its region's free cell bands.
pub fn seg_cell(j: usize) -> usize {
    if j < 1 << 12 { 277_402 + j } else if j < 39_744 { 405_504 + (j - (1 << 12)) } else { 1_003_010 + (j - 39_744) }
}

/// Sparse rows: per row its index and three term ranges into `cells`/`coefs`.
pub struct Rows {
    pub idx: Vec<u32>,
    /// `[a0, a1, b1, c1]` per row: A is `a0..a1`, B `a1..b1`, C `b1..c1`.
    pub rng: Vec<[u32; 4]>,
    pub cells: Vec<u32>,
    /// Each term's coefficient as an index into `cv` (pass 13: 2 bytes a term instead of 16; the
    /// node data's 5.3 M terms a prototype carry 513 distinct values). `coef(t)` is the value.
    pub coefs: Vec<u16>,
    /// The distinct coefficients, `cv[0] = 1` (`ONE_IX`).
    pub cv: Vec<F>,
    /// Their inverses (`done`; a solve whose linear factor is one coefficient needs no inversion).
    pub cvinv: Vec<F>,
    /// The interning map of `cv` while the rows are built (`term`; empty after `done`).
    ix: std::collections::HashMap<[u8; 16], u16>,
}

/// The index of the coefficient 1 in every `Rows::cv`.
pub const ONE_IX: u16 = 0;

impl Rows {
    pub fn new() -> Rows {
        let mut r = Rows { idx: Vec::new(), rng: Vec::new(), cells: Vec::new(), coefs: Vec::new(), cv: Vec::new(), cvinv: Vec::new(), ix: Default::default() };
        assert_eq!(r.intern(F::ONE), ONE_IX);
        r
    }
    /// Rows from their arrays (the image; `cv[0]` must be 1 and every index in range).
    pub fn from_parts(idx: Vec<u32>, rng: Vec<[u32; 4]>, cells: Vec<u32>, coefs: Vec<u16>, cv: Vec<F>) -> Option<Rows> {
        let ok = cv.first() == Some(&F::ONE) && cells.len() == coefs.len() && coefs.iter().all(|&c| (c as usize) < cv.len());
        ok.then(|| {
            let mut r = Rows { idx, rng, cells, coefs, cv, cvinv: Vec::new(), ix: Default::default() };
            r.done();
            r
        })
    }
    pub fn len(&self) -> usize {
        self.idx.len()
    }
    /// The index of the coefficient `c` in `cv` (added if new).
    pub fn intern(&mut self, c: F) -> u16 {
        let k = c.to_bytes();
        if let Some(&i) = self.ix.get(&k) {
            return i;
        }
        let i = u16::try_from(self.cv.len()).expect("node rows: more than 2^16 distinct coefficients");
        self.cv.push(c);
        self.ix.insert(k, i);
        i
    }
    /// Append the term `c·cell`.
    #[inline]
    pub fn term(&mut self, cell: u32, c: F) {
        let i = self.intern(c);
        self.cells.push(cell);
        self.coefs.push(i);
    }
    /// Drop the interning map and compute the inverses (the rows are complete).
    pub fn done(&mut self) {
        self.ix = Default::default();
        self.cvinv = self.cv.iter().map(|c| c.inv()).collect();
    }
    /// The inverse of coefficient `i` (`cvinv`, else computed).
    #[inline(always)]
    fn inv_ix(&self, i: u16) -> F {
        self.cvinv.get(i as usize).copied().unwrap_or_else(|| self.cv[i as usize].inv())
    }
    /// Term `t`'s coefficient.
    #[inline(always)]
    pub fn coef(&self, t: usize) -> F {
        self.cv[self.coefs[t] as usize]
    }
    /// Term `t`'s coefficient times `x` (no product for a coefficient 1).
    #[inline(always)]
    pub fn cmul(&self, t: usize, x: F) -> F {
        let i = self.coefs[t];
        if i == ONE_IX {
            x
        } else {
            self.cv[i as usize] * x
        }
    }
    /// Every term's coefficient as a value (the 16-byte form before pass 13; tests, `bench`).
    pub fn coef_values(&self) -> Vec<F> {
        self.coefs.iter().map(|&i| self.cv[i as usize]).collect()
    }
    /// Rebuild the interning map (to append rows after `done`).
    pub fn reopen(&mut self) {
        self.ix = self.cv.iter().enumerate().map(|(i, c)| (c.to_bytes(), i as u16)).collect();
    }
    /// Append one row (`(cell, coefficient)` per form).
    pub fn push_row(&mut self, idx: u32, forms: [&[(u32, F)]; 3]) {
        let a0 = self.cells.len() as u32;
        let mut rg = [a0; 4];
        for k in 0..3 {
            for &(c, x) in forms[k] {
                self.term(c, x);
            }
            rg[k + 1] = self.cells.len() as u32;
        }
        self.idx.push(idx);
        self.rng.push(rg);
    }
    /// Push one `k | A | B | C` line with its row index and cells mapped (`cell` gets the dump's
    /// cell, which may exceed `u32`: a replay local).
    fn push_line_map(&mut self, line: &str, row: &dyn Fn(usize) -> u32, cell: &dyn Fn(u64) -> u32) {
        let mut it = line.split(" | ");
        let k: usize = it.next().unwrap().trim().parse().expect("row");
        let a0 = self.cells.len() as u32;
        let mut rg = [a0; 4];
        for m in 0..3 {
            for t in it.next().unwrap_or("").trim().split(' ') {
                if t.is_empty() {
                    continue;
                }
                let (c, h) = t.split_once(':').expect("cell:coef");
                self.term(cell(c.parse().expect("cell")), parse_coef(h));
            }
            rg[m + 1] = self.cells.len() as u32;
        }
        self.idx.push(row(k));
        self.rng.push(rg);
    }
    fn push_terms(&mut self, s: &str) {
        for t in s.split(' ') {
            if t.is_empty() {
                continue;
            }
            let (c, h) = t.split_once(':').expect("cell:coef");
            self.term(c.parse().expect("cell"), parse_coef(h));
        }
    }
    /// Push one `row | A | B | C` line.
    fn push_line(&mut self, line: &str) {
        let mut it = line.split(" | ");
        let r: u32 = it.next().unwrap().trim().parse().expect("row");
        let a0 = self.cells.len() as u32;
        let mut rg = [a0; 4];
        for k in 0..3 {
            self.push_terms(it.next().unwrap_or("").trim());
            rg[k + 1] = self.cells.len() as u32;
        }
        self.idx.push(r);
        self.rng.push(rg);
    }
    /// Row `i`'s three forms evaluated at `w` (cells mapped by `m`).
    pub fn eval(&self, i: usize, w: &dyn Fn(u32) -> F) -> [F; 3] {
        let rg = self.rng[i];
        let mut o = [F::ZERO; 3];
        for k in 0..3 {
            for t in rg[k] as usize..rg[k + 1] as usize {
                o[k] += self.cmul(t, w(self.cells[t]));
            }
        }
        o
    }
}


fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn parse_coef(h: &str) -> F {
    if h.len() == 32 && h.starts_with("01") && h[2..].bytes().all(|b| b == b'0') {
        F::ONE
    } else {
        F::from_bytes(&unhex(h))
    }
}

/// The longest register form `Proto::load` keeps (E1: the cap check's running sums are dropped).
pub const LONG_FORM: usize = 256;

/// A register's type in `mregs` (the F components it occupies).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Ty {
    Untracked,
    F,
    K,
    D,
    Bit,
    AF(usize),
    AK(usize),
}

/// One register: import flag, type, one form per F component (ranges into `Proto::fcells`).
pub struct Reg {
    pub imp: bool,
    pub ty: Ty,
    pub forms: Vec<(u32, u32)>,
}

/// An auxiliary import: the register, its reading, its cells (a range into `Proto::fcells`).
pub struct Aux {
    pub reg: u32,
    pub bits: bool,
    pub n: usize,
    pub terms: (u32, u32),
}

/// One prototype: its rows (M-relative cells and rows of region `π`), register forms and
/// auxiliary imports.
pub struct Proto {
    pub pi: usize,
    pub rows: Rows,
    pub regs: Vec<Reg>,
    pub aux: Vec<Aux>,
    pub fcells: Vec<u32>,
    pub fcoefs: Vec<F>,
    /// E1b: prototype 0's replay rows (`repRowsP (rtC1d 0) 0`, REPF: slot 0 of `N2`/`N4`, rows and
    /// locals in the spare region `κ.vslots`): row `k`, frame cell `c < 2^20` as is, local `j` at
    /// `2^20 + j`. Empty for prototype 1 (its replay rows are in `rows`, moved like the rest).
    pub spare: Rows,
    /// The solve order of an inactive fill (`0`) and of an active fill at child index `ix` of a
    /// full (`1 + ix`) or partial (`4 + ix`: a segment below its kind's cap) child, recorded by the
    /// first such fill or loaded from `prover setup` (`load_plans`).
    pub plan: [std::sync::OnceLock<Vec<(u32, u32)>>; PLAN_KEYS],
    /// The cell → rows adjacency of `rows` (`worklist`), built once.
    pub adj: std::sync::OnceLock<(Vec<u32>, Vec<u32>)>,
    /// An inactive fill's cells (they do not depend on any child), from `prover setup`.
    pub inactive: std::sync::OnceLock<Vec<F>>,
    /// `fcoefs`' inverses (pass 13: a register's cell is its value over its coefficient; built
    /// once, before a request, by `warm_adjacency`).
    pub fcinv: std::sync::OnceLock<Vec<F>>,
    /// The rows' terms by cell (`by_cell`; `Mats::m_scatter`'s gather), built before a request.
    pub bycell: std::sync::OnceLock<ByCell>,
    /// Each recorded order's level schedule (`schedule`; the parallel replay), built before a
    /// request for the orders `prover setup` recorded.
    pub sched: [std::sync::OnceLock<Sched>; PLAN_KEYS],
}

/// A recorded solve order's level schedule (pass 13): the order's entries grouped into levels such
/// that an entry of a level reads (its row's cells) and writes (its cell) no cell another entry of
/// the same level writes, and every entry comes after the earlier entries it depends on (the
/// writers of its row's cells) and after the earlier readers of its cell (they saw it unknown).
/// So a level's entries run in parallel and each sees exactly the cells it saw in the sequential
/// replay. Level `j` is `ent[lv[j]..lv[j + 1]]` (positions in the order, ascending).
pub struct Sched {
    pub ent: Vec<u32>,
    pub lv: Vec<u32>,
}

/// `Sched` of the order `pl` over `rw`.
pub fn schedule(rw: &Rows, base: u32, pl: &[(u32, u32)]) -> Sched {
    // the level of a cell's (latest) writer + 1 (0: none so far); 1 + the highest level of an
    // entry that read the cell
    let mut lw = vec![0u32; SLOT];
    let mut lr = vec![0u32; SLOT];
    let mut lev: Vec<u32> = Vec::with_capacity(pl.len());
    for &(r, c) in pl {
        let rg = rw.rng[r as usize];
        let cs = &rw.cells[rg[0] as usize..rg[3] as usize];
        let c = c as usize;
        let mut l = lr[c].max(lw[c]);
        for &x in cs {
            l = l.max(lw[(x - base) as usize]);
        }
        lev.push(l);
        lw[c] = lw[c].max(l + 1);
        for &x in cs {
            let x = (x - base) as usize;
            lr[x] = lr[x].max(l + 1);
        }
    }
    let nl = lev.iter().map(|&l| l as usize + 1).max().unwrap_or(0);
    let mut lv = vec![0u32; nl + 1];
    for &l in &lev {
        lv[l as usize + 1] += 1;
    }
    for j in 0..nl {
        lv[j + 1] += lv[j];
    }
    let mut pos = lv[..nl].to_vec();
    let mut ent = vec![0u32; pl.len()];
    for (q, &l) in lev.iter().enumerate() {
        ent[pos[l as usize] as usize] = q as u32;
        pos[l as usize] += 1;
    }
    Sched { ent, lv }
}

/// Whether a replay runs by levels (`FLOCK_SEQ_REPLAY=1`: the sequential replay, the reference).
fn par_replay() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FLOCK_SEQ_REPLAY").is_none())
}

/// A level of fewer entries runs on the calling thread.
const LEVEL_PAR_MIN: usize = 4096;

/// The replay of order `pl` by its levels `sc`: each entry solves its own cell only (`try_row_p`
/// with `want`; an entry that would solve another cell is a miss, retried by the caller in order).
/// Returns the solved count and the misses (in the order's order).
fn replay_levels(rw: &Rows, base: u32, pl: &[(u32, u32)], sc: &Sched, val: &mut [F], known: &mut [bool]) -> (usize, Vec<(u32, u32)>) {
    assert!(val.len() >= SLOT && known.len() >= SLOT);
    let (vp, kp) = (crate::par::SyncPtr(val.as_mut_ptr()), crate::par::SyncPtr(known.as_mut_ptr()));
    let run = |es: &[u32]| -> (usize, Vec<u32>) {
        let (vp, kp) = (&vp, &kp);
        let (mut n, mut miss) = (0usize, Vec::new());
        for &q in es {
            let (r, c) = pl[q as usize];
            // SAFETY: `Sched`: no other entry of this level touches this row's cells or `c`, and
            // `try_row_p` with `want = c` writes `c` only; the levels run one after another
            match unsafe { try_row_p(rw, base, r as usize, Some(c as usize), vp.0, kp.0, None) } {
                Some(_) => n += 1,
                None if unsafe { *kp.0.add(c as usize) } => {}
                None => miss.push(q),
            }
        }
        (n, miss)
    };
    let (mut solved, mut miss) = (0usize, Vec::new());
    for j in 0..sc.lv.len() - 1 {
        let es = &sc.ent[sc.lv[j] as usize..sc.lv[j + 1] as usize];
        let parts = if es.len() < LEVEL_PAR_MIN { vec![run(es)] } else { crate::par::map_chunks(es.len(), 1024, |lo, hi| run(&es[lo..hi])) };
        for (n, m) in parts {
            solved += n;
            miss.extend(m);
        }
    }
    miss.sort_unstable();
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        let big: Vec<usize> = (0..sc.lv.len() - 1).map(|j| (sc.lv[j + 1] - sc.lv[j]) as usize).filter(|&n| n >= LEVEL_PAR_MIN).collect();
        eprintln!("  replay by levels: {} entries, {} levels ({} parallel, {} entries), {} misses", pl.len(), sc.lv.len() - 1, big.len(), big.iter().sum::<usize>(), miss.len());
    }
    (solved, miss.into_iter().map(|q| pl[q as usize]).collect())
}

/// A prototype's terms grouped by cell (pass 13): region-local cell `l`'s terms are
/// `ent[ptr[l]..ptr[l + 1]]` in row order, each `row | m << 30` (`row` region-local, `m` the
/// matrix: A, B, C) with its coefficient index `coef` (into `Rows::cv`).
pub struct ByCell {
    pub ptr: Vec<u32>,
    pub ent: Vec<u32>,
    pub coef: Vec<u16>,
}

/// `ByCell` of `rw` (cells and rows of the region at `base`).
pub fn by_cell(rw: &Rows, base: u32) -> ByCell {
    let mut ptr = vec![0u32; SLOT + 1];
    for &c in &rw.cells {
        ptr[(c - base) as usize + 1] += 1;
    }
    for l in 0..SLOT {
        ptr[l + 1] += ptr[l];
    }
    let mut pos: Vec<u32> = ptr[..SLOT].to_vec();
    let n = rw.cells.len();
    let (mut ent, mut coef) = (vec![0u32; n], vec![0u16; n]);
    for i in 0..rw.len() {
        let row = rw.idx[i] - base;
        assert!(row < 1 << 30);
        let rg = rw.rng[i];
        for m in 0..3 {
            for t in rg[m] as usize..rg[m + 1] as usize {
                let l = (rw.cells[t] - base) as usize;
                let q = pos[l] as usize;
                ent[q] = row | (m as u32) << 30;
                coef[q] = rw.coefs[t];
                pos[l] += 1;
            }
        }
    }
    ByCell { ptr, ent, coef }
}

impl Proto {
    /// The level schedule of order `key` (built once; `None` without that order).
    pub fn sched_for(&self, key: usize) -> Option<&Sched> {
        let pl = self.plan[key].get()?;
        Some(self.sched[key].get_or_init(|| schedule(&self.rows, (self.pi * SLOT) as u32, pl)))
    }
    /// The terms by cell (built once).
    pub fn by_cell(&self) -> &ByCell {
        self.bycell.get_or_init(|| by_cell(&self.rows, (self.pi * SLOT) as u32))
    }
    /// `fcoefs`' inverses (each distinct value inverted once).
    pub fn fcinv(&self) -> &[F] {
        self.fcinv.get_or_init(|| {
            let mut m: std::collections::HashMap<[u8; 16], F> = Default::default();
            self.fcoefs.iter().map(|k| *m.entry(k.to_bytes()).or_insert_with(|| k.inv())).collect()
        })
    }
}

/// Per node kind (`node-N*.txt`): the slot table, the link rows, the public cells.
pub struct KindTab {
    pub name: String,
    pub m: usize,
    pub blocks: usize,
    pub m_base: usize,
    pub one_cell: usize,
    pub log_m: usize,
    pub l_base: usize,
    pub n_l: usize,
    pub h_used: usize,
    /// Per slot: prototype, first L bit cell, the bit count, the three selector bits' cells.
    pub slots: Vec<(usize, usize, usize, [usize; 3])>,
    /// Link rows (global row indices, absolute cells).
    pub links: Rows,
    pub cells: Vec<usize>,
    /// The link rows from `node-N*.txt` (the first `base_links`; E1b's arena₁ and replay rows follow).
    pub base_links: usize,
    /// The link rows' terms by cell (built once; `links_by_cell`).
    pub lbc: std::sync::OnceLock<LinkByCell>,
}

/// A kind table's link terms grouped by cell (E1b): the distinct cells `cells` (ascending), cell
/// `cells[u]`'s terms `ent[ptr[u]..ptr[u + 1]]`, each `row | m << 30` (`row` the link row's position in
/// `links`, `m` the matrix) with its coefficient index `coef`.
pub struct LinkByCell {
    pub cells: Vec<u32>,
    pub ptr: Vec<u32>,
    pub ent: Vec<u32>,
    pub coef: Vec<u16>,
}

impl KindTab {
    /// The link terms by cell (built once).
    pub fn links_by_cell(&self) -> &LinkByCell {
        self.lbc.get_or_init(|| {
            // a counting sort by cell over the cells' range (the kinds' M spans < 2^26 cells)
            let l = &self.links;
            let n = l.cells.iter().map(|&c| c as usize + 1).max().unwrap_or(0);
            let mut cnt = vec![0u32; n + 1];
            for &c in &l.cells {
                cnt[c as usize + 1] += 1;
            }
            for i in 0..n {
                cnt[i + 1] += cnt[i];
            }
            let mut ent = vec![0u32; l.cells.len()];
            let mut coef = vec![0u16; l.cells.len()];
            let mut pos = cnt.clone();
            for i in 0..l.len() {
                let rg = l.rng[i];
                for m in 0..3 {
                    for q in rg[m] as usize..rg[m + 1] as usize {
                        let c = l.cells[q] as usize;
                        let p = pos[c] as usize;
                        ent[p] = i as u32 | (m as u32) << 30;
                        coef[p] = l.coefs[q];
                        pos[c] += 1;
                    }
                }
            }
            drop(pos);
            let mut cells = Vec::new();
            let mut ptr = vec![0u32];
            for c in 0..n {
                if cnt[c + 1] > cnt[c] {
                    cells.push(c as u32);
                    ptr.push(cnt[c + 1]);
                }
            }
            LinkByCell { cells, ptr, ent, coef }
        })
    }
    /// Per link row and matrix, `Σ coef·x(cell)` (in parallel).
    pub fn links_eval(&self, x: &(dyn Fn(usize) -> F + Sync)) -> Vec<[F; 3]> {
        let l = &self.links;
        crate::par::collect_vec(l.len(), 1 << 12, |i| {
            let rg = l.rng[i];
            let mut o = [F::ZERO; 3];
            for m in 0..3 {
                for q in rg[m] as usize..rg[m + 1] as usize {
                    o[m] += l.cmul(q, x(l.cells[q] as usize));
                }
            }
            o
        })
    }
    /// Per distinct link cell, `Σ_{rows, m} r(row)·s_m·coef` (in parallel; `r` per link row).
    pub fn links_cols(&self, r: &[F], s: &[F]) -> Vec<F> {
        let b = self.links_by_cell();
        let cv = &self.links.cv;
        crate::par::collect_vec(b.cells.len(), 1 << 12, |u| {
            let mut acc = [F::ZERO; 3];
            for q in b.ptr[u] as usize..b.ptr[u + 1] as usize {
                let en = b.ent[q];
                let (i, m) = ((en & 0x3FFF_FFFF) as usize, (en >> 30) as usize);
                acc[m] += cv[b.coef[q] as usize] * r[i];
            }
            s[0] * acc[0] + s[1] * acc[1] + s[2] * acc[2]
        })
    }
}

fn field<'a>(h: &'a str, key: &str) -> &'a str {
    let i = h.find(key).unwrap_or_else(|| panic!("{key} in {h}")) + key.len();
    let s = h[i..].trim_start();
    let e = s.find(|c: char| !(c.is_ascii_digit() || c == '^')).unwrap_or(s.len());
    &s[..e]
}

fn num(s: &str) -> usize {
    match s.split_once('^') {
        Some((a, b)) => a.parse::<usize>().unwrap().pow(b.parse().unwrap()),
        None => s.parse().unwrap(),
    }
}

impl KindTab {
    pub fn load(path: &Path) -> KindTab {
        let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        Self::parse(&text)
    }
    /// `node-N*.txt`'s text.
    pub fn parse(text: &str) -> KindTab {
        let mut lines = text.lines();
        let h = lines.next().unwrap();
        let name = h.trim_start_matches("# ").split(':').next().unwrap().rsplit('.').next().unwrap().to_string();
        let nm = field(h, "N_M 2");
        let mut kt = KindTab {
            name,
            m: num(field(h, ": m ")),
            blocks: num(field(h, "blocks ")),
            m_base: num(field(h, "M base block ")),
            one_cell: num(field(h, "one cell ")),
            log_m: num(nm.trim_start_matches('^')),
            l_base: num(field(h, "L base block ")),
            n_l: num(field(h, "N_L ")),
            h_used: num(field(h, "H used ")),
            slots: Vec::new(),
            links: Rows::new(),
            cells: Vec::new(),
            base_links: 0,
            lbc: Default::default(),
        };
        let mut sec = 0;
        for l in lines {
            if let Some(c) = l.strip_prefix("# public cells") {
                let v = c.split('[').nth(1).unwrap().trim_end_matches(']');
                kt.cells = v.split(", ").map(|x| x.trim().parse().unwrap()).collect();
                continue;
            }
            if l.starts_with("# link rows") {
                sec = 1;
                continue;
            }
            if l.starts_with('#') || l.is_empty() {
                continue;
            }
            if sec == 0 {
                let p: Vec<&str> = l.split(" | ").collect();
                let (a, b) = p[3].split_once(", ").unwrap();
                let s: Vec<usize> = p[4].split(' ').map(|x| x.parse().unwrap()).collect();
                kt.slots.push((p[1].trim().parse().unwrap(), a.parse().unwrap(), b.trim().parse().unwrap(), [s[0], s[1], s[2]]));
            } else {
                kt.links.push_line(l);
            }
        }
        kt.links.done();
        kt.base_links = kt.links.len();
        kt
    }
    /// The slot's region's first absolute cell.
    pub fn slot_cell(&self, sg: usize) -> usize {
        self.one_cell + sg * SLOT
    }
}

/// E1b: the rows of prototype `π` beyond `protoRows π` (NodeDumpX's files), appended to `rows` in
/// this order: the ask templates' rows (`mask-p{π}.txt`, `askRowsT π`: row `k` at `π·2^20 + arR2 + k`),
/// the bits' rows (`bitRows`, generated), and for prototype 1 its replay rows (`mrep-p1.txt`, moved to
/// SEG-R2's bands and cells); prototype 0's replay rows go to `spare` (`Proto::spare`).
pub fn load_extra(dir: &Path, pi: usize, rows: &mut Rows, spare: &mut Rows) {
    let rd = |n: &str| std::fs::read_to_string(dir.join(n)).unwrap_or_else(|e| panic!("{}/{n}: {e}", dir.display()));
    let base = pi * SLOT;
    for l in rd(&format!("mask-p{pi}.txt")).lines() {
        if !l.starts_with('#') && !l.is_empty() {
            rows.push_line_map(l, &|k| (base + AR_R2 + k) as u32, &|c| u32::try_from(c).expect("an ask row's cell"));
        }
    }
    add_bit_rows(rows, pi);
    for l in rd(&format!("mrep-p{pi}.txt")).lines() {
        if l.starts_with('#') || l.is_empty() {
            continue;
        }
        if pi == 0 {
            spare.push_line_map(l, &|k| k as u32, &|c| if c < REP_B { u32::try_from(c).unwrap() } else { (SLOT as u64 + (c - REP_B)) as u32 });
        } else {
            rows.push_line_map(l, &|k| (base + seg_row(k)) as u32, &|c| if c < REP_B { c as u32 } else { (base + seg_cell((c - REP_B) as usize)) as u32 });
        }
    }
}

/// The bits' rows of region `π` (`bitRows`: row `π·2^20 + arRb + j` is `b·b = b`, `b = π·2^20 + arBt + j`).
pub fn add_bit_rows(rows: &mut Rows, pi: usize) {
    for j in 0..AR_NB {
        let b = [((pi * SLOT + AR_BT + j) as u32, F::ONE)];
        rows.push_row((pi * SLOT + AR_RB + j) as u32, [&b, &b, &b]);
    }
}

impl Proto {
    pub fn load(dir: &Path, pi: usize) -> Proto {
        let rd = |n: &str| std::fs::read_to_string(dir.join(n)).unwrap_or_else(|e| panic!("{}/{n}: {e}", dir.display()));
        let mut rows = Rows::new();
        for l in rd(&format!("mrows-p{pi}.txt")).lines() {
            if !l.starts_with('#') && !l.is_empty() {
                rows.push_line(l);
            }
        }
        let mut spare = Rows::new();
        load_extra(dir, pi, &mut rows, &mut spare);
        rows.done();
        spare.done();
        let (mut fcells, mut fcoefs) = (Vec::new(), Vec::new());
        let push = |s: &str, fc: &mut Vec<u32>, fk: &mut Vec<F>| -> (u32, u32) {
            let a = fc.len() as u32;
            for t in s.split(' ') {
                if let Some((c, h)) = t.split_once(':') {
                    fc.push(c.parse().unwrap());
                    fk.push(parse_coef(h));
                }
            }
            (a, fc.len() as u32)
        };
        let mut regs = Vec::new();
        for l in rd(&format!("mregs-p{pi}.txt")).lines() {
            if l.starts_with('#') || l.is_empty() {
                continue;
            }
            let p: Vec<&str> = l.splitn(4, " | ").collect();
            assert_eq!(p[0].parse::<usize>().unwrap(), regs.len(), "mregs order");
            let ty = match p[2].trim() {
                "untracked" => Ty::Untracked,
                "F" => Ty::F,
                "K" => Ty::K,
                "D" => Ty::D,
                "Bit" => Ty::Bit,
                t if t.starts_with("AF") => Ty::AF(t[2..].parse().unwrap()),
                t if t.starts_with("AK") => Ty::AK(t[2..].parse().unwrap()),
                t => panic!("mregs type {t}"),
            };
            // a form of more than `LONG_FORM` terms is not kept (an empty range): the fill writes
            // single-cell forms only and checks the others (`form_mismatch`), and the long ones
            // (A2″'s cap-check running sums: up to ≈ 17 k terms, 90 % of `mregs`' size) are linear
            // sums of cells the rows already bind
            let forms = match p.get(3) {
                Some(f) => f
                    .split(" ; ")
                    .map(|s| if s.split(' ').filter(|t| !t.is_empty()).count() > LONG_FORM { (fcells.len() as u32, fcells.len() as u32) } else { push(s, &mut fcells, &mut fcoefs) })
                    .collect(),
                None => Vec::new(),
            };
            regs.push(Reg { imp: p[1].trim() == "imp", ty, forms });
        }
        let mut aux = Vec::new();
        for l in rd(&format!("maux-p{pi}.txt")).lines() {
            if l.starts_with('#') || l.is_empty() {
                continue;
            }
            let p: Vec<&str> = l.splitn(3, " | ").collect();
            let (k, n) = p[1].trim().split_once(' ').unwrap();
            let terms = push(p.get(2).copied().unwrap_or(""), &mut fcells, &mut fcoefs);
            aux.push(Aux { reg: p[0].trim().parse().unwrap(), bits: k == "bits", n: n.parse().unwrap(), terms });
        }
        Proto { pi, rows, regs, aux, fcells, fcoefs, spare, plan: Default::default(), adj: Default::default(), inactive: Default::default(), fcinv: Default::default(), bycell: Default::default(), sched: Default::default() }
    }
}

/// A value's F components in `mregs`' order (`K`: `a`, `b`; `D`: the halves `[0,16)`, `[16,32)`;
/// `AK`: interleaved).
pub fn comps(v: &V) -> Vec<F> {
    match v {
        V::F(x) => vec![*x],
        V::K(x) => vec![x.a, x.b],
        V::D(d) => vec![F::from_bytes(&d[..16]), F::from_bytes(&d[16..])],
        V::Bit(b) => vec![if *b { F::ONE } else { F::ZERO }],
        V::AF(a) => a.clone(),
        V::AK(a) => a.iter().flat_map(|k| [k.a, k.b]).collect(),
        V::N(n) => vec![F::new(*n, 0)],
        V::B(b) => b.chunks(16).map(|c| {
            let mut e = [0u8; 16];
            e[..c.len()].copy_from_slice(c);
            F::from_bytes(&e)
        }).collect(),
    }
}

/// An auxiliary import's components: `felems n` (the bytes as `n` sixteen-byte elements, zero
/// padded), `bits n` (bit `i` of the number as `0`/`1`).
fn aux_comps(v: &V, bits: bool, n: usize) -> Vec<F> {
    if bits {
        let x = match v {
            V::N(x) => *x,
            _ => 0,
        };
        (0..n).map(|i| if (x >> i) & 1 == 1 { F::ONE } else { F::ZERO }).collect()
    } else {
        let b: Vec<u8> = match v {
            V::B(b) => b.clone(),
            V::D(d) => d.to_vec(),
            _ => Vec::new(),
        };
        (0..n).map(|i| {
            let mut e = [0u8; 16];
            for j in 0..16 {
                e[j] = b.get(16 * i + j).copied().unwrap_or(0);
            }
            F::from_bytes(&e)
        })
        .collect()
    }
}

/// A recorded order's entry that sets its cell to zero (an inactive fill's unpinned import; E1b).
pub const ZERO_ENTRY: u32 = u32::MAX;

/// Retry the replay's misses until none solves (the tolerant replay's loop).
fn retry_misses(rw: &Rows, base: u32, miss: &mut Vec<(u32, u32)>, val: &mut [F], known: &mut [bool], solved: &mut usize) {
    while !miss.is_empty() {
        let before = miss.len();
        miss.retain(|&(r, c)| {
            if known[c as usize] {
                return false;
            }
            match try_row(rw, base, r as usize, val, known) {
                Some(_) => {
                    *solved += 1;
                    false
                }
                None => true,
            }
        });
        if miss.len() == before {
            break;
        }
    }
}

/// The import cells of a prototype (E1b): every import register's single-cell forms and every
/// auxiliary import's cells (an inactive slot's are zero unless a template row pins them).
fn inactive_imports(p: &Proto) -> &'static [u32] {
    static T: [std::sync::OnceLock<Vec<u32>>; 2] = [std::sync::OnceLock::new(), std::sync::OnceLock::new()];
    T[p.pi].get_or_init(|| {
        let mut v: Vec<u32> = Vec::new();
        for r in p.regs.iter().filter(|r| r.imp) {
            for &(a, b) in &r.forms {
                if b == a + 1 && !p.fcoefs[a as usize].is_zero() {
                    v.push(p.fcells[a as usize]);
                }
            }
        }
        for ax in &p.aux {
            v.extend_from_slice(&p.fcells[ax.terms.0 as usize..ax.terms.1 as usize]);
        }
        v
    })
}

/// What a slot replays: `Some((registers, index))` for an active slot (the index's selector copy is
/// set), `None` for an inactive sub-slot (every selector copy zero, every import zero).
pub type SlotRun<'a> = Option<(&'a [V], usize)>;

/// The fill's report.
#[derive(Default, Debug)]
pub struct FillStats {
    pub written: usize,
    pub solved: usize,
    pub zeroed: usize,
    pub conflicts: usize,
    pub first_conflicts: Vec<String>,
    pub failed_rows: usize,
    pub first_failed: Vec<u32>,
    pub form_mismatch: usize,
    pub first_form_mismatch: Vec<u32>,
    /// The solve replayed a recorded order.
    pub replayed: bool,
}

/// **The slot fill** in the prototype's region coordinates (`local = cell − π·2^20`): returns the
/// `2^20` cells (`one′` at 0, the selector copies at 1–3).
/// The plan keys per prototype (`Proto::plan`).
pub const PLAN_KEYS: usize = 7;

static EXACT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Replay only a fill's own key's order (`prover setup`: every key records its own).
pub fn set_exact_plans(on: bool) {
    EXACT.store(on, std::sync::atomic::Ordering::Relaxed);
}

pub fn fill(p: &Proto, run: SlotRun, arena: &[F]) -> (Vec<F>, FillStats) {
    fill_part(p, run, false, arena)
}

/// `fill`, for a child that is `partial` (a segment below its kind's cap: its own plan key).
/// E1b: `arena` is the slot's arena₁ (`AR_N` elements: its segment's stream, 16 bytes each; an inactive
/// sub-slot's is the phantom stream, `node::phantom_arena`), written at `AR_A1` before the solve.
pub fn fill_part(p: &Proto, run: SlotRun, partial: bool, arena: &[F]) -> (Vec<F>, FillStats) {
    // the cached inactive fill holds for the arena it was made with (`prover setup`: a zero `vk`)
    if let (None, Some(v)) = (run, p.inactive.get()) {
        if (0..AR_N).all(|e| v[AR_A1 + e] == arena[e]) {
            return (v.clone(), FillStats { replayed: true, ..Default::default() });
        }
    }
    let r = fill_with(p, run, partial, true, arena);
    if r.1.failed_rows == 0 || !r.1.replayed {
        return r;
    }
    // a replayed order that left a solvable cell unknown (another child's data): solve afresh
    fill_with(p, run, partial, false, arena)
}

fn fill_with(p: &Proto, run: SlotRun, partial: bool, replay: bool, arena: &[F]) -> (Vec<F>, FillStats) {
    let t0 = std::time::Instant::now();
    let sp = crate::prof::span(if run.is_some() { "fill.solve" } else { "fill.solve_inactive" });
    let base = (p.pi * SLOT) as u32;
    let mut val = vec![F::ZERO; SLOT];
    let mut known = vec![false; SLOT];
    let mut st = FillStats::default();
    let set = |c: u32, x: F, val: &mut Vec<F>, known: &mut Vec<bool>, st: &mut FillStats, what: &dyn Fn() -> String| {
        let l = (c - base) as usize;
        if known[l] {
            if val[l] != x {
                st.conflicts += 1;
                if st.first_conflicts.len() < 8 {
                    st.first_conflicts.push(what());
                }
            }
        } else {
            known[l] = true;
            val[l] = x;
            st.written += 1;
        }
    };
    set(base, F::ONE, &mut val, &mut known, &mut st, &|| "one".into());
    for i in 0..3 {
        let on = matches!(run, Some((_, ix)) if ix == i);
        set(base + 1 + i as u32, if on { F::ONE } else { F::ZERO }, &mut val, &mut known, &mut st, &|| "sel".into());
    }
    // arena₁ (E1b): the slot's stream; FEL's aliased `dotKF` imports write the same cells again
    assert_eq!(arena.len(), AR_N, "arena₁'s elements");
    for (e, &x) in arena.iter().enumerate() {
        set(base + (AR_A1 + e) as u32, x, &mut val, &mut known, &mut st, &|| format!("arena {e}"));
    }
    // registers (single-cell forms) and auxiliary imports
    let fcinv = p.fcinv();
    for (ri, r) in p.regs.iter().enumerate() {
        let cs: Vec<F> = match run {
            Some((regs, _)) => match regs.get(ri) {
                Some(v) => comps(v),
                None => continue,
            },
            // E1b: an inactive slot's imports are not pre-set: the ungated template rows pin some
            // (the `input` op's cells to `vk ‖ c`, a replay op's output to its template's); the rest
            // are set to zero after the first solve (`inactive_zero`)
            None => continue,
        };
        for (j, &(a, b)) in r.forms.iter().enumerate() {
            if b == a + 1 && j < cs.len() {
                let k = p.fcoefs[a as usize];
                if !k.is_zero() {
                    set(p.fcells[a as usize], cs[j] * fcinv[a as usize], &mut val, &mut known, &mut st, &|| format!("reg r{ri}[{j}]"));
                }
            }
        }
    }
    for ax in &p.aux {
        let cs = match run {
            Some((regs, _)) => aux_comps(&regs[ax.reg as usize], ax.bits, ax.n),
            None => continue,
        };
        for (j, t) in (ax.terms.0..ax.terms.1).enumerate() {
            set(p.fcells[t as usize], cs.get(j).copied().unwrap_or(F::ZERO) * fcinv[t as usize], &mut val, &mut known, &mut st, &|| format!("aux r{}[{j}]", ax.reg));
        }
    }
    // the forward solve: the prototype's recorded order when it replays (the same rows solve the
    // same cells in every slot of the prototype), else the worklist to a fixed point
    let rw = &p.rows;
    let nr = rw.len();
    let key = match run {
        Some((_, ix)) => 1 + ix + 3 * partial as usize,
        None => 0,
    };
    // this key's order, else (an active fill) another index's: the orders mostly agree
    let ckey = if !replay {
        None
    } else if key == 0 || EXACT.load(std::sync::atomic::Ordering::Relaxed) {
        Some(key).filter(|&k| p.plan[k].get().is_some())
    } else {
        // the other variant of this index first
        let twin = if key >= 4 { key - 3 } else { key + 3 };
        [key, twin].into_iter().chain(1..PLAN_KEYS).find(|&k| p.plan[k].get().is_some())
    };
    let mut done = false;
    if let Some(ck) = ckey {
        let pl = p.plan[ck].get().unwrap();
        // tolerant replay: an entry that does not solve its cell here is retried after the rest
        // (another child's data can change which row solves a cell first); the row check below
        // decides (an assignment that satisfies every row agrees with the worklist's on every cell
        // the worklist solves, and leaves the others zero as it does). Pass 13: by the order's
        // levels, in parallel (`replay_levels`), for an active slot (an inactive fill is cached)
        let (mut solved, mut miss) = match (ck > 0 && par_replay()).then(|| p.sched_for(ck)).flatten() {
            Some(sc) => replay_levels(rw, base, pl, sc, &mut val, &mut known),
            None => {
                let mut miss: Vec<(u32, u32)> = Vec::new();
                let mut solved = 0usize;
                for &(r, c) in pl {
                    if r == ZERO_ENTRY {
                        // an inactive fill's zeroed import (E1b), after the misses so far
                        retry_misses(rw, base, &mut miss, &mut val, &mut known, &mut solved);
                        if !known[c as usize] {
                            known[c as usize] = true;
                        }
                        continue;
                    }
                    match try_row(rw, base, r as usize, &mut val, &mut known) {
                        Some(_) => solved += 1,
                        None if known[c as usize] => {}
                        None => miss.push((r, c)),
                    }
                }
                (solved, miss)
            }
        };
        while !miss.is_empty() {
            let before = miss.len();
            miss.retain(|&(r, c)| {
                if known[c as usize] {
                    return false;
                }
                match try_row(rw, base, r as usize, &mut val, &mut known) {
                    Some(_) => {
                        solved += 1;
                        false
                    }
                    None => true,
                }
            });
            if miss.len() == before {
                break;
            }
        }
        st.solved = solved;
        st.replayed = true;
        done = true;
        if std::env::var_os("FLOCK_VERBOSE").is_some() && (solved != pl.len() || !miss.is_empty()) {
            eprintln!("  fill p{} replay: {solved} of {} entries solved, {} unsolved", p.pi, pl.len(), miss.len());
        }
    }
    if !done {
        let mut rec = worklist_with(p, base, &mut val, &mut known);
        if run.is_none() {
            // the imports no row pinned are zero, then the solve goes on from them (recorded as
            // `ZERO_ENTRY` entries, so that a replay zeroes the same imports at the same point)
            let mut z = 0usize;
            for c in inactive_imports(p) {
                let l = (c - base) as usize;
                if !known[l] {
                    known[l] = true;
                    rec.push((ZERO_ENTRY, l as u32));
                    z += 1;
                }
            }
            rec.extend(worklist_unknown(p, base, &mut val, &mut known));
            if std::env::var_os("FLOCK_VERBOSE").is_some() {
                eprintln!("  fill p{} inactive: {z} imports zero", p.pi);
            }
        }
        st.solved = rec.len();
        let _ = p.plan[key].set(rec);
    }
    let t_solve = t0.elapsed().as_secs_f64();
    drop(sp);
    let _sp = crate::prof::span(if run.is_some() { "fill.check" } else { "fill.check_inactive" });
    // check every row; a replay that falls short (another child's data) is completed by the
    // worklist from where it stopped (the deduction's closure is the same) and checked again: pass
    // 12 re-checks only the rows that failed or touch a cell the completion solved (every other
    // row reads the same values as before; `FLOCK_FULL_RECHECK=1` re-checks all, the reference)
    let mut recheck: Option<Vec<u32>> = None;
    for pass in 0..2 {
        st.failed_rows = 0;
        st.first_failed.clear();
        let n_check = recheck.as_ref().map_or(nr, |v| v.len());
        // the rows checked in parallel (pass 13; each chunk's failures in row order, the chunks in
        // order: the same list as the sequential check)
        let bad = crate::par::map_chunks(n_check, 1 << 13, |lo, hi| {
            let mut f: Vec<u32> = Vec::new();
            for q in lo..hi {
                let i = recheck.as_ref().map_or(q, |v| v[q] as usize);
                let [a, b, c] = rw.eval(i, &|x| val[(x - base) as usize]);
                if a * b != c {
                    f.push(i as u32);
                }
            }
            f
        });
        let mut failed: Vec<u32> = Vec::new();
        for i in bad.into_iter().flatten() {
            let i = i as usize;
            {
                st.failed_rows += 1;
                if st.failed_rows <= 2 && std::env::var_os("FLOCK_FILL_DEBUG").is_some() {
                    let [a, b, c] = rw.eval(i, &|x| val[(x - base) as usize]);
                    let rg = rw.rng[i];
                    let mut d = format!("row {} a={a:?} b={b:?} c={c:?}:", rw.idx[i]);
                    for m in 0..3 {
                        for t in rg[m] as usize..rg[m + 1] as usize {
                            let l = (rw.cells[t] - base) as usize;
                            d.push_str(&format!(" [{m}] {}={:x}{:x} k={}", rw.cells[t], val[l].hi, val[l].lo, known[l]));
                        }
                    }
                    eprintln!("{d}");
                }
                if st.first_failed.len() < 12 {
                    st.first_failed.push(rw.idx[i]);
                }
                failed.push(i as u32);
            }
        }
        if pass == 0 && st.failed_rows > 0 && st.replayed {
            let rec = worklist_unknown(p, base, &mut val, &mut known);
            if std::env::var_os("FLOCK_VERBOSE").is_some() {
                eprintln!("  fill p{} replay completed by the worklist: {} more cells ({} rows failed)", p.pi, rec.len(), st.failed_rows);
            }
            st.solved += rec.len();
            if std::env::var_os("FLOCK_FULL_RECHECK").is_none() {
                let (deg, adj) = p.adj.get().expect("the completion built the adjacency");
                let mut mark = vec![false; nr];
                let mut v: Vec<u32> = Vec::new();
                for &i in failed.iter().chain(rec.iter().flat_map(|&(_, u)| adj[deg[u as usize] as usize..deg[u as usize + 1] as usize].iter())) {
                    if !std::mem::replace(&mut mark[i as usize], true) {
                        v.push(i);
                    }
                }
                v.sort_unstable();
                recheck = Some(v);
            }
            continue;
        }
        break;
    }
    st.zeroed = known.iter().filter(|k| !**k).count();
    if let Some((regs, _)) = run {
        for (ri, r) in p.regs.iter().enumerate() {
            let Some(v) = regs.get(ri) else { continue };
            let cs = comps(v);
            for (j, &(a, b)) in r.forms.iter().enumerate() {
                let mut s = F::ZERO;
                for t in a..b {
                    s += p.fcoefs[t as usize] * val[(p.fcells[t as usize] - base) as usize];
                }
                if j < cs.len() && s != cs[j] {
                    st.form_mismatch += 1;
                    if st.first_form_mismatch.len() < 12 {
                        st.first_form_mismatch.push(ri as u32);
                    }
                }
            }
        }
    }
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("  fill p{} solve {t_solve:.3} total {:.3} replayed {}", p.pi, t0.elapsed().as_secs_f64(), st.replayed);
    }
    (val, st)
}

/// Whether `try_row` takes a coefficient's inverse from `Rows::cvinv` (`FLOCK_FILL_INV=1`: always
/// `lin.inv()`, the reference).
fn inv_tab() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FLOCK_FILL_INV").is_none())
}

/// One row with one unknown cell, solved in place: `(a0 + αx)(b0 + βx) = c0 + γx` with one of
/// `α`, `β` zero gives `x·(a0β + αb0 + γ) = a0b0 + c0`. A row whose `A` (or `B`) is known and zero
/// is `C = 0`, solved for `C`'s one unknown whatever the other factor's (an inverse gate at `0`:
/// `0·i = s` gives `s = 0`, S-E12e's `tplShiftSeg`). Returns the solved cell (region-local).
fn try_row(rw: &Rows, base: u32, i: usize, val: &mut [F], known: &mut [bool]) -> Option<usize> {
    try_row_x(rw, base, i, val, known, None)
}

/// `try_row`; a packing row's other solved cells (beyond the returned one) are pushed to `extra`.
fn try_row_x(rw: &Rows, base: u32, i: usize, val: &mut [F], known: &mut [bool], extra: Option<&mut Vec<u32>>) -> Option<usize> {
    assert!(val.len() >= SLOT && known.len() >= SLOT);
    // SAFETY: the cells are region-local (< val.len()) and the slices exclusively borrowed
    unsafe { try_row_p(rw, base, i, None, val.as_mut_ptr(), known.as_mut_ptr(), extra) }
}

/// A coefficient that is one bit `x^j` of the polynomial basis: `j`.
#[inline]
fn one_bit(f: F) -> Option<u32> {
    match (f.lo.count_ones(), f.hi.count_ones()) {
        (1, 0) => Some(f.lo.trailing_zeros()),
        (0, 1) => Some(64 + f.hi.trailing_zeros()),
        _ => None,
    }
}

/// **A packing row** (E1b; IMPC2's bit decompositions `sel·(x + Σ_h x^h b_h) = 0`, unaligned reads):
/// every unknown cell lies in one form `m`, once, with distinct one-bit coefficients `x^{j}`, and the
/// rest of the row is known: `Σ x^{j} b = t` (`t = C/A − B₀` for `m` = B, symmetric for A; `t = A·B − C₀`
/// for C), so `b` is bit `j` of `t` (every bit of `t` must be covered). With `want`, only that cell is
/// written; otherwise all, the first returned and the rest pushed to `extra`.
#[allow(clippy::too_many_arguments)]
unsafe fn try_pack(rw: &Rows, base: u32, i: usize, want: Option<usize>, val: *mut F, known: *mut bool, kn: [F; 3], extra: Option<&mut Vec<u32>>) -> Option<usize> {
    let rg = rw.rng[i];
    let mut m_unk = usize::MAX;
    for k in 0..3 {
        for t in rg[k] as usize..rg[k + 1] as usize {
            if !*known.add((rw.cells[t] - base) as usize) {
                if m_unk != usize::MAX && m_unk != k {
                    return None;
                }
                m_unk = k;
            }
        }
    }
    let t = match m_unk {
        1 if !kn[0].is_zero() => kn[2] * kn[0].inv() + kn[1],
        0 if !kn[1].is_zero() => kn[2] * kn[1].inv() + kn[0],
        2 => kn[0] * kn[1] + kn[2],
        _ => return None,
    };
    let tv = (t.hi as u128) << 64 | t.lo as u128;
    let mut seen = 0u128;
    let k = m_unk;
    for q in rg[k] as usize..rg[k + 1] as usize {
        let l = (rw.cells[q] - base) as usize;
        if *known.add(l) {
            continue;
        }
        let j = one_bit(rw.coef(q))?;
        if seen >> j & 1 == 1 {
            return None;
        }
        seen |= 1u128 << j;
    }
    if tv & !seen != 0 {
        return None;
    }
    // the cells are distinct (a repeated cell would repeat a bit or have two coefficients)
    let mut first = None;
    let mut extra = extra;
    for q in rg[k] as usize..rg[k + 1] as usize {
        let l = (rw.cells[q] - base) as usize;
        if *known.add(l) {
            continue;
        }
        if want.is_some_and(|w| w != l) {
            continue;
        }
        let j = one_bit(rw.coef(q)).unwrap();
        *val.add(l) = F::new((tv >> j & 1) as u64, 0);
        *known.add(l) = true;
        if first.is_none() {
            first = Some(l);
        } else if let Some(e) = extra.as_deref_mut() {
            e.push(l as u32);
        }
    }
    first
}

/// `try_row` on pointers; with `want`, only a solve of cell `want` is written (else `None`).
/// SAFETY: `val`, `known` point at `SLOT` cells, and no other thread writes row `i`'s cells or
/// accesses the solved cell meanwhile.
unsafe fn try_row_p(rw: &Rows, base: u32, i: usize, want: Option<usize>, val: *mut F, known: *mut bool, extra: Option<&mut Vec<u32>>) -> Option<usize> {
    let rg = rw.rng[i];
    let mut unk: [Option<usize>; 3] = [None; 3];
    let mut multi = [false; 3];
    let mut kn = [F::ZERO; 3];
    let mut co = [F::ZERO; 3];
    // C's unknown terms: how many, and the last one's coefficient index (one term: `co[2]` is that
    // coefficient, whose inverse `cvinv` holds; pass 13)
    let (mut nc, mut ic) = (0usize, ONE_IX);
    for k in 0..3 {
        for t in rg[k] as usize..rg[k + 1] as usize {
            let l = (rw.cells[t] - base) as usize;
            if *known.add(l) {
                kn[k] += rw.cmul(t, *val.add(l));
            } else {
                match unk[k] {
                    None => unk[k] = Some(l),
                    Some(u) if u == l => {}
                    _ => multi[k] = true,
                }
                co[k] += rw.coef(t);
                if k == 2 {
                    nc += 1;
                    ic = rw.coefs[t];
                }
            }
        }
    }
    // `lin = co[2]` with one term: its inverse from the table (`lin.inv()` is the reference)
    let cinv = (nc == 1 && inv_tab()).then(|| rw.inv_ix(ic));
    let solve = |u: usize, lin: F, inv: Option<F>, rhs: F, val: *mut F, known: *mut bool| -> Option<usize> {
        if lin.is_zero() || want.is_some_and(|w| w != u) {
            return None;
        }
        *val.add(u) = if lin == F::ONE { rhs } else { rhs * inv.unwrap_or_else(|| lin.inv()) };
        *known.add(u) = true;
        Some(u)
    };
    // the distinct unknown cells of the three forms, sorted (no allocation: at most three)
    let mut us = unk;
    us.sort_unstable();
    let (mut single, mut distinct) = (None, 0);
    for &x in us.iter().flatten() {
        if single != Some(x) {
            distinct += 1;
            single = Some(x);
        }
    }
    if distinct == 1 && !multi.iter().any(|&m| m) {
        if !co[0].is_zero() && !co[1].is_zero() {
            return None;
        }
        let only_c = co[0].is_zero() && co[1].is_zero();
        return solve(single.unwrap(), kn[0] * co[1] + co[0] * kn[1] + co[2], cinv.filter(|_| only_c), kn[0] * kn[1] + kn[2], val, known);
    }
    // a known zero factor: the row is `C = 0`
    let zero_factor = (unk[0].is_none() && kn[0].is_zero()) || (unk[1].is_none() && kn[1].is_zero());
    match (zero_factor, unk[2], multi[2]) {
        (true, Some(u), false) => solve(u, co[2], cinv, kn[2], val, known),
        _ if distinct > 1 || multi.iter().any(|&m| m) => try_pack(rw, base, i, want, val, known, kn, extra),
        _ => None,
    }
}

/// **Slot 0's replay locals** (E1b; prototype 0's `spare` rows, REPF/C1b §5.5: the templates' gates in
/// order): the frame is slot 0's fill (every cell known), the locals (`2^20` cells) are solved by the
/// worklist from the rows in order; every row is checked. Returns the locals and a report (`solved`,
/// `failed_rows`, `zeroed`: locals no row determines).
pub fn spare_fill(p: &Proto, frame: &[F]) -> (Vec<F>, FillStats) {
    static ADJ: std::sync::OnceLock<(Vec<u32>, Vec<u32>)> = std::sync::OnceLock::new();
    let _sp = crate::prof::span("fill.spare");
    let rw = &p.spare;
    let n = 2 * SLOT;
    let mut st = FillStats::default();
    if rw.len() == 0 {
        return (Vec::new(), st);
    }
    let mut val = vec![F::ZERO; n];
    val[..SLOT].copy_from_slice(&frame[..SLOT]);
    let mut known = vec![false; n];
    known[..SLOT].fill(true);
    let (deg, adj) = ADJ.get_or_init(|| adjacency_n(rw, 0, n));
    st.solved = worklist(rw, 0, deg, adj, &mut val, &mut known).len();
    let bad = crate::par::map_chunks(rw.len(), 1 << 13, |lo, hi| {
        (lo..hi).filter(|&i| {
            let [a, b, c] = rw.eval(i, &|x| val[x as usize]);
            a * b != c
        })
        .map(|i| rw.idx[i])
        .collect::<Vec<u32>>()
    });
    for b in bad.into_iter().flatten() {
        st.failed_rows += 1;
        if st.first_failed.len() < 12 {
            st.first_failed.push(b);
        }
    }
    st.zeroed = known[SLOT..].iter().filter(|k| !**k).count();
    (val.split_off(SLOT), st)
}

/// Build the prototype's adjacency now (before a request).
pub fn warm_adjacency(p: &Proto) {
    let _ = p.adj.get_or_init(|| adjacency(&p.rows, (p.pi * SLOT) as u32));
    let _ = p.fcinv();
}

/// `worklist` with the prototype's cached adjacency.
fn worklist_with(p: &Proto, base: u32, val: &mut [F], known: &mut [bool]) -> Vec<(u32, u32)> {
    let (deg, adj) = p.adj.get_or_init(|| adjacency(&p.rows, base));
    worklist(&p.rows, base, deg, adj, val, known)
}

/// The completion of a short replay (pass 12; `worklist_with` is the reference,
/// `FLOCK_FULL_RECHECK=1` uses it): the worklist started from the rows that touch an unknown cell,
/// in row order. A row with no unknown cell solves nothing (`try_row`), and every row the full
/// worklist would reach later is pushed here too when one of its cells is solved, so the closure
/// (the solved cells and their values) is the same.
fn worklist_unknown(p: &Proto, base: u32, val: &mut [F], known: &mut [bool]) -> Vec<(u32, u32)> {
    let (deg, adj) = p.adj.get_or_init(|| adjacency(&p.rows, base));
    if std::env::var_os("FLOCK_FULL_RECHECK").is_some() {
        return worklist(&p.rows, base, deg, adj, val, known);
    }
    let nr = p.rows.len();
    let mut queued = vec![false; nr];
    let mut start: Vec<u32> = Vec::new();
    for l in 0..SLOT {
        if !known[l] {
            for &r in &adj[deg[l] as usize..deg[l + 1] as usize] {
                if !std::mem::replace(&mut queued[r as usize], true) {
                    start.push(r);
                }
            }
        }
    }
    start.sort_unstable_by(|a, b| b.cmp(a));
    worklist_q(&p.rows, base, deg, adj, val, known, queued, start)
}

/// The cell → rows adjacency (CSR: `deg` offsets per region-local cell, `adj` the rows).
fn adjacency(rw: &Rows, base: u32) -> (Vec<u32>, Vec<u32>) {
    adjacency_n(rw, base, SLOT)
}

/// `adjacency` over `n` cells.
fn adjacency_n(rw: &Rows, base: u32, n: usize) -> (Vec<u32>, Vec<u32>) {
    let nr = rw.len();
    let mut deg = vec![0u32; n + 1];
    for &c in &rw.cells {
        deg[(c - base) as usize + 1] += 1;
    }
    for i in 0..n {
        deg[i + 1] += deg[i];
    }
    let mut adj = vec![0u32; rw.cells.len()];
    let mut fillp = deg.clone();
    for i in 0..nr {
        let rg = rw.rng[i];
        for t in rg[0]..rg[3] {
            let l = (rw.cells[t as usize] - base) as usize;
            adj[fillp[l] as usize] = i as u32;
            fillp[l] += 1;
        }
    }
    drop(fillp);
    (deg, adj)
}

/// The worklist solve to a fixed point from the current state; returns the order `(row, cell)`.
fn worklist(rw: &Rows, base: u32, deg: &[u32], adj: &[u32], val: &mut [F], known: &mut [bool]) -> Vec<(u32, u32)> {
    let nr = rw.len();
    worklist_q(rw, base, deg, adj, val, known, vec![true; nr], (0..nr as u32).rev().collect())
}

/// The worklist loop from the queue `work` (popped from the end), `queued` its membership.
#[allow(clippy::too_many_arguments)]
fn worklist_q(rw: &Rows, base: u32, deg: &[u32], adj: &[u32], val: &mut [F], known: &mut [bool], mut queued: Vec<bool>, mut work: Vec<u32>) -> Vec<(u32, u32)> {
    let mut rec = Vec::new();
    let mut ex: Vec<u32> = Vec::new();
    while let Some(i) = work.pop() {
        queued[i as usize] = false;
        let Some(u) = try_row_x(rw, base, i as usize, val, known, Some(&mut ex)) else { continue };
        ex.push(u as u32);
        for u in ex.drain(..).map(|u| u as usize) {
            rec.push((i, u as u32));
            for &r in &adj[deg[u] as usize..deg[u + 1] as usize] {
                if !queued[r as usize] {
                    queued[r as usize] = true;
                    work.push(r);
                }
            }
        }
    }
    rec
}

/// The dump directory (`FLOCK_NODE_DUMP`, else `logs/E1b/nodedump` above the working directory; E1: rev44 HEAD `e464756`; pass 13:
/// B0's row layout, was `logs/S-E13a/nodedump`)
/// and the prototype programs' directory (`FLOCK_PROTO_DIR`, else the dump directory).
pub fn find_dirs() -> Option<(std::path::PathBuf, std::path::PathBuf)> {
    let d = match std::env::var_os("FLOCK_NODE_DUMP") {
        Some(p) => std::path::PathBuf::from(p),
        None => crate::kat::find_up("logs/E1b/nodedump/mrows-p0.txt")?.parent()?.to_path_buf(),
    };
    let p = std::env::var_os("FLOCK_PROTO_DIR").map(std::path::PathBuf::from).unwrap_or_else(|| d.clone());
    Some((d, p))
}

/// The recorded solve orders of both prototypes (`Proto::plan`), as `prover setup` stores them:
/// `FLPLAN02`, the node data's tag, then per prototype and key a length (`u32::MAX`: none) and the
/// `(row, cell)` pairs (little-endian `u32`).
pub fn save_plans(protos: &[Proto; 2], tag: &[u8; 32]) -> Vec<u8> {
    let mut out = b"FLPLAN02".to_vec();
    out.extend_from_slice(tag);
    for p in protos.iter() {
        for o in &p.plan {
            match o.get() {
                None => out.extend_from_slice(&u32::MAX.to_le_bytes()),
                Some(v) => {
                    out.extend_from_slice(&(v.len() as u32).to_le_bytes());
                    for &(r, c) in v {
                        out.extend_from_slice(&r.to_le_bytes());
                        out.extend_from_slice(&c.to_le_bytes());
                    }
                }
            }
        }
    }
    out
}

/// Load `save_plans`' bytes into the prototypes' unset orders; `false` (nothing loaded) when the
/// bytes are not plans of this node data. A loaded order is only a guess: `fill` checks every row
/// and solves afresh when a replay leaves one unsatisfied.
pub fn load_plans(protos: &[Proto; 2], tag: &[u8; 32], b: &[u8]) -> bool {
    if b.len() < 40 || &b[..8] != b"FLPLAN02" || &b[8..40] != tag {
        return false;
    }
    let mut parsed: Vec<Option<Vec<(u32, u32)>>> = Vec::new();
    let mut i = 40;
    let rd = |i: &mut usize| -> Option<u32> {
        let x = b.get(*i..*i + 4)?;
        *i += 4;
        Some(u32::from_le_bytes(x.try_into().unwrap()))
    };
    for _ in 0..2 * PLAN_KEYS {
        let Some(n) = rd(&mut i) else { return false };
        if n == u32::MAX {
            parsed.push(None);
            continue;
        }
        let n = n as usize;
        if b.len() < i + 8 * n {
            return false;
        }
        let v: Vec<(u32, u32)> = b[i..i + 8 * n]
            .chunks_exact(8)
            .map(|c| (u32::from_le_bytes(c[..4].try_into().unwrap()), u32::from_le_bytes(c[4..].try_into().unwrap())))
            .collect();
        i += 8 * n;
        parsed.push(Some(v));
    }
    if i != b.len() {
        return false;
    }
    for (j, v) in parsed.into_iter().enumerate() {
        if let Some(v) = v {
            let _ = protos[j / PLAN_KEYS].plan[j % PLAN_KEYS].set(v);
        }
    }
    true
}

/// Every recorded order's level schedule (built here if not yet), as `prover setup` stores them
/// (pass 13): `FLSCHD01`, the node data's tag, then per prototype and key the order's length
/// (`u32::MAX`: no order), the level count and the arrays `lv`, `ent` (little-endian `u32`).
pub fn save_scheds(protos: &[Proto; 2], tag: &[u8; 32]) -> Vec<u8> {
    let mut out = b"FLSCHD01".to_vec();
    out.extend_from_slice(tag);
    let mut put = |x: u32| out.extend_from_slice(&x.to_le_bytes());
    for p in protos.iter() {
        for k in 0..PLAN_KEYS {
            match (k > 0).then(|| p.sched_for(k)).flatten() {
                None => put(u32::MAX),
                Some(sc) => {
                    put(sc.ent.len() as u32);
                    put(sc.lv.len() as u32);
                    sc.lv.iter().chain(sc.ent.iter()).for_each(|&x| put(x));
                }
            }
        }
    }
    out
}

/// Load `save_scheds`' bytes for the orders loaded (`load_plans`, same tag): a schedule is taken
/// only when its order is set and of its length, its levels ascend from 0 to that length and its
/// entries are a permutation of the order's positions. `false` when the bytes are not this data's.
pub fn load_scheds(protos: &[Proto; 2], tag: &[u8; 32], b: &[u8]) -> bool {
    if b.len() < 40 || &b[..8] != b"FLSCHD01" || &b[8..40] != tag {
        return false;
    }
    let mut i: usize = 40;
    let mut rd = |n: usize| -> Option<Vec<u32>> {
        let x = b.get(i..i.checked_add(n.checked_mul(4)?)?)?;
        i += 4 * n;
        Some(x.chunks_exact(4).map(|c| u32::from_le_bytes(c.try_into().unwrap())).collect())
    };
    let mut got: Vec<(usize, usize, Sched)> = Vec::new();
    for p in 0..2 {
        for k in 0..PLAN_KEYS {
            let Some(h) = rd(1) else { return false };
            if h[0] == u32::MAX {
                continue;
            }
            let n = h[0] as usize;
            let Some(nl) = rd(1) else { return false };
            let (Some(lv), Some(ent)) = (rd(nl[0] as usize), rd(n)) else { return false };
            let len_ok = protos[p].plan[k].get().is_some_and(|pl| pl.len() == n);
            let lv_ok = lv.first() == Some(&0) && lv.last() == Some(&(n as u32)) && lv.windows(2).all(|w| w[0] <= w[1]);
            let mut seen = vec![false; n];
            let perm_ok = ent.iter().all(|&q| (q as usize) < n && !std::mem::replace(&mut seen[q as usize], true));
            if len_ok && lv_ok && perm_ok {
                got.push((p, k, Sched { ent, lv }));
            }
        }
    }
    if i != b.len() {
        return false;
    }
    for (p, k, sc) in got {
        let _ = protos[p].sched[k].set(sc);
    }
    true
}

#[cfg(test)]
mod pass11_tests {
    use super::*;

    /// `save_plans` / `load_plans` round trip; a wrong tag or a cut file loads nothing.
    #[test]
    fn plans_round_trip() {
        let mk = || Proto { pi: 0, rows: Rows::new(), regs: vec![], aux: vec![], fcells: vec![], fcoefs: vec![], spare: Rows::new(), plan: Default::default(), adj: Default::default(), inactive: Default::default(), fcinv: Default::default(), bycell: Default::default(), sched: Default::default() };
        let a = [mk(), mk()];
        let _ = a[0].plan[0].set(vec![(1, 2), (3, 4)]);
        let _ = a[1].plan[2].set(vec![(5, 6)]);
        let tag = [7u8; 32];
        let b = save_plans(&a, &tag);
        let c = [mk(), mk()];
        assert!(!load_plans(&c, &[8u8; 32], &b));
        assert!(!load_plans(&c, &tag, &b[..b.len() - 1]));
        assert!(c.iter().all(|p| p.plan.iter().all(|o| o.get().is_none())));
        assert!(load_plans(&c, &tag, &b));
        assert_eq!(c[0].plan[0].get(), Some(&vec![(1, 2), (3, 4)]));
        assert_eq!(c[1].plan[2].get(), Some(&vec![(5, 6)]));
        assert!(c[0].plan[1].get().is_none() && c[1].plan[0].get().is_none());
    }
    /// (+) A chain of rows gets one level per link and independent rows share a level; the
    /// schedules round-trip through `save_scheds`/`load_scheds`; (−) a wrong tag, a cut file and a
    /// schedule that is not a permutation load nothing.
    #[test]
    fn schedules_levels_and_round_trip() {
        let mk = || Proto { pi: 0, rows: Rows::new(), regs: vec![], aux: vec![], fcells: vec![], fcoefs: vec![], spare: Rows::new(), plan: Default::default(), adj: Default::default(), inactive: Default::default(), fcinv: Default::default(), bycell: Default::default(), sched: Default::default() };
        let mut a = [mk(), mk()];
        // rows `x_{i+1} = x_i · 1` for cells 1 → 2 → 3, and `x_5 = x_4 · 1` beside them
        for (i, (x, y)) in [(1u32, 2u32), (2, 3), (4, 5)].into_iter().enumerate() {
            a[0].rows.push_line(&format!("{i} | {x}:01000000000000000000000000000000 | 0:01000000000000000000000000000000 | {y}:01000000000000000000000000000000"));
        }
        a[0].rows.done();
        let _ = a[0].plan[1].set(vec![(0, 2), (2, 5), (1, 3)]);
        let sc = a[0].sched_for(1).unwrap();
        assert_eq!((sc.lv.clone(), sc.ent.clone()), (vec![0, 2, 3], vec![0, 1, 2]));
        let tag = [3u8; 32];
        let b = save_scheds(&a, &tag);
        let c = [mk(), mk()];
        let _ = c[0].plan[1].set(vec![(0, 2), (2, 5), (1, 3)]);
        assert!(!load_scheds(&c, &[4u8; 32], &b) && !load_scheds(&c, &tag, &b[..b.len() - 4]));
        let mut bad = b.clone();
        // prototype 0, key 1's last `ent` entry (after key 0's marker, n, the level count, lv, ent)
        bad[40 + 4 * 8..40 + 4 * 9].copy_from_slice(&0u32.to_le_bytes()); // ent = [0, 1, 0]
        assert!(load_scheds(&c, &tag, &bad) && c[0].sched[1].get().is_none());
        assert!(load_scheds(&c, &tag, &b));
        let l = c[0].sched[1].get().unwrap();
        assert_eq!((l.lv.clone(), l.ent.clone()), (vec![0, 2, 3], vec![0, 1, 2]));
    }
}

/// An inactive fill's cells as bytes (`prover setup`'s `inactive-p{π}.bin`).
pub fn save_inactive(v: &[F]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_bytes()).collect()
}

/// Load `save_inactive`'s bytes as the prototype's inactive fill (`false`: not one).
pub fn load_inactive(p: &Proto, b: &[u8]) -> bool {
    if b.len() != 16 * SLOT {
        return false;
    }
    let _ = p.inactive.set(b.chunks_exact(16).map(F::from_bytes).collect());
    true
}

#[cfg(test)]
mod e1b_tests {
    use super::*;

    /// (+) A packing row `one·(x + Σ_h x^h b_h) = 0` solves the bits of a known `x` (worklist and a
    /// replay with `want`); (−) an `x` with a bit no unknown covers solves nothing.
    #[test]
    fn packing_rows() {
        let mut rw = Rows::new();
        let one = [(0u32, F::ONE)];
        let b: Vec<(u32, F)> = std::iter::once((1u32, F::ONE)).chain((0..4).map(|h| (2 + h, F::new(1 << h, 0)))).collect();
        rw.push_row(0, [&one, &b, &[]]);
        rw.done();
        for (x, want) in [(0b1011u64, Some(vec![1, 1, 0, 1])), (0b1_0000, None)] {
            let mut val = vec![F::ZERO; SLOT];
            let mut known = vec![false; SLOT];
            val[0] = F::ONE;
            val[1] = F::new(x, 0);
            known[0] = true;
            known[1] = true;
            let mut ex = Vec::new();
            let r = try_row_x(&rw, 0, 0, &mut val, &mut known, Some(&mut ex));
            match want {
                Some(bits) => {
                    assert_eq!(r, Some(2));
                    assert_eq!(ex, vec![3, 4, 5]);
                    assert_eq!((2..6).map(|c| val[c].lo).collect::<Vec<_>>(), bits);
                    let [a, bb, c] = rw.eval(0, &|q| val[q as usize]);
                    assert_eq!(a * bb, c);
                }
                None => assert_eq!(r, None),
            }
        }
        // a replay entry writes its own cell only
        let mut val = vec![F::ZERO; SLOT];
        let mut known = vec![false; SLOT];
        val[0] = F::ONE;
        val[1] = F::new(0b0110, 0);
        known[0] = true;
        known[1] = true;
        let r = unsafe { try_row_p(&rw, 0, 0, Some(3), val.as_mut_ptr(), known.as_mut_ptr(), None) };
        assert_eq!(r, Some(3));
        assert!(known[3] && !known[2] && !known[4] && val[3] == F::ONE);
    }
}
