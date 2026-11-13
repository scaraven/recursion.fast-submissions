//! B1-IE (lvm2 roll 8): the typed layout `Lay` of the B program (Lean `LvmTypedLayout.Lay`), read from B1-K's
//! text dump (`LvmTypedLay.layDump`), and what it gives the prover:
//! - the word of every cell (`Lay.wordK`, `Lay.wordE`) and the slot of every constraint row (`Lay.slot`, `auxSlot`);
//! - **the matrices' entries `ents Q lay`** (`LvmWiring.instEnts` and `auxRowEnts`, entry for entry: `muladd`
//!   `A a, B b, D d, W res`; `lin k k'` `D (a + k·b + k'·1), W res`; `assert0` `A gate, B a`; `fixmul`
//!   `D (F(j)·a + d), W res`; an operand is `cellEnts`: one word for `K` (a constant cell: the word `1` with weight
//!   `w·value`), three limbs with weights `w, w·y, w·y²` for `E`, a virtual `loadE` cell through its operands' words),
//!   as the prover's [`Typed`] (CSR/CSC, tags per template row for the class kernels);
//! - the results-only witness `z` on the committed region (`memOf`'s inverse on the run).
//!
//! `Φ_Q` is the multilinear extension of these entries in `2 + 20 + 21` variables, `o` lowest, then `x`, then `y`
//! (`LvmWiring.PhiQF`); V evaluates it by B1-K's `PhiQC`, so the prover's entries must be the Lean's (their sum per
//! index: zero-weight entries may be dropped).

use std::collections::HashMap;

use crate::lv::primitives::field::{F64, F192};
use crate::lvm::loopir::{Addr, Compiled, Op, Ty, unflat};
use crate::lvm::typed::{Ent, MA, MB, MD, MW, Typed};

/// `xVars`, `yVars` (B-DES §1.1).
pub const X_VARS: usize = 20;
pub const Y_VARS: usize = 21;
const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum YSrc {
    Com,
    Sflat,
    Pub,
    Sigma,
    Ks,
    Qlt,
    One,
}

#[derive(Clone, Debug)]
pub struct YReg {
    pub base: usize,
    pub log: usize,
    pub src: YSrc,
}

/// Cells `[lo, lo + n)` of memory `ty` in cell order, limb `m` of cell `c` at word `bases[m] + (c − lo)`.
#[derive(Clone, Debug)]
pub struct DReg {
    pub ty: Ty,
    pub lo: usize,
    pub n: usize,
    pub bases: Vec<usize>,
    /// Lane-split (B1-IX v3, `DReg.lanes`/`laneBases`): cell `lo + R·x + l` at word `laneBases[l] + x`.
    pub lanes: Option<(usize, Vec<usize>)>,
}

impl DReg {
    /// `DReg.word`: limb `m` of cell `c` (inside the region).
    fn word(&self, c: usize, m: usize) -> usize {
        match &self.lanes {
            Some((r, lb)) => lb[(c - self.lo) % r] + (c - self.lo) / r,
            None => self.bases.get(m).copied().unwrap_or(0) + (c - self.lo),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CSrc {
    Slot(usize),
    Load,
    Alias(Vec<usize>),
}

#[derive(Clone, Debug)]
pub struct RChunk {
    pub s0: usize,
    pub n: usize,
    pub bases: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
pub struct BLay {
    pub dims: Vec<usize>,
    pub st_k: usize,
    pub st_e: usize,
    pub tw_k: usize,
    pub tw_e: usize,
    pub src_k: Vec<CSrc>,
    pub src_e: Vec<CSrc>,
    pub ch_k: Vec<RChunk>,
    pub ch_e: Vec<RChunk>,
    pub cr: Vec<Option<usize>>,
}

impl BLay {
    fn l(&self) -> usize {
        self.dims.iter().sum()
    }
    /// `BLay.slotWord`.
    fn slot_word(&self, ty: Ty, s: usize, jf: usize, m: usize) -> usize {
        let ch = if ty == Ty::K { &self.ch_k } else { &self.ch_e };
        match ch.iter().find(|c| c.s0 <= s && s < c.s0 + c.n) {
            Some(c) => c.bases.get(m).copied().unwrap_or(0) + ((s - c.s0) << self.l()) + jf,
            None => 0,
        }
    }
}

#[derive(Clone, Debug)]
pub enum AOp {
    Word(usize, usize),
    Cell(Addr),
    One,
}

#[derive(Clone, Debug)]
pub struct ABlk {
    pub l: usize,
    pub rows: Vec<Vec<(u8, AOp, F192)>>,
}

#[derive(Clone, Copy, Debug)]
pub struct XChunk {
    pub blk: usize,
    pub l: usize,
    pub r0: usize,
    pub n: usize,
    pub base: usize,
}

/// **The typed layout** (Lean `Lay`).
#[derive(Clone, Debug)]
pub struct TLay {
    pub n_in_k: usize,
    pub n_in_e: usize,
    pub one: usize,
    pub yregs: Vec<YReg>,
    pub inp: Vec<DReg>,
    pub dense: Vec<DReg>,
    /// The constant cells `[lo, lo + n)` (values: the inputs' at those cells, `qltCst`).
    pub cst: Vec<(usize, usize)>,
    pub blocks: Vec<BLay>,
    pub xs: Vec<XChunk>,
    pub aux: Vec<ABlk>,
}

fn nums(it: &mut dyn Iterator<Item = &str>) -> Vec<usize> {
    it.map(|t| t.parse().unwrap_or_else(|_| panic!("layDump: number {t:?}"))).collect()
}

fn ysrc(s: &str) -> YSrc {
    match s.rsplit('.').next().unwrap() {
        "com" => YSrc::Com,
        "sflat" => YSrc::Sflat,
        "pub" => YSrc::Pub,
        "sigma" => YSrc::Sigma,
        "ks" => YSrc::Ks,
        "qlt" => YSrc::Qlt,
        "one" => YSrc::One,
        x => panic!("layDump: region source {x:?}"),
    }
}

fn ty_of(s: &str) -> Ty {
    match s {
        "K" => Ty::K,
        "E" => Ty::E,
        _ => panic!("layDump: type {s:?}"),
    }
}

fn csrcs(rest: &str) -> Vec<CSrc> {
    let rest = rest.trim();
    if rest.is_empty() {
        return Vec::new();
    }
    rest.split(" ; ")
        .map(|it| {
            let mut t = it.split_whitespace();
            match t.next() {
                Some("s") => CSrc::Slot(t.next().unwrap().parse().unwrap()),
                Some("l") => CSrc::Load,
                Some("a") => CSrc::Alias(nums(&mut t)),
                x => panic!("layDump: a writer's source {x:?}"),
            }
        })
        .collect()
}

impl TLay {
    /// Parse `layDump` (B1-K, `LvmTypedLay.layDump`).
    pub fn parse(text: &str) -> TLay {
        let mut lay = TLay { n_in_k: 0, n_in_e: 0, one: 0, yregs: Vec::new(), inp: Vec::new(), dense: Vec::new(), cst: Vec::new(), blocks: Vec::new(), xs: Vec::new(), aux: Vec::new() };
        let mut cur_aux: Option<ABlk> = None;
        let mut cur_row: Vec<(u8, AOp, F192)> = Vec::new();
        for line in text.lines() {
            let (tag, rest) = line.split_once(' ').unwrap_or((line, ""));
            match tag {
                "N" => {
                    let v = nums(&mut rest.split_whitespace());
                    (lay.n_in_k, lay.n_in_e, lay.one) = (v[0], v[1], v[2]);
                }
                "Y" => {
                    let t: Vec<&str> = rest.split_whitespace().collect();
                    lay.yregs.push(YReg { base: t[0].parse().unwrap(), log: t[1].parse().unwrap(), src: ysrc(t[2]) });
                }
                "I" => {
                    let (a, lanes) = match rest.split_once('|') {
                        Some((a, b)) => {
                            let mut t = b.split_whitespace();
                            assert_eq!(t.next(), Some("L"), "layDump: I … | L R laneBases…");
                            let v = nums(&mut t);
                            assert_eq!(v.len(), v[0] + 1, "layDump: one lane base per lane");
                            (a, Some((v[0], v[1..].to_vec())))
                        }
                        None => (rest, None),
                    };
                    let v = nums(&mut a.split_whitespace());
                    let ty = if v.len() == 3 { Ty::K } else { assert_eq!(v.len(), 5, "layDump: I"); Ty::E };
                    lay.inp.push(DReg { ty, lo: v[0], n: v[1], bases: v[2..].to_vec(), lanes });
                }
                "D" => {
                    let mut t = rest.split_whitespace();
                    let ty = ty_of(t.next().unwrap());
                    let v = nums(&mut t);
                    lay.dense.push(DReg { ty, lo: v[0], n: v[1], bases: v[2..].to_vec(), lanes: None });
                }
                "C" => {
                    let v = nums(&mut rest.split_whitespace());
                    lay.cst.push((v[0], v[1]));
                }
                "B" => {
                    let (a, b) = rest.split_once('|').expect("layDump: B … | …");
                    let a = nums(&mut a.split_whitespace());
                    assert_eq!(a[0], lay.blocks.len(), "layDump: blocks in order");
                    let b = nums(&mut b.split_whitespace());
                    lay.blocks.push(BLay { dims: a[1..].to_vec(), st_k: b[0], st_e: b[1], tw_k: b[2], tw_e: b[3], ..Default::default() });
                }
                "SK" => lay.blocks.last_mut().unwrap().src_k = csrcs(rest),
                "SE" => lay.blocks.last_mut().unwrap().src_e = csrcs(rest),
                "HK" | "HE" => {
                    let v = nums(&mut rest.split_whitespace());
                    let c = RChunk { s0: v[0], n: v[1], bases: v[2..].to_vec() };
                    let b = lay.blocks.last_mut().unwrap();
                    if tag == "HK" { b.ch_k.push(c) } else { b.ch_e.push(c) }
                }
                "R" => {
                    lay.blocks.last_mut().unwrap().cr = nums(&mut rest.split_whitespace()).into_iter().map(|r| (r != 999_999_999).then_some(r)).collect();
                }
                "X" => {
                    let v = nums(&mut rest.split_whitespace());
                    lay.xs.push(XChunk { blk: v[0], l: v[1], r0: v[2], n: v[3], base: v[4] });
                }
                "A" => {
                    if let Some(a) = cur_aux.take() {
                        lay.aux.push(a);
                    }
                    let v = nums(&mut rest.split_whitespace());
                    assert_eq!(v[0], lay.aux.len(), "layDump: aux blocks in order");
                    cur_aux = Some(ABlk { l: v[1], rows: Vec::with_capacity(v[2]) });
                }
                "O" => {
                    let t: Vec<&str> = rest.split_whitespace().collect();
                    let n = t.len();
                    let w = F192::new(t[n - 3].parse().unwrap(), t[n - 2].parse().unwrap(), t[n - 1].parse().unwrap());
                    let o: u8 = t[0].parse().unwrap();
                    let a = match t[1] {
                        "w" => AOp::Word(t[2].parse().unwrap(), t[3].parse().unwrap()),
                        "c" => AOp::Cell(Addr { ty: ty_of(t[2]), base: t[3].parse().unwrap(), strides: t[4..n - 3].iter().map(|x| x.parse().unwrap()).collect() }),
                        "1" => AOp::One,
                        x => panic!("layDump: aux operand {x:?}"),
                    };
                    cur_row.push((o, a, w));
                }
                "." => cur_aux.as_mut().expect("layDump: a row inside an aux block").rows.push(std::mem::take(&mut cur_row)),
                "" => {}
                x => panic!("layDump: line tag {x:?}"),
            }
        }
        if let Some(a) = cur_aux.take() {
            lay.aux.push(a);
        }
        lay
    }

    /// `Lay.dreg?` then `wordD`: limb `m` of cell `n` in its dense or input region.
    fn word_d(&self, ty: Ty, n: usize, m: usize) -> Option<usize> {
        self.dense.iter().chain(&self.inp).find(|d| d.ty == ty && d.lo <= n && n < d.lo + d.n).map(|d| d.word(n, m))
    }

    /// The constant cell `n`'s index into its run's values, if it is one (`Lay.cst?`).
    pub fn is_cst(&self, n: usize) -> bool {
        self.cst.iter().any(|&(lo, len)| lo <= n && n < lo + len)
    }

    /// The end of the word space's regions (the used prefix of `y`).
    pub fn y_end(&self) -> usize {
        self.yregs.iter().map(|r| r.base + (1 << r.log)).max().unwrap_or(0)
    }

    /// The regions of `src`.
    pub fn regs_of(&self, src: YSrc) -> impl Iterator<Item = &YReg> {
        self.yregs.iter().filter(move |r| r.src == src)
    }

    /// `Lay.slotR b r jf` (`None`: no chunk holds rank `r`).
    fn slot_r(&self, xi: &HashMap<usize, Vec<usize>>, b: usize, r: usize, jf: usize) -> Option<usize> {
        let c = xi.get(&b)?.iter().map(|&i| &self.xs[i]).find(|c| c.r0 <= r && r < c.r0 + c.n)?;
        Some(c.base + ((r - c.r0) << c.l) + jf)
    }
}

/// The word of every cell (`Lay.wordK`, `Lay.wordE` tabulated); `NONE` for a constant `K` cell (no word).
pub struct Words {
    pub k: Vec<u32>,
    pub e: Vec<[u32; 3]>,
}

impl Words {
    /// `wordK`/`wordE` for every cell of `c`'s program, read for read the Lean definitions (`owner?`, the
    /// writer's source, `wordC`'s dense region first, `slotWord`; inputs through `wordD`; `0` where Lean gives `0`).
    pub fn new(c: &Compiled, lay: &TLay) -> Words {
        let [nk, ne] = c.cells;
        let mut k = vec![0u32; nk];
        for (n, w) in k.iter_mut().enumerate().take(c.q.n_in[0]) {
            *w = lay.word_d(Ty::K, n, 0).unwrap_or(0) as u32;
        }
        let mut alias: Vec<(usize, usize)> = Vec::new();
        for (b, bl) in lay.blocks.iter().enumerate() {
            let size = 1usize << bl.l();
            assert_eq!(bl.st_k, c.lay[b].start[0], "layDump: block {b}'s K start");
            assert_eq!(bl.st_e, c.lay[b].start[1], "layDump: block {b}'s E start");
            for jf in 0..size {
                for r in 0..bl.tw_k {
                    let n = bl.st_k + bl.tw_k * jf + r;
                    k[n] = match &bl.src_k[r] {
                        CSrc::Slot(s) => lay.word_d(Ty::K, n, 0).unwrap_or_else(|| bl.slot_word(Ty::K, *s, jf, 0)) as u32,
                        CSrc::Alias(tgt) => {
                            alias.push((n, tgt.get(jf).copied().unwrap_or(0)));
                            0
                        }
                        CSrc::Load => 0,
                    };
                }
            }
        }
        // an alias's word is its target input cell's (`wordD`)
        for (n, t) in alias {
            k[n] = lay.word_d(Ty::K, t, 0).unwrap_or(0) as u32;
        }
        let mut e = vec![[0u32; 3]; ne];
        for (n, w) in e.iter_mut().enumerate().take(c.q.n_in[1]) {
            *w = std::array::from_fn(|m| lay.word_d(Ty::E, n, m).unwrap_or(0) as u32);
        }
        for (b, bl) in lay.blocks.iter().enumerate() {
            let size = 1usize << bl.l();
            let blk = &c.q.blocks[b];
            // the template row of each E writer rank (a `load` source names that row's operands)
            let ewriters: Vec<usize> = blk.tpl.iter().enumerate().filter(|(_, r)| r.writes() == Some(Ty::E)).map(|(t, _)| t).collect();
            assert_eq!(ewriters.len(), bl.tw_e, "layDump: block {b}'s E writers");
            for jf in 0..size {
                let j = unflat(&blk.dims, jf);
                for r in 0..bl.tw_e {
                    let n = bl.st_e + bl.tw_e * jf + r;
                    e[n] = match &bl.src_e[r] {
                        CSrc::Slot(s) => std::array::from_fn(|m| lay.word_d(Ty::E, n, m).unwrap_or_else(|| bl.slot_word(Ty::E, *s, jf, m)) as u32),
                        CSrc::Load => {
                            let row = &blk.tpl[ewriters[r]];
                            std::array::from_fn(|m| k[row.args[m].at(&j)])
                        }
                        CSrc::Alias(_) => [0; 3],
                    };
                }
            }
        }
        for (lo, len) in &lay.cst {
            for w in &mut k[*lo..lo + len] {
                *w = NONE;
            }
        }
        Words { k, e }
    }
}

/// The entries of `ents Q lay` as `(x, Ent)`, with a tag per (template or aux) row: `(x, Ent)` lists, the tags
/// `(pseudo-block, row)` with `ℓ` per pseudo-block (the blocks, then the aux blocks), the slot → tag map.
pub struct Ents {
    pub ents: Vec<(u32, Ent)>,
    pub tags: Vec<(usize, usize)>,
    pub ell: Vec<u8>,
    pub slot_tag: Vec<u32>,
}

/// **The matrices' entries** (`LvmWiring.ents`): every constraint instance's (`instEnts`), then the auxiliary rows'
/// (`auxRowEnts`). `kc` holds the constant cells' values (the inputs').
pub fn entries(c: &Compiled, lay: &TLay, w: &Words, kc: &[F64]) -> Ents {
    let nb = lay.blocks.len();
    let mut xi: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, x) in lay.xs.iter().enumerate() {
        xi.entry(x.blk).or_default().push(i);
    }
    let one = lay.one as u32;
    let cell = |ty: Ty, n: usize, wt: F192, o: u8, x: u32, out: &mut Vec<(u32, Ent)>| match ty {
        Ty::K => {
            let y = w.k[n];
            if y == NONE {
                out.push((x, Ent { y: one, o, c: wt.mul_base(kc[n]) }));
            } else {
                out.push((x, Ent { y, o, c: wt }));
            }
        }
        Ty::E => {
            let ys = w.e[n];
            out.push((x, Ent { y: ys[0], o, c: wt }));
            out.push((x, Ent { y: ys[1], o, c: wt * F192::Y }));
            out.push((x, Ent { y: ys[2], o, c: wt * F192::Y * F192::Y }));
        }
    };
    let mut ents: Vec<(u32, Ent)> = Vec::new();
    let mut tags: Vec<(usize, usize)> = Vec::new();
    let mut ell: Vec<u8> = lay.blocks.iter().map(|b| b.l() as u8).collect();
    ell.extend(lay.aux.iter().map(|a| a.l as u8));
    let mut slot_tag = vec![NONE; 1 << X_VARS];
    let one_w = F192::ONE;
    for (b, bl) in lay.blocks.iter().enumerate() {
        let blk = &c.q.blocks[b];
        let cl = &c.lay[b];
        assert_eq!(bl.cr.len(), blk.tpl.len(), "layDump: block {b}'s constraint ranks");
        for (t, r) in blk.tpl.iter().enumerate() {
            let Some(rank) = bl.cr[t] else { continue };
            tags.push((b, t));
            let tag = tags.len() as u32 - 1;
            for jf in 0..cl.size {
                let j = unflat(&blk.dims, jf);
                let x = lay.slot_r(&xi, b, rank, jf).unwrap_or(0) as u32;
                slot_tag[x as usize] = tag;
                let arg = |k: usize, wt: F192, o: u8, out: &mut Vec<(u32, Ent)>| {
                    let a = &r.args[k];
                    cell(a.ty, a.at(&j), wt, o, x, out)
                };
                let res = |out: &mut Vec<(u32, Ent)>| {
                    let ty = r.ty;
                    let ti = if ty == Ty::K { 0 } else { 1 };
                    cell(ty, cl.start[ti] + cl.tw[ti] * jf + cl.rank[t][ti], one_w, MW, x, out)
                };
                match r.op {
                    Op::MulAdd => {
                        arg(0, one_w, MA, &mut ents);
                        arg(1, one_w, MB, &mut ents);
                        arg(2, one_w, MD, &mut ents);
                        res(&mut ents);
                    }
                    Op::Lin(k, k2) => {
                        arg(0, one_w, MD, &mut ents);
                        arg(1, F192::from(k), MD, &mut ents);
                        ents.push((x, Ent { y: one, o: MD, c: F192::from(k2) }));
                        res(&mut ents);
                    }
                    Op::Assert0 => {
                        arg(1, one_w, MA, &mut ents);
                        arg(0, one_w, MB, &mut ents);
                    }
                    Op::FixMul => {
                        arg(0, F192::from(c.fix_mat(&j)), MD, &mut ents);
                        arg(1, one_w, MD, &mut ents);
                        res(&mut ents);
                    }
                    Op::LoadE | Op::Readd(..) => unreachable!("layDump: a loadE or readd row with a constraint rank"),
                }
            }
        }
    }
    for (k, a) in lay.aux.iter().enumerate() {
        let pb = nb + k;
        for (r, row) in a.rows.iter().enumerate() {
            tags.push((pb, r));
            let tag = tags.len() as u32 - 1;
            for j in 0..1usize << a.l {
                let x = lay.slot_r(&xi, pb, r, j).unwrap_or(0) as u32;
                slot_tag[x as usize] = tag;
                for (o, op, wt) in row {
                    match op {
                        AOp::Word(base, stride) => ents.push((x, Ent { y: (base + stride * j) as u32, o: *o, c: *wt })),
                        AOp::Cell(ad) => cell(ad.ty, ad.at(&[j]), *wt, *o, x, &mut ents),
                        AOp::One => ents.push((x, Ent { y: one, o: *o, c: *wt })),
                    }
                }
            }
        }
    }
    // zero weights add nothing to Φ_Q (`lin` with k = 0 or k' = 0, a zero constant)
    ents.retain(|e| !e.1.c.is_zero());
    Ents { ents, tags, ell, slot_tag }
}

/// The results-only witness `z` (`2^yVars` words): every cell with a word (committed results, inputs on their
/// regions, `loadE` cells through their operands, aliases through their targets) gets the run's value, `z(one) = 1`.
/// Two cells on one word must agree (asserted). The virtual regions are then the inputs' values on the words the
/// inputs name; the caller fills the rest of them from their sources and checks the inputs ([`fill_virtual`]).
pub fn witness(c: &Compiled, lay: &TLay, w: &Words, kc: &[F64], ec: &[F192]) -> Vec<F64> {
    witness_set(c, lay, w, kc, ec).0
}

/// [`witness`] and which words a cell set (what [`crate::lvm::typed_prove::fill_virtual`] checks against the sources).
pub fn witness_set(c: &Compiled, lay: &TLay, w: &Words, kc: &[F64], ec: &[F192]) -> (Vec<F64>, Vec<bool>) {
    let mut z = vec![F64::ZERO; 1 << Y_VARS];
    let mut set = vec![false; 1 << Y_VARS];
    let mut put = |y: u32, v: F64, what: &dyn Fn() -> String| {
        let y = y as usize;
        if set[y] {
            assert!(z[y] == v, "two cells on word {y} disagree ({})", what());
        }
        z[y] = v;
        set[y] = true;
    };
    for (n, &y) in w.k.iter().enumerate() {
        if y != NONE {
            put(y, kc[n], &|| format!("K cell {n}"));
        }
    }
    for (b, bl) in lay.blocks.iter().enumerate() {
        let size = 1usize << bl.l();
        for jf in 0..size {
            for r in 0..bl.tw_e {
                if let CSrc::Slot(_) = bl.src_e[r] {
                    let n = bl.st_e + bl.tw_e * jf + r;
                    let l = ec[n].to_limbs();
                    for m in 0..3 {
                        put(w.e[n][m], F64(l[m]), &|| format!("E cell {n} limb {m} (block {b})"));
                    }
                }
            }
        }
    }
    for n in 0..c.q.n_in[1] {
        let l = ec[n].to_limbs();
        for m in 0..3 {
            put(w.e[n][m], F64(l[m]), &|| format!("E input {n}"));
        }
    }
    put(lay.one as u32, F64::ONE, &|| "the word 1".into());
    (z, set)
}

/// `Typed` from the entries (`x_log = 20`, `y_log = 21`), its used prefixes the layout's.
pub fn typed_of(e: Ents, lay: &TLay) -> Typed {
    let x_live = lay.xs.iter().map(|c| c.base + (c.n << c.l)).max().unwrap_or(0);
    let y_live = lay.y_end();
    Typed::from_ents(X_VARS, Y_VARS, e.ents, x_live, y_live, lay.one as u32, e.ell, e.slot_tag, e.tags)
}

/// **The `BITS` bit words** (B1-Q's `bitsAux`, `LvmQTypedBits.chunkRows`): class `k`'s row `x` has its 64 bits at the
/// free committed words `bw_k + 64x + z`, `z < 64` (bit `z` of its word: the cell `wc[x]` when `rd`, else the free
/// word, the WOTS checksum of its 4 cells). The aux blocks are the classes' chunks in class order (`bspecs`), each
/// block's booleanity row `z` naming bit `z`'s word at iteration 0 (`AOp::Word(base, 64)`); a block's chunk starts
/// where the class's previous one ended. Returns how many words it set.
pub fn fill_bits(z: &mut [F64], lay: &TLay, spec: &crate::lvm::loopir::M3Spec, kc: &[F64]) -> usize {
    let mut blocks = lay.aux.iter();
    let mut set = 0usize;
    for (k, b) in spec.bits.iter().enumerate() {
        let word = |x: usize| -> u64 {
            match spec.free.iter().find(|f| f.0 == k) {
                Some(&(_, 0, cell)) => crate::lvm::m3::free_checksum(&kc[cell..cell + 4]),
                Some(&(_, kind, _)) => panic!("BITS: free word kind {kind}"),
                None => kc[b.wc[x]].0,
            }
        };
        let mut x0 = 0usize;
        while x0 < b.n {
            let a = blocks.next().expect("an aux block per chunk of every BITS class");
            assert!(a.rows.len() >= 64, "a BITS chunk's 64 booleanity rows");
            for zb in 0..64 {
                let (base, stride) = match a.rows[zb].first() {
                    Some((_, AOp::Word(base, stride), _)) => (*base, *stride),
                    _ => panic!("BITS: booleanity row {zb} names its bit word"),
                };
                for j in 0..1usize << a.l {
                    z[base + stride * j] = F64((word(x0 + j) >> zb) & 1);
                    set += 1;
                }
            }
            x0 += 1 << a.l;
        }
        assert_eq!(x0, b.n, "class {k}'s chunks cover its rows");
    }
    assert!(blocks.next().is_none(), "every aux block is a BITS chunk");
    set
}

/// R9-TY: [`witness_set`] and [`fill_bits`] as tabulated gathers, built before `ready` (program data only).
/// `src[y]`: the first cell [`witness_set`] puts on word `y` (a `K` cell `n`; an `E` cell's limb, `SRC_E | 3n + m`;
/// the word 1; none); `dups`: every later put `(y, source)`, which must agree with the first (the serial version
/// asserts it at each put); `set[y]`: some cell put on `y`. `bits`: [`fill_bits`]'s chunks `(class, x0, aux block)`,
/// when their bit words are pairwise distinct (else `None`, and the serial [`fill_bits`] runs).
/// The words are the same as the serial functions' (each a copy of one cell or one bit), in any order.
pub struct WSrc {
    src: Vec<u32>,
    dups: Vec<(u32, u32)>,
    pub set: Vec<bool>,
    bits: Option<Vec<(usize, usize, usize)>>,
}

const SRC_NONE: u32 = u32::MAX;
const SRC_ONE: u32 = u32::MAX - 1;
const SRC_E: u32 = 1 << 31;

impl WSrc {
    pub fn new(c: &Compiled, lay: &TLay, w: &Words, spec: &crate::lvm::loopir::M3Spec) -> WSrc {
        let ny = 1usize << Y_VARS;
        let (mut src, mut dups) = (vec![SRC_NONE; ny], Vec::new());
        assert!(w.k.len() < SRC_E as usize && 3 * w.e.len() < (SRC_ONE - SRC_E) as usize, "WSrc: the cells fit the codes");
        let mut put = |y: u32, code: u32| {
            let y = y as usize;
            if src[y] == SRC_NONE {
                src[y] = code;
            } else {
                dups.push((y as u32, code));
            }
        };
        for (n, &y) in w.k.iter().enumerate() {
            if y != NONE {
                put(y, n as u32);
            }
        }
        for bl in &lay.blocks {
            for jf in 0..1usize << bl.l() {
                for r in 0..bl.tw_e {
                    if let CSrc::Slot(_) = bl.src_e[r] {
                        let n = bl.st_e + bl.tw_e * jf + r;
                        for m in 0..3 {
                            put(w.e[n][m], SRC_E | (3 * n + m) as u32);
                        }
                    }
                }
            }
        }
        for n in 0..c.q.n_in[1] {
            for m in 0..3 {
                put(w.e[n][m], SRC_E | (3 * n + m) as u32);
            }
        }
        put(lay.one as u32, SRC_ONE);
        let set = src.iter().map(|&s| s != SRC_NONE).collect();
        // fill_bits' chunks, in its order; parallel only when no word gets two bits
        let mut chunks = Vec::new();
        let mut blocks = lay.aux.iter().enumerate();
        let mut seen = vec![false; ny];
        let mut distinct = true;
        for (k, b) in spec.bits.iter().enumerate() {
            let mut x0 = 0usize;
            while x0 < b.n {
                let Some((ai, a)) = blocks.next() else { break };
                if a.rows.len() < 64 {
                    distinct = false;
                    break;
                }
                for zb in 0..64 {
                    match a.rows[zb].first() {
                        Some((_, AOp::Word(base, stride), _)) => {
                            for j in 0..1usize << a.l {
                                let y = base + stride * j;
                                distinct &= y < ny && !std::mem::replace(&mut seen[y], true);
                            }
                        }
                        _ => distinct = false,
                    }
                }
                chunks.push((k, x0, ai));
                x0 += 1 << a.l;
            }
            // (a class its chunks do not cover exactly: the serial version's asserts report it)
            distinct &= x0 == b.n;
        }
        distinct &= blocks.next().is_none();
        let bits = distinct.then_some(chunks);
        WSrc { src, dups, set, bits }
    }

    /// [`witness_set`]'s `z` (its `set` is [`Self::set`]), on the pool.
    pub fn witness(&self, kc: &[F64], ec: &[F192]) -> Vec<F64> {
        let val = |code: u32| -> F64 {
            match code {
                SRC_NONE => F64::ZERO,
                SRC_ONE => F64::ONE,
                c if c & SRC_E != 0 => {
                    let i = (c & !SRC_E) as usize;
                    F64(ec[i / 3].to_limbs()[i % 3])
                }
                c => kc[c as usize],
            }
        };
        // SAFETY: `fill` writes every element before any read.
        let z = unsafe { crate::lv::primitives::filled_vec(self.src.len(), |z: &mut [F64]| crate::lv::parallel::fill(z, |y| val(self.src[y]))) };
        let bad = crate::lv::parallel::find_first(self.dups.len(), |i| z[self.dups[i].0 as usize] != val(self.dups[i].1));
        if let Some(i) = bad {
            panic!("two cells on word {} disagree (source code {:#x})", self.dups[i].0, self.dups[i].1);
        }
        z
    }

    /// [`fill_bits`] on the pool (its serial version when the chunks' words are not distinct).
    pub fn fill_bits(&self, z: &mut [F64], lay: &TLay, spec: &crate::lvm::loopir::M3Spec, kc: &[F64]) {
        let Some(chunks) = &self.bits else {
            fill_bits(z, lay, spec, kc);
            return;
        };
        let zp = crate::lv::parallel::SendPtr(z.as_mut_ptr());
        let nz = z.len();
        crate::lv::parallel::for_each(chunks.len(), |ci| {
            let (k, x0, ai) = chunks[ci];
            let (b, a) = (&spec.bits[k], &lay.aux[ai]);
            let free = spec.free.iter().find(|f| f.0 == k);
            let words: Vec<u64> = (x0..x0 + (1usize << a.l))
                .map(|x| match free {
                    Some(&(_, 0, cell)) => crate::lvm::m3::free_checksum(&kc[cell..cell + 4]),
                    Some(&(_, kind, _)) => panic!("BITS: free word kind {kind}"),
                    None => kc[b.wc[x]].0,
                })
                .collect();
            for zb in 0..64 {
                let Some((_, AOp::Word(base, stride), _)) = a.rows[zb].first() else { unreachable!() };
                for (j, &w) in words.iter().enumerate() {
                    let y = base + stride * j;
                    assert!(y < nz);
                    // SAFETY: every bit word is one chunk's, once (`WSrc::new` checked them pairwise distinct).
                    unsafe { *zp.add(y) = F64((w >> zb) & 1) };
                }
            }
        });
    }
}
