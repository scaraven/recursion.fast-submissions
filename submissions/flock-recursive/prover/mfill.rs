//! The node's M region (BLUEPRINT §4.3–4.4, A.7; S-E12b–d's node dump, `logs/S-E12d/nodedump/`):
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

/// Sparse rows: per row its index and three term ranges into `cells`/`coefs`.
pub struct Rows {
    pub idx: Vec<u32>,
    /// `[a0, a1, b1, c1]` per row: A is `a0..a1`, B `a1..b1`, C `b1..c1`.
    pub rng: Vec<[u32; 4]>,
    pub cells: Vec<u32>,
    pub coefs: Vec<F>,
}

impl Rows {
    fn new() -> Rows {
        Rows { idx: Vec::new(), rng: Vec::new(), cells: Vec::new(), coefs: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.idx.len()
    }
    fn push_terms(&mut self, s: &str) {
        for t in s.split(' ') {
            if t.is_empty() {
                continue;
            }
            let (c, h) = t.split_once(':').expect("cell:coef");
            self.cells.push(c.parse().expect("cell"));
            self.coefs.push(parse_coef(h));
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
                o[k] += self.coefs[t] * w(self.cells[t]);
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
    /// The solve order of an inactive (`0`) and an active (`1`) fill, recorded by the first.
    pub plan: [std::sync::OnceLock<Vec<(u32, u32)>>; 2],
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
        kt
    }
    /// The slot's region's first absolute cell.
    pub fn slot_cell(&self, sg: usize) -> usize {
        self.one_cell + sg * SLOT
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
            let forms = match p.get(3) {
                Some(f) => f.split(" ; ").map(|s| push(s, &mut fcells, &mut fcoefs)).collect(),
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
        Proto { pi, rows, regs, aux, fcells, fcoefs, plan: Default::default() }
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
}

/// **The slot fill** in the prototype's region coordinates (`local = cell − π·2^20`): returns the
/// `2^20` cells (`one′` at 0, the selector copies at 1–3).
pub fn fill(p: &Proto, run: SlotRun) -> (Vec<F>, FillStats) {
    let t0 = std::time::Instant::now();
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
    // registers (single-cell forms) and auxiliary imports
    for (ri, r) in p.regs.iter().enumerate() {
        let cs: Vec<F> = match run {
            Some((regs, _)) => match regs.get(ri) {
                Some(v) => comps(v),
                None => continue,
            },
            None if r.imp => vec![F::ZERO; r.forms.len()],
            None => continue,
        };
        for (j, &(a, b)) in r.forms.iter().enumerate() {
            if b == a + 1 && j < cs.len() {
                let k = p.fcoefs[a as usize];
                if !k.is_zero() {
                    set(p.fcells[a as usize], cs[j] * k.inv(), &mut val, &mut known, &mut st, &|| format!("reg r{ri}[{j}]"));
                }
            }
        }
    }
    for ax in &p.aux {
        let cs = match run {
            Some((regs, _)) => aux_comps(&regs[ax.reg as usize], ax.bits, ax.n),
            None => vec![F::ZERO; ax.n],
        };
        for (j, t) in (ax.terms.0..ax.terms.1).enumerate() {
            let k = p.fcoefs[t as usize];
            set(p.fcells[t as usize], cs.get(j).copied().unwrap_or(F::ZERO) * k.inv(), &mut val, &mut known, &mut st, &|| format!("aux r{}[{j}]", ax.reg));
        }
    }
    // the forward solve: the prototype's recorded order when it replays (the same rows solve the
    // same cells in every slot of the prototype), else the worklist to a fixed point
    let rw = &p.rows;
    let nr = rw.len();
    let key = run.is_some() as usize;
    let snap = p.plan[key].get().map(|_| (val.clone(), known.clone()));
    let mut done = false;
    if let Some(pl) = p.plan[key].get() {
        done = pl.iter().all(|&(r, c)| try_row(rw, base, r as usize, &mut val, &mut known) == Some(c as usize));
        if done {
            st.solved = pl.len();
        }
    }
    if !done {
        if let Some((v0, k0)) = snap {
            (val, known) = (v0, k0);
        }
        let rec = worklist(rw, base, &mut val, &mut known);
        st.solved = rec.len();
        let _ = p.plan[key].set(rec);
    }
    let t_solve = t0.elapsed().as_secs_f64();
    st.zeroed = known.iter().filter(|k| !**k).count();
    // check every row, and the multi-cell register forms against the run's values
    for i in 0..nr {
        let [a, b, c] = rw.eval(i, &|x| val[(x - base) as usize]);
        if a * b != c {
            st.failed_rows += 1;
            if st.first_failed.len() < 12 {
                st.first_failed.push(rw.idx[i]);
            }
        }
    }
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
        eprintln!("  fill p{} solve {t_solve:.3} total {:.3}", p.pi, t0.elapsed().as_secs_f64());
    }
    (val, st)
}

/// One row with one unknown cell, solved in place: `(a0 + αx)(b0 + βx) = c0 + γx` with one of
/// `α`, `β` zero gives `x·(a0β + αb0 + γ) = a0b0 + c0`. Returns the solved cell (region-local).
fn try_row(rw: &Rows, base: u32, i: usize, val: &mut [F], known: &mut [bool]) -> Option<usize> {
    let rg = rw.rng[i];
    let mut unk: Option<usize> = None;
    let mut kn = [F::ZERO; 3];
    let mut co = [F::ZERO; 3];
    for k in 0..3 {
        for t in rg[k] as usize..rg[k + 1] as usize {
            let l = (rw.cells[t] - base) as usize;
            if known[l] {
                kn[k] += rw.coefs[t] * val[l];
            } else {
                match unk {
                    None => unk = Some(l),
                    Some(u) if u == l => {}
                    _ => return None,
                }
                co[k] += rw.coefs[t];
            }
        }
    }
    let u = unk?;
    if !co[0].is_zero() && !co[1].is_zero() {
        return None;
    }
    let lin = kn[0] * co[1] + co[0] * kn[1] + co[2];
    if lin.is_zero() {
        return None;
    }
    let rhs = kn[0] * kn[1] + kn[2];
    val[u] = if lin == F::ONE { rhs } else { rhs * lin.inv() };
    known[u] = true;
    Some(u)
}

/// The worklist solve (cell → rows adjacency) to a fixed point; returns the order `(row, cell)`.
fn worklist(rw: &Rows, base: u32, val: &mut [F], known: &mut [bool]) -> Vec<(u32, u32)> {
    let nr = rw.len();
    let mut deg = vec![0u32; SLOT + 1];
    for &c in &rw.cells {
        deg[(c - base) as usize + 1] += 1;
    }
    for i in 0..SLOT {
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
    let mut rec = Vec::new();
    let mut queued = vec![true; nr];
    let mut work: Vec<u32> = (0..nr as u32).rev().collect();
    while let Some(i) = work.pop() {
        queued[i as usize] = false;
        let Some(u) = try_row(rw, base, i as usize, val, known) else { continue };
        rec.push((i, u as u32));
        for &r in &adj[deg[u] as usize..deg[u + 1] as usize] {
            if !queued[r as usize] {
                queued[r as usize] = true;
                work.push(r);
            }
        }
    }
    rec
}

/// The dump directory (`FLOCK_NODE_DUMP`, else `logs/S-E12d/nodedump` above the working directory)
/// and the prototype programs' directory (`FLOCK_PROTO_DIR`, else the dump directory).
pub fn find_dirs() -> Option<(std::path::PathBuf, std::path::PathBuf)> {
    let d = match std::env::var_os("FLOCK_NODE_DUMP") {
        Some(p) => std::path::PathBuf::from(p),
        None => crate::kat::find_up("logs/S-E12d/nodedump/mrows-p0.txt")?.parent()?.to_path_buf(),
    };
    let p = std::env::var_os("FLOCK_PROTO_DIR").map(std::path::PathBuf::from).unwrap_or_else(|| d.clone());
    Some((d, p))
}
