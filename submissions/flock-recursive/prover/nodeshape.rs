//! Timing surrogate of the node's element phases on the **dumped** node circuit (P2 resumption 4,
//! rev. 3.13; not part of any proof). It loads S-E5's node dump (`logs/S-E5/nodedump/`: `mrows-0/1`,
//! `lrows`; env `FLOCK_NODE_ROWS` = the directory) once, before the clock, and runs on the packed
//! witness `f` (`2^23` F, the node's size) the work the node prover adds to the shared PIOP:
//!
//! * E2: `a = A_M f`, `b = B_M f`, `c = C_M f` over `N_M = 2^21` rows (sparse products), then 21
//!   degree-3 zerocheck rounds of `eq(r, ·)(a b − c)` (Gruen's form, the leaf's kernels);
//! * E4 (rev. 3.13): the table `W = (A_M + κ B_M + κ² C_M)ᵀ eq(r_E2, ·) + κ³ (A_L + …)ᵀ eq(r_Lr, ·)`
//!   over the `2^23` cells (one transposed sweep of both matrices), then the 23-round degree-2
//!   lincheck `Σ W·f`;
//! * Lr: `A_L f`, `B_L f`, `C_L f` over `2^15` rows, 15 degree-3 rounds.
//!
//! Challenges come from a local hash chain. The dump holds the rows S-E5 compiled (282,319 per slot);
//! the node circuit's model has 968,943 (the missing templates); `report` gives both the measured
//! times and the entry counts, so the sparse parts can be scaled.

use crate::field::{FAcc, F};
use crate::mle::eq_table;
use crate::par;
use crate::sumcheck::{fold_f, prove_pairs};
use std::sync::OnceLock;
use std::time::Instant;

/// A sparse matrix by rows: `ptr[i]..ptr[i+1]` index `(cell, coef)`.
pub struct Csr {
    pub nrows: usize,
    pub ptr: Vec<u32>,
    pub cell: Vec<u32>,
    pub coef: Vec<F>,
}

pub struct Rows {
    pub a: Csr,
    pub b: Csr,
    pub c: Csr,
    /// the three matrices transposed (by cell), with the matrix index in the entry: `(row, coef, k)`
    pub t: Csr,
    pub tk: Vec<u8>,
}

impl Rows {
    pub fn nnz(&self) -> usize {
        self.a.cell.len() + self.b.cell.len() + self.c.cell.len()
    }
}

fn parse_lin(s: &str, cells: &mut Vec<u32>, coefs: &mut Vec<F>) {
    for t in s.split_whitespace() {
        if let Some((c, h)) = t.split_once(':') {
            let mut b = [0u8; 16];
            for i in 0..16 {
                b[i] = u8::from_str_radix(&h[2 * i..2 * i + 2], 16).unwrap_or(0);
            }
            cells.push(c.parse().unwrap());
            coefs.push(F::from_bytes(&b));
        }
    }
}

/// Load `files` (`row | A | B | C` lines, global row indices) into `nrows`-row matrices.
pub fn load(files: &[std::path::PathBuf], nrows: usize) -> Option<Rows> {
    let mut per: Vec<[(Vec<u32>, Vec<F>); 3]> = (0..nrows).map(|_| Default::default()).collect();
    for f in files {
        let text = std::fs::read_to_string(f).ok()?;
        for line in text.lines() {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let p: Vec<&str> = line.split(" | ").collect();
            if p.len() < 4 {
                continue;
            }
            let r: usize = p[0].trim().parse().ok()?;
            if r >= nrows {
                return None;
            }
            for k in 0..3 {
                let (c, v) = &mut per[r][k];
                parse_lin(p[k + 1], c, v);
            }
        }
    }
    let mk = |k: usize| -> Csr {
        let mut ptr = Vec::with_capacity(nrows + 1);
        let (mut cell, mut coef) = (Vec::new(), Vec::new());
        ptr.push(0);
        for r in per.iter() {
            cell.extend_from_slice(&r[k].0);
            coef.extend_from_slice(&r[k].1);
            ptr.push(cell.len() as u32);
        }
        Csr { nrows, ptr, cell, coef }
    };
    let (a, b, c) = (mk(0), mk(1), mk(2));
    // the transpose over the 2^23 cells (built once, untimed)
    let ncells = 1usize << 23;
    let mut cnt = vec![0u32; ncells + 1];
    for m in [&a, &b, &c] {
        for &cl in &m.cell {
            cnt[cl as usize + 1] += 1;
        }
    }
    for i in 0..ncells {
        cnt[i + 1] += cnt[i];
    }
    let n = cnt[ncells] as usize;
    let (mut row, mut coef, mut tk) = (vec![0u32; n], vec![F::ZERO; n], vec![0u8; n]);
    let mut fill = cnt.clone();
    for (k, m) in [&a, &b, &c].iter().enumerate() {
        for r in 0..m.nrows {
            for i in m.ptr[r] as usize..m.ptr[r + 1] as usize {
                let p = fill[m.cell[i] as usize] as usize;
                fill[m.cell[i] as usize] += 1;
                row[p] = r as u32;
                coef[p] = m.coef[i];
                tk[p] = k as u8;
            }
        }
    }
    let t = Csr { nrows: ncells, ptr: cnt, cell: row, coef };
    Some(Rows { a, b, c, t, tk })
}

fn matvec(m: &Csr, f: &[F]) -> Vec<F> {
    par::collect_vec(m.nrows, 1 << 12, |r| {
        let mut acc = FAcc::default();
        for i in m.ptr[r] as usize..m.ptr[r + 1] as usize {
            acc.mac(m.coef[i], f.get(m.cell[i] as usize).copied().unwrap_or(F::ZERO));
        }
        acc.reduce()
    })
}

/// `out[cell] += Σ_k s_k Σ_rows w[row]·M_k(row, cell)` by the transpose, in parallel over cells.
fn transpose_acc(m: &Rows, w: &[F], s: [F; 3], out: &mut [F]) {
    par::for_each_chunk_mut(out, 1 << 12, |off, ch| {
        for (j, o) in ch.iter_mut().enumerate() {
            let c = off + j;
            let mut acc = [FAcc::default(), FAcc::default(), FAcc::default()];
            for i in m.t.ptr[c] as usize..m.t.ptr[c + 1] as usize {
                acc[m.tk[i] as usize].mac(m.t.coef[i], w[m.t.cell[i] as usize]);
            }
            *o += s[0] * acc[0].reduce() + s[1] * acc[1].reduce() + s[2] * acc[2].reduce();
        }
    });
}

/// A zerocheck of `eq(r,·)(a b − c)` to its end (timing; the linear part's `h(1)` by a pass).
fn zerocheck(mut a: Vec<F>, mut b: Vec<F>, mut c: Vec<F>, next: &mut dyn FnMut() -> F) {
    let lg = a.len().trailing_zeros() as usize;
    let r: Vec<F> = (0..lg).map(|_| next()).collect();
    for k in 0..lg {
        let (h1, hi) = crate::zerocheck::round_tab(&a, &b, &r[k + 1..], a.len());
        let e = eq_table(&r[k + 1..]);
        let mut acc = FAcc::default();
        for (p, w) in e.iter().enumerate() {
            acc.mac(*w, c[2 * p + 1]);
        }
        std::hint::black_box((h1, hi, acc.reduce()));
        let s = next();
        a = fold_f(&a, s);
        b = fold_f(&b, s);
        c = fold_f(&c, s);
    }
}

pub struct Dump {
    pub m: Rows,
    pub l: Rows,
}

static DUMP: OnceLock<Option<Dump>> = OnceLock::new();

/// Load the dump named by `FLOCK_NODE_ROWS` (once).
pub fn preload() -> Option<&'static Dump> {
    DUMP.get_or_init(|| {
        let d = std::path::PathBuf::from(std::env::var_os("FLOCK_NODE_ROWS")?);
        let t = Instant::now();
        let m = load(&[d.join("mrows-0.txt"), d.join("mrows-1.txt")], 1 << 21)?;
        let l = load(&[d.join("lrows.txt")], 1 << 15)?;
        eprintln!("nodeshape: loaded {} M entries, {} L entries in {:.2} s", m.nnz(), l.nnz(), t.elapsed().as_secs_f64());
        Some(Dump { m, l })
    })
    .as_ref()
}

/// Run E2, E4 and Lr on `f`; returns the phase times `(E2, E4, Lr)` in seconds.
pub fn run(f: &[F], seed: F) -> Option<(f64, f64, f64)> {
    let d = preload()?;
    let mut x = seed;
    let mut next = || {
        x = x * x + F::new(0x9E37_79B9_7F4A_7C15, 5);
        x
    };
    // Lr (its point is used by E4)
    let t = Instant::now();
    let (al, bl, cl) = (matvec(&d.l.a, f), matvec(&d.l.b, f), matvec(&d.l.c, f));
    zerocheck(al, bl, cl, &mut next);
    let r_lr: Vec<F> = (0..15).map(|_| next()).collect();
    let t_lr = t.elapsed().as_secs_f64();
    // E2
    let t = Instant::now();
    let (am, bm, cm) = (matvec(&d.m.a, f), matvec(&d.m.b, f), matvec(&d.m.c, f));
    zerocheck(am, bm, cm, &mut next);
    let r_e2: Vec<F> = (0..21).map(|_| next()).collect();
    let t_e2 = t.elapsed().as_secs_f64();
    // E4: the table over the 2^23 cells, then the lincheck
    let t = Instant::now();
    let k = next();
    let em = eq_table(&r_e2);
    let el = eq_table(&r_lr);
    let mut w = vec![F::ZERO; f.len()];
    transpose_acc(&d.m, &em, [F::ONE, k, k * k], &mut w);
    let k3 = k * k * k;
    transpose_acc(&d.l, &el, [k3, k3 * k, k3 * k * k], &mut w);
    let (pt, _) = prove_pairs(vec![(w, f.to_vec())], &mut |g| {
        std::hint::black_box(g);
        next()
    });
    std::hint::black_box(pt);
    Some((t_e2, t.elapsed().as_secs_f64(), t_lr))
}
