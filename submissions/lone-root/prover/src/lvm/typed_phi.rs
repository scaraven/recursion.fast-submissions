//! B1-P (lvm2 roll 8): `Φ_Q` by class kernels, the prover's evaluator of the A23 line `h` and of the matrix values
//! `v_o = M̃_o(r_x, r_y)` (B-DES §1.3–§1.4; B1-G0a correction 6: the prover's `h` uses the kernels, not entries).
//!
//! The entries of the four matrices are grouped per (template row, entry position) over the row's `2^ℓ` instances
//! (slot `x0 + jf`, iteration bits low). A group's word map `jf ↦ y(jf)` is cut into aligned sub-cubes
//! `[a, a + 2^ℓ')` on each of which it is affine in the bits of `jf`: `y = y0 + Σ_{i<ℓ'} c_i·jf_i` (the cube is split
//! on its top bit until it is; this is how B1-W's K2 "init at iteration 0" and its piecewise-affine splits land).
//! A piece is then summed by one of three kernels:
//! - **K1** (bit injection: every `c_i` is 0, a broadcast bit, or a distinct power of two `2^k` that misses `y0`):
//!   `eq_x(x0 ≫ ℓ')·eq_y(y0)·Π_i (1 + rx_i + ry_k)·(1 + ry_k)^{-1}` (characteristic 2);
//! - **the carry automaton** (K3, and every other affine map): the bits of `y` from low to high, the state the carry;
//!   pieces with the same `(o, ℓ', c)` and nearby `y0` share one pass, their offsets from the pass's base the initial
//!   states (B-DES §1.4's `W[o]`);
//! - **points**: the rest (glue rows, one-instance pieces, rows whose instances differ in shape).
//!
//! Every point of a batch is evaluated in the same pass: a weight is a vector over the points (point-minor tables),
//! so the static data is read once per batch. Exact: [`PhiK::eval`] equals the plain sparse evaluator
//! ([`super::typed::phi_multi`]) at random points (checked by `lvm-prover typed toy`).
use std::collections::HashMap;

use crate::lv::primitives::field::{F192, F192Unreduced};
use crate::lv::primitives::multilinear::eq_table_serial;
use crate::lvm::typed::{Ent, Typed, eq_o};

const NONE: u32 = u32::MAX;
/// Points per batch of [`PhiK::mats`] (`TYPED_PHIK_BATCH`): 42 line points in 7 batches.
const BATCH: usize = 6;
/// Work items per batch.
const CHUNKS: usize = 24;

enum Chunk {
    K1(std::ops::Range<usize>),
    Auto(std::ops::Range<usize>),
    Pts(std::ops::Range<usize>),
    /// R9-TY: point entries `pty[r]`, y-major
    PtsY(std::ops::Range<usize>),
}
/// At most this many free bits share a level of one automaton pass (else the piece's entries are points).
const MAX_LEVEL_BITS: usize = 3;

/// A K1 piece: the slot `x0 ≫ ℓ` at level `ℓ` (`x`), word `y0`, matrix `o`, pattern, coefficient index.
#[derive(Clone, Copy)]
struct K1E {
    x: u32,
    ell: u8,
    y0: u32,
    o: u8,
    pat: u32,
    c: u32,
}

/// The group key of a K1 piece: `(o, pattern, ℓ, the x-high index, y0 ≫ ys)`; within a group the x factor's
/// high half, the y factor's high half and the pattern are common.
fn k1_key(e: &K1E, xs: usize, ys: usize) -> (u8, u32, u8, u32, u32) {
    let xh = if (e.ell as usize) <= xs { e.x >> (xs - e.ell as usize) } else { e.x };
    (e.o, e.pat, e.ell, xh, e.y0 >> ys)
}

/// The coefficient vector of an automaton pass, by level: `(k, [(i, c_i >> k)])` for the levels `k` that carry
/// free bits (`k` = the trailing zeros of `c_i`), in increasing `k`; `kstop` = the last such level + 1.
struct Shape {
    ell: u8,
    levels: Vec<(u8, Vec<(u8, i64)>)>,
    kstop: u8,
}

struct Pass {
    shape: u32,
    o: u8,
    ybase: i64,
    span: u32,
    mlo: u32,
    mhi: u32,
}

#[derive(Clone, Copy)]
struct Mem {
    /// the slot of the member's first instance (its enumerated bits set)
    x0: u32,
    delta: u32,
    c: u32,
    /// enumerated bits below `ℓ` (fixed per member: their `x` factor is the member's)
    mask: u32,
}

pub struct PhiK {
    x_log: usize,
    y_log: usize,
    coefs: Vec<F192>,
    /// K1 pieces, sorted by [`k1_key`].
    k1e: Vec<K1E>,
    /// Per pattern, its injected `(x bit, y bit)` pairs.
    pats: Vec<Vec<(u8, u8)>>,
    shapes: Vec<Shape>,
    passes: Vec<Pass>,
    mem: Vec<Mem>,
    /// Point entries `(x, y, o | coefficient index << 2)`, sorted by `(o, x ≫ 10, y ≫ 11, x, y)`.
    pt: Vec<(u32, u32, u32)>,
    /// R9-TY: the point groups with fewer distinct `y` than `x`, sorted by `(o, x ≫ 10, y ≫ 11, y, x)`: their sums run
    /// over `x` inside `y` (one `eq_lo(y)` product per `y` instead of one `eq_lo(x)` per `x`; the same field sum)
    pty: Vec<(u32, u32, u32)>,
    /// The work split (by the static counts) of one batch of points.
    chunks: Vec<Chunk>,
    /// Static product count per point, by class: tables, K1, automaton, points.
    pub products: [usize; 4],
    pub report: String,
}

/// `Π`-ready split of `eq(r, ·)` over `n` variables at `s`: `lev(ell, v) = eq(r[ell..], v)`.
struct Lev {
    s: usize,
    n: usize,
    /// `lo[ell]` = `eq(r[ell..s])` (ell ≤ s), point-minor
    lo: Vec<Vec<F192>>,
    /// `hi[j]` = `eq(r[s + j..n])`, point-minor
    hi: Vec<Vec<F192>>,
}

impl Lev {
    fn new(rs: &[&[F192]], s: usize) -> Lev {
        let np = rs.len();
        let n = rs[0].len();
        let s = s.min(n);
        let pm = |tabs: Vec<Vec<F192>>| -> Vec<F192> {
            let len = tabs[0].len();
            let mut out = vec![F192::ZERO; len * np];
            for (p, t) in tabs.into_iter().enumerate() {
                for (v, x) in t.into_iter().enumerate() {
                    out[v * np + p] = x;
                }
            }
            out
        };
        let lo = (0..=s).map(|ell| pm(rs.iter().map(|r| eq_table_serial(&r[ell..s])).collect())).collect();
        let hi = (0..=n - s).map(|j| pm(rs.iter().map(|r| eq_table_serial(&r[s + j..n])).collect())).collect();
        Lev { s, n, lo, hi }
    }

    /// Table entries built (products, roughly one per entry) per point.
    fn size(&self, np: usize) -> usize {
        (self.lo.iter().map(Vec::len).sum::<usize>() + self.hi.iter().map(Vec::len).sum::<usize>()) / np
    }

    /// `eq(r[ell..n], v)` into `out` (all points); `false` when `v` is outside `[0, 2^(n − ell))` (the value is 0).
    #[inline]
    fn get(&self, ell: usize, v: i64, np: usize, out: &mut [F192]) -> bool {
        if v < 0 || (ell < self.n && (v as u64) >> (self.n - ell) != 0) || (ell >= self.n && v != 0) {
            return false;
        }
        let v = v as usize;
        if ell <= self.s {
            let w = self.s - ell;
            let (l, h) = (v & ((1 << w) - 1), v >> w);
            let (a, b) = (&self.lo[ell][l * np..][..np], &self.hi[0][h * np..][..np]);
            for p in 0..np {
                out[p] = a[p] * b[p];
            }
        } else {
            out.copy_from_slice(&self.hi[ell - self.s][v * np..][..np]);
        }
        true
    }
}

/// Every point's tables.
struct Tabs {
    np: usize,
    x: Lev,
    y: Lev,
    /// per x bit `i` and point: `rx_i`; per y bit `k`: `ry_k`, `(1 + ry_k)^{-1}` (point-minor)
    rx: Vec<F192>,
    ry: Vec<F192>,
    iy: Vec<F192>,
    /// per pattern and point
    pat: Vec<F192>,
    /// `eq(ry_k, e)`, at `(2k + e)·np`; `eq(rx_i, b)·eq(ry_k, e)` at `((i·y_log + k)·4 + 2b + e)·np`
    fy: Vec<F192>,
    fxy: Vec<F192>,
}

impl PhiK {
    /// The kernel plan of `t`'s matrices (static; built before `ready`).
    pub fn new(t: &Typed) -> PhiK {
        let nx = 1usize << t.x_log;
        let mut coefs = t.coefs.clone();
        let mut cidx: HashMap<[u64; 3], u32> = coefs.iter().enumerate().map(|(i, c)| (c.to_limbs(), i as u32)).collect();
        let mut code = |c: F192| -> u32 {
            *cidx.entry(c.to_limbs()).or_insert_with(|| {
                coefs.push(c);
                coefs.len() as u32 - 1
            })
        };
        // first slot of every tag
        let mut first = vec![NONE; t.tags.len()];
        for x in 0..nx {
            let g = t.slot_tag[x];
            if g != NONE && first[g as usize] == NONE {
                first[g as usize] = x as u32;
            }
        }
        let rng = |x: usize| (t.row_ptr[x] as usize, t.row_ptr[x + 1] as usize);
        // slots x and x' have the same entry shape (count, and (o, c) per position)
        let same_shape = |x: usize, x2: usize| {
            let ((s, e), (s2, e2)) = (rng(x), rng(x2));
            e - s == e2 - s2 && (0..e - s).all(|i| t.ent[s + i].o == t.ent[s2 + i].o && t.ent[s + i].c == t.ent[s2 + i].c)
        };
        let mut is_pt = vec![false; t.ent.len()];
        let (mut n_k1, mut n_auto, mut n_pt_small, mut n_pt_shape, mut n_pt_cost) = (0usize, 0usize, 0usize, 0usize, 0usize);
        // the cubes `(x0, ℓ)` of one entry shape: a loop row's `2^ℓ` instances; runs of ℓ = 0 rows (glue) with
        // consecutive slots and one shape, cut into aligned power-of-two cubes (glue re-rolled)
        let mut cubes: Vec<(usize, usize)> = Vec::new();
        let mut glue: Vec<usize> = Vec::new();
        for (tag, &(b, _)) in t.tags.iter().enumerate() {
            let ell = t.ell[b] as usize;
            let x0 = first[tag] as usize;
            if ell == 0 {
                glue.push(x0);
            } else if (x0..x0 + (1 << ell)).all(|x| same_shape(x, x0)) {
                cubes.push((x0, ell));
            } else {
                for x in x0..x0 + (1 << ell) {
                    let (s, e) = rng(x);
                    is_pt[s..e].iter_mut().for_each(|v| *v = true);
                    n_pt_shape += e - s;
                }
            }
        }
        glue.sort_unstable();
        let mut gi = 0;
        let mut n_glue_cubes = 0usize;
        while gi < glue.len() {
            let mut gj = gi + 1;
            while gj < glue.len() && glue[gj] == glue[gj - 1] + 1 && same_shape(glue[gj], glue[gi]) {
                gj += 1;
            }
            let (mut x, e) = (glue[gi], glue[gj - 1] + 1);
            while x < e {
                let mut k = 0;
                while x % (2 << k) == 0 && x + (2 << k) <= e {
                    k += 1;
                }
                cubes.push((x, k));
                n_glue_cubes += (k > 0) as usize;
                x += 1 << k;
            }
            gi = gj;
        }
        let mut k1e: Vec<K1E> = Vec::new();
        let mut pats: Vec<Vec<(u8, u8)>> = Vec::new();
        let mut pat_id: HashMap<Vec<(u8, u8)>, u32> = HashMap::new();
        // automaton members by (o, ℓ, coefficient vector): (y0, x0, c, enumerated-bit mask)
        let mut amem: HashMap<(u8, u8, Vec<i64>), Vec<(i64, u32, u32, u32)>> = HashMap::new();
        let diag = std::env::var_os("TYPED_PHIK_DIAG").is_some();
        for &(x0, ell) in &cubes {
            let (s0, e0) = rng(x0);
            for i in 0..e0 - s0 {
                let e0 = t.ent[s0 + i];
                let c = code(e0.c);
                let y = |jf: usize| t.ent[t.row_ptr[x0 + jf] as usize + i].y as i64;
                let mut pieces: Vec<(usize, usize, i64, Vec<i64>)> = Vec::new();
                decompose(&y, 0, ell, &mut pieces);
                for (a, l, y0, cv) in pieces {
                    let xp = (x0 + a) as u32;
                    if l == 0 {
                        is_pt[t.row_ptr[x0 + a] as usize + i] = true;
                        n_pt_small += 1;
                        continue;
                    }
                    if let Some(pat) = k1_pattern(y0, &cv, t.y_log) {
                        let id = *pat_id.entry(pat.clone()).or_insert_with(|| {
                            pats.push(pat);
                            pats.len() as u32 - 1
                        });
                        k1e.push(K1E { x: xp >> l, ell: l as u8, y0: y0 as u32, o: e0.o, pat: id, c });
                        n_k1 += 1 << l;
                        continue;
                    }
                    // the automaton keeps the power-of-two runs and the longest other run; the other runs' bits
                    // are enumerated into members
                    let (cv2, enum_bits) = split_runs(&cv);
                    if enum_bits.len() > 8 || !levels_ok(&cv2) {
                        for jf in a..a + (1 << l) {
                            is_pt[t.row_ptr[x0 + jf] as usize + i] = true;
                        }
                        n_pt_cost += 1 << l;
                        continue;
                    }
                    let mask: u32 = enum_bits.iter().map(|&i| 1u32 << i).sum();
                    for asg in 0..1usize << enum_bits.len() {
                        let (mut yy, mut xx) = (y0, xp);
                        for (j, &bi) in enum_bits.iter().enumerate() {
                            if (asg >> j) & 1 == 1 {
                                yy += cv[bi];
                                xx |= 1 << bi;
                            }
                        }
                        amem.entry((e0.o, l as u8, cv2.clone())).or_default().push((yy, xx, c, mask));
                    }
                    n_auto += 1 << l;
                }
            }
        }
        if diag {
            eprintln!("phik diag: cubes {} ({n_glue_cubes} re-rolled glue cubes of ≥ 2 rows, from {} glue rows)", cubes.len(), glue.len());
        }
        {
            let (xs, ys) = (10.min(t.x_log), 11.min(t.y_log));
            k1e.sort_unstable_by_key(|e| (k1_key(e, xs, ys), e.x, e.y0));
        }
        // automaton passes: per key, members by y0, greedy clusters of bounded span; a pass dearer than its entries
        // as points is enumerated instead
        let (mut shapes, mut passes, mut mem): (Vec<Shape>, Vec<Pass>, Vec<Mem>) = (Vec::new(), Vec::new(), Vec::new());
        let mut xpts: Vec<(u32, u32, u32)> = Vec::new();
        let mut dear: HashMap<String, usize> = HashMap::new();
        // a pass is kept when it costs at most this many products per entry (points cost ≈ 1.1)
        let pt_cost: f64 = std::env::var("TYPED_PHIK_PT").ok().and_then(|v| v.parse().ok()).unwrap_or(1.5);
        let mut akeys: Vec<_> = amem.keys().cloned().collect();
        akeys.sort();
        for key in akeys {
            let mut ms = amem.remove(&key).unwrap();
            ms.sort();
            let (o, ell, cv) = key;
            let sh = shape_of(ell, &cv);
            let rmax = cv.iter().filter(|&&c| c != 0).map(|c| c.unsigned_abs() >> c.trailing_zeros()).max().unwrap_or(1) as i64;
            let cap = (2 * rmax).max(1 << sh.kstop).max(64);
            let sid = shapes.len() as u32;
            shapes.push(sh);
            let mut i = 0;
            while i < ms.len() {
                let base = ms[i].0;
                let mut j = i;
                while j < ms.len() && ms[j].0 - base <= cap {
                    j += 1;
                }
                let mlo = mem.len() as u32;
                for &(y0, x0, c, mask) in &ms[i..j] {
                    mem.push(Mem { x0, delta: (y0 - base) as u32, c, mask });
                }
                let ps = Pass { shape: sid, o, ybase: base, span: (ms[j - 1].0 - base) as u32, mlo, mhi: mem.len() as u32 };
                let ents: usize = ms[i..j].iter().map(|m| 1usize << (ell as u32 - m.3.count_ones())).sum();
                let pcost = pass_cost(&shapes[sid as usize], &ps, &mem);
                if diag && pcost as f64 > pt_cost * ents as f64 {
                    *dear.entry(format!("o {o} ℓ {ell} levels {:?}", shapes[sid as usize].levels)).or_default() += ents;
                }
                if pcost as f64 > pt_cost * ents as f64 {
                    // enumerate: every member's free bits
                    for m in mem.drain(mlo as usize..) {
                        let free: Vec<usize> = (0..ell as usize).filter(|&b| m.mask >> b & 1 == 0).collect();
                        for asg in 0..1usize << free.len() {
                            let (mut yy, mut xx) = (base + m.delta as i64, m.x0);
                            for (q, &bi) in free.iter().enumerate() {
                                if (asg >> q) & 1 == 1 {
                                    yy += cv[bi];
                                    xx |= 1 << bi;
                                }
                            }
                            xpts.push((xx, yy as u32, o as u32 | (m.c << 2)));
                        }
                    }
                    n_pt_cost += ents;
                    n_auto -= ents;
                } else {
                    passes.push(ps);
                }
                i = j;
            }
        }
        if diag {
            let mut ptmp: Vec<(u32, u32, u32)> = xpts.clone();
            for x in 0..nx {
                for i in t.row_ptr[x] as usize..t.row_ptr[x + 1] as usize {
                    if is_pt[i] {
                        ptmp.push((x as u32, t.ent[i].y, t.ent[i].o as u32));
                    }
                }
            }
            // R9-TY: the points' products with the inner loop over x (as now), over y, and the cheaper per group
            for (xs, ys) in [(10u32, 11u32), (9, 12), (11, 10), (12, 9)] {
                let mut v: Vec<(u32, u32, u32)> = ptmp.iter().map(|&(x, y, o)| (o & 3, x, y)).collect();
                v.sort_unstable_by_key(|&(o, x, y)| (o, x >> xs, y >> ys, x, y));
                let (mut gx, mut gy, mut gmin, mut groups) = (0usize, 0usize, 0usize, 0usize);
                let mut i = 0;
                while i < v.len() {
                    let g = (v[i].0, v[i].1 >> xs, v[i].2 >> ys);
                    let mut j = i;
                    while j < v.len() && (v[j].0, v[j].1 >> xs, v[j].2 >> ys) == g {
                        j += 1;
                    }
                    let mut xsv: Vec<u32> = v[i..j].iter().map(|e| e.1).collect();
                    let mut ysv: Vec<u32> = v[i..j].iter().map(|e| e.2).collect();
                    xsv.dedup();
                    ysv.sort_unstable();
                    ysv.dedup();
                    gx += xsv.len();
                    gy += ysv.len();
                    gmin += xsv.len().min(ysv.len());
                    groups += 1;
                    i = j;
                }
                eprintln!("phik diag R9-TY: split (x {xs}, y {ys}): groups {groups}, x-runs {gx}, y-runs {gy}, min {gmin}");
            }
            for (xs, ys) in [(10, 11), (10, 13), (10, 14), (12, 14), (8, 16)] {
                let mut keys: Vec<(u32, u32, u32)> = ptmp.iter().map(|&(x, y, o)| (o & 3, x >> xs, y >> ys)).collect();
                keys.sort_unstable();
                keys.dedup();
                eprintln!("phik diag: points {} in {} groups at split (x {xs}, y {ys})", ptmp.len(), keys.len());
            }
            let mut v: Vec<_> = dear.into_iter().collect();
            v.sort_by(|a, b| b.1.cmp(&a.1));
            for (k, n) in v.iter().take(25) {
                eprintln!("  dear {n}: {k}");
            }
        }
        // point entries `(x, y, o | c << 2)`: the enumerated ones and the dear passes', sorted by
        // `(o, x ≫ 10, y ≫ 11, x, y)` (one group per pair of high halves)
        let mut pt: Vec<(u32, u32, u32)> = xpts;
        for x in 0..nx {
            for i in t.row_ptr[x] as usize..t.row_ptr[x + 1] as usize {
                if is_pt[i] {
                    let e: Ent = t.ent[i];
                    pt.push((x as u32, e.y, e.o as u32 | (code(e.c) << 2)));
                }
            }
        }
        let (xs, ys) = (10.min(t.x_log), 11.min(t.y_log));
        pt.sort_unstable_by_key(|&(x, y, oc)| (oc & 3, x >> xs, y >> ys, x, y));
        // R9-TY: each group in the cheaper inner order (`TYPED_PHIK_YMAJOR=0`: all x-major, as before)
        let (pt, pty) = if std::env::var("TYPED_PHIK_YMAJOR").map_or(true, |v| v != "0") { split_major(pt, xs, ys) } else { (pt, Vec::new()) };
        if diag {
            // R9-TY: K1's products with the inner loop over x (as now) against the cheaper of x and y per group
            let (xs, ys) = (10.min(t.x_log), 11.min(t.y_log));
            let ym = (1u32 << ys) - 1;
            let (mut gx, mut gmin, mut groups, mut coef) = (0usize, 0usize, 0usize, 0usize);
            let mut i = 0;
            while i < k1e.len() {
                let key = k1_key(&k1e[i], xs, ys);
                let mut j = i;
                while j < k1e.len() && k1_key(&k1e[j], xs, ys) == key {
                    j += 1;
                }
                let mut xv: Vec<u32> = k1e[i..j].iter().map(|e| e.x).collect();
                let mut yv: Vec<u32> = k1e[i..j].iter().map(|e| e.y0 & ym).collect();
                xv.dedup();
                yv.sort_unstable();
                yv.dedup();
                gx += xv.len();
                gmin += xv.len().min(yv.len());
                coef += k1e[i..j].iter().filter(|e| e.c != 0).count();
                groups += 1;
                i = j;
            }
            eprintln!("phik diag R9-TY: K1 groups {groups}, x-runs {gx}, min(x, y) {gmin}, coefficient products {coef}");
        }
        let mut pk = PhiK {
            x_log: t.x_log,
            y_log: t.y_log,
            coefs,
            k1e,
            pats,
            shapes,
            passes,
            mem,
            pt,
            pty,
            chunks: Vec::new(),
            products: [0; 4],
            report: String::new(),
        };
        pk.products = pk.count();
        pk.chunks = pk.split();
        if diag {
            let mut pc: Vec<(usize, usize)> = pk.passes.iter().enumerate().map(|(i, ps)| (pass_cost(&pk.shapes[ps.shape as usize], ps, &pk.mem), i)).collect();
            pc.sort_unstable_by(|a, b| b.cmp(a));
            let hist = |lo: usize, hi: usize| pc.iter().filter(|r| r.0 >= lo && r.0 < hi).map(|r| r.0).sum::<usize>();
            eprintln!("phik diag: pass cost <100 {} <1k {} <10k {} ≥10k {}", hist(0, 100), hist(100, 1000), hist(1000, 10000), hist(10000, usize::MAX));
            for &(cost, i) in pc.iter().take(20) {
                let ps = &pk.passes[i];
                let sh = &pk.shapes[ps.shape as usize];
                eprintln!("  pass {i}: cost {cost}, o {}, ℓ {}, members {}, span {}, ybase {}, levels {:?}", ps.o, sh.ell, ps.mhi - ps.mlo, ps.span, ps.ybase, sh.levels);
            }
        }
        // which kernel cases this program reaches (the exactness check covers only these)
        let cov = {
            let k1_big = pk.k1e.iter().filter(|e| e.ell as usize > 10.min(t.x_log)).count();
            let (mut neg, mut big, mut masked, mut k0) = (0usize, 0usize, 0usize, 0usize);
            for ps in &pk.passes {
                let sh = &pk.shapes[ps.shape as usize];
                neg += sh.levels.iter().any(|l| l.1.iter().any(|b| b.1 < 0)) as usize;
                big += (sh.ell as usize > 10 || sh.kstop > 11) as usize;
                masked += pk.mem[ps.mlo as usize..ps.mhi as usize].iter().any(|m| m.mask != 0) as usize;
                k0 += (sh.kstop == 0) as usize;
            }
            format!("; cases reached: K1 pieces with ℓ > 10 {k1_big}, passes with a negative coefficient {neg}, with ℓ > 10 or kstop > 11 {big}, with enumerated members {masked}, with kstop 0 {k0}, glue cubes {n_glue_cubes}")
        };
        let p = pk.products;
        pk.report = format!(
            "phik: K1 {} pieces, {n_k1} entries, {} patterns; automaton {} passes ({} shapes, {} members, {n_auto} entries); \
             points {} (one-instance pieces {n_pt_small}, rows of differing shape {n_pt_shape}, dearer as passes {n_pt_cost}); \
             products per point: tables {} K1 {} automaton {} points {} = {}",
            pk.k1e.len(),
            pk.pats.len(),
            pk.passes.len(),
            pk.shapes.len(),
            pk.mem.len(),
            pk.pt.len(),
            p[0],
            p[1],
            p[2],
            p[3],
            p.iter().sum::<usize>()
        ) + &cov;
        pk
    }

    /// The static product count per point (the loops of [`Self::eval`], without running them).
    fn count(&self) -> [usize; 4] {
        let xs = 10.min(self.x_log);
        let ys = 11.min(self.y_log);
        let lev = |s: usize, n: usize| (0..=s).map(|l| 1usize << (s - l)).sum::<usize>() + (0..=n - s).map(|j| 1usize << (n - s - j)).sum::<usize>();
        let tables = lev(xs, self.x_log) + lev(ys, self.y_log) + 2 * self.pats.iter().map(Vec::len).sum::<usize>() + 4 + 2 * self.y_log + self.x_log * self.y_log;
        let (xs, ys) = (10.min(self.x_log), 11.min(self.y_log));
        let k1groups = if self.k1e.is_empty() { 0 } else { 1 + self.k1e.windows(2).filter(|w| k1_key(&w[0], xs, ys) != k1_key(&w[1], xs, ys)).count() };
        let k1xs = if self.k1e.is_empty() { 0 } else { 1 + self.k1e.windows(2).filter(|w| (k1_key(&w[0], xs, ys), w[0].x) != (k1_key(&w[1], xs, ys), w[1].x)).count() };
        let k1 = k1xs + self.k1e.iter().filter(|e| e.c != 0).count() + 3 * k1groups;
        let auto: usize = self.passes.iter().map(|ps| pass_cost(&self.shapes[ps.shape as usize], ps, &self.mem)).sum();
        let (xs, ys) = (10.min(self.x_log), 11.min(self.y_log));
        let grp = |e: &(u32, u32, u32)| (e.2 & 3, e.0 >> xs, e.1 >> ys);
        let groups = if self.pt.is_empty() { 0 } else { 1 + self.pt.windows(2).filter(|w| grp(&w[0]) != grp(&w[1])).count() };
        let ptxs = if self.pt.is_empty() { 0 } else { 1 + self.pt.windows(2).filter(|w| (grp(&w[0]), w[0].0) != (grp(&w[1]), w[1].0)).count() };
        let pts = ptxs + self.pt.iter().filter(|e| e.2 >> 2 != 0).count() + 2 * groups;
        let ygroups = if self.pty.is_empty() { 0 } else { 1 + self.pty.windows(2).filter(|w| grp(&w[0]) != grp(&w[1])).count() };
        let ptys = if self.pty.is_empty() { 0 } else { 1 + self.pty.windows(2).filter(|w| (grp(&w[0]), w[0].1) != (grp(&w[1]), w[1].1)).count() };
        let pts = pts + ptys + self.pty.iter().filter(|e| e.2 >> 2 != 0).count() + 2 * ygroups;
        [tables, k1, auto, pts]
    }

    /// Cut the work into about [`CHUNKS`] items of equal static cost.
    fn split(&self) -> Vec<Chunk> {
        let total: usize = self.products[1..].iter().sum();
        let target = (total / CHUNKS).max(1);
        let mut out = Vec::new();
        let (mut lo, mut acc) = (0usize, 0usize);
        let (xs, ys) = (10.min(self.x_log), 11.min(self.y_log));
        for i in 0..self.k1e.len() {
            acc += 2;
            if acc >= target && (i + 1 == self.k1e.len() || k1_key(&self.k1e[i], xs, ys) != k1_key(&self.k1e[i + 1], xs, ys)) {
                out.push(Chunk::K1(lo..i + 1));
                (lo, acc) = (i + 1, 0);
            }
        }
        if lo < self.k1e.len() {
            out.push(Chunk::K1(lo..self.k1e.len()));
        }
        (lo, acc) = (0, 0);
        for (i, ps) in self.passes.iter().enumerate() {
            acc += pass_cost(&self.shapes[ps.shape as usize], ps, &self.mem);
            if acc >= target {
                out.push(Chunk::Auto(lo..i + 1));
                (lo, acc) = (i + 1, 0);
            }
        }
        if lo < self.passes.len() {
            out.push(Chunk::Auto(lo..self.passes.len()));
        }
        let (xs, ys) = (10.min(self.x_log), 11.min(self.y_log));
        let grp = |e: &(u32, u32, u32)| (e.2 & 3, e.0 >> xs, e.1 >> ys);
        (lo, acc) = (0, 0);
        for i in 0..self.pt.len() {
            acc += 2;
            if acc >= target && (i + 1 == self.pt.len() || grp(&self.pt[i]) != grp(&self.pt[i + 1])) {
                out.push(Chunk::Pts(lo..i + 1));
                (lo, acc) = (i + 1, 0);
            }
        }
        if lo < self.pt.len() {
            out.push(Chunk::Pts(lo..self.pt.len()));
        }
        (lo, acc) = (0, 0);
        for i in 0..self.pty.len() {
            acc += 2;
            if acc >= target && (i + 1 == self.pty.len() || grp(&self.pty[i]) != grp(&self.pty[i + 1])) {
                out.push(Chunk::PtsY(lo..i + 1));
                (lo, acc) = (i + 1, 0);
            }
        }
        if lo < self.pty.len() {
            out.push(Chunk::PtsY(lo..self.pty.len()));
        }
        out
    }

    fn tabs(&self, pts: &[Vec<F192>]) -> Tabs {
        let np = pts.len();
        let (xl, yl) = (self.x_log, self.y_log);
        let rxs: Vec<&[F192]> = pts.iter().map(|p| &p[2..2 + xl]).collect();
        let rys: Vec<&[F192]> = pts.iter().map(|p| &p[2 + xl..2 + xl + yl]).collect();
        let x = Lev::new(&rxs, 10);
        let y = Lev::new(&rys, 11);
        let mut rx = vec![F192::ZERO; xl * np];
        let mut ry = vec![F192::ZERO; yl * np];
        let mut iy = vec![F192::ZERO; yl * np];
        for p in 0..np {
            for i in 0..xl {
                rx[i * np + p] = rxs[p][i];
            }
            // batch inversion of 1 + ry_k
            let vals: Vec<F192> = rys[p].iter().map(|&v| F192::ONE + v).collect();
            let mut pre = Vec::with_capacity(yl);
            let mut acc = F192::ONE;
            for &v in &vals {
                assert!(!v.is_zero(), "1 + r_y,k ≠ 0");
                pre.push(acc);
                acc *= v;
            }
            let mut inv = acc.inv();
            for k in (0..yl).rev() {
                iy[k * np + p] = inv * pre[k];
                inv *= vals[k];
                ry[k * np + p] = rys[p][k];
            }
        }
        let mut pat = vec![F192::ZERO; self.pats.len() * np];
        for (pi, pr) in self.pats.iter().enumerate() {
            for p in 0..np {
                let mut v = F192::ONE;
                for &(i, k) in pr {
                    let (a, b) = (rx[i as usize * np + p], ry[k as usize * np + p]);
                    v *= (F192::ONE + a + b) * iy[k as usize * np + p];
                }
                pat[pi * np + p] = v;
            }
        }
        let mut fy = vec![F192::ZERO; 2 * yl * np];
        for k in 0..yl {
            for p in 0..np {
                fy[(2 * k) * np + p] = F192::ONE + ry[k * np + p];
                fy[(2 * k + 1) * np + p] = ry[k * np + p];
            }
        }
        let mut fxy = vec![F192::ZERO; 4 * xl * yl * np];
        for i in 0..xl {
            for k in 0..yl {
                for p in 0..np {
                    let (a, b) = (rx[i * np + p], ry[k * np + p]);
                    let base = (i * yl + k) * 4;
                    fxy[(base + 3) * np + p] = a * b;
                    fxy[(base + 2) * np + p] = a + fxy[(base + 3) * np + p];
                    fxy[(base + 1) * np + p] = b + fxy[(base + 3) * np + p];
                    fxy[base * np + p] = F192::ONE + a + b + fxy[(base + 3) * np + p];
                }
            }
        }
        Tabs { np, x, y, rx, ry, iy, pat, fy, fxy }
    }

    /// `Σ_{x,y} M_o(x, y)·eq(px, x)·eq(py, y)` per matrix `o` and point (`out[o·np + p]`); a point is
    /// `κ ++ px ++ py` (`κ` unused here).
    pub fn mats(&self, pts: &[Vec<F192>]) -> Vec<F192> {
        self.mats_timed(pts).0
    }

    /// [`Self::mats`] and its phases' wall times: tables, then the work items (K1, automaton and points chunks
    /// together; their split is [`Self::chunks`]'s by the static counts).
    ///
    /// The points go in batches of [`BATCH`] (each batch's tables stay in L2); every (batch, chunk) pair is one task.
    pub fn mats_timed(&self, pts: &[Vec<F192>]) -> (Vec<F192>, [f64; 4]) {
        let np = pts.len();
        let bp: usize = std::env::var("TYPED_PHIK_BATCH").ok().and_then(|v| v.parse().ok()).unwrap_or(BATCH).max(1);
        let nb = np.div_ceil(bp);
        let t0 = std::time::Instant::now();
        let tabs: Vec<Tabs> = crate::lv::parallel::map_collect(nb, |b| self.tabs(&pts[b * bp..((b + 1) * bp).min(np)]));
        let t_tab = t0.elapsed().as_secs_f64();
        let nc = self.chunks.len();
        let parts: Vec<Vec<F192>> = crate::lv::parallel::map_collect(nb * nc, |it| {
            let (b, ci) = (it % nb, it / nb);
            let tb = &tabs[b];
            let mut out = vec![F192::ZERO; 4 * tb.np];
            match &self.chunks[ci] {
                Chunk::K1(r) => self.eval_k1(tb, r.clone(), &mut out),
                Chunk::Auto(r) => {
                    for ps in &self.passes[r.clone()] {
                        self.eval_pass(tb, ps, &mut out);
                    }
                }
                Chunk::Pts(r) => self.eval_points(tb, r.clone(), &mut out),
                Chunk::PtsY(r) => self.eval_points_y(tb, r.clone(), &mut out),
            }
            out
        });
        let mut m = vec![F192::ZERO; 4 * np];
        for (it, part) in parts.into_iter().enumerate() {
            let b = it % nb;
            let bn = tabs[b].np;
            for o in 0..4 {
                for q in 0..bn {
                    m[o * np + b * bp + q] += part[o * bn + q];
                }
            }
        }
        (m, [t_tab, t0.elapsed().as_secs_f64() - t_tab, 0.0, 0.0])
    }

    /// `Φ_Q` at every point.
    pub fn eval(&self, pts: &[Vec<F192>]) -> Vec<F192> {
        let np = pts.len();
        let m = self.mats(pts);
        (0..np)
            .map(|p| {
                let eo = eq_o(&pts[p][..2]);
                (0..4).map(|o| eo[o] * m[o * np + p]).sum()
            })
            .collect()
    }

    /// K1 pieces `r` (whole groups of [`k1_key`]): per piece `c·eq_x,lo·eq_y,lo`, per group the high halves and the
    /// pattern once.
    fn eval_k1(&self, tb: &Tabs, r: std::ops::Range<usize>, out: &mut [F192]) {
        let np = tb.np;
        let (xs, ys) = (tb.x.s, tb.y.s);
        let ym = (1u32 << ys) - 1;
        let ones = vec![F192::ONE; np];
        let mut run = vec![F192Unreduced::ZERO; np];
        let mut sub = vec![F192Unreduced::ZERO; np];
        let es = &self.k1e[r];
        let mut i = 0;
        while i < es.len() {
            let key = k1_key(&es[i], xs, ys);
            let (o, pat, ell) = (key.0 as usize, key.1 as usize, key.2 as usize);
            let mut j = i;
            while j < es.len() && k1_key(&es[j], xs, ys) == key {
                // the pieces of one x: Σ c·eq_lo(y0), then eq_lo(x) once
                let x = es[j].x;
                while j < es.len() && es[j].x == x && k1_key(&es[j], xs, ys) == key {
                    let e = &es[j];
                    let ly = &tb.y.lo[0][(e.y0 & ym) as usize * np..][..np];
                    if e.c == 0 {
                        for p in 0..np {
                            sub[p] ^= F192Unreduced::from(ly[p]);
                        }
                    } else {
                        let c = self.coefs[e.c as usize];
                        for p in 0..np {
                            sub[p] ^= ly[p].mul_unreduced(c);
                        }
                    }
                    j += 1;
                }
                let lx: &[F192] = if ell <= xs { &tb.x.lo[ell][(x & ((1 << (xs - ell)) - 1)) as usize * np..][..np] } else { &ones };
                for p in 0..np {
                    run[p] ^= sub[p].reduce().mul_unreduced(lx[p]);
                    sub[p] = F192Unreduced::ZERO;
                }
            }
            let hx = if ell <= xs { &tb.x.hi[0][key.3 as usize * np..][..np] } else { &tb.x.hi[ell - xs][key.3 as usize * np..][..np] };
            let hy = &tb.y.hi[0][key.4 as usize * np..][..np];
            let pt = &tb.pat[pat * np..][..np];
            for p in 0..np {
                out[o * np + p] += run[p].reduce() * hx[p] * hy[p] * pt[p];
                run[p] = F192Unreduced::ZERO;
            }
            i = j;
        }
    }

    fn eval_pass(&self, tb: &Tabs, ps: &Pass, out: &mut [F192]) {
        let np = tb.np;
        let sh = &self.shapes[ps.shape as usize];
        let ell = sh.ell as usize;
        // initial states: offsets 0..=span
        let (mut lo, mut hi) = (0i64, ps.span as i64);
        let mut w = vec![F192::ZERO; (hi - lo + 1) as usize * np];
        let mut ex = vec![F192::ZERO; np];
        for m in &self.mem[ps.mlo as usize..ps.mhi as usize] {
            assert!(tb.x.get(ell, (m.x0 >> ell) as i64, np, &mut ex), "a member's slot is in range");
            let mut mk = m.mask;
            while mk != 0 {
                let i = mk.trailing_zeros() as usize;
                mk &= mk - 1;
                let r = &tb.rx[i * np..][..np];
                if (m.x0 >> i) & 1 == 1 {
                    for p in 0..np {
                        ex[p] *= r[p];
                    }
                } else {
                    for p in 0..np {
                        ex[p] *= F192::ONE + r[p];
                    }
                }
            }
            let c = self.coefs[m.c as usize];
            let dst = &mut w[m.delta as usize * np..][..np];
            if m.c == 0 {
                for p in 0..np {
                    dst[p] += ex[p];
                }
            } else {
                for p in 0..np {
                    dst[p] += ex[p] * c;
                }
            }
        }
        let mut li = 0;
        let mut fac = vec![F192::ZERO; (2 << MAX_LEVEL_BITS) * np];
        let mut nw: Vec<F192Unreduced> = Vec::with_capacity(w.len() * 2);
        for k in 0..sh.kstop as usize {
            let bits: &[(u8, i64)] = if li < sh.levels.len() && sh.levels[li].0 as usize == k {
                li += 1;
                &sh.levels[li - 1].1
            } else {
                &[]
            };
            let nb = bits.len();
            // fac[(assignment, e)] = Π_i eq(rx_i, b_i) · eq(ry_k, e): the shared tables for nb ≤ 1
            let yl = self.y_log;
            let shared: Option<&[F192]> = match bits {
                [] => Some(&tb.fy[2 * k * np..][..2 * np]),
                [(i, _)] => Some(&tb.fxy[(*i as usize * yl + k) * 4 * np..][..4 * np]),
                _ => None,
            };
            for asg in 0..if shared.is_some() { 0 } else { 1usize << nb } {
                for p in 0..np {
                    let mut f = F192::ONE;
                    for (j, &(i, _)) in bits.iter().enumerate() {
                        let r = tb.rx[i as usize * np + p];
                        f *= if (asg >> j) & 1 == 1 { r } else { F192::ONE + r };
                    }
                    let r = tb.ry[k * np + p];
                    fac[(2 * asg) * np + p] = f * (F192::ONE + r);
                    fac[(2 * asg + 1) * np + p] = f * r;
                }
            }
            let ybit = (ps.ybase >> k) & 1;
            let sums: Vec<i64> = (0..1usize << nb).map(|asg| bits.iter().enumerate().filter(|(j, _)| (asg >> j) & 1 == 1).map(|(_, &(_, c))| c).sum()).collect();
            let (neg, pos) = (*sums.iter().min().unwrap(), *sums.iter().max().unwrap());
            let (nlo, nhi) = ((lo + ybit + neg).div_euclid(2), (hi + ybit + pos).div_euclid(2));
            nw.clear();
            nw.resize((nhi - nlo + 1) as usize * np, F192Unreduced::ZERO);
            for s in lo..=hi {
                let ws = &w[(s - lo) as usize * np..][..np];
                if ws[0].is_zero() && ws.iter().all(|v| v.is_zero()) {
                    continue;
                }
                for (asg, &sm) in sums.iter().enumerate() {
                    let t = s + ybit + sm;
                    let e = (t & 1) as usize;
                    let ns = t.div_euclid(2);
                    let f = match shared {
                        Some(t) => &t[(2 * asg + e) * np..][..np],
                        None => &fac[(2 * asg + e) * np..][..np],
                    };
                    let d = &mut nw[(ns - nlo) as usize * np..][..np];
                    for p in 0..np {
                        d[p] ^= ws[p].mul_unreduced(f[p]);
                    }
                }
            }
            w.clear();
            w.extend(nw.iter().map(|u| u.reduce()));
            lo = nlo;
            hi = nhi;
        }
        // finish: eq(ry[kstop..], (ybase >> kstop) + s)
        let kk = sh.kstop as usize;
        let mut ey = vec![F192::ZERO; np];
        let o = ps.o as usize;
        for s in lo..=hi {
            let ws = &w[(s - lo) as usize * np..][..np];
            if tb.y.get(kk, (ps.ybase >> kk) + s, np, &mut ey) {
                for p in 0..np {
                    out[o * np + p] += ws[p] * ey[p];
                }
            }
        }
    }

    /// Point entries `r` (whole groups): per entry `c·eq_lo(x)·eq_lo(y)`, per group of equal `(o, x ≫ 10, y ≫ 11)`
    /// the high halves once.
    fn eval_points(&self, tb: &Tabs, r: std::ops::Range<usize>, out: &mut [F192]) {
        let np = tb.np;
        let (xs, ys) = (tb.x.s, tb.y.s);
        let (xm, ym) = ((1u32 << xs) - 1, (1u32 << ys) - 1);
        let mut run = vec![F192Unreduced::ZERO; np];
        let mut sub = vec![F192Unreduced::ZERO; np];
        let es = &self.pt[r];
        let mut i = 0;
        while i < es.len() {
            let (o, xh, yh) = (es[i].2 & 3, es[i].0 >> xs, es[i].1 >> ys);
            let mut j = i;
            while j < es.len() && es[j].2 & 3 == o && es[j].0 >> xs == xh && es[j].1 >> ys == yh {
                // the entries of one slot: Σ c·eq_lo(y) (a unit c costs no product), then eq_lo(x) once
                let x = es[j].0;
                while j < es.len() && es[j].0 == x && es[j].2 & 3 == o && es[j].1 >> ys == yh {
                    let (_, y, oc) = es[j];
                    let ly = &tb.y.lo[0][(y & ym) as usize * np..][..np];
                    if oc >> 2 == 0 {
                        for p in 0..np {
                            sub[p] ^= F192Unreduced::from(ly[p]);
                        }
                    } else {
                        let c = self.coefs[(oc >> 2) as usize];
                        for p in 0..np {
                            sub[p] ^= ly[p].mul_unreduced(c);
                        }
                    }
                    j += 1;
                }
                let lx = &tb.x.lo[0][(x & xm) as usize * np..][..np];
                for p in 0..np {
                    run[p] ^= sub[p].reduce().mul_unreduced(lx[p]);
                    sub[p] = F192Unreduced::ZERO;
                }
            }
            let (hx, hy) = (&tb.x.hi[0][xh as usize * np..][..np], &tb.y.hi[0][yh as usize * np..][..np]);
            for p in 0..np {
                out[o as usize * np + p] += run[p].reduce() * hx[p] * hy[p];
                run[p] = F192Unreduced::ZERO;
            }
            i = j;
        }
    }
}

impl PhiK {
    /// [`Self::eval_points`] on `pty[r]`: per group `Σ_y eq_lo(y)·Σ_x c·eq_lo(x)`, then the high halves.
    fn eval_points_y(&self, tb: &Tabs, r: std::ops::Range<usize>, out: &mut [F192]) {
        let np = tb.np;
        let (xs, ys) = (tb.x.s, tb.y.s);
        let (xm, ym) = ((1u32 << xs) - 1, (1u32 << ys) - 1);
        let mut run = vec![F192Unreduced::ZERO; np];
        let mut sub = vec![F192Unreduced::ZERO; np];
        let es = &self.pty[r];
        let mut i = 0;
        while i < es.len() {
            let (o, xh, yh) = (es[i].2 & 3, es[i].0 >> xs, es[i].1 >> ys);
            let mut j = i;
            while j < es.len() && es[j].2 & 3 == o && es[j].0 >> xs == xh && es[j].1 >> ys == yh {
                let y = es[j].1;
                while j < es.len() && es[j].1 == y && es[j].2 & 3 == o && es[j].0 >> xs == xh {
                    let (x, _, oc) = es[j];
                    let lx = &tb.x.lo[0][(x & xm) as usize * np..][..np];
                    if oc >> 2 == 0 {
                        for p in 0..np {
                            sub[p] ^= F192Unreduced::from(lx[p]);
                        }
                    } else {
                        let c = self.coefs[(oc >> 2) as usize];
                        for p in 0..np {
                            sub[p] ^= lx[p].mul_unreduced(c);
                        }
                    }
                    j += 1;
                }
                let ly = &tb.y.lo[0][(y & ym) as usize * np..][..np];
                for p in 0..np {
                    run[p] ^= sub[p].reduce().mul_unreduced(ly[p]);
                    sub[p] = F192Unreduced::ZERO;
                }
            }
            let (hx, hy) = (&tb.x.hi[0][xh as usize * np..][..np], &tb.y.hi[0][yh as usize * np..][..np]);
            for p in 0..np {
                out[o as usize * np + p] += run[p].reduce() * hx[p] * hy[p];
                run[p] = F192Unreduced::ZERO;
            }
            i = j;
        }
    }
}

/// R9-TY: split the point entries (sorted by `(o, x ≫ xs, y ≫ ys, x, y)`) into the groups kept x-major and the ones
/// with fewer distinct `y` than `x` (re-sorted by `(o, x ≫ xs, y ≫ ys, y, x)`).
fn split_major(pt: Vec<(u32, u32, u32)>, xs: usize, ys: usize) -> (Vec<(u32, u32, u32)>, Vec<(u32, u32, u32)>) {
    let grp = |e: &(u32, u32, u32)| (e.2 & 3, e.0 >> xs, e.1 >> ys);
    let (mut px, mut py) = (Vec::with_capacity(pt.len()), Vec::new());
    let mut i = 0;
    while i < pt.len() {
        let g = grp(&pt[i]);
        let mut j = i;
        while j < pt.len() && grp(&pt[j]) == g {
            j += 1;
        }
        let nx = 1 + pt[i..j].windows(2).filter(|w| w[0].0 != w[1].0).count();
        let mut yv: Vec<u32> = pt[i..j].iter().map(|e| e.1).collect();
        yv.sort_unstable();
        yv.dedup();
        if yv.len() < nx { py.extend_from_slice(&pt[i..j]) } else { px.extend_from_slice(&pt[i..j]) }
        i = j;
    }
    py.sort_unstable_by_key(|&(x, y, oc)| (oc & 3, x >> xs, y >> ys, y, x));
    (px, py)
}

/// The products of one pass per point (its loops in [`PhiK::eval_pass`], counted).
fn pass_cost(sh: &Shape, ps: &Pass, mem: &[Mem]) -> usize {
    let mut cost: usize = mem[ps.mlo as usize..ps.mhi as usize].iter().map(|m| 2 + m.mask.count_ones() as usize).sum();
    let (mut lo, mut hi) = (0i64, ps.span as i64);
    let mut li = 0;
    for k in 0..sh.kstop as usize {
        let bits: &[(u8, i64)] = if li < sh.levels.len() && sh.levels[li].0 as usize == k {
            li += 1;
            &sh.levels[li - 1].1
        } else {
            &[]
        };
        let (neg, pos): (i64, i64) = bits.iter().fold((0, 0), |(n, p), &(_, c)| if c < 0 { (n + c, p) } else { (n, p + c) });
        cost += ((hi - lo + 1) as usize) << bits.len();
        if bits.len() >= 2 {
            cost += (2 + bits.len()) << bits.len();
        }
        let ybit = 1;
        lo = (lo + neg).div_euclid(2);
        hi = (hi + ybit + pos).div_euclid(2);
    }
    cost + 2 * (hi - lo + 1) as usize
}

/// Split a piece's coefficients into the runs of one dimension (`c_{i+1} = 2·c_i`): the automaton keeps the runs whose
/// odd part is 1 and the longest other run; the remaining runs' bits are returned to be enumerated (their
/// coefficients zeroed in the kept vector).
fn split_runs(cv: &[i64]) -> (Vec<i64>, Vec<usize>) {
    let mut runs: Vec<(usize, usize)> = Vec::new();
    let mut i = 0;
    while i < cv.len() {
        if cv[i] == 0 {
            i += 1;
            continue;
        }
        let mut j = i + 1;
        while j < cv.len() && cv[j] == 2 * cv[j - 1] {
            j += 1;
        }
        runs.push((i, j));
        i = j;
    }
    let odd = |r: &(usize, usize)| cv[r.0].unsigned_abs() >> cv[r.0].trailing_zeros();
    let keep = runs.iter().filter(|r| odd(r) > 1).max_by_key(|r| (r.1 - r.0, std::cmp::Reverse(odd(r)))).copied();
    let mut cv2 = cv.to_vec();
    let mut en = Vec::new();
    for r in &runs {
        if odd(r) > 1 && Some(*r) != keep {
            for b in r.0..r.1 {
                cv2[b] = 0;
                en.push(b);
            }
        }
    }
    (cv2, en)
}

/// Cut `[a, a + 2^ell)` into aligned sub-cubes on which `y` is affine in the free bits: `(a, ℓ', y0, c)`.
fn decompose(y: &dyn Fn(usize) -> i64, a: usize, ell: usize, out: &mut Vec<(usize, usize, i64, Vec<i64>)>) {
    let y0 = y(a);
    if ell == 0 {
        out.push((a, 0, y0, Vec::new()));
        return;
    }
    let cv: Vec<i64> = (0..ell).map(|i| y(a + (1 << i)) - y0).collect();
    let mut pred = vec![0i64; 1 << ell];
    pred[0] = y0;
    let mut ok = true;
    for j in 1..1usize << ell {
        let tz = j.trailing_zeros() as usize;
        pred[j] = pred[j & (j - 1)] + cv[tz];
        if pred[j] != y(a + j) {
            ok = false;
            break;
        }
    }
    if ok {
        out.push((a, ell, y0, cv));
    } else {
        decompose(y, a, ell - 1, out);
        decompose(y, a + (1 << (ell - 1)), ell - 1, out);
    }
}

/// The K1 pattern `[(i, k)]` of an affine piece when it is a bit injection that misses `y0` (no carry), else `None`.
fn k1_pattern(y0: i64, cv: &[i64], y_log: usize) -> Option<Vec<(u8, u8)>> {
    if y0 < 0 {
        return None;
    }
    let mut used = y0 as u64;
    let mut pat = Vec::new();
    for (i, &c) in cv.iter().enumerate() {
        if c == 0 {
            continue;
        }
        if c < 0 || !(c as u64).is_power_of_two() {
            return None;
        }
        let k = c.trailing_zeros();
        if k as usize >= y_log || used >> k & 1 == 1 {
            return None;
        }
        used |= 1 << k;
        pat.push((i as u8, k as u8));
    }
    Some(pat)
}

fn levels_ok(cv: &[i64]) -> bool {
    let mut cnt: HashMap<u32, usize> = HashMap::new();
    for &c in cv.iter().filter(|&&c| c != 0) {
        *cnt.entry(c.trailing_zeros()).or_default() += 1;
    }
    cnt.values().all(|&n| n <= MAX_LEVEL_BITS)
}

fn shape_of(ell: u8, cv: &[i64]) -> Shape {
    let mut by: std::collections::BTreeMap<u8, Vec<(u8, i64)>> = std::collections::BTreeMap::new();
    for (i, &c) in cv.iter().enumerate() {
        if c != 0 {
            let k = c.trailing_zeros() as u8;
            by.entry(k).or_default().push((i as u8, c >> k));
        }
    }
    let kstop = by.keys().next_back().map_or(0, |&k| k + 1);
    Shape { ell, levels: by.into_iter().collect(), kstop }
}
