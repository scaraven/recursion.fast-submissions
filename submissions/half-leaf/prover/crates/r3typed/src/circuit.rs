//! The circuit `Q` of the typed phases (FORMAT6 v2.4 §6.4a; Lean `Lvm6.Ty.TInst6`, `relE`, `PhiQE`, `virtE`,
//! `relayKernE`, `regClaimE`): four matrices `M_0 … M_3` (`A`, `B`, `D`, `W`) over `2^20` slots × `2^21` words with
//! `E` coefficients, and the word space's regions.
//!
//! - **Relation** (`relE`): at every slot `x`, `(M_0 z)(x)·(M_1 z)(x) + (M_2 z)(x) + (M_3 z)(x) = 0` in `E`, with
//!   `z : 2^21 → K` the words.
//! - **Words** (`zOf`): a word's value comes from its region's source: `com` (a stack word: the typed result memory
//!   `T`), `ks` (a stack word: the `KS` aliases), `sflat`, `sigma` (a word of `C_rec`'s window), `pub` (the public
//!   header lanes), `qlt` (public constants), `one` (the constant 1); a word in no region is 0.
//! - **`Φ_Q`** (`PhiQE`): `Σ_e c_e·eq(pt, o_e + 4·(x_e + 2^20·y_e))` in `43 = 2 + 20 + 21` variables.
//!
//! Every region is a season-1 `TReg` (`typed_prove.rs`): `2^log` words from `base`, word `base + i` ↔ target
//! `off + i`, with `base` and `off` multiples of `2^log` (season 1's blobs satisfy it; it makes every region term
//! of `virt`, `kern` and the region claims' weights a product of `eq`s, `O(25)` for `V`).
//!
//! **The blob** (a text file, season 1's token form, `typed_blob.rs`): `Q6 1`, then
//! - `TYPED n {src base log off}` (as season 1's `TYPED` regions; `com`/`ks` targets are stack indices
//!   `r + 2^19·slot`, `sflat`/`sigma` targets are `C_rec` words `< 2^19`),
//! - `ENTS n {o x y c0 c1}` (the matrices; season 1 carried the LoopIR program and compiled it, CD's generator
//!   emits the entries),
//! - `OUT n {x y}` (the witness order: row `x` defines word `y`, which occurs only in `M_2`/`M_3` of that row;
//!   season 1 ran the LoopIR program instead),
//! - `CONST n {lo len values…}` (as season 1: `QLT`'s words `lo …`),
//! - `END`.
//!
//! The circuit in use is [`circuit`]: the one [`install`]ed, else the blob at `$LVM6_Q_BLOB`, else the synthetic
//! stub ([`crate::stub::generate`]).

use std::sync::OnceLock;

use primitives::field::{F64, F128};
use primitives::multilinear::eq_table;
use r3core::layout;

/// `r_x`'s coordinates (slots).
pub const X_VARS: usize = fs6::params::TY_X;
/// `r_y`'s coordinates (words).
pub const Y_VARS: usize = fs6::params::TY_Y;
/// The relayout's rounds: `C_rec`'s window is `2^19` words (`P18`), `2^18` (`P17`): one stack slot.
pub const REC_VARS: usize = fs6::params::TY_RELAYOUT;
const _: () = assert!(REC_VARS == layout::ROW_LOG);
/// `Φ_Q`'s selector bits (`κ ∈ E^2`, four matrices).
pub const SEL_BITS: usize = 2;
/// `Φ_Q`'s variables: `2 + 20 + 21 = 43` (`HDR.accIn.pt ∈ E^43`).
pub const PHI_VARS: usize = SEL_BITS + X_VARS + Y_VARS;
const _: () = assert!(PHI_VARS == fs6::params::SHAPE.phi_vars);

/// `C_rec`'s window on the stack: the block of `2^REC_VARS` words at block offset `REC_OFF` (slot 33, `STREAM`;
/// STUB: CD fixes the window, FORMAT6 §6.4 "claims"). A `C_rec` word `w` is stack index `REC_BASE + w`.
pub const REC_OFF: usize = layout::SLOT_STREAM;
pub const REC_BASE: usize = REC_OFF << REC_VARS;

/// A region's source (Lean `YSrc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Src {
    Com,
    Ks,
    Sflat,
    Sigma,
    Pub,
    Qlt,
    One,
}

impl Src {
    pub fn name(self) -> &'static str {
        match self {
            Src::Com => "com",
            Src::Ks => "ks",
            Src::Sflat => "sflat",
            Src::Sigma => "sigma",
            Src::Pub => "pub",
            Src::Qlt => "qlt",
            Src::One => "one",
        }
    }

    pub fn parse(s: &str) -> Option<Src> {
        [Src::Com, Src::Ks, Src::Sflat, Src::Sigma, Src::Pub, Src::Qlt, Src::One].into_iter().find(|x| x.name() == s)
    }

    /// Whether the target is a stack word (`com`, `ks`) or a `C_rec` word (`sflat`, `sigma`).
    pub fn committed(self) -> bool {
        matches!(self, Src::Com | Src::Ks | Src::Sflat | Src::Sigma)
    }
}

/// A region: words `base … base + 2^log − 1` ↔ targets `off …` (`off` unused for `pub`, `qlt`, `one`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TReg {
    pub src: Src,
    pub base: usize,
    pub log: usize,
    pub off: usize,
}

impl TReg {
    pub fn len(&self) -> usize {
        1 << self.log
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    /// The stack index of the target of word `base + i` (committed sources).
    pub fn stack_idx(&self, i: usize) -> usize {
        match self.src {
            Src::Com | Src::Ks => self.off + i,
            Src::Sflat | Src::Sigma => REC_BASE + self.off + i,
            _ => panic!("region {:?} has no stack target", self.src),
        }
    }
}

/// A matrix entry: `M_o[x][y] += c`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ent {
    pub o: u8,
    pub x: u32,
    pub y: u32,
    pub c: F128,
}

impl Ent {
    /// The entry's index on `Φ_Q`'s cube (Lean `EntT.idxE`): `o + 4·(x + 2^20·y)`.
    pub fn idx(&self) -> u64 {
        self.o as u64 + 4 * (self.x as u64 + ((self.y as u64) << X_VARS))
    }
}

/// The circuit `Q` (a swappable input).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit {
    pub regs: Vec<TReg>,
    /// Sorted by `(x, o, y)`, no duplicate `(o, x, y)`, no zero coefficient ([`Circuit::normalize`]).
    pub ents: Vec<Ent>,
    /// The witness order: `(x, y)`, row `x` defines word `y`.
    pub outs: Vec<(u32, u32)>,
    /// `QLT`'s words: `(lo, values)`, word `lo + i` holds `values[i]`.
    pub qlt: Vec<(usize, Vec<u64>)>,
}

/// `eq(r, bits(v))`, `|r|` bits of `v`, low first (Lean `eqAtF`).
pub fn eq_bits(r: &[F128], v: usize) -> F128 {
    r.iter().enumerate().fold(F128::ONE, |a, (i, &ri)| a * if v >> i & 1 == 1 { ri } else { F128::ONE + ri })
}

/// `eq(l, r) = Π (1 + l_i + r_i)`.
pub fn eq2(l: &[F128], r: &[F128]) -> F128 {
    assert_eq!(l.len(), r.len());
    l.iter().zip(r).fold(F128::ONE, |a, (&x, &y)| a * (F128::ONE + x + y))
}

/// The four matrices' weights of the wiring batch: `1, γ, γ², γ²` (Lean `wGE`).
pub fn mat_weights(gamma: F128) -> [F128; 4] {
    let g2 = gamma * gamma;
    [F128::ONE, gamma, g2, g2]
}

impl Circuit {
    /// Sort the entries by `(x, o, y)`, merge duplicates, drop zeros.
    pub fn normalize(&mut self) {
        self.ents.sort_by_key(|e| (e.x, e.o, e.y));
        let mut out: Vec<Ent> = Vec::with_capacity(self.ents.len());
        for e in self.ents.drain(..) {
            match out.last_mut() {
                Some(l) if (l.x, l.o, l.y) == (e.x, e.o, e.y) => l.c += e.c,
                _ => out.push(e),
            }
        }
        out.retain(|e| !e.c.is_zero());
        self.ents = out;
        self.regs.sort_by_key(|r| r.base);
    }

    /// The static checks (panics with the first violation): shapes, alignment, disjoint regions, targets inside
    /// their windows, `com` targets inside `T`, every output word a `com` word that the row's `A`/`B` do not read.
    pub fn check(&self) {
        let ny = 1usize << Y_VARS;
        for (k, r) in self.regs.iter().enumerate() {
            assert!(r.base % r.len() == 0 && r.base + r.len() <= ny, "region {k} {r:?}: base");
            if k > 0 {
                let p = &self.regs[k - 1];
                assert!(p.base + p.len() <= r.base, "regions {} and {k} overlap", k - 1);
            }
            match r.src {
                Src::Com | Src::Ks | Src::Sflat | Src::Sigma => assert!(r.off % r.len() == 0, "region {k} {r:?}: target alignment"),
                _ => {}
            }
            match r.src {
                Src::Com => {
                    let (lo, hi) = (r.off, r.off + r.len());
                    assert!(lo >= layout::idx(layout::SLOT_T, 0) && hi <= layout::idx(layout::SLOT_T + layout::T_SLOTS, 0), "region {k}: com outside T");
                    // a `com` region may cover `X`'s words (CD places `X` in `T`): the witness then writes `X`
                }
                Src::Ks => assert!(r.off + r.len() <= layout::LANES << layout::ROW_LOG, "region {k}: ks outside the stack"),
                Src::Sflat | Src::Sigma => assert!(r.off + r.len() <= 1 << REC_VARS, "region {k}: outside C_rec"),
                Src::One => {}
                Src::Pub | Src::Qlt => {}
            }
            // R9: the `σ` region (`σ'` and `σ_leaf`, 2^11 words) starts at `STREAM_SIG` (`sB`), which differs between
            // shapes: a circuit of another shape fails here (or on a window or `T` bound above)
            if r.src == Src::Sigma {
                assert!(r.off == layout::STREAM_SIG, "region {k} {r:?}: sigma not at sB = {}", layout::STREAM_SIG);
            }
        }
        assert!(self.regs.iter().filter(|r| r.src == Src::One).count() >= 1, "no one region");
        for w in self.ents.windows(2) {
            assert!((w[0].x, w[0].o, w[0].y) < (w[1].x, w[1].o, w[1].y), "entries not normalized");
        }
        for e in &self.ents {
            assert!(e.o < 4 && (e.x as usize) < 1 << X_VARS && (e.y as usize) < ny && !e.c.is_zero(), "entry {e:?}");
        }
        let mut defined = std::collections::HashSet::new();
        for &(x, y) in &self.outs {
            assert!(matches!(self.src_of(y as usize), Some((Src::Com, _))), "out ({x}, {y}): not a com word");
            assert!(defined.insert(y), "out word {y} defined twice");
            let row = self.row(x);
            assert!(row.iter().all(|e| e.o >= 2 || e.y != y), "out ({x}, {y}): read by A or B");
            assert!(row.iter().any(|e| e.o >= 2 && e.y == y), "out ({x}, {y}): not in C");
        }
    }

    /// Row `x`'s entries.
    pub fn row(&self, x: u32) -> &[Ent] {
        let lo = self.ents.partition_point(|e| e.x < x);
        let hi = self.ents.partition_point(|e| e.x <= x);
        &self.ents[lo..hi]
    }

    /// The region of word `y` and its index in it.
    pub fn src_of(&self, y: usize) -> Option<(Src, usize)> {
        let k = self.regs.partition_point(|r| r.base <= y);
        let r = self.regs.get(k.checked_sub(1)?)?;
        (y < r.base + r.len()).then_some((r.src, y - r.base))
    }

    pub fn regs_of(&self, s: Src) -> impl Iterator<Item = &TReg> {
        self.regs.iter().filter(move |r| r.src == s)
    }

    /// `QLT`'s value of word `y` (0 if unset).
    pub fn qlt_word(&self, y: usize) -> u64 {
        for (lo, v) in &self.qlt {
            if (*lo..lo + v.len()).contains(&y) {
                return v[y - lo];
            }
        }
        0
    }

    /// `Φ_Q(pt)` (Lean `PhiQE`), `pt ∈ E^43` (selector, `x`, `y`; low bit first): five small `eq` tables, five
    /// products an entry.
    pub fn phi_q(&self, pt: &[F128]) -> F128 {
        assert_eq!(pt.len(), PHI_VARS);
        let (s, x, y) = (&pt[..SEL_BITS], &pt[SEL_BITS..SEL_BITS + X_VARS], &pt[SEL_BITS + X_VARS..]);
        let (xh, yh) = (X_VARS / 2, Y_VARS / 2);
        let t = PhiTabs {
            o: eq_table(s),
            xl: eq_table(&x[..xh]),
            xh: eq_table(&x[xh..]),
            yl: eq_table(&y[..yh]),
            yh: eq_table(&y[yh..]),
        };
        const CH: usize = 1 << 14;
        let parts = parallel::map_collect(self.ents.len().div_ceil(CH), |c| {
            let es = &self.ents[c * CH..((c + 1) * CH).min(self.ents.len())];
            es.iter().fold(F128::ZERO, |a, e| {
                let (xv, yv) = (e.x as usize, e.y as usize);
                a + e.c * t.o[e.o as usize] * t.xl[xv & ((1 << xh) - 1)] * t.xh[xv >> xh] * t.yl[yv & ((1 << yh) - 1)] * t.yh[yv >> yh]
            })
        });
        parts.into_iter().fold(F128::ZERO, |a, b| a + b)
    }

    /// `Φ_Q` at every point of `pts` in one pass over the entries (R5, PATCHES.md): what [`Circuit::phi_q`] gives
    /// point by point. The points go eight to a vector (`F128x8`): the five `eq` tables are laid out index-major,
    /// the points' values of one index side by side. The entries are sorted by `(x, o, y)`: a run of one `(x, o)`
    /// sums `c·eq(y)` (two vector products an entry per eight points) and multiplies by `eq(o)·eq(x)` once; the pool
    /// takes chunks of entries (a run cut by a chunk boundary is summed in both parts).
    pub fn phi_q_many(&self, pts: &[Vec<F128>]) -> Vec<F128> {
        use primitives::field::F128x8;
        let (xh, yh) = (X_VARS / 2, Y_VARS / 2);
        let n = pts.len();
        let nv = n.div_ceil(8);
        let tabs: Vec<PhiTabs> = parallel::map_collect(n, |k| {
            let pt = &pts[k];
            assert_eq!(pt.len(), PHI_VARS);
            let (s, x, y) = (&pt[..SEL_BITS], &pt[SEL_BITS..SEL_BITS + X_VARS], &pt[SEL_BITS + X_VARS..]);
            PhiTabs { o: eq_table(s), xl: eq_table(&x[..xh]), xh: eq_table(&x[xh..]), yl: eq_table(&y[..yh]), yh: eq_table(&y[yh..]) }
        });
        // `t[i·nv + v]`: lane `j` = point `8v + j`'s entry `i` (zero past the points).
        let wide = |get: &dyn Fn(&PhiTabs) -> &Vec<F128>| -> Vec<F128x8> {
            let len = tabs.first().map_or(0, |t| get(t).len());
            (0..len * nv)
                .map(|k| {
                    let (i, v) = (k / nv, k % nv);
                    F128x8::from_array(&std::array::from_fn(|j| tabs.get(8 * v + j).map_or(F128::ZERO, |t| get(t)[i])))
                })
                .collect()
        };
        let (wo, wxl, wxh, wyl, wyh) = (wide(&|t| &t.o), wide(&|t| &t.xl), wide(&|t| &t.xh), wide(&|t| &t.yl), wide(&|t| &t.yh));
        const CH: usize = 1 << 12;
        let (xm, ym) = ((1usize << xh) - 1, (1usize << yh) - 1);
        let zero = F128x8::splat(F128::ZERO);
        let parts = parallel::map_collect(self.ents.len().div_ceil(CH), |c| {
            let es = &self.ents[c * CH..((c + 1) * CH).min(self.ents.len())];
            let mut acc = vec![zero; nv];
            let mut inner = vec![zero; nv];
            let mut i = 0;
            while i < es.len() {
                let (x, o) = (es[i].x, es[i].o);
                inner.iter_mut().for_each(|v| *v = zero);
                while i < es.len() && es[i].x == x && es[i].o == o {
                    let yv = es[i].y as usize;
                    let cc = F128x8::splat(es[i].c);
                    let (l, h) = (&wyl[(yv & ym) * nv..][..nv], &wyh[(yv >> yh) * nv..][..nv]);
                    for v in 0..nv {
                        inner[v] = inner[v] + cc * l[v] * h[v];
                    }
                    i += 1;
                }
                let xv = x as usize;
                let (wo, l, h) = (&wo[o as usize * nv..][..nv], &wxl[(xv & xm) * nv..][..nv], &wxh[(xv >> xh) * nv..][..nv]);
                for v in 0..nv {
                    acc[v] = acc[v] + wo[v] * l[v] * h[v] * inner[v];
                }
            }
            acc.into_iter().flat_map(|a| a.to_array()).take(n).collect::<Vec<F128>>()
        });
        parts.into_iter().fold(vec![F128::ZERO; n], |mut a, p| {
            a.iter_mut().zip(p).for_each(|(a, p)| *a += p);
            a
        })
    }

    /// `Φ_Q(pt)` entry by entry (`eqWT pt (idxE e)`, 43 factors an entry): the verifier's form, independent of
    /// [`Circuit::phi_q`]'s tables.
    pub fn phi_q_direct(&self, pt: &[F128]) -> F128 {
        assert_eq!(pt.len(), PHI_VARS);
        self.ents.iter().fold(F128::ZERO, |a, e| {
            let idx = e.idx();
            a + e.c * pt.iter().enumerate().fold(F128::ONE, |p, (i, &r)| p * if idx >> i & 1 == 1 { r } else { F128::ONE + r })
        })
    }

    /// The public part of `z̃(r_y)` (Lean `virtE`): `Σ eq(r_y, y)·z(y)` over the `pub`, `qlt` and `one` regions;
    /// `pub`'s word `base + i` is `pub_words[i]` (0 past it).
    pub fn virt(&self, ry: &[F128], pub_words: &[u64]) -> F128 {
        assert_eq!(ry.len(), Y_VARS);
        let mut acc = F128::ZERO;
        for r in &self.regs {
            let hi = eq_bits(&ry[r.log..], r.base >> r.log);
            match r.src {
                Src::One => acc += hi,
                Src::Pub | Src::Qlt => {
                    let lo = eq_table(&ry[..r.log]);
                    let s = (0..r.len()).fold(F128::ZERO, |a, i| {
                        let w = if r.src == Src::Pub { pub_words.get(i).copied().unwrap_or(0) } else { self.qlt_word(r.base + i) };
                        a + lo[i].mul_base(F64(w))
                    });
                    acc += hi * s;
                }
                _ => {}
            }
        }
        acc
    }

    /// The relayout's kernel (Lean `relayKernE`): `Σ_{y ∈ sflat} eq(r_y, y)·eq(r, sflatW(y))`, `r ∈ E^REC_VARS`.
    pub fn relay_kern(&self, ry: &[F128], r: &[F128]) -> F128 {
        assert_eq!((ry.len(), r.len()), (Y_VARS, REC_VARS));
        self.regs_of(Src::Sflat).fold(F128::ZERO, |a, g| {
            a + eq2(&ry[..g.log], &r[..g.log]) * eq_bits(&ry[g.log..], g.base >> g.log) * eq_bits(&r[g.log..], g.off >> g.log)
        })
    }

    /// The weight of `s`'s region claim (Lean `regClaimE`) at a stack point `pt ∈ E^25`:
    /// `Σ_{y ∈ s} eq(r_y, y)·eq(pt, stackIdx(y))`, a product of `eq`s per region.
    pub fn region_weight_at(&self, s: Src, ry: &[F128], pt: &[F128]) -> F128 {
        assert_eq!((ry.len(), pt.len()), (Y_VARS, layout::STACK_LOG));
        self.regs_of(s).fold(F128::ZERO, |a, g| {
            a + eq2(&ry[..g.log], &pt[..g.log]) * eq_bits(&ry[g.log..], g.base >> g.log) * eq_bits(&pt[g.log..], g.stack_idx(0) >> g.log)
        })
    }

    /// The smallest aligned stack block `(off, μ)` holding every target of `s`'s regions.
    pub fn region_block(&self, s: Src) -> (usize, usize) {
        let regs: Vec<&TReg> = self.regs_of(s).collect();
        assert!(!regs.is_empty(), "no {s:?} region");
        let lo = regs.iter().map(|g| g.stack_idx(0)).min().unwrap();
        let hi = regs.iter().map(|g| g.stack_idx(0) + g.len()).max().unwrap() - 1;
        let mut mu = regs.iter().map(|g| g.log).max().unwrap();
        while lo >> mu != hi >> mu {
            mu += 1;
        }
        (lo >> mu, mu)
    }

    // ------------------------------------------------------------------------------------------------ the blob

    /// The blob text (see the module docs).
    pub fn to_blob(&self) -> String {
        use std::fmt::Write;
        let mut s = String::new();
        writeln!(s, "Q6 1").unwrap();
        writeln!(s, "TYPED {}", self.regs.len()).unwrap();
        for r in &self.regs {
            writeln!(s, "{} {} {} {}", r.src.name(), r.base, r.log, r.off).unwrap();
        }
        writeln!(s, "ENTS {}", self.ents.len()).unwrap();
        for e in &self.ents {
            writeln!(s, "{} {} {} {} {}", e.o, e.x, e.y, e.c.c0, e.c.c1).unwrap();
        }
        writeln!(s, "OUT {}", self.outs.len()).unwrap();
        for (x, y) in &self.outs {
            writeln!(s, "{x} {y}").unwrap();
        }
        write!(s, "CONST {}", self.qlt.len()).unwrap();
        for (lo, v) in &self.qlt {
            write!(s, "\n{lo} {}", v.len()).unwrap();
            for w in v {
                write!(s, " {w}").unwrap();
            }
        }
        writeln!(s, "\nEND").unwrap();
        s
    }

    /// Parse a blob; normalizes and [`Circuit::check`]s it. An optional `MINIBUS` section is skipped (r3mb's,
    /// [`parse_minibus`]); an optional trailing `CHECKSUM <hex>` is verified;
    /// `#` lines are comments.
    pub fn from_blob(text: &str) -> Circuit {
        let body = uncommented(checked_body(text));
        let mut t = body.split_ascii_whitespace();
        let mut word = || t.next().expect("Q6 blob: truncated");
        assert_eq!((word(), word()), ("Q6", "1"), "Q6 blob: header");
        assert_eq!(word(), "TYPED");
        let n: usize = num(word());
        let regs = (0..n)
            .map(|_| {
                let src = Src::parse(word()).expect("Q6 blob: region source");
                TReg { src, base: num(word()), log: num(word()), off: num(word()) }
            })
            .collect();
        assert_eq!(word(), "ENTS");
        let n: usize = num(word());
        let ents = (0..n).map(|_| Ent { o: num(word()), x: num(word()), y: num(word()), c: F128::new(num(word()), num(word())) }).collect();
        assert_eq!(word(), "OUT");
        let n: usize = num(word());
        let outs = (0..n).map(|_| (num(word()), num(word()))).collect();
        assert_eq!(word(), "CONST");
        let n: usize = num(word());
        let qlt = (0..n)
            .map(|_| {
                let lo = num(word());
                let len: usize = num(word());
                (lo, (0..len).map(|_| num(word())).collect())
            })
            .collect();
        // optional sections, each at most once, in any order (R7: `BITS`)
        let mut seen: Vec<&str> = Vec::new();
        let mut tag = word();
        while tag != "END" {
            assert!(!seen.contains(&tag), "Q6 blob: section {tag} twice");
            match tag {
                "MINIBUS" => {
                    let (ns, nr): (usize, usize) = (num(word()), num(word()));
                    for k in 0..ns + nr {
                        let limbs: usize = num(word());
                        let len = if k < ns { 4 + limbs } else { 3 + limbs };
                        (0..len).for_each(|_| _ = word());
                    }
                }
                "POWBITS" => {
                    let n: usize = num(word());
                    (0..3 * n).for_each(|_| _ = word());
                }
                "BITS" => {
                    let n: usize = num(word());
                    for _ in 0..n {
                        let _y = word();
                        let nb: usize = num(word());
                        (0..nb).for_each(|_| _ = word());
                    }
                }
                "BOUT" => {
                    let n: usize = num(word());
                    (0..4 * n).for_each(|_| _ = word());
                }
                "CSUM" => {
                    let n: usize = num(word());
                    (0..n * (1 + CSUM_BITS + 2 * CSUM_CHAINS)).for_each(|_| _ = word());
                }
                "XSRC" => {
                    let n: usize = num(word());
                    (0..3 * n).for_each(|_| _ = word());
                }
                t => panic!("Q6 blob: unknown section {t:?}"),
            }
            seen.push(tag);
            tag = word();
        }
        assert!(t.next().is_none(), "Q6 blob: nothing after END but CHECKSUM");
        let mut c = Circuit { regs, ents, outs, qlt };
        c.normalize();
        c.check();
        c
    }
}

fn num<T: std::str::FromStr>(w: &str) -> T {
    w.parse().unwrap_or_else(|_| panic!("Q6 blob: number {w:?}"))
}

/// The blob without its `CHECKSUM` line, which (if present) must be the Keccak-256 of every byte before it.
fn checked_body(text: &str) -> &str {
    match text.rfind("CHECKSUM") {
        None => text,
        Some(at) => {
            let want = text[at + 8..].trim();
            let got: String = keccak256::hash(&text.as_bytes()[..at]).iter().map(|b| format!("{b:02x}")).collect();
            assert_eq!(want, got, "Q6 blob: CHECKSUM");
            &text[..at]
        }
    }
}

/// The blob without its `#` comment lines.
fn uncommented(text: &str) -> String {
    text.lines().filter(|l| !l.trim_start().starts_with('#')).collect::<Vec<_>>().join("\n")
}

/// The blob's `CHECKSUM` line for `text` (everything before it).
pub fn checksum_line(text: &str) -> String {
    let h: String = keccak256::hash(text.as_bytes()).iter().map(|b| format!("{b:02x}")).collect();
    format!("CHECKSUM {h}\n")
}

/// The `MINIBUS` section (EXPORT.md): seeds `limbs base stride tau v_0 … v_{limbs−1} fin` and reads
/// `limbs tau addr v_0 … v_{limbs−1} cnt`, every column a stack index (`2^tau`-aligned). For r3mb's loader.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MbExport {
    /// `(limbs, base, stride, tau, value columns, finalize column)`.
    pub seeds: Vec<(usize, usize, usize, usize, Vec<usize>, usize)>,
    /// `(limbs, tau, address column, value columns, count column)`.
    pub reads: Vec<(usize, usize, usize, Vec<usize>, usize)>,
}

/// The blob's `MINIBUS` section, if any.
pub fn parse_minibus(text: &str) -> Option<MbExport> {
    let body = uncommented(checked_body(text));
    let mut t = body.split_ascii_whitespace().skip_while(|w| *w != "MINIBUS");
    t.next()?;
    let mut word = || t.next().expect("Q6 blob: MINIBUS truncated");
    let (ns, nr): (usize, usize) = (num(word()), num(word()));
    let mut m = MbExport::default();
    for _ in 0..ns {
        let (limbs, base, stride, tau) = (num(word()), num(word()), num(word()), num(word()));
        let v = (0..limbs).map(|_| num(word())).collect();
        m.seeds.push((limbs, base, stride, tau, v, num(word())));
    }
    for _ in 0..nr {
        let (limbs, tau, addr) = (num(word()), num(word()), num(word()));
        let v = (0..limbs).map(|_| num(word())).collect();
        m.reads.push((limbs, tau, addr, v, num(word())));
    }
    Some(m)
}

struct PhiTabs {
    o: Vec<F128>,
    xl: Vec<F128>,
    xh: Vec<F128>,
    yl: Vec<F128>,
    yh: Vec<F128>,
}

// ---------------------------------------------------------------------------------------- the circuit in use

/// A run of PoW bit words (LAY's `POWBITS`, EXPORT.md): word `bw + i` is bit `i` of `STREAM` word `w` (the child's
/// PoW lane), `i < nb = 64 − g`. Free words of `T`, not in `OUT`: the witness writes them from `C_rec` first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PowBits {
    pub w: usize,
    pub bw: usize,
    pub nb: usize,
}

/// A `POWBITS n` section (`w bw nb` lines) in `text` (a blob, or a sidecar `POWBITS n … END`), if any.
pub fn parse_powbits(text: &str) -> Option<Vec<PowBits>> {
    let body = uncommented(checked_body(text));
    let mut t = body.split_ascii_whitespace().skip_while(|w| *w != "POWBITS");
    t.next()?;
    let mut word = || t.next().expect("Q6 blob: POWBITS truncated");
    let n: usize = num(word());
    Some((0..n).map(|_| PowBits { w: num(word()), bw: num(word()), nb: num(word()) }).collect())
}

/// A BITS aux row (F2, R7's `BITS` section): word `dst[i]` (if any) is bit `i` of word `y` (any word, an `OUT` word
/// included: the witness writes the bits once `y` is known, in the rows' dependency order). The `dst` are free
/// `com` words, not in `OUT`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuxBits {
    pub y: u32,
    pub dst: Vec<Option<u32>>,
}

/// A `BITS n` section (`y nb d_0 … d_{nb−1}` lines, `-` for an unused bit) in `text`, if any.
pub fn parse_bits(text: &str) -> Option<Vec<AuxBits>> {
    let body = uncommented(checked_body(text));
    let mut t = body.split_ascii_whitespace().skip_while(|w| *w != "BITS");
    t.next()?;
    let mut word = || t.next().expect("Q6 blob: BITS truncated");
    let n: usize = num(word());
    Some(
        (0..n)
            .map(|_| {
                let y = num(word());
                let nb: usize = num(word());
                assert!(nb <= 64, "Q6 blob: BITS row of {nb} bits");
                AuxBits { y, dst: (0..nb).map(|_| Some(word()).filter(|w| *w != "-").map(num)).collect() }
            })
            .collect(),
    )
}

/// A `BOUT` line (NODE3's F2 export, Lean `LvmBits.BOut.word`): word `d` := `f_{k,a}` of word `y` (as `u64`):
/// `k = 0` `v << a`, `k = 1` `v >> a`, `k = 2` bit `a` of `v`, `k = 3` with `a = z + 64·m + 4096·dst`: the `m` bits of
/// `v` from bit `z`, placed at bit `dst` (all truncated to 64 bits).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BOut {
    pub y: u32,
    pub k: u8,
    pub a: u32,
    pub d: u32,
}

impl BOut {
    pub fn apply(&self, v: u64) -> u64 {
        let sh = |x: u64, n: u32| if n >= 64 { 0 } else { x << n };
        let sr = |x: u64, n: u32| if n >= 64 { 0 } else { x >> n };
        match self.k {
            0 => sh(v, self.a),
            1 => sr(v, self.a),
            2 => sr(v, self.a) & 1,
            3 => {
                let (z, m, dst) = (self.a % 64, (self.a / 64) % 64, self.a / 4096);
                let mask = if m >= 64 { u64::MAX } else { (1u64 << m) - 1 };
                sh(sr(v, z) & mask, dst)
            }
            k => panic!("BOUT kind {k}"),
        }
    }
}

/// A `BOUT m` section (`y k a d` lines) in `text`, if any.
pub fn parse_bout(text: &str) -> Option<Vec<BOut>> {
    let body = uncommented(checked_body(text));
    let mut t = body.split_ascii_whitespace().skip_while(|w| *w != "BOUT");
    t.next()?;
    let mut word = || t.next().expect("Q6 blob: BOUT truncated");
    let n: usize = num(word());
    Some((0..n).map(|_| BOut { y: num(word()), k: num(word()), a: num(word()), d: num(word()) }).collect())
}

/// The WOTS checksum's digit bits (`C = Σ_{i<128} (3 − d_i)`, 10 bits).
pub const CSUM_BITS: usize = 10;
/// The message chains whose digits the checksum sums.
pub const CSUM_CHAINS: usize = 128;

/// A `CSUM` line (NODE3's export, Q_sig's checksum class row `sCs`): `bw c_0 … c_9 bd_0 … bd_255`. With `d_i =
/// z[bd_2i] + 2·z[bd_2i+1]` and the integer `C = Σ_{i<128} (3 − d_i)`: word `bw + k` is bit `k` of `C` (`k < 64`), word
/// `c_k` is bit `k` of `C` (`k < 10`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Csum {
    pub bw: u32,
    pub c: Vec<u32>,
    pub bd: Vec<u32>,
}

impl Csum {
    /// `C` of the digit bit words' values.
    pub fn value(&self, z: &[F64]) -> u64 {
        (0..CSUM_CHAINS).map(|i| 3 - (z[self.bd[2 * i] as usize].0 & 1) - 2 * (z[self.bd[2 * i + 1] as usize].0 & 1)).sum()
    }

    /// The words it defines.
    pub fn outputs(&self) -> impl Iterator<Item = u32> + '_ {
        (self.bw..self.bw + 64).chain(self.c.iter().copied())
    }
}

/// A `CSUM n` section, if any.
pub fn parse_csum(text: &str) -> Option<Vec<Csum>> {
    let body = uncommented(checked_body(text));
    let mut t = body.split_ascii_whitespace().skip_while(|w| *w != "CSUM");
    t.next()?;
    let mut word = || t.next().expect("Q6 blob: CSUM truncated");
    let n: usize = num(word());
    Some(
        (0..n)
            .map(|_| Csum {
                bw: num(word()),
                c: (0..CSUM_BITS).map(|_| num(word())).collect(),
                bd: (0..2 * CSUM_CHAINS).map(|_| num(word())).collect(),
            })
            .collect(),
    )
}

/// An `XSRC n` section (`i l y`: the sponge message cell `X(i, l)` is word `y`), if any.
pub fn parse_xsrc(text: &str) -> Option<Vec<(usize, usize, u32)>> {
    let body = uncommented(checked_body(text));
    let mut t = body.split_ascii_whitespace().skip_while(|w| *w != "XSRC");
    t.next()?;
    let mut word = || t.next().expect("Q6 blob: XSRC truncated");
    let n: usize = num(word());
    Some((0..n).map(|_| (num(word()), num(word()), num(word()))).collect())
}

static CSUM: OnceLock<Vec<Csum>> = OnceLock::new();
static XSRC: OnceLock<Vec<(usize, usize, u32)>> = OnceLock::new();

/// The `CSUM` lines of `c` if it is the circuit in use, else none.
pub fn csum_of(c: &Circuit) -> &'static [Csum] {
    match CIRCUIT.get() {
        Some((cc, ..)) if std::ptr::eq(cc, c) => CSUM.get().map_or(&[], |v| v.as_slice()),
        _ => &[],
    }
}

/// The `XSRC` lines of `c` if it is the circuit in use, else none.
pub fn xsrc_of(c: &Circuit) -> &'static [(usize, usize, u32)] {
    match CIRCUIT.get() {
        Some((cc, ..)) if std::ptr::eq(cc, c) => XSRC.get().map_or(&[], |v| v.as_slice()),
        _ => &[],
    }
}

/// [`check_bits`] with `BOUT` lines too.
pub fn check_aux(c: &Circuit, pow: &[PowBits], bits: &[AuxBits], bout: &[BOut]) -> std::collections::HashSet<u32> {
    let mut taken = check_bits(c, pow, bits);
    for (k, b) in bout.iter().enumerate() {
        assert!(b.k <= 3 && (b.y as usize) < 1 << Y_VARS && b.y != b.d, "BOUT line {k}: {b:?}");
        // `LvmBits.BOut.Valid`: shifts and bits below 64; a field of `1 ≤ m` bits inside the word at both ends
        let (z, m, dst) = (b.a % 64, (b.a / 64) % 64, b.a / 4096);
        assert!(if b.k < 3 { b.a < 64 } else { m >= 1 && z + m <= 64 && dst + m <= 64 }, "BOUT line {k}: invalid {b:?}");
        assert!(matches!(c.src_of(b.d as usize), Some((Src::Com, _))), "BOUT line {k}: word {} not a com word", b.d);
        assert!(taken.insert(b.d), "BOUT line {k}: word {} defined twice", b.d);
    }
    taken
}

/// The aux-row words of `c` (`BITS`) checked against it: every destination a `com` word, defined once, not by
/// `OUT`, not a PoW bit word. Returns every defined word.
pub fn check_bits(c: &Circuit, pow: &[PowBits], bits: &[AuxBits]) -> std::collections::HashSet<u32> {
    let mut taken: std::collections::HashSet<u32> = c.outs.iter().map(|&(_, y)| y).collect();
    for p in pow {
        taken.extend((p.bw..p.bw + p.nb).map(|w| w as u32));
    }
    for (k, b) in bits.iter().enumerate() {
        assert!((b.y as usize) < 1 << Y_VARS, "BITS row {k}: source word");
        for &d in b.dst.iter().flatten() {
            assert!(d != b.y, "BITS row {k}: word {d} is its own source");
            assert!(matches!(c.src_of(d as usize), Some((Src::Com, _))), "BITS row {k}: word {d} not a com word");
            assert!(taken.insert(d), "BITS row {k}: word {d} defined twice");
        }
    }
    taken
}

type InUse = (Circuit, Vec<PowBits>, Vec<AuxBits>, Vec<BOut>);

static CIRCUIT: OnceLock<InUse> = OnceLock::new();

static MINIBUS: OnceLock<Option<MbExport>> = OnceLock::new();

/// The `MINIBUS` section of the blob in use (`$LVM6_Q_BLOB`), if any (R7: r3mb's real tables; none for the stub or
/// an [`install`]ed circuit).
pub fn minibus() -> Option<&'static MbExport> {
    circuit();
    MINIBUS.get_or_init(|| None).as_ref()
}

/// Install the circuit (CD's, once it exists) before the first [`circuit`] call. Panics if one is already in use.
pub fn install(c: Circuit) {
    install_with(c, Vec::new());
}

/// [`install`] with the circuit's PoW bit words.
pub fn install_with(c: Circuit, pow: Vec<PowBits>) {
    install_full(c, pow, Vec::new(), Vec::new());
}

/// [`install_with`] with the circuit's BITS aux rows.
pub fn install_full(c: Circuit, pow: Vec<PowBits>, bits: Vec<AuxBits>, bout: Vec<BOut>) {
    c.check();
    let _ = check_aux(&c, &pow, &bits, &bout);
    assert!(CIRCUIT.set((c, pow, bits, bout)).is_ok(), "a circuit is already installed");
}

/// The text blob at `p` with its sections and sidecar, checked (dev builds; `qpack`'s input).
pub fn load_text(p: &std::ffi::OsStr) -> crate::qbin::Loaded {
    let text = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("LVM6_Q_BLOB {p:?}: {e}"));
    if !text.contains("CHECKSUM") {
        eprintln!("r3typed: warning: LVM6_Q_BLOB {p:?} has no CHECKSUM line (accepted)");
    }
    let c = Circuit::from_blob(&text);
    // PoW bits: the blob's own section, else `$LVM6_Q_POW`, else `<blob stem>.pow` next to the blob
    let pow = parse_powbits(&text).or_else(|| {
        let side = std::env::var_os("LVM6_Q_POW").map(std::path::PathBuf::from).unwrap_or_else(|| std::path::Path::new(p).with_extension("pow"));
        let t = std::fs::read_to_string(&side).ok()?;
        eprintln!("r3typed: PoW bits from {}", side.display());
        Some(parse_powbits(&t).unwrap_or_else(|| panic!("{}: no POWBITS section", side.display())))
    });
    let l = crate::qbin::Loaded {
        c,
        pow: pow.unwrap_or_default(),
        bits: parse_bits(&text).unwrap_or_default(),
        bout: parse_bout(&text).unwrap_or_default(),
        csum: parse_csum(&text).unwrap_or_default(),
        xsrc: parse_xsrc(&text).unwrap_or_default(),
        minibus: parse_minibus(&text),
    };
    l.check();
    l
}

/// R8: the circuit in use comes from the embedded form in an `embedded-q` build (the setup's raw form, else the
/// embedded compact form; `$LVM6_Q_BLOB` is ignored), else from `$LVM6_Q_BLOB` (dev), else the synthetic stub.
fn load() -> InUse {
    let l = if crate::qbin::embedded().is_some() {
        if std::env::var_os("LVM6_Q_BLOB").is_some() {
            eprintln!("r3typed: warning: LVM6_Q_BLOB ignored: this build embeds its Q");
        }
        crate::qbin::load_embedded()
    } else if let Some(p) = std::env::var_os("LVM6_Q_BLOB") {
        load_text(&p)
    } else {
        let c = crate::stub::generate(crate::stub::SEED);
        crate::qbin::Loaded { c, pow: Vec::new(), bits: Vec::new(), bout: Vec::new(), csum: Vec::new(), xsrc: Vec::new(), minibus: None }
    };
    let crate::qbin::Loaded { c, pow, bits, bout, csum, xsrc, minibus } = l;
    let _ = MINIBUS.set(minibus);
    if !csum.is_empty() || !xsrc.is_empty() {
        eprintln!("r3typed: {} CSUM lines, {} XSRC cells", csum.len(), xsrc.len());
    }
    let _ = (CSUM.set(csum), XSRC.set(xsrc));
    eprintln!("r3typed: Q {} entries, {} OUT, {} PoW runs, {} BITS rows, {} BOUT lines", c.ents.len(), c.outs.len(), pow.len(), bits.len(), bout.len());
    (c, pow, bits, bout)
}

/// The circuit in use: [`install`]ed, else `$LVM6_Q_BLOB`, else the synthetic stub.
pub fn circuit() -> &'static Circuit {
    &CIRCUIT.get_or_init(load).0
}

/// The BITS aux rows of the circuit in use.
pub fn aux_bits() -> &'static [AuxBits] {
    &CIRCUIT.get_or_init(load).2
}

/// The PoW bit words of the circuit in use.
pub fn pow_bits() -> &'static [PowBits] {
    &CIRCUIT.get_or_init(load).1
}

/// The PoW bit words of `c` if it is the circuit in use (an installed or loaded one), else none.
pub fn pow_bits_of(c: &Circuit) -> &'static [PowBits] {
    match CIRCUIT.get() {
        Some((cc, pow, _, _)) if std::ptr::eq(cc, c) => pow,
        _ => &[],
    }
}

/// The BITS aux rows of `c` if it is the circuit in use, else none.
pub fn aux_bits_of(c: &Circuit) -> &'static [AuxBits] {
    match CIRCUIT.get() {
        Some((cc, _, bits, _)) if std::ptr::eq(cc, c) => bits,
        _ => &[],
    }
}

/// The `BOUT` lines of `c` if it is the circuit in use, else none.
pub fn bout_of(c: &Circuit) -> &'static [BOut] {
    match CIRCUIT.get() {
        Some((cc, _, _, bout)) if std::ptr::eq(cc, c) => bout,
        _ => &[],
    }
}

/// `Φ_Q(pt)` of the circuit in use (the driver's `HDR.accIn = (0^43, Φ_Q(0^43))` at `b = 0`, FORMAT6 §2.1).
pub fn phi_q(pt: &[F128]) -> F128 {
    circuit().phi_q(pt)
}
