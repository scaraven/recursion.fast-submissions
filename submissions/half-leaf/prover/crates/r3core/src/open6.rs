//! FORMAT6 v2.4 §6.1 (the commitment and its OOD claim), §6.5 (ring switching and the `λ₀` batch of the stack
//! claims) and §6.6 (the affine-fold WHIR opening), prover side, on the v6 hash chain (`fs6::Transcript`).
//!
//! The mathematics is R1's KAT generator (`tools/refv/src/prover.rs`, accepted by refv at `P18`), which is
//! leanVM's experimental prover transcribed naively: the RS encodes are `pcs::ntt::AdditiveNttF64` (vendored,
//! unchanged); the fold tables, the glue of the OOD and query claims and the tail sumcheck are `pcs::whir`'s
//! `Dense::table`/`Dense::fold`/`glue`/`tail_sumcheck`. What is new here (R3): the batched weight. Claim `k` of
//! §6.5's list has coefficient `λ₀^k`; the weight of every claim is built densely over the whole stack (a ring
//! claim's `Φ(eq(point, ·))` through byte tables of the `F₂`-linear `Φ`), and the opening runs on
//! `w = Σ_k λ₀^k W_k` with target `Σ_k λ₀^k value_k`.
//!
//! Memory at `P18`: the stack as `E` (512 MiB) and the weight (512 MiB) in the transposed layout of `Dense`
//! (coefficient `c` = stack row, lane = slot), level 0's codeword (2^21 × 48 words, 768 MiB) and its tree.

use fs6::{Digest, Oracle, Transcript, Tree6};
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F128};
use verifier::{K, Subspace};

use crate::claim::{PClaim, RingMap, Weight};
use crate::layout::{LANES, ROW_LOG, ROWS, STACK_LOG};

#[inline]
fn fs_f(x: F128) -> fs6::E {
    [x.c0, x.c1]
}
#[inline]
fn f_of(x: fs6::E) -> F128 {
    F128::new(x[0], x[1])
}

/// A committed codeword: rows of `rw` words, a leaf being words `off .. off + n` of its row, and its tree.
pub struct Committed {
    cw: Vec<F64>,
    rw: usize,
    off: usize,
    n: usize,
    tree: Tree6,
}

impl Committed {
    fn build(o: &dyn Oracle, l: &fs6::params::Level, cw: Vec<F64>, rw: usize, off: usize, n: usize) -> Self {
        let leaf = |p: usize, b: &mut Vec<u8>| {
            for w in &cw[p * rw + off..p * rw + off + n] {
                b.extend_from_slice(&w.0.to_le_bytes());
            }
        };
        let tree = Tree6::build(o, l.ht, l.lv, &leaf);
        Self { cw, rw, off, n, tree }
    }

    fn leaf(&self, p: usize, b: &mut Vec<u8>) {
        for w in &self.cw[p * self.rw + self.off..p * self.rw + self.off + self.n] {
            b.extend_from_slice(&w.0.to_le_bytes());
        }
    }

    pub fn cap(&self) -> &[Digest] {
        self.tree.cap()
    }
}

/// Level 0 of the stack `q` (`2^25` words, slot `s` of row `r` at `r + 2^19·s`): lane `t` of the codeword is slot
/// `LANES−1−t`, after `rw − LANES` zero lanes (`pcs::whir::commit`), so a leaf is slot 45 first, slot 0 last
/// (FORMAT6 §5). R1's `commit0`.
pub fn commit0(o: &dyn Oracle, sh: &fs6::params::Shape, q: &[F64]) -> Committed {
    let l = &sh.levels[0];
    let (m, r) = (l.log_msg_cols as usize, l.log_inv_rate as usize);
    assert_eq!((m, sh.lanes, q.len()), (ROW_LOG, LANES, 1 << STACK_LOG));
    let rw = sh.lanes.next_multiple_of(8).min(64);
    let z = rw - sh.lanes;
    let mut cw = vec![F64(0); (1usize << (m + r)) * rw];
    parallel::chunks_mut(&mut cw[..(1usize << m) * rw], rw, |c, row| {
        for (j, w) in row.iter_mut().enumerate().skip(z) {
            *w = q[c + ((sh.lanes - 1 - (j - z)) << m)];
        }
    });
    AdditiveNttF64::standard(m + r).encode_interleaved_in_place(&mut cw, rw, r);
    Committed::build(o, l, cw, rw, z, sh.lanes)
}

/// Level `i ≥ 1`: the low part of the folded lane, `2^k` interleaved lanes of `E`, lane `u` at bytes `16u` of the
/// leaf (`pcs::whir::ligero_commit_ext`). R1's `commit_e`.
fn commit_e(o: &dyn Oracle, sh: &fs6::params::Shape, i: usize, p_low: &[F128]) -> Committed {
    let l = &sh.levels[i];
    let (cols, k, r) = (l.log_msg_cols as usize, l.fold, l.log_inv_rate as usize);
    assert_eq!(p_low.len(), 1 << (cols + k));
    let rw = 2 << k;
    let mut cw = vec![F64(0); (1usize << (cols + r)) * rw];
    for (j, x) in p_low.iter().enumerate() {
        cw[2 * j] = F64(x.c0);
        cw[2 * j + 1] = F64(x.c1);
    }
    AdditiveNttF64::standard(cols + r).encode_interleaved_in_place(&mut cw, rw, r);
    Committed::build(o, l, cw, rw, 0, rw)
}

/// §6.1 after the commitment: `CAP(0)` · `B` · `G(g_ood[0])`, `D(24)` → `z₀` · `E(1)` → `y₀`. Returns claim 0.
pub fn commitment(tr: &mut Transcript, sh: &fs6::params::Shape, c0: &Committed, q: &[F64]) -> PClaim {
    tr.absorb_cap(c0.cap());
    tr.bind();
    let mut z0 = vec![tr.ground(sh.levels[0].grind_ood)];
    z0.extend(tr.draws(STACK_LOG - 1));
    let z0: Vec<F128> = z0.into_iter().map(|x| F128::new(x[0], x[1])).collect();
    let y0 = primitives::multilinear::mle_eval_par(q, &z0);
    tr.absorb_e(&[[y0.c0, y0.c1]]);
    PClaim::point("0 ood", 0, z0, y0)
}

// ------------------------------------------------------------------------------------------- the batched weight

/// `Φ` as 16 byte tables: `Φ(v) = ⊕_j T_j[byte j of (c₀ ‖ c₁)]` (`Φ` is `F₂`-linear).
fn phi_tables(c: &[F128; 64]) -> Vec<[F128; 256]> {
    (0..16)
        .map(|j| {
            let mut t = [F128::ZERO; 256];
            for bit in 0..8 {
                let b = 8 * j + bit;
                let v = if b < 64 { F128::new(1 << b, 0) } else { F128::new(0, 1 << (b - 64)) };
                let img = RingMap::apply(c, v);
                let step = 1usize << bit;
                for x in 0..step {
                    t[x + step] = t[x] + img;
                }
            }
            t
        })
        .collect()
}

#[inline]
fn phi_by_tables(t: &[[F128; 256]], v: F128) -> F128 {
    let mut acc = F128::ZERO;
    for j in 0..8 {
        acc += t[j][(v.c0 >> (8 * j)) as usize & 0xff];
        acc += t[8 + j][(v.c1 >> (8 * j)) as usize & 0xff];
    }
    acc
}

/// The weight of `claim` on its block, times `scale`, in block order (`2^μ` entries).
fn block_weight(claim: &PClaim, scale: F128, maps: &[RingMap; 2]) -> Vec<F128> {
    match &claim.weight {
        Weight::Point { point, .. } => {
            let mut t = primitives::multilinear::eq_table(point);
            parallel::chunks_mut(&mut t, 1 << 12, |_, ch| ch.iter_mut().for_each(|x| *x *= scale));
            t
        }
        Weight::Ring { point, map, .. } => {
            let tabs = phi_tables(&maps[*map].coefficients());
            let mut t = primitives::multilinear::eq_table(point);
            parallel::chunks_mut(&mut t, 1 << 12, |_, ch| ch.iter_mut().for_each(|x| *x = scale * phi_by_tables(&tabs, *x)));
            t
        }
        Weight::Dense { mu, fill, .. } => {
            let mut t = vec![F128::ZERO; 1 << mu];
            fill(scale, &mut t);
            t
        }
    }
}

/// `w` in `Dense`'s layout (`w[r·64 + slot]` = weight at stack index `r + 2^19·slot`): `Σ_k λ₀^k W_k`.
fn batched_weight(claims: &[PClaim], lambda0: F128, maps: &[RingMap; 2]) -> (Vec<F128>, F128) {
    let mut w = vec![F128::ZERO; 1 << STACK_LOG];
    let (mut scale, mut target) = (F128::ONE, F128::ZERO);
    // Point claims on whole slots (`μ ≥ 19`) factor as `eq_row(p[..19], r)·coef(slot)`: grouped by row point, one
    // pass per group adds `eq_row[r]·coef[s]` (the wiring claims share `(ρ, 0)`, the root claims `0^19`).
    let mut groups: Vec<(Vec<F128>, [F128; 64])> = Vec::new();
    for c in claims {
        target += scale * c.batch_value(maps);
        if let Weight::Point { off, point } = &c.weight
            && point.len() >= ROW_LOG
        {
            let (off, mu) = (*off, point.len());
            let gi = match groups.iter().position(|(p, _)| p[..] == point[..ROW_LOG]) {
                Some(i) => i,
                None => {
                    groups.push((point[..ROW_LOG].to_vec(), [F128::ZERO; 64]));
                    groups.len() - 1
                }
            };
            let eq_hi = primitives::multilinear::eq_table(&point[ROW_LOG..]);
            for s in 0..64usize {
                if s >> (mu - ROW_LOG) == off {
                    groups[gi].1[s] += scale * eq_hi[s & ((1 << (mu - ROW_LOG)) - 1)];
                }
            }
            scale *= lambda0;
            continue;
        }
        let (off, mu) = c.weight.block();
        let bw = block_weight(c, scale, maps);
        let base = off << mu;
        let (lo, hi) = (base, base + (1 << mu));
        let (s_lo, s_hi) = (lo >> ROW_LOG, (hi - 1) >> ROW_LOG);
        parallel::chunks_mut(&mut w, 64, |r, row| {
            for s in s_lo..=s_hi {
                let x = r + (s << ROW_LOG);
                if x >= lo && x < hi {
                    row[s] += bw[x - base];
                }
            }
        });
        scale *= lambda0;
    }
    for (rp, coef) in &groups {
        let eq_row = primitives::multilinear::eq_table(rp);
        let coef: Vec<(usize, F128)> = coef.iter().enumerate().filter(|(_, c)| **c != F128::ZERO).map(|(s, &c)| (s, c)).collect();
        parallel::chunks_mut(&mut w, 64, |r, row| {
            if eq_row[r] != F128::ZERO {
                let er = eq_row[r];
                for &(s, c) in &coef {
                    row[s] += er * c;
                }
            }
        });
    }
    (w, target)
}

// ------------------------------------------------------------------------------------------- WHIR (R1's Dense)

/// One fold round's challenges: `P = G + (α + β X) F` (`L:whir.rs:150`).
#[derive(Clone, Copy, Debug)]
struct FoldRound {
    alpha: F128,
    beta: F128,
}

impl FoldRound {
    /// The claim after the round from the table `[v_G, v_F, t₀, t₁]` (`L:whir.rs:304`).
    fn next_claim(&self, claim: F128, t: &[F128]) -> F128 {
        let (u0, w, c0, c1) = (t[0], t[1], t[2], t[3]);
        let (a, b) = (self.alpha, self.beta);
        u0 + b * c0 + a * (u0 + claim + a * w + b * (c0 + c1))
    }
}

/// `a_i = W_(i+1)(β_(i+1)) / W_i(β_i)²` (`L:whir.rs` test `times_x`).
fn x_constants(n: usize) -> Vec<K> {
    let roots = verifier::subspace_roots(n + 1);
    (0..n).map(|i| roots[i + 1] * roots[i].square().inv()).collect()
}

/// `X · H` in the novel basis (refv `arith::times_x_strided`).
fn times_x_strided(h: &[F128], first: usize, stride: usize, count: usize, a: &[K]) -> Vec<F128> {
    let mut out = vec![F128::ZERO; count + 1];
    for c in 0..count {
        let v = h[first + stride * c];
        let t = c.trailing_ones() as usize;
        let mut prod = K(1);
        for (j, &aj) in a.iter().enumerate().take(t) {
            out[c & !((1 << j) - 1)] += v.mul_base(F64(prod.0));
            prod = prod * aj;
        }
        out[c + 1] += v.mul_base(F64(prod.0));
    }
    out
}

/// `X_c(x) = Π_{i: c_i = 1} What_i(x)` for `c < count` (`L:whir.rs:126`).
fn novel_basis(what: &[K], count: usize) -> Vec<K> {
    let mut basis = vec![K(1)];
    for &v in what {
        if basis.len() >= count {
            break;
        }
        let doubled: Vec<K> = basis.iter().map(|&b| b * v).collect();
        basis.extend(doubled);
    }
    basis.truncate(count);
    basis
}

/// Lanes in the clear, coefficient by coefficient: coefficient `c` of lane `l` at `c·stride + l`.
struct Dense {
    f: Vec<F128>,
    w: Vec<F128>,
    stride: usize,
}

impl Dense {
    fn xf(&self) -> Vec<Vec<F128>> {
        let (s, ncols) = (self.stride, self.f.len() / self.stride);
        let a = x_constants((usize::BITS - ncols.leading_zeros()) as usize + 2);
        parallel::map_collect(s / 2, |m| times_x_strided(&self.f, 2 * m, s, ncols, &a))
    }

    /// `[v_G, v_F, t₀, t₁]`. The lane pairs are summed in a fixed order (deterministic).
    fn table(&self, xf: &[Vec<F128>]) -> [F128; 4] {
        let (s, f, w) = (self.stride, &self.f, &self.w);
        let low = w.len() / s;
        let parts = parallel::map_collect(s / 2, |m| {
            let mut acc = [F128::ZERO; 4];
            for c in 0..low {
                let (w0, w1, ff, g, x) = (w[c * s + 2 * m], w[c * s + 2 * m + 1], f[c * s + 2 * m], f[c * s + 2 * m + 1], xf[m][c]);
                acc[0] += w0 * g;
                acc[1] += (w0 + w1) * ff;
                acc[2] += w0 * x;
                acc[3] += w1 * x;
            }
            acc
        });
        parts.into_iter().fold([F128::ZERO; 4], |a, b| std::array::from_fn(|k| a[k] + b[k]))
    }

    fn fold(&mut self, xf: &[Vec<F128>], r: FoldRound) {
        let (s, pairs) = (self.stride, self.stride / 2);
        let ncols = self.f.len() / s;
        let f = &self.f;
        let mut next = vec![F128::ZERO; (ncols + 1) * pairs];
        parallel::chunks_mut(&mut next, pairs, |c, out| {
            for (m, o) in out.iter_mut().enumerate() {
                let bx = r.beta * xf[m][c];
                *o = if c == ncols { bx } else { f[c * s + 2 * m + 1] + r.alpha * f[c * s + 2 * m] + bx };
            }
        });
        let mut w = vec![F128::ZERO; self.w.len() / 2];
        let old = &self.w;
        parallel::chunks_mut(&mut w, 1 << 12, |c, out| {
            for (j, o) in out.iter_mut().enumerate() {
                let i = (c << 12) + j;
                *o = old[2 * i] + r.alpha * (old[2 * i] + old[2 * i + 1]);
            }
        });
        (self.f, self.w, self.stride) = (next, w, pairs);
    }

    fn claim(&self) -> F128 {
        let parts = parallel::map_collect(self.w.len().div_ceil(1 << 14), |c| {
            let lo = c << 14;
            let hi = (lo + (1 << 14)).min(self.w.len());
            (lo..hi).fold(F128::ZERO, |a, i| a + self.w[i] * self.f[i])
        });
        parts.into_iter().fold(F128::ZERO, |a, b| a + b)
    }
}

fn draw_positions(tr: &mut Transcript, l: &fs6::params::Level) -> Vec<usize> {
    let mut draws = vec![tr.ground(l.grind_query)];
    draws.extend(tr.draws(l.position_draws() - 1));
    fs6::merkle::positions(&draws, l.ht, l.queries)
}

fn open_level(tr: &mut Transcript, cur: &Committed, pos: &[usize]) {
    for &p in pos {
        tr.open(&cur.tree, &[p], &|p, b: &mut Vec<u8>| cur.leaf(p, b));
    }
}

// ------------------------------------------------------------------------- R5: leanVM's opening machinery

/// §6.5's list as leanVM's opening terms (`pcs::open6`), claim `k` scaled by `λ₀^k`, and the batched target.
/// A point claim is a point term; a ring claim a ring term with its map's 128 coordinate weights; a dense weight is
/// cut into the stack's blocks of `2^low_vars` words, each block `v₀·N` (`v₀` its first nonzero entry), the blocks
/// of one lane with the same `N` making one lane term (`low = N`, `gamma(h) = v₀` of block `h`).
pub struct Terms6 {
    pub points: Vec<pcs::open6::PointTerm>,
    pub lanes: Vec<pcs::open6::LaneTerm>,
    pub rings: Vec<pcs::open6::RingTerm>,
    pub target: F128,
}

pub fn terms6(claims: &[PClaim], lambda0: F128, maps: &[RingMap; 2]) -> Terms6 {
    terms6_where(claims, lambda0, maps, &|_| true)
}

/// [`terms6`] over the claims `keep` selects (the others keep their power of `λ₀` but add nothing).
pub fn terms6_where(claims: &[PClaim], lambda0: F128, maps: &[RingMap; 2], keep: &dyn Fn(&PClaim) -> bool) -> Terms6 {
    use pcs::open6::{DEGREE_E, PointTerm, RingTerm};
    let mut t = Terms6 { points: Vec::new(), lanes: Vec::new(), rings: Vec::new(), target: F128::ZERO };
    let mut index = std::collections::HashMap::new();
    let mut scale = F128::ONE;
    for c in claims {
        if !keep(c) {
            scale *= lambda0;
            continue;
        }
        t.target += scale * c.batch_value(maps);
        match &c.weight {
            Weight::Point { off, point } => {
                t.points.push(PointTerm { offset: off << point.len(), point: point.clone(), lambda: scale })
            }
            Weight::Ring { off, point, map, .. } => {
                let coef = maps[*map].coefficients();
                let weights: [F128; DEGREE_E] =
                    std::array::from_fn(|w| scale * RingMap::apply(&coef, pcs::open6::coordinate_basis(w)));
                t.rings.push(RingTerm { offset: off << point.len(), point: point.clone(), weights });
            }
            Weight::Dense { off, mu, fill } => {
                let mut w = vec![F128::ZERO; 1 << mu];
                fill(scale, &mut w);
                dense_lane_terms(off << mu, &w, &mut t.lanes, &mut index);
            }
        }
        scale *= lambda0;
    }
    t
}

/// A dense weight `w` on the stack words `[base, base + |w|)` as lane terms (appended; `index` keys
/// `(lane, N)` to its term, across the claims).
fn dense_lane_terms(
    base: usize,
    w: &[F128],
    out: &mut Vec<pcs::open6::LaneTerm>,
    index: &mut std::collections::HashMap<(usize, Vec<[u64; 2]>), usize>,
) {
    let low = pcs::open6::low_vars(ROW_LOG);
    let (bl, nb) = (1usize << low, 1usize << (ROW_LOG - low));
    let (b0, b1) = (base >> low, (base + w.len() - 1) >> low);
    let blocks = parallel::map_collect(b1 + 1 - b0, |k| {
        let b = b0 + k;
        let at = |x: usize| {
            let i = (b << low) + x;
            if i >= base && i < base + w.len() { w[i - base] } else { F128::ZERO }
        };
        let v0 = (0..bl).map(at).find(|v| !v.is_zero())?;
        let inv = v0.inv();
        Some((b, v0, (0..bl).map(|x| at(x) * inv).collect::<Vec<F128>>()))
    });
    for (b, v0, n) in blocks.into_iter().flatten() {
        let (lane, h) = (b / nb, b % nb);
        assert!(lane < LANES, "a dense weight on an uncommitted lane");
        let key = (lane, n.iter().map(|x| [x.c0, x.c1]).collect::<Vec<_>>());
        let i = *index.entry(key).or_insert_with(|| {
            out.push(pcs::open6::LaneTerm { lane, low: n, gamma: vec![F128::ZERO; nb], lambda: F128::ONE });
            out.len() - 1
        });
        out[i].gamma[h] += v0;
    }
}

/// Dev (`LVM6_OPEN=cmp`): level 0's first table, naive dense weight against the terms, per claim kind.
fn dev_compare(q: &[F64], claims: &[PClaim], lambda0: F128, maps: &[RingMap; 2]) {
    let kinds: [(&str, &dyn Fn(&PClaim) -> bool); 4] = [
        ("point", &|c| matches!(c.weight, Weight::Point { .. })),
        ("ring", &|c| matches!(c.weight, Weight::Ring { .. })),
        ("dense", &|c| matches!(c.weight, Weight::Dense { .. })),
        ("all", &|_| true),
    ];
    for (name, keep) in kinds {
        let mut w = vec![F128::ZERO; 1 << STACK_LOG];
        let mut scale = F128::ONE;
        for c in claims {
            if keep(c) {
                let (off, mu) = c.weight.block();
                let bw = block_weight(c, scale, maps);
                let base = off << mu;
                for (j, &x) in bw.iter().enumerate() {
                    let i = base + j;
                    w[(i & (ROWS - 1)) * 64 + (i >> ROW_LOG)] += x;
                }
            }
            scale *= lambda0;
        }
        let mut d = Dense { f: vec![F128::ZERO; 64 << ROW_LOG], w, stride: 64 };
        parallel::chunks_mut(&mut d.f, 64, |c, row| {
            for (l, x) in row.iter_mut().enumerate().take(LANES) {
                *x = F128::new(q[c + (l << ROW_LOG)].0, 0);
            }
        });
        let naive = d.table(&d.xf());
        drop(d);
        let t6 = terms6_where(claims, lambda0, maps, keep);
        let mut l0 = pcs::open6::Level0::new(q[..LANES << ROW_LOG].to_vec(), STACK_LOG, ROW_LOG, &t6.points, &t6.lanes, &t6.rings);
        let terms = l0.table();
        eprintln!(
            "cmp {name}: points {} lanes {} rings {}: {}",
            t6.points.len(),
            t6.lanes.len(),
            t6.rings.len(),
            if naive == terms { "EQUAL".to_string() } else { format!("DIFFER naive {naive:?} terms {terms:?}") }
        );
    }
}

fn dot_e(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    parallel::map_reduce(
        a.len().div_ceil(1 << 14),
        || F128::ZERO,
        |c| {
            let (lo, hi) = (c << 14, ((c + 1) << 14).min(a.len()));
            a[lo..hi].iter().zip(&b[lo..hi]).fold(F128::ZERO, |s, (&x, &y)| s + x * y)
        },
        |x, y| x + y,
    )
}

/// §6.5 and §6.6: `B`, the group `G(g_batch)`, `D(32)` (tree map, sponge map, `λ₀`), then the opening of `q`
/// (consumed) against `Σ_k λ₀^k claims[k]`. `claims` is §6.5's list in order (claim 0 = the OOD claim).
///
/// R5: the same messages as R1's naive dense opening (`LVM6_OPEN=naive`, kept), computed with leanVM's own
/// machinery (`pcs::open6`): level 0's rounds on the terms of the batched weight (never written out over the
/// stack), the later levels' rounds with `whir::Dense`, the queries' weight with `induce_basis_auto`.
/// With `check`, asserts after every level's rounds that the running claim is `⟨w, f⟩` (level 0's also checks
/// the terms against the target) and that the query weight is the novel basis at a query.
pub fn open(
    tr: &mut Transcript,
    sh: &fs6::params::Shape,
    mut q: Vec<F64>,
    c0: Committed,
    claims: &[PClaim],
    check: bool,
) -> OpenTimes {
    if std::env::var("LVM6_OPEN").is_ok_and(|v| v == "naive") {
        return open_naive(tr, sh, q, c0, claims, check);
    }
    let o = tr.oracle();
    let mut times = OpenTimes::default();
    let t = std::time::Instant::now();
    assert!(claims.len() <= sh.j0, "more than J₀ stack claims");
    tr.bind();
    let mut v = vec![tr.ground(sh.grind_batch)];
    v.extend(tr.draws(32));
    let v: Vec<F128> = v.into_iter().map(|x| F128::new(x[0], x[1])).collect();
    let maps = [RingMap::from_draws(&v[0..16]), RingMap::from_draws(&v[16..32])];
    let lambda0 = v[32];
    if std::env::var("LVM6_OPEN").is_ok_and(|v| v == "cmp") {
        dev_compare(&q, claims, lambda0, &maps);
    }
    let t6 = terms6(claims, lambda0, &maps);
    q.truncate(LANES << ROW_LOG);
    let mut level0 = Some(pcs::open6::Level0::new(q, STACK_LOG, ROW_LOG, &t6.points, &t6.lanes, &t6.rings));
    let mut claim = t6.target;
    times.batch = t.elapsed().as_secs_f64();

    let mut cur = c0;
    let n_levels = sh.levels.len();
    let mut carried: Option<(Vec<F128>, Vec<F128>)> = None;
    let laps_on = std::env::var_os("LVM6_R5_LAPS").is_some();
    for (i, l) in sh.levels.iter().enumerate() {
        let t = std::time::Instant::now();
        let mut lt = std::time::Instant::now();
        let mut laps: Vec<(&str, f64)> = Vec::new();
        let mut lap = |n: &'static str, laps: &mut Vec<(&str, f64)>| {
            laps.push((n, lt.elapsed().as_secs_f64()));
            lt = std::time::Instant::now();
        };
        let mut round = |tb: pcs::open6::Table, claim: &mut F128| {
            tr.absorb_e(&tb.map(fs_f));
            let alpha = f_of(tr.ground(l.grind_fold));
            let beta = f_of(tr.draw());
            *claim = FoldRound { alpha, beta }.next_claim(*claim, &tb);
            (alpha, beta)
        };
        let (mut f, mut w) = match level0.take() {
            Some(mut l0) => {
                for _ in 0..l.fold {
                    let (a, b) = round(l0.table(), &mut claim);
                    l0.fold(a, b);
                }
                l0.finish()
            }
            None => {
                let (f, w) = carried.take().expect("a level's lane");
                let mut r = pcs::open6::Rounds::new(f, w, 1 << l.fold);
                for _ in 0..l.fold {
                    let (a, b) = round(r.table(), &mut claim);
                    r.fold(a, b);
                }
                r.into_parts()
            }
        };
        let mu = l.log_msg_cols as usize;
        assert_eq!((f.len(), w.len()), ((1 << mu) + l.fold, 1 << mu));
        lap("rounds", &mut laps);
        if check {
            assert_eq!(claim, dot_e(&f[..1 << mu], &w), "level {i}: the rounds keep the claim");
        }
        if i + 1 == n_levels {
            tr.absorb_e(&f.iter().copied().map(fs_f).collect::<Vec<_>>());
            let pos = draw_positions(tr, l);
            open_level(tr, &cur, &pos);
            f.truncate(1 << mu);
            let (mut fv, mut wv) = (f, w);
            for _ in 0..sh.tail_rounds {
                let (mut c0, mut c2) = (F128::ZERO, F128::ZERO);
                for k in 0..fv.len() / 2 {
                    c0 += fv[2 * k] * wv[2 * k];
                    c2 += (fv[2 * k] + fv[2 * k + 1]) * (wv[2 * k] + wv[2 * k + 1]);
                }
                tr.absorb_e(&[c0, c2].map(fs_f));
                let r = f_of(tr.ground(sh.grind_tail));
                claim = c0 + r * (claim + c2) + r * r * c2;
                let fold = |v: &[F128]| v.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect::<Vec<F128>>();
                (fv, wv) = (fold(&fv), fold(&wv));
            }
            if check {
                assert_eq!(claim, fv[0] * wv[0], "the tail keeps the claim");
            }
            times.levels.push(t.elapsed().as_secs_f64());
            break;
        }
        let high = f.split_off(1 << mu);
        let next = commit_e(o, sh, i + 1, &f);
        lap("commit", &mut laps);
        tr.absorb_e(&high.iter().copied().map(fs_f).collect::<Vec<_>>());
        tr.absorb_cap(next.tree.cap());
        tr.bind();
        let nl = &sh.levels[i + 1];
        let mut z = vec![f_of(tr.ground(nl.grind_ood))];
        z.extend(tr.draws(mu - 1).into_iter().map(f_of));
        let eqz = primitives::multilinear::eq_table(&z);
        let y = dot_e(&f, &eqz);
        tr.absorb_e(&[fs_f(y)]);
        lap("ood", &mut laps);
        let pos = draw_positions(tr, l);
        let lambda = f_of(tr.draw());
        open_level(tr, &cur, &pos);
        lap("open", &mut laps);
        // Glue (`pcs::whir::glue`): `λ`·(eq(z), y), `λ²`·(Σ_q λ^q X_·(x_q), Σ_q λ^q P_low(x_q)).
        let log_rate = l.ht as usize - mu;
        let basis = pcs::open6::induce(mu, log_rate, &pos, &primitives::field::powers(lambda, pos.len()));
        let l2 = lambda * lambda;
        if check {
            let one = pcs::open6::induce(mu, log_rate, &pos[..1], &[F128::ONE]);
            let nb = novel_basis(&Subspace::new(mu).at(K(pos[0] as u64)), 1 << mu);
            assert!(one.iter().zip(&nb).all(|(&a, &b)| a == F128::new(b.0, 0)), "level {i}: induce = the novel basis");
        }
        // The running claim (never sent; tracked for `check` and kept right without it).
        claim += lambda * y + l2 * dot_e(&f, &basis);
        parallel::chunks_mut(&mut w, 1 << 12, |c, out| {
            for (j, x) in out.iter_mut().enumerate() {
                let k = (c << 12) + j;
                *x += lambda * eqz[k] + l2 * basis[k];
            }
        });
        if check {
            assert_eq!(claim, dot_e(&f, &w), "level {i}: the glue keeps the claim");
        }
        lap("glue", &mut laps);
        if laps_on {
            eprintln!("r5 open level {i} laps {laps:?}"); // dev (R5)
        }
        carried = Some((f, w));
        cur = next;
        times.levels.push(t.elapsed().as_secs_f64());
    }
    times
}

/// Seconds per sub-phase of the opening.
#[derive(Clone, Debug, Default)]
pub struct OpenTimes {
    pub batch: f64,
    pub levels: Vec<f64>,
}

/// §6.5 and §6.6: `B`, the group `G(g_batch)`, `D(32)` (tree map, sponge map, `λ₀`), then the opening of `q`
/// (consumed) against `Σ_k λ₀^k claims[k]`. `claims` is §6.5's list in order (claim 0 = the OOD claim).
/// With `check`, asserts after every level that the running claim is `⟨w, f⟩` and that the folded weight is the
/// batched weight's extension at the terminal point (the dev form of `V_S`'s terminal check).
fn open_naive(
    tr: &mut Transcript,
    sh: &fs6::params::Shape,
    q: Vec<F64>,
    c0: Committed,
    claims: &[PClaim],
    check: bool,
) -> OpenTimes {
    let o = tr.oracle();
    let mut times = OpenTimes::default();
    let t = std::time::Instant::now();
    assert!(claims.len() <= sh.j0, "more than J₀ stack claims");
    // §6.5.
    tr.bind();
    let mut v = vec![tr.ground(sh.grind_batch)];
    v.extend(tr.draws(32));
    let v: Vec<F128> = v.into_iter().map(|x| F128::new(x[0], x[1])).collect();
    let maps = [RingMap::from_draws(&v[0..16]), RingMap::from_draws(&v[16..32])];
    let lambda0 = v[32];
    let (w, target) = batched_weight(claims, lambda0, &maps);
    let m = ROW_LOG;
    let mut d = Dense { f: vec![F128::ZERO; 64 << m], w, stride: 64 };
    parallel::chunks_mut(&mut d.f, 64, |c, row| {
        for (l, x) in row.iter_mut().enumerate().take(LANES) {
            *x = F128::new(q[c + (l << m)].0, 0);
        }
    });
    drop(q);
    let mut claim = target;
    if check {
        assert_eq!(claim, d.claim(), "§6.5: the batched claims hold on the stack");
    }
    times.batch = t.elapsed().as_secs_f64();

    let mut cur = c0;
    let n_levels = sh.levels.len();
    let mut point: Vec<F128> = Vec::new(); // the fold challenges' terminal point is checked by `V_S`; kept for `check`
    for (i, l) in sh.levels.iter().enumerate() {
        let t = std::time::Instant::now();
        for _ in 0..l.fold {
            let xf = d.xf();
            let tb = d.table(&xf);
            tr.absorb_e(&tb.map(fs_f));
            let alpha = f_of(tr.ground(l.grind_fold));
            let beta = f_of(tr.draw());
            let r = FoldRound { alpha, beta };
            claim = r.next_claim(claim, &tb);
            d.fold(&xf, r);
            point.push(alpha);
        }
        let mu = l.log_msg_cols as usize;
        assert_eq!((d.stride, d.f.len(), d.w.len()), (1, (1 << mu) + l.fold, 1 << mu));
        if check {
            assert_eq!(claim, d.claim(), "level {i}: the rounds keep the claim");
        }
        if i + 1 == n_levels {
            let fin = d.f.clone();
            tr.absorb_e(&fin.iter().copied().map(fs_f).collect::<Vec<_>>());
            let pos = draw_positions(tr, l);
            open_level(tr, &cur, &pos);
            let (mut fv, mut wv) = (d.f[..1 << mu].to_vec(), d.w.clone());
            for _ in 0..sh.tail_rounds {
                let (mut c0, mut c2) = (F128::ZERO, F128::ZERO);
                for k in 0..fv.len() / 2 {
                    c0 += fv[2 * k] * wv[2 * k];
                    c2 += (fv[2 * k] + fv[2 * k + 1]) * (wv[2 * k] + wv[2 * k + 1]);
                }
                tr.absorb_e(&[c0, c2].map(fs_f));
                let r = f_of(tr.ground(sh.grind_tail));
                claim = c0 + r * (claim + c2) + r * r * c2;
                let fold = |v: &[F128]| v.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect::<Vec<F128>>();
                (fv, wv) = (fold(&fv), fold(&wv));
            }
            if check {
                assert_eq!(claim, fv[0] * wv[0], "the tail keeps the claim");
            }
            times.levels.push(t.elapsed().as_secs_f64());
            break;
        }
        let high = d.f.split_off(1 << mu);
        let next = commit_e(o, sh, i + 1, &d.f);
        tr.absorb_e(&high.iter().copied().map(fs_f).collect::<Vec<_>>());
        tr.absorb_cap(next.tree.cap());
        tr.bind();
        let nl = &sh.levels[i + 1];
        let mut z = vec![f_of(tr.ground(nl.grind_ood))];
        z.extend(tr.draws(mu - 1).into_iter().map(f_of));
        let eqz = primitives::multilinear::eq_table(&z);
        let y = d.f.iter().zip(&eqz).fold(F128::ZERO, |a, (&x, &e)| a + x * e);
        tr.absorb_e(&[fs_f(y)]);
        let pos = draw_positions(tr, l);
        let lambda = f_of(tr.draw());
        open_level(tr, &cur, &pos);
        // Glue (`pcs::whir::glue`): `λ`·(eq(z), y), `λ²`·(Σ_q λ^q X_·(x_q), Σ_q λ^q P_low(x_q)).
        let sub = Subspace::new(mu);
        let mut wq = lambda * lambda;
        let mut add = vec![F128::ZERO; 1 << mu];
        let mut enforced = F128::ZERO;
        for &p in &pos {
            let basis = novel_basis(&sub.at(K(p as u64)), 1 << mu);
            enforced += wq * d.f.iter().zip(&basis).fold(F128::ZERO, |a, (&x, &b)| a + x.mul_base(F64(b.0)));
            for (x, &b) in add.iter_mut().zip(&basis) {
                *x += wq.mul_base(F64(b.0));
            }
            wq *= lambda;
        }
        claim += lambda * y + enforced;
        for ((w, &ez), &a) in d.w.iter_mut().zip(&eqz).zip(&add) {
            *w += lambda * ez + a;
        }
        d.stride = 1 << nl.fold;
        if check {
            assert_eq!(claim, d.claim(), "level {i}: the glue keeps the claim");
        }
        cur = next;
        times.levels.push(t.elapsed().as_secs_f64());
    }
    let _ = point;
    times
}

