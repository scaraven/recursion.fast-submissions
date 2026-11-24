//! Season 1's `lvm/m3.rs` (`archive/season-1/wide-packs/prover/src/lvm/m3.rs`, WP-15b and MBL/S2GL) ported from
//! F192 to F128 for FORMAT6 §6.4b: the bus phase alone (leanVM's `leaf::prove_balance` over the tables' flushes,
//! no framework block) and the three linear claims that replace the table sumcheck (roll #32's tableless form).
//! Dropped: `prove`, `prove_tables`, `shape_constraints`, the LoopIR builders (`piece_tables`, `loop_tables`, …):
//! no table carries a constraint and the tables come from [`crate::tables`]. Dropped with them: S1's trailing zero
//! scalar (`BUS_TRAILING_ZERO`, MB-decision §2: every group now opens with a nonce) and `SEND_FIXED` (no table
//! sumcheck sends evaluations).

use crate::leaf::{self, Block, Coord};
use crate::tables::{MbCol, MbTab, Side, UNPLACED};
use crate::transcript::ProverState;
use primitives::field::{F64, F128};
use primitives::multilinear::{eq_eval, mle_eval};

/// One flush of a table (local column indices).
#[derive(Clone, Debug)]
pub struct FlushW {
    pub push: bool,
    pub coords: Vec<Coord>,
    /// A read's count column: the count side carries it (`CountsNonzero`).
    pub count: Option<usize>,
}

/// A table: `2^tau` rows, columns (`com[c]`: committed, else fixed: verifier-known), flushes. S1's `cons`, `pre`
/// and `hdr` are gone: no constraint; placements live in [`MbTab`].
#[derive(Clone)]
pub struct TableW {
    pub tau: usize,
    pub cols: Vec<Vec<F64>>,
    pub com: Vec<bool>,
    pub flushes: Vec<FlushW>,
}

impl TableW {
    /// The table of a description, its committed columns' values `com_vals[c]` (fixed ones from the description).
    pub fn of(t: &MbTab, col: impl Fn(usize) -> Vec<F64>) -> Self {
        let cols: Vec<Vec<F64>> = (0..t.width())
            .map(|c| match &t.cols[c] {
                MbCol::Fix(v) => v.clone(),
                MbCol::Com { .. } => col(c),
            })
            .collect();
        assert!(cols.iter().all(|c| c.len() == 1 << t.tau), "every column has 2^τ rows");
        TableW {
            tau: t.tau,
            com: t.cols.iter().map(|c| matches!(c, MbCol::Com { .. })).collect(),
            flushes: t
                .flushes()
                .into_iter()
                .map(|f| FlushW { push: f.side == Side::Push, coords: f.coords, count: f.count })
                .collect(),
            cols,
        }
    }
}

fn shift(co: &Coord, base: usize) -> Coord {
    match co {
        Coord::Col(i) => Coord::Col(i + base),
        Coord::GCol(i, k) => Coord::GCol(i + base, *k),
        Coord::Prod(i, j, k) => Coord::Prod(i + base, j + base, *k),
        Coord::Sum(cs) => Coord::Sum(cs.iter().map(|x| shift(x, base)).collect()),
        x => x.clone(),
    }
}

/// The bus phase alone (leanVM's "Prove bus"): the fingerprint group, the grand-product GKR over every table's
/// flushes. Also returns each side's padding mass `1 + Σ_b eq(bits(off_b ≫ κ_b), ζ[κ_b..])` (S1's patched
/// `decompose_prove` returned it as the side's framework share; here it is computed from the layouts).
pub fn prove_bus(ps: &mut ProverState, tables: &[TableW]) -> (leaf::BusProof, [F128; 3]) {
    let mut cols: Vec<&[F64]> = Vec::new();
    let mut spans = Vec::with_capacity(tables.len());
    let (mut push, mut pull, mut count) = (Vec::new(), Vec::new(), Vec::new());
    let mut owners: [Vec<Option<(usize, usize)>>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for (t, tw) in tables.iter().enumerate() {
        let base = cols.len();
        for col in &tw.cols {
            assert_eq!(col.len(), 1 << tw.tau);
            cols.push(col);
        }
        spans.push((base, tw.cols.len()));
        for f in &tw.flushes {
            let blk = Block::full(tw.tau, f.coords.iter().map(|x| shift(x, base)).collect());
            if f.push {
                push.push(blk);
                owners[0].push(Some((t, base)));
            } else {
                pull.push(blk);
                owners[1].push(Some((t, base)));
            }
            if let Some(k) = f.count {
                count.push(Block::full(tw.tau, vec![Coord::Col(base + k)]));
                owners[2].push(Some((t, base)));
            }
        }
    }
    assert_eq!(leaf::layout(&push).mu, leaf::layout(&pull).mu);
    let bus = leaf::prove_balance(&push, &pull, &count, &cols, &owners, &spans, ps);
    assert!(bus.claims.is_empty(), "no framework block: nothing is opened per column");
    let mu = leaf::layout(&push).mu;
    assert_eq!(bus.point.len(), mu, "the GKR point has the bus depth");
    let padding: [F128; 3] = std::array::from_fn(|s| {
        let blocks = [&push, &pull, &count][s];
        let lay = leaf::layout(blocks);
        blocks.iter().zip(&lay.offsets).fold(F128::ONE, |acc, (b, &off)| {
            let sel = off >> b.kappa;
            let bits: Vec<F128> = (0..mu - b.kappa).map(|k| F128::new(((sel >> k) & 1) as u64, 0)).collect();
            acc + eq_eval(&bits, &bus.point[b.kappa..])
        })
    });
    (bus, padding)
}

/// MBL (stage S2GL): one of the three K-linear claims on the stack that replace the table sumcheck: side `s`'s
/// final GKR leaf claim `Ṽ_s(ζ)` less its padding mass and its known part (constants, fixed columns), as
/// `Σ_{(t, c)} coef·col~_{t,c}(ζ[..τ_t]) = value` over the committed columns `c` of table `t` that side `s` names.
pub struct LinClaim {
    /// `(table, column, coefficient)`: tables in order, a table's committed columns in column order.
    pub terms: Vec<(usize, usize, F128)>,
    pub value: F128,
}

/// What the mini-bus leaves to the opening: the GKR point `ζ` and the three claims (push, pull, count); `alphas`,
/// `beta` and `values` (the GKR's `Ṽ_s(ζ)`) for the dev identity checks.
pub struct LinOut {
    pub point: Vec<F128>,
    pub claims: [LinClaim; 3],
    pub alphas: Vec<F128>,
    pub beta: F128,
    pub values: [F128; 3],
}

/// The committed columns side `s` (0 push, 1 pull, 2 count) of `t` names: a `Col`/`GCol` coordinate of one of its
/// flushes on that side, or its count column. (S1's `side_reads`; equal to Lean's `sideColsG` on committed
/// columns.)
pub fn side_reads(t: &TableW, s: usize, c: usize) -> bool {
    fn names(x: &Coord, c: usize) -> bool {
        match x {
            Coord::Col(i) | Coord::GCol(i, _) => *i == c,
            Coord::Sum(cs) => cs.iter().any(|y| names(y, c)),
            _ => false,
        }
    }
    t.flushes.iter().any(|f| match s {
        2 => f.count == Some(c),
        _ => f.push == (s == 0) && f.coords.iter().any(|x| names(x, c)),
    })
}

/// MBL (S2GL): the bus phase, then the three claims (no `ξ`, no table sumcheck, no evaluations sent).
///
/// lvm6: every named committed column is a term, also one whose coefficient happens to vanish (Lean's `mbPartsG`
/// lists them all; S1 asserted the coefficient nonzero); a column the side does not name has coefficient zero.
pub fn prove_lin(ps: &mut ProverState, tables: &[TableW]) -> LinOut {
    assert!(
        tables.iter().all(|t| t.flushes.iter().all(|f| f.coords.iter().all(lin_coord))),
        "MB-LIN: every flush coordinate is Const, Col, GCol or a Sum of them"
    );
    let (bus, padding) = prove_bus(ps, tables);
    let zeta = bus.point.clone();
    let claims: [LinClaim; 3] = std::array::from_fn(|s| {
        let mut terms = Vec::new();
        let mut known = padding[s];
        for (t, tw) in tables.iter().enumerate() {
            let f = &bus.forms[s][t];
            assert!(f.prods.is_empty());
            known += f.constant;
            for c in 0..tw.cols.len() {
                let k = f.coeffs[c];
                if !tw.com[c] {
                    if k != F128::ZERO {
                        known += k * mle_eval(&tw.cols[c], &zeta[..tw.tau]);
                    }
                } else if side_reads(tw, s, c) {
                    terms.push((t, c, k));
                } else {
                    assert_eq!(k, F128::ZERO, "a column side {s} does not name has no coefficient");
                }
            }
        }
        LinClaim { terms, value: bus.values[s] + known }
    });
    LinOut { point: zeta, claims, alphas: bus.alphas, beta: bus.beta, values: bus.values }
}

fn lin_coord(c: &Coord) -> bool {
    match c {
        Coord::Const(_) | Coord::Col(_) | Coord::GCol(..) => true,
        Coord::Sum(cs) => cs.iter().all(lin_coord),
        _ => false,
    }
}

/// Place every unplaced committed column ([`UNPLACED`]) of `tables`: largest first at aligned offsets from `lo`
/// (rounded up to the largest column), ties by (table, column). Panics if they do not fit below `hi`. (S1's
/// `place`, on the descriptions; S1 placed into `C_main` above WP-15a's tables.)
pub fn place(tables: &mut [MbTab], lo: usize, hi: usize) {
    let mut cols: Vec<(usize, usize, usize)> = Vec::new(); // (tau, table, column)
    for (t, tw) in tables.iter().enumerate() {
        for (c, col) in tw.cols.iter().enumerate() {
            if *col == (MbCol::Com { at: UNPLACED }) {
                cols.push((tw.tau, t, c));
            }
        }
    }
    cols.sort_by(|a, b| b.0.cmp(&a.0).then((a.1, a.2).cmp(&(b.1, b.2))));
    let top = cols.first().map_or(0, |x| x.0);
    let mut off = lo.div_ceil(1 << top) << top;
    for (tau, t, c) in cols {
        tables[t].cols[c] = MbCol::Com { at: off };
        off += 1 << tau;
    }
    assert!(off <= hi, "the mini-bus columns fit their region ({off:#x} > {hi:#x})");
}

/// Committed words the tables take (aliased blocks counted once).
pub fn committed_words(tables: &[MbTab]) -> usize {
    let mut spans: Vec<(usize, usize)> = tables
        .iter()
        .flat_map(|t| t.cols.iter().filter_map(move |c| if let MbCol::Com { at } = c { Some((*at, 1 << t.tau)) } else { None }))
        .collect();
    spans.sort_unstable();
    spans.dedup();
    spans.iter().map(|s| s.1).sum()
}
