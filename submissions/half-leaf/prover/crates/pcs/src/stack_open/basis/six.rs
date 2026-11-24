//! lvm6 (WP R5, PATCHES.md): [`super::initial_basis`] for FORMAT6 §6.5's claim list. leanVM's opening batches point
//! claims and ring claims on ONE `q_keccak` slice under one map; lvm6's list has ring claims on several slices
//! under their own maps (tree, sponge) and weights that are not one `eq` tensor (FORMAT6 §6.3's link claims, the
//! typed region claims, the mini-bus claims). Both fit [`super::Terms`] unchanged:
//!
//! - a ring claim keeps leanVM's `Ring` term, at its own offset, with its own 128 coordinate weights;
//! - a weight on one lane that is `low(x_lo)·gamma(h)` (any `low` over a block's `2^low_vars` words, any `gamma`
//!   over the lane's blocks) is a claim of its own pattern: `L(l)` = the lane's indicator, `pi` = `low`.
//!
//! Nothing else differs from [`super::initial_basis`]; the terms then run leanVM's `LaneRounds` as they are.

use primitives::field::{F64, F128};

use super::{DEGREE_E, LOW_VARS, Low, Pattern, Ring, Terms, equal_blocks, extend_table, point_factors, table};
use crate::ring_switch::{RingWeight, coordinate_basis};
use crate::whir::InitialBasis;
use primitives::bit_fold::BitFold;

/// A point claim: `lambda·eq(point, ·)` on `[offset, offset + 2^|point|)` (aligned).
pub struct PointTerm {
    pub offset: usize,
    pub point: Vec<F128>,
    pub lambda: F128,
}

/// `lambda·low(x mod 2^low_vars)·gamma(x >> low_vars)` on lane `lane` (`x` inside the lane block).
pub struct LaneTerm {
    pub lane: usize,
    pub low: Vec<F128>,
    pub gamma: Vec<F128>,
    pub lambda: F128,
}

/// A ring claim `Phi(eq(point, ·))` on `[offset, offset + 2^|point|)`, `Phi` by its value on every coordinate basis
/// element of `E` (the batching scalar included).
pub struct RingTerm {
    pub offset: usize,
    pub point: Vec<F128>,
    pub weights: [F128; DEGREE_E],
}

/// Bits of a block's low part for a lane of `lane_vars` bits (what [`LaneTerm::low`] spans).
pub fn low_vars(lane_vars: usize) -> usize {
    lane_vars.min(LOW_VARS)
}

/// The opening's weight `sum points + sum lanes + sum rings` as terms (see [`super::initial_basis`]).
pub(crate) fn initial_basis6(
    stack: &[F64],
    log_n: usize,
    lane_vars: usize,
    points: &[PointTerm],
    lane_terms: &[LaneTerm],
    rings: &[RingTerm],
) -> InitialBasis {
    assert!(lane_vars >= super::ROWS.ilog2() as usize, "a lane block holds at least one row of bits");
    let block = 1usize << lane_vars;
    assert!(stack.len().is_multiple_of(block), "the stack is whole lane blocks");
    let (low_vars, lane_bits, bits) = (low_vars(lane_vars), log_n - lane_vars, log_n);
    let (n_lanes, n_blocks) = (1usize << lane_bits, 1usize << (lane_vars - low_vars));
    let mut terms = Terms {
        lane_vars,
        low_vars,
        gamma: Vec::new(),
        ranges: Vec::new(),
        patterns: Vec::new(),
        rings: Vec::new(),
        repeats: if low_vars == LOW_VARS { equal_blocks(stack) } else { Vec::new() },
    };
    let mut lanes: Vec<F128> = Vec::new();
    for (c, claim) in points.iter().enumerate() {
        assert!(claim.offset.is_multiple_of(1 << claim.point.len()) && claim.offset + (1 << claim.point.len()) <= 1 << log_n);
        let factors = point_factors(&claim.point, claim.offset, bits);
        let (low, rest) = factors.split_at(low_vars);
        let (mid, lane) = rest.split_at(lane_vars - low_vars);
        extend_table(&mut terms.gamma, mid);
        let at = lanes.len();
        extend_table(&mut lanes, lane);
        lanes[at..].iter_mut().for_each(|l| *l *= claim.lambda);
        match terms.patterns.iter_mut().find(|p| !p.factors.is_empty() && p.factors == low) {
            Some(pattern) => pattern.claims.push(c),
            None => terms.patterns.push(Pattern { low: Low::new(low), factors: low.to_vec(), claims: vec![c], active: Vec::new() }),
        }
    }
    // Lane terms: a pattern per distinct `low` (no factors: never shared with a point claim's).
    let mut tables: Vec<(Vec<F128>, usize)> = Vec::new();
    for (k, claim) in lane_terms.iter().enumerate() {
        let c = points.len() + k;
        assert_eq!((claim.low.len(), claim.gamma.len()), (1 << low_vars, n_blocks));
        assert!(claim.lane < n_lanes);
        terms.gamma.extend_from_slice(&claim.gamma);
        lanes.extend((0..n_lanes).map(|l| if l == claim.lane { claim.lambda } else { F128::ZERO }));
        match tables.iter().find(|(t, _)| *t == claim.low) {
            Some(&(_, p)) => terms.patterns[p].claims.push(c),
            None => {
                tables.push((claim.low.clone(), terms.patterns.len()));
                terms.patterns.push(Pattern {
                    low: Low::from_table(&claim.low),
                    factors: Vec::new(),
                    claims: vec![c],
                    active: Vec::new(),
                });
            }
        }
    }
    let n_claims = points.len() + lane_terms.len();
    for gamma in terms.gamma.chunks_exact(n_blocks) {
        let nonzero = |h: &usize| gamma[*h] != F128::ZERO;
        let first = (0..n_blocks).find(nonzero).unwrap_or(0);
        let end = (0..n_blocks).rfind(nonzero).map_or(0, |h| h + 1);
        terms.ranges.push(first / 8 * 8..end.next_multiple_of(8).min(n_blocks));
    }
    let gamma = |c: usize| &terms.gamma[c * n_blocks..][..n_blocks];
    for pattern in &mut terms.patterns {
        pattern.active = (0..n_blocks).map(|h| pattern.claims.iter().any(|&c| gamma(c)[h] != F128::ZERO)).collect();
    }
    for (i, ring) in rings.iter().enumerate() {
        assert!(ring.offset.is_multiple_of(1 << ring.point.len()) && ring.offset + (1 << ring.point.len()) <= 1 << log_n);
        let factors = point_factors(&ring.point, ring.offset, bits);
        let (low, rest) = factors.split_at(low_vars);
        let (mid, lane) = rest.split_at(lane_vars - low_vars);
        terms.rings.push(Ring {
            fold: BitFold::new(&table(low)),
            e_hi: table(mid),
            point: ring.point.clone(),
            x_offset: ring.offset & (block - 1),
            first: n_claims + DEGREE_E * i,
        });
        extend_table(&mut lanes, lane);
    }

    let n_terms = terms.n_terms();
    let mut a = vec![F128::ZERO; n_lanes * n_terms];
    for (l, row) in a.chunks_exact_mut(n_terms).enumerate() {
        let weight_of = |t: usize| lanes[(t << lane_bits) + l];
        for (c, slot) in row[..n_claims].iter_mut().enumerate() {
            *slot = weight_of(c);
        }
        for (i, (ring, term)) in rings.iter().zip(&terms.rings).enumerate() {
            let s = weight_of(n_claims + i);
            if s != F128::ZERO {
                let weight = RingWeight::new(ring.weights, ring.point.clone());
                for (w, slot) in row[term.first..term.first + DEGREE_E].iter_mut().enumerate() {
                    *slot = weight.apply(coordinate_basis(w) * s);
                }
            }
        }
    }
    InitialBasis { a, n_terms, terms }
}

impl Low {
    /// A pattern's table given outright (a lane term's `low`).
    fn from_table(t: &[F128]) -> Self {
        use primitives::field::{F128x8, Weights8};
        let packed = t.as_chunks::<8>().0.iter().map(Weights8::new).collect();
        let table = t.as_chunks::<8>().0.iter().map(F128x8::from_array).collect();
        Low { table, packed }
    }
}
