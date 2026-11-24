//! lvm6 (WP R5, PATCHES.md): leanVM's own opening machinery, for FORMAT6 §6.6's prover (`r3core::open6`), which
//! drives it through the v6 transcript. The pieces are those of `whir::recursive_prover_with_prepared_basis`,
//! unchanged:
//!
//! - [`Level0`]: level 0's fold rounds on the weight's terms (`whir_lanes::LaneRounds` over
//!   `stack_open::basis`'s projections), the weight never written out over the stack; the terms are FORMAT6 §6.5's
//!   list ([`PointTerm`], [`LaneTerm`], [`RingTerm`], `stack_open::basis::six`);
//! - [`Rounds`]: a later level's dense fold rounds (`whir::Dense`);
//! - [`induce`]: the queries' batched column weight (`whir_induce::induce_basis_auto`).
//!
//! FORMAT6 orders the messages differently from leanVM's PCS (the level commitment, the OOD draw, the query
//! positions and the tail), so the transcript stays with the caller; every value here is a function of its
//! inputs alone (the thread count changes no byte).

use primitives::field::{F64, F128};

pub use crate::stack_open::six::{LaneTerm, PointTerm, RingTerm, low_vars};
pub use crate::tensor_algebra::DEGREE_E;

/// The `w`-th `F₂`-coordinate basis element of `E` (the order of a ring term's weights).
pub fn coordinate_basis(w: usize) -> F128 {
    crate::ring_switch::coordinate_basis(w)
}
use crate::whir::{Dense, FoldChallenges};
use crate::whir_lanes::LaneRounds;

/// A round's message `[u0, w, c0, c1]` (`whir::FoldTable`).
pub type Table = [F128; 4];

/// Level 0's fold rounds on the terms of the batched weight.
pub struct Level0(LaneRounds);

impl Level0 {
    /// `stack`: the committed lanes (whole lane blocks of `2^lane_vars` words, zero past them), of a stack of
    /// `2^log_n` words.
    pub fn new(
        stack: Vec<F64>,
        log_n: usize,
        lane_vars: usize,
        points: &[PointTerm],
        lanes: &[LaneTerm],
        rings: &[RingTerm],
    ) -> Self {
        let basis = crate::stack_open::six::initial_basis6(&stack, log_n, lane_vars, points, lanes, rings);
        Self(LaneRounds::new(stack, basis, 1 << lane_vars, false))
    }

    pub fn table(&mut self) -> Table {
        self.0.table()
    }

    pub fn fold(&mut self, alpha: F128, beta: F128) {
        self.0.fold(&FoldChallenges { alpha, beta });
    }

    /// The folded lane (low coefficients, then the rounds' high ones) and the weight over its low part.
    pub fn finish(self) -> (Vec<F128>, Vec<F128>) {
        let (p, w, _) = self.0.finish();
        (p, w)
    }
}

/// A later level's dense fold rounds: lanes coefficient by coefficient (`f[c·stride + lane]`), the weight over the
/// low coefficients in the same order.
pub struct Rounds(Dense);

impl Rounds {
    pub fn new(f: Vec<F128>, w: Vec<F128>, stride: usize) -> Self {
        Self(Dense { f, w, stride })
    }

    pub fn table(&self) -> Table {
        self.0.table()
    }

    pub fn fold(&mut self, alpha: F128, beta: F128) {
        self.0.fold(&FoldChallenges { alpha, beta });
    }

    pub fn stride(&self) -> usize {
        self.0.stride
    }

    pub fn into_parts(self) -> (Vec<F128>, Vec<F128>) {
        (self.0.f, self.0.w)
    }
}

/// `Σ_q weights[q]·X_·(x_q)` over the `2^log_msg_cols` novel-basis coefficients, `x_q` = query `q`'s domain point
/// of a codeword of `2^(log_msg_cols + log_inv_rate)` rows.
pub fn induce(log_msg_cols: usize, log_inv_rate: usize, queries: &[usize], weights: &[F128]) -> Vec<F128> {
    crate::whir_induce::induce_basis_auto(log_msg_cols, log_inv_rate, queries, weights)
}
