//! lvm6 (not leanVM; `PATCHES.md`, WP R2): the tree batch of `docs/lvm6/design/FORMAT6.md` §6.2 (BLUEPRINT §2.3 v3).
//!
//! The batch is the heap of `2N` rows of the data tree over `N = 2^k` blocks: row 1 is the root, row 0 a spare
//! whose left child is itself, row `κ = b + 2j` is child `b` of parent row `j`, leaf `i` is row `N + i`. `D(row)` is
//! output lanes 0–3 of the row's permutation. Committed per row, one stack slot (`2^(k+1)` words) each:
//! - slots 0–7, raw words: parent rows `j < N`: `D(2j)` then `D(2j+1)` (row 0: `0^4` then `h = D(1)`); leaf rows:
//!   block `x_i`, then zeros (FORMAT6 §2.1);
//! - slots 8–32: the state after 12 rounds;
//! - slots 33–63: zero here (other blocks of the real stack ride them; every opening below reads them).
//!
//! The permutation's input is never committed: it is `B_t(slots 0–7) + c_t` (the bytes `0x44 ‖ l ‖ r` or
//! `0x48 ‖ x` with Keccak-256 padding), and only the two ends of the reduction see that map. The 12 layers are
//! leanVM's `prover::prove_layer`, unchanged, on a [`Witness`] generated from those inputs.
//!
//! Ends, against leanVM's `Witness::prove` and `open.rs`:
//! - start (§6.2 rows 1–7): `δ = D(0)` as four `K` words, `ρ`, `D⁰`, `D¹`, `u`, the 21 other output lanes, then
//!   leanVM's first claim at `instance = (u, ρ)` with the committed middle at slot `8 + l` (leanVM: `25 + l`);
//! - middle opening (row 9): leanVM's `open_outputs` with the word weights on slots `8 + l`;
//! - input opening (row 10): the constants off the claim, 4 low row bits, the top row bit, 6 slot bits, then the
//!   64 slices, with the pull-back weights `pw^P`, `pw^L` on slots 0–7 and `pw^M` on slots 8–32.

use primitives::bit_fold::{BLOCK as ROWS, BitFold};
use primitives::field::{F64, F128, F128Unreduced};
use primitives::hash::STATE_LANES;
use primitives::field::dot_base;
use primitives::multilinear::{eq_table, interp, mle_eval, packed_eq, poly_eval};
use primitives::transcript::ProverState;
use verifier::keccak::LANE_BITS;

use crate::open::{Opening, WordOpening};
use crate::protocol::{Claim, dot};
use crate::{OutputClaim, Shape, Witness};

/// Middle lane `l` is slot `MID + l`.
pub const MID: usize = 8;
/// Slots of a stack row (`2^6`).
pub const SLOTS: usize = 64;
pub const TAG_ITEM: u8 = 0x48;
pub const TAG_NODE: u8 = 0x44;
/// FORMAT6 §6.2: `c^P` and `c^L` as (lane, bit).
pub const CP_BITS: [(usize, usize); 4] = [(0, 2), (0, 6), (8, 8), (16, 63)];
pub const CL_BITS: [(usize, usize); 4] = [(0, 3), (0, 6), (4, 8), (16, 63)];
/// FORMAT6 §6.2 grinds outside the reduction core (P18's `P.groups`, fixed for every shape).
pub const GRIND_RHO: u32 = 5;
pub const GRIND_U: u32 = 1;

/// The lanes of `w << 8` (`Sh_ℓ`), for an `8`-word string: lane `ℓ` of the byte string shifted by one byte.
fn shifted(words: &[u64; 8], lanes: &mut [u64; STATE_LANES]) {
    for l in 0..=8 {
        let lo = if l >= 1 { words[l - 1] >> 56 } else { 0 };
        let hi = if l < 8 { words[l] << 8 } else { 0 };
        lanes[l] ^= lo ^ hi;
    }
}

fn set_bits(lanes: &mut [u64; STATE_LANES], bits: &[(usize, usize)]) {
    for &(l, b) in bits {
        lanes[l] ^= 1 << b;
    }
}

/// The input of a parent row: `0x44 ‖ l ‖ r`, padded (BLUEPRINT §2.3, T1's `nodeLanes`).
pub fn node_lanes(l: &[u64; 4], r: &[u64; 4]) -> [u64; STATE_LANES] {
    let mut lanes = [0; STATE_LANES];
    shifted(&[l[0], l[1], l[2], l[3], r[0], r[1], r[2], r[3]], &mut lanes);
    set_bits(&mut lanes, &CP_BITS);
    lanes
}

/// The input of a leaf row: `0x48 ‖ x`, padded (T1's `itemLanes`).
pub fn item_lanes(x: &[u64; 4]) -> [u64; STATE_LANES] {
    let mut lanes = [0; STATE_LANES];
    shifted(&[x[0], x[1], x[2], x[3], 0, 0, 0, 0], &mut lanes);
    set_bits(&mut lanes, &CL_BITS);
    lanes
}

fn digest_of(input: &[u64; STATE_LANES]) -> [u64; 4] {
    let s = permuted(input);
    [s[0], s[1], s[2], s[3]]
}

/// Lanes 0–3 of a state (`D` of a row's output).
fn lanes4(s: &[u64; STATE_LANES]) -> [u64; 4] {
    [s[0], s[1], s[2], s[3]]
}

/// Rows a task of [`Tree::new`] writes and permutes.
const PERMUTE_CHUNK: usize = 1024;

/// `outs[i] = keccak_f(ins[i])`, eight states at a time (leanVM's `keccak_f_many`), on the pool.
fn permute_rows(ins: &[[u64; STATE_LANES]], outs: &mut [[u64; STATE_LANES]]) {
    parallel::chunks_mut(outs, PERMUTE_CHUNK, |c, outs| {
        outs.copy_from_slice(&ins[c * PERMUTE_CHUNK..][..outs.len()]);
        primitives::hash::keccak_f_many(outs);
    });
}

/// The permutation's output state (R6: kept per row, so §6.2's output claim needs no second permutation).
fn permuted(input: &[u64; STATE_LANES]) -> [u64; STATE_LANES] {
    let mut s = *input;
    primitives::hash::keccak_f(&mut s);
    s
}

/// The heap of the data tree over `blocks` (a power of two, at least `2^12`).
pub struct Tree {
    pub log_blocks: usize,
    pub blocks: Vec<[u64; 4]>,
    /// The permutation input of every row.
    pub inputs: Vec<[u64; STATE_LANES]>,
    /// `D(row)`.
    pub digests: Vec<[u64; 4]>,
    /// The permutation's whole output state of every row (R6; `digests` is its lanes 0–3).
    pub outputs: Vec<[u64; STATE_LANES]>,
    /// Dev forgeries (R2's tests): `(row, m, xor)` on a parent row's raw slot, the tree above it rehashed.
    pub forged: Vec<(usize, usize, u64)>,
}

impl Tree {
    /// Hash the tree level by level (each level on the pool; every digest a function of its index). R6: a level's
    /// inputs are written, then permuted eight at a time by leanVM's `keccak_f_many` (`keccak256`'s lanes), and every
    /// row's whole output state is kept for §6.2's output claim.
    pub fn new(blocks: Vec<[u64; 4]>) -> Self {
        let n = blocks.len();
        assert!(n.is_power_of_two() && n >= 1 << 12, "the tree batch takes 2^k blocks, k ≥ 12");
        let log_blocks = n.ilog2() as usize;
        let mut inputs = vec![[0u64; STATE_LANES]; 2 * n];
        let mut outputs = vec![[0u64; STATE_LANES]; 2 * n];
        parallel::chunks_mut(&mut inputs[n..], PERMUTE_CHUNK, |c, ins| {
            for (k, x) in ins.iter_mut().enumerate() {
                *x = item_lanes(&blocks[c * PERMUTE_CHUNK + k]);
            }
        });
        permute_rows(&inputs[n..], &mut outputs[n..]);
        // Parents `j` of level `[2^t, 2^(t+1))`, from the level below; row 0 last (`0^4 ‖ D(1)`).
        for t in (0..log_blocks).rev() {
            let (lo, hi) = (1usize << t, 1usize << (t + 1));
            let below = &outputs;
            parallel::chunks_mut(&mut inputs[lo..hi], PERMUTE_CHUNK, |c, ins| {
                for (k, x) in ins.iter_mut().enumerate() {
                    let j = lo + c * PERMUTE_CHUNK + k;
                    *x = node_lanes(&lanes4(&below[2 * j]), &lanes4(&below[2 * j + 1]));
                }
            });
            permute_rows(&inputs[lo..hi], &mut outputs[lo..hi]);
        }
        inputs[0] = node_lanes(&[0; 4], &lanes4(&outputs[1]));
        outputs[0] = permuted(&inputs[0]);
        let digests = outputs.iter().map(lanes4).collect();
        Self { log_blocks, blocks, inputs, digests, outputs, forged: Vec::new() }
    }

    /// Dev (TOY2's A1): parent row `row ≥ 1` commits a wrong word in slot `m < 8` and is hashed from it, and so is
    /// every row above it; `h` becomes the forged root. Only the wiring (W) at that slot is broken.
    pub fn forge(&mut self, row: usize, m: usize, xor: u64) {
        assert!(row >= 1 && row < 1 << self.log_blocks && m < 8);
        self.forged.push((row, m, xor));
        let mut k = row;
        while k >= 1 {
            let w: [u64; 8] = std::array::from_fn(|j| self.raw(k, j));
            self.inputs[k] = node_lanes(&[w[0], w[1], w[2], w[3]], &[w[4], w[5], w[6], w[7]]);
            self.outputs[k] = permuted(&self.inputs[k]);
            self.digests[k] = digest_of(&self.inputs[k]);
            k /= 2;
        }
        self.inputs[0] = node_lanes(&[0; 4], &self.digests[1]);
        self.outputs[0] = permuted(&self.inputs[0]);
        self.digests[0] = digest_of(&self.inputs[0]);
    }

    pub fn rows(&self) -> usize {
        2 << self.log_blocks
    }

    /// `OutputClaim::of_inputs(self.shape(), &self.inputs, instance)` without permuting again (R6): every row is
    /// an instance, so there is no padding one, and the sums are the same field elements. Per block of `2^10` rows,
    /// each lane's words go through leanVM's MLE kernel (`packed_eq` of the low 10 variables, `dot_base`), scaled
    /// by `eq` of the high ones.
    pub fn output_claim(&self, instance: Vec<F128>) -> OutputClaim {
        const LOW: usize = 10;
        assert_eq!(instance.len(), self.shape().n_log());
        assert!(instance.len() >= LOW);
        let low = packed_eq(&instance[..LOW]);
        let high = eq_table(&instance[LOW..]);
        let lanes = parallel::fold_reduce(
            self.rows() >> LOW,
            || [F128::ZERO; STATE_LANES],
            |acc, b| {
                let mut cols = vec![F64(0); STATE_LANES << LOW];
                for (r, out) in self.outputs[b << LOW..][..1 << LOW].iter().enumerate() {
                    for (l, &w) in out.iter().enumerate() {
                        cols[(l << LOW) + r] = F64(w);
                    }
                }
                for (acc, col) in acc.iter_mut().zip(cols.chunks_exact(1 << LOW)) {
                    *acc += high[b] * dot_base(&low, col).reduce();
                }
            },
            |mut a, b| {
                for (a, b) in a.iter_mut().zip(b) {
                    *a += b;
                }
                a
            },
        );
        OutputClaim { instance, lanes }
    }

    /// The batch's [`Shape`]: `2N` permutations, depth 12.
    pub fn shape(&self) -> Shape {
        Shape::new(self.rows(), 12)
    }

    /// `h = D(1)`, as 32 bytes (`dataRoot` of the blocks).
    pub fn root(&self) -> [u8; 32] {
        let mut h = [0u8; 32];
        for (m, w) in self.digests[1].iter().enumerate() {
            h[8 * m..8 * m + 8].copy_from_slice(&w.to_le_bytes());
        }
        h
    }

    /// Raw word `m < 8` of a row's slots 0–7 (FORMAT6 §2.1's honest values).
    pub fn raw(&self, row: usize, m: usize) -> u64 {
        let n = 1usize << self.log_blocks;
        let forged = self.forged.iter().filter(|f| (f.0, f.1) == (row, m)).fold(0, |a, f| a ^ f.2);
        forged ^ match (row < n, m < 4) {
            (true, true) if row == 0 => 0,
            (true, true) => self.digests[2 * row][m],
            (true, false) => self.digests[2 * row + 1][m - 4],
            (false, true) => self.blocks[row - n][m],
            (false, false) => 0,
        }
    }

    /// The witness and the committed stack (`2^(k+1+6)` words, slot `s` of row `r` at `s·2N + r`).
    pub fn witness(&self) -> (Witness, Vec<F64>) {
        let shape = self.shape();
        let n = shape.n();
        assert_eq!(n, self.rows());
        let mut stack = vec![F64(0); SLOTS * n];
        // leanVM's layout first: inputs at slots 0–24, middle states at 25–49, zero past them.
        let witness = Witness::generate(shape, &self.inputs, &mut stack);
        // Middle states to slots 8–32 (ascending: a source slot is read before it is overwritten).
        for l in 0..STATE_LANES {
            stack.copy_within((STATE_LANES + l) * n..(STATE_LANES + l + 1) * n, (MID + l) * n);
        }
        stack[(MID + STATE_LANES) * n..].fill(F64(0));
        let (raw, _) = stack.split_at_mut(MID * n);
        parallel::chunks_mut(raw, n, |m, col| {
            if !self.forged.is_empty() {
                for (row, w) in col.iter_mut().enumerate() {
                    *w = F64(self.raw(row, m));
                }
                return;
            }
            // R6: `raw` without the forgery lookup, a column at a time (the same words).
            let (parents, leaves) = col.split_at_mut(n / 2);
            for (row, w) in parents.iter_mut().enumerate() {
                *w = F64(if m < 4 { if row == 0 { 0 } else { self.digests[2 * row][m] } } else { self.digests[2 * row + 1][m - 4] });
            }
            for (block, w) in self.blocks.iter().zip(leaves) {
                *w = F64(if m < 4 { block[m] } else { 0 });
            }
        });
        (witness, stack)
    }
}

/// What §6.2 leaves for the stacked opening (FORMAT6 §6.5 claims 1–14).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeOpenings {
    pub delta: [u64; 4],
    pub rho: Vec<F128>,
    /// `D⁰_m`, `D¹_m`.
    pub d: [[F128; 4]; 2],
    /// The middle opening: `q̃((u, ρ), ϱ) = c_out`.
    pub outputs: WordOpening,
    /// The input opening: the 64 slices at `(ϱ_low, r_mid, ϱ_top, ϱ_slot)`.
    pub inputs: Opening,
}

impl TreeOpenings {
    /// The stack points (row variables then slot variables) and values of the 8 wiring and 4 root claims, in §6.5's
    /// order: `q̃((ρ,0), slot m) = D⁰_m + eq(ρ,0)·δ_m`, `q̃((ρ,0), slot 4+m) = D¹_m`, `q(row 0, slot 4+m) = h_m`.
    pub fn wiring_claims(&self, h: &[u64; 4]) -> Vec<(Vec<F128>, F128)> {
        let eq0: F128 = self.rho.iter().map(|&r| F128::ONE + r).product();
        let slot = |s: usize| (0..6).map(|b| F128::new((s >> b & 1) as u64, 0)).collect::<Vec<_>>();
        let row = [&self.rho[..], &[F128::ZERO]].concat();
        let zero_row = vec![F128::ZERO; row.len()];
        let mut v = Vec::new();
        for m in 0..4 {
            v.push(([&row[..], &slot(m)].concat(), self.d[0][m] + eq0 * F128::new(self.delta[m], 0)));
        }
        for m in 0..4 {
            v.push(([&row[..], &slot(4 + m)].concat(), self.d[1][m]));
        }
        for (m, &w) in h.iter().enumerate() {
            v.push(([&zero_row[..], &slot(4 + m)].concat(), F128::new(w, 0)));
        }
        v
    }
}

/// A dev tamper (R2's tests): one prover message of §6.2 off by one bit, the prover going on with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tamper {
    None,
    /// `δ₀`.
    Delta,
    /// `D⁰₀`.
    D0,
    /// `o₇`.
    O7,
    /// `c_st`.
    Cst,
    /// `c_out`.
    Cout,
    /// `s₅`.
    Slice5,
}

fn flip(x: F128, on: bool) -> F128 {
    if on { x + F128::ONE } else { x }
}

/// §6.2, on a v6 transcript right after §6.1 (`y₀` pending): rows 1–10.
pub fn prove_tree(ps: &mut ProverState, tree: &Tree, witness: &Witness, stack: &[F64]) -> TreeOpenings {
    prove_tree_with(ps, tree, witness, stack, Tamper::None)
}

/// [`prove_tree`] with a [`Tamper`].
pub fn prove_tree_with(ps: &mut ProverState, tree: &Tree, witness: &Witness, stack: &[F64], tamper: Tamper) -> TreeOpenings {
    let shape = witness.shape;
    let n = shape.n();
    let half = n / 2;
    assert_eq!((shape.depth(), n, stack.len()), (12, tree.rows(), SLOTS * n));
    // 1. δ = D(0) (row 0's slots 0–3 are zero), four K words.
    let mut delta = tree.digests[0];
    delta[0] ^= u64::from(tamper == Tamper::Delta);
    ps.chain().expect("§6.2 runs on the v6 transcript").absorb_k(&delta);
    // 2. ρ ∈ E^(k): G(5), D(k−1).
    ps.grind(GRIND_RHO);
    let rho = ps.sample_vec(shape.n_log() - 1);
    // 3. D^b_m = Σ_j eq(ρ, j)·D_m(b + 2j).
    let eq = eq_table(&rho);
    let sums = parallel::fold_reduce(
        half,
        || [F128Unreduced::ZERO; 8],
        |acc, j| {
            for b in 0..2 {
                for m in 0..4 {
                    acc[4 * b + m] ^= eq[j].mul_base_unreduced(F64(tree.digests[b + 2 * j][m]));
                }
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
            a
        },
    );
    let mut d: [[F128; 4]; 2] = std::array::from_fn(|b| std::array::from_fn(|m| sums[4 * b + m].reduce()));
    let honest_d = d;
    d[0][0] = flip(d[0][0], tamper == Tamper::D0);
    ps.add_scalars(&d[0]);
    ps.add_scalars(&d[1]);
    drop(eq);
    // 4. u: G(1).
    ps.grind(GRIND_U);
    let u = ps.sample();
    let instance = [&[u][..], &rho].concat();
    // 5. o₄ … o₂₄ (o₀ … o₃ are V's own, from D⁰, D¹).
    // leanVM's `OutputClaim::of_inputs` (every row written: no padding instance), on the outputs `Tree::new` kept.
    let mut output = tree.output_claim(instance.clone());
    for m in 0..4 {
        assert_eq!(output.lanes[m], (F128::ONE + u) * honest_d[0][m] + u * honest_d[1][m], "o_m from D^b");
    }
    output.lanes[7] = flip(output.lanes[7], tamper == Tamper::O7);
    ps.add_scalars(&output.lanes[4..]);
    // 6–10. leanVM's reduction with the tree's ends.
    let (outputs, inputs) = reduce(ps, witness, stack, &output, tamper);
    TreeOpenings { delta, rho, d, outputs, inputs }
}

/// Rows 6–10: leanVM's `Witness::prove` with slot `8 + l` for the middle and the tree's input opening.
fn reduce(
    ps: &mut ProverState,
    witness: &Witness,
    stack: &[F64],
    output: &OutputClaim,
    tamper: Tamper,
) -> (WordOpening, Opening) {
    let shape = witness.shape;
    let n = shape.n();
    ps.grind(fiat_shamir::grinding_bits((shape.seg_log() + LANE_BITS) as u128));
    let (segment, r_lane) = (ps.sample_vec(shape.seg_log()), ps.sample_vec(LANE_BITS));
    let mut first = crate::first(shape, output, segment, &r_lane);
    let instance = &output.instance;
    let words = parallel::map_collect(SLOTS, |slot| mle_eval(&stack[slot * n..][..n], instance));
    let word_weights = mid_word_weights(shape, &first);
    let committed_value = flip(dot(&words, &word_weights), tamper == Tamper::Cst);
    ps.add_scalar(committed_value);
    first.value += committed_value;

    let mut claim = first.clone();
    let mut scratch = crate::prover::Scratch::new(shape);
    for step in 0..shape.depth() {
        claim = crate::prover::prove_layer(ps, witness, &mut scratch, step, &claim);
    }
    drop(scratch);
    // 9. The middle opening (leanVM's `open_outputs`, slots 8 + l).
    let mut value = committed_value;
    let (word, _, slot) = prove_rounds(ps, words, word_weights, 1, F128::ONE, &mut value);
    let c_out = flip(word[0], tamper == Tamper::Cout);
    ps.add_scalar(c_out);
    let outputs = WordOpening { point: [&instance[..], &slot].concat(), value: c_out };
    // 10. The input opening.
    let inputs = open_inputs(ps, shape, stack, &claim, tamper == Tamper::Slice5);
    (outputs, inputs)
}

/// The first claim's weight on each slot's word: `eq(r_seg, 0)·eq(r_lane, l)` on slot `8 + l` (leanVM's
/// `word_weights` with the middle at slot 8).
fn mid_word_weights(shape: Shape, claim: &Claim) -> Vec<F128> {
    let seg0 = eq_table(&claim.point[shape.pack_vars()..])[0];
    let mut w = vec![F128::ZERO; SLOTS];
    for l in 0..STATE_LANES {
        w[MID + l] = seg0 * claim.weights[64 * l];
    }
    w
}

/// `pw(o, z)`: the weight of bit `z` of raw word `o` under `w << 8` (`weights_{64o+z+8}`, `z < 56`;
/// `weights_{64(o+1)+z−56}`, `z ≥ 56`).
fn pull_back(weights: &[F128], o: usize, z: usize) -> F128 {
    if z < 56 { weights[64 * o + z + 8] } else { weights[64 * (o + 1) + z - 56] }
}

/// The weight the claim (constants taken off) puts on bit `z` of slot `s` of a row with top bit `t`, without the
/// `eq(r_top, t)` factor: `(1+r'_seg)·pw^t(s, z) + r'_seg·pw^M(s, z)`. Entry `64·s + z`.
fn top_weights(claim: &Claim, r_seg: F128, t: usize) -> Vec<F128> {
    let mut w = vec![F128::ZERO; 64 * SLOTS];
    let raw = if t == 0 { 8 } else { 4 };
    for s in 0..raw {
        for z in 0..64 {
            w[64 * s + z] = (F128::ONE + r_seg) * pull_back(&claim.weights, s, z);
        }
    }
    for l in 0..STATE_LANES {
        for z in 0..64 {
            w[64 * (MID + l) + z] = r_seg * claim.weights[64 * l + z];
        }
    }
    w
}

/// `C^t = Σ weights_j` over the set bits of `c_t`.
fn constants(claim: &Claim, bits: &[(usize, usize)]) -> F128 {
    bits.iter().map(|&(l, b)| claim.weights[64 * l + b]).sum()
}

/// Row 10: the claim after 12 layers, on segment 0's inputs `B_t(slots) + c_t` and segment 1's committed middle,
/// to the 64 slices of the stack at one point.
fn open_inputs(ps: &mut ProverState, shape: Shape, stack: &[F64], claim: &Claim, tamper5: bool) -> Opening {
    let n = shape.n();
    let pv = shape.pack_vars();
    let pack = &claim.point[..pv];
    let r_seg = claim.point[pv];
    let (r_mid, r_top) = (&pack[..pv - 1], pack[pv - 1]);
    let mubar: F128 = claim.mu.iter().copied().sum();
    let mut value = claim.value
        + (F128::ONE + r_seg)
            * mubar
            * ((F128::ONE + r_top) * constants(claim, &CP_BITS) + r_top * constants(claim, &CL_BITS));
    let wt = [top_weights(claim, r_seg, 0), top_weights(claim, r_seg, 1)];
    let eq_top = [F128::ONE + r_top, r_top];
    // slices[t·64 + s][i][z] = Σ_pm eq(r_mid, pm)·bit z of q[i + 16·pm + t·n/2, s].
    let slices = instance_slices(stack, n, r_mid);
    let per_instance: Vec<F128> = (0..16)
        .map(|i| {
            let mut acc = F128::ZERO;
            for t in 0..2 {
                let mut inner = F128::ZERO;
                for s in 0..MID + STATE_LANES {
                    inner += dot(&wt[t][64 * s..][..64], &slices[64 * t + s][i]);
                }
                acc += eq_top[t] * inner;
            }
            acc
        })
        .collect();
    let (_, mu, low) = prove_rounds(ps, per_instance, claim.mu.to_vec(), 1, F128::ONE, &mut value);
    let eq_low = eq_table(&low);
    let mut table = vec![F128::ZERO; 2 * 64 * SLOTS];
    let mut weights = vec![F128::ZERO; 2 * 64 * SLOTS];
    for s in 0..SLOTS {
        for t in 0..2 {
            let at = 64 * (t + 2 * s);
            for z in 0..64 {
                table[at + z] = (0..16).map(|i| eq_low[i] * slices[64 * t + s][i][z]).sum();
                weights[at + z] = eq_top[t] * wt[t][64 * s + z];
            }
        }
    }
    let (mut s_z, _, rest) = prove_rounds(ps, table, weights, 64, mu[0], &mut value);
    s_z[5] = flip(s_z[5], tamper5);
    ps.add_scalars(&s_z);
    Opening { point: [&low[..], r_mid, &rest[..]].concat(), slices: s_z }
}

/// Byte `b` of word `x` at `8x + b`.
fn le_bytes(words: &[u64; 8]) -> [u8; 64] {
    let mut bytes = [0u8; 64];
    for (bytes, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        *bytes = word.to_le_bytes();
    }
    bytes
}

/// For each top bit `t`, slot `s` and instance `i` of a pack: the 64 slices of the stack's column `s` over the rows
/// `i + 16·pm + t·n/2` at `r_mid` (`2^|r_mid|` rows each). Entry `[64t + s][i][z]`. A task per `(t, s)`; a chunk of
/// 4,096 consecutive rows is 256 values of `pm` for every `i`, one [`BitFold`] by `eq` of `r_mid`'s low 8
/// variables, its sums scaled by the high table.
fn instance_slices(stack: &[F64], n: usize, r_mid: &[F128]) -> Vec<[[F128; 64]; 16]> {
    assert!(r_mid.len() >= 8 && 16 << r_mid.len() == n / 2);
    let (lo, hi) = r_mid.split_at(8);
    let fold = BitFold::new(&eq_table(lo));
    let high = eq_table(hi);
    let half = n / 2;
    parallel::map_collect(2 * SLOTS, |task| {
        let (t, s) = (task / SLOTS, task % SLOTS);
        let col = &stack[s * n + t * half..][..half];
        let mut acc = [[F128Unreduced::ZERO; 64]; 16];
        for (c, &scale) in high.iter().enumerate() {
            let chunk = &col[c << 12..][..1 << 12];
            // R6: zero test 64 words at a time (vectorised OR), exiting at the first nonzero block.
            if chunk.chunks_exact(64).all(|b| b.iter().fold(0, |a, w| a | w.0) == 0) {
                continue;
            }
            for (i, acc) in acc.iter_mut().enumerate() {
                let mut cols = [[0u8; ROWS]; 32];
                for (g, col) in cols.iter_mut().enumerate() {
                    let words: [u64; 8] = std::array::from_fn(|w| chunk[i + 16 * (8 * g + w)].0);
                    primitives::bits::bit_transpose_64bytes(&le_bytes(&words), col);
                }
                let mut sums = [F128::ZERO; ROWS];
                fold.fold_columns(&cols, &mut sums);
                for (a, s) in acc.iter_mut().zip(sums) {
                    *a ^= scale.mul_unreduced(s);
                }
            }
        }
        acc.map(|a| a.map(F128Unreduced::reduce))
    })
}

// ------------------------------------------------------------------ leanVM's `open.rs` round helpers (private there)

/// The sum over rows of the two tables' dot product: its round values at `0` and infinity.
fn round_values(a: &[F128], b: &[F128], width: usize) -> (F128, F128) {
    let mut zero = F128::ZERO;
    let mut infinity = F128::ZERO;
    for (a, b) in a.chunks_exact(2 * width).zip(b.chunks_exact(2 * width)) {
        for j in 0..width {
            zero += a[j] * b[j];
            infinity += (a[j] + a[width + j]) * (b[j] + b[width + j]);
        }
    }
    (zero, infinity)
}

fn fold(table: &[F128], width: usize, challenge: F128) -> Vec<F128> {
    table
        .chunks_exact(2 * width)
        .flat_map(|pair| (0..width).map(move |j| interp(pair[j], pair[width + j], challenge)))
        .collect()
}

/// Bind the leading variable of `scale * sum of a * b` in every round, down to one row of `a` (plain rounds
/// `R(2, g)`: `c₀, c₂` sent).
fn prove_rounds(
    ps: &mut ProverState,
    mut a: Vec<F128>,
    mut b: Vec<F128>,
    width: usize,
    scale: F128,
    value: &mut F128,
) -> (Vec<F128>, Vec<F128>, Vec<F128>) {
    let mut point = Vec::new();
    while a.len() > width {
        let (zero, infinity) = round_values(&a, &b, width);
        let (zero, infinity) = (scale * zero, scale * infinity);
        let coeffs = [zero, *value + infinity, infinity];
        ps.add_round_poly(&coeffs, false);
        let challenge = ps.sample();
        *value = poly_eval(&coeffs, challenge);
        point.push(challenge);
        a = fold(&a, width, challenge);
        b = fold(&b, width, challenge);
    }
    (a, b, point)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The lane maps are the bytes `0x44 ‖ l ‖ r` / `0x48 ‖ x` with Keccak-256 padding (FORMAT6 §6.2's bit sets).
    #[test]
    fn lanes_are_the_padded_bytes() {
        let mut x = 0x1234_5678_9abc_def0u64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for _ in 0..100 {
            let (l, r): ([u64; 4], [u64; 4]) = (std::array::from_fn(|_| next()), std::array::from_fn(|_| next()));
            let block = |msg: &[u8]| {
                let mut b = [0u8; 200];
                b[..msg.len()].copy_from_slice(msg);
                b[msg.len()] ^= 1;
                b[135] ^= 0x80;
                std::array::from_fn::<u64, 25, _>(|i| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap()))
            };
            let bytes = |w: &[u64]| w.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>();
            let node = [&[TAG_NODE][..], &bytes(&l), &bytes(&r)].concat();
            let item = [&[TAG_ITEM][..], &bytes(&l)].concat();
            assert_eq!(node_lanes(&l, &r), block(&node));
            assert_eq!(item_lanes(&l), block(&item));
            // And the digest is Keccak-256 of those bytes.
            let d = digest_of(&node_lanes(&l, &r));
            assert_eq!(bytes(&d), primitives::hash::hash(&node).to_vec());
        }
    }
}
