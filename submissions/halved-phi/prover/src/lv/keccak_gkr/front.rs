//! E2F (lvm2 S1, stage S2GF): the Keccak GKR's output claims and the KS run with its openings, over the front's field
//! ([`Ext`]). At E3 (`W = 3`) every entry delegates to the E3 code (`open.rs`, [`OutputClaim::of_inputs_padded`],
//! [`Witness::prove`]), so S2GM's bytes are unchanged; at E2 (`W = 2`) the same protocol runs on E2 values with the
//! E2 transcript (16-byte scalars, a nonce before every challenge: [`ProverState::challenge`]). The E2 openings are
//! the portable forms of `open.rs` (leanVM 0b850750's), shared by both trees: KS is small.

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::{Ext, F64, F128, F192, Unreduced};

use crate::lv::keccak_gkr::basis::byte_sums;
use crate::lv::keccak_gkr::keccak::{BITS, LANES, LANE_VARS};
use crate::lv::keccak_gkr::open::state_words;
use crate::lv::keccak_gkr::protocol::{Claim, dot};
use crate::lv::keccak_gkr::witness::{BLOCK_WORDS, Shape, Witness};
use crate::lv::keccak_gkr::{OutputClaim, first, prover};

/// `F` as `F192` when it is (`W = 3`).
fn e3<F: Ext<W>, const W: usize>(x: F) -> F192 {
    let l = x.to_limbs();
    F192::from_limbs(std::array::from_fn(|k| if k < W { l[k] } else { 0 }))
}

/// `F192` as `F` (`W = 3`).
fn of_e3<F: Ext<W>, const W: usize>(x: F192) -> F {
    debug_assert!(W == 3, "an E3 value as F192");
    let l = x.to_limbs();
    F::from_limbs(std::array::from_fn(|k| l[k]))
}


/// The output claim of a batch of `inputs` (padded with all-zero inputs) at `instance`, in `F`: at E3
/// [`OutputClaim::of_inputs_padded`] (`padded`) or [`OutputClaim::of_inputs`].
pub fn output_claim_in<F: Ext<W>, const W: usize>(shape: Shape, inputs: &[[u64; LANES]], instance: Vec<F>, padded: bool) -> OutputClaim<F> {
    if W == 3 {
        let inst: Vec<F192> = instance.iter().map(|&x| e3(x)).collect();
        let c = if padded { OutputClaim::of_inputs_padded(shape, inputs, inst) } else { OutputClaim::of_inputs(shape, inputs, inst) };
        return OutputClaim { instance, lanes: c.lanes.map(of_e3) };
    }
    let permute = |mut state: [u64; LANES]| {
        crate::lv::primitives::hash::keccak_f(&mut state);
        state
    };
    let padding = permute([0; LANES]);
    let len = inputs.len();
    let eq = crate::lvm::front::eq_prefix(&instance, len);
    const RUN: usize = 64;
    let mut lanes = crate::lv::parallel::fold_reduce(
        len.div_ceil(RUN),
        || [F::Unreduced::ZERO; LANES],
        |acc, task| {
            let (lo, hi) = (RUN * task, (RUN * task + RUN).min(len));
            let mut states = [[0u64; LANES]; RUN];
            let states = &mut states[..hi - lo];
            states.copy_from_slice(&inputs[lo..hi]);
            crate::lv::primitives::hash::keccak_f_many(states);
            for (i, output) in states.iter().enumerate() {
                let e = eq[lo + i];
                for (acc, &word) in acc.iter_mut().zip(output) {
                    *acc ^= e.mul_base_unreduced(F64(word));
                }
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
            a
        },
    )
    .map(|x| x.reduce());
    if len < shape.n() {
        let rest: F = F::ONE + eq.iter().copied().sum::<F>();
        for (l, w) in lanes.iter_mut().zip(padding) {
            *l += rest.mul_base(F64(w));
        }
    }
    OutputClaim { instance, lanes }
}

/// The KS run's openings in its field: the committed segment outputs as a word claim `(point, value)`, the inputs as
/// 64 bit slices at `point`.
pub struct OpeningsIn<F> {
    pub outputs: Option<(Vec<F>, F)>,
    pub inputs: (Vec<F>, Vec<F>),
}

impl Witness {
    /// [`Witness::prove`] in the front's field: the segment and lane challenges, the committed segment outputs' value,
    /// the layers, then the output and input openings.
    pub fn prove_in<F: Ext<W>, const W: usize>(&self, ps: &mut ProverState, committed: &[F64], output: &OutputClaim<F>) -> OpeningsIn<F> {
        if W == 3 {
            let out3 = OutputClaim { instance: output.instance.iter().map(|&x| e3(x)).collect(), lanes: output.lanes.map(e3) };
            let o = self.prove(ps, committed, &out3);
            let conv = |v: Vec<F192>| v.into_iter().map(of_e3).collect::<Vec<F>>();
            return OpeningsIn {
                outputs: o.outputs.map(|w| (conv(w.point), of_e3(w.value))),
                inputs: (conv(o.inputs.point), conv(o.inputs.slices)),
            };
        }
        let shape = self.shape;
        assert_eq!(committed.len(), 1 << shape.stack_log(), "the openings are claims on the whole committed block");
        let segment = ps.challenges::<F, W>(Grp::C1, shape.seg_log());
        let r_lane = ps.challenges::<F, W>(Grp::C1, LANE_VARS);
        let mut first = first::<F, W>(shape, output, segment, &r_lane);
        let instance = &output.instance;
        let (folded, committed_value) = crate::lv::tracing::info_span!("Outputs/E2").in_scope(|| output_words(shape, committed, instance, &first));
        if shape.segments() > 1 {
            ps.add_ext(&[committed_value]);
        }
        first.value += committed_value;
        let mut claim = first.clone();
        let mut scratch = prover::Scratch::<W>::new(shape);
        for step in 0..shape.depth {
            claim = crate::lv::tracing::info_span!("Layer/E2", step).in_scope(|| prover::prove_layer::<F, W>(ps, self, &mut scratch, step, &claim));
        }
        let _span = crate::lv::tracing::info_span!("Openings/E2").entered();
        let outputs = (shape.segments() > 1).then(|| open_outputs(ps, shape, instance, &first, committed_value, folded));
        let inputs = open_inputs(ps, self, committed, &claim);
        OpeningsIn { outputs, inputs }
    }
}

/// `open.rs`'s `slot_weights`, generic.
fn slot_weights<F: Ext<W>, const W: usize>(shape: Shape, claim: &Claim<F>, first: usize, count: usize) -> Vec<F> {
    let segments = F::eq_table(&claim.point[shape.pack_vars()..]);
    let mut out = vec![F::ZERO; 64 << shape.slot_log()];
    for segment in 0..count {
        let base = 64 * LANES * (first + segment);
        for j in 0..BITS {
            out[base + j] = segments[segment] * claim.weights[j];
        }
    }
    out
}

fn le_bytes(words: &[u64; BLOCK_WORDS]) -> [u8; 64] {
    let mut bytes = [0u8; 64];
    for (bytes, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        *bytes = word.to_le_bytes();
    }
    bytes
}

/// `open.rs`'s `fold_packs`, generic: entry `(i + 16·slot)·64 + z`.
fn fold_packs<F: Ext<W>, const W: usize>(witness: &Witness, point: &[F]) -> Vec<F> {
    let shape = witness.shape;
    let written = witness.written();
    let padding: F = F::eq_table(&point[5..])[written..].iter().copied().sum();
    let run_vars = (point.len() - 5).min(3);
    let (low, runs) = (F::eq_table(&point[..5 + run_vars]), F::eq_table(&point[5 + run_vars..]));
    let tables: Vec<[F; 256]> = (0..4 << run_vars)
        .map(|t| byte_sums(&std::array::from_fn(|w| low[t % 4 + 4 * w + 32 * (t / 4)])))
        .collect();
    let positions: Vec<[F; 16]> = crate::lv::parallel::map_collect(64 * shape.slots(), |task| {
        let (lane, z) = (task / 64, task % 64);
        let round = shape.depth * (lane / LANES);
        let j = 64 * (lane % LANES) + z;
        let mut acc = [F::Unreduced::ZERO; 16];
        for (run, &scale) in runs.iter().enumerate().take(written.div_ceil(1 << run_vars)) {
            let mut sums = [F::ZERO; 16];
            for block in 0..(1 << run_vars).min(written - (run << run_vars)) {
                let words = state_words(witness, round, (run << run_vars) + block, j);
                let mut gathered = [0u8; 64];
                crate::lv::primitives::bits::bit_transpose_64bytes(&le_bytes(&words), &mut gathered);
                for (i, sum) in sums.iter_mut().enumerate() {
                    for p in 0..4 {
                        *sum += tables[4 * block + p][gathered[8 * (2 * p + i / 8) + i % 8] as usize];
                    }
                }
            }
            for (acc, sum) in acc.iter_mut().zip(sums) {
                *acc ^= scale.mul_unreduced(sum);
            }
        }
        let pad = written < shape.n_blocks() && state_words(witness, round, written, j)[0] & 1 == 1;
        acc.map(|acc| if pad { acc.reduce() + padding } else { acc.reduce() })
    });
    let mut out = vec![F::ZERO; (16 * 64) << shape.slot_log()];
    for (task, sums) in positions.iter().enumerate() {
        let (lane, z) = (task / 64, task % 64);
        for (i, &sum) in sums.iter().enumerate() {
            out[(i + 16 * lane) * 64 + z] = sum;
        }
    }
    out
}

fn round_values<F: Ext<W>, const W: usize>(a: &[F], b: &[F], width: usize) -> (F, F) {
    let (mut zero, mut infinity) = (F::ZERO, F::ZERO);
    for (a, b) in a.chunks_exact(2 * width).zip(b.chunks_exact(2 * width)) {
        for j in 0..width {
            zero += a[j] * b[j];
            infinity += (a[j] + a[width + j]) * (b[j] + b[width + j]);
        }
    }
    (zero, infinity)
}

fn fold<F: Ext<W>, const W: usize>(table: &[F], width: usize, c: F) -> Vec<F> {
    table
        .chunks_exact(2 * width)
        .flat_map(|pair| (0..width).map(move |j| pair[j] + c * (pair[j] + pair[width + j])))
        .collect()
}

/// `open.rs`'s `prove_rounds` in `F`: degree-2 rounds (group `c = 2`).
fn prove_rounds<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    mut a: Vec<F>,
    mut b: Vec<F>,
    width: usize,
    scale: F,
    value: &mut F,
) -> (Vec<F>, Vec<F>, Vec<F>) {
    let mut point = Vec::new();
    while a.len() > width {
        let (zero, infinity) = round_values(&a, &b, width);
        let (zero, infinity) = (scale * zero, scale * infinity);
        let coeffs = [zero, *value + infinity, infinity];
        ps.add_round_poly_ext(&coeffs, false);
        let c = ps.challenge::<F, W>(Grp::C2);
        *value = F::poly_eval(&coeffs, c);
        point.push(c);
        a = fold(&a, width, c);
        b = fold(&b, width, c);
    }
    (a, b, point)
}

fn word_weights<F: Ext<W>, const W: usize>(shape: Shape, claim: &Claim<F>) -> Vec<F> {
    slot_weights(shape, claim, 1, shape.segments() - 1).into_iter().step_by(64).collect()
}

/// Every slot of the committed block as a word at `instance`, and the part of `claim` on the committed segment outputs.
fn output_words<F: Ext<W>, const W: usize>(shape: Shape, committed: &[F64], instance: &[F], claim: &Claim<F>) -> (Vec<F>, F) {
    let n = shape.n();
    let eq = F::eq_table(instance);
    let words: Vec<F> = crate::lv::parallel::map_collect(1 << shape.slot_log(), |slot| {
        let mut acc = F::Unreduced::ZERO;
        for (e, w) in eq.iter().zip(&committed[slot * n..][..n]) {
            acc ^= e.mul_base_unreduced(*w);
        }
        acc.reduce()
    });
    let value = dot(&words, &word_weights(shape, claim));
    (words, value)
}

fn open_outputs<F: Ext<W>, const W: usize>(ps: &mut ProverState, shape: Shape, instance: &[F], claim: &Claim<F>, mut value: F, words: Vec<F>) -> (Vec<F>, F) {
    let (word, _, slot) = prove_rounds(ps, words, word_weights(shape, claim), 1, F::ONE, &mut value);
    let word = word[0];
    ps.add_ext(&[word]);
    ([instance, &slot].concat(), word)
}

/// `open.rs`'s `spare_slices`, generic.
fn spare_slices<F: Ext<W>, const W: usize>(shape: Shape, committed: &[F64], instance: &[F]) -> Vec<[F; 64]> {
    let (n, spare) = (shape.n(), (1 << shape.slot_log()) - shape.slots());
    let eq = F::eq_table(instance);
    let (groups, slots) = (eq.as_chunks::<8>().0, &committed[shape.slots() * n..]);
    crate::lv::parallel::fold_reduce(
        n / 8,
        || vec![[F::ZERO; 64]; spare],
        |acc, group| {
            let table = byte_sums(&groups[group]);
            for (slot, acc) in acc.iter_mut().enumerate() {
                let words = std::array::from_fn(|w| slots[slot * n + 8 * group + w].0);
                let mut gathered = [0u8; 64];
                crate::lv::primitives::bits::bit_transpose_64bytes(&le_bytes(&words), &mut gathered);
                for (acc, &byte) in acc.iter_mut().zip(&gathered) {
                    *acc += table[byte as usize];
                }
            }
        },
        |mut a, b| {
            for (a, b) in a.iter_mut().flatten().zip(b.iter().flatten()) {
                *a += *b;
            }
            a
        },
    )
}

fn open_inputs<F: Ext<W>, const W: usize>(ps: &mut ProverState, witness: &Witness, committed: &[F64], claim: &Claim<F>) -> (Vec<F>, Vec<F>) {
    let shape = witness.shape;
    let pack = &claim.point[..shape.pack_vars()];
    let folded = fold_packs(witness, pack);
    let weights = slot_weights(shape, claim, 0, shape.segments());
    let per_instance: Vec<F> = crate::lv::parallel::map_collect(16, |i| {
        let mut acc = F::Unreduced::ZERO;
        for slot in 0..1usize << shape.slot_log() {
            for (x, y) in folded[(i + 16 * slot) * 64..][..64].iter().zip(&weights[slot * 64..][..64]) {
                acc ^= x.mul_unreduced(*y);
            }
        }
        acc.reduce()
    });
    let mut value = claim.value;
    let (_, mu, low) = prove_rounds(ps, per_instance, claim.mu.to_vec(), 1, F::ONE, &mut value);
    let mut at_instance = vec![F::ZERO; 64 << shape.slot_log()];
    let low_eq = F::eq_table(&low);
    crate::lv::parallel::chunks_mut(&mut at_instance, 64, |slot, out| {
        for (z, out) in out.iter_mut().enumerate() {
            let mut acc = F::Unreduced::ZERO;
            for (i, &e) in low_eq.iter().enumerate().take(16) {
                acc ^= e.mul_unreduced(folded[(i + 16 * slot) * 64 + z]);
            }
            *out = acc.reduce();
        }
    });
    for (slot, slices) in spare_slices(shape, committed, &[&low, pack].concat()).into_iter().enumerate() {
        at_instance[(shape.slots() + slot) * 64..][..64].copy_from_slice(&slices);
    }
    let (slices, _, slot) = prove_rounds(ps, at_instance, weights, 64, mu[0], &mut value);
    ps.add_ext(&slices);
    ([&low, pack, &slot].concat(), slices)
}

/// E2 values of an E2 front (`W = 2`).
pub fn to_f128<F: Ext<W>, const W: usize>(v: &[F]) -> Vec<F128> {
    v.iter().map(|&x| crate::lvm::front::to_e2(x)).collect()
}
