//! `smoke`: leanVM's standalone Keccak GKR batch (keccak_gkr `batch_bench.rs` at fdb317982, without the bench
//! harness): witness, stacked commitment, output claim, GKR reduction, WHIR opening; then the native verifier
//! (`verifier::verify_keccak_batch`). The transcript is leanVM's own (unkeyed duplex sponge), not the v6 oracle:
//! this mode probes the engine through the asm pipeline, not the v6 protocol.

use std::time::Instant;

use keccak_gkr::{OutputClaim, Shape, Witness};
use pcs::stack_open::StackClaim;
use pcs::whir::{LOG_INV_RATE_0, ProverConfig, ProverData, commit, config_for_rate};
use primitives::field::{F64, F128};
use primitives::transcript::ProverState;
use verifier::INITIAL_FOLDING_FACTOR;

const LABEL: &[u8] = b"keccak-gkr-batch";

/// `splitmix64`: the inputs of a run, a function of `seed` alone.
pub struct SplitMix(pub u64);

impl SplitMix {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

pub struct Report {
    pub proof: Vec<u8>,
    pub stages: [f64; 6],
    pub verify_s: f64,
    pub verified: bool,
}

/// Prove `n` permutations of random inputs (from `seed`), a state committed every `depth` rounds, and verify.
pub fn run(n_log: usize, depth: usize, seed: u64) -> Report {
    let n = 1usize << n_log;
    let log_inv_rate = LOG_INV_RATE_0;
    let shape = Shape::new(n, depth);
    let mu = shape.stack_log();
    let mut rng = SplitMix(seed ^ n as u64);
    let inputs: Vec<[u64; 25]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let config = config_for_rate(mu, log_inv_rate).expect("WHIR configuration");

    let t_pass = Instant::now();
    let t = Instant::now();
    // SAFETY: the witness generator writes every word.
    let mut committed = unsafe { primitives::uninit_vec::<F64>(1 << mu) };
    let witness = Witness::generate(shape, &inputs, &mut committed);
    let witness_s = t.elapsed().as_secs_f64();

    let mut ps = batch_transcript(LABEL, shape, log_inv_rate);
    let t = Instant::now();
    let (prover_data, ood) = commit_stack(&mut ps, shape, &committed, log_inv_rate);
    let commit_s = t.elapsed().as_secs_f64();

    let t = Instant::now();
    let instance = batch_instance(&mut ps, shape);
    let output = OutputClaim::of_inputs(shape, &inputs, instance);
    ps.add_scalars(&output.lanes);
    let output_s = t.elapsed().as_secs_f64();

    let t = Instant::now();
    let openings = witness.prove(&mut ps, &committed, &output);
    drop(witness);
    let gkr_s = t.elapsed().as_secs_f64();

    let t = Instant::now();
    open_commitment(&mut ps, shape, committed, prover_data, &config, openings, ood);
    let open_s = t.elapsed().as_secs_f64();
    let proof = ps.into_proof();
    let pass_s = t_pass.elapsed().as_secs_f64();

    let iv = primitives::hash::hash(LABEL);
    let t = Instant::now();
    let verified = verifier::verify_keccak_batch(&iv, shape.n_log(), shape.depth(), log_inv_rate, &proof).is_ok();
    let verify_s = t.elapsed().as_secs_f64();
    Report {
        proof: proof.to_bytes(),
        stages: [witness_s, commit_s, output_s, gkr_s, open_s, pass_s],
        verify_s,
        verified,
    }
}

fn batch_transcript(label: &[u8], shape: Shape, log_inv_rate: usize) -> ProverState {
    let iv = verifier::Digest(primitives::hash::hash(label)).words();
    let statement = [shape.n_log(), shape.depth(), log_inv_rate, 0].map(|w| w as u64);
    ProverState::new(iv, statement)
}

fn commit_stack(ps: &mut ProverState, shape: Shape, stack: &[F64], log_inv_rate: usize) -> (ProverData, StackClaim) {
    let (commitment, prover_data) = commit(stack, shape.stack_log(), INITIAL_FOLDING_FACTOR, log_inv_rate);
    ps.add_commitment(&commitment.cap);
    let ood = pcs::ood::ood_sample(ps, stack, shape.stack_log());
    (prover_data, ood)
}

fn batch_instance(ps: &mut ProverState, shape: Shape) -> Vec<F128> {
    ps.grind(fiat_shamir::grinding_bits(shape.n_log() as u128));
    ps.sample_vec(shape.n_log())
}

fn open_commitment(
    ps: &mut ProverState,
    shape: Shape,
    stack: Vec<F64>,
    prover_data: ProverData,
    config: &ProverConfig,
    openings: keccak_gkr::Openings,
    ood: StackClaim,
) {
    let (ring, outputs) = openings.into_pcs_claims(0);
    let points: Vec<_> = outputs.into_iter().chain([ood]).collect();
    pcs::stack_open::open_batch_mixed_whir_stacked(ps, shape.stack_log(), stack, prover_data, config, &points, &ring);
}

/// What `smoke6` reports.
pub struct Report6 {
    pub body: Vec<u8>,
    pub trace: crate::oracle::Trace,
    pub stages: [f64; 6],
    pub frozen: bool,
}

/// `smoke6`: the same leanVM flow in v6 mode (`fs6::set_v6`): FORMAT6's hash chain over the installed oracle in
/// place of the duplex sponge (`ProverState::v6`), `pcs`'s Merkle trees through the oracle with caps, the WHIR
/// parameters frozen when the shape is `P18`'s (else leanVM's derivation, dev sizes only). leanVM's message order
/// is not FORMAT6's §6 (R2/R3 change the flows) and no verifier reads it yet (R1): this checks that leanVM's crates
/// run on the v6 seams, deterministically, and measures their oracle traffic.
pub fn run_v6(n_log: usize, depth: usize, seed: u64) -> Report6 {
    let n = 1usize << n_log;
    let log_inv_rate = LOG_INV_RATE_0;
    let shape = Shape::new(n, depth);
    let mu = shape.stack_log();
    let mut rng = SplitMix(seed ^ n as u64);
    let inputs: Vec<[u64; 25]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    fs6::set_v6(true);
    let (config, frozen) = match config_for_rate(mu, log_inv_rate) {
        Ok(c) => (c, true),
        Err(_) => {
            fs6::set_v6(false);
            let c = config_for_rate(mu, log_inv_rate).expect("WHIR configuration");
            fs6::set_v6(true);
            (c, false)
        }
    };

    let t_pass = Instant::now();
    let t = Instant::now();
    // SAFETY: the witness generator writes every word.
    let mut committed = unsafe { primitives::uninit_vec::<F64>(1 << mu) };
    let witness = Witness::generate(shape, &inputs, &mut committed);
    let witness_s = t.elapsed().as_secs_f64();

    let c = primitives::hash::hash(&[n_log as u8, depth as u8, log_inv_rate as u8]);
    // dev smoke (no HDR): the shape digest stands in for the header in the seed (v2.5: seed = a₀ ‖ HDR)
    let mut ps = ProverState::v6(fs6::Transcript::start(crate::oracle::get(), &c));
    let t = Instant::now();
    let (prover_data, ood) = commit_stack(&mut ps, shape, &committed, log_inv_rate);
    let commit_s = t.elapsed().as_secs_f64();

    let t = Instant::now();
    let instance = batch_instance(&mut ps, shape);
    let output = OutputClaim::of_inputs(shape, &inputs, instance);
    ps.add_scalars(&output.lanes);
    let output_s = t.elapsed().as_secs_f64();

    let t = Instant::now();
    let openings = witness.prove(&mut ps, &committed, &output);
    drop(witness);
    let gkr_s = t.elapsed().as_secs_f64();

    let t = Instant::now();
    open_commitment(&mut ps, shape, committed, prover_data, &config, openings, ood);
    let open_s = t.elapsed().as_secs_f64();
    let (body, trace) = ps.into_v6();
    let pass_s = t_pass.elapsed().as_secs_f64();
    Report6 { body, trace, stages: [witness_s, commit_s, output_s, gkr_s, open_s, pass_s], frozen }
}
