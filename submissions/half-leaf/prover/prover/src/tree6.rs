//! `tree6` (WP R2, dev): the tree batch of FORMAT6 §6.2 on the v6 transcript, as a prefix of a leaf-mode proof:
//! `HDR ‖ §6.1 ‖ §6.2 ‖ §6.5's B and group (G(17), D(32))` (FORMAT6 v2.2), signed with the toy signer over the keyed local oracle. The
//! stack is written next to it so that `refv-tree` can check the stack claims natively (in place of the PCS).
//!
//! `lvm6-prover tree6 LOG_BLOCKS OUT [SEED] [TAMPER]`; `TAMPER` one of `none` (default), the message tampers of
//! `keccak_gkr::tree::Tamper` (`delta d0 o7 cst cout s5`), or the witness tampers `forge` (parent row 5 commits a
//! wrong word in slot 1 and is hashed from it, as everything above it: TOY2's A1), `mid` (one committed middle word
//! off), `root` (the header claims another root).

use std::time::Instant;

use keccak_gkr::tree::{self, Tamper, Tree};
use pcs::whir::commit;
use primitives::field::F64;
use primitives::multilinear::mle_eval_par;
use primitives::transcript::ProverState;
use verifier::INITIAL_FOLDING_FACTOR;

use crate::format::{Signed, to_file, toy_sign, trace_digest};
use crate::keccak::{data_root, keccak256, leaf_stmt};
use crate::smoke::SplitMix;
use crate::stream::hex;

/// The dev oracle key and toy signer seed.
pub const KEY: [u8; 32] = [0x5A; 32];
pub const SIGN_SEED: u8 = 7;
/// Rate ¼.
pub const LOG_INV_RATE: usize = 2;

fn peak_rss_mib() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|v| v.parse::<f64>().ok())
        .map_or(0.0, |kb| kb / 1024.0)
}

pub fn run(args: &[String]) -> i32 {
    let log_blocks: usize = args.get(2).map_or(14, |v| v.parse().expect("LOG_BLOCKS"));
    let out = std::path::PathBuf::from(args.get(3).expect("OUT dir"));
    let seed: u64 = args.get(4).map_or(1, |v| v.parse().expect("SEED"));
    let tamper_name = args.get(5).map_or("none", String::as_str);
    let tamper = match tamper_name {
        "delta" => Tamper::Delta,
        "d0" => Tamper::D0,
        "o7" => Tamper::O7,
        "cst" => Tamper::Cst,
        "cout" => Tamper::Cout,
        "s5" => Tamper::Slice5,
        _ => Tamper::None,
    };
    std::fs::create_dir_all(&out).expect("OUT dir");
    parallel::init();
    crate::oracle::install(Box::new(crate::oracle::Local::keyed(&KEY)));
    fs6::set_v6(true);
    let sh = fs6::params::SHAPE;
    let n_blocks = 1usize << log_blocks;
    let t_all = Instant::now();

    // The blocks, the tree, the witness and the stack.
    let t = Instant::now();
    let mut rng = SplitMix(seed ^ n_blocks as u64);
    let blocks: Vec<[u64; 4]> = (0..n_blocks).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    let data: Vec<u8> = blocks.iter().flat_map(|b| b.iter().flat_map(|w| w.to_le_bytes())).collect();
    let mut tr = Tree::new(blocks);
    assert_eq!(tr.root(), data_root(&data), "D(1) is the contract's dataRoot");
    if tamper_name == "forge" {
        tr.forge(5, 1, 1 << 9);
    }
    let (witness, mut stack) = tr.witness();
    let n = tr.rows();
    let stack_log = n.ilog2() as usize + 6;
    if tamper_name == "mid" {
        stack[(tree::MID + 3) * n + 777].0 ^= 1;
    }
    let mut h = tr.root();
    if tamper_name == "root" {
        h[0] ^= 1;
    }
    let witness_s = t.elapsed().as_secs_f64();

    // HDR, statement, seed.
    let (vk, _) = toy_sign(SIGN_SEED, &[0; 32]);
    let hdr = fs6::schedule::header(&sh, 0, n_blocks as u64, &h, &[0; 32], &vk, None);
    let c = leaf_stmt(&h, n_blocks as u64);
    let mut ps = ProverState::v6(fs6::Transcript::start(crate::oracle::get(), &hdr));

    // §6.1: CAP(0) · G(18), D(M−1) → z₀ · E(1) → y₀ (the 46 occupied lanes committed).
    let t = Instant::now();
    let (commitment, _prover_data) = commit(&stack[..sh.lanes * n], stack_log, INITIAL_FOLDING_FACTOR, LOG_INV_RATE);
    ps.add_commitment(&commitment.cap);
    ps.chain().unwrap().bind();
    ps.grind(sh.levels[0].grind_ood);
    let z0 = ps.sample_vec(stack_log);
    let y0 = mle_eval_par(&stack, &z0);
    ps.add_scalar(y0);
    let commit_s = t.elapsed().as_secs_f64();

    // §6.2.
    let t = Instant::now();
    let body_before = ps.chain().unwrap().body_len();
    let trace_before = ps.chain().unwrap().trace_len();
    let openings = tree::prove_tree_with(&mut ps, &tr, &witness, &stack, tamper);
    let tree_body = ps.chain().unwrap().body_len() - body_before;
    let tree_queries = ps.chain().unwrap().trace_len() - trace_before;
    let tree_s = t.elapsed().as_secs_f64();
    drop(witness);

    // §6.5: B, then the group G(17), D(32) (the two maps and λ₀); the dev proof ends here.
    ps.chain().unwrap().bind();
    ps.grind(sh.grind_batch);
    let _maps = ps.sample_vec(33);
    let (body, trace) = ps.into_v6();
    let pi = [hdr, body].concat();
    let (vk2, sig) = toy_sign(SIGN_SEED, &trace_digest(&trace));
    assert_eq!(vk, vk2);
    let file = to_file(&Signed { pi: pi.clone(), tr: trace.clone(), sig });
    let total_s = t_all.elapsed().as_secs_f64();

    std::fs::write(out.join("tree6.signed"), &file).expect("write proof");
    let words: Vec<u8> = stack.iter().flat_map(|w| w.0.to_le_bytes()).collect();
    std::fs::write(out.join("stack.bin"), &words).expect("write stack");
    let meta = format!(
        "log_blocks {log_blocks}\nseed {seed}\ntamper {tamper_name}\nkey {}\nvk {}\nc {}\nh {}\n",
        hex(&KEY),
        hex(&vk),
        hex(&c),
        hex(&h)
    );
    std::fs::write(out.join("meta.txt"), &meta).expect("write meta");
    let _ = openings;
    let _: &[F64] = &stack;
    println!(
        "tree6 tier {} threads {} 2^{log_blocks} blocks tamper {tamper_name}: |pi| {} |tree| {} B tree queries {} trace {} \
         file keccak {} | witness {witness_s:.3} commit {commit_s:.3} tree {tree_s:.3} total {total_s:.3} s | peak {:.0} MiB",
        crate::VARIANT,
        parallel::num_threads(),
        pi.len(),
        tree_body,
        tree_queries,
        trace.len(),
        hex(&keccak256(&file)),
        peak_rss_mib()
    );
    0
}
