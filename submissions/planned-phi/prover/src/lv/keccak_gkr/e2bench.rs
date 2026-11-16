// lvm2 E2-K (ARCH-7 §2.4–§2.5): E3 against E2 on the Keccak GKR's layer passes. Mounted by both GKR trees.
//! Three tools, each run on whichever tier the binary is (v2, v4p, or v4 natively or under SDE):
//!
//! - [`check`]: the generic fast layer prover against the plain [`reference`](super::reference) one, at E3 and at
//!   E2, layer after layer: equal transcripts and equal claims, or an error naming the first difference;
//! - [`bench`]: wall time of the tape GKR (`prove_tape_in`, depth 24, P20's chain shape) or of the KS layers
//!   (2^15 rows, depth 12, two segments), E3 and E2 interleaved, per pass (the layer prover's spans) and in total;
//! - [`probe`]: `prover setup`'s two-second form of `bench` at 2^14, one line for `lvm-selftest.txt`.
//!
//! The E2 transcript is G0's stand-in (`Ext::to_scalar`: an E scalar with lane 2 zero), so E2's proof is not the
//! roll-7 protocol's yet; its cost is the layer passes', which is what gate G1 needs.

use std::time::Instant;

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::{Ext, F64, F128, F192};

use crate::lv::keccak_gkr::keccak::{LANE_VARS, LANES};
use crate::lv::keccak_gkr::protocol::{Claim, first_claim};
use crate::lv::keccak_gkr::prover::{Scratch, prove_layer};
use crate::lv::keccak_gkr::reference;
use crate::lv::keccak_gkr::witness::{Shape, Witness};
use crate::lv::keccak_gkr::OutputClaim;

fn inputs(n: usize, seed: u64) -> Vec<[u64; LANES]> {
    let mut x = seed | 1;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    (0..n).map(|_| std::array::from_fn(|_| next())).collect()
}

fn witness(n: usize, depth: usize, seed: u64) -> Witness {
    let shape = Shape::new(n, depth);
    let inputs = inputs(n, seed);
    if shape.segments() == 1 {
        Witness::generate_uncommitted(shape, &inputs)
    } else {
        let mut committed = vec![F64::ZERO; 1 << shape.stack_log()];
        Witness::generate(shape, &inputs, &mut committed)
    }
}

/// A first claim from the transcript: `y_vars` point, four instance and five lane challenges.
fn start<F: Ext<W>, const W: usize>(ps: &mut ProverState, shape: Shape) -> Claim<F> {
    let mut draw = |n: usize| -> Vec<F> { (0..n).map(|_| ps.challenge::<F, W>(Grp::C1)).collect() };
    let (point, low, lane) = (draw(shape.y_vars()), draw(4), draw(LANE_VARS));
    first_claim::<F, W>(shape, &low, point, &lane)
}

fn check_field<F: Ext<W>, const W: usize>(w: &Witness, layers: usize, tag: &str) -> Result<(), String> {
    let shape = w.shape;
    let header = *b"e2check-0123456789abcdef";
    let (mut a, mut b) = (ProverState::seeded(&header), ProverState::seeded(&header));
    let (mut ca, mut cb): (Claim<F>, Claim<F>) = (start(&mut a, shape), start(&mut b, shape));
    let mut scratch = Scratch::<W>::new(shape);
    for step in 0..layers.min(shape.depth()) {
        ca = prove_layer(&mut a, w, &mut scratch, step, &ca);
        cb = reference::prove_layer(&mut b, w, step, &cb);
        if a.state() != b.state() || ca != cb {
            return Err(format!("{tag} {}: layer {step} differs (transcript {}, claim {})", F::NAME, a.state() == b.state(), ca == cb));
        }
    }
    Ok(())
}

/// `e2check`: the fast passes against the reference on a few shapes (padding block, one and two segments).
pub fn check(layers: usize) -> Result<String, String> {
    crate::lv::primitives::field::gf2_64x2::self_check();
    // Padding with one, two and three segments (depth 24, 12, 8; three segments leave a fourth, empty one), no
    // padding, one block (n <= 512), and the paired tail of the v4 tree (4096).
    let cases = [
        (1100usize, 24usize, 3u64),
        (2048, 12, 5),
        (700, 12, 7),
        (4096, 24, 9),
        (1100, 12, 11),
        (3000, 8, 13),
        (300, 24, 15),
    ];
    let mut done = Vec::new();
    for (n, depth, seed) in cases {
        let w = witness(n, depth, seed);
        let tag = format!("n {n} depth {depth}");
        check_field::<F192, 3>(&w, layers, &tag)?;
        check_field::<F128, 2>(&w, layers, &tag)?;
        done.push(tag);
    }
    Ok(format!("e2check ok: E3 and E2 fast = reference, {} layers, on [{}]", layers, done.join("; ")))
}

/// Span seconds by name, for the deltas of one run.
fn spans() -> Vec<(&'static str, f64)> {
    crate::lv::tracing::snapshot().into_iter().map(|(n, s, _)| (n, s)).collect()
}

fn delta(before: &[(&'static str, f64)], after: &[(&'static str, f64)], name: &str) -> f64 {
    let get = |v: &[(&'static str, f64)]| v.iter().find(|e| e.0 == name).map_or(0.0, |e| e.1);
    get(after) - get(before)
}

/// The passes, as the layer prover's spans name them (E2's carry a `/E2` suffix).
const PASSES: [&str; 5] = ["Product", "Skip", "Groups", "Tables", "Tail"];

fn pass_name(pass: &str, e2: bool) -> String {
    if e2 { format!("{pass}/E2") } else { pass.to_string() }
}

/// One timed run: total seconds and per-pass seconds.
fn timed<F: Ext<W>, const W: usize>(w: &Witness, tape: bool, seed: u64) -> (f64, [f64; 5]) {
    let shape = w.shape;
    let mut ps = ProverState::seeded(b"e2bench-0123456789abcdef");
    let before = spans();
    let t = Instant::now();
    if tape {
        let instance: Vec<F> = (0..shape.n_log()).map(|_| ps.challenge::<F, W>(Grp::C1)).collect();
        let lanes: [F; LANES] = std::array::from_fn(|i| F::from(F64(seed.wrapping_mul(i as u64 + 1))));
        let out = OutputClaim { instance, lanes };
        let _ = w.prove_tape_in(&mut ps, &out);
    } else {
        let mut claim: Claim<F> = start(&mut ps, shape);
        let mut scratch = Scratch::<W>::new(shape);
        for step in 0..shape.depth() {
            claim = prove_layer(&mut ps, w, &mut scratch, step, &claim);
        }
    }
    let total = t.elapsed().as_secs_f64();
    let after = spans();
    (total, PASSES.map(|p| delta(&before, &after, &pass_name(p, W == 2))))
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.total_cmp(b));
    if v.is_empty() { 0.0 } else { v[v.len() / 2] }
}

/// `e2bench tape|ks LOG_N REPS`: E3 and E2 interleaved after one warm-up each; per rep the totals, then the
/// medians per pass, the ratios E3/E2 and the per-layer seconds. `LVM_PROF=1` for the per-pass columns.
pub fn bench(mode: &str, log_n: usize, reps: usize) -> String {
    let tape = mode == "tape";
    let t = Instant::now();
    let w = if tape {
        let p = crate::lvm::params::Params::by_name("P20").unwrap();
        let chain = crate::lvm::tables::Chain::run_gated(p.log_n, &[7u8; 32], 1 << log_n, false);
        Witness::generate_uncommitted(chain.shape, &chain.inputs)
    } else {
        witness(1 << log_n, 12, 11)
    };
    let mut out = format!(
        "e2bench {mode} n=2^{log_n} depth {} segments {} threads {} variant {} (witness {:.3} s)\n",
        w.shape.depth(),
        w.shape.segments(),
        crate::lv::parallel::num_threads(),
        crate::VARIANT,
        t.elapsed().as_secs_f64()
    );
    let _ = timed::<F192, 3>(&w, tape, 1);
    let _ = timed::<F128, 2>(&w, tape, 1);
    let (mut e3, mut e2) = (Vec::new(), Vec::new());
    for r in 0..reps {
        let a = timed::<F192, 3>(&w, tape, r as u64 + 2);
        let b = timed::<F128, 2>(&w, tape, r as u64 + 2);
        out += &format!("rep {r}: E3 {:.4} s {:?} | E2 {:.4} s {:?}\n", a.0, a.1.map(|x| (x * 1e4).round() / 1e4), b.0, b.1.map(|x| (x * 1e4).round() / 1e4));
        e3.push(a);
        e2.push(b);
    }
    let layers = w.shape.depth() as f64;
    let col = |v: &[(f64, [f64; 5])], i: Option<usize>| median(v.iter().map(|x| i.map_or(x.0, |i| x.1[i])).collect());
    for (i, pass) in PASSES.iter().enumerate() {
        let (a, b) = (col(&e3, Some(i)), col(&e2, Some(i)));
        if a > 0.0 {
            out += &format!("{pass:<8} E3 {:.4} s  E2 {:.4} s  ratio E2/E3 {:.3}  speed-up {:.3}x\n", a, b, b / a, a / b);
        }
    }
    let (a, b) = (col(&e3, None), col(&e2, None));
    out += &format!(
        "total    E3 {a:.4} s  E2 {b:.4} s  ratio E2/E3 {:.3}  speed-up {:.3}x  per layer E3 {:.4} E2 {:.4} s\n",
        b / a,
        a / b,
        a / layers,
        b / layers
    );
    out
}

/// `e2probe` (a child of `prover setup`, on the chosen tier): the tape GKR at 2^14, E3 and E2, best of three
/// after a warm-up, as one line.
pub fn probe() -> String {
    let t = Instant::now();
    let p = crate::lvm::params::Params::by_name("P20").unwrap();
    let chain = crate::lvm::tables::Chain::run_gated(p.log_n, &[7u8; 32], 1 << 14, false);
    let w = Witness::generate_uncommitted(chain.shape, &chain.inputs);
    let _ = timed::<F192, 3>(&w, true, 1);
    let _ = timed::<F128, 2>(&w, true, 1);
    let (mut a, mut b) = ((f64::MAX, [0.0; 5]), (f64::MAX, [0.0; 5]));
    for r in 0..3 {
        let x = timed::<F192, 3>(&w, true, r + 2);
        let y = timed::<F128, 2>(&w, true, r + 2);
        if x.0 < a.0 {
            a = x;
        }
        if y.0 < b.0 {
            b = y;
        }
    }
    let ms = |v: [f64; 5]| v.map(|x| format!("{:.1}", x * 1e3)).join("/");
    format!(
        "e2probe {} threads {} tape 2^14: E3 {:.1} ms E2 {:.1} ms speed-up {:.3}x; Product/Skip/Groups(v4 only)/Tables/Tail ms E3 {} E2 {} ({:.1} s)",
        crate::VARIANT,
        crate::lv::parallel::num_threads(),
        a.0 * 1e3,
        b.0 * 1e3,
        a.0 / b.0,
        ms(a.1),
        ms(b.1),
        t.elapsed().as_secs_f64()
    )
}
