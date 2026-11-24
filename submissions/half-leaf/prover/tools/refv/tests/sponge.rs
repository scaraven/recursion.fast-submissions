//! §6.3 end to end on a v6 transcript: prover, refv's `VChain` with [`refv::sponge::verify`], FORMAT6's counts, the
//! 31 stack claims natively and at a point against the verifier's weights, tampers, thread-count determinism.
//! Run: `cargo test -p refv --release --test sponge` (moved from `r3sponge` by R1).

use std::time::Instant;

use primitives::field::{F64, F128};
use primitives::transcript::ProverState;
use r3core::claim::{RingMap, check_all};
use r3core::layout::{SPLIT, STACK_LOG, m_idx};
use refv::chain::{Ask, RecordAsk, TraceAsk, VChain};
use refv::stack::Maps;
use refv::{E, Res};

use r3sponge::prove::{Tamper, prove_sponge_with, SpongeOut};
use refv::sponge::{SpongeCheck, SpongeV, sponge_check, verify};
use r3sponge::witness::{SpongeWitness, cont_rows, write_messages};

const KEY: [u8; 32] = [0x5a; 32];

fn rng(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed | 1;
    move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    }
}

/// The keyed local oracle (one leaked per call: a few hundred bytes a proof, tests only).
fn oracle() -> &'static fs6::oracle::Local {
    Box::leak(Box::new(fs6::oracle::Local::keyed(&KEY)))
}

fn header() -> Vec<u8> {
    fs6::schedule::header(&fs6::params::SHAPE, 0, 1 << fs6::params::SHAPE.log_blocks, &[3; 32], &[0; 32], &[9; 32], None)
}

/// The stack with `SP`, `Y` (and, with `msgs`, random `M` and `X`) and the witness.
fn setup(msgs: bool) -> (Vec<F64>, SpongeWitness) {
    let mut stack = vec![F64(0); 1 << STACK_LOG];
    if msgs {
        let mut next = rng(0x1234);
        let m: Vec<u64> = (0..SPLIT * 17).map(|_| next()).collect();
        let x: Vec<u64> = (0..17 << 10).map(|_| next()).collect();
        write_messages(&mut stack, |r, l| m[17 * r + l], |i, l| x[17 * i + l]);
    }
    let w = SpongeWitness::generate(&mut stack, &cont_rows());
    (stack, w)
}

struct Proof {
    body: Vec<u8>,
    trace: fs6::Trace,
    out: SpongeOut,
    secs: f64,
}

/// `HDR`; a prefix of 64 `E` scalars (as the tree batch's `E(64)`); §6.3; a trailing `G(1)` (§6.4a's `τ₀`).
fn prove(stack: &[F64], w: &SpongeWitness, tamper: Tamper) -> Proof {
    let t = fs6::Transcript::start(oracle(), &header());
    let mut ps = ProverState::v6(t);
    let mut next = rng(99);
    let prefix: Vec<F128> = (0..64).map(|_| F128::new(next(), next())).collect();
    ps.add_scalars(&prefix);
    let t0 = Instant::now();
    let out = prove_sponge_with(&mut ps, w, stack, tamper);
    let secs = t0.elapsed().as_secs_f64();
    ps.grind(1);
    let _ = ps.sample();
    let (body, trace) = ps.into_v6();
    Proof { body, trace, out, secs }
}

/// The verifier on `BODY`, its queries answered by `ask`: prefix, §6.3, the trailing group, end of `BODY`.
fn verify_body(ask: &mut dyn Ask, body: &[u8]) -> Res<SpongeV> {
    let mut ch = VChain::start(ask, &header(), body)?;
    ch.read_e(64)?;
    let sv = verify(&mut ch, &cont_rows())?;
    ch.ground(1)?;
    ch.finish()?;
    Ok(sv)
}

fn accept(p: &Proof) -> SpongeV {
    let mut ask = TraceAsk::new(&p.trace, Some(&KEY));
    let sv = verify_body(&mut ask, &p.body).expect("the honest proof is accepted");
    ask.finish().expect("every trace entry used");
    sv
}

fn to_e(x: F128) -> E {
    let [a, b] = x.to_limbs();
    E::new(a, b)
}

fn to_f(x: E) -> F128 {
    F128::new(x.c0, x.c1)
}

/// (b) counts and query lengths, (c) native claims, (d) weights at a point.
fn check_honest(stack: &[F64], p: &Proof, sv: &SpongeV) {
    // (b) FORMAT6 §6.3, CB §T.
    let [c, k, l] = &sv.counts;
    assert_eq!((c.body, c.queries, c.nonces, c.draws), (504, 13, 13, 13), "caller");
    assert_eq!((k.body, k.queries, k.nonces), (23_688, 298, 293), "core");
    assert_eq!((l.body, l.queries, l.nonces, l.draws), (728, 31, 31, 31), "link");
    assert_eq!(c.lengths, [vec![1064], vec![40; 12]].concat());
    assert_eq!(k.lengths[0], 440);
    assert_eq!(l.lengths, [vec![1064], vec![40; 17], vec![72; 13]].concat());
    assert_eq!(p.trace.last().unwrap().0.len(), 104, "the first typed query absorbs L3's E(4)");
    assert_eq!(p.body.len(), 64 * 16 + 504 + 23_688 + 728 + 8);
    assert_eq!(p.trace.len(), 2 + 13 + 298 + 31 + 1);
    // The prover's view equals the verifier's.
    assert_eq!(p.out.r.iter().map(|&x| to_e(x)).collect::<Vec<_>>(), sv.r);
    assert_eq!(p.out.rho_p.iter().map(|&x| to_e(x)).collect::<Vec<_>>(), sv.rho_p);
    assert_eq!(p.out.inputs.point.iter().map(|&x| to_e(x)).collect::<Vec<_>>(), sv.slice_point);
    assert_eq!(p.out.outputs.point.iter().map(|&x| to_e(x)).collect::<Vec<_>>(), sv.c_out_point);
    // (c) every claim natively.
    assert_eq!(p.out.claims.len(), 31);
    let t = Instant::now();
    let fails = check_all(&p.out.claims, stack);
    assert!(fails.is_empty(), "claims failing natively: {fails:?}");
    eprintln!("native check of 31 claims: {:.3} s", t.elapsed().as_secs_f64());
    // (d) the verifier's weights and values at a random point, random maps.
    let mut next = rng(0xabc);
    let mut e = || E::new(next(), next());
    let draws: Vec<E> = (0..33).map(|_| e()).collect();
    let maps = Maps {
        tree_f: draws[0..8].to_vec(),
        tree_g: draws[8..16].to_vec(),
        sponge_f: draws[16..24].to_vec(),
        sponge_g: draws[24..32].to_vec(),
        lambda0: draws[32],
    };
    let fmaps = [
        RingMap::from_draws(&draws[0..16].iter().map(|&x| to_f(x)).collect::<Vec<_>>()),
        RingMap::from_draws(&draws[16..32].iter().map(|&x| to_f(x)).collect::<Vec<_>>()),
    ];
    let z: Vec<E> = (0..25).map(|_| e()).collect();
    let zf: Vec<F128> = z.iter().map(|&x| to_f(x)).collect();
    for (pc, d) in p.out.claims.iter().zip(sv.deferred()) {
        let (wf, val): (Box<dyn Fn(&[E]) -> E>, E) = d(&maps);
        assert_eq!(val, to_e(pc.batch_value(&fmaps)), "value of {}", pc.label);
        assert_eq!(wf(&z), to_e(pc.weight_at(&zf, &fmaps)), "weight of {}", pc.label);
        // And the weight vanishes off the claim's block (a point whose selector bits differ).
        let (off, mu) = pc.weight.block();
        let mut zo: Vec<E> = z.clone();
        for (k, zk) in zo.iter_mut().enumerate().skip(mu) {
            *zk = E::new(((off >> (k - mu)) & 1) as u64 ^ u64::from(k == mu), 0);
        }
        assert_eq!(wf(&zo), E::new(0, 0), "selector of {}", pc.label);
    }
}

fn honest(msgs: bool) {
    let t = Instant::now();
    let (stack, w) = setup(msgs);
    let gen_s = t.elapsed().as_secs_f64();
    let p = prove(&stack, &w, Tamper::None);
    let t = Instant::now();
    let sv = accept(&p);
    let ver_s = t.elapsed().as_secs_f64();
    check_honest(&stack, &p, &sv);
    eprintln!(
        "msgs={msgs}: witness {gen_s:.3} s, prove_sponge {:.3} s, verify {ver_s:.3} s, BODY {} B, {} queries, hash {}",
        p.secs,
        p.body.len(),
        p.trace.len(),
        hex8(&p.body)
    );
}

fn hex8(b: &[u8]) -> String {
    primitives::hash::hash(b)[..8].iter().map(|x| format!("{x:02x}")).collect()
}

/// (a)–(d) at leaf mode (`M = 0`, `X = 0`).
#[test]
fn leaf_mode_accepts() {
    honest(false);
}

/// (a)–(d) with random `M` and `X` (the link's message terms nonzero).
#[test]
fn messages_accept() {
    honest(true);
}

/// (e) prover-side tampers, a witness off the link relation, and byte flips of `BODY`.
#[test]
fn tampers_reject() {
    let (mut stack, w) = setup(true);
    let reject = |stack: &[F64], tamper: Tamper| -> SpongeCheck {
        let p = prove(stack, &w, tamper);
        let mut ask = TraceAsk::new(&p.trace, Some(&KEY));
        let e = verify_body(&mut ask, &p.body).expect_err("a tamper is rejected");
        sponge_check(&e).unwrap_or_else(|| panic!("{tamper:?}: rejected outside §6.3's checks: {e:?}"))
    };
    let c = reject(&stack, Tamper::V7);
    assert!(matches!(c, SpongeCheck::Product(_) | SpongeCheck::Layer(_) | SpongeCheck::Input), "V7: {c:?}");
    eprintln!("V7 → {c:?}");
    for k in [0, 5, 12] {
        assert_eq!(reject(&stack, Tamper::LinkRound(k)), SpongeCheck::Link, "round {k}");
    }
    for j in 0..4 {
        assert_eq!(reject(&stack, Tamper::Vals(j)), SpongeCheck::Link, "vals {j}");
    }
    // A STREAM word that row 100 did not absorb: SP and Y are Keccak-consistent, the link relation is broken.
    stack[m_idx(100, 3)].0 ^= 1 << 17;
    assert_eq!(reject(&stack, Tamper::None), SpongeCheck::Link, "broken link");
    stack[m_idx(100, 3)].0 ^= 1 << 17;
    // Byte flips of BODY (the trace re-derived through the oracle): v, c_st, a layer message, a slice, a shift
    // round, the last value. The trailing group's nonce is not flipped (it is outside §6.3).
    let p = prove(&stack, &w, Tamper::None);
    let v0 = 64 * 16 + 13 * 8;
    let core0 = v0 + 25 * 16;
    let link0 = core0 + 23_688;
    let end = p.body.len() - 8;
    for off in [v0 + 3, core0 + 8 + 5, core0 + 8 + 16 + 100, link0 - 64 * 16 + 37, link0 + 18 * 8 + 1, end - 1] {
        let mut body = p.body.clone();
        body[off] ^= 0x10;
        let mut ask = RecordAsk { o: oracle(), tr: Vec::new() };
        let r = verify_body(&mut ask, &body);
        assert!(r.is_err(), "flip at {off} accepted");
        eprintln!("flip at {off}: {:?}", r.err().map(|e| sponge_check(&e).map_or(format!("{e:?}"), |c| format!("{c:?}"))));
    }
}

/// The child of [`body_identical_across_threads`]: the pool at `R3SP_THREADS` workers, both witnesses.
#[test]
#[ignore]
fn body_hash_child() {
    let n: usize = std::env::var("R3SP_THREADS").expect("run by the parent").parse().unwrap();
    parallel::set_num_threads(n);
    let mut line = String::new();
    for msgs in [false, true] {
        let (stack, w) = setup(msgs);
        let p = prove(&stack, &w, Tamper::None);
        line += &format!(" {} {:.3}", hex8(&p.body), p.secs);
    }
    println!("BODYHASH{line}");
}

/// (f) `BODY` byte-identical at 1, 4 and 8 threads (one process each: the pool's size is fixed at its start).
#[test]
fn body_identical_across_threads() {
    let exe = std::env::current_exe().unwrap();
    let mut hashes = Vec::new();
    for n in [1, 4, 8] {
        let out = std::process::Command::new(&exe)
            .args(["--exact", "body_hash_child", "--ignored", "--nocapture", "--test-threads=1"])
            .env("R3SP_THREADS", n.to_string())
            .output()
            .unwrap();
        let s = String::from_utf8_lossy(&out.stdout);
        let line = s.lines().find_map(|l| l.split_once("BODYHASH ").map(|(_, r)| r)).unwrap_or_else(|| panic!("child at {n}: {s}"));
        let f: Vec<&str> = line.split_whitespace().collect();
        eprintln!("threads {n}: leaf {} ({} s), msgs {} ({} s)", f[0], f[1], f[2], f[3]);
        hashes.push((f[0].to_string(), f[2].to_string()));
    }
    assert!(hashes.windows(2).all(|w| w[0] == w[1]), "BODY differs across thread counts: {hashes:?}");
}
