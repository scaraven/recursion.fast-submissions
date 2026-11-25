//! §6.4a end to end on the v6 transcript: the stub circuit's witness, the prover, refv's `VChain` with
//! `r3typed::verify`, the counts against FORMAT6, the stack claims against the stack and against the verifier's
//! weights, tampers, and `BODY` at 1/4/8 threads (`cargo test -p r3typed --features verify --release --
//! --test-threads=1`).

use std::time::Instant;

use fiat_shamir::ProverState;
use fs6::oracle::{Local, Oracle};
use fs6::params::P18;
use primitives::field::{F64, F128};
use primitives::transcript::Pool;
use r3core::claim::{RingMap, check_all};
use r3core::layout;
use r3typed::circuit::{Circuit, PHI_VARS, REC_BASE, Src};
use r3typed::prove::{Acc, Tamper, TypedOut, prove_typed_with};
use refv::typed::{TyCheck, TyReject, TyVOut, to_e, to_f, verify_typed};
use r3typed::witness::{TypedWitness, pub_lanes, witness};
use r3typed::stub;
use refv::chain::{TraceAsk, VChain};
use refv::{E, Part};

const KEY: [u8; 32] = [0x5a; 32];
/// The prefix: 4 `E` scalars (the sponge link's last `E(4)`), so `τ₀`'s query is 104 bytes.
const PREFIX: usize = 4;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn e(&mut self) -> F128 {
        F128::new(self.next(), self.next())
    }
}

fn vm_hwm_mb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).and_then(|l| l.split_whitespace().nth(1)?.parse::<u64>().ok()))
        .map_or(0, |kb| kb / 1024)
}

/// A leaf-mode stack: `STREAM` zero; `Y` (slot 36, `25·2^13` words), `X`'s words and the mini-bus columns random
/// (the other parts' data, which the witness must read or leave alone).
fn leaf_stack() -> Vec<F64> {
    let mut s = vec![F64::ZERO; 1 << layout::STACK_LOG];
    let mut g = Rng(11);
    for w in &mut s[layout::y_idx(0, 0)..layout::y_idx(0, 25)] {
        *w = F64(g.next());
    }
    for w in &mut s[layout::x_idx(0, 0)..layout::x_idx(0, 0) + layout::X_WORDS] {
        *w = F64(g.next());
    }
    for w in &mut s[layout::MB_LO..layout::MB_LO + 4096] {
        *w = F64(g.next());
    }
    s
}

struct Setup {
    circ: &'static Circuit,
    stack: Vec<F64>,
    z: Vec<F64>,
    hdr: Vec<u8>,
    acc: Acc,
    pubw: Vec<u64>,
}

fn setup() -> Setup {
    let circ = r3typed::circuit();
    let acc = Acc::leaf(circ);
    assert!(!acc.y.is_zero(), "the stub's Φ_Q(0) is nonzero");
    let hdr = fs6::schedule::header(&P18, 0, 1 << 18, &[3; 32], &[0; 32], &[9; 32], Some(&acc.to_hdr()));
    let pubw = pub_lanes(&hdr);
    let mut stack = leaf_stack();
    let before = stack.clone();
    let w = witness(circ, &mut stack, &pubw).expect("the stub is satisfiable in leaf mode");
    // T written, nothing else
    let t_lo = layout::idx(layout::SLOT_T, 0);
    let t_hi = layout::idx(layout::SLOT_T + layout::T_SLOTS, 0);
    let (xl, xh) = (layout::x_idx(0, 0), layout::x_idx(0, 0) + layout::X_WORDS);
    let changed: Vec<usize> = (0..stack.len()).filter(|&i| stack[i] != before[i]).collect();
    assert!(changed.len() > stub::ROWS / 2, "T is nonzero ({} words)", changed.len());
    assert!(changed.iter().all(|&i| i >= t_lo && i < t_hi && !(xl..xh).contains(&i)), "the witness writes only T, not X");
    let z = w.z;
    Setup { circ, stack, z, hdr, acc, pubw }
}

struct Run {
    body: Vec<u8>,
    trace: fs6::Trace,
    out: TypedOut,
    nonces: usize,
    secs: f64,
}

fn oracle() -> &'static dyn Oracle {
    Box::leak(Box::new(Local::keyed(&KEY)))
}

fn prefix() -> Vec<F128> {
    (0..PREFIX as u64).map(|i| F128::new(0x1111 * (i + 1), 0x2222 * (i + 1))).collect()
}

fn prove(s: &Setup, z: &[F64], tamper: &[Tamper]) -> Run {
    let t = fs6::Transcript::start(oracle(), &s.hdr);
    let mut ps = ProverState::<F128, Pool>::v6(t);
    ps.add_scalars(&prefix());
    let w = TypedWitness { circ: s.circ, z: z.to_vec(), pub_words: s.pubw.clone() };
    let t0 = Instant::now();
    let out = prove_typed_with(&mut ps, &w, &s.stack, &s.acc, tamper);
    let secs = t0.elapsed().as_secs_f64();
    let nonces = ps.chain().unwrap().nonces;
    let (body, trace) = ps.into_v6();
    Run { body, trace, out, nonces, secs }
}

struct Verified {
    out: TyVOut,
    stats: refv::chain::Stats,
}

fn verify(s: &Setup, r: &Run, acc_y: E) -> Result<Verified, TyReject> {
    let mut ask = TraceAsk::new(&r.trace, Some(&KEY));
    let mut ch = VChain::start(&mut ask, &s.hdr, &r.body)?;
    let pre = ch.read_e(PREFIX)?;
    assert_eq!(pre, prefix().into_iter().map(to_e).collect::<Vec<_>>());
    ch.phase(Part::Stub);
    let acc_pt: Vec<E> = s.acc.pt.iter().map(|&x| to_e(x)).collect();
    let out = verify_typed(&mut ch, s.circ, &s.pubw, &acc_pt, acc_y)?;
    let (stats, _) = ch.finish()?;
    ask.finish()?;
    Ok(Verified { out, stats: stats[&Part::Stub].clone() })
}

#[test]
fn stub_blob_roundtrip() {
    let c = stub::generate(stub::SEED);
    let text = c.to_blob();
    let d = Circuit::from_blob(&text);
    assert_eq!(c, d);
    assert_eq!(d.src_of(stub::COM_W + 5), Some((Src::Com, 5)));
    assert_eq!(d.src_of(stub::ONE_W), Some((Src::One, 0)));
    assert_eq!(d.src_of(40), None);
    // Φ_Q: the tables and the entry-by-entry form agree
    let mut g = Rng(5);
    let pt: Vec<F128> = (0..PHI_VARS).map(|_| g.e()).collect();
    assert_eq!(c.phi_q(&pt), c.phi_q_direct(&pt));
    eprintln!("stub: {} entries, {} defining rows, blob {} bytes", c.ents.len(), c.outs.len(), text.len());
}

#[test]
fn typed_end_to_end() {
    let s = setup();
    let r = prove(&s, &s.z, &[]);
    // FORMAT6 §6.4a counts: 84 draws, 84 nonces, 176 scalars, B_ty = 3,488
    assert_eq!(r.body.len(), 16 * PREFIX + 3488);
    assert_eq!(r.trace.len(), 2 + 84);
    assert_eq!(r.nonces, 84);
    assert_eq!(r.trace[2].0.len(), 104, "τ₀'s query absorbs the prefix's E(4)");
    // every chain query's length as fs6's schedule of §6.4a
    let (tally, pending) = fs6::schedule::tally_from(&P18, &fs6::schedule::typed_phases(&P18), 16 * PREFIX, false).unwrap();
    assert_eq!(pending, 0);
    let lens: Vec<usize> = r.trace[2..].iter().map(|(q, _)| q.len()).collect();
    assert_eq!(lens, tally.chain_lengths);
    assert_eq!((tally.body, tally.queries, tally.nonces), (3488, 84, 84));

    let v = verify(&s, &r, to_e(s.acc.y)).expect("V accepts");
    assert_eq!((v.stats.body, v.stats.queries, v.stats.nonces, v.stats.draws), (3488, 84, 84, 84));
    assert!(v.out.acc_ok(s.circ), "Φ_Q(accOut.pt) = accOut.y");
    assert_eq!(v.out.acc_pt.iter().map(|&e| to_f(e)).collect::<Vec<_>>(), r.out.acc_out.pt);
    assert_eq!(to_f(v.out.acc_y), r.out.acc_out.y);
    assert_eq!(s.circ.phi_q(&r.out.acc_out.pt), r.out.acc_out.y);
    assert_eq!(v.out.regions.iter().map(|&e| to_f(e)).collect::<Vec<_>>(), r.out.regions.to_vec());

    // claims 46–49: on the stack, and the verifier's weights and values = the prover's
    assert_eq!(r.out.claims.len(), 4);
    let bad = check_all(&r.out.claims, &s.stack);
    assert!(bad.is_empty(), "claims fail on the stack: {bad:?}");
    let vc = v.out.stack_claims();
    let maps = [RingMap { f: [F128::ZERO; 8], g: [F128::ZERO; 8] }; 2];
    let mut g = Rng(99);
    for trial in 0..3 {
        let mut z: Vec<F128> = (0..layout::STACK_LOG).map(|_| g.e()).collect();
        if trial == 2 {
            // a point on the claims' blocks' selectors: boolean high coordinates of each block
            for (k, zi) in z.iter_mut().enumerate().skip(19) {
                *zi = F128::new((layout::SLOT_STREAM >> (k - 19) & 1) as u64, 0);
            }
        }
        for (k, (pc, (w, val))) in r.out.claims.iter().zip(&vc).enumerate() {
            assert_eq!(pc.value, to_f(*val), "claim {}: value", 46 + k);
            let ez: Vec<E> = z.iter().map(|&x| to_e(x)).collect();
            assert_eq!(pc.weight_at(&z, &maps), to_f(w(&ez)), "claim {}: weight at a random point", 46 + k);
        }
    }
    // a nonzero T: the committed region's value is not trivially zero
    assert!(!r.out.regions[0].is_zero());
    eprintln!(
        "§6.4a: prove {:.3} s (stack 2^25 words, {} threads), BODY {} B, {} queries, {} nonces, VmHWM {} MiB",
        r.secs,
        parallel::num_threads(),
        r.body.len() - 16 * PREFIX,
        r.trace.len() - 2,
        r.nonces,
        vm_hwm_mb()
    );
}

fn reject(s: &Setup, z: &[F64], tamper: &[Tamper]) -> TyReject {
    let r = prove(s, z, tamper);
    match verify(s, &r, to_e(s.acc.y)) {
        Ok(_) => panic!("V accepted a tampered proof {tamper:?}"),
        Err(e) => e,
    }
}

#[test]
fn typed_tampers() {
    let s = setup();
    let d = F128::new(0x1234, 0x5678);
    let one = |index: usize| [Tamper { index, delta: d }];
    // scalar indices in BODY order: zerocheck rounds 0–39, A B C 40–42, wiring rounds 43–84, matrix values 85–88,
    // region values 89–92, relayout rounds 93–130, v_R 131, h 132–175
    let cases: Vec<(&str, Vec<Tamper>, TyCheck)> = vec![
        ("zerocheck round 0 c1", one(0).to_vec(), TyCheck::Zerocheck),
        ("zerocheck round 19 c2", one(39).to_vec(), TyCheck::Zerocheck),
        ("B at r_x", one(41).to_vec(), TyCheck::Zerocheck),
        ("wiring round 3 c0", one(49).to_vec(), TyCheck::Wiring),
        ("v_D", one(87).to_vec(), TyCheck::Wiring),
        ("v_com", one(89).to_vec(), TyCheck::Wiring),
        ("v_KS", one(92).to_vec(), TyCheck::Wiring),
        ("relayout round 0 c0", one(93).to_vec(), TyCheck::Relayout),
        ("v_R", one(131).to_vec(), TyCheck::Relayout),
        ("h_0", one(132).to_vec(), TyCheck::AccIn),
        ("h_7", one(139).to_vec(), TyCheck::AccOwn),
        ("h_5 and h_6 (h(0), h(1) kept)", vec![Tamper { index: 137, delta: d }, Tamper { index: 138, delta: d }], TyCheck::AccPhi),
    ];
    for (name, t, want) in cases {
        assert_eq!(reject(&s, &s.z, &t), TyReject::Check(want), "{name}");
    }
    // a wrong T word (the stack claims would catch the stack; here the words the prover works on)
    let mut z = s.z.clone();
    z[stub::com_word(17)] += F64::ONE;
    assert_eq!(reject(&s, &z, &[]), TyReject::Check(TyCheck::Zerocheck), "a T word");
    // a C_rec word under S_flat changes v_S's relayout target only if S̃(r) differs: the claim catches it
    let r = prove(&s, &s.z, &[]);
    let mut stack = s.stack.clone();
    stack[REC_BASE + 12345] = F64(77);
    assert_eq!(check_all(&r.out.claims[..1], &stack), vec![r.out.claims[0].label.clone()], "relayout point claim");
    stack = s.stack.clone();
    stack[s.circ.regs.iter().find(|g| g.src == Src::Com).unwrap().stack_idx(251 * 3)] += F64::ONE;
    assert_eq!(check_all(&r.out.claims[2..3], &stack).len(), 1, "committed region claim");
    // a wrong accIn.y (V given another header value)
    assert_eq!(
        verify(&s, &r, to_e(s.acc.y + F128::ONE)).err(),
        Some(TyReject::Check(TyCheck::AccIn)),
        "accIn.y"
    );
    // a BODY byte: the trace no longer matches (runSeq)
    let mut r2 = prove(&s, &s.z, &[]);
    r2.body[16 * PREFIX + 300] ^= 1;
    assert!(matches!(verify(&s, &r2, to_e(s.acc.y)), Err(TyReject::Chain(_))));
}

/// `BODY` and the trace at 1, 4 and 8 threads, each in its own process (the pool's size is fixed per process).
#[test]
fn typed_threads_deterministic() {
    let exe = std::env::current_exe().unwrap();
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("r3ty-det");
    std::fs::create_dir_all(&dir).unwrap();
    let mut outs = Vec::new();
    for n in [1usize, 4, 8] {
        let path = dir.join(format!("body-{n}"));
        let st = std::process::Command::new(&exe)
            .args(["--ignored", "--exact", "det_child", "--nocapture", "--test-threads=1"])
            .env("R3TY_DET_THREADS", n.to_string())
            .env("R3TY_DET_OUT", &path)
            .status()
            .unwrap();
        assert!(st.success(), "child at {n} threads");
        outs.push(std::fs::read(&path).unwrap());
    }
    assert!(outs[0].len() > 3488);
    assert_eq!(outs[0], outs[1], "1 vs 4 threads");
    assert_eq!(outs[0], outs[2], "1 vs 8 threads");
}

#[test]
#[ignore = "run by typed_threads_deterministic"]
fn det_child() {
    let n: usize = std::env::var("R3TY_DET_THREADS").unwrap().parse().unwrap();
    parallel::set_num_threads(n);
    let t0 = Instant::now();
    let s = setup();
    let wit = t0.elapsed().as_secs_f64();
    let r = prove(&s, &s.z, &[]);
    let mut blob = r.body.clone();
    for (q, a) in &r.trace {
        blob.extend_from_slice(q);
        blob.extend_from_slice(a);
    }
    for c in &r.out.claims {
        blob.extend_from_slice(&c.value.c0.to_le_bytes());
        blob.extend_from_slice(&c.value.c1.to_le_bytes());
    }
    std::fs::write(std::env::var("R3TY_DET_OUT").unwrap(), blob).unwrap();
    eprintln!("det_child: {n} threads: setup+witness {wit:.3} s, prove {:.3} s, VmHWM {} MiB", r.secs, vm_hwm_mb());
}
