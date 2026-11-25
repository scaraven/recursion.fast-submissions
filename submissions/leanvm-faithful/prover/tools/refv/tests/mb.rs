//! §6.4b round trip on the v6 transcript: the prover (`r3mb::prove_minibus`, vendored leanVM GKR) against the
//! verifier (`refv::minibus`, refv's `VChain`, the Lean's arithmetic), on the stub tables.
//!
//! The transcript: `fs6::Transcript::start` with a `P18` header (v2.5 seed `a₀ ‖ HDR`), a prefix absorbing one `E` scalar and a `G(6)`
//! draw (as after TY's `t`, so the fingerprint's ground query is 40 bytes), §6.4b, finish.

use std::sync::OnceLock;
use std::time::Instant;

use fs6::oracle::Local;
use fs6::params::P18;
use fs6::schedule::Item;
use primitives::field::{F64, F128};
use primitives::transcript::ProverState;
use r3core::claim::RingMap;
use r3core::layout::STACK_LOG;
use refv::minibus::{MbReject, VClaim};
use r3mb::{MbOut, MbWitness, prove_minibus, stub};
use refv::chain::{Ask, RecordAsk, Stats, TraceAsk, VChain};
use refv::{E, Part, Reject};

const KEY: [u8; 32] = [0x5a; 32];
const SEED: u64 = 0x6d62_6c76_6d36;

fn oracle() -> &'static Local {
    static O: OnceLock<Local> = OnceLock::new();
    O.get_or_init(|| Local::keyed(&KEY))
}

/// A `P18` header (FORMAT6 v2.5: the seed is `a₀ ‖ HDR`).
fn hdr() -> Vec<u8> {
    fs6::schedule::header(&P18, 0, 1 << P18.log_blocks, &[3; 32], &[0; 32], &[4; 32], None)
}

const PREFIX_SCALAR: F128 = F128::new(0x1234, 0x5678);

/// The honest stub witness and its stack.
fn honest() -> &'static (MbWitness, Vec<F64>) {
    static H: OnceLock<(MbWitness, Vec<F64>)> = OnceLock::new();
    H.get_or_init(|| stack_of(stub::stub_witness(SEED)))
}

fn stack_of(w: MbWitness) -> (MbWitness, Vec<F64>) {
    let mut stack = vec![F64::ZERO; 1 << STACK_LOG];
    w.write(&mut stack);
    (w, stack)
}

struct Proof {
    body: Vec<u8>,
    trace: fs6::Trace,
    out: MbOut,
}

fn prove(w: &MbWitness, stack: &[F64]) -> Proof {
    let mut ps = ProverState::v6(fs6::Transcript::start(oracle(), &hdr()));
    ps.add_scalar(PREFIX_SCALAR);
    ps.grind(6);
    let _t = ps.sample();
    let out = prove_minibus(&mut ps, w, stack);
    let (body, trace) = ps.into_v6();
    Proof { body, trace, out }
}

fn walk(ask: &mut dyn Ask, body: &[u8], w: &MbWitness) -> Result<(Vec<VClaim>, Stats), MbReject> {
    let hdr = hdr();
    let mut ch = VChain::start(ask, &hdr, body)?;
    ch.phase(Part::Tree);
    ch.read_e(1)?;
    ch.ground(6)?;
    ch.phase(Part::Stub);
    let claims = refv::minibus::verify_claims(&mut ch, &w.tabs)?;
    let (stats, _) = ch.finish()?;
    Ok((claims, stats[&Part::Stub].clone()))
}

/// Verify against the recorded trace (runSeq: every entry used, each answer the keyed oracle's).
fn verify(p_body: &[u8], trace: &fs6::Trace, w: &MbWitness) -> Result<(Vec<VClaim>, Stats), MbReject> {
    let mut ask = TraceAsk::new(trace, Some(&KEY));
    let r = walk(&mut ask, p_body, w)?;
    ask.finish()?;
    Ok(r)
}

/// Verify a (possibly tampered) `BODY` against the real oracle (its trace re-derived), so only the checks reject.
fn verify_oracle(body: &[u8], w: &MbWitness) -> Result<(Vec<VClaim>, Stats), MbReject> {
    let mut ask = RecordAsk { o: oracle(), tr: Vec::new() };
    walk(&mut ask, body, w)
}

fn e(x: F128) -> E {
    E::new(x.c0, x.c1)
}

fn maps() -> [RingMap; 2] {
    let m = RingMap { f: [F128::ZERO; 8], g: [F128::ZERO; 8] };
    [m, m]
}

#[test]
fn honest_round_trip() {
    let (w, stack) = honest();
    assert_eq!(w.balanced(), (true, true), "the stub's push and pull are equal multisets, counts nonzero");
    let t = Instant::now();
    let p = prove(w, stack);
    let secs = t.elapsed().as_secs_f64();
    let (claims, st) = verify(&p.body, &p.trace, w).expect("the honest proof is accepted");
    eprintln!(
        "mini-bus: prove {secs:.3} s, BODY {} B ({} in §6.4b), {} queries, {} nonces, committed {} words",
        p.body.len(),
        st.body,
        st.queries,
        st.nonces,
        r3mb::m3::committed_words(&w.tabs)
    );
    // FORMAT6 §6.4b counts: 53 draws (queries), 43 nonces, 194 scalars: 3,448 bytes
    assert_eq!((st.queries, st.draws, st.nonces, st.body, st.binds), (53, 53, 43, 3448, 0));
    assert_eq!(p.body.len(), 24 + 3448);
    // the fingerprint's ground query is 40 bytes (`st ‖ nonce`), within FORMAT6 §4's bind rule
    assert_eq!(st.ground_bufs[0], (16, 8));
    assert_eq!(st.chain_lengths[0], 40);
    assert!(st.ground_bufs.iter().all(|&(g, n)| g < 15 || n <= 56));
    // the grinds in schedule order are FORMAT6's (fs6::schedule::mini_bus)
    let gs: Vec<u32> = fs6::schedule::mini_bus(&P18).iter().filter_map(|i| if let Item::G(g) = i { Some(*g) } else { None }).collect();
    assert_eq!(st.ground_bufs.iter().map(|x| x.0).collect::<Vec<_>>(), gs);
    // every query of §6.4b has length 32 or ≡ 8 (mod 16) (FORMAT6 v2.3 check)
    assert!(st.chain_lengths.iter().all(|&l| l == 32 || l % 16 == 8));

    // claims 50–52: the stack satisfies the prover's, and the verifier's are the same claims
    assert_eq!(p.out.claims.len(), 3);
    assert_eq!(r3core::claim::check_all(&p.out.claims, stack), Vec::<String>::new());
    assert_eq!(claims.len(), 3);
    let mut rng = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for (pc, vc) in p.out.claims.iter().zip(&claims) {
        assert_eq!(e(pc.value), vc.value, "{}: value", pc.label);
        for _ in 0..3 {
            let z: Vec<F128> = (0..STACK_LOG).map(|_| F128::new(next(), next())).collect();
            let ze: Vec<E> = z.iter().map(|&x| e(x)).collect();
            assert_eq!(e(pc.weight_at(&z, &maps())), vc.weight(&ze), "{}: weight", pc.label);
        }
        // and on the cube: the weight at a stack index is the dense weight's entry
        let z: Vec<F128> = (0..STACK_LOG).map(|k| F128::new((r3core::layout::MB_LO + 77 >> k & 1) as u64, 0)).collect();
        let ze: Vec<E> = z.iter().map(|&x| e(x)).collect();
        assert_eq!(e(pc.weight_at(&z, &maps())), vc.weight(&ze));
    }
    // the Deferred path refv's batch uses gives the same claims
    let mut ask = TraceAsk::new(&p.trace, Some(&KEY));
    let hdr = hdr();
    let mut ch = VChain::start(&mut ask, &hdr, &p.body).unwrap();
    ch.read_e(1).unwrap();
    ch.ground(6).unwrap();
    let d = refv::minibus::verify(&mut ch, &w.tabs).unwrap();
    ch.finish().unwrap();
    let m = refv::stack::Maps { tree_f: vec![], tree_g: vec![], sponge_f: vec![], sponge_g: vec![], lambda0: E::new(0, 0) };
    let z: Vec<F128> = (0..STACK_LOG).map(|_| F128::new(next(), next())).collect();
    let ze: Vec<E> = z.iter().map(|&x| e(x)).collect();
    for (pc, d) in p.out.claims.iter().zip(d) {
        let (wf, v) = d(&m);
        assert_eq!((wf(&ze), v), (e(pc.weight_at(&z, &maps())), e(pc.value)));
    }
}

/// The GKR's leaf values are the leaves' multilinear extensions at `ζ` by the identity (season 1's
/// `lin_identity`), computed here from the witness alone: `Ṽ_s(ζ) = (1 + Σ_b e_b) + Σ_b e_b·(β_s + Σ_i w_i·c_i~)`.
#[test]
fn leaf_values_match_the_identity() {
    let (w, stack) = honest();
    let p = prove(w, stack);
    let (claims, _) = verify(&p.body, &p.trace, w).unwrap();
    // the claims hold on the stack by the verifier's weights too (dense evaluation over the block)
    for (vc, pc) in claims.iter().zip(&p.out.claims) {
        let mut acc = E::new(0, 0);
        for &(k, at, tau) in &vc.parts {
            let col: Vec<E> = stack[at..at + (1 << tau)].iter().map(|x| E::new(x.0, 0)).collect();
            acc += k * refv::arith::multilinear_eval(&col, &vc.zeta[..tau]);
        }
        assert_eq!(acc, vc.value, "{}", pc.label);
    }
    assert_eq!(p.out.point.len(), r3mb::MINI_DEPTH);
    assert_eq!(p.out.alphas.len(), 4);
}

/// Rebuild `BODY` with the scalars of §6.4b tampered (`tamper(i, bytes)` on scalar `i`) and every nonce searched
/// again, so the proof of work passes and only the checks can reject.
fn regrind(body: &[u8], tamper: impl Fn(usize, &mut [u8])) -> (Vec<u8>, fs6::Trace) {
    let mut t = fs6::Transcript::start(oracle(), &hdr());
    t.absorb(&body[..16]);
    t.ground(6);
    let (mut pos, mut i) = (24usize, 0usize);
    for item in fs6::schedule::mini_bus(&P18) {
        match item {
            Item::E(k) => {
                for _ in 0..k {
                    let mut b = body[pos..pos + 16].to_vec();
                    tamper(i, &mut b);
                    t.absorb(&b);
                    pos += 16;
                    i += 1;
                }
            }
            Item::G(g) => {
                pos += 8;
                t.ground(g);
            }
            Item::D(k) => {
                t.draws(k);
            }
            x => panic!("§6.4b has no {x:?}"),
        }
    }
    assert_eq!((pos, i), (body.len(), 194));
    t.finish()
}

#[test]
fn tampered_scalars_are_rejected() {
    let (w, stack) = honest();
    let p = prove(w, stack);
    // the regrind itself is faithful
    let (b0, tr0) = regrind(&p.body, |_, _| {});
    assert_eq!(b0, p.body);
    assert!(verify(&b0, &tr0, w).is_ok());
    // scalar indices: 0 shared, 1 count; step k starts at 2 + Σ_{j<k} (8j + 12), its 2k rounds (4 each) first
    let start = |k: usize| 2 + (0..k).map(|j| 8 * j + 12).sum::<usize>();
    let cases = [
        (0, 0),
        (1, 0),
        (start(0) + 5, 0),             // a child of step 0
        (start(3) + 2 * 4 + 1, 3),     // round 2's c₂ of step 3
        (start(5), 5),                 // round 0's c₁ of step 5
        (start(5) + 40 + 11, 5),       // the count tree's last child of step 5 (the last scalar)
    ];
    for (idx, step) in cases {
        let (b, tr) = regrind(&p.body, |i, x| {
            if i == idx {
                x[0] ^= 1;
            }
        });
        assert_eq!(verify(&b, &tr, w).err(), Some(MbReject::Layer(step)), "scalar {idx}");
    }
    assert_eq!(start(5) + 40 + 12, 194);
}

#[test]
fn tampered_nonce_and_trace_are_rejected() {
    let (w, stack) = honest();
    let p = prove(w, stack);
    // the fingerprint group's nonce: its PoW lane fails (with probability 1 − 2^-16)
    let mut b = p.body.clone();
    b[24] ^= 1;
    assert_eq!(verify_oracle(&b, w).err(), Some(MbReject::Chain(Reject::Pow(Part::Stub))));
    // a scalar changed under the honest trace: the query is not the trace's
    let mut b = p.body.clone();
    b[24 + 8] ^= 1;
    assert!(matches!(verify(&b, &p.trace, w).err(), Some(MbReject::Chain(Reject::TraceMismatch(..)))));
    // a short BODY
    assert!(matches!(verify_oracle(&p.body[..p.body.len() - 16], w).err(), Some(MbReject::Chain(Reject::BodyShort(_)))));
}

/// Push ≠ pull: the honest-looking prover fails (the vendored GKR asserts the two roots equal).
#[test]
fn unbalanced_tables_fail() {
    let (w, stack) = stack_of(stub::stub_unbalanced(SEED));
    assert!(!w.balanced().0);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove(&w, &stack)));
    assert!(r.is_err(), "the prover refuses unbalanced tables");
}

/// A zero count (balanced tables): the count root is zero and the verifier rejects (`count ≠ 0`).
#[test]
fn zero_count_is_rejected() {
    let (w, stack) = stack_of(stub::stub_zero_count(SEED));
    assert_eq!(w.balanced(), (true, false));
    let p = prove(&w, &stack);
    assert_eq!(verify(&p.body, &p.trace, &w).err(), Some(MbReject::CountZero));
}

/// A committed word changed after the proof: some claim of 50–52 no longer holds on the stack.
#[test]
fn tampered_stack_fails_the_claims() {
    let (w, stack) = honest();
    let p = prove(w, stack);
    for (t, c) in [(0usize, 0usize), (2, 2), (3, 1)] {
        let r3mb::MbCol::Com { at } = w.tabs[t].cols[c] else { panic!() };
        let mut s = stack.clone();
        s[at + 3].0 ^= 1 << 7;
        assert!(!r3core::claim::check_all(&p.out.claims, &s).is_empty(), "table {t} column {c}");
    }
}

/// BODY byte-identical at 1, 4 and 8 threads (each in its own process: the pool's size is fixed once).
#[test]
fn deterministic_across_threads() {
    let exe = std::env::current_exe().unwrap();
    let bodies: Vec<String> = [1, 4, 8]
        .iter()
        .map(|n| {
            let out = std::process::Command::new(&exe)
                .args(["det_child", "--exact", "--ignored", "--nocapture", "--test-threads=1"])
                .env("R3MB_THREADS", n.to_string())
                .output()
                .unwrap();
            let text = String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
            assert!(out.status.success(), "child at {n} threads: {text}");
            // the harness prints `test det_child ... ` before the child's own line
            let body = text.split("BODY ").nth(1).and_then(|r| r.split_whitespace().next());
            body.unwrap_or_else(|| panic!("no BODY line: {text}")).to_string()
        })
        .collect();
    assert_eq!(bodies[0].len(), 2 * (24 + 3448));
    assert!(bodies.iter().all(|b| *b == bodies[0]), "BODY differs across thread counts");
}

#[test]
#[ignore = "run by deterministic_across_threads"]
fn det_child() {
    let n: usize = std::env::var("R3MB_THREADS").unwrap().parse().unwrap();
    parallel::set_num_threads(n);
    let (w, stack) = honest();
    let p = prove(w, stack);
    println!("BODY {}", p.body.iter().map(|b| format!("{b:02x}")).collect::<String>());
}

/// R7: real-table shape (MBT's `mbT6`, a blob's `MINIBUS` section): 76 seed arrays of 16 `STREAM` cells (values in
/// `C_rec`, slot 33), 16 read tables of `2^6` rows with address and value columns in `T` (slot 38), finalize and
/// count columns in `MB_LO..MB_HI`. The prover's claims (one dense weight on the block holding every column) and the
/// verifier's (`r3mb::export::tables_of`, parts) agree; the round trip accepts.
#[test]
fn export_round_trip() {
    use r3core::layout::{MB_LO, idx};
    use r3mb::typed_mb::seed_addr;
    use r3typed::circuit::MbExport;
    let mut rng = 0x1234_5678_9abc_def1u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let mut stack = vec![F64::ZERO; 1 << STACK_LOG];
    let mut m = MbExport::default();
    let mut cells = Vec::new();
    for i in 0..76usize {
        let q = 3 + i; // stream cells 16q …
        let v = idx(33, 16 * q);
        for x in 0..16 {
            stack[v + x] = F64(next());
            cells.push((16 * q + x, stack[v + x]));
        }
        m.seeds.push((1, 16 * q, 1, 4, vec![v], MB_LO + 16 * i));
    }
    for k in 0..16usize {
        let (a, v) = (idx(38, 128 * k), idx(38, 128 * k + 64));
        for x in 0..64 {
            let (c, val) = cells[(next() as usize) % if x % 3 == 0 { cells.len() } else { 40 }];
            stack[a + x] = seed_addr(c, 1, 0)[0];
            stack[v + x] = val;
        }
        m.reads.push((1, 6, a, vec![v], MB_LO + 4096 + 64 * k));
    }
    let w = r3mb::export::witness_of(&m, &stack);
    assert_eq!(w.balanced(), (true, true));
    w.write(&mut stack);
    let vt = r3mb::export::tables_of(&m);
    assert_eq!(format!("{:?}", vt), format!("{:?}", w.tabs), "the verifier's tables are the prover's");
    assert_eq!(r3mb::prove::claim_block(&w.tabs), (4, 22), "slots 32–39");
    let p = prove(&w, &stack);
    let (claims, _) = verify(&p.body, &p.trace, &w).expect("accepted");
    assert_eq!(r3core::claim::check_all(&p.out.claims, &stack), Vec::<String>::new());
    for (pc, vc) in p.out.claims.iter().zip(&claims) {
        assert_eq!(e(pc.value), vc.value, "{}: value", pc.label);
        let z: Vec<F128> = (0..STACK_LOG).map(|_| F128::new(next(), next())).collect();
        let ze: Vec<E> = z.iter().map(|&x| e(x)).collect();
        assert_eq!(e(pc.weight_at(&z, &maps())), vc.weight(&ze), "{}: weight", pc.label);
    }
}
