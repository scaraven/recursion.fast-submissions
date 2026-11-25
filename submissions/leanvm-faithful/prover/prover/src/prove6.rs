//! The lvm6 SNARK prover for one step (WP R3): FORMAT6 v2.5.2 end to end, leaf mode (`b = 0`, step 1) or node mode
//! (`b = 1`, steps 2 … 16). `HDR`, the witness of every block (tree, `STREAM`, sponge rows, typed memory, mini-bus
//! columns), §6.1 commitment, §6.2 tree batch (R2), §6.3 sponge batch, §6.4a typed phases, §6.4b mini-bus, §6.5 ring
//! switching and the `λ₀` batch of the 53 stack claims, §6.6 opening. The caller signs the returned trace (the
//! stream driver's last `SIGN`, or the toy signer in dev).
//!
//! Node mode's `STREAM` (slot 33, CD-circuit.md §0): from word 0 the child's trace stream `0x54 ‖ Σ (enc64 |q| ‖ q ‖ a)`
//! (the bytes `traceDigest` hashes) with its Keccak padding (`PadOkB`: `0x01` at byte `L`, `0x80` in the last byte of
//! block `⌊L/136⌋`), 8 bytes a word; `σ'` at word `2^18`, `σ_leaf` at `2^18 + 597`, both in `readSig`'s order
//! (`format::put_sig`: index, 133 chain values, 16 path nodes). Every other cell is zero (§2.1).

use std::time::Instant;

use keccak_gkr::tree::{self, Tree};
use primitives::field::F64;
use primitives::transcript::ProverState;
use r3core::claim::{PClaim, check_all};
use r3core::layout;
use r3core::open6;

use crate::format::{Sig, Signed, put_sig};
use crate::keccak::{data_root, leaf_stmt, node_stmt};
use fs6::Digest;

/// STUB tables of the mini-bus (`r3mb::stub`) until CD's exist; `refv-full` rebuilds them from the same seed.
pub const MB_SEED: u64 = 1;

/// The previous step, for node mode.
pub struct Child<'a> {
    /// The child's statement `c'` (`prev.stmt`).
    pub c_prev: Digest,
    /// The child's signed proof `(π', tr', σ')` (`prev.bin`).
    pub signed: &'a Signed,
    /// This step's `σ_leaf` (the zero-item `SIGN`, FORMAT6 §8).
    pub sigma_leaf: &'a Sig,
    /// The child's `accOut` (this step's `accIn`).
    pub acc_out: r3typed::Acc,
}

/// Which parts to prove (dev: all four in a real proof) and whether to check every stack claim natively.
#[derive(Clone, Copy, Debug)]
pub struct Opts {
    pub sponge: bool,
    pub typed: bool,
    pub mb: bool,
    pub check: bool,
}

impl Default for Opts {
    fn default() -> Self {
        Self { sponge: true, typed: true, mb: true, check: false }
    }
}

pub struct Proved {
    pub pi: Vec<u8>,
    pub trace: fs6::Trace,
    /// The statement `c` and the data root `h`.
    pub c: Digest,
    pub h: Digest,
    /// This proof's `accOut` (the next step's `accIn`).
    pub acc_out: Option<r3typed::Acc>,
    pub claims: usize,
    pub times: Vec<(&'static str, f64)>,
}

/// Dev (instruction counts by prefix, R3-node.md §5): `LVM6_STOP_AFTER=<phase>` ends the process right after that
/// phase of the first proof made (`witness`, `commit`, `tree`, `rest`), so an SDE icount of the prefix can be taken.
/// It never changes a byte of a proof that is written.
fn stop_after(phase: &str) {
    if std::env::var("LVM6_STOP_AFTER").is_ok_and(|v| v == phase) {
        eprintln!("LVM6_STOP_AFTER={phase}: exit");
        std::process::exit(0);
    }
}

/// The trace stream `0x54 ‖ Σ (enc64 |q| ‖ q ‖ a)` with its Keccak-256 padding to whole 136-byte blocks.
pub fn trace_stream(tr: &fs6::Trace) -> Vec<u8> {
    let mut b = vec![0x54u8];
    for (q, a) in tr {
        b.extend_from_slice(&(q.len() as u64).to_le_bytes());
        b.extend_from_slice(q);
        b.extend_from_slice(a);
    }
    let l = b.len();
    let blocks = l / 136 + 1;
    b.resize(136 * blocks, 0);
    b[l] ^= 0x01;
    b[136 * blocks - 1] ^= 0x80;
    b
}

/// Node mode's `STREAM` words into the stack.
pub fn write_stream(stack: &mut [F64], child: &Child) {
    let words = |b: &[u8]| -> Vec<u64> {
        b.chunks(8)
            .map(|c| {
                let mut w = [0u8; 8];
                w[..c.len()].copy_from_slice(c);
                u64::from_le_bytes(w)
            })
            .collect()
    };
    let ts = words(&trace_stream(&child.signed.tr));
    assert!(ts.len() <= layout::STREAM_SIG, "the child's trace fits below σ' (CD: traceFits_P18)");
    for (w, &x) in ts.iter().enumerate() {
        stack[layout::stream_idx(w)] = F64(x);
    }
    for (base, sig) in [(layout::STREAM_SIG, &child.signed.sig), (layout::STREAM_SIG_LEAF, child.sigma_leaf)] {
        let mut b = Vec::new();
        put_sig(&mut b, sig);
        let ws = words(&b);
        assert_eq!(ws.len(), 597);
        for (w, &x) in ws.iter().enumerate() {
            stack[layout::stream_idx(base + w)] = F64(x);
        }
    }
}

/// R8: load the circuit `Q` in use and compute its witness plan (`r3typed::witness::prewarm`), so that a step's
/// timed part does neither: the stream calls it before `ready`, `full6` before step 1. `LVM6_NO_PRELOAD=1` (dev) skips
/// it (the step then loads `Q` and plans as before R8; the proof is the same).
pub fn preload() {
    if std::env::var_os("LVM6_NO_PRELOAD").is_some_and(|v| v == "1") {
        return;
    }
    let t = Instant::now();
    let c = r3typed::circuit();
    let tl = t.elapsed().as_secs_f64();
    let tp = r3typed::witness::prewarm(&r3sponge::cont_rows());
    eprintln!("preload: Q {} entries in {tl:.3} s, witness plan {tp:.3} s", c.ents.len());
}

/// One step's proof: `xs` the `n·32` data bytes (`n = 2^18`), `vk` the stream's key, `child` in node mode.
pub fn prove6(n: u64, xs: &[u8], vk: &Digest, child: Option<&Child>, opts: &Opts) -> Proved {
    let sh = fs6::params::P18;
    assert_eq!(n, 1 << sh.log_blocks, "the SNARK branch has one leaf size (BLUEPRINT §2.1)");
    assert_eq!(xs.len() as u64, 32 * n);
    fs6::set_v6(true);
    let o = crate::oracle::get();
    let mut times: Vec<(&'static str, f64)> = Vec::new();

    // The tree (slots 0–32 of the stack).
    let t = Instant::now();
    let blocks: Vec<[u64; 4]> = xs
        .chunks_exact(32)
        .map(|b| std::array::from_fn(|m| u64::from_le_bytes(b[8 * m..8 * m + 8].try_into().unwrap())))
        .collect();
    let tr = Tree::new(blocks);
    let h = tr.root();
    debug_assert_eq!(h, data_root(xs), "D(1) is the contract's dataRoot");
    let (witness, mut stack) = tr.witness();
    assert_eq!(stack.len(), 1 << layout::STACK_LOG);
    times.push(("witness.tree", t.elapsed().as_secs_f64()));

    // HDR and the statement: b = 0: c' = 0, accIn = (0^v, Φ_Q(0^v)); b = 1: c', accIn = the child's accOut.
    let circ = r3typed::circuit();
    let acc_in = child.map_or_else(|| r3typed::Acc::leaf(circ), |ch| ch.acc_out.clone());
    let acc_hdr = opts.typed.then(|| acc_in.to_hdr());
    let (b, c_prev) = child.map_or((0, [0u8; 32]), |ch| (1, ch.c_prev));
    let hdr = fs6::schedule::header(&sh, b, n, &h, &c_prev, vk, acc_hdr.as_deref());
    let leaf = leaf_stmt(&h, n);
    let c = child.map_or(leaf, |ch| node_stmt(&ch.c_prev, &leaf));

    // Every other block before the commitment and before §6.2 (which reads all 64 slots): STREAM, then the sponge
    // rows (they absorb STREAM and X), then T (its `KS` region reads Y), then the mini-bus columns.
    let t = Instant::now();
    if let Some(ch) = child {
        write_stream(&mut stack, ch);
    }
    times.push(("witness.stream", t.elapsed().as_secs_f64()));
    let t = Instant::now();
    let mut sp_w = opts.sponge.then(|| r3sponge::SpongeWitness::generate(&mut stack, &r3sponge::cont_rows()));
    times.push(("witness.sponge", t.elapsed().as_secs_f64()));
    let t = Instant::now();
    // Dev (`LVM6_TY_TIE_PROBE`, node mode): the accumulator tie rows of `Q`, the witness on this header and on two
    // headers with `accIn` altered (on copies of the stack).
    if opts.typed && child.is_some() && std::env::var_os("LVM6_TY_TIE_PROBE").is_some() {
        eprintln!("typed tie probe: {:?}", r3typed::witness::acc_tie_probe(circ, &stack, &hdr));
    }
    // R7: if `Q` reads the sponge message cells `X` through `ks` (KSA), the typed witness runs the rows from `split`
    // itself (`X` from their copy rows), then `X` is written and the sponge rows are generated again.
    let link = opts.typed.then(|| r3typed::witness::sponge_link(circ, &r3sponge::cont_rows())).flatten();
    let ty_w = opts.typed.then(|| {
        r3typed::witness::witness_linked(circ, &mut stack, &r3typed::pub_lanes(&hdr), link.as_ref()).unwrap_or_else(|e| {
            // dev (R7): every violated row with its words, sources and values
            if std::env::var_os("LVM6_TY_DIAG").is_some() {
                eprintln!("{}", r3typed::witness::diagnose(circ, &stack, &r3typed::pub_lanes(&hdr), link.clone()));
            }
            if let (Some(ch), Some(l)) = (child.filter(|_| std::env::var_os("LVM6_X_CHECK").is_some()), link.as_ref()) {
                let mut st = stack.clone();
                r3typed::witness::x_writes_dev(circ, &stack, &r3typed::pub_lanes(&hdr), l).iter().for_each(|&(i, v)| st[i] = v);
                x_check(&st, ch);
            }
            panic!("typed witness: {e:?}")
        })
    });
    if let Some(w) = ty_w.as_ref().filter(|w| !w.x_writes.is_empty()) {
        w.x_writes.iter().for_each(|&(i, v)| stack[i] = v);
        if opts.sponge {
            sp_w = Some(r3sponge::SpongeWitness::generate(&mut stack, &r3sponge::cont_rows()));
        }
        if let Some(ch) = child.filter(|_| std::env::var_os("LVM6_X_CHECK").is_some()) {
            x_check(&stack, ch);
        }
        // the `ks` words the typed witness used are the stack's now (dev runs without the sponge part skip it)
        for r in circ.regs_of(r3typed::circuit::Src::Ks).filter(|_| opts.sponge) {
            for k in 0..r.len() {
                assert_eq!(stack[r.stack_idx(k)], w.z[r.base + k], "ks word {} after the sponge rows", r.base + k);
            }
        }
    }
    times.push(("witness.typed", t.elapsed().as_secs_f64()));
    let t = Instant::now();
    let mb_w = opts.mb.then(|| {
        // R7: the blob's MINIBUS tables (their value columns are `T`/`STREAM` words already written), else the stub
        let w = r3mb::export::witness_in_use(MB_SEED, &stack);
        w.write(&mut stack);
        w
    });
    times.push(("witness.mb", t.elapsed().as_secs_f64()));
    stop_after("witness");

    // §6.1.
    let t = Instant::now();
    let c0 = open6::commit0(o, &sh, &stack);
    times.push(("commit", t.elapsed().as_secs_f64()));
    stop_after("commit");
    let mut ps = ProverState::v6(fs6::Transcript::start(o, &hdr));
    let mut claims: Vec<PClaim> = vec![open6::commitment(ps.chain().unwrap(), &sh, &c0, &stack)];

    // §6.2.
    let t = Instant::now();
    let op = tree::prove_tree(&mut ps, &tr, &witness, &stack);
    drop(witness);
    claims.push(PClaim::ring("1 tree ring", 0, op.inputs.point.clone(), op.inputs.slices.clone(), 0));
    claims.push(PClaim::point("2 tree c_out", 0, op.outputs.point.clone(), op.outputs.value));
    let hw: [u64; 4] = std::array::from_fn(|m| u64::from_le_bytes(h[8 * m..8 * m + 8].try_into().unwrap()));
    for (k, (p, v)) in op.wiring_claims(&hw).into_iter().enumerate() {
        let name = if k < 8 { format!("{} wiring slot {k}", 3 + k) } else { format!("{} root {}", 3 + k, k - 8) };
        claims.push(PClaim::point(name, 0, p, v));
    }
    times.push(("6.2 tree", t.elapsed().as_secs_f64()));
    stop_after("tree");

    // §6.3.
    if let Some(w) = &sp_w {
        let t = Instant::now();
        claims.extend(r3sponge::prove_sponge(&mut ps, w, &stack).claims);
        times.push(("6.3 sponge", t.elapsed().as_secs_f64()));
    }
    drop(sp_w);

    // §6.4a, §6.4b.
    let mut acc_out = None;
    if let Some(w) = &ty_w {
        let t = Instant::now();
        let out = r3typed::prove_typed(&mut ps, w, &stack, &acc_in);
        claims.extend(out.claims);
        acc_out = Some(out.acc_out);
        times.push(("6.4a typed", t.elapsed().as_secs_f64()));
    }
    if let Some(w) = &mb_w {
        let t = Instant::now();
        claims.extend(r3mb::prove_minibus(&mut ps, w, &stack).claims);
        times.push(("6.4b mb", t.elapsed().as_secs_f64()));
    }
    drop((ty_w, mb_w));
    stop_after("rest");

    if opts.check {
        let t = Instant::now();
        let bad = check_all(&claims, &stack);
        assert!(bad.is_empty(), "stack claims fail natively: {bad:?}");
        times.push(("check", t.elapsed().as_secs_f64()));
    }

    // §6.5, §6.6.
    let t = Instant::now();
    let n_claims = claims.len();
    let ot = open6::open(ps.chain().unwrap(), &sh, stack, c0, &claims, opts.check);
    times.push(("6.5 batch", ot.batch));
    for (i, s) in ot.levels.iter().enumerate() {
        times.push((["6.6 L0", "6.6 L1", "6.6 L2", "6.6 L3", "6.6 L4+tail"][i.min(4)], *s));
    }
    times.push(("open", t.elapsed().as_secs_f64()));

    let (body, trace) = ps.into_v6();
    let pi = [hdr, body].concat();
    Proved { pi, trace, c, h, acc_out, claims: n_claims, times }
}

/// The child's `accOut` (this step's `accIn`), from its signed proof alone (the stream driver reads only `prev.bin`):
/// `r3typed::acc_out_from_proof` (accIn from its `HDR`, `h` from its `BODY`, `κ, r_x, r_y, t` from its trace answers,
/// positions from `fs6::schedule`).
pub fn child_acc_out(signed: &Signed) -> r3typed::Acc {
    r3typed::acc_out_from_proof(&signed.pi, &signed.tr)
}

/// Dev (R7, `LVM6_X_CHECK`): the sponge message cells `X` of rows `split + i` against σ′'s honest Keccak blocks
/// (chain steps, the WOTS leaf's 32 blocks, the 16 path nodes), printed.
fn x_check(stack: &[F64], ch: &Child) {
    use crate::format::{TAG_SIG_NODE, TAG_WOTS, TAG_WOTS_LEAF, WOTS_LEN, trace_digest, wots_digits};
    use r3core::layout::{MSG_LANES, x_idx};
    let blocks = |m: &[u8]| -> Vec<[u64; MSG_LANES]> {
        let mut b = m.to_vec();
        let l = b.len();
        let n = l / 136 + 1;
        b.resize(136 * n, 0);
        b[l] ^= 1;
        b[136 * n - 1] ^= 0x80;
        b.chunks(136).map(|c| std::array::from_fn(|k| u64::from_le_bytes(c[8 * k..8 * k + 8].try_into().unwrap()))).collect()
    };
    let x = |i: usize| -> [u64; MSG_LANES] { std::array::from_fn(|l| stack[x_idx(i, l)].0) };
    let sig = &ch.signed.sig;
    let m = trace_digest(&ch.signed.tr);
    let d = wots_digits(&m);
    let j = sig.idx;
    // honest chain steps (from ots[c] at pos d_c), every pos
    let mut steps = std::collections::HashMap::new();
    let mut ends = Vec::new();
    for c in 0..WOTS_LEN {
        let mut v = sig.ots[c];
        for pos in d[c]..3 {
            let pre = [&[TAG_WOTS][..], &j.to_le_bytes(), &[c as u8, pos as u8], &v].concat();
            steps.insert(blocks(&pre)[0], (c, pos));
            v = keccak256::hash(&pre);
        }
        ends.push(v);
    }
    let mut hits = 0;
    let mut first_miss = Vec::new();
    for i in 0..399 {
        match steps.get(&x(i)) {
            Some(_) => hits += 1,
            None if first_miss.len() < 6 => first_miss.push(i),
            None => {}
        }
    }
    eprintln!("x_check: digits d[128..133] = {:?} (honest, checksum {})", &d[128..], d[..128].iter().map(|v| 3 - v).sum::<u32>());
    for i in 381..399 {
        let w = x(i);
        eprintln!("x_check: row {i}: chain {} pos {} lane0 {:#x} honest {:?}", w[1] >> 8 & 0xff, w[1] >> 16 & 0xff, w[0], steps.get(&w));
    }
    eprintln!("x_check: chain rows 0..399: {hits} match an honest step (honest steps {}), first misses {first_miss:?}", steps.len());
    let leaf = [&[TAG_WOTS_LEAF][..], &j.to_le_bytes(), &ends.concat()].concat();
    let lb = blocks(&leaf);
    let lm: Vec<usize> = (0..lb.len()).filter(|&k| x(399 + k) != lb[k]).collect();
    eprintln!("x_check: leaf blocks {}: mismatching {:?}", lb.len(), &lm[..lm.len().min(10)]);
    if let Some(&k) = lm.first() {
        eprintln!("x_check: block {k} want {:x?}\n          got  {:x?}", lb[k], x(399 + k));
    }
    let mut cur = keccak256::hash(&leaf);
    let mut kk = j;
    for (t, sib) in sig.path.iter().enumerate() {
        let pre = if kk % 2 == 0 { [&[TAG_SIG_NODE][..], &cur, sib].concat() } else { [&[TAG_SIG_NODE][..], sib, &cur].concat() };
        let ok = x(399 + lb.len() + t) == blocks(&pre)[0];
        if !ok || t == 0 {
            eprintln!("x_check: path node {t} (row i {}): {}", 399 + lb.len() + t, if ok { "ok" } else { "MISMATCH" });
        }
        cur = keccak256::hash(&pre);
        kk /= 2;
    }
}
