//! `flock-prover`: the native prover of the `flock-recursive` entry (stage P1: the prover core).
//!
//! Modes (development; the runner's `setup`/`tree`/`leaf`/`node` are stage P2):
//!   flock-prover selftest                         tier kernels against the reference
//!   flock-prover test-leaf M [--n N] [--reps R]   prove + native verify, in-process keyed oracle
//!   flock-prover prove-leaf M [--n N] --start HEX --out FILE [--reps R]
//!                                                 through the service at $RF_ORACLE: prove, record
//!                                                 the verifier's trace, SIGN, write the signed file,
//!                                                 check it with the native `acc`
//!   flock-prover prove-agg N --start HEX --out FILE [--reps R]
//!                                                 the aggregate leaf `A` of a chain of N steps
//!                                                 (segments L32/L31) through the service, signed
//!   flock-prover first WORK | step WORK           the stream (PROVER.md §3): N8 from chainA/B.json;
//!                                                 N2/N4 from prev.stmt, prev.bin, chain.json
//!   flock-prover node-kat N8|N4|N2 [--prev FILE] [--agg N] [--prove] [--out-signed FILE]
//!   flock-prover plan-build [--out FILE] | plan-kat   the embedded node data (plan form)
//!   flock-prover acc --vk HEX --stmt HEX FILE     the native `acc` on a signed-proof file
//! Environment: FLOCK_THREADS (default all CPUs), FLOCK_TIER (force `portable`, `pclmul`, `ymm`).
#![allow(clippy::needless_range_loop, clippy::too_many_arguments, dead_code)]

mod agg;
mod alloc;
mod bench;
mod blake2s;
mod circuit;
mod field;
mod format;
mod ir;
mod items;
mod kat;
mod leaf;
mod ligerito;
mod lincheck;
mod merkle;
mod mfill;
mod node;
mod nodeops;
mod nodeprove;
mod mle;
mod nodeshape;
mod ntt;
mod oracle;
mod par;
mod params;
mod plan;
mod prof;
mod ringswitch;
mod service;
mod simd;
mod skipdom;
mod stream;
mod sumcheck;
mod transcript;
mod witness;
mod zerocheck;

use blake2s::{leaf_stmt, Digest};
use oracle::{Recorder, Replay, Seq};
use std::time::Instant;

#[global_allocator]
static ALLOC: alloc::Cache = alloc::Cache;

fn unhex(s: &str) -> Digest {
    let s = s.trim();
    assert_eq!(s.len(), 64, "a digest is 64 hex characters");
    let mut d = [0u8; 32];
    for i in 0..32 {
        d[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex");
    }
    d
}

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

pub fn peak_rss_mb() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    for l in s.lines() {
        if let Some(v) = l.strip_prefix("VmHWM:") {
            let kb: f64 = v.trim().trim_end_matches("kB").trim().parse().unwrap_or(0.0);
            return kb / 1024.0;
        }
    }
    0.0
}

/// Which verifier `acc` runs on the proof.
#[derive(Clone, Copy, PartialEq)]
pub enum Top {
    /// `V4with` (`FRVerifier4.kindOf4`): `'A'` → `V_A`; a bare segment byte → reject; a node byte →
    /// the node verifier (not built natively: reject); anything else → `W` (not built: reject).
    V4,
    /// A bare segment proof against its own kind's verifier (the measurement modes' check; not the
    /// relation's `acc`, which rejects a bare segment).
    Seg,
    /// `V4with` with `V_A` over the dumped Lean segment programs (`ir::run_agg`) in `dir`.
    Lean(&'static std::path::Path),
}

/// The native `acc vk c p` (FORMAT.md, `FRVerifier4.accWith4`): `|π| < 2^64`, `|tr| ≤ qV4`,
/// `queryCap`, the signature on the trace digest, and `V` run against the trace (`runSeq`: the trace
/// consumed exactly).
pub fn acc(circ: &circuit::Circuit, vk: &Digest, c: &Digest, file: &[u8]) -> Result<(), String> {
    acc_with(Top::V4, circ, vk, c, file)
}

pub fn acc_with(top: Top, circ: &circuit::Circuit, vk: &Digest, c: &Digest, file: &[u8]) -> Result<(), String> {
    let p = format::from_file(file).ok_or("not a signed-proof file")?;
    if u64::try_from(p.pi.len()).is_err() {
        return Err(format!("|π| = {} is not below 2^64", p.pi.len()));
    }
    if p.tr.len() > params::QV {
        return Err(format!("|tr| = {} > qV = {}", p.tr.len(), params::QV));
    }
    if p.tr.iter().any(|(q, _)| q.len() > format::QUERY_CAP) {
        return Err("a query above queryCap".into());
    }
    if !format::sig_ok(vk, &format::trace_digest(&p.tr), &p.sig) {
        return Err("SigOk fails".into());
    }
    let seq = Seq::new(&p.tr);
    let b = p.pi.first().copied().unwrap_or(0);
    let ok = match (top, b) {
        (Top::Seg, _) => ir::seg_cap(b).is_some() && leaf::verify(&seq, circ, vk, c, &p.pi),
        (_, agg::KIND_AGG) => match top {
            Top::Lean(dir) => {
                let prog = |k: u8| -> Option<String> {
                    let m = match k {
                        0x50 => 30,
                        0x4B => 31,
                        _ => 32,
                    };
                    std::fs::read_to_string(dir.join(format!("ops-L{m}.txt"))).ok()
                };
                ir::run_agg(&prog, circ, &seq, vk, c, &p.pi).ok
            }
            _ => agg::verify(&seq, circ, vk, c, &p.pi),
        },
        _ if ir::seg_cap(b).is_some() => return Err("a bare segment proof (V4with: rejected)".into()),
        // a node: the kind's dumped program (prototype 0's at the kind's index, real cells) with its
        // node ops, and the statement fact `stmtOk4` after the run (INT-8)
        (_, 0x4D..=0x4F) => {
            let k = node::NK::of_byte(b).unwrap();
            let nd = plan::node_data();
            let ctx = std::sync::Arc::new(ir::NodeCtx { k, protos: nd.protos.clone(), kt: std::sync::Arc::new(nd.kind_tab(k)) });
            let base = circuit::Circuit::build_base();
            ir::run_node(&nd.node_program(k), ctx, &base, &seq, vk, c, &p.pi).ok && nodeprove::stmt_ok4(&p.pi, c)
        }
        _ => return Err("a W proof: not built natively".into()),
    };
    if !ok {
        return Err("V rejects".into());
    }
    if !seq.consumed() {
        return Err("V did not ask exactly the trace's queries".into());
    }
    Ok(())
}

/// The dumped Lean programs (`kat::find_ir_dump`), leaked for `Top::Lean`.
fn lean_dir() -> Option<&'static std::path::Path> {
    kat::find_ir_dump().map(|d| &*Box::leak(d.into_boxed_path()))
}

/// `--n N`: a segment of `N ≤ 2^(m−14)` steps (revision 4.0); default the full `2^(m−14)`.
fn seg_n(args: &[String], m: usize) -> u64 {
    let n = arg(args, "--n").map(|x| x.parse().expect("--n")).unwrap_or_else(|| params::leaf_n(m));
    assert!((1..=params::leaf_n(m)).contains(&n), "--n: 1 … 2^(m−14)");
    n
}

/// The M slot fill on the node dump (`mfill.rs`): segment children of the given `m` (and `--n`)
/// replayed by prototype 1 at their index, the inactive fill of both prototypes; every row checked.
fn mfill_kat(args: &[String]) {
    let (dd, pd) = mfill::find_dirs().unwrap_or_else(|| service::fatal("no node dump (FLOCK_NODE_DUMP)"));
    let t = Instant::now();
    let protos: Vec<mfill::Proto> = (0..2).map(|pi| mfill::Proto::load(&dd, pi)).collect();
    println!("MFILL load {:.2}s rows {} / {} regs {} / {} aux {} / {}", t.elapsed().as_secs_f64(), protos[0].rows.len(), protos[1].rows.len(), protos[0].regs.len(), protos[1].regs.len(), protos[0].aux.len(), protos[1].aux.len());
    for (pi, p) in protos.iter().enumerate() {
        for rep in 0..2 {
            let t = Instant::now();
            let (_, st) = mfill::fill(p, None);
            println!("MFILL proto={pi} inactive rep={rep} {:.2}s {st:?}", t.elapsed().as_secs_f64());
        }
    }
    let circ = circuit::Circuit::build();
    let o = oracle::Local::keyed(&[0x5Au8; 32]);
    let vk = [7u8; 32];
    let s: Digest = std::array::from_fn(|i| i as u8 ^ 0x33);
    let text = std::fs::read_to_string(pd.join("proto-p1.txt")).unwrap_or_else(|_| service::fatal("proto-p1.txt (FLOCK_PROTO_DIR)"));
    for m in args[2..].iter().take_while(|a| !a.starts_with("--")).filter_map(|a| a.parse::<usize>().ok()) {
        let n = seg_n(args, m);
        let (pi, _) = leaf::prove_seg(&o, &circ, &vk, &s, m, n);
        let c = leaf::seg_c(&s, n);
        let ix = match m { 32 => 0, 30 => 1, _ => 2 };
        let t = Instant::now();
        let (r, regs) = ir::run_regs(&ir::spec_kind(&text, ix), &circ, &o, &vk, &c, &pi);
        let rt = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let (_, st) = mfill::fill(&protos[1], Some((&regs, ix)));
        println!("MFILL proto=1 m={m} n={n} ix={ix} run_ok={} failed={:?} asks={} run_s={rt:.2} fill_s={:.2} {st:?}", r.ok, r.failed, r.asks, t.elapsed().as_secs_f64());
    }
}

/// An ordered recording oracle (the trace a verifier asks).
struct Tape<'a>(&'a dyn oracle::Oracle, std::sync::Mutex<oracle::Trace>);
impl oracle::Oracle for Tape<'_> {
    fn ask(&self, q: &[u8]) -> Digest {
        let a = self.0.ask(q);
        self.1.lock().unwrap().push((q.to_vec(), a));
        a
    }
}

/// **The node witness KAT** (`node-kat N8 [--n N] [--m M]`): two aggregates of one segment each
/// (kind `L{M}`, `N` steps), signed by the test signer; the N8 witness from them; every relation
/// checked (`node::check`).
fn node_kat(args: &[String]) {
    let kind = match args.get(2).map(|s| s.as_str()) {
        Some("N8") | None => node::NK::N8,
        Some("N4") => node::NK::N4,
        Some("N2") => node::NK::N2,
        Some(k) => service::fatal(&format!("node-kat: kind {k}")),
    };
    // `N2`/`N4`: the previous node (`--prev FILE`, a signed node proof, e.g. `--out-signed`'s)
    let prev_signed = kind.has_prev().then(|| {
        let p = arg(args, "--prev").unwrap_or_else(|| service::fatal("node-kat N2/N4: --prev FILE"));
        format::from_file(&std::fs::read(&p).expect("read --prev")).unwrap_or_else(|| service::fatal("--prev: not a signed proof"))
    });
    // the node data: the embedded blob (plan form), or the dumps when FLOCK_NODE_DUMP is set
    let t = Instant::now();
    let nd = plan::node_data();
    let protos = nd.protos.clone();
    let texts = nd.texts.clone();
    let kt = std::sync::Arc::new(nd.kind_tab(kind));
    println!("NODE-KAT load {:.2}s", t.elapsed().as_secs_f64());
    let m: usize = arg(args, "--m").map(|x| x.parse().unwrap()).unwrap_or(32);
    let n = seg_n(args, m);
    let circ = circuit::Circuit::build();
    let gcirc = node::general_circuit();
    let o = oracle::Local::keyed(&[0x5Au8; 32]);
    let (vk, _) = format::toy_sign(9, &[0u8; 32]);
    let mut signed = Vec::new();
    for a in 0..kind.n_agg() {
        let s: Digest = std::array::from_fn(|i| i as u8 ^ (0x33 + a as u8 + 16 * kind.has_prev() as u8));
        let t = Instant::now();
        // `--agg N`: the aggregate of N steps by the split rule; else one `L{m}` segment of `n`
        let (n, pi) = match arg(args, "--agg") {
            Some(x) => {
                let na: u64 = x.parse().expect("--agg N");
                (na, agg::prove(&o, &circ, &vk, &s, na, 32).0)
            }
            None => {
                let (p, _) = leaf::prove_seg(&o, &circ, &vk, &s, m, n);
                let mut pi = vec![0u8; 48];
                pi[0] = 0x41;
                pi[1] = 1;
                pi[8..16].copy_from_slice(&n.to_le_bytes());
                pi[16..48].copy_from_slice(&blake2s::chain_end(&s, n));
                pi.extend_from_slice(&p);
                (n, pi)
            }
        };
        let e = blake2s::chain_end(&s, n);
        let c = leaf_stmt(&e, n);
        let tape = Tape(&o, std::sync::Mutex::new(Vec::new()));
        let ok = agg::verify(&tape, &circ, &vk, &c, &pi);
        let tr = tape.1.into_inner().unwrap();
        let (_, sig) = format::toy_sign(9, &format::trace_digest(&tr));
        println!("NODE-KAT aggregate {a}: k={} n={n} prove {:.2}s V_A={ok} |tr|={}", pi[1], t.elapsed().as_secs_f64(), tr.len());
        signed.push(format::Signed { pi, tr, sig });
    }
    let aggs: Vec<node::AggIn> = signed.iter().map(node::agg_in).collect();
    let t = Instant::now();
    node::warm_plans(&protos);
    println!("NODE-KAT inactive plans {:.2}s (before a request)", t.elapsed().as_secs_f64());
    let t = Instant::now();
    let base = circuit::Circuit::build_base();
    let prev_in = prev_signed.as_ref().map(|ps| {
        let pk = node::NK::of_byte(ps.pi[0]).unwrap_or_else(|| service::fatal("--prev: not a node proof"));
        let st = &ps.pi[params::field_off(params::F_STMT)..];
        let c = nodeprove::node_c(&[st[1..33].try_into().unwrap(), st[33..65].try_into().unwrap()]);
        let ctx = std::sync::Arc::new(ir::NodeCtx { k: pk, protos: protos.clone(), kt: std::sync::Arc::new(nd.kind_tab(pk)) });
        println!("NODE-KAT previous node {} |tr|={}", pk.name(), ps.tr.len());
        node::PrevIn { signed: ps, c, ix: [1, 0, 2][pk as usize], ctx, base: &base }
    });
    let w = node::witness(kind, &vk, prev_in.as_ref(), &aggs, &protos, &texts, &gcirc, &circ);
    println!("NODE-KAT witness {:.2}s {:?}", t.elapsed().as_secs_f64(), w.times);
    for (v, st) in w.mstats.iter().enumerate() {
        println!("NODE-KAT slot {v}: {st:?}");
    }
    let t = Instant::now();
    let ch = node::check(&w, &protos, &kt);
    println!("NODE-KAT check {:.2}s {ch:?} peak_rss_mb={:.0}", t.elapsed().as_secs_f64(), peak_rss_mb());
    if !args.iter().any(|a| a == "--prove") {
        return;
    }
    // the node proof, then INT-8's dumped program of the kind on it (real cells), and the canaries
    let cs: [Digest; 2] = match &prev_in {
        Some(p) => [p.c, aggs[0].c],
        None => [aggs[0].c, aggs[1].c],
    };
    let ni = nodeprove::NodeIn { k: kind, vk, cs, w: &w, mats: nodeprove::Mats { k: kind, kt: &kt, protos: &protos }, base: &base };
    let t = Instant::now();
    let (pi, tm) = nodeprove::prove(&o, &ni);
    println!("NODE-PROVE {} {:.2}s |pi|={} pi_b2s={} {} peak_rss_mb={:.0}", kind.name(), t.elapsed().as_secs_f64(), pi.len(), hexs(&blake2s::blake2s256(&pi)), tm.report(), peak_rss_mb());
    if let Some(p) = arg(args, "--out") {
        std::fs::write(&p, &pi).expect("write");
    }
    let c = nodeprove::node_c(&cs);
    let Some(d) = kat::find_ir_dump() else { service::fatal("no IR dump (FLOCK_IR_DUMP)") };
    let raw = std::fs::read_to_string(d.join(format!("ops-{}.txt", kind.name()))).expect("ops-N*.txt");
    let ph: Vec<usize> = (0..9).map(|j| kind.one_cell() + j).collect();
    let text = ir::with_cells(&raw, &ph, &kind.cells4(), params::M_STAR - 7).unwrap_or_else(|| service::fatal("the dump's cells are not the placeholders"));
    // the embedded group program at the kind's index is the dumped fixed program (INT-8 `Op.at`)
    let gtext = nd.node_program(kind);
    println!("NODE-IR proto-p0 at {} = ops-{} (real cells): {}", kind.name(), kind.name(), gtext == text);
    let ctx = std::sync::Arc::new(ir::NodeCtx { k: kind, protos: protos.clone(), kt: kt.clone() });
    let t = Instant::now();
    let tape = Tape(&o, std::sync::Mutex::new(Vec::new()));
    let r = ir::run_node(&text, ctx.clone(), &base, &tape, &vk, &c, &pi);
    let tr = tape.1.into_inner().unwrap();
    if let Some(p) = arg(args, "--out-signed") {
        // the accepted proof with its trace, signed by the test signer (a later node's `--prev`)
        let (_, sig) = format::toy_sign(9, &format::trace_digest(&tr));
        std::fs::write(&p, format::to_file(&format::Signed { pi: pi.clone(), tr, sig })).expect("write");
    }
    let st = nodeprove::stmt_ok4(&pi, &c);
    println!("NODE-IR {} ok={} stmtOk4={st} failed={:?} asks={} {:.2}s", kind.name(), r.ok, r.failed, r.asks, t.elapsed().as_secs_f64());
    // canaries: another statement; a flipped byte in the E field; the placeholder-cell program
    let mut c2 = c;
    c2[3] ^= 0x40;
    let k1 = ir::run_node(&text, ctx.clone(), &base, &o, &vk, &c2, &pi).ok && nodeprove::stmt_ok4(&pi, &c2);
    let mut p2 = pi.clone();
    p2[params::field_off(params::F_E) + 100] ^= 1;
    let k2 = ir::run_node(&text, ctx.clone(), &base, &o, &vk, &c, &p2).ok;
    let k3 = ir::run_node(&raw, ctx, &base, &o, &vk, &c, &pi).ok;
    println!("NODE-IR canaries accepted: stmt={k1} flipped_E={k2} placeholder_cells={k3}");
}

fn hexs(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn test_leaf(m: usize, n: u64, reps: usize) {
    let circ = circuit::Circuit::build();
    let o = oracle::Local::keyed(&[0x5Au8; 32]);
    let vk = [7u8; 32];
    let s: Digest = std::array::from_fn(|i| i as u8 ^ 0x33);
    let want = kat::find_items_json().and_then(|p| kat::load_items(&p));
    for rep in 0..reps {
        let t = Instant::now();
        let ((pi, tm), plog) = leaf::prove_logged(&o, &circ, &vk, &s, m, n, true);
        let pt = t.elapsed().as_secs_f64();
        let c = leaf::seg_c(&s, n);
        let t = Instant::now();
        let ok = leaf::verify(&o, &circ, &vk, &c, &pi);
        let vt = t.elapsed().as_secs_f64();
        let (_, vlog) = leaf::verify_logged(&o, &circ, &vk, &c, &pi, true);
        let kat = match &want {
            None => "skip(no items.json)".to_string(),
            Some(w) => match (kat::compare(vlog.as_deref().unwrap(), w), kat::compare_fs(plog.as_deref().unwrap(), w)) {
                (Ok(()), Ok(())) => format!("pass({} items)", w.len()),
                (Err(e), _) | (_, Err(e)) => format!("FAIL({e})"),
            },
        };
        let mut c2 = c;
        c2[0] ^= 1;
        let bad1 = leaf::verify(&o, &circ, &vk, &c2, &pi);
        // the dumped Lean program (with the finals) on the same proof, for the Lean kinds
        // the dumped Lean segment program of the kind (S-F4, revision 4.1) on the same proof; the
        // canaries: the flipped statement and the statement of `n + 1` (same end)
        let ir = match (m, kat::find_ir_dump()) {
            (30..=32, Some(d)) => {
                let text = std::fs::read_to_string(d.join(format!("ops-L{m}.txt"))).unwrap_or_default();
                let r = ir::run(&text, &circ, &o, &vk, &c, &pi);
                let c3 = leaf_stmt(&blake2s::chain_end(&s, n), n + 1);
                let canary = ir::run(&text, &circ, &o, &vk, &c2, &pi).ok || ir::run(&text, &circ, &o, &vk, &c3, &pi).ok;
                format!("{}(lines {:?}; canary_accept={}; asks={})", if r.ok { "accept" } else { "REJECT" }, r.failed, canary, r.asks)
            }
            _ => "skip".to_string(),
        };
        let mut bad2 = false;
        for frac in [7usize, 3, 2] {
            let mut pi2 = pi.clone();
            let k = pi.len() / frac;
            pi2[k] ^= 4;
            bad2 |= leaf::verify(&o, &circ, &vk, &c, &pi2);
        }
        println!(
            "TEST-LEAF m={m} rep={rep} n={n} |pi|={} pi_b2s={} piSize={} prove_s={pt:.3} verify_s={vt:.3} accept={ok} flipped_stmt_accept={bad1} flipped_byte_accept={bad2} items_kat={kat} lean_ir={ir} peak_rss_mb={:.0} threads={} tier={} {}",
            pi.len(),
            blake2s::blake2s256(&pi).iter().map(|x| format!("{x:02x}")).collect::<String>(),
            params::PI_SIZE,
            peak_rss_mb(),
            par::threads(),
            simd::tier_name(),
            tm.report()
        );
        if !ok || bad1 || bad2 || pi.len() != params::PI_SIZE || kat.starts_with("FAIL") || ir.starts_with("REJECT") || ir.contains("canary_accept=true") {
            eprintln!("test-leaf: FAIL");
            std::process::exit(1);
        }
    }
}

fn prove_leaf_service(m: usize, n: u64, start: &Digest, out: &str, reps: usize) {
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    svc.warm(par::threads().min(service::MAX_CONNS));
    par::warm();
    let vk = svc.vk();
    let circ = circuit::Circuit::build();
    let pf: usize = std::env::var("FLOCK_PREFAULT_MIB").ok().and_then(|x| x.parse().ok()).unwrap_or(0);
    if pf > 0 {
        let t = Instant::now();
        alloc::prefault(pf << 20);
        eprintln!("prefault {pf} MiB {:.3}s", t.elapsed().as_secs_f64());
    }
    if std::env::var_os("FLOCK_NODE_SHAPE").is_some() {
        let _ = nodeshape::preload();
    }
    for rep in 0..reps {
        let t0 = Instant::now();
        let mut rec = Recorder::new(&svc);
        rec.batch_max = 128;
        let (pi, tm) = leaf::prove_seg(&rec, &circ, &vk, start, m, n);
        let t_prove = t0.elapsed().as_secs_f64();
        let prof_s = prof::report();
        let stats = rec.stats.report();
        let oracle_s = rec.stats.oracle_s();
        let t = Instant::now();
        let table = rec.into_table();
        let h = blake2s::chain_end(start, n);
        let c = leaf_stmt(&h, n);
        let mut rp = Replay::new(&table);
        rp.fallback = Some(&svc);
        if !leaf::verify(&rp, &circ, &vk, &c, &pi) {
            service::fatal("the native verifier rejects the proof (replay)");
        }
        let (tr, missing) = rp.finish();
        if missing != 0 {
            service::fatal(&format!("{missing} verifier queries were not asked while proving"));
        }
        let t_trace = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
        let (answers, sig) = svc.sign(&qs);
        if answers.iter().zip(tr.iter()).any(|(a, (_, b))| a != b) {
            service::fatal("SIGN answers differ from the QUERY answers");
        }
        let t_sign = t.elapsed().as_secs_f64();
        let total = t0.elapsed().as_secs_f64();
        let file = format::to_file(&format::Signed { pi: pi.clone(), tr: tr.clone(), sig });
        std::fs::write(out, &file).expect("write");
        let t = Instant::now();
        let r = acc_with(Top::Seg, &circ, &vk, &c, &file);
        let t_acc = t.elapsed().as_secs_f64();
        // the dumped Lean segment program on the file's trace (`runSeq`), when the dumps are found
        let lean = match lean_dir() {
            Some(d) => {
                let p = format::from_file(&file).unwrap();
                let text = std::fs::read_to_string(d.join(format!("ops-L{m}.txt"))).unwrap_or_default();
                let seq = Seq::new(&p.tr);
                let ok = ir::run(&text, &circ, &seq, &vk, &c, &p.pi).ok && seq.consumed();
                if ok { "accept" } else { "REJECT" }
            }
            None => "skip",
        };
        let qbytes: usize = tr.iter().map(|(q, _)| q.len()).sum();
        let mut c2 = c;
        c2[31] ^= 1;
        let canary = acc_with(Top::Seg, &circ, &vk, &c2, &file).is_ok();
        // the trace against A.4: |tr| = 8,905 (`seq4`) and every query length as `items.json` lists it
        let tr_kat = match kat::find_items_json().and_then(|p| kat::load_items(&p)) {
            None => "skip(no items.json)".to_string(),
            Some(w) => {
                let bad = tr.iter().zip(w.iter()).position(|((q, _), it)| q.len() != kat::qlen_of(it));
                match (tr.len() == w.len(), bad) {
                    (true, None) => format!("pass({} items, qlens equal)", w.len()),
                    (_, Some(i)) => format!("FAIL(item {i}: qlen {} vs {})", tr[i].0.len(), kat::qlen_of(&w[i])),
                    (false, None) => format!("FAIL(|tr| {} vs {})", tr.len(), w.len()),
                }
            }
        };
        let reasm = items::reassemble(&tr).as_deref() == Some(&pi[..]);
        println!(
            "PROVE-LEAF m={m} rep={rep} n={n} trace_kat={tr_kat} reassemble_eq_pi={reasm} total_s={total:.3} prove_s={t_prove:.3} trace_s={t_trace:.3} sign_s={t_sign:.3} oracle_s={oracle_s:.3} \
             compressions_per_s={:.0} |pi|={} |tr|={} trace_query_bytes={qbytes} file={} acc={} acc_s={t_acc:.3} lean_seg={lean} canary_accept={canary} peak_rss_mb={:.0} threads={} tier={} | {} | {stats} | {}{}",
            n as f64 / total,
            pi.len(),
            tr.len(),
            file.len(),
            r.as_ref().map(|_| "accept".to_string()).unwrap_or_else(|e| e.clone()),
            peak_rss_mb(),
            par::threads(),
            simd::tier_name(),
            tm.report(),
            svc.report(),
            if prof_s.is_empty() { String::new() } else { format!(" | prof {prof_s}") }
        );
        if r.is_err() || canary || !reasm || tr_kat.starts_with("FAIL") || pi.len() != params::PI_SIZE || lean == "REJECT" {
            std::process::exit(1);
        }
    }
}

/// `prove-agg N`: the aggregate leaf of a chain of `N` steps through the service (one trace, one
/// `SIGN`), the native `acc` on the file and the statement canary; per-segment times.
fn prove_agg_service(n: u64, start: &Digest, out: &str, reps: usize) {
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    svc.warm(par::threads().min(service::MAX_CONNS));
    par::warm();
    let vk = svc.vk();
    let circ = circuit::Circuit::build();
    let pf: usize = std::env::var("FLOCK_PREFAULT_MIB").ok().and_then(|x| x.parse().ok()).unwrap_or(0);
    if pf > 0 {
        let t = Instant::now();
        alloc::prefault(pf << 20);
        eprintln!("prefault {pf} MiB {:.3}s", t.elapsed().as_secs_f64());
    }
    let c = leaf::seg_c(start, n);
    for rep in 0..reps {
        let t0 = Instant::now();
        let mut rec = Recorder::new(&svc);
        rec.batch_max = 128;
        let (pi, tms) = agg::prove(&rec, &circ, &vk, start, n, agg::M_SEG);
        let t_prove = t0.elapsed().as_secs_f64();
        let t = Instant::now();
        let table = rec.into_table();
        let mut rp = Replay::new(&table);
        rp.fallback = Some(&svc);
        if !agg::verify(&rp, &circ, &vk, &c, &pi) {
            service::fatal("the native verifier rejects the aggregate (replay)");
        }
        let (tr, missing) = rp.finish();
        if missing != 0 {
            service::fatal(&format!("{missing} verifier queries were not asked while proving"));
        }
        let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
        let (_, sig) = svc.sign(&qs);
        let t_trace_sign = t.elapsed().as_secs_f64();
        let total = t0.elapsed().as_secs_f64();
        let file = format::to_file(&format::Signed { pi: pi.clone(), tr: tr.clone(), sig });
        std::fs::write(out, &file).expect("write");
        let r = acc(&circ, &vk, &c, &file);
        let mut c2 = c;
        c2[31] ^= 1;
        let canary = acc(&circ, &vk, &c2, &file).is_ok();
        // `V4with` with `V_A` over the dumped Lean segment programs (`ir::run_agg`), and its canary
        let t = Instant::now();
        let lean = match lean_dir() {
            Some(d) => {
                let a = acc_with(Top::Lean(d), &circ, &vk, &c, &file);
                let cn = acc_with(Top::Lean(d), &circ, &vk, &c2, &file).is_ok();
                format!("{}{}", a.map(|_| "accept".to_string()).unwrap_or_else(|e| format!("REJECT({e})")), if cn { ",CANARY_ACCEPTED" } else { "" })
            }
            None => "skip".into(),
        };
        let t_lean = t.elapsed().as_secs_f64();
        let segs: Vec<String> = agg::split(n, agg::M_SEG).iter().zip(tms.iter()).map(|((m, ni), tm)| format!("L{m}:{ni}:{:.3}", tm.total())).collect();
        println!(
            "PROVE-AGG n={n} rep={rep} k={} segs=[{}] total_s={total:.3} prove_s={t_prove:.3} trace_sign_s={t_trace_sign:.3} |pi|={} |tr|={} file={} acc={} lean_acc={lean} lean_s={t_lean:.2} canary_accept={canary} peak_rss_mb={:.0} threads={} tier={}",
            tms.len(),
            segs.join(","),
            pi.len(),
            tr.len(),
            file.len(),
            r.as_ref().map(|_| "accept".to_string()).unwrap_or_else(|e| e.clone()),
            peak_rss_mb(),
            par::threads(),
            simd::tier_name(),
        );
        if r.is_err() || canary || lean.contains("REJECT") || lean.contains("CANARY") {
            std::process::exit(1);
        }
    }
}

extern "C" {
    /// glibc's `mallopt` (the prover is linked with glibc, `-static`).
    fn mallopt(param: i32, value: i32) -> i32;
}

/// Keep small freed memory in one arena (glibc) and pre-fault `mib` MiB for the large-block cache
/// (`alloc.rs`), before the request's clock.
pub(crate) fn heap_setup(mib: usize) {
    // SAFETY: plain glibc calls (M_ARENA_MAX = -8, M_TRIM_THRESHOLD = -1); a refused setting is
    // only slower.
    unsafe {
        mallopt(-8, 1);
        mallopt(-1, i32::MAX);
    }
    alloc::prefault(mib << 20);
}

pub(crate) fn say(word: &str) {
    use std::io::Write;
    let mut out = std::io::stdout().lock();
    let _ = writeln!(out, "{word}");
    let _ = out.flush();
}

pub(crate) fn wait_go() {
    let mut line = String::new();
    loop {
        line.clear();
        if std::io::stdin().read_line(&mut line).unwrap_or(0) == 0 {
            service::fatal("stdin closed before `go`");
        }
        if line.trim() == "go" {
            return;
        }
    }
}

/// Prefault size per shape (peak RSS measured in P1 plus margin).
fn prefault_mib(m: usize) -> usize {
    if m >= 32 {
        6000
    } else {
        1800
    }
}

/// A signed leaf through the service: prove, the verifier's trace by replay, SIGN; the file bytes.
fn leaf_file(svc: &service::Service, circ: &circuit::Circuit, vk: &Digest, s: &Digest, m: usize) -> Vec<u8> {
    let mut rec = Recorder::new(svc);
    rec.batch_max = 128; // column queries are asked again by the replay (≈ 750 of them)
    let (pi, _) = leaf::prove(&rec, circ, vk, s, m);
    let table = rec.into_table();
    let n = params::leaf_n(m);
    let c = leaf_stmt(&blake2s::chain_end(s, n), n);
    let mut rp = Replay::new(&table);
    rp.fallback = Some(svc);
    if !leaf::verify(&rp, circ, vk, &c, &pi) {
        service::fatal("the native verifier rejects the proof (replay)");
    }
    let (tr, missing) = rp.finish();
    if missing != 0 {
        service::fatal(&format!("{missing} verifier queries were not asked while proving"));
    }
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (_, sig) = svc.sign(&qs);
    format::to_file(&format::Signed { pi, tr, sig })
}

/// `prover leaf /work` (PROVER.md §3): `leaf.json` = `{"n": N, "start": "HEX"}`, `n ∈ {2^16, 2^18}`.
fn cmd_leaf(dir: &std::path::Path) {
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    svc.warm(par::threads().min(service::WARM_CONNS));
    par::warm();
    let circ = circuit::Circuit::build();
    let vk = unhex(&std::fs::read_to_string(dir.join("vk.hex")).unwrap_or_else(|e| service::fatal(&format!("vk.hex: {e}"))));
    heap_setup(prefault_mib(30));
    let _ = skipdom::skip();
    say("ready");
    wait_go();
    let t = Instant::now();
    let j = std::fs::read_to_string(dir.join("leaf.json")).unwrap_or_else(|e| service::fatal(&format!("leaf.json: {e}")));
    let num = |k: &str| -> String {
        let i = j.find(&format!("\"{k}\"")).unwrap_or_else(|| service::fatal(&format!("leaf.json: no {k}")));
        let rest = &j[i + k.len() + 2..];
        let rest = rest[rest.find(':').unwrap() + 1..].trim_start();
        rest.chars().take_while(|c| c.is_ascii_hexdigit() || *c == '"').filter(|c| *c != '"').collect()
    };
    let n: u64 = num("n").parse().unwrap_or_else(|_| service::fatal("leaf.json: n"));
    let s = unhex(&num("start"));
    if !n.is_power_of_two() || !(1u64 << 11..=1u64 << 18).contains(&n) {
        service::fatal(&format!("leaf n = {n}: this prover proves n = 2^11 … 2^18 (m = 25 … 32)"));
    }
    let m = 14 + n.trailing_zeros() as usize;
    let f = leaf_file(&svc, &circ, &vk, &s, m);
    std::fs::write(dir.join("proof.bin"), &f).unwrap_or_else(|e| service::fatal(&format!("proof.bin: {e}")));
    say("done");
    eprintln!("leaf request m={m} {:.3}s file={} {}", t.elapsed().as_secs_f64(), f.len(), svc.report());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    simd::tier();
    let mode = args.get(1).map(String::as_str).unwrap_or("");
    let reps: usize = arg(&args, "--reps").and_then(|x| x.parse().ok()).unwrap_or(1);
    match mode {
        "setup" => {}
        "vk" => {
            let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
            let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
            println!("{}", svc.vk().iter().map(|x| format!("{x:02x}")).collect::<String>());
        }
        "leaf" => cmd_leaf(std::path::Path::new(args.get(2).map(String::as_str).unwrap_or("."))),
        "tree" | "node" => {
            eprintln!("flock-prover {mode}: the node prover is not built yet (stage P2 waits for S-0's compileMux dump)");
            std::process::exit(2);
        }
        "bench" => bench::run(),
        "bench-rs" => bench::run_rs(args.get(2).and_then(|x| x.parse().ok()).unwrap_or(32)),
        "selftest" => match simd::selftest() {
            Ok(s) => println!("SELFTEST pass {s}"),
            Err(e) => {
                println!("SELFTEST FAIL {e}");
                std::process::exit(1);
            }
        },
        "mfill-kat" => mfill_kat(&args),
        "node-kat" => node_kat(&args),
        "first" | "step" => stream::run(args[1] == "first", std::path::Path::new(args.get(2).map(|s| s.as_str()).unwrap_or("."))),
        "plan-build" => {
            // the node blob from the dumps (FLOCK_NODE_DUMP, FLOCK_PROTO_DIR, FLOCK_IR_DUMP)
            let (dd, _) = mfill::find_dirs().unwrap_or_else(|| service::fatal("no node dump"));
            let t = Instant::now();
            let (b64, rep) = plan::build_blob(&dd);
            let out = arg(&args, "--out").unwrap_or_else(|| "nodeblob.b64".into());
            std::fs::write(&out, &b64).expect("write");
            print!("{rep}");
            println!("PLAN-BUILD {} B to {out} in {:.1}s (from {})", b64.len(), t.elapsed().as_secs_f64(), dd.display());
        }
        "plan-kat" => {
            // the embedded blob's rebuild against the full dump
            let t = Instant::now();
            let nd = plan::decode_blob(plan::BLOB);
            let dt = t.elapsed().as_secs_f64();
            let (dd, pd) = mfill::find_dirs().unwrap_or_else(|| service::fatal("no node dump"));
            let mut ok = true;
            for pi in 0..2 {
                let p = mfill::Proto::load(&dd, pi);
                let r = plan::proto_eq(&nd.protos[pi], &p);
                println!("PLAN-KAT p{pi}: rows {} terms {} regs {} aux {}: {:?}", p.rows.len(), p.rows.cells.len(), p.regs.len(), p.aux.len(), r);
                ok &= r.is_ok();
                let tx = std::fs::read_to_string(pd.join(format!("proto-p{pi}.txt"))).unwrap_or_default();
                println!("PLAN-KAT proto-p{pi}.txt equal: {}", tx == nd.texts[pi]);
                ok &= tx == nd.texts[pi];
            }
            for (i, k) in ["N2", "N4", "N8"].iter().enumerate() {
                let tx = std::fs::read_to_string(dd.join(format!("node-{k}.txt"))).unwrap_or_default();
                ok &= tx == nd.kinds[i];
            }
            println!("PLAN-KAT decode {dt:.2}s (blob {} B) all equal: {ok}", plan::BLOB.len());
            if !ok {
                std::process::exit(1);
            }
        }
        "test-leaf" => {
            let m: usize = args[2].parse().expect("M");
            test_leaf(m, seg_n(&args, m), reps)
        }
        "prove-leaf" => {
            let m: usize = args[2].parse().expect("M");
            let n = seg_n(&args, m);
            let start = unhex(&arg(&args, "--start").unwrap_or_else(|| "11".repeat(32)));
            let out = arg(&args, "--out").unwrap_or_else(|| "leaf.bin".into());
            prove_leaf_service(m, n, &start, &out, reps);
        }
        "prove-agg" => {
            let n: u64 = args[2].parse().expect("N");
            let start = unhex(&arg(&args, "--start").unwrap_or_else(|| "11".repeat(32)));
            let out = arg(&args, "--out").unwrap_or_else(|| "agg.bin".into());
            prove_agg_service(n, &start, &out, reps);
        }
        "acc" => {
            let vk = unhex(&arg(&args, "--vk").expect("--vk"));
            let c = unhex(&arg(&args, "--stmt").expect("--stmt"));
            let f = std::fs::read(args.last().unwrap()).expect("read");
            let circ = circuit::Circuit::build();
            let top = match (args.iter().any(|a| a == "--lean").then_some(()), lean_dir()) {
                (Some(_), Some(d)) => Top::Lean(d),
                (Some(_), None) => service::fatal("--lean: no dump found (FLOCK_IR_DUMP)"),
                _ if args.iter().any(|a| a == "--seg") => Top::Seg,
                _ => Top::V4,
            };
            match acc_with(top, &circ, &vk, &c, &f) {
                Ok(()) => println!("accept"),
                Err(e) => {
                    println!("reject: {e}");
                    std::process::exit(1);
                }
            }
        }
        _ => {
            eprintln!("usage: flock-prover selftest | test-leaf M | prove-leaf M --start HEX --out FILE | acc --vk HEX --stmt HEX FILE");
            std::process::exit(2);
        }
    }
}
