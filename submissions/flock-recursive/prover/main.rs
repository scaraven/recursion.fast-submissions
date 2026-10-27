//! `flock-prover`: the native prover of the `flock-recursive` entry (stage P1: the prover core).
//!
//! Modes (development; the runner's `setup`/`tree`/`leaf`/`node` are stage P2):
//!   flock-prover selftest                         tier kernels against the reference
//!   flock-prover test-leaf M [--reps R]           prove + native verify, in-process keyed oracle
//!   flock-prover prove-leaf M --start HEX --out FILE [--reps R]
//!                                                 through the service at $RF_ORACLE: prove, record
//!                                                 the verifier's trace, SIGN, write the signed file,
//!                                                 check it with the native `acc`
//!   flock-prover acc --vk HEX --stmt HEX FILE     the native `acc` on a signed-proof file
//! Environment: FLOCK_THREADS (default all CPUs), FLOCK_TIER (force `portable`, `pclmul`, `ymm`).
#![allow(clippy::needless_range_loop, clippy::too_many_arguments, dead_code)]

mod alloc;
mod blake2s;
mod circuit;
mod field;
mod format;
mod items;
mod kat;
mod leaf;
mod ligerito;
mod lincheck;
mod merkle;
mod mle;
mod ntt;
mod oracle;
mod par;
mod params;
mod ringswitch;
mod service;
mod simd;
mod skipdom;
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

fn peak_rss_mb() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    for l in s.lines() {
        if let Some(v) = l.strip_prefix("VmHWM:") {
            let kb: f64 = v.trim().trim_end_matches("kB").trim().parse().unwrap_or(0.0);
            return kb / 1024.0;
        }
    }
    0.0
}

/// The native `acc vk c p` (FORMAT.md): caps, the signature on the trace digest, and `V` run
/// against the trace (`runSeq`).
pub fn acc(circ: &circuit::Circuit, vk: &Digest, c: &Digest, file: &[u8]) -> Result<(), String> {
    let p = format::from_file(file).ok_or("not a signed-proof file")?;
    if p.pi.len() > format::PROOF_CAP {
        return Err(format!("|π| = {} > proofCap", p.pi.len()));
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
    if !leaf::verify(&seq, circ, vk, c, &p.pi) {
        return Err("V rejects".into());
    }
    if !seq.consumed() {
        return Err("V did not ask exactly the trace's queries".into());
    }
    Ok(())
}

fn test_leaf(m: usize, reps: usize) {
    let circ = circuit::Circuit::build();
    let o = oracle::Local::keyed(&[0x5Au8; 32]);
    let vk = [7u8; 32];
    let s: Digest = std::array::from_fn(|i| i as u8 ^ 0x33);
    let want = kat::find_items_json().and_then(|p| kat::load_items(&p));
    for rep in 0..reps {
        let t = Instant::now();
        let ((pi, tm), plog) = leaf::prove_logged(&o, &circ, &vk, &s, m, true);
        let pt = t.elapsed().as_secs_f64();
        let n = params::leaf_n(m);
        let c = leaf::leaf_c(&s, m);
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
        let mut bad2 = false;
        for frac in [7usize, 3, 2] {
            let mut pi2 = pi.clone();
            let k = pi.len() / frac;
            pi2[k] ^= 4;
            bad2 |= leaf::verify(&o, &circ, &vk, &c, &pi2);
        }
        println!(
            "TEST-LEAF m={m} rep={rep} n={n} |pi|={} piSize={} prove_s={pt:.3} verify_s={vt:.3} accept={ok} flipped_stmt_accept={bad1} flipped_byte_accept={bad2} items_kat={kat} peak_rss_mb={:.0} threads={} tier={} {}",
            pi.len(),
            params::PI_SIZE,
            peak_rss_mb(),
            par::threads(),
            simd::tier_name(),
            tm.report()
        );
        if !ok || bad1 || bad2 || pi.len() != params::PI_SIZE || kat.starts_with("FAIL") {
            eprintln!("test-leaf: FAIL");
            std::process::exit(1);
        }
    }
}

fn prove_leaf_service(m: usize, start: &Digest, out: &str, reps: usize) {
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    svc.warm(par::threads().min(service::MAX_CONNS));
    par::warm();
    let vk = svc.vk();
    let circ = circuit::Circuit::build();
    let n = params::leaf_n(m);
    if let Some(u) = std::env::var("FLOCK_USED_BLOCKS").ok().and_then(|x| x.parse().ok()) {
        par::USED_BLOCKS.store(u, std::sync::atomic::Ordering::Relaxed);
    }
    let timing_only = par::used_blocks() < params::leaf_n(m) as usize;
    let pf: usize = std::env::var("FLOCK_PREFAULT_MIB").ok().and_then(|x| x.parse().ok()).unwrap_or(0);
    if pf > 0 {
        let t = Instant::now();
        alloc::prefault(pf << 20);
        eprintln!("prefault {pf} MiB {:.3}s", t.elapsed().as_secs_f64());
    }
    for rep in 0..reps {
        let t0 = Instant::now();
        let mut rec = Recorder::new(&svc);
        rec.batch_max = 128;
        let (pi, tm) = leaf::prove(&rec, &circ, &vk, start, m);
        let t_prove = t0.elapsed().as_secs_f64();
        let stats = rec.stats.report();
        let oracle_s = rec.stats.oracle_s();
        let t = Instant::now();
        let table = rec.into_table();
        let h = blake2s::chain_end(start, n);
        let c = leaf_stmt(&h, n);
        let mut rp = Replay::new(&table);
        rp.fallback = Some(&svc);
        if !leaf::verify(&rp, &circ, &vk, &c, &pi) && !timing_only {
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
        let r = acc(&circ, &vk, &c, &file);
        let t_acc = t.elapsed().as_secs_f64();
        let qbytes: usize = tr.iter().map(|(q, _)| q.len()).sum();
        let mut c2 = c;
        c2[31] ^= 1;
        let canary = acc(&circ, &vk, &c2, &file).is_ok();
        // the trace against A.4: |tr| = 8,874 and every query length as `items.json` lists it
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
             compressions_per_s={:.0} |pi|={} |tr|={} trace_query_bytes={qbytes} file={} acc={} acc_s={t_acc:.3} canary_accept={canary} peak_rss_mb={:.0} threads={} tier={} | {} | {stats} | {}",
            n as f64 / total,
            pi.len(),
            tr.len(),
            file.len(),
            r.as_ref().map(|_| "accept".to_string()).unwrap_or_else(|e| e.clone()),
            peak_rss_mb(),
            par::threads(),
            simd::tier_name(),
            tm.report(),
            svc.report()
        );
        if (r.is_err() || canary || !reasm || tr_kat.starts_with("FAIL") || pi.len() != params::PI_SIZE) && !timing_only {
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
fn heap_setup(mib: usize) {
    // SAFETY: plain glibc calls (M_ARENA_MAX = -8, M_TRIM_THRESHOLD = -1); a refused setting is
    // only slower.
    unsafe {
        mallopt(-8, 1);
        mallopt(-1, i32::MAX);
    }
    alloc::prefault(mib << 20);
}

fn say(word: &str) {
    use std::io::Write;
    let mut out = std::io::stdout().lock();
    let _ = writeln!(out, "{word}");
    let _ = out.flush();
}

fn wait_go() {
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
        "selftest" => match simd::selftest() {
            Ok(s) => println!("SELFTEST pass {s}"),
            Err(e) => {
                println!("SELFTEST FAIL {e}");
                std::process::exit(1);
            }
        },
        "test-leaf" => test_leaf(args[2].parse().expect("M"), reps),
        "prove-leaf" => {
            let m: usize = args[2].parse().expect("M");
            let start = unhex(&arg(&args, "--start").unwrap_or_else(|| "11".repeat(32)));
            let out = arg(&args, "--out").unwrap_or_else(|| "leaf.bin".into());
            prove_leaf_service(m, &start, &out, reps);
        }
        "acc" => {
            let vk = unhex(&arg(&args, "--vk").expect("--vk"));
            let c = unhex(&arg(&args, "--stmt").expect("--stmt"));
            let f = std::fs::read(args.last().unwrap()).expect("read");
            let circ = circuit::Circuit::build();
            match acc(&circ, &vk, &c, &f) {
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
