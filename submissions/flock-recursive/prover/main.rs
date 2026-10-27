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

mod blake2s;
mod circuit;
mod field;
mod format;
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
    if leaf::verify(&seq, circ, vk, c, &p.pi).is_none() {
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
    for rep in 0..reps {
        let t = Instant::now();
        let (pi, tm) = leaf::prove(&o, &circ, &vk, &s, m);
        let pt = t.elapsed().as_secs_f64();
        let n = params::leaf_n(m);
        let h = blake2s::chain_end(&s, n);
        let c = leaf_stmt(&h, n);
        let t = Instant::now();
        let ok = leaf::verify(&o, &circ, &vk, &c, &pi).is_some();
        let vt = t.elapsed().as_secs_f64();
        let mut c2 = c;
        c2[0] ^= 1;
        let bad1 = leaf::verify(&o, &circ, &vk, &c2, &pi).is_some();
        let mut bad2 = false;
        for frac in [7usize, 3, 2] {
            let mut pi2 = pi.clone();
            let k = pi.len() / frac;
            pi2[k] ^= 4;
            bad2 |= leaf::verify(&o, &circ, &vk, &c, &pi2).is_some();
        }
        println!(
            "TEST-LEAF m={m} rep={rep} n={n} |pi|={} prove_s={pt:.3} verify_s={vt:.3} accept={ok} flipped_stmt_accept={bad1} flipped_byte_accept={bad2} threads={} tier={} {}",
            pi.len(),
            par::threads(),
            simd::tier_name(),
            tm.report()
        );
        if !ok || bad1 || bad2 {
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
    for rep in 0..reps {
        let t0 = Instant::now();
        let rec = Recorder::new(&svc);
        let (pi, tm) = leaf::prove(&rec, &circ, &vk, start, m);
        let t_prove = t0.elapsed().as_secs_f64();
        let stats = rec.stats.report();
        let oracle_s = rec.stats.oracle_s();
        let t = Instant::now();
        let table = rec.into_table();
        let h = blake2s::chain_end(start, n);
        let c = leaf_stmt(&h, n);
        let rp = Replay::new(&table);
        if leaf::verify(&rp, &circ, &vk, &c, &pi).is_none() {
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
        println!(
            "PROVE-LEAF m={m} rep={rep} n={n} total_s={total:.3} prove_s={t_prove:.3} trace_s={t_trace:.3} sign_s={t_sign:.3} oracle_s={oracle_s:.3} \
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
        if r.is_err() || canary {
            std::process::exit(1);
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    simd::tier();
    let mode = args.get(1).map(String::as_str).unwrap_or("");
    let reps: usize = arg(&args, "--reps").and_then(|x| x.parse().ok()).unwrap_or(1);
    match mode {
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
