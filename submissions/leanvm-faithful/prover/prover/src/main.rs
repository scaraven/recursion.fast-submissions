//! `lvm6-prover`: the v6 prover binary of the lvm6 entry (scaffold, stage P1).
//!
//! The submitted program is several builds of this crate, one per CPU tier (`build-asm.sh`), each with its
//! symbols suffixed, behind season 1's `cpuid` stub (`dispatch.s`), which calls the tier's `lvm_main_<v>`.
//!
//! Modes:
//!   lvm6-prover setup DIR              PROVER.md §3 (untimed): the CPU self-test of every tier, cap in DIR/lvm-cpu (`setup.rs`)
//!   lvm6-prover selftest               one tier's self-test (setup's child; `LVM_CPU` forced)
//!   lvm6-prover first DIR | step DIR   the stream (PROVER.md §3, FORMAT6 §8; `stream.rs`): handshake, the two
//!                                      SIGNs, the W proof (default; the fallback for n ≠ 2^18) or the SNARK skeleton
//!   lvm6-prover smoke [N_LOG] [DEPTH] [SEED]
//!                                      leanVM's Keccak GKR batch of 2^N_LOG permutations (default 16, depth 12),
//!                                      proved and natively verified (`smoke.rs`); prints the proof's Keccak-256
//!   lvm6-prover smoke6 [N_LOG] [DEPTH] [SEED]
//!                                      the same flow on the v6 seams (hash chain, oracle Merkle with caps) over a
//!                                      fixed-key local oracle; prints Keccak-256 of BODY and of the trace
//!   lvm6-prover kat | kat prf KEYHEX   known-answer tests (`kat.rs`)
//!   lvm6-prover tree6 LOG_BLOCKS OUT [SEED] [TAMPER]
//!                                      WP-R2 (dev): HDR, §6.1, the tree batch §6.2, §6.5's group (`tree6.rs`)
//!   lvm6-prover full6 OUT [SEED] [PARTS] [check,node]
//!                                      WP-R3 (dev): a complete leaf-mode proof at P18 (`full6.rs`)
//!   lvm6-prover info                   the tier, the pool size and the embedded Q's identity
//!   lvm6-prover qpack BLOB OUT         R8 (dev): the text blob BLOB, loaded and checked, in the compact form
//!                                      (`r3typed::qbin`) that `build-asm.sh --q OUT` embeds
//!   lvm6-prover svcbench [GS] [LS] [--local]  WP-R0: one step's service-run oracle traffic, timed (`svcbench.rs`)
//! Environment: LVM_THREADS (the pool's size; default leanVM's: the physical cores), LVM_CPU (dispatch.s: force a
//! tier), LVM6_PI (w | skel, `stream.rs`), LVM6_PRF_KAT=0, LVM6_CONNS (oracle connections; default max(8, pool)).
#![no_main]
#![allow(dead_code)]

mod format;
mod kat;
mod keccak;
mod oracle;
mod service;
mod smoke;
mod stream;
mod svcbench;
mod tree6;
mod full6;
mod prove6;
mod setup;

use std::ffi::{CStr, c_char, c_int};
use std::io::Write;

/// The CPU tier this build is (`build-asm.sh` sets `LVM_VARIANT` at compile time).
pub const VARIANT: &str = match option_env!("LVM_VARIANT") {
    Some(v) => v,
    None => "native-build",
};

fn run(args: Vec<String>) -> i32 {
    if let Some(k) = std::env::var("LVM_THREADS").ok().and_then(|v| v.parse::<usize>().ok()) {
        parallel::set_num_threads(k);
    }
    match args.get(1).map(String::as_str) {
        Some("info") => {
            let q = r3typed::qbin::embedded_id().map_or("none (LVM6_Q_BLOB or the stub)".to_string(), |id| stream::hex(&id));
            println!("lvm6-prover tier {VARIANT} threads {} embedded Q {q}", parallel::num_threads());
            0
        }
        Some("kat") => match args.get(2).map(String::as_str) {
            Some("prf") => kat::run_prf(args.get(3).map_or("", String::as_str)),
            _ => kat::run_all(),
        },
        Some("smoke") => {
            let n_log: usize = args.get(2).map_or(16, |v| v.parse().expect("N_LOG"));
            let depth: usize = args.get(3).map_or(12, |v| v.parse().expect("DEPTH"));
            let seed: u64 = args.get(4).map_or(1, |v| v.parse().expect("SEED"));
            parallel::init();
            let r = smoke::run(n_log, depth, seed);
            let [w, c, o, g, op, pass] = r.stages;
            println!(
                "smoke tier {VARIANT} threads {} n 2^{n_log} depth {depth}: verified {} |proof| {} B keccak {} | \
                 witness {w:.3} commit {c:.3} output {o:.3} gkr {g:.3} open {op:.3} prove {pass:.3} s verify {:.4} s",
                parallel::num_threads(),
                r.verified,
                r.proof.len(),
                stream::hex(&keccak::keccak256(&r.proof)),
                r.verify_s
            );
            i32::from(!r.verified)
        }
        Some("smoke6") => {
            let n_log: usize = args.get(2).map_or(14, |v| v.parse().expect("N_LOG"));
            let depth: usize = args.get(3).map_or(12, |v| v.parse().expect("DEPTH"));
            let seed: u64 = args.get(4).map_or(1, |v| v.parse().expect("SEED"));
            parallel::init();
            oracle::install(Box::new(oracle::Local::keyed(&[0x5A; 32])));
            let r = smoke::run_v6(n_log, depth, seed);
            let [w, c, o, g, op, pass] = r.stages;
            let mut tb = Vec::new();
            for (q, a) in &r.trace {
                tb.extend_from_slice(&(q.len() as u64).to_le_bytes());
                tb.extend_from_slice(q);
                tb.extend_from_slice(a);
            }
            println!(
                "smoke6 tier {VARIANT} threads {} conns {} n 2^{n_log} depth {depth} frozen-whir {}: |BODY| {} B keccak {} \
                 trace {} keccak {} | witness {w:.3} commit {c:.3} output {o:.3} gkr {g:.3} open {op:.3} prove {pass:.3} s; {}",
                parallel::num_threads(),
                fs6::oracle::conns(),
                r.frozen,
                r.body.len(),
                stream::hex(&keccak::keccak256(&r.body)),
                r.trace.len(),
                stream::hex(&keccak::keccak256(&tb)),
                oracle::report()
            );
            0
        }
        Some("svcbench") => svcbench::run(&args),
        Some("tree6") => tree6::run(&args),
        Some("full6") => full6::run(&args),
        Some("setup") => setup::setup(&args.get(2).cloned().unwrap_or_else(|| "/setup".into())),
        Some("selftest") => setup::selftest(),
        Some("qpack") => qpack(&args),
        Some(m @ ("first" | "step")) => stream::run(m, args.get(2).map_or("/work", String::as_str)),
        _ => {
            eprintln!("usage: lvm6-prover setup DIR | first DIR | step DIR | smoke [N_LOG] [DEPTH] [SEED] | kat [prf KEYHEX] | info");
            2
        }
    }
}

/// `qpack BLOB OUT` (R8, dev): the compact form of the text blob (its identity: the blob's Keccak-256), checked to
/// decode to the same circuit in both forms.
fn qpack(args: &[String]) -> i32 {
    let (Some(blob), Some(out)) = (args.get(2), args.get(3)) else {
        eprintln!("usage: lvm6-prover qpack BLOB OUT");
        return 2;
    };
    let text = std::fs::read(blob).unwrap_or_else(|e| panic!("{blob}: {e}"));
    let id = keccak::keccak256(&text);
    drop(text);
    let l = r3typed::circuit::load_text(std::ffi::OsStr::new(blob));
    let bin = r3typed::qbin::encode(&l, &id, &[0; 32], false);
    for b in [&bin, &r3typed::qbin::encode(&l, &id, &keccak::keccak256(&bin), true)] {
        let (did, dl) = r3typed::qbin::decode(b).unwrap_or_else(|e| panic!("qpack: decode: {e}"));
        assert!(did == id && dl == l, "qpack: the encoded form does not round-trip");
    }
    std::fs::write(out, &bin).unwrap_or_else(|e| panic!("{out}: {e}"));
    println!("qpack {blob}: keccak {} | {} entries, {} OUT | compact {} B -> {out}", stream::hex(&id), l.c.ents.len(), l.c.outs.len(), bin.len());
    0
}

/// The entry point: `main` of a plain build, `lvm_main_<tier>` behind `dispatch.s` (renamed by `build-asm.sh`).
/// `argv` is read here, so no tier depends on std's own argument capture.
#[unsafe(no_mangle)]
pub extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    // SAFETY: the C runtime passes `argc` valid NUL-terminated strings.
    let args: Vec<String> = (0..argc as usize)
        .map(|i| unsafe { CStr::from_ptr(*argv.add(i)) }.to_string_lossy().into_owned())
        .collect();
    let code = run(args);
    let _ = std::io::stdout().flush();
    code
}
