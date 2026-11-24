//! `full6` (WP R3, dev): complete lvm6 proofs at the build's shape (`P18`; `P17` with the feature `p17`) through [`crate::prove6`], toy-signed over the keyed local
//! oracle; `refv-full` (tools/r3v) checks each file as `acc` does.
//!
//! `lvm6-prover full6 OUT [SEED] [PARTS] [FLAGS]`: `PARTS` is `all` (default) or a comma list of `tree`, `sponge`,
//! `typed`, `mb` (dev: omitted parts are not proved; `refv-full` must be told the same list). `FLAGS`, comma list:
//! `check` asserts every stack claim natively and the opening's running claim at every level; `node` makes step 1
//! (leaf mode) in `OUT/leaf` and then step 2 (node mode, over step 1's signed proof, with a toy `σ_leaf`) in
//! `OUT/node`. Without `node` the leaf proof is written to `OUT` itself.

use std::path::Path;
use std::time::Instant;

use crate::format::{Signed, to_file, toy_sign, trace_digest};
use crate::keccak::keccak256;
use crate::prove6::{Child, Opts, Proved, prove6};
use crate::smoke::SplitMix;
use crate::stream::hex;

/// The dev oracle key and toy signer seed (as `tree6`).
pub const KEY: [u8; 32] = [0x5A; 32];
pub const SIGN_SEED: u8 = 7;

fn peak_rss_mib() -> f64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|v| v.parse::<f64>().ok())
        .map_or(0.0, |kb| kb / 1024.0)
}

fn data(seed: u64, n: usize) -> Vec<u8> {
    let mut rng = SplitMix(seed ^ n as u64);
    (0..4 * n).flat_map(|_| rng.next_u64().to_le_bytes()).collect()
}

fn write(out: &Path, p: &Proved, signed: &Signed, parts: &str, seed: u64, vk: &[u8; 32], secs: f64) {
    std::fs::create_dir_all(out).expect("OUT dir");
    let file = to_file(signed);
    std::fs::write(out.join("full6.signed"), &file).expect("write proof");
    let meta = format!(
        "seed {seed}\nparts {parts}\nkey {}\nvk {}\nc {}\nh {}\n",
        hex(&KEY),
        hex(vk),
        hex(&p.c),
        hex(&p.h)
    );
    std::fs::write(out.join("meta.txt"), &meta).expect("write meta");
    let tline: Vec<String> = p.times.iter().map(|(n, s)| format!("{n} {s:.3}")).collect();
    println!(
        "full6 {} tier {} threads {} parts {parts}: |pi| {} trace {} claims {} file keccak {} | {} | total {secs:.3} s | peak {:.0} MiB",
        out.display(),
        crate::VARIANT,
        parallel::num_threads(),
        p.pi.len(),
        p.trace.len(),
        p.claims,
        hex(&keccak256(&file)),
        tline.join(", "),
        peak_rss_mib()
    );
}

pub fn run(args: &[String]) -> i32 {
    let out = std::path::PathBuf::from(args.get(2).expect("OUT dir"));
    let seed: u64 = args.get(3).map_or(1, |v| v.parse().expect("SEED"));
    let parts_arg = args.get(4).map_or("all", String::as_str).to_string();
    let has = |p: &str| parts_arg == "all" || parts_arg.split(',').any(|x| x == p);
    assert!(has("tree"), "the tree batch is every proof's");
    let flags = args.get(5).map_or("", String::as_str);
    let flag = |f: &str| flags.split(',').any(|x| x == f);
    let opts = Opts { sponge: has("sponge"), typed: has("typed"), mb: has("mb"), check: flag("check") };
    let parts = if parts_arg == "all" { "tree,sponge,typed,mb".to_string() } else { parts_arg.clone() };
    parallel::init();
    crate::oracle::install(Box::new(crate::oracle::Local::keyed(&KEY)));
    // R8: as the stream before `ready` (untimed there; here outside the steps' totals)
    if opts.typed {
        crate::prove6::preload();
    }
    let n = 1usize << fs6::params::SHAPE.log_blocks;
    let (vk, _) = toy_sign(SIGN_SEED, &[0; 32]);

    // Step 1 (leaf mode).
    let t = Instant::now();
    // Dev (R7): `LVM6_LEAF_FROM=DIR` takes step 1 from `DIR/full6.signed` (+ `meta.txt`'s `c`) instead of proving it.
    let (s1, c1, acc1) = if let Some(d) = std::env::var_os("LVM6_LEAF_FROM").filter(|_| flag("node")) {
        let d = std::path::PathBuf::from(d);
        let s1 = crate::format::from_file(&std::fs::read(d.join("full6.signed")).expect("leaf file")).expect("leaf parse");
        let meta = std::fs::read_to_string(d.join("meta.txt")).expect("leaf meta");
        let ch = meta.lines().find_map(|l| l.strip_prefix("c ")).expect("meta c");
        let c1: [u8; 32] = std::array::from_fn(|i| u8::from_str_radix(&ch[2 * i..2 * i + 2], 16).unwrap());
        eprintln!("full6: step 1 from {}", d.display());
        let acc = opts.typed.then(|| crate::prove6::child_acc_out(&s1));
        (s1, c1, acc)
    } else {
        let xs = data(seed, n);
        let p1 = prove6(n as u64, &xs, &vk, None, &opts);
        let (vk1, sig) = toy_sign(SIGN_SEED, &trace_digest(&p1.trace));
        assert_eq!(vk, vk1);
        let s1 = Signed { pi: p1.pi.clone(), tr: p1.trace.clone(), sig };
        let dir1 = if flag("node") { out.join("leaf") } else { out.clone() };
        write(&dir1, &p1, &s1, &parts, seed, &vk, t.elapsed().as_secs_f64());
        if !flag("node") {
            return 0;
        }
        (s1, p1.c, p1.acc_out.clone())
    };

    // Step 2 (node mode) over step 1: σ_leaf signs `traceDigest []` (toy key; a real stream uses a fresh one-time key).
    let t = Instant::now();
    let (_, sigma_leaf) = toy_sign(SIGN_SEED, &trace_digest(&Vec::new()));
    let acc_out = acc1.unwrap_or_else(|| r3typed::Acc::leaf(r3typed::circuit()));
    if opts.typed {
        assert_eq!(crate::prove6::child_acc_out(&s1), acc_out, "accOut recomputed from the signed file");
    }
    let child = Child { c_prev: c1, signed: &s1, sigma_leaf: &sigma_leaf, acc_out };
    let xs2 = data(seed + 1, n);
    let p2 = prove6(n as u64, &xs2, &vk, Some(&child), &opts);
    let (_, sig2) = toy_sign(SIGN_SEED, &trace_digest(&p2.trace));
    let s2 = Signed { pi: p2.pi.clone(), tr: p2.trace.clone(), sig: sig2 };
    write(&out.join("node"), &p2, &s2, &parts, seed + 1, &vk, t.elapsed().as_secs_f64());
    0
}
