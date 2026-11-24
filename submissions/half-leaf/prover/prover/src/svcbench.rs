//! `svcbench [GRIND_SCALE] [LEAF_SCALE] [--local]` (WP-R0, M7 of RV1): the oracle traffic of one v6 step in the
//! service run, dummy queries of the real sizes through the real client (`service.rs`), timed by phase.
//!
//! The mix (BLUEPRINT §2.2, §4: `M = 25`, rate ¼, 46 lanes, ladder (6,4,4,4,4), caps 2^7,2^6,2^5,2^5,2^4):
//! - level 0: `2^21 · LEAF_SCALE` leaves of 368 B (3 permutations each under the key), then the node levels down to
//!   the cap, 64 B each (1 permutation), each level one parallel call;
//! - levels 1–4: `2^16, 2^15, 2^14, 2^13` leaves of 16 `E` values (256 B, 3 permutations), nodes down to their caps;
//! - grinds (56 B queries `st ‖ nonce`, 1 permutation), each of `2^g` expected attempts × GRIND_SCALE, searched in
//!   rounds of a quarter of that (leanVM's windows; at most 2^17 a round) over the pool: OOD 19 × 5, level-0 query
//!   20, level-1..4 queries 18 × 4, ring switch 17 × 2, mini-bus 14, WHIR fold 11 × 22 rounds;
//! - the sequential Fiat–Shamir side: 900 chain steps and 700 small grinds (≤ 6 bits, one 64-candidate request
//!   each), one round trip each.
//! Every query's bytes are a function of its index, nothing is kept; only the time and the counts matter.

use std::time::Instant;

use crate::oracle::{self, Digest};

const GRIND_Q: usize = 56;

struct Tally {
    queries: u64,
    perms: u64,
    bytes: u64,
}

fn perms(len: usize) -> u64 {
    crate::keccak::oracle_perms(len)
}

/// `n` queries of `len` bytes over the pool, `chunk` per task, each task on its own connection.
fn par_queries(n: usize, len: usize, chunk: usize, salt: u64, t: &mut Tally) {
    let mut out = vec![[0u8; 32]; n];
    parallel::chunks_mut(&mut out, chunk.max(1), |c, sub: &mut [Digest]| {
        let off = (c * chunk) as u64;
        oracle::get().ask_many_here(sub, &|i, buf: &mut Vec<u8>| {
            let w = (salt ^ (off + i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)).to_le_bytes();
            for k in 0..len {
                buf.push(w[k % 8] ^ k as u8);
            }
        });
    });
    std::hint::black_box(&out);
    t.queries += n as u64;
    t.perms += n as u64 * perms(len);
    t.bytes += (n * len) as u64;
}

/// A Merkle commitment: `leaves` of `leaf_len` bytes, then node levels (64 B) down to `cap` nodes.
fn commit(leaves: usize, leaf_len: usize, cap: usize, chunk: usize, salt: u64, t: &mut Tally) {
    par_queries(leaves, leaf_len, chunk, salt, t);
    let mut m = leaves / 2;
    while m >= cap.max(1) {
        par_queries(m, 64, chunk.min(m.div_ceil(parallel::num_threads()).max(1)), salt ^ m as u64, t);
        m /= 2;
    }
}

pub fn run(args: &[String]) -> i32 {
    let num = |i: usize, d: f64| args.get(i).filter(|v| !v.starts_with("--")).map_or(d, |v| v.parse().expect("scale"));
    let (gscale, lscale) = (num(2, 1.0), num(3, 1.0));
    let local = args.iter().any(|a| a == "--local");
    if local {
        oracle::install(Box::new(oracle::Local::keyed(&[7u8; 32])));
    } else {
        let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| "/run/rf/oracle.sock".into());
        oracle::install(Box::new(crate::service::Service::connect(&path).unwrap_or_else(|e| crate::service::fatal(&e))));
    }
    parallel::init();
    let chunk: usize = std::env::var("LVM6_CHUNK").ok().and_then(|v| v.parse().ok()).unwrap_or(4096);
    let t_all = Instant::now();
    let mut lines = vec![];
    let mut total = Tally { queries: 0, perms: 0, bytes: 0 };
    let mut phase = |name: &str, f: &mut dyn FnMut(&mut Tally)| {
        let mut t = Tally { queries: 0, perms: 0, bytes: 0 };
        let t0 = Instant::now();
        f(&mut t);
        let s = t0.elapsed().as_secs_f64();
        lines.push(format!(
            "  {name:<22} {:>10} q {:>10} perms {:>8.1} MB {:>7.3} s  {:>6.2} Mq/s {:>6.2} Mperm/s",
            t.queries, t.perms, t.bytes as f64 / 1e6, s, t.queries as f64 / s / 1e6, t.perms as f64 / s / 1e6
        ));
        total.queries += t.queries;
        total.perms += t.perms;
        total.bytes += t.bytes;
    };
    phase("level0 commit", &mut |t| commit(((1usize << 21) as f64 * lscale) as usize, 368, 1 << 7, chunk, 1, t));
    phase("levels1-4 commit", &mut |t| {
        for (i, (lg, cap)) in [(16, 6), (15, 5), (14, 5), (13, 4)].into_iter().enumerate() {
            commit(((1usize << lg) as f64 * lscale) as usize, 256, 1 << cap, chunk, 100 + i as u64, t);
        }
    });
    phase("grinds", &mut |t| {
        let mut grinds = vec![19u32; 5];
        grinds.push(20);
        grinds.extend([18; 4]);
        grinds.extend([17; 2]);
        grinds.push(14);
        grinds.extend([11; 22]);
        for (k, g) in grinds.into_iter().enumerate() {
            let total = ((1u64 << g) as f64 * gscale) as usize;
            let round = (total / 4).clamp(64, 1 << 17);
            let per = round.div_ceil(parallel::num_threads()).max(1);
            let mut done = 0;
            while done < total {
                par_queries(round, GRIND_Q, per.min(chunk), 1000 + k as u64 + done as u64, t);
                done += round;
            }
        }
    });
    phase("sequential FS", &mut |t| {
        for i in 0..900u64 {
            let q = [&i.to_le_bytes()[..], &[0u8; 48][..]].concat();
            std::hint::black_box(oracle::ask(&q));
        }
        t.queries += 900;
        t.perms += 900;
        t.bytes += 900 * GRIND_Q as u64;
        let mut out = vec![[0u8; 32]; 64];
        for i in 0..700u64 {
            oracle::get().ask_many_here(&mut out, &|j, buf: &mut Vec<u8>| {
                buf.extend_from_slice(&(i << 8 | j as u64).to_le_bytes());
                buf.resize(GRIND_Q, 0);
            });
        }
        t.queries += 700 * 64;
        t.perms += 700 * 64;
        t.bytes += 700 * 64 * GRIND_Q as u64;
    });
    let s = t_all.elapsed().as_secs_f64();
    println!(
        "svcbench {} threads {} chunk {chunk} grind x{gscale} leaves x{lscale}: {} queries, {} perms, {:.0} MB in {s:.3} s = {:.2} Mq/s, {:.2} Mperm/s",
        if local { "local-PRF" } else { "service" },
        parallel::num_threads(),
        total.queries,
        total.perms,
        total.bytes as f64 / 1e6,
        total.queries as f64 / s / 1e6,
        total.perms as f64 / s / 1e6
    );
    for l in lines {
        println!("{l}");
    }
    0
}
