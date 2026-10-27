//! Prover-kernel probe for a Flock-class entry (FR-R5). std only, no dependencies.
//!
//!   kernels [all|gf|eq|ntt|skip|lig|lin|wit|mem]... [--threads 1,4] [--quick]
//!
//! Every hot loop lives in a `#[target_feature]` function selected at run time
//! (`is_x86_feature_detected!`), so the binary runs on a CPU without carry-less multiply (the
//! development VM) and on the runners (AVX2 + VPCLMULQDQ-256 Zen 3, AVX-512 Zen 4 / Xeon).
//! Output lines: `RESULT <kernel> <variant> T=<threads> <param> <ns per unit> ns/<unit> <rate>/s`.
#![allow(clippy::too_many_arguments, clippy::needless_range_loop)]
mod blake;
mod gf;
mod gfbench;
mod lin;
mod ntt;
mod pipe;
mod skip;
mod sumcheck;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Barrier, OnceLock};
use std::time::Instant;

pub static CPU: OnceLock<gf::Cpu> = OnceLock::new();
pub static QUICK: OnceLock<bool> = OnceLock::new();
pub fn quick() -> bool {
    *QUICK.get().unwrap_or(&false)
}

/// xorshift64*.
#[derive(Clone)]
pub struct Rng(pub u64);
impl Rng {
    pub fn u64(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn f(&mut self) -> gf::F128 {
        gf::F128::new(self.u64(), self.u64())
    }
    pub fn fvec(&mut self, n: usize) -> Vec<gf::F128> {
        (0..n).map(|_| self.f()).collect()
    }
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        let mut v = vec![0u8; n];
        for c in v.chunks_mut(8) {
            let x = self.u64().to_le_bytes();
            c.copy_from_slice(&x[..c.len()]);
        }
        v
    }
}

/// Best wall time of `trials` runs of `f`.
pub fn best<F: FnMut()>(trials: usize, mut f: F) -> f64 {
    let mut b = f64::MAX;
    for _ in 0..trials {
        let t = Instant::now();
        f();
        b = b.min(t.elapsed().as_secs_f64());
    }
    b
}

/// `threads` copies of `f(tid)` started together; wall time from the common start to the last
/// finish. Best of `trials`.
pub fn par_best<F: Fn(usize) + Sync>(threads: usize, trials: usize, f: F) -> f64 {
    let mut b = f64::MAX;
    for _ in 0..trials {
        let bar = Barrier::new(threads + 1);
        let el = std::thread::scope(|s| {
            for t in 0..threads {
                let (bar, f) = (&bar, &f);
                s.spawn(move || {
                    bar.wait();
                    f(t);
                });
            }
            bar.wait();
            let t0 = Instant::now();
            // scope joins all threads on exit
            t0
        });
        b = b.min(el.elapsed().as_secs_f64());
    }
    b
}

/// Dynamic parallel for over `0..n` items with `threads` workers (scoped threads, atomic counter).
pub fn par_for<F: Fn(usize) + Sync>(threads: usize, n: usize, f: F) {
    if threads <= 1 || n <= 1 {
        for i in 0..n {
            f(i);
        }
        return;
    }
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..threads.min(n) {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= n {
                    break;
                }
                f(i);
            });
        }
    });
}

/// A raw pointer that may cross threads (disjoint writes are the caller's duty).
#[derive(Clone, Copy)]
pub struct SyncPtr<T>(pub *mut T);
unsafe impl<T> Send for SyncPtr<T> {}
unsafe impl<T> Sync for SyncPtr<T> {}

pub fn report(kernel: &str, variant: &str, threads: usize, param: &str, units: f64, secs: f64, unit: &str) {
    let ns = secs * 1e9 / units;
    println!(
        "RESULT\t{kernel}\t{variant}\tT={threads}\t{param}\t{ns:.3} ns/{unit}\t{:.4e} {unit}/s\t({secs:.4} s for {units:.3e})",
        units / secs
    );
}

pub fn peak_rss_mb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.to_string()))
        .and_then(|l| l.split_whitespace().nth(1).and_then(|x| x.parse::<f64>().ok()))
        .map(|kb| kb / 1024.0)
        .unwrap_or(0.0)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut threads = vec![1usize, 4];
    let mut what: Vec<String> = vec![];
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--threads" => {
                threads = args[i + 1].split(',').map(|x| x.parse().unwrap()).collect();
                i += 1;
            }
            "--quick" => {
                QUICK.set(true).ok();
            }
            w => what.push(w.to_string()),
        }
        i += 1;
    }
    if what.is_empty() || what.iter().any(|w| w == "all") {
        what = ["selftest", "mem", "gf", "eq", "ntt", "skip", "lig", "lin", "wit"].iter().map(|s| s.to_string()).collect();
    }
    let c = gf::cpu();
    CPU.set(c).ok();
    println!(
        "CPU features: pclmulqdq={} avx2+vpclmulqdq(ymm)={} avx512f+bw+vpclmulqdq(zmm)={} gfni={} ; available_parallelism={}",
        c.pclmul,
        c.ymm,
        c.zmm,
        c.gfni,
        std::thread::available_parallelism().map(|n| n.get()).unwrap_or(0)
    );
    println!("tiers measured: {:?}", gf::tiers(c).iter().map(|t| t.name()).collect::<Vec<_>>());
    let t0 = Instant::now();
    for w in &what {
        let ts = Instant::now();
        println!("=== {w}");
        match w.as_str() {
            "selftest" => selftest(c),
            "mem" => gfbench::bench_mem(&threads),
            "gf" => gfbench::bench_gf(c, &threads),
            "eq" => sumcheck::bench_eq_rs(c, &threads),
            "ntt" => ntt::bench(c, &threads),
            "skip" => skip::bench(c, &threads),
            "lig" => sumcheck::bench_sumcheck(c, &threads),
            "lin" => lin::bench(c, &threads),
            "wit" => blake::bench(&threads),
            w if w.starts_with("pipe:") => {
                // pipe:M[:USEFUL]  (USEFUL compressions with witness; default 2^(M-14))
                let p: Vec<usize> = w[5..].split(':').map(|x| x.parse().unwrap()).collect();
                let useful = if p.len() > 1 { p[1] } else { 1 << (p[0] - 14) };
                for &t in &threads {
                    pipe::run(c, p[0], useful, t);
                }
            }
            _ => println!("unknown benchmark {w}"),
        }
        println!("=== {w} done in {:.1} s; peak RSS {:.0} MB", ts.elapsed().as_secs_f64(), peak_rss_mb());
    }
    println!("TOTAL {:.1} s; peak RSS {:.0} MB", t0.elapsed().as_secs_f64(), peak_rss_mb());
}

fn selftest(c: gf::Cpu) {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let mut ok = true;
    let mut check = |name: &str, r: Result<(), String>| match r {
        Ok(()) => println!("SELFTEST {name}: ok"),
        Err(e) => {
            ok = false;
            println!("SELFTEST {name}: FAIL {e}")
        }
    };
    check("gf", gf::selftest(c, &mut rng));
    check("ntt", ntt::selftest(c, &mut rng));
    check("skip", skip::selftest(c, &mut rng));
    check("sumcheck", sumcheck::selftest(c, &mut rng));
    check("lin", lin::selftest(c, &mut rng));
    check("blake2s", blake::selftest());
    println!("SELFTEST {}", if ok { "PASS" } else { "FAIL" });
}
