//! `setup DIR` (PROVER.md §3, untimed, `setup_s` 4 min): the CPU self-test of every tier, season 1's form
//! (`archive/season-1/wide-packs/prover/src/main.rs` `cmd_setup`, WP-15a). `dispatch.s` runs `setup` on the
//! portable tier v2; each tier runs `selftest` in a child process (`LVM_CPU` forced, 4 threads, a deadline): v2
//! first, the reference, then v4, then v4p. The fastest tier whose child exits 0 with v2's digest is kept: when it is
//! not v4, `DIR/lvm-cpu` names the cap (`v4p` or `v2`), which `dispatch.s` reads at every start
//! (`$RF_SETUP/lvm-cpu`). A tier the CPU lacks raises SIGILL in its child only (a failure). `LVM_SELFTEST_FAIL=v4[,v4p]`
//! makes those children fail (a test of the fallback).
//!
//! R8: then the embedded circuit `Q` is decoded, checked and written raw to `DIR/lvm6-q.bin`
//! (`r3typed::qbin::setup`), which every step reads before `ready`. A failure to write it is logged, not fatal (a
//! step then decodes the embedded form); a damaged embedded form aborts.
//!
//! `selftest` (the child): the FORMAT6/contract KATs (`kat::run_all`), then leanVM's Keccak GKR batch at 2^14 proved
//! on this tier's kernels and verified natively; prints `selftest <tier> <digest>`, the digest being Keccak-256 of
//! the proof (tier-independent: P1's fixture `20706a33…e5c7`).

use std::time::{Duration, Instant};

/// R9: `selftest`'s exit code when a KAT fails (a deterministic build fault, not a CPU's: `setup` refuses it on v2).
pub const SELFTEST_KAT_FAIL: i32 = 3;

pub fn selftest() -> i32 {
    parallel::init();
    let fails = crate::kat::run_all();
    let r = crate::smoke::run(14, 12, 1);
    if fails != 0 || !r.verified {
        eprintln!("selftest {}: kat fails {fails}, verified {}", crate::VARIANT, r.verified);
        return if fails != 0 { SELFTEST_KAT_FAIL } else { 1 };
    }
    println!("selftest {} {}", crate::VARIANT, crate::stream::hex(&crate::keccak::keccak256(&r.proof)));
    0
}

const KAT_FAIL: &str = "KAT failure";

fn run_child(exe: &str, v: &str, budget_s: u64) -> Result<String, String> {
    if std::env::var("LVM_SELFTEST_FAIL").unwrap_or_default().split(',').any(|x| x == v) {
        return Err("failure injected (LVM_SELFTEST_FAIL)".into());
    }
    use std::os::unix::process::CommandExt;
    unsafe extern "C" {
        fn setrlimit(resource: i32, rlim: *const [u64; 2]) -> i32;
    }
    let mut cmd = std::process::Command::new(exe);
    // SAFETY: async-signal-safe: one setrlimit (RLIMIT_CORE = 4) in the child before exec, so that a crashing tier
    // leaves no core file in the setup directory.
    unsafe {
        cmd.pre_exec(|| {
            setrlimit(4, &[0u64, 0u64]);
            Ok(())
        });
    }
    let mut child = cmd
        .arg("selftest")
        .env("LVM_CPU", v)
        .env("LVM_THREADS", "4")
        .env_remove("RF_SETUP")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .map_err(|e| format!("spawn: {e}"))?;
    let deadline = Instant::now() + Duration::from_secs(budget_s);
    let status = loop {
        match child.try_wait() {
            Ok(Some(st)) => break st,
            Ok(None) if Instant::now() > deadline => {
                let _ = child.kill();
                let _ = child.wait();
                return Err("timeout".into());
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(e) => return Err(format!("wait: {e}")),
        }
    };
    let mut out = String::new();
    use std::io::Read;
    if let Some(mut o) = child.stdout.take() {
        let _ = o.read_to_string(&mut out);
    }
    if status.code() == Some(SELFTEST_KAT_FAIL) {
        return Err(format!("{KAT_FAIL}: {status}"));
    }
    if !status.success() {
        return Err(format!("{status}"));
    }
    out.lines()
        .find_map(|l| l.strip_prefix("selftest ").and_then(|r| r.split_whitespace().nth(1)).map(str::to_string))
        .ok_or_else(|| "no selftest line".into())
}

pub fn setup(dir: &str) -> i32 {
    let t0 = Instant::now();
    let exe = std::env::current_exe().map(|p| p.to_string_lossy().into_owned()).unwrap_or_else(|_| "/prover/prover".into());
    let budget = |v: &str| -> u64 {
        std::env::var(format!("LVM_SELFTEST_S_{v}")).ok().and_then(|x| x.parse().ok()).unwrap_or(if v == "v2" { 120 } else { 50 })
    };
    let mut log = String::new();
    let cap = format!("{dir}/lvm-cpu");
    let reference = match run_child(&exe, "v2", budget("v2")) {
        Ok(d) => d,
        // R9: a KAT failure on the portable tier is the build's (e.g. a stale schedule tally for the shape), not the
        // CPU's: fail setup instead of capping every tier at v2 with no error (P17-freeze §5)
        Err(e) if e.starts_with(KAT_FAIL) => {
            log += &format!("v2: FAIL ({e}); setup fails\n");
            let _ = std::fs::write(format!("{dir}/lvm-selftest.txt"), &log);
            eprint!("{log}");
            return 1;
        }
        Err(e) => {
            log += &format!("v2: FAIL ({e}); cap v2\n");
            let _ = std::fs::write(&cap, "v2\n");
            let rc = setup_q(dir, &mut log);
            let _ = std::fs::write(format!("{dir}/lvm-selftest.txt"), &log);
            eprint!("{log}");
            return rc;
        }
    };
    log += &format!("v2: ok {reference}\n");
    let mut chosen = "v2";
    for v in ["v4", "v4p"] {
        match run_child(&exe, v, budget(v)) {
            Ok(d) if d == reference => {
                log += &format!("{v}: ok\n");
                chosen = v;
                break;
            }
            Ok(d) => log += &format!("{v}: FAIL (digest differs: {d})\n"),
            Err(e) => log += &format!("{v}: FAIL ({e})\n"),
        }
    }
    if chosen == "v4" {
        let _ = std::fs::remove_file(&cap);
    } else if let Err(e) = std::fs::write(&cap, format!("{chosen}\n")) {
        eprintln!("setup: {cap}: {e}");
        return 1;
    }
    log += &format!("cap: {chosen} ({:.1} s)\n", t0.elapsed().as_secs_f64());
    let rc = setup_q(dir, &mut log);
    let _ = std::fs::write(format!("{dir}/lvm-selftest.txt"), &log);
    eprint!("{log}");
    rc
}

/// R8: the embedded `Q` in its raw form (`r3typed::qbin::setup`).
fn setup_q(dir: &str, log: &mut String) -> i32 {
    let t = Instant::now();
    match r3typed::qbin::setup(dir) {
        Ok(None) => {
            *log += "q: no embedded Q\n";
            0
        }
        Ok(Some(n)) => {
            *log += &format!("q: {dir}/{} {n} B ({:.1} s)\n", r3typed::qbin::SETUP_FILE, t.elapsed().as_secs_f64());
            0
        }
        Err(e) => {
            // not fatal: a step without the setup file decodes the embedded form itself (slower start-up)
            *log += &format!("q: FAIL ({e}); steps decode the embedded Q\n");
            0
        }
    }
}
