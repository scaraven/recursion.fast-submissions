//! `spartan-srom-prover`: the native prover of the `spartan-srom` entry (blueprint §7), talking to
//! the v4 oracle service at `$RF_ORACLE` (`service/PROTOCOL.md`). Submitted as `prover.s`
//! (`build-asm.sh`). The runner's invocations (`harness/PROVER.md`):
//!
//!   setup DIR       nothing to precompute; exits 0
//!   tree DIR        DIR/leaves.json, DIR/vk.hex -> DIR/proofs/L<i>.bin, DIR/proofs/N<l>_<j>.bin,
//!                   DIR/root.bin (leaves `L`, inner nodes and root bundles `B` of their subtrees)
//!   leaf DIR        ready / go / done; DIR/leaf.json -> DIR/proof.bin (`L`)
//!   node DIR        ready / go / done; DIR/child{1,2}.{stmt,bin} -> DIR/proof.bin (`B`)
//!
//! Development modes (VK, STMT, START: 64 hex digits or a file holding them):
//!
//!   verify-native VK STMT FILE      the native `acc` (acc.rs); prints `accept` or `reject: why`,
//!                                   exit 0 / 1
//!   extract-check VK STMT FILE      the copy extractor's witness `decode π` of the file is in
//!                                   `Rel (acc vk) STMT` (a stand-in of the runner's liveness check)
//!   info FILE                       kind and sizes of a signed-proof file
//!   prove-leaf [--oracle O] START N OUT   the raw leaf `π` (v3's bytes) under oracle O; prints
//!                                   its statement
//!   check-leaf [--oracle O] STMT PI the raw leaf `π` checked by the native leaf verifier under O
//!   prove-signed START N OUT        a signed `L` file through the service; prints its statement
//!   bench-leaf [--oracle O] N REPS  prove (and, with the service, SIGN) a leaf REPS
//!                                   times; key=value lines on stdout
//!   selftest-field [COUNT]          compare the pclmulqdq field products with the portable ones
//!   dump-field | dump-circuit | dump-walk | dump-encode | dump-mle | dump-phi | dump-sumcheck
//!   dump-transcript [--oracle O] | dump-transcript-ops [--oracle O] | dump-proof [--oracle O] DIR
//!   dump-leaf-trace [--oracle O] DIR      v3's known-answer dumps
//!
//! Oracles O: `v3` (`blake2s256(0x52 ‖ q)`, the default of the dumps), `keyed` / `keyed:HEX`
//! (keyed BLAKE2s-256 under 32 zero bytes / the given key, the default of `prove-leaf` and
//! `bench-leaf`), `service` (`$RF_ORACLE`). SPARTAN_VERBOSE=1 prints timings on stderr (2: per
//! sumcheck round too), SPARTAN_THREADS bounds the threads, SPARTAN_NO_CLMUL=1 forces the portable
//! field product, SPARTAN_REPLAY=1 replays the native verifier on every leaf and checks the trace,
//! SPARTAN_TREE_WIDTH sets how many tree leaves are proved at once.

// Some helpers are used only by the tests and the known-answer dumps.
#![allow(dead_code)]

mod acc;
mod blake2s;
mod chain;
mod circuit;
mod field;
mod format;
mod kat;
mod make;
mod mle;
mod oracle;
mod par;
mod prover;
mod ringswitch;
mod rs;
mod service;
mod sumcheck;
mod transcript;
mod verifier;

use std::io::{BufRead, Write};
use std::path::Path;
use std::process::ExitCode;
use std::time::Instant;

use blake2s::{chain_end, leaf_stmt, node_stmt, Digest};
use circuit::Circuit;
use format::{from_file, to_file, Sig, Signed};
use oracle::{Local, Oracle};
use service::Service;

fn verbose() -> bool {
    std::env::var("SPARTAN_VERBOSE").map(|v| v != "0").unwrap_or(false)
}

macro_rules! note {
    ($($t:tt)*) => { if verbose() { eprintln!($($t)*); } };
}

fn parse_hex32(s: &str) -> Option<Digest> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut d = [0u8; 32];
    for i in 0..32 {
        d[i] = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(d)
}

/// A statement or key file: 64 hex digits and an optional newline (PROVER.md §3).
fn read_hex32(path: &Path) -> Result<Digest, String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    std::str::from_utf8(&b).ok().and_then(parse_hex32).ok_or_else(|| format!("{}: not 64 hex digits", path.display()))
}

/// 64 hex digits given directly, or the file holding them.
fn hex_arg(a: &str) -> Result<Digest, String> {
    parse_hex32(a).map_or_else(|| read_hex32(Path::new(a)), Ok)
}

fn hex(b: &[u8]) -> String {
    kat::hex(b)
}

/// The number after `"key":`.
fn json_u64(text: &str, key: &str) -> Option<u64> {
    let k = format!("\"{key}\"");
    let i = text.find(&k)?;
    let rest = text[i + k.len()..].trim_start().strip_prefix(':')?.trim_start();
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

/// The string after `"key":`.
fn json_str<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    let k = format!("\"{key}\"");
    let i = text.find(&k)?;
    let rest = text[i + k.len()..].trim_start().strip_prefix(':')?.trim_start().strip_prefix('"')?;
    Some(&rest[..rest.find('"')?])
}

/// `{"n": N, "starts": ["<64 hex>", ...]}`.
fn parse_leaves(text: &str) -> Result<(u64, Vec<Digest>), String> {
    let bad = || "leaves.json: expected {\"n\": N, \"starts\": [hex, ...]}".to_string();
    let n = json_u64(text, "n").ok_or_else(bad)?;
    let si = text.find("\"starts\"").ok_or_else(bad)?;
    let open = si + text[si..].find('[').ok_or_else(bad)?;
    let close = open + text[open..].find(']').ok_or_else(bad)?;
    let mut starts = vec![];
    for part in text[open + 1..close].split(',') {
        let p = part.trim();
        if p.is_empty() {
            continue;
        }
        let p = p.strip_prefix('"').and_then(|p| p.strip_suffix('"')).ok_or_else(bad)?;
        starts.push(parse_hex32(p).ok_or_else(bad)?);
    }
    if n > chain::CHAIN_CAP || starts.is_empty() || !starts.len().is_power_of_two() {
        return Err("leaves.json: n in [0, 2^20] and a power of two of 32-byte starts".into());
    }
    Ok((n, starts))
}

/// `{"n": N, "start": "<64 hex>"}`.
fn parse_leaf(text: &str) -> Result<(u64, Digest), String> {
    let bad = || "leaf.json: expected {\"n\": N, \"start\": hex}".to_string();
    let n = json_u64(text, "n").ok_or_else(bad)?;
    let s = json_str(text, "start").and_then(parse_hex32).ok_or_else(bad)?;
    if n > chain::CHAIN_CAP {
        return Err("leaf.json: n > chainCap".into());
    }
    Ok((n, s))
}

fn write(path: &Path, b: &[u8]) -> Result<(), String> {
    std::fs::write(path, b).map_err(|e| format!("{}: {e}", path.display()))
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn read_signed(path: &Path) -> Result<Signed, String> {
    from_file(&read(path)?).ok_or_else(|| format!("{}: not a signed-proof file", path.display()))
}

/// The service at `$RF_ORACLE`.
fn service() -> Result<Service, String> {
    let p = std::env::var("RF_ORACLE").map_err(|_| "RF_ORACLE is not set".to_string())?;
    Service::connect(&p)
}

/// The service, its key checked against `DIR/vk.hex` when that file exists.
fn service_for(dir: &Path) -> Result<Service, String> {
    let svc = service()?;
    let f = dir.join("vk.hex");
    if f.exists() {
        let vk = read_hex32(&f)?;
        if svc.vk() != vk {
            return Err("vk.hex differs from the service's public key".into());
        }
    }
    Ok(svc)
}

/// An oracle from its name (module header).
fn local_or_service(spec: &str) -> Result<Box<dyn Oracle>, String> {
    Ok(match spec {
        "v3" => Box::new(Local::V3),
        "keyed" => Box::new(Local::keyed(&[0u8; 32])),
        "service" => Box::new(service()?),
        _ => match spec.strip_prefix("keyed:").and_then(parse_hex32) {
            Some(k) => Box::new(Local::keyed(&k)),
            None => return Err(format!("unknown oracle {spec:?} (v3, keyed, keyed:HEX, service)")),
        },
    })
}

/// Wait for the line `go` on stdin (PROVER.md §3).
fn wait_go() -> Result<(), String> {
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        line.clear();
        let n = stdin.lock().read_line(&mut line).map_err(|e| format!("stdin: {e}"))?;
        if n == 0 {
            return Err("stdin closed before `go`".into());
        }
        if line.trim() == "go" {
            return Ok(());
        }
    }
}

fn say(word: &str) {
    let mut out = std::io::stdout().lock();
    let _ = writeln!(out, "{word}");
    let _ = out.flush();
}

fn file_summary(f: &[u8], p: &Signed) -> String {
    let qb: usize = p.tr.iter().map(|(q, _)| q.len()).sum();
    format!(
        "kind={} pi_bytes={} trace_entries={} trace_query_bytes={} trace_file_bytes={} file_bytes={}",
        make::kind(&p.pi),
        p.pi.len(),
        p.tr.len(),
        qb,
        8 + qb + 40 * p.tr.len(),
        f.len()
    )
}

/// A line on stderr when an output is above a cap that `acc` or the runner checks (review F2-m5):
/// the file is still written, and the runner's `acc` decides, but its failure then explains itself.
fn warn_caps(name: &str, f: &[u8]) {
    let Some(v) = make::view(f) else { return };
    let mut why = vec![];
    if v.pi.len() > format::PROOF_CAP {
        why.push(format!("|π| = {} > proofCap = {}", v.pi.len(), format::PROOF_CAP));
    }
    if v.items.len() as u64 > acc::Q_V {
        why.push(format!("{} trace entries > qV = {}", v.items.len(), acc::Q_V));
    }
    if let Some(m) = v.items.iter().map(|x| x.1).max().filter(|&m| m > format::QUERY_CAP) {
        why.push(format!("a query of {m} bytes > queryCap = {}", format::QUERY_CAP));
    }
    if f.len() > 64 << 20 {
        why.push(format!("{} file bytes > the runner's file_cap of 64 MiB", f.len()));
    }
    if !why.is_empty() {
        eprintln!("spartan-srom-prover: {name}: {}: acc will reject it", why.join(", "));
    }
}

fn leaf_signed(circ: &Circuit, svc: &Service, s: &Digest, n: u64) -> Result<Signed, String> {
    let t = Instant::now();
    let mut cost = make::LeafCost::default();
    let p = make::leaf(circ, svc, s, n, &mut cost)?;
    note!(
        "leaf n={n} total={:.4}s prove={:.4}s replay={:.4}s sign={:.4}s table={} | {} | {} | {}",
        t.elapsed().as_secs_f64(),
        cost.prove_s,
        cost.replay_s,
        cost.sign_s,
        cost.table,
        cost.phases,
        cost.oracle,
        svc.report()
    );
    Ok(p)
}

/// How many leaves of a tree are proved at once (they share the pool's threads): as many as the
/// threads, within a memory budget of 8 GiB at `32 MiB + 64 KiB·n` per leaf (a leaf's measured
/// peak is 40–55 KiB per chain step at `n ≥ 4096`); `SPARTAN_TREE_WIDTH` overrides.
fn tree_width(n: u64, leaves: usize) -> usize {
    let w = match std::env::var("SPARTAN_TREE_WIDTH").ok().and_then(|v| v.parse().ok()) {
        Some(w) => w,
        None => ((8u64 << 30) / ((32 << 20) + (64 << 10) * n)) as usize,
    };
    w.min(par::threads()).clamp(1, leaves)
}

fn cmd_tree(dir: &Path) -> Result<(), String> {
    let t0 = Instant::now();
    heap_setup(0);
    let text = std::fs::read_to_string(dir.join("leaves.json")).map_err(|e| format!("leaves.json: {e}"))?;
    let (n, starts) = parse_leaves(&text)?;
    let svc = service_for(dir)?;
    let circ = Circuit::build();
    let pdir = dir.join("proofs");
    std::fs::create_dir_all(&pdir).map_err(|e| e.to_string())?;
    let r = starts.len().trailing_zeros();
    let mut level: Vec<(Digest, Signed)> = vec![];
    // the leaves are proved `w` at a time on the shared pool (`tree_width`) and signed in order,
    // here, while the later ones are still being proved
    let k = starts.len();
    let w = tree_width(n, k);
    type Proved = Result<(Vec<u8>, oracle::Trace, make::LeafCost, f64), String>;
    let slots: Vec<std::sync::Mutex<Option<Proved>>> = (0..k).map(|_| std::sync::Mutex::new(None)).collect();
    let ready = std::sync::Condvar::new();
    let next = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|sc| -> Result<(), String> {
        sc.spawn(|| {
            par::run(w, &|_| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= k {
                    break;
                }
                let t = Instant::now();
                let mut cost = make::LeafCost::default();
                let p = make::prove_traced(&circ, &svc, &starts[i], n, &mut cost);
                *slots[i].lock().unwrap() = Some(p.map(|(pi, tr)| (pi, tr, cost, t.elapsed().as_secs_f64())));
                ready.notify_all();
            })
        });
        for (i, slot) in slots.iter().enumerate() {
            let mut g = slot.lock().unwrap();
            while g.is_none() {
                g = ready.wait(g).unwrap();
            }
            let (pi, tr, mut cost, prove_wall) = g.take().unwrap()?;
            drop(g);
            let t = Instant::now();
            let sig = make::sign(&svc, &tr)?;
            cost.sign_s = t.elapsed().as_secs_f64();
            let p = Signed { pi, tr, sig };
            let f = to_file(&p);
            warn_caps(&format!("L{i}.bin"), &f);
            write(&pdir.join(format!("L{i}.bin")), &f)?;
            if r == 0 {
                write(&dir.join("root.bin"), &f)?;
            }
            note!(
                "leaf {i} n={n} prove+trace={prove_wall:.4}s sign={:.4}s (width {w}) | {} | {}",
                cost.sign_s,
                cost.phases,
                cost.oracle
            );
            let h: Digest = p.pi[48..80].try_into().unwrap();
            level.push((leaf_stmt(&h, n), p));
        }
        Ok(())
    })?;
    let mut sigma0: Option<Sig> = None;
    for lv in 1..=r {
        let mut next = vec![];
        for j in 0..level.len() / 2 {
            let ((c1, p1), (c2, p2)) = (&level[2 * j], &level[2 * j + 1]);
            let t = Instant::now();
            let mut cost = make::NodeCost::default();
            let p = make::node(
                &svc,
                c1,
                p1,
                c2,
                p2,
                &mut || {
                    if sigma0.is_none() {
                        sigma0 = Some(make::sign(&svc, &vec![])?);
                    }
                    Ok(sigma0.clone().unwrap())
                },
                &mut cost,
            )?;
            let f = to_file(&p);
            let name = if lv < r { pdir.join(format!("N{lv}_{j}.bin")) } else { dir.join("root.bin") };
            warn_caps(&name.file_name().unwrap().to_string_lossy(), &f);
            write(&name, &f)?;
            note!(
                "node {lv}_{j} {:.4}s (build {:.4}s, SIGN {:.4}s) {}",
                t.elapsed().as_secs_f64(),
                cost.build_s,
                cost.sign_s,
                file_summary(&f, &p)
            );
            next.push((node_stmt(c1, c2), p));
        }
        level = next;
    }
    note!("tree r={r} n={n} {:.4}s {}", t0.elapsed().as_secs_f64(), svc.report());
    Ok(())
}

extern "C" {
    /// glibc's `mallopt` (the prover is linked with glibc, `-static`).
    fn mallopt(param: i32, value: i32) -> i32;
}

/// Keep the memory the prover frees (one arena, no trimming, the largest heap threshold for
/// `mmap`), and map `mib` MiB of heap now: a request's allocations then reuse pages that are
/// already mapped instead of faulting them in while timed. No effect on any result.
fn heap_setup(mib: usize) {
    // SAFETY: plain glibc calls with documented parameters (M_ARENA_MAX = -8, M_TRIM_THRESHOLD =
    // -1, M_MMAP_THRESHOLD = -3, at most 32 MiB on 64-bit); a refused setting is only slower.
    unsafe {
        mallopt(-8, 1);
        mallopt(-1, i32::MAX);
        mallopt(-3, 32 << 20);
    }
    let blocks: Vec<Vec<u8>> = (0..mib.div_ceil(16))
        .map(|_| {
            let mut v = vec![0u8; 16 << 20];
            for i in (0..v.len()).step_by(4096) {
                v[i] = 1;
            }
            std::hint::black_box(v)
        })
        .collect();
    drop(blocks);
}

/// The start of a stream request: the circuit, the service (connections opened), `ready`, `go`.
fn stream_start(dir: &Path) -> Result<(Circuit, Service), String> {
    heap_setup(64);
    let circ = Circuit::build();
    let svc = service_for(dir)?;
    svc.warm(par::threads().min(service::WARM_CONNS));
    par::warm();
    say("ready");
    wait_go()?;
    Ok((circ, svc))
}

fn cmd_leaf(dir: &Path) -> Result<(), String> {
    let (circ, svc) = stream_start(dir)?;
    let t = Instant::now();
    let (n, s) = parse_leaf(&std::fs::read_to_string(dir.join("leaf.json")).map_err(|e| format!("leaf.json: {e}"))?)?;
    let p = leaf_signed(&circ, &svc, &s, n)?;
    let f = to_file(&p);
    write(&dir.join("proof.bin"), &f)?;
    warn_caps("leaf proof.bin", &f);
    say("done");
    note!("leaf request {:.4}s {}", t.elapsed().as_secs_f64(), file_summary(&f, &p));
    Ok(())
}

fn cmd_node(dir: &Path) -> Result<(), String> {
    let (_circ, svc) = stream_start(dir)?;
    let t = Instant::now();
    let c1 = read_hex32(&dir.join("child1.stmt"))?;
    let c2 = read_hex32(&dir.join("child2.stmt"))?;
    let (n1, n2) = (dir.join("child1.bin"), dir.join("child2.bin"));
    let (f1, f2) = (read(&n1)?, read(&n2)?);
    let bad = |p: &Path| format!("{}: not a signed-proof file", p.display());
    let (v1, v2) = (make::view(&f1).ok_or_else(|| bad(&n1))?, make::view(&f2).ok_or_else(|| bad(&n2))?);
    let t_read = t.elapsed().as_secs_f64();
    let mut sign0 = 0.0;
    let mut cost = make::NodeCost::default();
    let sigma0 = &mut || {
        let t = Instant::now();
        let s = make::sign(&svc, &vec![]);
        sign0 = t.elapsed().as_secs_f64();
        s
    };
    // the bundle straight from the files (written as it is made); the plain node (`n = 0` or
    // `n > 2^12`, D-6; mixed σ0) through `make::node`
    let out = dir.join("proof.bin");
    let f = match make::node_files(&svc, &c1, &v1, &c2, &v2, sigma0, &out, &mut cost)? {
        Some(f) => f,
        None => {
            let (p1, p2) = (from_file(&f1).ok_or_else(|| bad(&n1))?, from_file(&f2).ok_or_else(|| bad(&n2))?);
            let f = to_file(&make::node(&svc, &c1, &p1, &c2, &p2, sigma0, &mut cost)?);
            write(&out, &f)?;
            f
        }
    };
    let t_made = t.elapsed().as_secs_f64();
    warn_caps("node proof.bin", &f);
    say("done");
    note!(
        "node request {:.4}s (read+parse {t_read:.4}s, build+write {:.4}s incl. SIGN [] {sign0:.4}s, SIGN {:.4}s, rest {:.4}s) {}",
        t.elapsed().as_secs_f64(),
        cost.build_s,
        cost.sign_s,
        t.elapsed().as_secs_f64() - t_made,
        from_file(&f).map(|p| file_summary(&f, &p)).unwrap_or_default(),
    );
    Ok(())
}

/// Remove `--oracle X` from the arguments; X or the default.
fn take_oracle(args: &mut Vec<String>, default: &str) -> String {
    match args.iter().position(|a| a == "--oracle") {
        Some(i) if i + 1 < args.len() => {
            let v = args.remove(i + 1);
            args.remove(i);
            v
        }
        _ => default.to_string(),
    }
}

fn run(mut args: Vec<String>) -> Result<ExitCode, String> {
    let ok = Ok(ExitCode::SUCCESS);
    let cmd = args.first().cloned().unwrap_or_default();
    let dflt = if cmd.starts_with("dump-") { "v3" } else { "keyed" };
    let ospec = take_oracle(&mut args, dflt);
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    match a.as_slice() {
        ["setup", _dir] => ok,
        ["tree", dir] => cmd_tree(Path::new(dir)).and(ok),
        ["leaf", dir] => cmd_leaf(Path::new(dir)).and(ok),
        ["node", dir] => cmd_node(Path::new(dir)).and(ok),
        ["verify-native", vk, stmt, file] => {
            let (vk, c) = (hex_arg(vk)?, hex_arg(stmt)?);
            let b = read(Path::new(file))?;
            let t = Instant::now();
            let r = match from_file(&b) {
                None => Err("not a signed-proof file".to_string()),
                Some(p) => acc::acc(&Circuit::build(), &vk, &c, &p),
            };
            note!("verify-native {:.4}s", t.elapsed().as_secs_f64());
            match r {
                Ok(()) => {
                    println!("accept");
                    ok
                }
                Err(e) => {
                    println!("reject: {e}");
                    Ok(ExitCode::from(1))
                }
            }
        }
        ["extract-check", vk, stmt, file] => {
            let (vk, c) = (hex_arg(vk)?, hex_arg(stmt)?);
            let p = read_signed(Path::new(file))?;
            let circ = Circuit::build();
            let r = match format::decode(&p.pi).map(|x| x.0) {
                None => Err("no witness".to_string()),
                Some(format::Wit::Leaf { s, n }) => {
                    if n <= chain::CHAIN_CAP && c == leaf_stmt(&chain_end(&s, n), n) {
                        Ok(())
                    } else {
                        Err("leaf witness not in Rel".into())
                    }
                }
                Some(format::Wit::Node { c1, c2, p1, p2 }) => {
                    if c != node_stmt(&c1, &c2) {
                        Err("node statement".into())
                    } else {
                        acc::acc(&circ, &vk, &c1, &p1)
                            .map_err(|e| format!("child 1: {e}"))
                            .and_then(|_| acc::acc(&circ, &vk, &c2, &p2).map_err(|e| format!("child 2: {e}")))
                    }
                }
            };
            match r {
                Ok(()) => {
                    println!("ok witness in Rel ({})", make::kind(&p.pi));
                    ok
                }
                Err(e) => {
                    println!("fail {e}");
                    Ok(ExitCode::from(1))
                }
            }
        }
        ["info", file] => {
            let b = read(Path::new(file))?;
            let p = from_file(&b).ok_or("not a signed-proof file")?;
            println!("{}", file_summary(&b, &p));
            ok
        }
        ["prove-leaf", start, n, out] => {
            let s = hex_arg(start)?;
            let n: u64 = n.parse().map_err(|_| "N: not a number")?;
            if n > chain::CHAIN_CAP {
                return Err("N > chainCap".into());
            }
            let o = local_or_service(&ospec)?;
            let circ = Circuit::build();
            let t = Instant::now();
            let (pi, tm, _) = prover::prove_leaf(&circ, o.as_ref(), &s, n, false);
            note!("prove-leaf n={n} bytes={} {:.4}s {}", pi.len(), t.elapsed().as_secs_f64(), tm.report());
            write(Path::new(out), &pi)?;
            let h: Digest = pi[48..80].try_into().unwrap();
            println!("{}", hex(&leaf_stmt(&h, n)));
            ok
        }
        ["check-leaf", stmt, pi] => {
            let c = hex_arg(stmt)?;
            let pi = read(Path::new(pi))?;
            let o = local_or_service(&ospec)?;
            match verifier::check_leaf(&Circuit::build(), o.as_ref(), &c, &pi) {
                Ok(q) => {
                    println!("accept queries={q}");
                    ok
                }
                Err(e) => {
                    println!("reject: {e}");
                    Ok(ExitCode::from(1))
                }
            }
        }
        ["prove-signed", start, n, out] => {
            let s = hex_arg(start)?;
            let n: u64 = n.parse().map_err(|_| "N: not a number")?;
            if n > chain::CHAIN_CAP {
                return Err("N > chainCap".into());
            }
            let svc = service()?;
            let p = leaf_signed(&Circuit::build(), &svc, &s, n)?;
            let f = to_file(&p);
            warn_caps(out, &f);
            write(Path::new(out), &f)?;
            println!("{} {}", hex(&leaf_stmt(&chain_end(&s, n), n)), file_summary(&f, &p));
            ok
        }
        ["bench-leaf", n, reps] => {
            let n: u64 = n.parse().map_err(|_| "N: not a number")?;
            let reps: usize = reps.parse().map_err(|_| "REPS: not a number")?;
            if n == 0 || n > chain::CHAIN_CAP {
                return Err("N in [1, chainCap]".into());
            }
            heap_setup(64);
            let circ = Circuit::build();
            let s = kat::kat_rand("bench-leaf", n);
            println!("oracle={ospec} n={n} threads={} clmul={}", par::threads(), field::clmul_on());
            if ospec == "service" {
                let svc = service()?;
                svc.warm(par::threads().min(service::WARM_CONNS));
                for k in 0..reps {
                    let t = Instant::now();
                    let mut cost = make::LeafCost::default();
                    let p = make::leaf(&circ, &svc, &s, n, &mut cost)?;
                    let total = t.elapsed().as_secs_f64();
                    let f = to_file(&p);
                    println!(
                        "rep={k} total_s={total:.4} prove_s={:.4} replay_s={:.4} sign_s={:.4} oracle_s={:.4} {} {} {} {}",
                        cost.prove_s,
                        cost.replay_s,
                        cost.sign_s,
                        cost.oracle_s,
                        cost.phases,
                        cost.oracle,
                        file_summary(&f, &p),
                        svc.report()
                    );
                }
            } else {
                let o = local_or_service(&ospec)?;
                for k in 0..reps {
                    let t = Instant::now();
                    let mut cost = make::LeafCost::default();
                    let (pi, tr) = make::prove_traced(&circ, o.as_ref(), &s, n, &mut cost)?;
                    let total = t.elapsed().as_secs_f64();
                    let qb: usize = tr.iter().map(|(q, _)| q.len()).sum();
                    println!(
                        "rep={k} total_s={total:.4} prove_s={:.4} replay_s={:.4} oracle_s={:.4} {} {} pi_bytes={} trace_entries={} trace_query_bytes={}",
                        cost.prove_s,
                        cost.replay_s,
                        cost.oracle_s,
                        cost.phases,
                        cost.oracle,
                        pi.len(),
                        tr.len(),
                        qb
                    );
                }
            }
            ok
        }
        ["selftest-field"] | ["selftest-field", _] => {
            let count = a.get(1).map_or(Ok(100_000), |c| c.parse()).map_err(|_| "COUNT: not a number")?;
            match field::selftest_dispatch(count) {
                Ok(k) => {
                    println!("pclmulqdq products equal the portable ones on {k} inputs");
                    ok
                }
                Err(e) => {
                    println!("selftest-field: {e}");
                    Ok(ExitCode::from(1))
                }
            }
        }
        ["dump-field"] => {
            print!("{}", kat::dump_field());
            ok
        }
        ["dump-circuit"] => {
            print!("{}", kat::dump_circuit(&Circuit::build()));
            ok
        }
        ["dump-walk"] => {
            print!("{}", kat::dump_walk(&Circuit::build()));
            ok
        }
        ["dump-encode"] => {
            print!("{}", kat::dump_encode());
            ok
        }
        ["dump-mle"] => {
            print!("{}", kat::dump_mle());
            ok
        }
        ["dump-phi"] => {
            print!("{}", kat::dump_phi());
            ok
        }
        ["dump-sumcheck"] => {
            print!("{}", kat::dump_sumcheck());
            ok
        }
        ["dump-transcript"] => {
            print!("{}", kat::dump_transcript(&Circuit::build(), local_or_service(&ospec)?.as_ref()));
            ok
        }
        ["dump-transcript-ops"] => {
            print!("{}", kat::dump_transcript_ops(local_or_service(&ospec)?.as_ref()));
            ok
        }
        ["dump-leaf-trace", dir] => {
            kat::dump_leaf_trace(&Circuit::build(), local_or_service(&ospec)?.as_ref(), dir).map_err(|e| e.to_string())?;
            ok
        }
        ["dump-proof", dir] => {
            print!("{}", kat::dump_proofs(&Circuit::build(), local_or_service(&ospec)?.as_ref(), dir).map_err(|e| e.to_string())?);
            ok
        }
        _ => Err("usage: spartan-srom-prover setup DIR | tree DIR | leaf DIR | node DIR | verify-native VK STMT FILE | \
                  info FILE | prove-leaf [--oracle O] START N OUT | check-leaf [--oracle O] STMT PI | \
                  prove-signed START N OUT | bench-leaf [--oracle O] N REPS | selftest-field [COUNT] | dump-* \
                  (see main.rs)"
            .into()),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(args) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("spartan-srom-prover: {e}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acc::{acc, v};
    use crate::chain::leaf_size;
    use crate::format::{toy_sign, trace_digest};
    use crate::make::{bundle, child, LeafCost};
    use crate::oracle::Seq;

    fn start(i: u8) -> Digest {
        std::array::from_fn(|j| (j as u8).wrapping_mul(13).wrapping_add(i))
    }

    /// A signed proof under the toy key (`format::toy_sign`, seed 9).
    fn toy(pi: Vec<u8>, tr: oracle::Trace) -> (Digest, Signed) {
        let (vk, sig) = toy_sign(9, &trace_digest(&tr));
        (vk, Signed { pi, tr, sig })
    }

    fn leaf(o: &dyn Oracle, circ: &Circuit, s: &Digest, n: u64) -> (Digest, Signed) {
        let (pi, tr) = make::prove_traced_opt(circ, o, s, n, &mut LeafCost::default(), true).unwrap();
        assert_eq!(pi.len(), leaf_size(n));
        let (_, p) = toy(pi, tr);
        (leaf_stmt(&chain_end(s, n), n), p)
    }

    #[test]
    fn leaf_roundtrip_and_canaries() {
        let circ = Circuit::build();
        let o = Local::keyed(&[1u8; 32]);
        for n in [1u64, 2, 3, 16] {
            let (c, p) = leaf(&o, &circ, &start(n as u8), n);
            let (vk, _) = toy_sign(9, &[0; 32]);
            assert_eq!(acc(&circ, &vk, &c, &p), Ok(()), "n = {n}");
            // the trace's length is v3's exact query bound
            assert_eq!(p.tr.len() as u64, acc::q_bound(n));
            let rej = |q: &Signed, c: &Digest| acc(&circ, &vk, c, q).is_err();
            let mut q = p.clone();
            q.pi.push(0);
            assert!(rej(&q, &c), "π+1");
            let mut q = p.clone();
            q.pi.pop();
            assert!(rej(&q, &c), "π-1");
            let mut q = p.clone();
            q.tr[0].1[0] ^= 1;
            assert!(rej(&q, &c), "answer");
            let mut q = p.clone();
            q.tr.push((vec![], [0; 32]));
            assert!(rej(&q, &c), "extra entry");
            let mut c2 = c;
            c2[0] ^= 1;
            assert!(rej(&p, &c2), "statement");
            // a changed answer with a re-signed trace is still rejected (the replay diverges)
            let mut tr = p.tr.clone();
            let k = tr.len() / 2;
            tr[k].1[3] ^= 0x10;
            let (_, q) = toy(p.pi.clone(), tr);
            assert!(rej(&q, &c), "re-signed changed answer");
            for pos in [0usize, 8, 40, 48, 80, 200, p.pi.len() / 2, p.pi.len() - 1] {
                let mut q = p.clone();
                q.pi[pos] ^= 4;
                assert!(rej(&q, &c), "n = {n}: flipped byte {pos}");
            }
        }
    }

    #[test]
    fn clear_leaf_and_n0() {
        let circ = Circuit::build();
        let (vk, s0) = toy_sign(9, &trace_digest(&[]));
        let s = start(3);
        let c = leaf_stmt(&chain_end(&s, 5), 5);
        let pc = Signed { pi: format::encode(&format::Wit::Leaf { s, n: 5 }), tr: vec![], sig: s0.clone() };
        assert_eq!(acc(&circ, &vk, &c, &pc), Ok(()));
        let mut bad = pc.clone();
        bad.pi.pop();
        assert!(acc(&circ, &vk, &c, &bad).is_err());
        // n = 0: the 80-byte header
        let p0 = Signed { pi: prover::leaf_header(&s, 0, &s), tr: vec![], sig: s0.clone() };
        assert_eq!(acc(&circ, &vk, &leaf_stmt(&s, 0), &p0), Ok(()));
        // D-6: a clear leaf of 2^12 steps is accepted, of 2^12 + 1 rejected (true statement)
        let clear = |n: u64| Signed { pi: format::encode(&format::Wit::Leaf { s, n }), tr: vec![], sig: s0.clone() };
        let c4096 = leaf_stmt(&chain_end(&s, 4096), 4096);
        assert_eq!(acc(&circ, &vk, &c4096, &clear(4096)), Ok(()));
        let c4097 = leaf_stmt(&chain_end(&s, 4097), 4097);
        assert_eq!(acc(&circ, &vk, &c4097, &clear(4097)), Err("C: n > 2^12 (D-6)".into()));
    }

    /// D-6 in the bundle branch and in the prover; the trace-length cap `qV` of `acc`.
    #[test]
    fn caps_d6_and_qv() {
        let circ = Circuit::build();
        let (vk, s0) = toy_sign(9, &trace_digest(&[]));
        let (s1, s2) = (start(1), start(2));
        let (n1, n2) = (5000u64, 16u64);
        let (c1, c2) = (leaf_stmt(&chain_end(&s1, n1), n1), leaf_stmt(&chain_end(&s2, n2), n2));
        let slot = |s: Digest, n: u64| Box::new(Signed { pi: format::encode(&format::Wit::Leaf { s, n }), tr: vec![], sig: s0.clone() });
        let w = format::Wit::Node { c1, c2, p1: slot(s1, n1), p2: slot(s2, n2) };
        let mut pi = format::encode(&w);
        pi.extend_from_slice(&[0u8; 1000]);
        let p = Signed { pi, tr: vec![], sig: s0.clone() };
        assert_eq!(make::kind(&p.pi), "B");
        let e = acc(&circ, &vk, &node_stmt(&c1, &c2), &p).unwrap_err();
        assert!(e.contains("2^12"), "{e}");
        // the prover does not bundle a leaf above 2^12 (it would make the plain node)
        let mut big = prover::leaf_header(&s1, n1, &chain_end(&s1, n1));
        big.extend_from_slice(&[0u8; 64]);
        let pl = Signed { pi: big, tr: vec![], sig: s0.clone() };
        assert_eq!(make::kind(&pl.pi), "L");
        assert!(child(&c1, &pl).is_none());
        // a trace of 2^16 + 1 entries is rejected before anything else
        let tr: oracle::Trace = (0..(1 << 16) + 1).map(|_| (vec![], [0u8; 32])).collect();
        let (vk2, q) = toy(vec![0u8; 48], tr);
        let e = acc(&circ, &vk2, &c1, &q).unwrap_err();
        assert!(e.contains("qV"), "{e}");
    }

    /// The smoke shape r = 2, n = 16 under the keyed oracle and the toy key: leaves, level-1
    /// bundles, the root bundle; every one accepted; canaries rejected; the plain node too.
    #[test]
    fn bundles_r2_n16() {
        let circ = Circuit::build();
        let o = Local::keyed(&[2u8; 32]);
        let (vk, s0) = toy_sign(9, &trace_digest(&[]));
        let leaves: Vec<(Digest, Signed)> = (0..4).map(|i| leaf(&o, &circ, &start(i), 16)).collect();
        let mk = |a: &(Digest, Signed), b: &(Digest, Signed)| -> (Digest, Signed) {
            let (pi, tr) = bundle(child(&a.0, &a.1).unwrap(), child(&b.0, &b.1).unwrap(), &s0);
            let c = node_stmt(&a.0, &b.0);
            let (vk2, p) = toy(pi, tr);
            assert_eq!(vk2, vk);
            (c, p)
        };
        let n1 = [mk(&leaves[0], &leaves[1]), mk(&leaves[2], &leaves[3])];
        let root = mk(&n1[0], &n1[1]);
        for (c, p) in leaves.iter().chain(n1.iter()).chain([&root]) {
            assert_eq!(acc(&circ, &vk, c, p), Ok(()));
        }
        assert_eq!(make::kind(&root.1.pi), "B");
        assert_eq!(root.1.tr.len() as u64, 4 * acc::q_bound(16));
        // stream-style: bundle of (bundle, leaf)
        let s3 = mk(&n1[0], &leaves[2]);
        assert_eq!(acc(&circ, &vk, &s3.0, &s3.1), Ok(()));
        let rej = |c: &Digest, q: &Signed| acc(&circ, &vk, c, q).is_err();
        let (c, p) = &root;
        let mut q = p.clone();
        q.pi.push(0);
        assert!(rej(c, &q));
        let mut q = p.clone();
        q.pi.pop();
        assert!(rej(c, &q));
        let mut q = p.clone();
        let k = q.pi.len() / 2;
        q.pi[k] ^= 1;
        assert!(rej(c, &q));
        let mut q = p.clone();
        q.tr[7].1[0] ^= 1;
        assert!(rej(c, &q));
        // swapped children
        let (pi, tr) = bundle(child(&n1[1].0, &n1[1].1).unwrap(), child(&n1[0].0, &n1[0].1).unwrap(), &s0);
        let (_, q) = toy(pi, tr);
        assert!(rej(c, &q));
        // a slot signed by a different σ0 is rejected
        let (_, other) = toy_sign(9, &[7u8; 32]);
        let (pi, tr) = bundle(child(&leaves[0].0, &leaves[0].1).unwrap(), child(&leaves[1].0, &leaves[1].1).unwrap(), &other);
        let (_, q) = toy(pi, tr);
        assert!(rej(&n1[0].0, &q));
        // the plain node of two n = 16 leaves (their traces inside) is above proofCap (route
        // analysis, point 1); of two n = 1 leaves it is accepted, with no query of its own
        let pn = make::plain(&leaves[0].0, &leaves[1].0, &leaves[0].1, &leaves[1].1);
        let (_, q) = toy(pn, vec![]);
        assert_eq!(make::kind(&q.pi), "N");
        assert!(q.pi.len() > format::PROOF_CAP && rej(&n1[0].0, &q));
        let small: Vec<(Digest, Signed)> = (0..2).map(|i| leaf(&o, &circ, &start(i), 1)).collect();
        let pn = make::plain(&small[0].0, &small[1].0, &small[0].1, &small[1].1);
        let (_, q) = toy(pn, vec![]);
        let c = node_stmt(&small[0].0, &small[1].0);
        assert_eq!(acc(&circ, &vk, &c, &q), Ok(()));
        let seq_empty = Seq::new(&[]);
        assert!(v(&circ, &vk, &seq_empty, &c, &q.pi).is_ok());
    }

    #[test]
    fn json_inputs() {
        let s = hex(&start(1));
        assert_eq!(parse_leaf(&format!("{{\"n\": 16, \"start\": \"{s}\"}}")).unwrap(), (16, start(1)));
        let (n, st) = parse_leaves(&format!("{{\"n\": 4, \"starts\": [\"{s}\", \"{s}\"]}}")).unwrap();
        assert_eq!((n, st.len()), (4, 2));
    }
}
