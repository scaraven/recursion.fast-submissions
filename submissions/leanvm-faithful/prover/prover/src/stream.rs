//! The v6 stream (PROVER.md §3, FORMAT6 §8): `first /work` and `step /work` (stage R4 on P1's scaffold).
//!
//! Per request:
//! 1. before `ready` (untimed; no socket exists): read `vk.hex`, start the pool's workers, load the circuit `Q`
//!    (R8: from the setup) and its witness plan (`prove6::preload`);
//! 2. `ready`, then wait for `go` on stdin;
//! 3. **node mode (`step`) only, first thing after `go`: `SIGN` with zero items** (FORMAT6 §8, the first of the two
//!    `SIGN`s): its signature is `σ_leaf`, which signs `traceDigest []`;
//! 4. the oracle: with `/work/oracle.key` (a timed pass) queries are answered in-process (`Local`), after a 4-query
//!    known-answer test of the local PRF against the service's `QUERY` (0, 103, 104, 239 bytes; `LVM6_PRF_KAT=0`
//!    skips it); otherwise by the service (`QUERY` batches over the connections). `SIGN` always goes to the service,
//!    one request at a time, awaited, never retried;
//! 5. the statement: `L = leafStmt (dataRoot xs) n`; `c = L` (first) or `nodeStmt prev L` (step), where `prev.bin`
//!    is parsed strictly as a signed proof, its signature checked under `vk`, and its statement (from its `HDR` for
//!    a SNARK proof, from its witness for a `W` proof) checked equal to `prev.stmt`;
//! 6. the proof (`LVM6_PI` unset: the SNARK for `n = 2^18`, `W` otherwise):
//!    - the SNARK (`prove6.rs`, WP R3; `LVM6_PI=snark` forces it): `first` = leaf mode (`b = 0`), `step` = node mode
//!      (`b = 1`) over `prev.bin`, with `σ_leaf` (step 3) and the child's `accOut` written into `STREAM`/`HDR`;
//!    - `w` (also `ws`), **the fallback for every `n ≠ 2^18`** (and forced by `LVM6_PI=w`): the library's witness-sending proof,
//!      as the core's toy prover: leaf `u64 0 ‖ u64 n ‖ xs`, node `u64 1 ‖ c1 ‖ c2 ‖ signedWords prev ‖ signedWords
//!      leaf`; the leaf part is signed with `σ_leaf` (node mode) or with the step's one `SIGN` (leaf mode), the node
//!      with the last `SIGN`, all with empty traces;
//!    - `skel` (dev; any `n`): the SNARK branch's shape without its mathematics: `HDR ‖ BODY` with FORMAT6's fixed
//!      schedule (§6.1, §6.2, §6.3's core, §6.5, §6.6) run on the real transcript, real trees and openings over
//!      skeleton leaves and dummy messages, signed with its own trace (`qS` minus §T). `acc` rejects it (expected):
//!      it exercises the oracle traffic, the trace capture and the `SIGN` order at the real sizes;
//! 7. **last: `SIGN` with the proof's own trace** (its answers compared with the recorded ones, the signature
//!    checked under `vk`); write `proof.bin`, print `done`.
//!
//! Nothing here reads a clock, `/dev/urandom` or a measured quantity into the output; every oracle batch's answers
//! are functions of their queries and every nonce is the least, so the output is the same at any thread count and
//! for either oracle.

use std::io::Write;
use std::time::Instant;

use fs6::params::P18;
use fs6::schedule;

use crate::format::{self, Sig, Signed};
use crate::keccak::{self, Digest};
use crate::oracle::{self, Local, Trace};
use crate::service::{self, Service};

/// One line on stdout, flushed (`ready`, `done`).
fn say(word: &str) {
    let mut o = std::io::stdout().lock();
    let _ = writeln!(o, "{word}");
    let _ = o.flush();
}

/// Block until the runner writes `go` on stdin.
fn wait_go() {
    let mut line = String::new();
    loop {
        line.clear();
        match std::io::stdin().read_line(&mut line) {
            Ok(0) => service::fatal("stdin closed before `go`"),
            Ok(_) if line.trim() == "go" => return,
            Ok(_) => {}
            Err(e) => service::fatal(&format!("stdin: {e}")),
        }
    }
}

pub fn unhex32(s: &str) -> Option<Digest> {
    let s = s.trim_end_matches('\n');
    if s.len() != 64 {
        return None;
    }
    let mut d = [0u8; 32];
    for (i, b) in d.iter_mut().enumerate() {
        *b = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(d)
}

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn read(dir: &str, name: &str) -> Vec<u8> {
    std::fs::read(format!("{dir}/{name}")).unwrap_or_else(|e| service::fatal(&format!("{dir}/{name}: {e}")))
}

fn read_digest(dir: &str, name: &str) -> Digest {
    let b = read(dir, name);
    unhex32(&String::from_utf8_lossy(&b)).unwrap_or_else(|| service::fatal(&format!("{dir}/{name}: not 64 hex")))
}

/// `leaf.json` `{"n": N}` and `leaf.bin` (32 N bytes).
fn read_leaf(dir: &str) -> (u64, Vec<u8>) {
    let j = String::from_utf8_lossy(&read(dir, "leaf.json")).into_owned();
    let at = j.find("\"n\"").unwrap_or_else(|| service::fatal("leaf.json: no \"n\""));
    let rest = j[at + 3..].trim_start_matches([' ', ':', '\t', '\n', '\r']);
    let n: u64 = rest
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| service::fatal("leaf.json: bad n"));
    let xs = read(dir, "leaf.bin");
    if xs.len() as u64 != 32 * n {
        service::fatal(&format!("leaf.bin is {} bytes, not 32 n = {}", xs.len(), 32 * n));
    }
    (n, xs)
}

/// The PRF known-answer test of PROVER.md §3: the local PRF against the service's `QUERY`.
pub fn prf_kat(local: &Local, svc: &Service) -> Result<(), String> {
    use crate::oracle::Oracle;
    for len in [0usize, 103, 104, 239] {
        let q: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(31) ^ 0xA5).collect();
        let (a, b) = (local.ask(&q), svc.ask(&q));
        if a != b {
            return Err(format!("local PRF differs from QUERY at {len} bytes: {} vs {}", hex(&a), hex(&b)));
        }
    }
    Ok(())
}

/// `SIGN` the trace (one request, waited for); its answers must be the ones recorded while proving, and the
/// signature must verify under `vk` (cheap: ≈ 450 permutations).
fn sign_checked(svc: &Service, vk: &Digest, tr: &Trace) -> Sig {
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (answers, sig) = svc.sign(&qs);
    if answers.len() != tr.len() || answers.iter().zip(tr.iter()).any(|(a, (_, b))| a != b) {
        service::fatal("SIGN answers differ from the QUERY answers");
    }
    if !format::sig_ok(vk, &format::trace_digest(tr), &sig) {
        service::fatal("SIGN: the signature does not verify under vk.hex");
    }
    sig
}

/// `signedWords p`: the signed-proof file with `π` and every query zero-padded to whole words (FORMAT.md).
fn app_signed_words(b: &mut Vec<u8>, p: &Signed) {
    let pad = |b: &mut Vec<u8>, x: &[u8]| {
        b.extend_from_slice(&(x.len() as u64).to_le_bytes());
        b.extend_from_slice(x);
        b.resize(b.len() + (8 - x.len() % 8) % 8, 0);
    };
    pad(b, &p.pi);
    b.extend_from_slice(&(p.tr.len() as u64).to_le_bytes());
    for (q, a) in &p.tr {
        pad(b, q);
        b.extend_from_slice(a);
    }
    format::put_sig(b, &p.sig);
}

/// Check `prev.bin` against `prev.stmt` and `vk` (a malformed or foreign child would make a proof `V` rejects:
/// fail here, loudly): the signed-proof file parses strictly, its signature verifies on its trace, and its
/// statement is `prev.stmt`: from `HDR` (`hdrOk`) for a SNARK proof, from the witness for a `W` proof.
fn check_prev(vk: &Digest, prev_stmt: &Digest, prev_bin: &[u8]) -> Signed {
    let p = format::from_file(prev_bin).unwrap_or_else(|| service::fatal("prev.bin: not one signed proof"));
    if !format::sig_ok(vk, &format::trace_digest(&p.tr), &p.sig) {
        service::fatal("prev.bin: its signature does not verify under vk.hex");
    }
    let u64_at = |o: usize| p.pi.get(o..o + 8).map(|b| u64::from_le_bytes(b.try_into().unwrap()));
    let stmt = match (p.pi.first(), u64_at(0)) {
        (Some(b'S'), _) => {
            let (h, _) = schedule::parse_header(&P18, &p.pi).unwrap_or_else(|| service::fatal("prev.bin: bad HDR"));
            if h.vk != *vk {
                service::fatal("prev.bin: its HDR's vk is not vk.hex");
            }
            schedule::hdr_statement(&h)
        }
        (_, Some(0)) => {
            let n = u64_at(8).unwrap_or_else(|| service::fatal("prev.bin: short W leaf"));
            let xs = p.pi.get(16..).filter(|xs| xs.len() as u64 == 32 * n);
            let xs = xs.unwrap_or_else(|| service::fatal("prev.bin: W leaf of the wrong length"));
            keccak::leaf_stmt(&keccak::data_root(xs), n)
        }
        (_, Some(1)) if p.pi.len() >= 72 => keccak::node_stmt(p.pi[8..40].try_into().unwrap(), p.pi[40..72].try_into().unwrap()),
        _ => service::fatal("prev.bin: neither a SNARK nor a W proof"),
    };
    if &stmt != prev_stmt {
        service::fatal(&format!("prev.bin proves {}, not prev.stmt {}", hex(&stmt), hex(prev_stmt)));
    }
    p
}

/// The proof's kind (`LVM6_PI`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    /// Witness-sending.
    W,
    /// The SNARK branch's skeleton (dev).
    Skel,
    /// The SNARK (`prove6`).
    Snark,
    /// Unset: `Snark` for `n = 2^18`, `W` otherwise.
    Auto,
}

/// Whether the SNARK path exists (R3: leaf and node mode, `prove6`).
const SNARK_READY: bool = true;

pub fn run(mode: &str, dir: &str) -> i32 {
    let t_start = Instant::now();
    // untimed start-up: nothing here may touch the socket
    let vk = read_digest(dir, "vk.hex");
    parallel::init();
    let asked = match std::env::var("LVM6_PI").as_deref() {
        Err(_) => Kind::Auto,
        Ok("w") | Ok("ws") => Kind::W,
        Ok("skel") => Kind::Skel,
        Ok("snark") => Kind::Snark,
        Ok(k) => service::fatal(&format!("LVM6_PI={k}: w, skel or snark")),
    };
    let node = mode == "step";
    // R8: the circuit `Q` (the setup's raw form, else the embedded one) and its witness plan, before `ready`: start-up
    // is untimed, and neither depends on the request's inputs
    if matches!(asked, Kind::Auto | Kind::Snark) {
        crate::prove6::preload();
    }
    let startup_s = t_start.elapsed().as_secs_f64();
    say("ready");
    wait_go();
    let t0 = Instant::now();

    // FORMAT6 §8 (1): node mode, first thing after `go`: SIGN with zero items -> σ_leaf
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| "/run/rf/oracle.sock".into());
    let svc: &'static Service = Box::leak(Box::new(Service::connect(&path).unwrap_or_else(|e| service::fatal(&e))));
    let sigma_leaf = node.then(|| sign_checked(svc, &vk, &vec![]));

    // the oracle, after `go`
    let key = std::fs::read(format!("{dir}/oracle.key")).ok();
    let timed = key.is_some();
    match key {
        Some(k) => {
            let k = unhex32(&String::from_utf8_lossy(&k)).unwrap_or_else(|| service::fatal("oracle.key: not 64 hex"));
            let local = Local::keyed(&k);
            if std::env::var("LVM6_PRF_KAT").map_or(true, |v| v != "0") {
                prf_kat(&local, svc).unwrap_or_else(|e| service::fatal(&e));
            }
            oracle::install(Box::new(local));
        }
        None => oracle::install(Box::new(Service::connect(&path).unwrap_or_else(|e| service::fatal(&e)))),
    }

    // the statement
    let (n, xs) = read_leaf(dir);
    let h = keccak::data_root(&xs);
    let leaf = keccak::leaf_stmt(&h, n);
    let prev = node.then(|| {
        let p = read_digest(dir, "prev.stmt");
        let signed = check_prev(&vk, &p, &read(dir, "prev.bin"));
        (p, signed)
    });
    let c = match &prev {
        None => leaf,
        Some((p, _)) => keccak::node_stmt(p, &leaf),
    };
    let t_stmt = t0.elapsed().as_secs_f64();

    // the branch: W for every n ≠ 2^18 and until the SNARK path exists; `skel` on request (dev, any n)
    let kind = match asked {
        Kind::Auto if SNARK_READY && n == 1 << P18.log_blocks => Kind::Snark,
        Kind::Auto => Kind::W,
        Kind::Snark if n != 1 << P18.log_blocks => service::fatal("LVM6_PI=snark needs n = 2^18"),
        k => k,
    };
    let mut detail = String::new();
    let file = match kind {
        Kind::W => {
            let mut pi_leaf = Vec::with_capacity(16 + xs.len());
            pi_leaf.extend_from_slice(&0u64.to_le_bytes());
            pi_leaf.extend_from_slice(&n.to_le_bytes());
            pi_leaf.extend_from_slice(&xs);
            match (&prev, sigma_leaf) {
                (None, _) => format::to_file(&Signed { pi: pi_leaf, tr: vec![], sig: sign_checked(svc, &vk, &vec![]) }),
                (Some((p, prev_p)), Some(sig_leaf)) => {
                    let leaf_p = Signed { pi: pi_leaf, tr: vec![], sig: sig_leaf };
                    let mut pi = Vec::new();
                    pi.extend_from_slice(&1u64.to_le_bytes());
                    pi.extend_from_slice(p);
                    pi.extend_from_slice(&leaf);
                    app_signed_words(&mut pi, prev_p);
                    app_signed_words(&mut pi, &leaf_p);
                    format::to_file(&Signed { pi, tr: vec![], sig: sign_checked(svc, &vk, &vec![]) })
                }
                (Some(_), None) => unreachable!(),
            }
        }
        Kind::Snark => {
            let child = prev.as_ref().map(|(p, signed)| crate::prove6::Child {
                c_prev: *p,
                signed,
                sigma_leaf: sigma_leaf.as_ref().expect("node mode signs σ_leaf first"),
                acc_out: crate::prove6::child_acc_out(signed),
            });
            let pr = crate::prove6::prove6(n, &xs, &vk, child.as_ref(), &crate::prove6::Opts::default());
            debug_assert_eq!(pr.c, c, "the SNARK's statement is the driver's");
            let tl: Vec<String> = pr.times.iter().map(|(k, s)| format!("{k} {s:.3}")).collect();
            detail = format!(" |pi| {} qS {} claims {} | {}", pr.pi.len(), pr.trace.len(), pr.claims, tl.join(", "));
            // a fresh connection for the last SIGN: the proof takes longer than the service's I/O timeout
            // (`rf-oracle --io-timeout`, default 60 s), which would close the idle connection of step 3
            let svc_last = Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
            let sig = sign_checked(&svc_last, &vk, &pr.trace);
            format::to_file(&Signed { pi: pr.pi, tr: pr.trace, sig })
        }
        Kind::Auto => unreachable!(),
        Kind::Skel => {
            let c_prev = prev.as_ref().map_or([0; 32], |(p, _)| *p);
            let hdr = schedule::header(&P18, u64::from(node), n, &h, &c_prev, &vk, None);
            let mut t = fs6::Transcript::start(oracle::get(), &hdr);
            let items: Vec<schedule::Item> = schedule::fixed_parts(&P18, true).into_iter().flat_map(|(_, v)| v).collect();
            // σ_leaf enters the trees' seeds, as the real prover writes it into STREAM before the commitment
            let extra = sigma_leaf.as_ref().map_or(0, |s| {
                let mut b = Vec::new();
                format::put_sig(&mut b, s);
                u64::from_le_bytes(keccak::keccak256(&b)[..8].try_into().unwrap())
            });
            let rep = schedule::run_skeleton(&mut t, &P18, &items, extra);
            let (nonces, binds) = (t.nonces, t.binds);
            let (body, tr) = t.finish();
            let mut pi = hdr;
            pi.extend_from_slice(&body);
            detail = format!(
                " |pi| {} |BODY| {} qS {} nonces {} binds {} candidates {} trees {:.3} s",
                pi.len(),
                body.len(),
                tr.len(),
                nonces,
                binds,
                rep.grind_candidates,
                rep.tree_s
            );
            let sig = sign_checked(svc, &vk, &tr);
            format::to_file(&Signed { pi, tr, sig })
        }
    };
    std::fs::write(format!("{dir}/proof.bin"), &file).unwrap_or_else(|e| service::fatal(&format!("proof.bin: {e}")));
    let t_done = t0.elapsed().as_secs_f64();
    eprintln!(
        "lvm6-prover {mode} [{}] {} {kind:?}: n {n} c {} |file| {}{detail} startup {startup_s:.3} s stmt {t_stmt:.3} s total {t_done:.3} s threads {} conns {} signs {}; {}",
        crate::VARIANT,
        if timed { "timed (oracle.key)" } else { "service run" },
        hex(&c),
        file.len(),
        parallel::num_threads(),
        fs6::oracle::conns(),
        svc.signs.load(std::sync::atomic::Ordering::Relaxed),
        oracle::report()
    );
    // the log first: the runner kills the sandbox at `done`
    say("done");
    0
}
