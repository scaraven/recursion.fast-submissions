//! `refv-tree DIR` (WP R2, dev): accept or reject `DIR/tree6.signed` (`lvm6-prover tree6`: `HDR ‖ §6.1 ‖ §6.2 ‖
//! §6.5's group`) as `acc` would, the signature and `runSeq` included, with `V_S`'s §6.2 checks (`refv::tree`);
//! then check the 13 point claims and the 64 slices §6.2 leaves against `DIR/stack.bin` (a native stand-in for the
//! PCS, as TOY2's exact oracle). Exit 0 iff both pass.

use refv::chain::{RecordAsk, TraceAsk};
use refv::format::{QUERY_CAP, Signed, from_file, sig_ok, to_file, toy_sign, trace_digest};
use refv::{Reject, unhex32};

fn main() {
    let dir = std::path::PathBuf::from(std::env::args().nth(1).expect("refv-tree DIR"));
    let meta = std::fs::read_to_string(dir.join("meta.txt")).expect("meta.txt");
    let field = |k: &str| {
        meta.lines().find_map(|l| l.strip_prefix(&format!("{k} "))).unwrap_or_else(|| panic!("meta {k}")).to_string()
    };
    let log_blocks: u32 = field("log_blocks").parse().unwrap();
    let (vk, c, key) = (unhex32(&field("vk")).unwrap(), unhex32(&field("c")).unwrap(), unhex32(&field("key")).unwrap());
    // P18 at `2^log_blocks` blocks: `M = log_blocks + 7`, level 0's cap as `fs6` sizes it.
    let mut sh = refv::shape::active();
    sh.log_blocks = log_blocks;
    sh.stack_log = log_blocks as usize + 7;
    let ht = sh.stack_log as u32 - 6 + sh.levels[0].log_inv_rate;
    sh.levels[0].ht = ht;
    sh.levels[0].lv = fs6::log_cap_for_height(&fs6::params::SHAPE, ht);
    let file = std::fs::read(dir.join("tree6.signed")).expect("tree6.signed");
    // `--flips K`: K byte flips spread over §6.2's bytes of `π` (plus its first and last byte), each re-derived
    // through the oracle and re-signed with the toy signer (seed 7, `tree6.rs`), each expected to be rejected.
    if let Some(k) = std::env::args().position(|a| a == "--flips").and_then(|i| std::env::args().nth(i + 1)) {
        let k: usize = k.parse().unwrap();
        let s = from_file(&file).expect("honest file");
        let o = fs6::oracle::Local::keyed(&key);
        let start = sh.hdr_len() + (32 << sh.levels[0].lv) + 8 + 16;
        let len = s.pi.len() - start - 8; // §6.5's nonce is the last 8 bytes
        let mut offs: Vec<usize> = (0..k).map(|j| start + j * (len - 1) / (k - 1).max(1)).collect();
        offs.dedup();
        let mut tally = std::collections::BTreeMap::<String, usize>::new();
        let mut accepted = 0;
        for &off in &offs {
            let mut pi = s.pi.clone();
            pi[off] ^= 0x01;
            let mut ask = RecordAsk { o: &o, tr: Vec::new() };
            let _ = refv::tree::verify_tree_pi(&sh, &vk, &c, &pi, &mut ask);
            let (_, sig) = toy_sign(7, &trace_digest(&ask.tr));
            let f = to_file(&Signed { pi: pi.clone(), tr: ask.tr, sig });
            let s2 = from_file(&f).unwrap();
            let mut ta = TraceAsk::new(&s2.tr, Some(&key));
            match refv::tree::verify_tree_pi(&sh, &vk, &c, &s2.pi, &mut ta).and_then(|r| ta.finish().map(|_| r)) {
                Ok(_) => {
                    accepted += 1;
                    println!("ACCEPTED flip at {off}");
                }
                Err(e) => {
                    let key: String = format!("{e:?}").chars().filter(|c| !c.is_ascii_digit()).collect();
                    *tally.entry(key).or_default() += 1;
                }
            }
        }
        println!("flips {} accepted {accepted} rejected {:?}", offs.len(), tally);
        std::process::exit(i32::from(accepted > 0));
    }
    let t = std::time::Instant::now();
    let verdict = (|| -> Result<refv::tree::TreeReport, Reject> {
        let s = from_file(&file).ok_or(Reject::File)?;
        for (i, (q, _)) in s.tr.iter().enumerate() {
            if q.len() > QUERY_CAP {
                return Err(Reject::QueryCap(i));
            }
        }
        if !sig_ok(&vk, &trace_digest(&s.tr), &s.sig) {
            return Err(Reject::Sig);
        }
        let mut ask = TraceAsk::new(&s.tr, Some(&key));
        let rep = refv::tree::verify_tree_pi(&sh, &vk, &c, &s.pi, &mut ask)?;
        ask.finish()?;
        Ok(rep)
    })();
    let vs_s = t.elapsed().as_secs_f64();
    let rep = match verdict {
        Ok(r) => r,
        Err(e) => {
            println!("REJECT V_S {e} ({vs_s:.3} s)");
            std::process::exit(1);
        }
    };
    let words = std::fs::read(dir.join("stack.bin")).expect("stack.bin");
    let q: Vec<u64> = words.chunks_exact(8).map(|b| u64::from_le_bytes(b.try_into().unwrap())).collect();
    assert_eq!(q.len(), 1usize << sh.stack_log, "stack.bin is the whole 2^M stack");
    let t = std::time::Instant::now();
    let fails = refv::tree::check_claims(&rep.out, &q);
    let claims_s = t.elapsed().as_secs_f64();
    let line = format!(
        "body {} queries {} | §6.2: body {} queries {} nonces {} | V_S {vs_s:.3} s, claims {claims_s:.3} s",
        rep.body, rep.queries, rep.tree_body, rep.tree_queries, rep.tree_nonces
    );
    if fails.is_empty() {
        println!("ACCEPT {line}");
    } else {
        println!("REJECT claims {} | {line}", fails.join(","));
        std::process::exit(1);
    }
}
