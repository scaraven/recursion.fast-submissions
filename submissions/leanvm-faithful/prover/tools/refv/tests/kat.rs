//! Per-phase KATs (RV2 F4): the honest `T15` proof is accepted; every tamper is rejected at the check that guards
//! the field. `P18` (slow, `--ignored`): the honest proof is accepted and its per-part counts are FORMAT6 §6's table.

use refv::prover::{Cfg, Kat, prove, resign, sign};
use refv::shape::{p18, t15};
use refv::vs::verify_file;
use refv::{Part, Reject};

fn honest(seed: u64) -> (Cfg, Kat) {
    let cfg = Cfg::new(t15(), seed);
    let kat = prove(&cfg);
    (cfg, kat)
}

fn check(cfg: &Cfg, kat: &Kat, file: &[u8]) -> Result<refv::vs::Report, Reject> {
    verify_file(&cfg.sh, &kat.vk, &kat.c, file, Some(&cfg.key))
}

#[test]
fn t15_honest_accepted_and_deterministic() {
    let (cfg, kat) = honest(1);
    let r = check(&cfg, &kat, &kat.file).expect("honest");
    assert_eq!(r.queries, kat.trace.len());
    assert_eq!(r.total().body + cfg.sh.hdr_len(), kat.pi.len());
    assert_eq!(cfg.sh.hdr_len(), 824, "v2.3: phiVars 43");
    let f = cfg.sh.forbidden_lengths();
    assert!(r.total().chain_lengths.iter().all(|l| !f.contains(l)), "T15's length rule");
    // the same bytes again (least nonces, no randomness)
    assert_eq!(prove(&cfg).file, kat.file);
    // and a second seed
    let (cfg2, kat2) = honest(2);
    check(&cfg2, &kat2, &kat2.file).expect("honest seed 2");
}

/// Kind P: one wrong message, the prover continues honestly (re-grinding); V must reject at the guarding check.
#[test]
fn t15_prover_tampers_rejected() {
    let sh = t15();
    for (t, want) in refv::prover::tamper_set(&sh) {
        let mut cfg = Cfg::new(sh.clone(), 1);
        cfg.tamper = Some(t);
        let kat = prove(&cfg);
        let got = check(&cfg, &kat, &kat.file).err();
        assert_eq!(got, Some(want.clone()), "tamper {t:?}");
        eprintln!("{t:?}: {want:?}");
    }
}

/// Kind R: bytes of `π` edited after the fact, trace re-derived from the oracle and re-signed.
#[test]
fn t15_byte_tampers_rejected() {
    let (cfg, kat) = honest(1);
    let sh = &cfg.sh;
    let rep = check(&cfg, &kat, &kat.file).unwrap();
    let hl = sh.hdr_len();
    let at = |p: Part| rep.checkpoints.iter().find(|c| c.part == p).unwrap().body_end + hl;
    // offsets of fields: §6.1 = cap0, nonce, y0; the stub part is empty; §6.5 = its nonce.
    let cap0 = 32usize << sh.levels[0].lv;
    let commit_start = hl;
    let nonce61 = commit_start + cap0;
    let nonce65 = at(Part::Commit);
    let l0_start = at(Part::Batch);
    let fold_nonce = l0_start + 64;
    let mut cases: Vec<(&str, Vec<u8>, Reject)> = Vec::new();
    let edit = |off: usize, x: u8| {
        let mut p = kat.pi.clone();
        p[off] ^= x;
        p
    };
    cases.push(("magic", edit(0, 1), Reject::Magic));
    cases.push(("b = 2", edit(8, 2), Reject::HdrB));
    cases.push(("b = 1 (statement)", edit(8, 1), Reject::Statement));
    cases.push(("n", edit(16, 1), Reject::HdrN));
    cases.push(("h", edit(24, 1), Reject::Statement));
    cases.push(("c' at b = 0", edit(56, 1), Reject::HdrCPrime));
    // `accIn` has no native check (FORMAT6 v2 §2); the seed absorbs it, so the chain moves and §6.1's PoW fails.
    cases.push(("vk", edit(88, 1), Reject::HdrVk));
    cases.push(("accIn pt", edit(120, 1), Reject::Pow(Part::Commit)));
    cases.push(("accIn y", edit(hl - 1, 1), Reject::Pow(Part::Commit)));
    cases.push(("6.1 nonce", edit(nonce61 + 7, 0x80), Reject::Pow(Part::Commit)));
    cases.push(("6.5 nonce", edit(nonce65 + 7, 0x80), Reject::Pow(Part::Batch)));
    cases.push(("6.6 L0 fold nonce", edit(fold_nonce + 7, 0x80), Reject::Pow(Part::Level(0))));
    cases.push(("6.6 L0 v_G (next PoW)", edit(l0_start, 1), Reject::Pow(Part::Level(0))));
    cases.push(("6.1 y0 (next PoW)", edit(nonce61 + 8, 1), Reject::Pow(Part::Batch)));
    let mut longer = kat.pi.clone();
    longer.push(0);
    cases.push(("BODY + 1 byte", longer, Reject::BodyLeft(1)));
    let shorter = kat.pi[..kat.pi.len() - 1].to_vec();
    cases.push(("BODY − 1 byte", shorter, Reject::BodyShort(Part::Tail)));
    cases.push(("HDR cut", kat.pi[..hl - 1].to_vec(), Reject::HdrLen));
    for (name, pi, want) in cases {
        let file = resign(&cfg, &kat.vk, &kat.c, &pi);
        assert_eq!(check(&cfg, &kat, &file).err(), Some(want.clone()), "{name}");
        eprintln!("{name}: {want:?}");
    }
}

/// The signed file and `runSeq`.
#[test]
fn t15_file_tampers_rejected() {
    let (cfg, kat) = honest(1);
    let flen = kat.file.len();
    let edit = |off: usize| {
        let mut f = kat.file.clone();
        f[off] ^= 1;
        f
    };
    // π edited, trace and signature kept: the next query differs from the trace's (runSeq).
    let off_pi_y0 = 8 + cfg.sh.hdr_len() + (32 << cfg.sh.levels[0].lv) + 8;
    assert!(matches!(check(&cfg, &kat, &edit(off_pi_y0)), Err(Reject::TraceMismatch(_, Part::Batch))));
    // an answer edited: the trace digest changes, SigOk fails
    let off_a0 = 8 + kat.pi.len() + 8 + 8 + 7;
    assert_eq!(check(&cfg, &kat, &edit(off_a0)).err(), Some(Reject::Sig));
    // the signature edited
    assert_eq!(check(&cfg, &kat, &edit(flen - 1)).err(), Some(Reject::Sig));
    // the file one byte longer or shorter
    let mut f = kat.file.clone();
    f.push(0);
    assert_eq!(check(&cfg, &kat, &f).err(), Some(Reject::File));
    assert_eq!(check(&cfg, &kat, &kat.file[..flen - 1]).err(), Some(Reject::File));
    // one more trace entry, re-signed: not used up
    let mut tr = kat.trace.clone();
    tr.push((vec![1, 2, 3], [0; 32]));
    assert_eq!(check(&cfg, &kat, &sign(&cfg, &kat.pi, tr)).err(), Some(Reject::TraceLeft(1)));
    // the last entry dropped, re-signed: V asks past the trace
    let mut tr = kat.trace.clone();
    tr.pop();
    assert_eq!(check(&cfg, &kat, &sign(&cfg, &kat.pi, tr)).err(), Some(Reject::TraceShort(Part::Tail)));
    // a true-looking answer that is not the oracle's, re-signed: only the dev key check sees it
    let mut tr = kat.trace.clone();
    tr[0].1[0] ^= 1;
    let f = sign(&cfg, &kat.pi, tr);
    assert_eq!(check(&cfg, &kat, &f).err(), Some(Reject::NotOracle(0)));
    // a query above queryCap
    let mut tr = kat.trace.clone();
    tr.push((vec![0; (1 << 20) + 1], [0; 32]));
    assert_eq!(check(&cfg, &kat, &sign(&cfg, &kat.pi, tr)).err(), Some(Reject::QueryCap(kat.trace.len())));
    // wrong statement or key
    let mut c2 = kat.c;
    c2[0] ^= 1;
    assert_eq!(verify_file(&cfg.sh, &kat.vk, &c2, &kat.file, None).err(), Some(Reject::Statement));
    let mut vk2 = kat.vk;
    vk2[0] ^= 1;
    assert_eq!(verify_file(&cfg.sh, &vk2, &kat.c, &kat.file, None).err(), Some(Reject::Sig));
}

/// FORMAT6 §6's table for the frozen parts at `P18`, from the walk of an honest proof (minutes).
#[test]
#[ignore]
fn p18_honest_counts() {
    let cfg = Cfg::new(p18(), 1);
    let kat = prove(&cfg);
    let r = check(&cfg, &kat, &kat.file).expect("honest P18");
    let s = |p: Part| r.stats.get(&p).cloned().unwrap_or_default();
    let tri = |p: Part| (s(p).body, s(p).queries, s(p).nonces);
    assert_eq!(tri(Part::Seed), (0, 2, 0));
    assert_eq!(tri(Part::Commit), (4_120, 26, 1));
    assert_eq!(tri(Part::Tree), (0, 0, 0));
    assert_eq!(tri(Part::Stub), (0, 0, 0));
    assert_eq!(tri(Part::Batch), (8, 34, 1));
    let lv = [(92_368, 1_702), (33_088, 708), (21_120, 446), (15_520, 314)];
    for (i, (b, q)) in lv.into_iter().enumerate() {
        assert_eq!((s(Part::Level(i)).body, s(Part::Level(i)).queries), (b, q), "level {i}");
    }
    // FORMAT6 counts the tail with level 4
    let (l4, tail) = (s(Part::Level(4)), s(Part::Tail));
    assert_eq!((l4.body + tail.body, l4.queries + tail.queries), (12_128, 248));
    let nonces: usize = (0..5).map(|i| s(Part::Level(i)).nonces).sum::<usize>() + tail.nonces;
    assert_eq!(nonces, 34);
    // RT's static tally of the same items (`fs6::schedule`), an independent reading of §6
    let f = fs6::params::P18;
    let t = |items: &[fs6::schedule::Item]| {
        let (t, _) = fs6::schedule::tally_from(&f, items, 0, false).expect("tally");
        (t.body, t.queries, t.nonces)
    };
    assert_eq!(t(&fs6::schedule::commitment(&f)), tri(Part::Commit));
    assert_eq!(t(&fs6::schedule::ring_switch(&f)), tri(Part::Batch));
    for i in 0..4 {
        assert_eq!(t(&fs6::schedule::opening_level(&f, i)), tri(Part::Level(i)), "fs6 level {i}");
    }
    assert_eq!(t(&fs6::schedule::opening_level(&f, 4)), (l4.body + tail.body, l4.queries + tail.queries, l4.nonces + tail.nonces));
    // §3's length rule on every chain query of the walk
    assert!(r.total().chain_lengths.iter().all(|l| ![64, 256, 368].contains(l)));
    // v2.2.1: six binds; every group with g ≥ 15 grinds on a buffer of at most 56 bytes; level 4's G(13) on 200
    assert_eq!(r.total().binds, 6);
    assert!(r.total().ground_bufs.iter().all(|&(g, b)| g < 15 || b <= 56), "{:?}", r.total().ground_bufs);
    assert!(s(Part::Level(4)).ground_bufs.contains(&(13, 200)));
    eprintln!("P18: |π| {} trace {} file {}", kat.pi.len(), kat.trace.len(), kat.file.len());
}
