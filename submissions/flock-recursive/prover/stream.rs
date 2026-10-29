//! The stream (`harness/PROVER.md` §3): `prover first /work` (two chains → two aggregates → `N8`)
//! and `prover step /work` (`prev.bin` + one chain → an aggregate → `N2` when it has `≤ 2`
//! segments, else `N4`), each through the oracle service: prove with the service's answers recorded,
//! the verifier's trace by replay, `SIGN`, `proof.bin`. A node's trace is the verifier program's
//! queries (`ir::run` of the kind's program without its node ops: the item sequence does not
//! depend on them), replayed from the prover's.

use crate::blake2s::{leaf_stmt, Digest};
use crate::oracle::{Recorder, Replay};
use crate::{agg, circuit, format, ir, leaf, node, nodeprove, params, plan, service};
use std::path::Path;
use std::time::Instant;

fn unhex(s: &str) -> Vec<u8> {
    let s = s.trim();
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex")).collect()
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// A chain file `{"n": N, "start": "HEX"}`.
pub fn read_chain(p: &Path) -> (u64, Digest) {
    let t = std::fs::read_to_string(p).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", p.display())));
    let after = |k: &str| -> &str { &t[t.find(k).unwrap_or_else(|| service::fatal(&format!("{}: no {k}", p.display()))) + k.len()..] };
    let n: u64 = after("\"n\"").trim_start_matches([' ', ':']).split(|c: char| !c.is_ascii_digit()).next().unwrap().parse().expect("n");
    let s = after("\"start\"");
    let q = s.find('"').expect("start") + 1;
    let start: Digest = unhex(&s[q..q + 64]).try_into().expect("start: 32 bytes");
    (n, start)
}

/// The signed aggregate of the chain `(n, start)` and its statement.
pub fn agg_signed(svc: &service::Service, circ: &circuit::Circuit, vk: &Digest, start: &Digest, n: u64) -> (format::Signed, Digest) {
    let c = leaf::seg_c(start, n);
    let mut rec = Recorder::new(svc);
    rec.batch_max = 128;
    let (pi, _) = agg::prove(&rec, circ, vk, start, n, agg::M_SEG);
    let table = rec.into_table();
    let mut rp = Replay::new(&table);
    rp.fallback = Some(svc);
    if !agg::verify(&rp, circ, vk, &c, &pi) {
        service::fatal("the aggregate's verifier rejects (replay)");
    }
    let (tr, missing) = rp.finish();
    if missing != 0 {
        service::fatal(&format!("{missing} aggregate queries were not asked while proving"));
    }
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (_, sig) = svc.sign(&qs);
    (format::Signed { pi, tr, sig }, c)
}

/// The signed node of kind `k` over the previous node (if any) and the aggregates.
fn node_signed(svc: &service::Service, k: node::NK, vk: &Digest, prev: Option<(&format::Signed, Digest)>, aggs: &[(format::Signed, Digest)], tm: &mut Vec<(&'static str, f64)>) -> (format::Signed, Digest) {
    let mut t = Instant::now();
    let mut mark = |n: &'static str, t: &mut Instant| {
        tm.push((n, t.elapsed().as_secs_f64()));
        *t = Instant::now();
    };
    let nd = plan::node_data();
    let kt = nd.kind_tab(k);
    let (circ, gcirc, base) = (circuit::Circuit::build(), node::general_circuit(), circuit::Circuit::build_base());
    mark("load", &mut t);
    let ains: Vec<node::AggIn> = aggs.iter().map(|(s, _)| node::agg_in(s)).collect();
    let prev_in = prev.map(|(ps, c)| {
        let pk = node::NK::of_byte(ps.pi[0]).unwrap_or_else(|| service::fatal("prev.bin: not a node proof"));
        let ctx = std::sync::Arc::new(ir::NodeCtx { k: pk, protos: nd.protos.clone(), kt: std::sync::Arc::new(nd.kind_tab(pk)) });
        node::PrevIn { signed: ps, c, ix: [1, 0, 2][pk as usize], ctx, base: &base }
    });
    let w = node::witness(k, vk, prev_in.as_ref(), &ains, &nd.protos, &nd.texts, &gcirc, &circ);
    for (v, st) in w.mstats.iter().enumerate() {
        if st.failed_rows != 0 || st.conflicts != 0 || !st.first_conflicts.is_empty() {
            service::fatal(&format!("node witness slot {v}: {st:?}"));
        }
    }
    mark("witness", &mut t);
    let cs: [Digest; 2] = match &prev_in {
        Some(p) => [p.c, aggs[0].1],
        None => [aggs[0].1, aggs[1].1],
    };
    let mut rec = Recorder::new(svc);
    rec.batch_max = 128;
    let ni = nodeprove::NodeIn { k, vk: *vk, cs, w: &w, mats: nodeprove::Mats { k, kt: &kt, protos: &nd.protos }, base: &base };
    let (pi, ptm) = nodeprove::prove(&rec, &ni);
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("node {} phases {}", k.name(), ptm.report());
    }
    mark("prove", &mut t);
    let c = nodeprove::node_c(&cs);
    let table = rec.into_table();
    let mut rp = Replay::new(&table);
    rp.fallback = Some(svc);
    let _ = ir::run(&nd.node_program(k), &base, &rp, vk, &c, &pi);
    let (tr, missing) = rp.finish();
    if missing != 0 || tr.len() != params::N_ITEMS {
        service::fatal(&format!("node trace: {} queries, {missing} not asked while proving", tr.len()));
    }
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (_, sig) = svc.sign(&qs);
    mark("trace_sign", &mut t);
    (format::Signed { pi, tr, sig }, c)
}

/// `prover first /work` and `prover step /work`.
pub fn run(first: bool, work: &Path) {
    let t0 = Instant::now();
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    svc.warm(crate::par::threads().min(service::MAX_CONNS));
    crate::par::warm();
    let vk = svc.vk();
    let circ = circuit::Circuit::build();
    // decode the node data while the aggregates are proved
    let nd = std::thread::spawn(|| {
        plan::node_data();
    });
    let mut tm: Vec<(&'static str, f64)> = Vec::new();
    let mut t = Instant::now();
    let (file, c, k) = if first {
        let a = read_chain(&work.join("chainA.json"));
        let b = read_chain(&work.join("chainB.json"));
        let aggs = vec![agg_signed(&svc, &circ, &vk, &a.1, a.0), agg_signed(&svc, &circ, &vk, &b.1, b.0)];
        tm.push(("aggregates", t.elapsed().as_secs_f64()));
        t = Instant::now();
        nd.join().unwrap();
        tm.push(("data_wait", t.elapsed().as_secs_f64()));
        let (s, c) = node_signed(&svc, node::NK::N8, &vk, None, &aggs, &mut tm);
        (format::to_file(&s), c, node::NK::N8)
    } else {
        let prev_c: Digest = unhex(&std::fs::read_to_string(work.join("prev.stmt")).expect("prev.stmt")).try_into().expect("prev.stmt");
        let prev = format::from_file(&std::fs::read(work.join("prev.bin")).expect("prev.bin")).unwrap_or_else(|| service::fatal("prev.bin"));
        let (n, s) = read_chain(&work.join("chain.json"));
        let k = if agg::split(n, agg::M_SEG).len() <= 2 { node::NK::N2 } else { node::NK::N4 };
        let aggs = vec![agg_signed(&svc, &circ, &vk, &s, n)];
        tm.push(("aggregate", t.elapsed().as_secs_f64()));
        t = Instant::now();
        nd.join().unwrap();
        tm.push(("data_wait", t.elapsed().as_secs_f64()));
        let (sg, c) = node_signed(&svc, k, &vk, Some((&prev, prev_c)), &aggs, &mut tm);
        (format::to_file(&sg), c, k)
    };
    std::fs::write(work.join("proof.bin"), &file).expect("proof.bin");
    let total = t0.elapsed().as_secs_f64();
    eprintln!(
        "STREAM {} kind={} total_s={total:.3} {} stmt={} file={} peak_rss_mb={:.0}",
        if first { "first" } else { "step" },
        k.name(),
        tm.iter().map(|(n, s)| format!("{n}={s:.3}")).collect::<Vec<_>>().join(" "),
        hex(&c),
        file.len(),
        crate::peak_rss_mb()
    );
    let _ = leaf_stmt;
}
