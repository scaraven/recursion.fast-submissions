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

/// What a request needs that does not depend on its inputs, built before `ready` (untimed: the
/// node data decoded, the kind tables, the circuits, the inactive solve plans, the heap).
pub struct Pre {
    pub nd: &'static plan::NodeData,
    pub kts: [std::sync::Arc<crate::mfill::KindTab>; 3],
    pub circ: circuit::Circuit,
    pub gcirc: circuit::Circuit,
    pub base: circuit::Circuit,
}

impl Pre {
    pub fn new() -> Pre {
        let sp = crate::prof::span("pre.node_data");
        let nd = plan::node_data();
        drop(sp);
        // P2: the kind tables beside the plans (independent; both on the pool)
        let kts = std::thread::scope(|sc| {
            let h = sc.spawn(|| {
                let _sp = crate::prof::span("pre.kind_tabs");
                plan::kind_tabs_static().clone()
            });
            // the solve orders `prover setup` recorded, else the inactive ones now
            let sp = crate::prof::span("pre.load_plans");
            load_setup_plans(nd);
            drop(sp);
            let sp = crate::prof::span("pre.warm_plans");
            node::warm_plans(&nd.protos);
            drop(sp);
            h.join().unwrap_or_else(|_| service::fatal("the kind tables panicked"))
        });
        let gcirc = node::general_circuit();
        node::warm_trace(&gcirc);
        Pre { nd, kts, circ: circuit::Circuit::build(), gcirc, base: circuit::Circuit::build_base() }
    }
    fn kt(&self, k: node::NK) -> &std::sync::Arc<crate::mfill::KindTab> {
        &self.kts[k as usize]
    }
}

/// The solve orders file in the setup directory.
const PLANS: &str = "plans.bin";
/// Their level schedules (pass 13).
const SCHED: &str = "sched.bin";

/// Load the solve orders `prover setup` stored in `$RF_SETUP` (if any, and of this node data).
pub fn load_setup_plans(nd: &plan::NodeData) -> bool {
    let dir = std::env::var_os("RF_SETUP");
    let loaded = dir.as_ref().and_then(|d| plan::read_par(&Path::new(d).join(PLANS))).is_some_and(|b| crate::mfill::load_plans(&nd.protos, &plan::data_tag(), &b));
    // the inactive fills, recorded with the plans (same node data)
    if loaded {
        if let Some(b) = dir.as_ref().and_then(|d| plan::read_par(&Path::new(d).join(SCHED))) {
            crate::mfill::load_scheds(&nd.protos, &plan::data_tag(), &b);
        }
        for (i, p) in nd.protos.iter().enumerate() {
            if let Some(b) = dir.as_ref().and_then(|d| plan::read_par(&Path::new(d).join(format!("inactive-p{i}.bin")))) {
                crate::mfill::load_inactive(p, &b);
            }
        }
    }
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("setup plans loaded: {loaded}");
    }
    loaded
}

/// A signed node of kind `k` over the oracle `o` with the test signer (`prover setup`'s toy chain).
fn toy_node(o: &dyn crate::oracle::Oracle, pre: &Pre, k: node::NK, vk: &Digest, prev: Option<(&format::Signed, Digest)>, aggs: &[(format::Signed, Digest)]) -> (format::Signed, Digest) {
    let ains: Vec<node::AggIn> = aggs.iter().map(|(s, _)| node::agg_in(s)).collect();
    let pin = prev.map(|(ps, c)| prev_in(pre, ps, c));
    let w = node::witness(k, vk, pin.as_ref(), &ains, &pre.nd.protos, &pre.nd.texts, &pre.gcirc, &pre.circ, None);
    let cs: [Digest; 2] = match &pin {
        Some(p) => [p.c, aggs[0].1],
        None => [aggs[0].1, aggs[1].1],
    };
    let ni = nodeprove::NodeIn { k, vk: *vk, cs, w: &w, mats: nodeprove::Mats { k, kt: pre.kt(k), protos: &pre.nd.protos }, kts: [&*pre.kts[0], &*pre.kts[1], &*pre.kts[2]], base: &pre.base };
    let (pi, _) = nodeprove::prove(o, &ni);
    let c = nodeprove::node_c(&cs);
    let tape = crate::oracle::Tape::new(o);
    let _ = ir::run(&pre.nd.node_program(k), &pre.base, &tape, vk, &c, &pi);
    let tr = tape.into_trace();
    let (_, sig) = format::toy_sign(9, &format::trace_digest(&tr));
    (format::Signed { pi, tr, sig }, c)
}

/// A signed aggregate of `n` steps from `s` over `o` with the test signer.
fn toy_agg(o: &dyn crate::oracle::Oracle, circ: &circuit::Circuit, vk: &Digest, s: &Digest, n: u64) -> (format::Signed, Digest) {
    let (pi, _) = agg::prove(o, circ, vk, s, n, agg::M_SEG);
    let c = leaf::seg_c(s, n);
    let tape = crate::oracle::Tape::new(o);
    if !agg::verify(&tape, circ, vk, &c, &pi) {
        service::fatal("setup: the toy aggregate's verifier rejects");
    }
    let tr = tape.into_trace();
    let (_, sig) = format::toy_sign(9, &format::trace_digest(&tr));
    (format::Signed { pi, tr, sig }, c)
}

/// **`prover setup DIR`** (untimed, no service): the solve orders of every slot fill a request can
/// meet, each recorded on its own key from a toy chain (a local oracle, the test signer): `N8` over
/// two aggregates (prototype 1 at `L30`), `N2` and `N4` over it (prototype 0 after `N8`; prototype 1
/// at a partial `L32`), a witness over `L32 + L31`, then prototype 0's fill after the `N2` and the
/// `N4`; stored as `DIR/plans.bin`, with the inactive fills (`inactive-p{0,1}.bin`) and the decoded
/// node data's image (`nodedata.bin`, pass 12). A request replays them (`mfill::fill`
/// checks every row and solves afresh if a replay falls short).
pub fn setup(dir: &Path) {
    let t = Instant::now();
    crate::mfill::set_exact_plans(true);
    let pre = Pre::new();
    let o = crate::oracle::Local::keyed(&[0x5Au8; 32]);
    let (vk, _) = format::toy_sign(9, &[0u8; 32]);
    let st = |i: u8| -> Digest { std::array::from_fn(|j| j as u8 ^ i) };
    let say = |w: &str| eprintln!("setup: {w} {:.1}s", t.elapsed().as_secs_f64());
    let ok = |f: &node::Fill, w: &str| {
        if f.1.failed_rows != 0 || f.1.conflicts != 0 || !f.1.first_conflicts.is_empty() {
            service::fatal(&format!("setup: {w}: {:?}", f.1));
        }
    };
    // N8 over two one-segment aggregates (prototype 1 at L30)
    let a = [toy_agg(&o, &pre.circ, &vk, &st(1), 3), toy_agg(&o, &pre.circ, &vk, &st(2), 5)];
    let n8 = toy_node(&o, &pre, node::NK::N8, &vk, None, &a);
    say("N8");
    // N2 over it, a partial L32 (prototype 0 after N8; prototype 1 at L32)
    let n2 = toy_node(&o, &pre, node::NK::N2, &vk, Some((&n8.0, n8.1)), &[toy_agg(&o, &pre.circ, &vk, &st(3), 200_003)]);
    say("N2");
    // N4 over it: L32, L32, L30
    let n4 = toy_node(&o, &pre, node::NK::N4, &vk, Some((&n8.0, n8.1)), &[toy_agg(&o, &pre.circ, &vk, &st(4), 2 * (1 << 18) + 9)]);
    say("N4");
    // prototype 1 at L31: a witness over L32 + L31 (no proof)
    let a31 = [toy_agg(&o, &pre.circ, &vk, &st(5), (1 << 18) + 100_000)];
    let ains: Vec<node::AggIn> = a31.iter().map(|(s, _)| node::agg_in(s)).collect();
    let pin = prev_in(&pre, &n8.0, n8.1);
    let w = node::witness(node::NK::N2, &vk, Some(&pin), &ains, &pre.nd.protos, &pre.nd.texts, &pre.gcirc, &pre.circ, None);
    if w.mstats.iter().any(|s| s.failed_rows != 0 || s.conflicts != 0) {
        service::fatal("setup: the L31 witness's fills");
    }
    say("L31");
    // prototype 0 after N2 and after N4
    for (p, w) in [(&n2, "slot 0 after N2"), (&n4, "slot 0 after N4")] {
        ok(&node::slot0_fill(&prev_in(&pre, &p.0, p.1), &vk, &pre.nd.protos, &pre.nd.texts, &pre.circ), w);
    }
    let b = crate::mfill::save_plans(&pre.nd.protos, &plan::data_tag());
    std::fs::create_dir_all(dir).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", dir.display())));
    std::fs::write(dir.join(PLANS), &b).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", dir.display())));
    // the orders' level schedules (pass 13; a request loads them instead of building them)
    std::fs::write(dir.join(SCHED), crate::mfill::save_scheds(&pre.nd.protos, &plan::data_tag())).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", dir.display())));
    // the decoded node data's image (pass 12; not with `FLOCK_NODE_DUMP`, whose tag is fixed)
    if std::env::var_os("FLOCK_NODE_DUMP").is_none() {
        std::fs::write(dir.join(plan::IMAGE), plan::save_image(pre.nd, &plan::data_tag())).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", dir.display())));
    }
    // prototype 1 only: prototype 0 (the previous node's slot) is never inactive (E1b: its phantom
    // stream is a segment's, so its inactive fill would not hold)
    for (i, p) in pre.nd.protos.iter().enumerate().skip(1) {
        let (v, st) = crate::mfill::fill(p, None, crate::node::phantom_arena());
        if st.failed_rows != 0 || st.conflicts != 0 {
            service::fatal(&format!("setup: prototype {i}'s inactive fill: {st:?}"));
        }
        std::fs::write(dir.join(format!("inactive-p{i}.bin")), crate::mfill::save_inactive(&v)).unwrap_or_else(|e| service::fatal(&format!("{}: {e}", dir.display())));
    }
    let have: Vec<String> = pre.nd.protos.iter().map(|p| p.plan.iter().map(|o| o.get().map_or("-".to_string(), |v| v.len().to_string())).collect::<Vec<_>>().join("/")).collect();
    eprintln!("setup: plans {} B ({}) in {:.1}s, peak_rss_mb={:.0}", b.len(), have.join(" "), t.elapsed().as_secs_f64(), crate::peak_rss_mb());
}

/// The previous node's slot context (its kind's tables for its program's node ops).
fn prev_in<'a>(pre: &'a Pre, ps: &'a format::Signed, c: Digest) -> node::PrevIn<'a> {
    let pk = node::NK::of_byte(ps.pi[0]).unwrap_or_else(|| service::fatal("prev.bin: not a node proof"));
    let ctx = std::sync::Arc::new(ir::NodeCtx::new(pk, pre.nd.protos.clone(), pre.kts.clone()));
    node::PrevIn { signed: ps, c, ix: [1, 0, 2][pk as usize], ctx, base: &pre.base }
}

/// The signed node of kind `k` over the previous node (if any; `pre0` its slot's fill when computed
/// already) and the aggregates.
#[allow(clippy::too_many_arguments)]
fn node_signed(svc: &service::Service, pre: &Pre, k: node::NK, vk: &Digest, prev_in: Option<node::PrevIn>, pre0: Option<node::Fill>, aggs: &[(format::Signed, Digest)], tm: &mut Vec<(&'static str, f64)>) -> (format::Signed, Digest) {
    let mut t = Instant::now();
    let mut mark = |n: &'static str, t: &mut Instant| {
        tm.push((n, t.elapsed().as_secs_f64()));
        *t = Instant::now();
    };
    let nd = pre.nd;
    let kt = pre.kt(k);
    let (circ, gcirc, base) = (&pre.circ, &pre.gcirc, &pre.base);
    let ains: Vec<node::AggIn> = aggs.iter().map(|(s, _)| node::agg_in(s)).collect();
    let w = node::witness(k, vk, prev_in.as_ref(), &ains, &nd.protos, &nd.texts, gcirc, circ, pre0);
    for (v, st) in w.mstats.iter().enumerate() {
        if st.failed_rows != 0 || st.conflicts != 0 || !st.first_conflicts.is_empty() {
            service::fatal(&format!("node witness slot {v}: {st:?}"));
        }
    }
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("node {} witness {}", k.name(), w.times.iter().map(|(n, s)| format!("{n}={s:.3}")).collect::<Vec<_>>().join(" "));
    }
    mark("witness", &mut t);
    let cs: [Digest; 2] = match &prev_in {
        Some(p) => [p.c, aggs[0].1],
        None => [aggs[0].1, aggs[1].1],
    };
    let mut rec = Recorder::new(svc);
    rec.batch_max = 128;
    let ni = nodeprove::NodeIn { k, vk: *vk, cs, w: &w, mats: nodeprove::Mats { k, kt, protos: &nd.protos }, kts: [&*pre.kts[0], &*pre.kts[1], &*pre.kts[2]], base };
    let (pi, ptm) = nodeprove::prove(&rec, &ni);
    if std::env::var_os("FLOCK_VERBOSE").is_some() {
        eprintln!("node {} phases {}", k.name(), ptm.report());
    }
    mark("prove", &mut t);
    let c = nodeprove::node_c(&cs);
    let table = rec.into_table();
    let mut rp = Replay::new(&table);
    rp.fallback = Some(svc);
    let _ = ir::run(&nd.node_program(k), base, &rp, vk, &c, &pi);
    let (tr, missing) = rp.finish();
    if missing != 0 || tr.len() != params::N_ITEMS {
        service::fatal(&format!("node trace: {} queries, {missing} not asked while proving", tr.len()));
    }
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (_, sig) = svc.sign(&qs);
    mark("trace_sign", &mut t);
    (format::Signed { pi, tr, sig }, c)
}

/// `prover first /work` and `prover step /work`: everything that does not depend on the inputs
/// before `ready` (untimed, PROVER.md §3), the inputs after `go`, `done` after `proof.bin`.
pub fn run(first: bool, work: &Path) {
    let ts = Instant::now();
    let mut su: Vec<(&'static str, f64)> = Vec::new();
    let lap = |n: &'static str, su: &mut Vec<(&'static str, f64)>| su.push((n, ts.elapsed().as_secs_f64()));
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| service::fatal("RF_ORACLE is not set"));
    let svc = service::Service::connect(&path).unwrap_or_else(|e| service::fatal(&e));
    svc.warm(crate::par::threads().min(service::MAX_CONNS));
    crate::par::warm();
    let vk = svc.vk();
    lap("svc", &mut su);
    let pre = Pre::new();
    lap("pre", &mut su);
    let _ = crate::skipdom::skip();
    crate::heap_setup(prefault_mib());
    lap("prefault", &mut su);
    let startup = ts.elapsed().as_secs_f64();
    crate::say("ready");
    crate::wait_go();
    let t0 = Instant::now();
    let circ = &pre.circ;
    let mut tm: Vec<(&'static str, f64)> = Vec::new();
    let t = Instant::now();
    let (file, c, k) = if first {
        let a = read_chain(&work.join("chainA.json"));
        let b = read_chain(&work.join("chainB.json"));
        let aggs = vec![agg_signed(&svc, circ, &vk, &a.1, a.0), agg_signed(&svc, circ, &vk, &b.1, b.0)];
        tm.push(("aggregates", t.elapsed().as_secs_f64()));
        let (s, c) = node_signed(&svc, &pre, node::NK::N8, &vk, None, None, &aggs, &mut tm);
        (format::to_file(&s), c, node::NK::N8)
    } else {
        let prev_c: Digest = unhex(&std::fs::read_to_string(work.join("prev.stmt")).expect("prev.stmt")).try_into().expect("prev.stmt");
        let prev = format::from_file(&std::fs::read(work.join("prev.bin")).expect("prev.bin")).unwrap_or_else(|| service::fatal("prev.bin"));
        let (n, s) = read_chain(&work.join("chain.json"));
        let k = if agg::split(n, agg::M_SEG).len() <= 2 { node::NK::N2 } else { node::NK::N4 };
        // slot 0's fill (the previous node's program run and solve) needs only `prev`: it runs on
        // its own thread beside the aggregate (`FLOCK_NO_PRE0`: inside the witness, as before)
        let pin = prev_in(&pre, &prev, prev_c);
        let (aggs, pre0, t0s) = std::thread::scope(|sc| {
            let h = (std::env::var_os("FLOCK_NO_PRE0").is_none()).then(|| {
                sc.spawn(|| {
                    let t = Instant::now();
                    let f = node::slot0_fill(&pin, &vk, &pre.nd.protos, &pre.nd.texts, circ);
                    (f, t.elapsed().as_secs_f64())
                })
            });
            let aggs = vec![agg_signed(&svc, circ, &vk, &s, n)];
            let tw = Instant::now();
            match h.map(|h| h.join().unwrap_or_else(|_| service::fatal("slot 0's fill panicked"))) {
                Some((f, s0)) => (aggs, Some(f), Some((s0, tw.elapsed().as_secs_f64()))),
                None => (aggs, None, None),
            }
        });
        tm.push(("aggregate", t.elapsed().as_secs_f64()));
        if let Some((s0, w0)) = t0s {
            tm.push(("slot0", s0));
            tm.push(("slot0_wait", w0));
        }
        let (sg, c) = node_signed(&svc, &pre, k, &vk, Some(pin), pre0, &aggs, &mut tm);
        (format::to_file(&sg), c, k)
    };
    std::fs::write(work.join("proof.bin"), &file).expect("proof.bin");
    let total = t0.elapsed().as_secs_f64();
    eprintln!(
        "STREAM {} kind={} total_s={total:.3} {} stmt={} file={} peak_rss_mb={:.0} startup_s={startup:.3} su={}{}",
        if first { "first" } else { "step" },
        k.name(),
        tm.iter().map(|(n, s)| format!("{n}={s:.3}")).collect::<Vec<_>>().join(" "),
        hex(&c),
        file.len(),
        crate::peak_rss_mb(),
        su.iter().map(|(n, s)| format!("{n}@{s:.3}")).collect::<Vec<_>>().join(","),
        if crate::prof::on() { format!(" | prof {}", crate::prof::report()) } else { String::new() }
    );
    crate::say("done");
    let _ = leaf_stmt;
}

/// The heap pre-faulted before `ready` (MiB): the largest step's peak (N4 over a `2^20` chain,
/// 6.5 GB in pass 9) less what is mapped by then; `FLOCK_PREFAULT_MIB` overrides.
fn prefault_mib() -> usize {
    std::env::var("FLOCK_PREFAULT_MIB").ok().and_then(|x| x.parse().ok()).unwrap_or(6000)
}
