//! Signed proofs (blueprint §1, §7): a leaf `L` (prove, replay the verifier for its trace, one
//! `SIGN`), a bundle `B` of two children (no `QUERY`: the traces are concatenated, one `SIGN`), and
//! the plain node `N` used when a child cannot be bundled (a leaf of length 0).

use std::time::Instant;

use crate::blake2s::{leaf_stmt, Digest};
use crate::circuit::Circuit;
use crate::format::{decode, encode, Sig, Signed, Wit};
use crate::oracle::{Oracle, Recorder, Replay, Trace};
use crate::prover::{leaf_header, prove_leaf, Timings};
use crate::service::Service;
use crate::verifier::{check_leaf, word0};

/// What a leaf proof costs, for the logs (`SPARTAN_VERBOSE=1`) and the measurements.
#[derive(Default, Debug)]
pub struct LeafCost {
    pub prove_s: f64,
    pub replay_s: f64,
    pub sign_s: f64,
    pub phases: String,
    pub oracle: String,
    pub oracle_s: f64,
    pub table: usize,
}

/// The `L` proof bytes of `(s, n)` and its trace (the verifier's queries with the prover's
/// answers), under the oracle `o`. No query beyond those the prover asked: the verifier is replayed
/// against the prover's answers.
pub fn prove_traced(circ: &Circuit, o: &dyn Oracle, s: &Digest, n: u64, cost: &mut LeafCost) -> Result<(Vec<u8>, Trace), String> {
    if n == 0 {
        return Ok((leaf_header(s, 0, s), vec![]));
    }
    let t = Instant::now();
    let rec = Recorder::new(o);
    let (pi, tm, _): (Vec<u8>, Timings, _) = prove_leaf(circ, &rec, s, n, false);
    cost.prove_s = t.elapsed().as_secs_f64();
    cost.phases = tm.report();
    cost.oracle = rec.stats.report();
    cost.oracle_s = rec.stats.oracle_s();
    let t = Instant::now();
    let table = rec.into_table();
    cost.table = table.len();
    let rp = Replay::new(&table);
    let h: Digest = pi[48..80].try_into().unwrap();
    let r = check_leaf(circ, &rp, &leaf_stmt(&h, n), &pi);
    let (tr, missing) = rp.finish();
    cost.replay_s = t.elapsed().as_secs_f64();
    if missing != 0 {
        return Err(format!("replay: the verifier asked {missing} queries the prover never asked"));
    }
    r.map_err(|e| format!("replay: the native verifier rejects the proof: {e}"))?;
    Ok((pi, tr))
}

/// `SIGN` the trace's queries; the service's answers must equal the trace's.
pub fn sign(svc: &Service, tr: &Trace) -> Result<Sig, String> {
    let qs: Vec<&[u8]> = tr.iter().map(|(q, _)| q.as_slice()).collect();
    let (ans, sig) = svc.sign(&qs);
    if let Some(i) = (0..tr.len()).find(|&i| ans[i] != tr[i].1) {
        return Err(format!("SIGN: answer {i} differs from the answer used while proving"));
    }
    Ok(sig)
}

/// A signed leaf proof `L` of `(s, n)` through the service.
pub fn leaf(circ: &Circuit, svc: &Service, s: &Digest, n: u64, cost: &mut LeafCost) -> Result<Signed, String> {
    let (pi, tr) = prove_traced(circ, svc, s, n, cost)?;
    let t = Instant::now();
    let sig = sign(svc, &tr)?;
    cost.sign_s = t.elapsed().as_secs_f64();
    Ok(Signed { pi, tr, sig })
}

/// A child of a node as the bundle needs it: its statement, its clear form (`C` of a leaf,
/// `encode W` of a bundle), its part `T` of the bundle tail, its trace, and the `σ0` of a bundle.
pub struct Child {
    pub stmt: Digest,
    pub clear: Vec<u8>,
    pub t: Vec<u8>,
    pub tr: Trace,
    pub sigma0: Option<Sig>,
}

/// The kind of a signed proof's `π` (blueprint §2), for logs and size tables.
pub fn kind(pi: &[u8]) -> &'static str {
    match word0(pi) {
        Some(0) if pi.len() > 48 => "L",
        Some(0) if pi.len() == 48 => "C",
        _ => match decode(pi) {
            Some((Wit::Node { .. }, used)) if used == pi.len() => "N",
            Some((Wit::Node { .. }, used)) if used < pi.len() => "B",
            _ => "?",
        },
    }
}

/// A child for bundling, from its statement and signed proof (`L` with `n ≥ 1`, or `B`); `None`
/// if it cannot be bundled.
pub fn child(stmt: &Digest, p: &Signed) -> Option<Child> {
    match kind(&p.pi) {
        "L" => {
            let n = u64::from_le_bytes(p.pi[40..48].try_into().unwrap());
            if n == 0 {
                return None;
            }
            Some(Child { stmt: *stmt, clear: p.pi[..48].to_vec(), t: p.pi[48..].to_vec(), tr: p.tr.clone(), sigma0: None })
        }
        "B" => {
            let (w, used) = decode(&p.pi)?;
            let Wit::Node { p1, .. } = w else { return None };
            Some(Child {
                stmt: *stmt,
                clear: p.pi[..used].to_vec(),
                t: p.pi[used..].to_vec(),
                tr: p.tr.clone(),
                sigma0: Some(p1.sig.clone()),
            })
        }
        _ => None,
    }
}

/// The bundle of two children under `σ0` (§1.4): `π = encode W ‖ T₁ ‖ T₂` with
/// `W = .node c₁ c₂ (clear₁, [], σ0) (clear₂, [], σ0)`, and the trace `tr₁ ‖ tr₂`.
pub fn bundle(c1: Child, c2: Child, sigma0: &Sig) -> (Vec<u8>, Trace) {
    let slot = |clear: Vec<u8>| Box::new(Signed { pi: clear, tr: vec![], sig: sigma0.clone() });
    let w = Wit::Node { c1: c1.stmt, c2: c2.stmt, p1: slot(c1.clear), p2: slot(c2.clear) };
    let mut pi = encode(&w);
    pi.extend_from_slice(&c1.t);
    pi.extend_from_slice(&c2.t);
    let mut tr = c1.tr;
    tr.extend(c2.tr);
    (pi, tr)
}

/// What a node costs: building `π` and its trace (decode, `σ0`, encode, copies), the `SIGN`.
#[derive(Default, Debug)]
pub struct NodeCost {
    pub build_s: f64,
    pub sign_s: f64,
}

/// The signed node of two signed children (blueprint §7 `node`): their bundle when both can be
/// bundled under one `σ0` (a bundle child's, else `sigma0()`), otherwise the plain node `N`; one
/// `SIGN` of its trace.
pub fn node(
    svc: &Service,
    c1: &Digest,
    p1: &Signed,
    c2: &Digest,
    p2: &Signed,
    sigma0: &mut dyn FnMut() -> Result<Sig, String>,
    cost: &mut NodeCost,
) -> Result<Signed, String> {
    let t = Instant::now();
    let (pi, tr) = match (child(c1, p1), child(c2, p2)) {
        (Some(k1), Some(k2)) if k1.sigma0.is_none() || k2.sigma0.is_none() || k1.sigma0 == k2.sigma0 => {
            let s0 = match k1.sigma0.clone().or(k2.sigma0.clone()) {
                Some(s) => s,
                None => sigma0()?,
            };
            bundle(k1, k2, &s0)
        }
        _ => (plain(c1, c2, p1, p2), vec![]),
    };
    cost.build_s = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let sig = sign(svc, &tr)?;
    cost.sign_s = t.elapsed().as_secs_f64();
    Ok(Signed { pi, tr, sig })
}

/// The plain node `N` (§1.3): `encode (.node c₁ c₂ p₁ p₂)`, no query, empty trace.
pub fn plain(c1: &Digest, c2: &Digest, p1: &Signed, p2: &Signed) -> Vec<u8> {
    encode(&Wit::Node { c1: *c1, c2: *c2, p1: Box::new(p1.clone()), p2: Box::new(p2.clone()) })
}
