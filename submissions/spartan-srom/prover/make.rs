//! Signed proofs (blueprint §1, §7): a leaf `L` (prove, with the verifier's trace written by the
//! prover; one `SIGN`), a bundle `B` of two children (no `QUERY`: the traces are concatenated, one
//! `SIGN`), and the plain node `N` used when a child cannot be bundled (a leaf of length 0 or above
//! `2^12`, D-6). The
//! stream's `node` request builds its file in place and writes it while the service signs
//! (`node_files`).

use std::io::Write;
use std::time::Instant;

use crate::acc::CLEAR_CAP;
use crate::blake2s::{leaf_stmt, Digest};
use crate::circuit::Circuit;
use crate::format::{decode, encode, put_sig, Sig, Signed, Wit};
use crate::oracle::{Oracle, Recorder, Replay, Trace};
use crate::prover::{leaf_header, prove_leaf_core, Timings};
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
/// answers), under the oracle `o`. The prover writes the trace itself (`prover::prove_leaf_core`);
/// with `SPARTAN_REPLAY=1` the native verifier is also replayed against the prover's answers (no
/// query beyond those the prover asked), and its trace must be the same.
pub fn prove_traced(circ: &Circuit, o: &dyn Oracle, s: &Digest, n: u64, cost: &mut LeafCost) -> Result<(Vec<u8>, Trace), String> {
    let check = std::env::var("SPARTAN_REPLAY").map(|v| v != "0").unwrap_or(false);
    prove_traced_opt(circ, o, s, n, cost, check)
}

/// `prove_traced`, with the replay check when `check`.
pub fn prove_traced_opt(circ: &Circuit, o: &dyn Oracle, s: &Digest, n: u64, cost: &mut LeafCost, check: bool) -> Result<(Vec<u8>, Trace), String> {
    if n == 0 {
        return Ok((leaf_header(s, 0, s), vec![]));
    }
    let t = Instant::now();
    let rec = if check { Recorder::new(o) } else { Recorder::counting(o) };
    let mut tr = Trace::new();
    let (pi, tm, _): (Vec<u8>, Timings, _) = prove_leaf_core(circ, &rec, s, n, false, None, Some(&mut tr));
    cost.prove_s = t.elapsed().as_secs_f64();
    cost.phases = tm.report();
    cost.oracle = rec.stats.report();
    cost.oracle_s = rec.stats.oracle_s();
    if !check {
        return Ok((pi, tr));
    }
    let t = Instant::now();
    let table = rec.into_table();
    cost.table = table.len();
    let rp = Replay::new(&table);
    let h: Digest = pi[48..80].try_into().unwrap();
    let r = check_leaf(circ, &rp, &leaf_stmt(&h, n), &pi);
    let (rtr, missing) = rp.finish();
    cost.replay_s = t.elapsed().as_secs_f64();
    if missing != 0 {
        return Err(format!("replay: the verifier asked {missing} queries the prover never asked"));
    }
    r.map_err(|e| format!("replay: the native verifier rejects the proof: {e}"))?;
    if rtr != tr {
        return Err("replay: the verifier's trace differs from the prover's".into());
    }
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

/// A child for bundling, from its statement and signed proof (`L` with `1 ≤ n ≤ 2^12`, or `B`);
/// `None` if it cannot be bundled.
pub fn child(stmt: &Digest, p: &Signed) -> Option<Child> {
    match kind(&p.pi) {
        "L" => {
            // a bundled leaf has `1 ≤ n ≤ 2^12` (§2, D-6); any other leaf goes into a plain node
            let n = u64::from_le_bytes(p.pi[40..48].try_into().unwrap());
            if n == 0 || n > CLEAR_CAP {
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

/// A signed-proof file read in place (`format::from_file`'s strict layout): `π`, the trace's
/// entries as bytes (`enc64 |q| ‖ q ‖ a` each) with the place of each query, the signature.
pub struct FileView<'a> {
    pub pi: &'a [u8],
    pub entries: &'a [u8],
    /// `(offset of q in entries, |q|)`, in order
    pub items: Vec<(usize, usize)>,
    pub sig: Sig,
}

/// `FileView` of `b`, or `None` unless `b` is exactly one encoding (as `from_file`).
pub fn view(b: &[u8]) -> Option<FileView<'_>> {
    let u64_at = |o: usize| -> Option<u64> { Some(u64::from_le_bytes(b.get(o..o + 8)?.try_into().unwrap())) };
    let pl = u64_at(0)?;
    if pl > (b.len() - 8) as u64 {
        return None;
    }
    let pi = &b[8..8 + pl as usize];
    let mut o = 8 + pl as usize;
    let m = u64_at(o)?;
    if m > b.len() as u64 {
        return None;
    }
    o += 8;
    let e0 = o;
    let mut items = Vec::with_capacity(m as usize);
    for _ in 0..m {
        let ql = u64_at(o)?;
        if ql > (b.len() - o - 8) as u64 || (b.len() - o - 8 - ql as usize) < 32 {
            return None;
        }
        items.push((o + 8 - e0, ql as usize));
        o += 8 + ql as usize + 32;
    }
    let entries = &b[e0..o];
    let p = from_file_sig(b.get(o..)?)?;
    Some(FileView { pi, entries, items, sig: p })
}

/// The signature part of a file (`idx ‖ 133 + 16 digests`), exactly.
fn from_file_sig(b: &[u8]) -> Option<Sig> {
    if b.len() != 8 + 32 * 149 {
        return None;
    }
    let d = |k: usize| -> Digest { b[8 + 32 * k..40 + 32 * k].try_into().unwrap() };
    Some(Sig { idx: u64::from_le_bytes(b[..8].try_into().unwrap()), ots: (0..133).map(d).collect(), path: (133..149).map(d).collect() })
}

/// Where a child's `π` splits into its clear form and its part of `T` (`child`), with the `σ0` of
/// a bundle; `None` if it cannot be bundled.
fn split(pi: &[u8]) -> Option<(usize, Option<Sig>)> {
    match word0(pi) {
        Some(0) if pi.len() > 48 => {
            let n = u64::from_le_bytes(pi[40..48].try_into().unwrap());
            (1..=CLEAR_CAP).contains(&n).then_some((48, None))
        }
        Some(0) => None,
        _ => match decode(pi) {
            Some((Wit::Node { p1, .. }, used)) if used < pi.len() => Some((used, Some(p1.sig))),
            _ => None,
        },
    }
}

/// `node` of two children given as files, when both can be bundled under one `σ0`: the output
/// file, built from the children's bytes in place (`π = encode W ‖ T₁ ‖ T₂`, the trace entries
/// copied) and written to `out`, the `SIGN` sent first and the file up to the signature built and
/// written while the service hashes. The same bytes as `to_file (node …)` with the same `SIGN`
/// calls in the same order; `None` (nothing written) when `node` would make the plain node.
pub fn node_files(
    svc: &Service,
    c1: &Digest,
    v1: &FileView,
    c2: &Digest,
    v2: &FileView,
    sigma0: &mut dyn FnMut() -> Result<Sig, String>,
    out: &std::path::Path,
    cost: &mut NodeCost,
) -> Result<Option<Vec<u8>>, String> {
    let t = Instant::now();
    let ((l1, s1), (l2, s2)) = match (split(v1.pi), split(v2.pi)) {
        (Some(a), Some(b)) if a.1.is_none() || b.1.is_none() || a.1 == b.1 => (a, b),
        _ => return Ok(None),
    };
    let s0 = match s1.or(s2) {
        Some(s) => s,
        None => sigma0()?,
    };
    let count = v1.items.len() + v2.items.len();
    let qbytes: usize = v1.items.iter().chain(&v2.items).map(|x| x.1).sum();
    let mut req = Vec::with_capacity(16 + 4 * count + qbytes);
    req.resize(16, 0);
    for v in [v1, v2] {
        for &(o, l) in &v.items {
            req.extend_from_slice(&(l as u32).to_le_bytes());
            req.extend_from_slice(&v.entries[o..o + l]);
        }
    }
    let conn = svc.sign_start(&mut req, count);
    // while the service hashes: the file up to the signature
    let slot = |clear: &[u8]| Box::new(Signed { pi: clear.to_vec(), tr: vec![], sig: s0.clone() });
    let w = Wit::Node { c1: *c1, c2: *c2, p1: slot(&v1.pi[..l1]), p2: slot(&v2.pi[..l2]) };
    let enc = encode(&w);
    let (t1, t2) = (&v1.pi[l1..], &v2.pi[l2..]);
    let pl = enc.len() + t1.len() + t2.len();
    let mut f = Vec::with_capacity(24 + pl + v1.entries.len() + v2.entries.len() + 32 * 149);
    f.extend_from_slice(&(pl as u64).to_le_bytes());
    f.extend_from_slice(&enc);
    f.extend_from_slice(t1);
    f.extend_from_slice(t2);
    f.extend_from_slice(&(count as u64).to_le_bytes());
    f.extend_from_slice(v1.entries);
    f.extend_from_slice(v2.entries);
    let io = |e: std::io::Error| format!("{}: {e}", out.display());
    let mut file = std::fs::File::create(out).map_err(io)?;
    file.write_all(&f).map_err(io)?;
    cost.build_s = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let (ans, sig) = svc.sign_finish(conn, count, req.len() - 16);
    let mut k = 0;
    for v in [v1, v2] {
        for &(o, l) in &v.items {
            if ans[32 * k..32 * k + 32] != v.entries[o + l..o + l + 32] {
                return Err(format!("SIGN: answer {k} differs from the trace's"));
            }
            k += 1;
        }
    }
    let mut tail = Vec::with_capacity(8 + 32 * 149);
    put_sig(&mut tail, &sig);
    file.write_all(&tail).map_err(io)?;
    f.extend_from_slice(&tail);
    cost.sign_s = t.elapsed().as_secs_f64();
    Ok(Some(f))
}
