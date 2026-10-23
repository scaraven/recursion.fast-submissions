//! The native `acc` (`harness/FORMAT.md`, contract `Submission.acc`) with the entry's verifier `V`
//! (blueprint §2), for self-tests (`verify-native`) and the prover's own checks. The compiled Lean
//! `acc` is the only binding check; this one makes the same decisions on the proofs this prover
//! writes and on their canaries.
//!
//! `acc vk c p`: `|π| ≤ proofCap`, at most `qV = 2^16` trace entries (core `ea2e8ab`), every
//! `|q| ≤ queryCap`, `SigOk vk (traceDigest tr) σ`, and `V vk c π` run against the trace
//! (`oracle::Seq`) asks exactly the trace's queries and returns true. `V` decides the branch from
//! `π` before any query: `L` (tag 0, `|π| > 48`), `C` (tag 0, `|π| = 48`, `n ≤ 2^12`), `N` (`π` is
//! exactly `encode` of a node), `B` (`encode W` a strict prefix, every bundled `1 ≤ n ≤ 2^12`).

use crate::blake2s::{chain_end, leaf_stmt, node_stmt, Digest};
use crate::chain::{leaf_size, Shape, T_COLS};
use crate::circuit::Circuit;
use crate::format::{decode, encode, sig_ok, trace_digest, Sig, Signed, Wit, PROOF_CAP, QUERY_CAP};
use crate::oracle::{Oracle, Seq};
use crate::verifier::{check_leaf, verify_snark, word0};

/// `qV = 2^16`: the entry's query bound, the cap on a trace's length in `acc` (core `ea2e8ab`) and
/// the bundle's static cap `Σ_j qBound (kap n_j) ≤ 2^16`.
pub const Q_V: u64 = 1 << 16;

/// **The longest chain a clear or bundled leaf may claim** (blueprint D-6, the Lean `clearCap`):
/// `2^12` steps. No SNARK leaf above it fits `proofCap` (`leafSize 4096 = 796,111 ≤ 2^20 <
/// leafSize 8192`), so no accepted proof is lost.
pub const CLEAR_CAP: u64 = 1 << 12;

/// v3's exact per-leaf query bound `qBound κ` (`SpartanChainVerifier.lean`):
/// `1 + (2 + rows) + (5 ℓ_y + 9 + 2 ℓ_q) + (1 + ⌈t/cnt⌉ + t (1 + ℓ_N))`.
pub fn q_bound(n: u64) -> u64 {
    let sh = Shape::new(n);
    let t = T_COLS as u64;
    let cnt = sh.cnt as u64;
    1 + (2 + sh.m as u64) + (5 * sh.ell as u64 + 9 + 2 * sh.lq() as u64) + (1 + t.div_ceil(cnt) + t * (1 + sh.ln as u64))
}

/// A clear leaf of a bundle: its start, length and slot statement.
#[derive(Clone, Debug)]
pub struct ClearLeaf {
    pub s: Digest,
    pub n: u64,
    pub c: Digest,
}

/// The clear-tree check of one slot (`W`'s child `(c, p)`): empty trace, signature `σ0`, proof
/// within `proofCap`, proof `C` or `N` (with `nodeStmt` statements and clear slots below); the clear
/// leaves are appended depth first, child 1 before child 2.
pub fn clear_slot(c: &Digest, p: &Signed, sigma0: &Sig, out: &mut Vec<ClearLeaf>) -> Result<(), String> {
    if !p.tr.is_empty() {
        return Err("bundle: a clear slot has a non-empty trace".into());
    }
    if p.sig != *sigma0 {
        return Err("bundle: a clear slot's signature differs from σ0".into());
    }
    if p.pi.len() > PROOF_CAP {
        return Err("bundle: a clear slot's proof is above proofCap".into());
    }
    if word0(&p.pi) == Some(0) && p.pi.len() == 48 {
        let s: Digest = p.pi[8..40].try_into().unwrap();
        let n = u64::from_le_bytes(p.pi[40..48].try_into().unwrap());
        out.push(ClearLeaf { s, n, c: *c });
        return Ok(());
    }
    match decode(&p.pi) {
        Some((w @ Wit::Node { .. }, used)) if used == p.pi.len() && encode(&w) == p.pi => {
            let Wit::Node { c1, c2, p1, p2 } = w else { unreachable!() };
            if *c != node_stmt(&c1, &c2) {
                return Err("bundle: an inner slot's statement is not nodeStmt of its children".into());
            }
            clear_slot(&c1, &p1, sigma0, out)?;
            clear_slot(&c2, &p2, sigma0, out)
        }
        _ => Err("bundle: a clear slot is neither C nor N".into()),
    }
}

/// `V vk c π` over the oracle `o`; `Err(reason)` is `false`.
pub fn v(circ: &Circuit, vk: &Digest, o: &dyn Oracle, c: &Digest, pi: &[u8]) -> Result<(), String> {
    match word0(pi) {
        Some(0) if pi.len() > 48 => return check_leaf(circ, o, c, pi).map(|_| ()).map_err(|e| format!("L: {e}")),
        Some(0) if pi.len() == 48 => {
            let s: Digest = pi[8..40].try_into().unwrap();
            let n = u64::from_le_bytes(pi[40..48].try_into().unwrap());
            if n > CLEAR_CAP {
                return Err("C: n > 2^12 (D-6)".into());
            }
            return if *c == leaf_stmt(&chain_end(&s, n), n) { Ok(()) } else { Err("C: statement".into()) };
        }
        _ => {}
    }
    let (w, used) = decode(pi).ok_or("not a leaf and no node decodes")?;
    let Wit::Node { c1, c2, p1, p2 } = &w else { return Err("decodes to a leaf of the wrong size".into()) };
    if used > pi.len() || encode(&w).as_slice() != &pi[..used] {
        return Err("not a canonical node encoding".into());
    }
    if used == pi.len() {
        // N
        if *c != node_stmt(c1, c2) {
            return Err("N: statement".into());
        }
        acc(circ, vk, c1, p1).map_err(|e| format!("N child 1: {e}"))?;
        return acc(circ, vk, c2, p2).map_err(|e| format!("N child 2: {e}"));
    }
    // B
    if *c != node_stmt(c1, c2) {
        return Err("B: statement".into());
    }
    let sigma0 = &p1.sig;
    let mut leaves = vec![];
    clear_slot(c1, p1, sigma0, &mut leaves)?;
    clear_slot(c2, p2, sigma0, &mut leaves)?;
    if !sig_ok(vk, &trace_digest(&[]), sigma0) {
        return Err("B: σ0 is not a signature of the empty trace".into());
    }
    if leaves.iter().any(|l| l.n == 0 || l.n > CLEAR_CAP) {
        return Err("B: a bundled leaf has n = 0 or n > 2^12 (D-6)".into());
    }
    let t = &pi[used..];
    let want: usize = leaves.iter().map(|l| 32 + leaf_size(l.n) - 80).sum();
    if t.len() != want {
        return Err(format!("B: |T| = {}, expected {want}", t.len()));
    }
    let qb: u64 = leaves.iter().map(|l| q_bound(l.n)).sum();
    if qb > Q_V {
        return Err(format!("B: Σ qBound = {qb} > 2^16"));
    }
    let mut off = 0;
    for (j, l) in leaves.iter().enumerate() {
        let h: Digest = t[off..off + 32].try_into().unwrap();
        let len = leaf_size(l.n) - 80;
        if l.c != leaf_stmt(&h, l.n) {
            return Err(format!("B: leaf {j}: statement is not leafStmt h n"));
        }
        verify_snark(circ, o, &l.s, l.n, &h, &t[off + 32..off + 32 + len]).map_err(|e| format!("B: leaf {j}: {e}"))?;
        off += 32 + len;
    }
    Ok(())
}

/// `acc vk c p`.
pub fn acc(circ: &Circuit, vk: &Digest, c: &Digest, p: &Signed) -> Result<(), String> {
    if p.pi.len() > PROOF_CAP {
        return Err(format!("|π| = {} > proofCap", p.pi.len()));
    }
    if p.tr.len() as u64 > Q_V {
        return Err(format!("{} trace entries > qV = 2^16", p.tr.len()));
    }
    if p.tr.iter().any(|(q, _)| q.len() > QUERY_CAP) {
        return Err("a query above queryCap".into());
    }
    if !sig_ok(vk, &trace_digest(&p.tr), &p.sig) {
        return Err("SigOk fails".into());
    }
    let seq = Seq::new(&p.tr);
    v(circ, vk, &seq, c, &p.pi)?;
    if !seq.consumed() {
        return Err("runSeq: the verifier's queries are not exactly the trace".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn q_bound_matches_v3() {
        // F0 §2: the verifier's queries at n = 16, 1024, 4096, 16384, 65536
        assert_eq!(q_bound(16), 3533);
        assert_eq!(q_bound(1024), 4414);
        assert_eq!(q_bound(4096), 4753);
        assert_eq!(q_bound(16384), 5156);
        assert_eq!(q_bound(65536), 5687);
        // §6.3: 7 774 at κ = 20
        assert_eq!(q_bound(1 << 20), 7774);
    }
}
