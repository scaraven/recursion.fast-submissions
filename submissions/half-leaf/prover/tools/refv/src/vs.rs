//! `V_S` (FORMAT6 §2–§6) and `acc` on the signed file (§8, `harness/FORMAT.md`).

use crate::chain::{Ask, Checkpoint, Stats, TraceAsk, VChain};
use crate::format::{from_file, sig_ok, trace_digest};
use crate::hdr::{self, Hdr};
use crate::shape::Shape;
use crate::stack::{self, Commit, Maps, StackClaim};
use crate::whir::{self, Trail};
use crate::{Digest, Part, Reject, Res, require};
use std::collections::BTreeMap;

/// The parts between §6.1 and §6.5's group that `refv` does not walk itself: §6.2 (the tree batch, frozen in
/// FORMAT6 v2.1, written by R2 as `tree.rs` on these types) and §6.3–§6.4 (sponge caller, core and link; typed
/// phases and mini-bus: §T). Each reads its items from the chain and returns its stack claims in §6.5's order
/// (`tree`: 1, 2, 3–10, 11–14; `rest`: 15, 16, then §T's), as functions of §6.5's maps. The defaults are the STUB:
/// no item, no claim. A proof made for the stub schedule (the KATs) is not a valid lvm6 proof.
pub trait Stubs {
    /// §6.2, after `y₀` (its first ground query absorbs `y₀`, `δ` and the nonce).
    fn tree<'a>(&mut self, _ch: &mut VChain<'a>, _sh: &Shape, _c: &Commit) -> Res<Vec<Deferred>> {
        Ok(Vec::new())
    }
    /// §6.3 and §6.4.
    fn rest<'a>(&mut self, _ch: &mut VChain<'a>, _sh: &Shape, _c: &Commit) -> Res<Vec<Deferred>> {
        Ok(Vec::new())
    }
}

/// A claim whose weight needs the ring-switch maps (claims 1 and 15) or none.
pub type Deferred = Box<dyn FnOnce(&Maps) -> StackClaim<'static>>;

/// The stub schedule.
pub struct NoStubs;
impl Stubs for NoStubs {}

#[derive(Clone, Debug)]
pub struct Report {
    pub hdr: Hdr,
    pub stats: BTreeMap<Part, Stats>,
    pub checkpoints: Vec<Checkpoint>,
    pub queries: usize,
    pub claims: usize,
    pub trail: Trail,
    pub y0: crate::E,
    pub lambda0: crate::E,
}

impl Report {
    pub fn total(&self) -> Stats {
        let mut t = Stats::default();
        for s in self.stats.values() {
            t.body += s.body;
            t.queries += s.queries;
            t.nonces += s.nonces;
            t.draws += s.draws;
            t.binds += s.binds;
            t.ground_bufs.extend(&s.ground_bufs);
            t.chain_lengths.extend(&s.chain_lengths);
        }
        t
    }
}

/// `V_S sh vk c π`, its queries answered by `ask`.
pub fn verify_pi(sh: &Shape, vk: &Digest, c: &Digest, pi: &[u8], ask: &mut dyn Ask, stubs: &mut dyn Stubs) -> Res<Report> {
    let (h, hdr_bytes, body) = hdr::parse(sh, pi)?;
    hdr::vk_ok(vk, &h)?;
    hdr::statement_ok(c, &h)?;
    let mut ch = VChain::start(ask, hdr_bytes, body)?;
    let commit = stack::commit(&mut ch, sh)?;
    ch.phase(Part::Tree);
    let mut deferred = stubs.tree(&mut ch, sh, &commit)?;
    ch.phase(Part::Stub);
    deferred.extend(stubs.rest(&mut ch, sh, &commit)?);
    let maps = stack::maps(&mut ch, sh)?;
    // Claim 0 is the OOD claim (FORMAT6 §6.5; leanVM puts it last, `L:lib.rs:183`).
    let mut claims: Vec<StackClaim> = vec![commit.claim()];
    claims.extend(deferred.into_iter().map(|d| d(&maps)));
    let n_claims = claims.len();
    let (target, basis) = stack::batch(sh, maps.lambda0, claims)?;
    let trail = whir::verify(&mut ch, sh, target, commit.cap0.clone(), &*basis)?;
    let (mut stats, checkpoints) = ch.finish()?;
    let queries = stats.values().map(|s| s.queries).sum();
    stats.entry(Part::Tree).or_default();
    stats.entry(Part::Stub).or_default();
    Ok(Report { hdr: h, stats, checkpoints, queries, claims: n_claims, trail, y0: commit.y0, lambda0: maps.lambda0 })
}

/// `acc vk c p` on the bytes of a signed-proof file. With `key`, also the dev check that every trace answer is the
/// keyed oracle's.
pub fn verify_file(sh: &Shape, vk: &Digest, c: &Digest, file: &[u8], key: Option<&[u8; 32]>) -> Res<Report> {
    let s = from_file(file).ok_or(Reject::File)?;
    for (i, (q, _)) in s.tr.iter().enumerate() {
        require(q.len() <= crate::format::QUERY_CAP, Reject::QueryCap(i))?;
    }
    require(s.tr.len() <= sh.qv, Reject::TraceLen(s.tr.len()))?;
    require(sig_ok(vk, &trace_digest(&s.tr), &s.sig), Reject::Sig)?;
    let mut ask = TraceAsk::new(&s.tr, key);
    let rep = verify_pi(sh, vk, c, &s.pi, &mut ask, &mut NoStubs)?;
    ask.finish()?;
    Ok(rep)
}
