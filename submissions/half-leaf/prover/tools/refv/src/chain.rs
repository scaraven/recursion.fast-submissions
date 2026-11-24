//! FORMAT6 §3–§4, the verifier's side of the hash chain, reading `BODY` and asking an [`Ask`].
//!
//! `fs6::transcript::Transcript` is the prover's side (it searches nonces and records the trace); this is the
//! reader of the same bytes: a ground group *reads* its nonce from `BODY` and checks the PoW lane, it never searches.
//! The codec (`χ`, the PoW lane, the PoW test) is `fs6::codec`'s.

use crate::{Digest, E, Part, Reject, Res, e_of, require};
use fs6::codec;
use std::collections::BTreeMap;

/// The oracle as `V_S` sees it.
pub trait Ask {
    fn ask(&mut self, q: &[u8], part: Part) -> Res<Digest>;
    /// Queries asked so far.
    fn asked(&self) -> usize;
}

/// `OProg.runSeq`: the `i`-th query is answered by the `i`-th trace entry, whose query must be the one asked.
/// With `key`, also the dev check that every answer is `Keccak-256(k ‖ q)` (the service's `SIGN` guarantees it in
/// the contract; a toy signature does not).
pub struct TraceAsk<'t> {
    tr: &'t [(Vec<u8>, Digest)],
    next: usize,
    key: Option<fs6::oracle::Local>,
}

impl<'t> TraceAsk<'t> {
    pub fn new(tr: &'t [(Vec<u8>, Digest)], key: Option<&[u8; 32]>) -> Self {
        Self { tr, next: 0, key: key.map(fs6::oracle::Local::keyed) }
    }

    /// `runSeq` uses every entry.
    pub fn finish(&self) -> Res<()> {
        require(self.next == self.tr.len(), Reject::TraceLeft(self.tr.len() - self.next))
    }
}

impl Ask for TraceAsk<'_> {
    fn ask(&mut self, q: &[u8], part: Part) -> Res<Digest> {
        let i = self.next;
        let (tq, ta) = self.tr.get(i).ok_or(Reject::TraceShort(part))?;
        require(tq.as_slice() == q, Reject::TraceMismatch(i, part))?;
        if let Some(k) = &self.key {
            require(fs6::Oracle::ask(k, q) == *ta, Reject::NotOracle(i))?;
        }
        self.next += 1;
        Ok(*ta)
    }

    fn asked(&self) -> usize {
        self.next
    }
}

/// The real oracle, recording `V_S`'s queries: re-derives the trace of any `π` (used to re-sign tampered proofs).
pub struct RecordAsk<'o> {
    pub o: &'o dyn fs6::Oracle,
    pub tr: fs6::Trace,
}

impl Ask for RecordAsk<'_> {
    fn ask(&mut self, q: &[u8], _part: Part) -> Res<Digest> {
        let a = self.o.ask(q);
        self.tr.push((q.to_vec(), a));
        Ok(a)
    }

    fn asked(&self) -> usize {
        self.tr.len()
    }
}

/// Per-part counters: `BODY` bytes, queries, nonces, chain draws, and every chain query's length (§3's length rule).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    pub body: usize,
    pub queries: usize,
    pub nonces: usize,
    pub draws: usize,
    /// Bind draws `B` (v2.2), not in `draws`.
    pub binds: usize,
    /// `(g, |buf|)` at every ground query, the nonce included (v2.2's bind rule: `g ≥ 15 ⟹ |buf| ≤ 56`).
    pub ground_bufs: Vec<(u32, usize)>,
    pub chain_lengths: Vec<usize>,
}

/// Where each part ended: chain state, `BODY` offset, trace index (the per-phase KAT checkpoints).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checkpoint {
    pub part: Part,
    pub st: Digest,
    pub body_end: usize,
    pub queries_end: usize,
}

pub struct VChain<'a> {
    ask: &'a mut dyn Ask,
    body: &'a [u8],
    off: usize,
    st: Digest,
    buf: Vec<u8>,
    in_group: bool,
    part: Part,
    pub stats: BTreeMap<Part, Stats>,
    pub checkpoints: Vec<Checkpoint>,
}

impl<'a> VChain<'a> {
    /// `a₀ = O(q₀)`, `st = O(a₀ ‖ HDR)` (v2.5: `c` is not in the seed; `V_S` checks `c = stmtOf(HDR)` first), `buf = []`.
    pub fn start(ask: &'a mut dyn Ask, hdr: &[u8], body: &'a [u8]) -> Res<Self> {
        let mut ch = Self {
            ask,
            body,
            off: 0,
            st: [0; 32],
            buf: Vec::new(),
            in_group: false,
            part: Part::Seed,
            stats: BTreeMap::new(),
            checkpoints: Vec::new(),
        };
        let a0 = ch.ask_counted(&fs6::transcript::Q0)?;
        let seed = [&a0[..], hdr].concat();
        ch.st = ch.ask_counted(&seed)?;
        Ok(ch)
    }

    pub fn part(&self) -> Part {
        self.part
    }

    pub fn state(&self) -> Digest {
        self.st
    }

    /// Close the current part (checkpoint) and open `p`.
    pub fn phase(&mut self, p: Part) {
        self.checkpoint();
        self.part = p;
    }

    fn checkpoint(&mut self) {
        self.checkpoints.push(Checkpoint {
            part: self.part,
            st: self.st,
            body_end: self.off,
            queries_end: self.ask.asked(),
        });
    }

    fn cur(&mut self) -> &mut Stats {
        self.stats.entry(self.part).or_default()
    }

    fn ask_counted(&mut self, q: &[u8]) -> Res<Digest> {
        let part = self.part;
        let a = self.ask.ask(q, part)?;
        self.cur().queries += 1;
        Ok(a)
    }

    /// `n` bytes of `BODY`.
    fn take(&mut self, n: usize) -> Res<&'a [u8]> {
        require(self.body.len() - self.off >= n, Reject::BodyShort(self.part))?;
        let b = &self.body[self.off..self.off + n];
        self.off += n;
        self.cur().body += n;
        Ok(b)
    }

    /// A prover message: read and absorbed.
    fn absorb(&mut self, n: usize) -> Res<&'a [u8]> {
        let b = self.take(n)?;
        self.buf.extend_from_slice(b);
        Ok(b)
    }

    /// `E(k)`.
    pub fn read_e(&mut self, k: usize) -> Res<Vec<E>> {
        let b = self.absorb(16 * k)?;
        Ok(b.chunks_exact(16).map(|x| e_of(codec::get_e(x))).collect())
    }

    /// `K(k)`.
    pub fn read_k(&mut self, k: usize) -> Res<Vec<u64>> {
        let b = self.absorb(8 * k)?;
        Ok(b.chunks_exact(8).map(codec::le64).collect())
    }

    /// `CAP(i)` of `2^lv` digests: read and absorbed.
    pub fn read_cap(&mut self, lv: u32) -> Res<Vec<Digest>> {
        let b = self.absorb(32 << lv)?;
        Ok(b.chunks_exact(32).map(|x| x.try_into().unwrap()).collect())
    }

    /// Opening bytes: read, not absorbed.
    pub fn read_plain(&mut self, n: usize) -> Res<&'a [u8]> {
        self.take(n)
    }

    /// An opening's leaf or node query (§5): counted, not a chain step.
    pub fn ask_plain(&mut self, q: &[u8]) -> Res<Digest> {
        self.ask_counted(q)
    }

    fn chain_step(&mut self, q: &[u8]) -> Res<Digest> {
        let a = self.ask_counted(q)?;
        let s = self.cur();
        s.chain_lengths.push(q.len());
        self.st = a;
        self.buf.clear();
        Ok(a)
    }

    /// `B` (v2.2): one draw of `st ‖ buf` whose value and PoW lane are ignored; only the state moves. It does not
    /// open a group (no challenge follows it without a `G`).
    pub fn bind(&mut self) -> Res<()> {
        let q = [&self.st[..], &self.buf].concat();
        self.chain_step(&q)?;
        self.cur().binds += 1;
        self.in_group = false;
        Ok(())
    }

    /// `G(g)`: read the 8-byte nonce, absorb it last, draw; the PoW lane must be `< 2^(64−g)`. Returns `χ`.
    pub fn ground(&mut self, g: u32) -> Res<E> {
        self.absorb(8)?;
        let n = self.buf.len();
        let s = self.cur();
        s.nonces += 1;
        s.ground_bufs.push((g, n));
        let q = [&self.st[..], &self.buf].concat();
        let a = self.chain_step(&q)?;
        self.cur().draws += 1;
        require(codec::pow_ok(&a, g), Reject::Pow(self.part))?;
        self.in_group = true;
        Ok(e_of(codec::chi(&a)))
    }

    /// One further draw `D(1)`: the query is `st` (32 bytes). Only inside a group, with nothing absorbed since the
    /// last draw: the schedule guarantees both, so a violation is a `refv` bug.
    pub fn draw(&mut self) -> Res<E> {
        assert!(self.in_group && self.buf.is_empty(), "a further draw follows a draw, with an empty buffer");
        let q = self.st;
        let a = self.chain_step(&q)?;
        self.cur().draws += 1;
        Ok(e_of(codec::chi(&a)))
    }

    pub fn draws(&mut self, k: usize) -> Res<Vec<E>> {
        (0..k).map(|_| self.draw()).collect()
    }

    /// `G(g)`, `D(k − 1)`: `k` values, the ground draw first (a point, the positions' draws, a group's maps).
    pub fn group(&mut self, g: u32, k: usize) -> Res<Vec<E>> {
        let mut v = vec![self.ground(g)?];
        v.extend(self.draws(k - 1)?);
        Ok(v)
    }

    /// After the last item: `BODY` used up exactly (§2). Nothing absorbed is left unbound: the last item of the
    /// schedule is a draw.
    pub fn finish(mut self) -> Res<(BTreeMap<Part, Stats>, Vec<Checkpoint>)> {
        self.checkpoint();
        require(self.off == self.body.len(), Reject::BodyLeft(self.body.len() - self.off))?;
        assert!(self.buf.is_empty(), "the schedule ends on a draw");
        Ok((self.stats, self.checkpoints))
    }
}
