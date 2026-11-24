//! FORMAT6 §3–§4: the transcript is a hash chain over the oracle.
//!
//! - start: `a₀ = O(q₀)`, `q₀ = "lvm6/1" ‖ 0` (7 bytes); `st = O(a₀ ‖ c ‖ HDR)` (the seed; v2.2: `vk` is in `HDR`);
//!   `buf = []`;
//! - absorb: a prover message (scalars, words, nonces, caps) is written to `BODY` and appended to `buf`; Merkle
//!   openings are written to `BODY` only;
//! - draw: ask `st ‖ buf`; the answer becomes `st`, `buf = []`; the value is `χ(a)`;
//! - ground group `G(g)`: the least nonce `ν` (8 bytes LE, absorbed last) whose draw has PoW lane `< 2^(64−g)`;
//!   then further draws `D(k)` with an empty buffer (32-byte queries). No draw outside a group;
//! - bind `B` (v2.2): a draw whose value is discarded (only `st` moves), so the next ground query is short.
//!
//! The recorder keeps every query V asks, in V's order, with its answer: `q₀`, the seed, every chain query (a
//! grind's candidates are not V's queries; only the passing one is), and for an opening its leaf and node queries.
//! That list is what `SIGN` gets.
//!
//! Enforced here (panics: a prover bug, never input-dependent): the length rule (no chain query of 64, 256 or 368
//! bytes), every query `≤ 2^20` bytes, `1 ≤ g ≤ 23`, further draws only inside a group and with an empty buffer.

use crate::codec::{self, E};
use crate::merkle::{self, Tree6};
use crate::oracle::{self, Oracle};
use crate::{Digest, Trace};

/// `q₀ = "lvm6/1" ‖ 0`.
pub const Q0: [u8; 7] = *b"lvm6/1\0";

/// `P18`'s lengths no chain query may have (the leaf and node classes: 368, 256, 64). Another shape's list is
/// `Shape::forbidden_lengths` (FORMAT6 §3: `fsLenOK` per `Shape`), installed with [`Transcript::forbid`].
pub const FORBIDDEN_CHAIN_LENGTHS: [usize; 3] = [64, 256, 368];

/// `queryCap`.
pub const QUERY_CAP: usize = 1 << 20;

pub struct Transcript<'o> {
    o: &'o dyn Oracle,
    st: Digest,
    buf: Vec<u8>,
    body: Vec<u8>,
    trace: Trace,
    in_group: bool,
    forbidden: Vec<usize>,
    pub nonces: usize,
    pub draws: usize,
    pub binds: usize,
    /// Candidates the nonce searches asked (grinding work).
    pub candidates: u64,
}

impl<'o> Transcript<'o> {
    /// `q₀`, then the seed `a₀ ‖ HDR` (v2.5; `c` is bound natively, `c = stmtOf(HDR)`, before any query).
    pub fn start(o: &'o dyn Oracle, hdr: &[u8]) -> Self {
        let a0 = oracle::ask(o, &Q0);
        let seed = [&a0[..], hdr].concat();
        let st = oracle::ask(o, &seed);
        Self {
            o,
            st,
            buf: Vec::new(),
            body: Vec::new(),
            trace: vec![(Q0.to_vec(), a0), (seed, st)],
            in_group: false,
            forbidden: FORBIDDEN_CHAIN_LENGTHS.to_vec(),
            nonces: 0,
            draws: 0,
            binds: 0,
            candidates: 0,
        }
    }

    /// The length rule of another shape (default: `P18`'s list).
    pub fn forbid(mut self, lengths: Vec<usize>) -> Self {
        self.forbidden = lengths;
        self
    }

    pub fn oracle(&self) -> &'o dyn Oracle {
        self.o
    }

    /// The chain state `st` (the last chain answer).
    pub fn state(&self) -> Digest {
        self.st
    }

    pub fn body_len(&self) -> usize {
        self.body.len()
    }

    pub fn trace_len(&self) -> usize {
        self.trace.len()
    }

    /// Whether a ground draw has opened a group (further draws are allowed with an empty buffer).
    pub fn in_group(&self) -> bool {
        self.in_group
    }

    /// Bytes absorbed since the last draw.
    pub fn pending(&self) -> usize {
        self.buf.len()
    }

    // ---------------------------------------------------------------- absorb

    /// A prover message: written to `BODY` and absorbed.
    pub fn absorb(&mut self, m: &[u8]) {
        self.body.extend_from_slice(m);
        self.buf.extend_from_slice(m);
    }

    /// `E(k)`: scalars, 16 bytes each.
    pub fn absorb_e(&mut self, es: &[E]) {
        for &e in es {
            let mut b = Vec::with_capacity(16);
            codec::put_e(&mut b, e);
            self.absorb(&b);
        }
    }

    /// `K(k)`: words, 8 bytes each.
    pub fn absorb_k(&mut self, ws: &[u64]) {
        for &w in ws {
            self.absorb(&w.to_le_bytes());
        }
    }

    /// `CAP(i)`: `2^lv` digests, absorbed.
    pub fn absorb_cap(&mut self, cap: &[Digest]) {
        for d in cap {
            self.absorb(d);
        }
    }

    /// Bytes of `BODY` that are not absorbed (Merkle openings).
    pub fn write_unabsorbed(&mut self, b: &[u8]) {
        self.body.extend_from_slice(b);
    }

    // ---------------------------------------------------------------- draws

    fn chain_step(&mut self, q: Vec<u8>, a: Digest) -> E {
        assert!(!self.forbidden.contains(&q.len()), "length rule: a chain query of {} bytes", q.len());
        assert!(q.len() <= QUERY_CAP, "a query above queryCap");
        self.trace.push((q, a));
        self.st = a;
        self.buf.clear();
        self.draws += 1;
        codec::chi(&a)
    }

    /// `G(g)`: the least nonce whose draw passes, absorbed last; the draw's `χ`.
    pub fn ground(&mut self, g: u32) -> E {
        self.ground_with(g, |_| true)
    }

    /// `G(g)` where the prover also needs the challenge to be `usable` (e.g. leanVM's layer point `s ∉ K`): the
    /// least nonce whose draw passes the PoW and is usable. V checks only the PoW (it accepts any passing nonce).
    pub fn ground_with(&mut self, g: u32, usable: impl Fn(E) -> bool) -> E {
        assert!((1..=23).contains(&g), "a group's grind is 1..=23 bits");
        let mut prefix = Vec::with_capacity(32 + self.buf.len() + 8);
        prefix.extend_from_slice(&self.st);
        prefix.extend_from_slice(&self.buf);
        let (nonce, a, asked) = least_nonce(self.o, &prefix, g, &usable);
        self.candidates += asked;
        self.absorb(&nonce.to_le_bytes());
        prefix.extend_from_slice(&nonce.to_le_bytes());
        self.nonces += 1;
        self.in_group = true;
        self.chain_step(prefix, a)
    }

    /// `B`: ask `st ‖ buf`, keep only the new state (value and PoW lane ignored). Opens no group: a `G` follows.
    pub fn bind(&mut self) {
        let mut q = Vec::with_capacity(32 + self.buf.len());
        q.extend_from_slice(&self.st);
        q.extend_from_slice(&self.buf);
        let a = oracle::ask(self.o, &q);
        self.chain_step(q, a);
        self.draws -= 1;
        self.binds += 1;
        self.in_group = false;
    }

    /// One further draw of the current group (empty buffer: the query is `st`, 32 bytes).
    pub fn draw(&mut self) -> E {
        assert!(self.in_group, "no draw outside a group: a further draw follows a ground draw");
        assert!(self.buf.is_empty(), "a further draw has an empty buffer (messages are bound by the next G)");
        let q = self.st.to_vec();
        let a = oracle::ask(self.o, &q);
        self.chain_step(q, a)
    }

    /// `D(k)`.
    pub fn draws(&mut self, k: usize) -> Vec<E> {
        (0..k).map(|_| self.draw()).collect()
    }

    // ---------------------------------------------------------------- openings

    /// `OPEN(i)` of `tree` at `positions` (in drawn order, repeats included): each opening's leaf bytes and
    /// siblings go to `BODY` (not absorbed), and V's `1 + ht − lv` queries with their answers to the trace.
    pub fn open(&mut self, tree: &Tree6, positions: &[usize], leaf: &dyn Fn(usize, &mut Vec<u8>)) {
        let mut b = Vec::new();
        for &p in positions {
            b.clear();
            leaf(p, &mut b);
            tree.opening_trace(p, &b, &mut self.trace);
            self.body.extend_from_slice(&b);
            for s in tree.siblings(p) {
                self.body.extend_from_slice(&s);
            }
        }
    }

    /// An opening given as leaf bytes and siblings (leanVM's `MerklePath`): written to `BODY`, V's queries asked and
    /// recorded.
    pub fn open_asked(&mut self, p: usize, leaf: &[u8], siblings: &[Digest]) {
        merkle::opening_trace_asked(self.o, p, leaf, siblings, &mut self.trace);
        self.body.extend_from_slice(leaf);
        for s in siblings {
            self.body.extend_from_slice(s);
        }
    }

    /// `BODY` and the trace (V's queries in order, `q₀` and the seed first).
    pub fn finish(self) -> (Vec<u8>, Trace) {
        (self.body, self.trace)
    }
}

/// Candidates a window of the search asks: 64 up to `g = 8` (one round trip on the calling thread), then a
/// quarter of the expected `2^g`, at most 2^16 (spread over the connections). A function of `g` alone, and the
/// result is the least passing nonce for any window size anyway.
pub fn window(g: u32) -> u64 {
    if g <= 8 { 64 } else { (1u64 << (g - 2)).clamp(256, 1 << 16) }
}

/// The least `ν ≥ 0` with `pow_ok(O(prefix ‖ LE64 ν), g)` and `usable(χ)`: the nonce, its answer, candidates asked.
pub fn least_nonce(o: &dyn Oracle, prefix: &[u8], g: u32, usable: &dyn Fn(E) -> bool) -> (u64, Digest, u64) {
    let w = window(g);
    let mut answers = vec![[0u8; 32]; w as usize];
    let mut first = 0u64;
    loop {
        oracle::batch_nonces(o, prefix, first, &mut answers);
        if let Some(i) = answers.iter().position(|a| codec::pow_ok(a, g) && usable(codec::chi(a))) {
            return (first + i as u64, answers[i], first + w);
        }
        first += w;
    }
}
