//! The random oracle (blueprint §7): every Merkle and Fiat–Shamir hash of the prover and of the
//! native verifier is an `ask` of an `Oracle`.
//!
//! * `Local`: in-process. `Keyed(k)` is the v4 service's `PRF_k` (keyed BLAKE2s-256, RFC 7693,
//!   `service/PROTOCOL.md` §2.1) under a key given on the command line, for known-answer tests and
//!   local benchmarks; `V3` is v3's `blake2s256(0x52 ‖ q)`, for the v3 known-answer comparisons.
//! * `service::Service` (`service.rs`): the v4 oracle service over its Unix socket.
//! * `Recorder`: wraps the prover's oracle, counts its queries and (for the replay check) keeps a
//!   `(fingerprint of q → answer)` table of every query asked while proving.
//! * `Replay`: answers the native verifier from that table and records the query sequence it asks;
//!   a query missing from the table is counted, never sent to the service. The prover writes the
//!   trace to `SIGN` itself (`prover::prove_leaf_core`); `SPARTAN_REPLAY=1` and the tests check it
//!   against this replay.
//! * `Seq`: answers the `i`-th query from the `i`-th trace entry and fails on any other query, the
//!   native `OProg.runSeq` of `acc` (FORMAT.md).
//!
//! Merkle levels are asked in batches (`ask_many`, parallel); the transcript is sequential.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use crate::blake2s::{Blake2s, Digest, Keyed, TAG_RO};
use crate::par;

/// Writes query `i` by appending its bytes to the buffer.
pub type Builder<'a> = dyn Fn(usize, &mut Vec<u8>) + Sync + 'a;

pub trait Oracle: Sync {
    /// The answer to one query.
    fn ask(&self, q: &[u8]) -> Digest;
    /// `out[i] = H(q_i)` for the queries `build` writes; the default asks them one by one.
    fn ask_many(&self, out: &mut [Digest], build: &Builder) {
        let mut buf = Vec::new();
        for (i, o) in out.iter_mut().enumerate() {
            buf.clear();
            build(i, &mut buf);
            *o = self.ask(&buf);
        }
    }
}

/// An in-process oracle.
pub enum Local {
    /// v3's `H(q) = blake2s256(0x52 ‖ q)`.
    V3,
    /// Keyed BLAKE2s-256 under a 32-byte key (the service's `PRF_k`).
    Keyed(Keyed),
}

impl Local {
    pub fn keyed(key: &[u8; 32]) -> Local {
        Local::Keyed(Keyed::new(key))
    }
}

impl Oracle for Local {
    fn ask(&self, q: &[u8]) -> Digest {
        match self {
            Local::V3 => Blake2s::new().update(&[TAG_RO]).update(q).finalize(),
            Local::Keyed(k) => k.hash(q),
        }
    }
    fn ask_many(&self, out: &mut [Digest], build: &Builder) {
        par::for_each_chunk_mut(out, 64, |off, chunk| {
            let mut buf = Vec::new();
            for (i, o) in chunk.iter_mut().enumerate() {
                buf.clear();
                build(off + i, &mut buf);
                *o = self.ask(&buf);
            }
        });
    }
}

/// A 128-bit fingerprint of a byte string (not cryptographic): two 64-bit multiply–xorshift lanes
/// over little-endian words, seeded with the length. A collision could only make the replay use a
/// wrong answer, and every replayed answer is compared with the service's `SIGN` answers, so it
/// would abort the proof, never emit a wrong one.
pub fn fp(q: &[u8]) -> u128 {
    const P1: u64 = 0x9E37_79B9_7F4A_7C15;
    const P2: u64 = 0xC2B2_AE3D_27D4_EB4F;
    let len = q.len() as u64;
    let mut a = len ^ 0x243F_6A88_85A3_08D3;
    let mut b = len.wrapping_mul(P2) ^ 0x1319_8A2E_0370_7344;
    let mut step = |w: u64| {
        a = (a ^ w).wrapping_mul(P1);
        a ^= a >> 29;
        b = (b ^ w.rotate_left(23)).wrapping_mul(P2);
        b ^= b >> 31;
    };
    let mut chunks = q.chunks_exact(8);
    for c in &mut chunks {
        step(u64::from_le_bytes(c.try_into().unwrap()));
    }
    let r = chunks.remainder();
    if !r.is_empty() {
        let mut t = [0u8; 8];
        t[..r.len()].copy_from_slice(r);
        step(u64::from_le_bytes(t));
    }
    let mut x = (a ^ b.rotate_left(17)).wrapping_mul(P2);
    x ^= x >> 32;
    let mut y = (b ^ a.rotate_left(41)).wrapping_mul(P1);
    y ^= y >> 29;
    ((x as u128) << 64) | y as u128
}

/// Counters of an oracle as the prover sees it.
#[derive(Default)]
pub struct Stats {
    pub queries: AtomicU64,
    pub bytes: AtomicU64,
    /// wall-clock nanoseconds inside `ask` (sequential Fiat–Shamir steps)
    pub ask_ns: AtomicU64,
    pub asks: AtomicU64,
    /// wall-clock nanoseconds inside `ask_many` (Merkle levels; includes building the queries)
    pub many_ns: AtomicU64,
    pub manys: AtomicU64,
}

impl Stats {
    pub fn report(&self) -> String {
        let g = |x: &AtomicU64| x.load(Ordering::Relaxed);
        format!(
            "oracle_queries={} oracle_bytes={} fs_asks={} fs_s={:.4} batches={} batch_s={:.4}",
            g(&self.queries),
            g(&self.bytes),
            g(&self.asks),
            g(&self.ask_ns) as f64 * 1e-9,
            g(&self.manys),
            g(&self.many_ns) as f64 * 1e-9
        )
    }
    pub fn oracle_s(&self) -> f64 {
        (self.ask_ns.load(Ordering::Relaxed) + self.many_ns.load(Ordering::Relaxed)) as f64 * 1e-9
    }
}

/// The prover's answers, by query fingerprint, sorted for lookup.
pub struct Table(Vec<(u128, Digest)>);

impl Table {
    pub fn get(&self, q: &[u8]) -> Option<Digest> {
        let f = fp(q);
        self.0.binary_search_by(|e| e.0.cmp(&f)).ok().map(|i| self.0[i].1)
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

/// Counts the queries asked through it (`stats`) and, when `keep`, records each (by fingerprint)
/// with its answer.
pub struct Recorder<'a> {
    inner: &'a dyn Oracle,
    keep: bool,
    table: Mutex<Vec<(u128, Digest)>>,
    pub stats: Stats,
}

impl<'a> Recorder<'a> {
    pub fn new(inner: &'a dyn Oracle) -> Recorder<'a> {
        Recorder { inner, keep: true, table: Mutex::new(Vec::new()), stats: Stats::default() }
    }
    /// Counts only; `into_table` is then empty.
    pub fn counting(inner: &'a dyn Oracle) -> Recorder<'a> {
        Recorder { keep: false, ..Recorder::new(inner) }
    }
    pub fn into_table(self) -> Table {
        let mut v = self.table.into_inner().unwrap();
        v.sort_unstable_by(|x, y| x.0.cmp(&y.0));
        Table(v)
    }
}

impl Oracle for Recorder<'_> {
    fn ask(&self, q: &[u8]) -> Digest {
        let t = Instant::now();
        let a = self.inner.ask(q);
        self.stats.ask_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        self.stats.asks.fetch_add(1, Ordering::Relaxed);
        self.stats.queries.fetch_add(1, Ordering::Relaxed);
        self.stats.bytes.fetch_add(q.len() as u64, Ordering::Relaxed);
        if self.keep {
            self.table.lock().unwrap().push((fp(q), a));
        }
        a
    }
    fn ask_many(&self, out: &mut [Digest], build: &Builder) {
        let t = Instant::now();
        let n = out.len();
        if !self.keep {
            let bytes = AtomicU64::new(0);
            self.inner.ask_many(out, &|i, buf: &mut Vec<u8>| {
                let st = buf.len();
                build(i, buf);
                bytes.fetch_add((buf.len() - st) as u64, Ordering::Relaxed);
            });
            self.stats.many_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
            self.stats.manys.fetch_add(1, Ordering::Relaxed);
            self.stats.queries.fetch_add(n as u64, Ordering::Relaxed);
            self.stats.bytes.fetch_add(bytes.into_inner(), Ordering::Relaxed);
            return;
        }
        let fps: Vec<AtomicU64> = (0..2 * n).map(|_| AtomicU64::new(0)).collect();
        let bytes = AtomicU64::new(0);
        self.inner.ask_many(out, &|i, buf: &mut Vec<u8>| {
            let st = buf.len();
            build(i, buf);
            let f = fp(&buf[st..]);
            fps[2 * i].store((f >> 64) as u64, Ordering::Relaxed);
            fps[2 * i + 1].store(f as u64, Ordering::Relaxed);
            bytes.fetch_add((buf.len() - st) as u64, Ordering::Relaxed);
        });
        {
            let mut tab = self.table.lock().unwrap();
            tab.reserve(n);
            for (i, a) in out.iter().enumerate() {
                let f = ((fps[2 * i].load(Ordering::Relaxed) as u128) << 64) | fps[2 * i + 1].load(Ordering::Relaxed) as u128;
                tab.push((f, *a));
            }
        }
        self.stats.many_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        self.stats.manys.fetch_add(1, Ordering::Relaxed);
        self.stats.queries.fetch_add(n as u64, Ordering::Relaxed);
        self.stats.bytes.fetch_add(bytes.load(Ordering::Relaxed), Ordering::Relaxed);
    }
}

/// A trace: queries with their answers, in the order the verifier asks them.
pub type Trace = Vec<(Vec<u8>, Digest)>;

/// Answers from the prover's table and records the queries asked, in order.
pub struct Replay<'a> {
    table: &'a Table,
    rec: Mutex<Trace>,
    missing: AtomicU64,
}

impl<'a> Replay<'a> {
    pub fn new(table: &'a Table) -> Replay<'a> {
        Replay { table, rec: Mutex::new(Vec::new()), missing: AtomicU64::new(0) }
    }
    /// The recorded trace and the number of queries the table did not hold.
    pub fn finish(self) -> (Trace, u64) {
        (self.rec.into_inner().unwrap(), self.missing.into_inner())
    }
}

impl Oracle for Replay<'_> {
    fn ask(&self, q: &[u8]) -> Digest {
        let a = self.table.get(q).unwrap_or_else(|| {
            self.missing.fetch_add(1, Ordering::Relaxed);
            [0u8; 32]
        });
        self.rec.lock().unwrap().push((q.to_vec(), a));
        a
    }
}

/// `OProg.runSeq`: the `i`-th query must equal the `i`-th trace entry's query and is answered by
/// its answer; any other query, or a query past the end, fails the run (answered with zeros).
pub struct Seq<'a> {
    tr: &'a [(Vec<u8>, Digest)],
    pos: AtomicU64,
    bad: AtomicBool,
}

impl<'a> Seq<'a> {
    pub fn new(tr: &'a [(Vec<u8>, Digest)]) -> Seq<'a> {
        Seq { tr, pos: AtomicU64::new(0), bad: AtomicBool::new(false) }
    }
    /// Every query matched its entry and every entry was used.
    pub fn consumed(&self) -> bool {
        !self.bad.load(Ordering::Relaxed) && self.pos.load(Ordering::Relaxed) as usize == self.tr.len()
    }
}

impl Oracle for Seq<'_> {
    fn ask(&self, q: &[u8]) -> Digest {
        if self.bad.load(Ordering::Relaxed) {
            return [0u8; 32];
        }
        let i = self.pos.fetch_add(1, Ordering::Relaxed) as usize;
        match self.tr.get(i) {
            Some((qq, a)) if qq.as_slice() == q => *a,
            _ => {
                self.bad.store(true, Ordering::Relaxed);
                [0u8; 32]
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fingerprints_differ() {
        let mut seen = std::collections::HashSet::new();
        let mut q = vec![];
        for len in 0..200usize {
            for v in 0..20u8 {
                q.clear();
                q.resize(len, 0);
                if len > 0 {
                    q[(v as usize * 7) % len] = v;
                }
                if v == 0 || len > 0 {
                    seen.insert((q.clone(), fp(&q)));
                }
            }
        }
        let fps: std::collections::HashSet<u128> = seen.iter().map(|x| x.1).collect();
        let qs: std::collections::HashSet<Vec<u8>> = seen.iter().map(|x| x.0.clone()).collect();
        assert_eq!(fps.len(), qs.len());
    }

    #[test]
    fn recorder_replay_seq() {
        let base = Local::keyed(&[7u8; 32]);
        let rec = Recorder::new(&base);
        let a = rec.ask(b"abc");
        let mut out = vec![[0u8; 32]; 100];
        rec.ask_many(&mut out, &|i, b: &mut Vec<u8>| b.extend_from_slice(format!("q{i}").as_bytes()));
        assert_eq!(out[5], base.ask(b"q5"));
        let tab = rec.into_table();
        assert_eq!(tab.len(), 101);
        let rp = Replay::new(&tab);
        assert_eq!(rp.ask(b"q7"), base.ask(b"q7"));
        assert_eq!(rp.ask(b"abc"), a);
        rp.ask(b"never");
        let (tr, miss) = rp.finish();
        assert_eq!((tr.len(), miss), (3, 1));
        let sq = Seq::new(&tr[..2]);
        assert_eq!(sq.ask(b"q7"), base.ask(b"q7"));
        assert!(!sq.consumed());
        sq.ask(b"abc");
        assert!(sq.consumed());
        sq.ask(b"more");
        assert!(!sq.consumed());
    }
}
