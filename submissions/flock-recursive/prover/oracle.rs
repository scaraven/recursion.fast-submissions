//! The random oracle (from `submissions/spartan-srom/prover/oracle.rs`): every Merkle and Fiat–Shamir hash of the prover and of the
//! native verifier is an `ask` of an `Oracle`.
//!
//! * `Local`: in-process. `Keyed(k)` is the v4 service's `PRF_k` (keyed BLAKE2s-256, RFC 7693,
//!   `service/PROTOCOL.md` §2.1) under a key given on the command line, for known-answer tests and
//!   local benchmarks.
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

use crate::blake2s::{Digest, Keyed};
use crate::par;

/// Writes query `i` by appending its bytes to the buffer.
pub type Builder<'a> = dyn Fn(usize, &mut Vec<u8>) + Sync + 'a;
/// Writes query `i` of batch `b` (`build(b, i, buf)`).
pub type Builder2<'a> = dyn Fn(usize, usize, &mut Vec<u8>) + Sync + 'a;

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
    /// Several independent batches at once (the grinder's sub-batches, `transcript::Fs::grind`):
    /// `outs[b][i]` is the answer to query `i` of batch `b`. Not recorded for the replay (the grinder
    /// asks the winning attempt again through `ask`). The default runs `ask_many` per batch in
    /// parallel.
    fn ask_batches(&self, outs: &mut [Vec<Digest>], build: &Builder2) {
        par::for_each_chunk_mut(outs, 1, |off, ch| {
            for (j, o) in ch.iter_mut().enumerate() {
                self.ask_many(o, &|i, buf: &mut Vec<u8>| build(off + j, i, buf));
            }
        });
    }
    /// G4: a verifier item whose answer the prover already holds, in the verifier's order (an
    /// opened column or Merkle node, a grinded phase's winning absorb and squeezes). Nothing is
    /// sent; a taping `Recorder` appends it to the trace (and, when keeping, to the replay table).
    fn note(&self, _q: &[u8], _a: &Digest) {}
    /// Whether `note` records anything (the prover builds the noted queries only then).
    fn taping(&self) -> bool {
        false
    }
    /// The grinder's search in one call (`transcript::Fs::grind`), for an oracle that has one
    /// (`service::Service`: pipelined batches); `None`: the grinder uses `ask_batches`.
    fn grind(&self, _job: &GrindJob) -> Option<GrindWin> {
        None
    }
}

/// A grinded phase (D128 §2.1, `transcript::Fs::grind`): the attempt for nonce `n` is the absorb
/// query `pre ‖ enc64 n ‖ 0^8` followed by `nsq` squeezes `"FRSQZ000" ‖ a`; it wins if the last
/// answer's byte `POW_BYTE` is zero. The search must return the **smallest** winning nonce.
pub struct GrindJob<'a> {
    pub pre: &'a [u8],
    pub nsq: usize,
    /// nonces per request
    pub batch: usize,
    /// requests in flight (one connection each)
    pub depth: usize,
}

/// The smallest winning nonce, its attempt's answers (absorb, then the `nsq` squeezes) and the
/// cost counters of the search.
pub struct GrindWin {
    pub nonce: u64,
    pub abs: Digest,
    pub sq: Vec<Digest>,
    pub attempts: u64,
    pub queries: u64,
    pub compressions: u64,
    pub rounds: u64,
}

/// An in-process oracle.
pub enum Local {
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
    /// batch queries longer than this are not kept (the replay asks them again)
    pub batch_max: usize,
    table: Mutex<Vec<(u128, Digest)>>,
    /// G4: every `ask` and `note`, in order (the verifier's trace), when taping
    tape: Option<Mutex<Trace>>,
    pub stats: Stats,
}

impl<'a> Recorder<'a> {
    pub fn new(inner: &'a dyn Oracle) -> Recorder<'a> {
        Recorder { inner, keep: true, batch_max: usize::MAX, table: Mutex::new(Vec::new()), tape: None, stats: Stats::default() }
    }
    /// Counts only; `into_table` is then empty.
    pub fn counting(inner: &'a dyn Oracle) -> Recorder<'a> {
        Recorder { keep: false, ..Recorder::new(inner) }
    }
    /// G4: also tape every `ask` and `note` in order (`take_tape`).
    pub fn taped(mut self) -> Recorder<'a> {
        self.tape = Some(Mutex::new(Vec::with_capacity(4 * crate::params::N_ITEMS + 8)));
        self
    }
    /// The prover's recorder for a signed proof: taping, and keeping the replay table only for the
    /// cross-check (`trace_check`).
    pub fn for_trace(inner: &'a dyn Oracle) -> Recorder<'a> {
        let mut r = if trace_check() { Recorder::new(inner) } else { Recorder::counting(inner) }.taped();
        r.batch_max = 128;
        r
    }
    /// The tape so far (emptied).
    pub fn take_tape(&self) -> Trace {
        self.tape.as_ref().map(|t| std::mem::take(&mut *t.lock().unwrap())).unwrap_or_default()
    }
    pub fn into_table(self) -> Table {
        let mut v = self.table.into_inner().unwrap();
        v.sort_unstable_by(|x, y| x.0.cmp(&y.0));
        Table(v)
    }
}

impl Oracle for Recorder<'_> {
    fn note(&self, q: &[u8], a: &Digest) {
        if let Some(t) = &self.tape {
            t.lock().unwrap().push((q.to_vec(), *a));
        }
        if self.keep {
            self.table.lock().unwrap().push((fp(q), *a));
        }
    }
    fn taping(&self) -> bool {
        self.tape.is_some() || self.keep
    }
    /// Forwarded and counted; nothing kept (the winning attempt reaches the trace by `note`).
    fn grind(&self, job: &GrindJob) -> Option<GrindWin> {
        let t = Instant::now();
        let w = self.inner.grind(job)?;
        self.stats.many_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        self.stats.manys.fetch_add(w.rounds, Ordering::Relaxed);
        self.stats.queries.fetch_add(w.queries, Ordering::Relaxed);
        Some(w)
    }
    /// Forwarded, counted, never kept in the table (the grinder's failed attempts are not asked by
    /// the verifier; its winning attempt reaches the trace and the table by `note`).
    fn ask_batches(&self, outs: &mut [Vec<Digest>], build: &Builder2) {
        let t = Instant::now();
        let bytes = AtomicU64::new(0);
        self.inner.ask_batches(outs, &|b, i, buf: &mut Vec<u8>| {
            let st = buf.len();
            build(b, i, buf);
            bytes.fetch_add((buf.len() - st) as u64, Ordering::Relaxed);
        });
        let n: usize = outs.iter().map(|o| o.len()).sum();
        self.stats.many_ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        self.stats.manys.fetch_add(1, Ordering::Relaxed);
        self.stats.queries.fetch_add(n as u64, Ordering::Relaxed);
        self.stats.bytes.fetch_add(bytes.into_inner(), Ordering::Relaxed);
    }
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
        if let Some(t) = &self.tape {
            t.lock().unwrap().push((q.to_vec(), a));
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
            let f = if buf.len() - st <= self.batch_max { fp(&buf[st..]) } else { 0 };
            fps[2 * i].store((f >> 64) as u64, Ordering::Relaxed);
            fps[2 * i + 1].store(f as u64, Ordering::Relaxed);
            bytes.fetch_add((buf.len() - st) as u64, Ordering::Relaxed);
        });
        {
            let mut tab = self.table.lock().unwrap();
            tab.reserve(n);
            for (i, a) in out.iter().enumerate() {
                let f = ((fps[2 * i].load(Ordering::Relaxed) as u128) << 64) | fps[2 * i + 1].load(Ordering::Relaxed) as u128;
                if f != 0 {
                    tab.push((f, *a));
                }
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

/// `FLOCK_TRACE_CHECK=1`: besides taping the trace while proving (G4), replay the native verifier
/// on the prover's answers and require the same trace (the pre-G4 path, now a test-mode check).
pub fn trace_check() -> bool {
    static C: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *C.get_or_init(|| std::env::var("FLOCK_TRACE_CHECK").is_ok_and(|v| v != "0"))
}

/// The verifier's trace of a proof made through `rec` (`Recorder::for_trace`): its tape (G4). When
/// `rec` kept its table (`trace_check`), the native verifier `verify` is also replayed on the
/// prover's answers (`fallback` for a query the table lacks), and it must accept and ask exactly
/// the tape's queries with the tape's answers.
pub fn finish_trace(rec: Recorder, fallback: &dyn Oracle, verify: &dyn Fn(&dyn Oracle) -> bool) -> Result<Trace, String> {
    let tape = rec.take_tape();
    if !rec.keep {
        return Ok(tape);
    }
    let table = rec.into_table();
    let mut rp = Replay::new(&table);
    rp.fallback = Some(fallback);
    if !verify(&rp) {
        return Err("the native verifier rejects the proof (replay)".into());
    }
    let (tr, missing) = rp.finish();
    if missing != 0 {
        return Err(format!("{missing} verifier queries were not asked while proving"));
    }
    if tr != tape {
        let i = tr.iter().zip(tape.iter()).position(|(a, b)| a != b).unwrap_or(tr.len().min(tape.len()));
        return Err(format!("the tape differs from the replay at item {i} (|tape| {}, |replay| {})", tape.len(), tr.len()));
    }
    eprintln!("trace check: the tape equals the native verifier's replay ({} items)", tr.len());
    Ok(tape)
}

/// Answers from the prover's table and records the queries asked, in order.
pub struct Replay<'a> {
    table: &'a Table,
    /// asked for a query the table does not hold (`None`: the miss is counted)
    pub fallback: Option<&'a dyn Oracle>,
    rec: Mutex<Trace>,
    missing: AtomicU64,
}

impl<'a> Replay<'a> {
    pub fn new(table: &'a Table) -> Replay<'a> {
        Replay { table, fallback: None, rec: Mutex::new(Vec::new()), missing: AtomicU64::new(0) }
    }
    /// The recorded trace and the number of queries the table did not hold.
    pub fn finish(self) -> (Trace, u64) {
        (self.rec.into_inner().unwrap(), self.missing.into_inner())
    }
}

impl Oracle for Replay<'_> {
    fn ask(&self, q: &[u8]) -> Digest {
        let a = self.table.get(q).unwrap_or_else(|| match self.fallback {
            Some(o) => o.ask(q),
            None => {
                self.missing.fetch_add(1, Ordering::Relaxed);
                [0u8; 32]
            }
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

/// An oracle that records every query and answer of another (a verifier's trace).
pub struct Tape<'a>(&'a dyn Oracle, std::sync::Mutex<Trace>);
impl<'a> Tape<'a> {
    pub fn new(o: &'a dyn Oracle) -> Tape<'a> {
        Tape(o, std::sync::Mutex::new(Vec::new()))
    }
    pub fn into_trace(self) -> Trace {
        self.1.into_inner().unwrap()
    }
}
impl Oracle for Tape<'_> {
    fn ask(&self, q: &[u8]) -> Digest {
        let a = self.0.ask(q);
        self.1.lock().unwrap().push((q.to_vec(), a));
        a
    }
}
