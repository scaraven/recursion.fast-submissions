//! Fiat–Shamir through the oracle (blueprint rev. 3.7 §1.2, A.2, A.4): `seed`, `absorb`, `squeeze`
//! queries, the challenge maps, and `π` as A.3's eighteen fields. The prover writes each message
//! into its field (`Writer`); the verifier reads each field with its own cursor (`Reader`), so the
//! reading order is the item order of A.4 while `π` is grouped by field.
//!
//! `Fs` can log every query it asks as an A.4 item (`ItemRec`: phase, query kind, payload length,
//! Merkle level and depth, query length), the form of `logs/S-F4/dump/items.json` (the KAT).

use crate::blake2s::Digest;
use crate::field::{F, K};
use crate::merkle::node_query;
use crate::oracle::{GrindJob, GrindWin, Oracle};
use crate::params::{field_off, FIELD_SIZES, NONCE_LEN, N_FIELDS, PI_SIZE, POW_BYTE, TAG_ABS, TAG_SEED, TAG_SQZ};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;
use std::time::Instant;

/// One item of the query sequence, as `FRTranscriptDefs.items` names it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemRec {
    pub phase: &'static str,
    pub q: &'static str,
    pub len: Option<usize>,
    pub level: Option<usize>,
    pub depth: Option<usize>,
    pub qlen: usize,
}

impl ItemRec {
    /// The item as one object of `items.json` (the dump tool's key order).
    pub fn json(&self) -> String {
        let mut s = format!("{{\"phase\":\"{}\",\"q\":\"{}\"", self.phase, self.q);
        if let Some(l) = self.len {
            s += &format!(",\"len\":{l}");
        }
        if let Some(l) = self.level {
            s += &format!(",\"level\":{l}");
        }
        if let Some(d) = self.depth {
            s += &format!(",\"depth\":{d}");
        }
        s += &format!(",\"qlen\":{}}}", self.qlen);
        s
    }
}

/// The proof-of-work rule's role in a transcript (`flock-128`, D128 §2.1): the prover asserts its own
/// grinding (a missed phase is a bug), the verifier records a failed byte as a rejection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pow {
    Off,
    Assert,
    Check,
}

/// `pow_at()[i]`: Fiat–Shamir item `i` (seed, absorbs and squeezes in order) is the last squeeze of a
/// grinded phase (`items::pow_positions`, KAT'd against Lean's `powPos`).
fn pow_at() -> &'static [bool] {
    static T: OnceLock<Vec<bool>> = OnceLock::new();
    T.get_or_init(|| {
        let mut v = vec![false; crate::params::N_FS_ITEMS];
        for p in crate::items::pow_positions() {
            v[p] = true;
        }
        v
    })
}

/// The grinding's cost, over the process (`logs/I7/grind.log`): phases ground, nonces tried, oracle
/// queries asked by the grinder (absorbs and squeezes of every attempt, the winning one included),
/// keyed-BLAKE2s compressions of those queries (the key block counted, as the service computes
/// them), the sequential steps (one `ask_batches` call per absorb or squeeze step of a batch: a
/// round trip each) and the wall time.
pub struct GrindStats {
    pub phases: AtomicU64,
    pub attempts: AtomicU64,
    pub queries: AtomicU64,
    pub compressions: AtomicU64,
    pub rounds: AtomicU64,
    pub ns: AtomicU64,
}
pub static GRIND: GrindStats = GrindStats {
    phases: AtomicU64::new(0),
    attempts: AtomicU64::new(0),
    queries: AtomicU64::new(0),
    compressions: AtomicU64::new(0),
    rounds: AtomicU64::new(0),
    ns: AtomicU64::new(0),
};
impl GrindStats {
    pub fn snapshot(&self) -> [u64; 6] {
        let g = |x: &AtomicU64| x.load(Ordering::Relaxed);
        [g(&self.phases), g(&self.attempts), g(&self.queries), g(&self.compressions), g(&self.rounds), g(&self.ns)]
    }
    /// The counters since `s0` (a `snapshot`), as one line.
    pub fn report_since(&self, s0: &[u64; 6]) -> String {
        let s = self.snapshot();
        let d: Vec<u64> = (0..6).map(|i| s[i] - s0[i]).collect();
        format!(
            "grind_phases={} grind_attempts={} grind_queries={} grind_compressions={} grind_steps={} grind_s={:.4}",
            d[0],
            d[1],
            d[2],
            d[3],
            d[4],
            d[5] as f64 * 1e-9
        )
    }
}

/// Keyed BLAKE2s compressions of a query of `n` bytes (the key block and `⌈n/64⌉` message blocks).
fn compressions(n: usize) -> u64 {
    1 + n.div_ceil(64) as u64
}

/// The grinding batch of a phase: `B = par · sub` nonces; the absorbs go as `par` requests of `sub`
/// queries, one connection each (`Oracle::ask_batches`), each squeeze step as one request of `B`;
/// the smallest winning nonce of the batch is taken, so the proof does not depend on the timing. A
/// batch costs `1 + nsq` sequential steps and wins with probability `1 − (255/256)^B`. The shape
/// minimises the expected time under the cost of a step measured on the service (`grind-bench`,
/// `logs/I7/gb1.log`, `gb2.log`): about `18 µs` for the round trip, `25 µs` per further
/// connection, `0.1 µs` per compression on one connection (the service hashes a request on one
/// thread); `qa`, `qs`: compressions of an absorb and of a squeeze query. Cheap phases get one
/// connection and 256–512 nonces (about 1.2–1.6 batches); the costly absorbs (the caps, `RS0`,
/// `Z2`) spread over several connections. `FLOCK_GRIND=par,sub` fixes the shape (measurements).
fn grind_shape(qa: u64, qs: u64, nsq: usize) -> (usize, usize) {
    static S: OnceLock<Option<(usize, usize)>> = OnceLock::new();
    let fixed = *S.get_or_init(|| {
        std::env::var("FLOCK_GRIND")
            .ok()
            .and_then(|v| {
                let (a, b) = v.split_once(',')?;
                Some((a.trim().parse().ok()?, b.trim().parse().ok()?))
            })
            .filter(|&(a, b): &(usize, usize)| a >= 1 && b >= 1)
    });
    if let Some(f) = fixed {
        return f;
    }
    let step = |np: f64, per: f64, q: f64| 18.0 + 25.0 * (np - 1.0) + per * q * 0.1;
    let mut best = (f64::MAX, (1usize, 256usize));
    for b in [64usize, 128, 256, 512] {
        let batches = 1.0 / (1.0 - (255.0f64 / 256.0).powi(b as i32));
        for np in [1usize, 2, 4, 8] {
            let per = (b / np) as f64;
            let t = batches * (step(np as f64, per, qa as f64) + nsq as f64 * step(1.0, b as f64, qs as f64));
            if t < best.0 {
                best = (t, (np, b / np));
            }
        }
    }
    best.1
}

/// PD: the shape `(batch, depth)` of the service's pipelined search (`Oracle::grind`,
/// `service::Service::grind`): `depth` requests of `batch` nonces in flight, one connection each,
/// every request's chain advanced as soon as its answer arrives. `FLOCK_GRIND_PIPE=B,D` fixes it;
/// `FLOCK_GRIND_PIPE=0` turns the search off (I7's lock-step batches, `grind_shape`).
fn pipe_shape(qa: u64, _qs: u64, nsq: usize) -> Option<(usize, usize)> {
    static S: OnceLock<Option<Option<(usize, usize)>>> = OnceLock::new();
    let fixed = *S.get_or_init(|| {
        let v = std::env::var("FLOCK_GRIND_PIPE").ok()?;
        if v.trim() == "0" {
            return Some(None);
        }
        let (a, b) = v.split_once(',')?;
        Some(Some((a.trim().parse().ok()?, b.trim().parse().ok()?)).filter(|&(a, b): &(usize, usize)| a >= 1 && b >= 1))
    });
    if let Some(f) = fixed {
        return f;
    }
    // measured on the VM (`grind-mix`, `logs/PD/gm/`): a big absorb (the caps, the final message,
    // `RS0`, `Z2`: the service's hashing dominates) is spread over 4 connections of 32 nonces;
    // the rest (round trips dominate) runs 2 requests of 80 nonces
    let _ = nsq;
    Some(if qa > 4 { (32, 4) } else { (80, 2) })
}

thread_local! {
    /// Test hooks (the canaries `pow_canaries`): `NO_GRIND` makes the prover skip the grinding (every
    /// nonce 0, its own proof-of-work assertion off), `NO_POW_CHECK` makes the native verifier ignore
    /// the proof of work (to show that it is the check that rejects an ungrinded proof).
    pub static NO_GRIND: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    pub static NO_POW_CHECK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The nonce `enc64 n ‖ 0^8` (D128 §2.1).
pub fn nonce_bytes(n: u64) -> [u8; NONCE_LEN] {
    let mut b = [0u8; NONCE_LEN];
    b[..8].copy_from_slice(&n.to_le_bytes());
    b
}

pub struct Fs<'a> {
    pub o: &'a dyn Oracle,
    pub st: Digest,
    buf: Vec<u8>,
    /// The current phase (A.4's names), for the item log.
    pub phase: &'static str,
    /// The items asked so far, if logging.
    pub log: Option<Vec<ItemRec>>,
    /// Fiat–Shamir items asked so far (the seed is item 0).
    pub nfs: usize,
    /// The proof-of-work rule (`Pow`), and whether every grinded answer had byte 31 zero.
    pub pow: Pow,
    pub pow_ok: bool,
    /// The winning attempt's squeeze answers (`absorb_won`), taken by the next squeezes in order.
    pend: std::collections::VecDeque<Digest>,
}

impl<'a> Fs<'a> {
    /// `st₀ = H("FRSEED0" ‖ vk ‖ c ‖ hdr)`.
    pub fn seed(o: &'a dyn Oracle, vk: &Digest, c: &Digest, hdr: &[u8], log: bool) -> Fs<'a> {
        let mut q = Vec::with_capacity(7 + 64 + hdr.len());
        q.extend_from_slice(TAG_SEED);
        q.extend_from_slice(vk);
        q.extend_from_slice(c);
        q.extend_from_slice(hdr);
        let st = o.ask(&q);
        let qlen = q.len();
        let mut fs = Fs { o, st, buf: q, phase: "seed", log: log.then(Vec::new), nfs: 1, pow: Pow::Off, pow_ok: true, pend: Default::default() };
        fs.rec("seed", None, None, None, qlen);
        fs
    }
    fn rec(&mut self, q: &'static str, len: Option<usize>, level: Option<usize>, depth: Option<usize>, qlen: usize) {
        if let Some(l) = self.log.as_mut() {
            l.push(ItemRec { phase: self.phase, q, len, level, depth, qlen });
        }
    }
    /// `st ← H("FRABS000" ‖ st ‖ msg)` (every message is a multiple of 16 bytes, A.2).
    pub fn absorb(&mut self, msg: &[u8]) {
        assert_eq!(msg.len() % 16, 0, "an absorbed message is a multiple of 16 bytes");
        assert!(self.pend.is_empty(), "an absorb inside a grinded phase's squeezes");
        self.buf.clear();
        self.buf.extend_from_slice(TAG_ABS);
        self.buf.extend_from_slice(&self.st);
        self.buf.extend_from_slice(msg);
        self.st = self.o.ask(&self.buf);
        self.nfs += 1;
        self.rec("absorb", Some(msg.len()), None, None, 40 + msg.len());
    }
    /// **The grinding loop** (D128 §4.4): `msg` is the payload of the absorb that precedes a grinded
    /// phase of `nsq` squeezes, its last 16 bytes the nonce slot. Try nonces `0, 1, …` (in batches,
    /// `grind_shape`): absorb `msg` with the nonce from the current state, squeeze `nsq` times, and
    /// keep the first nonce whose last answer has byte 31 zero; write it into the slot. Nothing is
    /// recorded in the item log and the state is unchanged. Returns the winning attempt's answers
    /// (`None` with `NO_GRIND`): the caller then absorbs `msg` with them (`absorb_won`), so its
    /// queries are not asked again (PD; I7 asked them once more through `absorb` and `squeeze`).
    /// The oracle's own search (`Oracle::grind`, the service's pipelined one) is used when it has
    /// one; both return the smallest winning nonce, so `π` does not depend on which ran.
    pub fn grind(&self, msg: &mut [u8], nsq: usize) -> Option<GrindWin> {
        self.grind_shaped(msg, nsq, None)
    }

    /// `grind` with the search's shape given (`grind-mix`): `Some(None)` I7's lock-step batches,
    /// `Some(Some((B, D)))` the pipelined search at that shape, `None` the default (`pipe_shape`).
    pub fn grind_shaped(&self, msg: &mut [u8], nsq: usize, shape: Option<Option<(usize, usize)>>) -> Option<GrindWin> {
        assert!(msg.len() >= NONCE_LEN && nsq >= 1);
        assert!(self.pend.is_empty(), "a grinded phase inside another one's squeezes");
        if NO_GRIND.with(|x| x.get()) {
            return None;
        }
        let t = Instant::now();
        let mut pre = Vec::with_capacity(40 + msg.len());
        pre.extend_from_slice(TAG_ABS);
        pre.extend_from_slice(&self.st);
        pre.extend_from_slice(&msg[..msg.len() - NONCE_LEN]);
        let (qa, qs) = (compressions(pre.len() + NONCE_LEN), compressions(40));
        let o = self.o;
        if let Some((batch, depth)) = shape.unwrap_or_else(|| pipe_shape(qa, qs, nsq)) {
            if let Some(w) = o.grind(&GrindJob { pre: &pre, nsq, batch, depth }) {
                return Some(self.won(msg, nsq, w, &format!("pipe {batch}x{depth}"), t));
            }
        }
        let (np, sub) = grind_shape(qa, qs, nsq);
        let mut n0 = 0u64;
        let (mut tries, mut queries, mut comps, mut rounds) = (0u64, 0u64, 0u64, 0u64);
        let win = loop {
            // the batch: its absorbs, then its squeeze chain, every sub-batch at each step at once
            // (`ask_batches`: one request per sub-batch, a round trip a step)
            let mut st: Vec<Vec<Digest>> = vec![vec![[0u8; 32]; sub]; np];
            o.ask_batches(&mut st, &|b, i, buf: &mut Vec<u8>| {
                buf.extend_from_slice(&pre);
                buf.extend_from_slice(&nonce_bytes(n0 + (b * sub + i) as u64));
            });
            // the squeezes: one request of the whole batch (40-byte queries: the round trip dominates);
            // every step's answers kept for the winning attempt
            let mut steps = vec![st.concat()];
            for s in 0..nsq {
                let mut nx = vec![vec![[0u8; 32]; np * sub]];
                let prev = &steps[s];
                o.ask_batches(&mut nx, &|_, i, buf: &mut Vec<u8>| {
                    buf.extend_from_slice(TAG_SQZ);
                    buf.extend_from_slice(&prev[i]);
                });
                steps.push(nx.pop().unwrap());
            }
            let batch = (np * sub) as u64;
            tries += batch;
            queries += batch * (1 + nsq as u64);
            comps += batch * (qa + nsq as u64 * qs);
            rounds += 1 + nsq as u64;
            if let Some(i) = steps[nsq].iter().position(|a| a[POW_BYTE] == 0) {
                break GrindWin {
                    nonce: n0 + i as u64,
                    abs: steps[0][i],
                    sq: (1..=nsq).map(|s| steps[s][i]).collect(),
                    attempts: tries,
                    queries,
                    compressions: comps,
                    rounds,
                };
            }
            n0 += batch;
        };
        Some(self.won(msg, nsq, win, &format!("{np}x{sub}"), t))
    }

    /// Write the winning nonce into the slot and count the search.
    fn won(&self, msg: &mut [u8], nsq: usize, w: GrindWin, shape: &str, t: Instant) -> GrindWin {
        let k = msg.len() - NONCE_LEN;
        msg[k..].copy_from_slice(&nonce_bytes(w.nonce));
        if std::env::var_os("FLOCK_GRIND_LOG").is_some() {
            eprintln!(
                "GRIND-PHASE {} len={} nsq={nsq} shape={shape} attempts={} rounds={} nonce={} us={:.0}",
                self.phase,
                msg.len(),
                w.attempts,
                w.rounds,
                w.nonce,
                t.elapsed().as_secs_f64() * 1e6
            );
        }
        GRIND.phases.fetch_add(1, Ordering::Relaxed);
        GRIND.attempts.fetch_add(w.attempts, Ordering::Relaxed);
        GRIND.queries.fetch_add(w.queries, Ordering::Relaxed);
        GRIND.compressions.fetch_add(w.compressions, Ordering::Relaxed);
        GRIND.rounds.fetch_add(w.rounds, Ordering::Relaxed);
        GRIND.ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        w
    }

    /// `absorb(msg)` for a grinded `msg` whose attempt `w` the grinder asked already: the query is
    /// not asked again but noted (`Oracle::note`: the trace, the replay table) with its answer, and
    /// the next `nsq` squeezes take `w.sq` the same way. Same state, item log and FS count as
    /// `absorb` and the squeezes.
    pub fn absorb_won(&mut self, msg: &[u8], w: GrindWin) {
        assert_eq!(msg.len() % 16, 0, "an absorbed message is a multiple of 16 bytes");
        assert!(self.pend.is_empty(), "an absorb inside a grinded phase's squeezes");
        self.buf.clear();
        self.buf.extend_from_slice(TAG_ABS);
        self.buf.extend_from_slice(&self.st);
        self.buf.extend_from_slice(msg);
        self.st = w.abs;
        self.o.note(&self.buf, &self.st);
        self.nfs += 1;
        self.rec("absorb", Some(msg.len()), None, None, 40 + msg.len());
        self.pend.extend(w.sq);
    }
    /// `st ← H("FRSQZ000" ‖ st)`; the answer is the challenge material.
    pub fn squeeze(&mut self) -> Digest {
        self.buf.clear();
        self.buf.extend_from_slice(TAG_SQZ);
        self.buf.extend_from_slice(&self.st);
        self.st = match self.pend.pop_front() {
            Some(a) => {
                self.o.note(&self.buf, &a);
                a
            }
            None => self.o.ask(&self.buf),
        };
        if self.pow != Pow::Off && pow_at().get(self.nfs).copied().unwrap_or(false) {
            let ok = self.st[POW_BYTE] == 0;
            assert!(ok || self.pow != Pow::Assert, "the prover missed the proof of work of phase {} (item {})", self.phase, self.nfs);
            self.pow_ok &= ok;
        }
        self.nfs += 1;
        self.rec("squeeze", None, None, None, 40);
        self.st
    }
    /// `n` squeezes whose answers are not used (a phase another kind uses).
    pub fn squeezes(&mut self, n: usize) {
        for _ in 0..n {
            self.squeeze();
        }
    }
    /// One F challenge: bytes 0…15 of one squeeze (`chF a 0`).
    pub fn chal_f(&mut self) -> F {
        let a = self.squeeze();
        F::from_bytes(&a[..16])
    }
    /// The `2·nsq` F coordinates of `nsq` squeezes: coordinate `2s + c` is bytes `16c … 16c + 15`
    /// of answer `s` (A.2; S-0 deviation 7).
    pub fn coords(&mut self, nsq: usize) -> Vec<F> {
        let mut v = Vec::with_capacity(2 * nsq);
        for _ in 0..nsq {
            let a = self.squeeze();
            v.push(F::from_bytes(&a[..16]));
            v.push(F::from_bytes(&a[16..32]));
        }
        v
    }
    /// One K challenge: all 32 bytes.
    pub fn chal_k(&mut self) -> K {
        let a = self.squeeze();
        K::from_bytes(&a)
    }
    /// `nsq` squeezes; the first `t` indices of `bits` bits, `⌊256/bits⌋` per answer (index `i` of
    /// answer `a` is bits `[ib, (i+1)b)` of `a` read little-endian, `idxOf`), answers in order.
    pub fn positions(&mut self, nsq: usize, t: usize, bits: usize) -> Vec<u64> {
        let per = 256 / bits;
        assert!(t <= nsq * per, "the item sequence has a squeeze for every position");
        let mut v = Vec::with_capacity(t);
        for _ in 0..nsq {
            let a = self.squeeze();
            let x = u128::from_le_bytes(a[..16].try_into().unwrap());
            let y = u128::from_le_bytes(a[16..].try_into().unwrap());
            for i in 0..per {
                if v.len() == t {
                    break;
                }
                let mut p = 0u64;
                for b in 0..bits {
                    let k = i * bits + b;
                    let bit = if k < 128 { (x >> k) & 1 } else { (y >> (k - 128)) & 1 };
                    p |= (bit as u64) << b;
                }
                v.push(p);
            }
        }
        v
    }
    /// The column query of level `i` (a verifier item).
    pub fn ask_col(&mut self, level: usize, payload: &[u8]) -> Digest {
        assert!(self.pend.is_empty(), "a column query inside a grinded phase's squeezes");
        let mut q = std::mem::take(&mut self.buf);
        q.clear();
        q.extend_from_slice(crate::params::TAG_MCOL);
        q.push(level as u8);
        q.push(0);
        q.extend_from_slice(payload);
        let a = self.o.ask(&q);
        let qlen = q.len();
        self.buf = q;
        self.rec("col", None, Some(level), None, qlen);
        a
    }
    /// The Merkle-node query of level `i` at depth `h` (a verifier item; a dummy asks `0^64`).
    pub fn ask_node(&mut self, level: usize, depth: usize, l: &Digest, r: &Digest) -> Digest {
        assert!(self.pend.is_empty(), "a node query inside a grinded phase's squeezes");
        let mut q = std::mem::take(&mut self.buf);
        q.clear();
        node_query(level as u8, l, r, &mut q);
        let a = self.o.ask(&q);
        self.buf = q;
        self.rec("node", None, Some(level), Some(depth), 72);
        a
    }
}

pub fn f_bytes(v: &[F]) -> Vec<u8> {
    let mut o = Vec::with_capacity(16 * v.len());
    for x in v {
        o.extend_from_slice(&x.to_bytes());
    }
    o
}
pub fn k_bytes(v: &[K]) -> Vec<u8> {
    let mut o = Vec::with_capacity(32 * v.len());
    for x in v {
        o.extend_from_slice(&x.to_bytes());
    }
    o
}

/// The prover's side: each message appended to its A.3 field.
pub struct Writer<'a> {
    pub fs: Fs<'a>,
    fields: Vec<Vec<u8>>,
}
impl<'a> Writer<'a> {
    pub fn new(mut fs: Fs<'a>, hdr: &[u8]) -> Writer<'a> {
        fs.pow = if NO_GRIND.with(|x| x.get()) { Pow::Off } else { Pow::Assert };
        let mut fields: Vec<Vec<u8>> = FIELD_SIZES.iter().map(|&n| Vec::with_capacity(n)).collect();
        fields[0].extend_from_slice(hdr);
        Writer { fs, fields }
    }
    /// Append to field `f` and absorb.
    pub fn send(&mut self, f: usize, b: &[u8]) {
        self.fields[f].extend_from_slice(b);
        self.fs.absorb(b);
    }
    pub fn send_f(&mut self, f: usize, v: &[F]) {
        self.send(f, &f_bytes(v));
    }
    pub fn send_k(&mut self, f: usize, v: &[K]) {
        self.send(f, &k_bytes(v));
    }
    /// Send `body ‖ nonce` to field `f` (absorbed as one message), the nonce ground for the `nsq`
    /// squeezes of the grinded phase that follows (`Fs::grind`). An empty `body` is a standalone
    /// nonce absorb (`S1n`, `Lr1n`, `E1n`, `B'n`, `P3n`).
    pub fn send_pow(&mut self, f: usize, body: &[u8], nsq: usize) {
        let mut b = Vec::with_capacity(body.len() + NONCE_LEN);
        b.extend_from_slice(body);
        b.extend_from_slice(&[0u8; NONCE_LEN]);
        match self.fs.grind(&mut b, nsq) {
            Some(w) => {
                self.fields[f].extend_from_slice(&b);
                self.fs.absorb_won(&b, w);
            }
            None => self.send(f, &b),
        }
    }
    pub fn send_f_pow(&mut self, f: usize, v: &[F], nsq: usize) {
        self.send_pow(f, &f_bytes(v), nsq);
    }
    /// One F sumcheck round of the grinded format (D128 §2.1): degree 3 sends `c₀ ‖ c₁ ‖ c₂ ‖ nonce`
    /// (64 B), degree 2 `c₀ ‖ c₁ ‖ nonce` (48 B, the verifier derives `c₂ = claim + c₁`); returns
    /// the challenge (the round's one squeeze, its byte 31 zero).
    pub fn round_f(&mut self, f: usize, c: &[F]) -> F {
        assert!(c.len() == 2 || c.len() == 3);
        self.send_f_pow(f, c, 1);
        self.fs.chal_f()
    }
    /// Append to field `f` without absorbing (columns, siblings; caps absorbed separately).
    pub fn put(&mut self, f: usize, b: &[u8]) {
        self.fields[f].extend_from_slice(b);
    }
    /// The bytes written so far to field `f`.
    pub fn field(&self, f: usize) -> &[u8] {
        &self.fields[f]
    }
    /// `π`: the fields in A.3's order; every field must have its size.
    pub fn finish(self) -> Vec<u8> {
        assert!(self.fs.pend.is_empty(), "a grinded phase's squeezes left unasked");
        let mut pi = Vec::with_capacity(PI_SIZE);
        for (f, b) in self.fields.iter().enumerate() {
            assert_eq!(b.len(), FIELD_SIZES[f], "field {f} of π");
            pi.extend_from_slice(b);
        }
        pi
    }
}

/// The verifier's side: one cursor per field; the flag `ok` collects every check (a failed check
/// does not stop the run: the query sequence is the same for every `π`, as `gen`'s is).
pub struct Reader<'a, 'b> {
    pub fs: Fs<'a>,
    pub pi: &'b [u8],
    cur: [usize; N_FIELDS],
    pub ok: bool,
}
impl<'a, 'b> Reader<'a, 'b> {
    /// `pi` has `piSize` bytes; field 0 (`hdr`) was read by the seed.
    pub fn new(mut fs: Fs<'a>, pi: &'b [u8]) -> Reader<'a, 'b> {
        assert_eq!(pi.len(), PI_SIZE);
        fs.pow = if NO_POW_CHECK.with(|x| x.get()) { Pow::Off } else { Pow::Check };
        let mut cur = [0usize; N_FIELDS];
        for (f, c) in cur.iter_mut().enumerate() {
            *c = field_off(f);
        }
        cur[0] = field_off(1);
        Reader { fs, pi, cur, ok: true }
    }
    /// Record one check (`FLOCK_DEBUG_V`: print the location of a failed one).
    #[track_caller]
    pub fn check(&mut self, c: bool) {
        if !c && self.ok && std::env::var_os("FLOCK_DEBUG_V").is_some() {
            eprintln!("verifier: first failed check at {} (phase {})", std::panic::Location::caller(), self.fs.phase);
        }
        self.ok &= c;
    }
    /// The next `n` bytes of field `f` (the layout is static: reading past a field is a bug).
    pub fn take(&mut self, f: usize, n: usize) -> &'b [u8] {
        let o = self.cur[f];
        assert!(o + n <= field_off(f) + FIELD_SIZES[f], "read past field {f}");
        self.cur[f] += n;
        &self.pi[o..o + n]
    }
    pub fn recv(&mut self, f: usize, n: usize) -> &'b [u8] {
        let r = self.take(f, n);
        self.fs.absorb(r);
        r
    }
    pub fn recv_f(&mut self, f: usize, n: usize) -> Vec<F> {
        self.recv(f, 16 * n).chunks_exact(16).map(F::from_bytes).collect()
    }
    /// The payload of an absorb that carries a nonce (`body ‖ nonce`, D128 §2.1): absorbs all of it
    /// and returns the body; the nonce is not read (any value is accepted).
    pub fn recv_pow(&mut self, f: usize, body: usize) -> &'b [u8] {
        &self.recv(f, body + NONCE_LEN)[..body]
    }
    pub fn recv_f_pow(&mut self, f: usize, n: usize) -> Vec<F> {
        self.recv_pow(f, 16 * n).chunks_exact(16).map(F::from_bytes).collect()
    }
    pub fn recv_k(&mut self, f: usize, n: usize) -> Vec<K> {
        self.recv(f, 32 * n).chunks_exact(32).map(K::from_bytes).collect()
    }
    /// Every check passed, the proof of work included.
    pub fn accepted(&self) -> bool {
        self.ok && self.fs.pow_ok
    }
    /// Every field read to its end.
    pub fn all_read(&self) -> bool {
        (0..N_FIELDS).all(|f| self.cur[f] == field_off(f) + FIELD_SIZES[f])
    }
}
