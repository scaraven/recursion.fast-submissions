//! The random oracle every Fiat–Shamir step and every Merkle hash queries: `O(q) = Keccak-256(k ‖ q)`
//! (`service/PROTOCOL.md` §2.0), answered by the service (`QUERY`, the service run) or computed in-process from
//! `/work/oracle.key` ([`Local`], the timed passes). Both give the same bytes, so nothing the prover writes depends
//! on which one is installed.
//!
//! Moved here from the binary's `oracle.rs` (P1) so that leanVM's crates (`fiat_shamir_prover`, `pcs`) can reach
//! the installed oracle. The service client stays in the binary and implements [`Oracle`].
//!
//! Batching (not normative, changes no byte; `stages/R0-service.md`): [`batch`] spreads a set of queries over
//! [`conns`] threads, each asking chunks of [`CHUNK`] queries on its own connection; one connection per CPU (8 on
//! the 4C/8T machine) whatever the compute pool's size.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::Instant;

use crate::Digest;

/// Writes query `i` into the (cleared) buffer.
pub type Builder<'a> = dyn Fn(usize, &mut Vec<u8>) + Sync + 'a;

/// Queries a batch asks per chunk (one `QUERY` request of at most 4,096 items).
pub const CHUNK: usize = 4096;

pub trait Oracle: Sync + Send {
    /// One answer (latency-bound: a chain step).
    fn ask(&self, q: &[u8]) -> Digest;
    /// `out[i] = O(q_i)` for the queries `build` writes, on the calling thread (one connection).
    fn ask_many_here(&self, out: &mut [Digest], build: &Builder) {
        let mut buf = Vec::new();
        for (i, o) in out.iter_mut().enumerate() {
            buf.clear();
            build(i, &mut buf);
            *o = self.ask(&buf);
        }
    }
    /// `out[i] = O(prefix ‖ LE64(first + i))`: a nonce window. [`Local`] hashes the prefix once.
    fn ask_nonces_here(&self, prefix: &[u8], first: u64, out: &mut [Digest]) {
        self.ask_many_here(out, &|i, b: &mut Vec<u8>| {
            b.extend_from_slice(prefix);
            b.extend_from_slice(&(first + i as u64).to_le_bytes());
        });
    }
    fn name(&self) -> &'static str;
}

/// `PRF_k(q) = Keccak-256(k ‖ q)` in-process: the hasher after the 32 key bytes, cloned per query.
///
/// R5 (PATCHES.md): a batch ([`Oracle::ask_many_here`], [`Oracle::ask_nonces_here`]) goes through leanVM's
/// multi-way Keccak (`keccak256::hash_many_from_state`, [`keccak256::LANES`] states per permutation: 8 on AVX-512),
/// runs of equal-length queries at a time; byte-identical to the one-query form, which stays the fallback
/// (`LVM6_KECCAK=scalar`, or a build whose `LANES` is 1).
#[derive(Clone)]
pub struct Local {
    h: keccak256::Hasher,
    key: [u8; 32],
}

impl Local {
    pub fn keyed(key: &[u8; 32]) -> Self {
        let mut h = keccak256::Hasher::new();
        h.update(key);
        Self { h, key: *key }
    }
}

/// Whether batches use the multi-way permutation (`LVM6_KECCAK=scalar` turns it off).
pub fn multiway() -> bool {
    static M: OnceLock<bool> = OnceLock::new();
    *M.get_or_init(|| keccak256::LANES > 1 && std::env::var("LVM6_KECCAK").map_or(true, |v| v != "scalar"))
}

/// The sponge state after absorbing the whole `RATE`-byte blocks of `bytes` (a prefix every input shares), and the
/// number of bytes absorbed.
fn absorb_blocks(bytes: &[u8]) -> ([u64; keccak256::STATE_LANES], usize) {
    let mut st = [0u64; keccak256::STATE_LANES];
    let full = bytes.len() / keccak256::RATE * keccak256::RATE;
    for block in bytes[..full].chunks_exact(keccak256::RATE) {
        for (s, w) in st.iter_mut().zip(block.chunks_exact(8)) {
            *s ^= u64::from_le_bytes(w.try_into().unwrap());
        }
        keccak256::keccak_f(&mut st);
    }
    (st, full)
}

impl Oracle for Local {
    fn ask(&self, q: &[u8]) -> Digest {
        let mut h = self.h.clone();
        h.update(q);
        h.finalize()
    }
    fn ask_many_here(&self, out: &mut [Digest], build: &Builder) {
        if !multiway() {
            let mut buf = Vec::new();
            for (i, o) in out.iter_mut().enumerate() {
                buf.clear();
                build(i, &mut buf);
                *o = self.ask(&buf);
            }
            return;
        }
        // Runs of equal-length queries, each `k ‖ q`, hashed `LANES` at a time.
        let zero = [0u64; keccak256::STATE_LANES];
        let (mut data, mut q) = (Vec::new(), Vec::new());
        let (mut run, mut len) = (0usize, usize::MAX);
        let flush = |data: &mut Vec<u8>, out: &mut [Digest], len: usize| {
            if !out.is_empty() {
                keccak256::hash_many_from_state(data, 32 + len, &zero, out.as_flattened_mut());
            }
            data.clear();
        };
        for i in 0..out.len() {
            q.clear();
            build(i, &mut q);
            if q.len() != len {
                flush(&mut data, &mut out[run..i], len);
                (run, len) = (i, q.len());
            }
            data.extend_from_slice(&self.key);
            data.extend_from_slice(&q);
        }
        let n = out.len();
        flush(&mut data, &mut out[run..n], len);
    }
    fn ask_nonces_here(&self, prefix: &[u8], first: u64, out: &mut [Digest]) {
        if out.is_empty() {
            return;
        }
        if !multiway() {
            let mut h = self.h.clone();
            h.update(prefix);
            for (i, o) in out.iter_mut().enumerate() {
                let mut g = h.clone();
                g.update(&(first + i as u64).to_le_bytes());
                *o = g.finalize();
            }
            return;
        }
        // `k ‖ prefix`'s whole blocks once, then the rest and the nonce per input.
        let common = [&self.key[..], prefix].concat();
        let (st, done) = absorb_blocks(&common);
        let rest = &common[done..];
        let len = rest.len() + 8;
        let mut data = Vec::with_capacity(out.len() * len);
        for i in 0..out.len() as u64 {
            data.extend_from_slice(rest);
            data.extend_from_slice(&(first + i).to_le_bytes());
        }
        keccak256::hash_many_from_state(&data, len, &st, out.as_flattened_mut());
    }
    fn name(&self) -> &'static str {
        "local"
    }
}

// ------------------------------------------------------------------ the installed oracle

static ORACLE: OnceLock<Box<dyn Oracle>> = OnceLock::new();

/// Install the process's oracle (once, after `go`).
pub fn install(o: Box<dyn Oracle>) {
    if ORACLE.set(o).is_err() {
        panic!("the oracle is installed once");
    }
}

pub fn installed() -> bool {
    ORACLE.get().is_some()
}

pub fn get() -> &'static dyn Oracle {
    ORACLE.get().expect("no oracle installed").as_ref()
}

// ------------------------------------------------------------------ connections and counters

/// Threads (= service connections) a batch uses: `LVM6_CONNS`, else `max(8, pool size)`, at most 30 (the service
/// allows 32 connections; one more is the `SIGN` client's).
pub fn conns() -> usize {
    static C: OnceLock<usize> = OnceLock::new();
    *C.get_or_init(|| {
        std::env::var("LVM6_CONNS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or_else(|| parallel::num_threads().max(8))
            .clamp(1, 30)
    })
}

static QUERIES: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
static PERMS: AtomicU64 = AtomicU64::new(0);
static WAIT_NS: AtomicU64 = AtomicU64::new(0);

/// `⌊(32 + |q|)/136⌋ + 1`: the service's permutations for one keyed query.
pub fn perms(len: usize) -> u64 {
    ((32 + len) / 136 + 1) as u64
}

fn note(n: u64, bytes: u64, p: u64, t: Instant) {
    QUERIES.fetch_add(n, Ordering::Relaxed);
    BYTES.fetch_add(bytes, Ordering::Relaxed);
    PERMS.fetch_add(p, Ordering::Relaxed);
    WAIT_NS.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
}

/// Counted single query.
pub fn ask(o: &dyn Oracle, q: &[u8]) -> Digest {
    let t = Instant::now();
    let a = o.ask(q);
    note(1, q.len() as u64, perms(q.len()), t);
    a
}

/// Run `f(chunk_index, chunk)` over the chunks of `out` on up to [`conns`] threads (the calling thread when there
/// is one chunk). Each chunk's answers are functions of its queries: the split changes no byte.
fn spread(out: &mut [Digest], chunk: usize, f: &(dyn Fn(usize, &mut [Digest]) + Sync)) {
    let n_chunks = out.len().div_ceil(chunk);
    let threads = conns().min(n_chunks);
    if threads <= 1 {
        for (c, sub) in out.chunks_mut(chunk).enumerate() {
            f(c, sub);
        }
        return;
    }
    let base = parallel::SendPtr(out.as_mut_ptr());
    let len = out.len();
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                let base = &base;
                loop {
                    let c = next.fetch_add(1, Ordering::Relaxed);
                    if c >= n_chunks {
                        break;
                    }
                    let off = c * chunk;
                    // SAFETY: chunk `c` is taken by exactly one thread (the counter), and `out` outlives the scope.
                    let sub = unsafe { base.slice(off, chunk.min(len - off)) };
                    f(c, sub);
                }
            });
        }
    });
}

/// `out[i] = O(q_i)` for the queries `build` writes, over [`conns`] connections in chunks of [`CHUNK`].
pub fn batch(o: &dyn Oracle, out: &mut [Digest], build: &Builder) {
    let t = Instant::now();
    let (lens, ps) = (AtomicU64::new(0), AtomicU64::new(0));
    spread(out, CHUNK, &|c, sub| {
        let off = c * CHUNK;
        o.ask_many_here(sub, &|i, b: &mut Vec<u8>| {
            let s = b.len();
            build(off + i, b);
            let l = b.len() - s;
            lens.fetch_add(l as u64, Ordering::Relaxed);
            ps.fetch_add(perms(l), Ordering::Relaxed);
        });
    });
    note(out.len() as u64, lens.into_inner(), ps.into_inner(), t);
}

/// `out[i] = O(prefix ‖ LE64(first + i))` over [`conns`] connections.
pub fn batch_nonces(o: &dyn Oracle, prefix: &[u8], first: u64, out: &mut [Digest]) {
    let t = Instant::now();
    let chunk = if out.len() <= 256 { out.len().max(1) } else { CHUNK.min(out.len().div_ceil(conns())).max(64) };
    spread(out, chunk, &|c, sub| o.ask_nonces_here(prefix, first + (c * chunk) as u64, sub));
    let q = prefix.len() + 8;
    note(out.len() as u64, (q * out.len()) as u64, perms(q) * out.len() as u64, t);
}

pub fn report() -> String {
    format!(
        "oracle {}: queries {} bytes {} perms {} wait {:.3} s",
        ORACLE.get().map_or("none", |o| o.name()),
        QUERIES.load(Ordering::Relaxed),
        BYTES.load(Ordering::Relaxed),
        PERMS.load(Ordering::Relaxed),
        WAIT_NS.load(Ordering::Relaxed) as f64 * 1e-9
    )
}

#[cfg(test)]
mod r5_tests {
    use super::*;

    /// R5: the multi-way batch forms equal the one-query form (mixed lengths, multi-block keys ‖ prefixes).
    #[test]
    fn multiway_matches_scalar() {
        let o = Local::keyed(&[0x5A; 32]);
        let lens: Vec<usize> = (0..300).map(|i| [0, 1, 7, 64, 64, 64, 95, 96, 103, 104, 135, 136, 239, 256, 368][i % 15] + (i / 150)).collect();
        let q = |i: usize, b: &mut Vec<u8>| b.extend((0..lens[i]).map(|j| (i * 31 + j * 7) as u8));
        let mut out = vec![[0u8; 32]; lens.len()];
        o.ask_many_here(&mut out, &q);
        for (i, d) in out.iter().enumerate() {
            let mut b = Vec::new();
            q(i, &mut b);
            assert_eq!(*d, o.ask(&b), "query {i}");
        }
        for plen in [0usize, 40, 95, 96, 103, 104, 200, 300] {
            let prefix: Vec<u8> = (0..plen).map(|j| (j * 13) as u8).collect();
            let mut out = vec![[0u8; 32]; 37];
            o.ask_nonces_here(&prefix, 1000, &mut out);
            for (i, d) in out.iter().enumerate() {
                assert_eq!(*d, o.ask(&[&prefix[..], &(1000 + i as u64).to_le_bytes()].concat()), "prefix {plen} nonce {i}");
            }
        }
    }
}
