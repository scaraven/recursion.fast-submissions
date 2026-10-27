//! Fiat–Shamir through the oracle (blueprint rev. 3.7 §1.2, A.2, A.4): `seed`, `absorb`, `squeeze`
//! queries, the challenge maps, and `π` as A.3's eighteen fields. The prover writes each message
//! into its field (`Writer`); the verifier reads each field with its own cursor (`Reader`), so the
//! reading order is the item order of A.4 while `π` is grouped by field.
//!
//! `Fs` can log every query it asks as an A.4 item (`ItemRec`: phase, query kind, payload length,
//! Merkle level and depth, query length), the form of `logs/S-0/dump/items.json` (the KAT).

use crate::blake2s::Digest;
use crate::field::{F, K};
use crate::merkle::{col_query, node_query};
use crate::oracle::Oracle;
use crate::params::{field_off, FIELD_SIZES, N_FIELDS, PI_SIZE, TAG_ABS, TAG_SEED, TAG_SQZ};

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

pub struct Fs<'a> {
    pub o: &'a dyn Oracle,
    pub st: Digest,
    buf: Vec<u8>,
    /// The current phase (A.4's names), for the item log.
    pub phase: &'static str,
    /// The items asked so far, if logging.
    pub log: Option<Vec<ItemRec>>,
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
        let mut fs = Fs { o, st, buf: q, phase: "seed", log: log.then(Vec::new) };
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
        self.buf.clear();
        self.buf.extend_from_slice(TAG_ABS);
        self.buf.extend_from_slice(&self.st);
        self.buf.extend_from_slice(msg);
        self.st = self.o.ask(&self.buf);
        self.rec("absorb", Some(msg.len()), None, None, 40 + msg.len());
    }
    /// `st ← H("FRSQZ000" ‖ st)`; the answer is the challenge material.
    pub fn squeeze(&mut self) -> Digest {
        self.buf.clear();
        self.buf.extend_from_slice(TAG_SQZ);
        self.buf.extend_from_slice(&self.st);
        self.st = self.o.ask(&self.buf);
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
    pub fn ask_col(&mut self, level: usize, col: &[F]) -> Digest {
        let mut q = std::mem::take(&mut self.buf);
        q.clear();
        col_query(level as u8, col, &mut q);
        let a = self.o.ask(&q);
        let qlen = q.len();
        self.buf = q;
        self.rec("col", None, Some(level), None, qlen);
        a
    }
    /// The Merkle-node query of level `i` at depth `h` (a verifier item; a dummy asks `0^64`).
    pub fn ask_node(&mut self, level: usize, depth: usize, l: &Digest, r: &Digest) -> Digest {
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
    pub fn new(fs: Fs<'a>, hdr: &[u8]) -> Writer<'a> {
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
    pub fn new(fs: Fs<'a>, pi: &'b [u8]) -> Reader<'a, 'b> {
        assert_eq!(pi.len(), PI_SIZE);
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
    pub fn recv_k(&mut self, f: usize, n: usize) -> Vec<K> {
        self.recv(f, 32 * n).chunks_exact(32).map(K::from_bytes).collect()
    }
    /// Every field read to its end.
    pub fn all_read(&self) -> bool {
        (0..N_FIELDS).all(|f| self.cur[f] == field_off(f) + FIELD_SIZES[f])
    }
}
