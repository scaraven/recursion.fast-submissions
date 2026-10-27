//! The v4 byte layouts the prover writes and the native `acc` reads, byte for byte as the contract:
//!
//! * witnesses `encode w` = the bytes of `witWords w` (`Library/Words.lean`, `WitnessSending.encode`)
//!   and the strict decoder `decodeWit (packBytes π)` (`Contract/Extractor.lean`), which ignores the
//!   words after the witness;
//! * the signed-proof file (`harness/FORMAT.md`);
//! * the trace digest and the WOTS/Merkle signature check `SigOk` (`Contract/Signature.lean`).
//!
//! All integers are little-endian `u64` words; byte strings are length-prefixed and zero-padded to
//! a whole word; a digest is 4 words.

use crate::blake2s::{Blake2s, Digest};
use crate::oracle::Trace;

pub const TAG_TRACE: u8 = 0x54;
pub const TAG_WOTS: u8 = 0x57;
pub const TAG_WOTS_LEAF: u8 = 0x4B;
pub const TAG_SIG_NODE: u8 = 0x4D;
pub const WOTS_LEN: usize = 133;
pub const SIG_HEIGHT: usize = 16;
/// `proofCap`, `queryCap` (`Contract/Relation.lean`).
pub const PROOF_CAP: usize = 1 << 20;
pub const QUERY_CAP: usize = 1 << 20;

/// A signature (`Contract/Relation.lean`, `Sig`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sig {
    pub idx: u64,
    pub ots: Vec<Digest>,
    pub path: Vec<Digest>,
}

/// A signed proof `(π, tr, σ)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signed {
    pub pi: Vec<u8>,
    pub tr: Trace,
    pub sig: Sig,
}

/// A witness (`Contract/Relation.lean`, `Wit`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Wit {
    Leaf { s: Digest, n: u64 },
    Node { c1: Digest, c2: Digest, p1: Box<Signed>, p2: Box<Signed> },
}

fn pad8(v: &mut Vec<u8>) {
    v.resize(v.len().div_ceil(8) * 8, 0);
}

fn put_bytes(v: &mut Vec<u8>, b: &[u8]) {
    v.extend_from_slice(&(b.len() as u64).to_le_bytes());
    v.extend_from_slice(b);
    pad8(v);
}

/// `sigWords σ` as bytes.
pub fn put_sig(v: &mut Vec<u8>, s: &Sig) {
    v.extend_from_slice(&s.idx.to_le_bytes());
    for d in s.ots.iter().chain(s.path.iter()) {
        v.extend_from_slice(d);
    }
}

/// `signedWords p` as bytes.
pub fn put_signed(v: &mut Vec<u8>, p: &Signed) {
    put_bytes(v, &p.pi);
    v.extend_from_slice(&(p.tr.len() as u64).to_le_bytes());
    for (q, a) in &p.tr {
        put_bytes(v, q);
        v.extend_from_slice(a);
    }
    put_sig(v, &p.sig);
}

/// `encode w`: the bytes of `witWords w`.
pub fn encode(w: &Wit) -> Vec<u8> {
    let mut v = Vec::new();
    match w {
        Wit::Leaf { s, n } => {
            v.extend_from_slice(&0u64.to_le_bytes());
            v.extend_from_slice(s);
            v.extend_from_slice(&n.to_le_bytes());
        }
        Wit::Node { c1, c2, p1, p2 } => {
            v.extend_from_slice(&1u64.to_le_bytes());
            v.extend_from_slice(c1);
            v.extend_from_slice(c2);
            put_signed(&mut v, p1);
            put_signed(&mut v, p2);
        }
    }
    v
}

/// The strict word reader of `decodeWit` over the packed bytes of `π` (the last word zero-padded).
struct Rd<'a> {
    b: &'a [u8],
    /// position in words
    w: usize,
}

impl<'a> Rd<'a> {
    fn words(&self) -> usize {
        self.b.len().div_ceil(8)
    }
    fn word(&mut self) -> Option<u64> {
        if self.w >= self.words() {
            return None;
        }
        let o = 8 * self.w;
        let mut t = [0u8; 8];
        let e = (o + 8).min(self.b.len());
        t[..e - o].copy_from_slice(&self.b[o..e]);
        self.w += 1;
        Some(u64::from_le_bytes(t))
    }
    /// `readBytes n`: `⌈n/8⌉` words, the first `n` bytes (the padding bytes are not checked).
    fn bytes(&mut self, n: u64) -> Option<Vec<u8>> {
        if n == 0 {
            return Some(vec![]);
        }
        let nw = n / 8 + u64::from(n % 8 != 0);
        if nw > (self.words() - self.w) as u64 {
            return None;
        }
        let o = 8 * self.w;
        let n = n as usize;
        let mut out = vec![0u8; n];
        let e = (o + n).min(self.b.len());
        out[..e - o].copy_from_slice(&self.b[o..e]);
        self.w += nw as usize;
        Some(out)
    }
    fn digest(&mut self) -> Option<Digest> {
        Some(self.bytes(32)?.try_into().unwrap())
    }
    fn string(&mut self) -> Option<Vec<u8>> {
        let n = self.word()?;
        self.bytes(n)
    }
    fn sig(&mut self) -> Option<Sig> {
        let idx = self.word()?;
        let ots = (0..WOTS_LEN).map(|_| self.digest()).collect::<Option<Vec<_>>>()?;
        let path = (0..SIG_HEIGHT).map(|_| self.digest()).collect::<Option<Vec<_>>>()?;
        Some(Sig { idx, ots, path })
    }
    fn signed(&mut self) -> Option<Signed> {
        let pi = self.string()?;
        let m = self.word()?;
        // every entry takes at least 5 words
        if m > ((self.words() - self.w) / 5) as u64 {
            return None;
        }
        let mut tr = Vec::with_capacity(m as usize);
        for _ in 0..m {
            let q = self.string()?;
            let a = self.digest()?;
            tr.push((q, a));
        }
        let sig = self.sig()?;
        Some(Signed { pi, tr, sig })
    }
    fn wit(&mut self) -> Option<Wit> {
        match self.word()? {
            0 => Some(Wit::Leaf { s: self.digest()?, n: self.word()? }),
            1 => {
                let c1 = self.digest()?;
                let c2 = self.digest()?;
                let p1 = Box::new(self.signed()?);
                let p2 = Box::new(self.signed()?);
                Some(Wit::Node { c1, c2, p1, p2 })
            }
            _ => None,
        }
    }
}

/// `decode π` (`WitnessSending.decode`): the witness read strictly from the front of `π`'s packed
/// words, and the number of bytes (whole words) it occupies.
pub fn decode(pi: &[u8]) -> Option<(Wit, usize)> {
    let mut r = Rd { b: pi, w: 0 };
    let w = r.wit()?;
    Some((w, 8 * r.w))
}

/// The signed-proof file (`harness/FORMAT.md`).
pub fn to_file(p: &Signed) -> Vec<u8> {
    let tb: usize = p.tr.iter().map(|(q, _)| 40 + q.len()).sum();
    let mut v = Vec::with_capacity(8 + p.pi.len() + 8 + tb + 8 + 32 * (WOTS_LEN + SIG_HEIGHT));
    v.extend_from_slice(&(p.pi.len() as u64).to_le_bytes());
    v.extend_from_slice(&p.pi);
    v.extend_from_slice(&(p.tr.len() as u64).to_le_bytes());
    for (q, a) in &p.tr {
        v.extend_from_slice(&(q.len() as u64).to_le_bytes());
        v.extend_from_slice(q);
        v.extend_from_slice(a);
    }
    put_sig(&mut v, &p.sig);
    v
}

/// Parse a signed-proof file strictly: `None` unless `b` is exactly one encoding. The counts of
/// the signature are fixed by the format (133 chain values, 16 siblings).
pub fn from_file(b: &[u8]) -> Option<Signed> {
    let mut o = 0usize;
    let mut take = |n: u64| -> Option<&[u8]> {
        if n > (b.len() - o) as u64 {
            return None;
        }
        let r = &b[o..o + n as usize];
        o += n as usize;
        Some(r)
    };
    let u64_ = |x: &[u8]| u64::from_le_bytes(x.try_into().unwrap());
    let pl = u64_(take(8)?);
    let pi = take(pl)?.to_vec();
    let m = u64_(take(8)?);
    if m > b.len() as u64 {
        return None;
    }
    let mut tr = Vec::with_capacity(m as usize);
    for _ in 0..m {
        let ql = u64_(take(8)?);
        let q = take(ql)?.to_vec();
        let a: Digest = take(32)?.try_into().unwrap();
        tr.push((q, a));
    }
    let idx = u64_(take(8)?);
    let mut ds = Vec::with_capacity(WOTS_LEN + SIG_HEIGHT);
    for _ in 0..WOTS_LEN + SIG_HEIGHT {
        ds.push(<Digest>::try_from(take(32)?).unwrap());
    }
    if o != b.len() {
        return None;
    }
    let path = ds.split_off(WOTS_LEN);
    Some(Signed { pi, tr, sig: Sig { idx, ots: ds, path } })
}

/// `traceDigest tr = BLAKE2s-256(0x54 ‖ (enc64 |q| ‖ q ‖ a)…)`.
pub fn trace_digest(tr: &[(Vec<u8>, Digest)]) -> Digest {
    let mut h = Blake2s::new();
    h.update(&[TAG_TRACE]);
    for (q, a) in tr {
        h.update(&(q.len() as u64).to_le_bytes()).update(q).update(a);
    }
    h.finalize()
}

/// `wotsDigits m`: 128 base-4 digits (byte `i` gives digits `4i … 4i+3`, low bits first), then
/// the 5 digits of the checksum `Σ (3 − dᵢ)`.
pub fn wots_digits(m: &Digest) -> Vec<u32> {
    let mut d: Vec<u32> = Vec::with_capacity(WOTS_LEN);
    for &b in m {
        for t in 0..4 {
            d.push(((b >> (2 * t)) & 3) as u32);
        }
    }
    let c: u32 = d.iter().map(|x| 3 - x).sum();
    for t in 0..5 {
        d.push((c >> (2 * t)) & 3);
    }
    d
}

/// `wotsStep j i s x = BLAKE2s-256(0x57 ‖ enc64 j ‖ i ‖ s ‖ x)`.
fn wots_step(j: u64, i: usize, s: u32, x: &Digest) -> Digest {
    Blake2s::new().update(&[TAG_WOTS]).update(&j.to_le_bytes()).update(&[i as u8, s as u8]).update(x).finalize()
}

fn sig_node(l: &Digest, r: &Digest) -> Digest {
    Blake2s::new().update(&[TAG_SIG_NODE]).update(l).update(r).finalize()
}

/// `SigOk vk m σ`: index below `2^16`, 133 chain values, 16 siblings, and the root they determine
/// is `vk`.
pub fn sig_ok(vk: &Digest, m: &Digest, s: &Sig) -> bool {
    if s.idx >= 1 << SIG_HEIGHT || s.ots.len() != WOTS_LEN || s.path.len() != SIG_HEIGHT {
        return false;
    }
    let j = s.idx;
    let mut leaf = Blake2s::new();
    leaf.update(&[TAG_WOTS_LEAF]).update(&j.to_le_bytes());
    for (i, (d, x)) in wots_digits(m).iter().zip(s.ots.iter()).enumerate() {
        let mut v = *x;
        for pos in *d..3 {
            v = wots_step(j, i, pos, &v);
        }
        leaf.update(&v);
    }
    let mut cur = leaf.finalize();
    let mut k = j;
    for sib in &s.path {
        cur = if k % 2 == 0 { sig_node(&cur, sib) } else { sig_node(sib, &cur) };
        k /= 2;
    }
    cur == *vk
}

/// A **test-only** signer: one-time key `j = 0` with chain starts from `seed` and an arbitrary
/// path; returns the public key it determines and the signature of `m`. Every message signed with
/// the same seed verifies under the same key (the key is reused, so this is no signature scheme;
/// it exists so unit tests can make `SigOk`-valid signatures without the service).
pub fn toy_sign(seed: u8, m: &Digest) -> (Digest, Sig) {
    let j = 0u64;
    let d = wots_digits(m);
    let mut ots = Vec::with_capacity(WOTS_LEN);
    let mut leaf = Blake2s::new();
    leaf.update(&[TAG_WOTS_LEAF]).update(&j.to_le_bytes());
    for i in 0..WOTS_LEN {
        let mut x: Digest = Blake2s::new().update(&[0xEE, seed, i as u8]).finalize();
        for pos in 0..3u32 {
            if pos == d[i] {
                ots.push(x);
            }
            x = wots_step(j, i, pos, &x);
        }
        if d[i] == 3 {
            ots.push(x);
        }
        leaf.update(&x);
    }
    let path: Vec<Digest> = (0..SIG_HEIGHT).map(|t| [t as u8 ^ seed; 32]).collect();
    let mut cur = leaf.finalize();
    for sib in &path {
        cur = sig_node(&cur, sib);
    }
    (cur, Sig { idx: j, ots, path })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sig(seed: u8) -> Sig {
        Sig { idx: seed as u64, ots: (0..133).map(|i| [seed ^ i as u8; 32]).collect(), path: (0..16).map(|i| [i as u8; 32]).collect() }
    }

    #[test]
    fn encode_decode_roundtrip() {
        let leaf = Wit::Leaf { s: [3; 32], n: 16 };
        let e = encode(&leaf);
        assert_eq!(e.len(), 48);
        assert_eq!(decode(&e), Some((leaf.clone(), 48)));
        let p = Signed { pi: e.clone(), tr: vec![], sig: sig(1) };
        let q = Signed { pi: vec![1, 2, 3], tr: vec![(vec![9; 13], [5; 32]), (vec![], [6; 32])], sig: sig(2) };
        let node = Wit::Node { c1: [1; 32], c2: [2; 32], p1: Box::new(p), p2: Box::new(q) };
        let e = encode(&node);
        assert_eq!(e.len() % 8, 0);
        assert_eq!(decode(&e), Some((node.clone(), e.len())));
        // trailing bytes are ignored by decode
        let mut t = e.clone();
        t.extend_from_slice(&[7; 13]);
        assert_eq!(decode(&t), Some((node.clone(), e.len())));
        // a truncated encoding decodes to nothing
        assert_eq!(decode(&e[..e.len() - 8]), None);
        assert_eq!(decode(&e[..e.len() - 1]).map(|x| x.1), Some(e.len()));
    }

    #[test]
    fn file_roundtrip_strict() {
        let p = Signed { pi: vec![1, 2, 3, 4, 5], tr: vec![(vec![9; 13], [5; 32])], sig: sig(3) };
        let f = to_file(&p);
        assert_eq!(f.len(), 8 + 5 + 8 + (8 + 13 + 32) + 8 + 4768);
        assert_eq!(from_file(&f), Some(p));
        let mut g = f.clone();
        g.push(0);
        assert_eq!(from_file(&g), None);
        assert_eq!(from_file(&f[..f.len() - 1]), None);
    }

    #[test]
    fn toy_signatures_verify() {
        let (vk, s1) = toy_sign(5, &[1u8; 32]);
        assert!(sig_ok(&vk, &[1u8; 32], &s1));
        assert!(!sig_ok(&vk, &[2u8; 32], &s1));
        let (vk2, s2) = toy_sign(5, &trace_digest(&[]));
        assert_eq!(vk, vk2);
        assert!(sig_ok(&vk, &trace_digest(&[]), &s2));
        let mut bad = s2.clone();
        bad.idx = 1;
        assert!(!sig_ok(&vk, &trace_digest(&[]), &bad));
    }

    #[test]
    fn digits_checksum() {
        let d = wots_digits(&[0u8; 32]);
        assert_eq!(d.len(), 133);
        // all-zero digits: checksum 384 = 0b01_10_00_00_00 → base-4 digits 0,0,0,2,1
        assert_eq!(&d[128..], &[0, 0, 0, 2, 1]);
        let d = wots_digits(&[0xFF; 32]);
        assert_eq!(&d[128..], &[0, 0, 0, 0, 0]);
    }
}
