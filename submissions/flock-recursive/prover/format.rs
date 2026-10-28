//! The signed-proof file (`harness/FORMAT.md`), the trace digest and the WOTS/Merkle signature
//! check `SigOk` (`Contract/Signature.lean`), from `submissions/spartan-srom/prover/format.rs`.

use crate::blake2s::{Blake2s, Digest};
use crate::oracle::Trace;

pub const TAG_TRACE: u8 = 0x54;
pub const TAG_WOTS: u8 = 0x57;
pub const TAG_WOTS_LEAF: u8 = 0x4B;
pub const TAG_SIG_NODE: u8 = 0x4D;
pub const WOTS_LEN: usize = 133;
pub const SIG_HEIGHT: usize = 16;
/// `queryCap` (`Contract/Relation.lean`). There is no `proofCap` since core PR #20: `acc` only
/// requires `|π| < 2^64` (`FRVerifier.accWith`, `decide (p.π.size < 2 ^ 64)`).
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

/// `sigWords σ` as bytes.
pub fn put_sig(v: &mut Vec<u8>, s: &Sig) {
    v.extend_from_slice(&s.idx.to_le_bytes());
    for d in s.ots.iter().chain(s.path.iter()) {
        v.extend_from_slice(d);
    }
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

