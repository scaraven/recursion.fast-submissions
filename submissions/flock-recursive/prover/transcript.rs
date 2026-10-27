//! Fiat–Shamir through the oracle (blueprint §1.2, **PLACEHOLDER layouts**, BP-E-M1/M8): `seed`,
//! `absorb`, `squeeze` queries, and the proof byte stream `π` that the prover writes and the
//! verifier reads in the same order. Prover messages that the verifier absorbs go through
//! `send`/`recv`; columns and Merkle siblings (read, not absorbed: they enter Merkle queries) go
//! through `put`/`take`.

use crate::blake2s::Digest;
use crate::field::{F, K};
use crate::oracle::Oracle;
use crate::params::{TAG_ABS, TAG_SEED, TAG_SQZ};

pub struct Fs<'a> {
    pub o: &'a dyn Oracle,
    pub st: Digest,
    /// pending F challenges of the last squeeze (the second 16 bytes)
    spare: Option<F>,
    buf: Vec<u8>,
}

impl<'a> Fs<'a> {
    pub fn seed(o: &'a dyn Oracle, vk: &Digest, c: &Digest, hdr: &[u8]) -> Fs<'a> {
        let mut q = Vec::with_capacity(8 + 64 + hdr.len());
        q.extend_from_slice(TAG_SEED);
        q.extend_from_slice(vk);
        q.extend_from_slice(c);
        q.extend_from_slice(hdr);
        let st = o.ask(&q);
        Fs { o, st, spare: None, buf: q }
    }
    /// `st ← H("FRABS000" ‖ st ‖ msg)`, `msg` zero-padded to a multiple of 16 bytes.
    pub fn absorb(&mut self, msg: &[u8]) {
        self.buf.clear();
        self.buf.extend_from_slice(TAG_ABS);
        self.buf.extend_from_slice(&self.st);
        self.buf.extend_from_slice(msg);
        let pad = (16 - msg.len() % 16) % 16;
        self.buf.resize(self.buf.len() + pad, 0);
        self.st = self.o.ask(&self.buf);
        self.spare = None;
    }
    /// `st ← H("FRSQZ000" ‖ st)`; the answer is the challenge material.
    pub fn squeeze(&mut self) -> Digest {
        self.buf.clear();
        self.buf.extend_from_slice(TAG_SQZ);
        self.buf.extend_from_slice(&self.st);
        self.st = self.o.ask(&self.buf);
        self.spare = None;
        self.st
    }
    /// One F challenge alone (bytes 0…15 of a fresh squeeze).
    pub fn chal_f(&mut self) -> F {
        let a = self.squeeze();
        F::from_bytes(&a[..16])
    }
    /// `n` F challenges, two per squeeze (bytes 0…15, 16…31).
    pub fn chal_fs(&mut self, n: usize) -> Vec<F> {
        let mut v = Vec::with_capacity(n);
        while v.len() < n {
            if let Some(x) = self.spare.take() {
                v.push(x);
                continue;
            }
            let a = self.squeeze();
            v.push(F::from_bytes(&a[..16]));
            self.spare = Some(F::from_bytes(&a[16..32]));
        }
        self.spare = None;
        v
    }
    pub fn chal_k(&mut self) -> K {
        let a = self.squeeze();
        K::from_bytes(&a)
    }
    /// `t` positions of `bits` bits, `⌊256/bits⌋` per squeeze, little-endian bit fields.
    pub fn positions(&mut self, t: usize, bits: usize) -> Vec<u64> {
        let per = 256 / bits;
        let mut v = Vec::with_capacity(t);
        while v.len() < t {
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

/// The prover's side: `π` written in reading order.
pub struct Writer<'a> {
    pub fs: Fs<'a>,
    pub pi: Vec<u8>,
}
impl<'a> Writer<'a> {
    pub fn send(&mut self, b: &[u8]) {
        self.pi.extend_from_slice(b);
        self.fs.absorb(b);
    }
    pub fn send_f(&mut self, v: &[F]) {
        self.send(&f_bytes(v));
    }
    pub fn send_k(&mut self, v: &[K]) {
        self.send(&k_bytes(v));
    }
    pub fn put(&mut self, b: &[u8]) {
        self.pi.extend_from_slice(b);
    }
}

/// The verifier's side: `π` read in the same order; every read past the end fails.
pub struct Reader<'a, 'b> {
    pub fs: Fs<'a>,
    pub pi: &'b [u8],
    pub off: usize,
}
impl<'a, 'b> Reader<'a, 'b> {
    pub fn take(&mut self, n: usize) -> Option<&'b [u8]> {
        if self.pi.len() - self.off < n {
            return None;
        }
        let r = &self.pi[self.off..self.off + n];
        self.off += n;
        Some(r)
    }
    pub fn recv(&mut self, n: usize) -> Option<&'b [u8]> {
        let r = self.take(n)?;
        self.fs.absorb(r);
        Some(r)
    }
    pub fn recv_f(&mut self, n: usize) -> Option<Vec<F>> {
        let r = self.recv(16 * n)?;
        Some(r.chunks_exact(16).map(F::from_bytes).collect())
    }
    pub fn recv_k(&mut self, n: usize) -> Option<Vec<K>> {
        let r = self.recv(32 * n)?;
        Some(r.chunks_exact(32).map(K::from_bytes).collect())
    }
}
