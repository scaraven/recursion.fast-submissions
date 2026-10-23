//! The Fiat–Shamir transcript (BLUEPRINT-R1 §6) and the Merkle tree (§5.3), both over an oracle
//! `H` (`oracle.rs`). The query bytes are v3's (blueprint §1.1): seed `0x10 ‖ s ‖ enc64 n ‖ h`,
//! absorb `0x20 ‖ st ‖ kind ‖ msg`, squeeze `0x30 ‖ st`, Merkle leaf `0x00 ‖ column`, node
//! `0x01 ‖ λₗ ‖ λᵣ`. Under v3's oracle they are hashed after the prefix `0x52`; under v4 they go to
//! the service as they are. Every transcript state can be logged (`dump-transcript`).

use crate::blake2s::Digest;
use crate::field::{ch_e, E};
use crate::oracle::Oracle;

pub type Label = [u8; 31];

pub fn trunc(d: &Digest) -> Label {
    d[..31].try_into().unwrap()
}

pub struct Transcript<'a> {
    pub st: Digest,
    /// `(operation, kind, state after)` when logging
    pub log: Option<Vec<(String, Digest)>>,
    pub queries: usize,
    o: &'a dyn Oracle,
    buf: Vec<u8>,
}

impl<'a> Transcript<'a> {
    /// `st ← H(0x10 ‖ s ‖ enc64 n ‖ h)`.
    pub fn new(o: &'a dyn Oracle, s: &Digest, n: u64, h: &Digest, logging: bool) -> Transcript<'a> {
        let mut buf = Vec::with_capacity(1 << 12);
        buf.push(0x10);
        buf.extend_from_slice(s);
        buf.extend_from_slice(&n.to_le_bytes());
        buf.extend_from_slice(h);
        let st = o.ask(&buf);
        let mut t = Transcript { st, log: if logging { Some(vec![]) } else { None }, queries: 1, o, buf };
        t.note("seed".into());
        t
    }
    fn note(&mut self, what: String) {
        let st = self.st;
        if let Some(l) = self.log.as_mut() {
            l.push((what, st));
        }
    }
    /// `absorb(st, kind, msg) := H(0x20 ‖ st ‖ kind ‖ msg)`.
    pub fn absorb(&mut self, kind: u8, msg: &[u8]) {
        self.buf.clear();
        self.buf.push(0x20);
        self.buf.extend_from_slice(&self.st);
        self.buf.push(kind);
        self.buf.extend_from_slice(msg);
        self.st = self.o.ask(&self.buf);
        self.queries += 1;
        if self.log.is_some() {
            self.note(format!("absorb {:02x} {}", kind, msg.len()));
        }
    }
    /// `squeeze(st) := H(0x30 ‖ st)`; the answer is the new state and the challenge source.
    pub fn squeeze(&mut self) -> Digest {
        self.buf.clear();
        self.buf.push(0x30);
        self.buf.extend_from_slice(&self.st);
        self.st = self.o.ask(&self.buf);
        self.queries += 1;
        if self.log.is_some() {
            self.note("squeeze".into());
        }
        self.st
    }
    pub fn squeeze_e(&mut self) -> E {
        let a = self.squeeze();
        ch_e(&a)
    }
    /// `t` column indices in `[0, 2^ln)` from `⌈t/cnt⌉` answers (§6.1).
    pub fn squeeze_indices(&mut self, t: usize, ln: usize) -> Vec<usize> {
        let cnt = 256 / ln;
        let mut out = Vec::with_capacity(t);
        while out.len() < t {
            let a = self.squeeze();
            for i in 0..cnt {
                if out.len() == t {
                    break;
                }
                let mut v = 0usize;
                for b in 0..ln {
                    let bit = i * ln + b;
                    v |= (((a[bit / 8] >> (bit % 8)) & 1) as usize) << b;
                }
                out.push(v);
            }
        }
        out
    }
}

/// `λ(c) = [H(0x00 ‖ column bytes)]_31`.
pub fn leaf_label(o: &dyn Oracle, col: &[u8]) -> Label {
    let mut q = Vec::with_capacity(1 + col.len());
    q.push(0x00);
    q.extend_from_slice(col);
    trunc(&o.ask(&q))
}

/// `λ(v) = [H(0x01 ‖ λ(left) ‖ λ(right))]_31`.
pub fn node_label(o: &dyn Oracle, l: &Label, r: &Label) -> Label {
    let mut q = [0u8; 63];
    q[0] = 0x01;
    q[1..32].copy_from_slice(l);
    q[32..].copy_from_slice(r);
    trunc(&o.ask(&q))
}

/// A Merkle tree over `2^ln` labels: `levels[0]` the leaves, `levels[ln]` the root.
pub struct Merkle {
    pub levels: Vec<Vec<Label>>,
}

impl Merkle {
    /// The tree over `leaves`, one batch of node queries per level.
    pub fn build(o: &dyn Oracle, leaves: Vec<Label>) -> Merkle {
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let mut ans = vec![[0u8; 32]; prev.len() / 2];
            o.ask_many(&mut ans, &|i, b: &mut Vec<u8>| {
                b.push(0x01);
                b.extend_from_slice(&prev[2 * i]);
                b.extend_from_slice(&prev[2 * i + 1]);
            });
            levels.push(ans.iter().map(trunc).collect());
        }
        Merkle { levels }
    }
    pub fn root(&self) -> Label {
        self.levels.last().unwrap()[0]
    }
    /// The `ℓ_N` sibling labels of leaf `c`, bottom-up.
    pub fn path(&self, c: usize) -> Vec<Label> {
        let mut out = vec![];
        let mut i = c;
        for l in 0..self.levels.len() - 1 {
            out.push(self.levels[l][i ^ 1]);
            i >>= 1;
        }
        out
    }
}

/// Recompute the root from a column's bytes and its path (`V`'s climb, §5.3).
pub fn climb(o: &dyn Oracle, c: usize, col: &[u8], path: &[Label]) -> Label {
    let mut cur = leaf_label(o, col);
    for (l, sib) in path.iter().enumerate() {
        cur = if (c >> l) & 1 == 0 { node_label(o, &cur, sib) } else { node_label(o, sib, &cur) };
    }
    cur
}
