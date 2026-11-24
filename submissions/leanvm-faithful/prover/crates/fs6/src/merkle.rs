//! FORMAT6 §5: Merkle commitments over the oracle, with caps and no root.
//!
//! - leaf digest `O(leaf bytes)` (368 B at level 0, 256 B at levels 1–4);
//! - node at height `t ≥ 1`, index `j`: `O(node_{t−1,2j} ‖ node_{t−1,2j+1})` (64 B);
//! - the cap: the `2^lv` nodes at height `ht − lv`, in index order (sent in `BODY` and absorbed, never hashed);
//! - the opening of `p` in `BODY`: leaf bytes, then `ht − lv` siblings, lowest first; V asks the leaf query, then for
//!   `t = 0 … ht−lv−1` `d ‖ s` if bit `t` of `p` is 0, else `s ‖ d`, and compares with cap entry `p >> (ht − lv)`;
//! - no deduplication: every opening asks all `1 + ht − lv` queries, in the order the positions were drawn;
//! - positions: a draw `N = c₀ + 2^64·c₁` gives `(N >> (j·ht)) mod 2^ht`, `j < ⌊128/ht⌋`; the level's `t` positions
//!   are the first `t` of its draws.
//!
//! Built by whole levels through [`oracle::batch`] (batches of 4,096 queries over the connections); every answer
//! is a function of its query, so the tree is the same for any batching or thread count.

use crate::codec::E;
use crate::oracle::{self, Oracle};
use crate::{Digest, Trace};

/// A tree from its leaves up to its cap: `levels[t]` holds the `2^(ht−t)` nodes of height `t`, `t ≤ ht − lv`.
pub struct Tree6 {
    pub ht: u32,
    pub lv: u32,
    levels: Vec<Vec<Digest>>,
}

impl Tree6 {
    /// Hash the `2^ht` leaves `leaf(p, buf)` writes, then the levels up to the cap.
    pub fn build(o: &dyn Oracle, ht: u32, lv: u32, leaf: &(dyn Fn(usize, &mut Vec<u8>) + Sync)) -> Self {
        let mut level0 = vec![[0u8; 32]; 1usize << ht];
        oracle::batch(o, &mut level0, leaf);
        Self::from_leaf_digests(o, ht, lv, level0)
    }

    /// The levels above given leaf digests.
    pub fn from_leaf_digests(o: &dyn Oracle, ht: u32, lv: u32, level0: Vec<Digest>) -> Self {
        assert!(lv <= ht && level0.len() == 1usize << ht, "2^ht leaves, a cap of at most 2^ht nodes");
        let mut levels = vec![level0];
        for _ in 0..ht - lv {
            let prev = levels.last().unwrap();
            let mut next = vec![[0u8; 32]; prev.len() / 2];
            oracle::batch(o, &mut next, &|j, b: &mut Vec<u8>| {
                b.extend_from_slice(&prev[2 * j]);
                b.extend_from_slice(&prev[2 * j + 1]);
            });
            levels.push(next);
        }
        Self { ht, lv, levels }
    }

    pub fn cap(&self) -> &[Digest] {
        self.levels.last().unwrap()
    }

    pub fn leaf_digest(&self, p: usize) -> Digest {
        self.levels[0][p]
    }

    /// The `ht − lv` siblings of `p`, lowest first.
    pub fn siblings(&self, p: usize) -> Vec<Digest> {
        (0..(self.ht - self.lv) as usize).map(|t| self.levels[t][(p >> t) ^ 1]).collect()
    }

    /// V's queries for the opening of `p` and their answers, from the stored nodes (no oracle call).
    pub fn opening_trace(&self, p: usize, leaf: &[u8], tr: &mut Trace) {
        tr.push((leaf.to_vec(), self.levels[0][p]));
        for t in 0..(self.ht - self.lv) as usize {
            let (d, s) = (self.levels[t][p >> t], self.levels[t][(p >> t) ^ 1]);
            tr.push((node_query(&d, &s, (p >> t) & 1 == 1).to_vec(), self.levels[t + 1][p >> (t + 1)]));
        }
    }
}

/// The node query at a path step: `d ‖ s` if the bit is 0, `s ‖ d` if it is 1.
pub fn node_query(d: &Digest, s: &Digest, bit: bool) -> [u8; 64] {
    let mut q = [0u8; 64];
    let (l, r) = if bit { (s, d) } else { (d, s) };
    q[..32].copy_from_slice(l);
    q[32..].copy_from_slice(r);
    q
}

/// V's side of an opening, asking the oracle (for callers that hold only the leaf and the siblings, e.g. leanVM's
/// `MerklePath`s): the queries in V's order with their answers, and the cap entry index `p >> (ht − lv)`. The last
/// answer is what V compares with that cap entry.
pub fn opening_trace_asked(o: &dyn Oracle, p: usize, leaf: &[u8], siblings: &[Digest], tr: &mut Trace) -> usize {
    let mut d = oracle::ask(o, leaf);
    tr.push((leaf.to_vec(), d));
    for (t, s) in siblings.iter().enumerate() {
        let q = node_query(&d, s, (p >> t) & 1 == 1);
        d = oracle::ask(o, &q);
        tr.push((q.to_vec(), d));
    }
    p >> siblings.len()
}

/// The positions of a level: the first `t` of `(N >> (j·ht)) mod 2^ht`, `j < ⌊128/ht⌋`, over the draws in order.
pub fn positions(draws: &[E], ht: u32, t: usize) -> Vec<usize> {
    let per = 128 / ht as usize;
    assert!(draws.len() * per >= t, "enough draws for the positions");
    let mask = (1u128 << ht) - 1;
    draws
        .iter()
        .flat_map(|&[c0, c1]| {
            let n = c0 as u128 | (c1 as u128) << 64;
            (0..per).map(move |j| ((n >> (j * ht as usize)) & mask) as usize)
        })
        .take(t)
        .collect()
}
