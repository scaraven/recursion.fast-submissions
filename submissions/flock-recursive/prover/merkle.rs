//! Merkle trees through the oracle (blueprint §2.2, A.2): a leaf is the answer to the column query
//! `"FRMCOL" ‖ i ‖ 0 ‖ column` (`rowsᵢ` F elements, row 0 first), a node the answer to
//! `"FRMNOD" ‖ i ‖ 0 ‖ left ‖ right`; the cap is the layer at depth `depth − cap`, in index order.

use crate::blake2s::Digest;
use crate::field::F;
use crate::oracle::Oracle;
use crate::params::{TAG_MCOL, TAG_MNOD};

pub struct Tree {
    pub level: u8,
    /// `layers[d]` has `n >> d` digests, `d ≤ depth − cap`.
    pub layers: Vec<Vec<Digest>>,
}

pub fn col_query(level: u8, col: &[F], out: &mut Vec<u8>) {
    out.extend_from_slice(TAG_MCOL);
    out.push(level);
    out.push(0);
    for x in col {
        out.extend_from_slice(&x.to_bytes());
    }
    // rev. 3.12: the column item is padded to a multiple of 64 bytes in the stream
    out.extend_from_slice(&[0u8; crate::params::COL_PAD]);
}

pub fn node_query(level: u8, l: &Digest, r: &Digest, out: &mut Vec<u8>) {
    out.extend_from_slice(TAG_MNOD);
    out.push(level);
    out.push(0);
    out.extend_from_slice(l);
    out.extend_from_slice(r);
}

impl Tree {
    /// Commit the interleaved codeword `cw` (`rows` F elements per position).
    pub fn commit(o: &dyn Oracle, level: u8, cw: &[F], rows: usize, cap_log: usize) -> Tree {
        let n = cw.len() / rows;
        let depth = n.trailing_zeros() as usize;
        let sp = crate::prof::span(if level == 0 { "merkle0.leaves" } else { "merkle.leaves" });
        let mut leaves = vec![[0u8; 32]; n];
        o.ask_many(&mut leaves, &|p, buf: &mut Vec<u8>| col_query(level, &cw[p * rows..(p + 1) * rows], buf));
        drop(sp);
        let _sp = crate::prof::span(if level == 0 { "merkle0.nodes" } else { "merkle.nodes" });
        let mut layers = vec![leaves];
        for _ in 0..depth - cap_log {
            let prev = layers.last().unwrap();
            let mut next = vec![[0u8; 32]; prev.len() / 2];
            o.ask_many(&mut next, &|i, buf: &mut Vec<u8>| node_query(level, &prev[2 * i], &prev[2 * i + 1], buf));
            layers.push(next);
        }
        Tree { level, layers }
    }
    pub fn cap(&self) -> &[Digest] {
        self.layers.last().unwrap()
    }
    /// The siblings of position `p`, leaf level first.
    pub fn path(&self, p: usize) -> Vec<Digest> {
        let mut v = Vec::with_capacity(self.layers.len() - 1);
        for d in 0..self.layers.len() - 1 {
            v.push(self.layers[d][(p >> d) ^ 1]);
        }
        v
    }
}
