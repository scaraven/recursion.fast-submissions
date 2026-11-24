//! FORMAT6 §5: positions, and V's side of an opening against a cap (no root, no deduplication).

use crate::chain::VChain;
use crate::shape::Level;
use crate::{Digest, E, Reject, Res, fs_e, require};

/// The level's positions: `G(g_q)`, `D(d − 1)`, each draw `N = c₀ + 2^64·c₁` giving `(N >> (j·ht)) mod 2^ht` for
/// `j < ⌊128/ht⌋`, the first `t` kept (`fs6::merkle::positions`).
pub fn positions(ch: &mut VChain, l: &Level) -> Res<Vec<usize>> {
    let draws: Vec<fs6::E> = ch.group(l.grind_query, l.position_draws())?.into_iter().map(fs_e).collect();
    Ok(fs6::merkle::positions(&draws, l.ht, l.queries))
}

/// The opening of position `p` (`BODY`: the leaf bytes, then `ht − lv` siblings, lowest first): V asks the leaf
/// query, then `d ‖ s` or `s ‖ d` by bit `t` of `p`, and compares the last answer with cap entry `p >> (ht − lv)`.
/// Returns the leaf bytes.
pub fn open<'a>(ch: &mut VChain<'a>, level: usize, l: &Level, cap: &[Digest], p: usize) -> Res<&'a [u8]> {
    let leaf = ch.read_plain(l.leaf_bytes)?;
    let mut d = ch.ask_plain(leaf)?;
    for t in 0..l.path() {
        let s: Digest = ch.read_plain(32)?.try_into().unwrap();
        d = ch.ask_plain(&fs6::merkle::node_query(&d, &s, (p >> t) & 1 == 1))?;
    }
    require(d == cap[p >> l.path()], Reject::MerkleCap(level))?;
    Ok(leaf)
}

/// A level-0 leaf (slot 45 first, slot 0 last) as the fold's lanes: lane `s` = slot `s`, then zero lanes up to 64
/// (season 1's `padRow` reversed, as `L:whir.rs:262` reverses level 0's leaf image).
pub fn lanes0(leaf: &[u8], lanes: usize) -> Vec<E> {
    let w: Vec<u64> = leaf.chunks_exact(8).map(fs6::codec::le64).collect();
    assert_eq!(w.len(), lanes);
    (0..64).map(|s| if s < lanes { E::new(w[lanes - 1 - s], 0) } else { E::new(0, 0) }).collect()
}

/// A level-`i ≥ 1` leaf: lane `u` = the `E` value at bytes `16u` (`L:whir.rs:85`, `ext_row`).
pub fn lanes_e(leaf: &[u8]) -> Vec<E> {
    leaf.chunks_exact(16).map(|x| crate::e_of(fs6::codec::get_e(x))).collect()
}
