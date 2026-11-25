//! FORMAT6 §2: `HDR`, its native checks, and the statement check made before any query.
//!
//! Written from the table, not from `fs6::schedule::parse_header` (an independent reading; the KATs compare them).

use crate::keccak::{leaf_stmt, node_stmt};
use crate::shape::Shape;
use crate::{Digest, E, Reject, Res, e_of, require};

/// `53 6C 76 6D 36 00 00 01`.
pub const MAGIC: [u8; 8] = *b"Slvm6\0\0\x01";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hdr {
    pub b: u64,
    pub n: u64,
    pub h: Digest,
    pub c_prev: Digest,
    /// `vk` (v2.2: in `HDR`, so the seed `a₀ ‖ c ‖ HDR` binds it).
    pub vk: Digest,
    /// `accIn`: `pt ∈ E^v`, then `y`.
    pub acc_pt: Vec<E>,
    pub acc_y: E,
}

/// `parseHdr` and the native checks of §2's table, in table order. Returns the header, its bytes and `BODY`.
pub fn parse<'a>(sh: &Shape, pi: &'a [u8]) -> Res<(Hdr, &'a [u8], &'a [u8])> {
    let len = sh.hdr_len();
    require(pi.len() >= len, Reject::HdrLen)?;
    require(pi[..8] == MAGIC, Reject::Magic)?;
    let u = |o: usize| u64::from_le_bytes(pi[o..o + 8].try_into().unwrap());
    let (b, n) = (u(8), u(16));
    require(b <= 1, Reject::HdrB)?;
    require(n == 1u64 << sh.log_blocks, Reject::HdrN)?;
    let h: Digest = pi[24..56].try_into().unwrap();
    let c_prev: Digest = pi[56..88].try_into().unwrap();
    require(b == 1 || c_prev == [0; 32], Reject::HdrCPrime)?;
    let vk: Digest = pi[88..120].try_into().unwrap();
    let e = |k: usize| e_of(fs6::codec::get_e(&pi[120 + 16 * k..]));
    let acc_pt: Vec<E> = (0..sh.phi_vars).map(e).collect();
    let acc_y = e(sh.phi_vars);
    // `accIn` has no native check of its own (FORMAT6 v2 §2: the accumulator check is on `accOut`, §T); the seed
    // absorbs it, and its honest value at `b = 0` is §2.1's `(0^v, Φ_Q(0^v))`.
    Ok((Hdr { b, n, h, c_prev, vk, acc_pt, acc_y }, &pi[..len], &pi[len..]))
}

/// `HDR.vk` equals `V_S`'s `vk` argument (v2.2).
pub fn vk_ok(vk: &Digest, x: &Hdr) -> Res<()> {
    require(x.vk == *vk, Reject::HdrVk)
}

/// The statement check: `L = leafStmtF h n`; `b = 0`: `c = L`; `b = 1`: `c = nodeStmtF c' L`.
pub fn statement_ok(c: &Digest, x: &Hdr) -> Res<()> {
    let l = leaf_stmt(&x.h, x.n);
    let want = if x.b == 0 { l } else { node_stmt(&x.c_prev, &l) };
    require(*c == want, Reject::Statement)
}
