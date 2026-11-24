//! The random oracle the prover hashes with (`fs6::oracle`, where it moved in R0 so that leanVM's crates reach it):
//! every Fiat–Shamir step and every Merkle hash is a query `q ↦ Keccak-256(k ‖ q)`, answered by the service
//! (`service.rs`, the service run) or computed in-process from `/work/oracle.key` (`Local`, the timed passes).
//! Both give the same bytes, so the prover's output does not depend on which one is installed.

pub use crate::keccak::Digest;
pub use fs6::Trace;
pub use fs6::oracle::{Builder, Local, Oracle, get, install, report};

/// One counted query to the installed oracle.
pub fn ask(q: &[u8]) -> Digest {
    fs6::oracle::ask(get(), q)
}

/// `out[i] = H(item_i)` for the fixed-size items of `data` (`len` bytes each), over the oracle's connections
/// (`fs6::oracle::batch`; the split changes no byte). `_chunk` is kept for the P1/R0 callers.
pub fn hash_par(data: &[u8], len: usize, out: &mut [Digest], _chunk: usize) {
    assert_eq!(data.len(), len * out.len());
    fs6::oracle::batch(get(), out, &|i, b: &mut Vec<u8>| b.extend_from_slice(&data[i * len..][..len]));
}
