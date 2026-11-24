//! `fs6`: the byte-level protocol of `docs/lvm6/design/FORMAT6.md` (normative), prover side.
//!
//! - [`codec`]: §1 (lanes, `K` words, `E` scalars, `χ`, the PoW lane).
//! - [`oracle`]: the random oracle `O(q) = Keccak-256(k ‖ q)`, answered by the service or computed locally from
//!   `oracle.key` (the bytes never depend on which), batched over connections.
//! - [`transcript`]: §3–§4, the hash chain: `q₀`, seed, absorb, ground groups `G(g)` with the least nonce, further
//!   draws `D(k)`, the length rule, and the trace recorder (V's exact query sequence, for `SIGN`).
//! - [`merkle`]: §5, leaf/node queries, caps, openings, positions, V's opening queries.
//! - [`params`]: `params6.json` frozen as constants (no `f64` anywhere), the `Shape`s `P18` and `P17`, and the build's [`params::SHAPE`].
//! - [`schedule`]: §6's item lists and their counts (`qS`, `|BODY|`, nonces, the length rule `fsLenOK`).
//!
//! Determinism (§9): every answer is a function of its query; batches and searches return the same bytes for any
//! split, connection count or thread count; the nonce is the least passing one.

pub mod codec;
pub mod merkle;
pub mod oracle;
pub mod params;
pub mod schedule;
pub mod transcript;

/// A 32-byte digest (an oracle answer).
pub type Digest = [u8; 32];

/// Queries and their answers, in order.
pub type Trace = Vec<(Vec<u8>, Digest)>;

pub use codec::E;
pub use merkle::Tree6;
pub use oracle::Oracle;
pub use transcript::Transcript;

#[cfg(test)]
mod kat;

// ------------------------------------------------------------------ the v6 switch of leanVM's crates

static V6: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Put leanVM's crates in v6 mode (`pcs`'s Merkle trees through the oracle with caps, frozen WHIR parameters).
/// Off by default: leanVM's own flows (the `smoke` mode, with its native verifier) are then byte-identical to
/// leanVM's. Set once, before any commitment.
pub fn set_v6(on: bool) {
    V6.store(on, std::sync::atomic::Ordering::Relaxed);
}

pub fn v6() -> bool {
    V6.load(std::sync::atomic::Ordering::Relaxed)
}

/// The cap of a tree of `2^ht` leaves: `sh`'s level with that height, else `min(ht, 5)` (dev shapes). R9: the shape
/// is an argument (it read `P18`'s levels, so `P17`'s heights 20 and 19 took caps 6 and 5: P17-freeze §5).
pub fn log_cap_for_height(sh: &params::Shape, ht: u32) -> u32 {
    sh.level_of_height(ht).map_or(ht.min(5), |i| sh.levels[i].lv)
}
