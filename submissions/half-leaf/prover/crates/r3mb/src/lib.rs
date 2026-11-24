//! lvm6 WP R3 (not leanVM; `PATCHES.md`): FORMAT6 v2.4 §6.4b, the mini-bus at `E = GF(2^128)`, prover side (and,
//! with feature `verify`, the dev verifier side on refv's types).
//!
//! The protocol is season 1's mini-bus re-instantiated at `E` (`docs/lvm6/design/MB-decision.md`; Lean
//! `Lvm6.Mb.miniBusLProg6`): one fingerprint group `G(16), D(4)` (`α₀ … α₃, β`, weights `w = eq(α, ·)`), the roots
//! `shared, count`, the batched push/pull/count grand-product GKR in two-level steps (leanVM's walk with PARAM's
//! grinds), the check `count ≠ 0`, and three linear claims on the stack (§6.4's claims 50–52).
//!
//! - [`gkr`], [`leaf`]: leanVM `fdb317982` `crates/experimental_prover/lean_vm_core/src/{gkr.rs, leaf.rs}`, copied
//!   verbatim into `src/lv/` and patched (every edit marked `lvm6`, listed in `PATCHES.md` as MB-1 … MB-4). They are
//!   mounted at the crate root so that their `crate::` paths resolve unchanged (the items below stand in for
//!   leanVM's `lib.rs`).
//! - [`m3`]: season 1's `lvm/m3.rs` (`TableW`, `prove_bus`, `prove_lin`, `place`) ported from F192 to F128.
//! - [`tables`]: the table description (Lean's `Tab`: reads with count columns, seeds with finalize columns), the
//!   swappable interface: CD's/TY's real tables replace [`stub`]'s.
//! - [`typed_mb`]: season 1's `lvm/typed_mb.rs` ported: seed arrays and read tables with the honest counts.
//! - [`stub`]: the stub tables (until CD's generator exists).
//! - [`prove`]: [`prove::MbWitness`], [`prove::prove_minibus`].
//! - `verify` (feature `verify`): §6.4b on refv's `VChain`, the claims recomputed from the tables as the Lean does.

#[path = "lv/gkr.rs"]
pub mod gkr;
#[path = "lv/leaf.rs"]
#[allow(dead_code)] // `BusForm::{eval, linear}` served the dev verifier, now refv's `minibus`
pub mod leaf;

pub mod export;
pub mod m3;
pub mod prove;
pub mod stub;
pub mod tables;
pub mod typed_mb;

pub use prove::{MbOut, MbWitness, prove_minibus};
pub use tables::{MbCol, MbKey, MbTab};

/// The shared transcript (leanVM `lean_vm_core/src/transcript.rs`, verbatim): the v6 chain behind `ProverState::v6`.
pub mod transcript {
    pub use primitives::transcript::ProverState;
}

/// leanVM `lean_vm_core/src/lib.rs`: below this many parallelizable items a pass runs serially.
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// leanVM `lean_vm_core/src/lib.rs`: one named prover stage, run inside its `tracing` span.
macro_rules! stage {
    ($name:literal, $f:expr) => {
        tracing::info_span!($name).in_scope($f)
    };
}
pub(crate) use stage;

pub(crate) use primitives::log2_ceil_usize;

/// leanVM `lean_vm_core/src/cpu/mod.rs:368` `to_scalar`, for the vendored `gkr.rs` tests only.
#[cfg(test)]
pub(crate) mod cpu {
    use primitives::field::F128;
    pub fn to_scalar(value: &F128) -> verifier::E {
        verifier::E::new(value.c0, value.c1)
    }
}

/// Lean `Lvm6.Mb.miniDepth`: the walk's depth, `2^12` leaves (FORMAT6 §6.4b: 6 two-level steps).
pub const MINI_DEPTH: usize = 12;

/// PARAM's grinds of §6.4b (Lean `gAB`, `gLam`, `gRd`, `gY`, `gYl`), as the vendored prover uses them.
pub const G_AB: u32 = leaf::FINGERPRINT_GRIND;
pub const G_LAM: u32 = gkr::LAMBDA_GRIND;
pub const G_RD: u32 = gkr::ROUND_GRIND;
pub const G_Y: u32 = 2;
pub const G_Y_LAST: u32 = 3;

/// The stack block every mini-bus column lies in (`r3core::layout`'s STUB region `MB_LO..MB_HI`): `2^MB_MU` words
/// at block offset `MB_OFF`; the claims' weights are supported on it.
pub const MB_MU: usize = 18;
pub const MB_OFF: usize = r3core::layout::MB_LO >> MB_MU;
const _: () = assert!(MB_OFF << MB_MU == r3core::layout::MB_LO);
const _: () = assert!((MB_OFF + 1) << MB_MU == r3core::layout::MB_HI);
