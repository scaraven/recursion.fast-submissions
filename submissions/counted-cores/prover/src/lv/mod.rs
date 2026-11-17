//! leanVM's prover crates (leanVM 0b850750), vendored as modules by `tools/vendor.py`; every edit
//! after vendoring is listed in `PATCHES.md`.
#![allow(dead_code, unused_imports, unused_variables, clippy::all)]

pub mod fiat_shamir;
// PORT-13: the v4 tier (AVX-512 + GFNI + VBMI + VPCLMULQDQ, the evaluation machine) runs leanvm-gkr-fast's (#13)
// re-vendor of gattaca-com/leanVM `pr/all`'s GKR (`keccak_gkr_v4/`), storing every round as in #15.
// lvm2 W32-P (K = 32, lead: v4p must run W32's Skip at SKIP = 2): every tier now mounts `keccak_gkr_v4/` (its
// non-GFNI forms: PCLMULQDQ Skip core, digit-bucket Product, `fold_groups` rows); leanVM 0b850750's tree
// (`keccak_gkr/`, K = 16 SKIP = 4 there) is no longer mounted: its shared files (`front.rs`, `e2bench.rs`,
// `reference.rs`) are mounted from the v4 tree by path. Same proofs, byte for byte (e2check, identall).
#[path = "keccak_gkr_v4/mod.rs"]
pub mod keccak_gkr;
pub mod leanvm_core;
// lvm2 W32 G0 (prototype, prover-only, no proof path): K = 32 RMFE-pack Skip/Product kernels and their bench.
pub mod w32;
pub mod parallel;
pub mod pcs;
pub mod primitives;
pub mod tracing;
