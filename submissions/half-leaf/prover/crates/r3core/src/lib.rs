//! lvm6 WP R3 (not leanVM; `PATCHES.md`): what the R3 parts share.
//!
//! - [`layout`]: where every block sits in the one stacked commitment `q : cube(25) → K` (FORMAT6 §2.2 of
//!   BLUEPRINT v3, FORMAT6 v2.4 §6.5, §T), index `r + 2^19·slot`.
//! - [`claim`]: [`claim::PClaim`], a stack claim on the prover side (value + weight), as each phase hands it to
//!   §6.5's batch, with a native check against the stack (the dev oracle in place of the PCS).
//! - `open6` (WP R3 step 3): §6.5 and §6.6 on the v6 transcript.

pub mod claim;
pub mod layout;
pub mod open6;
