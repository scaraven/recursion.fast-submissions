//! `r3v` (WP R3, dev): a thin wrapper. The §6.2–§6.4 verifiers live in refv (`refv::full`, `refv::tree`,
//! `refv::sponge`, `refv::typed`, `refv::minibus`; moved there by R1 on 2026-11-23: one verifier, not two).

pub use refv::full::{FULL_CLAIMS, FULL_QS, FullStubs, MB_SEED, verify_full_file};
