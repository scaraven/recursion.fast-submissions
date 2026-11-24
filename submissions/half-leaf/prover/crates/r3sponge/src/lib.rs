//! lvm6 WP R3 (not leanVM; `PATCHES.md`): FORMAT6 v2.4 §6.3, the sponge batch, prover side (and, with feature
//! `verify`, the dev verifier side on refv's types).
//!
//! The batch is `2^13` Keccak-f rows `x` (`κ_s = 13`). Row `x` absorbs `in(x)[l] = [x ∈ rows]·Y(x−1)[l] +
//! [l < 17]·Msg(x, l)` and outputs `Y(x) = keccak_f(in(x))`; `Msg(x, l)` is `M(x, l)` (`STREAM` word `17x + l`) below
//! `split = 2^13 − 2^xl` and `X(x − split, l)` from it (`r3core::layout`). Committed: the `SP` block (slot 35, leanVM's
//! layout: inputs at slots 0–24, the state after 12 rounds at 25–49) and `Y` (slot 36, lane `l` of row `x` at word
//! `x + 2^13·l`).
//!
//! The schedule (FORMAT6 §6.3): caller C1 (13 × `G(1)` → `r`), C2 (`E(25)` → `v`, `Ỹ_l(r) = v_l`); the core, which
//! is leanVM's `Witness::prove` unchanged at `κ_s = 13` (the item list of §6.2 rows 6–10 with 10 eq-mode rounds a
//! layer, 10 input-opening rounds, no top-bit round, no constants); the link L1 (18 × `G(1)` → `ρ`, `λ`), L2 (13
//! plain `R(2, 2)` from claim 0), L3 (`E(4)` → `Y, in, M, X` at `ρ'`). It leaves stack claims 15, 16, 17–45 of §6.5.
//!
//! - [`witness`]: [`SpongeWitness`] (reads `M`, `X` off the stack, writes `SP` and `Y`), [`cont_rows`].
//! - [`prove`]: [`prove_sponge`], [`SpongeOut`].
//! - `verify` (feature `verify`, dev only): `verify::verify` on refv's `VChain`, `SpongeV::deferred`.

pub mod prove;
pub mod witness;

pub use prove::{SpongeOut, Tamper, prove_sponge, prove_sponge_with};
pub use witness::{SpongeWitness, cont_rows, cont_rows_stub, region_block, write_messages};

