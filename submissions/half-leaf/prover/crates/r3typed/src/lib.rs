//! lvm6 WP R3 (not leanVM; `PATCHES.md`): FORMAT6 v2.4 §6.4a, the typed phases at `E` (zerocheck, wiring,
//! relayout) and the accumulator fold A23, prover side (the verifier side is refv's `typed`, R1). The
//! mini-bus (§6.4b) is `r3mb`'s.
//!
//! - [`circuit`]: the circuit `Q` (matrices, regions, `Φ_Q`, the blob format), the one in use ([`circuit::circuit`],
//!   swappable), [`circuit::phi_q`];
//! - [`stub`]: STUB, a synthetic `Q` with the frozen dimensions until CD's generator exists;
//! - [`witness`]: the words `z` and the typed result memory `T` written into the stack;
//! - [`prove`]: rows 1–12 on the v6 transcript, stack claims 46–49 and `accOut`;
//! - `EXPORT.md`: the format of CD's generator output that [`circuit::Circuit::from_blob`] reads.
//!
//! Lean (normative arithmetic): `Lvm6.Ty.typedProgE` (`lvm6-wip/lean/Lvm6TyProg.lean`).

pub mod circuit;
pub mod prove;
pub mod qbin;
pub mod stub;
pub mod witness;

pub use circuit::{Circuit, circuit, phi_q};
pub use prove::{Acc, Tamper, TypedOut, acc_out_from_proof, prove_typed};
pub use witness::{TypedWitness, WitnessError, pub_lanes, witness};
