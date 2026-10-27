//! Every protocol constant of the P1 prover and the native verifier, in one place (blueprint
//! `docs/v4/flock-recursive/BLUEPRINT.md` §1–§2, with the P1 choices of
//! `docs/v4/flock-recursive/stages/P1-RESULT.md` §4 where the blueprint leaves a detail open).
//! A change of the protocol is a change of this file (and of the phase code that reads it).
//!
//! **PLACEHOLDERS.** The blueprint's engineering review (BP-E-M8) found that β, α, the domain
//! basis, the GF(2^8) embedding and skip sets, ρ₁…ρ₇, the column order, `piSize` and the
//! transcript/query layouts are not yet normative; a fix pass (stage S-0, "interfaces" appendix)
//! and S-A ("Normative constants") will fix them. Every value below marked `PLACEHOLDER` is a P1
//! choice for measurement only: throughput does not depend on it, and the byte formats it implies
//! are not final.

/// Bits per BLAKE2s block (`m₀`).
pub const BLOCK_LOG: usize = 14;
/// Skip variables (`k_s`): the 64-point univariate skip over the low 6 bit-index variables.
pub const SKIP: usize = 6;
/// Packed variables: one F element carries 128 = 2^7 witness bits.
pub const PACK: usize = 7;
/// Pinned zerocheck coordinates (variables x₆ … x₁₂): 3 in GF(2^8), 4 in F.
pub const PINNED: usize = 7;

// ---------------------------------------------------------------- the fields (B-4)

/// PLACEHOLDER (S-A fixes it). `F = BF64[y]/(y² + y + β)`, here `β = x^63` (absolute trace 1:
/// `Tr(x^k) = 1` for `k ∈ {61, 63}` only among the monomials; every element of degree < 61 has
/// trace 0). BF64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1) (CompPoly's `BF64`). The field code is
/// generic in `BETA` (one more carry-less product than a dedicated shift would cost).
pub const BETA: u64 = 1u64 << 63;
/// PLACEHOLDER (S-A fixes it). `K = F[u]/(u² + u + α)`, here `α = β·y` (trace 1:
/// `Tr_F(c₀ + c₁y) = Tr_BF64(c₁)`), as `(c₀, c₁)`.
pub const ALPHA: (u64, u64) = (0, 1u64 << 63);

// ---------------------------------------------------------------- the block layout (Appendix A.6)

/// Blueprint rev. 2 A.6: `h_in` 0…255, `h_out` 256…511, the message 512…1023 in natural byte order
/// (chain block: `0x43 ‖ d ‖ 0^31`, so `d` sits at 520…775), `t_lo` 1024…1055, `t_hi` 1056…1087,
/// `f0` 1088…1119, `f1` 1120…1151, `one` 1152, the 14,720 gates from 1280.
pub const OUT_BASE: usize = 256;
pub const MSG_BASE: usize = 512;
pub const D_BASE: usize = 520;
pub const TLO_BASE: usize = 1024;
pub const THI_BASE: usize = 1056;
pub const F0_BASE: usize = 1088;
pub const F1_BASE: usize = 1120;
pub const ONE_POS: usize = 1152;
pub const GATE_BASE: usize = 1280;
pub const GATES: usize = 14720;

// ---------------------------------------------------------------- Ligerito (B-3)

/// Blueprint rev. 2 §2.2: five levels, rates 1/2 … 1/32.
pub const LEVELS: usize = 5;
/// log₂ of the inverse rate per level.
pub const LOG_INV_RATE: [usize; LEVELS] = [1, 2, 3, 4, 5];
/// Row variables folded per level: 6, then 4 (= 1 coordinate-split bit + 3 message variables).
pub const ROW_LOG: [usize; LEVELS] = [6, 4, 4, 4, 4];
/// Merkle cap depth per level (clamped to the tree depth for test shapes).
pub const CAP_LOG: [usize; LEVELS] = [9, 8, 8, 8, 7];
/// Consistency batching coordinates (eq over ⌈log₂(t + 1)⌉ = 9 bits).
pub const KAPPA_C: usize = 9;

/// Queries per level (rev. 2 §2.2: `t = ⌈120.25 / −log₂(1 − e/n)⌉`, `e = ⌊(n − k)/2⌋`).
pub fn queries(_m: usize) -> [usize; LEVELS] {
    [290, 178, 145, 132, 126]
}

pub fn queries_formula(log_inv_rate: usize, log_n: usize) -> usize {
    let n = 1u64 << log_n;
    let k = n >> log_inv_rate;
    let e = (n - k) / 2;
    (120.25 / -(1.0 - e as f64 / n as f64).log2()).ceil() as usize
}

/// The per-level shape for `m` committed bits: `(rows_log, msg_log, code_log)` of level `i`
/// (level 0 message = the packed polynomial, `m − 7` variables).
#[derive(Clone, Copy, Debug)]
pub struct Level {
    pub rows_log: usize,
    pub msg_log: usize,
    pub code_log: usize,
    pub cap_log: usize,
    pub queries: usize,
}

pub fn ladder(m: usize) -> [Level; LEVELS] {
    let q = queries(m);
    let mut vars = m - PACK; // variables of level 0
    let mut out = [Level { rows_log: 0, msg_log: 0, code_log: 0, cap_log: 0, queries: 0 }; LEVELS];
    for i in 0..LEVELS {
        let rows_log = ROW_LOG[i];
        let msg_log = vars - rows_log;
        let code_log = msg_log + LOG_INV_RATE[i];
        out[i] = Level { rows_log, msg_log, code_log, cap_log: CAP_LOG[i].min(code_log), queries: q[i] };
        vars = msg_log + 1; // the folded K-word as F coordinates: one split variable more
    }
    out
}

/// Variables of the final (clear) K-message: `msg_log` of the last level.
pub fn final_log(m: usize) -> usize {
    ladder(m)[LEVELS - 1].msg_log
}

// ---------------------------------------------------------------- transcript (§1.2; PLACEHOLDER layouts)

/// A.2: the seed tag is 7 bytes (BP-E-M1: every field of the hashed trace stream is 16-aligned).
pub const TAG_SEED: &[u8; 7] = b"FRSEED0";
pub const TAG_ABS: &[u8; 8] = b"FRABS000";
pub const TAG_SQZ: &[u8; 8] = b"FRSQZ000";
/// `"FRMNOD" ‖ level ‖ 0` and `"FRMCOL" ‖ level ‖ 0`.
pub const TAG_MNOD: &[u8; 6] = b"FRMNOD";
pub const TAG_MCOL: &[u8; 6] = b"FRMCOL";

pub const KIND_LEAF: u8 = 0x4C;
pub const KIND_NODE: u8 = 0x4E;
pub const HDR_LEN: usize = 48;
pub const HDR2_LEN: usize = 48;

/// `qV` (rev. 2 A.1).
pub const QV: usize = 10240;

/// The leaf shapes: `m ∈ {30, 32}` (B-1); test shapes `m ≥ 25` use the same code.
pub fn leaf_n(m: usize) -> u64 {
    1u64 << (m - BLOCK_LOG)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ladder_matches_blueprint() {
        let l = ladder(30);
        assert_eq!(l.map(|x| x.msg_log), [17, 14, 11, 8, 5]);
        assert_eq!(l.map(|x| x.code_log), [18, 16, 14, 12, 10]);
        assert_eq!(final_log(30), 5); // P1: the level-4 fold, 2^5 K elements (rev. 2 A.3 lists k₅ = 4)
        let l = ladder(32);
        assert_eq!(l.map(|x| x.code_log), [20, 18, 16, 14, 12]);
        assert_eq!(final_log(32), 7);
        for m in [30usize, 32] {
            let l = ladder(m);
            for i in 0..LEVELS {
                assert_eq!(queries_formula(LOG_INV_RATE[i], l[i].code_log), l[i].queries, "m {m} level {i}");
            }
        }
    }
}
