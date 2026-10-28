//! Every protocol constant of the P1 prover and the native verifier, in one place (blueprint
//! `docs/v4/flock-recursive/BLUEPRINT.md` §1–§2, with the P1 choices of
//! `docs/v4/flock-recursive/stages/P1-RESULT.md` §4 where the blueprint leaves a detail open).
//! A change of the protocol is a change of this file (and of the phase code that reads it).
//!
//! Revision 3.13: the constants are A.1's (S-A), the layouts A.2–A.4's (S-0): the proof's eighteen
//! fields (`FIELD_SIZES`, `piSize = 797,904`), the item counts of the phase table (`Z1_SQ` …), the
//! `m* = 32` ladder that sizes the item sequence (`STAR_*`). The old P1 notes below that say
//! "PLACEHOLDER" record where a value came from before S-A fixed it (the values did not change).

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

// ---------------------------------------------------------------- the proof layout (rev. 3.7 A.3, A.4)

/// `m* = 32`: the item sequence and `π`'s fields are sized for the larger kind (A.4); a smaller
/// `m` (the `P30` leaf, and the native test shapes `m = 25 … 29`) fills the difference with dummies.
pub const M_STAR: usize = 32;

/// A.3's fields, in order (`FRTranscriptDefs.fHdr … fSibs`).
pub const F_HDR: usize = 0;
pub const F_STMT: usize = 1;
pub const F_Z2: usize = 2;
pub const F_Z3: usize = 3;
pub const F_ZEND: usize = 4;
pub const F_L2: usize = 5;
pub const F_S2: usize = 6;
pub const F_LR: usize = 7;
pub const F_LREND: usize = 8;
/// Rev. 3.13: E's fields precede RS0's (E before RS; A.3 "fields 9, 9′ precede field 8").
pub const F_E: usize = 9;
pub const F_EEND: usize = 10;
pub const F_RS0: usize = 11;
pub const F_P1: usize = 12;
pub const F_PF: usize = 13;
pub const F_CAPS: usize = 14;
pub const F_FINAL: usize = 15;
pub const F_COLS: usize = 16;
pub const F_SIBS: usize = 17;
pub const N_FIELDS: usize = 18;
/// A.3's sizes (`FRFormat.fieldSizes_eq`; `logs/S-0/dump/summary.txt`).
pub const FIELD_SIZES: [usize; N_FIELDS] =
    [48, 128, 2048, 1248, 32, 800, 1344, 816, 48, 2336, 48, 8192, 2112, 672, 45056, 4096, 487504, 241664];
/// `piSize = 798,192` (revision 4.1, `FRShape4.piSizeOf_seq4`; `logs/S-F4/dump/summary.txt`): 3.x's
/// 797,904 plus Lr's 2 and E's 4 extra rounds (96 + 192 B, the `m = 32` node's phases), the same for
/// every SNARK kind.
pub const PI_SIZE: usize = 798192;

/// The offset of field `f` in `π`.
pub const fn field_off(f: usize) -> usize {
    let mut s = 0;
    let mut i = 0;
    while i < f {
        s += FIELD_SIZES[i];
        i += 1;
    }
    s
}

/// Squeeze and round counts of the item sequence (A.4, `FRTranscriptDefs.piopPhases`).
pub const Z1_SQ: usize = 10;
pub const Z3_ROUNDS: usize = 26;
pub const L2_ROUNDS: usize = 14;
/// The `v_kind` entries of L3 (rev. 3.8.2: 8, 128 bytes; a leaf's `v` is entry 0, the rest zero).
pub const L3_KINDS: usize = 8;
pub const S1_SQ: usize = 15;
pub const S2_ROUNDS: usize = 28;
/// S1's coordinate layout (S-0 deviation 7): `τ` = 0…17, `θ` = 18…27, `κ_s` = 28.
pub const S1_THETA: usize = 18;
pub const THETA_LEN: usize = 10;
pub const S1_KAPPA: usize = 28;
/// Revision 4.1 (`seq4`): Lr 17 rounds (Lr1 9 squeezes), E2 23 (E1 12), E4 25; 3.x had 15 (8), 21 (11),
/// 23. A segment sends them all as zero dummies.
pub const LR1_SQ: usize = 9;
pub const LR_ROUNDS: usize = 17;
/// `J_z = 4` (rev. 3.8: Z's quirky claim, Lc's, Sh's one claim, Lr's; a leaf's fourth is zero).
pub const RS_CLAIMS: usize = 4;
pub const RS1_SQ: usize = 4;
pub const E1_SQ: usize = 12;
pub const E2_ROUNDS: usize = 23;
/// E4: the E lincheck (rev. 3.12/3.13), 25 degree-2 rounds at `seq4`; E4 end absorbs `f̂(r′) ‖ 0^16`.
pub const E4_ROUNDS: usize = 25;
pub const E4END_LEN: usize = 32;
/// Column items are padded to a multiple of 64 B in the stream (rev. 3.12): 48 zero bytes after the
/// column's F elements (query 8 + 16·rows + 48).
pub const COL_PAD: usize = 48;
pub const PF_ROUNDS: usize = 7;
/// P3: `κ_c` from 5 squeezes, the first 9 coordinates (rev. 3.8: `eq(κ_c, bits₉(j))`).
pub const P3_SQ: usize = 5;
pub const KAPPA_C: usize = 9;
/// The final message: `2^7` K elements (`P30`: `2^5` then zeros).
pub const FINAL_ELEMS: usize = 1 << PF_ROUNDS;
/// The `m* = 32` ladder's position squeezes and Merkle-node queries per position (`lvlStar`).
pub const STAR_SQ: [usize; LEVELS] = [25, 13, 10, 8, 6];
pub const STAR_SIB: [usize; LEVELS] = [11, 10, 8, 6, 5];
/// Rows per column (`2^ℓ`), the same for every kind.
pub const STAR_ROWS: [usize; LEVELS] = [64, 16, 16, 16, 16];

/// The kind byte of a leaf of `m` committed bits: `L32` (`'L'`) for `m = 32`, `L31` (`0x4B`, S-0′'s
/// draft `FRShape4.SegKind.byte`) for `m = 31`, `'P'` otherwise (the 3.x `P30` leaf; `m = 25 … 29`
/// are native test shapes with the `P30` byte).
pub fn leaf_kind_byte(m: usize) -> u8 {
    match m {
        M_STAR => KIND_LEAF,
        31 => KIND_L31,
        _ => KIND_P30,
    }
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
pub const KIND_L31: u8 = 0x4B;
/// `L30` (`FRShape4.SegKind.byte`; 3.x's `P30` byte).
pub const KIND_P30: u8 = 0x50;
/// The item count of `seq4` (`itemsOf_seq4_length`) and its Fiat–Shamir items.
pub const N_ITEMS: usize = 8905;
pub const N_FS_ITEMS: usize = 482;
pub const KIND_NODE: u8 = 0x4E;
pub const HDR_LEN: usize = 48;

/// `qV4 = 36,000` (`FRShape4.qV4`; the aggregate verifier asks `≤ 4 × 8,905`).
pub const QV: usize = 36000;

/// The leaf shapes: `m ∈ {30, 32}` (B-1); test shapes `m ≥ 25` use the same code.
pub fn leaf_n(m: usize) -> u64 {
    1u64 << (m - BLOCK_LOG)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A.3's sizes from the counts of A.4 (`sizes.py`): rounds × 48 or 96, the caps, the final
    /// message, the columns and the siblings of the `m* = 32` ladder.
    #[test]
    fn layout_matches_a3() {
        assert_eq!(FIELD_SIZES.iter().sum::<usize>(), PI_SIZE);
        assert_eq!(field_off(N_FIELDS - 1) + FIELD_SIZES[N_FIELDS - 1], PI_SIZE);
        let l = ladder(M_STAR);
        let want = [
            (F_Z2, 2048),
            (F_Z3, Z3_ROUNDS * 48),
            (F_ZEND, 32),
            (F_L2, L2_ROUNDS * 48 + L3_KINDS * 16),
            (F_S2, S2_ROUNDS * 48),
            (F_LR, LR_ROUNDS * 48),
            (F_LREND, 48),
            (F_RS0, RS_CLAIMS * 128 * 16),
            (F_E, (E2_ROUNDS + E4_ROUNDS) * 48 + E4END_LEN),
            (F_EEND, 48),
            (F_P1, ROW_LOG.iter().sum::<usize>() * 96),
            (F_PF, PF_ROUNDS * 96),
            (F_CAPS, CAP_LOG.iter().map(|c| 32 << c).sum()),
            (F_FINAL, FINAL_ELEMS * 32),
            (F_COLS, (0..LEVELS).map(|i| l[i].queries * (STAR_ROWS[i] * 16 + COL_PAD)).sum()),
            (F_SIBS, (0..LEVELS).map(|i| l[i].queries * STAR_SIB[i] * 32).sum()),
        ];
        for (f, n) in want {
            assert_eq!(FIELD_SIZES[f], n, "field {f}");
        }
        for i in 0..LEVELS {
            assert_eq!(STAR_SIB[i], l[i].code_log - l[i].cap_log);
            assert_eq!(STAR_SQ[i], l[i].queries.div_ceil(256 / l[i].code_log));
            assert_eq!(STAR_ROWS[i], 1 << l[i].rows_log);
        }
        assert_eq!(final_log(M_STAR), PF_ROUNDS);
    }

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
