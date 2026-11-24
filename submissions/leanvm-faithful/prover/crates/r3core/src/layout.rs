//! The stack layout (BLUEPRINT v3 §2.2; FORMAT6 v2.4 §6.3, §6.5, §T). Stack index `x = r + 2^ROW_LOG·slot`,
//! `r < 2^19`, `slot < 64`; slots `≥ LANES` are never committed (zero). A *block* of `2^μ` words at block offset
//! `off` is the aligned range `[off·2^μ, (off+1)·2^μ)`; FORMAT6 §6.5's placement weight of a claim on it is
//! `eq(bits(off), x[μ..25])·W(x[..μ])`.
//!
//! Constants marked STUB are not frozen by FORMAT6 (§T: CD fixes `STREAM`, `X`, the mini-bus columns and the
//! windows); they are `Shape` constants that change no count, and both the prover and the R3 dev verifier read
//! them from here.

/// `M`.
pub const STACK_LOG: usize = 25;
/// Rows of the stack (`2^19`); one slot = one row-block of `2^ROW_LOG` words.
pub const ROW_LOG: usize = 19;
pub const ROWS: usize = 1 << ROW_LOG;
/// Committed slots (lanes).
pub const LANES: usize = 46;

/// Stack index of word `r` of slot `slot`.
#[inline]
pub const fn idx(slot: usize, r: usize) -> usize {
    r + (slot << ROW_LOG)
}

// ---- tree batch (R2, `keccak_gkr::tree`): slots 0–7 raw words, 8–32 middle state.
pub const SLOT_TREE_IN: usize = 0;
pub const SLOT_TREE_MID: usize = 8;

// ---- STREAM (CD-circuit.md §0, frozen): slot 33 only, stride 1: word `w` at stack index `idx(33, 0) + w`; slot 34
// is a free zero lane. The trace from word 0 (the `0x54` tag at byte 0), `σ'` at word `2^18` (597 words, `readSig`'s
// order), `σ_leaf` at `2^18 + 597` (also `readSig`'s order). `C_rec`'s window = slot 33 (`⟨19, 33·2^19⟩`);
// `C_main`'s window = the whole stack (`⟨25, 0⟩`).
pub const SLOT_STREAM: usize = 33;
pub const STREAM_WORDS: usize = ROWS;
pub const STREAM_SIG: usize = 1 << 18;
pub const STREAM_SIG_LEAF: usize = STREAM_SIG + 597;
#[inline]
pub const fn stream_idx(w: usize) -> usize {
    idx(SLOT_STREAM, 0) + w
}

// ---- SP (slot 35): the sponge batch, `2^13` rows × 64 slots, word `row + 2^13·spslot`; slots 0–24 inputs,
// 25–49 middle state (leanVM's numbering), 50–63 zero. One block of `2^19` words at block offset 35.
pub const SLOT_SP: usize = 35;
pub const SP_LOG: usize = 13;
pub const SP_ROWS: usize = 1 << SP_LOG;
pub const SP_MU: usize = ROW_LOG;
pub const SP_OFF: usize = SLOT_SP;
#[inline]
pub const fn sp_idx(row: usize, spslot: usize) -> usize {
    idx(SLOT_SP, 0) + row + (spslot << SP_LOG)
}

// ---- Y (slot 36, words 0 … 25·2^13 − 1): output lane `l` of sponge row `x` at word `x + 2^13·l`; lane `l` is the
// block of `2^13` words at block offset `36·64 + l`.
pub const SLOT_Y: usize = 36;
pub const Y_MU: usize = SP_LOG;
#[inline]
pub const fn y_off(lane: usize) -> usize {
    SLOT_Y * 64 + lane
}
#[inline]
pub const fn y_idx(row: usize, lane: usize) -> usize {
    idx(SLOT_Y, 0) + row + (lane << SP_LOG)
}

// ---- the sponge link (FORMAT6 §6.3 L1–L3; `ksLinkProgE2 13 xl rows`).
pub const XL: usize = 10;
/// `split = 2^13 − 2^xl`: rows below take their message from `STREAM` (`M(x, l)` = `STREAM` word `17x + l`), rows
/// from it from `X`.
pub const SPLIT: usize = SP_ROWS - (1 << XL);
pub const MSG_LANES: usize = 17;
#[inline]
pub const fn m_idx(x: usize, lane: usize) -> usize {
    stream_idx(MSG_LANES * x + lane)
}
/// STUB (CD places `X` in `T`): `X(i, l)` (sponge row `split + i`, `i < 2^xl`, lane `l < 17`) is word `i` of the
/// block of `2^xl` words at block offset `X_OFF0 + l`, i.e. slot 37 words `l·2^10 + i`.
pub const X_OFF0: usize = idx(SLOT_T, 0) >> XL;
#[inline]
pub const fn x_idx(i: usize, lane: usize) -> usize {
    ((X_OFF0 + lane) << XL) + i
}
/// STUB: the words of `T` reserved for `X` (slot 37 words `0 … 17·2^10 − 1`); the typed backend lays `T` out
/// around them.
pub const X_WORDS: usize = MSG_LANES << XL;

// ---- mini-bus columns: STUB, slot 36 words `2^18 … 2^19 − 1` (above `Y`'s `25·2^13 = 204,800` words).
pub const MB_LO: usize = idx(SLOT_Y, 1 << 18);
pub const MB_HI: usize = idx(SLOT_Y + 1, 0);

// ---- T (slots 37–45): typed result memory (≤ 9·2^19 words), except `X`'s words above.
pub const SLOT_T: usize = 37;
pub const T_SLOTS: usize = 9;
