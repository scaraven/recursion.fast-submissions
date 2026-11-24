//! The stack layout (BLUEPRINT v3 §2.2; FORMAT6 v2.4 §6.3, §6.5, §T; v2.6 / P17-freeze §3.3 for `P17`). Stack
//! index `x = r + 2^ROW_LOG·slot`, `r < 2^ROW_LOG`, `slot < 64`; slots `≥ LANES` are never committed (zero). A
//! *block* of `2^μ` words at block offset `off` is the aligned range `[off·2^μ, (off+1)·2^μ)`; FORMAT6 §6.5's
//! placement weight of a claim on it is `eq(bits(off), x[μ..M])·W(x[..μ])`.
//!
//! R9: the slot map is one table per shape ([`Place`]: [`P18_PLACE`], [`P17_PLACE`]), chosen by the build's shape
//! (`fs6::params::SHAPE`); the constants below are read off [`PLACE`], and the `const` asserts at the end tie every
//! block to its slot and to the shape. refv reads this module too, so its ACCEPT says nothing about placement:
//! the asserts and P17-freeze §3.3 are the check.
//!
//! | block | `P18` (slots of `2^19` words) | `P17` (slots of `2^18` words) |
//! |---|---|---|
//! | tree inputs, middle state | 0–32 | 0–32 |
//! | `STREAM` (`C_rec`) | 33, `σ'` at word `2^18` | 33, `σ'` at word `2^17` |
//! | `SP` (`2^19` words) | 35 (block offset 35) | 34–35 (block offset 17) |
//! | `Y` (`25·2^13` words) | 36, low half | 40 |
//! | mini-bus columns | 36, words `2^18 …` | 41 |
//! | `X` (`17·2^10` words) | 37 (inside `T`) | 42 |
//! | `T` (`com` targets) | 37–45 (the stub's `com`: 38–39) | 36–39 (`com`: 36–39) |
//! | zero | 34 | 43–45 |
//!
//! Constants marked STUB are not frozen by FORMAT6 (§T: CD fixes `STREAM`, `X`, the mini-bus columns and the
//! windows); they are `Shape` constants that change no count, and both the prover and the R3 dev verifier read
//! them from here.

/// One shape's slot map (stack indices; see the table above).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Place {
    /// `M` and the slot size `2^row_log` (`= 2^κ`: a slot is one row-block of the tree batch).
    pub stack_log: usize,
    pub row_log: usize,
    pub lanes: usize,
    /// `STREAM`'s slot and the word of `σ'` in it (`sB`; `σ_leaf` at `sB + 597`).
    pub slot_stream: usize,
    pub stream_sig: usize,
    /// `SP`'s first slot (a block of `2^SP_MU` words).
    pub slot_sp: usize,
    /// `Y`'s slot (words `0 … 25·2^13 − 1` of it).
    pub slot_y: usize,
    /// The mini-bus columns' region `[mb_lo, mb_hi)` (one block of `2^r3mb::MB_MU` words).
    pub mb_lo: usize,
    pub mb_hi: usize,
    /// `X`'s first word (`17·2^10` words from it).
    pub x_base: usize,
    /// `T`, the slots `com` targets may use, and the stub circuit's `com` region (`2^20` words).
    pub slot_t: usize,
    pub t_slots: usize,
    pub stub_com: usize,
}

const fn at(slot: usize, r: usize, row_log: usize) -> usize {
    r + (slot << row_log)
}

/// `P18` (BLUEPRINT v3 §2.2, CD-circuit.md §0): unchanged from r8.
pub const P18_PLACE: Place = Place {
    stack_log: 25,
    row_log: 19,
    lanes: 46,
    slot_stream: 33,
    stream_sig: 1 << 18,
    slot_sp: 35,
    slot_y: 36,
    mb_lo: at(36, 1 << 18, 19),
    mb_hi: at(37, 0, 19),
    x_base: at(37, 0, 19),
    slot_t: 37,
    t_slots: 9,
    stub_com: at(38, 0, 19),
};

/// `P17` (P17-freeze §3.3 with the coordinator's slot-42 decision for `X`; `r3mb::MB_MU = 18` kept: the mini-bus
/// columns fill slot 41 alone).
pub const P17_PLACE: Place = Place {
    stack_log: 24,
    row_log: 18,
    lanes: 46,
    slot_stream: 33,
    stream_sig: 1 << 17,
    slot_sp: 34,
    slot_y: 40,
    mb_lo: at(41, 0, 18),
    mb_hi: at(42, 0, 18),
    x_base: at(42, 0, 18),
    slot_t: 36,
    t_slots: 4,
    stub_com: at(36, 0, 18),
};

/// The build's shape and its slot map.
pub const SHAPE: fs6::params::Shape = fs6::params::SHAPE;
pub const PLACE: Place = if SHAPE.log_blocks == 17 { P17_PLACE } else { P18_PLACE };

/// `M`.
pub const STACK_LOG: usize = PLACE.stack_log;
/// Rows of the stack (`2^κ`); one slot = one row-block of `2^ROW_LOG` words.
pub const ROW_LOG: usize = PLACE.row_log;
pub const ROWS: usize = 1 << ROW_LOG;
/// Committed slots (lanes).
pub const LANES: usize = PLACE.lanes;

/// Stack index of word `r` of slot `slot`.
#[inline]
pub const fn idx(slot: usize, r: usize) -> usize {
    r + (slot << ROW_LOG)
}

// ---- tree batch (R2, `keccak_gkr::tree`): slots 0–7 raw words, 8–32 middle state.
pub const SLOT_TREE_IN: usize = 0;
pub const SLOT_TREE_MID: usize = 8;

// ---- STREAM (CD-circuit.md §0, frozen): slot 33 only, stride 1: word `w` at stack index `idx(33, 0) + w`. The
// trace from word 0 (the `0x54` tag at byte 0), `σ'` at word `STREAM_SIG` (`2^18` at `P18`, `2^17` at `P17`; 597
// words, `readSig`'s order), `σ_leaf` at `STREAM_SIG + 597` (also `readSig`'s order). `C_rec`'s window = slot 33
// (`⟨κ, 33·2^κ⟩`); `C_main`'s window = the whole stack (`⟨M, 0⟩`).
pub const SLOT_STREAM: usize = PLACE.slot_stream;
pub const STREAM_WORDS: usize = ROWS;
pub const STREAM_SIG: usize = PLACE.stream_sig;
pub const STREAM_SIG_LEAF: usize = STREAM_SIG + 597;
#[inline]
pub const fn stream_idx(w: usize) -> usize {
    idx(SLOT_STREAM, 0) + w
}

// ---- SP (`P18`: slot 35; `P17`: slots 34–35): the sponge batch, `2^13` rows × 64 slots, word `row + 2^13·spslot`;
// slots 0–24 inputs, 25–49 middle state (leanVM's numbering), 50–63 zero. One block of `2^19` words at block offset
// `SP_OFF` (35 at `P18`, 17 at `P17`).
pub const SLOT_SP: usize = PLACE.slot_sp;
pub const SP_LOG: usize = 13;
pub const SP_ROWS: usize = 1 << SP_LOG;
/// `2^13` rows × 64 slots: `μ = 19` at every shape (R9: no longer `ROW_LOG`).
pub const SP_MU: usize = SP_LOG + 6;
pub const SP_OFF: usize = idx(SLOT_SP, 0) >> SP_MU;
#[inline]
pub const fn sp_idx(row: usize, spslot: usize) -> usize {
    idx(SLOT_SP, 0) + row + (spslot << SP_LOG)
}

// ---- Y (slot `SLOT_Y`, words 0 … 25·2^13 − 1): output lane `l` of sponge row `x` at word `x + 2^13·l`; lane `l` is
// the block of `2^13` words at block offset `SLOT_Y·2^(ROW_LOG − 13) + l` (`36·64 + l` at `P18`, `40·32 + l` at
// `P17`).
pub const SLOT_Y: usize = PLACE.slot_y;
pub const Y_MU: usize = SP_LOG;
#[inline]
pub const fn y_off(lane: usize) -> usize {
    (SLOT_Y << (ROW_LOG - SP_LOG)) + lane
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
/// STUB (CD places `X`): `X(i, l)` (sponge row `split + i`, `i < 2^xl`, lane `l < 17`) is word `i` of the block of
/// `2^xl` words at block offset `X_OFF0 + l`, i.e. words `l·2^10 + i` from `PLACE.x_base` (slot 37 at `P18`, inside
/// `T`; slot 42 at `P17`).
pub const X_OFF0: usize = PLACE.x_base >> XL;
#[inline]
pub const fn x_idx(i: usize, lane: usize) -> usize {
    ((X_OFF0 + lane) << XL) + i
}
/// STUB: the words reserved for `X`; at `P18` the typed backend lays `T` out around them.
pub const X_WORDS: usize = MSG_LANES << XL;

// ---- mini-bus columns: STUB (`P18`: slot 36 words `2^18 … 2^19 − 1`, above `Y`'s `25·2^13 = 204,800` words;
// `P17`: slot 41).
pub const MB_LO: usize = PLACE.mb_lo;
pub const MB_HI: usize = PLACE.mb_hi;

// ---- T: typed result memory (`com` targets; `P18`: slots 37–45, ≤ 9·2^19 words, except `X`'s words above;
// `P17`: slots 36–39).
pub const SLOT_T: usize = PLACE.slot_t;
pub const T_SLOTS: usize = PLACE.t_slots;
/// The stub circuit's `com` region (`2^20` words: slots 38–39 at `P18`, 36–39 at `P17`).
pub const STUB_COM: usize = PLACE.stub_com;

// ------------------------------------------------------------------------------------------ the static checks

/// Blocks `[lo, hi)` in address order: each non-empty, disjoint from the next, the last inside the committed lanes.
const fn ordered(b: &[(usize, usize)]) -> bool {
    let mut i = 0;
    while i < b.len() {
        if b[i].0 >= b[i].1 || (i > 0 && b[i - 1].1 > b[i].0) {
            return false;
        }
        i += 1;
    }
    b[b.len() - 1].1 <= LANES << ROW_LOG
}

// the shape: `M = κ + 6` (a row is 64 slots of `2^κ` words), `κ = log N★ + 1`, the lanes
const _: () = assert!(STACK_LOG == SHAPE.stack_log as usize && ROW_LOG == SHAPE.kappa as usize && ROW_LOG + 6 == STACK_LOG);
const _: () = assert!(LANES == SHAPE.lanes && ROW_LOG == SHAPE.log_blocks as usize + 1);
// STREAM: one slot = `C_rec` (`relayout = κ`), the trace below `σ'`, both signatures in the slot, `σ` (2^11) aligned
const _: () = assert!(STREAM_WORDS == 1 << SHAPE.relayout && STREAM_SIG_LEAF + 597 <= STREAM_WORDS);
const _: () = assert!(STREAM_SIG % (1 << 11) == 0 && STREAM_SIG + (1 << 11) <= STREAM_WORDS);
const _: () = assert!(MSG_LANES * SPLIT <= STREAM_SIG, "the sponge's STREAM messages lie below σ'");
// the child's trace stream (`B` blocks of 136 bytes = 17 words; `write_stream` checks `B` at run time) below `σ'`
const _: () = assert!(MSG_LANES * SHAPE.trace_rows <= STREAM_SIG && SHAPE.trace_rows <= SPLIT);
// SP: an aligned block of `2^19` words on whole slots
const _: () = assert!(SP_OFF << SP_MU == idx(SLOT_SP, 0) && SP_MU >= ROW_LOG);
// Y: lane blocks of `2^13` words at `y_off`, all 25 in slot `SLOT_Y`
const _: () = assert!(y_off(0) << Y_MU == idx(SLOT_Y, 0) && y_idx(SP_ROWS - 1, 24) < idx(SLOT_Y + 1, 0));
// X: 17 lane blocks of `2^10` words from `x_base`, inside one slot
const _: () = assert!(X_OFF0 << XL == PLACE.x_base && x_idx((1 << XL) - 1, MSG_LANES - 1) + 1 == PLACE.x_base + X_WORDS);
const _: () = assert!(PLACE.x_base >> ROW_LOG == (PLACE.x_base + X_WORDS - 1) >> ROW_LOG);
// the mini-bus region: one aligned block of `2^18` words (`r3mb::MB_MU`)
const _: () = assert!(MB_HI - MB_LO == 1 << 18 && MB_LO % (1 << 18) == 0);
// T and the stub's `com` region (`2^20` words, aligned) inside it
const _: () = assert!(STUB_COM % (1 << 20) == 0 && STUB_COM >= idx(SLOT_T, 0) && STUB_COM + (1 << 20) <= idx(SLOT_T + T_SLOTS, 0));
const _: () = assert!(SLOT_T + T_SLOTS <= LANES);
// the blocks, in address order, disjoint, inside the lanes (`T` itself is left out: at `P18` it holds `X`)
const _: () = assert!(ordered(&if SHAPE.log_blocks == 17 {
    [
        (0, idx(SLOT_STREAM, 0)),
        (idx(SLOT_STREAM, 0), idx(SLOT_STREAM + 1, 0)),
        (idx(SLOT_SP, 0), idx(SLOT_SP, 0) + (1 << SP_MU)),
        (STUB_COM, STUB_COM + (1 << 20)),
        (idx(SLOT_Y, 0), y_idx(SP_ROWS - 1, 24) + 1),
        (MB_LO, MB_HI),
        (PLACE.x_base, PLACE.x_base + X_WORDS),
    ]
} else {
    [
        (0, idx(SLOT_STREAM, 0)),
        (idx(SLOT_STREAM, 0), idx(SLOT_STREAM + 1, 0)),
        (idx(SLOT_SP, 0), idx(SLOT_SP, 0) + (1 << SP_MU)),
        (idx(SLOT_Y, 0), y_idx(SP_ROWS - 1, 24) + 1),
        (MB_LO, MB_HI),
        (PLACE.x_base, PLACE.x_base + X_WORDS),
        (STUB_COM, STUB_COM + (1 << 20)),
    ]
}));
// P17-freeze §3.3's offsets, literally (`P17`): STREAM 33·2^18, `sB = 2^17`, SP 17·2^19 (selector 17 on 5 bits),
// com 9·2^20, Y 40·2^18 (lane index 40·32), counts 41·2^18, X 42·2^18 (the slot-42 decision)
const _: () = assert!(
    SHAPE.log_blocks != 17
        || (idx(SLOT_STREAM, 0) == 8_650_752
            && STREAM_SIG == 131_072
            && idx(SLOT_SP, 0) == 17 << 19
            && SP_OFF == 17
            && STACK_LOG - SP_MU == 5
            && STUB_COM == 9 << 20
            && idx(SLOT_Y, 0) == 10_485_760
            && y_off(0) == 40 * 32
            && MB_LO == 41 << 18
            && PLACE.x_base == 42 << 18)
);
// and r8's (`P18`), unchanged
const _: () = assert!(
    SHAPE.log_blocks != 18
        || (idx(SLOT_STREAM, 0) == 33 << 19
            && STREAM_SIG == 1 << 18
            && SP_OFF == 35
            && y_off(0) == 36 * 64
            && MB_LO == (36 << 19) + (1 << 18)
            && MB_HI == 37 << 19
            && X_OFF0 == (37 << 19) >> 10
            && SLOT_T == 37
            && T_SLOTS == 9
            && STUB_COM == 38 << 19)
);
