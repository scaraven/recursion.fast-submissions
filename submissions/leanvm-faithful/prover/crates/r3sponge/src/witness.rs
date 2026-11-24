//! The sponge batch's witness (FORMAT6 v2.4 §6.3, §6.5; Lean `LvmSpongeTableLink`: `in_i[l] = cont_i·Y_{i−1}[l] +
//! [l < 17]·Msg_l[i]`).
//!
//! [`SpongeWitness::generate`] reads the messages off the stack (`M(x, l)` = `STREAM` word `17x + l` for
//! `x < split`, `X(i, l)` at `layout::x_idx` for the rows from `split`), runs the `2^13` rows in order (row `x`
//! continues row `x − 1` iff `x ∈ rows`) and writes the committed `SP` block (leanVM's `Witness::generate` at
//! `κ = 13`, depth 12: slot `s` of row `r` at word `r + 2^13·s` of the block, which is exactly `layout::sp_idx`) and
//! the 25 output lanes `Y` (`layout::y_idx`). Every other committed cell is left as it is.

use keccak_gkr::{Shape, Witness};
use primitives::field::F64;
use primitives::hash::STATE_LANES;
use r3core::layout::{
    MSG_LANES, SLOT_SP, SP_LOG, SP_MU, SP_ROWS, SPLIT, STACK_LOG, XL, idx, m_idx, x_idx, y_idx,
};

/// Rounds between two committed states (leanVM's depth at the VM: two segments, the middle state committed).
pub const DEPTH: usize = 12;

/// FORMAT6 v2.5.1 §6.3 "Sponge row map" (normative `Shape` constants): the trace digest takes rows `0 … B−1`,
/// `B = ⌊L/136⌋ + 1 = 4,002` at `P18` (`L = hashedLen6 = 544,152`); the two key leaves start at `K₁ = split + 399`
/// (`σ′`'s walk) and `K₂ = split + 864` (`σ_leaf`'s walk).
pub const TRACE_ROWS: usize = 4002;
pub const KEY_LEAVES: [usize; 2] = [SPLIT + 399, SPLIT + 864];
/// Rows a key leaf continues over: `[K + 1, K + 32)`.
pub const KEY_LEAF_ROWS: usize = 31;

/// `contRows` (FORMAT6 v2.5.1 §6.3): `[1, B) ∪ [K₁+1, K₁+32) ∪ [K₂+1, K₂+32)` = `[1, 4002) ∪ [7568, 7599) ∪
/// [8033, 8064)`, sorted, `0 ∉ rows`.
pub fn cont_rows() -> Vec<usize> {
    let mut rows: Vec<usize> = (1..TRACE_ROWS).collect();
    for k in KEY_LEAVES {
        rows.extend(k + 1..k + 1 + KEY_LEAF_ROWS);
    }
    rows
}

/// The name of [`cont_rows`] before FORMAT6 v2.5.1 froze it (it was a STUB then); the same set.
pub fn cont_rows_stub() -> Vec<usize> {
    cont_rows()
}

/// The smallest aligned block `[off·2^μ, (off+1)·2^μ)` holding the stack indices `lo .. hi`: `(off, μ)`.
pub fn region_block(lo: usize, hi: usize) -> (usize, usize) {
    assert!(lo < hi && hi <= 1 << STACK_LOG);
    let mu = (0..=STACK_LOG).find(|&mu| lo >> mu == (hi - 1) >> mu).expect("inside the stack");
    (lo >> mu, mu)
}

/// The `SP` block of the stack (`2^19` words at block offset 35).
pub fn sp_block(stack: &[F64]) -> &[F64] {
    &stack[idx(SLOT_SP, 0)..][..1 << SP_MU]
}

/// `Msg(x, l)` off the stack: `M(x, l)` below `split`, `X(x − split, l)` from it (`l < 17`).
#[inline]
pub fn msg_word(stack: &[F64], x: usize, l: usize) -> u64 {
    if x < SPLIT { stack[m_idx(x, l)].0 } else { stack[x_idx(x - SPLIT, l)].0 }
}

/// Dev: write `M` (`STREAM` words `17x + l`, `x < split`) and `X` (`x_idx(i, l)`, `i < 2^xl`) into the stack.
pub fn write_messages(stack: &mut [F64], m: impl Fn(usize, usize) -> u64, x: impl Fn(usize, usize) -> u64) {
    for row in 0..SPLIT {
        for l in 0..MSG_LANES {
            stack[m_idx(row, l)] = F64(m(row, l));
        }
    }
    for i in 0..1 << XL {
        for l in 0..MSG_LANES {
            stack[x_idx(i, l)] = F64(x(i, l));
        }
    }
}

/// The sponge rows' witness: the continuation rows and leanVM's Keccak witness of the `SP` block.
pub struct SpongeWitness {
    /// `contRows`, sorted.
    pub rows: Vec<usize>,
    /// `cont[x] = [x ∈ rows]`, `x < 2^13`.
    pub cont: Vec<bool>,
    /// leanVM's witness of the `2^13` permutations (depth 12).
    pub keccak: Witness,
}

impl SpongeWitness {
    /// The batch's [`Shape`]: `2^13` permutations, depth 12 (`slots = 50`, a block of `2^19` words).
    pub fn shape() -> Shape {
        Shape::new(SP_ROWS, DEPTH)
    }

    /// Run the rows on the messages the stack holds and write `SP` and `Y` into it (the whole `2^25`-word stack).
    pub fn generate(stack: &mut [F64], rows: &[usize]) -> Self {
        assert_eq!(stack.len(), 1 << STACK_LOG, "the whole stack");
        assert!(rows.windows(2).all(|w| w[0] < w[1]), "contRows sorted, no repeats");
        assert!(rows.iter().all(|&x| (1..SP_ROWS).contains(&x)), "contRows in [1, 2^13)");
        let mut cont = vec![false; SP_ROWS];
        rows.iter().for_each(|&x| cont[x] = true);
        // The rows in order (2^13 permutations, serial: row x may continue row x − 1).
        let mut inputs = vec![[0u64; STATE_LANES]; SP_ROWS];
        let mut outputs = vec![[0u64; STATE_LANES]; SP_ROWS];
        for x in 0..SP_ROWS {
            let mut s = if cont[x] { outputs[x - 1] } else { [0; STATE_LANES] };
            for (l, w) in s.iter_mut().enumerate().take(MSG_LANES) {
                *w ^= msg_word(stack, x, l);
            }
            inputs[x] = s;
            primitives::hash::keccak_f(&mut s);
            outputs[x] = s;
        }
        let shape = Self::shape();
        assert_eq!((shape.n_log(), shape.stack_log()), (SP_LOG, SP_MU));
        let block = &mut stack[idx(SLOT_SP, 0)..][..1 << SP_MU];
        let keccak = Witness::generate(shape, &inputs, block);
        for (x, out) in outputs.iter().enumerate() {
            for (l, &w) in out.iter().enumerate() {
                stack[y_idx(x, l)] = F64(w);
            }
        }
        Self { rows: rows.to_vec(), cont, keccak }
    }
}
