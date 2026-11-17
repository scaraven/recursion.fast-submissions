// Vendored from leanVM 0b850750 + the pr/all crate diff (04fba039b..edd857be9) `crates/keccak_gkr/src/prover.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The layer prover.
//!
//! One layer makes four passes over the bits of the states it reduces to:
//!
//! 1. the product polynomial, before its evaluation point `s` is known;
//! 2. three sumcheck rounds on bit-level products, keeping the next variable binary;
//! 3. the next round's quadratic coefficient, from differences of groups;
//! 4. one field element per half block and position, for the rounds that remain.
//!
//! From `s` on, everything stays in the power basis of `s` ([`crate::lv::keccak_gkr::power`]) until the tables
//! are down to one row.
//!
//! lvm2 E2-K: [`prove_layer`] is generic over the field of the weights and challenges ([`Ext`] of `W` words:
//! E3 = `F192` at `W = 3`, E2 = `F128` at `W = 2`); every pass compiled on the v4 tier is. The forms compiled
//! only off v4 (the digit buckets' `Weigh`, the `fold_groups` form of `Fold`) stay E3's: this tree is mounted
//! only on v4 (`lv/mod.rs`), where they are dead code or not built.

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::{Ext, F128, F128Unreduced, F192, F192Unreduced, F192x8, Prod8, Unreduced};
use crate::lv::primitives::multilinear::eq_table;
use crate::lv::primitives::stream::Stream;

use crate::lv::keccak_gkr::basis::{PolyEval, add_mul};
use crate::lv::keccak_gkr::e2x4::{E2x4, E2x4U};
use crate::lv::keccak_gkr::keccak::{BITS, LOCAL_VARS, along, linear_transpose, row_positions};
use crate::lv::keccak_gkr::kernels::{
    GROUP, GROUP_BYTES, HALF_BYTES, MIXED, PACK_VARS, PACKS, SKIP, SkipBlock, SkipWeights, TERNARY, embed, products, slot,
};
use crate::lv::keccak_gkr::power::{Element, PowerField, WideDot, factor_row, get, set};
use crate::lv::keccak_gkr::protocol::{Claim, chi_weights, mu_at, tag};
use crate::lv::keccak_gkr::rmfe::PROD_BITS;
use crate::lv::keccak_gkr::witness::transpose64;
use crate::lv::keccak_gkr::witness::{Recompute, Shape, Witness, words};

/// The pattern index of a binary assignment.
fn ternary(b: usize) -> usize {
    (0..SKIP).fold(0, |acc, k| acc + (b >> k & 1) * 3usize.pow(k as u32))
}

// lvm2 W32-P: the digit buckets of the v2/v4p tree (`keccak_gkr/prover.rs`, generic in `W`), the E3 Product pass
// of this tier (E2 runs `w32::v4::Product32`).
/// The bits of a digit a weight splits into (`8 W` digits).
const DIGIT_BITS: usize = 8;

/// The bits of a block position's products, 128 to each pack (lvm2 W32: 105 used).
pub(crate) const PAYLOAD_BITS: usize = 128 * PACKS;
/// The packs of a part of a block position, and the words of their products: with AVX-512 the
/// whole position, three registers; with AVX2 half, three registers; elsewhere a quarter, a
/// block's worth of which stays in cache.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
const PART: usize = PACKS;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
const PART: usize = PACKS / 2;
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
const PART: usize = 8;
const PART_WORDS: usize = 2 * PART;
// `add` XORs whole vectors, so `PART_WORDS` divides by each arm's lane count. A `PART` that broke it would
// drop products or store past the array rather than fail to build.
const _: () = assert!(PACKS.is_multiple_of(PART));
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
const _: () = assert!(PART_WORDS.is_multiple_of(8));
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
const _: () = assert!(PART_WORDS.is_multiple_of(4));
#[cfg(target_arch = "aarch64")]
const _: () = assert!(PART_WORDS.is_multiple_of(2));

/// The products of a part of a block position's packs, 128 bits each (105 used), grouped while every digit
/// of the weights groups the block's positions.
#[derive(Clone, Copy)]
#[cfg_attr(all(target_arch = "x86_64", target_feature = "avx512f"), repr(C, align(64)))]
#[cfg_attr(not(all(target_arch = "x86_64", target_feature = "avx512f")), repr(C, align(16)))]
struct Part([u64; PART_WORDS]);

impl Part {
    const ZERO: Self = Self([0; PART_WORDS]);

    /// Product `q` at bits `128 * q ..`: two words a product.
    #[inline(always)]
    fn pack(products: &[u128; PART]) -> Self {
        Self(std::array::from_fn(|w| (products[w / 2] >> (64 * (w % 2))) as u64))
    }

    #[inline(always)]
    fn add(&mut self, other: &Self) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        // SAFETY: both parts are three registers, aligned to 64, and AVX-512 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (
                self.0.as_mut_ptr().cast::<__m512i>(),
                other.0.as_ptr().cast::<__m512i>(),
            );
            for i in 0..PART_WORDS / 8 {
                let x = _mm512_xor_si512(
                    _mm512_load_si512(dst.add(i).cast()),
                    _mm512_load_si512(src.add(i).cast()),
                );
                _mm512_store_si512(dst.add(i).cast(), x);
            }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        // SAFETY: both parts are three registers, and AVX2 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..PART_WORDS).step_by(4) {
                let (d, s) = (dst.add(i).cast::<__m256i>(), src.add(i).cast::<__m256i>());
                _mm256_storeu_si256(d, _mm256_xor_si256(_mm256_loadu_si256(d), _mm256_loadu_si256(s)));
            }
        }
        // Left to itself, the compiler XORs the words in general registers.
        #[cfg(target_arch = "aarch64")]
        // SAFETY: both parts are six words, and aarch64 always has NEON.
        unsafe {
            use core::arch::aarch64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..PART_WORDS).step_by(2) {
                vst1q_u64(dst.add(i), veorq_u64(vld1q_u64(dst.add(i)), vld1q_u64(src.add(i))));
            }
        }
        #[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
        for (x, y) in self.0.iter_mut().zip(&other.0) {
            *x ^= y;
        }
    }
}

/// Digit `d` of a weight.
#[inline(always)]
fn digit<F: Ext<W>, const W: usize>(weight: F, d: usize) -> usize {
    let w = weight.to_limbs();
    (w[d / 8] >> (DIGIT_BITS * (d % 8))) as usize & ((1 << DIGIT_BITS) - 1)
}

/// The positions grouped by each digit of their weight: those whose digit `d` is `v` are
/// `order[d][starts[d][v]..starts[d][v + 1]]`.
struct Groups {
    order: Vec<[u16; BITS]>,
    starts: Vec<[u16; (1 << DIGIT_BITS) + 1]>,
}

impl Groups {
    fn new<F: Ext<W>, const W: usize>(weights: &[F]) -> Self {
        let digits = 64 * W / DIGIT_BITS;
        let mut order = vec![[0u16; BITS]; digits];
        let mut starts = vec![[0u16; (1 << DIGIT_BITS) + 1]; digits];
        for (d, (order, starts)) in order.iter_mut().zip(&mut starts).enumerate() {
            let digits: Vec<usize> = weights[..BITS].iter().map(|&w| digit::<F, W>(w, d)).collect();
            for &v in &digits {
                starts[v + 1] += 1;
            }
            for v in 0..1 << DIGIT_BITS {
                starts[v + 1] += starts[v];
            }
            let mut next = *starts;
            for (p, &v) in digits.iter().enumerate() {
                order[next[v] as usize] = p as u16;
                next[v] += 1;
            }
        }
        Self { order, starts }
    }

    /// `sum over positions of weight[j] (x) payloads[j]` into `rows`: row `DIGIT_BITS * d + i`
    /// sums the payloads whose weight has that bit set. Each group is summed in registers, so
    /// the payloads are only read.
    fn add_rows(&self, payloads: &[Part; BITS], rows: &mut [Part], sums: &mut [Part; 1 << DIGIT_BITS]) {
        for (rows, (order, starts)) in rows
            .as_chunks_mut::<DIGIT_BITS>()
            .0
            .iter_mut()
            .zip(self.order.iter().zip(&self.starts))
        {
            for (v, sum) in sums.iter_mut().enumerate() {
                let mut acc = Part::ZERO;
                for &p in &order[starts[v] as usize..starts[v + 1] as usize] {
                    // SAFETY: `order` holds positions.
                    acc.add(unsafe { payloads.get_unchecked(p as usize) });
                }
                *sum = acc;
            }
            // Bit `i` of the digit: the sums whose value has it, then fold it away.
            for (i, row) in rows.iter_mut().enumerate().rev() {
                let (low, high) = sums[..2 << i].split_at_mut(1 << i);
                let mut acc = Part::ZERO;
                for (low, high) in low.iter_mut().zip(&*high) {
                    acc.add(high);
                    low.add(high);
                }
                *row = acc;
            }
        }
    }
}

/// Byte `r` of an element's 24.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
pub(crate) fn byte(x: &F192, r: usize) -> u8 {
    ([x.c0, x.c1, x.c2][r / 8] >> (8 * (r % 8))) as u8
}

/// Byte `r` of an element's `8 W` (lvm2 E2-K: [`byte`] for either field).
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
fn byte_w<F: Ext<W>, const W: usize>(x: &F, r: usize) -> u8 {
    (x.to_limbs()[r / 8] >> (8 * (r % 8))) as u8
}

/// The GF2P8AFFINE matrix whose output bit `t` sums the input bits `k` with bit `t` of
/// `bytes[k]` set: that output's row is matrix byte `7 - t`, the 8 x 8 transpose reversed.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
pub(crate) fn affine_matrix(bytes: [u8; 8]) -> u64 {
    // Bit `8 r + c` moves to bit `8 c + r` (Hacker's Delight, section 7-3).
    let mut x = u64::from_le_bytes(bytes);
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^= t ^ (t << 28);
    x.swap_bytes()
}

/// lvm2 W32-P: the tables' rows of a block off the GFNI tier (v4p, v2): per row (`B / 4` packs, four bytes a pack) and
/// position, `sum over the row's packs q of embed(pack q) * fold[q]` by carry-less products (`W` partial products of
/// 117 bits), `W + 1` words, reduced. The same rows as the GFNI maps.

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
)))]
struct Fold<const B: usize, const W: usize>(Vec<Element<W>>);


#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
)))]
impl<const B: usize, const W: usize> Fold<B, W> {
    fn new<F: Ext<W>>(_: &PowerField<F, W>, fold: &[Element<W>]) -> Self {
        assert!(fold.len() == B / 4);
        Self(fold.to_vec())
    }

    fn scratch() -> Vec<u64> {
        vec![0u64; 2 * (W + 1) * BITS]
    }

    /// `row`'s value at one position: the packs `P r ..` of `e`, folded; `W + 1` words.
    #[inline(always)]
    fn fold_row(&self, e: &[u64], r: usize) -> [u64; 4] {
        let p = B / 4;
        let mut acc = [0u128; W];
        for (q, f) in self.0.iter().enumerate() {
            for (acc, &f) in acc.iter_mut().zip(f) {
                *acc ^= crate::lv::primitives::field::gf2_64::mul_wide(e[p * r + q], f);
            }
        }
        let mut out = [0u64; 4];
        for (k, &x) in acc.iter().enumerate() {
            out[k] ^= x as u64;
            out[k + 1] ^= (x >> 64) as u64;
        }
        out
    }

    /// The first `rows.len() / (W BITS)` rows.
    fn rows<F: Ext<W>>(&self, field: &PowerField<F, W>, block: &[u64], rows: &mut [u64], wide: &mut [u64]) {
        let (row, n) = (W * BITS, rows.len() / (W * BITS));
        assert!(n <= 64 / B && wide.len() >= n * (W + 1) * BITS);
        for j in 0..BITS {
            let e = embed(words(block, j));
            for r in 0..n {
                let sum = self.fold_row(&e, r);
                for (k, &word) in sum[..W + 1].iter().enumerate() {
                    wide[r * (W + 1) * BITS + k * BITS + j] = word;
                }
            }
        }
        for r in 0..n {
            field.reduce_row(&mut rows[r * row..][..row], &wide[r * (W + 1) * BITS..][..(W + 1) * BITS], BITS);
        }
    }
}

/// [`Fold`] as a GF(2)-linear map of a row's `B` bytes to its value's `8 W`: GF2P8AFFINE matrix
/// `[i][z]` lane `l` sends input byte `i` to output byte `8z + l`, eight positions at a time
/// (`B W` maps a row byte and group: 24 a pack pair at E3, 16 at E2).
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
struct Fold<const B: usize, const W: usize>([[[u64; 8]; W]; B]);

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
impl<const B: usize, const W: usize> Fold<B, W> {
    fn new<F: Ext<W>>(field: &PowerField<F, W>, fold: &[Element<W>]) -> Self {
        assert!(fold.len() == B / 4);
        Self(std::array::from_fn(|i| {
            // Bit `k` of input byte `i` is bit `8 (i % 4) + k` of pack `i / 4` (lvm2 W32: four bytes a pack).
            let values: [F; 8] = std::array::from_fn(|k| {
                let mut e = [0u64; W];
                e[0] = crate::lv::keccak_gkr::rmfe::RMFE.emb[8 * (i % 4) + k];
                F::from_limbs(field.mul(&fold[i / 4], &e))
            });
            std::array::from_fn(|z| std::array::from_fn(|l| affine_matrix(values.map(|v| byte_w(&v, 8 * z + l)))))
        }))
    }

    fn scratch() -> Vec<u64> {
        Vec::new()
    }

    fn rows<F>(&self, _: &PowerField<F, W>, block: &[u64], rows: &mut [u64], _: &mut [u64]) {
        let row = W * BITS;
        assert!(block.len() >= BITS * 8 && rows.len().is_multiple_of(row) && rows.len() <= 64 / B * row);
        // SAFETY: the features are enabled at compile time.
        unsafe { fold_gfni::<B, BITS, false, false, W>(&self.0, block, rows) }
    }
}

/// A block's 64 input qwords, aligned for whole-register stores.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
#[repr(C, align(64))]
struct Spill([u64; 64]);

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
#[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
fn fold_gfni<const B: usize, const WIDTH: usize, const DIFFERENCES: bool, const COMPACT: bool, const W: usize>(
    maps: &[[[u64; 8]; W]; B],
    block: &[u64],
    rows: &mut [u64],
) {
    use core::arch::x86_64::*;
    use crate::lv::primitives::simd::{load, store, transpose8};
    if W == 2 {
        // SAFETY: the same features.
        return unsafe {
            if rows.len() == 2 * W * WIDTH {
                fold_gfni_e2::<B, WIDTH, DIFFERENCES, COMPACT, W, 2>(maps, block, rows)
            } else {
                fold_gfni_e2::<B, WIDTH, DIFFERENCES, COMPACT, W, 1>(maps, block, rows)
            }
        };
    }
    // Byte `8b + m` of the output is byte `8m + b` of the input: an 8 x 8 byte transpose per word.
    let gather: [u8; 64] = std::array::from_fn(|o| (8 * (o % 8) + o / 8) as u8);
    let gather = load(&gather[..], 0);
    let groups = rows.len() / (W * WIDTH);
    for c in 0..WIDTH / 8 {
        // lvm2 R9-KG: input qword `i` broadcast from memory (a load) rather than a GPR broadcast
        // of its index and a qword permute (two shuffle-port operations) per affine map pair.
        let mut spilled = Spill([0u64; 64]);
        if COMPACT {
            // lvm2 SLF-PR: `block` holds the differences as `spill_differences` spilled them.
            spilled.0[..32].copy_from_slice(&block[32 * c..][..32]);
        } else {
            // Word `b` of `bytes[w]` holds byte `b` of word `w` of the eight positions, one to a byte.
            let words = transpose8(std::array::from_fn(|m| load(&block[64 * c..], m)));
            let mut bytes = words.map(|w| _mm512_permutexvar_epi8(gather, w));
            if DIFFERENCES {
                bytes = [
                    _mm512_xor_si512(bytes[0], bytes[2]),
                    _mm512_xor_si512(bytes[1], bytes[3]),
                    _mm512_xor_si512(bytes[4], bytes[6]),
                    _mm512_xor_si512(bytes[5], bytes[7]),
                    _mm512_setzero_si512(),
                    _mm512_setzero_si512(),
                    _mm512_setzero_si512(),
                    _mm512_setzero_si512(),
                ];
            }
            for (k, b) in bytes.iter().enumerate().take(if DIFFERENCES { 4 } else { 8 }) {
                store(&mut spilled.0[8 * k..][..8], 0, *b);
            }
        }
        for g in 0..groups {
            let mut acc = [_mm512_setzero_si512(); W];
            for (pair, maps) in maps.as_chunks::<2>().0.iter().enumerate() {
                let x: [__m512i; 2] = std::array::from_fn(|h| _mm512_set1_epi64(spilled.0[B * g + 2 * pair + h] as i64));
                for (z, acc) in acc.iter_mut().enumerate() {
                    let a = _mm512_gf2p8affine_epi64_epi8(x[0], load(&maps[0][z][..], 0), 0);
                    let b = _mm512_gf2p8affine_epi64_epi8(x[1], load(&maps[1][z][..], 0), 0);
                    *acc = _mm512_ternarylogic_epi64(*acc, a, b, 0x96);
                }
            }
            // Lane `l` byte `m` of `acc[z]` is byte `8z + l` of position `m`'s value.
            for (z, acc) in acc.into_iter().enumerate() {
                let at = if DIFFERENCES {
                    (c / 8) * factor_row::<W>() + z * 64 + (8 * c) % 64
                } else {
                    z * WIDTH + 8 * c
                };
                store(
                    &mut rows[g * W * WIDTH + at..][..8],
                    0,
                    _mm512_permutexvar_epi8(gather, acc),
                );
            }
        }
    }
}

/// lvm2 PFAST-K2: [`fold_gfni`] at E2 with the affine maps' operands swapped: the maps register (`maps[i][z]`, its
/// qword `l` for output byte `8 z + l`) is the source and the eight positions' input byte `i` (a qword, byte `m`
/// for position `m`) the broadcast matrix, so the broadcast rides the instruction and each maps register, loaded
/// once, serves eight chunks of eight positions and both groups. The sum's byte `8 l + s`, bit `j`, is bit `7 - s` of
/// output byte `8 z + l` of position `7 - j`; one bit transpose and one byte permute give the same rows as
/// [`fold_gfni`].
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
#[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
fn fold_gfni_e2<const B: usize, const WIDTH: usize, const DIFFERENCES: bool, const COMPACT: bool, const W: usize, const G: usize>(
    maps: &[[[u64; 8]; W]; B],
    block: &[u64],
    rows: &mut [u64],
) {
    use core::arch::x86_64::*;
    use crate::lv::primitives::simd::{load, store, transpose8};
    /// Chunks of eight positions a step.
    const CHUNKS: usize = 8;
    // Byte `8b + m` of the output is byte `8m + b` of the input: an 8 x 8 byte transpose per word.
    let gather: [u8; 64] = std::array::from_fn(|o| (8 * (o % 8) + o / 8) as u8);
    let gather = load(&gather[..], 0);
    // Byte `8m + l` of a row word is byte `8l + 7 - m` of the transposed sum.
    let spread: [u8; 64] = std::array::from_fn(|o| (8 * (o % 8) + 7 - o / 8) as u8);
    let spread = load(&spread[..], 0);
    // The GF2P8AFFINE source that makes it an 8 x 8 bit transpose of its matrix operand (bytes reversed).
    let bit_transpose = _mm512_set1_epi64(0x8040_2010_0804_0201_u64 as i64);
    // `G` groups (rows of `W * WIDTH` words), one or two.
    assert!(W == 2 && B % 2 == 0 && (1..=2).contains(&G) && (WIDTH / 8).is_multiple_of(CHUNKS));
    assert!(block.len() >= WIDTH * if COMPACT { 4 } else { 8 } && rows.len() == G * W * WIDTH);
    let mut spilled: [Spill; CHUNKS] = std::array::from_fn(|_| Spill([0u64; 64]));
    for c0 in (0..WIDTH / 8).step_by(CHUNKS) {
        for (cc, spilled) in spilled.iter_mut().enumerate() {
            let c = c0 + cc;
            if COMPACT {
                // lvm2 SLF-PR: `block` holds the differences as `spill_differences` spilled them.
                spilled.0[..32].copy_from_slice(&block[32 * c..][..32]);
                continue;
            }
            let words = transpose8(std::array::from_fn(|m| load(&block[64 * c..], m)));
            let mut bytes = words.map(|w| _mm512_permutexvar_epi8(gather, w));
            if DIFFERENCES {
                bytes = [
                    _mm512_xor_si512(bytes[0], bytes[2]),
                    _mm512_xor_si512(bytes[1], bytes[3]),
                    _mm512_xor_si512(bytes[4], bytes[6]),
                    _mm512_xor_si512(bytes[5], bytes[7]),
                    _mm512_setzero_si512(),
                    _mm512_setzero_si512(),
                    _mm512_setzero_si512(),
                    _mm512_setzero_si512(),
                ];
            }
            for (k, b) in bytes.iter().enumerate().take(if DIFFERENCES { 4 } else { 8 }) {
                store(&mut spilled.0[8 * k..][..8], 0, *b);
            }
        }
        // One output word at a time, so that each input qword's broadcast has one use and rides its affine map.
        for z in 0..2 {
            // `acc[g][cc]`: group `g`, chunk `c0 + cc`.
            let mut acc = [[_mm512_setzero_si512(); CHUNKS]; G];
            for i in (0..B).step_by(2) {
                let m: [__m512i; 2] = std::array::from_fn(|h| load(&maps[i + h][z % W][..], 0));
                for (g, acc) in acc.iter_mut().enumerate() {
                    for (cc, acc) in acc.iter_mut().enumerate() {
                        let x = |h: usize| _mm512_set1_epi64(spilled[cc].0[B * g + i + h] as i64);
                        *acc = _mm512_ternarylogic_epi64(
                            *acc,
                            _mm512_gf2p8affine_epi64_epi8(m[0], x(0), 0),
                            _mm512_gf2p8affine_epi64_epi8(m[1], x(1), 0),
                            0x96,
                        );
                    }
                }
            }
            for (g, acc) in acc.iter().enumerate() {
                for (cc, &acc) in acc.iter().enumerate() {
                    let c = c0 + cc;
                    let at = if DIFFERENCES {
                        (c / 8) * factor_row::<W>() + z * 64 + (8 * c) % 64
                    } else {
                        z * WIDTH + 8 * c
                    };
                    let v = _mm512_gf2p8affine_epi64_epi8(bit_transpose, acc, 0);
                    store(&mut rows[g * W * WIDTH + at..][..8], 0, _mm512_permutexvar_epi8(spread, v));
                }
            }
        }
    }
}

/// Words of a block's differences ([`spill_differences`]): four a position.
const DIFF_WORDS: usize = 4 * BITS;

/// lvm2 SLF-PR (PFAST4's compact Groups): a block's differences of adjacent groups as [`fold_gfni`]'s `DIFFERENCES`
/// form spills them, eight positions at a time (32 words: the bytes of words `0 ^ 2`, `1 ^ 3`, `4 ^ 6`, `5 ^ 7` of
/// the eight, transposed), all positions in order. `Skip` writes them while the block is in cache, and `Groups` reads
/// them ([`Fold::differences_compact`]): four words a position instead of the block's eight.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
))]
#[target_feature(enable = "avx512f,avx512bw,avx512vbmi,gfni")]
fn spill_differences(block: &[u64], out: &mut [u64]) {
    use core::arch::x86_64::*;
    use crate::lv::primitives::simd::{load, store, transpose8};
    assert!(block.len() >= BITS * 8 && out.len() == DIFF_WORDS);
    let gather: [u8; 64] = std::array::from_fn(|o| (8 * (o % 8) + o / 8) as u8);
    let gather = load(&gather[..], 0);
    for c in 0..BITS / 8 {
        let words = transpose8(std::array::from_fn(|m| load(&block[64 * c..], m)));
        let bytes = words.map(|w| _mm512_permutexvar_epi8(gather, w));
        let differences = [
            _mm512_xor_si512(bytes[0], bytes[2]),
            _mm512_xor_si512(bytes[1], bytes[3]),
            _mm512_xor_si512(bytes[4], bytes[6]),
            _mm512_xor_si512(bytes[5], bytes[7]),
        ];
        for (k, d) in differences.into_iter().enumerate() {
            store(&mut out[32 * c + 8 * k..][..8], 0, d);
        }
    }
}

/// lvm2 SLF-PR: whether `Skip` writes the blocks' differences for `Groups` ([`spill_differences`]); on by default,
/// `LVM_TAPE_CG=0` turns it off (dev). The same values either way.
fn compact_groups() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // lvm2 W32-P: GFNI tier only (every tier mounts this tree now; the spill and the compact fold are its kernels)
    let gfni = cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vbmi", target_feature = "gfni"));
    *ON.get_or_init(|| gfni && std::env::var("LVM_TAPE_CG").map_or(true, |v| v != "0"))
}

/// The two differences of a block's adjacent groups, five lanes at a time, laid out by lane.
impl<const W: usize> Fold<GROUP_BYTES, W> {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512vbmi",
        target_feature = "gfni"
    ))]
    fn difference_scratch() -> Vec<u64> {
        Vec::new()
    }

    #[cfg(not(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512vbmi",
        target_feature = "gfni"
    )))]
    fn difference_scratch() -> Vec<u64> {
        vec![0; 2 * 5 * (W + 1) * 64]
    }

    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512vbmi",
        target_feature = "gfni"
    ))]
    fn differences<F>(&self, _: &PowerField<F, W>, block: &[u64], rows: &mut [u64], _: &mut [u64]) {
        assert!(block.len() >= 5 * 64 * 8 && rows.len() == 10 * factor_row::<W>());
        // SAFETY: the features are enabled at compile time and both buffers are bounded above.
        unsafe { fold_gfni::<GROUP_BYTES, { 5 * 64 }, true, false, W>(&self.0, block, rows) }
    }

    /// lvm2 SLF-PR: [`Self::differences`] from the five lanes' differences as [`spill_differences`] wrote them
    /// (`5 * 64 * 4` words: a quarter of a block's). The same rows. (lvm2 W32: a group is two words at K = 32 too.)
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512vbmi",
        target_feature = "gfni"
    ))]
    fn differences_compact(&self, compact: &[u64], rows: &mut [u64]) {
        assert!(compact.len() >= 5 * 64 * 4 && rows.len() == 10 * factor_row::<W>());
        // SAFETY: the features are enabled at compile time and both buffers are bounded above.
        unsafe { fold_gfni::<GROUP_BYTES, { 5 * 64 }, true, true, W>(&self.0, compact, rows) }
    }

    #[cfg(not(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512vbmi",
        target_feature = "gfni"
    )))]
    fn differences<F: Ext<W>>(&self, field: &PowerField<F, W>, block: &[u64], rows: &mut [u64], wide: &mut [u64]) {
        // lvm2 W32-P: a group is two words (4 packs of 32); the halves' differences are words `0 ^ 2, 1 ^ 3` and
        // `4 ^ 6, 5 ^ 7`, packs 0..4 and 4..8 of their embedding.
        let fr = factor_row::<W>();
        assert!(block.len() >= 5 * 64 * 8 && rows.len() == 10 * fr && wide.len() >= 10 * (W + 1) * 64);
        for x in 0..5 {
            for z in 0..64 {
                let w = words(block, 64 * x + z);
                let packed = [w[0] ^ w[2], w[1] ^ w[3], w[4] ^ w[6], w[5] ^ w[7], 0, 0, 0, 0];
                let e = embed(&packed);
                for half in 0..2 {
                    let sum = self.fold_row(&e, half);
                    let at = (5 * half + x) * (W + 1) * 64;
                    for (k, &word) in sum[..W + 1].iter().enumerate() {
                        wide[at + k * 64 + z] = word;
                    }
                }
            }
        }
        for (i, row) in rows.chunks_exact_mut(fr).enumerate() {
            field.reduce_row(row, &wide[i * (W + 1) * 64..][..(W + 1) * 64], 64);
        }
    }
}

struct Layer<'a> {
    witness: &'a Witness,
    /// The round whose `chi` each segment's claim is on.
    rounds: Vec<usize>,
    /// lvm2 U-TAPE (T-P2's halves): the upper half-batch. With it the layer has two segments at the same round,
    /// `witness` (instances `< 2^n_log`) and `upper`, each its own written prefix and padding block: the half bit plays
    /// the segment variable's role in every `eq` table. `None` is leanVM's layer.
    upper: Option<&'a Witness>,
    /// lvm2 U-TAPE: the tasks `(segment, g)` of a pass: each segment's written blocks but its holes
    /// ([`Witness::holes`]), then its padding block once. Without holes, leanVM's `held * segment + g`.
    tasks: Vec<(usize, usize)>,
}

impl<'a> Layer<'a> {
    fn new(witness: &'a Witness, rounds: Vec<usize>, upper: Option<&'a Witness>) -> Self {
        let mut tasks = Vec::new();
        for s in 0..rounds.len() {
            let w = if s == 1 { upper.unwrap_or(witness) } else { witness };
            let holes = w.holes();
            let mut h = 0;
            for g in 0..w.written() {
                if h < holes.len() && holes[h] == g {
                    h += 1;
                    continue;
                }
                tasks.push((s, g));
            }
            if w.written() < w.shape.n_blocks() {
                tasks.push((s, w.written()));
            }
        }
        Layer { witness, rounds, upper, tasks }
    }
}

/// A row of a table in the power basis: `W` words per position, laid out by word.
#[inline(always)]
const fn row<const W: usize>() -> usize {
    W * BITS
}

/// E3's row, for the forms that stay E3's.
#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512vbmi",
    target_feature = "gfni"
)))]
const ROW: usize = 3 * BITS;

/// `acc += a * b` on binary polynomials, `a` of `A` words (of `a`'s array) and `b` of `W`.
#[inline(always)]
fn add_mul_n<const A: usize, const W: usize, const N: usize, const M: usize>(acc: &mut [u64; N], a: &[u64; M], b: &[u64; W]) {
    for i in 0..A {
        for k in 0..W {
            let p = crate::lv::primitives::field::gf2_64::mul_wide(a[i], b[k]);
            acc[i + k] ^= p as u64;
            acc[i + k + 1] ^= (p >> 64) as u64;
        }
    }
}

impl Layer<'_> {
    /// lvm2 U-TAPE: the witness segment `segment`'s blocks come from.
    fn part(&self, segment: usize) -> &Witness {
        match self.upper {
            Some(u) if segment == 1 => u,
            _ => self.witness,
        }
    }

    /// The blocks a segment's tasks walk: those written, then the padding block once, standing
    /// for every block after them.
    fn held_of(&self, segment: usize) -> usize {
        self.part(segment).held()
    }

    /// Task `t` as `(segment, g)` ([`Layer::tasks`]).
    fn locate(&self, task: usize) -> (usize, usize) {
        self.tasks[task]
    }

    /// Task `t`, as `(segment, g, block)`, recomputed into `scratch` if not stored.
    fn block<'b>(&'b self, scratch: &'b mut Recompute, task: usize) -> (usize, usize, &'b [u64]) {
        let (segment, g) = self.locate(task);
        (segment, g, self.part(segment).state(scratch, self.rounds[segment], g))
    }

    fn n_tasks(&self) -> usize {
        self.tasks.len()
    }

    /// The tasks of the written blocks but the holes (the passes whose padding block adds nothing: `Skip`, `Groups`).
    fn written_tasks(&self) -> Vec<(usize, usize)> {
        self.tasks.iter().copied().filter(|&(s, g)| g < self.part(s).written()).collect()
    }

    /// lvm2 U-TAPE: segment `segment`'s live rows of the table (leanVM: `layout.live`; with an upper half, each
    /// half's own `2 · written`).
    fn live_of(&self, segment: usize, layout: Rows) -> usize {
        if self.upper.is_some() { 2 * self.part(segment).written() } else { layout.live }
    }

    /// Each task's weight in `eq`, a table over the blocks then the segment: the padding block's
    /// is the sum over the blocks it stands for.
    fn task_weights<F: Copy + for<'a> std::iter::Sum<&'a F>>(&self, eq: &[F]) -> Vec<F> {
        let nb = self.witness.shape.n_blocks();
        (0..self.n_tasks())
            .map(|task| {
                let (segment, g) = self.locate(task);
                let eq = &eq[nb * segment..][..nb];
                if g < self.part(segment).written() {
                    eq[g]
                } else {
                    // the padding block stands for the blocks after the written ones and for the holes
                    eq[g..].iter().chain(self.part(segment).holes().iter().map(|&h| &eq[h])).sum()
                }
            })
            .collect()
    }

    /// Per pack `q` of a block, the coefficients of
    /// `sum over blocks and positions of eq(point[PACK_VARS..], block) * weights[j] * product(q, j)`,
    /// where the product is `ones * u[j] + (ones + u[j + 1]) * u[j + 2]` on embeddings, the
    /// unprojected `chi`.
    ///
    /// Nothing here knows where the polynomials will be evaluated, so each product meets its
    /// weight bit by bit. The position weights are the same in every block, so a block's sum
    /// over positions is taken bit by bit, by GFNI outer products where they are compiled
    /// (`products_gfni`) and by digit buckets elsewhere ([`Weigh`], E3 only); only that sum meets the
    /// block's weight, as field elements.
    fn pack_products<F: Ext<W>, const W: usize>(&self, claim: &Claim<F>) -> Vec<[F; PROD_BITS]> {
        // lvm2 W32-P: off the GFNI tier (v4p, v2) both fields take the digit buckets.
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
        if W == 2 {
            return self.pack_products_e2(claim);
        }
        self.pack_products_buckets(claim)
    }

    /// lvm2 W32-P: E2 by W32 G0's `Product32` (per block position, `ones (a + c) + b c` of each pack, staged by
    /// coefficient, then GFNI outer products with the position weights; each block's column sums meet its weight
    /// as Karatsuba parts, `F128Unreduced::from_products`). The same sums as [`Self::pack_products_buckets`].
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
    fn pack_products_e2<F: Ext<W>, const W: usize>(&self, claim: &Claim<F>) -> Vec<[F; PROD_BITS]> {
        use core::arch::x86_64::{__m512i, _mm512_xor_si512};
        use crate::lv::w32::{column, v4::Product32};
        assert_eq!(W, 2);
        let weights = self.task_weights(&F::eq_table(&claim.point[PACK_VARS..]));
        let w: Vec<[u64; 2]> = claim.weights.iter().map(|x| {
            let l = x.to_limbs();
            [l[0], l[1 % W]]
        }).collect();
        let kernel = Product32::new(&w);
        let sums: Vec<__m512i> = crate::lv::parallel::map_reduce_with_state(
            self.n_tasks(),
            || (kernel.scratch(), Recompute::new()),
            || kernel.sums(),
            |(scratch, recompute), sums, task| {
                let (_, _, block) = self.block(recompute, task);
                let wb = weights[task].to_limbs();
                kernel.block_sums(scratch, block, [wb[0], wb[1 % W]], sums);
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    // SAFETY: this tree is compiled with AVX-512F.
                    *x = unsafe { _mm512_xor_si512(*x, y) };
                }
                a
            },
        );
        (0..PACKS)
            .map(|q| {
                std::array::from_fn(|c| {
                    let v = F128Unreduced::from_products(Product32::parts(&sums, column(q, c))).reduce();
                    F::from_limbs(std::array::from_fn(|k| [v.c0, v.c1][k]))
                })
            })
            .collect()
    }

    /// [`Self::pack_products`] by digit buckets (the v2/v4p tree's, generic in `W`): this tier's E3 form, and E2's
    /// oracle.
    fn pack_products_buckets<F: Ext<W>, const W: usize>(&self, claim: &Claim<F>) -> Vec<[F; PROD_BITS]> {
        let weights = self.task_weights(&F::eq_table(&claim.point[PACK_VARS..]));
        let groups = Groups::new::<F, W>(&claim.weights);
        let sums = crate::lv::parallel::map_reduce_with_state(
            self.n_tasks(),
            || {
                (
                    vec![[Part::ZERO; BITS]; PACKS / PART],
                    vec![vec![Part::ZERO; 64 * W]; PACKS / PART],
                    Box::new([Part::ZERO; 1 << DIGIT_BITS]),
                    Recompute::new(),
                )
            },
            || vec![<F::Unreduced as Unreduced<F>>::ZERO; PAYLOAD_BITS],
            |(payloads, rows, digit_sums, recompute), sums, task| {
                let (_, _, block) = self.block(recompute, task);
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        let e: [[u64; PACKS]; 5] = std::array::from_fn(|x| embed(words(block, js[x])));
                        for x in 0..5 {
                            let p = products(&e[x], &e[(x + 1) % 5], &e[(x + 2) % 5]);
                            for (q, part) in payloads.iter_mut().enumerate() {
                                part[js[x]] = Part::pack(p[PART * q..][..PART].try_into().unwrap());
                            }
                        }
                    }
                }
                for (payloads, rows) in payloads.iter().zip(rows.iter_mut()) {
                    groups.add_rows(payloads, rows, digit_sums);
                }
                // Row `r` holds bit `r` of each payload bit's weighted sum: transposed, they are
                // field elements, which the block's weight multiplies.
                let mut columns = [[0u64; 64]; W];
                for m in 0..PAYLOAD_BITS / 64 {
                    let (q, w) = (m / PART_WORDS, m % PART_WORDS);
                    for (k, column) in columns.iter_mut().enumerate() {
                        for (b, word) in column.iter_mut().enumerate() {
                            *word = rows[q][64 * k + b].0[w];
                        }
                        transpose64(column);
                    }
                    for (t, sum) in sums[64 * m..][..64].iter_mut().enumerate() {
                        *sum ^= weights[task].mul_unreduced(F::from_limbs(std::array::from_fn(|k| columns[k][t])));
                    }
                }
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    *x ^= y;
                }
                a
            },
        );
        (0..PACKS)
            .map(|q| std::array::from_fn(|c| sums[128 * q + c].reduce()))
            .collect()
    }

    /// The layer's summand at `s`, extended over the packs of a group, keeping variable `SKIP`
    /// binary and summing over the later variables. Its two grids give the first `SKIP` round
    /// messages and the next round's values at zero and one.
    ///
    /// A point at infinity in some variable keeps only the product `u[j + 1] * u[j + 2]`, summed
    /// here. A binary one is a pack, whose sum `binary` already holds. The packs of the padding
    /// block are all equal, so their extension vanishes there.
    /// lvm2 W32: per half and group, the 5 mixed points of `{0, 1, inf}^2` ([`MIXED`]); a slot's sum has `W + 2`
    /// words (a 105-bit product times a weight).
    fn skip_sums<F: Ext<W>, const W: usize>(
        &self,
        claim: &Claim<F>,
        field: &PowerField<F, W>,
        polys: &[Element<W>],
        binary: &[[F; GROUP]; 2],
        diffs: &mut [u64],
    ) -> [Vec<F>; 2] {
        let weights = SkipWeights::<W>::new(polys.to_vec());
        // lvm2 SLF-PR: with `diffs` (the compact Groups), written task `t`'s block differences go to its `DIFF_WORDS`.
        let compact = !diffs.is_empty();
        let stream = streams(diffs.len());
        let out = crate::lv::parallel::SendPtr(diffs.as_mut_ptr());
        let groups: Vec<Element<W>> = F::eq_table(&claim.point[SKIP + 1..])
            .iter()
            .map(|&e| field.to_poly(e))
            .collect();
        let (nb, wt) = (self.witness.shape.n_blocks(), self.written_tasks());
        assert!(!compact || diffs.len() == wt.len() * DIFF_WORDS);
        // lvm2 BND-P: backwards ([`walk`]), from the blocks `Product` read last
        let rev = true;
        let mixed = crate::lv::parallel::map_reduce_with_state(
            wt.len(),
            || (SkipBlock::<W>::new(), Recompute::new(), Vec::<u64>::new()),
            || [[[0u64; 8]; 5]; 2],
            |(skip, recompute, local), total, step| {
                let task = walk(rev, wt.len(), step);
                let (segment, g) = wt[task];
                let (row, block) = (g + nb * segment, self.part(segment).state(recompute, self.rounds[segment], g));
                skip.run(block, &weights);
                if compact {
                    // SAFETY: task `task` alone writes words `task * DIFF_WORDS..` of `diffs`, which holds `wt.len()`
                    // blocks' worth, and `diffs` stays borrowed until the dispatch returns.
                    let out = unsafe { out.slice(task * DIFF_WORDS, DIFF_WORDS) };
                    // SAFETY: the features are enabled at compile time (this tree is built only with them).
                    #[cfg(all(
                        target_arch = "x86_64",
                        target_feature = "avx512f",
                        target_feature = "avx512vbmi",
                        target_feature = "gfni"
                    ))]
                    publish(stream, out, local, |d| unsafe { spill_differences(block, d) });
                    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vbmi", target_feature = "gfni")))]
                    unreachable!("compact Groups is the GFNI tier's ({out:p}, {stream}, {})", local.len());
                }
                for half in 0..2 {
                    let weight = &groups[2 * row + half];
                    for (side, total) in total.iter_mut().enumerate() {
                        for (p, total) in total.iter_mut().enumerate() {
                            add_mul_n::<5, W, 8, 5>(total, &skip.get(slot(half, side, p)), weight);
                        }
                    }
                }
            },
            |mut a, b| {
                for (a, b) in a.iter_mut().flatten().zip(b.iter().flatten()) {
                    for (x, y) in a.iter_mut().zip(b) {
                        *x ^= y;
                    }
                }
                a
            },
        );
        let eval = field.eval();
        std::array::from_fn(|side| {
            let mut sums = vec![F::ZERO; TERNARY];
            for (p, &t) in MIXED.iter().enumerate() {
                sums[t] = eval.eval(&mixed[side][p]);
            }
            for (q, &value) in binary[side].iter().enumerate() {
                sums[ternary(q)] = value;
            }
            sums
        })
    }

    /// The fourth round needs only its quadratic coefficient: the binary values rode `Skip`.
    /// lvm2 SLF-PR: a non-empty `diffs` holds the written blocks' differences, as [`Self::skip_sums`] wrote them.
    fn group_infinity<F: Ext<W>, const W: usize>(&self, round: &Round<F, W>, challenges: &[F], point: &[F], diffs: &[u64]) -> F {
        let field = round.field;
        let fr = factor_row::<W>();
        let fold: Vec<Element<W>> = F::eq_table(challenges).iter().map(|&e| field.to_poly(e)).collect();
        let fold = Fold::<GROUP_BYTES, W>::new(field, &fold);
        let groups: Vec<Element<W>> = F::eq_table(&point[SKIP + 1..]).iter().map(|&e| field.to_poly(e)).collect();
        let (nb, wt) = (self.witness.shape.n_blocks(), self.written_tasks());
        let sum = crate::lv::parallel::map_reduce_with_state(
            wt.len(),
            || {
                (
                    vec![0u64; 10 * fr],
                    Fold::<GROUP_BYTES, W>::difference_scratch(),
                    Recompute::new(),
                )
            },
            || [0u64; 9],
            |(rows, wide, recompute), total, task| {
                let (segment, g) = wt[task];
                let compact = if diffs.is_empty() { None } else { Some(&diffs[task * DIFF_WORDS..][..DIFF_WORDS]) };
                let block = if compact.is_some() { &[][..] } else { self.part(segment).state(recompute, self.rounds[segment], g) };
                let mut sums = [[0u64; 6]; 2];
                // lvm2 PFAST-K3: at E2 the products stay unreduced, `3W` words, summed in registers until the task's end.
                let mut dots = [WideDot::new(); 2];
                for r in 0..5 {
                    match compact {
                        #[cfg(all(
                            target_arch = "x86_64",
                            target_feature = "avx512f",
                            target_feature = "avx512vbmi",
                            target_feature = "gfni"
                        ))]
                        Some(d) => fold.differences_compact(&d[r * 5 * 64 * 4..], rows),
                        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vbmi", target_feature = "gfni")))]
                        Some(_) => unreachable!("compact Groups is the GFNI tier's"),
                        None => fold.differences(field, &block[r * 5 * 64 * 8..], rows, wide),
                    }
                    for (half, sum) in sums.iter_mut().enumerate() {
                        let lanes = &rows[5 * half * fr..][..5 * fr];
                        for x in 0..5 {
                            let a = &lanes[(x + 1) % 5 * fr..][..fr];
                            let b = &lanes[(x + 2) % 5 * fr..][..fr];
                            let w = &round.weights[(5 * r + x) * fr..][..fr];
                            if W == 2 {
                                field.weighted_dot_e2_add(&mut dots[half], a, b, w, 64);
                                continue;
                            }
                            for (sum, value) in sum.iter_mut().zip(field.weighted_dot(a, b, w, 64)) {
                                *sum ^= value;
                            }
                        }
                    }
                }
                if W == 2 {
                    sums = dots.map(|dot| dot.finish());
                }
                for (half, sum) in sums.iter().enumerate() {
                    let weight = &groups[2 * (nb * segment + g) + half];
                    if W == 2 {
                        add_mul_n::<6, W, 9, 6>(total, sum, weight);
                    } else {
                        add_wide::<W>(total, sum, weight);
                    }
                }
            },
            |mut a, b| {
                for (a, b) in a.iter_mut().zip(b) {
                    *a ^= b;
                }
                a
            },
        );
        if W == 2 {
            // lvm2 PFAST-K3: `4W` words at E2, past the evaluation table's `3W`: words `2W..4W` reduced first, the
            // same value at `s`.
            let high = field.reduce(&std::array::from_fn(|k| if k < 2 * W { sum[2 * W + k] } else { 0 }));
            let sum: [u64; 9] = std::array::from_fn(|k| {
                if k < 2 * W {
                    sum[k]
                } else if k < 3 * W {
                    high[k - 2 * W]
                } else {
                    0
                }
            });
            return round.field.eval().eval(&sum);
        }
        round.field.eval().eval(&sum)
    }

    /// The table the remaining rounds fold, a row per half block: `T[j]` folded over the half's
    /// packs at `challenges`. A block's two halves are the first of those rounds' pairs, so its
    /// round values are summed while the rows are at hand, weighted by `blocks`. The padding
    /// block's halves are one row, its segment's entry of `pads`.
    fn table<F: Ext<W>, const W: usize>(
        &self,
        round: &Round<F, W>,
        challenges: &[F],
        blocks: &[F],
        layout: Rows,
        table: &mut [u64],
        pads: &mut [u64],
    ) -> (F, F) {
        let (field, row, fr) = (round.field, row::<W>(), factor_row::<W>());
        let fold: Vec<Element<W>> = F::eq_table(challenges).iter().map(|&e| field.to_poly(e)).collect();
        let fold = Fold::<HALF_BYTES, W>::new(field, &fold);
        let weights = self.task_weights(blocks);
        // Rows of segments that do not exist are zero, and so is their product.
        table[self.rounds.len() * layout.live * row..layout.len() * row].fill(0);
        pads[self.rounds.len() * row..].fill(0);
        // Task `held * segment + g` owns its rows: a written block's two, or its segment's padding row (lvm2 U-TAPE:
        // with an upper half, each half's rows its own run, the upper's after the lower's).
        let mut parts: Vec<&mut [u64]> = Vec::with_capacity(self.n_tasks());
        let mut hole_rows: Vec<(&mut [u64], usize)> = Vec::new();
        {
            let mut rest = &mut table[..];
            let mut pad_rows = &mut pads[..];
            for seg in 0..self.rounds.len() {
                let (segment, tail) = rest.split_at_mut(self.live_of(seg, layout) * row);
                let (pad, pad_tail) = pad_rows.split_at_mut(row);
                (rest, pad_rows) = (tail, pad_tail);
                let holes = self.part(seg).holes();
                for (g, chunk) in segment.chunks_mut(2 * row).enumerate() {
                    // (lvm2 U-TAPE: a hole's rows are filled from the padding row after the pass)
                    if holes.binary_search(&g).is_ok() { hole_rows.push((chunk, seg)) } else { parts.push(chunk) }
                }
                if self.held_of(seg) > self.part(seg).written() {
                    parts.push(pad);
                }
            }
        }
        let stream = streams(layout.len() * row);
        let sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || {
                (
                    vec![0u64; 4 * fr],
                    Fold::<HALF_BYTES, W>::scratch(),
                    Recompute::new(),
                    Vec::new(),
                )
            },
            RoundSums::default,
            |(scratch, wide, recompute, local), sums, task, [part]| {
                let (_, _, block) = self.block(recompute, task);
                publish(stream, &mut *part[0], local, |rows| {
                    fold.rows(field, block, rows, wide);
                    round.add_pair(sums, scratch, &rows[..row], &rows[rows.len() - row..], weights[task]);
                });
            },
            RoundSums::merge,
        );
        drop(parts);
        // lvm2 U-TAPE: a hole's two rows are its segment's padding row (their pair's sums rode the padding task's weight)
        for (chunk, seg) in hole_rows {
            for out in chunk.chunks_exact_mut(row) {
                out.copy_from_slice(&pads[seg * row..][..row]);
            }
        }
        round.finish(&sums)
    }
}

/// `acc += a * b` for a `2W`-word unreduced sum `a` and an element `b`.
#[inline(always)]
fn add_wide<const W: usize>(acc: &mut [u64; 9], a: &[u64; 6], b: &[u64; W]) {
    if W == 3 {
        add_mul_n::<6, W, 9, 6>(acc, a, b);
    } else {
        add_mul_n::<4, W, 9, 6>(acc, a, b);
    }
}

/// The sums a round accumulates, unreduced: its values at `0` and at infinity (`3W` words of nine).
#[derive(Clone, Copy, Default)]
struct RoundSums([u64; 9], [u64; 9]);

impl RoundSums {
    fn merge(mut self, other: Self) -> Self {
        for i in 0..9 {
            self.0[i] ^= other.0[i];
            self.1[i] ^= other.1[i];
        }
        self
    }
}

/// The position weights and constants `kappa * weights[j + 2]`, by lane, then by word.
struct Round<'a, F, const W: usize> {
    field: &'a PowerField<F, W>,
    kappa: Element<W>,
    weights: Vec<u64>,
    constant: Vec<u64>,
}

impl<'a, F: Ext<W>, const W: usize> Round<'a, F, W> {
    /// lvm2 R9-KG: `polys` are the claim's weights in the power basis, converted once for `Skip`
    /// and here.
    fn new(field: &'a PowerField<F, W>, claim: &Claim<F>, polys: &[Element<W>], kappa: F) -> Self {
        let fr = factor_row::<W>();
        let (mut weights, mut constant) = (vec![0u64; row::<W>()], vec![0u64; row::<W>()]);
        let constants: Vec<Element<W>> = (0..BITS).map(|j| field.to_poly(kappa * claim.weights[along(j, 2)])).collect();
        for j in 0..BITS {
            let at = fr * (j / 64);
            set(&mut weights[at..][..fr], 64, j % 64, &polys[j]);
            set(&mut constant[at..][..fr], 64, j % 64, &constants[j]);
        }
        Self {
            field,
            kappa: field.to_poly(kappa),
            weights,
            constant,
        }
    }

    /// Add one pair of rows to a round's sums, weighted by `eq`.
    fn add_pair(&self, sums: &mut RoundSums, scratch: &mut [u64], low: &[u64], high: &[u64], eq: F) {
        let (zero, infinity) =
            self.field
                .chi_dot_pair([low, high], &self.weights, &self.constant, &self.kappa, scratch);
        let weight = self.field.to_poly(eq);
        add_wide(&mut sums.0, &zero, &weight);
        add_wide(&mut sums.1, &infinity, &weight);
    }

    fn finish(&self, sums: &RoundSums) -> (F, F) {
        (self.field.eval().eval(&sums.0), self.field.eval().eval(&sums.1))
    }

    /// Fold the rows of `src`, laid out as `from`, in pairs into `dst`, and sum the next round's
    /// values over the pairs of what was just written, weighted by `eq`.
    fn fold(
        &self,
        src: &[u64],
        from: Rows,
        dst: &mut [u64],
        pads: &[u64],
        challenge: &Element<W>,
        eq: &[F],
        rev: bool,
    ) -> (F, F) {
        let (row, fr) = (row::<W>(), factor_row::<W>());
        let to = from.next();
        let fold = |out: &mut [u64], segment: usize, r: usize| {
            let (low, high) = if from.m == 1 {
                (
                    from.row(src, pads, 2 * segment, 0),
                    from.row(src, pads, 2 * segment + 1, 0),
                )
            } else {
                (
                    from.row(src, pads, segment, 2 * r),
                    from.row(src, pads, segment, 2 * r + 1),
                )
            };
            self.field.fold_row(out, low, high, challenge, BITS);
        };
        if to.m == 1 {
            // A row per segment, few enough to fold in place.
            for (segment, out) in dst[..to.len() * row].chunks_exact_mut(row).enumerate() {
                fold(out, segment, 0);
            }
            let mut sums = RoundSums::default();
            let mut scratch = vec![0u64; 4 * fr];
            for (pair, &eq) in dst[..to.len() * row].chunks_exact(2 * row).zip(eq) {
                self.add_pair(&mut sums, &mut scratch, &pair[..row], &pair[row..], eq);
            }
            return self.finish(&sums);
        }
        // A task per pair of rows written, the second of a ragged one being the padding row.
        let (pairs, half) = (to.live.div_ceil(2), to.m / 2);
        // Task `pairs * segment + t` owns rows `2t` and `2t + 1` of its segment, the last one alone if it is ragged.
        // With no block written, no row is live and there are no parts.
        let mut parts: Vec<&mut [u64]> = dst[..to.len() * row]
            .chunks_mut(to.live.max(1) * row)
            .flat_map(|segment| segment.chunks_mut(2 * row))
            .collect();
        // lvm2 BND-P: backwards when `rev` (the first fold, [`walk`]), from the rows `Tables` wrote last
        let n = parts.len();
        if rev {
            parts.reverse();
        }
        let stream = streams(to.len() * row);
        let mut sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || (vec![0u64; 4 * fr], Vec::new()),
            RoundSums::default,
            |(scratch, local), sums, task, [part]| {
                let task = walk(rev, n, task);
                let (segment, t) = (task / pairs, task % pairs);
                publish(stream, &mut *part[0], local, |rows| {
                    let n = rows.len() / row;
                    for (i, out) in rows.chunks_exact_mut(row).enumerate() {
                        fold(out, segment, 2 * t + i);
                    }
                    let high = if n == 2 {
                        &rows[row..]
                    } else {
                        &pads[segment * row..][..row]
                    };
                    self.add_pair(sums, scratch, &rows[..row], high, eq[half * segment + t]);
                });
            },
            RoundSums::merge,
        );
        self.add_padding(&mut sums, to, pads, eq);
        self.finish(&sums)
    }

    /// Add the pairs of two padding rows of a table laid out as `layout`, weighted by `eq`: each
    /// segment's padding row, once, at the sum of their weights.
    fn add_padding(&self, sums: &mut RoundSums, layout: Rows, pads: &[u64], eq: &[F]) {
        let (first, half) = (layout.live.div_ceil(2), layout.m / 2);
        if first == half {
            return;
        }
        let mut scratch = vec![0u64; 4 * factor_row::<W>()];
        for (pad, eq) in pads.chunks_exact(row::<W>()).zip(eq.chunks_exact(half)) {
            self.add_pair(sums, &mut scratch, pad, pad, eq[first..].iter().sum());
        }
    }
}

/// The rows of the table the tail folds: per segment, the first `live` of `m`, then, if there are
/// fewer, the padding row every later one equals, kept apart. Once `m` is one, a row per segment.
/// A row is `width` words (`W * BITS`).
#[derive(Clone, Copy)]
struct Rows {
    m: usize,
    live: usize,
    segments: usize,
    width: usize,
}

impl Rows {
    fn len(&self) -> usize {
        self.segments * self.live
    }

    /// The layout once the next variable is bound: the group, the block's, then the segment's.
    fn next(&self) -> Self {
        match self.m {
            1 => Self {
                segments: self.segments / 2,
                ..*self
            },
            // The fold writes every segment's row, a padding one included.
            2 => Self { m: 1, live: 1, ..*self },
            m => Self {
                m: m / 2,
                live: self.live.div_ceil(2),
                ..*self
            },
        }
    }

    fn row<'t>(&self, table: &'t [u64], pads: &'t [u64], segment: usize, r: usize) -> &'t [u64] {
        let row = self.width;
        if r < self.live {
            &table[(self.live * segment + r) * row..][..row]
        } else {
            &pads[segment * row..][..row]
        }
    }
}

/// lvm2 SLF-PR (PFAST4's rider, the v4p tree's form): a pass that writes at least this many bytes of table builds each
/// task's rows in the task's own buffer, sums them there, and publishes them with streaming stores ([`Stream`]), so
/// the table's lines are not fetched before they are overwritten. A smaller table is stored in place, to stay in the
/// cache for the next pass. The rows' values are the same either way. `LVM_TAPE_NT=0|1` forces it off or on (dev).
const STREAM_MIN_BYTES: usize = 16 << 20;

/// Whether a pass writing `words` words of table publishes them by streaming stores ([`STREAM_MIN_BYTES`]).
fn streams(words: usize) -> bool {
    static FORCE: std::sync::OnceLock<Option<bool>> = std::sync::OnceLock::new();
    let force = *FORCE.get_or_init(|| std::env::var("LVM_TAPE_NT").ok().map(|v| v != "0"));
    force.unwrap_or(8 * words >= STREAM_MIN_BYTES)
}

/// lvm2 BND-P (PFAST5's rider): `Skip` and the tail's first fold walk their tasks backwards, so each starts on the
/// end of the blocks (rows) the pass before it (`Product`, `Tables`, both forwards) left in the cache. Only the order
/// of the claims changes; every task writes its own rows and the sums are XORs, so the bytes are the same.
/// The task a walk of `n` tasks runs at step `i`: `n - 1 - i` backwards, else `i`.
#[inline(always)]
fn walk(rev: bool, n: usize, i: usize) -> usize {
    if rev { n - 1 - i } else { i }
}

/// Run `work` on the rows that end up in `out`: built in `local` and streamed to `out` if `stream`, else in place.
#[inline(always)]
fn publish<R>(stream: bool, out: &mut [u64], local: &mut Vec<u64>, work: impl FnOnce(&mut [u64]) -> R) -> R {
    if !stream {
        return work(out);
    }
    if local.len() < out.len() {
        local.resize(out.len(), 0);
    }
    let rows = &mut local[..out.len()];
    let r = work(rows);
    Stream::new().copy(out, rows);
    r
}

// The paired tail: with AVX-512, a pass over the table binds two variables, so the tail reads
// each table half as often. Its messages are the same as two single rounds'.

const PAIRED_TAIL: bool = cfg!(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "vpclmulqdq"
));

impl Rows {
    fn paired(&self) -> bool {
        PAIRED_TAIL && self.m >= 4
    }
}

#[derive(Clone, Copy, Default)]
struct PairSums([[u64; 9]; 8]);

impl PairSums {
    fn merge(mut self, other: Self) -> Self {
        for (a, b) in self.0.iter_mut().zip(other.0) {
            for (a, b) in a.iter_mut().zip(b) {
                *a ^= b;
            }
        }
        self
    }
}

/// The eight bivariate values needed to send two ordinary round messages.
struct RoundPair<F>([F; 8]);

impl<F: Copy + std::ops::Add<Output = F> + std::ops::Mul<Output = F>> RoundPair<F> {
    fn first(&self, eta: F) -> (F, F) {
        let q = &self.0;
        (q[0] + eta * (q[0] + q[2]), q[1] + eta * (q[1] + q[3]))
    }

    fn second(&self, r: F) -> (F, F) {
        let q = &self.0;
        let r2 = r * r + r;
        (
            q[0] + r * (q[0] + q[4]) + r2 * q[1],
            q[6] + r * (q[6] + q[5]) + r2 * q[7],
        )
    }
}

enum TailMessage<F> {
    Single(F, F),
    Pair(RoundPair<F>),
}

impl<F: Copy + std::ops::Add<Output = F> + std::ops::Mul<Output = F>> TailMessage<F> {
    fn first(&self, eta: F) -> (F, F) {
        match self {
            Self::Single(zero, infinity) => (*zero, *infinity),
            Self::Pair(pair) => pair.first(eta),
        }
    }
}

impl Layer<'_> {
    /// [`Layer::table`], summing the values of the first two rounds over each four rows.
    fn table_pair<F: Ext<W>, const W: usize>(
        &self,
        round: &Round<F, W>,
        challenges: &[F],
        eq: &[F],
        layout: Rows,
        table: &mut [u64],
        pads: &mut [u64],
    ) -> RoundPair<F> {
        let (field, row, fr) = (round.field, row::<W>(), factor_row::<W>());
        let fold: Vec<Element<W>> = F::eq_table(challenges).iter().map(|&e| field.to_poly(e)).collect();
        let fold = Fold::<HALF_BYTES, W>::new(field, &fold);
        table[self.rounds.len() * layout.live * row..layout.len() * row].fill(0);
        pads.fill(0);
        assert!(self.upper.is_none(), "the paired table is leanVM's layer's");
        let (held, written) = (self.held_of(0), self.witness.written());
        if held > written {
            let (mut recompute, mut wide) = (Recompute::new(), Fold::<HALF_BYTES, W>::scratch());
            for segment in 0..self.rounds.len() {
                let (_, _, block) = self.block(&mut recompute, held * segment + written);
                fold.rows(field, block, &mut pads[segment * row..][..row], &mut wide);
            }
        }
        let pairs = written.div_ceil(2);
        let stream = streams(self.rounds.len() * layout.live * row);
        let mut parts: Vec<&mut [u64]> = table[..self.rounds.len() * layout.live * row]
            .chunks_mut(layout.live.max(1) * row)
            .flat_map(|segment| segment.chunks_mut(4 * row))
            .collect();
        let pads = &*pads;
        let mut sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || {
                (
                    vec![0u64; 12 * fr],
                    Fold::<HALF_BYTES, W>::scratch(),
                    Recompute::new(),
                    Vec::new(),
                )
            },
            PairSums::default,
            |(scratch, wide, recompute, local), sums, task, [part]| {
                let (segment, pair) = (task / pairs, task % pairs);
                publish(stream, &mut *part[0], local, |rows| {
                    for (i, rows) in rows.chunks_mut(2 * row).enumerate() {
                        let (_, _, block) = self.block(recompute, held * segment + 2 * pair + i);
                        fold.rows(field, block, rows, wide);
                    }
                    let n = rows.len() / row;
                    round.add_quad(
                        sums,
                        scratch,
                        std::array::from_fn(|i| {
                            if i < n {
                                &rows[i * row..][..row]
                            } else {
                                &pads[segment * row..][..row]
                            }
                        }),
                        eq[layout.m / 4 * segment + pair],
                    );
                });
            },
            PairSums::merge,
        );
        round.add_padding_quad(&mut sums, layout, pads, eq);
        round.finish_pair(&sums)
    }
}

impl<F: Ext<W>, const W: usize> Round<'_, F, W> {
    fn add_quad(&self, sums: &mut PairSums, scratch: &mut [u64], rows: [&[u64]; 4], eq: F) {
        let values = self
            .field
            .chi_dot_quad(rows, &self.weights, &self.constant, &self.kappa, scratch);
        let weight = self.field.to_poly(eq);
        for (sum, value) in sums.0.iter_mut().zip(values) {
            add_wide(sum, &value, &weight);
        }
    }

    fn finish_pair(&self, sums: &PairSums) -> RoundPair<F> {
        RoundPair(sums.0.map(|sum| self.field.eval().eval(&sum)))
    }

    /// [`Round::fold`] of two variables at once.
    fn fold_pair(
        &self,
        src: &[u64],
        from: Rows,
        dst: &mut [u64],
        pads: &[u64],
        challenges: &[Element<W>; 2],
        eq: &[F],
        rev: bool,
    ) -> TailMessage<F> {
        let (row, fr) = (row::<W>(), factor_row::<W>());
        let to = from.next().next();
        let challenges = [
            challenges[0],
            challenges[1],
            self.field.mul(&challenges[0], &challenges[1]),
        ];
        let fold = |out: &mut [u64], segment: usize, r: usize| {
            self.field.fold_quad(
                out,
                std::array::from_fn(|i| from.row(src, pads, segment, 4 * r + i)),
                &challenges,
                BITS,
            );
        };
        if to.m < 4 {
            for (i, out) in dst[..to.len() * row].chunks_exact_mut(row).enumerate() {
                fold(out, i / to.live, i % to.live);
            }
            let mut sums = RoundSums::default();
            let mut scratch = vec![0; 4 * fr];
            if to.m == 1 {
                for (pair, &eq) in dst[..to.len() * row].chunks_exact(2 * row).zip(eq) {
                    self.add_pair(&mut sums, &mut scratch, &pair[..row], &pair[row..], eq);
                }
            } else {
                for (segment, &eq) in eq.iter().enumerate() {
                    self.add_pair(
                        &mut sums,
                        &mut scratch,
                        to.row(dst, pads, segment, 0),
                        to.row(dst, pads, segment, 1),
                        eq,
                    );
                }
            }
            let (zero, infinity) = self.finish(&sums);
            return TailMessage::Single(zero, infinity);
        }
        let quads = to.live.div_ceil(4);
        let mut parts: Vec<&mut [u64]> = dst[..to.len() * row]
            .chunks_mut(to.live.max(1) * row)
            .flat_map(|segment| segment.chunks_mut(4 * row))
            .collect();
        // lvm2 BND-P: backwards when `rev` (the first fold, [`walk`]), from the rows `Tables` wrote last
        let n = parts.len();
        if rev {
            parts.reverse();
        }
        let stream = streams(to.len() * row);
        let mut sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || (vec![0; 12 * fr], Vec::new()),
            PairSums::default,
            |(scratch, local), sums, task, [part]| {
                let task = walk(rev, n, task);
                let (segment, q) = (task / quads, task % quads);
                publish(stream, &mut *part[0], local, |rows| {
                    for (i, out) in rows.chunks_exact_mut(row).enumerate() {
                        fold(out, segment, 4 * q + i);
                    }
                    let n = rows.len() / row;
                    self.add_quad(
                        sums,
                        scratch,
                        std::array::from_fn(|i| {
                            if i < n {
                                &rows[i * row..][..row]
                            } else {
                                &pads[segment * row..][..row]
                            }
                        }),
                        eq[to.m / 4 * segment + q],
                    );
                });
            },
            PairSums::merge,
        );
        self.add_padding_quad(&mut sums, to, pads, eq);
        TailMessage::Pair(self.finish_pair(&sums))
    }

    fn add_padding_quad(&self, sums: &mut PairSums, layout: Rows, pads: &[u64], eq: &[F]) {
        let (first, quads) = (layout.live.div_ceil(4), layout.m / 4);
        if first == quads {
            return;
        }
        let mut scratch = vec![0; 12 * factor_row::<W>()];
        for (pad, eq) in pads.chunks_exact(row::<W>()).zip(eq.chunks_exact(quads)) {
            self.add_quad(sums, &mut scratch, [pad; 4], eq[first..].iter().sum());
        }
    }
}

impl<F: Ext<W>, const W: usize> Round<'_, F, W> {
    /// lvm2 U-TAPE (T-P2's `fold_parts`): [`Round::fold`] over the two halves of the tape in one pass. Part `p`'s rows
    /// are `from[p].1` (one segment) from row `from[p].0` of `src`, its padding row `pads[p]`; the folded rows go to
    /// `dst` the same way, the parts one after another. `eqs[p]` weighs part `p`'s next pairs. Needs `to.m ≥ 2`.
    /// Returns the next round's values (the sum over both parts) and the new layout.
    #[allow(clippy::type_complexity)]
    fn fold_parts(
        &self,
        src: &[u64],
        from: [(usize, Rows); 2],
        dst: &mut [u64],
        pads: &[u64],
        challenge: &Element<W>,
        eqs: [&[F]; 2],
        rev: bool,
    ) -> ((F, F), [(usize, Rows); 2]) {
        let (row, fr) = (row::<W>(), factor_row::<W>());
        let t0 = from[0].1.next();
        let to = [(0, t0), (t0.len(), from[1].1.next())];
        assert!(to[0].1.m >= 2 && to[0].1.segments == 1 && to[1].1.segments == 1);
        let pairs = [to[0].1.live.div_ceil(2), to[1].1.live.div_ceil(2)];
        let pad = |p: usize| &pads[p * row..][..row];
        let (d0, rest) = dst.split_at_mut(to[0].1.live * row);
        let d1 = &mut rest[..to[1].1.live * row];
        let stream = streams((to[0].1.live + to[1].1.live) * row);
        let mut parts: Vec<&mut [u64]> = d0.chunks_mut(2 * row).chain(d1.chunks_mut(2 * row)).collect();
        // lvm2 BND-P: backwards when `rev` (the first fold, [`walk`]), from the rows `Tables` wrote last
        let n = parts.len();
        if rev {
            parts.reverse();
        }
        let mut sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || (vec![0u64; 4 * fr], Vec::new()),
            RoundSums::default,
            |(scratch, local), sums, task, [part]| {
                let task = walk(rev, n, task);
                let (p, t) = if task < pairs[0] { (0, task) } else { (1, task - pairs[0]) };
                let (fb, f) = from[p];
                publish(stream, &mut *part[0], local, |rows| {
                    let n = rows.len() / row;
                    for (i, out) in rows.chunks_exact_mut(row).enumerate() {
                        let r = 2 * (2 * t + i);
                        let (low, high) = (f.row(&src[fb * row..], pad(p), 0, r), f.row(&src[fb * row..], pad(p), 0, r + 1));
                        self.field.fold_row(out, low, high, challenge, BITS);
                    }
                    let high = if n == 2 { &rows[row..] } else { pad(p) };
                    self.add_pair(sums, scratch, &rows[..row], high, eqs[p][t]);
                });
            },
            RoundSums::merge,
        );
        for p in 0..2 {
            self.add_padding(&mut sums, to[p].1, pad(p), eqs[p]);
        }
        (self.finish(&sums), to)
    }
}

impl Layer<'_> {
    /// lvm2 U-TAPE: [`Layer::table_pair`] for the two halves (`self.upper`): each half's rows its own run of the table
    /// (`lives[p]` rows from row `bases[p]`), its padding row `pads[p]`, computed first; a hole's rows are its half's
    /// padding row. `eq` is over the block pairs then the half bit. The same sums as the whole batch's.
    fn table_pair_parts<F: Ext<W>, const W: usize>(
        &self,
        round: &Round<F, W>,
        challenges: &[F],
        eq: &[F],
        m: usize,
        table: &mut [u64],
        pads: &mut [u64],
    ) -> RoundPair<F> {
        let (field, row, fr) = (round.field, row::<W>(), factor_row::<W>());
        assert!(self.upper.is_some() && m >= 4);
        let fold: Vec<Element<W>> = F::eq_table(challenges).iter().map(|&e| field.to_poly(e)).collect();
        let fold = Fold::<HALF_BYTES, W>::new(field, &fold);
        pads.fill(0);
        {
            let (mut recompute, mut wide) = (Recompute::new(), Fold::<HALF_BYTES, W>::scratch());
            for p in 0..2 {
                let w = self.part(p);
                if w.written() < w.shape.n_blocks() {
                    let block = w.state(&mut recompute, self.rounds[p], w.written());
                    fold.rows(field, block, &mut pads[p * row..][..row], &mut wide);
                }
            }
        }
        let lives = [2 * self.part(0).written(), 2 * self.part(1).written()];
        let quads = [lives[0].div_ceil(4), lives[1].div_ceil(4)];
        let (t0, rest) = table.split_at_mut(lives[0] * row);
        let t1 = &mut rest[..lives[1] * row];
        let mut parts: Vec<&mut [u64]> = t0.chunks_mut(4 * row).chain(t1.chunks_mut(4 * row)).collect();
        let pads = &*pads;
        let half = m / 4;
        let stream = streams((lives[0] + lives[1]) * row);
        let mut sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || (vec![0u64; 12 * fr], Fold::<HALF_BYTES, W>::scratch(), Recompute::new(), Vec::new()),
            PairSums::default,
            |(scratch, wide, recompute, local), sums, task, [part]| {
                let (p, q) = if task < quads[0] { (0, task) } else { (1, task - quads[0]) };
                let w = self.part(p);
                let pad = &pads[p * row..][..row];
                publish(stream, &mut *part[0], local, |rows| {
                    for (i, rows) in rows.chunks_mut(2 * row).enumerate() {
                        let g = 2 * q + i;
                        if w.holes().binary_search(&g).is_ok() {
                            for out in rows.chunks_exact_mut(row) {
                                out.copy_from_slice(pad);
                            }
                        } else {
                            let block = w.state(recompute, self.rounds[p], g);
                            fold.rows(field, block, rows, wide);
                        }
                    }
                    let n = rows.len() / row;
                    round.add_quad(sums, scratch, std::array::from_fn(|i| if i < n { &rows[i * row..][..row] } else { pad }), eq[half * p + q]);
                });
            },
            PairSums::merge,
        );
        for p in 0..2 {
            let layout = Rows { m, live: lives[p], segments: 1, width: row };
            round.add_padding_quad(&mut sums, layout, &pads[p * row..][..row], &eq[half * p..][..half]);
        }
        round.finish_pair(&sums)
    }
}

impl<F: Ext<W>, const W: usize> Round<'_, F, W> {
    /// lvm2 U-TAPE: [`Round::fold_pair`] over the two halves, each its own run of rows (`from[p]`: first row, layout of
    /// one segment) and padding row; `eqs[p]` weighs part `p`'s next quads. Needs `to.m ≥ 4`. Returns the next pair
    /// message and the new layouts.
    #[allow(clippy::type_complexity)]
    fn fold_pair_parts(
        &self,
        src: &[u64],
        from: [(usize, Rows); 2],
        dst: &mut [u64],
        pads: &[u64],
        challenges: &[Element<W>; 2],
        eqs: [&[F]; 2],
        rev: bool,
    ) -> (RoundPair<F>, [(usize, Rows); 2]) {
        let (row, fr) = (row::<W>(), factor_row::<W>());
        let t0 = from[0].1.next().next();
        let to = [(0, t0), (t0.len(), from[1].1.next().next())];
        assert!(to[0].1.m >= 4 && to[0].1.segments == 1 && to[1].1.segments == 1);
        let challenges = [challenges[0], challenges[1], self.field.mul(&challenges[0], &challenges[1])];
        let quads = [to[0].1.live.div_ceil(4), to[1].1.live.div_ceil(4)];
        let pad = |p: usize| &pads[p * row..][..row];
        let (d0, rest) = dst.split_at_mut(to[0].1.live * row);
        let d1 = &mut rest[..to[1].1.live * row];
        let stream = streams((to[0].1.live + to[1].1.live) * row);
        let mut parts: Vec<&mut [u64]> = d0.chunks_mut(4 * row).chain(d1.chunks_mut(4 * row)).collect();
        // lvm2 BND-P: backwards when `rev` (the first fold, [`walk`]), from the rows `Tables` wrote last
        let n = parts.len();
        if rev {
            parts.reverse();
        }
        let mut sums = crate::lv::parallel::map_reduce_chunks_mut(
            [&mut parts[..]],
            [1],
            || (vec![0; 12 * fr], Vec::new()),
            PairSums::default,
            |(scratch, local), sums, task, [part]| {
                let task = walk(rev, n, task);
                let (p, q) = if task < quads[0] { (0, task) } else { (1, task - quads[0]) };
                let (fb, f) = from[p];
                publish(stream, &mut *part[0], local, |rows| {
                    for (i, out) in rows.chunks_exact_mut(row).enumerate() {
                        let r = 4 * q + i;
                        self.field.fold_quad(out, std::array::from_fn(|k| f.row(&src[fb * row..], pad(p), 0, 4 * r + k)), &challenges, BITS);
                    }
                    let n = rows.len() / row;
                    self.add_quad(sums, scratch, std::array::from_fn(|i| if i < n { &rows[i * row..][..row] } else { pad(p) }), eqs[p][q]);
                });
            },
            PairSums::merge,
        );
        for p in 0..2 {
            self.add_padding_quad(&mut sums, to[p].1, pad(p), eqs[p]);
        }
        (self.finish_pair(&sums), to)
    }
}

/// A round of the sumcheck over bit positions, on small tables in the standard basis: the
/// coefficients of `sum_j w (kappa t0 + (kappa + t1) t2)` in the variable being bound.
fn local_round<F: Ext<W>, const W: usize>(w: &[F], t: &[Vec<F>; 3], kappa: F) -> [F; 4] {
    let mut h = [F::ZERO; 4];
    for i in 0..w.len() / 2 {
        let line = |v: &[F]| (v[2 * i], v[2 * i] + v[2 * i + 1]);
        let (w, t0, t1, t2) = (line(w), line(&t[0]), line(&t[1]), line(&t[2]));
        let u = (kappa + t1.0, t1.1);
        let a = [
            kappa * t0.0 + u.0 * t2.0,
            kappa * t0.1 + u.0 * t2.1 + u.1 * t2.0,
            u.1 * t2.1,
        ];
        h[0] += w.0 * a[0];
        h[1] += w.0 * a[1] + w.1 * a[0];
        h[2] += w.0 * a[2] + w.1 * a[1];
        h[3] += w.1 * a[2];
    }
    h
}

/// Bind the low variable of a table: `lo + t (lo + hi)` pairwise (`open::fold` at width one, any field).
fn fold<F: Ext<W>, const W: usize>(table: &[F], challenge: F) -> Vec<F> {
    table.chunks_exact(2).map(|p| p[0] + challenge * (p[0] + p[1])).collect()
}

/// The table the rounds after the bit-level ones fold, and their output buffer: reused
/// from layer to layer (`W` words an entry).
pub struct Scratch<const W: usize> {
    table: Vec<u64>,
    /// Each segment's padding row.
    pads: Vec<u64>,
    /// lvm2 SLF-PR: the written blocks' differences, from `Skip` to `Groups` ([`spill_differences`]); sized at first use.
    diffs: Vec<u64>,
}

impl<const W: usize> Scratch<W> {
    /// lvm2 SLF-PR: the differences buffer for `layer`'s written tasks, or an empty one when `Groups` reads the blocks.
    fn diffs<'d>(diffs: &'d mut Vec<u64>, layer: &Layer<'_>) -> &'d mut [u64] {
        if !compact_groups() {
            return &mut [];
        }
        let need = layer.written_tasks().len() * DIFF_WORDS;
        if diffs.len() < need {
            diffs.resize(need, 0);
        }
        &mut diffs[..need]
    }
}

impl<const W: usize> Scratch<W> {
    /// lvm2 U-TAPE: the scratch of [`prove_layer_halves`] for halves of shape `half`: the whole tape's table (the
    /// single-round tail), and a padding row per half.
    pub fn new_halves(half: Shape) -> Self {
        let row = row::<W>();
        let rows = 2usize << (half.y_vars() - PACK_VARS + 1);
        Self { table: vec![0u64; rows * row + rows * row / 2], pads: vec![0u64; 2 * row], diffs: Vec::new() }
    }
    pub fn new(shape: Shape) -> Self {
        let row = row::<W>();
        let rows = 1usize << (shape.y_vars() - PACK_VARS + 1);
        let divisor = if PAIRED_TAIL && shape.n_blocks() >= 2 { 4 } else { 2 };
        let table = vec![0u64; rows * row + rows * row / divisor];
        let pads = vec![0u64; row << shape.seg_log()];
        Self { table, pads, diffs: Vec::new() }
    }
}

/// Prove one layer, as `crates/verifier`'s `keccak.rs` checks it: a claim on the states `step`
/// layers below the outputs becomes one on the states a layer further down. (lvm2 E2-K: over E3 or E2.)
pub fn prove_layer<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    witness: &Witness,
    scratch: &mut Scratch<W>,
    step: usize,
    claim: &Claim<F>,
) -> Claim<F> {
    let shape = witness.shape;
    let layer = Layer::new(witness, (0..shape.segments()).map(|segment| shape.round(segment, step)).collect(), None);

    let per_pack =
        crate::lv::tracing::info_span!(tag::<W>("Product", "Product/E2")).in_scope(|| layer.pack_products(claim));
    let pack_weights = F::eq_table(&claim.point[..PACK_VARS]);
    let mut product: [F; PROD_BITS] =
        std::array::from_fn(|c| (0..PACKS).map(|q| pack_weights[q] * per_pack[q][c]).sum());
    w32_tamper_u(step, &claim.mu, &mut product);
    ps.add_ext(&product);
    let s = ps.challenge::<F, W>(Grp::C104);
    let kappa = mu_at::<F, W>(s).iter().sum();
    let mut value = F::poly_eval(&product, s);
    let field = crate::lv::tracing::info_span!("Field")
        .in_scope(|| PowerField::<F, W>::new(s).expect("the challenge lies in no proper subfield"));
    // lvm2 R9-KG: the weights in the power basis, once for `Skip` and the round tables.
    let polys: Vec<Element<W>> = claim.weights.iter().map(|&w| field.to_poly(w)).collect();

    // Keep the fourth variable binary, summing over the block's halves.
    let binary: [[F; GROUP]; 2] = std::array::from_fn(|side| {
        std::array::from_fn(|q| {
            let half = claim.point[SKIP + 1];
            let q = GROUP * side + q;
            (F::ONE + half) * F::poly_eval(&per_pack[q], s) + half * F::poly_eval(&per_pack[2 * GROUP + q], s)
        })
    });
    let diffs = Scratch::<W>::diffs(&mut scratch.diffs, &layer);
    let mut sums = crate::lv::tracing::info_span!(tag::<W>("Skip", "Skip/E2"))
        .in_scope(|| layer.skip_sums(claim, &field, &polys, &binary, diffs));
    let side_weights = [F::ONE + claim.point[SKIP], claim.point[SKIP]];
    let mut scale = F::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for i in 0..SKIP {
        let later = F::eq_table(&claim.point[i + 1..SKIP]);
        let mut h = [F::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, h) in h.iter_mut().enumerate() {
                *h += eq
                    * (side_weights[0] * sums[0][d + 3 * ternary(b)] + side_weights[1] * sums[1][d + 3 * ternary(b)]);
            }
        }
        let coeffs = [scale * h[0], scale * (h[0] + h[1] + h[2]), scale * h[2]];
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        sums = sums.map(|sums| {
            sums.as_chunks::<3>()
                .0
                .iter()
                .map(|v| v[0] + challenge * (v[0] + v[1]) + (challenge.square() + challenge) * v[2])
                .collect()
        });
    }

    let round = crate::lv::tracing::info_span!("RoundNew").in_scope(|| Round::new(&field, claim, &polys, kappa));
    let blocks = F::eq_table(&claim.point[PACK_VARS..]);
    let infinity = crate::lv::tracing::info_span!(tag::<W>("Groups", "Groups/E2"))
        .in_scope(|| layer.group_infinity(&round, &point, &claim.point, diffs));
    let coeffs = [
        scale * sums[0][0],
        scale * (sums[0][0] + sums[1][0] + infinity),
        scale * infinity,
    ];
    bind(ps, &coeffs, claim.point[SKIP], &mut value, &mut scale, &mut point);

    // The blocks and segments, on a table in the power basis. Each pass over it writes the rows
    // of one round and sums that round's values over them.
    let row = row::<W>();
    let mut layout = Rows {
        m: 2 * shape.n_blocks(),
        live: 2 * witness.written(),
        segments: 1 << shape.seg_log(),
        width: row,
    };
    let (mut src, mut dst) = scratch.table.split_at_mut(layout.m * layout.segments * row);
    let pads = &mut scratch.pads;
    let mut message = crate::lv::tracing::info_span!(tag::<W>("Tables", "Tables/E2")).in_scope(|| {
        if layout.paired() {
            let eq = F::eq_table(&claim.point[PACK_VARS + 1..]);
            TailMessage::Pair(layer.table_pair(&round, &point, &eq, layout, src, pads))
        } else {
            let (zero, infinity) = layer.table(&round, &point, &blocks, layout, src, pads);
            TailMessage::Single(zero, infinity)
        }
    });
    let tail = crate::lv::tracing::info_span!(tag::<W>("Tail", "Tail/E2")).entered();
    let mut i = PACK_VARS - 1;
    while i < claim.point.len() {
        // lvm2 BND-P: the first fold walks backwards ([`walk`])
        let rev = i == PACK_VARS - 1;
        let values = message.first(claim.point.get(i + 1).copied().unwrap_or(F::ZERO));
        let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        match message {
            TailMessage::Pair(pair) => {
                let values = pair.second(challenge);
                let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i + 1]);
                let second = bind(ps, &coeffs, claim.point[i + 1], &mut value, &mut scale, &mut point);
                let to = layout.next().next();
                i += 2;
                let skipped = if to.paired() { 2 } else { 1 };
                let later = F::eq_table(claim.point.get(i + skipped..).unwrap_or(&[]));
                message = round.fold_pair(
                    src,
                    layout,
                    dst,
                    pads,
                    &[field.to_poly(challenge), field.to_poly(second)],
                    &later,
                    rev,
                );
                layout = to;
            }
            TailMessage::Single(_, _) => {
                let later = F::eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
                let (zero, infinity) = round.fold(src, layout, dst, pads, &field.to_poly(challenge), &later, rev);
                message = TailMessage::Single(zero, infinity);
                layout = layout.next();
                i += 1;
            }
        }
        (src, dst) = (dst, src);
    }
    let table = &src[..row];
    drop(tail);

    // The bit positions, in the standard basis.
    let local_span = crate::lv::tracing::info_span!("Local").entered();
    let t0: Vec<F> = (0..BITS).map(|j| field.to_field(&get(table, BITS, j))).collect();
    let shift = |k: usize| -> Vec<F> { (0..BITS).map(|j| t0[along(j, k)]).collect() };
    let (t1, t2) = (shift(1), shift(2));
    let (local, t) = local_rounds(ps, claim.weights.clone(), [t0, t1, t2], kappa, scale);
    ps.add_ext(&t);
    let beta = ps.challenge::<F, W>(Grp::C2);
    let out = Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu: mu_at::<F, W>(s),
        point,
        weights: linear_transpose(&chi_weights(&F::eq_table(&local), beta)),
    };
    drop(local_span);
    out
}

/// lvm2 U-TAPE (T-P2's `prove_layer_halves` on this tree's passes): [`prove_layer`] for one segment of
/// `2^(n_log + 1)` instances held as two half-batches of the same shape (`halves[h]` is instances `h·2^n_log + i`),
/// each a written prefix and leanVM's padding block. The claim's last point coordinate is the half bit, which every
/// pass treats as leanVM treats a segment variable ([`Layer::upper`]): one task list over both halves' blocks per
/// pass, each half's rows its own run of the table. The tail is single-round ([`Round::fold_parts`]; the paired tail
/// is leanVM's layer's only) and the halves meet at the last pack round. The bytes are [`prove_layer`]'s on the
/// whole batch (`LVM_PGATE=dense`).
pub fn prove_layer_halves<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    halves: [&Witness; 2],
    scratch: &mut Scratch<W>,
    step: usize,
    claim: &Claim<F>,
) -> Claim<F> {
    let shape = halves[0].shape;
    assert_eq!(halves[1].shape, shape, "two halves of one shape");
    assert_eq!(shape.segments(), 1, "the tape is one segment");
    let hv = shape.y_vars();
    assert_eq!(claim.point.len(), hv + 1, "the claim's point: a half's packs, then the half bit");
    assert!(hv >= PACK_VARS + 1, "a half has at least two blocks");
    let round_no = shape.round(0, step);
    let layer = Layer::new(halves[0], vec![round_no, round_no], Some(halves[1]));

    let per_pack =
        crate::lv::tracing::info_span!(tag::<W>("Product", "Product/E2")).in_scope(|| layer.pack_products(claim));
    let pack_weights = F::eq_table(&claim.point[..PACK_VARS]);
    let mut product: [F; PROD_BITS] =
        std::array::from_fn(|c| (0..PACKS).map(|q| pack_weights[q] * per_pack[q][c]).sum());
    w32_tamper_u(step, &claim.mu, &mut product);
    ps.add_ext(&product);
    let s = ps.challenge::<F, W>(Grp::C104);
    let kappa = mu_at::<F, W>(s).iter().sum();
    let mut value = F::poly_eval(&product, s);
    let field = crate::lv::tracing::info_span!("Field")
        .in_scope(|| PowerField::<F, W>::new(s).expect("the challenge lies in no proper subfield"));
    let polys: Vec<Element<W>> = claim.weights.iter().map(|&w| field.to_poly(w)).collect();

    let binary: [[F; GROUP]; 2] = std::array::from_fn(|side| {
        std::array::from_fn(|q| {
            let half = claim.point[SKIP + 1];
            let q = GROUP * side + q;
            (F::ONE + half) * F::poly_eval(&per_pack[q], s) + half * F::poly_eval(&per_pack[2 * GROUP + q], s)
        })
    });
    let diffs = Scratch::<W>::diffs(&mut scratch.diffs, &layer);
    let mut sums = crate::lv::tracing::info_span!(tag::<W>("Skip", "Skip/E2"))
        .in_scope(|| layer.skip_sums(claim, &field, &polys, &binary, diffs));
    let side_weights = [F::ONE + claim.point[SKIP], claim.point[SKIP]];
    let mut scale = F::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for i in 0..SKIP {
        let later = F::eq_table(&claim.point[i + 1..SKIP]);
        let mut h = [F::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, h) in h.iter_mut().enumerate() {
                *h += eq
                    * (side_weights[0] * sums[0][d + 3 * ternary(b)] + side_weights[1] * sums[1][d + 3 * ternary(b)]);
            }
        }
        let coeffs = [scale * h[0], scale * (h[0] + h[1] + h[2]), scale * h[2]];
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        sums = sums.map(|sums| {
            sums.as_chunks::<3>()
                .0
                .iter()
                .map(|v| v[0] + challenge * (v[0] + v[1]) + (challenge.square() + challenge) * v[2])
                .collect()
        });
    }

    let round = crate::lv::tracing::info_span!("RoundNew").in_scope(|| Round::new(&field, claim, &polys, kappa));
    let blocks = F::eq_table(&claim.point[PACK_VARS..]);
    let infinity = crate::lv::tracing::info_span!(tag::<W>("Groups", "Groups/E2"))
        .in_scope(|| layer.group_infinity(&round, &point, &claim.point, diffs));
    let coeffs = [
        scale * sums[0][0],
        scale * (sums[0][0] + sums[1][0] + infinity),
        scale * infinity,
    ];
    bind(ps, &coeffs, claim.point[SKIP], &mut value, &mut scale, &mut point);

    // The two halves' tables, one run of rows each in one buffer (lower first), their padding rows in `pads`.
    let row = row::<W>();
    let m0 = 2 * shape.n_blocks();
    let lives = [2 * halves[0].written(), 2 * halves[1].written()];
    let layout = Rows { m: m0, live: lives[0], segments: 2, width: row };
    let (mut src, mut dst) = scratch.table.split_at_mut(2 * m0 * row);
    let pads = &mut scratch.pads;
    assert!(pads.len() >= 2 * row, "a padding row per half");
    let mut from = [(0, Rows { m: m0, live: lives[0], segments: 1, width: row }), (lives[0], Rows { m: m0, live: lives[1], segments: 1, width: row })];
    let mut last = vec![0u64; 3 * row];
    let fr = factor_row::<W>();
    // the paired tail (as `prove_layer`'s, with AVX-512): two variables a pass while a half has at least 4 rows; a half
    // of `4^k` rows ends at one row, and the merge round's one pair is the halves' rows
    if PAIRED_TAIL && m0.trailing_zeros() % 2 == 0 && m0 >= 4 && std::env::var_os("LVM_UT_NOPAIR").is_none() {
        let mut message = crate::lv::tracing::info_span!(tag::<W>("Tables", "Tables/E2")).in_scope(|| {
            let eq = F::eq_table(&claim.point[PACK_VARS + 1..]);
            TailMessage::Pair(layer.table_pair_parts(&round, &point, &eq, m0, src, pads))
        });
        let tail = crate::lv::tracing::info_span!(tag::<W>("Tail", "Tail/E2")).entered();
        let mut i = PACK_VARS - 1;
        while i <= hv {
            // lvm2 BND-P: the first fold walks backwards ([`walk`])
            let rev = i == PACK_VARS - 1;
            let values = message.first(claim.point.get(i + 1).copied().unwrap_or(F::ZERO));
            let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
            let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
            match message {
                TailMessage::Pair(pair) => {
                    let values = pair.second(challenge);
                    let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i + 1]);
                    let second = bind(ps, &coeffs, claim.point[i + 1], &mut value, &mut scale, &mut point);
                    i += 2;
                    let ch = [field.to_poly(challenge), field.to_poly(second)];
                    if from[0].1.next().next().m >= 4 {
                        let later = F::eq_table(&claim.point[i + 2..]);
                        let half = later.len() / 2;
                        let (pair, to) = round.fold_pair_parts(src, from, dst, pads, &ch, [&later[..half], &later[half..]], rev);
                        message = TailMessage::Pair(pair);
                        from = to;
                        (src, dst) = (dst, src);
                    } else {
                        // each half down to one row (from 4); the merge round's one pair is the two
                        assert_eq!((from[0].1.m, i), (4, hv), "a half of 4^k rows");
                        let c3 = [ch[0], ch[1], field.mul(&ch[0], &ch[1])];
                        let (l0, rest) = last.split_at_mut(row);
                        for (p, out) in [l0, &mut rest[..row]].into_iter().enumerate() {
                            let ((fb, f), pad) = (from[p], &pads[p * row..][..row]);
                            field.fold_quad(out, std::array::from_fn(|k| f.row(&src[fb * row..], pad, 0, k)), &c3, BITS);
                        }
                        let mut sums = RoundSums::default();
                        let mut sc = vec![0u64; 4 * fr];
                        round.add_pair(&mut sums, &mut sc, &last[..row], &last[row..2 * row], F::ONE);
                        let (zero, infinity) = round.finish(&sums);
                        message = TailMessage::Single(zero, infinity);
                    }
                }
                TailMessage::Single(_, _) => {
                    let (lo, hi) = last.split_at_mut(2 * row);
                    field.fold_row(hi, &lo[..row], &lo[row..], &field.to_poly(challenge), BITS);
                    i += 1;
                }
            }
        }
        drop(tail);
    } else {
    let mut values = crate::lv::tracing::info_span!(tag::<W>("Tables", "Tables/E2"))
        .in_scope(|| layer.table(&round, &point, &blocks, layout, src, pads));
    let tail = crate::lv::tracing::info_span!(tag::<W>("Tail", "Tail/E2")).entered();
    for i in PACK_VARS - 1..=hv {
        let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        let ch = field.to_poly(challenge);
        if i + 1 < hv {
            let later = F::eq_table(&claim.point[i + 2..]);
            let half = later.len() / 2;
            // lvm2 BND-P: the first fold walks backwards ([`walk`])
            let rev = i == PACK_VARS - 1;
            let (v, to) = round.fold_parts(src, from, dst, pads, &ch, [&later[..half], &later[half..]], rev);
            values = v;
            from = to;
            (src, dst) = (dst, src);
        } else if i + 1 == hv {
            // each half down to one row; the merge round's one pair is the two
            let (l0, rest) = last.split_at_mut(row);
            for (p, out) in [l0, &mut rest[..row]].into_iter().enumerate() {
                let ((fb, f), pad) = (from[p], &pads[p * row..][..row]);
                field.fold_row(out, f.row(&src[fb * row..], pad, 0, 0), f.row(&src[fb * row..], pad, 0, 1), &ch, BITS);
            }
            let mut sums = RoundSums::default();
            let mut sc = vec![0u64; 4 * fr];
            round.add_pair(&mut sums, &mut sc, &last[..row], &last[row..2 * row], F::ONE);
            values = round.finish(&sums);
        } else {
            let (lo, hi) = last.split_at_mut(2 * row);
            field.fold_row(hi, &lo[..row], &lo[row..], &ch, BITS);
        }
    }
    drop(tail);
    }
    let table = &last[2 * row..];

    let local_span = crate::lv::tracing::info_span!("Local").entered();
    let t0: Vec<F> = (0..BITS).map(|j| field.to_field(&get(table, BITS, j))).collect();
    let shift = |k: usize| -> Vec<F> { (0..BITS).map(|j| t0[along(j, k)]).collect() };
    let (t1, t2) = (shift(1), shift(2));
    let (local, t) = local_rounds(ps, claim.weights.clone(), [t0, t1, t2], kappa, scale);
    ps.add_ext(&t);
    let beta = ps.challenge::<F, W>(Grp::C2);
    let out = Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu: mu_at::<F, W>(s),
        point,
        weights: linear_transpose(&chi_weights(&F::eq_table(&local), beta)),
    };
    drop(local_span);
    out
}

/// `v` as `F192` values when `F` is `F192` (E3), for the eight-wide arm of [`local_rounds`].
#[inline(always)]
fn as_e3<F: Ext<W>, const W: usize>(v: &[F]) -> Option<&[F192]> {
    (std::any::TypeId::of::<F>() == std::any::TypeId::of::<F192>())
        // SAFETY: `F` is `F192`, so the slice's type is unchanged.
        .then(|| unsafe { std::slice::from_raw_parts(v.as_ptr().cast::<F192>(), v.len()) })
}

/// `x` as an `F192` when `F` is `F192` (E3).
#[inline(always)]
fn to_e3<F: Ext<W>, const W: usize>(x: F) -> F192 {
    debug_assert!(std::any::TypeId::of::<F>() == std::any::TypeId::of::<F192>());
    F192::from_limbs(std::array::from_fn(|k| if k < W { x.to_limbs()[k] } else { 0 }))
}

/// An `F192` back as `F` when `F` is `F192` (E3).
#[inline(always)]
fn from_e3<F: Ext<W>, const W: usize>(x: F192) -> F {
    let l = x.to_limbs();
    F::from_limbs(std::array::from_fn(|k| l[k]))
}

/// `v` as `F128` values when `F` is `F128` (E2), for the four-wide arm of [`local_rounds`] (lvm2 PFAST-K).
#[inline(always)]
fn as_e2<F: Ext<W>, const W: usize>(v: &[F]) -> Option<&[F128]> {
    (std::any::TypeId::of::<F>() == std::any::TypeId::of::<F128>())
        // SAFETY: `F` is `F128`, so the slice's type is unchanged.
        .then(|| unsafe { std::slice::from_raw_parts(v.as_ptr().cast::<F128>(), v.len()) })
}

/// `x` as an `F128` when `F` is `F128` (E2).
#[inline(always)]
fn to_e2<F: Ext<W>, const W: usize>(x: F) -> F128 {
    debug_assert!(std::any::TypeId::of::<F>() == std::any::TypeId::of::<F128>());
    let l = x.to_limbs();
    F128::new(l[0], l[1 % W])
}

/// An `F128` back as `F` when `F` is `F128` (E2).
#[inline(always)]
fn from_e2<F: Ext<W>, const W: usize>(x: F128) -> F {
    F::from_limbs(std::array::from_fn(|k| [x.c0, x.c1][k % 2]))
}

/// lvm2 R9-KG: the `LOCAL_VARS` rounds of the sumcheck over bit positions. It sends and binds what
/// leanVM's loop of [`local_round`] and `fold` over the `2^LOCAL_VARS` cube does, with the same field
/// values (the field is exact, so neither the order of the sums nor where they reduce changes a
/// value). Every table is zero from position `BITS` on, and a fold keeps it zero from `live` on, so
/// only the pairs below `live` are summed and folded, eight at a time (`F192x8`, E3 only), and the
/// sums accumulate unreduced. It stays on
/// the calling thread: between two transcript round trips a pool dispatch costs about what it saves.
/// Returns the challenges and the three tables' last values. (lvm2 E2F-P: generic over [`Ext`]; lvm2
/// PFAST-K: at E2 four pairs at a time, `E2x4`.)
/// W32-P (dev, `LVM_W32_TAMPER`): send a wrong `U` at layer `L`, the rest of the proof following it (the transcript
/// takes the tampered coefficients): `u:L:C` adds one to coefficient `C` (the projected check must fail); `uk:L` adds
/// `(P1, P0, 0, ...)`, `Pc = sum over k with PROJ_k bit c of mu_k`, which leaves the projection unchanged (the claim
/// on `U(s)`, so the sumcheck, must fail).
fn w32_tamper_u<F: Ext<W>, const W: usize>(step: usize, mu: &[F; crate::lv::keccak_gkr::rmfe::PACK], product: &mut [F; PROD_BITS]) {
    let Ok(t) = std::env::var("LVM_W32_TAMPER") else { return };
    let f: Vec<&str> = t.split(':').collect();
    let layer = |i: usize| f.get(i).and_then(|v| v.parse::<usize>().ok());
    let pm = |c: usize| -> F {
        (0..crate::lv::keccak_gkr::rmfe::PACK).filter(|&k| crate::lv::keccak_gkr::rmfe::RMFE.proj[k] >> c & 1 == 1).map(|k| mu[k]).sum()
    };
    match (f.first().copied(), layer(1)) {
        (Some("u"), Some(l)) if l == step => {
            let c = layer(2).unwrap_or(0);
            product[c] += F::ONE;
            eprintln!("lvm: LVM_W32_TAMPER={t}: U coefficient {c} of layer {l} + 1");
        }
        (Some("uk"), Some(l)) if l == step => {
            let (p0, p1) = (pm(0), pm(1));
            product[0] += p1;
            product[1] += p0;
            eprintln!("lvm: LVM_W32_TAMPER={t}: U of layer {l} + (P1, P0, 0..) (projection kept)");
        }
        _ => {}
    }
}

/// lvm2 W32-P: `E2x4` is AVX-512F + VPCLMULQDQ (every tier mounts this tree now).
const E2X4: bool = cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"));

fn local_rounds<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    mut w: Vec<F>,
    mut t: [Vec<F>; 3],
    kappa: F,
    scale: F,
) -> (Vec<F>, [F; 3]) {
    assert!(w.len() == BITS && t.iter().all(|v| v.len() == BITS));
    let e3 = as_e3(&w).is_some();
    let e2 = as_e2(&w).is_some();
    let mut live = BITS;
    let mut local = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        let pairs = live.div_ceil(2);
        // Entry pair `i` of a table as `(v(0), v(0) + v(1))`, the entry past `live` being zero.
        let line = |v: &[F], i: usize| {
            let lo = v[2 * i];
            let hi = if 2 * i + 1 < live { v[2 * i + 1] } else { F::ZERO };
            (lo, lo + hi)
        };
        // Eight pairs at a time (`F192x8`) while sixteen live entries remain, then one at a time. lvm2 PFAST-K: at
        // E2 four pairs at a time (`E2x4`) while eight live entries remain.
        let wide = if e3 {
            8 * (live / 16)
        } else if e2 && E2X4 {
            4 * (live / 8)
        } else {
            0
        };
        let mut h8 = [Prod8::ZERO; 4];
        // (`E2x4U::zero` is a zmm instruction: only where the four-wide arm runs)
        // SAFETY: an `E2x4U` is plain data, all-zero bytes being zero.
        let mut h4: [E2x4U; 4] = if wide > 0 && e2 { [E2x4U::zero(); 4] } else { unsafe { core::mem::zeroed() } };
        if wide > 0 && e2 {
            let (w, t) = (as_e2(&w).expect("E2"), t.each_ref().map(|v| as_e2(v).expect("E2")));
            let k4 = E2x4::splat(to_e2(kappa));
            let line4 = |v: &[F128], g: usize| {
                let (lo, hi) = E2x4::even_odd(E2x4::load(&v[8 * g..]), E2x4::load(&v[8 * g + 4..]));
                (lo, lo.add(hi))
            };
            for g in 0..wide / 4 {
                let (w, t0, t1, t2) = (line4(w, g), line4(t[0], g), line4(t[1], g), line4(t[2], g));
                let u = (k4.add(t1.0), t1.1);
                let a0 = k4.mul_unreduced(t0.0).xor(u.0.mul_unreduced(t2.0));
                let a1 = k4.mul_unreduced(t0.1).xor(u.0.mul_unreduced(t2.1)).xor(u.1.mul_unreduced(t2.0));
                let a = [a0.reduce(), a1.reduce(), u.1.mul(t2.1)];
                h4[0] = h4[0].xor(w.0.mul_unreduced(a[0]));
                h4[1] = h4[1].xor(w.0.mul_unreduced(a[1])).xor(w.1.mul_unreduced(a[0]));
                h4[2] = h4[2].xor(w.0.mul_unreduced(a[2])).xor(w.1.mul_unreduced(a[1]));
                h4[3] = h4[3].xor(w.1.mul_unreduced(a[2]));
            }
        }
        if wide > 0 && e3 {
            let (w, t) = (as_e3(&w).expect("E3"), t.each_ref().map(|v| as_e3(v).expect("E3")));
            let k8 = F192x8::splat(to_e3(kappa));
            let line8 = |v: &[F192], g: usize| {
                let at = |o: usize| F192x8::from_array(v[16 * g + o..][..8].try_into().expect("eight"));
                let (lo, hi) = F192x8::even_odd(at(0), at(8));
                (lo, lo + hi)
            };
            for g in 0..wide / 8 {
                let (w, t0, t1, t2) = (line8(w, g), line8(t[0], g), line8(t[1], g), line8(t[2], g));
                let u = (k8 + t1.0, t1.1);
                let mut a0 = k8.mul_unreduced(t0.0);
                a0 ^= u.0.mul_unreduced(t2.0);
                let mut a1 = k8.mul_unreduced(t0.1);
                a1 ^= u.0.mul_unreduced(t2.1);
                a1 ^= u.1.mul_unreduced(t2.0);
                let a = [a0.reduce_lanes(), a1.reduce_lanes(), u.1 * t2.1];
                h8[0] ^= w.0.mul_unreduced(a[0]);
                h8[1] ^= w.0.mul_unreduced(a[1]);
                h8[1] ^= w.1.mul_unreduced(a[0]);
                h8[2] ^= w.0.mul_unreduced(a[2]);
                h8[2] ^= w.1.mul_unreduced(a[1]);
                h8[3] ^= w.1.mul_unreduced(a[2]);
            }
        }
        let mut h = [F::Unreduced::ZERO; 4];
        for i in wide..pairs {
            let (w, t0, t1, t2) = (line(&w, i), line(&t[0], i), line(&t[1], i), line(&t[2], i));
            let u = (kappa + t1.0, t1.1);
            let a = [
                (kappa.mul_unreduced(t0.0) ^ u.0.mul_unreduced(t2.0)).reduce(),
                (kappa.mul_unreduced(t0.1) ^ u.0.mul_unreduced(t2.1) ^ u.1.mul_unreduced(t2.0)).reduce(),
                u.1 * t2.1,
            ];
            h[0] ^= w.0.mul_unreduced(a[0]);
            h[1] ^= w.0.mul_unreduced(a[1]) ^ w.1.mul_unreduced(a[0]);
            h[2] ^= w.0.mul_unreduced(a[2]) ^ w.1.mul_unreduced(a[1]);
            h[3] ^= w.1.mul_unreduced(a[2]);
        }
        let coeffs: [F; 4] = std::array::from_fn(|d| {
            let wide_sum = if wide > 0 && e3 {
                from_e3::<F, W>(h8[d].reduce())
            } else if wide > 0 && e2 {
                from_e2::<F, W>(h4[d].sum().reduce())
            } else {
                F::ZERO
            };
            scale * (wide_sum + h[d].reduce())
        });
        ps.add_round_poly_ext(&coeffs, false);
        let challenge = ps.challenge::<F, W>(Grp::C3);
        local.push(challenge);
        // `fold(v, 1, challenge)` on the live pairs.
        let fold = |v: &[F]| -> Vec<F> {
            let mut out = Vec::with_capacity(pairs);
            if wide > 0 && e2 {
                let v2 = as_e2(v).expect("E2");
                let c4 = E2x4::splat(to_e2(challenge));
                for g in 0..wide / 4 {
                    let (lo, hi) = E2x4::even_odd(E2x4::load(&v2[8 * g..]), E2x4::load(&v2[8 * g + 4..]));
                    out.extend(lo.add(c4.mul(lo.add(hi))).to_array().map(from_e2::<F, W>));
                }
            }
            if wide > 0 && e3 {
                let v3 = as_e3(v).expect("E3");
                let c8 = F192x8::splat(to_e3(challenge));
                for g in 0..wide / 8 {
                    let at = |o: usize| F192x8::from_array(v3[16 * g + o..][..8].try_into().expect("eight"));
                    let (lo, hi) = F192x8::even_odd(at(0), at(8));
                    out.extend((lo + c8 * (lo + hi)).to_array().map(from_e3::<F, W>));
                }
            }
            out.extend((wide..pairs).map(|i| {
                let (lo, sum) = line(v, i);
                lo + challenge * sum
            }));
            out
        };
        (w, t) = (fold(&w), [fold(&t[0]), fold(&t[1]), fold(&t[2])]);
        live = pairs;
    }
    (local, [t[0][0], t[1][0], t[2][0]])
}

/// Send a round of the sumcheck over the packs and segments and bind its variable, whose point
/// in the claim is `at`: the claim's `eq` factor on it moves into `scale`.
fn bind<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    coeffs: &[F; 3],
    at: F,
    value: &mut F,
    scale: &mut F,
    point: &mut Vec<F>,
) -> F {
    ps.add_round_poly_ext(coeffs, true);
    let challenge = ps.challenge::<F, W>(Grp::C3);
    let eq = F::ONE + at + challenge;
    *value = eq * F::poly_eval(coeffs, challenge);
    *scale *= eq;
    point.push(challenge);
    challenge
}

/// The coefficients of a round polynomial `h`, scaled, from its values at `0` and infinity:
/// `(1 + r) h(0) + r h(1) = value` gives the value at one.
fn round_coefficients<F: Ext<W>, const W: usize>(scale: F, zero: F, infinity: F, value: F, r: F) -> [F; 3] {
    let (c0, c2) = (scale * zero, scale * infinity);
    // value = c0 + r (c1 + c2).
    let c1 = (value + c0) * r.inv() + c2;
    [c0, c1, c2]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lv::primitives::test_rng::Rng;

    #[test]
    fn paired_messages_match_successive_rounds() {
        let mut rng = Rng::new(47);
        let s = rng.ext();
        let field = PowerField::new(s).unwrap();
        let claim = Claim {
            value: F192::ZERO,
            mu: [F192::ZERO; crate::lv::keccak_gkr::rmfe::PACK],
            point: Vec::new(),
            weights: rng.ext_vec(BITS),
        };
        let round = Round::new(&field, &claim, s, rng.ext());
        let rows: [Vec<u64>; 4] = std::array::from_fn(|_| (0..ROW).map(|_| rng.next_u64()).collect());
        let mut scratch = vec![0; 12 * FACTOR_ROW];
        for input in [
            rows.each_ref().map(Vec::as_slice),
            [&rows[0][..], &rows[1], &rows[2], &rows[2]],
            [&rows[0][..]; 4],
        ] {
            let (eq, eta, r) = (rng.ext(), rng.ext(), rng.ext());
            let mut sums = PairSums::default();
            round.add_quad(&mut sums, &mut scratch, input, eq);
            let pair = round.finish_pair(&sums);
            let mut first = RoundSums::default();
            round.add_pair(&mut first, &mut scratch, input[0], input[1], eq * (F192::ONE + eta));
            round.add_pair(&mut first, &mut scratch, input[2], input[3], eq * eta);
            assert_eq!(pair.first(eta), round.finish(&first));

            let (mut low, mut high) = (vec![0; ROW], vec![0; ROW]);
            field.fold_row_portable(&mut low, input[0], input[1], &field.to_poly(r), BITS);
            field.fold_row_portable(&mut high, input[2], input[3], &field.to_poly(r), BITS);
            let mut second = RoundSums::default();
            round.add_pair(&mut second, &mut scratch, &low, &high, eq);
            assert_eq!(pair.second(r), round.finish(&second));
        }
    }
}

#[cfg(all(test, target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
mod gfni_tests {
    use crate::lv::primitives::test_rng::Rng;

    use super::*;
    use crate::lv::keccak_gkr::keccak::LANES;
    use crate::lv::keccak_gkr::protocol::first_claim;

    /// The GFNI outer products give the digit buckets' sums, on dense, sparse and zero weights,
    /// with and without a padding block.
    #[test]
    fn gfni_pack_products_equal_the_buckets() {
        // 1100 instances: three blocks written, a padding block for the fourth.
        {
            let (n, depth, seed) = (1100, 12, 2);
            let mut rng = Rng::new(seed);
            let inputs: Vec<[u64; LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
            let shape = Shape::new(n, depth);
            let mut committed = vec![crate::lv::primitives::field::F64(0); 1 << shape.stack_log()];
            let witness = Witness::generate(shape, &inputs, &mut committed);
            assert!(witness.written() < shape.n_blocks(), "a padding block");
            for (step, mode) in [(0, "dense"), (depth - 1, "sparse"), (depth / 2, "lanes"), (1, "zero")] {
                let layer = Layer::new(&witness, (0..shape.segments()).map(|m| shape.round(m, step)).collect(), None);
                let mut claim = first_claim(shape, &rng.ext_vec(4), rng.ext_vec(shape.y_vars()), &rng.ext_vec(5));
                claim.weights = (0..BITS)
                    .map(|j| {
                        // Sparse: whole lane bytes and some single positions are zero. Lanes: only
                        // lanes 0..3 weigh, so rows with no active lane at all are skipped.
                        if mode == "zero"
                            || (mode == "sparse" && ((j / 8) % 3 == 1 || j % 7 == 0))
                            || (mode == "lanes" && j >= 4 * 64)
                        {
                            F192::ZERO
                        } else {
                            rng.ext()
                        }
                    })
                    .collect();
                assert!(
                    layer.pack_products_gfni(&claim) == layer.pack_products_buckets(&claim),
                    "n {n} depth {depth} step {step} {mode}"
                );
            }
        }
    }
}
