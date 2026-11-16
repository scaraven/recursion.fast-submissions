// Vendored from leanVM 0b850750 + the pr/all crate diff (04fba039b..edd857be9) `crates/keccak_gkr/src/products_gfni.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The product polynomial's bit sums by GFNI outer products (x86-64 with AVX2 and GFNI): the
//! same values as [`crate::lv::keccak_gkr::prover`]'s digit buckets, `sum over positions j of weights[j] (x)
//! product(q, j)` for every pack `q` of a block and every coefficient of its product.
//!
//! Eight consecutive `z` of one lane are a *lane byte*. For a lane byte's positions `j_0 .. j_7`
//! and one byte `b` of their weights, GF2P8AFFINEQB with the matrix `M_b` maps a *column byte*
//! (bit `k` = one coefficient of `product(q, j_k)`) to byte `b` of the sum of the weights of the
//! positions whose coefficient is set: the lane byte's share of that coefficient's sum. One
//! instruction does this for 32 (pack, coefficient) column bytes at once.
//!
//! Per block, two phases:
//! 1. per *row byte* with a nonzero weight (the same byte of the five lanes of a row, which `chi`
//!    mixes): the five lane bytes' embeddings, the products of each active lane byte, and their
//!    bit transposes into column bytes, staged register by register in a per-thread buffer;
//! 2. per staged register, every active lane byte's 24 matrices applied into accumulators held in
//!    registers (eight at a time on AVX2, all 24 with AVX-512), then one byte transpose back to
//!    field elements.
//!
//! The 8x8 byte transpose without VPERMB ([`transpose_bytes8x8`]) leaves the positions in a fixed
//! order ([`TRANSPOSED_ORDER`]), which the matrices absorb ([`COLUMN_BIT_POSITION`]).
//!
//! The two-phase outer-product scheme follows hashmancer-keccak's GFNI kernels; the code here is
//! written for this crate's layout (16-instance packs, 192-bit weights).
//!
//! lvm2 E2-K: generic over the weights' field ([`Ext`] of `W` words): `8 W` matrices a lane byte, 24 at E3 and
//! 16 at E2, so phase 2 applies `8 W` affine byte maps per staged register and active lane byte.

use core::arch::x86_64::*;

use crate::lv::primitives::field::Ext;

use crate::lv::keccak_gkr::keccak::BITS;
use crate::lv::keccak_gkr::kernels::{PACKS, embed, products};
use crate::lv::keccak_gkr::prover::PAYLOAD_BITS;
use crate::lv::keccak_gkr::witness::words;

/// Staged registers per active lane byte: 32 column bytes each, six coefficient bytes per pack.
const STAGED: usize = PAYLOAD_BITS / 32;
/// Bytes of a weight, at most (E3's 24; E2's are 16).
const WEIGHT_BYTES: usize = 24;

type V = __m256i;

/// The GF2P8AFFINEQB source that turns the instruction into an 8x8 bit transpose of its matrix.
const BIT_TRANSPOSE: i64 = 0x8040_2010_0804_0201_u64 as i64;

/// The qword order [`transpose_bytes8x8`] leaves: output qword `d` byte `n` is byte `d` of input
/// `TRANSPOSED_ORDER[n]`.
const TRANSPOSED_ORDER: [usize; 8] = [0, 1, 4, 5, 2, 3, 6, 7];
/// The position that bit `i` of a column byte stands for, after the byte and bit transposes.
const COLUMN_BIT_POSITION: [usize; 8] = {
    let mut p = [0; 8];
    let mut i = 0;
    while i < 8 {
        p[i] = TRANSPOSED_ORDER[7 - i];
        i += 1;
    }
    p
};

/// lvm2 PFAST-K: the byte permutes of [`ProductSums::stage_lane_byte_vbmi`]'s gather. Output register pair `j` of a
/// group of eight packs holds its column qwords `8 j + s` (`s < 8`), qword `c` being coefficient byte `c % 6` of
/// pack `c / 6`, whose byte `n` (before the bit transpose) is byte `c % 6` of position `TRANSPOSED_ORDER[n]`'s
/// product. Byte `(o, s, e)` of level 1 (`16 o + 2 s + e`) is output `2 h + o`'s byte from the pair's position
/// `e`; byte `(o, s, f, e)` of level 2 (`32 o + 4 s + 2 f + e`) from pair `f`'s; level 3 places them.
struct Gather {
    l1: [[u8; 64]; 3],
    l2: [u8; 64],
    l3: [[u8; 64]; 2],
}

static GATHER: Gather = {
    let mut g = Gather { l1: [[0; 64]; 3], l2: [0; 64], l3: [[0; 64]; 2] };
    let mut o = 0;
    while o < 2 {
        let mut s = 0;
        while s < 8 {
            let mut e = 0;
            while e < 2 {
                let mut h = 0;
                while h < 3 {
                    let c = 8 * (2 * h + o) + s;
                    g.l1[h][16 * o + 2 * s + e] = ((e << 6) | (8 * (c / 6) + c % 6)) as u8;
                    h += 1;
                }
                let mut f = 0;
                while f < 2 {
                    g.l2[32 * o + 4 * s + 2 * f + e] = ((f << 6) | (16 * o + 2 * s + e)) as u8;
                    f += 1;
                }
                e += 1;
            }
            let mut n = 0;
            while n < 8 {
                let k = TRANSPOSED_ORDER[n];
                g.l3[o][8 * s + n] = (((k / 4) << 6) | (32 * o + 4 * s + 2 * (k / 2 % 2) + k % 2)) as u8;
                n += 1;
            }
            s += 1;
        }
        o += 1;
    }
    g
};

/// lvm2 PFAST-K4: the byte permutes of the position-major staging ([`ProductSums::stage_row_s`]).
/// `spread[l]` builds a pack's *staggered* register from the halves of an embedded transposed register whose
/// 128-bit lane `l` is that pack (16-bit element `k` = position `k`): 128-bit lane `i` holds positions `2 i` in
/// bits 0..24 and `2 i + 1` in bits 88..112 (qword 1 shifted up by 24 bits), every other byte zero (`high`'s odd
/// bytes are). `chain[r]` gathers output register pair `r` of four packs (column qwords `8 r .. 8 r + 8`, qword
/// `c` = coefficient byte `c % 6` of pack `c / 6`, byte `n` from position `TRANSPOSED_ORDER[n]`) from the
/// products of packs `r` and `r + 1`, whose 128-bit lane `i` holds position `2 i`'s product in bytes 0..6 and
/// `2 i + 1`'s in bytes 6..12. Aligned, so that each table is one aligned 512-bit load.
#[repr(C, align(64))]
struct StagingS {
    spread: [[u8; 64]; 4],
    chain: [[u8; 64]; 3],
}

static STAGING_S: StagingS = {
    let mut g = StagingS { spread: [[0; 64]; 4], chain: [[0; 64]; 3] };
    let mut l = 0;
    while l < 4 {
        let mut i = 0;
        while i < 64 {
            // `high` byte 1: an odd byte, zero.
            g.spread[l][i] = 64 + 1;
            i += 1;
        }
        let mut k = 0;
        while k < 8 {
            let at = 16 * (k / 2) + 11 * (k % 2);
            g.spread[l][at] = (16 * l + 2 * k) as u8;
            g.spread[l][at + 1] = (16 * l + 2 * k + 1) as u8;
            g.spread[l][at + 2] = (64 + 16 * l + 2 * k) as u8;
            k += 1;
        }
        l += 1;
    }
    let mut r = 0;
    while r < 3 {
        let mut s = 0;
        while s < 8 {
            let c = 8 * r + s;
            let (pack, m) = (c / 6, c % 6);
            let mut n = 0;
            while n < 8 {
                let k = TRANSPOSED_ORDER[n];
                g.chain[r][8 * s + n] = (((pack - r) << 6) | (16 * (k / 2) + 6 * (k % 2) + m)) as u8;
                n += 1;
            }
            s += 1;
        }
        r += 1;
    }
    g
};

/// In-lane byte interleave of the lane's two qwords (16-bit element `d` = byte `d` of both).
const INTERLEAVE: [u8; 32] = {
    let mut t = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let j = i % 16;
        t[i] = if j % 2 == 0 { (j / 2) as u8 } else { (8 + j / 2) as u8 };
        i += 1;
    }
    t
};

/// 8x8 byte transpose of the qwords `a_0 .. a_7` (`p` = `a_0 .. a_3`, `q` = `a_4 .. a_7`): output
/// qword `d` (`d < 4` in the first register) byte `n` = byte `d` of `a_{TRANSPOSED_ORDER[n]}`. Two
/// in-lane byte shuffles, two 16-bit unpacks and two dword permutes.
///
/// # Safety
/// AVX2 (the module's build).
#[inline(always)]
unsafe fn transpose_bytes8x8(p: V, q: V) -> [V; 2] {
    unsafe {
        let il = _mm256_loadu_si256(INTERLEAVE.as_ptr().cast());
        let (p, q) = (_mm256_shuffle_epi8(p, il), _mm256_shuffle_epi8(q, il));
        // Dword d of lane 0: bytes d of (a0, a1, a4, a5); of lane 1: of (a2, a3, a6, a7).
        let (e, f) = (_mm256_unpacklo_epi16(p, q), _mm256_unpackhi_epi16(p, q));
        let idx = _mm256_setr_epi32(0, 4, 1, 5, 2, 6, 3, 7);
        [_mm256_permutevar8x32_epi32(e, idx), _mm256_permutevar8x32_epi32(f, idx)]
    }
}

/// 4x4 transpose of qwords: `out[i]` qword `k` = `r[k]` qword `i`.
///
/// # Safety
/// AVX2.
#[inline(always)]
unsafe fn transpose_qwords4x4(r: [V; 4]) -> [V; 4] {
    unsafe {
        let t0 = _mm256_unpacklo_epi64(r[0], r[1]);
        let t1 = _mm256_unpackhi_epi64(r[0], r[1]);
        let t2 = _mm256_unpacklo_epi64(r[2], r[3]);
        let t3 = _mm256_unpackhi_epi64(r[2], r[3]);
        [
            _mm256_permute2x128_si256(t0, t2, 0x20),
            _mm256_permute2x128_si256(t1, t3, 0x20),
            _mm256_permute2x128_si256(t0, t2, 0x31),
            _mm256_permute2x128_si256(t1, t3, 0x31),
        ]
    }
}

/// Where staged register `r` of active lane byte `a` lies in the buffer (`n_active` active lane
/// bytes). With AVX-512 the register pairs `2 R`, `2 R + 1` are adjacent, lane byte after lane byte,
/// so phase 2 reads a pair with one load; otherwise each register's lane bytes are contiguous.
#[inline(always)]
const fn staged_index(r: usize, a: usize, n_active: usize) -> usize {
    if cfg!(all(target_feature = "avx512f", target_feature = "avx512bw")) {
        2 * ((r / 2) * n_active + a) + r % 2
    } else {
        r * n_active + a
    }
}

/// lvm2 PFAST-K4: the pack whose column qwords the staged registers hold in place of pack `q`'s, so that payload bit
/// `48 staged_pack(q) + c` is coefficient `c` of pack `q`'s product. With VBMI the staging takes the packs `j`,
/// `8 + j`, `16 + j`, `24 + j` as staged packs `4 j .. 4 j + 4` ([`ProductSums::stage_row_s`]); otherwise in order.
/// (The same `cfg` as `stage`'s branch that calls it.)
#[inline(always)]
pub const fn staged_pack(q: usize) -> usize {
    if cfg!(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni")) {
        4 * (q % 8) + q / 8
    } else {
        q
    }
}

/// The `8 W` matrices of a lane byte's weights: `M_b` maps a column byte (bit `i` = position
/// `COLUMN_BIT_POSITION[i]`) to byte `b` of the sum of the weights it selects. An affine byte map
/// reads output bit `i` off matrix byte `7 - i`, whose bit `k` is then bit `8 b + i` of
/// `w[COLUMN_BIT_POSITION[k]]`.
///
/// lvm2 R9-KG: the same matrices as leanVM's bit-by-bit build: byte `k` of `x` is byte `b` of
/// `w[COLUMN_BIT_POSITION[k]]`, an 8 x 8 bit transpose puts bit `i` of every byte in byte `i`, and
/// byte `i` goes to byte `7 - i`.
fn lane_byte_matrices<F: Ext<W>, const W: usize>(w: &[F]) -> Vec<u64> {
    let columns: [[u64; W]; 8] = std::array::from_fn(|k| w[COLUMN_BIT_POSITION[k]].to_limbs());
    (0..8 * W)
        .map(|b| {
            let x = (0..8).fold(0u64, |x, k| x | (columns[k][b / 8] >> (8 * (b % 8)) & 0xff) << (8 * k));
            transpose_bits8x8(x).swap_bytes()
        })
        .collect()
}

/// The 8 x 8 bit transpose of a word whose byte `i` is row `i`: bit `8 i + j` swaps with `8 j + i`.
#[inline(always)]
fn transpose_bits8x8(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^ t ^ (t << 28)
}

/// One layer's product sums by outer products: the weights' matrices, in the order the blocks visit
/// the lane bytes.
pub struct ProductSums<const W: usize> {
    /// Row bytes `(y, z / 8)` with a nonzero weight, and the mask of their active lanes `x`.
    row_bytes: Vec<(u8, u8, u8)>,
    /// The active lane bytes' matrices, `8 W` each, in the order the row bytes visit them (`row_bytes`, then `x`).
    matrices: Vec<u64>,
}

/// A thread's buffers.
pub struct Scratch {
    /// The staged registers of a block, laid out by [`staged_index`].
    staged: Vec<V>,
    acc: Box<[[V; WEIGHT_BYTES]; STAGED]>,
    /// Per payload bit, its weighted sum's `W` words (of three). E3 only.
    pub out: Box<[[u64; 3]; PAYLOAD_BITS]>,
    /// lvm2 PFAST-K: E2's sums, in [`OutE2`]'s order.
    pub out2: Box<OutE2>,
}

/// lvm2 PFAST-K: a block's E2 sums, two words each, payload bit `32 r + 16 l + k` at entry `32 r + 2 k + l` (the
/// order the byte transpose leaves them in, one 256-bit store per pair), aligned so that four entries are one
/// 512-bit load. (lvm2 PFAST-K4: [`ProductSums::block_sums`]'s E2 form only; the prover's E2 pass uses
/// [`ProductSums::block_sums_weigh_e2`].)
#[repr(C, align(64))]
pub struct OutE2(pub [[u64; 2]; PAYLOAD_BITS]);

/// lvm2 PFAST-K4: the entry `4 g + i` (`sums[g]`, 128-bit lane `i`) of the [`SumsE2`] that
/// [`ProductSums::block_sums_weigh_e2`] accumulates payload bit `bit` in: payload bit `64 P + 16 l + k` at
/// `64 P + 4 k + l`, the order the 512-bit byte transpose of staged register pair `P` leaves.
#[inline(always)]
pub const fn e2_entry(bit: usize) -> usize {
    64 * (bit / 64) + 4 * (bit % 16) + bit % 64 / 16
}

/// lvm2 PFAST-K: E2's weighted sums of four entries, unreduced: the Karatsuba products
/// `P0 = a0 w0`, `P1 = a1 w1` and `M = (a0 + a1)(w0 + w1)` of entry `4 g + i` in 128-bit lane `i` of
/// `self.0[g]`'s three registers.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub struct SumsE2(pub [[u64; 8]; 3]);

impl Default for SumsE2 {
    fn default() -> Self {
        Self([[0; 8]; 3])
    }
}

/// lvm2 PFAST-K: `sums[g] += w * out[4 g .. 4 g + 4]` at E2 (`w = w0 + w1 X`), unreduced, four entries a
/// register: three carry-less products of 512 bits per four entries where the scalar form takes twelve
/// of 128.
#[cfg(all(target_feature = "avx512f", target_feature = "vpclmulqdq"))]
pub fn weigh_e2(w: [u64; 2], out: &OutE2, sums: &mut [SumsE2]) {
    assert_eq!(4 * sums.len(), PAYLOAD_BITS);
    // SAFETY: AVX-512F and VPCLMULQDQ are enabled at compile time; the loads read entries `4 g .. 4 g + 4` of
    // `out` (64-byte aligned, `4 g + 4 <= PAYLOAD_BITS`), the sums are 64-byte aligned.
    unsafe {
        let wv = _mm512_broadcast_i32x4(_mm_set_epi64x(w[1] as i64, w[0] as i64));
        let ws = _mm512_set1_epi64((w[0] ^ w[1]) as i64);
        for (g, s) in sums.iter_mut().enumerate() {
            let e = _mm512_load_si512(out.0.as_ptr().add(4 * g).cast());
            // Lane `i`: `[a0 + a1, a0 + a1]` of entry `4 g + i`.
            let a = _mm512_xor_si512(e, _mm512_shuffle_epi32::<0x4e>(e));
            let p = [
                _mm512_clmulepi64_epi128::<0x00>(e, wv),
                _mm512_clmulepi64_epi128::<0x11>(e, wv),
                _mm512_clmulepi64_epi128::<0x00>(a, ws),
            ];
            for (s, p) in s.0.iter_mut().zip(p) {
                let at = s.as_mut_ptr().cast::<__m512i>();
                _mm512_store_si512(at, _mm512_xor_si512(_mm512_load_si512(at), p));
            }
        }
    }
}

impl<const W: usize> ProductSums<W> {
    /// Matrices a lane byte.
    const BYTES: usize = 8 * W;

    pub fn new<F: Ext<W>>(weights: &[F]) -> Self {
        assert!(weights.len() >= BITS);
        let lane_bytes: Vec<Option<Vec<u64>>> = (0..BITS / 8)
            .map(|o| {
                let w = &weights[8 * o..8 * o + 8];
                w.iter().any(|&x| x != F::ZERO).then(|| lane_byte_matrices(w))
            })
            .collect();
        let mut row_bytes = Vec::new();
        let mut matrices = Vec::new();
        for y in 0..5usize {
            for zb in 0..8usize {
                let at = |x: usize| &lane_bytes[8 * (x + 5 * y) + zb];
                let mask = (0..5).fold(0u8, |m, x| m | u8::from(at(x).is_some()) << x);
                if mask != 0 {
                    row_bytes.push((y as u8, zb as u8, mask));
                    matrices.extend((0..5).filter_map(|x| at(x).clone()).flatten());
                }
            }
        }
        Self { row_bytes, matrices }
    }

    pub fn scratch(&self) -> Scratch {
        // SAFETY: AVX2 is enabled at compile time.
        let zero = unsafe { _mm256_setzero_si256() };
        Scratch {
            staged: vec![zero; STAGED * self.n_active()],
            acc: Box::new([[zero; WEIGHT_BYTES]; STAGED]),
            out: Box::new([[0; 3]; PAYLOAD_BITS]),
            out2: Box::new(OutE2([[0; 2]; PAYLOAD_BITS])),
        }
    }

    /// The weighted bit sums of a block (`BITS` positions of eight words) into `s.out`: entry
    /// `48 staged_pack(q) + c` is `sum over j of weights[j] * coefficient c of product(q, j)` ([`staged_pack`]).
    fn n_active(&self) -> usize {
        self.matrices.len() / Self::BYTES
    }

    pub fn block_sums(&self, s: &mut Scratch, block: &[u64]) {
        let n_active = self.n_active();
        self.stage(block, &mut s.staged, n_active);
        self.accumulate(&s.staged, n_active, &mut s.acc);
        if W == 2 {
            Self::to_field_elements_e2(&s.acc, &mut s.out2);
        } else {
            Self::to_field_elements(&s.acc, &mut s.out);
        }
    }

    /// lvm2 PFAST-K4: phase 2 at E2 fused with the byte transpose and the block's weight: per pair of staged
    /// registers, every active lane byte through its 16 matrices (four lane bytes a step), the 16 accumulators
    /// byte-transposed in registers (four entries of [`e2_entry`]'s order a register) and weighed into `sums`
    /// as [`weigh_e2`] does. The same sums.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "vpclmulqdq"))]
    pub fn block_sums_weigh_e2(&self, s: &mut Scratch, block: &[u64], w: [u64; 2], sums: &mut [SumsE2]) {
        assert_eq!(W, 2);
        let n_active = self.n_active();
        self.stage(block, &mut s.staged, n_active);
        let staged = &s.staged;
        assert!(staged.len() >= STAGED * n_active);
        assert!(self.matrices.len() >= n_active * Self::BYTES);
        assert_eq!(4 * sums.len(), PAYLOAD_BITS);
        // SAFETY: AVX-512F/BW, VPCLMULQDQ and GFNI are enabled at compile time; lane byte `a`'s registers `2 pair`,
        // `2 pair + 1` are the 64 bytes at `staged_index(2 pair, a, n_active)` (`a < n_active`, asserted size), its
        // matrices the 16 words at `16 a` (asserted), and `sums[16 pair + k]` is in bounds (`16 STAGED / 2 = 384`).
        unsafe {
            let wv = _mm512_broadcast_i32x4(_mm_set_epi64x(w[1] as i64, w[0] as i64));
            let ws = _mm512_set1_epi64((w[0] ^ w[1]) as i64);
            let (sp, mp) = (staged.as_ptr(), self.matrices.as_ptr());
            for pair in 0..STAGED / 2 {
                let ld = |a: usize| _mm512_loadu_si512(sp.add(staged_index(2 * pair, a, n_active)).cast());
                let g = |c: __m512i, a: usize, b: usize| _mm512_gf2p8affine_epi64_epi8(c, _mm512_set1_epi64(*mp.add(16 * a + b) as i64), 0);
                let mut acc = [_mm512_setzero_si512(); 16];
                // Four lane bytes a step (eight take more registers than there are: spills and copies).
                for step in 0..n_active / 4 {
                    let a = 4 * step;
                    let c: [__m512i; 4] = std::array::from_fn(|i| ld(a + i));
                    let mrow = mp.add(16 * a);
                    let g4 = |i: usize, b: usize| _mm512_gf2p8affine_epi64_epi8(c[i], _mm512_set1_epi64(*mrow.add(16 * i + b) as i64), 0);
                    macro_rules! step {
                        ($($b:literal)*) => {$(
                            acc[$b] = _mm512_ternarylogic_epi64(
                                acc[$b],
                                _mm512_ternarylogic_epi64(g4(0, $b), g4(1, $b), g4(2, $b), 0x96),
                                g4(3, $b),
                                0x96,
                            );
                        )*};
                    }
                    step!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15);
                }
                let mut a = n_active - n_active % 4;
                while a < n_active {
                    let c = ld(a);
                    for (b, acc) in acc.iter_mut().enumerate() {
                        *acc = _mm512_xor_si512(*acc, g(c, a, b));
                    }
                    a += 1;
                }
                crate::lv::primitives::bits::transpose_bytes16x16_per_lane512(&mut acc);
                // acc[k] 128-bit lane `l`: payload bit `64 pair + 16 l + k`, entry `64 pair + 4 k + l`.
                for (k, e) in acc.into_iter().enumerate() {
                    let a = _mm512_xor_si512(e, _mm512_shuffle_epi32::<0x4e>(e));
                    let p = [
                        _mm512_clmulepi64_epi128::<0x00>(e, wv),
                        _mm512_clmulepi64_epi128::<0x11>(e, wv),
                        _mm512_clmulepi64_epi128::<0x00>(a, ws),
                    ];
                    for (s, p) in sums.get_unchecked_mut(16 * pair + k).0.iter_mut().zip(p) {
                        let at = s.as_mut_ptr().cast::<__m512i>();
                        _mm512_store_si512(at, _mm512_xor_si512(_mm512_load_si512(at), p));
                    }
                }
            }
        }
    }

    /// lvm2 PFAST-K: [`Self::to_field_elements`] at E2: one 16 x 16 byte transpose a register, its rows
    /// stored whole into [`OutE2`]'s order.
    fn to_field_elements_e2(acc: &[[V; WEIGHT_BYTES]; STAGED], out: &mut OutE2) {
        for (r, acc) in acc.iter().enumerate() {
            // SAFETY: AVX2 is enabled at compile time; the stores write entries `32 r + 2 k`, `32 r + 2 k + 1`
            // (`r < STAGED`, `32 STAGED = PAYLOAD_BITS`).
            unsafe {
                let mut lo: [V; 16] = std::array::from_fn(|b| acc[b]);
                crate::lv::primitives::bits::transpose_bytes16x16_per_lane256(&mut lo);
                // lo[k] lane l: bytes 0..16 of payload bit 32 r + 16 l + k, entry 32 r + 2 k + l.
                for (k, v) in lo.iter().enumerate() {
                    _mm256_store_si256(out.0.as_mut_ptr().add(32 * r + 2 * k).cast(), *v);
                }
            }
        }
    }

    /// Phase 1: every active lane byte's column bytes into `staged[staged_index(r, a, n_active)]`.
    fn stage(&self, block: &[u64], staged: &mut [V], n_active: usize) {
        assert!(staged.len() >= STAGED * n_active);
        // lvm2 PFAST-K4: with VBMI, position-major: per row byte each lane's eight positions transposed once
        // (pack-major registers), then per pack slot `j` the five lanes embedded in registers and every active lane
        // byte's products, gathers and stores straight from them ([`Self::stage_row_s`]).
        #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
        {
            const WORDS: usize = crate::lv::keccak_gkr::witness::BLOCK_WORDS;
            assert!(block.len() >= BITS * WORDS, "a block's positions");
            // SAFETY: AVX-512F/BW is enabled at compile time.
            let mut lanes = [[unsafe { _mm512_setzero_si512() }; 8]; 5];
            let mut a = 0;
            for &(y, zb, mask) in &self.row_bytes {
                let (y, zb) = (y as usize, zb as usize);
                assert!(y < 5 && zb < 8, "a row byte");
                for (x, lane) in lanes.iter_mut().enumerate() {
                    // SAFETY: AVX-512F/BW is enabled at compile time; lane `x + 5 y` (< 25) byte `zb` (< 8) is the
                    // 64 words from `(64 (x + 5 y) + 8 zb) WORDS`, inside `block` (asserted length `BITS WORDS`).
                    *lane = unsafe { Self::transpose_lane_s(block.as_ptr().add((64 * (x + 5 * y) + 8 * zb) * WORDS)) };
                }
                let count = mask.count_ones() as usize;
                assert!(a + count <= n_active, "one staged column per active lane byte");
                // SAFETY: AVX-512F/BW/VBMI, VPCLMULQDQ and GFNI are enabled at compile time; the row byte's active lane
                // bytes are `a .. a + count`, `a + count <= n_active` (asserted), and the stores are register pairs
                // `R < STAGED / 2` of those, inside `staged` (asserted size).
                unsafe {
                    // Every lane active (the usual case): no per-lane tests in the kernel.
                    if mask == 0x1f {
                        Self::stage_row_s::<true>(&lanes, mask, staged.as_mut_ptr(), a, n_active)
                    } else {
                        Self::stage_row_s::<false>(&lanes, mask, staged.as_mut_ptr(), a, n_active)
                    }
                };
                a += count;
            }
            assert_eq!(a, n_active, "every active lane byte staged");
            return;
        }
        #[allow(unreachable_code)]
        let mut embedded = [[[0u32; PACKS]; 8]; 5];
        let mut prod = [[0u64; PACKS]; 8];
        let mut a = 0;
        for &(y, zb, mask) in &self.row_bytes {
            let (y, zb) = (y as usize, zb as usize);
            for (x, lane) in embedded.iter_mut().enumerate() {
                for (k, e) in lane.iter_mut().enumerate() {
                    *e = embed(words(block, 64 * (x + 5 * y) + 8 * zb + k));
                }
            }
            for x in (0..5).filter(|x| mask >> x & 1 == 1) {
                let (e0, e1, e2) = (&embedded[x], &embedded[(x + 1) % 5], &embedded[(x + 2) % 5]);
                // lvm2 PFAST-K: with VBMI the products go from registers straight into the gather.
                #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
                {
                    assert!(a < n_active, "one staged column per active lane byte");
                    // SAFETY: AVX-512F/BW/VBMI, VPCLMULQDQ and GFNI are enabled at compile time (the v4 tree);
                    // `a < n_active` (asserted) and the stores are register pairs `R < STAGED / 2` of lane byte
                    // `a`, inside `staged` (asserted size).
                    unsafe { Self::stage_lane_byte_vbmi([e0, e1, e2], staged.as_mut_ptr(), a, n_active) };
                    a += 1;
                    continue;
                }
                #[allow(unreachable_code)]
                for (k, p) in prod.iter_mut().enumerate() {
                    *p = products(&e0[k], &e1[k], &e2[k]);
                }
                assert!(a < n_active, "one staged column per active lane byte");
                // SAFETY: AVX2 and GFNI are enabled at compile time; `a < n_active` (asserted) and
                // `stage_lane_byte` writes registers `r < STAGED` only (`3 * 15 + 2`), so every store
                // is inside `staged` (asserted size).
                #[cfg(not(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi")))]
                unsafe { Self::stage_lane_byte(&prod, staged.as_mut_ptr(), a, n_active) };
                a += 1;
            }
        }
        // Phase 2 reads every active lane byte's registers: none may be left from another block.
        assert_eq!(a, n_active, "every active lane byte staged");
    }

    /// lvm2 PFAST-K4: a lane's eight positions at `raw` (position `k` = words `8 k .. 8 k + 8`), transposed by
    /// 16-bit unpacks inside each 128-bit lane: register `j` lane `l` holds pack `8 l + j`, 16-bit element `k` its
    /// position `k`.
    ///
    /// # Safety
    /// AVX-512F/BW; `raw` readable for 64 words.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
    #[inline(always)]
    unsafe fn transpose_lane_s(raw: *const u64) -> [__m512i; 8] {
        const { assert!(crate::lv::keccak_gkr::witness::BLOCK_WORDS == 8, "a position is one 512-bit register") };
        unsafe {
            let v: [__m512i; 8] = std::array::from_fn(|k| _mm512_loadu_si512(raw.add(8 * k).cast()));
            let a: [__m512i; 8] = std::array::from_fn(|i| {
                let (p, q) = (v[i & !1], v[i | 1]);
                if i % 2 == 0 { _mm512_unpacklo_epi16(p, q) } else { _mm512_unpackhi_epi16(p, q) }
            });
            // b[4 h + 2 u + w]: 32-bit unpack (w) of a[4 h + u], a[4 h + u + 2].
            let b: [__m512i; 8] = std::array::from_fn(|i| {
                let (h, u, w) = (i / 4, i / 2 % 2, i % 2);
                let (p, q) = (a[4 * h + u], a[4 * h + u + 2]);
                if w == 0 { _mm512_unpacklo_epi32(p, q) } else { _mm512_unpackhi_epi32(p, q) }
            });
            // Element `j` of every input: positions 0..4 from b[j / 2], 4..8 from b[4 + j / 2].
            std::array::from_fn(|j| {
                let (p, q) = (b[j / 2], b[4 + j / 2]);
                if j % 2 == 0 { _mm512_unpacklo_epi64(p, q) } else { _mm512_unpackhi_epi64(p, q) }
            })
        }
    }

    /// lvm2 PFAST-K4: [`Self::stage_lane_byte`] for a row byte's active lane bytes (`mask`; lane byte `x` is staged
    /// column `a0 +` the number of active lanes below `x`), from its five lanes' transposed registers: the same staged
    /// registers up to the order of the packs ([`staged_pack`]). Per pack slot `j`: the five lanes' embeddings
    /// ([`embedding_words`](crate::lv::keccak_gkr::kernels::embedding_words)); per pack `8 l + j` each lane's
    /// *staggered* register ([`StagingS`]: one byte permute) and each active lane byte's product `ones (a + c) + b c`,
    /// four VPCLMULQDQ and two XORs (two positions a 128-bit lane, the odd one's operands shifted up by 24 bits so
    /// its product lands at bit 48); per four packs (`l = 0 .. 4`, staged packs `4 j .. 4 j + 4`) three byte permutes
    /// to the three register pairs their 96 column qwords fill, each then bit-transposed by one affine map.
    ///
    /// # Safety
    /// AVX-512F/BW/VBMI, VPCLMULQDQ and GFNI; `staged + staged_index(2 R, a, n_active)` writable for 64 bytes,
    /// `R < STAGED / 2`, for the row byte's active lane bytes `a`; `mask == 0x1f` if `FULL`.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
    #[inline(always)]
    unsafe fn stage_row_s<const FULL: bool>(lanes: &[[__m512i; 8]; 5], mask: u8, staged: *mut V, a0: usize, n_active: usize) {
        unsafe {
            let bit_transpose = _mm512_set1_epi64(BIT_TRANSPOSE);
            let ones = crate::lv::keccak_gkr::rmfe::RMFE.ones as i64;
            let ones = _mm512_broadcast_i32x4(_mm_set_epi64x(ones << 24, ones));
            let chain = STAGING_S.chain.each_ref().map(|t| _mm512_loadu_si512(t.as_ptr().cast()));
            let mut slot = [0usize; 5];
            let mut next = a0;
            for (x, slot) in slot.iter_mut().enumerate() {
                *slot = next;
                next += usize::from(mask >> x & 1 == 1);
            }
            for j in 0..8 {
                let halves: [(__m512i, __m512i); 5] =
                    std::array::from_fn(|x| crate::lv::keccak_gkr::kernels::embedding_words(lanes[x][j]));
                let mut prev = [_mm512_setzero_si512(); 5];
                for l in 0..4 {
                    // The spread index is read where it is used (a volatile load), so it takes no register across
                    // the loop: the vpermi2b it feeds overwrites its index anyway.
                    let s: [__m512i; 5] = std::array::from_fn(|x| {
                        let idx = core::ptr::read_volatile(STAGING_S.spread[l].as_ptr().cast::<__m512i>());
                        _mm512_permutex2var_epi8(halves[x].0, idx, halves[x].1)
                    });
                    for x in 0..5 {
                        if !FULL && mask >> x & 1 == 0 {
                            continue;
                        }
                        let (za, zb, zc) = (s[x], s[(x + 1) % 5], s[(x + 2) % 5]);
                        let linear = _mm512_xor_si512(za, zc);
                        let r = _mm512_xor_si512(
                            _mm512_ternarylogic_epi64(
                                _mm512_clmulepi64_epi128::<0x00>(linear, ones),
                                _mm512_clmulepi64_epi128::<0x11>(linear, ones),
                                _mm512_clmulepi64_epi128::<0x00>(zc, zb),
                                0x96,
                            ),
                            _mm512_clmulepi64_epi128::<0x11>(zc, zb),
                        );
                        if l > 0 {
                            let out = _mm512_permutex2var_epi8(prev[x], chain[l - 1], r);
                            let out = _mm512_gf2p8affine_epi64_epi8(bit_transpose, out, 0);
                            _mm512_storeu_si512(staged.add(staged_index(2 * (3 * j + l - 1), slot[x], n_active)).cast(), out);
                        }
                        prev[x] = r;
                    }
                }
            }
        }
    }

    /// lvm2 PFAST-K: [`Self::stage_lane_byte`] with AVX-512 VBMI: the same staged registers. Per group of eight
    /// packs, the eight positions' product registers (`P_k` qword `i` = pack `8 g + i`) go through a three-level
    /// byte gather ([`GATHER`], two-source byte permutes) straight to the six register pairs the group's 48
    /// column qwords fill, each qword then bit-transposed by one affine map.
    ///
    /// # Safety
    /// AVX-512F/BW/VBMI and GFNI; `staged + staged_index(2 R, a, n_active)` writable for 64 bytes, `R < STAGED / 2`.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
    #[inline(always)]
    unsafe fn stage_lane_byte_vbmi(e: [&[[u32; PACKS]; 8]; 3], staged: *mut V, a: usize, n_active: usize) {
        unsafe {
            let bit_transpose = _mm512_set1_epi64(BIT_TRANSPOSE);
            let ones = _mm512_set1_epi64(crate::lv::keccak_gkr::rmfe::RMFE.ones as i64);
            let idx = |t: &[u8; 64]| _mm512_loadu_si512(t.as_ptr().cast());
            let (l1, l2, l3) = (GATHER.l1.each_ref().map(idx), idx(&GATHER.l2), GATHER.l3.each_ref().map(idx));
            for g in 0..PACKS / 8 {
                // `products` of packs `8 g ..` at position `k`, qword `i` the pack `8 g + i`'s (as `products_vectors`).
                let p: [__m512i; 8] = std::array::from_fn(|k| {
                    let ld = |v: &[u32; PACKS]| _mm512_cvtepu32_epi64(_mm256_loadu_si256(v.as_ptr().add(8 * g).cast()));
                    let (za, zb, zc) = (ld(&e[0][k]), ld(&e[1][k]), ld(&e[2][k]));
                    let linear = _mm512_xor_si512(za, zc);
                    let even = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x00>(zb, zc), _mm512_clmulepi64_epi128::<0x00>(linear, ones));
                    let odd = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x11>(zb, zc), _mm512_clmulepi64_epi128::<0x11>(linear, ones));
                    _mm512_unpacklo_epi64(even, odd)
                });
                for h in 0..3 {
                    // Level 1: per pair of positions, the bytes of outputs `2 h`, `2 h + 1`.
                    let q1: [__m512i; 4] = std::array::from_fn(|f| _mm512_permutex2var_epi8(p[2 * f], l1[h], p[2 * f + 1]));
                    // Level 2: per four positions.
                    let q2: [__m512i; 2] = std::array::from_fn(|u| _mm512_permutex2var_epi8(q1[2 * u], l2, q1[2 * u + 1]));
                    for o in 0..2 {
                        let out = _mm512_permutex2var_epi8(q2[0], l3[o], q2[1]);
                        let out = _mm512_gf2p8affine_epi64_epi8(bit_transpose, out, 0);
                        let r = 2 * (6 * g + 2 * h + o);
                        _mm512_storeu_si512(staged.add(staged_index(r, a, n_active)).cast(), out);
                    }
                }
            }
        }
    }

    /// The column bytes of one lane byte's products (`prod[k][q]`: position `k`, pack `q`): register
    /// `r` holds column qwords `4 r .. 4 r + 4`, qword `6 q + m` being coefficient byte `m` of pack
    /// `q` (bit `i` of its byte `b`: coefficient `8 m + b` of position `COLUMN_BIT_POSITION[i]`).
    ///
    /// # Safety
    /// AVX2 and GFNI; `staged + staged_index(r, a, n_active)` writable for `r < STAGED`.
    #[inline(always)]
    unsafe fn stage_lane_byte(prod: &[[u64; PACKS]; 8], staged: *mut V, a: usize, n_active: usize) {
        unsafe {
            let bit_transpose = _mm256_set1_epi64x(BIT_TRANSPOSE);
            let ld = |k: usize, q: usize| _mm256_loadu_si256(prod[k].as_ptr().add(q).cast());
            for qq in (0..PACKS).step_by(4) {
                // t[h][i] qword k = the product of pack qq + i at position 4 h + k.
                let t = [
                    transpose_qwords4x4([ld(0, qq), ld(1, qq), ld(2, qq), ld(3, qq)]),
                    transpose_qwords4x4([ld(4, qq), ld(5, qq), ld(6, qq), ld(7, qq)]),
                ];
                let columns: [[V; 2]; 4] = std::array::from_fn(|i| {
                    let [lo, hi] = transpose_bytes8x8(t[0][i], t[1][i]);
                    [
                        _mm256_gf2p8affine_epi64_epi8(bit_transpose, lo, 0),
                        _mm256_gf2p8affine_epi64_epi8(bit_transpose, hi, 0),
                    ]
                });
                for pair in 0..2 {
                    // Packs q, q + 1 take three registers: bytes 0..4 of q; 4, 5 of q and 0, 1
                    // of q + 1; 2..4 and 4, 5 of q + 1.
                    let (c0, c1) = (columns[2 * pair], columns[2 * pair + 1]);
                    let r = 3 * ((qq + 2 * pair) / 2);
                    *staged.add(staged_index(r, a, n_active)) = c0[0];
                    *staged.add(staged_index(r + 1, a, n_active)) = _mm256_permute2x128_si256(c0[1], c1[0], 0x20);
                    *staged.add(staged_index(r + 2, a, n_active)) = _mm256_permute2x128_si256(c1[0], c1[1], 0x21);
                }
            }
        }
    }

    /// Phase 2: per staged register, every active lane byte through its 24 matrices, eight
    /// accumulators at a time in registers.
    #[cfg(not(all(target_feature = "avx512f", target_feature = "avx512bw")))]
    fn accumulate(&self, staged: &[V], n_active: usize, acc: &mut [[V; WEIGHT_BYTES]; STAGED]) {
        assert!(staged.len() >= STAGED * n_active);
        for (r, acc) in acc.iter_mut().enumerate() {
            for b0 in (0..Self::BYTES).step_by(8) {
                // SAFETY: AVX2 and GFNI are enabled at compile time (module cfg), and
                // `staged_index(r, a, n_active) < STAGED * n_active <= staged.len()` (asserted).
                unsafe {
                    let mut a8 = [_mm256_setzero_si256(); 8];
                    for (a, m) in self.matrices.chunks_exact(Self::BYTES).enumerate() {
                        let column = staged.get_unchecked(staged_index(r, a, n_active));
                        for (o, ao) in a8.iter_mut().enumerate() {
                            let g = _mm256_gf2p8affine_epi64_epi8(*column, _mm256_set1_epi64x(m[b0 + o] as i64), 0);
                            *ao = _mm256_xor_si256(*ao, g);
                        }
                    }
                    acc[b0..b0 + 8].copy_from_slice(&a8);
                }
            }
        }
    }

    /// Phase 2 with AVX-512: per pair of staged registers (one 512-bit load), every active lane byte
    /// through its 24 matrices, all 24 accumulators in registers, two lane bytes per three-way XOR.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
    fn accumulate(&self, staged: &[V], n_active: usize, acc: &mut [[V; WEIGHT_BYTES]; STAGED]) {
        assert!(staged.len() >= STAGED * n_active);
        let matrices = &self.matrices;
        for pair in 0..STAGED / 2 {
            // SAFETY: AVX-512F/BW and GFNI are enabled at compile time; lane byte `a`'s registers
            // `2 pair`, `2 pair + 1` are the 64 bytes at `staged_index(2 pair, a, n_active)`
            // (asserted size).
            unsafe {
                let ld = |a: usize| _mm512_loadu_si512(staged.as_ptr().add(staged_index(2 * pair, a, n_active)).cast());
                let bc = |m: u64| _mm512_set1_epi64(m as i64);
                let mut a24 = [_mm512_setzero_si512(); WEIGHT_BYTES];
                let m = |a: usize| -> &[u64] { &matrices[a * Self::BYTES..][..Self::BYTES] };
                let mut a = 0;
                // lvm2 PFAST-K2: four lane bytes a step, by pointers (their bounds asserted once): the same affine
                // maps, each accumulator's terms XORed in another order.
                if W == 2 {
                    assert!(matrices.len() >= n_active * Self::BYTES);
                    let (sp, mp) = (staged.as_ptr(), matrices.as_ptr());
                    let ldp = |a: usize| _mm512_loadu_si512(sp.add(staged_index(2 * pair, a, n_active)).cast());
                    while a + 3 < n_active {
                        let c = [ldp(a), ldp(a + 1), ldp(a + 2), ldp(a + 3)];
                        let mrow = mp.add(a * 16);
                        let g = |i: usize, b: usize| _mm512_gf2p8affine_epi64_epi8(c[i], bc(*mrow.add(16 * i + b)), 0);
                        // Unrolled by hand, so that the accumulators stay in registers.
                        macro_rules! step {
                            ($($b:literal)*) => {$(
                                a24[$b] = _mm512_ternarylogic_epi64(
                                    a24[$b],
                                    _mm512_ternarylogic_epi64(g(0, $b), g(1, $b), g(2, $b), 0x96),
                                    g(3, $b),
                                    0x96,
                                );
                            )*};
                        }
                        step!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15);
                        a += 4;
                    }
                }
                while a + 1 < n_active {
                    let (c0, c1, m0, m1) = (ld(a), ld(a + 1), m(a), m(a + 1));
                    for (b, ab) in a24[..Self::BYTES].iter_mut().enumerate() {
                        let g0 = _mm512_gf2p8affine_epi64_epi8(c0, bc(m0[b]), 0);
                        let g1 = _mm512_gf2p8affine_epi64_epi8(c1, bc(m1[b]), 0);
                        *ab = _mm512_ternarylogic_epi64(*ab, g0, g1, 0x96);
                    }
                    a += 2;
                }
                if a < n_active {
                    let (c0, m0) = (ld(a), m(a));
                    for (b, ab) in a24[..Self::BYTES].iter_mut().enumerate() {
                        *ab = _mm512_xor_si512(*ab, _mm512_gf2p8affine_epi64_epi8(c0, bc(m0[b]), 0));
                    }
                }
                // The low half is staged register `2 pair`, the high one `2 pair + 1`.
                for (b, ab) in a24[..Self::BYTES].iter().enumerate() {
                    acc[2 * pair][b] = _mm512_castsi512_si256(*ab);
                    acc[2 * pair + 1][b] = _mm512_extracti64x4_epi64::<1>(*ab);
                }
            }
        }
    }

    /// The accumulators as field elements: register `r`'s accumulator `b` byte `n` is byte `b` of
    /// payload bit `32 r + n`'s sum.
    fn to_field_elements(acc: &[[V; WEIGHT_BYTES]; STAGED], out: &mut [[u64; 3]; PAYLOAD_BITS]) {
        for (r, acc) in acc.iter().enumerate() {
            // SAFETY: AVX2 is enabled at compile time; the stores write 16 bytes into checked
            // `[u64; 3]` entries.
            unsafe {
                let mut lo: [V; 16] = std::array::from_fn(|b| acc[b]);
                let z = _mm256_setzero_si256();
                let mut hi: [V; 16] = std::array::from_fn(|b| if b < 8 && W == 3 { acc[16 + b] } else { z });
                crate::lv::primitives::bits::transpose_bytes16x16_per_lane256(&mut lo);
                if W == 3 {
                    crate::lv::primitives::bits::transpose_bytes16x16_per_lane256(&mut hi);
                }
                // lo[k] lane l: bytes 0..16 of payload bit 32 r + 16 l + k; hi[k]: bytes 16..24.
                for k in 0..16 {
                    for l in 0..2 {
                        let o = &mut out[32 * r + 16 * l + k];
                        let (v, w) = if l == 0 {
                            (_mm256_castsi256_si128(lo[k]), _mm256_castsi256_si128(hi[k]))
                        } else {
                            (_mm256_extracti128_si256(lo[k], 1), _mm256_extracti128_si256(hi[k], 1))
                        };
                        _mm_storeu_si128(o.as_mut_ptr().cast(), v);
                        if W == 3 {
                            o[2] = _mm_cvtsi128_si64(w) as u64;
                        }
                    }
                }
            }
        }
    }
}
