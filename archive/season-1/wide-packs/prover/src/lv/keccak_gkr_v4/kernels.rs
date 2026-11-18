// Vendored from leanVM 0b850750 + the pr/all crate diff (04fba039b..edd857be9) `crates/keccak_gkr/src/kernels.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The bit-level kernels of the layer prover, over one block position at a time: the 16 packs of
//! one bit position of one block.
//!
//! lvm2 W32 (K = 32 RMFE packs, lead decision D1): a block position is 16 packs of 32 instances (pack `q` is bits
//! `32 (q % 2) ..` of word `q / 2`), a pack's embedding 53 bits and a product of two 105. A half block is 8 packs,
//! two groups of 4: the Skip pass's two symbolic rounds (`SKIP = 2`) bind a group's pack variables, the group bit
//! stays binary (the Groups pass gives its quadratic coefficient), and the half bit is the Tables pass's. So Skip
//! has 5 mixed points of `{0, 1, inf}^2` per group, 10 per half (K = 16: 19 of `{0, 1, inf}^3`, 38).
//!
//! The E2 kernels are W32 G0's (`lv/w32/v4.rs`: `Skip32`, `Product32`, AVX-512 BW/VBMI + VPCLMULQDQ + GFNI); the E3
//! forms are portable (no S2GS phase runs the tape at E3 on this tier).

use crate::lv::primitives::field::gf2_64::mul_wide;

use crate::lv::keccak_gkr::keccak::{BITS, row_positions};
use crate::lv::keccak_gkr::rmfe::RMFE;
use crate::lv::keccak_gkr::witness::BLOCK_WORDS;

/// Packs in a block position, and the variables indexing them.
pub const PACKS: usize = 1 << PACK_VARS;
pub const PACK_VARS: usize = 4;
/// Variables indexing the packs the bit-level rounds fold together, a group.
pub const SKIP: usize = 2;
pub const GROUP: usize = 1 << SKIP;
/// Groups in a block position.
pub const GROUPS: usize = PACKS / GROUP;
/// Points of `{0, 1, infinity}^SKIP`.
pub const TERNARY: usize = 3usize.pow(SKIP as u32);
/// Packs of a half block (two groups), and the bytes of a group and of a half at one position.
pub const HALF: usize = 2 * GROUP;
pub const GROUP_BYTES: usize = 16;
pub const HALF_BYTES: usize = 32;
/// The mixed points of `{0, 1, inf}^2` (a digit at infinity), as ternary indices `d0 + 3 d1`, in the order of
/// `w32::mixed`: (inf, 0), (inf, 1), (0, inf), (1, inf), (inf, inf).
pub const MIXED: [usize; 5] = [2, 5, 6, 7, 8];
/// Slots of a block: per half and group, the 5 mixed points (`10 h + 5 g + p`).
pub const SLOTS: usize = 20;
/// Words of a Skip slot's sum: a 105-bit product times a weight of at most three words.
pub const SKIP_WORDS: usize = 5;

const _: () = assert!(PACKS * crate::lv::keccak_gkr::rmfe::PACK == crate::lv::keccak_gkr::witness::BLOCK);
const _: () = assert!(GROUP_BYTES * 8 == GROUP * crate::lv::keccak_gkr::rmfe::PACK && HALF_BYTES == 2 * GROUP_BYTES);

/// Slot of half `h`, group `g`, mixed point `p`.
#[inline(always)]
pub const fn slot(h: usize, g: usize, p: usize) -> usize {
    10 * h + 5 * g + p
}

/// The 16 packs of a block position, embedded.
#[inline(always)]
pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u64; PACKS] {
    std::array::from_fn(|q| RMFE.embed((words[q / 2] >> (32 * (q % 2))) as u32))
}

/// The unprojected `chi` of 16 packs: `ones * (a + c) + b * c`.
#[inline(always)]
pub fn products(a: &[u64; PACKS], b: &[u64; PACKS], c: &[u64; PACKS]) -> [u128; PACKS] {
    let ones = RMFE.ones;
    std::array::from_fn(|q| mul_wide(ones, a[q] ^ c[q]) ^ mul_wide(b[q], c[q]))
}

/// The layer's position weights in the power basis of `s`, `W` words each (and at E2 the vector layouts).
pub struct SkipWeights<const W: usize> {
    polys: Vec<[u64; W]>,
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
    e2: Option<crate::lv::w32::v4::Weights32>,
}

impl<const W: usize> SkipWeights<W> {
    pub fn new(weights: Vec<[u64; W]>) -> Self {
        assert_eq!(weights.len(), BITS);
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
        {
            let e2 = (W == 2).then(|| {
                let w: Vec<[u64; 2]> = weights.iter().map(|w| [w[0], w[1 % W]]).collect();
                crate::lv::w32::v4::Weights32::new(&w)
            });
            Self { polys: weights, e2 }
        }
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni")))]
        Self { polys: weights }
    }
}

/// The Skip pass over one block: per slot, `sum over rows, slices and positions x of w[x] * B_p * C_p`, `B_p`, `C_p`
/// the mixed-point extensions over the group's packs of the embeddings at the two positions `chi` mixes into `x`.
pub struct SkipBlock<const W: usize> {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
    fast: Option<crate::lv::w32::v4::Skip32>,
    acc: [[u64; SKIP_WORDS]; SLOTS],
}

impl<const W: usize> SkipBlock<W> {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
            fast: (W == 2).then(crate::lv::w32::v4::Skip32::new),
            acc: [[0; SKIP_WORDS]; SLOTS],
        })
    }

    pub fn run(&mut self, block: &[u64], weights: &SkipWeights<W>) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi", target_feature = "vpclmulqdq", target_feature = "gfni"))]
        if let (Some(fast), Some(w)) = (self.fast.as_mut(), weights.e2.as_ref()) {
            fast.run(block, w);
            for (i, acc) in self.acc.iter_mut().enumerate() {
                let v = fast.get(i);
                *acc = [v[0], v[1], v[2], v[3], 0];
            }
            return;
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        if W == 2 {
            // SAFETY: PCLMULQDQ is enabled at compile time.
            unsafe { self.run_pclmul_e2(block, &weights.polys) };
            return;
        }
        self.run_portable(block, &weights.polys);
    }

    /// lvm2 W32-P: W32 G0's dev core (`w32::dev`, W32-S2) on 128-bit PCLMULQDQ, E2: per point and position `b c`
    /// (one product) times the weight by Karatsuba (three), accumulated per slot as `[P0, P1, M]`.
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    #[inline(never)]
    unsafe fn run_pclmul_e2(&mut self, block: &[u64], polys: &[[u64; W]]) {
        use core::arch::x86_64::*;
        unsafe {
            let x = |a: __m128i, b: __m128i| _mm_xor_si128(a, b);
            let mut acc = [[_mm_setzero_si128(); 3]; SLOTS];
            for r in 0..5 {
                for z in 0..64 {
                    let js = row_positions(r, z);
                    let e: [[u64; PACKS]; 5] = std::array::from_fn(|xx| embed(crate::lv::keccak_gkr::witness::words(block, js[xx])));
                    let wv: [__m128i; 5] = std::array::from_fn(|xx| _mm_set_epi64x(polys[js[xx]][1 % W] as i64, polys[js[xx]][0] as i64));
                    let ws: [__m128i; 5] = std::array::from_fn(|xx| _mm_cvtsi64_si128((polys[js[xx]][0] ^ polys[js[xx]][1 % W]) as i64));
                    for hg in 0..4 {
                        let m: [[u64; 5]; 5] = std::array::from_fn(|xx| crate::lv::w32::mixed(e[xx][GROUP * hg..][..4].try_into().unwrap()));
                        for p in 0..5 {
                            let s = &mut acc[5 * hg + p];
                            for xx in 0..5 {
                                let (b, c) = (m[(xx + 1) % 5][p], m[(xx + 2) % 5][p]);
                                let prod = _mm_clmulepi64_si128::<0x00>(_mm_cvtsi64_si128(b as i64), _mm_cvtsi64_si128(c as i64));
                                let mm = x(prod, _mm_unpackhi_epi64(prod, prod));
                                s[0] = x(s[0], _mm_clmulepi64_si128::<0x00>(prod, wv[xx]));
                                s[1] = x(s[1], _mm_clmulepi64_si128::<0x11>(prod, wv[xx]));
                                s[2] = x(s[2], _mm_clmulepi64_si128::<0x00>(mm, ws[xx]));
                            }
                        }
                    }
                }
            }
            let u = |v: __m128i| -> u128 { core::mem::transmute(v) };
            for (out, s) in self.acc.iter_mut().zip(&acc) {
                let (p0, p1, m) = (u(s[0]), u(s[1]), u(s[2]));
                let mid = m ^ p0 ^ p1;
                let (lo, hi) = (p0 ^ (mid << 64), p1 ^ (mid >> 64));
                *out = [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64, 0];
            }
        }
    }

    fn run_portable(&mut self, block: &[u64], polys: &[[u64; W]]) {
        self.acc = [[0; SKIP_WORDS]; SLOTS];
        for r in 0..5 {
            for z in 0..64 {
                let js = row_positions(r, z);
                let e: [[u64; PACKS]; 5] = std::array::from_fn(|x| embed(crate::lv::keccak_gkr::witness::words(block, js[x])));
                for hg in 0..4 {
                    let q0 = GROUP * hg;
                    let m: [[u64; 5]; 5] = std::array::from_fn(|x| crate::lv::w32::mixed(e[x][q0..q0 + 4].try_into().unwrap()));
                    for x in 0..5 {
                        let w = &polys[js[x]];
                        for p in 0..5 {
                            let product = mul_wide(m[(x + 1) % 5][p], m[(x + 2) % 5][p]);
                            let acc = &mut self.acc[5 * hg + p];
                            for (i, part) in [product as u64, (product >> 64) as u64].into_iter().enumerate() {
                                for (k, &wk) in w.iter().enumerate() {
                                    let t = mul_wide(part, wk);
                                    acc[i + k] ^= t as u64;
                                    acc[i + k + 1] ^= (t >> 64) as u64;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Slot `i`'s sum, `W + 2` words.
    #[inline(always)]
    pub fn get(&self, i: usize) -> [u64; SKIP_WORDS] {
        self.acc[i]
    }
}
