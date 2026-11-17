// Vendored from leanVM 0b850750 `crates/keccak_gkr/src/kernels.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The bit-level kernels of the layer prover, over one block position at a time: the 16 packs of
//! one bit position of one block.
//!
//! lvm2 W32 (K = 32 RMFE packs): a block position is 16 packs of 32 instances, a pack's embedding 53 bits and a
//! product of two 105. The bit-level rounds fold a group, half a block (8 packs, `SKIP = 3` variables; leanVM folds
//! its 16-pack half block with 4). This tree serves v2 and v4p only (`keccak_gkr_v4` is v4's), so the kernels are
//! the portable forms: `mul_wide` is one PCLMULQDQ on v4p and the run-time tiered product on v2. The bytes are
//! the protocol's (`reference.rs`); only the algorithm is this tree's.

use crate::lv::primitives::field::gf2_64::mul_wide;

use crate::lv::keccak_gkr::keccak::row_positions;
use crate::lv::keccak_gkr::rmfe::RMFE;
use crate::lv::keccak_gkr::witness::BLOCK_WORDS;

/// Packs in a block position.
pub(crate) const PACKS: usize = 16;
/// Packs the bit-level rounds fold together: half a block.
pub const GROUP: usize = 8;
/// Variables indexing the packs of a group.
pub(crate) const SKIP: usize = 3;
/// Points of `{0, 1, infinity}^SKIP`, and those of them with a coordinate at infinity.
pub(crate) const TERNARY: usize = 3usize.pow(SKIP as u32);
pub(crate) const MIXED: usize = TERNARY - GROUP;
/// The mixed points of a block position's two groups.
pub const SLOTS: usize = 2 * MIXED;
/// Words a Skip slot's sum takes: a 105-bit product times a weight of at most three words.
pub const SKIP_WORDS: usize = 5;

/// The slot of output `i` of group `half` of a block position.
#[inline(always)]
pub const fn slot(half: usize, i: usize) -> usize {
    MIXED * half + i
}

/// The ternary index of each output of [`extend_group`]: variable `k`'s point is its `k`-th
/// digit, with infinity as 2. The points with a digit at infinity, in increasing order.
pub(crate) const fn mixed_points() -> [usize; MIXED] {
    let mut out = [0usize; MIXED];
    let (mut t, mut i) = (0, 0);
    while t < TERNARY {
        if t % 3 == 2 || t / 3 % 3 == 2 || t / 9 % 3 == 2 {
            out[i] = t;
            i += 1;
        }
        t += 1;
    }
    out
}

static MIXED_POINTS: [usize; MIXED] = mixed_points();

/// Extend one group's values on the binary cube to the mixed points of `{0, 1, infinity}^SKIP`:
/// along each variable, the value at infinity is the sum of the two others.
#[inline(always)]
pub(crate) fn extend_group(v: &[u64; GROUP]) -> [u64; MIXED] {
    let mut all = [0u64; TERNARY];
    for (b, &x) in v.iter().enumerate() {
        all[(b & 1) + 3 * (b >> 1 & 1) + 9 * (b >> 2)] = x;
    }
    // Along variable 0, then 1, then 2: point `2` of the variable is the sum of `0` and `1`.
    for stride in [1, 3, 9] {
        for t in 0..TERNARY {
            if t / stride % 3 == 2 {
                all[t] = all[t - stride] ^ all[t - 2 * stride];
            }
        }
    }
    std::array::from_fn(|i| all[MIXED_POINTS[i]])
}

/// Both groups of a block position, at their [`slot`]s.
#[inline(always)]
pub fn extend(packs: &[u64; PACKS], out: &mut [u64; SLOTS]) {
    for half in 0..2 {
        let e = extend_group(packs[GROUP * half..][..GROUP].try_into().unwrap());
        out[MIXED * half..][..MIXED].copy_from_slice(&e);
    }
}

/// [`extend`] of [`embed`].
#[inline(always)]
pub fn embed_extend(words: &[u64; BLOCK_WORDS], out: &mut [u64; SLOTS]) {
    extend(&embed(words), out)
}

/// The 16 packs of a block position, embedded: pack `q` is bits `32 (q % 2) ..` of word `q / 2`.
#[inline(always)]
pub fn embed(words: &[u64; BLOCK_WORDS]) -> [u64; PACKS] {
    std::array::from_fn(|q| RMFE.embed((words[q / 2] >> (32 * (q % 2))) as u32))
}

/// The unprojected `chi` of 16 packs: `ones * (a + c) + b * c`, 105 bits each.
#[inline(always)]
pub fn products(a: &[u64; PACKS], b: &[u64; PACKS], c: &[u64; PACKS]) -> [u128; PACKS] {
    let ones = RMFE.ones;
    std::array::from_fn(|q| mul_wide(ones, a[q] ^ c[q]) ^ mul_wide(b[q], c[q]))
}

/// Per slot, `sum over positions of weight * product`: per weight word `k`, the partial products of the product's
/// low and high words (`lo[k]` at word `k`, `hi[k]` at word `k + 1`).
pub struct SkipAcc<const W: usize> {
    lo: [[u128; W]; SLOTS],
    hi: [[u128; W]; SLOTS],
}

impl<const W: usize> SkipAcc<W> {
    pub fn new() -> Box<Self> {
        Box::new(Self { lo: [[0; W]; SLOTS], hi: [[0; W]; SLOTS] })
    }

    pub fn clear(&mut self) {
        self.lo = [[0; W]; SLOTS];
        self.hi = [[0; W]; SLOTS];
    }

    /// Slot `i`'s sum, a polynomial of `W + 2` words (of [`SKIP_WORDS`]).
    pub fn get(&self, i: usize) -> [u64; SKIP_WORDS] {
        let mut out = [0u64; SKIP_WORDS];
        for k in 0..W {
            out[k] ^= self.lo[i][k] as u64;
            out[k + 1] ^= (self.lo[i][k] >> 64) as u64 ^ self.hi[i][k] as u64;
            out[k + 2] ^= (self.hi[i][k] >> 64) as u64;
        }
        out
    }
}

/// One row of five positions, which `chi` mixes cyclically: for every slot,
/// `acc[p] += sum over x of weights[x] * e[x + 1][p] * e[x + 2][p]`.
#[inline(always)]
pub fn skip_row<const W: usize>(acc: &mut SkipAcc<W>, e: &[[u64; SLOTS]; 5], weights: [&[u64; W]; 5]) {
    for x in 0..5 {
        let (b, c, w) = (&e[(x + 1) % 5], &e[(x + 2) % 5], weights[x]);
        for p in 0..SLOTS {
            let product = mul_wide(b[p], c[p]);
            let (lo, hi) = (product as u64, (product >> 64) as u64);
            for k in 0..W {
                acc.lo[p][k] ^= mul_wide(lo, w[k]);
                acc.hi[p][k] ^= mul_wide(hi, w[k]);
            }
        }
    }
}

/// For both groups of a block position, `sum over the group's packs of weights[.][q] * e[q]`,
/// as `W` partial products (53 + 64 bits each).
#[inline(always)]
pub fn fold_groups<const W: usize>(e: &[u64; PACKS], weights: &[[u64; GROUP]; W]) -> [[u128; W]; 2] {
    std::array::from_fn(|half| {
        std::array::from_fn(|k| (0..GROUP).fold(0, |acc, q| acc ^ mul_wide(e[GROUP * half + q], weights[k][q])))
    })
}

/// [`skip_row`] over every row and slice of a block, a position at a time.
pub(crate) struct SkipBlock<const W: usize> {
    acc: Box<SkipAcc<W>>,
    extended: [[u64; SLOTS]; 5],
}

impl<const W: usize> SkipBlock<W> {
    pub fn new() -> Box<Self> {
        Box::new(Self { acc: SkipAcc::new(), extended: [[0; SLOTS]; 5] })
    }

    /// Sum a block, the position weights as elements.
    pub fn run(&mut self, block: &[u64], weights: &[[u64; W]]) {
        self.acc.clear();
        for r in 0..5 {
            for z in 0..64 {
                let js = row_positions(r, z);
                for x in 0..5 {
                    embed_extend(crate::lv::keccak_gkr::witness::words(block, js[x]), &mut self.extended[x]);
                }
                skip_row(&mut self.acc, &self.extended, std::array::from_fn(|x| &weights[js[x]]));
            }
        }
    }

    /// Slot `i`'s sum, `W + 2` words.
    pub fn get(&self, i: usize) -> [u64; SKIP_WORDS] {
        self.acc.get(i)
    }
}
