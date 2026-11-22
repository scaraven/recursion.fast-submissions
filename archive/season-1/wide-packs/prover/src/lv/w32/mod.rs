//! lvm2 W32 G0 (NEXT-PROTO3 §2.2; prototype, prover-only, used by no proof): the tape GKR's Skip and Product
//! passes at a 32-instance RMFE pack, (32, 53 -> 105) (DEEP-AND's verified RMFE, `tables.rs`), next to the K = 16
//! kernels, for instruction counts (SDE) and timings.
//!
//! Layout: a block position is the witness's eight words (512 instances), here 16 packs of 32 instances (pack `q` is
//! bits `32 (q % 2) ..` of word `q / 2`). A half is 8 packs (256 instances), two groups of 4 packs: the Skip pass's
//! two symbolic rounds bind a group's two pack variables, and the group bit stays binary. Its points are the 5 mixed
//! points of `{0, 1, inf}^2` per group, 10 per half ([`mixed`]); slot `10 h + 5 g + p`.
//!
//! Skip: per mixed point, `sum over positions x of w[x] * b * c` with `b, c` the point's embedded values at the two
//! positions `chi` mixes into `x`, as a polynomial of 233 bits (53 x 53 -> 105, times a 128-bit weight). Product:
//! per pack and coefficient of `ones (a + c) + b c` (105 coefficients), `sum over positions of w[j] * coefficient`,
//! times the block's weight.
#![allow(clippy::all, dead_code, unused_unsafe)]

mod tables;
pub use tables::{EMB, ONES, PROJ};

use crate::lv::keccak_gkr::keccak::{BITS, row_positions};
use crate::lv::primitives::field::gf2_64::mul_wide;

pub const BLOCK_WORDS: usize = 8;
pub const PACKS: usize = 16;
pub const POINTS: usize = 5;
pub const SLOTS: usize = 20;
pub const PROD_BITS: usize = 105;
/// Payload columns of a lane byte: 64 per pack (coefficients 0..64), then 41 per pack (64..105).
pub const COLS: usize = PACKS * PROD_BITS;
/// 64-byte staged registers per lane byte.
pub const PAIRS: usize = COLS.div_ceil(64);

/// `EMB8[b][v]`: the embedding of byte value `v` at input byte `b`.
pub static EMB8: [[u64; 256]; 4] = {
    let mut t = [[0u64; 256]; 4];
    let mut b = 0;
    while b < 4 {
        let mut v = 0;
        while v < 256 {
            let mut e = 0;
            let mut i = 0;
            while i < 8 {
                if v >> i & 1 == 1 {
                    e ^= EMB[8 * b + i];
                }
                i += 1;
            }
            t[b][v] = e;
            v += 1;
        }
        b += 1;
    }
    t
};

#[inline(always)]
pub fn embed(a: u32) -> u64 {
    EMB8[0][a as u8 as usize] ^ EMB8[1][(a >> 8) as u8 as usize] ^ EMB8[2][(a >> 16) as u8 as usize] ^ EMB8[3][(a >> 24) as usize]
}

/// Bit `i` of the projection of a 105-bit polynomial.
pub fn project(p: u128) -> u32 {
    (0..32).fold(0, |acc, i| acc | (((p & PROJ[i]).count_ones() & 1) << i))
}

#[inline(always)]
pub fn pack(block: &[u64], j: usize, q: usize) -> u32 {
    (block[j * BLOCK_WORDS + q / 2] >> (32 * (q % 2))) as u32
}

/// The 5 mixed points of `{0, 1, inf}^2` of a group's 4 values (`v[b0 + 2 b1]`): (inf,0), (inf,1), (0,inf), (1,inf),
/// (inf,inf), infinity being the sum.
#[inline(always)]
pub fn mixed(v: [u64; 4]) -> [u64; 5] {
    [v[0] ^ v[1], v[2] ^ v[3], v[0] ^ v[2], v[1] ^ v[3], v[0] ^ v[1] ^ v[2] ^ v[3]]
}

/// The carry-less product of a 128-bit and a 128-bit polynomial, four words.
#[inline(always)]
pub fn mul256(p: u128, w: [u64; 2]) -> [u64; 4] {
    let (p0, p1) = (p as u64, (p >> 64) as u64);
    let lo = mul_wide(p0, w[0]);
    let mid = mul_wide(p0, w[1]) ^ mul_wide(p1, w[0]);
    let hi = mul_wide(p1, w[1]);
    let r0 = lo ^ (mid << 64);
    let r1 = hi ^ (mid >> 64);
    [r0 as u64, (r0 >> 64) as u64, r1 as u64, (r1 >> 64) as u64]
}

fn xor4(a: &mut [u64; 4], b: [u64; 4]) {
    for i in 0..4 {
        a[i] ^= b[i];
    }
}

/// Portable reference of the K = 32 Skip pass over one block: per slot, the 256-bit polynomial.
pub fn skip_ref(block: &[u64], w: &[[u64; 2]]) -> [[u64; 4]; SLOTS] {
    let mut acc = [[0u64; 4]; SLOTS];
    for r in 0..5 {
        for z in 0..64 {
            let js = row_positions(r, z);
            let e: [[u64; PACKS]; 5] = std::array::from_fn(|x| std::array::from_fn(|q| embed(pack(block, js[x], q))));
            for h in 0..2 {
                for g in 0..2 {
                    let q0 = 8 * h + 4 * g;
                    let m: [[u64; 5]; 5] = std::array::from_fn(|x| mixed(e[x][q0..q0 + 4].try_into().unwrap()));
                    for p in 0..POINTS {
                        for x in 0..5 {
                            let prod = mul_wide(m[(x + 1) % 5][p], m[(x + 2) % 5][p]);
                            xor4(&mut acc[10 * h + 5 * g + p], mul256(prod, w[js[x]]));
                        }
                    }
                }
            }
        }
    }
    acc
}

/// The unprojected `chi` of a pack at position `j`: `ones (a + c) + b c`.
pub fn chi_product(block: &[u64], j: usize, q: usize) -> u128 {
    let along = |k: usize| crate::lv::keccak_gkr::keccak::along(j, k);
    let (a, b, c) = (embed(pack(block, j, q)), embed(pack(block, along(1), q)), embed(pack(block, along(2), q)));
    mul_wide(ONES, a ^ c) ^ mul_wide(b, c)
}

/// The staged column index of pack `q`'s coefficient `c`.
#[inline(always)]
pub const fn column(q: usize, c: usize) -> usize {
    if c < 64 { 64 * q + c } else { 1024 + 41 * q + (c - 64) }
}

/// Portable reference of the K = 32 Product pass's per-block sums: `out[column(q, c)] = sum over j of w[j] *
/// coefficient c of chi_product(j, q)` (128 bits), every position.
pub fn product_ref(block: &[u64], w: &[[u64; 2]]) -> Vec<u128> {
    let mut out = vec![0u128; PAIRS * 64];
    for j in 0..BITS {
        let wj = w[j][0] as u128 | (w[j][1] as u128) << 64;
        for q in 0..PACKS {
            let p = chi_product(block, j, q);
            for c in 0..PROD_BITS {
                if p >> c & 1 == 1 {
                    out[column(q, c)] ^= wj;
                }
            }
        }
    }
    out
}

/// SSC markers for SDE (`mov ebx, mark; fs addr32 nop`), a no-op natively: `0x4c56_KK_0S`, `KK` 0x21 K16 Skip,
/// 0x22 W32 Skip, 0x23 K16 Product, 0x24 W32 Product, 0x25 W32 embedding only; `S` 1 start, 2 end.
#[cfg(target_arch = "x86_64")]
macro_rules! ssc {
    ($m:expr) => {
        // SAFETY: rbx is saved and restored around the marker; the marker is a no-op outside SDE.
        unsafe {
            core::arch::asm!(
                "xchg {t}, rbx",
                "mov ebx, {m}",
                ".byte 0x64, 0x67, 0x90",
                "xchg {t}, rbx",
                m = const $m,
                t = inout(reg) 0u64 => _,
            )
        }
    };
}

#[inline(never)]
pub fn mark(kernel: u32, end: bool) {
    if !std::env::var("LVM_SDE_MARKS").is_ok_and(|v| v == "1") {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    match (kernel, end) {
        (0x21, false) => ssc!(0x4c562101),
        (0x21, true) => ssc!(0x4c562102),
        (0x22, false) => ssc!(0x4c562201),
        (0x22, true) => ssc!(0x4c562202),
        (0x23, false) => ssc!(0x4c562301),
        (0x23, true) => ssc!(0x4c562302),
        (0x24, false) => ssc!(0x4c562401),
        (0x24, true) => ssc!(0x4c562402),
        (0x25, false) => ssc!(0x4c562501),
        (0x25, true) => ssc!(0x4c562502),
        _ => {}
    }
}

/// The W32 kernels need AVX-512 BW/VBMI, VPCLMULQDQ and GFNI: the v4 tier.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
pub mod v4;

pub mod bench;
// W32-P task 2: the dev check of (B) and (C) on a real tape's layers (`LVM_W32_CHECK=1`).
pub mod check;
pub mod dev;
