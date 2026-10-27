//! The lincheck (blueprint §2.3 Lc, paper §4.1, §4.5): `va + α vb = Σ_j η(j) Z(j)` over the
//! block's `2^14` positions, with `Z(j) = Σ_blk eq(s_out, blk) z(blk, j)` (the partial fold of the
//! witness over the block variables) and `η = A0ᵀ w + α B0ᵀ w` (the transpose circuit walk) for the
//! row weights `w(k) = L^S_{k mod 64}(λ) · eq(s_in, ⌊k/64⌋)`. **P1 choice** (the blueprint says
//! 9 rounds + a 64-entry skip collapse): 14 degree-2 rounds over all inner variables, the skip bits
//! read as Boolean variables, so the resulting z-claim is a plain multilinear one,
//! `z̃(t₀ … t₁₃, s_out) = vz`.
//!
//! The partial fold uses 256-entry sum tables per 8-block stripe after 8×8 bit transposes
//! (Flock `lincheck.rs`, `pack_z_lincheck` / `partial_fold_packed_z_fast`, as ported in
//! `probe/kernels/src/lin.rs`; `../LICENSE-flock`).

use crate::circuit::{Circuit, BLOCK};
use crate::field::F;
use crate::mle::eq_table;
use crate::par;
use crate::skipdom::{lagrange_weights, skip};

#[inline(always)]
pub fn transpose8(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^= t ^ (t << 28);
    x
}

/// `Z(j) = Σ_blk eq(s_out, blk) z(blk, j)` (`z` block-major words; at least 8 blocks).
pub fn partial_fold(z: &[u64], s_out: &[F]) -> Vec<F> {
    let nb = z.len() / 256;
    assert!(nb >= 8 && nb == 1 << s_out.len());
    let e = eq_table(s_out);
    let stripes = nb / 8;
    let parts = par::map_chunks(stripes, 1, |lo, hi| {
        let mut acc = vec![F::ZERO; BLOCK];
        let mut t = [F::ZERO; 256];
        let used_s = crate::par::used_blocks().div_ceil(8);
        for s in lo..hi.min(used_s) {
            t[0] = F::ZERO;
            for i in 0..8 {
                let h = 1 << i;
                for j in 0..h {
                    t[h + j] = t[j] + e[8 * s + i];
                }
            }
            let base = 8 * s * 256;
            for wi in 0..256 {
                for byte in 0..8 {
                    let mut x = 0u64;
                    for r in 0..8 {
                        x |= ((z[base + r * 256 + wi] >> (8 * byte)) & 0xFF) << (8 * r);
                    }
                    let y = transpose8(x);
                    let p = wi * 64 + byte * 8;
                    for tt in 0..8 {
                        acc[p + tt] += t[((y >> (8 * tt)) & 0xFF) as usize];
                    }
                }
            }
        }
        acc
    });
    let mut out = vec![F::ZERO; BLOCK];
    for p in parts {
        for j in 0..BLOCK {
            out[j] += p[j];
        }
    }
    out
}

/// Row weights `w(k) = L^S_{k mod 64}(λ) eq(s_in, ⌊k/64⌋)`.
pub fn row_weights(lambda: F, s_in: &[F]) -> Vec<F> {
    let l = lagrange_weights(&skip().s_pts, lambda);
    let e = eq_table(s_in);
    let mut w = vec![F::ZERO; BLOCK];
    for k in 0..BLOCK {
        w[k] = l[k & 63] * e[k >> 6];
    }
    w
}

/// `η = A0ᵀ w + α B0ᵀ w`.
pub fn eta(c: &Circuit, lambda: F, s_in: &[F], alpha: F) -> Vec<F> {
    let w = row_weights(lambda, s_in);
    let wb: Vec<F> = w.iter().map(|x| *x * alpha).collect();
    c.transpose(&w, &wb)
}
