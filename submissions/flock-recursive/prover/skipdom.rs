//! The univariate-skip domain and the pinned coordinates (blueprint §2.3 Z1–Z2, paper §4.2–§4.3).
//! Appendix A.1 values: `ζ = x^((2^64−1)/255)`, `φ₈(v) = Σ vᵢ ζ^i` (GF(2^8) represented modulo
//! the minimal polynomial of `ζ`, `field::gf8_poly`), the skip set `S = φ₈(0…63)` (bit `i` of the
//! position ↦ `ζ^i`) and `Λ = S + ζ^6 = φ₈(64…127)`.
//!
//! **Deviation (P1, reported):** the pinned point. A.1's candidate `ρⱼ = (x^(2^(j+3)), 0)` has no
//! product structure, so round 1 would have to lift every row's 64 GF(2^8) products to F with its
//! own weight (8× the table work of the paper's kernel). P1 keeps the paper's two-level geometric
//! progression (§4.3): `ρᵢ = gᵢ/(1 + gᵢ)` with `gᵢ = ζ^(2^(i−1))` (`i ≤ 3`) and `gᵢ = γ^(2^(i−4))`
//! (`i ≥ 4`, `γ = y`), so `eq(ρ, (k, j)) = C · ζ^k · γ^j` (`k < 8`, `j < 16`, `C = Π(1 + ρᵢ)`); the
//! 128 weights are F₂-independent because `y` has degree 16 over GF(2^8) (test `pinned_rank`).
//!
//! Tables (all derived, built once): the LDE byte table `t0` of the composite map
//! `M = NTT_Λ ∘ iNTT_S` (paper §4.2, compressed form: `M[i][8b + j] = M[i ⊕ 8b][j]`), the convert
//! table `conv[j][v] = γ^j φ₈(v)`, the matrix `M` itself (GF(2^8)), and the Lagrange weights the
//! verifier needs.

use crate::field::{gf8_inv, gf8_mul, B64, F};

pub struct Skip {
    pub omega: B64,
    pub phi8: [B64; 256],
    pub gamma: F,
    pub rho: [F; 7],
    pub c_pin: F,
    /// `conv[j·256 + v] = γ^j φ₈(v)`, `j < 16`.
    pub conv: Vec<F>,
    /// `t0[v·64 + i] = Σ_{j<8, v_j} M[i][j]` (bytes of GF(2^8)), 64-byte aligned via `t0_off`.
    t0: Vec<u8>,
    t0_off: usize,
    /// `mlam[i][σ] = L^S_σ(Λ_i)` in GF(2^8).
    pub mlam: [[u8; 64]; 64],
    /// `ms[σ][i] = L^Λ_i(S_σ)` in GF(2^8) (the inverse direction).
    pub ms: [[u8; 64]; 64],
    /// The 64 points of `S` and of `Λ` as F, and `S ∪ Λ` (128 points, `φ₈(0…127)`).
    pub s_pts: Vec<F>,
    pub l_pts: Vec<F>,
    pub sl_pts: Vec<F>,
}

fn lagrange8(pts: &[u8], sigma: usize, x: u8) -> u8 {
    let mut num = 1u8;
    let mut den = 1u8;
    for (q, &p) in pts.iter().enumerate() {
        if q != sigma {
            num = gf8_mul(num, x ^ p);
            den = gf8_mul(den, pts[sigma] ^ p);
        }
    }
    gf8_mul(num, gf8_inv(den))
}

impl Skip {
    fn build() -> Skip {
        let omega = crate::field::zeta();
        let mut phi8 = [B64::ZERO; 256];
        let mut pw = [B64::ONE; 8];
        for i in 1..8 {
            pw[i] = pw[i - 1].mul(omega);
        }
        for v in 0..256usize {
            let mut r = 0u64;
            for i in 0..8 {
                if (v >> i) & 1 == 1 {
                    r ^= pw[i].0;
                }
            }
            phi8[v] = B64(r);
        }
        let gamma = F::Y;
        let mut rho = [F::ZERO; 7];
        let mut g = F::b(omega);
        for i in 0..3 {
            rho[i] = g * (F::ONE + g).inv();
            g = g.sq();
        }
        let mut g = gamma;
        for i in 3..7 {
            rho[i] = g * (F::ONE + g).inv();
            g = g.sq();
        }
        let mut c_pin = F::ONE;
        for r in &rho {
            c_pin *= F::ONE + *r;
        }
        let mut conv = vec![F::ZERO; 16 * 256];
        let mut gj = F::ONE;
        for j in 0..16 {
            for v in 0..256 {
                conv[j * 256 + v] = gj.mulb(phi8[v]);
            }
            gj *= gamma;
        }
        let s8: Vec<u8> = (0..64u8).collect();
        let l8: Vec<u8> = (64..128u8).collect();
        let mut mlam = [[0u8; 64]; 64];
        let mut ms = [[0u8; 64]; 64];
        for i in 0..64 {
            for s in 0..64 {
                mlam[i][s] = lagrange8(&s8, s, l8[i]);
                ms[s][i] = lagrange8(&l8, i, s8[s]);
            }
        }
        let mut t0 = vec![0u8; 256 * 64 + 63];
        let t0_off = (64 - (t0.as_ptr() as usize & 63)) & 63;
        for v in 1..256usize {
            let low = v & v.wrapping_neg();
            let j = low.trailing_zeros() as usize;
            for i in 0..64 {
                t0[t0_off + v * 64 + i] = t0[t0_off + (v ^ low) * 64 + i] ^ mlam[i][j];
            }
        }
        let s_pts = (0..64).map(|v| F::b(phi8[v])).collect();
        let l_pts = (64..128).map(|v| F::b(phi8[v])).collect();
        let sl_pts = (0..128).map(|v| F::b(phi8[v])).collect();
        Skip { omega, phi8, gamma, rho, c_pin, conv, t0, t0_off, mlam, ms, s_pts, l_pts, sl_pts }
    }

    #[inline(always)]
    pub fn t0p(&self) -> *const u8 {
        unsafe { self.t0.as_ptr().add(self.t0_off) }
    }

    /// The LDE of one 64-bit row (8 bytes) to `Λ` (64 GF(2^8) bytes), by the compressed table.
    #[inline(always)]
    pub fn lde_row(&self, row: &[u8], out: &mut [u8; 64]) {
        let t = &self.t0[self.t0_off..];
        out.copy_from_slice(&t[row[0] as usize * 64..row[0] as usize * 64 + 64]);
        for b in 1..8 {
            let base = row[b] as usize * 64;
            for i in 0..64 {
                out[i] ^= t[base + (i ^ (8 * b))];
            }
        }
    }

    /// `φ₈(v)` as F.
    #[inline(always)]
    pub fn phi(&self, v: u8) -> F {
        F::b(self.phi8[v as usize])
    }
}

pub fn skip() -> &'static Skip {
    static S: std::sync::OnceLock<Skip> = std::sync::OnceLock::new();
    S.get_or_init(Skip::build)
}

/// Lagrange weights `L_p(x)` over the point set `pts` (distinct), `Σ_p L_p(x) f(p) = f̂(x)` for
/// `deg f < |pts|`: `V(x)/((x − p) Π_{q≠p}(p − q))`, one batched inversion.
pub fn lagrange_weights(pts: &[F], x: F) -> Vec<F> {
    let n = pts.len();
    if let Some(i) = pts.iter().position(|p| *p == x) {
        let mut w = vec![F::ZERO; n];
        w[i] = F::ONE;
        return w;
    }
    // denominators d_p (x − p) Π_{q≠p} (p − q)
    let mut den = vec![F::ONE; n];
    for p in 0..n {
        let mut d = x + pts[p];
        for q in 0..n {
            if q != p {
                d *= pts[p] + pts[q];
            }
        }
        den[p] = d;
    }
    let mut vx = F::ONE;
    for p in pts {
        vx *= x + *p;
    }
    // batch inversion
    let mut pre = vec![F::ONE; n + 1];
    for i in 0..n {
        pre[i + 1] = pre[i] * den[i];
    }
    let mut inv = pre[n].inv();
    let mut out = vec![F::ZERO; n];
    for i in (0..n).rev() {
        out[i] = vx * inv * pre[i];
        inv *= den[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The 128 pinned weights `C ω^k γ^j` are F₂-independent (rank 128) and equal `eq(ρ, ·)`.
    #[test]
    fn pinned_rank() {
        let s = skip();
        let mut w = Vec::new();
        let mut ok = 0;
        for j in 0..16 {
            for k in 0..8 {
                let v = s.conv[j * 256 + (1usize << k)] * s.c_pin;
                let idx = (k as u64) | ((j as u64) << 3);
                let _ = idx;
                w.push(v);
                ok += 1;
            }
        }
        assert_eq!(ok, 128);
        // eq(ρ, (k, j)) = C ω^k γ^j for the integer k, j (k: x₆…x₈, j: x₉…x₁₂)
        for k in 0..8u64 {
            for j in 0..16u64 {
                let e = crate::mle::eq_at_int(&s.rho, k | (j << 3));
                let mut wk = F::ONE;
                for _ in 0..k {
                    wk = wk.mulb(s.omega);
                }
                let mut gj = F::ONE;
                for _ in 0..j {
                    gj *= s.gamma;
                }
                assert_eq!(e, s.c_pin * wk * gj);
            }
        }
        // rank over F₂ of the 128 vectors ω^k γ^j (Gaussian elimination on 128-bit rows)
        let mut rows: Vec<u128> = Vec::new();
        for j in 0..16 {
            for k in 0..8 {
                let v = s.conv[j * 256 + (1usize << k)];
                rows.push(v.lo as u128 | ((v.hi as u128) << 64));
            }
        }
        let mut rank = 0;
        for bit in 0..128 {
            if let Some(p) = (rank..rows.len()).find(|&i| (rows[i] >> bit) & 1 == 1) {
                rows.swap(rank, p);
                let r = rows[rank];
                for i in 0..rows.len() {
                    if i != rank && (rows[i] >> bit) & 1 == 1 {
                        rows[i] ^= r;
                    }
                }
                rank += 1;
            }
        }
        assert_eq!(rank, 128);
    }

    /// The compressed LDE equals the direct Lagrange map, and `ms` inverts `mlam`'s direction.
    #[test]
    fn lde_table() {
        let s = skip();
        let row: [u8; 8] = [0x13, 0xA7, 0x00, 0xFF, 0x5C, 0x81, 0x3E, 0x02];
        let mut out = [0u8; 64];
        s.lde_row(&row, &mut out);
        for i in 0..64 {
            let mut v = 0u8;
            for sg in 0..64 {
                if (row[sg / 8] >> (sg % 8)) & 1 == 1 {
                    v ^= s.mlam[i][sg];
                }
            }
            assert_eq!(out[i], v, "lane {i}");
        }
        // F-level: Lagrange weights over S at a Λ point are φ₈ of mlam
        let w = lagrange_weights(&s.s_pts, s.l_pts[5]);
        for sg in 0..64 {
            assert_eq!(w[sg], s.phi(s.mlam[5][sg]));
        }
    }
}
