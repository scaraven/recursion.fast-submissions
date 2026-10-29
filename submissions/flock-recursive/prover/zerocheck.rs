//! The zerocheck with the univariate skip (blueprint §2.3 Z, paper §4.2–§4.4, App. A), prover side.
//!
//! The witness is viewed as `2^(m−6)` rows of 64 bits (`x₀ … x₅`, the skip variables, are the bit
//! within a 64-bit word). Rows `x = (x₆ … x_{m−1})`; the zerocheck point is `r = (ρ₁ … ρ₇, r₈ …)`
//! for `x₆ …` (`skipdom.rs`). Round 1 sends `P^{ab}` and `P^z` on `Λ`; the c-side is computed as
//! two banks split by `x₆` (`bank_b[σ] = Σ_{x: x₆ = b} eq(r, x) z(x, σ)`, giving `P^z` on `Λ`).
//! Then (rev. 3.8, "skipping c") `m − 6` degree-3 rounds of `eq(r, x)·a_λ(x)·b_λ(x)` in Gruen's
//! form: `H_k(X) = Σ eq(r_{>k}, ·) â(λ, s_{<k}, X, ·) b̂(…)` from `H_k(1)`, `H_k(∞)` and the reduced
//! claim (`H_k(0) = (claim′ + r_k H_k(1))/(1 + r_k)`); the message is the coefficients of `g_k(X) =
//! eq(r_{<k}, s_{<k})·(1 + r_k + X)·H_k(X)` (`zc_coeffs`); the final value is `eq(r, s)·â·b̂`.
//!
//! The round-1 structure (windows of 2^13 bits, 16 "medium" positions × 8 rows, the compressed LDE
//! table, the GF(2^8) accumulation by `a^k`, the convert table and the two C banks) is Flock's
//! `crates/flock-core/src/zerocheck/univariate_skip_optimized.rs` as the phase-0 probe ported it
//! (`probe/kernels/src/skip.rs`; MIT/Apache-2.0, `../LICENSE-flock`).

use crate::field::{FAcc, F};
use crate::mle::eq_table;
use crate::par;
use crate::skipdom::{skip, Skip};
use crate::simd;

/// Round 1 output: `P^{ab}` on `Λ`, and the two C banks.
pub struct R1 {
    pub pab: [F; 64],
    pub bank: [[F; 64]; 2],
}

/// GF(2^8) product table (portable round 1).
fn gf8_tab() -> &'static Vec<u8> {
    static T: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    T.get_or_init(|| {
        let mut t = vec![0u8; 65536];
        for a in 0..256usize {
            for b in 0..256usize {
                t[(a << 8) | b] = crate::field::gf8_mul(a as u8, b as u8);
            }
        }
        t
    })
}

#[inline(always)]
fn gf8_reduce15(p: u16) -> u8 {
    let mut r = p as u32;
    for i in (8..15).rev() {
        if (r >> i) & 1 == 1 {
            r ^= (crate::field::gf8_poly() as u32) << (i - 8);
        }
    }
    r as u8
}

/// One window (128 rows of 64 bits) of round 1, portable: returns the window's unweighted sums
/// `(cab, c0, c1)` (each 64 lanes) of `Σ_{bm,k} ω^k γ^bm (…)`.
pub fn window_portable(sk: &Skip, a: &[u8], b: &[u8], z: &[u8], out: &mut [F; 192]) {
    let mul = gf8_tab();
    let mut la = [0u8; 64];
    let mut lb = [0u8; 64];
    out.fill(F::ZERO);
    for bm in 0..16 {
        let mut acc = [0u16; 64];
        for k in 0..8 {
            let off = (bm * 8 + k) * 8;
            sk.lde_row(&a[off..off + 8], &mut la);
            sk.lde_row(&b[off..off + 8], &mut lb);
            for lane in 0..64 {
                acc[lane] ^= (mul[((la[lane] as usize) << 8) | lb[lane] as usize] as u16) << k;
            }
        }
        let cv = &sk.conv[bm * 256..bm * 256 + 256];
        for lane in 0..64 {
            out[lane] += cv[gf8_reduce15(acc[lane]) as usize];
            let mut v = 0usize;
            for k in 0..8 {
                let off = (bm * 8 + k) * 8;
                v |= (((z[off + lane / 8] >> (lane % 8)) & 1) as usize) << k;
            }
            out[64 + lane] += cv[v & 0x55];
            out[128 + lane] += cv[v & 0xAA];
        }
    }
}

/// Round 1 over the witness (bytes of `a`, `b`, `z`), with `r_out` the coordinates of
/// `x₁₃ … x_{m−1}` (`m − 13` of them). Blocks `≥ used` are zero (`a = b = z = 0`: a segment's
/// blocks past its length) and contribute nothing, so only the first `used` are read.
pub fn round1(a: &[u8], b: &[u8], z: &[u8], r_out: &[F], used: usize) -> R1 {
    let sk = skip();
    let nw = a.len() / 1024;
    assert_eq!(nw, 1 << r_out.len());
    let eo = eq_table(r_out);
    let _sp = crate::prof::span("r1.windows");
    // a window whose a, b and z are all zero adds nothing (its LDEs are zero and the convert
    // tables map 0 to 0): skipped (a node's free and spare blocks, a third of its windows)
    let skip0 = (0..16).all(|bm| sk.conv[bm * 256].is_zero());
    let parts = par::map_chunks(nw.min(used.saturating_mul(2)), 16, |lo, hi| {
        let mut acc = vec![F::ZERO; 192];
        let mut w = [F::ZERO; 192];
        for x in lo..hi {
            let base = x * 1024;
            if skip0 && zero_bytes(&a[base..base + 1024]) && zero_bytes(&b[base..base + 1024]) && zero_bytes(&z[base..base + 1024]) {
                continue;
            }
            simd::round1_window(sk, &a[base..base + 1024], &b[base..base + 1024], &z[base..base + 1024], &mut w);
            simd::axpy(&mut acc, &w, eo[x]);
        }
        acc
    });
    let mut acc = vec![F::ZERO; 192];
    for p in parts {
        for i in 0..192 {
            acc[i] += p[i];
        }
    }
    let mut r = R1 { pab: [F::ZERO; 64], bank: [[F::ZERO; 64]; 2] };
    for i in 0..64 {
        r.pab[i] = acc[i] * sk.c_pin;
        r.bank[0][i] = acc[64 + i] * sk.c_pin;
        r.bank[1][i] = acc[128 + i] * sk.c_pin;
    }
    r
}

/// `P^z` on `Λ` from the banks: `P^z(Λᵢ) = Σ_σ L^S_σ(Λᵢ) (bank₀ + bank₁)[σ]`.
pub fn pz_on_lambda(r: &R1) -> [F; 64] {
    let sk = skip();
    let mut out = [F::ZERO; 64];
    for i in 0..64 {
        let mut s = F::ZERO;
        for sg in 0..64 {
            s += (r.bank[0][sg] + r.bank[1][sg]).mulb(sk.phi8[sk.mlam[i][sg] as usize]);
        }
        out[i] = s;
    }
    out
}

/// The fold tables at `λ`: `T_b[v] = Σ_{j: v_j = 1} L^S_{8b+j}(λ)` (8 × 256).
pub fn fold_tables(lambda: F) -> Vec<F> {
    let w = crate::skipdom::lagrange_weights(&skip().s_pts, lambda);
    let mut t = vec![F::ZERO; 8 * 256];
    for b in 0..8 {
        for v in 1..256usize {
            let low = v & v.wrapping_neg();
            t[b * 256 + v] = t[b * 256 + (v ^ low)] + w[8 * b + low.trailing_zeros() as usize];
        }
    }
    t
}

#[inline(always)]
pub fn fold_row(t: &[F], row: &[u8]) -> F {
    let mut acc = F::ZERO;
    for j in 0..8 {
        acc += t[j * 256 + row[j] as usize];
    }
    acc
}

/// `E(p) = eq(rest, p)` as `lo ⊗ hi` tables.
pub struct EqSplit {
    pub lo: Vec<F>,
    pub hi: Vec<F>,
    pub nlo: usize,
}
impl EqSplit {
    pub fn new(rest: &[F]) -> EqSplit {
        let nlo = rest.len().min(10);
        EqSplit { lo: eq_table(&rest[..nlo]), hi: eq_table(&rest[nlo..]), nlo }
    }
}

/// The first tail round (variable `x₆`) from the bits: `(h(1), h(∞))` over row pairs, with the
/// rows folded at `λ` on the fly. `rest` = the coordinates of `x₇ … x_{m−1}`; blocks `≥ used` are zero.
pub fn round_x6(t: &[F], a: &[u8], b: &[u8], rest: &[F], used: usize) -> (F, F) {
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    // pair p is rows 2p, 2p+1; a block has 256 rows
    let used_h = used.saturating_mul(128).div_ceil(1 << nlo);
    let parts = par::map_chunks(es.hi.len().min(used_h), 1, |lo, hi| {
        let (mut s1, mut si) = (FAcc::default(), FAcc::default());
        for h in lo..hi {
            // a pair range whose a or b rows are all zero adds nothing
            let (p0, p1) = (16 * (h << nlo), 16 * ((h + 1) << nlo));
            if zero_bytes(&a[p0..p1]) || zero_bytes(&b[p0..p1]) {
                continue;
            }
            let (i1, ii) = simd::x6_inner(t, a, b, h << nlo, &es.lo);
            s1.mac(es.hi[h], i1);
            si.mac(es.hi[h], ii);
        }
        (s1, si)
    });
    let (mut s1, mut si) = (FAcc::default(), FAcc::default());
    for (x, y) in parts {
        s1.add(&x);
        si.add(&y);
    }
    (s1.reduce(), si.reduce())
}

/// After `s₁`: the folded tables `A'[p] = A(2p) + s₁(A(2p) + A(2p+1))` from the bits (blocks `≥ used`
/// are zero: their `128·used …` entries are zero).
pub fn fold_x6(t: &[F], a: &[u8], s1: F, used: usize) -> Vec<F> {
    let n = a.len() / 16;
    let mut out: Vec<F> = par::uninit_vec(n);
    let used_p = used.saturating_mul(128);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| {
        // sub-chunks of 1024 pairs; zero rows fold to zero (`t[·][0] = 0`)
        for (i, sub) in ch.chunks_mut(1 << 10).enumerate() {
            let o = off + (i << 10);
            if o >= used_p || zero_bytes(&a[16 * o..16 * (o + sub.len())]) {
                sub.iter_mut().for_each(|x| *x = F::ZERO);
            } else {
                simd::x6_fold(t, a, o, s1, sub)
            }
        }
    });
    out
}

/// All bytes zero (word at a time).
#[inline]
pub fn zero_bytes(s: &[u8]) -> bool {
    let (h, m, t) = unsafe { s.align_to::<u64>() };
    h.iter().all(|&x| x == 0) && m.iter().all(|&x| x == 0) && t.iter().all(|&x| x == 0)
}

fn zero_f(s: &[F]) -> bool {
    s.iter().all(|x| x.is_zero())
}

/// A later tail round on tables: `(h(1), h(∞))`. Entries `≥ live` of both tables are zero.
pub fn round_tab(a: &[F], b: &[F], rest: &[F], live: usize) -> (F, F) {
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    let parts = par::map_chunks(es.hi.len().min(live.div_ceil(2 << nlo)), 1, |lo, hi| {
        let (mut s1, mut si) = (FAcc::default(), FAcc::default());
        for h in lo..hi {
            let (sa, sb) = (&a[(h << nlo) * 2..((h + 1) << nlo) * 2], &b[(h << nlo) * 2..((h + 1) << nlo) * 2]);
            if zero_f(sa) || zero_f(sb) {
                continue;
            }
            let (i1, ii) = simd::zc_inner(sa, sb, &es.lo);
            s1.mac(es.hi[h], i1);
            si.mac(es.hi[h], ii);
        }
        (s1, si)
    });
    let (mut s1, mut si) = (FAcc::default(), FAcc::default());
    for (x, y) in parts {
        s1.add(&x);
        si.add(&y);
    }
    (s1.reduce(), si.reduce())
}

/// `h(0)` from the claim: `(1 + r) h(0) + r h(1) = claim`.
pub fn h0_from_claim(claim: F, r: F, h1: F) -> F {
    (claim + r * h1) * (F::ONE + r).inv()
}

/// The degree-3 message `(c₀, c₁, c₂)` of `g(X) = P·(1 + r + X)·H(X)` from `H(0), H(1), H(∞)`
/// (`c₃ = P·H(∞)` is the verifier's `claim + c₁ + c₂`).
pub fn zc_coeffs(p: F, r: F, h0: F, h1: F, hinf: F) -> [F; 3] {
    let e0 = F::ONE + r;
    let h1p = h0 + h1 + hinf;
    [p * e0 * h0, p * (h0 + e0 * h1p), p * (h1p + e0 * hinf)]
}

#[cfg(test)]
mod pass11_tests {
    use super::*;

    /// Round 1 with zero windows skipped equals the sum over every window (pass 11).
    #[test]
    fn round1_zero_windows_skipped_equal() {
        let r_out: Vec<F> = (0..4u64).map(|i| F::new(0x9e37_79b9 ^ (i * 77), i + 3)).collect();
        let nw = 1usize << r_out.len();
        let mut s = 0xfeed_beefu64;
        let mut bytes = |zero: bool| -> Vec<u8> {
            (0..nw * 1024)
                .map(|i| {
                    s ^= s << 13;
                    s ^= s >> 7;
                    s ^= s << 17;
                    if zero && (i / 1024) % 3 != 1 { 0 } else { s as u8 }
                })
                .collect()
        };
        let (a, b, z) = (bytes(true), bytes(true), bytes(true));
        let got = round1(&a, &b, &z, &r_out, nw);
        let sk = skip();
        let eo = eq_table(&r_out);
        let mut acc = vec![F::ZERO; 192];
        let mut w = [F::ZERO; 192];
        for x in 0..nw {
            simd::round1_window(sk, &a[x * 1024..x * 1024 + 1024], &b[x * 1024..x * 1024 + 1024], &z[x * 1024..x * 1024 + 1024], &mut w);
            for i in 0..192 {
                acc[i] += w[i] * eo[x];
            }
        }
        for i in 0..64 {
            assert_eq!(got.pab[i], acc[i] * sk.c_pin);
            assert_eq!(got.bank[0][i], acc[64 + i] * sk.c_pin);
            assert_eq!(got.bank[1][i], acc[128 + i] * sk.c_pin);
        }
    }
}
