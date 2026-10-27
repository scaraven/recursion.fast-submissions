//! The zerocheck with the univariate skip (blueprint §2.3 Z, paper §4.2–§4.4, App. A), prover side.
//!
//! The witness is viewed as `2^(m−6)` rows of 64 bits (`x₀ … x₅`, the skip variables, are the bit
//! within a 64-bit word). Rows `x = (x₆ … x_{m−1})`; the zerocheck point is `r = (ρ₁ … ρ₇, r₈ …)`
//! for `x₆ …` (`skipdom.rs`). Round 1 sends `P^{ab}` and `P^z` on `Λ`; the c-side is computed as
//! two banks split by `x₆` (`bank_b[σ] = Σ_{x: x₆ = b} eq(r, x) z(x, σ)`), which also give the
//! ring-switch partials of the c-claim. Then `m − 6` degree-3 rounds in Gruen's form: round `k`
//! sends `h_k(0), h_k(1), h_k(∞)` of `h_k(X) = Σ eq(r_{>k}, ·) â(λ, s_{<k}, X, ·) b̂(…)`, checked
//! `(1 + r_k) h(0) + r_k h(1) = claim`, next claim `h_k(s_k)`; the final claim is `â · b̂`.
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

/// Round 1 over the whole witness (bytes of `a`, `b`, `z`), with `r_out` the coordinates of
/// `x₁₃ … x_{m−1}` (`m − 13` of them).
pub fn round1(a: &[u8], b: &[u8], z: &[u8], r_out: &[F]) -> R1 {
    let sk = skip();
    let nw = a.len() / 1024;
    assert_eq!(nw, 1 << r_out.len());
    let eo = eq_table(r_out);
    let parts = par::map_chunks(nw, 16, |lo, hi| {
        let mut acc = vec![F::ZERO; 192];
        let mut w = [F::ZERO; 192];
        for x in lo..hi {
            let base = x * 1024;
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
/// rows folded at `λ` on the fly. `rest` = the coordinates of `x₇ … x_{m−1}`.
pub fn round_x6(t: &[F], a: &[u8], b: &[u8], rest: &[F]) -> (F, F) {
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    let parts = par::map_chunks(es.hi.len(), 1, |lo, hi| {
        let (mut s1, mut si) = (FAcc::default(), FAcc::default());
        for h in lo..hi {
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

/// After `s₁`: the folded tables `A'[p] = A(2p) + s₁(A(2p) + A(2p+1))` from the bits.
pub fn fold_x6(t: &[F], a: &[u8], s1: F) -> Vec<F> {
    let n = a.len() / 16;
    let mut out: Vec<F> = par::uninit_vec(n);
    par::for_each_chunk_mut(&mut out, 1 << 12, |off, ch| simd::x6_fold(t, a, off, s1, ch));
    out
}

/// A later tail round on tables: `(h(1), h(∞))`.
pub fn round_tab(a: &[F], b: &[F], rest: &[F]) -> (F, F) {
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    let parts = par::map_chunks(es.hi.len(), 1, |lo, hi| {
        let (mut s1, mut si) = (FAcc::default(), FAcc::default());
        for h in lo..hi {
            let (i1, ii) = simd::zc_inner(&a[(h << nlo) * 2..((h + 1) << nlo) * 2], &b[(h << nlo) * 2..((h + 1) << nlo) * 2], &es.lo);
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
