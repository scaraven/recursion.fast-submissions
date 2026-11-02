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
/// blocks past its length) and contribute nothing, so only the first `used` are read. Pass 12:
/// the tower-form window (`simd::r1::window_t`) and the windows' `eq` weights accumulated
/// unreduced (`simd::mac_u`); `round1_ref` is pass 11's.
pub fn round1(a: &[u8], b: &[u8], z: &[u8], r_out: &[F], used: usize) -> R1 {
    round1_with(a, b, z, r_out, used, false)
}

/// Pass 11's round 1 (the reference): `simd::round1_window_ref`, reduced `axpy` per window.
pub fn round1_ref(a: &[u8], b: &[u8], z: &[u8], r_out: &[F], used: usize) -> R1 {
    round1_with(a, b, z, r_out, used, true)
}

fn round1_with(a: &[u8], b: &[u8], z: &[u8], r_out: &[F], used: usize, reference: bool) -> R1 {
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
        let mut accu = vec![0u128; 576];
        let mut w = [F::ZERO; 192];
        for x in lo..hi {
            let base = x * 1024;
            if skip0 && zero_bytes(&a[base..base + 1024]) && zero_bytes(&b[base..base + 1024]) && zero_bytes(&z[base..base + 1024]) {
                continue;
            }
            let (wa, wb, wz) = (&a[base..base + 1024], &b[base..base + 1024], &z[base..base + 1024]);
            if reference {
                simd::round1_window_ref(sk, wa, wb, wz, &mut w);
                simd::axpy(&mut acc, &w, eo[x]);
            } else {
                simd::round1_window(sk, wa, wb, wz, &mut w);
                simd::mac_u(&mut accu, &w, eo[x]);
            }
        }
        if !reference {
            acc = simd::red_u(&accu);
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

// ---------------------------------------------------------------- Z3 by lookahead (pass PA)

/// The lookahead sums of two variables `(k, k+1)` (pass PA; Flock `yukon-optimizations.tex`
/// §cascade, `multilinear.rs` `LookaheadSums`). Over the groups `u` of four positions `v = X + 2Y`
/// (`a_{XY}` the value at `X + 2Y + 4u`), weighted by `e(u) = eq(r_{>k+1}, u)`:
/// `[s10, sinf0, c0, t11, c2, d0, dt, d2] = Σ_u e(u)·[a₁₀b₁₀, Δ₀ᵃΔ₀ᵇ, a₀₁b₀₁, a₁₁b₁₁, Δ₁ᵃΔ₁ᵇ,
/// (a₀₀+a₀₁)(b₀₀+b₀₁), (a₁₀+a₁₁)(b₁₀+b₁₁), (Δ₀ᵃ+Δ₁ᵃ)(Δ₀ᵇ+Δ₁ᵇ)]` with `Δ_Y = a_{0Y} + a_{1Y}`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct La(pub [F; 8]);

impl La {
    /// Round `k`'s `(H(1), H(∞))`: the `Y = 0, 1` columns combined by `eq(r_{k+1}, Y)`.
    pub fn first(&self, ry: F) -> (F, F) {
        let s = &self.0;
        let om = F::ONE + ry;
        (om * s[0] + ry * s[3], om * s[1] + ry * s[4])
    }
    /// Round `k+1`'s `(H(1), H(∞))` once `x_k = x`: `Σ e·a′(1)b′(1)` and `Σ e·(a′(0)+a′(1))(…)`
    /// with `a′(Y) = a_{0Y} + x Δ_Y`, quadratics in `x` whose coefficients are the sums (`c₁ =
    /// t11 + c0 + c2`, the value at 1 less the others; likewise `d₁`).
    pub fn second(&self, x: F) -> (F, F) {
        let s = &self.0;
        let (c0, c2) = (s[2], s[4]);
        let (d0, d2) = (s[5], s[7]);
        let (c1, d1) = (s[3] + c0 + c2, s[6] + d0 + d2);
        (c0 + x * (c1 + x * c2), d0 + x * (d1 + x * d2))
    }
}

/// Sub-range of a pass, in groups: zero stretches are skipped at this grain (one block of a
/// pass-0 group range, four of a pass-1 range).
const SUB: usize = 64;

fn la_total(parts: Vec<[FAcc; 8]>) -> La {
    let mut s = [F::ZERO; 8];
    for p in parts {
        for k in 0..8 {
            s[k] += p[k].reduce();
        }
    }
    La(s)
}

/// Per `eq` high index `h`, the inner sums of its sub-ranges (unreduced) reduced once and weighted.
fn la_weigh(acc: &mut [FAcc; 8], hi: F, inner: &[FAcc; 8]) {
    for k in 0..8 {
        acc[k].mac(hi, inner[k].reduce());
    }
}

fn add8(x: &mut [FAcc; 8], y: &[FAcc; 8]) {
    for k in 0..8 {
        x[k].add(&y[k]);
    }
}

/// Pass 0: the lookahead sums of `x₆, x₇` from the bits (groups of four rows), `rest = r[2..]`;
/// groups `≥ live_g` are zero.
fn la_pass_bits0(t: &[F], a: &[u8], b: &[u8], rest: &[F], live_g: usize) -> La {
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    let parts = par::map_chunks(live_g.div_ceil(1 << nlo), 1, |h0, h1| {
        let mut acc = [FAcc::default(); 8];
        for h in h0..h1 {
            let (gl, gh) = (h << nlo, ((h + 1) << nlo).min(live_g));
            let mut inner = [FAcc::default(); 8];
            let mut any = false;
            for s0 in (gl..gh).step_by(SUB) {
                let s1 = (s0 + SUB).min(gh);
                // a group range whose a or b rows are all zero adds nothing
                if zero_bytes(&a[32 * s0..32 * s1]) || zero_bytes(&b[32 * s0..32 * s1]) {
                    continue;
                }
                add8(&mut inner, &simd::la_bits(t, a, b, s0, &es.lo[s0 - gl..s1 - gl]));
                any = true;
            }
            if any {
                la_weigh(&mut acc, es.hi[h], &inner);
            }
        }
        acc
    });
    la_total(parts)
}

/// The two output tables of a pass, written by disjoint group ranges in parallel.
struct Out2(par::SyncPtr<F>, par::SyncPtr<F>);
impl Out2 {
    /// The outputs of groups `s0 … s1` (four a group).
    #[allow(clippy::mut_from_ref)]
    unsafe fn at(&self, s0: usize, s1: usize) -> (&mut [F], &mut [F]) {
        (std::slice::from_raw_parts_mut(self.0 .0.add(4 * s0), 4 * (s1 - s0)), std::slice::from_raw_parts_mut(self.1 .0.add(4 * s0), 4 * (s1 - s0)))
    }
}

/// Pass 1: `x₆, x₇` bound at `s` from the bits (four rows an output; `live` = the live outputs, that
/// is pass 0's live groups; outputs `≥ live` are zero and not stored: the tables are the live
/// prefix, `4⌈live/4⌉` long), and the lookahead sums of `x₈, x₉` over the outputs, `rest = r[4..]`.
fn la_pass_bits1(t: &[F], a: &[u8], b: &[u8], s: (F, F), rest: &[F], live: usize) -> (Vec<F>, Vec<F>, La) {
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    let ng = live.div_ceil(4);
    let (mut oa, mut ob): (Vec<F>, Vec<F>) = (par::uninit_vec(4 * ng), par::uninit_vec(4 * ng));
    let out = Out2(par::SyncPtr(oa.as_mut_ptr()), par::SyncPtr(ob.as_mut_ptr()));
    let parts = par::map_chunks(ng.div_ceil(1 << nlo), 1, |h0, h1| {
        let mut acc = [FAcc::default(); 8];
        for h in h0..h1 {
            let (gl, gh) = (h << nlo, ((h + 1) << nlo).min(ng));
            let mut inner = [FAcc::default(); 8];
            let mut any = false;
            for s0 in (gl..gh).step_by(SUB) {
                let s1 = (s0 + SUB).min(gh);
                // SAFETY: the group ranges of the chunks are disjoint and inside `0 … ng`
                let (xa, xb) = unsafe { out.at(s0, s1) };
                let (za, zb) = (zero_bytes(&a[128 * s0..128 * s1]), zero_bytes(&b[128 * s0..128 * s1]));
                if !za && !zb {
                    add8(&mut inner, &simd::la_fold_bits(t, a, b, s0, &es.lo[s0 - gl..s1 - gl], s, xa, xb));
                    any = true;
                    continue;
                }
                // zero rows fold to zero (`t[·][0] = 0`), and the products of the range are zero
                for (z, src, x) in [(za, a, xa), (zb, b, xb)] {
                    if z {
                        x.fill(F::ZERO);
                    } else {
                        simd::fold2_bits(t, src, 4 * s0, s, x);
                    }
                }
            }
            if any {
                la_weigh(&mut acc, es.hi[h], &inner);
            }
        }
        acc
    });
    (oa, ob, la_total(parts))
}

/// A later pass on the tables (a live prefix, a multiple of 16 long): two pending variables bound
/// at `s` (4 → 1) and the lookahead sums of the next two over the outputs, `rest` their `eq` tail.
fn la_pass_tab(ta: &[F], tb: &[F], s: (F, F), rest: &[F]) -> (Vec<F>, Vec<F>, La) {
    assert!(ta.len() == tb.len() && ta.len() % 16 == 0 && ta.len() <= 16 << rest.len());
    let es = EqSplit::new(rest);
    let nlo = es.nlo;
    let ng = ta.len() / 16;
    let (mut oa, mut ob): (Vec<F>, Vec<F>) = (par::uninit_vec(4 * ng), par::uninit_vec(4 * ng));
    let out = Out2(par::SyncPtr(oa.as_mut_ptr()), par::SyncPtr(ob.as_mut_ptr()));
    let parts = par::map_chunks(ng.div_ceil(1 << nlo), 1, |h0, h1| {
        let mut acc = [FAcc::default(); 8];
        for h in h0..h1 {
            let (gl, gh) = (h << nlo, ((h + 1) << nlo).min(ng));
            let mut inner = [FAcc::default(); 8];
            let mut any = false;
            for s0 in (gl..gh).step_by(SUB) {
                let s1 = (s0 + SUB).min(gh);
                // SAFETY: as in `la_pass_bits1`
                let (xa, xb) = unsafe { out.at(s0, s1) };
                let (ia, ib) = (&ta[16 * s0..16 * s1], &tb[16 * s0..16 * s1]);
                let (za, zb) = (zero_f(ia), zero_f(ib));
                if !za && !zb {
                    add8(&mut inner, &simd::la_fold_tab(ia, ib, &es.lo[s0 - gl..s1 - gl], s, xa, xb));
                    any = true;
                    continue;
                }
                for (z, src, x) in [(za, ia, xa), (zb, ib, xb)] {
                    if z {
                        x.fill(F::ZERO);
                    } else {
                        simd::fold2_tab(src, s, x);
                    }
                }
            }
            if any {
                la_weigh(&mut acc, es.hi[h], &inner);
            }
        }
        acc
    });
    (oa, ob, la_total(parts))
}

/// **Z3 by lookahead** (pass PA; Flock §cascade, §tailfuse, §foldentry): the `n = r.len()` rounds of
/// `eq(r, x)·a_λ(x)·b_λ(x)` over `x = (x₆ …)` from the bit tables `a`, `b` (rows of 64 bits folded at
/// λ by `t`; blocks `≥ used` zero), two rounds per pass:
/// * pass 0 reads the bits once for the lookahead sums of `x₆, x₇` (rounds 0, 1; no table written);
/// * pass 1 reads them again, binds `x₆, x₇` (four rows to one output) and forms the sums of
///   `x₈, x₉` over the outputs while they are in registers;
/// * each later pass binds two variables (4 → 1) and forms the next two rounds' sums;
/// * a last odd round, if any, is `round_tab` on the (at most 8-entry) table.
///
/// `step(k, H_k(1), H_k(∞))` sends round `k`'s message and returns its challenge. Returns `(â, b̂)`
/// at the challenges. The messages are those of `round_x6`/`fold_x6`/`round_tab`/`fold` round by
/// round (`z3_rounds_ref`): every value is the same field element computed in another order.
pub fn z3_rounds(t: &[F], a: &[u8], b: &[u8], r: &[F], used: usize, step: &mut dyn FnMut(usize, F, F) -> F) -> (F, F) {
    let n = r.len();
    assert!(a.len() == 8 << n && b.len() == a.len() && t.len() >= 8 * 256);
    if n < 4 {
        // no shape has `m < 10` (leaves 25 … 32, nodes 31, 32); kept total for the tests
        return z3_rounds_ref(t, a, b, r, used, step);
    }
    let live_g = used.saturating_mul(256).min(1 << n) / 4; // groups of four rows; a block is 256 rows
    let la = {
        let _sp = crate::prof::span("x6.round");
        la_pass_bits0(t, a, b, &r[2..], live_g)
    };
    let (h1, hi) = la.first(r[1]);
    let x0 = step(0, h1, hi);
    let (h1, hi) = la.second(x0);
    let mut pend = (x0, step(1, h1, hi));
    let mut k = 2;
    let mut tabs: Option<(Vec<F>, Vec<F>)> = None; // `None`: still the bits
    while n - k >= 2 {
        let (oa, ob, la) = match tabs.take() {
            None => {
                let _sp = crate::prof::span("x6.fold");
                la_pass_bits1(t, a, b, pend, &r[k + 2..], live_g) // pass 1's outputs: one a pass-0 group
            }
            Some((mut ta, mut tb)) => {
                let _sp = crate::prof::span("tail.fold");
                // the live prefix padded to a whole number of groups (within the table's size)
                let l = ta.len().next_multiple_of(16).min(4 << (n - k));
                ta.resize(l, F::ZERO);
                tb.resize(l, F::ZERO);
                la_pass_tab(&ta, &tb, pend, &r[k + 2..])
            }
        };
        tabs = Some((oa, ob));
        let (h1, hi) = la.first(r[k + 1]);
        let x = step(k, h1, hi);
        let (h1, hi) = la.second(x);
        pend = (x, step(k + 1, h1, hi));
        k += 2;
    }
    let _sp = crate::prof::span("tail.round");
    // the last pending pair bound on the whole (≤ 8-entry) tables, then the odd round, if any
    let (mut ta, mut tb) = tabs.expect("n ≥ 4: pass 1 ran");
    let full = 4 << (n - k);
    ta.resize(full, F::ZERO);
    tb.resize(full, F::ZERO);
    let (mut fa, mut fb) = (vec![F::ZERO; full / 4], vec![F::ZERO; full / 4]);
    simd::fold2_tab(&ta, pend, &mut fa);
    simd::fold2_tab(&tb, pend, &mut fb);
    if n - k == 1 {
        // `live = 2`: the whole table (entries past the live prefix are zero here)
        let (h1, hi) = round_tab(&fa, &fb, &[], 2);
        let x = step(k, h1, hi);
        return (fa[0] + x * (fa[0] + fa[1]), fb[0] + x * (fb[0] + fb[1]));
    }
    (fa[0], fb[0])
}

/// The reference of `z3_rounds`: the leaf's rounds as passes 1–13 made them (`round_x6`, `fold_x6`,
/// then `round_tab` and `fold_f_live` per round on the tables' nonzero prefix).
pub fn z3_rounds_ref(t: &[F], a: &[u8], b: &[u8], r: &[F], used: usize, step: &mut dyn FnMut(usize, F, F) -> F) -> (F, F) {
    let n = r.len();
    let (mut ta, mut tb) = (Vec::new(), Vec::new());
    let mut live = used.saturating_mul(128); // 128 row pairs a block
    for k in 0..n {
        let (h1, hi) = if k == 0 { round_x6(t, a, b, &r[1..], used) } else { round_tab(&ta, &tb, &r[k + 1..], live) };
        let x = step(k, h1, hi);
        if k == 0 {
            ta = fold_x6(t, a, x, used);
            tb = fold_x6(t, b, x, used);
        } else {
            ta = crate::sumcheck::fold_f_live(&ta, x, live);
            tb = crate::sumcheck::fold_f_live(&tb, x, live);
            live = live.div_ceil(2);
        }
    }
    (ta[0], tb[0])
}

type Z3Fn = fn(&[F], &[u8], &[u8], &[F], usize, &mut dyn FnMut(usize, F, F) -> F) -> (F, F);

/// `z3_rounds` against `z3_rounds_ref` on random bits of `2^n` rows with zero stretches, for several
/// `used` (the bits past `used` blocks zeroed, as a segment's are), the challenges derived from the
/// messages: every message and both final values equal (selftest, tests).
pub fn z3_check(n: usize, seed: u64) -> bool {
    let mut s = seed | 1;
    let mut rnd = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let rows = 1usize << n;
    let mut a: Vec<u8> = (0..8 * rows).map(|_| rnd() as u8).collect();
    let mut b: Vec<u8> = (0..8 * rows).map(|_| rnd() as u8).collect();
    // zero stretches: a's rows `rows/4 … 3rows/8`, b's last sixteenth, and one row of each
    a[2 * rows..3 * rows].fill(0);
    b[8 * rows - (rows / 2).max(8)..].fill(0);
    a[8..16].fill(0);
    b[24..32].fill(0);
    let t = fold_tables(F::new(rnd(), rnd()));
    let r: Vec<F> = (0..n).map(|_| F::new(rnd(), rnd())).collect();
    let blocks = rows.div_ceil(256);
    for used in [blocks, blocks.div_ceil(2), 1, blocks + 3] {
        let cut = (256 * 8 * used).min(8 * rows);
        let (mut ua, mut ub) = (a.clone(), b.clone());
        ua[cut..].fill(0);
        ub[cut..].fill(0);
        let go = |f: Z3Fn| {
            let mut log = Vec::new();
            let v = f(&t, &ua, &ub, &r, used, &mut |k, h1, hi| {
                log.push((k, h1, hi));
                (h1 + F::new(k as u64, 3)) * (hi + F::ONE) + F::new(seed, k as u64)
            });
            (log, v)
        };
        let (x, y) = (go(z3_rounds), go(z3_rounds_ref));
        if x != y || x.0.len() != n {
            return false;
        }
    }
    true
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

#[cfg(test)]
mod pass12_tests {
    use super::*;

    /// Pass 12's round 1 (tower window, unreduced accumulation) equals pass 11's, with zero and
    /// unused windows.
    #[test]
    fn round1_matches_ref() {
        let r_out: Vec<F> = (0..5u64).map(|i| F::new(0x51ed_270b ^ (i * 91), 7 * i + 1)).collect();
        let nw = 1usize << r_out.len();
        let mut s = 0x0dd_ba11u64;
        let mut bytes = || -> Vec<u8> {
            (0..nw * 1024)
                .map(|i| {
                    s ^= s << 13;
                    s ^= s >> 7;
                    s ^= s << 17;
                    if (i / 1024) % 4 == 2 { 0 } else { s as u8 }
                })
                .collect()
        };
        let (a, b, z) = (bytes(), bytes(), bytes());
        for used in [nw / 2, nw / 2 - 3, 5] {
            let (x, y) = (round1(&a, &b, &z, &r_out, used), round1_ref(&a, &b, &z, &r_out, used));
            assert!(x.pab == y.pab && x.bank == y.bank, "used {used}");
        }
        if crate::simd::hw_avx2() {
            // the AVX2 windows directly (this VM's tier may be portable)
            let sk = skip();
            let eo = eq_table(&r_out);
            let mut acc = vec![F::ZERO; 192];
            let mut u = vec![0u128; 576];
            let (mut w0, mut w1) = ([F::ZERO; 192], [F::ZERO; 192]);
            for x in 0..nw {
                let o = x * 1024;
                window_portable(sk, &a[o..o + 1024], &b[o..o + 1024], &z[o..o + 1024], &mut w0);
                unsafe { simd::r1::window_t(sk, &a[o..o + 1024], &b[o..o + 1024], &z[o..o + 1024], &mut w1) };
                assert_eq!(w0, w1);
                for i in 0..192 {
                    acc[i] += w0[i] * eo[x];
                }
                simd::mac_u_ref(&mut u, &w1, eo[x]);
            }
            assert_eq!(simd::red_u(&u), acc);
        }
    }
}

#[cfg(test)]
mod pa_tests {
    /// Pass PA's lookahead rounds equal the round-by-round ones (every message, both final values),
    /// even and odd `n` (2 and 3: the fallback), several `used`, zero stretches; `n = 17` splits the
    /// passes over several `eq` high indices. In the current tier (`FLOCK_TIER`; the selftest covers every tier).
    #[test]
    fn z3_lookahead_matches_ref() {
        for n in 2..=13 {
            assert!(super::z3_check(n, 0x5eed + n as u64), "n = {n}");
        }
        assert!(super::z3_check(17, 77), "n = 17");
    }
}
