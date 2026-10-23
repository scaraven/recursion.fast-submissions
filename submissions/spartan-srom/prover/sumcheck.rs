//! Honest sumcheck provers (BLUEPRINT-R1 §3, §4.4). Every sumcheck binds variable 0 first; a
//! round polynomial is its coefficients, ascending (degree 3 for the outer sumcheck, 2 for the
//! others). The round polynomial is the unique one of the definition, so any correct way of
//! computing it gives the same bytes; the code below avoids materialising `E` tables over the
//! full cube in the first three rounds by reading the bit tables through lookup tables of
//! `Σ_{b<2^l} p_b eq(r_{<l}, b)` over bit patterns `p` (the "small-value" rounds).

use crate::chain::{pub_bit, row_factors, Shape, Witness};
use crate::circuit::{Circuit, BLOCK, CPOS};
use crate::field::{ETab, E};
use crate::mle::{coeffs2, eq_table, horner};
use crate::par;
use crate::transcript::Transcript;

pub const KIND_OUTER: u8 = 0x03;
pub const KIND_INNER: u8 = 0x05;
pub const KIND_RS: u8 = 0x07;

pub fn bytes_of(es: &[E]) -> Vec<u8> {
    let mut v = Vec::with_capacity(24 * es.len());
    for e in es {
        v.extend_from_slice(&e.to_bytes());
    }
    v
}

/// `T[p] = Σ_{b : bit b of p} eqr[b]` for every pattern `p` of `eqr.len()` bits.
fn pattern_table(eqr: &[E]) -> Vec<E> {
    let w = eqr.len();
    let mut t = vec![E::ZERO; 1 << w];
    for p in 1..(1usize << w) {
        let low = p.trailing_zeros() as usize;
        t[p] = t[p & (p - 1)] + eqr[low];
    }
    t
}

#[inline(always)]
fn chunk_bits(v: &[u64], off: usize, width: usize) -> usize {
    // width ≤ 16 and aligned: the chunk lies in one word
    ((v[off >> 6] >> (off & 63)) as usize) & ((1usize << width) - 1)
}

fn fold(v: &[E], r: E) -> Vec<E> {
    let half = v.len() / 2;
    if half >= 1 << 14 {
        let tab = ETab::new(r);
        return par::collect_vec(half, 1 << 12, |i| {
            let a = v[2 * i];
            a + tab.mul(a + v[2 * i + 1])
        });
    }
    par::collect_vec(half, 1 << 10, |i| {
        let a = v[2 * i];
        a + r * (a + v[2 * i + 1])
    })
}

/// Split `eq(τ_{vars}, ·)` into a low and a high table: of about the same size when `balanced`
/// (each round then builds `O(2^{|vars|/2})` entries), else with the low table as large as allowed
/// (the bucketed rounds combine their buckets once per block of the low table). At most 12
/// variables low.
fn eq_split(vars: &[E], balanced: bool) -> (Vec<E>, Vec<E>, usize) {
    let hb = if balanced { vars.len().div_ceil(2) } else { vars.len() }.min(12);
    (eq_table(&vars[..hb]), eq_table(&vars[hb..]), hb)
}

/// `Σ_{y < 2^rem} eq_lo[y mod 2^hb]·eq_hi[y >> hb]·f(y)`, in parallel over aligned ranges of `y`.
/// `body(y0, y1)` returns `Σ_{y ∈ [y0, y1)} eq_lo[y mod 2^hb]·f(y)` (each component) for a range
/// inside one block of `2^hb`; ranges are aligned to `min(1024, 2^hb)`.
fn eq_sum<const K: usize>(eq_hi: &[E], hb: usize, body: impl Fn(usize, usize) -> [E; K] + Sync) -> [E; K] {
    let ny = eq_hi.len() << hb;
    let mut k = 1usize;
    while k < 4 * par::threads() && ny / (2 * k) >= 1 << 10 {
        k *= 2;
    }
    let size = ny / k;
    let parts = par::map_chunks(k, 1, |c0, c1| {
        let mut tot = [E::ZERO; K];
        for c in c0..c1 {
            let (mut y, end) = (c * size, (c + 1) * size);
            while y < end {
                let hi = y >> hb;
                let stop = end.min((hi + 1) << hb);
                let sv = body(y, stop);
                for i in 0..K {
                    if !sv[i].is_zero() {
                        tot[i] += eq_hi[hi] * sv[i];
                    }
                }
                y = stop;
            }
        }
        tot
    });
    let mut out = [E::ZERO; K];
    for p in parts {
        for i in 0..K {
            out[i] += p[i];
        }
    }
    out
}

/// `T_g[p] = Σ_{i : bit i of p} eqr[8g + i]` for the bytes `p` (`g < |eqr|/8`): the byte tables of
/// the `F₂`-linear map `x ↦ Σ_b x_b eqr[b]` on bit patterns of `|eqr|` bits.
fn byte_tables(eqr: &[E]) -> Vec<E> {
    let mut t = Vec::with_capacity(32 * eqr.len());
    for g in eqr.chunks(8) {
        t.extend(pattern_table(g));
    }
    t
}

/// The linear map of `byte_tables` at the pattern with bytes `p`.
#[inline(always)]
fn lin(bt: &[E], p: &[u8]) -> E {
    let mut acc = E::ZERO;
    for (g, &x) in p.iter().enumerate() {
        acc += bt[256 * g + x as usize];
    }
    acc
}

/// The linear map of `byte_tables` at the pattern `p ⊕ q`.
#[inline(always)]
fn lin2(bt: &[E], p: &[u8], q: &[u8]) -> E {
    let mut acc = E::ZERO;
    for (g, (&x, &y)) in p.iter().zip(q).enumerate() {
        acc += bt[256 * g + (x ^ y) as usize];
    }
    acc
}

const _: () = assert!(cfg!(target_endian = "little"), "bit tables are read as little-endian bytes");

/// The bytes of a bit table: byte `i` holds bits `8i … 8i + 7`.
fn as_bytes(v: &[u64]) -> &[u8] {
    // SAFETY: `u64` has no padding, `u8` no alignment; little-endian (asserted above).
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, 8 * v.len()) }
}

/// `1/x` for each non-zero `x` (one inversion, Montgomery's trick); `None` for zero.
fn batch_inv(v: &[E]) -> Vec<Option<E>> {
    let mut acc = E::ONE;
    let mut pre = Vec::with_capacity(v.len());
    for &x in v {
        pre.push(acc);
        if !x.is_zero() {
            acc *= x;
        }
    }
    let mut inv = acc.inv();
    let mut out = vec![None; v.len()];
    for i in (0..v.len()).rev() {
        if !v[i].is_zero() {
            out[i] = Some(inv * pre[i]);
            inv *= v[i];
        }
    }
    out
}

/// The round from which the outer sumcheck keeps its tables over `E` (folded each round); before
/// it, each round reads `A(r_{<l}, ·)`, `B`, `C` from the bit tables through `byte_tables` of
/// `eq(r_{<l}, ·)`, so the `E` tables have `2^{ℓ − LATE}` entries instead of `2^{ℓ − 4}`.
const LATE: usize = 7;

pub struct OuterOut {
    pub polys: Vec<[E; 4]>,
    pub r_x: Vec<E>,
    pub v: [E; 3],
}

/// The outer sumcheck: `0 = Σ_x eq(τ, x)·((Az)(x)(Bz)(x) + (Cz)(x))`, `ℓ_x` rounds, degree 3.
///
/// Round `l` sends `g(X) = prefix·(1 + τ_l + X)·h(X)` with `h(X) = Σ_y eq(τ_{>l}, y)·(A·B + C)(r_{<l},
/// X, y)` (degree 2). Only `h(0)` and `h(∞)` are summed: `g(0) + g(1)` is the claim, so `h(1)`
/// follows (`τ_l ≠ 0`; otherwise it is summed too), and in round 0, `A·B = C` on the cube (the honest
/// witness) gives `h(0) = h(1) = 0`. The polynomial is the unique one of the definition, so the
/// bytes do not depend on how it is computed.
///
/// `bits` are the witness's bit tables `A`, `B`, `C` (`Witness::a`, `b`, `c`); each is freed once
/// its `E` table is made (round `LATE − 1`), unless `keep_bits`.
pub fn outer(sh: &Shape, bits: &mut [Vec<u64>; 3], tau: &[E], tr: &mut Transcript, keep_bits: bool) -> OuterOut {
    let ell = sh.ell;
    let tinv = batch_inv(&tau[..ell]);
    let mut r: Vec<E> = vec![];
    let mut polys = vec![];
    let mut claim = E::ZERO;
    let mut prefix = E::ONE;
    let mut tabs: Option<[Vec<E>; 3]> = None;
    let verbose = std::env::var("SPARTAN_VERBOSE").map(|v| v == "2").unwrap_or(false);
    for l in 0..ell {
        let tl = std::time::Instant::now();
        let (ta, tb, tc) = (&bits[0][..], &bits[1][..], &bits[2][..]);
        let (ba, bb, bc) = (as_bytes(ta), as_bytes(tb), as_bytes(tc));
        let (eq_lo, eq_hi, hb) = eq_split(&tau[l + 1..ell], l == 0 || l >= LATE);
        let mask = (1usize << hb) - 1;
        let eq_lo = &eq_lo;
        let need1 = tinv[l].is_none();
        // [h(0), h(1) if need1, h(∞)]
        let hv: [E; 3] = if l == 0 {
            // A·B = C on the cube: only the leading coefficient (bits: A(1)+A(0) and B(1)+B(0))
            let s = eq_sum(&eq_hi, hb, |y0, y1| {
                let mut s = E::ZERO;
                for wi in y0 / 32..y1 / 32 {
                    let (a, b) = (ta[wi], tb[wi]);
                    let mut d = (a ^ (a >> 1)) & (b ^ (b >> 1)) & 0x5555_5555_5555_5555;
                    let base = (32 * wi) & mask;
                    while d != 0 {
                        s += eq_lo[base + (d.trailing_zeros() as usize >> 1)];
                        d &= d - 1;
                    }
                }
                [s]
            });
            [E::ZERO, E::ZERO, s[0]]
        } else if l == 1 {
            // bit-sliced: with r = r_0 and bits a_{bX} = A(b, X, y), A(r, 0, y) = a00 + r·(a00 + a10)
            // and A(r, ∞, y) = u + r·δu (u = a00 + a01, δu = u + a10 + a11), likewise B and C; with
            // A·B = C on the cube, h(0) = r·Σ e·[a00 δb + b00 δa + δc] + r²·Σ e·[δa δb] and
            // h(∞) = Σ e·[u v] + r·Σ e·[u δv + v δu] + r²·Σ e·[δu δv]: sums of eq over bit masks
            let r0 = r[0];
            let s = eq_sum(&eq_hi, hb, |y0, y1| {
                const N: u64 = 0x1111_1111_1111_1111;
                let mut acc = [E::ZERO; 7];
                for wi in y0 / 16..y1 / 16 {
                    let (a, b, c) = (ta[wi], tb[wi], tc[wi]);
                    let (a00, a10, a01, a11) = (a & N, (a >> 1) & N, (a >> 2) & N, (a >> 3) & N);
                    let (b00, b10, b01, b11) = (b & N, (b >> 1) & N, (b >> 2) & N, (b >> 3) & N);
                    let (c00, c10, c01, c11) = (c & N, (c >> 1) & N, (c >> 2) & N, (c >> 3) & N);
                    let (da, db, dc) = (a00 ^ a10, b00 ^ b10, c00 ^ c10);
                    let (u, v) = (a00 ^ a01, b00 ^ b01);
                    let (du, dv) = (u ^ a10 ^ a11, v ^ b10 ^ b11);
                    let mut masks = [(a00 & db) ^ (b00 & da) ^ dc, da & db, u & v, (u & dv) ^ (v & du), du & dv, 0, 0];
                    if need1 {
                        let (da1, db1) = (a01 ^ a11, b01 ^ b11);
                        masks[5] = (a01 & db1) ^ (b01 & da1) ^ c01 ^ c11;
                        masks[6] = da1 & db1;
                    }
                    let base = (16 * wi) & mask;
                    for (m, x) in masks.iter().zip(acc.iter_mut()) {
                        let mut m = *m;
                        while m != 0 {
                            *x += eq_lo[base + (m.trailing_zeros() as usize >> 2)];
                            m &= m - 1;
                        }
                    }
                }
                acc
            });
            let r2 = r0 * r0;
            [r0 * s[0] + r2 * s[1], r0 * s[5] + r2 * s[6], s[2] + r0 * s[3] + r2 * s[4]]
        } else if l < 3 {
            // pattern rounds on the bit tables, bucketed by pattern
            let pw = 1usize << l;
            let t = pattern_table(&eq_table(&r[..l]));
            let np = 1usize << pw;
            let mut pt = vec![E::ZERO; np * np];
            for pa in 0..np {
                for pb in 0..np {
                    pt[pa * np + pb] = t[pa] * t[pb];
                }
            }
            let (t, pt) = (&t, &pt);
            eq_sum(&eq_hi, hb, |y0, y1| {
                let m = np - 1;
                // two copies of every bucket, for even and odd y (independent updates)
                let mut ab = [[[E::ZERO; 2]; 256]; 2];
                let mut ab1 = [E::ZERO; 256];
                let mut cb = [[E::ZERO; 16]; 2];
                let mut cb1 = [E::ZERO; 16];
                for y in y0..y1 {
                    let off = y << (l + 1);
                    let ca = chunk_bits(ta, off, 2 * pw);
                    let cbb = chunk_bits(tb, off, 2 * pw);
                    let cc = chunk_bits(tc, off, 2 * pw);
                    let (a0, a1) = (ca & m, ca >> pw);
                    let (b0, b1) = (cbb & m, cbb >> pw);
                    let e = eq_lo[y & mask];
                    let (abk, cbk) = (&mut ab[y & 1], &mut cb[y & 1]);
                    abk[a0 * np + b0][0] += e;
                    abk[(a0 ^ a1) * np + (b0 ^ b1)][1] += e;
                    cbk[cc & m] += e; // C is linear in X: no leading term
                    if need1 {
                        ab1[a1 * np + b1] += e;
                        cb1[cc >> pw] += e;
                    }
                }
                let mut sv = [E::ZERO; 3];
                for key in 0..np * np {
                    if pt[key].is_zero() {
                        continue;
                    }
                    let (x0, xi) = (ab[0][key][0] + ab[1][key][0], ab[0][key][1] + ab[1][key][1]);
                    for (c, x) in [(0, x0), (1, ab1[key]), (2, xi)] {
                        if !x.is_zero() {
                            sv[c] += x * pt[key];
                        }
                    }
                }
                for key in 1..np {
                    for (c, x) in [(0, cb[0][key] + cb[1][key]), (1, cb1[key])] {
                        if !x.is_zero() {
                            sv[c] += x * t[key];
                        }
                    }
                }
                sv
            })
        } else if l < LATE {
            // the values from the bit tables: 2^l bits per half, read as bytes
            let bt = byte_tables(&eq_table(&r[..l]));
            let bt = &bt;
            let gsz = 1usize << (l - 3);
            eq_sum(&eq_hi, hb, |y0, y1| {
                let mut sv = [E::ZERO; 3];
                // the buckets save two products per y and cost 2·256·gsz to combine
                if need1 || y1 - y0 < 512 * gsz {
                    for y in y0..y1 {
                        let o0 = y << (l - 2);
                        let o1 = o0 + gsz;
                        let (pa0, pa1) = (&ba[o0..o1], &ba[o1..o1 + gsz]);
                        let (pb0, pb1) = (&bb[o0..o1], &bb[o1..o1 + gsz]);
                        let (pc0, pc1) = (&bc[o0..o1], &bc[o1..o1 + gsz]);
                        let e = eq_lo[y & mask];
                        sv[0] += e * (lin(bt, pa0) * lin(bt, pb0) + lin(bt, pc0));
                        if need1 {
                            sv[1] += e * (lin(bt, pa1) * lin(bt, pb1) + lin(bt, pc1));
                        }
                        sv[2] += e * (lin2(bt, pa0, pa1) * lin2(bt, pb0, pb1));
                    }
                    return sv;
                }
                // A's pattern bytes as buckets: Σ_y e·A·B = Σ_{g,p} T_g[p]·Σ_{y : A's byte g = p} e·B,
                // and C's alongside A₀'s (Σ e·C₀ = Σ_{g,p} T_g[p]·Σ_{C's byte g = p} e)
                let mut bk0 = vec![E::ZERO; 256 * gsz];
                let mut bki = vec![E::ZERO; 256 * gsz];
                for y in y0..y1 {
                    let o0 = y << (l - 2);
                    let o1 = o0 + gsz;
                    let (pa0, pa1) = (&ba[o0..o1], &ba[o1..o1 + gsz]);
                    let (pb0, pb1) = (&bb[o0..o1], &bb[o1..o1 + gsz]);
                    let pc0 = &bc[o0..o1];
                    let e = eq_lo[y & mask];
                    let eb0 = e * lin(bt, pb0);
                    let ebi = e * lin2(bt, pb0, pb1);
                    for g in 0..gsz {
                        bk0[256 * g + pa0[g] as usize] += eb0;
                        bk0[256 * g + pc0[g] as usize] += e;
                        bki[256 * g + (pa0[g] ^ pa1[g]) as usize] += ebi;
                    }
                }
                for (i, &t) in bt.iter().enumerate() {
                    if !bk0[i].is_zero() {
                        sv[0] += t * bk0[i];
                    }
                    if !bki[i].is_zero() {
                        sv[2] += t * bki[i];
                    }
                }
                sv
            })
        } else {
            let [ta, tb, tc] = tabs.as_ref().unwrap();
            eq_sum(&eq_hi, hb, |y0, y1| {
                let mut sv = [E::ZERO; 3];
                for y in y0..y1 {
                    let (a0, a1) = (ta[2 * y], ta[2 * y + 1]);
                    let (b0, b1) = (tb[2 * y], tb[2 * y + 1]);
                    let e = eq_lo[y & mask];
                    sv[0] += e * (a0 * b0 + tc[2 * y]);
                    sv[2] += e * ((a0 + a1) * (b0 + b1));
                    if need1 {
                        sv[1] += e * (a1 * b1 + tc[2 * y + 1]);
                    }
                }
                sv
            })
        };
        // g = prefix·(a + X)·h(X), a = 1 + τ_l; with H = prefix·h: g(0) = a·H(0), g(1) = τ_l·H(1)
        let a = E::ONE + tau[l];
        let h0 = prefix * hv[0];
        let hinf = prefix * hv[2];
        let h1 = match tinv[l] {
            Some(ti) => (claim + a * h0) * ti,
            None => prefix * hv[1],
        };
        let h1c = h1 + h0 + hinf; // the coefficient of X in H
        let g = [a * h0, a * h1c + h0, a * hinf + h1c, hinf];
        debug_assert_eq!(g[1] + g[2] + g[3], claim, "outer round {l}");
        tr.absorb(KIND_OUTER, &bytes_of(&g));
        let rl = tr.squeeze_e();
        claim = horner(&g, rl);
        prefix *= E::ONE + tau[l] + rl;
        r.push(rl);
        polys.push(g);
        if l + 1 == LATE {
            // materialise the three tables with LATE variables bound (each bit table freed after)
            let bt = byte_tables(&eq_table(&r[..LATE]));
            let gsz = 1usize << (LATE - 3);
            let mut made = Vec::with_capacity(3);
            for b in bits.iter_mut() {
                let bytes = as_bytes(b);
                made.push(par::collect_vec(1usize << (ell - LATE), 1 << 12, |y| lin(&bt, &bytes[y * gsz..(y + 1) * gsz])));
                if !keep_bits {
                    *b = Vec::new();
                }
            }
            let tc = made.pop().unwrap();
            let tb = made.pop().unwrap();
            tabs = Some([made.pop().unwrap(), tb, tc]);
        } else if l >= LATE {
            // one old table at a time is dropped as its fold is made
            let [ta, tb, tc] = tabs.take().unwrap();
            let fa = fold(&ta, rl);
            drop(ta);
            let fb = fold(&tb, rl);
            drop(tb);
            let fc = fold(&tc, rl);
            drop(tc);
            tabs = Some([fa, fb, fc]);
        }
        if verbose {
            eprintln!("  outer round {l}: {:.4}s", tl.elapsed().as_secs_f64());
        }
    }
    let [ta, tb, tc] = tabs.unwrap();
    OuterOut { polys, r_x: r, v: [ta[0], tb[0], tc[0]] }
}

pub struct InnerOut {
    pub polys: Vec<[E; 3]>,
    pub r_y: Vec<E>,
    pub final_m: E,
    pub final_z: E,
}

/// The inner sumcheck: `v_A + ρ v_B + ρ² v_C = Σ_y M̃ρ(r_x, y)·z(y)`, `ℓ_y` rounds, degree 2.
///
/// On `top = 0` the table is a sum of three tensors `Σ_i P_i(j)·γ_i(t')` (region 0 through the
/// transpose walk; the wiring and tail rows through `eq(r_kj, ·)` on the output and message
/// ranges); on `top = 1` it is supported on `t' = 0`, `j < 513` (`Mpub`). The first 14 rounds
/// bind `j`; the last `κ + 1` run on a dense table over `(t', top)`.
///
/// The first 14 rounds sum over `t'` before `j` (Flock §4.1's block-diagonal collapse): with
/// `Z_i(j) = Σ_{t'} γ_i(t') z(j, t')`, the part `top = 0` is `Σ_i Σ_j P_i(j) Z_i(j)`, and binding
/// `j` commutes with that sum, so these rounds run on six tables of `2^14` entries. Each round
/// polynomial is the unique one of the definition, so the bytes are those of any other way of
/// computing it; `g(1) = claim − g(0)` is not summed.
pub fn inner(
    circ: &Circuit,
    sh: &Shape,
    wit: &Witness,
    s: &[u8; 32],
    r_x: &[E],
    rho: E,
    claim0: E,
    tr: &mut Transcript,
) -> InnerOut {
    let kp = sh.kappa;
    let nb = sh.blocks();
    let verbose = std::env::var("SPARTAN_VERBOSE").map(|v| v == "2").unwrap_or(false);
    let t0 = std::time::Instant::now();
    let lap = |what: &str| {
        if verbose {
            eprintln!("  inner {what}: {:.4}s", t0.elapsed().as_secs_f64());
        }
    };
    let rf = row_factors(sh, r_x);
    lap("row factors");
    let rho2 = rho * rho;
    // P_0 = U = uA + ρ uB + ρ² e (C = I)
    let eb: Vec<E> = par::collect_vec(BLOCK, 1 << 11, |j| rf.e[j] * rho);
    let mut p0 = circ.transpose(&rf.e, &eb);
    par::for_each_chunk_mut(&mut p0, 1 << 11, |off, ch| {
        for (i, x) in ch.iter_mut().enumerate() {
            *x += rho2 * rf.e[off + i];
        }
    });
    let mut p1 = vec![E::ZERO; BLOCK];
    let mut p2 = vec![E::ZERO; BLOCK];
    for j in 0..256 {
        p1[256 + j] = rf.ekj[j];
        p2[648 + j] = rf.ekj[j];
    }
    let eq_t = eq_table(&r_x[14..14 + kp]);
    let eq_t2 = eq_table(&r_x[8..8 + kp]);
    let mut gam = [vec![E::ZERO; nb], vec![E::ZERO; nb], vec![E::ZERO; nb]];
    for t in 0..nb {
        gam[0][t] = rf.r0 * eq_t[t];
        let mut g1 = if t + 1 < nb { eq_t2[t + 1] * rf.rw } else { E::ZERO };
        if t as u64 == sh.n - 1 {
            g1 += rf.rt;
        }
        gam[1][t] = g1;
        gam[2][t] = rho2 * eq_t2[t] * rf.rw;
    }
    let mut mpub = vec![E::ZERO; BLOCK];
    mpub[0] = rf.e[CPOS] * rf.r0 * (E::ONE + rho) + rho * (rf.rw + rf.rt);
    for j in 0..256 {
        mpub[1 + j] = rf.ekj[j] * rf.t0 * rf.rw;
        mpub[257 + j] = rho2 * rf.ekj[j] * rf.rt;
    }
    let mut zpub: Vec<E> = (0..BLOCK).map(|u| E::from_bit(pub_bit(s, &wit.h, u))).collect();
    lap("transpose and setup");
    // the dense tables P_0, Z_0, Z_1, Z_2 side by side; P_1, P_2 and the public tables apart
    let mut dense = fold_blocks(&wit.w, nb, &gam, &p0);
    drop(p0);
    lap("fold over t'");
    let mut ps = [p1, p2];
    // the entries of P_1, P_2 and of the public tables that can be non-zero
    let mut ranges = [(256usize, 512usize), (648, 904)];
    let mut plen = 513usize;

    let mut r: Vec<E> = vec![];
    let mut polys = vec![];
    let mut claim = claim0;
    let mut gv = sum_pairs(&mut dense, &ps, &ranges, None);
    for l in 0..14 {
        let half = BLOCK >> (l + 1); // pairs per table
        // the public half (t' = 0, top = 1)
        for jj in 0..half.min(plen.div_ceil(2)) {
            let (ma, mb) = (mpub[2 * jj], mpub[2 * jj + 1]);
            let (za, zb) = (zpub[2 * jj], zpub[2 * jj + 1]);
            gv[0] += ma * za;
            gv[1] += (ma + mb) * (za + zb);
        }
        // g(1) = claim − g(0)
        let g = coeffs2(gv[0], claim + gv[0], gv[1]);
        tr.absorb(KIND_INNER, &bytes_of(&g));
        let rl = tr.squeeze_e();
        claim = horner(&g, rl);
        r.push(rl);
        polys.push(g);
        for i in 0..2 {
            ps[i] = fold_range(&ps[i], rl, ranges[i].0, ranges[i].1);
            ranges[i] = (ranges[i].0 >> 1, (ranges[i].1 + 1) >> 1);
        }
        mpub = fold_range(&mpub, rl, 0, plen);
        zpub = fold_range(&zpub, rl, 0, plen);
        plen = plen.div_ceil(2);
        // fold the dense tables and sum the next round in the same pass
        let mut next: Vec<[E; 4]> = vec![[E::ZERO; 4]; half];
        gv = if l < 13 { sum_pairs(&mut next, &ps, &ranges, Some((&dense, rl))) } else { [E::ZERO; 2] };
        if l == 13 {
            let (a, b) = (dense[0][0], dense[1][0]);
            next[0][0] = a + rl * (a + b);
        }
        dense = next;
    }
    let p0f = dense[0][0];
    lap("14 rounds over j");
    // phase 2: dense tables over (t', top); z̃(r_{<14}, t') from the bits of each block
    let eq14 = eq_table(&r);
    let zt = par::collect_vec(nb, 1, |t| {
        let mut acc = E::ZERO;
        for (wi, &word) in wit.w[t * (BLOCK / 64)..(t + 1) * (BLOCK / 64)].iter().enumerate() {
            let mut x = word;
            while x != 0 {
                acc += eq14[64 * wi + x.trailing_zeros() as usize];
                x &= x - 1;
            }
        }
        acc
    });
    let sz = 2 * nb;
    let mut m2 = vec![E::ZERO; sz];
    let mut z2 = vec![E::ZERO; sz];
    for t in 0..nb {
        m2[t] = p0f * gam[0][t] + ps[0][0] * gam[1][t] + ps[1][0] * gam[2][t];
        z2[t] = zt[t];
    }
    m2[nb] = mpub[0];
    z2[nb] = zpub[0];
    lap("z(r_j, t')");
    let (p2polys, r2, fm, fz) = product_sumcheck(m2, z2, claim, KIND_INNER, tr);
    lap("rounds over (t', top)");
    polys.extend(p2polys);
    r.extend(r2);
    InnerOut { polys, r_y: r, final_m: fm, final_z: fz }
}

/// One pass over the dense tables `(P_0, Z_0, Z_1, Z_2)` of a round of the inner sumcheck: with
/// `fold = Some((old, r))`, first `tab[j] = old[2j] + r·(old[2j] + old[2j + 1])`; then the round's
/// sums `[Σ P(0)·Z(0), Σ (P(0) + P(1))·(Z(0) + Z(1))]` over the pairs of `tab`, of `P_0·Z_0` and of
/// `P_i·Z_i` (`P_1`, `P_2` in `ps`, non-zero in `ranges`). Parallel over aligned ranges of pairs.
fn sum_pairs(tab: &mut [[E; 4]], ps: &[Vec<E>; 2], ranges: &[(usize, usize); 2], fold: Option<(&[[E; 4]], E)>) -> [E; 2] {
    let half = tab.len() / 2;
    let parts = par::map_chunks_mut(tab, 2, 1 << 10, |off, ch| {
        if let Some((old, r)) = fold {
            for (i, o) in ch.iter_mut().enumerate() {
                let (a, b) = (&old[2 * (off + i)], &old[2 * (off + i) + 1]);
                for c in 0..4 {
                    o[c] = a[c] + r * (a[c] + b[c]);
                }
            }
        }
        let (j0, j1) = (off / 2, (off + ch.len()) / 2);
        let mut sv = [E::ZERO; 2];
        for jj in j0..j1 {
            let (x, y) = (&ch[2 * jj - off], &ch[2 * jj + 1 - off]);
            sv[0] += x[0] * x[1];
            sv[1] += (x[0] + y[0]) * (x[1] + y[1]);
        }
        for i in 0..2 {
            let (lo, hi) = (ranges[i].0 >> 1, ((ranges[i].1 + 1) >> 1).min(half));
            let p = &ps[i];
            for jj in lo.max(j0)..hi.min(j1) {
                let (pa, pb) = (p[2 * jj], p[2 * jj + 1]);
                let (za, zb) = (ch[2 * jj - off][2 + i], ch[2 * jj + 1 - off][2 + i]);
                sv[0] += pa * za;
                sv[1] += (pa + pb) * (za + zb);
            }
        }
        sv
    });
    let mut gv = [E::ZERO; 2];
    for p in parts {
        gv[0] += p[0];
        gv[1] += p[1];
    }
    gv
}

/// `[P_0(j), Z_0(j), Z_1(j), Z_2(j)]` for every `j < 2^14`, with `Z_i(j) = Σ_{t < nb} γ_i(t)·w(j +
/// 2^14 t)` from the bits of `w` (parallel over ranges of `j`).
fn fold_blocks(w: &[u64], nb: usize, gam: &[Vec<E>; 3], p0: &[E]) -> Vec<[E; 4]> {
    const WPB: usize = BLOCK / 64; // words per block
    let mut z: Vec<[E; 4]> = vec![[E::ZERO; 4]; BLOCK];
    par::map_chunks_mut(&mut z, 64, 512, |off, acc| {
        for (i, a) in acc.iter_mut().enumerate() {
            a[0] = p0[off + i];
        }
        let w0 = off / 64;
        for t in 0..nb {
            let g = [gam[0][t], gam[1][t], gam[2][t]];
            for k in 0..acc.len() / 64 {
                let mut x = w[t * WPB + w0 + k];
                while x != 0 {
                    let a = &mut acc[64 * k + x.trailing_zeros() as usize];
                    a[1] += g[0];
                    a[2] += g[1];
                    a[3] += g[2];
                    x &= x - 1;
                }
            }
        }
    });
    z
}

/// `fold` of a table that is zero outside `[lo, hi)`: only the pairs that meet the range are
/// computed.
fn fold_range(v: &[E], r: E, lo: usize, hi: usize) -> Vec<E> {
    let half = v.len() / 2;
    let mut out = vec![E::ZERO; half];
    for i in (lo >> 1)..((hi + 1) >> 1).min(half) {
        let a = v[2 * i];
        out[i] = a + r * (a + v[2 * i + 1]);
    }
    out
}

/// A degree-2 sumcheck of `Σ_y f(y) g(y)` over dense tables. Returns the round polynomials, the
/// challenges and the final `f`, `g` values.
pub fn product_sumcheck(
    f: Vec<E>,
    g: Vec<E>,
    claim: E,
    kind: u8,
    tr: &mut Transcript,
) -> (Vec<[E; 3]>, Vec<E>, E, E) {
    product_rounds(f, g, claim, &mut |poly: &[E; 3]| {
        tr.absorb(kind, &bytes_of(poly));
        tr.squeeze_e()
    })
}

/// The rounds of `product_sumcheck` with the challenges from `next` (given each polynomial).
pub fn product_rounds(
    mut f: Vec<E>,
    mut g: Vec<E>,
    mut claim: E,
    next: &mut dyn FnMut(&[E; 3]) -> E,
) -> (Vec<[E; 3]>, Vec<E>, E, E) {
    let mut polys = vec![];
    let mut r = vec![];
    while f.len() > 1 {
        let half = f.len() / 2;
        let (fr, gr) = (&f, &g);
        let parts = par::map_chunks(half, 1 << 12, |a, b| {
            let mut s = [E::ZERO; 2];
            for y in a..b {
                let (f0, f1, g0, g1) = (fr[2 * y], fr[2 * y + 1], gr[2 * y], gr[2 * y + 1]);
                s[0] += f0 * g0;
                s[1] += (f0 + f1) * (g0 + g1);
            }
            s
        });
        let mut sv = [E::ZERO; 2];
        for p in parts {
            sv[0] += p[0];
            sv[1] += p[1];
        }
        // g(1) = claim − g(0): the polynomial is the unique one of the definition
        let poly = coeffs2(sv[0], claim + sv[0], sv[1]);
        debug_assert_eq!(poly[1] + poly[2], claim);
        let rl = next(&poly);
        claim = horner(&poly, rl);
        f = fold(&f, rl);
        g = fold(&g, rl);
        polys.push(poly);
        r.push(rl);
    }
    debug_assert_eq!(f[0] * g[0], claim);
    (polys, r, f[0], g[0])
}

/// The 64 slices `s_i = Q̃_i(r_hi)`, `Q_i(u') = bit i of q(u')` (§4.2).
pub fn slices(q: &[u64], eq_hi: &[E]) -> Vec<E> {
    let parts = par::map_chunks(q.len(), 1 << 12, |a, b| {
        let mut acc = [E::ZERO; 64];
        for u in a..b {
            let mut word = q[u];
            let e = eq_hi[u];
            while word != 0 {
                let i = word.trailing_zeros() as usize;
                acc[i] += e;
                word &= word - 1;
            }
        }
        acc
    });
    let mut s = vec![E::ZERO; 64];
    for p in parts {
        for i in 0..64 {
            s[i] += p[i];
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::witness;
    use crate::mle::eq_ee;
    use crate::oracle::Local;

    /// The outer sumcheck with some `τ_l = 0` (so `h(1)` is summed in those rounds, in each kind
    /// of round) passes the verifier's checks: each `g(0) + g(1)` is the claim, and the last claim
    /// is `eq(τ, r_x)·(v_A·v_B + v_C)`.
    #[test]
    fn outer_with_zero_tau() {
        let circ = Circuit::build();
        let o = Local::keyed(&[5u8; 32]);
        for n in [1u64, 3] {
            let sh = Shape::new(n);
            let s: [u8; 32] = std::array::from_fn(|i| i as u8 ^ 0x5a);
            let wit = witness(&circ, &sh, &s);
            let mut tau: Vec<E> = (0..sh.ell).map(|l| E([l as u64 * 77 + 3, 9, l as u64])).collect();
            for z in [1usize, 4, 8, sh.ell - 1] {
                tau[z] = E::ZERO;
            }
            let mut tr = Transcript::new(&o, &s, n, &wit.h, false);
            let mut bits = [wit.a.clone(), wit.b.clone(), wit.c.clone()];
            let out = outer(&sh, &mut bits, &tau, &mut tr, false);
            let mut claim = E::ZERO;
            for (l, g) in out.polys.iter().enumerate() {
                assert_eq!(g[1] + g[2] + g[3], claim, "n = {n}, round {l}");
                claim = horner(g, out.r_x[l]);
            }
            let [va, vb, vc] = out.v;
            assert_eq!(claim, eq_ee(&tau, &out.r_x) * (va * vb + vc), "n = {n}");
        }
    }
}
