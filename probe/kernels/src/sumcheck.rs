//! Item 2 (eq tables, ring switching's packed-bit inner products) and the sumcheck round kernels
//! that follow round 2 (zerocheck tail over F; Ligerito's opening sumcheck, F -> K and K -> K).
//!
//! - `eq_build`: eq(r, x) over 2^k points, one product per entry (Flock `build_eq`).
//! - `fold_1b_rows_2way`: Flock `pcs/ring_switch.rs::fold_1b_rows_2way_method_of_four_russians`:
//!   `s_v = sum_x t(x) * bit_v(packed[x])` for v < 128 and two claims t0, t1 (the ring-switch
//!   partial evaluations; the GF(2^128) x packed-GF(2)-vector product).
//! - `fold_b128`: Flock `fold_b128_elems`: `rs_eq_ind[x] = sum_v bit_v(tensor[x]) * eq_r''[v]`.
//! - `fold_msg_*`: Flock `fold_and_message_x86_avx512` (zerocheck rounds 3..): fold a, b at r,
//!   then (P(1), P(inf)) = sum eq * (a1 b1, (a0+a1)(b0+b1)) with delayed reduction.
//! - `lig_f2k`, `lig_k2k`: one Ligerito sumcheck round on (f, w): fold both by a K = GF(2^256)
//!   challenge, then the next message sum f1 w1, sum (f0+f1)(w0+w1) in K, delayed reduction.
use crate::gf::*;
use crate::{par_best, par_for, quick, report, Rng, SyncPtr};
use std::arch::x86_64::*;
use std::hint::black_box;

// ------------------------------------------------------------------ eq table
pub fn eq_build_portable(r: &[F128], e: &mut [F128]) {
    e[0] = F128::ONE;
    for (i, &ri) in r.iter().enumerate() {
        let h = 1usize << i;
        for j in 0..h {
            let v = mul_portable(e[j], ri);
            e[j + h] = v;
            e[j] += v;
        }
    }
}
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn eq_step_pclmul(e: *mut F128, h: usize, s: usize, n: usize, ri: F128) {
    for j in s..s + n {
        let v = mul_pclmul(*e.add(j), ri);
        *e.add(j + h) = v;
        *e.add(j) += v;
    }
}
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn eq_step_ymm(e: *mut F128, h: usize, s: usize, n: usize, ri: F128) {
    let r = bcast_y(ri);
    let rk = kara_pre_y(r);
    let mut j = s;
    while j < s + n {
        let x = ld_y(e.add(j));
        let v = mul_y_kara(x, r, rk);
        st_y(e.add(j + h), v);
        st_y(e.add(j), _mm256_xor_si256(x, v));
        j += 2;
    }
}
pub fn eq_build(r: &[F128], e: &mut [F128], tier: Tier, threads: usize) {
    if tier == Tier::Portable {
        return eq_build_portable(r, e);
    }
    e[0] = F128::ONE;
    let p = SyncPtr(e.as_mut_ptr());
    for (i, &ri) in r.iter().enumerate() {
        let h = 1usize << i;
        let (th, nchunks) = if h >= 1 << 14 { (threads, 16) } else { (1, 1) };
        let chunk = h / nchunks;
        par_for(th, nchunks, |c| unsafe {
            let p = p;
            if tier == Tier::Pclmul || h < 2 {
                eq_step_pclmul(p.0, h, c * chunk, chunk, ri)
            } else {
                eq_step_ymm(p.0, h, c * chunk, chunk, ri)
            }
        });
    }
}

// ------------------------------------------------------------------ ring switching
#[inline(always)]
pub fn transpose8x8(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA00AA00AA00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000CCCC0000CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x00000000F0F0F0F0;
    x ^= t ^ (t << 28);
    x
}
fn subset4(e: [F128; 4]) -> [F128; 16] {
    let mut s = [F128::ZERO; 16];
    for (i, &v) in e.iter().enumerate() {
        let h = 1 << i;
        for k in 0..h {
            s[h + k] = s[k] + v;
        }
    }
    s
}
/// Flock's 4-wide 2-way method of four Russians, one worker's range.
pub fn fold_1b_rows_2way_range(packed: &[F128], t0: &[F128], t1: &[F128], a0: &mut [F128; 128], a1: &mut [F128; 128]) {
    for g in 0..packed.len() / 4 {
        let l0 = subset4([t0[4 * g], t0[4 * g + 1], t0[4 * g + 2], t0[4 * g + 3]]);
        let l1 = subset4([t1[4 * g], t1[4 * g + 1], t1[4 * g + 2], t1[4 * g + 3]]);
        let m: [[u8; 16]; 4] = std::array::from_fn(|k| {
            let e = packed[4 * g + k];
            let mut b = [0u8; 16];
            b[..8].copy_from_slice(&e.lo.to_le_bytes());
            b[8..].copy_from_slice(&e.hi.to_le_bytes());
            b
        });
        for rb in 0..16 {
            let comb = (m[0][rb] as u64) | ((m[1][rb] as u64) << 8) | ((m[2][rb] as u64) << 16) | ((m[3][rb] as u64) << 24);
            let tb = transpose8x8(comb).to_le_bytes();
            let base = rb * 8;
            for p in 0..8 {
                a0[base + p] += l0[(tb[p] & 15) as usize];
                a1[base + p] += l1[(tb[p] & 15) as usize];
            }
        }
    }
}
/// Flock's 1-way method of four Russians (one claim).
pub fn fold_1b_rows_1way_range(packed: &[F128], t0: &[F128], a0: &mut [F128; 128]) {
    for g in 0..packed.len() / 4 {
        let l0 = subset4([t0[4 * g], t0[4 * g + 1], t0[4 * g + 2], t0[4 * g + 3]]);
        let m: [[u8; 16]; 4] = std::array::from_fn(|k| {
            let e = packed[4 * g + k];
            let mut b = [0u8; 16];
            b[..8].copy_from_slice(&e.lo.to_le_bytes());
            b[8..].copy_from_slice(&e.hi.to_le_bytes());
            b
        });
        for rb in 0..16 {
            let comb = (m[0][rb] as u64) | ((m[1][rb] as u64) << 8) | ((m[2][rb] as u64) << 16) | ((m[3][rb] as u64) << 24);
            let tb = transpose8x8(comb).to_le_bytes();
            for p in 0..8 {
                a0[rb * 8 + p] += l0[(tb[p] & 15) as usize];
            }
        }
    }
}
pub fn fold_1b_naive(packed: &[F128], t: &[F128]) -> Vec<F128> {
    let mut o = vec![F128::ZERO; 128];
    for (x, e) in packed.iter().enumerate() {
        for v in 0..128 {
            let bit = if v < 64 { (e.lo >> v) & 1 } else { (e.hi >> (v - 64)) & 1 };
            if bit == 1 {
                o[v] += t[x];
            }
        }
    }
    o
}
pub fn fold_b128_tables(eqr: &[F128]) -> Vec<F128> {
    let mut t = vec![F128::ZERO; 16 * 256];
    for bi in 0..16 {
        for w in 1..256usize {
            let low = w & w.wrapping_neg();
            t[bi * 256 + w] = t[bi * 256 + (w ^ low)] + eqr[bi * 8 + low.trailing_zeros() as usize];
        }
    }
    t
}
#[inline(always)]
pub fn fold_b128_range(tens: &[F128], tab: &[F128], out: &mut [F128]) {
    for (i, e) in tens.iter().enumerate() {
        let (lo, hi) = (e.lo.to_le_bytes(), e.hi.to_le_bytes());
        let mut acc = [F128::ZERO; 4];
        for k in 0..8 {
            acc[k & 3] += tab[k * 256 + lo[k] as usize];
            acc[(k + 1) & 3] += tab[(8 + k) * 256 + hi[k] as usize];
        }
        out[i] = (acc[0] + acc[1]) + (acc[2] + acc[3]);
    }
}

// ------------------------------------------------------------------ zerocheck tail: fold + message
/// Returns (P1, Pinf); folds a_in (2n) into a_out (n), same for b. eq has n/2 entries (masked).
pub fn fold_msg_portable(ai: &[F128], bi: &[F128], ao: &mut [F128], bo: &mut [F128], r: F128, eq: &[F128]) -> (F128, F128) {
    let mask = eq.len() - 1;
    for i in 0..ao.len() {
        ao[i] = ai[2 * i] + mul_portable(r, ai[2 * i] + ai[2 * i + 1]);
        bo[i] = bi[2 * i] + mul_portable(r, bi[2 * i] + bi[2 * i + 1]);
    }
    let (mut p1, mut pi) = (F128::ZERO, F128::ZERO);
    for k in 0..ao.len() / 2 {
        let (a0, a1, b0, b1) = (ao[2 * k], ao[2 * k + 1], bo[2 * k], bo[2 * k + 1]);
        p1 += mul_portable(eq[k & mask], mul_portable(a1, b1));
        pi += mul_portable(eq[k & mask], mul_portable(a0 + a1, b0 + b1));
    }
    (p1, pi)
}
/// Flock's portable x86 path (no AVX-512): `fold_pairs` (2 products per output) then message.
#[target_feature(enable = "pclmulqdq,sse4.1")]
pub unsafe fn fold_msg_flock(ai: &[F128], bi: &[F128], ao: &mut [F128], bo: &mut [F128], r: F128, eq: &[F128]) -> (F128, F128) {
    let mask = eq.len() - 1;
    let r1 = F128::ONE + r;
    for i in 0..ao.len() {
        ao[i] = mul_pclmul(ai[2 * i], r1) + mul_pclmul(ai[2 * i + 1], r);
        bo[i] = mul_pclmul(bi[2 * i], r1) + mul_pclmul(bi[2 * i + 1], r);
    }
    let (mut p1, mut pi) = ([0u64; 4], [0u64; 4]);
    for k in 0..ao.len() / 2 {
        let (a0, a1, b0, b1) = (ao[2 * k], ao[2 * k + 1], bo[2 * k], bo[2 * k + 1]);
        let u = mul_unreduced_pclmul(eq[k & mask], mul_pclmul(a1, b1));
        let v = mul_unreduced_pclmul(eq[k & mask], mul_pclmul(a0 + a1, b0 + b1));
        for j in 0..4 {
            p1[j] ^= u[j];
            pi[j] ^= v[j];
        }
    }
    (reduce(p1[0], p1[1], p1[2], p1[3]), reduce(pi[0], pi[1], pi[2], pi[3]))
}
/// ymm port of `fold_and_message_x86_avx512`: fused, 4 outputs per iteration.
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq,sse4.1")]
pub unsafe fn fold_msg_ymm(ai: &[F128], bi: &[F128], ao: &mut [F128], bo: &mut [F128], r: F128, eq: &[F128]) -> (F128, F128) {
    let mask = eq.len() - 1;
    let ry = bcast_y(r);
    let rk = kara_pre_y(ry);
    let mut w1 = Wide2::zero();
    let mut wi = Wide2::zero();
    #[inline(always)]
    unsafe fn fold2(src: *const F128, r: __m256i, rk: __m256i) -> __m256i {
        let x = ld_y(src); // e0 o0
        let y = ld_y(src.add(2)); // e1 o1
        let ev = _mm256_permute2x128_si256::<0x20>(x, y);
        let od = _mm256_permute2x128_si256::<0x31>(x, y);
        _mm256_xor_si256(ev, mul_y_kara(_mm256_xor_si256(ev, od), r, rk))
    }
    let mut o = 0;
    while o + 4 <= ao.len() {
        let a01 = fold2(ai.as_ptr().add(2 * o), ry, rk); // outputs o, o+1 = pair k
        let a23 = fold2(ai.as_ptr().add(2 * o + 4), ry, rk); // pair k+1
        let b01 = fold2(bi.as_ptr().add(2 * o), ry, rk);
        let b23 = fold2(bi.as_ptr().add(2 * o + 4), ry, rk);
        st_y(ao.as_mut_ptr().add(o), a01);
        st_y(ao.as_mut_ptr().add(o + 2), a23);
        st_y(bo.as_mut_ptr().add(o), b01);
        st_y(bo.as_mut_ptr().add(o + 2), b23);
        let a0 = _mm256_permute2x128_si256::<0x20>(a01, a23);
        let a1 = _mm256_permute2x128_si256::<0x31>(a01, a23);
        let b0 = _mm256_permute2x128_si256::<0x20>(b01, b23);
        let b1 = _mm256_permute2x128_si256::<0x31>(b01, b23);
        let k = o / 2;
        let e = ld_y(eq.as_ptr().add(k & mask));
        w1.mac(e, mul_y(a1, b1));
        wi.mac(e, mul_y(_mm256_xor_si256(a0, a1), _mm256_xor_si256(b0, b1)));
        o += 4;
    }
    (w1.reduce_sum(), wi.reduce_sum())
}

// ------------------------------------------------------------------ Ligerito sumcheck rounds
// K elements are stored as two consecutive F128 (c0, c1).
pub fn lig_f2k_portable(f: &[F128], w: &[F128], fo: &mut [F128], wo: &mut [F128], r: [F128; 2]) -> [F128; 4] {
    let n = f.len() / 2;
    for i in 0..n {
        for (src, dst) in [(f, &mut *fo), (w, &mut *wo)] {
            let d = src[2 * i] + src[2 * i + 1];
            dst[2 * i] = src[2 * i] + mul_portable(r[0], d);
            dst[2 * i + 1] = mul_portable(r[1], d);
        }
    }
    lig_msg_portable(fo, wo)
}
pub fn lig_k2k_portable(f: &[F128], w: &[F128], fo: &mut [F128], wo: &mut [F128], r: [F128; 2]) -> [F128; 4] {
    let n = f.len() / 4; // K outputs
    for i in 0..n {
        for (src, dst) in [(f, &mut *fo), (w, &mut *wo)] {
            let d = [src[4 * i] + src[4 * i + 2], src[4 * i + 1] + src[4 * i + 3]];
            let p = k_mul_portable(r, d);
            dst[2 * i] = src[4 * i] + p[0];
            dst[2 * i + 1] = src[4 * i + 1] + p[1];
        }
    }
    lig_msg_portable(fo, wo)
}
fn lig_msg_portable(f: &[F128], w: &[F128]) -> [F128; 4] {
    let (mut p1, mut pi) = ([F128::ZERO; 2], [F128::ZERO; 2]);
    for k in 0..f.len() / 4 {
        let f0 = [f[4 * k], f[4 * k + 1]];
        let f1 = [f[4 * k + 2], f[4 * k + 3]];
        let w0 = [w[4 * k], w[4 * k + 1]];
        let w1 = [w[4 * k + 2], w[4 * k + 3]];
        let a = k_mul_portable(f1, w1);
        let b = k_mul_portable([f0[0] + f1[0], f0[1] + f1[1]], [w0[0] + w1[0], w0[1] + w1[1]]);
        p1[0] += a[0];
        p1[1] += a[1];
        pi[0] += b[0];
        pi[1] += b[1];
    }
    [p1[0], p1[1], pi[0], pi[1]]
}

/// Accumulates K x K products unreduced: p01 += [a0 b0, a1 b1], pm += (a0+a1)(b0+b1) (two
/// products per Wide2 slot).
struct KAcc {
    p01: Wide2,
    pm: Wide2,
}
impl KAcc {
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn zero() -> Self {
        KAcc { p01: Wide2::zero(), pm: Wide2::zero() }
    }
    /// add a*b + c*d (four K elements in ymm)
    #[inline]
    #[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
    unsafe fn mac2(&mut self, a: __m256i, b: __m256i, c: __m256i, d: __m256i) {
        self.p01.mac(a, b);
        self.p01.mac(c, d);
        let sa = fold_y(a);
        let sb = fold_y(b);
        let sc = fold_y(c);
        let sd = fold_y(d);
        self.pm.mac(_mm256_set_m128i(sc, sa), _mm256_set_m128i(sd, sb));
    }
    #[inline]
    #[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
    unsafe fn finish(self) -> [F128; 2] {
        let mut p = [F128::ZERO; 2];
        st_y(p.as_mut_ptr(), self.p01.reduce_lanes());
        let pm = self.pm.reduce_sum();
        [p[0] + mul_xinv(p[1]), pm + p[0]]
    }
}

/// Fold of F vectors by a K challenge, then the K-message. Per 4 inputs: 2 K outputs per vector.
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq,sse4.1")]
pub unsafe fn lig_f2k_ymm(f: &[F128], w: &[F128], fo: &mut [F128], wo: &mut [F128], r: [F128; 2]) -> [F128; 4] {
    let ry = pair_y(r[0], r[1]);
    let (mut a1, mut ai) = (KAcc::zero(), KAcc::zero());
    let mut i = 0;
    while i + 4 <= f.len() {
        // inputs i..i+4 -> K outputs i/2, i/2+1 (one message pair)
        let mut out = [[_mm256_setzero_si256(); 2]; 2]; // [vec][k]
        for (vi, src) in [f, w].iter().enumerate() {
            for k in 0..2 {
                let e = src[i + 2 * k];
                let d = e + src[i + 2 * k + 1];
                let prod = mul_y(ry, bcast_y(d));
                out[vi][k] = _mm256_xor_si256(prod, _mm256_set_m128i(_mm_setzero_si128(), to_x(e)));
            }
        }
        st_y(fo.as_mut_ptr().add(i), out[0][0]);
        st_y(fo.as_mut_ptr().add(i + 2), out[0][1]);
        st_y(wo.as_mut_ptr().add(i), out[1][0]);
        st_y(wo.as_mut_ptr().add(i + 2), out[1][1]);
        let (f0, f1, w0, w1) = (out[0][0], out[0][1], out[1][0], out[1][1]);
        // P1 += f1 w1 ; Pinf += (f0+f1)(w0+w1): accumulate both into separate accumulators
        a1.p01.mac(f1, w1);
        a1.pm.mac(_mm256_set_m128i(_mm_setzero_si128(), fold_y(f1)), _mm256_set_m128i(_mm_setzero_si128(), fold_y(w1)));
        let fs = _mm256_xor_si256(f0, f1);
        let ws = _mm256_xor_si256(w0, w1);
        ai.p01.mac(fs, ws);
        ai.pm.mac(_mm256_set_m128i(_mm_setzero_si128(), fold_y(fs)), _mm256_set_m128i(_mm_setzero_si128(), fold_y(ws)));
        i += 4;
    }
    let (x, y) = (a1.finish(), ai.finish());
    [x[0], x[1], y[0], y[1]]
}

/// Fold of K vectors by a K challenge, then the K-message. Inputs: 2n F128 (n K); per 8 inputs
/// (4 K) -> 2 K outputs per vector.
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq,sse4.1")]
pub unsafe fn lig_k2k_ymm(f: &[F128], w: &[F128], fo: &mut [F128], wo: &mut [F128], r: [F128; 2]) -> [F128; 4] {
    let ry = pair_y(r[0], r[1]);
    let (mut a1, mut ai) = (KAcc::zero(), KAcc::zero());
    let mut i = 0;
    while i + 8 <= f.len() {
        let mut out = [[_mm256_setzero_si256(); 2]; 2];
        for (vi, src) in [f, w].iter().enumerate() {
            let e0 = ld_y(src.as_ptr().add(i));
            let o0 = ld_y(src.as_ptr().add(i + 2));
            let e1 = ld_y(src.as_ptr().add(i + 4));
            let o1 = ld_y(src.as_ptr().add(i + 6));
            let (p, q) = k_mul2(ry, _mm256_xor_si256(e0, o0), ry, _mm256_xor_si256(e1, o1));
            out[vi][0] = _mm256_xor_si256(e0, p);
            out[vi][1] = _mm256_xor_si256(e1, q);
        }
        st_y(fo.as_mut_ptr().add(i / 2), out[0][0]);
        st_y(fo.as_mut_ptr().add(i / 2 + 2), out[0][1]);
        st_y(wo.as_mut_ptr().add(i / 2), out[1][0]);
        st_y(wo.as_mut_ptr().add(i / 2 + 2), out[1][1]);
        let (f0, f1, w0, w1) = (out[0][0], out[0][1], out[1][0], out[1][1]);
        // two products (f1 w1) and ((f0+f1)(w0+w1)) into separate sums: use mac2 with a zero pair
        a1.p01.mac(f1, w1);
        let fs = _mm256_xor_si256(f0, f1);
        let ws = _mm256_xor_si256(w0, w1);
        ai.p01.mac(fs, ws);
        // middle terms of both, packed into one Wide2 (lane 0 -> P1, lane 1 -> Pinf)
        a1.pm.mac(_mm256_set_m128i(fold_y(fs), fold_y(f1)), _mm256_set_m128i(fold_y(ws), fold_y(w1)));
        i += 8;
    }
    // a1.pm holds lane0 = P1 middle, lane1 = Pinf middle
    let mut p = [F128::ZERO; 2];
    st_y(p.as_mut_ptr(), a1.p01.reduce_lanes());
    let mut q = [F128::ZERO; 2];
    st_y(q.as_mut_ptr(), ai.p01.reduce_lanes());
    let mut mids = [F128::ZERO; 2];
    st_y(mids.as_mut_ptr(), a1.pm.reduce_lanes());
    [p[0] + mul_xinv(p[1]), mids[0] + p[0], q[0] + mul_xinv(q[1]), mids[1] + q[0]]
}

pub fn selftest(c: Cpu, rng: &mut Rng) -> Result<(), String> {
    // eq
    let r = rng.fvec(10);
    let mut e_ref = vec![F128::ZERO; 1 << 10];
    eq_build_portable(&r, &mut e_ref);
    for t in tiers(c) {
        let mut e = vec![F128::ZERO; 1 << 10];
        eq_build(&r, &mut e, t, 3);
        if e != e_ref {
            return Err(format!("eq_build {t:?} mismatch"));
        }
    }
    // spot-check eq at a vertex: e[x] = prod r_i^{x_i} (1+r_i)^{1-x_i}
    let x = 0b1011001110usize;
    let mut v = F128::ONE;
    for i in 0..10 {
        v = mul_portable(v, if (x >> i) & 1 == 1 { r[i] } else { F128::ONE + r[i] });
    }
    if v != e_ref[x] {
        return Err("eq vertex value wrong".into());
    }
    // four Russians
    let n = 64;
    let packed = rng.fvec(n);
    let (t0, t1) = (rng.fvec(n), rng.fvec(n));
    let (mut a0, mut a1) = ([F128::ZERO; 128], [F128::ZERO; 128]);
    fold_1b_rows_2way_range(&packed, &t0, &t1, &mut a0, &mut a1);
    if a0.to_vec() != fold_1b_naive(&packed, &t0) || a1.to_vec() != fold_1b_naive(&packed, &t1) {
        return Err("fold_1b_rows mismatch".into());
    }
    let mut a2 = [F128::ZERO; 128];
    fold_1b_rows_1way_range(&packed, &t1, &mut a2);
    if a2 != a1 {
        return Err("fold_1b_rows 1-way mismatch".into());
    }
    let eqr = rng.fvec(128);
    let tab = fold_b128_tables(&eqr);
    let mut o = vec![F128::ZERO; n];
    fold_b128_range(&packed, &tab, &mut o);
    for i in 0..n {
        let mut s = F128::ZERO;
        for vv in 0..128 {
            let bit = if vv < 64 { (packed[i].lo >> vv) & 1 } else { (packed[i].hi >> (vv - 64)) & 1 };
            if bit == 1 {
                s += eqr[vv];
            }
        }
        if s != o[i] {
            return Err("fold_b128 mismatch".into());
        }
    }
    // fold + message
    let m = 256;
    let (ai, bi) = (rng.fvec(m), rng.fvec(m));
    let eq = rng.fvec(16);
    let rr = rng.f();
    let (mut ao, mut bo) = (vec![F128::ZERO; m / 2], vec![F128::ZERO; m / 2]);
    let refm = fold_msg_portable(&ai, &bi, &mut ao, &mut bo, rr, &eq);
    let (ar, br) = (ao.clone(), bo.clone());
    unsafe {
        if c.pclmul {
            let x = fold_msg_flock(&ai, &bi, &mut ao, &mut bo, rr, &eq);
            if x != refm || ao != ar || bo != br {
                return Err("fold_msg_flock mismatch".into());
            }
        }
        if c.ymm {
            let x = fold_msg_ymm(&ai, &bi, &mut ao, &mut bo, rr, &eq);
            if x != refm || ao != ar || bo != br {
                return Err("fold_msg_ymm mismatch".into());
            }
        }
    }
    // Ligerito rounds
    let rk = [rng.f(), rng.f()];
    let (f, w) = (rng.fvec(m), rng.fvec(m));
    let (mut fo, mut wo) = (vec![F128::ZERO; m], vec![F128::ZERO; m]);
    let r1 = lig_f2k_portable(&f, &w, &mut fo, &mut wo, rk);
    let (fr, wr) = (fo.clone(), wo.clone());
    let (mut fo2, mut wo2) = (vec![F128::ZERO; m / 2], vec![F128::ZERO; m / 2]);
    let r2 = lig_k2k_portable(&f, &w, &mut fo2, &mut wo2, rk);
    let (fr2, wr2) = (fo2.clone(), wo2.clone());
    if c.ymm {
        unsafe {
            let x = lig_f2k_ymm(&f, &w, &mut fo, &mut wo, rk);
            if x != r1 || fo != fr || wo != wr {
                return Err("lig_f2k_ymm mismatch".into());
            }
            let x = lig_k2k_ymm(&f, &w, &mut fo2, &mut wo2, rk);
            if x != r2 || fo2 != fr2 || wo2 != wr2 {
                return Err("lig_k2k_ymm mismatch".into());
            }
        }
    }
    Ok(())
}

/// eq tables and ring-switch folds.
pub fn bench_eq_rs(c: Cpu, threads: &[usize]) {
    let k = if quick() { 16 } else { 22 };
    let mut rng = Rng(21);
    let r = rng.fvec(k);
    let mut e = vec![F128::ZERO; 1 << k];
    for t in tiers(c) {
        if t == Tier::Zmm {
            continue;
        }
        for &th in threads {
            let secs = crate::best(3, || eq_build(&r, &mut e, t, th));
            report("eq-table-build", t.name(), th, &format!("2^{k}"), (1usize << k) as f64, secs, "entry");
        }
    }
    // ring switching folds over N packed elements (128 per BLAKE2s compression)
    let n = 1usize << k;
    let packed = rng.fvec(n);
    let (t0, t1) = (rng.fvec(n), rng.fvec(n));
    for &th in threads {
        let secs = crate::best(3, || {
            let per = n / th;
            par_for(th, th, |w| {
                let (mut a0, mut a1) = ([F128::ZERO; 128], [F128::ZERO; 128]);
                let s = w * per;
                fold_1b_rows_2way_range(&packed[s..s + per], &t0[s..s + per], &t1[s..s + per], &mut a0, &mut a1);
                black_box((a0, a1));
            });
        });
        report("ringswitch-fold_1b_rows-2way(s_hat_v, MoFR)", "scalar(Flock port)", th, &format!("2^{k}"), n as f64, secs, "packed-elem");
        let secs = crate::best(3, || {
            let per = n / th;
            par_for(th, th, |w| {
                let mut a0 = [F128::ZERO; 128];
                let s = w * per;
                fold_1b_rows_1way_range(&packed[s..s + per], &t0[s..s + per], &mut a0);
                black_box(a0);
            });
        });
        report("ringswitch-fold_1b_rows-1way(s_hat_v, MoFR)", "scalar(Flock port)", th, &format!("2^{k}"), n as f64, secs, "packed-elem");
        let tab = fold_b128_tables(&t0[..128]);
        let mut out = vec![F128::ZERO; n];
        let op = SyncPtr(out.as_mut_ptr());
        let secs = crate::best(3, || {
            let per = n / th;
            par_for(th, th, |w| {
                let op = op;
                let o = unsafe { std::slice::from_raw_parts_mut(op.0.add(w * per), per) };
                fold_b128_range(&packed[w * per..(w + 1) * per], &tab, o);
            });
        });
        report("ringswitch-fold_b128(rs_eq_ind)", "scalar(Flock port)", th, &format!("2^{k}"), n as f64, secs, "packed-elem");
    }
}

/// zerocheck tail and Ligerito sumcheck rounds, per input element, streamed from DRAM (2^22) and
/// cache-resident (2^14) sizes.
pub fn bench_sumcheck(c: Cpu, threads: &[usize]) {
    let mut rng = Rng(31);
    let sizes: Vec<usize> = if quick() { vec![14, 16] } else { vec![14, 22] };
    for &lg in &sizes {
        let n = 1usize << lg;
        let (ai, bi) = (rng.fvec(n), rng.fvec(n));
        let eq = rng.fvec(1024.min(n / 4));
        let r = rng.f();
        let reps = (1usize << if quick() { 18 } else { 24 }) / n;
        for &th in threads {
            // each thread owns a copy of the output buffers; inputs shared (read-only)
            let run = |name: &str, f: &(dyn Fn(&[F128], &[F128], &mut [F128], &mut [F128]) -> (F128, F128) + Sync)| {
                let secs = par_best(th, 3, |_| {
                    let (mut ao, mut bo) = (vec![F128::ZERO; n / 2], vec![F128::ZERO; n / 2]);
                    for _ in 0..reps {
                        black_box(f(&ai, &bi, &mut ao, &mut bo));
                    }
                });
                report("zerocheck-tail-fold+msg", name, th, &format!("n=2^{lg}"), (th * reps * n) as f64, secs, "input-index");
            };
            if c.pclmul {
                run("flock-zen3(pclmul, fold_pairs 2 mul)", &|a, b, ao, bo| unsafe { fold_msg_flock(a, b, ao, bo, r, &eq) });
            } else {
                run("portable", &|a, b, ao, bo| fold_msg_portable(a, b, ao, bo, r, &eq));
            }
            if c.ymm {
                run("ymm-vpclmul(fused)", &|a, b, ao, bo| unsafe { fold_msg_ymm(a, b, ao, bo, r, &eq) });
            }
        }
        // Ligerito rounds
        let (f, w) = (rng.fvec(n), rng.fvec(n));
        let rk = [rng.f(), rng.f()];
        for &th in threads {
            let run = |name: &str, kk: bool, g: &(dyn Fn(&[F128], &[F128], &mut [F128], &mut [F128]) -> [F128; 4] + Sync)| {
                let secs = par_best(th, 3, |_| {
                    let (mut fo, mut wo) = (vec![F128::ZERO; n], vec![F128::ZERO; n]);
                    for _ in 0..reps {
                        black_box(g(&f, &w, &mut fo, &mut wo));
                    }
                });
                let units = if kk { n / 2 } else { n }; // input elements (F or K)
                report(if kk { "ligerito-sumcheck-round K->K" } else { "ligerito-sumcheck-round F->K" }, name, th, &format!("n=2^{lg}"), (th * reps * units) as f64, secs, "input-elem");
            };
            if c.ymm {
                run("ymm-vpclmul", false, &|f, w, fo, wo| unsafe { lig_f2k_ymm(f, w, fo, wo, rk) });
                run("ymm-vpclmul", true, &|f, w, fo, wo| unsafe { lig_k2k_ymm(f, w, &mut fo[..f.len() / 2], &mut wo[..f.len() / 2], rk) });
            } else if c.pclmul || !quick() {
                let lim = if c.pclmul { n } else { n / 16 };
                let secs = par_best(th, 1, |_| {
                    let (mut fo, mut wo) = (vec![F128::ZERO; lim], vec![F128::ZERO; lim]);
                    black_box(lig_f2k_portable(&f[..lim], &w[..lim], &mut fo, &mut wo, rk));
                });
                report("ligerito-sumcheck-round F->K", "portable", th, &format!("n=2^{lg}"), (th * lim) as f64, secs, "input-elem");
            }
        }
    }
}
