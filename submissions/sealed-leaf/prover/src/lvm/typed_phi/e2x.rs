//! PFAST-PQ: the E2 (`F128`) kernels of [`super::PhiK`] in vector registers (x86-64 with PCLMULQDQ: the v4p and v4
//! tiers). The same field sums as the generic kernels, regrouped only by XOR (exact), so the values are equal; what
//! changes is where they live: an element is one 128-bit lane (`c0` low, `c1` high), a product is four carry-less
//! products kept apart until one reduction per sum, and the reduction stays in the register (no round trip through
//! integer registers).
//!
//! The kernels are generic over [`Lane`]: one point per `__m128i` (PCLMULQDQ), or four per `__m512i` (VPCLMULQDQ, the
//! v4 tier). A batch row of `N = Q·L` points (the tables are point-minor) is `Q` vectors.
use core::arch::x86_64::*;
use std::ops::Range;

use super::{CK_K, CK_KX, CK_ONE, CK_X, Lev, MAX_LEVEL_BITS, NONE, Pass, PhiK, Tabs};
use crate::lv::primitives::field::F128;

/// `L` consecutive elements (points) in one register, a 128-bit lane each; the operations act lane by lane.
pub(super) trait Lane: Copy {
    const L: usize;
    fn zero() -> Self;
    /// `p[..L]`.
    fn ld(p: &[F128]) -> Self;
    fn st(p: &mut [F128], v: Self);
    /// `c` in every lane.
    fn bc(c: &F128) -> Self;
    fn xor(a: Self, b: Self) -> Self;
    fn or(a: Self, b: Self) -> Self;
    /// Per lane: the carry-less product of `a`'s qword `I & 1` and `b`'s qword `I ≫ 4 & 1` (PCLMULQDQ's selector).
    fn clmul<const I: i32>(a: Self, b: Self) -> Self;
    /// Per qword: `≪ 1, 3, 4`, `≫ 60, 61, 63`.
    fn sl1(a: Self) -> Self;
    fn sl3(a: Self) -> Self;
    fn sl4(a: Self) -> Self;
    fn sr60(a: Self) -> Self;
    fn sr61(a: Self) -> Self;
    fn sr63(a: Self) -> Self;
    /// Per lane: the low qword moved up (`≪ 64`), the high one moved down (`≫ 64`), the high one cleared.
    fn up(a: Self) -> Self;
    fn down(a: Self) -> Self;
    fn low(a: Self) -> Self;
    /// Per lane: `[a₀, b₀]`, `[a₁, b₁]`.
    fn unlo(a: Self, b: Self) -> Self;
    fn unhi(a: Self, b: Self) -> Self;
    fn is_zero(a: Self) -> bool;
}

impl Lane for __m128i {
    const L: usize = 1;
    // SAFETY (every method): SSE2 is baseline on x86-64, and pclmulqdq is enabled at compile time (this module's
    // cfg); the loads and stores touch `p[..1]` (`F128` is `repr(C)` `(c0, c1)`: 16 bytes, `c0` the low qword).
    #[inline(always)]
    fn zero() -> Self {
        unsafe { _mm_setzero_si128() }
    }
    #[inline(always)]
    fn ld(p: &[F128]) -> Self {
        assert!(!p.is_empty());
        unsafe { _mm_loadu_si128(p.as_ptr() as *const __m128i) }
    }
    #[inline(always)]
    fn st(p: &mut [F128], v: Self) {
        assert!(!p.is_empty());
        unsafe { _mm_storeu_si128(p.as_mut_ptr() as *mut __m128i, v) }
    }
    #[inline(always)]
    fn bc(c: &F128) -> Self {
        Self::ld(std::slice::from_ref(c))
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        unsafe { _mm_xor_si128(a, b) }
    }
    #[inline(always)]
    fn or(a: Self, b: Self) -> Self {
        unsafe { _mm_or_si128(a, b) }
    }
    #[inline(always)]
    fn clmul<const I: i32>(a: Self, b: Self) -> Self {
        unsafe { _mm_clmulepi64_si128::<I>(a, b) }
    }
    #[inline(always)]
    fn sl1(a: Self) -> Self {
        unsafe { _mm_slli_epi64::<1>(a) }
    }
    #[inline(always)]
    fn sl3(a: Self) -> Self {
        unsafe { _mm_slli_epi64::<3>(a) }
    }
    #[inline(always)]
    fn sl4(a: Self) -> Self {
        unsafe { _mm_slli_epi64::<4>(a) }
    }
    #[inline(always)]
    fn sr60(a: Self) -> Self {
        unsafe { _mm_srli_epi64::<60>(a) }
    }
    #[inline(always)]
    fn sr61(a: Self) -> Self {
        unsafe { _mm_srli_epi64::<61>(a) }
    }
    #[inline(always)]
    fn sr63(a: Self) -> Self {
        unsafe { _mm_srli_epi64::<63>(a) }
    }
    #[inline(always)]
    fn up(a: Self) -> Self {
        unsafe { _mm_slli_si128::<8>(a) }
    }
    #[inline(always)]
    fn down(a: Self) -> Self {
        unsafe { _mm_srli_si128::<8>(a) }
    }
    #[inline(always)]
    fn low(a: Self) -> Self {
        unsafe { _mm_move_epi64(a) }
    }
    #[inline(always)]
    fn unlo(a: Self, b: Self) -> Self {
        unsafe { _mm_unpacklo_epi64(a, b) }
    }
    #[inline(always)]
    fn unhi(a: Self, b: Self) -> Self {
        unsafe { _mm_unpackhi_epi64(a, b) }
    }
    #[inline(always)]
    fn is_zero(a: Self) -> bool {
        unsafe { _mm_movemask_epi8(_mm_cmpeq_epi8(a, _mm_setzero_si128())) == 0xFFFF }
    }
}

/// The v4 tier: four points per register (AVX512BW for the in-lane byte shifts).
#[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f", target_feature = "avx512bw"))]
impl Lane for __m512i {
    const L: usize = 4;
    // SAFETY (every method): avx512f and vpclmulqdq are enabled at compile time (this impl's cfg); the loads and
    // stores touch `p[..4]` (64 bytes).
    #[inline(always)]
    fn zero() -> Self {
        unsafe { _mm512_setzero_si512() }
    }
    #[inline(always)]
    fn ld(p: &[F128]) -> Self {
        assert!(p.len() >= 4);
        unsafe { _mm512_loadu_si512(p.as_ptr() as *const __m512i) }
    }
    #[inline(always)]
    fn st(p: &mut [F128], v: Self) {
        assert!(p.len() >= 4);
        unsafe { _mm512_storeu_si512(p.as_mut_ptr() as *mut __m512i, v) }
    }
    #[inline(always)]
    fn bc(c: &F128) -> Self {
        unsafe { _mm512_broadcast_i32x4(<__m128i as Lane>::bc(c)) }
    }
    #[inline(always)]
    fn xor(a: Self, b: Self) -> Self {
        unsafe { _mm512_xor_si512(a, b) }
    }
    #[inline(always)]
    fn or(a: Self, b: Self) -> Self {
        unsafe { _mm512_or_si512(a, b) }
    }
    #[inline(always)]
    fn clmul<const I: i32>(a: Self, b: Self) -> Self {
        unsafe { _mm512_clmulepi64_epi128::<I>(a, b) }
    }
    #[inline(always)]
    fn sl1(a: Self) -> Self {
        unsafe { _mm512_slli_epi64::<1>(a) }
    }
    #[inline(always)]
    fn sl3(a: Self) -> Self {
        unsafe { _mm512_slli_epi64::<3>(a) }
    }
    #[inline(always)]
    fn sl4(a: Self) -> Self {
        unsafe { _mm512_slli_epi64::<4>(a) }
    }
    #[inline(always)]
    fn sr60(a: Self) -> Self {
        unsafe { _mm512_srli_epi64::<60>(a) }
    }
    #[inline(always)]
    fn sr61(a: Self) -> Self {
        unsafe { _mm512_srli_epi64::<61>(a) }
    }
    #[inline(always)]
    fn sr63(a: Self) -> Self {
        unsafe { _mm512_srli_epi64::<63>(a) }
    }
    #[inline(always)]
    fn up(a: Self) -> Self {
        unsafe { _mm512_bslli_epi128::<8>(a) }
    }
    #[inline(always)]
    fn down(a: Self) -> Self {
        unsafe { _mm512_bsrli_epi128::<8>(a) }
    }
    #[inline(always)]
    fn low(a: Self) -> Self {
        unsafe { _mm512_maskz_mov_epi64(0x55, a) }
    }
    #[inline(always)]
    fn unlo(a: Self, b: Self) -> Self {
        unsafe { _mm512_unpacklo_epi64(a, b) }
    }
    #[inline(always)]
    fn unhi(a: Self, b: Self) -> Self {
        unsafe { _mm512_unpackhi_epi64(a, b) }
    }
    #[inline(always)]
    fn is_zero(a: Self) -> bool {
        unsafe { _mm512_test_epi64_mask(a, a) == 0 }
    }
}

/// A sum of products `Σ a·b`, unreduced: `lo = Σ a₀b₀`, `hi = Σ a₁b₁`, `mid = Σ (a₀b₁ + a₁b₀)` (128-bit polynomials).
#[derive(Clone, Copy)]
struct Acc<V> {
    lo: V,
    hi: V,
    mid: V,
}

impl<V: Lane> Acc<V> {
    #[inline(always)]
    fn zero() -> Self {
        Acc { lo: V::zero(), hi: V::zero(), mid: V::zero() }
    }

    /// `self += a·b`.
    #[inline(always)]
    fn mac(&mut self, a: V, b: V) {
        self.lo = V::xor(self.lo, V::clmul::<0x00>(a, b));
        self.hi = V::xor(self.hi, V::clmul::<0x11>(a, b));
        self.mid = V::xor(self.mid, V::xor(V::clmul::<0x01>(a, b), V::clmul::<0x10>(a, b)));
    }

    /// The field element: `(a₀ + a₁X)(b₀ + b₁X) = (P₀ + P₁) + (mid + x·P₁)X` (`X² = xX + 1`), each coefficient reduced
    /// modulo `x⁶⁴ + x⁴ + x³ + x + 1` as `gf2_64::reduce` does (the same residue).
    #[inline(always)]
    fn reduce(self) -> V {
        let a = V::xor(self.lo, self.hi);
        // x·P₁: P₁ is a sum of products of 64-bit polynomials (degree ≤ 126), so the 128-bit shift is exact
        let h1 = V::or(V::sl1(self.hi), V::up(V::sr63(self.hi)));
        let b = V::xor(self.mid, h1);
        red2(a, b)
    }
}

/// `(r(a), r(b))` as one element `[c₀, c₁]` per lane: `r(p) = lo ⊕ f(hi ⊕ spill)`, `spill = hi≫63 ⊕ hi≫61 ⊕
/// hi≫60`, `f(v) = v ⊕ v≪1 ⊕ v≪3 ⊕ v≪4` (`gf2_64::reduce`), qword-wise on `[a, b]`'s halves.
#[inline(always)]
fn red2<V: Lane>(a: V, b: V) -> V {
    let (lo, hi) = (V::unlo(a, b), V::unhi(a, b));
    let v = V::xor(V::xor(hi, V::sr63(hi)), V::xor(V::sr61(hi), V::sr60(hi)));
    let w = V::xor(V::xor(v, V::sl1(v)), V::xor(V::sl3(v), V::sl4(v)));
    V::xor(lo, w)
}

/// `a·b`, reduced.
#[inline(always)]
fn mul<V: Lane>(a: V, b: V) -> V {
    let mut t = Acc::zero();
    t.mac(a, b);
    t.reduce()
}

/// The sum of terms `Σ c·a` by the coefficient's kind ([`super::PhiF::coef_kind`]): the unit and `X` terms as plain
/// sums (`X·Σa` once at the end), `(l, 0)` and `(0, l)` by two carry-less products, any other by four.
#[derive(Clone, Copy)]
struct Sub<V> {
    one: V,
    x: V,
    acc: Acc<V>,
}

impl<V: Lane> Sub<V> {
    #[inline(always)]
    fn zero() -> Self {
        Sub { one: V::zero(), x: V::zero(), acc: Acc::zero() }
    }

    /// `self += c·a`, `c` (in every lane) of kind `k`.
    #[inline(always)]
    fn add(&mut self, k: u8, c: V, a: V) {
        match k {
            CK_ONE => self.one = V::xor(self.one, a),
            CK_X => self.x = V::xor(self.x, a),
            // (a₀ + a₁X)·l: lo += a₀l, mid += a₁l
            CK_K => {
                self.acc.lo = V::xor(self.acc.lo, V::clmul::<0x00>(a, c));
                self.acc.mid = V::xor(self.acc.mid, V::clmul::<0x01>(a, c));
            }
            // (a₀ + a₁X)·lX: mid += a₀l, hi += a₁l
            CK_KX => {
                self.acc.mid = V::xor(self.acc.mid, V::clmul::<0x10>(a, c));
                self.acc.hi = V::xor(self.acc.hi, V::clmul::<0x11>(a, c));
            }
            _ => self.acc.mac(a, c),
        }
    }

    /// The sum, reduced; `prod`: some term had a product, `xs`: some term had `X` (else `acc` is zero).
    #[inline(always)]
    fn reduce(mut self, prod: bool, xs: bool) -> V {
        if xs {
            // X·(s₀ + s₁X): hi += s₁, mid += s₀ (as 64-bit polynomials)
            self.acc.hi = V::xor(self.acc.hi, V::down(self.x));
            self.acc.mid = V::xor(self.acc.mid, V::low(self.x));
        }
        if prod || xs { V::xor(self.acc.reduce(), self.one) } else { self.one }
    }
}

/// The `N = Q·L` points of row `i` of a point-minor table.
#[inline(always)]
fn row<V: Lane, const Q: usize>(t: &[F128], i: usize) -> [V; Q] {
    let n = Q * V::L;
    let r = &t[i * n..][..n];
    std::array::from_fn(|q| V::ld(&r[q * V::L..]))
}

#[inline(always)]
fn put<V: Lane, const Q: usize>(t: &mut [F128], i: usize, v: &[V; Q]) {
    let n = Q * V::L;
    let r = &mut t[i * n..][..n];
    for q in 0..Q {
        V::st(&mut r[q * V::L..], v[q]);
    }
}

/// `t[i] += v` (row `i`).
#[inline(always)]
fn add_to<V: Lane, const Q: usize>(t: &mut [F128], i: usize, v: &[V; Q]) {
    let w = row::<V, Q>(t, i);
    put::<V, Q>(t, i, &std::array::from_fn(|q| V::xor(w[q], v[q])));
}

/// The automaton's passes `r` at `Q·L` points.
pub(super) fn run_auto<V: Lane, const Q: usize>(pk: &PhiK<F128>, tb: &Tabs<F128>, r: Range<usize>, out: &mut [F128]) {
    debug_assert_eq!(tb.np, Q * V::L);
    for ps in &pk.passes[r] {
        eval_pass::<V, Q>(pk, tb, ps, out);
    }
}

/// [`super::PhiK::plan_lists`]: the inner lists `r`'s sums into `s`.
pub(super) fn plan_lists<V: Lane, const Q: usize>(pk: &PhiK<F128>, tb: &Tabs<F128>, r: Range<usize>, s: &mut [F128]) {
    debug_assert_eq!(tb.np, Q * V::L);
    let pl = pk.plan.as_ref().unwrap();
    for (k, l) in r.enumerate() {
        let tab = if pl.lside[l] { &tb.x.lo[0][..] } else { &tb.y.lo[0][..] };
        let mut sub = [Sub::<V>::zero(); Q];
        let (mut prod, mut xk) = (false, false);
        for &(rw, c) in &pl.lent[pl.lptr[l] as usize..pl.lptr[l + 1] as usize] {
            let v = row::<V, Q>(tab, rw as usize);
            let (kd, cv) = (pk.ckind[c as usize], V::bc(&pk.coefs[c as usize]));
            prod |= kd >= CK_K;
            xk |= kd == CK_X;
            for q in 0..Q {
                sub[q].add(kd, cv, v[q]);
            }
        }
        put::<V, Q>(s, k, &std::array::from_fn(|q| sub[q].reduce(prod, xk)));
    }
}

/// [`super::PhiK::plan_sigs`]: the signatures `r`'s sums from the lists' sums `s`, then their instances.
pub(super) fn plan_sigs<V: Lane, const Q: usize>(pk: &PhiK<F128>, tb: &Tabs<F128>, s: &[F128], r: Range<usize>, out: &mut [F128]) {
    debug_assert_eq!(tb.np, Q * V::L);
    let n = Q * V::L;
    let pl = pk.plan.as_ref().unwrap();
    let one = vec![F128::ONE; n];
    for sg in r {
        let mut acc = [Acc::<V>::zero(); Q];
        for t in pl.tptr[sg] as usize..pl.tptr[sg + 1] as usize {
            let mut u = [V::zero(); Q];
            for &rf in &pl.refs[pl.rptr[t] as usize..pl.rptr[t + 1] as usize] {
                let o = row::<V, Q>(PhiK::outer(tb, rf, n, &one), 0);
                for q in 0..Q {
                    u[q] = V::xor(u[q], o[q]);
                }
            }
            let sl = row::<V, Q>(s, pl.tlist[t] as usize);
            for q in 0..Q {
                acc[q].mac(u[q], sl[q]);
            }
        }
        let g: [V; Q] = std::array::from_fn(|q| acc[q].reduce());
        for it in &pl.inst[pl.iptr[sg] as usize..pl.iptr[sg + 1] as usize] {
            let hx = row::<V, Q>(&tb.x.hi[it.hj as usize], it.hx as usize);
            let hy = row::<V, Q>(&tb.y.hi[0], it.hy as usize);
            let mut v: [V; Q] = std::array::from_fn(|q| mul(mul(g[q], hx[q]), hy[q]));
            if it.pat != NONE {
                let pt = row::<V, Q>(&tb.pat, it.pat as usize);
                v = std::array::from_fn(|q| mul(v[q], pt[q]));
            }
            add_to::<V, Q>(out, it.o as usize, &v);
        }
    }
}

/// [`Lev::get`]: `eq(r[ell..n], v)` at the batch's points, `None` outside the cube.
#[inline(always)]
fn lev_get<V: Lane, const Q: usize>(lv: &Lev<F128>, ell: usize, v: i64) -> Option<[V; Q]> {
    if v < 0 || (ell < lv.n && (v as u64) >> (lv.n - ell) != 0) || (ell >= lv.n && v != 0) {
        return None;
    }
    let v = v as usize;
    Some(if ell <= lv.s {
        let w = lv.s - ell;
        let (l, h) = (v & ((1 << w) - 1), v >> w);
        let (a, b) = (row::<V, Q>(&lv.lo[ell], l), row::<V, Q>(&lv.hi[0], h));
        std::array::from_fn(|q| mul(a[q], b[q]))
    } else {
        row::<V, Q>(&lv.hi[ell - lv.s], v)
    })
}

/// [`super::PhiK::eval_pass`]: the carry automaton of one pass, its states' weights a row each.
fn eval_pass<V: Lane, const Q: usize>(pk: &PhiK<F128>, tb: &Tabs<F128>, ps: &Pass, out: &mut [F128]) {
    let sh = &pk.shapes[ps.shape as usize];
    let ell = sh.ell as usize;
    let one = V::bc(&F128::ONE);
    // initial states: offsets 0..=span
    let (mut lo, mut hi) = (0i64, ps.span as i64);
    let mut w: Vec<[V; Q]> = vec![[V::zero(); Q]; (hi - lo + 1) as usize];
    for m in &pk.mem[ps.mlo as usize..ps.mhi as usize] {
        let mut ex = lev_get::<V, Q>(&tb.x, ell, (m.x0 >> ell) as i64).expect("a member's slot is in range");
        let mut mk = m.mask;
        while mk != 0 {
            let i = mk.trailing_zeros() as usize;
            mk &= mk - 1;
            let r = row::<V, Q>(&tb.rx, i);
            let set = (m.x0 >> i) & 1 == 1;
            for q in 0..Q {
                ex[q] = mul(ex[q], if set { r[q] } else { V::xor(one, r[q]) });
            }
        }
        let dst = &mut w[m.delta as usize];
        if m.c == 0 {
            for q in 0..Q {
                dst[q] = V::xor(dst[q], ex[q]);
            }
        } else {
            let c = V::bc(&pk.coefs[m.c as usize]);
            for q in 0..Q {
                dst[q] = V::xor(dst[q], mul(ex[q], c));
            }
        }
    }
    let n = Q * V::L;
    let mut li = 0;
    let mut fac: Vec<F128> = vec![F128::ZERO; (2 << MAX_LEVEL_BITS) * n];
    let mut nw: Vec<[Acc<V>; Q]> = Vec::with_capacity(w.len() * 2);
    let yl = pk.y_log;
    for k in 0..sh.kstop as usize {
        let bits: &[(u8, i64)] = if li < sh.levels.len() && sh.levels[li].0 as usize == k {
            li += 1;
            &sh.levels[li - 1].1
        } else {
            &[]
        };
        let nb = bits.len();
        // fac[(assignment, e)] = Π_i eq(rx_i, b_i) · eq(ry_k, e): the shared tables for nb ≤ 1
        let shared: Option<&[F128]> = match bits {
            [] => Some(&tb.fy[2 * k * n..][..2 * n]),
            [(i, _)] => Some(&tb.fxy[(*i as usize * yl + k) * 4 * n..][..4 * n]),
            _ => None,
        };
        if shared.is_none() {
            let ry = row::<V, Q>(&tb.ry, k);
            for asg in 0..1usize << nb {
                let mut f = [one; Q];
                for (j, &(i, _)) in bits.iter().enumerate() {
                    let r = row::<V, Q>(&tb.rx, i as usize);
                    for q in 0..Q {
                        f[q] = mul(f[q], if (asg >> j) & 1 == 1 { r[q] } else { V::xor(one, r[q]) });
                    }
                }
                put::<V, Q>(&mut fac, 2 * asg, &std::array::from_fn(|q| mul(f[q], V::xor(one, ry[q]))));
                put::<V, Q>(&mut fac, 2 * asg + 1, &std::array::from_fn(|q| mul(f[q], ry[q])));
            }
        }
        let ftab: &[F128] = shared.unwrap_or(&fac);
        let ybit = (ps.ybase >> k) & 1;
        let mut sums = [0i64; 1 << MAX_LEVEL_BITS];
        for (asg, sm) in sums.iter_mut().enumerate().take(1 << nb) {
            *sm = bits.iter().enumerate().filter(|(j, _)| (asg >> j) & 1 == 1).map(|(_, &(_, c))| c).sum();
        }
        let sums = &sums[..1 << nb];
        let (neg, pos) = (*sums.iter().min().unwrap(), *sums.iter().max().unwrap());
        let (nlo, nhi) = ((lo + ybit + neg).div_euclid(2), (hi + ybit + pos).div_euclid(2));
        nw.clear();
        nw.resize((nhi - nlo + 1) as usize, [Acc::zero(); Q]);
        for s in lo..=hi {
            let ws = &w[(s - lo) as usize];
            if ws.iter().all(|&v| V::is_zero(v)) {
                continue;
            }
            for (asg, &sm) in sums.iter().enumerate() {
                let t = s + ybit + sm;
                let e = (t & 1) as usize;
                let ns = t.div_euclid(2);
                let f = row::<V, Q>(ftab, 2 * asg + e);
                let d = &mut nw[(ns - nlo) as usize];
                for q in 0..Q {
                    d[q].mac(ws[q], f[q]);
                }
            }
        }
        w.clear();
        w.extend(nw.iter().map(|a| std::array::from_fn(|q| a[q].reduce())));
        lo = nlo;
        hi = nhi;
    }
    // finish: eq(ry[kstop..], (ybase >> kstop) + s)
    let kk = sh.kstop as usize;
    let mut acc = [Acc::<V>::zero(); Q];
    for s in lo..=hi {
        if let Some(ey) = lev_get::<V, Q>(&tb.y, kk, (ps.ybase >> kk) + s) {
            let ws = &w[(s - lo) as usize];
            for q in 0..Q {
                acc[q].mac(ws[q], ey[q]);
            }
        }
    }
    add_to::<V, Q>(out, ps.o as usize, &std::array::from_fn(|q| acc[q].reduce()));
}

/// [`Lev::new`]: the tables point-minor from the start, each level from the next (`eq(r[ℓ..s], v) =
/// eq(r[ℓ+1..s], v ≫ 1)·eq(r_ℓ, v & 1)`; the same products as `eq_table`'s, in another order).
pub(super) fn lev_new(rs: &[&[F128]], s: usize) -> Lev<F128> {
    type X = __m128i;
    let np = rs.len();
    let n = rs[0].len();
    let s = s.min(n);
    // suffix tables eq(r[a..b]) for a = b down to lo, point-minor; `out[k]` = eq(r[lo + k..b])
    let suffixes = |lo: usize, b: usize| -> Vec<Vec<F128>> {
        let mut out: Vec<Vec<F128>> = vec![Vec::new(); b - lo + 1];
        out[b - lo] = vec![F128::ONE; np];
        for a in (lo..b).rev() {
            let (head, tail) = out.split_at_mut(a - lo + 1);
            let next = &tail[0];
            let m = 1usize << (b - a);
            let mut t = vec![F128::ZERO; m * np];
            let r: Vec<X> = rs.iter().map(|rp| X::bc(&rp[a])).collect();
            // entries 2v + 1 and 2v from entry v: `e·r` and `e·(1 + r) = e + e·r`
            for v in 0..m / 2 {
                for p in 0..np {
                    let e = X::ld(&next[v * np + p..]);
                    let er = mul(e, r[p]);
                    X::st(&mut t[(2 * v + 1) * np + p..], er);
                    X::st(&mut t[2 * v * np + p..], X::xor(e, er));
                }
            }
            head[a - lo] = t;
        }
        out
    };
    let lo = suffixes(0, s);
    let hi = suffixes(s, n);
    Lev { s, n, lo, hi }
}
