//! GF(2^128) in Flock's GHASH form (x^128 + x^7 + x^2 + x + 1, `lo` = x^0..x^63, no bit
//! reflection; Flock `crates/flock-field/src/gf2_128.rs`), and K = GF(2^256) = F[u]/(u^2+u+x^-1)
//! (Flock `gf2_256.rs`). Tiers, chosen at run time:
//! - portable: 4-bit-window carry-less multiply (only so the probe runs on a CPU without clmul);
//! - pclmul: scalar PCLMULQDQ, Flock's x86 `ghash_mul_karatsuba_barrett` (5 CLMUL, lane extracts)
//!   and an xmm-resident schoolbook + two-fold reduction (Flock's `ghash_mul_binius`, 6 CLMUL);
//! - ymm: 256-bit VPCLMULQDQ, two products per instruction (Flock's `ghash_mul_x4` narrowed);
//! - zmm: 512-bit VPCLMULQDQ, four products per instruction (Flock's `ghash_mul_x4`, verbatim).
#![allow(clippy::missing_safety_doc)]
use std::arch::x86_64::*;

#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
#[repr(C, align(16))]
pub struct F128 {
    pub lo: u64,
    pub hi: u64,
}

impl F128 {
    pub const ZERO: F128 = F128 { lo: 0, hi: 0 };
    pub const ONE: F128 = F128 { lo: 1, hi: 0 };
    #[inline(always)]
    pub const fn new(lo: u64, hi: u64) -> Self {
        F128 { lo, hi }
    }
}
impl std::ops::Add for F128 {
    type Output = F128;
    #[inline(always)]
    fn add(self, o: F128) -> F128 {
        F128 { lo: self.lo ^ o.lo, hi: self.hi ^ o.hi }
    }
}
impl std::ops::AddAssign for F128 {
    #[inline(always)]
    fn add_assign(&mut self, o: F128) {
        self.lo ^= o.lo;
        self.hi ^= o.hi;
    }
}

/// Flock's `ghash_reduce`: r0 + r1 x^64 + r2 x^128 + r3 x^192 mod p.
#[inline(always)]
pub fn reduce(r0: u64, r1: u64, r2: u64, r3: u64) -> F128 {
    let s1_lo = r2 << 1;
    let s1_hi = (r3 << 1) | (r2 >> 63);
    let s2_lo = r2 << 2;
    let s2_hi = (r3 << 2) | (r2 >> 62);
    let s7_lo = r2 << 7;
    let s7_hi = (r3 << 7) | (r2 >> 57);
    let t_lo = r2 ^ s1_lo ^ s2_lo ^ s7_lo;
    let t_hi = r3 ^ s1_hi ^ s2_hi ^ s7_hi;
    let ov = (r3 >> 63) ^ (r3 >> 62) ^ (r3 >> 57);
    let corr = ov ^ (ov << 1) ^ (ov << 2) ^ (ov << 7);
    F128 { lo: r0 ^ t_lo ^ corr, hi: r1 ^ t_hi }
}

// ---------------------------------------------------------------- portable

#[inline(always)]
pub fn clmul64_portable(a: u64, b: u64) -> (u64, u64) {
    let mut tlo = [0u64; 16];
    let mut thi = [0u64; 16];
    for i in 1..16usize {
        let low = i & i.wrapping_neg();
        let s = low.trailing_zeros();
        let (l, h) = (a << s, if s == 0 { 0 } else { a >> (64 - s) });
        tlo[i] = tlo[i ^ low] ^ l;
        thi[i] = thi[i ^ low] ^ h;
    }
    let (mut lo, mut hi) = (0u64, 0u64);
    for nib in (0..16).rev() {
        hi = (hi << 4) | (lo >> 60);
        lo <<= 4;
        let n = ((b >> (4 * nib)) & 15) as usize;
        lo ^= tlo[n];
        hi ^= thi[n];
    }
    (lo, hi)
}

pub fn mul_portable(a: F128, b: F128) -> F128 {
    let (ll0, ll1) = clmul64_portable(a.lo, b.lo);
    let (lh0, lh1) = clmul64_portable(a.lo, b.hi);
    let (hl0, hl1) = clmul64_portable(a.hi, b.lo);
    let (hh0, hh1) = clmul64_portable(a.hi, b.hi);
    reduce(ll0, ll1 ^ lh0 ^ hl0, hh0 ^ lh1 ^ hl1, hh1)
}

pub fn inv_portable(a: F128) -> F128 {
    let mut r = F128::ONE;
    let mut cur = mul_portable(a, a);
    for _ in 1..128 {
        r = mul_portable(r, cur);
        cur = mul_portable(cur, cur);
    }
    r
}

/// Multiply by x^-1 (cheap: a shift and a conditional fold).
#[inline(always)]
pub fn mul_xinv(z: F128) -> F128 {
    let c = z.lo & 1;
    let lo = z.lo ^ (c.wrapping_neg() & 0x87);
    F128 { lo: (lo >> 1) | (z.hi << 63), hi: (z.hi >> 1) | (c << 63) }
}

// ---------------------------------------------------------------- CPU tiers

#[derive(Clone, Copy, Debug)]
pub struct Cpu {
    pub pclmul: bool,
    pub ymm: bool,
    pub zmm: bool,
    pub gfni: bool,
}

pub fn cpu() -> Cpu {
    let pclmul = is_x86_feature_detected!("pclmulqdq") && is_x86_feature_detected!("sse4.1");
    let ymm = pclmul && is_x86_feature_detected!("avx2") && is_x86_feature_detected!("vpclmulqdq");
    let zmm = ymm && is_x86_feature_detected!("avx512f") && is_x86_feature_detected!("avx512bw");
    Cpu { pclmul, ymm, zmm, gfni: is_x86_feature_detected!("gfni") }
}

// ---------------------------------------------------------------- scalar PCLMULQDQ

#[inline]
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn pmull(a: u64, b: u64) -> __m128i {
    _mm_clmulepi64_si128::<0x00>(_mm_set_epi64x(0, a as i64), _mm_set_epi64x(0, b as i64))
}
#[inline(always)]
unsafe fn l0(v: __m128i) -> u64 {
    _mm_cvtsi128_si64(v) as u64
}
#[inline]
#[target_feature(enable = "sse4.1")]
unsafe fn l1(v: __m128i) -> u64 {
    _mm_extract_epi64::<1>(v) as u64
}

/// Flock's x86 default `Mul` (`ghash_mul_karatsuba_barrett`), verbatim.
#[inline]
#[target_feature(enable = "pclmulqdq,sse4.1")]
pub unsafe fn mul_pclmul(a: F128, b: F128) -> F128 {
    let d0 = pmull(a.lo, b.lo);
    let d2 = pmull(a.hi, b.hi);
    let dm = pmull(a.lo ^ a.hi, b.lo ^ b.hi);
    let d1 = _mm_xor_si128(_mm_xor_si128(dm, d0), d2);
    let lo_lo = l0(d0);
    let lo_hi = l1(d0) ^ l0(d1);
    let hi_lo = l0(d2) ^ l1(d1);
    let hi_hi = l1(d2);
    let r_hi = pmull(hi_hi, 0x87);
    let r_lo = pmull(hi_lo, 0x87);
    let ov = l1(r_hi);
    let corr = ov ^ (ov << 1) ^ (ov << 2) ^ (ov << 7);
    F128 { lo: lo_lo ^ l0(r_lo) ^ corr, hi: lo_hi ^ l1(r_lo) ^ l0(r_hi) }
}

/// Flock's `ghash_mul_unreduced_x86`: 4 CLMUL, 256-bit result for deferred reduction.
#[inline]
#[target_feature(enable = "pclmulqdq,sse4.1")]
pub unsafe fn mul_unreduced_pclmul(a: F128, b: F128) -> [u64; 4] {
    let p_ll = pmull(a.lo, b.lo);
    let p_lh = pmull(a.lo, b.hi);
    let p_hl = pmull(a.hi, b.lo);
    let p_hh = pmull(a.hi, b.hi);
    let cross = _mm_xor_si128(p_lh, p_hl);
    [l0(p_ll), l1(p_ll) ^ l0(cross), l0(p_hh) ^ l1(cross), l1(p_hh)]
}

#[inline(always)]
pub unsafe fn to_x(a: F128) -> __m128i {
    _mm_loadu_si128(&a as *const F128 as *const __m128i)
}
#[inline(always)]
pub unsafe fn from_x(v: __m128i) -> F128 {
    let mut o = F128::ZERO;
    _mm_storeu_si128(&mut o as *mut F128 as *mut __m128i, v);
    o
}

/// xmm-resident product (Flock `ghash_mul_binius` with vector lanes kept in the register file).
#[inline]
#[target_feature(enable = "pclmulqdq,sse4.1")]
pub unsafe fn mul_xmm(x: __m128i, y: __m128i) -> __m128i {
    let poly = _mm_set_epi64x(0, 0x87);
    let mut t1 = _mm_xor_si128(_mm_clmulepi64_si128::<0x01>(x, y), _mm_clmulepi64_si128::<0x10>(x, y));
    let t2 = _mm_clmulepi64_si128::<0x11>(x, y);
    t1 = _mm_xor_si128(t1, _mm_xor_si128(_mm_slli_si128::<8>(t2), _mm_clmulepi64_si128::<0x01>(t2, poly)));
    let t0 = _mm_clmulepi64_si128::<0x00>(x, y);
    _mm_xor_si128(t0, _mm_xor_si128(_mm_slli_si128::<8>(t1), _mm_clmulepi64_si128::<0x01>(t1, poly)))
}

/// xmm unreduced accumulator {lo, mid, hi}.
#[derive(Clone, Copy)]
pub struct Wide1 {
    pub lo: __m128i,
    pub mid: __m128i,
    pub hi: __m128i,
}
impl Wide1 {
    #[inline]
    #[target_feature(enable = "sse2")]
    pub unsafe fn zero() -> Self {
        Wide1 { lo: _mm_setzero_si128(), mid: _mm_setzero_si128(), hi: _mm_setzero_si128() }
    }
    #[inline]
    #[target_feature(enable = "pclmulqdq,sse4.1")]
    pub unsafe fn mac(&mut self, x: __m128i, y: __m128i) {
        self.lo = _mm_xor_si128(self.lo, _mm_clmulepi64_si128::<0x00>(x, y));
        self.hi = _mm_xor_si128(self.hi, _mm_clmulepi64_si128::<0x11>(x, y));
        self.mid = _mm_xor_si128(
            self.mid,
            _mm_xor_si128(_mm_clmulepi64_si128::<0x01>(x, y), _mm_clmulepi64_si128::<0x10>(x, y)),
        );
    }
    #[inline]
    #[target_feature(enable = "pclmulqdq,sse4.1")]
    pub unsafe fn reduce(self) -> __m128i {
        let poly = _mm_set_epi64x(0, 0x87);
        let t1 = _mm_xor_si128(
            self.mid,
            _mm_xor_si128(_mm_slli_si128::<8>(self.hi), _mm_clmulepi64_si128::<0x01>(self.hi, poly)),
        );
        _mm_xor_si128(self.lo, _mm_xor_si128(_mm_slli_si128::<8>(t1), _mm_clmulepi64_si128::<0x01>(t1, poly)))
    }
}

// ---------------------------------------------------------------- ymm VPCLMULQDQ (2 lanes)

#[inline]
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
pub unsafe fn red_y(t0: __m256i, t1: __m256i) -> __m256i {
    let poly = _mm256_set_epi64x(0, 0x87, 0, 0x87);
    _mm256_xor_si256(t0, _mm256_xor_si256(_mm256_bslli_epi128::<8>(t1), _mm256_clmulepi64_epi128::<0x01>(t1, poly)))
}

/// Two independent products per call: schoolbook 4 + two-fold reduction 2 VPCLMULQDQ.
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
pub unsafe fn mul_y(x: __m256i, y: __m256i) -> __m256i {
    let mut t1 = _mm256_xor_si256(_mm256_clmulepi64_epi128::<0x01>(x, y), _mm256_clmulepi64_epi128::<0x10>(x, y));
    let t2 = _mm256_clmulepi64_epi128::<0x11>(x, y);
    t1 = red_y(t1, t2);
    red_y(_mm256_clmulepi64_epi128::<0x00>(x, y), t1)
}

/// Karatsuba variant: 3 + 2 VPCLMULQDQ; `yk` must be `y ^ swap64(y)` (precomputed for constants).
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
pub unsafe fn mul_y_kara(x: __m256i, y: __m256i, yk: __m256i) -> __m256i {
    let xk = _mm256_xor_si256(x, _mm256_shuffle_epi32::<0x4E>(x));
    let d0 = _mm256_clmulepi64_epi128::<0x00>(x, y);
    let d2 = _mm256_clmulepi64_epi128::<0x11>(x, y);
    let dm = _mm256_clmulepi64_epi128::<0x00>(xk, yk);
    let d1 = _mm256_xor_si256(dm, _mm256_xor_si256(d0, d2));
    red_y(d0, red_y(d1, d2))
}
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn kara_pre_y(y: __m256i) -> __m256i {
    _mm256_xor_si256(y, _mm256_shuffle_epi32::<0x4E>(y))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn bcast_y(a: F128) -> __m256i {
    _mm256_broadcastsi128_si256(to_x(a))
}
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn ld_y(p: *const F128) -> __m256i {
    _mm256_loadu_si256(p as *const __m256i)
}
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn st_y(p: *mut F128, v: __m256i) {
    _mm256_storeu_si256(p as *mut __m256i, v)
}
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn pair_y(a: F128, b: F128) -> __m256i {
    _mm256_set_m128i(to_x(b), to_x(a))
}
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn fold_y(v: __m256i) -> __m128i {
    _mm_xor_si128(_mm256_castsi256_si128(v), _mm256_extracti128_si256::<1>(v))
}

/// ymm unreduced accumulator (Flock `WideGhashX4` at width 2).
#[derive(Clone, Copy)]
pub struct Wide2 {
    pub lo: __m256i,
    pub mid: __m256i,
    pub hi: __m256i,
}
impl Wide2 {
    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn zero() -> Self {
        Wide2 { lo: _mm256_setzero_si256(), mid: _mm256_setzero_si256(), hi: _mm256_setzero_si256() }
    }
    #[inline]
    #[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
    pub unsafe fn mac(&mut self, x: __m256i, y: __m256i) {
        self.lo = _mm256_xor_si256(self.lo, _mm256_clmulepi64_epi128::<0x00>(x, y));
        self.hi = _mm256_xor_si256(self.hi, _mm256_clmulepi64_epi128::<0x11>(x, y));
        self.mid = _mm256_xor_si256(
            self.mid,
            _mm256_xor_si256(_mm256_clmulepi64_epi128::<0x01>(x, y), _mm256_clmulepi64_epi128::<0x10>(x, y)),
        );
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn add(&mut self, o: &Wide2) {
        self.lo = _mm256_xor_si256(self.lo, o.lo);
        self.mid = _mm256_xor_si256(self.mid, o.mid);
        self.hi = _mm256_xor_si256(self.hi, o.hi);
    }
    /// Reduce each lane; returns the two reduced lanes.
    #[inline]
    #[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
    pub unsafe fn reduce_lanes(self) -> __m256i {
        red_y(self.lo, red_y(self.mid, self.hi))
    }
    #[inline]
    #[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
    pub unsafe fn reduce_sum(self) -> F128 {
        from_x(fold_y(self.reduce_lanes()))
    }
}

/// K x K for packed K elements (one K = [c0, c1] = one ymm): returns (p01 = [a0b0, a1b1], pm =
/// (a0+a1)(b0+b1) in lane 0). Caller combines: c0 = p0 + x^-1 p1, c1 = pm + p0.
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
pub unsafe fn k_combine(p01: __m256i, pm: __m128i) -> __m256i {
    // c0 = p0 + x^-1 p1 ; c1 = pm + p0
    let p0 = _mm256_castsi256_si128(p01);
    let p1 = _mm256_extracti128_si256::<1>(p01);
    let p1x = to_x(mul_xinv(from_x(p1)));
    _mm256_set_m128i(_mm_xor_si128(pm, p0), _mm_xor_si128(p0, p1x))
}
/// Two K x K products: (a, b) and (c, d), each K packed in a ymm. 3 ymm products.
#[inline]
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
pub unsafe fn k_mul2(a: __m256i, b: __m256i, c: __m256i, d: __m256i) -> (__m256i, __m256i) {
    let p_ab = mul_y(a, b);
    let p_cd = mul_y(c, d);
    // (a0+a1) and (c0+c1) into one ymm, likewise (b0+b1), (d0+d1)
    let s_a = fold_y(a);
    let s_c = fold_y(c);
    let s_b = fold_y(b);
    let s_d = fold_y(d);
    let pm = mul_y(_mm256_set_m128i(s_c, s_a), _mm256_set_m128i(s_d, s_b));
    (k_combine(p_ab, _mm256_castsi256_si128(pm)), k_combine(p_cd, _mm256_extracti128_si256::<1>(pm)))
}

/// Portable K x K, the reference.
pub fn k_mul_portable(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    let p0 = mul_portable(a[0], b[0]);
    let p1 = mul_portable(a[1], b[1]);
    let pm = mul_portable(a[0] + a[1], b[0] + b[1]);
    [p0 + mul_xinv(p1), pm + p0]
}

// ---------------------------------------------------------------- zmm VPCLMULQDQ (4 lanes)

#[inline]
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
pub unsafe fn red_z(t0: __m512i, t1: __m512i) -> __m512i {
    let poly = _mm512_set_epi64(0, 0x87, 0, 0x87, 0, 0x87, 0, 0x87);
    _mm512_xor_si512(t0, _mm512_xor_si512(_mm512_bslli_epi128::<8>(t1), _mm512_clmulepi64_epi128::<0x01>(t1, poly)))
}
/// Flock's `ghash_mul_x4`.
#[inline]
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
pub unsafe fn mul_z(x: __m512i, y: __m512i) -> __m512i {
    let mut t1 = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x01>(x, y), _mm512_clmulepi64_epi128::<0x10>(x, y));
    let t2 = _mm512_clmulepi64_epi128::<0x11>(x, y);
    t1 = red_z(t1, t2);
    red_z(_mm512_clmulepi64_epi128::<0x00>(x, y), t1)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn bcast_z(a: F128) -> __m512i {
    _mm512_broadcast_i32x4(to_x(a))
}
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn ld_z(p: *const F128) -> __m512i {
    _mm512_loadu_si512(p as *const __m512i)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn st_z(p: *mut F128, v: __m512i) {
    _mm512_storeu_si512(p as *mut __m512i, v)
}
#[derive(Clone, Copy)]
pub struct Wide4 {
    pub lo: __m512i,
    pub mid: __m512i,
    pub hi: __m512i,
}
impl Wide4 {
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub unsafe fn zero() -> Self {
        Wide4 { lo: _mm512_setzero_si512(), mid: _mm512_setzero_si512(), hi: _mm512_setzero_si512() }
    }
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
    pub unsafe fn mac(&mut self, x: __m512i, y: __m512i) {
        self.lo = _mm512_xor_si512(self.lo, _mm512_clmulepi64_epi128::<0x00>(x, y));
        self.hi = _mm512_xor_si512(self.hi, _mm512_clmulepi64_epi128::<0x11>(x, y));
        self.mid = _mm512_xor_si512(
            self.mid,
            _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x01>(x, y), _mm512_clmulepi64_epi128::<0x10>(x, y)),
        );
    }
    #[inline]
    #[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
    pub unsafe fn reduce_sum(self) -> F128 {
        let r = red_z(self.lo, red_z(self.mid, self.hi));
        let a = _mm512_extracti32x4_epi32::<0>(r);
        let b = _mm512_extracti32x4_epi32::<1>(r);
        let c = _mm512_extracti32x4_epi32::<2>(r);
        let d = _mm512_extracti32x4_epi32::<3>(r);
        from_x(_mm_xor_si128(_mm_xor_si128(a, b), _mm_xor_si128(c, d)))
    }
}

// ---------------------------------------------------------------- tier-generic scalar mul

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Tier {
    Portable,
    Pclmul,
    Ymm,
    Zmm,
}
impl Tier {
    pub fn name(self) -> &'static str {
        match self {
            Tier::Portable => "portable",
            Tier::Pclmul => "pclmul",
            Tier::Ymm => "ymm-vpclmul",
            Tier::Zmm => "zmm-vpclmul",
        }
    }
}
pub fn tiers(c: Cpu) -> Vec<Tier> {
    let mut v = vec![];
    if c.pclmul {
        v.push(Tier::Pclmul);
    }
    if c.ymm {
        v.push(Tier::Ymm);
    }
    if c.zmm {
        v.push(Tier::Zmm);
    }
    if v.is_empty() {
        v.push(Tier::Portable);
    }
    v
}
/// The best scalar product available (used outside the hot loops).
#[inline]
pub fn mul(a: F128, b: F128) -> F128 {
    if crate::CPU.get().map(|c| c.pclmul).unwrap_or(false) {
        unsafe { mul_pclmul(a, b) }
    } else {
        mul_portable(a, b)
    }
}

// ---------------------------------------------------------------- self-test

pub fn selftest(c: Cpu, rng: &mut crate::Rng) -> Result<(), String> {
    // field sanity on the portable reference
    let x64 = F128::new(0, 1);
    if mul_portable(x64, x64) != F128::new(0x87, 0) {
        return Err("x^64 * x^64 != x^7+x^2+x+1".into());
    }
    for _ in 0..200 {
        let (a, b, d) = (rng.f(), rng.f(), rng.f());
        if mul_portable(mul_portable(a, b), d) != mul_portable(a, mul_portable(b, d)) {
            return Err("portable mul not associative".into());
        }
        if mul_portable(a, b + d) != mul_portable(a, b) + mul_portable(a, d) {
            return Err("portable mul not distributive".into());
        }
        if mul_xinv(mul_portable(a, F128::new(2, 0))) != a {
            return Err("x^-1 wrong".into());
        }
    }
    let a = rng.f();
    if mul_portable(a, inv_portable(a)) != F128::ONE {
        return Err("inverse wrong".into());
    }
    unsafe {
        for _ in 0..1000 {
            let (a, b, e, f) = (rng.f(), rng.f(), rng.f(), rng.f());
            let r1 = mul_portable(a, b);
            let r2 = mul_portable(e, f);
            if c.pclmul {
                if mul_pclmul(a, b) != r1 {
                    return Err("pclmul karatsuba mismatch".into());
                }
                if from_x(mul_xmm(to_x(a), to_x(b))) != r1 {
                    return Err("xmm mul mismatch".into());
                }
                let u = mul_unreduced_pclmul(a, b);
                if reduce(u[0], u[1], u[2], u[3]) != r1 {
                    return Err("unreduced mismatch".into());
                }
                let mut w = Wide1::zero();
                w.mac(to_x(a), to_x(b));
                w.mac(to_x(e), to_x(f));
                if from_x(w.reduce()) != r1 + r2 {
                    return Err("Wide1 mismatch".into());
                }
            }
            if c.ymm {
                let mut out = [F128::ZERO; 2];
                st_y(out.as_mut_ptr(), mul_y(pair_y(a, e), pair_y(b, f)));
                if out != [r1, r2] {
                    return Err("ymm mul mismatch".into());
                }
                let yb = pair_y(b, f);
                st_y(out.as_mut_ptr(), mul_y_kara(pair_y(a, e), yb, kara_pre_y(yb)));
                if out != [r1, r2] {
                    return Err("ymm karatsuba mismatch".into());
                }
                let mut w = Wide2::zero();
                w.mac(pair_y(a, e), pair_y(b, f));
                if w.reduce_sum() != r1 + r2 {
                    return Err("Wide2 mismatch".into());
                }
                let (ka, kb, kc, kd) = ([a, b], [e, f], [b, e], [f, a]);
                let (p, q) = k_mul2(pair_y(ka[0], ka[1]), pair_y(kb[0], kb[1]), pair_y(kc[0], kc[1]), pair_y(kd[0], kd[1]));
                st_y(out.as_mut_ptr(), p);
                if out != k_mul_portable(ka, kb) {
                    return Err("K mul mismatch".into());
                }
                st_y(out.as_mut_ptr(), q);
                if out != k_mul_portable(kc, kd) {
                    return Err("K mul (2nd) mismatch".into());
                }
            }
            if c.zmm {
                let xs = [a, e, b, f];
                let ys = [b, f, e, a];
                let mut out = [F128::ZERO; 4];
                st_z(out.as_mut_ptr(), mul_z(ld_z(xs.as_ptr()), ld_z(ys.as_ptr())));
                for i in 0..4 {
                    if out[i] != mul_portable(xs[i], ys[i]) {
                        return Err("zmm mul mismatch".into());
                    }
                }
                let mut w = Wide4::zero();
                w.mac(ld_z(xs.as_ptr()), ld_z(ys.as_ptr()));
                let mut s = F128::ZERO;
                for i in 0..4 {
                    s += mul_portable(xs[i], ys[i]);
                }
                if w.reduce_sum() != s {
                    return Err("Wide4 mismatch".into());
                }
            }
        }
    }
    Ok(())
}
