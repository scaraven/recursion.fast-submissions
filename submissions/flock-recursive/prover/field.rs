//! The fields of B-4, scalar layer (the vector kernels are in `simd.rs`):
//!
//! * `B64`: BF64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1) (CompPoly's `BF64`), bit `i` ↔ `x^i`;
//! * `F` = BF64[y]/(y² + y + β) (`params::BETA`, a placeholder until S-A), limbs `(c₀, c₁)`;
//! * `K` = F[u]/(u² + u + α) (`params::ALPHA`, likewise), limbs `(f₀, f₁)` of `f₀ + f₁u`.
//!
//! An F product is three BF64 carry-less products (Karatsuba), `c₁ = (a₀+a₁)(b₀+b₁) + a₀b₀`,
//! `c₀ = a₀b₀ + β·a₁b₁`; a K product is three F products. The carry-less product is
//! `pclmulqdq` when the CPU has it (decided once, `init`), else a 4-bit-window shift-and-add
//! (tier 2, this VM). `FLOCK_NO_CLMUL=1` forces the portable path.

use std::ops::{Add, AddAssign, Mul, MulAssign};
use std::sync::atomic::{AtomicU8, Ordering};

static MODE: AtomicU8 = AtomicU8::new(0); // 0 undecided, 1 portable, 2 pclmul

pub fn hw_pclmul() -> bool {
    std::arch::is_x86_feature_detected!("pclmulqdq") && std::arch::is_x86_feature_detected!("sse4.1")
}

#[cold]
fn init_mode() -> bool {
    let hw = hw_pclmul() && std::env::var_os("FLOCK_NO_CLMUL").map_or(true, |v| v == "0");
    MODE.store(if hw { 2 } else { 1 }, Ordering::Relaxed);
    hw
}

#[inline(always)]
pub fn pclmul_on() -> bool {
    match MODE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => init_mode(),
    }
}

/// Tests: force the portable (`false`) or hardware (`true`, if present) product.
pub fn set_pclmul(hw: bool) {
    MODE.store(if hw && hw_pclmul() { 2 } else { 1 }, Ordering::Relaxed);
}

/// The 4-bit-window carry-less product (portable).
#[inline(always)]
pub fn clmul_soft(a: u64, b: u64) -> u128 {
    let a = a as u128;
    let mut t = [0u128; 16];
    t[1] = a;
    t[2] = a << 1;
    t[3] = t[2] ^ a;
    t[4] = a << 2;
    t[5] = t[4] ^ a;
    t[6] = t[4] ^ t[2];
    t[7] = t[6] ^ a;
    t[8] = a << 3;
    t[9] = t[8] ^ a;
    t[10] = t[8] ^ t[2];
    t[11] = t[10] ^ a;
    t[12] = t[8] ^ t[4];
    t[13] = t[12] ^ a;
    t[14] = t[12] ^ t[2];
    t[15] = t[14] ^ a;
    let mut r: u128 = 0;
    let mut i = 60i32;
    while i >= 0 {
        r = (r << 4) ^ t[((b >> i) & 15) as usize];
        i -= 4;
    }
    r
}

pub mod hw {
    use std::arch::x86_64::*;
    #[inline]
    #[target_feature(enable = "pclmulqdq,sse4.1")]
    pub unsafe fn clmul(a: u64, b: u64) -> u128 {
        let r = _mm_clmulepi64_si128(_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64), 0x00);
        let lo = _mm_cvtsi128_si64(r) as u64;
        let hi = _mm_extract_epi64::<1>(r) as u64;
        ((hi as u128) << 64) | lo as u128
    }
    /// An F product with `pclmulqdq` (same formula as `F::mul_soft`).
    #[target_feature(enable = "pclmulqdq,sse4.1")]
    pub unsafe fn mul_f(a0: u64, a1: u64, b0: u64, b1: u64) -> (u64, u64) {
        let p0 = clmul(a0, b0);
        let p1 = clmul(a1, b1);
        let pm = clmul(a0 ^ a1, b0 ^ b1);
        super::combine_f(p0, p1, pm)
    }
    #[target_feature(enable = "pclmulqdq,sse4.1")]
    pub unsafe fn mul_b(a: u64, b: u64) -> u64 {
        super::red(clmul(a, b))
    }
}

#[inline(always)]
pub fn clmul(a: u64, b: u64) -> u128 {
    if pclmul_on() {
        unsafe { hw::clmul(a, b) }
    } else {
        clmul_soft(a, b)
    }
}

/// `x mod (x^64 + x^4 + x^3 + x + 1)` for a 128-bit `x`.
#[inline(always)]
pub fn red(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    // hi·x^64 = hi·(x^4 + x^3 + x + 1); the bits shifted past x^63 (ov, degree ≤ 3) are folded by
    // the same shifts of `hi ^ ov` (ov's own shifts stay below x^8): review S-A-M1 fixed a double fold
    let ov = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    let h = hi ^ ov;
    lo ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4)
}

/// `(c₀, c₁)` from the unreduced `a₀b₀`, `a₁b₁`, `(a₀+a₁)(b₀+b₁)`: `c₁ = pm + p0`,
/// `c₀ = p0 + β·red(p1)`. Linear in `(p0, p1, pm)`, so sums of unreduced products reduce once.
#[inline(always)]
pub fn combine_f(p0: u128, p1: u128, pm: u128) -> (u64, u64) {
    let r1 = red(p1);
    (red(p0 ^ clmul(r1, crate::params::BETA)), red(pm ^ p0))
}

// ---------------------------------------------------------------- BF64

#[derive(Clone, Copy, Default, PartialEq, Eq, Debug, Hash)]
pub struct B64(pub u64);

impl B64 {
    pub const ZERO: B64 = B64(0);
    pub const ONE: B64 = B64(1);
    #[inline(always)]
    pub fn mul(self, o: B64) -> B64 {
        B64(red(clmul(self.0, o.0)))
    }
    pub fn sq(self) -> B64 {
        self.mul(self)
    }
    pub fn pow(self, mut e: u128) -> B64 {
        let (mut r, mut b) = (B64::ONE, self);
        while e > 0 {
            if e & 1 == 1 {
                r = r.mul(b);
            }
            b = b.sq();
            e >>= 1;
        }
        r
    }
    /// `a^(2^64 − 2)` by square-and-multiply (127 products; the reference of `inv`).
    pub fn inv_ref(self) -> B64 {
        self.pow(u64::MAX as u128 - 1)
    }
    /// `self^(2^k)`.
    #[inline(always)]
    fn sqn(self, k: usize) -> B64 {
        let mut x = self;
        for _ in 0..k {
            x = x.sq();
        }
        x
    }
    /// `a^(2^64 − 2)` by an addition chain (pass 13, Itoh–Tsujii: `t_k = a^(2^k − 1)`,
    /// `t_{i+j} = t_i^(2^j)·t_j`; 63 squarings and 8 products, was 127 products).
    pub fn inv(self) -> B64 {
        let t1 = self;
        let t2 = t1.sq().mul(t1);
        let t3 = t2.sq().mul(t1);
        let t6 = t3.sqn(3).mul(t3);
        let t12 = t6.sqn(6).mul(t6);
        let t15 = t12.sqn(3).mul(t3);
        let t30 = t15.sqn(15).mul(t15);
        let t60 = t30.sqn(30).mul(t30);
        let t63 = t60.sqn(3).mul(t3);
        t63.sq()
    }
    /// Absolute trace to GF(2).
    pub fn trace(self) -> u64 {
        let (mut s, mut x) = (0u64, self);
        for _ in 0..64 {
            s ^= x.0;
            x = x.sq();
        }
        s
    }
}

// ---------------------------------------------------------------- F

#[derive(Clone, Copy, Default, PartialEq, Eq, Debug, Hash)]
#[repr(C, align(16))]
pub struct F {
    pub lo: u64,
    pub hi: u64,
}

impl F {
    pub const ZERO: F = F { lo: 0, hi: 0 };
    pub const ONE: F = F { lo: 1, hi: 0 };
    /// `y`.
    pub const Y: F = F { lo: 0, hi: 1 };
    #[inline(always)]
    pub const fn new(lo: u64, hi: u64) -> F {
        F { lo, hi }
    }
    #[inline(always)]
    pub const fn b(x: B64) -> F {
        F { lo: x.0, hi: 0 }
    }
    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.lo == 0 && self.hi == 0
    }
    pub fn mul_soft(self, o: F) -> F {
        let p0 = clmul_soft(self.lo, o.lo);
        let p1 = clmul_soft(self.hi, o.hi);
        let pm = clmul_soft(self.lo ^ self.hi, o.lo ^ o.hi);
        let (c0, c1) = combine_f(p0, p1, pm);
        F { lo: c0, hi: c1 }
    }
    #[inline(always)]
    pub fn mulb(self, t: B64) -> F {
        F { lo: red(clmul(self.lo, t.0)), hi: red(clmul(self.hi, t.0)) }
    }
    pub fn sq(self) -> F {
        self * self
    }
    pub fn pow(self, mut e: u128) -> F {
        let (mut r, mut b) = (F::ONE, self);
        while e > 0 {
            if e & 1 == 1 {
                r = r * b;
            }
            b = b.sq();
            e >>= 1;
        }
        r
    }
    /// The inverse by the norm to BF64: `(a₀ + a₁y)⁻¹ = ((a₀+a₁) + a₁y) / (a₀² + a₀a₁ + βa₁²)`.
    pub fn inv(self) -> F {
        let (a0, a1) = (B64(self.lo), B64(self.hi));
        let n = B64(a0.sq().0 ^ a0.mul(a1).0 ^ a1.sq().mul(beta()).0);
        let ni = n.inv();
        F { lo: B64(a0.0 ^ a1.0).mul(ni).0, hi: a1.mul(ni).0 }
    }
    pub fn to_bytes(self) -> [u8; 16] {
        let mut b = [0u8; 16];
        b[..8].copy_from_slice(&self.lo.to_le_bytes());
        b[8..].copy_from_slice(&self.hi.to_le_bytes());
        b
    }
    pub fn from_bytes(b: &[u8]) -> F {
        F { lo: u64::from_le_bytes(b[..8].try_into().unwrap()), hi: u64::from_le_bytes(b[8..16].try_into().unwrap()) }
    }
    /// Bit `u` of the 128-bit F₂-coordinate vector (the packing basis `b_u`).
    #[inline(always)]
    pub fn bit(self, u: usize) -> bool {
        if u < 64 {
            (self.lo >> u) & 1 == 1
        } else {
            (self.hi >> (u - 64)) & 1 == 1
        }
    }
    /// `self · α` (`params::ALPHA`).
    #[inline(always)]
    pub fn mul_alpha(self) -> F {
        self * alpha()
    }
}

#[inline(always)]
pub fn beta() -> B64 {
    B64(crate::params::BETA)
}
#[inline(always)]
pub fn alpha() -> F {
    F { lo: crate::params::ALPHA.0, hi: crate::params::ALPHA.1 }
}

impl Add for F {
    type Output = F;
    #[inline(always)]
    fn add(self, o: F) -> F {
        F { lo: self.lo ^ o.lo, hi: self.hi ^ o.hi }
    }
}
impl AddAssign for F {
    #[inline(always)]
    fn add_assign(&mut self, o: F) {
        self.lo ^= o.lo;
        self.hi ^= o.hi;
    }
}
impl Mul for F {
    type Output = F;
    #[inline(always)]
    fn mul(self, o: F) -> F {
        if pclmul_on() {
            let (c0, c1) = unsafe { hw::mul_f(self.lo, self.hi, o.lo, o.hi) };
            F { lo: c0, hi: c1 }
        } else {
            self.mul_soft(o)
        }
    }
}
impl MulAssign for F {
    #[inline(always)]
    fn mul_assign(&mut self, o: F) {
        *self = *self * o;
    }
}

/// An unreduced F accumulator: sums of `a₀b₀`, `a₁b₁`, `(a₀+a₁)(b₀+b₁)` (`combine_f` is linear).
#[derive(Clone, Copy, Default)]
pub struct FAcc {
    pub p0: u128,
    pub p1: u128,
    pub pm: u128,
}
impl FAcc {
    #[inline(always)]
    pub fn mac(&mut self, a: F, b: F) {
        self.p0 ^= clmul(a.lo, b.lo);
        self.p1 ^= clmul(a.hi, b.hi);
        self.pm ^= clmul(a.lo ^ a.hi, b.lo ^ b.hi);
    }
    #[inline(always)]
    pub fn add(&mut self, o: &FAcc) {
        self.p0 ^= o.p0;
        self.p1 ^= o.p1;
        self.pm ^= o.pm;
    }
    #[inline(always)]
    pub fn reduce(&self) -> F {
        let (c0, c1) = combine_f(self.p0, self.p1, self.pm);
        F { lo: c0, hi: c1 }
    }
}

// ---------------------------------------------------------------- K

#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
#[repr(C, align(32))]
pub struct K {
    pub a: F,
    pub b: F,
}

impl K {
    pub const ZERO: K = K { a: F::ZERO, b: F::ZERO };
    pub const ONE: K = K { a: F::ONE, b: F::ZERO };
    /// `u`.
    pub const U: K = K { a: F::ZERO, b: F::ONE };
    #[inline(always)]
    pub const fn f(x: F) -> K {
        K { a: x, b: F::ZERO }
    }
    #[inline(always)]
    pub fn mulf(self, x: F) -> K {
        K { a: self.a * x, b: self.b * x }
    }
    #[inline(always)]
    pub fn mulb(self, t: B64) -> K {
        K { a: self.a.mulb(t), b: self.b.mulb(t) }
    }
    pub fn sq(self) -> K {
        self * self
    }
    /// `(A₀ + A₁u)⁻¹ = ((A₀+A₁) + A₁u) / (A₀² + A₀A₁ + αA₁²)`.
    pub fn inv(self) -> K {
        let n = self.a.sq() + self.a * self.b + self.b.sq().mul_alpha();
        let ni = n.inv();
        K { a: (self.a + self.b) * ni, b: self.b * ni }
    }
    pub fn to_bytes(self) -> [u8; 32] {
        let mut o = [0u8; 32];
        o[..16].copy_from_slice(&self.a.to_bytes());
        o[16..].copy_from_slice(&self.b.to_bytes());
        o
    }
    pub fn from_bytes(b: &[u8]) -> K {
        K { a: F::from_bytes(&b[..16]), b: F::from_bytes(&b[16..32]) }
    }
}
impl Add for K {
    type Output = K;
    #[inline(always)]
    fn add(self, o: K) -> K {
        K { a: self.a + o.a, b: self.b + o.b }
    }
}
impl AddAssign for K {
    #[inline(always)]
    fn add_assign(&mut self, o: K) {
        self.a += o.a;
        self.b += o.b;
    }
}
impl Mul for K {
    type Output = K;
    #[inline(always)]
    fn mul(self, o: K) -> K {
        let p0 = self.a * o.a;
        let p1 = self.b * o.b;
        let pm = (self.a + self.b) * (o.a + o.b);
        K { a: p0 + p1.mul_alpha(), b: pm + p0 }
    }
}
impl MulAssign for K {
    #[inline(always)]
    fn mul_assign(&mut self, o: K) {
        *self = *self * o;
    }
}

/// An unreduced K × F accumulator (two F accumulators).
#[derive(Clone, Copy, Default)]
pub struct KAcc {
    pub a: FAcc,
    pub b: FAcc,
}
impl KAcc {
    #[inline(always)]
    pub fn mac_f(&mut self, k: K, x: F) {
        self.a.mac(k.a, x);
        self.b.mac(k.b, x);
    }
    #[inline(always)]
    pub fn add(&mut self, o: &KAcc) {
        self.a.add(&o.a);
        self.b.add(&o.b);
    }
    pub fn reduce(&self) -> K {
        K { a: self.a.reduce(), b: self.b.reduce() }
    }
}

// ---------------------------------------------------------------- GF(2^8) and its embedding

/// Appendix A.1: `ζ := x^((2^64 − 1)/255)` (order 255 in BF64), the GF(2^8) basis `gᵢ = ζ^i`.
pub fn zeta() -> B64 {
    B64(2).pow((u64::MAX / 255) as u128)
}

/// The minimal polynomial of `ζ` over GF(2), `X^8 + …` as a 9-bit word: GF(2^8) is represented as
/// GF(2)[a]/(this polynomial), a byte `v` ↦ `φ₈(v) = Σ vᵢ ζ^i`.
pub fn gf8_poly() -> u16 {
    static P: std::sync::OnceLock<u16> = std::sync::OnceLock::new();
    *P.get_or_init(|| {
        let z = zeta();
        // Π_{i<8} (X + ζ^(2^i)), coefficients in BF64 (they come out in {0, 1})
        let mut c = vec![B64::ONE];
        let mut r = z;
        for _ in 0..8 {
            let mut n = vec![B64::ZERO; c.len() + 1];
            for (k, ck) in c.iter().enumerate() {
                n[k + 1] = B64(n[k + 1].0 ^ ck.0);
                n[k] = B64(n[k].0 ^ ck.mul(r).0);
            }
            c = n;
            r = r.sq();
        }
        let mut p = 0u16;
        for (k, ck) in c.iter().enumerate() {
            assert!(ck.0 <= 1, "minimal polynomial not over GF(2)");
            p |= (ck.0 as u16) << k;
        }
        p
    })
}

/// A product in GF(2^8) = GF(2)[a]/(`gf8_poly`).
pub fn gf8_mul(a: u8, b: u8) -> u8 {
    let poly = gf8_poly() as u32;
    let mut r: u32 = 0;
    for i in 0..8 {
        if (b >> i) & 1 == 1 {
            r ^= (a as u32) << i;
        }
    }
    for i in (8..15).rev() {
        if (r >> i) & 1 == 1 {
            r ^= poly << (i - 8);
        }
    }
    r as u8
}
pub fn gf8_inv(a: u8) -> u8 {
    let mut r = 1u8;
    for _ in 0..254 {
        r = gf8_mul(r, a);
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    fn rnd(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }
    /// The kernel-checked products of `FRFieldControls.katF` / `katK` (`probe/fr-field/kat.out`,
    /// an independent schoolbook reference), on the portable and the `pclmulqdq` path.
    #[test]
    fn kat_products() {
        let fk: [[u64; 6]; 8] = [
            [0x0CC65817272B53A4, 0x2120FC8CCEE55FE9, 0x99363C9930CF43AC, 0x6889C91E3005A706, 0x6BDB7CDE7A2DD504, 0x24D581B7235CF4BE],
            [0x3A31AADC19E3ECBF, 0x071674EE0693E0D9, 0x6BE1E08A7E114E68, 0x8DE424016B820FE4, 0x244BC9B01462D3E5, 0xF3026AA4979DAC65],
            [0x0A727244D2A65227, 0x141337ACF1E2B441, 0x6EDE80A3BA89E31D, 0xC6C4EE2E3B9EFAD5, 0x43BFB2E669825116, 0x8467CA181C3F98D6],
            [0xBE6FA6127EA696C3, 0xE25C7C4AE65CB5DB, 0x3500F48AB489CB10, 0x62734460417AE7FB, 0x196AF3312759DBBB, 0x1F8A3C54929ACFFC],
            [0x2C442A3AD00F1436, 0x7C3C2F9F335B53E5, 0x53976270C78E175D, 0x213B6DA5685F71AE, 0x7221CD99AFCD97CD, 0x57FB40AF14D4B13F],
            [0x5E4C955942756822, 0xF428D119E3DFF133, 0x1674844A519AABEC, 0xD64A860802F38533, 0x2985AE2715D2C9A3, 0x4D1D9F8365A7AD5E],
            [0x1E0E94DACDCA2A59, 0x36F2F503A871DFF9, 0xF18D6C4DEB6AF134, 0xEB03A85E443884FC, 0x16F1BD1FF2CFF07F, 0x664115F41524AF2A],
            [0x9063204D4E6752C1, 0x8A97BB29A59B03D7, 0x3056DFADA05552BE, 0x1562FBD6451163B3, 0x7629E63DF7DC3402, 0x4DF4929E6F052775]
        ];
        let kk: [[u64; 12]; 8] = [
            [0x2641940B4DF62868, 0xC0450C5C86166DEC, 0x5298E4BB63FE5590, 0x5DB1608995CCB6A0, 0x95E30255B5D45D27, 0x18B2BF46EE11E992, 0x91782A4F625E5555, 0xB49F8D70989DA94A, 0xA7076D7E76A71A45, 0xB6C9CAE676ACD4CA, 0x423E1CBA3D46D2A5, 0xFBB4F8964518C30E],
            [0xA52DD713B80A40B6, 0xFD252688627FD848, 0xC02AEDEBA2F6AA9E, 0xC83E8BAF538499D9, 0x5A875486E99ED6AE, 0xA087CC556F4BE6E8, 0x9AA80F8A49B4FA90, 0x24ADBA25E931A56F, 0x0D4F356658BF4069, 0xEBE1DC9188041AEF, 0xD462760B899E75C3, 0x3782A5182D0B1F9E],
            [0x3E60CA3809906D54, 0xE02071366047B633, 0x83FF7FE3E1F0859D, 0x564B1DD7CDEE32A2, 0xCBD2D4944CA05421, 0x9CB9557B327BD25B, 0x0F276F7FD5562BFA, 0xA24590AB86A403FD, 0xD6584FDCF9CF8D2B, 0xC5CDAAD8E827E37C, 0x5A5FCDDDE69A286E, 0x7BB481D0F11023C3],
            [0x9E6C6D9E859C2FBA, 0x3892543B0FDF7BC0, 0x792677BC063764FD, 0x219B5D8FF50BB9C4, 0x8B1E1BC8CD7CBF52, 0x20B98C04B7D04B52, 0x4C673AB53E2154AD, 0x3060D10A946FE4FF, 0xB753BA9F6745AF6E, 0xB70CEF74E349BC6D, 0x03021F07A81C9C81, 0x263CE689B68A5810],
            [0xF23A8FFAF0634524, 0x9377D946442173B3, 0x3985F9E7AC6C785B, 0xAFA98C2177F38F49, 0xA27D336DC4FC4FEA, 0x15A7DB7DF35032D8, 0x9874971FDCA0574D, 0x523798B489BE8404, 0x26A4964AFA48C3A9, 0xDF4AA5043F8618CF, 0x5EDF2AF0FA806412, 0xC7A9F0EE4BC23EFD],
            [0x88784399D488568F, 0x620149105780C65F, 0x67611E61FEDB3279, 0xFB6C68D5B547B182, 0xB03C81BC6773B421, 0xA704BAAD5793637E, 0x6681D9241DD87B27, 0x483F418A59675F13, 0x843DAFAD26A2C2C6, 0x01F5A9063C3BB2A2, 0x1807167468C6DA9D, 0xBE8B0756A2F8AC1B],
            [0xDEED24C57DCFA85A, 0x87EC348182DAD535, 0x85F6E63FE2CDE537, 0xFE38D6C201850D6B, 0x1DCB523513030A49, 0x3921ECA7874FE119, 0x779F589D84032702, 0x794EA4975B9652EF, 0x968603B5DE3EA199, 0xB9A22F9718C9AE37, 0xD473BFF6D9F0CA37, 0xA7AA1B7000878A69],
            [0x9471CDED08D7C8C0, 0x4B1D7C1F2A8446A5, 0xAE554A5B0F1521D0, 0x5668546DC1BC8189, 0x385F308022E74768, 0x813555B112B0FE9C, 0x3B65F1FC3D281B70, 0x930DC8303513FD75, 0x9330CE0A8B54D9EF, 0xFA3D2271A9DA8AB8, 0x6FFED1B3C16E1E86, 0x963A0BAC2915A224]
        ];
        for hw in [false, true] {
            set_pclmul(hw);
            for t in fk {
                assert_eq!(F::new(t[0], t[1]) * F::new(t[2], t[3]), F::new(t[4], t[5]));
                assert_eq!(F::new(t[0], t[1]).mul_soft(F::new(t[2], t[3])), F::new(t[4], t[5]));
            }
            let k = |t: &[u64]| K { a: F::new(t[0], t[1]), b: F::new(t[2], t[3]) };
            for t in kk {
                assert_eq!(k(&t[0..4]) * k(&t[4..8]), k(&t[8..12]));
            }
        }
        set_pclmul(true);
    }

    #[test]
    fn field_laws() {
        let mut s = 0x1234_5678_9abc_def1u64;
        assert_eq!(beta().trace(), 1);
        for _ in 0..300 {
            let a = F::new(rnd(&mut s), rnd(&mut s));
            let b = F::new(rnd(&mut s), rnd(&mut s));
            let c = F::new(rnd(&mut s), rnd(&mut s));
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a * b, b * a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F::ONE);
            }
            let mut acc = FAcc::default();
            acc.mac(a, b);
            acc.mac(b, c);
            assert_eq!(acc.reduce(), a * b + b * c);
            assert_eq!(a.mul_alpha(), a * alpha());
            let t = B64(rnd(&mut s));
            assert_eq!(a.mulb(t), a * F::b(t));
            let ka = K { a, b };
            let kb = K { a: c, b: a + b };
            let kc = K { a: b, b: c };
            assert_eq!((ka * kb) * kc, ka * (kb * kc));
            assert_eq!(ka * (kb + kc), ka * kb + ka * kc);
            assert_eq!(ka * ka.inv(), K::ONE);
        }
        // y² + y + β = 0, u² + u + α = 0
        assert_eq!(F::Y * F::Y + F::Y + F::b(beta()), F::ZERO);
        assert_eq!(K::U * K::U + K::U + K::f(alpha()), K::ZERO);
        // Tr_F(α) = Tr_BF64(α₁) = 1: u² + u + α is irreducible
        assert_eq!(B64(alpha().hi).trace(), 1);
        // the field has 2^128 elements: a^(2^128) = a
        let a = F::new(0x1234, 0x5678_9abc);
        let mut x = a;
        for _ in 0..128 {
            x = x.sq();
        }
        assert_eq!(x, a);
        let mut x = a;
        for _ in 0..64 {
            x = x.sq();
        }
        assert_ne!(x, a); // not in BF64
    }
    #[test]
    fn soft_matches_hw() {
        if !hw_pclmul() {
            return;
        }
        let mut s = 99u64;
        for _ in 0..1000 {
            let (a, b) = (rnd(&mut s), rnd(&mut s));
            assert_eq!(clmul_soft(a, b), unsafe { hw::clmul(a, b) });
        }
    }
    #[test]
    fn gf8_embedding() {
        let w = zeta();
        assert_eq!(w.pow(255), B64::ONE);
        for d in [3u128, 5, 17] {
            assert_ne!(w.pow(255 / d), B64::ONE);
        }
        let phi = |v: u8| -> B64 {
            let mut r = B64::ZERO;
            let mut p = B64::ONE;
            for i in 0..8 {
                if (v >> i) & 1 == 1 {
                    r = B64(r.0 ^ p.0);
                }
                p = p.mul(w);
            }
            r
        };
        for a in [3u8, 7, 0x53, 0xCA, 0xFF] {
            for b in [1u8, 2, 0x11, 0x80, 0xFE] {
                assert_eq!(phi(gf8_mul(a, b)), phi(a).mul(phi(b)));
            }
        }
        assert_eq!(gf8_mul(0x53, gf8_inv(0x53)), 1);
    }
}

#[cfg(test)]
mod pass13_tests {
    use super::*;

    /// The addition-chain inverse equals square-and-multiply's (`inv_ref`) on 0, 1 and random
    /// elements, and `F::inv` built on it inverts.
    #[test]
    fn inv_chain_matches_ref() {
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let mut nx = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for x in [0u64, 1, 2, u64::MAX] {
            assert_eq!(B64(x).inv(), B64(x).inv_ref());
        }
        for _ in 0..20_000 {
            let x = B64(nx());
            assert_eq!(x.inv(), x.inv_ref());
            let f = F::new(nx(), nx());
            assert_eq!(f * f.inv(), F::ONE);
        }
    }
}
