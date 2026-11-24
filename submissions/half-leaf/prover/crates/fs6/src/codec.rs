//! FORMAT6 §1: little-endian lanes; a `K` word is a `u64` (bit `z` = coefficient of `x^z`); an `E` scalar
//! `c₀ + c₁·y` is 16 bytes, `c₀` then `c₁`; a draw's value `χ(a)` is lanes 0–1 of the answer, its PoW lane is lane 2.

use crate::Digest;

/// An `E` scalar as its two `K` limbs `[c₀, c₁]`.
pub type E = [u64; 2];

pub fn le64(b: &[u8]) -> u64 {
    u64::from_le_bytes(b[..8].try_into().unwrap())
}

pub fn put_k(b: &mut Vec<u8>, w: u64) {
    b.extend_from_slice(&w.to_le_bytes());
}

pub fn put_e(b: &mut Vec<u8>, e: E) {
    put_k(b, e[0]);
    put_k(b, e[1]);
}

/// The 16 bytes of an `E` scalar back to `[c₀, c₁]`.
pub fn get_e(b: &[u8]) -> E {
    [le64(&b[0..8]), le64(&b[8..16])]
}

/// `χ(a) = (LE64(a[0..8]), LE64(a[8..16]))`.
pub fn chi(a: &Digest) -> E {
    get_e(&a[..16])
}

/// The PoW lane `LE64(a[16..24])`.
pub fn pow_lane(a: &Digest) -> u64 {
    le64(&a[16..24])
}

/// `G(g)` passes iff the PoW lane is `< 2^(64−g)` (its top `g` bits are zero), `1 ≤ g ≤ 23`.
pub fn pow_ok(a: &Digest, g: u32) -> bool {
    assert!((1..=23).contains(&g), "a group's grind is 1..=23 bits (FORMAT6 §4)");
    pow_lane(a) >> (64 - g) == 0
}

/// A digest as four `K` words (lanes 0–3).
pub fn digest_words(d: &Digest) -> [u64; 4] {
    std::array::from_fn(|i| le64(&d[8 * i..]))
}
