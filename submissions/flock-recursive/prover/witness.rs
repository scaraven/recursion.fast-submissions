//! The leaf witness (blueprint §4.1): the chain `d₀ = s, d_{i+1} = chainStep dᵢ` (sequential), then
//! every block's bits `z` and rows `Az`, `Bz` (bit-sliced, 64 blocks per tape run, in parallel).
//! Layout: block-major, `2^14` bits per block, bit `i` of the witness is bit `i mod 64` of word
//! `i / 64`.

use crate::blake2s::{chain_step, Digest};
use crate::circuit::Circuit;
use crate::par;

pub struct Witness {
    pub m: usize,
    pub z: Vec<u64>,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    /// the chain end `d_n`
    pub h: Digest,
}

impl Witness {
    pub fn bytes(v: &[u64]) -> &[u8] {
        unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 8) }
    }
}

/// An uninitialised `Vec<u64>` of `n` words (every word is written before it is read).
pub fn alloc_u64(n: usize) -> Vec<u64> {
    let mut v = Vec::with_capacity(n);
    unsafe { v.set_len(n) };
    v
}

pub fn leaf_witness(c: &Circuit, s: &Digest, m: usize) -> Witness {
    let nb = 1usize << (m - 14);
    let mut ds = Vec::with_capacity(nb + 1);
    ds.push(*s);
    for i in 0..nb {
        let n = chain_step(&ds[i]);
        ds.push(n);
    }
    let words = nb * 256;
    let (mut z, mut a, mut b) = (alloc_u64(words), alloc_u64(words), alloc_u64(words));
    let (pz, pa, pb) = (par::SyncPtr(z.as_mut_ptr()), par::SyncPtr(a.as_mut_ptr()), par::SyncPtr(b.as_mut_ptr()));
    let groups = nb.div_ceil(64);
    par::run(groups, &|g| {
        let (pz, pa, pb) = (pz, pa, pb);
        let lo = 64 * g;
        let k = 64.min(nb - lo);
        let mut vals = Vec::new();
        unsafe {
            let zw = std::slice::from_raw_parts_mut(pz.0.add(256 * lo), 256 * k);
            let aw = std::slice::from_raw_parts_mut(pa.0.add(256 * lo), 256 * k);
            let bw = std::slice::from_raw_parts_mut(pb.0.add(256 * lo), 256 * k);
            c.trace64(&ds[lo..lo + k], &mut vals, zw, aw, bw);
        }
    });
    Witness { m, z, a, b, h: ds[nb] }
}

// ---------------------------------------------------------------- word-level witness

/// The fixed part of a block's `(z, a, b)` words: constant rows and the one position.
pub struct Template {
    pub z: [u64; 256],
    pub a: [u64; 256],
    pub b: [u64; 256],
}

impl Template {
    pub fn new(c: &Circuit) -> Template {
        // a block whose d is zero, with its d, output and gate positions cleared
        let mut vals = Vec::new();
        let (mut z, mut a, mut b) = c.trace(&[0u8; 32], &mut vals);
        let clear = |w: &mut [u64; 256], lo: usize, hi: usize| {
            for p in lo..hi {
                w[p / 64] &= !(1u64 << (p % 64));
            }
        };
        for w in [&mut z, &mut a, &mut b] {
            clear(w, crate::params::OUT_BASE, crate::params::OUT_BASE + 256);
            clear(w, crate::params::D_BASE, crate::params::D_BASE + 256);
            clear(w, crate::params::GATE_BASE, crate::params::GATE_BASE + crate::params::GATES);
        }
        Template { z, a, b }
    }
}

#[inline(always)]
fn put(w: &mut [u64; 256], pos: usize, bits: u64, n: usize) {
    let (i, o) = (pos / 64, pos % 64);
    let v = bits & ((1u64 << n) - 1);
    w[i] |= v << o;
    if o + n > 64 {
        w[i + 1] |= v >> (64 - o);
    }
}

struct Emit<'a> {
    z: &'a mut [u64; 256],
    a: &'a mut [u64; 256],
    b: &'a mut [u64; 256],
    pos: usize,
}

impl Emit<'_> {
    /// `n` gates with A-sides `ga`, B-sides `gb` (bits `lo … lo + n` of the words).
    #[inline(always)]
    fn gates(&mut self, ga: u32, gb: u32, lo: u32, n: usize) {
        let (x, y) = ((ga >> lo) as u64, (gb >> lo) as u64);
        put(self.a, self.pos, x, n);
        put(self.b, self.pos, y, n);
        put(self.z, self.pos, x & y, n);
        self.pos += n;
    }
    /// `addW`: 31 carry gates.
    #[inline(always)]
    fn add(&mut self, x: u32, y: u32) -> u32 {
        let s = x.wrapping_add(y);
        let c = s ^ x ^ y;
        self.gates(x ^ c, y ^ c, 0, 31);
        s
    }
    /// `add3W`: 31 majority gates, then 30 ripple gates.
    #[inline(always)]
    fn add3(&mut self, x: u32, y: u32, z: u32) -> u32 {
        self.gates(x ^ z, y ^ z, 0, 31);
        let ms = ((x ^ z) & (y ^ z)) ^ z;
        let p = x ^ y ^ z;
        let q = ms << 1;
        let s = p.wrapping_add(q);
        let c = s ^ p ^ q;
        self.gates(p ^ c, q ^ c, 1, 30);
        s
    }
}

/// One chain block's `(z, a, b)` from its input digest, by word arithmetic in the circuit's gate
/// order (`Circuit::trace` is the reference; `witness::tests`). Returns the output digest.
pub fn block_fast(t: &Template, d: &Digest, z: &mut [u64; 256], a: &mut [u64; 256], b: &mut [u64; 256]) -> Digest {
    use crate::blake2s::{h0, IV, SIGMA};
    z.copy_from_slice(&t.z);
    a.copy_from_slice(&t.a);
    b.copy_from_slice(&t.b);
    let mut msg = [0u8; 64];
    msg[0] = 0x43;
    msg[1..33].copy_from_slice(d);
    let m: [u32; 16] = std::array::from_fn(|w| u32::from_le_bytes(msg[4 * w..4 * w + 4].try_into().unwrap()));
    let h = h0();
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(&h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= 33;
    v[14] ^= 0xFFFF_FFFF;
    let mut e = Emit { z, a, b, pos: crate::params::GATE_BASE };
    let gf = |e: &mut Emit, v: &mut [u32; 16], ia: usize, ib: usize, ic: usize, id: usize, x: u32, y: u32| {
        let a1 = e.add3(v[ia], v[ib], x);
        let d1 = (v[id] ^ a1).rotate_right(16);
        let c1 = e.add(v[ic], d1);
        let b1 = (v[ib] ^ c1).rotate_right(12);
        let a2 = e.add3(a1, b1, y);
        let d2 = (d1 ^ a2).rotate_right(8);
        let c2 = e.add(c1, d2);
        let b2 = (b1 ^ c2).rotate_right(7);
        v[ia] = a2;
        v[ib] = b2;
        v[ic] = c2;
        v[id] = d2;
    };
    for s in SIGMA.iter() {
        gf(&mut e, &mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        gf(&mut e, &mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        gf(&mut e, &mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        gf(&mut e, &mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        gf(&mut e, &mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        gf(&mut e, &mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        gf(&mut e, &mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        gf(&mut e, &mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    debug_assert_eq!(e.pos, crate::params::GATE_BASE + crate::params::GATES);
    let mut out = [0u8; 32];
    for w in 0..8 {
        let o = v[w] ^ v[w + 8] ^ h[w];
        out[4 * w..4 * w + 4].copy_from_slice(&o.to_le_bytes());
        // output rows (out, one) and input rows (d, one)
        put(e.z, crate::params::OUT_BASE + 32 * w, o as u64, 32);
        put(e.a, crate::params::OUT_BASE + 32 * w, o as u64, 32);
        put(e.b, crate::params::OUT_BASE + 32 * w, 0xFFFF_FFFF, 32);
    }
    for k in 0..4 {
        let x = u64::from_le_bytes(d[8 * k..8 * k + 8].try_into().unwrap());
        let p = crate::params::D_BASE + 64 * k;
        put(e.z, p, x, 64.min(63)); // 63 bits, then the top bit
        put(e.z, p + 63, x >> 63, 1);
        put(e.a, p, x, 63);
        put(e.a, p + 63, x >> 63, 1);
        put(e.b, p, u64::MAX, 63);
        put(e.b, p + 63, 1, 1);
    }
    out
}

/// The leaf witness by `block_fast` (blocks in parallel after the sequential chain).
pub fn leaf_witness_fast(c: &Circuit, s: &Digest, m: usize) -> Witness {
    let nb = 1usize << (m - 14);
    let mut ds = Vec::with_capacity(nb + 1);
    ds.push(*s);
    for i in 0..nb {
        let n = chain_step(&ds[i]);
        ds.push(n);
    }
    let t = Template::new(c);
    let words = nb * 256;
    let (mut z, mut a, mut b) = (alloc_u64(words), alloc_u64(words), alloc_u64(words));
    let (pz, pa, pb) = (par::SyncPtr(z.as_mut_ptr()), par::SyncPtr(a.as_mut_ptr()), par::SyncPtr(b.as_mut_ptr()));
    par::run(nb.div_ceil(64), &|g| {
        let (pz, pa, pb) = (pz, pa, pb);
        for i in 64 * g..(64 * g + 64).min(nb) {
            unsafe {
                let zw = &mut *(pz.0.add(256 * i) as *mut [u64; 256]);
                let aw = &mut *(pa.0.add(256 * i) as *mut [u64; 256]);
                let bw = &mut *(pb.0.add(256 * i) as *mut [u64; 256]);
                block_fast(&t, &ds[i], zw, aw, bw);
            }
        }
    });
    Witness { m, z, a, b, h: ds[nb] }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fast_block_equals_the_tape() {
        let c = Circuit::build();
        let t = Template::new(&c);
        let mut vals = vec![];
        for seed in 0..5u8 {
            let d: Digest = std::array::from_fn(|i| (i as u8).wrapping_mul(91).wrapping_add(seed.wrapping_mul(37)) ^ 0xA5);
            let (z0, a0, b0) = c.trace(&d, &mut vals);
            let (mut z, mut a, mut b) = ([0u64; 256], [0u64; 256], [0u64; 256]);
            let out = block_fast(&t, &d, &mut z, &mut a, &mut b);
            assert_eq!(out, chain_step(&d));
            for w in 0..256 {
                assert_eq!(z[w], z0[w], "z word {w}");
                assert_eq!(a[w], a0[w], "a word {w}");
                assert_eq!(b[w], b0[w], "b word {w}");
            }
        }
    }
}
