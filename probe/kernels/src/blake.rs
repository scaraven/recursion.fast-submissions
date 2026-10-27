//! BLAKE2s compression and the per-compression witness of the BLAKE2s R1CS (item 5).
//!
//! The witness follows Flock's BLAKE3 "Option F" encoding carried to BLAKE2s (F-flock §3): the
//! only products are the carries of the 32-bit additions; a 3-operand add `x + y + m` is a
//! carry-save majority row `(x^m)(y^m)` plus a ripple add, a 2-operand add one ripple add whose
//! carries satisfy `c_{i+1} = (x_i^c_i)(y_i^c_i) ^ c_i`. Each product word is written to `z` and
//! its two linear operands to `a` and `b` (the prover needs a = A z and b = B z as bit vectors for
//! the zerocheck), 6 product words per G, 80 G per compression: 480 words = 15,360 bits of the
//! 2^14-bit block, plus h_in, m, h_out. XORs and rotations are not materialised.
use crate::{par_best, quick, report};
use std::hint::black_box;

pub const IV: [u32; 8] = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19];
pub const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

#[inline(always)]
fn g(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(12);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(8);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(7);
}

pub fn compress(h: &[u32; 8], m: &[u32; 16], t: u64, f0: u32) -> [u32; 8] {
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    v[14] ^= f0;
    for s in SIGMA.iter() {
        g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    let mut o = [0u32; 8];
    for i in 0..8 {
        o[i] = h[i] ^ v[i] ^ v[i + 8];
    }
    o
}

struct W<'a> {
    z: &'a mut [u32],
    a: &'a mut [u32],
    b: &'a mut [u32],
    i: usize,
}
impl W<'_> {
    #[inline(always)]
    fn push(&mut self, p: u32, x: u32, y: u32) {
        self.z[self.i] = p;
        self.a[self.i] = x;
        self.b[self.i] = y;
        self.i += 1;
    }
    #[inline(always)]
    fn add2(&mut self, x: u32, y: u32) -> u32 {
        let s = x.wrapping_add(y);
        let c = s ^ x ^ y; // carry into each bit
        let (ax, by) = (x ^ c, y ^ c);
        self.push(ax & by, ax, by);
        s
    }
    #[inline(always)]
    fn add3(&mut self, x: u32, y: u32, m: u32) -> u32 {
        let (ax, by) = (x ^ m, y ^ m);
        let p = ax & by;
        self.push(p, ax, by);
        let maj = p ^ m;
        self.add2(x ^ y ^ m, maj << 1)
    }
    #[inline(always)]
    fn g(&mut self, v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
        v[a] = self.add3(v[a], v[b], x);
        v[d] = (v[d] ^ v[a]).rotate_right(16);
        v[c] = self.add2(v[c], v[d]);
        v[b] = (v[b] ^ v[c]).rotate_right(12);
        v[a] = self.add3(v[a], v[b], y);
        v[d] = (v[d] ^ v[a]).rotate_right(8);
        v[c] = self.add2(v[c], v[d]);
        v[b] = (v[b] ^ v[c]).rotate_right(7);
    }
}

/// One compression with its witness block (512 words each of z, a, b).
pub fn compress_wit(h: &[u32; 8], m: &[u32; 16], t: u64, z: &mut [u32], a: &mut [u32], b: &mut [u32]) -> [u32; 8] {
    let mut w = W { z, a, b, i: 0 };
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    for s in SIGMA.iter() {
        w.g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        w.g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        w.g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        w.g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        w.g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        w.g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        w.g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        w.g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    let mut o = [0u32; 8];
    for i in 0..8 {
        o[i] = h[i] ^ v[i] ^ v[i + 8];
    }
    // I/O slots
    let base = w.i;
    w.z[base..base + 8].copy_from_slice(h);
    w.z[base + 8..base + 24].copy_from_slice(m);
    w.z[base + 24..base + 32].copy_from_slice(&o);
    o
}

pub fn selftest() -> Result<(), String> {
    // BLAKE2s-256("abc"): h0 = IV ^ 0x01010020, one block, t = 3, final
    let mut h = IV;
    h[0] ^= 0x0101_0020;
    let mut m = [0u32; 16];
    m[0] = 0x0063_6261;
    let o = compress(&h, &m, 3, 0xFFFF_FFFF);
    let want = [0x8C5E8C50u32, 0xE2147C32, 0xA32BA7E1, 0x2F45EB4E, 0x208B4537, 0x293AD69E, 0x4C9B994D, 0x82596786];
    if o != want {
        return Err(format!("BLAKE2s(abc) wrong: {o:08x?}"));
    }
    // the witness path computes the same compression (f0 = 0 here)
    let (mut z, mut a, mut b) = (vec![0u32; 512], vec![0u32; 512], vec![0u32; 512]);
    let o2 = compress_wit(&h, &m, 3, &mut z, &mut a, &mut b);
    if o2 != compress(&h, &m, 3, 0) {
        return Err("witness compression differs".into());
    }
    // every product word is the AND of its operands
    for i in 0..480 {
        if z[i] != a[i] & b[i] {
            return Err("product row != a & b".into());
        }
    }
    Ok(())
}

pub fn bench(threads: &[usize]) {
    let n = if quick() { 1 << 12 } else { 1 << 16 };
    for &th in threads {
        let secs = par_best(th, 3, |tid| {
            let mut h = IV;
            h[0] ^= tid as u32;
            let mut m = [0u32; 16];
            for i in 0..n {
                m[0] = i as u32;
                h = compress(&h, &m, 64, 0);
            }
            black_box(h);
        });
        report("blake2s-compress", "scalar", th, "chain", (th * n) as f64, secs, "compression");
        let nw = n / 4;
        // fresh buffers (allocation and first-touch page faults inside the timing)
        let secs = par_best(th, 3, |tid| {
            let (mut z, mut a, mut b) = (vec![0u32; 512 * nw], vec![0u32; 512 * nw], vec![0u32; 512 * nw]);
            let mut h = IV;
            h[0] ^= tid as u32;
            let mut m = [0u32; 16];
            for i in 0..nw {
                m[0] = i as u32;
                let s = 512 * i;
                h = compress_wit(&h, &m, 64, &mut z[s..s + 512], &mut a[s..s + 512], &mut b[s..s + 512]);
            }
            black_box((&z, &a, &b, h));
        });
        report("blake2s-witness(z,a,b) fresh buffers", "scalar", th, &format!("chain of {nw}"), (th * nw) as f64, secs, "compression");
        // warm (pre-faulted, reused) buffers
        let mut bufs: Vec<Vec<u32>> = (0..3 * th).map(|_| vec![1u32; 512 * nw]).collect();
        let ptrs: Vec<crate::SyncPtr<u32>> = bufs.iter_mut().map(|v| crate::SyncPtr(v.as_mut_ptr())).collect();
        let secs = par_best(th, 3, |tid| {
            let (z, a, b) = unsafe {
                (
                    std::slice::from_raw_parts_mut(ptrs[3 * tid].0, 512 * nw),
                    std::slice::from_raw_parts_mut(ptrs[3 * tid + 1].0, 512 * nw),
                    std::slice::from_raw_parts_mut(ptrs[3 * tid + 2].0, 512 * nw),
                )
            };
            let mut h = IV;
            h[0] ^= tid as u32;
            let mut m = [0u32; 16];
            for i in 0..nw {
                m[0] = i as u32;
                let s = 512 * i;
                h = compress_wit(&h, &m, 64, &mut z[s..s + 512], &mut a[s..s + 512], &mut b[s..s + 512]);
            }
            black_box(h);
        });
        black_box(&bufs);
        report("blake2s-witness(z,a,b) warm buffers", "scalar", th, &format!("chain of {nw}"), (th * nw) as f64, secs, "compression");
    }
}
