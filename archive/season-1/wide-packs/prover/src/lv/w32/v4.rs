//! lvm2 W32 G0: the K = 32 Skip and Product kernels on the v4 tier (AVX-512 BW/VBMI, VPCLMULQDQ, GFNI).
//!
//! Embedding ([`embed8`]): eight positions' 16 packs. A 3-level two-source byte-permute transpose makes the registers
//! byte-sliced (`R[2 b + h]` qword `k` byte `n` = byte `b` of pack `8 h + k` at position `n`), 4 x 7 affine byte maps
//! give the embedding's 7 bytes byte-sliced, and a second transpose makes one register a pack (qword `n` = its 53-bit
//! embedding at position `n`): 24 + 56 (+28 XOR) + 48 instructions per 128 pack values.
//!
//! Skip ([`Skip32`]): per row of 8 slices, per half and group, per mixed point and position `x`: `b c` (2 VPCLMULQDQ
//! for 8 positions), then the 105-bit product times the 128-bit weight by Karatsuba (6), so 4 lane-products per
//! position-point, against 3 at K = 16 over 38 points.
//!
//! Product ([`Product32`]): per lane byte, per pack: `ones (a + c) + b c` (4 VPCLMULQDQ for 8 positions), a byte
//! gather of its 16 coefficient bytes over the 8 positions (2 VPERMI2B), the bit transpose (2 affine), and the
//! columns stored packed (64 + 41 bytes a pack, 1680 a lane byte, 27 registers); phase 2 as the K = 16 kernel.

use core::arch::x86_64::*;

use super::{BITS, BLOCK_WORDS, EMB, ONES, PACKS, PAIRS, POINTS, SLOTS, row_positions};

#[repr(C, align(64))]
struct Idx([[u8; 64]; 8]);

/// `AFF[b][o]`: the affine byte map sending input byte `b` of a pack to its share of embedding byte `o` (output bit
/// `t` reads matrix byte `7 - t`).
static AFF: [[u64; 7]; 4] = {
    let mut m = [[0u64; 7]; 4];
    let mut b = 0;
    while b < 4 {
        let mut o = 0;
        while o < 7 {
            let mut a = 0u64;
            let mut t = 0;
            while t < 8 {
                let mut row = 0u64;
                let mut u = 0;
                while u < 8 {
                    row |= (EMB[8 * b + u] >> (8 * o + t) & 1) << u;
                    u += 1;
                }
                a |= row << (8 * (7 - t));
                t += 1;
            }
            m[b][o] = a;
            o += 1;
        }
        b += 1;
    }
    m
};

/// Product column gather: `COL[h]` byte `8 m + n` = byte `8 h + m` of position `n`'s product (even positions in the
/// first source's 128-bit lane `n / 2`, odd ones in the second's).
static COL: Idx = {
    let mut t = [[0u8; 64]; 8];
    let mut h = 0;
    while h < 2 {
        let mut m = 0;
        while m < 8 {
            let mut n = 0;
            while n < 8 {
                t[h][8 * m + n] = (((n % 2) << 6) | (16 * (n / 2) + 8 * h + m)) as u8;
                n += 1;
            }
            m += 1;
        }
        h += 1;
    }
    Idx(t)
};

const BIT_TRANSPOSE: i64 = 0x8040_2010_0804_0201_u64 as i64;

#[repr(C, align(64))]
struct Consts([__m512i; 2]);
// SAFETY: plain data.
unsafe impl Sync for Consts {}
/// `ones` and the bit-transpose source, broadcast to every qword.
static STAGE_CONSTS: Consts = Consts(unsafe { core::mem::transmute::<[u64; 16], [__m512i; 2]>([ONES, ONES, ONES, ONES, ONES, ONES, ONES, ONES, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64, BIT_TRANSPOSE as u64]) });

#[inline(always)]
unsafe fn ld(t: &[u8; 64]) -> __m512i {
    unsafe { _mm512_loadu_si512(t.as_ptr().cast()) }
}

/// `_mm512_unpack{lo,hi}_epi{8 size}` on byte labels: elements of `size` bytes, per 128-bit lane.
fn unpack_lbl(a: &[u16; 64], b: &[u16; 64], size: usize, hi: bool) -> [u16; 64] {
    let mut r = [0u16; 64];
    let half = 8 / size;
    for lane in 0..4 {
        for i in 0..half {
            let e = if hi { half + i } else { i };
            for t in 0..size {
                r[16 * lane + 2 * i * size + t] = a[16 * lane + e * size + t];
                r[16 * lane + (2 * i + 1) * size + t] = b[16 * lane + e * size + t];
            }
        }
    }
    r
}

/// The level-1 byte-permute tables of the transpose network [`net`]: level 1 `X[p][s] = vpermi2b(src[2p], T[s],
/// src[2p + 1])`, level 2 `unpack{lo,hi}_epi16` of `X[2 q][s], X[2 q + 1][s]`, level 3 `unpack{lo,hi}_epi32`, final
/// register `4 s + 2 lh2 + lh3`. `want(f, fb) = (e, sb)`: final register `f` byte `fb` is byte `sb` of source
/// `2 p + e`, `p` being the pair the unpacks deliver there (asserted to be `(fb % 8) / 2`).
fn net_tables(want: impl Fn(usize, usize) -> (usize, usize)) -> [[u8; 64]; 2] {
    let x: Vec<[u16; 64]> = (0..8).map(|ps| std::array::from_fn(|i| (64 * ps + i) as u16)).collect();
    let mut t = [[0xffu8; 64]; 2];
    for s in 0..2 {
        for lh2 in 0..2 {
            let y = |q2: usize| unpack_lbl(&x[2 * (2 * q2) + s], &x[2 * (2 * q2 + 1) + s], 2, lh2 == 1);
            let (y0, y1) = (y(0), y(1));
            for lh3 in 0..2 {
                let f = unpack_lbl(&y0, &y1, 4, lh3 == 1);
                let reg = 4 * s + 2 * lh2 + lh3;
                for fb in 0..64 {
                    let l = f[fb] as usize;
                    let (ps, i) = (l / 64, l % 64);
                    let (p, s1) = (ps / 2, ps % 2);
                    assert_eq!((s1, p), (s, (fb % 8) / 2), "the network's pair");
                    let (e, sb) = want(reg, fb);
                    let v = ((e << 6) | sb) as u8;
                    assert!(t[s][i] == 0xff || t[s][i] == v, "one table for every pair");
                    t[s][i] = v;
                }
            }
        }
    }
    t
}

#[repr(C, align(64))]
struct Nets([[u8; 64]; 4]);

/// Input network (final register `2 b + hh`, qword `k` = pack `8 hh + k`'s byte `b`, byte `n` = position `n`), then
/// output network (final register `k` = pack `8 hh + k`, qword `n` = position `n`, byte `o` = source `Y[o]`).
static NETS: std::sync::LazyLock<Nets> = std::sync::LazyLock::new(|| {
    let a = net_tables(|f, fb| {
        let (b, hh, k, n) = (f >> 1, f & 1, fb / 8, fb % 8);
        (n % 2, 4 * (8 * hh + k) + b)
    });
    let o = net_tables(|f, fb| {
        let (k, n, o) = (f, fb / 8, fb % 8);
        (o % 2, 8 * k + n)
    });
    Nets([a[0], a[1], o[0], o[1]])
});

#[inline(always)]
unsafe fn net(src: &[__m512i; 8], t: [__m512i; 2]) -> [__m512i; 8] {
    unsafe {
        let x: [[__m512i; 2]; 4] = std::array::from_fn(|p| std::array::from_fn(|s| _mm512_permutex2var_epi8(src[2 * p], t[s], src[2 * p + 1])));
        let mut out = [_mm512_setzero_si512(); 8];
        for s in 0..2 {
            for lh2 in 0..2 {
                let y = |q2: usize| {
                    let (a, b) = (x[2 * q2][s], x[2 * q2 + 1][s]);
                    if lh2 == 0 { _mm512_unpacklo_epi16(a, b) } else { _mm512_unpackhi_epi16(a, b) }
                };
                let (y0, y1) = (y(0), y(1));
                out[4 * s + 2 * lh2] = _mm512_unpacklo_epi32(y0, y1);
                out[4 * s + 2 * lh2 + 1] = _mm512_unpackhi_epi32(y0, y1);
            }
        }
        out
    }
}

/// The network tables in registers, for [`embed8`].
#[derive(Clone, Copy)]
pub struct EmbedTables([__m512i; 4]);

impl EmbedTables {
    pub fn new() -> Self {
        // SAFETY: AVX-512F at compile time; aligned 64-byte rows.
        Self(std::array::from_fn(|i| unsafe { ld(&NETS.0[i]) }))
    }
}

/// The 16 packs of the 8 positions at `src` (64 words), embedded: `out[q]` qword `n` = pack `q` at position `n`.
#[inline(always)]
pub unsafe fn embed8(t: &EmbedTables, src: *const u64, out: &mut [__m512i; PACKS]) {
    unsafe {
        let a: [__m512i; 8] = std::array::from_fn(|n| _mm512_loadu_si512(src.add(BLOCK_WORDS * n).cast()));
        let r = net(&a, [t.0[0], t.0[1]]);
        for hh in 0..2 {
            let mut y = [_mm512_setzero_si512(); 8];
            for o in 0..7 {
                let g = |b: usize| _mm512_gf2p8affine_epi64_epi8(r[2 * b + hh], _mm512_set1_epi64(AFF[b][o] as i64), 0);
                y[o] = _mm512_xor_si512(_mm512_ternarylogic_epi64::<0x96>(g(0), g(1), g(2)), g(3));
            }
            let e = net(&y, [t.0[2], t.0[3]]);
            out[8 * hh..8 * hh + 8].copy_from_slice(&e);
        }
    }
}

/// Position weights by word for vector loads: `w0` at `j`, `w1` at `BITS + j`, `w0 + w1` at `2 BITS + j`.
pub struct Weights32(pub Vec<u64>);

impl Weights32 {
    pub fn new(w: &[[u64; 2]]) -> Self {
        let mut v = vec![0u64; 3 * BITS + 8];
        for (j, w) in w.iter().enumerate().take(BITS) {
            v[j] = w[0];
            v[BITS + j] = w[1];
            v[2 * BITS + j] = w[0] ^ w[1];
        }
        Self(v)
    }
}

/// The K = 32 Skip pass's block kernel.
pub struct Skip32 {
    /// Per slot, the Karatsuba sums `P0 = sum p0 w0`, `P1 = sum p1 w1`, `M = sum (p0 + p1)(w0 + w1)`, 4 lanes each.
    acc: Vec<__m512i>,
    e: Vec<__m512i>,
}

impl Skip32 {
    pub fn new() -> Self {
        // SAFETY: AVX-512F is enabled at compile time.
        let z = unsafe { _mm512_setzero_si512() };
        Self { acc: vec![z; 3 * SLOTS], e: vec![z; 5 * PACKS] }
    }

    pub fn run(&mut self, block: &[u64], w: &Weights32) {
        assert!(block.len() >= BITS * BLOCK_WORDS && w.0.len() >= 3 * BITS);
        // SAFETY: the features are enabled at compile time; every load reads 8 positions inside the asserted lengths
        // (`row_positions(r, 8 zs) + 8 <= BITS`).
        unsafe { self.sum(block, &w.0) }
    }

    #[inline(never)]
    unsafe fn sum(&mut self, block: &[u64], w: &[u64]) {
        unsafe {
            let acc = self.acc.as_mut_ptr();
            for i in 0..3 * SLOTS {
                *acc.add(i) = _mm512_setzero_si512();
            }
            let e = self.e.as_mut_ptr();
            let et = EmbedTables::new();
            for r in 0..5 {
                for zs in 0..8 {
                    let js = row_positions(r, 8 * zs);
                    for x in 0..5 {
                        embed8(&et, block.as_ptr().add(BLOCK_WORDS * js[x]), &mut *(e.add(PACKS * x) as *mut [__m512i; PACKS]));
                    }
                    let wt: [[__m512i; 3]; 5] =
                        std::array::from_fn(|x| std::array::from_fn(|k| _mm512_loadu_si512(w.as_ptr().add(k * BITS + js[x]).cast())));
                    for hg in 0..4 {
                        let q0 = 4 * hg;
                        for p in 0..POINTS {
                            let ev: [__m512i; 5] = std::array::from_fn(|x| {
                                let v = |i: usize| *e.add(PACKS * x + q0 + i);
                                match p {
                                    0 => _mm512_xor_si512(v(0), v(1)),
                                    1 => _mm512_xor_si512(v(2), v(3)),
                                    2 => _mm512_xor_si512(v(0), v(2)),
                                    3 => _mm512_xor_si512(v(1), v(3)),
                                    _ => _mm512_ternarylogic_epi64::<0x96>(v(0), v(1), _mm512_xor_si512(v(2), v(3))),
                                }
                            });
                            let s = acc.add(3 * (5 * hg + p));
                            let (mut a0, mut a1, mut a2) = (*s, *s.add(1), *s.add(2));
                            for x in 0..5 {
                                let (b, c) = (ev[(x + 1) % 5], ev[(x + 2) % 5]);
                                let (even, odd) = (_mm512_clmulepi64_epi128::<0x00>(b, c), _mm512_clmulepi64_epi128::<0x11>(b, c));
                                // Lane L: [p0, p1] of positions 2L (t's qword 0) and 2L + 1 (qword 1).
                                let t = _mm512_unpacklo_epi64(even, odd);
                                let u = _mm512_unpackhi_epi64(even, odd);
                                let m = _mm512_xor_si512(t, u);
                                let [w0, w1, ws] = wt[x];
                                a0 = _mm512_ternarylogic_epi64::<0x96>(a0, _mm512_clmulepi64_epi128::<0x00>(t, w0), _mm512_clmulepi64_epi128::<0x11>(t, w0));
                                a1 = _mm512_ternarylogic_epi64::<0x96>(a1, _mm512_clmulepi64_epi128::<0x00>(u, w1), _mm512_clmulepi64_epi128::<0x11>(u, w1));
                                a2 = _mm512_ternarylogic_epi64::<0x96>(a2, _mm512_clmulepi64_epi128::<0x00>(m, ws), _mm512_clmulepi64_epi128::<0x11>(m, ws));
                            }
                            *s = a0;
                            *s.add(1) = a1;
                            *s.add(2) = a2;
                        }
                    }
                }
            }
        }
    }

    /// Slot `i`'s 256-bit polynomial.
    pub fn get(&self, i: usize) -> [u64; 4] {
        let lanes = |v: __m512i| -> u128 {
            let a: [u128; 4] = unsafe { core::mem::transmute(v) };
            a[0] ^ a[1] ^ a[2] ^ a[3]
        };
        let (p0, p1, m) = (lanes(self.acc[3 * i]), lanes(self.acc[3 * i + 1]), lanes(self.acc[3 * i + 2]));
        let mid = m ^ p0 ^ p1;
        let lo = p0 ^ (mid << 64);
        let hi = p1 ^ (mid >> 64);
        [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64]
    }
}

/// The K = 32 Product pass's block kernel: staged columns, then GFNI outer products with the position weights.
/// W32-P: the maps (a layer's, shared by the threads) apart from each thread's [`Product32Scratch`].
pub struct Product32 {
    row_bytes: Vec<(u8, u8, u8)>,
    mats: Vec<u64>,
    n_active: usize,
}

/// A thread's staging buffers for [`Product32`].
pub struct Product32Scratch {
    staged: Vec<__m512i>,
    e: Vec<__m512i>,
}

/// The GF2P8AFFINE matrix whose output bit `t` sums the input bits `k` with bit `t` of `bytes[k]` set (byte `7 - t`
/// of the matrix is that output's row): the 8 x 8 bit transpose (Hacker's Delight 7-3), bytes reversed.
#[inline(always)]
fn affine8(bytes: [u8; 8]) -> u64 {
    let mut x = u64::from_le_bytes(bytes);
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^= t ^ (t << 28);
    x.swap_bytes()
}

impl Product32 {
    pub fn new(w: &[[u64; 2]]) -> Self {
        let wide = |j: usize| w[j][0] as u128 | (w[j][1] as u128) << 64;
        let mut row_bytes = Vec::new();
        let mut mats = Vec::new();
        for y in 0..5 {
            for zb in 0..8 {
                let j0 = |x: usize| 64 * (x + 5 * y) + 8 * zb;
                let active = |x: usize| (0..8).any(|t| wide(j0(x) + t) != 0);
                let mask = (0..5).fold(0u8, |m, x| m | u8::from(active(x)) << x);
                if mask == 0 {
                    continue;
                }
                row_bytes.push((y as u8, zb as u8, mask));
                for x in (0..5).filter(|&x| active(x)) {
                    for b in 0..16 {
                        // W32-P: matrix byte `7 - i` bit `t` = bit `8 b + i` of position `j0 + 7 - t`'s weight: an 8 x 8
                        // bit transpose of the eight weight bytes, then reversed (the K = 16 kernel's `affine_matrix`).
                        mats.push(affine8(std::array::from_fn(|t| (wide(j0(x) + 7 - t) >> (8 * b)) as u8)));
                    }
                }
            }
        }
        let n_active = mats.len() / 16;
        Self { row_bytes, mats, n_active }
    }

    pub fn scratch(&self) -> Product32Scratch {
        // SAFETY: AVX-512F is enabled at compile time.
        let z = unsafe { _mm512_setzero_si512() };
        Product32Scratch { staged: vec![z; self.n_active.max(1) * PAIRS], e: vec![z; 5 * PACKS] }
    }

    /// `PAIRS * 16` entries of three registers.
    pub fn sums(&self) -> Vec<__m512i> {
        // SAFETY: AVX-512F is enabled at compile time.
        vec![unsafe { _mm512_setzero_si512() }; 3 * 16 * PAIRS]
    }

    /// The block's column sums, times `wb`, into `sums` (unreduced Karatsuba parts).
    pub fn block_sums(&self, sc: &mut Product32Scratch, block: &[u64], wb: [u64; 2], sums: &mut [__m512i]) {
        assert!(block.len() >= BITS * BLOCK_WORDS && sums.len() >= 3 * 16 * PAIRS);
        assert!(sc.staged.len() >= self.n_active * PAIRS && sc.e.len() >= 5 * PACKS);
        // SAFETY: the features are enabled at compile time; the staged buffer holds `n_active * PAIRS` registers.
        unsafe {
            self.stage(sc, block);
            self.accumulate(sc, wb, sums);
        }
    }

    #[inline(never)]
    unsafe fn stage(&self, sc: &mut Product32Scratch, block: &[u64]) {
        unsafe {
            // Volatile loads, so that the constants stay in registers rather than being rematerialized per pack.
            let ones = core::ptr::read_volatile(STAGE_CONSTS.0.as_ptr());
            let bt = core::ptr::read_volatile(STAGE_CONSTS.0.as_ptr().add(1));
            let (c0, c1) = (core::ptr::read_volatile(COL.0[0].as_ptr().cast::<__m512i>()), core::ptr::read_volatile(COL.0[1].as_ptr().cast::<__m512i>()));
            let e = sc.e.as_mut_ptr();
            let et = EmbedTables::new();
            let base = sc.staged.as_mut_ptr() as *mut u8;
            let mut a = 0;
            for &(y, zb, mask) in &self.row_bytes {
                let (y, zb) = (y as usize, zb as usize);
                for x in 0..5 {
                    let j0 = 64 * (x + 5 * y) + 8 * zb;
                    embed8(&et, block.as_ptr().add(BLOCK_WORDS * j0), &mut *(e.add(PACKS * x) as *mut [__m512i; PACKS]));
                }
                // W32-P: per pack, the five positions' embeddings loaded once (not three times), then each active
                // position's product staged at its own run of `PAIRS` registers. Every position active (the claims'
                // weights are nonzero): one base, the five runs at fixed offsets, no per-position test.
                if mask == 31 {
                    let run = base.add(a * PAIRS * 64);
                    a += 5;
                    let (mut lo_at, mut hi_at) = (run, run.add(1024));
                    for q in 0..PACKS {
                        let v: [__m512i; 5] = std::array::from_fn(|x| *e.add(PACKS * x + q));
                        for x in 0..5 {
                            let (za, zb_, zc) = (v[x], v[(x + 1) % 5], v[(x + 2) % 5]);
                            let lin = _mm512_xor_si512(za, zc);
                            let even = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x00>(zb_, zc), _mm512_clmulepi64_epi128::<0x00>(lin, ones));
                            let odd = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x11>(zb_, zc), _mm512_clmulepi64_epi128::<0x11>(lin, ones));
                            let lo = _mm512_gf2p8affine_epi64_epi8(bt, _mm512_permutex2var_epi8(even, c0, odd), 0);
                            let hi = _mm512_gf2p8affine_epi64_epi8(bt, _mm512_permutex2var_epi8(even, c1, odd), 0);
                            _mm512_store_si512(lo_at.add(x * PAIRS * 64).cast(), lo);
                            _mm512_storeu_si512(hi_at.add(x * PAIRS * 64).cast(), hi);
                        }
                        lo_at = lo_at.add(64);
                        hi_at = hi_at.add(41);
                    }
                    continue;
                }
                let mut outs = [core::ptr::null_mut::<u8>(); 5];
                for (x, out) in outs.iter_mut().enumerate() {
                    if mask >> x & 1 == 1 {
                        *out = base.add(a * PAIRS * 64);
                        a += 1;
                    }
                }
                for q in 0..PACKS {
                    let v: [__m512i; 5] = std::array::from_fn(|x| *e.add(PACKS * x + q));
                    for x in 0..5 {
                        let out = outs[x];
                        if out.is_null() {
                            continue;
                        }
                        let (za, zb_, zc) = (v[x], v[(x + 1) % 5], v[(x + 2) % 5]);
                        let lin = _mm512_xor_si512(za, zc);
                        let even = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x00>(zb_, zc), _mm512_clmulepi64_epi128::<0x00>(lin, ones));
                        let odd = _mm512_xor_si512(_mm512_clmulepi64_epi128::<0x11>(zb_, zc), _mm512_clmulepi64_epi128::<0x11>(lin, ones));
                        let lo = _mm512_gf2p8affine_epi64_epi8(bt, _mm512_permutex2var_epi8(even, c0, odd), 0);
                        let hi = _mm512_gf2p8affine_epi64_epi8(bt, _mm512_permutex2var_epi8(even, c1, odd), 0);
                        _mm512_store_si512(out.add(64 * q).cast(), lo);
                        // Bytes 41.. of `hi` are columns 105..128, zero: a whole store, which pack `q + 1`'s
                        // overwrites (the last one ends at byte 1703 < 1728, in the padding).
                        _mm512_storeu_si512(out.add(1024 + 41 * q).cast(), hi);
                    }
                }
            }
            assert_eq!(a, self.n_active);
        }
    }

    #[inline(never)]
    unsafe fn accumulate(&self, sc: &Product32Scratch, wb: [u64; 2], sums: &mut [__m512i]) {
        unsafe {
            let n = self.n_active;
            let (sp, mp) = (sc.staged.as_ptr(), self.mats.as_ptr());
            let wv = _mm512_broadcast_i32x4(_mm_set_epi64x(wb[1] as i64, wb[0] as i64));
            let ws = _mm512_set1_epi64((wb[0] ^ wb[1]) as i64);
            for pair in 0..PAIRS {
                let ldp = |a: usize| *sp.add(a * PAIRS + pair);
                let mut acc = [_mm512_setzero_si512(); 16];
                let mut a = 0;
                let (mut cp, mut mrow) = (sp.add(pair), mp);
                while a + 3 < n {
                    let c = [*cp, *cp.add(PAIRS), *cp.add(2 * PAIRS), *cp.add(3 * PAIRS)];
                    cp = cp.add(4 * PAIRS);
                    let g = |i: usize, b: usize| _mm512_gf2p8affine_epi64_epi8(c[i], _mm512_set1_epi64(*mrow.add(16 * i + b) as i64), 0);
                    macro_rules! step {
                        ($($b:literal)*) => {$(
                            acc[$b] = _mm512_ternarylogic_epi64::<0x96>(acc[$b], _mm512_ternarylogic_epi64::<0x96>(g(0, $b), g(1, $b), g(2, $b)), g(3, $b));
                        )*};
                    }
                    step!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15);
                    a += 4;
                    mrow = mrow.add(64);
                }
                while a < n {
                    let c = ldp(a);
                    for b in 0..16 {
                        acc[b] = _mm512_xor_si512(acc[b], _mm512_gf2p8affine_epi64_epi8(c, _mm512_set1_epi64(*mp.add(16 * a + b) as i64), 0));
                    }
                    a += 1;
                }
                crate::lv::primitives::bits::transpose_bytes16x16_per_lane512(&mut acc);
                // acc[k] lane l: column 64 pair + 16 l + k.
                for (k, e) in acc.into_iter().enumerate() {
                    let am = _mm512_xor_si512(e, _mm512_shuffle_epi32::<0x4e>(e));
                    let p = [
                        _mm512_clmulepi64_epi128::<0x00>(e, wv),
                        _mm512_clmulepi64_epi128::<0x11>(e, wv),
                        _mm512_clmulepi64_epi128::<0x00>(am, ws),
                    ];
                    let s = sums.as_mut_ptr().add(3 * (16 * pair + k));
                    for (i, p) in p.into_iter().enumerate() {
                        *s.add(i) = _mm512_xor_si512(*s.add(i), p);
                    }
                }
            }
        }
    }

    /// W32-P: column `c`'s Karatsuba parts `[P0, P1, M]` from `sums` (`F128Unreduced::from_products`).
    pub fn parts(sums: &[__m512i], c: usize) -> [u128; 3] {
        let (pair, l, k) = (c / 64, (c % 64) / 16, c % 16);
        let lane = |v: __m512i| -> u128 {
            // SAFETY: a register is four 128-bit lanes.
            let a: [u128; 4] = unsafe { core::mem::transmute(v) };
            a[l]
        };
        let s = &sums[3 * (16 * pair + k)..];
        [lane(s[0]), lane(s[1]), lane(s[2])]
    }

    /// Column `c`'s 256-bit sum from `sums`.
    pub fn get(sums: &[__m512i], c: usize) -> [u64; 4] {
        let (pair, l, k) = (c / 64, (c % 64) / 16, c % 16);
        let lane = |v: __m512i| -> u128 {
            let a: [u128; 4] = unsafe { core::mem::transmute(v) };
            a[l]
        };
        let s = &sums[3 * (16 * pair + k)..];
        let (p0, p1, m) = (lane(s[0]), lane(s[1]), lane(s[2]));
        let mid = m ^ p0 ^ p1;
        let lo = p0 ^ (mid << 64);
        let hi = p1 ^ (mid >> 64);
        [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64]
    }
}

/// Embedding only (for the SDE split): every position of a block.
#[inline(never)]
pub fn embed_block(block: &[u64], out: &mut [__m512i; PACKS]) -> u64 {
    assert!(block.len() >= BITS * BLOCK_WORDS);
    let mut x = 0u64;
    let et = EmbedTables::new();
    for j in (0..BITS).step_by(8) {
        // SAFETY: features enabled at compile time; 8 positions inside the block.
        unsafe {
            embed8(&et, block.as_ptr().add(BLOCK_WORDS * j), out);
            x ^= core::mem::transmute::<__m512i, [u64; 8]>(out[0])[0];
        }
    }
    x
}

/// Portable check of [`embed8`] at the 8 positions from `j`.
pub fn embed8_ok(block: &[u64], j: usize) -> bool {
    // SAFETY: features enabled at compile time.
    let mut out = [unsafe { _mm512_setzero_si512() }; PACKS];
    unsafe { embed8(&EmbedTables::new(), block.as_ptr().add(BLOCK_WORDS * j), &mut out) };
    (0..PACKS).all(|q| {
        let v: [u64; 8] = unsafe { core::mem::transmute(out[q]) };
        (0..8).all(|n| v[n] == super::embed(super::pack(block, j + n, q)))
    })
}
