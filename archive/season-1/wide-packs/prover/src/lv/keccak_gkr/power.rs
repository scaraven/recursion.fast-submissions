// Vendored from leanVM 0b850750 `crates/keccak_gkr/src/power.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The field in the power basis of a challenge `s`: an element is its `64 W` coefficients on
//! `1, s, ..., s^(64 W - 1)`, and a product is a carry-less one reduced modulo the minimal polynomial
//! of `s`.
//!
//! The rounds after the bit-level ones stay in this basis. Their tables come out of carry-less
//! sums already in it, and moving every entry to the standard basis would cost more than
//! reducing by a dense modulus does.
//!
//! A table row is laid out by word: word `k` of entry `j` at `k * width + j`.
//!
//! lvm2 E2-K: generic over the field ([`Ext`] of `W` words: E3 at 3, E2 at 2). A `2W`-word product is held in
//! six words and a `W + 1`-word one in four, the high ones zero at `W = 2`. The NEON kernels were E3-only and are
//! not kept: aarch64 takes the portable rows (no tier of the entry is aarch64).

use crate::lv::primitives::field::Ext;

use crate::lv::keccak_gkr::basis::{PolyEval, PowerBasis, add_mul};

pub type Element<const W: usize> = [u64; W];

/// A row kernel's vector form, where one is compiled and `width` is whole vectors of it, else
/// `portable`. The caller bounds every row.
macro_rules! row_kernel {
    ($width:expr, $kernel:ident($($arg:expr),*), $portable:expr) => {
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq") => {
                if $width.is_multiple_of(x86::STEP) {
                    // SAFETY: the features are enabled at compile time, and the caller bounds every row.
                    unsafe { x86::$kernel($($arg),*) }
                } else {
                    $portable
                }
            }
            _ => $portable,
        }
    };
}

pub struct PowerField<F, const W: usize> {
    pub basis: PowerBasis<W>,
    /// `s^(64 W)`, the modulus without its leading term.
    modulus: Element<W>,
    /// `floor(x^(128 W) / modulus)` without its leading term, for Barrett's reduction.
    barrett: Element<W>,
    eval: PolyEval<F, W>,
}

/// The carry-less product of two elements, `2 W` words (of six).
#[inline(always)]
fn mul_wide<const W: usize>(a: &Element<W>, b: &Element<W>) -> [u64; 6] {
    let mut out = [0u64; 6];
    add_mul(&mut out, a, b);
    out
}

impl<F: Ext<W>, const W: usize> PowerField<F, W> {
    /// `None` when `s` lies in a proper subfield.
    ///
    /// lvm2 R9-KG: `s^(64W)` comes from the basis' walk, the division shifts whole words, and the
    /// evaluation table is the layer's largest (`24W` bytes), which [`Self::eval`] lends to the rest.
    pub fn new(s: F) -> Option<Self> {
        let n = 64 * W;
        let (basis, power) = PowerBasis::<W>::with_top(s)?;
        let modulus = basis.to_poly(power);
        // Long division of `x^(2n)` by `x^n + modulus`.
        let mut dividend = [0u64; 7];
        dividend[2 * W] = 1;
        let mut barrett = [0u64; W];
        for bit in (n..=2 * n).rev() {
            if dividend[bit / 64] >> (bit % 64) & 1 == 1 {
                let shift = bit - n;
                if shift < n {
                    barrett[shift / 64] |= 1 << (shift % 64);
                }
                dividend[bit / 64] ^= 1 << (bit % 64);
                // `modulus << shift`, a word at a time.
                let (w, b) = (shift / 64, shift % 64);
                for (k, &m) in modulus.iter().enumerate() {
                    dividend[w + k] ^= m << b;
                    if b != 0 {
                        dividend[w + k + 1] ^= m >> (64 - b);
                    }
                }
            }
        }
        Some(Self {
            basis,
            modulus,
            barrett,
            eval: PolyEval::new(s, 24 * W),
        })
    }

    /// Evaluation at `s` of binary polynomials of at most `24W` bytes.
    pub fn eval(&self) -> &PolyEval<F, W> {
        &self.eval
    }

    pub fn to_poly(&self, a: F) -> Element<W> {
        self.basis.to_poly(a)
    }

    pub fn to_field(&self, a: &Element<W>) -> F {
        self.eval.eval(a)
    }

    /// A polynomial of at most `128 W` coefficients (its first `2 W` words), modulo the minimal polynomial.
    #[inline(always)]
    pub fn reduce(&self, p: &[u64; 6]) -> Element<W> {
        let high: Element<W> = std::array::from_fn(|k| p[W + k]);
        // The quotient: `high`, plus the top half of `high * barrett`.
        let t = mul_wide(&high, &self.barrett);
        let q: Element<W> = std::array::from_fn(|k| high[k] ^ t[W + k]);
        let r = mul_wide(&q, &self.modulus);
        std::array::from_fn(|k| p[k] ^ r[k])
    }

    #[inline(always)]
    pub fn mul(&self, a: &Element<W>, b: &Element<W>) -> Element<W> {
        self.reduce(&mul_wide(a, b))
    }

    /// `sum of a[j] * b[j]` and `sum of (a[j] + a'[j]) * (b[j] + b'[j])` over two pairs of rows,
    /// unreduced.
    pub fn dot_pair(&self, a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        assert!(a.iter().chain(&b).all(|row| row.len() >= W * width));
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq") => {
                if width.is_multiple_of(x86::STEP) {
                    // SAFETY: the features are enabled at compile time, and every row is bounded above.
                    unsafe { x86::dot_pair::<W>(a, b, width) }
                } else {
                    dot_pair_portable::<W>(a, b, width)
                }
            }
            _ => dot_pair_portable::<W>(a, b, width),
        }
    }

    /// `dst[j] = lo[j] + challenge * (lo[j] + hi[j])`.
    pub fn fold_row(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element<W>, width: usize) {
        assert!(dst.len() >= W * width && lo.len() >= W * width && hi.len() >= W * width);
        row_kernel!(
            width,
            fold_row(self, dst, lo, hi, challenge, width),
            self.fold_row_portable(dst, lo, hi, challenge, width)
        )
    }

    /// `dst[j] = wide[j]` reduced, for a row of `W + 1`-word polynomials laid out by word.
    pub fn reduce_row(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        assert!(dst.len() >= W * width && wide.len() >= (W + 1) * width);
        row_kernel!(
            width,
            reduce_row(self, dst, wide, width),
            self.reduce_row_portable(dst, wide, width)
        )
    }

    pub fn reduce_row_portable(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in 0..width {
            let mut p = [0u64; 6];
            for (k, p) in p[..W + 1].iter_mut().enumerate() {
                *p = wide[k * width + j];
            }
            set(dst, width, j, &self.reduce(&p));
        }
    }

    /// `dst[j] = a[j] * b[j] + c[j]`.
    pub fn mul_row(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        assert!(dst.len() >= W * width && [a, b, c].iter().all(|row| row.len() >= W * width));
        row_kernel!(
            width,
            mul_row(self, dst, a, b, c, width),
            self.mul_row_portable(dst, a, b, c, width)
        )
    }

    pub fn mul_row_portable(&self, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in 0..width {
            let (p, c) = (self.mul(&get(a, width, j), &get(b, width, j)), get::<W>(c, width, j));
            set::<W>(dst, width, j, &std::array::from_fn(|k| p[k] ^ c[k]));
        }
    }

    pub fn fold_row_portable(&self, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element<W>, width: usize) {
        for j in 0..width {
            let (l, h) = (get::<W>(lo, width, j), get::<W>(hi, width, j));
            let delta: Element<W> = std::array::from_fn(|k| l[k] ^ h[k]);
            let folded = self.mul(challenge, &delta);
            for k in 0..W {
                dst[k * width + j] = l[k] ^ folded[k];
            }
        }
    }
}

/// Entry `j` of a row.
#[inline(always)]
pub fn get<const W: usize>(row: &[u64], width: usize, j: usize) -> Element<W> {
    std::array::from_fn(|k| row[k * width + j])
}

#[inline(always)]
pub fn set<const W: usize>(row: &mut [u64], width: usize, j: usize, value: &Element<W>) {
    for k in 0..W {
        row[k * width + j] = value[k];
    }
}

pub fn dot_pair_portable<const W: usize>(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
    let (mut zero, mut infinity) = ([0u64; 6], [0u64; 6]);
    for j in 0..width {
        let (a0, a1, b0, b1) = (
            get::<W>(a[0], width, j),
            get::<W>(a[1], width, j),
            get::<W>(b[0], width, j),
            get::<W>(b[1], width, j),
        );
        let da: Element<W> = std::array::from_fn(|k| a0[k] ^ a1[k]);
        let db: Element<W> = std::array::from_fn(|k| b0[k] ^ b1[k]);
        for (acc, p) in [(&mut zero, mul_wide(&a0, &b0)), (&mut infinity, mul_wide(&da, &db))] {
            for (x, y) in acc.iter_mut().zip(p) {
                *x ^= y;
            }
        }
    }
    (zero, infinity)
}

/// The x86 kernels on a register of [`Vector`](crate::lv::keccak_gkr::clmul::Vector) lanes, two entries to a lane.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
mod x86 {
    use super::*;
    use crate::lv::keccak_gkr::clmul::{V, Vector};

    /// Entries to a register.
    pub const STEP: usize = 2 * V::N;

    #[inline(always)]
    unsafe fn load<const W: usize>(row: &[u64], width: usize, j: usize) -> [V; W] {
        unsafe { std::array::from_fn(|k| V::load(row.as_ptr().add(k * width + j))) }
    }

    #[inline(always)]
    unsafe fn store<const W: usize>(row: &mut [u64], width: usize, j: usize, value: [V; W]) {
        for (k, v) in value.into_iter().enumerate() {
            unsafe { V::store(row.as_mut_ptr().add(k * width + j), v) };
        }
    }

    #[inline(always)]
    fn xor<const W: usize>(a: &[V; W], b: &[V; W]) -> [V; W] {
        std::array::from_fn(|k| a[k].xor(b[k]))
    }

    /// The pairwise sums of the words Karatsuba multiplies: `0 + 1`, `0 + 2`, `1 + 2` at `W = 3`, `0 + 1` at
    /// `W = 2` (the rest zero).
    #[inline(always)]
    fn sums<const W: usize>(a: &[V; W]) -> [V; 3] {
        if W == 3 {
            [a[0].xor(a[1]), a[0].xor(a[W - 1]), a[1].xor(a[W - 1])]
        } else {
            [a[0].xor(a[W - 1]), V::zero(), V::zero()]
        }
    }

    /// The products of the entries, as partial sums by word offset: `out[half][s]` holds the
    /// 128-bit sum of `a[i] * b[k]` over `i + k = s`, for the even or the odd entries. Karatsuba's
    /// six products where the schoolbook takes nine (`W = 3`), three where it takes four (`W = 2`).
    #[inline(always)]
    fn karatsuba<const W: usize>(a: &[V; W], sa: &[V; 3], b: &[V; W], sb: &[V; 3]) -> [[V; 5]; 2] {
        let product = |x: V, y: V| [x.clmul::<0x00>(y), x.clmul::<0x11>(y)];
        if W == 3 {
            let (p0, p1, p2) = (product(a[0], b[0]), product(a[1], b[1]), product(a[W - 1], b[W - 1]));
            let (m01, m02, m12) = (product(sa[0], sb[0]), product(sa[1], sb[1]), product(sa[2], sb[2]));
            std::array::from_fn(|h| {
                [
                    p0[h],
                    m01[h].xor(p0[h]).xor(p1[h]),
                    m02[h].xor(p0[h]).xor(p1[h]).xor(p2[h]),
                    m12[h].xor(p1[h]).xor(p2[h]),
                    p2[h],
                ]
            })
        } else {
            let (p0, p1, m) = (product(a[0], b[0]), product(a[W - 1], b[W - 1]), product(sa[0], sb[0]));
            std::array::from_fn(|h| [p0[h], m[h].xor(p0[h]).xor(p1[h]), p1[h], V::zero(), V::zero()])
        }
    }

    #[inline(always)]
    fn partial<const W: usize>(a: &[V; W], b: &[V; W]) -> [[V; 5]; 2] {
        karatsuba(a, &sums(a), b, &sums(b))
    }

    /// Word `w` of a product from its partial sums by offset, in the low word of each lane.
    #[inline(always)]
    fn word(sums: &[V; 5], w: usize) -> V {
        let low = if w < 5 { sums[w] } else { V::zero() };
        let high = if w > 0 { sums[w - 1].high() } else { V::zero() };
        low.xor(high)
    }

    /// Reduce the products given by their `2 W` words in the low word of each lane.
    #[inline(always)]
    fn reduce<F, const W: usize>(field: &PowerField<F, W>, p: &[V; 6]) -> [V; W] {
        let barrett: [V; W] = std::array::from_fn(|k| V::splat(field.barrett[k]));
        let modulus: [V; W] = std::array::from_fn(|k| V::splat(field.modulus[k]));
        let high: [V; W] = std::array::from_fn(|k| p[W + k]);
        // The top `W` words of `high * barrett`: sums at offsets `W - 1 ..`.
        let mut t = [V::zero(); 5];
        for i in 0..W {
            for k in W - 1 - i..W {
                t[i + k] = t[i + k].xor(high[i].clmul::<0x00>(barrett[k]));
            }
        }
        let q: [V; W] = std::array::from_fn(|k| high[k].xor(word(&t, W + k)));
        // The low `W` words of `q * modulus`: sums at offsets `.. W - 1`.
        let mut r = [V::zero(); 5];
        for i in 0..W {
            for k in 0..W - i {
                r[i + k] = r[i + k].xor(q[i].clmul::<0x00>(modulus[k]));
            }
        }
        std::array::from_fn(|k| p[k].xor(word(&r, k)))
    }

    /// [`reduce`] of products of `W + 1` words, whose high half is their word `W` alone: most of
    /// the products vanish.
    #[inline(always)]
    fn reduce_short<F, const W: usize>(field: &PowerField<F, W>, p: &[V; 4]) -> [V; W] {
        let q = p[W].xor(p[W].clmul::<0x00>(V::splat(field.barrett[W - 1])).high());
        let mut r = [V::zero(); 5];
        for k in 0..W {
            r[k] = q.clmul::<0x00>(V::splat(field.modulus[k]));
        }
        std::array::from_fn(|k| word(&r, k).xor(p[k]))
    }

    /// The even and the odd entries' reductions, interleaved back.
    #[inline(always)]
    fn reduce_pair<F, const W: usize>(field: &PowerField<F, W>, sums: &[[V; 5]; 2]) -> [V; W] {
        let [even, odd] = [0, 1].map(|half| reduce(field, &std::array::from_fn(|w| word(&sums[half], w))));
        std::array::from_fn(|k| even[k].unpacklo(odd[k]))
    }

    pub unsafe fn dot_pair<const W: usize>(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        let mut acc = [[V::zero(); 5]; 2];
        for j in (0..width).step_by(STEP) {
            let (a0, a1, b0, b1) = unsafe {
                (
                    load::<W>(a[0], width, j),
                    load::<W>(a[1], width, j),
                    load::<W>(b[0], width, j),
                    load::<W>(b[1], width, j),
                )
            };
            for (acc, p) in acc
                .iter_mut()
                .zip([partial(&a0, &b0), partial(&xor(&a0, &a1), &xor(&b0, &b1))])
            {
                for s in 0..2 * W - 1 {
                    acc[s] = acc[s].xor(p[0][s].xor(p[1][s]));
                }
            }
        }
        let finish = |acc: &[V; 5]| {
            let mut out = [0u64; 6];
            for (s, sum) in acc[..2 * W - 1].iter().enumerate() {
                let sum = sum.sum();
                out[s] ^= sum as u64;
                out[s + 1] ^= (sum >> 64) as u64;
            }
            out
        };
        (finish(&acc[0]), finish(&acc[1]))
    }

    pub unsafe fn reduce_row<F, const W: usize>(field: &PowerField<F, W>, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in (0..width).step_by(STEP) {
            let mut w = [V::zero(); 4];
            for (k, w) in w[..W + 1].iter_mut().enumerate() {
                *w = unsafe { V::load(wide.as_ptr().add(k * width + j)) };
            }
            let [even, odd] = [0, 1].map(|half| {
                let at = |x: V| if half == 0 { x } else { x.high() };
                reduce_short(field, &w.map(at))
            });
            unsafe { store(dst, width, j, std::array::from_fn::<V, W, _>(|k| even[k].unpacklo(odd[k]))) };
        }
    }

    pub unsafe fn mul_row<F, const W: usize>(field: &PowerField<F, W>, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in (0..width).step_by(STEP) {
            let (a, b, c) = unsafe { (load::<W>(a, width, j), load::<W>(b, width, j), load::<W>(c, width, j)) };
            let product = reduce_pair(field, &partial(&a, &b));
            unsafe { store(dst, width, j, xor(&c, &product)) };
        }
    }

    pub unsafe fn fold_row<F, const W: usize>(
        field: &PowerField<F, W>,
        dst: &mut [u64],
        lo: &[u64],
        hi: &[u64],
        challenge: &Element<W>,
        width: usize,
    ) {
        let challenge: [V; W] = std::array::from_fn(|k| V::splat(challenge[k]));
        let challenge_sums = sums(&challenge);
        for j in (0..width).step_by(STEP) {
            let (l, h) = unsafe { (load::<W>(lo, width, j), load::<W>(hi, width, j)) };
            let delta = xor(&l, &h);
            let folded = reduce_pair(field, &karatsuba(&delta, &sums(&delta), &challenge, &challenge_sums));
            unsafe { store(dst, width, j, xor(&l, &folded)) };
        }
    }
}
