// Vendored from leanVM 0b850750 + the pr/all crate diff (04fba039b..edd857be9) `crates/keccak_gkr/src/power.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The field in the power basis of a challenge `s`: an element is its `64 W` coefficients on
//! `1, s, ..., s^(64W - 1)`, and a product is a carry-less one reduced modulo the minimal polynomial
//! of `s`.
//!
//! The rounds after the bit-level ones stay in this basis. Their tables come out of carry-less
//! sums already in it, and moving every entry to the standard basis would cost more than
//! reducing by a dense modulus does.
//!
//! A table row is laid out by word: word `k` of entry `j` at `k * width + j`.
//!
//! lvm2 E2-K: generic over the field of the challenge ([`Ext`] of `W` words: E3 at `W = 3`, E2 at `W = 2`).
//! Wide values keep E3's array sizes (`[u64; 6]` for a product, `[V; 5]` for its partial sums by word offset);
//! at `W = 2` only the first `2W` words (`2W - 1` sums) are used and the rest stay zero. The `aarch64` (`neon`)
//! kernels below are E3's and are not compiled on any tier this entry builds (this tree is mounted only on v4).

use crate::lv::primitives::field::Ext;

use crate::lv::keccak_gkr::basis::{PolyEval, PowerBasis};
use crate::lv::keccak_gkr::keccak::{BITS, along};
use crate::lv::primitives::field::gf2_64::mul_wide;

/// An element in the power basis: `W` words.
pub type Element<const W: usize> = [u64; W];

/// The words of one lane's 64 entries of a row: `W * 64`.
#[inline(always)]
pub const fn factor_row<const W: usize>() -> usize {
    W * 64
}

/// lvm2 PFAST-K2: `dst[z] = src[z] ^ x` for 64 words, a register at a time where AVX-512 is (the scalar loop
/// checked each index and did not vectorize).
#[inline(always)]
fn xor_splat64(dst: &mut [u64], src: &[u64], x: u64) {
    let (dst, src): (&mut [u64; 64], &[u64; 64]) = (dst.try_into().unwrap(), src.try_into().unwrap());
    #[cfg(target_feature = "avx512f")]
    {
        use core::arch::x86_64::*;
        use crate::lv::primitives::simd::{load, store};
        // SAFETY: AVX-512F is enabled at compile time; `load` and `store` check their bounds.
        let splat = unsafe { _mm512_set1_epi64(x as i64) };
        for i in 0..8 {
            store(&mut dst[..], i, unsafe { _mm512_xor_si512(load(&src[..], i), splat) });
        }
    }
    #[cfg(not(target_feature = "avx512f"))]
    for (d, s) in dst.iter_mut().zip(src) {
        *d = s ^ x;
    }
}

/// A row kernel's vector form, where one is compiled and `width` is whole vectors of it, else
/// `portable`. The caller bounds every row.
macro_rules! row_kernel {
    ($width:expr, $kernel:ident $(::<$gen:ident>)? ($($arg:expr),*), $portable:expr) => {
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq") => {
                if $width.is_multiple_of(x86::STEP) {
                    // SAFETY: the features are enabled at compile time, and the caller bounds every row.
                    unsafe { x86::$kernel $(::<$gen>)? ($($arg),*) }
                } else {
                    $portable
                }
            }
            all(target_arch = "aarch64", target_feature = "aes") => {
                if $width.is_multiple_of(2) {
                    // SAFETY: the feature is enabled at compile time, and the caller bounds every row.
                    unsafe { neon::$kernel $(::<$gen>)? ($($arg),*) }
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
    /// `s^(64W)`, the modulus without its leading term.
    modulus: Element<W>,
    /// `floor(x^(128W) / modulus)` without its leading term, for Barrett's reduction.
    barrett: Element<W>,
    eval: PolyEval<F, W>,
}

/// `acc += a * b` on binary polynomials of `W` words, into the first `2W` words.
#[inline(always)]
fn add_mul_w<const W: usize, const N: usize>(acc: &mut [u64; N], a: &[u64; W], b: &[u64; W]) {
    for i in 0..W {
        for k in 0..W {
            let p = mul_wide(a[i], b[k]);
            acc[i + k] ^= p as u64;
            acc[i + k + 1] ^= (p >> 64) as u64;
        }
    }
}

/// The carry-less product of two elements, `2W` words (of six).
#[inline(always)]
fn mul_wide_w<const W: usize>(a: &Element<W>, b: &Element<W>) -> [u64; 6] {
    let mut out = [0u64; 6];
    add_mul_w(&mut out, a, b);
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

    /// A polynomial of at most `128 W` coefficients (its first `2W` words), modulo the minimal polynomial.
    #[inline(always)]
    pub fn reduce(&self, p: &[u64; 6]) -> Element<W> {
        let high: Element<W> = std::array::from_fn(|k| p[W + k]);
        // The quotient: `high`, plus the top half of `high * barrett`.
        let t = mul_wide_w(&high, &self.barrett);
        let q: Element<W> = std::array::from_fn(|k| high[k] ^ t[W + k]);
        let r = mul_wide_w(&q, &self.modulus);
        std::array::from_fn(|k| p[k] ^ r[k])
    }

    #[inline(always)]
    pub fn mul(&self, a: &Element<W>, b: &Element<W>) -> Element<W> {
        self.reduce(&mul_wide_w(a, b))
    }

    /// `sum of a[j] * b[j]` and `sum of (a[j] + a'[j]) * (b[j] + b'[j])` over two pairs of rows,
    /// unreduced.
    pub fn dot_pair(&self, a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        assert!(a.iter().chain(&b).all(|row| row.len() >= W * width));
        row_kernel!(width, dot_pair::<W>(a, b, width), dot_pair_portable::<W>(a, b, width))
    }

    /// `sum_j (weights[j] * a[j]) * b[j]`, with the inner product reduced and the sum unreduced.
    pub fn weighted_dot(&self, a: &[u64], b: &[u64], weights: &[u64], width: usize) -> [u64; 6] {
        assert!([a, b, weights].iter().all(|row| row.len() >= W * width));
        row_kernel!(
            width,
            weighted_dot(self, a, b, weights, width),
            self.weighted_dot_portable(a, b, weights, width)
        )
    }

    fn weighted_dot_portable(&self, a: &[u64], b: &[u64], weights: &[u64], width: usize) -> [u64; 6] {
        let mut sum = [0; 6];
        for j in 0..width {
            let product = self.mul(&get(a, width, j), &get(weights, width, j));
            add_mul_w(&mut sum, &product, &get(b, width, j));
        }
        sum
    }

    /// lvm2 PFAST-K3: `dot += sum_j (a[j] * weights[j]) * b[j]` at `W = 2` with every product unreduced: [`WideDot::finish`]
    /// gives `3W` words of six, congruent to the sum of [`Self::weighted_dot`]s modulo the minimal polynomial.
    pub fn weighted_dot_e2_add(&self, dot: &mut WideDot, a: &[u64], b: &[u64], weights: &[u64], width: usize) {
        assert!(W == 2);
        assert!([a, b, weights].iter().all(|row| row.len() >= W * width));
        row_kernel!(
            width,
            weighted_dot_e2_add(&mut dot.vector, a, b, weights, width),
            self.weighted_dot_e2_portable(&mut dot.words, a, b, weights, width)
        )
    }

    fn weighted_dot_e2_portable(&self, sum: &mut [u64; 6], a: &[u64], b: &[u64], weights: &[u64], width: usize) {
        for j in 0..width {
            let product = mul_wide_w(&get::<W>(a, width, j), &get::<W>(weights, width, j));
            let y = get::<W>(b, width, j);
            for i in 0..2 * W {
                for (k, &y) in y.iter().enumerate() {
                    let p = mul_wide(product[i], y);
                    sum[i + k] ^= p as u64;
                    if i + k + 1 < 6 {
                        sum[i + k + 1] ^= (p >> 64) as u64;
                    }
                }
            }
        }
    }

    /// The dot products of `B[j] = weights[j] * (kappa + T[j + 1]) + constant[j]` and `T[j + 2]`,
    /// at zero and infinity over two rows, unreduced or not. Weights and constants are by lane,
    /// then by word.
    pub fn chi_dot_pair(
        &self,
        t: [&[u64]; 2],
        weights: &[u64],
        constant: &[u64],
        kappa: &Element<W>,
        scratch: &mut [u64],
    ) -> ([u64; 6], [u64; 6]) {
        assert!(
            t.into_iter()
                .chain([weights, constant])
                .all(|row| row.len() >= W * BITS)
        );
        assert!(scratch.len() >= 4 * factor_row::<W>());
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
        if 64usize.is_multiple_of(x86::STEP) {
            // SAFETY: the rows are bounded above, and a lane contains whole vectors.
            return unsafe { x86::chi_dot_pair(self, t, weights, constant, kappa, scratch) };
        }
        self.chi_dot_pair_by_lane(t, weights, constant, kappa, scratch)
    }

    fn chi_dot_pair_by_lane(
        &self,
        t: [&[u64]; 2],
        weights: &[u64],
        constant: &[u64],
        kappa: &Element<W>,
        scratch: &mut [u64],
    ) -> ([u64; 6], [u64; 6]) {
        let fr = factor_row::<W>();
        let (b, shifted) = scratch.split_at_mut(2 * fr);
        let (mut zero, mut infinity) = ([0u64; 6], [0u64; 6]);
        for lane in 0..BITS / 64 {
            for (half, t) in t.into_iter().enumerate() {
                let (b, shifted) = (&mut b[half * fr..][..fr], &mut shifted[half * fr..][..fr]);
                let at = along(64 * lane, 1);
                for k in 0..W {
                    for z in 0..64 {
                        shifted[64 * k + z] = t[k * BITS + at + z] ^ kappa[k];
                    }
                }
                let at = fr * lane;
                self.mul_row(b, &weights[at..][..fr], shifted, &constant[at..][..fr], 64);
                let at = along(64 * lane, 2);
                for k in 0..W {
                    shifted[64 * k..][..64].copy_from_slice(&t[k * BITS + at..][..64]);
                }
            }
            let (z, i) = self.dot_pair([&b[..fr], &b[fr..]], [&shifted[..fr], &shifted[fr..]], 64);
            for k in 0..6 {
                zero[k] ^= z[k];
                infinity[k] ^= i[k];
            }
        }
        (zero, infinity)
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

    /// Fold rows indexed by `x + 2y`, with challenges `[r, s, r*s]`, sharing one reduction.
    pub fn fold_quad(&self, dst: &mut [u64], rows: [&[u64]; 4], challenges: &[Element<W>; 3], width: usize) {
        assert!(dst.len() >= W * width && rows.iter().all(|row| row.len() >= W * width));
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
        if width.is_multiple_of(x86::STEP) {
            // SAFETY: the features are enabled at compile time and the rows are bounded above.
            unsafe { x86::fold_quad(self, dst, rows, challenges, width) };
            return;
        }
        for j in 0..width {
            let [a, b, c, d] = rows.map(|row| get::<W>(row, width, j));
            let differences: [Element<W>; 3] = [
                std::array::from_fn(|k| a[k] ^ b[k]),
                std::array::from_fn(|k| a[k] ^ c[k]),
                std::array::from_fn(|k| a[k] ^ b[k] ^ c[k] ^ d[k]),
            ];
            let mut wide = [0; 6];
            for (delta, r) in differences.iter().zip(challenges) {
                add_mul_w(&mut wide, delta, r);
            }
            let folded = self.reduce(&wide);
            set::<W>(dst, width, j, &std::array::from_fn(|k| a[k] ^ folded[k]));
        }
    }

    /// Chi at (0,0), (inf,0), (0,1), (inf,1), (1,0), (1,inf), (0,inf), (inf,inf).
    /// Infinity selects the leading coefficient in that variable.
    pub fn chi_dot_quad(
        &self,
        rows: [&[u64]; 4],
        weights: &[u64],
        constant: &[u64],
        kappa: &Element<W>,
        scratch: &mut [u64],
    ) -> [[u64; 6]; 8] {
        let fr = factor_row::<W>();
        assert!(
            rows.into_iter()
                .chain([weights, constant])
                .all(|row| row.len() >= W * BITS)
        );
        assert!(scratch.len() >= 12 * fr);
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
        if W == 2 && 64usize.is_multiple_of(x86::STEP) {
            // SAFETY: the rows are bounded above, and a lane contains whole vectors.
            return unsafe { x86::chi_dot_quad_e2(self, rows, weights, constant, kappa) };
        }
        let (a, b) = scratch.split_at_mut(6 * fr);
        let mut sums = [[0; 6]; 8];
        for lane in 0..BITS / 64 {
            for (i, row) in rows.iter().enumerate() {
                let (a, b) = (&mut a[i * fr..][..fr], &mut b[i * fr..][..fr]);
                for k in 0..W {
                    xor_splat64(&mut b[64 * k..][..64], &row[BITS * k + along(64 * lane, 1)..][..64], kappa[k]);
                }
                let at = lane * fr;
                self.mul_row(a, &weights[at..], b, &constant[at..], 64);
                for k in 0..W {
                    xor_splat64(&mut b[64 * k..][..64], &row[BITS * k + along(64 * lane, 2)..][..64], 0);
                }
            }
            for row in [&mut *a, &mut *b] {
                for k in 0..2 * fr {
                    row[4 * fr + k] = row[k] ^ row[2 * fr + k];
                }
            }
            for (pair, [lo, hi]) in [[0, 1], [2, 3], [1, 3], [4, 5]].into_iter().enumerate() {
                let (zero, infinity) = self.dot_pair(
                    [lo, hi].map(|i| &a[i * fr..][..fr]),
                    [lo, hi].map(|i| &b[i * fr..][..fr]),
                    64,
                );
                for k in 0..6 {
                    sums[2 * pair][k] ^= zero[k];
                    sums[2 * pair + 1][k] ^= infinity[k];
                }
            }
        }
        sums
    }

    /// `dst[j] = wide[j]` reduced, for a row of `W + 1`-word polynomials laid out by word.
    #[cfg(any(
        test,
        not(all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512vbmi",
            target_feature = "gfni"
        ))
    ))]
    pub fn reduce_row(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        assert!(dst.len() >= W * width && wide.len() >= (W + 1) * width);
        row_kernel!(
            width,
            reduce_row(self, dst, wide, width),
            self.reduce_row_portable(dst, wide, width)
        )
    }

    #[cfg(any(
        test,
        not(all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512vbmi",
            target_feature = "gfni"
        ))
    ))]
    pub fn reduce_row_portable(&self, dst: &mut [u64], wide: &[u64], width: usize) {
        for j in 0..width {
            let p: [u64; 6] = std::array::from_fn(|k| if k <= W { wide[k * width + j] } else { 0 });
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

/// lvm2 PFAST-K3: the running sum of [`PowerField::weighted_dot_e2_add`]: the x86 kernel's Karatsuba sums (six
/// registers of at most 512 bits, combined once by [`WideDot::finish`]) and the portable kernel's words.
#[derive(Clone, Copy)]
pub struct WideDot {
    vector: [u64; 48],
    words: [u64; 6],
}

impl WideDot {
    pub fn new() -> Self {
        Self { vector: [0; 48], words: [0; 6] }
    }

    /// The sum, `3W` words of six (at `W = 2`), unreduced.
    pub fn finish(&self) -> [u64; 6] {
        #[allow(unused_mut)]
        let mut out = self.words;
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
        {
            // SAFETY: the features are enabled at compile time.
            let v = unsafe { x86::finish_wide_dot(&self.vector) };
            for (o, v) in out.iter_mut().zip(v) {
                *o ^= v;
            }
        }
        out
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
        add_mul_w(&mut zero, &a0, &b0);
        add_mul_w(&mut infinity, &da, &db);
    }
    (zero, infinity)
}

/// The x86 kernels on a register of [`V`](crate::lv::keccak_gkr::clmul::V) lanes, two entries to a lane. They carry
/// the features of `V`, which this module's cfg guarantees, so the dispatch calls them with `unsafe`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "pclmulqdq"))]
mod x86 {
    use super::*;
    use crate::lv::keccak_gkr::clmul::{V, clmul_kernel};

    /// Entries to a register.
    pub const STEP: usize = 2 * V::N;

    clmul_kernel! {
        fn load_w<const W: usize>(row: &[u64], width: usize, j: usize) -> [V; W] {
            std::array::from_fn(|k| V::load(row, k * width + j))
        }

        fn store_w<const W: usize>(row: &mut [u64], width: usize, j: usize, value: [V; W]) {
            for (k, v) in value.into_iter().enumerate() {
                V::store(row, k * width + j, v);
            }
        }

        fn xor_w<const W: usize>(a: &[V; W], b: &[V; W]) -> [V; W] {
            std::array::from_fn(|k| a[k].xor(b[k]))
        }

        /// The pairwise sums Karatsuba multiplies: at `W = 3` the words `0 + 1`, `0 + 2`, `1 + 2`; at `W = 2`
        /// the word `0 + 1` (the rest unused).
        fn sums<const W: usize>(a: &[V; W]) -> [V; 3] {
            if W == 3 {
                [a[0].xor(a[1]), a[0].xor(a[2 % W]), a[1].xor(a[2 % W])]
            } else {
                [a[0].xor(a[1 % W]), V::zero(), V::zero()]
            }
        }

        /// The products of the entries, as partial sums by word offset: `out[half][s]` holds the
        /// 128-bit sum of `a[i] * b[k]` over `i + k = s`, for the even or the odd entries. Karatsuba's
        /// six products where the schoolbook takes nine at `W = 3`; three where it takes four at `W = 2`.
        /// Sums `2W - 1..` are zero.
        fn karatsuba<const W: usize>(a: &[V; W], sa: &[V; 3], b: &[V; W], sb: &[V; 3]) -> [[V; 5]; 2] {
            let product = |x: V, y: V| [x.clmul::<0x00>(y), x.clmul::<0x11>(y)];
            if W == 3 {
                let (p0, p1, p2) = (product(a[0], b[0]), product(a[1], b[1]), product(a[2 % W], b[2 % W]));
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
                let (p0, p1, m) = (product(a[0], b[0]), product(a[1 % W], b[1 % W]), product(sa[0], sb[0]));
                std::array::from_fn(|h| [p0[h], m[h].xor(p0[h]).xor(p1[h]), p1[h], V::zero(), V::zero()])
            }
        }

        fn partial<const W: usize>(a: &[V; W], b: &[V; W]) -> [[V; 5]; 2] {
            karatsuba(a, &sums(a), b, &sums(b))
        }

        /// Word `w` of a product from its partial sums by offset, in the low word of each lane.
        fn word(sums: &[V; 5], w: usize) -> V {
            let low = if w < 5 { sums[w] } else { V::zero() };
            let high = if w > 0 { sums[w - 1].high() } else { V::zero() };
            low.xor(high)
        }

        /// Reduce the products given by their `2W` words in the low word of each lane.
        fn reduce<F: Ext<W>, const W: usize>(field: &PowerField<F, W>, p: &[V; 6]) -> [V; W] {
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
        #[cfg(any(test, not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vbmi", target_feature = "gfni"))))]
        fn reduce_w1<F: Ext<W>, const W: usize>(field: &PowerField<F, W>, p: &[V; 4]) -> [V; W] {
            let q = p[W].xor(p[W].clmul::<0x00>(V::splat(field.barrett[W - 1])).high());
            let mut r = [V::zero(); 5];
            for k in 0..W {
                r[k] = q.clmul::<0x00>(V::splat(field.modulus[k]));
            }
            std::array::from_fn(|k| word(&r, k).xor(p[k]))
        }

        /// The even and the odd entries' reductions, interleaved back.
        fn reduce_pair<F: Ext<W>, const W: usize>(field: &PowerField<F, W>, sums: &[[V; 5]; 2]) -> [V; W] {
            let [even, odd] = [0, 1].map(|half| reduce(field, &std::array::from_fn(|w| word(&sums[half], w))));
            std::array::from_fn(|k| even[k].unpacklo(odd[k]))
        }

        pub fn dot_pair<const W: usize>(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
            let mut acc = [[V::zero(); 5]; 2];
            for j in (0..width).step_by(STEP) {
                let (a0, a1, b0, b1) = (
                    load_w::<W>(a[0], width, j),
                    load_w::<W>(a[1], width, j),
                    load_w::<W>(b[0], width, j),
                    load_w::<W>(b[1], width, j),
                );
                for (acc, p) in acc
                    .iter_mut()
                    .zip([partial(&a0, &b0), partial(&xor_w(&a0, &a1), &xor_w(&b0, &b1))])
                {
                    for s in 0..2 * W - 1 {
                        acc[s] = acc[s].xor(p[0][s].xor(p[1][s]));
                    }
                }
            }
            finish_dot(&acc)
        }

        fn finish_dot(acc: &[[V; 5]; 2]) -> ([u64; 6], [u64; 6]) {
            let finish = |acc: &[V; 5]| {
                let mut out = [0u64; 6];
                for (s, sum) in acc.iter().enumerate() {
                    let sum = sum.sum();
                    out[s] ^= sum as u64;
                    out[s + 1] ^= (sum >> 64) as u64;
                }
                out
            };
            (finish(&acc[0]), finish(&acc[1]))
        }

        pub fn weighted_dot<F: Ext<W>, const W: usize>(field: &PowerField<F, W>, a: &[u64], b: &[u64], weights: &[u64], width: usize) -> [u64; 6] {
            let mut acc = [V::zero(); 5];
            for j in (0..width).step_by(STEP) {
                let weighted = reduce_pair(field, &partial(&load_w::<W>(a, width, j), &load_w::<W>(weights, width, j)));
                let p = partial(&weighted, &load_w::<W>(b, width, j));
                for k in 0..2 * W - 1 {
                    acc[k] = acc[k].xor(p[0][k].xor(p[1][k]));
                }
            }
            finish_dot(&[acc, [V::zero(); 5]]).0
        }

        /// lvm2 PFAST-K3: [`weighted_dot`] at `W = 2` with `a * weights` left unreduced, four words a half: its words
        /// meet `b` in two Karatsuba products by pairs (words 0, 1 and 2, 3), six products a half where the
        /// reduction and one product took nine. The Karatsuba sums (of the low pair `P0`, `P1`, `M` and the high
        /// pair `Q0`, `Q1`, `N`) run on in `acc`, six registers, until [`finish_wide_dot`].
        pub fn weighted_dot_e2_add(acc: &mut [u64; 48], a: &[u64], b: &[u64], weights: &[u64], width: usize) {
            let mut sums: [V; 6] = std::array::from_fn(|k| V::load(&acc[..], 2 * V::N * k));
            for j in (0..width).step_by(STEP) {
                let (x, w, y) = (load_w::<2>(a, width, j), load_w::<2>(weights, width, j), load_w::<2>(b, width, j));
                let (sx, sw, sy) = (x[0].xor(x[1]), w[0].xor(w[1]), y[0].xor(y[1]));
                let even = weighted_half::<0x00, 0x00, 0x01>(&x, sx, &w, sw, &y, sy);
                let odd = weighted_half::<0x11, 0x10, 0x11>(&x, sx, &w, sw, &y, sy);
                for k in 0..6 {
                    sums[k] = sums[k].xor(even[k].xor(odd[k]));
                }
            }
            for (k, sum) in sums.into_iter().enumerate() {
                V::store(&mut acc[..], 2 * V::N * k, sum);
            }
        }

        /// The words of [`weighted_dot_e2_add`]'s sums: the two pairs' products at word offsets 0 and 2.
        pub fn finish_wide_dot(acc: &[u64; 48]) -> [u64; 6] {
            let [p0, p1, m, q0, q1, n]: [V; 6] = std::array::from_fn(|k| V::load(&acc[..], 2 * V::N * k));
            let sums = [p0, m.xor(p0).xor(p1), p1.xor(q0), n.xor(q0).xor(q1), q1];
            finish_dot(&[sums, [V::zero(); 5]]).0
        }

        /// One half's products for [`weighted_dot_e2_add`]: `AW` picks the half's words of `a` and `weights`, `LO` and
        /// `HI` a low or a high word of `a * weights` against the half's word of `b`.
        fn weighted_half<const AW: i32, const LO: i32, const HI: i32>(
            x: &[V; 2],
            sx: V,
            w: &[V; 2],
            sw: V,
            y: &[V; 2],
            sy: V,
        ) -> [V; 6] {
            let (p0, p1, m) = (x[0].clmul::<AW>(w[0]), x[1].clmul::<AW>(w[1]), sx.clmul::<AW>(sw));
            // `a * weights` by words: `W0 = p0.lo`, `W1 = p0.hi + s.lo`, `W2 = s.hi + p1.lo`, `W3 = p1.hi`, where
            // `s = m + p0 + p1`. `e.lo = W0 + W1`, `f.hi = W2 + W3`, `v = [W1, W2]`.
            let al = p1.align_high_low(p0);
            let e = m.xor(p1).xor(al);
            let f = m.xor(p0).xor(al);
            let v = e.xor(p0);
            [
                p0.clmul::<LO>(y[0]),
                v.clmul::<LO>(y[1]),
                e.clmul::<LO>(sy),
                v.clmul::<HI>(y[0]),
                p1.clmul::<HI>(y[1]),
                f.clmul::<HI>(sy),
            ]
        }

        /// lvm2 PFAST-K3: one half's product at `W = 2` (`H` picks the words), reduced as [`reduce`] does: `[R0, R1]`
        /// in each lane. Barrett's constants come as `[low, high]` lanes, so the products pick their words in place.
        fn mul_half_e2<const H: i32>(x: &[V; 2], sx: V, y: &[V; 2], sy: V, barrett: V, modulus: V) -> V {
            let (p0, p1, m) = (x[0].clmul::<H>(y[0]), x[1].clmul::<H>(y[1]), sx.clmul::<H>(sy));
            // The product's words: `[W0, W1] = p0 + s.low()`, `[W2, W3] = p1 + s.high()`, `s = m + p0 + p1`.
            let s = m.xor(p0).xor(p1);
            let high = p1.xor(s.high());
            // `q = high + the top two words of high * barrett`: the products at word offsets 1 and 2.
            let t1 = high.clmul::<0x10>(barrett).xor(high.clmul::<0x01>(barrett));
            let q = high.xor(high.clmul::<0x11>(barrett)).xor(t1.high());
            // The low two words of `q * modulus`: the products at offsets 0 and 1.
            let r1 = q.clmul::<0x10>(modulus).xor(q.clmul::<0x01>(modulus));
            p0.xor(q.clmul::<0x00>(modulus)).xor(s.xor(r1).low())
        }

        /// lvm2 PFAST-K3: `x * y` reduced at `W = 2`, by word.
        fn mul_e2(x: &[V; 2], y: &[V; 2], sy: V, barrett: V, modulus: V) -> [V; 2] {
            let sx = x[0].xor(x[1]);
            let even = mul_half_e2::<0x00>(x, sx, y, sy, barrett, modulus);
            let odd = mul_half_e2::<0x11>(x, sx, y, sy, barrett, modulus);
            [even.unpacklo(odd), even.unpackhi(odd)]
        }

        /// lvm2 PFAST-K3: `acc += x * y` unreduced at `W = 2`, as Karatsuba's three sums (`x0 y0`, `x1 y1`,
        /// `(x0 + x1)(y0 + y1)`) of both halves, combined by [`finish_karatsuba`].
        fn dot_add_e2(acc: &mut [V; 3], x: &[V; 2], y: &[V; 2]) {
            let (sx, sy) = (x[0].xor(x[1]), y[0].xor(y[1]));
            acc[0] = acc[0].xor(x[0].clmul::<0x00>(y[0]).xor(x[0].clmul::<0x11>(y[0])));
            acc[1] = acc[1].xor(x[1].clmul::<0x00>(y[1]).xor(x[1].clmul::<0x11>(y[1])));
            acc[2] = acc[2].xor(sx.clmul::<0x00>(sy).xor(sx.clmul::<0x11>(sy)));
        }

        fn finish_karatsuba(acc: &[V; 3]) -> [u64; 6] {
            let [p0, p1, m] = *acc;
            finish_dot(&[[p0, m.xor(p0).xor(p1), p1, V::zero(), V::zero()], [V::zero(); 5]]).0
        }

        /// lvm2 PFAST-K3: [`PowerField::chi_dot_quad`] at `W = 2` in one pass over each lane's entries: the four rows'
        /// `B` (reduced, as `mul_row` gives it) and `T[j + 2]` stay in registers, and the dot products' Karatsuba
        /// sums run over every lane and are combined once. The same sums, word for word.
        pub fn chi_dot_quad_e2<F: Ext<W>, const W: usize>(
            field: &PowerField<F, W>,
            rows: [&[u64]; 4],
            weights: &[u64],
            constant: &[u64],
            kappa: &Element<W>,
        ) -> [[u64; 6]; 8] {
            let fr = factor_row::<W>();
            let kappa = [V::splat(kappa[0]), V::splat(kappa[1 % W])];
            let barrett = V::pair(field.barrett[0], field.barrett[1 % W]);
            let modulus = V::pair(field.modulus[0], field.modulus[1 % W]);
            let mut acc = [[V::zero(); 3]; 8];
            // A lane's 64 entries of a row, by word: fixed lengths, so the loads below need no checks.
            fn words(row: &[u64], at: usize, stride: usize) -> [&[u64; 64]; 2] {
                std::array::from_fn(|k| row[k * stride + at..][..64].try_into().unwrap())
            }
            let load = |words: &[&[u64; 64]; 2], z: usize| -> [V; 2] { std::array::from_fn(|k| V::load(&words[k][..], z)) };
            for lane in 0..BITS / 64 {
                let (weights, constant) = (words(weights, fr * lane, 64), words(constant, fr * lane, 64));
                let (at1, at2) = (along(64 * lane, 1), along(64 * lane, 2));
                let t: [[&[u64; 64]; 2]; 4] = std::array::from_fn(|i| words(rows[i], at1, BITS));
                let u: [[&[u64; 64]; 2]; 4] = std::array::from_fn(|i| words(rows[i], at2, BITS));
                for step in 0..64 / STEP {
                    let z = step * STEP;
                    let (w, c) = (load(&weights, z), load(&constant, z));
                    let sw = w[0].xor(w[1]);
                    let a: [[V; 2]; 4] = std::array::from_fn(|i| {
                        let t = xor_w(&load(&t[i], z), &kappa);
                        xor_w(&c, &mul_e2(&t, &w, sw, barrett, modulus))
                    });
                    let b: [[V; 2]; 4] = std::array::from_fn(|i| load(&u[i], z));
                    let (a4, b4) = (xor_w(&a[0], &a[2]), xor_w(&b[0], &b[2]));
                    let (a5, b5) = (xor_w(&a[1], &a[3]), xor_w(&b[1], &b[3]));
                    let pairs = [(a[0], a[1], b[0], b[1]), (a[2], a[3], b[2], b[3]), (a[1], a[3], b[1], b[3]), (a4, a5, b4, b5)];
                    for (p, (alo, ahi, blo, bhi)) in pairs.into_iter().enumerate() {
                        dot_add_e2(&mut acc[2 * p], &alo, &blo);
                        dot_add_e2(&mut acc[2 * p + 1], &xor_w(&alo, &ahi), &xor_w(&blo, &bhi));
                    }
                }
            }
            std::array::from_fn(|i| finish_karatsuba(&acc[i]))
        }

        /// `B` stays unreduced, `2W` words: its two halves each meet `T[j + 2]` in a Karatsuba
        /// product, which costs fewer products than reducing `B` first. The sums are reduced once.
        pub fn chi_dot_pair<F: Ext<W>, const W: usize>(
            field: &PowerField<F, W>,
            t: [&[u64]; 2],
            weights: &[u64],
            constant: &[u64],
            kappa: &Element<W>,
            scratch: &mut [u64],
        ) -> ([u64; 6], [u64; 6]) {
            let fr = factor_row::<W>();
            let kappa: [V; W] = std::array::from_fn(|k| V::splat(kappa[k]));
            // Sums by word offset: the low half's products at 0, the high half's at `W`.
            let mut acc = [[V::zero(); 8]; 2];
            for lane in 0..BITS / 64 {
                let (weights, constant) = (&weights[fr * lane..], &constant[fr * lane..]);
                let at = along(64 * lane, 1);
                for (half, t) in t.into_iter().enumerate() {
                    let b = &mut scratch[2 * half * fr..][..2 * fr];
                    for z in (0..64).step_by(STEP) {
                        let (w, c, shifted) = (
                            load_w::<W>(weights, 64, z),
                            load_w::<W>(constant, 64, z),
                            xor_w(&load_w::<W>(t, BITS, at + z), &kappa),
                        );
                        let sums = partial(&w, &shifted);
                        let [even, odd] = [0, 1].map(|h| -> [V; 6] { std::array::from_fn(|k| word(&sums[h], k)) });
                        let low: [V; W] = std::array::from_fn(|k| even[k].unpacklo(odd[k]));
                        let high: [V; W] = std::array::from_fn(|k| even[W + k].unpacklo(odd[W + k]));
                        store_w(b, 64, z, xor_w(&c, &low));
                        store_w(&mut b[fr..], 64, z, high);
                    }
                }
                let at = along(64 * lane, 2);
                for z in (0..64).step_by(STEP) {
                    let b: [[V; W]; 4] = std::array::from_fn(|i| load_w::<W>(&scratch[i * fr..], 64, z));
                    let (t0, t1) = (load_w::<W>(t[0], BITS, at + z), load_w::<W>(t[1], BITS, at + z));
                    let (dt, db) = (xor_w(&t0, &t1), [xor_w(&b[0], &b[2]), xor_w(&b[1], &b[3])]);
                    for (acc, (a, t)) in acc.iter_mut().zip([([b[0], b[1]], t0), (db, dt)]) {
                        let (low, high) = (partial(&a[0], &t), partial(&a[1], &t));
                        for s in 0..2 * W - 1 {
                            acc[s] = acc[s].xor(low[0][s].xor(low[1][s]));
                            acc[s + W] = acc[s + W].xor(high[0][s].xor(high[1][s]));
                        }
                    }
                }
            }
            let finish = |acc: &[V; 8]| -> [u64; 6] {
                let mut wide = [0u64; 9];
                for (s, sum) in acc[..3 * W - 1].iter().enumerate() {
                    let sum = sum.sum();
                    wide[s] ^= sum as u64;
                    wide[s + 1] ^= (sum >> 64) as u64;
                }
                let high = field.reduce(&std::array::from_fn(|k| if k < 2 * W { wide[W + k] } else { 0 }));
                let r = field.reduce(&std::array::from_fn(|k| if k < W { wide[k] } else if k < 2 * W { high[k - W] } else { 0 }));
                std::array::from_fn(|k| if k < W { r[k] } else { 0 })
            };
            (finish(&acc[0]), finish(&acc[1]))
        }

        #[cfg(any(test, not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512vbmi", target_feature = "gfni"))))]
        pub fn reduce_row<F: Ext<W>, const W: usize>(field: &PowerField<F, W>, dst: &mut [u64], wide: &[u64], width: usize) {
            for j in (0..width).step_by(STEP) {
                let w: [V; 4] = std::array::from_fn(|k| if k <= W { V::load(wide, k * width + j) } else { V::zero() });
                let [even, odd] = [0, 1].map(|half| {
                    let at = |x: V| if half == 0 { x } else { x.high() };
                    reduce_w1(field, &w.map(at))
                });
                store_w(dst, width, j, std::array::from_fn(|k| even[k].unpacklo(odd[k])));
            }
        }

        pub fn mul_row<F: Ext<W>, const W: usize>(field: &PowerField<F, W>, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
            for j in (0..width).step_by(STEP) {
                let (a, b, c) = (load_w::<W>(a, width, j), load_w::<W>(b, width, j), load_w::<W>(c, width, j));
                let product = reduce_pair(field, &partial(&a, &b));
                store_w(dst, width, j, xor_w(&c, &product));
            }
        }

        pub fn fold_row<F: Ext<W>, const W: usize>(
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
                let (l, h) = (load_w::<W>(lo, width, j), load_w::<W>(hi, width, j));
                let delta = xor_w(&l, &h);
                let folded = reduce_pair(field, &karatsuba(&delta, &sums(&delta), &challenge, &challenge_sums));
                store_w(dst, width, j, xor_w(&l, &folded));
            }
        }

        pub fn fold_quad<F: Ext<W>, const W: usize>(
            field: &PowerField<F, W>,
            dst: &mut [u64],
            rows: [&[u64]; 4],
            challenges: &[Element<W>; 3],
            width: usize,
        ) {
            let challenges: [[V; W]; 3] = challenges.map(|r| r.map(|x| V::splat(x)));
            for j in (0..width).step_by(STEP) {
                let [a, b, c, d] = rows.map(|row| load_w::<W>(row, width, j));
                let dx = xor_w(&a, &b);
                let dy = xor_w(&a, &c);
                let dxy = xor_w(&dx, &xor_w(&c, &d));
                let mut wide = [[V::zero(); 5]; 2];
                for (delta, r) in [dx, dy, dxy].iter().zip(&challenges) {
                    let product = partial(delta, r);
                    for half in 0..2 {
                        for k in 0..2 * W - 1 {
                            wide[half][k] = wide[half][k].xor(product[half][k]);
                        }
                    }
                }
                let folded = reduce_pair(field, &wide);
                store_w(dst, width, j, xor_w(&a, &folded));
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod neon {
    use core::arch::aarch64::*;

    use crate::lv::primitives::field::gf2_64::aarch64 as pm;

    // The field helpers are `unsafe fn`s that need `aes`, which this module's cfg enables.
    #[inline(always)]
    fn mul_lo(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        // SAFETY: `aes` is enabled at compile time.
        unsafe { pm::pmull_lo_asm(a, b) }
    }
    #[inline(always)]
    fn mul_hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        // SAFETY: `aes` is enabled at compile time.
        unsafe { pm::pmull_hi_asm(a, b) }
    }

    use crate::lv::primitives::{load_at, store_at};

    use super::*;

    /// Entries `j` and `j + 1` of a row, a lane each, by word.
    #[target_feature(enable = "neon,aes")]
    #[inline]
    fn load3(row: &[u64], width: usize, j: usize) -> [uint64x2_t; 3] {
        std::array::from_fn(|k| load_at(row, k * width + j))
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    fn xor3(a: &[uint64x2_t; 3], b: &[uint64x2_t; 3]) -> [uint64x2_t; 3] {
        std::array::from_fn(|k| veorq_u64(a[k], b[k]))
    }

    /// The products `a[i] * b[k]` of the listed word pairs, of each lane, as 128-bit sums by
    /// offset `i + k`.
    #[target_feature(enable = "neon,aes")]
    #[inline]
    fn partial<const N: usize>(
        a: &[uint64x2_t; 3],
        b: &[uint64x2_t; 3],
        terms: [(usize, usize); N],
    ) -> [[uint64x2_t; 5]; 2] {
        let mut out = [[vdupq_n_u64(0); 5]; 2];
        for (i, k) in terms {
            out[0][i + k] = veorq_u64(out[0][i + k], mul_lo(a[i], b[k]));
            out[1][i + k] = veorq_u64(out[1][i + k], mul_hi(a[i], b[k]));
        }
        out
    }

    const ALL: [(usize, usize); 9] = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)];

    /// Word `w` of each lane's product: the low half of its sum `w` and the high half of its
    /// sum `w - 1`.
    #[target_feature(enable = "neon,aes")]
    #[inline]
    fn word(sums: &[[uint64x2_t; 5]; 2], w: usize) -> uint64x2_t {
        let low = if w < 5 {
            vzip1q_u64(sums[0][w], sums[1][w])
        } else {
            vdupq_n_u64(0)
        };
        let high = if w > 0 {
            vzip2q_u64(sums[0][w - 1], sums[1][w - 1])
        } else {
            vdupq_n_u64(0)
        };
        veorq_u64(low, high)
    }

    /// Reduce two products, a lane each, given by their six words.
    #[target_feature(enable = "neon,aes")]
    #[inline]
    fn reduce(field: &PowerField, p: &[uint64x2_t; 6]) -> [uint64x2_t; 3] {
        let barrett: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(field.barrett[k]));
        let modulus: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(field.modulus[k]));
        let high = [p[3], p[4], p[5]];
        // The top three words of `high * barrett`, then the low three of `q * modulus`.
        let t = partial(&high, &barrett, [(0, 2), (1, 1), (2, 0), (1, 2), (2, 1), (2, 2)]);
        let q: [uint64x2_t; 3] = std::array::from_fn(|k| veorq_u64(high[k], word(&t, 3 + k)));
        let r = partial(&q, &modulus, [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0)]);
        std::array::from_fn(|k| veorq_u64(p[k], word(&r, k)))
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    fn store3(row: &mut [u64], width: usize, j: usize, value: &[uint64x2_t; 3]) {
        for (k, &v) in value.iter().enumerate() {
            store_at(row, k * width + j, v);
        }
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub fn weighted_dot(field: &PowerField, a: &[u64], b: &[u64], weights: &[u64], width: usize) -> [u64; 6] {
        let mut acc = [vdupq_n_u64(0); 5];
        for j in (0..width).step_by(2) {
            let p = partial(&load3(a, width, j), &load3(weights, width, j), ALL);
            let weighted = reduce(field, &std::array::from_fn(|w| word(&p, w)));
            let p = partial(&weighted, &load3(b, width, j), ALL);
            for k in 0..5 {
                acc[k] = veorq_u64(acc[k], veorq_u64(p[0][k], p[1][k]));
            }
        }
        let mut out = [0; 6];
        for (k, &sum) in acc.iter().enumerate() {
            out[k] ^= vgetq_lane_u64::<0>(sum);
            out[k + 1] ^= vgetq_lane_u64::<1>(sum);
        }
        out
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub fn dot_pair(a: [&[u64]; 2], b: [&[u64]; 2], width: usize) -> ([u64; 6], [u64; 6]) {
        let mut acc = [[vdupq_n_u64(0); 5]; 2];
        for j in (0..width).step_by(2) {
            let (a0, a1, b0, b1) = (
                load3(a[0], width, j),
                load3(a[1], width, j),
                load3(b[0], width, j),
                load3(b[1], width, j),
            );
            for (acc, p) in acc
                .iter_mut()
                .zip([partial(&a0, &b0, ALL), partial(&xor3(&a0, &a1), &xor3(&b0, &b1), ALL)])
            {
                for s in 0..5 {
                    acc[s] = veorq_u64(acc[s], veorq_u64(p[0][s], p[1][s]));
                }
            }
        }
        let finish = |acc: &[uint64x2_t; 5]| {
            let mut out = [0u64; 6];
            for (s, &sum) in acc.iter().enumerate() {
                out[s] ^= vgetq_lane_u64(sum, 0);
                out[s + 1] ^= vgetq_lane_u64(sum, 1);
            }
            out
        };
        (finish(&acc[0]), finish(&acc[1]))
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub fn reduce_row(field: &PowerField, dst: &mut [u64], wide: &[u64], width: usize) {
        let zero = vdupq_n_u64(0);
        for j in (0..width).step_by(2) {
            let w: [uint64x2_t; 4] = std::array::from_fn(|k| load_at(wide, k * width + j));
            store3(dst, width, j, &reduce(field, &[w[0], w[1], w[2], w[3], zero, zero]));
        }
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub fn mul_row(field: &PowerField, dst: &mut [u64], a: &[u64], b: &[u64], c: &[u64], width: usize) {
        for j in (0..width).step_by(2) {
            let sums = partial(&load3(a, width, j), &load3(b, width, j), ALL);
            let product = reduce(field, &std::array::from_fn(|w| word(&sums, w)));
            store3(dst, width, j, &xor3(&product, &load3(c, width, j)));
        }
    }

    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub fn fold_row(field: &PowerField, dst: &mut [u64], lo: &[u64], hi: &[u64], challenge: &Element, width: usize) {
        let challenge: [uint64x2_t; 3] = std::array::from_fn(|k| vdupq_n_u64(challenge[k]));
        for j in (0..width).step_by(2) {
            let l = load3(lo, width, j);
            let sums = partial(&xor3(&l, &load3(hi, width, j)), &challenge, ALL);
            let folded = reduce(field, &std::array::from_fn(|w| word(&sums, w)));
            store3(dst, width, j, &xor3(&l, &folded));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lv::primitives::test_rng::Rng;

    #[test]
    fn two_round_fold_matches_successive_folds() {
        let mut rng = Rng::new(45);
        let field = PowerField::new(rng.ext()).unwrap();
        for width in [7, 16, BITS] {
            let rows: [Vec<u64>; 4] = std::array::from_fn(|_| (0..3 * width).map(|_| rng.next_u64()).collect());
            let [x, y] = [rng.ext(), rng.ext()].map(|r| field.to_poly(r));
            let mut actual = vec![0; 3 * width];
            let mut expected = actual.clone();
            let mut low = actual.clone();
            let mut high = actual.clone();
            for input in [rows.each_ref().map(Vec::as_slice), [&rows[0][..]; 4]] {
                field.fold_row_portable(&mut low, input[0], input[1], &x, width);
                field.fold_row_portable(&mut high, input[2], input[3], &x, width);
                field.fold_row_portable(&mut expected, &low, &high, &y, width);
                field.fold_quad(&mut actual, input, &[x, y, field.mul(&x, &y)], width);
                assert_eq!(actual, expected, "width {width}");
            }
        }
    }

    #[test]
    fn chi_factors_match_separate_row_operations() {
        let mut rng = Rng::new(43);
        let field = PowerField::new(rng.ext()).unwrap();
        let rows: [Vec<u64>; 4] = std::array::from_fn(|_| (0..3 * BITS).map(|_| rng.next_u64()).collect());
        let kappa = std::array::from_fn(|_| rng.next_u64());
        let mut scratch = vec![0; 4 * FACTOR_ROW];
        for high in [&rows[1], &rows[0]] {
            let t = [rows[0].as_slice(), high.as_slice()];
            let expected = field.chi_dot_pair_by_lane(t, &rows[2], &rows[3], &kappa, &mut scratch);
            let actual = field.chi_dot_pair(t, &rows[2], &rows[3], &kappa, &mut scratch);
            // The kernels may leave the sums reduced to different degrees.
            assert_eq!(field.reduce(&actual.0), field.reduce(&expected.0));
            assert_eq!(field.reduce(&actual.1), field.reduce(&expected.1));
        }
    }

    #[test]
    fn arithmetic_matches_the_standard_basis() {
        let mut rng = Rng::new(41);
        let field = PowerField::new(rng.ext()).unwrap();
        let width = 16;
        let elements = |rng: &mut Rng| -> (Vec<F192>, Vec<u64>) {
            let values = rng.ext_vec(width);
            let mut row = vec![0u64; 3 * width];
            for (j, &v) in values.iter().enumerate() {
                set(&mut row, width, j, &field.to_poly(v));
            }
            (values, row)
        };
        let ((a0, ra0), (a1, ra1), (b0, rb0), (b1, rb1)) = (
            elements(&mut rng),
            elements(&mut rng),
            elements(&mut rng),
            elements(&mut rng),
        );
        assert_eq!(
            field.to_field(&field.mul(&get(&ra0, width, 3), &get(&rb0, width, 5))),
            a0[3] * b0[5]
        );

        let (zero, infinity) = field.dot_pair([&ra0, &ra1], [&rb0, &rb1], width);
        assert_eq!((zero, infinity), dot_pair_portable([&ra0, &ra1], [&rb0, &rb1], width));
        let expected = (0..width).map(|j| a0[j] * b0[j]).sum();
        assert_eq!(field.to_field(&field.reduce(&zero)), expected);
        let expected = (0..width).map(|j| (a0[j] + a1[j]) * (b0[j] + b1[j])).sum();
        assert_eq!(field.to_field(&field.reduce(&infinity)), expected);

        let weighted = field.weighted_dot(&ra0, &rb0, &ra1, width);
        assert_eq!(weighted, field.weighted_dot_portable(&ra0, &rb0, &ra1, width));
        let expected = (0..width).fold(F192::ZERO, |acc, j| acc + a0[j] * b0[j] * a1[j]);
        assert_eq!(field.to_field(&field.reduce(&weighted)), expected);

        let challenge = rng.ext();
        let (mut fast, mut slow) = (vec![0u64; 3 * width], vec![0u64; 3 * width]);
        field.fold_row(&mut fast, &ra0, &ra1, &field.to_poly(challenge), width);
        field.fold_row_portable(&mut slow, &ra0, &ra1, &field.to_poly(challenge), width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(
                field.to_field(&get(&fast, width, j)),
                crate::lv::primitives::multilinear::interp(a0[j], a1[j], challenge)
            );
        }
        let wide: Vec<u64> = (0..4 * width).map(|_| rng.next_u64()).collect();
        field.reduce_row(&mut fast, &wide, width);
        field.reduce_row_portable(&mut slow, &wide, width);
        assert_eq!(fast, slow);
        field.mul_row(&mut fast, &ra0, &rb0, &rb1, width);
        field.mul_row_portable(&mut slow, &ra0, &rb0, &rb1, width);
        assert_eq!(fast, slow);
        for j in 0..width {
            assert_eq!(field.to_field(&get(&fast, width, j)), a0[j] * b0[j] + b1[j]);
        }
    }
}
