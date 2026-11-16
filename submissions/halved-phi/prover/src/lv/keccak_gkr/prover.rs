// Vendored from leanVM 0b850750 `crates/keccak_gkr/src/prover.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The layer prover.
//!
//! One layer makes three passes over the bits of the states it reduces to:
//!
//! 1. the product polynomial, before its evaluation point `s` is known;
//! 2. the first sumcheck rounds, over the packs of half a block, as sums of bit-level products;
//! 3. one field element per half block and position, for the rounds that remain.
//!
//! From `s` on, everything stays in the power basis of `s` ([`crate::lv::keccak_gkr::power`]) until the tables
//! are down to one row.
//!
//! lvm2 E2-K: generic over the field of the weights and challenges ([`Ext`] of `W` words): `F192` (E3, today's
//! bytes) or `F128` (E2). A weight is `W` words throughout: `8 W` digit rows, `W` partial products per slot, rows of
//! `W` words per position. This tree serves v2 and v4p, so its GFNI arms (dead since PORT-13) are dropped.

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::gf2_64::mul_wide;
use crate::lv::primitives::field::{Ext, F192, F192x8, Prod8, Unreduced};

use crate::lv::keccak_gkr::basis::{PolyEval, carry};
use crate::lv::keccak_gkr::keccak::{BITS, LOCAL_VARS, along, linear_transpose, row_positions};
use crate::lv::keccak_gkr::kernels::{GROUP, MIXED, PACKS, SKIP, SkipBlock, TERNARY, embed, mixed_points, products, slot};
use crate::lv::keccak_gkr::power::{Element, PowerField, get, set};
use crate::lv::keccak_gkr::protocol::{Claim, chi_weights, mu_at, tag};
use crate::lv::keccak_gkr::rmfe::PROD_BITS;
use crate::lv::keccak_gkr::witness::{Shape, Witness, transpose64, words};

/// The pattern index of a binary assignment.
fn ternary(b: usize) -> usize {
    (0..SKIP).fold(0, |acc, k| acc + (b >> k & 1) * 3usize.pow(k as u32))
}

/// The bits of a digit a weight splits into (`8 W` digits).
const DIGIT_BITS: usize = 8;

/// `acc += a[..n] * b`, on binary polynomials: the first `n` words of `a`.
#[inline(always)]
fn add_mul_n<const A: usize, const W: usize, const N: usize>(acc: &mut [u64; N], a: &[u64; A], n: usize, b: &[u64; W]) {
    for (i, &a) in a[..n].iter().enumerate() {
        for (k, &b) in b.iter().enumerate() {
            let p = mul_wide(a, b);
            acc[i + k] ^= p as u64;
            acc[i + k + 1] ^= (p >> 64) as u64;
        }
    }
}

/// `lo + t (lo + hi)` over pairs, low variable first.
fn fold<F: Ext<W>, const W: usize>(table: &[F], t: F) -> Vec<F> {
    table.chunks_exact(2).map(|p| p[0] + t * (p[0] + p[1])).collect()
}

/// The bits of a block position's products, 48 to each pack.
pub(crate) const PAYLOAD_BITS: usize = 48 * PACKS;
/// The packs of a part of a block position, and the words of their products: with AVX-512 the
/// whole position, three registers; with AVX2 half, three registers; elsewhere a quarter, a
/// block's worth of which stays in cache.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
const PART: usize = PACKS;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
const PART: usize = PACKS / 2;
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
const PART: usize = 8;
const PART_WORDS: usize = 48 * PART / 64;
// `pack` reads four products to three words and `add` XORs whole vectors, so `PART` divides by four
// and `PART_WORDS` by each arm's lane count. A `PART` that broke either would drop products or store
// past the array rather than fail to build.
const _: () = assert!(PART.is_multiple_of(4));
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
const _: () = assert!(PART_WORDS.is_multiple_of(8));
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
const _: () = assert!(PART_WORDS.is_multiple_of(4));
#[cfg(target_arch = "aarch64")]
const _: () = assert!(PART_WORDS.is_multiple_of(2));

/// The products of a part of a block position's packs, 48 bits each, grouped while every digit
/// of the weights groups the block's positions.
#[derive(Clone, Copy)]
#[cfg_attr(all(target_arch = "x86_64", target_feature = "avx512f"), repr(C, align(64)))]
#[cfg_attr(not(all(target_arch = "x86_64", target_feature = "avx512f")), repr(C, align(16)))]
struct Part([u64; PART_WORDS]);

impl Part {
    const ZERO: Self = Self([0; PART_WORDS]);

    /// Product `q` at bits `48 * q ..`: four products to three words.
    #[inline(always)]
    fn pack(products: &[u64; PART]) -> Self {
        let mut out = [0u64; PART_WORDS];
        for (out, p) in out.as_chunks_mut::<3>().0.iter_mut().zip(products.as_chunks::<4>().0) {
            *out = [p[0] | p[1] << 48, p[1] >> 16 | p[2] << 32, p[2] >> 32 | p[3] << 16];
        }
        Self(out)
    }

    #[inline(always)]
    fn add(&mut self, other: &Self) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        // SAFETY: both parts are three registers, aligned to 64, and AVX-512 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (
                self.0.as_mut_ptr().cast::<__m512i>(),
                other.0.as_ptr().cast::<__m512i>(),
            );
            for i in 0..PART_WORDS / 8 {
                let x = _mm512_xor_si512(
                    _mm512_load_si512(dst.add(i).cast()),
                    _mm512_load_si512(src.add(i).cast()),
                );
                _mm512_store_si512(dst.add(i).cast(), x);
            }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        // SAFETY: both parts are three registers, and AVX2 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..PART_WORDS).step_by(4) {
                let (d, s) = (dst.add(i).cast::<__m256i>(), src.add(i).cast::<__m256i>());
                _mm256_storeu_si256(d, _mm256_xor_si256(_mm256_loadu_si256(d), _mm256_loadu_si256(s)));
            }
        }
        // Left to itself, the compiler XORs the words in general registers.
        #[cfg(target_arch = "aarch64")]
        // SAFETY: both parts are six words, and aarch64 always has NEON.
        unsafe {
            use core::arch::aarch64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..PART_WORDS).step_by(2) {
                vst1q_u64(dst.add(i), veorq_u64(vld1q_u64(dst.add(i)), vld1q_u64(src.add(i))));
            }
        }
        #[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
        for (x, y) in self.0.iter_mut().zip(&other.0) {
            *x ^= y;
        }
    }
}

/// Digit `d` of a weight.
#[inline(always)]
fn digit<F: Ext<W>, const W: usize>(weight: F, d: usize) -> usize {
    let w = weight.to_limbs();
    (w[d / 8] >> (DIGIT_BITS * (d % 8))) as usize & ((1 << DIGIT_BITS) - 1)
}

/// The positions grouped by each digit of their weight: those whose digit `d` is `v` are
/// `order[d][starts[d][v]..starts[d][v + 1]]`.
struct Groups {
    order: Vec<[u16; BITS]>,
    starts: Vec<[u16; (1 << DIGIT_BITS) + 1]>,
}

impl Groups {
    fn new<F: Ext<W>, const W: usize>(weights: &[F]) -> Self {
        let digits = 64 * W / DIGIT_BITS;
        let mut order = vec![[0u16; BITS]; digits];
        let mut starts = vec![[0u16; (1 << DIGIT_BITS) + 1]; digits];
        for (d, (order, starts)) in order.iter_mut().zip(&mut starts).enumerate() {
            let digits: Vec<usize> = weights[..BITS].iter().map(|&w| digit::<F, W>(w, d)).collect();
            for &v in &digits {
                starts[v + 1] += 1;
            }
            for v in 0..1 << DIGIT_BITS {
                starts[v + 1] += starts[v];
            }
            let mut next = *starts;
            for (p, &v) in digits.iter().enumerate() {
                order[next[v] as usize] = p as u16;
                next[v] += 1;
            }
        }
        Self { order, starts }
    }

    /// `sum over positions of weight[j] (x) payloads[j]` into `rows`: row `DIGIT_BITS * d + i`
    /// sums the payloads whose weight has that bit set. Each group is summed in registers, so
    /// the payloads are only read.
    fn add_rows(&self, payloads: &[Part; BITS], rows: &mut [Part], sums: &mut [Part; 1 << DIGIT_BITS]) {
        for (rows, (order, starts)) in rows
            .as_chunks_mut::<DIGIT_BITS>()
            .0
            .iter_mut()
            .zip(self.order.iter().zip(&self.starts))
        {
            for (v, sum) in sums.iter_mut().enumerate() {
                let mut acc = Part::ZERO;
                for &p in &order[starts[v] as usize..starts[v + 1] as usize] {
                    // SAFETY: `order` holds positions.
                    acc.add(unsafe { payloads.get_unchecked(p as usize) });
                }
                *sum = acc;
            }
            // Bit `i` of the digit: the sums whose value has it, then fold it away.
            for (i, row) in rows.iter_mut().enumerate().rev() {
                let (low, high) = sums[..2 << i].split_at_mut(1 << i);
                let mut acc = Part::ZERO;
                for (low, high) in low.iter_mut().zip(&*high) {
                    acc.add(high);
                    low.add(high);
                }
                *row = acc;
            }
        }
    }
}

struct Layer<'a> {
    witness: &'a Witness,
    /// The round whose `chi` each segment's claim is on.
    rounds: Vec<usize>,
}

/// A row of a table in the power basis: `W` words per position, laid out by word.
const fn row_len<const W: usize>() -> usize {
    W * BITS
}

impl Layer<'_> {
    /// The blocks a segment's tasks walk: those written, then the padding block once, standing
    /// for every block after them.
    fn held(&self) -> usize {
        let written = self.witness.written();
        written + usize::from(written < self.witness.shape.n_blocks())
    }

    /// Task `held * segment + g`, as `(segment, g, block)`.
    fn block(&self, task: usize) -> (usize, usize, &[u64]) {
        let (segment, g) = (task / self.held(), task % self.held());
        (segment, g, self.witness.layer(self.rounds[segment], g))
    }

    fn n_tasks(&self) -> usize {
        self.rounds.len() * self.held()
    }

    /// Each task's weight in `eq`, a table over the blocks then the segment: the padding block's
    /// is the sum over the blocks it stands for.
    fn task_weights<F: Ext<W>, const W: usize>(&self, eq: &[F]) -> Vec<F> {
        let nb = self.witness.shape.n_blocks();
        (0..self.n_tasks())
            .map(|task| {
                let (segment, g) = (task / self.held(), task % self.held());
                let eq = &eq[nb * segment..][..nb];
                if g < self.witness.written() {
                    eq[g]
                } else {
                    eq[g..].iter().sum()
                }
            })
            .collect()
    }

    /// Per pack `q` of a block, the coefficients of
    /// `sum over blocks and positions of eq(point[5..], block) * weights[j] * product(q, j)`,
    /// where the product is `ones * u[j] + (ones + u[j + 1]) * u[j + 2]` on embeddings, the
    /// unprojected `chi`.
    ///
    /// Nothing here knows where the polynomials will be evaluated, so each product meets its
    /// weight bit by bit. The position weights are the same in every block, so a block's sum
    /// over positions is taken bit by bit, by digit buckets ([`Groups`]); only that sum meets
    /// the block's weight, as field elements.
    fn pack_products<F: Ext<W>, const W: usize>(&self, claim: &Claim<F>) -> Vec<[F; PROD_BITS]> {
        self.pack_products_buckets::<F, W>(claim)
    }

    /// [`Self::pack_products`] by digit buckets: the block's positions grouped by each digit of
    /// their weight ([`Groups`]), a part of the packs at a time.
    fn pack_products_buckets<F: Ext<W>, const W: usize>(&self, claim: &Claim<F>) -> Vec<[F; PROD_BITS]> {
        let weights = self.task_weights::<F, W>(&F::eq_table(&claim.point[SKIP + 1..]));
        let groups = Groups::new::<F, W>(&claim.weights);
        let sums = crate::lv::parallel::map_reduce_with_state(
            self.n_tasks(),
            || {
                (
                    vec![[Part::ZERO; BITS]; PACKS / PART],
                    vec![vec![Part::ZERO; 64 * W]; PACKS / PART],
                    Box::new([Part::ZERO; 1 << DIGIT_BITS]),
                )
            },
            || vec![<F::Unreduced as Unreduced<F>>::ZERO; PAYLOAD_BITS],
            |(payloads, rows, digit_sums), sums, task| {
                let (_, _, block) = self.block(task);
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        let e: [[u32; PACKS]; 5] = std::array::from_fn(|x| embed(words(block, js[x])));
                        for x in 0..5 {
                            let p = products(&e[x], &e[(x + 1) % 5], &e[(x + 2) % 5]);
                            for (q, part) in payloads.iter_mut().enumerate() {
                                part[js[x]] = Part::pack(p[PART * q..][..PART].try_into().unwrap());
                            }
                        }
                    }
                }
                for (payloads, rows) in payloads.iter().zip(rows.iter_mut()) {
                    groups.add_rows(payloads, rows, digit_sums);
                }
                // Row `r` holds bit `r` of each payload bit's weighted sum: transposed, they are
                // field elements, which the block's weight multiplies.
                let mut columns = [[0u64; 64]; W];
                for m in 0..PAYLOAD_BITS / 64 {
                    let (q, w) = (m / PART_WORDS, m % PART_WORDS);
                    for (k, column) in columns.iter_mut().enumerate() {
                        for (b, word) in column.iter_mut().enumerate() {
                            *word = rows[q][64 * k + b].0[w];
                        }
                        transpose64(column);
                    }
                    for (t, sum) in sums[64 * m..][..64].iter_mut().enumerate() {
                        *sum ^= weights[task].mul_unreduced(F::from_limbs(std::array::from_fn(|k| columns[k][t])));
                    }
                }
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    *x ^= y;
                }
                a
            },
        );
        (0..PACKS)
            .map(|q| std::array::from_fn(|c| sums[48 * q + c].reduce()))
            .collect()
    }

    /// The layer's summand at `s`, extended over the packs of a group and summed over the groups:
    /// for every point `p` of `{0, 1, infinity}^SKIP`,
    /// `sum over groups of eq(point[SKIP..], group) * Q(p, group)`.
    ///
    /// A point at infinity in some variable keeps only the product `u[j + 1] * u[j + 2]`, summed
    /// here. A binary one is a pack, whose sum `binary` already holds. The packs of the padding
    /// block are all equal, so their extension vanishes there.
    /// lvm2 R9-KG: `weights` are the claim's weights in the power basis, converted once a layer.
    fn skip_sums<F: Ext<W>, const W: usize>(
        &self,
        claim: &Claim<F>,
        field: &PowerField<F, W>,
        weights: &[Element<W>],
        binary: &[F; GROUP],
    ) -> Vec<F> {
        let groups: Vec<Element<W>> = F::eq_table(&claim.point[SKIP..])
            .iter()
            .map(|&e| field.to_poly(e))
            .collect();
        let (nb, written) = (self.witness.shape.n_blocks(), self.witness.written());
        let mixed = crate::lv::parallel::map_reduce_with_state(
            self.rounds.len() * written,
            SkipBlock::<W>::new,
            || vec![[0u64; 7]; MIXED],
            |skip, total, task| {
                let (segment, g) = (task / written, task % written);
                let (row, block) = (g + nb * segment, self.witness.layer(self.rounds[segment], g));
                skip.run(block, &weights);
                for half in 0..2 {
                    for (i, total) in total.iter_mut().enumerate() {
                        let sum: [u64; 4] = carry(&skip.get(slot(half, i)));
                        add_mul_n(total, &sum, W + 1, &groups[2 * row + half]);
                    }
                }
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    for (x, y) in x.iter_mut().zip(y) {
                        *x ^= y;
                    }
                }
                a
            },
        );
        let eval = field.eval();
        let mut sums = vec![F::ZERO; TERNARY];
        for (slot, p) in mixed_points().into_iter().enumerate() {
            sums[p] = eval.eval(&mixed[slot]);
        }
        for (q, &value) in binary.iter().enumerate() {
            sums[ternary(q)] = value;
        }
        sums
    }

    /// The table the remaining rounds fold, a row per group: `T[j]`, the value at `s` of position
    /// `j`'s embeddings, folded over the group's packs at `challenges`. A block's two groups are
    /// the first of those rounds' pairs, so its round values are summed while the rows are at hand.
    /// The padding block's groups are one row, its segment's entry of `pads`.
    fn table<F: Ext<W>, const W: usize>(
        &self,
        round: &Round<F, W>,
        challenges: &[F],
        eq: &[F],
        layout: Rows,
        table: &mut [u64],
        pads: &mut [u64],
    ) -> (F, F) {
        const { assert!(W <= 3) };
        let row = row_len::<W>();
        let field = round.field;
        let fold: Vec<Element<W>> = F::eq_table(challenges).iter().map(|&e| field.to_poly(e)).collect();
        let fold: [[u64; GROUP]; W] = std::array::from_fn(|k| std::array::from_fn(|q| fold[q][k]));
        let weights = self.task_weights::<F, W>(eq);
        // Rows of segments that do not exist are zero, and so is their product.
        table[self.rounds.len() * layout.live * row..layout.len() * row].fill(0);
        pads[self.rounds.len() * row..].fill(0);
        let (ptr, pads) = (
            crate::lv::parallel::SendPtr(table.as_mut_ptr()),
            crate::lv::parallel::SendPtr(pads.as_mut_ptr()),
        );
        let sums = crate::lv::parallel::map_reduce_with_state(
            self.n_tasks(),
            || (vec![0u64; 4 * row], vec![0u64; 2 * (W + 1) * BITS], vec![0u64; 2 * row]),
            RoundSums::default,
            |(scratch, wide, rows), sums, task| {
                let (segment, g, block) = self.block(task);
                // SAFETY: each task owns its rows: a written block's two, or its segment's padding row.
                let out = unsafe {
                    if 2 * g < layout.live {
                        ptr.slice((layout.live * segment + 2 * g) * row, 2 * row)
                    } else {
                        pads.slice(segment * row, row)
                    }
                };
                let rows = &mut rows[..out.len()];
                let halves = rows.len() / row;
                // Both groups' unreduced sums, `W + 1` words each and laid out by word, then reduced.
                for j in 0..BITS {
                    let sums = crate::lv::keccak_gkr::kernels::fold_groups(&embed(words(block, j)), &fold);
                    for (wide, sum) in wide.chunks_exact_mut((W + 1) * BITS).take(halves).zip(&sums) {
                        let sum: [u64; 4] = carry(sum);
                        for (k, &word) in sum[..W + 1].iter().enumerate() {
                            wide[k * BITS + j] = word;
                        }
                    }
                }
                for (t, wide) in rows.chunks_exact_mut(row).zip(wide.chunks_exact((W + 1) * BITS)) {
                    field.reduce_row(t, wide, BITS);
                }
                round.add_pair(sums, scratch, &rows[..row], &rows[rows.len() - row..], weights[task]);
                // Built in cache for the round values, then published: the next round reads them.
                crate::lv::primitives::stream::Stream::new().copy(out, rows);
            },
            RoundSums::merge,
        );
        round.finish(&sums)
    }
}

/// The sums a round accumulates, unreduced: its values at `0` and at infinity.
#[derive(Clone, Copy, Default)]
struct RoundSums([u64; 9], [u64; 9]);

impl RoundSums {
    fn merge(mut self, other: Self) -> Self {
        for i in 0..9 {
            self.0[i] ^= other.0[i];
            self.1[i] ^= other.1[i];
        }
        self
    }
}

/// What a round needs of the claim, by word as a table row is: the position weights, and each
/// position's constant `kappa * weights[j + 2]`.
struct Round<'a, F, const W: usize> {
    field: &'a PowerField<F, W>,
    kappa: Element<W>,
    weights: Vec<u64>,
    constant: Vec<u64>,
}

impl<'a, F: Ext<W>, const W: usize> Round<'a, F, W> {
    const ROW: usize = row_len::<W>();

    /// lvm2 R9-KG: `polys` are the claim's weights in the power basis, converted once for `Skip`
    /// and here.
    fn new(field: &'a PowerField<F, W>, claim: &Claim<F>, polys: &[Element<W>], kappa: F) -> Self {
        let (mut weights, mut constant) = (vec![0u64; Self::ROW], vec![0u64; Self::ROW]);
        let constants: Vec<Element<W>> = (0..BITS).map(|j| field.to_poly(kappa * claim.weights[along(j, 2)])).collect();
        for j in 0..BITS {
            set(&mut weights, BITS, j, &polys[j]);
            set(&mut constant, BITS, j, &constants[j]);
        }
        Self {
            field,
            kappa: field.to_poly(kappa),
            weights,
            constant,
        }
    }

    /// `B[j] = weights[j] * (kappa + T[j + 1]) + kappa * weights[j + 2]` and `T[j + 2]`, for a
    /// row `T`.
    fn factors(&self, t: &[u64], b: &mut [u64], shifted: &mut [u64]) {
        // `T[j + 1] + kappa`, then `T[j + 2]`: a lane is 64 positions, five lanes to a row.
        for k in 0..W {
            let (src, next) = (&t[k * BITS..][..BITS], &mut shifted[k * BITS..][..BITS]);
            for lane in 0..BITS / 64 {
                let at = along(64 * lane, 1);
                for z in 0..64 {
                    next[64 * lane + z] = src[at + z] ^ self.kappa[k];
                }
            }
        }
        self.field.mul_row(b, &self.weights, shifted, &self.constant, BITS);
        for k in 0..W {
            let (src, dst) = (&t[k * BITS..][..BITS], &mut shifted[k * BITS..][..BITS]);
            for lane in 0..BITS / 64 {
                dst[64 * lane..][..64].copy_from_slice(&src[along(64 * lane, 2)..][..64]);
            }
        }
    }

    /// Add one pair of rows to a round's sums: the values at `0` and at infinity of
    /// `sum over positions of B[j] * T[j + 2]`, weighted by `eq`.
    fn add_pair(&self, sums: &mut RoundSums, scratch: &mut [u64], low: &[u64], high: &[u64], eq: F) {
        let row = Self::ROW;
        let (b, shifted) = scratch.split_at_mut(2 * row);
        for (half, t) in [low, high].into_iter().enumerate() {
            self.factors(t, &mut b[half * row..][..row], &mut shifted[half * row..][..row]);
        }
        let (zero, infinity) = self
            .field
            .dot_pair([&b[..row], &b[row..]], [&shifted[..row], &shifted[row..]], BITS);
        let weight = self.field.to_poly(eq);
        add_mul_n(&mut sums.0, &zero, 2 * W, &weight);
        add_mul_n(&mut sums.1, &infinity, 2 * W, &weight);
    }

    fn finish(&self, sums: &RoundSums) -> (F, F) {
        (self.field.eval().eval(&sums.0), self.field.eval().eval(&sums.1))
    }

    /// Fold the rows of `src`, laid out as `from`, in pairs into `dst`, and sum the next round's
    /// values over the pairs of what was just written, weighted by `eq`.
    fn fold(
        &self,
        src: &[u64],
        from: Rows,
        dst: &mut [u64],
        pads: &[u64],
        challenge: &Element<W>,
        eq: &[F],
    ) -> (F, F) {
        let row = Self::ROW;
        let to = from.next();
        let ptr = crate::lv::parallel::SendPtr(dst.as_mut_ptr());
        let fold = |out: &mut [u64], segment: usize, r: usize| {
            let (low, high) = if from.m == 1 {
                (
                    from.row(src, pads, 2 * segment, 0),
                    from.row(src, pads, 2 * segment + 1, 0),
                )
            } else {
                (
                    from.row(src, pads, segment, 2 * r),
                    from.row(src, pads, segment, 2 * r + 1),
                )
            };
            self.field.fold_row(out, low, high, challenge, BITS);
        };
        if to.m == 1 {
            // A row per segment, few enough to fold in place.
            for (segment, out) in dst[..to.len() * row].chunks_exact_mut(row).enumerate() {
                fold(out, segment, 0);
            }
            let mut sums = RoundSums::default();
            let mut scratch = vec![0u64; 4 * row];
            for (pair, &eq) in dst[..to.len() * row].chunks_exact(2 * row).zip(eq) {
                self.add_pair(&mut sums, &mut scratch, &pair[..row], &pair[row..], eq);
            }
            return self.finish(&sums);
        }
        // A task per pair of rows written, the second of a ragged one being the padding row.
        let (pairs, half) = (to.live.div_ceil(2), to.m / 2);
        let mut sums = crate::lv::parallel::map_reduce_with_state(
            to.segments * pairs,
            || (vec![0u64; 4 * row], vec![0u64; 2 * row]),
            RoundSums::default,
            |(scratch, rows), sums, task| {
                let (segment, t) = (task / pairs, task % pairs);
                let n = (to.live - 2 * t).min(2);
                let rows = &mut rows[..n * row];
                for (i, r) in rows.chunks_exact_mut(row).enumerate() {
                    fold(r, segment, 2 * t + i);
                }
                let high = if n == 2 {
                    &rows[row..]
                } else {
                    &pads[segment * row..][..row]
                };
                self.add_pair(sums, scratch, &rows[..row], high, eq[half * segment + t]);
                // SAFETY: each task owns its rows of `dst`.
                let out = unsafe { ptr.slice((to.live * segment + 2 * t) * row, n * row) };
                // Built in cache for the round values, then published: the next round reads them.
                crate::lv::primitives::stream::Stream::new().copy(out, rows);
            },
            RoundSums::merge,
        );
        self.add_padding(&mut sums, to, pads, eq);
        self.finish(&sums)
    }

    /// Add the pairs of two padding rows of a table laid out as `layout`, weighted by `eq`: each
    /// segment's padding row, once, at the sum of their weights.
    fn add_padding(&self, sums: &mut RoundSums, layout: Rows, pads: &[u64], eq: &[F]) {
        let (first, half) = (layout.live.div_ceil(2), layout.m / 2);
        if first == half {
            return;
        }
        let mut scratch = vec![0u64; 4 * Self::ROW];
        for (pad, eq) in pads.chunks_exact(Self::ROW).zip(eq.chunks_exact(half)) {
            self.add_pair(sums, &mut scratch, pad, pad, eq[first..].iter().sum());
        }
    }
}

/// The rows of the table the tail folds: per segment, the first `live` of `m`, then, if there are
/// fewer, the padding row every later one equals, kept apart. Once `m` is one, a row per segment.
#[derive(Clone, Copy)]
struct Rows {
    m: usize,
    live: usize,
    segments: usize,
    /// Words a row (`W * BITS`).
    row: usize,
}

impl Rows {
    fn len(&self) -> usize {
        self.segments * self.live
    }

    /// The layout once the next variable is bound: the group, the block's, then the segment's.
    fn next(&self) -> Self {
        match self.m {
            1 => Self {
                segments: self.segments / 2,
                ..*self
            },
            // The fold writes every segment's row, a padding one included.
            2 => Self { m: 1, live: 1, ..*self },
            m => Self {
                m: m / 2,
                live: self.live.div_ceil(2),
                ..*self
            },
        }
    }

    fn row<'t>(&self, table: &'t [u64], pads: &'t [u64], segment: usize, r: usize) -> &'t [u64] {
        let row = self.row;
        if r < self.live {
            &table[(self.live * segment + r) * row..][..row]
        } else {
            &pads[segment * row..][..row]
        }
    }
}

/// A round of the sumcheck over bit positions, on small tables in the standard basis: the
/// coefficients of `sum_j w (kappa t0 + (kappa + t1) t2)` in the variable being bound.
fn local_round<F: Ext<W>, const W: usize>(w: &[F], t: &[Vec<F>; 3], kappa: F) -> [F; 4] {
    let mut h = [F::ZERO; 4];
    for i in 0..w.len() / 2 {
        let line = |v: &[F]| (v[2 * i], v[2 * i] + v[2 * i + 1]);
        let (w, t0, t1, t2) = (line(w), line(&t[0]), line(&t[1]), line(&t[2]));
        let u = (kappa + t1.0, t1.1);
        let a = [
            kappa * t0.0 + u.0 * t2.0,
            kappa * t0.1 + u.0 * t2.1 + u.1 * t2.0,
            u.1 * t2.1,
        ];
        h[0] += w.0 * a[0];
        h[1] += w.0 * a[1] + w.1 * a[0];
        h[2] += w.0 * a[2] + w.1 * a[1];
        h[3] += w.1 * a[2];
    }
    h
}

/// The table the rounds after the bit-level ones fold, and the half they fold it into: reused
/// from layer to layer.
pub struct Scratch<const W: usize> {
    table: Vec<u64>,
    /// Each segment's padding row.
    pads: Vec<u64>,
}

impl<const W: usize> Scratch<W> {
    pub fn new(shape: Shape) -> Self {
        let (rows, row) = (1usize << (shape.y_vars() - SKIP), row_len::<W>());
        // SAFETY: every pass writes the rows it reads.
        let table = unsafe { crate::lv::primitives::uninit_vec(rows * row + rows * row / 2) };
        let pads = vec![0u64; row << shape.seg_log()];
        Self { table, pads }
    }
}

/// Prove one layer, as `crates/verifier`'s `keccak.rs` checks it: a claim on the states `step`
/// layers below the outputs becomes one on the states a layer further down.
pub fn prove_layer<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    witness: &Witness,
    scratch: &mut Scratch<W>,
    step: usize,
    claim: &Claim<F>,
) -> Claim<F> {
    let shape = witness.shape;
    let row = row_len::<W>();
    let layer = Layer {
        witness,
        rounds: (0..shape.segments())
            .map(|segment| shape.round(segment, step))
            .collect(),
    };

    let per_pack =
        crate::lv::tracing::info_span!(tag::<W>("Product", "Product/E2")).in_scope(|| layer.pack_products::<F, W>(claim));
    let pack_weights = F::eq_table(&claim.point[..SKIP + 1]);
    let product: [F; PROD_BITS] =
        std::array::from_fn(|c| (0..PACKS).map(|q| pack_weights[q] * per_pack[q][c]).sum());
    ps.add_ext(&product);
    let s = ps.challenge::<F, W>(Grp::C46);
    let kappa = mu_at::<F, W>(s).iter().sum();
    let mut value = F::poly_eval(&product, s);
    let field = crate::lv::tracing::info_span!("Field")
        .in_scope(|| PowerField::<F, W>::new(s).expect("the challenge lies in no proper subfield"));
    // lvm2 R9-KG: the weights in the power basis, once for `Skip` and the round tables.
    let polys: Vec<Element<W>> = claim.weights.iter().map(|&w| field.to_poly(w)).collect();

    // The packs of a group, from sums of bit-level products. A pack's own sum is its product
    // polynomial at `s`, over both groups of the block.
    let binary: [F; GROUP] = std::array::from_fn(|q| {
        let half = claim.point[SKIP];
        (F::ONE + half) * F::poly_eval(&per_pack[q], s) + half * F::poly_eval(&per_pack[GROUP + q], s)
    });
    let mut sums = crate::lv::tracing::info_span!(tag::<W>("Skip", "Skip/E2"))
        .in_scope(|| layer.skip_sums(claim, &field, &polys, &binary));
    let mut scale = F::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for i in 0..SKIP {
        let later = F::eq_table(&claim.point[i + 1..SKIP]);
        let mut h = [F::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, h) in h.iter_mut().enumerate() {
                *h += eq * sums[d + 3 * ternary(b)];
            }
        }
        let coeffs = [scale * h[0], scale * (h[0] + h[1] + h[2]), scale * h[2]];
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        sums = sums
            .as_chunks::<3>()
            .0
            .iter()
            .map(|v| v[0] + challenge * (v[0] + v[1]) + (challenge.square() + challenge) * v[2])
            .collect();
    }

    // The groups, blocks and segments, on a table in the power basis. Each pass over it writes
    // the rows of one round and sums that round's values over them.
    let round = crate::lv::tracing::info_span!("RoundNew").in_scope(|| Round::new(&field, claim, &polys, kappa));
    let mut layout = Rows {
        m: 2 * shape.n_blocks(),
        live: 2 * witness.written(),
        segments: 1 << shape.seg_log(),
        row,
    };
    let (mut src, mut dst) = scratch.table.split_at_mut(layout.m * layout.segments * row);
    let pads = &mut scratch.pads;
    let mut values = crate::lv::tracing::info_span!(tag::<W>("Tables", "Tables/E2")).in_scope(|| {
        let eq = F::eq_table(&claim.point[SKIP + 1..]);
        layer.table(&round, &point, &eq, layout, src, pads)
    });
    let tail = crate::lv::tracing::info_span!(tag::<W>("Tail", "Tail/E2")).entered();
    for i in SKIP..claim.point.len() {
        let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        let later = F::eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
        values = round.fold(src, layout, dst, pads, &field.to_poly(challenge), &later);
        layout = layout.next();
        (src, dst) = (dst, src);
    }
    let table = &src[..row];
    drop(tail);

    // The bit positions, in the standard basis.
    let local_span = crate::lv::tracing::info_span!("Local").entered();
    let t0: Vec<F> = (0..BITS).map(|j| field.to_field(&get(table, BITS, j))).collect();
    let shift = |k: usize| -> Vec<F> { (0..BITS).map(|j| t0[along(j, k)]).collect() };
    let (t1, t2) = (shift(1), shift(2));
    let (local, t) = local_rounds(ps, claim.weights.clone(), [t0, t1, t2], kappa, scale);
    ps.add_ext(&t);
    let beta = ps.challenge::<F, W>(Grp::C2);
    let out = Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu: mu_at::<F, W>(s),
        point,
        weights: linear_transpose(&chi_weights(&F::eq_table(&local), beta)),
    };
    drop(local_span);
    out
}

/// `v` as `F192` values when `F` is `F192` (E3), for the eight-wide arm of [`local_rounds`].
#[inline(always)]
fn as_e3<F: Ext<W>, const W: usize>(v: &[F]) -> Option<&[F192]> {
    (std::any::TypeId::of::<F>() == std::any::TypeId::of::<F192>())
        // SAFETY: `F` is `F192`, so the slice's type is unchanged.
        .then(|| unsafe { std::slice::from_raw_parts(v.as_ptr().cast::<F192>(), v.len()) })
}

/// `x` as an `F192` when `F` is `F192` (E3).
#[inline(always)]
fn to_e3<F: Ext<W>, const W: usize>(x: F) -> F192 {
    debug_assert!(std::any::TypeId::of::<F>() == std::any::TypeId::of::<F192>());
    F192::from_limbs(std::array::from_fn(|k| if k < W { x.to_limbs()[k] } else { 0 }))
}

/// An `F192` back as `F` when `F` is `F192` (E3).
#[inline(always)]
fn from_e3<F: Ext<W>, const W: usize>(x: F192) -> F {
    let l = x.to_limbs();
    F::from_limbs(std::array::from_fn(|k| l[k]))
}

/// lvm2 R9-KG: the `LOCAL_VARS` rounds of the sumcheck over bit positions. It sends and binds what
/// leanVM's loop of [`local_round`] and `fold` over the `2^LOCAL_VARS` cube does, with the same field
/// values (the field is exact, so neither the order of the sums nor where they reduce changes a
/// value). Every table is zero from position `BITS` on, and a fold keeps it zero from `live` on, so
/// only the pairs below `live` are summed and folded, eight at a time (`F192x8`, E3 only), and the
/// sums accumulate unreduced. It stays on
/// the calling thread: between two transcript round trips a pool dispatch costs about what it saves.
/// Returns the challenges and the three tables' last values. (lvm2 E2F-P: generic over [`Ext`]; at E2
/// every pair takes the one-at-a-time arm.)
fn local_rounds<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    mut w: Vec<F>,
    mut t: [Vec<F>; 3],
    kappa: F,
    scale: F,
) -> (Vec<F>, [F; 3]) {
    assert!(w.len() == BITS && t.iter().all(|v| v.len() == BITS));
    let e3 = as_e3(&w).is_some();
    let mut live = BITS;
    let mut local = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        let pairs = live.div_ceil(2);
        // Entry pair `i` of a table as `(v(0), v(0) + v(1))`, the entry past `live` being zero.
        let line = |v: &[F], i: usize| {
            let lo = v[2 * i];
            let hi = if 2 * i + 1 < live { v[2 * i + 1] } else { F::ZERO };
            (lo, lo + hi)
        };
        // Eight pairs at a time (`F192x8`) while sixteen live entries remain, then one at a time.
        let wide = if e3 { 8 * (live / 16) } else { 0 };
        let mut h8 = [Prod8::ZERO; 4];
        if wide > 0 {
            let (w, t) = (as_e3(&w).expect("E3"), t.each_ref().map(|v| as_e3(v).expect("E3")));
            let k8 = F192x8::splat(to_e3(kappa));
            let line8 = |v: &[F192], g: usize| {
                let at = |o: usize| F192x8::from_array(v[16 * g + o..][..8].try_into().expect("eight"));
                let (lo, hi) = F192x8::even_odd(at(0), at(8));
                (lo, lo + hi)
            };
            for g in 0..wide / 8 {
                let (w, t0, t1, t2) = (line8(w, g), line8(t[0], g), line8(t[1], g), line8(t[2], g));
                let u = (k8 + t1.0, t1.1);
                let mut a0 = k8.mul_unreduced(t0.0);
                a0 ^= u.0.mul_unreduced(t2.0);
                let mut a1 = k8.mul_unreduced(t0.1);
                a1 ^= u.0.mul_unreduced(t2.1);
                a1 ^= u.1.mul_unreduced(t2.0);
                let a = [a0.reduce_lanes(), a1.reduce_lanes(), u.1 * t2.1];
                h8[0] ^= w.0.mul_unreduced(a[0]);
                h8[1] ^= w.0.mul_unreduced(a[1]);
                h8[1] ^= w.1.mul_unreduced(a[0]);
                h8[2] ^= w.0.mul_unreduced(a[2]);
                h8[2] ^= w.1.mul_unreduced(a[1]);
                h8[3] ^= w.1.mul_unreduced(a[2]);
            }
        }
        let mut h = [F::Unreduced::ZERO; 4];
        for i in wide..pairs {
            let (w, t0, t1, t2) = (line(&w, i), line(&t[0], i), line(&t[1], i), line(&t[2], i));
            let u = (kappa + t1.0, t1.1);
            let a = [
                (kappa.mul_unreduced(t0.0) ^ u.0.mul_unreduced(t2.0)).reduce(),
                (kappa.mul_unreduced(t0.1) ^ u.0.mul_unreduced(t2.1) ^ u.1.mul_unreduced(t2.0)).reduce(),
                u.1 * t2.1,
            ];
            h[0] ^= w.0.mul_unreduced(a[0]);
            h[1] ^= w.0.mul_unreduced(a[1]) ^ w.1.mul_unreduced(a[0]);
            h[2] ^= w.0.mul_unreduced(a[2]) ^ w.1.mul_unreduced(a[1]);
            h[3] ^= w.1.mul_unreduced(a[2]);
        }
        let coeffs: [F; 4] = std::array::from_fn(|d| {
            let wide_sum = if wide > 0 { from_e3::<F, W>(h8[d].reduce()) } else { F::ZERO };
            scale * (wide_sum + h[d].reduce())
        });
        ps.add_round_poly_ext(&coeffs, false);
        let challenge = ps.challenge::<F, W>(Grp::C3);
        local.push(challenge);
        // `fold(v, 1, challenge)` on the live pairs.
        let fold = |v: &[F]| -> Vec<F> {
            let mut out = Vec::with_capacity(pairs);
            if wide > 0 {
                let v3 = as_e3(v).expect("E3");
                let c8 = F192x8::splat(to_e3(challenge));
                for g in 0..wide / 8 {
                    let at = |o: usize| F192x8::from_array(v3[16 * g + o..][..8].try_into().expect("eight"));
                    let (lo, hi) = F192x8::even_odd(at(0), at(8));
                    out.extend((lo + c8 * (lo + hi)).to_array().map(from_e3::<F, W>));
                }
            }
            out.extend((wide..pairs).map(|i| {
                let (lo, sum) = line(v, i);
                lo + challenge * sum
            }));
            out
        };
        (w, t) = (fold(&w), [fold(&t[0]), fold(&t[1]), fold(&t[2])]);
        live = pairs;
    }
    (local, [t[0][0], t[1][0], t[2][0]])
}

/// Send a round of the sumcheck over the packs and segments and bind its variable, whose point
/// in the claim is `at`: the claim's `eq` factor on it moves into `scale`.
fn bind<F: Ext<W>, const W: usize>(
    ps: &mut ProverState,
    coeffs: &[F; 3],
    at: F,
    value: &mut F,
    scale: &mut F,
    point: &mut Vec<F>,
) -> F {
    ps.add_round_poly_ext(coeffs, true);
    let challenge = ps.challenge::<F, W>(Grp::C3);
    let eq = F::ONE + at + challenge;
    *value = eq * F::poly_eval(coeffs, challenge);
    *scale *= eq;
    point.push(challenge);
    challenge
}

/// The coefficients of a round polynomial `h`, scaled, from its values at `0` and infinity:
/// `(1 + r) h(0) + r h(1) = value` gives the value at one.
fn round_coefficients<F: Ext<W>, const W: usize>(scale: F, zero: F, infinity: F, value: F, r: F) -> [F; 3] {
    let (c0, c2) = (scale * zero, scale * infinity);
    // value = c0 + r (c1 + c2).
    let c1 = (value + c0) * r.inv() + c2;
    [c0, c1, c2]
}
