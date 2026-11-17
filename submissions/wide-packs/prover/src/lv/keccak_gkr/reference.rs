// lvm2 E2-K: the layer prover's plain reference, over any field of the GKR front (`F192` or `F128`).
//! A dense, unoptimised prover of one layer: the same transcript as `prover::prove_layer`, computed from the
//! definition, with field arithmetic only (no power basis, no bit-level kernels, no padding shortcut).
//!
//! It is the oracle of the generic passes: at E3 it must give today's transcript (checked against the fast
//! prover, whose E3 bytes are the shipped ones), and at E2 the fast passes must give its transcript. Mounted by
//! both GKR trees (`keccak_gkr_v4` through `#[path]`); it reads blocks through `Witness::layer`, which both have.
//!
//! The layer, with `idx` a pack index and segment (the claim's point variables, low first), `T_idx[j]` the value
//! at `s` of the embedding of position `j`'s 32 instance bits, and `kappa` the value at `s` of the all-ones
//! embedding:
//!
//! 1. `U = sum_idx eq(point, idx) sum_j w_j (ones (e_j + e_{j+2}) + e_{j+1} e_{j+2})`, 105 coefficients, sent;
//! 2. `s` drawn; the claim is `U(s) = sum_idx eq(point, idx) sum_j w_j (kappa T[j] + (kappa + T[j+1]) T[j+2])`;
//! 3. one round per point variable, its `eq` factor taken out (the coefficients scaled by the bound part), then
//!    one plain round per position variable; the three values `T[j], T[j+1], T[j+2]` at the end, sent; `beta`.

use crate::lv::fiat_shamir::transcript::{Grp, ProverState};
use crate::lv::primitives::field::Ext;
use crate::lv::primitives::field::gf2_64::mul_wide;

use crate::lv::keccak_gkr::keccak::{BITS, LOCAL_VARS, along, linear_transpose};
use crate::lv::keccak_gkr::protocol::{Claim, chi_weights, mu_at};
use crate::lv::keccak_gkr::rmfe::{EMBED_BITS, PROD_BITS, RMFE};
use crate::lv::keccak_gkr::witness::{Witness, words};

/// Packs of a block (lvm2 W32: 16 packs of 32 instances).
const PACKS: usize = crate::lv::keccak_gkr::witness::BLOCK / crate::lv::keccak_gkr::rmfe::PACK;

/// `lo + t (lo + hi)` pairwise, low variable first.
fn fold<F: Ext<W>, const W: usize>(v: &[F], t: F) -> Vec<F> {
    v.chunks_exact(2).map(|p| p[0] + t * (p[0] + p[1])).collect()
}

/// The coefficients of a product of polynomials.
fn mul_poly<F: Ext<W>, const W: usize>(a: &[F], b: &[F]) -> Vec<F> {
    let mut out = vec![F::ZERO; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (k, &y) in b.iter().enumerate() {
            out[i + k] += x * y;
        }
    }
    out
}

/// Prove one layer as `prover::prove_layer` does, from the definition.
pub fn prove_layer<F: Ext<W>, const W: usize>(ps: &mut ProverState, witness: &Witness, step: usize, claim: &Claim<F>) -> Claim<F> {
    let shape = witness.shape;
    let (nb, segments) = (shape.n_blocks(), shape.segments());
    let n_y = claim.point.len();
    assert_eq!(n_y, shape.y_vars());
    // The embeddings of every pack index, segment and position (nonexistent segments are zero).
    let rows = 1usize << n_y;
    let mut emb = vec![0u64; rows * BITS];
    for segment in 0..segments {
        let round = shape.round(segment, step);
        for g in 0..nb {
            let block = witness.layer(round, g);
            for j in 0..BITS {
                let w = words(block, j);
                for q in 0..PACKS {
                    let idx = q + PACKS * (g + nb * segment);
                    emb[idx * BITS + j] = RMFE.embed((w[q / 2] >> (32 * (q % 2))) as u32);
                }
            }
        }
    }
    // 1. The product polynomial.
    let eq = F::eq_table(&claim.point);
    let ones = RMFE.ones;
    let mut product = [F::ZERO; PROD_BITS];
    for idx in 0..rows {
        let e = &emb[idx * BITS..][..BITS];
        let mut sums = [F::ZERO; PROD_BITS];
        for j in 0..BITS {
            let (a, b, c) = (e[j], e[along(j, 1)], e[along(j, 2)]);
            let p = mul_wide(ones, a ^ c) ^ mul_wide(b, c);
            for (bit, sum) in sums.iter_mut().enumerate() {
                if p >> bit & 1 == 1 {
                    *sum += claim.weights[j];
                }
            }
        }
        for (u, sum) in product.iter_mut().zip(sums) {
            *u += eq[idx] * sum;
        }
    }
    ps.add_ext(&product);
    let s = ps.challenge::<F, W>(Grp::C104);
    let mu = mu_at::<F, W>(s);
    let kappa: F = mu.iter().sum();
    let mut value = F::poly_eval(&product, s);
    // 2. The table at `s`.
    let powers = F::powers(s, EMBED_BITS);
    let mut table: Vec<F> = emb
        .iter()
        .map(|&e| (0..EMBED_BITS).filter(|b| e >> b & 1 == 1).map(|b| powers[b]).sum())
        .collect();
    // The summand's values on one row, and its quadratic coefficient on the line through two rows.
    let summand = |t: &[F]| -> F {
        (0..BITS)
            .map(|j| claim.weights[j] * (kappa * t[j] + (kappa + t[along(j, 1)]) * t[along(j, 2)]))
            .sum()
    };
    let leading = |lo: &[F], hi: &[F]| -> F {
        (0..BITS)
            .map(|j| claim.weights[j] * (lo[along(j, 1)] + hi[along(j, 1)]) * (lo[along(j, 2)] + hi[along(j, 2)]))
            .sum()
    };
    // 3. The point variables, `eq` factored out.
    let (mut scale, mut point) = (F::ONE, Vec::with_capacity(n_y));
    for i in 0..n_y {
        let later = F::eq_table(&claim.point[i + 1..]);
        let mut h = [F::ZERO; 3];
        for (r, &e) in later.iter().enumerate() {
            let (lo, hi) = (&table[2 * r * BITS..][..BITS], &table[(2 * r + 1) * BITS..][..BITS]);
            h[0] += e * summand(lo);
            h[1] += e * summand(hi);
            h[2] += e * leading(lo, hi);
        }
        let coeffs = [scale * h[0], scale * (h[0] + h[1] + h[2]), scale * h[2]];
        ps.add_round_poly_ext(&coeffs, true);
        let challenge = ps.challenge::<F, W>(Grp::C3);
        let e = F::ONE + claim.point[i] + challenge;
        value = e * F::poly_eval(&coeffs, challenge);
        scale *= e;
        point.push(challenge);
        table = table
            .chunks_exact(2 * BITS)
            .flat_map(|pair| (0..BITS).map(move |j| pair[j] + challenge * (pair[j] + pair[BITS + j])))
            .collect();
    }
    let _ = value;
    // The position variables, plain rounds.
    let cube = 1usize << LOCAL_VARS;
    let shifted = |k: usize| -> Vec<F> { (0..cube).map(|j| if j < BITS { table[along(j, k)] } else { F::ZERO }).collect() };
    let mut t = [shifted(0), shifted(1), shifted(2)];
    let mut w = claim.weights.clone();
    w.resize(cube, F::ZERO);
    let mut local = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        let mut h = [F::ZERO; 4];
        for i in 0..w.len() / 2 {
            let line = |v: &[F]| [v[2 * i], v[2 * i] + v[2 * i + 1]];
            let (wl, t0, t1, t2) = (line(&w), line(&t[0]), line(&t[1]), line(&t[2]));
            let inner = mul_poly(&[kappa + t1[0], t1[1]], &t2);
            let inner = [kappa * t0[0] + inner[0], kappa * t0[1] + inner[1], inner[2]];
            for (h, c) in h.iter_mut().zip(mul_poly(&wl, &inner)) {
                *h += c;
            }
        }
        let coeffs = h.map(|c| scale * c);
        ps.add_round_poly_ext(&coeffs, false);
        let challenge = ps.challenge::<F, W>(Grp::C3);
        local.push(challenge);
        w = fold(&w, challenge);
        t = t.map(|v| fold(&v, challenge));
    }
    let t = [t[0][0], t[1][0], t[2][0]];
    ps.add_ext(&t);
    let beta = ps.challenge::<F, W>(Grp::C2);
    Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu,
        point,
        weights: linear_transpose(&chi_weights(&F::eq_table(&local), beta)),
    }
}
