//! W32-P task 2 (dev only, `LVM_W32_CHECK=1`; never on the hot path): check32.py's (B) and (C) on a real layer of
//! the tape, from the raw witness bits and field arithmetic alone, independent of the layer prover's passes.
//!
//! With `lambda_q = eq(point, q)` over the batch's packs (16 a block), `w` the claim's position weights, `mu` its
//! instance weights and `U` the sent product polynomial (105 coefficients):
//!  (B)  `sum_c U_c * sum_{k : PROJ_k has bit c} mu_k  =  sum_q lambda_q sum_j w_j sum_k mu_k chi_j(32 q + k)`, `chi`
//!       on the raw bits (`a ^ (!b & c)`), no RMFE; and the claim itself: that plus the round's `iota` term equals
//!       the claim's value (what `verifyKeccakLayer` requires).
//!  (C)  `U(s) = sum_q lambda_q sum_j w_j [b(s) c(s) + ones(s) (a(s) + c(s))]`, each pack's embedding evaluated at `s`
//!       in the field (`s`-powers), not in the prover's power basis.

use crate::lv::keccak_gkr::keccak::{BITS, along};
use crate::lv::keccak_gkr::rmfe::{EMBED_BITS, PACK, PROD_BITS, RMFE};
use crate::lv::primitives::field::Ext;

/// Whether the dev check runs (`LVM_W32_CHECK=1`).
pub fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LVM_W32_CHECK").is_ok_and(|v| v == "1"))
}

/// The sum of every subset of eight values, by the byte that picks it.
fn byte_sums<F: Ext<W>, const W: usize>(v: &[F]) -> [F; 256] {
    let mut t = [F::ZERO; 256];
    for byte in 1usize..256 {
        let low = byte.trailing_zeros() as usize;
        t[byte] = t[byte & (byte - 1)] + v.get(low).copied().unwrap_or(F::ZERO);
    }
    t
}

/// Check (B) and (C) on one layer. `blocks(g)` is block `g` of the batch's pre-`chi` state of round `round`
/// (`g < 2^(point.len() - 4)`: a half's blocks, then the upper half's, the padding block standing for the blocks past
/// the written ones). Panics on a failure; returns a one-line summary.
#[allow(clippy::too_many_arguments)]
pub fn layer<'a, F: Ext<W>, const W: usize>(
    step: usize,
    round: usize,
    point: &[F],
    mu: &[F; PACK],
    weights: &[F],
    value: F,
    product: &[F; PROD_BITS],
    s: F,
    blocks: impl Fn(usize) -> &'a [u64] + Sync,
) -> String {
    const PACKS: usize = crate::lv::keccak_gkr::witness::BLOCK / PACK;
    let eq = F::eq_table(point);
    let n_blocks = eq.len() / PACKS;
    // (B)'s left side: the projection of U with the instance weights mu.
    let projected: F = (0..PROD_BITS)
        .map(|c| {
            let m: F = (0..PACK).filter(|&k| RMFE.proj[k] >> c & 1 == 1).map(|k| mu[k]).sum();
            m * product[c]
        })
        .sum();
    let mu_t: [[F; 256]; 4] = std::array::from_fn(|b| byte_sums(&mu[8 * b..8 * b + 8]));
    let mu_dot = |x: u32| -> F { (0..4).map(|b| mu_t[b][(x >> (8 * b)) as u8 as usize]).sum() };
    let powers = F::powers(s, EMBED_BITS);
    let pw_t: Vec<[F; 256]> = (0..EMBED_BITS.div_ceil(8)).map(|b| byte_sums(&powers[8 * b..(8 * b + 8).min(EMBED_BITS)])).collect();
    let at_s = |e: u64| -> F { pw_t.iter().enumerate().map(|(b, t)| t[(e >> (8 * b)) as u8 as usize]).sum() };
    let ones = at_s(RMFE.ones);
    let (raw, at) = crate::lv::parallel::fold_reduce(
        n_blocks,
        || (F::ZERO, F::ZERO),
        |acc, g| {
            let block = blocks(g);
            let pack = |j: usize, q: usize| (block[8 * j + q / 2] >> (32 * (q % 2))) as u32;
            for q in 0..PACKS {
                let (mut b_sum, mut c_sum) = (F::ZERO, F::ZERO);
                for j in 0..BITS {
                    let (a, b, c) = (pack(j, q), pack(along(j, 1), q), pack(along(j, 2), q));
                    b_sum += weights[j] * mu_dot(a ^ (!b & c));
                    let (ea, eb, ec) = (at_s(RMFE.embed(a)), at_s(RMFE.embed(b)), at_s(RMFE.embed(c)));
                    c_sum += weights[j] * (eb * ec + ones * (ea + ec));
                }
                let lambda = eq[q + PACKS * g];
                acc.0 += lambda * b_sum;
                acc.1 += lambda * c_sum;
            }
        },
        |a, b| (a.0 + b.0, a.1 + b.1),
    );
    // The round's iota flips lane 0's bits `z` of the round constant in every instance (sum of lambda: 1).
    let iota: F = (0..64).filter(|&z| crate::lv::keccak_gkr::iota_bit(round, z)).map(|z| weights[z]).sum();
    let kappa: F = mu.iter().copied().sum();
    let b_ok = projected == raw;
    let claim_ok = raw + iota * kappa == value;
    let c_ok = F::poly_eval(product, s) == at;
    let line = format!(
        "W32 check layer {step} (round {round}, {} blocks, {}): (B) projected U = raw-bit chi sum: {}; claim = chi + iota: {}; (C) U(s) = field sum: {}",
        n_blocks,
        F::NAME,
        if b_ok { "OK" } else { "FAIL" },
        if claim_ok { "OK" } else { "FAIL" },
        if c_ok { "OK" } else { "FAIL" }
    );
    eprintln!("lvm: {line}");
    assert!(b_ok && claim_ok && c_ok, "{line}");
    line
}
