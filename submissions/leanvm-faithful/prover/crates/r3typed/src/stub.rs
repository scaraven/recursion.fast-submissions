//! STUB: a synthetic circuit `Q` with FORMAT6's frozen dimensions (`2^20` slots, `2^21` words, `C_rec` of `2^19`
//! words, `Φ_Q` in 43 variables), until CD's generator exists. It is a [`Circuit`] like any blob (swap it with
//! [`crate::circuit::install`] or `$LVM6_Q_BLOB`).
//!
//! The word space (all regions aligned, season 1's shape, `qb-p20.td`):
//!
//! | words | source | target |
//! |---|---|---|
//! | 0 | `one` | — |
//! | 1024 … 2047 | `pub` | header lanes 0 … 1023 |
//! | 2048 … 3071 | `ks` | `Y` lane 0, rows 0 … 1023 (slot 36) |
//! | 3072 … 3583 | `ks` | `Y` lane 1, rows 0 … 511 |
//! | 4096 … 6143 | `sigma` | `C_rec` words `2^18 …` |
//! | `2^19` … `2^20 − 1` | `sflat` | `C_rec` words `0 … 2^19 − 1` |
//! | `2^20` … `2^21 − 1` | `com` | `T`: slots 38–39 (`2^20` words) |
//!
//! The rows: `ROWS` defining rows, row `k` at slot `256k + k mod 7` defines `com` word `251k` by
//! `α·(a₁ + κ₁a₂)·(b₁ + κ₂b₂) + α·c + α·t = 0` (entries `A: α, ακ₁`; `B: 1, κ₂`; `D: α`; `W: α`, with
//! `α ∈ E∖K`, `κ ∈ K`), the operands drawn from the earlier `com` words, `ks`, `pub`, `one`, `sflat`,
//! `sigma`, with random coefficients; then `CHECKS` rows at slots `256k + 128`: `α·s·t + α·u = 0` defining `com`
//! word `u = com_word(ROWS + k)` from a `sflat` or `sigma` word `s`, or the check `α·t·1 + α·t = 0`. Every row is
//! solvable for any stack contents and any header: the stub holds in leaf and in node mode (any `STREAM`).
//! Row 0 reads word 0 (`one`) in `A`, so `Φ_Q(0^43) ≠ 0`. As CD's instance (`stages/CD-circuit.md` §0): one
//! `S_flat` region (`sflatW(b + p) = p`), one `σ` region of `2^11` words at `C_rec` word `sB = 2^18`, one `PUB`
//! region of `2^10` header lanes, no `QLT` region (the blob format keeps `CONST` for one).

use primitives::field::F128;
use r3core::layout;

use crate::circuit::{Circuit, Ent, Src, TReg};

/// The default stub's seed.
pub const SEED: u64 = 0x7479_7065_645f_7136;
/// Defining rows.
pub const ROWS: usize = 4096;
/// Rows that only check.
pub const CHECKS: usize = 64;

pub const ONE_W: usize = 0;
pub const PUB_W: usize = 1024;
pub const KS0_W: usize = 2048;
pub const KS1_W: usize = 3072;
pub const SIG_W: usize = 4096;
pub const SFLAT_W: usize = 1 << 19;
pub const COM_W: usize = 1 << 20;

/// `com` word `k` of the defining rows.
pub fn com_word(k: usize) -> usize {
    COM_W + 251 * k
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// `α ∈ E∖K`.
    fn alpha(&mut self) -> F128 {
        F128::new(self.next(), self.next() | 1)
    }

    fn k(&mut self) -> F128 {
        F128::new(self.next() | 1, 0)
    }
}

/// The stub circuit of `seed`.
pub fn generate(seed: u64) -> Circuit {
    let mut g = Rng(seed);
    let regs = vec![
        TReg { src: Src::One, base: ONE_W, log: 0, off: 0 },
        TReg { src: Src::Pub, base: PUB_W, log: 10, off: 0 },
        TReg { src: Src::Ks, base: KS0_W, log: 10, off: layout::y_idx(0, 0) },
        TReg { src: Src::Ks, base: KS1_W, log: 9, off: layout::y_idx(0, 1) },
        TReg { src: Src::Sigma, base: SIG_W, log: 11, off: 1 << 18 },
        TReg { src: Src::Sflat, base: SFLAT_W, log: 19, off: 0 },
        TReg { src: Src::Com, base: COM_W, log: 20, off: layout::idx(layout::SLOT_T + 1, 0) },
    ];
    let qlt = Vec::new();
    let mut ents = Vec::new();
    let mut outs = Vec::new();
    // an operand word for row `k` (one of the sources, or an earlier defined word)
    let operand = |g: &mut Rng, k: usize| -> usize {
        match g.below(10) {
            0 | 1 => ONE_W,
            2 => PUB_W + g.below(110),
            3 => KS0_W + g.below(1024),
            4 => KS1_W + g.below(512),
            5 => SIG_W + g.below(2048),
            6 => SFLAT_W + g.below(1 << 19),
            _ if k > 0 => com_word(k - 1 - g.below(k.min(64))),
            _ => ONE_W,
        }
    };
    for k in 0..ROWS {
        let x = (256 * k + k % 7) as u32;
        let t = com_word(k);
        let (alpha, k1, k2) = (g.alpha(), g.k(), g.k());
        let (a1, a2, b1, b2, c) = if k == 0 {
            (ONE_W, PUB_W + 1, PUB_W, ONE_W, KS0_W)
        } else {
            (operand(&mut g, k), operand(&mut g, k), operand(&mut g, k), operand(&mut g, k), operand(&mut g, k))
        };
        let e = |o: u8, y: usize, c: F128| Ent { o, x, y: y as u32, c };
        ents.extend([e(0, a1, alpha), e(0, a2, alpha * k1), e(1, b1, F128::ONE), e(1, b2, k2), e(2, c, alpha), e(3, t, alpha)]);
        outs.push((x, t as u32));
    }
    for k in 0..CHECKS {
        let x = (256 * k + 128) as u32;
        let alpha = g.alpha();
        let t = com_word(g.below(ROWS));
        let e = |o: u8, y: usize, c: F128| Ent { o, x, y: y as u32, c };
        // rows 0, 1 mod 3 define `com` word `ROWS + k` from a child-dependent word (any `STREAM`), row 2 mod 3 only
        // checks
        let u = com_word(ROWS + k);
        match k % 3 {
            0 => ents.extend([e(0, SFLAT_W + g.below(1 << 19), alpha), e(1, t, F128::ONE), e(3, u, alpha)]),
            1 => ents.extend([e(0, SIG_W + g.below(2048), alpha), e(1, t, g.k()), e(2, u, alpha)]),
            _ => ents.extend([e(0, t, alpha), e(1, ONE_W, F128::ONE), e(2, t, alpha)]),
        }
        if k % 3 < 2 {
            outs.push((x, u as u32));
        }
    }
    let mut c = Circuit { regs, ents, outs, qlt };
    c.normalize();
    c.check();
    c
}
