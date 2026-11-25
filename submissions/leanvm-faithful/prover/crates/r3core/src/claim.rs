//! A stack claim on the prover side: `Σ_x W(x)·q(x) = value` over the stack `q` (2^25 `K` words, `layout`), as
//! a phase hands it to §6.5's `λ₀` batch (FORMAT6 v2.4 §6.5: claim `k` has coefficient `λ₀^k`). The weight is
//! supported on one aligned block (FORMAT6's placement: `eq(bits(off), x[μ..])·W(x[..μ])`).
//!
//! [`PClaim::check`] evaluates a claim natively on the stack: the dev oracle the R3 parts use before the opening
//! (§6.6) is wired, as R2's `refv-tree` does for §6.2.

use primitives::field::{F64, F128};
use primitives::multilinear::eq_table;

/// The weight of a stack claim, on the block `[off·2^μ, (off+1)·2^μ)`.
pub enum Weight {
    /// `eq(point, ·)`, `μ = |point|`.
    Point { off: usize, point: Vec<F128> },
    /// A ring-switched claim (FORMAT6 §6.5, `L:ring_switch.rs`): the 64 bit-slice MLEs of the block at `point`
    /// (`μ = |point|`) are `slices`; after §6.5's group draws ring map `map` (0 = tree, 1 = sponge) the claim is
    /// `Σ_x Φ(eq(point, x))·q(x) = ring_target(slices)`. Its `PClaim::value` is unused (§6.5 computes it).
    Ring { off: usize, point: Vec<F128>, slices: Vec<F128>, map: usize },
    /// Any other weight (region claims, sums of several lanes): `fill(scale, w)` ADDS `scale·W(x)` to `w[x]` for
    /// every `x < 2^μ` of the block (`w.len() == 2^μ`).
    Dense { off: usize, mu: usize, fill: Box<dyn Fn(F128, &mut [F128]) + Send + Sync> },
}

impl Weight {
    /// `(off, μ)`.
    pub fn block(&self) -> (usize, usize) {
        match self {
            Weight::Point { off, point } | Weight::Ring { off, point, .. } => (*off, point.len()),
            Weight::Dense { off, mu, .. } => (*off, *mu),
        }
    }
}

/// One stack claim, in §6.5's order when collected.
pub struct PClaim {
    /// For reports and failures, e.g. `"15 sponge ring"`.
    pub label: String,
    pub value: F128,
    pub weight: Weight,
}

impl PClaim {
    pub fn point(label: impl Into<String>, off: usize, point: Vec<F128>, value: F128) -> Self {
        Self { label: label.into(), value, weight: Weight::Point { off, point } }
    }

    pub fn ring(label: impl Into<String>, off: usize, point: Vec<F128>, slices: Vec<F128>, map: usize) -> Self {
        assert_eq!(slices.len(), 64);
        Self { label: label.into(), value: F128::ZERO, weight: Weight::Ring { off, point, slices, map } }
    }

    pub fn dense(
        label: impl Into<String>,
        off: usize,
        mu: usize,
        value: F128,
        fill: impl Fn(F128, &mut [F128]) + Send + Sync + 'static,
    ) -> Self {
        Self { label: label.into(), value, weight: Weight::Dense { off, mu, fill: Box::new(fill) } }
    }

    /// The block's words of the stack.
    fn block<'a>(&self, stack: &'a [F64]) -> &'a [F64] {
        let (off, mu) = self.weight.block();
        &stack[off << mu..(off + 1) << mu]
    }

    /// Dev oracle: does the claim hold on `stack` (the whole `2^25`-word stack)? For a ring claim: every one of
    /// the 64 slices.
    pub fn check(&self, stack: &[F64]) -> bool {
        let q = self.block(stack);
        match &self.weight {
            Weight::Point { point, .. } => {
                let eq = eq_table(point);
                dot_base(&eq, q) == self.value
            }
            Weight::Dense { mu, fill, .. } => {
                let mut w = vec![F128::ZERO; 1 << mu];
                fill(F128::ONE, &mut w);
                dot_base(&w, q) == self.value
            }
            Weight::Ring { point, slices, .. } => {
                let eq = eq_table(point);
                (0..64).all(|z| {
                    let s = eq.iter().zip(q).fold(F128::ZERO, |a, (&e, w)| if w.0 >> z & 1 == 1 { a + e } else { a });
                    s == slices[z]
                })
            }
        }
    }
}

/// `Σ_i w_i·q_i`.
pub fn dot_base(w: &[F128], q: &[F64]) -> F128 {
    assert_eq!(w.len(), q.len());
    let parts = parallel::map_collect(w.len().div_ceil(1 << 14), |c| {
        let lo = c << 14;
        let hi = (lo + (1 << 14)).min(w.len());
        (lo..hi).fold(F128::ZERO, |a, i| a + w[i].mul_base(q[i]))
    });
    parts.into_iter().fold(F128::ZERO, |a, b| a + b)
}

/// Native check of every claim; the labels of those that fail.
pub fn check_all(claims: &[PClaim], stack: &[F64]) -> Vec<String> {
    claims.iter().filter(|c| !c.check(stack)).map(|c| c.label.clone()).collect()
}

// ------------------------------------------------------------------------------------- ring maps, weight at a point

/// One ring-switch map of §6.5's group: `f₀ … f₇`, `g₀ … g₇` (`L:ring_switch.rs:11`; refv `arith`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RingMap {
    pub f: [F128; 8],
    pub g: [F128; 8],
}

const GEN: F128 = F128::new(2, 0);

fn frobenius_8(v: F128, p: usize) -> F128 {
    (0..8 * p).fold(v, |v, _| v.square())
}

fn horner(c: &[F128], x: F128) -> F128 {
    c.iter().rev().fold(F128::ZERO, |acc, &v| acc * x + v)
}

impl RingMap {
    /// From the 16 draws `f₀ … f₇, g₀ … g₇`.
    pub fn from_draws(v: &[F128]) -> Self {
        Self { f: std::array::from_fn(|i| v[i]), g: std::array::from_fn(|i| v[8 + i]) }
    }

    /// `Φ(v) = Σ_k c_k v^(2^k)`, `c_(8p+b) = f_p g_b^(2^(8p))` (`L:ring_switch.rs:45`).
    pub fn coefficients(&self) -> [F128; 64] {
        let mut c = [F128::ZERO; 64];
        let mut pw = self.g;
        for (p, &fp) in self.f.iter().enumerate() {
            for b in 0..8 {
                c[8 * p + b] = fp * pw[b];
            }
            pw.iter_mut().for_each(|gb| *gb = frobenius_8(*gb, 1));
        }
        c
    }

    /// `Φ(v)`.
    pub fn apply(c: &[F128; 64], v: F128) -> F128 {
        let (mut acc, mut pw) = (F128::ZERO, v);
        for &ck in c {
            acc += ck * pw;
            pw = pw.square();
        }
        acc
    }

    /// `T = Σ_i x^i Φ(s_i)` (`L:ring_switch.rs:33`): the value of the ring claim of slices `s`.
    pub fn target(&self, s: &[F128]) -> F128 {
        let psi = |v: F128| {
            let (mut acc, mut pw) = (F128::ZERO, v);
            for &gb in &self.g {
                acc += gb * pw;
                pw = pw.square();
            }
            acc
        };
        let images: Vec<F128> = s.iter().map(|&v| psi(v)).collect();
        let (mut t, mut z) = (F128::ZERO, GEN);
        for p in (0..8).rev() {
            z = frobenius_8(z, 1);
            t += self.f[p] * frobenius_8(horner(&images, z), p);
        }
        t
    }

    /// `W(u) = Φ(eq(r, u))` at `r'`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)` (`L:ring_switch.rs:58`).
    pub fn weight_at(c: &[F128; 64], r: &[F128], r_prime: &[F128]) -> F128 {
        assert_eq!(r.len(), r_prime.len());
        let (mut total, mut fr) = (F128::ZERO, r.to_vec());
        for &ck in c {
            let mut prod = ck;
            for (v, &ch) in fr.iter_mut().zip(r_prime) {
                prod *= F128::ONE + *v + ch;
                *v = v.square();
            }
            total += prod;
        }
        total
    }
}

/// `eq(l, r) = Π (1 + l_i + r_i)`.
pub fn eq_eval(l: &[F128], r: &[F128]) -> F128 {
    assert_eq!(l.len(), r.len());
    l.iter().zip(r).fold(F128::ONE, |acc, (&x, &y)| acc * (F128::ONE + x + y))
}

/// The placement selector `eq(bits(off), z)` (bits of `off` low first).
pub fn selector(off: usize, z: &[F128]) -> F128 {
    z.iter().enumerate().fold(F128::ONE, |acc, (k, &x)| acc * if off >> k & 1 == 1 { x } else { F128::ONE + x })
}

/// The multilinear extension of `t` at `point`, low variable first.
pub fn mle_ext(t: &[F128], point: &[F128]) -> F128 {
    assert_eq!(t.len(), 1 << point.len());
    let mut cur = t.to_vec();
    for &r in point {
        let half = cur.len() / 2;
        for i in 0..half {
            cur[i] = cur[2 * i] + r * (cur[2 * i] + cur[2 * i + 1]);
        }
        cur.truncate(half);
    }
    cur[0]
}

impl PClaim {
    /// The claim's value once §6.5's maps are drawn (`maps[0]` tree, `maps[1]` sponge).
    pub fn batch_value(&self, maps: &[RingMap; 2]) -> F128 {
        match &self.weight {
            Weight::Ring { slices, map, .. } => maps[*map].target(slices),
            _ => self.value,
        }
    }

    /// The weight's multilinear extension at a stack point `z` (25 coordinates, row variables low): what
    /// `V_S` evaluates at WHIR's terminal point. For tests and for the opening's final assertion.
    pub fn weight_at(&self, z: &[F128], maps: &[RingMap; 2]) -> F128 {
        let (off, mu) = self.weight.block();
        let sel = selector(off, &z[mu..]);
        sel * match &self.weight {
            Weight::Point { point, .. } => eq_eval(point, &z[..mu]),
            Weight::Ring { point, map, .. } => RingMap::weight_at(&maps[*map].coefficients(), point, &z[..mu]),
            Weight::Dense { mu, fill, .. } => {
                let mut w = vec![F128::ZERO; 1 << mu];
                fill(F128::ONE, &mut w);
                mle_ext(&w, &z[..*mu])
            }
        }
    }
}
