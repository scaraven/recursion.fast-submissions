//! The arithmetic of the checks, "normative by reference" (FORMAT6 preamble): leanVM's `crates/verifier` at
//! `fdb317982`, function by function. The field (`E`, `K`) and the subspace polynomials (`Subspace`,
//! `subspace_roots`) are the vendored crate's public items; what the crate keeps private is transcribed here with
//! its source line (`L:` = `crates/verifier/src/`). Nothing here reads bytes or the transcript.

use verifier::{E, K, Subspace};

pub const ZERO: E = E::new(0, 0);
pub const ONE: E = E::new(1, 0);
pub const GEN: E = E::new(2, 0);

/// `[1, base, base², …]` (`L:field.rs:251`).
pub fn powers(base: E, count: usize) -> Vec<E> {
    let mut out = Vec::with_capacity(count);
    let mut p = ONE;
    for _ in 0..count {
        out.push(p);
        p *= base;
    }
    out
}

/// `eq(l, r) = Π (1 + l_i + r_i)` (`L:multilinear.rs:91`).
pub fn eq_eval(l: &[E], r: &[E]) -> E {
    assert_eq!(l.len(), r.len());
    l.iter().zip(r).fold(ONE, |acc, (&x, &y)| acc * (ONE + x + y))
}

pub fn dot(l: &[E], r: &[E]) -> E {
    assert_eq!(l.len(), r.len());
    l.iter().zip(r).fold(ZERO, |acc, (&x, &y)| acc + x * y)
}

/// The multilinear extension of `mle` at `point`, low variable first (`L:multilinear.rs:49`).
pub fn multilinear_eval(mle: &[E], point: &[E]) -> E {
    assert_eq!(mle.len(), 1 << point.len());
    let mut cur = mle.to_vec();
    for &r in point {
        let half = cur.len() / 2;
        for i in 0..half {
            cur[i] = cur[2 * i] + r * (cur[2 * i] + cur[2 * i + 1]);
        }
        cur.truncate(half);
    }
    cur[0]
}

/// Horner, constant first (`L:multilinear.rs:131`).
pub fn poly_eval(c: &[E], x: E) -> E {
    c.iter().rev().fold(ZERO, |acc, &v| acc * x + v)
}

/// `X_c(x) = Π_{i: c_i = 1} What_i(x)` for `c < count` (`L:whir.rs:126`, Annex D's novel basis).
pub fn novel_basis(what: &[K], count: usize) -> Vec<K> {
    let mut basis = vec![K(1)];
    for &v in what {
        if basis.len() >= count {
            break;
        }
        let doubled: Vec<K> = basis.iter().map(|&b| b * v).collect();
        basis.extend(doubled);
    }
    assert!(basis.len() >= count, "the novel basis needs What_i for every bit of its indices");
    basis.truncate(count);
    basis
}

/// `P(x) = Σ_c p_c X_c(x)` (`L:whir.rs:143`).
pub fn novel_eval(p: &[E], what: &[K]) -> E {
    let basis = novel_basis(what, p.len());
    p.iter().zip(basis).fold(ZERO, |acc, (&c, b)| acc + c * b)
}

/// One fold round's challenges: `P = G + (α + β X) F` (`L:whir.rs:150`).
#[derive(Clone, Copy, Debug)]
pub struct FoldRound {
    pub alpha: E,
    pub beta: E,
}

impl FoldRound {
    /// The claim after the round from the table `[v_G, v_F, t₀, t₁]` (`L:whir.rs:304`).
    pub fn next_claim(&self, claim: E, t: &[E]) -> E {
        let (u0, w, c0, c1) = (t[0], t[1], t[2], t[3]);
        let (a, b) = (self.alpha, self.beta);
        u0 + b * c0 + a * (u0 + claim + a * w + b * (c0 + c1))
    }
}

/// An opened row, its lanes in fold order, folded at `x` (`L:whir.rs:158`): `F`, `G` = lanes `2m`, `2m + 1`.
pub fn fold_row(mut v: Vec<E>, x: K, rounds: &[FoldRound]) -> E {
    for r in rounds {
        let (affine, half) = (r.alpha + r.beta * x, v.len() / 2);
        for i in 0..half {
            v[i] = v[2 * i + 1] + affine * v[2 * i];
        }
        v.truncate(half);
    }
    assert_eq!(v.len(), 1, "one round per lane variable");
    v[0]
}

/// The level's batched query weight at `point` (`L:whir.rs:177`): `Σ_q w_q Π_k (1 + p_k (1 + What_k(x_q)))`.
pub fn induced_weight(mu: usize, queries: &[u64], weights: &[E], point: &[E]) -> E {
    assert_eq!(point.len(), mu, "induced basis dimensions");
    let sub = Subspace::new(mu);
    let mut total = ZERO;
    for (&w, &q) in weights.iter().zip(queries) {
        let what = sub.at(K(q));
        let mut prod = w;
        for (&c, &v) in point.iter().zip(&what) {
            prod *= ONE + c * (K(1) + v);
        }
        total += prod;
    }
    total
}

/// The v6 grinding rule (PARAM, season 1's `εFS_le_of`): the least `g ≥ 1` with `8c ≤ 7·2^g` for a group of error
/// `c/|E|` (FORMAT6 §4: every group has a nonce, also at `c = 1`). The same rule as RT's
/// `fiat_shamir_prover::grinding_bits` for v6; the frozen parts read their grinds from the `Shape` instead.
pub fn grinding_bits6(c: u128) -> u32 {
    (1..=23).find(|&g| 8 * c <= 7u128 << g).expect("a group's grind is at most 23 bits")
}

// ------------------------------------------------------------------------------------------- ring switching

/// `Φ`'s challenges come in two rows of eight: `f_p`, then `g_b` (`L:ring_switch.rs:11`).
pub const RING_MAP_WIDTH: usize = 8;

fn frobenius_8(v: E, p: usize) -> E {
    (0..RING_MAP_WIDTH * p).fold(v, |v, _| v.square())
}

fn ring_psi(v: E, g: &[E]) -> E {
    let (mut psi, mut pw) = (ZERO, v);
    for &gb in g {
        psi += gb * pw;
        pw = pw.square();
    }
    psi
}

/// `T = Σ_i x^i Φ(s_i)` (`L:ring_switch.rs:33`).
pub fn ring_target(s: &[E], f: &[E], g: &[E]) -> E {
    let images: Vec<E> = s.iter().map(|&v| ring_psi(v, g)).collect();
    let (mut t, mut z) = (ZERO, GEN);
    for p in (0..RING_MAP_WIDTH).rev() {
        z = frobenius_8(z, 1);
        t += f[p] * frobenius_8(poly_eval(&images, z), p);
    }
    t
}

/// `Φ(v) = Σ_k c_k v^(2^k)`, `c_(8p+b) = f_p g_b^(2^(8p))` (`L:ring_switch.rs:45`).
pub fn ring_coefficients(f: &[E], g: &[E]) -> Vec<E> {
    let mut c = Vec::with_capacity(64);
    let mut pw = g.to_vec();
    for &fp in f {
        c.extend(pw.iter().map(|&gb| fp * gb));
        pw.iter_mut().for_each(|gb| *gb = frobenius_8(*gb, 1));
    }
    c
}

/// `W(u) = Φ(eq(r, u))` at `r'`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)` (`L:ring_switch.rs:58`).
pub fn ring_weight(r: &[E], r_prime: &[E], c: &[E]) -> E {
    assert_eq!(r.len(), r_prime.len());
    let (mut total, mut fr) = (ZERO, r.to_vec());
    for &ck in c {
        let mut prod = ck;
        for (v, &ch) in fr.iter_mut().zip(r_prime) {
            prod *= ONE + *v + ch;
            *v = v.square();
        }
        total += prod;
    }
    total
}

// ------------------------------------------------------------------------------------------- prover side (gen)

/// `eq(z, b)` for every `b < 2^|z|`, low bit first.
pub fn eq_table(z: &[E]) -> Vec<E> {
    let mut out = vec![ONE];
    for &r in z {
        let n = out.len();
        out.extend_from_within(..);
        for i in 0..n {
            let h = out[i] * r;
            out[n + i] = h;
            out[i] += h;
        }
    }
    out
}

/// `a_i = W_(i+1)(β_(i+1)) / W_i(β_i)²` for `i < n` (`L:whir.rs` test `times_x`).
pub fn x_constants(n: usize) -> Vec<K> {
    let roots = verifier::subspace_roots(n + 1);
    (0..n).map(|i| roots[i + 1] * roots[i].square().inv()).collect()
}

/// `X · H` in the novel basis (`L:whir.rs` test `times_x`, which checks it against multiplication by `x`):
/// `X X_c = Σ_(j < t) A_j X_(c, low j bits cleared) + A_t X_(c+1)`, `t` the trailing ones of `c`,
/// `A_j = a_0 ⋯ a_(j−1)`. `h` is read at `h[first + stride·c]`, `c < count`; the result has `count + 1` entries.
pub fn times_x_strided(h: &[E], first: usize, stride: usize, count: usize, a: &[K]) -> Vec<E> {
    let mut out = vec![ZERO; count + 1];
    for c in 0..count {
        let v = h[first + stride * c];
        let t = c.trailing_ones() as usize;
        let mut prod = K(1);
        for (j, &aj) in a.iter().enumerate().take(t) {
            out[c & !((1 << j) - 1)] += v * prod;
            prod = prod * aj;
        }
        out[c + 1] += v * prod;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rng() -> impl FnMut() -> E {
        let mut s = 0x9E37_79B9_7F4A_7C15u64;
        move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            E::new(s, s.rotate_left(29))
        }
    }

    /// `times_x_strided` is multiplication by `x` at every point (the vendored test's statement, for our copy).
    #[test]
    fn times_x_is_multiplication_by_x() {
        let mut next = rng();
        let n = 37;
        let h: Vec<E> = (0..n).map(|_| next()).collect();
        let a = x_constants(8);
        let p = times_x_strided(&h, 0, 1, n, &a);
        let sub = Subspace::new(7);
        for _ in 0..4 {
            let x = K(next().c0);
            let what = sub.at(x);
            assert_eq!(novel_eval(&p, &what), novel_eval(&h, &what) * x);
        }
    }

    /// The ring map's target and coefficients expand `Σ_i x^i Σ_k c_k s_i^(2^k)` (the vendored test, for our copy).
    #[test]
    fn ring_target_matches_coefficients() {
        let mut next = rng();
        let ch: Vec<E> = (0..16).map(|_| next()).collect();
        let (f, g) = ch.split_at(8);
        let c = ring_coefficients(f, g);
        let s: Vec<E> = (0..64).map(|_| next()).collect();
        let images: Vec<E> = s
            .iter()
            .map(|&v| {
                let (mut img, mut pw) = (ZERO, v);
                for &ck in &c {
                    img += ck * pw;
                    pw = pw.square();
                }
                img
            })
            .collect();
        assert_eq!(ring_target(&s, f, g), poly_eval(&images, GEN));
    }

    /// PARAM's table: 1 for `c = 1`; 2 for 2, 3; 3 for 4–6; 4 for 8; 5 for 18; 6 for 46.
    #[test]
    fn grinding_rule_matches_param() {
        for (c, g) in [(1, 1), (2, 2), (3, 2), (4, 3), (6, 3), (7, 3), (8, 4), (18, 5), (46, 6), (1 << 15, 16)] {
            assert_eq!(grinding_bits6(c), g, "c = {c}");
        }
    }

    #[test]
    fn eq_table_matches_eq_eval() {
        let mut next = rng();
        let z: Vec<E> = (0..5).map(|_| next()).collect();
        let t = eq_table(&z);
        for b in [0usize, 1, 6, 31] {
            let bits: Vec<E> = (0..5).map(|k| E::new((b >> k & 1) as u64, 0)).collect();
            assert_eq!(t[b], eq_eval(&z, &bits));
        }
    }
}
