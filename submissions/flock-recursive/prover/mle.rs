//! Multilinear helpers. Convention everywhere: variable `k` of an index `i` is bit `k` of `i`
//! (least significant first), and `eq(r, i) = Π_k (r_k if i_k else 1 + r_k)` (characteristic 2).

use crate::field::{F, K};
use crate::par;

/// `eq(r, ·)` over `{0,1}^|r|` (F), built in place in parallel for large tables.
pub fn eq_table(r: &[F]) -> Vec<F> {
    eq_table_scaled(r, F::ONE)
}

pub fn eq_table_scaled(r: &[F], scale: F) -> Vec<F> {
    let n = r.len();
    let mut t = vec![F::ZERO; 1 << n];
    t[0] = scale;
    // high variables first, so that each step doubles the filled prefix: t[i + h] = t[i] r, t[i] (1+r)
    let mut len = 1usize;
    for k in (0..n).rev() {
        let rk = r[k];
        // new layout: index bit k is the lowest so far; we build from the top variable down by
        // spreading: entries j < len become (2j, 2j+1)
        let src: Vec<F> = if len >= 1 << 16 { crate::par::collect_vec(len, 1 << 14, |j| t[j]) } else { t[..len].to_vec() };
        let p = par::SyncPtr(t.as_mut_ptr());
        let body = |j: usize| {
            let p = p;
            let v = src[j];
            let hi = v * rk;
            unsafe {
                *p.0.add(2 * j) = v + hi;
                *p.0.add(2 * j + 1) = hi;
            }
        };
        if len >= 1 << 14 {
            let chunks = len >> 12;
            par::run(chunks, &|c| {
                for j in c << 12..(c + 1) << 12 {
                    body(j);
                }
            });
        } else {
            (0..len).for_each(body);
        }
        len *= 2;
    }
    t
}

/// `eq(r, ·)` over `{0,1}^|r|` (K).
pub fn eq_table_k(r: &[K]) -> Vec<K> {
    let n = r.len();
    let mut t = vec![K::ZERO; 1 << n];
    t[0] = K::ONE;
    let mut len = 1usize;
    for k in (0..n).rev() {
        let rk = r[k];
        for j in (0..len).rev() {
            let v = t[j];
            let hi = v * rk;
            t[2 * j] = v + hi;
            t[2 * j + 1] = hi;
        }
        len *= 2;
    }
    t
}

/// `eq(a, b)` for two points of the same length (F).
pub fn eq_f(a: &[F], b: &[F]) -> F {
    let mut r = F::ONE;
    for (x, y) in a.iter().zip(b.iter()) {
        // xy + (1+x)(1+y) = 1 + x + y
        r *= F::ONE + *x + *y;
    }
    r
}

/// `eq(a, b)` with `a ∈ F^n`, `b ∈ K^n`.
pub fn eq_fk(a: &[F], b: &[K]) -> K {
    let mut r = K::ONE;
    for (x, y) in a.iter().zip(b.iter()) {
        r = r * (K::f(F::ONE + *x) + *y);
    }
    r
}

pub fn eq_kk(a: &[K], b: &[K]) -> K {
    let mut r = K::ONE;
    for (x, y) in a.iter().zip(b.iter()) {
        r = r * (K::ONE + *x + *y);
    }
    r
}

/// `eq(r, bits of i)` for an integer point `i` (F).
pub fn eq_at_int(r: &[F], i: u64) -> F {
    let mut v = F::ONE;
    for (k, rk) in r.iter().enumerate() {
        v *= if (i >> k) & 1 == 1 { *rk } else { F::ONE + *rk };
    }
    v
}

/// `Σ_{b < n} eq(r, b)` over the `2^|r|` points (`r` least significant coordinate first): the
/// multilinear extension of the indicator of `[0, n)` (a segment's chain blocks, revision 4.0).
pub fn range_eq(r: &[F], n: u64) -> F {
    if n >> r.len() != 0 {
        return F::ONE;
    }
    let mut v = F::ZERO; // Σ over b < (n mod 2^k), the low k coordinates
    for (k, rk) in r.iter().enumerate() {
        // extend from k to k + 1 coordinates: the prefix [0, n mod 2^(k+1))
        v = if (n >> k) & 1 == 1 { (F::ONE + *rk) + *rk * v } else { (F::ONE + *rk) * v };
    }
    v
}

pub fn eq_at_int_k(r: &[K], i: u64) -> K {
    let mut v = K::ONE;
    for (k, rk) in r.iter().enumerate() {
        v = v * if (i >> k) & 1 == 1 { *rk } else { K::ONE + *rk };
    }
    v
}

/// The multilinear extension of `t` at `r` (F), by folding.
pub fn mle_f(t: &[F], r: &[F]) -> F {
    assert_eq!(t.len(), 1 << r.len());
    let mut v = t.to_vec();
    for rk in r {
        let h = v.len() / 2;
        for i in 0..h {
            v[i] = v[2 * i] + *rk * (v[2 * i] + v[2 * i + 1]);
        }
        v.truncate(h);
    }
    v[0]
}

/// The multilinear extension of a K table at a K point.
pub fn mle_k(t: &[K], r: &[K]) -> K {
    assert_eq!(t.len(), 1 << r.len());
    let mut v = t.to_vec();
    for rk in r {
        let h = v.len() / 2;
        for i in 0..h {
            v[i] = v[2 * i] + *rk * (v[2 * i] + v[2 * i + 1]);
        }
        v.truncate(h);
    }
    v[0]
}

/// `shift̂(a, b)`: the multilinear extension of `[b = a + 1]` on `n`-bit integers (LSB first), no
/// wrap-around: `Σ_k (Π_{i<k} a_i (1 − b_i)) (1 − a_k) b_k Π_{i>k} eq(a_i, b_i)`.
pub fn shift_mle<T: Copy + std::ops::Add<Output = T> + std::ops::Mul<Output = T>>(a: &[T], b: &[T], one: T) -> T {
    let n = a.len();
    // suffix eq products
    let mut suf = vec![one; n + 1];
    for i in (0..n).rev() {
        // eq(a_i, b_i) = 1 + a_i + b_i
        suf[i] = suf[i + 1] * (one + a[i] + b[i]);
    }
    let mut pre = one;
    let mut s: Option<T> = None;
    for k in 0..n {
        let term = pre * (one + a[k]) * b[k] * suf[k + 1];
        s = Some(match s {
            None => term,
            Some(x) => x + term,
        });
        pre = pre * a[k] * (one + b[k]);
    }
    s.unwrap_or(one + one) // n = 0: no successor, 0
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn range_eq_is_the_indicator_mle() {
        let r: Vec<F> = (0..5).map(|i| F::new(0x9E37_79B9 * (i + 3), 5 * i + 1)).collect();
        for n in [0u64, 1, 2, 7, 16, 17, 31, 32, 40] {
            let direct = (0..n.min(32)).fold(F::ZERO, |a, b| a + eq_at_int(&r, b));
            assert_eq!(range_eq(&r, n), direct, "n = {n}");
        }
    }

    #[test]
    fn eq_and_shift() {
        let r: Vec<F> = (0..5).map(|i| F::new(3 + 7 * i, 11 * i)).collect();
        let t = eq_table(&r);
        for i in 0..32u64 {
            assert_eq!(t[i as usize], eq_at_int(&r, i));
        }
        let mut s = F::ZERO;
        for x in &t {
            s += *x;
        }
        assert_eq!(s, F::ONE);
        // shift at Boolean points
        let n = 4;
        for a in 0..16u64 {
            for b in 0..16u64 {
                let av: Vec<F> = (0..n).map(|k| if (a >> k) & 1 == 1 { F::ONE } else { F::ZERO }).collect();
                let bv: Vec<F> = (0..n).map(|k| if (b >> k) & 1 == 1 { F::ONE } else { F::ZERO }).collect();
                let want = if b == a + 1 { F::ONE } else { F::ZERO };
                assert_eq!(shift_mle(&av, &bv, F::ONE), want, "a {a} b {b}");
            }
        }
    }
}
