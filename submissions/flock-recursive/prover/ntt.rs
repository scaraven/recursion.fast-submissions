//! The additive NTT over F on the subspace basis `β_q = x^q` of BF64 (blueprint §2.1), in the
//! Lin–Chung–Han novel polynomial basis: the message of a codeword is its coefficient vector
//! `(a_c)` in the basis `X_c(X) = Π_k Ŵ_k(X)^{c_k}` (`Ŵ_k` the normalised subspace polynomial of
//! `span(β_0 … β_{k−1})`), and position `p` of the codeword is the value at the point `D[p] = p`
//! (the BF64 element with bit pattern `p`). Every twiddle lies in BF64, so a butterfly is two BF64
//! products. Rate `1/2^R`: replicate the message `2^R` times and transform from layer `R`.
//! Data is interleaved: `data[pos · lanes + lane]` (one Merkle column per position).
//!
//! The structure (layer order, twiddle tables, the replicate start) follows Flock's
//! `crates/flock-core/src/ntt/additive_ntt_f128.rs` as the phase-0 probe ported it
//! (`probe/kernels/src/ntt.rs`); the code is written for the tower field (`../LICENSE-flock`).

use crate::field::{B64, F, K};
use crate::par;
use crate::simd;

/// `Ŵ_k(β_q)` for `k, q < 64` (zero for `q < k`, one for `q = k`).
pub fn what_table() -> &'static Vec<[B64; 64]> {
    static T: std::sync::OnceLock<Vec<[B64; 64]>> = std::sync::OnceLock::new();
    T.get_or_init(|| {
        let n = 40usize;
        // evals[i][q] = W_i(β_q) (unnormalised), W_0 = X, W_{i+1} = W_i (W_i + W_i(β_i))
        let mut ev: Vec<Vec<B64>> = vec![(0..n).map(|q| B64(1u64 << q)).collect()];
        for i in 1..n {
            let p = &ev[i - 1];
            let row: Vec<B64> = (0..n).map(|q| p[q].mul(B64(p[q].0 ^ p[i - 1].0))).collect();
            ev.push(row);
        }
        let mut out = vec![[B64::ZERO; 64]; n];
        for i in 0..n {
            let inv = ev[i][i].inv();
            for q in 0..n {
                out[i][q] = ev[i][q].mul(inv);
            }
            debug_assert!((0..i).all(|q| out[i][q] == B64::ZERO) && out[i][i] == B64::ONE);
        }
        out
    })
}

/// `Ŵ_k(p)` for the domain point `p` (linear in `p`).
#[inline]
pub fn what_at(k: usize, p: u64) -> B64 {
    let t = &what_table()[k];
    let mut r = 0u64;
    let mut x = p;
    while x != 0 {
        let q = x.trailing_zeros() as usize;
        r ^= t[q].0;
        x &= x - 1;
    }
    B64(r)
}

/// `X̂_c(D[p])` at a point `c ∈ K^bits`: `Π_k (1 + c_k + c_k Ŵ_k(p))` (the multilinear extension
/// in `c` of the novel-basis row of position `p`).
pub fn xhat(p: u64, c: &[K]) -> K {
    let mut r = K::ONE;
    for (k, ck) in c.iter().enumerate() {
        let w = what_at(k, p);
        // 1 + c + c w = 1 + c (1 + w)
        let f = K::ONE + ck.mulb(B64(w.0 ^ 1));
        r = r * f;
    }
    r
}

/// The row `(X_c(D[p]))_c` for `c < 2^bits` (BF64 values), by the tensor product.
pub fn xrow(p: u64, bits: usize, out: &mut Vec<B64>) {
    out.clear();
    out.push(B64::ONE);
    for k in 0..bits {
        let w = what_at(k, p);
        let n = out.len();
        for j in 0..n {
            let v = out[j].mul(w);
            out.push(v);
        }
    }
}

pub struct Ntt {
    pub log_d: usize,
    /// `tw[layer][block]`
    pub tw: Vec<Vec<B64>>,
}

impl Ntt {
    pub fn new(log_d: usize) -> Ntt {
        let wt = what_table();
        let mut tw = Vec::with_capacity(log_d);
        for l in 0..log_d {
            let k = log_d - l - 1;
            let mut t = vec![B64::ZERO; 1 << l];
            for b in 1..(1usize << l) {
                let low = b & b.wrapping_neg();
                // block bit j ↔ β_{log_d − l + j}
                let q = log_d - l + low.trailing_zeros() as usize;
                t[b] = B64(t[b ^ low].0 ^ wt[k][q].0);
            }
            tw.push(t);
        }
        Ntt { log_d, tw }
    }

    /// The reference loop (scalar, one thread): layers `start … log_d − 1`.
    pub fn forward_reference(&self, data: &mut [F], lanes: usize, start: usize) {
        let ld = self.log_d;
        for l in start..ld {
            let half = 1usize << (ld - l - 1);
            for b in 0..(1usize << l) {
                let t = self.tw[l][b];
                let bs = b * 2 * half * lanes;
                for r in 0..half {
                    for lane in 0..lanes {
                        let (i, j) = (bs + r * lanes + lane, bs + (r + half) * lanes + lane);
                        let u = data[i] + data[j].mulb(t);
                        data[i] = u;
                        data[j] = data[j] + u;
                    }
                }
            }
        }
    }

    /// The rows of a block that `forward` keeps in cache (about 256 KiB), as a log.
    fn log_c(lanes: usize) -> usize {
        ((256usize << 10) / (lanes * 16)).max(2).trailing_zeros() as usize
    }

    /// `encode`'s replication fused into the first radix-4 pass (pass 13): layers `r` and `r + 1`
    /// of `forward`, every block's rows read from `msg` (at layer `r` a block's input is the whole
    /// message) into `data`, then the same butterflies. Saves the copy's pass over `data`.
    fn first_pass_from(&self, msg: &[F], data: &mut [F], lanes: usize, r: usize) {
        let ld = self.log_d;
        let half = 1usize << (ld - r - 1);
        let q = half / 2;
        let blocks = 1usize << r;
        let rows_per = 16usize.min(q);
        let per = q / rows_per;
        let (tw0, tw1) = (&self.tw[r], &self.tw[r + 1]);
        assert_eq!(msg.len(), 2 * half * lanes);
        let p = par::SyncPtr(data.as_mut_ptr());
        par::run(blocks * per, &|it| {
            let p = p;
            let (b, rc) = (it / per, it % per);
            let bs = b * 2 * half * lanes;
            let r0 = rc * rows_per;
            let len = rows_per * lanes;
            unsafe {
                // SAFETY: item `(b, rc)` owns rows r0, r0 + q, r0 + half, r0 + half + q (+ rows_per) of block b
                let sl = |r: usize| {
                    let d = std::slice::from_raw_parts_mut(p.0.add(bs + r * lanes), len);
                    d.copy_from_slice(&msg[r * lanes..r * lanes + len]);
                    d
                };
                let (x0, x1, x2, x3) = (sl(r0), sl(r0 + q), sl(r0 + half), sl(r0 + half + q));
                simd::butterfly(x0, x2, tw0[b]);
                simd::butterfly(x1, x3, tw0[b]);
                simd::butterfly(x0, x1, tw1[2 * b]);
                simd::butterfly(x2, x3, tw1[2 * b + 1]);
            }
        });
    }

    /// Layers `start … log_d − 1`, parallel: whole-buffer passes while a block is larger than
    /// about 256 KiB, then each block to completion.
    pub fn forward(&self, data: &mut [F], lanes: usize, start: usize) {
        let ld = self.log_d;
        assert_eq!(data.len(), lanes << ld);
        let log_c = Self::log_c(lanes);
        let p = par::SyncPtr(data.as_mut_ptr());
        let mut l = start;
        // radix-4: two layers per pass over the buffer (rows r, r + h/2, r + h, r + 3h/2)
        let sp = crate::prof::span("ntt.passes");
        while ld - l > log_c + 1 {
            let half = 1usize << (ld - l - 1);
            let q = half / 2;
            let blocks = 1usize << l;
            let rows_per = 16usize.min(q);
            let per = q / rows_per;
            let (tw0, tw1) = (&self.tw[l], &self.tw[l + 1]);
            par::run(blocks * per, &|it| {
                let p = p;
                let (b, rc) = (it / per, it % per);
                let bs = b * 2 * half * lanes;
                let r0 = rc * rows_per;
                let len = rows_per * lanes;
                unsafe {
                    let sl = |r: usize| std::slice::from_raw_parts_mut(p.0.add(bs + r * lanes), len);
                    let (x0, x1, x2, x3) = (sl(r0), sl(r0 + q), sl(r0 + half), sl(r0 + half + q));
                    simd::butterfly(x0, x2, tw0[b]);
                    simd::butterfly(x1, x3, tw0[b]);
                    simd::butterfly(x0, x1, tw1[2 * b]);
                    simd::butterfly(x2, x3, tw1[2 * b + 1]);
                }
            });
            l += 2;
        }
        while l < ld && ld - l > log_c {
            let half = 1usize << (ld - l - 1);
            let blocks = 1usize << l;
            let rows_per = 64usize.min(half);
            let items = blocks * (half / rows_per);
            let tw = &self.tw[l];
            par::run(items, &|it| {
                let p = p;
                let per = half / rows_per;
                let (b, rc) = (it / per, it % per);
                let t = tw[b];
                let bs = b * 2 * half * lanes;
                let r0 = rc * rows_per;
                unsafe {
                    let top = std::slice::from_raw_parts_mut(p.0.add(bs + r0 * lanes), rows_per * lanes);
                    let bot = std::slice::from_raw_parts_mut(p.0.add(bs + (r0 + half) * lanes), rows_per * lanes);
                    simd::butterfly(top, bot, t);
                }
            });
            l += 1;
        }
        drop(sp);
        if l >= ld {
            return;
        }
        let _sp = crate::prof::span("ntt.blocks");
        let l0 = l;
        par::run(1usize << l0, &|b0| {
            let p = p;
            let bsz = 1usize << (ld - l0);
            let base = b0 * bsz * lanes;
            for ll in l0..ld {
                let half = 1usize << (ld - ll - 1);
                let sub = 1usize << (ll - l0);
                for sb in 0..sub {
                    let b = (b0 << (ll - l0)) + sb;
                    let t = self.tw[ll][b];
                    let bs = base + sb * 2 * half * lanes;
                    unsafe {
                        let top = std::slice::from_raw_parts_mut(p.0.add(bs), half * lanes);
                        let bot = std::slice::from_raw_parts_mut(p.0.add(bs + half * lanes), half * lanes);
                        simd::butterfly(top, bot, t);
                    }
                }
            }
        });
    }

    /// Encode `lanes` interleaved messages of `2^(log_d − r)` coefficients at rate `1/2^r`.
    pub fn encode(&self, msg: &[F], lanes: usize, r: usize, out: &mut Vec<F>) {
        let n = lanes << self.log_d;
        assert_eq!(msg.len() << r, n);
        out.clear();
        out.reserve(n);
        unsafe { out.set_len(n) };
        let h = msg.len();
        let ld = self.log_d;
        // the first two layers a radix-4 pass of `forward`: the copy fused into it (pass 13;
        // `FLOCK_NTT_COPY=1`: the copy, then `forward`, the reference)
        if r + 1 < ld && ld - r > Self::log_c(lanes) + 1 && std::env::var_os("FLOCK_NTT_COPY").is_none() {
            let sp = crate::prof::span("ntt.first");
            self.first_pass_from(msg, out, lanes, r);
            drop(sp);
            self.forward(out, lanes, r + 2);
            return;
        }
        let po = par::SyncPtr(out.as_mut_ptr());
        let chunk = 1usize << 16;
        let sp = crate::prof::span("ntt.copy");
        par::run(n.div_ceil(chunk), &|c| {
            let po = po;
            let (s, e) = (c * chunk, ((c + 1) * chunk).min(n));
            for k in s..e {
                unsafe { *po.0.add(k) = msg[k % h] };
            }
        });
        drop(sp);
        self.forward(out, lanes, r);
    }
}

/// `Σ_c a_c X_c(D[p])` directly (tests and the verifier's final level).
pub fn eval_novel(a: &[F], p: u64) -> F {
    let bits = a.len().trailing_zeros() as usize;
    let mut row = Vec::new();
    xrow(p, bits, &mut row);
    let mut s = F::ZERO;
    for (x, w) in a.iter().zip(row.iter()) {
        s += x.mulb(*w);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    fn rnd(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }
    #[test]
    fn encode_is_novel_basis_evaluation() {
        let mut s = 5u64;
        for (log_d, lanes, r) in [(6usize, 1usize, 1usize), (7, 4, 2), (9, 16, 3), (10, 64, 1), (12, 16, 4), (12, 64, 1), (13, 16, 1)] {
            let k = 1usize << (log_d - r);
            let msg: Vec<F> = (0..k * lanes).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
            let ntt = Ntt::new(log_d);
            let mut cw = Vec::new();
            ntt.encode(&msg, lanes, r, &mut cw);
            let mut refd: Vec<F> = (0..(lanes << log_d)).map(|i| msg[i % msg.len()]).collect();
            ntt.forward_reference(&mut refd, lanes, r);
            assert_eq!(cw, refd);
            for lane in [0, lanes - 1] {
                let a: Vec<F> = (0..k).map(|c| msg[c * lanes + lane]).collect();
                for p in [0u64, 1, 3, (1 << log_d) - 1, 37 % (1 << log_d)] {
                    assert_eq!(cw[p as usize * lanes + lane], eval_novel(&a, p), "log_d {log_d} p {p}");
                }
            }
        }
    }
    #[test]
    fn xhat_is_the_mle() {
        let mut s = 11u64;
        let bits = 5;
        let p = 0b1011_0110u64;
        let c: Vec<K> = (0..bits).map(|_| K { a: F::new(rnd(&mut s), rnd(&mut s)), b: F::new(rnd(&mut s), 0) }).collect();
        let mut row = Vec::new();
        xrow(p, bits, &mut row);
        let eq = crate::mle::eq_table_k(&c);
        let mut acc = K::ZERO;
        for i in 0..row.len() {
            acc += eq[i].mulb(row[i]);
        }
        assert_eq!(acc, xhat(p, &c));
    }
}
