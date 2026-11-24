//! The KAT generator: an honest prover for the frozen parts (§6.1, §6.5, §6.6, with §6.2–§6.4 stubbed), on RT's
//! prover-side transcript (`fs6::Transcript`, `fs6::Tree6`, the keyed oracle `fs6::oracle::Local`).
//!
//! The mathematics is leanVM's experimental prover: the Reed–Solomon encodes are `pcs::ntt::AdditiveNttF64` (the
//! vendored NTT, unchanged); the fold rounds, the glue of the OOD and query claims and the tail sumcheck are
//! `pcs::whir` `Dense::table`/`Dense::fold`/`glue`/`tail_sumcheck` transcribed naively here, because those are
//! `pub(crate)` and bound to leanVM's duplex sponge. Once RT routes `pcs` through `fs6`, the generator should call
//! `pcs` directly and these fixtures must not change a byte.
//!
//! [`Tamper`] injects one wrong prover message and lets the prover continue honestly (re-grinding every later
//! nonce), so the verifier must reject at the check that guards that message; [`resign`] instead edits bytes of a
//! finished `π` and re-derives the trace from the oracle (the checks right at the edit).

use crate::arith::{FoldRound, ONE, ZERO, eq_table, novel_basis, times_x_strided, x_constants};
use crate::chain::RecordAsk;
use crate::format::{Signed, to_file, toy_sign, trace_digest};
use crate::hdr::MAGIC;
use crate::keccak::leaf_stmt;
use crate::shape::Shape;
use crate::{Digest, E, K, e_of, fs_e};
use fs6::oracle::Local;
use fs6::{Transcript, Tree6};
use pcs::ntt::AdditiveNttF64;
use primitives::field::F64;
use verifier::Subspace;

/// One wrong prover message (Kind P).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tamper {
    /// Bit 0 of every entry of level `i`'s cap (`CAP(0)` in §6.1, `CAP(i)` in level `i−1`).
    Cap(usize),
    /// `y₀` (§6.1).
    Y0,
    /// Entry `idx` of fold round `round`'s table at `level` (`v_G, v_F, t₀, t₁`).
    Fold { level: usize, round: usize, idx: usize },
    /// Coefficient 0 of level `i`'s high part `φ`.
    High(usize),
    /// `y_(i+1)`, the OOD value sent at level `i`.
    OodY(usize),
    /// Byte 0 of the first opening's leaf at level `i`.
    Leaf(usize),
    /// Byte 0 of the first opening's first sibling at level `i`.
    Sibling(usize),
    /// Final polynomial coefficient `idx`.
    Final(usize),
    /// Tail round `round`'s `c₀` (`idx = 0`) or `c₂` (`idx = 1`).
    Tail { round: usize, idx: usize },
}

#[derive(Clone, Debug)]
pub struct Cfg {
    pub sh: Shape,
    pub seed: u64,
    pub key: [u8; 32],
    pub sign_seed: u8,
    pub tamper: Option<Tamper>,
}

impl Cfg {
    pub fn new(sh: Shape, seed: u64) -> Self {
        let key: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(29) ^ 0xA5 ^ seed as u8);
        Self { sh, seed, key, sign_seed: 7, tamper: None }
    }
}

pub struct Kat {
    pub vk: Digest,
    pub c: Digest,
    pub h: Digest,
    pub pi: Vec<u8>,
    pub trace: fs6::Trace,
    pub file: Vec<u8>,
}

pub fn mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The header of a leaf proof: magic, `b = 0`, `n = 2^log_blocks`, `h`, `c' = 0`, `vk` (v2.2, offset 88),
/// `accIn = 0`. FORMAT6 §2.1's honest `accIn.y` is `Φ_Q(0^v)`, which §T has not fixed: the KATs use 0.
pub fn leaf_header(sh: &Shape, h: &Digest, vk: &Digest) -> Vec<u8> {
    let mut v = MAGIC.to_vec();
    v.extend_from_slice(&0u64.to_le_bytes());
    v.extend_from_slice(&(1u64 << sh.log_blocks).to_le_bytes());
    v.extend_from_slice(h);
    v.extend_from_slice(&[0; 32]);
    v.extend_from_slice(vk);
    v.resize(sh.hdr_len(), 0);
    v
}

/// A committed codeword: rows of `rw` words, a leaf being words `off .. off + n` of its row, and its tree.
struct Committed {
    cw: Vec<F64>,
    rw: usize,
    off: usize,
    n: usize,
    tree: Tree6,
}

impl Committed {
    fn build(o: &Local, l: &crate::shape::Level, cw: Vec<F64>, rw: usize, off: usize, n: usize) -> Self {
        let leaf = |p: usize, b: &mut Vec<u8>| {
            for w in &cw[p * rw + off..p * rw + off + n] {
                b.extend_from_slice(&w.0.to_le_bytes());
            }
        };
        let tree = Tree6::build(o, l.ht, l.lv, &leaf);
        Self { cw, rw, off, n, tree }
    }

    fn leaf(&self, p: usize, b: &mut Vec<u8>) {
        for w in &self.cw[p * self.rw + self.off..p * self.rw + self.off + self.n] {
            b.extend_from_slice(&w.0.to_le_bytes());
        }
    }
}

/// Level 0: lane `t` of the codeword is slot `lanes−1−t`, after `rw − lanes` zero lanes (`pcs::whir::commit`), so
/// a leaf is slot 45 first, slot 0 last (FORMAT6 §5).
fn commit0(o: &Local, sh: &Shape, q: &[u64]) -> Committed {
    let l = &sh.levels[0];
    let (m, r) = (l.log_msg_cols as usize, l.log_inv_rate as usize);
    let rw = sh.lanes.next_multiple_of(8).min(64);
    let z = rw - sh.lanes;
    let mut cw = vec![F64(0); (1usize << (m + r)) * rw];
    parallel::chunks_mut(&mut cw[..(1usize << m) * rw], rw, |c, row| {
        for (j, w) in row.iter_mut().enumerate().skip(z) {
            *w = F64(q[c + (sh.lanes - 1 - (j - z) << m)]);
        }
    });
    AdditiveNttF64::standard(m + r).encode_interleaved_in_place(&mut cw, rw, r);
    Committed::build(o, l, cw, rw, z, sh.lanes)
}

/// Level `i ≥ 1`: the low part of the folded lane, `2^k` interleaved lanes of `E` (two words each), lane `u` at
/// bytes `16u` of the leaf (`pcs::whir::ligero_commit_ext`).
fn commit_e(o: &Local, sh: &Shape, i: usize, p_low: &[E]) -> Committed {
    let l = &sh.levels[i];
    let (cols, k, r) = (l.log_msg_cols as usize, l.fold, l.log_inv_rate as usize);
    assert_eq!(p_low.len(), 1 << (cols + k));
    let rw = 2 << k;
    let mut cw = vec![F64(0); (1usize << (cols + r)) * rw];
    for (j, e) in p_low.iter().enumerate() {
        cw[2 * j] = F64(e.c0);
        cw[2 * j + 1] = F64(e.c1);
    }
    AdditiveNttF64::standard(cols + r).encode_interleaved_in_place(&mut cw, rw, r);
    Committed::build(o, l, cw, rw, 0, rw)
}

/// Lanes in the clear, coefficient by coefficient (`pcs::whir::Dense`): coefficient `c` of lane `l` at
/// `c·stride + l`, the weight over the low coefficients in the same order.
struct Dense {
    f: Vec<E>,
    w: Vec<E>,
    stride: usize,
}

impl Dense {
    /// `X·F` for every pair's `F` (lane `2m`), all columns, one longer.
    fn xf(&self) -> Vec<Vec<E>> {
        let (s, ncols) = (self.stride, self.f.len() / self.stride);
        let a = x_constants((usize::BITS - ncols.leading_zeros()) as usize + 2);
        parallel::map_collect(s / 2, |m| times_x_strided(&self.f, 2 * m, s, ncols, &a))
    }

    /// `[v_G, v_F, t₀, t₁] = [⟨W₀, G⟩, ⟨W₀ + W₁, F⟩, ⟨W₀, XF⟩, ⟨W₁, XF⟩]` over the low columns.
    fn table(&self, xf: &[Vec<E>]) -> [E; 4] {
        let (s, f, w) = (self.stride, &self.f, &self.w);
        let low = w.len() / s;
        let parts = parallel::map_collect(s / 2, |m| {
            let mut acc = [ZERO; 4];
            for c in 0..low {
                let (w0, w1, ff, g, x) = (w[c * s + 2 * m], w[c * s + 2 * m + 1], f[c * s + 2 * m], f[c * s + 2 * m + 1], xf[m][c]);
                acc[0] += w0 * g;
                acc[1] += (w0 + w1) * ff;
                acc[2] += w0 * x;
                acc[3] += w1 * x;
            }
            acc
        });
        parts.into_iter().fold([ZERO; 4], |a, b| std::array::from_fn(|k| a[k] + b[k]))
    }

    /// Lanes `P = G + αF + βXF` (one column longer), weight `W₀ + α(W₀ + W₁)`.
    fn fold(&mut self, xf: &[Vec<E>], r: FoldRound) {
        let (s, pairs) = (self.stride, self.stride / 2);
        let ncols = self.f.len() / s;
        let f = &self.f;
        let mut next = vec![ZERO; (ncols + 1) * pairs];
        parallel::chunks_mut(&mut next, pairs, |c, out| {
            for (m, o) in out.iter_mut().enumerate() {
                let bx = r.beta * xf[m][c];
                *o = if c == ncols { bx } else { f[c * s + 2 * m + 1] + r.alpha * f[c * s + 2 * m] + bx };
            }
        });
        let w: Vec<E> = self.w.chunks_exact(2).map(|p| p[0] + r.alpha * (p[0] + p[1])).collect();
        (self.f, self.w, self.stride) = (next, w, pairs);
    }

    fn claim(&self) -> E {
        self.w.iter().zip(&self.f).fold(ZERO, |a, (&w, &f)| a + w * f)
    }
}

/// The honest proof of `Σ_b eq(z₀, b)·q(b) = y₀` for a pseudo-random stack `q`, through the stub schedule.
pub fn prove(cfg: &Cfg) -> Kat {
    let sh = &cfg.sh;
    let tamper = cfg.tamper;
    let o = Local::keyed(&cfg.key);
    let m = sh.stack_log - 6;
    let rows = 1usize << m;
    let mut q = vec![0u64; 1 << sh.stack_log];
    parallel::fill(&mut q, |i| if i >> m < sh.lanes { mix(cfg.seed ^ mix(i as u64)) } else { 0 });

    let mut cur = commit0(&o, sh, &q);
    let flip_cap = |i: usize, cap: &[Digest]| -> Vec<Digest> {
        let mut v = cap.to_vec();
        if tamper == Some(Tamper::Cap(i)) {
            v.iter_mut().for_each(|d| d[0] ^= 1);
        }
        v
    };
    let fix = |t: Tamper, v: &mut [E], idx: usize| {
        if tamper == Some(t) {
            v[idx] += ONE;
        }
    };

    let h = crate::keccak::keccak256(&[b"refv kat h".as_slice(), &cfg.seed.to_le_bytes()].concat());
    let vk = toy_sign(cfg.sign_seed, &[0; 32]).0;
    let hdr = leaf_header(sh, &h, &vk);
    let c = leaf_stmt(&h, 1 << sh.log_blocks);
    let mut tr = Transcript::start(&o, &hdr).forbid(sh.forbidden_lengths());

    // §6.1
    tr.absorb_cap(&flip_cap(0, cur.tree.cap()));
    tr.bind();
    let mut z0 = vec![e_of(tr.ground(sh.levels[0].grind_ood))];
    z0.extend(tr.draws(sh.stack_log - 1).into_iter().map(e_of));
    let (eq_row, eq_slot) = (eq_table(&z0[..m]), eq_table(&z0[m..]));
    let y0 = (0..sh.lanes).fold(ZERO, |a, s| {
        let col = (0..rows).fold(ZERO, |b, r| b + eq_row[r] * K(q[r + (s << m)]));
        a + eq_slot[s] * col
    });
    let mut msg = [y0];
    fix(Tamper::Y0, &mut msg, 0);
    tr.absorb_e(&msg.map(fs_e));
    // §6.2–§6.4: the stub (no item). §6.5: `B`, the maps and `λ₀`; claim 0 alone, so the target is `y₀`.
    tr.bind();
    tr.ground(sh.grind_batch);
    tr.draws(32);
    let mut claim = y0;

    let mut d = Dense { f: vec![ZERO; 64 << m], w: vec![ZERO; 64 << m], stride: 64 };
    parallel::chunks_mut(&mut d.f, 64, |c, row| {
        for (l, x) in row.iter_mut().enumerate().take(sh.lanes) {
            *x = E::new(q[c + (l << m)], 0);
        }
    });
    parallel::chunks_mut(&mut d.w, 64, |c, row| {
        for (l, x) in row.iter_mut().enumerate() {
            *x = eq_row[c] * eq_slot[l];
        }
    });
    drop(q);

    let n_levels = sh.levels.len();
    for (i, l) in sh.levels.iter().enumerate() {
        let mut rounds = Vec::with_capacity(l.fold);
        for j in 0..l.fold {
            let xf = d.xf();
            let t = d.table(&xf);
            let mut sent = t;
            for idx in 0..4 {
                fix(Tamper::Fold { level: i, round: j, idx }, &mut sent, idx);
            }
            tr.absorb_e(&sent.map(fs_e));
            let alpha = e_of(tr.ground(l.grind_fold));
            let beta = e_of(tr.draw());
            let r = FoldRound { alpha, beta };
            claim = r.next_claim(claim, &t);
            d.fold(&xf, r);
            rounds.push(r);
        }
        let mu = l.log_msg_cols as usize;
        assert_eq!((d.stride, d.f.len(), d.w.len()), (1, (1 << mu) + l.fold, 1 << mu));
        if tamper.is_none() {
            assert_eq!(claim, d.claim(), "level {i}: the rounds keep the claim");
        }
        if i + 1 == n_levels {
            let mut fin = d.f.clone();
            for idx in 0..fin.len() {
                fix(Tamper::Final(idx), &mut fin, idx);
            }
            tr.absorb_e(&fin.iter().copied().map(fs_e).collect::<Vec<_>>());
            let pos = draw_positions(&mut tr, l);
            open_level(&mut tr, &cur, &pos, i, tamper);
            let (mut f, mut w) = (d.f[..1 << mu].to_vec(), d.w.clone());
            for round in 0..sh.tail_rounds {
                let (mut c0, mut c2) = (ZERO, ZERO);
                for k in 0..f.len() / 2 {
                    c0 += f[2 * k] * w[2 * k];
                    c2 += (f[2 * k] + f[2 * k + 1]) * (w[2 * k] + w[2 * k + 1]);
                }
                let mut sent = [c0, c2];
                fix(Tamper::Tail { round, idx: 0 }, &mut sent, 0);
                fix(Tamper::Tail { round, idx: 1 }, &mut sent, 1);
                tr.absorb_e(&sent.map(fs_e));
                let r = e_of(tr.ground(sh.grind_tail));
                claim = c0 + r * (claim + c2) + r * r * c2;
                let fold = |v: &[E]| v.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect::<Vec<E>>();
                (f, w) = (fold(&f), fold(&w));
            }
            if tamper.is_none() {
                assert_eq!(claim, f[0] * w[0], "the tail keeps the claim");
            }
            break;
        }
        // Commit the folded lane's low part, send its high part, the OOD point and value, then open level `i`.
        let mut high = d.f.split_off(1 << mu);
        let next = commit_e(&o, sh, i + 1, &d.f);
        fix(Tamper::High(i), &mut high, 0);
        tr.absorb_e(&high.iter().copied().map(fs_e).collect::<Vec<_>>());
        tr.absorb_cap(&flip_cap(i + 1, next.tree.cap()));
        tr.bind();
        let nl = &sh.levels[i + 1];
        let mut z = vec![e_of(tr.ground(nl.grind_ood))];
        z.extend(tr.draws(mu - 1).into_iter().map(e_of));
        let eqz = eq_table(&z);
        let y = d.f.iter().zip(&eqz).fold(ZERO, |a, (&f, &e)| a + f * e);
        let mut sent = [y];
        fix(Tamper::OodY(i), &mut sent, 0);
        tr.absorb_e(&sent.map(fs_e));
        let pos = draw_positions(&mut tr, l);
        let lambda = e_of(tr.draw());
        open_level(&mut tr, &cur, &pos, i, tamper);
        // Glue (`pcs::whir::glue`): `λ`·(eq(z), y), `λ²`·(Σ_q λ^q X_·(x_q), Σ_q λ^q P_low(x_q)).
        let sub = Subspace::new(mu);
        let l2 = lambda * lambda;
        let mut wq = l2;
        let mut add = vec![ZERO; 1 << mu];
        let mut enforced = ZERO;
        for &p in &pos {
            let basis = novel_basis(&sub.at(K(p as u64)), 1 << mu);
            enforced += wq * d.f.iter().zip(&basis).fold(ZERO, |a, (&f, &b)| a + f * b);
            for (x, &b) in add.iter_mut().zip(&basis) {
                *x += wq * b;
            }
            wq *= lambda;
        }
        claim += lambda * y + enforced;
        for ((w, &e), &a) in d.w.iter_mut().zip(&eqz).zip(&add) {
            *w += lambda * e + a;
        }
        d.stride = 1 << nl.fold;
        if tamper.is_none() {
            assert_eq!(claim, d.claim(), "level {i}: the glue keeps the claim");
        }
        cur = next;
    }

    let (body, trace) = tr.finish();
    let pi = [hdr, body].concat();
    let file = sign(cfg, &pi, trace.clone());
    Kat { vk, c, h, pi, trace, file }
}

/// The Kind P tamper set of a shape, each with the rejection `V_S` must give: every prover message class of the
/// frozen parts, at every level.
pub fn tamper_set(sh: &Shape) -> Vec<(Tamper, crate::Reject)> {
    use crate::Reject;
    let last = sh.levels.len() - 1;
    let mut cases: Vec<(Tamper, Reject)> = vec![
        (Tamper::Cap(0), Reject::MerkleCap(0)),
        (Tamper::Y0, Reject::Terminal),
        (Tamper::Final(0), Reject::FinalQuery),
        (Tamper::Final(sh.final_coeffs - 1), Reject::FinalQuery),
    ];
    for i in 0..sh.levels.len() {
        for idx in 0..4 {
            cases.push((Tamper::Fold { level: i, round: 0, idx }, Reject::Terminal));
        }
        cases.push((Tamper::Fold { level: i, round: sh.levels[i].fold - 1, idx: 3 }, Reject::Terminal));
        cases.push((Tamper::Leaf(i), Reject::MerkleCap(i)));
        cases.push((Tamper::Sibling(i), Reject::MerkleCap(i)));
        if i < last {
            cases.push((Tamper::Cap(i + 1), Reject::MerkleCap(i + 1)));
            cases.push((Tamper::High(i), Reject::Terminal));
            cases.push((Tamper::OodY(i), Reject::Terminal));
        }
    }
    for round in 0..sh.tail_rounds {
        for idx in 0..2 {
            cases.push((Tamper::Tail { round, idx }, Reject::Terminal));
        }
    }
    cases
}

fn draw_positions(tr: &mut Transcript, l: &crate::shape::Level) -> Vec<usize> {
    let mut draws = vec![tr.ground(l.grind_query)];
    draws.extend(tr.draws(l.position_draws() - 1));
    fs6::merkle::positions(&draws, l.ht, l.queries)
}

fn open_level(tr: &mut Transcript, cur: &Committed, pos: &[usize], i: usize, tamper: Option<Tamper>) {
    for (k, &p) in pos.iter().enumerate() {
        let (tl, ts) = (tamper == Some(Tamper::Leaf(i)), tamper == Some(Tamper::Sibling(i)));
        if k == 0 && (tl || ts) {
            let mut leaf = Vec::new();
            cur.leaf(p, &mut leaf);
            let mut sibs = cur.tree.siblings(p);
            if tl {
                leaf[0] ^= 1;
            } else {
                sibs[0][0] ^= 1;
            }
            tr.open_asked(p, &leaf, &sibs);
        } else {
            tr.open(&cur.tree, &[p], &|p, b: &mut Vec<u8>| cur.leaf(p, b));
        }
    }
}

/// The signed file of `π` with `trace`, under the toy key of `cfg.sign_seed`.
pub fn sign(cfg: &Cfg, pi: &[u8], trace: fs6::Trace) -> Vec<u8> {
    let (_, sig) = toy_sign(cfg.sign_seed, &trace_digest(&trace));
    to_file(&Signed { pi: pi.to_vec(), tr: trace, sig })
}

/// Kind R: `π'`'s trace re-derived from the oracle by walking `V_S` on it (up to the check that rejects), signed.
pub fn resign(cfg: &Cfg, vk: &Digest, c: &Digest, pi: &[u8]) -> Vec<u8> {
    let o = Local::keyed(&cfg.key);
    let mut ask = RecordAsk { o: &o, tr: Vec::new() };
    let _ = crate::vs::verify_pi(&cfg.sh, vk, c, pi, &mut ask, &mut crate::vs::NoStubs);
    sign(cfg, pi, ask.tr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith::novel_eval;

    /// The vendored NTT's codeword row `p` is the lanes' novel-basis polynomials at `K(p)` (FORMAT6 §5, RV2 F1:
    /// position `p` is the domain point `K.ofBits p`).
    #[test]
    fn ntt_position_is_domain_point() {
        let (m, r, rw) = (5usize, 2usize, 8usize);
        let msg: Vec<u64> = (0..(rw << m) as u64).map(mix).collect();
        let mut cw = vec![F64(0); rw << (m + r)];
        for (i, &x) in msg.iter().enumerate() {
            cw[i] = F64(x);
        }
        AdditiveNttF64::standard(m + r).encode_interleaved_in_place(&mut cw, rw, r);
        let sub = Subspace::new(m);
        for p in [0usize, 1, 2, 37, 100, 127] {
            let what = sub.at(K(p as u64));
            for lane in 0..rw {
                let coeffs: Vec<E> = (0..1 << m).map(|c| E::new(msg[c * rw + lane], 0)).collect();
                assert_eq!(E::new(cw[p * rw + lane].0, 0), novel_eval(&coeffs, &what), "p {p} lane {lane}");
            }
        }
    }
}
