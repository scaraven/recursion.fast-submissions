//! The node proof (revision 4.1 `N2`/`N4`/`N8`; BLUEPRINT §2.3 with the node's phases, A.9's node
//! finals as INT-8's `progNode` programs dump them): the prover, phase for phase in `seq4`'s item
//! order, on `node::witness`. The verifier is the dumped Lean program (`ir::run_node`) plus the
//! statement fact `stmtOk4` (`node_stmt(stmt[1..33], stmt[33..65]) = c`, checked after the run).
//!
//! What differs from the leaf (`leaf.rs`), phase by phase:
//! * **Z**: every block is used; `P^e` is the node's target (`nodeops::target_s_node4`).
//! * **Lc**: the summand is `Σ_κ η_κ(j)·zfold_κ(j)` over the seven H kinds (`η_κ` the transpose of
//!   the base matrix with the kind's pinned rows zeroed, `maskRows`) plus `free`'s `(1 + α)·rowW`;
//!   L3 sends `v_κ = zfold_κ(r_k)` (index `κ − 1`; `free` last).
//! * **Sh**: `Out` masked by `chainLk4`, `In` the masked successor with the two chain starts
//!   (`nodeops::shift_in_table`), and the eight link families (`κ_s^{f+2}`, source and mirror
//!   slots), all rank-one terms `e(y)·sw(p)` in one sumcheck; the collapse over positions `< 1024`.
//! * **Lr** (`2^logL` rows, the declared L bits `b·(one + b) = 0`) and **E2** (`2^logM` M rows) are
//!   degree-3 zerochecks of `eq(r,·)(a b + c)` in Gruen's form from claim 0; **E4** the lincheck
//!   `Σ_y W(y) f(y)` with `W = W_M(r_E2) + κ_E³ W_L(r_Lr)`, ending with `f̂(r′)`.
//! * **RS**: four claims, the Lc claim's outer weight carries the kind factor `kf4` (`β^{κ−1}` per
//!   block); **B′**: the nine public cells `f[cell_j] = pub_j` at `κ′^{j+2}` in Ligerito's weight.

use crate::blake2s::{node_stmt, Digest, TAG_NODE};
use crate::circuit::{Circuit, BLOCK};
use crate::field::{FAcc, F};
use crate::leaf::{self, Times};
use crate::mfill::{a1_h, KindTab, Proto, AR_A1, AR_N, AR_R1, SLOT};
use crate::node::spare_cell;
use crate::mle::eq_table;
use crate::node::{NodeWit, FAMS, NK};
use crate::oracle::Oracle;
use crate::params as pp;
use crate::skipdom::skip;
use crate::sumcheck::{coeffs_f, eval2_f, prove_pairs};
use crate::transcript::{Fs, Writer};
use crate::witness::Witness;
use crate::{ligerito, par, ringswitch, zerocheck};
use std::time::Instant;

/// `hdr = kindByte ‖ m ‖ 0^14 ‖ vk` (a node's `pub` is `vk`).
pub fn header(k: NK, vk: &Digest) -> Vec<u8> {
    let mut h = vec![0u8; pp::HDR_LEN];
    h[0] = k.byte();
    h[1] = k.m() as u8;
    h[16..48].copy_from_slice(vk);
    h
}

/// `stmt = tagNode ‖ c₀ ‖ c₁ ‖ 0^63`: the two signed children's statements.
pub fn stmt_bytes(c: &[Digest; 2]) -> Vec<u8> {
    let mut v = vec![0u8; 128];
    v[0] = TAG_NODE;
    v[1..33].copy_from_slice(&c[0]);
    v[33..65].copy_from_slice(&c[1]);
    v
}

/// The node's statement `c = stmtDigest(N, stmt)`.
pub fn node_c(c: &[Digest; 2]) -> Digest {
    node_stmt(&c[0], &c[1])
}

/// **`stmtOk4`** for any SNARK kind (INT-8: checked after the program's run): the statement field
/// `π[48..176)` hashed as the kind's statement (`N` for a node byte, `L` otherwise) equals `c`.
pub fn stmt_ok4(pi: &[u8], c: &Digest) -> bool {
    if pi.len() < 176 {
        return false;
    }
    let s = &pi[48..176];
    let h: Digest = s[1..33].try_into().unwrap();
    let d = if NK::of_byte(pi[0]).is_some() {
        node_stmt(&h, &s[33..65].try_into().unwrap())
    } else {
        crate::blake2s::leaf_stmt(&h, u64::from_le_bytes(s[33..41].try_into().unwrap()))
    };
    d == *c
}

/// The node's M rows (every slot's prototype rows moved, then the link rows) and L rows, for the
/// E2/E4 and Lr phases.
pub struct Mats<'a> {
    pub k: NK,
    pub kt: &'a KindTab,
    pub protos: &'a [Proto; 2],
}

impl Mats<'_> {
    /// `(A_M f, B_M f, C_M f)` over the `2^logM` M rows.
    pub fn m_matvec(&self, f: &[F]) -> [Vec<F>; 3] {
        let n = 1usize << self.k.log_m();
        let mut out: [Vec<F>; 3] = [vec![F::ZERO; n], vec![F::ZERO; n], vec![F::ZERO; n]];
        let one = self.kt.one_cell;
        let ptrs = [par::SyncPtr(out[0].as_mut_ptr()), par::SyncPtr(out[1].as_mut_ptr()), par::SyncPtr(out[2].as_mut_ptr())];
        for (v, &(pi, ..)) in self.kt.slots.iter().enumerate() {
            let p = &self.protos[pi];
            let base = pi * SLOT;
            par::map_chunks(p.rows.len(), 4096, |lo, hi| {
                let ptrs = &ptrs;
                for i in lo..hi {
                    let row = p.rows.idx[i] as usize - base + v * SLOT;
                    let rg = p.rows.rng[i];
                    for m in 0..3 {
                        // a coefficient 1 (most terms) is a plain sum, the rest unreduced products
                        let (mut acc, mut s1) = (FAcc::default(), F::ZERO);
                        for t in rg[m] as usize..rg[m + 1] as usize {
                            let x = f[one + p.rows.cells[t] as usize - base + v * SLOT];
                            match p.rows.coefs[t] {
                                crate::mfill::ONE_IX => s1 += x,
                                i => acc.mac(p.rows.cv[i as usize], x),
                            }
                        }
                        // SAFETY: the rows of one slot are distinct (`ProtoFit`), slots disjoint
                        unsafe { *ptrs[m].0.add(row) = acc.reduce() + s1 };
                    }
                }
            });
        }
        // P2: the arena₁ rows and slot 0's replay rows by their structure
        if let Some(x) = &self.kt.ext {
            let fo = f[one];
            for v in 0..x.vs {
                let (r, b0, lc) = (v * SLOT + AR_R1, x.a1_b0[v], one + v * SLOT + AR_A1);
                out[0][r..r + AR_N].fill(fo);
                par::for_each_chunk_mut(&mut out[1][r..r + AR_N], 1 << 12, |o, ch| ch.iter_mut().enumerate().for_each(|(i, y)| *y = f[lc + o + i] + f[a1_h(b0, o + i)]));
            }
            if x.spare {
                let (sp, vs) = (&self.protos[0].spare, x.vs);
                par::map_chunks(sp.len(), 4096, |lo, hi| {
                    let ptrs = &ptrs;
                    for i in lo..hi {
                        let row = vs * SLOT + sp.idx[i] as usize;
                        let rg = sp.rng[i];
                        for m in 0..3 {
                            let (mut acc, mut s1) = (FAcc::default(), F::ZERO);
                            for t in rg[m] as usize..rg[m + 1] as usize {
                                let y = f[spare_cell(one, vs, sp.cells[t] as usize)];
                                match sp.coefs[t] {
                                    crate::mfill::ONE_IX => s1 += y,
                                    c => acc.mac(sp.cv[c as usize], y),
                                }
                            }
                            // SAFETY: the spare rows are distinct (`spare_ix`) and in the spare slot
                            unsafe { *ptrs[m].0.add(row) = acc.reduce() + s1 };
                        }
                    }
                });
            }
        }
        let l = &self.kt.links;
        // the link rows in parallel (`node-N*.txt`'s; a full table's also E1b's rows)
        let lv = self.kt.links_eval(&|c| f[c]);
        for (i, v) in lv.iter().enumerate() {
            for m in 0..3 {
                out[m][l.idx[i] as usize] = v[m];
            }
        }
        out
    }

    /// `W[cell] += Σ_rows e[row]·(s₀ A + s₁ B + s₂ C)(row, cell)` over the M rows, as a gather by
    /// cell (pass 13: `ByCell`; every cell written once, `2^14`-cell chunks of every slot in
    /// parallel; per cell and matrix the terms with coefficient 1 summed, the others accumulated
    /// unreduced, then one product by `s_m`), the link rows after. `FLOCK_SCATTER_REF=1`:
    /// `m_scatter_ref`.
    pub fn m_scatter(&self, e: &[F], s: [F; 3], w: &mut [F]) {
        if std::env::var_os("FLOCK_SCATTER_REF").is_some() {
            return self.m_scatter_ref(e, s, w);
        }
        const CH: usize = 1 << 14;
        let one = self.kt.one_cell;
        let nslots = self.kt.slots.len();
        let nch = SLOT / CH;
        let wp = par::SyncPtr(w.as_mut_ptr());
        par::run(nslots * nch, &|j| {
            let wp = &wp;
            let (v, c0) = (j / nch, (j % nch) * CH);
            let p = &self.protos[self.kt.slots[v].0];
            let (bc, cv) = (p.by_cell(), &p.rows.cv);
            let eo = v * SLOT;
            for l in c0..c0 + CH {
                let (a, b) = (bc.ptr[l] as usize, bc.ptr[l + 1] as usize);
                if a == b {
                    continue;
                }
                let mut acc = [FAcc::default(); 3];
                let mut pl = [F::ZERO; 3];
                for q in a..b {
                    let en = bc.ent[q];
                    let (r, m) = ((en & 0x3FFF_FFFF) as usize, (en >> 30) as usize);
                    let x = e[eo + r];
                    match bc.coef[q] {
                        crate::mfill::ONE_IX => pl[m] += x,
                        i => acc[m].mac(cv[i as usize], x),
                    }
                }
                let mut sum = F::ZERO;
                for m in 0..3 {
                    let t = acc[m].reduce() + pl[m];
                    if !t.is_zero() {
                        sum += s[m] * t;
                    }
                }
                // SAFETY: cell `one + v·2^20 + l` is written by this chunk only
                unsafe { *wp.0.add(one + l + eo) += sum };
            }
        });
        self.links_scatter(e, s, w);
        self.ext_scatter(e, s, w);
    }

    /// P2: the factored rows' part of `m_scatter` (row by row; the debug check and the test).
    fn ext_scatter(&self, e: &[F], s: [F; 3], w: &mut [F]) {
        let Some(x) = &self.kt.ext else { return };
        let one = self.kt.one_cell;
        for v in 0..x.vs {
            for i in 0..AR_N {
                let r = e[v * SLOT + AR_R1 + i];
                w[one] += s[0] * r;
                w[one + v * SLOT + AR_A1 + i] += s[1] * r;
                w[a1_h(x.a1_b0[v], i)] += s[1] * r;
            }
        }
        if x.spare {
            let sp = &self.protos[0].spare;
            for i in 0..sp.len() {
                let r = e[x.vs * SLOT + sp.idx[i] as usize];
                let rg = sp.rng[i];
                for m in 0..3 {
                    for t in rg[m] as usize..rg[m + 1] as usize {
                        w[spare_cell(one, x.vs, sp.cells[t] as usize)] += r * s[m] * sp.coef(t);
                    }
                }
            }
        }
    }

    /// The link rows' part of `m_scatter`.
    fn links_scatter(&self, e: &[F], s: [F; 3], w: &mut [F]) {
        // by cell, in parallel (E1b; `m_scatter_ref` is the reference)
        let l = &self.kt.links;
        let r: Vec<F> = par::collect_vec(l.len(), 1 << 14, |i| e[l.idx[i] as usize]);
        let v = self.kt.links_cols(&r, &s);
        for (u, &c) in self.kt.links_by_cell().cells.iter().enumerate() {
            w[c as usize] += v[u];
        }
    }

    /// `m_scatter` row by row (pass 12's; slots in parallel: their cells are disjoint; the link rows
    /// after). The reference (P2: of a full table).
    pub fn m_scatter_ref(&self, e: &[F], s: [F; 3], w: &mut [F]) {
        assert!(self.kt.ext.is_none(), "m_scatter_ref: a full table");
        let one = self.kt.one_cell;
        let nslots = self.kt.slots.len();
        let wp = par::SyncPtr(w.as_mut_ptr());
        par::run(nslots, &|v| {
            let wp = &wp;
            let pi = self.kt.slots[v].0;
            let p = &self.protos[pi];
            let base = pi * SLOT;
            for i in 0..p.rows.len() {
                let row = p.rows.idx[i] as usize - base + v * SLOT;
                let er = e[row];
                if er.is_zero() {
                    continue;
                }
                let rg = p.rows.rng[i];
                for m in 0..3 {
                    let c = er * s[m];
                    for t in rg[m] as usize..rg[m + 1] as usize {
                        let cell = one + p.rows.cells[t] as usize - base + v * SLOT;
                        // SAFETY: slot `v`'s cells lie in its own region
                        unsafe { *wp.0.add(cell) += p.rows.cmul(t, c) };
                    }
                }
            }
        });
        let l = &self.kt.links;
        for i in 0..l.len() {
            let er = e[l.idx[i] as usize];
            let rg = l.rng[i];
            for m in 0..3 {
                for t in rg[m] as usize..rg[m + 1] as usize {
                    w[l.cells[t] as usize] += er * s[m] * l.coef(t);
                }
            }
        }
    }

    /// The L rows' bit cells (row `j` = the `j`-th declared bit, slot-major).
    pub fn l_cells(&self) -> Vec<usize> {
        let k = self.k;
        let mut v = Vec::with_capacity(k.vslots() * 8220);
        for s in 0..k.vslots() {
            for i in 0..8220 {
                v.push(k.l_base() * 128 + s * (1 << 14) + 299 + i);
            }
        }
        v
    }
}

/// `Z_κ(j) = Σ_blk eq(s_out, blk)·[kind(blk) = κ]·z(blk, j)` for the nine kinds (`kind` per block:
/// `BK::idx`), in one pass (most 8-block stripes hold one kind).
pub fn partial_fold_kinds(z: &[u64], s_out: &[F], kind: &[u8]) -> Vec<Vec<F>> {
    let nb = z.len() / 256;
    assert!(nb >= 8 && nb == 1 << s_out.len() && kind.len() == nb);
    let e = eq_table(s_out);
    let parts = par::map_chunks(nb / 8, 1, |lo, hi| {
        let mut acc: Vec<Vec<F>> = vec![Vec::new(); 9];
        let mut t = [F::ZERO; 256];
        for s in lo..hi {
            // a stripe of zero blocks adds nothing (`t[0] = 0`)
            if z[8 * s * 256..(8 * s + 8) * 256].iter().all(|&x| x == 0) {
                continue;
            }
            let ks = &kind[8 * s..8 * s + 8];
            let seen = ks.iter().fold(0u16, |a, &x| a | 1 << x);
            for kk in 0..9u8 {
                if (seen >> kk) & 1 == 0 {
                    continue;
                }
                t[0] = F::ZERO;
                for i in 0..8 {
                    let h = 1 << i;
                    let ei = if ks[i] == kk { e[8 * s + i] } else { F::ZERO };
                    for j in 0..h {
                        t[h + j] = t[j] + ei;
                    }
                }
                let a = &mut acc[kk as usize];
                if a.is_empty() {
                    *a = vec![F::ZERO; BLOCK];
                }
                crate::simd::pf_stripe(&z[8 * s * 256..(8 * s + 8) * 256], &t, a);
            }
        }
        acc
    });
    let mut out = vec![vec![F::ZERO; BLOCK]; 9];
    for p in parts {
        for (kk, a) in p.into_iter().enumerate() {
            if !a.is_empty() {
                crate::simd::axpy(&mut out[kk], &a, F::ONE);
            }
        }
    }
    out
}

/// `Σ_{s < 8·nbytes} eq(θ, s)·z[blk, base + s]` for every block (`t` = `leaf::theta_tables`, `base`
/// a multiple of 8).
fn collapse_n(z: &[u64], t: &[F], base: usize, nbytes: usize) -> Vec<F> {
    let bytes = Witness::bytes(z);
    let nb = z.len() / 256;
    par::collect_vec(nb, 1 << 10, |b| {
        let o = b * 2048 + base / 8;
        let mut acc = F::ZERO;
        for p in 0..nbytes {
            acc += t[p * 256 + bytes[o + p] as usize];
        }
        acc
    })
}

/// `collapse_n` for every key at once (pass 12; `collapse_n` is the reference): one pass over the
/// blocks, a key's bytes skipped when they are all zero (a zero byte's table entry is 0; a third of
/// a node's blocks are zero). `cols[i][blk]` for key `i`.
fn collapse_keys(z: &[u64], t: &[F], keys: &[(usize, usize)]) -> Vec<Vec<F>> {
    let bytes = Witness::bytes(z);
    let nb = z.len() / 256;
    let mut cols: Vec<Vec<F>> = keys.iter().map(|_| par::uninit_vec(nb)).collect();
    let ptrs: Vec<par::SyncPtr<F>> = cols.iter_mut().map(|c| par::SyncPtr(c.as_mut_ptr())).collect();
    par::map_chunks(nb, 1 << 10, |lo, hi| {
        for b in lo..hi {
            for (i, &(base, n)) in keys.iter().enumerate() {
                let o = b * 2048 + base / 8;
                let src = &bytes[o..o + n];
                let mut acc = F::ZERO;
                if !zerocheck::zero_bytes(src) {
                    for (p, &v) in src.iter().enumerate() {
                        acc += t[p * 256 + v as usize];
                    }
                }
                unsafe { *ptrs[i].0.add(b) = acc };
            }
        }
    });
    cols
}

/// One degree-3 zerocheck of `Σ_x eq(r, x)·(a(x) b(x) + c(x)) = claim₀` in Gruen's form (the leaf's Z3
/// rounds, with a linear `c`; `c = None` for `c ≡ 0`): the messages through `send`, the challenges
/// from `chal`. Returns the challenges and `(â, b̂, ĉ)`.
fn zc_abc(r: &[F], a: Vec<F>, b: Vec<F>, c: Option<Vec<F>>, claim0: F, step: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, [F; 3]) {
    let (xs, v, _) = zc_abc_x(r, a, b, c, claim0, None, step);
    (xs, v)
}

/// The extra product of `zc_abc_x`: `P = η·eq(p, ·)` in closed form (P2: never a table) and `Q`.
struct EqProd {
    p: Vec<F>,
    pre: F,
    q: Vec<F>,
}

impl EqProd {
    /// Round `k`'s message `(g(0), g(1), g(∞))` of `Σ_x P(x) Q(x)` with `P = pre·eq(p[k..], ·)`:
    /// `pre·((1 + p_k) D₀, p_k D₁, D₀ + D₁)`, `D_b = Σ_i eq(p[k+1..], i) Q(2i + b)` (the split eq table's
    /// low half doubled, `lo2[2l] = lo2[2l + 1] = lo[l]`, so that `round_ff(Q, lo2)` gives `(D₀, D₁, 0)`
    /// per high block). The same message as `msg_pairs` on `P`'s table.
    fn msg(&self, k: usize) -> [F; 3] {
        let es = zerocheck::EqSplit::new(&self.p[k + 1..]);
        let lo2: Vec<F> = es.lo.iter().flat_map(|&x| [x, x]).collect();
        let bl = lo2.len();
        let q = &self.q;
        let parts = par::map_chunks(es.hi.len(), 1, |lo, hi| {
            let (mut d0, mut d1) = (FAcc::default(), FAcc::default());
            for h in lo..hi {
                let r = crate::simd::round_ff(&q[h * bl..(h + 1) * bl], &lo2);
                d0.mac(es.hi[h], r[0]);
                d1.mac(es.hi[h], r[1]);
            }
            (d0.reduce(), d1.reduce())
        });
        let (d0, d1) = parts.into_iter().fold((F::ZERO, F::ZERO), |a, x| (a.0 + x.0, a.1 + x.1));
        let pk = self.p[k];
        [self.pre * (F::ONE + pk) * d0, self.pre * pk * d1, self.pre * (d0 + d1)]
    }
    /// Bind variable `k` at `x`.
    fn fold(&mut self, k: usize, x: F) {
        let pk = self.p[k];
        self.pre *= (F::ONE + pk) * (F::ONE + x) + pk * x;
        self.q = crate::sumcheck::fold_f(&self.q, x);
    }
}

/// `zc_abc` plus an extra degree-2 product `Σ_x P(x) Q(x)` (RSV2's E2: `P = η·eq(p_x, ·)`, `Q` the
/// child claim's table minus `X`) in the same rounds: each message is the sum of both parts' (the
/// verifier completes `c₃` from the total claim). Also returns the extra pair's final `(P, Q)`.
#[allow(clippy::type_complexity)]
fn zc_abc_x(r: &[F], mut a: Vec<F>, mut b: Vec<F>, mut c: Option<Vec<F>>, claim0: F, mut extra: Option<EqProd>, step: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, [F; 3], (F, F)) {
    let n = r.len();
    assert_eq!(a.len(), 1 << n);
    let mut claim = claim0;
    let mut pref = F::ONE;
    let mut xs = Vec::with_capacity(n);
    for kk in 0..n {
        let rest = &r[kk + 1..];
        let (mut h1, hi) = zerocheck::round_tab(&a, &b, rest, a.len());
        if let Some(c) = &c {
            let es = zerocheck::EqSplit::new(rest);
            let parts = par::map_chunks(es.hi.len(), 1, |lo, hh| {
                let mut acc = FAcc::default();
                for h in lo..hh {
                    // a zero stretch of c adds nothing (the holes after each slot's rows; pass 12)
                    let blk = &c[2 * (h << es.nlo)..2 * ((h + 1) << es.nlo)];
                    if blk.iter().all(|x| x.is_zero()) {
                        continue;
                    }
                    let mut inner = FAcc::default();
                    for (l, el) in es.lo.iter().enumerate() {
                        inner.mac(*el, c[2 * ((h << es.nlo) | l) + 1]);
                    }
                    acc.mac(es.hi[h], inner.reduce());
                }
                acc
            });
            for p in parts {
                h1 += p.reduce();
            }
        }
        let h0 = zerocheck::h0_from_claim(claim, r[kk], h1);
        let mut msg = zerocheck::zc_coeffs(pref, r[kk], h0, h1, hi);
        if let Some(e) = &extra {
            let g = coeffs_f(e.msg(kk));
            for j in 0..3 {
                msg[j] += g[j];
            }
        }
        let x = step(msg);
        claim = eval2_f([h0, h1, hi], x);
        pref *= F::ONE + r[kk] + x;
        xs.push(x);
        a = crate::sumcheck::fold_f_sparse(&a, x);
        b = crate::sumcheck::fold_f_sparse(&b, x);
        if let Some(cc) = c.as_mut() {
            *cc = crate::sumcheck::fold_f_sparse(cc, x);
        }
        if let Some(e) = extra.as_mut() {
            e.fold(kk, x);
        }
    }
    let cv = c.map(|c| c[0]).unwrap_or(F::ZERO);
    assert_eq!(claim, a[0] * b[0] + cv);
    (xs, [a[0], b[0], cv], extra.map(|e| (e.pre, e.q[0])).unwrap_or((F::ZERO, F::ZERO)))
}

/// **`FRVerifierC4.rsvRel`**: the 60 M-relative cells (prototype 0, the previous node's slot) of the
/// child claim's values: the packed mixed row point `x̂` (23; entry 22 the kind-muxed cell), `ŷ`
/// (25), the nine coefficients `s^P`, the three outputs of the child's one `evalM` call.
pub const RSV_REL: [usize; 60] = [
    1318, 1329, 1340, 1351, 1362, 1373, 1384, 1395, 1406, 1417, 1428, 1439, 1450, 1461, 1472, 1483, 1494, 1505, 1516, 1527,
    1538, 1549, 116596, 1579, 1589, 1599, 1609, 1619, 1629, 1639, 1649, 1659, 1669, 1679, 1689, 1699, 1709, 1719, 1729,
    1739, 1749, 1759, 1769, 1779, 1789, 1799, 1809, 116600, 116584, 116585, 116586, 116587, 116588, 116589, 116590,
    116591, 116592, 116601, 116602, 116603,
];

/// RSV2's child claim `(p_x, p_y, s, X₃)` (`fLrEnd[48, 1008)`): a node with a previous node copies
/// the previous node's one `evalM` call (its slot-0 cells `rsvCells`); `N8`'s is zero.
pub fn child_claim(k: NK, f: &[F]) -> Vec<F> {
    if !k.has_prev() {
        return vec![F::ZERO; 60];
    }
    RSV_REL.iter().map(|&r| f[k.one_cell() + r]).collect()
}

fn kind_of(ix: usize) -> NK {
    [NK::N2, NK::N4, NK::N8][ix]
}

/// Per prototype `π` and matrix `m`: `U_{π,m}(l) = Σ_c M_{π,m}(l, c)·e(c)` over the region's `2^20`
/// local rows, `e` over its local cells (a slot's rows and cells are its prototype's moved by
/// `v·2^20`, so with `e = eq(p_lo, ·)` every slot of every kind shares `U`).
fn proto_matvec(p: &Proto, elo: &[F]) -> [Vec<F>; 3] {
    let base = p.pi * SLOT;
    let mut out: [Vec<F>; 3] = [vec![F::ZERO; SLOT], vec![F::ZERO; SLOT], vec![F::ZERO; SLOT]];
    let ptrs = [par::SyncPtr(out[0].as_mut_ptr()), par::SyncPtr(out[1].as_mut_ptr()), par::SyncPtr(out[2].as_mut_ptr())];
    par::map_chunks(p.rows.len(), 4096, |lo, hi| {
        let ptrs = &ptrs;
        for i in lo..hi {
            let row = p.rows.idx[i] as usize - base;
            let rg = p.rows.rng[i];
            for m in 0..3 {
                let (mut acc, mut s1) = (FAcc::default(), F::ZERO);
                for t in rg[m] as usize..rg[m + 1] as usize {
                    let x = elo[p.rows.cells[t] as usize - base];
                    match p.rows.coefs[t] {
                        crate::mfill::ONE_IX => s1 += x,
                        c => acc.mac(p.rows.cv[c as usize], x),
                    }
                }
                // SAFETY: a prototype's rows are distinct
                unsafe { *ptrs[m].0.add(row) = acc.reduce() + s1 };
            }
        }
    });
    out
}

/// Per prototype `π` and matrix `m`: `T_{π,m}(c) = Σ_l e(l)·M_{π,m}(l, c)` over the region's `2^20`
/// local cells (`ByCell`'s gather), `e` over its local rows.
fn proto_scatter(p: &Proto, elo: &[F]) -> [Vec<F>; 3] {
    let bc = p.by_cell();
    let cv = &p.rows.cv;
    let mut out: [Vec<F>; 3] = [par::uninit_vec(SLOT), par::uninit_vec(SLOT), par::uninit_vec(SLOT)];
    let ptrs = [par::SyncPtr(out[0].as_mut_ptr()), par::SyncPtr(out[1].as_mut_ptr()), par::SyncPtr(out[2].as_mut_ptr())];
    par::map_chunks(SLOT, 1 << 14, |lo, hi| {
        let ptrs = &ptrs;
        for l in lo..hi {
            let (a, b) = (bc.ptr[l] as usize, bc.ptr[l + 1] as usize);
            let mut acc = [FAcc::default(); 3];
            let mut pl = [F::ZERO; 3];
            for q in a..b {
                let en = bc.ent[q];
                let (r, m) = ((en & 0x3FFF_FFFF) as usize, (en >> 30) as usize);
                let x = elo[r];
                match bc.coef[q] {
                    crate::mfill::ONE_IX => pl[m] += x,
                    i => acc[m].mac(cv[i as usize], x),
                }
            }
            for m in 0..3 {
                // SAFETY: cell `l` is written by this chunk only
                unsafe { *ptrs[m].0.add(l) = acc[m].reduce() + pl[m] };
            }
        }
    });
    out
}

/// `Σ_m s_m·V_m` elementwise (P2: by the vector kernel `axpy`).
fn comb3(v: &[Vec<F>; 3], s: &[F]) -> Vec<F> {
    let mut out: Vec<F> = par::uninit_vec(v[0].len());
    par::for_each_chunk_mut(&mut out, 1 << 14, |o, ch| {
        ch.fill(F::ZERO);
        for m in 0..3 {
            crate::simd::axpy(ch, &v[m][o..o + ch.len()], s[m]);
        }
    });
    out
}

/// Where entry `pos` of a kind's table of `kl` entries lands in the parent's `n` (RSV2's constant
/// extension): equal sizes the same entry; one more coordinate folded at `p` (the parent's entry
/// `pos mod n` with weight `p` or `1 + p` by the top bit); one fewer duplicated over the top bit.
fn land(n: usize, kl: usize, pos: usize, p: F) -> [(usize, F); 2] {
    if kl == n {
        [(pos, F::ONE), (usize::MAX, F::ZERO)]
    } else if kl == 2 * n {
        if pos >= n { [(pos - n, p), (usize::MAX, F::ZERO)] } else { [(pos, F::ONE + p), (usize::MAX, F::ZERO)] }
    } else {
        assert_eq!(2 * kl, n);
        [(pos, F::ONE), (pos + kl, F::ONE)]
    }
}

/// `d[land(pos(i))] += val(i)` for `n` items at distinct positions `pos(i) < kl` (E1b: in parallel, in
/// two passes when a kind with twice the rows folds its upper half onto the lower one).
fn land_items(d: &mut [F], kl: usize, p: F, n: usize, item: &(dyn Fn(usize) -> (usize, F) + Sync)) {
    let nd = d.len();
    let dp = par::SyncPtr(d.as_mut_ptr());
    for pass in 0..1 + (kl == 2 * nd) as usize {
        par::map_chunks(n, 1 << 14, |lo, hi| {
            let dp = &dp;
            for i in lo..hi {
                let (pos0, v) = item(i);
                if kl == 2 * nd && (pos0 >= nd) != (pass == 1) {
                    continue;
                }
                for (pos, w) in land(nd, kl, pos0, p) {
                    if pos != usize::MAX {
                        // SAFETY: distinct items land on distinct positions within a pass
                        unsafe { *dp.0.add(pos) += w * v };
                    }
                }
            }
        });
    }
}

/// `d[land(off + i)] += c·v[i]` for a contiguous run (a slot: `2^20` entries never straddle the top bit).
fn add_run(d: &mut [F], kl: usize, off: usize, c: F, v: &[F], p: F) {
    for (pos, w) in land(d.len(), kl, off, p) {
        if pos == usize::MAX {
            continue;
        }
        let cw = c * w;
        par::for_each_chunk_mut(&mut d[pos..pos + v.len()], 1 << 14, |o, ch| crate::simd::axpy(ch, &v[o..o + ch.len()], cw));
    }
}

/// `Σ_{κ,m} s_{κ,m}·M̃_{κ,m}(x ‖ p_x[n, 23), p_y)` over the parent's `2^n` rows `x` (RSV2 §2.3). Each
/// kind is read at its own `logM κ` row and `logM κ + 2` column coordinates (a kind with more rows is
/// folded at `p_x[n]`, one with fewer is constant in the top coordinate). Factorized: slot `v`'s rows
/// are `eq(p_y[20..], one/2^20 + v)·U_π` (`proto_matvec` at `eq(p_y[<20])`, once per prototype for every
/// kind), then (P2) the kind's arena₁ rows slot by slot and slot 0's replay rows from prototype 0's
/// spare sums (`spare_matvec`, once for every kind), then its link rows.
fn child_rows(kts: &[&KindTab; 3], protos: &[Proto; 2], px: &[F], py: &[F], s: &[F], n: usize) -> Vec<F> {
    let mut d = vec![F::ZERO; 1 << n];
    let elo = eq_table(&py[..20]);
    let us: [std::sync::OnceLock<[Vec<F>; 3]>; 2] = [std::sync::OnceLock::new(), std::sync::OnceLock::new()];
    let usp: std::sync::OnceLock<[[Vec<F>; 3]; 2]> = std::sync::OnceLock::new();
    let p = px.get(n).copied().unwrap_or(F::ZERO);
    for (kk, kt) in kts.iter().enumerate() {
        let sk = &s[3 * kk..3 * kk + 3];
        if sk.iter().all(|x| x.is_zero()) {
            continue;
        }
        let kl = 1usize << kt.log_m;
        let hs = eq_table(&py[20..kt.log_m + 2]);
        let ob = kt.one_cell / SLOT;
        for pi in 0..2 {
            if kt.slots.iter().any(|sl| sl.0 == pi) {
                let _sp = crate::prof::span("cr.proto");
                us[pi].get_or_init(|| proto_matvec(&protos[pi], &elo));
            }
        }
        let sp = crate::prof::span("cr.runs");
        let cb: [Option<Vec<F>>; 2] = [0, 1].map(|pi| kt.slots.iter().any(|sl| sl.0 == pi).then(|| comb3(us[pi].get().unwrap(), sk)));
        for (v, sl) in kt.slots.iter().enumerate() {
            add_run(&mut d, kl, v * SLOT, hs[ob + v], cb[sl.0].as_ref().unwrap(), p);
        }
        drop(sp);
        let es = crate::nodeops::EqSplit::new(&py[..kt.log_m + 2]);
        if let Some(x) = &kt.ext {
            let _sp = crate::prof::span("lk.ext_rows");
            // arena₁ row `v·2^20 + AR_R1 + e`: `s₀·eq(p_y, one) + s₁·(eq(p_y, A₁ cell) + eq(p_y, H cell))`
            let c0 = sk[0] * es.at(kt.one_cell);
            for v in 0..x.vs {
                let (c1, b0) = (sk[1] * hs[ob + v], x.a1_b0[v]);
                let val: Vec<F> = par::collect_vec(AR_N, 1 << 12, |e| c0 + c1 * elo[AR_A1 + e] + sk[1] * es.at(a1_h(b0, e)));
                add_run(&mut d, kl, v * SLOT + AR_R1, F::ONE, &val, p);
            }
            if x.spare {
                let ix = protos[0].spare_ix();
                let [fr, lo] = usp.get_or_init(|| spare_matvec(&protos[0], &elo));
                let (a, b) = (sk.iter().map(|&y| y * hs[ob]).collect::<Vec<F>>(), sk.iter().map(|&y| y * hs[ob + x.vs]).collect::<Vec<F>>());
                let val: Vec<F> = par::collect_vec(ix.nr, 1 << 12, |l| a[0] * fr[0][l] + a[1] * fr[1][l] + a[2] * fr[2][l] + b[0] * lo[0][l] + b[1] * lo[1][l] + b[2] * lo[2][l]);
                add_run(&mut d, kl, x.vs * SLOT + ix.r0, F::ONE, &val, p);
            }
        }
        let l = &kt.links;
        let sp = crate::prof::span("lk.eval");
        let lv = kt.links_eval(&|c| es.at(c));
        drop(sp);
        let _sp = crate::prof::span("lk.landr");
        land_items(&mut d, kl, p, l.len(), &|i| (l.idx[i] as usize, sk[0] * lv[i][0] + sk[1] * lv[i][1] + sk[2] * lv[i][2]));
    }
    d
}

/// P2: prototype 0's spare rows at the column table `elo` (`eq(·_{<20})`), per matrix, over their local
/// row span (`SpareIx`): the frame terms (`elo[c]`) and the local ones (`elo[c − 2^20]`) apart.
fn spare_matvec(p0: &Proto, elo: &[F]) -> [[Vec<F>; 3]; 2] {
    let (sp, ix) = (&p0.spare, p0.spare_ix());
    let mut out: [[Vec<F>; 3]; 2] = std::array::from_fn(|_| std::array::from_fn(|_| vec![F::ZERO; ix.nr]));
    let ptrs: [[par::SyncPtr<F>; 3]; 2] = std::array::from_fn(|g| std::array::from_fn(|m| par::SyncPtr(out[g][m].as_mut_ptr())));
    par::map_chunks(sp.len(), 4096, |lo, hi| {
        let ptrs = &ptrs;
        for i in lo..hi {
            let row = sp.idx[i] as usize - ix.r0;
            let rg = sp.rng[i];
            for m in 0..3 {
                let (mut acc, mut s1) = ([FAcc::default(); 2], [F::ZERO; 2]);
                for t in rg[m] as usize..rg[m + 1] as usize {
                    let c = sp.cells[t] as usize;
                    let g = (c >= SLOT) as usize;
                    let y = elo[c - g * SLOT];
                    match sp.coefs[t] {
                        crate::mfill::ONE_IX => s1[g] += y,
                        q => acc[g].mac(sp.cv[q as usize], y),
                    }
                }
                for g in 0..2 {
                    // SAFETY: the spare rows are distinct (`spare_ix`)
                    unsafe { *ptrs[g][m].0.add(row) = acc[g].reduce() + s1[g] };
                }
            }
        }
    });
    out
}

/// E4's prototype tables at `eq(r_E2[<20])`: `T_π` (`proto_scatter`) per prototype read, and (P2)
/// prototype 0's spare columns (`cols3` per distinct spare cell) when a kind read has them.
struct E4Tabs<'a> {
    elo: &'a [F],
    ts: [Option<[Vec<F>; 3]>; 2],
    tsp: Option<Vec<[F; 3]>>,
    p0: &'a Proto,
}

/// The own kind's `W_M(r_E2) = Σ_{rows} eq(r_E2, row)·(s₀A + s₁B + s₂C)(row, ·)` into `w` (`m_scatter`'s
/// value): slot `v`'s cells are `eq(r_E2[20..], v)·Σ_m s_m T_{π,m}`, then the factored and the link rows.
fn own_w_m(kt: &KindTab, tb: &E4Tabs, r_e2: &[F], s: [F; 3], w: &mut [F]) {
    add_cols(kt, tb, r_e2, &s, w, F::ZERO);
}

/// `w[land(cell)] += Σ_rows eq(xh[<logM], row)·(Σ_m s_m M_m)(row, cell)` over a kind's rows (slot by
/// slot from `T_π = proto_scatter(eq(xh[<20]))`; P2: the arena₁ rows slot by slot, slot 0's replay
/// rows from the spare columns; then its link rows), landed in `w`'s cell space.
fn add_cols(kt: &KindTab, tb: &E4Tabs, xh: &[F], s: &[F], w: &mut [F], p: F) {
    let kl = 1usize << (kt.log_m + 2);
    let ht = eq_table(&xh[20..kt.log_m]);
    let sp = crate::prof::span("lk.comb3");
    let cb: [Option<Vec<F>>; 2] = [0, 1].map(|pi| kt.slots.iter().any(|sl| sl.0 == pi).then(|| comb3(tb.ts[pi].as_ref().unwrap(), s)));
    drop(sp);
    let sp = crate::prof::span("lk.protorun");
    for (v, sl) in kt.slots.iter().enumerate() {
        add_run(w, kl, kt.one_cell + v * SLOT, ht[v], cb[sl.0].as_ref().unwrap(), p);
    }
    drop(sp);
    if let Some(x) = &kt.ext {
        let _sp = crate::prof::span("lk.ext_cols");
        let one = kt.one_cell;
        // arena₁: row weight `ht[v]·elo[AR_R1 + e]`; A the one cell, B the A₁ and the H cell
        let er = &tb.elo[AR_R1..AR_R1 + AR_N];
        let se = er.iter().fold(F::ZERO, |a, &y| a + y);
        let hsum = (0..x.vs).fold(F::ZERO, |a, v| a + ht[v]);
        let nw = w.len();
        for (pos, wt) in land(nw, kl, one, p) {
            if pos != usize::MAX {
                w[pos] += wt * s[0] * hsum * se;
            }
        }
        for v in 0..x.vs {
            let c = s[1] * ht[v];
            add_run(w, kl, one + v * SLOT + AR_A1, c, er, p);
            let b0 = x.a1_b0[v];
            // a slot's H cells are distinct and span < 2^22 cells, so their landings are distinct
            let wp = par::SyncPtr(w.as_mut_ptr());
            par::map_chunks(AR_N, 1 << 12, |lo, hi| {
                let wp = &wp;
                for e in lo..hi {
                    let y = c * er[e];
                    for (pos, wt) in land(nw, kl, a1_h(b0, e), p) {
                        if pos != usize::MAX {
                            // SAFETY: distinct positions (above)
                            unsafe { *wp.0.add(pos) += wt * y };
                        }
                    }
                }
            });
        }
        if x.spare {
            let (ix, t) = (tb.p0.spare_ix(), tb.tsp.as_ref().unwrap());
            let cs: Vec<F> = s.iter().map(|&y| y * ht[x.vs]).collect();
            let cells = &ix.bc.cells;
            land_items(w, kl, p, cells.len(), &|u| (spare_cell(one, x.vs, cells[u] as usize), cs[0] * t[u][0] + cs[1] * t[u][1] + cs[2] * t[u][2]));
        }
    }
    let et = crate::nodeops::EqSplit::new(&xh[..kt.log_m]);
    let l = &kt.links;
    // by cell, in parallel (E1b), then landed
    let sp = crate::prof::span("lk.bycell");
    let _ = kt.links_by_cell();
    drop(sp);
    let sp = crate::prof::span("lk.r");
    let r: Vec<F> = par::collect_vec(l.len(), 1 << 14, |i| et.at(l.idx[i] as usize));
    drop(sp);
    let sp = crate::prof::span("lk.cols");
    let v = kt.links_cols(&r, s);
    drop(sp);
    let _sp = crate::prof::span("lk.land");
    let cells = &kt.links_by_cell().cells;
    land_items(w, kl, p, cells.len(), &|u| (cells[u] as usize, v[u]));
}

/// `Σ_{κ,m} s_{κ,m}·M̃_{κ,m}(x̂, y ‖ p_y[n, 25))` over the parent's `2^n` cells `y` (E4's child term,
/// `tb` shared with the own scatter).
fn child_cols(kts: &[&KindTab; 3], tb: &E4Tabs, xh: &[F], py: &[F], s: &[F], n: usize) -> Vec<F> {
    let mut g: Vec<F> = par::uninit_vec(1 << n);
    par::for_each_chunk_mut(&mut g, 1 << 16, |_, c| c.fill(F::ZERO));
    let p = py.get(n).copied().unwrap_or(F::ZERO);
    for (kk, kt) in kts.iter().enumerate() {
        let sk = &s[3 * kk..3 * kk + 3];
        if !sk.iter().all(|x| x.is_zero()) {
            let _sp = crate::prof::span(["cc.N2", "cc.N4", "cc.N8"][kk]);
            add_cols(kt, tb, xh, sk, &mut g, p);
        }
    }
    g
}

/// The node prover's inputs besides the oracle.
pub struct NodeIn<'a> {
    pub k: NK,
    pub vk: Digest,
    /// The two signed children's statements (`stmt`'s `c₀`, `c₁`).
    pub cs: [Digest; 2],
    pub w: &'a NodeWit,
    pub mats: Mats<'a>,
    /// The three kinds' tables (`N2`, `N4`, `N8`), for RSV2's child claim.
    pub kts: [&'a KindTab; 3],
    /// The base block matrix (`Circuit::build_base`).
    pub base: &'a Circuit,
}

/// **The node prover**: `π` (`piSize` bytes) and the phase times.
pub fn prove(o: &dyn Oracle, ni: &NodeIn) -> (Vec<u8>, Times) {
    let (k, w) = (ni.k, ni.w);
    let m = k.m();
    let nb = m - 14;
    let blocks = k.blocks();
    let mut tm = Times::default();
    let mut t = Instant::now();
    let hdr = header(k, &ni.vk);
    let c = node_c(&ni.cs);
    let f = leaf::packed(&w.z);
    let c0 = ligerito::commit0(o, f, m);
    tm.mark("commit0", &mut t);
    let mut wr = Writer::new(Fs::seed(o, &ni.vk, &c, &hdr, false), &hdr);
    wr.fs.phase = "stmt";
    wr.send(pp::F_STMT, &stmt_bytes(&ni.cs));
    wr.fs.phase = "cap0";
    wr.send(pp::F_CAPS, &ligerito::cap_slot(0, c0.tree.cap()));

    // ---- Z (every block used; the node's target)
    let sk = skip();
    wr.fs.phase = "Z1";
    let co = wr.fs.coords(pp::Z1_SQ);
    let r_out = &co[..m - 13];
    let mut r: Vec<F> = sk.rho.to_vec();
    r.extend_from_slice(r_out);
    let (ab, bb, zb) = (Witness::bytes(&w.a), Witness::bytes(&w.b), Witness::bytes(&w.z));
    let r1 = zerocheck::round1(ab, bb, zb, r_out, blocks);
    let pz = zerocheck::pz_on_lambda(&r1);
    let mut msg = pz.to_vec();
    msg.extend_from_slice(&r1.pab[..63]);
    msg.push(F::ZERO);
    wr.fs.phase = "Z2";
    wr.send_f(pp::F_Z2, &msg);
    let lambda = wr.fs.chal_f();
    let pe = crate::nodeops::target_s_node4(k, r_out);
    let (mut claim, _pz_l) = leaf::z2_value_pe(&pz, &r1.pab[..63], &pe, lambda);
    let (i0, i1) = ((F::ONE + sk.rho[0]).inv(), sk.rho[0].inv());
    let mut s0v = vec![F::ZERO; 128];
    for sg in 0..64 {
        s0v[sg] = r1.bank[0][sg] * i0;
        s0v[64 + sg] = r1.bank[1][sg] * i1;
    }
    tm.mark("zc_round1", &mut t);
    wr.fs.phase = "Z3";
    let tabs = zerocheck::fold_tables(lambda);
    let mut pref = F::ONE;
    let mut sz = Vec::with_capacity(m - 6);
    let (mut ta, mut tb) = (Vec::new(), Vec::new());
    for kk in 0..m - 6 {
        let (h1, hi) = if kk == 0 { zerocheck::round_x6(&tabs, ab, bb, &r[1..], blocks) } else { zerocheck::round_tab(&ta, &tb, &r[kk + 1..], ta.len()) };
        let h0 = zerocheck::h0_from_claim(claim, r[kk], h1);
        wr.send_f(pp::F_Z3, &zerocheck::zc_coeffs(pref, r[kk], h0, h1, hi));
        let x = wr.fs.chal_f();
        claim = eval2_f([h0, h1, hi], x);
        pref *= F::ONE + r[kk] + x;
        sz.push(x);
        if kk == 0 {
            ta = zerocheck::fold_x6(&tabs, ab, x, blocks);
            tb = zerocheck::fold_x6(&tabs, bb, x, blocks);
        } else {
            ta = crate::sumcheck::fold_f_sparse(&ta, x);
            tb = crate::sumcheck::fold_f_sparse(&tb, x);
        }
    }
    leaf::dummy_rounds(&mut wr, pp::F_Z3, pp::Z3_ROUNDS - (m - 6), 48);
    let (va, vb) = (ta[0], tb[0]);
    assert_eq!(claim, va * vb);
    drop((ta, tb));
    wr.fs.phase = "Zend";
    wr.send_f(pp::F_ZEND, &[va, vb]);
    tm.mark("zc_tail", &mut t);

    // ---- Lc: the seven H kinds and `free`
    wr.fs.phase = "L1";
    let alpha = wr.fs.chal_f();
    wr.fs.phase = "L2";
    let kinds: Vec<u8> = w.bks.iter().map(|b| b.idx() as u8).collect();
    let zf = partial_fold_kinds(&w.z, &sz[8..], &kinds);
    let rw = crate::lincheck::row_weights(lambda, &sz[..8]);
    let mut pairs: Vec<(Vec<F>, Vec<F>)> = Vec::with_capacity(8);
    for kk in 1..=7usize {
        let mut kw = vec![F::ZERO; 9];
        kw[kk] = F::ONE;
        let wm = crate::ir::mask_rows(&kw, &rw);
        let wa: Vec<F> = wm.iter().map(|x| *x * alpha).collect();
        pairs.push((ni.base.transpose(&wm, &wa), zf[kk].clone()));
    }
    let a1 = F::ONE + alpha;
    pairs.push((rw.iter().map(|x| *x * a1).collect(), zf[8].clone()));
    assert_eq!(pairs.iter().map(|(p, q)| leaf::dot(p, q)).fold(F::ZERO, |a, b| a + b), va + alpha * vb, "Lc's sum");
    let (tl, fin) = prove_pairs(pairs, &mut |g| {
        wr.send_f(pp::F_L2, &coeffs_f(g));
        wr.fs.chal_f()
    });
    let vk8: Vec<F> = fin.iter().map(|x| x.1).collect();
    wr.fs.phase = "L3";
    wr.send_f(pp::F_L2, &vk8);
    wr.fs.phase = "L3β";
    let beta = wr.fs.chal_f();
    tm.mark("lincheck", &mut t);

    // ---- Sh: Out, In (masked by chainLk4, the chain starts), the link families; then the collapse
    wr.fs.phase = "S1";
    let co = wr.fs.coords(pp::S1_SQ);
    let (tau, theta, kap_s) = (&co[..nb], &co[pp::S1_THETA..pp::S1_THETA + pp::THETA_LEN], co[pp::S1_KAPPA]);
    let eqt = leaf::theta_eq(theta);
    let tt = leaf::theta_tables(&eqt);
    let et = eq_table(tau);
    // rank-one terms `e(y)·sw(p)`, keyed by the slot weight's `(base, bytes)`
    let mut keys: Vec<(usize, usize)> = vec![(pp::OUT_BASE, 32), (0, 32)];
    let mut es: Vec<Vec<F>> = vec![(0..blocks).map(|y| if k.chain_lk(y) { et[y] } else { F::ZERO }).collect(), crate::nodeops::shift_in_table(k, tau, kap_s)];
    let mut pw = kap_s * kap_s;
    for fm in FAMS.iter() {
        for sg in 0..2 {
            for ti in 0..fm.n {
                let src = k.wots_b(sg) + (fm.src)(ti);
                let g = (fm.mir)(ti);
                let mir = k.wm_b(sg) + g / 4;
                let x = pw * et[src];
                for (key, y) in [((512 + 8 * fm.off, fm.len), src), ((256 * (g % 4) + fm.mbo, fm.len), mir)] {
                    let i = match keys.iter().position(|q| *q == key) {
                        Some(i) => i,
                        None => {
                            keys.push(key);
                            es.push(vec![F::ZERO; blocks]);
                            keys.len() - 1
                        }
                    };
                    es[i][y] += x;
                }
            }
        }
        pw *= kap_s;
    }
    let sp = crate::prof::span("sh.collapse");
    let cols = collapse_keys(&w.z, &tt, &keys);
    debug_assert!(keys.iter().zip(&cols).all(|(&(b, n), c)| *c == collapse_n(&w.z, &tt, b, n)));
    drop(sp);
    let pairs: Vec<(Vec<F>, Vec<F>)> = es.into_iter().zip(cols).collect();
    assert!(pairs.iter().map(|(p, q)| leaf::dot(p, q)).fold(F::ZERO, |a, b| a + b).is_zero(), "Sh's sum is 0");
    wr.fs.phase = "S2";
    let sp = crate::prof::span("sh.pairs");
    let (taup, fin) = prove_pairs(pairs, &mut |g| {
        wr.send_f(pp::F_S2, &coeffs_f(g));
        wr.fs.chal_f()
    });
    let mut wsl = vec![F::ZERO; 1024];
    for (&(b, n), (eb, _)) in keys.iter().zip(fin.iter()) {
        for s in 0..8 * n {
            wsl[b + s] += *eb * eqt[s];
        }
    }
    drop(sp);
    let sp = crate::prof::span("sh.prefix");
    let zs = leaf::partial_fold_prefix(&w.z, &taup, 16);
    drop(sp);
    let zs_keep = zs.clone();
    let (tpp, _) = prove_pairs(vec![(wsl, zs)], &mut |g| {
        wr.send_f(pp::F_S2, &coeffs_f(g));
        wr.fs.chal_f()
    });
    leaf::dummy_rounds(&mut wr, pp::F_S2, pp::S2_ROUNDS - (m - 4), 48);
    tm.mark("shift", &mut t);

    // ---- Lr: the declared L bits, `b·(one + b) = 0`
    let lr = k.log_l();
    wr.fs.phase = "Lr1";
    let co = wr.fs.coords(pp::LR1_SQ);
    let r_l = co[..lr].to_vec();
    let lcells = ni.mats.l_cells();
    let one = f[k.one_cell()];
    let (mut al, mut bl) = (vec![F::ZERO; 1 << lr], vec![F::ZERO; 1 << lr]);
    for (j, &cl) in lcells.iter().enumerate() {
        al[j] = f[cl];
        bl[j] = one + f[cl];
    }
    wr.fs.phase = "Lr2";
    let (r_lr2, vl) = zc_abc(&r_l, al, bl, None, F::ZERO, &mut |g| {
        wr.send_f(pp::F_LR, &g);
        wr.fs.chal_f()
    });
    leaf::dummy_rounds(&mut wr, pp::F_LR, pp::LR_ROUNDS - lr, 48);
    wr.fs.phase = "Lrend";
    // `fLrEnd = â_L ‖ b̂_L ‖ ĉ_L ‖ p_x ‖ p_y ‖ s ‖ X₃` (RSV2 §2.1; `N8`: zeros)
    let rsv = child_claim(k, f);
    let mut lre = vl.to_vec();
    lre.extend_from_slice(&rsv);
    wr.send_f(pp::F_LREND, &lre);
    let (px, py, sc, xc) = (&rsv[..23], &rsv[23..48], &rsv[48..57], rsv[57]);
    let child = k.has_prev() && sc.iter().any(|x| !x.is_zero());
    wr.fs.phase = "Lr3";
    let kap_l = wr.fs.chal_f();
    tm.mark("lr", &mut t);

    // ---- E: E2 over the M rows, then E4 (the M and L linchecks at once)
    let lm = k.log_m();
    wr.fs.phase = "E1";
    let co = wr.fs.coords(pp::E1_SQ);
    let r_e = co[..lm].to_vec();
    let eta = co[23];
    let sp = crate::prof::span("ne2.matvec");
    let [am, bm, cm] = ni.mats.m_matvec(f);
    drop(sp);
    // RSV2 (ii″): E2's summand gains `η·eq(p_x, x)·(Σ_i s_i M̃_i(x ‖ hi, p_y) − X)`
    let sp = crate::prof::span("ne2.child");
    let extra = child.then(|| {
        let mut d = child_rows(&ni.kts, ni.mats.protos, px, py, sc, lm);
        par::for_each_chunk_mut(&mut d, 1 << 14, |_, ch| ch.iter_mut().for_each(|x| *x += xc));
        EqProd { p: px[..lm].to_vec(), pre: eta, q: d }
    });
    drop(sp);
    wr.fs.phase = "E2";
    let (r_e2, vm, (_, dfin)) = zc_abc_x(&r_e, am, bm, Some(cm), F::ZERO, extra, &mut |g| {
        wr.send_f(pp::F_E, &g);
        wr.fs.chal_f()
    });
    leaf::dummy_rounds(&mut wr, pp::F_E, pp::E2_ROUNDS - lm, 48);
    // `m̂* = Σ_i s_i M̃_i(r_E2 ‖ p_x[n, 23), p_y)` (zero without a child claim)
    let mstar = if child { dfin + xc } else { F::ZERO };
    wr.fs.phase = "Eend";
    wr.send_f(pp::F_EEND, &[vm[0], vm[1], vm[2], mstar, F::ZERO, F::ZERO, F::ZERO]);
    wr.fs.phase = "E3";
    let kap_e = wr.fs.chal_f();
    tm.mark("e2", &mut t);
    wr.fs.phase = "E4";
    let sp = crate::prof::span("ne4.scatter");
    let mut wt4: Vec<F> = par::uninit_vec(f.len());
    par::for_each_chunk_mut(&mut wt4, 1 << 16, |_, c| c.fill(F::ZERO));
    // `T_π = Σ_l eq(r_E2[<20], l)·M_π(l, ·)` once per prototype the own kind or the child claim reads:
    // the own `W_M(r_E2)` slot by slot from it (`m_scatter`'s value), and E4's child term
    let elo = eq_table(&r_e2[..20]);
    let reads = |kk: usize| child && !sc[3 * kk..3 * kk + 3].iter().all(|x| x.is_zero());
    let used = |pi: usize| ni.mats.kt.slots.iter().any(|sl| sl.0 == pi) || (0..3).any(|kk| reads(kk) && ni.kts[kk].slots.iter().any(|sl| sl.0 == pi));
    let has_sp = |kt: &KindTab| kt.ext.as_ref().is_some_and(|x| x.spare);
    let p0 = &ni.mats.protos[0];
    let tsp = (has_sp(ni.mats.kt) || (0..3).any(|kk| reads(kk) && has_sp(ni.kts[kk]))).then(|| {
        let (sp, ix) = (&p0.spare, p0.spare_ix());
        crate::mfill::cols3(sp, &ix.bc, &|i| elo[sp.idx[i] as usize])
    });
    let tb = E4Tabs { ts: [0, 1].map(|pi| used(pi).then(|| proto_scatter(&ni.mats.protos[pi], &elo))), tsp, elo: &elo, p0 };
    own_w_m(ni.mats.kt, &tb, &r_e2, [F::ONE, kap_e, kap_e * kap_e], &mut wt4);
    debug_assert!({
        let mut w2 = vec![F::ZERO; f.len()];
        ni.mats.m_scatter(&eq_table(&r_e2), [F::ONE, kap_e, kap_e * kap_e], &mut w2);
        w2 == wt4
    });
    let k3 = kap_e * kap_e * kap_e;
    let el = eq_table(&r_lr2);
    let oc = k.one_cell();
    let mut wone = F::ZERO;
    for (j, &cl) in lcells.iter().enumerate() {
        let x = k3 * el[j];
        wt4[cl] += x * (F::ONE + kap_l);
        wone += x * kap_l;
    }
    wt4[oc] += wone;
    drop(sp);
    let k4 = k3 * kap_e;
    let c4 = vm[0] + kap_e * vm[1] + kap_e * kap_e * vm[2] + k3 * (vl[0] + kap_l * vl[1] + kap_l * kap_l * vl[2]) + k4 * mstar;
    // RSV2 (iii″/iv″): E4's summand gains `κ_E⁴·eq(p_y, y)·Σ_i s_i M̃_i(x̂, y ‖ hi)`, `x̂ = r_E2 ‖ p_x[n, 23)`
    let sp = crate::prof::span("ne4.child");
    let mut extra4 = child.then(|| {
        let ny = m - 7;
        let mut xh = r_e2.clone();
        xh.extend_from_slice(&px[lm..]);
        let sp = crate::prof::span("ne4.cc");
        let g = child_cols(&ni.kts, &tb, &xh, py, sc, ny);
        drop(sp);
        g
    });
    drop(sp);
    debug_assert_eq!(crate::simd::dot(&wt4, f) + extra4.as_ref().map(|g| k4 * leaf::dot(&eq_table(&py[..m - 7]), g)).unwrap_or(F::ZERO), c4, "E4's sum");
    let _ = c4;
    // `W` lives on the M slots, the L bits and the one cell: the early rounds skip its zero chunks
    let sp = crate::prof::span("ne4.sumcheck");
    // the support's chunk size `2^a` (P2: 2^4; `FLOCK_E4_A` for measurements)
    let a4: usize = std::env::var("FLOCK_E4_A").ok().and_then(|x| x.parse().ok()).unwrap_or(4);
    let mut step4 = |g: [F; 3]| {
        wr.send_f(pp::F_E, &coeffs_f(g));
        wr.fs.chal_f()
    };
    // `G` (the child term) is zero off the child kinds' M cells and link cells, like `W`: both
    // pairs' supports are skipped in the early rounds
    // `FLOCK_E4_BENCH=a,b,…` (measurements only): the E4 sumcheck on copies of its tables at each
    // chunk size, with a local challenge chain, timed (best of two) and its outputs compared
    if let Ok(list) = std::env::var("FLOCK_E4_BENCH") {
        let mut first: Option<(Vec<F>, Vec<(F, F)>)> = None;
        for a in list.split(',').filter_map(|x| x.parse::<usize>().ok()) {
            let mut best = f64::MAX;
            for _ in 0..2 {
                let mut x = F::new(0x5a5a, 0xa5a5);
                let mut ch = |g: [F; 3]| {
                    x = x * x + g[0] + g[1] + g[2];
                    x
                };
                let ps = match &extra4 { None => vec![wt4.clone()], Some(g) => vec![wt4.clone(), g.clone()] };
                let qs: Vec<crate::sumcheck::Q> = if extra4.is_some() { vec![crate::sumcheck::Q::Tab(f), crate::sumcheck::Q::Eq(&py[..m - 7], k4)] } else { vec![crate::sumcheck::Q::Tab(f)] };
                let t = Instant::now();
                let r = crate::sumcheck::prove_pairs_support(ps, &qs, a, &mut ch);
                best = best.min(t.elapsed().as_secs_f64());
                match &first {
                    None => first = Some(r),
                    Some(f0) => assert!(*f0 == r, "E4 bench: a = {a} differs"),
                }
            }
            eprintln!("E4-BENCH {} a={a} {best:.3}s {}", k.name(), if crate::prof::on() { crate::prof::report() } else { String::new() });
        }
    }
    let (r4, fhat) = match extra4.take() {
        None => {
            let (r4, (_, fhat)) = crate::sumcheck::prove_pair_support(wt4, f, a4, &mut step4);
            (r4, fhat)
        }
        Some(g) => {
            // the child term `G·κ_E⁴·eq(p_y[<n], ·)`, its eq side in closed form
            let qs = [crate::sumcheck::Q::Tab(f), crate::sumcheck::Q::Eq(&py[..m - 7], k4)];
            let (r4, fin) = crate::sumcheck::prove_pairs_support(vec![wt4, g], &qs, a4, &mut step4);
            (r4, fin[0].1)
        }
    };
    drop(sp);
    leaf::dummy_rounds(&mut wr, pp::F_E, pp::E4_ROUNDS - (m - 7), 48);
    // E4's slices (sent in RS0) from the block fold at E4's block coordinates `r4[7..]` (the leaf
    // Lc's 8-block stripes), then the 7 element coordinates: `s_v = Σ_y eq(r4, y) bit_v(f[y])`, as
    // `ringswitch::partials` (whose dense pass over the 2^25 elements was RS's largest part)
    let sp = crate::prof::span("ne4.slices");
    let s3v = leaf::partials_from_fold(&crate::lincheck::partial_fold(&w.z, &r4[7..], blocks), &r4[..7]);
    drop(sp);
    debug_assert_eq!(s3v.iter().enumerate().fold(F::ZERO, |a, (v, x)| a + ringswitch::basis(v) * *x), fhat);
    wr.fs.phase = "E4end";
    wr.send_f(pp::F_E, &[fhat, F::ZERO]);
    tm.mark("e4", &mut t);

    // ---- RS: four claims (Lc's with the kind factor)
    let his = leaf::claim_points(&r, &sz, &tl, &tpp, &taup);
    let mut zbeta = vec![F::ZERO; BLOCK];
    let mut bp = F::ONE;
    for kk in 1..=8 {
        crate::simd::axpy(&mut zbeta, &zf[kk], bp);
        bp *= beta;
    }
    let s1v = leaf::partials_from_fold(&zbeta, &tl[7..14]);
    let s2v = leaf::partials_from_fold(&zs_keep, &tpp[7..10]);
    assert_eq!(leaf::dot(&eq_table(&tl[..7]), &s1v), vk8.iter().rev().fold(F::ZERO, |a, v| a * beta + *v));
    let mut msg = s0v.clone();
    msg.extend_from_slice(&s1v);
    msg.extend_from_slice(&s2v);
    msg.extend_from_slice(&s3v);
    wr.fs.phase = "RS0";
    wr.send_f(pp::F_RS0, &msg);
    wr.fs.phase = "RS1";
    let ch = wr.fs.coords(pp::RS1_SQ);
    let (rpp, kap) = (&ch[..7], ch[7]);
    let (coef, v_rs) = leaf::rs_batch(&[&s0v, &s1v, &s2v, &s3v], rpp, kap);
    let sp = crate::prof::span("nrs.kf");
    let kf: Vec<F> = (0..blocks).map(|tb| crate::nodeops::kf4(k, beta, tb)).collect();
    drop(sp);
    let sp = crate::prof::span("nrs.weight_table");
    let mut wt = ringswitch::weight_table_kf(&[(&his[0][..], coef[0], None), (&his[1][..], coef[1], Some(&kf[..])), (&his[2][..], coef[2], None), (&r4[..], coef[3], None)], rpp);
    drop(sp);
    tm.mark("ringswitch", &mut t);
    // ---- B′: the public cells
    wr.fs.phase = "B'";
    let kp = wr.fs.chal_f();
    let mut claim1 = v_rs;
    let mut p = kp * kp;
    for (cell, v) in k.cells4().iter().zip(w.pubv.iter()) {
        wt[*cell] += p;
        claim1 += p * *v;
        p *= kp;
    }
    // RSV2: the 60 child-claim cells at `κ′^{11} … κ′^{70}` (`rsvCells`; none for `N8`)
    if k.has_prev() {
        for (r, v) in RSV_REL.iter().zip(rsv.iter()) {
            wt[k.one_cell() + r] += p;
            claim1 += p * *v;
            p *= kp;
        }
    }

    // ---- P
    ligerito::prove(m, f, wt, claim1, c0, &mut wr);
    tm.mark("ligerito", &mut t);
    (wr.finish(), tm)
}

#[cfg(test)]
mod tests {
    use crate::blake2s::{chain_end, leaf_stmt, Digest};
    use crate::{agg, circuit, format, ir, leaf, node, oracle, params, plan};

    struct Tape<'a>(&'a dyn oracle::Oracle, std::sync::Mutex<oracle::Trace>);
    impl oracle::Oracle for Tape<'_> {
        fn ask(&self, q: &[u8]) -> Digest {
            let a = self.0.ask(q);
            self.1.lock().unwrap().push((q.to_vec(), a));
            a
        }
    }

    /// (+) **An `N8` node proof** over two signed aggregates (one `L32` segment of 3 steps each) is
    /// accepted by the kind's dumped program (prototype 0's at `N30`, real cells) with its node ops,
    /// with 8,905 asks, and `stmtOk4` holds; (−) another statement, a flipped byte of each PIOP field
    /// and the trivial `stmtOk4` canary are rejected.
    #[test]
    fn node_n8_accepted() {
        if plan::BLOB.len() < 16 && crate::mfill::find_dirs().is_none() {
            eprintln!("node_n8_accepted: SKIP (no node data)");
            return;
        }
        let nd = plan::node_data();
        let k = node::NK::N8;
        let (circ, gcirc, base) = (circuit::Circuit::build(), node::general_circuit(), circuit::Circuit::build_base());
        let o = oracle::Local::keyed(&[0x6Bu8; 32]);
        let (vk, _) = format::toy_sign(9, &[0u8; 32]);
        let mut signed = Vec::new();
        for a in 0..2u8 {
            let s: Digest = [0x40 + a; 32];
            let n = 3u64;
            let mut pi = vec![0u8; 48];
            pi[0] = agg::KIND_AGG;
            pi[1] = 1;
            pi[8..16].copy_from_slice(&n.to_le_bytes());
            pi[16..48].copy_from_slice(&chain_end(&s, n));
            pi.extend_from_slice(&leaf::prove_seg(&o, &circ, &vk, &s, 32, n).0);
            let c = leaf_stmt(&chain_end(&s, n), n);
            let tape = Tape(&o, std::sync::Mutex::new(Vec::new()));
            assert!(agg::verify(&tape, &circ, &vk, &c, &pi));
            let tr = tape.1.into_inner().unwrap();
            let (_, sig) = format::toy_sign(9, &format::trace_digest(&tr));
            signed.push(format::Signed { pi, tr, sig });
        }
        let aggs: Vec<node::AggIn> = signed.iter().map(node::agg_in).collect();
        let w = node::witness(k, &vk, None, &aggs, &nd.protos, &nd.texts, &gcirc, &circ, None);
        let kt = std::sync::Arc::new(nd.kind_tab(k));
        let ch = node::check(&w, &nd.protos, &kt);
        assert!(ch.h_bad_blocks + ch.chain_bad + ch.links_bad + ch.cells_bad + ch.l_bad + ch.m_bad + ch.link_rows_bad == 0, "{ch:?}");
        let cs = [aggs[0].c, aggs[1].c];
        let kts = nd.kind_tabs();
        let ni = super::NodeIn { k, vk, cs, w: &w, mats: super::Mats { k, kt: &kt, protos: &nd.protos }, kts: [&*kts[0], &*kts[1], &*kts[2]], base: &base };
        let (pi, _) = super::prove(&o, &ni);
        let c = super::node_c(&cs);
        let ctx = std::sync::Arc::new(ir::NodeCtx::new(k, nd.protos.clone(), kts.clone()));
        let text = nd.node_program(k);
        let r = ir::run_node(&text, ctx.clone(), &base, &o, &vk, &c, &pi);
        assert!(r.ok && r.asks == params::N_ITEMS && super::stmt_ok4(&pi, &c), "{:?}", r.failed);
        let mut c2 = c;
        c2[0] ^= 1;
        assert!(!ir::run_node(&text, ctx.clone(), &base, &o, &vk, &c2, &pi).ok);
        assert!(!super::stmt_ok4(&pi, &c2));
        for f in [params::F_Z2, params::F_L2, params::F_S2, params::F_LR, params::F_E, params::F_RS0] {
            let mut p2 = pi.clone();
            p2[params::field_off(f) + params::FIELD_SIZES[f] / 2] ^= 2;
            assert!(!ir::run_node(&text, ctx.clone(), &base, &o, &vk, &c, &p2).ok, "field {f}");
        }
    }
}

#[cfg(test)]
mod pass12_tests {
    use super::*;

    /// `fold_f_sparse` equals `fold_f` on a table with zero stretches.
    #[test]
    fn fold_sparse_matches() {
        let t: Vec<F> = (0..(1u64 << 15)).map(|i| if (i >> 11) % 3 == 1 || (i >> 9) % 7 == 2 { F::new(i * 77 + 1, i ^ 9) } else { F::ZERO }).collect();
        let s = F::new(0x1234_5678, 0x9abc);
        assert_eq!(crate::sumcheck::fold_f_sparse(&t, s), crate::sumcheck::fold_f(&t, s));
    }

    /// `collapse_keys` equals `collapse_n` key by key, with zero and nonzero blocks.
    #[test]
    fn collapse_keys_matches() {
        let nb = 37;
        let mut s = 0x5151_7e57u64;
        let z: Vec<u64> = (0..nb * 256)
            .map(|i| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                if (i / 256) % 3 == 0 || (i % 256) % 5 == 1 { 0 } else { s }
            })
            .collect();
        let eqt: Vec<F> = (0..256u64).map(|i| F::new(i * 0x9e37 + 1, i ^ 0x55)).collect();
        let tt = leaf::theta_tables(&eqt);
        let keys = [(0usize, 32usize), (512, 9), (1024 + 64, 3), (256, 32), (8 * 1000, 17)];
        let cols = collapse_keys(&z, &tt, &keys);
        for (k, &(b, n)) in keys.iter().enumerate() {
            assert_eq!(cols[k], collapse_n(&z, &tt, b, n), "key {k}");
        }
    }
}

#[cfg(test)]
mod pass13_tests {
    use super::*;
    use crate::{node, plan};

    /// On the node data (N2 and N4): `m_scatter`'s gather equals `m_scatter_ref` (pass 12's
    /// scatter) and `m_matvec` (the coefficient-1 terms summed apart) equals each row's forms by
    /// `Rows::eval`, on pseudo-random `e`, `s` and `f` with zero stretches.
    #[test]
    fn scatter_gather_and_matvec_match() {
        if plan::BLOB.len() < 16 && crate::mfill::find_dirs().is_none() {
            return;
        }
        let nd = plan::node_data();
        let mut st = 0x2545_f491_4f6c_dd1du64;
        let mut nx = move || {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            st
        };
        for k in [node::NK::N2, node::NK::N4] {
            // P2: the factored table's gather against the full table's reference
            let (kt, ktf) = (nd.kind_tab(k), nd.kind_tab_full(k));
            let mats = Mats { k, kt: &kt, protos: &nd.protos };
            let nm = 1usize << k.log_m();
            let e: Vec<F> = (0..nm).map(|i| if (i >> 12) % 5 == 3 { F::ZERO } else { F::new(nx(), nx()) }).collect();
            let s = [F::ONE, F::new(nx(), nx()), F::new(nx(), nx())];
            let ncell = (ktf.one_cell + (ktf.slots.len() + 1) * SLOT).max(ktf.links.cells.iter().map(|&c| c as usize + 1).max().unwrap_or(0));
            let w0: Vec<F> = (0..ncell).map(|i| if i % 3 == 0 { F::new(nx(), 0) } else { F::ZERO }).collect();
            let (mut w1, mut w2) = (w0.clone(), w0.clone());
            mats.m_scatter(&e, s, &mut w1);
            Mats { k, kt: &ktf, protos: &nd.protos }.m_scatter_ref(&e, s, &mut w2);
            assert!(w1 == w2, "{k:?}: m_scatter");
            let f: Vec<F> = (0..ncell).map(|i| if (i >> 10) % 7 == 1 { F::ZERO } else { F::new(nx(), nx()) }).collect();
            let mv = mats.m_matvec(&f);
            let one = kt.one_cell;
            for (v, &(pi, ..)) in kt.slots.iter().enumerate() {
                let p = &nd.protos[pi];
                let base = (pi * SLOT) as u32;
                for i in (0..p.rows.len()).step_by(7) {
                    let o = p.rows.eval(i, &|c| f[one + (c - base) as usize + v * SLOT]);
                    let row = (p.rows.idx[i] - base) as usize + v * SLOT;
                    assert!((0..3).all(|m| mv[m][row] == o[m]), "{k:?}: m_matvec row {row}");
                }
            }
        }
    }
}

/// P2: the factored rows (`mfill::Ext`) against the full tables (E1b's rows as link rows), on the
/// node data at pseudo-random points: E2's `m_matvec` and child table, E4's own `W_M` and child
/// columns, for an `N4` and an `N2` parent with every child kind read. Returns the times (best of
/// `reps`, full then factored) and whether every output is equal.
pub fn ext_ab(reps: usize) -> (Vec<(&'static str, f64, f64)>, bool) {
    use crate::node::NK;
    let nd = crate::plan::node_data();
    let t = Instant::now();
    let kf: Vec<KindTab> = par::collect_vec(3, 1, |i| {
        let kt = nd.kind_tab_full([NK::N2, NK::N4, NK::N8][i]);
        let _ = kt.links_by_cell();
        kt
    });
    let t_full = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let kn = nd.kind_tabs();
    let t_new = t.elapsed().as_secs_f64();
    let mut st = 0x9e37_79b9_7f4a_7c15u64;
    let mut rf = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        F::new(st, st.rotate_left(23) ^ 0x3c)
    };
    let mut res: Vec<(&'static str, f64, f64)> = vec![("kind_tabs", t_full, t_new)];
    let mut eq_all = true;
    for k in [NK::N4, NK::N2] {
        let lm = k.log_m();
        let ncell = 1usize << (k.m() - 7);
        let f: Vec<F> = par::collect_vec(ncell, 1 << 14, |i| F::new((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x1234, (i as u64).rotate_left(31) ^ 0xab));
        let px: Vec<F> = (0..23).map(|_| rf()).collect();
        let py: Vec<F> = (0..25).map(|_| rf()).collect();
        let sc: Vec<F> = (0..9).map(|_| rf()).collect();
        let r_e2: Vec<F> = (0..lm).map(|_| rf()).collect();
        let s3 = [F::ONE, rf(), rf()];
        let mut xh = r_e2.clone();
        xh.extend_from_slice(&px[lm..]);
        let elo = eq_table(&r_e2[..20]);
        let mut outs: [Vec<Vec<F>>; 2] = [Vec::new(), Vec::new()];
        let mut best = [[f64::MAX; 2]; 4];
        for _ in 0..reps {
            for (j, kts) in [[&kf[0], &kf[1], &kf[2]], [&*kn[0], &*kn[1], &*kn[2]]].iter().enumerate() {
                let kt = kts[k as usize];
                let mats = Mats { k, kt, protos: &nd.protos };
                let t = Instant::now();
                let mv = mats.m_matvec(&f);
                best[0][j] = best[0][j].min(t.elapsed().as_secs_f64());
                let t = Instant::now();
                let d = child_rows(kts, &nd.protos, &px, &py, &sc, lm);
                best[1][j] = best[1][j].min(t.elapsed().as_secs_f64());
                let t = Instant::now();
                let p0 = &nd.protos[0];
                let has_sp = |kt: &KindTab| kt.ext.as_ref().is_some_and(|x| x.spare);
                let tsp = (has_sp(kt) || kts.iter().any(|kt| has_sp(kt))).then(|| crate::mfill::cols3(&p0.spare, &p0.spare_ix().bc, &|i| elo[p0.spare.idx[i] as usize]));
                let sp = crate::prof::span("b.proto_scatter");
                let ts = [0, 1].map(|pi| Some(proto_scatter(&nd.protos[pi], &elo)));
                drop(sp);
                let tb = E4Tabs { ts, tsp, elo: &elo, p0 };
                let mut w = vec![F::ZERO; ncell];
                own_w_m(kt, &tb, &r_e2, s3, &mut w);
                best[2][j] = best[2][j].min(t.elapsed().as_secs_f64());
                let t = Instant::now();
                let g = child_cols(kts, &tb, &xh, &py, &sc, k.m() - 7);
                best[3][j] = best[3][j].min(t.elapsed().as_secs_f64());
                outs[j] = vec![mv[0].clone(), mv[1].clone(), mv[2].clone(), d, w, g];
            }
        }
        eq_all &= outs[0] == outs[1];
        let nm = if k == NK::N4 { ["N4 m_matvec", "N4 child_rows", "N4 own_w_m+T", "N4 child_cols"] } else { ["N2 m_matvec", "N2 child_rows", "N2 own_w_m+T", "N2 child_cols"] };
        for i in 0..4 {
            res.push((nm[i], best[i][0], best[i][1]));
        }
    }
    (res, eq_all)
}

#[cfg(test)]
mod p2_tests {
    /// (P2) The factored rows give E2's and E4's tables exactly as the full tables do (N4 and N2
    /// parents, every child kind read), and `m_scatter` (the gather, with the factored rows) equals
    /// `m_scatter_ref` on the full table.
    #[test]
    fn ext_matches_full() {
        if crate::plan::BLOB.len() < 16 && crate::mfill::find_dirs().is_none() {
            return;
        }
        let (_, ok) = super::ext_ab(1);
        assert!(ok);
        let nd = crate::plan::node_data();
        for k in [crate::node::NK::N2, crate::node::NK::N4, crate::node::NK::N8] {
            let (kt, ktf) = (nd.kind_tab(k), nd.kind_tab_full(k));
            let nm = 1usize << k.log_m();
            let e: Vec<super::F> = (0..nm).map(|i| if (i >> 12) % 5 == 3 { super::F::ZERO } else { super::F::new(i as u64 * 31 + 7, i as u64 ^ 0x77) }).collect();
            let s = [super::F::ONE, super::F::new(5, 9), super::F::new(11, 3)];
            let ncell = 1usize << (k.m() - 7);
            let (mut w1, mut w2) = (vec![super::F::ZERO; ncell], vec![super::F::ZERO; ncell]);
            super::Mats { k, kt: &kt, protos: &nd.protos }.m_scatter(&e, s, &mut w1);
            super::Mats { k, kt: &ktf, protos: &nd.protos }.m_scatter_ref(&e, s, &mut w2);
            assert!(w1 == w2, "{k:?}: m_scatter");
        }
    }
}
