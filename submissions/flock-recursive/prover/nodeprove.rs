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
use crate::mfill::{KindTab, Proto, SLOT};
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
        let l = &self.kt.links;
        for i in 0..l.len() {
            let v = l.eval(i, &|c| f[c as usize]);
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
    }

    /// The link rows' part of `m_scatter`.
    fn links_scatter(&self, e: &[F], s: [F; 3], w: &mut [F]) {
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

    /// `m_scatter` row by row (pass 12's; slots in parallel: their cells are disjoint; the link rows
    /// after). The reference.
    pub fn m_scatter_ref(&self, e: &[F], s: [F; 3], w: &mut [F]) {
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
fn zc_abc(r: &[F], mut a: Vec<F>, mut b: Vec<F>, mut c: Option<Vec<F>>, claim0: F, step: &mut dyn FnMut([F; 3]) -> F) -> (Vec<F>, [F; 3]) {
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
        let x = step(zerocheck::zc_coeffs(pref, r[kk], h0, h1, hi));
        claim = eval2_f([h0, h1, hi], x);
        pref *= F::ONE + r[kk] + x;
        xs.push(x);
        a = crate::sumcheck::fold_f_sparse(&a, x);
        b = crate::sumcheck::fold_f_sparse(&b, x);
        if let Some(cc) = c.as_mut() {
            *cc = crate::sumcheck::fold_f_sparse(cc, x);
        }
    }
    let cv = c.map(|c| c[0]).unwrap_or(F::ZERO);
    assert_eq!(claim, a[0] * b[0] + cv);
    (xs, [a[0], b[0], cv])
}

/// The node prover's inputs besides the oracle.
pub struct NodeIn<'a> {
    pub k: NK,
    pub vk: Digest,
    /// The two signed children's statements (`stmt`'s `c₀`, `c₁`).
    pub cs: [Digest; 2],
    pub w: &'a NodeWit,
    pub mats: Mats<'a>,
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
    wr.send_f(pp::F_LREND, &vl);
    wr.fs.phase = "Lr3";
    let kap_l = wr.fs.chal_f();
    tm.mark("lr", &mut t);

    // ---- E: E2 over the M rows, then E4 (the M and L linchecks at once)
    let lm = k.log_m();
    wr.fs.phase = "E1";
    let co = wr.fs.coords(pp::E1_SQ);
    let r_e = co[..lm].to_vec();
    let sp = crate::prof::span("ne2.matvec");
    let [am, bm, cm] = ni.mats.m_matvec(f);
    drop(sp);
    wr.fs.phase = "E2";
    let (r_e2, vm) = zc_abc(&r_e, am, bm, Some(cm), F::ZERO, &mut |g| {
        wr.send_f(pp::F_E, &g);
        wr.fs.chal_f()
    });
    leaf::dummy_rounds(&mut wr, pp::F_E, pp::E2_ROUNDS - lm, 48);
    wr.fs.phase = "Eend";
    wr.send_f(pp::F_EEND, &vm);
    wr.fs.phase = "E3";
    let kap_e = wr.fs.chal_f();
    tm.mark("e2", &mut t);
    wr.fs.phase = "E4";
    let sp = crate::prof::span("ne4.scatter");
    let mut wt4: Vec<F> = par::uninit_vec(f.len());
    par::for_each_chunk_mut(&mut wt4, 1 << 16, |_, c| c.fill(F::ZERO));
    ni.mats.m_scatter(&eq_table(&r_e2), [F::ONE, kap_e, kap_e * kap_e], &mut wt4);
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
    let c4 = vm[0] + kap_e * vm[1] + kap_e * kap_e * vm[2] + k3 * (vl[0] + kap_l * vl[1] + kap_l * kap_l * vl[2]);
    assert_eq!(crate::simd::dot(&wt4, f), c4, "E4's sum");
    let _ = c4;
    // `W` lives on the M slots, the L bits and the one cell: the early rounds skip its zero chunks
    let sp = crate::prof::span("ne4.sumcheck");
    let (r4, (_, fhat)) = crate::sumcheck::prove_pair_support(wt4, f, 12, &mut |g| {
        wr.send_f(pp::F_E, &coeffs_f(g));
        wr.fs.chal_f()
    });
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
        let ni = super::NodeIn { k, vk, cs, w: &w, mats: super::Mats { k, kt: &kt, protos: &nd.protos }, base: &base };
        let (pi, _) = super::prove(&o, &ni);
        let c = super::node_c(&cs);
        let ctx = std::sync::Arc::new(ir::NodeCtx { k, protos: nd.protos.clone(), kt: kt.clone() });
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
            let kt = nd.kind_tab(k);
            let mats = Mats { k, kt: &kt, protos: &nd.protos };
            let nm = 1usize << k.log_m();
            let e: Vec<F> = (0..nm).map(|i| if (i >> 12) % 5 == 3 { F::ZERO } else { F::new(nx(), nx()) }).collect();
            let s = [F::ONE, F::new(nx(), nx()), F::new(nx(), nx())];
            let ncell = (kt.one_cell + kt.slots.len() * SLOT).max(kt.links.cells.iter().map(|&c| c as usize + 1).max().unwrap_or(0));
            let w0: Vec<F> = (0..ncell).map(|i| if i % 3 == 0 { F::new(nx(), 0) } else { F::ZERO }).collect();
            let (mut w1, mut w2) = (w0.clone(), w0.clone());
            mats.m_scatter(&e, s, &mut w1);
            mats.m_scatter_ref(&e, s, &mut w2);
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
