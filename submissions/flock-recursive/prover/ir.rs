//! A native interpreter of the Lean verifier program as dumped (`irdump ops L|P`, one op per line,
//! `opName operands… → dst`; `FRVIR.evalOp`), for the finals' KAT (stage P2, rev. 3.9): the dumped
//! `gen fin` of a leaf kind is run on a native proof with native implementations of the abstract
//! ops (`OpImpl`), mirroring S-F2's concrete `FRVerifierImpl` (`lagrangeSI`, `eqZI`, `rowWI`,
//! `phiRSI`, `rsWeightI`, `tensorWI`, `slotWI`, `shiftTargetI`, `targetSLeafI`). Its flag is the
//! Lean verifier's verdict on the proof, up to those op implementations.
//!
//! Two operands the ops do not carry are supplied as S-F2's `implC` does for a fixed kind: `κ_s` of
//! `shiftTarget` (S1's coordinate 28, found from the registers of `τ`), and the kind for `targetS`,
//! `slotW`, `linkW` (a leaf: every block `chain`; no link families). `evalL`/`evalMK` (the node's L
//! and M matrices) are not implemented: a leaf program must not use their values ungated, so they
//! return zeros and the run records that they were evaluated.

use crate::blake2s::Digest;
use crate::field::{F, K};
use crate::mle::eq_table;
use crate::oracle::Oracle;
use crate::params::field_off;

#[derive(Clone, Debug)]
pub enum V {
    F(F),
    K(K),
    D(Digest),
    B(Vec<u8>),
    N(u64),
    Bit(bool),
    AF(Vec<F>),
    AK(Vec<K>),
}

impl V {
    pub fn f(&self) -> F {
        match self {
            V::F(x) => *x,
            _ => F::ZERO,
        }
    }
    pub fn k(&self) -> K {
        match self {
            V::K(x) => *x,
            _ => K::ZERO,
        }
    }
    pub fn d(&self) -> Digest {
        match self {
            V::D(x) => *x,
            _ => [0u8; 32],
        }
    }
    pub fn b(&self) -> &[u8] {
        match self {
            V::B(x) => x,
            _ => &[],
        }
    }
    pub fn n(&self) -> u64 {
        match self {
            V::N(x) => *x,
            _ => 0,
        }
    }
    pub fn bit(&self) -> bool {
        matches!(self, V::Bit(true))
    }
    pub fn af(&self) -> &[F] {
        match self {
            V::AF(x) => x,
            _ => &[],
        }
    }
    pub fn ak(&self) -> &[K] {
        match self {
            V::AK(x) => x,
            _ => &[],
        }
    }
    fn is_zero(&self) -> bool {
        match self {
            V::F(x) => x.is_zero(),
            V::K(x) => *x == K::ZERO,
            V::D(x) => x.iter().all(|&b| b == 0),
            V::B(x) => x.iter().all(|&b| b == 0),
            V::N(x) => *x == 0,
            V::Bit(x) => !*x,
            V::AF(x) => x.iter().all(|y| y.is_zero()),
            V::AK(x) => x.iter().all(|y| *y == K::ZERO),
        }
    }
    fn eqv(&self, o: &V) -> bool {
        match (self, o) {
            (V::F(a), V::F(b)) => a == b,
            (V::K(a), V::K(b)) => a == b,
            (V::D(a), V::D(b)) => a == b,
            (V::B(a), V::B(b)) => a == b,
            (V::N(a), V::N(b)) => a == b,
            (V::Bit(a), V::Bit(b)) => a == b,
            (V::AF(a), V::AF(b)) => a == b,
            (V::AK(a), V::AK(b)) => a == b,
            _ => false,
        }
    }
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn parse_val(s: &str) -> V {
    let (t, x) = s.split_once(':').unwrap_or((s, ""));
    match t {
        "F" => V::F(F::from_bytes(&unhex(x))),
        "K" => V::K(K::from_bytes(&unhex(x))),
        "D" => V::D(unhex(x).try_into().unwrap()),
        "B" => V::B(unhex(x)),
        "N" => V::N(x.parse().unwrap()),
        "Bit" => V::Bit(x == "true"),
        "AF" => V::AF(x.trim_matches(['[', ']']).split(',').filter(|e| !e.is_empty()).map(|e| F::from_bytes(&unhex(e))).collect()),
        "AK" => V::AK(x.trim_matches(['[', ']']).split(',').filter(|e| !e.is_empty()).map(|e| K::from_bytes(&unhex(e))).collect()),
        _ => V::AF(Vec::new()),
    }
}

fn reg(s: &str) -> usize {
    s.trim_matches(['[', ']']).strip_prefix('r').unwrap_or_else(|| panic!("register {s}")).parse().unwrap()
}

/// The outcome of a run: the flag, the failed assertions (line numbers, first 20), what was used.
#[derive(Default, Debug)]
pub struct Run {
    pub ok: bool,
    pub failed: Vec<usize>,
    pub asks: usize,
    pub node_matrices_used: bool,
    /// Named values of the finals, for comparison with the native verifier.
    pub regs_out: usize,
}

/// `eq(a, b)` over `a`'s length, `b` padded with zeros (`FRVIR.eqPoint`).
fn eq_point(a: &[F], b: &[F]) -> F {
    let mut acc = F::ONE;
    for (v, x) in a.iter().enumerate() {
        let y = b.get(v).copied().unwrap_or(F::ZERO);
        acc *= *x * y + (F::ONE + *x) * (F::ONE + y);
    }
    acc
}

fn eq_tab_k(r: &[K]) -> Vec<K> {
    crate::mle::eq_table_k(r)
}

/// `idxOf b a i`: bits `[ib, (i+1)b)` of `a` little-endian.
fn idx_of(bits: usize, a: &Digest, i: usize) -> u64 {
    let x = u128::from_le_bytes(a[..16].try_into().unwrap());
    let y = u128::from_le_bytes(a[16..].try_into().unwrap());
    let mut p = 0u64;
    for b in 0..bits {
        let k = i * bits + b;
        let bit = if k < 128 { (x >> k) & 1 } else { (y >> (k - 128)) & 1 };
        p |= (bit as u64) << b;
    }
    p
}

/// A.6's pinned rows per block kind, in `blockKinds` order (`FRTranscriptDefs.zeroRows`).
const ZERO_ROWS: [&[(usize, usize)]; 9] = [
    &[(0, 255), (512, 519), (776, 1023), (1024, 1152)],
    &[(1024, 1152)],
    &[(0, 255), (1024, 1152)],
    &[(840, 1023), (1024, 1152)],
    &[(0, 255), (512, 519), (840, 1023), (1024, 1152)],
    &[(0, 255), (512, 519), (1024, 1152)],
    &[(520, 1023), (1024, 1152)],
    &[(0, 255), (512, 519), (584, 599), (856, 1023), (1024, 1152)],
    &[],
];

/// `maskRows kindW rowW`: `rowW[k]·Σ_{kind: k not pinned} kindW[kind]`.
pub fn mask_rows(kind_w: &[F], row_w: &[F]) -> Vec<F> {
    row_w
        .iter()
        .enumerate()
        .map(|(k, w)| {
            let mut s = F::ZERO;
            for (i, zr) in ZERO_ROWS.iter().enumerate() {
                if !zr.iter().any(|&(a, b)| a <= k && k <= b) {
                    s += kind_w.get(i).copied().unwrap_or(F::ZERO);
                }
            }
            *w * s
        })
        .collect()
}

/// Run the dumped program `text` (a fixed leaf kind) on `π` with the oracle `o`.
pub fn run(text: &str, circ: &crate::circuit::Circuit, o: &dyn Oracle, vk: &Digest, c: &Digest, pi: &[u8]) -> Run {
    run_regs(text, circ, o, vk, c, pi).0
}

/// A group (mux) program's kind tables `{L:a, P:b, N:c}` (`IRDump8`'s `showKC` in mux mode) read at
/// index `ix` (0 `L32`, 1 `P30`, 2 `N30`): the fixed program of that index (`FRVIR4At`'s `Op.at`).
pub fn spec_kind(text: &str, ix: usize) -> String {
    let tag = ["L:", "P:", "N:"][ix];
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(i) = rest.find('{') {
        out.push_str(&rest[..i]);
        let j = i + rest[i..].find('}').expect("kind table");
        let body = &rest[i + 1..j];
        // top-level entries are separated by ", " (entries hold no ", " inside brackets)
        let e = body.split(", ").find(|e| e.starts_with(tag)).expect("kind entry");
        out.push_str(&e[2..]);
        rest = &rest[j + 1..];
    }
    out.push_str(rest);
    out
}

/// **The node program with its real public cells** (INT-8 dumped `progNode` with the placeholder
/// cells `oneCell + j`, `IRDump8.cellsPH`; a cell enters only as `finPf`'s `nc` per-coordinate
/// `keep (bit v of cell)` ops, `gCellOpsK`). Finds, after the `rsWeight` op, the `cells.len()` runs
/// of `nc` consecutive `keep` ops, checks each run's flags are the placeholder's bits, and writes the
/// real cell's bits. `None` if the program does not have that shape.
pub fn with_cells(text: &str, ph: &[usize], real: &[usize], nc: usize) -> Option<String> {
    let lines: Vec<&str> = text.lines().collect();
    let start = lines.iter().position(|l| l.starts_with("rsWeight "))?;
    let mut runs: Vec<usize> = Vec::new();
    let mut i = start;
    while i < lines.len() && runs.len() < ph.len() {
        if lines[i].starts_with("keep ") {
            let j = (i..lines.len()).find(|&j| !lines[j].starts_with("keep ")).unwrap_or(lines.len());
            if j - i == nc {
                runs.push(i);
            }
            i = j;
        } else {
            i += 1;
        }
    }
    if runs.len() != ph.len() {
        return None;
    }
    let mut out: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
    for (r, (&p, &c)) in runs.iter().zip(ph.iter().zip(real.iter())) {
        for v in 0..nc {
            let l = &lines[r + v];
            let want = if (p >> v) & 1 == 1 { "keep true " } else { "keep false " };
            if !l.starts_with(want) {
                return None;
            }
            let rest = &l[want.len()..];
            out[r + v] = format!("keep {} {rest}", (c >> v) & 1 == 1);
        }
    }
    let mut s = out.join("\n");
    s.push('\n');
    Some(s)
}

/// A node kind's context for its program's node ops (`targetS`, `shiftMask`, `linkWAll`, the kind
/// factor of `rsWeight`, `evalM`/`evalL` over the dumped rows): `nodeops.rs`'s specification forms.
pub struct NodeCtx {
    pub k: crate::node::NK,
    pub protos: std::sync::Arc<[crate::mfill::Proto; 2]>,
    /// The three kinds' tables (`N2`, `N4`, `N8`: RSV2's stacked `evalM` reads every kind's rows).
    pub kts: [std::sync::Arc<crate::mfill::KindTab>; 3],
}

impl NodeCtx {
    pub fn new(k: crate::node::NK, protos: std::sync::Arc<[crate::mfill::Proto; 2]>, kts: [std::sync::Arc<crate::mfill::KindTab>; 3]) -> NodeCtx {
        NodeCtx { k, protos, kts }
    }
    /// The node's own kind table.
    pub fn kt(&self) -> &crate::mfill::KindTab {
        &self.kts[self.k as usize]
    }
}

thread_local! {
    static NODE: std::cell::RefCell<Option<std::sync::Arc<NodeCtx>>> = const { std::cell::RefCell::new(None) };
}

/// `run` of a node kind's program (its node ops from `ctx`).
pub fn run_node(text: &str, ctx: std::sync::Arc<NodeCtx>, circ: &crate::circuit::Circuit, o: &dyn Oracle, vk: &Digest, c: &Digest, pi: &[u8]) -> Run {
    NODE.with(|n| *n.borrow_mut() = Some(ctx));
    let r = run_regs(text, circ, o, vk, c, pi).0;
    NODE.with(|n| *n.borrow_mut() = None);
    r
}

/// `run_regs` of a node kind's program (its node ops from `ctx`): the M fill of a previous-node slot.
pub fn run_node_regs(text: &str, ctx: std::sync::Arc<NodeCtx>, circ: &crate::circuit::Circuit, o: &dyn Oracle, vk: &Digest, c: &Digest, pi: &[u8]) -> (Run, Vec<V>) {
    NODE.with(|n| *n.borrow_mut() = Some(ctx));
    let r = run_regs(text, circ, o, vk, c, pi);
    NODE.with(|n| *n.borrow_mut() = None);
    r
}

fn node_ctx() -> Option<std::sync::Arc<NodeCtx>> {
    NODE.with(|n| n.borrow().clone())
}

/// `run`, and every register's value (the M fill reads them through `mregs`/`maux`).
pub fn run_regs(text: &str, circ: &crate::circuit::Circuit, o: &dyn Oracle, vk: &Digest, c: &Digest, pi: &[u8]) -> (Run, Vec<V>) {
    let mut regs: Vec<V> = Vec::with_capacity(110_000);
    // the source registers of each packF/packFK result (for shiftTarget's κ_s)
    let mut src: std::collections::HashMap<usize, Vec<usize>> = std::collections::HashMap::new();
    let mut out = Run { ok: true, ..Default::default() };
    let nctx = node_ctx();
    let prof_on = std::env::var_os("FLOCK_IRPROF").is_some();
    let t_run = std::time::Instant::now();
    let mut by_op: Vec<(String, f64, usize)> = Vec::new();
    let at = |f: usize, o: usize, n: usize| -> &[u8] { &pi[field_off(f) + o..field_off(f) + o + n] };
    let (sk, wtab) = (crate::skipdom::skip(), ());
    let _ = wtab;
    for (ln, line) in text.lines().enumerate() {
        if line.starts_with("--") || line.is_empty() {
            continue;
        }
        let (lhs, dst) = match line.split_once(" → ") {
            Some((a, b)) => (a, b.split(' ').map(reg).collect::<Vec<_>>()),
            None => (line, vec![]),
        };
        if let Some(&d0) = dst.first() {
            assert_eq!(d0, regs.len(), "line {}: register numbering", ln + 1);
        }
        let t: Vec<&str> = lhs.split(' ').collect();
        let g = |i: usize| -> &V { &regs[reg(t[i])] };
        let gr = |s: &str| -> &V { &regs[reg(s)] };
        let num = |i: usize| -> usize { t[i].parse().unwrap() };
        let flag = |i: usize| -> bool { t[i] == "true" };
        let fail = |ok: bool, out: &mut Run| {
            if !ok {
                out.ok = false;
                if out.failed.len() < 20 {
                    out.failed.push(ln + 1);
                }
            }
        };
        let ask = |q: &[u8], out: &mut Run| -> V {
            out.asks += 1;
            V::D(o.ask(q))
        };
        let t_op = std::time::Instant::now();
        let new: Vec<V> = match t[0] {
            "input" => vec![V::D(if num(1) == 0 { *vk } else { *c })],
            "const" => vec![parse_val(t[1])],
            "piField" => vec![V::B(at(num(1), num(2), num(3)).to_vec())],
            "piElem" => vec![V::F(F::from_bytes(at(num(1), num(2), 16)))],
            "piElemK" => vec![V::K(K::from_bytes(at(num(1), num(2), 32)))],
            "piDigest" => vec![V::D(at(num(1), num(2), 32).try_into().unwrap())],
            "piDigestAt" => {
                let k = g(3).n() as usize;
                vec![V::D(at(num(1), num(2) + 32 * k, 32).try_into().unwrap())]
            }
            "askSeed" => {
                let mut q = b"FRSEED0".to_vec();
                q.extend_from_slice(vk);
                q.extend_from_slice(c);
                q.extend_from_slice(g(1).b());
                vec![ask(&q, &mut out)]
            }
            "askAbsorb" => {
                let mut q = b"FRABS000".to_vec();
                q.extend_from_slice(&g(1).d());
                q.extend_from_slice(g(2).b());
                vec![ask(&q, &mut out)]
            }
            "askSqueeze" => {
                let mut q = b"FRSQZ000".to_vec();
                q.extend_from_slice(&g(1).d());
                vec![ask(&q, &mut out)]
            }
            "askNode" => {
                let mut q = Vec::with_capacity(72);
                let (l, r) = if flag(5) { (g(3).d(), g(4).d()) } else { ([0u8; 32], [0u8; 32]) };
                crate::merkle::node_query(num(1) as u8, &l, &r, &mut q);
                vec![ask(&q, &mut out)]
            }
            "askCol" => {
                let mut q = b"FRMCOL".to_vec();
                q.push(num(1) as u8);
                q.push(0);
                q.extend_from_slice(g(2).b());
                vec![ask(&q, &mut out)]
            }
            "chF" => vec![V::F(F::from_bytes(&g(1).d()[16 * num(2)..16 * num(2) + 16]))],
            "chK" => vec![V::K(K::from_bytes(&g(1).d()))],
            "idx" => vec![V::N(idx_of(num(2), &g(1).d(), num(3)))],
            "bitOf" => vec![V::Bit((g(1).n() >> num(2)) & 1 == 1)],
            "shrN" => vec![V::N(g(1).n() >> num(2))],
            "mulF" => vec![V::F(g(1).f() * g(2).f())],
            "addF" => vec![V::F(g(1).f() + g(2).f())],
            "mulK" => vec![V::K(g(1).k() * g(2).k())],
            "addK" => vec![V::K(g(1).k() + g(2).k())],
            "mulKF" => vec![V::K(g(1).k().mulf(g(2).f()))],
            "invF" => vec![V::F(g(1).f().inv())],
            "packF" | "packFK" => {
                let rs: Vec<usize> = t[1..].iter().map(|s| reg(s)).collect();
                src.insert(regs.len(), rs.clone());
                vec![V::AF(rs.iter().map(|&i| regs[i].f()).collect())]
            }
            "packK" => vec![V::AK(t[1..].iter().map(|s| gr(s).k()).collect())],
            "getF" => vec![V::F(g(1).af().get(num(2)).copied().unwrap_or(F::ZERO))],
            "getK" => vec![V::K(g(1).ak().get(num(2)).copied().unwrap_or(K::ZERO))],
            "eqTable" => vec![V::AF(eq_table(g(1).af()))],
            "eqTableK" => vec![V::AK(eq_tab_k(g(1).ak()))],
            "dotKF" => {
                let w = g(1).ak();
                let col = g(2).b();
                let mut acc = K::ZERO;
                for (r, x) in col.chunks_exact(16).enumerate() {
                    acc += w.get(r).copied().unwrap_or(K::ZERO).mulf(F::from_bytes(x));
                }
                vec![V::K(acc)]
            }
            "lagrangeS" => {
                let v = g(1).af();
                let r_full = &v[..];
                let pe = g(3).af();
                let (a, b) = lagrange_s(r_full, g(2).f(), pe);
                vec![V::F(a), V::F(b)]
            }
            // a segment's (revision 4.1, S-F4 `targetSSegI`): the operand is `r₀ ‖ blk(18) ‖ L(18)`,
            // the leaf target times `Σ_{t ≤ L} eq(blk, t)`; 3.x's leaf: the operand is Z1's point
            "targetS" if nctx.is_some() => vec![V::AF(crate::nodeops::target_s_node4(nctx.as_ref().unwrap().k, g(1).af()))],
            "targetS" => {
                let x = g(1).af();
                let mut v = target_s_leaf(x);
                if x.len() == 37 {
                    let g = crate::mle::range_eq(&x[1..19], last_at(x, 19) + 1);
                    v.iter_mut().for_each(|e| *e *= g);
                }
                vec![V::AF(v)]
            }
            "eqZ" => {
                let (l, rho) = (g(1).f(), g(2).f());
                let w = crate::skipdom::lagrange_weights(&sk.s_pts, l);
                vec![V::AF((0..128).map(|i| w[i % 64] * if (i >> 6) & 1 == 1 { rho } else { F::ONE + rho }).collect())]
            }
            "rowW" => {
                let mut rhi = g(2).af().to_vec();
                rhi.resize(8, F::ZERO);
                vec![V::AF(crate::lincheck::row_weights(g(1).f(), &rhi))]
            }
            "maskRows" => vec![V::AF(mask_rows(g(1).af(), g(2).af()))],
            "walkAB" => {
                // rev. 3.12: one op for `Â₀`, `B̂₀` (the fused walk)
                let (rw, cw) = (g(1).af(), g(2).af());
                let zeros = vec![F::ZERO; rw.len()];
                let (ca, cb) = (circ.transpose(rw, &zeros), circ.transpose(&zeros, rw));
                let dotp = |c: &[F]| -> F {
                    let mut acc = F::ZERO;
                    for (x, y) in c.iter().zip(cw.iter()) {
                        acc += *x * *y;
                    }
                    acc
                };
                vec![V::F(dotp(&ca)), V::F(dotp(&cb))]
            }
            "walkA" | "walkB" => {
                let (rw, cw) = (g(1).af(), g(2).af());
                let zeros = vec![F::ZERO; rw.len()];
                let (ea, eb) = if t[0] == "walkA" { (rw, &zeros[..]) } else { (&zeros[..], rw) };
                let col = circ.transpose(ea, eb);
                let mut acc = F::ZERO;
                for (x, y) in col.iter().zip(cw.iter()) {
                    acc += *x * *y;
                }
                vec![V::F(acc)]
            }
            "phiRS" => vec![V::F(crate::ringswitch::phi(g(1).af(), g(2).f()))],
            "rsWeight" => {
                // 3.13: `rsWeight r [pts] κ ρ`; 3.16: `rsWeight r [pts] κ β act ρ` (claim 2's kind
                // factor with `β` when `act`, else `β = 1`: the plain eq weight, a leaf's)
                let close = t.iter().position(|s| s.ends_with(']')).unwrap();
                let pts: Vec<Vec<K>> = t[2..=close].iter().map(|s| gr(s).ak().to_vec()).collect();
                let rest = &t[close + 1..];
                if rest.len() == 4 && rest[2] == "true" {
                    out.node_matrices_used = true; // the node's kind-weighted claim 2: not here
                }
                let (kap, rho) = (gr(rest[0]).f(), gr(rest[rest.len() - 1]).ak().to_vec());
                match &nctx {
                    Some(nc) if rest.len() == 4 && rest[2] == "true" => {
                        out.node_matrices_used = false;
                        vec![V::K(crate::nodeops::rs_weight4(nc.k, g(1).af(), &pts, kap, gr(rest[1]).f(), &rho))]
                    }
                    _ => vec![V::K(rs_weight_k(g(1).af(), &pts, kap, &rho))],
                }
            }
            "tensorW" => vec![V::K(crate::ntt::xhat(g(1).n(), g(2).ak()))],
            "slotW" => {
                let base = match num(1) {
                    0 => 256,
                    1 => 520,
                    _ => 0,
                };
                let et = eq_table(&pad(g(2).af(), 10));
                let er = eq_table(&pad(g(3).af(), 10));
                let mut acc = F::ZERO;
                for s in 0..256 {
                    acc += et[s] * er[base + s];
                }
                vec![V::F(acc)]
            }
            "shiftTarget" => {
                // revision 4.1 dumps carry `κ_s` as a fourth operand; 3.x's are found from `τ`'s pack
                let kap_s = if t.len() > 4 {
                    g(4).f()
                } else {
                    regs[src.get(&reg(t[1])).expect("τ is a pack")[0] + 42].f()
                };
                let (tau, theta, bnd) = (g(1).af(), g(2).af(), g(3).af());
                let et = eq_table(&pad(theta, 10));
                let dig = |e0: F, e1: F| -> F {
                    let mut s = F::ZERO;
                    for sg in 0..256 {
                        let e = if sg < 128 { e0 } else { e1 };
                        if e.bit(sg % 128) {
                            s += et[sg];
                        }
                    }
                    s
                };
                let g4 = |i: usize| bnd.get(i).copied().unwrap_or(F::ZERO);
                // eq(τ, last), `last = bnd[4 … 21]` (`shiftTargetI`, 18 coordinates, both zero-padded)
                // (3.13 dumps: `bnd` = the 4 digest halves only, the last block all ones on τ)
                let mut p = F::ONE;
                for l in 0..18 {
                    let x = tau.get(l).copied().unwrap_or(F::ZERO);
                    let y = if bnd.len() > 4 { g4(4 + l) } else if l < tau.len() { F::ONE } else { F::ZERO };
                    p *= x * y + (F::ONE + x) * (F::ONE + y);
                }
                vec![V::F(p * dig(g4(2), g4(3)) + kap_s * dig(g4(0), g4(1)))]
            }
            "eqPt" => vec![V::F(eq_point(g(1).af(), g(2).af()))],
            "shiftEq" => vec![V::F(crate::mle::shift_mle(g(1).af(), &pad(g(2).af(), g(1).af().len()), F::ONE))],
            "linkW" => vec![V::F(F::ZERO)],
            // node-only (revision 3.16): a leaf kind's program keeps them `false`; zeros here
            "linkWAll" if nctx.is_some() => vec![V::AF(crate::nodeops::link_w_all4(nctx.as_ref().unwrap().k, g(1).af(), g(2).af()))],
            "linkWAll" => {
                out.node_matrices_used = true;
                vec![V::AF(vec![F::ZERO; 8])]
            }
            // a segment's (revision 4.1, S-F4 `shiftSegI`): operand `τ(18) ‖ L(18)`, `r` the block
            // point; `(eq(τ, r), shift(τ, r) + [L + 1 < 2^18] eq(τ, L)·eq(r, L + 1), eq(r, 0))`.
            // A node's (another operand length) is not implemented here: zeros, recorded.
            "shiftMask" if nctx.is_some() => {
                let r = crate::nodeops::shift_mask4(nctx.as_ref().unwrap().k, g(1).af(), g(2).af());
                vec![V::F(r[0]), V::F(r[1]), V::F(r[2])]
            }
            "shiftMask" => {
                let tl = g(1).af();
                if tl.len() == 36 {
                    let tau = pad(&tl[..18], 18);
                    let rho = pad(&g(2).af()[..g(2).af().len().min(18)], 18);
                    let l = last_at(tl, 18);
                    let mask = if l + 1 < 1 << 18 { crate::mle::eq_at_int(&tau, l) * crate::mle::eq_at_int(&rho, l + 1) } else { F::ZERO };
                    vec![V::F(eq_point(&tau, &rho)), V::F(crate::mle::shift_mle(&tau, &rho, F::ONE) + mask), V::F(crate::mle::eq_at_int(&rho, 0))]
                } else {
                    out.node_matrices_used = true;
                    vec![V::F(F::ZERO), V::F(F::ZERO), V::F(F::ZERO)]
                }
            }
            "evalM" if nctx.is_some() => {
                let nc = nctx.as_ref().unwrap();
                // `evalMN4`: a 32-entry row point is RSV2's stacked call (`evalMX4`), else the own kind's
                let r = if g(1).af().len() == 32 {
                    let kts = [&*nc.kts[0], &*nc.kts[1], &*nc.kts[2]];
                    [crate::nodeops::eval_mx(&kts, &nc.protos, g(1).af(), g(2).af()), F::ZERO, F::ZERO]
                } else {
                    crate::nodeops::eval_m(nc.kt(), &nc.protos, g(1).af(), g(2).af())
                };
                vec![V::F(r[0]), V::F(r[1]), V::F(r[2])]
            }
            "evalL" if nctx.is_some() => {
                let r = crate::nodeops::eval_l(nctx.as_ref().unwrap().k, g(1).af(), g(2).af());
                vec![V::F(r[0]), V::F(r[1]), V::F(r[2])]
            }
            "evalL" | "evalM" => {
                out.node_matrices_used = true;
                vec![V::F(F::ZERO), V::F(F::ZERO), V::F(F::ZERO)]
            }
            "evalMK" => {
                out.node_matrices_used = true;
                vec![V::K(K::ZERO), V::K(K::ZERO), V::K(K::ZERO)]
            }
            "splitDigest" => {
                let d = g(1).d();
                vec![V::F(F::from_bytes(&d[..16])), V::F(F::from_bytes(&d[16..]))]
            }
            "selectHalf" => vec![if g(1).bit() { g(3).clone() } else { g(2).clone() }],
            "keep" => vec![if flag(1) { g(2).clone() } else { g(3).clone() }],
            "hashStmt" => {
                // `stmtDigest`: a leaf statement at `L`/`P`, a node statement at `N` (a group program at
                // an index computes its index's form, S-E12c §1 obstruction 3)
                let s = g(2).b();
                let h: Digest = s[1..33].try_into().unwrap();
                if t[1] == "N" {
                    vec![V::D(crate::blake2s::node_stmt(&h, &s[33..65].try_into().unwrap()))]
                } else {
                    vec![V::D(crate::blake2s::leaf_stmt(&h, u64::from_le_bytes(s[33..41].try_into().unwrap())))]
                }
            }
            "kindSel" => {
                let b = pi[0];
                vec![V::Bit(b == 0x4C), V::Bit(b == 0x50), V::Bit(b == 0x4E)]
            }
            "assertEq" => {
                let ok = !flag(3) || g(1).eqv(g(2));
                fail(ok, &mut out);
                vec![]
            }
            "assertZero" => {
                let ok = !flag(2) || g(1).is_zero();
                fail(ok, &mut out);
                vec![]
            }
            "assertBit" => vec![],
            "assertOneHot" => {
                let n = [g(1).bit(), g(2).bit(), g(3).bit()].iter().filter(|x| **x).count();
                fail(n == 1, &mut out);
                vec![]
            }
            "accept" => vec![],
            op => panic!("line {}: unknown op {op}", ln + 1),
        };
        if prof_on {
            let dt = t_op.elapsed().as_secs_f64();
            if dt > 0.02 {
                eprintln!("  ir line {} {} {:.3}s", ln + 1, t[0], dt);
            }
            match by_op.iter_mut().find(|x| x.0 == t[0]) {
                Some(x) => {
                    x.1 += dt;
                    x.2 += 1;
                }
                None => by_op.push((t[0].to_string(), dt, 1)),
            }
        }
        assert_eq!(new.len(), dst.len(), "line {}: outputs", ln + 1);
        regs.extend(new);
    }
    if prof_on {
        by_op.sort_by(|a, b| b.1.total_cmp(&a.1));
        let tot: f64 = by_op.iter().map(|x| x.1).sum();
        eprintln!("  ir ops {:.3}s (whole run {:.3}s): {}", tot, t_run.elapsed().as_secs_f64(), by_op.iter().take(14).map(|(n, s, c)| format!("{n}×{c}={s:.3}")).collect::<Vec<_>>().join(" "));
    }
    out.regs_out = regs.len();
    (out, regs)
}

/// A segment kind's capacity `2^(m − 14)` from its byte (`FRShape4.SegKind.ofByte?`, `cap`).
pub fn seg_cap(b: u8) -> Option<u64> {
    match b {
        0x50 => Some(1 << 16),
        0x4B => Some(1 << 17),
        0x4C => Some(1 << 18),
        _ => None,
    }
}

/// **`V_A`**, reconstructed from `FRAgg.VAwith (piSizeOf seq4)` (no `V_A` program is dumped: `A` has
/// no SNARK of its own). `prog b` is the dumped segment program of kind byte `b` (`ops-L30/31/32`).
/// The shape and `aggChecks` (on the views `FRSegment.segView`) are checked first, with no query;
/// then `seqAll`: the segment programs in order on the one oracle, each against `segC = leafStmt hᵢ
/// nᵢ`, stopping at the first rejection. The header's bytes 2–7 must be zero (R-4-m5's parse; HEAD's
/// `VAwith` does not read them, and the prover writes zeros).
pub fn run_agg(prog: &dyn Fn(u8) -> Option<String>, circ: &crate::circuit::Circuit, o: &dyn Oracle, vk: &Digest, c: &Digest, pi: &[u8]) -> Run {
    let seg = crate::params::PI_SIZE;
    let no = Run::default();
    let k = pi.get(1).copied().unwrap_or(0) as usize;
    if pi.len() != 48 + k * seg || pi[0] != 0x41 || pi[2..8].iter().any(|&x| x != 0) {
        return no;
    }
    let le = |b: &[u8]| u64::from_le_bytes(b[..8].try_into().unwrap());
    // the views: (kind byte, start, end, n)
    let mut vs = Vec::with_capacity(k);
    for i in 0..k {
        let p = &pi[48 + i * seg..48 + (i + 1) * seg];
        let Some(cap) = seg_cap(p[0]) else { return no };
        let (st, h): (Digest, Digest) = (p[16..48].try_into().unwrap(), p[49..81].try_into().unwrap());
        vs.push((p[0], cap, st, h, le(&p[81..89])));
    }
    let (n, e): (u64, Digest) = (le(&pi[8..16]), pi[16..48].try_into().unwrap());
    let checks = *c == crate::blake2s::leaf_stmt(&e, n)
        && (1..=4).contains(&k)
        && vs.iter().all(|v| 1 <= v.4 && v.4 <= v.1)
        && vs.iter().map(|v| v.4 as u128).sum::<u128>() == n as u128
        && vs.last().map(|v| v.3) == Some(e)
        && vs.windows(2).all(|w| w[1].2 == w[0].3);
    if !checks {
        return no;
    }
    let mut out = Run { ok: true, ..Default::default() };
    for (i, v) in vs.iter().enumerate() {
        let Some(text) = prog(v.0) else { return Run { ok: false, ..out } };
        if i > 0 {
            // the spacer between segments (revision 4.4.1, `FRAgg.aggProgs`)
            o.ask(&crate::agg::spacer_q());
            out.asks += 1;
        }
        let ci = crate::blake2s::leaf_stmt(&v.3, v.4);
        let r = run(&text, circ, o, vk, &ci, &pi[48 + i * seg..48 + (i + 1) * seg]);
        out.asks += r.asks;
        out.node_matrices_used |= r.node_matrices_used;
        if !r.ok {
            out.ok = false;
            out.failed = r.failed.iter().map(|l| l + 1_000_000 * i).collect();
            break;
        }
    }
    out
}

/// `lastAt a o` (S-F4): the number whose bit `l < 18` is set iff entry `o + l` of `a` is `1`.
fn last_at(a: &[F], o: usize) -> u64 {
    (0..18).filter(|&l| a.get(o + l).is_some_and(|x| *x == F::ONE)).map(|l| 1u64 << l).sum()
}

fn pad(a: &[F], n: usize) -> Vec<F> {
    let mut v = a.to_vec();
    v.resize(n.max(a.len()), F::ZERO);
    v
}

/// `lagrangeS vals λ pe` (rev. 3.8): `(P^{ab}*(λ), P^z*(λ))` (S-F2's `lagrangeSI`).
fn lagrange_s(vals: &[F], l: F, pe: &[F]) -> (F, F) {
    let sk = crate::skipdom::skip();
    let wl = crate::skipdom::lagrange_weights(&sk.l_pts, l);
    let pz = &vals[..64];
    let mut pzl = F::ZERO;
    for i in 0..64 {
        pzl += wl[i] * pz[i];
    }
    let mut v = vec![F::ZERO; 127];
    for sg in 0..64 {
        // P^z at S_σ by Lagrange on Λ (F arithmetic, as S-F2's lamAtS)
        let w = crate::skipdom::lagrange_weights(&sk.l_pts, sk.s_pts[sg]);
        let mut x = F::ZERO;
        for i in 0..64 {
            x += w[i] * pz[i];
        }
        v[sg] = x + pe.get(sg).copied().unwrap_or(F::ZERO);
    }
    v[64..].copy_from_slice(&vals[64..127]);
    let w = crate::skipdom::lagrange_weights(&sk.sl_pts[..127], l);
    let mut pab = F::ZERO;
    for i in 0..127 {
        pab += w[i] * v[i];
    }
    (pab, pzl)
}

/// `targetS` of a leaf kind (S-F2's `targetSLeafI`): `P^e(σ) = Σ_hi eq(r_lo, hi) E_chain(σ + 64 hi)`,
/// `r_lo = (ρ₁ … ρ₇, r₀)`, `r` Z1's coordinates.
fn target_s_leaf(r: &[F]) -> Vec<F> {
    let sk = crate::skipdom::skip();
    let mut lo: Vec<F> = sk.rho.to_vec();
    lo.push(r.first().copied().unwrap_or(F::ZERO));
    let h = eq_table(&lo);
    let mut pe = vec![F::ZERO; 64];
    for &p in crate::circuit::e_positions() {
        pe[p & 63] += h[p >> 6];
    }
    pe
}

/// `rsWeight r″ pts κ ρ` over K points (S-F2's `rsWeightI`): `Σ_j κ^j Σ_k c_k eq(p_j^{2^k}, ρ)`.
fn rs_weight_k(rpp: &[F], pts: &[Vec<K>], kap: F, rho: &[K]) -> K {
    let ck = crate::ringswitch::phi_coeffs(rpp);
    let mut out = K::ZERO;
    let mut kj = F::ONE;
    for p in pts {
        let mut q = p.clone();
        let mut acc = K::ZERO;
        for c in &ck {
            let mut e = K::ONE;
            for (a, b) in q.iter().zip(rho.iter()) {
                e = e * (K::ONE + *a + *b);
            }
            acc += e.mulf(*c);
            q.iter_mut().for_each(|x| *x = x.sq());
        }
        out += acc.mulf(kj);
        kj *= kap;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::params::{field_off, FIELD_SIZES, N_FIELDS};

    fn dump(name: &str) -> Option<String> {
        let d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../logs/E1/dump").join(name);
        std::fs::read_to_string(&d).ok()
    }

    /// The dumped Lean program of `L30` (S-F4, revision 4.1, all finals) accepts native m = 30 segment
    /// proofs at `n = 1`, an odd `n` and the full `2^16`, rejects the canaries (the statement of
    /// `n ± 1`, a flipped end), and agrees with the native verifier on a flipped byte in every field
    /// of `π` (both reject).
    #[test]
    fn ir_kat_l30() {
        let Some(text) = dump("ops-L30.txt") else {
            eprintln!("ir_kat_l30: SKIP (logs/E1/dump/ops-L30.txt absent)");
            return;
        };
        let circ = crate::circuit::Circuit::build();
        let o = crate::oracle::Local::keyed(&[8u8; 32]);
        let (vk, s, m) = ([3u8; 32], [4u8; 32], 30usize);
        for n in [1u64, 12_345, 1 << 16] {
            let (pi, _) = crate::leaf::prove_seg(&o, &circ, &vk, &s, m, n);
            let c = crate::leaf::seg_c(&s, n);
            let r = run(&text, &circ, &o, &vk, &c, &pi);
            assert!(r.ok, "n {n}: failed lines {:?}", r.failed);
            assert_eq!(r.asks, crate::params::N_ITEMS);
            let h = crate::blake2s::chain_end(&s, n);
            let mut bad = vec![crate::blake2s::leaf_stmt(&h, n + 1), crate::blake2s::leaf_stmt(&h, n - 1)];
            let mut h2 = h;
            h2[0] ^= 1;
            bad.push(crate::blake2s::leaf_stmt(&h2, n));
            for c2 in bad {
                assert!(!run(&text, &circ, &o, &vk, &c2, &pi).ok, "n {n}: canary accepted");
            }
            if n != 12_345 {
                continue;
            }
            for f in 0..N_FIELDS {
                for at in [0usize, FIELD_SIZES[f] / 2, FIELD_SIZES[f] - 1] {
                    let mut p2 = pi.clone();
                    p2[field_off(f) + at] ^= 0x10;
                    let native = crate::leaf::verify(&o, &circ, &vk, &c, &p2);
                    let lean = run(&text, &circ, &o, &vk, &c, &p2).ok;
                    assert_eq!((native, lean), (false, false), "field {f} byte {at}");
                }
            }
        }
    }

    /// (−) **The mask is needed** (S-F4 `shift_unmasked_link`): with 3.x's unmasked successor table
    /// at the last block, a segment of `n < 2^(m−14)` steps is rejected by the dumped program (and by
    /// the native verifier), although the witness past `n` is zero; at the full length it is accepted.
    #[test]
    fn ir_unmasked_shift_rejected() {
        let Some(text) = dump("ops-L30.txt") else {
            eprintln!("ir_unmasked_shift_rejected: SKIP");
            return;
        };
        let circ = crate::circuit::Circuit::build();
        let o = crate::oracle::Local::keyed(&[10u8; 32]);
        let (vk, s, m) = ([3u8; 32], [6u8; 32], 30usize);
        crate::leaf::NO_MASK.with(|x| x.set(true));
        let runs: Vec<(u64, bool, bool)> = [777u64, 1 << 16]
            .iter()
            .map(|&n| {
                let (pi, _) = crate::leaf::prove_seg(&o, &circ, &vk, &s, m, n);
                let c = crate::leaf::seg_c(&s, n);
                (n, run(&text, &circ, &o, &vk, &c, &pi).ok, crate::leaf::verify(&o, &circ, &vk, &c, &pi))
            })
            .collect();
        crate::leaf::NO_MASK.with(|x| x.set(false));
        assert_eq!(runs, vec![(777, false, false), (1 << 16, true, true)]);
    }

    /// `V_A` reconstructed (`run_agg`) on the dumped `L30` program: an aggregate of two `L30`
    /// segments (`2^16`, then 3 steps) is accepted with `2 × 8,783 + 1` asks; the statement of `n + 1` and
    /// a flipped segment byte are rejected; a broken chaining and a nonzero `hdr_A` byte 2 are rejected
    /// with no query.
    #[test]
    fn ir_agg_l30() {
        let Some(text) = dump("ops-L30.txt") else {
            eprintln!("ir_agg_l30: SKIP (logs/E1/dump/ops-L30.txt absent)");
            return;
        };
        let prog = |b: u8| if b == 0x50 { Some(text.clone()) } else { None };
        let circ = crate::circuit::Circuit::build();
        let o = crate::oracle::Local::keyed(&[9u8; 32]);
        let (vk, s) = ([3u8; 32], [5u8; 32]);
        // two L30 segments (the aggregate's split at m* = 30: full 2^16, then 3)
        let n = (1u64 << 16) + 3;
        let (pi, _) = crate::agg::prove(&o, &circ, &vk, &s, n, 30);
        let e = crate::blake2s::chain_end(&s, n);
        let c = crate::blake2s::leaf_stmt(&e, n);
        assert_eq!(pi[1], 2);
        let r = run_agg(&prog, &circ, &o, &vk, &c, &pi);
        assert!(r.ok && r.asks == 2 * crate::params::N_ITEMS + 1, "{r:?}");
        assert!(crate::agg::verify(&o, &circ, &vk, &c, &pi));
        // rejections: the statement, n + 1, a segment byte, the chaining
        let c2 = crate::blake2s::leaf_stmt(&e, n + 1);
        assert!(!run_agg(&prog, &circ, &o, &vk, &c2, &pi).ok);
        let mut p2 = pi.clone();
        p2[48 + crate::params::PI_SIZE / 2] ^= 8;
        assert!(!run_agg(&prog, &circ, &o, &vk, &c, &p2).ok);
        let mut p3 = pi.clone();
        p3[48 + crate::params::PI_SIZE + 20] ^= 1;
        let r3 = run_agg(&prog, &circ, &o, &vk, &c, &p3);
        assert!(!r3.ok && r3.asks == 0);
        // R-4-m5: a nonzero `hdr_A` byte 2 is rejected with no query (natively too)
        let mut p5 = pi.clone();
        p5[2] = 1;
        let r5 = run_agg(&prog, &circ, &o, &vk, &c, &p5);
        assert!(!r5.ok && r5.asks == 0 && !crate::agg::verify(&o, &circ, &vk, &c, &p5));
    }
}
