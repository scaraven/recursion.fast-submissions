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
    fn f(&self) -> F {
        match self {
            V::F(x) => *x,
            _ => F::ZERO,
        }
    }
    fn k(&self) -> K {
        match self {
            V::K(x) => *x,
            _ => K::ZERO,
        }
    }
    fn d(&self) -> Digest {
        match self {
            V::D(x) => *x,
            _ => [0u8; 32],
        }
    }
    fn b(&self) -> &[u8] {
        match self {
            V::B(x) => x,
            _ => &[],
        }
    }
    fn n(&self) -> u64 {
        match self {
            V::N(x) => *x,
            _ => 0,
        }
    }
    fn bit(&self) -> bool {
        matches!(self, V::Bit(true))
    }
    fn af(&self) -> &[F] {
        match self {
            V::AF(x) => x,
            _ => &[],
        }
    }
    fn ak(&self) -> &[K] {
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
    let mut regs: Vec<V> = Vec::with_capacity(110_000);
    // the source registers of each packF/packFK result (for shiftTarget's κ_s)
    let mut src: std::collections::HashMap<usize, Vec<usize>> = std::collections::HashMap::new();
    let mut out = Run { ok: true, ..Default::default() };
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
            "targetS" => vec![V::AF(target_s_leaf(g(1).af()))],
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
                let pts: Vec<Vec<K>> = t[2..t.len() - 2].iter().map(|s| gr(s).ak().to_vec()).collect();
                let (kap, rho) = (gr(t[t.len() - 2]).f(), gr(t[t.len() - 1]).ak().to_vec());
                vec![V::K(rs_weight_k(g(1).af(), &pts, kap, &rho))]
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
                let tau_src = src.get(&reg(t[1])).expect("τ is a pack");
                let kap_s = regs[tau_src[0] + 42].f();
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
                let mut p = F::ONE;
                for x in tau {
                    p *= *x;
                }
                let g4 = |i: usize| bnd.get(i).copied().unwrap_or(F::ZERO);
                vec![V::F(p * dig(g4(2), g4(3)) + kap_s * dig(g4(0), g4(1)))]
            }
            "eqPt" => vec![V::F(eq_point(g(1).af(), g(2).af()))],
            "shiftEq" => vec![V::F(crate::mle::shift_mle(g(1).af(), &pad(g(2).af(), g(1).af().len()), F::ONE))],
            "linkW" => vec![V::F(F::ZERO)],
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
                let s = g(2).b();
                assert!(t[1] == "L" || t[1] == "P", "a leaf program");
                let h: Digest = s[1..33].try_into().unwrap();
                vec![V::D(crate::blake2s::leaf_stmt(&h, u64::from_le_bytes(s[33..41].try_into().unwrap())))]
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
        assert_eq!(new.len(), dst.len(), "line {}: outputs", ln + 1);
        regs.extend(new);
    }
    out.regs_out = regs.len();
    out
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

    /// The dumped Lean program of the `P30` leaf (all finals, S-G dump) accepts a native m = 30
    /// proof, rejects the canary, and agrees with the native verifier on a flipped byte in every
    /// field of `π` (both reject).
    #[test]
    fn ir_kat_p30() {
        let d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../logs/S-G/dump/ops-P.txt");
        let Ok(text) = std::fs::read_to_string(&d) else {
            eprintln!("ir_kat_p30: SKIP (logs/S-G/dump/ops-P.txt absent)");
            return;
        };
        let circ = crate::circuit::Circuit::build();
        let o = crate::oracle::Local::keyed(&[8u8; 32]);
        let (vk, s, m) = ([3u8; 32], [4u8; 32], 30usize);
        let (pi, _) = crate::leaf::prove(&o, &circ, &vk, &s, m);
        let c = crate::leaf::leaf_c(&s, m);
        let r = run(&text, &circ, &o, &vk, &c, &pi);
        assert!(r.ok, "failed lines {:?}", r.failed);
        assert_eq!(r.asks, 8874);
        let mut c2 = c;
        c2[5] ^= 1;
        assert!(!run(&text, &circ, &o, &vk, &c2, &pi).ok);
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
