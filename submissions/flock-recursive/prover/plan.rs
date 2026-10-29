//! **The node data on the runner** (orchestrator's ruling, 2026-10-29): the prover carries the
//! node's M rows in **plan form**, not as the dump (`mrows-p{π}` is 100–115 MB of text): INT-9's
//! `plan-form-p{π}.bin` (`Rev4.planOf4`: each template key's rows once, the prototype's shared input
//! forms, then the pieces in order: sparse skeleton rows and instance placements), read here by its
//! README's specification (`read_planform`), with the prototypes' register forms (`mregs`) and
//! auxiliary imports (`maux`) varint-coded, their programs (`proto-p{π}.txt`) and the kinds' slot
//! tables (`node-N*.txt`), in one blob: LZ-compressed (`lz`), base64 in the binary
//! (`nodeblob.b64`, `include_str!`). At start the prover rebuilds the `Proto`s from it
//! (`node_data`); the KAT (`plan-kat`, test `plan_rebuild_kat`) compares them with the full dump
//! field by field (rows in order, forms, imports, programs).

use crate::field::F;
use crate::mfill::{Aux, KindTab, Proto, Reg, Rows, Ty};
use std::collections::HashMap;
use std::path::Path;

// ---------------------------------------------------------------- varints

#[derive(Default)]
pub struct Wb(pub Vec<u8>);
impl Wb {
    pub fn u(&mut self, mut x: u64) {
        while x >= 0x80 {
            self.0.push((x as u8) | 0x80);
            x >>= 7;
        }
        self.0.push(x as u8);
    }
    pub fn s(&mut self, x: i64) {
        self.u(((x << 1) ^ (x >> 63)) as u64);
    }
    pub fn bytes(&mut self, b: &[u8]) {
        self.u(b.len() as u64);
        self.0.extend_from_slice(b);
    }
}

pub struct Rb<'a> {
    pub b: &'a [u8],
    pub p: usize,
}
impl<'a> Rb<'a> {
    pub fn u(&mut self) -> u64 {
        let mut x = 0u64;
        let mut sh = 0;
        loop {
            let c = self.b[self.p];
            self.p += 1;
            x |= ((c & 0x7f) as u64) << sh;
            if c < 0x80 {
                return x;
            }
            sh += 7;
        }
    }
    pub fn s(&mut self) -> i64 {
        let z = self.u();
        ((z >> 1) as i64) ^ -((z & 1) as i64)
    }
    pub fn bytes(&mut self) -> &'a [u8] {
        let n = self.u() as usize;
        let s = &self.b[self.p..self.p + n];
        self.p += n;
        s
    }
}

// ---------------------------------------------------------------- LZ77 (byte-oriented)

/// `lit_len, literals, match_len − 3 (0: end), distance` tokens; greedy, hash chains, 1 MiB window.
pub fn lz_compress(inp: &[u8]) -> Vec<u8> {
    const W: usize = 1 << 20;
    const HB: usize = 18;
    let n = inp.len();
    let mut out = Wb::default();
    out.u(n as u64);
    let mut head = vec![u32::MAX; 1 << HB];
    let mut prev = vec![u32::MAX; W];
    let hash = |p: usize| -> usize {
        let x = u32::from_le_bytes([inp[p], inp[p + 1], inp[p + 2], inp[p + 3]]);
        (x.wrapping_mul(2654435761) >> (32 - HB)) as usize
    };
    let mut lit = 0usize;
    let mut i = 0usize;
    let insert = |p: usize, head: &mut Vec<u32>, prev: &mut Vec<u32>| {
        if p + 4 <= n {
            let h = hash(p);
            prev[p % W] = head[h];
            head[h] = p as u32;
        }
    };
    while i < n {
        let (mut best, mut bd) = (0usize, 0usize);
        if i + 4 <= n {
            let mut c = head[hash(i)];
            let mut steps = 0;
            while c != u32::MAX && steps < 48 {
                let cp = c as usize;
                if i - cp > W - 1 {
                    break;
                }
                let mut l = 0;
                while i + l < n && inp[cp + l] == inp[i + l] && l < 65535 {
                    l += 1;
                }
                if l > best {
                    best = l;
                    bd = i - cp;
                }
                c = prev[cp % W];
                steps += 1;
            }
        }
        if best >= 4 {
            out.u(lit as u64);
            out.0.extend_from_slice(&inp[i - lit..i]);
            out.u((best - 3) as u64);
            out.u(bd as u64);
            for p in i..i + best {
                insert(p, &mut head, &mut prev);
            }
            i += best;
            lit = 0;
        } else {
            insert(i, &mut head, &mut prev);
            i += 1;
            lit += 1;
        }
    }
    out.u(lit as u64);
    out.0.extend_from_slice(&inp[n - lit..]);
    out.u(0);
    out.0
}

pub fn lz_decompress(b: &[u8]) -> Vec<u8> {
    let mut r = Rb { b, p: 0 };
    let n = r.u() as usize;
    let mut out = Vec::with_capacity(n);
    loop {
        let lit = r.u() as usize;
        out.extend_from_slice(&r.b[r.p..r.p + lit]);
        r.p += lit;
        let m = r.u() as usize;
        if m == 0 {
            break;
        }
        let (l, d) = (m + 3, r.u() as usize);
        let s = out.len() - d;
        for k in 0..l {
            let x = out[s + k];
            out.push(x);
        }
    }
    assert_eq!(out.len(), n, "lz: length");
    out
}

// ---------------------------------------------------------------- base64

const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

pub fn b64_encode(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 4 / 3 + 4);
    for c in b.chunks(3) {
        let x = (c[0] as u32) << 16 | (*c.get(1).unwrap_or(&0) as u32) << 8 | *c.get(2).unwrap_or(&0) as u32;
        for k in 0..4 {
            if k <= c.len() {
                s.push(B64[((x >> (18 - 6 * k)) & 63) as usize] as char);
            } else {
                s.push('=');
            }
        }
    }
    s
}

pub fn b64_decode(s: &str) -> Vec<u8> {
    let mut inv = [255u8; 256];
    for (i, &c) in B64.iter().enumerate() {
        inv[c as usize] = i as u8;
    }
    let mut out = Vec::with_capacity(s.len() * 3 / 4);
    let (mut acc, mut nb) = (0u32, 0);
    for &c in s.as_bytes() {
        let v = inv[c as usize];
        if v == 255 {
            continue;
        }
        acc = acc << 6 | v as u32;
        nb += 6;
        if nb >= 8 {
            nb -= 8;
            out.push((acc >> nb) as u8);
        }
    }
    out
}

// ---------------------------------------------------------------- coefficients

#[derive(Default)]
pub struct Coefs {
    pub v: Vec<F>,
    ix: HashMap<[u8; 16], u32>,
}
impl Coefs {
    fn id(&mut self, x: F) -> u64 {
        let k = x.to_bytes();
        if let Some(&i) = self.ix.get(&k) {
            return i as u64;
        }
        self.v.push(x);
        self.ix.insert(k, (self.v.len() - 1) as u32);
        (self.v.len() - 1) as u64
    }
}

// ---------------------------------------------------------------- INT-9's plan form

fn rd_f(r: &mut Rb) -> F {
    let x = F::from_bytes(&r.b[r.p..r.p + 16]);
    r.p += 16;
    x
}

/// **`plan-form-p{π}.bin`** (INT-9 README, version 1) rebuilt into the prototype's rows, in the
/// pieces' order: a sparse piece's rows as written; an instance `(k, xh, ch, own)` of key `(A, B,
/// rows)` gives template row `j` at row `2^A·xh + j`, its terms instantiated in order (`one` → the
/// `one′` cell; input `i` → `ins[i]` scaled, `ins = shared[k] ++ own`, nothing past `|ins|`; local
/// `k` → `2^B·ch + k`). Returns `(π, rows)`.
pub fn read_planform(b: &[u8]) -> (usize, Rows) {
    assert_eq!(&b[..4], b"FRPF", "plan form magic");
    let mut r = Rb { b, p: 4 };
    assert_eq!(r.u(), 1, "plan form version");
    let pi = r.u() as usize;
    let one = r.u() as u32;
    let nrows = r.u() as usize;
    let nc = r.u() as usize;
    let cf: Vec<F> = (0..nc).map(|_| rd_f(&mut r)).collect();
    // keys: (A, B, rows of three forms of (wire, coef))
    type FormT = Vec<(u64, u32)>;
    let nk = r.u() as usize;
    let mut keys: Vec<(u32, u32, Vec<[FormT; 3]>)> = Vec::with_capacity(nk);
    for _ in 0..nk {
        let (a, bb) = (r.u() as u32, r.u() as u32);
        let nr = r.u() as usize;
        let rows = (0..nr)
            .map(|_| {
                std::array::from_fn(|_| {
                    let n = r.u() as usize;
                    (0..n).map(|_| (r.u(), r.u() as u32)).collect()
                })
            })
            .collect();
        keys.push((a, bb, rows));
    }
    let mut pc = 0i64;
    let lin = |r: &mut Rb, pc: &mut i64| -> Vec<(u32, u32)> {
        let n = r.u() as usize;
        (0..n)
            .map(|_| {
                *pc += r.s();
                (*pc as u32, r.u() as u32)
            })
            .collect()
    };
    let ns = r.u() as usize;
    let shared: Vec<Vec<Vec<(u32, u32)>>> = (0..ns)
        .map(|_| {
            let nf = r.u() as usize;
            (0..nf).map(|_| lin(&mut r, &mut pc)).collect()
        })
        .collect();
    let mut rows = Rows { idx: Vec::with_capacity(nrows), rng: Vec::with_capacity(nrows), cells: Vec::new(), coefs: Vec::new() };
    let np = r.u() as usize;
    let mut prow = 0i64;
    for _ in 0..np {
        let tag = r.b[r.p];
        r.p += 1;
        if tag == 0 {
            let n = r.u() as usize;
            for _ in 0..n {
                prow += r.s();
                let a0 = rows.cells.len() as u32;
                let mut rg = [a0; 4];
                for m in 0..3 {
                    for (c, k) in lin(&mut r, &mut pc) {
                        rows.cells.push(c);
                        rows.coefs.push(cf[k as usize]);
                    }
                    rg[m + 1] = rows.cells.len() as u32;
                }
                rows.idx.push(prow as u32);
                rows.rng.push(rg);
            }
        } else {
            assert_eq!(tag, 1, "plan form piece tag");
            let k = r.u() as usize;
            let (xh, ch) = (r.u() as u32, r.u() as u32);
            let no = r.u() as usize;
            let own: Vec<Vec<(u32, u32)>> = (0..no).map(|_| lin(&mut r, &mut pc)).collect();
            let sh = shared.get(k).map(|v| &v[..]).unwrap_or(&[]);
            let inp = |i: usize| -> Option<&Vec<(u32, u32)>> { if i < sh.len() { sh.get(i) } else { own.get(i - sh.len()) } };
            let (a, bb, ref trs) = keys[k];
            let (x0, cb) = (xh << a, ch << bb);
            for (j, tr) in trs.iter().enumerate() {
                let a0 = rows.cells.len() as u32;
                let mut rg = [a0; 4];
                for m in 0..3 {
                    for &(wire, c) in &tr[m] {
                        let cv = cf[c as usize];
                        match wire & 3 {
                            0 => {
                                rows.cells.push(one);
                                rows.coefs.push(cv);
                            }
                            1 => {
                                if let Some(l) = inp((wire >> 2) as usize) {
                                    for &(cell, d) in l {
                                        rows.cells.push(cell);
                                        rows.coefs.push(cv * cf[d as usize]);
                                    }
                                }
                            }
                            _ => {
                                rows.cells.push(cb + (wire >> 2) as u32);
                                rows.coefs.push(cv);
                            }
                        }
                    }
                    rg[m + 1] = rows.cells.len() as u32;
                }
                rows.idx.push(x0 + j as u32);
                rows.rng.push(rg);
            }
        }
    }
    assert_eq!(rows.idx.len(), nrows, "plan form row count");
    (pi, rows)
}

/// A prototype's register forms and auxiliary imports, varint-coded (cells delta-coded, one
/// running value; coefficients by index).
pub fn encode_regs(p: &Proto, cf: &mut Coefs) -> Vec<u8> {
    let mut w = Wb::default();
    let mut pc = 0i64;
    let put_terms = |w: &mut Wb, a: u32, b: u32, pc: &mut i64, cf: &mut Coefs| {
        w.u((b - a) as u64);
        for t in a as usize..b as usize {
            w.s(p.fcells[t] as i64 - *pc);
            *pc = p.fcells[t] as i64;
            w.u(cf.id(p.fcoefs[t]));
        }
    };
    w.u(p.regs.len() as u64);
    for r in &p.regs {
        let (tag, n) = match r.ty {
            Ty::Untracked => (0, 0),
            Ty::F => (1, 0),
            Ty::K => (2, 0),
            Ty::D => (3, 0),
            Ty::Bit => (4, 0),
            Ty::AF(n) => (5, n),
            Ty::AK(n) => (6, n),
        };
        w.u(tag * 2 + r.imp as u64);
        w.u(n as u64);
        w.u(r.forms.len() as u64);
        for &(a, b) in &r.forms {
            put_terms(&mut w, a, b, &mut pc, cf);
        }
    }
    w.u(p.aux.len() as u64);
    for ax in &p.aux {
        w.u(ax.reg as u64);
        w.u(ax.bits as u64);
        w.u(ax.n as u64);
        put_terms(&mut w, ax.terms.0, ax.terms.1, &mut pc, cf);
    }
    w.0
}

/// A prototype from its plan form (the rows) and `encode_regs`' bytes.
pub fn decode_proto(pf: &[u8], regs: &[u8], cf: &[F]) -> Proto {
    let (pi, rows) = read_planform(pf);
    let r = &mut Rb { b: regs, p: 0 };
    let (mut fcells, mut fcoefs) = (Vec::new(), Vec::new());
    let mut pc = 0i64;
    let get_terms = |r: &mut Rb, fcells: &mut Vec<u32>, fcoefs: &mut Vec<F>, pc: &mut i64| -> (u32, u32) {
        let a = fcells.len() as u32;
        let n = r.u();
        for _ in 0..n {
            *pc += r.s();
            fcells.push(*pc as u32);
            fcoefs.push(cf[r.u() as usize]);
        }
        (a, fcells.len() as u32)
    };
    let nreg = r.u() as usize;
    let mut regs = Vec::with_capacity(nreg);
    for _ in 0..nreg {
        let x = r.u();
        let n = r.u() as usize;
        let ty = match x >> 1 {
            0 => Ty::Untracked,
            1 => Ty::F,
            2 => Ty::K,
            3 => Ty::D,
            4 => Ty::Bit,
            5 => Ty::AF(n),
            _ => Ty::AK(n),
        };
        let nf = r.u() as usize;
        let forms = (0..nf).map(|_| get_terms(r, &mut fcells, &mut fcoefs, &mut pc)).collect();
        regs.push(Reg { imp: x & 1 == 1, ty, forms });
    }
    let na = r.u() as usize;
    let mut aux = Vec::with_capacity(na);
    for _ in 0..na {
        let reg = r.u() as u32;
        let bits = r.u() == 1;
        let n = r.u() as usize;
        let terms = get_terms(r, &mut fcells, &mut fcoefs, &mut pc);
        aux.push(Aux { reg, bits, n, terms });
    }
    Proto { pi, rows, regs, aux, fcells, fcoefs, plan: Default::default(), adj: Default::default(), inactive: Default::default() }
}

// ---------------------------------------------------------------- the blob

/// Everything the node prover reads: the two prototypes and their programs, the kinds' tables.
pub struct NodeData {
    pub protos: std::sync::Arc<[Proto; 2]>,
    pub texts: [String; 2],
    pub kinds: [String; 3],
}

impl NodeData {
    pub fn kind_tab(&self, k: crate::node::NK) -> KindTab {
        KindTab::parse(&self.kinds[k as usize])
    }
    /// The fixed program of node kind `k`: prototype 0's program (`progNodeGK N4c.cells4`, every
    /// kind's real cells) at the kind's index (`L32 P30 N30` = `N4 N2 N8`; INT-8 `Op.at`).
    pub fn node_program(&self, k: crate::node::NK) -> String {
        crate::ir::spec_kind(&self.texts[0], [1, 0, 2][k as usize])
    }
}

/// Build the blob from INT-9's node dump `dd` (`plan-form-p{π}.bin`, `mregs`, `maux`,
/// `proto-p{π}.txt`, `node-N*.txt`). Returns the base64 text and a report.
pub fn build_blob(dd: &Path) -> (String, String) {
    let mut cf = Coefs::default();
    let mut body = Wb::default();
    let mut rep = String::new();
    for pi in 0..2 {
        let pf = std::fs::read(dd.join(format!("plan-form-p{pi}.bin"))).expect("plan-form-p*.bin");
        let p = Proto::load(dd, pi);
        let rg = encode_regs(&p, &mut cf);
        rep.push_str(&format!("p{pi}: plan form {} B, register forms and imports {} B\n", pf.len(), rg.len()));
        body.bytes(&pf);
        body.bytes(&rg);
    }
    for pi in 0..2 {
        body.bytes(&std::fs::read(dd.join(format!("proto-p{pi}.txt"))).expect("proto-p*.txt"));
    }
    for k in ["N2", "N4", "N8"] {
        body.bytes(&std::fs::read(dd.join(format!("node-{k}.txt"))).expect("node-N*.txt"));
    }
    let mut all = Wb::default();
    all.0.extend_from_slice(b"FRNB2");
    all.u(cf.v.len() as u64);
    for x in &cf.v {
        all.0.extend_from_slice(&x.to_bytes());
    }
    all.0.extend_from_slice(&body.0);
    let z = lz_compress(&all.0);
    rep.push_str(&format!("raw {} B; lz {} B; base64 {} B\n", all.0.len(), z.len(), z.len().div_ceil(3) * 4));
    (b64_encode(&z), rep)
}

/// Decode a blob (the prototypes rebuilt in parallel).
pub fn decode_blob(b64: &str) -> NodeData {
    let sp = crate::prof::span("nd.b64");
    let packed = b64_decode(b64);
    drop(sp);
    let sp = crate::prof::span("nd.lz");
    let raw = lz_decompress(&packed);
    drop(sp);
    let _sp = crate::prof::span("nd.parse");
    assert_eq!(&raw[..5], b"FRNB2", "node blob magic");
    let mut r = Rb { b: &raw, p: 5 };
    let nc = r.u() as usize;
    let cf: Vec<F> = (0..nc).map(|_| rd_f(&mut r)).collect();
    let segs: Vec<(&[u8], &[u8])> = (0..2).map(|_| (r.bytes(), r.bytes())).collect();
    let mut ps: Vec<Proto> = crate::par::collect_vec(2, 1, |i| decode_proto(segs[i].0, segs[i].1, &cf));
    let s = |r: &mut Rb| String::from_utf8(r.bytes().to_vec()).expect("utf-8");
    let texts = [s(&mut r), s(&mut r)];
    let kinds = [s(&mut r), s(&mut r), s(&mut r)];
    let p1 = ps.pop().unwrap();
    let p0 = ps.pop().unwrap();
    assert_eq!((p0.pi, p1.pi), (0, 1));
    NodeData { protos: std::sync::Arc::new([p0, p1]), texts, kinds }
}

// ---------------------------------------------------------------- the decoded image (pass 12)

/// The decoded node data as a flat image (`prover setup` writes it as `nodedata.bin` beside the
/// plans; the blob's format is unchanged): `FLNDIMG1`, the blob's tag, then per prototype its
/// fields as length-prefixed little-endian arrays, then the texts. A request loads it with bulk
/// copies instead of the blob's base64, LZ and varint decoding (start-up 0.18 s on the 7763).
pub const IMAGE: &str = "nodedata.bin";

struct Wi(Vec<u8>);
impl Wi {
    fn u(&mut self, x: u64) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }
    fn raw<T: Copy>(&mut self, v: &[T]) {
        self.u(v.len() as u64);
        // SAFETY: plain-data element types (u32, [u32; 4], (u32, u32), F), read back by `Ri::raw`
        self.0.extend_from_slice(unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) });
    }
}
struct Ri<'a> {
    b: &'a [u8],
    p: usize,
}
impl Ri<'_> {
    fn u(&mut self) -> Option<u64> {
        let x = u64::from_le_bytes(self.b.get(self.p..self.p + 8)?.try_into().ok()?);
        self.p += 8;
        Some(x)
    }
    fn raw<T: Copy>(&mut self) -> Option<Vec<T>> {
        let n = usize::try_from(self.u()?).ok()?;
        let bytes = n.checked_mul(std::mem::size_of::<T>())?;
        let src = self.b.get(self.p..self.p.checked_add(bytes)?)?;
        let mut v: Vec<T> = Vec::with_capacity(n);
        // SAFETY: `bytes` bytes are copied into the capacity of `n` elements of a plain-data type
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), v.as_mut_ptr() as *mut u8, bytes);
            v.set_len(n);
        }
        self.p += bytes;
        Some(v)
    }
}

fn ty_code(t: Ty) -> (u64, u64) {
    match t {
        Ty::Untracked => (0, 0),
        Ty::F => (1, 0),
        Ty::K => (2, 0),
        Ty::D => (3, 0),
        Ty::Bit => (4, 0),
        Ty::AF(n) => (5, n as u64),
        Ty::AK(n) => (6, n as u64),
    }
}

/// The image of `nd` (tagged with `tag`, the blob's `data_tag`).
pub fn save_image(nd: &NodeData, tag: &[u8; 32]) -> Vec<u8> {
    let mut w = Wi(b"FLNDIMG1".to_vec());
    w.0.extend_from_slice(tag);
    for p in nd.protos.iter() {
        w.u(p.pi as u64);
        w.raw(&p.rows.idx);
        w.raw(&p.rows.rng);
        w.raw(&p.rows.cells);
        w.raw(&p.rows.coefs);
        // the registers: (imp, type, n, form count) per register, then all forms in one array
        let head: Vec<[u64; 4]> = p.regs.iter().map(|r| { let (c, n) = ty_code(r.ty); [r.imp as u64, c, n, r.forms.len() as u64] }).collect();
        let forms: Vec<(u32, u32)> = p.regs.iter().flat_map(|r| r.forms.iter().copied()).collect();
        w.raw(&head);
        w.raw(&forms);
        let aux: Vec<[u64; 5]> = p.aux.iter().map(|a| [a.reg as u64, a.bits as u64, a.n as u64, a.terms.0 as u64, a.terms.1 as u64]).collect();
        w.raw(&aux);
        w.raw(&p.fcells);
        w.raw(&p.fcoefs);
    }
    for t in nd.texts.iter().chain(nd.kinds.iter()) {
        w.raw(t.as_bytes());
    }
    w.0
}

/// The node data from an image, if it is one and carries `tag`.
pub fn load_image(b: &[u8], tag: &[u8; 32]) -> Option<NodeData> {
    if b.len() < 40 || &b[..8] != b"FLNDIMG1" || &b[8..40] != tag {
        return None;
    }
    let mut r = Ri { b, p: 40 };
    let mut ps = Vec::with_capacity(2);
    for _ in 0..2 {
        let pi = r.u()? as usize;
        let rows = Rows { idx: r.raw()?, rng: r.raw()?, cells: r.raw()?, coefs: r.raw()? };
        let head: Vec<[u64; 4]> = r.raw()?;
        let forms: Vec<(u32, u32)> = r.raw()?;
        let mut at = 0usize;
        let mut regs = Vec::with_capacity(head.len());
        for h in &head {
            let ty = match h[1] {
                0 => Ty::Untracked,
                1 => Ty::F,
                2 => Ty::K,
                3 => Ty::D,
                4 => Ty::Bit,
                5 => Ty::AF(h[2] as usize),
                6 => Ty::AK(h[2] as usize),
                _ => return None,
            };
            let e = at.checked_add(h[3] as usize)?;
            regs.push(Reg { imp: h[0] == 1, ty, forms: forms.get(at..e)?.to_vec() });
            at = e;
        }
        let aux = r.raw::<[u64; 5]>()?.into_iter().map(|a| Aux { reg: a[0] as u32, bits: a[1] == 1, n: a[2] as usize, terms: (a[3] as u32, a[4] as u32) }).collect();
        let (fcells, fcoefs) = (r.raw()?, r.raw()?);
        ps.push(Proto { pi, rows, regs, aux, fcells, fcoefs, plan: Default::default(), adj: Default::default(), inactive: Default::default() });
    }
    let mut s = || String::from_utf8(r.raw::<u8>()?).ok();
    let texts = [s()?, s()?];
    let kinds = [s()?, s()?, s()?];
    let p1 = ps.pop()?;
    let p0 = ps.pop()?;
    (p0.pi == 0 && p1.pi == 1).then(|| NodeData { protos: std::sync::Arc::new([p0, p1]), texts, kinds })
}

/// The embedded blob (`nodeblob.b64`, generated by `flock-prover plan-build`).
pub static BLOB: &str = include_str!("nodeblob.b64");

/// A tag of the node data in use (`mfill::save_plans`): the embedded blob's hash, or a fixed tag for
/// the dump directories (`FLOCK_NODE_DUMP`).
pub fn data_tag() -> [u8; 32] {
    static T: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    *T.get_or_init(|| {
        if std::env::var_os("FLOCK_NODE_DUMP").is_some() || BLOB.len() < 16 {
            crate::blake2s::blake2s256(b"flock-recursive node dump")
        } else {
            crate::blake2s::blake2s256(BLOB.as_bytes())
        }
    })
}

/// The node data: from the dumps when `FLOCK_NODE_DUMP` is set (development), else the embedded
/// blob (the runner), decoded once.
pub fn node_data() -> &'static NodeData {
    static D: std::sync::OnceLock<NodeData> = std::sync::OnceLock::new();
    D.get_or_init(|| {
        if std::env::var_os("FLOCK_NODE_DUMP").is_some() || BLOB.len() < 16 {
            let (dd, pd) = crate::mfill::find_dirs().expect("no node dump and no blob");
            let rd = |p: std::path::PathBuf| std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
            NodeData {
                protos: std::sync::Arc::new([Proto::load(&dd, 0), Proto::load(&dd, 1)]),
                texts: [rd(pd.join("proto-p0.txt")), rd(pd.join("proto-p1.txt"))],
                kinds: ["N2", "N4", "N8"].map(|k| rd(dd.join(format!("node-{k}.txt")))),
            }
        } else {
            // `prover setup`'s image of this blob, if there is one (pass 12), else the blob
            let img = std::env::var_os("RF_SETUP").and_then(|d| std::fs::read(std::path::Path::new(&d).join(IMAGE)).ok());
            let sp = crate::prof::span("nd.image");
            let nd = img.and_then(|b| load_image(&b, &data_tag()));
            drop(sp);
            nd.unwrap_or_else(|| decode_blob(BLOB))
        }
    })
}

/// **The KAT**: two prototypes equal field by field (rows in order, register forms, imports).
pub fn proto_eq(a: &Proto, b: &Proto) -> Result<(), String> {
    if a.pi != b.pi {
        return Err("pi".into());
    }
    let (x, y) = (&a.rows, &b.rows);
    if x.idx != y.idx || x.rng != y.rng || x.cells != y.cells || x.coefs != y.coefs {
        let i = (0..x.idx.len().min(y.idx.len())).find(|&i| x.idx[i] != y.idx[i] || x.rng[i] != y.rng[i]).unwrap_or(0);
        return Err(format!("rows differ (lengths {} / {}, first at {i})", x.idx.len(), y.idx.len()));
    }
    if a.regs.len() != b.regs.len() || a.regs.iter().zip(&b.regs).any(|(r, s)| r.imp != s.imp || r.ty != s.ty || r.forms != s.forms) {
        return Err("register forms differ".into());
    }
    if a.aux.len() != b.aux.len() || a.aux.iter().zip(&b.aux).any(|(r, s)| r.reg != s.reg || r.bits != s.bits || r.n != s.n || r.terms != s.terms) {
        return Err("auxiliary imports differ".into());
    }
    if a.fcells != b.fcells || a.fcoefs != b.fcoefs {
        return Err("form cells differ".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn lz_b64_roundtrip() {
        let mut v: Vec<u8> = Vec::new();
        for i in 0..200_000u32 {
            v.extend_from_slice(format!("addK r{} r{} → r{}\n", i % 977, i * 3 % 1013, i).as_bytes());
        }
        let z = super::lz_compress(&v);
        assert!(z.len() < v.len() * 3 / 5, "{} of {}", z.len(), v.len());
        assert_eq!(super::lz_decompress(&z), v);
        let s = super::b64_encode(&z[..1001]);
        assert_eq!(super::b64_decode(&s), &z[..1001]);
    }

    /// The embedded blob rebuilds the prototypes of the dump it was built from (when the dump is
    /// present).
    #[test]
    fn plan_rebuild_kat() {
        if super::BLOB.len() < 16 {
            eprintln!("plan_rebuild_kat: SKIP (no blob)");
            return;
        }
        let Some((dd, _)) = crate::mfill::find_dirs() else { return };
        if !dd.join("mrows-p0.txt").is_file() {
            return;
        }
        let nd = super::decode_blob(super::BLOB);
        for pi in 0..2 {
            let p = crate::mfill::Proto::load(&dd, pi);
            super::proto_eq(&nd.protos[pi], &p).unwrap();
        }
    }
}

#[cfg(test)]
mod pass12_tests {
    use super::*;

    /// The image round-trips the embedded blob's node data (every field: the image of the loaded
    /// image is the same bytes, and the bulk arrays are equal), and a foreign tag or a cut image is
    /// refused.
    #[test]
    fn image_round_trip() {
        if BLOB.len() < 16 {
            return;
        }
        let nd = decode_blob(BLOB);
        let tag = [7u8; 32];
        let img = save_image(&nd, &tag);
        let back = load_image(&img, &tag).expect("image loads");
        assert_eq!(save_image(&back, &tag), img);
        for (p, q) in nd.protos.iter().zip(back.protos.iter()) {
            assert!(p.rows.idx == q.rows.idx && p.rows.rng == q.rows.rng && p.rows.cells == q.rows.cells && p.rows.coefs == q.rows.coefs);
            assert!(p.fcells == q.fcells && p.fcoefs == q.fcoefs && p.regs.len() == q.regs.len() && p.aux.len() == q.aux.len());
            assert!(p.regs.iter().zip(&q.regs).all(|(a, b)| a.imp == b.imp && a.ty == b.ty && a.forms == b.forms));
            assert!(p.aux.iter().zip(&q.aux).all(|(a, b)| a.reg == b.reg && a.bits == b.bits && a.n == b.n && a.terms == b.terms));
        }
        assert!(nd.texts == back.texts && nd.kinds == back.kinds);
        assert!(load_image(&img, &[8u8; 32]).is_none());
        assert!(load_image(&img[..img.len() - 1], &tag).is_none());
    }
}
