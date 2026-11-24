//! R8 (PATCHES.md): the circuit `Q` in binary form, embedded in the shipped prover and pre-decoded by `prover setup`.
//!
//! The text blob ([`crate::circuit::Circuit::from_blob`], 70 MB for q6-node4) is no longer read by the shipped
//! binary. Its loaded form ([`Loaded`]: the normalized, checked circuit and every section the prover uses) is
//! serialized once by `lvm6-prover qpack BLOB OUT` and carried in two encodings of one layout ([`encode`]):
//!
//! - **compact** (`LVM6QC2`): every number a LEB128 varint; the entries (sorted by `(x, o, y)`) as `Δx·4 + o`,
//!   the zigzag `Δy` and an index into the table of distinct coefficients. This is what `build-asm.sh --q` places in
//!   `qblob.s` (`.quad` lines in `.rodata`, symbols `lvm6_qblob` / `lvm6_qblob_len`), linked beside the tiers;
//! - **raw** (`LVM6QR2`): the same numbers as fixed 8-byte little-endian words. `prover setup DIR` decodes the
//!   embedded compact form, runs every check ([`Loaded::check`]) and writes `DIR/lvm6-q.bin` in this form; a step
//!   reads it with one `read` before `ready` and skips the checks.
//!
//! Both start with a header: the magic, the Keccak-256 of the text blob (the blob's identity, as refv's
//! `q_blob_keccak`), `src` (raw form: the Keccak-256 of the compact file it was decoded from; zero in the compact
//! form), a 64-bit checksum and the length of the payload, which ends with [`END`]. A step uses the setup file only
//! if it is the raw form of this binary's own embedded file (`src`) and its checksum holds; otherwise (missing,
//! damaged, from another build) it decodes the embedded form and checks it. The circuit is the same either way, so
//! the proof bytes are too.

use primitives::field::F128;

use crate::circuit::{AuxBits, BOut, Circuit, Csum, Ent, MbExport, PowBits, Src, TReg};

/// R9: the magic's last byte is the shape tag: `0` for `P18` (r8's magics, unchanged), `17` for `P17`. A file of
/// another shape is refused by name ([`header`]), not only by `Circuit::check`.
pub const SHAPE_TAG: u8 = if fs6::params::SHAPE.log_blocks == 17 { 17 } else { 0 };
const fn magic(form: u8) -> [u8; 8] {
    [b'L', b'V', b'M', b'6', b'Q', form, b'2', SHAPE_TAG]
}
pub const MAGIC_COMPACT: &[u8; 8] = &magic(b'C');
pub const MAGIC_RAW: &[u8; 8] = &magic(b'R');
const fn same(a: &[u8; 8], b: &[u8; 8]) -> bool {
    let mut i = 0;
    while i < 8 {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}
const _: () = assert!(SHAPE_TAG != 0 || (same(MAGIC_COMPACT, b"LVM6QC2\0") && same(MAGIC_RAW, b"LVM6QR2\0")));
/// The payload's last number.
pub const END: u64 = 0x5145_4E44;
/// The setup file's name inside the setup directory.
pub const SETUP_FILE: &str = "lvm6-q.bin";
/// magic ‖ id ‖ src ‖ sum ‖ len.
const HDR: usize = 8 + 32 + 32 + 8 + 8;

/// The circuit in use with every section the prover reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loaded {
    pub c: Circuit,
    pub pow: Vec<PowBits>,
    pub bits: Vec<AuxBits>,
    pub bout: Vec<BOut>,
    pub csum: Vec<Csum>,
    pub xsrc: Vec<(usize, usize, u32)>,
    pub minibus: Option<MbExport>,
}

impl Loaded {
    /// Every static check of the text loader (panics at the first violation): the circuit's ([`Circuit::check`]),
    /// the derived words' ([`crate::circuit::check_aux`]: each a `com` word defined once), `CSUM`'s and `XSRC`'s.
    pub fn check(&self) {
        let c = &self.c;
        c.check();
        let mut taken = crate::circuit::check_aux(c, &self.pow, &self.bits, &self.bout);
        for (k, cs) in self.csum.iter().enumerate() {
            assert!(cs.c.len() == crate::circuit::CSUM_BITS && cs.bd.len() == 2 * crate::circuit::CSUM_CHAINS, "CSUM line {k}");
            for d in cs.outputs() {
                assert!(matches!(c.src_of(d as usize), Some((Src::Com, _))) && taken.insert(d), "CSUM line {k}: word {d}");
            }
        }
        for &(i, l, y) in &self.xsrc {
            assert!(
                i < 1 << r3core::layout::XL && l < r3core::layout::MSG_LANES && (y as usize) < 1 << crate::circuit::Y_VARS,
                "XSRC ({i}, {l}, {y})"
            );
        }
    }
}

const SRCS: [Src; 7] = [Src::Com, Src::Ks, Src::Sflat, Src::Sigma, Src::Pub, Src::Qlt, Src::One];

struct W {
    raw: bool,
    b: Vec<u8>,
}

impl W {
    fn u(&mut self, v: u64) {
        if self.raw {
            self.b.extend_from_slice(&v.to_le_bytes());
        } else {
            let mut v = v;
            while v >= 0x80 {
                self.b.push(v as u8 | 0x80);
                v >>= 7;
            }
            self.b.push(v as u8);
        }
    }
    fn z(&mut self, d: i64) {
        self.u(((d << 1) ^ (d >> 63)) as u64);
    }
}

struct R<'a> {
    raw: bool,
    b: &'a [u8],
    at: usize,
}

impl R<'_> {
    #[inline]
    fn u(&mut self) -> Result<u64, String> {
        if self.raw {
            let w = self.b.get(self.at..self.at + 8).ok_or("truncated")?;
            self.at += 8;
            return Ok(u64::from_le_bytes(w.try_into().unwrap()));
        }
        let (mut v, mut sh) = (0u64, 0u32);
        loop {
            let x = *self.b.get(self.at).ok_or("truncated")?;
            self.at += 1;
            if sh == 63 && x > 1 {
                return Err("varint overflow".into());
            }
            v |= ((x & 0x7f) as u64) << sh;
            if x < 0x80 {
                return Ok(v);
            }
            sh += 7;
            if sh > 63 {
                return Err("varint overflow".into());
            }
        }
    }
    fn us(&mut self) -> Result<usize, String> {
        Ok(usize::try_from(self.u()?).map_err(|_| "size")?)
    }
    fn u32(&mut self) -> Result<u32, String> {
        u32::try_from(self.u()?).map_err(|_| "u32 field".into())
    }
    /// A count of items of at least `k` numbers each, bounded by the bytes left, so that a bad count cannot reserve
    /// more than about the file's size.
    fn n(&mut self, k: usize) -> Result<usize, String> {
        let n = self.us()?;
        let per = k.max(1) * if self.raw { 8 } else { 1 };
        if n.saturating_mul(per) > self.b.len() - self.at {
            return Err(format!("count {n} past the end"));
        }
        Ok(n)
    }
    fn z(&mut self) -> Result<i64, String> {
        let v = self.u()?;
        Ok((v >> 1) as i64 ^ -((v & 1) as i64))
    }
}

/// The payload of `l` (one layout; `raw` picks the number encoding).
fn payload(l: &Loaded, raw: bool) -> Vec<u8> {
    let mut w = W { raw, b: Vec::new() };
    let c = &l.c;
    w.u(c.regs.len() as u64);
    for r in &c.regs {
        w.u(SRCS.iter().position(|s| *s == r.src).unwrap() as u64);
        w.u(r.base as u64);
        w.u(r.log as u64);
        w.u(r.off as u64);
    }
    // the distinct coefficients, in first-use order
    let mut ix: std::collections::HashMap<(u64, u64), u64> = std::collections::HashMap::new();
    let mut tab: Vec<(u64, u64)> = Vec::new();
    for e in &c.ents {
        ix.entry((e.c.c0, e.c.c1)).or_insert_with(|| {
            tab.push((e.c.c0, e.c.c1));
            tab.len() as u64 - 1
        });
    }
    w.u(tab.len() as u64);
    tab.iter().for_each(|&(a, b)| {
        w.u(a);
        w.u(b);
    });
    w.u(c.ents.len() as u64);
    let (mut px, mut py) = (0u32, 0i64);
    for e in &c.ents {
        assert!(e.x >= px && e.o < 4, "entries are normalized");
        w.u(((e.x - px) as u64) << 2 | e.o as u64);
        w.z(e.y as i64 - py);
        w.u(ix[&(e.c.c0, e.c.c1)]);
        (px, py) = (e.x, e.y as i64);
    }
    w.u(c.outs.len() as u64);
    let (mut px, mut py) = (0i64, 0i64);
    for &(x, y) in &c.outs {
        w.z(x as i64 - px);
        w.z(y as i64 - py);
        (px, py) = (x as i64, y as i64);
    }
    w.u(c.qlt.len() as u64);
    for (lo, v) in &c.qlt {
        w.u(*lo as u64);
        w.u(v.len() as u64);
        v.iter().for_each(|&x| w.u(x));
    }
    w.u(l.pow.len() as u64);
    for p in &l.pow {
        w.u(p.w as u64);
        w.u(p.bw as u64);
        w.u(p.nb as u64);
    }
    w.u(l.bits.len() as u64);
    for b in &l.bits {
        w.u(b.y as u64);
        w.u(b.dst.len() as u64);
        b.dst.iter().for_each(|d| w.u(d.map_or(0, |d| d as u64 + 1)));
    }
    w.u(l.bout.len() as u64);
    for b in &l.bout {
        w.u(b.y as u64);
        w.u(b.k as u64);
        w.u(b.a as u64);
        w.u(b.d as u64);
    }
    w.u(l.csum.len() as u64);
    for cs in &l.csum {
        w.u(cs.bw as u64);
        w.u(cs.c.len() as u64);
        cs.c.iter().for_each(|&x| w.u(x as u64));
        w.u(cs.bd.len() as u64);
        cs.bd.iter().for_each(|&x| w.u(x as u64));
    }
    w.u(l.xsrc.len() as u64);
    for &(i, lane, y) in &l.xsrc {
        w.u(i as u64);
        w.u(lane as u64);
        w.u(y as u64);
    }
    match &l.minibus {
        None => w.u(0),
        Some(m) => {
            w.u(1);
            w.u(m.seeds.len() as u64);
            w.u(m.reads.len() as u64);
            for (limbs, base, stride, tau, v, fin) in &m.seeds {
                assert_eq!(*limbs, v.len());
                [*limbs, *base, *stride, *tau].iter().for_each(|&x| w.u(x as u64));
                v.iter().for_each(|&x| w.u(x as u64));
                w.u(*fin as u64);
            }
            for (limbs, tau, addr, v, cnt) in &m.reads {
                assert_eq!(*limbs, v.len());
                [*limbs, *tau, *addr].iter().for_each(|&x| w.u(x as u64));
                v.iter().for_each(|&x| w.u(x as u64));
                w.u(*cnt as u64);
            }
        }
    }
    w.u(END);
    w.b
}

/// A fast 64-bit checksum of `b` (not cryptographic: it detects a damaged setup file; the setup is the entry's own).
pub fn checksum(b: &[u8]) -> u64 {
    let mut h = 0x243F_6A88_85A3_08D3u64 ^ b.len() as u64;
    let mut ch = b.chunks_exact(8);
    for w in &mut ch {
        h = (h ^ u64::from_le_bytes(w.try_into().unwrap())).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29);
    }
    let mut t = [0u8; 8];
    t[..ch.remainder().len()].copy_from_slice(ch.remainder());
    (h ^ u64::from_le_bytes(t)).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// `l` in the compact (`raw = false`) or raw form, with its header: `id` the text blob's Keccak-256, `src` (raw form)
/// the Keccak-256 of the compact file it was decoded from (zero in the compact form), the payload's checksum and
/// length.
pub fn encode(l: &Loaded, id: &[u8; 32], src: &[u8; 32], raw: bool) -> Vec<u8> {
    let p = payload(l, raw);
    let mut out = Vec::with_capacity(HDR + p.len());
    out.extend_from_slice(if raw { MAGIC_RAW } else { MAGIC_COMPACT });
    out.extend_from_slice(id);
    out.extend_from_slice(src);
    out.extend_from_slice(&checksum(&p).to_le_bytes());
    out.extend_from_slice(&(p.len() as u64).to_le_bytes());
    out.extend_from_slice(&p);
    out
}

/// The header of an encoded file: (raw, id, src, payload); the payload's length and checksum verified.
pub fn header(b: &[u8]) -> Result<(bool, [u8; 32], [u8; 32], &[u8]), String> {
    let raw = match b.get(..8) {
        Some(m) if m == MAGIC_RAW => true,
        Some(m) if m == MAGIC_COMPACT => false,
        Some(m) if m[..7] == MAGIC_RAW[..7] || m[..7] == MAGIC_COMPACT[..7] => {
            return Err(format!("Q of another shape (tag {}, this build's {SHAPE_TAG})", m[7]));
        }
        _ => return Err("bad magic".into()),
    };
    if b.len() < HDR {
        return Err("short header".into());
    }
    let id: [u8; 32] = b[8..40].try_into().unwrap();
    let src: [u8; 32] = b[40..72].try_into().unwrap();
    let sum = u64::from_le_bytes(b[72..80].try_into().unwrap());
    let len = u64::from_le_bytes(b[80..88].try_into().unwrap());
    if len != (b.len() - HDR) as u64 {
        return Err(format!("payload length {len} vs {} bytes", b.len() - HDR));
    }
    if checksum(&b[HDR..]) != sum {
        return Err("payload checksum".into());
    }
    Ok((raw, id, src, &b[HDR..]))
}

/// Decode an encoded file (either form). Structural checks only: [`Loaded::check`] is the caller's.
pub fn decode(b: &[u8]) -> Result<([u8; 32], Loaded), String> {
    let (raw, id, _, p) = header(b)?;
    let mut r = R { raw, b: p, at: 0 };
    let n = r.n(4)?;
    let mut regs = Vec::with_capacity(n);
    for _ in 0..n {
        let src = *SRCS.get(r.us()?).ok_or("region source")?;
        regs.push(TReg { src, base: r.us()?, log: r.us()?, off: r.us()? });
    }
    let n = r.n(2)?;
    let mut tab = Vec::with_capacity(n);
    for _ in 0..n {
        tab.push(F128::new(r.u()?, r.u()?));
    }
    let n = r.n(3)?;
    let mut ents = Vec::with_capacity(n);
    let (mut x, mut y) = (0u64, 0i64);
    for _ in 0..n {
        let a = r.u()?;
        x += a >> 2;
        y += r.z()?;
        let c = *tab.get(r.us()?).ok_or("coefficient index")?;
        ents.push(Ent { o: (a & 3) as u8, x: u32::try_from(x).map_err(|_| "x")?, y: u32::try_from(y).map_err(|_| "y")?, c });
    }
    let n = r.n(2)?;
    let mut outs = Vec::with_capacity(n);
    let (mut x, mut y) = (0i64, 0i64);
    for _ in 0..n {
        x += r.z()?;
        y += r.z()?;
        outs.push((u32::try_from(x).map_err(|_| "out x")?, u32::try_from(y).map_err(|_| "out y")?));
    }
    let n = r.n(2)?;
    let mut qlt = Vec::with_capacity(n);
    for _ in 0..n {
        let lo = r.us()?;
        let len = r.n(1)?;
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(r.u()?);
        }
        qlt.push((lo, v));
    }
    let n = r.n(3)?;
    let mut pow = Vec::with_capacity(n);
    for _ in 0..n {
        pow.push(PowBits { w: r.us()?, bw: r.us()?, nb: r.us()? });
    }
    let n = r.n(2)?;
    let mut bits = Vec::with_capacity(n);
    for _ in 0..n {
        let y = r.u32()?;
        let nb = r.n(1)?;
        let mut dst = Vec::with_capacity(nb);
        for _ in 0..nb {
            let d = r.u()?;
            dst.push(if d == 0 { None } else { Some(u32::try_from(d - 1).map_err(|_| "bit word")?) });
        }
        bits.push(AuxBits { y, dst });
    }
    let n = r.n(4)?;
    let mut bout = Vec::with_capacity(n);
    for _ in 0..n {
        bout.push(BOut { y: r.u32()?, k: u8::try_from(r.u()?).map_err(|_| "BOUT k")?, a: r.u32()?, d: r.u32()? });
    }
    let n = r.n(3)?;
    let mut csum = Vec::with_capacity(n);
    for _ in 0..n {
        let bw = r.u32()?;
        let k = r.n(1)?;
        let c = (0..k).map(|_| r.u32()).collect::<Result<Vec<_>, _>>()?;
        let k = r.n(1)?;
        let bd = (0..k).map(|_| r.u32()).collect::<Result<Vec<_>, _>>()?;
        csum.push(Csum { bw, c, bd });
    }
    let n = r.n(3)?;
    let mut xsrc = Vec::with_capacity(n);
    for _ in 0..n {
        xsrc.push((r.us()?, r.us()?, r.u32()?));
    }
    let minibus = match r.u()? {
        0 => None,
        1 => {
            let (ns, nr) = (r.n(5)?, r.n(4)?);
            let mut m = MbExport::default();
            for _ in 0..ns {
                let (limbs, base, stride, tau) = (r.n(1)?, r.us()?, r.us()?, r.us()?);
                let v = (0..limbs).map(|_| r.us()).collect::<Result<Vec<_>, _>>()?;
                m.seeds.push((limbs, base, stride, tau, v, r.us()?));
            }
            for _ in 0..nr {
                let (limbs, tau, addr) = (r.n(1)?, r.us()?, r.us()?);
                let v = (0..limbs).map(|_| r.us()).collect::<Result<Vec<_>, _>>()?;
                m.reads.push((limbs, tau, addr, v, r.us()?));
            }
            Some(m)
        }
        _ => return Err("minibus flag".into()),
    };
    if r.u()? != END || r.at != p.len() {
        return Err("no END at the payload's end".into());
    }
    Ok((id, Loaded { c: Circuit { regs, ents, outs, qlt }, pow, bits, bout, csum, xsrc, minibus }))
}

// ------------------------------------------------------------------------------------------- the embedded form

#[cfg(feature = "embedded-q")]
unsafe extern "C" {
    /// `qblob.s` (`build-asm.sh --q`): the compact form, `lvm6_qblob_len` bytes from `lvm6_qblob`.
    static lvm6_qblob: [u8; 0];
    static lvm6_qblob_len: u64;
}

/// The compact form linked into this binary (`embedded-q` builds), else none.
pub fn embedded() -> Option<&'static [u8]> {
    #[cfg(feature = "embedded-q")]
    {
        // SAFETY: `qblob.s` defines `lvm6_qblob_len` bytes of read-only data from `lvm6_qblob`.
        // (the pointer through `black_box`: the declared `[u8; 0]` says nothing about the bytes behind the symbol)
        Some(unsafe {
            let p = std::hint::black_box((&raw const lvm6_qblob).cast::<u8>());
            std::slice::from_raw_parts(p, std::ptr::read_volatile(&raw const lvm6_qblob_len) as usize)
        })
    }
    #[cfg(not(feature = "embedded-q"))]
    None
}

/// The embedded blob's identity (the text blob's Keccak-256), if any.
pub fn embedded_id() -> Option<[u8; 32]> {
    embedded().map(|b| header(b).expect("the embedded Q").1)
}

/// The Keccak-256 of the embedded compact file (a setup file's `src` must be it).
fn embedded_src() -> [u8; 32] {
    keccak256::hash(embedded().expect("an embedded-q build"))
}

/// The embedded circuit, decoded and checked.
pub fn decode_embedded() -> ([u8; 32], Loaded) {
    let (id, l) = decode(embedded().expect("no embedded Q (an `embedded-q` build)")).unwrap_or_else(|e| panic!("the embedded Q: {e}"));
    l.check();
    (id, l)
}

/// The setup directory's file (`$RF_SETUP/lvm6-q.bin`), if it is the raw form of this binary's embedded file (its
/// `src`) and its payload's checksum holds.
fn from_setup() -> Result<Loaded, String> {
    let dir = std::env::var_os("RF_SETUP").ok_or("RF_SETUP unset")?;
    let p = std::path::Path::new(&dir).join(SETUP_FILE);
    let b = std::fs::read(&p).map_err(|e| format!("{}: {e}", p.display()))?;
    let (raw, _, src, _) = header(&b)?;
    if !raw || src != embedded_src() {
        return Err(format!("{}: not the raw form of the embedded Q", p.display()));
    }
    Ok(decode(&b)?.1)
}

/// The circuit of an `embedded-q` build: the setup's raw form if it matches (checked at setup), else the embedded
/// compact form, decoded and checked.
pub fn load_embedded() -> Loaded {
    let t = std::time::Instant::now();
    match from_setup() {
        Ok(l) => {
            eprintln!("r3typed: Q from the setup ({:.3} s)", t.elapsed().as_secs_f64());
            l
        }
        Err(e) => {
            let l = decode_embedded().1;
            eprintln!("r3typed: Q from the embedded form ({e}; {:.3} s)", t.elapsed().as_secs_f64());
            l
        }
    }
}

/// `prover setup`'s part: the embedded form decoded, checked and written raw to `DIR/lvm6-q.bin` (through a temporary
/// name, then renamed). `Ok(None)` for a build without an embedded `Q`.
pub fn setup(dir: &str) -> Result<Option<usize>, String> {
    if embedded().is_none() {
        return Ok(None);
    }
    let (id, l) = decode_embedded();
    let raw = encode(&l, &id, &embedded_src(), true);
    // the raw form must decode to the same circuit
    if decode(&raw)?.1 != l {
        return Err("the raw form does not round-trip".into());
    }
    let (tmp, dst) = (format!("{dir}/{SETUP_FILE}.tmp"), format!("{dir}/{SETUP_FILE}"));
    std::fs::write(&tmp, &raw).map_err(|e| format!("{tmp}: {e}"))?;
    std::fs::rename(&tmp, &dst).map_err(|e| format!("{dst}: {e}"))?;
    Ok(Some(raw.len()))
}
