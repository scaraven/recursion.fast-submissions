//! B1-IE (roll 8): B1-IX's typed blob (`qasm genb`, `prover/src/lvm/q-p20.blob`): the B program's LOOPIR1 tokens, then
//! - `TYPED tOff comLog freeLo n {src base log dst}` (the word space's regions and their targets: `com`, `ks` a
//!   `C_main` word, `sigma` a `C_rec` word, `sflat` a stream position, `pub` a header lane, `one`),
//! - `MINIBUS nSeed {tau base stride valRec valOff finOff} nRead {tau wa wv wc}` (`mbT`: seeds, then read tables),
//! - `CONST n {lo len values…}` (QLT's cells, constants of `Φ_Q`),
//! - `HDR pubLanes {selector}` (`PUB`'s lanes: `hdrSel`),
//! - `END`.
//!
//! The program's input arrays and `BITS` (what the run reads from the commitments and the fixpoint) come from the
//! `M3B` supplement B1-IE's `ietool m3b` emits from the same frozen instance (`qb-p20.m3b`: `qasm gen`'s section
//! with no groups).
use crate::lvm::typed_mb::{MbRead, MbSeed, MbSpec};
use crate::lvm::typed_prove::{TData, TReg};

/// The parsed sections.
pub struct TypedBlob {
    /// The LOOPIR1 tokens (the program part, as `loopir::parse_blob` reads it).
    pub program: String,
    pub td: TData,
    pub t_off: usize,
    pub free_lo: usize,
    pub mb: MbSpec,
    /// `(lo, values)` of the constant cells.
    pub cst: Vec<(usize, Vec<u64>)>,
    /// `PUB`'s lane selectors.
    pub hdr: Vec<usize>,
}

struct Cur<'a> {
    t: Vec<&'a str>,
    i: usize,
}

impl Cur<'_> {
    fn n(&mut self) -> usize {
        let v = self.t[self.i].parse().unwrap_or_else(|_| panic!("typed blob: number {:?} at token {}", self.t[self.i], self.i));
        self.i += 1;
        v
    }
    fn word(&mut self) -> &str {
        self.i += 1;
        self.t[self.i - 1]
    }
    fn tag(&mut self, w: &str) {
        assert_eq!(self.word(), w, "typed blob: the {w} section");
    }
}

pub fn parse(text: &str) -> TypedBlob {
    let toks: Vec<&str> = text.split_ascii_whitespace().collect();
    let at = toks.iter().position(|&t| t == "TYPED").expect("typed blob: the TYPED section");
    let program = toks[..at].join(" ");
    let mut c = Cur { t: toks, i: at + 1 };
    let (t_off, _com_log, free_lo, nregs) = (c.n(), c.n(), c.n(), c.n());
    let mut td = TData::default();
    for _ in 0..nregs {
        let src = c.word().to_string();
        let (base, log, dst) = (c.n(), c.n(), c.n());
        match src.as_str() {
            "com" => td.com.push(TReg { base, log, off: dst }),
            "ks" => td.ks.push(TReg { base, log, off: dst }),
            "sigma" => td.sig.push(TReg { base, log, off: dst }),
            "sflat" => {
                assert_eq!((log, dst), (19, 0), "typed blob: S_flat is 2^19 positions from 0");
                td.sflat = base
            }
            "pub" => {
                assert_eq!((log, dst), (10, 0), "typed blob: PUB is 2^10 header lanes from 0");
                td.pubb = base
            }
            "one" => td.one = base,
            x => panic!("typed blob: region source {x:?}"),
        }
    }
    c.tag("MINIBUS");
    let mut mb = MbSpec::default();
    for _ in 0..c.n() {
        let (tau, base, stride, vr, vo, fo) = (c.n(), c.n(), c.n(), c.n(), c.n(), c.n());
        mb.seeds.push(MbSeed { base, stride, tau, val: (vr == 1, vo), fin: (false, fo) });
    }
    for _ in 0..c.n() {
        let (tau, wa, wv, wc) = (c.n(), c.n(), c.n(), c.n());
        mb.reads.push(MbRead { blk: usize::MAX, row: usize::MAX, tau, wa: (false, wa), wv: (false, wv), cnt: (false, wc) });
    }
    c.tag("CONST");
    let mut cst = Vec::new();
    for _ in 0..c.n() {
        let (lo, len) = (c.n(), c.n());
        let vs: Vec<u64> = (0..len).map(|_| c.n() as u64).collect();
        cst.push((lo, vs));
    }
    c.tag("HDR");
    let hdr: Vec<usize> = (0..c.n()).map(|_| c.n()).collect();
    c.tag("END");
    assert_eq!(c.i, c.t.len(), "typed blob: nothing after END");
    TypedBlob { program, td, t_off, free_lo, mb, cst, hdr }
}
