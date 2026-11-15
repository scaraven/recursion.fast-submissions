//! B1-IE dev commands (not on any proving path):
//! - `lvm-prover tlay DIR INPUTS`: the B program (`DIR/prog.blob`, B1-IE's `ietool dump`) on its typed layout
//!   (`DIR/layout.txt`, B1-K's `layDump`) and an `LVM_TYPED_DUMP` input file: the run, the words, the entries; checks
//!   `Φ_Q` against the Lean `PhiQC` values at B1-K's points (`DIR/phi.txt`), the relation on every slot (by row
//!   tag), and the class kernels against the sparse evaluator.
use std::time::Instant;

use crate::lv::primitives::field::{F64, F192};
use crate::lvm::typed::{Inputs, Typed, phi_multi, read_inputs, run_fixpoint};
use crate::lvm::typed_lay::{self, TLay, Words};
use crate::lvm::typed_phi::PhiK;

/// B1-K's `wire` points (`randPt seed`, 43 coordinates).
pub fn rand_pt(seed: u64) -> Vec<F192> {
    let rnd = |mut s: u64| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let mut s = (seed + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    (0..43)
        .map(|_| {
            let a = rnd(s);
            let b = rnd(a);
            let c = rnd(b);
            s = c;
            F192::new(a, b, c)
        })
        .collect()
}

pub struct Loaded {
    pub c: crate::lvm::loopir::Compiled,
    pub spec: crate::lvm::loopir::M3Spec,
    pub lay: TLay,
}

pub fn load(dir: &str) -> Loaded {
    let text = std::fs::read_to_string(format!("{dir}/prog.blob")).expect("prog.blob");
    let (prog, spec) = crate::lvm::loopir::parse_blob(&text);
    let c = crate::lvm::loopir::Compiled::new(prog);
    let lay = TLay::parse(&std::fs::read_to_string(format!("{dir}/layout.txt")).expect("layout.txt"));
    Loaded { c, spec: spec.expect("an M3B section"), lay }
}

pub fn cmd_tlay(args: &[String]) {
    let dir = args.get(2).expect("DIR");
    let ia = args.get(3).expect("INPUTS | zero");
    crate::lv::parallel::init();
    let t = Instant::now();
    let Loaded { c, spec, lay } = load(dir);
    // `zero`: zero inputs (the static checks only: Φ_Q against the Lean PhiQC, the class kernels)
    let mut inp: Inputs = if ia == "zero" { Inputs { in_k: vec![F64::ZERO; c.q.n_in[0]], in_e: vec![F192::ZERO; c.q.n_in[1]], hdr: Vec::new() } } else { read_inputs(ia) };
    // the dump's QLT cells are its pin's: this program's constants (`DIR/cst.txt`, `qltCst`) replace them
    if let Ok(cst) = std::fs::read_to_string(format!("{dir}/cst.txt")) {
        for l in cst.lines() {
            let v: Vec<u64> = l.split_whitespace().skip(1).map(|t| t.parse().unwrap()).collect();
            let (lo, n) = (v[0] as usize, v[1] as usize);
            for i in 0..n {
                inp.in_k[lo + i] = F64(v[2 + i]);
            }
        }
    }
    println!("tlay: program cells K {} E {}, blocks {}; layout blocks {}, xs {}, aux {}, yregs {} ({:.2} s)", c.cells[0], c.cells[1], c.q.blocks.len(), lay.blocks.len(), lay.xs.len(), lay.aux.len(), lay.yregs.len(), t.elapsed().as_secs_f64());
    let t = Instant::now();
    let run = run_fixpoint(&c, &spec, &inp);
    println!("run ok {} inb {} ({:.3} s)", run.ok, run.inb, t.elapsed().as_secs_f64());
    let t = Instant::now();
    let w = Words::new(&c, &lay);
    let e = typed_lay::entries(&c, &lay, &w, &run.kc);
    let n_ent = e.ents.len();
    let b1 = typed_lay::typed_of(e, &lay);
    println!("{} ({:.3} s; {n_ent} nonzero entries)", b1.report, t.elapsed().as_secs_f64());
    // Φ_Q against the Lean PhiQC
    if let Ok(phi) = std::fs::read_to_string(format!("{dir}/phi.txt")) {
        let mut want = Vec::new();
        for l in phi.lines() {
            let t: Vec<&str> = l.split_whitespace().collect();
            if t.first() == Some(&"P") {
                want.push((t[1].parse::<u64>().unwrap(), F192::new(t[2].parse().unwrap(), t[3].parse().unwrap(), t[4].parse().unwrap())));
            }
        }
        let pts: Vec<Vec<F192>> = want.iter().map(|&(s, _)| rand_pt(s)).collect();
        let got = phi_multi(&b1, &pts);
        for ((s, w), g) in want.iter().zip(&got) {
            println!("Φ_Q(randPt {s}) {} Lean PhiQC", if w == g { "==" } else { "!=" });
        }
    }
    // the witness and the relation
    let t = Instant::now();
    let mut z = typed_lay::witness(&c, &lay, &w, &run.kc, &run.ec);
    let nb = typed_lay::fill_bits(&mut z, &lay, &spec, &run.kc);
    println!("witness ({:.3} s; {nb} BITS bit words)", t.elapsed().as_secs_f64());
    check_rel(&b1, &z, &c);
    let t = Instant::now();
    let pk = PhiK::new(&b1);
    println!("{} ({:.3} s)", pk.report, t.elapsed().as_secs_f64());
    let mut r = crate::lvm::typed::Rng::new(77);
    let pts: Vec<Vec<F192>> = (0..3).map(|_| (0..43).map(|_| r.e()).collect()).collect();
    let k = pk.eval(&pts);
    let s = phi_multi(&b1, &pts);
    println!("phik == sparse at 3 random points: {}", k == s);
}

/// The relation per slot, failures by row tag.
pub fn check_rel(b1: &Typed, z: &[F64], c: &crate::lvm::loopir::Compiled) {
    let abc = b1.abc(z);
    let bad = b1.check(&abc);
    let nb = c.q.blocks.len();
    let tot: usize = bad.iter().map(|b| b.1).sum();
    let nbad_aux = bad.iter().filter(|b| b1.tags.get(b.0 as usize).is_some_and(|t| t.0 >= nb)).count();
    let nbad_ops: std::collections::BTreeMap<String, usize> = bad.iter().fold(Default::default(), |mut m, b| {
        let k = match b1.tags.get(b.0 as usize) {
            Some(&(blk, t)) if blk < nb => format!("{:?}", c.q.blocks[blk].tpl[t].op.kind()),
            Some(_) => "aux".into(),
            None => "untagged".into(),
        };
        *m.entry(k).or_default() += b.1;
        m
    });
    println!("relation: {tot} failing slots in {} rows ({nbad_aux} aux rows); by kind {nbad_ops:?}", bad.len());
    for (tag, n, x) in bad.iter().take(12) {
        let (b, t) = b1.tags.get(*tag as usize).copied().unwrap_or((usize::MAX, 0));
        let what = if b < nb { format!("block {b} row {t} ({:?})", c.q.blocks[b].tpl[t].op) } else if b == usize::MAX { "untagged".into() } else { format!("aux {} row {t}", b - nb) };
        println!("  {what}: {n} slots, first {x}");
    }
}

// ---------------------------------------------------------------- a replica of V_S's typed phases (dev)

/// The signed trace as V_S's reader sees it (`LvmDecideBase.DM`): entries `query ‖ answer`, a query being the
/// state (32 B) then the message; `read_e` takes the next 24-byte scalar of the current message, `sample` the
/// current entry's answer (lanes 0–2) and moves to the next entry.
pub struct Reader<'a> {
    pub tr: &'a [(Vec<u8>, crate::oracle::Digest)],
    pub ent: usize,
    pub msg: usize,
    pub ok: bool,
}

impl<'a> Reader<'a> {
    pub fn new(tr: &'a [(Vec<u8>, crate::oracle::Digest)]) -> Self {
        // after q₀ and the seed
        Reader { tr, ent: 2, msg: 0, ok: true }
    }
    pub fn skip(&mut self, n: usize) {
        self.msg += n;
    }
    pub fn read_e(&mut self) -> F192 {
        let q = &self.tr[self.ent].0;
        let o = 32 + self.msg;
        let l = |i: usize| q.get(o + 8 * i..o + 8 * i + 8).map_or(0, |b| u64::from_le_bytes(b.try_into().unwrap()));
        self.msg += 24;
        F192::new(l(0), l(1), l(2))
    }
    pub fn read_es(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.read_e()).collect()
    }
    pub fn sample(&mut self) -> F192 {
        assert_eq!(self.tr[self.ent].0.len(), 32 + self.msg, "entry {}: the message is read whole before its answer", self.ent);
        let a = &self.tr[self.ent].1;
        let l = |i: usize| u64::from_le_bytes(a[8 * i..8 * i + 8].try_into().unwrap());
        self.ent += 1;
        self.msg = 0;
        F192::new(l(0), l(1), l(2))
    }
    pub fn samples(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }
    pub fn require(&mut self, c: bool, what: &str) {
        if !c && self.ok {
            println!("  V replica: {what} fails");
        }
        self.ok &= c;
    }
    /// `sumcheck claim count eqs` (`LvmDecideSumcheck`): the challenges and the final claim.
    pub fn sumcheck(&mut self, mut claim: F192, count: usize, eqs: &[Option<F192>]) -> (Vec<F192>, F192) {
        let mut pt = Vec::new();
        for e in eqs {
            let q: Vec<F192> = match e {
                None => {
                    let c0 = self.read_e();
                    let tail = self.read_es(count - 2);
                    let s: F192 = tail.iter().copied().sum();
                    [vec![c0, claim + s], tail].concat()
                }
                Some(r) => {
                    let tail = self.read_es(count - 1);
                    let s: F192 = tail.iter().copied().sum();
                    [vec![claim + *r * s], tail].concat()
                }
            };
            let ch = self.sample();
            claim = poly_eval(&q, ch);
            pt.push(ch);
        }
        (pt, claim)
    }
}

use crate::lv::primitives::multilinear::poly_eval;

/// The replica of `dTypedT`'s first four phases (zerocheck, wiring, relayout, A23) and `decideFT`'s `Φ_Q` check, on
/// the trace from entry 2 (after the caps of `cm_cap`, `cr_cap` nodes). The region weights by brute force over the
/// regions (`affW`, `relayKern`, `virtE` as `LvmTypedSpec` sums them); `Φ_Q` by the sparse evaluator; the claims'
/// values against the commitments' extensions (the openings, trusted here).
#[allow(clippy::too_many_arguments)]
pub fn verify_core(
    tr: &[(Vec<u8>, crate::oracle::Digest)],
    caps: usize,
    b1: &Typed,
    td: &crate::lvm::typed_prove::TData,
    hdr: &[u64],
    acc_in: &crate::lvm::acc::Acc,
    cmain: &[F64],
    s_off: usize,
) -> bool {
    use crate::lvm::typed_prove::{SFLAT_LOG, eq_at, sflat_word};
    let mut r = Reader::new(tr);
    r.skip(caps * 32);
    // zerocheck
    let tau = r.samples(20);
    let (rx, fz) = r.sumcheck(F192::ZERO, 3, &tau.iter().map(|&t| Some(t)).collect::<Vec<_>>());
    let abc = r.read_es(3);
    r.require(fz == abc[0] * abc[1] + abc[2], "zerocheck final");
    // wiring
    let g = r.sample();
    let (ry, fw) = r.sumcheck(abc[0] + g * abc[1] + g * g * abc[2], 3, &vec![None; 21]);
    let vs = r.read_es(4);
    let rv = r.read_es(4);
    let virt: F192 = (0..1usize << 10).map(|i| eq_at(&ry, td.pubb + i) * F192::from(F64(hdr.get(i).copied().unwrap_or(0)))).sum::<F192>() + eq_at(&ry, td.one);
    let s_rv: F192 = rv.iter().copied().sum();
    r.require(fw == (vs[0] + g * vs[1] + g * g * (vs[2] + vs[3])) * (s_rv + virt), "wiring final");
    // relayout
    let (rr, fr) = r.sumcheck(rv[1], 3, &vec![None; SFLAT_LOG]);
    let v_r = r.read_e();
    let kern: F192 = (0..1usize << SFLAT_LOG).map(|p| eq_at(&ry, td.sflat + p) * eq_at(&rr, sflat_word(p))).sum();
    r.require(fr == kern * v_r, "relayout final");
    // A23
    let kappa = r.samples(2);
    let h = r.read_es(44);
    let t = r.sample();
    let zs = r.read_e();
    r.require(h[0] == acc_in.y, "h(0) = acc_in.y");
    let eo = crate::lvm::typed::eq_o(&kappa);
    r.require(h.iter().copied().sum::<F192>() == (0..4).map(|o| eo[o] * vs[o]).sum::<F192>(), "h(1) = Σ eq(κ, o)·v_o");
    r.require(zs == F192::ZERO, "the zero scalar");
    let b: Vec<F192> = [&kappa[..], &rx, &ry].concat();
    let pt = crate::lvm::acc::line(&acc_in.pt, &b, t);
    let y = poly_eval(&h, t);
    let core = r.ok;
    let phi = phi_multi(b1, std::slice::from_ref(&pt))[0];
    // the claims against the commitments
    let reg = |regs: &[crate::lvm::typed_prove::TReg], f: &[F64]| -> F192 {
        regs.iter().map(|g| eq_at(&ry[g.log..], g.base >> g.log) * crate::lv::primitives::multilinear::mle_eval_par(&f[g.off..g.off + (1 << g.log)], &ry[..g.log])).sum()
    };
    let c_ok = [
        ("relayout point", crate::lv::primitives::multilinear::mle_eval_par(&cmain[s_off..s_off + (1 << SFLAT_LOG)], &rr) == v_r),
        ("σ′ region", reg(&td.sig, cmain) == rv[2]),
        ("com region", reg(&td.com, cmain) == rv[0]),
        ("KS region", reg(&td.ks, cmain) == rv[3]),
    ];
    for (n, ok) in &c_ok {
        if !ok {
            println!("  V replica: claim {n} is not the commitment's");
        }
    }
    println!("  V replica: core {core}, Φ_Q(acc_out) = y: {}, claims {}", phi == y, c_ok.iter().all(|c| c.1));
    core && phi == y && c_ok.iter().all(|c| c.1)
}

/// `lvm-prover tprove DIR INPUTS`: the typed core end to end on a local oracle, from the dump's inputs: a `C_main`
/// holding the stream block `S` (the stream and `σ′` from the input cells; R11, S2GM: P20's `S`), the committed
/// regions and a `KS` block from the `KS` inputs (a stand-in: the dev layout's `KS` region is the inputs' words), the
/// replica verifier.
pub fn cmd_tprove(args: &[String]) {
    use crate::lvm::typed_prove::{self, TData, TReg};
    let dir = args.get(2).expect("DIR");
    let mut inp: Inputs = read_inputs(args.get(3).expect("INPUTS"));
    crate::oracle::install(Box::new(crate::oracle::Local::keyed(&[0x5A; 32])));
    crate::lv::parallel::init();
    let Loaded { c, spec, lay } = load(dir);
    if let Ok(cst) = std::fs::read_to_string(format!("{dir}/cst.txt")) {
        for l in cst.lines() {
            let v: Vec<u64> = l.split_whitespace().skip(1).map(|t| t.parse().unwrap()).collect();
            for i in 0..v[1] as usize {
                inp.in_k[v[0] as usize + i] = F64(v[2 + i]);
            }
        }
    }
    let run = run_fixpoint(&c, &spec, &inp);
    let w = Words::new(&c, &lay);
    let mut e = typed_lay::entries(&c, &lay, &w, &run.kc);
    let mut z = typed_lay::witness(&c, &lay, &w, &run.kc, &run.ec);
    typed_lay::fill_bits(&mut z, &lay, &spec, &run.kc);
    // dev (the dump's child is a bus-path proof, so the B program's typed gadget fails its asserts): drop the
    // entries of the failing slots, so the relation holds for these matrices (prover and replica both use them)
    if std::env::var_os("LVM_DEV_DROPFAIL").is_some() {
        let b0 = typed_lay::typed_of(typed_lay::Ents { ents: e.ents.clone(), tags: e.tags.clone(), ell: e.ell.clone(), slot_tag: e.slot_tag.clone() }, &lay);
        let abc = b0.abc(&z);
        let fail: std::collections::HashSet<u32> = (0..abc[0].len()).filter(|&x| !(abc[0][x] * abc[1][x] + abc[2][x]).is_zero()).map(|x| x as u32).collect();
        e.ents.retain(|(x, _)| !fail.contains(x));
        println!("tprove: LVM_DEV_DROPFAIL: {} failing slots' entries dropped", fail.len());
    }
    let mut b1 = typed_lay::typed_of(e, &lay);
    // the dev regions: the layout's, with stand-in targets
    let reg = |s: typed_lay::YSrc| lay.regs_of(s).map(|r| (r.base, r.log)).collect::<Vec<_>>();
    let com = reg(typed_lay::YSrc::Com);
    let ks = reg(typed_lay::YSrc::Ks);
    let sig = reg(typed_lay::YSrc::Sigma);
    let td = TData {
        com: com.iter().map(|&(b, l)| TReg { base: b, log: l, off: 6 << 20 }).collect(),
        ks: ks.iter().map(|&(b, l)| TReg { base: b, log: l, off: 4 << 20 }).collect(),
        sig: sig.iter().map(|&(b, l)| TReg { base: b, log: l, off: S_OFF + (17 << 14) }).collect(),
        sflat: reg(typed_lay::YSrc::Sflat)[0].0,
        pubb: reg(typed_lay::YSrc::Pub)[0].0,
        one: lay.one,
    };
    let mut cmain = vec![F64::ZERO; 1 << 23];
    for p in 0..S_STREAM.min(inp.in_k.len()) {
        cmain[S_OFF + typed_prove::sflat_word(p)] = inp.in_k[p];
    }
    for g in &td.sig {
        for i in 0..1usize << g.log {
            cmain[g.off + i] = z[g.base + i];
        }
    }
    for g in &td.ks {
        for i in 0..1usize << g.log {
            cmain[g.off + i] = z[g.base + i];
        }
    }
    let hdr: Vec<u64> = (0..1usize << 10).map(|i| z[td.pubb + i].0).collect();
    let bad = typed_prove::fill_virtual(&mut z, None, &td, &cmain, S_OFF, &hdr);
    println!("tprove: virtual regions filled, {bad} input words differ from their sources");
    typed_prove::place_com(&z, &td, &mut cmain);
    check_rel(&b1, &z, &c);
    b1.phik = Some(PhiK::new(&b1));
    let acc_in = crate::lvm::acc::Acc { pt: rand_pt(9), y: F192::ZERO };
    let acc_in = crate::lvm::acc::Acc { y: phi_multi(&b1, std::slice::from_ref(&acc_in.pt))[0], ..acc_in };
    let mut ps = crate::lv::fiat_shamir::transcript::ProverState::seeded(&vec![b'S'; 5000]);
    ps.add_cap(&[[1u8; 32], [2u8; 32]]);
    let t = Instant::now();
    let general = std::env::var_os("LVM_B1_Q1").is_some() || !run.ok;
    let out = typed_prove::prove(&mut ps, &b1, &z, &td, &cmain[S_OFF..S_OFF + (1 << 19)], S_OFF, &acc_in, general, None);
    println!("tprove: typed core proved in {:.3} s {:?} (general zerocheck {general})", t.elapsed().as_secs_f64(), out.stages);
    let replay = typed_prove::acc_out_of(&acc_in, &ps.trace);
    println!("tprove: accOutOf replays the fold: {}", replay == out.acc_out);
    // the mini-bus (dev placements: the count and finalize columns after z's committed words)
    if let Ok(mbt) = std::fs::read_to_string(format!("{dir}/mb.txt")) {
        let mb = dev_mb(&mbt, &c, &w, &td);
        let tabs = crate::lvm::typed_mb::tables(&mb, &c, &run.kc);
        println!("tprove: mini-bus {} tables, M3 numbers {:?}", tabs.len(), crate::lvm::m3::shape(&tabs));
        let mo = crate::lvm::m3::prove(&mut ps, &tabs);
        println!("tprove: mini-bus proved ({} table claims)", mo.claims.len());
    }
    let _ = ps.sample();
    let ok = verify_core(&ps.trace, 2, &b1, &td, &hdr, &acc_in, &cmain, S_OFF);
    println!("tprove: V replica {}", if ok { "ACCEPTS" } else { "REJECTS" });
}

/// Dev: `ietool`'s `mb.txt` (`S base stride tau valRec valOff`, `R blk row tau adrCell resCell`) with placements: the
/// read tables' address and value columns at their cells' committed words (through `td.com`), the count and
/// finalize columns after the committed region's used words, largest first, aligned.
pub fn dev_mb(text: &str, c: &crate::lvm::loopir::Compiled, w: &Words, td: &crate::lvm::typed_prove::TData) -> crate::lvm::typed_mb::MbSpec {
    use crate::lvm::typed_mb::{MbRead, MbSeed, MbSpec};
    let com_off = |y: usize| -> usize {
        let g = td.com.iter().find(|g| g.base <= y && y < g.base + (1 << g.log)).expect("a read column's words are committed");
        g.off + (y - g.base)
    };
    let used = (0..c.cells[0]).map(|n| w.k[n]).filter(|&y| y != u32::MAX && (y as usize) < (1 << 20)).max().unwrap_or(0) as usize + 1;
    let used_e = w.e.iter().flat_map(|l| l.iter().copied()).filter(|&y| (y as usize) < (1 << 20)).max().unwrap_or(0) as usize + 1;
    let mut next = com_off(0) + used.max(used_e);
    let mut m = MbSpec::default();
    let mut place = |tau: usize| {
        next = next.div_ceil(1 << tau) << tau;
        let o = next;
        next += 1 << tau;
        (false, o)
    };
    let mut reads = Vec::new();
    for l in text.lines() {
        let t: Vec<usize> = l.split_whitespace().skip(1).map(|x| x.parse().unwrap()).collect();
        match l.as_bytes().first() {
            Some(b'S') => m.seeds.push(MbSeed { base: t[0], stride: t[1], tau: t[2], val: (t[3] == 1, t[4]), fin: (false, 0) }),
            Some(b'R') => reads.push(t),
            _ => {}
        }
    }
    // largest first: the reads' count columns (2^tau ≥ 2^4), then the seeds' finalize columns
    for t in &reads {
        let (blk, row, tau, a0, r0) = (t[0], t[1], t[2], t[3], t[4]);
        let cnt = place(tau);
        m.reads.push(MbRead { blk, row, tau, wa: (false, com_off(w.k[a0] as usize)), wv: (false, com_off(w.k[r0] as usize)), cnt });
    }
    for s in &mut m.seeds {
        s.fin = place(s.tau);
    }
    m
}

const S_STREAM: usize = 17 << 14;
/// R11 (S2GM): the dev tool's stream block, P20's `S`.
const S_OFF: usize = crate::lvm::layout::P20.s_off;
