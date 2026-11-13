//! The stream driver (PROVER.md §3; BLUEPRINT §0, §11 A2): `first` = `S,0` on chain A, then `S,1` on chain B
//! whose left child is that proof (3 SIGNs: the empty trace once for `σ_leaf`, A, the output); `step` = one
//! `S,1` on the new chain with the previous signed proof as the left child, `σ_leaf` reused from its header
//! (1 SIGN). The trace of every proof is the verifier's query sequence, which the prover recorded while
//! proving (the same queries and answers `V_S` replays), signed by one `SIGN`; the file is FORMAT.md's.
//! The recursion witness of every `S,1` proof is its left child's (`RecWitness::from_child`, WP-15b);
//! `S,0` keeps the zero convention. Dev only: `LVM_SAVE_CHILD=FILE` writes step 1's intermediate `S,0` proof.

use std::time::Instant;

use crate::format::{self, Sig, Signed};
use crate::lv::primitives::field::F64;
use crate::keccak::{leaf_stmt, node_stmt};
use crate::lvm::acc::{self, Acc};
use crate::lvm::params::{self, HEADER_BASE, Params};
use crate::lvm::prove::{Header, RecWitness, prove};
use crate::oracle::Digest;
use crate::service::{Service, fatal};

/// The node programs (WP-16a, `qasm gen P20|P8`: program, M3B tables, PUBX): every `S` proof carries its tables.
pub const Q_P20: &str = include_str!("q-p20.blob");
pub const Q_P8: &str = include_str!("q-p8.blob");
/// B1-IE (roll 8): the typed backend's supplements to B1-IX's blob, from the same frozen instance (`ietool m3b`):
/// the B program's `M3B` section (its input arrays, `BITS`, PUBX, FREE) and its typed layout (`layDump`).
pub const QB_P20_M3B: &str = include_str!("qb-p20.m3b");
pub const QB_P20_LAY: &str = include_str!("qb-p20.lay");
pub const QB_P8_M3B: &str = include_str!("qb-p8.m3b");
pub const QB_P8_LAY: &str = include_str!("qb-p8.lay");

pub fn unhex(s: &str) -> Digest {
    let s = s.trim();
    if s.len() != 64 || !s.bytes().all(|c| c.is_ascii_hexdigit()) {
        fatal(&format!("not a 64-hex digest: {s:?}"));
    }
    std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

/// R9-TY (dev, `LVM_LOG`): the step's serial parts outside `prove` (read, parse, `accOutOf`, sign, file), for the
/// `step parts` line; no effect on any byte.
static PARTS: std::sync::Mutex<Vec<(&'static str, f64)>> = std::sync::Mutex::new(Vec::new());

/// Record the time since `*t` under `name` and restart `*t` (R9-TY's `step parts`).
pub fn part(name: &'static str, t: &mut Instant) {
    if parts_on() {
        PARTS.lock().unwrap().push((name, t.elapsed().as_secs_f64()));
        *t = Instant::now();
    }
}

/// Whether the step parts are recorded (`LVM_LOG`, read once).
fn parts_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("LVM_LOG").is_some())
}

/// R9-TY (dev): the request's `go` (the start of [`run`]), for `since_go`.
static GO: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();

/// Record the time since `go` under `name` (R9-TY's `step parts`; nothing before [`run`]).
pub fn since_go(name: &'static str) {
    if let Some(g) = GO.get().filter(|_| parts_on()) {
        PARTS.lock().unwrap().push((name, g.elapsed().as_secs_f64()));
    }
}

/// The recorded parts, `name ms` each.
pub fn parts_line() -> String {
    PARTS.lock().unwrap().iter().map(|(k, v)| format!("{k} {:.1}", v * 1e3)).collect::<Vec<_>>().join(", ")
}

fn read(dir: &str, name: &str) -> Vec<u8> {
    std::fs::read(format!("{dir}/{name}")).unwrap_or_else(|e| fatal(&format!("{dir}/{name}: {e}")))
}

/// The statement an `S` header proves (`Header.stmt` of the Lean driver).
pub fn stmt_of(hd: &Header) -> Digest {
    let leaf = leaf_stmt(&hd.h, hd.n);
    if hd.b == 0 { leaf } else { node_stmt(&hd.c_l, &leaf) }
}

/// The header fields of a proof at `p`.
pub fn header_of(p: &Params, pi: &[u8]) -> Header {
    let hb = params::header_bytes(p);
    if pi.len() < hb || pi[0] != b'S' {
        fatal("the proof is not an S proof with a header");
    }
    let d = |o: usize| -> Digest { pi[o..o + 32].try_into().unwrap() };
    let u = |o: usize| u64::from_le_bytes(pi[o..o + 8].try_into().unwrap());
    let sig = format::from_sig_bytes(&pi[152..HEADER_BASE]);
    let acc_in = Acc::parse(&pi[HEADER_BASE..hb], p.acc_d());
    Header { b: u(8), vk: d(16), c_l: d(48), s: d(80), n: u(112), h: d(120), sig_leaf: Some(sig), acc_in }
}

pub struct Ctx {
    pub p: Params,
    pub svc: &'static Service,
    pub vk: Digest,
    pub log: bool,
    /// The LoopIR program whose tables every proof carries (dev: `LVM_LOOP_BLOB`; its inputs are the
    /// stream lanes), with its blob's M3 section if any; `None`: WP-15a's null bus.
    pub q: Option<(crate::lvm::loopir::Compiled, Option<crate::lvm::loopir::M3Spec>)>,
    /// `Φ̃(0)` (A23: step 1's `S,0` carries `acc_in = (0, Φ̃(0))`), from the zero build.
    pub phi0: crate::lv::primitives::field::F192,
    /// B1-IE (roll 8): the typed backend (`LVM_TYPED=1`; the B program, its layout, matrices, regions, mini-bus).
    pub typed: Option<TypedQ>,
}

/// B1-IE (roll 8, B-DES §1): the typed backend's static data, built before `ready` (untimed): the B program and its
/// input arrays (`prog.blob`: LOOPIR1 + an `M3B` section with no groups), B1-K's layout (`layout.txt`, `layDump`),
/// the regions' targets (`tdata.txt`, B1-Q's `TData`), the mini-bus (`mb.txt`), the words of every cell, the
/// matrices `ents Q lay` with the class kernels.
pub struct TypedQ {
    pub c: crate::lvm::loopir::Compiled,
    pub spec: crate::lvm::loopir::M3Spec,
    pub lay: crate::lvm::typed_lay::TLay,
    pub words: crate::lvm::typed_lay::Words,
    pub b1: crate::lvm::typed::Typed,
    pub td: crate::lvm::typed_prove::TData,
    pub mb: crate::lvm::typed_mb::MbSpec,
    /// TB (H-taint): whether the run may start with `h = 0` ([`h_sites`] holds), found before `ready` (R9-TY: it was
    /// found at the first proof, after `go`, ≈ 8–13 ms on the critical path before the walk)
    pub h_free: bool,
    /// R9-TY: the words' sources (`typed_lay::WSrc`), before `ready`
    pub ws: crate::lvm::typed_lay::WSrc,
}

impl TypedQ {
    /// From the four texts (the constant cells' values: the inputs' at those cells, PUBX's).
    pub fn new(prog: &str, layout: &str, tdata: &str, mb: &str) -> TypedQ {
        use crate::lvm::typed_lay;
        let (q, spec) = crate::lvm::loopir::parse_blob(prog);
        let spec = spec.unwrap_or_else(|| fatal("the B program's blob has no M3B section"));
        let c = crate::lvm::loopir::Compiled::new(q);
        let lay = typed_lay::TLay::parse(layout);
        let words = typed_lay::Words::new(&c, &lay);
        // the constants' values: a zero build's inputs (PUBX, after the public lanes)
        let nl = (crate::lvm::params::HEADER_BASE + crate::lvm::params::E_BYTES * (crate::lvm::params::ACC_VARS + 1) - 8) / 8 + 4;
        let (run0, _) = run_q(&c, &spec, &|_, _, n| vec![F64::ZERO; n], &vec![0; nl], None);
        let e = typed_lay::entries(&c, &lay, &words, &run0.kc);
        let mut b1 = typed_lay::typed_of(e, &lay);
        b1.phik = Some(crate::lvm::typed_phi::PhiK::new(&b1));
        let h_free = h_sites(&c, &spec).is_some();
        let ws = typed_lay::WSrc::new(&c, &lay, &words, &spec);
        TypedQ { c, spec, lay, words, b1, td: crate::lvm::typed_prove::TData::parse(tdata), mb: crate::lvm::typed_mb::MbSpec::parse(mb), h_free, ws }
    }

    /// The dev data of `LVM_TYPED_DIR`: B1-IX's typed blob (`q.blob`) with B1-IE's `M3B` supplement (`m3b.txt`) and
    /// the layout dump (`layout.txt`); else (older dev dirs) `prog.blob`, `layout.txt`, `tdata.txt`, `mb.txt`.
    pub fn from_dir(dir: &str) -> TypedQ {
        let r = |f: &str| std::fs::read_to_string(format!("{dir}/{f}")).unwrap_or_else(|e| fatal(&format!("{dir}/{f}: {e}")));
        if std::path::Path::new(&format!("{dir}/q.blob")).exists() {
            return TypedQ::from_blob(&r("q.blob"), &r("m3b.txt"), &r("layout.txt"));
        }
        TypedQ::new(&r("prog.blob"), &r("layout.txt"), &r("tdata.txt"), &r("mb.txt"))
    }

    /// From B1-IX's typed blob (`typed_blob`: the program, `TYPED`, `MINIBUS`, `CONST`, `HDR`), the program's `M3B`
    /// supplement (its input arrays, `BITS`, PUBX, FREE) and the layout dump. The blob's constants must be the
    /// inputs' (PUBX's) and its `PUB` selectors `hdrSel`'s (asserted).
    pub fn from_blob(blob: &str, m3b: &str, layout: &str) -> TypedQ {
        use crate::lvm::typed_lay;
        let tbl = crate::lvm::typed_blob::parse(blob);
        let (q, spec) = crate::lvm::loopir::parse_blob(&format!("{} {}", tbl.program, m3b));
        let spec = spec.unwrap_or_else(|| fatal("the M3B supplement"));
        let c = crate::lvm::loopir::Compiled::new(q);
        let lay = typed_lay::TLay::parse(layout);
        let words = typed_lay::Words::new(&c, &lay);
        // the zero build: the public lanes (the header's 747 and the statement's 4) zero, PUBX after them
        let (run0, _) = run_q(&c, &spec, &|_, _, n| vec![F64::ZERO; n], &vec![0; tbl.hdr.len() + 4], None);
        for (lo, vs) in &tbl.cst {
            assert!(vs.iter().enumerate().all(|(i, &v)| run0.kc[lo + i].0 == v), "the blob's constants are the inputs' (QLT)");
            assert!(lay.cst.iter().any(|&(l, n)| l == *lo && n == vs.len()), "the blob's constants are the layout's");
        }
        let sel: Vec<usize> = (0..tbl.hdr.len()).map(|k| if k < 5 { k } else { k + 4 }).collect();
        assert_eq!(tbl.hdr, sel, "PUB's lanes are the header's (hdrSel)");
        let e = typed_lay::entries(&c, &lay, &words, &run0.kc);
        let mut b1 = typed_lay::typed_of(e, &lay);
        b1.phik = Some(crate::lvm::typed_phi::PhiK::new(&b1));
        let h_free = h_sites(&c, &spec).is_some();
        let ws = typed_lay::WSrc::new(&c, &lay, &words, &spec);
        TypedQ { c, spec, lay, words, b1, td: tbl.td, mb: tbl.mb, h_free, ws }
    }

    /// `Φ_Q(0)`: the `acc_in.y` of step 1's `S,0` (`acc_in = (0, Φ_Q(0))`).
    pub fn phi0(&self) -> crate::lv::primitives::field::F192 {
        let z = vec![crate::lv::primitives::field::F192::ZERO; crate::lvm::typed_prove::PHI_VARS];
        crate::lvm::typed::phi_multi(&self.b1, std::slice::from_ref(&z))[0]
    }
}

impl Ctx {
    /// Attach the program (dev: `LVM_LOOP_BLOB`) and fix the schedule numbers its tables make (they replace
    /// the record's when they differ: test programs; the real `Q`'s are the record's).
    pub fn with_loop(mut self) -> Self {
        // B1-IE: the typed backend (`LVM_TYPED=1`, dev data from `LVM_TYPED_DIR`)
        // B1-IE (roll 8): the typed backend is the shipped path (`LVM_TYPED=0`: the bus path, for a bus blob only);
        // its data: B1-IX's blob with B1-IE's supplements, or dev data from `LVM_TYPED_DIR`
        let embedded = match self.p.name {
            "P20" => Some((Q_P20, QB_P20_M3B, QB_P20_LAY)),
            "P8" => Some((Q_P8, QB_P8_M3B, QB_P8_LAY)),
            _ => None,
        };
        let dir = std::env::var("LVM_TYPED_DIR").ok();
        if std::env::var("LVM_TYPED").map_or(true, |v| v != "0") && (dir.is_some() || embedded.is_some()) {
            let t = match (&dir, embedded) {
                (Some(d), _) => TypedQ::from_dir(d),
                (None, Some((b, m, l))) => TypedQ::from_blob(b, m, l),
                _ => unreachable!(),
            };
            self.phi0 = t.phi0();
            if self.log {
                eprintln!("lvm: typed backend: {}; {}", t.b1.report, t.b1.phik.as_ref().map_or("", |k| k.report.as_str()));
                eprintln!("lvm: B program: inputs {:?}, cells {:?}", t.c.q.n_in, t.c.cells);
            }
            assert_eq!(self.p.acc_d(), crate::lvm::typed_prove::PHI_VARS, "the typed backend's acc_in has 43 coordinates (accVars)");
            self.typed = Some(t);
            return self;
        }
        // the shipped prover carries the node program of its parameter set (WP-16a: `qasm gen`'s blobs);
        // dev: `LVM_LOOP_BLOB` replaces it, `LVM_LOOP_BLOB=none` runs without one (WP-15a's null bus)
        let blob = match std::env::var("LVM_LOOP_BLOB") {
            Ok(path) if path == "none" => None,
            Ok(path) => Some(std::fs::read_to_string(&path).unwrap_or_else(|e| fatal(&format!("{path}: {e}")))),
            Err(_) => match self.p.name {
                "P20" => Some(Q_P20.to_string()),
                "P8" => Some(Q_P8.to_string()),
                _ => None,
            },
        };
        if let Some(text) = blob {
            let (q, spec) = crate::lvm::loopir::parse_blob(&text);
            // A23: the header array selects the header lanes from byte 8 (`Pub.hdrLanes` = `pub_lanes` without `c`),
            // every other public array the constant lanes after them (PUBX)
            if let Some(s) = &spec {
                let hl = crate::lvm::m3::pub_lanes_len(&self.p);
                let want: Vec<usize> = (0..5).chain(9..hl).collect();
                for a in s.arrs.iter().filter(|a| a.kind == crate::lvm::loopir::ArrKind::Public) {
                    if a.sel.iter().any(|&i| i < hl) && a.sel != want {
                        fatal("the blob's header array does not select the A23 header lanes (regenerate it: qasm gen)");
                    }
                }
            }
            self.q = Some((crate::lvm::loopir::Compiled::new(q), spec));
            let z = match &self.q {
                Some((_, Some(_))) => self.build_tables(&|_, _, n| vec![F64::ZERO; n], &vec![0; crate::lvm::m3::pub_lanes_len(&self.p)]),
                _ => self.attach(RecWitness::zero(&self.p)).tables,
            };
            // TB: the H-taint check's program walk, before `ready`
            if let Some((c, Some(spec))) = &self.q {
                let _ = h_sites(c, spec);
            }
            let z: Vec<_> = z.into_iter().filter(crate::lvm::m3::active).collect();
            let (d, l, r, e) = crate::lvm::m3::shape(&z);
            if (d, l, r, e) != (self.p.bus_depth, self.p.leafdec_reads, self.p.table_rounds, self.p.table_evals) {
                if std::env::var_os("LVM_M3_OVERRIDE").is_none() {
                    fatal(&format!("the program's M3 numbers ({d}, {l}, {r}, {e}) are not {}'s (dev: LVM_M3_OVERRIDE=1)", self.p.name));
                }
                eprintln!(
                    "lvm: the program's M3 numbers ({d}, {l}, {r}, {e}) replace {}'s ({}, {}, {}, {})",
                    self.p.name, self.p.bus_depth, self.p.leafdec_reads, self.p.table_rounds, self.p.table_evals
                );
            }
            // A23: PUB is the record's sumcheck table, Φ's columns fit 2^dk (header-independent: the zero build's)
            if !z.is_empty() && acc::hdr_tab(&z) != Some(self.p.pub_tab) {
                match (acc::hdr_tab(&z), std::env::var_os("LVM_M3_OVERRIDE")) {
                    (Some(t), Some(_)) => {
                        eprintln!("lvm: the program's pubTab {t} replaces {}'s {}", self.p.name, self.p.pub_tab);
                        self.p = Params { pub_tab: t, ..self.p.clone() };
                    }
                    _ => fatal(&format!("the header array is sumcheck table {:?}, not {}'s pubTab {}", acc::hdr_tab(&z), self.p.name, self.p.pub_tab)),
                }
            }
            self.p = Params { bus_depth: d, leafdec_reads: l, table_rounds: r, table_evals: e, ..self.p.clone() };
            let cols = acc::fix_cols(&z, self.p.pub_tab);
            if cols.len() > 1 << self.p.acc_log() {
                fatal(&format!("Φ has {} columns > 2^{} (accVars − tableRounds)", cols.len(), self.p.acc_log()));
            }
            // Φ̃(0) = Φ(0) = F_0(0)
            self.phi0 = cols.first().map_or(crate::lv::primitives::field::F192::ZERO, |c| c[0].into());
            if self.log {
                eprintln!("lvm: Φ: {} fixed columns, {} cells, D = {}, dk = {}", cols.len(), cols.iter().map(|c| c.len()).sum::<usize>(), self.p.acc_d(), self.p.acc_log());
            }
        }
        self
    }

    /// The tables of a program without an M3 section (WP-15b's stream programs: inputs = the stream lanes).
    fn attach(&self, mut rec: RecWitness) -> RecWitness {
        if let Some((c, None)) = &self.q {
            // KS14: the program's inputs are C_rec's stream columns (the KS rows `< ks_split`, zero above)
            rec.tables = crate::lvm::m3::stream_program_tables(c, self.p.rec_rows_log, &rec.stream_rows(&self.p));
        }
        rec
    }

    /// The tables of the program's M3 section: the input cells from the arrays (aliased: `col(rec, off, len)`
    /// of the commitments; public: `pub_lanes`), the BITS outputs by a fixpoint (run, set every output cell
    /// to its word function, until nothing changes: the program defines each word before it reads the
    /// word's outputs, so this ends after the BITS dependency depth + 1 runs), then WP-9's tables.
    pub fn build_tables(&self, col: &dyn Fn(bool, usize, usize) -> Vec<F64>, pub_lanes: &[u64]) -> Vec<crate::lvm::m3::TableW> {
        build_q_tables(&self.q, col, pub_lanes)
    }

    /// The builder `prove` calls (M3 section present): aliased columns from the commitments, public lanes from
    /// the header and its statement. TB (OH-DES P1, "H-taint"): it starts before `h` is known (`get_h` waits
    /// for it). When the tables depend on `h` only through public-array cells no instance reads ([`h_sites`]),
    /// they are built with `h = 0` and those cells' values are set once `h` comes; else the build waits.
    fn builder(&self) -> Option<impl Fn(&Header, &crate::lvm::prove::Col, &crate::lvm::prove::GetH) -> Vec<crate::lvm::m3::TableW> + Sync + '_> {
        let lanes = |hd: &Header| crate::lvm::m3::pub_lanes(&hd.bytes(), &stmt_of(hd));
        matches!(&self.q, Some((_, Some(_)))).then_some(move |hd: &Header, col: &crate::lvm::prove::Col, get_h: &crate::lvm::prove::GetH| {
            let Some((c, Some(spec))) = &self.q else { unreachable!() };
            let mut hd = hd.clone();
            hd.h = [0; 32];
            let l0 = lanes(&hd);
            hd.h = [0xff; 32];
            let l1 = lanes(&hd);
            // dev: `LVM_HTAINT=0` waits for `h` as before
            let on = std::env::var("LVM_HTAINT").map_or(true, |v| v != "0");
            let sites = h_sites(c, spec).filter(|_| on && (0..l0.len()).all(|i| l0[i] == l1[i] || H_LANES.contains(&i)));
            match sites {
                Some(sites) => {
                    let mut t = self.build_tables(col, &l0);
                    hd.h = get_h();
                    let l = lanes(&hd);
                    for (ti, x, i) in sites {
                        t[ti].cols[0][x] = F64(l[i]);
                    }
                    t
                }
                None => {
                    hd.h = get_h();
                    self.build_tables(col, &lanes(&hd))
                }
            }
        })
    }

    fn sign(&self, pi: Vec<u8>, tr: crate::oracle::Trace) -> Signed {
        let t = Instant::now();
        // P6B (OH-DES P4): the trace digest of the check while the service signs
        let (sig, m) = crate::proc::sign_checked(self.svc, &tr, || format::trace_digest(&tr));
        if !format::sig_ok(&self.vk, &m, &sig) {
            fatal("SIGN: SigOk fails on the returned signature");
        }
        if self.log {
            eprintln!("lvm: SIGN {} queries in {:.3} s (idx {})", tr.len(), t.elapsed().as_secs_f64(), sig.idx);
        }
        Signed { pi, tr, sig }
    }

    /// One `S` proof, signed; checks its own statement against `want`.
    /// `last`: the request's last proof (R9-TY: its dead buffers go back to the kernel while the service signs).
    fn s_proof(&self, hd: Header, rec: RecWitness, want: Option<&Digest>, last: bool) -> (Signed, Digest, Acc) {
        let t = Instant::now();
        let mut tp = Instant::now();
        let sp = match &self.typed {
            Some(tq) => prove_typed(tq, &self.p, hd.clone(), rec),
            None => {
                let b = self.builder();
                prove(&self.p, hd.clone(), rec, b.as_ref().map(|f| f as &crate::lvm::prove::Build))
            }
        };
        let sp_stages = sp.stages.clone();
        let mut hd = hd;
        hd.h = sp.h;
        let c = stmt_of(&hd);
        if let Some(w) = want {
            assert_eq!(&c, w, "the proof's statement");
        }
        if self.log {
            let st: Vec<String> = sp_stages.iter().map(|(k, v)| format!("{k} {v:.2}")).collect();
            eprintln!("lvm: S,{} n={} proved in {:.3} s [{}]", hd.b, hd.n, t.elapsed().as_secs_f64(), st.join(", "));
        }
        part("prove", &mut tp);
        let acc_out = sp.acc_out.clone();
        // R9-TY (TSU): the request's large buffers are dead once its last proof is made, so the cache's free blocks
        // are handed back to the kernel now, on detached threads beside the service's SIGN (the runner's clock runs
        // until the process is dead, PROVER.md §3; freed here, the kill has less to free). `LVM_REL_EARLY=0`: at `done`.
        if last && std::env::var("LVM_REL_EARLY").map_or(true, |v| v != "0") {
            crate::lvm::prove::drop_prepared();
            crate::proc::tsu_release();
        }
        let signed = self.sign(sp.proof, sp.trace);
        part("sign", &mut tp);
        // the replay a later step does on this file gives the prover's own accumulator
        assert_eq!(self.acc_of_child(&signed), acc_out, "accOutOf replays the proof's fold");
        part("acc check", &mut tp);
        (signed, c, acc_out)
    }

    /// `acc_in` of an `S,1` proof over `child`: `accOutOf` of the child's stream (A23).
    fn acc_of_child(&self, child: &Signed) -> Acc {
        if self.typed.is_some() {
            return crate::lvm::typed_prove::acc_out_of(&header_of(&self.p, &child.pi).acc_in, &child.tr);
        }
        acc::acc_out_of(&self.p, &child.pi, &child.tr)
    }

    /// `σ_leaf`: the signature of the empty trace (`traceDigest []` is a constant, A2).
    pub fn sig_leaf(&self) -> Sig {
        self.sign(Vec::new(), Vec::new()).sig
    }

    /// Step 1: `nodeStmt (leafStmt hA nA) (leafStmt hB nB)`.
    pub fn first(&self, (na, sa): (u64, Digest), (nb, sb): (u64, Digest)) -> Signed {
        let sig_leaf = self.sig_leaf();
        let ha = Header { b: 0, vk: self.vk, c_l: [0; 32], s: sa, n: na, h: [0; 32], sig_leaf: None, acc_in: Acc::zero(self.p.acc_d(), self.phi0) };
        let (a, ca, _) = self.s_proof(ha, self.attach(RecWitness::zero(&self.p)), None, false);
        if let Ok(path) = std::env::var("LVM_SAVE_CHILD") {
            std::fs::write(&path, format::to_file(&a)).expect("LVM_SAVE_CHILD");
        }
        let hb = Header { b: 1, vk: self.vk, c_l: ca, s: sb, n: nb, h: [0; 32], sig_leaf: Some(sig_leaf), acc_in: self.acc_of_child(&a) };
        let rec = self.attach(RecWitness::from_child(&self.p, &a));
        self.s_proof(hb, rec, None, true).0
    }

    /// Step i ≥ 2: `nodeStmt prev (leafStmt h n)`.
    pub fn step(&self, prev_stmt: &Digest, prev: &Signed, (n, s): (u64, Digest)) -> Signed {
        let mut tp = Instant::now();
        let ph = header_of(&self.p, &prev.pi);
        if &stmt_of(&ph) != prev_stmt {
            fatal("prev.bin does not prove prev.stmt");
        }
        let sig_leaf = if ph.b == 1 { ph.sig_leaf.clone().unwrap() } else { self.sig_leaf() };
        part("header", &mut tp);
        let hd = Header { b: 1, vk: self.vk, c_l: *prev_stmt, s, n, h: [0; 32], sig_leaf: Some(sig_leaf), acc_in: self.acc_of_child(prev) };
        part("acc in", &mut tp);
        let rec = self.attach(RecWitness::from_child(&self.p, prev));
        part("from child", &mut tp);
        self.s_proof(hd, rec, None, true).0
    }
}

/// B1-IE: one typed `S` proof (`prove_with` with the B program's run: the inputs from the arrays, the KS alias cells
/// from the typed regions, the H-taint early start), for the stream and the CPU self-test.
pub fn prove_typed(tq: &TypedQ, p: &Params, hd: Header, rec: RecWitness) -> crate::lvm::prove::SProof {

                let lanes = |hd: &Header| crate::lvm::m3::pub_lanes(&hd.bytes(), &stmt_of(hd));
                // TB (H-taint) on the typed path: when no instance reads the cells that depend on `h` ([`h_sites`]),
                // the run starts beside the walk with `h = 0`; those cells' words are `PUB`'s, which the prover fills
                // from the real header afterwards (`typed_prove::fill_virtual`). Else (or `LVM_HTAINT=0`) it waits.
                let mut tp = Instant::now();
                let early = std::env::var("LVM_HTAINT").map_or(true, |v| v != "0") && tq.h_free;
                part("h_sites", &mut tp);
                // the KS alias cells (xs, ys, md) from the typed regions: `C_main`'s words at the regions' targets, through
                // the layout's (lane-split) input regions; V binds them so (`TYPED`'s ks regions). The M3B arrays' own KS
                // placements are not used (at P8, `LvmQAsmTabs.xCol`/`ksY` key on `rl = 14` and give P20's offsets);
                // `LVM_TYPED_KSVIEW=0` keeps them (diagnosis)
                let ksview = std::env::var("LVM_TYPED_KSVIEW").map_or(true, |v| v != "0");
                let run = move |hd: &Header, col: &crate::lvm::prove::Col, get_h: &crate::lvm::prove::GetH| {
                    let mut hd = hd.clone();
                    hd.h = if early { [0; 32] } else { get_h() };
                    let fix = |in_k: &mut [F64]| {
                        for g in &tq.td.ks {
                            let vals = col(false, g.off, 1 << g.log);
                            let (lo_w, hi_w) = (g.base, g.base + (1usize << g.log));
                            for d in tq.lay.inp.iter().filter(|d| d.ty == crate::lvm::loopir::Ty::K) {
                                match &d.lanes {
                                    None => {
                                        let (a, b) = (lo_w.max(d.bases[0]), hi_w.min(d.bases[0] + d.n));
                                        for y in a..b {
                                            in_k[d.lo + (y - d.bases[0])] = vals[y - lo_w];
                                        }
                                    }
                                    Some((r, lb)) => {
                                        let rows = d.n / r;
                                        for (l, &b0) in lb.iter().enumerate() {
                                            let (a, b) = (lo_w.max(b0), hi_w.min(b0 + rows));
                                            for y in a..b {
                                                in_k[d.lo + r * (y - b0) + l] = vals[y - lo_w];
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    };
                    run_q(&tq.c, &tq.spec, col, &lanes(&hd), if ksview { Some(&fix) } else { None }).0
                };
                let tb = crate::lvm::prove::TypedB { c: &tq.c, spec: &tq.spec, lay: &tq.lay, words: &tq.words, b1: &tq.b1, td: &tq.td, mb: &tq.mb, ws: Some(&tq.ws), run: &run };
                crate::lvm::prove::prove_with(p, hd, rec, Some(crate::lvm::prove::Job::Typed(&tb)))
}

/// TB (H-taint): the public lanes that depend on `h`: the statement `c` (lanes 5..9 of [`crate::lvm::m3::pub_lanes`])
/// and `h` (header bytes 120..152, lanes 18..22). The builder checks on every call that no other lane moves with `h`.
const H_LANES: [usize; 8] = [5, 6, 7, 8, 18, 19, 20, 21];

/// TB (H-taint): the cells `(table, row, lane)` of the public arrays that select an [`H_LANES`] lane (the tables
/// in [`build_q_tables`]'s order: groups, arrays, BITS), if nothing else in the build depends on those cells: no
/// instance reads them ([`crate::lvm::loopir::Compiled::unread`]), no BITS word or free word is one, no written
/// array holds one. Then the tables built with any `h` differ only in those cells' values (column 0). A cell
/// that two public arrays share is patched in both: a public array's values come from its selectors, not from
/// the cell.
fn h_sites(c: &crate::lvm::loopir::Compiled, spec: &crate::lvm::loopir::M3Spec) -> Option<Vec<(usize, usize, usize)>> {
    use crate::lvm::loopir::ArrKind;
    let (mut sites, mut cells) = (Vec::new(), Vec::new());
    for (ai, a) in spec.arrs.iter().enumerate().filter(|(_, a)| a.kind == ArrKind::Public) {
        for (x, &i) in a.sel.iter().enumerate().take(1 << a.tau).filter(|(_, i)| H_LANES.contains(i)) {
            sites.push((spec.groups.len() + ai, x, i));
            cells.push(a.base + a.stride * x);
        }
    }
    cells.sort_unstable();
    cells.dedup();
    let hit = |e: usize| cells.binary_search(&e).is_ok();
    let words = spec.bits.iter().any(|b| b.wc.iter().any(|&e| hit(e)));
    let free = spec.free.iter().any(|&(_, _, cell)| (cell..cell + 4).any(hit));
    let written = spec.arrs.iter().filter(|a| a.kind == ArrKind::Written).any(|a| (0..1usize << a.tau).any(|x| hit(a.base + a.stride * x)));
    (!words && !free && !written && c.unread(&cells)).then_some(sites)
}

/// [`Ctx::build_tables`] on a program alone (no service: the `tbench` dev command times it).
pub fn build_q_tables(
    q: &Option<(crate::lvm::loopir::Compiled, Option<crate::lvm::loopir::M3Spec>)>,
    col: &dyn Fn(bool, usize, usize) -> Vec<F64>,
    pub_lanes: &[u64],
) -> Vec<crate::lvm::m3::TableW> {
    let Some((c, Some(spec))) = q else { return Vec::new() };
    let (run, lanes) = run_q(c, spec, col, pub_lanes, None);
    crate::lv::tracing::info_span!("B spec_tables").in_scope(|| crate::lvm::m3::spec_tables(c, &run, spec, col, &lanes, lanes.len() - spec.pubx.len()))
}

/// The node program's run on the inputs its M3 section assembles ([`build_q_tables`]' first half; B1-IE: the typed
/// backend's build): the input cells from the arrays (aliased: `col(rec, off, len)` of the commitments; public:
/// `pub_lanes` then PUBX), the BITS outputs by the fixpoint. Returns the run and the public lanes (with PUBX).
pub fn run_q(
    c: &crate::lvm::loopir::Compiled,
    spec: &crate::lvm::loopir::M3Spec,
    col: &dyn Fn(bool, usize, usize) -> Vec<F64>,
    pub_lanes: &[u64],
    fix: Option<&dyn Fn(&mut [F64])>,
) -> (crate::lvm::loopir::Run, Vec<u64>) {
    use crate::lv::primitives::field::F192;
    use crate::lvm::loopir::{ArrKind, Ty};
    let mut tq = Instant::now();
    let hdr_pub = pub_lanes;
    let lanes: Vec<u64> = pub_lanes.iter().chain(&spec.pubx).copied().collect();
    let pub_lanes = &lanes[..];
    let mut in_k = vec![F64::ZERO; c.q.n_in[0]];
    let mut in_e = vec![F192::ZERO; c.q.n_in[1]];
    for a in &spec.arrs {
        let n = 1usize << a.tau;
        let cols: Vec<Vec<F64>> = match a.kind {
            ArrKind::Aliased => a.val.iter().map(|&(r, o)| col(r, o, n)).collect(),
            ArrKind::Public => vec![(0..n).map(|x| F64(a.sel.get(x).and_then(|&i| pub_lanes.get(i).copied()).unwrap_or(0))).collect()],
            ArrKind::Written => continue,
        };
        for x in 0..n {
            match a.ty {
                Ty::K => in_k[a.base + a.stride * x] = cols[0][x],
                Ty::E => in_e[a.base + a.stride * x] = F192::new(cols[0][x].0, cols[1][x].0, cols[2][x].0),
            }
        }
    }
    // B1-P (`LVM_TYPED_DUMP=DIR`, dev only, not on any shipped path): the assembled inputs and the header lanes of
    // every non-zero build, for `lvm-prover typed` (`crate::lvm::typed`)
    if let Some(dir) = std::env::var_os("LVM_TYPED_DUMP").filter(|_| hdr_pub.iter().any(|&x| x != 0)) {
        crate::lvm::typed::dump_inputs(std::path::Path::new(&dir), &in_k, &in_e, hdr_pub);
    }
    // B1-IE dev (`LVM_TYPED_KSVIEW=1`): the input cells as the typed regions name them (`fix`)
    if let Some(f) = fix {
        f(&mut in_k);
    }
    part("rq inputs", &mut tq);
    // every BITS output cell is a K input cell outside the aliased/public arrays, written once
    let mut owner = vec![0u8; c.q.n_in[0]];
    for a in spec.arrs.iter().filter(|a| a.ty == Ty::K && a.kind != ArrKind::Written) {
        for x in 0..1usize << a.tau {
            owner[a.base + a.stride * x] = 1;
        }
    }
    for b in &spec.bits {
        for o in &b.oc {
            for &e in o {
                assert!(e < c.q.n_in[0], "a BITS output is a K input cell ({e})");
                assert!(owner[e] != 1, "a BITS output cell lies in an aliased or public array ({e})");
                assert!(owner[e] != 2, "two BITS outputs write cell {e}");
                owner[e] = 2;
            }
        }
    }
    // TB: after the first run, only the BITS outputs' cone is re-run (the same run as a full one, `Cone`);
    // with `LVM_QDEBUG` (its listing of the failed checks) every run is a full one, as before
    let seeds: Vec<usize> = spec.bits.iter().flat_map(|b| b.oc.iter().flatten().copied()).collect();
    part("rq owner", &mut tq);
    let mut tp = Instant::now();
    let cone = c.cone(&seeds).filter(|_| std::env::var_os("LVM_QDEBUG").is_none());
    part("cone", &mut tp);
    tq = Instant::now();
    let mut prev: Option<crate::lvm::loopir::Run> = None;
    let mut runs = 0;
    let run = loop {
        let run = crate::lv::tracing::info_span!("B interp").in_scope(|| match (prev.take(), cone) {
            (Some(mut r), Some(cone)) => {
                c.rerun(cone, &mut r, &in_k);
                r
            }
            _ => c.interp(&in_k, &in_e),
        });
        part(if runs == 0 { "rq interp" } else { "rq rerun" }, &mut tq);
        runs += 1;
        let mut changed = false;
        for (bi, b) in spec.bits.iter().enumerate() {
            for x in 0..b.n {
                let w = match spec.free.iter().find(|f| f.0 == bi) {
                    // the WOTS checksum of the digest's 32 bytes (4 digits per byte, low bits first)
                    Some(&(_, 0, cell)) => crate::lvm::m3::free_checksum(&in_k[cell..cell + 4]),
                    Some(&(_, k, _)) => panic!("LoopIR blob: free word kind {k}"),
                    None => run.kc[b.wc[x]].0,
                };
                for (j, o) in b.outs.iter().enumerate() {
                    let e = b.oc[j][x];
                    let v = F64(o.word(w));
                    if in_k[e] != v {
                        in_k[e] = v;
                        changed = true;
                    }
                }
            }
        }
        part("rq bits", &mut tq);
        if !changed {
            part("run_q fix", &mut tp);
            break run;
        }
        assert!(runs < 64, "the BITS outputs settle");
        prev = Some(run);
    };
    if std::env::var_os("LVM_TB_REF").is_some() {
        let r = c.interp(&in_k, &in_e);
        assert!(r.kc == run.kc && r.ec == run.ec && r.ok == run.ok && r.inb == run.inb && r.fails == run.fails, "TB: the cone re-runs give the full run");
        eprintln!("lvm: LVM_TB_REF: {runs} runs, the last equals a full run");
    }
    if !run.ok || !run.inb {
        if std::env::var_os("LVM_QDEBUG").is_some() { eprintln!("lvm qdebug: ---- end of run"); }
        if let Some(path) = std::env::var_os("LVM_QDEBUG_DUMP") {
            let b: Vec<u8> = in_k.iter().flat_map(|v| v.0.to_le_bytes()).collect();
            let _ = std::fs::write(path, b);
        }
        eprintln!("lvm: the node program's run on these inputs: ok {} inb {} (dev: LVM_QDEBUG=1 lists the rows)", run.ok, run.inb);
    }
    (run, lanes)
}

/// `first`/`step` inputs from `/work`.
pub fn run(ctx: &Ctx, mode: &str, dir: &str) -> Vec<u8> {
    let chain = |name: &str| crate::proc::read_chain(&std::path::Path::new(dir).join(name));
    let _ = GO.set(Instant::now());
    let mut tp = Instant::now();
    let out = match mode {
        "first" => ctx.first(chain("chainA.json"), chain("chainB.json")),
        "step" => {
            // R9-TY: the new chain's walk starts first, beside the child's read and parse (`prove::start_walk`)
            let c = chain("chain.json");
            if ctx.typed.is_some() {
                crate::lvm::prove::start_walk(&ctx.p, c.1, c.0 as usize);
            }
            part("walk start", &mut tp);
            let prev_stmt = unhex(&String::from_utf8_lossy(&read(dir, "prev.stmt")));
            let raw = read(dir, "prev.bin");
            part("read", &mut tp);
            let prev = format::from_file(&raw).unwrap_or_else(|| fatal("prev.bin is not a signed file"));
            drop(raw);
            part("parse", &mut tp);
            ctx.step(&prev_stmt, &prev, c)
        }
        _ => unreachable!(),
    };
    let mut tp = Instant::now();
    let file = format::to_file(&out);
    part("to file", &mut tp);
    assert_eq!(format::from_file(&file).as_ref(), Some(&out), "the file parses back");
    part("parse back", &mut tp);
    file
}
