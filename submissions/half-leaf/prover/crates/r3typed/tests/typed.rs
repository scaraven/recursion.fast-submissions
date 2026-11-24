//! r3typed's own tests (the verifier round trip moved to `tools/refv/tests/typed.rs`, R1, 2026-11-23): the stub's
//! witness in leaf and node mode, and `accOut` recomputed from a proof's bytes and trace.
//! `cargo test -p r3typed --release -- --test-threads=1`; with `R3TY_FULL6=OUT` (an `lvm6-prover full6 OUT 1 all
//! node` directory) `acc_out_full6` also checks the real files.

use fiat_shamir::ProverState;
use fs6::oracle::{Local, Oracle};
use fs6::params::SHAPE as P18;
use primitives::field::{F64, F128};
use primitives::transcript::Pool;
use r3core::layout;
use r3typed::circuit::{PHI_VARS, REC_BASE};
use r3typed::prove::{Acc, acc_out_from_proof, acc_out_from_typed, prove_typed};
use r3typed::witness::{pub_lanes, witness};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn header(b: u64, acc: &Acc) -> Vec<u8> {
    let cp = if b == 0 { [0; 32] } else { [0x77; 32] };
    fs6::schedule::header(&P18, b, 1 << P18.log_blocks, &[3; 32], &cp, &[9; 32], Some(&acc.to_hdr()))
}

/// Node mode: any `STREAM` (slot 33), any `accIn`, any `Y`: the stub's rows all solve.
#[test]
fn witness_any_stream() {
    let circ = r3typed::circuit();
    let leaf = Acc::leaf(circ);
    assert!(!leaf.y.is_zero(), "Φ_Q(0^43) ≠ 0");
    let mut g = Rng(3);
    for b in [0u64, 1] {
        let mut stack = vec![F64::ZERO; 1 << layout::STACK_LOG];
        if b == 1 {
            for w in &mut stack[REC_BASE..REC_BASE + (1 << r3typed::circuit::REC_VARS)] {
                *w = F64(g.next());
            }
        }
        for w in &mut stack[layout::y_idx(0, 0)..layout::y_idx(0, 25)] {
            *w = F64(g.next());
        }
        let acc = if b == 0 {
            leaf.clone()
        } else {
            Acc { pt: (0..PHI_VARS).map(|_| F128::new(g.next(), g.next())).collect(), y: F128::new(g.next(), 5) }
        };
        let w = witness(circ, &mut stack, &pub_lanes(&header(b, &acc))).unwrap_or_else(|e| panic!("b = {b}: {e:?}"));
        assert!(w.z.iter().filter(|x| **x != F64::ZERO).count() > 1000);
    }
}

/// `accOut` from §6.4a's bytes and answers = the prover's.
#[test]
fn acc_out_from_bytes() {
    let circ = r3typed::circuit();
    let mut g = Rng(8);
    let mut stack = vec![F64::ZERO; 1 << layout::STACK_LOG];
    for w in &mut stack[REC_BASE..REC_BASE + (1 << r3typed::circuit::REC_VARS)] {
        *w = F64(g.next());
    }
    let pt: Vec<F128> = (0..PHI_VARS).map(|_| F128::new(g.next(), g.next())).collect();
    let acc = Acc { y: circ.phi_q(&pt), pt };
    let hdr = header(1, &acc);
    let w = witness(circ, &mut stack, &pub_lanes(&hdr)).unwrap();
    let o: &'static dyn Oracle = Box::leak(Box::new(Local::keyed(&[0x5a; 32])));
    let mut ps = ProverState::<F128, Pool>::v6(fs6::Transcript::start(o, &hdr));
    ps.add_scalars(&[F128::new(1, 2), F128::new(3, 4), F128::new(5, 6), F128::new(7, 8)]);
    let out = prove_typed(&mut ps, &w, &stack, &acc);
    let (body, trace) = ps.into_v6();
    let answers: Vec<fs6::Digest> = trace[2..].iter().map(|(_, a)| *a).collect();
    let got = acc_out_from_typed(&acc, &body[64..], &answers);
    assert_eq!(got, out.acc_out);
    assert_eq!(circ.phi_q(&got.pt), got.y, "Φ_Q(accOut.pt) = accOut.y");
}

fn signed(path: &std::path::Path) -> (Vec<u8>, fs6::Trace) {
    let b = std::fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let u = |o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap()) as usize;
    let pl = u(0);
    let pi = b[8..8 + pl].to_vec();
    let m = u(8 + pl);
    let mut o = 16 + pl;
    let mut tr = Vec::with_capacity(m);
    for _ in 0..m {
        let ql = u(o);
        tr.push((b[o + 8..o + 8 + ql].to_vec(), b[o + 8 + ql..o + 40 + ql].try_into().unwrap()));
        o += 40 + ql;
    }
    (pi, tr)
}

/// On `full6 … node` output: the leaf proof's `accOut` (from its file alone) is the node's `HDR.accIn`, and each
/// proof's `accOut` lies on `Φ_Q`.
#[test]
fn acc_out_full6() {
    let Some(dir) = std::env::var_os("R3TY_FULL6") else {
        eprintln!("acc_out_full6: R3TY_FULL6 unset, skipped");
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    let (lpi, ltr) = signed(&dir.join("leaf/full6.signed"));
    let (npi, ntr) = signed(&dir.join("node/full6.signed"));
    let la = acc_out_from_proof(&lpi, &ltr);
    let nin = Acc::from_hdr(&(0..=PHI_VARS).map(|k| fs6::codec::get_e(&npi[120 + 16 * k..])).collect::<Vec<_>>());
    assert_eq!(la, nin, "the node's accIn is the leaf's accOut");
    let circ = r3typed::circuit();
    assert_eq!(circ.phi_q(&la.pt), la.y);
    let na = acc_out_from_proof(&npi, &ntr);
    assert_eq!(circ.phi_q(&na.pt), na.y);
    eprintln!("acc_out_full6: leaf accOut = node accIn; both on Φ_Q");
}

/// The blob with a `MINIBUS` section and a `CHECKSUM` line (EXPORT.md) parses to the same circuit.
#[test]
fn blob_export_sections() {
    use r3typed::circuit::{Circuit, checksum_line, parse_minibus};
    let c = r3typed::stub::generate(r3typed::stub::SEED);
    let text = c.to_blob().replace("\nEND\n", "\nMINIBUS 1 1\n1 0 1 4 18890752 18890768\n2 4 18890784 18890800 18890816 18890832\nEND\n");
    let text = format!("# phi0 {} {}\n{text}", c.phi_q(&[F128::ZERO; 43]).c0, c.phi_q(&[F128::ZERO; 43]).c1);
    let full = format!("{text}{}", checksum_line(&text));
    assert_eq!(Circuit::from_blob(&full), c);
    let m = parse_minibus(&full).unwrap();
    assert_eq!(m.seeds, vec![(1, 0, 1, 4, vec![18890752], 18890768)]);
    assert_eq!(m.reads, vec![(2, 4, 18890784, vec![18890800, 18890816], 18890832)]);
    assert!(parse_minibus(&c.to_blob()).is_none());
    let bad = full.replacen("ENTS", "ENTS ", 1);
    assert!(std::panic::catch_unwind(|| Circuit::from_blob(&bad)).is_err(), "a wrong CHECKSUM is rejected");
}

/// The twin-row solve: `c_a·y_a + c_b·y_b = v` over `K`, CD's `(1, y)` and a general pair.
#[test]
fn solve_twin_rows() {
    use r3typed::witness::solve_k;
    let mut g = Rng(21);
    for c in [[F128::ONE, F128::new(0, 1)], [F128::new(g.next(), g.next()), F128::new(g.next(), g.next())]] {
        let (ya, yb) = (F64(g.next()), F64(g.next()));
        let v = c[0].mul_base(ya) + c[1].mul_base(yb);
        assert_eq!(solve_k(&c, v), Some(vec![ya, yb]));
    }
    assert_eq!(solve_k(&[F128::ONE, F128::new(5, 0)], F128::new(1, 1)), None, "K-dependent coefficients");
    assert_eq!(solve_k(&[F128::new(3, 0)], F128::new(1, 1)), None, "one word, not in K");
}

/// CD's exported typed blob (`R3TY_CD_BLOB`, default `/home/devops/scratch-lvm6/CD/q6-ty.blob`; skipped if absent):
/// it loads, its dimensions are FORMAT6's, and its leaf-mode witness solves (twin rows) with the relation holding.
#[test]
fn cd_blob_leaf_witness() {
    use r3typed::circuit::{Circuit, Src};
    let path = std::env::var("R3TY_CD_BLOB").unwrap_or_else(|_| "/home/devops/scratch-lvm6/CD/q6-ty.blob".into());
    let Ok(text) = std::fs::read_to_string(&path) else {
        eprintln!("cd_blob_leaf_witness: {path} absent, skipped");
        return;
    };
    let c = Circuit::from_blob(&text);
    let srcs: Vec<Src> = c.regs.iter().map(|r| r.src).collect();
    let rows = c.ents.iter().map(|e| e.x).max().unwrap() + 1;
    eprintln!("CD blob: {} entries (merged), {} OUT words, {rows} rows, regions {srcs:?}", c.ents.len(), c.outs.len());
    let acc = Acc::leaf(&c);
    let mut stack = vec![F64::ZERO; 1 << layout::STACK_LOG];
    let w = witness(&c, &mut stack, &pub_lanes(&header(0, &acc))).expect("CD's Q in leaf mode");
    let nz = c.outs.iter().filter(|&&(_, y)| w.z[y as usize] != F64::ZERO).count();
    eprintln!("CD blob: Φ_Q(0^43) = {:?}; {nz} of {} OUT words nonzero", acc.y, c.outs.len());
    let hdr = header(0, &acc);
    let o: &'static dyn Oracle = Box::leak(Box::new(Local::keyed(&[0x5a; 32])));
    let mut ps = ProverState::<F128, Pool>::v6(fs6::Transcript::start(o, &hdr));
    ps.add_scalars(&[F128::new(1, 2), F128::new(3, 4), F128::new(5, 6), F128::new(7, 8)]);
    let t0 = std::time::Instant::now();
    let out = prove_typed(&mut ps, &w, &stack, &acc);
    eprintln!("CD blob: §6.4a {:.3} s on {} threads: {:?}", t0.elapsed().as_secs_f64(), parallel::num_threads(), out.times);
    assert_eq!(c.phi_q(&out.acc_out.pt), out.acc_out.y);
}

/// The solve order is the dependencies', not the blob's: the stub with its `OUT` list reversed has the same witness.
#[test]
fn solve_order_independent_of_out_order() {
    let c = r3typed::stub::generate(r3typed::stub::SEED);
    let mut r = c.clone();
    r.outs.reverse();
    let acc = Acc::leaf(&c);
    let hdr = header(0, &acc);
    let mut s1 = vec![F64::ZERO; 1 << layout::STACK_LOG];
    let mut s2 = s1.clone();
    let z1 = witness(&c, &mut s1, &pub_lanes(&hdr)).unwrap().z;
    let z2 = witness(&r, &mut s2, &pub_lanes(&hdr)).unwrap().z;
    assert!(z1 == z2 && s1 == s2);
}

/// `POWBITS` in a sidecar and in the blob; the witness writes bit `i` of `STREAM` word `w` at word `bw + i`.
#[test]
fn powbits_words() {
    use r3typed::circuit::{Circuit, PowBits, parse_powbits};
    use r3typed::witness::witness_with;
    let side = "POWBITS 2\n5 1048576 3\n7 1048580 2\nEND\n";
    let pow = parse_powbits(side).unwrap();
    assert_eq!(pow, vec![PowBits { w: 5, bw: 1048576, nb: 3 }, PowBits { w: 7, bw: 1048580, nb: 2 }]);
    let c = r3typed::stub::generate(r3typed::stub::SEED);
    let blob = c.to_blob().replace("\nEND\n", &format!("\n{}", side));
    assert_eq!(Circuit::from_blob(&blob), c);
    assert_eq!(parse_powbits(&blob).unwrap(), pow);
    // the stub's com words 1048576 … (com_word(0) is defined by OUT: use words no row defines)
    let pow = vec![PowBits { w: 5, bw: r3typed::stub::COM_W + 1, nb: 3 }];
    let mut stack = vec![F64::ZERO; 1 << layout::STACK_LOG];
    stack[REC_BASE + 5] = F64(0b101);
    let acc = Acc::leaf(&c);
    let w = witness_with(&c, &pow, &mut stack, &pub_lanes(&header(1, &acc))).unwrap();
    let b = r3typed::stub::COM_W + 1;
    assert_eq!((w.z[b], w.z[b + 1], w.z[b + 2]), (F64(1), F64(0), F64(1)));
}
