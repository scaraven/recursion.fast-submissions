//! B1-P dev commands (`lvm-prover typed …`; not on any proving path), from B1-P5's `b1p5`:
//! - `typed toy P8|P20|BLOB INPUTS [SEED]`: the relation on every slot, the class kernels against the sparse
//!   evaluator, the backend end to end with the toy verifier, and the tampers (a result word, an operand of each
//!   matrix, `h`);
//! - `typed time P20|BLOB INPUTS REPS`: today's table build against the results-only witness, and the backend's
//!   phases (`h` and `v_o` by the kernels; `TYPED_SPARSE=1` for the sparse evaluator).
//!
//! `INPUTS` is an `LVM_TYPED_DUMP` file. On the worker pool (`LEANVM_NUM_THREADS`).
use std::time::Instant;

use crate::lv::primitives::field::{F64, F192};
use crate::lvm::loopir::{Op, Ty};
use crate::lvm::typed::*;
use crate::lvm::typed_phi::PhiK;

pub fn cmd(args: &[String]) {
    let mode = args.get(2).cloned().unwrap_or_default();
    let which = args.get(3).cloned().unwrap_or_else(|| "P8".into());
    let text = match which.as_str() {
        "P20" => crate::lvm::stream::Q_P20.to_string(),
        "P8" => crate::lvm::stream::Q_P8.to_string(),
        path => std::fs::read_to_string(path).expect("blob"),
    };
    let inp = read_inputs(args.get(4).expect("INPUTS"));
    crate::lv::parallel::init();
    let t = Instant::now();
    let (prog, spec) = crate::lvm::loopir::parse_blob(&text);
    let q = Some((crate::lvm::loopir::Compiled::new(prog), spec));
    let (c, spec) = match &q {
        Some((c, Some(s))) => (c, s),
        _ => panic!("the blob has an M3 section"),
    };
    let run = run_fixpoint(c, spec, &inp);
    println!(
        "typed {which}: cells K {} E {}, inputs K {} E {}; run ok {} inb {} ({:.3} s)",
        c.cells[0],
        c.cells[1],
        c.q.n_in[0],
        c.q.n_in[1],
        run.ok,
        run.inb,
        t.elapsed().as_secs_f64()
    );
    let t = Instant::now();
    let mut b1 = Typed::new(c, spec, &run, inp.hdr.len());
    println!("{} (static build {:.3} s)", b1.report, t.elapsed().as_secs_f64());
    let t = Instant::now();
    let pk = PhiK::new(&b1);
    println!("{} ({:.3} s)", pk.report, t.elapsed().as_secs_f64());
    {
        // the kernels against the plain sparse evaluator at random points (exact equality), per matrix too
        let mut r = Rng::new(77);
        let d = 2 + b1.x_log + b1.y_log;
        let pts: Vec<Vec<F192>> = (0..3).map(|_| (0..d).map(|_| r.e()).collect()).collect();
        let t = Instant::now();
        let k = pk.eval(&pts);
        let tk = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let s = phi_multi(&b1, &pts);
        let ts = t.elapsed().as_secs_f64();
        assert_eq!(k, s, "the class kernels equal the sparse evaluator");
        let m = pk.mats(&pts[..1]);
        let mv = mat_vals(&b1, &pts[0][2..2 + b1.x_log], &pts[0][2 + b1.x_log..]);
        assert_eq!(&m[..], &mv[..], "the kernels' matrix values equal the CSC's");
        println!("phik: equals the sparse evaluator at 3 random points, and M̃_o at one ({tk:.3} s vs {ts:.3} s, untimed)");
    }
    if std::env::var_os("TYPED_SPARSE").is_none() {
        b1.phik = Some(pk);
    }
    let d = 2 + b1.x_log + b1.y_log;
    let seed: u64 = args.get(5).and_then(|v| v.parse().ok()).unwrap_or(1);
    match mode.as_str() {
        "toy" => toy(&b1, c, &run, d, seed, &which),
        "time" => {
            let reps: usize = args.get(5).and_then(|v| v.parse().ok()).unwrap_or(5);
            // the stream's heap set-up (before `ready`): the large-block cache pre-faulted
            crate::proc::heap_setup(3000);
            let fe = fe_bench();
            println!("fe product {fe:.2} ns (one thread, independent products)");
            let col = col_of(spec, &inp);
            let a: Vec<F192> = {
                let mut r = Rng::new(9);
                (0..d).map(|_| r.e()).collect()
            };
            let v_prev = phi_multi(&b1, std::slice::from_ref(&a))[0];
            if let Some(pk) = &b1.phik {
                // the kernels' phases at the 42 line points (the A23 step's batch)
                let pts: Vec<Vec<F192>> = (2..d as u64 + 1).map(|j| crate::lvm::acc::line(&a, &a.iter().rev().copied().collect::<Vec<_>>(), F192::new(j, 0, 0))).collect();
                for _ in 0..3 {
                    let (_, ts) = pk.mats_timed(&pts);
                    println!("phik phases ({} points): tables {:.4} kernels {:.4} s", pts.len(), ts[0], ts[1]);
                }
            }
            let mut buf = vec![F64::ZERO; 1 << 23];
            for rep in 0..reps {
                let t = Instant::now();
                let tabs = crate::lvm::stream::build_q_tables(&q, &col, &inp.hdr);
                let t_a = t.elapsed().as_secs_f64();
                let words = crate::lvm::m3::committed_words(&tabs);
                drop(tabs);
                let t = Instant::now();
                let run = run_fixpoint(c, spec, &inp);
                let t_run = t.elapsed().as_secs_f64();
                let z = b1.witness(&run);
                let t_z = t.elapsed().as_secs_f64() - t_run;
                let t = Instant::now();
                buf[..b1.committed].copy_from_slice(&z[..b1.committed]);
                let t_cp = t.elapsed().as_secs_f64();
                let t = Instant::now();
                let pf = prove(&b1, &z, &a, v_prev, &mut Rng::new(100 + rep as u64));
                let t_b = t.elapsed().as_secs_f64();
                std::hint::black_box(&pf.acc.y);
                println!(
                    "typed time rep={rep} A_build_s={t_a:.4} A_words={words} B_run_s={t_run:.4} B_z_s={t_z:.4} B_copy_s={t_cp:.4} backend_s={t_b:.4} abc_s={:.4} zc_s={:.4} u_s={:.4} wiring_s={:.4} mvals_s={:.4} h_s={:.4} h_eval_s={:.4}",
                    pf.secs[0], pf.secs[1], pf.secs[2], pf.secs[3], pf.secs[4], pf.secs[5], pf.acc.secs_eval
                );
            }
        }
        _ => crate::service::fatal("typed toy|time P8|P20|BLOB INPUTS [SEED|REPS]"),
    }
}

fn toy(b1: &Typed, c: &crate::lvm::loopir::Compiled, run: &crate::lvm::loopir::Run, d: usize, seed: u64, which: &str) {
    let mut rng = Rng::new(seed);
    let z = b1.witness(run);
    let abc = b1.abc(&z);
    let bad = b1.check(&abc);
    {
        // the honest prover's fast zerocheck against the general one, same challenges
        let tau: Vec<F192> = {
            let mut r = Rng::new(5);
            (0..b1.x_log).map(|_| r.e()).collect()
        };
        let g = zerocheck([abc[0].clone(), abc[1].clone(), abc[2].clone()], &tau, &mut Rng::new(6));
        let f = zerocheck_fast(b1.ab_vals(&z), &tau, b1.x_live, &mut Rng::new(6));
        let dr = (0..g.rounds.len()).find(|&i| g.rounds[i] != f.rounds[i]);
        println!("zerocheck fast vs general: first differing round {dr:?}; finals equal a {} b {} c {}", g.a == f.a, g.b == f.b, g.c == f.c);
    }
    let (mut nk, mut ne) = (0usize, 0usize);
    for &(b, t) in &b1.tags {
        let r = &c.q.blocks[b].tpl[t];
        if r.ty == Ty::E {
            ne += c.lay[b].size
        } else {
            nk += c.lay[b].size
        }
    }
    println!("relation: {} failing (block, row) kinds; constraint rows K {nk} E {ne}", bad.len());
    for (tag, n, x) in bad.iter().take(40) {
        let (b, t) = b1.tags[*tag as usize];
        let r = &c.q.blocks[b].tpl[t];
        println!("  FAIL block {b} row {t} op {:?} ty {:?} args {:?}: {n} slots (first {x})", r.op, r.ty, r.args.iter().map(|a| a.ty).collect::<Vec<_>>());
    }
    // the incoming accumulator: a random point and its true value
    let a: Vec<F192> = (0..d).map(|_| rng.e()).collect();
    let v_prev = phi_brute(b1, &a);
    let t = Instant::now();
    let pf = prove(b1, &z, &a, v_prev, &mut Rng::new(seed + 1));
    println!(
        "honest prove {:.3} s (abc {:.4} zc {:.4} u {:.4} wiring {:.4} M̃ {:.4} h {:.4}); h eval {:.4}",
        t.elapsed().as_secs_f64(),
        pf.secs[0],
        pf.secs[1],
        pf.secs[2],
        pf.secs[3],
        pf.secs[4],
        pf.secs[5],
        pf.acc.secs_eval
    );
    let honest = verify(b1, &z, &pf, &a, v_prev, true);
    println!(
        "HONEST: {}",
        match &honest {
            Ok(()) => "ACCEPT (zerocheck with K and E rows closes; wiring closes; M̃, z̃ match; acc step holds)".to_string(),
            Err(e) => format!("REJECT {e}"),
        }
    );
    println!("acc_out: Φ_Q(pt) = h(t): {}", phi_brute(b1, &pf.acc.pt) == pf.acc.y);
    let mut ok = honest.is_ok() && bad.is_empty();
    let mut tamper = |name: &str, want_reject: bool, r: Result<(), String>| {
        let pass = r.is_err() == want_reject;
        ok &= pass;
        println!(
            "TAMPER {name}: {} [{}]",
            match &r {
                Ok(()) => "ACCEPT".to_string(),
                Err(e) => format!("REJECT: {e}"),
            },
            if pass { "as expected" } else { "UNEXPECTED" }
        );
    };
    // 1. one wrong result word (an E result limb of a muladd row, then a K result word)
    for ty in [Ty::E, Ty::K] {
        let tag = (0..b1.tags.len())
            .find(|&i| {
                let (b, t) = b1.tags[i];
                let r = &c.q.blocks[b].tpl[t];
                r.op == Op::MulAdd && r.ty == ty
            })
            .expect("a muladd row");
        let x = (0..1usize << b1.x_log).find(|&x| b1.slot_tag[x] == tag as u32).unwrap();
        let w = b1.ent[b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize].iter().find(|e| e.o == MW).unwrap().y as usize;
        let mut z2 = z.clone();
        z2[w] = z2[w] + F64(0x5a5a);
        let pf2 = prove(b1, &z2, &a, v_prev, &mut Rng::new(seed + 2));
        tamper(&format!("result word ({ty:?} muladd, slot {x}, word {w})"), true, verify(b1, &z2, &pf2, &a, v_prev, true));
    }
    // 2. one wrong operand entry of each matrix, pointing at another word with the same value (the relation still
    //    holds on the prover's matrices): caught by M̃ (brute) and, without it, by the accumulator
    for o in [MA, MB, MD, MW] {
        let i = (0..b1.ent.len()).find(|&i| b1.ent[i].o == o && b1.ent[i].c == F192::ONE).expect("an entry");
        let y = b1.ent[i].y as usize;
        let y2 = (0..z.len()).find(|&y2| y2 != y && z[y2] == z[y]).expect("another word with the value");
        let mut b2 = b1.clone_with_entry(i, y2 as u32);
        // the tampered prover evaluates its own (tampered) matrices with its own kernels
        b2.phik = Some(PhiK::new(&b2));
        let pf2 = prove(&b2, &z, &a, v_prev, &mut Rng::new(seed + 3));
        tamper(&format!("operand of {} (entry {i}: word {y} -> {y2}, same value)", ["A", "B", "D", "W"][o as usize]), true, verify(b1, &z, &pf2, &a, v_prev, true));
        tamper("  same, V without the brute M̃ check (the accumulator alone)", true, verify(b1, &z, &pf2, &a, v_prev, false));
    }
    // 3. h: one coefficient (h(1) moves), then two equal shifts (h(0), h(1) kept)
    {
        let mut pf2 = prove(b1, &z, &a, v_prev, &mut Rng::new(seed + 5));
        pf2.acc.h[5] += F192::new(1, 2, 3);
        tamper("h[5]", true, verify(b1, &z, &pf2, &a, v_prev, true));
        pf2.acc.h[6] += F192::new(1, 2, 3);
        tamper("h[5], h[6] (h(0), h(1) kept)", true, verify(b1, &z, &pf2, &a, v_prev, true));
    }
    println!("typed toy {which}: {}", if ok { "PASS" } else { "FAIL" });
    if !ok {
        std::process::exit(1);
    }
}
