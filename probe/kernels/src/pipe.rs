//! An end-to-end leaf (or node-shaped) prover skeleton at real sizes: every per-witness-bit kernel
//! of the measured items, in protocol order, on one set of buffers, with the best tier available.
//! It checks the additive per-compression model against cache and memory effects at m = 30..32,
//! and gives the peak memory of a straightforward buffer schedule.
//!
//! Not modelled here (each is costed separately in K-kernels.md): the oracle service's Merkle and
//! Fiat-Shamir hashing (it runs on the same CPUs), transcript round trips, the lincheck's
//! per-proof matrix evaluation (a circuit walk, O(10^5) XOR), queries and proof serialisation.
//! Challenges and tables are random; values are not checked (the kernels are checked in selftest).
use crate::gf::*;
use crate::ntt::{Kern, Ntt};
use crate::skip::{R1Kern, R2Kern, R2};
use crate::sumcheck::*;
use crate::{blake, lin, par_for, peak_rss_mb, skip, Rng, SyncPtr};
use std::time::Instant;

fn as_u8(v: &[F128]) -> &[u8] {
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 16) }
}

struct Clock {
    phases: Vec<(String, f64)>,
}
impl Clock {
    fn run<T>(&mut self, name: &str, f: impl FnOnce() -> T) -> T {
        let t = Instant::now();
        let r = f();
        let s = t.elapsed().as_secs_f64();
        println!("  phase {name:<28} {s:9.4} s   (peak RSS so far {:.0} MB)", peak_rss_mb());
        self.phases.push((name.into(), s));
        r
    }
}

/// Parallel fold+message over the prefix `len` of (a, b) into (ao, bo).
fn tail_round(a: &[F128], b: &[F128], ao: &mut [F128], bo: &mut [F128], len: usize, r: F128, eq: &[F128], c: Cpu, threads: usize) {
    let chunk = (1usize << 15).min(len);
    let n = len / chunk;
    let (pa, pb) = (SyncPtr(ao.as_mut_ptr()), SyncPtr(bo.as_mut_ptr()));
    par_for(threads, n, |i| {
        let (pa, pb) = (pa, pb);
        let (ao, bo) = unsafe { (std::slice::from_raw_parts_mut(pa.0.add(i * chunk / 2), chunk / 2), std::slice::from_raw_parts_mut(pb.0.add(i * chunk / 2), chunk / 2)) };
        let (ai, bi) = (&a[i * chunk..(i + 1) * chunk], &b[i * chunk..(i + 1) * chunk]);
        std::hint::black_box(if c.ymm {
            unsafe { fold_msg_ymm(ai, bi, ao, bo, r, eq) }
        } else if c.pclmul {
            unsafe { fold_msg_flock(ai, bi, ao, bo, r, eq) }
        } else {
            fold_msg_portable(ai, bi, ao, bo, r, eq)
        });
    });
}

fn lig_round(f: &[F128], w: &[F128], fo: &mut [F128], wo: &mut [F128], kk: bool, r: [F128; 2], c: Cpu, threads: usize) {
    let len = f.len();
    let chunk = (1usize << 15).min(len);
    let n = len / chunk;
    let (pf, pw) = (SyncPtr(fo.as_mut_ptr()), SyncPtr(wo.as_mut_ptr()));
    par_for(threads, n, |i| {
        let (pf, pw) = (pf, pw);
        let oc = if kk { chunk / 2 } else { chunk };
        let (fo, wo) = unsafe { (std::slice::from_raw_parts_mut(pf.0.add(i * oc), oc), std::slice::from_raw_parts_mut(pw.0.add(i * oc), oc)) };
        let (fi, wi) = (&f[i * chunk..(i + 1) * chunk], &w[i * chunk..(i + 1) * chunk]);
        std::hint::black_box(match (c.ymm, kk) {
            (true, false) => unsafe { lig_f2k_ymm(fi, wi, fo, wo, r) },
            (true, true) => unsafe { lig_k2k_ymm(fi, wi, fo, wo, r) },
            (false, false) => lig_f2k_portable(fi, wi, fo, wo, r),
            (false, true) => lig_k2k_portable(fi, wi, fo, wo, r),
        });
    });
}

/// A vector of `n` zeroed F128, first-touched by `threads` threads.
fn falloc(n: usize, threads: usize) -> Vec<F128> {
    let mut v: Vec<F128> = Vec::with_capacity(n);
    unsafe { v.set_len(n) };
    let p = SyncPtr(v.as_mut_ptr());
    let parts = 64.min(n);
    par_for(threads, parts, |i| {
        let p = p;
        let (s, e) = (i * n / parts, (i + 1) * n / parts);
        unsafe { std::slice::from_raw_parts_mut(p.0.add(s), e - s) }.fill(F128::ZERO);
    });
    v
}
fn sl<'a>(v: &'a mut [F128], s: usize, n: usize) -> &'a mut [F128] {
    &mut v[s..s + n]
}

/// `m`: log2 of committed bits; `useful`: compressions carrying witness (= 2^(m-14) for a leaf).
///
/// Buffer plan (np = 2^(m-7) packed F128): an arena of z, a, b (np each) and r2a, r2b (2np each),
/// 7np x 16 B = 7 * 2^(m-3) bytes, allocated and first-touched once (in the tree it is reused
/// from leaf to leaf), then: lincheck scratch in r2a; round-2 outputs r2a, r2b; tail ping-pong in
/// a, b; codeword in r2a; ring-switch tensors in r2b; rs_eq_ind in a; Ligerito K vectors in b and
/// r2b.
pub fn run(c: Cpu, m: usize, useful: usize, threads: usize) {
    let comps = 1usize << (m - 14);
    assert!(useful <= comps && useful % 8 == 0);
    let mut rng = Rng(1000 + m as u64);
    let mut ck = Clock { phases: vec![] };
    let t_all = Instant::now();
    println!("PIPE m={m} compressions={comps} useful={useful} threads={threads}");
    let tables = skip::Tables::new(&mut rng);
    let ntt0 = Ntt::new(m - 12);
    let ntt1 = Ntt::new(m - 14);
    let kern = if c.zmm {
        Kern::ZmmR8
    } else if c.ymm {
        Kern::YmmR4Kara
    } else if c.pclmul {
        Kern::ScalarR4(Tier::Pclmul)
    } else {
        Kern::ScalarR4(Tier::Portable)
    };
    let tier = if c.ymm { Tier::Ymm } else if c.pclmul { Tier::Pclmul } else { Tier::Portable };
    println!("  setup (tables, twiddles) {:.3} s; NTT kernel {}", t_all.elapsed().as_secs_f64(), kern.name());
    let np = 1usize << (m - 7);
    let (mut z, mut a, mut b, mut r2a, mut r2b) =
        ck.run("arena alloc+first touch", || (falloc(np, threads), falloc(np, threads), falloc(np, threads), falloc(2 * np, threads), falloc(2 * np, threads)));
    let t_prove = Instant::now();
    // 1. witness
    let hs = ck.run("chain (sequential compress)", || {
        let mut h = blake::IV;
        let mut hs = Vec::with_capacity(useful);
        let mut msg = [0u32; 16];
        for i in 0..useful {
            hs.push(h);
            msg[0] = i as u32;
            h = blake::compress(&h, &msg, 64, 0);
        }
        hs
    });
    ck.run("witness (z,a,b)", || {
        let (pz, pa, pb) = (SyncPtr(z.as_mut_ptr() as *mut u32), SyncPtr(a.as_mut_ptr() as *mut u32), SyncPtr(b.as_mut_ptr() as *mut u32));
        let per = 256;
        par_for(threads, useful.div_ceil(per), |ci| {
            let (pz, pa, pb) = (pz, pa, pb);
            let mut msg = [0u32; 16];
            for i in ci * per..((ci + 1) * per).min(useful) {
                msg[0] = i as u32;
                let o = 512 * i;
                unsafe {
                    blake::compress_wit(
                        &hs[i],
                        &msg,
                        64,
                        std::slice::from_raw_parts_mut(pz.0.add(o), 512),
                        std::slice::from_raw_parts_mut(pa.0.add(o), 512),
                        std::slice::from_raw_parts_mut(pb.0.add(o), 512),
                    );
                }
            }
        });
    });
    drop(hs);
    // 2. lincheck: pack z into stripes (scratch in r2a), partial fold over the outer variables
    ck.run("lincheck pack+partial fold", || {
        let zb = &as_u8(&z)[..useful * 2048];
        let zp = unsafe { std::slice::from_raw_parts_mut(r2a.as_mut_ptr() as *mut u8, zb.len()) };
        lin::pack(zb, zp, threads);
        let eq = rng.fvec(useful);
        std::hint::black_box(lin::partial_fold(zp, &eq, threads));
    });
    // 3. zerocheck round 1 (univariate skip) on (a, b, c = z); its C banks are the c-claim's s_hat_v
    let (n_lo, n_hi) = skip::r1_split(m);
    let (eq_lo, eq_hi) = (rng.fvec(1 << n_lo), rng.fvec(1 << n_hi));
    let xhi_lim = (useful * 2).div_ceil(1 << n_lo);
    let r1k = if c.ymm { R1Kern::Avx2 } else if c.pclmul { R1Kern::FlockZen3 } else { R1Kern::Portable };
    ck.run("zerocheck round 1 (skip)", || {
        let v = skip::View { m, a: as_u8(&a), b: as_u8(&b), c: as_u8(&z), eq_lo: &eq_lo, eq_hi: &eq_hi, n_lo };
        std::hint::black_box(skip::round1_lim(&tables, &v, r1k, threads, xhi_lim));
    });
    // 4. round 2: fold at z + message, into r2a, r2b
    let rows = 2 * np;
    let (l2, h2) = skip::r2_split(m);
    let (eq2_lo, eq2_hi) = (rng.fvec(1 << l2), rng.fvec(1 << h2));
    let useful_rows = useful * 256;
    let r2k = if c.ymm { R2Kern::Ymm } else if c.pclmul { R2Kern::FlockZen3 } else { R2Kern::Portable };
    let mut r2 = R2 { a_out: std::mem::take(&mut r2a), b_out: std::mem::take(&mut r2b), p1: F128::ZERO, pinf: F128::ZERO };
    ck.run("zerocheck round 2 (fold+msg)", || {
        let lim = (useful_rows / 2).div_ceil(1 << l2);
        skip::round2_lim(&tables, m, as_u8(&a), as_u8(&b), &eq2_lo, &eq2_hi, r2k, threads, &mut r2, lim);
    });
    r2a = std::mem::take(&mut r2.a_out);
    r2b = std::mem::take(&mut r2.b_out);
    // 5. zerocheck tail rounds over F: r2a/r2b -> a/b -> prefix of r2a/r2b -> ...
    ck.run("zerocheck tail rounds", || {
        let eq = rng.fvec(1024);
        let mut len = useful_rows.next_power_of_two().min(rows);
        let mut flip = false;
        while len >= 64 {
            let r = rng.f();
            if !flip {
                tail_round(&r2a, &r2b, sl(&mut a, 0, len / 2), sl(&mut b, 0, len / 2), len, r, &eq, c, threads);
            } else {
                tail_round(&a, &b, sl(&mut r2a, 0, len / 2), sl(&mut r2b, 0, len / 2), len, r, &eq, c, threads);
            }
            flip = !flip;
            len /= 2;
        }
    });
    // 6. commit: RS-encode level 0 (64 lanes, rate 1/2) into r2a
    ck.run("NTT level-0 encode", || ntt0.encode_half(&z, &mut r2a, 64, kern, threads));
    // 7. ring switching: two suffix eq tensors (in r2b), s_hat_v of the lincheck claim (1-way; the
    //    c-claim's came from round 1), rs_eq_ind of both claims (gamma folded into the tables) in a
    ck.run("ring switch", || {
        let (t0, t1) = r2b.split_at_mut(np);
        eq_build(&rng.fvec(m - 7), t0, tier, threads);
        eq_build(&rng.fvec(m - 7), t1, tier, threads);
        let per = np / 64;
        let (t0, t1) = (&*t0, &*t1);
        par_for(threads, 64, |w| {
            let mut a0 = [F128::ZERO; 128];
            let s = w * per;
            fold_1b_rows_1way_range(&z[s..s + per], &t1[s..s + per], &mut a0);
            std::hint::black_box(a0);
        });
        let tab0 = fold_b128_tables(&rng.fvec(128));
        let tab1 = fold_b128_tables(&rng.fvec(128));
        let prs = SyncPtr(a.as_mut_ptr());
        let pb = SyncPtr(b.as_mut_ptr());
        par_for(threads, 64, |w| {
            let (prs, pb) = (prs, pb);
            let o = unsafe { std::slice::from_raw_parts_mut(prs.0.add(w * per), per) };
            let o2 = unsafe { std::slice::from_raw_parts_mut(pb.0.add(w * per), per) };
            fold_b128_range(&t0[w * per..(w + 1) * per], &tab0, o);
            fold_b128_range(&t1[w * per..(w + 1) * per], &tab1, o2);
            for (x, y) in o.iter_mut().zip(o2.iter()) {
                *x += *y;
            }
        });
    });
    // 8. Ligerito opening sumcheck over (f = packed z, w = rs_eq_ind in a): one F->K round into
    //    (b, r2b[..np]), then K->K rounds ping-ponging with r2b[np..] to the end; level-1 commit
    //    (16 lanes; rate 1/4 approximated by a rate-1/2 encode of twice the message)
    let lev1 = ck.run("Ligerito sumcheck", || {
        let r = [rng.f(), rng.f()];
        let (w0, w1) = r2b.split_at_mut(np);
        lig_round(&z, &a, &mut b, w0, false, r, c, threads);
        let (g0, g1) = w1.split_at_mut(np / 2);
        let mut len = np;
        let mut lev1 = vec![];
        let mut round = 1;
        let (mut fk, mut wk): (&mut [F128], &mut [F128]) = (&mut b[..], w0);
        let (mut gf, mut gw): (&mut [F128], &mut [F128]) = (g0, g1);
        while len >= 1 << 12 {
            lig_round(&fk[..len], &wk[..len], &mut gf[..len / 2], &mut gw[..len / 2], true, r, c, threads);
            std::mem::swap(&mut fk, &mut gf);
            std::mem::swap(&mut wk, &mut gw);
            len /= 2;
            round += 1;
            if round == 6 {
                lev1 = fk[..len].to_vec();
            }
        }
        lev1
    });
    ck.run("NTT level-1 encode", || {
        let msg_len = 1usize << (m - 11);
        let mut msg = lev1.clone();
        msg.resize(msg_len, F128::ONE);
        let mut out = vec![F128::ZERO; 2 * msg_len];
        ntt1.encode_half(&msg, &mut out, 16, kern, threads);
    });
    std::hint::black_box((&z, &a, &b, &r2a, &r2b));
    let total = t_prove.elapsed().as_secs_f64();
    let alloc = ck.phases[0].1;
    println!(
        "PIPE_TOTAL m={m} useful={useful} threads={threads}: compute {total:.4} s ({:.1} ns per useful compression, {:.0} compressions/s); arena alloc+touch {alloc:.4} s; peak RSS {:.0} MB",
        total * 1e9 / useful as f64,
        useful as f64 / total,
        peak_rss_mb()
    );
}
