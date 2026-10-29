//! `bench`: kernel and memory throughput on this machine (measurements only, P2 pass 6). Each
//! kernel runs on `par::threads()` workers, each on its own in-cache data; memory figures are over
//! 1 GiB buffers.

use crate::field::{B64, F};
use crate::par;
use std::time::Instant;

fn rnd(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

fn timed<R>(f: impl FnOnce() -> R) -> (R, f64) {
    let t = Instant::now();
    let r = f();
    (r, t.elapsed().as_secs_f64())
}

/// Per-worker in-cache loop: `iters` calls of `body(worker)`; returns calls per second in all.
fn per_worker(iters: usize, body: &(dyn Fn(usize, usize) + Sync)) -> f64 {
    let t = par::threads();
    let (_, s) = timed(|| par::run(t, &|w| body(w, iters)));
    (t * iters) as f64 / s
}

pub fn run() {
    let t = par::threads();
    let gib = 1usize << 30;
    let words = gib / 8;
    let mut buf: Vec<u64> = vec![0; words];
    let mut b2: Vec<u64> = vec![0; words];
    for _ in 0..2 {
        let p = par::SyncPtr(buf.as_mut_ptr());
        let (_, ws) = timed(|| par::fill(&mut b2, 1 << 16, |i| i as u64));
        let (x, rs) = timed(|| {
            let parts = par::map_chunks(words, 1 << 16, |lo, hi| {
                let p = p;
                let s = unsafe { std::slice::from_raw_parts(p.0.add(lo), hi - lo) };
                s.iter().fold(0u64, |a, b| a ^ b)
            });
            parts.into_iter().fold(0, |a, b| a ^ b)
        });
        let src = &b2;
        let (_, cs) = timed(|| par::for_each_chunk_mut(&mut buf, 1 << 16, |off, ch| ch.copy_from_slice(&src[off..off + ch.len()])));
        println!("BENCH mem threads={t} write_GBs={:.1} read_GBs={:.1} copy_GBs={:.1} ({x})", gib as f64 / ws / 1e9, gib as f64 / rs / 1e9, gib as f64 / cs / 1e9);
    }
    drop((buf, b2));
    // round 1: one window = 1,024 bytes each of a, b, z
    let sk = crate::skipdom::skip();
    let nwin = 16;
    let mut s = 7u64;
    let data: Vec<u8> = (0..3 * 1024 * nwin).map(|_| rnd(&mut s) as u8).collect();
    let r1 = per_worker(20_000, &|_, it| {
        let mut out = [F::ZERO; 192];
        let mut acc = F::ZERO;
        for i in 0..it {
            let w = i % nwin;
            let (a, b, z) = (&data[w * 1024..w * 1024 + 1024], &data[(nwin + w) * 1024..(nwin + w) * 1024 + 1024], &data[(2 * nwin + w) * 1024..(2 * nwin + w) * 1024 + 1024]);
            crate::simd::round1_window(sk, a, b, z, &mut out);
            acc += out[i % 192];
        }
        std::hint::black_box(acc);
    });
    println!("BENCH r1_window threads={t} windows_per_s={r1:.0} ns_per_window_per_thread={:.0}", 1e9 * t as f64 / r1);
    // butterfly: 2 × 8 KiB slices
    let bf = per_worker(200_000, &|w, it| {
        let mut s = 99 + w as u64;
        let mut top: Vec<F> = (0..512).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
        let mut bot: Vec<F> = (0..512).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
        for i in 0..it {
            crate::simd::butterfly(&mut top, &mut bot, B64(0x1234_5678_9abc_def0 ^ i as u64));
        }
        std::hint::black_box(&top);
    });
    println!("BENCH butterfly threads={t} butterflies_per_s={:.3e} ns_per_bfly_per_thread={:.2}", bf * 512.0, 1e9 * t as f64 / (bf * 512.0));
    // axpy (F × F products)
    let ax = per_worker(200_000, &|w, it| {
        let mut s = 5 + w as u64;
        let mut acc: Vec<F> = (0..512).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
        let x: Vec<F> = (0..512).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
        for i in 0..it {
            crate::simd::axpy(&mut acc, &x, F::new(i as u64 | 1, 3));
        }
        std::hint::black_box(&acc);
    });
    println!("BENCH axpy threads={t} mul_per_s={:.3e} ns_per_mul_per_thread={:.2}", ax * 512.0, 1e9 * t as f64 / (ax * 512.0));
    // phi_add: 16 byte-table lookups per element (64 KiB tables)
    let mut s = 11u64;
    let rpp: Vec<F> = (0..7).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
    let tab = crate::ringswitch::phi_tables(&rpp, F::new(5, 9));
    let ph = per_worker(20_000, &|w, it| {
        let mut s = 3 + w as u64;
        let x: Vec<F> = (0..1024).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
        let mut acc = vec![F::ZERO; 1024];
        for _ in 0..it {
            crate::simd::phi_add(&tab, &x, &mut acc);
        }
        std::hint::black_box(&acc);
    });
    println!("BENCH phi_add threads={t} per_s={:.3e} ns_per_elem_per_thread={:.2}", ph * 1024.0, 1e9 * t as f64 / (ph * 1024.0));
}

/// `bench-rs [m]` (pass 10): the node's ring-switch passes at `m` (default 32) on random data:
/// E4's slices (`partials` vs the block fold) and the four-claim weight table (the reference vs row
/// tables of `2^lo` elements, `lo = 3 … 6`); each result checked equal to the reference.
pub fn run_rs(m: usize) {
    let mu = m - 7;
    let mut s = 0x5eedu64;
    let mut rf = || F::new(rnd(&mut s), rnd(&mut s));
    let z: Vec<u64> = {
        let mut z = crate::witness::alloc_u64(2usize << mu);
        par::for_each_chunk_mut(&mut z, 1 << 16, |off, ch| {
            let mut s = 0x9e37_79b9u64 ^ off as u64;
            ch.iter_mut().for_each(|x| *x = rnd(&mut s));
        });
        z
    };
    let r4: Vec<F> = (0..mu).map(|_| rf()).collect();
    for rep in 0..2 {
        let (a, ta) = timed(|| crate::ringswitch::partials(&z, &r4));
        let (b, tb) = timed(|| crate::leaf::partials_from_fold(&crate::lincheck::partial_fold(&z, &r4[7..], z.len() / 256), &r4[..7]));
        println!("BENCH rs.slices m={m} rep={rep} partials_s={ta:.3} fold_s={tb:.3} equal={}", a == b);
    }
    let rpp: Vec<F> = (0..7).map(|_| rf()).collect();
    let his: Vec<Vec<F>> = (0..4).map(|j| (0..mu).map(|i| if j == 2 && (3..7).contains(&i) { F::ZERO } else { rf() }).collect()).collect();
    let kf: Vec<F> = (0..1usize << (mu - 7)).map(|i| if i % 3 == 0 { F::ONE } else { F::new(7 + (i % 5) as u64, 0) }).collect();
    let cs: Vec<F> = (0..4).map(|_| rf()).collect();
    let cl: Vec<(&[F], F, Option<&[F]>)> = vec![(&his[0][..], cs[0], None), (&his[1][..], cs[1], Some(&kf[..])), (&his[2][..], cs[2], None), (&his[3][..], cs[3], None)];
    let mut want = Vec::new();
    for rep in 0..2 {
        let (w, t) = timed(|| crate::ringswitch::weight_table_kf_ref(&cl, &rpp));
        println!("BENCH rs.weight m={m} rep={rep} ref_s={t:.3}");
        want = w;
    }
    for lo in 3..=6 {
        for rep in 0..2 {
            let (w, t) = timed(|| crate::ringswitch::weight_table_rows(&cl, &rpp, lo));
            println!("BENCH rs.weight m={m} rep={rep} rows lo={lo} s={t:.3} equal={}", w == want);
        }
    }
}

/// `bench-trace [N2|N4|N8]`: the node's H block trace (`node::trace_blocks`) on random inputs of the
/// kind's H blocks: one thread per batch and all threads; checked equal to `trace_blocks_ref`.
pub fn run_trace(kind: &str) {
    use crate::node::{self, BlockIn, NK};
    let k = match kind {
        "N4" => NK::N4,
        "N8" => NK::N8,
        _ => NK::N2,
    };
    let c = node::general_circuit();
    let gates = c.nodes.iter().filter(|n| matches!(n, crate::circuit::Node::Gate(..))).count();
    let rows = c.rows.iter().filter(|r| r.is_some()).count();
    let h_end = k.h_end();
    let bks: Vec<node::BK> = (0..h_end).map(|b| node::bk_at(k, b)).collect();
    let mut s = 0x7ace_u64;
    let ins: Vec<BlockIn> = bks
        .iter()
        .map(|&bk| {
            let h: [u32; 8] = std::array::from_fn(|_| rnd(&mut s) as u32);
            let msg: Vec<u8> = (0..64).map(|_| rnd(&mut s) as u8).collect();
            BlockIn::of(bk, h, &msg)
        })
        .collect();
    let nbat = h_end.div_ceil(64);
    println!("BENCH trace {} nodes={} gates={gates} rows={rows} h_end={h_end} batches={nbat} threads={}", k.name(), c.nodes.len(), par::threads());
    let words = nbat * 64 * 256;
    let run = |f: fn(&crate::circuit::Circuit, &[BlockIn], &[node::BK], &mut [u64], &mut [u64], &mut [u64]), nb: usize, par_on: bool| {
        let (mut z, mut a, mut b) = (vec![0u64; words], vec![0u64; words], vec![0u64; words]);
        let (pz, pa, pb) = (par::SyncPtr(z.as_mut_ptr()), par::SyncPtr(a.as_mut_ptr()), par::SyncPtr(b.as_mut_ptr()));
        let body = |g: usize| {
            let (pz, pa, pb) = (pz, pa, pb);
            let (lo, hi) = (64 * g, (64 * g + 64).min(h_end));
            let n = hi - lo;
            let (zs, as_, bs) = unsafe {
                (
                    std::slice::from_raw_parts_mut(pz.0.add(256 * lo), 256 * n),
                    std::slice::from_raw_parts_mut(pa.0.add(256 * lo), 256 * n),
                    std::slice::from_raw_parts_mut(pb.0.add(256 * lo), 256 * n),
                )
            };
            f(&c, &ins[lo..hi], &bks[lo..hi], zs, as_, bs);
        };
        let t = Instant::now();
        if par_on {
            par::run(nb, &body);
        } else {
            (0..nb).for_each(body);
        }
        (t.elapsed().as_secs_f64(), z, a, b)
    };
    let one = 16.min(nbat);
    for rep in 0..2 {
        let (tr, zr, ar, br) = run(node::trace_blocks_ref, one, false);
        let (tn, zn, an, bn) = run(node::trace_blocks, one, false);
        println!("BENCH trace 1 thread rep={rep}: {one} batches ref {:.3} ms/batch new {:.3} ms/batch equal={}", tr * 1e3 / one as f64, tn * 1e3 / one as f64, zr == zn && ar == an && br == bn);
    }
    for rep in 0..2 {
        let (tr, zr, ar, br) = run(node::trace_blocks_ref, nbat, true);
        let (tn, zn, an, bn) = run(node::trace_blocks, nbat, true);
        println!("BENCH trace all rep={rep}: ref {tr:.3} s new {tn:.3} s equal={}", zr == zn && ar == an && br == bn);
    }
}

/// `bench-r1 [m]` (pass 12): round 1's window kernels, one thread and all threads (in-cache
/// windows; pass 11's `r1::window` and the tower form `r1::window_t`, checked equal), then
/// `zerocheck::round1` vs `round1_ref` over a random witness of `2^m` bits (default 30).
pub fn run_r1(m: usize) {
    let sk = crate::skipdom::skip();
    let nwin = 16;
    let mut s = 7u64;
    let data: Vec<u8> = (0..3 * 1024 * nwin).map(|_| rnd(&mut s) as u8).collect();
    let win = |w: usize| (&data[w * 1024..w * 1024 + 1024], &data[(nwin + w) * 1024..(nwin + w) * 1024 + 1024], &data[(2 * nwin + w) * 1024..(2 * nwin + w) * 1024 + 1024]);
    let mut eq = true;
    for w in 0..nwin {
        let (a, b, z) = win(w);
        let (mut o0, mut o1) = ([F::ZERO; 192], [F::ZERO; 192]);
        crate::zerocheck::window_portable(sk, a, b, z, &mut o0);
        if crate::simd::hw_avx2() {
            unsafe { crate::simd::r1::window_t(sk, a, b, z, &mut o1) };
            eq &= o0 == o1;
        }
    }
    println!("BENCH r1 tier={} window_t_equal={eq}", crate::simd::tier_name());
    if !crate::simd::hw_avx2() {
        return;
    }
    type Wf = unsafe fn(&crate::skipdom::Skip, &[u8], &[u8], &[u8], &mut [F; 192]);
    let kernels: [(&str, Wf); 3] = [("window", crate::simd::r1::window), ("window_t1", crate::simd::r1::window_t1), ("window_t", crate::simd::r1::window_t)];
    for thr in [1usize, par::threads()] {
        for rep in 0..2 {
            for (name, f) in kernels {
                let it = 20_000;
                let (_, sec) = timed(|| {
                    par::run(thr, &|_| {
                        let mut out = [F::ZERO; 192];
                        let mut acc = F::ZERO;
                        for i in 0..it {
                            let (a, b, z) = win(i % nwin);
                            unsafe { f(sk, a, b, z, &mut out) };
                            acc += out[i % 192];
                        }
                        std::hint::black_box(acc);
                    })
                });
                println!("BENCH r1 {name} threads={thr} rep={rep} ns_per_window_per_thread={:.0}", sec * 1e9 / it as f64);
            }
        }
    }
    // the parts of window_t: rows (LDE, products, z transposes) and the conversion
    for thr in [1usize, par::threads()] {
        for rep in 0..2 {
            let it = 20_000;
            let (_, sr) = timed(|| {
                par::run(thr, &|_| {
                    let mut ch = crate::simd::r1::Chunks::new();
                    for i in 0..it {
                        let (a, b, z) = win(i % nwin);
                        unsafe { crate::simd::r1::rows_t(sk, a, b, z, &mut ch, true) };
                        std::hint::black_box(&ch);
                    }
                })
            });
            let (_, sc) = timed(|| {
                par::run(thr, &|_| {
                    let mut ch = crate::simd::r1::Chunks::new();
                    let mut out = [F::ZERO; 192];
                    let mut acc = F::ZERO;
                    for i in 0..it {
                        let (a, b, z) = win(i % nwin);
                        if i < nwin {
                            unsafe { crate::simd::r1::rows_t(sk, a, b, z, &mut ch, false) };
                        }
                        unsafe { crate::simd::r1::convert(sk, std::hint::black_box(&ch), &mut out) };
                        acc += out[i % 192];
                    }
                    std::hint::black_box(acc);
                })
            });
            let (_, st) = timed(|| {
                par::run(thr, &|_| {
                    let mut ch = crate::simd::r1::Chunks::new();
                    let mut out = [F::ZERO; 192];
                    let mut acc = F::ZERO;
                    for i in 0..it {
                        let (a, b, z) = win(i % nwin);
                        if i < nwin {
                            unsafe { crate::simd::r1::rows_t(sk, a, b, z, &mut ch, true) };
                        }
                        unsafe { crate::simd::r1::convert_t(sk, std::hint::black_box(&ch), &mut out) };
                        acc += out[i % 192];
                    }
                    std::hint::black_box(acc);
                })
            });
            let (_, sm) = timed(|| {
                par::run(thr, &|w| {
                    let mut u = vec![0u128; 576];
                    let x: Vec<F> = (0..192).map(|i| F::new(i as u64 * 77 + w as u64, 5)).collect();
                    for i in 0..it {
                        crate::simd::mac_u(&mut u, &x, F::new(i as u64 | 1, 9));
                    }
                    std::hint::black_box(&u);
                })
            });
            let (_, sa) = timed(|| {
                par::run(thr, &|w| {
                    let mut u = vec![F::ZERO; 192];
                    let x: Vec<F> = (0..192).map(|i| F::new(i as u64 * 77 + w as u64, 5)).collect();
                    for i in 0..it {
                        crate::simd::axpy(&mut u, &x, F::new(i as u64 | 1, 9));
                    }
                    std::hint::black_box(&u);
                })
            });
            let ns = |x: f64| x * 1e9 / it as f64;
            println!("BENCH r1 parts threads={thr} rep={rep} ns_per_window_per_thread: rows_t={:.0} convert={:.0} convert_t={:.0} mac_u={:.0} axpy={:.0}", ns(sr), ns(sc), ns(st), ns(sm), ns(sa));
        }
    }
    // the whole round 1 over 2^m bits
    let n = 1usize << (m - 3);
    let mk = |seed: u64| -> Vec<u8> {
        let mut v = vec![0u8; n];
        par::for_each_chunk_mut(&mut v, 1 << 19, |off, ch| {
            let mut s = (seed ^ (off as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)) | 1;
            ch.iter_mut().for_each(|x| *x = rnd(&mut s) as u8);
        });
        v
    };
    let (a, b, z) = (mk(1), mk(2), mk(3));
    let mut s = 0x77u64;
    let r_out: Vec<F> = (0..m - 13).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect();
    let used = n / 2048;
    for rep in 0..2 {
        let (x, t1) = timed(|| crate::zerocheck::round1_ref(&a, &b, &z, &r_out, used));
        let (y, t2) = timed(|| crate::zerocheck::round1(&a, &b, &z, &r_out, used));
        println!("BENCH r1 round1 m={m} rep={rep} ref_s={t1:.3} new_s={t2:.3} equal={}", x.pab == y.pab && x.bank == y.bank);
    }
}

/// `bench-k` (pass 12): the butterfly and the F product with the reductions by carry-less products
/// (pass 11's `butterfly_cl`, `axpy_cl`) and by shifts (`butterfly`, `axpy`), one thread and all threads, in
/// cache; checked equal. Needs the ymm tier.
pub fn run_k() {
    if crate::simd::tier() != 3 {
        println!("BENCH k: tier {} (needs ymm)", crate::simd::tier_name());
        return;
    }
    use crate::simd::ymm;
    let mk = |w: usize, n: usize| -> Vec<F> {
        let mut s = 99 + w as u64;
        (0..n).map(|_| F::new(rnd(&mut s), rnd(&mut s))).collect()
    };
    let (mut t0, mut b0) = (mk(1, 512), mk(2, 512));
    let (mut t1, mut b1) = (t0.clone(), b0.clone());
    unsafe {
        ymm::butterfly_cl(&mut t0, &mut b0, B64(0x1234_5678_9abc_def1));
        ymm::butterfly(&mut t1, &mut b1, B64(0x1234_5678_9abc_def1));
    }
    let (mut a0, x) = (mk(3, 512), mk(4, 512));
    let mut a1 = a0.clone();
    unsafe {
        ymm::axpy_cl(&mut a0, &x, F::new(77, 99));
        ymm::axpy(&mut a1, &x, F::new(77, 99));
    }
    println!("BENCH k equal butterfly={} axpy={}", t0 == t1 && b0 == b1, a0 == a1);
    for thr in [1usize, par::threads()] {
        for rep in 0..2 {
            let it = 100_000;
            let bf = |sh: bool| {
                timed(|| {
                    par::run(thr, &|w| {
                        let (mut top, mut bot) = (mk(w, 512), mk(w + 7, 512));
                        for i in 0..it {
                            let t = B64(0x1234_5678_9abc_def0 ^ i as u64);
                            unsafe {
                                if sh {
                                    ymm::butterfly(&mut top, &mut bot, t)
                                } else {
                                    ymm::butterfly_cl(&mut top, &mut bot, t)
                                }
                            }
                        }
                        std::hint::black_box(&top);
                    })
                })
                .1 * 1e9
                    / (it as f64 * 512.0)
            };
            let ax = |sh: bool| {
                timed(|| {
                    par::run(thr, &|w| {
                        let (mut acc, x) = (mk(w, 512), mk(w + 7, 512));
                        for i in 0..it {
                            let c = F::new(i as u64 | 1, 3);
                            unsafe {
                                if sh {
                                    ymm::axpy(&mut acc, &x, c)
                                } else {
                                    ymm::axpy_cl(&mut acc, &x, c)
                                }
                            }
                        }
                        std::hint::black_box(&acc);
                    })
                })
                .1 * 1e9
                    / (it as f64 * 512.0)
            };
            println!(
                "BENCH k threads={thr} rep={rep} ns_per_item_per_thread: butterfly_cl={:.3} butterfly={:.3} axpy_cl={:.3} axpy={:.3}",
                bf(false),
                bf(true),
                ax(false),
                ax(true)
            );
        }
    }
}

/// `bench-nd [DIR]` (pass 12): the node data from the embedded blob (`decode_blob`) and from its
/// image (`save_image` written to `DIR/nodedata.bin`, read back and `load_image`d), twice each.
pub fn run_nd(dir: &str) {
    let tag = crate::plan::data_tag();
    let path = std::path::Path::new(dir).join(crate::plan::IMAGE);
    for rep in 0..2 {
        let (nd, td) = timed(|| crate::plan::decode_blob(crate::plan::BLOB));
        let img = crate::plan::save_image(&nd, &tag);
        if rep == 0 {
            for p in nd.protos.iter() {
                let nf: usize = p.regs.iter().map(|r| r.forms.len()).sum();
                let mut cf: Vec<F> = p.rows.cv.iter().chain(p.fcoefs.iter()).copied().collect();
                cf.sort_by_key(|x| (x.lo, x.hi));
                cf.dedup();
                let ones = p.rows.coefs.iter().filter(|&&i| i == crate::mfill::ONE_IX).count();
                println!("BENCH nd proto {}: rows {} nnz {} (coefficient 1: {ones}) regs {} forms {} aux {} fcells {} distinct coefs {} (rows {})", p.pi, p.rows.idx.len(), p.rows.cells.len(), p.regs.len(), nf, p.aux.len(), p.fcells.len(), cf.len(), p.rows.cv.len());
            }
        }
        std::fs::write(&path, &img).expect("write the image");
        drop(nd);
        let (ok, ti) = timed(|| std::fs::read(&path).ok().and_then(|b| crate::plan::load_image(&b, &tag)).is_some());
        println!("BENCH nd rep={rep} blob_s={td:.3} image_s={ti:.3} image_bytes={} loaded={ok}", img.len());
    }
}
