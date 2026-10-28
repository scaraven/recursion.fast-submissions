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
