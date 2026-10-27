//! Field-product throughput (item 1) and memory bandwidth.
use crate::gf::*;
use crate::{par_best, quick, report, Rng};
use std::arch::x86_64::*;
use std::hint::black_box;

const N: usize = 4096; // L1/L2-resident operand arrays

// ---- batched c[i] = a[i] * b[i]
fn batch_portable(a: &[F128], b: &[F128], c: &mut [F128]) {
    for i in 0..a.len() {
        c[i] = mul_portable(a[i], b[i]);
    }
}
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn batch_pclmul(a: &[F128], b: &[F128], c: &mut [F128]) {
    for i in 0..a.len() {
        c[i] = mul_pclmul(a[i], b[i]);
    }
}
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn batch_xmm(a: &[F128], b: &[F128], c: &mut [F128]) {
    for i in 0..a.len() {
        c[i] = from_x(mul_xmm(to_x(a[i]), to_x(b[i])));
    }
}
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn batch_ymm(a: &[F128], b: &[F128], c: &mut [F128]) {
    let mut i = 0;
    while i < a.len() {
        st_y(c.as_mut_ptr().add(i), mul_y(ld_y(a.as_ptr().add(i)), ld_y(b.as_ptr().add(i))));
        i += 2;
    }
}
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn batch_ymm_kara(a: &[F128], b: &[F128], c: &mut [F128]) {
    let mut i = 0;
    while i < a.len() {
        let y = ld_y(b.as_ptr().add(i));
        st_y(c.as_mut_ptr().add(i), mul_y_kara(ld_y(a.as_ptr().add(i)), y, kara_pre_y(y)));
        i += 2;
    }
}
/// Product by one constant (NTT twiddle / fold challenge shape): Karatsuba with the constant's
/// middle operand precomputed.
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn bconst_ymm_kara(a: &[F128], t: F128, c: &mut [F128]) {
    let y = bcast_y(t);
    let yk = kara_pre_y(y);
    let mut i = 0;
    while i < a.len() {
        st_y(c.as_mut_ptr().add(i), mul_y_kara(ld_y(a.as_ptr().add(i)), y, yk));
        i += 2;
    }
}
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn bconst_ymm(a: &[F128], t: F128, c: &mut [F128]) {
    let y = bcast_y(t);
    let mut i = 0;
    while i < a.len() {
        st_y(c.as_mut_ptr().add(i), mul_y(ld_y(a.as_ptr().add(i)), y));
        i += 2;
    }
}
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
unsafe fn batch_zmm(a: &[F128], b: &[F128], c: &mut [F128]) {
    let mut i = 0;
    while i < a.len() {
        st_z(c.as_mut_ptr().add(i), mul_z(ld_z(a.as_ptr().add(i)), ld_z(b.as_ptr().add(i))));
        i += 4;
    }
}

// ---- multiply-accumulate, delayed reduction
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn mac_pclmul(a: &[F128], b: &[F128]) -> F128 {
    // Flock's scalar F256Unreduced accumulate
    let mut r = [0u64; 4];
    for i in 0..a.len() {
        let u = mul_unreduced_pclmul(a[i], b[i]);
        for k in 0..4 {
            r[k] ^= u[k];
        }
    }
    reduce(r[0], r[1], r[2], r[3])
}
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn mac_xmm(a: &[F128], b: &[F128]) -> F128 {
    let mut w = Wide1::zero();
    for i in 0..a.len() {
        w.mac(to_x(a[i]), to_x(b[i]));
    }
    from_x(w.reduce())
}
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn mac_ymm(a: &[F128], b: &[F128]) -> F128 {
    let mut w0 = Wide2::zero();
    let mut w1 = Wide2::zero();
    let mut i = 0;
    while i < a.len() {
        w0.mac(ld_y(a.as_ptr().add(i)), ld_y(b.as_ptr().add(i)));
        w1.mac(ld_y(a.as_ptr().add(i + 2)), ld_y(b.as_ptr().add(i + 2)));
        i += 4;
    }
    w0.add(&w1);
    w0.reduce_sum()
}
#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
unsafe fn mac_zmm(a: &[F128], b: &[F128]) -> F128 {
    let mut w = Wide4::zero();
    let mut i = 0;
    while i < a.len() {
        w.mac(ld_z(a.as_ptr().add(i)), ld_z(b.as_ptr().add(i)));
        i += 4;
    }
    w.reduce_sum()
}

// ---- latency chain
fn lat_portable(x: F128, y: F128, n: usize) -> F128 {
    let mut x = x;
    for _ in 0..n {
        x = mul_portable(x, y);
    }
    x
}
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn lat_pclmul(x: F128, y: F128, n: usize) -> F128 {
    let mut x = x;
    for _ in 0..n {
        x = mul_pclmul(x, y);
    }
    x
}
#[target_feature(enable = "pclmulqdq,sse4.1")]
unsafe fn lat_xmm(x: F128, y: F128, n: usize) -> F128 {
    let (mut x, y) = (to_x(x), to_x(y));
    for _ in 0..n {
        x = mul_xmm(x, y);
    }
    from_x(x)
}

// ---- K = GF(2^256) arithmetic
/// c[i] (K) = a[i] (K) * b[i] (F): Ligerito column folds / sumcheck folds of F-vectors by K.
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn kf_ymm(a: &[F128], b: &[F128], c: &mut [F128]) {
    for i in 0..b.len() {
        st_y(c.as_mut_ptr().add(2 * i), mul_y(ld_y(a.as_ptr().add(2 * i)), bcast_y(b[i])));
    }
}
#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn kk_ymm(a: &[F128], b: &[F128], c: &mut [F128]) {
    let mut i = 0;
    while i < a.len() {
        let (p, q) = k_mul2(
            ld_y(a.as_ptr().add(i)),
            ld_y(b.as_ptr().add(i)),
            ld_y(a.as_ptr().add(i + 2)),
            ld_y(b.as_ptr().add(i + 2)),
        );
        st_y(c.as_mut_ptr().add(i), p);
        st_y(c.as_mut_ptr().add(i + 2), q);
        i += 4;
    }
}

pub fn bench_gf(c: Cpu, threads: &[usize]) {
    let reps = if quick() { 20 } else { 2000 }; // N * reps products per run
    for &t in threads {
        let run = |name: &str, f: &(dyn Fn(&[F128], &[F128], &mut [F128]) + Sync), per: usize| {
            let secs = par_best(t, 3, |tid| {
                let mut rng = Rng(77 + tid as u64);
                let a = rng.fvec(N);
                let b = rng.fvec(N);
                let mut cc = vec![F128::ZERO; N];
                for _ in 0..reps {
                    f(&a, &b, &mut cc);
                    black_box(&mut cc);
                }
            });
            report("gf128-mul", name, t, "batch4096", (t * reps * N / per) as f64, secs, "product");
        };
        if !c.pclmul {
            run("portable(4-bit window)", &|a, b, cc| batch_portable(a, b, cc), 1);
        }
        if c.pclmul {
            run("pclmul-scalar-karatsuba(Flock x86 Mul)", &|a, b, cc| unsafe { batch_pclmul(a, b, cc) }, 1);
            run("pclmul-xmm-schoolbook", &|a, b, cc| unsafe { batch_xmm(a, b, cc) }, 1);
        }
        if c.ymm {
            run("ymm-vpclmul-schoolbook(2/insn)", &|a, b, cc| unsafe { batch_ymm(a, b, cc) }, 1);
            run("ymm-vpclmul-karatsuba", &|a, b, cc| unsafe { batch_ymm_kara(a, b, cc) }, 1);
            run("ymm-vpclmul-schoolbook-by-const", &|a, b, cc| unsafe { bconst_ymm(a, b[0], cc) }, 1);
            run("ymm-vpclmul-karatsuba-by-const", &|a, b, cc| unsafe { bconst_ymm_kara(a, b[0], cc) }, 1);
            // K arithmetic: a,b as N/2 K-elements
            let secs = par_best(t, 3, |tid| {
                let mut rng = Rng(9 + tid as u64);
                let a = rng.fvec(N);
                let b = rng.fvec(N / 2);
                let mut cc = vec![F128::ZERO; N];
                for _ in 0..reps {
                    unsafe { kf_ymm(&a, &b, &mut cc) };
                    black_box(&mut cc);
                }
            });
            report("gf256-mul", "KxF ymm (1 ymm product)", t, "batch2048", (t * reps * N / 2) as f64, secs, "product");
            run("KxK ymm (3 ymm products per 2)", &|a, b, cc| unsafe { kk_ymm(a, b, cc) }, 2);
        }
        if c.zmm {
            run("zmm-vpclmul-schoolbook(4/insn, Flock ghash_mul_x4)", &|a, b, cc| unsafe { batch_zmm(a, b, cc) }, 1);
        }
        // MAC
        let runm = |name: &str, f: &(dyn Fn(&[F128], &[F128]) -> F128 + Sync)| {
            let secs = par_best(t, 3, |tid| {
                let mut rng = Rng(5 + tid as u64);
                let a = rng.fvec(N);
                let b = rng.fvec(N);
                for _ in 0..reps {
                    black_box(f(&a, &b));
                }
            });
            report("gf128-mac", name, t, "batch4096", (t * reps * N) as f64, secs, "product");
        };
        if c.pclmul {
            runm("pclmul-scalar-unreduced(Flock F256Unreduced)", &|a, b| unsafe { mac_pclmul(a, b) });
            runm("pclmul-xmm-wide", &|a, b| unsafe { mac_xmm(a, b) });
        }
        if c.ymm {
            runm("ymm-vpclmul-wide", &|a, b| unsafe { mac_ymm(a, b) });
        }
        if c.zmm {
            runm("zmm-vpclmul-wide(Flock WideGhashX4)", &|a, b| unsafe { mac_zmm(a, b) });
        }
    }
    // latency (1 thread)
    let n = if quick() { 100_000 } else { 4_000_000 };
    let mut rng = Rng(3);
    let (x, y) = (rng.f(), rng.f());
    if c.pclmul {
        let s = crate::best(3, || {
            black_box(unsafe { lat_pclmul(black_box(x), y, n) });
        });
        report("gf128-mul-latency", "pclmul-scalar-karatsuba", 1, "chain", n as f64, s, "product");
        let s = crate::best(3, || {
            black_box(unsafe { lat_xmm(black_box(x), y, n) });
        });
        report("gf128-mul-latency", "pclmul-xmm-schoolbook", 1, "chain", n as f64, s, "product");
    } else {
        let s = crate::best(3, || {
            black_box(lat_portable(black_box(x), y, n / 10));
        });
        report("gf128-mul-latency", "portable", 1, "chain", (n / 10) as f64, s, "product");
    }
}

#[target_feature(enable = "avx2")]
unsafe fn copy_avx2(src: &[u8], dst: &mut [u8]) {
    let mut i = 0;
    while i < src.len() {
        let v0 = _mm256_loadu_si256(src.as_ptr().add(i) as *const __m256i);
        let v1 = _mm256_loadu_si256(src.as_ptr().add(i + 32) as *const __m256i);
        _mm256_storeu_si256(dst.as_mut_ptr().add(i) as *mut __m256i, v0);
        _mm256_storeu_si256(dst.as_mut_ptr().add(i + 32) as *mut __m256i, v1);
        i += 64;
    }
}

/// Streaming copy and read bandwidth on 256 MiB per thread pair of buffers (DRAM-bound).
pub fn bench_mem(threads: &[usize]) {
    let n: usize = if quick() { 16 << 20 } else { 256 << 20 };
    for &t in threads {
        let per = n / t;
        let src: Vec<Vec<u8>> = (0..t).map(|i| vec![i as u8 + 1; per]).collect();
        let mut dst: Vec<Vec<u8>> = (0..t).map(|_| vec![0u8; per]).collect();
        let dp: Vec<crate::SyncPtr<u8>> = dst.iter_mut().map(|d| crate::SyncPtr(d.as_mut_ptr())).collect();
        let secs = par_best(t, 3, |tid| {
            let d = unsafe { std::slice::from_raw_parts_mut(dp[tid].0, per) };
            unsafe { copy_avx2(&src[tid], d) };
        });
        report("mem", "copy (read+write bytes)", t, &format!("{}MiB", n >> 20), (2 * n) as f64, secs, "byte");
        let secs = par_best(t, 3, |tid| {
            let mut s = 0u64;
            for c in src[tid].chunks_exact(64) {
                s = s.wrapping_add(u64::from_le_bytes(c[..8].try_into().unwrap()) ^ u64::from_le_bytes(c[32..40].try_into().unwrap()));
            }
            black_box(s);
        });
        report("mem", "read (64B lines touched)", t, &format!("{}MiB", n >> 20), n as f64, secs, "byte");
        black_box(&dst);
    }
}
