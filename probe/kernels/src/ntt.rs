//! Additive NTT over GF(2^128) in the LCH novel basis, interleaved (SoA) layout
//! `data[pos * lanes + lane]`, as Flock's Ligerito encoder uses it
//! (`crates/flock-core/src/ntt/additive_ntt_f128.rs`: subspace basis {1, x, .., x^(l-1)},
//! normalised subspace polynomials, neighbours-last layers, rate-1/2 encode = replicate the
//! message and start at layer 1). Passes fuse 1-3 layers (radix-2/4/8 row groups); top layers
//! stream the whole buffer, deep layers run block by block in L2.
use crate::gf::*;
use crate::{par_for, quick, report, Rng, SyncPtr};

pub struct Ntt {
    pub log_d: usize,
    pub tw: Vec<Vec<F128>>, // tw[layer][block]
    pub cache_log: Option<usize>,
}

impl Ntt {
    pub fn new(log_d: usize) -> Ntt {
        assert!(log_d <= 64);
        let basis: Vec<F128> = (0..log_d).map(|i| F128::new(1u64 << i, 0)).collect();
        let mut evals: Vec<Vec<F128>> = vec![basis];
        for i in 1..log_d {
            let prev = &evals[i - 1];
            let row: Vec<F128> = (1..prev.len()).map(|k| mul(prev[k], prev[k] + prev[0])).collect();
            evals.push(row);
        }
        for row in evals.iter_mut() {
            let inv = inv_portable(row[0]);
            for v in row.iter_mut() {
                *v = mul(*v, inv);
            }
        }
        let mut tw = vec![];
        for l in 0..log_d {
            let v = &evals[log_d - l - 1][1..];
            let mut t = vec![F128::ZERO; 1 << l];
            for b in 1..(1usize << l) {
                let low = b & b.wrapping_neg();
                t[b] = t[b ^ low] + v[low.trailing_zeros() as usize];
            }
            tw.push(t);
        }
        Ntt { log_d, tw, cache_log: None }
    }

    fn tws(&self, layer: usize, block: usize, nl: usize) -> [F128; 7] {
        let mut t = [F128::ZERO; 7];
        t[0] = self.tw[layer][block];
        if nl >= 2 {
            t[1] = self.tw[layer + 1][2 * block];
            t[2] = self.tw[layer + 1][2 * block + 1];
        }
        if nl >= 3 {
            for q in 0..4 {
                t[3 + q] = self.tw[layer + 2][4 * block + q];
            }
        }
        t
    }

    /// Flock's `interleaved_scalar_live_from_layer` (the reference), portable product.
    pub fn forward_reference(&self, data: &mut [F128], lanes: usize, start_layer: usize) {
        let log_d = self.log_d;
        for layer in start_layer..log_d {
            let half = 1usize << (log_d - layer - 1);
            for block in 0..(1usize << layer) {
                let t = self.tw[layer][block];
                let bs = block * 2 * half * lanes;
                for row in 0..half {
                    let (ot, ob) = (bs + row * lanes, bs + (row + half) * lanes);
                    for lane in 0..lanes {
                        let v = data[ob + lane];
                        let nu = data[ot + lane] + mul_portable(v, t);
                        data[ot + lane] = nu;
                        data[ob + lane] = v + nu;
                    }
                }
            }
        }
    }

    /// Forward transform from `start_layer` with the given kernel; `max_nl` caps the fused depth.
    pub fn forward(&self, data: &mut [F128], lanes: usize, start_layer: usize, kern: Kern, threads: usize) {
        let log_d = self.log_d;
        assert_eq!(data.len(), lanes << log_d);
        let max_nl = kern.max_nl();
        let row_bytes = lanes * 16;
        let log_c = self.cache_log.unwrap_or(((256 << 10) / row_bytes).max(8).trailing_zeros() as usize); // block rows in L2
        let p = SyncPtr(data.as_mut_ptr());
        let mut l = start_layer;
        // top phase: whole-buffer passes
        while log_d - l > log_c {
            let nl = max_nl.min(log_d - l - log_c);
            let s = 1usize << (log_d - l);
            let sub = s >> nl;
            let items = (1usize << l) * sub;
            let chunk = 16usize.min(items);
            par_for(threads, items / chunk, |ci| {
                let p = p;
                for it in ci * chunk..(ci + 1) * chunk {
                    let (b, r) = (it / sub, it % sub);
                    let tw = self.tws(l, b, nl);
                    unsafe { group(kern, nl, p.0, b * s + r, sub, lanes, &tw) };
                }
            });
            l += nl;
        }
        // deep phase: each block of 2^(log_d - l) rows to completion
        let l0 = l;
        let nblocks = 1usize << l0;
        par_for(threads, nblocks, |b0| {
            let p = p;
            let mut ll = l0;
            while ll < log_d {
                let nl = max_nl.min(log_d - ll);
                let s = 1usize << (log_d - ll);
                let sub = s >> nl;
                for sb in 0..(1usize << (ll - l0)) {
                    let b = (b0 << (ll - l0)) + sb;
                    let tw = self.tws(ll, b, nl);
                    for r in 0..sub {
                        unsafe { group(kern, nl, p.0, b * s + r, sub, lanes, &tw) };
                    }
                }
                ll += nl;
            }
        });
    }

    /// Rate-1/2 RS encode: replicate the message (layer 0 is a copy) and transform from layer 1.
    pub fn encode_half(&self, msg: &[F128], out: &mut [F128], lanes: usize, kern: Kern, threads: usize) {
        let h = msg.len();
        assert_eq!(out.len(), 2 * h);
        let po = SyncPtr(out.as_mut_ptr());
        let chunk = 1 << 16;
        par_for(threads, (2 * h).div_ceil(chunk), |c| {
            let po = po;
            let (s, e) = (c * chunk, ((c + 1) * chunk).min(2 * h));
            let o = unsafe { std::slice::from_raw_parts_mut(po.0.add(s), e - s) };
            for (k, x) in o.iter_mut().enumerate() {
                *x = msg[(s + k) % h];
            }
        });
        self.forward(out, lanes, 1, kern, threads);
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kern {
    /// Flock's Zen-3 path: fused-2 layer groups, one scalar product per lane (portable or pclmul)
    ScalarR4(Tier),
    YmmR4Kara,
    YmmR8Kara,
    YmmR8School,
    ZmmR8,
}
impl Kern {
    fn max_nl(self) -> usize {
        match self {
            Kern::ScalarR4(_) | Kern::YmmR4Kara => 2,
            _ => 3,
        }
    }
    pub fn name(self) -> String {
        match self {
            Kern::ScalarR4(t) => format!("scalar-{}-radix4(Flock Zen3 path)", t.name()),
            Kern::YmmR4Kara => "ymm-vpclmul-radix4-karatsuba".into(),
            Kern::YmmR8Kara => "ymm-vpclmul-radix8-karatsuba".into(),
            Kern::YmmR8School => "ymm-vpclmul-radix8-schoolbook".into(),
            Kern::ZmmR8 => "zmm-vpclmul-radix8(Flock AVX-512 path)".into(),
        }
    }
    pub fn all(c: Cpu) -> Vec<Kern> {
        let mut v = vec![];
        if c.pclmul {
            v.push(Kern::ScalarR4(Tier::Pclmul));
        } else {
            v.push(Kern::ScalarR4(Tier::Portable));
        }
        if c.ymm {
            v.extend([Kern::YmmR4Kara, Kern::YmmR8Kara, Kern::YmmR8School]);
        }
        if c.zmm {
            v.push(Kern::ZmmR8);
        }
        v
    }
}

unsafe fn group(kern: Kern, nl: usize, p: *mut F128, row0: usize, stride: usize, lanes: usize, tw: &[F128; 7]) {
    match kern {
        Kern::ScalarR4(Tier::Pclmul) => match nl {
            1 => grp_s_pclmul::<1>(p, row0, stride, lanes, tw),
            _ => grp_s_pclmul::<2>(p, row0, stride, lanes, tw),
        },
        Kern::ScalarR4(_) => match nl {
            1 => grp_s_portable::<1>(p, row0, stride, lanes, tw),
            _ => grp_s_portable::<2>(p, row0, stride, lanes, tw),
        },
        Kern::YmmR4Kara | Kern::YmmR8Kara => match nl {
            1 => grp_y::<1, true>(p, row0, stride, lanes, tw),
            2 => grp_y::<2, true>(p, row0, stride, lanes, tw),
            _ => grp_y::<3, true>(p, row0, stride, lanes, tw),
        },
        Kern::YmmR8School => match nl {
            1 => grp_y::<1, false>(p, row0, stride, lanes, tw),
            2 => grp_y::<2, false>(p, row0, stride, lanes, tw),
            _ => grp_y::<3, false>(p, row0, stride, lanes, tw),
        },
        Kern::ZmmR8 => match nl {
            1 => grp_z::<1>(p, row0, stride, lanes, tw),
            2 => grp_z::<2>(p, row0, stride, lanes, tw),
            _ => grp_z::<3>(p, row0, stride, lanes, tw),
        },
    }
}

/// The butterfly schedule of a group of 2^NL rows (Flock's fused_2layer / fused_3layer order):
/// (u, w, twiddle index).
const fn sched(nl: usize) -> &'static [(usize, usize, usize)] {
    match nl {
        1 => &[(0, 1, 0)],
        2 => &[(0, 2, 0), (1, 3, 0), (0, 1, 1), (2, 3, 2)],
        _ => &[
            (0, 4, 0),
            (1, 5, 0),
            (2, 6, 0),
            (3, 7, 0),
            (0, 2, 1),
            (1, 3, 1),
            (4, 6, 2),
            (5, 7, 2),
            (0, 1, 3),
            (2, 3, 4),
            (4, 5, 5),
            (6, 7, 6),
        ],
    }
}

macro_rules! scalar_group {
    ($name:ident, $feat:literal, $mul:expr) => {
        #[target_feature(enable = $feat)]
        unsafe fn $name<const NL: usize>(p: *mut F128, row0: usize, stride: usize, lanes: usize, tw: &[F128; 7]) {
            let n = 1usize << NL;
            for lane in 0..lanes {
                let mut v = [F128::ZERO; 4];
                for j in 0..n {
                    v[j] = *p.add((row0 + j * stride) * lanes + lane);
                }
                for &(u, w, t) in sched(NL) {
                    let nu = v[u] + $mul(v[w], tw[t]);
                    v[w] = v[w] + nu;
                    v[u] = nu;
                }
                for j in 0..n {
                    *p.add((row0 + j * stride) * lanes + lane) = v[j];
                }
            }
        }
    };
}
scalar_group!(grp_s_pclmul, "pclmulqdq,sse4.1", |a, b| mul_pclmul(a, b));
scalar_group!(grp_s_portable, "sse2", |a, b| mul_portable(a, b));

#[target_feature(enable = "avx2,vpclmulqdq,pclmulqdq")]
unsafe fn grp_y<const NL: usize, const KARA: bool>(
    p: *mut F128,
    row0: usize,
    stride: usize,
    lanes: usize,
    tw: &[F128; 7],
) {
    use std::arch::x86_64::*;
    let n = 1usize << NL;
    let mut t = [_mm256_setzero_si256(); 7];
    let mut tk = [_mm256_setzero_si256(); 7];
    for i in 0..n - 1 {
        t[i] = bcast_y(tw[i]);
        tk[i] = kara_pre_y(t[i]);
    }
    let mut lane = 0;
    while lane < lanes {
        let mut v = [_mm256_setzero_si256(); 8];
        for j in 0..n {
            v[j] = ld_y(p.add((row0 + j * stride) * lanes + lane));
        }
        for &(u, w, ti) in sched(NL) {
            let prod = if KARA { mul_y_kara(v[w], t[ti], tk[ti]) } else { mul_y(v[w], t[ti]) };
            let nu = _mm256_xor_si256(v[u], prod);
            v[w] = _mm256_xor_si256(v[w], nu);
            v[u] = nu;
        }
        for j in 0..n {
            st_y(p.add((row0 + j * stride) * lanes + lane), v[j]);
        }
        lane += 2;
    }
}

#[target_feature(enable = "avx512f,avx512bw,vpclmulqdq")]
unsafe fn grp_z<const NL: usize>(p: *mut F128, row0: usize, stride: usize, lanes: usize, tw: &[F128; 7]) {
    use std::arch::x86_64::*;
    let n = 1usize << NL;
    let mut t = [_mm512_setzero_si512(); 7];
    for i in 0..n - 1 {
        t[i] = bcast_z(tw[i]);
    }
    let mut lane = 0;
    while lane < lanes {
        let mut v = [_mm512_setzero_si512(); 8];
        for j in 0..n {
            v[j] = ld_z(p.add((row0 + j * stride) * lanes + lane));
        }
        for &(u, w, ti) in sched(NL) {
            let nu = _mm512_xor_si512(v[u], mul_z(v[w], t[ti]));
            v[w] = _mm512_xor_si512(v[w], nu);
            v[u] = nu;
        }
        for j in 0..n {
            st_z(p.add((row0 + j * stride) * lanes + lane), v[j]);
        }
        lane += 4;
    }
}

pub fn selftest(c: Cpu, rng: &mut Rng) -> Result<(), String> {
    for &(log_d, lanes) in &[(9usize, 8usize), (11, 4), (6, 64)] {
        let mut ntt = Ntt::new(log_d);
        let msg = rng.fvec(lanes << (log_d - 1));
        // reference: zero-padded message from layer 0
        let mut r = msg.clone();
        r.resize(lanes << log_d, F128::ZERO);
        ntt.forward_reference(&mut r, lanes, 0);
        // replicate trick, reference kernel
        let mut r2 = [msg.clone(), msg.clone()].concat();
        ntt.forward_reference(&mut r2, lanes, 1);
        if r != r2 {
            return Err("replicate-from-layer-1 != zero-padded transform".into());
        }
        for k in Kern::all(c) {
            for (th, cl) in [(1, None), (3, None), (1, Some(3)), (3, Some(4))] {
                ntt.cache_log = cl;
                let mut o = vec![F128::ZERO; lanes << log_d];
                ntt.encode_half(&msg, &mut o, lanes, k, th);
                if o != r {
                    return Err(format!("{} mismatch at log_d={log_d} lanes={lanes} threads={th}", k.name()));
                }
            }
        }
    }
    Ok(())
}

pub fn bench(c: Cpu, threads: &[usize]) {
    let shapes: Vec<(usize, usize)> = if quick() {
        vec![(64, 10), (64, 12)]
    } else {
        // codeword length per lane 2^n with 64 lanes (Ligerito level 0 at m = 30/31/32 is n = 18/19/20)
        // and 16 lanes (levels >= 1)
        vec![(64, 10), (64, 12), (64, 14), (64, 16), (64, 18), (64, 19), (64, 20), (16, 16), (16, 20), (16, 22)]
    };
    let mut rng = Rng(42);
    for &(lanes, log_d) in &shapes {
        let ntt = Ntt::new(log_d);
        let msg = rng.fvec(lanes << (log_d - 1));
        let mut out = vec![F128::ZERO; lanes << log_d];
        let bfly = (lanes as f64) * ((log_d - 1) as f64) * ((1usize << (log_d - 1)) as f64);
        let trials = if log_d >= 18 { 2 } else { 3 };
        for k in Kern::all(c) {
            for &t in threads {
                if matches!(k, Kern::ScalarR4(Tier::Portable)) && log_d > 14 {
                    continue;
                }
                let secs = crate::best(trials, || ntt.encode_half(&msg, &mut out, lanes, k, t));
                let param = format!("lanes={lanes},n=2^{log_d},total=2^{}", log_d + lanes.trailing_zeros() as usize);
                report("ntt-rs-encode-rate1/2", &k.name(), t, &param, bfly, secs, "butterfly");
                println!("  encode wall {:.4} s; per message element {:.3} ns", secs, secs * 1e9 / msg.len() as f64);
            }
        }
    }
}
