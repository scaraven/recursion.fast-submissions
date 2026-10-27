//! Lincheck prover's per-witness-bit work (Flock `lincheck.rs`): the partial fold of z over the
//! outer (batch) variables, `out[i_inner] = sum_outer eq(r_outer, outer) * z(i_inner, outer)`, by
//! 256-entry sum tables per 8-row stripe (`partial_fold_packed_z_fast`), after packing z into the
//! stripe layout (`pack_z_lincheck`: byte = 8 outer rows of one inner position, by 8x8 bit
//! transposes). Also a sparse gather-XOR (the O(nnz) matrix-fold alternative to a circuit walk).
use crate::gf::*;
use crate::sumcheck::transpose8x8;
use crate::{par_for, quick, report, Rng};
use std::hint::black_box;

const KLOG: usize = 14; // 2^14 witness bits per BLAKE2s compression
const K: usize = 1 << KLOG;
const KB: usize = K / 8; // bytes per compression

/// z: compressions x KB bytes (row-major). Output: stripes x K bytes.
pub fn pack(z: &[u8], out: &mut [u8], threads: usize) {
    let n = z.len() / KB;
    let stripes = n / 8;
    let op = crate::SyncPtr(out.as_mut_ptr());
    par_for(threads, stripes, |s| {
        let op = op;
        let o = unsafe { std::slice::from_raw_parts_mut(op.0.add(s * K), K) };
        for j in 0..KB {
            let mut x = 0u64;
            for r in 0..8 {
                x |= (z[(8 * s + r) * KB + j] as u64) << (8 * r);
            }
            o[8 * j..8 * j + 8].copy_from_slice(&transpose8x8(x).to_le_bytes());
        }
    });
}

fn sum_table(eq8: &[F128], t: &mut [F128; 256]) {
    t[0] = F128::ZERO;
    for i in 0..8 {
        let h = 1 << i;
        for j in 0..h {
            t[h + j] = t[j] + eq8[i];
        }
    }
}

pub fn partial_fold(zp: &[u8], eq: &[F128], threads: usize) -> Vec<F128> {
    let stripes = zp.len() / K;
    let per = stripes.div_ceil(threads);
    let parts: Vec<std::sync::Mutex<Vec<F128>>> = (0..threads).map(|_| std::sync::Mutex::new(vec![])).collect();
    par_for(threads, threads, |w| {
        let mut acc = vec![F128::ZERO; K];
        let mut t = [F128::ZERO; 256];
        for s in w * per..((w + 1) * per).min(stripes) {
            sum_table(&eq[8 * s..8 * s + 8], &mut t);
            let st = &zp[s * K..(s + 1) * K];
            for i in 0..K {
                acc[i] += t[st[i] as usize];
            }
        }
        *parts[w].lock().unwrap() = acc;
    });
    let mut out = vec![F128::ZERO; K];
    for p in parts {
        let p = p.into_inner().unwrap();
        for i in 0..p.len() {
            out[i] += p[i];
        }
    }
    out
}

pub fn selftest(_c: Cpu, rng: &mut Rng) -> Result<(), String> {
    let n = 32;
    let z = rng.bytes(n * KB);
    let eq = rng.fvec(n);
    let mut zp = vec![0u8; n * KB];
    pack(&z, &mut zp, 3);
    let got = partial_fold(&zp, &eq, 3);
    for &i in &[0usize, 1, 77, 8191, K - 1] {
        let mut s = F128::ZERO;
        for o in 0..n {
            if (z[o * KB + i / 8] >> (i % 8)) & 1 == 1 {
                s += eq[o];
            }
        }
        if s != got[i] {
            return Err(format!("partial fold mismatch at {i}"));
        }
    }
    Ok(())
}

pub fn bench(_c: Cpu, threads: &[usize]) {
    let mut rng = Rng(51);
    let n = if quick() { 64 } else { 2048 }; // compressions
    let z = rng.bytes(n * KB);
    let eq = rng.fvec(n);
    let mut zp = vec![0u8; n * KB];
    for &th in threads {
        let secs = crate::best(3, || pack(&z, &mut zp, th));
        report("lincheck-pack-z(8x8 transposes)", "scalar", th, &format!("{n} compressions"), n as f64, secs, "compression");
        let secs = crate::best(3, || {
            black_box(partial_fold(&zp, &eq, th));
        });
        report("lincheck-partial-fold(sum tables)", "scalar(Flock port)", th, &format!("{n} compressions"), n as f64, secs, "compression");
    }
    // sparse gather-XOR from a 2^14-entry eq table (L2-resident)
    let nnz = if quick() { 1 << 18 } else { 1 << 24 };
    let tab = rng.fvec(K);
    let idx: Vec<u16> = (0..nnz).map(|_| (rng.u64() as u16) & (K as u16 - 1)).collect();
    for &th in threads {
        let per = nnz / th;
        let secs = crate::best(3, || {
            par_for(th, th, |w| {
                let mut acc = [F128::ZERO; 4];
                for (j, &i) in idx[w * per..(w + 1) * per].iter().enumerate() {
                    acc[j & 3] += tab[i as usize];
                }
                black_box(acc);
            });
        });
        report("sparse-gather-xor(matrix fold per nnz)", "scalar", th, "table 2^14", nnz as f64, secs, "nnz");
    }
}
