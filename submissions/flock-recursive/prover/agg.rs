//! The aggregate leaf `A` (revision 4.0, B-11): a chain of `n` steps as `k = ⌈n/2^(M−14)⌉` segment
//! proofs in sequence, the first `k − 1` full (`2^(M−14)` steps, shape `M`), the last the remainder
//! `r`, in the smallest of `L30`, `L31`, `L32` that holds it (revision 4.1, S-0′ §6). `π_A = hdr_A ‖ π_1 ‖ … ‖
//! π_k`; the verifier runs the `k` segment verifiers in sequence on one oracle (one signed trace
//! `tr_A = tr_1 ‖ … ‖ tr_k`) and checks the chaining `s_{i+1} = h_i`, `c = leafStmt h_k (Σ n_i)`.
//!
//! **Format** (`FRAgg.aggHdr`, `aggChecks`, `VAwith`, `FRSegment.segView`; revision 4.1):
//! `hdr_A = 0x41 ‖ k ‖ 0^6 ‖ enc64 n ‖ e`; a segment's view is its kind byte, start (`hdr` bytes
//! 16–47), end and length (`stmt` bytes 1–32, 33–40). `V_A` checks first: `c = leafStmt e n`,
//! `1 ≤ k ≤ 4`, `1 ≤ n_i ≤ cap(kind_i)`, `Σ n_i = n`, the last end `= e`, `s_{i+1} = e_i`; then runs
//! the segment verifiers in sequence (none when a check fails), stopping at the first rejection
//! (`seqAll`). `ir::run_agg` is the same `V_A` over the dumped Lean segment programs.

use crate::blake2s::{leaf_stmt, Digest};
use crate::circuit::Circuit;
use crate::leaf::{self, Times};
use crate::oracle::Oracle;
use crate::params as pp;

pub const KIND_AGG: u8 = 0x41;
pub const HDR_A: usize = 48;
/// The largest segment shape of a step (`L32`).
pub const M_SEG: usize = 32;

/// The segments `(m_i, s_i-independent n_i)` of a chain of `n` steps with largest shape `mmax`.
pub fn split(n: u64, mmax: usize) -> Vec<(usize, u64)> {
    assert!(n >= 1);
    let full = pp::leaf_n(mmax);
    let k = n.div_ceil(full);
    let mut v: Vec<(usize, u64)> = (1..k).map(|_| (mmax, full)).collect();
    let r = n - (k - 1) * full;
    // the remainder in the smallest kind that holds it: `L30` (`≤ 2^16`), `L31` (`≤ 2^17`) or `L32`
    // (S-0′ §6); test shapes below `m = 30` use `mmax − 1` or `mmax`
    let lo = if mmax >= 30 { 30.max(mmax - 2) } else { mmax - 1 };
    let mr = (lo..=mmax).find(|&m| r <= pp::leaf_n(m)).unwrap();
    v.push((mr, r));
    v
}

/// The aggregate prover: `π_A` and each segment's phase times. Segment `i` starts at the end of
/// segment `i − 1`. The segments are proved one after another, each on every thread.
pub fn prove(o: &dyn Oracle, circ: &Circuit, vk: &Digest, s: &Digest, n: u64, mmax: usize) -> (Vec<u8>, Vec<Times>) {
    let segs = split(n, mmax);
    let mut pi = vec![0u8; HDR_A];
    pi[0] = KIND_AGG;
    pi[1] = segs.len() as u8;
    pi[8..16].copy_from_slice(&n.to_le_bytes());
    let mut tms = Vec::new();
    let mut start = *s;
    for &(m, ni) in &segs {
        let (p, tm) = leaf::prove_seg(o, circ, vk, &start, m, ni);
        start = seg_end(&p);
        pi.extend_from_slice(&p);
        tms.push(tm);
    }
    pi[16..48].copy_from_slice(&start);
    (pi, tms)
}

/// A segment proof's end `h` and length `n` (its statement field).
fn seg_stmt(p: &[u8]) -> (Digest, u64) {
    let o = pp::field_off(pp::F_STMT);
    (p[o + 1..o + 33].try_into().unwrap(), u64::from_le_bytes(p[o + 33..o + 41].try_into().unwrap()))
}

fn seg_end(p: &[u8]) -> Digest {
    seg_stmt(p).0
}

/// `V_A vk c π_A` (S-0′'s draft `VAwith`): the checks on the segments' views, then every segment
/// verifier in sequence (each asks its items whatever its result). A `π_A` of the wrong shape or
/// failing a check is rejected with no query.
pub fn verify(o: &dyn Oracle, circ: &Circuit, vk: &Digest, c: &Digest, pi: &[u8]) -> bool {
    if pi.len() < HDR_A || pi[0] != KIND_AGG {
        return false;
    }
    let k = pi[1] as usize;
    // `hdr_A`'s bytes 2–7 zero: R-4-m5 (HEAD's `VAwith` does not read them; the fix in progress
    // adds the check). The prover writes zeros, so its proofs pass both forms.
    if pi.len() != HDR_A + k * pp::PI_SIZE || pi[2..8].iter().any(|&x| x != 0) || !(1..=4).contains(&k) {
        return false;
    }
    let n = u64::from_le_bytes(pi[8..16].try_into().unwrap());
    let e: Digest = pi[16..48].try_into().unwrap();
    let segs: Vec<&[u8]> = (0..k).map(|i| &pi[HDR_A + i * pp::PI_SIZE..HDR_A + (i + 1) * pp::PI_SIZE]).collect();
    let mut total = 0u64;
    let mut prev: Option<Digest> = None;
    let mut ok = *c == leaf_stmt(&e, n);
    for p in &segs {
        let cap = match p[0] {
            pp::KIND_LEAF => pp::leaf_n(32),
            pp::KIND_L31 => pp::leaf_n(31),
            pp::KIND_P30 => pp::leaf_n(p[1] as usize), // native test shapes
            _ => return false,
        };
        let (h, ni) = seg_stmt(p);
        let si: Digest = p[16..48].try_into().unwrap();
        ok &= (1..=cap).contains(&ni) && prev.is_none_or(|e| si == e);
        prev = Some(h);
        total = total.saturating_add(ni);
    }
    if !(ok && total == n && prev == Some(e)) {
        return false;
    }
    // `seqAll`: in order, stopping at the first rejection
    segs.iter().all(|p| {
        let (h, ni) = seg_stmt(p);
        leaf::verify(o, circ, vk, &leaf_stmt(&h, ni), p)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::{Local, Recorder, Replay, Seq};

    #[test]
    fn split_rule() {
        assert_eq!(split(1 << 17, 32), vec![(31, 1 << 17)]);
        assert_eq!(split((1 << 17) + 1, 32), vec![(32, (1 << 17) + 1)]);
        assert_eq!(split(1 << 18, 32), vec![(32, 1 << 18)]);
        assert_eq!(split((1 << 18) + 5, 32), vec![(32, 1 << 18), (30, 5)]);
        assert_eq!(split(1 << 16, 32), vec![(30, 1 << 16)]);
        assert_eq!(split((1 << 16) + 1, 32), vec![(31, (1 << 16) + 1)]);
        assert_eq!(split((1 << 18) + (1 << 17), 32), vec![(32, 1 << 18), (31, 1 << 17)]);
        assert_eq!(split((1 << 16) + 3, 30), vec![(30, 1 << 16), (30, 3)]);
        assert_eq!(split(1 << 20, 32), vec![(32, 1 << 18); 4]);
        assert_eq!(split(3 << 18 | 1 << 17 | 1, 32), vec![(32, 1 << 18), (32, 1 << 18), (32, 1 << 18), (32, (1 << 17) + 1)]);
    }

    /// Small shapes (`mmax = 26`: segments of `2^12` steps, the remainder in `m = 25` when `≤ 2^11`):
    /// `V_A` accepts, through the recorded trace as `acc` runs it (one `Seq` over `tr_A`, consumed
    /// exactly), and rejects a wrong `n`, a flipped end, a broken link and a flipped segment byte.
    #[test]
    fn aggregate_roundtrip() {
        let circ = Circuit::build();
        let base = Local::keyed(&[0x44u8; 32]);
        let (vk, s) = ([6u8; 32], [0x17u8; 32]);
        for n in [3000u64, 4096, 4096 + 7, 2 * 4096 + 3000] {
            let rec = Recorder::new(&base);
            let (pi, _) = prove(&rec, &circ, &vk, &s, n, 26);
            let c = leaf::seg_c(&s, n);
            let table = rec.into_table();
            let mut rp = Replay::new(&table);
            rp.fallback = Some(&base);
            assert!(verify(&rp, &circ, &vk, &c, &pi), "n = {n}");
            let (tr, missing) = rp.finish();
            assert_eq!(missing, 0);
            let seq = Seq::new(&tr);
            assert!(verify(&seq, &circ, &vk, &c, &pi) && seq.consumed());
            assert!(!verify(&base, &circ, &vk, &leaf::seg_c(&s, n + 1), &pi));
            let mut c2 = c;
            c2[0] ^= 1;
            assert!(!verify(&base, &circ, &vk, &c2, &pi));
            let mut p2 = pi.clone();
            p2[HDR_A + pp::PI_SIZE / 2] ^= 8;
            assert!(!verify(&base, &circ, &vk, &c, &p2));
            let mut p4 = pi.clone();
            p4[8] ^= 1; // hdr_A's n
            assert!(!verify(&base, &circ, &vk, &c, &p4));
            if pi[1] > 1 {
                let mut p3 = pi.clone();
                p3[HDR_A + pp::PI_SIZE + 20] ^= 1; // segment 2's start
                assert!(!verify(&base, &circ, &vk, &c, &p3));
            }
        }
    }
}
