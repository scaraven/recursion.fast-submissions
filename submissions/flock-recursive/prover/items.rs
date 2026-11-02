//! The item sequence of A.4 as a static list (`FRTranscriptDefs.items`, sized by `m* = 32`), and
//! `reassemble tr : π` (A.5): a child's proof from its trace, as the node prover will read it.
//!
//! `reassemble`: `hdr` from the seed's payload bytes 64…111; `stmt` from item 1's payload; every
//! absorb's payload into its A.3 field in item order (rows 2–11, the caps from `cap₀` and `C.0 …
//! C.3`, the final message from `C.4`); the columns from the column queries in order; for the
//! Merkle-node query at depth `h` of index `j` of level `i`, the sibling is the half whose position
//! is not bit `h` of `j` (`j` read from `P2.i`'s answers by `idxOf` with the kind's `log₂ nᵢ`),
//! dummies (`0^64`) copied as zeros.

use crate::blake2s::Digest;
use crate::params::{self as pp, ladder, LEVELS, M_STAR, STAR_SIB, STAR_SQ};
use crate::transcript::ItemRec;

/// What an item is, with the A.3 field an absorb's payload belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum It {
    Seed,
    Absorb { len: usize, field: usize },
    Squeeze,
    Col { level: usize },
    Node { level: usize, depth: usize },
}

/// The phases of A.4 with their items (`FRTranscriptDefs.phases`).
pub fn items_seq() -> Vec<(&'static str, It)> {
    let mut v: Vec<(&'static str, It)> = Vec::with_capacity(pp::N_ITEMS);
    let ab = |v: &mut Vec<(&'static str, It)>, ph: &'static str, len: usize, field: usize| v.push((ph, It::Absorb { len, field }));
    let sq = |v: &mut Vec<(&'static str, It)>, ph: &'static str, n: usize| (0..n).for_each(|_| v.push((ph, It::Squeeze)));
    let rounds = |v: &mut Vec<(&'static str, It)>, ph: &'static str, n: usize, len: usize, field: usize| {
        for _ in 0..n {
            v.push((ph, It::Absorb { len, field }));
            v.push((ph, It::Squeeze));
        }
    };
    // `flock-128` (D128 §4.1, `FRShape4.phasesOf seq4`): a 16-byte nonce after the absorb before
    // every grinded phase (`NONCE_LEN`), the degree-3 rounds 64 B, the standalone nonce absorbs
    // `S1n`, `Lr1n`, `E1n`, `B'n`, `P3n` (field `F_NONCE`), E1 13, RS1 5 and P2.4 7 squeezes, E4 end
    // 128 B.
    let nb = pp::NONCE_LEN;
    v.push(("seed", It::Seed));
    ab(&mut v, "stmt", 128, pp::F_STMT);
    ab(&mut v, "cap0", (32 << pp::CAP_LOG[0]) + nb, pp::F_CAPS);
    sq(&mut v, "Z1", pp::Z1_SQ);
    rounds(&mut v, "Z2", 1, 2048, pp::F_Z2);
    rounds(&mut v, "Z3", pp::Z3_ROUNDS, pp::RND3_LEN, pp::F_Z3);
    ab(&mut v, "Zend", 32 + nb, pp::F_ZEND);
    sq(&mut v, "L1", 1);
    rounds(&mut v, "L2", pp::L2_ROUNDS, pp::RND2_LEN, pp::F_L2);
    ab(&mut v, "L3", 16 * pp::L3_KINDS + nb, pp::F_L2);
    sq(&mut v, "L3β", 1);
    ab(&mut v, "S1n", nb, pp::F_NONCE);
    sq(&mut v, "S1", pp::S1_SQ);
    rounds(&mut v, "S2", pp::S2_ROUNDS, pp::RND2_LEN, pp::F_S2);
    ab(&mut v, "Lr1n", nb, pp::F_NONCE);
    sq(&mut v, "Lr1", pp::LR1_SQ);
    rounds(&mut v, "Lr2", pp::LR_ROUNDS, pp::RND3_LEN, pp::F_LR);
    ab(&mut v, "Lrend", pp::LREND_LEN + nb, pp::F_LREND);
    sq(&mut v, "Lr3", 1);
    ab(&mut v, "E1n", nb, pp::F_NONCE);
    sq(&mut v, "E1", pp::E1_SQ);
    rounds(&mut v, "E2", pp::E2_ROUNDS, pp::RND3_LEN, pp::F_E);
    ab(&mut v, "Eend", pp::EEND_LEN + nb, pp::F_EEND);
    sq(&mut v, "E3", 1);
    rounds(&mut v, "E4", pp::E4_ROUNDS, pp::RND2_LEN, pp::F_E);
    ab(&mut v, "E4end", pp::E4END_LEN, pp::F_E);
    ab(&mut v, "RS0", pp::RS_CLAIMS * 128 * 16 + nb, pp::F_RS0);
    sq(&mut v, "RS1", pp::RS1_SQ);
    ab(&mut v, "B'n", nb, pp::F_NONCE);
    sq(&mut v, "B'", 1);
    let star = ladder(M_STAR);
    for i in 0..LEVELS {
        rounds(&mut v, "P1", star[i].rows_log, 96, pp::F_P1);
        if i + 1 < LEVELS {
            ab(&mut v, "C", (32 << pp::CAP_LOG[i + 1]) + nb, pp::F_CAPS);
        } else {
            ab(&mut v, "C", 32 * pp::FINAL_ELEMS + nb, pp::F_FINAL);
        }
        sq(&mut v, "P2", STAR_SQ[i]);
        for _ in 0..star[i].queries {
            v.push(("Q", It::Col { level: i }));
            for d in 0..STAR_SIB[i] {
                v.push(("Q", It::Node { level: i, depth: d }));
            }
        }
        ab(&mut v, "P3n", nb, pp::F_NONCE);
        sq(&mut v, "P3", pp::P3_SQ);
    }
    rounds(&mut v, "Pf", pp::PF_ROUNDS, 96, pp::F_PF);
    // revision 4.4.1 (β′): the committed path digests, ζ, the selectors, z (phases 52–55)
    ab(&mut v, "CapD", 32 * pp::CAP_READS, pp::F_D);
    sq(&mut v, "CapZeta", 1);
    ab(&mut v, "CapChk", 32 * pp::CAP_ENTRIES, pp::F_A);
    sq(&mut v, "CapChkZ", 1);
    v
}

/// `flock-128` (D128 §2.1, `FRShape4.powPosOf seq4`): the Fiat–Shamir positions (index among the
/// seed, absorb and squeeze items) of the last squeeze of every grinded phase, where the answer's
/// byte `POW_BYTE` must be zero: every squeeze run's last squeeze except K phases' (`P1`, `Pf`, the
/// cap check's `CapZeta`, `CapChkZ`). 154 of them.
pub fn pow_positions() -> Vec<usize> {
    let fs: Vec<(&'static str, It)> =
        items_seq().into_iter().filter(|(_, it)| !matches!(it, It::Col { .. } | It::Node { .. })).collect();
    let mut v = Vec::with_capacity(pp::N_POW);
    for p in 0..fs.len() {
        let (ph, it) = fs[p];
        let last = p + 1 == fs.len() || fs[p + 1].1 != It::Squeeze;
        if it == It::Squeeze && last && !matches!(ph, "P1" | "Pf" | "CapZeta" | "CapChkZ") {
            v.push(p);
        }
    }
    v
}

/// The phase of grinded answer `p` (`pow_positions` order, the node's `T.pw` order): for error messages.
pub fn pow_phase(p: usize) -> &'static str {
    let fs: Vec<&'static str> =
        items_seq().into_iter().filter(|(_, it)| !matches!(it, It::Col { .. } | It::Node { .. })).map(|(ph, _)| ph).collect();
    pow_positions().get(p).map_or("?", |&i| fs[i])
}

/// The items as `ItemRec`s (the KAT's form).
pub fn item_recs() -> Vec<ItemRec> {
    items_seq()
        .into_iter()
        .map(|(phase, it)| match it {
            It::Seed => ItemRec { phase, q: "seed", len: None, level: None, depth: None, qlen: 7 + 64 + pp::HDR_LEN },
            It::Absorb { len, .. } => ItemRec { phase, q: "absorb", len: Some(len), level: None, depth: None, qlen: 40 + len },
            It::Squeeze => ItemRec { phase, q: "squeeze", len: None, level: None, depth: None, qlen: 40 },
            It::Col { level } => ItemRec { phase, q: "col", len: None, level: Some(level), depth: None, qlen: 8 + 16 * pp::STAR_ROWS[level] + pp::COL_PAD },
            It::Node { level, depth } => ItemRec { phase, q: "node", len: None, level: Some(level), depth: Some(depth), qlen: 72 },
        })
        .collect()
}

/// G4's cheap check of a taped trace (`oracle::finish_trace`): `k` segment item sequences (A.4),
/// with the 89-byte spacer between consecutive ones (`agg::spacer_q`), every query of its item's
/// length. The tape is the verifier's trace by construction; this catches a missing, extra or
/// misplaced item before `SIGN`.
pub fn shape_ok(tr: &[(Vec<u8>, Digest)], k: usize) -> bool {
    static Q: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let ql = Q.get_or_init(|| item_recs().iter().map(|r| r.qlen).collect());
    if k == 0 || tr.len() != k * ql.len() + (k - 1) {
        return false;
    }
    let mut at = 0;
    for s in 0..k {
        if s > 0 {
            if tr[at].0 != crate::agg::spacer_q() {
                return false;
            }
            at += 1;
        }
        if tr[at..at + ql.len()].iter().zip(ql.iter()).any(|((q, _), &l)| q.len() != l) {
            return false;
        }
        at += ql.len();
    }
    true
}

/// `reassemble tr` (A.5) for a leaf kind: `None` if the trace does not have A.4's shape.
pub fn reassemble(tr: &[(Vec<u8>, Digest)]) -> Option<Vec<u8>> {
    let seq = items_seq();
    if tr.len() != seq.len() {
        return None;
    }
    let mut fields: Vec<Vec<u8>> = pp::FIELD_SIZES.iter().map(|&n| Vec::with_capacity(n)).collect();
    let mut m = 0usize;
    let mut level_pos: Vec<u64> = Vec::new();
    let mut answers: Vec<Digest> = Vec::new();
    let mut qi = 0usize;
    for ((phase, it), (q, a)) in seq.iter().zip(tr.iter()) {
        match *it {
            It::Seed => {
                let hdr = q.get(7 + 64..7 + 64 + pp::HDR_LEN)?;
                m = hdr[1] as usize;
                if !(25..=M_STAR).contains(&m) {
                    return None;
                }
                fields[pp::F_HDR].extend_from_slice(hdr);
            }
            It::Absorb { len, field } => {
                if q.len() != 40 + len {
                    return None;
                }
                fields[field].extend_from_slice(&q[40..]);
            }
            It::Squeeze => {
                if *phase == "P2" {
                    answers.push(*a);
                }
            }
            It::Col { level } => {
                if !answers.is_empty() {
                    // the first column of level i: its positions from P2.i's answers (the kind's log₂ n)
                    let lv = ladder(m)[level];
                    level_pos = positions_of(&answers, lv.queries, lv.code_log);
                    answers.clear();
                    qi = 0;
                } else {
                    qi += 1;
                }
                fields[pp::F_COLS].extend_from_slice(q.get(8..)?);
            }
            It::Node { depth, .. } => {
                if q.len() != 72 {
                    return None;
                }
                let j = *level_pos.get(qi)?;
                let sib = if (j >> depth) & 1 == 0 { &q[40..72] } else { &q[8..40] };
                fields[pp::F_SIBS].extend_from_slice(sib);
            }
        }
    }
    let mut pi = Vec::with_capacity(pp::PI_SIZE);
    for (f, b) in fields.iter().enumerate() {
        if b.len() != pp::FIELD_SIZES[f] {
            return None;
        }
        pi.extend_from_slice(b);
    }
    Some(pi)
}

/// `idxOf`: the first `t` indices of `bits` bits, `⌊256/bits⌋` per answer.
fn positions_of(answers: &[Digest], t: usize, bits: usize) -> Vec<u64> {
    let per = 256 / bits;
    let mut v = Vec::with_capacity(t);
    for a in answers {
        let x = u128::from_le_bytes(a[..16].try_into().unwrap());
        let y = u128::from_le_bytes(a[16..].try_into().unwrap());
        for i in 0..per {
            if v.len() == t {
                return v;
            }
            let mut p = 0u64;
            for b in 0..bits {
                let k = i * bits + b;
                let bit = if k < 128 { (x >> k) & 1 } else { (y >> (k - 128)) & 1 };
                p |= (bit as u64) << b;
            }
            v.push(p);
        }
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::{Local, Recorder, Replay};

    /// The static sequence is `items.json` (when present) and has A.4's counts.
    #[test]
    fn items_seq_kat() {
        let recs = item_recs();
        assert_eq!(recs.len(), pp::N_ITEMS);
        assert_eq!(recs.iter().filter(|r| r.q != "col" && r.q != "node").count(), pp::N_FS_ITEMS);
        // `FLOCK_ITEMS_JSON` (`flock-128`: `logs/I12/dump/items.json`, `itemdump items`), else E1b's dump
        let p = std::env::var_os("FLOCK_ITEMS_JSON").map(std::path::PathBuf::from).unwrap_or_else(|| {
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../logs/I6b/dump/items.json")
        });
        match crate::kat::load_items(&p) {
            Some(want) => crate::kat::compare(&recs, &want).unwrap(),
            None => eprintln!("items_seq_kat: items.json absent, counts only"),
        }
    }

    /// The grinded positions: 154, and Lean's `powPosOf seq4` when `FLOCK_POWPOS` names its dump
    /// (`itemdump powpos`, one position per line).
    #[test]
    fn pow_positions_kat() {
        let v = pow_positions();
        assert_eq!(v.len(), pp::N_POW);
        match std::env::var_os("FLOCK_POWPOS").and_then(|p| std::fs::read_to_string(p).ok()) {
            Some(s) => {
                let want: Vec<usize> = s.split_whitespace().map(|x| x.parse().unwrap()).collect();
                assert_eq!(v, want);
            }
            None => eprintln!("pow_positions_kat: FLOCK_POWPOS absent, count only"),
        }
    }

    /// `reassemble` of an honest trace is the proof (`reassemble_roundtrip`), m = 25 and 26.
    #[test]
    fn reassemble_roundtrip() {
        let circ = crate::circuit::Circuit::build();
        let base = Local::keyed(&[9u8; 32]);
        for m in [25usize, 26] {
            let rec = Recorder::new(&base);
            let (vk, s) = ([1u8; 32], [m as u8; 32]);
            let (pi, _) = crate::leaf::prove(&rec, &circ, &vk, &s, m);
            let table = rec.into_table();
            let mut rp = Replay::new(&table);
            rp.fallback = Some(&base);
            assert!(crate::leaf::verify(&rp, &circ, &vk, &crate::leaf::leaf_c(&s, m), &pi));
            let (tr, _) = rp.finish();
            assert_eq!(reassemble(&tr).as_deref(), Some(&pi[..]), "m = {m}");
        }
    }
}
