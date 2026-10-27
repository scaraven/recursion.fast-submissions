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
    let mut v: Vec<(&'static str, It)> = Vec::with_capacity(8854);
    let ab = |v: &mut Vec<(&'static str, It)>, ph: &'static str, len: usize, field: usize| v.push((ph, It::Absorb { len, field }));
    let sq = |v: &mut Vec<(&'static str, It)>, ph: &'static str, n: usize| (0..n).for_each(|_| v.push((ph, It::Squeeze)));
    let rounds = |v: &mut Vec<(&'static str, It)>, ph: &'static str, n: usize, len: usize, field: usize| {
        for _ in 0..n {
            v.push((ph, It::Absorb { len, field }));
            v.push((ph, It::Squeeze));
        }
    };
    v.push(("seed", It::Seed));
    ab(&mut v, "stmt", 128, pp::F_STMT);
    ab(&mut v, "cap0", 32 << pp::CAP_LOG[0], pp::F_CAPS);
    sq(&mut v, "Z1", pp::Z1_SQ);
    rounds(&mut v, "Z2", 1, 2048, pp::F_Z2);
    rounds(&mut v, "Z3", pp::Z3_ROUNDS, 48, pp::F_Z3);
    ab(&mut v, "Zend", 32, pp::F_ZEND);
    sq(&mut v, "L1", 1);
    rounds(&mut v, "L2", pp::L2_ROUNDS, 48, pp::F_L2);
    ab(&mut v, "L3", 16 * pp::L3_KINDS, pp::F_L2);
    sq(&mut v, "L3β", 1);
    sq(&mut v, "S1", pp::S1_SQ);
    rounds(&mut v, "S2", pp::S2_ROUNDS, 48, pp::F_S2);
    sq(&mut v, "Lr1", pp::LR1_SQ);
    rounds(&mut v, "Lr2", pp::LR_ROUNDS, 48, pp::F_LR);
    ab(&mut v, "Lrend", 48, pp::F_LREND);
    sq(&mut v, "Lr3", 1);
    rounds(&mut v, "Lr4", pp::LR_ROUNDS, 48, pp::F_LR);
    ab(&mut v, "RS0", pp::RS_CLAIMS * 128 * 16, pp::F_RS0);
    sq(&mut v, "RS1", pp::RS1_SQ);
    sq(&mut v, "E1", pp::E1_SQ);
    rounds(&mut v, "E2", pp::E2_ROUNDS, 48, pp::F_E);
    ab(&mut v, "Eend", 48, pp::F_EEND);
    sq(&mut v, "E3", 1);
    sq(&mut v, "B'", 1);
    let star = ladder(M_STAR);
    for i in 0..LEVELS {
        rounds(&mut v, "P1", star[i].rows_log, 96, pp::F_P1);
        if i + 1 < LEVELS {
            ab(&mut v, "C", 32 << pp::CAP_LOG[i + 1], pp::F_CAPS);
        } else {
            ab(&mut v, "C", 32 * pp::FINAL_ELEMS, pp::F_FINAL);
        }
        sq(&mut v, "P2", STAR_SQ[i]);
        for _ in 0..star[i].queries {
            v.push(("Q", It::Col { level: i }));
            for d in 0..STAR_SIB[i] {
                v.push(("Q", It::Node { level: i, depth: d }));
            }
        }
        sq(&mut v, "P3", 1);
    }
    rounds(&mut v, "Pf", pp::PF_ROUNDS, 96, pp::F_PF);
    v
}

/// The items as `ItemRec`s (the KAT's form).
pub fn item_recs() -> Vec<ItemRec> {
    items_seq()
        .into_iter()
        .map(|(phase, it)| match it {
            It::Seed => ItemRec { phase, q: "seed", len: None, level: None, depth: None, qlen: 7 + 64 + pp::HDR_LEN },
            It::Absorb { len, .. } => ItemRec { phase, q: "absorb", len: Some(len), level: None, depth: None, qlen: 40 + len },
            It::Squeeze => ItemRec { phase, q: "squeeze", len: None, level: None, depth: None, qlen: 40 },
            It::Col { level } => ItemRec { phase, q: "col", len: None, level: Some(level), depth: None, qlen: 8 + 16 * pp::STAR_ROWS[level] },
            It::Node { level, depth } => ItemRec { phase, q: "node", len: None, level: Some(level), depth: Some(depth), qlen: 72 },
        })
        .collect()
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
        assert_eq!(recs.len(), 8854);
        assert_eq!(recs.iter().filter(|r| r.q != "col" && r.q != "node").count(), 431);
        let p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../logs/S-0/dump/items.json");
        match crate::kat::load_items(&p) {
            Some(want) => crate::kat::compare(&recs, &want).unwrap(),
            None => eprintln!("items_seq_kat: items.json absent, counts only"),
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
