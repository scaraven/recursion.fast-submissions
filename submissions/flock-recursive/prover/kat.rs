//! Known-answer checks against the Lean dumps (stage P2, rev. 3.7):
//!
//! * the item sequence (A.4): `logs/E1/dump/items.json` (revision 4.1, `seq4`; identical to S-0′'s) (`irdump items`, 8,905 items: phase, query
//!   kind, payload length, Merkle level and depth, query length), compared item by item with what
//!   the native verifier asks (`leaf::verify_logged`) and, for the Fiat–Shamir items, with what the
//!   prover asks. The file is read where it is (env `FLOCK_ITEMS_JSON`, else `logs/S-0/dump/
//!   items.json` above the working directory); it is not copied into the crate.
//! * the leaf chain block's rows and target (A.6, `FRBlockKinds.kindRows gateBase
//!   Chain.chainTarget`): `kat-chain-kind.txt` holds the BLAKE2s-256 of the Lean dump (448 MB, one
//!   line per position) with its provenance; the test renders the same lines from `circuit.rs` and
//!   compares the digest (and the dump line by line where the file is present).

use crate::transcript::ItemRec;
use std::path::PathBuf;

/// `items.json`'s path: `FLOCK_ITEMS_JSON`, else `logs/E1/dump/items.json` in the working directory
/// or one of its parents.
pub fn find_items_json() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("FLOCK_ITEMS_JSON") {
        return Some(PathBuf::from(p));
    }
    let mut d = std::env::current_dir().ok()?;
    loop {
        let p = d.join("logs/E1/dump/items.json");
        if p.is_file() {
            return Some(p);
        }
        if !d.pop() {
            return None;
        }
    }
}

/// The dumped verifier programs with the finals (`ops-L30.txt`, `ops-L31.txt`, `ops-L32.txt`; S-F4, revision 4.1): `FLOCK_IR_DUMP`, else
/// `logs/E1/dump` in the working directory or one of its parents.
pub fn find_ir_dump() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("FLOCK_IR_DUMP") {
        return Some(PathBuf::from(p));
    }
    let mut d = std::env::current_dir().ok()?;
    loop {
        let p = d.join("logs/E1/dump");
        if p.join("ops-L32.txt").is_file() {
            return Some(p);
        }
        if !d.pop() {
            return None;
        }
    }
}

/// The item objects of `items.json`, one per line as the dump tool prints them.
pub fn load_items(p: &std::path::Path) -> Option<Vec<String>> {
    let s = std::fs::read_to_string(p).ok()?;
    Some(
        s.lines()
            .map(|l| l.trim_start_matches([' ', ',']).trim_end())
            .filter(|l| l.starts_with('{'))
            .map(String::from)
            .collect(),
    )
}

/// The query length of an item object (`"qlen":N`).
pub fn qlen_of(item: &str) -> usize {
    let i = item.find("\"qlen\":").expect("qlen") + 7;
    item[i..].trim_end_matches('}').parse().expect("qlen")
}

/// `log` against `want`, item by item (the first difference is reported).
pub fn compare(log: &[ItemRec], want: &[String]) -> Result<(), String> {
    for (i, (a, b)) in log.iter().zip(want.iter()).enumerate() {
        let a = a.json();
        if &a != b {
            return Err(format!("item {i}: native {a}, Lean {b}"));
        }
    }
    if log.len() != want.len() {
        return Err(format!("{} items, Lean {}", log.len(), want.len()));
    }
    Ok(())
}

/// The prover's Fiat–Shamir items against the Fiat–Shamir subsequence of `want`.
pub fn compare_fs(log: &[ItemRec], want: &[String]) -> Result<(), String> {
    let fs: Vec<String> = want.iter().filter(|w| !w.contains("\"q\":\"col\"") && !w.contains("\"q\":\"node\"")).cloned().collect();
    compare(log, &fs)
}

/// The item KAT of a verifier log, if `items.json` is found: `Some(Ok)`, `Some(Err(first
/// difference))`, or `None` (file absent).
pub fn items_kat(log: &[ItemRec]) -> Option<Result<(), String>> {
    let p = find_items_json()?;
    let want = load_items(&p)?;
    Some(compare(log, &want))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blake2s::Blake2s;
    use crate::circuit::{e_positions, Circuit, BLOCK};
    use crate::params::{leaf_kind_byte, PI_SIZE};

    fn items_path() -> Option<PathBuf> {
        std::env::var_os("FLOCK_ITEMS_JSON").map(PathBuf::from).or_else(|| {
            let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../logs/E1/dump/items.json");
            p.is_file().then_some(p)
        })
    }

    /// The verifier asks A.4's 8,905 items for every leaf kind and test shape, whatever `π` holds
    /// (here a zero proof with the kind's header).
    #[test]
    fn items_kat_verifier() {
        let Some(p) = items_path() else {
            eprintln!("items_kat_verifier: SKIP (logs/E1/dump/items.json absent)");
            return;
        };
        let want = load_items(&p).unwrap();
        assert_eq!(want.len(), crate::params::N_ITEMS);
        assert_eq!(want.iter().filter(|w| !w.contains("\"q\":\"col\"") && !w.contains("\"q\":\"node\"")).count(), crate::params::N_FS_ITEMS);
        let circ = Circuit::build();
        let o = crate::oracle::Local::keyed(&[3u8; 32]);
        for m in [25usize, 28, 30, 32] {
            let mut pi = vec![0u8; PI_SIZE];
            pi[0] = leaf_kind_byte(m);
            pi[1] = m as u8;
            let (ok, log) = crate::leaf::verify_logged(&o, &circ, &[1u8; 32], &[2u8; 32], &pi, true);
            assert!(!ok);
            let log = log.unwrap();
            compare(&log, &want).unwrap_or_else(|e| panic!("m = {m}: {e}"));
        }
    }

    /// A real proof (m = 25): the prover's Fiat–Shamir items and the verifier's items are A.4's.
    #[test]
    fn items_kat_prover() {
        let Some(p) = items_path() else {
            eprintln!("items_kat_prover: SKIP (logs/E1/dump/items.json absent)");
            return;
        };
        let want = load_items(&p).unwrap();
        let circ = Circuit::build();
        let o = crate::oracle::Local::keyed(&[4u8; 32]);
        let (vk, s, m) = ([5u8; 32], [6u8; 32], 25usize);
        let ((pi, _), plog) = crate::leaf::prove_logged(&o, &circ, &vk, &s, m, crate::params::leaf_n(m), true);
        assert_eq!(pi.len(), PI_SIZE);
        compare_fs(&plog.unwrap(), &want).unwrap();
        let c = crate::leaf::leaf_c(&s, m);
        let (ok, vlog) = crate::leaf::verify_logged(&o, &circ, &vk, &c, &pi, true);
        assert!(ok);
        compare(&vlog.unwrap(), &want).unwrap();
    }

    fn render_line(k: usize, a: &[u64; 256], b: &[u64; 256], e: bool, out: &mut String) {
        use std::fmt::Write;
        let bits = |w: &[u64; 256]| -> String {
            let mut v = Vec::new();
            for (i, x) in w.iter().enumerate() {
                let mut x = *x;
                while x != 0 {
                    v.push((64 * i + x.trailing_zeros() as usize).to_string());
                    x &= x - 1;
                }
            }
            v.join(",")
        };
        let _ = writeln!(out, "{k} a:{} b:{} e:{}", bits(a), bits(b), e as u8);
    }

    /// A.6's dump KAT for the leaf chain block: `A₀^chain`, `B₀^chain` and `E`, position by position,
    /// equal the Lean `kindRows gateBase Chain.chainTarget` (digest in `kat-chain-kind.txt`).
    #[test]
    fn chain_kind_rows_kat() {
        let kat = include_str!("kat-chain-kind.txt");
        let field = |name: &str| -> &str {
            kat.lines().find_map(|l| l.strip_prefix(name).map(str::trim)).unwrap_or_else(|| panic!("{name}"))
        };
        let want_digest = field("blake2s ");
        let want_lines: usize = field("lines ").parse().unwrap();
        let want_bytes: usize = field("bytes ").parse().unwrap();
        let want_e: Vec<usize> = field("e1 ").split(',').map(|x| x.parse().unwrap()).collect();
        let circ = Circuit::build();
        let rows = circ.row_bitsets();
        assert_eq!(rows.len(), want_lines);
        let e = e_positions();
        assert_eq!(e, &want_e, "the target E's 1-positions");
        let full = std::env::var_os("FLOCK_CHAIN_ROWS").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../logs/P2/r37/kinds/chain-rows.txt"));
        let lean = std::fs::read_to_string(&full).ok();
        let mut lean_lines = lean.as_deref().map(|s| s.lines());
        let mut h = Blake2s::new();
        let mut bytes = 0usize;
        let mut line = String::new();
        for k in 0..BLOCK {
            line.clear();
            render_line(k, &rows[k].0, &rows[k].1, e.binary_search(&k).is_ok(), &mut line);
            if let Some(ll) = lean_lines.as_mut() {
                let l = ll.next().unwrap();
                assert_eq!(line.trim_end(), l, "row {k}");
            }
            h.update(line.as_bytes());
            bytes += line.len();
        }
        let d: String = h.finalize().iter().map(|x| format!("{x:02x}")).collect();
        assert_eq!((bytes, d.as_str()), (want_bytes, want_digest));
        eprintln!("chain_kind_rows_kat: digest equal; full dump {}", if lean.is_some() { "compared line by line" } else { "absent (digest only)" });
    }
}

/// `rel` in the working directory or one of its parents (KAT files under `logs/`).
pub fn find_up(rel: &str) -> Option<PathBuf> {
    let mut d = std::env::current_dir().ok()?;
    loop {
        let p = d.join(rel);
        if p.exists() {
            return Some(p);
        }
        if !d.pop() {
            return None;
        }
    }
}
