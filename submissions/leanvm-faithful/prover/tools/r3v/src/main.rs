//! `refv-full DIR [--parts LIST]` (WP R3, dev): accept or reject `DIR/full6.signed` (`lvm6-prover full6`) as `acc`
//! does: strict file parse, `|q_i| ≤ 2^20`, `m ≤ qV`, `SigOk`, then refv's `V_S` (`refv::vs::verify_pi`) with
//! query `i` answered by trace entry `i` (`runSeq`), every entry used, and the dev check that each answer is the
//! keyed oracle's: `refv::full::verify_full_file` (every part walked by refv). `--parts` must be the list the proof was made with (`meta.txt`'s `parts`, the default).
//! Exit 0 iff accepted.

use refv::unhex32;

fn main() {
    let dir = std::path::PathBuf::from(std::env::args().nth(1).expect("refv-full DIR"));
    let meta = std::fs::read_to_string(dir.join("meta.txt")).expect("meta.txt");
    let field = |k: &str| {
        meta.lines().find_map(|l| l.strip_prefix(&format!("{k} "))).unwrap_or_else(|| panic!("meta {k}")).to_string()
    };
    let parts = std::env::args()
        .position(|a| a == "--parts")
        .and_then(|i| std::env::args().nth(i + 1))
        .unwrap_or_else(|| field("parts"));
    let (vk, c, key, h) =
        (unhex32(&field("vk")).unwrap(), unhex32(&field("c")).unwrap(), unhex32(&field("key")).unwrap(), unhex32(&field("h")).unwrap());
    let sh = refv::shape::p18();
    let file = std::fs::read(dir.join("full6.signed")).expect("full6.signed");
    let t = std::time::Instant::now();
    // `h` and `accIn` are read from `HDR` by `refv::full` (never from the prover's meta).
    let _ = h;
    let verdict = refv::full::verify_full_file(&sh, &vk, &c, &file, Some(&key), &parts);
    let secs = t.elapsed().as_secs_f64();
    match verdict {
        Ok(rep) => {
            let tot = rep.total();
            let per: Vec<String> =
                rep.stats.iter().map(|(p, s)| format!("{p}: {} B {} q {} n", s.body, s.queries, s.nonces)).collect();
            println!(
                "ACCEPT parts {parts}: file {} B queries {} claims {} body {} nonces {} binds {} | {} | {secs:.3} s",
                file.len(),
                rep.queries,
                rep.claims,
                tot.body,
                tot.nonces,
                tot.binds,
                per.join("; ")
            );
        }
        Err(e) => {
            println!("REJECT {e} ({secs:.3} s)");
            std::process::exit(1);
        }
    }
}
