//! `refv verify --shape p18 --vk HEX --c HEX [--key HEX] FILE` — accept or reject a signed proof file.
//! `refv kat --shape t15|p18 --out DIR [--seed N]` — write the honest fixture, its checkpoints and the tamper set.

use refv::{Part, hex, shape, unhex32};
use std::fmt::Write as _;

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let sh = shape::by_name(&arg(&args, "--shape").unwrap_or("p18".into())).expect("--shape p18|t15");
    match args.get(1).map(String::as_str) {
        Some("verify") => {
            let vk = unhex32(&arg(&args, "--vk").expect("--vk")).expect("vk hex");
            let c = unhex32(&arg(&args, "--c").expect("--c")).expect("c hex");
            let key = arg(&args, "--key").map(|k| unhex32(&k).expect("key hex"));
            let file = std::fs::read(args.last().unwrap()).expect("read file");
            match refv::vs::verify_file(&sh, &vk, &c, &file, key.as_ref()) {
                Ok(r) => println!("ACCEPT queries {} body {}", r.queries, r.total().body),
                Err(e) => {
                    println!("REJECT {e}");
                    std::process::exit(1);
                }
            }
        }
        Some("kat") => {
            let out = std::path::PathBuf::from(arg(&args, "--out").expect("--out DIR"));
            let seed: u64 = arg(&args, "--seed").map_or(1, |s| s.parse().unwrap());
            std::fs::create_dir_all(&out).unwrap();
            let t = std::time::Instant::now();
            let cfg = refv::prover::Cfg::new(sh.clone(), seed);
            let kat = refv::prover::prove(&cfg);
            eprintln!("proved in {:.1} s", t.elapsed().as_secs_f64());
            let rep = refv::vs::verify_file(&sh, &kat.vk, &kat.c, &kat.file, Some(&cfg.key)).expect("honest KAT accepted");
            let name = sh.name.to_ascii_lowercase();
            std::fs::write(out.join(format!("{name}.signed")), &kat.file).unwrap();
            std::fs::write(out.join(format!("{name}.json")), checkpoints_json(&sh, &cfg, &kat, &rep)).unwrap();
            println!("{}", checkpoints_json(&sh, &cfg, &kat, &rep));
            if args.iter().any(|a| a == "--tampers") {
                // Kind P tampers: one file each, and a manifest of the rejection V_S must give.
                let mut manifest = String::new();
                for (k, (t, want)) in refv::prover::tamper_set(&sh).into_iter().enumerate() {
                    let mut tc = cfg.clone();
                    tc.tamper = Some(t);
                    let tk = refv::prover::prove(&tc);
                    let got = refv::vs::verify_file(&sh, &tk.vk, &tk.c, &tk.file, Some(&cfg.key)).err();
                    assert_eq!(got.as_ref(), Some(&want), "tamper {t:?}");
                    let f = format!("{name}-tamper-{k:02}.signed");
                    std::fs::write(out.join(&f), &tk.file).unwrap();
                    let _ = writeln!(manifest, "{f}\t{t:?}\t{want:?}");
                }
                std::fs::write(out.join(format!("{name}-tampers.tsv")), manifest).unwrap();
            }
        }
        Some("verify-full") => {
            let vk = unhex32(&arg(&args, "--vk").expect("--vk")).expect("vk hex");
            let c = unhex32(&arg(&args, "--c").expect("--c")).expect("c hex");
            let key = arg(&args, "--key").map(|k| unhex32(&k).expect("key hex"));
            let parts = arg(&args, "--parts").unwrap_or("all".into());
            let file = std::fs::read(args.last().unwrap()).expect("read file");
            match refv::full::verify_full_file(&sh, &vk, &c, &file, key.as_ref(), &parts) {
                Ok(r) => println!("ACCEPT queries {} claims {} body {}", r.queries, r.claims, r.total().body),
                Err(e) => {
                    println!("REJECT {e}");
                    std::process::exit(1);
                }
            }
        }
        Some("kat-full") => kat_full(&sh, &args),
        _ => {
            eprintln!("usage: refv verify|verify-full|kat|kat-full …");
            std::process::exit(2);
        }
    }
}

fn checkpoints_json(sh: &shape::Shape, cfg: &refv::prover::Cfg, kat: &refv::prover::Kat, r: &refv::vs::Report) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "{{\n  \"shape\": \"{}\", \"seed\": {}, \"sign_seed\": {},", sh.name, cfg.seed, cfg.sign_seed);
    let _ = writeln!(s, "  \"oracle_key\": \"{}\", \"vk\": \"{}\", \"c\": \"{}\", \"h\": \"{}\",", hex(&cfg.key), hex(&kat.vk), hex(&kat.c), hex(&kat.h));
    let _ = writeln!(
        s,
        "  \"pi_len\": {}, \"trace_len\": {}, \"file_len\": {}, \"file_keccak\": \"{}\",",
        kat.pi.len(),
        kat.trace.len(),
        kat.file.len(),
        hex(&refv::keccak::keccak256(&kat.file))
    );
    let _ = writeln!(s, "  \"y0\": [{}, {}], \"lambda0\": [{}, {}],", r.y0.c0, r.y0.c1, r.lambda0.c0, r.lambda0.c1);
    let _ = writeln!(s, "  \"parts\": [");
    let n = r.checkpoints.len();
    for (k, cp) in r.checkpoints.iter().enumerate() {
        let st = r.stats.get(&cp.part).cloned().unwrap_or_default();
        let _ = writeln!(
            s,
            "    {{\"part\": \"{}\", \"body\": {}, \"queries\": {}, \"nonces\": {}, \"draws\": {}, \"binds\": {}, \"body_end\": {}, \"queries_end\": {}, \"st\": \"{}\"}}{}",
            cp.part,
            if cp.part == Part::Seed { 0 } else { st.body },
            st.queries,
            st.nonces,
            st.draws,
            st.binds,
            cp.body_end,
            cp.queries_end,
            hex(&cp.st),
            if k + 1 < n { "," } else { "" }
        );
    }
    let _ = writeln!(s, "  ],");
    let pos: Vec<String> = r.trail.positions.iter().map(|p| format!("{p:?}")).collect();
    let _ = writeln!(s, "  \"positions\": [{}]\n}}", pos.join(", "));
    s
}

/// `refv kat-full --in DIR --out DIR`: the honest full proof `DIR/full6.signed` (+ `meta.txt`, `lvm6-prover full6`)
/// checked, copied, and one byte tamper per message class of every part (trace re-derived, re-signed), each with the
/// rejection `V_S` gives; `full-tampers.tsv` lists them.
fn kat_full(sh: &shape::Shape, args: &[String]) {
    use fs6::schedule::Item;
    let din = std::path::PathBuf::from(arg(args, "--in").expect("--in DIR"));
    let out = std::path::PathBuf::from(arg(args, "--out").expect("--out DIR"));
    std::fs::create_dir_all(&out).unwrap();
    let meta = std::fs::read_to_string(din.join("meta.txt")).expect("meta.txt");
    let field = |k: &str| meta.lines().find_map(|l| l.strip_prefix(&format!("{k} "))).map(str::to_string).expect("meta field");
    let (vk, c, key) = (unhex32(&field("vk")).unwrap(), unhex32(&field("c")).unwrap(), unhex32(&field("key")).unwrap());
    let file = std::fs::read(din.join("full6.signed")).expect("full6.signed");
    let rep = refv::full::verify_full_file(sh, &vk, &c, &file, Some(&key), "all").expect("honest full proof accepted");
    std::fs::write(out.join("full.signed"), &file).unwrap();
    let pi = refv::format::from_file(&file).unwrap().pi;
    let mut info = String::new();
    // R7: the mode from `HDR.b` (lane 1), and the circuit `Q` the proof is for (`$LVM6_Q_BLOB`'s Keccak-256, or the stub)
    let mode = if pi[8] == 1 { "node" } else { "leaf" };
    let q = std::env::var_os("LVM6_Q_BLOB").map_or("stub".to_string(), |p| hex(&refv::keccak::keccak256(&std::fs::read(&p).expect("LVM6_Q_BLOB"))));
    let _ = writeln!(info, "{{\n  \"shape\": \"P18\", \"mode\": \"{mode}\", \"q_blob_keccak\": \"{q}\", \"oracle_key\": \"{}\", \"vk\": \"{}\", \"c\": \"{}\",", hex(&key), hex(&vk), hex(&c));
    let _ = writeln!(info, "  \"pi_len\": {}, \"queries\": {}, \"claims\": {}, \"file_len\": {}, \"file_keccak\": \"{}\",", pi.len(), rep.queries, rep.claims, file.len(), hex(&refv::keccak::keccak256(&file)));
    let _ = writeln!(info, "  \"parts\": [");
    let n = rep.checkpoints.len();
    for (k, cp) in rep.checkpoints.iter().enumerate() {
        let st = rep.stats.get(&cp.part).cloned().unwrap_or_default();
        let _ = writeln!(info, "    {{\"part\": \"{}\", \"body\": {}, \"queries\": {}, \"nonces\": {}, \"binds\": {}, \"body_end\": {}, \"queries_end\": {}, \"st\": \"{}\"}}{}",
            cp.part, st.body, st.queries, st.nonces, st.binds, cp.body_end, cp.queries_end, hex(&cp.st), if k + 1 < n { "," } else { "" });
    }
    let _ = writeln!(info, "  ]\n}}");
    std::fs::write(out.join("full.json"), &info).unwrap();
    // Targets: per part, its first and last absorbed message, its first nonce, and its openings' first byte.
    let items = refv::full::item_map(sh);
    let mut targets: Vec<(String, usize, String)> = Vec::new();
    let mut parts: Vec<String> = items.iter().map(|i| i.part.clone()).collect();
    parts.dedup();
    for p in &parts {
        let mine: Vec<_> = items.iter().filter(|i| &i.part == p).collect();
        let msgs: Vec<_> = mine.iter().filter(|i| matches!(i.item, Item::E(_) | Item::K(_) | Item::Cap(_))).collect();
        if let Some(i) = msgs.first() {
            targets.push((p.clone(), i.off, format!("first message {:?} (item {})", i.item, i.index)));
        }
        if let Some(i) = msgs.last() {
            targets.push((p.clone(), i.off + i.len - 16.min(i.len), format!("last message {:?} (item {}), its last scalar", i.item, i.index)));
        }
        if let Some(i) = mine.iter().find(|i| matches!(i.item, Item::G(_))) {
            targets.push((p.clone(), i.off + 7, format!("first nonce {:?} (item {}), top byte", i.item, i.index)));
        }
        if let Some(i) = mine.iter().find(|i| matches!(i.item, Item::Open(_))) {
            targets.push((p.clone(), i.off, format!("first opening {:?}, leaf byte 0", i.item)));
        }
    }
    // Every message that a native check reads before the next group (the next item is not a `G`): a byte edit there
    // must be rejected by that check, not by a nonce.
    for w in items.windows(2) {
        let (i, next) = (&w[0], &w[1]);
        let lead = !matches!(next.item, Item::G(_) | Item::D(_) | Item::B);
        if matches!(i.item, Item::E(_)) && lead && !targets.iter().any(|t| t.1 == i.off || t.1 == i.off + i.len - 16) {
            targets.push((i.part.clone(), i.off, format!("message before a check {:?} (item {})", i.item, i.index)));
        }
    }
    // §6.4a checks made before the next group's draw: `A, B, C` (row 3) and `v_R` (row 9).
    for i in items.iter().filter(|i| i.part == "6.4ty" && (i.index == 60 || i.index == 144)) {
        targets.push((i.part.clone(), i.off, format!("message before a check {:?} (item {})", i.item, i.index)));
    }
    let mut tsv = String::new();
    for (k, (p, off, what)) in targets.iter().enumerate() {
        let mut t = pi.clone();
        t[*off] ^= if what.contains("nonce") { 0x80 } else { 1 };
        let f = refv::full::resign_full(sh, &vk, &c, &t, &key, 7);
        let got = refv::full::verify_full_file(sh, &vk, &c, &f, Some(&key), "all").err().expect("a tamper is rejected");
        let name = format!("full-tamper-{k:02}.signed");
        std::fs::write(out.join(&name), &f).unwrap();
        let _ = writeln!(tsv, "{name}\t{p}\t{off}\t{what}\t{got:?}");
        eprintln!("{name} {p} @{off} {what}: {got:?}");
    }
    std::fs::write(out.join("full-tampers.tsv"), tsv).unwrap();
}
