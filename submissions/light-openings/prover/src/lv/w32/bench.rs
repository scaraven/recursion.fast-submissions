//! lvm2 W32 G0: `lvm-prover w32 bench LOGN REPS` (the K = 32 block kernels over random blocks, one thread, each
//! loop between SDE marks; the K = 16 kernels left with the K = 16 protocol, W32-P) and `lvm-prover w32 dump DIR` (inputs and reference outputs at 2 blocks,
//! the v4 kernels checked against the references, for the W32 reference checker `check32.py`, a lead-side script, not shipped).

use std::io::Write;
use std::time::Instant;

use super::*;

pub struct Rng(u64);
impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

pub struct Data {
    pub blocks: Vec<Vec<u64>>,
    pub w: Vec<[u64; 2]>,
    pub wb: Vec<[u64; 2]>,
}

pub fn data(nb: usize, seed: u64) -> Data {
    let mut rng = Rng(seed);
    let blocks = (0..nb).map(|_| (0..BITS * BLOCK_WORDS).map(|_| rng.next_u64()).collect()).collect();
    let w = (0..BITS).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
    let wb = (0..nb).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
    Data { blocks, w, wb }
}

pub fn cmd(args: &[String]) -> i32 {
    match args.get(2).map(String::as_str) {
        Some("bench") => {
            let log_n: usize = args.get(3).map_or(14, |v| v.parse().expect("LOGN"));
            let reps: usize = args.get(4).map_or(1, |v| v.parse().expect("REPS"));
            let which = args.get(5).cloned().unwrap_or_else(|| "all".into());
            bench(log_n, reps, &which)
        }
        Some("dump") => dump(args.get(3).expect("DIR")),
        Some("rmfe") => rmfe(args.get(3).expect("JSON (rmfe_lean.json)")),
        _ => {
            eprintln!("usage: w32 bench LOGN REPS [all|skip|product|w32|embed] | w32 dump DIR | w32 rmfe JSON");
            2
        }
    }
}

fn report(name: &str, t: f64, inst: usize, sink: u64) {
    println!("{name:12} {:9.3} ms  {:8.3} ns/instance-layer  (sink {sink:016x})", 1e3 * t, 1e9 * t / inst as f64);
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
fn bench(log_n: usize, reps: usize, which: &str) -> i32 {
    let nb = (1usize << log_n) / 512;
    let d = data(nb.max(1), 0x5732);
    let inst = d.blocks.len() * 512 * reps;
    println!("w32 bench: 2^{log_n} instances ({} blocks) x {reps} reps, one thread, v4", d.blocks.len());
    let on = |k: &str| which == "all" || which == k;
    if on("skip") || on("w32") {
        let w = v4::Weights32::new(&d.w);
        let mut sk = v4::Skip32::new();
        let mut sink = 0;
        mark(0x22, false);
        let t = Instant::now();
        for _ in 0..reps {
            for b in &d.blocks {
                sk.run(b, &w);
                sink ^= sk.get(0)[0];
            }
        }
        let t = t.elapsed().as_secs_f64();
        mark(0x22, true);
        report("W32 Skip", t, inst, sink);
    }
    if on("product") || on("w32") {
        let pr = v4::Product32::new(&d.w);
        let mut sc = pr.scratch();
        let mut sums = pr.sums();
        mark(0x24, false);
        let t = Instant::now();
        for _ in 0..reps {
            for (b, wb) in d.blocks.iter().zip(&d.wb) {
                pr.block_sums(&mut sc, b, *wb, &mut sums);
            }
        }
        let t = t.elapsed().as_secs_f64();
        mark(0x24, true);
        report("W32 Product", t, inst, v4::Product32::get(&sums, 0)[0]);
    }
    if on("embed") || which == "all" {
        // SAFETY: AVX-512F at compile time.
        let mut out = [unsafe { core::arch::x86_64::_mm512_setzero_si512() }; PACKS];
        let mut sink = 0;
        mark(0x25, false);
        let t = Instant::now();
        for _ in 0..reps {
            for b in &d.blocks {
                sink ^= v4::embed_block(b, &mut out);
            }
        }
        let t = t.elapsed().as_secs_f64();
        mark(0x25, true);
        report("W32 embed", t, inst, sink);
    }
    0
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
)))]
fn bench(log_n: usize, reps: usize, which: &str) -> i32 {
    super::dev::bench(log_n, reps, which)
}

fn hex2(w: [u64; 2]) -> String {
    format!("{:016x}{:016x}", w[1], w[0])
}

fn dump(dir: &str) -> i32 {
    std::fs::create_dir_all(dir).expect("dir");
    let d = data(2, 0xD32);
    let mut f = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/in.txt")).unwrap());
    writeln!(f, "{}", d.blocks.len()).unwrap();
    for b in &d.blocks {
        writeln!(f, "{}", b.iter().map(|x| format!("{x:016x}")).collect::<Vec<_>>().join(" ")).unwrap();
    }
    for w in &d.w {
        writeln!(f, "{}", hex2(*w)).unwrap();
    }
    for w in &d.wb {
        writeln!(f, "{}", hex2(*w)).unwrap();
    }
    drop(f);
    let mut fs = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/skip.txt")).unwrap());
    let mut fp = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/prod.txt")).unwrap());
    let mut refs_skip = Vec::new();
    let mut refs_prod = Vec::new();
    for b in &d.blocks {
        let s = skip_ref(b, &d.w);
        for v in &s {
            writeln!(fs, "{:016x}{:016x}{:016x}{:016x}", v[3], v[2], v[1], v[0]).unwrap();
        }
        let p = product_ref(b, &d.w);
        for q in 0..PACKS {
            for c in 0..PROD_BITS {
                writeln!(fp, "{:032x}", p[column(q, c)]).unwrap();
            }
        }
        refs_skip.push(s);
        refs_prod.push(p);
    }
    drop((fs, fp));
    println!("w32 dump: {} blocks written to {dir}", d.blocks.len());
    check_kernels(&d, &refs_skip, &refs_prod)
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
fn check_kernels(d: &Data, refs_skip: &[[[u64; 4]; SLOTS]], refs_prod: &[Vec<u128>]) -> i32 {
    let mut ok = true;
    for b in &d.blocks {
        for j in (0..BITS).step_by(8) {
            ok &= v4::embed8_ok(b, j);
        }
    }
    println!("embed8 vs portable embed: {}", if ok { "OK" } else { "FAIL" });
    let w = v4::Weights32::new(&d.w);
    let mut sk = v4::Skip32::new();
    let mut sok = true;
    for (b, r) in d.blocks.iter().zip(refs_skip) {
        sk.run(b, &w);
        for i in 0..SLOTS {
            sok &= sk.get(i) == r[i];
        }
    }
    println!("Skip32 (v4) vs skip_ref: {}", if sok { "OK" } else { "FAIL" });
    let pr = v4::Product32::new(&d.w);
    let mut sc = pr.scratch();
    let mut sums = pr.sums();
    let mut want = vec![[0u64; 4]; PAIRS * 64];
    for ((b, wb), r) in d.blocks.iter().zip(&d.wb).zip(refs_prod) {
        pr.block_sums(&mut sc, b, *wb, &mut sums);
        for (c, v) in r.iter().enumerate() {
            xor4(&mut want[c], mul256(*v, *wb));
        }
    }
    let pok = (0..PAIRS * 64).all(|c| v4::Product32::get(&sums, c) == want[c]);
    println!("Product32 (v4) vs product_ref (weighed by the block weights): {}", if pok { "OK" } else { "FAIL" });
    i32::from(!(ok && sok && pok))
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
)))]
fn check_kernels(d: &Data, refs_skip: &[[[u64; 4]; SLOTS]], _refs_prod: &[Vec<u128>]) -> i32 {
    super::dev::check(d, refs_skip)
}

/// lvm2 W32-P: the protocol's RMFE (`keccak_gkr::rmfe`, both trees' copies) against the Lean truth probe's
/// `rmfeEmbed`/`rmfeProject` (a JSON of two integer lists), and the prototype's tables against it.
fn rmfe(path: &str) -> i32 {
    let text = std::fs::read_to_string(path).expect("JSON");
    let list = |key: &str| -> Vec<u128> {
        let at = text.find(&format!("\"{key}\"")).expect("key");
        let (open, close) = (at + text[at..].find('[').unwrap(), at + text[at..].find(']').unwrap());
        text[open + 1..close].split(',').map(|v| v.trim().parse().expect("integer")).collect()
    };
    let (embed, project) = (list("embed"), list("project"));
    let mut ok = match crate::lv::keccak_gkr::rmfe::check(&embed, &project) {
        Ok(()) => { println!("rmfe: emb/proj = Lean's (32 each), all 32^2 unit-vector identities hold"); true }
        Err(e) => { println!("rmfe: FAIL {e}"); false }
    };
    let r = &crate::lv::keccak_gkr::rmfe::RMFE;
    let t = (0..32).all(|i| EMB[i] == r.emb[i] && PROJ[i] == r.proj[i]) && ONES == r.ones;
    println!("w32 tables (EMB, PROJ, ONES) = rmfe: {}", if t { "OK" } else { "FAIL" });
    ok &= t;
    i32::from(!ok)
}
