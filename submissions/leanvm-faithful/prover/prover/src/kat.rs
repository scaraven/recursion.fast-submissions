//! Known-answer tests run by the binary itself (`kat`, `kat prf KEYHEX`): Keccak-256, the committed-data leaf
//! (`.contract/tests/vectors/data_root.json`), the signed-proof format and `SigOk`, and the local PRF against
//! the service's `QUERY` (PROVER.md §3: 0-, 103-, 104- and 239-byte queries).

use crate::format;
use crate::keccak::{self, Digest};
use crate::stream::{hex, unhex32};

/// `(n, dataRoot, leafStmt)` of `tests/vectors/data_root.json` (data byte `i` = `i mod 256`).
const DATA_ROOT: [(u64, &str, &str); 9] = [
    (0, "0000000000000000000000000000000000000000000000000000000000000000", "e5cccee57d4d4929ba748848efc9a66adafaade38cc37f8942d5bd5222a53b41"),
    (1, "09910f8c671ec97437b818fd5a1cb7f10ce4be81bf37778b0605b381eaabbe69", "949bd35e15ea565d678b0a51a067a7e8c431127c395d845d86ae2f9654978261"),
    (2, "a8886ea246bda7de84ecc698aa1cc03cf96654a74818887a43b3d042e5935020", "a7f68d0c19abd06304d01c284cb4f3d972eca094de930e607179037399b28e86"),
    (3, "e05b7300eecd28cd7e31a9d377deea6030b49cf9bfd08b0b47c132230812615b", "44f3a6c107823c2b42c86ae9f96a120d212a10a429bcd4ed64a2a0d513749050"),
    (4, "55c3ed43367f2313bd98059444f498d7ad3efb1aa34846e9543dde3a414085b1", "954cd3e680062826d0744b03ef59dbf53a9e7d55d694c46a5627e45d67a6e45f"),
    (5, "b2271079ecba02c30b299a5659f8b64cad48f697d2c565a754cfede0427a9420", "5bc0a00cd566ebca604dcafd2a36317266aa429c8bd6d24426b81af7b81ff428"),
    (6, "259aa413be633639776254e69323bc335fc8647907e6b499ddbff7b98d92d460", "96e3c271c4b595302742c871508c521bb02568993a17455c7355c22b6af7480f"),
    (7, "5387590c6b14b2b1cea975eeb354600cb4154a9c45a4ff17da5137526afc592b", "fcb369adca4122c5fc1174326ca70899296906b5172dcee56324e4b371c7d191"),
    (9, "b7c34972d370a3ea7942cc7cf246cdf40dbd585093f48144944bb6f2892a9f1c", "f6d213f1b8205192e8445bbbf22686a6d6ed97d214530d290572be8f6f9d400a"),
];

fn check(ok: bool, what: &str, fails: &mut u32) {
    println!("kat {what}: {}", if ok { "ok" } else { "FAIL" });
    *fails += u32::from(!ok);
}

pub fn run_all() -> i32 {
    let mut fails = 0;
    let d = |s: &str| unhex32(s).unwrap();
    check(keccak::keccak256(b"") == d("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), "keccak256 empty", &mut fails);
    check(keccak::keccak256(b"abc") == d("4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"), "keccak256 abc", &mut fails);
    // multi-block sponge: a 300-byte message hashed whole and in pieces
    let m: Vec<u8> = (0..300u32).map(|i| (i * 7) as u8).collect();
    let mut h = keccak::Keccak256::new();
    h.update(&m[..135]).update(&m[135..137]).update(&m[137..]);
    check(h.finalize() == keccak::keccak256(&m), "keccak256 streaming", &mut fails);
    let mut all = true;
    for (n, root, stmt) in DATA_ROOT {
        let xs: Vec<u8> = (0..32 * n).map(|i| i as u8).collect();
        let r = keccak::data_root(&xs);
        all &= r == d(root) && keccak::leaf_stmt(&r, n) == d(stmt);
    }
    check(all, "dataRoot/leafStmt (data_root.json, 9 vectors)", &mut fails);
    let m: Digest = std::array::from_fn(|i| i as u8 ^ 0x5A);
    let (vk, sig) = format::toy_sign(7, &m);
    let mut bad = sig.clone();
    bad.ots[0][0] ^= 1;
    check(format::sig_ok(&vk, &m, &sig) && !format::sig_ok(&vk, &m, &bad), "SigOk (toy signer)", &mut fails);
    let p = format::Signed { pi: vec![1, 2, 3], tr: vec![(vec![9; 5], [4; 32])], sig };
    let f = format::to_file(&p);
    let mut longer = f.clone();
    longer.push(0);
    check(
        format::from_file(&f).as_ref() == Some(&p) && format::from_file(&longer).is_none() && f.len() == 8 + 3 + 8 + (8 + 5 + 32) + 8 + 4768,
        "signed-proof file round trip (strict)",
        &mut fails,
    );
    fails += fs6_kats();
    i32::from(fails > 0)
}

/// FORMAT6's examples and counts, through this build (the crate's unit tests hold the full set: `cargo test -p fs6`).
fn fs6_kats() -> u32 {
    use fs6::oracle::Oracle;
    let mut fails = 0;
    let a: Digest = std::array::from_fn(|i| i as u8);
    let e = fs6::codec::chi(&a);
    check(
        e == [0x0706050403020100, 0x0f0e0d0c0b0a0908]
            && fs6::codec::pow_lane(&a) == 0x1716151413121110
            && fs6::codec::pow_ok(&a, 3)
            && !fs6::codec::pow_ok(&a, 4),
        "FORMAT6 §1/§4 codec, chi, PoW lane",
        &mut fails,
    );
    check(
        fs6::merkle::positions(&[e], 21, 6) == [131328, 532504, 115073, 1315344, 1097904, 493318],
        "FORMAT6 §5 positions example",
        &mut fails,
    );
    let sh = &fs6::params::P18;
    let mut tot = (0, 0, 0);
    let mut pending = 0;
    let mut ok = true;
    for (name, items) in fs6::schedule::fixed_parts(sh, false) {
        let (t, p) = fs6::schedule::tally_from(sh, &items, pending, true).unwrap();
        pending = p;
        ok &= fs6::schedule::fs_len_ok(&t);
        let _ = name;
        tot = (tot.0 + t.body, tot.1 + t.queries, tot.2 + t.nonces);
    }
    // v2.4 (frozen): everything but §6.3's core (sponge caller + link 1,232 B / 44 / 44, typed 3,488 / 84 / 84,
    // mini-bus 3,448 / 53 / 43); with the core (23,688 / 298 / 293) and HDR: qS 4,349, |π| 238,152, 868 nonces
    check(
        ok && tot == (205_472 + 1_232 + 3_488 + 3_448, 3_868 + 44 + 84 + 53, 404 + 44 + 84 + 43),
        "FORMAT6 v2.4 schedule without §6.3's core: 213,640 B, 4,049 queries, 575 nonces, fsLenOK",
        &mut fails,
    );
    let k: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(1));
    let o = fs6::oracle::Local::keyed(&k);
    let want = [
        (0usize, "99d1533d5b1f52d46ed078f873d9e797591d47911c8622346cba44a38b23c06b"),
        (103, "a4ba618092f332e9048ff740f6fa4305bf51b5b1adfebdf7c896312ee813452b"),
        (104, "3913ae29a58b62726b99621f00b73af350943cf39dc430fe6987ad7c0b04365d"),
        (239, "fa7e05dde3c2eb6d1e346b6a4b866ad80edee8a553f46559802eacca168f2f92"),
    ];
    let all = want.iter().all(|&(n, w)| {
        let q: Vec<u8> = (0..n).map(|i| (i as u8).wrapping_mul(31) ^ 0xA5).collect();
        o.ask(&q) == unhex32(w).unwrap()
    });
    check(all, "PRF Keccak-256(k ‖ q) at 0/103/104/239 B (fixed key, independent vectors)", &mut fails);
    fails
}

/// `kat prf KEYHEX`: the local PRF against `QUERY` of the service at `$RF_ORACLE` (whose key is `KEYHEX`, e.g.
/// from its `replay` line).
pub fn run_prf(key_hex: &str) -> i32 {
    let Some(k) = unhex32(key_hex) else {
        eprintln!("kat prf: KEYHEX is 64 hex characters");
        return 2;
    };
    let path = std::env::var("RF_ORACLE").unwrap_or_else(|_| "/run/rf/oracle.sock".into());
    let svc = crate::service::Service::connect(&path).unwrap_or_else(|e| crate::service::fatal(&e));
    match crate::stream::prf_kat(&crate::oracle::Local::keyed(&k), &svc) {
        Ok(()) => {
            println!("kat prf: local PRF = QUERY at 0, 103, 104, 239 bytes: ok (vk {})", hex(&svc.vk()));
            0
        }
        Err(e) => {
            println!("kat prf: FAIL: {e}");
            1
        }
    }
}
