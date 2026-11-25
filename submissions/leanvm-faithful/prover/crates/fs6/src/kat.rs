//! Known answers: every worked example of FORMAT6.md, byte for byte; §6's table and §7's counts; the PRF on 0-,
//! 103-, 104- and 239-byte queries under a fixed key (vectors from an independent Python Keccak-256); the nonce
//! rule; a skeleton run of the whole fixed schedule at a small shape whose bytes and queries match the counts.

use std::sync::Mutex;

use crate::codec::{self, E};
use crate::merkle::{self, Tree6};
use crate::oracle::{Local, Oracle};
use crate::params::{Level, P18, Shape};
use crate::schedule::{self, Item};
use crate::transcript::{self, Q0, Transcript};
use crate::{Digest, Trace};

/// An oracle that answers `00 01 … 1f` to everything and records the queries.
struct Const(Mutex<Vec<Vec<u8>>>);

impl Oracle for Const {
    fn ask(&self, q: &[u8]) -> Digest {
        self.0.lock().unwrap().push(q.to_vec());
        std::array::from_fn(|i| i as u8)
    }
    fn name(&self) -> &'static str {
        "const"
    }
}

fn key() -> [u8; 32] {
    std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(1))
}

fn hexd(s: &str) -> Digest {
    std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

/// §1: the 16 bytes `00 01 … 0f` are `c₀ = 0x0706050403020100`, `c₁ = 0x0f0e0d0c0b0a0908`.
#[test]
fn codec_example() {
    let b: Vec<u8> = (0..16).collect();
    assert_eq!(codec::get_e(&b), [0x0706050403020100, 0x0f0e0d0c0b0a0908]);
    let mut back = Vec::new();
    codec::put_e(&mut back, [0x0706050403020100, 0x0f0e0d0c0b0a0908]);
    assert_eq!(back, b);
}

/// §3: `q₀` is the 7 bytes `6C 76 6D 36 2F 31 00`; the first trace item ends at byte `1 + 8 + 7 + 32 = 48`; the
/// seed is `a₀ ‖ HDR` (v2.5), `168 + 16v` bytes (856 at `P18`).
#[test]
fn q0_seed_and_alignment() {
    assert_eq!(Q0, [0x6C, 0x76, 0x6D, 0x36, 0x2F, 0x31, 0x00]);
    assert_eq!((1 + 8 + Q0.len() + 32) % 8, 0);
    assert_eq!(1 + 8 + Q0.len() + 32, 48);
    let o = Local::keyed(&key());
    let hdr = schedule::header(&P18, 0, 262144, &[3; 32], &[0; 32], &[1; 32], None);
    let t = Transcript::start(&o, &hdr);
    let (_, tr) = t.finish();
    assert_eq!(tr[0].0, Q0.to_vec());
    assert_eq!(tr[0].1, o.ask(&Q0));
    assert_eq!(tr[1].0.len(), 168 + 16 * P18.phi_vars);
    assert_eq!(tr[1].0.len(), 856);
    assert_eq!(tr[1].0, [&tr[0].1[..], &hdr[..]].concat());
    assert_eq!(&hdr[88..120], &[1; 32], "vk at HDR offset 88");
    assert_eq!(tr[1].1, o.ask(&tr[1].0));
}

/// §4 ground-group example: query `st ‖ m₁ ‖ m₂ ‖ LE64(ν)`, 72 bytes; answer `00 … 1f` gives
/// `χ = (0x0706050403020100, 0x0f0e0d0c0b0a0908)` and PoW lane `0x1716151413121110` (in `[2^60, 2^61)`: passes at
/// `g ≤ 3`, fails at `g ≥ 4`, so at 5 as FORMAT6 says).
#[test]
fn ground_group_example() {
    let o = Const(Mutex::new(Vec::new()));
    let mut t = Transcript::start(&o, &[]);
    let st = t.state();
    let (m1, m2): (E, E) = ([1, 2], [3, 4]);
    t.absorb_e(&[m1, m2]);
    let chi = t.ground(3);
    let mut want = st.to_vec();
    codec::put_e(&mut want, m1);
    codec::put_e(&mut want, m2);
    want.extend_from_slice(&0u64.to_le_bytes());
    // the search asked a window from ν = 0; candidate 0 is the 72-byte query and it passes (answer 00 … 1f)
    let qs = o.0.lock().unwrap().clone();
    assert_eq!(qs[2], want);
    assert_eq!(chi, [0x0706050403020100, 0x0f0e0d0c0b0a0908]);
    let a: Digest = std::array::from_fn(|i| i as u8);
    assert_eq!(codec::pow_lane(&a), 0x1716151413121110);
    assert!(codec::pow_lane(&a) < 1 << 61 && codec::pow_lane(&a) >= 1 << 60);
    assert!(codec::pow_ok(&a, 1) && codec::pow_ok(&a, 3));
    assert!(!codec::pow_ok(&a, 4) && !codec::pow_ok(&a, 5));
    // the nonce is in BODY, absorbed last: BODY = m1 ‖ m2 ‖ LE64(0)
    let (body, tr) = t.finish();
    assert_eq!(body, want[32..].to_vec());
    assert_eq!(tr.len(), 3);
    assert_eq!(tr[2].0.len(), 72);
    assert_eq!(tr[2].0, want, "the trace holds the passing candidate only");
}

/// §4 `(α, β)` example: `absorb v_G, v_F, t₀, t₁, ν`; draw (104 bytes, `g = 10`) → `α`, state `st₁`; draw (query
/// `st₁`, 32 bytes) → `β`, state `st₂`.
#[test]
fn alpha_beta_example() {
    let o = Local::keyed(&key());
    let mut t = Transcript::start(&o, &[]);
    let st0 = t.state();
    let msgs: [E; 4] = [[1, 0], [2, 0], [3, 0], [4, 0]];
    t.absorb_e(&msgs);
    let alpha = t.ground(10);
    let st1 = t.state();
    let beta = t.draw();
    let st2 = t.state();
    let (body, tr) = t.finish();
    let (q1, a1) = &tr[2];
    assert_eq!(q1.len(), 104);
    assert_eq!(&q1[..32], &st0);
    let nonce = codec::le64(&q1[96..104]);
    assert_eq!(*a1, st1);
    assert_eq!(alpha, codec::chi(&st1));
    assert!(codec::pow_ok(&st1, 10));
    // the least nonce: no smaller one passes
    for nu in 0..nonce {
        let mut q = q1[..96].to_vec();
        q.extend_from_slice(&nu.to_le_bytes());
        assert!(!codec::pow_ok(&o.ask(&q), 10), "nonce {nu} < {nonce} passes");
    }
    assert_eq!(tr[3].0, st1.to_vec());
    assert_eq!(tr[3].1, st2);
    assert_eq!(beta, codec::chi(&st2));
    assert_eq!(body.len(), 4 * 16 + 8);
}

/// §4: a point of 18 coordinates is `G(5)`, `D(17)`: 18 queries, one nonce, each further draw from the previous state.
#[test]
fn point_of_18() {
    let o = Local::keyed(&key());
    let mut t = Transcript::start(&o, &[]);
    t.absorb_e(&[[9, 9]]);
    let mut pt = vec![t.ground(5)];
    pt.extend(t.draws(17));
    assert_eq!(pt.len(), 18);
    assert_eq!(t.nonces, 1);
    let (body, tr) = t.finish();
    assert_eq!(tr.len(), 2 + 18);
    assert_eq!(body.len(), 16 + 8);
    for k in 3..20 {
        assert_eq!(tr[k].0, tr[k - 1].1.to_vec(), "D's query is the previous state");
        assert_eq!(codec::chi(&tr[k].1), pt[k - 2]);
    }
}

/// §4: no draw outside a group, and a further draw needs an empty buffer.
#[test]
#[should_panic(expected = "no draw outside a group")]
fn no_draw_outside_a_group() {
    let o = Local::keyed(&key());
    let mut t = Transcript::start(&o, &[]);
    t.draw();
}

#[test]
#[should_panic(expected = "empty buffer")]
fn further_draw_needs_empty_buffer() {
    let o = Local::keyed(&key());
    let mut t = Transcript::start(&o, &[]);
    t.ground(1);
    t.absorb_e(&[[1, 1]]);
    t.draw();
}

/// §3 length rule, enforced at run time: a chain query of 64 bytes (st + 24 + nonce) is refused.
#[test]
#[should_panic(expected = "length rule")]
fn length_rule_enforced() {
    let o = Local::keyed(&key());
    let mut t = Transcript::start(&o, &[]);
    t.absorb_k(&[1, 2, 3]);
    t.ground(1);
}

/// §4: the nonce is the least passing one, also with a `usable` filter, and for any window split.
#[test]
fn least_nonce_is_least() {
    let o = Local::keyed(&key());
    for (g, plen) in [(1u32, 40usize), (3, 72), (6, 56), (9, 1064)] {
        let prefix: Vec<u8> = (0..plen).map(|i| (i * 13 + g as usize) as u8).collect();
        let usable = |e: E| e[1] & 3 != 0;
        let (nu, a, _) = transcript::least_nonce(&o, &prefix, g, &usable);
        let brute = (0u64..)
            .find(|&n| {
                let a = o.ask(&[&prefix[..], &n.to_le_bytes()].concat());
                codec::pow_ok(&a, g) && usable(codec::chi(&a))
            })
            .unwrap();
        assert_eq!(nu, brute, "g = {g}");
        assert_eq!(a, o.ask(&[&prefix[..], &nu.to_le_bytes()].concat()));
    }
}

/// §5 positions example: answer `00 … 1f` at level 0 (`ht = 21`).
#[test]
fn positions_example() {
    let a: Digest = std::array::from_fn(|i| i as u8);
    assert_eq!(merkle::positions(&[codec::chi(&a)], 21, 6), [131328, 532504, 115073, 1315344, 1097904, 493318]);
    // 6 per draw at levels 0–2, 7 at levels 3–4; draws 19, 8, 5, 3, 3
    assert_eq!(P18.levels.iter().map(|l| l.per_draw()).collect::<Vec<_>>(), [6, 6, 6, 7, 7]);
    assert_eq!(P18.levels.iter().map(|l| l.position_draws()).collect::<Vec<_>>(), [19, 8, 5, 3, 3]);
    // surplus positions of the last draw are dropped
    assert_eq!(merkle::positions(&[codec::chi(&a), codec::chi(&a)], 21, 7).len(), 7);
}

/// §5 path example: level 0, `p = 1234567`: bits 0–13 are `1,1,1,0,0,0,0,1,0,1,1,0,1,0`; the first node query is
/// `s₀ ‖ d₀`, the fourth `d₃ ‖ s₃`; the cap entry is `p >> 14 = 75`.
#[test]
fn path_example() {
    let p = 1234567usize;
    assert_eq!((0..14).map(|t| (p >> t) & 1).collect::<Vec<_>>(), [1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0]);
    let o = Local::keyed(&key());
    let leaf = vec![0xAB; 368];
    let sib: Vec<Digest> = (0..14u8).map(|i| [i + 1; 32]).collect();
    let mut tr: Trace = Vec::new();
    assert_eq!(merkle::opening_trace_asked(&o, p, &leaf, &sib, &mut tr), 75);
    assert_eq!(tr.len(), 15);
    assert_eq!(tr[0].0, leaf);
    let d = |k: usize| tr[k].1; // d_t = the answer before node query t + 1
    assert_eq!(tr[1].0, [&sib[0][..], &d(0)[..]].concat(), "first node query s₀ ‖ d₀");
    assert_eq!(tr[4].0, [&d(3)[..], &sib[3][..]].concat(), "fourth node query d₃ ‖ s₃");
    for (k, (q, a)) in tr.iter().enumerate() {
        assert_eq!(*a, o.ask(q), "answer {k}");
    }
}

/// §5 the tree: leaves, nodes, cap, siblings, and V's opening queries from stored nodes equal the asked ones.
#[test]
fn tree_cap_and_openings() {
    let o = Local::keyed(&key());
    let (ht, lv) = (6u32, 2u32);
    let leaf = |p: usize, b: &mut Vec<u8>| b.extend((0..256).map(|j| (p * 3 + j) as u8));
    let tree = Tree6::build(&o, ht, lv, &leaf);
    assert_eq!(tree.cap().len(), 4);
    // a naive tree
    let mut lvl: Vec<Digest> = (0..64)
        .map(|p| {
            let mut b = Vec::new();
            leaf(p, &mut b);
            o.ask(&b)
        })
        .collect();
    for _ in 0..ht - lv {
        lvl = lvl.chunks(2).map(|c| o.ask(&[&c[0][..], &c[1][..]].concat())).collect();
    }
    assert_eq!(tree.cap(), &lvl[..]);
    for p in [0usize, 5, 37, 63] {
        let mut b = Vec::new();
        leaf(p, &mut b);
        let (mut t1, mut t2) = (Vec::new(), Vec::new());
        tree.opening_trace(p, &b, &mut t1);
        let idx = merkle::opening_trace_asked(&o, p, &b, &tree.siblings(p), &mut t2);
        assert_eq!(t1, t2);
        assert_eq!(t1.last().unwrap().1, tree.cap()[idx], "the last answer is the cap entry");
    }
}

/// §6's table, §6.2's sub-counts, §6.3's core, §7's `qS` and `|π|`, and the length rule `fsLenOK` for `P18`.
#[test]
fn schedule_counts_p18() {
    let sh = &P18;
    let mut pending = 0;
    let mut in_group = false;
    let mut total = schedule::Tally::default();
    let mut rows = Vec::new();
    for (name, items) in schedule::fixed_parts(sh, true) {
        let (t, p) = schedule::tally_from(sh, &items, pending, in_group).unwrap();
        pending = p;
        in_group = true;
        rows.push((name.clone(), t.body, t.queries, t.nonces));
        if !name.starts_with("6.3") && !name.starts_with("6.4") {
            total.body += t.body;
            total.queries += t.queries;
            total.nonces += t.nonces;
            total.draws += t.draws;
            total.binds += t.binds;
            total.opening_queries += t.opening_queries;
        }
        assert!(schedule::fs_len_ok(&t), "{name}: length rule");
        total.chain_lengths.extend(t.chain_lengths);
    }
    let want = [
        ("6.1", 4_120, 26, 1),
        ("6.2", 27_120, 390, 368),
        ("6.3caller", 504, 13, 13),
        ("6.3core", 23_688, 298, 293),
        ("6.3link", 728, 31, 31),
        ("6.4ty", 3_488, 84, 84),
        ("6.4mb", 3_448, 53, 43),
        ("6.5", 8, 34, 1),
        ("6.6L0", 92_368, 1_702, 8),
        ("6.6L1", 33_088, 708, 6),
        ("6.6L2", 21_120, 446, 6),
        ("6.6L3", 15_520, 314, 6),
        ("6.6L4", 12_128, 248, 8),
    ];
    assert_eq!(rows, want.map(|(n, b, q, k)| (n.to_string(), b, q, k)));
    assert_eq!((total.body, total.queries, total.nonces), (205_472, 3_868, 404));
    assert_eq!((total.draws, total.binds, total.opening_queries), (589, 6, 3_273));
    // §6.2: 512 bytes before row 6, 26,608 from row 6 on
    let tb = schedule::tree_batch(sh);
    let (head, _) = schedule::tally_from(sh, &tb[..6], 16, true).unwrap();
    assert_eq!(head.body, 512);
    let (core, _) = schedule::tally_from(sh, &tb[6..], 0, true).unwrap();
    assert_eq!(core.body, 26_608);
    // §7 (v2.4, frozen): qS = 2 + 3,868 + 298 + 44 + 84 + 53 = 4,349; |π| = 824 + 229,160 + 1,232 + 3,488 + 3,448
    // = 238,152; nonces 404 + 293 + 44 + 84 + 43 = 868
    let all: Vec<Item> = schedule::fixed_parts(sh, true).into_iter().flat_map(|(_, v)| v).collect();
    let (a, _) = schedule::tally_from(sh, &all, 0, false).unwrap();
    assert_eq!((2 + a.queries, sh.hdr_len() + a.body, a.nonces), (4_349, 238_152, 868));
    assert_eq!(2 + total.queries + 298 + 44 + 84 + 53, 4_349);
    assert_eq!(total.body + 23_688, 229_160);
    assert_eq!(sh.hdr_len(), 824);
    assert!(schedule::fs_len_ok(&a), "fsLenOK over the whole schedule");
    assert!(4_349 <= sh.qv, "qS within qV");
    // §3: the δ group 88; bind queries after caps 4,128, 2,176, 1,120 (32 + 16ℓ + 32·2^c); ground queries after a
    // bind 40; every other chain query 32 or ≡ 8 (mod 16); the longest is the first bind, 4,128
    // v2.2's cost rule holds everywhere but §6.6 level 4's G(13) after the final E(12) (RT-transcript.md)
    let exceptions: Vec<_> = schedule::fixed_parts(sh, true)
        .iter()
        .flat_map(|(_, items)| schedule::bind_rule_exceptions(&schedule::tally_from(sh, items, 0, true).unwrap().0))
        .collect();
    assert!(exceptions.is_empty(), "{exceptions:?}");
    // §6.4b's fingerprint G(16) grinds on an empty buffer (40-byte query); §6.4's chain queries are 32 or ≡ 8 (16)
    let (mb, _) = schedule::tally_from(sh, &schedule::mini_bus(sh), 0, true).unwrap();
    assert_eq!(mb.ground_bufs[0], (16, 8));
    let (ty, _) = schedule::tally_from(sh, &schedule::typed_phases(sh), 0, true).unwrap();
    assert!(ty.chain_lengths.iter().chain(&mb.chain_lengths).all(|&l| l == 32 || l % 16 == 8));
    // §6.3 (v2.4): no group with g ≥ 15; caller and link queries 1,064 (after an E(64)), 440, 72, 40
    for items in [schedule::sponge_caller(sh), schedule::sponge_link(sh)] {
        let (t, _) = schedule::tally_from(sh, &items, 1_024, true).unwrap();
        assert!(t.ground_bufs.iter().all(|&(g, _)| g < 15) && t.chain_lengths.iter().all(|&l| l % 16 == 8));
        assert_eq!(t.chain_lengths[0], 1_064);
    }
    let cl = &total.chain_lengths;
    for want in [88usize, 4_128, 2_176, 1_120, 40] {
        assert!(cl.contains(&want), "{want}");
    }
    let binds = [4_128usize, 2_176, 1_120, 1_120]; // §6.5's bind is 32 bytes after §6.4b's last y (v2.3)
    assert!(cl.iter().all(|&l| l == 32 || l % 16 == 8 || binds.contains(&l)), "chain lengths");
    assert_eq!(*cl.iter().max().unwrap(), 4_128);
    // §8: a stream of 16 steps makes 1 + 2·15 signatures
    assert_eq!(1 + 2 * (16 - 1), 31);
    // §5 table: path queries 14, 14, 14, 13, 12; the cap bytes of §6.1
    assert_eq!(sh.levels.iter().map(|l| l.path()).collect::<Vec<_>>(), [14, 14, 14, 13, 12]);
    assert_eq!(sh.levels[0].cap_bytes(), 4_096);
}

/// §2 (v2.2): the header's layout (`vk` at 88, `accIn` at 120, `|HDR| = 136 + 16v`), `parseHdr`'s rules, `hdrOk`.
#[test]
fn header_layout() {
    let sh = &P18;
    let (h, vk) = ([7u8; 32], [8u8; 32]);
    let hdr = schedule::header(sh, 0, 262144, &h, &[0; 32], &vk, None);
    assert_eq!(hdr.len(), 136 + 16 * sh.phi_vars);
    assert_eq!(&hdr[..8], &[0x53, 0x6C, 0x76, 0x6D, 0x36, 0, 0, 1]);
    assert_eq!(hdr[0], b'S');
    assert_eq!(&hdr[88..120], &vk);
    assert!(hdr[120..].iter().all(|&b| b == 0), "accIn zero at b = 0 (§2.1)");
    let (x, rest) = schedule::parse_header(sh, &hdr).unwrap();
    assert!(rest.is_empty());
    assert_eq!((x.b, x.n, x.h, x.c_prev, x.vk), (0, 262144, h, [0; 32], vk));
    let l = keccak256::hash(&[&[0x4Cu8][..], &h, &262144u64.to_le_bytes()].concat());
    assert!(schedule::hdr_ok(&vk, &l, &x) && !schedule::hdr_ok(&[9; 32], &l, &x) && !schedule::hdr_ok(&vk, &h, &x));
    let mut bad = hdr.clone();
    bad[56] = 1; // b = 0 with c' ≠ 0
    assert!(schedule::parse_header(sh, &bad).is_none());
    let mut bad = hdr.clone();
    bad[8] = 2; // b ∉ {0, 1}
    assert!(schedule::parse_header(sh, &bad).is_none());
    let node = schedule::header(sh, 1, 262144, &h, &[9; 32], &vk, None);
    let x = schedule::parse_header(sh, &node).unwrap().0;
    assert_eq!(x.c_prev, [9; 32]);
    let c = keccak256::hash(&[&[0x4Eu8][..], &[9; 32], &l].concat());
    assert!(schedule::hdr_ok(&vk, &c, &x));
}

/// §4 bind `B` (v2.2): one query `st ‖ buf` whose value is ignored; the state moves; the next ground query is
/// `st' ‖ LE64(ν)`, 40 bytes; no further draw directly after a bind.
#[test]
fn bind_item() {
    let o = Local::keyed(&key());
    let mut t = Transcript::start(&o, &[]);
    let cap: Vec<Digest> = (0..128u8).map(|i| [i; 32]).collect();
    let st0 = t.state();
    t.absorb_cap(&cap);
    t.bind();
    let st1 = t.state();
    t.ground(18);
    t.draws(2);
    let (body, tr) = t.finish();
    assert_eq!(tr[2].0.len(), 4_128);
    assert_eq!(&tr[2].0[..32], &st0);
    assert_eq!(tr[2].1, st1);
    assert_eq!(tr[3].0.len(), 40);
    assert_eq!(&tr[3].0[..32], &st1);
    assert_eq!(body.len(), 4_096 + 8, "a bind writes nothing to BODY");
}

/// The PRF `Keccak-256(k ‖ q)` on 0-, 103-, 104- and 239-byte queries (1, 1, 2, 2 permutations), against vectors
/// from an independent Keccak-256 (`k_i = 7i + 1`, `q_i = 31i ⊕ 0xA5`).
#[test]
fn prf_vectors() {
    let o = Local::keyed(&key());
    for (n, want) in [
        (0usize, "99d1533d5b1f52d46ed078f873d9e797591d47911c8622346cba44a38b23c06b"),
        (103, "a4ba618092f332e9048ff740f6fa4305bf51b5b1adfebdf7c896312ee813452b"),
        (104, "3913ae29a58b62726b99621f00b73af350943cf39dc430fe6987ad7c0b04365d"),
        (239, "fa7e05dde3c2eb6d1e346b6a4b866ad80edee8a553f46559802eacca168f2f92"),
    ] {
        let q: Vec<u8> = (0..n).map(|i| (i as u8).wrapping_mul(31) ^ 0xA5).collect();
        assert_eq!(o.ask(&q), hexd(want), "{n} bytes");
        assert_eq!(crate::oracle::perms(n), [1, 1, 2, 2][[0, 103, 104, 239].iter().position(|&m| m == n).unwrap()]);
        // the nonce path hashes the prefix once: same answers
        if n >= 8 {
            let mut out = [[0u8; 32]];
            o.ask_nonces_here(&q[..n - 8], codec::le64(&q[n - 8..]), &mut out);
            assert_eq!(out[0], hexd(want));
        }
    }
}

/// A small shape for an end-to-end skeleton run: three levels (FORMAT6 v2.2 is generic in their number), heights
/// 10, 9, 8, low grinds; P18's counts otherwise.
fn test_shape() -> Shape {
    const fn lvl(ht: u32, lv: u32, leaf_bytes: usize, queries: usize, fold: usize, cols: u32, gq: u32) -> Level {
        Level {
            ht,
            lv,
            leaf_bytes,
            queries,
            fold,
            log_msg_cols: cols,
            log_inv_rate: ht - cols,
            agreement_end: 0,
            grind_fold: 3,
            grind_ood: 4,
            grind_query: gq,
        }
    }
    static LEVELS: [Level; 3] = [lvl(10, 3, 368, 9, 6, 8, 4), lvl(9, 3, 256, 5, 4, 6, 3), lvl(8, 2, 256, 4, 4, 5, 3)];
    Shape { levels: &LEVELS, grind_batch: 4, ..P18 }
}

/// The skeleton executor at a small shape: `|BODY|`, the trace and the nonces equal the schedule's counts; every
/// query after `q₀` is a whole number of lanes; the run is a function of its inputs (two runs, same bytes).
#[test]
fn skeleton_matches_counts() {
    let sh = test_shape();
    let o = Local::keyed(&key());
    let items: Vec<Item> = schedule::fixed_parts(&sh, true).into_iter().flat_map(|(_, v)| v).collect();
    let (t, _) = schedule::tally_from(&sh, &items, 0, false).unwrap();
    assert!(schedule::fs_len_ok(&t));
    let run = || {
        let hdr = schedule::header(&sh, 0, 6, &[1; 32], &[0; 32], &[2; 32], None);
        let mut tr = Transcript::start(&o, &hdr);
        schedule::run_skeleton(&mut tr, &sh, &items, 77);
        let nonces = tr.nonces;
        let (body, trace) = tr.finish();
        (body, trace, nonces)
    };
    let (body, trace, nonces) = run();
    assert_eq!(body.len(), t.body);
    assert_eq!(trace.len(), 2 + t.queries);
    assert_eq!(t.binds, 2 + sh.levels.len() - 1, "a bind after every cap and before G(17)");
    assert_eq!(nonces, t.nonces);
    assert!(trace[1..].iter().all(|(q, _)| q.len() % 8 == 0));
    for (q, a) in trace.iter().step_by(97) {
        assert_eq!(*a, o.ask(q));
    }
    let again = run();
    assert_eq!((again.0, again.1), (body, trace));
}
