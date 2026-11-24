//! FORMAT6 §6: the schedule as item lists, their counts (`|BODY|`, queries, nonces: §6's table and §7's `qS`), the
//! static length rule `fsLenOK` (§3), and a skeleton executor that runs a schedule on a [`Transcript`] with dummy
//! messages and real trees (every byte count, query, nonce and opening at the real shape, no proof mathematics).
//!
//! FORMAT6 v2.2. Frozen and here: §6.1, §6.2 (TOY2 passed), §6.3's core, §6.5, §6.6 (with the binds `B`). Not frozen (§T): the sponge
//! caller and link, the typed phases, the mini-bus, the claims after 16; the skeleton leaves them out.

use crate::codec::E;
use crate::merkle::{self, Tree6};
use crate::params::Shape;
use crate::transcript::{FORBIDDEN_CHAIN_LENGTHS, Transcript};
use crate::Digest;

/// A schedule item (FORMAT6 §6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Item {
    /// `k` scalars read and absorbed.
    E(usize),
    /// `k` words.
    K(usize),
    /// Level `i`'s cap.
    Cap(usize),
    /// A ground group of `g` bits (nonce, one draw).
    G(u32),
    /// `k` further draws.
    D(usize),
    /// Level `i`'s openings (not absorbed).
    Open(usize),
    /// A bind draw (v2.2): value discarded, only the state moves.
    B,
}
use Item::*;

/// A sumcheck round `R(n, g)`: `E(n)` then `G(g)`.
fn round(v: &mut Vec<Item>, n: usize, g: u32) {
    v.push(E(n));
    v.push(G(g));
}

/// §6.1: `CAP(0) · B · G(g_ood[0]), D(24) → z₀ ∈ E^25 · E(1) → y₀`.
pub fn commitment(sh: &Shape) -> Vec<Item> {
    vec![Cap(0), B, G(sh.levels[0].grind_ood), D(sh.stack_log as usize - 1), E(1)]
}

/// §6.2 rows 6–10 (the reduction core) at batch `κ`: `G(3), D(5)`; `E(1)`; 12 layers of `E(47) · G(6) · (κ−3)` eq
/// rounds `R(2,2)` · 11 plain `R(3,2)` · `E(3) · G(2)`; 6 × `R(2,2)`, `E(1)`; `4 + top + 6` input rounds `R(2,2)`,
/// `E(64)`. With `top = false` and `κ_s` it is §6.3's core.
pub fn reduction_core(kappa: u32, top_bit: bool) -> Vec<Item> {
    let mut v = vec![G(3), D(5), E(1)];
    for _ in 0..12 {
        v.extend([E(47), G(6)]);
        for _ in 0..kappa - 3 {
            round(&mut v, 2, 2);
        }
        for _ in 0..11 {
            round(&mut v, 3, 2);
        }
        v.extend([E(3), G(2)]);
    }
    for _ in 0..6 {
        round(&mut v, 2, 2);
    }
    v.push(E(1));
    for _ in 0..10 + usize::from(top_bit) {
        round(&mut v, 2, 2);
    }
    v.push(E(64));
    v
}

/// §6.2: rows 1–5 (`K(4)`; `G(5), D(17)` → `ρ`; `E(8)`; `G(1)` → `u`; `E(21)`), then the core at `κ` with the top bit.
pub fn tree_batch(sh: &Shape) -> Vec<Item> {
    let mut v = vec![K(4), G(5), D(sh.log_blocks as usize - 1), E(8), G(1), E(21)];
    v.extend(reduction_core(sh.kappa, true));
    v
}

/// §6.3's core (`κ_s`, no top bit round).
pub fn sponge_core(sh: &Shape) -> Vec<Item> {
    reduction_core(sh.kappa_s, false)
}

/// §6.5: `B`, `G(17), D(32)`: the two ring-switch maps (16 each, the ground draw first) and `λ₀`.
pub fn ring_switch(sh: &Shape) -> Vec<Item> {
    vec![B, G(sh.grind_batch), D(32)]
}

/// §6.6 level `i`.
pub fn opening_level(sh: &Shape, i: usize) -> Vec<Item> {
    let l = &sh.levels[i];
    let mut v = Vec::new();
    for _ in 0..l.fold {
        v.extend([E(4), G(l.grind_fold), D(1)]);
    }
    let d = l.position_draws();
    if i + 1 < sh.levels.len() {
        let nu = l.log_msg_cols as usize;
        // v2.2: the high part before the cap, a bind after it, and the OOD grind of the level the point binds (i + 1)
        let g_ood = sh.levels[i + 1].grind_ood;
        v.extend([E(l.fold), Cap(i + 1), B, G(g_ood), D(nu - 1), E(1), G(l.grind_query), D(d - 1), D(1), Open(i)]);
    } else {
        v.extend([E(sh.final_coeffs), G(l.grind_query), D(d - 1), Open(i)]);
        for _ in 0..sh.tail_rounds {
            round(&mut v, 2, sh.grind_tail);
        }
    }
    v
}

/// §6.3's caller (v2.4, `spCaller6 13`): `13 × G(1)` (the instance point `r`), `E(25)` (the output lanes `v`).
/// 13 draws, 13 nonces, 504 bytes.
pub fn sponge_caller(sh: &Shape) -> Vec<Item> {
    let mut v = vec![G(1); sh.kappa_s as usize];
    v.push(E(25));
    v
}

/// §6.3's link (v2.4, `ksLinkProgE2 13 xl rows`): `18 × G(1)` (`ρ ∈ E^13`, then the lane point `λ ∈ E^5`),
/// 13 plain `R(2, 2)` (the shift sumcheck), `E(4)` (`Y, in, M, X` at `ρ'`). 31 draws, 31 nonces, 728 bytes.
pub fn sponge_link(sh: &Shape) -> Vec<Item> {
    let hk = sh.kappa_s as usize;
    let mut v = vec![G(1); hk + 5];
    for _ in 0..hk {
        round(&mut v, 2, 2);
    }
    v.push(E(4));
    v
}

/// §6.4a (v2.3), the typed phases: `20 × G(1)` (`τ`); 20 eq-mode `R(2, 2)`; `E(3)`; `G(2)` (`γ`); 21 plain
/// `R(2, 2)`; `E(4)`; `E(4)`; `sh.relayout` (19, `P17`: 18) plain `R(2, 2)`; `E(1)`; `2 × G(1)` (`κ`);
/// `E(phiVars + 1)`; `G(6)` (`t`). 84 draws, 84 nonces, 3,488 bytes (`P17`: 83, 83, 3,448).
pub fn typed_phases(sh: &Shape) -> Vec<Item> {
    use crate::params::{TY_X, TY_Y};
    let mut v = vec![G(1); TY_X];
    for _ in 0..TY_X {
        round(&mut v, 2, 2);
    }
    v.extend([E(3), G(2)]);
    for _ in 0..TY_Y {
        round(&mut v, 2, 2);
    }
    v.extend([E(4), E(4)]);
    for _ in 0..sh.relayout {
        round(&mut v, 2, 2);
    }
    v.extend([E(1), G(1), G(1), E(sh.phi_vars + 1), G(6)]);
    v
}

/// §6.4b (v2.3), the mini-bus: `G(16), D(4)` (`α₀ … α₃, β`); `E(2)` (roots); steps `k = 0 … 5`: `G(2)` (`λ_k`),
/// `2k` eq-mode `R(4, 3)`, `E(4) × 3` (children), `G(2), D(1)` (`y_k`; the last step `G(3), D(1)`).
/// 53 draws, 43 nonces, 3,448 bytes.
pub fn mini_bus(_sh: &Shape) -> Vec<Item> {
    use crate::params::MB_STEPS;
    let mut v = vec![G(16), D(4), E(2)];
    for k in 0..MB_STEPS {
        v.push(G(2));
        for _ in 0..2 * k {
            round(&mut v, 4, 3);
        }
        v.extend([E(4), E(4), E(4), G(if k + 1 == MB_STEPS { 3 } else { 2 }), D(1)]);
    }
    v
}

/// The schedule in proof order (FORMAT6 v2.4, frozen): §6.1, §6.2, §6.3 (caller, core, link), §6.4a, §6.4b,
/// §6.5, §6.6 levels. `with_sponge_core = false` leaves out §6.3's core only (as before v2.4).
pub fn fixed_parts(sh: &Shape, with_sponge_core: bool) -> Vec<(String, Vec<Item>)> {
    let mut v = vec![("6.1".to_string(), commitment(sh)), ("6.2".to_string(), tree_batch(sh))];
    v.push(("6.3caller".to_string(), sponge_caller(sh)));
    if with_sponge_core {
        v.push(("6.3core".to_string(), sponge_core(sh)));
    }
    v.push(("6.3link".to_string(), sponge_link(sh)));
    v.push(("6.4ty".to_string(), typed_phases(sh)));
    v.push(("6.4mb".to_string(), mini_bus(sh)));
    v.push(("6.5".to_string(), ring_switch(sh)));
    for i in 0..sh.levels.len() {
        v.push((format!("6.6L{i}"), opening_level(sh, i)));
    }
    v
}

/// Counts of a list of items.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    pub body: usize,
    pub queries: usize,
    pub nonces: usize,
    pub draws: usize,
    pub binds: usize,
    pub opening_queries: usize,
    /// `(g, |buf|)` at every ground query (v2.2.1 rule: `g ≥ 15 ⟹ |buf| ≤ 56`).
    pub ground_bufs: Vec<(u32, usize)>,
    /// Every chain query's length, in order (for the length rule).
    pub chain_lengths: Vec<usize>,
}

/// Count `items`, continuing from `pending` absorbed bytes and group state; `Err` if a further draw would have a
/// non-empty buffer or no group.
pub fn tally_from(sh: &Shape, items: &[Item], mut pending: usize, mut in_group: bool) -> Result<(Tally, usize), String> {
    let mut t = Tally::default();
    for (k, it) in items.iter().enumerate() {
        match *it {
            E(n) => {
                t.body += 16 * n;
                pending += 16 * n;
            }
            K(n) => {
                t.body += 8 * n;
                pending += 8 * n;
            }
            Cap(i) => {
                t.body += sh.levels[i].cap_bytes();
                pending += sh.levels[i].cap_bytes();
            }
            G(g) => {
                if !(1..=23).contains(&g) {
                    return Err(format!("item {k}: G({g})"));
                }
                t.body += 8;
                t.ground_bufs.push((g, pending + 8));
                t.chain_lengths.push(32 + pending + 8);
                pending = 0;
                t.nonces += 1;
                t.queries += 1;
                t.draws += 1;
                in_group = true;
            }
            D(n) => {
                if n > 0 && (pending != 0 || !in_group) {
                    return Err(format!("item {k}: D({n}) with {pending} bytes pending or outside a group"));
                }
                t.chain_lengths.extend(std::iter::repeat_n(32, n));
                t.queries += n;
                t.draws += n;
            }
            B => {
                t.chain_lengths.push(32 + pending);
                pending = 0;
                t.queries += 1;
                t.binds += 1;
                in_group = false;
            }
            Open(i) => {
                let l = &sh.levels[i];
                t.body += l.queries * l.opening_bytes();
                t.queries += l.queries * (1 + l.path());
                t.opening_queries += l.queries * (1 + l.path());
            }
        }
    }
    Ok((t, pending))
}

/// `fsLenOK` of `P18` (and of `P17`: the same leaves): no chain query has length 64, 256 or 368 (and none exceeds `2^20`).
pub fn fs_len_ok(t: &Tally) -> bool {
    t.chain_lengths.iter().all(|l| !FORBIDDEN_CHAIN_LENGTHS.contains(l) && *l <= 1 << 20)
}

/// `fsLenOK` of any shape (FORMAT6 §3: per `Shape`): no chain query of a leaf's or a node's length.
pub fn fs_len_ok_for(sh: &Shape, t: &Tally) -> bool {
    let f = sh.forbidden_lengths();
    t.chain_lengths.iter().all(|l| !f.contains(l) && *l <= 1 << 20)
}

/// v2.2.1's cost rule (§4 "Rule for §T"): a group with `g ≥ 15` must grind on `|buf| ≤ 56` (`buf` with the
/// nonce). Returns the `(g, |buf|)` of the groups that do not (none in `P18`'s fixed parts; level 4's `G(13)` on
/// 200 bytes is below the threshold; at `P17` level 4's `G(18)` on 136 bytes, the one exception FORMAT6 v2.6 §4
/// lists). Not a soundness condition (`V` never checks it).
pub fn bind_rule_exceptions(t: &Tally) -> Vec<(u32, usize)> {
    t.ground_bufs.iter().copied().filter(|&(g, b)| g >= 15 && b > 56).collect()
}

// ------------------------------------------------------------------ skeleton executor

/// `splitmix64`.
pub fn mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Word `j` of leaf `p` of a skeleton tree seeded with `seed`.
fn leaf_word(seed: u64, p: usize, j: usize) -> u64 {
    mix(seed ^ mix(((p as u64) << 8) | j as u64))
}

/// The bytes of leaf `p` of a skeleton tree at level `i` (`leaf_bytes / 8` words).
pub fn skeleton_leaf(sh: &Shape, i: usize, seed: u64, p: usize, b: &mut Vec<u8>) {
    for j in 0..sh.levels[i].leaf_bytes / 8 {
        b.extend_from_slice(&leaf_word(seed, p, j).to_le_bytes());
    }
}

/// What a skeleton run did.
#[derive(Debug, Default)]
pub struct SkeletonReport {
    pub tree_s: f64,
    pub grind_candidates: u64,
}

/// Run `items` on `t` with dummy messages (functions of the chain state and a counter) and real trees over
/// skeleton leaves (seeded with the chain state when their cap is sent): every query and byte of the real schedule.
/// `extra_seed` enters every tree seed (the driver passes `σ_leaf`'s hash, so it is used as the real `STREAM` is).
pub fn run_skeleton(t: &mut Transcript, sh: &Shape, items: &[Item], extra_seed: u64) -> SkeletonReport {
    let mut rep = SkeletonReport::default();
    let mut trees: Vec<Option<(Tree6, u64)>> = (0..sh.levels.len()).map(|_| None).collect();
    let mut group: Vec<E> = Vec::new();
    let mut ctr = 0u64;
    let st_word = |t: &Transcript| crate::codec::digest_words(&t.state())[0];
    for it in items {
        match *it {
            E(n) => {
                let s = st_word(t);
                let es: Vec<E> = (0..n)
                    .map(|_| {
                        ctr += 2;
                        [mix(s ^ ctr), mix(s ^ (ctr + 1))]
                    })
                    .collect();
                t.absorb_e(&es);
            }
            K(n) => {
                let s = st_word(t);
                let ws: Vec<u64> = (0..n)
                    .map(|_| {
                        ctr += 1;
                        mix(s ^ ctr)
                    })
                    .collect();
                t.absorb_k(&ws);
            }
            Cap(i) => {
                let seed = mix(st_word(t) ^ extra_seed ^ (i as u64) << 56);
                let l = &sh.levels[i];
                let t0 = std::time::Instant::now();
                let tree = Tree6::build(t.oracle(), l.ht, l.lv, &|p, b: &mut Vec<u8>| skeleton_leaf(sh, i, seed, p, b));
                rep.tree_s += t0.elapsed().as_secs_f64();
                t.absorb_cap(tree.cap());
                trees[i] = Some((tree, seed));
            }
            G(g) => {
                group.clear();
                group.push(t.ground(g));
            }
            D(n) => group.extend(t.draws(n)),
            B => t.bind(),
            Open(i) => {
                let l = &sh.levels[i];
                let ps = merkle::positions(&group[..l.position_draws()], l.ht, l.queries);
                let (tree, seed) = trees[i].take().expect("a level is opened after its cap");
                t.open(&tree, &ps, &|p, b: &mut Vec<u8>| skeleton_leaf(sh, i, seed, p, b));
            }
        }
    }
    rep.grind_candidates = t.candidates;
    rep
}

/// `HDR` (§2, v2.2): magic, `b`, `n`, `h`, `c'`, `vk`, `accIn` (`v` points and `y`; zero unless given: §2.1).
pub fn header(sh: &Shape, b: u64, n: u64, h: &Digest, c_prev: &Digest, vk: &Digest, acc_in: Option<&[E]>) -> Vec<u8> {
    let mut v = Vec::with_capacity(sh.hdr_len());
    v.extend_from_slice(&MAGIC);
    v.extend_from_slice(&b.to_le_bytes());
    v.extend_from_slice(&n.to_le_bytes());
    v.extend_from_slice(h);
    v.extend_from_slice(c_prev);
    v.extend_from_slice(vk);
    let zero = vec![[0u64; 2]; sh.phi_vars + 1];
    let acc = acc_in.unwrap_or(&zero);
    assert_eq!(acc.len(), sh.phi_vars + 1, "accIn is v points and y");
    for &e in acc {
        crate::codec::put_e(&mut v, e);
    }
    assert_eq!(v.len(), sh.hdr_len());
    v
}

/// `53 6C 76 6D 36 00 00 01`: `"Slvm6"`, 0, 0, version 1.
pub const MAGIC: [u8; 8] = [0x53, 0x6C, 0x76, 0x6D, 0x36, 0x00, 0x00, 0x01];

/// A parsed `HDR`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hdr {
    pub b: u64,
    pub n: u64,
    pub h: Digest,
    pub c_prev: Digest,
    pub vk: Digest,
    pub acc_in: Vec<E>,
}

/// `parseHdr`: magic, `b ∈ {0, 1}`, `b = 0 ⟹ c' = 0^32`; `None` otherwise (the `n` check is the caller's: `V_S`
/// rejects `n ≠ 2^log_blocks`). Returns the header and the rest (`BODY`).
pub fn parse_header<'a>(sh: &Shape, pi: &'a [u8]) -> Option<(Hdr, &'a [u8])> {
    if pi.len() < sh.hdr_len() || pi[..8] != MAGIC {
        return None;
    }
    let u = |o: usize| u64::from_le_bytes(pi[o..o + 8].try_into().unwrap());
    let (b, n) = (u(8), u(16));
    let h: Digest = pi[24..56].try_into().unwrap();
    let c_prev: Digest = pi[56..88].try_into().unwrap();
    let vk: Digest = pi[88..120].try_into().unwrap();
    if b > 1 || (b == 0 && c_prev != [0; 32]) {
        return None;
    }
    let acc_in = (0..=sh.phi_vars).map(|k| crate::codec::get_e(&pi[120 + 16 * k..])).collect();
    Some((Hdr { b, n, h, c_prev, vk, acc_in }, &pi[sh.hdr_len()..]))
}

/// `hdrOk vk c x` (§2, v2.2): `x.vk = vk` and the statement check: `L = leafStmt h n`; `b = 0`: `c = L`;
/// `b = 1`: `c = nodeStmt c' L` (`leafStmt h n = Keccak-256(0x4C ‖ h ‖ u64 n)`, `nodeStmt = Keccak-256(0x4E ‖ c' ‖ L)`).
pub fn hdr_ok(vk: &Digest, c: &Digest, x: &Hdr) -> bool {
    x.vk == *vk && hdr_statement(x) == *c
}

/// The statement a header proves.
pub fn hdr_statement(x: &Hdr) -> Digest {
    let l = keccak256::hash(&[&[0x4Cu8][..], &x.h, &x.n.to_le_bytes()].concat());
    if x.b == 0 { l } else { keccak256::hash(&[&[0x4Eu8][..], &x.c_prev, &l].concat()) }
}
