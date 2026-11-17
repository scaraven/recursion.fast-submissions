//! The recursion witness of a `b = 1` proof (WP-15b; BLUEPRINT §2.2, §3.1, §4.2, §11 A2/A3): from the left
//! child's signed proof `(π', tr', σ')`:
//!
//! - **the stream** `Σ` = the lanes of `pad10*1(0x54 ‖ traceBytes tr')` (the bytes `traceDigest tr'` hashes, with
//!   Keccak-256's padding): KS row `i < B` absorbs lanes `17i … 17i + 16` (`C_rec`'s `M_l[i] = Σ[17i + l]`),
//!   rows `B … R − 1` absorb zero; so `Y` of row `B − 1` is `traceDigest tr'`;
//! - **`σ'`** as the stream block's column 17 (R11, S2GM: `C_main`'s `S + 17·2^14`; was `C_rec`'s): the 597 lanes of `idx ‖ ots ‖ path` (FORMAT.md's signature words);
//! - **KS rows `≥ R`** (messages `X`, padded blocks as 17 lanes; `R = ks_split`: `2^rec` at P8, 15,360 at KS14's P20),
//!   in this order:
//!   - 133 × 3 WOTS chain steps, chain-major: row `R + 3i + (s − 1)` hashes `wotsStep j i (s − 1) a_s` with
//!     `a_s` = the previous step's output if `d_i + 1 < s`, else `ots_i` (the selection of WP-12's
//!     `wots_chain_sound`; `d = wotsDigits (traceDigest tr')`, `j = σ'.idx`); chain `i` ends at step 3's output
//!     if `d_i < 3`, else at `ots_i`;
//!   - rows `R + 399 … R + 430`: the key leaf `0x4B ‖ enc64 j ‖ end_0 ‖ … ‖ end_132` (32 blocks, `cont` inside);
//!   - rows `R + 431 + t`, `t < 16`: `sigNode` of the current value and `path[t]`, ordered by bit `t` of `j`;
//!   - row `R + 447`: `leafStmt h' n'`; row `R + 448`: `nodeStmt c_L' (leafStmt h' n')` (both for either `b'`);
//!   - every later row absorbs zero.
//!
//! [`RecWitness::zero`] is the `b = 0` convention (BLUEPRINT §4.5 Gate): every message zero.

use crate::format::{self, Sig, Signed, SIG_HEIGHT, TAG_SIG_NODE, TAG_WOTS, TAG_WOTS_LEAF, WOTS_LEN};
use crate::keccak::{self, Digest, RATE, RATE_LANES, TAG_LEAF, TAG_NODE};
use crate::lvm::params::{Params, REC_STREAM_COLS, SIG_BYTES};
use crate::lvm::stream::header_of;

/// First KS row (above `R`) of each group.
pub const ROW_CHAIN: usize = 0;
pub const ROW_LEAF: usize = 3 * WOTS_LEN;
pub const ROW_PATH: usize = ROW_LEAF + 32;
pub const ROW_LEAF_STMT: usize = ROW_PATH + SIG_HEIGHT;
pub const ROW_NODE_STMT: usize = ROW_LEAF_STMT + 1;
/// KS rows `≥ R` used (WP-0: 449).
pub const UPPER_ROWS: usize = ROW_NODE_STMT + 1;
/// Lanes of `σ'` in its column (of the stream block `S`).
pub const SIG_LANES: usize = SIG_BYTES / 8;

/// SLF (S2GS): the KS rows of the second WOTS walk (`σ_leaf` on the constant `traceDigest []`, variant A = Q_sig's
/// walk without the statement rows): 399 chain steps, 32 key-leaf blocks, 16 path nodes.
pub const LEAF_WALK_ROWS: usize = ROW_LEAF_STMT;

/// SLF (S2GS, provisional until SLF-C fixes the rows): the second walk's first KS row. X (rows `≥ ks_split`) has
/// `2^x_log` = 512 rows at P20 and Q_sig uses 449, so the default puts the walk in the dead stream rows right below
/// `ks_split` (`[ks_split − 447, ks_split)`; the stream ends at `B` = 3,808). Dev: `LVM_SLF_W2ROW=r`.
pub fn leaf_walk_row0(ks_log: usize, rec_log: usize) -> usize {
    match std::env::var("LVM_SLF_W2ROW").ok().and_then(|v| v.parse().ok()) {
        Some(r) => r,
        None => crate::lvm::tables::ks_split(ks_log, rec_log) - LEAF_WALK_ROWS,
    }
}

/// The KS messages of one WOTS walk of `sig` on the message digest `m`, from KS row `r0` (module doc's rows `R … R +
/// 446`); returns the key it reaches (`vk` when `SigOk vk m sig`).
fn wots_walk_rows(msg: &mut [[u64; REC_STREAM_COLS]], r0: usize, m: &Digest, sig: &Sig) -> Digest {
    let j = sig.idx;
    let d = format::wots_digits(m);
    let mut ends = Vec::with_capacity(WOTS_LEN);
    for i in 0..WOTS_LEN {
        let mut prev = [0u8; 32];
        for s in 1..=3usize {
            let a = if (d[i] as usize) + 1 < s { prev } else { sig.ots[i] };
            let blk = wots_step_msg(j, i, s - 1, &a);
            msg[r0 + ROW_CHAIN + 3 * i + (s - 1)] = blk;
            prev = hash_block(&blk);
        }
        ends.push(if d[i] < 3 { prev } else { sig.ots[i] });
    }
    leaf_path_rows(msg, r0 + ROW_LEAF, j, &ends, &sig.path)
}

/// The key leaf `0x4B ‖ enc64 j ‖ end_0 ‖ … ‖ end_132` (32 blocks from KS row `l0`, `cont` inside) and the 16 path
/// rows after it; returns the root.
fn leaf_path_rows(msg: &mut [[u64; REC_STREAM_COLS]], l0: usize, j: u64, ends: &[Digest], path: &[Digest]) -> Digest {
    let mut leaf = Vec::with_capacity(9 + 32 * WOTS_LEN);
    leaf.push(TAG_WOTS_LEAF);
    leaf.extend_from_slice(&j.to_le_bytes());
    for e in ends {
        leaf.extend_from_slice(e);
    }
    let lb = padded_blocks(&leaf);
    assert_eq!(lb.len(), 32);
    for (k, b) in lb.iter().enumerate() {
        msg[l0 + k] = *b;
    }
    let mut cur = keccak::keccak256(&leaf);
    for t in 0..SIG_HEIGHT {
        let sib = &path[t];
        let blk = if (j >> t) & 1 == 0 { two_msg(TAG_SIG_NODE, &cur, sib) } else { two_msg(TAG_SIG_NODE, sib, &cur) };
        msg[l0 + 32 + t] = blk;
        cur = hash_block(&blk);
    }
    cur
}

/// SLF D8 (variant C, the default; `LVM_SLF_VARIANT=A`: s-dev1's generic walk): walk 2 specialised to the constant
/// digits `D = wotsDigits (traceDigest [])`.
pub fn variant_c() -> bool {
    std::env::var("LVM_SLF_VARIANT").map_or(true, |v| v != "A")
}

/// Variant C's chain order `permC`: the chains of digit 0, then 1, 2, 3 (ascending `i` inside a group), and the
/// group sizes.
pub fn perm_c() -> (Vec<usize>, [usize; 4]) {
    let d = format::wots_digits(&format::trace_digest(&[]));
    let mut n = [0usize; 4];
    for &x in &d {
        n[x as usize] += 1;
    }
    let d = &d;
    ((0..4u32).flat_map(|g| (0..WOTS_LEN).filter(move |&i| d[i] == g)).collect(), n)
}

/// Variant C: KS rows of walk 2 from `ks_split − 400` (7,280 at P20): per group `g < 3` a loop of
/// `next_pow2(|group g|)` iterations (64, 64, 32), iteration `k` chain `permC[gOff g + k]`, steps `t < 3 − g` (`s = g +
/// t`) at row `w0 + gRow g + (3 − g)k + t` (`gRow` 0, 192, 320); a padded iteration (`k ≥ |group g|`) hashes the step
/// message with `x = 0` at every step. Then the key leaf (`ks_split − 48`) and the path. Returns the root.
fn leaf_walk_rows_c(msg: &mut [[u64; REC_STREAM_COLS]], split: usize, sig: &Sig) -> Digest {
    let (perm, n) = perm_c();
    let j = sig.idx;
    let w0 = split - 400;
    let mut ends: Vec<Digest> = sig.ots.clone();
    let (mut goff, mut grow) = (0usize, 0usize);
    for g in 0..3usize {
        let iters = n[g].next_power_of_two();
        for k in 0..iters {
            let i = perm[goff + k];
            let real = k < n[g];
            let mut x = if real { sig.ots[i] } else { [0u8; 32] };
            for t in 0..3 - g {
                let blk = wots_step_msg(j, i, g + t, &x);
                msg[w0 + grow + (3 - g) * k + t] = blk;
                if real {
                    x = hash_block(&blk);
                }
            }
            if real {
                ends[i] = x;
            }
        }
        goff += n[g];
        grow += (3 - g) * iters;
    }
    assert_eq!(grow, 352, "walk 2's step rows (C)");
    leaf_path_rows(msg, split - 48, j, &ends, &sig.path)
}

/// SLF: the first KS row of the own leaf's key leaf (the third `cont` run is its rows 1..31): `ks_split − 48`.
pub fn leaf_key_row(ks_log: usize, rec_log: usize) -> usize {
    if variant_c() { crate::lvm::tables::ks_split(ks_log, rec_log) - 48 } else { leaf_walk_row0(ks_log, rec_log) + ROW_LEAF }
}

/// σ_leaf's 597 window lanes: FORMAT.md's order (variant A), or (C) `idx`, the chains in `permC` order, the path.
pub fn leaf_window_lanes(sig: &Sig) -> Vec<u64> {
    let l = sig_lanes(sig);
    if !variant_c() {
        return l;
    }
    let (perm, _) = perm_c();
    let mut v = Vec::with_capacity(SIG_LANES);
    v.push(l[0]);
    for &i in &perm {
        v.extend_from_slice(&l[1 + 4 * i..5 + 4 * i]);
    }
    v.extend_from_slice(&l[1 + 4 * WOTS_LEN..]);
    assert_eq!(v.len(), SIG_LANES);
    v
}

/// The 597 lanes of a signature (FORMAT.md's words: `idx ‖ ots ‖ path`).
pub fn sig_lanes(sig: &Sig) -> Vec<u64> {
    let mut sb = Vec::with_capacity(SIG_BYTES);
    format::put_sig(&mut sb, sig);
    assert_eq!(sb.len(), SIG_BYTES);
    (0..SIG_LANES).map(|k| keccak::lane_of(&sb, k)).collect()
}

/// The recursion witness: the 17 message lanes of every KS row (rows `< ks_split` are `C_rec`'s stream columns
/// `M_l`, rows `≥ ks_split` the `X` columns of `C_main`) and `σ'`'s column (`2^rec` words).
pub struct RecWitness {
    pub msg: Vec<[u64; REC_STREAM_COLS]>,
    pub sigma: Vec<u64>,
    /// The recursion tables (LoopIR pieces, input arrays, BITS) for the real bus and the table sumcheck;
    /// empty: the null bus of WP-15a (`M3.v0`).
    pub tables: Vec<crate::lvm::m3::TableW>,
}

/// `m` with Keccak's `pad10*1` as rate blocks of 17 lanes.
pub fn padded_blocks(m: &[u8]) -> Vec<[u64; RATE_LANES]> {
    let nb = m.len() / RATE + 1;
    let mut b = vec![0u8; nb * RATE];
    b[..m.len()].copy_from_slice(m);
    b[m.len()] ^= 0x01;
    b[nb * RATE - 1] ^= 0x80;
    (0..nb).map(|k| std::array::from_fn(|l| keccak::lane_of(&b[k * RATE..(k + 1) * RATE], l))).collect()
}

/// The bytes `traceDigest` hashes: `0x54 ‖ (enc64 |q| ‖ q ‖ a)…`.
pub fn trace_bytes(tr: &[(Vec<u8>, Digest)]) -> Vec<u8> {
    let n = 1 + tr.iter().map(|(q, _)| 40 + q.len()).sum::<usize>();
    let mut v = Vec::with_capacity(n);
    v.push(format::TAG_TRACE);
    for (q, a) in tr {
        v.extend_from_slice(&(q.len() as u64).to_le_bytes());
        v.extend_from_slice(q);
        v.extend_from_slice(a);
    }
    v
}

fn one_block(m: &[u8]) -> [u64; RATE_LANES] {
    let b = padded_blocks(m);
    assert_eq!(b.len(), 1, "a one-block message");
    b[0]
}

fn hash_block(m: &[u64; RATE_LANES]) -> Digest {
    let mut a = [0u64; 25];
    a[..RATE_LANES].copy_from_slice(m);
    keccak::keccak_f(&mut a);
    keccak::digest_of(&a)
}

pub fn wots_step_msg(j: u64, i: usize, s: usize, x: &Digest) -> [u64; RATE_LANES] {
    let mut m = Vec::with_capacity(43);
    m.push(TAG_WOTS);
    m.extend_from_slice(&j.to_le_bytes());
    m.extend_from_slice(&[i as u8, s as u8]);
    m.extend_from_slice(x);
    one_block(&m)
}

fn two_msg(tag: u8, a: &Digest, b: &Digest) -> [u64; RATE_LANES] {
    let mut m = Vec::with_capacity(65);
    m.push(tag);
    m.extend_from_slice(a);
    m.extend_from_slice(b);
    one_block(&m)
}

impl RecWitness {
    /// The `b = 0` convention: every message zero.
    pub fn zero(p: &Params) -> Self {
        // R11 (S2GM): σ′'s region is 2^10 words (KSY2 follows it inside S)
        // (SLF, S2GS: and σ_leaf's lanes after it, `LEAF_SIG_OFF`)
        Self { msg: vec![[0; REC_STREAM_COLS]; 1 << p.ks_log], sigma: vec![0; 1 << crate::lvm::tables::sig_region_log()], tables: Vec::new() }
    }

    /// The witness of a node whose left child is `child` (module doc).
    pub fn from_child(p: &Params, child: &Signed) -> Self {
        let r = crate::lvm::tables::ks_split(p.ks_log, p.rec_rows_log);
        let mut w = Self::zero(p);
        // the stream
        let blocks = padded_blocks(&trace_bytes(&child.tr));
        assert_eq!(blocks.len(), crate::lvm::prove::sponge_blocks(p), "the child's trace has the schedule's length");
        assert!(blocks.len() <= r);
        for (i, b) in blocks.iter().enumerate() {
            w.msg[i] = *b;
        }
        // σ'
        w.sigma[..SIG_LANES].copy_from_slice(&sig_lanes(&child.sig));
        // the WOTS walk of σ' on traceDigest tr'
        let _ = wots_walk_rows(&mut w.msg, r, &format::trace_digest(&child.tr), &child.sig);
        // the child's statement
        let hd = header_of(p, &child.pi);
        let mut ls = Vec::with_capacity(41);
        ls.push(TAG_LEAF);
        ls.extend_from_slice(&hd.h);
        ls.extend_from_slice(&hd.n.to_le_bytes());
        let lsb = one_block(&ls);
        w.msg[r + ROW_LEAF_STMT] = lsb;
        w.msg[r + ROW_NODE_STMT] = two_msg(TAG_NODE, &hd.c_l, &hash_block(&lsb));
        w
    }

    /// SLF (S2GS): the node's own leaf signature `σ_leaf` (on `traceDigest []`): its 597 lanes at
    /// [`crate::lvm::tables::LEAF_SIG_OFF`] of `σ'`'s column and its WOTS walk from KS row [`leaf_walk_row0`]
    /// (the third `cont` run is [`crate::lvm::tables::cont_column`]'s). Asserts that the walk reaches `vk`.
    pub fn set_leaf(&mut self, p: &Params, vk: &Digest, sig: &Sig) {
        assert!(crate::lvm::params::FrontCfg::get().sigout, "σ_leaf is in the window at S2GS only");
        let off = crate::lvm::tables::LEAF_SIG_OFF;
        assert!(off + SIG_LANES <= self.sigma.len());
        self.sigma[off..off + SIG_LANES].copy_from_slice(&leaf_window_lanes(sig));
        let got = if variant_c() {
            leaf_walk_rows_c(&mut self.msg, crate::lvm::tables::ks_split(p.ks_log, p.rec_rows_log), sig)
        } else {
            wots_walk_rows(&mut self.msg, leaf_walk_row0(p.ks_log, p.rec_rows_log), &format::trace_digest(&[]), sig)
        };
        // (SLF dev, `LVM_SLF_TAMPER`; the circuit must reject each: `win:K` window lane K of σ_leaf flipped (the walk rows
        // stay honest), `row:R:L` KS message row R lane L flipped, `wrongsig` (stream.rs) a real signature on another message)
        let tm: Vec<String> = std::env::var("LVM_SLF_TAMPER").unwrap_or_default().split(':').map(String::from).collect();
        let num = |i: usize| tm.get(i).and_then(|x| x.parse::<usize>().ok()).expect("LVM_SLF_TAMPER: win:K | row:R:L | wrongsig");
        match tm[0].as_str() {
            "" => assert_eq!(&got, vk, "σ_leaf's walk reaches vk (SigOk vk (traceDigest []) σ_leaf)"),
            "win" => {
                self.sigma[off + num(1)] ^= 1;
                eprintln!("lvm: LVM_SLF_TAMPER=win:{}: σ_leaf window lane flipped (word {})", num(1), off + num(1));
            }
            "row" => {
                self.msg[num(1)][num(2)] ^= 1;
                eprintln!("lvm: LVM_SLF_TAMPER=row:{}:{}: KS message lane flipped", num(1), num(2));
            }
            "wrongsig" | "otherkey" => eprintln!("lvm: LVM_SLF_TAMPER={}: walk 2 reaches vk: {}", tm[0], &got == vk),
            m => panic!("LVM_SLF_TAMPER={m}"),
        }
    }

    /// The `C_rec` stream columns `M_l` (`2^rec` rows): the KS messages of rows `< ks_split`, zero above (KS14).
    pub fn stream_rows(&self, p: &Params) -> Vec<[u64; REC_STREAM_COLS]> {
        let split = crate::lvm::tables::ks_split(p.ks_log, p.rec_rows_log);
        let mut m = self.msg[..split].to_vec();
        m.resize(1 << p.rec_rows_log, [0; REC_STREAM_COLS]);
        m
    }

    /// The `C_rec` stream columns and the `X` messages as one dump (`LVM_REC_DUMP`, for the Lean check):
    /// `2^ks_log` rows of 17 little-endian lanes, then `2^10` lanes of `σ'` (R11, S2GM: σ′'s region).
    pub fn dump(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(8 * (17 * self.msg.len() + self.sigma.len()));
        for row in &self.msg {
            for x in row {
                v.extend_from_slice(&x.to_le_bytes());
            }
        }
        for x in &self.sigma {
            v.extend_from_slice(&x.to_le_bytes());
        }
        v
    }
}

/// Self-checks (`lvm-prover rqtest`; the crate's `cargo test` does not build the vendored tests).
pub mod check {
    use super::*;

    pub fn padding_matches_keccak256() {
        for n in [0usize, 1, 41, 43, 65, 135, 136, 137, 4265] {
            let m: Vec<u8> = (0..n).map(|k| (k * 7 + 3) as u8).collect();
            let bl = padded_blocks(&m);
            let mut st = [0u64; 25];
            for b in &bl {
                for l in 0..RATE_LANES {
                    st[l] ^= b[l];
                }
                keccak::keccak_f(&mut st);
            }
            assert_eq!(keccak::digest_of(&st), keccak::keccak256(&m), "n = {n}");
        }
    }

    /// SLF (S2GS, P20): `set_leaf`'s rows and the third `cont` run replay to `vk` in KS (and σ_leaf's lanes sit at
    /// `LEAF_SIG_OFF`), beside a child's σ′ walk.
    pub fn leaf_walk_reaches_the_key() {
        if !crate::lvm::params::FrontCfg::get().sigout {
            return;
        }
        let p = crate::lvm::params::p20_g(0);
        let tr: Vec<(Vec<u8>, Digest)> = crate::lvm::params::query_list(&p).iter().enumerate().map(|(k, (_, len))| (vec![k as u8; *len], [k as u8; 32])).collect();
        let (vk, sig2) = format::toy_sign(9, &format::trace_digest(&tr));
        let (vk_l, sig_l) = format::toy_sign(9, &format::trace_digest(&[]));
        assert_eq!(vk, vk_l);
        let mut pi = vec![0u8; crate::lvm::params::header_bytes(&p)];
        pi[0] = b'S';
        let child = Signed { pi, tr, sig: sig2 };
        let mut w = RecWitness::from_child(&p, &child);
        w.set_leaf(&p, &vk, &sig_l);
        let off = crate::lvm::tables::LEAF_SIG_OFF;
        assert_eq!(&w.sigma[off..off + SIG_LANES], &leaf_window_lanes(&sig_l)[..]);
        let r = crate::lvm::tables::ks_split(p.ks_log, p.rec_rows_log);
        let l0 = leaf_key_row(p.ks_log, p.rec_rows_log);
        let cont = crate::lvm::tables::cont_column(p.ks_log, p.rec_rows_log, crate::lvm::prove::sponge_blocks(&p));
        let runs = crate::lvm::wire::cont_runs(&cont);
        let ks = crate::lvm::tables::Sponge::run(p.ks_log, cont, w.msg.clone());
        assert_eq!(keccak::digest_of(&ks.outputs[r + ROW_PATH + SIG_HEIGHT - 1]), vk, "σ′'s walk reaches vk");
        assert_eq!(keccak::digest_of(&ks.outputs[l0 + 32 + SIG_HEIGHT - 1]), vk, "σ_leaf's walk reaches vk");
        let (_, n) = perm_c();
        println!("rqtest S2GS leaf walk (variant {}): digit groups {n:?}, key leaf {l0}..{}, path ..{}, cont runs {runs:?}: ok", if variant_c() { "C" } else { "A" }, l0 + 32, l0 + 48);
    }

    pub fn wots_rows_reach_the_key() {
        let msg: Digest = std::array::from_fn(|k| (k as u8).wrapping_mul(13));
        let (vk, sig) = format::toy_sign(7, &msg);
        // a fake child whose trace digest is not `msg`: sign its digest instead
        let p = crate::lvm::params::p8_g(0);
        let tr: Vec<(Vec<u8>, Digest)> = crate::lvm::params::query_list(&p)
            .iter()
            .enumerate()
            .map(|(k, (_, len))| (vec![k as u8; *len], [k as u8; 32]))
            .collect();
        let m = format::trace_digest(&tr);
        let (vk2, sig2) = format::toy_sign(7, &m);
        assert!(format::sig_ok(&vk, &msg, &sig) && format::sig_ok(&vk2, &m, &sig2));
        let mut pi = vec![0u8; crate::lvm::params::header_bytes(&p)];
        pi[0] = b'S';
        let child = Signed { pi, tr, sig: sig2.clone() };
        let w = RecWitness::from_child(&p, &child);
        let r = crate::lvm::tables::ks_split(p.ks_log, p.rec_rows_log);
        // replay the KS rows: trace sponge, then the path's last output is vk2
        let cont = crate::lvm::tables::cont_column(p.ks_log, p.rec_rows_log, crate::lvm::prove::sponge_blocks(&p));
        let ks = crate::lvm::tables::Sponge::run(p.ks_log, cont, w.msg.clone());
        let b = crate::lvm::prove::sponge_blocks(&p);
        assert_eq!(keccak::digest_of(&ks.outputs[b - 1]), m, "Y of the last trace row is traceDigest");
        assert_eq!(keccak::digest_of(&ks.outputs[r + ROW_PATH + SIG_HEIGHT - 1]), vk2, "the walk reaches vk");
    }
}
