//! The revision 4.1 node's witness (N2/N4/N8, 1 + k slots; BLUEPRINT §4.2–4.3, A.6–A.7 as S-E12a's
//! `FRNodeKinds4`, S-E12b–d's node rows): the layout `nodeLayout4` (block kinds and targets), the H
//! blocks (both signed children's digest chains, the candidate final blocks and `c_A`'s `hashA`,
//! `hashStmt` per verifier slot, WOTS per signed child with the `WM` mirrors), the L bits, the M
//! region (`mfill`), and direct checks of every relation the node's verifier tests: each H block's
//! R1CS with its target, the masked chain links (`chainLk4`), the eight link families, the public
//! cells, L's Booleanity, every M row (prototype rows moved per slot, link and activity rows).
//!
//! Provisional where the circuit is still open (S-E12a D6, S-E12d README): the slot holding a signed
//! child's signature, digits and step selectors in L (here: L slot `σ` for signed child `σ`), the
//! content of free `stmt` blocks of a slot whose child is of the other kind (pins, zeros), and the
//! main chain's bytes past an aggregate of `k < maxK` segments (zeros).

use crate::blake2s::{self, Digest};
use crate::circuit::{Circuit, Node};
use crate::field::F;
use crate::format::{self, Sig};
use crate::ir::V;
use crate::mfill;
use crate::par;
use crate::params as pp;

/// One trace's stream `0x54 ‖ traceBytes tr` at `seq4` (`N4c.segB`).
pub const SEG_B: usize = 1_482_752;
/// Its digest chain's blocks (`N4c.cLen`).
pub const C_LEN: usize = 23_168;
pub const WOTS_SLOT: usize = 498;
pub const WM_SLOT: usize = 146;
pub const TAG_WOTS: u8 = 0x57;
pub const TAG_WOTS_LEAF: u8 = 0x4B;
pub const TAG_SIG_NODE: u8 = 0x4D;

pub fn agg_b(k: usize) -> usize {
    1 + k * (SEG_B - 1)
}
pub fn agg_l(k: usize) -> usize {
    agg_b(k).div_ceil(64)
}
fn n_blocks(l: usize) -> usize {
    (l - 1) / 64 + 1
}

/// The node kinds (`FRShape4.NodeKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NK {
    N2,
    N4,
    N8,
}

impl NK {
    pub fn of_byte(b: u8) -> Option<NK> {
        match b {
            0x4D => Some(NK::N2),
            0x4E => Some(NK::N4),
            0x4F => Some(NK::N8),
            _ => None,
        }
    }
    pub fn byte(self) -> u8 {
        [0x4D, 0x4E, 0x4F][self as usize]
    }
    pub fn name(self) -> &'static str {
        ["N2", "N4", "N8"][self as usize]
    }
    pub fn m(self) -> usize {
        [31, 32, 32][self as usize]
    }
    pub fn seg_slots(self) -> usize {
        [2, 4, 8][self as usize]
    }
    pub fn has_prev(self) -> bool {
        self != NK::N8
    }
    pub fn vslots(self) -> usize {
        self.has_prev() as usize + self.seg_slots()
    }
    pub fn max_k(self) -> usize {
        if self.has_prev() { self.seg_slots() } else { 4 }
    }
    pub fn blocks(self) -> usize {
        1 << (self.m() - 14)
    }
    pub fn log_m(self) -> usize {
        [22, 23, 23][self as usize]
    }
    pub fn log_l(self) -> usize {
        [16, 17, 17][self as usize]
    }
    pub fn n_agg(self) -> usize {
        if self.has_prev() { 1 } else { 2 }
    }
    pub fn is_agg(self, sg: usize) -> bool {
        !self.has_prev() || sg != 0
    }
    pub fn ch_len(self, sg: usize) -> usize {
        if self.is_agg(sg) { agg_l(self.max_k()) } else { C_LEN }
    }
    pub fn ch_bytes(self, sg: usize) -> usize {
        if self.is_agg(sg) { agg_b(self.max_k()) } else { SEG_B }
    }
    pub fn ch_base(self, sg: usize) -> usize {
        sg * self.ch_len(0)
    }
    pub fn stmt_b(self) -> usize {
        self.ch_len(0) + self.ch_len(1)
    }
    pub fn wots_b(self, sg: usize) -> usize {
        self.stmt_b() + 3 * self.vslots() + WOTS_SLOT * sg
    }
    pub fn wm_b(self, sg: usize) -> usize {
        self.wots_b(2) + WM_SLOT * sg
    }
    pub fn h_used(self) -> usize {
        self.wots_b(2) + WM_SLOT * self.vslots() + 8
    }
    pub fn fin_b(self, a: usize) -> usize {
        self.h_used() + a * self.max_k()
    }
    pub fn h_end(self) -> usize {
        self.fin_b(self.n_agg())
    }
    pub fn c_ab(self, a: usize) -> usize {
        self.fin_b(a) + self.max_k() - 1
    }
    pub fn l_base(self) -> usize {
        self.h_used().div_ceil(256) * 256
    }
    pub fn n_m(self) -> usize {
        1 << self.log_m()
    }
    pub fn m_base(self) -> usize {
        self.blocks() - self.n_m() / 128
    }
    pub fn one_cell(self) -> usize {
        self.m_base() * 128
    }
    /// Aggregate `a`'s signed child, and signed child `σ`'s aggregate.
    pub fn agg_child(self, a: usize) -> usize {
        if self.has_prev() { 1 } else { a }
    }
    pub fn agg_of(self, sg: usize) -> usize {
        if self.has_prev() { sg - 1 } else { sg }
    }
    /// The verifier slot of aggregate `a`'s sub-slot `i`.
    pub fn sub_slot(self, a: usize, i: usize) -> usize {
        if self.has_prev() { 1 + i } else { 4 * a + i }
    }
    /// Signed child `σ`'s seed payload element `e` (`seedC`).
    pub fn seed_c(self, sg: usize, e: usize) -> usize {
        (self.ch_base(sg) + (1 + e) / 4) * 128 + 4 + (1 + e) % 4
    }
    /// Signed child `σ`'s statement half `h` (`stC`: an aggregate's from its `c_A` block).
    pub fn st_c(self, sg: usize, h: usize) -> usize {
        if self.is_agg(sg) { self.c_ab(self.agg_of(sg)) * 128 + 2 + h } else { self.seed_c(sg, 2 + h) }
    }
    /// **`cells4`**: M's `one`, then per signed child `vk`'s and its statement's halves.
    pub fn cells4(self) -> Vec<usize> {
        let mut v = vec![self.one_cell()];
        for sg in 0..2 {
            v.extend([self.seed_c(sg, 0), self.seed_c(sg, 1), self.st_c(sg, 0), self.st_c(sg, 1)]);
        }
        v
    }
    /// **`chainLk4`**: block `y`'s `h_out` is block `y + 1`'s `h_in` (both in one main chain).
    pub fn chain_lk(self, y: usize) -> bool {
        let l0 = self.ch_len(0);
        y + 1 < l0 || (l0 <= y && y + 1 < l0 + self.ch_len(1))
    }
}

/// A.6's block kinds with their per-block target data (`FRBlockKinds.Kind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BK {
    Stream(u64, bool),
    StreamStart,
    StreamEnd41,
    HashA,
    HashB1(u8),
    HashB2,
    W43(u8, u8),
    Free,
}

/// `streamTarget L i`.
pub fn stream_target(l: usize, i: usize) -> BK {
    let fin = i + 1 == n_blocks(l);
    BK::Stream(if fin { l as u64 } else { 64 * (i as u64 + 1) }, fin)
}

impl BK {
    /// `bkIdx4`.
    pub fn idx(self) -> usize {
        match self {
            BK::Stream(..) => 1,
            BK::StreamStart => 2,
            BK::StreamEnd41 => 3,
            BK::HashA => 4,
            BK::HashB1(_) => 5,
            BK::HashB2 => 6,
            BK::W43(..) => 7,
            BK::Free => 8,
        }
    }
    pub(crate) fn h0_pin(self) -> bool {
        matches!(self, BK::StreamStart | BK::HashA | BK::HashB1(_) | BK::W43(..))
    }
    pub(crate) fn msg_pin(self, p: usize) -> Option<u8> {
        match self {
            BK::StreamEnd41 if p >= 41 => Some(0),
            BK::HashA if p == 0 => Some(blake2s::TAG_LEAF),
            BK::HashA if p >= 41 => Some(0),
            BK::HashB1(t) if p == 0 => Some(t),
            BK::HashB2 if p >= 1 => Some(0),
            BK::W43(_, _) if p == 0 => Some(TAG_WOTS),
            BK::W43(i, _) if p == 9 => Some(i),
            BK::W43(_, s) if p == 10 => Some(s),
            BK::W43(..) if p >= 43 => Some(0),
            _ => None,
        }
    }
    /// The counter and final flag (`blockTarget t fin`).
    pub fn ctr(self) -> (u64, bool) {
        match self {
            BK::Stream(t, f) => (t, f),
            BK::StreamStart | BK::HashB1(_) => (64, false),
            BK::StreamEnd41 => (4265, true),
            BK::HashA => (41, true),
            BK::HashB2 => (65, true),
            BK::W43(..) => (43, true),
            BK::Free => (0, false),
        }
    }
    /// **The public target** at position `k` (`Kind.target`; `None`: unpinned or a zero row).
    pub fn target(self, k: usize) -> Option<bool> {
        if self == BK::Free {
            return None;
        }
        let h0 = blake2s::h0();
        if k < 256 {
            return self.h0_pin().then(|| (h0[k / 32] >> (k % 32)) & 1 == 1);
        }
        if (512..1024).contains(&k) {
            return self.msg_pin((k - 512) / 8).map(|b| (b >> ((k - 512) % 8)) & 1 == 1);
        }
        let (t, fin) = self.ctr();
        match k {
            1024..=1055 => Some((t >> (k - 1024)) & 1 == 1),
            1056..=1087 => Some((t >> (32 + k - 1056)) & 1 == 1),
            1088..=1119 => Some(fin),
            1120..=1151 => Some(false),
            1152 => Some(true),
            _ => None,
        }
    }
    /// A pinned input position (`zeroRows`).
    pub fn pinned(self, k: usize) -> bool {
        k < 1153 && self.target(k).is_some()
    }
}

/// `NodeT.wotsTgt o` (`o < 498`).
fn wots_tgt(o: usize) -> BK {
    match o {
        0..=398 => BK::W43((o / 3) as u8, (o % 3) as u8),
        399 => BK::HashB1(TAG_WOTS_LEAF),
        400..=464 => stream_target(4265, o - 399),
        465 => BK::StreamEnd41,
        _ if (o - 466) % 2 == 0 => BK::HashB1(TAG_SIG_NODE),
        _ => BK::HashB2,
    }
}

/// **`nodeKind4`/`nodeBK4`**: block `blk`'s kind and target (`nodeLayout4`'s intervals).
pub fn bk_at(k: NK, blk: usize) -> BK {
    for sg in 0..2 {
        let (b0, l) = (k.ch_base(sg), k.ch_len(sg));
        if blk >= b0 && blk < b0 + l {
            return if blk == b0 { BK::StreamStart } else { stream_target(k.ch_bytes(sg), blk - b0) };
        }
    }
    let sb = k.stmt_b();
    if blk < sb + 3 * k.vslots() {
        return [BK::HashA, BK::HashB1(blake2s::TAG_NODE), BK::HashB2][(blk - sb) % 3];
    }
    if blk < k.wots_b(2) {
        return wots_tgt((blk - k.wots_b(0)) % WOTS_SLOT);
    }
    if blk >= k.h_used() && blk < k.h_end() {
        let j = (blk - k.h_used()) % k.max_k();
        return if j + 1 < k.max_k() { stream_target(agg_b(j + 1), agg_l(j + 1) - 1) } else { BK::HashA };
    }
    BK::Free
}

/// The eight link families (`NodeT.fam`): sources, source block (relative to the WOTS run),
/// field offset and length in bytes, mirror source, the field's first bit in its mirror.
pub struct Fam {
    pub n: usize,
    pub src: fn(usize) -> usize,
    pub off: usize,
    pub len: usize,
    pub mir: fn(usize) -> usize,
    pub mbo: usize,
}

pub const FAMS: [Fam; 8] = [
    Fam { n: 399, src: |t| t, off: 11, len: 32, mir: |t| t, mbo: 0 },
    Fam { n: 400, src: |t| t, off: 1, len: 8, mir: |_| 399, mbo: 0 },
    Fam { n: 67, src: |t| 399 + t, off: 9, len: 32, mir: |t| 400 + t, mbo: 0 },
    Fam { n: 66, src: |t| 399 + t, off: 41, len: 23, mir: |t| 467 + t, mbo: 0 },
    Fam { n: 66, src: |t| 400 + t, off: 0, len: 9, mir: |t| 467 + t, mbo: 184 },
    Fam { n: 16, src: |t| 466 + 2 * t, off: 1, len: 32, mir: |t| 533 + t, mbo: 0 },
    Fam { n: 16, src: |t| 466 + 2 * t, off: 33, len: 31, mir: |t| 549 + t, mbo: 0 },
    Fam { n: 16, src: |t| 467 + 2 * t, off: 0, len: 1, mir: |t| 565 + t, mbo: 0 },
];

/// A compression's inputs.
#[derive(Clone, Copy)]
pub struct BlockIn {
    pub h: [u32; 8],
    pub msg: [u8; 64],
    pub t: u64,
    pub f0: u32,
}

impl BlockIn {
    pub fn zero() -> BlockIn {
        BlockIn { h: [0; 8], msg: [0; 64], t: 0, f0: 0 }
    }
    /// The inputs of a kind's block: its pins, `h_in` (when free), the free message bytes.
    pub fn of(bk: BK, h: [u32; 8], msg: &[u8]) -> BlockIn {
        let mut b = BlockIn { h: if bk.h0_pin() { blake2s::h0() } else { h }, msg: [0; 64], t: bk.ctr().0, f0: if bk.ctr().1 { u32::MAX } else { 0 } };
        for p in 0..64 {
            b.msg[p] = bk.msg_pin(p).unwrap_or(msg.get(p).copied().unwrap_or(0));
        }
        b
    }
    pub fn out(&self) -> [u32; 8] {
        let mut m = [0u32; 16];
        for (i, w) in m.iter_mut().enumerate() {
            *w = u32::from_le_bytes(self.msg[4 * i..4 * i + 4].try_into().unwrap());
        }
        blake2s::compress(&self.h, &m, self.t, self.f0)
    }
}

fn words_bytes(h: &[u32; 8]) -> Digest {
    let mut d = [0u8; 32];
    for i in 0..8 {
        d[4 * i..4 * i + 4].copy_from_slice(&h[i].to_le_bytes());
    }
    d
}
fn bytes_words(d: &Digest) -> [u32; 8] {
    std::array::from_fn(|i| u32::from_le_bytes(d[4 * i..4 * i + 4].try_into().unwrap()))
}

/// The general block tape: leanerVM's circuit with every input position a variable (no chain
/// constants; `Circuit::build` folds the chain kind's into constant gates).
pub fn general_circuit() -> Circuit {
    Circuit::build_general()
}

/// **Up to 64 blocks of any kinds, bit-sliced**: `z`, `A₀z`, `B₀z` per block (the kind's rows: a
/// pinned input `(0, 0)`, a free input `(var k, one)`, gates and outputs their forms; `free`: `A₀ =
/// B₀ = I`). Block `t`'s words go to `[256 t, 256 t + 256)`.
pub fn trace_blocks_ref(c: &Circuit, ins: &[BlockIn], bks: &[BK], zw: &mut [u64], aw: &mut [u64], bw: &mut [u64]) {
    let k = ins.len();
    assert!(k <= 64 && bks.len() == k);
    const BLOCK: usize = 1 << 14;
    let mut z = vec![0u64; BLOCK];
    let lanes = if k == 64 { !0 } else { (1u64 << k) - 1 };
    let mut free = 0u64;
    for (t, (b, bk)) in ins.iter().zip(bks).enumerate() {
        if *bk == BK::Free {
            free |= 1 << t;
            continue;
        }
        let set = |z: &mut [u64], p: usize, v: bool| z[p] |= (v as u64) << t;
        for i in 0..256 {
            set(&mut z, i, (b.h[i / 32] >> (i % 32)) & 1 == 1);
        }
        for i in 0..512 {
            set(&mut z, pp::MSG_BASE + i, (b.msg[i / 8] >> (i % 8)) & 1 == 1);
        }
        for i in 0..64 {
            set(&mut z, pp::TLO_BASE + i, (b.t >> i) & 1 == 1);
        }
        for i in 0..32 {
            set(&mut z, pp::F0_BASE + i, (b.f0 >> i) & 1 == 1);
        }
        set(&mut z, pp::ONE_POS, true);
    }
    let mut vals = vec![0u64; c.nodes.len()];
    for (i, nd) in c.nodes.iter().enumerate() {
        vals[i] = match *nd {
            Node::Zero => 0,
            Node::Var(p) => z[p as usize],
            Node::Xor(a, b) => vals[a as usize] ^ vals[b as usize],
            Node::Gate(p, a, b) => {
                let v = vals[a as usize] & vals[b as usize];
                z[p as usize] = v;
                v
            }
        };
    }
    let hw = lanes & !free;
    // the lanes of each kind in the batch (most batches hold one or two): the pinned-input masks
    // per kind, not per lane
    let mut groups: Vec<(BK, u64)> = Vec::new();
    for (t, bk) in bks.iter().enumerate() {
        match groups.iter_mut().find(|g| g.0 == *bk) {
            Some(g) => g.1 |= 1 << t,
            None => groups.push((*bk, 1 << t)),
        }
    }
    let (mut mz, mut ma, mut mb) = ([0u64; 64], [0u64; 64], [0u64; 64]);
    for wi in 0..BLOCK / 64 {
        for j in 0..64 {
            let p = 64 * wi + j;
            let zz = z[p] & hw;
            let (a, b) = if let Some((a, b)) = c.rows[p] {
                (vals[a as usize] & hw, vals[b as usize] & hw)
            } else if p < pp::ONE_POS && !(256..512).contains(&p) {
                // an input: per lane, pinned (0, 0) or free (var k, one)
                let mut pin = 0u64;
                for &(bk, mask) in &groups {
                    if bk.pinned(p) {
                        pin |= mask;
                    }
                }
                (zz & !pin, hw & !pin)
            } else {
                (0, 0)
            };
            mz[j] = zz;
            ma[j] = a | (z[p] & free);
            mb[j] = b | (z[p] & free);
        }
        crate::circuit::transpose64(&mut mz);
        crate::circuit::transpose64(&mut ma);
        crate::circuit::transpose64(&mut mb);
        for t in 0..k {
            zw[256 * t + wi] = mz[t];
            aw[256 * t + wi] = ma[t];
            bw[256 * t + wi] = mb[t];
        }
    }
}

/// An aggregate child: `π_A`'s segments (proof bytes, trace, statement, kind index) and `c_A`.
pub struct AggIn<'a> {
    pub signed: &'a format::Signed,
    pub c: Digest,
    pub e: Digest,
    pub n: u64,
    pub segs: Vec<(&'a [u8], &'a [(Vec<u8>, Digest)], Digest, usize)>,
}

/// A previous-node child: the signed proof, its statement, its kind index in prototype 0 (`N4` 0,
/// `N2` 1, `N8` 2), and its kind's context for its program's node ops (the slot's run).
pub struct PrevIn<'a> {
    pub signed: &'a format::Signed,
    pub c: Digest,
    pub ix: usize,
    pub ctx: std::sync::Arc<crate::ir::NodeCtx>,
    /// The base block matrix (`walkAB` of a node program).
    pub base: &'a Circuit,
}

/// Split an aggregate's signed proof into its segments (`π_A = hdr_A ‖ π_1 ‖ …`, `tr_A = tr_1 ‖ …`).
pub fn agg_in<'a>(s: &'a format::Signed) -> AggIn<'a> {
    let pi = &s.pi;
    let k = pi[1] as usize;
    let n = u64::from_le_bytes(pi[8..16].try_into().unwrap());
    let e: Digest = pi[16..48].try_into().unwrap();
    let per = s.tr.len() / k;
    let segs = (0..k)
        .map(|i| {
            let p = &pi[48 + i * pp::PI_SIZE..48 + (i + 1) * pp::PI_SIZE];
            let so = pp::field_off(pp::F_STMT);
            let h: Digest = p[so + 1..so + 33].try_into().unwrap();
            let ni = u64::from_le_bytes(p[so + 33..so + 41].try_into().unwrap());
            let ix = match p[0] {
                pp::KIND_LEAF => 0,
                pp::KIND_P30 => 1,
                _ => 2,
            };
            (p, &s.tr[i * per..(i + 1) * per], blake2s::leaf_stmt(&h, ni), ix)
        })
        .collect();
    AggIn { signed: s, c: blake2s::leaf_stmt(&e, n), e, n, segs }
}

/// The node witness: `z`, `A₀z`, `B₀z` (`2^m` bits each), and what the checks and the prover need.
pub struct NodeWit {
    pub k: NK,
    pub z: Vec<u64>,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub bks: Vec<BK>,
    pub pubv: Vec<F>,
    pub times: Vec<(&'static str, f64)>,
    pub mstats: Vec<mfill::FillStats>,
}

fn digest_f(d: &Digest) -> [F; 2] {
    [F::from_bytes(&d[..16]), F::from_bytes(&d[16..])]
}

/// One signed child's WOTS run: the 498 blocks' inputs, the mirror sources (581 × 32 bytes), the
/// digits and step selectors.
struct Wots {
    ins: Vec<BlockIn>,
    mir: Vec<[u8; 32]>,
    digits: Vec<u32>,
}

fn wots_run(vk: &Digest, m: &Digest, s: &Sig) -> Wots {
    let d = format::wots_digits(m);
    let j = s.idx;
    let mut ins = Vec::with_capacity(WOTS_SLOT);
    let mut mir = vec![[0u8; 32]; 584];
    let mut ends = Vec::with_capacity(133);
    for i in 0..133 {
        let mut prev = [0u8; 32];
        for st in 0..3usize {
            let x = if (d[i] as usize) < st { prev } else { s.ots[i] };
            let mut msg = [0u8; 43];
            msg[1..9].copy_from_slice(&j.to_le_bytes());
            msg[11..43].copy_from_slice(&x);
            let b = BlockIn::of(BK::W43(i as u8, st as u8), [0; 8], &msg);
            prev = words_bytes(&b.out());
            ins.push(b);
            mir[3 * i + st] = x;
        }
        ends.push(if d[i] < 3 { prev } else { s.ots[i] });
    }
    // the key leaf: tagWotsLeaf ‖ enc64 j ‖ e_0 ‖ … ‖ e_132 (4,265 bytes, 67 blocks)
    let mut kl = vec![TAG_WOTS_LEAF];
    kl.extend_from_slice(&j.to_le_bytes());
    for e in &ends {
        kl.extend_from_slice(e);
    }
    let mut h = [0u32; 8];
    for u in 0..67 {
        let bk = wots_tgt(399 + u);
        let b = BlockIn::of(bk, h, &kl[64 * u..(64 * u + 64).min(kl.len())]);
        h = b.out();
        ins.push(b);
    }
    let mut jb = [0u8; 32];
    jb[..8].copy_from_slice(&j.to_le_bytes());
    mir[399] = jb;
    for u in 0..67 {
        mir[400 + u] = ends[2 * u];
    }
    for u in 0..66 {
        mir[467 + u] = ends[2 * u + 1];
    }
    // the path
    let mut cur = words_bytes(&h);
    for t in 0..16 {
        let sib = s.path[t];
        let (l, r) = if (j >> t) & 1 == 1 { (sib, cur) } else { (cur, sib) };
        let mut m1 = [0u8; 64];
        m1[0] = TAG_SIG_NODE;
        m1[1..33].copy_from_slice(&l);
        m1[33..64].copy_from_slice(&r[..31]);
        let b1 = BlockIn::of(BK::HashB1(TAG_SIG_NODE), [0; 8], &m1);
        let b2 = BlockIn::of(BK::HashB2, b1.out(), &[r[31]]);
        cur = words_bytes(&b2.out());
        ins.push(b1);
        ins.push(b2);
        mir[533 + t] = l;
        // the whole `r` (S-E13b's W5 mux is on whole elements; the `r0` family links bytes 0–30)
        mir[549 + t] = r;
        let mut r31 = [0u8; 32];
        r31[0] = r[31];
        mir[565 + t] = r31;
    }
    assert_eq!(&cur, vk, "the WOTS path's root is vk");
    Wots { ins, mir, digits: d }
}

/// `0x54 ‖ traceBytes tr`.
fn stream_bytes(tr: &[(Vec<u8>, Digest)]) -> Vec<u8> {
    let mut v = Vec::with_capacity(SEG_B * 4 + 64);
    v.push(format::TAG_TRACE);
    for (q, a) in tr {
        v.extend_from_slice(&(q.len() as u64).to_le_bytes());
        v.extend_from_slice(q);
        v.extend_from_slice(a);
    }
    v
}

/// **The node witness** of kind `k` for `vk`, the previous node (if `k.has_prev()`) and the
/// aggregate children; `protos` the dumped prototypes, `texts` their programs; `circ` the
/// general tape (`general_circuit`), `lcirc` the leaf tape (the IR's `walkAB`).
#[allow(clippy::too_many_arguments)]
/// The H region (the chains, tails, statements, WOTS: inputs, then the bits by the tape, 64 blocks
/// a batch, as a parallel job) and the L region's signature and digit cells: `z`, `a`, `b` (`a`, `b`
/// final on H; `z` zero past H but for the L cells) and the block kinds.
#[allow(clippy::type_complexity)]
fn h_part(k: NK, vk: &Digest, prev: Option<&PrevIn>, aggs: &[AggIn], signed: &[&format::Signed], circ: &Circuit) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<BK>, Vec<(&'static str, f64)>) {
    let mut times = Vec::new();
    let mut t0 = std::time::Instant::now();
    let mut mark = |n: &'static str, times: &mut Vec<(&'static str, f64)>| {
        times.push((n, t0.elapsed().as_secs_f64()));
        t0 = std::time::Instant::now();
    };
    let h_end = k.h_end();
    let mut ins = vec![BlockIn::zero(); h_end];
    let bks: Vec<BK> = (0..k.blocks()).map(|b| bk_at(k, b)).collect();
    // the two main chains (sequential compressions; the chains in parallel)
    let streams: Vec<Vec<u8>> = signed.iter().map(|s| stream_bytes(&s.tr)).collect();
    let chains: Vec<Vec<BlockIn>> = par::collect_vec(2, 1, |sg| {
        let (b0, l) = (k.ch_base(sg), k.ch_len(sg));
        let st = &streams[sg];
        let mut v = Vec::with_capacity(l);
        let mut h = [0u32; 8];
        for i in 0..l {
            let lo = (64 * i).min(st.len());
            let b = BlockIn::of(bks[b0 + i], h, &st[lo..(64 * i + 64).min(st.len())]);
            h = b.out();
            v.push(b);
        }
        v
    });
    for sg in 0..2 {
        ins[k.ch_base(sg)..k.ch_base(sg) + k.ch_len(sg)].copy_from_slice(&chains[sg]);
    }
    // the tails: candidate final blocks (the k-segment aggregate's at `F_{a,k}`), `c_A`'s hashA
    for (a, ag) in aggs.iter().enumerate() {
        let sg = k.agg_child(a);
        let kk = ag.segs.len();
        for j in 0..k.max_k() - 1 {
            let blk = k.fin_b(a) + j;
            ins[blk] = if j + 1 == kk {
                let l = agg_l(kk);
                let main = &chains[sg];
                let real = agg_b(kk) - 64 * (l - 1);
                BlockIn::of(bks[blk], main[l - 2].out(), &main[l - 1].msg[..real])
            } else {
                BlockIn::of(bks[blk], [0; 8], &[])
            };
        }
        let mut m = vec![blake2s::TAG_LEAF];
        m.extend_from_slice(&ag.e);
        m.extend_from_slice(&ag.n.to_le_bytes());
        let cb = k.c_ab(a);
        ins[cb] = BlockIn::of(BK::HashA, [0; 8], &m);
        assert_eq!(words_bytes(&ins[cb].out()), ag.c, "c_A's block");
        let dig = if kk == k.max_k() { chains[sg][k.ch_len(sg) - 1].out() } else { ins[k.fin_b(a) + kk - 1].out() };
        assert_eq!(words_bytes(&dig), format::trace_digest(&signed[sg].tr), "the aggregate's digest");
    }
    if let Some(p) = prev {
        assert_eq!(words_bytes(&chains[0][C_LEN - 1].out()), format::trace_digest(&p.signed.tr), "the previous node's digest");
    }
    // hashStmt per verifier slot: the slot's child's `stmt` field
    let slot_child: Vec<Option<(&[u8], bool)>> = (0..k.vslots())
        .map(|v| {
            if k.has_prev() && v == 0 {
                return Some((&prev.unwrap().signed.pi[..], true));
            }
            let (a, i) = if k.has_prev() { (0, v - 1) } else { (v / 4, v % 4) };
            aggs[a].segs.get(i).map(|s| (s.0, false))
        })
        .collect();
    for v in 0..k.vslots() {
        let b0 = k.stmt_b() + 3 * v;
        let so = pp::field_off(pp::F_STMT);
        let (sa, sb): (&[u8], &[u8]) = match slot_child[v] {
            Some((p, false)) => (&p[so..so + 64], &[]),
            Some((p, true)) => (&[], &p[so..so + 128]),
            None => (&[], &[]),
        };
        ins[b0] = BlockIn::of(BK::HashA, [0; 8], sa);
        ins[b0 + 1] = BlockIn::of(bks[b0 + 1], [0; 8], sb.get(..64).unwrap_or(&[]));
        ins[b0 + 2] = BlockIn::of(BK::HashB2, ins[b0 + 1].out(), sb.get(64..).unwrap_or(&[]));
    }
    // WOTS and the mirrors, per signed child
    let wots: Vec<Wots> = (0..2).map(|sg| wots_run(vk, &format::trace_digest(&signed[sg].tr), &signed[sg].sig)).collect();
    for sg in 0..2 {
        ins[k.wots_b(sg)..k.wots_b(sg) + WOTS_SLOT].copy_from_slice(&wots[sg].ins);
    }
    mark("h_inputs", &mut times);
    // the bits: H by the tape, 64 blocks a batch; the free blocks are zero here
    let words = k.blocks() * 256;
    let (mut z, mut a, mut b) = (crate::witness::alloc_u64(words), crate::witness::alloc_u64(words), crate::witness::alloc_u64(words));
    let nbat = h_end.div_ceil(64);
    {
        let (pz, pa, pb) = (par::SyncPtr(z.as_mut_ptr()), par::SyncPtr(a.as_mut_ptr()), par::SyncPtr(b.as_mut_ptr()));
        par::run(nbat, &|g| {
            let (pz, pa, pb) = (pz, pa, pb);
            let (lo, hi) = (64 * g, (64 * g + 64).min(h_end));
            let n = hi - lo;
            let (zs, as_, bs) = unsafe {
                (
                    std::slice::from_raw_parts_mut(pz.0.add(256 * lo), 256 * n),
                    std::slice::from_raw_parts_mut(pa.0.add(256 * lo), 256 * n),
                    std::slice::from_raw_parts_mut(pb.0.add(256 * lo), 256 * n),
                )
            };
            trace_blocks(circ, &ins[lo..hi], &bks[lo..hi], zs, as_, bs);
        });
    }
    par::for_each_chunk_mut(&mut z[256 * h_end..], 1 << 16, |_, c| c.fill(0));
    mark("h_trace", &mut times);
    // the WM mirrors (free blocks: z only; a = b = z at the end)
    let setbits = |z: &mut [u64], blk: usize, pos: usize, bytes: &[u8]| {
        for (i, &by) in bytes.iter().enumerate() {
            for bit in 0..8 {
                let p = blk * (1 << 14) + pos + 8 * i + bit;
                if (by >> bit) & 1 == 1 {
                    z[p / 64] |= 1 << (p % 64);
                }
            }
        }
    };
    for sg in 0..2 {
        for (g, src) in wots[sg].mir.iter().enumerate().take(581) {
            setbits(&mut z, k.wm_b(sg) + g / 4, 256 * (g % 4), src);
        }
    }
    // L: per slot the signature (signed child σ in slot σ, provisional), digits, step selectors,
    // position bits, the kind selector; M: the slot fill
    let fz = |z: &mut [u64], e: usize, x: F| {
        z[2 * e] = x.lo;
        z[2 * e + 1] = x.hi;
    };
    let lb = k.l_base() * 128;
    for sg in 0..2 {
        let s = &signed[sg].sig;
        let base = lb + sg * (1 << 14);
        fz(&mut z, base, F::new(s.idx, 0));
        for (i, d) in s.ots.iter().chain(s.path.iter()).enumerate() {
            let [x, y] = digest_f(d);
            fz(&mut z, base + 1 + 2 * i, x);
            fz(&mut z, base + 2 + 2 * i, y);
        }
        for (i, &d) in wots[sg].digits.iter().enumerate() {
            fz(&mut z, base + 299 + 2 * i, F::new((d & 1) as u64, 0));
            fz(&mut z, base + 300 + 2 * i, F::new((d >> 1) as u64, 0));
            for st in 1..4u32 {
                fz(&mut z, base + 299 + 266 + 3 * i + (st as usize - 1), F::new((d < st) as u64, 0));
            }
        }
    }
    // S-E13b's L cells per signed child σ (stride σ, offsets 8704–11648; `S-E13b-RESULT` §6)
    let el = |z: &[u64], c: usize| F::new(z[2 * c], z[2 * c + 1]);
    let bit = |x: F, q: usize| F::new(((if q < 64 { x.lo } else { x.hi }) >> (q % 64)) & 1, 0);
    let g = F::new(2, 0);
    let gi = g.inv();
    for sg in 0..2 {
        let base = lb + sg * (1 << 14);
        let s = &signed[sg].sig;
        // 8704 + t: the index bits
        for t in 0..16 {
            fz(&mut z, base + 8704 + t, F::new((s.idx >> t) & 1, 0));
        }
        // 8720 + i: the checksum's running products R_i = Π_{j<i} f_j, f_j = g^{3−d_j} (j < 128),
        // g^{−4^t c_t} (checksum digit t = j − 128)
        let d = &wots[sg].digits;
        let mut r = F::ONE;
        for i in 1..=132 {
            let j = i - 1;
            let f = if j < 128 { g.pow(3) * gi.pow(d[j] as u128) } else { gi.pow((1u128 << (2 * (j - 128))) * d[j] as u128) };
            r *= f;
            fz(&mut z, base + 8720 + i, r);
        }
        // 8960 + 128 t + q: the bits of mirror 549 + t's element 1 (r's bytes 16–31)
        for t in 0..16 {
            let g549 = 549 + t;
            let x = el(&z, (k.wm_b(sg) + g549 / 4) * 128 + 2 * (g549 % 4) + 1);
            for q in 0..128 {
                fz(&mut z, base + 8960 + 128 * t + q, bit(x, q));
            }
        }
        if !k.is_agg(sg) {
            continue;
        }
        let a = k.agg_of(sg);
        let kk = aggs[a].segs.len();
        // 11008 + 2(j − 1) + h: T_{j,h} = [k = j]·h_out(F_j)_h (F_maxK: the main chain's last block)
        let fj = if kk == k.max_k() { k.ch_base(sg) + k.ch_len(sg) - 1 } else { k.fin_b(a) + kk - 1 };
        for h in 0..2 {
            let x = el(&z, fj * 128 + 2 + h);
            fz(&mut z, base + 11008 + 2 * (kk - 1) + h, x);
        }
        // 11264 + 128(j − 2) + q, 2 ≤ j ≤ maxK: the bits of main block aggL j − 1's element 7
        for j in 2..=k.max_k() {
            let x = el(&z, (k.ch_base(sg) + agg_l(j) - 1) * 128 + 7);
            for q in 0..128 {
                fz(&mut z, base + 11264 + 128 * (j - 2) + q, bit(x, q));
            }
        }
    }
    mark("l_mirrors", &mut times);
    (z, a, b, bks, times)
}

/// A slot's fill: the M cells, the fill's report, the program run's bits.
pub type Fill = (Vec<F>, mfill::FillStats, Vec<bool>);

/// One verifier slot's fill: the prototype program's run at the child's index (`run`: the child's
/// proof, trace, statement, index; `None`: inactive), then `mfill::fill`. Slot `v` names it in the report.
#[allow(clippy::too_many_arguments)]
fn slot_fill(p: &mfill::Proto, text: &str, p0: bool, run: Option<(&[u8], &[(Vec<u8>, Digest)], Digest, usize)>, prev: Option<&PrevIn>, vk: &Digest, lcirc: &Circuit, v: usize) -> Fill {
    match run {
        Some((pi, tr, c, ix)) => {
            let o = crate::oracle::Seq::new(tr);
            let sp = crate::prof::span(if p0 { "wit.run_p0" } else { "wit.run_p1" });
            let spec = crate::ir::spec_kind(text, ix);
            let (r, regs) = match prev {
                Some(p) if p0 => crate::ir::run_node_regs(&spec, p.ctx.clone(), p.base, &o, vk, &c, pi),
                _ => crate::ir::run_regs(&spec, lcirc, &o, vk, &c, pi),
            };
            drop(sp);
            let mut st = mfill::FillStats::default();
            if !r.ok || !o.consumed() {
                st.first_conflicts.push(format!("slot {v}: program run ok={} failed={:?} consumed={}", r.ok, r.failed, o.consumed()));
            }
            let bits: Vec<bool> = regs.iter().zip(texts_bitof(text)).filter(|(_, b)| *b).map(|(r, _)| matches!(r, V::Bit(true))).collect();
            // a segment below its kind's cap (`L32` 2^18, `P30` 2^16, `P31` 2^17 steps) has its own plan
            let partial = !p0 && {
                let so = pp::field_off(pp::F_STMT);
                let n = u64::from_le_bytes(pi[so + 33..so + 41].try_into().unwrap());
                n < [1u64 << 18, 1 << 16, 1 << 17][ix]
            };
            let (val, st2) = mfill::fill_part(p, Some((&regs, ix)), partial);
            st.written = st2.written;
            st.solved = st2.solved;
            st.zeroed = st2.zeroed;
            st.conflicts = st2.conflicts;
            st.first_conflicts.extend(st2.first_conflicts);
            st.failed_rows = st2.failed_rows;
            st.first_failed = st2.first_failed;
            st.form_mismatch = st2.form_mismatch;
            st.first_form_mismatch = st2.first_form_mismatch;
            st.replayed = st2.replayed;
            (val, st, bits)
        }
        None => {
            let (val, st) = mfill::fill(p, None);
            (val, st, Vec::new())
        }
    }
}

/// Slot 0's fill of a node with a previous node (its program run on `prev` and the solve): it needs
/// only `prev`, so a step computes it beside its aggregate and hands it to `witness`.
pub fn slot0_fill(prev: &PrevIn, vk: &Digest, protos: &[mfill::Proto; 2], texts: &[String; 2], lcirc: &Circuit) -> Fill {
    slot_fill(&protos[0], &texts[0], true, Some((&prev.signed.pi[..], &prev.signed.tr[..], prev.c, prev.ix)), Some(prev), vk, lcirc, 0)
}

#[allow(clippy::too_many_arguments)]
pub fn witness(k: NK, vk: &Digest, prev: Option<&PrevIn>, aggs: &[AggIn], protos: &[mfill::Proto; 2], texts: &[String; 2], circ: &Circuit, lcirc: &Circuit, pre0: Option<Fill>) -> NodeWit {
    let mut times = Vec::new();
    let mut t0 = std::time::Instant::now();
    let mut mark = |n: &'static str, times: &mut Vec<(&'static str, f64)>| {
        times.push((n, t0.elapsed().as_secs_f64()));
        t0 = std::time::Instant::now();
    };
    assert_eq!(prev.is_some(), k.has_prev());
    assert_eq!(aggs.len(), k.n_agg());
    for a in aggs {
        assert!((1..=k.max_k()).contains(&a.segs.len()), "an aggregate of 1 … maxK segments");
    }
    let signed: Vec<&format::Signed> = (0..2).map(|sg| if k.is_agg(sg) { aggs[k.agg_of(sg)].signed } else { prev.unwrap().signed }).collect();
    let stmts: Vec<Digest> = (0..2).map(|sg| if k.is_agg(sg) { aggs[k.agg_of(sg)].c } else { prev.unwrap().c }).collect();
    // the slot runs (prototype program at the child's index) and fills, in parallel
    struct SlotJob<'a> {
        proto: usize,
        run: Option<(&'a [u8], &'a [(Vec<u8>, Digest)], Digest, usize)>,
    }
    let jobs: Vec<SlotJob> = (0..k.vslots())
        .map(|v| {
            if k.has_prev() && v == 0 {
                let p = prev.unwrap();
                return SlotJob { proto: 0, run: Some((&p.signed.pi[..], &p.signed.tr[..], p.c, p.ix)) };
            }
            let (a, i) = if k.has_prev() { (0, v - 1) } else { (v / 4, v % 4) };
            SlotJob { proto: 1, run: aggs[a].segs.get(i).copied() }
        })
        .collect();
    // the solve plans: the inactive ones need no child (`warm_plans`, before the request); the
    // first active slot of each prototype records its plan, the other slots replay it
    let sp = crate::prof::span("wit.warm_plans");
    warm_plans(protos);
    drop(sp);
    let fill_job = |v: usize| {
        let j = &jobs[v];
        slot_fill(&protos[j.proto], &texts[j.proto], j.proto == 0, j.run, prev, vk, lcirc, v)
    };
    // slot 0's fill when the caller computed it already (`slot0_fill`, during the aggregate)
    let mut pre0 = pre0;
    // the fills that start beside the H part: every slot whose solve order is known (recorded
    // before the request, e.g. by `prover setup`), and the first active slot of a prototype
    // without one (it records the order the others replay)
    let known = |j: &SlotJob| match j.run {
        Some(_) => protos[j.proto].plan[1..].iter().any(|o| o.get().is_some()),
        None => protos[j.proto].plan[0].get().is_some(),
    };
    let mut firsts: Vec<usize> = (0..jobs.len()).filter(|&v| !(v == 0 && pre0.is_some()) && known(&jobs[v])).collect();
    for p in 0..2 {
        if let Some(v) = (0..jobs.len()).find(|&v| jobs[v].proto == p && jobs[v].run.is_some() && !(v == 0 && pre0.is_some()) && !firsts.contains(&v)) {
            if !firsts.iter().any(|&f| jobs[f].proto == p && jobs[f].run.is_some()) {
                firsts.push(v);
            }
        }
    }
    // the H part (one task; its block trace is a parallel job of its own, taken by idle workers)
    // beside those fills (a slot's program run and solve are serial)
    let h_out: std::sync::Mutex<Option<(Vec<u64>, Vec<u64>, Vec<u64>, Vec<BK>, Vec<(&'static str, f64)>)>> = std::sync::Mutex::new(None);
    let first_out: Vec<std::sync::Mutex<Option<Fill>>> = firsts.iter().map(|_| std::sync::Mutex::new(None)).collect();
    par::run(1 + firsts.len(), &|i| {
        if i == 0 {
            *h_out.lock().unwrap() = Some(h_part(k, vk, prev, aggs, &signed, circ));
        } else {
            *first_out[i - 1].lock().unwrap() = Some(fill_job(firsts[i - 1]));
        }
    });
    let (mut z, mut a, mut b, bks, htimes) = h_out.into_inner().unwrap().unwrap();
    times.extend(htimes);
    mark("h_first_fills", &mut times);
    let mut first_fills: Vec<Option<Fill>> = first_out.into_iter().map(|m| m.into_inner().unwrap()).collect();
    let rest: Vec<usize> = (0..jobs.len()).filter(|&v| !firsts.contains(&v) && !(v == 0 && pre0.is_some())).collect();
    let mut rest_fills: Vec<Option<Fill>> = par::collect_vec(rest.len(), 1, |i| Some(fill_job(rest[i])));
    let fills: Vec<Fill> = (0..jobs.len())
        .map(|v| match firsts.iter().position(|&f| f == v) {
            Some(i) => first_fills[i].take().unwrap(),
            None if v == 0 && pre0.is_some() => pre0.take().unwrap(),
            None => rest_fills[rest.iter().position(|&r| r == v).unwrap()].take().unwrap(),
        })
        .collect();
    mark("rest_fills", &mut times);
    let h_end = k.h_end();
    let lb = k.l_base() * 128;
    let fz = |z: &mut [u64], e: usize, x: F| {
        z[2 * e] = x.lo;
        z[2 * e + 1] = x.hi;
    };
    let mut mstats = Vec::new();
    for (v, (val, st, bits)) in fills.into_iter().enumerate() {
        let base = k.one_cell() + v * mfill::SLOT;
        for (l, x) in val.iter().enumerate() {
            fz(&mut z, base + l, *x);
        }
        let lsl = lb + v * (1 << 14);
        for (i, &bt) in bits.iter().enumerate().take(7552) {
            fz(&mut z, lsl + 299 + 266 + 399 + i, F::new(bt as u64, 0));
        }
        if let Some((_, _, _, ix)) = jobs[v].run {
            fz(&mut z, lsl + 8516 + ix, F::ONE);
        }
        mstats.push(st);
    }
    // a = b = z on every block from H's end (L, M, free)
    let (az, bz) = (&mut a[256 * h_end..], &mut b[256 * h_end..]);
    az.copy_from_slice(&z[256 * h_end..]);
    bz.copy_from_slice(&z[256 * h_end..]);
    // the WM / spare blocks inside H are free: a = b = z there too
    for blk in k.wm_b(0)..k.h_used() {
        for w in 256 * blk..256 * blk + 256 {
            a[w] = z[w];
            b[w] = z[w];
        }
    }
    mark("l_m_write", &mut times);
    let mut pubv = vec![F::ONE];
    for sg in 0..2 {
        pubv.extend(digest_f(vk));
        pubv.extend(digest_f(&stmts[sg]));
    }
    NodeWit { k, z, a, b, bks, pubv, times, mstats }
}

/// Record both prototypes' inactive solve plans (no child needed: done before a request).
pub fn warm_plans(protos: &[mfill::Proto; 2]) {
    // pass 13: the per-prototype tables (`ByCell`, `fcinv`) and every recorded order's level
    // schedule as separate tasks over all threads (the schedules are independent)
    let mut jobs: Vec<(usize, usize)> = (0..2).flat_map(|p| [(p, 100), (p, 101)]).collect();
    jobs.extend((0..2).flat_map(|p| (1..mfill::PLAN_KEYS).filter(move |&k| protos[p].plan[k].get().is_some()).map(move |k| (p, k))));
    par::run(jobs.len(), &|j| {
        let (p, k) = jobs[j];
        let pr = &protos[p];
        match k {
            100 => {
                mfill::warm_adjacency(pr);
                if pr.plan[0].get().is_none() {
                    mfill::fill(pr, None);
                }
            }
            101 => {
                let _ = pr.by_cell();
                let _ = pr.fcinv();
            }
            k => {
                let _ = pr.sched_for(k);
            }
        }
    });
}

/// Which registers of a program are `bitOf` results (the position bits, in order).
fn texts_bitof(text: &str) -> Vec<bool> {
    let mut v = Vec::with_capacity(110_000);
    for line in text.lines() {
        let Some((lhs, dst)) = line.split_once(" → ") else { continue };
        let isb = lhs.starts_with("bitOf ");
        for _ in dst.split(' ') {
            v.push(isb);
        }
    }
    v
}

/// The checks' report.
#[derive(Debug, Default)]
pub struct Checks {
    pub h_bad_blocks: usize,
    pub first_bad: Vec<(usize, BK)>,
    pub chain_bad: usize,
    pub links_bad: usize,
    pub cells_bad: usize,
    pub l_bad: usize,
    pub m_rows: usize,
    pub m_bad: usize,
    pub link_rows_bad: usize,
    /// The first failing link rows' global indices.
    pub first_bad_links: Vec<u32>,
}

/// **Every relation of the node, checked directly on the witness.**
pub fn check(w: &NodeWit, protos: &[mfill::Proto; 2], kt: &mfill::KindTab) -> Checks {
    let k = w.k;
    let mut ch = Checks::default();
    let z = &w.z;
    let bit = |p: usize| (z[p / 64] >> (p % 64)) & 1 == 1;
    // H: (A₀z)(B₀z) = z + E per block (E: the target's 1 bits)
    let bad: Vec<usize> = par::map_chunks(k.blocks(), 256, |lo, hi| {
        let mut v = Vec::new();
        for blk in lo..hi {
            let bk = w.bks[blk];
            let mut ok = true;
            for wi in 0..256 {
                let mut e = 0u64;
                if bk != BK::Free && wi < 19 {
                    for j in 0..64 {
                        if bk.target(64 * wi + j) == Some(true) {
                            e |= 1 << j;
                        }
                    }
                }
                let i = 256 * blk + wi;
                ok &= w.a[i] & w.b[i] == z[i] ^ e;
            }
            if !ok {
                v.push(blk);
            }
        }
        v
    })
    .into_iter()
    .flatten()
    .collect();
    ch.h_bad_blocks = bad.len();
    ch.first_bad = bad.iter().take(8).map(|&b| (b, w.bks[b])).collect();
    // the masked chain links
    for y in 0..k.blocks() - 1 {
        if k.chain_lk(y) {
            let (o, i) = (256 * y + 4, 256 * (y + 1));
            if z[o..o + 4] != z[i..i + 4] {
                ch.chain_bad += 1;
            }
        }
    }
    // the eight link families against the mirrors
    for sg in 0..2 {
        for f in &FAMS {
            for t in 0..f.n {
                let sb = k.wots_b(sg) + (f.src)(t);
                let g = (f.mir)(t);
                let mb = k.wm_b(sg) + g / 4;
                for s in 0..8 * f.len {
                    if bit(sb * (1 << 14) + 512 + 8 * f.off + s) != bit(mb * (1 << 14) + 256 * (g % 4) + f.mbo + s) {
                        ch.links_bad += 1;
                    }
                }
            }
        }
    }
    let fv = |e: usize| F { lo: z[2 * e], hi: z[2 * e + 1] };
    // the public cells
    for (c, v) in k.cells4().iter().zip(w.pubv.iter()) {
        if fv(*c) != *v {
            ch.cells_bad += 1;
        }
    }
    // L: every declared bit is 0 or 1
    for v in 0..k.vslots() {
        for j in 0..8220 {
            let x = fv(k.l_base() * 128 + v * (1 << 14) + 299 + j);
            if x != F::ZERO && x != F::ONE {
                ch.l_bad += 1;
            }
        }
    }
    // M: every slot's prototype rows (moved) and the link rows
    let one = k.one_cell();
    for v in 0..k.vslots() {
        let (pi, ..) = kt.slots[v];
        let p = &protos[pi];
        let base = (pi * mfill::SLOT) as u32;
        let to = one + v * mfill::SLOT;
        let bad = par::map_chunks(p.rows.len(), 4096, |lo, hi| {
            (lo..hi).filter(|&i| {
                let [a, b, c] = p.rows.eval(i, &|x| fv(to + (x - base) as usize));
                a * b != c
            })
            .count()
        });
        ch.m_rows += p.rows.len();
        ch.m_bad += bad.iter().sum::<usize>();
    }
    for i in 0..kt.links.len() {
        let [a, b, c] = kt.links.eval(i, &|x| fv(x as usize));
        if a * b != c {
            ch.link_rows_bad += 1;
            if ch.first_bad_links.len() < 400 {
                ch.first_bad_links.push(kt.links.idx[i]);
            }
        }
    }
    ch
}

/// The general tape compiled for `trace_blocks`: one slot per block position (an input's bit, a
/// gate's value), a zero slot, and temporaries for the XOR forms, reused once dead (the tape's
/// ~85 k forms live in a few hundred slots, so a batch's values stay in cache). An op is
/// `(dst | GATE, a, b)`: a gate writes `a & b` to its position and keeps `a`, `b` (its row's forms).
/// Position `p`'s slot is `tperm(p)`: four consecutive 64-position words interleaved, so that
/// `trace_out` loads the four words' rows `j` at once.
struct TraceProg {
    ops: Vec<[u32; 3]>,
    slots: usize,
}

const GATE_OP: u32 = 1 << 31;

#[inline(always)]
fn tperm(p: usize) -> usize {
    (p & !255) | ((p & 63) << 2) | ((p >> 6) & 3)
}

fn trace_prog(c: &Circuit) -> &'static TraceProg {
    static P: std::sync::OnceLock<TraceProg> = std::sync::OnceLock::new();
    let p = P.get_or_init(|| {
        const BLOCK: usize = 1 << 14;
        let n = c.nodes.len();
        let mut last = vec![usize::MAX; n];
        for (i, nd) in c.nodes.iter().enumerate() {
            if let Node::Xor(a, b) | Node::Gate(_, a, b) = *nd {
                last[a as usize] = i;
                last[b as usize] = i;
            }
        }
        let mut is_gate = vec![false; BLOCK];
        let mut slot = vec![u32::MAX; n];
        let mut free: Vec<u32> = Vec::new();
        let mut is_free = vec![false; n + BLOCK + 1];
        let mut slots = BLOCK as u32 + 1;
        let mut ops = Vec::new();
        for (i, nd) in c.nodes.iter().enumerate() {
            match *nd {
                Node::Zero => slot[i] = BLOCK as u32,
                Node::Var(p) => {
                    assert!(!is_gate[p as usize], "a gate position read as an input");
                    slot[i] = tperm(p as usize) as u32;
                }
                Node::Xor(a, b) | Node::Gate(_, a, b) => {
                    let (sa, sb) = (slot[a as usize], slot[b as usize]);
                    assert!(sa != u32::MAX && sb != u32::MAX);
                    for &(x, sx) in &[(a, sa), (b, sb)] {
                        if last[x as usize] == i && sx > BLOCK as u32 && !is_free[sx as usize] {
                            is_free[sx as usize] = true;
                            free.push(sx);
                        }
                    }
                    if let Node::Gate(p, ..) = *nd {
                        assert!(!is_gate[p as usize] && c.rows[p as usize] == Some((a, b)), "one gate per position, its row");
                        is_gate[p as usize] = true;
                        slot[i] = tperm(p as usize) as u32;
                        ops.push([slot[i] | GATE_OP, sa, sb]);
                    } else if last[i] != usize::MAX {
                        let d = free.pop().unwrap_or_else(|| {
                            slots += 1;
                            slots - 1
                        });
                        is_free[d as usize] = false;
                        slot[i] = d;
                        ops.push([d, sa, sb]);
                    }
                }
            }
        }
        assert_eq!(is_gate.iter().filter(|&&g| g).count(), c.rows.iter().filter(|r| r.is_some()).count(), "every row a gate's");
        TraceProg { ops, slots: slots as usize }
    });
    p
}

/// Compile the general tape for `trace_blocks` now (before a request's clock).
pub fn warm_trace(c: &Circuit) {
    let _ = trace_prog(c);
}

/// The pinned input positions of a kind, as 19 words over positions `0 … 1215` (`BK::pinned`).
fn pin_words(bk: BK) -> [u64; 19] {
    let mut w = [0u64; 19];
    if bk == BK::Free {
        return w;
    }
    if bk.h0_pin() {
        w[..4].fill(!0);
    }
    for b in 0..64 {
        if bk.msg_pin(b).is_some() {
            w[8 + b / 8] |= 0xFF << (8 * (b % 8));
        }
    }
    w[16] = !0;
    w[17] = !0;
    w[18] = 1;
    w
}

/// **Up to 64 blocks of any kinds, bit-sliced** (as `trace_blocks_ref`, faster): the inputs by
/// 64×64 transposes, the compiled tape (`trace_prog`), the gates' forms kept at the gate, the
/// inputs' rows `(z & !pin, !pin)` by the kinds' pin words, then `trace_out`.
pub fn trace_blocks(c: &Circuit, ins: &[BlockIn], bks: &[BK], zw: &mut [u64], aw: &mut [u64], bw: &mut [u64]) {
    const BLOCK: usize = 1 << 14;
    let k = ins.len();
    assert!(k <= 64 && bks.len() == k);
    let prog = trace_prog(c);
    let mut vals = vec![0u64; prog.slots];
    let (mut ga, mut gb) = (vec![0u64; BLOCK], vec![0u64; BLOCK]);
    let lanes = if k == 64 { !0 } else { (1u64 << k) - 1 };
    let mut free = 0u64;
    let mut groups: Vec<(BK, u64)> = Vec::new();
    for (t, bk) in bks.iter().enumerate() {
        if *bk == BK::Free {
            free |= 1 << t;
        }
        match groups.iter_mut().find(|g| g.0 == *bk) {
            Some(g) => g.1 |= 1 << t,
            None => groups.push((*bk, 1 << t)),
        }
    }
    let pins: Vec<([u64; 19], u64)> = groups.iter().map(|&(bk, mask)| (pin_words(bk), mask)).collect();
    // the inputs: per 64-position word, the lanes' words transposed
    let word = |b: &BlockIn, w: usize| -> u64 {
        match w {
            0..=3 => b.h[2 * w] as u64 | (b.h[2 * w + 1] as u64) << 32,
            8..=15 => u64::from_le_bytes(b.msg[8 * (w - 8)..8 * (w - 7)].try_into().unwrap()),
            16 => b.t,
            17 => b.f0 as u64,
            18 => 1,
            _ => 0,
        }
    };
    let mut m = [0u64; 64];
    for w in (0..4).chain(8..19) {
        for t in 0..64 {
            m[t] = if t < k && free >> t & 1 == 0 { word(&ins[t], w) } else { 0 };
        }
        crate::circuit::transpose64(&mut m);
        for j in 0..64 {
            vals[tperm(64 * w + j)] = m[j];
        }
    }
    {
        let v = &mut vals[..];
        for &[d, a, b] in &prog.ops {
            let (x, y) = (v[a as usize], v[b as usize]);
            if d & GATE_OP != 0 {
                let p = (d & !GATE_OP) as usize;
                ga[p] = x;
                gb[p] = y;
                v[p] = x & y;
            } else {
                v[d as usize] = x ^ y;
            }
        }
    }
    let hw = lanes & !free;
    // the inputs' rows into the form arrays (every other non-gate position keeps the zero row)
    for p in (0..256).chain(512..pp::ONE_POS) {
        if c.rows[p].is_none() {
            let mut pin = 0u64;
            for (pw, mask) in &pins {
                if pw[p / 64] >> (p % 64) & 1 == 1 {
                    pin |= mask;
                }
            }
            let q = tperm(p);
            ga[q] = vals[q] & !pin;
            gb[q] = !pin;
        }
    }
    trace_out(&vals[..BLOCK], &ga, &gb, hw, free, k, zw, aw, bw);
}

/// `trace_blocks`' output (`z`, `ga`, `gb` in `tperm` order): per 64 positions, `z & hw`,
/// `(A & hw) | (z & free)`, `(B & hw) | (z & free)` transposed to the lanes' words.
#[allow(clippy::too_many_arguments)]
fn trace_out(z: &[u64], ga: &[u64], gb: &[u64], hw: u64, free: u64, k: usize, zw: &mut [u64], aw: &mut [u64], bw: &mut [u64]) {
    #[cfg(target_arch = "x86_64")]
    if std::is_x86_feature_detected!("avx2") {
        // SAFETY: AVX2 is present.
        return unsafe { trace_out_avx2(z, ga, gb, hw, free, k, zw, aw, bw) };
    }
    let (mut mz, mut ma, mut mb) = ([0u64; 64], [0u64; 64], [0u64; 64]);
    for wi in 0..z.len() / 64 {
        for j in 0..64 {
            let p = tperm(64 * wi + j);
            let zf = z[p] & free;
            mz[j] = z[p] & hw;
            ma[j] = (ga[p] & hw) | zf;
            mb[j] = (gb[p] & hw) | zf;
        }
        crate::circuit::transpose64(&mut mz);
        crate::circuit::transpose64(&mut ma);
        crate::circuit::transpose64(&mut mb);
        for t in 0..k {
            zw[256 * t + wi] = mz[t];
            aw[256 * t + wi] = ma[t];
            bw[256 * t + wi] = mb[t];
        }
    }
}

/// Four 64-position words at a time: lane `i` of a vector is word `4q + i`; each of the three
/// matrices is transposed by six vertical stages and stored as four consecutive words per lane.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
#[allow(clippy::too_many_arguments)]
unsafe fn trace_out_avx2(z: &[u64], ga: &[u64], gb: &[u64], hw: u64, free: u64, k: usize, zw: &mut [u64], aw: &mut [u64], bw: &mut [u64]) {
    use std::arch::x86_64::*;
    #[inline(always)]
    unsafe fn stage<const W: i32>(m: &mut [__m256i; 64], mask: u64) {
        let mv = _mm256_set1_epi64x(mask as i64);
        let w = W as usize;
        for i in 0..64 {
            if i & w == 0 {
                let t = _mm256_and_si256(_mm256_xor_si256(_mm256_srli_epi64::<W>(m[i]), m[i + w]), mv);
                m[i + w] = _mm256_xor_si256(m[i + w], t);
                m[i] = _mm256_xor_si256(m[i], _mm256_slli_epi64::<W>(t));
            }
        }
    }
    #[inline(always)]
    unsafe fn transpose(m: &mut [__m256i; 64]) {
        stage::<32>(m, 0x0000_0000_FFFF_FFFF);
        stage::<16>(m, 0x0000_FFFF_0000_FFFF);
        stage::<8>(m, 0x00FF_00FF_00FF_00FF);
        stage::<4>(m, 0x0F0F_0F0F_0F0F_0F0F);
        stage::<2>(m, 0x3333_3333_3333_3333);
        stage::<1>(m, 0x5555_5555_5555_5555);
    }
    let (hv, fv) = (_mm256_set1_epi64x(hw as i64), _mm256_set1_epi64x(free as i64));
    let ld = |s: &[u64], i: usize| _mm256_loadu_si256(s.as_ptr().add(i) as *const __m256i);
    let mut m = [_mm256_setzero_si256(); 64];
    for q in 0..z.len() / 256 {
        let o = 256 * q;
        for (s, dst) in [(0usize, &mut *zw), (1, &mut *aw), (2, &mut *bw)] {
            for j in 0..64 {
                let zj = ld(z, o + 4 * j);
                m[j] = match s {
                    0 => _mm256_and_si256(zj, hv),
                    1 => _mm256_or_si256(_mm256_and_si256(ld(ga, o + 4 * j), hv), _mm256_and_si256(zj, fv)),
                    _ => _mm256_or_si256(_mm256_and_si256(ld(gb, o + 4 * j), hv), _mm256_and_si256(zj, fv)),
                };
            }
            transpose(&mut m);
            for t in 0..k {
                _mm256_storeu_si256(dst.as_mut_ptr().add(256 * t + 4 * q) as *mut __m256i, m[t]);
            }
        }
    }
}

#[cfg(test)]
mod pass11_tests {
    use super::*;

    /// `trace_blocks` (compiled tape, transposes) equals `trace_blocks_ref` on full and partial
    /// batches of mixed kinds, free blocks included.
    #[test]
    fn trace_blocks_matches_ref() {
        let c = general_circuit();
        let mut s = 0x1234_5678_9abc_def0u64;
        let mut rnd = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let kinds = [BK::StreamStart, BK::Stream(128, false), BK::Stream(77, true), BK::StreamEnd41, BK::HashA, BK::HashB1(3), BK::HashB2, BK::W43(5, 9), BK::Free];
        for &k in &[64usize, 37, 1] {
            let bks: Vec<BK> = (0..k).map(|i| kinds[(rnd() as usize + i) % kinds.len()]).collect();
            let ins: Vec<BlockIn> = bks
                .iter()
                .map(|&bk| {
                    let h: [u32; 8] = std::array::from_fn(|_| rnd() as u32);
                    let msg: Vec<u8> = (0..64).map(|_| rnd() as u8).collect();
                    if bk == BK::Free { BlockIn::zero() } else { BlockIn::of(bk, h, &msg) }
                })
                .collect();
            let n = 256 * k;
            let (mut z0, mut a0, mut b0) = (vec![0u64; n], vec![0u64; n], vec![0u64; n]);
            let (mut z1, mut a1, mut b1) = (vec![0u64; n], vec![0u64; n], vec![0u64; n]);
            trace_blocks_ref(&c, &ins, &bks, &mut z0, &mut a0, &mut b0);
            trace_blocks(&c, &ins, &bks, &mut z1, &mut a1, &mut b1);
            assert!(z0 == z1 && a0 == a1 && b0 == b1, "k = {k}");
        }
    }
}
