//! The full `V_S`: every part of FORMAT6 §6 walked by refv (one verifier; R3's `r3v` `refv-full` is a wrapper of this).
//!
//! [`FullStubs`] fills [`crate::vs::Stubs`]: §6.2 is R2's [`crate::tree::verify`], §6.3 [`crate::sponge::verify`],
//! §6.4a [`crate::typed::verify_typed`] then the native `Φ_Q(accOut.pt) = accOut.y` (FORMAT6 §T, `V_S`'s last check,
//! order-independent), §6.4b [`crate::minibus::verify`]. `h` and `accIn` are read from `HDR`, never from a prover's
//! side file. [`verify_full_file`] is `acc` on the signed file and also requires FORMAT6's 53 claims and `qS = 4,349`.
//!
//! STUBs (until CD's generator, R3-node.md §3): the typed circuit `Q` (`r3typed::circuit`, or `$LVM6_Q_BLOB`), the
//! mini-bus tables (`r3mb::stub`, seed [`MB_SEED`]); a proof is valid "for STUB Q/MB" only.

use crate::chain::{TraceAsk, VChain};
use crate::format::{QUERY_CAP, from_file, sig_ok, trace_digest};
use crate::shape::Shape;
use crate::stack::Commit;
use crate::vs::{Deferred, Report, Stubs, verify_pi};
use crate::{Digest, E, Reject, Res, require};

/// The mini-bus STUB tables' seed (`lvm6-prover full6`'s `MB_SEED`).
pub const MB_SEED: u64 = 1;
/// FORMAT6 v2.4 §6.5 / §7.
pub const FULL_CLAIMS: usize = 53;
pub const FULL_QS: usize = 4_349;

/// Which parts a proof carries: `all`, or a comma list of `tree`, `sponge`, `typed`, `mb` (dev proofs of a prefix).
#[derive(Clone, Debug)]
pub struct FullStubs {
    pub h: Digest,
    pub tree: bool,
    pub sponge: bool,
    pub typed: bool,
    pub mb: bool,
    /// `HDR`'s lanes (the typed `PUB` region) and `accIn`.
    pub hdr_lanes: Vec<u64>,
    pub acc_in: Vec<E>,
}

impl FullStubs {
    pub fn new(hdr: &[u8], parts: &str) -> Self {
        let all = parts == "all";
        let has = |p: &str| all || parts.split(',').any(|x| x == p);
        Self {
            h: hdr[24..56].try_into().unwrap(),
            tree: has("tree") || has("sponge") || has("typed") || has("mb"),
            sponge: has("sponge"),
            typed: has("typed"),
            mb: has("mb"),
            hdr_lanes: hdr.chunks_exact(8).map(|b| u64::from_le_bytes(b.try_into().unwrap())).collect(),
            acc_in: hdr[120..].chunks_exact(16).map(|b| crate::e_of(fs6::codec::get_e(b))).collect(),
        }
    }

    pub fn is_full(&self) -> bool {
        self.tree && self.sponge && self.typed && self.mb
    }
}

impl Stubs for FullStubs {
    fn tree<'a>(&mut self, ch: &mut VChain<'a>, sh: &Shape, _c: &Commit) -> Res<Vec<Deferred>> {
        if !self.tree {
            return Ok(Vec::new());
        }
        Ok(crate::tree::verify(ch, sh.log_blocks as usize, &self.h)?.deferred())
    }

    fn rest<'a>(&mut self, ch: &mut VChain<'a>, _sh: &Shape, _c: &Commit) -> Res<Vec<Deferred>> {
        let mut d: Vec<Deferred> = Vec::new();
        if self.sponge {
            d.extend(crate::sponge::verify(ch, &r3sponge::cont_rows())?.deferred());
        }
        if self.typed {
            let circ = r3typed::circuit();
            let (pt, y) = self.acc_in.split_at(self.acc_in.len() - 1);
            let out = crate::typed::verify_typed(ch, circ, &self.hdr_lanes, pt, y[0])?;
            require(out.acc_ok(circ), Reject::AccOut)?;
            d.extend(out.deferred());
        }
        if self.mb {
            let tabs = r3mb::export::tables_in_use(MB_SEED);
            d.extend(crate::minibus::verify(ch, &tabs)?);
        }
        Ok(d)
    }
}

/// `acc vk c p` with every part walked; for `parts = all`, also FORMAT6's 53 claims and `qS = 4,349` queries.
pub fn verify_full_file(sh: &Shape, vk: &Digest, c: &Digest, file: &[u8], key: Option<&[u8; 32]>, parts: &str) -> Res<Report> {
    let s = from_file(file).ok_or(Reject::File)?;
    for (i, (q, _)) in s.tr.iter().enumerate() {
        require(q.len() <= QUERY_CAP, Reject::QueryCap(i))?;
    }
    require(s.tr.len() <= sh.qv, Reject::TraceLen(s.tr.len()))?;
    require(sig_ok(vk, &trace_digest(&s.tr), &s.sig), Reject::Sig)?;
    require(s.pi.len() >= sh.hdr_len(), Reject::HdrLen)?;
    let mut stubs = FullStubs::new(&s.pi[..sh.hdr_len()], parts);
    let mut ask = TraceAsk::new(&s.tr, key);
    let rep = verify_pi(sh, vk, c, &s.pi, &mut ask, &mut stubs)?;
    ask.finish()?;
    if stubs.is_full() {
        require(rep.claims == FULL_CLAIMS && rep.queries == FULL_QS, Reject::FullShape)?;
    }
    Ok(rep)
}

/// Kind R on a full proof: `π'`'s trace re-derived from the keyed oracle by walking the full `V_S` on it (up to the
/// check that rejects), signed with the toy key `sign_seed`.
pub fn resign_full(sh: &Shape, vk: &Digest, c: &Digest, pi: &[u8], key: &[u8; 32], sign_seed: u8) -> Vec<u8> {
    let o = fs6::oracle::Local::keyed(key);
    let mut ask = crate::chain::RecordAsk { o: &o, tr: Vec::new() };
    if pi.len() >= sh.hdr_len() {
        let mut stubs = FullStubs::new(&pi[..sh.hdr_len()], "all");
        let _ = verify_pi(sh, vk, c, pi, &mut ask, &mut stubs);
    }
    let (_, sig) = crate::format::toy_sign(sign_seed, &trace_digest(&ask.tr));
    crate::format::to_file(&crate::format::Signed { pi: pi.to_vec(), tr: ask.tr, sig })
}

/// One item of the full schedule (`fs6::schedule::fixed_parts(P18, true)`) and where its bytes sit in `π`.
#[derive(Clone, Debug)]
pub struct ItemAt {
    pub part: String,
    pub index: usize,
    pub item: fs6::schedule::Item,
    /// Offset in `π` (after `HDR`) and length in bytes (0 for `D`, `B`).
    pub off: usize,
    pub len: usize,
}

/// Every item of the full schedule with its offset in `π`.
pub fn item_map(sh: &Shape) -> Vec<ItemAt> {
    use fs6::schedule::Item::*;
    let f = fs6::params::P18;
    let mut off = sh.hdr_len();
    let mut v = Vec::new();
    for (part, items) in fs6::schedule::fixed_parts(&f, true) {
        for (index, &item) in items.iter().enumerate() {
            let len = match item {
                E(k) => 16 * k,
                K(k) => 8 * k,
                Cap(i) => f.levels[i].cap_bytes(),
                G(_) => 8,
                D(_) | B => 0,
                Open(i) => f.levels[i].queries * f.levels[i].opening_bytes(),
            };
            v.push(ItemAt { part: part.clone(), index, item, off, len });
            off += len;
        }
    }
    v
}
