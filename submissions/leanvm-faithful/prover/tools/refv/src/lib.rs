//! `refv`: the lvm6 reference verifier (WP R1, a development oracle, never shipped).
//!
//! It checks a signed proof file exactly as the contract's `acc` does (`harness/FORMAT.md`): strict file parse,
//! `|q_i| ≤ 2^20`, `m ≤ qV`, `SigOk vk (traceDigest tr) σ`, then `V_S` with its `i`-th oracle query answered by the
//! `i`-th trace entry (`OProg.runSeq`: the query must be equal, every entry used). `V_S` follows
//! `docs/lvm6/design/FORMAT6.md` byte for byte; the arithmetic of each check is leanVM's `crates/verifier` at
//! `fdb317982` (`arith`), patched to the v6 transcript (`chain`).
//!
//! Coverage (see `docs/lvm6/stages/R1-refv.md`): §1 codec, §2 header and statement, §3–§4 the chain, §5 Merkle with
//! caps, §6.1, §6.5, §6.6, §8 the signed file. §6.2–§6.4 and §T are stubs ([`vs::Stubs`]) until they freeze.
//!
//! Reused, not forked: `fs6` (RT, prover side of FORMAT6) for the codec, the oracle, `Level`/`P18`, the Merkle node
//! query and the positions; the prover binary's `keccak.rs`/`format.rs` (statement hashes, file, `SigOk`) by path.

pub mod arith;
pub mod chain;
pub mod prover;
pub mod hdr;
pub mod merkle;
pub mod minibus;
pub mod shape;
pub mod sponge;
pub mod stack;
pub mod tree;
pub mod typed;
pub mod full;
pub mod vs;
pub mod whir;

/// The prover binary's contract hashes (`leafStmt`, `nodeStmt`, `Keyed`), included by path (not copied).
#[path = "../../../prover/src/keccak.rs"]
#[allow(dead_code)]
pub mod keccak;

/// What the included `format.rs` imports as `crate::oracle::Trace`.
pub mod oracle {
    pub type Trace = fs6::Trace;
}

/// The signed-proof file, `traceDigest`, `SigOk` and the toy signer, included by path (not copied).
#[path = "../../../prover/src/format.rs"]
#[allow(dead_code)]
pub mod format;

pub use fs6::Digest;
pub use verifier::{E, K};

/// Where the walk was when it rejected (and what the per-part counters are keyed by).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Part {
    /// The signed file and the header (before any query).
    File,
    /// `q₀` and the seed.
    Seed,
    /// §6.1.
    Commit,
    /// §6.2, the tree batch (frozen in FORMAT6 v2.1; its check is R2's `tree.rs`, through [`vs::Stubs::tree`]).
    Tree,
    /// §6.3–§6.4 (§T, stubs).
    Stub,
    /// §6.5.
    Batch,
    /// §6.6 level `i`.
    Level(usize),
    /// §6.6 the tail sumcheck after the final level's openings.
    Tail,
}

impl std::fmt::Display for Part {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Part::File => write!(f, "file"),
            Part::Seed => write!(f, "seed"),
            Part::Commit => write!(f, "6.1"),
            Part::Tree => write!(f, "6.2"),
            Part::Stub => write!(f, "6.3-6.4"),
            Part::Batch => write!(f, "6.5"),
            Part::Level(i) => write!(f, "6.6.L{i}"),
            Part::Tail => write!(f, "6.6.tail"),
        }
    }
}

/// Why `refv` rejected. Every variant is a rejection of the input, never a bug of `refv` (those panic).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reject {
    /// Not exactly one signed-proof encoding (`FORMAT.md` "Strict").
    File,
    /// Trace entry `i` has a query above `queryCap = 2^20`.
    QueryCap(usize),
    /// `m > qV`.
    TraceLen(usize),
    /// `SigOk vk (traceDigest tr) σ` fails.
    Sig,
    /// Dev check (only with an oracle key): trace entry `i`'s answer is not `Keccak-256(k ‖ q_i)`.
    NotOracle(usize),
    /// `π` shorter than `HDR`.
    HdrLen,
    /// Magic bytes.
    Magic,
    /// `b ∉ {0, 1}`.
    HdrB,
    /// `n ≠ N★`.
    HdrN,
    /// `b = 0` and `c' ≠ 0^32`.
    HdrCPrime,
    /// `HDR.vk` is not `V_S`'s `vk` (v2.2).
    HdrVk,
    /// `c ≠ leafStmtF h n` (`b = 0`) or `c ≠ nodeStmtF c' L` (`b = 1`).
    Statement,
    /// `BODY` ended inside an item.
    BodyShort(Part),
    /// Bytes left in `BODY` after the last item.
    BodyLeft(usize),
    /// `V_S` asked query `i` but the trace's entry `i` is another query (runSeq).
    TraceMismatch(usize, Part),
    /// `V_S` asked more queries than the trace has.
    TraceShort(Part),
    /// Trace entries left unused after `V_S` returned.
    TraceLeft(usize),
    /// A ground group's PoW lane has one of its top `g` bits set.
    Pow(Part),
    /// An opening's last node differs from its cap entry (level `i`).
    MerkleCap(usize),
    /// A final-level opening does not fold to the final polynomial at its point.
    FinalQuery,
    /// The terminal check of the opening.
    Terminal,
    /// More than `J₀` stacked claims.
    StackedClaims,
    /// A full proof (`refv::full`) without FORMAT6 §6.5's 53 claims or §7's `qS = 4,349` queries.
    FullShape,
    /// A check of §6.3 (sponge caller, core, link).
    Sponge(sponge::SpongeCheck),
    /// A check of §6.4a (typed phases).
    Typed(typed::TyCheck),
    /// A check of §6.4b (mini-bus).
    MiniBus(minibus::MbCheck),
    /// `V_S`'s last check (FORMAT6 §T): `Φ_Q(accOut.pt) ≠ accOut.y`.
    AccOut,
    /// A check of §6.2, the tree batch (R2, `tree.rs`).
    Tree(tree::TreeCheck),
}

impl std::fmt::Display for Reject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for Reject {}

pub type Res<T> = Result<T, Reject>;

pub(crate) fn require(ok: bool, r: Reject) -> Res<()> {
    if ok { Ok(()) } else { Err(r) }
}

/// FORMAT6 §1: an `E` scalar is `c₀ ‖ c₁`; `fs6` keeps it as `[c₀, c₁]`.
pub fn e_of(x: fs6::E) -> E {
    E::new(x[0], x[1])
}

pub fn fs_e(x: E) -> fs6::E {
    [x.c0, x.c1]
}

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

pub fn unhex32(s: &str) -> Option<Digest> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut d = [0u8; 32];
    for (i, o) in d.iter_mut().enumerate() {
        *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(d)
}
