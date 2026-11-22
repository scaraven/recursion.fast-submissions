//! The `S` proof (BLUEPRINT §2.1, §4, §11; the Lean `V_S` on lvm/VQ, `LvmDecide.decideProg`, phase by phase).
//! The recursion part (LoopIR tables, `C_rec`'s stream and `σ'`, KS rows `≥ 2^rec`) is WP-15b's: here it is
//! the `b = 0` convention (BLUEPRINT §4.5 Gate): an all-zero stream with honest computations on it, entering
//! through [`RecWitness`].

use std::time::Instant;

use crate::format::Sig;
use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::keccak_gkr::OutputClaim;
use crate::lv::pcs::stack_open::{MixedClaim, RingClaimAt, StackClaim, open_mixed_whir_stacked};
use crate::lv::pcs::whir::{INITIAL_FOLDING_FACTOR, commit, commit_even};
use crate::lv::pcs::whir_config::config_of_levels;
use crate::lv::primitives::field::{F64, F128, F192};
use crate::lvm::link::{self, Claim};
use crate::lvm::acc::{self, Acc};
use crate::lvm::params::{self, LANES, Level, Params, QClass, RING_STAGES, REC_STREAM_COLS, SIG_BYTES};
use crate::lvm::shape;
use crate::lvm::tables::{self, Chain, Layout, Sponge};
use crate::oracle::{Digest, Trace};

/// The statement part of the header.
#[derive(Clone, Debug)]
pub struct Header {
    pub b: u64,
    pub vk: Digest,
    pub c_l: Digest,
    pub s: Digest,
    pub n: u64,
    pub h: Digest,
    pub sig_leaf: Option<Sig>,
    /// The incoming accumulator (A23): `(0, Φ̃(0))` for an `S,0` proof, else the left child's `accOutOf`.
    pub acc_in: Acc,
}

impl Header {
    /// `'S' pad[7] | b | vk | c_L | s | n | h | σ_leaf | acc_in` (4,928 B + 24 (D + 1)); SLF (S2GS): no `σ_leaf`
    /// (`'S' pad[7] | b | vk | c_L | s | n | h | acc_in`, 152 B + 16 (D + 1) = 888 B at P20; `sig_leaf` is ignored).
    pub fn bytes(&self) -> Vec<u8> {
        let base = params::header_base();
        let mut v = Vec::with_capacity(base + 24 * (self.acc_in.pt.len() + 1));
        v.push(b'S');
        v.extend_from_slice(&[0u8; 7]);
        v.extend_from_slice(&self.b.to_le_bytes());
        v.extend_from_slice(&self.vk);
        v.extend_from_slice(&self.c_l);
        v.extend_from_slice(&self.s);
        v.extend_from_slice(&self.n.to_le_bytes());
        v.extend_from_slice(&self.h);
        if base == params::HEADER_BASE {
            match &self.sig_leaf {
                Some(sig) => crate::format::put_sig(&mut v, sig),
                None => v.extend_from_slice(&[0u8; SIG_BYTES]),
            }
        }
        assert_eq!(v.len(), base);
        v.extend_from_slice(&self.acc_in.bytes());
        v
    }
}

pub use crate::lvm::rec::RecWitness;

pub struct SProof {
    pub proof: Vec<u8>,
    pub trace: Trace,
    pub h: Digest,
    /// The outgoing accumulator (`accOutOf` of this proof's stream).
    pub acc_out: Acc,
    pub stages: Vec<(&'static str, f64)>,
    /// PI-GRIND: per WHIR level (`C_rec`'s, then `C_main`'s), the attempts up to its accepted nonce
    pub grind_attempts: Vec<u64>,
}

/// `Σ (8 + |q| + 32)` + 1: the hashed length of the trace digest, and its sponge blocks.
pub fn sponge_blocks(p: &Params) -> usize {
    let l: usize = 1 + params::query_list(p).iter().map(|(_, len)| 40 + len).sum::<usize>();
    l / 136 + 1
}

fn e(x: u64) -> F192 {
    F192::new(x, 0, 0)
}

fn bits_point(x: usize, n: usize) -> Vec<F192> {
    (0..n).map(|i| e(((x >> i) & 1) as u64)).collect()
}

fn mixed(c: Claim) -> MixedClaim {
    match c {
        Claim::Point { terms, value } => MixedClaim::Point { terms, value },
        Claim::Ring { offset, point, slices, map, scale, tail } => MixedClaim::Ring(RingClaimAt { offset, point, slices, map, scale, tail }),
        Claim::E2 { terms, value } => MixedClaim::E2 { terms: terms.into_iter().map(|t| (t.offset, t.point, t.phi, t.klin)).collect(), value },
    }
}

fn whir_config(levels: &[Level], grind: usize, ood: bool) -> crate::lv::pcs::whir::ProverConfig {
    config_of_levels(&levels.iter().map(|l| (l.fold, l.rate, l.cap, l.t)).collect::<Vec<_>>(), grind, ood)
}

/// Builds the recursion tables once the commitments' fixed contents are written (CH, KS, the stream, `σ'`)
/// and the header is complete (`h`): `(header, C_main, C_rec) ↦ tables` (WP-15c: the M3 section's tables,
/// whose aliased input arrays read the commitments and whose public array reads the header).
/// The second argument reads `len` words at offset `o` of `C_rec` (`true`) or `C_main` (`false`).
pub type Col<'a> = dyn Fn(bool, usize, usize) -> Vec<F64> + 'a;
/// TB (H-taint): the build starts before `h` is known; the header it gets has `h` unset, and the third argument
/// returns `h` (waiting for the walk's end).
pub type GetH<'a> = dyn Fn() -> Digest + 'a;
pub type Build<'a> = dyn Fn(&Header, &Col, &GetH) -> Vec<crate::lvm::m3::TableW> + Sync + 'a;
/// B1-IE: the B program's run on a header and the commitments (the typed backend's build: the inputs from `Col` and
/// the header lanes, the `BITS` fixpoint; no tables).
pub type RunB<'a> = dyn Fn(&Header, &Col, &GetH) -> crate::lvm::loopir::Run + Sync + 'a;

/// B1-IE (roll 8, B-DES §1): the typed backend's static data (`stream::Ctx`'s, built before `ready`): the B program,
/// its layout, the cells' words, the matrices (`Typed`, with the class kernels), the regions' targets, the mini-bus.
pub struct TypedB<'a> {
    pub c: &'a crate::lvm::loopir::Compiled,
    pub spec: &'a crate::lvm::loopir::M3Spec,
    pub lay: &'a crate::lvm::typed_lay::TLay,
    pub words: &'a crate::lvm::typed_lay::Words,
    pub b1: &'a crate::lvm::typed::Typed,
    pub td: &'a crate::lvm::typed_prove::TData,
    pub mb: &'a crate::lvm::typed_mb::MbSpec,
    /// R9-TY: the words' sources (the witness as a gather; `None`: the serial `witness_set`)
    pub ws: Option<&'a crate::lvm::typed_lay::WSrc>,
    pub run: &'a RunB<'a>,
}

/// What the build thread makes: the bus path's tables, or the typed path's run.
enum Built {
    Tables(Vec<crate::lvm::m3::TableW>),
    Run(crate::lvm::loopir::Run),
}

/// The build of a proof: the bus path's tables (`Build`), or the typed backend.
#[derive(Clone, Copy)]
pub enum Job<'a> {
    Bus(&'a Build<'a>),
    Typed(&'a TypedB<'a>),
}

/// P6B (OH-DES P1d): one proof's large buffers, allocated and filled before `ready` (untimed): `C_main` (zero, but
/// `D`'s rows all `z = Keccak-f(0)[0..4)`, every row `≥ n`'s value), `C_rec` (zero) and the chain's `y` (all `z`).
/// The walk then writes rows `< n` only. `prove` takes them when their sizes are its own, else allocates as before.
struct Bufs {
    cmain: Vec<F64>,
    y: Vec<[u64; 4]>,
}

/// CR-P (SH2-Z): `C_main` is prepared once per shape (`P20`: the big one and the small one, whose `C_main` is the
/// `2^23`-word logical table with `2^18` `D` rows a lane), since `n` is known only at `go`; `C_rec` and `y` are the
/// same in both. The other shape's `C_main` stays here unused (it is not freed in the step).
struct Prep {
    mains: Vec<((usize, usize, usize, usize, usize), Vec<F64>)>,
    /// `y` goes with the first match (R11, S2GM: there is no `C_rec` buffer).
    y: Vec<[u64; 4]>,
    y_taken: bool,
}

static BUFS: std::sync::Mutex<Option<Prep>> = std::sync::Mutex::new(None);

/// `Y`'s lanes 0–3 on a zero input row (`Keccak-f(0)`): `D` and `y` on rows `≥ n`.
fn z_lanes() -> [u64; 4] {
    let mut z = [0u64; LANES];
    crate::lv::primitives::hash::keccak_f(&mut z);
    [z[0], z[1], z[2], z[3]]
}

/// P6B: [`Bufs`] for the next proof at `p` (`LVM_PREBUF=0`: none).
pub fn prepare(p: &Params) {
    if std::env::var("LVM_PREBUF").is_ok_and(|v| v == "0") {
        return;
    }
    let z = z_lanes();
    let shapes: &[bool] = if Layout::is_small(p, 1) { &[false, true] } else { &[false] };
    let mains = shapes
        .iter()
        .map(|&small| {
            let lay = Layout::shape(p, small);
            let mut cmain = vec![F64::ZERO; 1 << lay.nu_main];
            for l in 0..4 {
                cmain[lay.d(l)..lay.d(l) + (1 << lay.d_log)].fill(F64(z[l]));
            }
            (buf_key(p, &lay), cmain)
        })
        .collect();
    let y = vec![z; 1 << p.log_n];
    *BUFS.lock().unwrap() = Some(Prep { mains, y, y_taken: false });
}

/// R9-TY: the chain walk of a `step`, started at `go` on its own thread (`start_walk`), before the child's parse,
/// `RecWitness::from_child` and the proof's set-up (≈ 5 ms on the walk's critical path); `prove_with` takes it when
/// `(s, n)` are the proof's. The walk is `walk_emit` on the prepared `y` as in `prove_with`; its rows go to the
/// tape witness through `runs`, `h` through `h`. The thread owns the vectors and returns them; the slices it sends
/// point into their heap buffers, which do not move while the thread runs or when the vectors are returned.
struct EarlyWalk {
    s: Digest,
    n: usize,
    h: std::sync::mpsc::Receiver<Digest>,
    runs: std::sync::mpsc::Receiver<(&'static [[u64; LANES]], &'static [[u64; 4]])>,
    join: std::sync::mpsc::Receiver<(Vec<[u64; LANES]>, Vec<[u64; 4]>)>,
}

static EARLY: std::sync::Mutex<Option<EarlyWalk>> = std::sync::Mutex::new(None);

/// Whether `prove_with` runs the pipelined walk (P6B): not the dense prover, not `LVM_CHAIN_REF`, not `LVM_P6B=0`.
fn pipelined() -> bool {
    !std::env::var("LVM_PGATE").is_ok_and(|m| m == "dense") && std::env::var_os("LVM_CHAIN_REF").is_none() && std::env::var("LVM_P6B").map_or(true, |v| v != "0")
}

/// R9-TY: start the walk of chain `(s, n)` now (`LVM_EARLY_WALK=0`: off; also off where `prove_with` would not
/// pipeline it, or `n` is out of range).
pub fn start_walk(p: &Params, s: Digest, n: usize) {
    if std::env::var("LVM_EARLY_WALK").is_ok_and(|v| v == "0") || !pipelined() || n == 0 || n > 1 << p.log_n {
        return;
    }
    let big = 1usize << p.log_n;
    // the prepared `y` (rows ≥ n already `z`), else a fresh one whose rows ≥ n the thread sets
    let pre_y = BUFS.lock().unwrap().as_mut().map(|b| std::mem::take(&mut b.y)).filter(|y| y.len() == big);
    let (tx, h) = std::sync::mpsc::channel();
    let (ctx, runs) = std::sync::mpsc::channel();
    let (rtx, join) = std::sync::mpsc::channel();
    let job = move || {
        let y_ready = pre_y.is_some();
        // SAFETY: the walk writes every input row and the `y` rows `< n`; rows `≥ n` of a fresh `y` are set below.
        let mut w_in: Vec<[u64; LANES]> = unsafe { crate::lv::primitives::uninit_vec(n) };
        let mut w_y: Vec<[u64; 4]> = pre_y.unwrap_or_else(|| unsafe { crate::lv::primitives::uninit_vec(big) });
        {
            // SAFETY: the buffers live until the vectors are dropped, after the receiver's last use (`prove_with`
            // joins this thread and keeps the vectors in its `Chain`); nothing else touches them meanwhile.
            let w_in_r: &'static mut [[u64; LANES]] = unsafe { std::slice::from_raw_parts_mut(w_in.as_mut_ptr(), n) };
            let w_y_r: &'static mut [[u64; 4]] = unsafe { std::slice::from_raw_parts_mut(w_y.as_mut_ptr(), big) };
            let (head, tail) = w_y_r.split_at_mut(n);
            let at_end = move |h: [u64; 4]| {
                let _ = tx.send(tables::lanes_digest(&h));
            };
            crate::chainwalk::walk_emit(crate::chainwalk::select(), tables::digest_lanes(&s), w_in_r, head, at_end, move |a, b| {
                let _ = ctx.send((a, b));
            });
            if !y_ready {
                tail.fill(z_lanes());
            }
        }
        let _ = rtx.send((w_in, w_y));
    };
    drop(std::thread::spawn(job));
    *EARLY.lock().unwrap() = Some(EarlyWalk { s, n, h, runs, join });
}

/// The early walk of `(s, n)`, if one was started.
fn take_early(s: &Digest, n: usize) -> Option<EarlyWalk> {
    // (one not this proof's is dropped: its thread ends on its own, its vectors with the last receiver)
    EARLY.lock().unwrap().take().filter(|e| e.s == *s && e.n == n)
}

/// R9-TY: drop the prepared buffers no proof took (the other shape's `C_main`), back to the allocator's cache.
pub fn drop_prepared() {
    *BUFS.lock().unwrap() = None;
}

/// What the prepared buffers' contents depend on: the sizes and `D`'s offset and rows.
fn buf_key(p: &Params, lay: &Layout) -> (usize, usize, usize, usize, usize) {
    (lay.nu_main, lay.s_off, p.log_n, lay.d_off, lay.d_log)
}

/// The prepared buffers, if they are this proof's (once: `y` goes with the first match).
fn take_bufs(p: &Params, lay: &Layout) -> Option<Bufs> {
    let mut g = BUFS.lock().unwrap();
    let prep = g.as_mut()?;
    let i = prep.mains.iter().position(|(k, _)| *k == buf_key(p, lay))?;
    if prep.y_taken {
        return None;
    }
    prep.y_taken = true;
    let cmain = prep.mains.swap_remove(i).1;
    Some(Bufs { cmain, y: std::mem::take(&mut prep.y) })
}

/// P6B (OH-DES P1c): [`crate::lv::keccak_gkr::Witness::generate_uncommitted`] on the chain's `n` input rows, run as
/// the walk hands them over (`rx`, in order, in runs of `chainwalk::CHUNK` rows): the same blocks into the same
/// extent, and the same padding block. Every run's `y` rows also go into `D`'s rows (`d`, lane `l` at
/// `l·2^d_log`: `log_n`, or 18 in the small shape, where `n ≤ 2^18`); with `d_rest`, `D`'s rows `n … 2^d_log − 1` are
/// set to `z` at the end.
fn tape_witness_behind<'a>(
    log_n: usize,
    d_log: usize,
    n: usize,
    rx: std::sync::mpsc::Receiver<(&'a [[u64; LANES]], &'a [[u64; 4]])>,
    d: &mut [F64],
    d_rest: bool,
) -> crate::lv::keccak_gkr::Witness {
    use crate::lv::keccak_gkr::witness::BLOCK;
    const _: () = assert!(crate::chainwalk::CHUNK % BLOCK == 0);
    let big = 1usize << log_n;
    let shape = crate::lv::keccak_gkr::Shape::new(big, crate::lvm::params::TAPE_DEPTH);
    let written = n.div_ceil(BLOCK);
    let (mut extent, padding) = tape_ext::extents(shape, written);
    let mut slots = tape_ext::slots(&mut extent, written);
    let mut runs: Vec<&[[u64; LANES]]> = Vec::new();
    let (mut rows, mut next) = (0usize, 0usize);
    loop {
        let first = rx.recv();
        let end = first.is_err();
        for (ci, cy) in first.into_iter().chain(std::iter::from_fn(|| rx.try_recv().ok())) {
            for l in 0..4 {
                for (dst, v) in d[(l << d_log) + rows..][..cy.len()].iter_mut().zip(cy) {
                    *dst = F64(v[l]);
                }
            }
            rows += ci.len();
            runs.push(ci);
        }
        let ready = if end { written } else { rows / BLOCK };
        if ready > next {
            let (runs, base) = (&runs, next);
            tape_ext::run(shape.depth(), &mut slots[base..ready], |i| {
                let g = base + i;
                let (r, at) = (g * BLOCK / crate::chainwalk::CHUNK, g * BLOCK % crate::chainwalk::CHUNK);
                &runs[r][at..(at + BLOCK).min(runs[r].len())]
            });
            next = ready;
        }
        if end {
            break;
        }
    }
    assert_eq!(rows, n, "the walk hands over its n rows");
    if d_rest {
        let z = z_lanes();
        for l in 0..4 {
            d[(l << d_log) + n..(l + 1) << d_log].fill(F64(z[l]));
        }
    }
    drop(slots);
    // SAFETY: blocks `0 .. written` were run into `extent` above (each slot once), and the padding block into its
    // own by `tape_ext::extents`.
    unsafe { tape_ext::finish(shape, extent, written, padding) }
}

/// P6B-V4: the tier's `Extent` API as [`tape_witness_behind`] uses it. v2/v4p run leanVM 0b850750's
/// `keccak_gkr/` (`Extent::new(first, blocks)`, `slot(g)`, an `unsafe` [`block`] taking a `Copy` slot); v4 runs
/// PORT-13's `keccak_gkr_v4/` (`Extent::new(first, blocks, depth)`, `slots()` borrowing the extent, a safe
/// `block` taking `&mut Slot`). Both copies' `generate_uncommitted` run the same blocks the same way.
///
/// [`block`]: crate::lv::keccak_gkr::witness::block
// lvm2 W32-P: every tier mounts `keccak_gkr_v4/` (lv/mod.rs), so its `Extent` API serves all.
mod tape_ext {
    use crate::lv::keccak_gkr::witness::{Extent, Slot, block};
    use crate::lv::keccak_gkr::{Shape, Witness};
    use crate::lvm::params::LANES;

    /// The extent of blocks `0 .. written`, none run, and the padding block's extent, run (if blocks follow), as
    /// `keccak_gkr_v4`'s `padding` builds it.
    pub fn extents(shape: Shape, written: usize) -> (Extent, Option<Extent>) {
        let padding = (written < shape.n_blocks()).then(|| {
            let mut e = Extent::new(written, 1, shape.depth());
            block(shape.depth(), &[], e.slots().first_mut(), |_, _, _| {});
            e
        });
        (Extent::new(0, written, shape.depth()), padding)
    }

    /// The slots of `e`'s blocks (`0 .. written`), in order.
    pub fn slots(e: &mut Extent, written: usize) -> Vec<Slot<'_>> {
        let s = e.slots();
        assert_eq!(s.len(), written);
        s
    }

    /// Run `slots[i]`'s block on `inputs(i)`, on the pool, as `generate_uncommitted` does.
    pub fn run<'a>(depth: usize, slots: &mut [Slot<'_>], inputs: impl Fn(usize) -> &'a [[u64; LANES]] + Sync) {
        crate::lv::parallel::chunks_mut(slots, 1, |i, slot| block(depth, inputs(i), slot.first_mut(), |_, _, _| {}));
    }

    /// # Safety
    /// None beyond the v2 tier's signature: `from_extents` checks every block's `written` flag here.
    pub unsafe fn finish(shape: Shape, extent: Extent, written: usize, padding: Option<Extent>) -> Witness {
        Witness::from_extents(shape, vec![extent], written, padding)
    }
}

/// `v` cut at the disjoint ranges `a` and `b`: `(v[a], v[b], the three other pieces with their offsets)`.
fn split2<T>(v: &mut [T], a: (usize, usize), b: (usize, usize)) -> (&mut [T], &mut [T], [(usize, &[T]); 3]) {
    let swap = b.0 < a.0;
    let (x, y) = if swap { (b, a) } else { (a, b) };
    assert!(x.0 <= x.1 && x.1 <= y.0 && y.0 <= y.1 && y.1 <= v.len(), "two disjoint ranges");
    let (c0, r) = v.split_at_mut(x.0);
    let (h0, r) = r.split_at_mut(x.1 - x.0);
    let (c1, r) = r.split_at_mut(y.0 - x.1);
    let (h1, c2) = r.split_at_mut(y.1 - y.0);
    let cold = [(0, &*c0), (x.1, &*c1), (y.1, &*c2)];
    if swap { (h1, h0, cold) } else { (h0, h1, cold) }
}

/// R11 (M′, S2GM): the tables' pre-placements on the old `C_rec` (`(true, w)`: the stream block's word `w`) as
/// `C_main` words at the big layout's offsets (`S + w`), before [`shape::localize`]; afterwards no table names a
/// second commitment.
pub fn rec_to_main(p: &Params, tables: &mut [crate::lvm::m3::TableW]) {
    let big = Layout::new(p);
    for t in tables {
        for x in t.pre.iter_mut().filter(|x| x.1) {
            *x = (x.0, false, big.rec_word(x.2), x.3);
        }
    }
}

/// The tables' columns into `C_main`: placed ones, and pre-placed written ones where they are pre-placed; a
/// pre-placed column that is not written is checked against the commitment. P6B (OH-DES P1d): on the pool, the writes
/// first, then the checks. That is the serial order's result when the written ranges are disjoint and no checked range
/// meets one; otherwise (or `LVM_P6B=0`) the serial loop runs. (R11, S2GM: one commitment; [`rec_to_main`] first.)
fn place_columns(tables: &[crate::lvm::m3::TableW], place: &[Vec<Option<usize>>], cmain: &mut [F64]) {
    let mut writes: Vec<(usize, &[F64])> = Vec::new();
    let mut checks: Vec<(usize, &[F64])> = Vec::new();
    for (tw, pl) in tables.iter().zip(place) {
        for (c, (col, o)) in tw.cols.iter().zip(pl).enumerate() {
            if let Some(o) = o {
                writes.push((*o, col));
            }
            if let Some((r, o)) = tw.pre_of(c) {
                assert!(!r, "S2GM: no column is pre-placed in C_rec (rec_to_main)");
                if tw.pre_writes(c) { writes.push((o, col)) } else { checks.push((o, col)) }
            }
        }
    }
    let mut w: Vec<(usize, usize)> = writes.iter().map(|&(o, c)| (o, o + c.len())).collect();
    w.sort_unstable();
    let disjoint = w.windows(2).all(|x| x[0].1 <= x[1].0);
    let met = checks.iter().any(|&(o, c)| w.iter().any(|&(a, b)| o < b && a < o + c.len()));
    let fits = w.iter().all(|&(_, e)| e <= cmain.len());
    if !disjoint || met || !fits || std::env::var("LVM_P6B").is_ok_and(|v| v == "0") {
        for (tw, pl) in tables.iter().zip(place) {
            for (c, (col, o)) in tw.cols.iter().zip(pl).enumerate() {
                if let Some(o) = o {
                    cmain[*o..*o + col.len()].copy_from_slice(col);
                }
                if let Some((_, o)) = tw.pre_of(c) {
                    let dst = &mut cmain[o..o + col.len()];
                    if tw.pre_writes(c) {
                        dst.copy_from_slice(col);
                    } else {
                        assert!(dst == &col[..], "a pre-placed column holds the table's values");
                    }
                }
            }
        }
        return;
    }
    const PIECE: usize = 1 << 15;
    let jobs: Vec<(usize, &[F64])> = writes.iter().flat_map(|&(o, c)| c.chunks(PIECE).enumerate().map(move |(i, part)| (o + i * PIECE, part))).collect();
    let pm = crate::lv::parallel::SendPtr(cmain.as_mut_ptr());
    crate::lv::parallel::for_each(jobs.len(), |i| {
        let (o, src) = jobs[i];
        let dst = pm;
        // SAFETY: every written range lies in `C_main` (`fits`) and no two meet (`disjoint`), so each job writes words
        // no other job touches.
        unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), dst.0.add(o), src.len()) };
    });
    let cm = &*cmain;
    crate::lv::parallel::for_each(checks.len(), |i| {
        let (o, col) = checks[i];
        assert!(&cm[o..o + col.len()] == col, "a pre-placed column holds the table's values");
    });
}

/// R11 (M′, S2GM): the stack `C_main` is opened on: its committed lanes, zero-padded to cover every claim (the
/// relayout's point claim weighs the whole stream block `S`, whose last lanes may be absent under Z2). Buffer
/// (logical) words; the small shape's physical stack is twice as long.
fn open_len(lay: &Layout, main_words: usize) -> usize {
    main_words.max(lay.s_off + (1usize << lay.nu_rec))
}

/// Prove the `S` statement of `hd` (with `hd.h` filled in here) at parameter set `p` on the installed oracle.
/// The recursion tables are `rec.tables`, or `build`'s (then `p` must already carry their M3 numbers).
pub fn prove(p: &Params, hd: Header, rec: RecWitness, build: Option<&Build>) -> SProof {
    prove_with(p, hd, rec, build.map(Job::Bus))
}

/// [`prove`] with the build `job`: the bus path's tables, or (B1-IE) the typed backend's run ([`typed_tail`]).
pub fn prove_with(p: &Params, mut hd: Header, mut rec: RecWitness, job: Option<Job>) -> SProof {
    let build = match job {
        Some(Job::Bus(b)) => Some(b),
        _ => None,
    };
    let typed = match job {
        Some(Job::Typed(t)) => Some(t),
        _ => None,
    };
    rec.tables.retain(crate::lvm::m3::active);
    // with recursion tables, the schedule's bus and table numbers are theirs (the program `Q` fixes them;
    // the record `P20`/`P8` carries them once `Q` is final)
    let p_rec;
    let p = if rec.tables.is_empty() {
        p
    } else {
        let (d, l, r, e) = crate::lvm::m3::shape(&rec.tables);
        p_rec = Params { bus_depth: d, leafdec_reads: l, table_rounds: r, table_evals: e, ..p.clone() };
        &p_rec
    };
    // SH2-Z (roll 7): the shape by `n`, `P20`'s small one for `n ≤ 2^18` (`lvm::shape`); B1-IE tamper
    // `LVM_TYPED_TAMPER=shape` (dev): a small statement proved in the big shape (V_S must reject)
    let lay = if typed.is_some() && std::env::var("LVM_TYPED_TAMPER").is_ok_and(|v| v == "shape") && Layout::is_small(p, hd.n as usize) {
        eprintln!("lvm: LVM_TYPED_TAMPER=shape: n = {} proved in the big shape", hd.n);
        Layout::shape(p, false)
    } else {
        Layout::of_step(p, hd.n as usize)
    };
    let mut stages = Vec::new();
    let mut t = Instant::now();
    let prof = crate::lv::tracing::enabled();
    let mut c0 = if prof { crate::lv::tracing::cpu_now() } else { (0.0, 0.0) };
    let mut lap = |name: &'static str, stages: &mut Vec<(&'static str, f64)>| {
        let s = t.elapsed().as_secs_f64();
        crate::lv::tracing::record(name, s);
        if prof {
            let c = crate::lv::tracing::cpu_now();
            eprintln!("  PCPU {name:<14} wall {s:.3} cpu {:.3} svc {:.2}", c.0 - c0.0, c.1 - c0.1);
            c0 = c;
        }
        crate::alloc::memlog(name);
        stages.push((name, s));
        t = Instant::now();
    };
    assert_eq!(hd.acc_in.pt.len(), p.acc_d(), "acc_in has D coordinates");
    let n = hd.n as usize;
    assert!(n >= 1 && n <= 1 << p.log_n, "1 ≤ n ≤ 2^log_n (A1)");
    // S1 (BLUEPRINT2 §2.1): rows ≥ n hold the zero input and the CH link is gated by `[k ≤ m]`. The prover runs the
    // written prefix with leanVM's padding block and sums the padding in closed form; `LVM_PGATE=dense` runs and sums
    // every row instead, the byte-identity oracle (the same proof bytes).
    let dense = std::env::var("LVM_PGATE").is_ok_and(|m| m == "dense");

    // ---- witness: CH, KS, C_main, C_rec
    // the two sequential Keccak walks, side by side
    let cont = tables::cont_column(p.ks_log, p.rec_rows_log, sponge_blocks(p));
    if let Ok(path) = std::env::var("LVM_REC_DUMP") {
        std::fs::write(&path, rec.dump()).expect("LVM_REC_DUMP");
    }
    // P-QUICK lever 3 (prover-only: the same columns and tables, computed in another order): the serial chain
    // walk runs on its own thread; meanwhile this thread runs the sponge walk, allocates the commitments and
    // writes KS's lanes, σ' and the stream. The recursion tables need `h = chainEnd s n` (the header) and read C_rec
    // and C_main outside the `D` block: they are built on a third thread once the walk is done, beside the tape's
    // GKR witness (which commits nothing). P-FIX: KS's GKR witness is generated on a fourth thread beside the walk,
    // into the KS slots `[ks_off, ks_off + 50·2^ks_log)`, so that the build starts as soon as `h` is known. A read that would touch `D` or those slots is not served there:
    // the build is then redone after both are written (the old order).
    // P6B (OH-DES P1c, P1d): the buffers come from before `ready` when they were prepared ([`prepare`]); the walk
    // hands its rows over as it goes, and a fifth thread runs the tape's GKR witness on them and writes `D`
    // ([`tape_witness_behind`]). `LVM_P6B=0`, the dense prover and `LVM_CHAIN_REF` keep the walk-then-witness order.
    let (d_lo, d_hi) = (lay.d_off, lay.d_off + (1usize << lay.d_vars()));
    // U-TAPE (S2GU): no KS block and no KS GKR witness; the sponge half's tape witness commits nothing (an empty range
    // after D)
    let utape = FrontCfg::get().utape;
    let (k_lo, k_hi) = if utape { (d_hi, d_hi) } else { (lay.ks_off, lay.ks_off + (50usize << lay.ks_log)) };
    let rec_msg = std::mem::take(&mut rec.msg);
    let t0w = Instant::now();
    let tl = std::env::var_os("LVM_LOG").is_some();
    let big = 1usize << p.log_n;
    let pipe = !dense && pipelined();
    // R9-TY: the walk started at `go` (`start_walk`), when it is this proof's
    let early = if pipe { take_early(&hd.s, n) } else { None };
    let (pre_c, pre_y) = match take_bufs(p, &lay) {
        // (an early walk took the prepared `y`; when it was not this proof's, `y` is fresh)
        Some(b) => (Some(b.cmain), Some(b.y).filter(|y| early.is_none() && y.len() == big)),
        None => (None, None),
    };
    let d_ready = pre_c.is_some();
    let y_ready = pre_y.is_some();
    // the pipelined walk's rows: `n` inputs, `2^log_n` outputs (rows `≥ n`: `z`, prepared or set by the walk thread)
    // SAFETY: the walk writes every input row and the `y` rows `< n`; rows `≥ n` of an unprepared `y` are set below.
    let (mut w_in, mut w_y): (Vec<[u64; LANES]>, Vec<[u64; 4]>) = match (pipe && early.is_none(), pre_y) {
        (true, Some(y)) => (unsafe { crate::lv::primitives::uninit_vec(n) }, y),
        (true, None) => unsafe { (crate::lv::primitives::uninit_vec(n), crate::lv::primitives::uninit_vec(big)) },
        (false, _) => (Vec::new(), Vec::new()),
    };
    let (w_in_r, w_y_r) = (&mut w_in[..], &mut w_y[..]);
    let mut early_vecs = None;
    let early_vecs_r = &mut early_vecs;
    let (chain_old, ks, mut cmain, tape_w, ks_w, built, h) = std::thread::scope(|sc| {
        let (tx, rx) = std::sync::mpsc::channel();
        let (ctx, crx) = std::sync::mpsc::channel();
        let (rx, crx, early_join) = match early {
            // SAFETY: the same type up to the slices' lifetime: they point into the early walk's vectors, which are
            // kept (`early_vecs`) until after this scope.
            Some(e) => (e.h, unsafe { std::mem::transmute::<std::sync::mpsc::Receiver<(&'static [[u64; LANES]], &'static [[u64; 4]])>, std::sync::mpsc::Receiver<_>>(e.runs) }, Some(e.join)),
            None => (rx, crx, None),
        };
        let s = hd.s;
        let walk = early_join.is_none().then(|| sc.spawn(move || {
            if !pipe {
                return Some(Chain::run_gated_notify(p.log_n, &s, n, dense, move |h| tx.send(h).expect("the end of the chain")));
            }
            let (head, tail) = w_y_r.split_at_mut(n);
            let at_end = move |h: [u64; 4]| tx.send(tables::lanes_digest(&h)).expect("the end of the chain");
            crate::chainwalk::walk_emit(crate::chainwalk::select(), tables::digest_lanes(&s), w_in_r, head, at_end, move |a, b| {
                let _ = ctx.send((a, b));
            });
            if !y_ready {
                tail.fill(z_lanes());
            }
            None
        }));
        let ks = Sponge::run(p.ks_log, cont, rec_msg);
        let t_s = t0w.elapsed().as_secs_f64();
        let mut cmain = pre_c.unwrap_or_else(|| vec![F64::ZERO; 1 << lay.nu_main]);
        let t_a = t0w.elapsed().as_secs_f64();
        // R11 (S2GM): the 17 message lanes and σ' are the stream block S of C_main (the old C_rec's content)
        tables::write_ks_lanes(&lay, &ks, &mut cmain);
        let sig_at = lay.rec_col(REC_STREAM_COLS);
        for (i, &w) in rec.sigma.iter().enumerate() {
            cmain[sig_at + i] = F64(w);
        }
        let (chain, ks_w, tape_w, built, h) = std::thread::scope(|si| {
            let (dblk, kblk, cold) = split2(&mut cmain, (d_lo, d_hi), (k_lo, k_hi));
            let (ks_r, lay_r) = (&ks, &lay);
            let s_big = Layout::new(p).s_off;
            let d_log = lay.d_log;
            // KS's GKR witness beside the walk, into its slots (U-TAPE: the tape's sponge half, KS13's written prefix in a
            // half of `2^log_n` instances, committing nothing; none for the dense oracle, which runs one batch)
            let ksj = si.spawn(move || {
                let w = if utape {
                    (!dense).then(|| {
                        let half = crate::lv::keccak_gkr::Shape::new(1 << p.log_n, crate::lvm::params::TAPE_DEPTH);
                        let mut w = crate::lv::keccak_gkr::Witness::generate_uncommitted(half, &ks_r.inputs[..ks_r.written()]);
                        // (the dead rows B..ks_split: whole blocks of zero inputs, run as the padding block)
                        w.mark_holes(&ks_r.inputs[..ks_r.written()]);
                        w
                    })
                } else {
                    Some(crate::lv::keccak_gkr::Witness::generate(ks_r.shape, &ks_r.inputs, kblk))
                };
                (w, t0w.elapsed().as_secs_f64())
            });
            // P6B: the tape's GKR witness and `D` behind the walk
            let tj = pipe.then(|| {
                si.spawn(move || {
                    let w = tape_witness_behind(p.log_n, d_log, n, crx, dblk, !d_ready);
                    (w, t0w.elapsed().as_secs_f64())
                })
            });
            // TB (H-taint): the build starts now, beside the walk; it gets `h` through `hrx` when the walk ends
            let (htx, hrx) = std::sync::mpsc::channel::<Digest>();
            let hd_b = hd.clone();
            let tabs = job.map(|j| {
                si.spawn(move || {
                    let hit = std::cell::Cell::new(false);
                    let col = |r: bool, o: usize, len: usize| -> Vec<F64> {
                        // SH2-Z: a C_main read is at the big layout's offsets (D's rows ≥ 2^18: after the walk);
                        // R11 (S2GM): an old C_rec word `o` is S's (`S + o`, big offsets)
                        let o = if r { s_big + o } else { o };
                        let Some(o) = shape::buf_range(lay_r, o, len) else {
                            hit.set(true);
                            return vec![F64::ZERO; len];
                        };
                        let e = o + len;
                        if (o < d_hi && e > d_lo) || (o < k_hi && e > k_lo) {
                            hit.set(true);
                            vec![F64::ZERO; len]
                        } else {
                            // outside both, the range lies in one of the other pieces
                            let &(at, c) = cold.iter().find(|(at, c)| *at <= o && e <= at + c.len()).expect("a C_main range");
                            c[o - at..e - at].to_vec()
                        }
                    };
                    let hv = std::cell::OnceCell::new();
                    let get_h = || *hv.get_or_init(|| hrx.recv().expect("h, from the walk"));
                    let t = match j {
                        Job::Bus(b) => Built::Tables(b(&hd_b, &col, &get_h)),
                        Job::Typed(tb) => Built::Run((tb.run)(&hd_b, &col, &get_h)),
                    };
                    let t_b = t0w.elapsed().as_secs_f64();
                    (!hit.get()).then_some((t, t_b))
                })
            });
            let h = rx.recv().expect("the walk reaches row n − 1");
            let t_h = t0w.elapsed().as_secs_f64();
            let _ = htx.send(h);
            let chain = match (walk, early_join) {
                (Some(w), _) => w.join().expect("the chain walk"),
                (None, Some(j)) => {
                    *early_vecs_r = Some(j.recv().expect("the early chain walk"));
                    None
                }
                (None, None) => unreachable!(),
            };
            let t_w = t0w.elapsed().as_secs_f64();
            let (tape_w, t_g) = match (tj, &chain) {
                (Some(tj), _) => tj.join().expect("the tape witness"),
                (None, Some(c)) => (crate::lv::keccak_gkr::Witness::generate_uncommitted(c.shape, &c.inputs), t0w.elapsed().as_secs_f64()),
                (None, None) => unreachable!(),
            };
            let (ks_w, t_k) = ksj.join().expect("KS's GKR witness");
            let built = tabs.map(|t| t.join().expect("the recursion tables"));
            if tl {
                let t_b = built.as_ref().and_then(|b| b.as_ref().map(|x| x.1));
                eprintln!(
                    "lvm: witness timeline n={n}: sponge {t_s:.3}, alloc {t_a:.3}, h at {t_h:.3}, KS witness {t_k:.3}, walk {t_w:.3}, tape witness {t_g:.3}, tables {t_b:?} s"
                );
            }
            (chain, ks_w, tape_w, built.map(|b| b.map(|x| x.0)), h)
        });
        if let Some(chain) = &chain {
            tables::write_d(&lay, chain, &mut cmain);
        }
        (chain, ks, cmain, tape_w, ks_w, built, h)
    });
    if let Some((i, y)) = early_vecs {
        (w_in, w_y) = (i, y);
    }
    let chain = chain_old.unwrap_or_else(|| Chain { shape: crate::lv::keccak_gkr::Shape::new(big, crate::lvm::params::TAPE_DEPTH), inputs: w_in, y: w_y });
    hd.h = chain.end(n);
    assert_eq!(hd.h, h, "chainEnd s n");
    lap("chain+sponge", &mut stages);
    crate::lvm::stream::since_go("go to cs");
    if let Some(tb) = typed {
        let run = match built.flatten() {
            Some(Built::Run(r)) => r,
            _ => (tb.run)(&hd, &|r: bool, o: usize, len: usize| shape::read_big(&lay, &cmain, if r { Layout::new(p).rec_word(o) } else { o }, len), &|| hd.h),
        };
        return typed_tail(p, hd, &lay, tb, run, chain, ks, cmain, tape_w, ks_w, stages, dense);
    }
    assert!(!utape, "S2GU runs the typed path only (the bus path is S2GT's and older stages')");
    let ks_w = ks_w.expect("the KS GKR witness");
    if let Some(b) = build {
        rec.tables = match built.flatten() {
            Some(Built::Tables(t)) => t,
            _ => b(&hd, &|r: bool, o: usize, len: usize| shape::read_big(&lay, &cmain, if r { Layout::new(p).rec_word(o) } else { o }, len), &|| hd.h),
        };
        rec.tables.retain(crate::lvm::m3::active);
        let sh = crate::lvm::m3::shape(&rec.tables);
        assert_eq!(sh, (p.bus_depth, p.leafdec_reads, p.table_rounds, p.table_evals), "the tables' M3 numbers are the record's");
    }
    rec_to_main(p, &mut rec.tables);
    shape::localize(&lay, &mut rec.tables);
    let rec_place = crate::lvm::m3::place(&rec.tables, lay.free_lo(), lay.nu_main);
    if lay.small {
        // SH2-Z: the tables the prover places sit where the big layout's placement puts them, less 3·2^20
        let big = crate::lvm::m3::place(&rec.tables, Layout::new(p).free_lo(), p.nu_main);
        assert!(big.iter().flatten().zip(rec_place.iter().flatten()).all(|(b, s)| *b == s.map(|s| s + tables::SMALL_SHIFT)));
    }
    // Z2: a stack's root leaves carry its occupied lanes alone (the record's level-0 row, `params::occ_lanes`): the
    // lanes past them hold no data, so they are not encoded, hashed or sent, and the verifier reads them as zero.
    // `C_main`'s count covers both shapes (a small step's logical lane of 2^(ν − 7) words is one physical lane: its
    // even words).
    let occ_main = params::occ_lanes(&p.main_levels);
    let main_lane_log = lay.nu_main - INITIAL_FOLDING_FACTOR;
    let main_occ_words = occ_main << main_lane_log;
    // written placements (the prover's or the M3 section's) lie above the fixed blocks, below the stack's occupied
    // lanes, and do not overlap (R11, S2GM: one commitment)
    let mut spans: Vec<(bool, usize, usize)> = Vec::new();
    for (tw, pl) in rec.tables.iter().zip(&rec_place) {
        for c in tw.committed() {
            let w = match (pl[c], tw.pre_of(c)) {
                (Some(o), _) => Some((false, o)),
                (None, Some(x)) if tw.pre_writes(c) => Some(x),
                _ => None,
            };
            if let Some((r, o)) = w {
                assert!(!r, "S2GM: no C_rec placement");
                let (lo, hi) = (lay.free_lo(), main_occ_words);
                assert!(
                    lo <= o && o + (1 << tw.tau) <= hi,
                    "a written table column stays in the free region, below its stack's occupied lanes"
                );
                spans.push((r, o, o + (1 << tw.tau)));
            }
        }
    }
    spans.sort();
    assert!(spans.windows(2).all(|w| w[0].0 != w[1].0 || w[0].2 <= w[1].1), "written table columns do not overlap");
    place_columns(&rec.tables, &rec_place, &mut cmain);
    lap("witness", &mut stages);

    // ---- commit
    let header = hd.bytes();
    let mut ps = ProverState::seeded(&header);
    // Z2: `C_main` is committed on the lanes its words reach (a big step's tables end lanes below a small step's, so
    // its encode runs fewer lanes; every leaf still carries `occ_main` words, the absent ones zero); it is opened on
    // the zero-padded stack ([`open_len`]).
    // (`spans` holds the written columns; a pre-placed `C_main` column the tables only read counts too.)
    let pre_main = rec.tables.iter().flat_map(|tw| {
        tw.committed().filter_map(move |c| match tw.pre_of(c) { Some((false, o)) => Some(o + (1 << tw.tau)), _ => None })
    });
    let main_end = spans.iter().filter(|s| !s.0).map(|s| s.2).chain(pre_main).max().unwrap_or(0).max(lay.free_lo());
    let main_words = main_end.div_ceil(1 << main_lane_log) << main_lane_log;
    assert!(main_words <= main_occ_words, "C_main's words lie in its {occ_main} occupied lanes");
    #[cfg(feature = "selfcheck")]
    {
        assert!(cmain[main_words..].iter().all(|w| *w == F64::ZERO), "C_main past its committed lanes is zero");
    }
    let (cm, main_data, sh2_dense) = commit_main(p, &lay, &cmain, main_words);
    ps.add_cap(&cm.cap);
    lap("commit", &mut stages);

    // ---- bus, tables: the real ones over the recursion tables, else WP-15a's null instance
    let mut main_claims: Vec<Claim> = Vec::new();
    let (table_point, v_fix) = if rec.tables.is_empty() {
        crate::lvm::bus::prove_null_bus(&mut ps, p);
        (crate::lvm::bus::prove_null_tables(&mut ps, p), Vec::new())
    } else {
        let mo = crate::lvm::m3::prove(&mut ps, &rec.tables);
        // the tables' column claims (V_S: `bus.claims ++ m.tableClaims evals ++ …`): committed columns only
        for ((cl, tw), pl) in mo.claims.iter().zip(&rec.tables).zip(&rec_place) {
            for c in tw.committed() {
                match tw.pre_of(c) {
                    Some((_, o)) => main_claims.push(Claim::point(o, cl.chi.clone(), cl.evals[c])),
                    None => main_claims.push(Claim::point(pl[c].unwrap(), cl.chi.clone(), cl.evals[c])),
                }
            }
        }
        let point = mo.claims.iter().map(|c| &c.chi).max_by_key(|c| c.len()).cloned().unwrap_or_default();
        let evals: Vec<F192> = mo.claims.iter().flat_map(|c| c.evals.iter().copied()).collect();
        (point, acc::fix_index(&rec.tables, p.pub_tab).into_iter().map(|i| evals[i]).collect())
    };
    lap("bus+tables", &mut stages);

    // ---- phase 3b (A23): fold acc_in with this proof's fixed-column claims
    let fold = acc::prove(&mut ps, p, &hd.acc_in, &table_point, &v_fix, &acc::fix_cols(&rec.tables, p.pub_tab));
    stages.push(("line eval", fold.secs));
    lap("acc", &mut stages);

    // ---- Tape (BLUEPRINT2 §1.2 T1–T2, S2; T-P1 C.3–C.4): r, the 25 output lanes, the depth-24 GKR to the input claim
    let r = ps.sample_vec(p.log_n);
    let out = if dense {
        OutputClaim::of_inputs(chain.shape, &chain.inputs, r.clone())
    } else {
        OutputClaim::of_inputs_padded(chain.shape, &chain.inputs, r.clone())
    };
    ps.add_scalars(&out.lanes);
    let fin = tape_w.prove_tape(&mut ps, &out);
    drop(tape_w);
    lap("tape", &mut stages);

    // ---- Wire (T3–T4; T-P1 C.5–C.6), then the CH claims in the order of C.7: T1's words, the D ring, the boundary
    let d_ring = crate::lvm::wire::prove_wire(&mut ps, &lay, &chain, &cmain, &fin, &hd.s, n, dense);
    for l in 0..4 {
        main_claims.push(Claim::point(lay.d(l), r.clone(), out.lanes[l]));
    }
    main_claims.push(d_ring);
    let hl = tables::digest_lanes(&hd.h);
    for l in 0..4 {
        main_claims.push(Claim::point(lay.d(l), bits_point(n - 1, p.log_n), e(hl[l])));
    }
    drop(chain);
    lap("wire", &mut stages);

    // ---- KS
    let ks_block = lay.ks_off..lay.ks_off + (1 << lay.ks_vars());
    let rk = ps.sample_vec(p.ks_log);
    let kout = OutputClaim::of_inputs(ks.shape, &ks.inputs, rk.clone());
    ps.add_scalars(&kout.lanes);
    let kopen = ks_w.prove(&mut ps, &cmain[ks_block], &kout);
    drop(ks_w);
    let (kring, kword) = kopen.into_pcs_claims(lay.ks_off);
    let ks_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
    let StackClaim::Point { offset, low_point, value } = kword.expect("the KS word claim");
    main_claims.push(Claim::point(offset, low_point, value));
    let krc = kring.claims.into_iter().next().unwrap();
    main_claims.push(Claim::ring(lay.ks_off, krc.suffix_point, krc.s_hat_v.unwrap(), ks_map));
    lap("KS gkr", &mut stages);

    // ---- KS link
    let klink = link::prove_ks::<F192, 3>(&mut ps, &lay, &ks);
    drop(ks);
    lap("KS link", &mut stages);

    // ---- the claim lists (S2, T-P1 C.7: bus ++ tables ++ (T1 words ++ D ring ++ boundary) ++ KS ++ KS outputs ++ KS link)
    for l in 0..LANES {
        main_claims.push(Claim::point(lay.ks_y(l), rk.clone(), kout.lanes[l]));
    }
    // KS link order is [Y, in, M, X], all on C_main (R11, S2GM: M is S's columns)
    main_claims.extend(klink);

    // ---- the opening: C_main only (SH2-Z: its claims on the committed stack), zero-padded over S
    let main_claims = shape::relocate(&lay, main_claims);
    let main_stack = open_stack(&lay, cmain, main_words, sh2_dense);
    open_mixed_whir_stacked(&mut ps, p.nu_main, main_stack, main_data, &whir_config(&p.main_levels, p.grind, p.main_ood), main_claims.into_iter().map(mixed).collect());
    lap("open main", &mut stages);
    finish(p, ps, hd.h, fold.out, stages)
}

// ------------------------------------------------------------------ E2F (S2GF): the front over its field

pub use crate::lvm::params::FrontCfg;

/// E2F: the tape (T1–T2) and the wire (T3–T4) in `F`; appends the CH claims in T-P1 C.7's order (T1's words, the D
/// switch, the boundary).
#[allow(clippy::too_many_arguments)]
fn front_tape<F: crate::lv::primitives::field::Ext<W>, const W: usize>(
    ps: &mut ProverState,
    p: &Params,
    lay: &Layout,
    chain: &Chain,
    cmain: &[F64],
    tape_w: crate::lv::keccak_gkr::Witness,
    hd: &Header,
    dense: bool,
    main_claims: &mut Vec<Claim>,
    lap: &mut dyn FnMut(&'static str),
) {
    use crate::lv::fiat_shamir::transcript::Grp;
    let n = hd.n as usize;
    // S2GT: the front's first E2 challenge takes the separator again (after the typed phases' E2 challenges)
    if crate::lvm::params::FrontCfg::get().typed_t {
        ps.e2_restart();
    }
    let r: Vec<F> = ps.challenges::<F, W>(Grp::C1, p.log_n);
    let out = crate::lv::keccak_gkr::front::output_claim_in::<F, W>(chain.shape, &chain.inputs, r.clone(), !dense);
    ps.add_ext(&out.lanes);
    let fin = tape_w.prove_tape_in::<F, W>(ps, &out);
    drop(tape_w);
    lap("tape");
    let d_switch = crate::lvm::wire::prove_wire(ps, lay, chain, cmain, &fin, &hd.s, n, dense);
    for l in 0..4 {
        main_claims.extend(Claim::word(vec![(lay.d(l), r.clone(), F::ONE)], out.lanes[l]));
    }
    main_claims.push(d_switch);
    let hl = tables::digest_lanes(&hd.h);
    for l in 0..4 {
        main_claims.push(Claim::point(lay.d(l), bits_point(n - 1, p.log_n), e(hl[l])));
    }
    lap("wire");
}

/// E2F: KS (its output claim, GKR, openings and switch) and the KS link in `F`; appends the KS claims (word, switch),
/// the 25 output lanes and the link's `[Y, in, M, X]`.
fn front_ks<F: crate::lv::primitives::field::Ext<W>, const W: usize>(
    ps: &mut ProverState,
    p: &Params,
    lay: &Layout,
    cmain: &[F64],
    ks_w: crate::lv::keccak_gkr::Witness,
    ks: Sponge,
    main_claims: &mut Vec<Claim>,
    lap: &mut dyn FnMut(&'static str),
) {
    use crate::lv::fiat_shamir::transcript::Grp;
    use crate::lvm::front::{E2Term, row_switch, to_e2, to_e3};
    let ks_block = lay.ks_off..lay.ks_off + (1 << lay.ks_vars());
    let rk: Vec<F> = ps.challenges::<F, W>(Grp::C1, p.ks_log);
    let kout = crate::lv::keccak_gkr::front::output_claim_in::<F, W>(ks.shape, &ks.inputs, rk.clone(), false);
    ps.add_ext(&kout.lanes);
    let kopen = ks_w.prove_in::<F, W>(ps, &cmain[ks_block], &kout);
    drop(ks_w);
    let (kpoint, kslices) = kopen.inputs;
    let (wpoint, wvalue) = kopen.outputs.expect("the KS word claim");
    main_claims.extend(Claim::word(vec![(lay.ks_off, wpoint, F::ONE)], wvalue));
    if W == 3 {
        let ks_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
        main_claims.push(Claim::ring(lay.ks_off, kpoint.into_iter().map(to_e3).collect(), kslices.into_iter().map(to_e3).collect(), ks_map));
    } else {
        let r2 = ps.sample_vec(crate::lvm::wire::ROW_SWITCH_STAGES);
        let (phi, sigma) = row_switch(&kslices.into_iter().map(to_e2).collect::<Vec<_>>(), &r2);
        main_claims.push(Claim::E2 { terms: vec![E2Term { offset: lay.ks_off, point: kpoint.into_iter().map(to_e2).collect(), phi, klin: false }], value: sigma });
    }
    lap("KS gkr");
    let klink = link::prove_ks::<F, W>(ps, lay, &ks);
    drop(ks);
    lap("KS link");
    for l in 0..LANES {
        main_claims.extend(Claim::word(vec![(lay.ks_y(l), rk.clone(), F::ONE)], kout.lanes[l]));
    }
    main_claims.extend(klink);
}

/// U-TAPE (stage S2GU, COMMON T1–T5, `utape.py`): the 21-variable tape with KS merged in, at `F` (E2). T1 in R-BP2's B1
/// order: `r_<20`, the 50 scalars (`a_l`: the chain half's output lanes at `r_<20`, `a_<4` the `D` words; `b_l =
/// Ỹ_l(r_<13)`, the `Y` block's words), then `r_20`; the output claim `v_l = (1 − r_20)·a_l + r_20·(e·b_l + (1 − e)·z*_l)`,
/// `e = Π_{k=13}^{19}(1 − r_k)`. T2: the halves (the chain's `tape_w`, the sponges' `sp_w`) in one transcript; the dense
/// oracle runs one batch of `2^20 + 2^13` written rows. T3–T4: [`crate::lvm::wire::prove_wire_u`]. Appends the claims in
/// the lead's D-ORD order (revised): `a_0..a_3`, `b_0..b_24`, the `D`, `Y`, `M` rows, the boundary `h_0..h_3`.
#[allow(clippy::too_many_arguments)]
fn front_utape<F: crate::lv::primitives::field::Ext<W>, const W: usize>(
    ps: &mut ProverState,
    p: &Params,
    lay: &Layout,
    chain: &Chain,
    ks: &Sponge,
    cmain: &[F64],
    tape_w: crate::lv::keccak_gkr::Witness,
    sp_w: Option<crate::lv::keccak_gkr::Witness>,
    hd: &Header,
    dense: bool,
    main_claims: &mut Vec<Claim>,
    lap: &mut dyn FnMut(&'static str),
) {
    use crate::lv::fiat_shamir::transcript::Grp;
    use crate::lv::primitives::field::Unreduced;
    let n = hd.n as usize;
    let (w, hs) = (p.log_n, p.ks_log);
    let nh = 1usize << hs;
    assert!(FrontCfg::get().typed_t, "S2GU's typed phases are S2GT's");
    ps.e2_restart();
    let r_lo: Vec<F> = ps.challenges::<F, W>(Grp::C1, w);
    let a_out = crate::lv::keccak_gkr::front::output_claim_in::<F, W>(chain.shape, &chain.inputs, r_lo.clone(), !dense);
    let mut zs = [0u64; LANES];
    crate::lv::primitives::hash::keccak_f(&mut zs);
    // b_l = Ỹ_l(r_<13): the Y block's 2^13 rows of C_main (KS13's outputs; read from the commitment, so that its word
    // claims hold on what is committed)
    let ylane = |j: usize, l: usize| cmain[lay.y_lane(l) + j];
    let lane_sums = |eq: &[F]| -> [F; LANES] {
        crate::lv::parallel::fold_reduce(
            eq.len(),
            || [F::Unreduced::ZERO; LANES],
            |acc, j| {
                for (l, acc) in acc.iter_mut().enumerate() {
                    *acc ^= eq[j].mul_base_unreduced(ylane(j, l));
                }
            },
            |mut a, b| {
                for (a, b) in a.iter_mut().zip(b) {
                    *a ^= b;
                }
                a
            },
        )
        .map(|x| x.reduce())
    };
    let b_out = lane_sums(&F::eq_table(&r_lo[..hs]));
    // (dev tamper `LVM_UT_TAMPER=r20first`: r_20 drawn before the 50 scalars, against B1's order; V_S must reject)
    let r20first = std::env::var("LVM_UT_TAMPER").is_ok_and(|v| v == "r20first");
    let r_top = if r20first {
        eprintln!("lvm: LVM_UT_TAMPER=r20first: r_20 before the 50 scalars");
        let r = ps.challenge::<F, W>(Grp::C1);
        ps.add_ext(&a_out.lanes);
        ps.add_ext(&b_out);
        r
    } else {
        ps.add_ext(&a_out.lanes);
        ps.add_ext(&b_out);
        ps.challenge::<F, W>(Grp::C1)
    };
    let e_r: F = r_lo[hs..w].iter().fold(F::ONE, |acc, &r| acc * (F::ONE + r));
    let zf = |l: usize| F::ONE.mul_base(F64(zs[l]));
    let sp_half: [F; LANES] = std::array::from_fn(|l| e_r * b_out[l] + (F::ONE + e_r) * zf(l));
    {
        // T1's region formula against the sponge half's claim over all 2^20 rows of the half (rows ≥ 2^13: z*)
        let ew = crate::lvm::front::eq_prefix(&r_lo, nh);
        let mut spc = lane_sums(&ew);
        let rest = F::ONE + ew.iter().copied().sum::<F>();
        for (l, x) in spc.iter_mut().enumerate() {
            *x += rest * zf(l);
        }
        assert!(spc == sp_half, "T1: Σ_j eq(r_<20, j)·Z(2^20 + j) = e·b + (1 − e)·z*");
    }
    let out = crate::lv::keccak_gkr::OutputClaim {
        instance: [&r_lo[..], &[r_top]].concat(),
        lanes: std::array::from_fn(|l| (F::ONE + r_top) * a_out.lanes[l] + r_top * sp_half[l]),
    };
    let fin = match sp_w {
        Some(sw) => {
            let fin = crate::lv::keccak_gkr::Witness::prove_tape_halves_in::<F, W>([&tape_w, &sw], ps, &out);
            drop(sw);
            drop(tape_w);
            fin
        }
        None => {
            // the dense oracle: one batch of 2^21 instances, the chain's 2^20 written rows, then KS13's
            assert!(dense, "the sponge half's witness (sparse mode)");
            drop(tape_w);
            let rows: Vec<[u64; LANES]> = [&chain.inputs[..], &ks.inputs[..]].concat();
            assert_eq!(chain.inputs.len(), 1 << w, "the dense chain half is written out");
            let shape = crate::lv::keccak_gkr::Shape::new(2 << w, crate::lvm::params::TAPE_DEPTH);
            let all = crate::lv::keccak_gkr::Witness::generate_uncommitted(shape, &rows);
            drop(rows);
            all.prove_tape_in::<F, W>(ps, &out)
        }
    };
    lap("tape");
    let wr = crate::lvm::wire::prove_wire_u::<F, W>(ps, lay, chain, ks, cmain, &fin, &hd.s, n, dense);
    // the lead's D-ORD (revised): a_0..a_3, b_0..b_24, the D, Y, M rows, the boundary h
    for l in 0..4 {
        main_claims.extend(Claim::word(vec![(lay.d(l), r_lo.clone(), F::ONE)], a_out.lanes[l]));
    }
    for l in 0..LANES {
        main_claims.extend(Claim::word(vec![(lay.y_lane(l), r_lo[..hs].to_vec(), F::ONE)], b_out[l]));
    }
    main_claims.push(wr.d);
    main_claims.push(wr.y);
    main_claims.push(wr.m);
    let hl = tables::digest_lanes(&hd.h);
    for l in 0..4 {
        main_claims.push(Claim::point(lay.d(l), bits_point(n - 1, p.log_n), e(hl[l])));
    }
    lap("wire");
}

/// The end of a proof: the schedule's last query is asked, one grind per `C_main` level, the proof's shape.
fn finish(p: &Params, mut ps: ProverState, h: Digest, acc_out: Acc, stages: Vec<(&'static str, f64)>) -> SProof {
    assert!(ps.nothing_pending(), "the schedule ends with an FS query");
    if !ps.e2_grinds.is_empty() && std::env::var_os("LVM_LOG").is_some() {
        let att: u64 = ps.e2_grinds.iter().map(|g| g.1).sum();
        eprintln!(
            "lvm: E2 grinding: {} challenges, {att} attempts, {} requests, {} hashed queries ({} beyond one per challenge), {:.4} s (search incl. the accepted FS step)",
            ps.e2_grinds.len(), ps.e2_requests, ps.e2_hashed, ps.e2_hashed - ps.e2_grinds.len(), ps.e2_grind_s
        );
    }
    // (dev, the schedule self-check: `LVM_GRIND_DUMP=FILE` appends the PoW bits `g` of every E2 challenge in order, one
    // proof per line, for `s2gt.py`'s grinds list)
    if let Some(f) = std::env::var_os("LVM_GRIND_DUMP") {
        use std::io::Write;
        let line: Vec<String> = ps.e2_grinds.iter().map(|g| g.0.to_string()).collect();
        let mut h = std::fs::OpenOptions::new().create(true).append(true).open(f).expect("LVM_GRIND_DUMP");
        writeln!(h, "{}", line.join(" ")).expect("LVM_GRIND_DUMP");
    }
    // PFAST probe (dev): the oracle's per-class requests and waits for this proof
    if std::env::var_os("LVM_OREPORT").is_some() {
        eprint!("{}", crate::oracle::report());
    }
    let grind_attempts = std::mem::take(&mut ps.grind_attempts);
    assert_eq!(grind_attempts.len(), if p.grind > 0 { p.main_levels.len() } else { 0 }, "one grind per WHIR level");
    let proof = std::mem::take(&mut ps.body);
    let trace = std::mem::take(&mut ps.trace);
    if std::env::var_os("LVM_UT_TAMPER").is_some() {
        // (U-TAPE dev tamper: the query lengths move with the challenge order; the size is the schedule's)
        assert_eq!(proof.len(), params::pi_size(p), "piSize");
    } else {
        check_shape(p, &proof, &trace);
    }
    SProof { proof, trace, h, acc_out, stages, grind_attempts }
}

/// `C_main`'s commitment on its first `main_words` (buffer) words: SH2-Z's small shape commits the even-word table of
/// the logical one (`LVM_SH2_DENSE=1`: as a dense table, the byte-identity reference; CR-E tamper
/// `LVM_SH2_ODDJUNK=1`: the dense path with junk in the odd words, which V_S never reads: it must accept). Returns the
/// physical table of the dense modes.
fn commit_main(p: &Params, lay: &Layout, cmain: &[F64], main_words: usize) -> (crate::lv::pcs::whir::Commitment, crate::lv::pcs::whir::ProverData, Option<Vec<F64>>) {
    let m0 = p.main_levels[0];
    let occ_main = params::occ_lanes(&p.main_levels);
    let odd_junk = lay.small && std::env::var("LVM_SH2_ODDJUNK").is_ok_and(|v| v == "1");
    let sh2_dense = (lay.small && (odd_junk || std::env::var("LVM_SH2_DENSE").is_ok_and(|v| v == "1")))
        .then(|| if odd_junk { shape::expand_junk(&cmain[..main_words]) } else { shape::expand(&cmain[..main_words]) });
    let (cm, data) = match &sh2_dense {
        Some(phys) => commit(phys, p.nu_main, INITIAL_FOLDING_FACTOR, m0.rate, m0.cap, occ_main),
        None if lay.small => commit_even(&cmain[..main_words], p.nu_main, INITIAL_FOLDING_FACTOR, m0.rate, m0.cap, occ_main),
        None => commit(&cmain[..main_words], p.nu_main, INITIAL_FOLDING_FACTOR, m0.rate, m0.cap, occ_main),
    };
    (cm, data, sh2_dense)
}

/// The stack `C_main` is opened on ([`open_len`] buffer words; the dense modes' physical table zero-padded to twice
/// that).
fn open_stack(lay: &Layout, mut cmain: Vec<F64>, main_words: usize, sh2_dense: Option<Vec<F64>>) -> Vec<F64> {
    let ol = open_len(lay, main_words);
    match sh2_dense {
        Some(mut phys) => {
            phys.resize(2 * ol, F64::ZERO);
            phys
        }
        None => {
            cmain.truncate(ol);
            cmain
        }
    }
}

/// E2F (dev, `LVM_E2F_CHECK=1`): every opening claim's value against the stack it is opened on (the physical table;
/// `even`: `stack` is its half message, word `2w` = `stack[w]`): point claims and E2 claims (word coordinates, row
/// switches) by direct sums; E3 ring claims are not checked here.
fn check_claims(claims: &[Claim], stack: &[F64], even: bool) {
    use crate::lv::primitives::multilinear::eq_table;
    use crate::lvm::front::E2Fold;
    let word = |u: usize| -> F64 {
        if even {
            if u & 1 == 1 { F64::ZERO } else { stack.get(u >> 1).copied().unwrap_or(F64::ZERO) }
        } else {
            stack.get(u).copied().unwrap_or(F64::ZERO)
        }
    };
    let (mut ok, mut bad) = (0usize, 0usize);
    for (i, c) in claims.iter().enumerate() {
        let (got, want) = match c {
            Claim::Point { terms, value } => {
                let mut s = F192::ZERO;
                for (o, p, k) in terms {
                    let e = eq_table(p);
                    let part = crate::lv::parallel::fold_reduce(e.len(), || F192::ZERO, |acc, b| *acc += e[b].mul_base(word(o + b)), |a, b| a + b);
                    s += *k * part;
                }
                (s, *value)
            }
            Claim::E2 { terms, value } => {
                let mut s = F192::ZERO;
                for t in terms {
                    let fold = E2Fold::new(&t.phi, &t.point);
                    let n = 1usize << t.point.len();
                    s += crate::lv::parallel::fold_reduce(
                        n.div_ceil(4096),
                        || F192::ZERO,
                        |acc, blk| {
                            let lo = blk * 4096;
                            let len = 4096.min(n - lo);
                            let mut out = vec![F192::ZERO; len];
                            fold.add_chunk(lo, &mut out);
                            for (j, w) in out.iter().enumerate() {
                                *acc += w.mul_base(word(t.offset + lo + j));
                            }
                        },
                        |a, b| a + b,
                    );
                }
                (s, *value)
            }
            Claim::Ring { .. } => continue,
        };
        if got == want {
            ok += 1;
        } else {
            bad += 1;
            eprintln!("lvm: LVM_E2F_CHECK: claim {i} WRONG ({})", match c { Claim::Point { .. } => "point", Claim::E2 { .. } => "E2", _ => "ring" });
        }
    }
    eprintln!("lvm: LVM_E2F_CHECK: {ok} claims hold, {bad} wrong");
    assert_eq!(bad, 0, "LVM_E2F_CHECK: every checked claim holds on the stack");
}

/// B1-IE (roll 8, B-DES §1.2; V_S `LvmTypedV.decideProgT`, `LvmTypedVSched.phasesT`): the typed backend's proof from
/// the witness section's products. The B program's run gives the word vector `z` (`typed_lay::witness`); its virtual
/// regions are filled from their sources and checked against the inputs; `C_main`'s typed region holds `z`'s
/// committed words, then the mini-bus's count and finalize columns. Then: commit; zerocheck, wiring, relayout, A23 at
/// `Φ_Q` (`typed_prove::prove`); the mini-bus (`m3::prove` on `mbT`); tape, wire, `KS`, `KS` link as the bus path;
/// the openings with the typed claims first (`typedClaimsN ++ dClaimsZ … [] evals …`).
#[allow(clippy::too_many_arguments)]
fn typed_tail(
    p: &Params,
    hd: Header,
    lay: &Layout,
    tb: &TypedB,
    run: crate::lvm::loopir::Run,
    chain: Chain,
    ks: Sponge,
    mut cmain: Vec<F64>,
    tape_w: crate::lv::keccak_gkr::Witness,
    ks_w: Option<crate::lv::keccak_gkr::Witness>,
    mut stages: Vec<(&'static str, f64)>,
    dense: bool,
) -> SProof {
    use crate::lvm::typed_prove::{self, TData, TReg};
    let n = hd.n as usize;
    let mut t = Instant::now();
    let prof = crate::lv::tracing::enabled();
    let mut c0 = if prof { crate::lv::tracing::cpu_now() } else { (0.0, 0.0) };
    let mut lap = |name: &'static str, stages: &mut Vec<(&'static str, f64)>| {
        let s = t.elapsed().as_secs_f64();
        crate::lv::tracing::record(name, s);
        if prof {
            let c = crate::lv::tracing::cpu_now();
            eprintln!("  PCPU {name:<14} wall {s:.3} cpu {:.3} svc {:.2}", c.0 - c0.0, c.1 - c0.1);
            c0 = c;
        }
        crate::alloc::memlog(name);
        stages.push((name, s));
        t = Instant::now();
    };
    // ---- the word vector: the run's cells, the virtual regions from their sources (C_main's at buffer offsets)
    let header = hd.bytes();
    let hdr: Vec<u64> = (8..header.len()).step_by(8).map(|o| u64::from_le_bytes(header[o..o + 8].try_into().unwrap())).collect();
    let loc = |g: &TReg| TReg { off: shape::buf_range(lay, g.off, 1 << g.log).expect("a typed C_main region is held in this shape"), ..*g };
    // R11 (S2GM): σ′'s regions are C_main's (an old blob's C_rec word `w` is S's `S + w`)
    let big_s = Layout::new(p).s_off;
    let td = TData {
        com: tb.td.com.iter().map(loc).collect(),
        ks: tb.td.ks.iter().map(loc).collect(),
        sig: tb.td.sig.iter().map(|g| loc(&typed_prove::sig_main(g, big_s))).collect(),
        ..tb.td.clone()
    };
    let mut tp = Instant::now();
    // R9-TY: the words gathered from their sources on the pool (`LVM_TYPED_WREF=1`, or no table: the serial version);
    // R11-N (S2GM): `S_flat` and `σ′` read C_main's stream block `S`
    let ws = tb.ws.filter(|_| std::env::var("LVM_TYPED_WREF").map_or(true, |v| v != "1"));
    let mut z = match ws {
        Some(ws) => {
            let mut z = ws.witness(&run.kc, &run.ec);
            crate::lvm::stream::part("w set", &mut tp);
            ws.fill_bits(&mut z, tb.lay, tb.spec, &run.kc);
            crate::lvm::stream::part("w bits", &mut tp);
            let bad = typed_prove::fill_virtual_par(&mut z, &ws.set, &td, &cmain, lay.s_off, &hdr);
            // (`LVM_E2F_DEVPUB=1`, dev only: an older stage's blob on a newer header, e.g. S2GT's 16-byte acc_in
            // before the S2GT blob exists; the transcript still runs, V_S rejects the typed phases)
            if bad != 0 && std::env::var("LVM_E2F_DEVPUB").is_ok_and(|v| v == "1") {
                eprintln!("lvm: LVM_E2F_DEVPUB: {bad} input cells differ from their sources (an older blob)");
            } else {
                assert_eq!(bad, 0, "the B program's input cells hold their regions' sources (S_flat, σ′, KS, PUB)");
            }
            z
        }
        None => {
            let (mut z, set) = crate::lvm::typed_lay::witness_set(tb.c, tb.lay, tb.words, &run.kc, &run.ec);
            crate::lvm::stream::part("w set", &mut tp);
            crate::lvm::typed_lay::fill_bits(&mut z, tb.lay, tb.spec, &run.kc);
            crate::lvm::stream::part("w bits", &mut tp);
            let bad = typed_prove::fill_virtual(&mut z, Some(&set), &td, &cmain, lay.s_off, &hdr);
            assert_eq!(bad, 0, "the B program's input cells hold their regions' sources (S_flat, σ′, KS, PUB)");
            z
        }
    };
    let tm = std::env::var("LVM_TYPED_TAMPER").unwrap_or_default();
    // (`LVM_TYPED_FASTZC=1`, timing only: the honest prover's zerocheck even on a failing run)
    let mut general = (!run.ok && std::env::var_os("LVM_TYPED_FASTZC").is_none()) || std::env::var_os("LVM_B1_Q1").is_some();
    if tm == "res" || tm == "e2word" {
        // a result word of a slot's `W` entry in T, not one a mini-bus read table carries (`e2word`, E2F: the `W_1`
        // entry of an e2 twin, its second result cell's word)
        let mw = if tm == "e2word" { crate::lvm::typed::MW + 4 } else { crate::lvm::typed::MW };
        let mb_w: std::collections::HashSet<usize> = tb.mb.reads.iter().flat_map(|r| [r.wa.1, r.wv.1].into_iter().flat_map(move |o| o..o + (1 << r.tau))).collect();
        let t_off = tb.td.com.first().map_or(0, |g| g.off);
        let w = (0..1usize << tb.b1.x_log)
            .find_map(|x| {
                tb.b1.ent[tb.b1.row_ptr[x] as usize..tb.b1.row_ptr[x + 1] as usize]
                    .iter()
                    .find(|e| e.o == mw && (e.y as usize) < 1 << crate::lvm::tables::T_VARS && !mb_w.contains(&(t_off + e.y as usize)))
                    .map(|e| e.y as usize)
            })
            .expect("a committed result word");
        z[w] = z[w] + F64::ONE;
        general = true;
        eprintln!("lvm: LVM_TYPED_TAMPER={tm}: word {w} moved");
    }
    crate::lvm::stream::part("w virtual", &mut tp);
    if ws.is_some() { typed_prove::place_com_par(&z, &td, &mut cmain) } else { typed_prove::place_com(&z, &td, &mut cmain) }
    crate::lvm::stream::part("w place", &mut tp);
    // ---- the mini-bus's tables: count and finalize columns written, the pre-placed ones checked
    let mb_com = |rec: bool, off: usize, len: usize| shape::read_big(lay, &cmain, if rec { big_s + off } else { off }, len);
    let mut mb = crate::lvm::typed_mb::tables_with(tb.mb, tb.c, &run.kc, Some(&mb_com));
    rec_to_main(p, &mut mb);
    shape::localize(lay, &mut mb);
    let sh = crate::lvm::m3::shape(&mb);
    // (MBL, S2GL: the record keeps the table numbers as shape facts, D2)
    assert_eq!(sh, (p.bus_depth, p.leafdec_reads, p.table_rounds, p.table_evals), "the mini-bus's M3 numbers are the record's");
    // the columns the prover writes (counts, finalizes) miss T and the KS aliases (their claims are z's)
    // (R11, S2GM: and the stream block's message lanes and σ′, below `free_lo`)
    let s_used = lay.rec_col(REC_STREAM_COLS) + (1 << tables::sig_region_log());
    for t in &mb {
        for &(_, _, o, wr) in &t.pre {
            let (lo, hi) = (o, o + (1 << t.tau));
            assert!(!wr || td.com.iter().chain(&td.ks).chain(&td.sig).all(|g| hi <= g.off || g.off + (1 << g.log) <= lo), "a written mini-bus column misses T, KS and σ′");
            assert!(!wr || hi <= lay.s_off || lo >= s_used.max(lay.free_lo()), "a written mini-bus column misses S's message lanes");
        }
    }
    crate::lvm::stream::part("w mb tables", &mut tp);
    let none: Vec<Vec<Option<usize>>> = mb.iter().map(|t| vec![None; t.cols.len()]).collect();
    place_columns(&mb, &none, &mut cmain);
    // R11 (S2GM): S_flat's positions past the stream read S's words, the mini-bus's columns among them: z's S_flat
    // region from C_main once everything is placed
    typed_prove::refill_sflat(&mut z, &td, &cmain, lay.s_off);
    // Z2: the committed lanes cover the fixed blocks (below `free_lo`) and the mini-bus's columns
    let occ_main = params::occ_lanes(&p.main_levels);
    let main_lane_log = lay.nu_main - INITIAL_FOLDING_FACTOR;
    let main_occ_words = occ_main << main_lane_log;
    let mb_end = mb.iter().flat_map(|t| t.pre.iter().map(move |x| x.2 + (1 << t.tau))).max().unwrap_or(0);
    let main_end = lay.free_lo().max(mb_end);
    let main_words = main_end.div_ceil(1 << main_lane_log) << main_lane_log;
    assert!(main_words <= main_occ_words, "C_main's words lie in its {occ_main} occupied lanes");
    #[cfg(feature = "selfcheck")]
    {
        assert!(cmain[main_words..].iter().all(|w| *w == F64::ZERO), "C_main past its committed lanes is zero");
    }
    lap("witness", &mut stages);

    // R11 tamper modes (dev; V_S must reject each): `sword` (one stream word of S moved: column 3, row 100), `sig` (one
    // σ′ word moved: S + 17·2^14 + 5), after the witness and before the commitment, every claim computed as usual
    // (U-TAPE: `yword`, one Y block word moved: lane 5, row 100)
    if tm == "sword" || tm == "sig" || tm == "yword" {
        let w = match tm.as_str() {
            "sword" => lay.rec_col(3) + 100,
            "yword" => lay.y_lane(5) + 100,
            _ => lay.rec_col(REC_STREAM_COLS) + 5,
        };
        cmain[w] = cmain[w] + F64::ONE;
        eprintln!("lvm: LVM_TYPED_TAMPER={tm}: C_main word {w} (buffer offset; S = {}) moved", lay.s_off);
    }
    // ---- commit (as the bus path: the small shape's even-word table, its dense and odd-junk reference modes)
    let mut ps = ProverState::seeded(&header);
    let (cm, main_data, sh2_dense) = commit_main(p, lay, &cmain, main_words);
    ps.add_cap(&cm.cap);
    // E2F (S2GF, `LvmE2FPin`): the root OOD pin right after the cap: `ν` plain samples `z` (coordinate 0 the index's
    // least significant variable), then the committed physical table's `C̃_main(z)`; its claim is the opening's first
    let cfg = FrontCfg::get();
    let pin = cfg.pin.then(|| {
        let mut z = ps.sample_vec(p.nu_main);
        // (`LVM_E2F_TAMPER=pinpt`, dev: the pin's value and claim at another point, z₀ + 1; V_S must reject)
        if std::env::var("LVM_E2F_TAMPER").is_ok_and(|v| v == "pinpt") {
            z[0] = z[0] + crate::lv::primitives::field::F192::ONE;
            eprintln!("lvm: LVM_E2F_TAMPER=pinpt: the pin at z₀ + 1");
        }
        let a = match &sh2_dense {
            Some(phys) => crate::lvm::front::pin_value(&z, phys, false),
            None => crate::lvm::front::pin_value(&z, &cmain[..main_words], lay.small),
        };
        let at = ps.body.len();
        ps.add_scalar(a);
        // (`LVM_E2F_TAMPER=pin`, dev: the pin's answer flipped in the proof; V_S must reject)
        if std::env::var("LVM_E2F_TAMPER").is_ok_and(|v| v == "pin") {
            ps.body[at] ^= 1;
            eprintln!("lvm: LVM_E2F_TAMPER=pin: the pin's answer (proof byte {at}) flipped");
        }
        Claim::point(0, z, a)
    });
    lap("commit", &mut stages);

    // ---- the typed phases: zerocheck, wiring, relayout, A23 at Φ_Q
    // tamper modes (`LVM_TYPED_TAMPER`, dev; V_S must reject each): `res` (one committed result word moved: the
    // general zerocheck, which proves what the witness is), `op:X:O:Y` (the prover's own matrices with entry `(x, o, y)`
    // on another word of the same value, so its relation and its `h(0)`, `h(1)` hold: only `Φ_Q` catches it)
    let tampered = tm.strip_prefix("op:").map(|t| {
        let v: Vec<usize> = t.split(':').map(|x| x.parse().expect("op:X:O:Y")).collect();
        let (x, o, y) = (v[0], v[1] as u8, v[2]);
        let b1 = tb.b1;
        let i = (b1.row_ptr[x] as usize..b1.row_ptr[x + 1] as usize).find(|&i| b1.ent[i].o == o && b1.ent[i].y as usize == y).expect("the tampered entry (x, o, y) is an entry");
        let y2 = (0..b1.y_live).find(|&w| w != y && z[w] == z[y]).expect("another word of the same value");
        eprintln!("lvm: LVM_TYPED_TAMPER=op: entry ({x}, {o}, {y}) moved to word {y2} (value {:#x})", z[y].0);
        b1.clone_with_entry(i, y2 as u32)
    });
    let b1p = tampered.as_ref().unwrap_or(tb.b1);
    let s_blk = &cmain[lay.s_off..lay.s_off + (1 << p.nu_rec())];
    if std::env::var("LVM_E2F_RELCHECK").is_ok_and(|v| v == "1") {
        // (S2GF: the coordinate split's relation, both coordinates of `a·b + c` in E3[X]/(X² + x·X + 1))
        // (S2GT: the same relation, read in E3 ⊗_K E2 ≅ E3[X]/(X² + x·X + 1))
        let bad = if cfg.typed_x || cfg.typed_t { b1p.check_x(&crate::lvm::typed::abc_x(b1p, &z, false)) } else { b1p.check(&b1p.abc(&z)) };
        let tot: usize = bad.iter().map(|b| b.1).sum();
        eprintln!("lvm: LVM_E2F_CHECK: a·b + (D+W)z ≠ 0 at {tot} slots in {} rows; first {:?}", bad.len(),
            bad.iter().take(6).map(|&(tag, n, x)| (b1p.tags.get(tag as usize).copied(), n, x)).collect::<Vec<_>>());
        // (dev) the failing rows per block: `block: rows (slots)`
        let mut per: std::collections::BTreeMap<usize, (usize, usize)> = std::collections::BTreeMap::new();
        for &(tag, n, _) in &bad {
            let e = per.entry(b1p.tags.get(tag as usize).map_or(usize::MAX, |t| t.0)).or_default();
            e.0 += 1;
            e.1 += n;
        }
        if !per.is_empty() {
            eprintln!("lvm: LVM_E2F_CHECK: failing rows per block {per:?}");
        }
    }
    let tout = if cfg.typed_t {
        // (a failing witness, e.g. the dev tampers `res`/`e2word`: the general zerocheck on `C = (D + W)z`)
        assert!(tampered.is_none(), "E2F: the S2GT typed phases take no `op:` tamper (yet)");
        crate::lvm::typed_t::prove_t(&mut ps, b1p, &z, &td, s_blk, lay.s_off, &hd.acc_in, general)
    } else if cfg.typed_x {
        // (a failing witness, e.g. the dev tampers `res`/`e2word`/`sword`/`sig`: the general path = the plain rounds on
        // `C = (D + W)z`, as `LVM_E2F_RELCHECK=1`)
        assert!(tampered.is_none(), "E2F: the S2GF typed phases take no `op:` tamper (yet)");
        typed_prove::prove_x(&mut ps, b1p, &z, &td, s_blk, lay.s_off, &hd.acc_in, general)
    } else {
        typed_prove::prove(&mut ps, b1p, &z, &td, s_blk, lay.s_off, &hd.acc_in, general, tampered.as_ref().map(|_| tb.b1))
    };
    drop(z);
    stages.extend(tout.stages.iter().copied());
    lap("typed", &mut stages);
    let mut main_claims: Vec<Claim> = tout.main_claims;

    // ---- the mini-bus: its bus and table sumcheck, then its committed columns' claims
    // (MBL, S2GL: its bus, then three K-linear claims on C_main, push, pull, count, where the table claims stood)
    let mut tp = Instant::now();
    // (`LVM_MBL_G0=1`, dev: the GKR's three leaf claims against MBL's identity, computed from C_main's words)
    let g0 = |pt: &[F192], al: &[F192], be: F192, vals: [F192; 3]| {
        if std::env::var("LVM_MBL_G0").is_ok_and(|v| v == "1") {
            let (want, bad) = crate::lvm::typed_mb::lin_identity(tb.mb, &mb, &cmain, pt, al, be);
            let ok = want == vals;
            eprintln!(
                "lvm: MBL G0-2: n={n} small={} mu={} tables={} placed-word mismatches={bad} push {} pull {} count {} => {}",
                lay.small, pt.len(), mb.len(),
                if want[0] == vals[0] { "EQ" } else { "NE" }, if want[1] == vals[1] { "EQ" } else { "NE" }, if want[2] == vals[2] { "EQ" } else { "NE" },
                if ok && bad == 0 { "IDENTITY HOLDS" } else { "MISMATCH" }
            );
        }
    };
    if cfg.mblin {
        let lo = crate::lvm::m3::prove_lin(&mut ps, &mb);
        crate::lvm::stream::part("mb prove", &mut tp);
        g0(&lo.point, &lo.alphas, lo.beta, lo.values);
        // (`LVM_MBL_TAMPER`, dev; V_S must reject each: `val:S` claim S's value + 1 (nothing sent changes: the value is not
        // sent, so the file is the honest one), `coef:S:K` its term K's coefficient + 1, `pos:S:K` its term K on the next
        // aligned block; `vs:S` the bus GKR's last-layer read 4·S flipped in the proof (the `v_s` V_S derives);
        // S = 0 push, 1 pull, 2 count)
        let tm: Vec<String> = std::env::var("LVM_MBL_TAMPER").unwrap_or_default().split(':').map(String::from).collect();
        let tsel = |i: usize| tm.get(i).map(|x| x.parse::<usize>().expect("LVM_MBL_TAMPER: MODE:S[:K]"));
        if tm[0] == "vs" {
            // the bus phase ends: the last GKR layer's 12 E3 reads, its 2 samples, the trailing zero (24 B)
            let at = ps.body.len() - 24 - 12 * 24 + 24 * 4 * tsel(1).unwrap();
            ps.body[at] ^= 1;
            eprintln!("lvm: LVM_MBL_TAMPER=vs:{}: the bus GKR's last-layer read (proof byte {at}) flipped", tm[1]);
        }
        for (s, cl) in lo.claims.iter().enumerate() {
            let mut terms: Vec<(usize, Vec<F192>, F192)> = cl
                .terms
                .iter()
                .map(|&(t, c, k)| (mb[t].pre_of(c).expect("every mini-bus column is pre-placed").1, lo.point[..mb[t].tau].to_vec(), k))
                .collect();
            let mut value = cl.value;
            if tsel(1) == Some(s) {
                match tm[0].as_str() {
                    "val" => value += F192::ONE,
                    "coef" => terms[tsel(2).unwrap()].2 += F192::ONE,
                    "vs" => {}
                    "pos" => {
                        let tk = &mut terms[tsel(2).unwrap()];
                        tk.0 += 1 << tk.1.len();
                    }
                    m => panic!("LVM_MBL_TAMPER={m}: val, coef or pos"),
                }
                eprintln!("lvm: LVM_MBL_TAMPER={}: claim {s} tampered", tm.join(":"));
            }
            main_claims.push(Claim::Point { terms, value });
        }
    } else {
        let mo = crate::lvm::m3::prove(&mut ps, &mb);
        crate::lvm::stream::part("mb prove", &mut tp);
        g0(&mo.point, &mo.alphas, mo.beta, mo.values);
        for (cl, tw) in mo.claims.iter().zip(&mb) {
            for c in tw.committed() {
                match tw.pre_of(c) {
                    Some((_, o)) => main_claims.push(Claim::point(o, cl.chi.clone(), cl.evals[c])),
                    None => unreachable!("every mini-bus column is pre-placed"),
                }
            }
        }
    }
    drop(mb);
    lap("mini-bus", &mut stages);

    // ---- Tape, Wire, KS, KS link: the bus path's (E2F: in the stage's front field)
    {
        let mut lapf = |name: &'static str| lap(name, &mut stages);
        if cfg.utape {
            // U-TAPE (S2GU): the tape with KS merged in, the wire with the sponge terms; no KS, no KS link
            front_utape::<F128, 2>(&mut ps, p, lay, &chain, &ks, &cmain, tape_w, ks_w, &hd, dense, &mut main_claims, &mut lapf);
            drop(chain);
            drop(ks);
        } else {
            if cfg.tape_e2 {
                front_tape::<F128, 2>(&mut ps, p, lay, &chain, &cmain, tape_w, &hd, dense, &mut main_claims, &mut lapf);
            } else {
                front_tape::<F192, 3>(&mut ps, p, lay, &chain, &cmain, tape_w, &hd, dense, &mut main_claims, &mut lapf);
            }
            drop(chain);
            if cfg.ks_e2 {
            front_ks::<F128, 2>(&mut ps, p, lay, &cmain, ks_w.expect("KS"), ks, &mut main_claims, &mut lapf);
        } else {
            front_ks::<F192, 3>(&mut ps, p, lay, &cmain, ks_w.expect("KS"), ks, &mut main_claims, &mut lapf);
            }
        }
    }

    // ---- the opening: C_main only (the small shape: its claims on the committed stack). The relayout's point claim
    // weighs the whole stream block S (absent lanes too): the opening runs on the zero-padded stack, its rows the
    // committed lanes' (`whir::ProverData::n_lanes`)
    let mut main_claims = shape::relocate(lay, main_claims);
    // E2F: the pin's claim is on the committed physical table (not relocated), first; its weight covers the whole
    // `2^ν` table, the stack only the words up to `open_len` (the opening's weight tables reach the lanes past the
    // stack, whose words are zero: `stack_open::basis`)
    if let Some(c) = pin {
        main_claims.insert(0, c);
    }
    let half = lay.small && sh2_dense.is_none();
    let main_stack = open_stack(lay, cmain, main_words, sh2_dense);
    if std::env::var("LVM_E2F_CHECK").is_ok_and(|v| v == "1") {
        check_claims(&main_claims, &main_stack, half);
    }
    open_mixed_whir_stacked(&mut ps, p.nu_main, main_stack, main_data, &whir_config(&p.main_levels, p.grind, p.main_ood), main_claims.into_iter().map(mixed).collect());
    lap("open main", &mut stages);
    if std::env::var_os("LVM_SPANS").is_some() {
        eprint!("{}", crate::lv::tracing::report());
    }
    finish(p, ps, hd.h, tout.acc_out, stages)
}

/// The proof has the schedule's size and the trace the schedule's query classes and lengths, in order.
pub fn check_shape(p: &Params, proof: &[u8], trace: &Trace) {
    assert_eq!(proof.len(), params::pi_size(p), "piSize");
    let want = params::query_list(p);
    assert_eq!(trace.len(), want.len(), "qS");
    for (i, ((q, _), (cls, len))) in trace.iter().zip(&want).enumerate() {
        assert_eq!(q.len(), *len, "query {i} ({cls:?}) length");
        if *cls == QClass::Seed {
            assert_eq!(&q[32..], &proof[8..params::header_bytes(p)], "the seed carries the header");
        }
    }
}
