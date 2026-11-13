//! The committed tables and where they sit (BLUEPRINT §3.1, §4.1–4.2, §11 A7, A9; WP-15a layout, sent to
//! WP-11a for `M3.chBlock`/`ksBlock`):
//!
//! `C_main` (`2^nu_main` K words), S2 (BLUEPRINT2 §2.2; FRZ-0's layout, docs/lvm2/stages/T-P1.md C.1): the fixed
//! blocks largest first from word 0 (ties `D`, `KS`, `KSY2`, `X`), then the recursion tables from `free_lo`.
//! - `D`: the chain digests, lane `l < 4` at `d_off + l·2^log_n` (an aligned 4-column cube).
//! - `KS` (`ks_log + 6` variables): its own slots `in` 0–24, `mid` 25–49, `Y` lanes 0–13 in 50–63.
//! - `KSY2` (KS `Y` lanes 14–24, one `2^ks_log` column each), `X` (`X_l`, the KS messages of rows `≥ ks_split`).
//! - `P20` (ν = 24, KS14: `ks_log = rec_rows_log = 14`, `X_l` of `2^10` rows from KS row 15,360): `D` 0, `KS` 4·2^20,
//!   `KSY2` 5·2^20, `X` 5·2^20 + 2^18, tables from 5,537,792; its small shape (SH2-Z, `n ≤ 2^18`, `lvm::shape`): `D`
//!   0 (`2^18` rows a lane), `KS` 2^20, `KSY2` 2·2^20, `X` 2·2^20 + 2^18, tables from 2,392,064, of `2^23` words.
//!   `P8` (ν = 23): `KS` 0, `KSY2` 2^20, `X` 2^20 + 2^18, `D` 2^20 + 2^19.
//!
//! R11 (M′, stage S2GM, docs/lvm2/stages/R11-E.md): there is no `C_rec`. Its old content is `C_main`'s stream block
//! `S` (`2^(rec_rows_log + 5)` words, aligned, after `KS`): column `c` at `S + c·2^rec_rows_log`: the 17 `KS` message
//! lanes `M_l` (all `2^ks_log` rows: the stream below `ks_split`, the `X` messages from it, so the `X` block is gone),
//! `σ'` at column 17, then `KSY2` (11 lanes, aligned to `2^ks_log`) and the mini-bus's columns (`free_lo`).
//! `P20`: `S` 5,767,168, `KSY2` 6,053,888, `free_lo` 6,144,000; `P8`: `S` 6,291,456.

use crate::lv::keccak_gkr::{Shape, Witness};
use crate::lv::primitives::field::F64;
use crate::lvm::layout;
use crate::lvm::params::{GKR_DEPTH, LANES, Params, REC_STREAM_COLS, SLOT_LOG, TAPE_DEPTH};
use crate::oracle::Digest;

/// `log2` of the `D` block's lanes (4).
pub const D_LOG: usize = 2;

/// Where every column of the two commitments sits (word offsets).
///
/// SH2-Z (CR-DES §1.4, roll 7): a `P20` step with `n ≤ 2^SMALL_LOG_N` is the *small shape*. Its layout
/// ([`Layout::shape`] with `small`) is `layout::P20S`, the logical `2^23`-word table: `D_l` holds rows
/// `< 2^SMALL_LOG_N` only (`d_log`), the other blocks are the big layout's moved down by `3·2^20`. The buffer holds the
/// logical table; the commitment is the `2^24`-word table with logical word `w` at physical word `2w` and every
/// odd word zero (`whir::commit_even`). Every claim is made at the logical offsets with the big layout's points
/// and values (the transcript is the big layout's, `D`'s rows `≥ 2^18` being `z*`), then
/// [`crate::lvm::shape::relocate`] puts it on the physical stack (`LvmShape.onStackZ`).
#[derive(Clone, Debug)]
pub struct Layout {
    pub log_n: usize,
    pub ks_log: usize,
    pub rec_log: usize,
    /// The variables of the buffer (`2^nu_main` words; the small shape's logical table: `nu_main` = 23).
    pub nu_main: usize,
    pub nu_rec: usize,
    /// S2: the chain digests `D_l` (4 lanes × `2^d_log` rows), one aligned block (BLUEPRINT2 §1.1, T-P1 C.1).
    pub d_off: usize,
    /// The rows of a `D` lane held in the buffer: `log_n`, or `SMALL_LOG_N` in the small shape (rows above are `z*`).
    pub d_log: usize,
    pub ks_off: usize,
    /// B1 (roll 8): the typed region `T` (`2^20` words: `z`'s committed words, B1-K's layout).
    pub t_off: usize,
    pub ksy2_off: usize,
    /// S2GM: `S + ks_split` (`X_l` at `+ l·2^rec_log`: the top rows of `S`'s column `l`).
    pub x_off: usize,
    /// S2GM: the stream block `S` (the old `C_rec`: `2^nu_rec` words, column `c` at `+ c·2^rec_log`).
    pub s_off: usize,
    /// KS14: the rows of an `X` column (`2^x_log`); KS row `j ≥ ks_split` absorbs `X[j − ks_split]`.
    pub x_log: usize,
    /// KS14: KS rows `< ks_split` absorb the stream (`M_l`'s rows), the others `X` (the same columns' top rows).
    pub ks_split: usize,
    /// SH2-Z: the small shape (`P20`, `n ≤ 2^SMALL_LOG_N`).
    pub small: bool,
    /// The end of the fixed blocks: where the recursion tables go.
    free_lo: usize,
}

/// `log₂` of `σ'`'s region (597 lanes in 2^10 words).
pub const SIG_LOG: usize = 10;

/// KS14 (CR-DES §2): with `ks_log ≤ rec_rows_log`, the `X` columns have `2^(ks_log − KS14_SEL)` rows (P20: `2^10`,
/// selector `x₁₃x₁₂x₁₁x₁₀`; the Lean `ksXLog`).
pub const KS14_SEL: usize = 4;

/// SH2-Z: the big layout's blocks from `KS` up sit `SMALL_SHIFT` words higher than the small logical ones.
pub const SMALL_SHIFT: usize = 3 << 20;

/// The rows of an `X` column (the Lean `ksXLog`): KS14's `2^(ks_log − 4)` when `ks_log ≤ rec_log` (P20), else
/// `2^rec_log` (v1's layout, `ks_log = rec_log + 1`: P8).
pub fn x_log(ks_log: usize, rec_log: usize) -> usize {
    if ks_log <= rec_log {
        ks_log - KS14_SEL
    } else {
        assert_eq!(ks_log, rec_log + 1, "KS rows: the stream rows, then the X rows");
        rec_log
    }
}

/// The first KS row that absorbs `X` (`2^ks_log − 2^x_log`: P8 `2^rec_log`, KS14 15,360); the rows below absorb `M_l`.
pub fn ks_split(ks_log: usize, rec_log: usize) -> usize {
    let s = (1usize << ks_log) - (1usize << x_log(ks_log, rec_log));
    assert!(s <= 1 << rec_log, "the stream rows fit S's columns");
    s
}

/// B1: the typed region's variables (`T`: `2^20` words, the word space's committed region `[0, 2^comLog)`).
pub const T_VARS: usize = 20;

/// The KS slot of `Y` lane 0; lanes `0..KS_Y_IN_BLOCK` are in the KS block.
pub const KS_Y_SLOT: usize = 50;
pub const KS_Y_IN_BLOCK: usize = 14;

impl Layout {
    /// The big layout of `p` (every step at `P8`, and `P20`'s steps with `n > 2^SMALL_LOG_N`).
    pub fn new(p: &Params) -> Self {
        Self::shape(p, false)
    }
    /// SH2-Z: whether a step of `n` rows at `p` has the small shape (`P20` only): a function of the header, as
    /// `LvmShape.small` (no switch: a big-shape proof of a small statement is rejected).
    pub fn is_small(p: &Params, n: usize) -> bool {
        p.name == "P20" && p.nu_main == layout::P20.nu_main && n <= 1 << layout::SMALL_LOG_N
    }
    /// The layout of a step of `n` rows ([`Self::is_small`]).
    pub fn of_step(p: &Params, n: usize) -> Self {
        Self::shape(p, Self::is_small(p, n))
    }
    /// The big layout, or with `small` (`P20` only) the small shape's logical layout `layout::P20S`.
    pub fn shape(p: &Params, small: bool) -> Self {
        // S2 (T-P1 C.1 = FRZ-0's rule): the fixed blocks largest first from word 0, ties in the order D, KS, KSY2, X
        // (each a power of two, so each lands aligned to its size); the recursion tables from the end (`free_lo`)
        // KS14: `ks_log = rec_rows_log`, X has 2^10 rows per column; else (P8) `ks_log = rec_rows_log + 1`, X has 2^rec
        let x_log = x_log(p.ks_log, p.rec_rows_log);
        let ks_split = ks_split(p.ks_log, p.rec_rows_log);
        let d_log = if small { layout::SMALL_LOG_N } else { p.log_n };
        let nu_main = if small { p.nu_main - 1 } else { p.nu_main };
        let (d_vars, ks_vars, s_vars) = (d_log + D_LOG, p.ks_log + SLOT_LOG, p.nu_rec());
        // R11 (M′, S2GM): `D` at word 0; `T` (2^20) at 2^22 (the big shape's `D` extent; the small shape's from
        // `2^22 − 3·2^20`), `KS` after it, the stream block `S` after `KS` (aligned to its 2^19 words), and inside `S`
        // after `σ'`: `KSY2`'s 11 lanes (aligned to `2^ks_log`), then the mini-bus's columns (`free_lo`)
        assert!(p.ks_log <= p.rec_rows_log, "S2GM: KS's message rows fit S's columns");
        let floor = if small { (1usize << 22) - SMALL_SHIFT } else { (1usize << d_vars).max(1 << 22) };
        assert!(1usize << d_vars <= floor, "D lies below the typed region");
        let t_off = floor;
        let ks_off = t_off + (1usize << T_VARS);
        let s_off = (ks_off + (1usize << ks_vars)).next_multiple_of(1 << s_vars);
        let ksy2 = s_off + ((REC_STREAM_COLS << p.rec_rows_log) + (1 << SIG_LOG)).next_multiple_of(1 << p.ks_log);
        let free_lo = ksy2 + ((LANES - KS_Y_IN_BLOCK) << p.ks_log);
        assert!(free_lo <= s_off + (1 << s_vars), "KSY2 lies in S");
        let (d_off, spare, x_off) = (0usize, ksy2, s_off + ks_split);
        let at = free_lo;
        let l = Self {
            log_n: p.log_n,
            ks_log: p.ks_log,
            rec_log: p.rec_rows_log,
            nu_main,
            nu_rec: p.nu_rec(),
            d_off,
            d_log,
            ks_off,
            t_off,
            ksy2_off: spare,
            x_off,
            s_off,
            x_log,
            ks_split,
            small,
            free_lo: at,
        };
        assert!(l.free_lo <= 1 << nu_main, "the layout fits C_main");
        // the rule's offsets are the shared layout's (`layout.rs`, generated with Lean's `LvmLayout` from params.py)
        let b = if small {
            assert_eq!(p.name, "P20", "the small shape is P20's");
            &layout::P20S
        } else {
            layout::of(p.name)
        };
        assert_eq!((b.nu_main, b.d_off, b.t_off, b.ks_off, b.ksy2_off, b.x_off, b.s_off, b.free_lo),
            (l.nu_main, l.d_off, l.t_off, l.ks_off, l.ksy2_off, l.x_off, l.s_off, l.free_lo), "layout.rs is this layout");
        if small {
            // CR-DES §1.4: every block from T up moves by the same 3·2^20; D_l keeps its rows < 2^18 at l·2^18
            let big = Self::shape(p, false);
            assert_eq!((big.t_off, big.ks_off, big.ksy2_off, big.x_off, big.s_off, big.free_lo),
                (l.t_off + SMALL_SHIFT, l.ks_off + SMALL_SHIFT, l.ksy2_off + SMALL_SHIFT, l.x_off + SMALL_SHIFT, l.s_off + SMALL_SHIFT, l.free_lo + SMALL_SHIFT));
            assert!(big.d_off == 0 && l.d_off == 0 && big.d_vars() == 22 && l.d_vars() == 20 && 4 << 20 == l.t_off + SMALL_SHIFT);
        }
        assert_eq!(l.t_off % (1 << T_VARS), 0);
        assert_eq!(l.d_off % (1 << d_vars), 0);
        assert_eq!(l.ks_off % (1 << ks_vars), 0);
        assert_eq!(l.ksy2_off % (1 << p.ks_log), 0);
        assert_eq!(l.s_off % (1 << s_vars), 0);
        assert_eq!(l.x_off % (1 << x_log), 0);
        l
    }
    pub fn d_vars(&self) -> usize {
        self.d_log + D_LOG
    }
    pub fn ks_vars(&self) -> usize {
        self.ks_log + SLOT_LOG
    }
    /// The `D` column of lane `l < 4` (`2^d_log` rows).
    pub fn d(&self, l: usize) -> usize {
        self.d_off + (l << self.d_log)
    }
    pub fn ks_slot(&self, s: usize) -> usize {
        self.ks_off + (s << self.ks_log)
    }
    pub fn ks_y(&self, l: usize) -> usize {
        if l < KS_Y_IN_BLOCK { self.ks_slot(KS_Y_SLOT + l) } else { self.ksy2_off + ((l - KS_Y_IN_BLOCK) << self.ks_log) }
    }
    /// `X_l` (S2GM: the rows `ks_split …` of `S`'s column `l`).
    pub fn x(&self, l: usize) -> usize {
        self.x_off + (l << self.rec_log)
    }
    /// The first word above the fixed blocks (`layout.rs`; v1: the end of `X`, which takes 32 columns of
    /// `2^rec`): where the recursion tables go.
    pub fn free_lo(&self) -> usize {
        self.free_lo
    }
    /// The stream block's column `c` (S2GM: the `C_main` word `S + c·2^rec_log`; the old `C_rec` column `c`).
    pub fn rec_col(&self, c: usize) -> usize {
        self.s_off + (c << self.rec_log)
    }
    /// The `C_main` word of the old `C_rec` word `w` (S2GM: `S + w`).
    pub fn rec_word(&self, w: usize) -> usize {
        assert!(w < 1 << self.nu_rec, "a word of the stream block");
        self.s_off + w
    }
}

/// Little-endian lanes of a digest.
pub fn digest_lanes(d: &Digest) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap()))
}

pub fn lanes_digest(l: &[u64]) -> Digest {
    let mut d = [0u8; 32];
    for i in 0..4 {
        d[8 * i..8 * i + 8].copy_from_slice(&l[i].to_le_bytes());
    }
    d
}

/// The chain table `CH`: `in_0 = Pad43(s)`, `in_{i+1} = Pad43(Y_i)` for `i + 1 < n`; S1 (BLUEPRINT2 §2.1, A9 deleted):
/// rows `≥ n` hold the zero input ([`Chain::run_gated`]). [`Chain::run`] is v1's walk to `2^log_n` rows, kept for tests.
pub struct Chain {
    pub shape: Shape,
    pub inputs: Vec<[u64; LANES]>,
    /// Lanes 0–3 of every row's output.
    pub y: Vec<[u64; 4]>,
}

impl Chain {
    #[allow(dead_code)]
    pub fn run(log_n: usize, s: &Digest) -> Self {
        Self::run_notify(log_n, s, 0, |_| {})
    }
    /// [`Chain::run`], calling `at_end(chainEnd s n_end)` as soon as row `n_end − 1` is done (`n_end = 0`: never).
    pub fn run_notify(log_n: usize, s: &Digest, n_end: usize, mut at_end: impl FnMut(Digest)) -> Self {
        let n = 1usize << log_n;
        let mut inputs = Vec::with_capacity(n);
        let mut y = Vec::with_capacity(n);
        let mut d = *s;
        for i in 0..n {
            let a = crate::keccak::chain_block(&d);
            inputs.push(a);
            let mut b = a;
            // P-QUICK lever 2: the vendored single-state permutation (AVX-512 tier: 247 ns against 480 ns for
            // `keccak.rs`'s scalar one; `kat keccak` checks that the two agree)
            crate::lv::primitives::hash::keccak_f(&mut b);
            let out = [b[0], b[1], b[2], b[3]];
            y.push(out);
            d = lanes_digest(&out);
            if i + 1 == n_end {
                at_end(d);
            }
        }
        Self { shape: Shape::new(n, TAPE_DEPTH), inputs, y }
    }
    /// S1 (BLUEPRINT2 §2.1; P-GATE): walk only the `n` live rows; rows `≥ n` hold the all-zero input and
    /// `Y = Keccak-f(0)[0..4)`. `explicit` keeps the zero inputs as written rows (the dense reference prover,
    /// whose proof must be byte-identical to the padded one); otherwise `inputs` has `n` rows and the GKR
    /// witness pads the rest with leanVM's padding block.
    pub fn run_gated(log_n: usize, s: &Digest, n: usize, explicit: bool) -> Self {
        Self::run_gated_notify(log_n, s, n, explicit, |_| {})
    }
    /// [`Chain::run_gated`], calling `at_end(chainEnd s n)` as soon as row `n − 1` is done (P-QUICK lever 3).
    ///
    /// P-FIX2: the walk is PORT-12's `chainwalk::walk` (the kernel chosen once before `ready`: lv `keccak_f`, or
    /// relay-echo's `avx512vl` chain kernel; the same rows either way). `LVM_CHAIN_REF=1`: the loop of
    /// [`Chain::run_gated_notify_ref`].
    pub fn run_gated_notify(log_n: usize, s: &Digest, n: usize, explicit: bool, mut at_end: impl FnMut(Digest)) -> Self {
        if std::env::var_os("LVM_CHAIN_REF").is_some() {
            return Self::run_gated_notify_ref(log_n, s, n, explicit, at_end);
        }
        let big = 1usize << log_n;
        if n == 0 {
            at_end(*s);
        }
        let (mut inputs, mut y) = crate::chainwalk::walk_cap(
            crate::chainwalk::select(),
            digest_lanes(s),
            n,
            n,
            if explicit { big } else { n },
            big,
            |h| at_end(lanes_digest(&h)),
        );
        let mut z = [0u64; LANES];
        crate::lv::primitives::hash::keccak_f(&mut z);
        y.resize(big, [z[0], z[1], z[2], z[3]]);
        if explicit {
            inputs.resize(big, [0u64; LANES]);
        }
        Self { shape: Shape::new(big, TAPE_DEPTH), inputs, y }
    }
    /// The walk before P-FIX2 (P-QUICK lever 2's loop), kept as the reference.
    pub fn run_gated_notify_ref(log_n: usize, s: &Digest, n: usize, explicit: bool, mut at_end: impl FnMut(Digest)) -> Self {
        let big = 1usize << log_n;
        let mut inputs = Vec::with_capacity(if explicit { big } else { n });
        let mut y = Vec::with_capacity(big);
        let mut d = *s;
        for _ in 0..n {
            let a = crate::keccak::chain_block(&d);
            inputs.push(a);
            let mut b = a;
            crate::lv::primitives::hash::keccak_f(&mut b);
            let out = [b[0], b[1], b[2], b[3]];
            y.push(out);
            d = lanes_digest(&out);
        }
        at_end(d);
        let mut z = [0u64; LANES];
        crate::lv::primitives::hash::keccak_f(&mut z);
        y.resize(big, [z[0], z[1], z[2], z[3]]);
        if explicit {
            inputs.resize(big, [0u64; LANES]);
        }
        Self { shape: Shape::new(big, TAPE_DEPTH), inputs, y }
    }
    /// `chainEnd s n` for `1 ≤ n ≤ 2^log_n`: lanes 0–3 of row `n − 1`.
    pub fn end(&self, n: usize) -> Digest {
        lanes_digest(&self.y[n - 1])
    }
}

/// The sponge table `KS`: per row `in_i[l] = cont_i·Y_{i−1}[l] + [l < 17]·Msg_l[i]` (`cont_0 = 0`).
pub struct Sponge {
    pub shape: Shape,
    pub inputs: Vec<[u64; LANES]>,
    pub outputs: Vec<[u64; LANES]>,
    pub cont: Vec<bool>,
    /// The messages, 17 lanes per row: rows `< ks_split` are `C_rec`'s stream columns, the rest `X`.
    pub msg: Vec<[u64; REC_STREAM_COLS]>,
}

/// `cont` (structured, BLUEPRINT §4.2): rows `1 … B−1` (the trace sponge, `B` blocks) and rows 1–31 of the
/// 32-row WOTS leaf group (KS rows `≥ ks_split`: 399 chain steps, 32 leaf rows, 16 path rows, leafStmt, nodeStmt;
/// KS14: `ks_split` = 15,360).
pub fn cont_column(ks_log: usize, rec_log: usize, blocks: usize) -> Vec<bool> {
    let mut c = vec![false; 1 << ks_log];
    let split = ks_split(ks_log, rec_log);
    assert!(blocks <= split, "the trace sponge fits the stream rows");
    assert!(crate::lvm::rec::UPPER_ROWS <= (1 << ks_log) - split, "the X rows fit");
    for i in 1..blocks {
        c[i] = true;
    }
    let leaf = split + 399;
    for j in 1..32 {
        c[leaf + j] = true;
    }
    c
}

impl Sponge {
    pub fn run(ks_log: usize, cont: Vec<bool>, msg: Vec<[u64; REC_STREAM_COLS]>) -> Self {
        let n = 1usize << ks_log;
        assert_eq!(msg.len(), n);
        let mut inputs = Vec::with_capacity(n);
        let mut outputs: Vec<[u64; LANES]> = Vec::with_capacity(n);
        for i in 0..n {
            let mut a = if cont[i] { outputs[i - 1] } else { [0u64; LANES] };
            for l in 0..REC_STREAM_COLS {
                a[l] ^= msg[i][l];
            }
            inputs.push(a);
            let mut b = a;
            crate::lv::primitives::hash::keccak_f(&mut b);
            outputs.push(b);
        }
        Self { shape: Shape::new(n, GKR_DEPTH), inputs, outputs, cont, msg }
    }
}

/// S2: write `D` (lanes 0–3 of every chain row's output; `z*[0..4)` on rows `≥ n`) into `C_main`. The tape's GKR
/// witness commits nothing (its inputs are virtual, BLUEPRINT2 §1.1): `Witness::generate_uncommitted`.
/// SH2-Z: the buffer holds `D`'s rows `< 2^d_log` only.
pub fn write_d(lay: &Layout, ch: &Chain, cmain: &mut [F64]) {
    for m in 0..4 {
        let o = lay.d(m);
        for (i, y) in ch.y.iter().take(1 << lay.d_log).enumerate() {
            cmain[o + i] = F64(y[m]);
        }
    }
}

/// Write `KS` (its committed lanes, its 25 `Y` lanes and the 17 message lanes in `S`) into `C_main`.
pub fn write_ks(lay: &Layout, ks: &Sponge, cmain: &mut [F64]) -> Witness {
    let n = 1usize << lay.ks_log;
    let w = Witness::generate(ks.shape, &ks.inputs, &mut cmain[lay.ks_off..lay.ks_off + 50 * n]);
    write_ks_lanes(lay, ks, cmain);
    w
}

/// The KS columns outside its GKR witness's slots `[ks_off, ks_off + 50·2^ks_log)`: its 25 `Y` lanes and the 17
/// message lanes (P-FIX: written before the witness, which [`write_ks`] writes, so that the recursion tables can be
/// built meanwhile). S2GM: the message lane `l` is `S`'s column `l`, all `2^ks_log` rows (the stream below `ks_split`,
/// the `X` messages from it, so `X_l = rec_col(l) + ks_split`).
pub fn write_ks_lanes(lay: &Layout, ks: &Sponge, cmain: &mut [F64]) {
    let (split, xr) = (lay.ks_split, 1usize << lay.x_log);
    assert_eq!(split + xr, ks.msg.len(), "KS rows: the stream rows, then the X rows");
    assert!(ks.msg.len() <= 1 << lay.rec_log, "the messages fit S's columns");
    for l in 0..LANES {
        let o = lay.ks_y(l);
        for (i, y) in ks.outputs.iter().enumerate() {
            cmain[o + i] = F64(y[l]);
        }
    }
    for l in 0..REC_STREAM_COLS {
        let o = lay.rec_col(l);
        debug_assert_eq!(lay.x(l), o + split);
        for (i, m) in ks.msg.iter().enumerate() {
            cmain[o + i] = F64(m[l]);
        }
    }
}
