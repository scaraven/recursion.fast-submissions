//! The parameter record and the schedule, transcribed from the Lean verifier (`LvmParams.lean`,
//! `LvmSchedule.lean` on lvm/VQ; WP-0's `ref/params.py`). The Lean `V_S` is normative; this copy is used
//! to build the WHIR configurations and to check, after every proof, that the prover produced exactly
//! the schedule's sizes (`piSize`, `qS`, the query lengths in order).

/// One queried oracle of a WHIR opening (`Level`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Level {
    pub level: usize,
    pub fold: usize,
    pub kappa: usize,
    pub rate: usize,
    pub height: usize,
    pub cap: usize,
    pub path: usize,
    pub t: usize,
    pub row: usize,
}

/// `udQueries sec R`: the least `t` with `(2^R + 1)^t · 2^sec ≤ 2^((R+1) t)`.
pub fn ud_queries(sec: usize, r: usize) -> usize {
    (1..).find(|&t| exact_ok(sec, r, t)).unwrap()
}

/// `(2^R + 1)^t · 2^sec ≤ 2^((R+1) t)` with a small big-integer.
fn exact_ok(sec: usize, r: usize, t: usize) -> bool {
    // base-2^32 limbs
    let mut x: Vec<u64> = vec![1];
    let mul = |x: &mut Vec<u64>, m: u64| {
        let mut carry = 0u64;
        for l in x.iter_mut() {
            let v = *l * m + carry;
            *l = v & 0xffff_ffff;
            carry = v >> 32;
        }
        while carry > 0 {
            x.push(carry & 0xffff_ffff);
            carry >>= 32;
        }
    };
    for _ in 0..t {
        mul(&mut x, (1u64 << r) + 1);
    }
    let bits = |x: &Vec<u64>| -> usize {
        let top = *x.last().unwrap();
        32 * (x.len() - 1) + (64 - top.leading_zeros() as usize)
    };
    // x · 2^sec ≤ 2^e  ⟺  x ≤ 2^(e - sec)
    let e = (r + 1) * t;
    if e < sec {
        return false;
    }
    let k = e - sec;
    let b = bits(&x);
    let popcount: u32 = x.iter().map(|l| l.count_ones()).sum();
    b <= k || (b == k + 1 && popcount == 1)
}

/// The levels of `spec`; `t` is `udQueries sec R`, or `ts[i]` when `ts` is non-empty (JB-VQP J1: `C_main` at the
/// Johnson radius, the query counts given by the record).
fn mk_levels(sec: usize, nu: usize, spec: &[(usize, usize, usize)], ts: &[usize]) -> Vec<Level> {
    assert!(ts.is_empty() || ts.len() == spec.len(), "one query count per level");
    let mut k = nu;
    spec.iter()
        .enumerate()
        .map(|(i, &(l, r, c))| {
            k -= l;
            let h = k + r;
            Level {
                level: i,
                fold: l,
                kappa: k,
                rate: r,
                height: h,
                cap: c,
                path: h - c,
                t: if ts.is_empty() { ud_queries(sec, r) } else { ts[i] },
                row: if i == 0 { 8 << l } else { 24 << l },
            }
        })
        .collect()
}

/// The levels with level 0's leaf narrowed to the stack's `occ` occupied lanes (`LvmParams.withRow0`).
fn with_row0(mut levels: Vec<Level>, occ: usize) -> Vec<Level> {
    // R11 (M′, S2GM): no C_rec commitment, so an empty level list stays empty
    if levels.is_empty() {
        return levels;
    }
    assert!(1 <= occ && occ <= 1 << levels[0].fold, "the occupied lanes are some of level 0's 2^ℓ");
    levels[0].row = 8 * occ;
    levels
}

/// The occupied lanes of a commitment's root: the words its level-0 leaf carries (`row / 8`).
pub fn occ_lanes(levels: &[Level]) -> usize {
    levels[0].row / 8
}

pub const GKR_DEPTH: usize = 12;
/// S2: the chain tape's GKR is one segment of 24 rounds (`Shape { log_n, 24 }`).
pub const TAPE_DEPTH: usize = 24;
/// `Pad43`'s digest offset in the state (`Λ`: digest bit `p` to state bit `8 + p`).
pub const PAD_SHIFT: usize = 8;
pub const SLOT_LOG: usize = 6;
pub const REC_STREAM_COLS: usize = 17;
pub const REC_COLS: usize = 32;
pub const POSITIONS_PER_ANSWER: usize = 8;
pub const BUS_BITS: usize = 4;
pub const RING_STAGES: usize = 6;
pub const K_BITS: usize = 64;
pub const LANES: usize = 25;
pub const LANE_BITS: usize = 5;
pub const PACK_BITS: usize = 5;
pub const PRODUCT_BITS: usize = 105;
pub const LOCAL_BITS: usize = 11;
pub const SEGMENT_BITS: usize = 1;
pub const E_BYTES: usize = 24;
pub const NODE_BYTES: usize = 32;
pub const SIG_BYTES: usize = 8 + 133 * 32 + 16 * 32;
/// The header up to `σ_leaf` (4,928 B); the accumulator `acc_in` (`D + 1` `E` scalars) follows (A23).
pub const HEADER_BASE: usize = HEADER_STMT + SIG_BYTES;
/// The header's fields before `σ_leaf` (`'S' pad[7] | b | vk | c_L | s | n | h`: 152 B).
pub const HEADER_STMT: usize = 8 + 8 + 32 + 32 + 32 + 8 + 32;

/// The header up to `acc_in` at the stage: [`HEADER_BASE`], or [`HEADER_STMT`] at S2GS (no `σ_leaf`).
pub fn header_base() -> usize {
    if FrontCfg::get().sigout { HEADER_STMT } else { HEADER_BASE }
}

/// `D = accVars`: the variables of the fixed-column polynomial `Φ` (A23; `LvmParams.accVars`), the table
/// point's `tableRounds` then the column index's `accLog = D − tableRounds`.
pub const ACC_VARS: usize = 43;

/// The header's length: [`HEADER_BASE`] + `acc_in` (`D + 1` scalars): 5,624 B (`LvmParams.headerBytes`).
pub fn header_bytes(p: &Params) -> usize {
    header_base() + acc_w() * (p.acc_d() + 1)
}

/// E2F: `D`, the accumulator's coordinates at the stage (43; S2GF's amendment 1: 44).
pub fn acc_vars() -> usize {
    let cfg = FrontCfg::get();
    if cfg.typed_t {
        ACC_VARS + 2
    } else if cfg.typed_x {
        ACC_VARS + 1
    } else {
        ACC_VARS
    }
}

/// E2F (S2GT): the bytes of one `acc_in` scalar in the header (16: an E2 value; else 24).
pub fn acc_w() -> usize {
    if FrontCfg::get().typed_t { 16 } else { E_BYTES }
}

/// The seed query's length: the first answer and the header from byte 8.
pub fn seed_len(p: &Params) -> usize {
    32 + header_bytes(p) - 8
}

/// The parameter record (`Params`).
#[derive(Clone, Debug)]
pub struct Params {
    pub name: &'static str,
    pub log_n: usize,
    pub ks_log: usize,
    pub bits_log: usize,
    pub nu_main: usize,
    pub rec_rows_log: usize,
    pub sec_bits: usize,
    /// PI-GRIND: grinding bits `g` at every WHIR level of both openings (0: none, the v1/S2 schedule). The query
    /// counts are `udQueries (sec − g) R`.
    pub grind: usize,
    pub main_levels: Vec<Level>,
    /// JB-VQP J1 (`whirLevelsJ`, JB-L §3): `C_main`'s opening takes one OOD sample on every level with a next
    /// level (after the next cap: `κ` samples, the value `y`, the intro polynomial's two scalars).
    pub main_ood: bool,
    pub rec_levels: Vec<Level>,
    /// J2P-VQP J2′: `C_rec`'s opening takes the OOD samples too (`cfgRec20Jp`, `LvmParams.recOod`).
    pub rec_ood: bool,
    pub bus_depth: usize,
    pub leafdec_reads: usize,
    pub table_rounds: usize,
    pub table_evals: usize,
    /// The header array `PUB`'s index among the sumcheck tables (A23: its value column is the one fixed
    /// column outside `Φ`; `LvmParams.pubTab`).
    pub pub_tab: usize,
}

impl Params {
    /// `D`, the variables of `Φ` (= [`ACC_VARS`]).
    pub fn acc_d(&self) -> usize {
        acc_vars()
    }
    /// `dk = D − tableRounds`: the batching challenges `κ` (`Params.accLog`).
    pub fn acc_log(&self) -> usize {
        ACC_VARS - self.table_rounds
    }
    pub fn nu_rec(&self) -> usize {
        self.rec_rows_log + 5
    }
    pub fn main_final_log(&self) -> usize {
        self.main_levels.last().unwrap().kappa
    }
    pub fn levels(&self, com: Com) -> &[Level] {
        match com {
            Com::Main => &self.main_levels,
            Com::Rec => &self.rec_levels,
        }
    }
    pub fn by_name(name: &str) -> Option<Params> {
        match name {
            "P20" | "p20" => Some(p20()),
            "P8" | "p8" => Some(p8()),
            _ => None,
        }
    }
}

/// `main` is the `C_main` levels, any number (S2: three, v1: four), in `refreeze2.py`'s form `[(fold, rate, cap), …]`;
/// `main_t` their query counts (`[]`: `udQueries (sec − g) R`), `main_ood` [`Params::main_ood`]; `rec_t`, `rec_ood`
/// the same for `C_rec` (J2′); `main_occ` and `rec_occ` the stacks' occupied lanes (`LvmParams.mkParams`'s `mainOcc`,
/// `recOcc`; Z2, after #17): level 0's leaf carries only those words, so its row is `8 · occ` bytes (the verifier
/// reads the other lanes as zero).
#[allow(clippy::too_many_arguments)]
fn mk(
    name: &'static str,
    log_n: usize,
    sec: usize,
    grind: usize,
    rec_rows_log: usize,
    nu_main: usize,
    main: impl AsRef<[(usize, usize, usize)]>,
    rec: impl AsRef<[(usize, usize, usize)]>,
    ks_log: usize,
    bits_log: usize,
    fb: (usize, usize, usize, usize),
    pub_tab: usize,
    main_t: impl AsRef<[usize]>,
    main_ood: bool,
    rec_t: impl AsRef<[usize]>,
    rec_ood: bool,
    main_occ: usize,
    rec_occ: usize,
) -> Params {
    assert!(grind <= 64 && grind < sec, "{name}: {grind} grinding bits (at most 64, and below sec = {sec})");
    Params {
        name,
        log_n,
        ks_log,
        bits_log,
        nu_main,
        rec_rows_log,
        sec_bits: sec,
        grind,
        main_levels: with_row0(mk_levels(sec - grind, nu_main, main.as_ref(), main_t.as_ref()), main_occ),
        main_ood,
        rec_levels: with_row0(mk_levels(sec - grind, rec_rows_log + 5, rec.as_ref(), rec_t.as_ref()), rec_occ),
        rec_ood,
        bus_depth: fb.0,
        leafdec_reads: fb.1,
        table_rounds: fb.2,
        table_evals: fb.3,
        pub_tab,
    }
}

/// R11 (M′, S2GM): no `C_rec` levels, no `C_rec` query counts.
const NO_REC: [(usize, usize, usize); 0] = [];
const NO_T: [usize; 0] = [];

/// PI-GRIND's grinding bits per set (`LVM_GRIND=std`): P20 14, P8 4.
pub const GRIND_P20: usize = 14;
pub const GRIND_P8: usize = 4;

/// The frozen records' grinding bits (`refreeze2.py` writes them; the default when `LVM_GRIND` is unset).
pub const FROZEN_GRIND_P20: usize = 14;
pub const FROZEN_GRIND_P8: usize = 4;
/// E2F: the trace's sponge blocks of the S2GF/S2GT records (`check::frozen_numbers`).
const BLOCKS_P8_S2GF: usize = 2124;
const BLOCKS_P20_S2GT: usize = 4288;
const BLOCKS_P8_S2GT: usize = 2118;
/// U-TAPE: the trace's sponge blocks of the S2GU P20 record (utape.py).
const BLOCKS_P20_S2GU: usize = 3961;
/// MBL: the trace's sponge blocks of the S2GL P20 record (variants.py MB-LIN).
const BLOCKS_P20_S2GL: usize = 3843;
/// SLF: the trace's sponge blocks of the S2GS P20 record (g0b.py "S2GL + sigma_leaf out"); lvm2 W32: +144 (U 47 -> 105
/// in each of the 24 tape layers, one pack round fewer).
pub const BLOCKS_P20_S2GS: usize = 3952;

/// PI-GRIND's switch: `LVM_GRIND` unset gives the frozen record's bits (`frozen`); `std` gives the set's grinding
/// bits ([`GRIND_P20`], [`GRIND_P8`]); empty or `0` gives none; a number `g` gives `g` bits at either set.
pub fn grind_env(std_bits: usize, frozen: usize) -> usize {
    match std::env::var("LVM_GRIND") {
        Err(_) => frozen,
        Ok(v) if v == "std" => std_bits,
        Ok(v) if v.is_empty() => 0,
        Ok(v) => v.parse().unwrap_or_else(|_| panic!("LVM_GRIND: std or a number of bits, not {v:?}")),
    }
}

/// `P20` (BLUEPRINT §3.1); the M3 numbers `(busDepth, leafdecReads, tableRounds, tableEvals)` are INT-2's
/// freeze (`LvmParams.P20`, A21). Grinding bits from `LVM_GRIND` ([`grind_env`]; the frozen record's by default).
pub fn p20() -> Params {
    p20_g(grind_env(GRIND_P20, FROZEN_GRIND_P20))
}

/// `P20` with `g` grinding bits.
pub fn p20_g(g: usize) -> Params {
    // R11 (M′, stage S2GM): one commitment, C_main at ν = 23, three levels; C_rec's old content is C_main's stream
    // block `S` (`rec_rows_log` 14: 17 columns of 2^14 and σ' in a 2^19 block). The root leaves carry C_main's 47
    // occupied lanes (the big shape: S's columns end in lane 46)
    // U-TAPE (S2GU): no KS block; the Y block's mini-bus columns end in lane 46, so the root leaves carry 46 lanes
    // (`LVM_UT_GTLAY=1`, dev: S2GT's layout, 47)
    let occ = if FrontCfg::get().utape && !ut_gtlay() { 46 } else { 47 };
    // (MBL, S2GL, lead decision D2: the record keeps the mini-bus's shape (12, 1, 6, 633), Lean's P20L; the stage flag
    // `mblin` alone drops the `tables` phase)
    mk("P20", 20, 129, g, 14, 23, [(6, 2, 8), (4, 3, 7), (4, 4, 7)], NO_REC, 13, 13, (12, 1, 6, 633), 0, [115, 77, 58], true, NO_T, false, occ, 0)
}

/// `P8` (WP-0's test set). Grinding bits from `LVM_GRIND` ([`grind_env`]; the frozen record's by default).
pub fn p8() -> Params {
    p8_g(grind_env(GRIND_P8, FROZEN_GRIND_P8))
}

/// `P8` with `g` grinding bits.
pub fn p8_g(g: usize) -> Params {
    // R11 (M′, S2GM): KS 2^14, one commitment (C_main, three levels); the stream block `S` after KS (lanes 48–51)
    mk("P8", 9, 20, g, 14, 23, [(6, 1, 4), (4, 2, 4), (4, 3, 4)], NO_REC, 14, 12, (11, 1, 5, 378), 0, [33, 17, 11], true, NO_T, false, 52, 0)
}

/// `p` with `C_main` and `C_rec` in the unique-decoding regime (PI-GRIND-P's S2G record): `t = udQueries (sec − g) R`,
/// no OOD (`LvmParams.P20G`/`P8G`).
pub fn ud_main(p: Params) -> Params {
    let sec = p.sec_bits - p.grind;
    let main_levels = p.main_levels.iter().map(|l| Level { t: ud_queries(sec, l.rate), ..*l }).collect();
    let rec_levels = p.rec_levels.iter().map(|l| Level { t: ud_queries(sec, l.rate), ..*l }).collect();
    Params { main_levels, main_ood: false, rec_levels, rec_ood: false, ..p }
}

// ------------------------------------------------------------------------------------------- the schedule

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Com {
    Main,
    Rec,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Item {
    Read(usize),
    /// E2F (S2GF): `m` E2 scalars, 16 bytes each
    Read16(usize),
    /// E2F: an E2 challenge's nonce, one 8-byte `K` word
    Nonce,
    Cap(usize, Com, usize),
    Sample,
    Positions(Com, usize),
    Opening(Com, usize),
}

// ------------------------------------------------------------------ E2F (S2GF): the front's items

/// E2F: the stage's front and pin (`LVM_STAGE`: `S2GF`: tape, wire, KS and KS link at E2, the root OOD pin, the typed
/// phases' coordinate split; `S2GF-NOKS`: KS and KS link stay E3; `S2GM` (the default until the refreeze): roll 11's
/// all-E3 front, no pin, byte-identical to roll 11).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrontCfg {
    pub tape_e2: bool,
    pub ks_e2: bool,
    pub pin: bool,
    /// amendment 1: the typed phases with the coordinate split (`ω`, 6 values, 8 matrix values, `Φ_Q` on 44
    /// variables: `κ` 3, `h` 45, `acc_in` 44 coordinates)
    pub typed_x: bool,
    /// S2GT (`s2gt.py`): the typed phases at E2 (swapped split, `Φ_Q` on 45 variables, the header's `acc_in` as 46
    /// E2 scalars of 16 bytes); the mini-bus stays E3
    pub typed_t: bool,
    /// U-TAPE (stage S2GU, `utape.py`): KS merged into the tape at E2 (the 21-variable tape, T1 in B1 order, the wire
    /// with the sponge terms and the D/Y/M slot reductions; KS and KS link deleted; layout S2GU, occupancy 46)
    pub utape: bool,
    /// MBL (stage S2GL, MB-LIN): the mini-bus's table phase deleted (no `ξ`, no table rounds, no evaluations): its
    /// three trees' final GKR claims become three K-linear claims on `C_main` (the record keeps (12, 1, 6, 633): D2)
    pub mblin: bool,
    /// SLF (stage S2GS, σ_LEAF): the header has no `σ_leaf` (`'S' pad[7] | b | vk | c_L | s | n | h | acc_in`, 888 B
    /// at P20): every header offset after `h` moves down by `SIG_BYTES` (4,776 B, 597 lanes); `σ_leaf`'s 597 words
    /// sit in `C_main`'s window and the node circuit walks them
    pub sigout: bool,
}

/// U-TAPE (dev, timing only): `LVM_UT_GTLAY=1` runs stage S2GU on S2GT's layout and blob (the Y block is the old KS
/// block's slots 0–24, written as a copy; occupancy 47). The proofs are S2GU-shaped but no `V_S` accepts them.
pub fn ut_gtlay() -> bool {
    std::env::var("LVM_UT_GTLAY").is_ok_and(|v| v == "1")
}

impl FrontCfg {
    pub fn get() -> Self {
        // (`S2GF-B`, dev: S2GF's front and pin over S2GM's typed phases, for the old blobs)
        match std::env::var("LVM_STAGE").as_deref() {
            // (S2GM: roll 11's stage; at P20 it needs roll 11's blob dir, `LVM_TYPED_DIR`)
            Ok("S2GM") => FrontCfg { tape_e2: false, ks_e2: false, pin: false, typed_x: false, typed_t: false, utape: false, mblin: false, sigout: false },
            Ok("S2GF-B") => FrontCfg { tape_e2: true, ks_e2: true, pin: true, typed_x: false, typed_t: false, utape: false, mblin: false, sigout: false },
            // (dev, timing only: S2GF-B without the pin)
            Ok("S2GF-B-NOPIN") => FrontCfg { tape_e2: true, ks_e2: true, pin: false, typed_x: false, typed_t: false, utape: false, mblin: false, sigout: false },
            Ok("S2GF-NOKS") => FrontCfg { tape_e2: true, ks_e2: false, pin: true, typed_x: true, typed_t: false, utape: false, mblin: false, sigout: false },
            // (S2GF: #22's stage; at P20 it needs blob v4's dir, `LVM_TYPED_DIR`)
            Ok("S2GF") => FrontCfg { tape_e2: true, ks_e2: true, pin: true, typed_x: true, typed_t: false, utape: false, mblin: false, sigout: false },
            // (S2GT: halved-phi's stage, blob GT)
            Ok("S2GT") => FrontCfg { tape_e2: true, ks_e2: true, pin: true, typed_x: false, typed_t: true, utape: false, mblin: false, sigout: false },
            // (S2GU, U-TAPE's stage: S2GT's typed phases with KS merged into the tape)
            Ok("S2GU") => FrontCfg { tape_e2: true, ks_e2: true, pin: true, typed_x: false, typed_t: true, utape: true, mblin: false, sigout: false },
            // (S2GL, MBL's stage: S2GU without the mini-bus's table phase)
            Ok("S2GL") => FrontCfg { tape_e2: true, ks_e2: true, pin: true, typed_x: false, typed_t: true, utape: true, mblin: true, sigout: false },
            // (unset: S2GS, SLF's stage: S2GL without σ_leaf in the header (888 B at P20); σ_leaf goes to C_main's window)
            Ok("S2GS") | Err(_) => FrontCfg { tape_e2: true, ks_e2: true, pin: true, typed_x: false, typed_t: true, utape: true, mblin: true, sigout: true },
            Ok(s) => panic!("LVM_STAGE={s}: S2GS, S2GL, S2GU, S2GT, S2GF, S2GF-NOKS, S2GF-B or S2GM"),
        }
    }
}

/// E2F: the front's items in a field (`s2gf.py`'s `Sched` with `front = "E2"`): at E2 every read is 16 bytes and every
/// challenge `[separator] nonce sample`, the separator before the front's first E2 challenge and before every `s`.
struct Front {
    v: Vec<Item>,
    e2: bool,
    started: bool,
}

impl Front {
    fn rd(&mut self, m: usize) {
        if m > 0 {
            self.v.push(if self.e2 { Item::Read16(m) } else { Item::Read(m) });
        }
    }
    /// `n` challenges (`s`: the layer's `s`, which takes a separator).
    fn ch(&mut self, n: usize, s: bool) {
        for _ in 0..n {
            if self.e2 {
                if !self.started || s {
                    self.v.push(Item::Sample);
                }
                self.started = true;
                self.v.push(Item::Nonce);
            }
            self.v.push(Item::Sample);
        }
    }
    /// Plain `E` samples (the ring maps).
    fn smp(&mut self, n: usize) {
        self.v.extend(smp(n));
    }
    fn sumcheck(&mut self, rounds: usize, d: usize) {
        for _ in 0..rounds {
            self.rd(d);
            self.ch(1, false);
        }
    }
    fn layer(&mut self, point: usize) {
        self.rd(PRODUCT_BITS);
        self.ch(1, true);
        self.sumcheck(point, 2);
        self.sumcheck(LOCAL_BITS, 3);
        self.rd(3);
        self.ch(1, false);
    }
    fn take(&mut self) -> Vec<Item> {
        std::mem::take(&mut self.v)
    }
}

/// E2F: the front's phases (tape, wire, KS, KS link) at `cfg`.
fn front_phases(p: &Params, cfg: FrontCfg) -> Vec<(Phase, Vec<Item>)> {
    let mut f = Front { v: Vec::new(), e2: cfg.tape_e2, started: false };
    let ring = |f: &mut Front| f.smp(if f.e2 { ROW_STAGES } else { RING_STAGES });
    // tape
    f.ch(p.log_n, false);
    f.rd(LANES);
    f.ch(LANE_BITS, false);
    for _ in 0..TAPE_DEPTH {
        f.layer(p.log_n - PACK_BITS);
    }
    let tape = f.take();
    // wire
    f.sumcheck(p.log_n, 2);
    f.rd(1);
    f.sumcheck(2, 2);
    f.rd(K_BITS);
    ring(&mut f);
    let wire = f.take();
    // KS
    f.e2 = cfg.ks_e2;
    f.ch(p.ks_log, false);
    f.rd(LANES);
    f.ch(SEGMENT_BITS + LANE_BITS, false);
    f.rd(1);
    for _ in 0..GKR_DEPTH {
        f.layer(p.ks_log - PACK_BITS + SEGMENT_BITS);
    }
    f.sumcheck(SLOT_LOG, 2);
    f.rd(1);
    f.sumcheck(PACK_BITS, 2);
    f.sumcheck(SLOT_LOG, 2);
    f.rd(K_BITS);
    ring(&mut f);
    let ks = f.take();
    // KS link
    f.ch(p.ks_log + LANE_BITS, false);
    f.sumcheck(p.ks_log, 2);
    f.rd(4);
    let link = f.take();
    vec![(Phase::Tape, tape), (Phase::Wire, wire), (Phase::Ks, ks), (Phase::KsLink, link)]
}

/// U-TAPE (stage S2GU, `utape.py`'s `front_utape`): the tape (T1 in B1 order: `r_<20`, the 50 scalars, `r_20`; T2 on
/// `2^21` rows) and the wire (T3: 20 rounds, `g_D, g_Y, g_M`; T4: the `D`, `Y` and `M` slot reductions, each its
/// rounds, 64 slices and the row switch's samples). KS and KS link are gone.
fn front_phases_u(p: &Params) -> Vec<(Phase, Vec<Item>)> {
    let mut f = Front { v: Vec::new(), e2: true, started: false };
    f.ch(p.log_n, false);
    f.rd(2 * LANES);
    f.ch(1, false);
    f.ch(LANE_BITS, false);
    for _ in 0..TAPE_DEPTH {
        f.layer(p.log_n + 1 - PACK_BITS);
    }
    let tape = f.take();
    f.sumcheck(p.log_n, 2);
    f.rd(3);
    for b in [2, UT_Y_SLOTS_LOG, UT_M_SLOTS_LOG] {
        f.sumcheck(b, 2);
        f.rd(K_BITS);
        f.smp(ROW_STAGES);
    }
    let wire = f.take();
    vec![(Phase::Tape, tape), (Phase::Wire, wire)]
}

/// U-TAPE: the `Y` block's slots (`2^5`: lanes 0–24 used) and the stream block `S`'s columns (`2^5`: 0–16 the messages).
pub const UT_Y_SLOTS_LOG: usize = 5;
pub const UT_M_SLOTS_LOG: usize = 5;

/// E2F (S2GF): the row switch's ring-map samples.
pub const ROW_STAGES: usize = 7;

fn rd(m: usize) -> Vec<Item> {
    if m == 0 { vec![] } else { vec![Item::Read(m)] }
}
fn smp(n: usize) -> Vec<Item> {
    vec![Item::Sample; n]
}
fn sumcheck_i(rounds: usize, d: usize) -> Vec<Item> {
    (0..rounds).flat_map(|_| [rd(d), vec![Item::Sample]].concat()).collect()
}
fn keccak_layer_i(point: usize) -> Vec<Item> {
    [rd(PRODUCT_BITS), smp(1), sumcheck_i(point, 2), sumcheck_i(LOCAL_BITS, 3), rd(3), smp(1)].concat()
}
fn tape_layers_i(log_n: usize) -> Vec<Item> {
    (0..TAPE_DEPTH).flat_map(|_| keccak_layer_i(log_n - PACK_BITS)).collect()
}
fn keccak_i(log_steps: usize) -> Vec<Item> {
    let mut v = [smp(SEGMENT_BITS + LANE_BITS), rd(1)].concat();
    for _ in 0..GKR_DEPTH {
        v.extend(keccak_layer_i(log_steps - PACK_BITS + SEGMENT_BITS));
    }
    v.extend([sumcheck_i(SLOT_LOG, 2), rd(1), sumcheck_i(PACK_BITS, 2), sumcheck_i(SLOT_LOG, 2), rd(K_BITS)].concat());
    v
}
fn gp_layers_i(layer: usize, point: usize) -> Vec<Item> {
    if layer == 0 {
        return vec![];
    }
    let step = if layer % 2 == 1 { 1 } else { 2 };
    let mut v = smp(1);
    for _ in 0..point {
        v.extend(rd(1 << step));
        v.extend(smp(1));
    }
    v.extend(rd(3 << step));
    v.extend(smp(step));
    v.extend(gp_layers_i(layer - step, point + step));
    v
}
fn tail_i(n: usize) -> Vec<Item> {
    let mut v = vec![];
    for j in 0..n {
        v.push(Item::Sample);
        if j + 1 < n {
            v.push(Item::Read(2));
        }
    }
    v
}
/// PI-GRIND: a level's separating sample, nonce and PoW sample (none when `g = 0`).
fn grind_i(g: usize) -> Vec<Item> {
    if g == 0 { vec![] } else { [smp(1), rd(1), smp(1)].concat() }
}
fn whir_i(com: Com, levels: &[Level], final_log: usize, g: usize, ood: bool) -> Vec<Item> {
    let mut v = rd(2);
    for (i, l) in levels.iter().enumerate() {
        for _ in 0..l.fold {
            v.extend(smp(1));
            v.extend(rd(2));
        }
        let next = levels.get(i + 1);
        match next {
            None => v.extend(rd(1 << final_log)),
            Some(n) => {
                v.push(Item::Cap(n.cap, com, l.level + 1));
                if ood {
                    // JB-L §3: the OOD point (κ samples, κ = the folded message's variables), `y`, the intro poly
                    v.extend(smp(l.kappa));
                    v.extend(rd(1));
                    v.extend(rd(2));
                }
            }
        }
        v.extend(grind_i(g));
        v.push(Item::Positions(com, l.level));
        v.extend(smp(1));
        v.push(Item::Opening(com, l.level));
        v.extend(rd(2));
        if next.is_none() {
            v.extend(tail_i(final_log));
        }
    }
    v
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Commit,
    Bus,
    Tables,
    /// A23 phase 3b: `κ` (dk samples), `h` (D + 1), `t`, one zero scalar.
    Acc,
    /// S2: T1 (output claim) and T2 (the depth-24 GKR) on the chain digests `D`.
    Tape,
    /// S2: T3 (wiring sumcheck) and T4 (`D` slot reduction, ring switch).
    Wire,
    Ks,
    KsLink,
    OpenRec,
    OpenMain,
}

pub fn phases(p: &Params) -> Vec<(Phase, Vec<Item>)> {
    let cfg = FrontCfg::get();
    // E2F (S2GF): the root OOD pin after the cap: `ν` samples, one `E` read
    let pin: Vec<Item> = if cfg.pin { [smp(p.nu_main), rd(1)].concat() } else { vec![] };
    let mut out = vec![
        // R11 (M′, S2GM): one commitment, one root cap
        (Phase::Commit, [vec![Item::Cap(p.main_levels[0].cap, Com::Main, 0)], pin].concat()),
        // lvm2 roll 8 (B1, `LvmSchedule.phases` at S2GB1 = `LvmTypedVSched.phasesT`): `bus` carries the typed phases
        // (zerocheck: τ, 20 equality rounds of 2, a*, b*, c*; wiring: γ, 21 rounds of 2, the 4 + 4 values; relayout:
        // 19 rounds of 2, v_R; A23 at Φ_Q: κ (2), h (D + 1), t, the zero scalar), then the mini-bus's grand product;
        // `tables` is the mini-bus's table sumcheck
        (
            Phase::Bus,
            [
                smp(20),
                // E2F amendment 1: `ω`, the 6 values, the 8 matrix values, `κ` (3)
                smp(usize::from(cfg.typed_x)),
                sumcheck_i(20, 2),
                rd(if cfg.typed_x { 6 } else { 3 }),
                smp(1),
                sumcheck_i(21, 2),
                rd(if cfg.typed_x { 8 } else { 4 }),
                rd(4),
                sumcheck_i(19, 2),
                rd(1),
                smp(if cfg.typed_x { 3 } else { 2 }),
                rd(p.acc_d() + 1),
                smp(1),
                rd(1),
                smp(BUS_BITS + 1),
                rd(2),
                gp_layers_i(p.bus_depth, 0),
                rd(p.leafdec_reads),
            ]
            .concat(),
        ),
        (Phase::Tables, [smp(1), sumcheck_i(p.table_rounds, 3), rd(p.table_evals)].concat()),
    ];
    // MBL (S2GL, D2): no `tables` phase (the bus's trailing zero is followed by the front's first item); the record's
    // table numbers stay as shape facts
    if cfg.mblin {
        out.pop();
    }
    if cfg.typed_t {
        // S2GT (`s2gt.py` + amendments 1–2): the typed phases at E2, every challenge its own nonce, the separator
        // before the first; the mini-bus stays E3 (S2GF's items)
        let mut f = Front { v: Vec::new(), e2: true, started: false };
        f.ch(20, false);
        f.ch(1, false);
        f.sumcheck(20, 2);
        f.rd(9);
        f.ch(1, false);
        f.sumcheck(21, 2);
        f.rd(12);
        f.rd(4);
        f.sumcheck(19, 2);
        f.rd(1);
        f.ch(4, false);
        f.rd(p.acc_d() + 1);
        f.ch(1, false);
        f.rd(1);
        let mut bus = f.take();
        bus.extend([smp(BUS_BITS + 1), rd(2), gp_layers_i(p.bus_depth, 0), rd(p.leafdec_reads)].concat());
        out[1] = (Phase::Bus, bus);
    }
    if cfg.utape {
        out.extend(front_phases_u(p));
    } else if cfg.tape_e2 || cfg.ks_e2 {
        out.extend(front_phases(p, cfg));
    } else {
        out.extend([
            (Phase::Tape, [smp(p.log_n), rd(LANES), smp(LANE_BITS), tape_layers_i(p.log_n)].concat()),
            (Phase::Wire, [sumcheck_i(p.log_n, 2), rd(1), sumcheck_i(2, 2), rd(K_BITS), smp(RING_STAGES)].concat()),
            (Phase::Ks, [smp(p.ks_log), rd(LANES), keccak_i(p.ks_log), smp(RING_STAGES)].concat()),
            (Phase::KsLink, [smp(p.ks_log + LANE_BITS), sumcheck_i(p.ks_log, 2), rd(4)].concat()),
        ]);
    }
    out.push((Phase::OpenMain, [smp(1), whir_i(Com::Main, &p.main_levels, p.main_final_log(), p.grind, p.main_ood)].concat()));
    out
}

pub fn schedule(p: &Params) -> Vec<Item> {
    phases(p).into_iter().flat_map(|(_, v)| v).collect()
}

/// The query classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QClass {
    Q0,
    Seed,
    Fs,
    Leaf,
    Node,
}

/// The query sequence (`queryList`): class and length of every query `V_S` asks.
pub fn query_list(p: &Params) -> Vec<(QClass, usize)> {
    let mut out = vec![(QClass::Q0, 7), (QClass::Seed, seed_len(p))];
    let mut pend = 0usize;
    for it in schedule(p) {
        match it {
            Item::Read(m) => pend += E_BYTES * m,
            Item::Read16(m) => pend += 16 * m,
            Item::Nonce => pend += 8,
            Item::Cap(c, _, _) => pend += NODE_BYTES << c,
            Item::Sample => {
                out.push((QClass::Fs, 32 + pend));
                pend = 0;
            }
            Item::Positions(com, lv) => {
                let l = p.levels(com)[lv];
                let n = l.t.div_ceil(POSITIONS_PER_ANSWER);
                out.push((QClass::Fs, 32 + pend));
                pend = 0;
                for _ in 1..n {
                    out.push((QClass::Fs, 32));
                }
            }
            Item::Opening(com, lv) => {
                let l = p.levels(com)[lv];
                for _ in 0..l.t {
                    out.push((QClass::Leaf, l.row));
                    for _ in 0..l.path {
                        out.push((QClass::Node, 64));
                    }
                }
            }
        }
    }
    out
}

/// S2 dev check: `piSize`, `qS` and trace sponge blocks against `2^rec`, for P20 and P8: the frozen records (J1:
/// `C_main` at the Johnson radius with OOD, at `FROZEN_GRIND_*`), then `C_main` in UD at PI-GRIND's bits and without
/// grinding (with the query counts `t` and the positions queries `Σ ⌈t/8⌉`).
pub fn print_numbers() {
    for p in [
        p20_g(FROZEN_GRIND_P20),
        p8_g(FROZEN_GRIND_P8),
        ud_main(p20_g(GRIND_P20)),
        ud_main(p8_g(GRIND_P8)),
        ud_main(p20_g(0)),
        ud_main(p8_g(0)),
    ] {
        let ql = query_list(&p);
        let l: usize = 1 + ql.iter().map(|(_, len)| 40 + len).sum::<usize>();
        let ts: Vec<usize> = p.rec_levels.iter().chain(&p.main_levels).map(|l| l.t).collect();
        let pos: usize = ts.iter().map(|t| t.div_ceil(POSITIONS_PER_ANSWER)).sum();
        println!(
            "{} g {} main_ood {} rec_ood {} piSize {} qS {} t (rec; main) {:?} positions queries {} trace blocks {} (2^rec = {})",
            p.name, p.grind, p.main_ood, p.rec_ood, pi_size(&p), ql.len(), ts, pos, l / 136 + 1, 1usize << p.rec_rows_log
        );
    }
}

/// The trace's bytes (`traceBytes`: `0x54`, then `enc64 |q| ‖ q ‖ a` per query).
pub fn trace_len(p: &Params) -> usize {
    1 + query_list(p).iter().map(|(_, len)| 40 + len).sum::<usize>()
}

/// The length rule (`LvmSchedule.lengthRule`): the seed's length is not a node's (64), a leaf's ([`LEAF_LENS`]) or 32,
/// and no Fiat–Shamir query has a reserved length or the seed's.
pub fn length_rule(p: &Params) -> bool {
    let lens = crate::lv::fiat_shamir::transcript::LEAF_LENS;
    let reserved = |n: usize| n == 64 || lens.contains(&n);
    let seed = seed_len(p);
    !reserved(seed) && seed != 32 && query_list(p).iter().all(|&(c, n)| c != QClass::Fs || (!reserved(n) && n != seed))
}

/// `piSize`.
pub fn pi_size(p: &Params) -> usize {
    let mut s = header_bytes(p);
    for it in schedule(p) {
        match it {
            Item::Read(m) => s += E_BYTES * m,
            Item::Read16(m) => s += 16 * m,
            Item::Nonce => s += 8,
            Item::Cap(c, _, _) => s += NODE_BYTES << c,
            Item::Opening(com, lv) => {
                let l = p.levels(com)[lv];
                s += l.t * (l.row + l.path * NODE_BYTES);
            }
            _ => {}
        }
    }
    s
}

/// The frozen numbers' checks (`lvm-prover s2check`: the crate's `cargo test` does not build the vendored tests).
pub mod check {
    use super::*;

    pub fn frozen_numbers() {
        // the frozen records (`refreeze2.py` writes their numbers and `FROZEN_GRIND_*`); `grind_numbers` names its
        // sets `pg`/`qg` so that refreeze2's rewrites of `p`/`q` do not reach them
        let p = p20_g(FROZEN_GRIND_P20);
        assert_eq!(p.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![115, 77, 58]);
        // R11 (M′, S2GM): one commitment
        assert!(p.rec_levels.is_empty() && !p.rec_ood);
        let utape = FrontCfg::get().utape;
        assert_eq!(occ_lanes(&p.main_levels), if utape && !ut_gtlay() { 46 } else { 47 });
        let q = p8_g(FROZEN_GRIND_P8);
        assert_eq!(q.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![33, 17, 11]);
        assert!(q.rec_levels.is_empty() && !q.rec_ood);
        // JB-VQP J1: C_main's OOD (P20 κ 18, 14; P8 κ 17, 13) and the trace's sponge blocks
        assert!(p.main_ood && q.main_ood);
        let blocks = |p: &Params| (1 + query_list(p).iter().map(|(_, len)| 40 + len).sum::<usize>()) / 136 + 1;
        let got = |p: &Params| (query_list(p).len(), pi_size(p), blocks(p));
        // per stage at C_main occupancy 47: (P20 qS, |π|, blocks), (P8 qS, |π|, blocks). S2GM: R11 G0's model at 47
        // (340,328 B); E2F S2GF: s2gf-items.tsv (P20) and LvmScheduleF's piSizeF/qSF P8 44 (P8); S2GT: s2gt.py at 47
        let want = match std::env::var("LVM_STAGE").as_deref() {
            Ok("S2GF") => ((3959, 306992, 4295), (1900, 153968, BLOCKS_P8_S2GF)),
            Ok("S2GT") => ((3961, 305992, BLOCKS_P20_S2GT), (1902, 152968, BLOCKS_P8_S2GT)),
            // U-TAPE (utape.py at occupancy 46; P8 is not an S2GU set: its numbers here are only the schedule's)
            // MBL (variants.py MB-LIN at occupancy 46: the S2GU record less the table phase)
            // SLF (g0b.py "S2GL + sigma_leaf out": header 888 B, trace 517,752 B)
            Ok("S2GS") | Err(_) if !ut_gtlay() => {
                assert_eq!(header_bytes(&p), 888, "S2GS header");
                // lvm2 W32 (K = 32: U 105 coefficients, one pack round fewer a layer): |π| +21,312 B, qS −24 (W32-G0 §6 item 5)
                assert_eq!(got(&p), (3618, 284872, BLOCKS_P20_S2GS), "S2GS P20 at K = 32 (g0b.py S2GL + sigma_leaf out, W32)");
                assert_eq!(trace_len(&p), 537336, "S2GS P20 trace bytes (W32: +19,584)");
                assert!(length_rule(&p), "S2GS P20 length rule");
                return;
            }
            Ok("S2GL") if !ut_gtlay() => {
                assert_eq!(got(&p), (3642, 268336, BLOCKS_P20_S2GL), "S2GL P20 (variants.py MB-LIN)");
                assert!(length_rule(&p), "S2GL P20 length rule");
                return;
            }
            Ok("S2GU") if !ut_gtlay() => {
                assert_eq!(got(&p), (3649, 283960, BLOCKS_P20_S2GU), "S2GU P20 (utape.py)");
                return;
            }
            Ok("S2GU") | Ok("S2GL") | Ok("S2GS") | Err(_) => {
                assert_eq!(got(&p).0, 3649, "S2GU P20 on S2GT's layout: qS");
                return;
            }
            Ok("S2GM") => ((3895, 332336, 4447), (1836, 177288, 2262)),
            Ok(s) => panic!("frozen_numbers: no record for LVM_STAGE={s}"),
        };
        assert_eq!((got(&p), got(&q)), want);
    }

    pub fn grind_numbers() {
        // (the PI-GRIND dev records are S2GM's; the E2F stages have none)
        if std::env::var("LVM_STAGE").map_or(true, |s| s != "S2GM") {
            return;
        }
        // PI-GRIND Gate §3: t = udQueries (129 − 14) R (C_main in UD, the S2G record)
        let pg = ud_main(p20_g(GRIND_P20));
        assert_eq!(pg.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![170, 139, 127]);
        // PI-GRIND-P's record at g > 0 (dev `s2check`; R11, S2GM: one commitment)
        assert_eq!((query_list(&pg).len(), pi_size(&pg)), (5651, 453640));
        let qg = ud_main(p8_g(GRIND_P8));
        assert_eq!(qg.main_levels.iter().map(|l| l.t).collect::<Vec<_>>(), vec![39, 24, 20]);
        assert_eq!((query_list(&qg).len(), pi_size(&qg)), (2062, 193240));
    }

    pub fn s2gm_layout() {
        // R11 (S2GM): the rule's offsets are layout.rs's (asserted in `Layout::shape`), and S holds σ′, KSY2, free_lo
        use crate::lvm::tables::Layout;
        if FrontCfg::get().utape && !ut_gtlay() {
            // U-TAPE (S2GU, P20 only): S at lane 40, σ′ in S's column 17, the Y block after S, free_lo after Y's 25 lanes
            let l = Layout::new(&p20());
            assert_eq!((l.s_off, l.y_off, l.free_lo()), (5242880, 5767168, 5971968));
            assert_eq!(l.x(3), l.rec_col(3) + l.ks_split);
            assert_eq!(l.ks_y(24), l.y_off + (24 << 13));
            let s = Layout::shape(&p20(), true);
            assert_eq!((s.s_off, s.y_off, s.free_lo()), (2097152, 2621440, 2826240));
            return;
        }
        for p in [p20(), p8()] {
            let l = Layout::new(&p);
            assert_eq!(l.rec_col(17), l.s_off + (17 << 14));
            assert!(l.ksy2_off >= l.rec_col(17) + (1 << crate::lvm::tables::SIG_LOG) && l.free_lo() <= l.s_off + (1 << 19));
            assert_eq!(l.x(3), l.rec_col(3) + l.ks_split);
        }
        let s = Layout::shape(&p20(), true);
        assert_eq!(s.s_off, 2621440);
        // the window (Lvm.X.winLo = 40, winC = 8; lanes of 2^17 physical words): the stream and σ′ in lanes 40–47
        let len = (17 << 14) + (1 << crate::lvm::tables::SIG_LOG);
        let big = Layout::new(&p20()).s_off;
        assert!(big >= 40 << 17 && big + len <= 48 << 17);
        assert!(2 * s.s_off >= 40 << 17 && 2 * (s.s_off + len) <= 48 << 17);
    }
}
