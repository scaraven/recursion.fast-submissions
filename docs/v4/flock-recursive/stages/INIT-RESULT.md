# INIT RESULT: the badge's start-up

Track INIT, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`. Started at `9249a56`;
re-snapshotted onto `ae8b8d8` (ASK-T), `91e0d61` (IMPC2) and **`407260d` (REPF)**, which is the final state
measured here. Build trees: `logs/fr-build-INIT` (HEAD + INIT's files) and `logs/fr-build-INIT0` (HEAD
alone, for the A/B). Logs: `logs/INIT/`. Nothing is committed.

## 0. Verdict

- **The start-up is 12–13 s shorter at every HEAD I measured, with bit-identical outputs.** `start0` is
  the badge's import closure (`import Solution`, an empty `main`). User time, VM, one pinned core,
  alternating A/B:

  | HEAD | HEAD alone | HEAD + INIT | cut | log |
  |---|---|---|---|---|
  | `ae8b8d8` | 17.8–19.1 s | 7.05–7.47 s | −11.3 s (−61 %) | `ab-start0.log` |
  | `91e0d61`, plus the fused-plan prototype (§3.1) | 18.1–18.4 s | **6.14–6.40 s** | −12.0 s (−66 %) | `ab-start0-fuse2.log` |
  | **`407260d`** (REPF's replay fold) | 30.1–31.0 s | **17.3–18.3 s** | −12.8 s | `ab-start0-407.log` |

- **The ≤ 6 s VM target was within reach before REPF landed: 6.1–6.4 s with my edits plus the fusion
  prototype.** REPF then added about 12 s, all of it inside `planOf4D` (the replay rows: `arRepOf`/
  `trailMR`, `kRows`, grouping, `repFitB`). That code is CF's now. §3 lists the measured costs in it,
  including a 1.9 s trap: a `2^40` literal parsed from a string inside the loops.
- **The outputs are equal.** Each replaced definition is proved equal. On top of that, a fingerprint
  probe (`initfp`) hashes the six programs' ops (π offsets and register arguments), `progSegG`,
  `protoProg 0`, the node plan's pieces, shared forms, ask rows and **replay rows (845,862 + 8)**,
  `Impl.nodePlan`, and `chTab4 seq4 456`. The hashes are identical between HEAD and HEAD + INIT
  (`fp-base5.log` = `fp-init5.log` at `407260d`; also at `ae8b8d8` and `91e0d61`).
- **V per check is unchanged** (the programs are the same ops). V(N4) `runSeq`, 11 runs, best/median:
  HEAD 1,860.7/1,939.8 ms, INIT 1,871.8/1,961.2 ms (`vtime4-base.log`, `vtime4-init.log`; the two ran
  concurrently on two cores). The in-process program build (`collect`) dropped from 2,632 to 2,066 ms.
- **Nothing was made lazy.** `inituse.log`: every program (segments too) has one `evalM`, so
  `Impl.nodePlan` is live at run time. A lazy plan would land in a check: the DoS column, or `V_i`.
- **Statements.** `evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX`, the plan's `_eq` lemmas, `V4F_eq` and every
  other theorem statement are unchanged. Definitions changed: `chTab4`, `tabEnt4` (via `tabEntM`),
  `genPhase4`/`genPhaseG` (`let`s only), `finOps4`, `inputKindsF`, `tinRPu`, `eqTblG`, and `kt`
  (`@[noinline]`). Each comes with an equality lemma or is definitionally the old one (§2).
- **Checks.**
  - `lake build FR Solution FRSubmission4Fin` is green at `407260d` + INIT (`build-8.log`, 5,242 jobs).
  - `plan4t check` reported N2/N4/N8 `equal true` at `91e0d61` + edits 1–4 (`plan4t-check.log`). The
    final-state run was started (`plan4t-check-final.log`) and had not finished when I handed over.
  - MxKat passed at `ae8b8d8` + INIT (`mxkat.log`, `MX KAT PASS`). At `407260d` it prints
    `MX KAT FAIL 30` for HEAD **and** for HEAD + INIT, with identical output (`mxkat-base.log` =
    `mxkat-final.log`): REPF's fold changed `evalMT4` against the `face798` reference. This is not
    INIT's doing, but the orchestrator should know.
  - Axioms: 21 theorems, only `propext`/`Classical.choice`/`Quot.sound` (`axioms.log`).
  - Source rule: 462 files, 0 findings (`source-rule.log`). No `sorry`.
  - Per-module build times show no regression (160 common modules: 1,245 s at HEAD vs 1,169.5 s with
    INIT, under load).

## 1. Profile

There is no `perf` (paranoid 4) and no `gdb`, so I wrote two in-process tools (`logs/INIT/`):

- **`instr.py` + `initprof.c` + `build-instr.sh <exe>`** re-compile every entry module's C. They wrap each
  `_init_X`, both the eager top-level constants and the lazily forced `lean_obj_once` closed terms, in
  an enter/exit timer that gives inclusive and exclusive ms, and they also time `lean_mark_persistent`.
  The result is linked as an instrumented copy of the exe (`instr/start0`).
- **A SIGPROF sampler** in `initprof.c` (1 ms of CPU, `backtrace()`, set `INITPROF_SAMPLE=<file>`).
  `symb.py`, `callers.py`, `under.py`, `frself.py` and `direct.py` symbolize the samples with `nm`.

A finding that matters for every track: since Lean 4.2x, **closed subterms inside function bodies are
lazy** (`lean_obj_once`, forced on first use). **Every top-level nullary `def` of a data type is computed
at process start**, whether or not anything uses it, because the module initializer runs it.

**Start-up at `9249a56`** (17.7 s user; `prof-head-2.log`, `symb-head.txt`):

| constant (module) | exclusive ms | cause |
|---|---|---|
| `X.X4.nd` → `decF04.closed_2` = `chTab4 seq4 456` (FRXDec4F0) | **7,029** | `tabEnt4 S p` recomputes `fsMsgs4 S` (all phases, every `fieldOffOf`) for each of 457 entries |
| `planData4` + `planOf4` (FRNodeRows4Plan) | 4,526 | prototypes' compile, slot pieces, grouping, `arOf` trail |
| `progS30/31/32`, `progNN2/4/8` (FRSubmission4V) | 6 × 606–755 | `gen4`: `fieldOffOf`/`dOff4` recomputed per position (871 per program); `reloc` per op |
| `Impl.nodePlan` (FRVerifierImplCore) | 1,497 | `TEval.planOf` (3.x finals): compile, `slotRP`, grouping |
| `progSegG`, `protoProg` | 213 + 205 | `genPhaseG`'s `dOff4` per position |

**At `407260d` + INIT** (instrumented total 19.9 s; `prof-final.log`, `samp-final.txt`, `under-final-planOf4.txt`):

| item | exclusive ms | owner |
|---|---|---|
| `planOf4.closed_0` = `planOf4D` (replay fold: `arRepOf`/`trailMR` 6.4 s, `mkPlan4` 6.2 s) | 13,009 | **CF** (§3.1) |
| `planData4` (prototypes' compile + slot pieces + grouping) | 1,852 | CF's file, compile functions INIT's |
| `Impl.nodePlan` | 1,580–1,898 | INIT (no single hot spot; §4) |
| `planOf4` own (`mkPlan4`'s eager fields) | 1,171 | CF |
| `protoProg 0` (`planData4.closed_16`) | 222 | — |
| the six programs | 6 × 45–113 | — (was 6 × 0.6–0.75 s) |
| `progSegG`, `protoProg 1`, `lPlan`, `tplWalk14*`, `pfIR`, … | 30–80 each | — |

## 2. Changes made (INIT's)

Every change keeps the compiled values bit-identical (§0, `initfp`). They are in this order:

1. **`FRXChain4`: `chTab4` computes `fsMsgs4 S` once.** I added `tabEntM ms p`, the old `tabEnt4` body
   over a message list. Now `tabEnt4 S p := tabEntM (fsMsgs4 S) p` and
   `chTab4 S N := (List.range (N+1)).flatMap (tabEntM (fsMsgs4 S))`. **`chTab4_eq`** (rfl) recovers the
   old form, and four proof lines also unfold `tabEntM`. **−7.0 s.**
2. **`FRVIR4.genPhase4`, `FRVIR4Mux.genPhaseG`: per-phase offsets.** The queries branch binds `o fCols`,
   `o fSibs`, `dOff4 S i` and `posW4 S i` once per phase instead of once per position. These are
   `let`s only: every proof uses `simp only [genPhase4]` (zeta) and builds unchanged.
3. **`FRVIRFinals4.finOps4`: relocation by table.** `finOps4` maps `relocT P.S (fieldOffT P.S)` (both moved
   up from `FRVIR4Mux`, with **`relocT_eq`**). The old `reloc` form is **`finOps4_def`**, which four proofs
   now use: `finOps4_seq3`, `FRVIR4At.map_at_finOps4`, `FRSoundness4Qry.noAsk_finOps4` and
   `FRSoundness4R4Run.finOps4_eq`. `finOps4F` is now definitionally `finOps4`. Edits 2 + 3 together:
   **≈ −3.7 s** over the 8 programs.
4. **`FRVIRTplBuild`.**
   - `inputKindsF` accumulates the shared inputs reversed, with a counter. It used `q ++ [_]` and
     `length` per input, which is quadratic. No theorem mentions it, and the output is the same.
   - `tinRPu`'s unaligned tail uses **`instIRA`**, which reads the inputs from an array, with
     **`instIRA_eq`**; `tinRPu_rows` adds it to its `simp` set.
   - Together ≈ −0.25 s (sampled).
5. **`FRVIR4Mux.kt`: `@[noinline]`.** When `kt` is inlined, the compiler floats each `let` into its
   `match` branch, so every application recomputed `S.lvK`. ≈ −0.13 s, sampled. `noinline` is not a
   code-changing attribute; the source rule passes.
6. **`FRVIRTplTab.eqTblG`: reads the previous table from an array** (`let a := r.2.toArray`). The
   `List.getD` per entry was quadratic in the table size. I added **`toArray_getD`**, which
   `eqTblG_nlocs` and `eqTblG_ev` use; their statements are unchanged. It cut 1.6 s inside REPF's
   `evalL` replay templates (`tplEvLx`, `mkEvCx` → `tabsG` → `eqTblG`; `samp-407.txt` vs
   `samp-final.txt`).
7. **New module `FRInitFuse`: `compMSXA`**, the plan compile (`compMSX`) and the template generators' trail
   (`trailMS`) in one walk. **`compMSXA_eq`** proves it is the pair `(compMSX …, trailMS …)` for every
   extension, generator, memo and state, by induction with a split on `alignOf`/`cur` for `assertEq`.
   It is not wired in: the wiring is in CF's file (§3.1).

The files touched by edits 2, 3 and 6 (`FRVIR4`, `FRVIR4Mux`, `FRVIRFinals4`, `FRVIR4At`, `FRSoundness4Qry`,
`FRSoundness4R4Run`, `FRVIRTplTab`) are not on my list. No running track owned them. **Deviation, flagged for
the orchestrator.**

## 3. Proposed changes in others' files (measured)

### 3.1 For CF (`FRNodeRows4Plan`, `FRNodeRows4Rep*`, `FRVIRTplRep*`, `FRNodeRows4Defs`)

1. **The `2^40` literal: 1.9 s of start-up** (1,925 samples of 12,766 in `planOf4D`; `callers.py … lean_cstr_to_nat`).
   - The cause: `repB := 2 ^ 40` (FRNodeRows4Defs) is constant-folded into every use. Lean's C emitter
     writes a Nat literal ≥ 2^32 as `lean_cstr_to_nat("1099511627776")`, which is a GMP string parse at
     every evaluation.
   - Where it runs: inside `repFitB` (723 samples), `linFr`/`rowFr` (424), and `linLoc`/`rowLoc`
     (408 + 347).
   - The literals: `1099511627776` appears 19 times in the IR, and `repB + x` forms (`1099512184832`, …)
     6 more times (`grep lean_cstr_to_nat .lake/build/ir/*.c`).
   - The fix: `@[noinline] def repB : ℕ := 2 ^ 40`. Then each use reads the eagerly built global, and no
     proof changes. Alternatively, compare against a value bound once outside the loops. Expected: about
     −1.9 s.
   - **General rule for every track: no Nat literal ≥ 2^32, written or folded, inside a loop.**
   - The V path has a few too: a `2^64` in `accWith4`, `2^128` in `f256Params`. They are not hot
     (≤ 1 sample).
2. **Fuse the plan's two walks per prototype (`FRInitFuse.compMSXA`).**
   - Measured in process at `91e0d61` (`fusetime.log`, `probe/FuseTime.lean`, outputs `same true`):
     `compMSX` 721–784 ms + `trailMS` 1,449–1,551 ms = 2,171–2,335 ms; fused, **1,184–1,274 ms**
     (**−1.0 s**).
   - Real process (`ab-start0-fuse2.log`): 6.14–6.40 s with the fusion, against 7.05–7.47 s without.
   - The patch against `91e0d61`'s `FRNodeRows4Plan` is `logs/INIT/plan-fuse.patch`, built green with
     `FR Solution FRSubmission4Fin`. It adds `planDataA4` (both walks fused, returning
     `(planData4, askRowsT 0, askRowsT 1)`), **`planDataA4_eq`** (from `compMSXA_eq`, `arOf_eq` and
     `trailMS_T` with `compMSX_T`'s `MOk`), `planOf4DA` (`planOf4D` with the ask rows passed in), and
     `planOf4 := planOf4DA planDataA4.1 …`.
   - **`planData4` must become `noncomputable`.** Otherwise it is still built at start-up as well: my first
     try kept it and was ≈ 1 s slower than the fused figure (`ab-start0-fuse.log`).
   - REPF's `trailMR` (ask + replay rows) has the same step as `trailMS`, so the same pattern applies: a
     `compMSXR` with `compMSXR_eq`.
3. **`Tpl.instRows` by `instRowA`** (array inputs). `kRows → instRows` spends 179 ms in `List.getD`. Only
   `FRNodeSound4.tinIRows_snd` unfolds it; its proof becomes `rw [tRows_eq]; rfl`.
4. **The rest of the replay cost** (`under-final-planOf4.txt`; `kRows` 4.4 s, `kmuxT` 2.5 s, `grows`
   1.6 s, `repLocL/F` 2.3 s (incl. item 1), `Tpl.nlocs` 1.3 s, `subsG` 1.0 s, `lean_dec_ref` 1.7 s) is
   the replay rows themselves. CF's closed forms remove them.
5. **V(N4) is 1.86 s at `407260d`** (HEAD's own; `vtime4-base.log`). That is ≈ 9 × `v_ref`, close to the DoS
   per-item cap 10·v_ref = 2.06 s, and `verify_s`'s margin shrinks from 37× to ≈ 5×.

### 3.2 For IMPC/IMPC2 (no running owner; orchestrator's two levers)

- **`impcTG` (`pfLoc`/`provOf`)** costs **≈ 0.23 s for both prototypes** (sampled at `ae8b8d8`: `winE`/
  `pfLoc` 0.17 s, `provOf` 0.09 s).
  - `winE` calls `pfLoc` 17 times, each a linear `find?` over `pSegs`. `pfLoc_spec` only needs "some
    member of `pSegs` with `st ≤ o < st + len`".
  - A binary search over `pSegs.toArray` that **re-checks** the predicate keeps that spec. Being *equal*
    to the `find?` also needs `pSegs` sorted and disjoint as a decided fact: about 60 segments, but the
    kernel must evaluate `fieldOffOf seq4` for 20 fields, a kernel cost I did not measure.
  - `provOf`: `pv` comes from `provAcc`, so it is ordered by register. An array indexed by register,
    with a `provOf` equality lemma, would replace `find?`.
  - Not done: about −0.15 s for proof work in files whose structure I would be changing blind.
- **IMPC2's `bitOf`/`tensorW` copy rows (compile placement).** IMPC2 projects −0.7 s once folded (+1.0 →
  +0.3 s). I judge it **reasonable but a stage of its own, not an INIT edit.**
  - The shape: an extension in `FRVIRTplExt`'s style, like CK's `extGetK`, whose `Out` for `bitOf` (and
    `tensorW`'s `bits` aux) uses slots = the bit-area cells from `bitSrc`. It has no import, `fresh = 0`,
    and no rows.
  - The obligation: the extension's ok-lemma cannot be local. The value is then bound by `bitTGB`'s
    decomposition rows (generator rows), not by the op's own rows. So `bitOf` stops being an import, and
    IMPC2's `atImp_bitB`/`Gap4.imp` argument has to be restated as "the compile's slot is a bit cell
    that `bitTGB` constrains". The zero sources need a pinned zero cell.
  - The knock-on work: the prototypes' layout changes, so re-dump the node blob (the prover), re-fit the
    arena, re-run MxKat/V.
  - The payoff (−0.7 s) is real. It needs a track that owns `FRVIRCompile`/`FRVIRTplExt` and IMPC2's
    proofs together.

## 4. Remaining start-up outside the replay (for the next cut)

At `407260d` + INIT, outside `planOf4D`: `planData4` 1.85 s, `nodePlan` 1.6–1.9 s, `mkPlan4`'s eager
fields 1.17 s, programs and group programs ≈ 0.9 s, the rest < 0.5 s.

- **`nodePlan`** (`TEval.planOf (finC finPf)`, the segments' `evalM`) is spread across many functions:
  `compMSX` 0.5 s, `slotRP` 0.39 s (most of it freeing the compile state), `planOfD` 0.23 s, grouping
  0.18 s, `mkKM` 0.16 s, `patsFor` 0.16 s. It has no quadratic hot spot left.
- **Freeing is visible.** `lean_dec_ref_cold` is ≈ 0.7 s inside `slotRP`/`trailMS`, where the compile
  states are consumed. Fusing the walks (§3.1.2) removes one state per prototype.
- **`nodeQ`/`segQ`** rebuild `nodeFinP` (with `rsvCells`' 60-element map) at every kind-table application
  during the group programs' compile: 0.14 s sampled. A `kt`-memoized `nodeQ` would cut it, at the cost
  of proof changes in `FRVIR4Uni`.

## 5. Init budget for incoming rows

Measured on this VM, `initbudget` probe (`probe/InitBudget.lean`, `initbudget.log`, `prof-budget.log`).
Rows have the shape of a 1-term `a` and a 2-term `b`; the cost grows about linearly with the terms per row.

| structure | init per 100 k rows | notes |
|---|---|---|
| **sparse row list**, as a closed constant (`List (ℕ × Row)`) | **≈ 47 ms** (37 ms to build, ≈ 10 ms to mark persistent) | `topSparse` |
| **keyed instances** instantiated at init (template × instances, `instRowA`) | **≈ 85–95 ms** (k = 8 or 64 rows per template) | `topKeyed`, `keyedRows` |
| **rows from a generator in the plan's trail** (a `TG` in `askTG`) | its per-op work + ≈ 50–100 ms of rows. A **new walk** over the ≈ 155 k ops costs 0.7–1.5 s per prototype on its own (`askRowsT 0` standalone: 66,263 rows, 1.49 s), so ride the existing walk | ASK-T's `askTGT` +0.12 s, `impcTG` +0.40 s, IMPC2 `bitTGB` +0.9 s for 48k/63k rows |
| **closed form** (V evaluates the family directly) | 0 | V time only |

Rules of thumb:

1. **A top-level data `def` is paid at every start, used or not.** Put large tables behind a function
   (`(_ : Unit) →`) only if their first use is untimed. Here nothing is untimed: the stream, `V_i` and
   the DoS column all time the first check.
2. **Never index a `List` inside a loop** (`getD`, `get?`, `idxOf`), and never append with `l ++ [x]` in
   a fold. Use arrays or reversed accumulators. INIT's 7 s, 1.6 s and 0.25 s cuts were all this.
3. **Do not recompute shape helpers per item** (`phasesOf`, `fieldOffOf`, `dOff4`, `S.lvK`). Bind them
   once per phase or table. `kt` is `@[noinline]` now, so a `kt` table is evaluated once.
4. **No Nat literal ≥ 2^32 inside a loop** (§3.1.1).
5. **Grouping (`grows`) costs about as much as generating the rows** (IMPC2: ≈ 2.5 µs each).

## 6. Files

Edited, in `submissions/flock-recursive/lean/`:

- `FRXChain4.lean`
- `FRVIR4.lean`
- `FRVIR4Mux.lean`
- `FRVIRFinals4.lean`
- `FRVIR4At.lean`
- `FRSoundness4Qry.lean`
- `FRSoundness4R4Run.lean`
- `FRVIRTplBuild.lean`
- `FRVIRTplTab.lean`

New, in the same directory: `FRInitFuse.lean`.

Docs: `docs/v4/flock-recursive/stages/INIT-RESULT.md`, `INIT-JOURNAL.md`.

Logs and tools in `logs/INIT/`:

- Instrumentation: `instr.py`, `initprof.c`, `build-instr.sh`, `symb.py`, `callers.py`, `under.py`,
  `frself.py`, `direct.py`, `ab.sh`.
- The fusion patch: `plan-fuse.patch`, with `FRNodeRows4Plan.HEAD.lean`.
- Results: `ab-*.log`, `fp-*.log`, `prof-*.log`, `samp-*.txt`, `vtime4-*.log`, `mxkat*.log`,
  `plan4t-check*.log`, `axioms.log`, `source-rule.log`, `build-*.log`.

Probes in `logs/fr-build-INIT/probe/`: `Start0`, `InitUse`, `InitFp`, `InitBudget`, `FuseTime`.
