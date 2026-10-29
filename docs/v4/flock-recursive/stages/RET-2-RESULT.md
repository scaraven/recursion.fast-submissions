# RET-2 RESULT: the 3.x soundness front out of the Rev4 certificate's closure

This is step 3 of plan (B) in BLUEPRINT §10 "changes 27".

- **Base.** Work started on HEAD `1c5a738`. The final build ran on HEAD `43b72fc` plus RET-2's files.
  The commits S-I, S-E13a, S-E14 and D-PK landed in between. None of them touches a RET-2 file except
  `FR.lean`, where the commits added lines and RET-2 adds one line.
- **Build tree.** `logs/fr-build-RET2`, copied from `fr-build-INT10`. `MINE.txt` lists 65 modules.
- **Timing tree.** `logs/fr-build-RET2t`.
- **Logs and tools.** In `logs/RET2/`. The journal is `RET-2-JOURNAL.md`.
- **Rules followed.** Every lean/lake command ran in the 16G scope under `timeout`, builds on 4
  cores (`taskset`). No sub-agents. Nothing committed.

## Status

| Check | Result |
|---|---|
| Item 1: census | Done; see §3. At `2f437ed`, `Solution`'s closure held **66 3.x soundness modules**. The brief's 27 roots held 67. |
| Item 2: `tail_shift` | Moved verbatim to the new control module `FRSoundness4TailShift` (imports `FRSoundness4TailLig`, `FRSoundnessTail`), which is outside the certificate's closure. `FRSoundness4TailLig` no longer imports `FRSoundnessTail`. `FR.lean` imports the new module. |
| Item 3: re-point | 10 Rev4 modules had a direct import of a 3.x module; all now import Core instead (import lines only). **391 declarations and 1 anonymous instance** moved from 46 3.x modules into 6 new `FRSoundnessCore*` modules, with RET-1's chunker. |
| Item 4: result | **`Solution`'s closure holds 5 3.x soundness modules** (`Defs`, `StepA`, `StepB`, `StepC`, `Truths`; 1,492 lines). All of them come in through one edge, `FRXLevel → FRSoundnessTruths` (S-H4's module). **With S-H4's one-line edit (§6) it holds none.** That edit is built and checked. |
| Statements | 393 names hashed before and after (`stmt-{before,after}.txt`): the 391 moved declarations, the instance and `tail_shift`. Every type is identical, and so is every definition's value. **No statement and no proof changed.** |
| Build | `lake build FR Solution FRSoundness4TailShift` plus the 27 roots and controls: **green**, 2,582 jobs, at HEAD `43b72fc` + RET-2 (`build-FR-final.log`). |
| Axioms | `ax/AxRET2.lean` (`axioms-final.log`): all 393 names are in a Core module (`tail_shift` in `FRSoundness4TailShift`). They use only `propext`, `Classical.choice` and `Quot.sound`. So do `RecursionFast.Challenge.certified`, `certificate_sub4`, `complete_rev4`, `delta_rev4` and the rest of S-I's list. |
| Source rule | `logs/org20/scripts/source-rule.py submissions/flock-recursive`: 357 files, **0 findings** (`source-rule-final.log`). |

## 1. What was built

Line counts are `loc.py` total / code / theorems (`logs/RET2/loc-{before,after}.txt`).

| Module | total / code / thm | Imports | From |
|---|---|---|---|
| `FRSoundnessCoreChain` (new) | 757 / 631 / 29 | `CoreDefs` | `Defs` (14 declarations: `fsStarts`, `fsRanges`, `pRound`, …), `FrChain` (24 declarations + `DecidablePred` instance: `G.FsSeq`, `Matches`, `IsChain`, `EscG`, `muG`, `chains`) |
| `FRSoundnessCoreTruths` (new) | 351 / 217 / 15 | `CoreSteps`, `FRRSEval` | `StepA`, `StepB`, `StepC`, `Truths`: the 3.x positions (`phStart`, `capPos`), `wordOf`, `lvN`/`lvK`/`lvE`, the decoder's truths (`wordK`, `foldAt`, `sAt`, `msgOf`, `decodeL`, `farL`, `consSet`, …) |
| `FRSoundnessCoreRows` (new) | 1,158 / 748 / 75 | `CoreTail`, `CoreTruths`, `FRNodeCircuit`, the contract's `Certificate`/`PaperTheorem` | `StepE`, `Hide`, `FRKState`, `PIOP`, `Tail`, `TailM`, `Front`, `Rows`, `FrW0`, `FrRS`, `FrPend`, `FrZ`, `FrB`, `FrE`, `FrL`, `FrW0V`, `FrRS0` |
| `FRSoundnessCoreFront` (new) | 575 / 429 / 55 | `CoreRows` | `FrSh`, `FrS`, `FrZM`, `FrBind` |
| `FRSoundnessCoreAcc` (new) | 1,049 / 750 / 89 | `CoreTail`, `FRVIRChain`, `FRVerifierImplOps` | the 12 `Acc*`, `FrRun`, `FrRnd`, `FrRndV`, `FrLc`, `ExtStmt`, `ExtLeaf` |
| `FRSoundnessCoreWalk` (new) | 271 / 213 / 18 | `CoreAcc`, `CoreFront` | `FrWalk` |
| `FRSoundness4TailShift` (new control) | 40 / 29 / 1 | `FRSoundness4TailLig`, `FRSoundnessTail` | `tail_shift`, verbatim |
| 46 edited 3.x modules | 15,726 / 11,471 / 1,052 → 12,572 / 8,923 / 771 | each adds `import FRSoundnessCore…` and a `-- RET-2:` pointer line | the moved chunks deleted, nothing else changed |
| 10 Rev4 modules: `P4aNames`, `P4aSeg`, `P4bNames`, `Pos`, `R4FrLc`, `R4Ref`, `R4Rnd`, `R4Run`, `R4W0`, `XFinal` | import lines only | see §2 | |
| `FRSoundness4TailLig` | 583 / 400 / 38 (was 39 theorems) | `− FRSoundnessTail` | `tail_shift` out |
| `FR.lean` | + `import FRSoundness4TailShift` | | |

- **Totals.** The 6 Core modules have 4,161 total / 2,988 code lines. Over all RET-2 files the
  theorem count is unchanged (1,218), and the code is +447 lines: the replicated
  `namespace`/`open`/`variable` lines.
- **How the Core modules were built** (`tool/move2.py`):
  - Each source module becomes one `section … end` block in its Core module, with the context
    commands replicated and empty sections pruned.
  - Source modules are ordered topologically on the dependencies between the declarations.
  - A Core module's imports are the non-3.x FR modules its constants read, plus the earlier Core
    modules, transitively reduced. None of these imports reaches a 3.x soundness module (checked).

## 2. Re-pointed imports (item 3)

| Rev4 module | was | now |
|---|---|---|
| `FRSoundness4P4aNames` | `FRSoundnessFrZM` | `FRSoundnessCoreFront` |
| `FRSoundness4P4aSeg` | `FRSoundnessExtLeaf` | `FRSoundnessCoreAcc` |
| `FRSoundness4P4bNames` | `FRSoundnessFrPend` | `FRSoundnessCoreRows` |
| `FRSoundness4Pos` | `FRSoundnessFrChain`, `FRSoundnessStepA` | `FRSoundnessCoreChain`, `FRSoundnessCoreTruths` |
| `FRSoundness4R4FrLc` | `FRSoundnessFrLc` | `FRSoundnessCoreWalk` |
| `FRSoundness4R4Ref` / `R4Rnd` / `R4Run` | `AccSem` / `FrRndV` / `FrRun` | `FRSoundnessCoreAcc` |
| `FRSoundness4R4W0` | `FRSoundnessFrW0V` | `FRSoundnessCoreRows` |
| `FRSoundness4XFinal` | `FRKState` | `FRSoundnessCoreRows` |
| `FRSoundness4TailLig` | `FRSoundnessTail` | dropped (item 2) |

- **No name moved to a different namespace.** So no Rev4 proof text changed.
- **The import check before building.** `tool/impcheck.py` uses `scratch/ModUses.lean`, the
  module-level use relation of every FR module, with each 3.x constant mapped to its Core home. It
  showed that every module of the new closure still reaches every module it uses.

## 3. Census (item 1, then item 4)

The tool is `tool/census.py`. Module CPU times are from S-I's 7763 run,
`logs/S-I/run-40810876665/build-modules.txt`.

| Closure | Modules | 3.x soundness modules | Their CPU-s (7763) |
|---|---|---|---|
| `Solution`, before (`2f437ed`) | 306 | **66** (20,485 lines) | 476.8 of 2,972.7 |
| `Solution`, after (RET-2) | 251 (−61, +6 Core) | **5** (1,492 lines): `Defs`, `StepA`, `StepB`, `StepC`, `Truths` | 39.3 (pre-move times) |
| `Solution`, after + S-H4's edit | 246 (−66, +6 Core) | **0** | 0 |
| Brief's 27 roots (incl. `FRNodeSound4Ctrl`), before | 317 | 67 | |
| Brief's 27 roots, after | 314 | 58 | |

- **The brief's 27 roots after RET-2.** 53 of the 58 come in through
  `FRNodeSound4Ctrl → … → FRNodeRead4 → FRNodeSoundA → FRSoundnessExtLinks`. This chain is not in
  `Solution`'s closure. `FRNodeSoundA` is not on my edit list; see §6.
- **The direct edges before.**
  - `P4aNames→FrZM`, `P4aSeg→ExtLeaf`, `P4bNames→FrPend`, `Pos→FrChain,StepA`,
    `R4FrLc→FrLc`, `R4Ref→AccSem`, `R4Rnd→FrRndV`, `R4Run→FrRun`, `R4W0→FrW0V`,
    `TailLig→Tail`, `XFinal→FRKState`, `FRXLevel→Truths`.
  - In the controls only: `FRNodeSoundA→ExtLinks`.
  - In each case the edge pulled in the whole chain behind it, `AccRun → LigFinal → Compose → …`.
- **The direct edges after.** `FRXLevel→FRSoundnessTruths` in `Solution`'s closure, and
  `FRNodeSoundA→FRSoundnessExtLinks` in the controls' closure.
- **Dropped from `Solution`'s closure (61 modules).**
  - `FRKState` and `FRSoundness{Acc, AccCol, AccEq, AccFin, AccLog, AccLvl, AccPf, AccPos, AccQry,
    AccRun, AccSeg, AccSem, AccVal, AccW, Compose, ExtLeaf, ExtR, ExtStmt, Fold}`.
  - `FRSoundness{FrB, FrBind, FrChain, FrDF, FrE, FrExt, FrK, FrL, FrLN, FrLc, FrObl, FrPend, FrRS,
    FrRS0, FrRnd, FrRndV, FrRun, FrS, FrSh, FrStab, FrW0, FrW0V, FrWalk, FrZ, FrZM}`.
  - `FRSoundness{Front, Hide, LigFinal, Ligerito, PIOP, Phases, Rows, Shift, StepD, StepE, Tail,
    TailD, TailM, TailO, Walk, Weights}`.
  - With S-H4's edit, also `Defs`, `StepA`, `StepB`, `StepC` and `Truths`.
- **What remains of the old verifier, the old extractor and the old front:**
  - **Step 4, the 3.x verifier shapes:** `FRVIRFinalsSG`, `FRNodeLayout`, `FRNodeCircuit`, `FRVIRMux`,
    `FRVIRCompileSound`, `FRVIRFinals`, `FRVIRFinalsSF`, `FRVIREval`, `FRVerifier`, `FRVerifierImpl`.
    Core reads them: `CoreRows` (`FRNodeCircuit`, `FRVIREval` via `PIOP`'s `rowMat`, `Front`'s
    `nodeBK`), `CoreAcc` (`FRVIRFinals*`, `FRVIRChain`) and RET-1's `CoreSG`.
  - **Step 2, the FRX modules:** 41 non-`FRX4` `FRX*` modules, unchanged.
  - **The 3.x front modules themselves** stay in `lean/` and are still built by `FR`. They import
    Core. None was deleted.

## 4. The remaining Core content is not all "position-free"

- **Revision 4.1 reads it as it is.** The moved set is not a choice. It is exactly the
  dependency closure (type, value and proof) of the 3.x constants that the Rev4 closure reads. It
  includes 3.x-positional definitions that Rev4 names directly: `phStart`, `fsStarts`, `capPos`
  (S-G13's `phStart4_shift`, P4b's names), the item-list part of `Defs`, `AccSem`/`FrRun` (R4's
  reference semantics), and `FrSh`/`FrZM`'s `kMat`/`slotT`/`targetS_range` (P4a, `FRNodeTarget4W`,
  `FRNodeCircuit4`).
- **It is moved, not ported.** Each declaration keeps its name and its statement, so no Rev4
  statement changed. Replacing them with T4's copies (`FR.Snd.T4`) would change the Rev4 modules'
  statements. That needs the owning tracks.

## 5. Times

**Per-module estimate on the EPYC 7763 (S-I's table):**
- **Dropped:** 61 modules, **436.5 CPU-s**; with S-H4's edit, 66 modules, **476.8 CPU-s**.
- **Added:** the 6 Core modules, **≈ 75 CPU-s**. This is their VM times (190 s in `after`) divided
  by the measured VM/7763 per-module ratio of the common modules (2.51).
- **Net:** **≈ −360 CPU-s** (−400 with S-H4's edit). That takes S-I's 2,975 CPU-s to **≈ 2,615**
  (≈ 2,575), before the modules S-E13a/S-E14 have added since.
- **This is not enough on its own:** the target is ≤ 2,020 CPU-s, or ≤ 1,550 for a 1.3× margin.

**Measured on the VM** (`tool/times.py`):
- **Setup.** Each run is a fresh `lake build Solution` of the entry on 4 cores (`taskset -c 24-27`)
  in the 16G scope, timed with `/usr/bin/time -v` (`time-*.txt`, `tbuild-*.log`). The VM is shared:
  load averaged 9–24 during the runs.
- **Same sources.** `before2`, `after` and `after-h4` have the same Lean sources apart from RET-2
  (HEAD `e2b7bc2` = `adc7a74` for `lean/`).

| Run | Wall | CPU (user + sys) | Entry modules | Sum of Lake's per-module times |
|---|---|---|---|---|
| `before2` (HEAD) | 1,342 s | 4,740 s | 309 | 7,458 s |
| `after` (HEAD + RET-2) | **1,171 s (−171, −12.8 %)** | **4,231 s (−509, −10.7 %)** | 254 | 6,615 s |
| `after-h4` (+ `FRXLevel` re-pointed) | 1,080 s (−262) | 3,882 s (−858) | 249 | 5,844 s |

- **The noise is large.** Between `after` and `after-h4` only 5 small modules differ (139 s of
  module time), yet the CPU totals differ by 349 s.
- **Use the 7763 estimate above for planning.** The VM pair confirms the direction and the order
  of magnitude: ≈ −10 % CPU, ≈ −13 % wall.
- **The first `before` run (at `2f437ed`) is excluded.** HEAD moved during the runs, and S-E13a's
  `FRNodeRows4*` entered `Solution`'s closure.

## 6. Edits needed from other owners

1. **S-H4, in `FRXLevel`:** change `import FRSoundnessTruths` to `import FRSoundnessCoreTruths`.
   This one line is all that keeps `FRSoundness{Defs, StepA, StepB, StepC, Truths}` in the
   certificate's closure.
   - **Checked.** `FRXLevel` with this import elaborates (`frxlevel-repoint.log`).
   - **Built.** A full `Solution` build with this edit overlaid in the timing tree is green
     (`tbuild-after-h4.log`).
   - **Already in place.** Everything the `FRX*` chain read from the 3.x step/truth modules is in
     `FRSoundnessCoreTruths`.
2. **Orchestrator (`FRNodeSoundA`, S-N1's 3.x module, which no running track owns):**
   - **The edit.** Change `import FRSoundnessExtLinks` to `import FRSoundnessCoreRows`. Then add
     `import FRSoundnessExtLinks` to `FRSoundnessExtAll`, which reaches `X.E_leaf` and
     `E_node_of_run` only through `FRNodeSoundA`.
   - **What it gains.** It takes the remaining 53 3.x modules out of `FRNodeSound4Ctrl`'s closure.
     It does not affect `Solution`.
   - **Not applied.** I made it, saw `ExtAll` break, and reverted it because the module is not on
     my edit list. `impcheck.py` shows `FRNodeSoundA` needs nothing else.
3. **Step 4 (S-0′/S-E):** when `FRVIRFinalsSG`/`FRVIREval`/`FRNodeCircuit` are split, the Core
   modules' imports of them (`CoreRows`, `CoreAcc`, RET-1's `CoreSG`) are what must follow.

## 7. Deviations

- **Six new Core modules.** The blueprint names `Core{Steps,Weights,Tail,Lig}`; this pass adds
  `Core{Chain,Truths,Rows,Front,Acc,Walk}`. The grouping balances module start-up (≈ 6 s each on the
  VM) against parallelism. `CoreChain` (T4, `Pos`) and `CoreTruths` (the `FRX*` chain) are small
  and early. `CoreAcc` does not depend on `CoreRows`/`CoreFront`.
- **Context lines replicated.** The 46 3.x modules keep their remaining declarations; only the moved
  chunks are gone. +447 code lines in total, from the replicated context.
- **The mover keeps `open Circ`** (RET-1 dropped it). `PIOP`'s `rowMat` needs `open Circ Eval`.
- **One extra seed.** `levelPhases_length` is named in a `simp [...]` that does not end up in the
  proof term, so the dependency closure missed it. It was added by hand (`extra-seeds.txt`).
- **Time run at 4-core affinity.** Lake 4.34 has no `-j` flag, so builds ran at 4-core affinity.

## 8. Open questions

1. **Delete the dropped 3.x modules?** The orchestrator, together with S-I's `Solution`: may the
   61 dropped 3.x modules (66 after S-H4's edit) be deleted from `lean/`, along with
   `FRSoundness4TailShift` and the 3.x controls that read them (`FRSoundnessExtAll`, …)? `FR.lean`
   still imports them.
2. **Apply the `FRNodeSoundA` re-point (§6.2)?**
3. **The build budget.** Retiring the front gains ≈ 360–400 CPU-s on the 7763. The remaining gap
   to 2,020 CPU-s (≈ 550–600 s) has to come from step 2 (the 3.x extractor), step 4 (the 3.x
   verifier shapes) and G2's golf.
