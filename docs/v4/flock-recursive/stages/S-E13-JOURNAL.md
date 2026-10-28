# S-E13 (track L-circ): JOURNAL — the plan build ≤ 2 s per process

Build tree `logs/fr-build-SE13` (copy of `fr-build-INT6`; `snap.sh` symlinks the L-circ modules
listed in `MINE.txt`, probes in `probe/` as executables). Logs in `logs/S-E13/`. Every lean/lake/probe
command runs in a 16 GB scope with a timeout; probes are pinned to one idle core (`run.sh`, core 26).

## 2026-10-28

- **Baseline** (core 26, idle): `coldwarm init` (imports `FRNodePlan`, `main` does nothing) **49.9 s**
  (`base-coldwarm-init.log`); `initt` (imports `FRVerifierImpl`, no node plan) 4.36 s
  (`base-init-noplan.log`). Slot 0's parts (`base-plant.log`): compileT zero 1.70 s, mkLay 3.68,
  compileT 1.88, slotIRows 3.49, slotPPs 8.99, groupPPs 2.05, eqL 1.13, mkPats 0.22.
- **Where the 4.36 s of other process start goes** (import bisection, `base-init*.log`,
  `fix1-init*.log`): `FRVIRTplRep`'s closed `tplRowW = rowWG 2^14` rebuilds `lagG …` and `eqTblG …`
  for each of its 16,384 products (4.1 s).
- **Per-key template costs** (`base-planb.log`): `compile` without templates is 107 ms; with them
  1.86 s. `tplShiftMask 18 18` takes **1.5–1.7 s per construction**: `mEnt` rebuilds the four
  tables `mTabs` per entry (2,100 entries). It is built once per compile pass, in `mkLay`, `tRows`,
  `cregion` and the plan's replay: ≈ 6 constructions per slot.
- The walk (`walkb`, `fix1-walkb.log`): the DAG build is 50 ms, `tplWalkG` 53 ms, rows 51 ms; not a
  cost. (The builder's state updates now read every other field before pushing the gate array, so
  that the push is in place: `emit`, `padTo`, `dmul`, `dacc`.)
- **Fix 1 (templates computed with their tables once)**: `tplShiftMaskF` (`= tplShiftMask` by
  `rfl`) in `tplOf`; `rowWGF` (`= rowWG` by `rfl`) for `tplRowW`. Statements unchanged
  (`tplShiftMask_ok`, `tplRowW_ok` re-proved through the `rfl` lemmas).
  - `initt` 4.36 → **0.39 s** (`fix2-initt.log`).
  - slot 0's parts (`fix2-plant.log`): compileT zero 343 ms, mkLay 192, compileT 403, slotIRows
    676, slotPPs 1,677, groupPPs (both slots) 2,198, eqL 1,315, mkPats 254, prepPiece 56.
  - **`planOf` 12.4 s; process start with the plan 49.9 → 12.3 s** (`fix2-coldwarm-init.log`).
- **The new construction** (`FRVIRTplBuild`, new): proto-pieces `RP` without materialised rows; the
  compile with a template memo recording the skeleton's blocks (`compMS`, `compMS_eq`); per-key data
  once per process (`KM`, `mkKM`, `keyInfo_eq`); the skeleton's blocks abstracted with a confirmed
  lookup (`absRowsV`, `absRowsV_inst`); template blocks re-templated at the template level (`reT`,
  `reT_inst`), equal blocks sharing one object (`canonT`); **`slotRP_rows`** (proto-pieces' rows =
  `slotIRows`, for any compiled state, layout and blocks); the grouping keyed by hashes (`groupRP`,
  untrusted); **`toPiece_rows`** (the check `insOk` + `withPtrEq` on the template; `GK.hn` carries
  the input bound with its proof); `piecesOf_rows`.
  - First probe (`plann-1.log`, proofs not yet written): **3.2 s** for both slots, `evalMT` equal to
    the old plan's at a random point, 72 vs 75 ms.
- `FRVIRTplFast`: `planData`, `planData_rows`, `planOf` (= `planOfD … rfl`, `mkPlanF`),
  `planOf_lay`, `planOf_cs`, `nodeIRows_planOf`; the old checked construction is `planOfChk`.
  **`slotLay` changed**: slot `σ ≥ 1` takes slot 0's layout shifted if the slot's compile with it fits
  (`slotLayOk`), else its own `layOf` (one compile pass less).
- **Kernel trap** (found by bisection, `--profile`): any proof step after which the kernel must
  reduce a projection of `bif c then … else …` (or `if`) where `c` is a computed guard
  (`slotLayOk (compileT …) …`) makes the kernel *evaluate the compile*: 60–270 s of type checking.
  Fix: no `let`s and no `unfold`/`dsimp` over the choice; `slot1Of`/`slot1Pick`/`slot1Own`/`withLay`
  as separate definitions, rewritten with their equations and `Bool.apply_cond` only. Likewise
  `rfl` on `(mkPlanF …).cs = slotCST fin` sent the elaborator into `gen` (max recursion): `dsimp only`
  first. `FRVIRTplFast` now 7.4 s.
- **Integrated** (`build-1.log`: `lake build FR FRNodePlan FRNodeDag` green, 2,417 jobs): process start
  with the plan **3.06 s** (`coldwarm-init-1.log`), `planOf` 3.2 s (`planm-1.log`), `evalMT` equal to
  `planOfChk`'s at 5 random points.
- **`CS.tcnt`** (`FRVIRCompile`): `tcount` reads a per-key count table instead of counting `tins`
  (1.46 M key comparisons per pass); `compileX_tcount`: it is the instance count in every compiled
  state; control `tcount_ctl`.
- **Skeleton blocks matched** against the known templates of their shape (`absMatch`, `tryCands`,
  `blockRPC`; `Cands` carried from slot 0 to slot 1) instead of abstracted, hashed and compared:
  the piece check now compares pointers for every instance (pieces 205/222 → 31/33 ms).
  → process start **2.21 s** (`coldwarm-init-2.log`), `planOf` 1.91 s (`planm-2.log`).
- **Grouping** (untrusted): `inputKindsF` (no column lists; same kinds), own order per group
  (`ownIdx`); the compile's zero pass looks the op's key up first (`compMS`), so each template is built
  once. → groupRP 338 → 151 ms; process start **1.93 s** (`coldwarm-init-3.log`).
- **Template blocks matched** at the template level (`reMatch`, `tryBReps`, `mkBlk`; replaces
  `canonT`): kmsOf 194 → 119 ms. → **process start 1.84–1.88 s** (`coldwarm-init-4-*.log`),
  `planOf` 1.61 s (`planm-4.log`; old `planOfChk` 12.2 s in the same process; `evalMT` equal).
- Base process start without the node plan: 0.28–0.30 s (`init-noplan-*.log`); L's plan 54 ms
  (`init-l.log`). The compile itself: 101 ms without templates, 119 ms with memoized templates,
  137–158 ms as `compMS` (`compb-2.log`); three passes per process.
- V (S-E8's method, core 26, `vtime-N-1.log`): runSeq best **182.6 ms**, median 187.8 ms.
  Cold/warm (`coldwarm-1.log`): cold 228.7 ms, warm 190.8–206.4 ms.
- Controls: `insOk_pos/neg/neg_own`, `toPiece_pos/neg/neg_own`, `maxInp_ctl`, `absMatch_ctl`,
  `reMatch_ctl` (`decide +kernel` for the array updates), `tcount_ctl`, `shiftLay_ctl`,
  `slotLayOk_ctl`.
- **Final full build 1** (`build-2.log`, 2,425 jobs, green); dead `blockRP` removed after it.
- Axioms (`axioms.log`): 51 names, only `propext`, `Classical.choice`, `Quot.sound`. Source rule:
  0 findings (`source-rule.log`).
- **V check, alternating with HEAD** (`fr-build-SE13base`, same core, same method): with run patterns
  from slot 0's pieces, V looked 2–3 % slower (`vtime-N-base-2..6`, `vtime-N-final-2..6`);
  `evcmp` (`evalMT` best of 15 at `planOf`, at `planOf` with both slots' patterns, at `planOfChk`):
  71.3–73.2 / 68.8–70.3 / 70.6–71.9 ms (`evcmp-3..5.log`). `mkPats2` (B chosen on slot 0, slot 1's
  runs added) gave the same patterns as slot 0's alone. **Back to `mkPats` over both slots**
  (S-E11's heuristic): `evalMT` 71.1 vs old 73.7 ms (`evcmp-6.log`); V best 184.4 / 175.3 / 184.2
  vs HEAD 182.1 / 178.3 / 185.2 (`vtime-N-*-7..9`); `planOf` 1.63 s, process start **1.87–1.98 s**
  (`final2-coldwarm-init-*.log`; the machine was busier: HEAD's V also rose).
- A dev probe that rebuilt a `Plan` with `{ pl with … hp0 := rfl }` at `pl := planOf fins` was
  OOM-killed at 16 GB while compiling (the elaborator unfolds `planOf`); the probe now uses
  `mkPlanOf … sorry` (dev only).
- HEAD moved to `e1a2444` (P4a/P4b) during the stage: re-snapshotted and rebuilt, green, 2,438 jobs
  (`build-final-head.log`). Final checks: axioms (`axioms.log`), source rule 212 files 0 findings,
  profiles (`prof-final.txt`, `profile-*.log`). RESULT written.
