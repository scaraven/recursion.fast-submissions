# RET-1 RESULT: T4's position-free declarations moved into `FRSoundnessCore*`

This is the preparatory part of step 3 of plan (B) in BLUEPRINT 4.2 §10 "changes 27".

- **Base.** HEAD `60b65cc` at the start. The final build ran on HEAD `4919027` (P4d/R4b, S-E12b)
  plus RET-1's files. Neither commit touches a file that RET-1 edits.
- **Build tree.** `logs/fr-build-RET1`, with `gen.sh`/`snap.sh` from `fr-build-INT6` (org20).
  `MINE.txt` lists RET-1's 28 modules.
- **The "before" tree.** `logs/fr-build-RET1b`, at HEAD `60b65cc`, used only for the timing and
  statement comparisons.
- **Rules followed.** Every lean/lake command ran in the 16G scope under `timeout`. No sub-agents.
  Nothing committed.
- **Records.** Logs and tools are in `logs/RET1/`; the journal is `RET-1-JOURNAL.md`.

## Status

| Check | Result |
|---|---|
| Moved | **204 declarations**: 190 of T4's 195, plus 14 helpers they or T4 need. Same fully qualified names, statements and proofs copied verbatim. The 3.x modules import the Core modules, so every user resolves every name. |
| Not moved | 5 of the 195. See "Left in 3.x" below. |
| `lake build FR FRSoundnessCoreSG` | **green**, 2,481 jobs (`logs/RET1/build-FR.log`) |
| Axioms (`tool/Ax.lean`, `axioms.log`) | All 204 moved names are in an `FRSoundnessCore*` module, none misplaced. Their axioms are only `propext`, `Classical.choice`, `Quot.sound`. `#print axioms` on a sample of 14 agrees. |
| Statements (`tool/StmtHash.lean`, `stmt-{before,after}.txt`) | All 204 types hash-identical before and after. Definition values are identical except one, `clR2`: it now shares the matcher `clR.match_1`, because Lean shares equal matchers within a module. The auxiliary `FR.Snd.clR2.match_1` is gone; no source names it. |
| Source rule (`logs/org20/scripts/source-rule.py` on HEAD + RET-1, `source-rule.log`) | 257 files, 0 findings. On the live worktree it reports 1 finding: `FRVIRSpec.lean:259` "simproc", from G1's uncommitted edit, not RET-1's. |
| Name clashes | None. The build would reject a duplicate, and RET-1 creates no new names. |

## 1. What was built (`loc.py`; `logs/RET1/loc-{before,after}.txt`)

| Module | total / code / thm | Imports | Content |
|---|---|---|---|
| `FRSoundnessCoreDefs` (new) | 98 / 47 / 4 | `FRLog` | `FRSoundnessDefs`' item-list-free part: `L₀`, `EscAtG`, `StabExt`, `lastAns`, `ext1`, `ext`, `condCount`, `pRoundG`, … |
| `FRSoundnessCoreSteps` (new) | 1,024 / 736 / 75 | `CoreDefs`, `FRSumcheck`, `FRProximityFold`, `FRRS` | From `StepA`–`StepE` and `Truths`: the log readers, `clR`/`clR2`/`bindAll`/`bindL`/`Chk2`/`DC`, `mlDoom`/`msD`, the ε arithmetic, the per-round counts |
| `FRSoundnessCoreHide` (new) | 290 / 213 / 24 | `CoreSteps` | From `Ligerito`, `Hide`, `Walk`, `Phases` |
| `FRSoundnessCoreWeights` (new) | 272 / 199 / 17 | `CoreHide` | From `PIOP` (`algebraMap_f₀`), `Weights`, `Fold` |
| `FRSoundnessCoreTail` (new) | 274 / 189 / 26 | `CoreWeights` | From `Tail`, `TailD`, `TailO`, `Compose`, `LigFinal` |
| `FRSoundnessCoreSG` (new, **not theory-only**) | 48 / 29 / 2 | `CoreWeights`, `FRVIRFinalsSG` | `mleN_wSplit` (reads `uHat`) and `eqCellK_eq` (reads `eqCellK`). It merges into `CoreWeights` once step 4 moves `uHat`/`eqCellK` out of `FRVIRFinalsSG`. |
| 19 edited 3.x modules | 7,545 / 5,288 / 497 → 5,891 / 4,021 / 349 | each adds `import FRSoundnessCore…` and a `-- RET-1:` pointer line | the moved chunks deleted, nothing else changed |
| **all 25 modules** | 7,897 / 5,434 / 497 | | +146 code lines: the namespace, `open`, `variable` and `section` lines replicated in Core |

- **The Core modules are a linear chain.** It follows the 3.x import order, which is also the
  order of the declarations' dependencies.
- **What they import.** The theory (`FRSumcheck` → `FRMLE`, `FRRS`, `FRProximityFold`), `FRLog`
  (→ `FRTranscriptDefs`, `FRMerkle`, `RecursionFast.Library.Security`) and the contract.
  `FRLog`/`FRTranscriptDefs` are needed for `Log`, `Digest`, `Bad`, `pathOf`, `entriesOf`,
  `squeezeQ`, `bytesAt`, `Item` and `fsCheck`.
- **What they do not import.** No 3.x positions, no 3.x verifier, no `FRVIR*`.
  `FRLog`/`FRTranscriptDefs` also *define* `fsItems` and `Kind`, but no moved declaration
  reads `fsItems`, `fsStarts`, `fsRanges` or `items`. Both modules are in the revision 4.1
  frame's closure anyway (`FRSoundness4Frame` → … → `FRLog`).
- **The mover is mechanical** (`logs/RET1/tool/chunks.py`, `move.py`, `post.py`):
  - A declaration chunk is its doc comment, attributes and `open/set_option/omit … in` prefix,
    plus the command.
  - Core keeps every context command (`namespace`/`section`/`variable`/`include`/`open`/
    `set_option`), so each declaration elaborates in the same context. Sections left without a
    declaration are pruned.
  - `open Circ`, `FRVIRTplCore`'s namespace, is dropped from Core. No moved declaration uses it.

**T4's imports (import edits only):**

| T4 module | Import change |
|---|---|
| `FRSoundness4TailStep` | `FRSoundnessLigFinal` → `FRSoundnessCoreTail`, `FRSoundnessCoreSG` |
| `FRSoundness4TailTruths` | + `FRRSEval`, `FRBlockStream`: theory modules that reached it through 3.x `Truths` (`encF`, `coeffsOfValuesD`, `wAtD`) |
| `FRSoundness4TailLig` | + `FRSoundnessTail`, **only for the control `tail_shift`**. It states T4's positions as 3.x's `p1Start`/`cStart`/`p3S0`/`pfStart`/`capPos` + 14. |

## 2. Move table (`logs/RET1/move-table.md`; † = helper not in `keep.txt`)

| Core module | from (3.x) | n | declarations (`FR.Snd.` omitted; † = helper, not in `keep.txt`) |
|---|---|---|---|
| `FRSoundnessCoreDefs` | `FRSoundnessDefs` | 12 | `EscAtG`†, `L₀`†, `StabExt`†, `badCount_frac_le`†, `condCount`†, `ext`†, `ext1`†, `ext_append`†, `ext_dropLast`†, `ext_nil`†, `lastAns`†, `pRoundG`† |
| `FRSoundnessCoreSteps` | `FRSoundnessStepA` | 14 | `Agree`, `Agree.mono`, `Agree.symm`, `agree_append`, `ansAt`, `coordAt`, `entAt`, `entAt_append`, `fAt`, `kAt`, `msgAt`, `posAt`, `readF`, `readK` |
| `FRSoundnessCoreSteps` | `FRSoundnessStepB` | 30 | `N_le_deltaR`, `TruthLocal`, `bindAll_append`, `bindAll_size`, `clR`, `clR_congr`, `clR_log_congr`, `condCount_eq_zero`, `deltaR`, `deltaR_coe`, `entAt_ext1`, `epsD`, `epsD_add_epsH`, `epsD_coe`, `epsH`, `epsH_le_epsR`, `epsR`, `err_le_epsD`, `g3At`, `g3_check`, `g3_size`, `h_le_epsD`, `h_le_epsR`, `length_ext`, `peval_four`, `rch`, `rchs`, `rchs_congr`, `rchs_succ`, `three_le_deltaR` |
| `FRSoundnessCoreSteps` | `FRSoundnessStepC` | 19 | `DC`, `DPos`, `ansAt_ext`, `card_idx_in`, `card_pos_in`, `condCount_congr`, `idx_lt`, `length_ext1`, `mem_map_val`, `p2_round_le`, `pc`, `pc_last`, `round_row_F`, `round_row_K`, `single_F_le`, `single_K_le`, `sum_pc`, `vAt`, `vAt_of_lt` |
| `FRSoundnessCoreSteps` | `FRSoundnessTruths` | 13 | `ans_lt_of_carried`, `bytesAt_extract40`, `cap_carried`, `card_inter_ge`, `colL_frEncW`, `colL_take`, `colL_take_own`, `frEncW`, `hide_round_le`, `not_hit_of_not_bad`, `pre_take_own`, `sum_range_two_mul`, `wSplit` |
| `FRSoundnessCoreSteps` | `FRSoundnessStepD` | 6 | `card_coords_empty`, `card_coords_in`, `card_coords_univ`, `coordsOf`, `coords_prob`, `coords_round_le` |
| `FRSoundnessCoreSteps` | `FRSoundnessStepE` | 30 | `Chk2`, `TruthLocal2`, `bindL`, `bindL_append`, `bindL_size`, `clR2`, `clR2_congr`, `coord_le_deltaR`, `coord_rows_le`, `flat_round_le`, `g2At`, `isQ`, `ite_neg'`, `ite_pos'`, `mlDoom`, `mlDoom_nil`, `mlDoom_step`, `ml_round_le`, `msD`, `msD_inside_last`, `not_mlDoom_zero`, `pairsEquiv`, `pairsEquiv_apply`, `rch2`, `rchs2`, `rchs2_congr`, `rs1_round_le`, `seq_round_le`, `step_add`, `take_ext` |
| `FRSoundnessCoreHide` | `FRSoundnessLigerito` | 1 | `FR.eqBits_eq_eq` |
| `FRSoundnessCoreHide` | `FRSoundnessHide` | 11 | `bindL_mle`, `entAt_ext_lt`, `entAt_take`, `err_le_epsH`, `err_total`, `fsCheck_absorb_default`, `fsCheck_absorb_squeezeQ`, `fsCheck_ext_ge`, `hEll`, `hide_N_le`, `mlDoom_toy` |
| `FRSoundnessCoreHide` | `FRSoundnessWalk` | 10 | `back_take`, `entriesOf_pathOf_take`, `entriesOf_prefix`, `entriesOf_take`, `not_bad_take`, `pathOf_eq`, `pathOf_lt`, `pathOf_prefix`, `pathOf_take`, `predIdx_take` |
| `FRSoundnessCoreHide` | `FRSoundnessPhases` | 3 | `batch_N_le`, `batch_single`, `batch_single_true` |
| `FRSoundnessCoreWeights` | `FRSoundnessPIOP` | 1 | `algebraMap_f₀`† |
| `FRSoundnessCoreWeights` | `FRSoundnessWeights` | 12 | `bitProd_dbl`, `eqCell`, `foldW`, `foldl_mulK`, `mleN`, `mleN_foldW`, `mleN_w0F`, `mle_bitProd`, `mle_ind`, `uK_sub_one`, `w0F`, `w0F_cell` |
| `FRSoundnessCoreWeights` | `FRSoundnessFold` | 11 | `CloseN`, `algebraMap_eqBits`, `closeN_fold`, `closeN_unfold`, `evOdd`, `foldN`, `jointClose_equiv`, `mlDoomF_step`, `not_mlDoom_nine`, `sum_eqBits_one`, `two_pow_sub` |
| `FRSoundnessCoreTail` | `FRSoundnessTail` | 14 | `bindL_range_getD`, `e2`, `e2_deg`, `eqBits_congr`, `getD_bindAll`, `ofFn_getD`, `sum_eqBits_succ`, `tabs`, `tabs_getD0`, `tabs_getD1`, `tabs_size`, `trueSum_e2`, `trueSum_tabs`, `trueSum_tabs_fold` |
| `FRSoundnessCoreTail` | `FRSoundnessTailD` | 1 | `clR2_same` |
| `FRSoundnessCoreTail` | `FRSoundnessTailO` | 2 | `agree_ext`, `hEll_le` |
| `FRSoundnessCoreTail` | `FRSoundnessCompose` | 1 | `N_le` |
| `FRSoundnessCoreTail` | `FRSoundnessLigFinal` | 11 | `K_ofBytes_zero`, `bindL_ofFn_mle`, `bytesAt_empty`, `fin_append_nat`, `length_take_succ`, `mleP`, `mleP_pad`, `mleP_pt_split`, `mleP_zero`, `msgAt_nil`, `readK_nil` |
| `FRSoundnessCoreSG` | `FRSoundnessWeights` | 2 | `eqCellK_eq`, `mleN_wSplit` |

**Left in 3.x (5 of the 195):**

| Declaration | Module | Why it stays |
|---|---|---|
| `wE`, `mle_wE`, `sum_wE` | `FRSoundnessWeights` | They need `rowMat` (PIOP), which needs `FR.Eval.entriesOf` in `FRVIREval`. `FRVIREval` imports `FRNodeLayout`, `FRVIRMux` and `FRVIRCompileSound`. T4 does not use these three. |
| `truthP1_zero.sum_mul_sum_comm` | `FRSoundnessWeights` | A `where` auxiliary of `truthP1_zero`, which reads `lvl κ`/`fF κ` (kind-dependent). Unused by T4. |

**Notes on the moved set:**
- **Kind and ladder.**
  - `hEll_le` is moved. Its statement is `hEll i ≤ 6`. Its proof unfolds
    `lvlStar = lvl .L32`, so the proof term names `Kind.L32`; T4's own audit whitelists
    `lvlStar`.
  - `hEll` (`(lvlStar i).ell`) is likewise position-free.
- **Items.** `cap_carried` and `fsCheck_absorb_*`/`fsCheck_ext_ge` read the generic `Item` and
  `fsCheck`, not a 3.x item list. Revision 4.1's `G.Matches` uses the same `fsCheck`.

## 3. Import closure of the Rev4 theorem's modules (`logs/RET1/closure.py`)

**Roots:** `FRSoundness4Frame`, `FRSoundness4Tail*`, `FRSoundness4P4*`, `FRSoundness4R4*`,
`FRNodeCircuit4*`, `FRX4*`; 44 roots at HEAD `4919027`. The files are
`closure-{before,after,hypo}{,-T4}.txt`.

| Measure | Before (HEAD) | After (HEAD + RET-1) | + `tail_shift` moved out (hypothetical) |
|---|---|---|---|
| All 44 roots: FR modules in the closure | 229 of 251 | 235 of 257 (+6 Core) | 235 of 257 |
| All roots: 3.x soundness modules in it | **62** | **62** | 62 |
| T4's 11 `FRSoundness4Tail*` roots: modules | 126 | 125 | **113** |
| T4 roots: 3.x soundness modules | **22** | **15** | **3** (`FRSoundnessDefs`, `FRSoundnessStepA`, `FRSoundnessFrChain`, all via `FRSoundness4Pos`) |

**Why the whole closure still holds 62 3.x soundness modules.** Revision-4 modules owned by other
tracks import 3.x modules directly. The edges, after RET-1:

```
FRSoundness4P4aNames -> FRSoundnessFrZM      FRSoundness4R4Ref -> FRSoundnessAccSem
FRSoundness4P4aSeg   -> FRSoundnessExtLeaf   FRSoundness4R4Rnd -> FRSoundnessFrRndV
FRSoundness4P4bNames -> FRSoundnessFrPend    FRSoundness4R4Run -> FRSoundnessFrRun
FRSoundness4Pos      -> FRSoundnessFrChain, FRSoundnessStepA
FRSoundness4TailLig  -> FRSoundnessTail      (RET-1; before: FRSoundness4TailStep -> FRSoundnessLigFinal)
FRXLevel             -> FRSoundnessTruths
```

- **The front chain pulls the whole 3.x tail back in.** `FRSoundness4P4aNames` → `FrZM` → `FrBind` →
  `FrS` → `FrSh` → `AccEq` → `AccVal` → `AccSeg` → `AccSem` → `AccPos` → `AccFin` →
  `AccRun` → **`FRSoundnessLigFinal`** → `Compose` → `FRKState`, and with them the rest of the
  3.x tail, `FRSoundnessWeights` → `FRVIRFinalsSG` included.
- **What each edge uses** (`tool/Edges.lean`, `edges.txt`, run before `FRSoundness4R4Rnd` landed).
  All of it is positional or front-specific, and none of it is in Core:
  - `P4aNames`: `FrL`/`FrZ`/`FrS`/`FrZM`/`FrPend` (`vL`, `c0L`, `kMat`, `pzL`, …);
  - `P4aSeg`: `FrZM`/`FrSh`/`ExtLeaf`;
  - `P4bNames`: `Rows`, `Tail` (`Same`), `StepB`'s `D3`, `StepE`'s `D2`, `Truths`' `wordK`,
    `PIOP`'s `fF`/`rowMat`, `StepA`'s `capPos`/`kindOf`, `FrE`/`FrW0`/`FrRS0`, `Front`'s `Reads`;
  - `Pos`: `FrChain`'s `G.*`, `StepA`'s `phStart`/`fsStarts`/`fsStarts_eq` (S-G13's position
    certificate);
  - `R4Ref`/`R4Run`: `AccSem`/`AccRun`/`FrRun`/`FrChain`;
  - `FRXLevel`: `Truths`' `foldAt`, `sAt`, `wordK`, `msgOf`, `farL`, `decodeL`, …, `StepC`'s
    `lvN`/`lvK`/`lvE`, `StepA`'s `wordOf`.

  These are the declarations that T4 *copied* into `FR.Snd.T4`. Each importer has to switch to
  T4's copies, or to its own port, before step 3 can retire the 3.x front.
- **The 3.x verifier shapes stay in T4's closure** through `FRSoundnessCoreSG` → `FRVIRFinalsSG`
  (`FRNodeLayout`, `FRVIRMux`, `FRVIRCompileSound`, `FRVIRFinalsSF`). They also come in through
  `FRSoundness4Frame` → … → `FRVIREval`. Both are step 4's.

## 4. What remains in 3.x that the Rev4 closure still needs

1. **T4's chain** (owner T4 / S-G):
   - `tail_shift` in `FRSoundness4TailLig` is the only reason for `import FRSoundnessTail`.
     Moving that one control unchanged into its own module outside the closure (for example
     `FRSoundness4TailShift`, importing `FRSoundness4TailLig` and `FRSoundnessTail`) takes T4's
     3.x soundness modules from 15 to 3.
   - The brief allowed import edits only in T4's modules, so RET-1 did not move `tail_shift`.
2. **`FRSoundness4Pos`** (S-G13) imports `FRSoundnessStepA` for `phStart`/`fsStarts`/
   `fsStarts_eq` (3.x positions, used in `phStart4_shift`) and `FRSoundnessFrChain` for the
   generic `G.*` chain and potential.
   - `FrChain` (712 lines) is position-free except its `fs3` instance part. It is the next
     candidate for Core (`FRSoundnessCoreChain`).
   - `StepA`'s positions are needed only by the shift certificate, which could move to a control
     module like `tail_shift`.
3. **`FRSoundnessCoreSG`** depends on `FRVIRFinalsSG`'s `uHat` and `eqCellK` (step 4:
   `FRVIRFinalsCore`).
4. **The other tracks' edges** listed in §3: P4a/P4b → `FRSoundnessFr*`/`Rows`/`Front`/
   `StepB,E`/`Truths`/`PIOP`; R4 → `Acc*`/`FrRun`/`FrRndV`; `FRXLevel` → `Truths`/`StepC`.
   Until these move, the 3.x front (`Fr*`, `Acc*`) and through `AccRun` → `LigFinal` the whole 3.x
   tail stay in `Solution`'s closure, whatever T4 imports.

## 5. Times (sequential: `taskset -c N lake env lean -DElab.async=false --profile`; `logs/RET1/times.txt`, `prof/`)

| Set | Wall, summed | Kernel (profiler's "type checking", summed) |
|---|---|---|
| 19 3.x modules before (`fr-build-RET1b`, HEAD `60b65cc`) | 262.1 s | 40.2 s |
| the same 19 after | 213.7 s | 36.1 s |
| the 6 Core modules | 55.7 s | 0.2 s |
| **total after** | **269.4 s (+7.3 s, +2.8 %)** | 36.2 s |

- **The +7.3 s is start-up.** Each module load costs ≈ 5.7–7 s; the smallest modules,
  `FRSoundnessLigerito` and `FRSoundnessPhases`, take 7.0 s and 5.7 s. The 6 new modules add
  ≈ 36 s of it. Without start-up, elaboration fell by ≈ 29 s. The comparison is two runs on
  different cores of a shared VM, and the "before" run overlapped RET-1's own `lake build`.
- **So, sequentially, the move costs a few seconds and does not save any.** The saving comes later,
  when step 3 retires the 3.x modules: 213.7 s is what is left to remove, against 262.1 s before.
- **In a parallel build the critical path for T4 gets shorter.** T4's chain used to wait on all 19
  3.x modules up to `FRSoundnessLigFinal` (262 s sequential). It now waits on `CoreDefs` →
  `CoreSteps` → `CoreHide` → `CoreWeights` → `CoreTail` (49 s) and `CoreSG` (after
  `FRVIRFinalsSG`). `FRSoundness4TailLig` alone still waits on 3.x `Defs`…`Tail`, until
  `tail_shift` moves.

## 6. Deviations

- **`FRSoundnessCoreSG` is not theory-only** (it reads `FRVIRFinalsSG`). Without it,
  `FRSoundness4TailFold`'s use of `mleN_wSplit` would keep T4 on 3.x `FRSoundnessWeights` and the
  whole 3.x chain below it.
- **The grouping differs from the blueprint's names** `Core{Steps,Weights,Tail,Lig}`: here they are
  `Core{Defs,Steps,Hide,Weights,Tail,SG}`.
  - `CoreDefs` is split off so that `FRSoundnessDefs`, and through it `FrChain`/`Pos`, keep
    importing only `FRLog`.
  - LigFinal's 11 declarations sit in `CoreTail`.
- **The blueprint's per-module counts** (StepB 30, StepE 28, StepC 18, Weights 17, …) **differ
  slightly from `keep.txt` resolved through `deps.txt`**: StepE 30, StepC 19, Weights 18,
  StepA 14, Truths 13.
- **`FR.lean` is unchanged.** The Core modules are built as dependencies of the 3.x modules.

## 7. Open questions / requests

1. **T4 / orchestrator:** may `tail_shift` move into a control module outside the Rev4 closure
   (§4.1)? It is a pure move, with no statement or proof change.
2. **S-G13 (`FRSoundness4Pos`):** next candidates for Core are `FRSoundnessFrChain`'s generic
   part (`G.*`) and `Defs`' Parts A–C. `phStart4_shift`'s comparison with 3.x positions could
   become a control outside the closure.
3. **Step 4 (S-0′/S-E):** when `uHat`/`eqCellK` move to `FRVIRFinalsCore`, merge
   `FRSoundnessCoreSG` into `FRSoundnessCoreWeights`.
4. **P4a/P4b/R4/S-H:** the direct 3.x edges in §3 block retiring the 3.x front. Each importer
   needs T4's copies (`FR.Snd.T4`) or its own port.
