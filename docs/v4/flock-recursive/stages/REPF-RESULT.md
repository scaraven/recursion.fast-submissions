# REPF (track L-circ): RESULT — the previous node's replay folded into `nodeIRows4`, and the replay part of `Gaps4` discharged

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `77bfc19`; final build on
**HEAD `91e0d61`** + REPF + the build-tree-only RTOkW switch of §5 (measurements on `ae8b8d8` + REPF). Build tree `logs/fr-build-REPF` (copy of
`fr-build-C1b`). Logs `logs/REPF/`. Every lake/lean/probe in a 16 GB scope under `timeout`. No sub-agents,
nothing committed, no `sorry` in the worktree. Journal: `REPF-JOURNAL.md`.

## 0. Verdict

| Item | State |
|---|---|
| 1. Split | **Done**: `FRNodeRows4Defs` (definitions only, moved verbatim, names and namespaces kept); `askTG`/`XofT` untouched in `FRNodeRows4` |
| 2. Fold | **Done**: `nodeIRows4 κ = (slots: slotRows4 ++ arIRows4 ++ linkIRows4) ++ repAllRows κ`; `hfit4` re-proved, statement unchanged |
| 3. Plan | **Done and correct** (`evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX`, `slots_val` textually unchanged; MxKat PASS; `plan4t check` §4.3). `tplLW`'s 216 s init fixed. |
| 4. Fold lemma | **Done** (`arRepOf_eq`, `repRowsP_trail`; every `RT`, no locality/SSA argument) |
| 5. Discharge | **Done in the build tree**: `gaps4_of_runA`, `gap4Imp_rtC1c` (compose with ASK-T's `gap4Imp_of_askT`); needs the 36-line RTOkW diff to ASK-T's `FRNodeRun4`/`4S`/`4Ctrl` (§5, `logs/REPF/wswitch.diff`) |
| **V(N4)** | **over the stop line**: best **1,784.6 ms** own kind, **1,826.8 ms** full support (HEAD 445.0 / 484.3), `logs/REPF/vtime-ab.log`. Per the brief (> 1.6 s VM): **stopped, not optimised** |
| **Plan init** | **+12.3–12.6 s wall** (`plan4t init`: HEAD 7.49–7.89 s, REPF 19.83–20.51 s; RSS 0.52 → 1.95 GB; `plan4t-init-ab.log`). The +1 s target needs the closed forms (§6) |
| Build | `lake build FR Solution FRSubmission4Fin` green at `91e0d61` + REPF + §5 diff, 2,676 jobs (`logs/REPF/final.log`); probes built at `ae8b8d8` (`full5.log`) |
| Axioms / source rule | 34 declarations ⊆ {propext, Classical.choice, Quot.sound}; 455 files, 0 findings (§7) |
| Kernel | ≈ +4.5 s (`FRNodeRows4Fit` +3.5 s), §8.4 |

## 1. The split (`FRNodeRows4Defs`, new; definitions only)

Moved verbatim (`logs/REPF/tools/mover.py`, plans `plan1.txt`/`plan2.txt`): from `FRNodeRows4`: `mapC`,
`rowMapC`, `selIx`, `oneR`, `selR`, `baseR`, `protoP`, `isPrevSlot`, `protoOf`, `protoProg`, `protoLay`,
`protoF`, `nodeOf`, `maskQ`, `protoR`, `mvC`; from `FRNodeRows4Rep*`/`RsK`/`LT`: `RT`, `RT.none`,
`repRowsX`, `linLt`, `Xof`, `repRowsP`, `repBase`, `zeroRows`, `isLinkW`, `RT.orElse`, `rejRow`, `outsOk`,
`outF`, `copyRows`, `kOps`, `KOp`, `kIx`, `kBlocks`, `kSig`, `kTpl`, `kIns`, `kRows`, `rtK`, `zeroLin`,
`bndZ`, `isST`, `stOut`, `stRows`, `rtST0`, `isLW`, `lwArgs`, `lwIn`, `lwT`, `kLW`, `rtLinkSegW`, `repB`,
`cbLW`, `rtN0`, `repMapC`, `repRow0`, `repIRowsW`, `akS`, `rsShape`, `kIn`, `cIn`, `rsT`, `isRS`, `rsArgs`,
`rsIn`, `kRS`, `cbRS`, `rtRs`, `rtN0R`, `isTS` … `kEvL`, `cbTS`, `cbEvL`, `rtN0c`, `rtC1c`. New there:
`repSegB`, `gatesAtGo`, `rowsTR`. Imports: `FRVIR4Mux`, `FRVIRTplFast`, `FRVIRTplSet`, `FRNodeKinds4`,
`FRNodeRows4Hint`, `FRVIRTplKMux`, `FRVIRTplRepLW/LD/T`, `FRNodeRows4RepRs` (all below `FRNodeRows4`).
`FRNodeRows4` imports it; every downstream user is unaffected (the theorems stay where they were).
`FRNodeRows4AskPosT`'s imports are unchanged.

## 2. The fold (`FRNodeRows4`, `FRNodeRows4Fit`)

- **`repAllRows κ`** = `if ArFit then (if RepFit then (range vslots).flatMap (repIRowsW rtC1c κ) else
  [(repSegB, rejR κ)]) else []`; `nodeIRows4 κ = (… as before …) ++ repAllRows κ`. **`RepFit`**
  (`repFitB`, `repCellOk`): prototype 0's replay rows ≤ 2^20, every cell a frame cell `< 2^20` or a local
  in `[repB, repB + 2^20)`; prototype 1's ≤ 2^10 rows on region-1 frame cells. The plan checks it.
- **Placement.** Slot 0 (`N2`, `N4`; prototype 0): rows `κ.vslots·2^20 + k`, `k < 845,862`; frame cell
  `c ↦ oneCell + c`, local `repB + j ↦ oneCell + κ.vslots·2^20 + j` (`repMapC`). Segment slot `v`
  (prototype 1, `rtLinkSegW`, 8 rows): rows `v·2^20 + repSegB + k`, **`repSegB = 31·2^15 − 2^10 =
  1,014,784`** (orchestrator / IMPC2; S-E14's `repBase = 23·2^15` lies inside ASK-T's template-row range).
- **Fit** (`FRNodeRows4Fit`, new lemmas): `repConsts`, `ar_idx_hi` (arena rows end below `arRb + arNb`),
  `slotA_idx`, `repIRowsW_mem`, `repFitB_spec`, `prevSlot_of`, `prev_room`, `repReg`, `rep_fit1`,
  `repReg_inj`, `rep_fit`; **`hfit4` re-proved, statement unchanged**.
- `mem_node_slot/ar/link`: proofs only; new `mem_node_rep`.

## 3. The plan (`FRNodeRows4RepFD`, `FRNodeRows4Plan`, `FRVerifierImplNode4F`)

- **One pass** (`trailMR`): ASK-P's memoized trail with a second accumulator; `arRepOf π` gives the ask
  rows and the replay rows of prototype `π` (it replaces `arOf`; no second compile, the 131 s trap gone).
- **Fold lemma** **`arRepOf_eq π : arRepOf π = (askRowsT π, repRowsP (rtC1c π) π)`**, from
  **`trailMR_eq`** (both accumulators are `trailRows`/`repRowsX`); **`repRowsP_trail`** for any `RT`.
  This replaces C1b §5.2's `repRowsFin` plan: no SSA/locality argument is needed.
- `Plan4`: `rp0 rp1 : Thunk (Array Row)` + `hrp` (fallback only, recomputed on demand), `rgF rgL : GRows`
  + `hrg` (slot 0's replay rows in local coordinates: frame part `repLocF`, local part `repLocL`,
  grouped `2^11 × 2^12`); `inR` adds `repFitB 0 && repFitB 1`; **`hR : inR → ProtoFit ∧ lowKeys ∧ ArFit ∧
  RepFit`**.
- V: `LCx.rv` (`rvOf`: one thunk per call, `growsVal3` of `rgF`, `rgL` at 20 row/20 cell coordinates,
  low tables shared with the link context) — **shared by `N2` and `N4`**; `repV4` = for slot 0
  `hiF t vs · u_lm u_lm+1 · (hiF u 0 · rv.1 + hiF u vs · rv.2)` (**`repV0_eq`**, **`repV4_eq`**), for a
  segment slot the 8 rows sparse (`repIRowsWP`). `slotV4 := slotV4o + repV4`; `slots_val` re-proved
  (statement unchanged).
- `tplLW` (C1b §5.4): **`tplLWg`** over the tables built once (`let`); the spec accessors are now
  `abbrev`s over the generic ones; **`tplLW_eq`** (`tplLW` = the spec form); `tplLW_ok` re-proved,
  statement unchanged. `linkWAll`'s rows now take a fraction of a second (`RepInit`).
- **Process-start trap (fixed):** module initialisers run on the 8 MB process stack (`main` gets a big
  stack via `lean_run_main`); `Tpl.rows`' `gatesAt` is not tail-recursive and `tplEvL .N8` has 150,726
  gates, so `plan4t` aborted with a stack overflow (passing with `ulimit -s ≥ 64 MB`). **`rowsTR`**
  (`gatesAtGo`, **`rowsTR_eq`**) in `kRows` fixes it (probe `RepInit2`/`RepInit3`). **Other tracks:
  any template of > ~60 k gates built at process start needs `rowsTR`.**

## 4. Measurements

### 4.1 V (`abv.sh`, 3 rounds × 21, core 27, `logs/REPF/vtime-ab.log`; MxKat ran on core 30 meanwhile)

| | HEAD `ae8b8d8` (`askt-bin`) | **REPF** |
|---|---|---|
| V(N4), own kind | 445.0 best / 479.3 median | **1,784.6 / 1,909.9** |
| V(N4), full support | 484.3 / 507.6 | **1,826.8 / 1,918.7** |
| `evalMT4` N4 | 322.3 | 1,692.8 |
| `evalMX4` support all | 388.2 | 1,742.3 |

The replay piece costs ≈ +1.37 s (5.71 M terms, 845,862 rows; ≈ 0.24 µs per term), **once per call**:
full support costs +42 ms over own kind (HEAD: +39), so the N2/N4 sharing works. **1.78–1.83 s is above
the 1.6 s VM stop line** (and 0.2 s from the 2.07 s DoS cap on a 7763 at 1.19×: ≈ 2.1–2.2 s there).
Not optimised (brief). Where the time is: `rsWeight` ≈ 2.99 M terms, `evalL` ≈ 1.68 M, `targetS` ≈ 0.31 M,
`linkWAll` ≈ 0.20 M (C1b/R3 counts; total 5.71 M measured, `logs/REPF/repinit2b.log`).

### 4.2 Plan init (`plan4t init`, core 28, 3 alternating rounds, `logs/REPF/plan4t-init-ab.log`)

HEAD 7.49 / 7.55 / 7.89 s wall (7.1–7.5 user, 0.52 GB); **REPF 19.83 / 20.30 / 20.51 s** (19.0–19.7 user,
1.95 GB): **+12.3–12.6 s**. Breakdown (probe `RepInit`, main thread, `logs/REPF/repinit2b.log`,
`repinit1.log`): `arRepOf 0` 7.4 s (the trail ≈ 0.85 s it already paid + the template rows ≈ 6.5 s:
`evalL`, `rsWeight` dominate), `repFitB` 1.2–1.8 s, `repLocF` 1.0 s, `repLocL` 1.5 s, `grows` 0.6 + 1.9 s,
`arRepOf 1` 0.8 s (was `arOf 1`). The orchestrator's ≤ +1 s needs the closed forms (§6); sparse rows
cannot get there.

### 4.3 Correctness at run time

- **MxKat PASS** (`logs/REPF/mxkat.log`): `evalMT4` (all kinds) and `evalMX4` (all 8 supports) equal a
  reference whose replay part is the plain sparse sum `rows3 lm (lm+2)` of each slot's `repIRowsWP` at the
  kind's coordinates (independent of `repV4`'s shared local values), 3 random points.
- **`plan4t check`** (`evalMT4` vs the sparse sum over `nodeIRowsP`, which now holds the replay rows):
  **N2 equal true, N4 equal true** (§9; N8 was still running at the freeze).

### 4.4 Kernel CPU (`lean -DElab.async=false --profile`, one core; `logs/REPF/prof-summary.txt`)

See §8.4.

## 5. The discharge and the exact switch

**`FRNodeRows4RepF`** (new):
```lean
theorem repFit_of (hone : w κ.oneCell = 1) (hE : truthEI (nodeIRows4 κ) w) : ProtoFit ∧ ArFit ∧ RepFit
theorem repFold (hone) (hE) : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rtC1c κ v, p ∈ nodeIRows4 κ
theorem repOk_rtC1cB : RepOk rtC1c Sub4.implB (fun _ => Sub4.implB)
theorem gap4Imp_rtC1c (hS : StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunA (rtC1c (protoOf κ v)) (withImpc askAq (protoOf κ v)) (implP implB (fun _ => implB) (protoOf κ v) ι)
        (protoOf κ v) ι (slotIn …) (slotTr …) (slotAsg κ v w)) :
    ∀ v, Active4 (rd4 X.pf4) κ w v → SlotImp implB (fun _ => implB) κ v w (slotIn …) (slotTr …)
theorem gaps4_of_runA (h : ∀ vk κ w c₁ c₂ ch, StmtN4R … → ∀ v, Active4 … → ∀ ι, SelOk … →
    SlotRunA (rtC1c (protoOf κ v)) (withImpc askAq (protoOf κ v)) …) : Sub4.Gaps4
```
**How it composes with ASK-T:** `gap4Imp_of_askT hT₀ hT hok hfoldR hS h` takes `hok : RepOk rt impl₀
base` and `hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ`. At `rt := rtC1c`,
`impl₀ := implB`, `base := fun _ => implB`: `hok := repOk_rtC1cB`, `hfoldR := repFold (one_of_pubCells
hS.1.2.2.2.2) hS.1.2.2.2.1` (`gap4Imp_rtC1c` is exactly this). The same two terms fill the replay
hypotheses of `gap4Imp_of_run`, `gap4Imp_of_runS`, `gap4Imp_of_rsv` and IMPC's `gap4Imp_of_impc(R)`.
What is left in `SlotRunA` at `rtC1c`: the residual imports exclude prototype 0's `shiftTarget`,
`linkWAll`, `rsWeight`, `targetS`, `evalL` and prototype 1's `linkWAll`.

**The switch (RTOkW).** In the worktree, `RepOk`, `RepHolds` and `repIRows4` (`FRNodeRows4Rep`, mine)
are now *by definition* the `RTOkW` forms (`RepOkW`, `RepHoldsW` at `repAsg`, `repIRowsW`): every theorem
stated over them keeps its text. S-E14's `slotImp_of_rep`, `repHolds_of`, `gap4Imp_of_rep` moved to
`FRNodeRows4RepW` with the same statements. B3's run must take the replay rows at the spare region's
assignment; the **exact diff** (36 changed lines, `logs/REPF/wswitch.diff`, applied by
`logs/REPF/tools/wswitch_bt.py`; ASK-T's files, not edited here) is:

- `FRNodeRun4.compileFromX_run`: binders `{w w' : Asg} {B : ℕ}`, `(hP' : SelOk w' P κ) (hAg : Agree B w w')
  (hR : RTOkW impl X rt κ B)` for `(hR : RTOk impl X rt κ)`; its replay-rows premise and the local
  `hrr'`, `hrows` at `w'`; the call `(hR P cs op hc).2 inp w w' s.regs vs ok hP hP' hI hAg hrows hev hio`;
  the two recursive calls `compileFromX_run hX hP hP' hAg hR hA …`.
- `FRNodeRun4.compileX_run`: the same binders/hypotheses (`(hR : RTOkW impl X rt κ B)`, `(hP' …) (hAg …)`
  after `hP`, `hrr` at `w'`), and the call `compileFromX_run hX hP hP' hAg hR hA …`.
- `FRNodeRun4S`: `import FRNodeRows4RepW`; in `slotImp_of_runA`:
  `compileX_run hX (hok _ hπ ι) hA (baseR (protoOf κ v)) hS (selOk_repAsg hS) (agree_repAsg κ v w) he hrows.1 …`.
- `FRNodeRun4Ctrl.run_ctl`: `(RT.none_okW _ _ _ 0)` for `(RT.none_ok _ _ _)`, and `selOk_ctl selOk_ctl
  (fun _ _ => rfl)` for `selOk_ctl`.

**The orchestrator must merge this diff together with REPF's files** (the worktree's `FRNodeRun4S` does
not build against REPF's `RepOk` alone). Then FR imports `FRNodeRows4RepF` and `FRNodeRows4RepFCtrl`.

## 6. Open items (for the orchestrator)

1. **V (1.78–1.83 s) and init (+12.3 s) need the closed forms** (C1b §6.1 `evalL` carry split, R3 §4.2
   `rsWeight` chains/stage instances, C1b §6.2 `targetS`): each op's rows are a separate block of
   `repRowsP` (program order), so a closed form can replace one op's piece of `rv` with its own
   `= rows3` lemma; the fold, the fit and the discharge do not change.
2. Cheap init levers inside the sparse route (not taken: brief): one pass for `repFitB`+`repLocF/L`
   (≈ −2 s), skip `repLocF`'s copy by grouping directly (≈ −1 s).
3. `plan4t check` N8 (§9).
4. ASK-T's `FRNodeRun4AskT` renamed its `ctlP` (`b52ee6e`); REPF renamed `FRNodeRows4RepCtrl`'s to
   `repCtlP` too (harmless).

## 7. Hygiene

- **Axioms** (`logs/fr-build-REPF/ax/AxREPF.lean`, `logs/REPF/axioms.log`): 34 declarations, among them
  `gaps4_of_runA`, `gap4Imp_rtC1c`, `repFold`, `repFit_of`, `hfit4`, `rep_fit`, `evalMT4_eq`, `evalMX4_eq`,
  `implN4F_hMX`, `slots_val`, `repV0_eq`, `repV4_eq`, `arRepOf_eq`, `trailMR_eq`, `tplLW_ok`, `rowsTR_eq`,
  `compileX_run` (switched), `certificate_sub4`, `certificate_sub4F`: all ⊆ {propext, Classical.choice,
  Quot.sound}, no `sorryAx`.
- **Source rule**: `submissions/flock-recursive`, 455 files, **0 findings** (`logs/REPF/source-rule.log`).
- No `sorry` in the worktree or the build tree. `decide` only in controls on literals/toy rows.

## 8. Files, statement changes, line counts, kernel time

### 8.1 Files (absolute paths under `/home/devops/Verified-zkEVM/recursion.fast-submissions-rev44/submissions/flock-recursive/lean/`)

New: `FRNodeRows4Defs.lean`, `FRNodeRows4RepFD.lean`, `FRNodeRows4RepF.lean`, `FRNodeRows4RepFCtrl.lean`.
Edited: `FRNodeRows4.lean`, `FRNodeRows4Fit.lean`, `FRNodeRows4Plan.lean`, `FRVerifierImplNode4F.lean`,
`FRNodeRows4Rep.lean`, `FRNodeRows4RepS.lean`, `FRNodeRows4RepK.lean`, `FRNodeRows4RepN.lean`,
`FRNodeRows4RepW.lean`, `FRNodeRows4RepRsK.lean`, `FRNodeRows4RepLT.lean`, `FRNodeRows4RepCtrl.lean`,
`FRVIRTplRepLW.lean`. Not edited (diff for the orchestrator, §5): `FRNodeRun4.lean`, `FRNodeRun4S.lean`,
`FRNodeRun4Ctrl.lean`. **`FR.lean` (orchestrator): `import FRNodeRows4RepF`, `import FRNodeRows4RepFCtrl`.**
The other modified worktree files (`FRVIR4*`, `FRVIRFinals4`, `FRVIRTplBuild`, `FRXChain4`,
`FRSoundness4Qry`, `FRSoundness4R4Run`, `FRInitFuse`) are another track's, not REPF's.

**`FRNodeRows4.lean` hunks (REPF's only; vs HEAD `91e0d61`; `askTG`, its doc, `XofT` and ASK-T's/IMPC's
imports untouched):** (1) `import FRNodeRows4Defs` after `import FRNodeRows4AskI`; (2) HEAD lines 50–55,
65–67, 72–108, 111–117, 125–127 removed (the definitions moved to `FRNodeRows4Defs`; theorems `ev_mapC`,
`holds_rowMapC`, `nodeGrp_nodeOf` stay); (3) the new section before `rejectRows` (`repCellOk`, `repFitB`,
`RepFit`, `repAllRows`); (4) `nodeIRows4`'s doc and body (`… ++ repAllRows κ`); (5) the proofs of
`mem_node_slot/ar/link` (one line each) and the new `mem_node_rep`.

### 8.2 Statement changes (all listed)

| Declaration | Change | Why |
|---|---|---|
| **`nodeIRows4`** (def) | `++ repAllRows κ` | the fold |
| `RepOk`, `RepHolds`, `repIRows4` (defs, `FRNodeRows4Rep`) | now the `RTOkW` forms (`RTOkW … repB`, rows at `w ∘ repMapC κ v`, `repIRowsW`'s placement) | B3's switch; **every theorem stated over them keeps its text but changes meaning**: `gap4Imp_of_run`, `slotImp_of_runA`, `gap4Imp_of_runS`, `gap4Imp_of_rsv`, `gap4Imp_of_askT`, `gap4Imp_of_impc(R)`, IMPC2's `gap4Imp_of_bitsB`, … |
| `slotImp_of_rep`, `repHolds_of`, `gap4Imp_of_rep` | moved `FRNodeRows4Rep` → `FRNodeRows4RepW`, text unchanged | proofs by the W versions |
| `repOk_rtSeg` | **removed** | `rtLinkSeg` (no bound check) is not `RTOkW`-sound; `rtLinkSegW` replaces it |
| `compileFromX_run`, `compileX_run` (ASK-T's, diff §5) | `RTOkW`, `w'`, `hP'`, `hAg` | the replay rows at the spare region's assignment |
| `repRow0` (def) | segment base `repBase` → `repSegB` | ASK-T's template rows occupy `repBase` |
| `kRows` (def) | `rowsTR (kTpl …)` for `(kTpl …).rows` (`rowsTR_eq`) | the 8 MB init stack |
| `tplLW` (def) | over `tplLWg` (tables once); `lwK9…lwFams` are `abbrev`s | 216 s init |
| `Plan4` | fields `rp0 rp1 hrp rgF rgL hrg`; **`hR` adds `RepFit`** | the plan |
| `mkPlan4` | `+ (rl0 rl1) (hrl) (rp0 rp1) (hrp)`; `arOf` → `arRepOf` in `planOf4D` | — |
| `LCx` / `CxAt` | field `rv` / its third conjunct | the shared replay value |
| `innAt_thsOf` | `+ (rv)` argument | `LCx`'s new field |
| `cxAt_mk/lo/of` | contexts carry `rvOf` | — |
| `slotV4` (def) | `slotV4o + repV4` (old body is `slotV4o`) | — |
| `nodeIRowsP` (def) | `+ repAllRowsP` | fallback |
| `RepCtrl.ctlP` | renamed `repCtlP` | clash with `FRNodeRun4AskT` |

**Textually unchanged** (checked against HEAD): `evalMT4_eq`, `evalMS4`, `slots_val`, `evalMX4_eq`,
`implN4F_hMX`, `hfit4`, `linkV4_eq`, `protoV4_eq`, `ProtoFit`, `ArFit`, `tplLW_ok`, `rtK_okW`, `rtC1c_ok`,
`repOkW_rtC1c`, every `Gaps4`/`Open4F`/certificate statement. The certificate's top hypothesis is
unchanged (`Open4F := Gaps4`); `gaps4_of_runA` reduces it to the `SlotRunA` residual at `rtC1c`.

### 8.3 Line counts (`loc.py`: total / code / thm; `logs/REPF/loc.txt`)

HEAD (13 touched modules) 5,358 / 3,815 / 277 → REPF (13 + 4 new) 6,259 / 4,425 / 324. New:
`FRNodeRows4Defs` 479/236/0, `FRNodeRows4RepFD` 97/53/6, `FRNodeRows4RepF` 83/47/6, `FRNodeRows4RepFCtrl`
38/19/4. `FRNodeRows4Fit` 624 → 821 code, `FRNodeRows4Plan` 983 → 1,188; the Rep modules shrink by the moved
definitions.

### 8.4 Kernel CPU (one core, `-DElab.async=false --profile`; REPF `logs/REPF/prof-summary.txt`, HEAD
`ae8b8d8` in `fr-build-ASKT`, `logs/REPF/prof-head.txt`; load 4–8)

| Module | REPF type checking | HEAD | tactics (REPF) |
|---|---|---|---|
| `FRNodeRows4Defs` (new) | 0.10 s | — | — |
| `FRNodeRows4` | 0.22 s | (n/a) | 0.27 s |
| `FRNodeRows4Fit` | **6.51 s** | 3.01 s | 6.36 s (`rep_fit` 1.57 s, `rep_fit1` 0.87 s, `hfit4` 0.48 s elab.) |
| `FRNodeRows4Plan` | 1.64 s | 0.94 s | 7.03 s |
| `FRVerifierImplNode4F` | 1.15 s | 0.98 s | 1.63 s |
| `FRNodeRows4Rep` / `RepS` / `RepK` / `RepN` / `RepW` | 0.16 / 0.04 / 0.20 / 0.17 / 0.03 s | 0.14 / – / 0.20 / – / – | 1.05 / 0.29 / 0.98 / 7.36 / 0.11 s |
| `FRNodeRows4RepRsK` / `RepLT` / `FRVIRTplRepLW` | 0.14 / 0.20 / 0.19 s | – / – / 0.20 | 0.62 / 19.1 / 0.79 s |
| `FRNodeRows4RepCtrl` / `RepFD` / `RepF` / `RepFCtrl` | 0.03 / 0.02 / 0.004 / 0.02 s | | |
| `FRNodeRun4` / `4S` / `4Ctrl` (patched) | 0.29 / 0.12 / 0.21 s | 0.28 / – / – | |

**Δ kernel ≈ +4.5 s**, of which `FRNodeRows4Fit` ≈ +3.5 s (the new fit lemmas' `omega`s over region
arithmetic; a G5-style golf target: route the region facts through `p.1 / slotM4` as `rep_fit` does
for disjointness). All proofs are symbolic; no `decide` over the replay rows.

## 9. Final build and run-time checks

- **Final build** on **HEAD `91e0d61`** (IMPC2's modules) + REPF + the §5 diff: `lake build FR Solution
  FRSubmission4Fin` **green, 2,676 jobs** (`logs/REPF/final.log`).
- `plan4t check` (`logs/REPF/plan4t-check.log`): **N2 equal true** (sparse 241 s), **N4 equal true**
  (sparse 356 s); N8 (no prototype-0 slot; its replay part is the segment slots' 8 rows each) was still
  running at the freeze under `timeout 3600`.
- Prover cells and rows for E1: §2 (placement) and C1b §5.5 (the honest gate evaluation, per op in
  program order: kind-muxed template rows in `Tpl.rows` order, then one copy row per output component;
  local offsets from `repB`: `linkWAll` 0, `rsWeight` 2^16, `targetS` 2^19 + 2^14, `evalL` 2^19 + 2^15;
  prototype 0's last local `repB + 876,562`); segment slot `v`: rows `v·2^20 + 1,014,784 + k` (k < 8),
  `one · out_j = 0` on its `linkWAll` output cells (no locals). The plan form changed (`protoV4` did not;
  `slotV4` gained `repV4`).
