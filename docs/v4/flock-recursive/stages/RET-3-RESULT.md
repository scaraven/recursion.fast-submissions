# RET-3 RESULT: the 3.x verifier shapes out of the Rev4 certificate's closure

This is step 4 of plan (B) in BLUEPRINT §10 "changes 27".

- **Base.** HEAD `cb12cc4`. The final build ran on it plus RET-3's files. HEAD has since moved to
  `e4b8cd9`, but only docs changed.
- **Build tree.** `logs/fr-build-RET3`, copied from `fr-build-orch`. `MINE.txt` lists 38 modules.
  The read-only "before" tree is `logs/fr-build-RET3b`.
- **Logs and tools.** In `logs/RET3/` (tools in `logs/RET3/tool/`). The journal is `RET-3-JOURNAL.md`.
- **Rules followed.** Every lean/lake command ran in the 16G scope under `timeout`. No sub-agents.
  Nothing committed to the branch.
- **Stopped early.** The orchestrator stopped the work after the re-pin to `64378d2`, which raised
  `build_s` to 1,200 s. Item 4's local VM timing was cancelled. The 7763 probe was already running
  (§5).

## Status

| Check | Result |
|---|---|
| Item 1: census | See §3. At HEAD, `Solution`'s closure has 249 modules and 2,329.3 CPU-s (the probe's 7763 times). 3.x verifier/IR modules in it: 21 modules, 295.1 CPU-s. The 3.x node read: 4 modules, 59.0 s. Step 2's extractor: 13 modules, 157.7 s. |
| Item 2: move | **457 declarations** moved verbatim from 13 3.x modules into 5 new Core modules (§1). The importers were re-pointed, import lines only (§2). |
| Item 3: result | `Solution`'s closure: **240 modules**, with 14 dropped and 5 Core modules added. The dropped modules cost **189.0 CPU-s** at the 7763 times. The 5 Core modules cost 55.0 s on the probe's runner, ≈ 65 s at 7763 speed. **Net ≈ −124 CPU-s** (§5). |
| Statements | 457 names hashed before and after (`stmt-{before,after}.txt`). Every type is identical, and so is every definition's value except one, `rsPtIx`. Its `match` now reuses the structurally equal matcher `Layout.selCells.match_1` of the same Core module. This is the same effect as RET-1's `clR2`. **No statement and no proof changed.** |
| Build | `lake build FR Solution FRSubmission4Cert FRSoundness4XCtrl FRNodeSound4Ctrl`: **green**, 2,586 jobs (`build-FR2.log`). |
| Axioms | `ax/AxRET3.lean` → `axioms.log`. All 457 names are in a RET-3 Core module, none misplaced. They use only `propext`, `Classical.choice` and `Quot.sound`. So do `RecursionFast.Challenge.certified`, `complete_rev4`, `delta_rev4`, `certificate_sub4` and the rest of S-I's list. |
| Source rule | `logs/org20/scripts/source-rule.py submissions/flock-recursive`: 372 files, **0 findings** (`source-rule.log`). |
| Item 4: probe | Run 40850381037 (commit `3b8785b` = HEAD + RET-3's 38 Lean files + `probe.conf`; branch `probe/ret3-cert`, now deleted). **`build_s` = 565.3 s**, 241 modules, 1,888 CPU-s. **The runner was an Intel Xeon 8370C, not the 7763**, so this is not directly comparable with 696.2 s (§5). |

## 1. What was built (`loc.py`; `logs/RET3/loc-{before,after}.txt`)

| Module | total / code / thm | Imports | From |
|---|---|---|---|
| `FRVIRSpecCore` (new) | 813 / 654 / 65 | `FRVIR`, WitnessSending | `FRVerifier` (1), `FRVIRSpec` (67), `FRVIRChain` (22). Contents: the registers and `exec_app`/`exec_append`, the shape lemmas Rev4 reads, and the reference chain (`ChainOK`, `qOf`, …). |
| `FRVIRFinalsCore` (new) | 716 / 446 / 25 | `FRVIRSpecCore`, `FRSkip` | `FRVIRFinals` (56), `FRVIRFinalsSF` (32). Contents: `Finals`, `pureRun`, and **`finZ`, `finLc`, `finSh`, `finLr`, `finRS`, `finE`, `finB′`** with their run lemmas. |
| `FRVIRFinalsCoreSG` (new) | 1,251 / 912 / 41 | `FRVIRFinalsCore`, `FRVIRCompile` | `FRVIRMux` (5), `FRNodeLayout` (26), `FRVIRFinalsSG` (107), `FRNodeCircuit` (6). Contents: **`finP`, `finPf`** and their run lemmas, `uHat`, `eqCellK`, the layout constants and `PubCells`. |
| `FRNodeTargetCore` (new) | 1,180 / 901 / 61 | `FRVIRFinalsCoreSG`, `FRVerifierImplOps`, `FRBlockKinds` | `FRNodeTarget` (58), `FRVerifierImplNode` (64). Contents: `targetSNodeS`/`linkWS` and `targetSNodeI`/`linkWI` with `_meets`. |
| `FRVerifierImplCore` (new) | 147 / 96 / 3 | `FRNodeTargetCore`, `FRVIRTplFast` | `FRVerifierImpl` (8), `FRNodePlan` (3) |
| 13 residual 3.x modules | 7,998 / 6,011 / 385 → 4,272 / 3,166 / 190 (total with the Core modules: 8,379 / 6,175 / **385**) | each adds `import <Core>` and a `-- RET-3:` pointer line | only the moved chunks are deleted |

- **Theorem count.** Unchanged. The +164 code lines are the replicated `namespace`/`open`/`variable`
  lines.
- **The mover.** `tool/move3.py` is RET-2's `move2.py` with new groups. `tool/need3.py` computes the
  moved set: the X constants that non-X modules of `Solution`'s closure use, closed under use inside
  X. It works from `scratch/Graph.lean` → `graph.txt`.
- **Extra seeds** (`extra-seeds.txt`). These are names that a tactic uses without the term using
  them, or that shape a proof indirectly:
  - `toD_d`, `g3`, `round3Vals`, `toF_f` (`FRVIRSpec`) and `finV` (`FRVIRFinalsSG`): named in a `simp`;
  - `posHeadVals_length`: an `@[simp]` lemma. It is the only attributed declaration in the unread
    parts.
  - `nodeBit`, `nodeE_bit`: see the deviations.
- **What stays behind.** The unread parts that remain in the 3.x modules are the heavy proofs:
  - the flags `flag_finZ/Lc/Sh/Lr/E/B′/P4/Pf`;
  - `exec_finRS`, `exec_phaseZ`, `genPhase_ctx`, `refPhase*`;
  - the `run_*Ops` of the phases Rev4 does not read.

## 2. Re-pointed imports (import lines only)

| Module | was | now |
|---|---|---|
| **`FRVIRFinals4`** | `FRVIRFinalsSG` | `FRVIRFinalsCoreSG` (the only change to this file) |
| `FRSoundness4Qry` | `FRVIRSpec` | `FRVIRSpecCore` |
| `FRSoundness4P4aLast` | `FRVIRFinals` | `FRVIRFinalsCore` |
| `FRSoundness4R4Ref` | `FRVIRChain` | `FRVIRSpecCore` |
| `FRSoundness4R4Run` | — | + `FRXChainFlock`. It reads S-H4's `X.msgItem`, which used to come in through `CoreAcc → FRVIRChain → FRXChainFlock`. |
| `FRNodeCircuit4` | `FRNodeCircuit` | `FRVIRFinalsCoreSG` |
| `FRNodeKinds4` | `FRNodeTarget` | `FRNodeTargetCore` |
| `FRVerifierImplNode4` | `FRVerifierImplNode` | `FRNodeTargetCore` |
| `FRSegTarget4` | `FRVerifierImpl` | `FRVerifierImplCore` |
| `FRSubmission4V` | `FRNodePlan` | `FRVerifierImplCore` |
| `FRVerifier4` | `FRVerifier` | `FRVIRSpecCore` |
| `FRSoundnessCoreSG` | `FRVIRFinalsSG` | `FRVIRFinalsCoreSG` |
| `FRSoundnessCoreAcc` | `FRVIRChain` | `FRVIRSpecCore` |
| `FRSoundnessCoreRows` | `FRNodeCircuit` | `FRVIRFinalsCoreSG`, `FRVIRTplFast` (B0's module, imported, not edited; `FRNodeCircuit` reached `FR.Impl`/`Eval`/`NodeT` through it) |
| kept 3.x: `FRVIREval` | `FRNodeLayout` | `FRVIRFinalsCoreSG` |
| kept 3.x: `FRVerifierImplOps` | `FRVIRFinalsSG`, `FRVerifier` | `FRVIRFinalsCoreSG` |
| kept 3.x: `FRVIRTplMask` | `FRVerifierImplNode` | `FRNodeTargetCore` |

**Outside every Rev4 closure:** these modules lost a transitive path to residual 3.x names, so each
gets one import added:
- `FRSoundness4R4FrCtrl` (an R4 control): + `FRVIRFinalsSF`, for `relE`, `relSh`, `relRS`,
  `rsLeafZero`;
- `FRSoundnessPIOP`: + `FRNodeLayout`;
- `FRSoundnessAccRun`: + `FRWots`.

`tool/impcheck3.py` (`ALL=1`) runs on the before tree's use relation (`moduses.txt`). For every
module, each module it reads is in its import closure.

## 3. Census (7763 times: the probe's `build.log`, run 40839253556)

**3.x verifier/IR modules in `Solution`'s closure at HEAD, with the direct edge that pulls each one
in:**

| Module | CPU-s | Read by Rev4 (decls) | Pulled in by | After RET-3 |
|---|---|---|---|---|
| `FRVIRSpec` | 41.0 | 64/129 | `FRSoundness4Qry`, `FRVIRFinals` | **out** |
| `FRVIRFinalsSG` | 30.0 | 106/142 | `FRVIRFinals4`, `FRSoundnessCoreSG`, `FRVerifierImplOps`, `FRVerifierImpl` | **out** |
| `FRNodeTarget` | 22.0 | 56/74 | `FRNodeKinds4`, `FRVerifierImplNode` | **out** |
| `FRVIRFinals` | 17.0 | 56/68 | `FRSoundness4P4aLast`, `FRNodeLayout`, `FRVIRChain`, `FRVIRFinalsSF` | **out** |
| `FRVIRFinalsSF` | 15.0 | 32/58 | `FRVIRFinalsSG`, `FRVerifier` | **out** |
| `FRVerifierImplNode` | 13.0 | 64/76 | `FRVIRTplMask`, `FRVerifierImplNode4`, `FRVerifierImpl` | **out** |
| `FRVIRMux` | 12.0 | 5/30 | `FRNodeLayout` | **out** |
| `FRVIRChain` | 9.7 | 22/36 | `FRSoundness4R4Ref`, `FRSoundnessCoreAcc` | **out** |
| `FRVerifier` | 7.4 | 1/21 | `FRVerifier4`, `FRNodeCircuit`, `FRVerifierImpl(Ops)` | **out** |
| `FRWots` | 5.4 | — | `FRNodeCircuit` | **out** |
| `FRNodeLayout` | 5.0 | 26/66 | `FRVIREval`, `FRNodeCircuit`, `FRNodeTarget`, `FRVIRFinalsSG` | **out** |
| `FRNodeCircuit` | 4.2 | 6/18 | `FRNodeCircuit4`, `FRSoundnessCoreRows` | **out** |
| `FRVerifierImpl` | 3.9 | 8/10 | `FRSegTarget4`, `FRNodePlan` | **out** |
| `FRNodePlan` | 3.4 | 3/4 | `FRSubmission4V` | **out** |
| `FRVIRCompile` | 26.0 | 105/123 | `FRVIRTplCore`←…, `FRVIRCompileSound`, `FRVIRTemplates` (**B0's**) | stays |
| `FRVIR` | 18.0 | 99/120 | `FRVIR4`, `FRVIRTplCore` | stays (the IR) |
| `FRKindWeight` | 16.0 | 103/111 | `FRKindWeight4` | stays |
| `FRVerifierImplOps` | 16.0 | 121/139 | `FRVerifierImplOps4`, `FRNodeTargetCore`, `FRVIRTemplates`, `FRSoundnessCoreAcc` | stays |
| `FRVIRTplDag` | 13.0 | 35/39 | `FRVIRTplWalk` | stays |
| `FRVIRCompileSound` | 9.3 | 34/38 | `FRVIRTplExt` (**B0's**) | stays |
| `FRVIREval` | 7.7 | 32/37 | `FRVIRTplEval`, `FRKindWeight` | stays |
| `FRVIRTemplates` | 5.5 | 33/35 | `FRVIRTplExt` (**B0's**), `FRVIRTplLag`, `FRVIRTplTab` | stays |

**Remaining after RET-3 (`clo-after.json`), at the 7763 times:**

| Group | Modules | CPU-s |
|---|---|---|
| 3.x verifier/IR, kept (almost all of each is read) | 8 | 111.5 |
| 3.x node read `FRNodeRead/ReadW/ReadS/ReadP` (only S-H4's `FRXOut`, `FRXNode`, `FRXOutRun` read them) | 4 | 59.0 |
| Step 2's 3.x extractor (S-H4): `FRXNode` 21, `FRXChainFlock` 21, `FRXOutRun` 16, `FRXChainLoop` 15, `FRXChainSem` 15, `FRXDecLv` 14, `FRXLog` 9.9, `FRXSpec` 9.8, `FRXChainDefs` 8.7, `FRXChainTop` 8.2, `FRXChain` 7.4, `FRXComputes` 7.3, `FRXExt` 4.4 | 13 | 157.7 |
| The whole closure | 240 | ≈ 2,140 at the old times + the Core modules ≈ **2,165** |

**Step 2's direct edges after RET-3:**
- `FRX4Prog → FRXSpec`;
- `FRSoundness4R4Run → FRXChainFlock` (`X.msgItem`);
- `FRXSeed`/`FRXReadLv → FRXChainFlock`;
- `FRXDec → FRXExt`/`FRXNode`.

## 4. Edits needed from other tracks

1. **B0: none.** No edge into a retired module runs through a B0 module.
   - B0's working-copy edits (FRVIRCompile/Tpl*/Rows4Hint/Model) use no unread X name (checked
     against the diff).
   - `FRVIRCompileSound` and `FRVIRTemplates` stay because B0's `FRVIRTplExt` imports them. Almost
     all of both is read anyway.
2. **S-H4 (step 2), the 3.x node read: −59 CPU-s** once `FRXNode`/`FRXOutRun` leave the closure.
   - Without them, `FRXOut` reads only **4 declarations (45 lines) of `FRNodeReadS`**: `Read.Seg`,
     `Read.segOut`, `Read.sibW`, `Read.flatMap_single` (`need3.py` on `clo-nostep2.txt`).
   - The steps: move them into a `FRNodeReadCore`, then change `FRXOut`'s `import FRNodeReadP` to
     `import FRNodeReadCore`.
   - That takes `FRNodeRead`, `ReadW`, `ReadS` and `ReadP` out of the closure.
3. **S-H4 (step 2): `X.msgItem`.** `FRSoundness4R4Run` reads `X.msgItem` (`FRXChainFlock`). It must
   move to a common module before `FRXChainFlock` can retire.
4. **Rev44 merge.** `FRVIRFinals4`'s only change is line 3, `import FRVIRFinalsSG` → `import
   FRVIRFinalsCoreSG`. The edit A2′ made on `v4/rev44` (the file's body) should merge cleanly.

## 5. Times

- **The probe** (`logs/probe-cert-ret3/`, run 40850381037):
  - **`build_s` = 565.3 s**, 241 built modules, 1,888.2 CPU-s (sum of Lake's per-module times),
    `comparator_s` 39.5, `gate_s` 9.3, `badge_s` 48.3, gate PASS.
  - **The runner was an Intel Xeon Platinum 8370C** (`machine.txt`), not the EPYC 7763 of run
    40839253556 (696.2 s, 2,331.7 CPU-s).
  - The comparator's "statement does not match" failure is the same as in the previous run. It is
    not RET-3's.
- **Normalised to the 7763:**
  - **The machine factor.** On the 207 modules whose source is the same in both runs, the 8370C
    took 1,548.4 CPU-s against the 7763's 1,829.5. Its time is **0.846×** the 7763's.
  - **What changed.** The 14 dropped modules cost **189.0 CPU-s** (7763). The 5 Core modules cost
    55.0 s on the 8370C, ≈ **65 s** at 7763 speed (`FRNodeTargetCore` 20.0, `FRVIRSpecCore` 13.0,
    `FRVIRFinalsCoreSG` 13.0, `FRVIRFinalsCore` 6.2, `FRVerifierImplCore` 2.8). **RET-3's net is
    ≈ −124 CPU-s.**
  - **The whole closure** after RET-3 (and S-H4 pass 5, which landed between the runs): 1,888.2 /
    0.846 ≈ **2,231 CPU-s at 7763 speed**, against 2,331.7.
  - **Wall time**, scaled by the same factor (crude, because the critical path need not scale):
    565.3 / 0.846 ≈ **668 s on a 7763**, against 696.2. That is still above the old 600 s cap and
    well under the new 1,200 s.
- **Local VM timing:** started (`fr-build-RET3t/tb.sh before|after`) under load 14–17 and
  cancelled at the orchestrator's stop. There is no VM figure.

## 6. Deviations

- **Five Core modules, not one `FRVIRFinalsCore`.** The split follows the import order around the
  kept modules:
  - `FRVIREval` and `FRVerifierImplOps` sit between `FRVIRFinalsCoreSG` and `FRNodeTargetCore`;
  - `FRVIRTplFast` sits before `FRVerifierImplCore`.
- **Matcher sharing** (Lean reuses a structurally equal `match` auxiliary within a module):
  - `FRVIRSpec` and `FRVIRFinals` in one module broke `exec_pureRun`'s `split at h`. So they are
    separate Core modules (`FRVIRSpecCore`, `FRVIRFinalsCore`), and every proof stays verbatim.
  - The residual control `nodeE_bit` needed `nodeBit` to share `nodeE`'s matcher. Both moved to
    `FRNodeTargetCore` with `nodeE`, as extra seeds.
  - `rsPtIx`'s value now names `Layout.selCells.match_1` (see Status).
- **`open RecursionFast FR.X` → `open RecursionFast`** in `FRVIRSpecCore`'s `FRVIRChain` section.
  `FR.X` is S-H4's namespace. Core does not import it, and no moved declaration reads it.
- **Three modules outside the certificate gained one import each** (§2).

## 7. Open questions

1. **Delete the residual 3.x modules?** The orchestrator decides whether to delete the 13 residual
   modules (≈ 4,200 lines of 3.x-only proofs, outside every Rev4 closure) together with the 3.x
   soundness modules from RET-2. `FR.lean` still builds them.
2. **Should step 2 take item 4.2 (`FRNodeReadCore`)?**
