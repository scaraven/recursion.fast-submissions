# G6: RESULT — the certificate's build cut by merging modules (372 → 145 on `Solution`'s path)

Stage G6, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `c82be25`). Build trees
`logs/fr-build-G6` (the entry; real file copies, `snap.sh`) and `logs/fr-build-G6h` (HEAD's sources, byte-identical,
for the A/B). Logs `logs/G6/`. Every lake/lean run in a 16 GB scope under `timeout`. Nothing committed, no
sub-agents, `prover/` not touched.

## 0. Verdict

| item | before (HEAD `c82be25`) | after (G6) |
|---|---|---|
| modules in `Solution`'s import closure | **372** (371 FR + `Solution`) | **145** (144 FR + `Solution`) |
| clean `lake build Solution`, 4 cores (`taskset -c 20-23`), total CPU (user + sys) | 4,427 s / 4,507 s (two runs) | **3,207 s** (−28 %) |
| same, wall | 1,260 s / 1,296 s | **864 s** (−33 %) |
| sum of per-module CPU, each module alone on one core | 5,382 s | 3,737 s (−31 %) |
| critical path (per-module CPU, one core each) | 1,287 s (89 modules deep) | 982 s |
| kernel replay of `certified` + `submission` (KReplay, one core) | 444.4 s, 57,322 declarations | 408.8 s, 57,235 declarations (no declaration +0.21 s or more) |
| statements and definitions | — | **unchanged**: 44,288 FR constants compared by type hash (and value hash for definitions), 0 differ (§4) |
| `Solution.lean` | — | byte-identical to HEAD |
| `Challenge.certified` axioms | `[propext, Classical.choice, Quot.sound]` | `[propext, Classical.choice, Quot.sound]` (`logs/G6/axioms.log`) |
| source rule | 482 files, 0 findings | 263 files, 0 findings |
| builds | — | `Solution`, `FR`, `FRSubmission4Fin`, `FRNodeRows4Model`, every control (via `FR`), `FRSoundness4P4aCtrl3`, `FRSoundnessFrChain`: green, 2,490 jobs (`logs/G6/iter6.build.log`) |

Projected on the runner's EPYC 7763 (RUN2a: 983.6 s worst, cap 1,200 s): with the local CPU ratio (0.71) ≈ 700 s;
with the local wall ratio (0.67) ≈ 655 s. That is **≈ 1.7–1.8× of `build_s`** instead of 1.22×. This is a
projection from local ratios, not a runner measurement; a RUN2b probe would confirm it.

## 1. Measurements (logs)

- Clean builds: `logs/G6/build-before.{log,time}` (HEAD in `fr-build-G6`, before any edit),
  `logs/G6/build-head2.{log,time}` (HEAD in `fr-build-G6h`, run right after "after"), `logs/G6/build-after.{log,time}`
  (G6 in `fr-build-G6`). Each: `rm -rf .lake/build`, then `/usr/bin/time -v systemd-run … taskset -c 20-23 lake build
  Solution` (`fr-build-G6/clean.sh`). The machine was shared: E1b's prover ran unpinned (affinity 0–31) during all
  three, so wall times carry some noise; CPU totals are the steadier figure.

  | run | user | sys | CPU | wall | peak RSS |
  |---|---|---|---|---|---|
  | before | 3,914.1 | 513.0 | 4,427 | 20:59.8 | 4.79 GB |
  | head2 | 3,994.7 | 511.9 | 4,507 | 21:36.0 | 4.81 GB |
  | **after** | **2,990.0** | **217.1** | **3,207** | **14:24.1** | 3.97 GB |

- Per-module CPU (`fr-build-G6/permod.sh`: every closure module elaborated alone with `lake env lean`, one core
  each, 8 workers): `logs/G6/permod-before.txt`, `logs/G6/permod-after.txt`.
- Kernel: `probe/cert-time/KReplay.lean` on `certified` + `submission` (`logs/G6/kreplay-{before,after}.{log,tsv,time}`;
  before in `fr-build-FEL`, whose oleans are HEAD's).

## 2. Profile: where the time went

- **A module costs ≈ 6 s before it elaborates anything.** Importing the contract and Mathlib closure takes ≈ 3.5–4 s
  user and ≈ 2.5 s sys (`import FRSubmission4Fin` + one `trivial`: 6.2 s; `import RecursionFast.Contract` + two
  Mathlib modules: 5.5 s). FEL's `FRNodeRows4AskIS` "63 s" was this: `import took 39.4s` under I/O contention, 14 s of
  CPU.
- With 372 modules that floor was ≈ 2,200 s of the 5,382 s per-module sum (41 %), and ≈ 530 s of the 1,287 s
  critical path (89 modules deep). On a 4-core runner both the total and the depth matter (simulated 4-core
  makespan 1,703 s vs total/4 = 1,346 s).
- Only 7 of the 371 FR modules had no constant in `certified`'s closure (`logs/G6/used-before.txt`, probe
  `fr-build-G6/probe/Used.lean`). So taking whole modules off the path could not give much. Cutting the module
  count could.
- Top modules before (CPU s, alone): `FRXLag` 60.1, `FRVIRTplRepL` 56.8, `FRXLagT` 56.0, `FRXMsg` 54.7, `FRXBfly` 49.4,
  `FRXOut` 47.5, `FRXField` 44.6, `FRVIRCompile` 44.5, `FRXFlag` 44.0, `FRNodeRows4Fit` 42.6, `FRSoundness4Qry` 42.2,
  `FRXBary` 40.8.
- Top modules after (merged modules are bigger): `FRXDec4Front` 97.3, `FRXNd4` 91.6, `FRXOut` 82.6, `FRXMsg` 76.6,
  `FRSoundness4TailC` 74.1, `FRXFwd` 73.1, `FRXLag` 56.9, `FRSoundness4R4FinSh` 56.8, `FRVerifierImplOps` 54.0,
  `FRNodeRows4AskStmtS` 51.3. A merged module elaborates its theorems in parallel inside one `lean` process, so its
  build time is shorter than these single-core figures.

## 3. What changed

### 3.1 Modules taken off the path (no statement touched)

The 7 modules with no constant in `certified`'s closure were tried. In each case the importer's `import Z` was
replaced by `Z`'s own imports, and `Z` was kept built through `FR`.

- **Off the path:**
  - `FRSoundness4R4FinCtrl` (out of `FRSoundness4R4Acc`);
  - `FRSoundness4P4aCtrl5` (out of `FRSoundness4XFront`);
  - `FRSoundness4P4aCtrl` (out of `FRSoundness4P4aBridge`; `FR.lean` now imports it).
- **Kept on the path**, because the importer's own unused declarations need them:
  - `FRBlake2sWitness`: `FRBlockLayout` uses `compress_keys`;
  - `FRXNode`: `FRXExt`'s `decSnark` uses `decLN3`;
  - `FRNodeSound4K`: `FRNodeRows4PackSound`'s `ks_rev4GR` and `certificate_rev4GR`;
  - `FRNodeRun4Ctrl`: `FRNodeRows4AskInp`'s control `atImp_inp_neg`.

  Taking these off as well would mean moving those declarations, for ≈ 10 s each.

### 3.2 Controls moved off the path (verbatim)

Five control blocks were moved out of their on-path modules, verbatim and with the same namespace, `open`s and
`variable`s, into new off-path modules that `FR` imports:

| control block | from | new module | decl time (seq.) |
|---|---|---|---|
| `FR.X.AgreeControls` | `FRXAgree` | `FRXAgreeCtl` | 19.0 s |
| `FR.X.FlagControls` | `FRXFlag` | `FRXFlagCtl` | 16.6 s |
| `FR.X.Controls` | `FRXField` | `FRXFieldCtl` | 8.9 s |
| `FR.X.Controls` | `FRXDsl` | `FRXDslCtl` | 5.0 s |
| `FR.X.NodeControls` | `FRXNode` | `FRXNodeCtl` (imports `FRXFlagCtl`: it opens `FlagControls`) | 5.4 s |

The hash check (§4) shows every moved constant unchanged.

### 3.3 Proofs golfed (statements unchanged)

Times are per module, alone on one core (`logs/G6/prof/`, `logs/G6/dprof/`, `logs/G6/tprof-*.txt`).

| module | declaration | change | module time |
|---|---|---|---|
| `FRVIRTplRepL` | `tplEvL_ok` | `have ho : (tplEvL …).outs = (evGM …).2 := rfl` → `by simp only [tplEvL]`. The elaborator's `rfl` evaluated `evGM`: this was the 42 s "`refine`" (`have` is `refine_lift`). | 57 → 12 s |
| `FRNodeRows4RepSegK` | `rtKD_okW` | `cases h' : b.2[q]? <;> simp_all` (27 s) → `cases h' : b.2[q]? with \| none => rfl \| some l => rw [h'] at hrow; exact hrow` | 36 → 8 s |
| `FRVIRTplRepT` | `mkCx_k0` | `rfl` → `by simp only [mkCx]` (the same trap: 28 s) | 33 → 19 s |
| `FRXOut4R` | `ldPs_keep`, `cpBody_step`, one other | `subst he <;> simp_all` over the whole context → `subst he <;> simp at h` / `simp at hr` | 35 → 23 s |
| `FRXLag` | `yTab_sem` | five of six `nlinarith` → `omega`, or `lt_of_lt_of_le (Nat.add_lt_add_left hc _) (… Nat.mul_le_mul_left …)` | 60 → 44 s |
| `FRSoundness4Qry` | `noAsk_gFinE0` | `simp [gFinE0, Op.item?, hc]` → `simp only [gFinE0, hc, cond_true, cond_false, List.filterMap_cons, List.filterMap_append, List.filterMap_nil, Op.item?, List.append_nil]` | −4 s |

Not done, but measured candidates for a later pass:

- `pins_chain` (`FRSoundnessCoreFront`): one `split_ifs`, 16 s.
- `tgBody_sem` (`FRXLagT`): 16.5 s in one `have`'s expected type.
- `gathIR_sem` (`FRXMsg`): 19.5 s spread over many steps.
- `pinnedW_eq` (`FRSkip`): `decide +kernel`, 10 s. It is on the kernel path; left alone.

### 3.4 Modules merged (the main cut)

Every merge is mechanical (`logs/fr-build-G6/merge.py`).

- **The mechanism.** Module `A` is merged into a module `B` that imports it, along an import edge `B → A` with no other
  path `B ⇝ A`.
  - `B`'s file gets the union of the members' imports, then each member's text in import order, each wrapped in
    `section G6_<member> … end G6_<member>`, so every `open`, `variable`, `set_option` and `local` stays scoped as
    before.
  - A first-line comment lists the former modules.
  - `A`'s file is deleted, and every other importer of `A` (on or off the path) imports `B` instead.
- **The planner** (`logs/fr-build-G6/plan4.py`) chooses greedily: it accepts a merge if the simulated 4-core makespan
  (per-module CPU from `permod-before.txt`, 6 s import floor, processor sharing) does not grow, and caps a merged file
  at 2,500 lines.
- **Names never absorbed** (they may absorb others), for other agents and for the brief:
  - `Solution`, `FR`, `FRSubmission4Fin`, `FRNodeRows4Model`;
  - every module E1b's probes import: `FRNodeLayout4`, `FRNodeRows4`, `FRNodeRows4ArenaPlace`, `FRNodeRows4Plan`,
    `FRNodeRun4CT`, `FRSubmission4V`, `FRVIR4`, `FRVIR4Mux`, `FRVIRFinalsSG`, `FRVIRTplEval`, `FRVerifierC4`,
    `FRVerifierImpl`, `FRVerifierImplNode4`, `FRVerifierImplNode4F`.

**Merging can change what an absorbed module's declarations elaborate to.** In the merged file, a member sees every
import of the group and the earlier members, including their `private` names. The runs showed three ways this goes
wrong:

- **An auto-bound implicit gets captured.** `chain_spec`'s `zeroD` (`FRXChainFlock`) became `FR.zeroD` once `FRVIR`
  was visible. The harness ignores lakefile options, so `autoImplicit` is on.
- **A name resolves to another declaration.** `Rel` in `FRXSearch` resolved to `FRXSortSim`'s `Rel`.
- **A private name clashes, or matchers are shared.** `FR.W4.bitN_mod` clashed. A matcher shared with an earlier member
  broke `simp only [hv]` in `FRVIRFinalsCore`.

Most such changes are build errors. Some are silent: definitions or statements still build, with different terms,
for example `FR.W4.bitN`, `FR.B64.instField`, `FR.Snd.epsR`, `FR.X.sAt_words` and `chain_spec` itself.

**So every merge round was checked against HEAD by statement hash, and the offending modules were frozen**
(`fr-build-G6/iter2.sh`, `check.py`):

1. Build `Solution`, `FR` and the two stray controls.
2. Import every module that built (probe `fr-build-G6/probe/Hash.lean`) and hash each FR constant's type (and a
   definition's value), with private names and matchers normalised.
3. Diff against HEAD's hashes (`logs/G6/hash-head.txt`, from `fr-build-FEL`'s HEAD oleans).
4. Freeze every module with a build error or a changed constant. A frozen module is never merged and never a target,
   and no merge may change its import closure.
5. Re-plan from HEAD's sources (`logs/G6/base` = HEAD + §3.1–3.3), and repeat.

Six rounds (`logs/G6/iter{1..6}.*`). Rounds 5 and 6 built everything with 0 errors and **0 changed constants**.

- **Frozen** (17, `logs/G6/frozen.txt`): `FRBlake2sCompress`, `FRBlake2sWalk`, `FRField128`, `FRField256`,
  `FRFieldBaseCorrect`, `FRNodeRows4Wots`, `FRNodeRows4WotsB`, `FRNodeRows4WotsS`, `FRSoundness4P4aL`,
  `FRSoundness4P4aNames`, `FRSoundnessCoreSteps`, `FRVIRFinalsCore`, `FRWots`, `FRXChainFlock`, `FRXDec`, `FRXEqT`,
  `FRXSearch`.
- **Result:** 224 modules absorbed into 77 targets (`logs/G6/iter6.apply.json`). Merged files run up to 2,474 lines;
  the files total +935 lines (the section wrappers).

| target | lines | former modules now inside it |
|---|---|---|
| `FRAgg` | 1109 | FRSegment, FRLeafCircuit |
| `FRBlake2sWords` | 1547 | FRBlake2sCircuit |
| `FRBlockKinds` | 1820 | FRBlockChain, FRBlockStream, FRBlockLayout, FRBlake2sWitness |
| `FRInitFuse` | 798 | FRNodeRows4RepCFP, FRVIRTplCFE, FRNodeRows4RepFD |
| `FRNodeCircuit4` | 1636 | FRSoundness4P4bRows, FRSoundness4P4bNames, FRSoundness4RsvMLE |
| `FRNodeLinks4Run` | 499 | FRNodeLinks4 |
| `FRNodeReadCore` | 692 | FRNodeReadW, FRNodeRead |
| `FRNodeRows4` | 2091 | FRNodeRows4SegD, FRNodeRun4CA, FRNodeRows4AskC, FRNodeRows4Defs, FRVIRTplRepLD, FRNodeRows4Hint, FRVIRTplAlias, FRVIRTplRepLG |
| `FRNodeRows4Agg` | 1086 | FRNodeRows4WotsK, FRNodeRows4WotsF, FRNodeRows4WotsD, FRNodeRows4WotsP, FRNodeRows4WotsL, FRNodeRows4WotsT |
| `FRNodeRows4ArenaPlace` | 973 | FRNodeRows4ArenaRows, FRNodeRows4Pack, FRNodeRows4Arena |
| `FRNodeRows4AskB` | 1160 | FRNodeRows4AskT, FRNodeRows4AskBL, FRNodeRows4AskI, FRNodeRows4AskPosT |
| `FRNodeRows4AskStmtS` | 2311 | FRNodeRows4AggChkG, FRNodeRows4PackSound, FRNodeSound4K, FRSoundness4XRunG, FRSoundness4XRun, FRSoundness4RsvHM |
| `FRNodeRows4AskTH` | 1865 | FRNodeRows4AskTB, FRNodeRows4AskPosR, FRNodeRows4AskPos, FRNodeRows4AskPosF, FRNodeRsvLink, FRNodeRows4AskInp |
| `FRNodeRows4Ext` | 1029 | FRNodeRows4AskStmt, FRNodeRows4AggChkS, FRNodeRows4AggChkB, FRNodeRows4AggChk |
| `FRNodeRows4Plan` | 2461 | FRNodeRows4RepCFW, FRVIRTplCFF |
| `FRNodeRows4RepCFRs` | 2437 | FRVIRTplCF, FRNodeRows4RepRs, FRNodeRows4RepRsV, FRVerifierImplOps4, FRVIRTplChain, FRKindWeight4 |
| `FRNodeRows4RepF` | 1029 | FRNodeRows4RepSeg, FRNodeRows4RepSegT, FRNodeLinks4SigH, FRNodeLinks4Sub, FRSubmission4Cert, FRSubmission4, FRXSig4H |
| `FRNodeRun4` | 2474 | FRNodeRows4RepS, FRNodeRows4Rep, FRNodeSound4R, FRNodeRead4W, FRNodeRead4, FRNodeSound4, FRVIR4Uni |
| `FRNodeRun4BL` | 722 | FRNodeRows4AskBS, FRNodeRun4AskT |
| `FRNodeRun4BS` | 747 | FRNodeRun4BR |
| `FRNodeRun4CT` | 666 | FRNodeRun4CD, FRNodeRun4CS |
| `FRNodeRun4Ctrl` | 1586 | FRNodeRun4S, FRNodeRows4RepLT, FRNodeRows4RepW, FRNodeRows4RepRsK, FRVIRTplRepL, FRNodeRows4RepN, FRNodeRows4RepK |
| `FRNodeStmtR4` | 1015 | FRSoundness4RsvCtrl, FRSoundness4P4fObl, FRSoundness4XFinal |
| `FRNodeTarget4C` | 707 | FRNodeTarget4 |
| `FRProximityFold` | 754 | FRProximityLine, FRProximityBW |
| `FRSegTarget4` | 431 | FRVerifierImplCore |
| `FRSoundness4Agg` | 485 | FRSoundness4R4Link |
| `FRSoundness4P4aNS` | 1957 | FRSoundness4P4aNZ, FRSoundness4P4aRS, FRSoundness4P4aDF, FRSoundness4P4aT, FRSoundness4P4bRS |
| `FRSoundness4P4aSeg` | 1388 | FRSoundnessCoreAcc |
| `FRSoundness4P4aZ` | 1883 | FRSoundness4P4aS2, FRSoundness4P4aFin, FRSoundness4P4aS, FRSoundness4TailFront, FRSoundness4P4aBridge, FRSoundness4P4aLast |
| `FRSoundness4Pos` | 1436 | FRSoundnessCoreChain, FRShape4 |
| `FRSoundness4R4Cap` | 1380 | FRSoundness4R4Cols |
| `FRSoundness4R4FinSh` | 1814 | FRSoundness4R4FinRS, FRSoundness4R4FinLc, FRSoundness4R4Fin, FRSoundness4RsvRun |
| `FRSoundness4R4FrE` | 1916 | FRSoundness4RsvStack, FRSoundness4R4Rnd, FRSoundness4R4View, FRSoundness4R4Fld, FRSoundness4R4Ex, FRSoundness4R4Acc |
| `FRSoundness4R4FrRS` | 1616 | FRSoundness4R4FrLc, FRSoundness4R4FrZ, FRSoundness4R4FrS, FRSoundness4R4Ctrl, FRNodeTarget4W |
| `FRSoundness4R4Kind` | 1193 | FRSoundness4R4Outs, FRSoundness4R4At, FRSoundness4R4Run, FRSoundness4R4Chain |
| `FRSoundness4R4PfFin` | 2121 | FRSoundness4R4PfFlag, FRSoundness4R4PfRun, FRSoundness4R4P4, FRSoundness4R4ColsCtrl, FRSoundness4R4LinkP |
| `FRSoundness4R4Qv` | 1545 | FRSoundness4R4PosT, FRSoundness4R4Start, FRSoundness4R4Tail, FRSoundness4R4RndK, FRSoundness4R4FrCtrlB |
| `FRSoundness4R4W0` | 813 | FRSoundness4P4bB |
| `FRSoundness4R4W0R` | 795 | FRSoundness4R4Wt, FRSoundness4R4Full |
| `FRSoundness4TailC` | 2426 | FRSoundness4TailM, FRSoundness4TailO, FRSoundness4TailD, FRSoundness4TailCap, FRSoundness4Tail |
| `FRSoundness4TailFold` | 1568 | FRSoundness4TailHide, FRSoundness4TailTruths |
| `FRSoundness4TailStep` | 1864 | FRSoundnessCoreSG, FRSoundnessCoreTail, FRSoundnessCoreWeights, FRSoundnessCoreHide |
| `FRSoundness4XLaws` | 1080 | FRSoundness4P4fDF, FRSoundness4XFront, FRSoundness4P4aCtrl4, FRSoundness4P4aSplit |
| `FRSoundnessCoreFront` | 1745 | FRSoundnessCoreRows |
| `FRSoundnessCoreTruths` | 700 | FRRSEval |
| `FRSubmission4Fin` | 293 | FRNodeRun4FE |
| `FRSumcheck` | 1074 | FRMLE |
| `FRTranscriptDefs` | 1022 | FRMerkle |
| `FRVIR4Mux` | 690 | FRVIR4At |
| `FRVIRTplEval` | 2043 | FRVIRTplExt, FRVIRTplKMux, FRVIRTplRep, FRVIRTplMaskN |
| `FRVIRTplFast` | 2448 | FRVIRTplBuild |
| `FRVIRTplRepT` | 1553 | FRVIRTplRepLW, FRVerifierImplNode4T |
| `FRVIRTplRun` | 1463 | FRVIRTplGrp, FRVIRTplPlan |
| `FRVIRTplSeg` | 682 | FRVIRTplMask |
| `FRVIRTplSegT` | 643 | FRVIRTplSegR |
| `FRVIRTplSet` | 857 | FRVIRCompileK |
| `FRVIRTplTab` | 820 | FRVIRTplDag, FRVIRTemplates |
| `FRVerifierC4` | 502 | FRVerifier4 |
| `FRVerifierImplNode4F` | 631 | FRVIRTpl4Bridge |
| `FRVerifierImplOps` | 2447 | FRPubTarget, FRKindWeight, FRVIREval |
| `FRXBaryDefs` | 725 | FRXBflyDefs, FRXDecodeB |
| `FRXChainTop` | 2348 | FRXChainLoop, FRXChainSem, FRXChain, FRXChainDefs |
| `FRXComputes` | 540 | FRXProg |
| `FRXDec4F0` | 1731 | FRX4Ext, FRX4Prog, FRXChain4 |
| `FRXDec4Front` | 2339 | FRXDec4Back, FRXDec4Level, FRXDecLv, FRXLagT |
| `FRXDec4Levels` | 1179 | FRXDec4Map, FRXDec4Msg, FRXDec4Lv |
| `FRXFwd` | 2391 | FRXEncB, FRXBfly |
| `FRXLag` | 1507 | FRXBaryTop |
| `FRXLogSpec` | 696 | FRXLog |
| `FRXMsg` | 2026 | FRXReadLv, FRXFlag |
| `FRXNd4` | 2389 | FRXOut4O, FRXOut4A, FRXOut4P, FRXOut4K, FRXOut4F, FRXOut4E |
| `FRXOut` | 2219 | FRNodeReadP, FRNodeReadS |
| `FRXOut4R` | 1016 | FRXOut4C, FRXOut4W |
| `FRXPf4` | 1581 | FRXTr4, FRXSig4W, FRXSig4, FRXOut4 |
| `FRXSortSim` | 1567 | FRXMerge, FRXSortSpec |
| `FRXSpec` | 1548 | FRXExt, FRXNode, FRXOutRun |

Worktree diff: 224 files deleted, 167 modified, 5 added (the `*Ctl` modules); 482 → 263 files.

## 4. Statements, `Solution`, axioms, source rule

- **No statement or definition changed.** HEAD's hashes come from `fr-build-FEL`'s HEAD oleans; G6's from
  `logs/G6/hash-out.txt`, round 6, every one of the 263 modules imported. The constants compared are every one
  declared in an `FR*` module or `Solution`, keyed by name (private prefixes dropped).
  - Compared: a constant's type, plus the value for a definition. Matchers are replaced by their type's hash.
  - Excluded: `_proof_`, `.match_`, `_auxLemma`, `._simp_`, `._f`, `_sparseCasesOn`, `noConfusion`. These are
    auxiliary names, and their numbering is nondeterministic.
  - **44,288 constants identical, 0 differ.**
  - 16 names exist only at HEAD: `RecursionFast.XOp.eval.eq_1 … eq_15` and `RecursionFast.XProg.memFor.eq_1`. These are equation lemmas of
    contract definitions, realized on demand in whichever module first asks for them.
  - 20 names exist only now:
    - 18 are from `FRSoundnessFrChain` (9) and `FRSoundness4P4aCtrl3` (9). These two stray controls are not imported
      by HEAD's `FR`, so `fr-build-FEL` never built them; both build now.
    - 2 are equation lemmas realized on demand: `FR.Tpl.tplEvL.eq_1`, by the golfed `simp only [tplEvL]`, and
      `RecursionFast.enc64.eq_1`.
  - Script: `logs/fr-build-G6/check.py`; output `logs/G6/iter6.check.txt`.
- `Solution.lean`: `git diff HEAD` is empty.
- `#print axioms RecursionFast.Challenge.certified` and `submission`: `[propext, Classical.choice, Quot.sound]`
  (`logs/G6/axioms.log`).
- Source rule (`…-flock/logs/org20/scripts/source-rule.py submissions/flock-recursive`): 263 files, 0 findings. The
  merge adds only `section`/`end` lines and comments.

## 5. Kernel

- `certified` + `submission`, KReplay on one core (`logs/G6/kreplay-{before,after}.*`): 444.4 s → 408.8 s.
- Declarations: 57,322 → 57,235. The ones that dropped are matcher and aux duplicates.
- Over the 56,545 declarations common to both: 435.6 s → 399.7 s.
- Non-FR modules (`BF64` etc.) also dropped (68.3 → 62.4 s). So part of the drop is run-to-run noise; the change is
  not a kernel regression.
- No single declaration grew by more than 0.21 s (`FR.X.chR_agg._proof_1_9`).
- The golfed proofs on the path cost less in the kernel: `noAsk_gFinE0` went from 55 ms to 15 ms.

## 6. Notes for the orchestrator

1. **Module names changed.** 224 module names are gone; the map is §3.4 and `logs/G6/iter6.apply.json`.
   - Anything that imports one of them by name breaks: future stages, probes in other build trees,
     `docs/…` references. Each must import the target instead.
   - E1b's probe imports all still resolve, all to the same name; some of those modules are now supersets.
   - `fr-build-FEL` (and other trees whose `src/` symlinks into the worktree) now see the merged files. Their old
     oleans are stale against those sources.
2. **The merge is reproducible.** `fr-build-G6/iter2.sh <n>` (plan → reset to `logs/G6/base` → merge → build → hash
   check → freeze).
   - `logs/G6/base` is HEAD plus §3.1–3.3. With `frozen.txt` as it is, the same plan comes back (rounds 5 and 6 are
     identical).
   - To undo the merge but keep §3.1–3.3: copy `logs/G6/base/*.lean` over the lean dir.
3. **`autoImplicit` is live in this entry** (the harness ignores lakefile options). Merging showed `zeroD` in
   `chain_spec` is an auto-bound variable, not the constant `FR.zeroD`. Any future change to a module's imports can
   silently change such a statement. The hash check (`check.py`) is a cheap guard for later stages too.
4. Remaining levers, measured but not taken:
   - more merging. 17 modules are frozen; changing them would mean making their names explicit (for example
     `(zeroD : Digest)` binders), which edits statement text;
   - the four `simp`-heavy proofs in §3.3's "not done" list;
   - the four on-path modules that are needed only by unused declarations (§3.1).
5. Not measured: the runner. RUN2b (`build_s` on a 7763) would replace §0's projection with a measurement.

## 7. Files touched

- `submissions/flock-recursive/lean/`:
  - **Merged and deleted:** the 77 targets of §3.4 rewritten, 224 absorbed modules deleted, and importers redirected
    (`FR.lean` and the controls among them).
  - **Golfed:** `FRVIRTplRepL` (now inside `FRNodeRun4Ctrl`), `FRNodeRows4RepSegK`, `FRVIRTplRepT`, `FRXOut4R`,
    `FRXLag` and `FRSoundness4Qry`. `FRNodeRows4RepSegK` and `FRSoundness4Qry` stay standalone files.
  - **Controls moved and imports cut:** the 5 new `FRX*Ctl` modules; the controls cut from `FRXAgree`, `FRXFlag`,
    `FRXField`, `FRXDsl` and `FRXNode`; and the imports of `FRSoundness4R4Acc`, `FRSoundness4XFront` and
    `FRSoundness4P4aBridge` (§3.1).
- This file.
- Tools and logs: `logs/fr-build-G6/` (`snap.sh`, `clean.sh`, `permod.sh`, `closure.py`, `graph.py`, `sim.py`,
  `plan4.py`, `merge.py`, `check.py`, `iter2.sh`, `probe/{Used,Hash,Ax}.lean`), `logs/fr-build-G6h/` (HEAD A/B tree),
  and `logs/G6/`.

## Orchestrator note (review `reviews/G6-review.md`)

- **G6-R1.** The "44,288 constants identical" figure counts auxiliary names whose hashes happen to match. `check.py` actually compares 25,193 non-auxiliary names; 689 auxiliary names differ and are excluded, 15 of them `._f` values.
  - The review's deep check closes the gap on the certificate path. It folds every auxiliary constant into the hash of the constant that uses it, and includes binder info and the universe count. Over `Solution`'s closure at HEAD and at G6, 22,533 common constants match, and 0 differ.
  - Names present only at HEAD (119) all come from the moved controls and the three control modules taken off the path. Names present only in G6 (4) are equation lemmas generated on demand.
  - The probe code is kept at `logs/G6/deep.tail`; outputs are in `logs/G6/deep-G6h.txt` and `logs/G6/deep-G6.txt`.
- **G6-R3.** The HEAD at G6 was `4537909`; `lean/` is unchanged since `c82be25`.
- **G6-R5.** For later edits: a former module's code now sits inside its `section G6_<name> … end` in the merged file. After any edit, re-run the deep hash check (the `autoImplicit` capture hazard remains).
