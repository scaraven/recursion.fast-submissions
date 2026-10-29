# RET-3 JOURNAL: the 3.x verifier shapes out of the Rev4 certificate's closure

Blueprint §10 changes 27 (B), step 4. Base HEAD `cb12cc4` (S-H4 pass 5 `a84753a` + queue). Tools and
logs: `logs/RET3/` (tools in `logs/RET3/tool/`). Per-module times: the probe's 7763 run
40839253556 (`logs/probe-cert-g3/probe-si-cert/out/build.log`, entry `563e494`).

1. **Build tree.** `logs/fr-build-RET3`, a copy of `logs/fr-build-orch` (org20). `b.sh` snapshots
   (`MINE.txt`) and runs `lake build` under `taskset` in the 16G scope with `timeout`; `chk.sh`
   elaborates one file. Log: `../RET3/build-last.log`.
2. **HEAD build** (`b.sh FR Solution FRSubmission4Cert FRSoundness4XCtrl FRNodeSound4Ctrl`): green,
   2,581 jobs (replays; the orch tree was current).
3. **Census at HEAD** (`tool/clos.py` → `clo-head.json`): `Solution`'s closure is 249 modules,
   2,329.3 CPU-s at the probe's 7763 times (S-H4 pass 5 landed after the probe's entry; module set
   unchanged). The candidate 3.x verifier-shape modules and their direct non-3.x importers: see the
   RESULT §3.
4. **What the closure reads** (`scratch/Graph.lean` → `graph.txt`, 154k lines; ~25 min single-threaded
   on the VM): every constant of 25 candidate modules (`N`), their uses inside the set (`D`), of other
   FR modules (`E`), and every use by a non-candidate FR module (`U`). `tool/need3.py`: seeds = the
   candidates' constants used by non-candidate modules of `Solution`'s closure (plus every constant
   of a *kept* candidate), closed under `D`, mapped to source chunks (RET-1's chunker; private names
   mapped to their user names).
5. **Choice of the set** (`plan-v1.json`). Kept (most of the module is read, or another track owns
   an importer): `FRVIR` (99/120 decls read), `FRVIRCompile` (B0), `FRVIRCompileSound` (34/38; B0's
   `FRVIRTplExt` imports it), `FRVIRTemplates` (33/35; ditto), `FRVIRTplDag` (35/39), `FRVIREval`
   (32/37), `FRKindWeight` (103/111), `FRVerifierImplOps` (121/139), `FRNodeRead*` (S-H4's `FRXOut`,
   `FRXNode`, `FRXOutRun` read all of them). Moved (13 modules): `FRVerifier` (1/21), `FRVIRSpec`
   (64/129), `FRVIRFinals` (56/68), `FRVIRFinalsSF` (32/58), `FRVIRChain` (22/36), `FRVIRMux`
   (5/30), `FRNodeLayout` (26/66), `FRVIRFinalsSG` (106/142), `FRNodeCircuit` (6/18), `FRNodeTarget`
   (56/74), `FRVerifierImplNode` (64/76), `FRVerifierImpl` (8/10), `FRNodePlan` (3/4). The unread
   parts are the heavy proofs: `flag_finZ/Lc/Sh/Lr/E/B'/P4/Pf`, `exec_finRS`, `exec_phaseZ`,
   `genPhase_ctx`, `refPhase*`, the `run_*Ops` of the unread phases.
6. **Statements before** (`scratch/StmtHash.lean`, `moved.txt` → `stmt-before.txt`), on HEAD's oleans.
7. **Mover** (`tool/move3.py`, RET-2's `move2.py` with the groups replaced, kept modules as import
   targets, the `-- RET-3:` pointer). `redo.sh` restores `src-before/`, recomputes the plan, moves and
   re-points the importers (import lines only).
8. **First Core build:** (a) 4 names a tactic names without the term using them: `toD_d`, `g3`,
   `round3Vals` (`FRVIRSpec`), `finV` (`FRVIRFinalsSG`) → `extra-seeds.txt`; (b) `open RecursionFast
   FR.X` in `FRVIRChain`'s section: `FR.X` is S-H4's namespace, not imported by Core (no moved
   declaration reads it) → `open RecursionFast` in Core; (c) **matcher sharing**: with `FRVIRSpec` and
   `FRVIRFinals` in one module, `exec_pureRun`'s `split at h` also generalised the goal (Lean shares
   structurally equal matchers within a module, so `pureRun`'s match became `exec_app`'s) and
   `simp only [hv]` made no progress. Split into `FRVIRSpecCore` (`FRVerifier`, `FRVIRSpec`,
   `FRVIRChain`) and `FRVIRFinalsCore` (`FRVIRFinals`, `FRVIRFinalsSF`): every proof verbatim.
9. **Core modules green** (5): `FRVIRSpecCore`, `FRVIRFinalsCore`, `FRVIRFinalsCoreSG`,
   `FRNodeTargetCore`, `FRVerifierImplCore`.
10. **Census after** (`clo-after.json`): 240 modules (−14, +5 Core); the 13 moved modules and
    `FRWots` (through `FRNodeCircuit`) leave `Solution`'s closure: 189.0 CPU-s at the 7763 times.
11. **First `Solution` build** (`build-sol1.log`): (a) `FRSoundness4R4Ref` names `toF_f` in a `simp`
    → extra seed; a text scan (`tool/textseeds.py`: unread X declarations whose name occurs in a
    closure module's text) finds no other tactic-only use (the other hits are doc comments, local
    `set`s, or Rev4's own namesakes); (b) `FRSoundnessCoreRows` imported `FRNodeCircuit` and reached
    `FRVIREval`, `FR.Impl`, `FR.NodeT`, … through `FRNodeCircuit → FRVIRTplFast`; the re-pointed import
    is `FRVIRFinalsCoreSG` plus `FRVIRTplFast` (B0's module, imported, not edited).
12. **Before tree** `logs/fr-build-RET3b` (copy of `fr-build-orch` at HEAD, used read-only for the
    use relation `scratch/ModUses.lean` → `moduses.txt` and for the "before" timing). Import check
    `tool/impcheck3.py`.
13. **Second/third `Solution` builds** (`build-sol2.log`, `build-sol3.log`): (a) `FRSoundnessCoreFront`
    needs `FR.NodeT` — fixed by item 11(b)'s `FRVIRTplFast` import in `CoreRows`; (b)
    `FRSoundness4R4Run` reads `X.msgItem` (S-H4's `FRXChainFlock`), which it reached through
    `CoreAcc → FRVIRChain → FRXChainFlock`: R4Run now imports `FRXChainFlock` directly (import line
    only; an edge step 2 has to handle, see the RESULT); (c) `FRSoundness4R4PosT`: `simp [hl]; omega`
    failed — the `@[simp]` lemma `posHeadVals_length` (`FRVIRSpec`) shaped `simp`'s result without
    appearing in any term of the graph. It is the only attributed declaration in the unread parts;
    added as an extra seed.
14. **`Solution` green** (`build-sol4.log`, 2,467 jobs). `tool/impcheck3.py` (use relation
    `moduses.txt` from the before tree, X constants via `graph.txt`): no module of the new closure
    misses a module it reads.
15. **First full build** (`build-FR1.log`; `FR Solution FRSubmission4Cert FRSoundness4XCtrl
    FRNodeSound4Ctrl`): three failures *outside* `Solution`'s closure, all from re-pointed paths:
    (a) `FRSoundness4R4FrCtrl` (an R4 control) reads 3.x's `relE`, `relSh`, `relRS`, `rsLeafZero`
    (residual `FRVIRFinals`/`FRVIRFinalsSF`) → `import FRVIRFinalsSF` (import line only);
    (b) `FRSoundnessPIOP` reads `Layout.Ind`, `Layout.lRows_length` (residual `FRNodeLayout`) →
    `import FRNodeLayout`; `FRSoundnessAccRun` reaches `FRWots` only through the old `FRNodeCircuit`
    path → `import FRWots` (both 3.x soundness modules outside every Rev4 closure, edited by RET-2
    before); (c) matcher sharing again, the other way round: the residual control `nodeE_bit`
    (`unfold nodeE nodeBit tgtE; split <;> rfl`) relied on `nodeBit`'s match being `nodeE`'s matcher
    in one module → `nodeBit`, `nodeE_bit` are extra seeds (they move to `FRNodeTargetCore` with
    `nodeE`). `impcheck3.py` with `ALL=1` (every module) is clean after these.
16. **Full build green** (`build-FR2.log`): `lake build FR Solution FRSubmission4Cert
    FRSoundness4XCtrl FRNodeSound4Ctrl`, 2,586 jobs, HEAD `cb12cc4` + RET-3 (HEAD since moved to
    `e4b8cd9`: docs only).
17. **Statements** (`stmt-before.txt` on the before tree, `stmt-after.txt`): 457 names; every type
    identical; every definition value identical except `rsPtIx`, whose `match` now reuses the
    structurally equal matcher `Layout.selCells.match_1` of the same Core module (RET-1's `clR2` case).
18. **Axioms** (`ax/AxRET3.lean` → `axioms.log`): all 457 in the five Core modules; only `propext`,
    `Classical.choice`, `Quot.sound`, also for `certified` and S-I's list. **Source rule**
    (`source-rule.log`): 372 files, 0 findings.
19. **Timing.** Local 4-core runs (`fr-build-RET3t/tb.sh`) started under load 14–17 and were stopped
    at the orchestrator's message (re-pin to `64378d2`, `build_s` = 1,200 s): no VM figure. The 7763
    probe: commit `3b8785b` (HEAD + RET-3's 38 Lean files + `probe.conf = si-cert`, built with a
    temporary index; the local branch untouched), branch `probe/ret3-cert`, run 40850381037.
20. **Probe result** (`logs/probe-cert-ret3/`): `build_s` 565.3 s, 241 modules, 1,888.2 CPU-s, but
    on an **Intel Xeon 8370C**. The machine factor from the 207 source-unchanged modules is 0.846.
    RET-3's net at 7763 speed is ≈ −124 CPU-s (−189.0 dropped, +65 Core), and the scaled wall time
    is ≈ 668 s. Branch `probe/ret3-cert` deleted. Stopped here at the orchestrator's message.
