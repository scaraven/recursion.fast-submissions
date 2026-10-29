# RET-2 JOURNAL: the 3.x soundness front out of the Rev4 certificate's closure

Blueprint 4.3, §10 changes 27 (B), step 3. Base HEAD `1c5a738` (+ queue commit); rebased on
`2f437ed` (S-I) for the final build. Tools and logs: `logs/RET2/` (tools in `logs/RET2/tool/`).

1. **Build tree.** `logs/fr-build-RET2`, a copy of `logs/fr-build-INT10` (org20). `b.sh` logs to
   `../RET2/build-last.log` and runs `lake build` under `taskset -c 24-27` (4 cores, like the
   runner; Lake 4.34 has no `-j` flag) in the 16G scope. `MINE.txt` lists RET-2's 66 modules.
2. **Census, item 1** (`tool/census.py`; `census-before.txt` for the brief's roots,
   `census-before-sol.txt` for `Solution`'s closure at `2f437ed`).
   - Brief's roots (`FRSoundness4XRunG`, `FRVerifierC4`, `FRX4Ext`, `FRSoundness4Frame`,
     `FRSoundness4Tail*`, the Rev4 controls; 27 roots): 317 of 330 modules, **67 3.x soundness
     modules (20,593 lines)**.
   - `Solution` (orchestrator's measure, `2f437ed`): 306 FR modules, **66 3.x soundness modules
     (20,485 lines)**; `FRSoundnessExtLinks` is only in the controls' closure (via
     `FRNodeSound4Ctrl → … → FRNodeRead4 → FRNodeSoundA`).
   - The direct edges (the reason each 3.x module is there):

     ```
     FRSoundness4P4aNames -> FRSoundnessFrZM        FRSoundness4R4Ref -> FRSoundnessAccSem
     FRSoundness4P4aSeg   -> FRSoundnessExtLeaf     FRSoundness4R4Rnd -> FRSoundnessFrRndV
     FRSoundness4P4bNames -> FRSoundnessFrPend      FRSoundness4R4Run -> FRSoundnessFrRun
     FRSoundness4Pos      -> FRSoundnessFrChain, FRSoundnessStepA
     FRSoundness4R4FrLc   -> FRSoundnessFrLc        FRSoundness4R4W0  -> FRSoundnessFrW0V
     FRSoundness4TailLig  -> FRSoundnessTail        FRSoundness4XFinal -> FRKState
     FRXLevel             -> FRSoundnessTruths      (S-H4)
     FRNodeSoundA         -> FRSoundnessExtLinks    (controls only; S-N1's 3.x module, no owner)
     ```
     `FRSoundness4XFinal -> FRKState` and the two R4 edges `R4FrLc`/`R4W0` are new since RET-1.
3. **What the closure uses** (`scratch/Graph.lean` → `graph.txt`: every 3.x constant, its 3.x
   dependencies (type, value, proof), the non-3.x modules it reads, and every use of a 3.x constant
   by a non-3.x FR module). `tool/plan.py`: seeds = 3.x constants used by non-3.x modules of the
   closure, minus `tail_shift`; closure inside the 3.x modules; mapped to source chunks with RET-1's
   chunker. Result: **390 declarations (+ `FrChain`'s anonymous `DecidablePred` instance) from 46
   of the 3.x modules, ≈ 2,860 of their 15,772 lines**. `FRSoundnessFrChain` (531 of 713 lines) and
   `FrSh`/`FrWalk` are the large parts. No moved declaration is `private`; the 46 modules have no
   notation, `attribute` or `mutual` commands. Eq-lemma/matcher/splitter constants that a module
   realized for another module's definition (`X.eq_1` attributed to a 3.x module) are not
   declarations: Lean regenerates them on demand.
4. **Item 2: `tail_shift`.** Moved verbatim into a new control module `FRSoundness4TailShift`
   (imports `FRSoundness4TailLig`, `FRSoundnessTail`), outside the certificate's closure;
   `FRSoundness4TailLig` drops `import FRSoundnessTail`; `FR.lean` imports the new module.
5. **Grouping** (`tool/move2.py`, RET-1's chunker; per source module a `section … end` block with the
   context commands replicated and empty sections pruned; source modules ordered topologically on
   the declarations' module-level dependencies):

   | Core module | from | imports |
   |---|---|---|
   | `FRSoundnessCoreChain` | `Defs`, `FrChain` | `CoreDefs` |
   | `FRSoundnessCoreTruths` | `StepA`, `StepB`, `StepC`, `Truths` | `CoreSteps`, `FRRSEval` |
   | `FRSoundnessCoreRows` | `StepE`, `Hide`, `FRKState`, `PIOP`, `Tail`, `TailM`, `Front`, `Rows`, `FrW0`, `FrRS`, `FrPend`, `FrZ`, `FrB`, `FrE`, `FrL`, `FrW0V`, `FrRS0` | `CoreTail`, `CoreTruths`, `FRNodeCircuit`, the contract's `Certificate`/`PaperTheorem` |
   | `FRSoundnessCoreFront` | `FrSh`, `FrS`, `FrZM`, `FrBind` | `CoreRows` |
   | `FRSoundnessCoreAcc` | the 12 `Acc*`, `FrRun`, `FrRnd`, `FrRndV`, `FrLc`, `ExtStmt`, `ExtLeaf` | `CoreTail`, `FRVIRChain`, `FRVerifierImplOps` |
   | `FRSoundnessCoreWalk` | `FrWalk` | `CoreAcc`, `CoreFront` |

   Imports = the non-3.x FR modules the moved constants read + earlier Core modules, transitively
   reduced. No such module imports a 3.x soundness module (checked).
6. **Import check before building** (`scratch/ModUses.lean` → `moduses.txt`, `tool/impcheck.py`):
   for every non-3.x module of the new closure, every FR module whose constants it uses (3.x
   constants mapped to their Core home) is in its import closure. Realized-constant noise (an
   `eq_N` attributed to a module outside the user's old closure) is skipped. With the re-pointed
   imports below: no module misses anything.
7. **Re-pointed imports** (import lines only, a `-- RET-2:` line above them):
   `P4aNames` FrZM→CoreFront; `P4aSeg` ExtLeaf→CoreAcc; `P4bNames` FrPend→CoreRows; `Pos`
   FrChain→CoreChain, StepA→CoreTruths; `R4FrLc` FrLc→CoreWalk; `R4Ref` AccSem→CoreAcc; `R4Rnd`
   FrRndV→CoreAcc; `R4Run` FrRun→CoreAcc; `R4W0` FrW0V→CoreRows; `XFinal` FRKState→CoreRows.
   No name changed, so no proof text changed.
8. **First Core build:** two misses, both names a tactic script mentions without the final term
   using them: (a) RET-1's mover drops `open Circ` lines; `PIOP`'s `open Circ Eval` is needed
   (`entry`) — the drop removed from `move2.py`; (b) `levelPhases_length` (`AccSeg`), named in a
   `simp [...]` whose result does not use it — added as an extra seed (`extra-seeds.txt`). Re-run
   from the saved originals (`redo.sh`): the six Core modules green.
9. **Statements before** (`scratch/StmtHash.lean` on the old oleans, before the 3.x modules were
   rebuilt): `stmt-before.txt`, 393 names (the 390 + the instance + `levelPhases_length`'s seed +
   `tail_shift`), none missing.
10. **Full build 1** (`b-full1.out`): one error, in `FRSoundnessExtAll` (outside every Rev4 closure):
    `X.E_leaf`, `E_node_of_run` came to it only through `FRNodeSoundA → FRSoundnessExtLinks`, and I
    had re-pointed `FRNodeSoundA`. `FRNodeSoundA` is not in the brief's edit list (S-N1's 3.x module)
    and not in `Solution`'s closure (only `FRNodeSound4Ctrl`'s), so the edit was reverted
    (`git checkout`); its re-point is recorded for the orchestrator instead.
11. **Full build 2** (`build-FR.log`): `lake build FR Solution FRSoundness4TailShift` + the 27 roots:
    green, 2,565 jobs, at `2f437ed` + RET-2. The "automatically included section variable" warnings
    in `CoreAcc` are the same two `AccLog` had before.
12. **Statements after** (`stmt-after.txt`): `diff stmt-before.txt stmt-after.txt` empty — all 393
    types, and the values of the definitions among them, hash-identical. Axioms (`ax/AxRET2.lean`,
    `axioms.log`): every moved name sits in an `FRSoundnessCore*` module (`tail_shift` in
    `FRSoundness4TailShift`); only `propext`, `Classical.choice`, `Quot.sound`, also for
    `certified`, `certificate_sub4` and the rest of S-I's list. Source rule: 354 files, 0 findings.
13. **S-H4's re-point, checked without editing `FRXLevel`.** `scratch/FRXLevelP.lean` (=
    `FRXLevel` with `import FRSoundnessCoreTruths`) elaborates (`frxlevel-repoint.log`); the
    timing tree's `after-h4` run overlays it and builds `Solution` green (`tbuild-after-h4.log`).
14. **Census, `Solution`** (`census-*-sol.txt`; module CPU from S-I's 7763 run
    `logs/S-I/run-40810876665/build-modules.txt`):
    - before (`2f437ed`): 306 modules, 66 3.x soundness modules, 476.8 CPU-s of 2,972.7;
    - after: 251 modules (−61 +6 Core); 5 3.x modules left (`Defs`, `StepA`, `StepB`, `StepC`,
      `Truths`, 1,492 lines), all through `FRXLevel → FRSoundnessTruths`; 436.5 CPU-s drop out;
    - after + S-H4's one-line edit: 246 modules, 0 3.x modules; 476.8 CPU-s drop out.
15. **Timing** (`logs/fr-build-RET2t`, `tb.sh`: fresh `lake build Solution` of the entry, packages
    and org20 prebuilt, `taskset -c 24-27`, 16G scope, `/usr/bin/time -v`). HEAD moved twice during
    the runs (S-E13a/S-E14 added `FRNodeRows4*` to `Solution`'s closure), so the first `before`
    (at `2f437ed`) is not comparable; `before2`, `after` and `after-h4` have the same Lean sources
    apart from RET-2 (`e2b7bc2`/`adc7a74`: no Lean change in between). Results in the RESULT §5.
16. **Final build** at HEAD `43b72fc` + RET-2 (`build-FR-final.log`): green, 2,582 jobs. Axioms
    (`axioms-final.log`) and source rule (`source-rule-final.log`, 357 files, 0 findings) re-run.
