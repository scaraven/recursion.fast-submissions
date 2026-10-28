# RET-1 JOURNAL: the 3.x soundness modules' position-free declarations into `FRSoundnessCore*`

Blueprint 4.2, §10 changes 27 (B), step 3, preparatory part. Base HEAD `60b65cc`.

1. **Build tree.** `logs/fr-build-RET1`: `gen.sh`/`snap.sh` from `fr-build-INT6` (org20), `.lake`
   from `fr-build-orch` (built at HEAD, so `lake build FR` was cached: `logs/RET1/build-base.log`,
   2,466 jobs, 0 rebuilt). `MINE.txt` lists the edited and new modules.
2. **Which declarations.** `logs/T4/keep.txt` gives short names; `logs/T4/deps.txt` resolves each
   to one module and full name (`scratch` list `keep195.txt`; every name resolves uniquely).
3. **Closure** (`fr-build-RET1/scratch/Clos2.lean`, `logs/RET1/clos2.txt`). From the 195 plus T4's
   direct uses in `FRSoundnessDefs`/`FRSoundnessPIOP` (`L₀`, `StabExt`, `pRoundG`, `ext_dropLast`,
   `algebraMap_f₀`, …), follow type, value **and proof** through every constant of a 3.x
   soundness module. Mark a constant bad if it reaches `FRVIRFinalsSG`, `FRVIREval`, the 3.x
   verifier modules, or `Kind`/`lvl`/`fsItems`/`items`/`fsStarts`/`fsRanges`. Bad: `rowMat` (PIOP,
   `Eval.entriesOf`), hence `wE`, `mle_wE`, `sum_wE`; `mleN_wSplit` (`uHat`) and `eqCellK_eq`
   (`eqCellK`), both `FRVIRFinalsSG`; `hEll_le` (its proof unfolds `lvlStar = lvl .L32`).
   `truthP1_zero.sum_mul_sum_comm` is a `where` auxiliary of the kind-dependent `truthP1_zero`.
4. **Decisions.**
   - `hEll_le`: moved. Its statement is `hEll i ≤ 6`, and `hEll` itself is `(lvlStar i).ell`.
     The `Kind` reference comes only from unfolding `lvlStar` in the proof, and the Core modules
     import `FRTranscriptDefs` anyway (`Digest`, `Item`, `bytesAt`, `squeezeQ`).
   - `mleN_wSplit`, `eqCellK_eq`: moved to a separate shim, `FRSoundnessCoreSG`, which imports
     `FRSoundnessCoreWeights` and `FRVIRFinalsSG`. T4's `TailFold` needs `mleN_wSplit`, so without
     the shim T4 would still import 3.x `FRSoundnessWeights` and the chain below it.
   - `wE`, `mle_wE`, `sum_wE` (and `rowMat`): left in place. They need `FRVIREval`, which imports
     `FRNodeLayout`/`FRVIRMux`/`FRVIRCompileSound`. T4 does not use them.
   - The 3.x helpers needed by the closure: 12 from `FRSoundnessDefs`, plus `algebraMap_f₀`.
5. **Mover** (`logs/RET1/tool/{chunks,move}.py`). It splits each module into top-level chunks:
   - a declaration chunk is its doc comment, attributes and `open … in`/`set_option … in`/`omit …
     in` prefix, plus the command itself;
   - a context chunk is `namespace`/`section`/`end`/`variable`/`open`/`set_option`/`include`.

   The Core text for a source module is every context chunk plus the moved declarations, with
   `section`/`namespace` blocks that contain no declaration pruned. The 3.x module loses the moved
   chunks and gains `import FRSoundnessCore…`.
   - First run: `include`/`omit … in` were not recognised, so `include` lines were swallowed into
     the preceding chunk. Fixed, the 3.x files restored from HEAD, and the mover re-run.
   - `open Circ` is dropped from Core: `Circ` is `FRVIRTplCore`'s namespace, and no moved
     declaration uses it.
6. **Build.** `FRSoundnessCoreSteps` built first time. The 3.x chain to `FRSoundnessLigFinal` was
   green after the `include` fix (`build-2.log`).
7. **T4 imports.**
   - `FRSoundness4TailStep`: `FRSoundnessLigFinal` → `FRSoundnessCoreTail`, `FRSoundnessCoreSG`.
   - `FRSoundness4TailTruths`: + `FRRSEval`, `FRBlockStream`, the theory modules 3.x `Truths`
     imported (`encF`, `coeffsOfValuesD`, `wAtD`).
   - `FRSoundness4TailLig`: + `FRSoundnessTail`, only for the control `tail_shift`, which compares
     T4's positions with 3.x's `p1Start`/`cStart`/`p3S0`/`pfStart`.

   `FRSoundness4TailFront` green (`build-3.log`).
8. **First full build.** `lake build FR` green, 2,471 jobs. Axioms: 204 moved, all in Core, only
   the standard three. Source rule: 0 findings on HEAD + RET-1.
9. **`FRSoundnessCoreDefs` split.** `FRSoundnessDefs` imported only `FRLog` before RET-1. With the
   Defs helpers inside `FRSoundnessCoreSteps`, `FRSoundnessDefs`, and through it `FRSoundnessFrChain`
   and `FRSoundness4Pos`, waited on `FRSumcheck`/`FRRS`/`FRProximityFold` and the 1,000-line Core.
   Fix: a separate `FRSoundnessCoreDefs` (imports `FRLog` only), and `FRSoundnessCoreSteps` imports
   it. Re-run from HEAD's 3.x files (`move.py`, then `post.py` for the headers). `lake build FR
   FRSoundnessCoreSG` green, 2,481 jobs. HEAD had moved to `4919027` (P4d/R4b, S-E12b). Neither
   commit touches the edited files.
10. **Statement check** (`scratch/StmtHash.lean`, `logs/RET1/stmt-{before,after}.txt`). Compared the
    hash of each moved declaration's type, and of its value for definitions, between
    `fr-build-RET1b` (HEAD 60b65cc) and `fr-build-RET1`.
    - All 204 types are identical.
    - One value differs: `clR2`. It now reuses the matcher `clR.match_1`, because Lean shares
      structurally equal matchers within one module and `clR` and `clR2` now sit in the same
      module. The value is the same up to the auxiliary name, and `FR.Snd.clR2.match_1` no longer
      exists. No source text names it.
11. **Times** (`time.sh`, sequential, one core, `-DElab.async=false --profile`; `times.txt`).
    - The 19 3.x modules before: 262.1 s.
    - The 19 modules after: 213.7 s, plus 6 Core modules at 55.7 s, so 269.4 s in total.
    - The +7.3 s is the start-up of the 6 extra modules (≈ 6 s each).
