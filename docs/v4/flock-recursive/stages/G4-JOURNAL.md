# G4 journal: the finals' flag modules on a reversed accumulator

Track G4. The goal is to cut elaboration time in the certificate's heaviest remaining modules without
changing any statement.

- **Start.** Worktree HEAD `0c80576`.
- **Build tree.** `logs/fr-build-G4`, copied from `logs/fr-build-G3`; `MINE.txt` lists the four flag
  modules and `FRSoundness4R4FinCtrl`.
- **Tools.** `logs/G4/tools/` (G3's, re-pointed).
- **Logs.** `logs/G4/`.
- **Report.** `reviews/G4-golf.md`.

## 2026-10-29

- **Closure.** `tools/closure.py Solution` at HEAD gives 249 modules (`logs/G4/closure-Solution.txt`).
  All four flag modules are in it, and so are the second list's candidates.
- **Originals.** Saved in `logs/G4/before/`.
- **Baseline.** `./b.sh FR Solution FRSubmission4Cert` at HEAD is green (`logs/G4/build-base.log`).
- **Scratch experiment on `flag_gFinSh`** (`fr-build-G4/scratch/sh*.lean`). The accumulator is kept as
  `M.reverse`, with `M` the outputs, newest first.
  - **Setup.** `rw [pureRun_nil_rev]` turns the initial `[]` into `[].reverse`.
  - **Appends.** `revAcc_app_cons` (`M.reverse ++ a :: as = (a :: M).reverse ++ as`) turns each
    op's append into a cons. This costs O(1) per op, not O(|L|).
  - **Reads, first form.** `rd (r ++ M.reverse.toArray) (r.size + k)` became an `if k < M.length`
    lookup. The `ite`s cost more than they saved: 25.0 → 21.3 CPU-s.
  - **Reads, second form.** The unconditional `(default :: M).toArray[M.length - k]?` puts the
    out-of-range case at entry 0. It gave 14.6 CPU-s, but the reads were still not reduced, because
    `simp only` does not run `Array.reduceGetElem?` unless it is listed (G1 lists it).
  - **With `Array.reduceGetElem?` listed:** 25.0 → 9.95 CPU-s, simp 15.2 → 3.4 s, kernel
    3.24 → 1.7 s.
- **Orchestrator** (mid-track). The core was re-pinned to `64378d2`, and `build_s` is now 1,200 s.
  The new scope is to finish the flag-module item, get a green build and report. The second list was
  not started.
- **Lemmas, in `FRSoundness4R4Fin`** (new section "Running the flags on a reversed accumulator"):
  `getD_revAcc`, `rd_revAcc`, `rd_revAcc0`, `revAcc_app_cons`, `pureRun_nil_rev`.
- **R4Fin: `flag_gFinZ`, `flag_gFinLr`, `flag_gFinE`, `flag_gFinB'`.** Each gets
  `rw [pureRun_nil_rev]` and the reversed-accumulator simp set in place of
  `rd_app`/`rd_app0`/`List.getD_cons_*`.
  - **The extra conjuncts.** These are the `rd (r ++ L.toArray) (….2.getD j 0)` exports. The old
    `exact ⟨_, rfl, rfl, rfl⟩` timed out at `whnf` (200 k heartbeats) once `L` was a `reverse`. They
    are now `refine ⟨_, rfl, ?_…⟩ <;> simp only [List.getD_cons_*, rd_revAcc, …]`, plus `<;> rfl`
    for finLr's export, which is equal up to `fv`/`pe4` unfolding.
  - **Unused simp arguments.** The ones this change created were removed. Pre-existing warnings
    (`hc`) are untouched.
- **FinSh: `flag_gFinSh`.** The same change: `rw [pureRun_nil_rev]`, and the simp set swaps
  `rd_app`/`rd_app0`/`List.getD_cons_*` for the reversed-accumulator set.
- **FinLc: `flag_gFinLc`.**
  - **The head run (`gLcHead`).** It gets `rw [pureRun_nil_rev]` and the new reads. Its eight side
    facts (`V1.length = 41`, `V1.getD k default = …`) are first rewritten by
    `simp only [List.length_reverse, …, getD_revAcc, Array.reduceGetElem?, …]`. Otherwise the old
    `try simp` would reverse the 41-value literal with `List.reverse_cons`.
  - **The tail run (`lcTail` from `R2`).** The same change. `rv`, `rs` and `rr` are stated for any
    accumulator and apply unchanged.
- **FinRS: not changed.** It has no literal-accumulator chain. Its runs are already parametric block
  lemmas (`run_elemOps4`, `run_claimOps4`, `run_rsTail4`).
  - **Heartbeats** (`logs/G4/hb/rs0.txt`): `exec_gFinRS` 18.4 M, spread over `es` (2.0 s traced),
    `obtain … run_rsTail4` (1.4 s) and the `interval_cases` branch (1.2 s), with no single dominant
    step.
- **HEAD moved during the track.**
  - **RET-3 `0aaa99b`.** `FRVIRSpec`, and with it `rd_appT`, left R4Fin's imports. `rd_revAcc` is
    now `rd_app` + `getD_revAcc`.
  - **Then `4a8bd64` and `ee73ec9`.** The four flag modules were replayed: none of their imports
    changed.
- **Statements** (`logs/G4/check-stmt.log`).
  - **Method.** Each module (before and after) is elaborated in scratch, with an `#eval` that dumps
    every constant the file declares: kind, type hash, and value hash for `def`s. The dumps are
    compared with `tools/cmpstmt.py`. Private prefixes are normalized.
  - **Result.** 93 constants were compared. Every type hash and every user `def` value hash is
    unchanged. Five lemmas were added.
  - **Two differences, both artifacts.** These are the private on-demand `splitter` defs of
    `Rev4.reloc.match_1` and `Val.eqv.match_1`. Their values name file-dependent private
    `_sparseCasesOn` constants. The control (`logs/G4/check-stmt-control.log`) elaborates the same
    *before* source under two file names and shows the same two differences.
- **Final build** at HEAD `ee73ec9` (`logs/G4/build-r3.log`):
  `FR Solution FRSubmission4Cert FRSoundness4R4FinCtrl` is green, 2,606 jobs. The FinCtrl controls
  build.
- **Axioms** (`logs/G4/tool/Ax.lean`, `logs/G4/axioms.log`). The 109 constants of the three edited
  modules, `flag_gFinSh`, `flag_gFinLc`, `certificate_sub4` and `certified` use only `propext`,
  `Classical.choice` and `Quot.sound`.
- **Source rule** (`logs/G4/source-rule.log`): 381 files, 0 findings.
- **Measurement** (`logs/G4/measure-h{1,2}/summary.txt`, tree at `4a8bd64`). Before and after
  alternate, two rounds, on one pinned core; each figure is the minimum.

  | module | before CPU s | after CPU s | kernel s |
  |---|---|---|---|
  | R4Fin | 14.65 | 11.43 | 0.72 → 0.65 |
  | FinSh | 26.34 | 11.98 | 2.94 → 1.58 |
  | FinLc | 10.66 | 9.30 | 0.60 → 0.48 |

  The table in `reviews/G4-golf.md` adds the 7763 estimate.
