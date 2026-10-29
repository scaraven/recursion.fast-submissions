# G4: the finals' flag modules on a reversed accumulator

Track G4 targets the certificate build. The probe run 40839253556 measured **696.2 s** on the EPYC
7763 against `build_s = 600`. Mid-track the core was re-pinned to `64378d2` and `build_s` became
1,200 s. The orchestrator then cut the scope to the first item: the block-wise read lemma for the
finals' flag modules. The second list (FRSkip, FRSoundnessCoreFront, FRFieldBaseCorrect, …) was not
started.

**Where the work is.**

- **Worktree.** Uncommitted, at HEAD `ee73ec9`.
- **Build tree.** `logs/fr-build-G4`, copied from `logs/fr-build-G3` and re-snapshotted on HEAD.
- **Logs.** `logs/G4/`.
- **Journal.** `stages/G4-JOURNAL.md`.

Three modules were edited: `FRSoundness4R4Fin`, `FRSoundness4R4FinSh` and `FRSoundness4R4FinLc`. No
statement changed.

## 1. Result

**Method** (as in G2/G3):

- sequential elaboration, `lean -DElab.async=false --profile`, on one pinned core;
- CPU time is user + sys;
- "before" is the saved original (`logs/G4/before/`), "after" is the worktree, both against the same
  tree (HEAD `4a8bd64`; the later HEAD `ee73ec9` replays these modules unchanged);
- before and after alternate, two rounds, and each figure is the minimum of the two.

The logs are in `logs/G4/measure-h1/` and `measure-h2/`. "7763" is the probe's per-module time, from
`logs/probe-cert-g3/probe-si-cert/out/build.log`. The 7763 "after" column is that time scaled by the
local after/before ratio: an estimate, not a measurement.

| module | 7763 before | before: CPU s, min (runs) | after: CPU s, min (runs) | change | 7763 after (est.) | kernel s, before → after |
|---|---|---|---|---|---|---|
| FRSoundness4R4FinSh | 23 | 26.34 (26.34 / 26.78) | 11.98 (12.70 / 11.98) | −55 % | ≈ 10.5 | 2.94 → 1.58 |
| FRSoundness4R4Fin | 13 | 14.65 (15.33 / 14.65) | 11.43 (11.43 / 11.59) | −22 % | ≈ 10.1 | 0.72 → 0.65 |
| FRSoundness4R4FinLc | 9 | 10.66 (10.79 / 10.66) | 9.30 (9.31 / 9.34) | −13 % | ≈ 7.9 | 0.60 → 0.48 |
| **total** | **45** | **51.65** | **32.71** | **−37 %** | **≈ 28.5 (≈ −16.5)** | **4.26 → 2.71** |

Each module's figure includes its fixed import cost, about 5 s. Simp time alone falls more:

- FinSh: 13.9 → 3.1 s;
- R4Fin: 6.2 → 3.0 s;
- FinLc: 2.35 → 1.28 s.

**Kernel time** falls in every module. In FinSh it falls from 2.94 to 1.58 s, because the proof no
longer carries 2,700 `cons_append` steps per case.

**FRSoundness4R4FinRS was not changed.** It has no literal-accumulator chain (§3).

**Code lines** (`logs/org20/scripts/loc.py`, code column): 415 → 453 (+38). R4Fin 196 → 226 (the
five lemmas and their section note), FinSh 91 → 92, FinLc 128 → 135.

**Checks.**

- **Build.** `lake build FR Solution FRSubmission4Cert FRSoundness4R4FinCtrl` at HEAD `ee73ec9` is
  green: 2,606 jobs (`logs/G4/build-r3.log`). The FinCtrl controls build.
- **Statements** (`logs/G4/check-stmt.log`).
  - **Method.** Each module, before and after, is elaborated in scratch with an `#eval` that dumps
    every constant the file declares: kind, type hash, and value hash for `def`s. The dumps are
    compared with `tools/cmpstmt.py`.
  - **Result.** 93 constants were compared. Every type hash and every user `def` value hash is
    unchanged. The added constants are the five new lemmas (§2.1).
  - **Two differences, both artifacts.** They are the private, on-demand `splitter` definitions of
    `Rev4.reloc.match_1` and `Val.eqv.match_1`. Their values name private `_sparseCasesOn` constants
    whose names contain the source file's path. The control (`logs/G4/check-stmt-control.log`)
    elaborates the same *before* source under two file names and shows exactly these two
    differences.
- **Axioms** (`logs/G4/tool/Ax.lean`, `logs/G4/axioms.log`). Only `propext`, `Classical.choice` and
  `Quot.sound` are used by:
  - the 109 constants of the three modules;
  - `flag_gFinSh` and `flag_gFinLc`;
  - `FR.Sub4.certificate_sub4` and `RecursionFast.Challenge.certified`.
- **Source rule.** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive` reports
  381 files and 0 findings (`logs/G4/source-rule.log`).

## 2. What changed

### 2.1 The read lemma: a reversed accumulator (`FRSoundness4R4Fin`)

**The cost.** `pureRun` runs each op on `r ++ L.toArray` and appends its outputs, `L ++ vs`. The flag
proofs `simp` through a 60–90-op program with `L` as one list literal. That costs two things:

- every append re-walks `L` with `List.cons_append`;
- every read walks `L` with `List.getD_cons_succ` up to the register.

Together this is about 2,700 + 2,900 rewrites per case in `flag_gFinSh` (G3 §3): quadratic in the
program's length.

**The fix.** The proofs keep the accumulator as `M.reverse`, with `M` the outputs, newest first. New
section "Running the flags on a reversed accumulator", five lemmas:

- `pureRun_nil_rev`: `pureRun … ops r [] = pureRun … ops r ([] : List Val).reverse` (`rfl`).
  - Used once, by `rw`, before the run's `simp`.
- `revAcc_app_cons`: `M.reverse ++ a :: as = (a :: M).reverse ++ as`.
  - An op's output is consed onto `M`. Each op costs O(1) rewrites, not O(|L|).
- `getD_revAcc`: `M.reverse.getD k default = ((default :: M).toArray[M.length - k]?).getD default`.
- `rd_revAcc` and `rd_revAcc0`: the same for `rd (r ++ M.reverse.toArray) (r.size + k)` (and
  `r.size`), by `rd_app` + `getD_revAcc`.
  - Simp computes `M.length` once per prefix, since its cache shares the prefixes.
  - `Array.reduceGetElem?` then reads the entry in one `dsimp` step.
  - The `default` at the head of the list takes every read past the end, so the lemma needs no side
    condition.

**Two details that mattered** (scratch runs, `logs/fr-build-G4/scratch/sh*.lean`):

- **The read lemma's form.** A first version had `if k < M.length then … else default`. The `ite`s
  cost more than they saved: 25.0 → 21.3 CPU-s. The unconditional `default ::` form avoids them.
- **`Array.reduceGetElem?` must be listed.** It belongs to the default `simp` set, which `simp only`
  does not use. Without it the reads are left as array lookups, and the closing `exact ⟨_, rfl⟩`
  pays for them by `whnf`: 0.4 s per case. G1 lists it for the same reason.

### 2.2 The flag proofs

- **R4Fin `flag_gFinZ`, `flag_gFinLr`, `flag_gFinE`, `flag_gFinB'`; FinSh `flag_gFinSh`.**
  - `rw [pureRun_nil_rev]` before the run's `simp`.
  - In the simp set, `rd_app`, `rd_app0` and `List.getD_cons_*` give way to `rd_revAcc`,
    `rd_revAcc0`, `revAcc_app_cons`, `List.append_nil`, `List.length_cons`, `List.length_nil`,
    `Array.reduceGetElem?` and `Option.getD_some`. `Nat.reduceAdd` and `Nat.reduceSub` are added
    where the set lacked them.
  - **The exported registers** (`rd (r ++ L.toArray) (….2.getD j 0)`) in Lr, E and B′. With `L` a
    `reverse`, the old `exact ⟨_, rfl, rfl, rfl⟩` timed out at `whnf`. They are now
    `refine ⟨_, rfl, ?_…⟩ <;> simp only [List.getD_cons_*, rd_revAcc, …]`, plus `<;> rfl` for
    finLr's export, which is equal up to `fv`/`pe4` unfolding.
- **FinLc `flag_gFinLc`.**
  - **The head run (`gLcHead`) and the tail run (`lcTail` from `R2`)** get the same change.
  - **The head's eight side facts** (`V1.length = 41`, `V1.getD k default = …`) are first rewritten by
    `simp only [List.length_reverse, …, getD_revAcc, Array.reduceGetElem?, …]`. Without this step,
    the existing `try simp only [… List.reverse_cons …]` would reverse the 41-value literal step by
    step.
  - The tail's `rv`, `rs` and `rr` are stated for any accumulator and apply unchanged.
- **Unused simp arguments.** The ones this change made unused were removed. The pre-existing linter
  warnings (`hc`, `List.map_append`, …) are left as they were.

## 3. Declined, and why

- **FRSoundness4R4FinRS** (7763: 10 s). It has no literal-accumulator chain. Its runs go through the
  parametric block lemmas `run_elemOps4`, `run_claimOps4` and `run_rsTail4`, which are already
  linear.
  - **Where the cost is.** `exec_gFinRS` (18.4 M heartbeats, `logs/G4/hb/rs0.txt`) is spread over
    the `es` prefix run (2.0 s traced), the `obtain … run_rsTail4` (1.4 s) and the `interval_cases`
    branch (1.2 s). No single step dominates.
- **The second list** (FRSkip, FRSoundnessCoreFront, FRFieldBaseCorrect, FRBlake2s*, FRSumcheck, …).
  Not started, per the orchestrator's instruction after the `build_s = 1,200` re-pin.

## 4. For the orchestrator

- **The pattern is reusable.** Any `simp` through `pureRun` on a literal program can take
  `rw [pureRun_nil_rev]` and the reversed-accumulator set (§2.2).
  - **Where it fits.** The 3.x `flag_fin*` in `FRVIRFinals`/`FRVIRFinalsSF`/`FRVIRFinalsSG`, which
    are RET-3's and outside the scope here. G1 declined the same quadratic `cons_append` there.
  - **Requirement.** The lemmas live in `FRSoundness4R4Fin`. A module outside its imports would need
    them moved to a common ancestor, for example `FRVIRFinalsCore`, where `pureRun` lives.
- **No statement moved, but HEAD moved twice during the track.** At RET-3 (`0aaa99b`) `rd_appT` left
  R4Fin's imports, and `rd_revAcc` was re-proved from `rd_app`. The final build and checks are at
  `ee73ec9`.
