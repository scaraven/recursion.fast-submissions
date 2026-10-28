# INT-6 journal: re-pin onto core PR #20 (`6d05d00`) and the API adaptation (revision 4.0 (a))

## Setup (2026-10-28)

- `logs/org20`: `git -C logs/core-v20/core archive pr20 | tar -x` (= `6d05d003d46d…`, recorded in
  `logs/org20/.core-commit`), `.lake/packages → logs/pkgs`, then `harness/org-setup.sh logs/org20`
  under the 16G scope (`logs/INT-6/org-setup.log`, 219 s; steps logged in `logs/org20/logs/org-setup/`).
  `logs/org` was produced the same way at `15dac52` (no `.git`; `.lake/packages → logs/pkgs`;
  `logs/org/logs/org-setup/*.log`).
- `lake-manifest.json`, `lakefile.toml`, `lean-toolchain`: byte-identical between `logs/org` and
  `logs/org20` (`diff`), and `git diff 15dac52 pr20 -- lake-manifest.json lakefile.toml
  lean-toolchain` is empty. Before org-setup: `lake build --no-build +…BF64.Ext3 +…BF64.Bytes
  Mathlib` in `logs/org20` → "All targets up-to-date (8952 jobs)": nothing in `logs/pkgs` needs a
  rebuild. org-setup's step 4 (`extlibs.log`) built only `RecursionFast.*` and `Nop`: no package
  object was rebuilt.
- Build tree `logs/fr-build-INT6`: `snap.sh` (HEAD snapshot, `MINE` symlinks) and `gen.sh`, both
  requiring `logs/org20`; `lake-manifest.json` with the `RecursionFast` path `logs/org20`.
- `logs/INT-6/axiomaudit-org20.log`: the contract's `axiomaudit` (organiser declarations of
  `6d05d00`): PASS, 154 theorems use no axiom.

## Build 0 (HEAD unchanged against org20; `logs/INT-6/build-0.log`)

Two errors, everything downstream blocked: `FRFormat.lean:57` (`proofCap` unknown, parsed as an
auto-bound variable) and `FRKState.lean:50` (`KS` is no longer `Nonempty KState ∧ …`).

## Edits

- `FRFormat`: `piSize_le_proofCap` → `piSize_lt_word : piSize < 2 ^ 64`.
- `FRVerifier`: `accWith`'s first conjunct `decide (p.π.size < 2 ^ 64)` (mirrors `Submission.acc`);
  `acc_eq` unchanged in statement and proof; `fits_of_accWith` takes the word bound directly.
  `complete` unchanged: `complete_withError_zero` (Library/Completeness) now goes through
  `completeWithError_iff`/`prob` itself.
- `FRKState.ks_of`: body `(kstate_of …).ks hq` (`KState.ks`, import `Library.PaperTheorem`).
- `FRSoundnessCompose.ks_of_front` (new): `KS` from `FrontObl` + `FinalLaw` via `KState.ks`.
- `FRNodeCircuit.child_sound`/`node_sound`, `FRNodeSoundA.readSigned_fmt`: `≤ proofCap` → `< 2 ^ 64`.
- `FRXComputes`: `computes_Eof`, `halts_with`, `halts_of_tape`: domain `≤ 8 * outCap` (the W copy of
  a `2^27`-byte proof is exactly `outCap` words; `omega` closes it). `FRXLeaf.run_leaf`:
  `piSize ≤ 8 * outCap`. `FRXSpec`: comments only.
- **The W branch (`FRSoundnessAccRun`)**: `size_encode_lt` (an accepted `W` witness encodes below
  `2^64` bytes) is false without `proofCap` (two children of `2^64 − 1` bytes each); deleted.
  `signedWords_length_lt`: `< 2^32` → `< 2^62`. `acc_W` takes `hπ : π.size < 2 ^ 64`; new
  `acc_W_dec`, `WBeyond S vk` (the `final` law on accepted `W` proofs of `≥ 2^64` bytes),
  `acc_W_all` (both), control `wBeyond_of_decode`. `hWB : WBeyond S vk` threaded through
  `hAcc_of`, `hAcc_of_E`, `finalLaw_of_run` (FRSoundnessAcc), `hAcc_of_fin` (AccLog),
  `kstate_front_of` (FrK), `hAcc_of_finR`, `kstate_front_ofR` (ExtR), `kstate_front_ofE` (ExtAll).
- Docs: "the contract's `KState`" → "the library's" in FRKState, Hide, StepB, StepE.
- Name clashes: the 43 new declarations of `Library/Prob.lean`, `Library/KS.lean` against every
  `FR*` declaration: one homonym, `RecursionFast.ind` vs `FR…ind` (`FRNodeReadP`); no ambiguity
  arose in the build.

## Build 1 (`logs/INT-6/build-1.log`): `lake build FR` green, 2,408 jobs.
- Added after build 1: `FRSoundnessCompose.ks_of_front`; doc edits in Hide/StepB/StepE (build 2
  green, 2,408 jobs, `logs/INT-6/build-2.log`).
- The coordinator reported HEAD moved to `467a043` (S-T1 committed: FRKindWeight,
  FRVerifierImpl(Ops), FRVIRTplRun, FRVIRTplFast; disjoint from INT-6's 18 modules). Profiling
  stopped, re-snapshot from `467a043` (the five S-T1 files byte-equal to HEAD), **build 3 green,
  2,408 jobs, 0 errors, 0 `sorry`** (`logs/INT-6/build-3.log`); axioms re-checked
  (`logs/INT-6/axioms.log`); profiles (`logs/INT-6/prof-*.log`, `prof-summary.txt`); source rule
  of `6d05d00` (`logs/org20/scripts/source-rule.py`, byte-equal to `pr20`'s): 183 files, 0 findings.
