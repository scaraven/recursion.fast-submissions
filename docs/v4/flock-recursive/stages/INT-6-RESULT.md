# INT-6 RESULT: the entry on core PR #20 (`6d05d00`), revision 4.0 (a)

**Status: `lake build FR` green against `logs/org20` (core `6d05d00`): 2,408 jobs, 0 errors, no
`sorry`** (`logs/INT-6/build-3.log`, HEAD `467a043` + INT-6's 18 modules). Nothing committed, and
`.contract` was not touched. Revision 3.17's design is kept everywhere. None of 4.0's shapes was
started. Journal: `INT-6-JOURNAL.md`.

## 1. Setup

- **`logs/org20`**: `git -C logs/core-v20/core archive pr20 | tar -x` (core `6d05d003d46d…`,
  recorded in `logs/org20/.core-commit`), `.lake/packages → logs/pkgs`, then
  `harness/org-setup.sh logs/org20` under the 16G scope: 219 s, every step succeeded
  (`logs/INT-6/org-setup.log`, `logs/org20/logs/org-setup/`). `logs/org` was made the same way at
  `15dac52`: it has no `.git`, and its packages are linked the same way.
- **Package tree `logs/pkgs`: shared and unchanged.** `lake-manifest.json`, `lakefile.toml` and
  `lean-toolchain` are byte-identical between `logs/org` and `logs/org20`, and the
  `15dac52..pr20` diff of these files is empty. Before the setup, `lake build --no-build` of
  CompPoly's BF64 modules and Mathlib in `logs/org20` printed "All targets up-to-date (8952
  jobs)". In step 4 of the setup only `RecursionFast.*` and `Nop` were built; no package object
  was built. `lake update` and `cache get` were never run.
- **Build tree `logs/fr-build-INT6`**:
  - `snap.sh` takes a HEAD snapshot and makes `MINE` symlinks. `MINE.txt` lists INT-6's 18
    modules.
  - `gen.sh` builds straight from the worktree's `lean/`.
  - Both scripts, and `lake-manifest.json`, require `logs/org20`.
- **The contract's axiom audit** (`axiomaudit` at `6d05d00`): PASS, 154 theorems use no axiom
  (`logs/INT-6/axiomaudit-org20.log`). The gate needs a certificate theorem, which is S-I's, so it
  was not run.

## 2. What changed, file by file (code lines from `scripts/loc.py`; `logs/INT-6/loc.txt`)

Totals over the 18 modules: code lines went from 3,849 to 3,874, and theorems from 346 to 349.

| Module | code before → after | change |
|---|---|---|
| FRFormat | 123 → 123 | `piSize_le_proofCap` → `piSize_lt_word : piSize < 2 ^ 64` |
| FRVerifier | 138 → 138 | `accWith`'s first conjunct is now `decide (p.π.size < 2 ^ 64)`, which mirrors `Submission.acc`. `acc_eq` is unchanged, statement and proof. `fits_of_accWith` uses the word bound directly. `complete` is unchanged: the library's `complete_withError_zero` now goes through `prob`. |
| FRKState | 28 → 29 | `ks_of` := `(kstate_of …).ks hq` (`KState.ks`; imports `Library.PaperTheorem`); docs |
| FRSoundnessCompose | 324 → 329 | **new `ks_of_front`**: `KS … epsR S.qV` from `FrontObl` + `FinalLaw` + the query bound, via `KState.ks` (the B-14 route) |
| FRNodeCircuit | 102 → 102 | `child_sound`'s `hsize` and `node_sound`'s `hs₁`/`hs₂`: `≤ proofCap` → `< 2 ^ 64` |
| FRNodeSoundA | 181 → 181 | `readSigned_fmt`: first conjunct changed from `≤ proofCap` to `< 2 ^ 64` |
| FRXComputes | 226 → 227 | `computes_Eof`, `halts_with`, `halts_of_tape`: the domain changed from `≤ proofCap`/`≤ 2^20` to `≤ 8 * outCap`. The `W` copy of a `2^27`-byte proof is exactly `outCap` words, and `omega` closes the bound. |
| FRXLeaf | 132 → 132 | `run_leaf`: `piSize ≤ 8 * outCap` (proof only) |
| FRXSpec | 200 → 200 | comments only (the `W` case "above `8 · outCap`") |
| FRSoundnessAccRun | 214 → 225 | the `W` branch; see §3 |
| FRSoundnessAcc, AccLog, FrK, ExtR, ExtAll | +1 to +2 each | the `hWB : WBeyond S vk` hypothesis is passed through (§3) |
| FRSoundnessHide, StepB, StepE | unchanged | docs: "the library's `KState`" |

**`KState` imports.** No module imports `Contract.Security` by name. `KState` reaches every user
through `FRLog`'s import of `RecursionFast.Library.Security`. So the import paths needed no
change, only the doc texts. **`failProb`**: the entry never named it.

**`Submission`/`Certificate`/`Extractor`/`Relation`/`Oracle`/`Tree`**: the diff changes only
`acc`'s first conjunct, the domain of `Computes`, the deletion of `proofCap`, `KS`,
`CompleteWithError` (now through `prob`) and docs. The fields of `Submission` and `Certificate`
are unchanged.

**Name clashes.** I checked the 43 new declarations of `Library/Prob.lean` and `Library/KS.lean`
against every `FR*` declaration. There is one homonym: `RecursionFast.ind` and `FRNodeReadP`'s
`ind`. It caused no ambiguity in the build. `WBeyond`, `acc_W_dec`, `acc_W_all`,
`wBeyond_of_decode`, `ks_of_front` and `piSize_lt_word` are new names, and none of them is in
the core.

## 3. Finding: the `W` branch beyond the word (`WBeyond`)

`size_encode_lt` ("an accepted `W` witness encodes below `2^64` bytes") followed from `proofCap`
and is **false at `6d05d00`**. A `W` node with two accepted children of up to `2^64 − 1` bytes
each encodes to about `2^65` bytes, and `V`'s `W` branch accepts it.

- The verifier cannot reject such proofs. Completeness is required for every witness, and the
  contract states this case itself (`Certificate.lean`, V4-A11; `Library/WitnessSending`,
  "accepts proofs of every size up to about `2^65` bytes").
- `X.E = Eden` reads `|π|` on the tape as a 64-bit word, so `FRXSpec.E_W` holds only for
  `|π| < 2^64`.

So `final` on these proofs is a new residual. **I deleted `size_encode_lt`.** The new
declarations:

- `acc_W` now takes `hπ : π.size < 2 ^ 64`.
- **`WBeyond S vk`** (a definition): every accepted `W` proof of `≥ 2^64` bytes is extracted to a
  witness of `Rel (S.acc vk)`.
- `acc_W_all` gives the whole `W` branch: `acc_W` below the word, `WBeyond` above it.
- `acc_W_dec`: an accepted `W` proof decodes to a witness of the relation.
- **Positive control `wBeyond_of_decode`**: an `E` whose `W` case is `decode` at every size meets
  `WBeyond`. The contract's witness-sending `E` is such an `E`, so `WBeyond` is satisfiable.
- **Negative control: none.** Refuting `WBeyond` for some `E` needs an accepted proof of `2^64`
  or more bytes in the kernel, about 60 nested `W` levels. I did not build it (open question 2).

**`X.E` does not meet `WBeyond` in general**: its tape carries `|π| mod 2^64`. So the
`kstate_front_of*` routes for `E = X.E` now depend on `hWB` in the same way they already depend
on `hOut` (O3′). Both close under B-15: `E := if InDom then E_den else E_search`, owned by S-H2n.
S-H2n should either:
- put `π.size ≤ 8 * outCap` into `InDom`, so that `WBeyond`'s proofs are outside the domain and
  `E_search`/`search_spec` discharge them; or
- prove `WBeyond` directly from `E_search`.

## 4. Statements that changed because the contract changed

1. `FRFormat.piSize_le_proofCap` is replaced by `piSize_lt_word`, because `proofCap` was deleted.
2. `FRVerifier.accWith` (a definition): the first conjunct is now `< 2 ^ 64`. AGENTS.md §7.5
   requires `accWith` to mirror `acc`.
3. Hypotheses changed from `≤ proofCap` to `< 2 ^ 64`. Each theorem is stronger:
   - `FRNodeCircuit.child_sound`, `node_sound`;
   - `FRXComputes.computes_Eof`, `halts_with`;
   - `halts_of_tape`: `a ≤ 2^20` → `a ≤ 8 * outCap`.

   These mirror `acc` and `Computes`.
4. `FRNodeSoundA.readSigned_fmt`: the first conjunct of its conclusion is now `< 2 ^ 64`, the
   form `node_sound` needs.
5. `FRSoundnessAccRun.signedWords_length_lt`: `< 2 ^ 32` → `< 2 ^ 62`, because the proof is now
   bounded only by the word.
6. `FRSoundnessAccRun.size_encode_lt`: **deleted** (false, §3). `acc_W` gains `hπ`.
7. These gain the hypothesis `hWB : WBeyond S vk` (§3):
   - `hAcc_of`, `hAcc_of_E`, `finalLaw_of_run` (FRSoundnessAcc);
   - `hAcc_of_fin` (AccLog);
   - `kstate_front_of` (FrK);
   - `hAcc_of_finR`, `kstate_front_ofR` (ExtR);
   - `kstate_front_ofE` (ExtAll).
8. Same text, new meaning, because the contract's definitions changed:
   - `FRKState.ks_of` (`KS` is now the textbook game; the body is `KState.ks`);
   - `FRVerifier.complete` (`CompleteWithError` through `prob`);
   - `FRXExt.computes` (`Computes` at `8 · outCap`);
   - `acc_eq`.

No other statement changed. All existing controls are kept. One new control was added
(`wBeyond_of_decode`).

## 5. Checks

- **Axioms** (`logs/INT-6/axioms.log`, final tree): `propext`, `Classical.choice`, `Quot.sound`
  only, for:
  - `acc_eq`, `implC_meets`, `kstate_of_front`, `finalLaw_of_run`, `computes`, `E_leaf`, `E_node`;
  - the `KState.ks` route theorems `ks_of` and **`ks_of_front`**;
  - `acc_W_all`, `wBeyond_of_decode`, `kstate_front_ofR`, `kstate_front_ofE`, `complete`.

  `piSize_lt_word` uses `propext` only.
- **Source rule** of `6d05d00` (`logs/org20/scripts/source-rule.py`, byte-equal to `pr20`'s): 183
  files, 0 findings (`logs/INT-6/source-rule.log`). I ran the org20 copy and did not check out
  `pr20` in `logs/core-v20/core`; that clone stays on `main`.
- **Sequential profiles** (`taskset -c 7 lake env lean -DElab.async=false --profile`, one module
  at a time; `logs/INT-6/prof-summary.txt`, `prof-<M>.log`):
  - wall time over the 18 modules: 183 s, imports included;
  - kernel type checking: 6.3 s in total;
  - the largest: Compose 1.91 s, Hide 1.55 s, XSpec 0.78 s, StepE 0.57 s.

  No module got slower in a way that matters. These modules changed only in hypotheses.

## 6. For the orchestrator: moving the pin and the build trees

The old HEAD does not build at `6d05d00`, and INT-6's edits do not build at `15dac52`. So commit
the pin and INT-6's modules together, or one right after the other with nothing in between.

1. **Pin**:
   ```sh
   git -C .contract fetch origin pull/20/head    # or the v4/ivc-score branch; the commit is 6d05d00
   git -C .contract checkout 6d05d00
   git add .contract && git commit -m "pin: core 6d05d00 (PR #20 on #19)"
   ```
   `.contract/.lake/packages → logs/pkgs` stays as it is. The manifest is unchanged. The
   `.lake/build` of `.contract` was built at `15dac52`. If anything uses it, rebuild it with
   `lake build` in `.contract` under the scope, or use `logs/org20` instead.
2. **INT-6's commit**: the 18 modules in `logs/fr-build-INT6/MINE.txt`, plus `INT-6-JOURNAL.md`
   and `INT-6-RESULT.md`.
3. **Organiser copy**: `logs/org20` is ready (org-setup completed: allowlist, manifest, objects,
   service). Keep `logs/org` until S-T1-era trees are retired. Do not `mv` `org20` over `org`:
   Lake's `.lake/config` and org-setup's `.lake/rf` hold absolute paths.
4. **Build trees.** For every active tree (`logs/fr-build`, `logs/fr-build-orch`, and every new
   track tree), change `logs/org"` to `logs/org20"` in `gen.sh`/`snap.sh` and in
   `lake-manifest.json`, run `./gen.sh` or `./snap.sh`, then `lake build FR` (a full rebuild,
   since every module imports the contract):
   ```sh
   sed -i 's#logs/org"#logs/org20"#' gen.sh snap.sh lake-manifest.json
   ```
   The simplest way to get a new track tree is to copy `logs/fr-build-INT6`
   (`snap.sh`, `gen.sh`, `lake-manifest.json`, `lean-toolchain`). About 50 historical trees
   (`logs/S-*-review`, `fr-build-SG*`, …) still name `logs/org`. They are records; leave them.
5. **TRACK-RULES.md**:
   - "via `logs/org`" → `logs/org20`;
   - the source-rule command → `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`
     until `.contract` is re-pinned; after that, `.contract/scripts/…` again.
6. **Blueprint**: the status header can drop "until the re-pin commit". Changes 25 (a) should
   record `WBeyond` (§3) as a residual next to `hOut`, owned by S-H2n under B-15.

## 7. Open questions and requests

1. **`WBeyond`** (§3): is it to be closed by S-H2n through B-15's domain split (my
   recommendation: `InDom` ⊇ `π.size ≤ 8 * outCap`, the contract's `Computes` domain)?
2. A negative control for `WBeyond` needs a kernel term for an accepted proof of `2^64` or more
   bytes. Is the positive control (`wBeyond_of_decode`) enough for now?
3. **Prover (P2)**: `prover/main.rs:78` still rejects `|π| > proofCap`, and `prover/format.rs:13`
   cites `proofCap`. I did not touch them; they belong to P2's track.
4. `qV = 10,240` was kept (3.17). Revision 4.0's `qV = 36,000` belongs to S-0′, together with the
   new shapes.
