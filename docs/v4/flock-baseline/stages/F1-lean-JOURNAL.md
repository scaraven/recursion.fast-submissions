# F1 (Lean port of `spartan-chain` to the v4 contract): running journal

Implementer's journal, newest entry last. A successor reads this first.

## Setup (2026-10-22)

- Scratch core: `logs/lean/core` (gitignored), a copy of the core worktree
  `/home/devops/Verified-zkEVM/recursion.fast-v4` (`RecursionFast/`, `RecursionFast.lean`,
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) taken **2026-10-22T18:41:23Z**
  (`logs/lean/core/SNAPSHOT_TIME`). Contract + library build green (45 s, `logs/lean/build-core-1.log`).
- Package tree: the shared `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` has
  **no build products** (its `mathlib/.lake` is empty since 2026-10-22 13:44), so the scratch uses
  a private copy of stage A's built tree: `logs/lean/pkgs` (`cp -a --reflink=auto` of
  `recursion.fast-v4/.lake/pkgs-local`; also required by the orchestrator for executable builds).
  `logs/lean/core/.lake/packages -> logs/lean/pkgs`. Checked up to date with `lake build --no-build`.
- Scratch lakefile adds `RFChallenge` (srcDir `challenge`, the rendered `Challenge.lean`) and
  `EntryScratch` (srcDir `entry` -> `submissions/spartan-srom/lean`, globs `SpartanSrom.+`,
  `Solution`). Builds run under `taskset -c 0-7` with `timeout`.
- Layout (orchestrator, stage B): Lean in `submissions/spartan-srom/lean/` (flat), `Solution.lean`
  defines `RecursionFast.Challenge.submission` / proves `certified`; `claim.json` written
  (ε = 1/2^129, δ = 0, qV = 65536, fuel 0 + 8 t). `LICENSE-leanerVM` at the entry root.
- v3 source: `logs/lean/v3src/submissions/spartan-chain` (`git archive 1f59b38`). Every file copied
  with `SpartanChain` -> `SpartanSrom` and a first-line provenance comment.

## Plan

1. `Oracle`: the contract now has `OProg.bind`; the entry's `Monad` uses it (entry `bind` removed);
   add the v3 test oracle `katOracle q = BLAKE2s-256(0x52 ‖ q)` for KATs (v3's `blake2sOracle`).
2. `VerifierTop`: keep the leaf part (parsing, `leafProg`, leaf lemmas); re-prove `decode_leaf`
   for v4's `decodeWit`; drop v3's node branch, `check`, `vb`. `Decode`: v3's codec is for the v3
   node format: replaced by the v4 format helpers.
3. New `Queries`: `AtMost n p` (at most `n` queries along every answer path). Needed because
   completeness must decode `encode w` back to `w` for every node witness of `Rel`, which needs
   every accepted child's trace length `< 2^64` (`Signed.Fits`); a trace accepted by `runSeq`
   has length bounded by `AtMost`, not by the oracle-function bound `queries H`.
4. New `Node`: the clear tree, the bundle program, `V vk c π` (branches L, C, N, B), unfoldings.
5. `Submission`: `P`, `submission`, completeness for every `vk`, `certificate`.
6. `SoundnessKSFinal` / `KState`: `final` per branch; KS for every `vk`.
7. Controls (§6), `Run` (runner functions), `Solution.lean`, runner exe in `logs/lean/core/entrymain`.

## Log
- 18:50 Copied + renamed; `claim.json`; scratch lakefile (roots listed explicitly: lake globs
  `Foo.+` mean submodules, so `scratchpad/roots.py` regenerates the roots list).
- 18:55 `Oracle` (Monad on the contract's `bind`, `katOracle`); all carried modules up to
  `SoundnessKS`, `ChainInner`, the field/MLE/RS/Ligero/PCS controls, `TranscriptControls` and `Kat`
  (with `katOracle`) build unchanged (`logs/lean/build-3.log`, 2 m 31 s wall at 8 cores).
- 19:20 `Decode` rewritten (v4 byte facts: `decode_append`, `IsStrictPrefix`, `DecidableEq Sig`);
  `VerifierTop` cut to the leaf branch (`decode_leaf` re-proved for v4's `decodeWit`,
  `leafProg_final`); `LeafVerifier.qb` added (`Verifier.leafVerifier`: `qBound (kap n)`).
  `SoundnessChain`, `Prover`, `ChainHonest` build.
- 19:40 New `Queries` (`AtMost`), `SnarkQueries` (`atMost_snarkProg`), `Node` (V with L/C/N/B,
  `accV_eq_acc`, `atMost_V`, `V_final`, `clear_acc`, `runBundle_final`, `fits_of_accV`,
  `V_encode_node`): all green. Next: `Submission`, `KSFinal`/`KState`, `Final`, `Solution`,
  controls, `Run`.
- 20:30 `Submission` (generic `submissionOf`, `certificateOf`, completeness for every key),
  `SoundnessKSFinal` (`snark_final`: v3's leaf argument per SNARK; `mu_final` = `V_final`),
  `SoundnessKState` (`kstate vk`, `ks vk`), `Final` (**`SpartanSrom.certificate : Certificate
  SpartanSrom.submission`**, closed), `Solution.lean` (rendered `declared` verbatim), controls
  (`NodeControls`: formats, signer positives, bundle negatives, canaries, claim), `Run`
  (`accRun`, `proveWith`, `parseSigned`). Whole entry green (`logs/lean/build-5.log`).
  Axiom audit of every entry declaration: PASS (`logs/lean/axioms-1.log`, adapted harness
  `AxiomAudit` in `logs/lean/core/entrymain/EntryAxioms.lean`). Source rule: 0 findings.
  Next: re-sync the core snapshot, clean build with time/RSS, runner exe + timings, RESULT.
- 2026-10-22 20:03 Re-synced the scratch core to **core `85f0985`** (`git archive`; only
  `Controls/Relation.lean` differed from the 19:23 snapshot). Clean entry build green:
  3 m 23 s wall, 826 s user, peak RSS 4.10 GB (`logs/lean/build-full-2.log`).
- 20:10 Compiled-runner findings, fixed: (a) v3's `digestFrom` read `π.data.getD`, and compiled
  code turns `π.data` into a boxed copy of the whole proof on every call: quadratic `parseSigned`
  (F2 saw 87.8 s / 579 s outside `acc`) and 64 copies of the leaf proof per leaf check; now
  `byteAt` (in-place `π[j]`), proved equal (`byteAt_eq`, `rfl`). `tagWord`/`leafN` kept as v3
  (one copy each; changing them made `split_ifs` time out at `whnf`). (b) `accWith` took the
  child's program eagerly, so a rejected parent still built its children's programs; it now takes
  `Unit → OProg Bool`.
- 2026-10-23 09:40 (session restarted; build-7 re-run green). Made the submission **computable**
  (`εR1 := ((1 / 2^129 : ℚ≥0) : ℝ≥0)`, `εR1_eq`), because stage B's badge compiles
  `S.accF` with `S := Challenge.submission`; a noncomputable submission fails to compile there.
  Stage B's badge template rendered with `Solution` builds (`logs/lean/core/badge/`, exe
  `badge-verify`) and accepts/rejects the test files (`logs/lean/run/verify-final.log`).
  Axiom audit PASS on 3,508 declarations (`logs/lean/axioms-2.log`). Next: RESULT.
- Pending core API change (orchestrator): `Submission.acc` gains `p.tr.length ≤ S.qV` after the
  size cap. Adaptation: add `decide (p.tr.length ≤ 2 ^ 16)` as `accWith`'s second conjunct, give
  `accV_eq_acc` the hypothesis `S.qV = 2 ^ 16`, and close the new conjunct in `clear_acc`,
  `clearSlot_acc`, `clearTree_acc` (empty traces) and `fits_of_accV` (it then gives the trace
  bound directly).
- 2026-10-23 10:05 RESULT written. Clean build (final tree, core `85f0985`): 2 m 38 s, 672 s user,
  4.12 GB (`logs/lean/build-full-3.log`). Re-synced the scratch to **core `a5e4cff`** (stage A
  review + golf): entry builds unchanged, axiom audit PASS, badge OK (`logs/lean/build-a5-1.log`).
  Remaining: only the announced `acc` change (see the entry above).
