# F1 golf RESULT: `spartan-srom` (Lean), proofs and compiled verifier

Status: **wrapped up early** (orchestrator, after a rate-limit stop). Nothing was applied to the
worktree's `submissions/spartan-srom/lean/`: every change is in **`logs/golf-lean/golf.patch`**
(unified diff against commit `8111b71`, `git apply -p1` checks clean on the worktree), built and
checked in the private copy `logs/golf-lean/core` (`entry/` = the patched files; core `a5e4cff`
as in F1). The untouched F1 state is `logs/golf-lean/core-before` (sources from `git archive
8111b71`, F1's oleans and binaries; F1 binaries also kept in `logs/golf-lean/bin-before/`). Logs
below are under `logs/golf-lean/` (`G/`). The shared VM was loaded (load average 17–27) during
every measurement.

## 1. Checks

| Check | Result |
|---|---|
| Clean entry build (65 modules + challenge + `srom-run`, `badge-verify`, `srom-probe`), 8 cores | green (`G/build/build-golf-1.log`; full rebuild after the field change 3 min 24 s, `G/build/build-mul-1.log`) |
| `#print axioms SpartanSrom.certificate`, `RecursionFast.Challenge.certified` | unchanged: `[propext, Classical.choice, Quot.sound]` (`G/axioms-print-after.log`) |
| Axiom audit of every entry declaration (F1's `EntryAxioms`) | PASS (`G/axioms-audit-after.log`) |
| Statements | `G/stmt/StmtDump.lean` dumps every non-internal constant of the entry (type hash, pretty type) in both trees (`G/stmt/before.tsv`, `after.tsv`): **no type changed** except the auto-generated `V.eq_1`/`V.eq_def` (they spell `V`'s body, now `decodeFront π`; `V_tag` is unchanged and proved via `decodeFront_eq`); nothing removed; added only `F.clmul32`, `F.mul_eq_mulLoop`, `OProg.AtMost.ite_of`, `bundleOK_iff`, `decodeWit_append`, `decodeF_of_prefix`, `decodePre(_eq)`, `decodeFront(_eq)`. Only def value changed: `F.mul`. No private helper removed (only added). No new `decide +kernel`, `native_decide`, `interval_cases`, `sorry` |
| Runner verdicts on every file of `logs/lean/run/` (`t16/`, `neg/`, raw `kat-*.bin`, wrong statement/key cases; `srom-run` and the badge) | identical, 24 cases (`G/verdicts-before.txt` vs `G/verdicts-final.txt`, script `G/verdicts.sh`) |
| Prover KATs (`srom-run prove-leaf-kat`, n = 16, three starts) | byte-identical to `kat-n16.bin`, `kat-v3s-n16.bin`, `kat-ab-n16.bin` |

## 2. Compiled verifier (badge `accF`, what `T_V` measures)

Profiled with `gprofng` (perf is not permitted on this VM; `G/prof/`): **64 % of the badge's time
was `F.mulLoop`**, the 64-step shift-and-add `GF(2^64)` product (Ligero's `dotE` 48 %, Spartan's
`EF.mul` 47 %), then `decodeF` of the whole bundle (packing `T`, ~10 %).

| Change | Where | Equality kept by |
|---|---|---|
| **V1. `F.mul` = Karatsuba over 32-bit halves, each half product `clmul32`**: 16 integer multiplications of the operands split into the 4 classes of bit positions mod 4 (column sums ≤ 8 never carry into the next position of a class), then v3's `reduce`. 25 ns vs 85 ns per product (`golfbench`) | `FieldBase` (`clmul32`, `mul`; `mulLoop` kept as reference), `FieldBaseCorrect` (+343 lines: `P_clmul32` via `testBit_eval_two_sparse`/`testBit_mul_holes`, new `Q_mul`) | `Q_mul` re-proved, so `toBF64_mul` and everything downstream unchanged; **`mul_eq_mulLoop : a * b = ⟨mulLoop 16 a.val b.val 0 0 0⟩`** (v3's product). The kernel controls of `FieldControls` now evaluate the new product |
| **V2. `V` decodes the node from a prefix**: `decodeFront π` = `decodeF` of the first 16 KB, then 64 KB, … (fuel 8), else all of `π`; a bundle no longer packs `T` | `Decode` (`decodeWit_append`: the readers are prefix-stable; `decodeF_of_prefix`, `decodePre`, `decodeFront`), `Node.V` | `decodeFront_eq : decodeFront π = decodeF π` |
| **V3. `@[inline] bundleProg`**: the compiled `V` encodes the node once (CSE) instead of twice | `Node` | attribute only (not a code-changing attribute of the hard rules; v3 already uses `@[inline]`) |

Badge `NS` (parse + `accF`), one core, ABAB × 3 (`G/verify-abab.log`):

| File | before (F1) | after |
|---|---|---|
| `L` leaf n = 16 | 214 / 210 / 204 ms | 91 / 96 / 136 ms |
| `B` bundle of 2 leaves | 456 / 503 / 480 ms | 207 / 203 / 193 ms |
| `C` clear leaf | 0.3 ms | 0.3 ms |

`L` −55 %, `B` −58 %. After the change (`G/prof/b2.er`): `F.mul` 42 %, Spartan `chainMats` (R1CS
MLE evaluation through `walkAB`/`GOps.compressW`, `Finset` sums compiled through `Multiset`) 31 %,
Ligero `colCheck` 27 %, transcript `squeezeIdx`/`natLE` 6 %, decode 3 %. Proposed next (not done;
carried modules, proof cost): `chainMats` without `Finset`/`Multiset` in compiled code; fewer
`reduce`s in `EF.mul`/`dotE` (accumulate 128-bit products); `natLE` without `Nat` bignums.

## 3. Proof golf

| # | Change | Effect |
|---|---|---|
| G1 | `NodeControls.clearTree_size`: the size computed for every signature with the right counts, then instantiated with `σ0 sk` | kernel check 3.6–4.8 s → < 0.1 s (the kernel was evaluating `σ0 sk`, a BLAKE2s signature, inside casts) |
| G2 | `VerifierTop.take8_encode`: `List.take_left' (wordBytes_length _)` instead of `simp [… wordBytes]` | 4.2 s → 0.1 s |
| G3 | `Node.atMost_V`: `AtMost.ite`/new `AtMost.ite_of` instead of `split_ifs` (a case split on an `AtMost` goal makes `whnf` evaluate `leafHeaderOK`/`leafN`) | 4.1 s → ~2 s, −6 lines |
| G4 | `Node.bundleOK_iff` (new): the static checks as propositions; used by `atMost_V`, `V_final`, `fits_of_bundleOK`, `bundle_static`, the four `bundleOK_*` negatives (now one-line terms) and `canary_B_push/pop` | one `Decidable (∀ x ∈ ls, …)` synthesis (0.4 s each) instead of seven; −24 lines in `NodeControls` |
| G5 | `Node.clear_acc`: `by_cases`+`ite_eq_left/right` and targeted `split`s instead of `split_ifs at hcl`; shared slot conjuncts | 2.6 s → ~2 s |
| G6 | `clearLeaves_slot` (`ite_eq_right`), `runBundle_final`/`atMost_runBundle` (`bundleBytes`/`bundleQ` cons by `rfl`), `decode_leaf` (`h8` by `rw`+`omega`), `canary_B_pop` (`h32` nil case) | small |

Per-module `lake env lean` check, one core, **CPU seconds** (user+sys; wall is noisier), ABAB × 3
(`G/time/cpu-before.tsv`, `cpu-after.tsv`; import ≈ 5–6 s of each):

| Module | lines before → after | CPU s before (3 runs) | CPU s after |
|---|---|---|---|
| `Node` | 411 → 410 | 8.3 / 8.5 / 9.0 | 7.6 / 8.7 / 9.7 |
| `NodeControls` | 603 → 579 | 11.9 / 12.0 / 13.2 | 10.0 / 10.5 / 11.5 |
| `Queries` | 97 → 104 (`AtMost.ite_of`) | 5.7 / 5.7 / 5.9 | 5.5 / 5.5 / 6.2 |
| `SnarkQueries` | 128 → 128 | 7.3 / 7.6 / 7.7 | 7.6 / 7.6 / 9.3 |
| `Decode` | 111 → 221 (V2) | 5.8 / 6.0 / 6.7 | 6.5 / 6.6 / 8.6 |
| `VerifierTop` | 306 → 307 | 8.8 / 9.4 / 9.8 | 8.0 / 8.8 / 9.8 |
| `Submission` | 239 → 239 | 6.1 / 6.3 / 6.6 | 6.1 / 6.4 / 7.6 |
| `SoundnessKSFinal` | 66 → 66 | 6.6 / 6.8 / 6.9 | 6.3 / 6.5 / 7.5 |
| `SoundnessKState` | 54 → 54 | 6.7 / 6.7 / 7.4 | 6.3 / 7.2 / 7.6 |
| `Final` | 57 → 57 | 6.6 / 6.7 / 7.7 | 6.2 / 7.0 / 7.6 |
| `FieldBase` | 172 → 203 (V1) | 7.0 / 7.2 / 7.9 | 6.9 / 7.9 / 8.1 |
| `FieldBaseCorrect` | 715 → 1058 (V1) | 30.4 / 30.6 / 35.8 | 39.7 / 40.8 / 44.4 |

Honest reading: the golf gains are real per declaration (trace profiler, `G/time/tprof-*.txt`)
but within the noise at module level except `NodeControls` (−1.5 s); `FieldBaseCorrect` pays
+10 s for V1's proof. Not reached (stopped early): `Submission`, `SnarkQueries`, `KSFinal`,
`KState`, `Final` were left as they were (already short); `zeroLeaf_parse` (§4).
Cosmetic follow-up: some new lines in `FieldBaseCorrect` exceed 100 characters.

## 4. The 45 carried `decide +kernel` (size = characters of the decided statement, pretty-printed)

All are v3's, unchanged; none added. The only slow one measured: `VerifierTop.zeroLeaf_parse`,
3–4 s (an 80-byte proof's header through `byteAt`); `⟨rfl, rfl, rfl, rfl, rfl⟩` was 3.4 s and
per-conjunct `rfl` did not finish in minutes, so it stays. The `FieldControls` products now
evaluate V1's `mul` in the kernel (module 7.4 s in the build). `TranscriptControls` (KATs
evaluating BLAKE2s) is the slowest module of the entry (75–144 s in builds, load-dependent).

| module | line | declaration | decided statement (chars, pretty-printed) | statement (start) |
|---|---|---|---|---|
| Blake2sR1CS | 468 | `chainStep_zero_kat` | 202 | `RecursionFast.chainStep (Vector.replicate 32 0) =   #v[149, 74, 194, 164, 214, 167, 144, 3` |
| Controls | 159 | `y_ne_zero` | 20 | `SpartanSrom.EF.y ≠ 0` |
| Controls | 160 | `y_ne_one` | 20 | `SpartanSrom.EF.y ≠ 1` |
| FieldBaseCorrect | 603 | `mask32` | private | `(private)` |
| FieldBaseCorrect | 614 | `mask16` | private | `(private)` |
| FieldBaseCorrect | 641 | `mask8` | private | `(private)` |
| FieldBaseCorrect | 668 | `mask4` | private | `(private)` |
| FieldBaseCorrect | 695 | `mask2` | private | `(private)` |
| FieldBaseCorrect | 722 | `mask1` | private | `(private)` |
| FieldBaseCorrect | 990 | `conj_distinct` | 67 | `(List.map (fun k => SpartanSrom.F.x ^ 2 ^ k) (List.range 64)).Nodup` |
| FieldControls | 18 | `mul_x_x` | 42 | `{ val := 2 } * { val := 2 } = { val := 4 }` |
| FieldControls | 21 | `mul_x_x_ne` | 42 | `{ val := 2 } * { val := 2 } ≠ { val := 3 }` |
| FieldControls | 24 | `mul_wraps` | 61 | `{ val := 9223372036854775808 } * { val := 2 } = { val := 27 }` |
| FieldControls | 27 | `mul_wraps_ne` | 62 | `{ val := 9223372036854775808 } * { val := 2 } ≠ { val := 135 }` |
| FieldControls | 30 | `sq_top` | 99 | `{ val := 9223372036854775808 }.sq = { val := 9223372036854775808 } * { val := 922337203685` |
| FieldControls | 33 | `mul_inv_x` | 33 | `{ val := 2 } * { val := 2 }⁻¹ = 1` |
| FieldControls | 36 | `inv_x_ne` | 29 | `{ val := 2 }⁻¹ ≠ { val := 2 }` |
| FieldControls | 39 | `y_cube` | 127 | `{ c₀ := 0, c₁ := 1, c₂ := 0 } * { c₀ := 0, c₁ := 1, c₂ := 0 } * { c₀ := 0, c₁ := 1, c₂ := ` |
| FieldControls | 42 | `y_cube_ne` | 127 | `{ c₀ := 0, c₁ := 1, c₂ := 0 } * { c₀ := 0, c₁ := 1, c₂ := 0 } * { c₀ := 0, c₁ := 1, c₂ := ` |
| FieldControls | 45 | `mul_inv_y` | 67 | `{ c₀ := 0, c₁ := 1, c₂ := 0 } * { c₀ := 0, c₁ := 1, c₂ := 0 }⁻¹ = 1` |
| FieldControls | 49 | `toBytes_le` | 71 | `{ val := 578437695752307201 }.toBytes.toList = [1, 2, 3, 4, 5, 6, 7, 8]` |
| FieldControls | 53 | `toBytes_not_be` | 71 | `{ val := 578437695752307201 }.toBytes.toList ≠ [8, 7, 6, 5, 4, 3, 2, 1]` |
| FieldExtCorrect | 416 | `frob_three_y` | 57 | `SpartanSrom.EF.frob 3 SpartanSrom.EF.y = SpartanSrom.EF.y` |
| FieldExtCorrect | 448 | `ybasis` | 309 | `∀ k < 64,   !![SpartanSrom.EF.c₀ 1, (SpartanSrom.EF.y ^ 2 ^ k).c₀, (SpartanSrom.EF.y ^ 2 ^` |
| MLEControls | 55 | `sumcheck_pos` | 234 | `SpartanSrom.verifyRounds SpartanSrom.prodExpr.deg 0     ((SpartanSrom.honest SpartanSrom.p` |
| MLEControls | 102 | `weightEval_pos` | 112 | `SpartanSrom.weightEval [1, 1] [1, 0] [0, 1] = SpartanSrom.mleEval (SpartanSrom.weightTable` |
| RSControls | 55 | `encAt_toy` | 193 | `∀ (c : Fin 7),   SpartanSrom.RS.encAt SpartanSrom.RS.Controls.κ7 2 #[1, 2, 3, 4] (SpartanS` |
| SoundnessLogControls | 85 | `shape0_length` | 47 | `(SpartanSrom.SoundnessLog.shape 0).length = 117` |
| SoundnessLogControls | 90 | `shape0_zero` | 74 | `(SpartanSrom.SoundnessLog.shape 0)[0] = SpartanSrom.SoundnessLog.Step.seed` |
| SoundnessLogControls | 93 | `shape0_last` | 79 | `(SpartanSrom.SoundnessLog.shape 0)[116] = SpartanSrom.SoundnessLog.Step.squeeze` |
| SoundnessLogControls | 98 | `shape0_tail` | 101 | `((SpartanSrom.SoundnessLog.shape 0).tail.all fun x => x != SpartanSrom.SoundnessLog.Step.s` |
| TranscriptControls | 64 | `kat_transcript` | 212 | `RecursionFast.OProg.run SpartanSrom.katOracle     (SpartanSrom.TranscriptControls.katProg ` |
| TranscriptControls | 69 | `kat_transcript_root_ne` | 198 | `(RecursionFast.OProg.run SpartanSrom.katOracle       (SpartanSrom.TranscriptControls.katPr` |
| TranscriptControls | 74 | `kat_chE` | 187 | `SpartanSrom.Transcript.chE SpartanSrom.TranscriptControls.katSt2 =   { c₀ := { val := 1494` |
| TranscriptControls | 78 | `kat_indices` | 92 | `SpartanSrom.Transcript.indices 10 3 [SpartanSrom.TranscriptControls.katSt3] = [31, 811, 33` |
| TranscriptControls | 83 | `chE_not_be` | 187 | `SpartanSrom.Transcript.chE SpartanSrom.TranscriptControls.katSt2 ≠   { c₀ := { val := 7947` |
| TranscriptControls | 97 | `kat_merkle_root` | 241 | `SpartanSrom.Merkle.root     (RecursionFast.OProg.run SpartanSrom.katOracle       (SpartanS` |
| TranscriptControls | 102 | `kat_verify` | 384 | `RecursionFast.OProg.run SpartanSrom.katOracle     (SpartanSrom.Merkle.verify SpartanSrom.T` |
| TranscriptControls | 107 | `kat_verify_flip` | 392 | `RecursionFast.OProg.run SpartanSrom.katOracle     (SpartanSrom.Merkle.verify SpartanSrom.T` |
| TranscriptControls | 112 | `kat_verify_index` | 385 | `RecursionFast.OProg.run SpartanSrom.katOracle     (SpartanSrom.Merkle.verify SpartanSrom.T` |
| TranscriptControls | 132 | `colL_log4` | 192 | `List.map (SpartanSrom.Merkle.colL SpartanSrom.TranscriptControls.log4 8 SpartanSrom.Transc` |
| TranscriptControls | 139 | `colL_log4_missing` | 491 | `SpartanSrom.Merkle.colL       (List.filter (fun e => e.1 != SpartanSrom.leafQ SpartanSrom.` |
| TranscriptControls | 169 | `pathOf_linked` | 86 | `SpartanSrom.SoundnessLog.pathOf SpartanSrom.TranscriptControls.logLinked 2 = [0, 1, 2]` |
| TranscriptControls | 174 | `pathOf_orphan` | 299 | `SpartanSrom.SoundnessLog.pathOf     [(SpartanSrom.seedQ (SpartanSrom.TranscriptControls.dg` |
| VerifierTop | 302 | `zeroLeaf_parse` | 280 | `ByteArray.size SpartanSrom.zeroLeaf = 80 ∧   SpartanSrom.tagWord SpartanSrom.zeroLeaf = 0 ` |

45 uses

## 5. Conflicts with the review's fixes (`reviews/F1-lean-review.md`) and core `ea2e8ab`

* **F1-M2** (clear/bundled leaves capped at `n ≤ 2^12`; `tagWord`/`leafN` read in place):
  `bundleOK_iff` (G4) restates `bundleOK`'s conjuncts — if the cap changes in `bundleOK` or
  `clearLeafOK`, change the `x.2.2 ≤ chainCap` conjunct of `bundleOK_iff` the same way (its proof
  is one `simp only`); the four `bundleOK_*` negatives and `qbound_nine`'s context then follow.
  In-place `tagWord`/`leafN` touch `VerifierTop` near G2/G6 (`take8_encode`, `decode_leaf`'s
  `h8`, which reads `π.data.extract 40 48`) — re-prove `h8` against the new `leafN`.
* **`acc` gains `p.tr.length ≤ S.qV`** (ea2e8ab): `accWith` gets a conjunct; G5's `clear_acc`
  states the slot conjuncts once (`have hs`) — add the trace-length conjunct there (empty trace).
* **`wordBytes := enc64 w.toNat`** breaks `Decode` lines 47/50 (`wordBytes_ofLE`); the patch's
  `Decode` hunk is a new section further down (prefix decoding), so it should apply after that
  fix; G2 uses only `wordBytes_length`.
* V1 (`FieldBase`, `FieldBaseCorrect`) and V2's `Decode` lemmas are independent of the review.
  Apply order: review fixes first, then `golf.patch` (expect fuzz/rejects in `Node`,
  `NodeControls`, `VerifierTop` around the lines above), rebuild, re-run `G/verdicts.sh` and
  `G/stmt/StmtDump.lean`.
