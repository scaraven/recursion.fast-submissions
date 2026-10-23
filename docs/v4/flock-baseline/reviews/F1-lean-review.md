# F1 (Lean entry `spartan-srom`): adversarial review, 2026-10-23

Reviewed: commit `8111b71` on `v4/flock-baseline` (worktree `recursion.fast-submissions-v4`),
`submissions/spartan-srom/lean/*.lean` (65 modules) and `claim.json`; the claims of
`stages/F1-lean-RESULT.md` and `F1-lean-JOURNAL.md`; against `BLUEPRINT.md` §1–§6, the core at
`a5e4cff` (`Contract/*`, `Library/{WitnessSending,Words,Fast,Trace,Completeness,Signer}.lean`),
the harness (`recursion.fast-v4h`: `render-challenge.py`, `challenge/Challenge.lean.in`,
`badge/*.lean.in`, `evaluate.py`, `org-setup.sh`, `lean-tools/Gate.lean`,
`scripts/olean-manifest.py`, `rfh/{bench,checks}.py`) and the v3 source
(`logs/lean/v3src/submissions/spartan-chain`). Read-only except this file. Lean was run only in the
existing scratch (`logs/lean/core`, `lake env lean`, `taskset`, `timeout`) and in two private
copies of it under the session scratchpad (`core2`: the pending core diff applied; `core3`: a
timing probe executable); nothing was built in the shared package tree.

Method: the `adversarial-review` passes. Pass B (fidelity: the carried modules against v3, the
rendered challenge against `Solution.lean`) was run first and mechanically; pass A (does `V`
decide what BLUEPRINT §2 says, is every theorem of the certificate non-vacuous and as strong as
v3's) by reading `V`, `V_final`, `clear_acc`, `runBundle_final`, `fits_of_accV`, `complete`,
`certificateOf` against the contract's definitions before reading the RESULT's account of them;
pass C (hygiene, second-kernel risk) by scanning and by the logs. Severity: **major** = must fix
before the stage is accepted; **minor** = fix or answer; observations are marked.

## 0. Summary and verdict

The certificate says what it should: `SpartanSrom.certificate : Certificate submission` is closed,
its axioms are the three allowed (`logs/lean/axioms-print-a5.log`), `Solution.lean`'s `declared`
is byte-identical to what `render-challenge.py` produces from `claim.json` (§3.1), and the proof
`certified` is the generic `certificateR_of`. `V` decides exactly the branches of BLUEPRINT §2
(§3.1); the `final` law is sound and not weaker than v3's (§3.2); completeness at `δ = 0` is for
every key and every witness of `Rel` (§3.3); the controls exercise the branches they name (§3.4);
47 modules are byte-identical to v3 after the rename, as claimed (§3.7).

Two majors, neither a defect in a proved statement:

* **F1-M1** The entry cannot pass the harness's certificate job as the harness is configured: its
  closure holds 28 CompPoly modules (one with `@[csimp]`), which the v4 allowlist does not cover,
  so gate rule 3 (or rule 6, if they are pinned) rejects. v3's interim tooling allowlisted and
  pinned CompPoly; v4's `org-setup.sh` roots do not. Fix on the harness side (`RF_ORG_ROOTS`),
  recorded in the RESULT.
* **F1-M2** The compiled `acc` is adversary-controllable by a factor of 150–400 over the honest
  root under the published key: `σ0` (a signature of the empty trace) is public in every bundle,
  and a 970 KB plain-node chain signed with it costs **68 s** (`n = 1` leaves) to **183 s**
  (`n = 2^20` leaves), measured, against 0.43 s for the honest root bundle. The chain-recomputation
  part has a trivial fix (cap `C` at `n ≤ 2^12`, the largest leaf that fits `proofCap`); the
  decode part needs a byte-level node reader (a library change the RESULT already asks for).

Minors: the journal's adaptation plan for the coming `acc` change is insufficient (the same core
diff redefines `wordBytes`; `SpartanSromDecode` fails to build against it, F1-m1); a stale
docstring (m2); statement-binding negatives missing for `C`, `N`, `B` (m3); an import outside the
allowlist (m4); the static query bound is unreachable within `proofCap` (m5, observation); the
comparator, gate and nanoda were not run (m6).

**Verdict: pass on the Lean content (certificate, verifier semantics, soundness, completeness,
controls, fidelity); blocked for the harness by F1-M1 until the organiser allowlists CompPoly;
F1-M2 to be fixed in the entry (the `C` cap, `tagWord`/`leafN` via `byteAt`) and raised to the
library (the decoder).**

## 1. Major findings

### F1-M1 The gate rejects the entry's CompPoly imports under the v4 allowlist

*Claim attacked.* RESULT §8.3 lists the gate as "not run here"; BLUEPRINT §5 requires the layout
of `harness/evaluate.py`, whose `cert` job runs the gate with `--allowed-imports` (step 4).

*Evidence.* `SpartanSromFieldBase.lean` and `SpartanSromFieldExtCorrect.lean` import
`CompPoly.Fields.Binary.BF64.{Ext3,Bytes}`; their import closure (computed over the package tree's
sources, `public import` included) is 28 CompPoly modules and contains
`CompPoly.Fields.Extension.Arithmetic`, which has `@[csimp] theorem mul_eq_mulTbl` (line 355).
`harness/org-setup.sh:20`: `ROOTS=${RF_ORG_ROOTS:-Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls}`;
no core module imports CompPoly (`grep -rl 'import CompPoly' recursion.fast-v4/RecursionFast`:
none), so the allowlist and, with `--closure`, the olean manifest exclude CompPoly
(`scripts/olean-manifest.py` header: "the modules of the trusted closure"). In `Gate.lean` a module
is then neither trusted nor pinned, i.e. untrusted (`GateCtx.untrusted`, line 380), and rule 3
rejects **any** untrusted module that registers `csimp` (lines 29–39, 415–442). If the organiser
instead pins CompPoly without allowlisting it, rule 6 rejects the import (line 445–450: an import
must be untrusted or allowed). v3 met the same wall and solved it by allowlisting and pinning
CompPoly ("its one `@[csimp]` lemma made the gate reject until CompPoly was pinned",
`docs/v3-lessons…` §6, CompPoly row). No v4 document records that decision (`grep CompPoly
recursion.fast-v4h/docs/v4/stages/B-harness-RESULT.md`: none; `.github/workflows/*.yml` call
`org-setup.sh` with no `RF_ORG_ROOTS`).

*Fix.* Harness: set `RF_ORG_ROOTS` (CI and the season file) to add the CompPoly roots the baseline
needs (`CompPoly.Fields.Binary.BF64.Ext3`, `CompPoly.Fields.Binary.BF64.Bytes`: 28 modules), so
they are allowlisted and manifest-pinned; then run `evaluate.py cert` once on the entry. Entry:
state the dependency in the RESULT (§7 is the place: "the entry needs CompPoly's `BF64`/`Ext3`
allowlisted and pinned, as in v3") so the organiser's job is explicit. Cost: one line of
configuration, one certificate run.

### F1-M2 `acc`'s cost under the published key is adversary-controlled (68–183 s per proof)

*Claim attacked.* RESULT §5 ("anything superlinear left after F1's `byteAt` fix") and §6.1.8
(the `C` recomputation, "about 0.3 s"); the contract's rationale for `chainCap` ("a verifier that
recomputes chains is not driven past its time cap by a proof declaring a huge length",
`Contract/Relation.lean`), and `acc` being "the check any third party runs later with the
published `vk`" (`Contract/Certificate.lean`).

*Evidence.* `bundleOK` accepts any `σ0` with `SigOk vk (traceDigest []) σ0`, and every published
bundle carries its `σ0` in the clear (slot 1's signature). Whoever has one bundle can therefore sign
every empty-trace slot. Probe (`core3/entrymain/SromAttack.lean`, built against the unchanged
entry; `σ0` and `vk` read from the test material `logs/lean/run/t16/{B.bin,vk.hex}`; one core,
`taskset -c 4`, the same core and machine load as the honest numbers below;
`scratchpad/attack-run.log`):

| proof | bytes | `acc` | `acc` result |
|---|---|---|---|
| honest `B` (two `n = 16` leaves, `srom-run verify`) | 297,078 | **0.43 s** | accept |
| honest `L` (`n = 16`) | 143,711 | 0.19 s | accept |
| one `C` leaf, `n = 2^20`, trace `[]`, `σ0` | 48 | **0.79 s** | accept |
| plain-node chain, depth 20, `C` leaves `n = 2^20` | 194,128 | 27.2 s | accept |
| plain-node chain, depth 100, `C` leaves **`n = 1`** | 970,448 | **68.5 s** | accept |
| plain-node chain, depth 100, `C` leaves `n = 2^20` | 970,448 | **183 s** | accept |

Two causes. (i) The `N` branch re-decodes each child's bytes from scratch at every level
(`V` → `decodeF p₁.π` = `packFast π.data.toList`, 0.2 µs/byte, plus `tagWord π`, which copies
the whole array through `π.data.extract`, and the canonical `encodeF w = π` comparison): a chain
of depth `d` costs `Σ` of the sizes of the nested proofs, about `d · |π| / 2`; at 100 levels
within `proofCap` that is 68 s with no chain recomputed at all. (ii) `C` recomputes up to
`chainCap = 2^20` compressions per clear leaf (0.79 s each here), and a chain of plain nodes
multiplies it by the number of leaves. Neither is exercised by the harness's DoS column
(`rfh/checks.py:131`, random bytes and bit flips of the root: no valid signature reaches `V`),
so the score is unaffected; the exposure is the published `acc`.

*Why nested plain nodes cannot simply be refused.* The bundle's extracted witness is its clear
tree, and `clear_acc` needs every slot accepted by `acc`, i.e. by the `N` branch recursively; the
clear tree of a `2^r`-leaf root has depth `r`. (ii) however can be bounded without loss:
`leafSize 4096 = 796,111 ≤ 2^20 < leafSize 8192 = 1,062,591` (`#eval`, scratch), so no leaf with
`n > 2^12` can be an accepted `L` proof or a bundled SNARK; capping `C` (and `bundleOK`'s per-leaf
range) at `n ≤ 2^12` loses no `acc`-acceptable proof, keeps `P` complete (leaves go through `L`),
and bounds one recomputation at 4,096 compressions (about 1 ms).

*Fix.* Entry, now: `clearLeafOK`: `leafN π ≤ 2 ^ 12` (a named constant with a docstring) and the
same bound in `bundleOK`; `tagWord` and `leafN` through `byteAt` (the journal says `split_ifs`
timed out on that change at `whnf`; a `tagWord_eq`-style bridge lemma proved once avoids it);
re-prove `clear_acc`/`V_final` with the new bound (the `GoodLeaf` hypothesis gains `n ≤ 2^12`) and
amend BLUEPRINT §2 branches 2 and 4. Library (RESULT §7.4, to raise): a node reader over
`ByteArray` that reads the witness without `toList`/`packFast` of the whole proof, so a level
costs tens of nanoseconds per byte; with it the depth-100 chain costs about 0.5 s. Record the
residual `O(|π| · depth)` of `acc`-style recursion in the blueprint. Cost: a day for the entry's
part; the reader is a library stage.

## 2. Minor findings

### F1-m1 The adaptation plan for the pending `acc` change is insufficient

*Claim.* Journal, last entries: the pending core change is "`Submission.acc` gains `p.tr.length ≤
S.qV`"; adaptation: `accWith`, `accV_eq_acc` with `S.qV = 2^16`, `clear_acc`, `clearSlot_acc`,
`clearTree_acc`, `fits_of_accV`.

*Evidence.* The uncommitted diff in `recursion.fast-v4` (`git diff -- RecursionFast`, 227 lines,
saved as `scratchpad/pending-core.patch`) also redefines `Contract/Extractor.lean`'s `wordBytes`
as `enc64 w.toNat` (it was `List.ofFn …`), changes `Oracle.lean`'s `Log` to `abbrev Log := Trace`
and reproves `Words.lean`'s `wordBytes_length`/`ofLE_wordBytes`. Applied to a copy of the scratch
core (`core2`), `lake build SpartanSromSubmission` fails in the first entry module that touches
it (`scratchpad/q8-build.log`):

```
error: entry/SpartanSromDecode.lean:47:22: omega could not prove the goal   (wordBytes_ofLE)
error: entry/SpartanSromDecode.lean:50:6: Tactic `rewrite` failed: Did not find … Nat.toUInt8 ?x
```

`wordBytes_ofLE` unfolds `wordBytes` to `List.ofFn` (`simp only [wordBytes, List.getElem_ofFn,
toNat_toWord hlt]`); `take8_encode` (`VerifierTop`) and the modules after `Decode` were not
reached. *Fix.* Add to the plan: `wordBytes_ofLE` through `enc64` (`ofLE_enc64`, `enc64_length`,
or restate it as `enc64 (ofLE p) = p ++ replicate …`), check `take8_encode`, then the planned
`acc` items; rebuild the chain `Decode → VerifierTop → Node → Submission → NodeControls`. Cost:
an hour, once the change lands.

### F1-m2 Stale names in `SpartanSromNodeControls`'s module docstring

Lines 21–22 name `bundle_T_plus`, `bundle_T_minus`; no such theorems exist (`grep`: only the
docstring). The `|T| ± 1` negatives are `canary_B_push`/`canary_B_pop` (via `bundleOK_size`).
*Fix.* Rename in the docstring.

### F1-m3 No Lean negative for statement binding on `C`, `N`, `B` and the bundled leaf

v3 had `check_stmt_unique` and node canaries "under every statement"; v4 keeps
`zeroLeaf_other_stmt` for `L` only (RESULT §6.2 says the node ones moved to `NodeControls`; they
did not as statement negatives). The load-bearing checks `c = leafStmtF …` in `clearLeafOK`,
`c = nodeStmtF c₁ c₂` in `V`'s `N` branch and in `bundleOK`, and the per-leaf
`c = leafStmtF (digestFrom T o) n` in `runBundle` (without it `runBundle_final` could not conclude
`GoodLeaf` for the slot's statement) have only the compiled negatives (`neg.log`: "B under
L1.stmt", "C1 under L2.stmt"). *Fix.* Four one-line theorems: `c ≠ leafStmt (chainEnd (leafS π)
(leafN π)) (leafN π) → clearLeafOK c π = false`; `c ≠ nodeStmt c₁ c₂ → V … (encode (.node …)) =
.ret false` (via `V_tag`); the same for `bundleOK`; `c ≠ leafStmtF (digestFrom T o) n →
runBundle T ((c, s, n) :: ls) o = .ret false`. Cost: half an hour.

### F1-m4 `Batteries.Data.BitVec.Lemmas` is outside the allowlist

`SpartanSromBlake2sWords.lean` imports it; no Mathlib module does (`grep -rl 'import
Batteries.Data.BitVec' pkgs/mathlib/Mathlib`: none), so it is outside the closure of the default
roots and, like CompPoly, classified untrusted by the gate; it passes rules 6 and 6t only because
untrusted-imports-untrusted is allowed and it registers no code attribute. Fragile; *fix*: either
add it to `RF_ORG_ROOTS` with CompPoly (F1-M1) or replace the import by the Mathlib module that
provides the lemmas used.

### F1-m5 (observation) The static `Σ qBound ≤ 2^16` check is unreachable within `proofCap`

The cheapest query per byte is a bundled `n = 1` leaf: `leafSize 1 − 48 = 95,671` bytes of `T`
for `qBound 0 = 2,977` queries, so a bundle within `proofCap` carries at most 10 such leaves and
`Σ qBound ≤ 29,770` (`#eval`, scratch); `qbound_nine`'s nine `n = 2^20` leaves need 96 MB of
`T`. The check is still necessary: `KS`'s bound is over every input, not only those under
`proofCap`, and `V` does not know `proofCap`. Nothing to fix; the RESULT's "reachable within
`chainCap`" is accurate and could add "not within `proofCap`". (`qV` could be declared `2^15` =
32,768 with 10 % margin; not worth the change.)

### F1-m6 Comparator, gate and nanoda not run; second-kernel risk assessed low

RESULT §8.3. The comparator's acceptance of `Solution.lean` is expected (v3's pattern: the stub's
`declared` verbatim, one import added, `submission` and `certified` the only changed bodies;
checked by `diff` against the render, §3.1). Second kernel: the 47 byte-identical modules were
accepted by nanoda in v3 at 1f59b38 (70 s, 2.4 GB after the §4.5 fix, lessons §3); the remaining
`interval_cases` are 8-, 32- and 3-way over symbolic terms (`BlakeR1CS.lean:64,87`,
`FieldExtCorrect.lean:448`); the 45 `decide +kernel` are v3's (`TranscriptControls` 13, the
slowest module, 75 s in Lean); the new modules add `decide` on `2^16 < 9 · 7774` and on
`qVR1 ≤ 65536` only. *Fix.* Run `evaluate.py cert --nanoda` once F1-M1 is configured; nothing
to change in the entry.

## 3. The attack questions

### 3.1 Does the certificate say what it should? (pass A and B)

* **`declared`.** `python3 -I render-challenge.py Challenge.lean.in claim.json OUT; diff OUT
  Solution.lean`: the differences are the header comment, `import SpartanSromFinal`, and the two
  bodies; lines 12–22 (`declared`) are identical. `claim.json`'s `error` is `1/2^129` written out
  (`#eval (2:ℕ)^129` matches), `qV = 65536 = qVR1`, fuel `0 + 8 t`.
* **`certified`** is `certificateR_of facts declared εR1_le_declared (qVR1 ≤ 65536) (fuel)`, i.e.
  `CertificateR.bounds` with `S.ε = εR1 ≤ 2^-129` (`εR1_eq`, proved, the cast of `1/2^129 : ℚ≥0`
  is `2⁻¹^129` in `ℝ≥0`: the computable form changes no statement), `S.δ = 0`, `S.qV = 2^16`,
  `S.fuel = 8 t`. The `Submission` value is `submissionOf leafVerifier proveLeafR1` with
  `V := V leafVerifier`, `E := WitnessSending.E`, `ext`, `fuel` the library's.
* **`V` against BLUEPRINT §2, branch by branch** (`SpartanSromNode.lean:127–142`): `|π| < 8`
  rejects; tag `0` and `|π| = 48` is `C` (`leafN ≤ chainCap` first, then
  `leafStmtF (chainEndF s n) n`); tag `0` otherwise is v3's `leafProg` (the `|π| < 48` case is
  rejected by its exact-size check, RESULT deviation 1: same accepted set); tag `≠ 0`: `decodeF`,
  canonical ⇒ `N` = `c = nodeStmt ∧ accWith p₁ ∧ accWith p₂` with `accWith` the contract's `acc`
  at `a5e4cff` conjunct for conjunct (`accV_eq_acc`, `rfl`-level); not canonical ⇒ `B`:
  strict prefix, both slots clear trees under `p₁.σ` (`clearLeaves`: empty trace, `σ = σ0`,
  `|π| ≤ proofCap`, 48-byte tag-0 leaf or canonical node with `c = nodeStmtF d₁ d₂`, recursive),
  `bundleOK` (`1 ≤ n ≤ chainCap` each, `|T|` exact, `Σ qb ≤ 2^16`, `c = nodeStmtF c₁ c₂`,
  `SigOkF vk (traceDigestF []) σ0` once), then `runBundle` (per leaf `c = leafStmtF h n`, the
  SNARK on `T.extract`). Every item of §2.4 is present; the order differs (deviation 2) with the
  same accepted set. No branch accepts more than the specification; the specification itself
  is sound for the relation (§3.2). `SigOk` on `σ0` is evaluated once (`bundleOK`), and the
  slots' `SigOkF` inside `accV` are never evaluated by `B` (only `clear_acc` proves them).
* **Comparator setup.** `Solution.lean` defines nothing beyond the stub's three constants; the
  other 64 modules are separate modules. The gate's rule 6 accepts `import SpartanSromFinal`
  (own module); see F1-M1/m4 for the external imports.

### 3.2 Soundness

* **`final` for `B`** (`V_final`, `runBundle_final`, `clear_acc`): an accepted bundle on the log
  gives, per bundled leaf in order, `(LV.prog s n h πS).runLog L = some true` with
  `|πS| = leafSize n − 80` (from `|T|` exact and `size_extract`) and `c_slot = leafStmt h n`;
  `snark_final hμ` (v3's `runLog_chain` + `chainEnd_of_runChain` under `¬Bad`, `¬Esc` from
  `μ L < 1`) gives `chainEnd s n = h`, so `GoodLeaf`; `clear_acc` (strong induction on the slot's
  proof size) shows each clear slot is accepted by `accV`: empty trace, the checked `σ0`,
  `V_clear`'s recomputation equals `GoodLeaf`, or `V_tag`'s `N` branch with both children by
  the hypothesis. The extracted witness is `decode π = some W` by `decodeF_eq`. **Several SNARKs
  in one run cost no extra error:** `snark_final` is a statement about the log alone (for all
  `s n h πS`), as v3's `mu_final_leaf_closed` was; `μ` does not mention `V`, and `step` is
  unchanged (`mu_step_chain`). Checked: no hidden hypothesis; `L.length ≤ logCap` unused.
* **`N`, `C`, `L`:** by definition (`N` with `accV_eq_acc`), `decode_leaf` + `clearLeafOK`, and
  v3's `leafProg_final` (identical statement to `final_of_leaf` with `V` replaced by `leafProg`).
* **Not weakened relative to v3:** `final_law vk` is v3's `final_law` with `Rel (vb LV)` →
  `Rel (accV LV vk)` and `V LV` → `V LV vk` (the contract's new shape); `kstate vk` uses v3's
  `μ`, `mu_empty`, `mu_step_chain`; `ks vk` has `qV = 2^16` instead of `2^14` (the bundle).
* **`AtMost` and `LeafVerifier.qb`:** `AtMost n p` is the right notion for traces (`runSeq_length`
  needs no functionality of the trace); `atMost_snarkProg` re-derives v3's `qBound` component
  by component; `atMost_V` covers the four branches (the `B` bound by `bundleOK`'s static sum,
  `L` by `qb ≤ 2^16`). At `a5e4cff` it is **necessary** (node completeness needs
  `p.tr.length < 2^64` for `decode_encode`, and `KS`'s `queries H` bound does not give it on a
  non-functional trace); after the pending `acc` change it remains the simplest route to `KS`'s
  oracle-function bound for the bundle (otherwise `queries_bind` sums as in v3).

### 3.3 Completeness

`complete F vk : Complete (Rel (acc vk)) (P vk) (V vk)` for every oracle function, every key:
leaves as v3 (`leafBytes_parse`, `F.leaf_complete`, `n = 0` by the header); nodes: `P` returns
`encodeF w`, `V_encode_node` needs `w.Fits`, obtained by `fits_of_accV` from `acc` (proof cap,
query cap, `SigOk`'s counts) and `AtMost (2^16)` (trace length) — this covers children that are
bundles, plain nodes or leaves with traces up to the bound. `V` does not check `proofCap` on its
own input, so a node witness whose encoding is over `proofCap` is still accepted (D-5). `δ = 0`
through `complete_withError_zero`. No gap found.

### 3.4 Controls (`SpartanSromNodeControls`)

Each negative fails the conjunct it names, in a general theorem on the function that checks it
(`clearLeaves_trace/sig` on the slot guard, `bundleOK_size/qbound/zero/cap` on `bundleOK`,
`clearLeafOK_cap` on `C`), lifted to `V … = .ret false` by `V_bundle_reject`; none is rejected
for an unrelated reason. Positives: `clearSlot_acc` (`C` through `accV`), `clearTree_rel`,
`clearTree_acc` (`N` through the entry's `submission.acc`, 9,752 bytes), `bundle_static`
(the whole static phase of `B` under `Signer.pk sk` with `σ0 = Signer.sign sk 0 (traceDigest [])`,
reducing `V` to the two SNARK runs), `zeroLeaf_accepted`, `zeroClear_accepted`: all symbolic,
through `Signer.sigOk_sign`, no hash evaluated. The bundle branch's *acceptance* (a `T` on which
`runBundle` returns `true`) is shown only by the compiled check (`verify-final.log`, `neg.log`:
19 rejections, 3 acceptances), as the `L` branch's was in v3. Gaps: F1-m3.

### 3.5 Second kernel and hygiene

No `sorry`, `native_decide`, `partial`, `unsafe`, `opaque`, code-changing attribute (`grep`);
`set_option` only linter and `exponentiation.threshold` (carried). 45 `decide +kernel`, all v3's;
`interval_cases`: 8-way (`R1CS:64`), 32-way with `rfl` on symbolic BLAKE2s words (`R1CS:87`),
3-way with `decide +kernel` over `EF` (`FieldExtCorrect:448`); `fin_cases` 5 (carried). The
64-way `spread_getLsbD` of lessons §4.5 is the structural version (`FieldBaseCorrect:406`). New
modules: no `decide +kernel`, no `interval_cases`; lines ≤ 100 (two carried lines in `Oracle`
exceed it). Every new definition has a docstring saying what it means. Build 1 m 38 s at 8 cores
(`build-a5-1.log`); axiom audit PASS, 3,508 declarations (`axioms-a5.log`). See F1-m6.

### 3.6 The compiled verifier

F1-M2 (measured). The `B` numbers of RESULT §5 reproduce on this core (0.43 s). `decodeF`'s
60 ms packing of `T` stands (RESULT §7.4). The `ε` cast changes no statement (§3.1).

### 3.7 Fidelity to v3 and provenance

`for f in SpartanSrom*.lean: sed s/SpartanChain/SpartanSrom/ v3/$f | diff - $f` (first-line
header stripped): **47 SAME**, 4 NEW (`Node`, `NodeControls`, `Queries`, `SnarkQueries`), 13
DIFF (`VerifierTop` 461 diff lines, `Decode` 383, `Submission` 239, `Run` 117, `SpartanSrom`
100, `KSFinal` 74, `KState` 59, `TranscriptControls` 29, `Final` 25, `Oracle` 21, `Controls` 19,
`Verifier` 14, `Kat` 6) — exactly the RESULT's table. The small diffs are what the RESULT says
(`katOracle`, the contract's `OProg.bind`, `qBound` moved above `leafVerifier` and `qb` added,
the claim negatives moved). Every carried module has the provenance header; the four new ones
and `Solution.lean` have none (correct). Soundness core (`SoundnessKS`, `SoundnessKSBase`,
`SoundnessChain`, `SoundnessFinal`, `SoundnessPCS`, `SoundnessLog`, `Proximity`, `RS`, `Ligero`,
`SpartanProtocol`): byte-identical.

### 3.8 The coming contract change

F1-m1: the plan's `acc` items are right (after the change `fits_of_accV` reads the trace bound from
`acc` and `V_encode_node` no longer needs `hq`), but the diff also changes `wordBytes`, which
breaks `SpartanSromDecode` first.

## 4. Disposition

| Id | Severity | Owner | Status |
|---|---|---|---|
| F1-M1 CompPoly outside the v4 allowlist | major | harness (`RF_ORG_ROOTS`), RESULT note | open |
| F1-M2 `acc` cost under `σ0`: `C` cap, byte-level `tagWord`/`leafN`, decoder | major | entry (cap, parsers), library (reader), blueprint §2 | open |
| F1-m1 adaptation plan misses `wordBytes` | minor | entry | open |
| F1-m2 stale docstring names | minor | entry | open |
| F1-m3 statement-binding negatives | minor | entry | open |
| F1-m4 Batteries import outside the allowlist | minor | entry or harness | open |
| F1-m5 static bound unreachable within `proofCap` | observation | RESULT wording | — |
| F1-m6 comparator/gate/nanoda not run | minor | orchestrator | open |
