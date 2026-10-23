# F1 RESULT: the Lean port of `spartan-chain` to the v4 contract (`submissions/spartan-srom/lean/`)

Status: **done, certified; fix pass applied (§9, 2026-10-23), final tree built against core
`81e1ebf`** (its `RecursionFast/` is identical to `ea2e8ab`'s, the contract fix pass). §1–§8 are
the record of the first version (`8111b71`, core `85f0985`/`a5e4cff`); §9 says what the review,
the golf, D-6 and the new core changed, and gives the current numbers. `SpartanSrom.certificate : Certificate SpartanSrom.submission` (module
`SpartanSromFinal`) is a closed theorem, kernel-checked, axioms `propext`, `Classical.choice`,
`Quot.sound`. `Solution.lean` proves the rendered challenge `RecursionFast.Challenge.certified :
CertificateR declared submission` from it. Built against **core `85f0985`** (`v4/srom-rules`, stage
A, re-synced with `git archive` at 2026-10-22T20:03Z; every measurement below), and rebuilt
**unchanged against `a5e4cff`** (stage A's review and golf, 2026-10-23): green, axiom audit PASS,
the badge accepts and rejects as before (`L/build-a5-1.log`, `L/axioms-a5.log`,
`L/run/badge-a5.log`); the scratch core is now at `a5e4cff`. The scratch core and every log are
under the worktree's `logs/lean/` (gitignored, written `L/` below). The implementer's journal is
`F1-lean-JOURNAL.md`. Every time below was measured on the shared 32-vCPU VM with other agents' load
(load average 2–18), builds pinned to 8 cores (`taskset -c 0-7`), checks to one core.

## 1. What was built

The 61 v3 modules, copied with `SpartanChain` → `SpartanSrom` and a first-line provenance comment
(ported from v3 `spartan-chain`, local `main` at `1f59b38`), plus four new modules and the
solution; `LICENSE-leanerVM` at the entry root (the leanerVM-derived files keep their headers).
v3's Rust, Python and shell files are not copied (stage F2 owns the prover). The layout is stage
B's (`harness/evaluate.py`): `claim.json` at the root, the Lean flat in `lean/`.

| Module | What |
|---|---|
| 47 modules (field, BLAKE2s circuit and R1CS, MLE, sumcheck, RS, proximity, ring switching, transcript, Merkle, Ligero, Spartan protocol, prover, PCS bounds, chain R1CS, every soundness module up to `SoundnessKS`, `SoundnessChain`, the field/MLE/RS/Ligero/PCS/log controls) | **unchanged** but for the rename |
| `Oracle` | the `Monad OProg` instance now binds with the contract's `OProg.bind` (v3 defined its own, equal one); `katOracle q = BLAKE2s-256(0x52 ‖ q)` (v3's deleted `blake2sOracle`) as the known-answer tests' oracle |
| `TranscriptControls`, `Kat` | `blake2sOracle` → `katOracle` (the same function; the `hashlib` known answers are unchanged) |
| `Decode` | **rewritten**: v3's codec was for v3's node format (two plain child proofs); v4's byte facts: `decode_of_take`/`decode_of_extract`/`decode_append` (a proof starting with `encode w` decodes to `w`; `decode` of `encode W ‖ T` is `W`), `IsStrictPrefix`, `DecidableEq Sig` |
| `VerifierTop` | cut to the leaf branch: `LeafVerifier` (+ field `qb`, the per-leaf query bound), the header parsers, `leafProg` (unchanged), `decode_leaf` re-proved for v4's strict `decodeWit`, `leafProg_final`, the canaries' byte facts; v3's `check`/`checkNode`/`V`/`vb` removed; `digestFrom` reads bytes in place (`byteAt`, §5) |
| `Verifier` | `leafVerifier` sets `qb n := qBound (kap n)` |
| **`Queries`** (new) | `OProg.AtMost n p`: at most `n` queries along every path of answers; `runSeq_length` (an accepted trace has at most `n` entries), `queries_length` (the `KS` bound), its algebra |
| **`SnarkQueries`** (new) | `atMost_snarkProg`: v3's L-Q1 bound `qBound (kap n)` along every path |
| **`Node`** (new) | the v4 verifier `V LV vk c π` with the branches `L`, `C`, `N`, `B` (§2 below); `accWith`, `accV`, `accV_eq_acc` (= the contract's `acc`); `clearLeaves`, `runBundle`, `bundleOK`, `bundleProg`; `atMost_V`; `V_final`, `runBundle_final`, `clear_acc`; `fits_of_accV`, `V_encode_node` |
| `Submission` | `P` (key-taking), the generic `submissionOf LV proveLeaf`, `Facts` (v4 form), `acc_eq`, completeness for every key, `certificateOf`, `certificateR_of`; `εR1` as a rational cast (computable) |
| `SoundnessKSFinal`, `SoundnessKState` | `snark_final` (v3's leaf argument for one SNARK run on a log), `mu_final vk` = `V_final`; `kstate vk`, `ks vk` (`qV = 2^16`) |
| `Final` | `leafVerifier`, `proveLeafR1`, `facts`, **`submission`**, **`certificate`** |
| **`NodeControls`** (new) | the §6 controls (§4 below) |
| `Controls` | v3's controls; its claim negative moved to `NodeControls` |
| `Run` | `accRun` (= `submission.acc`), `proveWith H` (= `P` under an oracle function), `katOracleF`, `honestTrace`, `parseSigned`/`encodeSigned` (harness/FORMAT.md) |
| `Solution.lean` (new) | the rendered stub's `declared`, copied verbatim (diffed against `harness/render-challenge.py`'s output for `claim.json`); `submission := SpartanSrom.submission`; `certified` |
| `SpartanSrom` | imports every module |

`claim.json`: `error` `"1/680564733841876926926749214863536422912"` (2^-129), `completeness_error`
`"0"`, `qV` 65536, `fuel_base` 0, `fuel_per_word` 8.

### Line counts (code lines: not blank, not comment; v3's `scripts/loc.py` rule; `L/loc/`)

| | modules | code lines |
|---|---|---|
| v3 `spartan-chain` | 61 | 16,766 |
| v4 `spartan-srom` | 65 | 17,252 (24,037 total lines) |
| carried over unchanged (line-level diff after the rename) | 47 whole modules, 15,209 lines; 16,056 lines in all | |
| changed or added inside ported modules | 13 | 310 |
| new modules | `Node` 288, `NodeControls` 431, `Queries` 62, `SnarkQueries` 88, `Solution` 17 | 886 |
| v3 lines dropped | `Decode` 227, `VerifierTop` 255, `Submission` 84, `Solution` 23, others 121 | 710 |

Per ported module (v3 → v4 code lines, unchanged, added, dropped; `L/loc/loccmp-2.txt`):
`Decode` 247 → 63 (20, 43, 227); `VerifierTop` 386 → 189 (131, 58, 255); `Submission` 170 → 145
(86, 59, 84); `Oracle` 168 → 167 (164, 3, 4); `Run` 25 → 43; `SoundnessKSFinal` 22 → 26;
`SoundnessKState` 23 → 23; `Final` 17 → 20; `Verifier` 100 → 101; `Kat` 142 → 142 (2 changed);
`TranscriptControls` 83 → 83 (8 changed); `Controls` 102 → 92 (10 dropped).

## 2. The verifier (BLUEPRINT §2), as built

`V LV vk c π` (`SpartanSromNode`), decided from `π` before any query:

* `|π| < 8`: `ret false`.
* tag word `0`, `|π| = 48` — **`C`**: `ret (clearLeafOK c π)`: `leafN π ≤ chainCap` (checked first)
  and `c = leafStmtF (chainEndF (leafS π) (leafN π)) (leafN π)` (the library's fast twins).
* tag word `0`, `|π| ≠ 48` — **`L`**: v3's `leafProg`, unchanged.
* otherwise `match decodeF π` (the library's linear `decode`):
  * `some (.node c₁ c₂ p₁ p₂)` with `encodeF (.node …) = π` — **`N`**: `ret (c = nodeStmtF c₁ c₂ &&
    accWith vk p₁ (fun _ => V vk c₁ p₁.π) && accWith vk p₂ (fun _ => V vk c₂ p₂.π))`, recursive on
    the (shorter) child proofs (well-founded on `π.size`). `accWith` is the contract's `acc` with
    the fast hashes (`SigOkF`, `traceDigestF`); `accV_eq_acc` proves `accV = Submission.acc` for
    every submission whose `V` is `V LV`.
  * same node, not canonical — **`B`** (`bundleProg`): `encodeF W` a strict prefix of `π`; both
    slots clear trees under slot 1's signature `σ0` (`clearLeaves`: empty trace, `σ = σ0`,
    `|π| ≤ proofCap`, a 48-byte tag-0 clear leaf or a canonical plain node with statement
    `nodeStmt` of its children, recursively; it lists the clear leaves left to right); then, with
    no query, `bundleOK`: every bundled `1 ≤ n ≤ chainCap`, `|T| = Σ (32 + leafSize n − 80)`,
    `Σ qBound (kap n) ≤ 2^16`, `c = nodeStmt c₁ c₂`, `SigOkF vk (traceDigestF []) σ0`; then
    `runBundle`: for each bundled leaf in order, `h` and `π_S` read from `T`, the slot statement
    must be `leafStmt h n`, and `snarkProg` runs with fresh queries.
  * anything else: `ret false`.

`P` (§3): v3's leaf prover; a node is `encodeF w` (`N`), no query (D-5).
`E`, `ext`, `fuel`, `computes`: the library's `WitnessSending` ones, unchanged (§4).

## 3. The certificate (BLUEPRINT §5)

* **KS, every `vk`** (`KS.ks vk`): `KState (Rel (accV LV vk)) (V LV vk) WitnessSending.E (2^-129)`
  with v3's potential `KS.μ chainEvals` (it does not depend on `vk` or `V`), v3's `empty` and
  `step` unchanged, and `final := final_law vk` = `V_final (snark_final hμ)`:
  * `L`: v3's argument (`leafProg_final`, then `snark_final`);
  * `C`, `N`: by their definitions (they decide `Rel`; `N` decodes its witness);
  * `B`: the bundle accepted on the log ⇒ each `snarkProg` run accepts on the log
    (`runBundle_final`) ⇒ `chainEnd s n = h` for each bundled leaf (`snark_final`, v3's
    `runLog_chain` + `chainEnd_of_runChain` under `μ L < 1`; the potential already covers every
    chain of the log, so a bundle of `k` SNARKs costs no extra error) ⇒ every clear slot is
    accepted by `acc` (`clear_acc`, strong induction on the slot's proof size: no query, empty
    trace, the checked `σ0`) ⇒ `Rel (acc vk) c W`, and `E c π L = decode π = some W`.
  * qV: `atMost_V` (static bound in `B`, `qBound ≤ 2^14` in `L`) gives `queries_length ≤ 2^16`.
* **Completeness, every `vk`, `δ = 0`**: perfect completeness over every oracle function
  (`complete`), then the library's `complete_withError_zero`. Leaves as v3; a node witness's
  `encode w` is accepted by `N` (`V_encode_node`), which needs `w.Fits`, in particular every
  child's trace shorter than `2^64` entries: `fits_of_accV` gets it from `AtMost (2^16)` and exact
  trace consumption (`AtMost.runSeq_length`) — the reason for `Queries`/`SnarkQueries` (§7.2).
* **Computes**: `WitnessSending.computes` (definitionally the submission's fields).
* **Caps**: `εR1 = 2^-129 ≤ errorCap`, `δ = 0 ≤ completenessCap`, `qV = 2^16`, fuel `8 t ≤ B t`,
  `ext.body.size ≤ progCap` (`decide`).

### Axiom check

`#print axioms` (`L/axioms-print-2.log`):

```
'SpartanSrom.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
SpartanSrom.certificate : RecursionFast.Certificate SpartanSrom.submission
'RecursionFast.Challenge.certified' depends on axioms: [propext, Classical.choice, Quot.sound]
RecursionFast.Challenge.certified : RecursionFast.CertificateR RecursionFast.Challenge.declared
  RecursionFast.Challenge.submission
```

Every declaration of the entry, controls included (stage A's `AxiomAudit` with the module filter
changed to `SpartanSrom*`/`Solution`, `L/core/entrymain/EntryAxioms.lean`): **PASS**, 3,508
declarations within `propext`, `Classical.choice`, `Quot.sound` (`L/axioms-2.log`). Hygiene: no
`sorry`, `native_decide`, `partial`, `unsafe`, `opaque`, code-changing attribute; stage B's source
rule: `65 files, 0 finding(s)`. `decide +kernel` occurs 45 times, all carried from v3 on small
terms (the transcript/Merkle KATs evaluate a few BLAKE2s compressions in the kernel:
`TranscriptControls` is the slowest module, 75 s); the new modules use none.

## 4. Controls (BLUEPRINT §6)

Carried from v3 unchanged: field, circuit, MLE, RS, Ligero, transcript/Merkle KATs (under
`katOracle`), the log and PCS controls, `μ`/`Doom`/`Rej`/`EscAt`, the chain R1CS, booleanity.
New, in `SpartanSromNodeControls` (no hash evaluated; signatures through `Signer.sigOk_sign`):

| Kind | Theorems |
|---|---|
| formats | `format_C`, `format_N`, `format_B` (a bundle decodes to `W`, `decode` stops before `T`) |
| positive, reference signer `Signer.pk sk`, `σ0 = Signer.sign sk 0 (traceDigest [])` | `clearSlot_acc` (a clear slot is accepted); `clearTree_rel` (the clear tree of two clear leaves is a node witness of the relation); `clearTree_acc` (its plain encoding, signed `σ0`, is accepted by the entry's `acc`; 9,752 bytes, `clearTree_size`); `bundle_static` (the bundle of that tree with any `T` of the right size passes the whole static phase and reduces to its two SNARK runs) |
| positive, no query | `zeroLeaf_accepted` (`L`, `n = 0`), `zeroClear_accepted` (`C`, `n = 0`) |
| bundle negatives, no query | `clearLeaves_trace` (a slot with a non-empty trace), `clearLeaves_sig` (a slot with another signature), `bundleOK_size` (`|T|` off), `bundleOK_qbound` (`Σ qBound > 2^16`; reachable within `chainCap`: `qbound_nine`, nine `n = 2^20` leaves = 69,966 queries), `bundleOK_zero` (a bundled `n = 0`), `bundleOK_cap`, `clearLeafOK_cap`, `clear_overCap` (`n > chainCap`); `V_bundle_reject`, `bundleProg_none₁/₂` lift them to `V = ret false` |
| canaries (`V … = ret false` under every statement) | `canary_L_push/pop` (an accepted `L`), `canary_C_push/pop` (every 48-byte tag-0 proof), `canary_N_push/pop` (every plain node that fits), `canary_B_push/pop` (an accepted bundle; `bundle_accepted` gives what it passed), `zeroLeaf_canaries`, `zeroLeaf_other_stmt` |
| claim | `certificateR_claim` (the claim of `claim.json`); `claim_negatives`: `ε = 2^-130`, `qV = 2^16 − 1`, fuel `7 t` not certified |

Compiled checks on real files (`L/run/`): test material from `srom-run make-test` (two signed
`n = 16` leaves under the test oracle and the reference signer `Signer.Tree` of library
`SignerFast`, their clear leaves, a plain node, a bundle). Every canary (`π` ± 1 byte for `L`,
`C`, `B`; one flipped byte in `B`'s `T`; a trailing file byte; a wrong statement; a wrong key) is
rejected, by `srom-run` and by stage B's badge (19 rejections, no acceptance, `L/run/neg/neg.log`).

**Known answers.** `srom-run prove-leaf-kat` (the entry's `P` under `katOracle`) reproduces v3's
Rust prover byte for byte at `n = 16` (v3's `logs/spartan-chain/rust/kat/proofs/kat-n16.bin`,
143,711 bytes); F2 reports the same against its prover at `n = 1` and `16`.

## 5. Build and run measurements

**Build** (clean, the entry's 65 modules + the rendered challenge, against core `85f0985`, 8
cores): **2 min 38 s wall, 672 s user CPU, peak RSS 4.12 GB** (the largest Lean process;
`/usr/bin/time -v`, `L/build-full-3.log`; an earlier clean build of the same tree under heavier
load took 3 min 23 s, `L/build-full-2.log`). The core's contract and library: 42 s
(`L/build-core-2.log`).
Slowest modules: `TranscriptControls` (kernel KATs), `SoundnessKSBase`, `FieldBaseCorrect`,
`SoundnessChain`; the new modules take 4–10 s each.

**The compiled verifier** (one core, `taskset -c 20`; three runs, `L/run/verify-final.log`).
`badge` = stage B's `harness/badge/Verify.lean.in` rendered with `Solution` and built in the scratch
(`L/core/badge/`): its `NS` is parse + `accF`, what the harness times against `verify_s`.
`srom-run`'s `acc` excludes the parse.

| File (n = 16) | proof bytes | trace | file bytes | verdict | `acc` (srom-run) | badge NS | badge process wall |
|---|---|---|---|---|---|---|---|
| `L` leaf | 143,711 | 3,533 | 538,698 | accept | 0.18–0.20 s | 0.204–0.218 s | 0.29–0.31 s |
| `C` clear leaf | 48 | 0 | 4,840 | accept | 0.3 ms | 0.29–0.30 ms | 0.08–0.10 s |
| `B` bundle of 2 leaves | 297,078 | 7,066 | 1,082,260 | accept | 0.42–0.45 s | 0.45–0.50 s | 0.54–0.57 s |
| `N` plain node of 2 signed leaves | 1,089,384 | 0 | 1,094,176 | reject (`> proofCap`) | 3–7 µs | 0.69–0.83 ms | 0.08–0.09 s |

Breakdown of `B` (`L/run/probe-B.log`, `srom-probe`): `decodeF π` 60 ms (0.2 µs/byte over the
whole proof, `T` included), `encodeF W` 5 ms, the clear tree and static checks < 1 ms, the trace
digest 8 ms, `SigOk` 4–7 ms, the two SNARK runs the rest. The plain node `N` would have been
accepted by `V` (1.3 s) but is 40 KB over `proofCap`: plain witness-sending dies at the first
node, as the route analysis predicted (D-2).

**`parseSigned` and F2's 87.8 s / 579 s** (F2 RESULT §3.5): fixed. The cause was v3's
`digestFrom`, which read `π.data.getD`: compiled code materialises `ByteArray.data` as a boxed
copy of the whole array on every call, 32 calls per digest, so parsing a file was quadratic (and
every leaf check copied the leaf proof about 100 times). `digestFrom` now reads in place
(`byteAt`, proved equal by `rfl`); the runner's process wall is now 0.45–0.49 s for `L` and
0.94–0.97 s for `B` *including* its two extra breakdown evaluations, i.e. parsing is linear and a
few ms. Stage B's badge parser (`Common.lean.in`) is byte-level and linear (`get!`, 32-byte
`extract`s): under 0.83 ms for a 1 MB file (the `N` row: parse plus the size-cap rejection).

## 6. Deviations from the blueprint, and v3 statements that changed

### 6.1 Deviations

1. **`L` is `|π| ≠ 48`** (blueprint: `|π| > 48`). Proofs under 48 bytes go to `leafProg`, whose
   header check (`|π| = leafSize n ≥ 80`) rejects them with no query: the same accepted set.
2. **The static checks' order** in `B`: leaf range, `|T|`, query bound, `nodeStmt`, then `SigOk`
   (cheapest first); the per-leaf statement check `c = leafStmt h n` runs right before that leaf's
   SNARK (the blueprint's "for each bundled leaf in order"). Same accepted set.
3. **`LeafVerifier.qb`** (new field): the bundle's per-leaf bound is the leaf verifier's datum.
4. **`OProg.AtMost`** (not in the blueprint): needed for node completeness (§3, §7.2).
5. **The submission is computable** (`εR1 = ((1 / 2^129 : ℚ≥0) : ℝ≥0)`, equal to v3's
   `(2 : ℝ≥0)⁻¹ ^ 129`, `εR1_eq`): stage B's badge compiles `S.accF` of the whole structure, and a
   `noncomputable` submission does not compile there (§7.1).
6. Two speed changes to the verifier's code: `digestFrom` reads bytes in place (§5); `accWith`
   takes the child's program delayed (`Unit → OProg Bool`), so that a parent rejected by its
   size cap does not first build its children's programs (before: 1.3 s to reject the 1 MB
   `N` above; after: 3–7 µs).
7. The bundle negatives of §6 are general theorems; the query-bound negative is
   `bundleOK_qbound` with the reachability fact `qbound_nine`, not a concrete nine-leaf proof.
8. The `C` branch's recomputation is bounded by `chainCap = 2^20` (blueprint), so a random
   48-byte proof can cost `2^20` fast compressions (about 0.3 s at stage A's 280 ns); not bounded
   lower, as the blueprint keeps it.

### 6.2 v3 statements that changed (because the contract changed)

* v3 `KS.ks : KS (Rel (vb LV)) (V LV) E εKS (2^14)` → `KS.ks vk : KS (Rel (accV LV vk)) (V LV vk) E
  εKS (2^16)`: the key argument, the relation of `acc`, `qV = 2^16` (the bundle's bound).
  `kstate`, `mu_final`, `final_law` likewise take `vk`.
* v3 `Facts` (`ks`, `queries` with `2^14`) → v4 `Facts` (`ks` for every key; `atMost` along paths
  and `qb_le` instead of `queries`); `certificate (F)` → `certificateOf (F)`; perfect completeness
  `complete F : Complete (Rel Vb) P V` → `complete F vk` with the v4 relation and key.
* `final_of_leaf`/`final_of_not_leaf` (stated on v3's `V`) → `leafProg_final` (on `leafProg`) and
  `V_final`; v3's node lemmas (`checkNode_*`, `check_encode_node`, `check_stmt_unique`, node
  canaries on `check`) → `Node`/`NodeControls`; `tagWord_encode_node`, `size_encode_node` are about
  signed children (bound 88 → 8).
* v3's top-level controls on `check` (`zeroLeaf_accepted`, `zeroNode_accepted`, canaries,
  `bad_tag_rejected`) → `V … = .ret true/false` forms in `NodeControls`; v3's claim negatives (an
  image bit, fuel 7, `qV = 2^14 − 1`, `ε = 2^-130`) → `ε = 2^-130`, `qV = 2^16 − 1`, fuel `7 t`
  (no image in v4).
* Unchanged statements, re-proved: `decode_leaf` (v4's `decodeWit`), `leafBytes_parse`.

## 7. What in the v4 contract or library made the port harder (evidence for the rules' feedback)

1. **The badge needs a computable submission; nothing says so.** `harness/badge/Common.lean.in`
   compiles `S.accF vk c p` with `S := RecursionFast.Challenge.submission`, so the whole structure
   needs code; the gate (rule 4) accepts a `noncomputable` submission whose `ε` is spec data. With
   v3's `ε := (2 : ℝ≥0)⁻¹ ^ 129` (or the rendered `(1 : ℝ≥0) / 2^129`) the badge fails:
   `failed to compile definition, consider marking it as 'noncomputable' because it depends on
   'subV3', which is 'noncomputable'` (`L/noncomputable-probe.log`: `subV3` is the submission with
   v3's `ε`; the same `accF` of the entry as built compiles). Workaround: a
   rational cast. Fix: the template should project `S.V` (and `S.P`, `S.ext`) after unfolding, or
   the rules should require a computable `submission`.
2. **`Signed.Fits` vs the `KS` query bound.** `decodeWit_witWords` needs `p.tr.length < 2^64`
   (`Library/Words.lean`, `Signed.Fits`), so node completeness needs a bound on every *accepted*
   trace; `KS` bounds queries only under oracle **functions** (`Contract/Security.lean`,
   `∀ H c π, ((V c π).queries H).length ≤ qV`), and a trace may answer a repeated query
   differently. The entry had to prove a path-uniform bound (`AtMost`, `SnarkQueries`: 150 code
   lines). The announced change (`acc` checks `p.tr.length ≤ S.qV`) removes this need; adapting
   is small (journal, last entry).
3. **`acc` is restated in every recursive verifier.** `Submission.acc` takes the submission, so
   `V`'s node branch cannot call it; it restates it (`accWith`) and proves `accV_eq_acc`. Any
   change to `acc`'s conjuncts (as announced) must be mirrored by every entry.
4. **The library's `decode` packs the whole proof.** `decodeF π = decodeWit (packFast
   π.data.toList)` costs 0.2 µs/byte over all of `π`; for a bundle `encode W ‖ T` that is 60 ms for
   a 297 KB proof (13 % of `T_V` at the smoke shape) spent packing `T`, which is never read. A
   length-prefixed witness (or a library reader over bytes that stops at the witness) would remove
   it.
5. **`ByteArray.data` in compiled code is a full copy**: v3's `digestFrom` (`π.data.getD`) made
   parsing quadratic and every leaf check copy its proof ~100 times. Nothing in the contract is
   wrong, but the badge's `T_V` depends on such details; the library could export fast byte
   readers next to its fast hashes.
6. **`blake2sOracle` and `OProg.bind`.** The deleted oracle had to be re-created for the KATs
   (`katOracle`); the contract's new `OProg.bind` replaced v3's (equal) one. Both trivial.
7. **`decodeWit`'s new strict format** made v3's node codec obsolete and `decode_leaf` had to be
   re-proved (one lemma `take48_leaf`); the v4 `Words` reader lemmas made that easy.
8. **The plain node is over `proofCap` at the first level** (1,089,384 bytes for two signed
   `n = 16` leaves): the rules force every recursive entry to invent a bundle (D-2).
9. Infrastructure: the shared package tree
   `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` has no build products (its
   `mathlib/.lake` is empty); the scratch uses a private copy of stage A's tree. Lake's `globs =
   ["Foo.+"]` means submodules of `Foo`, not a name prefix: the scratch lists every root.

## 8. Open questions

1. The badge/computability mismatch (§7.1): which side changes? The entry is computable now.
2. The announced `acc` change: not landed at `a5e4cff`; the adaptation is listed in the journal.
3. Not run here: the comparator, the gate, nanoda, `evaluate.py cert` (the core has no
   `org-setup.sh` output, `.lake/rf/`). The badge template was built and run locally.
4. `T_V` at the smoke tree: the root bundle of 4 leaves is about 4 × 0.2 s + decode, ~0.9 s on
   this VM; against `T_triv,best / 10` that is likely over the cap, which the harness measures.
   The cheap wins left: decoding only the witness prefix (§7.4), the Lean SNARK verifier itself.
5. The `C` branch's `2^20`-step recomputation (§6.1.8): bound it lower (e.g. `2^16`) if the DoS
   column matters; soundness and completeness are unaffected (`P` never emits `C`, bundles check
   `n ≤ chainCap` themselves and could check the lower bound too).

## 9. Fix pass (2026-10-23): review `reviews/F1-lean-review.md`, golf, D-6, core `ea2e8ab`/`81e1ebf`

Order of work: the golf patch was applied **first** (`git apply logs/golf-lean/golf.patch`: it is
against `8111b71` and applied clean, where applying it after the review fixes would have needed
manual merges in `Node`, `NodeControls`, `VerifierTop`); then the core re-sync, D-6 and the
review fixes on top. Final tree: core `81e1ebf` (`git archive`; `RecursionFast/` byte-identical to
`ea2e8ab`), synced 2026-10-23T12:34Z. Logs below are under `logs/lean/` (`L/`).

### 9.1 Each finding and what was done

| Id | What was done |
|---|---|
| core `ea2e8ab` | `accWith` gains `decide (p.tr.length ≤ 2^16)` after the size cap (the contract's new `acc` conjunct with `qV = 2^16`); `accV_eq_acc` takes `S.qV = 2^16` (`acc_eq` passes `rfl`); `clear_acc`'s slot conjuncts (`have hs`) and `fits_of_accV` gain the conjunct; `Log = Trace` needed nothing. |
| F1-m1 (`wordBytes := enc64`) | `Decode.wordBytes_ofLE` re-proved through `enc64` (`wordBytes_length`, `enc64`'s `List.ofFn`); `take8_encode` already used `wordBytes_length` (golf G2). |
| **F1-M2** (`acc` cost under the public `σ0`) | (1) **D-6**: `clearCap := 2^12` (`Node`, docstring: no SNARK leaf above it fits `proofCap`); `C` checks `n ≤ clearCap` before any hash, `bundleOK` every bundled `1 ≤ n ≤ clearCap`; `GoodLeaf` and the controls follow; `L` keeps `n ≤ chainCap`. (2) **`tagWord`, `leafN` read in place**: `u64From π k` reads 8 bytes through `byteAt` (no `π.data` copy), `@[irreducible]` because unfolding it on a symbolic proof made `whnf` time out in `atMost_V`; bridges `u64From_eq`, `tagWord_eq`, `leafN_eq`. (3) **Nodes read at byte level** (new module `SpartanSromNodeBytes`, 180 code lines): after (1)+(2) the depth-100 chain still took 54–60 s (per level, the list-based `decodeF`/`encodeF` at about 1 µs/byte). `nodeFast π` parses the node by offsets (`parseNodeB`, unproved) and **validates** it: the reader's node must fit the format and its byte-level encoding `encodeB` (proved `= encode`, `encodeB_eq`) must equal `π` byte for byte (`bytesEqB`, in place, `bytesEqB_eq`). `nodeFast_sound`: its result is the canonical node (`decodeF π = some w`, `encodeF w = π`). `V`'s node branch and `clearLeaves` try `nodeFast` first and fall back to the library's decoder, so `V_tag` and the new `clearLeaves_eq` state them exactly as before and no proof above them changed. The attack (`L/run/attack-*.log`) is below. |
| F1-M1 (CompPoly allowlist) | No entry change: the core's stage B fix pass (FIXLIST Q2, `5b2b591`) adds `CompPoly.Fields.Binary.BF64.Ext3` and `CompPoly.Fields.Binary.BF64.Bytes` to `org-setup.sh`'s default `RF_ORG_ROOTS`, so the 28 CompPoly modules are allowlisted and pinned. The entry needs exactly those two roots (`SpartanSromFieldBase`, `SpartanSromFieldExtCorrect`), as v3 did. |
| Q7 (harness builds only `Solution`'s closure) | `Solution.lean` imports `SpartanSrom`, which imports every module, so the controls are built and checked with the certificate (header comment says so). |
| F1-m2 (stale names) | `NodeControls`' docstring names `bundleOK_size` (and `canary_B_push/pop`) for `|T| ± 1`. |
| F1-m3 (statement binding) | `clearLeafOK_stmt` (`C`), `V_node_stmt` (`N`, `V … = .ret false`), `bundleOK_stmt` (`B`'s node statement), `runBundle_stmt` (a bundled leaf's slot statement, before its SNARK); with `zeroLeaf_other_stmt` (`L`). |
| F1-m4 (`Batteries.Data.BitVec.Lemmas`) | Answered, not changed: it is v3's carried import (for `BitVec.ofFnLE`, used by `readWord`/`readByte` and their lemmas in two carried modules); it passes the gate today as an untrusted module that registers no code attribute. Recommendation to the organiser: add it to `RF_ORG_ROOTS` beside CompPoly; replacing it would mean re-proving `ofFnLE`'s lemmas inside carried modules. |
| F1-m5 (static bound unreachable within `proofCap`) | Wording: the control is now `qbound_fourteen` (fourteen `2^12`-step leaves, `qBound 12 = 4,753`, 66,542 > 2^16), "reachable within `clearCap`, not within `proofCap`" (`qbound_nine` used `n = 2^20` leaves, which D-6 rejects earlier). The check stays: `KS`'s bound is over every input. |
| F1-m6 (comparator, gate, nanoda) | Not run by F1; the orchestrator runs `harness/evaluate.py` on the entry against `81e1ebf`. The stage B badge template (`81e1ebf`'s `harness/badge/`) was rendered with `Solution` and built in the scratch (`L/core/badge/`); results below. |
| D-6 negatives | `clear_overCap`: the clear leaf of `n = 4097` is rejected (`V … = .ret false`, before any hash); `bundle_overCap`: a bundle whose clear tree holds a `4097`-step leaf is rejected with no query, under the reference key, whatever its `T`; `bundleOK_cap`, `clearLeafOK_cap` at `clearCap < n`. |
| golf | Applied in full (V1 Karatsuba `F.mul` proved `= mulLoop`, V2 `decodeFront`, V3 `@[inline] bundleProg`, G1–G6); `bundleOK_iff`'s range conjunct moved to `clearCap` with D-6, as the golfer foresaw. |

### 9.2 Statements

Statement dump of every non-internal constant (`logs/golf-lean/stmt/StmtDump.lean`) against the
golfed tree (`8111b71` + golf, core `a5e4cff`): `L/stmt-diff-fix.txt`. **Unchanged:** the
certificate, `Solution`'s `certified`, `KS.ks`, `kstate`, `complete`, `certificateOf`,
`V_final`, `clear_acc`, `V_tag`, `atMost_V`, `fits_of_accV`, `V_encode_node`, every carried
module's statement. **Changed (10, all by the review, D-6 or the core):** `accV_eq_acc` (+ `S.qV =
2^16`, core), `bundleOK_iff`, `runBundle_final` (bundled range `≤ clearCap`, D-6), and the
controls `clearSlot_acc`, `clearTree_rel`, `clearTree_acc`, `bundle_static` (hypotheses `n ≤
clearCap`), `bundleOK_cap`, `clearLeafOK_cap` (`clearCap < n`), `clear_overCap` (`n = 4097`).
Removed: `qbound_nine` (replaced by `qbound_fourteen`), `leafN.eq_1` (auto-generated). Added:
the D-6, m3 and NodeBytes declarations listed in the file. Definition bodies changed: `V`
(fast path), `clearLeaves` (fast path), `accWith`, `clearLeafOK`, `bundleOK`, `GoodLeaf`,
`tagWord`, `leafN`.

Runner verdicts on every test file (`logs/golf-lean/verdicts.sh`, 23 cases, `srom-run` and the
badge, plus the three prover KATs): **identical** to the golfer's (`L/verdicts-fix.txt`); the
KATs reproduce `kat-n16.bin`, `kat-v3s-n16.bin`, `kat-ab-n16.bin` byte for byte.

### 9.3 Checks and numbers (final tree, core `81e1ebf`)

* **Clean build** (65 modules + `Solution` + the challenge, 8 cores): **2 min 46 s wall, 690 s
  user, peak RSS 4.12 GB** (`L/build-full-fix2.log`). Slowest: `TranscriptControls` 74 s (kernel
  KATs), `SoundnessKSBase` 45 s, `FieldBaseCorrect` 22 s (golf V1).
* **Axioms**: `SpartanSrom.certificate`, `RecursionFast.Challenge.certified`:
  `[propext, Classical.choice, Quot.sound]` (`L/axioms-print-fix.log`); audit of all 3,600
  entry declarations PASS (`L/axioms-fix.log`). Source rule: `66 files, 0 finding(s)` (one
  binder renamed: the raw scan flags `, init`). No `sorry`, `native_decide`, `partial`,
  `unsafe`, `opaque`, code-changing attribute; `@[irreducible]` (`u64From`) and `@[inline]`
  (`bundleProg`) only.
* **Lines**: 17,901 code lines (24,940 total) in 66 modules; the fix pass and golf add 649 code
  lines over `8111b71` (NodeBytes 180, golf V1/V2 about 400, D-6 and m3 controls, u64From).
* **The badge** (stage B's `Verify.lean.in` at `81e1ebf`, rendered with `Solution`), one core,
  `NS` = parse + `accF`, three runs (`L/run/timings-fix.log`):

| Proof | proof bytes | trace | file | verdict | badge NS | was (§5) |
|---|---|---|---|---|---|---|
| `L` leaf, n = 16 (F1 test and F2's tree `L0`) | 143,711 | 3,533 | 538,698 | accept | 89–111 ms | 204–218 ms |
| `B`, 2 leaves (F1 test and F2's `N1_0`) | 297,078 | 7,066 | 1,082,260 | accept | 188–195 ms | 450–500 ms |
| `B`, 4 leaves (F2's smoke `root.bin`, r = 2) | 603,812 | 14,132 | 2,169,384 | accept | 404–619 ms | — |
| `C` clear leaf | 48 | 0 | 4,840 | accept | 0.3 ms | 0.3 ms |
| plain `N` over 2 signed leaves | 1,089,384 | 0 | 1,094,176 | reject (> `proofCap`) | 0.6–0.8 ms | 0.7–0.8 ms |

* **The review's attack** (`srom-attack`, the reviewer's probe extended with a mode `B` whose
  clear tree is the chain and whose `T` is one byte; one core; `L/run/attack-after-*.log`,
  `attack-final.log`):

| Proof (≤ 1 MiB, signed with the bundle's public `σ0`) | before (review) | after D-6 + in-place reads | final (+ `nodeFast`) |
|---|---|---|---|
| one `C` leaf, `n = 2^20` | 0.79 s, accept | 0 ms, **reject** (D-6) | 0 ms, reject |
| one `C` leaf, `n = 4097` | — | 0 ms, reject | 0 ms, reject |
| `N` chain depth 20, `C` leaves `n = 2^20` → `n = 4096` | 27.2 s | 2.5 s | 0.09 s |
| `N` chain depth 100 (970,448 B), `n = 1` | 68.5 s | 54.5 s | **0.46 s** |
| `N` chain depth 100, `n = 2^20` → `n = 4096` | 183 s | 60.1 s | **0.69 s** |
| `B` whose clear tree is that chain, `T` one byte | not measured | 50.8–51.4 s, reject | **1.3–1.5 s**, reject |

**Worst case now** among the measured shapes: 1.5 s (the bundle whose clear tree is a
970 KB chain, rejected by `|T|`), dominated by the one-level list-based `decodeFront` and
`encodeF` of the clear tree; a 4-leaf honest root 0.4–0.6 s. Every proof within `proofCap` that
`acc` can accept is bounded by one byte-level pass per nesting level (`nodeFast`), at most about
100 levels, plus at most a few SNARK checks (a node's children carry their traces, so a proof
within `proofCap` holds at most about two signed SNARK leaves or one signed bundle), plus `C`'s
`2^12` compressions per clear leaf. This is a measurement and an argument, not a theorem.

### 9.4 Remaining open items

1. `Batteries.Data.BitVec.Lemmas` in `RF_ORG_ROOTS` (F1-m4), the organiser's choice.
2. The bundle branch still encodes its clear tree with the list-based `encodeF` for the
   strict-prefix test (`bundleProg`) and decodes it with `decodeFront`: one pass, ≤ 1.5 s at
   1 MB; `encodeB`/`nodeFast` could replace both if the bundle's front ever becomes large in
   honest proofs (it is ≤ 10 KB per leaf pair today).
3. `evaluate.py cert` (comparator, gate, nanoda) on this tree: the orchestrator's next step.
