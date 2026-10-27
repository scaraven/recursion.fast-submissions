# S-0 (interfaces): RESULT

Stage S-0 of `flock-recursive` (BLUEPRINT §9: `FRTranscriptDefs` with `items_length` proved,
`FRFormat` with `piSize` a proved sum, `reassemble`, `parse ∘ serialise` proved, `FRVIR` with `gen`
for the three kinds and `Mux`, `OpImpl`/`OpSpec`, `runIR`, `semIR`, `FRVIRSpec` with phase Z proved
and every other phase stated, the two dump tools, `sizes.py` and `serial.py` re-run).
2026-10-27, branch `v4/flock-recursive`, built against **BLUEPRINT revision 3.4** (`2fa83b1`); the
stage started on revision 3 and absorbed 3.1, 3.2, 3.3 and 3.4 as they landed (journal). Build tree
`logs/fr-build-s0/`, logs `logs/S-0/`. Uncommitted; nothing outside S-0's files was edited.

## 1. What was built

Code lines by the core's `scripts/loc.py` (`logs/S-0/loc.txt`):

| Module | code (total) | Budget (§7) | Content |
|---|---|---|---|
| `FRTranscriptDefs` | 352 (619) | 400 | `Kind` (`L32`, `P30`, `N30`), ladders (`ladder32/30`, `Level.ell/per/sq/sib`), **the phase table `phases`** (the one place every count lives), `Item`, **`items`**, **`items_length = 8852`**, `fsItems_length = 429`, tags, query builders (`seedQ`, `absorbQ`, `squeezeQ`, `nodeQ`, `colQ`), `streamBytes_eq = 1,435,888`, `chainLen_eq = 22,436`, `qlen_mod`, `items_aligned`, `streamOff_aligned`, challenge maps (`chF`, `chK`, `natLE`, `idxOf`, `posOf`), the `MerkleEnc` fields (`parseNode`, `parseCol`, `carried`, laws), `windows`/`inPlay`, `eqBits_eq_eq`, `domBits`, A.6's `BlockKind`/`zeroRows`, `NM`, `NL`, `qVBound` |
| `FRFormat` | 123 (228) | 700 | `fieldSize` (computed from the phase table), `fieldSizes_eq` (A.3's column), **`piSize_eq = 755,568`**, offsets, `hdrBytes`, `stmtLeafBytes`/`stmtNodeBytes` (rev 3.3's padded hash blocks), `kindOf` (`W`/`bad`/`snark k`), `serialise`, `parse`, **`parse_serialise`**, `parse_size`, **`reassemble`** (A.5, walking the phase table), controls |
| `FRVIR` | 406 (648) | 1,100 | `Val`, `Op` (A.8 plus structural ops, §4), `OpImpl`, `OpSpec`, `OpImpl.Meets`, `evalOp`, `Mode`, `VProg`, `runOps`/**`runIR`**, `exec`/**`semIR`**, `Op.item?`, **`gen`** (one generator per `Shape`, driven by `phases`; `GCtx`; `Finals`), `finZ`, `maskRows`, `stmtDigest` |
| `FRVIRSpec` | 683 (856) | 1,500 | generic (138): `runSeq_runIR`, `exec_append`, `queries_runIR`, `items_gen`, **`queries_gen = 8852`**, `semIR_mux`; **phase Z end to end** (373): `exec_round3`, `exec_rounds3`, `exec_uni`, `exec_sqzC`, `exec_absorb`, `exec_phaseZ`; the other phases stated (149): `refPhase` and its shape references, `exec_genPhase` (`sorry`); controls (23) |
| **total** | **1,564** (2,351) | 3,700 | |

Outside the entry: `probe/fr-irdump/` (`gen.sh`, `IRDump.lean`: a lake project with the entry's
modules as a library and a compiled `main`; no elaboration-time code), its outputs
`logs/S-0/dump/{items.json, ops-L.txt, ops-P.txt, ops-N.txt, ops-M.txt, summary.txt}`;
`logs/blueprint/serial.py` (new); `logs/S-0/Axioms.lean` (the axiom check).

### 1.1 The design in one paragraph

**One phase table** (`FRTranscriptDefs.phases`: name + `Shape` ∈ seed / absorb / squeezes / uni /
rounds / queries, with per-kind real counts) generates `items` (A.4), the field sizes and `piSize`
(A.3), `reassemble` (A.5) and `gen` (A.8). Every revision (3.1–3.4) was adopted by editing that
table and the op list; nothing else had to move. **`gen` emits one op list for all kinds**: kind-
dependent data are tables `Kind → α` inside ops (constants, an assertion's activity, a dummy Merkle
step, a position's answer register); a `VProg` is a **mode** (`fixed κ` = `gen κ`, `mux` = `gen
Mux`, whose kind is read from `hdr`) plus that list, so the three kinds and the mux share the list
literally and `semIR_mux` holds by definition at the IR level. Registers are SSA (each op appends);
**assertions clear a flag and never stop the run**, so every run asks every ask op, and
`items_gen : (gen fin m).ops.filterMap Op.item? = items` is proved from the table's structure
(never by evaluating `gen`). `semIR` runs the ops against a trace consumed in order and
`runSeq_runIR : (runIR impl P inp).runSeq tr = semIR impl P inp tr` is an equality.

## 2. The definition of done, item by item

| Item | Status |
|---|---|
| `FRFieldDefs` | provided by S-A's `FRField*` (reused, not duplicated) |
| `items` with `items_length` **proved** | `items_length : items.length = 8852` (`decide +kernel` on the closed-form table); `fsItems_length = 429`; also `items_gen`, `queries_gen` |
| `piSize` as a proved sum | `piSize := fieldSizes.sum`, `fieldSizes_eq` (A.3's 16 rows), `piSize_eq : piSize = 755568` |
| `reassemble` | `FRFormat.reassemble` (A.5; the sibling half by bit `h` of the position, dummies as zeros, the kind from the seed's `hdr`); its round trip for honest traces is not stated here (L-cert's `reassemble_roundtrip`) |
| `parse ∘ serialise` **proved** | `parse_serialise : fs.map size = fieldSizes → parse (serialise fs) = some fs`; negative `parse_size` |
| `gen` for L32 / P30-leaf / P30-node and `Mux` | `gen fin (.fixed κ)`, `gen fin .mux`; 61,753 ops, 53,088 registers, 8,852 asks = `items` (dump summary) — **the phase-final algebraic checks are the parameter `fin`**, see §4 deviation 4 |
| `OpImpl`/`OpSpec` | `OpImpl` (12 functions: `lagrangeS`, `tensorW`, `mbp`, `walkA/B`, `kindInd`, `evalM`, `evalL`, `selWeight`, `targetMLE`, `shiftTarget`, `slotW`, `kindFoldWeight`), `OpSpec` (same signatures, the mathematical reading), `OpImpl.Meets` |
| `runIR` parametrised by an op implementation, `semIR` | yes; `runSeq_runIR` |
| phase Z's semantic lemma **proved** end to end | **`exec_phaseZ`** (Z1, Z2, Z3, Zend): Z's ops on any trace equal the reference `refZ` (the ten squeezes and twenty coordinates, the univariate round and `lagrangeS(P, λ)` as Z3's first claim, 26 degree-3 rounds with P30's two dummies, the `â ‖ b̂` absorb); no `sorry` |
| every other phase's lemma **stated** | `exec_genPhase` (one statement for every phase of the table: its ops equal `refPhase`, the shape references `roundsT` (degree 2, 3, K), `posAllT`/`posT`/`stepsT` (columns, Merkle paths, caps), `seedT`, the absorb with `stmtOk` and the final message's padding). **The one `sorry` of S-0** (§6) |
| the two dump tools | `probe/fr-irdump/` `irdump ops L|P|N|M` (one line per op, `opName operands… → dst`, the kind tables resolved, or all three for the mux) and `irdump items` (JSON: phase, query kind, payload length, query length) |
| `sizes.py` + `serial.py` re-run | `logs/S-0/sizes-rerun.txt` (unchanged script; its items 8,852, stream 1,435,888 B / 22,436 compressions and `piSize` 755,568 equal the Lean values and the dump); `logs/S-0/serial.txt` (§5) |

## 3. Controls (all kernel-checked)

| Control | Kind | What it shows |
|---|---|---|
| `items_length`, `fsItems_length`, `streamBytes_eq`, `chainLen_eq`, `fieldSizes_eq`, `piSize_eq` | positive | the table's closed forms are A.3/A.4's numbers (and `sizes.py`'s) |
| `parse_serialise` / `parse_size` | pos. / neg. | the fields round-trip; another size does not parse |
| `kindOf_snark`, `kindOf_bad`, `kindOf_W`, `kindOf_small` | pos. / neg. | a kind byte with `piSize` bytes runs its program; with another size it is `bad`; a witness-sending proof (first word 0/1) is `W`; concrete instances (`[0x4E] ↦ bad`, `[1,0] ↦ W`, `[] ↦ W`) |
| `toy_accept` | positive | `semIR` accepts a toy program (input, one squeeze, an assertion) on its own query |
| `toy_wrong_query` | negative | another query is rejected (`none`) unless it happens to be the program's |
| `toy_reject` | negative | a failed assertion gives `some false` (the run still consumes the trace) |
| `toy_extra` | negative | a trace with an entry left over is rejected (`runSeq` uses the trace up exactly) |
| `parseNode_nodeQ`, `nodeQ_of_parseNode`, `parseCol_colQ`, `carried_nodeQ`, `carried_absorb` | positive | the `MerkleEnc` laws (S-D) for the protocol's encodings |
| `qlen_mod`, `items_aligned`, `streamOff_aligned` | positive | S-E1's size facts and S-D's alignment (§4 deviation 12) |
| `tags_distinct`, `ladder_sq`, `ladder_sib`, `ladder_logN_le` | positive | the tags differ; the ladders' derived counts are §2.2's; `n ≤ 2^20` |

Axioms (`logs/S-0/axioms.log`, 24 declarations): `propext`, `Classical.choice`, `Quot.sound` only,
except `exec_genPhase` (`sorryAx`, the declared S-0 `sorry`). Source rule: 35 files, 0 findings
(`logs/S-0/source-rule.log`).

## 4. Deviations from the blueprint (and readings of ambiguous text)

1. **The op set** (A.8 says "complete"): structural ops A.8 leaves implicit are added: `input`
   (`vk`, `c`), `const` (a kind table), `packF`/`packK`/`packFK` (arrays; `packFK` a kind-dependent
   register list, for P30's shorter vectors), `getF`/`getK`, `piElemK`, `piDigestAt` (a cap entry
   at a computed index), `eqTableK`, `dotKF` (a column folded by K weights, compiled to `mulKF`/
   `addK` rows), `shrN` (the cap index `j >>> sib`), `keep` (a kind-gated selection: a dummy
   Merkle step or round keeps the old value), `kindSel` (the selector bits). `askNode` carries its
   depth and activity table, `askAbsorb` its static length, `askSeed` takes `hdr` only (`vk`, `c`
   are the input). `walkA/B` take no block kind (rev 3.3+: masked row weights by `maskRows`).
2. **`gen κ` and `gen Mux` are one op list with a mode** (§1.1). `semIR_mux` is the IR-level fact;
   `compile_mux_sound` stays L-circ's.
3. **Assertions do not stop the run** (a flag), so the query sequence never depends on the proof's
   validity; `V` = the flag at the end.
4. **Phase-final algebraic checks are a parameter `fin : Finals`** (ops appended after the
   skeleton; `items_gen` requires that they ask nothing). Appendix A pins the transcript, the
   challenge maps and the round format, but not, in a form S-0 can write without inventing the
   PIOP, the final checks of Lc (walk and the per-kind `β` batching), Sh (target, `slotW`), Lr, RS
   (`ẑ` and the claims from the partials), E (the weight), B′, Ligerito's consistency and `Enc₄`
   check, and Pf. The skeleton has every query, every challenge map, every round's consistency
   check (`c₁ + c₂ = claim` for degree 2 and K; `c₃` completed for degree 3), Z2's `lagrangeS`,
   every Merkle path with its cap comparison, the column folds, the dummy-zero checks, the kind and
   `stmtOk` checks. **Delivered fragment: `finZ`** (Z's final value `ŵ(r′)(â b̂ + ẑ) + Ŵ_E`,
   given the register of `ẑ` from RS). Owners: S-C (Lc, Sh, Lr, RS, E), L-pcs/L-cert (B′, P, Pf).
5. **Initial sumcheck claims** (`initClaim`, provisional, S-C to confirm): Z3 from Z2's
   `lagrangeS`; Lr2 and E2 zero (zerochecks); every degree-2 and K phase **free** (the first
   message's `c₁ + c₂`, an output for the finals).
6. **Dummy rounds/squeezes sit at the end** of each phase: a dummy round's message is asserted zero
   and its claim kept; P30's unused squeezes are asked and ignored; P30's Merkle dummies `0^64`
   with zero sibling slots (asserted).
7. **Coordinate layouts of multi-coordinate squeezes** (A.4 is silent): coordinate `2s + c` is bytes
   `16c … 16c+15` of answer `s`; Z1: 20 slots, the first `m − 13` used; S1 (15 squeezes): `τ` =
   0–17 (P30: 0–15), `θ` = 18–27, `κ_s` = 28; RS1 (4): `r″` = 0–6, `κ` = 7; Lr1, E1 likewise.
   The phase outputs are all coordinates; consumers pick.
8. **`selWeight`/`targetMLE` operands**: A.8's types say `AF (m−14)` / `AF (m−6)`; `finZ` passes Z1's
   `m − 13` free coordinates and Z3's `m − 6` challenges (the pinned ones are A.1 constants the
   implementation prepends); the block parts are the last `m − 14`.
9. **Pf has 7 real rounds for every kind** (P30's final message is zero beyond `2^5`, so the
   7-variable sum is unchanged); the final message's padding is asserted zero for `m = 30`.
10. **`hdr`'s `pub`** is not checked by `gen` (it is bound by the seed query; for `'N'` it is free).
11. **A.2's sentence "the final message is 16 K-elements (512 B …)" is stale**; A.3/§2.3 (`2^7` K,
    4,096 B) used.
12. **Alignment** (S-D-M1): no framing change was needed: after `0x54` and the seed (160 bytes),
    every item is a multiple of 16 bytes and its 8-byte tag follows `enc64`, so payloads and answers
    sit on 16-byte stream boundaries (`items_aligned`, `streamOff_aligned`); the in-play windows are
    `windows` (query offsets `≡ 8 mod 16`) plus the answers (`inPlay`), as revision 3.3 states.
13. **`carried` (the `MerkleEnc` field)** follows revision 3.3 per query type (node `[l, r]`; absorb
    `st` and every 32-byte element of the message; seed `[vk, c]`; squeeze `[st]`); `parseNode`/
    `parseCol` check the full 8-byte tag including the level byte.
14. **`FRTranscriptDefs` imports `FRRS` and `FRMLE`** (for `eqBits_eq_eq`, as revision 3.3 places
    it) and the contract's `Oracle`/`Signature` directly (§7's `FROracle` does not exist yet).
    This puts `FRRS` on the serial path before `FRTranscriptDefs` (+388 lines; §5).
15. **A.6**: `BlockKind` (8 kinds) and the pinned intervals `zeroRows` are encoded; the `E` values are
    left to `FRPubTarget`. `maskRows` is concrete (`rowW[k] · Σ_{kind ∌ k} v[kind]`, kinds in
    `blockKinds` order: 8 entries where A.8 speaks of "≤ 7 `v_kind`").
16. **Z2's revision-3.4 message form** (`P^z`, `P^{ab}` on `Λ`, `P^{ab}|_S = P^z|_S + P^e|_S`) is
    inside `lagrangeS`'s implementation; `gen` reads 127 values and pad (unchanged). If S-C's form
    needs the two polynomials separately, `lagrangeS` gains an operand (an interface change).

## 5. Build, kernel, sizes

Per module, `lake env lean -DElab.async=false --profile` on one core (`taskset -c 7`), development
VM (shared, 32 vCPU); logs `logs/S-0/profile-*.log`:

| Module | wall | kernel | elaboration | import |
|---|---|---|---|---|
| `FRTranscriptDefs` | 20.8 s | 8.1 s (the `decide +kernel` over `items`) | 0.6 s | 3.7 s |
| `FRFormat` | 7.3 s | 0.25 s | 0.2 s | 3.7 s |
| `FRVIR` | 15.1 s | 0.3 s | 7.1 s (the `Op` inductive, `evalOp`'s match) | 3.5 s |
| `FRVIRSpec` | 27.2 s | 3.1 s | 3.1 s (simp 8.7 s) | 3.6 s |

A kernel trap found and fixed: the first `exec_round3` took **36.9 s** of kernel time (one round!):
`simp` normalising the growing register array with `push_app`/`app_app` produced proof terms the
kernel checks very slowly. Stepping with `exec_app` (one op from registers `r ++ L.toArray`,
normal form built into the lemma) brings it to 0.07 s. Successors must use `exec_app`, not
`exec` + array lemmas (journal).

**Sizes** (Lean = `sizes.py` = dump): items 8,852 (`qV = 10,240`, 1.16×), FS items 429, stream
1,435,888 B = 22,436 compressions per slot, `piSize` 755,568 (`proofCap` 1.39×).

**Serial path** (`logs/blueprint/serial.py`, `logs/S-0/serial.txt`; actual modules read, planned
ones from §7; **estimate** at 30 CPU-s/kLoC): 11,854 lines, ≈ 356 s, through `FieldBase →
FieldBaseCorrect → Field128 → Field256 → RS → TranscriptDefs → Format → VIR → VIRCompile → VIREval →
Verifier → SoundnessDefs → StepA → StepB → SoundnessFinal → KState → Submission → Final → Controls →
Solution`. Up to `FRVIRSpec`: 3,423 lines. 65 modules, 31.6 k lines (11.5 k actual, 20.1 k planned).

## 6. The `sorry` (the branch's; the merged entry has none)

| Declaration | Module | What closes it |
|---|---|---|
| `exec_genPhase` | `FRVIRSpec` | per shape, as `exec_phaseZ` does for Z's shapes: the degree-2 F and K rounds (copies of `exec_rounds3`), `.one`/`.pos` squeezes (as `exec_sqzC`), the seed, the `stmt` and final-message absorbs, and the queries shape (`posAllT`: the column, the Merkle steps with `keep`, the cap) — then a dispatch on `p.shape` |

## 7. The mid-point kill test (FR-R10)

**Measured: phase Z end to end is 373 code lines** in `FRVIRSpec` (the shape lemmas and the
composite; 364 in the scratch version reported in the journal at the time). The rule "its line
count × 15 phases ≤ 1,500" gives **5,595 lines: the rule as stated fails (3.7×).**

But the ×15 does not describe the module that was built: phases share shapes, and one statement
(`exec_genPhase`) covers all of them. Of the 373 lines, ≈ 230 are shape lemmas reused by every
later phase (interpreter steps, squeezes, absorb, degree-3 rounds by induction, the univariate
round), ≈ 140 are Z's composite. What remains to close `exec_genPhase` is the shapes Z does not
use: degree-2 F and K rounds (≈ 120 lines, near copies), `.one`/`.pos` squeezes (≈ 40), seed
(≈ 40), `stmt`/final absorbs (≈ 60), queries (≈ 200, the hard one), the dispatch (≈ 80): ≈ 540
lines (**estimate**), so `FRVIRSpec` ≈ 1,250–1,400 code lines against 1,500. **Proposal:** keep
the 1,500 budget and the IR design; replace the per-phase ×15 rule by "per shape", and re-check
when the queries shape is proved. The fallback (`V` as structured Lean with `runIR (gen k) = V k`
proved once) is not needed on this evidence; `refPhase` is already that structured reading, phase
by phase. Separately, the phase-final checks (deviation 4) will add their own semantic lemmas
(owned by S-C/L-pcs/L-cert, not counted here).

## 8. Interfaces for the other tracks

- **S-D / L-cert (`FRMerkle.MerkleEnc`)**: instantiate with `nodeQ i`, `colQ i`, `parseNode i`,
  `parseCol i`, `carried`; laws `parseNode_nodeQ`, `nodeQ_of_parseNode`, `parseCol_colQ`,
  `carried_nodeQ` (and `carried_absorb` for the cap's absorb). `Bad`'s windows: `inPlay`.
- **S-E1/S-E2**: `qlen_mod` (first query 119 ≡ 7, others ≡ 8 mod 16), `items_aligned`,
  `streamOff_aligned`; `chainLen = 22,436`; A.6's `BlockKind`, `blockKinds`, `zeroRows`,
  `isZeroRow`; `stmtLeafBytes`/`stmtNodeBytes` (128 B).
- **S-C**: `OpImpl`'s fields and signatures (§2), `initClaim`, the coordinate layouts (deviation 7),
  `eqBits_eq_eq` and the variable order (`bitOrderLE` docstring: round `t` binds bit `t`, low bits
  first; fold round `t` binds row bit `t`; `tensorW`'s `r` in round order).
- **L-circ**: `gen fin .mux` and `VProg.kindOn`; every kind-dependent op carries its `Kind → α` table;
  `maskRows`; `Op.item?`; the dump format.
- **P2 (prover)**: `logs/S-0/dump/items.json` (8,852 items) and `ops-{L,P,N,M}.txt` are the
  references; `reassemble` and the field offsets (`fieldOff`, `phaseOff`).
- **L-cert**: `kindOf`, `parse`, `reassemble`, `runIR`, `runSeq_runIR`, `queries_gen` (the query
  bound for `KS`), `semIR_mux`.

## 9. Open questions for the orchestrator

1. Deviation 4: who writes the `Finals` fragments (Lc, Sh, Lr, RS/`ẑ`, E, B′, P/consistency/`Enc₄`,
   Pf), and in which module? They are IR ops, so `FRVIR` (S-0's) or a new `FRVIRFinals` that
   imports `FRVIR` (proposed: keeps the cycle-free order; each owner writes its fragment and its
   lemma).
2. The kill-test reading (§7): accept "per shape" instead of "× 15 phases"?
3. `FR.lean` (imports all) does not import the S-0 modules; I did not edit it. Add
   `FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec`.
4. Blueprint text to fix: A.2's final-message sentence (deviation 11); A.8's op list (deviation 1);
   A.8's `selWeight`/`targetMLE` operand types (deviation 8); the coordinate layouts of S1, RS1, Lr1,
   E1 (deviation 7); "≤ 7 `v_kind`" against A.6's eight kinds (deviation 15).
5. `compileMux`'s dump (A.7's M layout KAT) is L-circ's; the dump tool has the hook (`irdump ops M`
   prints the mux program with the three kinds' tables).

## Fix pass

Against the review (`reviews/S-0-review.md`, M1–M3, m1–m8) and BLUEPRINT revisions 3.5 (A.9,
`J_z = 5`, `linkW`, `windows` by stream offset, `piSize = 757,616`) and 3.6 (cell-reading ops as
imports). Builds run under the memory cap (`systemd-run … MemoryMax=16G`); logs `logs/S-0/fix-*`.

**The 16:37 OOM was this stage's**: a scratch `lake env lean` of `flag_finSh` (51 ops evaluated by
`simp` over a growing register list; the lookups through `List.getElem?_cons_succ` built proof
motives quadratic in the list). Fixed by (i) closed-form register numbers in the helper ops
(`hornerOps`, `linkOps`: `b + (16 + 4f)`, never `b + 16 + 4 + …`), (ii) generalising the phase
offsets and input registers before evaluation, and (iii) list lookups by the rfl lemmas
`List.getD_cons_succ/zero`. `flag_finSh` now checks in 0.36 s kernel, under the cap.

### What changed (code lines, `loc.py`; `logs/S-0/loc-fix.txt`)

| Module | code | Change |
|---|---|---|
| `FRTranscriptDefs` | 361 | imports `FRMerkle` (not `FRRS`/`FRMLE`, m6); **`frEnc i : Merkle.MerkleEnc`** (S-D); `windowsFrom`, `inPlay` by stream offset (m1: the seed's windows at `7 + 16k`); RS0 `5 × 128 × 16` (`J_z = 5`); stream 1,437,936 B, `chainLen = 22,468`; `parseCol`'s docstring (m4); `domBits` documented as `FRRS.logNMax` |
| `FRFormat` | 123 | `piSize_eq = 757,616` (A.3 rev 3.5); `kindOf`'s W-by-first-byte documented (m5) |
| `FRVIR` | 425 | ops `eqPt`, `rowW`, `shiftEq`, `linkW` (imports, rev 3.6); `OpImpl.linkW/rowW/shiftEq`; **`Meets` per op under length preconditions, owners named** (m2); `Op.outs`, `opsOut`; `gen` → `genWith (fin : FinOps)` |
| `FRVIRSpec` | 727 | **M3**: `CtxOk`, `genPhase_ctx` (stated), `refPhases`, **`exec_genPhases`** (proved by induction from `exec_genPhase` + `genPhase_ctx`), **`exec_skeleton`**, `skeleton_ok` (an accepted run has every phase's flag) |
| `FRVIRFinals` (new) | 301 | **M1**: `FinIn`, `FinField`, the typed **`Finals`** (A.9: `finRS, finZ, finLc, finSh, finLr, finE, finB′, finP i, finPf`), `Finals.ops`, **`gen (fin : Finals)`**, `pending`, `s0Finals`; S-0's fields `finZ`, `finLc`, `finSh` (with the ≤ 8 link families), `finLr`; `pureRun`, `exec_pureRun`, `exec_field`; **`flag_finZ`, `flag_finLc`, `flag_finSh`, `flag_finLr`** (proved: each field asks nothing and its flag is A.9's relation, `relLc`/`relSh`/`relLr`, over the register values) |
| total | 1,937 | |

### Sequential kernel times (one core, `-DElab.async=false`, capped; `logs/S-0/fix-profile-*.log`)

| Module | wall | kernel | elaboration |
|---|---|---|---|
| `FRTranscriptDefs` | 21.5 s | 8.5 s | 0.6 s |
| `FRFormat` | 7.5 s | 0.25 s | 0.2 s |
| `FRVIR` | 15.2 s | 0.33 s | 7.3 s |
| `FRVIRSpec` | 28.9 s | 3.3 s | 3.1 s |
| `FRVIRFinals` | 26.6 s | 1.0 s | 13.6 s |

Resident memory per module ≈ 2.6–2.9 GB.

### The `sorry`s (the branch's; the DoD allows the non-Z phases)

| Declaration | What closes it |
|---|---|
| `exec_genPhase` | per shape (Z's shapes are proved in `exec_phaseZ`): degree-2 F and K rounds, `.one`/`.pos` squeezes, seed, `stmt`/final absorbs, queries |
| `genPhase_ctx` (new, M3) | per shape: `next` = the shape's width, `st`/`uni`/`posAns`/`foldR` inside the appended registers (definitional from `genPhase` plus the `refPhase` lengths) |

`exec_genPhases`, `exec_skeleton` and `skeleton_ok` are proved from these two; axioms
(`logs/S-0/axioms.log`, 33 declarations): only `propext`, `Classical.choice`, `Quot.sound`, plus
`sorryAx` through those two.

### Dumps (`logs/S-0/dump/`)

`irdump ops L|P|N|M` now prints the skeleton, then each final field under a `-- final <name>`
header; S-F's and S-G's fields are marked `PENDING placeholder`. 61,875 ops; asks = items = 8,852;
`piSize` 757,616. Until `finRS` lands, the S-0 fields read `ẑ`/`α_j` from register 0 (the
`zhat` list is empty).

### Deviations and open points of the fix pass

1. **The finals run after the skeleton**, in the order `finRS, finZ, finLc, finSh, finLr, finE, finB′,
   finP 0…4, finPf`, not after each phase (A.9 says "after the phase's skeleton"). They ask nothing,
   so the transcript is unchanged. The order is forced: `finZ` and `finSh` need RS's certified values
   `α_j`, which `finRS` computes from RS0's partials.
2. **`finLr` needs `â_L, b̂_L, ĉ_L`, and A.4 has no item carrying them** (Z has `Zend`; Lr has none).
   `finLr` reads them from `zhat[6…8]`, provisional. **Blueprint question:** add an "Lr end" absorb
   (48 B, like `Zend`), changing `items`/`piSize`, or say where the prover sends them. E (S-F) has
   the same question for `â_M, b̂_M, ĉ_M`.
3. **`finSh`'s link term uses the Sh point.** It computes `Σ_f κ_s^(f+2) linkW τ f r_blk` at the Sh
   point (`OpImpl.linkW : AF → ℕ → AF → F`), while A.8 types `linkW` at the RS point (`AK (m−7)`).
   Within `finSh` only the Sh point exists. The term's powers start at `κ_s²` (`κ_s¹` weights the
   `eq(0,·)` term). To confirm with S-C.
4. **`finLc`'s `β` powers** follow the order of L3's message (`v_i`, i < 7); `maskRows` takes 8
   entries in `blockKinds` order (leaf: `v₀` at `chain`; node: `v₀ … v₆` at the other seven kinds,
   `chain = 0`).
5. **New impl functions** `rowW` (Lagrange at `λ` ⊗ `eq(r′_hi,·)`, `2^14`) and `shiftEq` (`shift(τ,
   r)`), both S-C's (A.8 has no op for them); `eqPt` is concrete.
6. **m6 against S-D's request:** `nMax`/`logNMax` are not imported from `FRRS`, because that would put
   `FRRS` back on the serial path. `domBits = 20` stays and equals `FRRS.logNMax` by `rfl` where
   both are in scope. `eqBits_eq_eq` leaves S-0; its text, for its consumer (`FRSoundnessLigerito`,
   importing `FRRS` and `FRMLE`):
   `theorem eqBits_eq_eq {R} [CommRing R] (r : ℕ → R) (ℓ) (x : Fin (2^ℓ)) : eqBits r ℓ x = eq (fun v : Fin ℓ => r v) (cube x) := by rw [eq_cube, eqBits, bitSel, Finset.prod_range]`.
7. **Revision 3.6's `B′` point weight** for the M `one` cell is `finB′`'s (S-F); nothing in S-0.
8. **m8:** 29 warnings remain (unused simp arguments, deprecated `if_pos`), left for golf.

**Serial path** (`logs/S-0/serial.txt`): 10,220 lines, ≈ 307 s (**estimate**), down from 11,854
now that `FRRS` is off the S-0 chain: `… Field256 → TranscriptDefs → Format → VIR → VIRSpec →
VIRFinals → Verifier → …`.

### Revision 3.7 update

- **Items and fields:** the absorbs "Lr end" (48 B, after Lr2, field 7′ = `fLrEnd`) and "E end"
  (48 B, after E2, field 9′ = `fEEnd`) are added to the phase table. A.3 now has 18 fields, so the
  field constants after `fLr` shift by one or two.
  - `items_length = 8,854` and 431 FS items.
  - `fieldSizes_eq` (A.3 rev 3.7) and **`piSize_eq = 757,712`**.
  - Stream 1,438,192 B, `chainLen = 22,472`.
  - `reassemble` follows from the table, unchanged in code.
  - For `L32`/`P30` the two messages are asserted zero (node-only, like the dummy rounds; `refPhase`
    matches).
- **`finLr`** reads `â_L, b̂_L, ĉ_L` from the Lr-end field (`piElem fLrEnd 0/16/32`) instead of
  `zhat[6…8]`. `relLr` and `flag_finLr` are restated and re-proved.
  - Open point 2 of the fix pass is closed for Lr. E's source exists now for S-F's `finE`.
- **Settled by revision 3.7, no code change:** the finals' order after the skeleton (already as
  built); `linkW` at the Sh point (as built); `rowW`/`shiftEq` as ops with S-C owning the specs;
  `domBits`.
- **Re-runs agree:**
  - `sizes.py` (`logs/S-0/sizes-rerun.txt`): 8,854 items, 1,438,192 B, 22,472 compressions,
    757,712 B — equal to the Lean values.
  - The dump (`logs/S-0/dump/`, the prover's byte-for-byte reference): 61,884 ops, 53,092
    registers, asks = items = 8,854.
  - `serial.py`: 10,352 lines, ≈ 311 s (estimate).
- **Checks:** source rule 0 findings (43 files). Axioms unchanged: `sorryAx` only through
  `exec_genPhase` and `genPhase_ctx`. S-0's modules total 1,940 code lines.

### Shape lemmas and revision 3.8 (in progress)

**Revision 3.8 (and 3.8.1) in `gen`:**
- Z2 `lagrangeS vals λ pe → F × F` with `pe = targetS r` (Z1's point, the new `GCtx.pt`); Z3's
  initial claim is `P^{ab}*(λ)`.
- `finZ = eqZ((ρ,r), r′)·â·b̂` (new impl `eqZ`, S-C; it exports `P^z*(λ)` for RS claim 1);
  `selWeight`/`targetMLE` removed.
- `J_z = 4`: RS0 `4 × 128`, `finSh` one claim `(w_out + w_in)·ẑ`, `finLr` reads `zhat[3]`.
- P3.i is 5 squeezes (9 coordinates).
- The `free` kind (nothing pinned; A₀ = B₀ = I per 3.8.1) makes 9 `blockKinds`: the leaf's `v` at 0,
  a node's 7 `v` at 1–7, `free` = 0.
- `flag_finZ`/`finLc`/`finSh`/`finLr` are re-proved.
- **`items_length = 8,874`**, `piSize = 755,664`, stream 1,437,744 B, `chainLen = 22,465`.
- **Discrepancy to fix in the blueprint's tooling:** `logs/blueprint/sizes.py` line 26 has
  `add("RS1", …)` inside a comment, so it counts 8,870 items and 22,460 compressions. A.4 lists RS1
  (4 squeezes), and the Lean follows A.4.
- Open: A.3 still carries 7 `v_kind` (112 B). Should the `free` kind's `v` be sent (8 values)?
- Dump re-run under the cap (`logs/S-0/dump/`): 61,951 ops, asks = items = 8,874.
  `serial.py`: 10,573 lines, ≈ 317 s (estimate).

**Shape lemmas** (S-0's last part; `FRVIRSpec`, 1,002 code lines of the 1,500 budget):
- Proved:
  - `exec_round` (all three round kinds, claim as a register value) and `exec_roundsT`/`exec_roundsT'`
    (induction);
  - `exec_sqzOps`, `exec_merkleOps`/`exec_merkleOps'` and `stepT_spec`/`stepsT_spec`;
  - `exec_genPhase` for **seed, absorb (all four variants), squeezes (coords/one/pos), uni, rounds
    (uni/zero/free init, F and K)**.
- Two references changed so that the statement is true in every context:
  - `round2Vals`/`roundKVals`/`round3V` keep the claim register's value (`keep` copies it);
  - `posT` reads the position answers through the registers.
- **Remaining `sorry`s (3):**
  - `exec_posOps` (one queries position): its first evaluation reaches the kernel's "deep recursion"
    on the rewrite through `exec_merkleOps'` over the concrete 4-register prefix. Not over budget;
    to restructure as for `exec_round`.
  - the queries case of `exec_genPhase` (positions induction).
  - `genPhase_ctx`.
- **Estimate:** ≈ 120 lines for the queries shape and ≈ 120 for `genPhase_ctx`, so FRVIRSpec
  ≈ 1,250 of 1,500. FR-R10 per shape holds so far.
- **Kernel:** every proved shape lemma checks in under 0.5 s, and FRVIRSpec builds in ≈ 25 s under
  the 16G cap.

### The last `sorry`s and revision 3.9 (2026-10-27)

**`FRVIRSpec` has no `sorry`** (1,283 code lines of the 1,500 budget; `logs/S-0/loc-3.9.txt`).
`logs/S-0/axioms.log`: every listed theorem, `exec_skeleton`, `exec_genPhase` and `genPhase_ctx`
included, depends on `propext`, `Classical.choice` and `Quot.sound` only.
- `exec_posOps`: the kernel's "deep recursion" came from `rw [exec_merkleOps' … _ …]` with metavariables
  solved against the goal. The fix is a closed lemma `exec_posMid` (the Merkle ops after the
  4-register head, all arguments explicit) plus `posHead_size`/`posHead_rd0`/`posHead_rd2`.
- The queries case: `exec_posAll`, induction on the positions with the register file's size as an
  invariant, and `posT_length`.
- `genPhase_ctx`: length lemmas (`seedT_length`, `roundsT_length`, `posAllT_length`,
  `uniVals_length`, `coordVals_length`, `initVals_length`), `CtxOk.mono`, and one finisher per shape.
- **Hypothesis change (statement):** the seed alternative of `exec_genPhase`/`genPhase_ctx` is now
  `p.shape = .seed ∧ CtxOk c #[default]`, and `StartOk` changed with it. Without it, `genPhase_ctx`
  is false for a seed with an arbitrary context (the seed keeps `uni`, `pt`, `posAns` and `foldR`).
  `ctx₀` satisfies it (`exec_skeleton` is unchanged).
- Trap: `omega` does not see `<` at type `Reg` (an `abbrev` for ℕ) as a ℕ fact. The fix is
  `dsimp only [Reg] at *` first.

**Revision 3.9 and stage-review changes 11 (the op set, `FRVIR`):**
- `eqZ λ ρ₁ → AF 128` (`OpImpl.eqZ : F → F → Array F`).
- `rsWeight r″ pts κ ρ → K` replaces `mbp`. `pts : KC (List Reg)`: the claims' outer points, a
  leaf passing 3. `OpImpl.rsWeight : Array F → List (Array K) → F → Array K → K`.
- `phiRS r″ a → F`.
- `evalMK τ σ → K × K × K` (three K registers, `Op.outs = 3`).
- `shiftTarget τ θ bnd` (`bnd : AF 4`).
- The `OpImpl` fields `selWeight`, `targetMLE` and `mbp` are removed. `Meets` covers the new fields:
  `rsWeight`/`phiRS` on `r″.size = 7`, `shiftTarget` on `bnd.size = 4`.

**Revision 3.9 in S-0's finals (`FRVIRFinals`, now importing `FRSkip`):**
- `finZ` uses `eqPt` on `(ρ₁…ρ₇, Z1's free coordinates)` against Z3's challenges. The pinned
  coordinates are 7 `const` registers from `FRSkip.pinnedRho` (`pinOps`), as A.9 lists (`eqPt`, 2
  `mulF`, `assertEq`). Exports are unchanged in meaning (`â`, `b̂`, Z2's `P^z*`).
- `finSh` builds `bnd` first (`bndOps`, 7 registers), then calls `shiftTarget τ θ bnd`.
  - A leaf's `bnd` is `hdr` bytes 16, 32 (`s`) and `stmt` bytes 1, 17 (`h`), from A.3's layout.
  - A node's `bnd` is `h0` twice. `h0Bytes` is checked equal to `FRBlockLayout.h0`'s digest by
    `logs/S-0/check/H0Check.lean` (`decide +kernel`, log `h0check.log`).
- `finSh` and `finLr` read `zhat[2]` and `zhat[3]`. `flag_finZ` and `flag_finSh` are re-proved
  (`relSh` now takes `inp`).

**Outside S-0's modules:** `FRVIRCompile` (S-E2) needs a one-line change in its op match, or it
does not build. I made it:
- `.mbp` → `.rsWeight`/`.phiRS`;
- `.eqZ` → `imports [.af 128]`;
- `.evalMK` → `imports [.k, .k, .k]`, with `nOut 3`.

S-E2 should confirm the import kinds. Every module of `FR` builds under the 16G cap, including
`FRVIRCompile`, `FRVIRFinalsSF`, `FRVerifier`, `FRNodeCircuit`, `FRVIRFinalsSG` and
`FRSoundness*` (2,260 jobs). `FR.lean` itself fails on a name clash that is not S-0's:
`FRVIRFinalsSG` defines `FR.accV`, which `FRVerifier` already defines.

**Dump (`logs/S-0/dump/`, previous dump in `prev/`):**
- The dump tool imports `FRVIRFinalsSF` and dumps S-0's and S-F's finals. Only `finP 0…4` and
  `finPf` are marked PENDING; S-G's private copy dumps those.
- Array constants are printed with their values (`AF:[…]`, `AK:[…]`).
- `gen.sh` takes every module as a root.
- Result: 149,974 ops, 53,164 registers, asks = items = 8,874, `piSize` 755,680. `items.json` is
  byte-identical to the previous dump.

**Checks:** `source-rule`: 63 files, 0 findings. `serial.py`: 7,974 lines on the serial path
(`logs/S-0/serial.txt`). Its table does not yet list `FRVIRFinals → FRSkip`.

**Open:**
- The leaf's `bnd` byte offsets (`hdr` 16/32, `stmt` 1/17) and the node's `h0`-twice order need
  P2's confirmation, as do the 7 `pinOps` constants' position in `finZ`'s point (variables `0…6`).
- S-F's `finRS` still has to switch to the new `eqZ λ ρ₁` (bit 6 = `ρ₁`).
- The concrete `OpImpl` needs computable twins of `rsWeight`, `phiRS`, `evalMK`, the three-argument
  `shiftTarget` and the AF-valued `eqZ`.
