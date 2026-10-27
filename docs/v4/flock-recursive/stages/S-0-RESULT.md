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
