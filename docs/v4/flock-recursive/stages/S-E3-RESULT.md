# S-E3 (track L-circ): RESULT — replay templates

Stage S-E3 of `submissions/flock-recursive`, 2026-10-27/28, branch `v4/flock-recursive`
(uncommitted). Started on `eba6537` (BLUEPRINT revision 3.11); final builds against HEAD
`ac43569` (S-G1h), with HEAD's versions of other tracks' modules (`logs/fr-build-e3b/snap.sh`).
Every build and probe ran in the 16 GB scope. Logs are in `logs/S-E3/`; the journal is
`S-E3-JOURNAL.md`.

**Status.**
- Items 1–5 are done for the ops listed below. The whole library builds (`lake build
  RFSubmission`, 3 min 16 s, rc 0).
- **Main finding: `T_V` is not met.** The templated `evalM` and `evalMK` are proved equal to the
  MLEs and run in 1.13 s and 2.02 s per call. The time goes to the skeleton's 1.23 M sparse entries
  per node (F-7, §5).
- Templates are proved for 11 op kinds. `tensorW`, `rsWeight`, `walkA/B`, `kindInd`, `rowW`,
  `shiftTarget` and the `evalM` replay are still imports (§6).

## 1. What was built

Code lines by `.contract/scripts/loc.py` (code / total):

| Module | code (total) | Content |
|---|---|---|
| `FRVIRTplCore` (new) | 179 (309) | `Circ.Lin`/`Row`, moved from `FRVIRCompile`; the template DSL (`Wire`, `LinT`, `Env`, `Gate.mul`/`.inv`, `Tpl`, `gatesAt`, `Eqns`); **`Tpl.eqns_of_rows`** (rows ⇒ gate equations, generic); `instLin`/`instRow`, **`inst_eqns`**; `TKey`, `TCtx`, `instRows`, `AuxK`; `Tpl.cbits`/`rbits` |
| `FRVIRCompile` | 862 (1,098) | compiler hook `Ext`/`stepOut`/`compileFromX`; `Out.tin`/`aux`, `CS.tins`/`aux`/`tcount`/`tplRows`; `ExtOk`; **`compileFromX_sound`**, **`compileX_sound`**; `compile_sound` re-derived at `noExt`. `CS.add` is now linear in place (§2). **FR-R3′: 862 ≤ 1,000.** |
| `FRVIRTemplates` (new) | 206 (289) | combinators `mulsG`, `prodG`, `scanG`, `sqG`, `shiftG`, `frobG`; templates and correctness for `eqPt`, `shiftEq`, `phiRS`, `zero` |
| `FRVIRTplTab` (new) | 194 (251) | `eqTblG` (`FRMLE.eqTable` over forms, `eqTblG_ev`); `targetS` (leaf kinds), `slotW`, `maskRows` |
| `FRVIRTplLag` (new, subagent) | 383 (499) | `lagG` (Lagrange weights by prefix/suffix products, `lagG_ev`); `eqZ`, `lagrangeS`, `eqTableK` (K tree, Karatsuba), `dotKF` |
| `FRVIRTplExt` (new) | 300 (383) | `tplOf`, `tplExt` (ops → templates at their operand types; `dotKF`'s column as an auxiliary import); `ImplT`; **`tplExt_ok`**; `compileT`, **`compileT_sound`**; the two-pass layout (`keyCounts`, `mkLay`, `layOf`) |
| `FRVIRTplEval` (new) | 422 (588) | `eqN`/`gN`, **`gN_split`**; **`tpl_mle`**; `slotIRows`; the evaluator (`Prep`, `prepOf`, `instVal`, `slotVal`, split `eq` tables), **`slotVal_eq`**; bridges `rowsVal_F`/`rowsVal_K`; `slotCST`, `Plan`/`planOf`, `nodeIRows`; **`evalMT`/`evalMT_eq`**, **`evalMKT`/`evalMKT_eq`** |
| `FRNodeLayout` | 159 (293) | F-5's 266 digit bits (`lBitCells`, `selCells` +133, `lRows_length = 16,440`); the WOTS order (`wotsKindAt`, `wots*Block`, **`ind_wots`**); `mRowModel` on the measured counts, `mRows_le`, `usedBlocks_le` |
| `FRNodeCircuit` | 102 (175) | `SlotHolds` over `slotCST` (+ template rows, auxiliary imports); `slot_sound` via `compileT_sound`; `ImplT` threaded through `node_m_sound`/`child_sound`/`node_sound`; `PubCells` without padding cells |
| `FRVerifierImplOps` (L-cert's, split) | 331 (523) | mechanical split of `FRVerifierImpl`: the `…I`/`…S` ops and their `…_meets` |
| `FRVerifierImpl` (L-cert's, mechanical) | 146 (206) | `implCWith pl` / `specCWith pl` over the plan, `implC := implCWith (planOf fin)`; `evalM := evalMT`, `evalMK := evalMKI pl`; `implCWith_meets`, `implC_meets`; **`implC_implT`** |

### Main statements (axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, 33 audited, `logs/S-E3/axioms.log`)

- **`Tpl.eqns_of_rows`**, **`Tpl.inst_eqns`**: an instance's rows, with `one = 1`, give every
  gate equation at the pulled-back wires (`envOf`). This is proved once for all templates.
- **`tplX_ok`**, per template: the gate equations and the inputs' values give
  `outs.map ev = encV (value of implC's op)`:
  - `tplEqPt_ok` (`eqPoint`), `tplShiftEq_ok` (`shiftEqI`), `tplPhiRS_ok` (`phiRSI`);
  - `tplTargetS_ok` (`targetSLeafI`), `tplSlotW_ok` (`slotWI`), `tplMaskRows_ok` (`maskRows`);
  - `tplEqZ_ok` (`eqZI`), `tplLagrangeS_ok` (`lagrangeSI`), `tplEqTableK_ok` (`eqTab` over K),
    `tplDotKF_ok` (`dotKF`), `tplZero_ok` (`linkW`, `kindFoldWeight`).

  With `inst_eqns`, `tplX_ok` is A.11's `tplX_sound`. The implementations equal S-F2's
  specifications by the `…_meets` lemmas.
- **`tplExt_ok : ImplT impl → ExtOk impl L.ctx (tplExt L.ctx)`** for every layout `L`.
  **`compileT_sound`**: the run accepts and every tracked register is represented, given:
  - `ImplT`;
  - the skeleton rows, the template rows and the auxiliary imports;
  - the imports left;
  - the foreign flags.

  The layout plays no part in soundness.
- **`tpl_mle`** (A.11's `tplX_mle`, generic): the sparse value of one aligned instance equals
  `eq(τ_hi, ⌊X/2^a⌋) · (eq(σ_hi, ⌊cb/2^b⌋) · LOC + ONE · E(one) + Σ_IT u · E(ins_i))`.
  `LOC`, `ONE` and `IT` are computed once per key and evaluation. The theorem is over any
  commutative ring with `ι : F →+* R`.
- **`slotVal_eq`**, **`nodeVal_eq`**, **`evalMT_eq`**: `evalMT pl τ σ = evalMS pl τ σ`, the
  `FRVIREval.matMLE` of the node's indexed rows. **`evalMKT_eq`** + `sparseK_eq` give
  **`evalMK_meets`**. `implC_meets` holds with the templated `evalM`/`evalMK`.
- **`slot_sound` / `node_sound`** (FRNodeCircuit) now rest on `compileT_sound`.
  `implC_implT : ImplT (implC …)` discharges the new hypothesis.

## 2. Measurements (VM, one core `taskset -c 9`, 16 GB scope)

| What | Value | Log |
|---|---|---|
| `compileT` of one slot (two passes) | 0.45 s (was 12.5 s per pass before the `CS.add` fix: the slot array was copied every op) | `logs/S-E3/tpl.log` |
| `planOf` (both slots) | 1.1 s, once per process | `eval5.log` |
| per slot: skeleton rows / template instances / emitted template rows / aligned row span | 120,597 / 1,401 / 126,030 / 310,656 | `tpl.log` |
| per slot: import registers / auxiliary imports / foreign | 27,304 (was 27,691) / 871 (`dotKF` columns) / 168 (was 173) | `nodedump-run.log` |
| skeleton entries (A+B+C) per node | 1,230,280 | `vtime-rows.log` |
| **`evalMT`** (templated `evalM`) | **1.13 s** per call (3 reps) | `vtime-rows.log` |
| **`evalMKT`** (templated `evalMK`) | **2.02 s** per call | `vtime-rows.log` |
| **V on an N30 proof** (`vtime v N`, warm `runSeq`, HEAD's `gen`) | **166.3 ms best, 171.5 ms median** of 9; `traceDigestF` 14.7 ms | `vtime-N.log` |
| node dump (both slots, rows + register map + groups + aux + L + WOTS) | 10.8 s, 331 MB | `nodedump-run.log` |

**`T_V` against the VM-equivalent cap ≈ 264 ms.** HEAD's `gen` does not call `evalM`/`evalMK` yet:
`finE`/`finPf` are pending, so the 166 ms V excludes them. Adding one call of each gives
**≈ 166 + 1,130 + 2,020 ≈ 3.3 s, about 12.5× the cap.** In slot 0's `A` matrix, the skeleton's
sparse sum takes 140 ms (128 k entries, about 1 µs per entry) and the 1,401 instances about 0.2 s.
So the skeleton is about two thirds of the evaluation, and A.11's estimate (≈ 40 ms) does not
hold (F-7).

Build and kernel times (sequential, `lean -DElab.async=false --profile`): `logs/S-E3/profile-*.log`,
see §8.

## 3. Controls

| Control | Shows |
|---|---|
| `implC_implT` | `ImplT` (the new hypothesis of `compileT_sound`) is satisfiable: `implC` meets it |
| `pubCells_nodup`, `pubCells_length` | the nine public cells are distinct and match the nine values (non-vacuity of `PubCells`, without padding) |
| `ind_wots` | the exported WOTS order is `nodeLayout`'s, for every offset `< 498` of both slots |
| S-E2's `kindProg_rows_N` / `kindProg_rows_L`, `three_hot_*`, `ind_controls*` | unchanged; they now run through `compileFromX` at `noExt` |
| `mul_rows_honest` / `mul_rows_reject` (`FRVIRTplControls`) | the honest product satisfies its row; a wrong product fails it |
| `inv_rows_honest` / `inv_rows_reject` | the honest locals `x⁻¹`, `x·x⁻¹` satisfy the three inverse rows for every `x`, `0` included (so `Eqns` and `inst_eqns`' hypothesis are satisfiable); a wrong inverse fails them |

## 4. Deviations

- **D-1 (template shapes).** Each template mirrors `implC`'s implementation gate for gate, not
  A.11's gadget sketch, so its correctness is an identity of pure functions:
  - `eqTableK` costs 3(2^v − 1) rows (A.11: 6(2^v − 1));
  - `lagrangeS` costs 760 rows, by prefix/suffix products. A.11's barycentric form needs
    `(λ − node)⁻¹`, which is wrong when `λ` is a node, so the template would be unsound there.
  - `eqZ` costs 254 rows and `targetS` 255 rows (leaf kinds; the node's per-block `E` is S-C's,
    S-F2 gap 1).
- **D-2 (`tplX_mle`).** There is one generic theorem, `tpl_mle`, not one closed formula per op.
  The local part is computed once per key and evaluation from the template's own rows
  (`O(|tpl|)`).
- **D-3 (mechanical changes to L-cert's module).**
  - `FRVerifierImpl` is split into `FRVerifierImplOps` (unchanged content) and `FRVerifierImpl`.
  - `implC` goes through `implCWith (TEval.planOf fin)`, so that the plan is computed once.
  - `evalMKI`/`evalMKS`/`evalMK_meets` take a `TEval.Plan`.
  - `specC.evalM` is `TEval.evalMS` (indexed rows).
- **D-4.** `Circ.Lin`/`Row` moved to `FRVIRTplCore` under the same names.
- **D-5 (row indices).** M's rows are indexed explicitly (`TEval.nodeIRows`: slot σ at `σ·2^20`,
  instances aligned). S-G's `truthE`/`RowsFit` still use `Layout.nodeRows`: position-indexed,
  without templates. **Request (S-G):** move `truthE` to `TEval.nodeIRows`/`entriesI`, the
  matrices `evalM` now evaluates.
- **D-6.** The six padding cells are dropped from `PubCells` (coordinator, S-G1e).
- **D-7.** `mRowModel` mixes measured counts with A.11's estimates for the ops still without a
  template (§6): **976,945 per slot ≤ 2^20 (1.07×), 1,953,890 per node ≤ 2^21; used blocks
  61,349 ≤ 65,536.** The model is a closed-form list sum. The real program is not evaluated.

## 5. Findings for the blueprint

- **F-7 (major, `T_V`).** A.11 assumed a skeleton of 68,795 rows and about 140 k entries per node.
  HEAD's skeleton has 120,597 rows per slot and **1,230,280 entries per node**. S-G's finals add
  16,060 `mulK` (298 k entries per slot) and the Merkle steps add 60 k rows. Evaluated sparsely,
  this costs about 0.7 s per `evalM`. Changes needed, in decreasing effect:
  - **op-block templates for the skeleton's repeated blocks**: the 7,552 Merkle steps (8 rows
    each), `finP4`'s per-position Horner block, the sumcheck rounds. Their soundness can reuse
    `compile_sound`, with an equivariance lemma for `opOut` under substitution.
  - **slot symmetry**: both slots are the same program shifted by `2^20` in rows and M cells, so
    one pass with the factor `eq(τ₂₀, σ₂₀)` would halve the cost;
  - materialising long linear forms (`addK` chains feed Karatsuba twice);
  - a lower constant factor: about 1 µs per entry now, from one boxed F per operation;
  - compacting `IT` per input (`phiRS`'s `a` is read about 30 times).
- **F-8 (minor).** `kindInd` and `packFK` registers are untracked, so `maskRows`, `slotW`,
  `shiftEq` and 3 of the 5 `eqPt` instances fall back to imports. They need a `kindInd` template
  and tracked kind-dependent packs.
- **RowsFit (S-G1h request 2).** `RowsFit (nodeRows fin) 21 23` is **false for an arbitrary
  `fin`**: a `fin` that emits more than 2^21 `mulF` breaks it. For the concrete `finC` it is a
  fact about the generated program, so a closed-form proof needs per-generator count lemmas
  (S-E2's open D-2: lengths and row counts of `genPhase`, `merkleOps`, S-F/S-G's finals). Kernel
  evaluation of the compile is out (too large, and forbidden by the rules). Not done.
  Measured: 2 × 120,597 skeleton rows ≤ 2^21; the largest cell is about `slotBase 1 + 383,359 <
  2^23` (`tpl.log`).
- **S-G1h request 1 (WOTS order): confirmed.** Chain `i`'s step `s` is at offset `3i + s`
  (`w43`, offsets 0–398). The key leaf is at 399–465: `hashB1` at 399, `stream` at 400–464,
  `streamEnd41` at 465. Path step `t` is at `466 + 2t` (`hashB1`) and `467 + 2t` (`hashB2`).
  - Exported as `Layout.wotsKindAt`, `wotsStepBlock`, `wotsLeafBlock`, `wotsPathBlock`.
  - Proved against `nodeLayout` by `Layout.ind_wots`.
  - Dumped in `logs/S-E3/nodedump/wots.txt`.

## 6. Open

1. Templates still to write: `tensorW` (needs `AuxK.bits` for `j`, which is already in the
   core), `rsWeight`, `walkA/B` (`walk_eq_sum` for the MLE), `kindInd`, `rowW` (`lagG` +
   `eqTblG` exist), `shiftTarget` (needs the digest bits), and the child's
   `evalM`/`evalMK`/`evalL` replay (the evaluator expressed as rows). Until then these are imports
   of `compileT_sound`.
2. F-7: `T_V`.
3. `RowsFit` (above).
4. From S-E2: the H-side assembly of `node_sound`, `node_complete`.

## 7. Prover dump (P2)

`logs/S-E3/nodedump/` (`probe` source: `logs/fr-build-e3b/probe/NodeDumpT.lean`, dev-only):

- `mrows-σ.txt`: every M row with its **global row index** (skeleton `σ·2^20 + j`, template
  instances at their aligned indices), `A | B | C` as `cell:coef`;
- `mregs-σ.txt`: register → import flag, type, forms;
- `maux-σ.txt`: the auxiliary imports (`dotKF`'s column cells and the register they read);
- `groups-σ.txt`: per key, row base, cell base, bits and instance count;
- `lrows.txt`: L's 16,440 rows (266 digit bits);
- `wots.txt`: the WOTS order.

## 8. Build and kernel times

**Measured** on this VM: sequential `lake env lean -DElab.async=false --profile`, one core, 16 GB
scope (`logs/S-E3/profile-*.log`).

| Module | wall | tactic exec. | simp | type checking (kernel) | peak RSS |
|---|---|---|---|---|---|
| `FRVIRTplCore` | 8.3 s | 0.18 s | 0.42 s | 0.18 s | 2.6 GB |
| `FRVIRCompile` | 44.1 s | 13.7 s | 11.4 s | 1.35 s | 2.7 GB |
| `FRVIRTemplates` | 11.2 s | 0.82 s | 0.60 s | 0.17 s | 2.7 GB |
| `FRVIRTplTab` | 13.5 s | 0.38 s | 4.44 s | 0.55 s | 2.8 GB |
| `FRVIRTplLag` | 12.3 s | 2.73 s | 0.95 s | 0.63 s | 2.7 GB |
| `FRVIRTplExt` | 9.1 s | 1.10 s | 0.72 s | 0.16 s | 2.7 GB |
| `FRVIRTplEval` | 10.8 s | 0.80 s | 0.87 s | 0.34 s | 2.8 GB |
| `FRNodeLayout` | 8.6 s | 0.55 s | 0.52 s | 0.49 s | 2.6 GB |
| `FRNodeCircuit` | 6.4 s | 0.12 s | 0.10 s | 0.05 s | 2.7 GB |
| `FRVerifierImpl` | 7.3 s | 0.12 s | 0.35 s | 0.03 s | 2.7 GB |
| **total** | **131.6 s** | | | **3.95 s** | |

Each module's wall time includes about 3.6 s of import. Checks:

- Source rule: 97 files. Its 5 findings are all in `FRSoundnessFold.lean`, another track's
  untracked file; L-circ's files have none.
- Axioms: the 37 audited statements use at most `propext`, `Classical.choice` and `Quot.sound`
  (`logs/S-E3/axioms.log`).

**Requests.**
- Orchestrator: `FR.lean` (not L-circ's) should import the new modules (`FRVIRTplCore`,
  `FRVIRTemplates`, `FRVIRTplTab`, `FRVIRTplLag`, `FRVIRTplExt`, `FRVIRTplEval`,
  `FRVIRTplControls`, `FRVerifierImplOps`). All but `FRVIRTplControls` already come in through
  `FRVerifierImpl` and `FRNodeCircuit`.
- S-G: switch `truthE`/`RowsFit` to `TEval.nodeIRows` (D-5).
- S-0: track `packFK`/`kindInd` registers (F-8).
