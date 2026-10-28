# S-E4 (track L-circ): RESULT — the verifier-time redesign, part 1

Stage S-E4 of `submissions/flock-recursive`, 2026-10-28, branch `v4/flock-recursive`
(uncommitted). Started on `f100c0d` (BLUEPRINT revision 3.12); final builds against HEAD
`603fc91` (S-0's revision-3.12 commit). Every build and probe ran in the 16 GB scope; probes on one
core (`taskset -c 9`). Build tree `logs/fr-build-e4` (`snap.sh`); logs in `logs/S-E4/`; journal
`S-E4-JOURNAL.md`.

**Status.**
- **The kill test passes.** The projection is 229.8 ms VM against 230 ms, and 215.4 ms with the
  fused `walkAB` op (§1).
- Done:
  - the flat evaluator (`FRVIRTplFast`; `evalMT_eq` unchanged). `evalM` takes 545 ms, down from
    1.13 s.
  - the walk sped up (`walkABF_eq`);
  - the fused `walkAB` IR op, added in S-0's modules at the coordinator's request;
  - `mRowModel` on revision 3.12's figures;
  - V (N30) measured at **149.7 ms best, 154.8 ms median**, down from S-E3's 166.3 / 171.5.
- **Not done (stopped here, §6):** the compiler-side half of the plan, which is where the rest
  of the time goes. That half is the op-block templates for the skeleton, the aligned layouts
  that give the regular and run import classes, and the class lemmas that come with them. With
  S-E3's circuit, the skeleton costs **≈ 440 ms of `evalM` even when evaluated flat**, so the plan's
  48–52 ms cannot be reached by evaluator work alone (§2, F-9, F-10).

## 1. Kill test (before any refactor; `logs/S-E4/kill.log`)

Probe `probe/fr-e4kill/E4Kill.lean`, outside the entry. It uses the entry's `F` and `walkAB`,
flat `Array F` tables and `for` loops, with the real node sizes from `logs/S-E3/nodedump/`.
Times are the median of 9 runs.

| Class | F products | ms | ns / product |
|---|---|---|---|
| `F.mul` chained (reference) | 10^5 | 8.30 | 83.0 |
| eq tables `τ` 2^11 + 2^10, `σ` 2^12 + 2^11, the walks' 2 × 2^14 | 41,978 | 4.51 | 107.4 |
| (i) regular imports, 1,500 (key, import) pairs, dyadic `rangeEq` | 86,582 | 10.08 | 116.5 |
| prefix array over 2^12 | 4,096 | 0.42 | 101.7 |
| (ii) Merkle-step runs, 7,552 × 4 | 45,312 | 5.06 | 111.6 |
| (iii) `hornerPos` LOC (127 `mulK`, 381 rows, 2,667 entries) | 1,524 | 0.20 (76 ns per entry) | 133.2 |
| (iv) `walkAB` as implemented, one run giving both `Â₀` and `B̂₀` | 29,440 | 14.32 | 486 |

- **Flat loops cost 102–117 ns per F product**, so the plan's 120 ns holds.
- Projected `evalM`: one table set and one walk, LOC for 36 k entries, and both slots' regular
  pairs and runs. That is 4.51 + 14.32 + 2.74 + 2 × 10.08 + 2 × 5.15 + 0.42 = **52.5 ms**.
- **V = 166.3 + 8 + 3 + 52.5 = 229.8 ms VM** against 230 ms; the kill threshold is 253 ms.
- With the fused op in V itself: **215.4 ms**.
- With regular pairs at the plan's 30 F instead of 58: 205.8 ms.

## 2. What was built

Code lines by `.contract/scripts/loc.py` (code / total).

| Module | code (total) | Content |
|---|---|---|
| `FRVIRTplFast` (new, L-circ) | 356 (522) | See below this table. |
| `FRVIRTplEval` (L-circ) | 372 (514) | The node section moved out. `prepT` (the template as an argument); `prepOf := prepT (tplOf k)`. |
| `FRVIREval` (L-circ) | 176 (268) | **`walkABF`**: the walk with the input rows summed over the 896 input positions (`inPos`) and `B̂₀`'s input term as `c · Σ e`. **`walkABF_eq`** (`sum_inPos`). `walkImpl := walkABF`. |
| `FRNodeLayout` (L-circ) | 158 (295) | `mRowModel` on revision 3.12's figures (§4). `mRows_le` and `usedBlocks_le` re-proved. |
| `FRNodeCircuit` (L-circ) | — | Import `FRVIRTplFast` (one line). |
| `FRVIRCompile` (L-circ) | 863 (1,099) | `opOut (.walkAB ..) = imports cs [.f, .f]`; `Op.nOut` = 2. |
| `FRVIR` (S-0's; mechanical, coordinator's request) | 447 (726) | `Op.walkAB (rowW colW)` replaces `walkA` and `walkB`. `OpImpl.walkAB : Array F → Array F → F × F`. The `Meets` conjunct; `evalOp` gives two F registers; `Op.outs` = 2. |
| `FRVIRFinals` (S-0's; mechanical) | 306 (426) | `finLc`: one `.walkAB (b+16) (b+18)`, so registers `b+19` and `b+20` are unchanged. `relLc` reads `(walkAB rw cw).1 + α·(walkAB rw cw).2`. `flag_finLc` builds unchanged. |
| `FRVerifierImpl` (L-cert's; mechanical) | 145 (205) | Import `FRVIRTplFast`. `implC.walkAB := Eval.walkImpl`; `specC.walkAB := (walkSpecA, walkSpecB)`; the `Meets` bullet. |

`FRVIRTplFast` contains:
- **The forms grouped by high cell index** (`grp`, `glVal`, **`glVal_grp`**) and **the rows
  grouped by high row index** (`grows`, `growsVal`, **`growsVal_grows`**).
- **`compactIT`**, which keeps one coefficient per input (**`compactIT_sum`**).
- `cprep`, `pcache`, `pfind` (`pfind_eq`) and `tplCache`.
- `GInst`, `ginstOf`, `ghv`, `ginstVal` (**`ginstVal_eq`**).
- `FSlot`, `fslotOf`, `fslotVal` (**`fslotVal_eq`**: the flat value of a slot is `slotVal`'s).
- The node section moved from `FRVIRTplEval` (`slotP`, `slotLay`, `slotCST`, `Plan`, `planOf`,
  `nodeIRows`, `nodeVal`, `evalMS`, `evalMKT`). `Plan` gains `fs0`/`fs1`, `tp` and their proof
  fields; `planOf` goes through `mkPlan`.
- `nodeFlat` (**`nodeFlat_eq`**), the flat **`evalMT`**, and **`evalMT_eq`** with S-E3's
  statement.

The fused op's signature (journal §2.2): **`walkAB rowW colW → F × F`**, `(Â₀, B̂₀)` from one
walk, replacing `walkA`/`walkB` in `finLc`. Neither old op is referenced anywhere, so both were
removed.

### Main statements

All 18 audited statements use only `propext`, `Classical.choice` and `Quot.sound`
(`logs/S-E4/axioms.log`):
- `TEval.evalMT_eq`, `fslotVal_eq`, `ginstVal_eq`, `glVal_grp`, `growsVal_grows`,
  `compactIT_sum`, `pfind_eq`, `nodeFlat_eq`, `evalMKT_eq`;
- `Eval.walkABF_eq`, `sum_inPos`, `walkA_eq`, `walkB_eq`;
- `Impl.implCWith_meets`, `implC_meets`, `implCWith_implT`;
- `Layout.mRows_le`, `usedBlocks_le`.

No statement changed. `evalMT_eq : evalMT pl τ σ = evalMS pl τ σ` and `walkA_eq`/`walkB_eq` are
S-E2/S-E3's statements. The new implementations are proved equal to them.

## 3. Measurements (VM, one core, 16 GB scope)

| What | Value | Log |
|---|---|---|
| **`evalMT` (flat)**, the node's three M matrices | **537 ms best, 545 ms median** of 5 (S-E3: 1.13 s); equal to S-E3's generic `nodeVal` at a random point | `eval-2.log` |
| ... slot 0, A / B / C | skeleton 75 / 93 / 55 ms; instances 17 / 40 / 1 ms; keys' local parts 4–5 ms per matrix; high factors 7 ms; tables 3 ms | `eval-2.log` |
| ... slot 0's data | skeleton 120,599 rows, 389,014 cell groups, 672,886 entries; 1,401 instances (all aligned), 87,994 inputs, 281,675 input cells | `eval-2.log` |
| `planOf` | 1.9 s, once per process. The harness times warm checks (`rfh/checks.py`, `verify(warm=True)`), so this is outside the timed check. | `eval-2.log` |
| `walkAB` | 14.5 ms: gadget core 8.5 ms, `Finset` input sums 5.5 ms. `@[specialize]` on every gadget gives 8.4 ms, so it gains nothing. | `walk-spec.log` |
| **V (N30), HEAD `603fc91`** (`vtime v N`, warm `runSeq`) | **149.7 ms best, 154.8 ms median** of 9; `traceDigestF` 12.6 ms. `gen` still has no `evalM` call (`finE`'s (iv) is pending). | `vtime-N.log` |
| per-op profile (N30) | `dotKF` 30.3, `askNode` 25.0, `idx` 20.5, **`walkAB` 9.9** (S-F2: `walkA` + `walkB` 30.2), `mulK` 9.7, `maskRows` 8.3, `piDigest` 8.0 ms | `prof-N.log` |

**`T_V` now:**
- V without `evalM` is 150 ms VM. The flat `evalM` adds 545 ms, giving ≈ 0.7 s VM. The
  VM-equivalent cap is ≈ 264 ms, so this is ≈ 2.6× over.
- Of the 545 ms, ≈ 440 ms is the skeleton. It costs about one product per (row, form) and one per
  cell group; the forms' cells are spread over many `2^12` blocks (1.7 entries per group).

**Build and kernel times** (sequential `lake env lean -DElab.async=false --profile`, one core;
`logs/S-E4/profile-*.log`):

| Module | wall | import | simp | tactic exec. | type checking (kernel) | peak RSS |
|---|---|---|---|---|---|---|
| `FRVIRTplFast` | 9.3 s | 3.7 s | 0.78 s | 0.34 s | 0.20 s | 2.7 GB |
| `FRVIREval` | 8.3 s | 3.4 s | 0.82 s | 0.52 s | 0.13 s | 2.6 GB |
| `FRVIRTplEval` | 10.1 s | 3.6 s | 0.86 s | 0.76 s | 0.31 s | 2.7 GB |

**Checks:**
- Source rule: 106 files, 0 findings.
- Build against HEAD `603fc91` with these files (`logs/S-E4/b9.log`): everything builds except
  `FRXLog` and `FRSoundnessDefs`. Both fail on S-0's commit (`piSize`, `fsRanges`), not on S-E4.
- The final library tree (`b12.log`) uses HEAD's `FRNodeLayout` with S-E4's `mRowModel` block.
  It builds `FRVerifierImpl` and `FRNodeCircuit`.

## 4. `mRowModel` (revision 3.12)

Per slot: skeleton 120,597 (measured) + emitted templates, aligned, 190,059 (measured) + the
missing templates 118,639 + `walkAB` 65,536 + `Φ`'s claim 5 17,152 + the child's `evalM` replay at
an F point 422,912. That is **934,895 ≤ 2^20 (1.12×)**, and 1,869,790 per node ≤ 2^21. The used
blocks are 60,692 with HEAD's H, and 62,212 with H grown by 2 × 760 blocks; both are ≤ 65,536.

The 3.12 model in `sizes.py` (805,330 per slot) leaves out the `walkAB` template's rows: the
tables `rowW′` and `colW` and the two walks' `2^14` product rows. They are added here (F-11).

## 5. Controls

- No specification changed, so no new definition is relied on by the certificate. The new code
  is proved equal to the existing specifications: `evalMT_eq` to `matMLE` of `nodeIRows`, and
  `walkABF_eq` to `walkAB`, hence `walk_eq_sum`.
- S-E3's controls are unchanged and build (`FRVIRTplControls`).
- The probe checks the flat value against S-E3's generic evaluator at a random point
  (`eval-1.log`, `eval-2.log`: `equal true`).

## 6. Findings, deviations, and what is left

- **F-9 (major): the Merkle chain's linear forms grow.**
  - `keep` and `selectHalf` compile to `muxOut`, whose output form is `x ++ u`. The current digest
    `cur` therefore gains one cell per step, and a step at depth `h` has forms with `h + O(1)`
    cells (the dump: B forms of 2, 3, 4, … cells along a path).
  - Steps at different depths are then **not instances of one template**. A `merkleStep` key
    needs `cur` materialised: one row `⟨one, x ++ u, v⟩` per component of the `keep`, or a
    length-triggered materialisation in `muxOut`, with `muxOut_sound` extended.
  - Cost: +2 rows per step, 15,104 rows per slot (well inside the 1.12× margin of §4).
- **F-10 (major): the remaining `T_V` is all on the compiler side.**
  - Flat evaluation of S-E3's circuit reaches 545 ms. The sparse skeleton cannot go below
    ≈ 1 product per row and per cell group, about 70 ms per slot per matrix triple.
  - The plan's 48–52 ms needs three things together:
    1. **block keys for the skeleton**: the Merkle steps (≈ 48 k of slot 0's rows) and
       `finP4`'s Horner block (≈ 48 k), with their locals and rows in aligned regions;
    2. **aligned allocation** of the import cells (`phiRS`'s 128 `a` cells per instance,
       `dotKF`'s columns, the steps' `cur`), so that the regular and run classes exist;
    3. the class lemmas in the evaluator.
  - On the current layout, the regular and run classes do not occur, because `compile` allocates
    fresh cells one after another. So `regImport_mle`, `run_mle`, `eqTree_mle` and
    `walkRows_mle` were not written as unused lemmas. The kill test's implementations
    (`E4Kill.lean`: `rangeEq`, the prefix runs) are the reference for them.
- **Route for item 3, with a smaller proof burden than `tplBlock_sound` via equivariance**:
  - Keep `compile`'s rows and soundness. Only *place* them: block `t` of a key gets aligned
    rows, and its fresh cells are renamed into an aligned region.
  - A cell renaming `π` preserves soundness for free: `(rename π r).Holds w ↔ r.Holds (w ∘ π)`.
    `π` is the identity on H/L, public and selector cells.
  - At `planOf`, a block's rows are abstracted to a template (cells inside the block → `loc`,
    others → single-cell inputs). The block is grouped with a key only if a decidable check
    finds its template equal to the key's; otherwise it stays sparse.
  - The roundtrip lemma `instRow (abs rows) ins cb = rows` makes the closed form exact.
  - This needs a CS field with the per-op row and fresh counts, to delimit blocks, plus F-9's
    materialisation.
- **F-11 (minor):** in `sizes.py`, "walks as implemented 2 × 15 ms" counts the walk twice, since
  one `walkAB` run gives both `Â₀` and `B̂₀`. The 3.12 row model leaves out the `walkAB`
  template's rows (§4).
- **D-1:** the node section moved from `FRVIRTplEval` to `FRVIRTplFast` under the same names.
  `FRVerifierImpl` and `FRNodeCircuit` changed one import line each.
- **D-2:** `walkA`/`walkB` were removed rather than kept, because nothing references them after
  `finLc`'s change.
- **D-3:** one evaluation pass per matrix, not a triple-valued pass. The three matrices share the
  tables, the keys' local parts and the instances' high factors. A triple pass would share the
  inputs' values too; how many inputs appear in more than one matrix was not measured.

## 7. Requests and notes

- **S-0 / S-F (`finE` (iv)):** add `evalM`'s call at `(r_E2, r′)`. Better still, give the op
  `κ_E` and return `Ã + κB̃ + κ²C̃` as one F value. That removes two of the three products per
  row and per instance group in the evaluator.
- **Integration pass:** the working tree's `FRNodeLayout` (an L-circ module) has
  `chainN = 23,225` and `lBase = 47,616`. `FRVIRFinalsSG`'s `decide` on `lBase`'s bits (line
  1876) fails against it.
  - Merging with S-E4: S-E4's `mRowModel` block was applied in place and keeps those edits.
    `mRows_le` and `usedBlocks_le` hold in both versions.
  - S-E4's build tree uses HEAD's `FRNodeLayout` with the new `mRowModel`.
- **Orchestrator:**
  - `FR.lean` may import `FRVIRTplFast` (it comes in through `FRVerifierImpl` already).
  - Next stage (S-E5, L-circ): F-9's materialisation, then block keys and aligned allocation by
    the route of §6, then the import classes. Then re-measure `evalM` and V with `finE`'s call.
- **Probes** (outside the entry):
  - `probe/fr-e4kill/E4Kill.lean`: the kill test.
  - `E4Eval.lean`: `evalMT` on the real plan, with `parts` and `check`.
  - `E4Walk.lean`: the walk's split and the specialisation test.
  - `ax/AxE4.lean`: the axiom audit.
  - `probe/fr-vtime/VTime.lean`: updated for `walkAB` and the plan.
