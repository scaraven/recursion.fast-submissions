# S-E6 (track L-circ): RESULT

Stage S-E6 of `submissions/flock-recursive`, 2026-10-28, branch `v4/flock-recursive`. Nothing is
committed. The base is HEAD `ce8cdc7` (INT-2, revision 3.13); the last snapshot was taken at
`1fe52f4`.

- Build tree: `logs/fr-build-e6`. Logs are in `logs/S-E6/`; the journal is `S-E6-JOURNAL.md`.
- Every run used the 16 GB scope, probes on one idle core.
- S-CN's `FRNodeTarget`/`FRVerifierImplNode` and the `FRX*` modules were not touched.

## Status by item

| Item | State |
|---|---|
| 1. `evalLT` in `implC`; V | **Done.** V = **228.9 ms best, 234.2 ms median** with the full 3.13 finals and the real L rows. **Final state (item 3's templates, `targetSNodeI` wired, HEAD `1fe52f4`): 229.3 ms best, 237.3 ms median** (§2). |
| 2. Dump at 3.13 | **Done**, `logs/S-E6/nodedump/`. It is the dump of the circuit as it now stands (after item 3), so it matches the source tree. |
| 3. Replay templates | **Partly.** **`tensorW`** (882 of 1,627 ops) and **`rowW`** are templates. `packFK` is tracked when its lists agree, and `kindInd` is not used by `gen`. **Not done:** `walkAB`, `rsWeight`, `shiftTarget`, and the other 745 `tensorW` (§3). **The child `evalM`/`evalL` replay is blocked on a design question** (§4). Slots for the node `targetS`/`linkW` (S-CN) are left in the row model. |
| 4. H-side assembly | **Partly.** The per-generator row counts for RowsFit are measured (§5), and `mRowModel` is updated without `rsWeight`'s claim 5. **Not done:** the pack map, the `input w` alias, the `SigOk`/format facts, the W-kind children, `node_complete`. |
| 5. Re-dump with every register bound | **Not reached** (27,350 import registers per slot are left, almost all trace cells waiting for the pack map). The rows per slot and per node are in §5. |

## 1. What was built

Code lines by `loc.py`, code (total), HEAD → now.

| Module | Code lines | Change |
|---|---|---|
| `FRVIRCompile` | 1,000 → **779 (1,019)** | split (FR-R3′); `packFK` with equal per-kind lists is `packF` of the list (`opOut` and its `opOut_sound` case) |
| `FRVIRCompileSound` (new) | 240 (287) | the program section moved from `FRVIRCompile` unchanged: `Inv`, `ExtOk`, the alignment lemmas, `compileFromX_mono`/`_sound`, `compile_sound`, `compileX_sound`. `FRVIRMux` and `FRVIRTplExt` import it. |
| `FRVIRTplRep` (new) | 117 (163) | see below |
| `FRVIRTplExt` | 304 → 352 | `tplOf`/`tplExt` cases for `.tensorW n` (with `n ≤ 20`; `j`'s bits are an `AuxK.bits 20` import in the instance's region) and `.rowW n`; `ImplT.tensorW`/`.rowW`; the `tplExt_ok` cases; `cregion (.tensorW n)`; `mkLay` changes below |
| `FRVIRTplPlan` | 223 → 231 | a template of more than `2^12` rows is cut into 64-row chunks, each abstracted over its 64 written cells (one key; the shared inputs once per slot) |
| `FRVIRTplFast` | 662 → 664 | `planL_rows` |
| `FRVerifierImpl` | 82 → 82 | `implCWith pl lp` (`evalL := TEval.evalLT lp`); `implC` builds `TEval.planL lRows` once; `implCWith_meets` via `evalLT_eq` + `planL_rows`; the specification is unchanged |
| `FRNodeLayout` | 157 → 160 | `mRowModel` on S-E6's counts (§5) |

`FRVIRTplRep` holds:

- **`tplTensorW n`**: `5n` rows. `Ŵ_v(D[j])` is a linear form in `j`'s bits, so each factor is two
  `K × F` gates; then the product (`mulKG`). The proof is **`tplTensorW_ok`**, through
  `twChain_ev`.
- **`tplRowW = rowWG (2^14)`**: the products `L_{k mod 64}·E_{⌊k/64⌋}` first (row `k` = local `k`),
  then `lagG` and `eqTblG`. The proofs are **`rowWG_ev`** and **`tplRowW_ok`**.

`mkLay` (in `FRVIRTplExt`):

- a template of more than `2^12` rows is aligned to 64 rows;
- the next group starts after the last instance's rows (no padding after it);
- soundness and the evaluator do not depend on the layout.

**Statements.** Of the 51 audited (`axioms.log`; `targetSNode_meets` added), none uses an axiom beyond `propext`,
`Classical.choice` and `Quot.sound`. They include S-E5's 42, `tplTensorW_ok`, `twChain_ev`,
`tplRowW_ok`, `rowWG_ev`, `planL_rows`, `evalLT_eq`, `mRows_le` and `usedBlocks_le`. No
statement changed, except `implCWith`'s second argument (an `LPlan`), which follows from item 1.

**Checks.**

- `lake build FR`: green, 2,322 jobs, 2 min 30 s (`build-FR-1.log`).
- Source rule: 122 files, 0 findings.
- The evaluator's plan check passes, and `evalMT` equals the sparse sum (`eval-3.log`).

## 2. V (N30, `vtime v N`, warm `runSeq`, VM, one idle core)

| State | best | median | Log |
|---|---|---|---|
| S-E5 (3.12, `finPf` pending, no L rows) | 204.9 ms | 208.3 ms | `logs/S-E5/vtime-N-final-*` |
| **item 1**: 3.13, full `finPf`, `evalLT` on `Layout.lRows` | **228.9 / 230.4 / 229.3 ms** | 234.2–238.6 ms | `vtime-N-{4,5,6}.log` |
| after item 3 (`tensorW`, `rowW` templates; snapshot `ce8cdc7`) | 243.8 / 247.4 / 248.9 ms | 245.9–254.2 ms | `vtime-N-c{1,2,3}.log` |
| **final**: plus `targetS` by kind (S-CN's `targetSNodeI` at a node kind), snapshot `1fe52f4` | **229.3 / 231.8 / 234.9 ms** | 237.3–249.9 ms | `vtime-N-d{1,2,3}.log` |

- `traceDigestF` stayed at 12.4–14.1 ms throughout, so the core was quiet.
- Per-op profile at item 1 (`prof-N-1.log`): `evalM` 62 ms, `dotKF` 28 ms, `rsWeight` 7.6 ms,
  `evalL` 4.9 ms.
- `evalMT` after item 3: 70.6 ms best (`eval-3.log`); final 59.5 ms best (`eval-4.log`). Before the 64-row chunking it was 114 ms,
  and V 295 ms (`eval-2.log`, `vtime-N-b*.log`).
- Between the item-3 and final rows, two things changed at once: the leaf `targetS` template
  became an import, and the snapshot moved to `1fe52f4` (S-CN's modules). I did not separate
  their effects on V.
- V is now at about S-E5's 230 ms VM target, and **under the ≈ 264 ms VM cap (1.13×)**. Every newly
  bound template adds its rows to `evalM`'s work. The rows still to bind (`rsWeight` 45.6 k,
  `walkAB` 65.5 k, the replay 423 k) would add far more (§4).

## 3. Templates not done

- **`walkAB`** (one op; A.11: `colW = eqTable(r_k)` 2^14 rows, `rowW′` = `maskRows`, then 2^14
  products per walk). The rows are the lincheck-replay class. Not started.
- **`rsWeight`** (one op).
  - The point lists depend on the kind: L and P have 3 points, N has 4, from different registers.
  - The template has to mux the 4 points by the selector cells, then compute 4 claims, the fourth
    gated to N.
  - That is ≈ 45.6 k rows (A.11's `wEvalC`: 128 squarings of a 23-coordinate K point and 22
    `eq` products per claim).
  - Not started.
- **`shiftTarget`** (one op). `digestMle` reads `bnd`'s digest **bits**, but `bnd` is two F halves
  per digest. It needs a bit decomposition: 256 Booleanity rows plus the recomposition, or the
  digests' L bits as an auxiliary import.
- **`finPf`'s 745 `tensorW`**. Their operand is `keep` of two arrays of different lengths per kind,
  so its type is not fixed and the compiler leaves it untracked. A fix: zero-pad to the longer
  length, since `tensorWI`'s factors at zero coordinates are 1. Any other reader of those arrays
  would also have to tolerate the padding.
- **`maskRows`** stays an import, because its `kindW` operand is a `packFK` whose lists differ by
  kind.

## 4. The child `evalM`/`evalL` replay: a design blocker (for the orchestrator)

The node circuit's M matrix contains the replay rows `R`, the template that evaluates the child's
`evalM` at `(r_E2, r′)`. The child is a node with the same circuit, so the matrix `R` evaluates
**contains `R` itself**. Two consequences:

1. **Structure.** `R`'s rows follow the plan of `M`, which contains `R`'s rows. So `R` is defined
   by a fixed point. A.11 and changes 17 size `R` at 422,912 rows as if the child's matrix were
   given.
2. **Size and time.** Evaluating `MLE(M)` includes `MLE(R)`. If `R`'s rows are as irregular as
   `evalMT`'s products (the 423 k estimate is about one row per product), then evaluating them
   costs about `|R|` products. That gives `|R| ≥ |M \ R| + |R|`, which has no solution, and `T_V`
   would grow the same way.

It can only work if `R`'s own rows have an MLE computable in **sublinear** size by `R` itself.
That means a uniform layout: strided product rows `⟨cell(a + s·i), cell(b + t·i), cell(c + i)⟩`,
whose MLE is `O(log)` per stride class, as for the tensor and eq-tree keys. `R` would then
evaluate `M \ R` by the plan and `R` by its closed form.

That is a redesign of the replay (and of A.11's figure). Options:

- (a) such a uniform replay layout;
- (b) the blueprint's rejected preprocessing commitment, changes 17 (d);
- (c) the child's `evalM` claim deferred to the parent's own E-phase, i.e. a batched lincheck
  across levels.

**I did not start (a) without a ruling.**

`evalL`'s replay has no such loop (L's rows are fixed, 16,440 Booleanity rows). As a template it
is the uniform chunked evaluation of `evalLT`; it was not written.

## 5. Rows (RowsFit, `mRowModel`)

**Per generator, slot 0** (`rows-per-generator.log`, probe `E6Rows`):

| Generator | Rows | Padding |
|---|---|---|
| PIOP phases: seed 5, stmt 4, Z3 80, L2 42, S2 86, Lr2 60, E2 84, E4 92, P1.0–4 48 + 4 × 32 | 629 | — |
| queries Q0 … Q4 | 15,660 / 8,900 / 6,090 / 4,488 / 3,780 | 2,901 / 2,520 / 3,214 / 3,984 / 280 |
| Pf | 56 | — |
| finals + `accept` | 74,343 | 16,243 |
| **skeleton** | **143,088 = 113,946 + 29,142 padding** | |

Template instances, before padding: 174,110 rows. By key:

- `phiRS` 512 × 134, aligned in 131,072;
- `dotKF` 290 × 128 and 581 × 32;
- `tensorW` 882 × 35;
- `rowW` 1 × 16,829;
- `lagrangeS` 760;
- `eqTableK` 189 + 4 × 45 + 381;
- `targetS` 255, `eqZ` 254, `eqPt` 30 + 42.

**RowsFit for S-G (`Layout.nodeRows`, `compileMux` without templates).**

- The rows are the same skeleton: 2 × 143,088 = 286,176 ≤ 2^21.
- The largest cell index is below `slotBase 1 + 2^20` < 2^23.
- These are **measured, not lemmas**. A closed-form `RowsFit` still needs per-generator count
  lemmas (S-E2's open D-2). The table above gives the values those lemmas must reach.

**`mRowModel`** (per slot):

| Part | Rows |
|---|---|
| measured: skeleton + every emitted template in its aligned layout (`lay-3.log`) | 406,016 |
| `rsWeight` (4 claims; claim 5 dropped, INT-2's note) | 45,604 |
| `walkAB` | 65,536 |
| `shiftTarget` | 100 |
| `finPf`'s 745 `tensorW` | 47,680 |
| node `targetS` (S-CN) | 10,000 |
| node `linkW` (S-CN) | 20,000 |
| the replay (§4: questionable) | 422,912 |

- **Total 1,017,848 per slot ≤ 2^20 (1.03×); 2,035,696 per node ≤ 2^21 (1.03×).**
- Blocks: 47,322 + 124 + 15,905 = **63,351 ≤ 65,536 (1.03×)**.
- `mRows_le` and `usedBlocks_le` build.
- The margin is thin. The levers are:
  - `phiRS` 134 rows in 256-row regions: −62 k;
  - the skeleton padding: up to −29 k;
  - the replay design (§4).

## 6. For P2

- **The dump `logs/S-E6/nodedump/`** (213 MB; `logs/S-E6/nodedump.sha256`; the format is S-E3's,
  produced by `logs/fr-build-e6/probe/NodeDumpT.lean` with `fins = Impl.finC finPf`, at HEAD
  `1fe52f4`):
  - 316,943 indexed rows per slot;
  - 2,284 template instances (the new keys `tensorW 7` and `rowW 8`; the leaf `targetS`
    template is gone);
  - 27,351 import registers;
  - 1,753 auxiliary imports (`dotKF` columns, and now `tensorW`'s 20 bits of `j` at
    `cb + 5n + i`);
  - 76 foreign flags.
- **Circuit changes against S-E5's dump:**
  - `tensorW` and `rowW` are template instances;
  - `packFK` registers with equal per-kind lists are tracked;
  - the layout has 64-row alignment for templates of more than `2^12` rows, and no padding after a
    group's last instance.
- **Still imports** (P2 writes their values): the trace cells (which wait for the pack map),
  `walkAB`, `rsWeight`, `shiftTarget`, `evalM`, `evalL`, `maskRows`, 745 `tensorW`, `targetS`
  (every kind now) and `linkW`.

## 6a. S-CN's heads-up (revision 3.14 pending)

- **The WM mirror map.**
  - No L-circ module reads A.6's mirror addresses: `FRVIRCompile*`, `FRVIRMux`, `FRVIRTpl*`,
    `FRNodeCircuit` and `FRVerifierImpl` do not mention `wmBase`/`wmSlot`/WM.
  - Only `FRNodeLayout` defines `wmBase`/`wmSlot`. They are used by others (`nodeLayout`, S-G),
    and I did not change them.
  - A future `tplLinkW` will take the mirror addresses from one function, to be fixed by the 3.14
    ruling.
- **`targetSNodeI` is wired by `κ.isNode`.**
  - `implC.targetS κ = if κ.isNode then NodeI.targetSNodeI else targetSLeafI`; `specC` uses
    `NodeT.targetSNodeS`; `Meets` via `targetSNode_meets`.
  - The leaf-only `targetS` template, and `ImplT.targetS`, are removed. A template must mirror the
    implementation at every kind, so `targetS` is an import until `tplTargetSNode`, which must cover
    both kinds or be gated.
- **Open:**
  - `linkW` is still `0` in `implC`. Its wiring needs `θ` and `r_pos` (S-CN §6, `finSh`'s
    registers), which waits for 3.14.
  - `tplLinkW` should template `linkWAllI`, the shared op of 8 families. A.11's 2,500 rows per
    family is low: S-CN measures ≈ 5.6 k products each for `x` and `j`. So `mRowModel`'s 20,000
    for `linkW` is likely too small.

## 7. Requests and open questions

1. **Orchestrator: §4's design question** (the replay's self-inclusion). It blocks item 3's first
   entry and bears on `T_V` and the row budget.
2. **Orchestrator: `FR.lean`** may import `FRVIRCompileSound`, `FRVIRTplRep` and `FRVIRTplPlan`.
   They are in the build already, through `FRVerifierImpl`.
3. **Next for S-E** (in order, if §4 is ruled):
   - `rsWeight` (kind-muxed points);
   - `walkAB`;
   - `shiftTarget` (the bits of `bnd`);
   - the zero-padded `keep` for `finPf`'s `tensorW`;
   - the pack map and the H-side `node_sound`;
   - the replay.
4. **`T_V`:** binding templates moves `evalM` up (62 → 70.6 ms here). The blueprint's T_V model
   should count the evaluation of every bound template's rows, not only the skeleton.
