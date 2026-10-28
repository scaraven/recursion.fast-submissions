# S-E5 (track L-circ): RESULT — templating the node circuit's skeleton

Stage S-E5 of `submissions/flock-recursive`, 2026-10-28, branch `v4/flock-recursive`
(uncommitted). Started on HEAD `5fc7d3b` (INT-1, revision 3.12); the other tracks' modules were
taken from HEAD at each snapshot (last: `1ad8fed`, revision 3.13 committed, INT-2 in progress).
Build tree `logs/fr-build-e5` (`snap.sh`: HEAD's modules, L-circ's symlinked to the worktree; the
probes are `lean_exe`s of the same tree). Every build and probe ran in the 16 GB scope; probes on
one core (`taskset -c 21`, `-c 9`). Logs in `logs/S-E5/`; journal `S-E5-JOURNAL.md`.

**Status: the target is met.**

- **V (N30, `vtime v N`, warm `runSeq`), with `finE`'s `evalM`: 204.9 ms best, 208.3–210.7 ms
  median** over three runs of 9 (`vtime-N-final-{1,2,3}.log`). The baseline at HEAD was
  685.7 / 709.7 ms (`vtime-N-base.log`). The target is ≤ 230 ms VM; the VM-equivalent cap is
  ≈ 264 ms.
- **`evalM` (`TEval.evalMT`): 50.1 ms best, 51.5 ms median** (S-E4: 545 ms). Inside V's
  per-op profile it takes 55.9 ms (`prof-N-1.log`).
- **`evalL` (new `TEval.evalLT`, revision 3.13's 23-coordinate point): 4.4 ms.** The sparse
  `FRVIREval.evalRows` on the real `Layout.lRows` takes 481 ms. `implC` still uses the sparse one,
  and the probe passes `lRows = []`; wiring `evalLT` in adds ≈ 4.5 ms to V (§7, request 1).
- **`lake build FR` is green**: 2,320 jobs, 2 min 54 s (`build-FR-2.log`).
- **Source rule**: 115 files, 0 findings.
- **Axioms**: the 42 audited statements use only `propext`, `Classical.choice` and `Quot.sound`,
  or a subset (`axioms.log`).
- The evaluator's API is unchanged: `TEval.Plan`, `planOf`, `evalMT`, `evalMS`, and
  `evalMT_eq : evalMT pl τ σ = evalMS pl τ σ` with S-E3's statement. `FRVerifierImpl` and
  `FRNodeCircuit` build unchanged.

## 1. What was built

Code lines by `.contract/scripts/loc.py`, code (total), HEAD `5fc7d3b` → now.

| Module | code | Content |
|---|---|---|
| `FRVIRCompile` | 862 (1,098) → **1,000 (1,274)** | See "Compiler" below. **FR-R3′: 1,000 ≤ 1,000 (no margin left).** |
| `FRVIRTplPlan` (new, L-circ) | 223 (339) | The plan's **search** (untrusted; see "Plan search" below) |
| `FRVIRTplFast` | 356 (522) → 662 (912) | The **evaluator**, rewritten; see "Evaluator" below |
| `FRVIRTplCore` | 179 → 188 | `Gate.mulAdd a b c` (one local `a·b + c`, one row); `eqn_of_rows` covers it. `Row`, `RowT` and `Wire` derive `DecidableEq`/`Hashable`. |
| `FRVIRTplLag` | 383 → 417 | `tplDotKF` on `mulAdd` (2n rows; outputs are two locals instead of `n`-term sums); `tplDotKF_ok` re-proved (cases `n`); `tplDotKF_nlocs = 2n` |
| `FRVIRTplExt` | 300 → 304 | `dotKF`'s column cells in the instance's own region (`cb + 2n + b`, not skeleton cells); `cregion` (the region's bits); `mkLay` uses `cregion` and `CS.nrows`. `alignUp` moved to `FRVIRCompile`. |
| `FRVIRMux` | 69 → 89 | S-E5's controls (§5) |
| `FRNodeLayout` | 158 → 157 | `mRowModel` on S-E5's measured counts (§4); only this block was edited, INT-2's 3.13 constants are kept |

**Compiler** (`FRVIRCompile`):

- **F-9, without extra rows.**
  - `muxOut`'s row is `g·(y − x) = v − x`, with `v` fresh and the output `v`. S-E4 proposed
    `+2` rows per step; this needs none.
  - `cur` no longer grows along a Merkle path.
  - `muxOut_sound` re-proved.
- **Assertions off for every kind** (`offK`) emit no row. Their flag is `true` for any operand
  value. This removes 11.6 k rows per slot (the Merkle steps that every kind has).
- **Alignment hook.**
  - `CS.nrows` keeps the row count.
  - `CS.align` adds empty rows and skips cells, which is sound for any argument.
  - `alignOf op rest` is a lookahead hint: a Merkle position (`idx`, sized `4s + 10` rows and
    `9s + 8` cells for `s` steps) and a Horner block (the first of 7 `tensorW` followed by `mulK`).
  - `compileFromX` is now structural recursion; `compileFromX_cons` holds by `rfl`.
  - `compileFromX_mono`, `compileFromX_sound` and `compile_sound` are re-proved; their
    statements are unchanged.
- **Tensor `eqTable`** for 8 or more coordinates (`eqTensor`):
  - `eq(lo) ⊗ eq(hi)`, `eqRows` each, then padding;
  - the products `prodRows` in aligned blocks of `2^p` rows, one block per `hi` index;
  - **`eqTensor_sound`** via `foldl_eqStep_tensor`, the tensor identity of `eqTab` over a
    concatenation, and `prodRows_sound`.

**Plan search** (`FRVIRTplPlan`, untrusted):

- **Keys and pieces.** A key is raw template rows with bits `A`/`B` (`Key.ok n`). A piece is
  either sparse rows or an instance `(key, xh, ch, own)` (`Piece.rows` via `instIR`). `eqL` is a
  tail-recursive list equality, `eqL_eq` its lemma.
- **Skeleton blocks.** `segsGo` replays the compile: a block runs from an aligned op to its
  closing `assertEq`, and the tensor's product blocks are added. `absRows` abstracts a block over
  its window: cells inside become locals, every other cell is an input.
- **Template instances.** The S-E3 instances (`tinPP`) are taken as they are.
- **Grouping** (`groupPPs`), by template. An input is:
  - local when it is one cell at a fixed offset in every window;
  - a **partition input** when it takes at most 16 values per slot and every part keeps at least
    4 members. The group is split by these values, so each part shares them;
  - otherwise own.
- `listPPs` does the same for an arbitrary row list (L).

**Evaluator** (`FRVIRTplFast`):

- **Closed form.** `tplR_mle` is `tpl_mle` for raw rows, any `A`, and `B` covering the locals.
- **Inputs.** `denseIT`/`denseIT_sum` give one coefficient per input. `sum_split` splits the
  inputs into shared and own.
- **High factors.** `hiTabs`/`hfac`/`hfac_eq` give the high `eq` factors by tables, one product
  each. Only the bits some key has are built.
- **Per-key preparation.** `kprepT`, `kprep` and `kprep3` (each key's two tables built once for
  the three matrices).
- **Pieces.**
  - `ppv` is a piece's value for one matrix; **`ppv_eq`** states it equals the rows' sparse value.
  - `rowsValI_filter`: padding rows add nothing.
  - **`slotV_eq`** lifts `ppv_eq` to a slot.
- **One pass for the three matrices** (`ppv3`, `slotV3`, **`slotV3_eq`**). The high factors, the
  own and shared inputs' `E` values and the sparse rows' row factor are computed once for `A`, `B`
  and `C`.
- **The plan.** `Plan` (with `ok`: the pieces' rows **are** `slotIRows`), `mkPlanOf`, and
  `mkPlan`, which checks the search's result once and falls back to one sparse piece per slot.
  `planOf`, `nodeIRows`, `nodeV`/`nodeV_eq`, `nodeV3`/`nodeV3_eq`, `evalMT`, `evalMS`,
  **`evalMT_eq`**.
- **`evalL`.** `LPlan`/`planL` with 64-row blocks; `evalLT`; **`evalLT_eq : evalLT pl τ σ =
  Eval.evalRowsSpec 15 23 pl.rows τ σ`**.
- **Deleted.** S-E4's flat evaluator (`GInst`, `FSlot`, `pcache`, …) and **`evalMKT`**, as
  INT-1 asked. The axiom probe `probe/fr-e4kill/ax/AxE4.lean` no longer lists them.

Soundness needs nothing new beyond the compiler lemmas above. The renaming route of S-E4 §6 was
not needed: the compiler aligns, so `nodeIRows` keeps its positional shape. The evaluator's
correctness rests only on `tplR_mle` and the generic lemmas, because the plan is checked.

## 2. Measurements (VM, one core, 16 GB scope)

| What | Value | Log |
|---|---|---|
| V (N30), HEAD baseline | 685.7 ms best, 709.7 ms median | `vtime-N-base.log` |
| **V (N30), S-E5** | **204.9 / 205.1 / 206.1 ms best, 209.2 / 208.3 / 210.7 ms median**; `traceDigestF` 12.9–15.3 ms | `vtime-N-final-*.log` |
| `evalMT` | **50.1 ms best, 51.5 ms median** of 7; equal to the plain sparse sum over `nodeIRows` (`check`) | `eval-final.log` |
| ... its parts | tables 3.3 ms; key preparations (39 keys, 25 k entries, three matrices) 12.2 ms; shared values of the two slots 14.5 ms; the pieces of both slots 22 ms | `eval-final.log` |
| `evalLT` (L's 16,440 rows, `σ` 23 coordinates) | **4.4–4.7 ms**; equal to `Eval.evalLImpl` (481 ms) | `eval-final.log` |
| `planOf` | 4.9 s, once per process (S-E4: 1.9 s): six compile passes, the search, the check | `eval-final.log`, `plan-prof-1.log` |
| the plan, per slot | 3,721 pieces: 2,718 instances of 39 keys (shared by the slots), own inputs 1,780 cells; sparse 4,167 non-empty rows (24 k entries) | `eval-final.log`, `eval-3.log` |
| slot 0's skeleton | 139,137 rows (≈ 29.5 k empty padding rows), 201,610 cells | `lay-2.log` |
| slot 0's rows, templates included | end at 361,856 (S-E4: 310,656) | `lay-2.log` |

The evaluation's history (each step measured): flat S-E4 545 ms → blocks and plan 165 ms
(`eval-1.log`) → partition inputs 121 ms → no singleton parts 91 ms (`eval-3.log`) → triple pass
54 ms (`eval-4.log`) → shared key tables, built-only partial tables 48–52 ms (`eval-5.log`) →
final 50.1 ms. V after the plan: 212.5 ms (`vtime-N-2-2.log`) → 204.9 ms.

**Build and kernel times** (sequential `lake env lean -DElab.async=false --profile`, one core;
`profile-*.log`):

| Module | wall | tactic exec. | simp | type checking (kernel) | peak RSS |
|---|---|---|---|---|---|
| `FRVIRCompile` | 32.1 s | 8.59 s | 7.31 s | 1.19 s | 2.7 GB |
| `FRVIRMux` | 16.5 s | 5.64 s | 0.16 s | 3.72 s (the `decide` controls) | 2.7 GB |
| `FRVIRTplCore` | 8.2 s | 0.17 s | 0.35 s | 0.15 s | 2.6 GB |
| `FRVIRTplLag` | 12.8 s | 2.96 s | 1.02 s | 0.69 s | 2.7 GB |
| `FRVIRTplExt` | 8.8 s | 1.03 s | 0.72 s | 0.16 s | 2.7 GB |
| `FRVIRTplPlan` | 7.5 s | 0.07 s | 0.03 s | 0.06 s | 2.7 GB |
| `FRVIRTplFast` | 11.9 s | 1.41 s | 1.10 s | 0.43 s | 2.8 GB |

Each wall time includes about 3.6 s of import.

## 3. Statements (axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}; `axioms.log`)

- Compiler: `compile_sound`, `compileX_sound`, `compileFromX_sound`, `opOut_sound`,
  `muxOut_sound`, `eqTensor_sound`, `foldl_eqStep_tensor`, `prodRows_sound`, `compileT_sound`,
  `tplExt_ok`.
- Templates: `tplDotKF_ok`, `Gate.eqn_of_rows`, `Tpl.eqns_of_rows`.
- Evaluator: `tplR_mle`, `denseIT_sum`, `sum_split`, `hfac_eq`, `rowsValI_filter`, `eqL_eq`,
  `ppv_eq`, `slotV_eq`, `slotV3_eq`, `nodeV_eq`, `nodeV3_eq`, **`evalMT_eq`**, **`evalLT_eq`**.
- Node: `slot_sound`, `node_m_sound`, `node_sound`.
- Verifier: `implCWith_meets`, `implC_meets`, `implCWith_implT`.
- The controls of §5.

No statement changed. `compile_sound`, `compileT_sound`, `node_sound` and `evalMT_eq` keep their
S-E2/S-E3 statements.

## 4. `mRowModel` (`FRNodeLayout`, per slot)

| Part | Rows |
|---|---|
| skeleton (measured, alignment padding included) | 139,137 |
| emitted templates, aligned (measured; includes `Φ`'s claim 5, which S-E4's model listed apart as 17,152) | 222,719 |
| templates still missing (changes 17) | 118,639 |
| `walkAB` | 65,536 |
| the child's `evalM` replay | 422,912 |

- **Total: 968,943 per slot ≤ 2^20 (1.08×); 1,937,886 per node ≤ 2^21.**
- Used blocks: 62,744 with HEAD's H end (47,480), 62,586 with INT-2's 3.13 end (47,322); both
  ≤ 65,536.
- `mRows_le` and `usedBlocks_le` build (my tree, HEAD's file with this block).
- Revision 3.13's `J_z = 4` removes 128 `phiRS` instances (−32,768 aligned rows) and `rsWeight`'s
  fifth claim (−11,400): **≈ 924.8 k per slot (1.13×)** once INT-2's finals land.

Where the margin went, against S-E4's 310,656 emitted rows per slot (now 361,856):

- +32.8 k: `phiRS` 640 instances under 3.12 (claim 5), each 134 rows in 256;
- +18.5 k: skeleton padding (29.5 k) less the dropped assertion rows (11.6 k);
- −0.0 k: `dotKF` keeps 128/32 rows thanks to `mulAdd`. My first materialisation used two extra
  rows and pushed them to 256/64: +56 k, undone.

## 5. Controls

New controls, in `FRVIRMux`, by `decide` on small programs:

| Control | Shows |
|---|---|
| `sel_rows_honest` / `sel_rows_reject` | the materialised select's row holds when the output cell holds the selected value, and fails on the other operand |
| `off_rows_none` / `on_rows_reject` | an assertion off for every kind has no row; the same assertion on for a kind is a live row that rejects a nonzero value |
| `prod_rows_honest` / `prod_rows_reject` | the tensor's product rows (2 × 2) hold for the honest products and reject a wrong one |

A `decide` on the whole 8-coordinate tensor (288 rows) exceeded the elaborator's budget, and the
track rules say not to raise it. Instead, `eqTensor_sound` is proved for every size, and its two
table halves are `eqRows`, whose rows S-E2's controls exercise.

Unchanged and building: `kindProg_rows_N`/`_L`, `three_hot_*`, `hotN_*`, `FRVIRTplControls`
(`mul_rows_*`, `inv_rows_*`), `pubCells_*`, `ind_wots`.

Every new evaluator definition is proved equal to an unchanged specification (`evalMT_eq`,
`evalLT_eq`). The probes check the values numerically too (`check`: equal to the sparse sum on
random points).

## 6. Deviations, findings, open items

- **D-1 (route).** Instead of S-E4's renaming of cells:
  - the compiler aligns (empty rows, skipped cells);
  - the evaluator's plan is a checked search (`mkPlan`'s `eqL` over `slotIRows`).

  Correctness then needs no lemma about the search, the abstraction or the alignment; a wrong
  search costs time, not soundness. The "roundtrip lemma" is replaced by that check.
- **D-2 (import classes).**
  - Not written: `regImport_mle` and `run_mle`.
  - Used instead: the classes **local** (in the instance's window: folded into the template),
    **shared** (constant per slot and part, evaluated once per slot) and **own**. The partition
    makes the per-level `eqTableK` tables of `dotKF` shared.
  - Measured result: 1,780 own cells per slot, ≈ 1 % of the evaluation. The regular and run
    classes are therefore not needed for the target.
- **D-3 (κ_E, step 3).**
  - Not done as an op change. The coordinator asked to keep the evaluator's API stable while
    INT-2 rewrites `finE` for 3.13.
  - Done instead, inside `evalMT`: the one-pass evaluation of the three matrices (`slotV3`). It
    shares everything a κ-combined pass would, except the 3 → 1 products per input and per key
    entry.
  - A κ-combined `evalM` op is a remaining lever, an estimated ≈ 10–15 ms, not measured.
- **D-4.** F-9 is resolved with zero extra rows (the merged mux row). S-E4 had budgeted +15 k rows
  per slot for it.
- **D-5.** `dotKF`'s template changed (`mulAdd`), and its column cells moved into its region.
  This is a circuit change for P2 (§7).
- **F-12 (row budget).** The skeleton's alignment padding costs ≈ 29.5 k rows per slot. The
  levers, not done:
  - split Horner's 383 rows into 256 + 128 (−16 k);
  - finer position blocks (≈ −8 k);
  - `phiRS` 134 rows in 256 (≈ −62 k at 512 instances): two instances per 256-row block, or a
    132-row template.
- **F-13 (`targetS` forms).**
  - `lagrangeS` reads `targetS`'s 64 output forms, 32,832 cells in all. This is 14.5 ms of
    `evalMT` (shared values, two slots).
  - Revision 3.13 replaces the node's `targetS` (`targetSNode`, S-C's spec pending). Its
    template should **materialise its outputs**, or build them as running sums, so they are not
    long linear forms.
- **F-14.** `planOf` takes 4.9 s once per process (six compile passes, the search, the check).
  The harness times warm checks, so this is outside the timed check. `segsGo`'s replay could be
  folded into the compile if needed.
- **Pending (revision 3.13, coordinator's note).**
  - `tplTargetSNode` (≈ 10 k rows) and `tplLinkW` (≈ 2,500 rows per family) wait for S-C's specs
    (`targetSNodeS`, `linkWS`).
  - `evalL` at 23 coordinates is done (`evalLT`), but is not wired into `implC` yet
    (request 1).
  - V must be re-measured once INT-2 lands.

## 7. Requests

1. **L-cert / INT-2 (`FRVerifierImpl`, mechanical):**
   - `implCWith` takes `TEval.LPlan`, built once by `implC fin lRows _ := implCWith (planOf fin)
     (TEval.planL lRows)`;
   - `evalL := TEval.evalLT lp`;
   - `Meets`' `evalL` conjunct is `TEval.evalLT_eq lp` (the spec `Eval.evalRowsSpec 15 23 lRows`
     is unchanged, `lp.rows = lRows` by construction).
2. **Orchestrator:** `FR.lean` may import `FRVIRTplPlan`. It already comes in through
   `FRVerifierImpl`.
3. **Blueprint (orchestrator):**
   - A.11 / §4.3: the row model (968,943 per slot, 1.08× under 3.12; ≈ 924.8 k under 3.13), and
     the evaluation route (aligned blocks, a checked plan, local/shared/own classes, one pass for
     the three matrices);
   - `T_V`: V ≈ 205 ms VM plus `evalL` ≈ 4.5 ms;
   - FR-R3′: `FRVIRCompile` is at its 1,000-line budget.
4. **P2 (prover), circuit changes in the node dump `logs/S-E5/nodedump/`** (169 MB; checksums in
   `logs/S-E5/nodedump.sha256`; made by `logs/fr-build-e5/probe/NodeDumpT.lean`):
   - mux rows `g·(y − x) = v − x`, with `v` the output cell;
   - no rows for assertions off for every kind;
   - empty padding rows and skipped cells before Merkle positions and Horner blocks;
   - `eqTable`s of 8 or more coordinates as a tensor (`colW`, the four `κ_c` tables);
   - `dotKF`'s last two rows are `c·w = out − Σ p` (outputs at locals `2n−2`, `2n−1`), its
     column cells at `cb + 2n + b`;
   - the template regions' bits are `cregion`.

   Per slot: 282,319 indexed rows, 1,529 instances, 27,577 import registers, 871 auxiliary
   imports, 98 foreign.
5. **S-G:** `Layout.nodeRows` (`compileMux`) now has the padding rows and the shapes above. Its
   statements are parametric, and `FR` builds. The rows are 2 × 139,137 ≤ 2^21.

## 8. Probes and tools (outside the entry)

`logs/fr-build-e5/probe/`:

| Probe | What it does |
|---|---|
| `E5Stat` | skeleton statistics by op and context |
| `E5Eval` | plan shape, `evalMT` and `evalLT` timing, checks against the sparse sums, stage breakdown |
| `E5Plan` | `planOf`'s stages |
| `E5Lay` | the template layout and its waste |
| `VTime` | V, updated for the new `Plan` |
| `NodeDumpT` | the P2 dump |

Axiom audit: `logs/fr-build-e5/ax/AxE5.lean`.
