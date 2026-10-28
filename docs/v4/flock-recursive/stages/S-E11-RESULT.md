# S-E11 (track L-circ): RESULT

Stage S-E11, 2026-10-28, HEAD `7a8cf13`. Build tree `logs/fr-build-SE11` (a copy of
`fr-build-SE10`; `snap.sh` symlinks L-circ's modules and the new `FRVIRTplGrp`, `FRVIRTplRun`,
`FRNodeDag`, `FRNodePlan`; every other module is HEAD's). Logs in `logs/S-E11/`; journal
`S-E11-JOURNAL.md`. Every lean/lake/probe command ran in a 16 GB scope with a timeout. Nothing is
committed.

**Note on the tree.** `FRVIRCompile` is an L-circ module and is symlinked, so INT-5's uncommitted
edit to it (12:22, `assertBit` foreign) is in every build and measurement after 12:22. It does not
change the rows.

## Status by item

| Item | State |
|---|---|
| 1. (d) the run class | **Done.** `evalMT` 189 → 81–89 ms; **V 277.9 → 192.9 ms best** (198.7 median). Kill rule passed. Padding `G`'s outputs not done (deviation 1). |
| 2. (b) the `phiRS` split | **Done** as a split layout of the one template: **−61,440 rows per slot**. `tplPhiRS_ok` is untouched (deviation 2). |
| 3. `dag_mle` | **Stated and proved** (`FRNodeDag`). `D̂` checked against the sparse value. |
| 4. Plan time | **Partly done.** The plan is a closed constant built at process start (`FRNodePlan`). The cold check is not slower than a warm one by any plan cost. **`planOf` is 43–47 s, not ≤ 5 s** (§4): blocked. |
| 5. `mRowModel` | **Done**: 825,697 per slot (1.27×), `mRows_le`, `usedBlocks_le`, negative control `mRows_neg`. |
| 6. Re-dump | **Done**: `logs/S-E11/nodedump/` with `SHA256SUMS`. |

## 1. What was built (code lines, core `loc.py`, HEAD → now)

| Module | Code | Change |
|---|---|---|
| `FRVIRTplGrp` (new) | 327 | The first half of HEAD's `FRVIRTplFast`, unchanged (grouped forms, `tplR_mle`, `denseIT`, `hfac`, `KP`), plus the triples and `ownSum`/`ownSum_eq` moved from the second half. |
| `FRVIRTplRun` (new) | 326 | **The run class**: `Pat`, `OwnP`, `runCh`/`runCh_spec`, `findRun`, `prepOwn` (well-founded), `ownSumP`, **`ownSumP_eq`** (for any pattern table), `run_val`, `ownSumP3(_eq)`, `runIn`, `inrOf(3)`. **The fast key preparation** `kprepF` (one product per row and matrix; none for a unit coefficient) with **`kprepF_eq : kprepF = kprepT`**, and the keys' low tables once per evaluation (`preTabs`, `tabOr_eq`). The search: `runsOf`, `patsFor` (chunk bits `B ∈ [2, 9]` by estimated cost), `mkPats`. Controls. |
| `FRVIRTplFast` | 664 → 400 | `PPc.ins` carries `List OwnP`; `prepPiece pats`; `Tb` gains the low tables; `ECtx`/`ECtx3` carry the patterns and their inner sums; `ownSumP_tb`; `ppv_eq`, `slotV_eq`, `slotV3_eq`, `nodeV_eq`, `nodeV3_eq`, `evalLT_eq` re-proved; `Plan` gains `pats`, `pbs`; `tbOfK`. **`evalMT_eq` unchanged in statement.** |
| `FRVIRTplPlan` | 244 → 274 | `sortOwn`: a key's own inputs renumbered by the cells of its first member's forms (so that runs are consecutive); `ownOf` by number; `tinPP` cuts a split template into head and tail blocks; uses `tRows`/`tRbits`. |
| `FRVIRTplExt` | 395 → 431 | The walk's rows and bit sizes as closed constants (`tplWalk14Rows`, `…RB`, `…CB`, `…NL`), `tRows`/`tRbits`/`tCbits`/`tNlocs` with `tRows_eq`, `tRbits_eq`; `splitOf`, `splitRow`; `mkLay` lays split templates out and reads each template's rows once; controls `splitRow_phi`, `splitOf_walk`. |
| `FRVIRTplEval` | 372 → 383 | `tinIRows`: split row placement; array lookups (`instRowA`); `tinIRows_none`; `slotVal`'s closed form only for unsplit keys. |
| `FRVIRTplCore` | 195 → 208 | `instLinA`, `instRowA`, `instRowA_eq`. |
| `FRNodeDag` (new) | 53 | **`dag_mle`**: `WPlan`, `mkWPlan`, `walkTin`, `dagHat`. |
| `FRNodePlan` (new) | 9 | `nodePlan`, `lPlan`, `implCN`, `implCN_eq` (`rfl`). |
| `FRNodeLayout` | 191 → 193 | `mRowModel` (revision 3.16), `mRowModel_sum`, `mRows_neg`. |

**Statements.** None of the statements other tracks use changed: `evalMT_eq`, `evalLT_eq`,
`planL_rows`, `implC_meets`, `tplExt_ok`, `compileT_sound` and `node_m_sound` all build with HEAD's
statements (`lake build FR FRNodeDag FRNodePlan` green, 2,392 jobs, `build-final.log`). Two
specifications changed:
- **M's row placement for `phiRS`** (`tinIRows`). The rows are the same; their indices changed.
- **The plan's internals** (`Plan`, `PPc`, `ECtx`). Only `FRVIRTplFast` and `FRVerifierImpl` use
  them, and `FRVerifierImpl` only through `planOf`, `evalMT`, `evalMT_eq`, `evalMS`.

## 2. Item 1: the run class (V)

Where `evalMT`'s time went, measured part by part (each forced; `evbrk-base.log`):

| Part | HEAD | after S-E11 (`evbrk-3.log`) |
|---|---|---|
| tables | 2.2 ms | 5.8 |
| **keys' preparation (`kprep3`)** | **66.6** | 34.1 |
| contexts (per slot) | 1.6 | 5.1 (the patterns' inner sums) |
| sparse pieces (per slot) | 11.1 | 11.6 |
| instances (per slot) | 51.7 (`G` key 26.4, `maskRows` 9.6) | 11.1 (`G` 1.2, `maskRows` 0.6, `phiRS` head 1.3 + tail 1.4) |
| **`evalMT` best** | **189 ms** | **89 ms** (81.2 ms on core 22, `e5eval-check.log`) |

- S-E10's per-key figures carried a ≈ 74 ms constant: its closures recomputed `kprep3`. The
  keys' preparation, not the shift class, was the largest single cost.
- The runs first found nothing in the `G` key. Its own inputs are numbered by first appearance in
  the block's rows, so `rowW′[k]`, the state words and `colW[k]` interleave (`owndump-51.log`).
  `sortOwn` fixes the numbering in the search.
- Now: 3,479 runs and 2,370 plain own forms per slot.

| V (N30, 21 warm runs) | best | median | log |
|---|---|---|---|
| HEAD (core 30) | 277.92 ms | 295.40 | `vtime-N-base.log` |
| item 1 (core 30) | 196.77 | 208.70 | `vtime-N-d1.log` |
| items 1, 2 and the plan-time changes (core 22) | **192.87** | **198.70** | `vtime-N-d3.log` |

`vtime-N-d2` (245 ms) was taken on core 30 while INT-5's `vtime prof` ran on the same core
(`ps`). It is void.

**Kill rule:** 192.9 + 18.5 still to add = **211 ms ≤ 230**: continue.
- The 18.5 ms is the kind factor 6, the remaining templates 4, `D̂` 1.5 and `R` 7.
- At the measured ratio 1.19 that is ≈ 178 ms on the 7763 against the 206 ms cap: 1.16×.

## 3. Item 2: the `phiRS` split

- `splitOf (.phiRS n) = (n, size (n − 2))`, i.e. (7, 3).
- Instance `i`'s row `j` is at `rowBase + splitRow 7 3 i j`:
  - instances in groups of 16;
  - each group holds 16 heads of 128 rows, then 16 tails of 8 rows: 2,176 rows;
  - so an instance takes 136 rows instead of 256.
- `mkLay` reserves `⌈n/16⌉ · 2,176` rows. `tinPP` cuts every instance into a head block
  (`A = 7`) and a tail block (`A = 3`) over the instance's cell window, which gives two keys.
- `Plan.ok` checks the pieces against the new `slotIRows`: they passed (89 keys, no fallback).
- **Rows per slot: 526,205 → 464,765 (−61,440)** (`evbrk-3.log`, dump). Changes 22 estimated
  −62,464.

## 4. Item 4: plan time

- **The closed constant.** `Impl.nodePlan := planOf (finC finPf)`; `Impl.implCN := implCWith
  nodePlan lPlan`; `implCN_eq : implCN = implC (finC finPf) Layout.lRows κs₀` (`rfl`).
- **Measured, it is built at process start:**
  - `probe/ColdWarm.lean init` does nothing in `main`, and the process still takes **48.8 s**
    (`coldwarm-init.log`). That is `nodePlan`, `lPlan` and the walk's closed constants.
  - In `probe/PlanT.lean`, the walk template's closed constants are already there when `main`
    starts (1.8 ms).
- **Cold against warm** (`coldwarm-2.log`, core 22): the first check takes 230.9 ms and the 7 warm
  ones 205.3–219.7 ms.
  - The first check is ≈ 15–25 ms slower: first-touch effects, not the plan.
  - **The S-I `acc` must be stated with `implCN`** (or another nullary constant), not with
    `implC fin …` applied inside `acc`.
- **`planOf` is 43.4 s** (`e5eval-check.log`, core 22; 46.9 s on a loaded core 30), **not ≤ 5 s.**
  - S-E10 had 57 s.
  - Done: the walk's template rows and bit sizes are closed constants; `instRowA` gives array
    lookups, since the walk instance's `2^15` input forms were looked up in a list; `mkLay` reads
    each template's rows once.
  - Where the rest goes, slot 0 (`plant-2.log`, loaded core):

    | Part | Time |
    |---|---|
    | compile, zero layout | 1.7 s |
    | `mkLay` | 4.7 s |
    | compile | 1.8 s |
    | `slotIRows` (428,466 rows) | 3.6 s |
    | `slotPPs` (`segsGo` replays the compile; `absRows` per block) | 8.7 s |
    | `groupPPs` | 2.1 s |
    | `eqL` | 1.3 s |
    | `mkPats` | 0.2 s |

    Both slots: ≈ 2 × 20 s + grouping.
  - **Why ≤ 5 s is out of reach this way.** `Plan.ok` equates the pieces' rows with
    `slotIRows (lay σ) … (cs σ)`, so the check needs both slots' compiles and 2 × 428 k
    materialised rows.
    - The compiles alone are ≈ 3.5 s on this VM.
    - Materialising and comparing the rows is ≥ 2 × 5 s at today's ≈ 10 µs per row.
  - **The routes, for the orchestrator:**
    1. **Memoise every key's template data** (rows, bits, locals) once per node and drop
       `segsGo`'s compile replay: the compile can record the blocks. This is mechanical, but I
       expect at most ≈ 2× (to ≈ 20 s).
    2. **Slot symmetry**: prove that slot 1's compile is slot 0's shifted by `2^20` outside the
       selector cells (S-E9: 20,506 of 20,510 cells shift). Slot 1's compile, rows and check go
       away (≈ 2×).
    3. **The compiler emits the pieces** (S-E10 option 2), with a generic lemma
       `flatMap Piece.rows (compilePieces …) = slotIRows …`. This removes `slotIRows`, `slotPPs`,
       `groupPPs` and `eqL` from the run time. It is the only route I see to ≤ 5 s, combined with 2.
  - The batch budget is `verify_s · n + 60 ≥ 70 s`. A 43–49 s process start fits it today, with
    ≈ 20 s to spare.

## 5. Item 3: `dag_mle`

- `mkWPlan L off tw` runs the plan's search over the walk instance alone: `tinPP` gives the
  head, 80 `G` blocks and the tail, and `groupPPs` makes them 5 keys and 83 instances. It keeps
  the result only if the rows **are** `tinIRows L oneL off tw`.
- **`dag_mle`**: `dagHat wp τ σ = (matMLE (entriesI .a (tinIRows …)) …, …)` for all three
  matrices, from `slotV3_eq` and `slotV_eq`.
- Measured (`daghat-1.log`, loaded core): `mkWPlan` 8.6 s at plan time; `dagHat` 13.9 ms, of
  which the five keys' preparation is 8.4 and the tables ≈ 4–5 (shared with `evalM` in V); the
  sparse value of the 85,506 walk rows is 151 ms; **equal**.

## 6. Items 5 and 6: `mRowModel` and the dump

**`mRowModel`** (per slot):

| Entry | Rows | Built? |
|---|---|---|
| skeleton, emitted templates, the walk DAG and the `phiRS` split | **464,765** | measured |
| `rsWeight` | 45,604 | no |
| claim-2 kind factor | 68,473 | no |
| `shiftTarget` | 1,300 | no |
| 745 `tensorW` | 47,680 | no |
| `tplTargetSNode` | 16,000 | no |
| `tplLinkWAll` | 15,000 | no |
| `free` term | 80 | no |
| `R` with the levers (163,795) and its closed-form share (3,000) | 166,795 | no |
| **total** | **825,697** | |

- Per node: **1,651,394 = `2^20.65` (1.27×)**. Changes 23 gives 825,411 per slot; the
  difference is +286 rows, all in the measured part.
- `mRows_le`, `usedBlocks_le`. Negative control `mRows_neg`: S-E9's 1,065,133 does not fit a
  slot.

**Dump**: `logs/S-E11/nodedump/` (the probe `NodeDumpT` now reads `Impl.nodePlan`; `SHA256SUMS`).

| | per slot | per node |
|---|---|---|
| indexed rows | 428,466 | 856,932 |
| layout rows | **464,765** (slot 1's last index `2^20 + 464,764`) | **929,530** |
| blocks of 128 | 3,631 | 7,262 |
| template instances | 2,285 | |

`groups-σ.txt` gives every key's layout. The two that changed:
- `phiRS 7 | 201728 | 6596352 | 8 | 8 | 134 | 512 | split a=7 b=3 g=16`
- `walkAB 16384 16384 | 305152 | 6799360 | 17 | 17 | 85506 | 1 | walk blocks 2^10`

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `runCh` | `runCh_pos`: three consecutive cells at offset 1 of a 4-cell chunk | `runCh_cross` (the run crosses its chunk), `runCh_gap` (a gap in the cells) |
| `prepOwn` / `ownSumP` | `ownSumP_eq` for every table; measured, `evalMT` equals the sparse value over `nodeIRows` (`e5eval-check.log`, `equal true`) | a run is emitted only where `runCh` succeeds (`runCh_spec`); the two refusals above |
| `kprepF` | `kprepF_eq` (equality with the spec); the same measured check | — (an equality) |
| `splitOf` / `splitRow` | `splitRow_phi`: 7/3, instance 0's tail at 2,048, instance 15's last row at 2,173, instance 16 at 2,176; the plan check passes | `splitOf_walk`: other keys keep their stride |
| `dagHat` / `mkWPlan` | `dag_mle`; measured equal to the sparse value (`daghat-1.log`) | `walkTin_none`; `mkWPlanOf_sparse` (the fallback is a plan) |
| `mRowModel` | `mRows_le`, `usedBlocks_le` | `mRows_neg` |
| `nodePlan` | `implCN_eq`; `coldwarm-init.log` (initialized before `main`) | `coldwarm-2.log`: the cold check is not seconds slower |

## 8. Checks

- **Build:** `lake build FR FRNodeDag FRNodePlan` green in `fr-build-SE11` (`build-final.log`).
- **Axioms** (`axioms.log`): 60 names, including the 24 new ones (`kprepF_eq`, `ownSumP_eq`,
  `ppv_eq`, `slotV3_eq`, `dag_mle`, `tinIRows_none`, `implCN_eq`, `mRows_neg`, …). The only axioms
  are `propext`, `Classical.choice` and `Quot.sound`; some names use none.
- **Source rule:** 172 files, 0 findings (`source-rule.log`).
- **Sequential profiles** (one core, `Elab.async=false`, `profile-*.log`):

  | Module | wall | type checking | tactics |
  |---|---|---|---|
  | `FRVIRTplRun` | 11.3 s | 0.27 s | 0.57 s |
  | `FRVIRTplGrp` | 9.3 s | 0.32 s | 0.60 s |
  | `FRVIRTplFast` | 10.0 s | 0.17 s | 0.99 s |
  | `FRVIRTplExt` | 10.3 s | 0.21 s | 1.54 s |
  | `FRVIRTplEval` | 10.2 s | 0.34 s | 0.76 s |
  | `FRVIRTplPlan` | 7.7 s | 0.06 s | 0.07 s |
  | `FRVIRTplCore` | 8.3 s | 0.16 s | 0.20 s |
  | `FRNodeDag` | 6.3 s | 0.03 s | 0.02 s |
  | `FRNodePlan` | 6.1 s | 0.00 s | — |
  | `FRNodeLayout` | 9.6 s | 0.69 s | 0.65 s |

## 9. Deviations and open questions

1. **`G`'s output words are not padded.** After `sortOwn` the `G` key costs 1.2 ms per slot (79
   instances, 1,794 pattern entries). Padding would save at most one run per word, < 0.5 ms, and
   would change the template and its proof.
2. **The `phiRS` split is a layout, not two templates.**
   - One template, two row blocks per instance (`splitOf`, `splitRow`).
   - `tplPhiRS` and `tplPhiRS_ok` are untouched, and `ImplT.phiRS` is unchanged.
   - Two templates per op would have needed two template instances per op in the compiler (`Out`
     has one `tin`) and a composition proof. The rows are the same: 136 per instance.
3. **The keys' preparation was rewritten** (`kprepF`). It was the largest part of `evalM` (67 of
   189 ms), and the brief did not list it.
4. **`sortOwn`** changes how the search numbers own inputs. `Plan.ok` still checks the result.
5. **Plan time is blocked** (§4). The ruling's ≤ 5 s needs route 3 (with 2), which changes the
   proof architecture of `Plan.ok`. The process start is 43–49 s, inside the 70 s batch floor.
6. More `evalM` levers, measured but not taken (V is 192.9 ms):
   - share the patterns' inner sums between the slots when their shared-input counts agree:
     ≈ 5 ms;
   - fold `one·E(one) + sv` into one constant per key and slot: ≈ 3 products per instance,
     ≈ 4 ms;
   - build the low tables by additions from the 12-bit table: ≈ 3 ms;
   - prepare the three matrices of a key in one pass.

**Edit requests**
- `FR.lean`: `import FRNodeDag`, `import FRNodePlan`. `FRVIRTplGrp` and `FRVIRTplRun` are
  already in `FR`'s closure, through `FRVIRTplFast`.
- **S-I**: state the certificate's `acc` with `Impl.implCN` (the closed plans).
- **Blueprint** (next revision):
  - §4.4/A.11: the walk's own-input runs; `phiRS`'s split layout (136 rows per instance,
    −61,440 per slot); `D̂ = dagHat` with `dag_mle`.
  - §0/§3.2: V 192.9 ms VM best after the shift class.
  - The plan-time ruling: the measured 43–49 s process start, and §4's routes.

## For P2

- **`phiRS`'s row map.** In group `phiRS 7` (row base `rb`, from `groups-σ.txt`), template row
  `j` of instance `i` is at slot row `rb + (i/16)·2,176 + r`, where
  - for `j < 128`: `r = (i mod 16)·128 + j`;
  - otherwise: `r = 2,048 + (i mod 16)·8 + (j − 128)`.

  The cells are unchanged: locals at `cellBase + i·2^8 + k`. The rows are the template's rows in
  order, so the head is stages 0–3 and four squarings of stage 4; the tail is the rest.
- **The walk.** Unchanged since S-E10 (one instance; head, 80 `G` blocks, tail at a 1,024 stride;
  locals `cellBase + k`).
- **Rows.** 464,765 per slot in the layout (428,466 listed; the rest are alignment gaps with no
  rows).
- **Dump.** `logs/S-E11/nodedump/`:
  - `mrows-σ.txt` gives every row with its global index; `groups-σ.txt` gives the keys and their
    layouts;
  - `mregs`, `maux`, `lrows`, `wm` and `wots` are as in S-E10's format;
  - `SHA256SUMS` holds the checksums.
