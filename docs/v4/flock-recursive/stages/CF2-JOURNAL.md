# CF2 (continues CF): JOURNAL — wiring the closed forms into the plan

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `f041d03`). Build tree `logs/fr-build-CF2`
(copy of `fr-build-CF`; `mysnap.sh` = HEAD snapshot + this track's modules linked, `mymods.txt`, now with
`FRInitFuse`, `FRNodeRows4RepCFW`). Logs `logs/CF2/`. Every lake/lean/probe in a 16 GB scope under
`timeout`. No sub-agents, nothing committed.

## 2026-10-30 start

- Baseline: `lake build FR Solution FRSubmission4Fin plan4t vtime4 cfrs FRNodeRows4RepCFP FRNodeRows4RepLCtrl`
  green at HEAD (nothing to rebuild; `logs/CF2/base.log`). Reference binaries: CF's (`logs/CF2/bin-cf`, from
  `fr-build-CF`).
- **Import cycle found**: `FRNodeRows4RepCFP` imported `FRNodeRows4RepK`, which is downstream of
  `FRVerifierImplNode4F` → `FRNodeRows4Plan`; the plan could not import CF's plan side. Fix: `gatesAtGo_eq`,
  `rowsTR_eq` (namespace `N4s`, statements unchanged) moved from `FRNodeRows4RepK` to `FRNodeRows4RepCFP`;
  CFP no longer imports RepK; RepK imports CFP.

## Step 1 (wire `arBlk0`/`kopV`): done, green (`logs/CF2/s1c.log`, 5,079 jobs)

- `FRNodeRows4RepCFW` (new): `kpLen` + `kpLen_eq` (an `rsWeight` op's row count from its preparation),
  `blkGo` (tail-recursive split of the blocks: row blocks' indexed rows, prepared ops at their first
  rows), `spV`, **`blkGo_val`**, `blk_val`, `blkGo_len`, `wFA`/`wLA` (+ `_eq`), `wF_cb`/`wL_cb` (the
  `hw` of `kopV_eq`), `kpsV3`, `rowsVal_spF/L`, `arBlkN` (`arBlk0` with the prototype as an argument, so
  no closed constant).
- `FRNodeRows4Plan`: `Plan4.rgF/rgL` now the row blocks' grouped rows; new field `kps`; `hrg` an
  existential over the blocks; `rvOf` adds `kpsV3` (frame: `wF`, `lam = 0`; local: `wL`, `lam = 1`);
  `rvOf_get` statement unchanged, new proof (`blk_val`). `planOf4D` uses `arBlkN k0`.
- Measured (core 29; `logs/CF2/init-s1.log`, `v-s1.log`): init 26.0–26.4 s user (CF 20.3–20.7; the rows are
  still built for `repFitB 0`, and the plan now also prepares the op), RSS 1.38 GB (CF 2.06); V(N4) best
  3,044.8 ms (CF 1,891.5): the unoptimised closed form, six `kopV` calls × three kinds.

## Step 2 (structural `RepFit`): done, green

- `FRNodeRows4RepCFW`: `linCellOk`, `rowCellOk` (+`_iff`), `lRoom`, `cb_cellOk`, `instLin_cellOk`,
  `instRow_cellOk`, `subsG_rows_loc`, `kSig_loc`, `kpFit`, **`kpFit_rows`** (a fitting prepared op's rows
  fit), `blkGo_sub`, `blkGo_mem`, `repFitS`, **`repFitS_spec`** (`repFitS (blkGo 0 bs [] []) → repFitB 0
  (bs.flatMap RBlk.rows)`). Plan: `inR` uses `repFitS q`; `mkPlan4` no longer takes prototype 0's rows.

## Step 3 (speed): partly done

- `SM.bind`, `SM.rep` let-bind (`pat 0` once per call), `srcCh` let-binds `res i`: building the three
  kinds' `rsGS` + preparation is now 0.42 s for the one op (`blkGo` in `cf2p init`), was ≈ 1.3 s per kind.
- `FRVIRTplCFF` (new): `tmG3`, `Rep.ctx3` (placeholder forms evaluated once for both carries; vanishing
  ones skipped by the flags `zl` (locals 0), `zi` (one, inputs 0), per instance), `Rep.pass3`, `psVal3`;
  **`ctx3_eq`** (= `ctx`), `pass3_eq`, **`psVal3_eq`**; `evF`/`mul1`/`mulZ` (no product for 1, 0).
- `FRNodeRows4RepCFW`: `subsV3` (block inputs from array slices, no `kSig`/`pullE` per wire), `kopV3`
  (+`kopV3_eq`), `kpsV3F` (+`kpsV3F_eq`); `rvOf` uses `kpsV3F`. KAT `kpsV3F = kpsV3` (probe `cf2p kat`).
- Measured after steps 2–3a (`init-s3.log`, `v-s3.log`): init **14.1–14.7 s user** (CF 20.3–21.8), RSS
  **1.29 GB**; V(N4) best **1,515.3 ms** (CF 1,886.3). rvOf per call (`cf2p-call`): rgF 82, rgL 450,
  kps frame 188, local 265 ms; after the per-instance skip (`cf2p-brk2`): kps frame 85, local 180 ms.
- Init pieces (`cf2p-init.log`): `arBlkN 0` 2.84 s (ask rows 114,320; 5 blocks), `blkGo` 0.42 s (sp rows
  373,550; one `rsWeight` op, 504,786 rows not built), `repFitS` 0.23 s, grouping 1.25 s, `arRepOf 1` 1.25 s.

## Step 4 (evalL carry automaton): in progress

- `FRVIRTplRepLG` (new, green): `PF`, `PF_succ`, `GS`, **`GS_eq`** (`Σ_{j<n} PF fa L (A+j)·PF fb L (B+j)`
  by the lowest-bit split), `autoG` (memoized states per bit, `kids` dedup), **`ok_autoG`**.
- `FRVIRTplRepLD`: `tplEvL` rebuilt over four automata (`evGM`); C1b's tables/E/F stages removed.
- `FRVIRTplRepL`: `tplEvL_ok` re-proved (statement unchanged): `qE_ev`, `PF_fE`, `PF_fO`, `eqAtR_gN`,
  `lsumR`, `flatten_ev`, `getD_ev`. Green (`s4b.log`, 5,083 jobs).
- Measured (`init-s4.log`, `v-s4.log`, `cf2p-init4/call4`): row blocks 373,550 → 57,972 rows; init
  10.71–10.82 s, RSS 0.82 GB; V(N4) 925.4 ms (CF 1,954.5 in the same run).

## Step 3c, step 5 (fusion), controls

- `evF` skips zero wires, `tmG3` skips zero rows (`mulZ`): kps frame 75, local 182 ms (`cf2p-call5.log`).
- `FRInitFuse.compMSXB` + `compMSXB_eq`; plan `planDataB`, `DataOk`, `planDataB_eq`, `spBlk`; `planData4`
  `noncomputable`; `planOf4D` takes the walk's result.
- `FRNodeRows4RepCFCtrl` (new): `linCellOk_ctl`, `cb_cellOk_ctl`, `kpFit_ctl`, `repFitS_ctl`, `GS_ctl`.
- Green: `lake build FR Solution FRSubmission4Fin plan4t vtime4 cf2p FRNodeRows4RepLCtrl FRNodeRows4RepCFCtrl`
  5,086 jobs (`s5c.log`).

## Step 6 (checks)

- MxKat PASS (33 × true). `plan4t check` N2 equal true (N4/N8 running). Axioms (`axioms.log`) ⊆ the three.
  Source rule 477 files, 0 findings.
- 97d578b reference binaries built in `logs/fr-build-CF2H` (`snapH.sh`: snapshot at 97d578b).
- Final A/B (`init-final.log`): 97d578b 20.34–20.38 s / 2.02–2.03 GB; CF2 9.38–10.88 s / 0.90–0.94 GB.
- Kernel profile (`prof-summary.txt`): `FRNodeRows4RepCFP` (CF's) type checking 84 s, two lemmas
  `linE_filt`/`linE_filtL` 41–43 s each (and a heartbeat timeout under `-DElab.async=false`): their `[]`
  case `rfl` → `simp`. `FRVIRTplRepL` tactic time 80 s, all in the final `exact hok 0 h` (unifying the
  template's gates): now `rw` by two `rfl` lemmas first (check 54 s wall).
- Final A/B V (`v-final.log`, 2 rounds): 97d578b best 1,916.8 / 2,032.5 ms; CF2 854.0 / 856.4 ms.
- `plan4t check`: N2, N4, N8 equal true. `FRNodeRows4RepCFP` kernel 84.3 → 0.24 s after the fix.
- Final build green (`final.log` 5,083 jobs + `final-plan4t.log`). Source rule 477 files, 0 findings.
- Hand-in: CF2-RESULT.md (§5 remaining: chain-read closed form, frame+local in one pass, the walk's
  retained blocks (RSS), `FRVIRTplRepL`'s 43 s `refine`).
