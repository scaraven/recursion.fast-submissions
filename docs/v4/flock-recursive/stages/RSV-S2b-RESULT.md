# RSV-S2b RESULT: B′ at 69 cells, the reserve's controls, the chain to `StmtN4R`

Track RSV-S2b, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`. Started at
`b156c27`, re-snapshotted onto `e464756` (A1′) when it landed. Build tree `logs/fr-build-RSVS2b`; logs
`logs/RSVS2b/`. Journal `stages/RSV-S2b-JOURNAL.md`. No sub-agents and nothing committed.

## 0. Summary

| Item | Status |
|---|---|
| 1. B′ at 69 cells via the DRS route (orchestrator's Q2) | **Done, green.** `PubOKR4` enters only RS0's and RS1's `Pub` (`PubRSX = PubX ∧ PubRX`); phases 16 … 22 and `bg16X`/`bg20X` are unchanged; `single_B4` is over `Fin 71` at `70·2^128`; `W₀`/`DBX` batch `cellsX ν = cells4 ν ++ rsvCells ν`. |
| 2. Controls `truthChild_pos`, `childBad_neg`, `kindChange_pos`, `n8_zero` | **Done, green** (new `FRSoundness4RsvCtrl`, + `kindChange_mat`, `n8_neg`, `vStarL4_rsv_ne`). |
| 3. The chain | **Done up to the value form of the discharge.** `StmtN4R`, `truthChildV`, `nodeRunR_X` (accept → `StmtN4R` at the log's own child claim), `RunFacts4.node` carries the zero outputs `RsvZero`, `nodeLaws4C'` and its two siblings generalised over `St`, `nodeSoundR_X`, `ks_rev4R`; `evalM_childV` (slot 0's `evalM` returns `ch`'s `X₃` at `ch`'s inputs). **Open:** the plumbing of `evalM_childV` into `SlotRunA`'s residual imports (`gap4Imp_of_rsv`), which sits on PORT's sorried `gap4Imp_of_run` (§5). |

Build: `lake build FRNodeStmtR4 FRSoundness4P4fCtrl FRSoundness4XRunG FRSoundness4XCtrl FRNodeSound4K` is
green in the build tree (`logs/RSVS2b/auto-1.log` of the last loop run, 2,475 jobs), with other tracks'
red declarations sorried in the build tree only (§3). Axioms of 20 key theorems and controls:
`propext`, `Classical.choice`, `Quot.sound` only (`logs/RSVS2b/axioms.log`). Source rule: 410 files, 0
findings (`logs/RSVS2b/source-rule.log`). No `sorry` in the worktree's sources.

## 1. What was built (code lines, the core's `loc.py`, HEAD → now)

| Module | Change | code |
|---|---|---|
| `FRSoundness4P4bB` | `rsvV`, `nRsv`, `rsvL`, `rsvHL`; **`vStarL4`** gains `κ′^{11}·Σ_i κ′^i v_i`; **`PubOKR4`**, `pubOKR4_reads`, `ReadsS.and`, `rsvV_congr`/`rsvL_congr`/`rsvHL_congr`; `dRS0_4_reads`/`dRS1_4_reads`/`rs1_hfin4` take `Pub` read up to 327/331/327; **`dRS0_4_mono`**; `bTerms4` over `Fin 71` with `pub ++ rsv`, `bTerms4_sum`, `sum_cells_pad`, `rsvHL_eq`, `rsvL_length`, **`pubPart_eq`**, `list_eq_of_getD`; **`single_B4`** (69 cells, `70·2^128`); controls `vStarL4_node_ne` (restated), `vStarL4_rsv_ne` (new) | 310 → 410 |
| `FRSoundness4XFront` | **`cellsX`**; `W0X := W₀L4 kf4 cellsX`; `frontObl_X.loc` at `cellsX` | 226 → 227 |
| `FRSoundness4P4fDF` | **`PubRX`**, **`PubRSX`**; `DRS0X`/`DRS1X` at `PubRSX`; `DBX` at `cellsX`; `rd_PubRX`, `rd_PubRSX`; `rd_DRS0X`/`rd_DRS1X` | 264 → 271 |
| `FRSoundness4P4fObl` | `hrcellsX`; `habs_hi` at 326 lands in `PubRSX`'s `DRS0X` (`dRS0_4_mono`); `hsingle_hi` B′ (`single_B4 … hrcellsX`, `70 ≤ 239`); `hfin_hi` RS1 (`rd_PubRSX`); `ip_W0X`, `locX` at `cellsX` | 380 → 384 |
| `FRSoundness4P4fCtrl` | `not_DFhi25_true` at `cellsX`; imports `FRSoundness4RsvCtrl` (so the controls are on `FR`'s build) | 41 → 42 |
| `FRSoundness4RsvCtrl` (new) | `child_rsvV`, **`truthChild_pos`**, **`childBad_neg`**, **`kindChange_pos`**, **`kindChange_mat`**, `e2R_N2_N4`, **`n8_zero`**, `n8_neg` | — → 73 |
| `FRSoundness4XLaws` | **`RsvZero`**; `RunFacts4.node` carries `RsvZero`; `nodeRun_X` ignores it | 81 → 83 |
| `FRSoundness4XRun` | `hcellsX`; `acceptRun4_seg`/`_node` call `wV4_of_fields` at `cellsX`; `runFacts4_node_C` gives `RsvZero` from `rsvZero4` (**RSV-S2a's, requested**, §5) | 216 → 221 |
| `FRNodeCircuit4` | `nodeSoundLog4_of`, `nodeExtLog4_of`, `nodeLaws4C` generalised over `St` with `hSt : St → StmtN4` | 308 → 314 |
| `FRNodeCircuit4Dig` | `nodeLaws4C'` likewise | 249 → 251 |
| `FRSoundness4XFinal` | `nodeSound_X` passes `hSt := id` | 64 → 64 |
| `FRNodeStmtR4` (new) | `mStackV`, **`truthChildV`**, **`StmtN4R`**, `truthChildV_nil`, `mStack_congr`, **`truthChildV_rsvL`**, **`evalM_childV`**; `phOf4_214_326`, `agree_takeN`, **`rsv_of_tail`**, **`nodeRunR_X`**, **`nodeSoundR_X`**, **`ks_rev4R`** | — → 160 |

## 2. Every statement change, with its reason

**Definitions whose meaning changed:**
- `P4b.vStarL4`: `v_RS + [node](κ′²·pubH(κ′) + κ′^{11}·rsvHL)`, `rsvHL = Σ_{i<nRsv} κ′^i·v_i` (60 on
  `N2`/`N4`, none on `N8`/segments). RSV2 §2.2's B′ claim. `c₀L4`, `DB4` follow.
- `X4.W0X`: cells `cellsX` (69 on `N2`/`N4`, 9 on `N8`): `finPf`'s two cell chains (κ′^{2…10}, κ′^{11…70}).
- `P4f.DRS0X`, `DRS1X`: `Pub := PubX ∧ PubRX` (orchestrator's Q2). `DBX`: cells `cellsX`.
- `X4.RunFacts4.node`: also `RsvZero` of the chain's entries (`finE`'s two zero asserts). Not
  `msgAt es 213 = fLrEnd π` as RSV-S's handover proposed: with `ch` a binder of `StmtN4R` the chain
  needs only the two values, and `π` never enters (see §4).

**Theorems restated:**

| Theorem | Change | Reason |
|---|---|---|
| `P4b.single_B4` | `+ rcells`, `hrcells`; RS1's `Pub` is `PubOK4 ∧ PubOKR4`; B′'s cells `cells ++ rcells`; bound `70·2^128` (was 10) | RSV2 §2.6: `J_f = 69` |
| `P4b.bTerms4`, `bTerms4_sum` | `Fin 71`, list `pub ++ rsv` | same |
| `P4b.dRS0_4_reads`, `dRS1_4_reads`, `rs1_hfin4` | `hP : ReadsS R 327/331/327 Pub` (was `3`) | `PubOKR4` reads Lrend's message (214). Weaker hypothesis; callers pass `.mono` |
| `P4b.vStarL4_node_ne` (control) | `+ hr : ∀ i, rsvV es i = 0` | `v*` now has the reserve's batch |
| `N4c.nodeSoundLog4_of`, `nodeExtLog4_of`, `nodeLaws4C`, `nodeLaws4C'` | `{St}` and `hSt : St → StmtN4` after `rd`; `hRun`/`hRes` over `St` | orchestrator's Q1; `St := StmtN4`, `hSt := id` gives the old form |
| `X4.RunFacts4` (structure) | `node`'s conclusion `∧ RsvZero …` | above |
| `R4.acceptRun4_seg/_node` | (proof only) `wV4_of_fields` at `cellsX` | `W0X` changed |

Rows: B′ `70/2^128 = 2^-121.9 < 2^-120.36`; `deltaR` and `εR = 15/2^124` unchanged.

## 3. Build, checks, times

- Build tree: HEAD `e464756` text for every module but this track's (symlinked). Build-tree-only
  sorries (`patchdec.py`, `autosorry.txt`): RSV-S's decoder/B3 list; RSV-S2a's `R4Fin.flag_gFinE`,
  `flag_gFinB'`, `R4FrE` (`e_end4`, `not_rejEndE4_node`, `e_in4`, `not_rejInE4_node`, `e_fin4`,
  `not_rejFinE4_node`), `R4FrRS.e_bind4`, `R4Start.start4_of_fields`, `R4PfFlag.gFinPf_reloc`,
  `R4FrCtrl.relE4_rejects`, `Qry.ks_queriesC4` (red at `e464756`: `8783 ≤ qV4` no longer decides,
  A1′'s spacers); PORT's `FRNodeLinks4.acceptRunL4_node`, `FRNodeLinks4Run.fmAns_of_run4`,
  `FRXOut4.reassemble4_size`/`pf4_size`, `FRXOut4W.sgnX_fits`, `FRXOut4P.rl_vS`,
  `FRXOut4A.chR_agg`/`aggRegs_sem`, `FRXOut4O.cso_pfIR` (FRXOut4O still red further on; not on my
  modules' path). **Two predicted interfaces** (build tree only, §5 requests 1–2): `R4W0R.w0V4_eq4`,
  `wV4_of_fields` with `hcl : P.cells ++ P.rcells = cellsC cells κc`; `R4FrE.rsvZero4`.
- Green: `FRNodeStmtR4 FRSoundness4P4fCtrl FRSoundness4XRunG FRSoundness4XCtrl FRNodeSound4K`.
- Sequential profiles (one core, `Elab.async=false`): `logs/RSVS2b/prof-summary.log` and
  `profile-<m>.log`; figures in §3.1.

### 3.1 Times (`prof-summary.log`; one core, `Elab.async=false`; wall includes ≈ 6.5 s of imports)

| Module | wall | type checking (kernel) | tactic execution |
|---|---|---|---|
| `FRSoundness4P4bB` | 11.5 s | 0.49 s | 0.83 s |
| `FRSoundness4XFront` | 8.8 s | 0.40 s | 0.52 s |
| `FRSoundness4P4fDF` | 9.4 s | 0.33 s | 0.74 s |
| `FRSoundness4P4fObl` | 11.3 s | 1.33 s | 0.81 s |
| `FRSoundness4P4fCtrl` | 7.2 s | 0.05 s | 0.12 s |
| `FRSoundness4RsvCtrl` (new) | 7.0 s | 0.06 s | 0.13 s |
| `FRSoundness4XLaws` | 7.7 s | 0.08 s | 0.17 s |
| `FRSoundness4XRun` | 8.6 s | 0.13 s | 0.52 s |
| `FRNodeStmtR4` (new) | 8.2 s | 0.16 s | 0.32 s |
| `FRNodeCircuit4` | 12.6 s | 1.28 s | 2.30 s |
| `FRNodeCircuit4Dig` | 9.8 s | 1.06 s | 0.86 s |
| `FRSoundness4XFinal` | 7.0 s | 0.01 s | 0.03 s |

New kernel time of this track's additions: the two new modules ≈ 0.2 s; P4bB's B′ rework is symbolic
(no `decide` over the 71 terms). The certificate's 461.7 s figure is not re-measured (tree not green).

## 4. The spacer question (orchestrator, after A1′)

Checked: no argument of this track ranges over trace entries. `nodeRunR_X`/`rsv_of_tail` read the
parent's **own** chain (`entriesOf L (pathOf L j)` of `V(P)`'s run, T4's `tail_of_accept`);
`RunFacts4.node`/`RsvZero` are facts of `V(P)`'s own log; `evalM_childV` is about slot 0, the previous
node (never an aggregate); `single_B4`/`PubOKR4` read `f⁽⁰⁾` and Lrend's message. Nothing assumes
that an aggregate trace entry is a segment's `(q, H q)`. (A ROM-consistency argument over `tr_A` would
live in the aggregate's slot discharge, `gap4Imp_of_run`/`Gap4R.aggChk`: PORT's/B4's.)

## 5. Open, in order; requests to other tracks

1. **RSV-S2a, `R4FrE`: `rsvZero4`** (XRun calls it; the worktree is red there until it exists):
   ```lean
   theorem rsvZero4 {impl : OpImpl} {ν : NodeKind} {cells : List ℕ} {inp : Input} {tr : Trace}
       (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) :
       readF (msgAt (fsOf tr (itemsOf seq4)) 213) (48 + 16 * 58) = 0 ∧
         readF (msgAt (fsOf tr (itemsOf seq4)) 213) (48 + 16 * 59) = 0
   ```
   (`relE4`'s zero conjuncts read through `msg_abs4` at 213, as `e_end4` reads Lrend's message.)
2. **RSV-S2a (finPf), `R4W0R`**: `w0V4_eq4` and `wV4_of_fields` with
   `(hcl : P.cells ++ P.rcells = P4b.cellsC cells κc)` (was `P.cells = …`), all else unchanged, once
   `w0V4` (`R4PfFlag`) adds `Σ_i κ′^{11+i}·eq(rcells_i, ρ)` where `rsvOps ∧ rsv`. XRun already calls
   it at `cellsX` with `rfl` (node: `cells4 ν ++ rsvCells ν`; segment: `[] ++ []`). `R4W0R` is in no
   track's list; it belongs with `relPf4`.
3. **RSV-S2a, `R4Start.start4_of_fields`**: `vStarL4`'s new form is
   `vRSL4 + [node](κ′²·pubHL + κ′^{11}·rsvHL)`, `rsvHL κ es kp = Σ_{i<nRsv κ} kp^i·rsvV es i`,
   `rsvV es i = readF (msgAt es 213) (48 + 16·i)`; `rsvHL_eq` gives the `range 60`/`getD` form. If
   `vStar4` is easier as `Σ_{i<60} κ′^{11+i}·v_i`, `pubPart_eq` is the bridge.
4. **`gap4Imp_of_rsv`** (this track's, next): `SlotRunA`'s residual imports at slot 0
   (`impAP … (protoOf κ 0)`) contain the stacked call's three output registers; their `RepS` facts
   follow from `evalM_childV` once the input registers' values are `w` at `rsvRel[0..57)` (the compile's
   slot map `(protoCS π).slot`) and `PubCellsR4` holds. It needs PORT's `gap4Imp_of_run`/`execA_proto`
   (sorried at HEAD) and A1′'s `Gap4R = imp, aggChk` (only `imp` is touched; `kindN`/`kindS`/`wf` now come
   from `gap4_of_rows` and are not involved).
5. **The switch to `StmtN4R` downstream**: `ks_rev4R` exists (at `P4f.DFhi`); `Resid4.slots`,
   `certificate_rev4`, P4fObl's `ks_rev4F`/`certificate_rev4F`, XRunG and `FRNodeSound4K` still use the
   `StmtN4` form of `hRes`. Switching is mechanical (`hRes` gains `ch`; users take `hS.1`); it pays off
   only with item 4, since `hRes` is unprovable from `StmtN4` alone at a kind change.
6. **FR.lean**: nothing needed (the controls are imported through `FRSoundness4P4fCtrl`).
