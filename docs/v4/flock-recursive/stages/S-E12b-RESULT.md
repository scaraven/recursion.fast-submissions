# S-E12b (track L-circ): RESULT, pass 1. The compiled rows of the 4.1 nodes: programs, slots, plan, `evalM`

Stage S-E12b, 2026-10-28. Base HEAD `4acc3b3`, re-snapshotted on `60b65cc` (S-E12a committed).
Build tree `logs/fr-build-SE12b`, against `logs/org20`. It is a copy of `fr-build-SE13` plus
S-E11's `E5Eval`, `RStat` and `NodeDumpT`; `MINE.txt` lists the symlinked modules. Logs are in
`logs/S-E12b/`; the journal is `S-E12b-JOURNAL.md`. Every lean, lake and probe command ran in a
16 GB scope with a timeout. Probes ran on core 27, which is shared (load ≈ 5). Nothing is
committed.

**This is a multi-pass track.** This pass delivers item 1 (the programs, the 1 + k slot layout,
the plan and `evalM` with its proof), the V projection (item 6) and part of the dump (item 5).
§7 is the handover: the remaining items in order, including the coordinator's `hRes`/`SlotIface4`
message.

## Status

| Item | State |
|---|---|
| 1. `gen` for N2/N4/N8 through the existing compiler; plan for 1 + k slots; `nodeIRows` per kind | **Done, with deviation 1.** `gen4G` is the group mux. `nodeIRows4 κ` covers all three kinds. `planOf4` is one plan for all kinds. **`evalMT4_eq`** is proved. **The plan costs 2.5–2.6 s per process (target 2 s): not met**, levers in §7. |
| 2. Templates for every unbound import | Not started (§7, item 3). |
| 3. `R` | Not started. The design consequence of the prototypes is in §4. |
| 4. `mRowModel4`, `mRows_le`, `hfit4` | Partly: the measured parts and the arithmetic are in §5. The Lean model and `HFit4` (via S-E12a's `hfit4_of`) are open. |
| 5. Node dumps | **Written:** `logs/S-E12b/nodedump/` (353 MB, `SHA256SUMS`; probe `NodeDump4`, 30 s). It has the prototype rows, groups, registers and aux, and the per-kind slot maps, link rows and `cells4`. The P2 README is open. |
| 6. V for N4 | **Projected 188 ms best, 196 ms median on the VM** (§3). Under the 230 ms kill line. A measured V needs `implN .N4`. |
| Kill rules | V: not hit. Rows: hit only under the literal reading `2^21/1.05` per node. Under each kind's own `N_M` it is not hit (§5). |

## 1. What was built

| Module | New | Content |
|---|---|---|
| `FRVIR4Mux` | yes | **The group mux.** `Grp`; `nodeGrp` (`L32 ↦ N4`, `P30 ↦ N2`, `N30 ↦ N8`) and `segGrp` (`L32 ↦ L32`, `P30 ↦ L30`, `N30 ↦ L31`). `kt`: a kind table evaluated once, `kt_eq`. **`gen4G`** is `gen4` with the kind tables per selector index: `seedOpsG`, `finalOpsG` (one zero-tail per distinct `m`, gated), `merkleOpsG`, `segPtOpG` (`packFK`), `posOpsG`, `genPhaseG`, `skeletonG`. `groupFinP`. `fieldOffT`, `relocT`/**`relocT_eq`**, `finOps4F`/**`finOps4F_eq`**: a relocation by table. **`progNodeG`**, **`progSegG`**, `progG_fin`. Controls `grp_ctl`, `grp_bytes`, `merkleOpsG_ctl`. |
| `FRNodeRows4` | yes | **Slots, prototypes, copies.** `mapC`, `rowMapC`, `ev_mapC`, **`holds_rowMapC`**. Selector cells: `selIx`, `selCells4`. Per-slot region: `oneR`, `selR`, `baseR`, `protoP`. Slot assignment: `isPrevSlot`, `protoOf`. Prototypes: `protoProg` (node prototype at `cells4 .N4`), `protoLay`, `protoCS`, `protoRows`. Moves: `mvC`, `mvRows`, `absRows4`, `slotRows4`. Link rows: `linkRows4`, `linkIRows4`. **`nodeIRows4 κ`**; `lBitCells4`, `lRows4`. Facts: `oneCell_eq` (`3·2^logM`). Controls `protoOf_ctl`, `mvC_ctl`, `selCells4_fit`, `regions4_fit`, `linkRows4_length`. |
| `FRNodeRows4Plan` | yes | **The plan and `evalM`.** `planData4`/**`planData4_rows`**: S-E13's construction for two programs, with one grouping. Region check: `pieceInB`/`pcIn_spec`/`InSlot`. `lowKeys`. `Plan4`, `mkPlan4`, **`planOf4`**. Prototype values: `tb4`, **`kprep_star`**, `kp_shared`, `protoV4`/`protoV4_eq`. The copy identity: `starPt`, `gN_star`, `hiF`, `gN_row`, `gN_cell`, `copy_term`, `copy_row`, **`copy_val`**. Evaluation: `slotV4`, `protoRowsP`, `nodeIRowsP_eq`, **`evalMT4`**, `evalMS4`, **`evalMT4_eq`**. Controls `star_ctl`, `pieceInB_ctl`. |
| `FRVIRCompile` | edit | `stepsAhead` counts `askNode`, not `piDigest fSibs`. This hint affects performance only, and it gives the same count for 3.x's programs (§2). |

Line counts, the axiom log and the source rule are in §6.

### The design (BLUEPRINT §4.4 applied to 1 + k slots)

**Regions.** Slot `σ` owns M-relative rows and cells `[σ·2^20, (σ+1)·2^20)`. M's first cell is
`κ.oneCell = 3·2^logM`.
- Cell `σ·2^20` is the slot's own `one`; slot 0's is M's `one` itself.
- The next three cells are its selector copies.
- The slot's program is compiled from `σ·2^20 + 4`.
- Only the **link rows** leave the region. There are at most 7 per slot, at the region's last 8
  rows: `one′ = one`, `s′_ι = s_ι` (the L bit) and the three one-hot products.

**Copies.** There are two programs, so there are two prototypes: the previous-node mux at slot 0
and the segment mux at slot 1. Every slot of every kind is a prototype moved by
`(σ − π)·2^20`.
- **Soundness is per slot.** `holds_rowMapC`: moved rows hold at `w` iff the prototype's rows hold
  at `w ∘ move`. So `compileT_sound` of the prototype applies to slot `σ`'s child.
- **Evaluation needs one pass per prototype.** Each entry of a copy has its row and its cell in
  the same region, so
  `MLE(slot σ) = eq(τ_[20,lm), σ)·eq(u_[20,lm), σ)·u_lm·u_lm+1 · MLE_lo(prototype)` (`copy_val`).
  The existing 21/23-bit evaluator computes `MLE_lo`.
- **The plan is kind-independent.** N2, N4 and N8 share the same two prototypes, so a verify
  process builds the plan once.

**The region facts** (`InSlot`) are checked once per process on the pieces (`pieceInB`), and
`lowKeys` is checked with them. If a check fails, `evalMT4` falls back to the sparse sum, which is
also proved. In the measured plan both checks pass (`inR true`).

## 2. Measurements

| What | Value | Log |
|---|---|---|
| program generation (each group) | 390 ms → **37 ms** (`kt`, hoisted offsets, `relocT`) | `comp4-N4-2.log` |
| compiled prototypes | node mux 106,242 ops, seg mux 106,085; skeleton 134,614 / 139,030 rows; 26.6 k imports; 11 / 79 foreign flags; 3,032 instances each (the 745 level `tensorW`s are now templated) | `comp4-N4.log` |
| layout rows per prototype region | **551,805 / 551,805** (indexed 487,301 / 486,597); cells 190.7 k / 190.5 k | `nodedump4-run.log` |
| pieces | 6,405 + 6,407; instances 5,395 + 5,395; sparse rows 40,745 + 36,557 (55,823 + 64,453 before the alignment fix); 100 shared keys | `plan4t` run, task `b0ypqr6bh` |
| **`evalMT4`** best (median) | N2 83.3 (84.8), **N4 83.7 (84.2)**, N8 57.5 (58.9) ms | same |
| 3.x on the same core | V (N30) best 179.1, median 187.3 ms; `evalMT` (two slots) ≈ 75 ms | `vtime-N-base-1.log`, `vtime-rows-base.log` |
| **process start with `planOf4`** | **2.54–2.73 s** (import-only start without the plan: 0.34 s) | `init4-q1/2.log`, `init4-f1/2.log` (on `60b65cc`), `ifrnoderows4-1.log` |

The **alignment fix** (`stepsAhead`). 3.x's position hint counted `piDigest fSibs`, but 4.x's
absolute addressing reads sibling digests as `piDigest 0`. Every Merkle position was therefore
unaligned and stayed sparse. With the fix, `evalMT4` (N4) went from 158 ms to 84 ms.

**A closure trap** (for the next agent, in the same family as S-E13's kernel trap). In
`planData4`, a `filter (fun k => !ks0.contains k)` with `ks0` derived from the first compile was
specialised by the compiler into the filter loop, and it recomputed the compile once per key. The
generated C showed `compMS` inside `List.filterTR_loop…planData4_spec`, and process start was
10.4 s. The fix was `keyCounts (z1 ++ z0)`.

## 3. V for N4 (item 6)

`V(N4) ≈ V_3x − evalMT_3x + evalMT4(N4)`. Best: `179.1 − 75 + 83.7 ≈ 188 ms`. Median:
`187.3 − 75 + 84.2 ≈ 196 ms` (VM, core 27, load ≈ 5).

At the measured ratio 1.19 this is **≈ 158–165 ms on the 7763**, against the 206 ms cap. The 230 ms
kill line is not hit.

**This is a projection, not a measurement.** It assumes the rest of V at N4's sizes (Lr 17, E2 23,
E4 25 rounds against 15/21/23) is close to N30's. Measuring V needs `implN .N4`: `evalM :=
evalMT4 planOf4 .N4` plus the node's `evalL`, `targetS`, `linkWAll` and `shiftMask` on the 4.1
layout. That is the next pass's item 2.

## 4. Consequences for `R` (item 3)

The child of slot 0 is N2, N4 or N8. All three share the two prototypes, and they differ only in
which prototype sits at which slot and in their M base. So `R` evaluates **two** prototype
structures plus selector-linear slot weights `Σ_ι s_ι · W_ι(τ, u)`. These are linear forms over
the kinds' slot assignments, which are constants.

S-E9's per-structure classes are 193 k rows, or about 64 k with the levers. Estimate for `R`:
`2 × 193 k + 48 k tables + 30 k keys + 9 k + 26 k D̂ ≈ 500 k` rows. With the sparse-skeleton
templating and the instance AP it is ≈ 240 k.

## 5. Rows (item 4, arithmetic; the Lean `mRowModel4` is open)

Per slot region (2^20 − 8 rows), using the measured prototype rows (≈ 545 k) and the changes-24
unbound items:

- **previous-node slot:** ≈ 552 k + `R` ≈ 240 k (with levers) + `rsWeight` 45.6 k + kind factor
  68.5 k + `targetSNode` 16 k + `linkWAll` 15 k + `evalL` 10 k + `shiftTarget` 1.3 k ≈
  **948 k** (1.11× under 2^20).
  - **Without the `R` levers it is ≈ 1.2 M and does not fit one region.** The fallback is to give
    the node slot two regions: N2 has 4 regions for 3 slots, N4 8 for 5.
- **segment slot:** ≈ 552 k + `rsWeight` 45.6 k + `shiftTarget` 1.3 k + the segment `targetS`
  and `shiftMask` (small) ≈ **599 k**.
- per node, plus 2 × 2,788 WOTS rows and the link rows:
  - N2 ≈ 948 k + 2 × 599 k ≈ 2.15 M of 2^22 (1.95×);
  - N4 ≈ 3.34 M of 2^23 (2.5×);
  - N8 ≈ 4.79 M of 2^23 (1.75×).

**Kill rule.** Under each kind's own `N_M/1.05` (3.99 M / 7.99 M), nothing is hit.

**The literal "2^21/1.05 per node at m = 32" (1.997 M) is exceeded** by N2, N4 and N8. That bound
is 3.x's two-slot `N_M`. I read the rule's "(or the kind's own M size)" as the operative bound; this
reading is for the orchestrator to confirm.

## 6. Checks (on HEAD `60b65cc` plus this track's modules)

- **Build:** `lake build FR` plus `FRNodeRows4Plan` plus the probes is green, 4,763 jobs. No `sorry`.
- **Axioms** (`axioms.log`, `ax/AxE12b.lean`): 16 theorems, including `evalMT4_eq`,
  `planData4_rows`, `copy_val`, `relocT_eq`, `finOps4F_eq`, `holds_rowMapC`, `nodeIRowsP_eq`,
  `kp_shared`, `pcIn_spec` and the controls. Each uses only `propext`, `Classical.choice` and
  `Quot.sound`, or a subset of them.
- **Source rule:** 257 files, 0 findings (`source-rule.log`).
- **Loc** (core `loc.py`, `loc.txt`), code / total:

  | Module | Code | Total |
  |---|---|---|
  | `FRVIR4Mux` | 156 | 254 |
  | `FRNodeRows4` | 66 | 168 |
  | `FRNodeRows4Plan` | 377 | 505 |

  That is 599 code lines and 43 theorems. `FRVIRCompile` changed by +3 lines.
- **Re-measured on `60b65cc`:**
  - `evalMT4`: N2 81.6, N4 83.4, N8 57.4 ms best;
  - process start: 2.64–2.73 s;
  - `inR` true.
- **Not done (§7, item 0):** sequential profiles of the three new modules.

## 7. Handover: the remaining items, in order

0. **Close this pass.** Run the sequential profiles: `prof.sh` with
   `MODS="FRVIR4Mux FRNodeRows4 FRNodeRows4Plan FRVIRCompile"`, after re-pointing `prof.sh` to
   `../S-E12b/`. Then write the dump's P2 README.
1. **The coordinator's interface (S-E12a, `60b65cc`).**
   - Instantiate `SlotIface4` with `lrows := lRows4`, `irows := nodeIRows4`, and per slot:
     - `imp`/`rep`/`tpl` from `compileT_sound`'s hypotheses at the prototype, moved by
       `holds_rowMapC`;
     - the selectors `s′` as linked by `linkRows4`;
     - `soundN`/`soundS` from the prototypes' `compileT_sound` at the moved assignment.
   - Prove **`hRes : StmtN4 → NodeResid4`** item by item: `imp`, `rep`, `tpl`, `selP`, `slotP`,
     `selA`, `pack`, `chainMsg`, `aggFmt`, `aggTr`, `aggChk`, `kOk`, `aggPad`, `wots`.
   - **Missing row:** the one-hot rows only give "at most one". `selA` (activity = `[σ ≤ k]`) needs
     a row `Σ_ι s′_ι = act_σ` linked to `k`. Add it to `linkRows4` once S-E12a's `kA` names the
     cell.
   - Prove **`HFit4`** via `hfit4_of`. `nodeIRows4`'s indices are increasing per region. Within a
     prototype, the layout's groups follow the skeleton. Check that the proof or a certificate of
     strictly increasing indices is cheap (no `decide` on the list).
   - **The semantic gap of deviation 1:** `exec`'s `hashStmt` uses `stmtDigest ι`. For the node
     group (indices `L32`/`P30`) it would hash a leaf statement. `soundN` needs either an exec with
     the group's kind type, or `hashStmt` taken as an import (it is one in the rows).
2. **Plan ≤ 2 s** (now 2.5–2.6 s). Levers:
   - The compile pass is 190–340 ms against 3.x's 150 ms. Profile the 4.1 programs' compile: the
     finals' `packFK` tables and the tensorW aux.
   - `kms` 192 ms: build only the keys the layout needs.
   - Run patterns from prototype 0 only: −90 ms, at a small V cost.
   - The region check (91 ms) by proof.
   - Then **`implN .N4`** and a measured V (S-E8's method).
3. **The templates of every unbound import** (item 2 of the task): the pack map and the `input w`
   alias; the WOTS mux rows; the kind-factor and `free`-term templates (INT-5 §10); the τ-ops on
   18/23 coordinates; `tplTargetSNode`, `tplLinkWAll`, `shiftMask`; `rsWeight`; `evalL`'s replay
   (over `lRows4`); the segment's `lastOps`/`targetS`/`shiftMask` (S-F4 §6).
4. **`R`** with the two-prototype structure (§4) and the levers.
5. **`mRowModel4`** in Lean with `mRows_le` per kind (the §5 arithmetic) and the dumps' "For P2"
   README.

## 8. Deviations and edit requests

1. **The group's finals take the representative's counts.** `FinP`'s `lrR`, `e2R`, `e4R`, `mB`,
   `nc` and `cells` are scalars, so `groupFinP` uses N4's and L32's counts.
   - This is exact for N4, N8 and L32.
   - For N2, L30 and L31 the op structure is the representative's.
   - **Edit request (`FRVIRFinals4`, S-F4):** make these fields kind tables (`Kind → ℕ`) and pad
     the points to one length with the zero register: `packFK` with equal lengths, as revision
     3.15 did for `τ`. Then `gen4 (G ι) fin = specialize ι (gen4G G fin)` can be stated, and S-G's
     relations transfer.
   - The same request applies to the previous-node finals' `cells` (`cells4 κ` per kind, also a
     table).
2. **`finalOpsG`** reads one tail per distinct `m`. So `gen4G` is not literally `gen4` at a fixed
   kind (2 to 3 more registers).
   - **Edit request (`FRVIR4`, S-0′):** give `finalOps4` this shape, so that the per-kind programs
     are the group program at a fixed index.
3. **`stepsAhead`** (`FRVIRCompile`) changed. It is a performance hint only, and 3.x's rows are
   unchanged.
4. **`FRNodeLayout4` is unchanged.** The track uses its `oneCell`, `lBase` and `mBase`, which
   S-E12a's `nodeLayout4` also uses. Its H tail (70,957 / 117,593 / 187,548) rounds to the same L
   base.
5. **The one-hot rows give "at most one".** The activity sum is open (§7, item 1).

## For P2 (provisional; the dump's README is item 0)

- Each node kind's M is its prototypes' rows moved per slot (`node-N*.txt`: slot → prototype, the
  shift, the link rows).
- Prototype files `mrows-p0/p1`, `groups-p*`, `mregs-p*`, `maux-p*`: cells are M-relative
  (absolute = `κ.oneCell + cell`), and rows are absolute M rows.
- In each slot the prover writes:
  - the slot's `one′` (`= 1`);
  - its selector copies (`=` the L selector bits);
  - its program's witness at the moved cells.
