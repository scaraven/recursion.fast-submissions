# S-E13 (track L-circ): RESULT — the plan build ≤ 2 s per process

Stage S-E13, 2026-10-28, HEAD `9d75d0e` (blueprint 4.1; re-verified on `e1a2444`). Build tree `logs/fr-build-SE13` (a copy of
`fr-build-INT6`, against `logs/org20`; `snap.sh` symlinks the L-circ modules in `MINE.txt`, probes in
`probe/`). Baseline tree for V: `logs/fr-build-SE13base` (HEAD's sources). Logs in `logs/S-E13/`;
journal `S-E13-JOURNAL.md`. Every lean/lake/probe command ran in a 16 GB scope with a timeout; probes
on one idle core (26). Nothing is committed.

## Status

| Item | State |
|---|---|
| Plan build ≤ 2 s per process (B-16, lever 1) | **Done.** Process start with the node plan **49.9 s → 1.87–1.98 s** (`coldwarm init`, `main` does nothing; `final2-coldwarm-init-*.log`); `planOf` alone 1.63 s (`planm-6.log`); 0.29–0.32 s of the process start is there without the node plan (`final-init-noplan-*.log`). |
| `Plan.ok` by proof, not by comparing 2 × 428k rows | **Done**: `slotRP_rows`, `toPiece_rows`, `piecesOf_rows`, `planData_rows`. |
| Slot symmetry | **Partly**: slot 1 reuses slot 0's layout (shifted, when it fits) and template memo, so it costs one compile pass, not two. The compile of slot 1 itself is not derived from slot 0's (deviation 2). |
| `evalMT_eq`, `implC_meets`, `acc_eq` | Statements unchanged. |
| V must not regress | **Unchanged**: alternating runs, same core and method (`vtime-N-base-7..9`, `vtime-N-final-7..9`): best 184.4 / 175.3 / 184.2 ms (mean 181.3) against HEAD's 182.1 / 178.3 / 185.2 (mean 181.9). `evalMT` best 71.1 ms against the old plan's 73.7 (`evcmp-6.log`). |
| Cold first check vs warm | cold 196.3 ms, warm 182.2–201.6 ms (`final-coldwarm.log`): no plan cost in the first check. |

## 1. Where the 49.9 s went, and what removed it

Process start, core 26 (`base-*.log`, `fix*-*.log`, `coldwarm-init-*.log`, `planm-*.log`):

| Step | Process start | What |
|---|---|---|
| HEAD | 49.9 s | `planOf` 45.5 s + 4.4 s of other closed terms |
| template generators | 12.3 s | `tplShiftMask` rebuilt its four tables per entry (1.5 s per construction, ≈ 6 per slot); `tplRowW` rebuilt `lagG`/`eqTblG` per product (4.1 s at init). Fixed by building them once (`tplShiftMaskF = tplShiftMask`, `rowWGF = rowWG`, both `rfl`); the walk builder now pushes in place; `tplWalk14RB/CB` read the closed rows. |
| proved pieces (`FRVIRTplBuild`) | 3.06 s | no `slotIRows`, no `eqL`, no compile replay, no row materialisation for instances; a template memo in the compile; slot 1 at slot 0's layout |
| `CS.tcnt`, skeleton matching | 2.21 s | `tcount` from a per-key table (1.46 M key comparisons per pass); skeleton blocks matched against known templates, so every piece check compares pointers |
| grouping, key-first memo | 1.93 s | `inputKindsF`, `ownIdx`; each template built once in the first pass |
| template block matching | 1.84–1.88 s | `reMatch` for the walk's `G` blocks and the 64-row chunks |
| run patterns from both slots (V parity) | **1.87–1.98 s** | slot 0's alone cost `evalMT` 1.5–2.5 ms (`evcmp-3..5.log`); `mkPats` over both slots is S-E11's heuristic, +80 ms here |

`planOf`'s parts (`planm-4.log`, both slots; the run patterns then from slot 0's pieces):

| Part | ms |
|---|---|
| gen | 22 |
| compile, slot 0, first pass (`compMS []`) | 184 |
| per-key data (`kmsOf`: rows, bits, split heads/tails, blocks) | 119 |
| compile, slot 0, with the layout | 158 |
| slot 1 (compile at slot 0's layout, fits) | 153 |
| proto-pieces, slot 0 / slot 1 | 207 / 207 |
| grouping (`groupRP`, untrusted) | 155 |
| pieces with their checks, slot 0 / slot 1 | 34 / 37 |
| keys, `Key.ok` | 20 |
| run patterns (slot 0's pieces; both slots' since: 163 ms, `planm-6.log`) | 85 |
| prepared pieces | 49 |
| **`planOf`** | **1,606** (old `planOfChk` in the same process: 12,226); final, with both slots' patterns: **1,629** |

Other process start: 0.28–0.30 s without the node plan (`init-noplan-*.log`; the walk's closed
template ≈ 0.2 s of it), L's plan 54 ms (`init-l.log`). One compile pass is 101 ms without templates
and 119 ms with memoized templates (`compb-2.log`); three passes remain per process.

## 2. What was built (code lines, core `loc.py`, HEAD → now)

| Module | Code | Change |
|---|---|---|
| `FRVIRTplBuild` (new) | 1,073 | The construction and its proofs (§3), the grouping (`groupRP`, `inputKindsF`, `ownIdx`), controls. |
| `FRVIRTplFast` | 415 → 576 | `shiftLay`, `tinKeys`, `slotLayOk`, `slotLay0`, `slotLayS`; **`slotLay` changed** (deviation 1); `kmsOf`, `infoOf`, `slot1Of` (`withLay`, `comp1`, `lay1`, `slot1Own`, `slot1Pick`); `planData`, `planData_rows`, `slot1Of_spec`; `mkPlanF`, `planOfD`, **`planOf`**; `planOf_lay`, `planOf_cs`, `nodeIRows_planOf`; the old construction kept as `planOfChk`. |
| `FRVIRCompile` | 846 → 885 | `CS.tcnt` (a per-key count table), `CS.tcount` reads it, `bumpCnt`, `CS.TcOk`, **`compileX_tcount`** (it is the instance count), `tcount_ctl`. |
| `FRVIRTplExt` | 435 → 439 | `tplOf (.shiftMask …) = tplShiftMaskF`; `cbitsOf`, `cbitsOf_rows`; the walk's row and cell bits from its closed rows; `tRbits_eq` by rewriting (an `rfl` made the kernel evaluate the walk). |
| `FRVIRTplMask` | 191 → 209 | `mEntT`, `mProdsT`, `mSPT`, `tplShiftMaskF`, `tplShiftMaskF_eq` (`rfl`). |
| `FRVIRTplRep` | 117 → 123 | `rowWGF`, `rowWGF_eq` (`rfl`); `tplRowW := rowWGF 2^14`; `tplRowW_ok` re-proved through it. |
| `FRVIRTplDag` | 140 → 146 | `emit`, `padTo`, `dmul`, `dacc` read the other fields before pushing (in place). Definitional; `FRVIRTplWalk` unchanged. |

## 3. The proof architecture

`Plan.ok` is unchanged: the pieces' rows are `slotIRows (lay σ) oneL off (cs σ)`. It is now proved:

1. **Proto-pieces** (`RP`: sparse rows, or a raw instance `T, ins, X, cb, A, B` whose rows are
   `instIR T one ins X cb`, not stored). **`slotRP_rows`**: for *any* compiled state, layout, block
   list and known-template list, the proto-pieces' rows are `slotIRows`:
   - `skelRP_rows`: the skeleton's blocks and gaps cover its rows in order (blocks out of order or
     range are skipped); a block is matched against a known template (`absMatch_inst`) or abstracted
     (`absRowsV_inst`; the cell lookup is confirmed against the array, so no `HashMap` lemma is needed);
   - `tinRP_rows`: a template instance is its whole rows, its split head and tail (`splitRow_lo`,
     `splitRow_hi`), or its blocks and the rest (`blk_rows`; each block matched, `reMatch_inst`, or
     re-templated, `reT_inst`); the per-key data are `mkKM`'s (`kmOf_map`, `keyInfo_eq`).
2. **The check** (`toPiece`): the untrusted grouping proposes a key `k` and own inputs; the instance is
   kept iff the bits and alignment agree, the proto-piece's template **is** the key's
   (`withPtrEq T g.T (T == g.T)`: one pointer comparison, since a template's instances share one
   object), and every input below the key's bound reads, under the key's rewrite, the instance's form
   (`insOk`, cost = the key's input count). The bound is a field of `GK` with its proof (`GK.hn`), so
   the grouping cannot give a wrong one. **`toPiece_rows`**: a piece has its proto-piece's rows,
   whatever was proposed; `piecesOf_rows` for a slot.
3. **`planData_rows`**: the compile passes are `compileT`'s (`compMS_eq`: the memo holds `tplOf`'s
   templates; the blocks it records are hints), the layouts are `slotLay`'s (`mkLayI_eq`,
   `slot1Of_spec`).
4. **`planOf`** builds the `Plan` at `lay := slotLay fin`, `cs := slotCST fin` (`planOf_lay`,
   `planOf_cs`, and **`nodeIRows_planOf`** for S-G's `truthE`).

**Kernel trap (recorded for the next agent).** A proof step that leaves the kernel to reduce a
projection of `bif c …`/`if c …` where `c` is a computed guard (`slotLayOk (compileT …) …`) makes the
kernel *evaluate the compile*: 60–270 s of type checking. `unfold`/`dsimp` over a `let`-bound choice
and `cases h : c` both triggered it. Fix: the choice is spread over small definitions (`slot1Pick`,
`withLay`, …) and the proofs rewrite with their equations and `Bool.apply_cond` only. Likewise `rfl`
on `(mkPlanF …).cs = slotCST fin` sent the elaborator into `gen` (`dsimp only` first).

## 4. Controls

| Definition | (+) | (−) |
|---|---|---|
| `insOk` | `insOk_pos` | `insOk_neg` (another cell than the local's), `insOk_neg_own` (another own form) |
| `toPiece` | `toPiece_pos` (an instance) | `toPiece_neg` (another template: rows kept), `toPiece_neg_own` |
| `maxInp`/`GK` | `maxInp_ctl` (`inp 3` gives 4), `maxInp_spec` | `maxInp_ctl` (locals do not count) |
| `absMatch` | `absMatch_ctl`, `absMatch_inst` | `absMatch_ctl` (a local at another cell) |
| `reMatch` | `reMatch_ctl`, `reMatch_inst` | `reMatch_ctl` (another local) |
| `absRowsV`, `reT`, `mkBlk` | `absRowsV_inst`, `reT_inst`, `mkBlk_inst` | — (equalities) |
| `CS.tcnt`/`tcount` | `tcount_ctl` (two instances count 2), `compileX_tcount` | `tcount_ctl` (an absent key counts 0) |
| `shiftLay`, `slotLayOk` | `shiftLay_ctl`, `slotLayOk_ctl` (fits when shifted by `d`) | `slotLayOk_ctl` (another row count; another shift) |
| `compMS`, `mkLayI`, `keyInfo`, `kmOf` | `compMS_eq`, `mkLayI_eq`, `keyInfo_eq`, `kmOf_map` | — (equalities) |
| `tplShiftMaskF`, `rowWGF`, `cbitsOf` | `tplShiftMaskF_eq`, `rowWGF_eq`, `cbitsOf_rows` (`rfl`) | — |
| `planOf` | `planData_rows`, `nodeIRows_planOf`; measured: `evalMT` equal to `planOfChk`'s at 5 random points (`planm-*.log`) | `coldwarm-1.log`: the cold check is not slower by any plan cost |

## 5. Checks

- **Build:** `lake build FR FRNodePlan FRNodeDag` green in `fr-build-SE13`, 2,425 jobs, no `sorry`
  (`build-final.log`, HEAD `9d75d0e`); **re-snapshotted on HEAD `e1a2444`** (P4a/P4b, whose `truthE3_iffI`
  states over `nodeIRows (planOf fin)`): green, 2,438 jobs, no `sorry` (`build-final-head.log`).
  `FRNodeCircuit` (which unfolds `slotLay`) builds unchanged.
- **Axioms** (`axioms.log`, `ax/Ax.lean`): 51 names — `acc_eq`, `implC_meets`, `implCWith_meets`,
  `implC_implT`, `compileT_sound`, `tplExt_ok`, `node_m_sound`, `evalMT_eq`, `evalLT_eq`, `implCN_eq`,
  `tplShiftMask_ok`, `tplRowW_ok`, `tplWalkAB_ok`, every new theorem and control above. Only
  `propext`, `Classical.choice`, `Quot.sound`; some use none.
- **Source rule:** 212 files, 0 findings (`source-rule.log`; the count includes S-0′'s new files).
- **Sequential profiles** (one core, `Elab.async=false`, `profile-*.log`):

  | Module | wall | type checking | tactics |
  |---|---|---|---|
  | `FRVIRTplBuild` | 16.5 s | 0.73 s | 2.61 s |
  | `FRVIRTplFast` | 10.3 s | 0.18 s | 1.00 s |
  | `FRVIRCompile` | 30.6 s | 1.10 s | 8.22 s |
  | `FRVIRTplExt` | 10.3 s | 0.22 s | 1.60 s |
  | `FRVIRTplMask` | 10.0 s | 0.33 s | 1.63 s |
  | `FRVIRTplRep` | 9.0 s | 1.26 s | 0.27 s |
  | `FRVIRTplDag` | 11.4 s | 0.23 s | 2.04 s |
  | `FRNodePlan` | 5.9 s | 0.00 s | — |

  (`FRVIRTplRep`'s 1.26 s is `rowWGF_eq`'s `rfl`.)

## 6. Deviations

1. **`slotLay` changed.** Slot `σ ≥ 1` takes slot 0's layout with its cells shifted to the slot's base
   when the slot's compile with it fits (`slotLayOk`: the same rows, cells and instance sequence as
   slot 0's first pass), else its own `layOf`. On the node it fits (`slot1Of … fits true`), and the
   layout is the one `layOf` gave (the groups' row and cell bases differ by `2^20` cells only). The
   layout only places instances; `compileT_sound` holds for every layout, and `FRNodeCircuit` builds
   unchanged. It spares one compile pass per process.
2. **Slot symmetry is not proved.** Slot 1 is compiled (one pass, with slot 0's layout and template
   memo): 153 ms. Deriving it from slot 0's would need a renaming lemma for `compileT` over every op
   (`opOut`'s ≈ 50 cases and `tplExt`'s 17); the saving (≈ 150 ms compile + ≈ 200 ms proto-pieces) was
   not needed for ≤ 2 s.
3. **The run patterns** are S-E11's heuristic over both slots' pieces (`mkPats`). From slot 0's
   pieces alone they cost 80 ms less to find but `evalMT` 1.5–2.5 ms more (`evcmp-3..5.log`).
4. **Template generators** (`FRVIRTplMask`, `FRVIRTplRep`, `FRVIRTplDag`, `FRVIRTplExt`) were made
   to build shared data once. Each is `rfl`-equal to the old definition, or definitionally the same
   state update; no template statement changed.
5. **The compiler state has a field more** (`CS.tcnt`). Compiled values are unchanged
   (`compileX_tcount`; `evalMT` equal to the old plan's).
6. **`withPtrEq`** (Lean core) is used in the check; its value is `T == g.T` by definition.
7. `planOfChk` (the S-E11 construction) is kept for the dev probes' comparison.

## 7. Open questions and notes for other tracks

- **S-G12′**: `nodeIRows_planOf fin : nodeIRows (planOf fin) = slotIRows (slotLay fin 0) oneL 0
  (slotCST fin 0) ++ slotIRows (slotLay fin 1) oneL slotM (slotCST fin 1)`; `planOf_lay`, `planOf_cs`.
- **S-0′ (N2/N4/N8)**: everything here is parametric in `fin`/`gen`. The `Plan` has two slots
  (`pc0`, `pc1`); `1 + k` slots need `planData` per slot (the per-slot steps are already functions of
  the slot) and `slotLay` for `σ ≥ 1` already handles any slot. If a sub-slot's program differs from
  slot 0's, `slotLayOk` fails and that slot pays its own two passes (≈ 150 ms more).
- **Further levers**, if a larger node needs them: slot symmetry (≈ 350 ms); materialising the
  skeleton blocks from the array without lists (≈ 40 ms); the run-pattern search (85 ms).
- **Blueprint** (next revision): §4.4's plan text: the plan is built at process start in ≈ 1.6 s
  (process start 1.84–1.88 s on the VM), by proof (`planData_rows`), no run-time row comparison.
