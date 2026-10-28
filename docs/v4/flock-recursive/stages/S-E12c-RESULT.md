# S-E12c (track L-circ): RESULT, pass 1. The 4.1 node rows: equivalence obstruction, plan < 2 s, `hfit4`, activity rows, row model, V(N4)

Stage S-E12c, 2026-10-28. Base HEAD `4919027`. Build tree `logs/fr-build-SE12c` (a copy of
`fr-build-SE12b` with the probes `Plan4T`, `PlanM4`, `Init4`, `NodeDump4`, `Gen4T`, S-E8's `VTime`,
and the new `LayDump4`, `VTime4`), against `logs/org20`. Logs are in `logs/S-E12c/`; the journal is
`S-E12c-JOURNAL.md`. Every lean, lake and probe command ran in a 16 GB scope with a timeout. The VM
was loaded (load 6–10) throughout; timings are best-of-n on one pinned core. Nothing is committed.

**This is a multi-pass track.** §8 is the handover.

## Status

| Item | State |
|---|---|
| 0. Profiles of S-E12b's modules; P2 README | **Done** (§6; `logs/S-E12c/nodedump/README.md`, dump regenerated at this pass's rows). |
| 1. `SlotIface4`, `hRes`, `HFit4` | **`soundN`/`soundS` blocked: the group programs are not equivalent to `gen4 κ` (§1, four exact obstructions), per the ruling reported, not worked around.** Done: **`hfit4 : HFit4 nodeIRows4`** (unconditional, no row evaluation); the **activity rows** and the selector parts of `selP`/`selA` (`selP_sel`, `selA_sel`); `ActK` states the pack map's tie to `k`. The other `NodeResid4` items need the concrete reader (S-E12a D6) and the templates/R (items 3–4). |
| 2. Plan ≤ 2 s; `implN .N4`; measured V | **Plan: process start 1.80 / 1.85 / 2.03 s** (from 2.82 s at the same load; S-E12b: 2.54–2.73 s at load ≈ 5). **V(N4) measured: 213–223 ms best, 231–241 ms median on the VM** (§3), with `evalM = evalMT4` and 3.x stand-ins for the node's `evalL`, `targetS`, `linkWAll`, `shiftMask` (their 4.1 versions do not exist). |
| 3. Templates of the unbound imports | Not started. One of them is forced by obstruction 4 (`shiftMask`). |
| 4. `R` | Not started. The row model gives the previous-node slot one region with `R`'s levers (§5). |
| 5. `mRowModel4` | **Done** (`FRNodeRows4Model`: `mRows4_le`, `mRowModel4_eq`, `mRows4_neg`). |

## 1. Item 1: the group program at a fixed index is not `gen4 κ`

`soundN` must turn the rows of slot 0 into `runIR (implN κ') (progNode κ' (cells κ'))` accepting,
`κ' = nodeGrp ι` at the selected index `ι`. The rows give, through `compileT_sound`, a run of the
**compiled** program `progNodeG` at exec kind `ι` under an `impl` with `ImplT impl`. So the bridge
is "the group run at `ι` accepts ⇒ `gen4 κ'`'s run accepts". I checked this against `exec`/`evalOp`,
`VnodeC`/`VsegC`, `implSeg`, `tplExt`/`ImplT`, S-F4's op dumps and S-E12b's prototype dump. **It is
false at four places:**

1. **The finals differ in op count per kind.** `FinP`'s `lrR`, `e2R`, `e4R`, `mB`, `nc`, `cells`
   are scalars, and `finPf`'s point families have `mB`-dependent lengths. The dumps (`logs/S-F4/
   dump/ops-*.txt`) have `N2` 106,221 ops against `N4`/`N8` 106,240, and `L30` 106,064, `L31`
   106,072, `L32` 106,081. The constructor sequences agree up to op 102,101, then `mulKF`, `addK`,
   `getK`, `mulK` are inserted.
   - Registers are positional (`exec` appends), so no choice of kind tables makes one op list equal
     each kind's at its index.
   - `groupFinP` takes the representative's counts, so at index `P30` the group runs `N4`'s finals
     on an `N2` proof. For example E2's `eqPt` is over 23 coordinates where `N2`'s is over 22: an
     extra factor `eq(x, y)` at a dummy round, which is not `1` in general.
   - `cells` enter `gCellsOps` as register choices, so `N4` and `N8` (with their own `cells4`)
     differ in register arguments as well.
2. **The final message's tail.** `finalOps4` reads `piField 0 (fo + 2^(m−25)·32) len_m`. Its
   offset and length depend on `m`, and `piField` has no kind table. `finalOpsG` reads one tail
   per distinct `m`, which shifts every later register against `gen4`'s.
3. **`hashStmt` at the index.** `evalOp (.hashStmt s) = stmtDigest κ` is `nodeStmtF` only at
   `.N30`. The node group at `L32` (`N4`) and `P30` (`N2`) computes a leaf statement, and the
   segment group at `N30` (`L31`) a node statement.
   - The `assertEq` against `c` then checks another relation.
   - An honest witness also cannot meet `compileT_sound`'s import hypothesis for this register.
     That hypothesis asks the cell to hold the run's value, and H's `hashStmt` blocks compute the
     other digest.
4. **The `shiftMask` template is 3.x's.** `tplExt` templates `.shiftMask` with `tplShiftMask`, and
   `ImplT` fixes `impl.shiftMask = NodeI.shiftMaskI`, 3.x's node chain mask. Both prototypes
   instantiate it (`groups-p0`: `shiftMask 18 18`; `groups-p1`: `shiftMask 36 18`). `VsegC` runs
   `shiftSegI` and `VnodeC` needs 4.1's mask (`chainLk4`). `finSh` uses the outputs (`keep mk`,
   `mk = vn ∨ node`), so **no** kind of either group is equivalent, independently of 1–3.
   - A smaller point: `implSeg`'s `targetS` reads `κ.isNode`, so at index `N30` it is the node's.
     A kind-blind `impl` at exec time fixes this, since `targetS` and `linkWAll` are not in `ImplT`.
   - `slotW` stays 3.x's `slotWI`, which 4.x also uses (`FRSoundness4P4aFin`, `slotWS`).

**An equivalence-preserving design**, all within L-circ modules, but large. These are the facts for
the coordinated integration the ruling offers:

- **(a) A template set per revision.** `shiftMask` must not use 3.x's template: either an import
  bound per kind, or a 4.1 per-kind template. That means `tplExt`, `ImplT` and `compileT_sound`
  with a filter, and the plan's proofs (`compMS_eq`, `compMS_T`, `slotRP_rows`, `planData4_rows`)
  over it. 3.x's instantiation must stay `rfl`-equal (S-G's `nodeIRows (planOf fin)` statements use
  it).
- **(b) A verified merge of the three kinds' `gen4` programs**, replacing the hand-written `gen4G`.
  - Under per-kind register renamings `f_ι`, ops equal up to tables become one op with tables.
  - The other ops become per-kind copies with their asserts gated to their index. At the other
    indices they are pure (`noAsk_finOps4` exists) and their asserts are off.
  - An untrusted schedule (a diff) aligns the lists.
  - One generic theorem: if the merge's flag is `true`, the merged run at `ι` simulates
    `gen4 (G ι)`'s (`∀ r, rd regsG (f_ι r) = rd regs r`).
  - If the flag is `false`, the slot program is a fixed always-rejecting program. `soundN` then
    holds vacuously, and the kernel never evaluates the merge (S-E13's trap).
  - Needs `Op.mapReg` and its `evalOp` lemma over all constructors, plus the exec simulation.
- **(c) `hashStmt` as an imported fact** (the ruling's option). The merge replaces it by `.input 1`
  and records the fact `stmtDigest tix (π's stmt bytes) = c`, which `imp` carries and H's
  `hashStmt` blocks bind.
- **(d) The tail (2)** falls out of (b) as gated copies.
- **Row cost of (b).** The lists agree structurally up to op 102,101 of about 106,240, so a lockstep
  merge gives tables there. About 4.1 k ops per kind are copied (`finPf`'s tail). The large finals
  templates come before op 102,101: walkAB 85.5 k, phiRS 512 × 134, maskRows 16.4 k, rowW 16.8 k.
- **The alternative** (coordinated): make `progNode`/`progSeg` the group program specialised (FinP
  tables, padded points, `finalOps4` per `m`, `hashStmt` import). This changes `gen4` for R4, P4
  and P2. Obstruction 4 needs (a) either way.

**Done under item 1 (independent of the equivalence):**

- **`hfit4 : N4c.HFit4 nodeIRows4`** (`FRNodeRows4Fit`), with no evaluation of rows.
  - `nodeIRows4 κ` is now `if ProtoFit then (per slot: prototype rows, then link rows) else
    rejectRows κ`. `ProtoFit` says each prototype's rows lie in its region below the link rows,
    with distinct indices. `rejectRows` is the row `one · one = 0`.
  - The plan checks `ProtoFit` on its pieces: the region check, and distinct indices by intervals
    sorted by start (`ivs_nodup`, `idsOkB_spec`). So `Plan4.hR : inR → ProtoFit ∧ lowKeys`. It
    holds (`inR = true`; and the fallback's `fitB`, evaluated on the materialised rows, agrees:
    `plan4t-check.log`).
  - The proof: `slot_mem` (indices in the slot's region; cells below `2^(logM+2)`: M cells below
    `oneCell + vslots·2^20`, L selector bits below `oneCell`); `slot_nodup` (`mvC` is injective on
    the region, link rows by `zipIdx`); disjoint regions.
- **Activity rows** (`actRows4`, part of `linkRows4`, which now has 7 or 8 rows in the region's
  last 8). With `S_σ = Σ_ι s′_ι`:
  - `S_σ = 1` at the previous node's slot and at each aggregate's first sub-slot;
  - `S_σ·(1 − S_{σ−1}) = 0` at a later sub-slot.
  - Without them, slot 0's selectors could all be zero (S-E12b's "at most one").
  - Lemmas: `link_facts`, `selOk_of_act`, `sel_zero_of_act`, `selSum_bit`, `act_first`,
    `act_mono`.
  - **`act_profile`**: under `ActK` (sub-slot `k − 1` active and, below `maxK`, sub-slot `k`
    inactive), exactly the sub-slots `i < k` are active.
  - **`selA_sel`**, **`selP_sel`**: every active slot selects exactly one kind
    (`SelOk (slotAsg κ σ w) (protoP π) ι`).
  - **The tie to `k` is the pack map's (`ActK`).** `F` has characteristic 2, so a row
    `Σ_i S_i = k` would only give `k`'s parity. The tie must pin the boundary from `k`'s bits.
- **How these map onto `NodeResid4`** (for the instantiation):
  - `selN κ v w κ' := ∃ ι, nodeGrp ι = .ofNode κ' ∧ SelOk (slotAsg κ v w) (protoP 0) ι`;
  - `selS` likewise with `segGrp`.
  - `selP`/`selA` then need, beyond `selP_sel`/`selA_sel`, that the selected kind is the read
    proof's (`kindOf4`, `segView`'s kind). That comes from the reader plus the slot's seed check
    (`hdr`'s 16 bytes against the selected kind's constant).
  - **No new `NodeResid4` item is needed.** `ActK` is a pack-map fact inside `selA`'s proof.

## 2. Item 2: the plan

| Part (ms) | before (`planm4-a`) | after (`planm4-b`) | Lever |
|---|---|---|---|
| first compile passes z0, z1 | 210 + 173 | — | layouts as constants (`FRNodeRows4Hint`, printed from `layOf` by `LayDump4`) |
| key data | 134 | 121 | keys from the layouts |
| compile r0, r1 | 239 + 169 | 196 + 181 | the template memo is built here now |
| proto-pieces, grouping, pieces, keys | 195 + 264, 200, 78, 14 | 191 + 216, 163, 75, 13 | — |
| run patterns | 172 | 80 | prototype 0's pieces only (S-E13's lever) |
| prepared pieces | 45 | 43 | — |
| region check | 86 | 37 | each key's shared forms once (`shInB`) |
| index check (new, `ProtoFit`) | — | 70 | intervals, merge sort |
| **process start** (`plan4t init`) | **2.82 s** | **1.80 / 1.85 / 2.03 s** | |

- The import-only start (`init4`) is 1.90 s: `planOf4` is a module-level closed term.
- **The layout is a hint, not a statement.** `compileT_sound` holds at any layout, and the pieces
  are the rows at any layout. A stale layout (after a program change) fails `ProtoFit`'s check,
  which leaves the node unprovable but sound. Regenerate with `LayDump4` then.
- Further levers, if a program change pushes it over 2 s:
  - the index check (70 ms) on runs of consecutive sparse rows;
  - the key data (121 ms) built lazily;
  - building the two prototypes in parallel tasks (the template memo shared first).

`evalMT4` (`plan4t-check.log`, best): N2 84.6, **N4 89.8**, N8 59.5 ms; 83–88 ms in later runs. It
equals the sparse sum over `nodeIRowsP` for all three kinds. Run patterns from prototype 0 cost
little here (S-E12b: 83.7 at load ≈ 5).

## 3. Item 2: V for N4, measured (S-E8's method)

`VTime4`: `runIR implN4 (progNode .N4 (cells4 .N4))` on a synthetic proof of `piSizeOf seq4` bytes
with `N4`'s kind byte. The oracle answers with pseudo-random digests (8,905 queries), and the trace
is replayed with `runSeq`, 21 reps, core 28. `implN4` is 3.x's `implC` with
`evalM := evalMT4 planOf4 .N4`. **Stand-ins:** `evalL`, `targetS`, `linkWAll` and `shiftMask` are
3.x's, because their 4.1 versions are not built.

| Run (same core, alternating) | best | median | Log |
|---|---|---|---|
| 3.x V (N30) | 176.2 / 182.7 ms | 183.5 / 191.7 ms | `vtime-N-base-c1/c2.log` |
| **V (N4)** | **217.6 / 223.5 / 213.1 ms** | 231.1 / 237.6 / 241.3 ms | `vtime4-n4-1/2/3.log` |
| V (N4) with `evalM` ≡ 0 | 125.5 ms | 131.7 ms | `vtime4-n4-noM.log` |

- The split: `evalM` ≈ 88 ms inside V (`evalMT4`). The rest of the 4.1 program at `seq4` is
  ≈ 125 ms against 3.x's ≈ 105 ms, so +31 to +45 ms over 3.x in all.
- **Against `v_ref`** (ratio 1.19): best 179–188 ms on the 7763, median 194–203 ms, against the
  206 ms cap.
- **The VM median (231–241 ms) is at or over the 230 ms kill line; the best (213–223 ms) is
  under it.** The load (6–10) inflates medians. The 4.1 `evalL`/`targetS`/`linkWAll`/`shiftMask`
  can move it either way.
- Next lever: profile the +20 ms in the non-`evalM` part (seq4's larger proof and rounds).

## 4. What was built

| Module | New | Content | Code / total |
|---|---|---|---|
| `FRNodeRows4Hint` | yes | `hintLay0`, `hintLay1`: the prototypes' layouts as constants (generated, `LayDump4`) | 32 / 52 |
| `FRNodeRows4` | edit | `protoLay := hint`; `InSlot`, `inSB`, `linInB`, `idxInB` (moved from the plan); **`ProtoFit`**, `rejectRows`; **`nodeIRows4`** (conditional, noncomputable, slot rows then link rows); `selSum`, `subIx`, **`actRows4`** in `linkRows4`; `actRows4_length`; `linkRows4_length` (7/8) | 85 / 217 |
| `FRNodeRows4Plan` | edit | `planData4` without first passes; `pieceInB` with `shInB`; **`ivOf`, `ivIdx`, `ivsOkB`, `ivs_nodup`, `idsOkB_spec`**; `strictB_iff`, `idxNodupB_iff`, `inSlotB_iff`, **`fitB_iff`**, **`protoFit_iff`**; `Plan4.hR : inR → ProtoFit ∧ lowKeys`; run patterns from prototype 0; `protoRowsP_eq`, `nodeIRowsP` (checked fallback), `nodeIRowsP_eq`; `slotV4` (copy then link); **`evalMT4_eq`** (statement unchanged) | 493 / 655 |
| `FRNodeRows4Fit` | yes | `fitConsts`, `linkCells`, `linkRows4_cells`, `slot_mem`, `slot_nodup`, **`hfit4`**; `slotAsg`, `link_facts`, `selOk_of_act`, `sel_zero_of_act`, `selSum_bit`, `act_first`, `act_mono`, `sub_facts`, **`ActK`**, **`act_profile`**, **`selA_sel`**, **`selP_sel`**; controls | 297 / 381 |
| `FRNodeRows4Model` | yes | `nodeSlotModel`, `segSlotModel`, `wotsRows4`, **`mRowModel4`**, **`mRows4_le`**, `mRowModel4_eq`, `mRows4_neg` | 38 / 83 |

Totals: 945 code lines, 78 theorems (`logs/S-E12c/loc.txt`).

## 5. Item 5: the row model

`mRows4_le` (with `mRowModel4_eq`):

- **The previous-node slot: 948,182 rows** (the measured prototype 551,805; `R` with the levers
  240 k; `rsWeight` 45.6 k; the kind factor 68.5 k; `tplTargetSNode` 16 k; `tplLinkWAll` 15 k;
  `evalL`'s replay 10 k; `shiftTarget` 1.3 k). With the link rows it **fits one region** (margin
  1.106).
- **A segment slot: 600,709 rows** (prototype; `rsWeight`; `shiftTarget`; a 2 k allowance for the
  segment's `targetS`/`shiftMask`). With the WOTS rows (2 × 2,788) in its slack, it also fits one
  region.
- **Per kind:** `N2` 2,155,200 rows of `2^22` (1.95×), `N4` 3,356,634 of `2^23` (2.50×), `N8`
  4,811,312 of `2^23` (1.74×). All are within `N_M / 1.05`.
- (−) `mRows4_neg`: with S-E9's sized replay (≈ 500 k) instead of `R`'s levers, the slot does not
  fit one region. It would take two: `N2` has 4 regions for 3 slots, `N4` 8 for 5.
- Only the prototypes' rows are measured; the rest are S-E12b's estimates.

## 6. Checks

- **Build:** `lake build FR FRNodeRows4Fit FRNodeRows4Model` green, **2,489 jobs**, no `sorry`
  (`logs/fr-build-SE12c/last.log`).
- **Axioms** (`axioms.log`, `ax/AxE12c.lean`): 43 declarations, including `hfit4`, `evalMT4_eq`,
  `planData4_rows`, `nodeIRowsP_eq`, `ivs_nodup`, `idxNodupB_iff`, `act_profile`, `selA_sel`,
  `selP_sel`, `mRows4_le` and every control. Each uses `propext`, `Classical.choice`,
  `Quot.sound` or a subset; one uses none.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 276
  files, 0 findings (`source-rule.log`).
- **Sequential profiles** (`prof.sh`, `Elab.async=false`, one shared core; `profile-*.log`; imports
  ≈ 4 s each):

  | Module | wall | type checking | tactics | peak RSS |
  |---|---|---|---|---|
  | `FRVIR4Mux` (S-E12b's) | 11.7 s | 0.06 s | 0.40 s | 2.68 GB |
  | `FRNodeRows4` | 6.7 s | 0.10 s | 0.07 s | 2.81 GB |
  | `FRNodeRows4Plan` | 11.9 s | 0.56 s | 1.59 s | 2.85 GB |
  | `FRVIRCompile` (S-E12b's edit) | 41.5 s | 1.34 s | 11.9 s | 2.77 GB |
  | `FRNodeRows4Hint` | 6.1 s | 0.00 s | — | 2.77 GB |
  | `FRNodeRows4Fit` | 18.6 s | 1.57 s | 1.44 s | 2.93 GB (simp 6.85 s) |
  | `FRNodeRows4Model` | 6.2 s | 0.01 s | 0.02 s | 2.80 GB |

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `ProtoFit` / `nodeIRows4` | measured: `inR = true`, and the fallback's `fitB` on the materialised rows (`plan4t-check.log`) | `rejectRows_ctl`: the rejecting row fails at `one = 1` |
| `ivsOkB` | `ivsOkB_ctl` (disjoint) | `ivsOkB_ctl` (overlap) |
| `idxNodupB` | `idxNodupB_ctl` (distinct, any order) | `idxNodupB_ctl` (a repeat) |
| `pieceInB` | `pieceInB_ctl` | `pieceInB_ctl` (a cell in another region) |
| `actRows4` | `actRows4_ctl` (pinned-active slots) | `actRows4_ctl` (monotone slots) |
| `ActK` | `act_profile` (its use) | `actK_ctl` (`k = 0`, `k > maxK`) |
| `mRowModel4` | `mRows4_le` | `mRows4_neg` |
| `linkRows4` | `linkRows4_length` | — |

## Deviations and requests

1. **`nodeIRows4` is conditional on `ProtoFit`** (rejecting row otherwise) and noncomputable.
   `evalM` evaluates it from the plan. Blueprint §4.4 should say that the M rows are the compiled
   rows when they fit, checked at process start.
2. **The layouts are constants** (`FRNodeRows4Hint`), not `layOf`. This does not change soundness.
3. **The link rows have the activity row** (7 or 8 per slot, still the region's last 8). A.7 is
   unchanged: no new cell.
4. **Run patterns from prototype 0's pieces only.**
5. **`FR.lean`:** please add `import FRNodeRows4Fit` and `import FRNodeRows4Model` (I did not edit
   it; the build above names them).
6. **S-E12b's edit requests stay withdrawn** (the ruling). §1 is the report the ruling asks for.

## 8. Handover: the remaining items, in order

0. **Decision needed (orchestrator):** the equivalence route of §1, (a)–(d) in L-circ, or the
   coordinated `gen4` change. Obstruction 4 (`shiftMask`'s template) needs (a) either way, so it
   can start now:
   - `tplExt` with a template filter;
   - `ImplT`/`compileT_sound` over it;
   - `compMS_eq`/`compMS_T`/`slotRP_rows`/`planData4_rows` generalised, with 3.x's `rfl`-equal;
   - the 4.x prototypes compiled with `shiftMask` an import.
   Then regenerate `FRNodeRows4Hint` (`LayDump4`) and the dump.
1. **`SlotIface4`** (after 0):
   - `lrows := lRows4`, `irows := nodeIRows4`;
   - `selN`/`selS` as in §1;
   - `imp κ v w inp tr := ∃ s, exec impl_κ' ι inp ops St.init tr = some (s, []) ∧ aux ∧ imports ∧
     fors ∧ facts` at `slotAsg κ v w` (the 3.x `SlotRest.run` shape), with `facts` the `hashStmt`
     and tail facts;
   - `tpl` the moved template rows, `rep` the `R` claims;
   - `soundN`/`soundS` from `compileT_sound` at `slotAsg` (rows via `holds_rowMapC`), then the
     simulation of §1 (b).
2. **`hRes` item by item:**
   - `selP`/`selA`: `selP_sel`/`selA_sel` plus the kind byte (needs the reader, S-E12a D6);
   - `ActK` from the pack map (`k`'s bits pin the boundary);
   - the rest: pack map, WOTS, `aggChk`, `kOk`, `aggPad`.
3. **The templates of every unbound import** (S-E12b §7 item 3): the 4.1 `shiftMask` (node: over
   `chainLk4`; segment: `shiftSegI`), `tplTargetSNode`, `tplLinkWAll`, `rsWeight` and the kind
   factor, `evalL`'s replay over `lRows4`, the segment's `targetS`. Then **`implN κ`** proper (the
   4.1 `evalL`, `targetS`, `linkWAll`, `shiftMask`) and V re-measured with `VTime4`.
4. **`R`** with the two-prototype structure (S-E12b §4). The model fits the previous-node slot in
   one region only with the levers (`mRows4_neg`).
5. V: profile the non-`evalM` +20 ms of the 4.1 program (§3), against the 230 ms kill line
   (median).
