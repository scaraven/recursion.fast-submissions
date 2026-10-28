# P4b RESULT (pass 1): the front's Lr, E (with O1) and RS0 at revision 4.1; handover for RS1, B′, W0, DF

- **Base.** HEAD `7e14be6`. **Build tree** `logs/fr-build-P4b` (a copy of `fr-build-SG13`; `MINE.txt`
  lists the four new modules; `logs/org20`). Logs in `logs/P4b/`. Journal: `P4b-JOURNAL.md` (§0 the
  decisions, §0.4 the names, written before the proofs).
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under
  `timeout`. No sub-agents. Nothing committed. No existing module edited, no existing statement
  changed. Other tracks' files (S-E13's modified `FRVIR*`, T4's and P4a's untracked modules) were
  not touched and are not imported.

## Status

| Item | State |
|---|---|
| `Rej*`/doom names for R4 (stub first) | **Done** (`FRSoundness4P4bNames`; journal §0.4). |
| Generalisation over an entries source (S-G12′ F3) and an abstract front source | **Done** (`ESrc`, `FSrc`, the generic unit `…G`); 3.x is the instance (`rejEnd_eq_G`, `endBad_eq_G`, `rowsBad_eq_G`, `reads_iff_readsS`, `rowMat_entMat`: all `Iff.rfl`/`rfl`). |
| **O1** | **Done in general, and at 3.x**: `sat_entMatI_iff` (indexed rows, `RowsFitI`), `rowsBadG_ofIRows_iff`, `truthE3_iffI` (`nodeIRows (planOf fin)`), `matMle_entMat`, `mle_wEb4` (E4's weight = the `evalM`/`evalL` values). At revision 4.1 the rows per node kind are S-E's: parameter `srcE`. |
| Lr at `seq4` (169 … 214) | **Done**: zerocheck charge, handoffs, single counts, `RejEndLr4` check. |
| E at `seq4` (214 … 325), E4 batched with Lr | **Done**: outer half, `e4_single_batchE`, `e4_habs_innerE`, `e4_single_innerE`, `D4E4_reads`, `e4_habs_end4`, the three checks. |
| RS0 (326) | **Done**: `PendBad4`, `DPend4`, `DRS0_4`, `habs_RS0_4`, `rejRS4_log`, `pendE4_pendBad4`, RS1's count `rs1_count4`. |
| RS1's frame, B′, W0 (327 … 332) | **Not started** (§6 item 1). |
| `FrDF`/`FrObl`/`FrStab` (the front's phase dooms and obligations at `seq4`) | **Not started** (§6 item 2): needs P4a's Z/L/S dooms and T4's `PhaseObl`/`RejOK`/frames. |

**Checks.**
- `lake build FR` plus the four modules: green, 2,432 jobs (`logs/P4b/build-final.log`).
- **Axioms** (`logs/P4b/axioms.log`, all 191 declarations of the four modules): within `propext`,
  `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 223
  files, 0 findings (`logs/P4b/source-rule.log`).
- **Names.** Every new top-level name was grepped against all `FR*.lean` (untracked included) before
  it was added. All are in `FR.Snd.P4b`. Names shared with `FR.Snd` were renamed (a nested namespace
  makes a shared short name ambiguous): see the journal's log.

**Imports for `FR.lean`:** add `import FRSoundness4P4bRS` (it pulls `FRSoundness4P4bE`,
`FRSoundness4P4bRows`, `FRSoundness4P4bNames`).

## 1. Design (journal §0)

- **The rounds need no copy.** 3.x's `D3`/`D2`/`ans3` read the kind only through `nr (kindOf es)`.
  With a constant `nr := fun _ => n` they are kind-free, so `D3_single`, `D2_single`,
  `D2_append_iff`, `clR2_same`, … are reused as they are.
- **One gate.** `OnNode P L es := ∃ κ, kindOfC es = .node κ ∧ P κ L es`; `P κ` is the unit at node
  kind `κ`'s dims. `onNode_card`, `onNode_imp`, `onNode_congr`, `readsS_onNode`, `rejLog4_onNode`
  lift the per-kind obligations.
- **Real rows vs slots.** The generic unit takes `a` (real row bits) and `A` (slots; the end absorb
  is at `b2 + 2A`). At revision 4.1 a node kind's real counts can be below `seq4`'s slots (`N2`: Lr
  16 < 17, E2 22 < 23, E4 24 < 25). The verifier skips the dummy rounds (`roundsOps`' `keep` at
  `j ≥ real κ`), and the dooms count real rounds only.
- **What is not P4b's is a parameter.**
  - `FSrc`: the abstract `Same` and `f⁽⁰⁾`. These are T4's at revision 4.1: the Ligerito words at
    `CKind`'s ladder.
  - `srcE`/`srcL`: the M and L rows per node kind (S-E's; S-G13 F3).
  - `kf`: the 3.16 kind factor `B_β(t)` per node kind (S-E's block-kind indicators).
  - `F0`/`Pub`: the level-0 word's distance (T4's) and the node's public cells (S-E's).
- **Checks are `RejLog4`**: monotone, unchanged at a `fsItems4` squeeze, independent of the charging
  log. T4's `RejOK` (in `FRSoundness4TailStep`, untracked) follows at once: its `stab` holds for any
  check that reads only `X`.

## 2. What was built (`loc.py`, `logs/P4b/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4P4bNames` | 328 / 157 / 11 | `FSrc`, **`src3`**, `ReadsS`, `ESrc` (`ofRows`, **`ofIRows`**), `entMat`; generic `zCG`, `RowsBadG`, `ZCwG`, `T3G`, `D3G`, `triTG`, `EndBadG`, `T4G`, `BatBadG`, `RejEndG`; `lrR`, `e2R`, `ncR`, **`OnNode`**; Lr: `RowsBadLr4`, `ZCwLr4`, `D3Lr4`, `EndBadLr4`, `BatBadLr4`, **`RejEndLr4`**; E: `nE4`, `ZCwE4`, `D3E4`, `EndBadE4`, `c4E4`, `wEb4`, `TEb4`, `BatBadE4`, `D2Eb4`, `D4E4`, **`RejEndE4`**, **`RejInE4`**, `okE4`, `rPt4`, **`RejFinE4`**, `PendE4`; RS: `xSL4`, `cwL4`, `ePtL4`, `rsPtsL4`, `sliceL4`, `sL4`, `alphaL4`, **`okRS4`**, **`RejRS4`**; controls |
| `FRSoundness4P4bRows` | 469 / 339 / 39 | `ReadsS` lemmas; **`RejLog4`**, `rejLog4_of`; the unit: `zCG_same`, reads (`rowsBadG_reads`, `zcwG_reads`, `endBadG_reads`, `batBadG_reads`, `D3G_reads`), `T3G_local`, **`zcG_count`**, **`habsG_outer`**, **`habsG_end`**, **`singleG_batch`**, `singleG_outer`, `outerG_append`, `D3G_same`, `rejEndG_agree`, `rejEndG_log`; **O1**: `RowsFitI`, `truthEI`, `sum_ite_none`/`_key`, `sum_entriesI`, `matVec_entMatI`, **`sat_entMatI_iff`**, `rowsBadG_ofIRows_iff`, `sat_ofRows_iff`, **`truthE3_iffI`**, `matMle_entMat`, `mle_wInn`; controls |
| `FRSoundness4P4bE` | 538 / 401 / 51 | `p4b_pos`, `absOK4_eq`/`p4b_abs` (certificates), `dims_le'`; the gate (`kindOfC_append`, `onNode_or/imp/congr/card`, `readsS_onNode`, `rejLog4_onNode`); Lr: `lr4_zc_count`, `lr4_habs_outer`, `lr4_single_outer`, `lr4_outer_append`, `lr4_habs_end`, `lr4_single_batch`, `rejEndLr4_log`; E outer: `e4_zc_count`, `e4_habs_outer`, `e4_single_outer`, `e4_outer_append`, `e4_habs_end`, `rejEndE4_log`; E4: `wEb4_agree`, `c4E4_agree`, `TEb4_same/_local/_size`, **`trueSum_TEb4`**, `single_batchE_at`, **`e4_single_batchE`**, **`e4_habs_innerE`**, **`e4_single_innerE`**, `e4_inner_appendE`, `D4E4_reads`, `rejInE4_log`, **`mle_wEb4`**, **`e4_habs_end4`**, `rejFinE4_log`; controls |
| `FRSoundness4P4bRS` | 334 / 228 / 25 | `rsPtsL4_congr`, `cwL4_congr`, `sL4_congr`, `alphaL4_congr`; `kfT4`, `gL4`, `rsQ4`, `trueL4`, `truthRS0_4`; `OkReads4`, **`PendBad4`**, **`DPend4`**, **`DRS0_4`**, reads, **`rejRS4_log`**, **`habs_RS0_4`**; **`trueL4_three`**, **`pendE4_pendBad4`**, `okRS4_reads`; **`rs1_count4`**; controls |
| **total** | 1,669 / 1,125 / 126 | |

## 3. The main statements

```lean
-- O1: the R1CS of indexed rows (what `evalMS` evaluates) is "every row holds"
def RowsFitI (rows : List (ℕ × Row)) (a b : ℕ) : Prop :=
  (rows.map Prod.fst).Nodup ∧ (∀ p ∈ rows, p.1 < 2 ^ a) ∧ ∀ p ∈ rows, ∀ t ∈ p.2.a ++ p.2.b ++ p.2.c, t.1 < 2 ^ b
theorem sat_entMatI_iff (rows) (hf : RowsFitI rows a b) (w : Asg) :
    Sat (entMat (ESrc.ofIRows rows).ea a b) (…eb…) (…ec…) (fun y => w y) ↔ truthEI rows w
theorem truthE3_iffI (fin) (hfit : RowsFitI (TEval.nodeIRows (TEval.planOf fin)) 21 23) κ L es :
    truthEI (TEval.nodeIRows (TEval.planOf fin)) (fF κ L es) ↔ Sat (entMat (ESrc.ofIRows (nodeIRows (planOf fin))).ea 21 23) …
theorem mle_wEb4 srcE srcL κ es r : mle (wEb4 srcE srcL κ es) r =
    (matMLE (srcE κ).ea r_x r + κ_E·matMLE (srcE κ).eb r_x r + κ_E²·matMLE (srcE κ).ec r_x r) +
      κ_E³·(matMLE (srcL κ).ea r_Lr r + κ_L·… + κ_L²·…)

-- E3 (274), E4 (275 …), E4 end (325), RS0 (326) at revision 4.1
theorem e4_single_batchE (L es) (hl : es.length = 274) :
    (univ.filter fun d => (EndBadE4 R srcE L es ∨ BatBadLr4 R srcL L es) ∧ ¬ BatBadE4 R srcE srcL L (ext1 es d)).card ≤ 3 * 2 ^ 128
theorem e4_single_innerE (L es) (hr : ¬ RejInE4 L es) :
    (univ.filter fun d => D4E4 R srcE srcL L es ∧ ¬ D4E4 R srcE srcL L (ext1 es d)).card ≤ 2 * 2 ^ 128
theorem e4_habs_end4 (x) (hl : es.length = 325) (hd : D4E4 R srcE srcL L es) :
    RejFinE4 srcE srcL L (es ++ [x]) ∨ PendE4 R L (es ++ [x])
theorem pendE4_pendBad4 (h : PendE4 R L es) : PendBad4 R kf (okRS4 oZ oLc oSh) L es
theorem habs_RS0_4 (hok : OkReads4 ok) (hF : ReadsS R 3 F0) (hP : ReadsS R 3 Pub) (x) (hl : es.length = 326)
    (hd : DPend4 R kf ok F0 Pub L es) : RejRS4 ok L (es ++ [x]) ∨ DRS0_4 R kf F0 Pub L (es ++ [x])
```

## 4. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `logs/P4b/prof-*.log`)

| Module | wall (import ≈ 3.7 s) | kernel (type checking) | max RSS |
|---|---|---|---|
| `FRSoundness4P4bNames` | 7.3 s | 0.03 s | 2.83 GB |
| `FRSoundness4P4bRows` | 10.2 s | 0.80 s | 2.85 GB |
| `FRSoundness4P4bE` | 15.9 s (`absOK4_eq`'s `decide +kernel` over `fsItems4` is most of the interpretation, ≈ 1 s) | 1.48 s | 2.91 GB |
| `FRSoundness4P4bRS` | 8.5 s | 0.31 s | 2.91 GB |

The `decide` uses are the position certificates only: `p4b_pos` (small lists after
`fsStarts4_eq`/`fsRanges4_eq`), `absOK4_eq` (`decide +kernel` over `seq4`'s item list, as S-G13's
certificates), and kind-table facts (`dims_le'`, `dims_le`). No `trueSum` is ever at a concrete
size: `trueSum_TEb4` is algebra over the symbolic `ncR κ`.

## 5. Controls

| Control | Shows |
|---|---|
| `rejEnd_eq_G`, `endBad_eq_G`, `rowsBad_eq_G`, `reads_iff_readsS`, `rowMat_entMat` (+) | 3.x's unit is the generic one at `src3`, `ESrc.ofRows`, `A = a` (by `Iff.rfl`/`rfl`). |
| `sat_ofRows_iff`, `truthE3_iffI` (+) | O1's lemma instantiates at 3.x's row list and at `nodeIRows (planOf fin)`. |
| `not_rowsFitI_dup` (−) | Two rows at one index are refused (`RowsFitI`'s distinctness is not vacuous). |
| `sat_entMatI_nil` (+), `not_sat_entMatI_one` (−) | The indexed R1CS holds with no rows and fails on `1 · 1 = 0`. |
| `dims_ctrl`, `dims_le` (+) | `(lrR, e2R, ncR)` per kind: N2 (16, 22, 24), N4/N8 (17, 23, 25); all within `seq4`'s slots. |
| `not_onNode_seg` (−), `onNode_iff` (+) | The gate is false on a segment's chain and is the kind's doom on a node's. |
| `rsPtsL4_length` (+/−), `rPt4_length`, `rPt4_N2` (+) | Four RS claims on a node, three on a segment; `N2`'s E4 point has 24 coordinates, not 25. |
| `not_batBadE4_seg` (+), `batBadE4_of_ne` (−) | A segment is never doomed at E3; a node with a false batched claim is. |
| `not_pendE4` (−) | E4 end's value equal to `ẑ(r′)` clears E's pending doom. |
| `not_pendBad4_true` (+), `pendBad4_false`, `rejRS4_false` (−) | Bindings at the true values clear `PendBad4`; a refusing binding is pending and rejected. |
| `alphaL4_true` (+), `alphaL4_zero` (−) | True slices give the true values; zero slices give `0`. |
| `kfT4_seg` (+) | A segment's kind factor is `1`. |

## 6. Handover: the remaining items, in order

1. **RS1's frame, B′, W0 (327 … 332).** Port `FRSoundnessFrW0`'s readers to `seq4`:
   - `rsCoL` at 326 (`coordAt es 326`), `rsRL`, `rsKL`, `kpL` at 331;
   - `wrsL4` with `kfT4 kf`, `rsTvL4`, `vRSL4`, `vStarL4`, `W₀L4`, `c₀L4`, and `frontLocal` before 332.

   Then port `FrRS`: `vRSL_eq`, `fipL_eq`, and `hfin_RS1` (the frame at `(326, 4) ∈ fsRanges4`
   through T4's `hfin_rs1`, with **`rs1_count4`** for the count). Then `FrB`: `DRS1`, `DB`, `single_B`
   at 331, and `handoff_B` into T4's P1.0 doom. Deltas:
   - the node's public cells per kind (`cells κ`, as `VnodeC` takes them);
   - `pubH` over the revision 4.1 node statement (`stmtOps4`, `gFinB'`): check which digests `finB′`
     batches for `N2`/`N4`/`N8`;
   - `Pub` (the `F0`/`Pub` parameters of `DPend4`/`DRS0_4`) instantiated by S-E's public cells.
2. **The front's phase dooms and obligations at `seq4`** (`FrDF`, `FrObl`, `FrStab`). These are
   `Dk k` for phases 13–25, with this track's parts:
   - `RowsBadLr4`/`ZCwLr4`/`D3Lr4`/`EndBadLr4`/`BatBadLr4`;
   - `nE4`/`ZCwE4`/`D3E4`/`EndBadE4`, `BatBadE4`, `D4E4`;
   - `PendE4` → `DPend4` → `DRS0_4`.

   The background carries P4a's pending Z/L/S claims (`FRSoundness4P4aNames`). The obligations are
   the lemmas above, framed by T4's `esc_msD_frame`/`card_frame` at `fsRanges4`, and its `RejOK` from
   `RejLog4`. This needs P4a's and T4's modules to be final.
3. **The instantiation (X4).**
   - `FSrc` at revision 4.1: T4's `Same` over `CKind`'s words and `fF`, with `fz_same` from 3;
   - `srcE κ := ESrc.ofIRows (rows of node kind κ)` and `srcL κ` (S-E's per-kind plans);
   - `kf` (S-E's indicators), `F0` (far at level 0), `Pub`.
4. **`hfit` per node kind:** `RowsFitI rows (e2R κ) (ncR κ)` for S-E's per-kind indexed rows, by a
   certificate about the generator (indices increasing by construction), not by `decide` on the
   list.

**For R4** (the front checks on an accepted run, at `gen4`):
- `RejEndLr4`/`RejEndE4` are `finLr`/`finE` (ii) at Lrend 213 and Eend 273, after `lrR κ`/`e2R κ`
  real rounds.
- `RejInE4` is E4's round checks for `l < ncR κ`.
- `RejFinE4 srcE srcL` is `finE` (iv). `mle_wEb4` puts its `W(r′)` in the form `evalM`/`evalL`'s
  specification reads (`Eval.matMLE` of the entries at `(r_x, r′)` and `(r_Lr, r′)`). The verifier's
  arrays need `Eval.ptOf` ↔ `ptOf` on lists.
- `RejRS4 (okRS4 oZ oLc oSh)` is the slice part (`α_j` at 327). `oZ`/`oLc`/`oSh` are P4a's bindings.
- Each check is a `RejLog4` (`rejEndLr4_log`, `rejEndE4_log`, `rejInE4_log`, `rejFinE4_log`,
  `rejRS4_log`).

## 7. Deviations and findings

- **D1. Names.** A short name shared with `FR.Snd` becomes ambiguous inside `FR.Snd.P4b`, so the
  revision 4.1 names carry a `4` suffix, and some differ from the brief's (`RejE4` → `RejFinE4`).
  The journal §0.4 table has the final names.
- **D2. The unit's inner half is not ported in its three-claim form.** Since 3.13, E4 batches
  Lr's claim (`finE` (iii)), so only the batched form (`TEb4`, `D4E4`, `RejInE4`) exists at
  revision 4.1. 3.x's `T4`/`D4`/`RejIn` have no revision 4.1 use. `T4G`/`BatBadG` are kept for
  Lr3's and E3's counts.
- **F1. O1 needs distinct row indices.** Over indexed rows, two rows at one index add up into one
  matrix row, and the R1CS then checks their sum, not each row. `hfit` must therefore include
  `(rows.map Prod.fst).Nodup` (`RowsFitI`). 3.x's `RowsFit` does not have this condition, because a
  row list's index is its position.
- **F2. No value is asserted by no final in this scope.** The values checked are:
  - Lr/E's end triples (`gFinLr`/`gFinE`, `piElem fEEnd`);
  - `κ_L`, `κ_E` (`outsOf "Lr3"/"E3"`);
  - E4's real rounds (`roundsOps` checks `j < real κ`);
  - E4's last claim against `evalM`/`evalL` and `fz` (`assertEq (b + 35) (claimN "E4")`);
  - `fz` against E4 end's message (`piElem fE o`);
  - RS0's slices through `finRS`'s `α_j`.

  The dummy slots (`N2`'s 17th Lr2, 23rd E2 and 25th E4 slot) are not checked, and no doom reads
  them.

## 8. Open questions

1. `FSrc`, `kf`, `F0`, `Pub`, `srcE`/`srcL` are parameters (§1). Does X4 instantiate them, or does
   each owning track (T4, S-E) export its instance for P4b to consume?
2. Retiring 3.x: the generic unit and O1 are stated so that 3.x is an instance. If the 3.x chain is
   kept until integration, should `FRSoundnessRows` be restated through `…G` (by `Iff.rfl`, at no
   cost), or left alone?
