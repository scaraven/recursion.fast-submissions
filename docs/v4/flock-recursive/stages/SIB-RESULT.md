# SIB (siblings + the closure generator): RESULT

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`; started at `97d578b`, final build against the snapshot of HEAD
`0f7d3a3` — CF WIP and SEG-R0 landed meanwhile). Build tree `logs/fr-build-SIB` (copy of `fr-build-IMPC2b`,
re-snapshotted onto HEAD by `snap.sh`, no old patches; my modules symlinked; `patch-sib.py` makes the
one edit outside my files, FR.lean's import). Logs `logs/SIB/`; journal `SIB-JOURNAL.md`. Every lake/lean/probe ran in a
16 GB scope under `timeout`. No sub-agents, nothing committed, no `sorry`.

## 0. Summary

| Item | State |
|---|---|
| Siblings: generator | **Done** `sibTG` (`FRNodeRows4AskC`): IMPC2's sibling rows plus process-start checks (`sibAt`, `sibPosOk`), so the proof decides nothing over tables |
| Siblings: `ATImp` | **Done** `atImp_sib` (`FRNodeRun4CS`) from `SibOk`; **`sibOk_of`** (`FRNodeRun4CD`) proves `SibOk` at every active slot: the kind tie `trM4_slot`, the position bit `posBit_eq` (`PosBits` + `phAns_getD` + `posOf4_bit`), the format `sib_bytes` (`reassemble4_byte`, `ctb4_sibs`), arena₁ `slot_qelemA` |
| Closure generator | **Done** `TG.close` (`FRNodeRows4AskC`) + soundness (`FRNodeRun4CA`, `FRNodeRun4CB`): `atImp_close`, `impB_sub`, `slotRunB_of_close` |
| Residual, exact | **`SlotRunC rt A`**: the `felems` aux cells and the imports of the replay ops (`isRep`) neither `rt` nor `A` covers (`impQP`). No flag conjunct. On the compile (probe): p0 **0** imports + 871 felems; p1 **5** imports (`targetS, shiftTarget, evalM, evalL, rsWeight`) + 871 felems |
| Final discharge | **`gaps4_of_runC`** (`FRNodeRun4CT`): `Sub4.Gaps4` from `SlotRunC (rtC1c π) (withSib askAq π)` at every active slot; fold `askFold_close` by `rfl` |
| Honest completeness | probe `sibstat`: **0 failing rows** in `askTG` (both prototypes); the closure emits **0 rows**; `bitNxAll` true; 7,426 sibling reads matched per prototype; rows p0 **130,914** / p1 **154,333** ≤ `arR2N` 180,560 |
| **Init (hard cap +0.2 s)** | **Exceeded by the siblings' rows**: `plan4t init` A/B **+2.7 s user** (§4). The closure alone costs ≈ 0 (within noise). Decision needed (§6.1) |
| V | in-process `askV` +35–40 ms per prototype (≈ +75 ms per node with both) |
| Kernel | ≈ 7.5 s type checking in my six modules; `atImp_sib` 4.35 s alone (§5, open item) |
| Build | `lake build FR Solution FRSubmission4Fin`: green (`build-final.out`/`.log`) with FR.lean importing `FRNodeRun4CT` |
| Axioms / source rule | 36 declarations incl. `certified`, each ⊆ {propext, Classical.choice, Quot.sound} (`axioms.log`); 475 files, 0 findings (`source-rule.log`) |

**FR.lean line** (replaces `import FRNodeRun4BT`, l. 170): `import FRNodeRun4CT`

## 1. The theorems

- **`gaps4_of_runC`** : `(∀ vk κ w c₁ c₂ ch, StmtN4R … → ∀ v, Active4 … v → ∀ ι, SelOk … ι → SlotRunC (rtC1c (protoOf κ v)) (withSib askAq (protoOf κ v)) (implP implB …) (protoOf κ v) ι (slotIn …) (slotTr …) (slotAsg κ v w)) → Sub4.Gaps4`.
- **`SlotRunC rt A impl π ι inp tr w`** := `∀ s, execA … = some (s, []) → (∀ a ∈ (protoCS π).aux, isBitsA a = false → <aux fact>) ∧ ∀ i ∈ impQP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)`, with `impQX` = imports of an op with `isRep op && !rt.cov op && !A.cov op`. It replaces FOLD2's `SlotRunB` (whose import list was `impBX` and which had a foreign-flag conjunct): **`slotRunB_of_close`** proves `SlotRunB rt (closeP A π)` from `SlotRunC rt A` given the closed template's rows.
- **Closure** (`FRNodeRun4CB`): `atImp_close` (covering every possible import costs no `ATImp`: at an import `A` does not cover the rows are `failRT`); `atAsk_close`; `impB_sub` (a residual import of the closed template is an `isRep` op's: `opImp`, the template lemmas and `bitNxAll`); `trail_forsF` + the flag case of `slotRunB_of_close` (no foreign flag survives `forRows` besides `zPin`/`stFlag`).
- **Template facts** (`FRNodeRun4CA`): `opOut_imp` (`opOut`'s import flag is `opImp op`), `opForeign_eq`, `opOut_foreign`, `tplExt4_flags` (a template output is never an import nor foreign), `tplExt4_isNone` (whether a template takes an op does not depend on the template bodies), `stepOut_imp_of`, `stepOut_foreign_of`.
- **Siblings**: `atImp_sib` (`SibOk` → `ATImp` of `sibTG`), `sibOk_of` and its lemmas (`sibAt_spec`, `sib_bytes`, `sib4_getD`, `ansN_succ`, `phAns_getD`, `posOf4_bit`, `lvl_mkTab`, `mkTab_ans_lt`, `trM4_slot`, `posBit_eq`).
- **Fold**: `withSib Aq π := (withBitsS Aq π).addE (sibTG (XofA π) π (bitTabP π)).toAT`, `withClose := closeP (withSib …)`, `askFold_close` (`rfl`), `close_rowsB`, `gap4Imp_of_close`, `gap4Imp_rtC1cC`.

## 2. Definitions (new, `FRNodeRows4AskC`, below `FRNodeRows4`)

- `sibSegs`, `sibAt o` (phase, level, position, depth, node item of an `fSibs` read), `sibPosOk` (per kind, at an active depth: phase `n−1` is the level's P2, `p / per < sq`, `ansCell` of bit `(p mod per)·logN + h` is `posCell i p h`), `sibRowsS` (IMPC2's rows + those checks + `itemsT[k] = node i h`, not in the last block), `sibCov`, `sibTG`.
- `isRep` (shiftTarget, linkWAll, rsWeight, targetS, evalL, evalM), `isBitOf`, `opImp`, `forCap`, `extCan`, `opForeign`, `bitNxT`/`bitNxAll` (tail-recursive), `zPinT`/`stFlagT` (copies of `zPin`/`stFlag`, `rfl` to them), `closeCov`, `impRows`, `forRows`, **`TG.close A X pv T nx`**, **`TG.addE`** (`addD` without asking `A` at `B`'s ops).
- `askTG π` (my line in `FRNodeRows4`): `let ops, Xa, pv, T`; FOLD2's chain `|>.addE (sibTG Xa π T)` then `.close Xa pv T (bitNxAll 0 ops)`.

## 3. Statement / definition changes

| declaration | change | why |
|---|---|---|
| `FRNodeRows4.askTG` | folds `sibTG` (addE) and closes (`TG.close`); `let`-shares `ops`, `pv`, `T` | the task |
| `FRNodeRun4BT.askFold_bitsS`, `gap4Imp_rtC1cS`, `gaps4_of_runS` | **removed** (false once `askTG` changes: row indices move) | replacements `askFold_close`, `gap4Imp_rtC1cC`, `gaps4_of_runC`. `gap4Imp_of_bitsS` (fold as hypothesis) kept. No other user (`grep`) |
| `FR.lean` | `import FRNodeRun4BT` → `import FRNodeRun4CT` | top module (not my file: diff here) |

## 4. Measurements

- **Honest compile** (`sibstat-final.log`): as §0; closure-covered ops 26,477 / 26,404 (of which 1,401 / 1,399 possible imports `A` does not cover, where the extension is asked; 8,731 / 8,722 possible flags).
- **`plan4t init` A/B** (core 20, alternating; user s):
  - base (FOLD2) vs SIB full (`plan4t-init-ab-sib5.log`): 20.29 19.87 19.98 20.45 20.47 vs 23.09 22.49 22.93 23.73 22.19 → **+2.7 s**;
  - base vs siblings only, no closure (`plan4t-init-ab-sibonly.log`): 18.39 18.86 19.10 18.50 vs 21.75 21.22 21.66 21.05 → **+2.7 s**. So the closure costs ≈ 0 and the siblings ≈ +2.7 s.
- **In-process** (`sibtime*.log`, min of 6): trail + group/fit +85 ms (siblings) per prototype with `trailMS`; with the plan's `trailMR` p0 +0.2–0.9 s, p1 ≈ +0.1 s. The in-process numbers do not explain the +2.7 s (§6.1). `askV` +35–40 ms per prototype.
- Costs cut on the way: `sibSegs` (5 parts, not `pSegs`), `opForeign` (no rows built), the extension asked only at `extCan` ops, `closeCov` tested before `A.cov` (so `impcCov`'s window test runs once per read), `addE` (not `addD`) for the siblings, `bitNxAll` passed as a value.

## 5. Kernel (`lean -DElab.async=false --profile`, core 20, `profile-*.log`)

| module | type checking | tactics |
|---|---|---|
| `FRNodeRows4AskC` | 0.09 s | 0 |
| `FRNodeRun4CA` | 0.36 s | 3.09 s |
| `FRNodeRun4CB` | 0.12 s | 0.63 s |
| `FRNodeRun4CS` | **4.38 s** (one declaration, `atImp_sib`) | 0.41 s |
| `FRNodeRun4CD` | 1.72 s | 3.36 s |
| `FRNodeRun4CT` | 0.82 s | 0.42 s |

≈ 7.5 s new type checking; on `certified`'s path only once `Sub4.Gaps4` is routed through `gaps4_of_runC`. `atImp_sib`'s 4.35 s is
likely a kernel unfolding (a closed table such as `itemsT` reached by a defeq check); not investigated (§6.3).

## 6. Open items

1. **Init: the siblings' rows cost +2.7 s in `plan4t init`** (cap +0.2 s). The closure is within the cap. Options:
   (a) fold the closure without the siblings (needs a `skip` parameter in `TG.close`/`impQX` so that sibling reads stay in the
   residual; `atImp_sib`/`sibOk_of` stay ready for a later fold); (b) find where the plan pays for template rows beyond the
   trail and grouping (the in-process trail+group explains ≤ 1 s; suspects: the plan's other per-row passes or memory effects
   next to p0's 10 s replay pass); (c) the compile-alias lever of IMPC2 §4 (fewer rows elsewhere).
2. The p1 replay ops (SEG-R) and the `felems` (`colTG`) are the explicit residual of `SlotRunC`; when they are handled (a
   template covering them, or `isRep` shrinking), `impQP` shrinks by definition.
3. Kernel: find the 4.35 s in `atImp_sib`.
4. Re-dump plan form / MxKat / V(N4) / hint after the `askTG` change (orchestrator).

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `bitNxAll` | `bitNxAll_ctl`: `bitOf` then its `selectHalf` | another op, a `selectHalf` on another register, last op |
| `closeCov` | `closeCov_ctl`: proof read, `input`, assertion | ask, `bitOf`, replay op, arithmetic |
| `impRows` | `impRows_ctl`: untaken `input`/`piDigest` fail | a templated `eqPt` taken: none |
| `forRows` | `forRows_ctl`: undischarged `assertBit` fails | `assertEq` off at every kind: none |
| `TG.close` | `close_ctl`: uncovered import fails; first ask with a bad `bitOf` fails | covered import: the part's rows; good `bitOf`: none |
| generators on the compile | `sibstat`: 0 failing rows, every sibling matched, residual = §0 | — |

## 8. Files

- New: `submissions/flock-recursive/lean/FRNodeRows4AskC.lean`, `FRNodeRun4CA.lean`, `FRNodeRun4CB.lean`, `FRNodeRun4CS.lean`,
  `FRNodeRun4CD.lean`, `FRNodeRun4CT.lean`.
- Edited: `FRNodeRows4.lean` (`askTG`, its doc, `import FRNodeRows4AskC`), `FRNodeRun4BT.lean` (three theorems removed, doc),
  `FRNodeRun4BF.lean` (doc line).
- Docs: `docs/v4/flock-recursive/stages/SIB-RESULT.md`, `SIB-JOURNAL.md`.
- Tree (dev): `logs/fr-build-SIB/{patch-sib.py, probe/SibStat.lean, probe/SibTime.lean, ax/AxSIB.lean}`, `logs/SIB/` (logs,
  `ab.sh`, `summ.py`, `bin/plan4t-*`).
