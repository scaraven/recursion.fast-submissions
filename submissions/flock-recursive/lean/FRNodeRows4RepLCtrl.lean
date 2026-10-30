-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b): the controls of
-- `FRNodeRows4RepLT`, `FRVIRTplRepL(D)` and `FRVIRTplRepT`.
import FRNodeRun4Ctrl
import FRNodeRows4RepNCtrl

/-!
# Controls for the `targetS` and `evalL` replays

| Definition | (+) | (−) |
|---|---|---|
| `rtC1b`, `rtC1c` | `rtC1b_cov`, `rtC1c_cov` (with `rsWeight`): `shiftTarget`, `linkWAll`, `targetS`, `evalL` at prototype 0; `linkWAll` at prototype 1 | not `evalM`, `rsWeight` (prototype 0), not the segment's `targetS`, `evalL` |
| `tsIn`, `evIn` | `in_ctl`: `[af n]`, `[af n, af m]` | an `f` operand, a missing operand |
| `kRows kTS`, `kRows kEvL` | the KAT (`probe/RepV2.lean`): at the real programs' operand forms, the honest locals satisfy every row | `kTS_neg`, `kEvL_neg`: an untracked operand, an operand of the wrong type: the rejecting row |
| `tsTpl`, `evTpl` | `tpl_ctl`: the operand shapes select `tplTS`, `tplEvL` | another shape gets the empty template (which `tsIn`/`evIn` reject) |
| `cbTS`, `cbEvL` | `cb_ctl`: the four locals blocks (with R3's `cbRS`) are disjoint at their measured sizes and inside the spare region | — (the sizes are measured: the KAT) |
| `tplTS`, `tplEvL` | `tplTS_outs` (64), `tplEvL_outs` (3) | `tplTS_ok`/`tplEvL_ok` are statements about every input (hypotheses: the gate equations); the KAT's perturbed input changes the value |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-- (+) `rtC1b` covers prototype 0's four templated ops and prototype 1's `linkWAll`; (−) not
`evalM` or `rsWeight` at prototype 0, nor the segment's `targetS`/`evalL`. -/
theorem rtC1b_cov : (rtC1b 0).cov (.shiftTarget 0 0 0 0) = true ∧ (rtC1b 0).cov (.linkWAll 0 0) = true ∧
    (rtC1b 0).cov (.targetS 0) = true ∧ (rtC1b 0).cov (.evalL 0 0) = true ∧
    (rtC1b 1).cov (.linkWAll 0 0) = true ∧ (rtC1b 0).cov (.evalM 0 0) = false ∧
    (rtC1b 0).cov (.rsWeight 0 (fun _ => []) 0 0 (fun _ => true) 0) = false ∧
    (rtC1b 1).cov (.targetS 0) = false ∧ (rtC1b 1).cov (.evalL 0 0) = false := by decide

/-- (+) `rtC1c` (with R3's `rsWeight`) covers all five ops of prototype 0; (−) not `evalM`, nor the
segment's `targetS`. -/
theorem rtC1c_cov : (rtC1c 0).cov (.targetS 0) = true ∧ (rtC1c 0).cov (.evalL 0 0) = true ∧
    (rtC1c 0).cov (.rsWeight 0 (fun _ => []) 0 0 (fun _ => true) 0) = true ∧
    (rtC1c 0).cov (.linkWAll 0 0) = true ∧ (rtC1c 0).cov (.evalM 0 0) = false ∧
    (rtC1c 1).cov (.targetS 0) = false := by decide

/-- (+) the shapes the templates serve; (−) others. -/
theorem in_ctl : tsIn [.af 20] = true ∧ tsIn [.f] = false ∧ tsIn [] = false ∧
    evIn [.af 17, .af 25] = true ∧ evIn [.af 17, .f] = false ∧ evIn [.af 17] = false := by decide

/-- (+) the operand shapes select the node kind's template. -/
theorem tpl_ctl (ν : Rev4.NodeKind) : tsTpl (.targetS 0) ν [.af 20] = tplTS ν 20 ∧
    evTpl (.evalL 0 1) ν [.af 17, .af 25] = tplEvL ν 17 25 ∧
    (tsTpl (.targetS 0) ν [.f]).gates = [] ∧ (evTpl (.evalL 0 1) ν [.af 17]).gates = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An `af 64` output slot on cells `30 … 93`. -/
def ctlOut64 : Slot := some (.af 64, (List.range 64).map fun j => Lin.cell (30 + j))

set_option maxRecDepth 16384 in
/-- (−) An untracked operand (register 2) or an `f` operand (register 0): the rejecting row. -/
theorem kTS_neg : kRows kTS 200 300 ctlPN toyCS (.targetS 2) [ctlOut64] = [rejRow ctlPN] ∧
    kRows kTS 200 300 ctlPN toyCS (.targetS 0) [ctlOut64] = [rejRow ctlPN] := by decide

theorem kEvL_neg :
    kRows kEvL 200 300 ctlPN toyCS (.evalL 0 2) [some (.f, [Lin.cell 30]), some (.f, [Lin.cell 31]),
      some (.f, [Lin.cell 32])] = [rejRow ctlPN] ∧
    kRows kEvL 200 300 ctlPN toyCS (.evalL 0 1) [some (.f, [Lin.cell 30]), some (.f, [Lin.cell 31]),
      some (.f, [Lin.cell 32])] = [rejRow ctlPN] := by decide +kernel

/-- The locals blocks in the spare region: `linkWAll` from `repB` (42,592), R3's `rsWeight` from
`repB + 2^16` (472,310), `targetS` after it (11.8 k), `evalL` after that (319.5 k), all below
`repB + 2^20` (the sizes: the KAT, `logs/C1b/repv2-*.log`, and R3's RESULT). -/
theorem cb_ctl : cbLW < cbRS ∧ cbRS + 504784 ≤ cbTS ∧ cbTS + 11891 ≤ cbEvL ∧ cbEvL + 319507 ≤ repB + 2 ^ 20 := by
  unfold cbLW cbRS cbTS cbEvL repB; omega

end N4s
end FR
