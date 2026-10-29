-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1): the controls of
-- `FRNodeRows4RepK`, `FRNodeRows4RepN`, `FRNodeRows4RepW` and `FRVIRTplRepLW`.
import FRNodeRows4RepW

/-!
# Controls for the previous node's replay templates

| Definition | (+) | (−) |
|---|---|---|
| `linLt` | `linLt_ctl`: a form below the bound | a cell at the bound |
| `bndZ`, `stOut` | `stOut_pos`: zero digest forms, an `f` output below `B`: the row `one · out = 0` | `stOut_neg`: a nonzero coefficient (or an output cell at `B`) gives the rejecting row |
| `kRows` (a toy `KOp`) | `kRows_pos`: typed operands at all three indices: the template's rows and one copy row | `kRows_neg`: an untracked operand, or an operand form above `B`: the rejecting row |
| `rtC1` | `rtC1_cov`: `shiftTarget`, `linkWAll` at prototype 0, `linkWAll` at prototype 1 | not `targetS`, `evalL`, `rsWeight`, `evalM` (still imports) |
| `rtLinkSegW` | `rtLinkSegW_pos`: outputs below `B`: S-E14's eight rows | `rtLinkSegW_neg`: an output cell at `B`: the rejecting row |
| `repMapC` | `repMapC_ctl`: a frame cell where `slotAsg` reads it; a local in `N4`'s spare region (cell `5·2^20`) | a local is not slot 1's cell |
| `tplLW` | `tplLW_outs` (8 outputs), `fam_pos` | `tplLW_ok` is a statement about every input: no vacuity (its hypotheses are the gate equations) |
| `STBase` | `stBase_implC` | `stBase_neg`: a base whose `shiftTarget` is `1` does not meet it |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-- (+) A form below the bound; (−) a cell at the bound. -/
theorem linLt_ctl : linLt 10 [(3, 1), (9, 2)] = true ∧ linLt 10 [(3, 1), (10, 2)] = false := by decide

/-- The controls' parameters: `one` is cell 0, the selectors cells 1–3. -/
def ctlPN : Params := ⟨Lin.cell 0, fun ι => Lin.cell (1 + kIx ι)⟩

/-- A compile state whose register 0 is `bnd` (`af 5`; its first four forms `zs`). -/
def bndCS (zs : List Lin) : CS := { CS.init 100 with slots := #[some (.af 5, zs ++ [Lin.cell 7])] }

/-- (+) Zero digest forms (coefficient 0 on cells 1–3) and an output below `B`: the row
`one · out = 0`. -/
theorem stOut_pos : stOut 50 ctlPN (bndCS [[(1, 0)], [(2, 0)], [(3, 0)], []]) 0 [some (.f, [Lin.cell 20])] =
    [⟨Lin.cell 0, Lin.cell 20, []⟩] := by decide

/-- (−) A nonzero coefficient in a digest form, or an output cell at `B`: the rejecting row. -/
theorem stOut_neg :
    stOut 50 ctlPN (bndCS [[(1, 0)], [(2, 1)], [(3, 0)], []]) 0 [some (.f, [Lin.cell 20])] = [rejRow ctlPN] ∧
    stOut 50 ctlPN (bndCS [[(1, 0)], [(2, 0)], [(3, 0)], []]) 0 [some (.f, [Lin.cell 50])] = [rejRow ctlPN] := by
  decide

/-- A toy kind-muxed op: `mulF a b` at every index, its sub-template one product. -/
def toyK : KOp :=
  ⟨fun op => match op with | .mulF .. => true | _ => false,
   fun op _ => match op with | .mulF a b => [a, b] | _ => [],
   fun _ => true,
   fun _ _ _ => ⟨[.mul (I 0) (I 1)], [L 0]⟩, [.f]⟩

/-- Two `f` registers on cells 10, 11. -/
def toyCS : CS := { CS.init 100 with slots := #[some (.f, [Lin.cell 10]), some (.f, [Lin.cell 11])] }

/-- (+) Typed operands at all three indices: the kind mux's rows and one copy row on the output
cell 30. -/
theorem kRows_pos : (kRows toyK 50 60 ctlPN toyCS (.mulF 0 1) [some (.f, [Lin.cell 30])]).length =
    (kTpl toyK (.mulF 0 1) [([.f, .f], [Lin.cell 10, Lin.cell 11]), ([.f, .f], [Lin.cell 10, Lin.cell 11]),
      ([.f, .f], [Lin.cell 10, Lin.cell 11])]).rows.length + 1 := by decide

/-- (−) An untracked operand (register 2), or an operand form at the bound (`B = 11`): the rejecting
row. -/
theorem kRows_neg : kRows toyK 50 60 ctlPN toyCS (.mulF 0 2) [some (.f, [Lin.cell 30])] = [rejRow ctlPN] ∧
    kRows toyK 11 60 ctlPN toyCS (.mulF 0 1) [some (.f, [Lin.cell 30])] = [rejRow ctlPN] := by decide

/-- (+) `rtC1` covers `shiftTarget` and `linkWAll` at prototype 0, `linkWAll` at prototype 1; (−) not
`targetS`, `evalL`, `rsWeight` or `evalM`. -/
theorem rtC1_cov : (rtC1 0).cov (.shiftTarget 0 0 0 0) = true ∧ (rtC1 0).cov (.linkWAll 0 0) = true ∧
    (rtC1 1).cov (.linkWAll 0 0) = true ∧ (rtC1 0).cov (.targetS 0) = false ∧
    (rtC1 0).cov (.evalL 0 0) = false ∧ (rtC1 0).cov (.evalM 0 0) = false ∧
    (rtC1 0).cov (.rsWeight 0 (fun _ => []) 0 0 (fun _ => true) 0) = false := by decide

/-- An `af 8` slot on cells `b … b + 7`. -/
def ctlSlot8 (b : ℕ) : Slot := some (.af 8, (List.range 8).map fun j => Lin.cell (b + j))

/-- (+) Outputs below `B`: S-E14's eight rows; (−) an output cell at `B`: the rejecting row. -/
theorem rtLinkSegW_pos : ((rtLinkSegW 50).rows ctlPN toyCS (.linkWAll 0 0) [ctlSlot8 20]).length = 8 := by decide

theorem rtLinkSegW_neg : (rtLinkSegW 50).rows ctlPN toyCS (.linkWAll 0 0) [ctlSlot8 45] = [rejRow ctlPN] := by
  decide

/-- (+) A frame cell where `slotAsg` reads it, a local in `N4`'s spare region; (−) the local is not
slot 1's cell `2^20 + c`. -/
theorem repMapC_ctl : repMapC .N4 0 5 = 5 + NodeKind.oneCell .N4 ∧
    repMapC .N4 0 (repB + 7) = 5 * 2 ^ 20 + 7 + NodeKind.oneCell .N4 ∧
    repMapC .N4 0 (repB + 7) ≠ 2 ^ 20 + 7 + NodeKind.oneCell .N4 := by
  have h1 : (5 : ℕ) < repB := by norm_num [repB]
  have h2 : ¬ (repB + 7 < repB) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [repMapC, if_pos h1]; rfl
  · rw [repMapC, if_neg h2, Nat.add_sub_cancel_left]; rfl
  · rw [repMapC, if_neg h2, Nat.add_sub_cancel_left]; decide

/-- (−) A base whose `shiftTarget` is `1` does not meet `STBase`. -/
theorem stBase_neg (impl : OpImpl) : ¬ STBase fun _ => { impl with shiftTarget := fun _ _ _ _ => 1 } := by
  intro h
  have := congrFun (congrFun (congrFun (congrFun (h .N4) 0) #[]) #[]) #[]
  rw [shiftTargetI_zero _ _ _ _ fun _ _ => rfl] at this
  exact one_ne_zero this

end N4s
end FR
