-- New for `flock-recursive` (stage S-E14, track L-circ): the controls of `FRNodeRows4Rep` and
-- `FRNodeRows4RepS`.
import FRNodeRows4RepS

/-!
# Controls for the replay templates

| Definition | (+) | (−) |
|---|---|---|
| `impRX` | `impRX_ctl`: a one-op program `linkWAll`: uncovered, its 8 registers are assumed | covered by `rtLinkSeg`, none is (`impRX_ctl`) |
| `repRowsX` | `repRows_ctl`: covered, the op's 8 `zeroRows` | uncovered, no row |
| `zeroRows` | `zeroRows_pos`: zero output cells meet them | `zeroRows_neg`: a nonzero cell does not |
| `LinkZero` | `linkZero_implC` | `linkZero_neg`: a base with `linkWAll = 1^8` does not meet it |
| `rtSeg` | `rtSeg_ctl`: covers `linkWAll` at prototype 1 | covers nothing at prototype 0, and not `targetS` |
| `SlotImpR` | `slotImp_of_rep` (from it, `SlotImp`) | `slotImpR_of_imp`: it asks nothing beyond `SlotImp` |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-- The controls' parameters: `one` is cell 0, no selector. -/
def repCtlP : Params := ⟨Lin.cell 0, fun _ => []⟩

/-- (+) Uncovered, a `linkWAll` import's 8 registers are assumed; (−) covered by `rtLinkSeg`, none. -/
theorem impRX_ctl :
    impRX noExt repCtlP RT.none (CS.init 1) [.linkWAll 0 0] = List.range' 0 1 ∧
      impRX noExt repCtlP rtLinkSeg (CS.init 1) [.linkWAll 0 0] = [] := by
  decide

/-- (+) Covered, the op's rows are `zeroRows` on its fresh cells (8 rows); (−) uncovered, none. -/
theorem repRows_ctl :
    (repRowsX noExt repCtlP rtLinkSeg (CS.init 1) [.linkWAll 0 0]).length = 8 ∧
      repRowsX noExt repCtlP RT.none (CS.init 1) [.linkWAll 0 0] = [] := by
  decide

/-- An `af 8` slot on cells `1 … 8`. -/
def ctlSlot : Slot := some (.af 8, (List.range 8).map fun j => Lin.cell (1 + j))

/-- (+) `one = 1` and zero output cells meet `zeroRows`. -/
theorem zeroRows_pos : ∀ r ∈ zeroRows repCtlP [ctlSlot], r.Holds fun c => if c = 0 then 1 else 0 := by
  intro r hr
  simp only [zeroRows, ctlSlot, repCtlP, List.length_map, List.length_range, and_self, if_true,
    List.map_map, List.mem_map, List.mem_range] at hr
  obtain ⟨j, -, rfl⟩ := hr
  simp [Row.Holds, Lin.cell, Lin.ev]

/-- (−) A nonzero output cell does not. -/
theorem zeroRows_neg : ¬ ∀ r ∈ zeroRows repCtlP [ctlSlot], r.Holds fun c => if c = 0 ∨ c = 1 then 1 else 0 := by
  intro h
  have := h ⟨Lin.cell 0, Lin.cell 1, []⟩ (by simp [zeroRows, ctlSlot, repCtlP]; exact ⟨0, by norm_num⟩)
  simp [Row.Holds, Lin.cell, Lin.ev] at this

/-- (−) A base whose `linkWAll` at `L32` is `1^8` does not meet `LinkZero`. -/
theorem linkZero_neg (impl₀ : OpImpl) :
    ¬ LinkZero { impl₀ with linkWAll := fun _ _ _ => Array.replicate nLinkFam 1 } := by
  intro h
  have := congrArg (fun a : Array F => a.getD 0 0) (h #[] #[])
  simp [nLinkFam] at this

/-- (+) `rtSeg` covers `linkWAll` at prototype 1; (−) nothing at prototype 0, and not `targetS`. -/
theorem rtSeg_ctl : (rtSeg 1).cov (.linkWAll 0 0) = true ∧ (rtSeg 0).cov (.linkWAll 0 0) = false ∧
    (rtSeg 1).cov (.targetS 0) = false := by
  decide

end N4s
end FR
