-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4; stage S-E13b, track L-circ).
import FRNodeRows4Wots
import FRNodeRows4AggChk
import FRNodeRows4AskStmt

/-!
# The node rows of S-E13b, as one list per slot (`extRows4`)

S-E13a's link region (`FRNodeRows4.linkRows4 = linkRowsB4 ++ packRows4 ++ …`, the last `2^15` rows
of every slot region) takes the node rows after the pack rows. They all sit at **slot 1** (every
kind has one): both signed children's WOTS rows (`W4.wotsRows`) and every aggregate's `aggPad` rows
(`W4.padRows`), with the aggregates' activities read off the sub-slots' selector copies (`actW`,
equal to `Rev4.selSum` of the sub-slot).

* **`extRows4 κ σ`**: the list (`xRowsA`: with B4's aggregate check rows `chkRows` and IMP's statement
  rows `stmtRows`, PK-m7); empty at every
  slot but 1;
* **`xRows_length`**, **`extRows4_length_le`**: `N2` 7,862, `N4` 7,878, `N8` 7,904 rows (R-A′: `aggPad`
  without the element-7 decompositions), inside the link region after the pack rows.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-- **Sub-slot `i` of aggregate `a`'s activity** `S = Σ_ι s′_ι` (its three selector copies;
`Rev4.selSum κ (sub κ a i)`). -/
def actW (κ : NodeKind) (a i : ℕ) : Lin :=
  (List.range 3).map fun x => (κ.oneCell + (N4c.sub κ a i * slotM4 + 1 + x), (1 : F))

/-- **The node rows**: the signed children's WOTS rows, the aggregates' `aggPad` rows. -/
def xRows (κ : NodeKind) : List Row :=
  wotsRows κ 0 (actW κ (aggOf κ 0)) ++ wotsRows κ 1 (actW κ (aggOf κ 1)) ++
    (List.range (nAgg κ)).flatMap fun a => padRows κ a (actW κ a)

/-- **The aggregates' check rows** (B4, `FRNodeRows4AggChk`): every aggregate's, with its sub-slots'
activities. -/
def chkRows (κ : NodeKind) : List Row := (List.range (nAgg κ)).flatMap fun a => aggRowsC κ a (actW κ a)

/-- **The node rows with the aggregates' checks and the statement rows** (B4, IMP): S-E13b's, then
`chkRows`, then `stmtRows` (PK-m7, `FRNodeRows4AskStmt`). -/
def xRowsA (κ : NodeKind) : List Row := xRows κ ++ (chkRows κ ++ stmtRows κ (actW κ))

/-- **Slot `σ`'s node rows** (S-E13b, B4): the node rows at slot 1, none elsewhere. -/
def extRows4 (κ : NodeKind) (σ : ℕ) : List Row := if σ = 1 then xRowsA κ else []

/-- **The node rows' count**: `N2` 7,862, `N4` 7,878, `N8` 7,904 (per child 3,926 for a previous node,
`3,924 + 2·maxK + 2` for an aggregate; `aggPad` `6·(maxK − 1)` per aggregate). -/
theorem xRows_length : (xRows .N2).length = 7862 ∧ (xRows .N4).length = 7878 ∧ (xRows .N8).length = 7904 := by
  simp [xRows, wotsRows, idxRows, selRows, chainRows, chainRowsI, leafRows, pathRows, pathRowsT, rootRows,
    digRows, sumRows, padRows, List.length_flatMap, NodeKind.maxK, N4c.nAgg, NodeKind.hasPrev,
    N4c.isAgg, N4c.aggChild, NodeKind.segSlots, RecursionFast.wotsLen, RecursionFast.sigHeight, N4c.aggOf]

theorem chkRows_length_le (κ : NodeKind) : (chkRows κ).length ≤ 4152 := by
  have hn : nAgg κ ≤ 2 := by cases κ <;> decide
  rw [chkRows, List.length_flatMap]
  refine le_trans (List.sum_le_length_nsmul _ 2076 fun x hx => ?_) (by simp; omega)
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact aggRowsC_length_le κ a _

/-- **They fit S-E13a's link region** after its rows (`2^15 − 8 − 8,919 = 23,841`): S-E13b's
at most 7,904, B4's at most 4,152, IMP's statement and `input` rows at most 80. -/
theorem extRows4_length_le (κ : NodeKind) (σ : ℕ) : (extRows4 κ σ).length ≤ 12136 := by
  unfold extRows4
  split_ifs
  · obtain ⟨h2, h4, h8⟩ := xRows_length
    have := chkRows_length_le κ
    have := stmtRows_length_le κ (actW κ)
    rw [xRowsA, List.length_append, List.length_append]
    cases κ <;> omega
  · simp

end W4
end FR
