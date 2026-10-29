-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4; stage S-E13b, track L-circ).
import FRNodeRows4Wots

/-!
# The node rows of S-E13b, as one list per slot (`extRows4`)

S-E13a's link region (`FRNodeRows4.linkRows4 = linkRowsB4 ++ packRows4 ++ …`, the last `2^15` rows
of every slot region) takes the node rows after the pack rows. They all sit at **slot 1** (every
kind has one): both signed children's WOTS rows (`W4.wotsRows`) and every aggregate's `aggPad` rows
(`W4.padRows`), with the aggregates' activities read off the sub-slots' selector copies (`actW`,
equal to `Rev4.selSum` of the sub-slot).

* **`extRows4 κ σ`**: the list; empty at every slot but 1;
* **`xRows_length`**, **`extRows4_length_le`**: `N2` 7,992, `N4` 8,266, `N8` 8,680 rows, inside
  the 23,854 the link region leaves after S-E13a's rows.
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

/-- **Slot `σ`'s node rows** (S-E13b): the node rows at slot 1, none elsewhere. -/
def extRows4 (κ : NodeKind) (σ : ℕ) : List Row := if σ = 1 then xRows κ else []

/-- **The node rows' count**: `N2` 7,992, `N4` 8,266, `N8` 8,680 (per child 3,926 for a previous node,
`3,924 + 2·maxK + 2` for an aggregate; `aggPad` `135·(maxK − 1) + 1` per aggregate). -/
theorem xRows_length : (xRows .N2).length = 7992 ∧ (xRows .N4).length = 8266 ∧ (xRows .N8).length = 8680 := by
  -- the kind is a variable while the rows unfold: the kernel never evaluates the closed row lists
  refine ⟨?_, ?_, ?_⟩ <;> [generalize hk : NodeKind.N2 = k; generalize hk : NodeKind.N4 = k;
    generalize hk : NodeKind.N8 = k] <;>
  simp only [xRows, wotsRows, idxRows, selRows, chainRows, chainRowsI, leafRows, pathRows, pathRowsT, rootRows,
    digRows, sumRows, padRows, List.length_flatMap, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil, N4c.isAgg, N4c.aggChild, RecursionFast.wotsLen, RecursionFast.sigHeight,
    N4c.aggOf] <;>
  subst hk <;>
  simp [NodeKind.maxK, N4c.nAgg, NodeKind.hasPrev, NodeKind.segSlots, List.length_flatMap]

/-- **They fit S-E13a's link region** after its rows (`2^15 − 8 − 8,906 = 23,854`). -/
theorem extRows4_length_le (κ : NodeKind) (σ : ℕ) : (extRows4 κ σ).length ≤ 8680 := by
  unfold extRows4
  split_ifs
  · obtain ⟨h2, h4, h8⟩ := xRows_length
    cases κ <;> omega
  · simp

end W4
end FR
