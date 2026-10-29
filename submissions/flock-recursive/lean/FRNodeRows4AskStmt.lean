-- New for `flock-recursive` (PACK-4.4 §1.3 `input`/`stmtOk4`, PK-m7; track IMP): the statement
-- blocks' message ties (rows only; their soundness is `FRNodeRows4AskStmtS`).
import FRNodeRows4AggChk

/-!
# The statement rows (PK-m7)

Every verifier slot `v` has three statement blocks in H: `hashA` at `stmtB κ + 3v`, `hashB1`,
`hashB2` after it (`N4c.stmtIvs`). Their Z truths hash their message cells, but no row ties the
messages to the slot's stream, so the blocks' outputs say nothing about the slot. These rows tie
them (R-A′: the stream's `stmt` field is element-aligned, elements `13 … 20` of the segment, and is
honestly the padded message blocks `tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64` or
`tagNode ‖ c₁ ‖ c₂ ‖ 0^63`), so whole-element copies suffice:

* **`stmtRowsS`** (segment slots, gated by the sub-slot's activity `act a i`): `hashA`'s message
  elements `4 … 7` are the segment's stream elements `13 … 16`. `hashA`'s output is then
  `leafStmt h n` of the slot's view: the cells of the slot's `input c` (`FRNodeRows4AskStmtS`).
* **`stmtRowsP`** (the previous node, ungated: slot 0 is always active): `hashB1`'s message is
  elements `13 … 16`, `hashB2`'s elements `17 … 20`, `hashB2.h_in = hashB1.h_out`, and
  `hashB2.h_out` is the public `c₁` (`seedC κ 0 2, 3`). Then `nodeStmt` of the `stmt` field is
  `c₁`: the previous node's `stmtOk4`.

`stmtRows κ act` is folded into slot 1's node rows (`W4.xRowsA`), next to B4's check rows.
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-- `one·(x − y) = 0`: cell `x` is cell `y` (with `w one = 1`). -/
def eqRow (one x y : ℕ) : Row := ⟨Lin.cell one, (Lin.cell x).sub (Lin.cell y), []⟩

/-- `g·(x − y) = 0`: where `g` is `1`, cell `x` is cell `y`. -/
def eqRowG (g : Lin) (x y : ℕ) : Row := ⟨g, (Lin.cell x).sub (Lin.cell y), []⟩

/-- **The segment slots' statement rows**: sub-slot `i` of aggregate `a` (slot `sub κ a i`), where
active (`act a i`), has `hashA`'s message element `4 + e` equal to its stream element `13 + e`,
`e < 4`. -/
def stmtRowsS (κ : NodeKind) (act : ℕ → ℕ → Lin) : List Row :=
  (List.range (nAgg κ)).flatMap fun a => (List.range κ.maxK).flatMap fun i =>
    (List.range 4).map fun e =>
      eqRowG (act a i) (hc (stmtB κ + 3 * sub κ a i) (4 + e)) (sE κ (aggChild κ a) i (13 + e))

/-- **The previous node's statement rows** (none without one): `hashB1`'s message is stream
elements `13 … 16`, `hashB2`'s `17 … 20`, `hashB2.h_in = hashB1.h_out`, `hashB2.h_out = c₁`'s cells. -/
def stmtRowsP (κ : NodeKind) : List Row :=
  if κ.hasPrev then
    (List.range 4).map (fun e => eqRow κ.oneCell (hc (stmtB κ + 1) (4 + e)) (sE κ 0 0 (13 + e))) ++
    (List.range 4).map (fun e => eqRow κ.oneCell (hc (stmtB κ + 2) (4 + e)) (sE κ 0 0 (17 + e))) ++
    (List.range 2).map (fun h => eqRow κ.oneCell (hc (stmtB κ + 2) h) (hc (stmtB κ + 1) (2 + h))) ++
    (List.range 2).map (fun h => eqRow κ.oneCell (hc (stmtB κ + 2) (2 + h)) (seedC κ 0 (2 + h)))
  else []

/-- **The `input` cells of a slot region** (M-relative): `inOff + 2j + h` holds half `h` of the
slot's `vk` (`j = 0`) or `c` (`j = 1`), between arena₁ (`< 387,752`) and the bits (`≥ 389,120`). The
`input` ask template (`N4s.AT.inp`) ties the compiled `input` registers' cells to them. -/
def inOff : ℕ := 388096

/-- **The `input` rows** (ungated): every slot's `input` cells are its `vk`'s public cells and its
statement cells — a segment slot's `hashA` output, the previous node's public `c₁`. -/
def inpRows (κ : NodeKind) : List Row :=
  ((List.range (nAgg κ)).flatMap fun a => (List.range κ.maxK).flatMap fun i =>
    (List.range 2).flatMap fun h =>
      [eqRow κ.oneCell (κ.oneCell + sub κ a i * slotM4 + inOff + h) (seedC κ (aggChild κ a) h),
       eqRow κ.oneCell (κ.oneCell + sub κ a i * slotM4 + inOff + 2 + h) (hc (stmtB κ + 3 * sub κ a i) (2 + h))]) ++
  if κ.hasPrev then
    (List.range 2).flatMap fun h =>
      [eqRow κ.oneCell (κ.oneCell + inOff + h) (seedC κ 0 h),
       eqRow κ.oneCell (κ.oneCell + inOff + 2 + h) (seedC κ 0 (2 + h))]
  else []

/-- **The statement and `input` rows** (PK-m7, IMP). -/
def stmtRows (κ : NodeKind) (act : ℕ → ℕ → Lin) : List Row := stmtRowsS κ act ++ stmtRowsP κ ++ inpRows κ

theorem stmtRows_length_le (κ : NodeKind) (act : ℕ → ℕ → Lin) : (stmtRows κ act).length ≤ 80 := by
  cases κ <;> simp [stmtRows, stmtRowsS, stmtRowsP, inpRows, List.length_flatMap, nAgg, NodeKind.maxK,
    NodeKind.hasPrev, NodeKind.segSlots]

theorem eqRow_holds {w : Asg} {one x y : ℕ} (hone : w one = 1) (h : (eqRow one x y).Holds w) : w x = w y := by
  simp only [eqRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hone, one_mul] at h
  exact sub_eq_zero.1 h

theorem eqRowG_holds {w : Asg} {g : Lin} {x y : ℕ} (hg : g.ev w = 1) (h : (eqRowG g x y).Holds w) :
    w x = w y := by
  simp only [eqRowG, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, hg, one_mul] at h
  exact sub_eq_zero.1 h

/-- (±) **The rows' controls**: an inactive slot's row holds whatever its cells (`g = 0`); an
active slot's row with differing cells fails; the ungated row with equal cells holds. -/
theorem eqRow_ctl :
    (eqRowG [] 0 1).Holds (fun i => if i = 0 then 1 else 0) ∧
      ¬ (eqRowG (Lin.cell 2) 0 1).Holds (fun i => if i = 1 then 0 else 1) ∧
      (eqRow 2 0 1).Holds (fun _ => 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [eqRowG, eqRow, Row.Holds, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil]

end W4
end FR
