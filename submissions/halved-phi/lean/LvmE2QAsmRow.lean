-- New for lvm2 E2-FT (E2F-B): the row switch's auxiliary rows in looped blocks (blob v2). Booleanity runs over the
-- 8,192 bit words, recomposition over the 128 row words, transposition over the 64 slices. Each row family is then
-- one looped row, not 8,192 / 128 / 128 one-instance rows. `rowAuxL_sound` keeps `rowAux_sound`'s conclusion.
import LvmQRingRowSem

/-!
# The row switch's looped auxiliary blocks (`rowAuxL`)

* **`rowAuxL bw tB qs`**: three blocks.
  * `2^13` iterations of the booleanity row on the word `bw + t`.
  * `2^7` iterations of the recomposition row: `t_j + Σ_i x^i·b(bw + i + 64 j) = 0`.
  * `2^6` iterations of the two transposition rows: `s_i^(h) + Σ_j x^j·b(bw + 64 (j + 64 h) + i) = 0`.
* **`aRowHolds_congr`**: a row's truth depends only on its entries' matrices and weighted values.
* **`rowAux_of_L`**: where the looped blocks hold, every row of the flat `rowAux` holds at iteration `0`.
* **`rowAuxL_sound`**: hence `rowAux_sound`'s conclusion: the free row words are V's `rowWordD` of the slices.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Typed

/-- The looped booleanity row: the word `bw + t` at iteration `t`. -/
def rowBoolL (bw : Nat) : ARow := ⟨[(0, .word bw 1, 1), (1, .word bw 1, 1), (2, .word bw 1, 1)]⟩

/-- The looped recomposition row: at iteration `j`, `t_j + Σ_i x^i·b_{j,i} = 0`. -/
def rowRecL (bw tB : Nat) : ARow :=
  ⟨(2, .cell ⟨.K, tB, [1]⟩, 1) :: (List.range 64).map fun i => (2, .word (bw + i) 64, xPowW i)⟩

/-- The looped transposition row of coordinate `h`: at iteration `i`, `s_i^(h) + Σ_j x^j·b_{j+64h, i} = 0`. -/
def rowTrL (bw qs h : Nat) : ARow :=
  ⟨(2, .cell ⟨.K, qs + h, [2]⟩, 1) :: (List.range 64).map fun j => (2, .word (bw + 64 * (j + 64 * h)) 1, xPowW j)⟩

/-- **The row switch's looped auxiliary blocks.** -/
def rowAuxL (bw tB qs : Nat) : List ABlk :=
  [⟨13, [rowBoolL bw]⟩, ⟨7, [rowRecL bw tB]⟩, ⟨6, [rowTrL bw qs 0, rowTrL bw qs 1]⟩]

/-- A row's weighted values at an iteration. -/
def aRowVals (lay : Lay) (z : ℕ → FK) (j : ℕ) (r : ARow) : List (ℕ × FE) :=
  r.ops.map fun e ↦ (e.1, e.2.2 * aopVal lay z j e.2.1)

theorem aRowMat_vals (lay : Lay) (z : ℕ → FK) (j : ℕ) (r : ARow) (o : ℕ) :
    aRowMat lay z j r o = (((aRowVals lay z j r).filter fun p ↦ p.1 == o).map Prod.snd).sum := by
  unfold aRowMat aRowVals
  rw [List.filter_map, List.map_map]
  rfl

/-- **A row's truth depends only on its weighted values.** -/
theorem aRowHolds_congr {lay : Lay} {z : ℕ → FK} {j j' : ℕ} {r r' : ARow}
    (h : aRowVals lay z j r = aRowVals lay z j' r') : ARowHolds lay z j r ↔ ARowHolds lay z j' r' := by
  unfold ARowHolds
  rw [aRowMat_vals, aRowMat_vals, aRowMat_vals, aRowMat_vals, h, ← aRowMat_vals, ← aRowMat_vals, ← aRowMat_vals,
    ← aRowMat_vals]

/-- **Where the looped blocks hold, the flat block's rows hold** (at iteration `0`). -/
theorem rowAux_of_L (lay : Lay) (z : ℕ → FK) {bw tB qs : ℕ}
    (h : ∀ B ∈ rowAuxL bw tB qs, ∀ j < 2 ^ B.l, ∀ r ∈ B.rows, ARowHolds lay z j r) :
    ∀ r ∈ (rowAux bw tB qs).rows, ARowHolds lay z 0 r := by
  have hB := h _ (List.mem_cons_self)
  have hR := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hT := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro r hr
  simp only [rowAux, rowBoolRows, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hr
  rcases hr with (⟨j, hj, i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨hh, hh2, i, hi, rfl⟩
  · refine (aRowHolds_congr ?_).mpr (hB (64 * j + i) (by norm_num; omega) _ List.mem_cons_self)
    simp only [aRowVals, rowBoolL, rowBit, List.map_cons, List.map_nil, aopVal, Nat.mul_zero, Nat.add_zero,
      Nat.one_mul, Nat.add_assoc]
  · refine (aRowHolds_congr ?_).mpr (hR j (by norm_num; omega) _ List.mem_cons_self)
    simp only [aRowVals, rowRecL, rowRecRow, rowBit, List.map_cons, List.map_map, Function.comp_def, aopVal,
      Addr.at, Lvm.Loop.dot, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.mul_comm]
  · have hrow : rowTrL bw qs hh ∈ [rowTrL bw qs 0, rowTrL bw qs 1] := by
      obtain rfl | rfl : hh = 0 ∨ hh = 1 := by omega
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    refine (aRowHolds_congr ?_).mpr (hT i (by norm_num; omega) _ hrow)
    simp only [aRowVals, rowTrL, rowTrRow, rowBit, List.map_cons, List.map_map, Function.comp_def, aopVal,
      Addr.at, Lvm.Loop.dot, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.mul_comm]

/-- **The row switch's looped rows are sound** (`rowAux_sound` on the looped blocks): the free row words are
`rowWordD` of the slices. -/
theorem rowAuxL_sound (lay : Lay) (z : ℕ → FK) {bw tB qs : ℕ}
    (h : ∀ B ∈ rowAuxL bw tB qs, ∀ j < 2 ^ B.l, ∀ r ∈ B.rows, ARowHolds lay z j r) {j : ℕ} (hj : j < 128) :
    (memOf lay z).k (tB + j) = rowWordD (slicesOf (memOf lay z) qs) j :=
  rowAux_sound lay z (rowAux_of_L lay z h) hj

end Lvm.Q2
