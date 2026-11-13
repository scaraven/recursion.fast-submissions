-- Split out of `LvmFinStatic` (lvm2 roll 8, B1-IX): QL's one-pass program check (`segsOkF`, `segsOkF_eq`), generic
-- in the program, so that the typed path's static guard (`LvmQTypedInst`) reads it without importing the bus
-- program's closed constants.
import LvmQBuildWf

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## The program check in one pass per block (adapted from WP-16a-QFX's uncommitted
`LvmQAsmFactsFast`): `blockOkAt` recomputes a row's rank (a prefix of the template) per row, quadratic
in the template (6.3 s natively at `P20`); `rowsOkF` advances a pointer, with the block's widths
computed once. -/

/-- A block's rows from the pointer `c` on (the pointer advanced past each row). -/
def rowsOkF (dims : List Nat) (tw : Ty → Nat) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC c.at dims tw r && rowsOkF dims tw (c.adv [.row r]) rs

/-- The widths `k`, `e` as a function of the memory (built inside the per-row check: the compiler
must not re-evaluate `B.tw` per operand). -/
def twKE (k e : Nat) : Ty → Nat
  | .K => k
  | .E => e

/-- A block's rows with the widths passed as numbers (evaluated once, at the call). -/
def rowsOkKE (dims : List Nat) (k e : Nat) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC c.at dims (twKE k e) r && rowsOkKE dims k e (c.adv [.row r]) rs

theorem rowsOkKE_eq (dims : List Nat) (k e : Nat) : ∀ (c : Ptr) (rs : List Row),
    rowsOkKE dims k e c rs = rowsOkF dims (twKE k e) c rs
  | _, [] => rfl
  | c, r :: rs => by rw [rowsOkKE, rowsOkF, rowsOkKE_eq dims k e _ rs]

theorem twKE_tw (B : Block) : twKE (B.tw .K) (B.tw .E) = B.tw := by
  funext τ; cases τ <;> rfl

/-- `blockOkAt` in one pass. -/
def blockOkF (p : Ptr) (B : Block) : Bool := rowsOkKE B.dims (B.tw .K) (B.tw .E) p B.tpl

/-- `segsOk` with `blockOkF`. -/
def segsOkF : Ptr → List Seg → Bool
  | _, [] => true
  | p, .row r :: δ => rowOkC p.at [] (fun _ => 0) r && segsOkF (p.adv [.row r]) δ
  | p, .blk B :: δ => blockOkF p B && segsOkF (p.adv [.blk B]) δ

theorem adv_row_at (c : Ptr) (r : Row) (τ : Ty) : (c.adv [.row r]).at τ = c.at τ + r.w τ := by
  cases τ <;> simp [Ptr.adv, Ptr.at, segsW, Seg.w]

theorem rowsOkF_eq (dims : List Nat) (tw : Ty → Nat) : ∀ (c : Ptr) (rs : List Row),
    rowsOkF dims tw c rs = (List.range rs.length).all fun t =>
      rowOkC (fun τ => c.at τ + ((rs.take t).map (Row.w τ)).sum) dims tw (rs.getD t default)
  | c, [] => by simp [rowsOkF]
  | c, r :: rs => by
    rw [rowsOkF, rowsOkF_eq dims tw _ rs, List.length_cons, List.range_succ_eq_map, List.all_cons,
      List.all_map]
    have h0 : (fun τ => c.at τ + (((r :: rs).take 0).map (Row.w τ)).sum) = c.at := by
      funext τ; simp
    have h1 : ∀ t, (fun τ => c.at τ + (((r :: rs).take (t + 1)).map (Row.w τ)).sum) =
        fun τ => (c.adv [.row r]).at τ + ((rs.take t).map (Row.w τ)).sum := fun t => by
      funext τ; rw [adv_row_at]; simp [Nat.add_assoc]
    simp only [h0, List.getD_cons_zero, Function.comp_def, h1, List.getD_cons_succ]

theorem blockOkF_eq (p : Ptr) (B : Block) : blockOkF p B = blockOkAt p B := by
  rw [blockOkF, rowsOkKE_eq, twKE_tw, rowsOkF_eq]; rfl

theorem segsOkF_eq : ∀ (p : Ptr) (δ : List Seg), segsOkF p δ = segsOk p δ
  | _, [] => rfl
  | p, .row r :: δ => by rw [segsOkF, segsOk, segsOkF_eq _ δ]
  | p, .blk B :: δ => by rw [segsOkF, segsOk, segsOkF_eq _ δ, blockOkF_eq]

end Lvm.Fin
