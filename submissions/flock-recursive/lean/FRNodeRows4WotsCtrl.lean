-- New for `flock-recursive` (stage S-E13b, track L-circ): controls of the node rows.
import FRNodeRows4Agg

/-!
# Controls for the S-E13b node rows

| Definition | (+) | (−) |
|---|---|---|
| `boolR` | `boolR_pos`: `0`, `1` pass | `boolR_neg`: `y` fails |
| `muxR` | `muxR_ctl`: selector `1` takes `x`, `0` takes `y` | `muxR_neg`: selector `1` with `m = y ≠ x` fails |
| `digV` | `digV_ctl`: bits `(1, 1)` give digit 3 | `digV_ctl`: bits `(0, 1)` give 2, not 1 |
| `gW` (the checksum's generator) | `gW_order` (order above 1023) | `one_not_inj`: `1` would not separate exponents (`1^0 = 1^1`) |
| `lastR` | `lastR_eq` (64 for `k = 1 … 4`: R-A′) | `lastR_no_spacer`: without the spacer `k = 2` would not fill its last block |
| `ind` | `ind_ctl`: at `k = 2 < maxK`, `ind 2 = 1`, `ind 1 = ind 3 = 0` | (the same) |
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

theorem boolR_pos (κ : NodeKind) (c : ℕ) (hc : c ≠ κ.oneCell) (b : F) (hb : b = 0 ∨ b = 1) :
    (boolR κ c).Holds (fun x => if x = κ.oneCell then 1 else if x = c then b else 0) := by
  rcases hb with rfl | rfl <;> simp [Row.Holds, boolR, one, hc]

theorem y_not_bit : F.y * (1 - F.y) ≠ 0 := by decide +kernel

theorem boolR_neg (κ : NodeKind) (c : ℕ) (hc : c ≠ κ.oneCell) :
    ¬ (boolR κ c).Holds (fun x => if x = κ.oneCell then 1 else if x = c then F.y else 0) := by
  simp only [Row.Holds, boolR, one, Lin.ev_cell, Lin.ev_sub, Lin.ev_nil, if_neg hc, if_true]
  exact y_not_bit

theorem muxR_ctl (x y : F) : (muxR (Lin.cell 0) (Lin.cell 1) (Lin.cell 2) (Lin.cell 3)).Holds
      (fun c => if c = 0 then 1 else if c = 1 then x else if c = 2 then y else x) ∧
    (muxR (Lin.cell 0) (Lin.cell 1) (Lin.cell 2) (Lin.cell 3)).Holds
      (fun c => if c = 0 then 0 else if c = 1 then x else if c = 2 then y else y) := by
  simp [Row.Holds, muxR]

theorem muxR_neg : ¬ (muxR (Lin.cell 0) (Lin.cell 1) (Lin.cell 2) (Lin.cell 3)).Holds
    (fun c => if c = 0 then 1 else if c = 1 then 1 else if c = 2 then 0 else 0) := by
  simp [Row.Holds, muxR]

theorem digV_ctl (κ : NodeKind) (σ : ℕ) :
    digV κ σ (fun _ => 1) 0 = 3 ∧ digV κ σ (fun c => if c = digC κ σ 0 then 0 else 1) 0 = 2 := by
  refine ⟨by simp [digV, bv], ?_⟩
  have h : digC κ σ (2 * 0 + 1) ≠ digC κ σ 0 := by simp [digC, Lc]
  simp [digV, bv, h]

theorem one_not_inj : (1 : F) ^ 0 = (1 : F) ^ 1 ∧ (0 : ℕ) ≠ 1 := by simp

theorem lastR_no_spacer : (1 + 2 * (segB - 1)) - 64 * ((1 + 2 * (segB - 1) + 63) / 64 - 1) = 63 := by decide

theorem ind_ctl {w : Asg} (hP : ∀ i < NodeKind.N4.maxK,
    (selSum .N4 (N4c.sub .N4 0 i)).ev w = if i < 2 then 1 else 0) :
    (ind .N4 (actW .N4 0) 2).ev w = 1 ∧ (ind .N4 (actW .N4 0) 1).ev w = 0 ∧ (ind .N4 (actW .N4 0) 3).ev w = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [ind_ev (k := 2) (by norm_num) (by decide) hP (by norm_num) (by decide)] <;> simp

end W4
end FR
