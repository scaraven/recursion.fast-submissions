-- New for lvm6 (WP W1). The ladder's weight facts at the deployed levels (`MidOK.hWH`,
-- `MidOK.hglue`, `FinOK.hchk`) for the admitted weights `wokE`: a folded admitted weight ignores the
-- high part `Ŵ_κ·H` (the low part of a multiple of `W_κ` is zero, leanVM `lowMsg_msgPoly_add`); the
-- glue keeps tables affine in each variable; and the final level's terminal check `chkE` (the tail
-- sumcheck of `Lvm6WhirSum` on the folded table and the final message's multilinear extension)
-- rejects a final polynomial that violates the claim.
import Lvm6WhirWeights
import Lvm6WhirE2
import Lvm6WhirNum

/-!
# The deployed weight facts (W1)

* `MA_wFolds`: folding keeps a table affine in each remaining variable.
* `hWH_E`: **`MidOK.hWH`** at `tailE2`; `hglue_E`: **`MidOK.hglue`** at `tailE2`.
* `cubeSum_eq_sum`, `mleL g`: the message's multilinear extension on lists, `mleL_bl`, `MA_mleL`.
* `chkE g κ w σ s`: the tail sumcheck; **`hchk_E`**: `FinOK.hchk` at `finE2` (escape `eSum`).
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir Polynomial Finset
open scoped ENNReal

theorem MA_wFolds {m : ℕ} : ∀ (j n : ℕ) (rs : List (Rnd E2)) (w : WtE.Wt (m + j)),
    MA (j + n) w.2 → MA n (wFolds (m := m) WtE j rs w).2
  | 0, n, _, _, h => by rw [Nat.zero_add] at h; exact h
  | j + 1, n, rs, w, h => MA_wFolds (m := m) j n rs.tail _
      (MA.fold (by rwa [show j + 1 + n = j + n + 1 by omega] at h) _)

theorem vanNF_eq (κ : ℕ) :
    vanNF κ = C (algebraMap K E2 (vanishingAt κ (basisVec κ))⁻¹) * vanF κ := by
  simp [vanNF, normVanishing, vanF, Polynomial.map_mul]

theorem lowMsgF_highF {κ ℓ : ℕ} (hκ : κ ≤ 64) (hi : List E2) : lowMsgF κ (highF κ ℓ hi) = 0 := by
  rw [highF, vanNF_eq, mul_assoc, mul_left_comm, lowMsgF_vanF_mul hκ]

/-- **`MidOK.hWH`** at a deployed level: a folded admitted weight ignores the high part. -/
theorem hWH_E {ko ℓ : ℕ} (hko : ko + 1 ≤ 64) (w : WtE.Wt (0 + ℓ)) (hw : wokE (ko + 1) ℓ w)
    (rs : List (Rnd E2)) (hi : List E2) :
    WtE.den (wFolds WtE ℓ rs w) (fun _ ↦ highF (ko + 1) ℓ hi) = 0 := by
  show denE _ _ _ = 0
  rw [wFolds_fst, hw.1]
  simp [denE, lowMsgF_highF hko]

/-- **`MidOK.hglue`** at a deployed level. -/
theorem hglue_E {ko ℓ κ' ℓ' t h : ℕ} (hκ : 0 + ℓ' + κ' = ko + 1) (w : WtE.Wt (0 + ℓ))
    (hw : wokE (ko + 1) ℓ w) (rs : List (Rnd E2)) (o : TailOut E2 ko t (2 ^ h)) :
    wokE κ' ℓ' (wGlueE κ' ℓ' ko t h (wFolds WtE ℓ rs w) o) := by
  refine ⟨rfl, ?_⟩
  have hn : ℓ' + κ' = ko + 1 := by omega
  rw [hn]
  have hΦ : MA (ko + 1) (wFolds (m := 0) WtE ℓ rs w).2 :=
    MA_wFolds ℓ (ko + 1) rs w hw.2
  exact MA_add (MA_add hΦ (MA_mul_const _ (MA_eqL o.z)))
    (MA_sum _ _ fun k _ ↦ MA_mul_const _ (MA_colL _ _))

/-! ## The final level's terminal check -/

theorem cubeSum_eq_sum : ∀ (n : ℕ) (f : List E2 → E2), cubeSum n f = ∑ c : Fin n → Bool, f (bl c)
  | 0, f => by simp [cubeSum, bl_zero]
  | n + 1, f => by
    rw [cubeSum, cubeSum_eq_sum n, cubeSum_eq_sum n, sum_cube_succ]
    simp [bl_cons]

/-- The multilinear extension of a message on lists. -/
noncomputable def mleL {κ : ℕ} (g : (Fin κ → Bool) → E2) (y : List E2) : E2 :=
  ∑ c, g c * prodL (fun i X ↦ if h : i < κ then (if c ⟨i, h⟩ then X else 1 - X) else 1) κ y

theorem mleL_bl {κ : ℕ} (g : (Fin κ → Bool) → E2) (c' : Fin κ → Bool) : mleL g (bl c') = g c' := by
  classical
  simp only [mleL, prodL_bl]
  rw [Finset.sum_eq_single c']
  · rw [Finset.prod_eq_one, mul_one]
    intro i _
    simp only [i.isLt, ↓reduceDIte, Fin.eta]
    by_cases h : c' i <;> simp [h]
  · intro c _ hc
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ c' i := by
      by_contra hn
      exact hc (funext fun i ↦ not_not.mp ((not_exists.mp hn) i))
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    simp only [i.isLt, ↓reduceDIte, Fin.eta]
    cases h1 : c i <;> cases h2 : c' i <;> simp_all
  · simp

theorem MA_mleL {κ : ℕ} (g : (Fin κ → Bool) → E2) : MA κ (mleL g) :=
  MA_sum _ _ fun c _ ↦ MA_mul_const _ (MA_prodL κ _ fun i X ↦ by split_ifs <;> ring)

/-- The final polynomial's message. -/
def msgOf (κ : ℕ) (s : List E2) : (Fin κ → Bool) → E2 := fun u ↦ s.getD (bitsToNat u) 0

/-- **The terminal check** (`3 × R(2, g)` and `Φ(τ)·m̃(τ) = claim`). -/
noncomputable def chkE (g κ : ℕ) (w : WtE.Wt 0) (σ : E2) (s : List E2) : VerifierProgram Bool :=
  sumP chalE2 g w.2 (mleL (msgOf κ s)) κ [] σ

/-- The claim on the final polynomial is the cube sum of the table times the message. -/
theorem den_fpolyE {κ ℓ : ℕ} (hκ : κ ≤ 64) (w : WtE.Wt 0) (hw : w.1 = κ) (s : List E2) :
    WtE.den w (fpolyE κ ℓ s) = cubeSum κ fun x ↦ w.2 ([] ++ x) * mleL (msgOf κ s) ([] ++ x) := by
  obtain ⟨κw, Φ⟩ := w
  simp only at hw
  subst hw
  show denE _ _ _ = _
  rw [cubeSum_eq_sum]
  simp only [denE, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_unique, bl_zero, List.nil_append,
    fpolyE, map_add, lowMsgF_msgPolyF hκ, lowMsgF_highF hκ, add_zero, mleL_bl, msgOf]

theorem eSum_le_εI : eSum E2 2 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  unfold eSum
  rw [card_E2]
  have h2 : ((2 ^ 128 : ℕ) : ℝ≥0∞) = 2 ^ 128 := by norm_num
  rw [h2, div_eq_mul_inv, ENNReal.inv_pow]
  have hx : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc (2 : ℝ≥0∞)⁻¹ ^ 2 * 2 * 2⁻¹ ^ 128 = ((2 : ℝ≥0∞)⁻¹ * 2) * 2⁻¹ ^ 129 := by ring
    _ = (2 : ℝ≥0∞)⁻¹ ^ 129 := by rw [hx, one_mul]
    _ = ((2 : ℝ≥0∞) ^ 2 * 2⁻¹ ^ 2) * 2⁻¹ ^ 129 := by rw [two_pow_mul_inv_pow, one_mul]
    _ = 4 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by ring
    _ ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by gcongr; norm_num

/-- **`FinOK.hchk`** at the final level: the terminal check rejects a violated claim. -/
theorem hchk_E {κ ℓ gT : ℕ} {εmax : ℝ≥0∞} (hκ : κ ≤ 64) (hg : gT ≤ 64) (he : eSum E2 gT < 1)
    (heT : eSum E2 gT ≤ εmax) (w : WtE.Wt (0 + ℓ)) (hw : wokE κ ℓ w) (σ : E2)
    (rs : List (Rnd E2)) (s : List E2) :
    Nonempty (Spec (chkE gT κ (wFolds WtE ℓ rs w) (foldsC ℓ rs σ) s)
      (fun _ ↦ WtE.den (wFolds WtE ℓ rs w) (fpolyE κ ℓ s) ≠ foldsC ℓ rs σ)
      (fun b _ ↦ b = false) εmax 0 0) :=
  ⟨(sumSpec chalE2 gT hg he heT _ _ κ [] _
      (MA_wFolds (m := 0) ℓ κ rs w hw.2) (MA_mleL _)).mono
    (fun _ h ↦ by rwa [den_fpolyE hκ _ (by rw [wFolds_fst]; exact hw.1)] at h)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end Lvm6.Whir
