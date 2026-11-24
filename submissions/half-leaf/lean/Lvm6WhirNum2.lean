-- New for lvm6 (WP W1). The OOD, query and final-query escapes of the deployed levels are at most
-- `εI = 7·2^-131` when PARAM admits their rows (`Lvm6Params.listOK`'s `C(ℓ, 2)·(κ + k)` at the OOD
-- grind, `queryMsgOK`'s `8(A−1)^w 2^128 + 8(w+1)ℓ' n^w ≤ 7·2^g n^w` at the query grind), for the
-- `TailIface`/`FinIface` instances of `Lvm6WhirCode` at `|E2| = 2^128`.
import Lvm6WhirCode
import Lvm6WhirNum

/-!
# The deployed groups' escapes (W1)

* `adm_le`: an admitted row `8c ≤ 7·2^g` has `2^-g · c / 2^128 ≤ εI` (from `Params.group_le_εI`).
* `qry_le`: the query message's form `2^-g ((w+1)ℓ'/2^128 + ((A−1)/n)^w) ≤ εI` from `queryMsgOK`.
* **`eOod_tailE2_le`**, **`eQry_tailE2_le`**, **`eFin_finE2_le`**.
-/

namespace Lvm6.Whir

open LeanVM.Parameters
open scoped ENNReal NNReal

/-- An admitted row's escape is at most `εI`. -/
theorem adm_le {c g : ℕ} (h : Lvm6.Params.admits c g = true) :
    (2 : ℝ≥0∞)⁻¹ ^ g * (c : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  have hn := Lvm6.Params.group_le_εI h
  have hc : ((((c : ℝ≥0) * (2 : ℝ≥0)⁻¹ ^ (128 + g) : ℝ≥0)) : ℝ≥0∞) ≤
      (((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0)) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hn
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two, ENNReal.coe_natCast,
    ENNReal.coe_ofNat] at hc
  refine le_of_eq_of_le ?_ hc
  rw [div_eq_mul_inv, show ((2 ^ 128 : ℕ) : ℝ≥0∞) = 2 ^ 128 by norm_num, ENNReal.inv_pow, pow_add]
  ring

/-- **The query message's escape** from PARAM's integer form (`B = A − 1`). -/
theorem qry_le {n w ℓ' B g : ℕ} (hn : 0 < n)
    (h : 8 * B ^ w * 2 ^ 128 + 8 * (w + 1) * ℓ' * n ^ w ≤ 7 * 2 ^ g * n ^ w) :
    (2 : ℝ≥0∞)⁻¹ ^ g * ((((w + 1) * ℓ' : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) +
      ((B : ℝ≥0∞) / n) ^ w) ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  set a : ℕ := (w + 1) * ℓ'
  have hcast : (8 : ℝ) * (B : ℝ) ^ w * (2 : ℝ) ^ 128 + 8 * (a : ℝ) * (n : ℝ) ^ w ≤
      7 * (2 : ℝ) ^ g * (n : ℝ) ^ w := by
    have : ((8 * B ^ w * 2 ^ 128 + 8 * a * n ^ w : ℕ) : ℝ) ≤ ((7 * 2 ^ g * n ^ w : ℕ) : ℝ) := by
      exact_mod_cast (show 8 * B ^ w * 2 ^ 128 + 8 * a * n ^ w ≤ 7 * 2 ^ g * n ^ w by
        simpa [a, mul_assoc] using h)
    push_cast at this
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) ^ w := pow_pos hnR w
  have hQ : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
  have hP : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have key : (2 : ℝ)⁻¹ ^ g * ((a : ℝ) / 2 ^ 128 + ((B : ℝ) / n) ^ w) ≤ 7 * (2 : ℝ)⁻¹ ^ 131 := by
    rw [div_pow, div_add_div _ _ hQ.ne' hN.ne', inv_pow, inv_pow, ← div_eq_inv_mul,
      div_div, div_le_iff₀ (by positivity)]
    have e : (2 : ℝ) ^ 131 = 8 * 2 ^ 128 := by norm_num
    rw [e]
    have hmul := mul_le_mul_of_nonneg_right hcast hQ.le
    calc (a : ℝ) * (n : ℝ) ^ w + 2 ^ 128 * (B : ℝ) ^ w
        = ((8 * (B : ℝ) ^ w * 2 ^ 128 + 8 * (a : ℝ) * (n : ℝ) ^ w) * 2 ^ 128) /
            (8 * 2 ^ 128) := by field_simp; ring
      _ ≤ (7 * (2 : ℝ) ^ g * (n : ℝ) ^ w * 2 ^ 128) / (8 * 2 ^ 128) := by gcongr
      _ = 7 * (8 * 2 ^ 128)⁻¹ * (2 ^ 128 * (n : ℝ) ^ w * 2 ^ g) := by field_simp
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hfin : (2 : ℝ≥0∞)⁻¹ ^ g * (((a : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) +
      ((B : ℝ≥0∞) / n) ^ w) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.div_ne_top (by simp) (by simp)
    · exact ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) hn0)
  rw [← ENNReal.toReal_le_toReal hfin
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.div_ne_top (by simp) (by simp))
    (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) hn0))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact key

/-- **The OOD group's escape** at a deployed level, from PARAM's admitted row `C(L', 2)·(ko + 1)`. -/
theorem eOod_tailE2_le {ko ℓ h κ' ℓ' h' kq t c : ℕ} {hκ : 0 + ℓ' + κ' = ko + 1}
    {hko : ko + 1 < 64} {hℓ : 1 ≤ ℓ} {hℓ' : ℓ ≤ 64} {hh : h ≤ 64} {hh' : h' ≤ 64} {hc : 0 < c}
    {hch : c * h ≤ 128} {ht : t ≤ (kq + 1) * c} (g Lst : ℕ)
    (hadm : Lvm6.Params.admits (Lst.choose 2 * (ko + 1)) g = true) :
    eOod (tailE2 ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht) g Lst ≤
      7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  unfold eOod
  rw [card_E2]
  exact adm_le hadm

/-- **The query message's escape** at a deployed level, from PARAM's `queryMsgOK` form. -/
theorem eQry_tailE2_le {ko ℓ h κ' ℓ' h' kq t c : ℕ} {hκ : 0 + ℓ' + κ' = ko + 1}
    {hko : ko + 1 < 64} {hℓ : 1 ≤ ℓ} {hℓ' : ℓ ≤ 64} {hh : h ≤ 64} {hh' : h' ≤ 64} {hc : 0 < c}
    {hch : c * h ≤ 128} {ht : t ≤ (kq + 1) * c} (g Lst A : ℕ)
    (hq : 8 * (A - 1) ^ t * 2 ^ 128 + 8 * (t + 1) * Lst * (2 ^ h) ^ t ≤ 7 * 2 ^ g * (2 ^ h) ^ t) :
    eQry (tailE2 ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht) g Lst A ≤
      7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  unfold eQry
  rw [card_E2]
  exact qry_le (by positivity) hq

/-- **The final position group's escape**, from PARAM's `queryMsgOK` form with no next list. -/
theorem eFin_finE2_le {κ ℓ h kq t c : ℕ} {hκ : κ < 64} {hℓ : 1 ≤ ℓ} {hℓ' : ℓ ≤ 64} {hh : h ≤ 64}
    {hc : 0 < c} {hch : c * h ≤ 128} {ht : t ≤ (kq + 1) * c} (g A : ℕ)
    (hq : 8 * (A - 1) ^ t * 2 ^ 128 + 8 * (t + 1) * 0 * (2 ^ h) ^ t ≤ 7 * 2 ^ g * (2 ^ h) ^ t) :
    eFin (finE2 κ ℓ h kq t c hκ hℓ hℓ' hh hc hch ht) g A ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  have := qry_le (n := 2 ^ h) (by positivity) hq
  simp only [mul_zero, Nat.cast_zero, ENNReal.zero_div, zero_add] at this
  exact this

end Lvm6.Whir
