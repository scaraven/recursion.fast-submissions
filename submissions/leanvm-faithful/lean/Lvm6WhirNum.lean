-- New for lvm6 (WP W1, second slice). Non-vacuity of the ladder's round hypotheses at the
-- deployed numbers: PARAM's frozen row (`Lvm6Params.levels`, fold grind 10) gives every round of
-- every level `RoundOK` at `|F| = 2^128`, escape exactly `εI = 7·2^-131`, chained thresholds,
-- from the level's start agreement `Aend − k` to `Aend` (M1's `foldRoundOK_sound`, through
-- `roundOK_of_foldRoundOK`).
import Lvm6WhirLadder

/-!
# The deployed rounds (W1)

* `parP i s`: PARAM's round `s = 1 … k` of level `i` (threshold `roundA k Aend s`, CWYZ26 witness,
  numerator `foldBudget 10 · 2^128`).
* **`levelRounds_ok`**: for each of the five levels, the round hypotheses of `MidOK`/`FinOK`
  (`hpar`, `he`, `heT`, `hchain`, `ha`) hold with `t₀ = 1`, `ℓ = k`, `g = 10`, `εmax = εI`,
  `n = 2^(κ+R)`, `d = 2^κ − 1 + k`, from `a = Aend − k`, and the rounds end at `aOut = Aend`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

/-- PARAM's level `i`: `(κ, R, k, Aend, witnesses)`. -/
def lvP (i : ℕ) : ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) := Lvm6.Params.levels.getD i (0, 0, 0, 0, [])

/-- The witness of round `s` (from `1`) of level `i`. -/
def wP (i s : ℕ) : ℕ × ℕ × ℕ := (lvP i).2.2.2.2.getD (s - 1) (0, 0, 0)

/-- **PARAM's round `s` of level `i`.** -/
def parP (i s : ℕ) : RoundPar :=
  ⟨roundA (lvP i).2.2.1 (lvP i).2.2.2.1 s, (wP i s).1, (wP i s).2.1, (wP i s).2.2,
    Lvm6.Params.foldBudget 10 * 2 ^ 128⟩

/-- Every round of every level passes PARAM's check at fold grind 10. -/
def roundsCheck : Bool :=
  (List.range 5).all fun i ↦ (List.range (lvP i).2.2.1).all fun j ↦
    Lvm6.Params.foldRoundOK (lvP i).1 (lvP i).2.1 (lvP i).2.2.1 (lvP i).2.2.2.1 (j + 1)
      (wP i (j + 1)).1 (wP i (j + 1)).2.1 (wP i (j + 1)).2.2 (Lvm6.Params.foldBudget 10)

theorem roundsCheck_ok : roundsCheck = true := by decide +kernel

theorem lvP_shape : ∀ i < 5, 1 ≤ (lvP i).2.2.1 ∧ (lvP i).2.2.1 ≤ (lvP i).2.2.2.1 := by decide

theorem parP_ok {i s : ℕ} (hi : i < 5) (h1 : 1 ≤ s) (h2 : s < 1 + (lvP i).2.2.1) :
    RoundOK (2 ^ 128) (roundN (lvP i).1 (lvP i).2.1) (roundD (lvP i).1 (lvP i).2.2.1)
      (parP i s) := by
  have h := roundsCheck_ok
  unfold roundsCheck at h
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) (s - 1)
    (List.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel h1] at h'
  exact roundOK_of_foldRoundOK h'

/-- `2^m · 2^-m = 1`. -/
theorem two_pow_mul_inv_pow (m : ℕ) : (2 : ℝ≥0∞) ^ m * 2⁻¹ ^ m = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

/-- A deployed round's escape is exactly `εI = 7·2^-131`. -/
theorem eRound_parP {F : Type} [Fintype F] (hF : Fintype.card F = 2 ^ 128) (i s : ℕ) :
    eRound F 10 (parP i s) = 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  have hb : ((Lvm6.Params.foldBudget 10 * 2 ^ 128 : ℕ) : ℝ≥0∞) = 7 * 2 ^ 7 * 2 ^ 128 := by
    norm_num [Lvm6.Params.foldBudget]
  have hq : ((2 ^ 128 : ℕ) : ℝ≥0∞) = 2 ^ 128 := by norm_num
  show (2 : ℝ≥0∞)⁻¹ ^ 10 * ((Lvm6.Params.foldBudget 10 * 2 ^ 128 : ℕ) : ℝ≥0∞) /
    (Fintype.card F : ℝ≥0∞) ^ 2 = _
  rw [hF, hb, hq, div_eq_mul_inv, ← pow_mul, ENNReal.inv_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ 10 * (7 * 2 ^ 7 * 2 ^ 128) * 2⁻¹ ^ (128 * 2)
      = 7 * ((2 : ℝ≥0∞) ^ 7 * 2⁻¹ ^ 7) * (2 ^ 128 * 2⁻¹ ^ 128) * 2⁻¹ ^ 131 := by ring
    _ = 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by rw [two_pow_mul_inv_pow, two_pow_mul_inv_pow]; ring

theorem εI_lt_one : 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 < 1 := by
  calc 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 = 2⁻¹ ^ 131 * 7 := mul_comm _ _
    _ < 2⁻¹ ^ 131 * 2 ^ 131 := ENNReal.mul_lt_mul_right (by simp) (by simp)
          (by exact_mod_cast (by norm_num : (7 : ℕ) < 2 ^ 131))
    _ = 1 := by rw [mul_comm, two_pow_mul_inv_pow]

/-- The threshold after `j > 0` rounds from round `t` is round `t + j − 1`'s. -/
theorem aOut_pos (Ar : ℕ → ℕ) : ∀ (j a t : ℕ), 0 < j → aOut Ar a t j = Ar (t + j - 1)
  | 0, _, _, h => absurd h (lt_irrefl 0)
  | 1, a, t, _ => by simp [aOut]
  | j + 2, a, t, _ => by
    rw [aOut, aOut_pos Ar (j + 1) (Ar t) (t + 1) (by omega)]
    congr 1
    omega

/-- **The deployed rounds of level `i`** meet the round hypotheses of the ladder (`MidOK`,
`FinOK`) at `εI`, from the level's start agreement `Aend − k`, and end at `Aend`. -/
theorem levelRounds_ok {F : Type} [Fintype F] (hF : Fintype.card F = 2 ^ 128) {i : ℕ}
    (hi : i < 5) :
    (∀ s, 1 ≤ s → s < 1 + (lvP i).2.2.1 → RoundOK (Fintype.card F) (roundN (lvP i).1 (lvP i).2.1)
      (roundD (lvP i).1 (lvP i).2.2.1) (parP i s)) ∧
    (∀ s, 1 ≤ s → s < 1 + (lvP i).2.2.1 → eRound F 10 (parP i s) < 1) ∧
    (∀ s, 1 ≤ s → s < 1 + (lvP i).2.2.1 → eRound F 10 (parP i s) ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131) ∧
    (∀ s, 1 ≤ s → s + 1 < 1 + (lvP i).2.2.1 → (parP i s).A ≤ (parP i (s + 1)).A - 1) ∧
    (0 < (lvP i).2.2.1 → (lvP i).2.2.2.1 - (lvP i).2.2.1 ≤ (parP i 1).A - 1) ∧
    aOut (fun s ↦ (parP i s).A) ((lvP i).2.2.2.1 - (lvP i).2.2.1) 1 (lvP i).2.2.1 =
      (lvP i).2.2.2.1 := by
  obtain ⟨hk1, hkA⟩ := lvP_shape i hi
  refine ⟨fun s h1 h2 ↦ hF ▸ parP_ok hi h1 h2, fun s _ _ ↦ (eRound_parP hF i s).trans_lt εI_lt_one,
    fun s _ _ ↦ (eRound_parP hF i s).le, fun s _ h2 ↦ ?_, fun _ ↦ ?_, ?_⟩
  · simp only [parP, roundA]
    omega
  · simp only [parP, roundA]
    omega
  · rw [aOut_pos _ _ _ _ (by omega)]
    simp only [parP, roundA]
    omega

end Lvm6.Whir
