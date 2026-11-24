-- New for lvm6 (WP W1, second slice). Non-vacuity of the ladder's round hypotheses at the
-- deployed numbers: PARAM's frozen row (fold grind 10) gives every round of every level `RoundOK` at
-- `|F| = 2^128`, escape exactly `εI = 7·2^-131`, chained thresholds, from the level's start agreement
-- `Aend − k` to `Aend` (M1's `foldRoundOK_sound`, through `roundOK_of_foldRoundOK`).
-- PORT17 W1: generic over PARAM's level list (`lvOf pl`, `parOf pl`, `roundsCheckOf pl`); the deployed
-- row is `Lvm6.Params17.levels` (`M = 24`), `P18`'s row (`Lvm6.Params.levels`) is a corollary.
import Lvm6WhirLadder
import Lvm6Params17

/-!
# The deployed rounds (W1)

* `PLv`: PARAM's level list `(κ, R, k, Aend, witnesses)`; `lvOf pl i`, `wOf pl i s`, `parOf pl i s`:
  PARAM's round `s = 1 … k` of level `i` (threshold `roundA k Aend s`, CWYZ26 witness, numerator
  `foldBudget 10 · 2^128`).
* `roundsCheckOf pl`: every round of every level passes PARAM's check at fold grind 10, and
  `1 ≤ k ≤ Aend` per level.
* **`levelRounds_okOf`**: for each level of a checked list, the round hypotheses of `MidOK`/`FinOK`
  (`hpar`, `he`, `heT`, `hchain`, `ha`) hold with `t₀ = 1`, `ℓ = k`, `g = 10`, `εmax = εI`,
  `n = 2^(κ+R)`, `d = 2^κ − 1 + k`, from `a = Aend − k`, and the rounds end at `aOut = Aend`.
* The deployed row: `lvP`, `parP` (`Lvm6.Params17.levels`), `roundsCheck_ok`, `levelRounds_ok`; `P18`'s:
  `roundsCheck_okP18` (in `Lvm6P18Park` since INT11).
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

/-- PARAM's level list: `(κ, R, k, Aend, witnesses)` per level. -/
abbrev PLv : Type := List (ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ))

/-- PARAM's level `i`: `(κ, R, k, Aend, witnesses)`. -/
def lvOf (pl : PLv) (i : ℕ) : ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) := pl.getD i (0, 0, 0, 0, [])

/-- The witness of round `s` (from `1`) of level `i`. -/
def wOf (pl : PLv) (i s : ℕ) : ℕ × ℕ × ℕ := (lvOf pl i).2.2.2.2.getD (s - 1) (0, 0, 0)

/-- **PARAM's round `s` of level `i`.** -/
def parOf (pl : PLv) (i s : ℕ) : RoundPar :=
  ⟨roundA (lvOf pl i).2.2.1 (lvOf pl i).2.2.2.1 s, (wOf pl i s).1, (wOf pl i s).2.1, (wOf pl i s).2.2,
    Lvm6.Params.foldBudget 10 * 2 ^ 128⟩

/-- Every round of every level passes PARAM's check at fold grind 10, and each level has
`1 ≤ k ≤ Aend`. -/
def roundsCheckOf (pl : PLv) : Bool :=
  (List.range pl.length).all fun i ↦ decide (1 ≤ (lvOf pl i).2.2.1) &&
    decide ((lvOf pl i).2.2.1 ≤ (lvOf pl i).2.2.2.1) &&
    (List.range (lvOf pl i).2.2.1).all fun j ↦
      Lvm6.Params.foldRoundOK (lvOf pl i).1 (lvOf pl i).2.1 (lvOf pl i).2.2.1 (lvOf pl i).2.2.2.1 (j + 1)
        (wOf pl i (j + 1)).1 (wOf pl i (j + 1)).2.1 (wOf pl i (j + 1)).2.2 (Lvm6.Params.foldBudget 10)

theorem lvOf_shape {pl : PLv} (hpl : roundsCheckOf pl = true) {i : ℕ} (hi : i < pl.length) :
    1 ≤ (lvOf pl i).2.2.1 ∧ (lvOf pl i).2.2.1 ≤ (lvOf pl i).2.2.2.1 := by
  have h := List.all_eq_true.mp hpl i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem parOf_ok {pl : PLv} (hpl : roundsCheckOf pl = true) {i s : ℕ} (hi : i < pl.length)
    (h1 : 1 ≤ s) (h2 : s < 1 + (lvOf pl i).2.2.1) :
    RoundOK (2 ^ 128) (roundN (lvOf pl i).1 (lvOf pl i).2.1) (roundD (lvOf pl i).1 (lvOf pl i).2.2.1)
      (parOf pl i s) := by
  have h := List.all_eq_true.mp hpl i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at h
  have h' := List.all_eq_true.mp h.2 (s - 1) (List.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel h1] at h'
  exact roundOK_of_foldRoundOK h'

/-- `2^m · 2^-m = 1`. -/
theorem two_pow_mul_inv_pow (m : ℕ) : (2 : ℝ≥0∞) ^ m * 2⁻¹ ^ m = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

/-- A deployed round's escape is exactly `εI = 7·2^-131`. -/
theorem eRound_parOf {F : Type} [Fintype F] (hF : Fintype.card F = 2 ^ 128) (pl : PLv) (i s : ℕ) :
    eRound F 10 (parOf pl i s) = 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
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

/-- **The rounds of level `i` of a checked PARAM list** meet the round hypotheses of the ladder
(`MidOK`, `FinOK`) at `εI`, from the level's start agreement `Aend − k`, and end at `Aend`. -/
theorem levelRounds_okOf {F : Type} [Fintype F] (hF : Fintype.card F = 2 ^ 128) {pl : PLv}
    (hpl : roundsCheckOf pl = true) {i : ℕ} (hi : i < pl.length) :
    (∀ s, 1 ≤ s → s < 1 + (lvOf pl i).2.2.1 → RoundOK (Fintype.card F)
      (roundN (lvOf pl i).1 (lvOf pl i).2.1) (roundD (lvOf pl i).1 (lvOf pl i).2.2.1) (parOf pl i s)) ∧
    (∀ s, 1 ≤ s → s < 1 + (lvOf pl i).2.2.1 → eRound F 10 (parOf pl i s) < 1) ∧
    (∀ s, 1 ≤ s → s < 1 + (lvOf pl i).2.2.1 → eRound F 10 (parOf pl i s) ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131) ∧
    (∀ s, 1 ≤ s → s + 1 < 1 + (lvOf pl i).2.2.1 → (parOf pl i s).A ≤ (parOf pl i (s + 1)).A - 1) ∧
    (0 < (lvOf pl i).2.2.1 → (lvOf pl i).2.2.2.1 - (lvOf pl i).2.2.1 ≤ (parOf pl i 1).A - 1) ∧
    aOut (fun s ↦ (parOf pl i s).A) ((lvOf pl i).2.2.2.1 - (lvOf pl i).2.2.1) 1 (lvOf pl i).2.2.1 =
      (lvOf pl i).2.2.2.1 := by
  obtain ⟨hk1, hkA⟩ := lvOf_shape hpl hi
  refine ⟨fun s h1 h2 ↦ hF ▸ parOf_ok hpl hi h1 h2,
    fun s _ _ ↦ (eRound_parOf hF pl i s).trans_lt εI_lt_one, fun s _ _ ↦ (eRound_parOf hF pl i s).le,
    fun s _ h2 ↦ ?_, fun _ ↦ ?_, ?_⟩
  · simp only [parOf, roundA]
    omega
  · simp only [parOf, roundA]
    omega
  · rw [aOut_pos _ _ _ _ (by omega)]
    simp only [parOf, roundA]
    omega

/-! ## The deployed row (`M = 24`) and `P18`'s -/

/-- PARAM's level `i` at the deployed shape (`Lvm6.Params17.levels`, `M = 24`). -/
abbrev lvP (i : ℕ) : ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) := lvOf Lvm6.Params17.levels i

/-- **PARAM's round `s` of level `i`** at the deployed shape. -/
abbrev parP (i s : ℕ) : RoundPar := parOf Lvm6.Params17.levels i s

theorem roundsCheck_ok : roundsCheckOf Lvm6.Params17.levels = true := by decide +kernel

theorem params17_length : Lvm6.Params17.levels.length = 5 := rfl

/-- **The deployed rounds of level `i`** (`levelRounds_okOf` at `Lvm6.Params17.levels`). -/
theorem levelRounds_ok {F : Type} [Fintype F] (hF : Fintype.card F = 2 ^ 128) {i : ℕ} (hi : i < 5) :
    (∀ s, 1 ≤ s → s < 1 + (lvP i).2.2.1 → RoundOK (Fintype.card F) (roundN (lvP i).1 (lvP i).2.1)
      (roundD (lvP i).1 (lvP i).2.2.1) (parP i s)) ∧
    (∀ s, 1 ≤ s → s < 1 + (lvP i).2.2.1 → eRound F 10 (parP i s) < 1) ∧
    (∀ s, 1 ≤ s → s < 1 + (lvP i).2.2.1 → eRound F 10 (parP i s) ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131) ∧
    (∀ s, 1 ≤ s → s + 1 < 1 + (lvP i).2.2.1 → (parP i s).A ≤ (parP i (s + 1)).A - 1) ∧
    (0 < (lvP i).2.2.1 → (lvP i).2.2.2.1 - (lvP i).2.2.1 ≤ (parP i 1).A - 1) ∧
    aOut (fun s ↦ (parP i s).A) ((lvP i).2.2.2.1 - (lvP i).2.2.1) 1 (lvP i).2.2.1 =
      (lvP i).2.2.2.1 :=
  levelRounds_okOf hF roundsCheck_ok (by rw [params17_length]; exact hi)

end Lvm6.Whir
