-- New for lvm6 (WP W1). The deployed challenge field `E2` with F1's group rule (`Lvm6FSGroup`:
-- `grp6`, `doomGrp6`, `doomSep6`, `grpEsc_eq_card`) as a `ChalIface`: the group is `grp6 g k`
-- (nonce, ground draw with `require (powOK g c₀)`, `k` draws; values `e2OfE`, lanes 0–1), the bind
-- is season 1's `e2Sep`. The invariant of the commitments becomes doom over a two-point candidate
-- map (`cmap`), one per start commitment list (`Spec.exPre`). The count is season 1's grind fact
-- `LvmE2Grind.card_powOK_prod` (`pwE2`, through `pwCount_le`).
import Lvm6WhirGround
import LvmE2Grind
import Lvm6FSGroup

/-!
# `E2` as the challenge field (`ChalIface E2`)

* `pwE2`: answers `c : E` with value `e2OfE c`, work `powOK g c`, `2^64` answers per value,
  `gmax = 64`, `card_pw` from `card_powOK_prod`.
* `grpEsc_le_grpE`: F1's joint escape of a group is at most `grpE E2 g k P = 2^-g |P| / |E2|^(k+1)`.
* `cmap cs₀`: the candidate `true` while the commitments are `cs₀`, else `false` (stable, one point).
* **`chalE2`**: `grp := grp6`, `sep := e2Sep`; `grpSpec` from `doomGrp6`, `sepSpec` from `doomSep6`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front Lvm.E2V Finset
open scoped ENNReal

theorem powOK_zero (c : E) : Verifier.powOK 0 c := by
  unfold Verifier.powOK
  rw [← eNatEquiv_val]
  exact lt_of_lt_of_le (eNatEquiv c).isLt (by norm_num)

/-- **Answers of `E` with their `E2` values and proof of work.** -/
noncomputable def pwE2 : PwIface E2 where
  dec := e2OfE
  pw := Verifier.powOK
  pwDec := fun g c ↦ Verifier.instDecidablePowOK g c
  m := 2 ^ 64
  card_E := by rw [card_E, card_E2, ← pow_add]
  fiber := fun y ↦ by
    have h := card_powOK_prod (g := 0) (by norm_num) (fun x ↦ x = y)
    rw [show (univ.filter fun x : E2 ↦ x = y) = {y} from by ext; simp, Finset.card_singleton,
      one_mul, Nat.sub_zero] at h
    rw [← h]
    exact congrArg Finset.card (Finset.filter_congr fun c _ ↦ by simp [powOK_zero c])
  gmax := 64
  card_pw := fun g hg P ↦ by
    have h := card_powOK_prod hg (fun x ↦ x ∈ P)
    rw [show (univ.filter fun x : E2 ↦ x ∈ P) = P from by ext; simp] at h
    have h2 : (2 : ℝ≥0∞) ^ (64 - g) = (2 : ℝ≥0∞)⁻¹ ^ g * 2 ^ 64 := by
      rw [show (2 : ℝ≥0∞) ^ 64 = 2 ^ g * 2 ^ (64 - g) by rw [← pow_add, Nat.add_sub_cancel' hg],
        ← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]
    calc _ = ((P.card * 2 ^ (64 - g) : ℕ) : ℝ≥0∞) := by
          rw [← h]
      _ = (2 : ℝ≥0∞)⁻¹ ^ g * (((2 ^ 64 : ℕ) : ℝ≥0∞) * P.card) := by
          push_cast; rw [h2]; ring
      _ ≤ _ := le_rfl

theorem gv_ofFn {k : ℕ} (f : Fin k → E2) : gv (List.ofFn f) = f := by
  funext i
  simp [gv, List.getD_eq_getElem?_getD]

open Classical in
/-- **F1's joint escape is the count `grpE`**: `grpEsc g k (P ∘ gv) ≤ 2^-g |P| / |E2|^(k+1)`. -/
theorem grpEsc_le_grpE {g : ℕ} (hg : g ≤ 64) (k : ℕ) (P : (Fin (k + 1) → E2) → Prop) :
    grpEsc g k (fun ys ↦ P (gv ys)) ≤ grpE E2 g k P := by
  rw [grpEsc_eq_card, ENNReal.inv_pow, mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card fun w hw ↦ ?_))
    zero_le') (pwCount_le pwE2 hg k (univ.filter P))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, gv_ofFn] at hw ⊢
  exact hw

/-! ## The two-point candidate map -/

theorem commits_app (h l : List Ev) : commits (h ++ l) = commits h ++ commits l := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

open Classical in
/-- The candidate `true` while the commitments are `cs₀`, else `false`. -/
noncomputable def cmap (cs₀ : List (ℕ × ℕ × Word)) (h : List Ev) : Set Bool :=
  if commits h = cs₀ then {true} else {false}

theorem cmap_stable (cs₀ : List (ℕ × ℕ × Word)) : Stable (cmap cs₀) := fun h₀ l hl ↦ by
  unfold cmap
  rw [commits_app, hl, List.append_nil]

theorem cmap_card (cs₀ : List (ℕ × ℕ × Word)) (h : List Ev) : (cmap cs₀ h).ncard ≤ 1 := by
  unfold cmap
  split_ifs <;> simp

/-- The predicate of `cmap`'s candidates: `P` at `true`, nothing at `false`. -/
def onTrue (P : Prop) : Bool → Prop
  | true => P
  | false => True

theorem doomed_onTrue {cs₀ : List (ℕ × ℕ × Word)} {P : Prop} {h : List Ev} :
    Doomed (cmap cs₀) (onTrue P) h ↔ commits h = cs₀ ∧ ¬ P := by
  unfold Doomed cmap
  by_cases hc : commits h = cs₀ <;> simp [hc, onTrue]

/-! ## The deployed challenge field -/

/-- **The deployed challenge field**: F1's group `grp6` and bind `e2Sep` with their doom rules. -/
noncomputable def chalE2 : ChalIface E2 where
  rd := e2OfE
  grp := grp6
  sep := e2Sep
  gmax := 64
  grpSpec g k hg Inv Good e he hesc :=
    (Spec.exPre (Pre := fun cs₀ h ↦ Doomed (cmap cs₀) (onTrue (¬ Inv cs₀)) h) fun cs₀ ↦
      (doomGrp6 (εmax := e) (T := 0) (cmap_stable cs₀) (cmap_card cs₀) (onTrue (¬ Inv cs₀))
        (fun ys ↦ onTrue (¬ Good (gv ys) cs₀)) e (fun q hq ↦ by
          cases q with
          | false => exact absurd trivial hq
          | true =>
            exact (grpEsc_le_grpE hg k (fun u ↦ ¬ Good u cs₀)).trans
              (hesc cs₀ (not_not.mp hq))) he (by simp)).mono (fun _ h ↦ h)
        (fun ys h hp ↦ by
          obtain ⟨hc, hG⟩ := doomed_onTrue.mp hp.2
          rw [hc]
          exact not_not.mp hG) le_rfl le_rfl le_rfl).mono
      (fun h hI ↦ ⟨commits h, doomed_onTrue.mpr ⟨rfl, not_not.mpr hI⟩⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl
  sepSpec Inv εmax T :=
    (Spec.exPre (Pre := fun cs₀ h ↦ Doomed (cmap cs₀) (onTrue (¬ Inv cs₀)) h) fun cs₀ ↦
      (doomSep6 (εmax := εmax) (T := T) (cmap_stable cs₀) (cmap_card cs₀)
        (onTrue (¬ Inv cs₀))).mono (fun _ h ↦ h)
        (fun _ h hp ↦ by
          obtain ⟨hc, hI⟩ := doomed_onTrue.mp hp
          rw [hc]
          exact not_not.mp hI) le_rfl le_rfl le_rfl).mono
      (fun h hI ↦ ⟨commits h, doomed_onTrue.mpr ⟨rfl, not_not.mpr hI⟩⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl

end Lvm6.Whir
