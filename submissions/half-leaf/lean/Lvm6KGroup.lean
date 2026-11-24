-- New for lvm6 K1: `gPoint g n` (`G(g) D(n)`) through F1's canonical group rule (`Lvm6FSGroup`: `grp6`,
-- `doomGrp6`): the program equation and the per-draw union bound for F1's joint escape `grpEsc`.
import Lvm6KProg
import Lvm6FSGroup

/-!
# The group rule `G(g) D(n)` for K1

F1's `doomGrp6` is the doom rule of a ground group (`grp6 g n`: nonce, ground draw with its proof of
work, `n` further draws), priced by the joint escape `grpEsc g n P`.

* `gPoint_eq_grp6`: K1's `gPoint g n` is F1's `grp6 g n` (`dDraws` is F1's `drawsE2`; `grp6_eq`);
* `grpEsc_union`: when each draw makes a candidate not alive alive with probability at most `e`
  (season 1's per-coordinate form at `g = 0`), the group's joint escape is at most `2^-g·(n+1)·e`;
* **`gPointSpec`**: `doomGrp6` for `gPoint` with that bound, at one candidate.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Verifier
open Lvm.E2V
open Finset
open scoped ENNReal

theorem dDraws_eq : ∀ n, dDraws n = drawsE2 n
  | 0 => rfl
  | n + 1 => by
    show (dDraw >>= fun x ↦ dDraws n >>= fun xs ↦ pure (x :: xs)) = _
    rw [dDraws_eq n]; rfl

/-- **K1's `gPoint` is F1's group** `grp6`. -/
theorem gPoint_eq_grp6 (g n : ℕ) : gPoint g n = grp6 g n := by
  rw [grp6_eq, gPoint]
  simp only [dDraws_eq]

/-! ## Escapes -/

theorem powOK_zero (c : E) : powOK 0 c :=
  (powOK_iff_lane2 (g := 0) (by norm_num) c).2 (kToNat_lt _)

theorem avgE_add_const (f : E → ℝ≥0∞) (k : ℝ≥0∞) : avgE (fun c ↦ f c + k) = avgE f + k := by
  unfold avgE
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- The draw with the proof of work: the escape `e` stated at `g = 0` is discounted by `2^-g`. -/
theorem avgE_powOK_disc {g : ℕ} (hg : g ≤ 64) (P : E2 → Prop) {e : ℝ≥0∞}
    (h : avgE (fun c ↦ indE (powOK 0 c ∧ P (e2OfE c))) ≤ e) :
    avgE (fun c ↦ indE (powOK g c ∧ P (e2OfE c))) ≤ (2 : ℝ≥0∞)⁻¹ ^ g * e := by
  classical
  rw [avgE_powOK_prod hg]
  rw [avgE_powOK_prod (by norm_num), pow_zero, one_mul] at h
  gcongr

theorem avgE_powOK (g : ℕ) (hg : g ≤ 64) : avgE (fun c ↦ indE (powOK g c)) = (2 : ℝ≥0∞)⁻¹ ^ g := by
  classical
  have h := avgE_powOK_prod hg (fun _ : E2 ↦ True)
  simp only [and_true] at h
  rw [h, Finset.filter_true_of_mem (fun _ _ ↦ trivial), Finset.card_univ, card_E2, Nat.cast_pow,
    Nat.cast_ofNat, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

/-- **Further draws** (the union bound): with `pre` drawn, `n` more draws make a candidate alive with
probability at most `n·e` beyond its current indicator. -/
theorem avgN_union (A : List E2 → Prop) (e : ℝ≥0∞)
    (hesc : ∀ acc, ¬ A acc → avgE (fun c ↦ indE (powOK 0 c ∧ A (acc ++ [e2OfE c]))) ≤ e) :
    ∀ (n : ℕ) (pre : List E2),
      avgN n (fun cs ↦ indE (A (pre ++ cs.map e2OfE))) ≤ indE (A pre) + n * e
  | 0, pre => by simp [avgN]
  | n + 1, pre => by
    simp only [avgN]
    calc avgE (fun c ↦ avgN n fun cs ↦ indE (A (pre ++ (c :: cs).map e2OfE)))
        ≤ avgE (fun c ↦ indE (A (pre ++ [e2OfE c])) + n * e) := avgE_mono fun c ↦ by
          have := avgN_union A e hesc n (pre ++ [e2OfE c])
          simpa only [List.map_cons, List.append_assoc, List.singleton_append] using this
      _ = avgE (fun c ↦ indE (A (pre ++ [e2OfE c]))) + n * e := avgE_add_const _ _
      _ ≤ indE (A pre) + ((n + 1 : ℕ) : ℝ≥0∞) * e := by
          rw [Nat.cast_succ, add_mul, one_mul, add_comm (↑n * e) e, ← add_assoc]
          gcongr
          by_cases ha : A pre
          · simp only [indE, ha, if_true]
            exact (avgE_indE_le_one _).trans le_self_add
          · simp only [indE, ha, if_false, zero_add]
            exact (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨powOK_zero c, h⟩).trans (hesc pre ha)

/-- **The group's joint escape from per-draw escapes**: `≤ 2^-g·(n+1)·e` for a candidate not alive. -/
theorem grpEsc_union {g : ℕ} (hg : g ≤ 64) (n : ℕ) (A : List E2 → Prop) (e : ℝ≥0∞)
    (hesc : ∀ acc, ¬ A acc → avgE (fun c ↦ indE (powOK 0 c ∧ A (acc ++ [e2OfE c]))) ≤ e)
    (h0 : ¬ A []) : grpEsc g n A ≤ (2 : ℝ≥0∞)⁻¹ ^ g * ((n + 1 : ℕ) * e) := by
  classical
  unfold grpEsc
  calc avgE (fun c ↦ if powOK g c then avgN n (fun cs ↦ indE (A (e2OfE c :: cs.map e2OfE))) else 0)
      ≤ avgE (fun c ↦ indE (powOK g c ∧ A ([] ++ [e2OfE c])) + n * e * indE (powOK g c)) :=
        avgE_mono fun c ↦ by
          split_ifs with hp
          · have := avgN_union A e hesc n [e2OfE c]
            simp only [List.singleton_append] at this
            simp only [indE, hp, true_and, if_true, mul_one, List.nil_append]
            exact this
          · exact zero_le
    _ = avgE (fun c ↦ indE (powOK g c ∧ A ([] ++ [e2OfE c]))) +
          n * e * avgE (fun c ↦ indE (powOK g c)) := by
        unfold avgE
        rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum (s := univ) (a := (n : ℝ≥0∞) * e)]
        ring
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ g * e + n * e * (2 : ℝ≥0∞)⁻¹ ^ g := by
        rw [avgE_powOK g hg]
        gcongr
        exact avgE_powOK_disc hg (fun y ↦ A ([] ++ [y])) (hesc [] h0)
    _ = (2 : ℝ≥0∞)⁻¹ ^ g * ((n + 1 : ℕ) * e) := by push_cast; ring

variable {β : Type} {C : List Ev → Set β} [Finite β]

/-- **The group rule `G(g) D(n)` for `gPoint`** (F1's `doomGrp6`): from doom of `A []` to doom of
`A pt` at the `n + 1` coordinates `pt`; lead `0`; the group `2^-g·(n+1)·e + T ≤ εmax` at one
candidate. -/
noncomputable def gPointSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) {g : ℕ} (hg : g ≤ 64)
    (n : ℕ) (A : List E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ acc q, ¬ A acc q → avgE (fun c ↦ indE (powOK 0 c ∧ A (acc ++ [e2OfE c]) q)) ≤ e)
    {εmax T : ℝ≥0∞} (hε : εmax < 1)
    (he : (2 : ℝ≥0∞)⁻¹ ^ g * ((n + 1 : ℕ) * e) + T ≤ εmax) :
    Spec (gPoint g n) (Doomed C (A [])) (fun l h ↦ l.length = n + 1 ∧ Doomed C (A l) h) εmax 0 T :=
  Spec.congr (gPoint_eq_grp6 g n).symm <|
    doomGrp6 hst hcard (A []) A ((2 : ℝ≥0∞)⁻¹ ^ g * ((n + 1 : ℕ) * e))
      (fun q hq ↦ grpEsc_union hg n (fun l ↦ A l q) e (fun acc h ↦ hesc acc q h) hq) hε
      (by rw [Nat.cast_one, one_mul]; exact he)

end Lvm6.K
