-- New for lvm2 E2-FT (stage S2GT, E2F-T): equality-mode sumcheck rounds at `E2` with grinding (the twin of
-- `LvmTypedSpecP.eqSumcheckSpec`), and the cube sums over a field (`tCubeSumF`, `eqCubeSumF`) with their families.
import LvmE2VSample
import LvmE2VWireAlg

/-!
# Equality-mode rounds at `E2`, cube sums over a field

* **`eqfG_escape`**, **`eqSumcheckGSpec`**: `sumcheckE2 g claim count (rs.map some)` (the zerocheck's rounds at
  `E2`), from doom of `claim = Fm q acc` to doom of `final = Fm q (acc ++ point)`, each challenge escaping at
  `L₀·errG g d` (`LvmTypedSpecP.eqSumcheckSpec` with `e2Sample`).
* **`tCubeSumF`**, **`eqCubeSumF`** (any field): `Σ_u g (acc ++ bits u)` and `Σ_u eq(r_{≥|acc|}, u)·g (acc ++ bits u)`
  over the coordinates left; `_full`, and the plain and equality families (`tCubeSumF_plainFamily`,
  `eqCubeSumF_eqFamily`) when the summand has degree `d` in each coordinate.
-/

set_option autoImplicit false

namespace Lvm.E2T

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Polynomial Finset
open scoped ENNReal

/-! ## Equality-mode rounds at `E2` -/

section Eq

variable {β : Type} {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-- **The escape of an equality-mode round's ground challenge**: the message against the family's next claim, a
polynomial identity of degree `d`, at `errG g d`. -/
theorem eqfG_escape {g : ℕ} (hg : g ≤ 64) {Fm : β → List E2 → E2} {r : List E2} {d : ℕ}
    (hF : EqFamilyF Fm r d) (R : β → Prop) {acc msg : List E2} (hacc : acc.length < r.length)
    (hd : msg.length - 1 ≤ d) (q : β) (hq : ¬ ((∀ x, polyEvalF msg x = Fm q (acc ++ [x])) ∧ R q)) :
    avgE (fun c ↦ indE (powOK g c ∧
      (polyEvalF msg (e2OfE c) = Fm q (acc ++ [e2OfE c]) ∧ R q))) ≤ errG g d := by
  by_cases hR : R q
  · have hne : ¬ ∀ x, polyEvalF msg x = Fm q (acc ++ [x]) := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
      (msgG_escape hg hd (hF q acc hacc).1 hne (fun _ ↦ 1) (PolyLEF.const 0 1) ⟨0, one_ne_zero⟩)
    simp only [one_mul]
    exact hc.2.1
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

variable [Finite β] {L₀ : ℕ}

/-- **Equality-mode rounds at `E2`** (`sumcheckE2 g claim count (rs.map some)`) at the point `r`, from the
challenges `acc` drawn (`rs = r.drop acc.length` left): from doom of `claim = Fm q acc` to doom of
`final = Fm q (acc ++ point)`, each ground challenge escaping at `L₀·errG g d`. Lead `T`. -/
noncomputable def eqSumcheckGSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {r : List E2} {d : ℕ} (hF : EqFamilyF Fm r d) {count : ℕ} (hc : 2 ≤ count)
    (hcd : count - 1 ≤ d) {g : ℕ} (hg : g ≤ 64) (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) :
    (rs : List E2) → (acc : List E2) → (claim : E2) → rs = r.drop acc.length →
      Spec (sumcheckE2 g claim count (rs.map some))
        (Doomed C (fun q ↦ claim = Fm q acc ∧ R q))
        (fun res h ↦ res.1.length = rs.length ∧ Doomed C (fun q ↦ res.2 = Fm q (acc ++ res.1) ∧ R q) h)
        εmax T T
  | [], acc, claim, _ =>
    (Spec.ret (Post := fun (res : List E2 × E2) h ↦ res.1.length = 0 ∧
        Doomed C (fun q ↦ res.2 = Fm q (acc ++ res.1) ∧ R q) h) ([], claim)).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | rk :: rs, acc, claim, hrs => by
    have hlt : acc.length < r.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hrs
      exact List.cons_ne_nil _ _ hrs
    have hrk : r[acc.length] = rk := by
      have := congrArg List.head? hrs
      rw [List.head?_drop, List.getElem?_eq_getElem hlt] at this
      simpa using this.symm
    refine ((roundSpecE2 (T := 0) hst _ zero_le count hc claim (some rk)).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = count ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = count
    · refine ((doomE2SampleSpec (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEvalF msg x = Fm q (acc ++ [x])) ∧ R q)
        (fun y q ↦ polyEvalF msg y = Fm q (acc ++ [y]) ∧ R q) (errG g d)
        (fun q hq ↦ eqfG_escape hg hF R hlt (by omega) q hq) he).mono
          (fun h (hh : msg.length = count ∧
              RoundSplitF (some rk) claim (polyEvalF msg 0) (polyEvalF msg 1) ∧
              Doomed C (fun q ↦ claim = Fm q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplitF, hall, hall, ← hrk] at hs
              rw [← hs, (hF q acc hlt).2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      refine (eqSumcheckGSpec hst hcard R hF hc hcd hg he rs (acc ++ [c]) (polyEvalF msg c)
        ?_).bind' fun res ↦ ?_
      · rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
        rfl
      · exact (Spec.ret (c :: res.1, res.2)).mono
          (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Eq

/-! ## Cube sums over a field -/

section Field

variable {F : Type} [Field F]

/-- `Σ_u g (acc ++ bits u)` over the cube of the `n − |acc|` coordinates left. -/
def tCubeSumF (n : ℕ) (g : List F → F) (acc : List F) : F :=
  ∑ u ∈ range (2 ^ (n - acc.length)), g (acc ++ bitsF u (n - acc.length))

/-- `Σ_u eq(r_{≥|acc|}, u)·g (acc ++ bits u)` over the cube of the `n − |acc|` coordinates left. -/
def eqCubeSumF (r : List F) (n : ℕ) (g : List F → F) (acc : List F) : F :=
  ∑ u ∈ range (2 ^ (n - acc.length)), eqAtF (r.drop acc.length) u * g (acc ++ bitsF u (n - acc.length))

theorem tCubeSumF_nil (n : ℕ) (g : List F → F) :
    tCubeSumF n g [] = ∑ u ∈ range (2 ^ n), g (bitsF u n) := by
  simp [tCubeSumF]

theorem tCubeSumF_full (n : ℕ) (g : List F → F) {acc : List F} (h : acc.length = n) :
    tCubeSumF n g acc = g acc := by
  simp [tCubeSumF, h, bitsF]

theorem eqCubeSumF_nil (r : List F) (n : ℕ) (g : List F → F) :
    eqCubeSumF r n g [] = ∑ u ∈ range (2 ^ n), eqAtF r u * g (bitsF u n) := by
  simp [eqCubeSumF]

theorem eqCubeSumF_full (r : List F) (n : ℕ) (g : List F → F) {acc : List F} (h : acc.length = n)
    (hr : r.length = n) : eqCubeSumF r n g acc = g acc := by
  simp only [eqCubeSumF, h, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton, bitsF,
    List.append_nil]
  rw [List.drop_eq_nil_of_le (by (clear * - F r n acc hr; omega)), eqAtF_nil, one_mul]

/-- **A cube sum is a plain family** when its summand has degree `d` in each coordinate. -/
theorem tCubeSumF_plainFamily {β : Type} (n d : ℕ) (G : β → List F → F)
    (hG : ∀ q pre post, PolyLEF d fun x ↦ G q (pre ++ x :: post)) :
    PlainFamilyF (fun q acc ↦ tCubeSumF n (G q) acc) d n := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by (clear * - n F acc hacc; omega)
  refine ⟨?_, ?_⟩
  · refine PolyLEF.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      G q (acc ++ x :: bitsF u (n - (acc.length + 1)))) ?_ fun x ↦ ?_
    · exact PolyLEF.sum _ fun u _ ↦ hG q acc _
    · simp only [tCubeSumF, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
  · simp only [tCubeSumF, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [bitsF_two_mul, bitsF_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

/-- **An equality cube sum is an equality family** at `r` (`|r| = n`) when its summand has degree `d` in each
coordinate. -/
theorem eqCubeSumF_eqFamily {β : Type} (r : List F) (n d : ℕ) (hr : r.length = n) (G : β → List F → F)
    (hG : ∀ q pre post, PolyLEF d fun x ↦ G q (pre ++ x :: post)) :
    EqFamilyF (fun q acc ↦ eqCubeSumF r n (G q) acc) r d := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by (clear * - n F acc r hr hacc; omega)
  have hdrop : r.drop acc.length = r[acc.length] :: r.drop (acc.length + 1) :=
    List.drop_eq_getElem_cons hacc
  refine ⟨?_, ?_⟩
  · refine PolyLEF.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      eqAtF (r.drop (acc.length + 1)) u * G q (acc ++ x :: bitsF u (n - (acc.length + 1)))) ?_ fun x ↦ ?_
    · exact PolyLEF.sum _ fun u _ ↦ PolyLEF.const_mul (hG q acc _) _
    · simp only [eqCubeSumF, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
  · simp only [eqCubeSumF, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succW, hdrop, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [eqAtF_succ, eqAtF_succ, bitsF_two_mul, bitsF_two_mul_add_one]
    have h1 : 2 * u % 2 = 0 := by (clear * - u F r n acc; omega)
    have h2 : (2 * u + 1) % 2 = 1 := by (clear * - u F r n acc h1; omega)
    have h3 : 2 * u / 2 = u := by (clear * - u F r n acc h1; omega)
    have h4 : (2 * u + 1) / 2 = u := by (clear * - u F r n acc h1 h2; omega)
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false, List.append_assoc,
      List.singleton_append]
    ring

end Field

end Lvm.E2T
