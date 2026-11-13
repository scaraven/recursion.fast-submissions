-- New for lvm2 (roll 8 = B1, wave L, L-B): the generic pieces of `typedSpecR` (LvmTypedSpec): equality-mode
-- `sumcheck` rounds over doomed candidates (`eqSumcheckSpec`, after WP-2's `sumcheckSpec`/`packSpec` of
-- `LvmKeccakRounds`), the cube-sum families of the zerocheck, the wiring and the relayout, the quadratic escape of
-- `γ`, and the matrices' sums over their entries.
import LvmTypedAcc
import LvmKeccakLayerSum

/-!
# The typed phases' generic specifications

* `roundError_eq`: `roundError L₀ d = L₀ · errE d` (the two forms of a round's escape).
* **`eqSumcheckSpec`**: `sumcheck claim count (r.map some)` (equality mode, the zerocheck's `gkrStep` form) from
  doom of `claim = F q acc` to doom of `final = F q (acc ++ point)` for an `EqFamily` at `r`; each challenge
  escapes at `L₀ · d/|E|` (WP-2's `sumcheckSpec` for the plain rounds, `packSpec` for the scaled ones).
* `tCubeSum n g acc = Σ_u g (acc ++ bits u)` (a plain family when `g` has degree `d` in each coordinate) and
  `eqCubeSum r n g acc = Σ_u eq(r_{≥|acc|}, u) · g (acc ++ bits u)` (an equality family at `r`).
* `quadT_escape`: `a + γ b + γ² c` against a different triple's agrees at `2/|E|` of the `γ`.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

/-! ## Errors -/

/-- **A round's escape in both forms.** -/
theorem roundError_eq (L₀ d : ℕ) : roundError L₀ d = L₀ * errE d := by
  unfold roundError errE
  rw [Nat.card_eq_fintype_card]
  have h0 : (Fintype.card E : ℝ≥0) ≠ 0 := by
    rw [card_E]; positivity
  rw [ENNReal.coe_div h0, ENNReal.coe_natCast, ENNReal.coe_natCast, div_eq_mul_inv]

/-! ## Equality-mode `sumcheck` rounds -/

section Eq

variable {β : Type} {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-- The escape of an equality-mode `sumcheck` round's challenge: the message against the family's next claim, a
polynomial identity of degree `d`. -/
theorem eqf_escape {F : β → List E → E} {r : List E} {d : ℕ} (hF : EqFamily F r d) (R : β → Prop)
    {acc msg : List E} (hacc : acc.length < r.length) (hd : msg.length - 1 ≤ d) (q : β)
    (hq : ¬ ((∀ x, polyEval msg x = F q (acc ++ [x])) ∧ R q)) :
    avgE (fun c ↦ indE (polyEval msg c = F q (acc ++ [c]) ∧ R q)) ≤ errE d := by
  by_cases hR : R q
  · have hne : ¬ ∀ x, polyEval msg x = F q (acc ++ [x]) := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
      (msg_escape hd (hF q acc hacc).1 hne (fun _ ↦ 1) (PolyLE.const 0 1) ⟨0, one_ne_zero⟩)
    simp only [one_mul]
    exact hc.1
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

variable [Finite β] {L₀ : ℕ}

/-- **Equality-mode `sumcheck` rounds** (`sumcheck claim count (rs.map some)`, the zerocheck's) at the point `r`,
from the challenges `acc` drawn (`rs = r.drop acc.length` left): from doom of `claim = F q acc` to doom of
`final = F q (acc ++ point)`, each challenge escaping at `L₀ · d/|E|`. Lead `T` (`0` when a round is left). -/
noncomputable def eqSumcheckSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) {F : β → List E → E} {r : List E} {d : ℕ} (hF : EqFamily F r d) {count : ℕ}
    (hc : 2 ≤ count) (hcd : count - 1 ≤ d) (hT : T ≤ εmax)
    (he : (L₀ : ℝ≥0∞) * errE d + T ≤ εmax) :
    (rs : List E) → (acc : List E) → (claim : E) → rs = r.drop acc.length →
      Spec (sumcheck claim count (rs.map some))
        (Doomed C (fun q ↦ claim = F q acc ∧ R q))
        (fun res h ↦ res.1.length = rs.length ∧ Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ R q) h)
        εmax T T
  | [], acc, claim, _ =>
    (Spec.ret (Post := fun (res : List E × E) h ↦ res.1.length = 0 ∧
        Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ R q) h) ([], claim)).mono
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
    refine ((roundSpec (T := (L₀ : ℝ≥0∞) * errE d + T) hst _ he count hc claim (some rk)).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = count ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = count
    · refine ((doomSample (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEval msg x = F q (acc ++ [x])) ∧ R q)
        (fun c q ↦ polyEval msg c = F q (acc ++ [c]) ∧ R q) (errE d)
        (fun q hq ↦ eqf_escape hF R hlt (by omega) q hq)).mono
          (fun h (hh : msg.length = count ∧
              RoundSplit (some rk) claim (polyEval msg 0) (polyEval msg 1) ∧
              Doomed C (fun q ↦ claim = F q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplit, hall, hall, ← hrk] at hs
              rw [← hs, (hF q acc hlt).2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      · refine (eqSumcheckSpec hst hcard R hF hc hcd hT he rs (acc ++ [c]) (polyEval msg c)
          ?_).bind' fun res ↦ ?_
        · rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
          rfl
        · exact (Spec.ret (c :: res.1, res.2)).mono
            (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Eq

/-! ## Cube sums -/

/-- `Σ_u g (acc ++ bits u)` over the cube of the `n − |acc|` coordinates left. -/
noncomputable def tCubeSum (n : ℕ) (g : List E → E) (acc : List E) : E :=
  ∑ u ∈ range (2 ^ (n - acc.length)), g (acc ++ bitsE u (n - acc.length))

/-- `Σ_u eq(r_{≥|acc|}, u) · g (acc ++ bits u)` over the cube of the `n − |acc|` coordinates left. -/
noncomputable def eqCubeSum (r : List E) (n : ℕ) (g : List E → E) (acc : List E) : E :=
  ∑ u ∈ range (2 ^ (n - acc.length)), eqAt (r.drop acc.length) u * g (acc ++ bitsE u (n - acc.length))

theorem tCubeSum_nil (n : ℕ) (g : List E → E) :
    tCubeSum n g [] = ∑ u ∈ range (2 ^ n), g (bitsE u n) := by
  simp [tCubeSum]

theorem tCubeSum_full (n : ℕ) (g : List E → E) {acc : List E} (h : acc.length = n) :
    tCubeSum n g acc = g acc := by
  simp [tCubeSum, h, bitsE]

theorem eqCubeSum_nil (r : List E) (n : ℕ) (g : List E → E) :
    eqCubeSum r n g [] = ∑ u ∈ range (2 ^ n), eqAt r u * g (bitsE u n) := by
  simp [eqCubeSum]

theorem eqCubeSum_full (r : List E) (n : ℕ) (g : List E → E) {acc : List E} (h : acc.length = n)
    (hr : r.length = n) : eqCubeSum r n g acc = g acc := by
  simp only [eqCubeSum, h, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton, bitsE,
    List.append_nil]
  rw [List.drop_eq_nil_of_le (by omega), eqAt_nil, one_mul]

/-- **A cube sum is a plain family** when its summand has degree `d` in each coordinate. -/
theorem tCubeSum_plainFamily {β : Type} (n d : ℕ) (G : β → List E → E)
    (hG : ∀ q pre post, PolyLE d fun x ↦ G q (pre ++ x :: post)) :
    PlainFamily (fun q acc ↦ tCubeSum n (G q) acc) d n := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by omega
  refine ⟨?_, ?_⟩
  · refine PolyLE.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      G q (acc ++ x :: bitsE u (n - (acc.length + 1)))) ?_ fun x ↦ ?_
    · exact PolyLE.sum _ fun u _ ↦ hG q acc _
    · simp only [tCubeSum, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
  · simp only [tCubeSum, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [bitsE_two_mul, bitsE_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

/-- **An equality cube sum is an equality family** at `r` (`|r| = n`) when its summand has degree `d` in each
coordinate (as `FP_eqFamily`). -/
theorem eqCubeSum_eqFamily {β : Type} (r : List E) (n d : ℕ) (hr : r.length = n) (G : β → List E → E)
    (hG : ∀ q pre post, PolyLE d fun x ↦ G q (pre ++ x :: post)) :
    EqFamily (fun q acc ↦ eqCubeSum r n (G q) acc) r d := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by omega
  have hdrop : r.drop acc.length = r[acc.length] :: r.drop (acc.length + 1) :=
    List.drop_eq_getElem_cons hacc
  refine ⟨?_, ?_⟩
  · refine PolyLE.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      eqAt (r.drop (acc.length + 1)) u * G q (acc ++ x :: bitsE u (n - (acc.length + 1)))) ?_ fun x ↦ ?_
    · exact PolyLE.sum _ fun u _ ↦ PolyLE.const_mul (hG q acc _) _
    · simp only [eqCubeSum, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
  · simp only [eqCubeSum, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, hdrop, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [eqAt_cons, eqAt_cons, bitsE_two_mul, bitsE_two_mul_add_one]
    have h1 : 2 * u % 2 = 0 := by omega
    have h2 : (2 * u + 1) % 2 = 1 := by omega
    have h3 : 2 * u / 2 = u := by omega
    have h4 : (2 * u + 1) / 2 = u := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false, List.append_assoc,
      List.singleton_append]
    ring

/-! ## Degrees -/

/-- A list sum of functions of degree `d`. -/
theorem polyLE_listSum {γ : Type} (d : ℕ) (l : List γ) (F : γ → E → E) (h : ∀ a ∈ l, PolyLE d (F a)) :
    PolyLE d fun x ↦ (l.map fun a ↦ F a x).sum := by
  induction l with
  | nil => exact (PolyLE.const d 0).congr fun x ↦ by simp
  | cons a l ih =>
    refine (PolyLE.add (h a (List.mem_cons_self ..)) (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))).congr
      fun x ↦ ?_
    simp

/-! ## The quadratic escape of `γ` -/

/-- **`a + γb + γ²c` against a different triple agrees at `2/|E|` of the `γ`** (Schwartz–Zippel). -/
theorem quadT_escape {a b c a' b' c' : E} (hne : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    avgE (fun g ↦ indE (a + g * b + g * g * c = a' + g * b' + g * g * c')) ≤ errE 2 := by
  have hp : ∀ (u v w : E), (C u + C v * X + C w * X ^ 2 : E[X]).natDegree ≤ 2 := fun u v w ↦ by
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le (by simp) ?_)) ?_)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have hne' : (C a + C b * X + C c * X ^ 2 : E[X]) ≠ C a' + C b' * X + C c' * X ^ 2 := by
    intro h
    refine hne ⟨?_, ?_, ?_⟩
    · have := congrArg (fun p : E[X] ↦ p.coeff 0) h
      simpa using this
    · have := congrArg (fun p : E[X] ↦ p.coeff 1) h
      simpa [coeff_X, coeff_X_pow] using this
    · have := congrArg (fun p : E[X] ↦ p.coeff 2) h
      simpa [coeff_X, coeff_X_pow] using this
  refine (avgE_mono fun g ↦ indE_mono fun hg ↦ ?_).trans (sz_escape hne' (hp a b c) (hp a' b' c'))
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination hg

/-! ## The matrices over their entries -/

/-- The multilinear extension of `f` on `n` coordinates at `pt`. -/
noncomputable def mleZ (n : ℕ) (f : ℕ → E) (pt : List E) : E := ∑ x ∈ range (2 ^ n), eqAt pt x * f x

/-- A word of `z` over `E`. -/
noncomputable def zwE (z : ℕ → FK) (y : ℕ) : E := FE.toExt3 (FE.ofK (z y))

/-- `(M_o z)(x)` over `E`. -/
noncomputable def matE (Q : Program) (lay : Lay) (z : ℕ → FK) (o x : ℕ) : E := FE.toExt3 (matZ Q lay o z x)

/-- The slot relation over `E`: `(A z)(B z) + ((D z) + (W z))` at `x`. -/
noncomputable def relE (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : E :=
  matE Q lay z 0 x * matE Q lay z 1 x + (matE Q lay z 2 x + matE Q lay z 3 x)

/-- The wiring's batching weights: `1, γ, γ², γ²` on `A, B, D, W`. -/
def wG (γ : E) (o : ℕ) : E := if o = 0 then 1 else if o = 1 then γ else γ * γ

/-- **The zerocheck's summand**: `Ã(pt)·B̃(pt) + C̃(pt)`, the slot extensions of `A z`, `B z`, `(D + W) z`. -/
noncomputable def zeroGT (Q : Program) (lay : Lay) (z : ℕ → FK) (pt : List E) : E :=
  mleZ xVars (matE Q lay z 0) pt * mleZ xVars (matE Q lay z 1) pt +
    mleZ xVars (fun x ↦ matE Q lay z 2 x + matE Q lay z 3 x) pt

/-- **The wiring's matrix weight** at `(r_x, pt)`: `Σ_e w_γ(o)·c·eq(r_x, x)·eq(pt, y)`. -/
noncomputable def wireM (Q : Program) (lay : Lay) (γ : E) (rx pt : List E) : E :=
  ((ents Q lay).map fun e ↦ wG γ e.o * FE.toExt3 e.c * eqAt rx e.x * eqAt pt e.y).sum

/-- **The wiring's summand**: the matrix weight times `z̃(pt)`. -/
noncomputable def wireGT (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E) (rx pt : List E) : E :=
  wireM Q lay γ rx pt * mleZ yVars (zwE z) pt

/-- `(M_o z)(x)` over `E` is its entries' sum. -/
theorem matE_eq (Q : Program) (lay : Lay) (z : ℕ → FK) (o x : ℕ) :
    matE Q lay z o x = (((ents Q lay).filter fun e ↦ e.o == o && e.x == x).map fun e ↦
      FE.toExt3 e.c * zwE z e.y).sum := by
  unfold matE matZ
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul]; rfl)

/-- The slot extension of a matrix's per-slot sums is the sum over its entries (slots below `2^n`). -/
theorem mle_filter (n o : ℕ) (r : List E) (f : Ent → E) :
    ∀ l : List Ent, (∀ e ∈ l, e.x < 2 ^ n) →
      ∑ x ∈ range (2 ^ n), eqAt r x * ((l.filter fun e ↦ e.o == o && e.x == x).map f).sum =
        ((l.filter fun e ↦ e.o == o).map fun e ↦ eqAt r e.x * f e).sum
  | [], _ => by simp
  | e :: l, hl => by
    have ih := mle_filter n o r f l fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have he : e.x < 2 ^ n := hl e (List.mem_cons_self ..)
    rw [Finset.sum_congr rfl fun x _ ↦ show eqAt r x * (((e :: l).filter fun e ↦ e.o == o && e.x == x).map f).sum =
        (if e.x = x then (if e.o = o then eqAt r e.x * f e else 0) else 0) +
          eqAt r x * ((l.filter fun e ↦ e.o == o && e.x == x).map f).sum by
      by_cases hx : e.x = x
      · subst hx
        by_cases ho : e.o = o
        · simp [ho, mul_add]
        · simp [ho]
      · simp [hx]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr he), ih]
    by_cases ho : e.o = o
    · simp [ho]
    · simp [ho]

/-- A matrix's slot extension at `r` is its entries' sum (a checked layout). -/
theorem mleZ_matE (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (o : ℕ) (r : List E) :
    mleZ xVars (matE Q lay z o) r = (((ents Q lay).filter fun e ↦ e.o == o).map fun e ↦
      eqAt r e.x * (FE.toExt3 e.c * zwE z e.y)).sum := by
  unfold mleZ
  simp only [matE_eq]
  exact mle_filter xVars o r _ _ fun e he ↦ (ents_fit Q lay hlay e he).2.1

/-- A finite sum of list sums is the list sum of the finite sums. -/
theorem sum_list_swap {α ι : Type} (s : Finset ι) (l : List α) (f : α → ι → E) :
    ∑ u ∈ s, (l.map fun a ↦ f a u).sum = (l.map fun a ↦ ∑ u ∈ s, f a u).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- The weights of the four matrices on `range 4`. -/
theorem sum_wG (γ : E) (S : ℕ → E) : ∑ w ∈ range (2 ^ 2), wG γ w * S w = S 0 + γ * S 1 + γ * γ * (S 2 + S 3) := by
  simp [Finset.sum_range_succ, wG]
  ring

/-- **The wiring sumcheck's claim**: before any challenge, the family is `a + γ b + γ² c` at the true slot
extensions (a checked layout: the entries' slots and words on the cube). -/
theorem wire_nil (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E) (rx : List E) :
    tCubeSum yVars (wireGT Q lay z γ rx) [] =
      mleZ xVars (matE Q lay z 0) rx + γ * mleZ xVars (matE Q lay z 1) rx +
        γ * γ * mleZ xVars (fun x ↦ matE Q lay z 2 x + matE Q lay z 3 x) rx := by
  have hfit := ents_fit Q lay hlay
  have hsplit : mleZ xVars (fun x ↦ matE Q lay z 2 x + matE Q lay z 3 x) rx =
      mleZ xVars (matE Q lay z 2) rx + mleZ xVars (matE Q lay z 3) rx := by
    simp only [mleZ, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have key := sum_wG γ fun w ↦ mleZ xVars (matE Q lay z w) rx
  rw [← key]
  simp only [mleZ_matE Q lay hlay]
  rw [sum_sel_filter (wG γ) _ _ fun e he ↦ (hfit e he).1, tCubeSum_nil]
  unfold wireGT wireM
  have hz : ∀ u < 2 ^ yVars, mleZ yVars (zwE z) (bitsE u yVars) = zwE z u := fun u hu ↦ by
    unfold mleZ; exact sum_eqAt_bitsE hu _
  rw [Finset.sum_congr rfl fun u hu ↦ by rw [hz u (Finset.mem_range.mp hu), ← List.sum_map_mul_right],
    sum_list_swap]
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  have hy := (hfit e he).2.2
  rw [Finset.sum_congr rfl fun u hu ↦ by
    rw [eqAt_bitsE_lt (Finset.mem_range.mp hu) hy]]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (range (2 ^ yVars)) e.y, ite_eq_left (Finset.mem_range.mpr hy)]
  ring

/-- **The wiring's final matrix weight** is the four matrices' values batched by `γ` (`|r_x| = 20`). -/
theorem wireM_full (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (γ : E) (rx ry : List E)
    (hrx : rx.length = xVars) :
    wireM Q lay γ rx ry = matMle Q lay 0 (rx ++ ry) + γ * matMle Q lay 1 (rx ++ ry) +
      γ * γ * (matMle Q lay 2 (rx ++ ry) + matMle Q lay 3 (rx ++ ry)) := by
  have hfit := ents_fit Q lay hlay
  rw [← sum_wG γ fun w ↦ matMle Q lay w (rx ++ ry)]
  simp only [matMle_eq_sum]
  rw [sum_sel_filter (wG γ) _ _ fun e he ↦ (hfit e he).1]
  unfold wireM
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  have hx := (hfit e he).2.1
  rw [eqAt_append, hrx, eqAt_mod rx (e.x + 2 ^ xVars * e.y), hrx,
    show (e.x + 2 ^ xVars * e.y) % 2 ^ xVars = e.x by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx],
    show (e.x + 2 ^ xVars * e.y) / 2 ^ xVars = e.y by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]]
  ring

/-- **The zerocheck's claim**: before any challenge, the family is the `eq(τ, ·)`-weighted slot relation. -/
theorem zero_nil (Q : Program) (lay : Lay) (z : ℕ → FK) (τ : List E) :
    eqCubeSum τ xVars (zeroGT Q lay z) [] = ∑ w ∈ range (2 ^ xVars), eqAt τ w * relE Q lay z w := by
  rw [eqCubeSum_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.mp hu
  unfold zeroGT mleZ relE
  rw [sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']

/-- **The wiring relation is the slot relation on the cube** (a checked layout: no entry past `2^20`). -/
theorem wiringRel_iff (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) :
    WiringRel Q lay z ↔ ∀ x < 2 ^ xVars, relE Q lay z x = 0 := by
  have hfit := ents_fit Q lay hlay
  have hrel : ∀ x, relE Q lay z x = FE.toExt3 (matA Q lay z x * matB Q lay z x + matD Q lay z x +
      matW Q lay z x) := fun x ↦ by
    simp only [relE, matE, FE.toExt3_add, FE.toExt3_mul]; ring
  constructor
  · intro h x _
    rw [hrel, h x, FE.toExt3_zero]
  · intro h x
    by_cases hx : x < 2 ^ xVars
    · have := h x hx
      rw [hrel, ← FE.toExt3_zero] at this
      exact FE.toExt3_injective this
    · have h0 : ∀ o, matZ Q lay o z x = 0 := fun o ↦ by
        unfold matZ
        rw [List.filter_eq_nil_iff.mpr fun e he ↦ by
          have := (hfit e he).2.1
          simp only [Bool.and_eq_true, beq_iff_eq, not_and]
          intro _ hex; omega]
        rfl
      simp only [matA, matB, matD, matW, h0, mul_zero, add_zero]

/-! ## Degrees of the summands -/

theorem polyLE_mleZ (n : ℕ) (f : ℕ → E) (pre post : List E) :
    PolyLE 1 fun x ↦ mleZ n f (pre ++ x :: post) :=
  polyLE_mle pre post _ f

theorem polyLE_zeroG (Q : Program) (lay : Lay) (z : ℕ → FK) (pre post : List E) :
    PolyLE 2 fun x ↦ zeroGT Q lay z (pre ++ x :: post) :=
  PolyLE.add (PolyLE.mul (polyLE_mleZ _ _ pre post) (polyLE_mleZ _ _ pre post))
    ((polyLE_mleZ _ _ pre post).mono (by norm_num))

theorem polyLE_wireM (Q : Program) (lay : Lay) (γ : E) (rx pre post : List E) :
    PolyLE 1 fun x ↦ wireM Q lay γ rx (pre ++ x :: post) :=
  polyLE_listSum 1 _ _ fun e _ ↦ PolyLE.const_mul (polyLE_eqAt pre post e.y) _

theorem polyLE_wireG (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E) (rx pre post : List E) :
    PolyLE 2 fun x ↦ wireGT Q lay z γ rx (pre ++ x :: post) :=
  PolyLE.mul (polyLE_wireM Q lay γ rx pre post) (polyLE_mleZ _ _ pre post)

/-! ## Cube points and fields -/

/-- `boolPoint` is `bitsE`. -/
theorem boolPoint_eq_bitsE : ∀ (m x : ℕ), LeanVM.Protocol.EndToEnd.boolPoint m x = bitsE x m
  | 0, _ => rfl
  | m + 1, x => by
    have h : LeanVM.Protocol.EndToEnd.boolPoint (m + 1) x =
        (if x.testBit 0 then 1 else 0) :: LeanVM.Protocol.EndToEnd.boolPoint m (x / 2) := by
      simp only [LeanVM.Protocol.EndToEnd.boolPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ ↦ ?_
      simp [Nat.testBit_succ]
    rw [h, boolPoint_eq_bitsE m (x / 2), bitsE, Nat.testBit_zero]
    simp

/-- A cube sum against equality weights picks the index (`n < 2^μ`). -/
theorem sum_fin_eqAt (μ n : ℕ) (hn : n < 2 ^ μ) (g : ℕ → E) :
    ∑ x : Fin (2 ^ μ), eqAt (LeanVM.Protocol.EndToEnd.boolPoint μ x) n * g x = g n := by
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ eqAt (LeanVM.Protocol.EndToEnd.boolPoint μ x) n * g x)]
  rw [Finset.sum_congr rfl fun x hx ↦ by
    rw [boolPoint_eq_bitsE, eqAt_bitsE_lt (Finset.mem_range.mp hx) hn]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq (range (2 ^ μ)) n, ite_eq_left (Finset.mem_range.mpr hn)]

/-- The same over a range. -/
theorem sum_range_eqAt (μ n : ℕ) (hn : n < 2 ^ μ) (g : ℕ → E) :
    ∑ u ∈ range (2 ^ μ), eqAt (bitsE u μ) n * g u = g n := by
  rw [Finset.sum_congr rfl fun u hu ↦ by rw [eqAt_bitsE_lt (Finset.mem_range.mp hu) hn]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq (range (2 ^ μ)) n, ite_eq_left (Finset.mem_range.mpr hn)]

/-- A list sum over a range is the finite sum. -/
theorem listRange_sum (n : ℕ) (f : ℕ → E) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A base-field word read over `E`. -/
theorem zE_ofBF64 (k : K) : FE.toExt3 (FE.ofK (Lvm.FK.ofBF64 k)) = ofK k := by
  rw [FE.toExt3_ofK]; rfl

/-! ## Regions of the word space -/

/-- A region holds the word. -/
abbrev YReg.Has (r : YReg) (y : ℕ) : Prop := r.base ≤ y ∧ y < r.base + 2 ^ r.log

/-- `regSum`'s body over a region list. -/
noncomputable def regSumL (L : List YReg) (S : YSrc → Bool) (f : ℕ → E) (r : List E) : E :=
  (L.map fun reg ↦ if S reg.src then
    ((List.range (2 ^ reg.log)).map fun i ↦ eqAt r (reg.base + i) * f (reg.base + i)).sum else 0).sum

/-- `TInst.src?`'s body over a region list. -/
def ysrcL (L : List YReg) (y : ℕ) : Option YSrc :=
  (L.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src)

/-- Sorted regions are pairwise disjoint and below `2^yVars`. -/
theorem yregsSorted_pairwise : ∀ L : List YReg, yregsSorted L = true →
    L.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base) ∧ ∀ r ∈ L, r.base + 2 ^ r.log ≤ 2 ^ yVars
  | [], _ => ⟨List.Pairwise.nil, by simp⟩
  | [r], h => by
    simp only [yregsSorted, decide_eq_true_eq] at h
    exact ⟨List.pairwise_singleton _ _, by simpa using h.2⟩
  | r :: r' :: rs, h => by
    simp only [yregsSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hp, hb⟩ := yregsSorted_pairwise (r' :: rs) h.2
    have hr' : ∀ r'' ∈ r' :: rs, r'.base ≤ r''.base := by
      intro r'' hr''
      rcases List.mem_cons.mp hr'' with rfl | hr''
      · exact le_rfl
      · have := List.rel_of_pairwise_cons hp hr''
        have := Nat.two_pow_pos r'.log
        omega
    refine ⟨List.Pairwise.cons (fun r'' hr'' ↦ (h.1.2.trans (hr' r'' hr''))) hp, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · have := hb r' (List.mem_cons_self ..)
      have := Nat.two_pow_pos r'.log
      omega
    · exact hb x hx

/-- **A region's words have its source** (sorted regions). -/
theorem ysrcL_of_mem {L : List YReg} (hP : L.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base))
    {reg : YReg} (hreg : reg ∈ L) {i : ℕ} (hi : i < 2 ^ reg.log) :
    ysrcL L (reg.base + i) = some reg.src := by
  induction L with
  | nil => simp at hreg
  | cons r rs ih =>
    unfold ysrcL
    by_cases hr : reg = r
    · subst hr
      rw [List.find?_cons_of_pos (by simp; omega)]
      rfl
    · have hreg' : reg ∈ rs := (List.mem_cons.mp hreg).resolve_left hr
      have hle := List.rel_of_pairwise_cons hP hreg'
      rw [List.find?_cons_of_neg (by simp; omega)]
      exact ih (List.Pairwise.of_cons hP) hreg'

/-- A word outside every region has no source. -/
theorem ysrcL_none {L : List YReg} {y : ℕ} (h : ∀ reg ∈ L, ¬ reg.Has y) : ysrcL L y = none := by
  unfold ysrcL
  rw [List.find?_eq_none.mpr fun r hr ↦ by simpa [YReg.Has] using h r hr]
  rfl

/-- **The cube sum splits into the regions' sums** (sorted regions inside `[0, N)`, `f` zero off them). -/
theorem sum_regions (N : ℕ) : ∀ (L : List YReg), L.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base) →
    (∀ r ∈ L, r.base + 2 ^ r.log ≤ N) → ∀ (f : ℕ → E), (∀ y, (∀ reg ∈ L, ¬ reg.Has y) → f y = 0) →
    ∑ y ∈ range N, f y = (L.map fun reg ↦ ∑ i ∈ range (2 ^ reg.log), f (reg.base + i)).sum
  | [], _, _, f, hf => by
    simp only [List.map_nil, List.sum_nil]
    exact Finset.sum_eq_zero fun y _ ↦ hf y (by simp)
  | r :: rs, hP, hN, f, hf => by
    have hrN := hN r (List.mem_cons_self ..)
    have hsplit : ∑ y ∈ range N, f y = ∑ y ∈ range N, (if r.Has y then f y else 0) +
        ∑ y ∈ range N, (if r.Has y then 0 else f y) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> simp
    have h1 : ∑ y ∈ range N, (if r.Has y then f y else 0) = ∑ i ∈ range (2 ^ r.log), f (r.base + i) := by
      rw [← Finset.sum_filter]
      have hset : (range N).filter (fun y ↦ r.Has y) = Finset.Ico r.base (r.base + 2 ^ r.log) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, YReg.Has]; omega
      rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have h2 := sum_regions N rs (List.Pairwise.of_cons hP) (fun x hx ↦ hN x (List.mem_cons_of_mem _ hx))
      (fun y ↦ if r.Has y then 0 else f y) (fun y hy ↦ by
        split_ifs with hr
        · rfl
        · exact hf y fun reg hreg ↦ by
            rcases List.mem_cons.mp hreg with rfl | hreg
            · exact hr
            · exact hy reg hreg)
    rw [hsplit, h1, h2, List.map_cons, List.sum_cons]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ Finset.sum_congr rfl fun i hi ↦ ?_)
    have hle := List.rel_of_pairwise_cons hP hreg
    rw [ite_eq_right (by simp only [YReg.Has]; omega)]

/-- **The seven sources' region sums** add up to the regions' sums. -/
theorem regSumL_sources (L : List YReg) (f : ℕ → E) (r : List E) :
    regSumL L (· == .com) f r + regSumL L (· == .sflat) f r + regSumL L (· == .sigma) f r +
        regSumL L (· == .ks) f r + (regSumL L (· == .pub) f r + regSumL L (· == .qlt) f r +
          regSumL L (· == .one) f r) =
      (L.map fun reg ↦ ∑ i ∈ range (2 ^ reg.log), eqAt r (reg.base + i) * f (reg.base + i)).sum := by
  induction L with
  | nil => simp [regSumL]
  | cons reg L ih =>
    simp only [regSumL, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, listRange_sum]
    cases reg.src <;> simp <;> ring

/-- Region sums agree when their functions agree on the regions' words. -/
theorem regSumL_congr (L : List YReg) (S : YSrc → Bool) {f g : ℕ → E} (r : List E)
    (h : ∀ reg ∈ L, S reg.src = true → ∀ i < 2 ^ reg.log, f (reg.base + i) = g (reg.base + i)) :
    regSumL L S f r = regSumL L S g r := by
  unfold regSumL
  refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ ?_)
  split_ifs with hS
  · refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    rw [h reg hreg hS i (List.mem_range.mp hi)]
  · rfl

/-- **A region claim holds** iff its value is the region sum of the commitment's words (the maps inside the
commitment). -/
theorem holds_regClaim (μ : ℕ) (L : List YReg) (S : YSrc → Bool) (w : ℕ → ℕ) (r : List E) (v : E) (q : Column μ)
    (hw : ∀ reg ∈ L, S reg.src = true → ∀ i < 2 ^ reg.log, w (reg.base + i) < 2 ^ μ) :
    LeanVM.Protocol.EndToEnd.StackClaim.Holds μ (fun X ↦ regSumL L S (fun y ↦ eqAt X (w y)) r, v) q ↔
      regSumL L S (fun y ↦ ofK (q.values.getD (w y) 0)) r = v := by
  unfold LeanVM.Protocol.EndToEnd.StackClaim.Holds
  refine Eq.congr_left ?_
  simp only [regSumL]
  simp only [← List.sum_map_mul_right]
  rw [sum_list_swap]
  refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ ?_)
  split_ifs with hS
  · simp only [← List.sum_map_mul_right]
    rw [sum_list_swap]
    refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    rw [← sum_fin_eqAt μ (w (reg.base + i)) (hw reg hreg hS i (List.mem_range.mp hi))
      (fun x ↦ ofK (q.values.getD x 0)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  · simp

/-! ## The relayout's family -/

/-- The relayout's kernel over a region list (`relayKern`'s body). -/
noncomputable def relayKernL (L : List YReg) (sw : ℕ → ℕ) (ry pt : List E) : E :=
  regSumL L (· == .sflat) (fun y ↦ eqAt pt (sw y)) ry

/-- **The relayout's summand**: the kernel times `C_rec`'s extension. -/
noncomputable def relayGT (L : List YReg) (sw : ℕ → ℕ) (ry : List E) (μ : ℕ) (f : ℕ → E) (pt : List E) : E :=
  relayKernL L sw ry pt * mleZ μ f pt

theorem polyLE_regSumL (L : List YReg) (S : YSrc → Bool) (ry : List E) (g : ℕ → ℕ) (pre post : List E) :
    PolyLE 1 fun x ↦ regSumL L S (fun y ↦ eqAt (pre ++ x :: post) (g y)) ry := by
  unfold regSumL
  refine polyLE_listSum 1 _ _ fun reg _ ↦ ?_
  by_cases hS : S reg.src = true
  · simp only [hS, ite_true]
    exact polyLE_listSum 1 _ _ fun i _ ↦ PolyLE.const_mul (polyLE_eqAt pre post _) _
  · simp only [hS, Bool.false_eq_true, ite_false]
    exact PolyLE.const 1 0

theorem polyLE_relayG (L : List YReg) (sw : ℕ → ℕ) (ry : List E) (μ : ℕ) (f : ℕ → E) (pre post : List E) :
    PolyLE 2 fun x ↦ relayGT L sw ry μ f (pre ++ x :: post) :=
  PolyLE.mul (polyLE_regSumL L _ ry sw pre post) (polyLE_mleZ μ f pre post)

/-- **The relayout's claim**: before any challenge, the family is the region sum of `C_rec`'s words through the
map (the map inside `C_rec`). -/
theorem relay_nil (L : List YReg) (sw : ℕ → ℕ) (ry : List E) (μ : ℕ) (f : ℕ → E)
    (hw : ∀ reg ∈ L, reg.src = .sflat → ∀ i < 2 ^ reg.log, sw (reg.base + i) < 2 ^ μ) :
    tCubeSum μ (relayGT L sw ry μ f) [] = regSumL L (· == .sflat) (fun y ↦ f (sw y)) ry := by
  rw [tCubeSum_nil]
  have hz : ∀ u < 2 ^ μ, mleZ μ f (bitsE u μ) = f u := fun u hu ↦ by
    unfold mleZ; exact sum_eqAt_bitsE hu _
  unfold relayGT relayKernL regSumL
  rw [Finset.sum_congr rfl fun u hu ↦ by rw [hz u (Finset.mem_range.mp hu), ← List.sum_map_mul_right],
    sum_list_swap]
  refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ ?_)
  split_ifs with hS
  · simp only [← List.sum_map_mul_right]
    rw [sum_list_swap]
    refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    rw [← sum_range_eqAt μ _ (hw reg hreg (by simpa using hS) i (List.mem_range.mp hi)) f, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ ↦ by ring
  · simp

end Lvm.Typed
