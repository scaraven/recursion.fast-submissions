-- New for lvm6 Y1 (2026-11-22): merged module (build cost: one import load), parts:
--   Lvm6EqKernel: `eq_kernel` and `dot` over any field (copies of `LvmE2VGkrBase`'s generic lemmas,
--   Lvm6MbSample: the multi-draw grinding rule at `E2`, written once: averages over `n` challenges,
import LvmE2VWireAlg
import Lvm6MbProg

/-! ### Part `Lvm6EqKernel` (was its own module) -/
section

/-!
# `eq_kernel` over a field

`eqKernelF_length`, `eqKernelF_getD` (the kernel lists the equality weights), `dotF_eq`, `dot_eqKernelF`: verbatim
from `LvmE2VGkrBase` (namespace `Lvm6` here).
-/

set_option autoImplicit false

namespace Lvm6

open Lvm.E2V Finset

section

variable {F : Type} [Field F]

theorem eqKernelF_append (pt : List F) (r : F) :
    eqKernelF (pt ++ [r]) = (eqKernelF pt).map (· * (1 + r)) ++ (eqKernelF pt).map (· * r) := by
  unfold eqKernelF
  rw [List.foldl_concat]

theorem eqKernelF_length : ∀ pt : List F, (eqKernelF pt).length = 2 ^ pt.length := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernelF_append, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem getD_map_mulF (l : List F) (c : F) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

/-- **`eq_kernel` lists the equality weights.** -/
theorem eqKernelF_getD : ∀ (pt : List F) (w : ℕ),
    (eqKernelF pt).getD w 0 = if w < 2 ^ pt.length then eqAtF pt w else 0 := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil =>
    intro w
    rcases w with _ | w
    · rfl
    · simp [eqKernelF, List.getD_eq_getElem?_getD]
  | append_singleton pt r ih =>
    intro w
    have hlen := eqKernelF_length pt
    rw [eqKernelF_append, List.length_append, List.length_singleton, eqAtF_append]
    by_cases hw : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using hw), getD_map_mulF, ih,
        ite_eq_left hw, ite_eq_left (by rw [pow_succ]; omega), Nat.div_eq_of_lt hw]
      simp [eqAtF]
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mulF, ih]
      by_cases hw2 : w < 2 ^ (pt.length + 1)
      · have hq : w / 2 ^ pt.length = 1 :=
          Nat.div_eq_of_lt_le (by rw [pow_succ] at hw2; omega) (by omega)
        rw [ite_eq_left hw2, hq, ite_eq_left (by rw [pow_succ] at hw2; omega), eqAtF_mod pt w,
          eqAtF_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega)]
        simp [eqAtF]
      · rw [ite_eq_right hw2, ite_eq_right (by rw [pow_succ] at hw2; omega), zero_mul]

theorem dotF_eq : ∀ (a b : List F), a.length = b.length →
    dotF a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 := by
  intro a b h
  unfold dotF
  rw [← sumF, sumF_eq_sum]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    rcases b with _ | ⟨y, b⟩
    · simp at h
    · simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
      rw [ih b (by simpa using h)]
      simp [add_comm]

/-- **The verifier's `dot(eq[:n], w)`**: the equality-weighted sum of `w`. -/
theorem dot_eqKernelF (pt w : List F) (hn : w.length ≤ 2 ^ pt.length) :
    dotF ((eqKernelF pt).take w.length) w = ∑ j ∈ range w.length, eqAtF pt j * w.getD j 0 := by
  rw [dotF_eq _ _ (by simp [eqKernelF_length, hn]), List.length_take, eqKernelF_length,
    min_eq_left hn]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj', ← List.getD_eq_getElem?_getD,
    eqKernelF_getD, ite_eq_left (by omega)]

/-! ## The linear map's transpose -/


end

section

variable {F : Type} [Field F] [CharP F 2]

/-- The equality weights sum to one. -/
theorem sum_eqAtF : ∀ pt : List F, ∑ w ∈ range (2 ^ pt.length), eqAtF pt w = 1
  | [] => by simp
  | r :: rs => by
    rw [List.length_cons, sum_cube_succW, ← sum_eqAtF rs, Finset.sum_congr rfl fun w _ ↦ ?_]
    rw [eqAtF_succ, eqAtF_succ]
    have h1 : 2 * w % 2 = 0 := by omega
    have h2 : (2 * w + 1) % 2 = 1 := by omega
    have h3 : 2 * w / 2 = w := by omega
    have h4 : (2 * w + 1) / 2 = w := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false]
    rw [← add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero, one_mul]

end

end Lvm6
end -- part Lvm6EqKernel

/-! ### Part `Lvm6MbSample` (was its own module) -/
section

/-!
# The group rule at `E2`

A ground group `e2SampleN g (n + 1)` (`Lvm6MbProg`) reads a nonce, draws `n + 1` challenges, and accepts only if the
first passes `powOK g` (lane 2 `< 2^(64 − g)`); its values are lanes 0–1 of each draw (`e2OfE`). The proof of work
looks at a lane the values do not, so an accepted bad tuple is a fraction `2^-g` of the bad `E2` tuples.

**Headline statements** (stable; the other Y1 modules consume them):

* `avgEN n f = |E|^-n · Σ_{c : Fin n → E} f c` — the average over `n` challenges;
* `avgEN_powOK_le (hg : g ≤ 64) (Q) (hQ : Nat.card {y // Q y} ≤ N · |E2|^m) :
    avgEN (m + 1) (fun c ↦ indE (powOK g (c 0) ∧ Q (fun i ↦ e2OfE (c i)))) ≤ errG g N` — the product rule;
* `szN_escape_grind (hg : g ≤ 64) (hP : P ≠ 0) (hd : P.totalDegree ≤ d) :
    avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧ MvPolynomial.eval (fun i ↦ e2OfE (c i)) P = 0)) ≤ errG g d`
  (`P : MvPolynomial (Fin (n + 1)) E2`; season 1's `sz_escape_grind` is `n = 0`);
* `e2SampleNSpecP` — the rule on any pre/postcondition: `Spec (e2SampleN g (n + 1)) Pre Post εmax 0 T` from reads
  keeping `Pre`, the escape `avgEN (n + 1) (powOK ∧ ¬ Post at the drawn history) ≤ e`, `e + T ≤ εmax`, `e < 1`;
* **`e2SampleNSpec`** — the `Doomed` form: from `Doomed C A` to `fun ys h ↦ ys.length = n + 1 ∧ Doomed C (A' ys) h`,
  lead `0`, given `hesc : ∀ q, ¬ A q → avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧ A' ((List.ofFn c).map e2OfE) q))
  ≤ e`, `L₀ · e + T ≤ εmax`, `εmax < 1`; `e2SampleNSpecPoly`: the escape event a nonzero polynomial of total degree
  `≤ d` vanishing (`e = errG g d`);
* **`e2SampleNSpecH`**, `e2SampleNSpecHCount` — the `HDoom` form (doom on a relation over the oracles `cands W`);
* `e2SampleSpecP`, **`e2SampleSpecH`** — one ground challenge (`e2Sample g`) on any pre/postcondition and in the
  `HDoom` form, the escape a count `≤ d` of bad `E2` values (`L₀ · errG g d`);
* `e2SampleN_one`, `e2SampleOneSpec` — `n = 1` is `e2Sample` with its value returned as a list.
-/

set_option autoImplicit false

namespace Lvm6.Mb

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V
open Finset
open scoped ENNReal

/-! ## Averages over `n` challenges -/

/-- **The average over `n` challenges**: `|E|^-n · Σ_{c : Fin n → E} f c`. -/
noncomputable def avgEN (n : ℕ) (f : (Fin n → E) → ℝ≥0∞) : ℝ≥0∞ :=
  ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ c, f c

theorem avgEN_mono {n : ℕ} {f f' : (Fin n → E) → ℝ≥0∞} (h : ∀ c, f c ≤ f' c) : avgEN n f ≤ avgEN n f' := by
  unfold avgEN
  gcongr with c
  exact h c

/-- **The union bound over candidates**, for an average over `n` challenges. -/
theorem avgEN_indE_exists_le {n : ℕ} {β : Type} {C : Set β} (hfin : C.Finite) {L₀ : ℕ} (hcard : C.ncard ≤ L₀)
    {P : β → (Fin n → E) → Prop} {e : ℝ≥0∞} (h : ∀ q ∈ C, avgEN n (fun c ↦ indE (P q c)) ≤ e) :
    avgEN n (fun c ↦ indE (∃ q ∈ C, P q c)) ≤ L₀ * e := by
  classical
  let s := hfin.toFinset
  have hpt : ∀ c, indE (∃ q ∈ C, P q c) ≤ ∑ q ∈ s, indE (P q c) := fun c ↦ by
    by_cases hc : ∃ q ∈ C, P q c
    · obtain ⟨q, hq, hP⟩ := hc
      rw [indE_of ⟨q, hq, hP⟩, ← indE_of hP]
      exact Finset.single_le_sum (f := fun q ↦ indE (P q c)) (fun _ _ ↦ zero_le) (hfin.mem_toFinset.mpr hq)
    · rw [indE_of_not hc]
      exact zero_le
  calc avgEN n (fun c ↦ indE (∃ q ∈ C, P q c))
      ≤ avgEN n (fun c ↦ ∑ q ∈ s, indE (P q c)) := avgEN_mono hpt
    _ = ∑ q ∈ s, avgEN n (fun c ↦ indE (P q c)) := by
        unfold avgEN
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _q ∈ s, e := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * e := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card C hfin]
        exact_mod_cast hcard

/-- A sum of indicators is a count. -/
theorem sum_indE_eq_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ∑ c, indE (p c) = ((univ.filter p).card : ℝ≥0∞) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  unfold indE
  by_cases h : p c <;> simp [h]

/-! ## The product rule -/

/-- `(Fin n → E) ≃ (Fin n → E2) × (Fin n → K)`: lanes 0–1 and lane 2 of every draw. -/
def eSplitN (n : ℕ) : (Fin n → E) ≃ (Fin n → E2) × (Fin n → K) where
  toFun c := (fun i ↦ e2OfE (c i), fun i ↦ (c i).limb 2)
  invFun p := fun i ↦ eSplit.symm (p.1 i, p.2 i)
  left_inv c := funext fun i ↦ eSplit.symm_apply_apply (c i)
  right_inv p := Prod.ext (funext fun i ↦ congrArg Prod.fst (eSplit.apply_symm_apply (p.1 i, p.2 i)))
    (funext fun i ↦ congrArg Prod.snd (eSplit.apply_symm_apply (p.1 i, p.2 i)))

/-- The lane-2 words of `m + 1` draws whose first is below `2^(64 − g)`: `2^(64 − g) · 2^(64 m)`. -/
theorem card_lane0 {g m : ℕ} (hg : g ≤ 64) :
    (univ.filter fun k : Fin (m + 1) → K ↦ kToNat (k 0) < 2 ^ (64 - g)).card = 2 ^ (64 - g) * (2 ^ 64) ^ m := by
  rw [← Finset.card_map (Fin.consEquiv fun _ : Fin (m + 1) ↦ K).symm.toEmbedding]
  have h : (univ.filter fun k : Fin (m + 1) → K ↦ kToNat (k 0) < 2 ^ (64 - g)).map
      (Fin.consEquiv fun _ : Fin (m + 1) ↦ K).symm.toEmbedding =
      (univ.filter fun a : K ↦ kToNat a < 2 ^ (64 - g)) ×ˢ (univ : Finset (Fin m → K)) := by
    ext ⟨a, v⟩
    simp [Finset.mem_map_equiv, Fin.consEquiv]
  rw [h, Finset.card_product, card_kToNat_lt (by omega), Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    BF64.card_bf64]

/-- `errG g N = N / 2^(128 + g)`. -/
theorem errG_eq (g N : ℕ) : errG g N = N * ((2 : ℝ≥0∞) ^ (128 + g))⁻¹ := by
  rw [errG, pow_add, ENNReal.mul_inv (by simp) (by simp)]
  simp only [ENNReal.inv_pow]
  ring

/-- `(2^(a + b))⁻¹ · (x · 2^a) = x · (2^b)⁻¹`. -/
theorem inv_two_pow_add_mul (a b : ℕ) (x : ℝ≥0∞) :
    ((2 : ℝ≥0∞) ^ (a + b))⁻¹ * (x * 2 ^ a) = x * ((2 : ℝ≥0∞) ^ b)⁻¹ := by
  have h : ((2 : ℝ≥0∞) ^ a)⁻¹ * 2 ^ a = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
  rw [pow_add, ENNReal.mul_inv (by simp) (by simp)]
  calc ((2 : ℝ≥0∞) ^ a)⁻¹ * (2 ^ b)⁻¹ * (x * 2 ^ a) = x * (2 ^ b)⁻¹ * (((2 : ℝ≥0∞) ^ a)⁻¹ * 2 ^ a) := by ring
    _ = x * (2 ^ b)⁻¹ := by rw [h, mul_one]

/-- **The product rule**: the proof of work of the first draw looks at lane 2, which no value reads, so an accepted
tuple of draws whose values lie in `Q` is a fraction `2^-g · |Q| / 2^(128 (m + 1))`; with `|Q| ≤ N · |E2|^m` this is
`errG g N`. -/
theorem avgEN_powOK_le {g m N : ℕ} (hg : g ≤ 64) (Q : (Fin (m + 1) → E2) → Prop)
    (hQ : Nat.card {y // Q y} ≤ N * Fintype.card E2 ^ m) :
    avgEN (m + 1) (fun c ↦ indE (powOK g (c 0) ∧ Q (fun i ↦ e2OfE (c i)))) ≤ errG g N := by
  classical
  have hcount : (univ.filter fun c : Fin (m + 1) → E ↦ powOK g (c 0) ∧ Q (fun i ↦ e2OfE (c i))).card =
      (univ.filter Q).card * (2 ^ (64 - g) * (2 ^ 64) ^ m) := by
    rw [← card_lane0 (m := m) hg, ← Finset.card_product, ← Finset.card_map (eSplitN (m + 1)).toEmbedding]
    congr 1
    ext ⟨y, k⟩
    have h1 : (fun i ↦ e2OfE ((eSplitN (m + 1)).symm (y, k) i)) = y :=
      congrArg Prod.fst ((eSplitN (m + 1)).apply_symm_apply (y, k))
    have h2 : (fun i ↦ ((eSplitN (m + 1)).symm (y, k) i).limb 2) = k :=
      congrArg Prod.snd ((eSplitN (m + 1)).apply_symm_apply (y, k))
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [powOK_iff_lane2 hg, h1, congrFun h2 0, and_comm]
  have hQ' : (univ.filter Q).card ≤ N * (2 ^ 128) ^ m := by
    rw [← natCard_subtype_eq_card_filter, ← card_E2]
    exact hQ
  have hle : (univ.filter fun c : Fin (m + 1) → E ↦ powOK g (c 0) ∧ Q (fun i ↦ e2OfE (c i))).card ≤
      N * 2 ^ (128 * m + 64 * m + (64 - g)) := by
    rw [hcount]
    calc (univ.filter Q).card * (2 ^ (64 - g) * (2 ^ 64) ^ m)
        ≤ N * (2 ^ 128) ^ m * (2 ^ (64 - g) * (2 ^ 64) ^ m) := Nat.mul_le_mul_right _ hQ'
      _ = N * 2 ^ (128 * m + 64 * m + (64 - g)) := by
        rw [pow_add, pow_add, pow_mul, pow_mul]
        ring
  unfold avgEN
  rw [sum_indE_eq_card, card_E, errG_eq]
  have hD : (((2 ^ 192 : ℕ) : ℝ≥0∞) ^ (m + 1)) = (2 : ℝ≥0∞) ^ ((128 * m + 64 * m + (64 - g)) + (128 + g)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    congr 1
    omega
  rw [hD, ← inv_two_pow_add_mul (128 * m + 64 * m + (64 - g)) (128 + g) (N : ℝ≥0∞)]
  gcongr
  exact_mod_cast hle

/-- **Schwartz–Zippel over `E2^(n+1)` with grinding**: a nonzero polynomial of total degree `≤ d` vanishes at the
values of an accepted tuple of draws with probability `≤ errG g d = 2^-g · d / 2^128` (the joint probability over
`E^(n+1)`). Season 1's univariate `sz_escape_grind` is the case `n = 0`. -/
theorem szN_escape_grind {n g d : ℕ} (hg : g ≤ 64) {P : MvPolynomial (Fin (n + 1)) E2} (hP : P ≠ 0)
    (hd : P.totalDegree ≤ d) :
    avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧ MvPolynomial.eval (fun i ↦ e2OfE (c i)) P = 0)) ≤ errG g d := by
  classical
  refine avgEN_powOK_le hg (fun y ↦ MvPolynomial.eval y P = 0) ?_
  rw [natCard_subtype_eq_card_filter]
  have h := card_zeros_le_of_totalDegree_le_fin P hP hd
  simp only [Nat.add_sub_cancel] at h
  convert h using 2

/-! ## The programs -/

/-- The draws of a group after its nonce. -/
def e2SampleNTail (g n : ℕ) : VerifierProgram (List E2) :=
  VerifierProgram.sampleChallenge >>= fun c ↦ VerifierProgram.require (powOK g c) >>= fun _ ↦
    VerifierProgram.sampleChallenges n >>= fun cs ↦ pure ((c :: cs).map e2OfE)

theorem e2SampleN_succ (g n : ℕ) :
    e2SampleN g (n + 1) = VerifierProgram.readScalar >>= fun _ ↦ e2SampleNTail g n := rfl

/-- `n` challenges then a program of challenges is a program of challenges. -/
theorem sampleOnly_sampleChallenges_bind {β : Type} :
    ∀ (n : ℕ) (k : List E → VerifierProgram β), (∀ l, SampleOnly (k l)) →
      SampleOnly ((VerifierProgram.sampleChallenges n).bind k)
  | 0, k, hk => hk []
  | n + 1, k, hk => by
    show SampleOnly (VerifierProgram.sample fun x ↦
      ((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs)).bind k)
    refine .sample fun x ↦ ?_
    rw [VerifierProgram.bind_assoc]
    exact sampleOnly_sampleChallenges_bind n _ fun l ↦ hk _

theorem sampleOnly_e2SampleNTail (g n : ℕ) : SampleOnly (e2SampleNTail g n) := by
  refine .sample fun c ↦ ?_
  by_cases hp : powOK g c
  · show SampleOnly ((VerifierProgram.require (powOK g c)).bind _)
    rw [VerifierProgram.require, ite_eq_left_of_eq_true _ _ (eq_true hp), VerifierProgram.ret_bind]
    exact sampleOnly_sampleChallenges_bind n _ fun _ ↦ .ret _
  · show SampleOnly ((VerifierProgram.require (powOK g c)).bind _)
    rw [VerifierProgram.require, ite_eq_right_of_eq_false _ _ (eq_false hp)]
    exact .fail

/-- **`n` challenges in a row, then a sub-program**: the expectation is the average over the tuples, the history
extended by their samples. -/
theorem retExp_sampleChallenges_bind {β : Type} (G : β → List Ev → ℝ≥0∞) (h₀ : List Ev) :
    ∀ (n : ℕ) (k : List E → VerifierProgram β) (l : List Ev),
      VerifierProgram.retExp G h₀ l ((VerifierProgram.sampleChallenges n).bind k) =
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E,
          VerifierProgram.retExp G h₀ (l ++ (List.ofFn v).map Ev.sample) (k (List.ofFn v))
  | 0, k, l => by simp [VerifierProgram.sampleChallenges]
  | n + 1, k, l => by
    show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, VerifierProgram.retExp G h₀ (l ++ [Ev.sample x])
        (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs)).bind k) = _
    have ih : ∀ x : E, VerifierProgram.retExp G h₀ (l ++ [Ev.sample x])
        (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs)).bind k) =
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, VerifierProgram.retExp G h₀
          (l ++ (List.ofFn (Fin.cons x v : Fin (n + 1) → E)).map Ev.sample)
          (k (List.ofFn (Fin.cons x v : Fin (n + 1) → E))) := fun x ↦ by
      rw [VerifierProgram.bind_assoc]
      rw [retExp_sampleChallenges_bind G h₀ n (fun xs ↦ (VerifierProgram.ret (x :: xs)).bind k)]
      congr 1
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp [List.ofFn_succ]
    simp_rw [ih]
    rw [sum_fin_succ_fun (n := n) (fun w ↦ VerifierProgram.retExp G h₀ (l ++ (List.ofFn w).map Ev.sample)
      (k (List.ofFn w))), ← Finset.mul_sum, ← mul_assoc, pow_succ, ENNReal.mul_inv (by simp) (by simp),
      mul_comm ((Fintype.card E : ℝ≥0∞)⁻¹)]

/-- **The escape of a group after its nonce**: the probability of a bad return is the average over the tuples of
draws of "the first passes the proof of work and the return breaks `Post`". -/
theorem escRet_e2SampleNTail (Post : List E2 → List Ev → Prop) (h₀ : List Ev) (g n : ℕ) :
    VerifierProgram.escRet Post h₀ [] (e2SampleNTail g n) =
      avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧
        ¬ Post ((List.ofFn c).map e2OfE) (h₀ ++ (List.ofFn c).map Ev.sample))) := by
  classical
  unfold VerifierProgram.escRet
  show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, VerifierProgram.retExp _ h₀ ([] ++ [Ev.sample c])
      ((VerifierProgram.require (powOK g c)).bind fun _ ↦ (VerifierProgram.sampleChallenges n).bind fun cs ↦
        VerifierProgram.ret ((c :: cs).map e2OfE)) = _
  have hc : ∀ c : E, VerifierProgram.retExp (fun a h ↦ if Post a h then 0 else 1) h₀ ([] ++ [Ev.sample c])
      ((VerifierProgram.require (powOK g c)).bind fun _ ↦ (VerifierProgram.sampleChallenges n).bind fun cs ↦
        VerifierProgram.ret ((c :: cs).map e2OfE)) =
      ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E,
        indE (powOK g ((Fin.cons c v : Fin (n + 1) → E) 0) ∧
          ¬ Post ((List.ofFn (Fin.cons c v : Fin (n + 1) → E)).map e2OfE)
            (h₀ ++ (List.ofFn (Fin.cons c v : Fin (n + 1) → E)).map Ev.sample)) := by
    intro c
    by_cases hp : powOK g c
    · rw [VerifierProgram.require, ite_eq_left_of_eq_true _ _ (eq_true hp), VerifierProgram.ret_bind, retExp_sampleChallenges_bind]
      congr 1
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [VerifierProgram.retExp, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.map_cons,
        List.nil_append, List.cons_append, hp, true_and]
      unfold indE
      split_ifs <;> simp
    · rw [VerifierProgram.require, ite_eq_right_of_eq_false _ _ (eq_false hp)]
      simp [VerifierProgram.bind, VerifierProgram.retExp, Fin.cons_zero, hp, indE]
  simp_rw [hc]
  unfold avgEN
  rw [sum_fin_succ_fun (n := n) (fun w ↦ indE (powOK g (w 0) ∧
      ¬ Post ((List.ofFn w).map e2OfE) (h₀ ++ (List.ofFn w).map Ev.sample))), ← Finset.mul_sum, ← mul_assoc,
    pow_succ, ENNReal.mul_inv (by simp) (by simp), mul_comm ((Fintype.card E : ℝ≥0∞)⁻¹)]

/-- The samples of a tuple commit nothing. -/
theorem commits_map_sample (l : List E) : commits (l.map Ev.sample) = [] := by
  induction l with
  | nil => rfl
  | cons c l ih => simpa [commits] using ih

/-! ## The rule of a group -/

section Rule

variable {εmax T : ℝ≥0∞}

/-- **The rule of a ground group on any pre/postcondition**: reads keep `Pre`, and from `Pre` the probability that
the first draw passes the proof of work and the return breaks `Post` (at the history the draws extend) is `≤ e < 1`.
Lead `0` (the nonce is a move); the group is `e + T ≤ εmax`. -/
noncomputable def e2SampleNSpecP {Pre : List Ev → Prop} {Post : List E2 → List Ev → Prop} {g n : ℕ} {e : ℝ≥0∞}
    (hread : ∀ h x, Pre h → Pre (h ++ [Ev.read x]))
    (hesc : ∀ h₀, Pre h₀ → avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧
      ¬ Post ((List.ofFn c).map e2OfE) (h₀ ++ (List.ofFn c).map Ev.sample))) ≤ e)
    (he : e + T ≤ εmax) (he1 : e < 1) :
    Spec (e2SampleN g (n + 1)) Pre Post εmax 0 T :=
  Spec.congr (e2SampleN_succ g n).symm <|
    (Spec.readE (Post := fun _ h ↦ Pre h) (fun h x hp ↦ hread h x hp) he).bind' fun _ ↦
      Spec.ofNoMove (fun _ ha ↦ ((sampleOnly_e2SampleNTail g n).after ha).not_isMove) he1
        fun h₀ hp ↦ (escRet_e2SampleNTail Post h₀ g n).trans_le (hesc h₀ hp)

/-- **The doom rule of a ground group** (`Doomed` form): from `Doomed C A` to doom of `A' ys` at the group's values
`ys`, when each candidate not alive becomes alive at an accepted tuple of draws with probability `≤ e`. Lead `0`
(the nonce is a move); the group is `L₀ · e + T ≤ εmax`; `εmax < 1` (for `Spec.ofNoMove`). -/
noncomputable def e2SampleNSpec {β : Type} {C : List Ev → Set β} (hst : Stable C) (hfin : ∀ h, (C h).Finite)
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {g n : ℕ} (A : β → Prop) (A' : List E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q →
      avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧ A' ((List.ofFn c).map e2OfE) q)) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) (hε : εmax < 1) :
    Spec (e2SampleN g (n + 1)) (Doomed C A) (fun ys h ↦ ys.length = n + 1 ∧ Doomed C (A' ys) h) εmax 0 T :=
  e2SampleNSpecP (fun h x hd ↦ (Doomed.append hst rfl).mpr hd)
    (fun h₀ hd ↦ by
      refine (avgEN_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (avgEN_indE_exists_le (hfin h₀) (hcard h₀) (P := fun q c ↦ powOK g (c 0) ∧
          A' ((List.ofFn c).map e2OfE) q) fun q hq ↦ hesc q (hd q hq))
      obtain ⟨hp, hn⟩ := hc
      have hn' : ¬ Doomed C (A' ((List.ofFn c).map e2OfE)) h₀ := fun hd' ↦
        hn ⟨by simp, (Doomed.append hst (commits_map_sample _)).mpr hd'⟩
      by_contra hno
      exact hn' fun q hq ha ↦ hno ⟨q, hq, hp, ha⟩)
    he (lt_of_le_of_lt (le_trans le_self_add he) hε)

/-- **The doom rule of a ground group, a polynomial escape**: each candidate not alive becomes alive only where a
nonzero polynomial of total degree `≤ d` vanishes at the values; the group is `L₀ · errG g d + T ≤ εmax`. -/
noncomputable def e2SampleNSpecPoly {β : Type} {C : List Ev → Set β} (hst : Stable C) (hfin : ∀ h, (C h).Finite)
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {g n d : ℕ} (hg : g ≤ 64) (A : β → Prop) (A' : List E2 → β → Prop)
    (hpoly : ∀ q, ¬ A q → ∃ P : MvPolynomial (Fin (n + 1)) E2, P ≠ 0 ∧ P.totalDegree ≤ d ∧
      ∀ y : Fin (n + 1) → E2, A' (List.ofFn y) q → MvPolynomial.eval y P = 0)
    (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) (hε : εmax < 1) :
    Spec (e2SampleN g (n + 1)) (Doomed C A) (fun ys h ↦ ys.length = n + 1 ∧ Doomed C (A' ys) h) εmax 0 T :=
  e2SampleNSpec hst hfin hcard A A' (errG g d) (fun q hq ↦ by
    obtain ⟨P, hP, hd, hz⟩ := hpoly q hq
    refine (avgEN_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, hz _ ?_⟩).trans (szN_escape_grind hg hP hd)
    have h2 := hc.2
    rw [List.map_ofFn] at h2
    exact h2) he hε

/-- The `HDoom` doom after a run that keeps the first commitment. -/
theorem hdoom_of_append {S : Type} {ι : Type} {O : ι → Type} {cands : Word → Set (∀ i, O i)}
    {R : Set ((S × ∀ i, O i) × Unit)} {x : S} {h₀ : List Ev} {W : Word} (hW : firstWord h₀ = some W) (l : List Ev)
    (hn : ¬ HDoom cands R x (h₀ ++ l)) : ∃ o ∈ cands W, ((x, o), ()) ∈ R := by
  by_contra hno
  exact hn ⟨W, firstWord_append hW l, fun o ho hin ↦ hno ⟨o, ho, hin⟩⟩

/-- **The doom rule of a ground group** (`HDoom` form, doom on a relation over the oracles of the first commitment):
from doom on `R` at `x` to doom on `R'` at `f ys`, when each oracle outside `R` at `x` lands in `R'` at an accepted
tuple of draws with probability `≤ e`. Lead `0`; the group is `L₀ · e + T ≤ εmax`; `εmax < 1`. -/
noncomputable def e2SampleNSpecH {S S' : Type} {ι : Type} {O : ι → Type} {cands : Word → Set (∀ i, O i)}
    (hfin : ∀ W, (cands W).Finite) {L₀ : ℕ} (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (R : Set ((S × ∀ i, O i) × Unit)) (x : S) (R' : Set ((S' × ∀ i, O i) × Unit)) (f : List E2 → S') {g n : ℕ}
    (e : ℝ≥0∞)
    (hesc : ∀ o, ((x, o), ()) ∉ R →
      avgEN (n + 1) (fun c ↦ indE (powOK g (c 0) ∧ ((f ((List.ofFn c).map e2OfE), o), ()) ∈ R')) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) (hε : εmax < 1) :
    Spec (e2SampleN g (n + 1)) (HDoom cands R x) (fun ys h ↦ ys.length = n + 1 ∧ HDoom cands R' (f ys) h)
      εmax 0 T :=
  e2SampleNSpecP (fun h x hd ↦ hd.append _)
    (fun h₀ hd ↦ by
      obtain ⟨W, hW, hR⟩ := hd
      refine (avgEN_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (avgEN_indE_exists_le (hfin W) (hcard W) (P := fun o c ↦ powOK g (c 0) ∧
          ((f ((List.ofFn c).map e2OfE), o), ()) ∈ R') fun o ho ↦ hesc o (hR o ho))
      obtain ⟨hp, hn⟩ := hc
      obtain ⟨o, ho, hin⟩ := hdoom_of_append hW _ fun hd' ↦ hn ⟨by simp, hd'⟩
      exact ⟨o, ho, hp, hin⟩)
    he (lt_of_le_of_lt (le_trans le_self_add he) hε)

/-- **The doom rule of a ground group, a count escape** (`HDoom` form): each oracle outside `R` at `x` lands in `R'`
at `≤ N · |E2|^n` tuples of values; the group is `L₀ · errG g N + T ≤ εmax`. -/
noncomputable def e2SampleNSpecHCount {S S' : Type} {ι : Type} {O : ι → Type} {cands : Word → Set (∀ i, O i)}
    (hfin : ∀ W, (cands W).Finite) {L₀ : ℕ} (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (R : Set ((S × ∀ i, O i) × Unit)) (x : S) (R' : Set ((S' × ∀ i, O i) × Unit)) (f : List E2 → S') {g n N : ℕ}
    (hg : g ≤ 64)
    (hcnt : ∀ o, ((x, o), ()) ∉ R →
      Nat.card {y : Fin (n + 1) → E2 // ((f (List.ofFn y), o), ()) ∈ R'} ≤ N * Fintype.card E2 ^ n)
    (he : (L₀ : ℝ≥0∞) * errG g N + T ≤ εmax) (hε : εmax < 1) :
    Spec (e2SampleN g (n + 1)) (HDoom cands R x) (fun ys h ↦ ys.length = n + 1 ∧ HDoom cands R' (f ys) h)
      εmax 0 T :=
  e2SampleNSpecH hfin hcard R x R' f (errG g N) (fun o ho ↦ by
    refine le_of_eq_of_le ?_ (avgEN_powOK_le hg (fun y ↦ ((f (List.ofFn y), o), ()) ∈ R') (hcnt o ho))
    simp only [List.map_ofFn]
    rfl) he hε

end Rule

/-! ## One ground challenge -/

section One

variable {εmax T : ℝ≥0∞}

/-- **One ground challenge on any pre/postcondition**: reads keep `Pre`, and from `Pre` the probability that the
answer passes the proof of work and its value breaks `Post` is `≤ e`. Lead `0`; the group is `e + T ≤ εmax`. -/
noncomputable def e2SampleSpecP {Pre : List Ev → Prop} {Post : E2 → List Ev → Prop} {g : ℕ} {e : ℝ≥0∞}
    (hread : ∀ h x, Pre h → Pre (h ++ [Ev.read x]))
    (hesc : ∀ h₀, Pre h₀ → avgE (fun c ↦ indE (powOK g c ∧ ¬ Post (e2OfE c) (h₀ ++ [Ev.sample c]))) ≤ e)
    (he : e + T ≤ εmax) :
    Spec (e2Sample g) Pre Post εmax 0 T :=
  (Spec.readE (Post := fun _ h ↦ Pre h) (fun h x hp ↦ hread h x hp) he).bind' fun _ ↦
    (Spec.sampleE (Post := fun c h ↦ powOK g c → Post (e2OfE c) h) e (fun h₀ hp ↦ by
      classical
      rw [card_filter_eq_avgE]
      refine le_trans (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_) (hesc h₀ hp)
      by_contra hno
      exact hc fun hpw ↦ by_contra fun hpost ↦ hno ⟨hpw, hpost⟩)).bind' fun c ↦
      (Spec.require (Post := fun _ h ↦ Post (e2OfE c) h) (fun _ hp hpw ↦ hp hpw)).bind' fun _ ↦
        Spec.ret (Post := Post) (e2OfE c)

/-- **One ground challenge** (`HDoom` form): from doom on `R` at `x` to doom on `R'` at `f y`, when each oracle
outside `R` at `x` lands in `R'` at `≤ d` values. Lead `0`; the group is `L₀ · errG g d + T ≤ εmax`. -/
noncomputable def e2SampleSpecH {S S' : Type} {ι : Type} {O : ι → Type} {cands : Word → Set (∀ i, O i)}
    (hfin : ∀ W, (cands W).Finite) {L₀ : ℕ} (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (R : Set ((S × ∀ i, O i) × Unit)) (x : S) (R' : Set ((S' × ∀ i, O i) × Unit)) (f : E2 → S') {g d : ℕ}
    (hg : g ≤ 64) (hcnt : ∀ o, ((x, o), ()) ∉ R → Nat.card {y : E2 // ((f y, o), ()) ∈ R'} ≤ d)
    (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) :
    Spec (e2Sample g) (HDoom cands R x) (fun y h ↦ HDoom cands R' (f y) h) εmax 0 T :=
  e2SampleSpecP (fun h x hd ↦ hd.append _)
    (fun h₀ hd ↦ by
      classical
      obtain ⟨W, hW, hR⟩ := hd
      refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (avgE_indE_exists_le (hfin W) (hcard W) (P := fun o c ↦ powOK g c ∧ ((f (e2OfE c), o), ()) ∈ R')
          fun o ho ↦ ?_)
      · obtain ⟨o, ho, hin⟩ := hdoom_of_append hW _ hc.2
        exact ⟨o, ho, hc.1, hin⟩
      · rw [avgE_powOK_prod hg (fun y ↦ ((f y, o), ()) ∈ R'), errG]
        gcongr
        rw [← natCard_subtype_eq_card_filter]
        exact_mod_cast hcnt o (hR o ho))
    he

/-- `n = 1` is one ground challenge with its value returned as a list. -/
theorem e2SampleN_one (g : ℕ) : e2SampleN g 1 = e2Sample g >>= fun y ↦ pure [y] := by
  simp only [e2SampleN, e2Sample, bind_assoc, pure_bind]
  rfl

/-- **The doom rule of `e2SampleN g 1`** from season 1's univariate escape (`doomE2SampleSpec`): the return is one
value `y`, doomed on `A' y`. -/
noncomputable def e2SampleOneSpec {β : Type} {C : List Ev → Set β} [Finite β] (hst : Stable C) {L₀ : ℕ}
    (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ} (A : β → Prop) (A' : E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → avgE (fun c ↦ indE (powOK g c ∧ A' (e2OfE c) q)) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) :
    Spec (e2SampleN g 1) (Doomed C A) (fun ys h ↦ ∃ y, ys = [y] ∧ Doomed C (A' y) h) εmax 0 T :=
  Spec.congr (e2SampleN_one g).symm <|
    (doomE2SampleSpec hst hcard A A' e hesc he).bind' fun y ↦
      (Spec.ret (Post := fun ys h ↦ ∃ y, ys = [y] ∧ Doomed C (A' y) h) [y]).mono
        (fun _ hd ↦ ⟨y, rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end One

end Lvm6.Mb
end -- part Lvm6MbSample
