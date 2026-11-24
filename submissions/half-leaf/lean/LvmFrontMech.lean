-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/FlockMech.lean` (formal rev 40f877dc) as `LvmFrontMech` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.FlockMech

  The mechanism of the front phases' specifications: doom as "no candidate is alive", prover
  moves keeping it, a challenge escaping it with the union bound over the candidates, and the
  loops of reads and samples of the verifier program.
-/
import LvmSpecRulesLeaves
import LvmDslProg

-- ===== merged from `LvmFrontEscape` (GOLF module merge: `LvmFrontEscape.lean` is now a stub importing `LvmFrontMech`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/PubEscape.lean` (formal rev 40f877dc) as `LvmFrontEscape` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.PubEscape

  The probability that one uniform challenge escapes the doom of a front phase, in the form the
  calculus of verifier programs states it: an average over `E`, bounded by a worst-case
  round-by-round error of an ArkLib phase and a union bound over the candidates.
-/

/-!
# Escape averages of front phases

The calculus of verifier programs (`LeanVM.Protocol.Compile.Spec`) states the probability of an
event over one challenge as an average, `|E|⁻¹ · Σ_c [p c]` (`avgE`, `indE`). A front phase's
security on ArkLib's typed framework states it as `Pr{let c ← $ᵗ E}[p c] ≤ ε` for one statement
and one stack, at every verifier prefix (`IsLocallyBounded`). The front phases' doom
quantifies over the candidates of the level-0 commitment, a finite set of stacks, so a challenge
escapes it when it escapes for one candidate:

* `avgE_indE_le_of_prEvent`: the probability bounds the average;
* `avgE_indE_exists_le`: the union bound, `L₀` times the per-candidate bound for at most `L₀`
  candidates;
* `avgE_le_one`, `avgE_indE_le_one`: an average of probabilities is one.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters
open scoped ENNReal NNReal

section

/-- Stacks of a given height are finitely many: the candidates of a commitment are a finite set. -/
instance instFiniteColumn (n : ℕ) : Finite (Column n) :=
  Finite.of_injective (fun c : Column n ↦ fun i : Fin (2 ^ n) ↦ c.values[i]) fun a b h ↦ by
    obtain ⟨va⟩ := a
    obtain ⟨vb⟩ := b
    congr 1
    exact Vector.ext fun i hi ↦ congrFun h ⟨i, hi⟩

/-- Stacks of a given height are finitely many. -/
theorem finite_column (n : ℕ) : Finite (Column n) := instFiniteColumn n

/-- The indicator of a proposition, `1` if it holds and `0` otherwise. -/
noncomputable def indE (p : Prop) : ℝ≥0∞ := by classical exact if p then 1 else 0

/-- The average of a function over one uniform challenge, as the calculus writes it. -/
noncomputable def avgE (f : E → ℝ≥0∞) : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, f c

/-- An indicator is at most one. -/
theorem indE_le_one (p : Prop) : indE p ≤ 1 := by
  unfold indE
  split_ifs <;> simp

/-- The indicator of a false proposition is zero. -/
theorem indE_of_not {p : Prop} (h : ¬ p) : indE p = 0 := by
  simp [indE, h]

/-- The indicator of a true proposition is one. -/
theorem indE_of {p : Prop} (h : p) : indE p = 1 := by
  simp [indE, h]

/-- The indicator grows with the proposition. -/
theorem indE_mono {p q : Prop} (h : p → q) : indE p ≤ indE q := by
  by_cases hp : p
  · rw [indE_of hp, indE_of (h hp)]
  · rw [indE_of_not hp]
    exact zero_le

private theorem card_E_ne_zero : (Fintype.card E : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- An average of values at most `c` is at most `c`. -/
theorem avgE_le_of_le {f : E → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, f x ≤ c) : avgE f ≤ c := by
  unfold avgE
  calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, f x
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _x : E, c := by gcongr with x; exact h x
    _ = c := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel card_E_ne_zero (ENNReal.natCast_ne_top _), one_mul]

/-- An average of values at most one is at most one. -/
theorem avgE_le_one {f : E → ℝ≥0∞} (h : ∀ x, f x ≤ 1) : avgE f ≤ 1 := avgE_le_of_le h

/-- An average of indicators is at most one. -/
theorem avgE_indE_le_one (p : E → Prop) : avgE (fun x ↦ indE (p x)) ≤ 1 :=
  avgE_le_one fun x ↦ indE_le_one (p x)

/-- The average grows with the function. -/
theorem avgE_mono {f g : E → ℝ≥0∞} (h : ∀ x, f x ≤ g x) : avgE f ≤ avgE g := by
  unfold avgE
  gcongr with x
  exact h x

/-- The average of the indicator of an event is its uniform probability, as a count (lvm: leanVM
states it as VCVio's `Pr{let c ← $ᵗ E}[p c]`; the count is that probability's
`SampleableType.prEvent_uniformSample` form). -/
theorem avgE_indE_eq_card (p : E → Prop) [DecidablePred p] :
    avgE (fun x ↦ indE (p x)) =
      ((Finset.univ.filter p).card : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [avgE, div_eq_mul_inv, mul_comm]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  unfold indE
  by_cases h : p c <;> simp [h]

/-- The average is additive over a finite sum. -/
private theorem avgE_finset_sum {β : Type} (s : Finset β) (f : β → E → ℝ≥0∞) :
    avgE (fun x ↦ ∑ b ∈ s, f b x) = ∑ b ∈ s, avgE (f b) := by
  unfold avgE
  rw [Finset.sum_comm, Finset.mul_sum]

/-- **The union bound over candidates.** If each of at most `L₀` candidates satisfies an event
with average at most `ε`, some candidate satisfies it with average at most `L₀ · ε`. -/
theorem avgE_indE_exists_le {β : Type} {C : Set β} (hfin : C.Finite) {L₀ : ℕ}
    (hcard : C.ncard ≤ L₀) {P : β → E → Prop} {ε : ℝ≥0∞}
    (h : ∀ q ∈ C, avgE (fun x ↦ indE (P q x)) ≤ ε) :
    avgE (fun x ↦ indE (∃ q ∈ C, P q x)) ≤ L₀ * ε := by
  classical
  let s := hfin.toFinset
  have hpt : ∀ x, indE (∃ q ∈ C, P q x) ≤ ∑ q ∈ s, indE (P q x) := fun x ↦ by
    by_cases hx : ∃ q ∈ C, P q x
    · obtain ⟨q, hq, hP⟩ := hx
      rw [indE_of ⟨q, hq, hP⟩]
      calc (1 : ℝ≥0∞) = indE (P q x) := (indE_of hP).symm
        _ ≤ ∑ q ∈ s, indE (P q x) :=
          Finset.single_le_sum (f := fun q ↦ indE (P q x)) (fun _ _ ↦ zero_le)
            (hfin.mem_toFinset.mpr hq)
    · rw [indE_of_not hx]
      exact zero_le
  calc avgE (fun x ↦ indE (∃ q ∈ C, P q x))
      ≤ avgE (fun x ↦ ∑ q ∈ s, indE (P q x)) := avgE_mono hpt
    _ = ∑ q ∈ s, avgE (fun x ↦ indE (P q x)) := avgE_finset_sum s _
    _ ≤ ∑ _q ∈ s, ε := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * ε := by
      gcongr
      rw [← Set.ncard_eq_toFinset_card C hfin]
      exact_mod_cast hcard

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontEscape` =====

/-!
# Doom over candidates

The front phases' doom is that no candidate of the level-0 commitment is *alive*: no candidate is
in the phase's ArkLib knowledge state at the decoded transcript (`Doomed C A h`, `C h` the
candidates the history `h` binds). Along a phase's local run the history gains no commitment, and
the candidates do not change (`Stable`).

* `doomRead`, `doomReadN`: a prover's scalars keep doom, with the alive predicate unchanged (the
  ArkLib phase's `toFun_next` is applied where the next challenge is bounded, not at the read).
* `doomSample`: a challenge escapes doom with average at most `L₀ · e` when it escapes for each
  candidate with average at most `e` (the ArkLib phase's worst-case per-challenge bound) and there
  are at most `L₀` candidates.
* `doomSampleN`: `n` challenges in a row, the alive predicate on the challenges so far, with
  per-challenge bounds `e i`: lead `Σ_i L₀ · e i` plus the follower's.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile
open scoped ENNReal

section

variable {β : Type}

/-- No candidate the history binds is alive. -/
def Doomed (C : List Ev → Set β) (A : β → Prop) (h : List Ev) : Prop := ∀ q ∈ C h, ¬ A q

/-- The candidates a history binds do not change along a run with no commitment. -/
def Stable (C : List Ev → Set β) : Prop := ∀ h₀ l, commits l = [] → C (h₀ ++ l) = C h₀

/-- Doom for a predicate gives doom for a stronger one. -/
theorem Doomed.mono {C : List Ev → Set β} {A A' : β → Prop} {h : List Ev}
    (hd : Doomed C A h) (hA : ∀ q, A' q → A q) : Doomed C A' h :=
  fun q hq ha ↦ hd q hq (hA q ha)

/-- Doom is the same after a run with no commitment. -/
theorem Doomed.append {C : List Ev → Set β} (hst : Stable C) {A : β → Prop} {h₀ l : List Ev}
    (hl : commits l = []) : Doomed C A (h₀ ++ l) ↔ Doomed C A h₀ := by
  unfold Doomed
  rw [hst h₀ l hl]

/-- The average over a challenge of the indicator of an event, as the calculus counts it. -/
theorem card_filter_eq_avgE (p : E → Prop) [DecidablePred p] :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter p).card : ℝ≥0∞) =
      avgE fun c ↦ indE (p c) := by
  rw [avgE_indE_eq_card, div_eq_mul_inv, mul_comm]

variable {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-! ## Reads -/

/-- A prover's scalar keeps doom. -/
noncomputable def doomRead (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    Spec VerifierProgram.readScalar (Doomed C A) (fun _ h ↦ Doomed C A h) εmax 0 T :=
  Spec.readE (fun _ _ hd ↦ (Doomed.append hst rfl).mpr hd) hT

/-- `n` prover scalars keep doom; the lead is `0` after at least one. -/
noncomputable def doomReadN (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (VerifierProgram.readScalars (n + 1)) (Doomed C A)
      (fun xs h ↦ xs.length = n + 1 ∧ Doomed C A h) εmax 0 T
  | 0 => (doomRead hst A hT).bind' fun x ↦
      (Spec.ret (Post := fun xs h ↦ xs = [] ∧ Doomed C A h) []).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl
  | n + 1 => (doomRead hst A (zero_le.trans (zero_le.trans le_rfl))).mono (fun _ h ↦ h)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun x ↦
        (doomReadN hst A hT n).bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl

/-! ## Samples -/

variable [Finite β] {L₀ : ℕ}

/-- **A challenge escapes doom** with average at most `L₀ · e`: for each candidate not alive, the
challenge makes it alive with average at most `e`. -/
noncomputable def doomSample (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (A : β → Prop) (A' : E → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → avgE (fun c ↦ indE (A' c q)) ≤ e) :
    Spec VerifierProgram.sampleChallenge (Doomed C A) (fun c h ↦ Doomed C (A' c) h) εmax (L₀ * e +
        T) T := by
  classical
  refine Spec.sampleE (L₀ * e) fun h₀ hd ↦ ?_
  rw [card_filter_eq_avgE]
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
    (avgE_indE_exists_le (Set.toFinite (C h₀)) (hcard h₀) (P := fun q c ↦ A' c q)
      fun q hq ↦ hesc q (hd q hq))
  rw [Doomed.append hst rfl] at hc
  by_contra hn
  exact hc fun q hq ha ↦ hn ⟨q, hq, ha⟩

/-- **`n` challenges in a row**, the alive predicate on the challenges drawn so far after `acc`:
each challenge escapes with average at most `e` of the number drawn before it. -/
noncomputable def doomSampleN (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (A : List E → β → Prop) (e : ℕ → ℝ≥0∞)
    (hesc : ∀ acc q, ¬ A acc q → avgE (fun c ↦ indE (A (acc ++ [c]) q)) ≤ e acc.length) :
    (n : ℕ) → (acc : List E) →
      Spec (VerifierProgram.sampleChallenges n) (Doomed C (A acc))
        (fun l h ↦ l.length = n ∧ Doomed C (A (acc ++ l)) h) εmax
        ((∑ i ∈ Finset.range n, L₀ * e (acc.length + i)) + T) T
  | 0, acc => (Spec.ret []).mono (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl
      (by simp) le_rfl
  | n + 1, acc =>
    ((doomSample (εmax := εmax) (T := (∑ i ∈ Finset.range n, L₀ * e (acc.length + 1 + i)) + T)
        hst hcard (A acc) (fun c ↦ A (acc ++ [c])) (e acc.length)
        (fun q hq ↦ hesc acc q hq)).bind' fun c ↦
      (doomSampleN hst hcard A e hesc n (acc ++ [c])).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
        (by simp [add_assoc]) le_rfl |>.bind' fun cs ↦
          (Spec.ret (c :: cs)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
      (by
        rw [Finset.sum_range_succ', add_zero, ← add_assoc, add_comm (L₀ * e acc.length)]
        gcongr with i hi
        exact le_of_eq (by rw [add_assoc, add_comm 1 i]))
      le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
