-- New for lvm2 S1 (E2-F, E2F-V): the multilinear zero test at `E2` (`LvmKeccakCandidate`'s `foldT`/`ZeroOn`
-- and `LvmKeccakCallerRing`'s `zeroSpec`), generic in the field where the algebra allows, its coordinates
-- ground challenges (`coordG`) at `errG g 1` each.
import LvmE2VSample
import LvmE2VWireAlg

/-!
# The zero test at `E2`

* `foldTF δ acc v`: the table `δ` with its first `|acc|` coordinates bound to `acc` (`foldT`);
  `ZeroOnF δ acc n`: its extension on `n` bits is zero part-way (`ZeroOn`); `foldTF_snoc`,
  `zeroOnF_nil`, `zeroOnF_full` (any field `F`);
* `zeroOnF_affine`: a part-way extension that is not zero gives a nonzero affine polynomial vanishing
  at every coordinate that makes the next one zero (any field `F`);
* `zeroOnG_escape`: at `E2`, an accepted ground challenge makes it zero with probability `≤ errG g 1`;
* **`zeroSpecE2`** (the twin of `zeroSpec`): `m + 1 ≤ n` ground coordinates (`e2Samples g (m + 1)`),
  from doom of `ZeroOnF δ [] n ∧ R` to doom of `ZeroOnF δ pt n ∧ R`; lead `0`, each group
  `L₀ · errG g 1 + T ≤ εmax`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Polynomial Finset
open scoped ENNReal

section Field

variable {F : Type} [Field F]

/-- The table `δ` with its first `|acc|` coordinates bound to `acc`, at the remaining index `v`. -/
def foldTF (δ : ℕ → F) (acc : List F) (v : ℕ) : F :=
  ∑ w ∈ range (2 ^ acc.length), eqAtF acc w * δ (w + 2 ^ acc.length * v)

/-- The multilinear extension of `δ` on `n` bits, its first coordinates bound to `acc`, is
identically zero. -/
def ZeroOnF (δ : ℕ → F) (acc : List F) (n : ℕ) : Prop :=
  ∀ v < 2 ^ (n - acc.length), foldTF δ acc v = 0

theorem foldTF_nil (δ : ℕ → F) (v : ℕ) : foldTF δ [] v = δ v := by simp [foldTF]

theorem foldTF_snoc (δ : ℕ → F) (acc : List F) (c : F) (v : ℕ) :
    foldTF δ (acc ++ [c]) v = (1 + c) * foldTF δ acc (2 * v) + c * foldTF δ acc (2 * v + 1) := by
  unfold foldTF
  rw [List.length_append, List.length_singleton, pow_succ, sum_range_mulW (2 ^ acc.length) 2,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.mul_sum,
    Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    rw [show w + 2 ^ acc.length * 0 + 2 ^ acc.length * 2 * v = w + 2 ^ acc.length * (2 * v) by ring,
      Nat.mul_zero, Nat.add_zero, eqAtF_append, Nat.div_eq_of_lt hw', eqAtF_succ, eqAtF_nil]
    norm_num
    ring
  · refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    have hd : (w + 2 ^ acc.length * 1) / 2 ^ acc.length = 1 := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hw', zero_add]
    rw [show w + 2 ^ acc.length * 1 + 2 ^ acc.length * 2 * v =
      w + 2 ^ acc.length * (2 * v + 1) by ring, eqAtF_append, hd,
      eqAtF_mod acc (w + 2 ^ acc.length * 1), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw',
      eqAtF_succ, eqAtF_nil]
    norm_num
    ring

theorem zeroOnF_nil (δ : ℕ → F) (n : ℕ) : ZeroOnF δ [] n ↔ ∀ v < 2 ^ n, δ v = 0 := by
  simp [ZeroOnF, foldTF_nil]

theorem zeroOnF_full (δ : ℕ → F) {acc : List F} {n : ℕ} (h : acc.length = n) :
    ZeroOnF δ acc n ↔ ∑ w ∈ range (2 ^ n), eqAtF acc w * δ w = 0 := by
  rw [ZeroOnF, h, Nat.sub_self]
  simp [foldTF, h]

/-- **A nonzero part-way extension**: a nonzero polynomial of degree `≤ 1` vanishes at every
coordinate `c` that makes the next part-way extension zero. -/
theorem zeroOnF_affine (δ : ℕ → F) {n : ℕ} {acc : List F} (hacc : acc.length < n)
    (hne : ¬ ZeroOnF δ acc n) :
    ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ 1 ∧ ∀ c, ZeroOnF δ (acc ++ [c]) n → p.eval c = 0 := by
  obtain ⟨v, hv, hfv⟩ : ∃ v < 2 ^ (n - acc.length), foldTF δ acc v ≠ 0 := by
    by_contra hall
    exact hne fun v hv ↦ by_contra fun h0 ↦ hall ⟨v, hv, h0⟩
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by (clear * - n F acc hacc v; omega)
  have hv2 : v / 2 < 2 ^ (n - (acc.length + 1)) := by
    rw [hm, pow_succ] at hv; (clear * - v n F acc hv; omega)
  set a0 := foldTF δ acc (2 * (v / 2))
  set a1 := foldTF δ acc (2 * (v / 2) + 1)
  have hpair : ¬ (a0 = 0 ∧ a1 = 0) := by
    rintro ⟨h0, h1⟩
    rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv0
    · exact hfv (by rw [show v = 2 * (v / 2) by (clear * - v F n acc hv0; omega)]; exact h0)
    · exact hfv (by rw [show v = 2 * (v / 2) + 1 by (clear * - v F n acc hv0; omega)]; exact h1)
  refine ⟨C a0 + C (a0 + a1) * X, ?_, ?_, fun c hc ↦ ?_⟩
  · intro he
    refine hpair ⟨?_, ?_⟩
    · have := congrArg (coeff · 0) he; simpa using this
    · have h0 : a0 = 0 := by have := congrArg (coeff · 0) he; simpa using this
      have := congrArg (coeff · 1) he
      simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, one_ne_zero, ite_false,
        coeff_zero] at this
      rw [h0] at this
      simpa using this
  · exact natDegree_add_le_of_degree_le ((natDegree_C _).trans_le (by norm_num))
      ((natDegree_C_mul_le _ _).trans (by simp))
  · have := hc (v / 2) (by rw [List.length_append, List.length_singleton]; exact hv2)
    rw [foldTF_snoc] at this
    simp only [eval_add, eval_mul, eval_C, eval_X]
    rw [← this]
    ring

end Field

/-! ## At `E2` -/

/-- **The zero test's escape at `E2`**: an accepted ground challenge makes a nonzero part-way
extension zero with probability `≤ errG g 1`. -/
theorem zeroOnG_escape {g : ℕ} (hg : g ≤ 64) (δ : ℕ → E2) {n : ℕ} {acc : List E2}
    (hacc : acc.length < n) (hne : ¬ ZeroOnF δ acc n) :
    avgE (fun c ↦ indE (powOK g c ∧ ZeroOnF δ (acc ++ [e2OfE c]) n)) ≤ errG g 1 := by
  obtain ⟨p, hp0, hp1, hp⟩ := zeroOnF_affine δ hacc hne
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
    (sampleG_escape hg hp0 (q := 0) hp1 (by simp))
  rw [eval_zero]
  exact hp _ hc.2

/-- The zero test's alive predicate: at most `n` coordinates, the part-way extension zero, and `R`. -/
def ZeroAliveF {β : Type} (δ : β → ℕ → E2) (R : β → Prop) (n : ℕ) (acc : List E2) (q : β) : Prop :=
  acc.length ≤ n ∧ ZeroOnF (δ q) acc n ∧ R q

/-- **A zero-test coordinate's escape at `E2`**, carrying `R`. -/
theorem zeroAliveG_escape {g : ℕ} (hg : g ≤ 64) {β : Type} (δ : β → ℕ → E2) (R : β → Prop)
    (n : ℕ) (acc : List E2) (q : β) (hq : ¬ ZeroAliveF δ R n acc q) :
    avgE (fun c ↦ indE (powOK g c ∧ ZeroAliveF δ R n (acc ++ [e2OfE c]) q)) ≤ errG g 1 := by
  by_cases hl : acc.length < n
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, hc.2.2.1⟩).trans
        (zeroOnG_escape hg (δ q) hl fun hz ↦ hq ⟨hl.le, hz, hR⟩)
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ ?_).trans
      ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
    have := h.2.1
    rw [List.length_append, List.length_singleton] at this
    (clear * - g n acc hl this; omega)

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **`m + 1 ≤ n` zero-test coordinates at `E2`** (the twin of `zeroSpec`), carrying `R`: from doom of
`ZeroOnF δ [] n ∧ R` to doom of `ZeroOnF δ pt n ∧ R` at the `m + 1` ground challenges `pt`. Lead `0`
(every challenge follows its nonce); each group `L₀ · errG g 1 + T ≤ εmax`. -/
noncomputable def zeroSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ}
    (hg : g ≤ 64) (δ : β → ℕ → E2) (R : β → Prop) {n m : ℕ} (hm : m + 1 ≤ n)
    (he : (L₀ : ℝ≥0∞) * errG g 1 + T ≤ εmax) :
    Spec (e2Samples g (m + 1)) (Doomed C (fun q ↦ ZeroOnF (δ q) [] n ∧ R q))
      (fun pt hist ↦ pt.length = m + 1 ∧ Doomed C (fun q ↦ ZeroOnF (δ q) pt n ∧ R q) hist)
      εmax 0 T :=
  (coordGSpec hst hcard (ZeroAliveF δ R n) (errG g 1)
      (fun acc q hq ↦ zeroAliveG_escape hg δ R n acc q hq) he m []).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨_, hz, hR⟩ ↦ ⟨hz, hR⟩)
    (fun pt _ ⟨hl, hd⟩ ↦ ⟨hl, Doomed.mono hd fun _ ⟨hz, hR⟩ ↦
      ⟨by rw [List.nil_append, hl]; exact hm, by rwa [List.nil_append], hR⟩⟩)
    le_rfl le_rfl le_rfl

/-- **`zeroSpecE2`** as a statement. -/
theorem zeroE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ} (hg : g ≤ 64)
    (δ : β → ℕ → E2) (R : β → Prop) {n m : ℕ} (hm : m + 1 ≤ n)
    (he : (L₀ : ℝ≥0∞) * errG g 1 + T ≤ εmax) :
    Nonempty (Spec (e2Samples g (m + 1)) (Doomed C (fun q ↦ ZeroOnF (δ q) [] n ∧ R q))
      (fun pt hist ↦ pt.length = m + 1 ∧ Doomed C (fun q ↦ ZeroOnF (δ q) pt n ∧ R q) hist)
      εmax 0 T) :=
  ⟨zeroSpecE2 hst hcard hg δ R hm he⟩

end Lvm.E2V
