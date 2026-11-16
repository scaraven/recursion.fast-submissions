-- New for lvm2 S1 (E2-F, E2F-V): the wiring kernels' closed forms over a field `F` (`LvmWireKernel`'s
-- `sum_msK_zero`, `thrEval_eq`, `sum_range_iota_succ`), for `LvmE2VProg`'s `msEvalF`/`thrEvalF` at `E2`.
import LvmE2VProg
import LvmE2VWireAlg

/-!
# The wiring kernels over `F`

`LvmWireKernel`'s automata, read over a field `F` (the evaluators `msEvalF`, `thrEvalF` of
`LvmE2VProg`):
* `msTailF_get`, `thrTailF_get`: what the automata compute (`msSemF`, `thrSemF`);
* **`sum_msKF_zero`**: `Σ_{x<2^w} eq(σ, x)·ι(x + 1)·[x + 1 ≤ t] = msEvalF ρ μ σ 0 t`;
* **`thrEvalF_eq`**, **`sum_range_iotaF_succ`**: `Σ_{i ≤ t} ι(i) = thrEvalF ρ μ t`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters Finset
open Lvm.WK (nextS le_iff_nextS)

section

variable {F : Type} [Field F]

/-- `a·b` indices, the high one outside. -/
theorem sum_range_mulB {M : Type*} [AddCommMonoid M] (a b : ℕ) (G : ℕ → M) :
    ∑ p ∈ range (a * b), G p = ∑ i ∈ range a, ∑ k ∈ range b, G (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

/-- `MS`'s kernel on the cube: `ι(base + x + 1)·[x + 1 ≤ t]`. -/
def msKF (ρ μ : List F) (base t x : ℕ) : F := if x + 1 ≤ t then iotaF ρ μ (base + x + 1) else 0

/-- What `msTailF σ ρ t` computes in state `(c, s)`. -/
def msSemF (σ ρ : List F) (c s : Bool) (t : ℕ) : F :=
  ∑ x ∈ range (2 ^ σ.length),
    if x + c.toNat < 2 ^ σ.length ∧ x + c.toNat + s.toNat ≤ t then eqAtF σ x * eqAtF ρ (x + c.toNat)
    else 0

/-- What `thrTailF ρ t` computes in state `s`. -/
def thrSemF (ρ : List F) (s : Bool) (t : ℕ) : F :=
  ∑ y ∈ range (2 ^ ρ.length), if y + s.toNat ≤ t then eqAtF ρ y else 0

theorem eqAtF_cons_bit (r : F) (ρ : List F) (y : ℕ) (b : Bool) :
    eqAtF (r :: ρ) (2 * y + b.toNat) = eqBitF r b * eqAtF ρ y := by
  cases b
  · rw [Bool.toNat_false, add_zero, eqAtF_succ, if_neg (by (clear * - y; omega)), show 2 * y / 2 = y by (clear * - y; omega)]; rfl
  · rw [Bool.toNat_true, eqAtF_succ, if_pos (by (clear * - y; omega)), show (2 * y + 1) / 2 = y by (clear * - y; omega)]; rfl

theorem ite_mul_congrF {P Q : Prop} [Decidable P] [Decidable Q] (hPQ : P ↔ Q) (X Y k : F)
    (hXY : X = k * Y) : (if P then X else 0) = k * (if Q then Y else 0) := by
  by_cases hq : Q
  · rw [if_pos (hPQ.2 hq), if_pos hq, hXY]
  · rw [if_neg (fun hp ↦ hq (hPQ.1 hp)), if_neg hq, mul_zero]

theorem msStepF_get (a r : F) (tb : Bool) (q : MS4F F) (c s : Bool) :
    (msStepF a r tb q).get c s = eqBitF a false * eqBitF r c * q.get false (nextS c s tb) +
      eqBitF a true * eqBitF r (!c) * q.get c (nextS (!c) s tb) := by
  cases c <;> cases s <;> rfl

theorem msSemF_term (a r : F) (σ ρ : List F) (n y t : ℕ) (b c s : Bool) :
    (if 2 * y + b.toNat + c.toNat < 2 ^ (n + 1) ∧ 2 * y + b.toNat + c.toNat + s.toNat ≤ t then
        eqAtF (a :: σ) (2 * y + b.toNat) * eqAtF (r :: ρ) (2 * y + b.toNat + c.toNat) else 0) =
      eqBitF a b * eqBitF r (b ^^ c) *
        (if y + (b && c).toNat < 2 ^ n ∧
            y + (b && c).toNat + (nextS (b ^^ c) s (t % 2 == 1)).toNat ≤ t / 2 then
          eqAtF σ y * eqAtF ρ (y + (b && c).toNat) else 0) := by
  have hsplit : 2 * y + b.toNat + c.toNat = 2 * (y + (b && c).toNat) + (b ^^ c).toNat := by
    cases b <;> cases c <;> simp <;> (clear * - y; omega)
  refine ite_mul_congrF ?_ _ _ _ ?_
  · rw [hsplit, add_assoc, ← le_iff_nextS, pow_succ]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨by cases b <;> cases c <;> simp at h1 ⊢ <;> (clear * - y n t s h1; omega), by (clear * - y b c s t n h2; omega)⟩
    · rintro ⟨h1, h2⟩; refine ⟨by cases b <;> cases c <;> simp at h1 ⊢ <;> (clear * - y n t s h1; omega), by (clear * - y b c s t n h2; omega)⟩
  · rw [hsplit, eqAtF_cons_bit, eqAtF_cons_bit]
    ring

theorem msTailF_get : ∀ (σ ρ : List F), σ.length = ρ.length → ∀ (t : ℕ) (c s : Bool),
    (msTailF σ ρ t).get c s = msSemF σ ρ c s t
  | [], [], _, t, c, s => by
    cases c <;> cases s <;>
      simp only [msTailF, MS4F.get, msSemF, List.length_nil, pow_zero, Finset.sum_range_one,
        eqAtF_nil, mul_one, Bool.toNat_false, Bool.toNat_true, zero_add, add_zero] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: σ, r :: ρ, h, t, c, s => by
    have h' : σ.length = ρ.length := by simpa using h
    rw [msTailF, msStepF_get, msTailF_get σ ρ h' (t / 2), msTailF_get σ ρ h' (t / 2), msSemF, msSemF,
      msSemF, List.length_cons, sum_cube_succW, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun y _ ↦ ?_) (Finset.sum_congr rfl fun y _ ↦ ?_)
    · have := msSemF_term a r σ ρ σ.length y t false c s
      simp only [Bool.toNat_false, add_zero, Bool.false_xor, Bool.false_and] at this
      rw [this]; simp only [Bool.toNat_false, add_zero]
    · have := msSemF_term a r σ ρ σ.length y t true c s
      simp only [Bool.toNat_true, Bool.true_xor, Bool.true_and] at this
      rw [this]

theorem thrTailF_get : ∀ (ρ : List F) (t : ℕ) (s : Bool),
    (if s then (thrTailF ρ t).2 else (thrTailF ρ t).1) = thrSemF ρ s t
  | [], t, s => by
    cases s <;>
      simp only [thrTailF, thrSemF, List.length_nil, pow_zero, Finset.sum_range_one, eqAtF_nil,
        Bool.toNat_false, Bool.toNat_true, zero_add, add_zero, ite_true, ite_false] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  | r :: ρ, t, s => by
    have ih := thrTailF_get ρ (t / 2)
    have hterm : ∀ (y : ℕ) (y0 : Bool), (if 2 * y + y0.toNat + s.toNat ≤ t then
        eqAtF (r :: ρ) (2 * y + y0.toNat) else 0) =
        eqBitF r y0 * (if y + (nextS y0 s (t % 2 == 1)).toNat ≤ t / 2 then eqAtF ρ y else 0) :=
      fun y y0 ↦ ite_mul_congrF (le_iff_nextS y0 s y t) _ _ _ (eqAtF_cons_bit r ρ y y0)
    have e0 := ih (nextS false s (t % 2 == 1))
    have e1 := ih (nextS true s (t % 2 == 1))
    rw [thrSemF, List.length_cons, sum_cube_succW, Finset.sum_add_distrib]
    have h0 : ∀ y, (if 2 * y + s.toNat ≤ t then eqAtF (r :: ρ) (2 * y) else 0) =
        eqBitF r false * (if y + (nextS false s (t % 2 == 1)).toNat ≤ t / 2 then eqAtF ρ y else 0) := by
      intro y; have := hterm y false; simpa using this
    have h1 : ∀ y, (if 2 * y + 1 + s.toNat ≤ t then eqAtF (r :: ρ) (2 * y + 1) else 0) =
        eqBitF r true * (if y + (nextS true s (t % 2 == 1)).toNat ≤ t / 2 then eqAtF ρ y else 0) := by
      intro y; have := hterm y true; simpa using this
    simp only [h0, h1, ← Finset.mul_sum]
    rw [← thrSemF, ← thrSemF, ← e0, ← e1]
    cases s <;> simp only [thrTailF, eqBitF] <;> simp

/-- `ι` at a row of an aligned block. -/
theorem iotaF_block (ρ μ : List F) (w base y : ℕ) (h4 : 4 ≤ w) (hρ : w - 4 ≤ ρ.length)
    (hb : 2 ^ w ∣ base) (hy : y < 2 ^ w) :
    iotaF ρ μ (base + y) =
      eqAtF (ρ.take (w - 4)) (y / 16) * μ.getD (y % 16) 0 * eqAtF (ρ.drop (w - 4)) (base / 2 ^ w) := by
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 4 := ⟨w - 4, by (clear * - w F ρ y h4; omega)⟩
  rw [Nat.add_sub_cancel] at hρ ⊢
  have hP : 0 < 2 ^ v := Nat.two_pow_pos v
  have h16 : 2 ^ (v + 4) = 16 * 2 ^ v := by rw [pow_add]; ring
  have hz : y / 16 < 2 ^ v := by (clear * - y v F ρ hy h16; omega)
  have hlen : (ρ.take v).length = v := by simp; (clear * - hρ; omega)
  have hsplit : 2 ^ (v + 4) * k + y = 16 * (2 ^ v * k) + y := by rw [h16]; ring
  have e1 : (2 ^ (v + 4) * k + y) / 16 = 2 ^ v * k + y / 16 := by rw [hsplit]; (clear * - v k y F ρ; omega)
  have e3 : (2 ^ (v + 4) * k + y) % 16 = y % 16 := by rw [hsplit]; (clear * - v k y F ρ e1; omega)
  have e2 : (2 ^ v * k + y / 16) % 2 ^ v = y / 16 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hz]
  have e4 : (2 ^ v * k + y / 16) / 2 ^ v = k := by
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt hz, add_zero]
  have e5 : 2 ^ (v + 4) * k / 2 ^ (v + 4) = k := Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)
  rw [iotaF, e1, e3, e5]
  conv_lhs => rw [← List.take_append_drop v ρ]
  rw [eqAtF_append, hlen, eqAtF_mod (ρ.take v), hlen, e2, e4]
  ring

/-- **`MS`'s extension is the automaton.** -/
theorem sum_msKF (ρ μ σ : List F) (base t : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) (ht : t < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAtF σ x * msKF ρ μ base t x = msEvalF ρ μ σ base t := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 4 := ⟨σ.length - 4, by (clear * - F σ ρ base t h4; omega)⟩
  have hσh : (σ.drop 4).length = v := by simp; (clear * - F σ v ρ base t h4 hv; omega)
  have hσ4 : (σ.take 4).length = 4 := by simp; (clear * - h4; omega)
  have hρh : (ρ.take (σ.length - 4)).length = v := by simp; (clear * - F σ ρ v base t h4 hρ hv hσh; omega)
  have hpow : 2 ^ σ.length = 2 ^ v * 16 := by rw [hv, pow_add]; norm_num
  have key : ∀ d ∈ range 16, ∀ x' ∈ range (2 ^ v),
      eqAtF σ (16 * x' + d) * msKF ρ μ base t (16 * x' + d) =
        eqAtF (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length) *
          (eqAtF (σ.take 4) d * μ.getD ((d + 1) % 16) 0 *
            (if x' + (d == 15).toNat < 2 ^ v ∧
                x' + (d == 15).toNat + (decide (t % 16 < (d + 1) % 16)).toNat ≤ t / 16 then
              eqAtF (σ.drop 4) x' * eqAtF (ρ.take (σ.length - 4)) (x' + (d == 15).toNat) else 0)) := by
    intro d hd x' hx'
    have hd' := Finset.mem_range.1 hd
    have hx'' := Finset.mem_range.1 hx'
    have hes : eqAtF σ (16 * x' + d) = eqAtF (σ.take 4) d * eqAtF (σ.drop 4) x' := by
      conv_lhs => rw [← List.take_append_drop 4 σ]
      rw [eqAtF_append, hσ4, eqAtF_mod (σ.take 4), hσ4,
        show (16 * x' + d) % 2 ^ 4 = d by norm_num; (clear * - hd'; omega),
        show (16 * x' + d) / 2 ^ 4 = x' by norm_num; (clear * - x' d F ρ σ base t v hd'; omega)]
    have hcv : ((16 * x' + d + 1 ≤ t) ↔ (x' + (d == 15).toNat < 2 ^ v ∧
        x' + (d == 15).toNat + (decide (t % 16 < (d + 1) % 16)).toNat ≤ t / 16)) ∧
        (16 * x' + d + 1) / 16 = x' + (d == 15).toNat ∧ (16 * x' + d + 1) % 16 = (d + 1) % 16 := by
      rcases (show d = 15 ∨ d < 15 by (clear * - d F ρ σ base t v x' hd'; omega)) with h | h
      · subst h; simp; (clear * - x' t v F ρ σ base ht hpow hx''; omega)
      · have h15 : (d == 15) = false := by simp; (clear * - d F ρ σ base t v x' hd' h; omega)
        rw [h15, Nat.mod_eq_of_lt (show d + 1 < 16 by (clear * - d F ρ σ base t v x' hd' h; omega))]
        by_cases hs : t % 16 < d + 1 <;> simp [hs] <;> (clear * - x' d t v F ρ σ base hd' hx'' h hs; omega)
    rw [msKF]
    by_cases hc' : 16 * x' + d + 1 ≤ t
    · rw [if_pos hc', if_pos (hcv.1.1 hc'),
        show base + (16 * x' + d) + 1 = base + (16 * x' + d + 1) by ring,
        iotaF_block ρ μ σ.length base _ h4 hρ hb (by (clear * - x' d F σ ρ base t ht v hpow hcv hc'; omega)), hcv.2.1, hcv.2.2, hes]
      ring
    · rw [if_neg hc', if_neg (fun h ↦ hc' (hcv.1.2 h))]
      ring
  have hq : ∀ c s, (msTailF (σ.drop 4) (ρ.take (σ.length - 4)) (t / 16)).get c s =
      msSemF (σ.drop 4) (ρ.take (σ.length - 4)) c s (t / 16) :=
    msTailF_get _ _ (by rw [hσh, hρh]) _
  simp only [msEvalF]
  rw [sumF_map_range]
  conv_lhs => rw [hpow, sum_range_mulB]
  simp only [hq, msSemF, hσh, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun x' hx' ↦ key d hd x' hx'

/-- `sum_msKF` at `base = 0` (`K̃_ch(σ)`). -/
theorem sum_msKF_zero (ρ μ σ : List F) (t : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (ht : t < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAtF σ x * msKF ρ μ 0 t x = msEvalF ρ μ σ 0 t :=
  sum_msKF ρ μ σ 0 t h4 hρ (dvd_zero _) ht

/-- **The threshold sum** `Σ_{i ≤ t} ι(i)` is the two-state automaton. -/
theorem thrEvalF_eq (ρ μ : List F) (t : ℕ) (ht : t < 2 ^ (ρ.length + 4)) :
    ∑ i ∈ range (t + 1), iotaF ρ μ i = thrEvalF ρ μ t := by
  have hpow : 2 ^ (ρ.length + 4) = 2 ^ ρ.length * 16 := by rw [pow_add]; norm_num
  have hsub : range (t + 1) ⊆ range (2 ^ (ρ.length + 4)) := Finset.range_subset_range.2 (by (clear * - t F ρ ht hpow; omega))
  have h1 : ∑ i ∈ range (t + 1), iotaF ρ μ i =
      ∑ i ∈ range (2 ^ (ρ.length + 4)), if i ≤ t then iotaF ρ μ i else 0 := by
    rw [← Finset.sum_subset hsub (fun x _ hx ↦ by rw [if_neg (by simp at hx; (clear * - x t F ρ hx; omega))])]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [if_pos (by simp at hi; (clear * - hi; omega))]
  rw [h1, hpow, sum_range_mulB, Finset.sum_comm]
  simp only [thrEvalF]
  rw [sumF_map_range]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Finset.mem_range.1 hd
  have hq : (if t % 16 < d then (thrTailF ρ (t / 16)).2 else (thrTailF ρ (t / 16)).1) =
      thrSemF ρ (decide (t % 16 < d)) (t / 16) := by
    rw [← thrTailF_get ρ (t / 16) (decide (t % 16 < d))]
    simp
  rw [hq, thrSemF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [iotaF, show (16 * y + d) / 16 = y by (clear * - y d F ρ t hd'; omega), show (16 * y + d) % 16 = d by (clear * - y d F ρ t hd'; omega), mul_ite,
    mul_zero]
  by_cases hs : t % 16 < d
  · simp only [hs, decide_true, Bool.toNat_true]
    split_ifs <;> first | (exfalso; omega) | ring
  · simp only [hs, decide_false, Bool.toNat_false, add_zero]
    split_ifs <;> first | (exfalso; omega) | ring

/-- `Σ_{i=1}^{t} ι(i) = thrEvalF − ι(0)`. -/
theorem sum_range_iotaF_succ (ρ μ : List F) (t : ℕ) (ht : t < 2 ^ (ρ.length + 4)) :
    ∑ i ∈ range t, iotaF ρ μ (i + 1) = thrEvalF ρ μ t - iotaF ρ μ 0 := by
  rw [← thrEvalF_eq ρ μ t ht, Finset.sum_range_succ']
  ring

end

end Lvm.E2V
