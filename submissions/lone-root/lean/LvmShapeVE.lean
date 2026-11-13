-- New for lvm2 (CR-V): auxiliary lemmas for `LvmShape`'s relocation (`holds_onStackZ`,
-- `isMultiaffine_onStackZ`, `onStackZB_eq`) and the `SCRel` transfer.
import LvmShapeVN
import LvmVEqRel
import LvmVEqClaims
import LvmWhirSumcheck

set_option autoImplicit false

namespace Lvm.Shape

open Lvm.VEq

/-! ## Skipping regions (`onStackZB_eq`) -/

theorem eqEvalF_eq_zero {l r : List FE} (j : ℕ) (hl : j < l.length) (hr : j < r.length)
    (h : 1 + l[j] + r[j] = 0) : Lvm.eqEval l r = 0 := by
  unfold Lvm.eqEval
  rw [← List.prod_eq_foldl]
  apply List.prod_eq_zero
  rw [List.mem_iff_getElem]
  exact ⟨j, by simp [hl, hr], by simp [List.getElem_zipWith, h]⟩

theorem getElem_selectorPointF (s n j : ℕ) (h : j < (Lvm.selectorPoint s n).length) :
    (Lvm.selectorPoint s n)[j] = Lvm.eOfNat ((s >>> j) % 2) := by
  simp [Lvm.selectorPoint]

theorem length_selectorPointF (s n : ℕ) : (Lvm.selectorPoint s n).length = n := by
  simp [Lvm.selectorPoint]

theorem one_add_eOfNat_bits {a b : ℕ} (h : a % 2 ≠ b % 2) :
    1 + Lvm.eOfNat (a % 2) + Lvm.eOfNat (b % 2) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp only [ha, hb] at h ⊢ <;>
    first | exact absurd rfl h | decide

theorem testBit_lt_two_pow {i n p : ℕ} (hi : i < 2 ^ n) (hp : n ≤ p) : i.testBit p = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hp))

/-- Two aligned disjoint windows below `2^24` differ in a bit at or above both. -/
theorem exists_bit_ne {v i k o : ℕ} (hiv : i % 2 ^ v = 0) (hi : i < 2 ^ 24) (hok : o % 2 ^ k = 0)
    (ho : o < 2 ^ 24) (hm : ¬ (i < o + 2 ^ k ∧ o < i + 2 ^ v)) :
    ∃ p, v ≤ p ∧ k ≤ p ∧ p < 24 ∧ (i >>> p) % 2 ≠ (o >>> p) % 2 := by
  by_contra hne
  push Not at hne
  have hsh : i >>> max v k = o >>> max v k := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    by_cases hj : max v k + j < 24
    · have := hne (max v k + j) (by omega) (by omega) hj
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at this
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, this]
    · rw [testBit_lt_two_pow hi (by omega), testBit_lt_two_pow ho (by omega)]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hsh
  apply hm
  rcases le_total v k with hvk | hvk
  · rw [max_eq_right hvk] at hsh
    have e1 := Nat.div_add_mod i (2 ^ k)
    have e2 := Nat.div_add_mod o (2 ^ k)
    have e3 := Nat.mod_lt i (Nat.two_pow_pos k)
    have : 0 < 2 ^ v := Nat.two_pow_pos v
    rw [hsh] at e1
    omega
  · rw [max_eq_left hvk] at hsh
    have e1 := Nat.div_add_mod i (2 ^ v)
    have e2 := Nat.div_add_mod o (2 ^ v)
    have e3 := Nat.mod_lt o (Nat.two_pow_pos v)
    have : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [hsh] at e1
    omega

theorem regions_facts : ∀ r ∈ regions, (r.1 = 18 ∨ r.1 = 20) ∧ r.2.1 % 2 ^ r.1 = 0 ∧
    r.2.1 + 2 ^ r.1 ≤ 2 ^ 23 := by
  decide +kernel

theorem length_relocF (x : List FE) (r : ℕ × ℕ × ℕ) (hr : r.1 ≤ 22) : (relocF x r).length = 23 := by
  simp [relocF, length_selectorPointF, CMain.nu20, sLog, CMain.nu20s]
  omega

theorem eqAbove_relocF_eq_zero (b : Lvm.Placement) (hb : InStack b) (x : List FE) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ regions) (hm : meets b r = false) : b.eqAbove (relocF x r) = 0 := by
  obtain ⟨hk, ho, hoe⟩ := regions_facts r hr
  obtain ⟨hv, hiv, hi⟩ := hb
  have hk22 : r.1 ≤ 22 := by omega
  have hi23 : b.index < 2 ^ 23 := by simpa [CMain.nu20] using hi
  have ho23 : r.2.1 < 2 ^ 23 := by have : 0 < 2 ^ r.1 := Nat.two_pow_pos _; omega
  have hm' : ¬ (b.index < r.2.1 + 2 ^ r.1 ∧ r.2.1 < b.index + 2 ^ b.variableCount) := by
    simpa [meets] using hm
  obtain ⟨p, hpv, hpk, hp, hne⟩ := exists_bit_ne hiv (by omega) ho (by omega) hm'
  -- both windows lie below `2^23`, so the differing bit is below `ν = 23`
  have hp23 : p < 23 := by
    by_contra hc
    apply hne
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (lt_of_lt_of_le hi23 (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.div_eq_of_lt (lt_of_lt_of_le ho23 (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  have hlen := length_relocF x r hk22
  unfold Lvm.Placement.eqAbove
  apply eqEvalF_eq_zero (p - b.variableCount)
    (by rw [length_selectorPointF, hlen]; omega) (by rw [List.length_drop, hlen]; omega)
  rw [getElem_selectorPointF, List.getElem_drop]
  have hreloc : (relocF x r)[b.variableCount + (p - b.variableCount)]'(by omega) =
      Lvm.eOfNat ((r.2.1 >>> p) % 2) := by
    unfold relocF
    rw [List.getElem_append_right (by simp; omega)]
    rw [getElem_selectorPointF]
    congr 2
    rw [← Nat.shiftRight_add]
    congr 1
    simp only [List.length_take, List.length_append, List.length_replicate, List.length_tail]
    simp only [sLog, CMain.nu20s] at *; omega
  rw [hreloc, ← Nat.shiftRight_add]
  have : b.variableCount + (p - b.variableCount) = p := by omega
  rw [this]
  exact one_add_eOfNat_bits hne

theorem sum_filter_eq {α : Type*} (L : List α) (P : α → Bool) (f : α → FE)
    (h : ∀ a ∈ L, P a = false → f a = 0) : ((L.filter P).map f).sum = (L.map f).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih' := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    by_cases hP : P a = true
    · simp [hP, ih']
    · simp [hP, ih', h a List.mem_cons_self (by simpa using hP)]

/-! ## Transfer helpers -/

theorem headD_map_toExt3 (xs : List FE) : (xs.map FE.toExt3).headD 0 = FE.toExt3 (xs.headD 0) := by
  cases xs <;> simp

theorem forall₂_main_map {l : List (Com × Lvm.BlockClaim × FE)} {l' : List (Com × BClaim)}
    (h : List.Forall₂ CRel (l.map fun e ↦ (e.1, e.2.1)) l') (F : Lvm.BlockClaim × FE → Lvm.StackClaim)
    (G : BClaim → VStackClaim)
    (hFG : ∀ e ∈ l, e.1 = .main → ∀ b, BCRel e.2.1 b → SCRel (F e.2) (G b)) :
    List.Forall₂ SCRel (((l.filter (·.1 == .main)).map (·.2)).map F)
      (((l'.filter (·.1 == .main)).map (·.2)).map G) := by
  induction l generalizing l' with
  | nil => cases h; exact .nil
  | cons e l ih =>
    cases h with
    | cons hab hrest =>
      rename_i b l''
      obtain ⟨h1, h2⟩ := hab
      have ih' := ih hrest fun e' he' ↦ hFG e' (List.mem_cons_of_mem _ he')
      by_cases hc : (e.1 == Com.main) = true
      · have hb : (b.1 == Com.main) = true := by rw [← h1]; exact hc
        simp only [List.filter_cons, hc, hb, ↓reduceIte, List.map_cons]
        exact .cons (hFG e List.mem_cons_self (by simpa using hc) b.2 h2) ih'
      · have hb : ¬ (b.1 == Com.main) = true := by rw [← h1]; exact hc
        simp only [List.filter_cons, hc, hb, Bool.false_eq_true, ↓reduceIte]
        exact ih'

/-! ## Sums for `holds_onStackZ` -/

section Sums

open Finset

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ,
      add_assoc]

theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    ∑ a ∈ range (m * n), f a = ∑ i ∈ range m, ∑ u ∈ range n, f (i * n + u) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem sum_window {M : Type*} [AddCommMonoid M] (G : ℕ → M) {k os N : ℕ} (hal : os % 2 ^ k = 0)
    (hfit : os + 2 ^ k ≤ N) :
    ∑ j ∈ range N, (if j / 2 ^ k = os / 2 ^ k then G j else 0) = ∑ u ∈ range (2 ^ k), G (os + u) := by
  rw [sum_ite, sum_const_zero, add_zero]
  have hP := Nat.two_pow_pos k
  have hos := Nat.div_add_mod os (2 ^ k)
  rw [hal, add_zero] at hos
  have e : (range N).filter (fun j ↦ j / 2 ^ k = os / 2 ^ k) = Ico os (os + 2 ^ k) := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    constructor
    · rintro ⟨hj, he⟩
      have h1 := Nat.div_add_mod j (2 ^ k)
      have h2 := Nat.mod_lt j hP
      rw [he] at h1
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, Nat.div_eq_of_lt_le ?_ ?_⟩
      · rw [Nat.mul_comm]; omega
      · rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega
  rw [e, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

theorem sum_list_sum_comm {α M : Type*} [AddCommMonoid M] (L : List α) (s : Finset ℕ) (g : α → ℕ → M) :
    ∑ j ∈ s, (L.map fun r ↦ g r j).sum = (L.map fun r ↦ ∑ j ∈ s, g r j).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]

theorem list_sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem sum_regions {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ × ℕ → M) :
    (regions.map g).sum = ∑ l ∈ range 4, g (18, l * 2 ^ 20, l * 2 ^ 18) +
      ∑ j ∈ range 3, g (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20) := by
  rw [regions, List.map_append, List.sum_append, List.map_map, List.map_map, list_sum_range',
    list_sum_range']
  rfl

theorem regions_small : ∀ r ∈ regions, r.2.2 % 2 ^ r.1 = 0 ∧ r.2.2 + 2 ^ r.1 ≤ 2 ^ 22 := by
  decide +kernel

theorem vector_getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {a : ℕ} (ha : a < n) :
    (Vector.ofFn f).getD a d = f ⟨a, ha⟩ := by
  unfold Vector.getD
  rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_ofFn]
  simp [ha]

end Sums

/-! ## Multiaffinity (`isMultiaffine_onStackZ`) -/

section Multiaffine

open LeanVM.Parameters LeanVM.Protocol.Whir.Sound

theorem isMultiaffine_congr {n : ℕ} {Φ Ψ : List E → E} (hΨ : IsMultiaffine n Ψ)
    (h : ∀ l : List E, l.length = n → Φ l = Ψ l) : IsMultiaffine n Φ := by
  intro l hl k hk X
  rw [h _ (by simp [hl]), h _ (by simp [hl]), h _ (by simp [hl])]
  exact hΨ l hl k hk X

theorem isMultiaffine_append_right {k n : ℕ} {Φ : List E → E} (hΦ : IsMultiaffine n Φ) (S : List E)
    (hS : k + S.length = n) : IsMultiaffine k fun m ↦ Φ (m ++ S) := by
  intro l hl i hi X
  have e : ∀ Y : E, l.set i Y ++ S = (l ++ S).set i Y := fun Y ↦ by
    simp [show i < l.length by omega]
  simp only [e]
  exact hΦ _ (by simp [hl, hS]) i (by omega) X

theorem isMultiaffine_list_sum {α : Type*} {n : ℕ} (L : List α) (Φs : α → List E → E)
    (h : ∀ a ∈ L, IsMultiaffine n (Φs a)) : IsMultiaffine n fun l ↦ (L.map fun a ↦ Φs a l).sum := by
  induction L with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

theorem isMultiaffine_headFactor (n : ℕ) : IsMultiaffine (n + 1) fun l : List E ↦ 1 - l.headD 0 := by
  intro l hl k hk X
  cases l with
  | nil => simp at hl
  | cons a l =>
    cases k with
    | zero => simp
    | succ k => simp; ring

end Multiaffine

end Lvm.Shape
