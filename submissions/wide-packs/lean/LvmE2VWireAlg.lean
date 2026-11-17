-- New for lvm2 S1 (E2-F, E2F-V): the multilinear algebra of the wiring and slot phases over a field `F`
-- (`LvmKeccakMultilinear`'s `eqAt`/`bitsE` lemmas, `LvmKeccakOpenOut`'s `cubeSum`/`col_split`, `LvmWireSpec`'s
-- slot family), generic in `F` for the `E2` front.
import LvmE2VBaseLemmas

/-!
# Equality weights, cube sums and slot families over `F`

* `eqAtF_mod`, `eqAtF_append`, `bitsF`, `sum_eqAtF_bitsF` (characteristic two);
* `cubeSumF`, `cube_plainFamilyF`, `polyLEF_eqAtF`, `polyLEF_mle`, `col_splitF`;
* the slot family `slotFF` (`slotFF_plain`, `slotFF_nil`, `slotFF_end`) and `slices_slotF`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters Polynomial Finset

section

variable {F : Type} [Field F]

/-! ## Lists and sums -/

theorem sumF_map_range (f : ℕ → F) (n : ℕ) : sumF ((List.range n).map f) = ∑ i ∈ range n, f i := by
  rw [sumF_eq_sum]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Finite sums of polynomial functions. -/
theorem PolyLEF.sum {d : ℕ} {ι : Type} (s : Finset ι) {G : ι → F → F}
    (h : ∀ i ∈ s, PolyLEF d (G i)) : PolyLEF d fun x ↦ ∑ i ∈ s, G i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (PolyLEF.const d 0).congr fun x ↦ by simp
  | insert a s ha ih =>
    refine (PolyLEF.add (h a (by simp)) (ih fun i hi ↦ h i (by simp [hi]))).congr fun x ↦ ?_
    rw [Finset.sum_insert ha]

/-- Sums over `2N` indices pair them. -/
theorem sum_range_two_mulW {M : Type*} [AddCommMonoid M] (G : ℕ → M) : ∀ N : ℕ,
    ∑ w ∈ range (2 * N), G w = ∑ w ∈ range N, (G (2 * w) + G (2 * w + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mulW G N, Finset.sum_range_succ, add_assoc]

theorem sum_cube_succW {M : Type*} [AddCommMonoid M] (m : ℕ) (G : ℕ → M) :
    ∑ w ∈ range (2 ^ (m + 1)), G w = ∑ w ∈ range (2 ^ m), (G (2 * w) + G (2 * w + 1)) := by
  rw [pow_succ, mul_comm, sum_range_two_mulW]

/-- A sum over `a·b` indices, the low `a` first. -/
theorem sum_range_mulW {M : Type*} [AddCommMonoid M] (a b : ℕ) (G : ℕ → M) :
    ∑ n ∈ range (a * b), G n = ∑ o ∈ range b, ∑ x ∈ range a, G (x + a * o) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ by rw [add_comm])

/-! ## Equality weights -/

@[simp] theorem eqAtF_nil (w : ℕ) : eqAtF ([] : List F) w = 1 := rfl

theorem eqAtF_succ (r : F) (rs : List F) (w : ℕ) :
    eqAtF (r :: rs) w = (if w % 2 = 1 then r else 1 + r) * eqAtF rs (w / 2) := rfl

/-- Only the low `|pt|` bits matter. -/
theorem eqAtF_mod : ∀ (pt : List F) (w : ℕ), eqAtF pt w = eqAtF pt (w % 2 ^ pt.length)
  | [], _ => rfl
  | r :: rs, w => by
    rw [eqAtF_succ, eqAtF_succ, List.length_cons, pow_succ, mul_comm (2 ^ rs.length) 2,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ← eqAtF_mod rs]

/-- A point split in two. -/
theorem eqAtF_append : ∀ (a b : List F) (w : ℕ),
    eqAtF (a ++ b) w = eqAtF a w * eqAtF b (w / 2 ^ a.length)
  | [], b, w => by simp
  | r :: a, b, w => by
    rw [List.cons_append, eqAtF_succ, eqAtF_succ, eqAtF_append a b, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm (2 ^ a.length) 2, mul_assoc]

/-- The cube point of index `z`, `m` coordinates, the lowest bit first. -/
def bitsF : ℕ → ℕ → List F
  | _, 0 => []
  | z, m + 1 => (if z % 2 = 1 then 1 else 0) :: bitsF (z / 2) m

@[simp] theorem bitsF_length : ∀ (z m : ℕ), (bitsF z m : List F).length = m
  | _, 0 => rfl
  | z, m + 1 => by simp [bitsF, bitsF_length (z / 2) m]

theorem bitsF_two_mul (z m : ℕ) : (bitsF (2 * z) (m + 1) : List F) = 0 :: bitsF z m := by
  simp [bitsF, Nat.mul_mod_right, Nat.mul_div_cancel_left z (by norm_num : 0 < 2)]

theorem bitsF_two_mul_add_one (z m : ℕ) : (bitsF (2 * z + 1) (m + 1) : List F) = 1 :: bitsF z m := by
  have h1 : (2 * z + 1) % 2 = 1 := by (clear * - z; omega)
  have h2 : (2 * z + 1) / 2 = z := by (clear * - z h1; omega)
  simp [bitsF, h1, h2]

/-- `selector_point` is the cube point of the selector. -/
theorem selPtF_eq_bitsF : ∀ (blk sb : ℕ), (selPtF blk sb : List F) = bitsF blk sb := by
  intro blk sb
  induction sb generalizing blk with
  | zero => rfl
  | succ n ih =>
    rw [bitsF, ← ih (blk / 2), selPtF, selPtF, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    simp only [List.map_inj_left, List.mem_range, Function.comp_apply]
    intro a _
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_succ']

/-- An equality weight is affine in each coordinate. -/
theorem polyLEF_eqAtF (pre post : List F) (w : ℕ) :
    PolyLEF 1 fun x ↦ eqAtF (pre ++ x :: post) w := by
  have h : ∀ x, eqAtF (pre ++ x :: post) w =
      eqAtF pre w * eqAtF post (w / 2 ^ pre.length / 2) *
        (if w / 2 ^ pre.length % 2 = 1 then x else 1 + x) := by
    intro x
    rw [eqAtF_append, eqAtF_succ]
    ring
  refine PolyLEF.congr ?_ fun x ↦ (h x).symm
  split_ifs
  · exact (PolyLEF.const_mul PolyLEF.id
      (eqAtF pre w * eqAtF post (w / 2 ^ pre.length / 2))).congr fun x ↦ rfl
  · exact (PolyLEF.const_mul (PolyLEF.affine 1 1)
      (eqAtF pre w * eqAtF post (w / 2 ^ pre.length / 2))).congr fun x ↦ by ring

/-- A multilinear extension is affine in each coordinate. -/
theorem polyLEF_mle (pre post : List F) (N : ℕ) (f : ℕ → F) :
    PolyLEF 1 fun x ↦ ∑ w ∈ range N, eqAtF (pre ++ x :: post) w * f w :=
  PolyLEF.sum _ fun w _ ↦ ((PolyLEF.mul (polyLEF_eqAtF pre post w) (PolyLEF.const 0 (f w))).mono
    (by (clear * -; omega))).congr fun _ ↦ rfl

/-- A product of two multilinear extensions has degree two in each coordinate. -/
theorem polyLEF_mle_mul (f g : ℕ → F) (N M : ℕ) (pre post : List F) :
    PolyLEF 2 fun x ↦ (∑ o ∈ range N, eqAtF (pre ++ x :: post) o * f o) *
      ∑ o ∈ range M, eqAtF (pre ++ x :: post) o * g o :=
  PolyLEF.mul (polyLEF_mle pre post N f) (polyLEF_mle pre post M g)

/-- **The column's multilinear extension**, low bits first. -/
theorem col_splitF {h : ℕ} {a s : List F} (ha : a.length = h) (G : ℕ → F) :
    ∑ n ∈ range (2 ^ (h + s.length)), eqAtF (a ++ s) n * G n =
      ∑ o ∈ range (2 ^ s.length), eqAtF s o * ∑ x ∈ range (2 ^ h), eqAtF a x * G (x + 2 ^ h * o) := by
  rw [pow_add, sum_range_mulW]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  have hd : (x + 2 ^ h * o) / 2 ^ h = o := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx', zero_add]
  have hmod : (x + 2 ^ h * o) % 2 ^ h = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  rw [eqAtF_append, ha, hd, eqAtF_mod a, ha, hmod]
  ring

/-! ## Sums over the cube -/

/-- The sum over the remaining cube of `φ`, the first coordinates bound to `acc`. -/
def cubeSumF (φ : List F → F) (n : ℕ) (acc : List F) : F :=
  ∑ u ∈ range (2 ^ (n - acc.length)), φ (acc ++ bitsF u (n - acc.length))

theorem cube_plainFamilyF {β : Type} (φ : β → List F → F) {d : ℕ} (n : ℕ)
    (hφ : ∀ q pre post, PolyLEF d fun x ↦ φ q (pre ++ x :: post)) :
    PlainFamilyF (fun q acc ↦ cubeSumF (φ q) n acc) d n := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by (clear * - n F acc hacc; omega)
  refine ⟨?_, ?_⟩
  · have e : ∀ x, cubeSumF (φ q) n (acc ++ [x]) =
        ∑ u ∈ range (2 ^ (n - (acc.length + 1))), φ q (acc ++ x :: bitsF u (n - (acc.length + 1))) := by
      intro x
      simp only [cubeSumF, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    exact PolyLEF.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      φ q (acc ++ x :: bitsF u (n - (acc.length + 1)))) (PolyLEF.sum _ fun u _ ↦ hφ q acc _)
      fun x ↦ (e x).symm
  · simp only [cubeSumF, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [bitsF_two_mul, bitsF_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

theorem cubeSumF_nil (φ : List F → F) (n : ℕ) :
    cubeSumF φ n [] = ∑ u ∈ range (2 ^ n), φ (bitsF u n) := by
  simp [cubeSumF]

theorem cubeSumF_full (φ : List F → F) {n : ℕ} {acc : List F} (h : acc.length = n) :
    cubeSumF φ n acc = φ acc := by
  rw [cubeSumF, h, Nat.sub_self]
  simp [bitsF]

/-! ## Characteristic two: cube points -/

variable [CharP F 2]

/-- **Equality weights at a cube point** pick the index. -/
theorem eqAtF_bitsF_lt : ∀ {m z w : ℕ}, z < 2 ^ m → w < 2 ^ m →
    eqAtF (bitsF z m : List F) w = if w = z then 1 else 0
  | 0, z, w, hz, hw => by
    have : z = 0 := by simpa using hz
    have : w = 0 := by simpa using hw
    subst z; subst w; simp [bitsF]
  | m + 1, z, w, hz, hw => by
    rw [bitsF, eqAtF_succ, eqAtF_bitsF_lt (m := m) (by rw [pow_succ] at hz; (clear * - z m w hz; omega))
      (by rw [pow_succ] at hw; (clear * - w m z hw; omega))]
    have key : w = z ↔ (w % 2 = z % 2 ∧ w / 2 = z / 2) := by (clear * - w z m; omega)
    by_cases h : w / 2 = z / 2
    · rcases Nat.mod_two_eq_zero_or_one z with hz2 | hz2 <;>
        rcases Nat.mod_two_eq_zero_or_one w with hw2 | hw2 <;>
        simp [hz2, hw2, h, key, CharTwo.add_self_eq_zero]
    · simp [h, key]

/-- A sum weighted by equality weights at a cube point picks the index. -/
theorem sum_eqAtF_bitsF {m z : ℕ} (hz : z < 2 ^ m) (G : ℕ → F) :
    ∑ w ∈ range (2 ^ m), eqAtF (bitsF z m : List F) w * G w = G z := by
  rw [Finset.sum_eq_single z]
  · rw [eqAtF_bitsF_lt hz hz, ite_eq_left rfl, one_mul]
  · intro w hw hne
    rw [eqAtF_bitsF_lt hz (Finset.mem_range.1 hw), ite_eq_right hne, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 hz) h

end

end Lvm.E2V
