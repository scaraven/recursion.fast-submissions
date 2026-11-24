-- New for lvm6 (WP CB-E). The weight algebra of the two Keccak input ends (FORMAT6 §6.2 row 10,
-- §6.3) in CB's circuit form: the claim's weights after a layer are product weights through the
-- transpose, so the ends' slice weights are lane forms of three rotated sums of the slices.
import Lvm6QKLayAlg

/-!
# The input ends' weight algebra (CB-E)

A claim after a layer carries `W = Lᵀ(batchWF p β)` (`WRep.lt`). Here, over a field or at `E2`:

* `batchW_eq`, `laneWB` (the 25 lane weights of the batch) are CB-L's (`Lvm6QKLayAlg`).
* **`laneForm_pairs`**: a lane form (`laneFormF`) is a sum over 11 fixed (lane, shift) pairs.
* The slice vectors of the byte shift: `uHi s z = s_{z−8}` (`z ≥ 8`), `uLo s z = s_{z+56}`
  (`z < 8`), `uS s z = s_z`; **`rot_hi`**, **`rot_lo`** (their rotated sums as plain sums) and
  **`rot_s`** (`rotSum uS = rotSum uHi + rotSum uLo`, both shifted by 56): 4,096 products for
  all three tables.
* **`shW_dot`**: `Σ_z s_z·shW(W, o, z)` is lane `o` against `uHi` plus lane `o+1` against `uLo`.
* **`treeSum`**: the tree end's check sum `Σ_z treeWt(…, z)·s_z` on `Lᵀ(prodWG A B)` is
  `c^P·Σ_{o<8} eq(ϱ, o)·X(o) + c^L·Σ_{o<4} eq(ϱ, o)·X(o) + c^M·Σ_{ℓ<25} eq(ϱ, 8+ℓ)·LD(ℓ)`,
  `X(o) = laneForm(rotSum uHi)(o) + laneForm(rotSum uLo)(o+1)`, `LD = laneForm(rotSum uS)`.
* **`spSum`**: the sponge's: `(1+r)·Σ_ℓ eq(ϱ, ℓ)·LD(ℓ) + r·Σ_ℓ eq(ϱ, 25+ℓ)·LD(ℓ)`.
-/

set_option autoImplicit false

namespace Lvm6.QK.En

open Lvm Lvm.E2V Lvm.Q1 Finset
open Lvm6.K
open LeanVM.Parameters (E2)

section

variable {F : Type} [Field F]

/-! ## Lane forms, slice vectors, rotated sums -/

/-- The 11 (lane weight, shift) pairs of lane `ℓ`'s form. -/
def lanePairs (l : ℕ) : List (ℕ × ℕ) :=
  (Lvm.keccakPi l, Lvm.Q1.rho l) ::
    ((List.range 5).map (fun y ↦ (Lvm.keccakPi ((l % 5 + 1) % 5 + 5 * y),
        Lvm.Q1.rho ((l % 5 + 1) % 5 + 5 * y))) ++
      (List.range 5).map (fun y ↦ (Lvm.keccakPi ((l % 5 + 4) % 5 + 5 * y),
        (Lvm.Q1.rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

theorem laneForm_pairs (B : List F) (R : ℕ → F) (l : ℕ) :
    laneFormF B R l = ((lanePairs l).map fun p ↦ B.getD p.1 0 * R p.2).sum := by
  simp only [laneFormF, lanePairs, sumF_eq_sum, List.map_cons, List.map_append, List.map_map,
    List.sum_cons, List.sum_append, Function.comp_def, add_assoc]

/-- The high part of the byte shift: `s_{z−8}` for `z ≥ 8`. -/
def uHi (s : List F) (z : ℕ) : F := if 8 ≤ z then s.getD (z - 8) 0 else 0

/-- The low part of the byte shift: `s_{z+56}` for `z < 8`. -/
def uLo (s : List F) (z : ℕ) : F := if z < 8 then s.getD (z + 56) 0 else 0

/-- The slices unshifted. -/
def uS (s : List F) (z : ℕ) : F := s.getD z 0

theorem rotSum_mod' (u A : ℕ → F) (t : ℕ) : rotSumG u A (t % 64) = rotSumG u A t := by
  unfold rotSumG
  exact congrArg sumF (List.map_congr_left fun z _ ↦ by rw [Nat.add_mod_mod])

theorem rot_hi (s : List F) (A : ℕ → F) (t : ℕ) :
    rotSumG (uHi s) A t = ∑ i ∈ range 56, s.getD i 0 * A ((i + 8 + t) % 64) := by
  have h := Finset.sum_range_add (fun z ↦ uHi s z * A ((z + t) % 64)) 8 56
  simp only [Nat.reduceAdd] at h
  have h0 : ∑ z ∈ range 8, uHi s z * A ((z + t) % 64) = 0 :=
    Finset.sum_eq_zero fun z hz ↦ by
      rw [uHi, if_neg (by have := Finset.mem_range.mp hz; omega), zero_mul]
  rw [rotSumG, sumF_map_range, h, h0, zero_add]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [uHi, if_pos (by omega), show 8 + i - 8 = i by omega, show 8 + i + t = i + 8 + t by omega]

theorem rot_lo (s : List F) (A : ℕ → F) (t : ℕ) :
    rotSumG (uLo s) A t = ∑ i ∈ range 8, s.getD (56 + i) 0 * A ((i + t) % 64) := by
  have h := Finset.sum_range_add (fun z ↦ uLo s z * A ((z + t) % 64)) 8 56
  simp only [Nat.reduceAdd] at h
  have h0 : ∑ z ∈ range 56, uLo s (8 + z) * A ((8 + z + t) % 64) = 0 :=
    Finset.sum_eq_zero fun z _ ↦ by rw [uLo, if_neg (by omega), zero_mul]
  rw [rotSumG, sumF_map_range, h, h0, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [uLo, if_pos (Finset.mem_range.mp hi), Nat.add_comm i 56]

/-- **The unshifted table from the two shifted ones.** -/
theorem rot_s (s : List F) (A : ℕ → F) (t : ℕ) :
    rotSumG (uS s) A t = rotSumG (uHi s) A ((t + 56) % 64) + rotSumG (uLo s) A ((t + 56) % 64) := by
  have h := Finset.sum_range_add (fun z ↦ uS s z * A ((z + t) % 64)) 56 8
  simp only [Nat.reduceAdd] at h
  rw [rot_hi, rot_lo, rotSumG, sumF_map_range, h]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [uS, show (i + 8 + (t + 56) % 64) % 64 = (i + t) % 64 by omega]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [uS, show (i + (t + 56) % 64) % 64 = (56 + i + t) % 64 by omega]

/-- **A lane of `Lᵀ(prodWG A B)` against a slice vector** (`lane_dotG` as a `Finset` sum). -/
theorem ld (A : ℕ → F) (B : List F) (u : ℕ → F) {l : ℕ} (hl : l < 25) :
    ∑ z ∈ range 64, u z * (linearTransposeF (prodWG A B)).getD (64 * l + z) 0 =
      laneFormF B (rotSumG u A) l := by
  rw [← sumF_map_range]
  exact lane_dotG A u B hl

theorem sum_ite_lt (f : ℕ → F) {n m : ℕ} (h : n ≤ m) :
    ∑ o ∈ range m, (if o < n then f o else 0) = ∑ o ∈ range n, f o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : ∑ o ∈ range n, (if o < n then f o else 0) = ∑ o ∈ range n, f o :=
    Finset.sum_congr rfl fun o ho ↦ if_pos (Finset.mem_range.mp ho)
  have h2 : ∑ x ∈ range k, (if n + x < n then f (n + x) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ if_neg (by omega)
  rw [Finset.sum_range_add, h1, h2, add_zero]

theorem sum_ite_mid (g : ℕ → F) :
    ∑ o ∈ range 64, (if 8 ≤ o ∧ o < 33 then g o else 0) = ∑ l ∈ range 25, g (8 + l) := by
  have h := Finset.sum_range_add (fun o ↦ if 8 ≤ o ∧ o < 33 then g o else 0) 8 56
  simp only [Nat.reduceAdd] at h
  have h0 : ∑ o ∈ range 8, (if 8 ≤ o ∧ o < 33 then g o else 0) = 0 :=
    Finset.sum_eq_zero fun o ho ↦ if_neg (by have := Finset.mem_range.mp ho; omega)
  rw [h, h0, zero_add, ← sum_ite_lt (fun l ↦ g (8 + l)) (show 25 ≤ 56 by norm_num)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x < 25
  · rw [if_pos ⟨by omega, by omega⟩, if_pos hx]
  · rw [if_neg (by omega), if_neg hx]

theorem sum_range_two (f : ℕ → F) : ∑ m ∈ range 2, f m = f 0 + f 1 := by
  simp [Finset.sum_range_succ]

end

/-! ## The byte shift's pull-back against the slices -/

theorem shW_dot (w s : List E2) (o : ℕ) :
    ∑ z ∈ range 64, shW w o z * s.getD z 0 =
      ∑ z ∈ range 64, uHi s z * w.getD (64 * o + z) 0 +
        ∑ z ∈ range 64, uLo s z * w.getD (64 * (o + 1) + z) 0 := by
  have h1 := Finset.sum_range_add (fun z ↦ shW w o z * s.getD z 0) 56 8
  have h2 := Finset.sum_range_add (fun z ↦ uHi s z * w.getD (64 * o + z) 0) 8 56
  have h3 := Finset.sum_range_add (fun z ↦ uLo s z * w.getD (64 * (o + 1) + z) 0) 8 56
  simp only [Nat.reduceAdd] at h1 h2 h3
  have e1 : ∑ x ∈ range 8, uHi s x * w.getD (64 * o + x) 0 = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by
      rw [uHi, if_neg (by have := Finset.mem_range.mp hx; omega), zero_mul]
  have e2 : ∑ x ∈ range 56, uLo s (8 + x) * w.getD (64 * (o + 1) + (8 + x)) 0 = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by rw [uLo, if_neg (by omega), zero_mul]
  rw [h1, h2, h3, e1, e2, zero_add, add_zero]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun x hx ↦ ?_) (Finset.sum_congr rfl fun x hx ↦ ?_)
  · rw [shW, if_pos (Finset.mem_range.mp hx), uHi, if_pos (by omega), show 8 + x - 8 = x by omega,
      show 64 * o + x + 8 = 64 * o + (8 + x) by omega]
    ring
  · rw [shW, if_neg (by omega), uLo, if_pos (Finset.mem_range.mp hx),
      show 64 * (o + 1) + (56 + x) - 56 = 64 * (o + 1) + x by omega, show x + 56 = 56 + x by omega]
    ring

/-! ## The two check sums -/

/-- Slot `o`'s shifted lane pair: lane `o` against `uHi`, lane `o + 1` against `uLo`. -/
def XF (A : ℕ → E2) (B s : List E2) (o : ℕ) : E2 :=
  laneFormF B (rotSumG (uHi s) A) o + laneFormF B (rotSumG (uLo s) A) (o + 1)

theorem eqAt_kernel {ϱs : List E2} (hϱ : ϱs.length = 6) {o : ℕ} (ho : o < 64) :
    Lvm.E2V.eqAtF ϱs o = (eqKernelF ϱs).getD o 0 := by
  rw [eqKernelF_getD, hϱ, if_pos (lt_of_lt_of_eq ho (by norm_num))]

/-- **The tree end's check sum** as lane forms of the three rotated sums. -/
theorem treeSum (A : ℕ → E2) (B : List E2) (rseg rtop ϱtop : E2) (ϱs s : List E2)
    (hϱ : ϱs.length = 6) :
    ∑ z ∈ range 64, treeWt rseg rtop ϱtop (linearTransposeF (prodWG A B)) ϱs z * s.getD z 0 =
      (1 + rseg) * (1 + rtop) * (1 + ϱtop) * ∑ o ∈ range 8, (eqKernelF ϱs).getD o 0 * XF A B s o +
      (1 + rseg) * rtop * ϱtop * ∑ o ∈ range 4, (eqKernelF ϱs).getD o 0 * XF A B s o +
      rseg * (1 + rtop + ϱtop) *
        ∑ l ∈ range 25, (eqKernelF ϱs).getD (8 + l) 0 * laneFormF B (rotSumG (uS s) A) l := by
  have hP : ∀ o, ∑ z ∈ range 64, pwP (linearTransposeF (prodWG A B)) o z * s.getD z 0 =
      if o < 8 then XF A B s o else 0 := by
    intro o
    by_cases ho : o < 8
    · have h : ∑ z ∈ range 64, pwP (linearTransposeF (prodWG A B)) o z * s.getD z 0 =
          ∑ z ∈ range 64, shW (linearTransposeF (prodWG A B)) o z * s.getD z 0 :=
        Finset.sum_congr rfl fun z _ ↦ by rw [pwP, if_pos ho]
      rw [if_pos ho, h, shW_dot, ld A B (uHi s) (show o < 25 by omega),
        ld A B (uLo s) (show o + 1 < 25 by omega), XF]
    · rw [if_neg ho]
      exact Finset.sum_eq_zero fun z _ ↦ by rw [pwP, if_neg ho, zero_mul]
  have hL : ∀ o, ∑ z ∈ range 64, pwL (linearTransposeF (prodWG A B)) o z * s.getD z 0 =
      if o < 4 then XF A B s o else 0 := by
    intro o
    by_cases ho : o < 4
    · have h : ∑ z ∈ range 64, pwL (linearTransposeF (prodWG A B)) o z * s.getD z 0 =
          ∑ z ∈ range 64, shW (linearTransposeF (prodWG A B)) o z * s.getD z 0 :=
        Finset.sum_congr rfl fun z _ ↦ by rw [pwL, if_pos ho]
      rw [if_pos ho, h, shW_dot, ld A B (uHi s) (show o < 25 by omega),
        ld A B (uLo s) (show o + 1 < 25 by omega), XF]
    · rw [if_neg ho]
      exact Finset.sum_eq_zero fun z _ ↦ by rw [pwL, if_neg ho, zero_mul]
  have hM : ∀ o, ∑ z ∈ range 64, pwM (linearTransposeF (prodWG A B)) o z * s.getD z 0 =
      if 8 ≤ o ∧ o < 33 then laneFormF B (rotSumG (uS s) A) (o - 8) else 0 := by
    intro o
    by_cases ho : 8 ≤ o ∧ o < 33
    · rw [if_pos ho, ← ld A B (uS s) (show o - 8 < 25 by omega)]
      exact Finset.sum_congr rfl fun z _ ↦ by rw [pwM, if_pos ho, uS, mul_comm]
    · rw [if_neg ho]
      exact Finset.sum_eq_zero fun z _ ↦ by rw [pwM, if_neg ho, zero_mul]
  have hsplit : ∀ z, treeWt rseg rtop ϱtop (linearTransposeF (prodWG A B)) ϱs z * s.getD z 0 =
      ∑ o ∈ range 64, (eqKernelF ϱs).getD o 0 *
        ((1 + rseg) * (1 + rtop) * (1 + ϱtop) *
            (pwP (linearTransposeF (prodWG A B)) o z * s.getD z 0) +
          (1 + rseg) * rtop * ϱtop * (pwL (linearTransposeF (prodWG A B)) o z * s.getD z 0) +
          rseg * (1 + rtop + ϱtop) * (pwM (linearTransposeF (prodWG A B)) o z * s.getD z 0)) := by
    intro z
    rw [treeWt, Finset.sum_mul]
    refine Finset.sum_congr rfl fun o ho ↦ ?_
    rw [eqAt_kernel hϱ (Finset.mem_range.mp ho)]
    ring
  have hinner : ∀ o, ∑ z ∈ range 64, (eqKernelF ϱs).getD o 0 *
        ((1 + rseg) * (1 + rtop) * (1 + ϱtop) *
            (pwP (linearTransposeF (prodWG A B)) o z * s.getD z 0) +
          (1 + rseg) * rtop * ϱtop * (pwL (linearTransposeF (prodWG A B)) o z * s.getD z 0) +
          rseg * (1 + rtop + ϱtop) * (pwM (linearTransposeF (prodWG A B)) o z * s.getD z 0)) =
      (1 + rseg) * (1 + rtop) * (1 + ϱtop) *
          (if o < 8 then (eqKernelF ϱs).getD o 0 * XF A B s o else 0) +
        (1 + rseg) * rtop * ϱtop * (if o < 4 then (eqKernelF ϱs).getD o 0 * XF A B s o else 0) +
        rseg * (1 + rtop + ϱtop) * (if 8 ≤ o ∧ o < 33 then
          (eqKernelF ϱs).getD o 0 * laneFormF B (rotSumG (uS s) A) (o - 8) else 0) := by
    intro o
    have hf : ∑ z ∈ range 64, (eqKernelF ϱs).getD o 0 *
          ((1 + rseg) * (1 + rtop) * (1 + ϱtop) *
              (pwP (linearTransposeF (prodWG A B)) o z * s.getD z 0) +
            (1 + rseg) * rtop * ϱtop * (pwL (linearTransposeF (prodWG A B)) o z * s.getD z 0) +
            rseg * (1 + rtop + ϱtop) * (pwM (linearTransposeF (prodWG A B)) o z * s.getD z 0)) =
        (eqKernelF ϱs).getD o 0 * ((1 + rseg) * (1 + rtop) * (1 + ϱtop) *
            ∑ z ∈ range 64, pwP (linearTransposeF (prodWG A B)) o z * s.getD z 0 +
          (1 + rseg) * rtop * ϱtop *
            ∑ z ∈ range 64, pwL (linearTransposeF (prodWG A B)) o z * s.getD z 0 +
          rseg * (1 + rtop + ϱtop) *
            ∑ z ∈ range 64, pwM (linearTransposeF (prodWG A B)) o z * s.getD z 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [hf, hP, hL, hM]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun z _ ↦ hsplit z, Finset.sum_comm,
    Finset.sum_congr rfl fun o _ ↦ hinner o, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_ite_lt _ (show 8 ≤ 64 by norm_num),
    sum_ite_lt _ (show 4 ≤ 64 by norm_num), sum_ite_mid]
  simp only [Nat.add_sub_cancel_left]

/-- **The sponge end's check sum** as lane forms of the rotated sum. -/
theorem spSum (A : ℕ → E2) (B : List E2) (rseg : E2) (ϱs s : List E2) (hϱ : ϱs.length = 6) :
    ∑ z ∈ range 64, spWt rseg (linearTransposeF (prodWG A B)) ϱs z * s.getD z 0 =
      (1 + rseg) * ∑ l ∈ range 25, (eqKernelF ϱs).getD l 0 * laneFormF B (rotSumG (uS s) A) l +
      rseg * ∑ l ∈ range 25, (eqKernelF ϱs).getD (25 + l) 0 * laneFormF B (rotSumG (uS s) A) l := by
  have e0 : Lvm.E2V.eqAtF [rseg] 0 = 1 + rseg := by simp [Lvm.E2V.eqAtF]
  have e1 : Lvm.E2V.eqAtF [rseg] 1 = rseg := by simp [Lvm.E2V.eqAtF]
  have hz : ∀ z, spWt rseg (linearTransposeF (prodWG A B)) ϱs z * s.getD z 0 =
      ∑ l ∈ range 25, ((1 + rseg) * (eqKernelF ϱs).getD l 0 *
          (uS s z * (linearTransposeF (prodWG A B)).getD (64 * l + z) 0) +
        rseg * (eqKernelF ϱs).getD (25 + l) 0 *
          (uS s z * (linearTransposeF (prodWG A B)).getD (64 * l + z) 0)) := by
    intro z
    rw [spWt, sum_range_two, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.mp hl
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    rw [eqAt_kernel hϱ (show l < 64 by omega), eqAt_kernel hϱ (show 25 + l < 64 by omega), e0, e1, uS]
    ring
  rw [Finset.sum_congr rfl fun z _ ↦ hz z, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.mp hl
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ld A B (uS s) hl']
  ring

end Lvm6.QK.En
