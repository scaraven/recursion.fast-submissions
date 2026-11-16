/- `LvmXSComputesOff` (GOLF2 off-path move, group 19 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXField, LvmXNtt, LvmXNtt2, LvmXNtt3, LvmXSOut, LvmXSComputes,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXField
import LvmXNtt
import LvmXNtt2
import LvmXNtt3
import LvmXSOut
import LvmXSComputes
import LvmMlListLemmas

-- ===== from `LvmXField` =====

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64

theorem wK_or_self (x : Word) : wK (x ||| x) = wK x := by rw [BitVec.or_self]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64

theorem invKC_inv (d a : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (invKC d a) M) :=
  inv_runPrims (fun p hp => by have := invKC_dst d a p hp; omega) hM

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

/-- The square in coordinates (characteristic two). -/
theorem mkE_sq (a₀ a₁ a₂ : BF64) :
    mkE a₀ a₁ a₂ * mkE a₀ a₁ a₂ = mkE (a₀ * a₀) (a₂ * a₂) (a₁ * a₁ + a₂ * a₂) := by
  have h2 : (2 : BF64) = 0 := CharTwo.two_eq_zero
  rw [mkE_mul]
  congr 1
  · linear_combination a₁ * a₂ * h2
  · linear_combination (a₀ * a₁ + a₁ * a₂) * h2
  · linear_combination a₀ * a₂ * h2

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

theorem mulEC_inv (d a b : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) :
    Inv (runPrims (mulEC d a b) M) :=
  inv_runPrims (fun p hp => by have := mulEC_dst d a b p hp; omega) hM

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

theorem addEC_dst (d a b : ℕ) : ∀ p ∈ addEC d a b, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 := by
  simp [addEC, Prim.dst]

/-- **`addEC` computes `E`'s sum** (the result may be an operand, not overlap one). -/
theorem addEC_spec {M : Mem} {d a b : ℕ} (hd : d + 2 < M.size)
    (ha : d = a ∨ d + 3 ≤ a ∨ a + 3 ≤ d) (hb : d = b ∨ d + 3 ≤ b ∨ b + 3 ≤ d) :
    rdE (runPrims (addEC d a b) M) d = rdE M a + rdE M b := by
  rw [rdE, rdE, rdE, mkE_add]
  simp (disch := ((try simp only [size_set]); omega)) only [addEC, runPrims_cons, runPrims_nil,
    Prim.run, rdK, rd_set_self, rd_set_ne, eval_xor, wK_xor]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

theorem mulEKC_dst (d a k : ℕ) :
    ∀ p ∈ mulEKC d a k, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  intro p hp
  simp only [mulEKC, List.mem_append] at hp
  rcases hp with (hp | hp) | hp <;> (have := mulKC_dst _ _ _ p hp; omega)

/-- **`mulEKC` computes `E × K`** (the result may be the `E` operand; `k` is not overwritten). -/
theorem mulEKC_spec {M : Mem} (hM : Inv M) {d a k : ℕ} (hd : 9 ≤ d) (hd' : d + 3 ≤ regs)
    (ha : 9 ≤ a) (hk : 9 ≤ k) (had : d = a ∨ d + 3 ≤ a ∨ a + 3 ≤ d) (hkd : k + 1 ≤ d ∨ d + 3 ≤ k) :
    rdE (runPrims (mulEKC d a k) M) d = rdE M a * mkE (rdK M k) 0 0 := by
  have hs : 256 ≤ M.size := hM.1
  simp only [regs] at hd'
  simp only [mulEKC, runPrims_append]
  set M1 := runPrims (mulKC d a k) M
  have i1 : Inv M1 := mulKC_inv d a k (by omega) hM
  have v1 : rdK M1 d = rdK M a * rdK M k := mulKC_spec hM hd (by simp [regs]; omega) ha hk
  set M2 := runPrims (mulKC (d + 1) (a + 1) k) M1
  have i2 : Inv M2 := mulKC_inv (d + 1) (a + 1) k (by omega) i1
  have v2 : rdK M2 (d + 1) = rdK M1 (a + 1) * rdK M1 k :=
    mulKC_spec i1 (by omega) (by simp [regs]; omega) (by omega) hk
  have v3 : rdK (runPrims (mulKC (d + 2) (a + 2) k) M2) (d + 2) = rdK M2 (a + 2) * rdK M2 k :=
    mulKC_spec i2 (by omega) (by simp [regs]; omega) (by omega) hk
  have f : ∀ (a' b' : ℕ) (M' : Mem) (i : ℕ), 9 ≤ i → i ≠ a' →
      rdK (runPrims (mulKC a' b' k) M') i = rdK M' i := fun a' b' M' i hi hne => by
    simp only [rdK]; rw [mulKC_frame _ _ _ (by omega) hne]
  have g0 : rdK (runPrims (mulKC (d + 2) (a + 2) k) M2) d = rdK M a * rdK M k := by
    rw [f _ _ _ d (by omega) (by omega), f _ _ _ d (by omega) (by omega), v1]
  have g1 : rdK (runPrims (mulKC (d + 2) (a + 2) k) M2) (d + 1) = rdK M (a + 1) * rdK M k := by
    rw [f _ _ _ (d + 1) (by omega) (by omega), v2, f _ _ _ (a + 1) (by omega) (by omega),
      f _ _ _ k (by omega) (by omega)]
  have g2 : rdK (runPrims (mulKC (d + 2) (a + 2) k) M2) (d + 2) = rdK M (a + 2) * rdK M k := by
    rw [v3, f _ _ _ (a + 2) (by omega) (by omega), f _ _ _ (a + 2) (by omega) (by omega),
      f _ _ _ k (by omega) (by omega), f _ _ _ k (by omega) (by omega)]
  simp only [rdE]
  rw [mkE_smul, g0, g1, g2]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

theorem sqEC_dst (d a : ℕ) :
    ∀ p ∈ sqEC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨ (5 ≤ p.dst ∧ p.dst < 10) := by
  intro p hp
  simp only [sqEC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((hp | hp) | hp) | hp | hp
  · have := mulKC_dst _ _ _ p hp; omega
  · have := mulKC_dst _ _ _ p hp; omega
  · have := mulKC_dst _ _ _ p hp; omega
  · subst hp; simp [Prim.dst]
  · subst hp; simp [Prim.dst]

/-- The tail of `sqEC`: `M[d + 2] ^= M[9]`, `M[d + 1] := M[9]`. -/
theorem sqTail_spec {N : Mem} {d : ℕ} (hs : d + 2 < N.size) (hd : 10 ≤ d) :
    rdE (runPrims [.op .xor (d + 2) (d + 2) 9, .op .or (d + 1) 9 9] N) d =
      mkE (rdK N d) (rdK N 9) (rdK N (d + 2) + rdK N 9) := by
  simp (disch := ((try simp only [size_set]); omega)) only [rdE, runPrims_cons, runPrims_nil,
    Prim.run, rdK, rd_set_self, rd_set_ne, eval_xor, eval_or, BitVec.or_self, wK_xor]

/-- **`sqEC` computes `E`'s square** (the result may be the operand). -/
theorem sqEC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 10 ≤ d) (hd' : d + 3 ≤ regs)
    (ha : 10 ≤ a) (had : d = a ∨ d + 3 ≤ a ∨ a + 3 ≤ d) :
    rdE (runPrims (sqEC d a) M) d = rdE M a * rdE M a := by
  have hs : 256 ≤ M.size := hM.1
  simp only [regs] at hd'
  simp only [sqEC, runPrims_append]
  have f : ∀ (a' b' : ℕ) (M' : Mem) (i : ℕ), 9 ≤ i → i ≠ a' →
      rdK (runPrims (mulKC a' b' b') M') i = rdK M' i := fun a' b' M' i hi hne => by
    simp only [rdK]; rw [mulKC_frame _ _ _ (by omega) hne]
  have i1 : Inv (runPrims (mulKC 9 (a + 2) (a + 2)) M) := mulKC_inv 9 (a + 2) (a + 2) (by omega) hM
  have v1 : rdK (runPrims (mulKC 9 (a + 2) (a + 2)) M) 9 = rdK M (a + 2) * rdK M (a + 2) :=
    mulKC_spec hM (by omega) (by simp [regs]) (by omega) (by omega)
  have g1 : ∀ i, 10 ≤ i → rdK (runPrims (mulKC 9 (a + 2) (a + 2)) M) i = rdK M i :=
    fun i hi => f _ _ _ i (by omega) (by omega)
  generalize runPrims (mulKC 9 (a + 2) (a + 2)) M = M1 at i1 v1 g1
  have i2 : Inv (runPrims (mulKC d a a) M1) := mulKC_inv d a a (by omega) i1
  have v2 : rdK (runPrims (mulKC d a a) M1) d = rdK M a * rdK M a := by
    rw [mulKC_spec i1 (by omega) (by simp [regs]; omega) (by omega) (by omega), g1 a (by omega)]
  have g2 : ∀ i, 9 ≤ i → i ≠ d → rdK (runPrims (mulKC d a a) M1) i = rdK M1 i :=
    fun i hi hne => f _ _ _ i hi hne
  have w9 : rdK (runPrims (mulKC d a a) M1) 9 = rdK M (a + 2) * rdK M (a + 2) := by
    rw [g2 9 (by omega) (by omega), v1]
  have wa1 : rdK (runPrims (mulKC d a a) M1) (a + 1) = rdK M (a + 1) := by
    rw [g2 (a + 1) (by omega) (by omega), g1 (a + 1) (by omega)]
  generalize runPrims (mulKC d a a) M1 = M2 at i2 v2 g2 w9 wa1
  have v3 : rdK (runPrims (mulKC (d + 2) (a + 1) (a + 1)) M2) (d + 2) =
      rdK M (a + 1) * rdK M (a + 1) := by
    rw [mulKC_spec i2 (by omega) (by simp [regs]; omega) (by omega) (by omega), wa1]
  have u9 : rdK (runPrims (mulKC (d + 2) (a + 1) (a + 1)) M2) 9 = rdK M (a + 2) * rdK M (a + 2) := by
    rw [f _ _ _ 9 (by omega) (by omega), w9]
  have u0 : rdK (runPrims (mulKC (d + 2) (a + 1) (a + 1)) M2) d = rdK M a * rdK M a := by
    rw [f _ _ _ d (by omega) (by omega), v2]
  have hsz : d + 2 < (runPrims (mulKC (d + 2) (a + 1) (a + 1)) M2).size := by
    rw [size_runPrims]; have := i2.1; simp only [regs] at this; omega
  generalize runPrims (mulKC (d + 2) (a + 1) (a + 1)) M2 = M3 at v3 u9 u0 hsz
  rw [sqTail_spec hsz hd, u0, u9, v3]
  simp only [rdE]
  rw [mkE_sq]

/-- The cofactor coordinates of `x = a₀ + a₁ y + a₂ y²`: `C x = N(x)` for the norm `N` below. -/
def cof0 (a₀ a₁ a₂ : BF64) : BF64 := (a₀ + a₂) * (a₀ + a₂) + a₁ * a₁ + a₁ * a₂
/-- See `cof0`. -/
def cof1 (a₀ a₁ a₂ : BF64) : BF64 := a₀ * a₁ + a₂ * a₂
/-- See `cof0`. -/
def cof2 (a₀ a₁ a₂ : BF64) : BF64 := a₁ * a₁ + a₂ * a₂ + a₀ * a₂
/-- The norm `N(x) = a₀ C₀ + a₂ C₁ + a₁ C₂` (the determinant of multiplication by `x`). -/
def normE (a₀ a₁ a₂ : BF64) : BF64 :=
  a₀ * cof0 a₀ a₁ a₂ + a₂ * cof1 a₀ a₁ a₂ + a₁ * cof2 a₀ a₁ a₂

theorem mkE_cof (a₀ a₁ a₂ : BF64) :
    mkE (cof0 a₀ a₁ a₂) (cof1 a₀ a₁ a₂) (cof2 a₀ a₁ a₂) * mkE a₀ a₁ a₂ = mkE (normE a₀ a₁ a₂) 0 0 := by
  have h2 : (2 : BF64) = 0 := CharTwo.two_eq_zero
  rw [mkE_mul]
  simp only [cof0, cof1, cof2, normE]
  congr 1
  · ring
  · linear_combination (a₂ ^ 3 + a₁ * a₂ ^ 2 + a₁ ^ 2 * a₂ + a₁ ^ 3 + a₀ * a₂ ^ 2 + 2 * a₀ * a₁ * a₂ +
      a₀ ^ 2 * a₁) * h2
  · linear_combination (a₂ ^ 3 + a₁ * a₂ ^ 2 + a₁ ^ 2 * a₂ + 2 * a₀ * a₂ ^ 2 + a₀ * a₁ ^ 2 +
      a₀ ^ 2 * a₂) * h2

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

/-- **The norm of a nonzero element is nonzero** (`y³ + y + 1` has no root in `K`). -/
theorem normE_ne_zero {a₀ a₁ a₂ : BF64} (hx : mkE a₀ a₁ a₂ ≠ 0) : normE a₀ a₁ a₂ ≠ 0 := by
  intro hN
  have h2 : (2 : BF64) = 0 := CharTwo.two_eq_zero
  have hc := mkE_cof a₀ a₁ a₂
  rw [hN, mkE_zero] at hc
  have hC := mul_eq_zero.mp hc
  rcases hC with hC | hC
  · rw [← mkE_zero] at hC
    obtain ⟨e0, e1, e2⟩ := mkE_inj hC
    simp only [cof0, cof1, cof2] at e0 e1 e2
    have hv : a₁ ^ 3 + a₁ * a₂ ^ 2 + a₂ ^ 3 = 0 := by
      linear_combination a₂ * e1 - a₁ * e2 + (a₁ ^ 3 + a₁ * a₂ ^ 2) * h2
    by_cases ha₂ : a₂ = 0
    · subst ha₂
      have ha₁ : a₁ = 0 := by
        have : a₁ * a₁ = 0 := by linear_combination e2
        exact mul_self_eq_zero.mp this
      subst ha₁
      have ha₀ : a₀ = 0 := by
        have : a₀ * a₀ = 0 := by linear_combination e0
        exact mul_self_eq_zero.mp this
      subst ha₀
      exact hx mkE_zero
    · apply BF64.ext3Poly_no_root (a₁ * a₂⁻¹)
      have h3 : a₂ ^ 3 ≠ 0 := pow_ne_zero 3 ha₂
      simp only [BF64.ext3Poly, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      have : (a₁ * a₂⁻¹) ^ 3 + a₁ * a₂⁻¹ + 1 = (a₁ ^ 3 + a₁ * a₂ ^ 2 + a₂ ^ 3) / a₂ ^ 3 := by
        field_simp
      rw [this, hv, zero_div]
  · exact hx hC

/-- **`E`'s inverse in coordinates**: `x⁻¹ = N(x)⁻¹ · C(x)` (`0⁻¹ = 0`). -/
theorem mkE_inv (a₀ a₁ a₂ : BF64) :
    (mkE a₀ a₁ a₂)⁻¹ = mkE ((normE a₀ a₁ a₂)⁻¹ * cof0 a₀ a₁ a₂) ((normE a₀ a₁ a₂)⁻¹ * cof1 a₀ a₁ a₂)
      ((normE a₀ a₁ a₂)⁻¹ * cof2 a₀ a₁ a₂) := by
  by_cases hx : mkE a₀ a₁ a₂ = 0
  · obtain ⟨rfl, rfl, rfl⟩ := mkE_inj (hx.trans mkE_zero.symm)
    simp only [cof0, cof1, cof2, normE, add_zero, mul_zero, inv_zero]
    rw [mkE_zero, inv_zero]
  · symm
    apply eq_inv_of_mul_eq_one_left
    have e : mkE ((normE a₀ a₁ a₂)⁻¹ * cof0 a₀ a₁ a₂) ((normE a₀ a₁ a₂)⁻¹ * cof1 a₀ a₁ a₂)
        ((normE a₀ a₁ a₂)⁻¹ * cof2 a₀ a₁ a₂) =
        mkE (cof0 a₀ a₁ a₂) (cof1 a₀ a₁ a₂) (cof2 a₀ a₁ a₂) * mkE (normE a₀ a₁ a₂)⁻¹ 0 0 := by
      rw [mkE_smul, mul_comm _ (cof0 a₀ a₁ a₂), mul_comm _ (cof1 a₀ a₁ a₂), mul_comm _ (cof2 a₀ a₁ a₂)]
    rw [e]
    calc mkE (cof0 a₀ a₁ a₂) (cof1 a₀ a₁ a₂) (cof2 a₀ a₁ a₂) * mkE (normE a₀ a₁ a₂)⁻¹ 0 0 *
          mkE a₀ a₁ a₂
        = mkE (normE a₀ a₁ a₂)⁻¹ 0 0 *
            (mkE (cof0 a₀ a₁ a₂) (cof1 a₀ a₁ a₂) (cof2 a₀ a₁ a₂) * mkE a₀ a₁ a₂) := by ring
      _ = mkE (normE a₀ a₁ a₂) 0 0 * mkE (normE a₀ a₁ a₂)⁻¹ 0 0 := by rw [mkE_cof, mul_comm]
      _ = 1 := by
        rw [mkE_smul]; simp only [zero_mul]; rw [mul_inv_cancel₀ (normE_ne_zero hx), mkE_one]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

theorem wK_cof0W (a₀ a₁ a₂ : Word) : wK (cof0W a₀ a₁ a₂) = cof0 (wK a₀) (wK a₁) (wK a₂) := by
  simp only [cof0W, cof0, wK_xor, mulKW_spec]
theorem wK_cof1W (a₀ a₁ a₂ : Word) : wK (cof1W a₀ a₁ a₂) = cof1 (wK a₀) (wK a₁) (wK a₂) := by
  simp only [cof1W, cof1, wK_xor, mulKW_spec]
theorem wK_cof2W (a₀ a₁ a₂ : Word) : wK (cof2W a₀ a₁ a₂) = cof2 (wK a₀) (wK a₁) (wK a₂) := by
  simp only [cof2W, cof2, wK_xor, mulKW_spec]
theorem wK_normW (a₀ a₁ a₂ : Word) : wK (normW a₀ a₁ a₂) = normE (wK a₀) (wK a₁) (wK a₂) := by
  simp only [normW, normE, wK_xor, mulKW_spec, wK_cof0W, wK_cof1W, wK_cof2W]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

theorem invPre_run {M : Mem} (hM : Inv M) {a : ℕ} (ha : 20 ≤ a) (ha' : a + 3 ≤ regs) :
    rd (runPrims (invPre a) M) 13 = cof0W (rd M a) (rd M (a + 1)) (rd M (a + 2)) ∧
    rd (runPrims (invPre a) M) 14 = cof1W (rd M a) (rd M (a + 1)) (rd M (a + 2)) ∧
    rd (runPrims (invPre a) M) 15 = cof2W (rd M a) (rd M (a + 1)) (rd M (a + 2)) ∧
    rd (runPrims (invPre a) M) 17 = normW (rd M a) (rd M (a + 1)) (rd M (a + 2)) := by
  obtain ⟨hs, h0, h2, h3⟩ := inv_consts hM
  simp only [regs] at ha'
  delta invPre
  simp only [mulKC, redC, List.cons_append, List.nil_append, List.append_assoc,
    runPrims_cons, runPrims_nil, Prim.run, cRed, normW, cof0W, cof1W, cof2W, mulKW, redW]
  simp (disch := ((try simp only [size_set]); omega)) only [rd_set_self, rd_set_ne, h2,
    eval_clmul, eval_clmulh, eval_xor, and_self]

theorem invPre_dst (a : ℕ) : ∀ p ∈ invPre a, 5 ≤ p.dst ∧ p.dst < 20 := by
  delta invPre
  simp only [mulKC, redC, List.forall_mem_append, List.forall_mem_cons, Prim.dst,
    List.mem_nil_iff, false_implies, implies_true, and_true]
  and_intros <;> omega

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext

/-- **`invEC` computes `E`'s inverse** (the result may be the operand). -/
theorem invEC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 20 ≤ d) (hd' : d + 3 ≤ regs)
    (ha : 20 ≤ a) (ha' : a + 3 ≤ regs) : rdE (runPrims (invEC d a) M) d = (rdE M a)⁻¹ := by
  have hr : regs = 256 := rfl
  obtain ⟨v13, v14, v15, v17⟩ := invPre_run hM ha ha'
  have i1 : Inv (runPrims (invPre a) M) :=
    inv_runPrims (fun p hp => by have := invPre_dst a p hp; omega) hM
  simp only [invEC, runPrims_append]
  generalize runPrims (invPre a) M = M1 at i1 v13 v14 v15 v17
  have i2 : Inv (runPrims (invKC 18 17) M1) := invKC_inv 18 17 (by omega) i1
  have w18 : rdK (runPrims (invKC 18 17) M1) 18 = (rdK M1 17)⁻¹ :=
    invKC_spec i1 (by omega) (by omega)
  have fi : ∀ i, 12 ≤ i → i ≠ 18 → rd (runPrims (invKC 18 17) M1) i = rd M1 i :=
    fun i hi hne => invKC_frame 18 17 (by omega) hne M1
  generalize runPrims (invKC 18 17) M1 = M2 at i2 w18 fi
  have f : ∀ (a' b' c' : ℕ) (M' : Mem) (i : ℕ), 9 ≤ i → i ≠ a' →
      rd (runPrims (mulKC a' b' c') M') i = rd M' i := fun a' b' c' M' i hi hne =>
    mulKC_frame _ _ _ (by omega) hne M'
  have i3 : Inv (runPrims (mulKC d 18 13) M2) := mulKC_inv d 18 13 (by omega) i2
  have i4 : Inv (runPrims (mulKC (d + 1) 18 14) (runPrims (mulKC d 18 13) M2)) :=
    mulKC_inv (d + 1) 18 14 (by omega) i3
  have g0 : rdK (runPrims (mulKC (d + 2) 18 15) (runPrims (mulKC (d + 1) 18 14)
      (runPrims (mulKC d 18 13) M2))) d = rdK M2 18 * rdK M2 13 := by
    simp only [rdK]
    rw [f _ _ _ _ d (by omega) (by omega), f _ _ _ _ d (by omega) (by omega)]
    exact (mulKC_spec i2 (by omega) (by omega) (by omega) (by omega))
  have g1 : rdK (runPrims (mulKC (d + 2) 18 15) (runPrims (mulKC (d + 1) 18 14)
      (runPrims (mulKC d 18 13) M2))) (d + 1) = rdK M2 18 * rdK M2 14 := by
    rw [rdK, f _ _ _ _ (d + 1) (by omega) (by omega)]
    rw [show rd _ (d + 1) = _ from mulKC_run i3 (by omega) (by omega) (by omega) (by omega)]
    rw [f _ _ _ _ 18 (by omega) (by omega), f _ _ _ _ 14 (by omega) (by omega), mulKW_spec]; rfl
  have g2 : rdK (runPrims (mulKC (d + 2) 18 15) (runPrims (mulKC (d + 1) 18 14)
      (runPrims (mulKC d 18 13) M2))) (d + 2) = rdK M2 18 * rdK M2 15 := by
    rw [rdK, mulKC_run i4 (by omega) (by omega) (by omega) (by omega)]
    rw [f _ _ _ _ 18 (by omega) (by omega), f _ _ _ _ 18 (by omega) (by omega),
      f _ _ _ _ 15 (by omega) (by omega), f _ _ _ _ 15 (by omega) (by omega), mulKW_spec]; rfl
  simp only [rdE]
  rw [g0, g1, g2, w18, mkE_inv]
  simp only [rdK]
  rw [fi 13 (by omega) (by omega), fi 14 (by omega) (by omega), fi 15 (by omega) (by omega), v13, v14,
    v15, v17, wK_cof0W, wK_cof1W, wK_cof2W, wK_normW]

theorem invEC_dst (d a : ℕ) :
    ∀ p ∈ invEC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨ (5 ≤ p.dst ∧ p.dst < 20) := by
  intro p hp
  simp only [invEC, List.mem_append] at hp
  rcases hp with ((((hp | hp) | hp) | hp) | hp)
  · have := invPre_dst a p hp; omega
  · have := invKC_dst 18 17 p hp; omega
  · have := mulKC_dst _ _ _ p hp; omega
  · have := mulKC_dst _ _ _ p hp; omega
  · have := mulKC_dst _ _ _ p hp; omega

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext
variable {I : Array Word} {s : St}

/-- **`K` square.** -/
theorem sqK_sem (hM : Inv s.M) {d a : ℕ} (hd : 9 ≤ d) (hd' : d < regs) (ha : 9 ≤ a) :
    rdK (semXIR I (sqK d a) s).M d = rdK s.M a ^ 2 := by
  rw [sqK, sem_blk, mulKC_spec hM hd hd' ha ha, sq]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext
variable {I : Array Word} {s : St}

/-- **`E` sum.** -/
theorem addE_sem (hM : Inv s.M) {d a b : ℕ} (hd : d + 3 ≤ regs)
    (ha : d = a ∨ d + 3 ≤ a ∨ a + 3 ≤ d) (hb : d = b ∨ d + 3 ≤ b ∨ b + 3 ≤ d) :
    rdE (semXIR I (addE d a b) s).M d = rdE s.M a + rdE s.M b := by
  rw [addE, sem_blk]; exact addEC_spec (by have := hM.1; simp only [regs] at hd this; omega) ha hb

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext
variable {I : Array Word} {s : St}

/-- **`E × K` product** (`mkE k 0 0` is `K`'s embedding, `mkE_base`). -/
theorem mulEK_sem (hM : Inv s.M) {d a k : ℕ} (hd : 9 ≤ d) (hd' : d + 3 ≤ regs) (ha : 9 ≤ a)
    (hk : 9 ≤ k) (had : d = a ∨ d + 3 ≤ a ∨ a + 3 ≤ d) (hkd : k + 1 ≤ d ∨ d + 3 ≤ k) :
    rdE (semXIR I (mulEK d a k) s).M d = rdE s.M a * algebraMap BF64 Ext3 (rdK s.M k) := by
  rw [mulEK, sem_blk, ← mkE_base]; exact mulEKC_spec hM hd hd' ha hk had hkd

/-- **`E` square.** -/
theorem sqE_sem (hM : Inv s.M) {d a : ℕ} (hd : 10 ≤ d) (hd' : d + 3 ≤ regs) (ha : 10 ≤ a)
    (had : d = a ∨ d + 3 ≤ a ∨ a + 3 ≤ d) :
    rdE (semXIR I (sqE d a) s).M d = rdE s.M a ^ 2 := by
  rw [sqE, sem_blk, sqEC_spec hM hd hd' ha had, sq]

/-- **`E` inverse.** -/
theorem invE_sem (hM : Inv s.M) {d a : ℕ} (hd : 20 ≤ d) (hd' : d + 3 ≤ regs) (ha : 20 ≤ a)
    (ha' : a + 3 ≤ regs) : rdE (semXIR I (invE d a) s).M d = (rdE s.M a)⁻¹ := by
  rw [invE, sem_blk]; exact invEC_spec hM hd hd' ha ha'

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext
variable {I : Array Word} {s : St}

theorem wf_sqK (d a : ℕ) (hd : 4 ≤ d) : WF (sqK d a) :=
  fun p hp => by have := mulKC_dst d a a p hp; omega

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext
variable {I : Array Word} {s : St}

theorem wf_addE (d a b : ℕ) (hd : 4 ≤ d) : WF (addE d a b) :=
  fun p hp => by have := addEC_dst d a b p hp; omega

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Polynomial BinaryField CompPoly.Extension BF64
open scoped CompPoly.Extension.Ext
variable {I : Array Word} {s : St}

theorem wf_mulEK (d a k : ℕ) (hd : 4 ≤ d) : WF (mulEK d a k) :=
  fun p hp => by have := mulEKC_dst d a k p hp; omega
theorem wf_sqE (d a : ℕ) (hd : 4 ≤ d) : WF (sqE d a) :=
  fun p hp => by have := sqEC_dst d a p hp; omega
theorem wf_invE (d a : ℕ) (hd : 4 ≤ d) : WF (invE d a) :=
  fun p hp => by have := invEC_dst d a p hp; omega

end Lvm.X
end

-- ===== from `LvmXNtt` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb

theorem mulK_loK_iff {d a b : ℕ} (hd : d < regs) : LoK (mulK d a b) ↔ True :=
  iff_true_intro fun p hp => by have := mulKC_dst d a b p hp; simp only [regs] at *; (clear * - hd this; omega)

theorem invK_loK_iff {d a : ℕ} (hd : d < regs) : LoK (invK d a) ↔ True :=
  iff_true_intro fun p hp => by have := invKC_dst d a p hp; simp only [regs] at *; (clear * - hd this; omega)

theorem wf_alphaIR : WF alphaIR := by
  simp +decide only [alphaIR, alphaBody, WF, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2,
    rC2, cTmp, regs, or_false, and_true]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb

theorem wf_pairBody : WF pairBody := by
  simp +decide only [pairBody, pairPs, arithIR, alphaIR, alphaBody, addK, WF, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs,
    mulK_wf_iff, mulK_writes_iff, or_false, and_true]

theorem wf_fpairBody : WF fpairBody := by
  simp +decide only [fpairBody, pairPs, farithIR, alphaIR, alphaBody, addK, WF, Writes, Prim.dst,
    rQ, uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp,
    regs, mulK_wf_iff, mulK_writes_iff, or_false, and_true]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb

theorem wf_rowBody : WF rowBody := by
  simp +decide only [rowBody, WF, Prim.dst, fU, fW, fH, fN, uT1, rAH, rTa, cTmp, mulK_wf_iff,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb

theorem fwdRun_top (ℓ : ℕ) (Y : ℕ → BF64) :
    ∀ j ≤ ℓ, fwdRun ptK nLog ℓ Y = fwdRun ptK nLog (ℓ - j) (fwdTop ℓ j Y)
  | 0, _ => rfl
  | j + 1, hj => by
    rw [fwdRun_top ℓ Y j (by omega), show ℓ - j = (ℓ - (j + 1)) + 1 by omega, fwdRun, fwdTop,
      show ℓ - (j + 1) = ℓ - 1 - j by omega]

end Lvm.X
end

-- ===== from `LvmXNtt2` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

theorem loK_alphaIR : LoK alphaIR := by
  simp +decide only [alphaIR, alphaBody, LoK, Prim.dst, regs, rBit, uT1, rTa, fG, fAl, uI, rN2,
    rC2, and_true]

/-- **One bit of `α`.** -/
theorem alphaBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {base ta j : ℕ} {T : ℕ → BF64}
    (hb : base < 2 ^ 64) (hj : j < 15) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hI : rd s.M uI = toWord j)
    (hTa : rd s.M rTa = toWord (ta + j)) (hT : rdK s.M (ta + j) = T j) :
    rdK (semXIR I alphaBody s).M fAl = rdK s.M fAl + (if base.testBit j then T j else 0) ∧
    rd (semXIR I alphaBody s).M uI = toWord (j + 1) ∧
    rd (semXIR I alphaBody s).M rTa = toWord (ta + (j + 1)) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hta
  have w1 : WF (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
      .op .sub rBit uT1 rBit]) := by simp +decide only [WF, Prim.dst, rBit, uT1]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
      .op .sub rBit uT1 rBit]) s (by simp +decide only [Lo, Prim.dst, regs, rBit, uT1])
  have r1 : rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M rBit =
        XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M rTa = toWord (ta + j) ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M uI = toWord j ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M fAl = rd s.M fAl ∧
      rd (semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
        .op .sub rBit uT1 rBit]) s).M cOne = 1 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rBit, uT1]; omega)) only
      [rd_set_self, rd_set_ne]
    · rw [hBs, hI, h1]
    · exact hTa
    · exact hI
    · exact h1
  rw [alphaBody, semXIR_seq]
  generalize semXIR I (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0,
    .op .sub rBit uT1 rBit]) s = s1 at hM1 hH1 r1
  obtain ⟨b1, a1, i1, f1, o1⟩ := r1
  obtain ⟨l1, l2, hM2⟩ := load_sem I s1 hM1 (d := fG) (p := rTa) (x := ta + j) (by decide)
    (by decide) a1 (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.load fG rTa) s1 = s2 at l1 l2 hM2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have g2 : wK (rd s2.M fG) = T j := by
    rw [← hT]; exact rdK_eq (l1.trans (hH1 _ (by simp only [regs]; omega)))
  have k1 : rd s2.M rBit = XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord base) (toWord j)) 1) :=
    (l2 _ (by decide)).trans b1
  have k2 : rd s2.M fAl = rd s.M fAl := (l2 _ (by decide)).trans f1
  have k4 : rd s2.M rTa = toWord (ta + j) := (l2 _ (by decide)).trans a1
  have k5 : rd s2.M uI = toWord j := (l2 _ (by decide)).trans i1
  have k6 : rd s2.M cOne = 1 := (l2 _ (by decide)).trans o1
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩
  · simp only [rdK]
    simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k1, k2, eval_xor, mask_bit _ hb (by omega), wK_acc, g2]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k5, k6, add_one_toWord]
  · simp (disch := first | decide | (simp only [size_set, fG, fAl, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [k4, k6, add_one_toWord]
    rfl

/-- **`α`**: the sum over the bits `i < 15` of `base` of the table entries `T i` at `ta + i`
(the row at `rTr`). -/
theorem alphaIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {base ta : ℕ} {T : ℕ → BF64}
    (hb : base < 2 ^ 64) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 15, rdK s.M (ta + i) = T i) :
    rdK (semXIR I alphaIR s).M fAl = ∑ i ∈ range 15, if base.testBit i then T i else 0 := by
  have hs := hM.1
  simp only [regs] at hs hta
  have w0 : WF (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 15]) := by
    simp +decide only [WF, Prim.dst, fAl, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have hH0 := hframe I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s
    (by simp +decide only [Lo, Prim.dst, regs, fAl, uI, rTa, rN2])
  have r0 : rdK (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 15]) s).M fAl = 0 ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 15]) s).M uI = toWord 0 ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 15]) s).M rTa = toWord (ta + 0) ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 15]) s).M rBs = toWord base ∧
      rd (semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr,
        .const rN2 15]) s).M rN2 = 15 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fAl, uI, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hBs
  rw [alphaIR, semXIR_seq]
  generalize semXIR I (.blk [.const fAl 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s
    = s0 at hM0 hH0 r0
  obtain ⟨z0, i0, t0, b0, n0⟩ := r0
  rw [loopK_eq I alphaBody s0 hM0 (by decide) (by decide) (by decide) n0]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 15 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 15) hM0 (by decide)
  have wb : WF alphaBody := wf_alphaIR.2.2.2.2
  have lb : LoK alphaBody := loK_alphaIR.2.2
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ rd s'.M uI = toWord j ∧
    rd s'.M rTa = toWord (ta + j) ∧ rd s'.M rBs = toWord base ∧
    (∀ x, regs ≤ x → rd s'.M x = rd s.M x) ∧
    rdK s'.M fAl = ∑ i ∈ range j, if base.testBit i then T i else 0
  have step : ∀ j s', j < 15 → P j s' → P (j + 1) (decS rC2 (semXIR I alphaBody s')) := by
    rintro j s' hj ⟨q1, q2, q3, q4, q5, q6⟩
    have hTj : rdK s'.M (ta + j) = T j := by
      rw [← hT j hj]
      exact rdK_eq (q5 (ta + j) (by simp only [regs]; omega))
    obtain ⟨e1, e2, e3⟩ := alphaBody_sem I s' q1 (T := T) hb hj (by simp only [regs]; omega) hta2
      q4 q2 q3 hTj
    refine ⟨inv_decS (inv_sem I wb q1) (by decide), ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · rw [rd_decS (by decide), e2]
    · rw [rd_decS (by decide), e3]
    · rw [rd_decS (by decide), frame I _ s' wb q1 _ (by decide) (by
        simp +decide only [alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rBs,
          or_false]), q4]
    · rw [rd_decS (by simp only [rC2, regs] at *; omega), hframeK I _ s' lb x hx, q5 x hx]
    · rw [rdK_decS _ (by decide), e1, q6, sum_range_succ]
  have hP0 : P 0 ⟨entryK rC2 rN2 15 s0.M, s0.o⟩ := by
    refine ⟨hME, ?_, ?_, ?_, fun x hx => ?_, ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), b0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [rdK_eq (hE _ (by decide) (by decide)), z0]; rfl
  have := iterL_ind (f := semXIR I alphaBody) (c := rC2) (m := 15) P step 15 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  exact this.2.2.2.2.2

/-- `α` on a table row is `wAt ptK 15 l base`. -/
theorem alphaIR_wAt (I : Array Word) (s : St) (hM : Inv s.M) {base ta l : ℕ}
    (hb : base < 2 ^ 64) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hBs : rd s.M rBs = toWord base) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 15, rdK s.M (ta + i) = (wRow ptK nLog l).getD i 0) :
    rdK (semXIR I alphaIR s).M fAl = wAt ptK nLog l base :=
  alphaIR_sem I s hM hb hta hta2 hBs hTr hT

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

theorem pairBody_nw {r : ℕ} (hr : r = rA0 ∨ r = rP2 ∨ r = rTr ∨ r = rLv ∨ r = rC1 ∨ r = rN1 ∨
    r = rC3 ∨ r = rN3) : ¬ Writes pairBody r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [pairBody, pairPs, arithIR, alphaIR, alphaBody, addK, Writes, Prim.dst, rQ,
    uX, uT1, uT2, rBs, rAL, rAH, rTa, rBit, uI, rC2, rN2, fAl, fU, fW, fH, fT, fN, fG, cTmp, rA0,
    rP2, rTr, rLv, rC1, rN1, rC3, rN3, mulK_writes_iff, or_false]

/-- **One butterfly**: the pair's low and high elements become `u + α (w + u)` and `w + u`,
`α = Σ_{i<15} [bit_i(base)] T(i)`; nothing else on the heap changes; `q += 1`. -/
theorem pairBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta l q : ℕ} {T : ℕ → BF64}
    (hl : l < 64) (hA : regs ≤ A) (hq : q < 2 ^ 64) (hhi : A + hiP l q < 2 ^ 64)
    (hsz : A + hiP l q < s.M.size) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hQ : rd s.M rQ = toWord q) (hP2 : rd s.M rP2 = toWord (2 ^ l)) (hA0 : rd s.M rA0 = toWord A)
    (hTr : rd s.M rTr = toWord ta) (hT : ∀ i < 15, rdK s.M (ta + i) = T i) :
    rdK (semXIR I pairBody s).M (A + loP l q) = rdK s.M (A + loP l q) +
      (∑ i ∈ range 15, if (baseP l q).testBit i then T i else 0) *
        (rdK s.M (A + hiP l q) + rdK s.M (A + loP l q)) ∧
    rdK (semXIR I pairBody s).M (A + hiP l q) =
      rdK s.M (A + hiP l q) + rdK s.M (A + loP l q) ∧
    (∀ x, regs ≤ x → x ≠ A + loP l q → x ≠ A + hiP l q →
      rd (semXIR I pairBody s).M x = rd s.M x) ∧
    rd (semXIR I pairBody s).M rQ = toWord (q + 1) := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hlh := loP_lt_hiP l q
  have hP : 2 ^ l < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hl
  have hbase : baseP l q < 2 ^ 64 := by
    have : baseP l q ≤ loP l q := by simp [loP]
    omega
  -- the addresses
  have w1 : WF (.blk pairPs) := by
    simp +decide only [pairPs, WF, Prim.dst, uT1, uX, uT2, rBs, rAL, rAH]
  obtain ⟨p1, p2, p3⟩ := pairPs_sem I s hM (A := A) hq hP hQ hP2 hA0
  have hM1 := inv_sem I w1 hM
  have z1 := size_sem I (.blk pairPs) s
  have hH1 := hframe I (.blk pairPs) s (by simp +decide only [pairPs, Lo, Prim.dst, regs, uT1, uX,
    uT2, rBs, rAL, rAH])
  have q1 : rd (semXIR I (.blk pairPs) s).M rQ = toWord q := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide only [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rQ]), hQ]
  have t1 : rd (semXIR I (.blk pairPs) s).M rTr = toWord ta := by
    rw [frame I _ s w1 hM _ (by decide) (by simp +decide only [pairPs, Writes, Prim.dst, uT1, uX,
      uT2, rBs, rAL, rAH, rTr]), hTr]
  rw [pairBody, semXIR_seq]
  generalize semXIR I (.blk pairPs) s = s1 at p1 p2 p3 hM1 hH1 q1 t1 z1
  have hT1 : ∀ i < 15, rdK s1.M (ta + i) = T i := fun i hi => by
    rw [← hT i hi]; exact rdK_eq (hH1 _ (by simp only [regs]; omega))
  -- `α`
  have a2 := alphaIR_sem I s1 hM1 hbase (by simp only [regs]; omega) hta2 p1 t1 hT1
  have hM2 := inv_sem I wf_alphaIR hM1
  have z2 := size_sem I alphaIR s1
  have hH2 := hframeK I alphaIR s1 loK_alphaIR
  have nwA : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I alphaIR s1).M r = rd s1.M r :=
    fun r hr => frame I _ s1 wf_alphaIR hM1 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide only [alphaIR, alphaBody, Writes, Prim.dst, rBit, uT1, rTa, fG, fAl, uI, rN2,
        rC2, cTmp, rAL, rAH, rQ, or_false])
  rw [semXIR_seq]
  generalize semXIR I alphaIR s1 = s2 at a2 hM2 hH2 nwA z2
  have l2 : rd s2.M rAL = toWord (A + loP l q) := (nwA _ (.inl rfl)).trans p2
  have h2 : rd s2.M rAH = toWord (A + hiP l q) := (nwA _ (.inr (.inl rfl))).trans p3
  have q2 : rd s2.M rQ = toWord q := (nwA _ (.inr (.inr rfl))).trans q1
  have hY : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => (hH2 x hx).trans (hH1 x hx)
  -- the arithmetic
  obtain ⟨b1, b2⟩ := arith_sem I s2 hM2 (a := A + loP l q) (b := A + hiP l q)
    (by omega) (by simp only [regs]; omega) (by omega) l2 h2
  have hM3 := inv_sem I wf_arithIR hM2
  have z3 := size_sem I arithIR s2
  have hH3 := hframe I arithIR s2 lo_arithIR
  have nwB : ∀ r, (r = rAL ∨ r = rAH ∨ r = rQ) → rd (semXIR I arithIR s2).M r = rd s2.M r :=
    fun r hr => frame I _ s2 wf_arithIR hM2 _ (by rcases hr with rfl | rfl | rfl <;> decide) (by
      rcases hr with rfl | rfl | rfl <;>
      simp +decide only [arithIR, addK, Writes, Prim.dst, fU, fW, fH, fT, fN, rAL, rAH, rQ,
        mulK_writes_iff, or_false])
  have eU : rdK s2.M (A + loP l q) = rdK s.M (A + loP l q) :=
    rdK_eq (hY _ (by simp only [regs]; omega))
  have eW : rdK s2.M (A + hiP l q) = rdK s.M (A + hiP l q) :=
    rdK_eq (hY _ (by simp only [regs]; omega))
  rw [eU, eW, a2] at b1
  rw [eU, eW] at b2
  rw [semXIR_seq]
  generalize semXIR I arithIR s2 = s3 at b1 b2 hM3 hH3 nwB z3
  have l3 : rd s3.M rAL = toWord (A + loP l q) := (nwB _ (.inl rfl)).trans l2
  have h3 : rd s3.M rAH = toWord (A + hiP l q) := (nwB _ (.inr (.inl rfl))).trans h2
  have q3 : rd s3.M rQ = toWord q := (nwB _ (.inr (.inr rfl))).trans q2
  -- the stores
  obtain ⟨c1, c2, hM4⟩ := store_sem I s3 hM3 (p := rAL) (v := fN) (x := A + loP l q)
    (by decide) (by decide) l3 (by simp only [regs]; omega) (by omega) (by omega)
  have z4 := size_sem I (.store rAL fN) s3
  rw [semXIR_seq]
  generalize semXIR I (.store rAL fN) s3 = s4 at c1 c2 hM4 z4
  have hT4 : cTmp = 4 := rfl
  have hr4 : ∀ r, r < 256 → r ≠ cTmp → rd s4.M r = rd s3.M r := fun r hr h2 =>
    c2 r (by omega) h2
  have h4 : rd s4.M rAH = toWord (A + hiP l q) := (hr4 _ (by decide) (by decide)).trans h3
  have q4 : rd s4.M rQ = toWord q := (hr4 _ (by decide) (by decide)).trans q3
  have f4 : rdK s4.M fH = rdK s3.M fH := rdK_eq (hr4 _ (by decide) (by decide))
  obtain ⟨d1, d2, hM5⟩ := store_sem I s4 hM4 (p := rAH) (v := fH) (x := A + hiP l q)
    (by decide) (by decide) h4 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fH) s4 = s5 at d1 d2 hM5
  have hr5 : ∀ r, r < 256 → r ≠ cTmp → rd s5.M r = rd s4.M r := fun r hr h2 =>
    d2 r (by omega) h2
  -- `q += 1`
  have e6 : ∀ x, x ≠ rQ → rd (semXIR I (.blk [.op .add rQ rQ cOne]) s5).M x = rd s5.M x :=
    fun x hx => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact fun h => hx h.symm) _
  refine ⟨?_, ?_, fun x hx x1 x2 => ?_, ?_⟩
  · rw [rdK_eq (e6 _ (by simp only [rQ]; omega)), rdK_eq (d2 _ (by omega) (by omega)),
      rdK_eq c1, b1]
  · rw [rdK_eq (e6 _ (by simp only [rQ]; omega)), rdK_eq d1, f4, b2]
  · simp only [regs] at hx
    rw [e6 _ (by simp only [rQ]; omega), d2 _ x2 (by omega), c2 _ x1 (by omega),
      hH3 x (by simp only [regs]; omega), hY x (by simp only [regs]; omega)]
  · have hs5 := hM5.1
    simp only [regs] at hs5
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rQ]; omega), hr5 _ (by decide) (by decide), q4,
      hr5 _ (by decide) (by decide), show rd s4.M cOne = 1 from hM4.2 0 (by decide)]
    exact add_one_toWord q

/-- **A level** `l < ℓ` on the row of `2^ℓ` elements at `A`, with the table row `wRow ptK 15 l`
at `ta`: every element becomes `bflyLevel`'s; the heap outside the row is kept. -/
theorem levelIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A ta ℓ l : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ 15) (hl : l < ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (hta : regs ≤ ta) (hta2 : ta + 15 < 2 ^ 64)
    (hdisj : ta + 15 ≤ A ∨ A + 2 ^ ℓ ≤ ta)
    (hLv : rd s.M rLv = toWord l) (hA0 : rd s.M rA0 = toWord A) (hTr : rd s.M rTr = toWord ta)
    (hT : ∀ i < 15, rdK s.M (ta + i) = (wRow ptK nLog l).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I (levelIR ℓ) s).M (A + i) = bflyLevel ptK nLog 0 l Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I (levelIR ℓ) s).M x = rd s.M x) ∧
    (semXIR I (levelIR ℓ) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hA hta
  have hP1 : 2 ^ (ℓ - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hPl : l * 1 < 64 := by omega
  have w0 : WF (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))]) := by
    simp +decide only [WF, Prim.dst, rQ, rP2, rN1, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s
  have hH0 := hframe I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s (by simp +decide only [Lo, Prim.dst, regs, rQ, rP2, rN1,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rQ = toWord 0 ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rP2 = toWord (2 ^ l) ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rN1 = toWord (2 ^ (ℓ - 1)) ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rA0 = toWord A ∧
      rd (semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
        .const rN1 (toWord (2 ^ (ℓ - 1)))]) s).M rTr = toWord ta := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rQ, rP2, rN1]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hLv, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by omega)
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.one_mul]
    · exact hA0
    · exact hTr
  rw [levelIR, semXIR_seq]
  generalize semXIR I (.blk [.const rQ 0, .op .shl rP2 cOne rLv,
    .const rN1 (toWord (2 ^ (ℓ - 1)))]) s = s0 at hM0 z0 hH0 r0
  obtain ⟨q0, p0, n0, a0, t0⟩ := r0
  rw [loopK_eq I pairBody s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hP1]
  have hE : ∀ i, i ≠ rC1 → i ≠ cTmp → rd (entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M) i =
      rd s0.M i := fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC1) (n := rN1) (K := toWord (2 ^ (ℓ - 1))) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rQ = toWord j ∧ rd s'.M rP2 = toWord (2 ^ l) ∧ rd s'.M rA0 = toWord A ∧
    rd s'.M rTr = toWord ta ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) =
      if pairOf l i < j then bflyLevel ptK nLog 0 l Y i else Y i
  have nwP : ∀ r, (r = rA0 ∨ r = rP2 ∨ r = rTr) → ∀ s', Inv s'.M →
      rd (decS rC1 (semXIR I pairBody s')).M r = rd s'.M r := fun r hr s' hs' => by
    rw [rd_decS (by rcases hr with rfl | rfl | rfl <;> decide)]
    exact frame I _ s' wf_pairBody hs' _ (by rcases hr with rfl | rfl | rfl <;> decide)
      (pairBody_nw (by rcases hr with rfl | rfl | rfl <;> simp))
  have step : ∀ j s', j < 2 ^ (ℓ - 1) → P j s' → P (j + 1) (decS rC1 (semXIR I pairBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    have hhi := hiP_lt hl hj
    have hlh := loP_lt_hiP l j
    have hT' : ∀ i < 15, rdK s'.M (ta + i) = (wRow ptK nLog l).getD i 0 := fun i hi => by
      rw [← hT i hi]
      exact rdK_eq (i7 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3, e4⟩ := pairBody_sem I s' i1 (A := A)
      (T := fun i => (wRow ptK nLog l).getD i 0)
      (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by simp only [regs]; omega) hta2 i3 i4 i5 i6 hT'
    have hd : ∀ x, x ≠ rC1 → rd (decS rC1 (semXIR I pairBody s')).M x =
        rd (semXIR I pairBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hlo' := i8 _ (by omega : loP l j < 2 ^ ℓ)
    have hhi' := i8 _ hhi
    rw [pairOf_loP, if_neg (lt_irrefl j)] at hlo'
    rw [pairOf_hiP, if_neg (lt_irrefl j)] at hhi'
    refine ⟨inv_decS (inv_sem I wf_pairBody i1) (by decide), by rw [size_decS, size_sem, i2], ?_,
      (nwP _ (.inr (.inl rfl)) s' i1).trans i4, (nwP _ (.inl rfl) s' i1).trans i5,
      (nwP _ (.inr (.inr rfl)) s' i1).trans i6, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide), e4]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC1]; omega), e3 x (by simp only [regs]; omega) (by omega)
        (by omega), i7 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq (hd _ (by simp only [rC1, regs] at *; omega))]
      by_cases hq : pairOf l i = j
      · rw [if_pos (by omega)]
        rcases pair_cases hq with rfl | rfl
        · rw [e1, hlo', hhi', bflyLevel_lo]; rfl
        · rw [e2, hlo', hhi', bflyLevel_hi]
      · have hil : i ≠ loP l j := fun h => hq (by rw [h, pairOf_loP])
        have hih : i ≠ hiP l j := fun h => hq (by rw [h, pairOf_hiP])
        rw [rdK_eq (e3 _ (by simp only [regs]; omega) (by omega) (by omega)), i8 i hi]
        by_cases hlt : pairOf l i < j
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
  have hP0 : P 0 ⟨entryK rC1 rN1 (toWord (2 ^ (ℓ - 1))) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), q0]
    · dsimp only; rw [hE _ (by decide) (by decide), p0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC1, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [if_neg (Nat.not_lt_zero _), ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC1]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I pairBody) (c := rC1) (m := 2 ^ (ℓ - 1)) P step (2 ^ (ℓ - 1)) 0
    _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨-, z, -, -, -, -, f7, f8⟩ := this
  refine ⟨fun i hi => ?_, f7, z⟩
  rw [f8 i hi, if_pos (pairOf_lt hl hi)]

theorem levelIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rLv ∨ r = rTr ∨ r = rC3 ∨ r = rN3) (ℓ : ℕ) :
    ¬ Writes (levelIR ℓ) r := by
  intro h
  simp only [levelIR, Writes] at h
  rcases h with ⟨p, hp, he⟩ | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, rQ, rP2, rN1, rA0, rLv, rTr, rC3, rN3] at he
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rC1, rA0, rLv, rTr, rC3, rN3] at h
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cTmp, rA0, rLv, rTr, rC3, rN3] at h
  · exact pairBody_nw (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) h

/-- **The inverse NTT** (`bflyRun`) on the machine: from the row `Y` of `2^ℓ` elements at `A`
(`rA0 = A`) and the basis table at `tb` (row `v` at `tb + 15 v`), `bflyIR ℓ tb` leaves
`bflyRun ptK 15 0 ℓ Y` in the row and keeps the heap outside it. -/
theorem bflyIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    (∀ i < 2 ^ ℓ, rdK (semXIR I (bflyIR ℓ tb) s).M (A + i) = bflyRun ptK nLog 0 ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd (semXIR I (bflyIR ℓ tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyIR ℓ tb) s).M := by
  have hs := hM.1
  have hN : nLog = 15 := rfl
  simp only [regs] at hs hA htb
  have hℓ64 : ℓ < 2 ^ 64 := by omega
  have w0 : WF (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) := by
    simp +decide only [WF, Prim.dst, rLv, rTr, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s
  have hH0 := hframe I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rLv, rTr, rN3, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have r0 : rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rTr = toWord (tb + 15 * 0) ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rN3 = toWord ℓ ∧
      rd (semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
        s).M rA0 = toWord A := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rTr, rN3]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · exact hA0
  rw [bflyIR, semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨l0, t0, n0, a0⟩ := r0
  rw [loopK_eq I (lvlStep ℓ) s0 hM0 (by decide) (by decide) (by decide) n0, toNat_toWord hℓ64]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 (toWord ℓ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := toWord ℓ) hM0 (by decide)
  have wl : WF (levelIR ℓ) := (wf_bflyIR ℓ tb).2.2.2.2.1
  have wlb : WF (.blk [.op .add rLv rLv cOne, .const uT1 15, .op .add rTr rTr uT1]) := by
    simp +decide only [WF, Prim.dst, rLv, uT1, rTr]
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + 15 * j) ∧ rd s'.M rA0 = toWord A ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < 2 ^ ℓ, rdK s'.M (A + i) = bflyRun ptK nLog 0 j Y i
  have step : ∀ j s', j < ℓ → P j s' → P (j + 1) (decS rC3 (semXIR I (lvlStep ℓ) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hT : ∀ i < 15, rdK s'.M (tb + 15 * j + i) = (wRow ptK nLog j).getD i 0 :=
      fun i hi => by
        rw [← hW j (by omega) i (by omega)]
        exact rdK_eq (i6 _ (by simp only [regs]; omega) (by omega))
    obtain ⟨e1, e2, e3⟩ := levelIR_sem I s' i1 (Y := bflyRun ptK nLog 0 j Y) (by omega) hj
      (by simp only [regs]; omega) hA2 (by omega) (by simp only [regs]; omega) (by omega)
      (by omega) i3 i5 i4 hT i7
    have hM1 := inv_sem I wl i1
    have nw : ∀ r, (r = rA0 ∨ r = rLv ∨ r = rTr) → rd (semXIR I (levelIR ℓ) s').M r = rd s'.M r :=
      fun r hr => frame I _ s' wl i1 _ (by rcases hr with rfl | rfl | rfl <;> decide)
        (levelIR_nw (by rcases hr with rfl | rfl | rfl <;> simp) ℓ)
    rw [lvlStep]
    simp only [semXIR_seq]
    generalize hs1 : semXIR I (levelIR ℓ) s' = s1 at e1 e2 e3 hM1 nw
    have hs1' := hM1.1
    simp only [regs] at hs1'
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I (.blk [.op .add rLv rLv cOne, .const uT1 15,
        .op .add rTr rTr uT1]) s1)).M x = rd (semXIR I (.blk [.op .add rLv rLv cOne,
        .const uT1 15, .op .add rTr rTr uT1]) s1).M x := fun x hx => rd_decS (Ne.symm hx) _
    have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
        .const uT1 15, .op .add rTr rTr uT1]) s1).M x = rd s1.M x := fun x h1 h2 h3 =>
      rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
    refine ⟨inv_decS (inv_sem I wlb hM1) (by decide), by rw [size_decS, size_sem, e3, i2], ?_, ?_,
      ?_, fun x hx hx2 => ?_, fun i hi => ?_⟩
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inl rfl)), i3, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
        add_one_toWord]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
        [rd_set_self, rd_set_ne]
      rw [nw _ (.inr (.inr rfl)), i4, show (15 : Word) = toWord 15 from rfl, add_toWord]
      congr 1
    · rw [hd _ (by decide), hb _ (by decide) (by decide) (by decide), nw _ (.inl rfl), i5]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), hb _ (by simp only [rLv]; omega)
        (by simp only [uT1]; omega) (by simp only [rTr]; omega), e2 x (by simp only [regs]; omega)
        hx2, i6 x (by simp only [regs]; omega) hx2]
    · rw [rdK_eq ((hd _ (by simp only [rC3]; omega)).trans (hb _ (by simp only [rLv]; omega)
        (by simp only [uT1]; omega) (by simp only [rTr]; omega))), e1 i hi]
      rfl
  have hP0 : P 0 ⟨entryK rC3 rN3 (toWord ℓ) s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_, fun i hi => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only
      rw [hE _ (by simp only [rC3, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
    · dsimp only
      rw [show bflyRun ptK nLog 0 0 Y i = Y i from rfl, ← hY i hi]
      exact rdK_eq ((hE _ (by simp only [rC3]; omega) (by simp only [cTmp]; omega)).trans
        (hH0 _ (by simp only [regs]; omega)))
  have := iterL_ind (f := semXIR I (lvlStep ℓ)) (c := rC3) (m := ℓ) P step ℓ 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  exact ⟨this.2.2.2.2.2.2, this.2.2.2.2.2.1, this.1⟩

/-- **The inverse NTT computes the novel-basis coefficients** (`bflyRun_eq`): `coeffsAt` of the
values on `ptK [0, 2^ℓ)`. -/
theorem bflyIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I (bflyIR ℓ tb) s).M (A + i) = coeffsAt ptK nLog ℓ 0 Y i :=
  fun i hi => ((bflyIR_sem I s hM hℓ hA hA2 hsz htb htb2 hdisj hA0 hW hY).1 i hi).trans
    (bflyRun_eq ptK nLog 0 ℓ Y hi)

end Lvm.X
end

-- ===== from `LvmXNtt3` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

theorem wRow_zero_getD {i : ℕ} (hi : i < 15) : (wRow ptK nLog 0).getD i 0 = ptK (2 ^ i) := by
  simp [wRow, hi, List.getD_eq_getElem?_getD, ptK_zero, show ptK 1 = 1 from rfl]

theorem wRow_succ_getD (v : ℕ) {i : ℕ} (hi : i < 15) : (wRow ptK nLog (v + 1)).getD i 0 =
    (wRow ptK nLog v).getD i 0 * ((wRow ptK nLog v).getD i 0 + 1) *
      ((wRow ptK nLog v).getD (v + 1) 0 * ((wRow ptK nLog v).getD (v + 1) 0 + 1))⁻¹ := by
  rw [wRow]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, wRow_length]; exact hi), List.getElem_map,
    ← List.getD_eq_getElem _ 0]
  rfl

/-- One entry of row `0`: `ptK (2^i)` at `tb + i`. -/
theorem row0Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb i : ℕ} (hi : i < 15)
    (htb : regs ≤ tb) (htb2 : tb + 15 < 2 ^ 64) (hsz : tb + 15 ≤ s.M.size)
    (hI : rd s.M uI = toWord i) (hTa : rd s.M rTa = toWord (tb + i)) :
    rdK (semXIR I row0Body s).M (tb + i) = ptK (2 ^ i) ∧
    (∀ x, regs ≤ x → x ≠ tb + i → rd (semXIR I row0Body s).M x = rd s.M x) ∧
    rd (semXIR I row0Body s).M uI = toWord (i + 1) ∧
    rd (semXIR I row0Body s).M rTa = toWord (tb + (i + 1)) ∧
    rd (semXIR I row0Body s).M rTr = rd s.M rTr := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w1 : WF (.blk [.op .shl fG cOne uI]) := by simp +decide only [WF, Prim.dst, fG]
  have hM1 := inv_sem I w1 hM
  have hH1 := hframe I (.blk [.op .shl fG cOne uI]) s (by simp +decide only [Lo, Prim.dst, regs, fG])
  have r1 : rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M fG = toWord (2 ^ i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M rTa = toWord (tb + i) ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M uI = toWord i ∧
      rd (semXIR I (.blk [.op .shl fG cOne uI]) s).M rTr = rd s.M rTr := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, fG]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hI, show rd s.M cOne = toWord 1 from hM.2 0 (by decide), shl_toWord (by omega)
        (by rw [Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.one_mul]
    · exact hTa
    · exact hI
  rw [row0Body, semXIR_seq]
  have z1 := size_sem I (.blk [.op .shl fG cOne uI]) s
  generalize semXIR I (.blk [.op .shl fG cOne uI]) s = s1 at hM1 hH1 r1 z1
  obtain ⟨g1, a1, i1, t1⟩ := r1
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := rTa) (v := fG) (x := tb + i) (by decide)
    (by decide) a1 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.store rTa fG) s1 = s2 at c1 c2 hM2
  have hT4 : cTmp = 4 := rfl
  have hr2 : ∀ r, r < 256 → r ≠ cTmp → rd s2.M r = rd s1.M r := fun r hr h2 =>
    c2 r (by omega) h2
  have hb : ∀ x, x ≠ rTa → x ≠ uI → rd (semXIR I (.blk [.op .add rTa rTa cOne,
      .op .add uI uI cOne]) s2).M x = rd s2.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hs2 := hM2.1
  simp only [regs] at hs2
  refine ⟨?_, fun x hx x1 => ?_, ?_, ?_, ?_⟩
  · rw [rdK_eq (hb _ (by simp only [rTa]; omega) (by simp only [uI]; omega)), rdK_eq c1, rdK, g1]
    rfl
  · simp only [regs] at hx
    rw [hb _ (by simp only [rTa]; omega) (by simp only [uI]; omega), c2 _ x1 (by omega),
      hH1 x (by simp only [regs]; omega)]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide), i1, hr2 _ (by decide) (by decide),
      show rd s1.M cOne = 1 from hM1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa, uI]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr2 _ (by decide) (by decide), a1, hr2 _ (by decide) (by decide),
      show rd s1.M cOne = 1 from hM1.2 0 (by decide), add_one_toWord]
    rfl
  · rw [hb _ (by decide) (by decide), hr2 _ (by decide) (by decide), t1]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

/-- **Row `0`** at `rTr = tb`: `ptK (2^i)` at `tb + i`, `i < 15`. -/
theorem row0IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 15 < 2 ^ 64) (hsz : tb + 15 ≤ s.M.size) (hTr : rd s.M rTr = toWord tb) :
    (∀ i < 15, rdK (semXIR I row0IR s).M (tb + i) = ptK (2 ^ i)) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 15 ≤ x) → rd (semXIR I row0IR s).M x = rd s.M x) ∧
    rd (semXIR I row0IR s).M rTr = toWord tb ∧ Inv (semXIR I row0IR s).M ∧
    (semXIR I row0IR s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs htb
  have w0 : WF (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) := by
    simp +decide only [WF, Prim.dst, uI, rTa, rN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s
  have hH0 := hframe I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s
    (by simp +decide only [Lo, Prim.dst, regs, uI, rTa, rN2])
  have r0 : rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M uI =
        toWord 0 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M rTa =
        toWord (tb + 0) ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M rN2 = 15 ∧
      rd (semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s).M rTr =
        toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, uI, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hTr, or_self_eval]; rfl
    · exact hTr
  rw [row0IR, semXIR_seq]
  generalize semXIR I (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 15]) s = s0
    at hM0 z0 hH0 r0
  obtain ⟨i0, a0, n0, t0⟩ := r0
  rw [loopK_eq I row0Body s0 hM0 (by decide) (by decide) (by decide) n0]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 15 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 15) hM0 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M uI = toWord j ∧ rd s'.M rTa = toWord (tb + j) ∧ rd s'.M rTr = toWord tb ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + j ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < j, rdK s'.M (tb + i) = ptK (2 ^ i)
  have step : ∀ j s', j < 15 → P j s' → P (j + 1) (decS rC2 (semXIR I row0Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := row0Body_sem I s' i1 hj (by simp only [regs]; omega) htb2
      (by omega) i3 i4
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I row0Body s')).M x =
        rd (semXIR I row0Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS (inv_sem I wf_row0Body i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [hd _ (by decide), e4], by rw [hd _ (by decide), e5, i5],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i6 x (by simp only [regs]; omega) (by omega)]
    · rw [rdK_eq (hd _ (by simp only [rC2]; omega))]
      by_cases h : i = j
      · subst h; exact e1
      · rw [rdK_eq (e2 _ (by simp only [regs]; omega) (by omega)), i7 i (by omega)]
  have hP0 : P 0 ⟨entryK rC2 rN2 15 s0.M, s0.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z0], ?_, ?_, ?_, fun x hx _ => ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), i0]
    · dsimp only; rw [hE _ (by decide) (by decide), a0]
    · dsimp only; rw [hE _ (by decide) (by decide), t0]
    · dsimp only
      rw [hE _ (by simp only [rC2, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        hH0 x hx]
  have := iterL_ind (f := semXIR I row0Body) (c := rC2) (m := 15) P step 15 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6, f7⟩ := this
  exact ⟨f7, fun x hx hx2 => f6 x hx (by omega), f5, f1, f2⟩

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM

/-- **One entry of row `j + 1`**: `a (a + 1) c` at `ta + 15 + k`, `a` the entry at `ta + k`,
`c` in `fAl`. -/
theorem rowBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {ta k : ℕ} (hk : k < 15)
    (hta : regs ≤ ta) (hta2 : ta + 30 < 2 ^ 64) (hsz : ta + 30 ≤ s.M.size)
    (hTa : rd s.M rTa = toWord (ta + k)) :
    rdK (semXIR I rowBody s).M (ta + 15 + k) =
      rdK s.M (ta + k) * (rdK s.M (ta + k) + 1) * rdK s.M fAl ∧
    (∀ x, regs ≤ x → x ≠ ta + 15 + k → rd (semXIR I rowBody s).M x = rd s.M x) ∧
    rd (semXIR I rowBody s).M rTa = toWord (ta + (k + 1)) ∧
    rdK (semXIR I rowBody s).M fAl = rdK s.M fAl ∧
    rd (semXIR I rowBody s).M rTr = rd s.M rTr ∧ rd (semXIR I rowBody s).M rLv = rd s.M rLv := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- load `a`
  obtain ⟨u1, u3, hM1⟩ := load_sem I s hM (d := fU) (p := rTa) (by decide) (by decide) hTa
    (by omega)
  have y1 := size_sem I (.load fU rTa) s
  rw [rowBody, semXIR_seq]
  generalize semXIR I (.load fU rTa) s = s1 at u1 u3 hM1 y1
  -- `a + 1`
  obtain ⟨v1, v2⟩ := plusOne_sem I s1 hM1
  have hM2 := inv_sem I wf_plusOne hM1
  have y2 := size_sem I (.blk [.op .xor fW fU cOne]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne]) s1 = s2 at v1 v2 hM2 y2
  -- the products
  have m3 := mulK_sem (I := I) (s := s2) hM2 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 9 ≤ i → i ≠ fH → rd (semXIR I (mulK fH fU fW) s2).M i = rd s2.M i :=
    fun i h0 h1 => mulK_frame I s2 h0 h1
  have hM3 := inv_sem I (wf_mulK fH fU fW (by decide)) hM2
  have y3 := size_sem I (mulK fH fU fW) s2
  rw [semXIR_seq]
  generalize semXIR I (mulK fH fU fW) s2 = s3 at m3 f3 hM3 y3
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fN) (a := fH) (b := fAl) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fN → rd (semXIR I (mulK fN fH fAl) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fN fH fAl (by decide)) hM3
  have y4 := size_sem I (mulK fN fH fAl) s3
  rw [semXIR_seq]
  generalize semXIR I (mulK fN fH fAl) s3 = s4 at m4 f4 hM4 y4
  -- facts on `s4`
  have k4 : ∀ x, 256 ≤ x → rd s4.M x = rd s.M x := fun x hx => by
    rw [f4 x (by omega) (by simp only [fN]; omega), f3 x (by omega) (by simp only [fH]; omega),
      v2 x (by simp only [fW]; omega), u3 x (by simp only [fU]; omega)]
  have r4 : ∀ r, (r = rTa ∨ r = rTr ∨ r = rLv ∨ r = fAl) → rd s4.M r = rd s.M r :=
    fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
      rw [f4 _ (by decide) (by decide), f3 _ (by decide) (by decide), v2 _ (by decide),
        u3 _ (by decide)]
  have n4 : rdK s4.M fN = rdK s.M (ta + k) * (rdK s.M (ta + k) + 1) * rdK s.M fAl := by
    have al2 : rdK s2.M fAl = rdK s.M fAl :=
      rdK_eq ((v2 _ (by decide)).trans (u3 _ (by decide)))
    have al3 : rdK s3.M fAl = rdK s.M fAl := (rdK_eq (f3 _ (by decide) (by decide))).trans al2
    have fu2 : rdK s2.M fU = rdK s.M (ta + k) := (rdK_eq (v2 _ (by decide))).trans (rdK_eq u1)
    rw [m4, m3, v1, al3, fu2, rdK_eq u1]
  -- the address
  have hs4 := hM4.1
  simp only [regs] at hs4
  have a5 : rd (semXIR I (.blk [.const uT1 15, .op .add rAH rTa uT1]) s4).M rAH =
      toWord (ta + 15 + k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rAH]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [r4 _ (.inl rfl), hTa, show (15 : Word) = toWord 15 from rfl, add_toWord]
    congr 1; omega
  have b5 : ∀ x, x ≠ uT1 → x ≠ rAH → rd (semXIR I (.blk [.const uT1 15, .op .add rAH rTa uT1])
      s4).M x = rd s4.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM5 := inv_sem I (P := .blk [.const uT1 15, .op .add rAH rTa uT1])
    (by simp +decide only [WF, Prim.dst, uT1, rAH]) hM4
  have z5 := size_sem I (.blk [.const uT1 15, .op .add rAH rTa uT1]) s4
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const uT1 15, .op .add rAH rTa uT1]) s4 = s5 at a5 b5 hM5 z5
  -- the store
  obtain ⟨c1, c2, hM6⟩ := store_sem I s5 hM5 (p := rAH) (v := fN) (x := ta + 15 + k)
    (by decide) (by decide) a5 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (.store rAH fN) s5 = s6 at c1 c2 hM6
  have hr6 : ∀ r, r < 256 → r ≠ cTmp → rd s6.M r = rd s5.M r := fun r hr h2 =>
    c2 r (by omega) h2
  have hb : ∀ x, x ≠ rTa → rd (semXIR I (.blk [.op .add rTa rTa cOne]) s6).M x = rd s6.M x :=
    fun x h1 => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm h1) _
  have hs6 := hM6.1
  simp only [regs] at hs6
  refine ⟨?_, fun x hx x1 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdK_eq (hb _ (by simp only [rTa]; omega)), rdK_eq c1,
      rdK_eq (b5 _ (by decide) (by decide)), n4]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rTa]; omega), c2 _ x1 (by omega), b5 _ (by simp only [uT1]; omega)
      (by simp only [rAH]; omega), k4 x hx]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rTa]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hr6 _ (by decide) (by decide), b5 _ (by decide) (by decide), r4 _ (.inl rfl), hTa,
      hr6 _ (by decide) (by decide), show rd s5.M cOne = 1 from hM5.2 0 (by decide),
      add_one_toWord]
    rfl
  · exact rdK_eq ((hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inr rfl)))))))
  · exact (hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inl rfl)))))
  · exact (hb _ (by decide)).trans ((hr6 _ (by decide) (by decide)).trans
      ((b5 _ (by decide) (by decide)).trans (r4 _ (.inr (.inr (.inl rfl))))))

set_option maxRecDepth 8000 in
/-- **Row `j + 1`** from row `j` (`R`, at `ta = rTr`; `rLv = j`, `j + 1 < 15`):
`R i (R i + 1) (b (b + 1))⁻¹` at `ta + 15 + i`, `b = R (j + 1)`. -/
theorem rowIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ta j : ℕ} {R : ℕ → BF64}
    (hj : j + 1 < 15) (hta : regs ≤ ta) (hta2 : ta + 30 < 2 ^ 64) (hsz : ta + 30 ≤ s.M.size)
    (hLv : rd s.M rLv = toWord j) (hTr : rd s.M rTr = toWord ta)
    (hR : ∀ i < 15, rdK s.M (ta + i) = R i) :
    (∀ i < 15, rdK (semXIR I rowIR s).M (ta + 15 + i) =
      R i * (R i + 1) * (R (j + 1) * (R (j + 1) + 1))⁻¹) ∧
    (∀ x, regs ≤ x → (x < ta + 15 ∨ ta + 30 ≤ x) → rd (semXIR I rowIR s).M x = rd s.M x) ∧
    rd (semXIR I rowIR s).M rLv = toWord (j + 1) ∧ rd (semXIR I rowIR s).M rTr = toWord (ta + 15) ∧
    Inv (semXIR I rowIR s).M ∧ (semXIR I rowIR s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hta
  have hT4 : cTmp = 4 := rfl
  -- `rTa := ta + (j + 1)`
  have r1 : rd (semXIR I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s).M rTa =
      toWord (ta + (j + 1)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, uT1, rTa]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hLv, hTr, show rd s.M cOne = 1 from hM.2 0 (by decide), add_one_toWord, add_toWord]
  have b1 : ∀ x, x ≠ uT1 → x ≠ rTa → rd (semXIR I (.blk [.op .add uT1 rLv cOne,
      .op .add rTa rTr uT1]) s).M x = rd s.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM1 := inv_sem I (P := .blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1])
    (by simp +decide only [WF, Prim.dst, uT1, rTa]) hM
  have y1 := size_sem I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s
  rw [rowIR, semXIR_seq]
  generalize semXIR I (.blk [.op .add uT1 rLv cOne, .op .add rTa rTr uT1]) s = s1 at r1 b1 hM1 y1
  -- `b`
  obtain ⟨u1, u3, hM2⟩ := load_sem I s1 hM1 (d := fU) (p := rTa) (by decide) (by decide) r1
    (by omega)
  have y2 := size_sem I (.load fU rTa) s1
  rw [semXIR_seq]
  generalize semXIR I (.load fU rTa) s1 = s2 at u1 u3 hM2 y2
  have hb2 : rdK s2.M fU = R (j + 1) := by
    rw [rdK_eq u1, ← hR (j + 1) hj]
    exact rdK_eq (b1 _ (by simp only [uT1]; omega) (by simp only [rTa]; omega))
  obtain ⟨v1, v2⟩ := plusOne_sem I s2 hM2
  have hM3 := inv_sem I wf_plusOne hM2
  have y3 := size_sem I (.blk [.op .xor fW fU cOne]) s2
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .xor fW fU cOne]) s2 = s3 at v1 v2 hM3 y3
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fH) (a := fU) (b := fW) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ i, 9 ≤ i → i ≠ fH → rd (semXIR I (mulK fH fU fW) s3).M i = rd s3.M i :=
    fun i h0 h1 => mulK_frame I s3 h0 h1
  have hM4 := inv_sem I (wf_mulK fH fU fW (by decide)) hM3
  have y4 := size_sem I (mulK fH fU fW) s3
  rw [semXIR_seq]
  generalize semXIR I (mulK fH fU fW) s3 = s4 at m4 f4 hM4 y4
  have i5 := invK_sem (I := I) (s := s4) hM4 (d := fAl) (a := fH) (by decide) (by decide)
  have f5 : ∀ i, 12 ≤ i → i ≠ fAl → rd (semXIR I (invK fAl fH) s4).M i = rd s4.M i :=
    fun i h0 h1 => by rw [invK, sem_blk]; exact invKC_frame _ _ (.inr h0) h1 _
  have hM5 := inv_sem I (wf_invK fAl fH (by decide)) hM4
  have y5 := size_sem I (invK fAl fH) s4
  rw [semXIR_seq]
  generalize semXIR I (invK fAl fH) s4 = s5 at i5 f5 hM5 y5
  have c5 : rdK s5.M fAl = (R (j + 1) * (R (j + 1) + 1))⁻¹ := by
    rw [i5, m4, v1, rdK_eq (v2 _ (by decide)), hb2]
  have k5 : ∀ x, 256 ≤ x → rd s5.M x = rd s.M x := fun x hx => by
    rw [f5 x (by omega) (by simp only [fAl]; omega), f4 x (by omega) (by simp only [fH]; omega),
      v2 x (by simp only [fW]; omega), u3 x (by simp only [fU]; omega),
      b1 x (by simp only [uT1]; omega) (by simp only [rTa]; omega)]
  have r5 : ∀ r, (r = rTr ∨ r = rLv) → rd s5.M r = rd s.M r := fun r hr => by
    rcases hr with rfl | rfl <;>
    rw [f5 _ (by decide) (by decide), f4 _ (by decide) (by decide), v2 _ (by decide),
      u3 _ (by decide), b1 _ (by decide) (by decide)]
  -- the entries
  have hs5 := hM5.1
  simp only [regs] at hs5
  have r6 : rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5).M rTa = toWord (ta + 0) ∧
      rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5).M rN2 = 15 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rTa, rN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [r5 _ (.inl rfl), hTr, or_self_eval]; rfl
  have b6 : ∀ x, x ≠ rTa → x ≠ rN2 → rd (semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15])
      s5).M x = rd s5.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM6 := inv_sem I (P := .blk [.op .or rTa rTr rTr, .const rN2 15])
    (by simp +decide only [WF, Prim.dst, rTa, rN2]) hM5
  have y6 := size_sem I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .or rTa rTr rTr, .const rN2 15]) s5 = s6 at r6 b6 hM6 y6
  obtain ⟨a6, n6⟩ := r6
  rw [semXIR_seq, loopK_eq I rowBody s6 hM6 (by decide) (by decide) (by decide) n6]
  have hE : ∀ i, i ≠ rC2 → i ≠ cTmp → rd (entryK rC2 rN2 15 s6.M) i = rd s6.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC2) (n := rN2) (K := 15) hM6 (by decide)
  let c := (R (j + 1) * (R (j + 1) + 1))⁻¹
  let P : ℕ → St → Prop := fun k s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rTa = toWord (ta + k) ∧ rdK s'.M fAl = c ∧ rd s'.M rTr = toWord ta ∧
    rd s'.M rLv = toWord j ∧
    (∀ x, regs ≤ x → (x < ta + 15 ∨ ta + 15 + k ≤ x) → rd s'.M x = rd s.M x) ∧
    ∀ i < k, rdK s'.M (ta + 15 + i) = R i * (R i + 1) * c
  have step : ∀ k s', k < 15 → P k s' → P (k + 1) (decS rC2 (semXIR I rowBody s')) := by
    rintro k s' hk ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowBody_sem I s' i1 hk (by simp only [regs]; omega) hta2
      (by omega) i3
    have hd : ∀ x, x ≠ rC2 → rd (decS rC2 (semXIR I rowBody s')).M x =
        rd (semXIR I rowBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hRk : rdK s'.M (ta + k) = R k := by
      rw [← hR k hk]
      exact rdK_eq (i7 _ (by simp only [regs]; omega) (by omega))
    refine ⟨inv_decS (inv_sem I wf_rowBody i1) (by decide), by rw [size_decS, size_sem, i2],
      by rw [hd _ (by decide), e3], by rw [rdK_decS _ (by decide), e4, i4],
      by rw [hd _ (by decide), e5, i5], by rw [hd _ (by decide), e6, i6],
      fun x hx hx2 => ?_, fun i hi => ?_⟩
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC2]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i7 x (by simp only [regs]; omega) (by omega)]
    · rw [rdK_eq (hd _ (by simp only [rC2]; omega))]
      by_cases h : i = k
      · subst h; rw [e1, hRk, i4]
      · rw [rdK_eq (e2 _ (by simp only [regs]; omega) (by omega)), i8 i (by omega)]
  have hP0 : P 0 ⟨entryK rC2 rN2 15 s6.M, s6.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, y6, y5, y4, y3, y2, y1], ?_, ?_, ?_, ?_,
      fun x hx _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · dsimp only; rw [hE _ (by decide) (by decide), a6]
    · dsimp only
      rw [rdK_eq ((hE _ (by decide) (by decide)).trans (b6 _ (by decide) (by decide))), c5]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inl rfl), hTr]
    · dsimp only
      rw [hE _ (by decide) (by decide), b6 _ (by decide) (by decide), r5 _ (.inr rfl), hLv]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC2]; omega) (by omega), b6 _ (by simp only [rTa]; omega)
        (by simp only [rN2]; omega), k5 x hx]
  have := iterL_ind (f := semXIR I rowBody) (c := rC2) (m := 15) P step 15 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  rw [show (15 : Word).toNat = 15 from rfl]
  generalize iterL (semXIR I rowBody) rC2 15 ⟨entryK rC2 rN2 15 s6.M, s6.o⟩ = s7 at this ⊢
  obtain ⟨g1, g2, -, -, g5, g6, g7, g8⟩ := this
  have hs7 := g1.1
  simp only [regs] at hs7
  have hb : ∀ x, x ≠ rLv → x ≠ uT1 → x ≠ rTr → rd (semXIR I (.blk [.op .add rLv rLv cOne,
      .const uT1 15, .op .add rTr rTr uT1]) s7).M x = rd s7.M x := fun x h1 h2 h3 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩) _
  have wfin : WF (.blk [.op .add rLv rLv cOne, .const uT1 15, .op .add rTr rTr uT1]) := by
    simp +decide only [WF, Prim.dst, rLv, uT1, rTr]
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, ?_, ?_, inv_sem I wfin g1, ?_⟩
  rotate_left 4
  · rw [size_sem, g2]
  · rw [rdK_eq (hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega)
      (by simp only [rTr]; omega)), g8 i hi]
  · simp only [regs] at hx
    rw [hb _ (by simp only [rLv]; omega) (by simp only [uT1]; omega) (by simp only [rTr]; omega),
      g7 x (by simp only [regs]; omega) (by omega)]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [g6, show rd s7.M cOne = 1 from g1.2 0 (by decide), add_one_toWord]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rLv, uT1, rTr]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [g5, show (15 : Word) = toWord 15 from rfl, add_toWord]

/-- **The basis table** (`wtabIR tb`): the rows `wRow ptK 15 v`, `v < 15`, at `tb + 15 v + i`;
the heap outside `[tb, tb + 225)` is kept. -/
theorem wtabIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 225 < 2 ^ 64) (hsz : tb + 225 ≤ s.M.size) :
    (∀ v < nLog, ∀ i < nLog, rdK (semXIR I (wtabIR tb) s).M (tb + 15 * v + i) =
      (wRow ptK nLog v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 225 ≤ x) → rd (semXIR I (wtabIR tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (wtabIR tb) s).M ∧ (semXIR I (wtabIR tb) s).M.size = s.M.size := by
  have hs := hM.1
  have hN : nLog = 15 := rfl
  simp only [regs] at hs htb
  have hT4 : cTmp = 4 := rfl
  have w0 : WF (.blk [.const rTr (toWord tb)]) := by simp +decide only [WF, Prim.dst, rTr,
    List.mem_cons, List.mem_nil_iff, forall_eq, or_false]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const rTr (toWord tb)]) s
  have hH0 := hframe I (.blk [.const rTr (toWord tb)]) s (by simp +decide only [Lo, Prim.dst, regs,
    rTr, List.mem_cons, List.mem_nil_iff, forall_eq, or_false])
  have t0 : rd (semXIR I (.blk [.const rTr (toWord tb)]) s).M rTr = toWord tb := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rTr]; omega)
  rw [wtabIR, semXIR_seq]
  generalize semXIR I (.blk [.const rTr (toWord tb)]) s = s0 at hM0 z0 hH0 t0
  obtain ⟨o1, o2, o3, hM1, z1⟩ := row0IR_sem I s0 hM0 (by simp only [regs]; omega) (by omega)
    (by omega) t0
  rw [semXIR_seq]
  generalize semXIR I row0IR s0 = s1 at o1 o2 o3 hM1 z1
  have r2 : rd (semXIR I (.blk [.const rLv 0, .const rN3 14]) s1).M rLv = toWord 0 ∧
      rd (semXIR I (.blk [.const rLv 0, .const rN3 14]) s1).M rN3 = 14 := by
    have := hM1.1; simp only [regs] at this
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLv, rN3]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have b2 : ∀ x, x ≠ rLv → x ≠ rN3 → rd (semXIR I (.blk [.const rLv 0, .const rN3 14]) s1).M x =
      rd s1.M x := fun x h1 h2 =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM2 := inv_sem I (P := .blk [.const rLv 0, .const rN3 14]) (by simp +decide only [WF,
    Prim.dst, rLv, rN3]) hM1
  have z2 := size_sem I (.blk [.const rLv 0, .const rN3 14]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rLv 0, .const rN3 14]) s1 = s2 at r2 b2 hM2 z2
  obtain ⟨l2, n2⟩ := r2
  rw [loopK_eq I rowIR s2 hM2 (by decide) (by decide) (by decide) n2,
    show (14 : Word).toNat = 14 from rfl]
  have hE : ∀ i, i ≠ rC3 → i ≠ cTmp → rd (entryK rC3 rN3 14 s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME := inv_entryK (c := rC3) (n := rN3) (K := 14) hM2 (by decide)
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M rLv = toWord j ∧ rd s'.M rTr = toWord (tb + 15 * j) ∧
    (∀ v ≤ j, ∀ i < 15, rdK s'.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0) ∧
    (∀ x, regs ≤ x → (x < tb ∨ tb + 15 * (j + 1) ≤ x) → rd s'.M x = rd s.M x)
  have step : ∀ j s', j < 14 → P j s' → P (j + 1) (decS rC3 (semXIR I rowIR s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rowIR_sem I s' i1 (ta := tb + 15 * j)
      (R := fun i => (wRow ptK nLog j).getD i 0) (by omega) (by simp only [regs]; omega)
      (by omega) (by omega) i3 i4 (fun i hi => i5 j le_rfl i hi)
    have hd : ∀ x, x ≠ rC3 → rd (decS rC3 (semXIR I rowIR s')).M x =
        rd (semXIR I rowIR s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS e5 (by decide), by rw [size_decS, e6, i2], by rw [hd _ (by decide), e3],
      by rw [hd _ (by decide), e4, show tb + 15 * j + 15 = tb + 15 * (j + 1) by ring],
      fun v hv i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [rdK_eq (hd _ (by simp only [rC3]; omega))]
      by_cases h : v = j + 1
      · subst h
        rw [show tb + 15 * (j + 1) + i = tb + 15 * j + 15 + i by ring, e1 i hi,
          wRow_succ_getD j hi]
      · rw [rdK_eq (e2 _ (by simp only [regs]; omega) (by omega)), i5 v (by omega) i hi]
    · simp only [regs] at hx
      rw [hd _ (by simp only [rC3]; omega), e2 x (by simp only [regs]; omega) (by omega),
        i6 x (by simp only [regs]; omega) (by omega)]
  have hP0 : P 0 ⟨entryK rC3 rN3 14 s2.M, s2.o⟩ := by
    refine ⟨hME, by simp only [size_entryK, z2, z1, z0], ?_, ?_, fun v hv i hi => ?_,
      fun x hx hx2 => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), l2]
    · dsimp only
      rw [hE _ (by decide) (by decide), b2 _ (by decide) (by decide), o3]; rfl
    · obtain rfl : v = 0 := by omega
      dsimp only
      rw [rdK_eq ((hE _ (by simp only [rC3]; omega) (by omega)).trans
          (b2 _ (by simp only [rLv]; omega) (by simp only [rN3]; omega))),
        Nat.mul_zero, Nat.add_zero, o1 i hi, wRow_zero_getD hi]
    · dsimp only
      simp only [regs] at hx
      rw [hE _ (by simp only [rC3]; omega) (by omega), b2 _ (by simp only [rLv]; omega)
        (by simp only [rN3]; omega), o2 x (by simp only [regs]; omega) (by omega),
        hH0 x (by simp only [regs]; omega)]
  have := iterL_ind (f := semXIR I rowIR) (c := rC3) (m := 14) P step 14 0 _ (by omega) hP0
  rw [Nat.zero_add] at this
  obtain ⟨f1, f2, -, -, f5, f6⟩ := this
  exact ⟨fun v hv i hi => f5 v (by omega) i (by omega), fun x hx hx2 => f6 x hx (by omega), f1, f2⟩

/-- **The table holds `Ŵ_v(ptK 2^i)`** (`Lvm.Nb.wRow_spec`). -/
theorem wtabIR_normW (I : Array Word) (s : St) (hM : Inv s.M) {tb : ℕ} (htb : regs ≤ tb)
    (htb2 : tb + 225 < 2 ^ 64) (hsz : tb + 225 ≤ s.M.size) :
    ∀ v < nLog, ∀ i < nLog, rdK (semXIR I (wtabIR tb) s).M (tb + 15 * v + i) =
      (Lvm.Nb.normW ptK v).eval (ptK (2 ^ i)) := fun v hv i hi => by
  rw [(wtabIR_sem I s hM htb htb2 hsz).1 v hv i hi, wRow_spec ptK_xor ptK_injOn15 v hv i hi]

end Lvm.X
end

-- ===== from `LvmXSOut` =====

section
set_option autoImplicit false
namespace Lvm.XS
open RecursionFast Lvm Lvm.X

set_option maxRecDepth 200000 in
/-- S2GF's output facts, in one kernel evaluation (the blocks, the plan's flag and the sums once; `|π|` from
`checks_P20F`, not re-evaluated). -/
theorem outOK_all :
    (Replay.planItems stF20.p Replay.w0 stF20.items).2.ok = true ∧
    (blocksS stF20).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true ∧
    8 + 8 * ((blocksS stF20).map blkPOutsL).sum = stF20.pz ∧ 4928 ≤ stF20.pz ∧ stF20.pz < 2 ^ 64 ∧
    6 + ((blocksS stF20).map Blk.lanes).sum ≤ nCp ∧ qSS stF20 < 2 ^ 64 ∧
    ((blocksS stF20).map blkPCostL).sum + ((blocksS stF20).map blkTCostL).sum ≤ 7128485 ∧
    ((blocksS stF20).map blkPOutsL).sum + ((blocksS stF20).map blkTOutsL).sum ≤ 163533 ∧
    ((blocksS stF20).map blkPSizeL).sum + ((blocksS stF20).map blkTSizeL).sum ≤ 250000 := by
  rw [show stF20.pz = 306992 from checks_P20F.1.1]
  decide +kernel

/-- S2GF's output facts. -/
theorem outOK_stF20 : OutOK stF20 :=
  let h := outOK_all
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

end Lvm.XS
end

-- ===== from `LvmXSComputes` =====

section
set_option autoImplicit false
namespace Lvm.XS
open RecursionFast Lvm Lvm.X

/-- S2GF's static facts (one `decide +kernel`; `|π|` enters as its value `checks_P20F` proved, so the kernel does
not evaluate the schedule's tally again). -/
theorem progFacts_stF20 : stF20.occ0 ≤ 64 ∧ 306992 < 2 ^ 32 ∧ nChainS stF20 < 2 ^ 11 ∧
    nChainS stF20 ≤ (fsMsgsS stF20).length ∧
    ((fsMsgsS stF20).take (nChainS stF20)).all (msgOkP 306992) = true ∧
    (fsMsgsS stF20).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS stF20 k < nChainS stF20) ∧
    capOffS stF20 0 / 8 + 4 * 2 ^ 8 ≤ 306992 / 8 ∧ capOffS stF20 1 / 8 + 4 * 2 ^ 7 ≤ 306992 / 8 ∧
    capOffS stF20 2 / 8 + 4 * 2 ^ 7 ≤ 306992 / 8 ∧ resOffS stF20 / 8 + 3 * 2 ^ 9 ≤ 306992 / 8 ∧
    capWS stF20 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS stF20 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS stF20 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS stF20 + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 306992 ≤ 2 ^ 60 ∧ 15 ≤ 306992 / 8 := by
  decide +kernel

/-- S2GF's `|π|`. -/
theorem stF20_pz : stF20.pz = 306992 := checks_P20F.1.1

/-- S2GF's program facts. -/
theorem progOK_stF20 : ProgOK stF20 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := progFacts_stF20
  have e : msgOkS stF20 = msgOkP 306992 := by funext m; rw [msgOkS, stF20_pz]
  exact ⟨outOK_stF20, h1, stF20_pz ▸ h2, h3, h4, e ▸ h5, h6, h7, stF20_pz ▸ h8, stF20_pz ▸ h9, stF20_pz ▸ h10,
    stF20_pz ▸ h11, h12, h13, h14, h15, by show posL stF20.pz ≤ 2 ^ 60; rw [stF20_pz]; exact h16, stF20_pz ▸ h17⟩

end Lvm.XS
end
