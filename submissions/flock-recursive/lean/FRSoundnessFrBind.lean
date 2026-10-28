-- New for `flock-recursive` (BLUEPRINT A.10 Z3 → RS0, L3β → RS0, §5.2; stage S-G8).
import FRSoundnessFrL
import FRSoundnessFrS

/-!
# The pending Z and Lc claims as RS0's `PendBad`

* **`trueL_zero`**: RS claim 1's true value (the `rsW` weights `eqZS(λ, ρ₁)` on the low 7
  coordinates, `eq` at Z1's point on the high `m − 7`) is `P^z(λ)` at Z1's point, the true value
  of the c-claim (`pzT`). The bit index splits as `σ + 64 b + 128 v` against `u′ = b + 2 v`.
* **`pendZ_pendBad`**: Z's pending doom (`PendZ`) is RS0's `PendBad (okRS oZ oSh)` at claim 1.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## RS claim 1's true value -/

/-- Z's slice table on bit positions: `z(σ, u) = z[σ + 64 u]`. -/
theorem zZ_eq (ℓ : ℕ) (κ : Kind) (L es : Log) (σ : Fin 64) (u : Fin (2 ^ ℓ)) :
    zZ ℓ κ L es σ u = zW κ L es (σ.val + 64 * u.val) := by
  simp only [zZ, zBk, pAt]
  congr 1
  have := Nat.div_add_mod u.val 256
  norm_num
  omega

/-- RS claim 1's inner weight: the Lagrange weight of the low 6 bits times `eq(ρ₁, ·)` at bit 6. -/
theorem cwL_zero (κ : Kind) (es : Log) {σ y : ℕ} (hσ : σ < 64) (hy : y < 2) :
    cwL κ es 0 (σ + 64 * y) = lagrangeWeight sNodeF (lamL es) ⟨σ, hσ⟩ *
      eqAtR (ptOf 1 [pinnedRho 0]) y := by
  have hi : σ + 64 * y < 128 := by omega
  have hb : (σ + 64 * y).testBit 6 = y.testBit 0 := by
    have h6 : (σ + 64 * y) / 2 ^ 6 = y := by norm_num; omega
    rw [show (6 : ℕ) = 0 + 6 from rfl, ← Nat.testBit_div_two_pow, h6]
  have hm : (σ + 64 * y) % 64 = σ := by omega
  show (eqZS (fAt es 14 0) (pinnedRho 0)).getD (σ + 64 * y) 0 = _
  simp only [eqZS, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true,
    Option.getD_some, hb, hm, eqAtR, Fin.prod_univ_one, Fin.val_zero, ptOf, List.getD_cons_zero]
  rfl

theorem zPtL_length (κ : Kind) (es : Log) : (zPtL κ.m es).length = nrP 0 κ := by
  rw [nrP_zero, zPtL]; cases κ <;> simp [Kind.m]

theorem zrL_drop (es : Log) : (zrL es).drop 1 = zPtL (kindOf es).m es := by
  simp only [zrL, zPtL]
  rw [List.drop_append_of_le_length (by simp)]

/-- **RS claim 1's true value is `P^z(λ)` at Z1's point** (the c-claim's true value). -/
theorem trueL_zero (L es : Log) : trueL (kindOf es) L es 0 = (pzT L es).eval (lamL es) := by
  have hzd := zrL_drop es
  simp only [pzT, pzPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    skipExt_eval]
  generalize kindOf es = κ at hzd ⊢
  have hm := kind_m κ
  have hℓ : mm 6 κ = 1 + nrP 0 κ := by rw [mm6_eq, nrP_zero]; omega
  set zr := zrL es
  set zP := zPtL κ.m es
  have hzP : zP.length = (nrP 0 κ) := zPtL_length κ es
  -- the weights and the slices as functions of ℕ
  have hg : ∀ u : Fin (2 ^ (nrP 0 κ)), gL κ es 0 u = eqAtR (ptOf (nrP 0 κ) zP) u := by
    intro u
    have hl : (rsPtsL κ es).getD 0 [] = zP := by cases κ <;> rfl
    have h0 : (0 : ℕ) < (rsPtsL κ es).length := by rw [rsPtsL_length]; split_ifs <;> norm_num
    rw [gL, Fin.val_zero, if_pos h0, if_neg (show (0 : ℕ) ≠ 1 by norm_num), mul_one, hl, eqPts_eq _ _ hzP (by simp [bitsL, hzP]), hzP,
      ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (nrP 0 κ))), algebraMap F F (rsQ κ L es (nrP 0 κ) i u) =
      zW κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [rsQ, zW, Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  set lw : ℕ → F := fun σ => lagrangeWeight sNodeF (lamL es) ⟨σ % 64, Nat.mod_lt _ (by norm_num)⟩
  -- the left side over `q < 2^(nrP 0 κ)`, `y < 2`, `σ < 64`
  have hL : trueL κ L es 0 = ∑ q ∈ range (2 ^ (nrP 0 κ)), ∑ y ∈ range 2, ∑ σ ∈ range 64,
      lw σ * eqAtR (ptOf 1 [pinnedRho 0]) y * eqAtR (ptOf (nrP 0 κ) zP) q *
        zW κ L es (σ + 64 * y + 2 ^ 7 * q) := by
    unfold trueL
    simp only [hg, hq, mul_sum, Fin.val_zero]
    rw [sum_comm]
    rw [Fin.sum_univ_eq_sum_range (fun q => ∑ i : Fin 128, cwL κ es 0 i *
      (eqAtR (ptOf (nrP 0 κ) zP) q * zW κ L es (i + 2 ^ 7 * q)))]
    refine sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => cwL κ es 0 i *
      (eqAtR (ptOf (nrP 0 κ) zP) q * zW κ L es (i + 2 ^ 7 * q))), show (128 : ℕ) = 64 * 2 from rfl,
      sum_range_mul_split]
    refine sum_congr rfl fun y hy => sum_congr rfl fun σ hσ => ?_
    rw [mem_range] at hy hσ
    rw [cwL_zero κ es hσ hy]
    simp only [lw, Nat.mod_eq_of_lt hσ]
    ring
  -- the right side
  have hR : ∑ u : Fin (2 ^ mm 6 κ), eq (ptOf (mm 6 κ) zr) (cube u) *
      ∑ σ : Fin 64, lagrangeWeight (fun b : Fin 64 => skipNode (Fin.castLE (by norm_num) b))
        (lamL es) σ * zZ (mm 6 κ) κ L es σ u =
      ∑ u ∈ range (2 ^ (1 + (nrP 0 κ))), eqAtR (ptOf (1 + (nrP 0 κ)) zr) u *
        ∑ σ ∈ range 64, lw σ * zW κ L es (σ + 64 * u) := by
    rw [← hℓ, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf (mm 6 κ) zr) u *
      ∑ σ ∈ range 64, lw σ * zW κ L es (σ + 64 * u))]
    refine sum_congr rfl fun u _ => ?_
    rw [eq_cube_eqAtR, ← Fin.sum_univ_eq_sum_range (fun σ => lw σ * zW κ L es (σ + 64 * u))]
    refine congrArg _ (sum_congr rfl fun σ _ => ?_)
    rw [zZ_eq]
    simp only [lw, Nat.mod_eq_of_lt σ.isLt]
    rfl
  rw [hR, sum_eqAtR_split, hL, hzd]
  refine sum_congr rfl fun q _ => ?_
  rw [pow_one]
  refine sum_congr rfl fun y _ => ?_
  have h1 : ptOf 1 zr = ptOf 1 [pinnedRho 0] := by
    funext l; fin_cases l; simp [ptOf, zr, zrL, List.getD_eq_getElem?_getD]
  rw [h1, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [show σ + 64 * y + 2 ^ 7 * q = σ + 64 * (y + 2 ^ 1 * q) by ring]
  ring

/-- **Z's pending doom is RS0's `PendBad` at claim 1** (`oZ`: the value is `P^z*(λ)`). -/
theorem pendZ_pendBad {oSh : Kind → Log → F → Prop} {L es : Log} (h : PendZ L es) :
    PendBad (okRS oZ oSh) L es :=
  ⟨0, by rw [rsPtsL_length]; split_ifs <;> norm_num, fun ho => h.2 (by
    have ho' : trueL (kindOf es) L es 0 = pzStar es := ho
    rw [← trueL_zero, ho'])⟩

end FR.Snd
