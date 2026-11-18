-- New for lvm2 (WP T-V): S2's WHIR openings (FRZ-0 §2.1, row `LvmWhirParams`): `C_main` at ν = 24 (P20)
-- and S2's P8 test set (`C_main` ν = 23 with three levels, `C_rec` ν = 18), their unique-decoding codes
-- and per-group error bounds, by `norm_num` on natural numbers, with v1's helpers from `LvmWhirParams`.
/-
  LeanVM.Protocol.Whir.Sound (lvm2 S2 parameters)

  The configurations `cfgMain24`, `cfgMain23`, `cfgRec18`, their codes, the arithmetic
  `LadderArithUd`, the escape bounds `whirEpsUd ≤ 2^-129` (P20) and `≤ 2^-20` (P8), and the
  stacked-opening specifications at those parameters. `C_rec` at P20 stays v1's `cfgRec20`.
-/

import LvmWhirParams

-- (GOLF2: 9 declarations that `certified` does not use moved verbatim to `LvmWhirSuffixROff`, outside its import closure.)

/-!
# lvm2's S2 WHIR parameters

| opening | `μ` | levels `(ℓ, R, t)` | `κ_i` | root `c₀` of `n₀` |
|---|---|---|---|---|
| `cfgMain24` (`C_main`, P20) | 24 | (6,1,311) (4,2,191) (4,3,156) | 18 14 10 | 0 of 2 |
| `cfgRec20` (`C_rec`, P20, v1) | 19 | (6,2,191) | 13 | 1 of 2 |
| `cfgMain23` (`C_main`, P8) | 23 | (6,1,49) (4,2,30) (4,3,25) | 17 13 9 | 0 of 2 |
| `cfgRec18` (`C_rec`, P8) | 18 | (6,2,30) | 12 | 1 of 2 |

As in v1: 8 positions per challenge, `direct = false`, every level's code `LevelCode.ud κ_i R_i`;
the final residuals are `2^10` (`cfgMain24`), `2^9` (`cfgMain23`) and `2^12` (`cfgRec18`) scalars.
`C_main` is root 0 and `C_rec` root 1 of `n₀ = 2`, exactly as v1.

Per-group bounds at P20 (A13):

* fold, per challenge: `eFold ≤ 2^-151, 2^-160, 2^-167` (exact `2^-152.0`, `2^-160.4`, `2^-167.2`;
  level 0's numerator `2^40 + 2^24 + 2` is just above `2^40`, hence 151);
* positions and query groups (with `λ`) `≤ 2^-129` at `t = 311, 191, 156`;
* `whirEpsUd ≤ 2^-129`. At P8 (20-bit test set) `≤ 2^-20`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

-- The positions' bounds raise `(A − 1)` to the query counts (up to 311): let `norm_num` evaluate them.
set_option exponentiation.threshold 512

section

/-! ## The configurations -/

/-- `C_main` at S2 P20: `μ = 24`, levels `(6,1,311) (4,2,191) (4,3,156)`, root `0` of `2`. -/
def cfgMain24 : UdConfig := ⟨24, [⟨6, 1, 311⟩, ⟨4, 2, 191⟩, ⟨4, 3, 156⟩], 8, 0, 2, false, 0⟩

/-- `C_main` at S2 P8: `μ = 23`, levels `(6,1,49) (4,2,30) (4,3,25)`, root `0` of `2`. -/
def cfgMain23 : UdConfig := ⟨23, [⟨6, 1, 49⟩, ⟨4, 2, 30⟩, ⟨4, 3, 25⟩], 8, 0, 2, false, 0⟩

/-- `C_rec` at S2 P8: `μ = 18`, one level `(6,2,30)`, final `2^12` scalars, root `1` of `2`. -/
def cfgRec18 : UdConfig := ⟨18, [⟨6, 2, 30⟩], 8, 1, 2, false, 0⟩

/-- The UD codes of `C_main` at S2 P20: `κ = 18, 14, 10`, `R = 1, 2, 3`. -/
noncomputable def codesMain24 : ℕ → LevelCode
  | 0 => LevelCode.ud 18 1 (by norm_num) (by norm_num) (by norm_num)
  | 1 => LevelCode.ud 14 2 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 10 3 (by norm_num) (by norm_num) (by norm_num)

/-- The UD codes of `C_main` at S2 P8: `κ = 17, 13, 9`, `R = 1, 2, 3`. -/
noncomputable def codesMain23 : ℕ → LevelCode
  | 0 => LevelCode.ud 17 1 (by norm_num) (by norm_num) (by norm_num)
  | 1 => LevelCode.ud 13 2 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)

/-- The UD codes of `C_rec` at S2 P8: `κ = 12`, `R = 2`; level 1 (S4) `κ = 8`, `R = 3`. -/
noncomputable def codesRec18 : ℕ → LevelCode
  | 0 => LevelCode.ud 12 2 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 8 3 (by norm_num) (by norm_num) (by norm_num)

/-! ## P20: per-group bounds (A13) -/

/-- The query groups (positions and `λ`) of `C_main` at S2 P20. -/
theorem eQuery_main24 :
    eQueryUd (codesMain24 0) (codesMain24 1) 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryUd (codesMain24 1) (codesMain24 2) 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryFinal (codesMain24 2) 156 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_⟩ <;>
    simp only [udThr] <;> norm_num

/-- **The levels' arithmetic of `C_main` at S2 P20.** -/
theorem ladderArith_main24 :
    LadderArithUd cfgMain24.μ cfgMain24.per codesMain24 0 0 cfgMain24.levels := by
  obtain ⟨q0, q1, q2⟩ := eQuery_main24
  have h := inv_two_pow_lt_one (c := 129) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain24, codesMain24], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgMain24, codesMain24], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain24, codesMain24]⟩

/-! ## S2 P8: the test set, `2^-20` -/

/-- The query groups of S2 P8 (for the arithmetic). -/
theorem eQuery_P8s2 :
    eQueryUd (codesMain23 0) (codesMain23 1) 49 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryUd (codesMain23 1) (codesMain23 2) 30 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryFinal (codesMain23 2) 25 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryFinal (codesRec18 0) 30 ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eQueryFinal_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- **The levels' arithmetic of `C_main` at S2 P8.** -/
theorem ladderArith_main23 :
    LadderArithUd cfgMain23.μ cfgMain23.per codesMain23 0 0 cfgMain23.levels := by
  obtain ⟨q0, q1, q2, -⟩ := eQuery_P8s2
  have h := inv_two_pow_lt_one (c := 20) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain23, codesMain23], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgMain23, codesMain23], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain23, codesMain23]⟩

/-- **The levels' arithmetic of `C_rec` at S2 P8.** -/
theorem ladderArith_rec18 :
    LadderArithUd cfgRec18.μ cfgRec18.per codesRec18 0 0 cfgRec18.levels :=
  ⟨rfl, rfl, eQuery_P8s2.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec18, codesRec18]⟩

/-! ## The stacked openings at S2's parameters -/

end
end LeanVM.Protocol.Whir.Sound
