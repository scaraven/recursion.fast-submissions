-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B1-P3P4 §P3): `C_main` at ν = 23, rate 1/4 at level 0, Johnson
-- with OOD: levels (6,2,115) (4,3,77) (4,4,58), `g = 14`, final 2^9. Constants from B1-C's fold-bound model
-- (`fb23.out`, JB-DES's `jcode_jb`). Level 1 reuses `codeJ13R3`. L-D owns the numerics (`eps_main23Jq`).
/-
  LeanVM.Protocol.Whir.Sound (lvm2 roll 8: ν = 23)
-/

import LvmWhirParamsJp

/-!
# `C_main` at ν = 23 (B1)

| opening | `μ` | levels `(ℓ, R, t)` | codes `(κ, R, A, L)` | `g` |
|---|---|---|---|---|
| `cfgMain23Jq n₀` (P20, B1) | 23 | (6,2,115) (4,3,77) (4,4,58) | `codeJ17R2` (17,2,263206,124), `codeJ13R3` (13,3,23261,231), `codeJ9R4` (9,4,2051,615) | 14 |

(`cfgMain23J` is P8's; hence `Jq`.) B1-P3P4 [exact]: worst group level 0's queries `2^-128.330 ≤ εS`; folds
`≤ 2^-130, 2^-132, 2^-130`; OOD `≤ 2^-173, 2^-170`; queries before the discount `2^-114.330, 2^-115.072,
2^-115.918`; level 2 needs 58 queries (57 gives `2^-127.92`). `L₀ = 124·304 = 37,696`.

* `codeJ17R2`, `codeJ9R4`, `codesMain23Jq`, **`cfgMain23Jq`**;
* **`eps_main23Jq`** (L-D: eight inequalities by `eFold_le_of`, `eOod_le_of`, `eQuery_le_mul_of`,
  `eQueryFinal_le_mul_of`);
* from it: **`whirEps_main23Jq`** (margin form, `+ 2^-131 ≤ 2^-128`), `ladderArith_main23Jq`,
  `stackedMain23JqSpec`; `candidates_main23Jq_ncard_le` (`≤ 124`), `L0_main23Jq`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson

set_option exponentiation.threshold 512

section

/-! ## The codes -/

/-- `C_main` level 0 at ν = 23: `κ = 17`, `R = 2`, `η = 135955/2^28`. -/
noncomputable def codeJ17R2 : LevelCode where
  κ := 17
  R := 2
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 263206
  listMax := 124
  mcaMax := 144115041830655840
  facts := codeFacts_johnson (domain _ _ _) (135955 / 2 ^ 28) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_main` level 2 at ν = 23: `κ = 9`, `R = 4`, `η = 40437/2^28`. -/
noncomputable def codeJ9R4 : LevelCode where
  κ := 9
  R := 4
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 2051
  listMax := 615
  mcaMax := 576450765148488047
  facts := codeFacts_johnson (domain _ _ _) (40437 / 2 ^ 28) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- The codes of `C_main` at ν = 23: `codeJ17R2`, `codeJ13R3`, `codeJ9R4`. -/
noncomputable def codesMain23Jq : ℕ → LevelCode
  | 0 => codeJ17R2
  | 1 => codeJ13R3
  | _ => codeJ9R4

/-- **`C_main` at ν = 23** (B1): `(6,2,115) (4,3,77) (4,4,58)`, `g = 14`, OOD; root `0` of `n₀`. -/
def cfgMain23Jq (n₀ : ℕ) : WhirConfig :=
  ⟨⟨23, [⟨6, 2, 115⟩, ⟨4, 3, 77⟩, ⟨4, 4, 58⟩], 8, 0, n₀, false, 14⟩, true⟩

/-! ## The escapes -/

/-- **The groups of `cfgMain23Jq` before the discount** (B1-P3P4, L-D): folds `≤ 2^-130, 2^-132, 2^-130`, OOD
`≤ 2^-173, 2^-170`, queries within `7·2^-117`. -/
theorem eps_main23Jq : eFold codeJ17R2 6 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eFold codeJ13R3 4 ≤ (2 : ENNReal)⁻¹ ^ 132 ∧ eFold codeJ9R4 4 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eOod codeJ13R3 17 ≤ (2 : ENNReal)⁻¹ ^ 173 ∧ eOod codeJ9R4 13 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧
    eQuery codeJ17R2 codeJ13R3 115 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQuery codeJ13R3 codeJ9R4 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQueryFinal codeJ9R4 58 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 := by
  refine ⟨eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_,
    eOod_le_of _ _ _ ?_, eQuery_le_mul_of _ _ _ _ _ ?_, eQuery_le_mul_of _ _ _ _ _ ?_,
    eQueryFinal_le_mul_of _ _ _ _ ?_⟩ <;>
    norm_num [codeJ17R2, codeJ13R3, codeJ9R4, LevelCode.n, Nat.choose_two_right]

/-- **`εmax` of `C_main` at ν = 23**: every group within `7·2^-131`, so `+ 2^-131 ≤ 2^-128`. -/
theorem whirEps_main23Jq (n₀ : ℕ) :
    whirEpsJ codesMain23Jq (cfgMain23Jq n₀).grind (cfgMain23Jq n₀).levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨f0, f1, f2, o0, o1, q0, q1, q2⟩ := eps_main23Jq
  refine add_margin_le ?_
  simp only [whirEpsJ, cfgMain23Jq, levelEpsJ, codesMain23Jq, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, le_seven_of (by norm_num) o0⟩, disc7 q0,
    ⟨le_seven_of (by norm_num) f1, le_seven_of (by norm_num) o1⟩, disc7 q1,
    le_seven_of (by norm_num) f2, disc7 q2, le_seven_of (by norm_num) eTail_le⟩

theorem ladderArith_main23Jq (n₀ : ℕ) :
    LadderArithJ (cfgMain23Jq n₀).μ (cfgMain23Jq n₀).per codesMain23Jq 0 0 (cfgMain23Jq n₀).levels := by
  obtain ⟨-, -, -, o0, o1, q0, q1, q2⟩ := eps_main23Jq
  have h := seven_inv_lt_one
  have ho := inv_two_pow_lt_one (c := 170) (by norm_num)
  exact ⟨rfl, rfl, o0.trans_lt (inv_two_pow_lt_one (by norm_num)), q0.trans_lt h,
    by norm_num [cfgMain23Jq, codesMain23Jq, codeJ17R2],
    rfl, rfl, o1.trans_lt ho, q1.trans_lt h, by norm_num [cfgMain23Jq, codesMain23Jq, codeJ13R3],
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain23Jq, codesMain23Jq, codeJ9R4]⟩

/-! ## The stacked opening -/

/-- **`C_main`'s stacked opening at ν = 23**: groups escape at most `2^-128`. -/
noncomputable def stackedMain23JqSpec (n₀ : ℕ) (hn₀ : 0 < n₀) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine (cfgMain23Jq n₀).μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ (cfgMain23Jq n₀) claims)
      (fun h ↦ StackedPreUd (cfgMain23Jq n₀).toUdConfig (codesMain23Jq 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesMain23Jq 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgMain23Jq]) rfl hn₀ (by norm_num [cfgMain23Jq])
    (by norm_num [cfgMain23Jq]) (ladderArith_main23Jq n₀) (le_of_add_margin (whirEps_main23Jq n₀)) T

/-! ## The candidates -/

/-- `C_main`'s root candidates at ν = 23: at most `124` (the `C_main` factor of `L₀`). -/
theorem candidates_main23Jq_ncard_le (W : Word) :
    (Candidates 23 2 (codesMain23Jq 0).thr W).ncard ≤ 124 :=
  candidates_ncard_le (codesMain23Jq 0) (by norm_num) rfl rfl W

/-- **`L₀` at B1** (B1-P3P4): `124·304`. -/
theorem L0_main23Jq : 124 * 304 = 37696 := by norm_num

end
end LeanVM.Protocol.Whir.Sound
