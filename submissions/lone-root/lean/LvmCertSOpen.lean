-- WP-14 (ASM). New for lvm: the specifications of `P_S`'s first and last parts — the two root
-- commitments (leanVM `EndToEnd/Sound/Frame.lean`'s `commitSpec` pattern: from no doom, the doom
-- created at the root) and the two stacked openings (WP-7's `stackedRec20GSpec`,
-- `stackedMain24GSpec`, joined by `Spec.orStable`), and `P_S`'s whole specification from `MidSpec`.
import LvmCertS
import LvmCertSFrame
import LvmWhirParamsJp

/-!
# The roots, the openings, and `P_S`'s specification

* **`rootsSpec Post`** (O8): `commitRootUd cfgMain24G; commitRootUd cfgRec20G` from no doom; the doom
  after `C_rec`'s root is `Post`, created there (Pre `False`, as leanVM's `commitSpec`).
* **`openSpec cl`** (O7): `C_rec`'s opening, `C_main`'s opening, `ret true`, from `OpenPost cl`
  (which splits into "`C_rec`'s claims fail" or "`C_main`'s claims fail", `openPost_split`) to
  rejection, every group's escape at most `2^-129`, lead at most `2^-129`. `C_main`'s
  precondition (`MainPre`, two commitments) is carried across `C_rec`'s two-level opening by
  `Spec.orStableRet`: that opening's completed runs commit exactly one word (hypothesis `hnc`,
  O7a `RecCommitsOne`), after which it is `C_main`'s `StackedPreUd` (three commitments).
* **`psSpec`**: `PSWith mid x` from no doom, given `MidSpec mid Good` at `2^-129` with lead at
  most `2^-129`: roots (doom `CommitDoomS Good x ∧ RootShape`), the middle phases, the openings.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

/-- The per-group error of `P_S` (lvm2 JB-VQP, J1: the exact budget, JB-L §1): `7·2^-131 = 2^-128 − 2^-131`.
`C_main`'s Johnson query groups reach `2^-128.30`; the luck (`2^-132`) and the hash term (`2^-139`) fit the
margin `2^-131`. Every other group is at most `2^-129` (`pow129_le_εS`). -/
noncomputable abbrev εS : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

theorem inv_pow_131_ne_top : (2 : ℝ≥0∞)⁻¹ ^ 131 ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)

theorem inv_pow_add2 (k : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ k = (2 : ℝ≥0∞)⁻¹ ^ (k + 2) * 4 := by
  rw [pow_add, mul_assoc, show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← mul_pow,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-- Every group bounded by `2^-129` is within `εS`. -/
theorem pow129_le_εS : (2 : ℝ≥0∞)⁻¹ ^ 129 ≤ εS := by
  rw [inv_pow_add2 129]
  show (2 : ℝ≥0∞)⁻¹ ^ 131 * 4 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131
  rw [mul_comm]
  exact mul_le_mul' (by norm_num) le_rfl

/-- `2^-128 = 7·2^-131 + 2^-131`. -/
theorem inv_pow_128_eq : (2 : ℝ≥0∞)⁻¹ ^ 128 = 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 + (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  rw [inv_pow_add2 128, inv_pow_add2 130, show 128 + 2 + 2 = 131 + 1 from rfl]
  rw [show (2 : ℝ≥0∞)⁻¹ ^ (131 + 1) * 4 * 4 = (2 : ℝ≥0∞)⁻¹ ^ (131 + 1) * 2 * 8 by ring,
    pow_succ, mul_assoc ((2 : ℝ≥0∞)⁻¹ ^ 131), ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  ring

/-- `x + 2^-131 ≤ 2^-128` gives `x ≤ εS` (JB-L's margin form of the Johnson groups). -/
theorem le_εS_of_margin {x : ℝ≥0∞} (h : x + (2 : ℝ≥0∞)⁻¹ ^ 131 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128) : x ≤ εS := by
  rw [inv_pow_128_eq] at h
  exact (ENNReal.add_le_add_iff_right inv_pow_131_ne_top).1 h

theorem εS_le_128 : εS ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := le_self_add.trans_eq inv_pow_128_eq.symm

/-! ## The roots (O8) -/

/-- **The two roots**, from no doom; the doom created at `C_rec`'s root is `Post`. -/
noncomputable def rootsSpec (Post : Unit → List Ev → Prop) {εm T : ℝ≥0∞} (hT : T ≤ εm) :
    Spec (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G) (fun _ ↦ False) Post εm 0 T :=
  Spec.bind' ((Spec.commitP (Pre := fun _ ↦ False) (Post := fun _ _ ↦ False) (εmax := εm) 19 64
      (fun _ _ h _ ↦ h.elim) zero_le).congr rfl) fun _ ↦
    (Spec.commitP (Pre := fun _ ↦ False) (Post := Post) 15 64 (fun _ _ h _ ↦ h.elim) hT).congr rfl

/-! ## The openings (O7) -/

/-- **O7a** (lvm2, S4): every completed run of `C_rec`'s two-level opening commits exactly one
word (its level-1 oracle). -/
def RecCommitsOne : Prop :=
  ∀ (cl : List LeanVM.Protocol.Verifier.StackClaim) (l : List Ev) (a : Unit),
    (verifyStackedUd cfgRec20G cl).after l = some (.ret a) → (commits l).length = 1

/-- The program of the openings. -/
def openProg (cl : OpenClaims) : VerifierProgram Bool :=
  verifyStackedJ cfgRec20Jp cl.1 >>= fun _ ↦ verifyStackedJ (cfgMain23Jq 3) cl.2 >>= fun _ ↦ .ret true

/-- **`C_main`'s stacked opening at the Johnson radius at `εS`** (JB-L's `stackedMain24JSpec` at the
exact budget: `whirEps_main23Jq`'s margin `2^-131` left for luck and hash). -/
noncomputable def stackedMain23JqSpecS (claims : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine (cfgMain23Jq 3).μ c.1) (T : ℝ≥0∞) :
    Spec (verifyStackedJ (cfgMain23Jq 3) claims)
      (fun h ↦ StackedPreUd (cfgMain23Jq 3).toUdConfig (codesMain23Jq 0) claims (commits h))
      (fun _ _ ↦ False) εS (eBatch claims.length (codesMain23Jq 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgMain23Jq]) rfl (by norm_num [cfgMain23Jq])
    (by norm_num [cfgMain23Jq]) (by norm_num [cfgMain23Jq]) (ladderArith_main23Jq 2)
    (le_εS_of_margin (whirEps_main23Jq 2)) T

/-- The stacked batching of `C_main` at the Johnson radius: `(J − 1)·124/|E| ≤ 2^-129` for at most
`2^40` claims. -/
theorem eBatch_main23Jq (J : ℕ) (hJ : J ≤ 2 ^ 40) : eBatch J (codesMain23Jq 0) ≤ εS := by
  refine le_trans ?_ pow129_le_εS
  unfold eBatch
  rw [card_E_ennreal, ← two_pow_cast 192]
  refine natCast_div_le_inv_pow (by positivity) ?_
  have h98 : (codesMain23Jq 0).listMax = 124 := rfl
  rw [h98]
  calc (J - 1) * 124 * 2 ^ 129 ≤ 2 ^ 40 * 124 * 2 ^ 129 := by gcongr; exact (Nat.sub_le J 1).trans hJ
    _ ≤ 2 ^ 192 := by norm_num

/-! ## `P_S` -/

/-- `P_S` as the roots, then the middle phases and the openings. -/
theorem PSWith_eq (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    PSWith mid x = ((commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G) >>= fun _ ↦
      mid x >>= openProg) := rfl

end Lvm.ASM
