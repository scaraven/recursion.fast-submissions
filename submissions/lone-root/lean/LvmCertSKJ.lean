-- New for lvm2 (J2C, J2′): the knowledge certificate of the `S` branch with `C_rec` at the Johnson radius, from
-- the invariant (J2C-DES §3 T9): `kcertOfInv` on J2C-B's `psInv` and J2C-C's `extJ`. Assembled at G0 by the lead
-- (J2C-INT owns it).
import LvmInvCert
import LvmCertSOpenJ
import LvmCertSExtJ

/-!
# The `S` branch's certificate at J2′ (J2C-DES §0, §3 T9)

* **`kcertSJ`**: `KCert (schemeS vk (PSWith mid)) (Rel (accV VS vk))` with no doom (`ε = 0`), luck
  `¬ Inv ∨ BL` at `εB = 7·2^-131 + 2^-132` (`Inv` the doom of `psInv`, `BL` the extractor's luck), extraction
  `extJ`'s. **`εFS_kcertSJ`**: `εFS ≤ 2^-128` (`7·2^-131 + 2^-132 + 2^-139`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}
  {VS : SProg} {vk : RecursionFast.Digest}

/-- **The knowledge certificate of the `S` branch at J2′** (J2C-DES T9): from `MidSpecR` (the middle phases
from the roots' shape into `OpenPostR`, every group `≤ εS`, lead `≤ εS`), the middle phases' shape and an
extraction `X`. -/
noncomputable def kcertSJ (hmid : MidSpecR mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    (X : ExtJ mid Good VS vk) : KCert (schemeS vk (PSWith mid)) (Rel (accV VS vk)) :=
  kcertOfInv (S := schemeS vk (PSWith mid)) (εI := 7 * (2 : ℝ≥0)⁻¹ ^ 131) (εL := (2 : ℝ≥0)⁻¹ ^ 132)
    (Ext := ExtI mid Good)
    (fun x ↦ (psInv hmid hLm x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl)
    zero_le (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWith hsh.noGrind x) hr)
    X.BL X.BL_nil X.BL_read X.BL_commit X.BL_group
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) X.ext X.extract

/-- **Its error** (J2C-DES T9): `εFS ≤ 2^-128`. -/
theorem εFS_kcertSJ (hmid : MidSpecR mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    (X : ExtJ mid Good VS vk) : Scheme.εFS (kcertSJ hmid hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

end Lvm.ASM
