-- Moved out of `LvmS2GTCert` (lvm2 U-TAPE, UT-L, 2026-11-16; text unchanged): the guarded certificate and the
-- executable extractor at any stage, so that a stage's certificate need not import another stage's.
import LvmXSStage
import LvmCertF20
import LvmFinGuard

/-!
# The guarded submission at any stage

* **`subGS st b VS`**: `V_S` behind the static guard `b`, the stage's extractor; **`certificateR_guardS`**: the guard
  off rejects, on the certificate of the unguarded submission; **`extS`**: the stage's executable extractor.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.XS
open scoped NNReal ENNReal

/-! ## The guard, generic in the stage -/

/-- **The guarded submission at a stage**: `V_S` behind the static guard `b`, the stage's extractor
(`subGF b VS = subGS stF20 b VS` by `rfl`). -/
def subGS (st : XStage) (b : Bool) (VS : SProg) : Submission :=
  subWith (Lvm.Fin.VSg b VS) (EXS st (accV (Lvm.Fin.VSg b VS))) (extXS st)

/-- **S2GT-STMT 22** (owner L, generic): **the guarded certificate at a stage** (`certificateR_guardF` with the
stage's `ProgOK`/`OutOK`): the guard off rejects; on, the certificate of the unguarded submission. -/
theorem certificateR_guardS (st : XStage) (hp : ProgOK st) (ho : OutOK st) {b : Bool} {VS : SProg}
    (h : b = true → CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (EXS st (accV VS)) (extXS st))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subGS st b VS) := by
  cases b with
  | false =>
    exact certificateR_claim _ _ _
      ⟨fun H vk c π _ => by simp [Lvm.Fin.VSg, OProg.queries], computesXS st hp ho _, extXS_size st hp ho,
        EXS_Wn st hp _, fun vk => Lvm.Fin.sSound_reject VS _ vk⟩
  | true => exact h rfl

/-- **The stage's executable extractor** for a verifier `VS` (`extF20` at a stage). -/
def extS (st : XStage) (hp : ProgOK st) (ho : OutOK st) (VS : SProg) : ExtF20 :=
  ⟨EXS st (accV VS), extXS st, computesXS st hp ho _, extXS_size st hp ho, EXS_Wn st hp _⟩

end Lvm.CT
