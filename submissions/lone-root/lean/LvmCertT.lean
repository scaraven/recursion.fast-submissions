-- New for lvm2 (roll 8 = B1, wave L, L-W): the typed certificate's generic glue. `LvmFinGuard`'s and
-- `LvmSubmissionS`'s certificate of a guarded submission, for any `V_S` with a query bound (roll 7's were at
-- `VSt tabs`, the bus path's `V_S`), and O1 for the typed `V_S` (`VST`, the same driver as `VS`).
import LvmFinGuard
import LvmCertSExq2
import LvmVerifierST

/-!
# The certificate of a guarded submission, for any `V_S`

* **`queries_VST_le`**, **`hq_VST20`**: O1 for `VST p N` (the driver over the schedule, as `queries_VS_le`): at
  most `2 + qcItems p (schedule p) 0` queries on every oracle path, `≤ qVlvm` at `P20`.
* **`EX_Wv`**: O4 for `EX (accV VS)`, any `VS`.
* **`certificateR_openV`**: the certificate of `subWith VS (EX (accV VS)) extX` from O1 and `OpenS`.
* **`certificateR_guardV`**: the certificate of `subG b VS` from O1 and `OpenS` under `b = true`.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-! ## O1 for the typed `V_S` -/

/-- **The query bound of the typed `V_S`** on every oracle path (`queries_VS_le`'s proof: the decision is a
`.ret`). -/
theorem queries_VST_le (p : Params) (N : TypedV.TNat) (vk c : Digest) (π : RecursionFast.Proof)
    (H : ByteArray → Digest) :
    ((VST p N vk c π).queries H).length ≤ 2 + qcItems p (schedule p) 0 := by
  unfold VST
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π p _ 0 (fun s ↦ by
      simp [OProg.queries]) (schedule p) 0 _ (by simp)) 1) 1).trans ?_
    omega
  · simp [OProg.queries]

/-- **O1** for the typed `V_S` at `P20`, any instance. -/
theorem hq_VST20 (N : TypedV.TNat) (H : ByteArray → Digest) (vk c : Digest) (π : RecursionFast.Proof) :
    ((VST P20 N vk c π).queries H).length ≤ qVlvm :=
  (queries_VST_le P20 N vk c π H).trans qcItems_P20

/-! ## The certificate for any `V_S` -/

/-- O4 for `EX (accV VS)`: on witness-sending proofs it decodes. -/
theorem EX_Wv (VS : SProg) (c : Digest) (π : RecursionFast.Proof) (L : Log) (h : isS π = false) :
    Lvm.X.EX (accV VS) c π L = decode π := by
  refine Lvm.X.EX_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- **The certificate of `subWith VS (EX (accV VS)) extX`** from O1 and the open obligations. -/
theorem certificateR_openV (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenS VS (Lvm.X.EX (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EX (accV VS)) Lvm.X.extX) :=
  certificateR_claim VS _ Lvm.X.extX
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesX _, Lvm.X.extX_caps.2, EX_Wv VS, sSound_of_openS o⟩

/-- The guarded submission with the guard on is the plain one. -/
theorem subG_true (VS : SProg) : Lvm.Fin.subG true VS = subWith VS (Lvm.X.EX (accV VS)) Lvm.X.extX := rfl

/-- **The certificate of the guarded submission `subG b VS`** from O1 and the open obligations under
`b = true` (`certificateR_guardT`'s, any `V_S`). -/
theorem certificateR_guardV (VS : SProg) (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) {b : Bool}
    (h : b = true → OpenS VS (Lvm.X.EX (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (Lvm.Fin.subG b VS) := by
  cases b with
  | false => exact Lvm.Fin.certificateR_reject _
  | true => rw [subG_true]; exact certificateR_openV VS hq (h rfl)

-- (R11-IS, M′: `ext_eqV`, O5c through B1's `ext_eq_gen`, is removed; M′'s O5c is `LvmCertM20.ext_eqM20`.)

end Lvm.CT
