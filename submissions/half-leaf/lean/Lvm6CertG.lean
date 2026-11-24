-- New for lvm6 (PORT17 C1): the certificate's assembly with the extractor as a parameter. Links 1 and 2 of WP C6
-- (`certified_ofS`, `certified_off`, `VSF6_on`, `VSF6_off`, moved verbatim from `Lvm6Cert`) and the guard split
-- for any extractor family that meets C4's obligations (`XOpen6D`) when the guard holds.
import Lvm6CertExt
import Lvm6CertMA
import Lvm6CertOpen
import Lvm6WOnly

/-!
# The certificate's assembly over any extractor (PORT17 C1)

`Lvm6Cert` assembles the certificate for C4's extractor `EX6D A DD` and the program `extX6 DD`. Their facts
(`open6XD`, `computes6D`, `wBranch6D`, `descOk6_FDep`, `sizeIR_F`) are the extractor's (`Lvm6XDom`,
`Lvm6XIndOk18`, `Lvm6XIndOpen18`). This module states and proves the rest of the assembly with the extractor as a
parameter, so that it does not import them:

* **`certified_ofS`** (link 1, season 1's form) and **`certified_off`** (link 2, guard off): as in WP C6.
* **`VSF6_on`**, **`VSF6_off`**: the guarded fast `V_S` at `P17` is `VSasm (Φ6 B h)` (guard on; `VSF6_eqP17`,
  `VSasm_Φ6`) or `VSoff` (guard off).
* **`certified_onG`**: C4's `certified_ofD` for an extractor `EX` and program `extX` meeting `XOpen6D` at
  `VSasm (Φ6 B h) P17`, with C3's `queries_VSasm` and `refines6_asm`.
* **`certified6_guardG`**: the certificate of the guarded submission `submissionOf (VSF6 B P17) (EXf (accV (VSF6 B
  P17))) extX`, for an extractor family `EXf` (one per acceptance), from `XOpen6D` when the guard holds and, for
  every acceptance, `Computes`, the size and the `W` branch. `Lvm6Cert.certified6_guard` is its instance at
  `EXf := fun A ↦ EX6D A DD`, `extX := extX6 DD`.
-/

set_option autoImplicit false

namespace Lvm6.Cert

open RecursionFast Lvm.T Lvm.X LeanVM.Parameters
open RecursionFast.WitnessSending (decode)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.V (TyBase6 staticOk6 inst6 VSF6 VSspec6 Φ6)
open scoped NNReal

/-! ## Link 1, season 1's form: from `SSound` -/

/-- **The certificate against `declared6` from `SSound`**: the `S` branch's knowledge soundness through a scheme it
refines (season 1's `SSound`), its query bound, the program's `Computes` within `fuel6` and size, and the
extractor's `W` branch. -/
theorem certified_ofS {VS : SProg} {EX : Digest → Proof → Log → Option Wit} {extX : XProg}
    (hq : ∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm)
    (hc : Computes extX EX fuel6) (hsz : extX.body.size ≤ progCap)
    (hEW : ∀ c π L, isS π = false → EX c π L = decode π) (hS : ∀ vk, SSound VS EX vk) :
    CertificateR declared6 (submissionOf VS EX extX) := by
  refine ⟨⟨fun vk => ks_subWith VS EX extX hq hEW vk (hS vk), fun vk => ?_, hc, ?_⟩, ?_⟩
  · rw [submissionOf_δ]; exact complete VS _ rfl rfl rfl vk
  · refine ⟨by rw [submissionOf_ε]; rfl, by rw [submissionOf_δ]; exact zero_le,
      show qVlvm ≤ 2 ^ 16 by decide, fun t => ?_, hsz⟩
    simp only [submissionOf, fuel6, extractorBudget]; omega
  · refine ⟨?_, by simp [submissionOf, declared6], le_rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
    · simp only [submissionOf, declared6]; push_cast; norm_num
    · simp [submissionOf, declared6, fuel6]
    · simp only [declared6, extractorBudget]; omega

/-! ## Link 2: the guard off -/

/-- **The certificate with the `S` branch off**, for every extractor that the program computes within `fuel6`, that
fits `progCap` and that decodes `W` proofs (`sSound_off`). -/
theorem certified_off {EX : Digest → Proof → Log → Option Wit} {extX : XProg}
    (hc : Computes extX EX fuel6) (hsz : extX.body.size ≤ progCap)
    (hEW : ∀ c π L, isS π = false → EX c π L = decode π) :
    CertificateR declared6 (submissionOf W.VSoff EX extX) :=
  certified_ofS (fun _ _ _ _ _ => by simp [W.VSoff, OProg.queries]) hc hsz hEW
    (fun vk => W.sSound_off EX vk)

/-- **With the guard on, the guarded fast `V_S` is `VSasm (Φ6 B h)` at `P17`** (`VSF6_eqP17`, V1; `VSasm_Φ6`,
C3). -/
theorem VSF6_on {B : TyBase6} (h : staticOk6 B = true) : VSF6 B P17 = VSasm (Φ6 B h) P17 := by
  rw [V.VSF6_eqP17, ← V.VSasm_Φ6 B h]
  funext vk c π
  simp [VSspec6, h]

/-- **With the guard off, the guarded fast `V_S` is `VSoff`.** -/
theorem VSF6_off {B : TyBase6} {sh : Shape} (h : ¬ staticOk6 B = true) : VSF6 B sh = W.VSoff := by
  funext vk c π
  simp [VSF6, h, W.VSoff]

/-! ## The guard split over any extractor -/

/-- **The certificate at C3's phases** `Φ6 B h` for any extractor `EX` and program `extX` that meet C4's
obligations `XOpen6D` there (`certified_ofD`, with `queries_VSasm` and `refines6_asm`). -/
theorem certified_onG (B : TyBase6) (h : staticOk6 B = true) {EX : Digest → Proof → Log → Option Wit}
    {extX : XProg} (hX : XOpen6D (VSasm (Φ6 B h) P17) (prog6 (Φ6 B h)) EX extX) :
    CertificateR declared6 (submissionOf (VSasm (Φ6 B h) P17) EX extX) :=
  certified_ofD (VS := VSasm (Φ6 B h))
    { hX with
      queries := V.queries_VSasm (Φ6 B h)
      refines := refines6_asm (Φ6 B h) P17 }

/-- **The certificate of the guarded submission** for an extractor family `EXf` (one per acceptance) and a program
`extX`: with the guard on, C4's obligations at `VSasm (Φ6 B h)`; with it off, `Computes`, the size and the `W`
branch for every acceptance. -/
theorem certified6_guardG (B : TyBase6)
    (EXf : (Digest → Digest → Signed → Bool) → Digest → Proof → Log → Option Wit) (extX : XProg)
    (hon : ∀ h : staticOk6 B = true,
      XOpen6D (VSasm (Φ6 B h) P17) (prog6 (Φ6 B h)) (EXf (accV (VSasm (Φ6 B h) P17))) extX)
    (hc : ∀ A, Computes extX (EXf A) fuel6) (hsz : extX.body.size ≤ progCap)
    (hEW : ∀ A c π L, isS π = false → EXf A c π L = decode π) :
    CertificateR declared6 (submissionOf (VSF6 B P17) (EXf (accV (VSF6 B P17))) extX) := by
  by_cases h : staticOk6 B = true
  · rw [VSF6_on h]
    exact certified_onG B h (hon h)
  · rw [VSF6_off h]
    exact certified_off (hc _) hsz (hEW _)

end Lvm6.Cert
