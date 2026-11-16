-- New for lvm2 U-TAPE (UT-V, lead decision U-A3): `MidSpecP` over followers of lead at most `τ` and the twin of
-- `midSpecOfRelG` for it (beside the generic ones, which S2GF/S2GT keep): S2GU's middle phases end with the `M` row
-- switch's challenges, which share their group with the follower's first challenge.
import LvmMPMid

/-!
# `MidSpecPτ`

* **`midSpecOfRelGτ`**: `midSpecOfRelG` into `LvmMPMid`'s `MidSpecPτ`, with the `Keccak` half's spec needed for `T ≤ τ` only.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (NoCG cg_ret)
open scoped ENNReal NNReal

section GlueTau

variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : List UInt8 → VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb Gk : List UInt8 → Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : List UInt8 → κ → Pair → Prop} {Qa : List UInt8 → α → Prop} {Qk : List UInt8 → κ → Prop}
  {εm Lb Lk : ℝ≥0∞} {C : List UInt8 → List Ev → Set Pair} {Sh : List Ev → Prop}

open Classical in
/-- **`midSpecOfRelG` over followers of lead at most `τ`** (the `Keccak` half's spec needed only for `T ≤ τ`). -/
theorem midSpecOfRelGτ {τ : ℝ≥0∞} (hSh : ∀ h₀ l, commits l = [] → Sh h₀ → Sh (h₀ ++ l))
    (SB : ∀ x, Spec (busP x)
      (fun h ↦ Sh h ∧ Doomed (C x) (fun p ↦ Gb x p ∧ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p))) h)
      (fun a h ↦ Doomed (C x)
        (fun p ↦ (B x a p ∧ ¬ (Gb x p ∧ Gk x p)) ∧ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p))) h ∧ Sh h)
      εm Lb Lk)
    (hQa : ∀ x, RetOK (Qa x) (busP x))
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ τ → Spec (kgP x)
      (Doomed (C x) (fun p ↦ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p)) ∧ (B x a p ∧ ¬ (Gb x p ∧ Gk x p))))
      (fun k h ↦ Doomed (C x) (fun p ↦ Kc x k p ∧ (B x a p ∧ ¬ (Gb x p ∧ Gk x p))) h) εm Lk T)
    (hQk : ∀ x, RetOK (Qk x) (kgP x)) (hkc : ∀ x, NoCG (kgP x))
    (hasm : ∀ x a k (p : Pair), Qa x a → Qk x k →
      (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc x k p ∧ B x a p)
    (hside : ∀ x a k, Qa x a → Qk x k → (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 55 ∧
      (asm x a k).2.length ≤ 2 ^ 40) :
    MidSpecPτ (fun x ↦ busP x >>= fun a ↦ kgP x >>= fun k ↦ VerifierProgram.ret (asm x a k)) C Sh
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) εm Lb τ := fun x T hT ↦
  ⟨((Lvm.KG.specWithRet (SB x) (hQa x)).bind' fun a ↦
      if ha : Qa x a then
        ((Lvm.KG.specWithRet ((SK x a T hT).frame Sh fun _ _ hl hr ↦
            hSh _ _ ((hkc x).1.reach_commits hl) hr) (hQk x)).mono
          (fun _ hp ↦ ⟨Doomed.mono hp.2.1 fun _ hq ↦ ⟨hq.2, hq.1⟩, hp.2.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun k ↦
        if hk : Qk x k then
          (Spec.ret (Post := OpenPostRG (C x) Sh (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) x) (εmax := εm)
              (T := T) (asm x a k)).mono
            (fun _ hp ↦ openPostRG_of (hasm x a k · ha hk) (hside x a k ha hk) hp.2.1 hp.2.2)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hk hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ ha hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun _ hp ↦ ⟨hp, fun _ _ hq ↦ hq.2.2 ⟨hq.1, hq.2.1⟩⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end GlueTau

end Lvm.ASM
