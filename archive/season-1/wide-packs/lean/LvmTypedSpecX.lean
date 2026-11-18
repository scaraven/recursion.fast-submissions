-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §6 statement 12): `typedSpecX`, the typed phases' specification with
-- the coordinate split. Frozen on day 0 (lead amended to `leadTX`); proof E2F-Q-S12's (LvmTypedSpecXP).
import LvmTypedSpecXP

/-!
# Statement 12: `typedSpecX`

The phases (`zeroProgX`, `wireProgX`, `accProgQX`, `typedProgX`), the good relation (`TGoodX`, `AccOkTX`) and the
error side conditions (`leadTX`, `leadMaxTX`, `TErrsX`) are in `LvmTypedSpecXD`; the proof in `LvmTypedSpecXP`.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst stackOf comCell NoCG KeysOk AllSc LayOk FixOk)
open Lvm.ASM (OpenClaims)
open scoped ENNReal NNReal

/-- **Statement 12: the typed phases' specification, coordinate-split** (E2AC-DES §6, `typedSpecR`'s shape):
from `G ∧ firstWord ∧ Doomed C (TGoodX ∧ R ∧ AccOkTX)` to the doom of the returned claims with `R`, generic in
the candidate set `C` and the carried `R`. Owner **E2F-Q**. -/
noncomputable def typedSpecX (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsX) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrsX L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProgX Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGoodX Ti L hτL pub p ∧ R p ∧ AccOkTX Ti pub) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadTX L₀) T :=
  typedSpecXP Ti L pub hτL hTi hmaps hrec hacc hsc hlay hkey hw hfix hμ C R G hCG hf hc herr

end Lvm.Typed
