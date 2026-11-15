-- New for lvm2 E2-FT (stage S2GT, E2F-T): the frozen statements of the typed phases at `E2`: `typedSpecT` and, at
-- P20, `THypT`, `GoodTT`, `midGT`, `midSpecP_GT` (the lead's pinned pair form). Definitions in `LvmE2TProg`.
import LvmE2TProg
import LvmE2FCert
import LvmE2TRet
import LvmE2TMid

/-!
# The typed phases at `E2`: the specification (S2GT)

* **`typedSpecT`** (`typedSpecX`'s statement at S2GT): from `G ∧ firstWord ∧ Doomed C (TGoodT ∧ R ∧ AccOkTT)` to
  the doom of the returned split claims with `R`; lead `0`; the errors `TErrsT`.
* At P20: **`THypT`** (`THyp` with `acc_in` of 45 coordinates and `TErrsT 1 … εS 0`), **`GbTT`**, **`GoodTT`**
  (`GoodTF`'s shape with `GbTT`), **`midGT`** (`midFWith (typedProgT Ti)`), **`midSpecP_GT`** (lead `leadF₂`,
  candidates `candRelZ recOf za`, shape `PinPost za`).
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst stackOf KeysOk AllSc LayOk FixOk lay26)
open Lvm.ASM (OpenClaims Pair GoodRel MidSpecP GkS BndS εS)
open Lvm.VEq (VStackClaim hdX pubX pubXT)
open LeanVM.Protocol.KeccakGkr (errE)
open Lvm.ASM (coe_overE coe_div_card errE_le_εS errE_add errE_smul εS_lt_one)
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (NoCG)
open scoped ENNReal NNReal

/-- **The typed phases' specification at S2GT** (`typedSpecX`'s shape): from `G ∧ firstWord ∧ Doomed C (TGoodT ∧
R ∧ AccOkTT)` to the doom of the returned (split) claims with `R`, generic in the candidate set `C` and the
carried `R`; lead `0` (the separator). Owner **E2F-T**. -/
noncomputable def typedSpecT (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrsT L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProgT Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGoodT Ti L hτL pub p ∧ R p ∧ AccOkTT Ti pub) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax 0 T :=
  typedSpecGT Ti L pub hτL hTi hmaps hrec hacc hsc hlay hkey hw hfix hμ C R G hCG hf hc herr

/-! ## The return facts and the shape -/

/-- **The typed phases' return facts at S2GT** (`TRet`'s twin): the claims are multiaffine on their commitments and
few (the mini-bus's at most its columns, `≤ 2^38`, the split typed claims 8). -/
def TRetT (a : OpenClaims) : Prop :=
  (∀ c ∈ a.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ a.2, IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39

/-! ## S2GT's `KS` link and middle phases (the continuation rows are the S2GT trace's) -/

/-- **The S2GT trace's sponge blocks** [model, `ref/s2gt.py` at occupancy 46: 4,282; 4,288 at 47]. The value
decides which `KS` rows the good relation links (`GoodTT`), so it must equal the S2GT trace's count: to be pinned by a
decided fact against the S2GT schedule (the `P20T` instance of the unified `LvmSchedule`; E2F-LEAD's standing item).
The proofs need only `≤ ksSplit P20 + 400` (`rowsOfB_struct`). -/
abbrev spongeBlocksGT : ℕ := 4282

/-- **The `KS` continuation rows at S2GT** (`contRowsF` with S2GT's trace): rows `1 … blocks − 1` and rows 1–31 of
the WOTS leaf. -/
def contRowsT : List ℕ :=
  (List.range (spongeBlocksGT - 1)).map (· + 1) ++ (List.range 31).map (ksSplit P20 + 399 + 1 + ·)

/-! ## At P20 -/

/-- **What the typed instance must meet at P20, S2GT** (`THyp` with `acc_in` of `phiVarsT` coordinates, read at
`E2` without loss, and the errors `TErrsT` at `L₀ = 1` after the pin, follower lead `0`: the front starts with
its separator). `accC2`: the S2GT header parse (E2F-V's, 16-B scalars: `(re, im, 0)`) gives `acc_in`'s scalars
with `c₂ = 0`, so `accPtT`/`accYT` lose nothing; the node's outgoing accumulator is written the same way (16-B
scalars), so `AccOkTT` composes across steps. -/
structure THypT (Ti : TInst) : Prop where
  ok : Ti.Ok
  maps : Ti.MapsFit lay26
  acc : ∀ x, (pubXT x).accIn.pt.length = phiVarsT
  accC2 : ∀ x, (∀ a ∈ (pubXT x).accIn.pt, a.c₂ = 0) ∧ (pubXT x).accIn.y.c₂ = 0
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ
  sc : AllSc Ti.mbT
  layOk : LayOk lay26 Ti.mbT
  keys : KeysOk Ti.mbT
  width : ∀ t ∈ Ti.mbT, 0 < t.w
  fix : FixOk Ti.mbT
  widths : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = miniDepth
  errs : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), TErrsT 1 (inst lay26 Ti.mbT h) εS 0

/-- **The bus half of a good pair at S2GT** (`GbT` with `TGoodT`, `AccOkTT`). -/
def GbTT (Ti : TInst) (H : THypT Ti) (x : List UInt8) (p : Pair) : Prop :=
  (TGoodT Ti lay26 H.hτ (pubXT x) p ∧ BndS x p.1) ∧ AccOkTT Ti (pubXT x)

/-- **The good pair at S2GT** (`GoodTF`'s shape with `GbTT` and S2GT's continuation rows). -/
def GoodTT (Ti : TInst) (H : THypT Ti) : GoodRel := fun x qm qr ↦ GbTT Ti H x (qm, qr) ∧ GkFR contRowsT x (qm, qr)

/-- **S2GT's middle phases**: the typed phases at `E2`, the `E2` front with S2GT's continuation rows (E2F-V's
rows-parametric `midFWithR`), the claims. -/
def midGT (Ti : TInst) : List UInt8 → VerifierProgram OpenClaims := midFWithR (fun x ↦ typedProgT Ti (pubXT x)) contRowsT

/-- **The typed phases' return facts** (multiaffine, few). -/
theorem retOK_typedProgT (Ti : TInst) (H : THypT Ti) (pub : Lvm.Pub) : RetOK TRetT (typedProgT Ti pub) := by
  exact retOK_typedProgT_of Ti H.layOk H.widths pub

/-- **The middle phases' claims are fewer than `2^40`** (`midSpecPin_of`'s `hlen`, strict). -/
theorem retOK_midGT_len (Ti : TInst) (H : THypT Ti) (x : List UInt8) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (midGT Ti x) := by
  exact retOK_midT_len_of Ti H.layOk H.widths x _ (retOK_kgFrontT contRowsT _ _)

/-- **The typed phases commit nothing and ask no proof of work** (the `E2` proofs of work are `require`s on the
answers, not `grind` nodes). -/
theorem cg_typedProgT (Ti : TInst) (pub : Lvm.Pub) : NoCG (typedProgT Ti pub) := by
  exact noCG_typedProgT Ti pub

/-- **S2GT's middle phases commit nothing and ask no proof of work** (`midShapeM_of`'s premise). -/
theorem cg_midGT (Ti : TInst) (x : List UInt8) : NoCG (midGT Ti x) := by
  exact Lvm.M3.NoCG.bind (noCG_typedProgT Ti _) fun _ ↦ Lvm.M3.NoCG.bind (noCG_kgFrontT contRowsT _ _) fun _ ↦
    Lvm.M3.cg_ret _

/-- **The pinned pair form of S2GT's middle phases** (`midSpecP_F₂`'s twin; E2F-L's `midSpecPin_of` consumes it):
for every pin `za`, from `PinPost za` to `OpenPostRG` over `candRelZ recOf za`, every group `≤ εS`, lead
`leadF₂`. Owner **E2F-T**. -/
theorem midSpecP_GT (Ti : TInst) (H : THypT Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) :
    MidSpecP (midGT Ti) (Lvm.E2F.candRelZ recOf za) (Lvm.E2F.PinPost za) (Lvm.Shape.Good₂ (GoodTT Ti H)) εS
      leadF₂ := by
  exact midSpecP_GT_of Ti H.hτ H.ok H.maps H.acc H.sc H.layOk H.keys H.width H.fix H.widths (H.μBus H.hτ)
    (H.errs H.hτ) contRowsT (rowsOfB_struct spongeBlocksGT (by rw [Lvm.ksSplit_P20]; norm_num)) recOf za

end Lvm.E2T
