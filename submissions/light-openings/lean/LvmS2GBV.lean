-- New for lvm2 MP-B cap pruning (CAP-L, 2026-11-17): `V_S` at S2GB (phase 1, G0-2): the decision's twins that read the
-- S2GB stream (the sent cap widths, the heap entries after each opening) and `VSSB`. S2GS's are untouched.
import LvmS2GBDrive
import LvmS2GSStmtV

/-!
# `V_S` at S2GB

* **`whirLevelsFB p`**: `whirLevelsF` reading the next level's sent cap (`2^capSendBits` nodes) and skipping the
  level's `heapQ` heap node entries (104 B each in `Σ`) after its openings; `verifyWhirFB`, `verifyStackedOpeningGB`,
  `dOpenFFLB` the callers' twins.
* **`decideProgSB`**, **`decideFSB`**: `decideProgSG` / `decideFSG` with the sent `L0` cap, the S2GB opening, and the
  tape's intervals `contIvSB a` (the trace's rows `1 … bB`, `bB = spongeBlocks P20B − 1`).
* **`VSSB N`**: `parseOkB P20B`, then `driveB P20B` with `decideFSB`.
-/

set_option autoImplicit false

namespace Lvm

open DM Lvm.E2V

/-- Skip `n` node entries of `Σ` (`8 + 64 + 32` bytes each: the heap queries). -/
@[inline] def skipEntries (n : Nat) : DM Unit := modify fun s => { s with ent := s.ent + 104 * n }

/-- **`whirLevelsF` at S2GB**: the next level's sent cap is `2^capSendBits` nodes, and each opening's heap entries
follow its paths. -/
def whirLevelsFB (p : Params) (logN laneFolds : Nat) (evaluateBasis : List FE → FE) (direct : Bool) (g : Nat)
    (ood : Bool) : List Level → WhirState → DM Unit
  | [], _ => require false
  | L :: rest, s => do
    let (s, levelFolds) ← foldRounds L.fold s []
    let messageLog := logN - s.folds.length
    let residual ← match rest with
      | [] => readEs (2 ^ messageLog)
      | N :: _ => do skip (nodeBytes * 2 ^ p.capSendBits N.level N.cap); pure []
    let oodClaims ← match rest with
      | [] => pure []
      | _ :: _ => oodStep ood messageLog
    grindPreR g
    powCheckR g
    let queries ← positionsR L
    let lam ← sampleE
    let queryWeights := powers lam queries.length
    let rowOffs ← openingR L
    skipEntries (p.heapQ L.level L.cap)
    let sig ← read
    let eq := eqKernelA levelFolds
    let folds := rowOffs.map fun o =>
      if L.level = 0 then foldRow0 sig eq o (L.row / 8) else foldRowE sig eq o (2 ^ L.fold)
    let enforced := dot queryWeights folds
    let intro ← sumcheckRoundPoly 3 enforced none
    let s := glue lam s (oodClaims ++ [(intro, fun x => inducedWeightK messageLog queries queryWeights x)])
    match rest with
    | [] => do
      if direct then require (directFinal residual L queries folds)
      let (tailFolds, target) ← tailRounds messageLog s.runningQuad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim =>
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      require (terminal == target)
    | _ :: _ => whirLevelsFB p logN laneFolds evaluateBasis direct g ood rest s

/-- **`verifyWhirF` at S2GB.** -/
def verifyWhirFB (p : Params) (levels : List Level) (logN : Nat) (target : FE) (evaluateBasis : List FE → FE)
    (direct : Bool) (g : Nat) (ood : Bool) : DM Unit := do
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsFB p logN ((levels.head?.map (·.fold)).getD 0) evaluateBasis direct g ood levels ⟨quad, [], []⟩

/-- **`verifyStackedOpeningG` at S2GB.** -/
def verifyStackedOpeningGB (p : Params) (levels : List Level) (stackLog : Nat) (gs : List SGroup) (direct : Bool)
    (g : Nat) (ood : Bool) : DM Unit := do
  let claims := gs.flatMap (·.flat)
  let scales := powers (← sampleE) claims.length
  verifyWhirFB p levels stackLog (dot scales (claims.map (·.2)))
    (fun point => dot scales (gs.flatMap (·.wts point))) direct g ood

end Lvm

namespace Lvm.E2L

open Lvm DM Lvm.E2V Lvm.E2T Lvm.E2U

/-- **`dOpenFFL` at S2GB.** -/
def dOpenFFLB (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × Nat × Nat))) (vs : List FE) (items : List FItem) : DM Unit := do
  require (((ti ++ items).flatMap FItem.flat).all (·.1 == .main))
  verifyStackedOpeningGB p p.mainLevels p.nuMain
    (SGroup.one (pin.weight, pin.value) :: (ti.flatMap (FItem.groups s p.nuMain) ++ linGroup s p.nuMain ζ css vs ::
      items.flatMap (FItem.groups s p.nuMain)))
    false p.grind p.mainOod

end Lvm.E2L

namespace Lvm.E2S

open RecursionFast Lvm DM Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V Lvm.E2T Lvm.E2U Lvm.E2L

/-- **The S2GB trace's sponge blocks less one** (`sizes_P20B`). -/
abbrev bB : ℕ := 4229

/-- `spongeBlocks P20B = bB + 1` (`sizes_P20B`). -/
theorem bB_eq : spongeBlocks P20B = bB + 1 := sizes_P20B.1.2.2.2.2.1

/-- **S2GB's `cont` intervals**: `contIvS` with the trace's rows `1 … bB`. -/
def contIvSB (a : ℕ) : List (ℕ × ℕ) := [(1, bB), (8080, 8110), (a + 1, a + 31)]

/-- **The decision program at S2GB** (`decideProgSG` with the sent `L0` cap, `dOpenFFLB` and the intervals `iv`). -/
def decideProgSB (p pT : Params) (iv : List (ℕ × ℕ)) (N : TNatT) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOfWS vk c sig
  let m := m3G N p
  skip (nodeBytes * 2 ^ p.capSendBits 0 (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, ti, ζ, bus) ← dTypedLG pT N m pub (typedItemsND N p)
  let tabs := M3.sumcheckTabs N.mbT
  let tp ← tapeUDGc iv rowSwitchDR p pub.s pub.n
  dOpenFFLB p (TypedV.smallT p pub) pin ti ζ ((List.range 3).map (M3.mbColsN tabs bus))
    (M3.mbValsF tabs bus ζ) (frontItemsU rowAccR p pub tp)
  pure acc

/-- **V_S's decision at S2GB** at `p`. -/
def decideFSB (p pT : Params) (iv : List (ℕ × ℕ)) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (r, s) := DM.runOnH (headerBytesP p) (decideProgSB p pT iv N vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phiT (r.pt.map Lvm.e2OfFE) == Lvm.e2OfFE r.y

/-- **The typed phases' record at S2GB**: `P20`'s with the mini-bus GKR at depth 13 (`P20B.busDepth`, RE-FREEZE P2). -/
def pTB : Params := { P20 with busDepth := 13 }

/-- **V_S's decision at S2GB** (`P20B`, the typed phases' record `pTB`, the own key leaf at `aSP`). -/
def decideFBX (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  decideFSB P20B pTB (contIvSB aSP) N vk c sig

/-- **`V_S` at S2GB** for the native typed record `N`. -/
def VSSB (N : TNatT) : SProg := fun vk c π =>
  if parseOkB P20B vk c π then driveB P20B π (decideFBX N vk c) else .ret false

end Lvm.E2S

/-! ## The S2GB instance's hypotheses (RE-FREEZE R1: the mini-bus at depth 13) -/

namespace Lvm.E2L

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.E2U Lvm.Typed LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26 LBus lvmBusProg mbClaimsL mbLinB stackOf)
open Lvm.ASM (OpenClaims GoodRel εS)
open LeanVM.Protocol.KeccakGkr (errE)
open scoped ENNReal

/-- **S2GB's typed errors at `L₀ = 1`** (`errsL_at` at bus depth 13): the fingerprint term `abError` is
`4 · 2^13 / |E| = 2^-177` (S2GS: `2^-178`); every group stays `≤ εS = 7·2^-131`, follower lead `0`. -/
theorem errsL_atB (I : M3Instance) (hμ : I.μBus = 13) : TErrsL 1 I εS 0 := by
  have hg : ∀ {c g : ℕ}, grpEps 1 c g ≤ epsS → ((1 : ℕ) : ℝ≥0∞) * errG g c ≤ εS := fun h ↦
    (le_of_eq (add_zero _).symm).trans (errG_le_εS h)
  have hab : abError I 1 = errE (1 * (4 * 2 ^ 13)) := by rw [abError, Lvm.ASM.coe_overE, Lvm.ASM.errE_smul, hμ]
  have hr : ∀ d, roundError 1 d = errE (1 * d) := fun d ↦ by
    rw [roundError, Lvm.ASM.coe_div_card, Lvm.ASM.errE_smul]
  have hl : lambdaError 1 = errE (1 * 2) := by rw [lambdaError, Lvm.ASM.coe_div_card, Lvm.ASM.errE_smul]
  have hu : unitError 1 = errE (1 * 1) := by rw [← Lvm.ASM.errE_smul]; simp [unitError, errE]
  have hM : leadMiniT 1 I 0 = errE (1 * (4 * 2 ^ 13)) := by
    rw [leadMiniT, hab, add_zero]; exact max_eq_left zero_le
  have fin : ∀ a : ℕ, a ≤ 2 ^ 62 → errE a + leadMiniT 1 I 0 ≤ εS := fun a ha ↦ by
    rw [hM, Lvm.ASM.errE_add]; exact Lvm.ASM.errE_le_εS (Nat.le_trans (Nat.add_le_add_right ha _) (by norm_num))
  refine ⟨hg (by unfold grpEps epsS; norm_num), hg (by unfold grpEps epsS; norm_num),
    hg (by unfold grpEps epsS; norm_num), hg (by unfold grpEps epsS; norm_num),
    hg (by unfold grpEps epsS; norm_num), by simpa using hg (c := 1) (g := gKappa) (by unfold grpEps epsS; norm_num),
    by simpa using hg (c := phiVarsT) (g := gT) (by unfold grpEps epsS phiVarsT selBitsT xVars yVars; norm_num),
    fun d hd ↦ ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hr]; exact fin _ (by omega)
  · rw [hab]; exact lt_of_le_of_lt (Lvm.ASM.errE_le_εS (by norm_num)) Lvm.ASM.εS_lt_one
  · rw [hab]; exact fin _ (by norm_num)
  · rw [interpLead_eq, hu, hl, Lvm.ASM.errE_smul, Lvm.ASM.errE_add]; exact fin _ (by norm_num)
  · rw [hl]; exact fin _ (by norm_num)
  · rw [hM]; exact Lvm.ASM.errE_le_εS (by norm_num)

end Lvm.E2L

namespace Lvm.E2S

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.E2U Lvm.E2L Lvm.Typed
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26 mbLinB)
open Lvm.ASM (εS)

/-- **The S2GB instance's hypotheses** (RE-FREEZE R1): `THypS`'s, with the mini-bus at depth 13 (`P20B.busDepth`,
RE-FREEZE P2) and its errors there (`errsL_atB`). -/
structure THypSB (Ti : TInst) : Prop where
  ok : Ti.Ok
  maps : Ti.MapsFit lay26
  acc : ∀ x, (pubXTS x).accIn.pt.length = phiVarsT
  accC2 : ∀ x, (∀ a ∈ (pubXTS x).accIn.pt, a.c₂ = 0) ∧ (pubXTS x).accIn.y.c₂ = 0
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ
  sc : AllSc Ti.mbT
  layOk : LayOk lay26 Ti.mbT
  keys : KeysOk Ti.mbT
  width : ∀ t ∈ Ti.mbT, 0 < t.w
  fix : FixOk Ti.mbT
  widths : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38
  lin : mbLinB Ti.mbT = true
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = 13
  errs : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), TErrsL 1 (inst lay26 Ti.mbT h) εS 0

end Lvm.E2S
