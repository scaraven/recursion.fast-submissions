-- New for lvm2 S1 (E2-F, E2F-V): V_S's tape caller at `E2` (`tapeD`: the GKR layers, the slot reduction, the chain
-- wiring) refines the spec's (`tapeProgE2`) on the width-aware stream, values through `FE2.toE2`.
import LvmE2VEqFront
import LvmE2VGkrSpec

/-!
# The tape caller at `E2`

* `cE2 c`: a claim mapped by `toE2`; widths `wLayer`, `wLayers`, `wTapeGkr`, `wSlot`, `wWire`, `wTape`;
* **`refW_verifyKeccakLayerD`**, **`refW_keccakLayersD`**, **`refW_tapeGkrD`**: the GKR (any shape);
* **`refW_slotD`**, **`refW_wireD`**: the slot reduction and the chain wiring;
* **`refW_tapeD`**: the tape caller, with V_S's statement words `s` whose bits are the digest's (`sBitsD`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)

/-- A claim mapped by `toE2`. -/
abbrev cE2 (c : E2V.KClaim FE2) : E2V.KClaim E2 := E2V.KClaim.map E2V.toE2Hom c

/-! ## Widths -/

/-- One layer at a claim point of `pl` coordinates. -/
def wLayer (pl : ℕ) : List ℕ := wReads 47 ++ wSampleG ++ wPack pl ++ wSc 4 11 ++ wReads 3 ++ wSampleG

/-- `n` layers. -/
def wLayers (pl n : ℕ) : List ℕ := (List.replicate n (wLayer pl)).flatten

theorem wLayers_succ (pl n : ℕ) : wLayers pl (n + 1) = wLayer pl ++ wLayers pl n := by
  rw [wLayers, List.replicate_succ, List.flatten_cons, ← wLayers]

/-! ## `MonoD` -/

theorem monoD_verifyKeccakLayerD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ)
    (claim : E2V.KClaim FE2) : MonoD (verifyKeccakLayerD sh logSteps step claim) :=
  (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sepE2.bind fun _ ↦
    (monoD_sampleG _).bind fun _ ↦ (monoD_packRoundsD _ _ _ _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind
      fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sampleG _).bind
        fun _ ↦ MonoD.pure _

theorem monoD_keccakLayersD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : E2V.KClaim FE2), MonoD (keccakLayersD sh logSteps steps claim)
  | [], _ => MonoD.pure _
  | s :: steps, c => (monoD_verifyKeccakLayerD sh logSteps s c).bind fun _ ↦
      monoD_keccakLayersD sh logSteps steps _

theorem monoD_tapeGkrD (h : ℕ) (inst output : List FE2) : MonoD (tapeGkrD h inst output) :=
  (monoD_samplesG _ _).bind fun _ ↦ monoD_keccakLayersD _ _ _ _

theorem monoD_slotD (b sb blk : ℕ) (W : ℕ → ℕ → FE2) (pt : List FE2) (v : FE2) :
    MonoD (slotD b sb blk W pt v) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_wireD (w sb dsel : ℕ) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    MonoD (wireD w sb dsel s n claim) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_tapeD (w sb dsel : ℕ) (s : List FK) (n : ℕ) : MonoD (tapeD w sb dsel s n) :=
  monoD_sepE2.bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireD _ _ _ _ _ _).bind
      fun _ ↦ MonoD.pure _

theorem map_replicate_noneE2 (n : ℕ) :
    (List.replicate n (none : Option FE2)).map (Option.map toE2) = List.replicate n none := by
  simp

/-! ## A layer with projections (`LvmE2VGkrSpec.layerProgE2`'s twin) -/

theorem kclaim_ext {a b : E2V.KClaim E2} (h1 : a.value = b.value) (h2 : a.mu = b.mu)
    (h3 : a.point = b.point) (h4 : a.weights = b.weights) : a = b := by
  cases a; cases b; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

/-- A layer's tail on `DM`. -/
def layerTailD (claim : E2V.KClaim FE2) (s : FE2) (vsp : FE2 × FE2 × List FE2) (lv : List FE2 × FE2) :
    DM (E2V.KClaim FE2) :=
  readE2s 3 >>= fun t ↦
  DM.require (vsp.2.1 * E2V.dotF ((E2V.eqKernelF lv.1).take LeanVM.Protocol.Verifier.keccakBits)
    claim.weights * (E2V.sumF (E2V.instWeightsF s) * t.getD 0 0 +
      (E2V.sumF (E2V.instWeightsF s) + t.getD 1 0) * t.getD 2 0) == lv.2) >>= fun _ ↦
  sampleG E2V.gC2 >>= fun beta ↦
  pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), E2V.instWeightsF s, vsp.2.2,
    E2V.linearTransposeF ((List.range LeanVM.Protocol.Verifier.keccakBits).map fun j =>
      (E2V.eqKernelF lv.1).getD j 0 + beta * ((E2V.eqKernelF lv.1).getD
        (LeanVM.Protocol.Verifier.keccakAlong j 4) 0 + beta * (E2V.eqKernelF lv.1).getD
          (LeanVM.Protocol.Verifier.keccakAlong j 3) 0))⟩

/-- A layer on `DM`, with projections. -/
def layerProgD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (claim : E2V.KClaim FE2) :
    DM (E2V.KClaim FE2) :=
  readE2s productBits >>= fun product ↦
  DM.require (E2V.projectedF claim product + E2V.iotaSF sh logSteps step claim * E2V.sumF claim.mu ==
    claim.value) >>= fun _ ↦
  sepE2 >>= fun _ ↦
  sampleG E2V.gC46 >>= fun s ↦
  packRoundsD E2V.gC3 claim.point (E2V.polyEvalF product s) 1 >>= fun vsp ↦
  sumcheckD E2V.gC3 vsp.1 4 (List.replicate LeanVM.Protocol.Verifier.keccakLocalBits none) >>= fun lv ↦
  layerTailD claim s vsp lv

theorem verifyKeccakLayerD_eq (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ)
    (claim : E2V.KClaim FE2) : verifyKeccakLayerD sh logSteps step claim = layerProgD sh logSteps step claim :=
  rfl

theorem monoD_layerTailD (claim : E2V.KClaim FE2) (s : FE2) (vsp : FE2 × FE2 × List FE2)
    (lv : List FE2 × FE2) : MonoD (layerTailD claim s vsp lv) :=
  (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sampleG _).bind fun _ ↦ MonoD.pure _

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **A layer's tail** (`t`, the final check, `β`, the next claim). -/
theorem refW_layerTailD (claim : E2V.KClaim FE2) (s : FE2) (vsp : FE2 × FE2 × List FE2)
    (lv : List FE2 × FE2) {i : ℕ} (hw : WAt rw i (wReads 3 ++ wSampleG)) :
    RefAtW cap occ shp rw sig i (layerTailD claim s vsp lv)
      (E2V.layerTailE2 (cE2 claim) (toE2 s) (toE2 vsp.1, toE2 vsp.2.1, vsp.2.2.map toE2)
        (lv.1.map toE2, toE2 lv.2))
      (fun c c' ↦ c' = cE2 c ∧ c.point = vsp.2.2) (i + 4) := by
  rw [WAt.append, wSampleG, WAt.cons] at hw
  unfold layerTailD E2V.layerTailE2
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sampleG _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 3 hw.1) ?_
  intro t t' ht
  subst ht
  refine RefAtW.bind (fun _ ↦ (monoD_sampleG _).bind fun _ ↦ MonoD.pure _) (RefAtW.require fun h ↦ ?_)
    fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    simp only [Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_add, E2V.toE2_dotF, List.map_take, E2V.map_toE2_eqKernelF,
      E2V.toE2_sumF, E2V.map_toE2_instWeightsF, toE2_getD] at h'
    exact h'
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_sampleG E2V.gC2 (by simpa [length_wReads] using hw.2.1)) ?_
  intro b b' hb
  subst hb
  refine (RefAtW.pure ⟨kclaim_ext ?_ ?_ ?_ ?_, rfl⟩).idx (by simp [length_wReads])
  · show _ = toE2 _
    simp only [Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, toE2_getD]
  · show _ = List.map toE2 _
    rw [E2V.map_toE2_instWeightsF]
  · rfl
  · show _ = List.map toE2 _
    rw [E2V.map_toE2_linearTransposeF]
    refine congrArg E2V.linearTransposeF ?_
    rw [E2V.batchWF, List.map_map, E2V.keccakAlong_eqV,
      show Lvm.keccakBits = LeanVM.Protocol.Verifier.keccakBits from rfl]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp_apply, Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, toE2_getD,
      E2V.map_toE2_eqKernelF]

set_option maxHeartbeats 400000 in
/-- **One GKR layer at `E2`.** -/
theorem refW_verifyKeccakLayerD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ)
    (claim : E2V.KClaim FE2) {i : ℕ} (hw : WAt rw i (wLayer claim.point.length)) :
    RefAtW cap occ shp rw sig i (verifyKeccakLayerD sh logSteps step claim)
      (E2V.verifyKeccakLayerE2 sh logSteps step (cE2 claim))
      (fun c c' ↦ c' = cE2 c ∧ c.point.length = claim.point.length)
      (i + (wLayer claim.point.length).length) := by
  rw [wLayer, WAt.append, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hw
  rw [wSampleG, WAt.cons] at h2
  refine RefAtW.congr_dm (verifyKeccakLayerD_eq sh logSteps step claim).symm ?_
  refine RefAtW.congr_prog (E2V.verifyKeccakLayerE2_eq sh logSteps step (cE2 claim)).symm ?_
  unfold layerProgD E2V.layerProgE2
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sepE2.bind fun _ ↦
    (monoD_sampleG _).bind fun _ ↦ (monoD_packRoundsD _ _ _ _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind
      fun _ ↦ monoD_layerTailD _ _ _ _) (refW_readE2s productBits h1) ?_
  intro product product' hp
  subst hp
  refine RefAtW.bind (fun _ ↦ monoD_sepE2.bind fun _ ↦
    (monoD_sampleG _).bind fun _ ↦ (monoD_packRoundsD _ _ _ _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind
      fun _ ↦ monoD_layerTailD _ _ _ _) (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    rw [Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, E2V.toE2_projectedF, E2V.toE2_iotaSF, E2V.toE2_sumF] at h'
    exact h'
  refine RefAtW.bind (fun _ ↦
    (monoD_sampleG _).bind fun _ ↦ (monoD_packRoundsD _ _ _ _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind
      fun _ ↦ monoD_layerTailD _ _ _ _) refW_sepE2 fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (monoD_packRoundsD _ _ _ _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind
      fun _ ↦ monoD_layerTailD _ _ _ _)
    (refW_sampleG E2V.gC46 (by simpa [length_wReads, show productBits = 47 from rfl] using h2.1)) ?_
  intro s s' hs
  subst hs
  have hpk := refW_packRoundsD (cap := cap) (occ := occ) (shp := shp) (sig := sig) E2V.gC3 claim.point
    (E2V.polyEvalF product s) 1 (by simpa [length_wReads, wSampleG, show productBits = 47 from rfl] using h3)
  rw [E2V.toE2_polyEvalF, Lvm.FE2.toE2_one] at hpk
  refine RefAtW.bind (fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ monoD_layerTailD _ _ _ _) hpk ?_
  intro vsp vsp' hv
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  refine RefAtW.bind (fun _ ↦ monoD_layerTailD _ _ _ _)
    ((refW_sumcheckD E2V.gC3 4 (by norm_num)
      (List.replicate LeanVM.Protocol.Verifier.keccakLocalBits none) vsp.1 ?_).congr_prog ?_) ?_
  · refine WAt.idx_eq h4 (by simp [length_wReads, wSampleG, wPack, length_wSc, show LeanVM.Protocol.Verifier.keccakLocalBits = 11 from rfl]; omega)
  · rw [map_replicate_noneE2, ← hv1]
  intro lv lv' hl
  obtain ⟨hl1, hl2, hl3⟩ := hl
  refine ((refW_layerTailD claim s vsp lv (WAt.append.2 ⟨?_, ?_⟩)).congr_prog ?_).mono ?_ |>.idx ?_
  · refine WAt.idx_eq h5 (by simp [length_wReads, wSampleG, wPack, length_wSc, show LeanVM.Protocol.Verifier.keccakLocalBits = 11 from rfl]; omega)
  · refine WAt.idx_eq h6 (by simp [length_wReads, wSampleG, wPack, length_wSc, show LeanVM.Protocol.Verifier.keccakLocalBits = 11 from rfl]; omega)
  · rw [show vsp' = (vsp'.1, vsp'.2.1, vsp'.2.2) from rfl, show lv' = (lv'.1, lv'.2) from rfl,
      hv1, hv2, hv3, hl1, hl2]
  · exact fun c c' hc ↦ ⟨hc.1, by rw [hc.2, hv4]⟩
  · simp [wLayer, length_wReads, wSampleG, wPack, length_wSc,
      show LeanVM.Protocol.Verifier.keccakLocalBits = 11 from rfl]
    omega

/-- **The layers.** -/
theorem refW_keccakLayersD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps pl : ℕ) :
    ∀ (steps : List ℕ) (claim : E2V.KClaim FE2) {i : ℕ}, claim.point.length = pl →
    WAt rw i (wLayers pl steps.length) →
    RefAtW cap occ shp rw sig i (keccakLayersD sh logSteps steps claim)
      (E2V.keccakLayersE2 sh logSteps steps (cE2 claim))
      (fun c c' ↦ c' = cE2 c ∧ c.point.length = pl) (i + (wLayers pl steps.length).length)
  | [], claim, i, hpl, _ => RefAtW.pure ⟨rfl, hpl⟩
  | step :: steps, claim, i, hpl, hw => by
    rw [List.length_cons, wLayers_succ, WAt.append] at hw
    subst hpl
    refine RefAtW.bind (fun _ ↦ monoD_keccakLayersD _ _ _ _)
      (refW_verifyKeccakLayerD sh logSteps step claim hw.1) ?_
    rintro c c' ⟨hc, hcl⟩
    subst hc
    refine (refW_keccakLayersD sh logSteps claim.point.length steps c hcl hw.2).idx ?_
    rw [List.length_cons, wLayers_succ, List.length_append, Nat.add_assoc]

/-- The widths of the tape's GKR at `h` instance coordinates. -/
def wTapeGkr (h : ℕ) : List ℕ := List.replicate 5 8 ++ wLayers (h - 4) 24

/-- **The tape's GKR.** -/
theorem refW_tapeGkrD (h : ℕ) (inst output : List FE2) (hi : inst.length = h) {i : ℕ}
    (hw : WAt rw i (wTapeGkr h)) :
    RefAtW cap occ shp rw sig i (tapeGkrD h inst output)
      (E2V.tapeGkrE2 h (inst.map toE2) (output.map toE2))
      (fun c c' ↦ c' = cE2 c ∧ c.point.length = h - 4) (i + (wTapeGkr h).length) := by
  rw [wTapeGkr, WAt.append] at hw
  unfold tapeGkrD E2V.tapeGkrE2
  refine RefAtW.bind (fun _ ↦ monoD_keccakLayersD _ _ _ _)
    (refW_samplesG E2V.gC1 LeanVM.Protocol.Verifier.keccakLaneBits hw.1) ?_
  intro lp lp' hlp
  subst hlp
  refine ((refW_keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.tape h (h - 4) (List.range 24)
    (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] lp output 0) ?_ ?_).congr_prog ?_).idx ?_
  · simp [E2V.firstClaimSF, hi]
  · exact WAt.idx_eq hw.2 (by simp [LeanVM.Protocol.Verifier.keccakLaneBits])
  · rw [cE2, E2V.toE2_firstClaimSF, List.map_nil, Lvm.FE2.toE2_zero]
  · simp [wTapeGkr, LeanVM.Protocol.Verifier.keccakLaneBits]
    omega

/-- `n` ground challenges, with the native list's length. -/
theorem refW_samplesGL (g : ℕ) (n : ℕ) {i : ℕ} (hw : WAt rw i (List.replicate n 8)) :
    RefAtW cap occ shp rw sig i (samplesG g n) (E2V.e2Samples g n)
      (fun xs ys ↦ ys = xs.map toE2 ∧ xs.length = n) (i + n) := by
  induction n generalizing i with
  | zero => exact RefAtW.pure ⟨rfl, rfl⟩
  | succ n ih =>
    rw [List.replicate_succ, WAt.cons] at hw
    refine RefAtW.bind (fun _ ↦ (monoD_samplesG g n).bind fun _ ↦ MonoD.pure _)
      (refW_sampleG g hw.1) ?_
    intro x y hxy
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (ih hw.2) ?_
    intro xs ys hs
    exact (RefAtW.pure ⟨by simp [hxy, hs.1], by simp [hs.2]⟩).idx (by omega)

/-- The widths of a slot reduction of `b` rounds. -/
def wSlot (b : ℕ) : List ℕ := wSc 3 b ++ wReads 64

/-- What a slot reduction's two sides relate. -/
def SlotRelW (x : (List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))
    (o : E2V.SlotOutE2) : Prop :=
  o.sl.1 = x.1.1.map toE2 ∧ o.sl.2 = toE2 x.1.2 ∧ o.sv = x.2.1.map toE2 ∧ RowRel x.2.2 o.row

/-- **A slot reduction.** -/
theorem refW_slotD (b sb blk : ℕ) (W : ℕ → ℕ → FE2) (pt : List FE2) (v : FE2) {i : ℕ}
    (hw : WAt rw i (wSlot b)) :
    RefAtW cap occ shp rw sig i (slotD b sb blk W pt v)
      (E2V.slotProgE2 b sb blk (fun o z ↦ toE2 (W o z)) (pt.map toE2) (toE2 v)) SlotRelW
      (i + (wSlot b).length) := by
  rw [wSlot, WAt.append] at hw
  unfold slotD E2V.slotProgE2
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate b none) v ?_).congr_prog ?_) ?_
  · simpa using hw.1
  · rw [map_replicate_noneE2]
  rintro sl sl' ⟨h1, h2, -⟩
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_rowSwitchD _ _).bind fun _ ↦
    MonoD.pure _) (refW_readE2s 64 (WAt.idx_eq hw.2 (by simp))) ?_
  intro sv sv' hsv
  subst hsv
  refine RefAtW.bind (fun _ ↦ (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    rw [h2, h', E2V.toE2_sumF, List.map_map]
    congr 1
    refine List.map_congr_left fun z _ ↦ ?_
    simp only [Function.comp_apply, Lvm.FE2.fe2_mul_eq, E2V.toE2_slotWF, toE2_getD, h1]
  · refine RefAtW.bind (fun _ ↦ MonoD.pure _)
      ((refW_rowSwitchD (pt ++ sl.1 ++ E2V.selPtF blk sb) sv).congr_prog ?_) fun row row' hr ↦ ?_
    · rw [List.map_append, List.map_append, E2V.map_toE2_selPtF, ← h1]
    · exact (RefAtW.pure ⟨h1, h2, rfl, hr⟩).idx (by simp [wSlot, length_wReads]; omega)

/-- The widths of the chain wiring at `w` row coordinates. -/
def wWire (w : ℕ) : List ℕ := wSc 3 w ++ wReads 1 ++ wSlot 2

/-- What the chain wiring's two sides relate. -/
def WireRelW (x : (List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 ×
    ((FE × (List FE → FE)) × List FE))) (o : E2V.WireChOutE2) : Prop :=
  o.sc.1 = x.1.1.map toE2 ∧ o.sc.2 = toE2 x.1.2 ∧ o.g = x.2.1.map toE2 ∧ SlotRelW x.2.2 o.d

/-- **The chain wiring.** -/
theorem refW_wireD (w sb dsel : ℕ) (s : List FK) (d : RecursionFast.Digest)
    (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ) (claim : E2V.KClaim FE2) {i : ℕ}
    (hw : WAt rw i (wWire w)) :
    RefAtW cap occ shp rw sig i (wireD w sb dsel s n claim) (E2V.wireChProgE2 w sb dsel d n (cE2 claim))
      WireRelW (i + (wWire w).length) := by
  rw [wWire, WAt.append, WAt.append] at hw
  obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hw
  unfold wireD E2V.wireChProgE2
  rw [hs]
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate w none)
      (wireTargetD (Lvm.KG.digestBits d) n claim) ?_).congr_prog ?_) ?_
  · simpa using hw1
  · rw [map_replicate_noneE2, E2V.toE2_wireTargetD]
  rintro sc sc' ⟨h1, h2, -⟩
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    MonoD.pure _) (refW_readE2s 1 (WAt.idx_eq hw2 (by simp))) ?_
  intro g g' hg
  subst hg
  refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    rw [h2, h', Lvm.FE2.fe2_mul_eq, E2V.toE2_msEvalF, toE2_getD, h1]
    rfl
  · have hW : (fun o z ↦ toE2 (E2V.dWF claim.weights o z)) = E2V.dWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ E2V.toE2_dWF _ _ _
    refine RefAtW.bind (fun _ ↦ MonoD.pure _)
      ((refW_slotD 2 sb dsel (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
        (WAt.idx_eq hw3 (by simp [length_wReads]; omega))).congr_prog
        ?_) fun dd dd' hd ↦ ?_
    · rw [hW, toE2_getD, ← h1]
      rfl
    · exact (RefAtW.pure ⟨h1, h2, rfl, hd⟩).idx (by simp [wSlot, wWire, length_wReads]; omega)

/-- The widths of the tape caller at `w` row coordinates. -/
def wTape (w : ℕ) : List ℕ := List.replicate w 8 ++ wReads 25 ++ wTapeGkr w ++ wWire w

/-- What the tape caller's two sides relate. -/
def TapeRelW (x : List FE2 × List FE2 × E2V.KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))))
    (o : E2V.TapeOutE2) : Prop :=
  o.1 = x.1.map toE2 ∧ o.2.1 = x.2.1.map toE2 ∧ o.2.2.1 = cE2 x.2.2.1 ∧ WireRelW x.2.2.2 o.2.2.2

/-- **The tape caller** (V_S's statement words `s` with the digest's bits). -/
theorem refW_tapeD (w sb dsel : ℕ) (s : List FK) (d : RecursionFast.Digest)
    (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ) {i : ℕ} (hw : WAt rw i (wTape w)) :
    RefAtW cap occ shp rw sig i (tapeD w sb dsel s n) (E2V.tapeProgE2 w sb dsel d n) TapeRelW
      (i + (wTape w).length) := by
  rw [wTape, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩ := hw
  unfold tapeD E2V.tapeProgE2
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireD _ _ _ _ _ _).bind
      fun _ ↦ MonoD.pure _) refW_sepE2 fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireD _ _ _ _ _ _).bind
      fun _ ↦ MonoD.pure _) (refW_samplesGL E2V.gC1 w hw1) ?_
  rintro r r' ⟨hr, hrl⟩
  subst hr
  refine RefAtW.bind (fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_wireD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _) (refW_readE2s 25 (WAt.idx_eq hw2 (by simp))) ?_
  intro v v' hv
  subst hv
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_wireD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_tapeGkrD w r v hrl (WAt.idx_eq hw3 (by simp [length_wReads]; omega))) ?_
  rintro c c' ⟨hc, -⟩
  subst hc
  refine RefAtW.bind (fun _ ↦ (monoD_wireD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.require fun h ↦ of_decide_eq_true h) fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    (refW_wireD w sb dsel s d hs n c (WAt.idx_eq hw4 (by simp [length_wReads, Nat.add_assoc]))) ?_
  intro wo wo' hwo
  exact (RefAtW.pure ⟨rfl, rfl, rfl, hwo⟩).idx (by simp [wTape, length_wReads, Nat.add_assoc])

end Ref

end Lvm.VEq
