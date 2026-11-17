-- New for lvm2 S1 (E2-F, E2F-V): V_S's `KS` at `E2` (`keccakOpenD`, `verifyKeccakD`, `callerD`) refines the spec's
-- (`keccakOpenE2`, `verifyKeccakE2`, `callerProgE2`) on the width-aware stream, values through `FE2.toE2`.
import LvmE2VEqTape

/-!
# `KS` at `E2`

* `wOpen`, `wVK h`, `wCaller h`: the widths;
* **`refW_keccakOpenD`**, **`refW_verifyKeccakD`** (`12 × 2`, through the flat programs `verifyKeccakProgD`,
  `verifyKeccakProgE2` with `1 < keccakSegments` decided), **`refW_callerD`**.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open LeanVM.Protocol.Verifier (keccakSegments keccakSegmentBits keccakLaneBits keccakDepth qkeccakSlotBits)

theorem one_lt_keccakSegments : 1 < keccakSegments := by decide

theorem keccakSegmentBits_eq : keccakSegmentBits = 1 := by decide

theorem keccakLaneBits_eq : keccakLaneBits = 5 := rfl

theorem keccakDepth_eq : keccakDepth = 12 := rfl

theorem kBits_eq : Lvm.kBits = 64 := rfl

theorem rw_idx_eq {rw : ℕ → ℕ} {a b w : ℕ} (h : rw a = w) (e : a = b) : rw b = w := e ▸ h

theorem toE2_headD (l : List FE2) : toE2 (l.headD 0) = (l.map toE2).headD 0 := by
  cases l <;> simp

/-! ## The flat programs (`1 < keccakSegments` decided) -/

/-- `verifyKeccakD` with its branches decided. -/
def verifyKeccakProgD (logSteps : ℕ) (inst output : List FE2) :
    DM (List (List FE2 × FE2) × List FE2 × List FE2) :=
  samplesG E2V.gC1 keccakSegmentBits >>= fun segment ↦
  samplesG E2V.gC1 keccakLaneBits >>= fun lanePoint ↦
  readE2 >>= fun committed ↦
  keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.v1 logSteps (List.range keccakDepth)
    (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) >>= fun claim ↦
  (keccakOpenD logSteps
      (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) 1
      (keccakSegments - 1) committed >>= fun o ↦
    readE2 >>= fun word ↦
    DM.require (o.2.1.headD 0 * word == o.2.2) >>= fun _ ↦
    pure [(inst.take 5 ++ inst.drop 5 ++ o.1, word)]) >>= fun outputs ↦
  sumcheckD E2V.gC2 claim.value 3 (List.replicate 5 none) >>= fun lv ↦
  keccakOpenD logSteps claim 0 keccakSegments lv.2 >>= fun o ↦
  readE2s kBits >>= fun slices ↦
  DM.require (E2V.multilinearEvalF claim.mu lv.1 * E2V.dotF o.2.1 slices == o.2.2) >>= fun _ ↦
  pure (outputs, lv.1 ++ claim.point.take (logSteps - 5) ++ o.1, slices)

theorem verifyKeccakD_eq (logSteps : ℕ) (inst output : List FE2) :
    verifyKeccakD logSteps inst output = verifyKeccakProgD logSteps inst output := by
  simp only [verifyKeccakD, verifyKeccakProgD, if_pos one_lt_keccakSegments, bind_assoc, pure_bind]

/-- `verifyKeccakE2` with its branches decided. -/
def verifyKeccakProgE2 (logSteps : ℕ) (inst output : List E2) :
    VerifierProgram (List E2V.ColClaimE2 × List E2 × List E2) :=
  E2V.e2Samples E2V.gC1 keccakSegmentBits >>= fun segment ↦
  E2V.e2Samples E2V.gC1 keccakLaneBits >>= fun lanePoint ↦
  E2V.e2Read >>= fun committed ↦
  E2V.keccakLayersE2 LeanVM.Protocol.KeccakGkr.Shape.v1 logSteps (List.range keccakDepth)
    (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) >>= fun claim ↦
  (E2V.keccakOpenE2 logSteps
      (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) 1
      (keccakSegments - 1) committed >>= fun o ↦
    E2V.e2Read >>= fun word ↦
    VerifierProgram.require (o.2.1.headD 0 * word = o.2.2) >>= fun _ ↦
    pure [(⟨LeanVM.Protocol.Verifier.qkeccak, inst.take 5 ++ inst.drop 5 ++ o.1, word⟩ : E2V.ColClaimE2)]) >>=
    fun outputs ↦
  E2V.sumcheckE2 E2V.gC2 claim.value 3 (List.replicate 5 none) >>= fun lv ↦
  E2V.keccakOpenE2 logSteps claim 0 keccakSegments lv.2 >>= fun o ↦
  E2V.e2Reads kBits >>= fun slices ↦
  VerifierProgram.require (E2V.multilinearEvalF claim.mu lv.1 * E2V.dotF o.2.1 slices = o.2.2) >>= fun _ ↦
  pure (outputs, lv.1 ++ claim.point.take (logSteps - 5) ++ o.1, slices)

theorem verifyKeccakE2_eq (logSteps : ℕ) (inst output : List E2) :
    E2V.verifyKeccakE2 logSteps inst output = verifyKeccakProgE2 logSteps inst output := by
  simp only [E2V.verifyKeccakE2, if_pos one_lt_keccakSegments]
  rfl

/-! ## Widths and `MonoD` -/

/-- The widths of `open`. -/
def wOpen : List ℕ := wSc 3 qkeccakSlotBits

/-- The widths of `verify_keccak` at `h` instance coordinates. -/
def wVK (h : ℕ) : List ℕ :=
  List.replicate 1 8 ++ List.replicate 5 8 ++ wReads 1 ++ wLayers (h - 5 + 1) 12 ++ wOpen ++ wReads 1 ++
    wSc 3 5 ++ wOpen ++ wReads 64

/-- The widths of `KS`. -/
def wCaller (h : ℕ) : List ℕ := List.replicate h 8 ++ wReads 25 ++ wVK h

theorem monoD_keccakOpenD (logSteps : ℕ) (claim : E2V.KClaim FE2) (first count : ℕ) (value : FE2) :
    MonoD (keccakOpenD logSteps claim first count value) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_verifyKeccakProgD (logSteps : ℕ) (inst output : List FE2) :
    MonoD (verifyKeccakProgD logSteps inst output) :=
  (monoD_samplesG _ _).bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ monoD_readE2.bind fun _ ↦
    (monoD_keccakLayersD _ _ _ _).bind fun _ ↦ ((monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_verifyKeccakD (logSteps : ℕ) (inst output : List FE2) :
    MonoD (verifyKeccakD logSteps inst output) := by
  rw [verifyKeccakD_eq]; exact monoD_verifyKeccakProgD _ _ _

/-- What `open`'s two sides relate. -/
def OpenRel (x : List FE2 × List FE2 × FE2) (o : List E2 × List E2 × E2) : Prop :=
  o.1 = x.1.map toE2 ∧ o.2.1 = x.2.1.map toE2 ∧ o.2.2 = toE2 x.2.2

/-- What `verify_keccak`'s two sides relate. -/
def VKRel (x : List (List FE2 × FE2) × List FE2 × List FE2) (o : List E2V.ColClaimE2 × List E2 × List E2) :
    Prop :=
  o.1 = x.1.map (fun pw ↦ (⟨LeanVM.Protocol.Verifier.qkeccak, pw.1.map toE2, toE2 pw.2⟩ : E2V.ColClaimE2)) ∧
    o.2.1 = x.2.1.map toE2 ∧ o.2.2 = x.2.2.map toE2

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **`open`.** -/
theorem refW_keccakOpenD (logSteps : ℕ) (claim : E2V.KClaim FE2) (first count : ℕ) (value : FE2) {i : ℕ}
    (hw : WAt rw i wOpen) :
    RefAtW cap occ shp rw sig i (keccakOpenD logSteps claim first count value)
      (E2V.keccakOpenE2 logSteps (cE2 claim) first count (toE2 value)) OpenRel (i + wOpen.length) := by
  unfold keccakOpenD E2V.keccakOpenE2
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate qkeccakSlotBits none) value ?_).congr_prog ?_) ?_
  · simpa [wOpen] using hw
  · rw [map_replicate_noneE2]
  rintro sv sv' ⟨h1, h2, -⟩
  refine (RefAtW.pure ⟨h1, ?_, h2⟩).idx (by simp [wOpen])
  rw [E2V.map_toE2_foldRowsF, E2V.map_toE2_slotWeightsF, h1]

/-- **`verify_keccak` at `E2`** (`12 × 2`). -/
theorem refW_verifyKeccakD (h : ℕ) (inst output : List FE2) (hi : inst.length = h) {i : ℕ}
    (hw : WAt rw i (wVK h)) :
    RefAtW cap occ shp rw sig i (verifyKeccakD h inst output)
      (E2V.verifyKeccakE2 h (inst.map toE2) (output.map toE2)) VKRel (i + (wVK h).length) := by
  rw [wVK] at hw
  simp only [WAt.append] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩, hw6⟩, hw7⟩, hw8⟩, hw9⟩ := hw
  refine RefAtW.congr_dm (verifyKeccakD_eq h inst output).symm ?_
  refine RefAtW.congr_prog (verifyKeccakE2_eq h _ _).symm ?_
  unfold verifyKeccakProgD verifyKeccakProgE2
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ monoD_readE2.bind fun _ ↦
    (monoD_keccakLayersD _ _ _ _).bind fun _ ↦ ((monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (refW_samplesGL E2V.gC1 keccakSegmentBits hw1) ?_
  rintro seg seg' ⟨hseg, hsl⟩
  subst hseg
  refine RefAtW.bind (fun _ ↦ monoD_readE2.bind fun _ ↦
    (monoD_keccakLayersD _ _ _ _).bind fun _ ↦ ((monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (refW_samplesG E2V.gC1 keccakLaneBits (WAt.idx_eq hw2 rfl)) ?_
  intro lp lp' hlp
  subst hlp
  refine RefAtW.bind (fun _ ↦
    (monoD_keccakLayersD _ _ _ _).bind fun _ ↦ ((monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2 (rw_idx_eq (WAt.cons.1 hw3).1 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))) ?_
  intro cm cm' hcm
  subst hcm
  have hfc : cE2 (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst seg lp output cm) =
      E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 (inst.map toE2) (seg.map toE2) (lp.map toE2)
        (output.map toE2) (toE2 cm) := by
    rw [cE2, E2V.toE2_firstClaimSF]
  have hpl : (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst seg lp output cm).point.length =
      h - 5 + 1 := by
    simp [E2V.firstClaimSF, hi, hsl, keccakSegmentBits_eq]
  refine RefAtW.bind (fun _ ↦ ((monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    ((refW_keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.v1 h (h - 5 + 1) (List.range keccakDepth) _ hpl
      (WAt.idx_eq hw4 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))).congr_prog
      (by rw [hfc])) ?_
  rintro claim claim' ⟨hc, hcl⟩
  subst hc
  -- the committed output
  refine RefAtW.bind (fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind
      fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (P := E2V.keccakOpenE2 h (E2V.firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 (inst.map toE2)
        (seg.map toE2) (lp.map toE2) (output.map toE2) (toE2 cm)) 1 (keccakSegments - 1) (toE2 cm) >>= fun o ↦
      E2V.e2Read >>= fun word ↦
      VerifierProgram.require (o.2.1.headD 0 * word = o.2.2) >>= fun _ ↦
      pure [(⟨LeanVM.Protocol.Verifier.qkeccak, (inst.map toE2).take 5 ++ (inst.map toE2).drop 5 ++ o.1, word⟩ :
        E2V.ColClaimE2)])
    (R := fun outs outs' ↦ outs' = outs.map (fun pw ↦
      (⟨LeanVM.Protocol.Verifier.qkeccak, pw.1.map toE2, toE2 pw.2⟩ : E2V.ColClaimE2)))
    (j := i + keccakSegmentBits + keccakLaneBits + 1 + (wLayers (h - 5 + 1) (List.range keccakDepth).length).length +
      wOpen.length + 1)
    ?_ ?_
  · refine RefAtW.bind (fun _ ↦ monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
      ((refW_keccakOpenD h _ 1 (keccakSegments - 1) cm
        (WAt.idx_eq hw5 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))).congr_prog
        (by rw [hfc])) ?_
    rintro o o' ⟨ho1, ho2, ho3⟩
    refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
      (refW_readE2 (rw_idx_eq (WAt.cons.1 hw6).1 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))) ?_
    intro word word' hword
    subst hword
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (RefAtW.require fun hh ↦ ?_) fun _ _ _ ↦ ?_
    · have h' := congrArg toE2 (beq_iff_eq.1 hh)
      rw [Lvm.FE2.fe2_mul_eq, toE2_headD] at h'
      rw [ho2, ho3]
      exact h'
    · refine RefAtW.pure ?_
      simp [ho1, List.map_take, List.map_drop]
  rintro outs outs' houts
  refine RefAtW.bind (fun _ ↦ (monoD_keccakOpenD _ _ _ _ _).bind fun _ ↦
      (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate 5 none) claim.value
      (WAt.idx_eq hw7 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))).congr_prog
      (by rw [map_replicate_noneE2]; rfl)) ?_
  rintro lv lv' ⟨hl1, hl2, hl3⟩
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    ((refW_keccakOpenD h claim 0 keccakSegments lv.2
      (WAt.idx_eq hw8 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))).congr_prog
      (by rw [hl2])) ?_
  rintro o o' ⟨ho1, ho2, ho3⟩
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s kBits (WAt.idx_eq hw9 (by simp [keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega))) ?_
  intro sl sl' hsl'
  subst hsl'
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (RefAtW.require fun hh ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 hh)
    rw [Lvm.FE2.fe2_mul_eq, E2V.toE2_multilinearEvalF, E2V.toE2_dotF] at h'
    rw [hl1, ho2, ho3]
    exact h'
  · refine (RefAtW.pure ⟨houts, ?_, rfl⟩).idx ?_
    · simp [wVK, keccakSegmentBits_eq, keccakLaneBits_eq, keccakDepth_eq, kBits_eq, length_wReads, length_wSc, wOpen] <;> omega
    · simp [hl1, ho1, List.map_take]
      rfl

/-- What `KS`'s two sides relate. -/
def CallerRel (x : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) ×
    ((FE × (List FE → FE)) × List FE)) (o : E2V.CallerOutE2) : Prop :=
  o.1 = x.1.map toE2 ∧ o.2.1 = x.2.1.map toE2 ∧ VKRel x.2.2.1 o.2.2.1 ∧ RowRel x.2.2.2 o.2.2.2

/-- **`KS` at `E2`.** -/
theorem refW_callerD (h : ℕ) {i : ℕ} (hw : WAt rw i (wCaller h)) :
    RefAtW cap occ shp rw sig i (callerD h) (E2V.callerProgE2 h) CallerRel (i + (wCaller h).length) := by
  rw [wCaller, WAt.append, WAt.append] at hw
  obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hw
  unfold callerD E2V.callerProgE2
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_verifyKeccakD _ _ _).bind fun _ ↦
    (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _) (refW_samplesGL E2V.gC1 h hw1) ?_
  rintro r r' ⟨hr, hrl⟩
  subst hr
  refine RefAtW.bind (fun _ ↦ (monoD_verifyKeccakD _ _ _).bind fun _ ↦
    (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _) (refW_readE2s 25 (WAt.idx_eq hw2 (by simp))) ?_
  intro v v' hv
  subst hv
  refine RefAtW.bind (fun _ ↦ (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _)
    (refW_verifyKeccakD h r v hrl (WAt.idx_eq hw3 (by simp [length_wReads]; omega))) ?_
  rintro res res' hres
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    ((refW_rowSwitchD res.2.1 res.2.2).congr_prog (by rw [hres.2.1, hres.2.2])) ?_
  intro row row' hrow
  exact (RefAtW.pure ⟨rfl, rfl, hres, hrow⟩).idx (by simp [wCaller, length_wReads]; omega)

end Ref

end Lvm.VEq
