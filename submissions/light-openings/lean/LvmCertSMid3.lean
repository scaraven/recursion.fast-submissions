-- WP-16b (CERT). New for lvm (O6): `MidSpec (midS tabs)` for WP-14a's middle phases, from WP-9b's
-- `midBusTableSpecS` and WP-8's `kgSpec` (lvm2 S2: `kgSpecS`, the tape then `KS`) (WP-14's glue
-- `LvmCertSMid.midSpecOf`, here with the programs' return facts), the semantic link of `assembleS`'s claims (`LvmCertSMid3Tab/Kec/Link`)
-- and its side conditions (`LvmCertSMid3Side`); `MidShape (midS tabs)`; `NodeSound` for the good
-- pair `GoodS` from WP-14c's `GoodN`.
import LvmVEqFit
import LvmCertSInv
import LvmAccSpecT
import LvmM3MidCert
import LvmCertSExt
import LvmVEqMid
import LvmKeccakCallerTape
import LvmCertSMid3Blk
import LvmVEqParse
-- (GOLF2 import pruning: dropped LvmChainTablePad: unused by this module.)

-- (GOLF2: 47 declarations that `certified` does not use moved verbatim to `LvmMPCertOff`, outside its import closure.)

-- ===== merged from `LvmAccSpecMid` (GOLF module merge: `LvmAccSpecMid.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- new for lvm (AC-S): V_S phases 2–3b in the form WP-14's `MidSpec` composes, as WP-9b's
-- `midBusTableSpec` → `midBusTableSpec'` → `midBusTableSpecB` → `midBusTableSpecS` (`LvmM3Mid`,
-- `LvmM3MidPost`, `LvmM3MidCert`) do for phases 2–3, with `lbusTableAccSpec` in place of
-- `lbusTableCheckSpec` and `AccOk acc_in` carried in the candidates' predicate.

/-!
# Phases 2–3b on WP-14's candidate pairs

* `cg_accProg`, **`noCG_lbusTableAccProg`**: phases 2–3b commit nothing and ask no proof of work;
* `midBusTableAccSpec` (glued at the candidate set, WP-9b's `Spec.glue`), `midBusTableAccSpec'`,
  `midBusTableAccSpecB`;
* **`midBusTableAccSpecS`** (WP-14's objects, `lay26`): from `RootShape ∧ Doomed candPairs (M3Holds ∘
  stackOf ∧ R ∧ AccOk acc_in)` to `Doomed candPairs ((∀ c ∈ cl, BlockHolds …) ∧ R) ∧ RootShape`:
  WP-9b's `midBusTableSpecS` with `AccOk` discharged (BLUEPRINT §12.6: `Good := GoodN ∧ AccOk`).
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV Lay inst colOfL TablePostC lvmBusTableProg
  NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_lvmBusProg
  cg_tablePhaseClaims MidTablePost CandIdx candIdx candSet oraOf publicLines_lvm auxAt_lvm
  CommittedHolds BlockHolds stackOf lay26 holds_of_committed committedHolds_iff_block)
open scoped ENNReal

/-! ## No commitment, no proof of work -/

theorem cg_accProg (dk D : ℕ) (ok : Bool) (yIn : E) (a : List E) (yOwn : List E → E)
    (bOf : List E → List E) (Φ : List E → E) : NoCG (accProg dk D ok yIn a yOwn bOf Φ) :=
  Lvm.M3.NoCG.bind (cg_sampleChallenges dk) fun _ ↦ Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦
    Lvm.M3.NoCG.bind cg_sample fun _ ↦ Lvm.M3.NoCG.bind cg_readScalar fun _ ↦ cg_require _

/-! ## Glued at the candidate set -/

section Mid

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **Phases 2–3b in `MidSpec`'s form** (WP-9b's `midBusTableSpec` with phase 3b): from
`Doomed C (M3Holds ∘ stk ∧ R ∧ AccOk acc_in)` to `MidTablePost`. -/
noncomputable def midBusTableAccSpec (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L (sumcheckTabs (tabs pub)) hτL) () (stk p) ∧ R p ∧
          AccOkE P tabs pub) h)
      (MidTablePost L (sumcheckTabs (tabs pub)) hτL C stk R) εmax
      (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  let σ := candIdx L (sumcheckTabs (tabs pub)) hτL C stk R hf hc
  ((Lvm.M3.Spec.glue (Pre := fun (S : CandIdx L (sumcheckTabs (tabs pub)) hτL L₀) ↦
        HDoom (candsA (fun _ ↦ S.1) (AccOkE P tabs pub))
          (Seam.commit (inst L (sumcheckTabs (tabs pub)) hτL)) ())
      (Post := fun (S : CandIdx L (sumcheckTabs (tabs pub)) hτL L₀) ↦
        TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) (fun _ ↦ S.1) ()
          (colOfL L (sumcheckTabs (tabs pub)) hτL))
      σ G (fun h₀ l hG ↦ by simp only [σ, candIdx, candSet, hCG h₀ l hG])
      fun S ↦ lbusTableAccSpec L P tabs pub hτL hsc (fun _ ↦ S.1) H hkey hw (fun _ ↦ S.2.1)
        (fun _ ↦ S.2.2) hμ hab he4 hT hlam he3 hTa hxi hD hTf)).mono
    (fun h ⟨hG, ⟨W, hW⟩, hDm⟩ ↦ ⟨hG, W, hW, fun o ⟨ho, hA⟩ hR ↦ by
      obtain ⟨p, ⟨hpC, hpR⟩, rfl⟩ := ho
      exact hDm p hpC ⟨hR, hpR, hA⟩⟩)
    (fun cl h hp ↦ by
      obtain ⟨W, tout, -, hDm, -, hcl, hout⟩ := hp
      refine ⟨tout, fun p hpC ⟨hcm, hpR⟩ ↦ hDm _ ⟨p, ⟨hpC, hpR⟩, rfl⟩
        ⟨hcm, publicLines_lvm L _ hτL _, auxAt_lvm L _ hτL _ _⟩, hcl, hout⟩)
    le_rfl le_rfl le_rfl

end Mid

section Blocks

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  {L₀ : ℕ} {εmax : ℝ≥0∞}

end Blocks

section Pairs

variable (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ lay26.μ) {L₀ : ℕ} {εmax : ℝ≥0∞}

end Pairs

end Lvm.Acc
end
-- ===== end of `LvmAccSpecMid` =====

-- ===== merged from `LvmCertSMid` (GOLF module merge: `LvmCertSMid.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- WP-14 (ASM). New for lvm (O6 glue): `MidSpec` for middle phases of the shape
-- `bus >>= kg >>= ret (assemble …)` from a bus/table phase specification (WP-9b `midBusTableSpecS`
-- form), a Keccak phase specification (WP-8 `kgSpec` form, framed with `RootShape`) and the
-- semantic link of the assembled stack claims.

/-!
# The middle phases' specification from its phases (O6 glue)

**`midSpecOf`**: for `mid x = busP x >>= fun a ↦ kgP >>= fun k ↦ ret (asm x a k)`, a specification of
`busP x` from `RootShape ∧ Doomed candPairs (Gb x ∧ Gk)` to `Doomed candPairs (B x a ∧ Gk) ∧
RootShape`, one of `kgP` from `Doomed candPairs (Gk ∧ B x a)` to `Doomed candPairs (Kc k ∧ B x a)`
(`kgP` commits nothing, so `RootShape` is framed across it), and the link "the assembled claims hold
on a pair ⇒ `Kc k ∧ B x a` on it" with the claims multiaffine and at most `2^63` give
`MidSpec mid (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk (qm, qr)) εS Lb`. **`midShapeOf`**: its shape.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front (Doomed)
open scoped ENNReal

/-- A pair of candidates. -/
abbrev Pair : Type := Column CMain.nu20 × Column 19

theorem rootShape_append' {h₀ l : List Ev} (hl : commits l = []) (hr : RootShape h₀) :
    RootShape (h₀ ++ l) := by
  obtain ⟨Wm, Wr, hc, hw⟩ := hr
  exact ⟨Wm, Wr, by rw [LeanVM.Protocol.Whir.Sound.commits_append, hl, List.append_nil, hc], hw⟩

section Glue

variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb : List UInt8 → Pair → Prop} {Gk : Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : κ → Pair → Prop} {Lb Lk : ℝ≥0∞}

end Glue

end Lvm.ASM
end
-- ===== end of `LvmCertSMid` =====

-- ===== merged from `LvmCertSMid2` (GOLF module merge: `LvmCertSMid2.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- WP-14d (EXQ). New for lvm (O6, first pieces): the structural and numeric parts of instantiating
-- WP-14's glue (`LvmCertSMid.midSpecOf`/`midShapeOf`) with WP-14a's middle phases `midS`
-- (`LvmVEqMid`): no commitment and no proof of work in V_S phases 4–7 (`kgProgS`, after WP-9b's
-- `noCG_lbusTableCheckProg` pattern), `MidShape (midS tabs)` from the `C_rec` claims'
-- multiaffinity, WP-8 `kgSpec`'s error side conditions at `εS` with one candidate pair, and the
-- invariance of `MidSpec` under an equivalent `Good`.

/-!
# O6 parts for `midS`

* `cg_verifyKeccak`, `cg_ringSwitch`, `cg_callerProg`, `cg_ksLinkProg`, lvm2 S2's
  `cg_verifyKeccakLayerS`, `cg_tapeGkr`, `cg_slotProg`, `cg_wireChProg`, `cg_tapeProg`,
  **`cg_kgProgS`**: `NoCommit ∧ NoGrind` (WP-9b's `NoCG`; `midS`'s shape is
  `LvmAccSpecCert.midShape_midSA`; lvm2 S2-CERT dropped the unused `cg_midS`/`midShape_midS`, 24 s
  of elaboration);
* **`kg_errsJ2`**: `kgSpecS`'s side conditions `h46 h2 hrK hrKL` at `εmax = εS`, `L₀ = 37,696 = 124·304`
  (lvm2 J2′: `candPairs_ncard_le`), P20's tape `w = 20`, `Pk = 9` (KS13), and its lead `≤ εS`;
* **`kgSpecS`** (lvm2 S2): V_S phases 4–7, T-V's `tapeSpec` then WP-8's `ksPhaseSpec`;
* `midSpec_congr`: `MidSpec` depends on `Good` only up to pointwise equivalence (WP-14c's
  `GoodN = GoodB ∧ GoodK` against `midSpecOf`'s `Gb x ∧ Gk`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges
  cg_roundPoly cg_sumcheck noCG_lbusTableCheckProg)
open scoped ENNReal

/-! ## No commitment, no proof of work -/

theorem cg_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    NoCG (LeanVM.Protocol.Verifier.keccakPackRounds rs value scale)
  | [], _, _ => cg_ret _
  | r :: rs, value, scale => by
    unfold LeanVM.Protocol.Verifier.keccakPackRounds
    refine NoCG.bind (cg_roundPoly _ _ _) fun _ ↦ NoCG.bind cg_sample fun _ ↦
      NoCG.bind (cg_keccakPackRounds rs _ _) fun t ↦ ?_
    obtain ⟨v, s, pt⟩ := t
    exact cg_ret _

theorem cg_verifyKeccakLayer (logSteps step : ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim) :
    NoCG (LeanVM.Protocol.Verifier.verifyKeccakLayer logSteps step claim) := by
  unfold LeanVM.Protocol.Verifier.verifyKeccakLayer
  refine NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_keccakPackRounds _ _ _) fun t ↦ ?_
  obtain ⟨v, s, pt⟩ := t
  refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨lp, v'⟩ := u
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_sample fun _ ↦ cg_ret _

theorem cg_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim),
    NoCG (LeanVM.Protocol.Verifier.keccakLayers logSteps steps claim)
  | [], _ => cg_ret _
  | s :: steps, claim => by
    unfold LeanVM.Protocol.Verifier.keccakLayers
    exact NoCG.bind (cg_verifyKeccakLayer _ _ _) fun _ ↦ cg_keccakLayers logSteps steps _

theorem cg_keccakOpen (logSteps : ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim) (first count : ℕ) (value : E) :
    NoCG (LeanVM.Protocol.Verifier.keccakOpen logSteps claim first count value) := by
  unfold LeanVM.Protocol.Verifier.keccakOpen
  refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨slot, v⟩ := u
  exact cg_ret _

theorem cg_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoCG (LeanVM.Protocol.Verifier.verifyKeccak logSteps inst output) := by
  unfold LeanVM.Protocol.Verifier.verifyKeccak
  refine NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_sampleChallenges _) fun _ ↦
    NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_keccakLayers _ _ _) fun _ ↦
      NoCG.bind (cg_keccakOpen _ _ _ _ _) fun t ↦ ?_
  obtain ⟨slot, w, v⟩ := t
  refine NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ ?_
  first
    | refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
    | refine NoCG.bind (cg_ret _) fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨low, v'⟩ := u
  refine NoCG.bind (cg_keccakOpen _ _ _ _ _) fun t' ↦ ?_
  obtain ⟨slot', w', v''⟩ := t'
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_ringSwitch (point s : List E) : NoCG (LeanVM.Protocol.Verifier.ringSwitch point s) := by
  unfold LeanVM.Protocol.Verifier.ringSwitch
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ cg_ret _

theorem cg_callerProg (h : ℕ) : NoCG (Lvm.KG.callerProg h) := by
  unfold Lvm.KG.callerProg
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_verifyKeccak _ _ _) fun _ ↦ NoCG.bind (cg_ringSwitch _ _) fun _ ↦ cg_ret _

theorem cg_ksLinkProg (hk r : ℕ) (rows : List ℕ) : NoCG (Lvm.KG.ksLinkProg hk r rows) := by
  unfold Lvm.KG.ksLinkProg
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun _ ↦
    NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_verifyKeccakLayerS (sh : KeccakGkr.Shape) (logSteps step : ℕ)
    (claim : LeanVM.Protocol.Verifier.KeccakClaim) : NoCG (verifyKeccakLayerS sh logSteps step claim) := by
  unfold verifyKeccakLayerS
  refine NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_keccakPackRounds _ _ _) fun t ↦ ?_
  obtain ⟨v, s, pt⟩ := t
  refine NoCG.bind (cg_sumcheck _ _ _) fun u ↦ ?_
  obtain ⟨lp, v'⟩ := u
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_sample fun _ ↦ cg_ret _

theorem cg_keccakLayersS (sh : KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim),
      NoCG (keccakLayersS sh logSteps steps claim)
  | [], _ => cg_ret _
  | s :: steps, claim => by
    unfold keccakLayersS
    exact NoCG.bind (cg_verifyKeccakLayerS _ _ _ _) fun _ ↦ cg_keccakLayersS sh logSteps steps _

/-- The tape's GKR (T2) commits nothing. -/
theorem cg_tapeGkr (h : ℕ) (inst output : List E) : NoCG (tapeGkr h inst output) := by
  rw [tapeGkr_eq]
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ cg_keccakLayersS _ _ _ _

theorem cg_slotProg (b sb blk : ℕ) (W : ℕ → ℕ → E) (pt : List E) (v : E) :
    NoCG (Lvm.KG.slotProg b sb blk W pt v) := by
  unfold Lvm.KG.slotProg
  exact NoCG.bind (cg_sumcheck _ _ _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ NoCG.bind (cg_ringSwitch _ _) fun _ ↦ cg_ret _

theorem cg_wireChProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ)
    (claim : LeanVM.Protocol.Verifier.KeccakClaim) : NoCG (Lvm.KG.wireChProg w sb dsel s n claim) := by
  unfold Lvm.KG.wireChProg
  exact NoCG.bind (cg_sumcheck _ _ _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ NoCG.bind (cg_slotProg _ _ _ _ _ _) fun _ ↦ cg_ret _

/-- The tape caller (V_S phases 4–5 at S2) commits nothing. -/
theorem cg_tapeProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    NoCG (Lvm.KG.tapeProg w sb dsel s n) := by
  unfold Lvm.KG.tapeProg
  exact NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_tapeGkr _ _ _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
      NoCG.bind (cg_wireChProg _ _ _ _ _ _) fun _ ↦ cg_ret _

/-- **V_S phases 4–7 commit nothing and ask no proof of work** (lvm2 S2: the tape, then `KS`). -/
theorem cg_kgProgS (s : RecursionFast.Digest) (n : ℕ) : NoCG (Lvm.VEq.kgProgS s n) :=
  NoCG.bind (cg_tapeProg _ _ _ _ _)
    fun _ ↦ NoCG.bind (NoCG.bind (cg_callerProg _) fun _ ↦ NoCG.bind (cg_ksLinkProg _ _ _) fun _ ↦
      cg_ret _) fun _ ↦ cg_ret _

/-! ## `kgSpec`'s error side conditions at `εS` -/

theorem errE_le_129 {d : ℕ} (hd : d ≤ 2 ^ 63) : errE d ≤ (2 : ℝ≥0∞)⁻¹ ^ 129 := by
  unfold errE
  rw [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat]
  have h1 : (d : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 63 := by exact_mod_cast hd
  have h2 : (2 : ℝ≥0∞) ^ 63 * ((2 : ℝ≥0∞) ^ 192)⁻¹ = (2 : ℝ≥0∞)⁻¹ ^ 129 := by
    rw [show (192 : ℕ) = 63 + 129 from rfl, pow_add,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
      ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
      one_mul, ENNReal.inv_pow]
  calc (d : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ≤ (2 : ℝ≥0∞) ^ 63 * ((2 : ℝ≥0∞) ^ 192)⁻¹ := by gcongr
    _ = _ := h2

/-- Every group of at most `2^63` over `|E|` is within `εS` (`≤ 2^-129`). -/
theorem errE_le_εS {d : ℕ} (hd : d ≤ 2 ^ 63) : errE d ≤ εS := (errE_le_129 hd).trans pow129_le_εS

theorem errE_add (a b : ℕ) : errE a + errE b = errE (a + b) := by
  unfold errE; push_cast; rw [add_mul]

theorem errE_smul (n d : ℕ) : (n : ℝ≥0∞) * errE d = errE (n * d) := by
  unfold errE; push_cast; rw [mul_assoc]

/-- `Σ_{6} L₀·errE 1` (ring switching's six challenges with `L₀` candidate pairs). -/
theorem sum6L (L : ℕ) : (∑ _i ∈ Finset.range 6, (L : ℝ≥0∞) * errE 1) = errE (6 * (L * 1)) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, errE_smul, errE_smul]

/-- **`kgSpecS`'s side conditions at P20 with `37,696 = 124·304` candidate pairs** (lvm2 J2′: `C_main`'s and
`C_rec`'s roots at the Johnson threshold, `candPairs_ncard_le`; the tape at `w = 20`, `Pk + 4 = 13`: KS13, lvm2 roll 8, B1; roll 7: `10 + 4`), and its
lead `20·37,696·errE 1 ≤ εS`. -/
theorem kg_errsJ2 :
    ((37696 : ℕ) : ℝ≥0∞) * errE 104 ≤ εS ∧ ((37696 : ℕ) : ℝ≥0∞) * errE 2 + 0 ≤ εS ∧
    (∑ _i ∈ Finset.range 6, ((37696 : ℕ) : ℝ≥0∞) * errE 1) +
      (((9 + 4 : ℕ) : ℝ≥0∞) * (((37696 : ℕ) : ℝ≥0∞) * errE 1) + 0) ≤ εS ∧
    (∑ _i ∈ Finset.range 6, ((37696 : ℕ) : ℝ≥0∞) * errE 1) +
      (((9 + 4 + 5 : ℕ) : ℝ≥0∞) * (((37696 : ℕ) : ℝ≥0∞) * errE 1) + 0) ≤ εS ∧
    ((15 + 5 : ℕ) : ℝ≥0∞) * (((37696 : ℕ) : ℝ≥0∞) * errE 1) + 0 ≤ εS := by
  rw [sum6L]
  simp only [errE_smul, errE_add, add_zero]
  exact ⟨errE_le_εS (by norm_num), errE_le_εS (by norm_num), errE_le_εS (by norm_num),
    errE_le_εS (by norm_num), errE_le_εS (by norm_num)⟩

/-- **`kgSpecS`'s structural arguments at P20** (lvm2 CR-K; KS13, lvm2 roll 8, B1): `X` has `2^9` rows and the
layout's split (`ksSplit P20 = 7,680`) is the language's `2^13 − 2^9`; the continuation rows `contRows P20`, the
trace's and the WOTS leaf's from the split, are distinct and inside `[1, 2^13)` (roll 7, KS14: `2^10`, 15,360,
`2^14`). -/
theorem kg_struct : Lvm.ksXLog Lvm.P20 = 9 ∧ Lvm.ksSplit Lvm.P20 = Lvm.KG.ksSplitN (9 + 4) 9 ∧
    (Lvm.contRows Lvm.P20).Nodup ∧
    ∀ i ∈ Lvm.contRows Lvm.P20, 1 ≤ i ∧ i < 2 ^ (9 + 4) := by
  have hs : Lvm.spongeBlocks Lvm.P20 - 1 < Lvm.ksSplit Lvm.P20 + 400 ∧
      Lvm.ksSplit Lvm.P20 + 400 + 31 ≤ 2 ^ (9 + 4) := by
    rw [Lvm.ksSplit_P20, Lvm.sizes_P20.2.2.2.2.2.2.2.2]
    decide
  refine ⟨Lvm.ksXLog_P20, by decide, ?_, ?_⟩
  · unfold Lvm.contRows
    rw [List.nodup_append]
    refine ⟨(List.nodup_range).map fun a b h ↦ by (clear * - h; omega), (List.nodup_range).map fun a b h ↦ by (clear * - h; omega),
      fun a ha b hb hab ↦ ?_⟩
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    (clear * - hs a' ha' b' hb' hab; omega)
  · intro i hi
    unfold Lvm.contRows at hi
    simp only [List.mem_append, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> omega

/-! ## V_S phases 4–7 at S2: the tape, then `KS` -/

section KgS

open Lvm.KG
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **V_S phases 4–7 (lvm2 S2)**: the tape caller (T1–T4 at `w = 20`, `D` at slots 0–3 of the whole
`C_main`, T-V's `tapeSpec`), then `KS` (Keccak with all lanes tied, sponge link; WP-8's
`ksPhaseSpec`), from doom of the tape's chain part on `D` (`TapeOut`), `KS`'s relation and `R` to
doom of every claim they leave and `R`. T5's boundary claims are placed by `assembleS` directly. -/
noncomputable def kgSpecS (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (s : RecursionFast.Digest) (n : ℕ) (Pk xl y2 : ℕ) (hPk : 1 ≤ Pk) (hxl : xl ≤ Pk + 4) (rows : List ℕ)
    (hnd : rows.Nodup) (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ (Pk + 4))
    (col main ks : β → ℕ → K) (M X : β → ℕ → ℕ → K) (R : β → Prop)
    (h46 : (L₀ : ℝ≥0∞) * errE 104 ≤ εmax) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hrK : (∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((Pk + 4 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax)
    (hrKL : (∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((Pk + 4 + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax) (hT : T ≤ εmax) :
    Spec (tapeProg (15 + 5) 1 0 s n >>= fun tp ↦
        (callerProg (Pk + 4) >>= fun co ↦ ksLinkProg (Pk + 4) xl rows >>= fun lo ↦
          VerifierProgram.ret (co, lo)) >>= fun kso ↦ VerifierProgram.ret (tp, kso))
      (Doomed C (fun q ↦ TapeOut (15 + 5) s n (dOf (15 + 5) 0 (col q)) ∧
        KSRel (Pk + 4) xl y2 rows (main q) (ks q) (M q) (X q) ∧ R q))
      (fun out hist ↦ ((out.1.1.length = 15 + 5 ∧ out.1.2.1.length = 25) ∧
          (out.2.1.1.length = Pk + 4 ∧ out.2.1.2.1.length = 25 ∧ out.2.2.2.1.1.length = Pk + 4)) ∧
        Doomed C (fun q ↦
          (RingColTrue 17 (col q) out.1.2.2.2.d.ring ∧ TiedD (15 + 5) (dOf (15 + 5) 0 (col q)) out.1.1
            out.1.2.1) ∧
          (CallerClaims (Pk + 4) 25 (ks q) (ksY (Pk + 4) y2 (main q) (ks q)) out.2.1 ∧
            KsLinkClaims (Pk + 4) xl (ks q) (ksYRow (Pk + 4) y2 (main q) (ks q)) (M q) (X q)
              out.2.2) ∧ R q) hist)
      εmax (((15 + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  (tapeSpec (P := 14) (sb := 1) (dsel := 0) (h := 17) hst hcard (by norm_num) (by norm_num) s col
      (fun q ↦ KSRel (Pk + 4) xl y2 rows (main q) (ks q) (M q) (X q) ∧ R q) h46 hrK).bind' fun tp ↦
  if htp : tp.1.length = 15 + 5 ∧ tp.2.1.length = 25 then
    ((ksPhaseSpec hst hcard Pk xl y2 hPk hxl rows hnd hrows main ks M X
        (fun q ↦ (RingColTrue 17 (col q) tp.2.2.2.d.ring ∧
          TiedD (15 + 5) (dOf (15 + 5) 0 (col q)) tp.1 tp.2.1) ∧ R q) h46 h2 hT hrKL).mono
      (fun _ hd ↦ Doomed.mono hd.2.2.2.2 fun _ ⟨hk, ⟨hring, htied⟩, hR⟩ ↦ ⟨hring, htied, hk, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kso ↦
    (Spec.ret (tp, kso)).mono
      (fun _ hd ↦ ⟨⟨htp, hd.1⟩, Doomed.mono hd.2 fun _ ⟨ht, ⟨hc, hk⟩, hR⟩ ↦ ⟨hc, hk, ht, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ htp ⟨hd.1, hd.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end KgS

/-! ## `MidSpec` and an equivalent `Good` -/

end Lvm.ASM
end
-- ===== end of `LvmCertSMid2` =====

-- ===== merged from `LvmCertSMid3Tab` (GOLF module merge: `LvmCertSMid3Tab.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- WP-16b (CERT). New for lvm (O6 link, the tables): the table phase's claims have their table's
-- height coordinates (a return fact of `lbusTableCheckProg`), and its assembled block claims
-- (`tableClaimsE`) holding on the commitments give WP-9b's `BlockHolds`.

/-!
# The table claims

* **`retOK_lbusTableCheckProg`**: every return of V_S phases 2–3 meets `TabRet`;
* **`blockHolds_of_tableClaims`**: the assembled table claims hold on `(qm, qr)` ⇒ every
  returned claim is WP-9b's `BlockHolds` (under `LayOk`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## The returns of the table phase -/

/-- Global column `base_j + i` (`i` inside table `j`'s width) decodes to `(j, i)`. -/
theorem colLoc_base (tabs : List Lvm.M3.Tab) {j i : ℕ} (hj : j < tabs.length) (hi : i < tabs[j].w) :
    Lvm.M3.colLoc tabs ((globalColumnBases (Lvm.M3.vTables tabs)).getD j 0 + i) = some (j, i) := by
  have hτ : ∀ t ∈ tabs, t.τ ≤ (⟨(tabs.map (·.τ)).sum, 0⟩ : Lvm.M3.Lay).μ := fun t ht ↦ by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.τ)) ht)
    simp only [Lvm.M3.Lay.μ]; (clear * - hj this; omega)
  exact Lvm.M3.colLoc_colOfL ⟨(tabs.map (·.τ)).sum, 0⟩ tabs hτ ⟨⟨j, hj⟩, ⟨i, hi⟩⟩

/-- A running maximum bounds its start and every element. -/
theorem foldl_max_ge : ∀ (l : List ℕ) (a x : ℕ), (x ≤ a ∨ x ∈ l) → x ≤ l.foldl max a
  | [], a, x, h => by simpa using h
  | b :: l, a, x, h => foldl_max_ge l (max a b) x (by
      rcases h with h | h
      · exact Or.inl (le_max_of_le_left h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr h)

/-- Zipping keeps at most the first list's total. -/
theorem sum_zip_fst_le {α β : Type} (f : α → ℕ) :
    ∀ (l : List α) (m : List β), ((l.zip m).map fun r ↦ f r.1).sum ≤ (l.map f).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have := sum_zip_fst_le f l m
    (clear * - f a α β l m this; omega)

open LeanVM.Protocol.Compile in
/-- **`tableTermsClaims`'s returns**: the claims meet `P` when the accumulated ones do and every
row's do, and there are as many new claims as the rows' widths. -/
theorem retOK_tableTermsClaims (tables : List Verifier.Table) (cp fp point : List E)
    (P : ColumnClaim → Prop) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), (∀ c ∈ claims, P c) →
      (∀ r ∈ rows, ∀ col < r.1.width, ∀ v : E,
        P ⟨(globalColumnBases tables).getD r.1.opcode 0 + col, point.take r.2.1, v⟩) →
      RetOK (fun x : E × List ColumnClaim ↦ (∀ c ∈ x.2, P c) ∧
          x.2.length = claims.length + (rows.map fun r ↦ r.1.width).sum)
        (tableTermsClaims tables cp fp point rows cursor final claims)
  | [], _, _, claims, hc, _ => RetOK.ret ⟨hc, by simp⟩
  | r :: rows, cursor, final, claims, hc, hr => by
    unfold tableTermsClaims
    refine (RetOK.readN r.1.width).bind fun evs hevs ↦ ?_
    refine (retOK_tableTermsClaims tables cp fp point P rows _ _ _ ?_
      (fun r' hr' ↦ hr r' (List.mem_cons_of_mem _ hr'))).mono ?_
    · intro c hc'
      rcases List.mem_append.mp hc' with h | h
      · exact hc c h
      · obtain ⟨⟨v, col⟩, hvc, rfl⟩ := List.mem_map.mp h
        have hcol := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hvc)).1
        exact hr r List.mem_cons_self col (by simp only at hcol; (clear * - hevs hcol; omega)) v
    · rintro x ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h2]
      simp [hevs]
      (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)

open LeanVM.Protocol.Compile in
/-- **`tableSumcheckClaims`'s returns**: the claims meet `P` when every row's claim at a point of
`max heights` coordinates does; at most `Σ widths` claims. -/
theorem retOK_tableSumcheckClaims (tables : List Verifier.Table) (heights : List ℕ)
    (busForms : List (List Verifier.Form)) (cp fp eqp : List E) (target : E)
    (P : ColumnClaim → Prop)
    (hP : ∀ point : List E, point.length = heights.foldl max 0 →
      ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
        (Verifier.tableWeights heights eqp point))), ∀ col < r.1.width, ∀ v : E,
        P ⟨(globalColumnBases tables).getD r.1.opcode 0 + col, point.take r.2.1, v⟩) :
    RetOK (fun cl : List ColumnClaim ↦ (∀ c ∈ cl, P c) ∧ cl.length ≤ (tables.map (·.width)).sum)
      (tableSumcheckClaims tables heights busForms cp fp eqp target) := by
  unfold tableSumcheckClaims
  refine (LeanVM.Protocol.EndToEnd.Front.retOK_sumcheck 4 _ _).bind fun x hx ↦ ?_
  obtain ⟨ch, claim⟩ := x
  simp only [List.length_replicate] at hx
  refine (retOK_tableTermsClaims tables cp fp ch.reverse P _ 0 0 [] (by simp)
    (hP ch.reverse (by simpa using hx))).bind fun y hy ↦ ?_
  obtain ⟨final, cl⟩ := y
  refine RetOK.bind_true fun _ ↦ RetOK.ret ⟨hy.1, ?_⟩
  rw [hy.2, List.length_nil, zero_add]
  exact sum_zip_fst_le Verifier.Table.width _ _

/-- The verifier tables' widths are the tables'. -/
theorem sum_width_vTables (T : List Lvm.M3.Tab) :
    ((Lvm.M3.vTables T).map (·.width)).sum = (T.map (·.w)).sum := by
  suffices h : ∀ k, ((T.zipIdx k).map fun x ↦ x.1.w) = T.map (·.w) by
    simp [Lvm.M3.vTables, Lvm.M3.vTable, Verifier.Table.width, List.map_map, Function.comp_def, h]
  induction T with
  | nil => intro; rfl
  | cons t T ih => intro k; simp [List.zipIdx_cons, ih]

/-- Verifier table `k` is table `k`, numbered `k`. -/
theorem getElem_vTables (T : List Lvm.M3.Tab) (k : ℕ) (hk : k < (Lvm.M3.vTables T).length) :
    (Lvm.M3.vTables T)[k] = Lvm.M3.vTable k (T[k]'(by simpa using hk)) := by
  simp [Lvm.M3.vTables, List.getElem_zipIdx]

/-- **Every return of the table phase meets `TabRet`.** -/
theorem retOK_lbusTableCheckProg (T : List Lvm.M3.Tab) (μ : ℕ) :
    RetOK (TabRet T) (Lvm.M3.lbusTableCheckProg T μ) := by
  unfold Lvm.M3.lbusTableCheckProg Lvm.M3.lvmBusTableProg
  refine RetOK.bind (Q' := TabRet T) (RetOK.bind_true fun b ↦ ?_) fun cl hcl ↦
    RetOK.bind_true fun _ ↦ RetOK.ret hcl
  unfold tablePhaseClaims
  refine RetOK.bind_true fun xi ↦ ?_
  refine (retOK_tableSumcheckClaims _ _ _ _ _ _ _ (fun c ↦ ∀ j i,
    Lvm.M3.colLoc T c.column = some (j, i) → c.point.length = (T[j]?.map (·.τ)).getD 0) ?_).bind
    fun cl hcl ↦ RetOK.ret ?_
  · intro point hpt r hr col hcol v j i hloc
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    have hkT : k < T.length := by
      simp only [List.length_zip, Lvm.M3.length_vTables] at hk; (clear hcol hloc hpt hr; (clear * - k T b point hk; omega))
    simp only [List.getElem_zip, getElem_vTables T k (by simpa using hkT)] at hcol hloc ⊢
    simp only [Lvm.M3.vLayout, List.getElem_map, Lvm.M3.vTable, Verifier.Table.width,
      List.length_replicate] at hcol hloc hpt ⊢
    rw [colLoc_base T hkT hcol] at hloc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hloc)
    have := foldl_max_ge (T.map (·.τ)) 0 T[k].τ
      (Or.inr (List.mem_map_of_mem (List.getElem_mem hkT)))
    simp [List.getElem?_eq_getElem hkT]
    (clear * - hpt hk hkT this; omega)
  · simp only [Lvm.M3.busResV, Lvm.M3.busFinalV, List.nil_append]
    exact ⟨hcl.1, (sum_width_vTables T) ▸ hcl.2⟩

/-! ## The table claims on the commitments -/

end Lvm.ASM
end
-- ===== end of `LvmCertSMid3Tab` =====

-- ===== merged from `LvmCertSMid3Kec` (GOLF module merge: `LvmCertSMid3Kec.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- WP-16b (CERT). New for lvm (O6 link, the Keccak tables): `KS`'s assembled claims
-- (`keccakClaimsE`, `ksOutputClaimsE`) holding on `C_main` give WP-8's `CallerClaims` with WP-14c's
-- accessors. lvm2 S2 (WP S2-CERT): the tape's claims (`tapeClaimsE`) give the ring claim and the
-- tied digest lanes (`tapeClaims_of`), its boundary claims give `BndS` (`bndS_of_tape`).

/-!
# The Keccak tables' claims

* **`tapeClaims_of`** (lvm2 S2): the tape's ring claim on `C_main` and `D̃_l(r) = a_l`;
* **`bndS_of_tape`** (lvm2 S2): `D_{n−1} = h` from T5's claims and the header (`pubX`);
* **`callerClaims_ks`**: `KS`'s ring claim, column claims and tied output lanes.

The helpers (namespace `Kec`): a point claim at `(a, sel(b))` on a block is slot `b`'s extension at
`a` (`holds_split`, after WP-8's `col_split`); the stream's header lanes are the statement's digest
lanes (`lane_hdr`); `pad43`'s lanes are `pad43Lane`'s (`pad43_getD`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM dD ksCol ksY2 msgM msgX)

namespace Kec

/-! ## Block claims on a slot -/

/-- `selE` is the cube point `bitsE`. -/
theorem selE_eq_bitsE (z m : ℕ) : selE z m = bitsE z m := by
  show LeanVM.Protocol.Verifier.selectorPoint z m = bitsE z m
  rw [LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint]
  induction m generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [LeanVM.Protocol.EndToEnd.Front.boolPoint_succ, bitsE, ih, Nat.testBit_zero]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one z with h0 | h1 <;> simp [*]

/-- A point claim on a block at `(a, sel(b))` is slot `b`'s extension at `a`. -/
theorem holds_split {μ h k off : ℕ} (hal : 2 ^ (h + k) ∣ off) (hfit : off + 2 ^ (h + k) ≤ 2 ^ μ)
    {a : List E} (ha : a.length = h) {b : ℕ} (hb : b < 2 ^ k) {val : E} {q : Column μ}
    (H : StackClaim.Holds μ (BClaim.point ⟨h + k, off⟩ (a ++ selE b k) val).onStack q) :
    ∑ x ∈ range (2 ^ h), eqAt a x * ofK (q.values.getD (off + (x + 2 ^ h * b)) 0) = val := by
  rw [selE_eq_bitsE] at H
  rw [holds_point hal hfit _ (by simp [ha])] at H
  have e := col_split (s := bitsE b k) ha (fun n ↦ ofK (q.values.getD (off + n) 0))
  rw [bitsE_length] at e
  rw [e, sum_eqAt_bitsE hb] at H
  exact H

/-- The ring claim on a block. -/
theorem ringCol_of_holds {μ h off : ℕ} (hal : 2 ^ (h + 6) ∣ off) (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ)
    {q : Column μ} {ring : E × (List E → E)}
    (H : StackClaim.Holds μ (⟨⟨h + 6, off⟩, ring.2, ring.1⟩ : BClaim).onStack q) :
    Lvm.KG.RingColTrue h (fun n ↦ q.values.getD (off + n) 0) ring :=
  ((holds_onStack _ hal hfit q).1 H).symm

/-! ## The header's lanes -/

/-- `laneAt` reads its eight bytes. -/
theorem laneAt_shift {b b' : ByteArray} {o o' : ℕ}
    (h : ∀ k < 8, b.get! (o + k) = b'.get! (o' + k)) : laneAt b o = laneAt b' o' := by
  apply UInt64.toNat_inj.mp
  rw [toNat_laneAt, toNat_laneAt]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h i i.isLt]

/-- A digest's lane `m < 4` is the lane of its bytes. -/
theorem blockLane_digestAt (π : ByteArray) (o : ℕ) {m : ℕ} (hm : m < 4) :
    RecursionFast.Keccak.blockLane (digestAt π o).toArray m = laneAt π (o + 8 * m) := by
  have hd : ∀ k < 8, (digestAt π o).toArray.getD (8 * m + k) 0 = π.get! (o + 8 * m + k) := by
    intro k hk
    simp [digestAt, Array.getD, show 8 * m + k < 32 by (clear * - m k hm hk; omega), Nat.add_assoc]
  have h0 := hd 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  rw [Nat.add_zero, Nat.add_zero] at h0
  rw [RecursionFast.Keccak.blockLane_unfold, h0, hd 1 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), hd 2 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), hd 3 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)),
    hd 4 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), hd 5 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), hd 6 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), hd 7 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))]
  simp only [laneAt, UInt64.zero_or, Nat.add_zero]
  rfl

/-- The stream's header byte `j ≥ 8` is the statement's. -/
theorem sig_get (x : List UInt8) {j : ℕ} (hj : 8 ≤ j) (k : ℕ) :
    (sigOfX x).get! (headerAt j + k) =
      (⟨(List.replicate 8 0 ++ x).toArray⟩ : ByteArray).get! (j + k) := by
  have h8 : headerAt 8 = 88 := rfl
  have hj' : headerAt j = 88 + (j - 8) := rfl
  rw [sigOfX, get!_mk, get!_mk, List.getD_append_right, List.getD_append_right]
  · simp only [List.length_replicate]
    congr 1
    (clear * - j k hj h8 hj'; omega)
  · simp only [List.length_replicate]; (clear * - hj; omega)
  · simp only [List.length_replicate]; (clear * - h8 hj'; omega)

/-- A lane of a header digest, from the stream. -/
theorem lane_hdr (x : List UInt8) {j : ℕ} (hj : 8 ≤ j) {m : ℕ} (hm : m < 4) :
    laneAt (sigOfX x) (headerAt j + 8 * m) =
      RecursionFast.Keccak.blockLane (digestAt ⟨(List.replicate 8 0 ++ x).toArray⟩ j).toArray m := by
  rw [blockLane_digestAt _ _ hm]
  refine laneAt_shift fun k _ ↦ ?_
  rw [Nat.add_assoc, sig_get x hj, Nat.add_assoc]

/-- An entry of a list, with its index, is in its `zipIdx`. -/
theorem getD_mem_zipIdx (L : List FK) {l : ℕ} (hl : l < L.length) : (L.getD l 0, l) ∈ L.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

end Kec

open Kec

/-- `pubX`'s chain length is the header's (`V_S` reads the header's lane of `n` from the stream). -/
theorem pubX_n (x : List UInt8) : (pubX x).n = (hdrOf x).n :=
  congrArg UInt64.toNat (laneAt_shift fun k _ ↦ sig_get x (by norm_num) k)

end Lvm.ASM
end
-- ===== end of `LvmCertSMid3Kec` =====

-- ===== merged from `LvmCertSMid3Link` (GOLF module merge: `LvmCertSMid3Link.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- WP-16b (CERT). New for lvm (O6 link, the `KS` link): the `KS` link's assembled claims
-- (`ksLinkClaimsE`) holding on the commitments give WP-8's `KsLinkClaims` with WP-14c's accessors.
-- lvm2 S2 (WP S2-CERT): `KS` at `C_main` word `4·2^20` (FRZ-0); v1's `CH` link is gone.

/-!
# The links' claims

* **`ksLinkClaims_of`**: the four combined claims `yC`, `inC`, `mC` (on `C_rec`), `xC`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## Helpers -/

/-! ## The links -/

end Lvm.ASM
end
-- ===== end of `LvmCertSMid3Link` =====

-- ===== merged from `LvmCertSMid3Side` (GOLF module merge: `LvmCertSMid3Side.lean` is now a stub importing `LvmCertSMid3`) =====
section
-- WP-16b (CERT). New for lvm (O6, the side conditions): every return of V_S phases 4–7 meets
-- `KgRet` (after WP-8's `retOK_verifyKeccak`), and `assembleS`'s claims are multiaffine and at
-- most `2^55` on `C_rec` and `2^40` on `C_main` (the openings' side conditions, `OpenPost`).

/-!
# The side conditions

* **`retOK_kgProgS`**: every return of `kgProgS s n` meets `KgRet` (lvm2 S2: `retOK_tapeProg`, then
  `retOK_callerProg`, `retOK_ksLinkProg`; ring weights `Σ_k c_k eq(r^(2^k), ·)` are multiaffine);
* `okC_claimsS`: every assembled claim's block fits its commitment (`τ ≤ 19` on `C_rec`, `≤ 23` on
  `C_main` (lvm2 roll 8, B1: ν = 23), from `LayOk` for the tables) with a weight multiaffine on the block;
* **`side_assembleS`**: `assembleS`'s claims are multiaffine, at most `2^55` on `C_rec` (lvm2 J2′), when
  `pub.h` has at most `2^61` lanes (`length_pubX_h`: `pubX`'s has four; `C_main` gets one boundary
  claim per lane of `pub.h`, `length_h_lt_main`, so the bound is needed).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## The returns of `kgProgS` -/

/-- Two return invariants of one program. -/
theorem retOK_and {α : Type} {P Q : α → Prop} {p : LeanVM.Protocol.Compile.VerifierProgram α}
    (hP : RetOK P p) (hQ : RetOK Q p) : RetOK (fun a ↦ P a ∧ Q a) p :=
  fun l a hl ↦ ⟨hP l a hl, hQ l a hl⟩

/-- A ring switch's weight is multiaffine on any number of coordinates. -/
theorem isMultiaffine_ringWeight (r cs : List E) (n : ℕ) :
    IsMultiaffine n fun y ↦ LeanVM.Protocol.Verifier.ringWeight r y cs := by
  simp only [ringWeight_eq_sum]
  exact IsMultiaffine.sum _ _ fun k _ ↦ (isMultiaffine_eqEvalN _ n).const_mul _

/-- Every weight `ringSwitch` returns is multiaffine. -/
theorem retOK_ringSwitch (point s : List E) :
    RetOK (fun r : E × (List E → E) ↦ ∀ n, IsMultiaffine n r.2)
      (LeanVM.Protocol.Verifier.ringSwitch point s) := by
  unfold LeanVM.Protocol.Verifier.ringSwitch
  exact RetOK.bind_true fun _ ↦ RetOK.ret fun n ↦ isMultiaffine_ringWeight _ _ n

/-- The facts of a return of `callerProg h`. -/
def CallerRet (h : ℕ) (co : CallerOut) : Prop :=
  co.1.length = h ∧ co.2.1.length = 25 ∧
    (∀ c ∈ co.2.2.1.1, c.column = qkeccak ∧ c.point.length = h + 6) ∧ co.2.2.1.1.length ≤ 1 ∧
    ∀ n, IsMultiaffine n co.2.2.2.2

/-- **Every return of `callerProg h`** (`4 ≤ h`) meets `CallerRet h`. -/
theorem retOK_callerProg (h : ℕ) (hh : 4 ≤ h) : RetOK (CallerRet h) (Lvm.KG.callerProg h) := by
  unfold Lvm.KG.callerProg
  refine (retOK_sampleN h).bind fun r hr ↦ (RetOK.readN 25).bind fun v hv ↦
    (retOK_and (retOK_verifyKeccak h r v (hr ▸ hh)) (retOK_verifyKeccak_count h r v)).bind
      fun res hres ↦ (retOK_ringSwitch _ _).bind fun ring hring ↦ RetOK.ret ?_
  exact ⟨hr, hv, fun c hc ↦ hr ▸ hres.1 c hc, hres.2, hring⟩

/-- Every return of the `KS` link: `hk + 5` challenges, `ρ'` has `hk` coordinates. -/
theorem retOK_ksLinkProg (hk xl : ℕ) (rows : List ℕ) :
    RetOK (fun lo : List E × (List E × E) × List E ↦ lo.1.length = hk + 5 ∧ lo.2.1.1.length = hk)
      (Lvm.KG.ksLinkProg hk xl rows) := by
  unfold Lvm.KG.ksLinkProg
  exact (retOK_sampleN _).bind fun kchal hk' ↦ (retOK_sumcheck _ _ _).bind fun kshift hs ↦
    RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨hk', by simpa using hs⟩

/-- Every return of a slot reduction: its ring weight is multiaffine. -/
theorem retOK_slotProg (b sb blk : ℕ) (W : ℕ → ℕ → E) (pt : List E) (v : E) :
    RetOK (fun o : Lvm.KG.SlotOut ↦ ∀ n, IsMultiaffine n o.ring.2) (Lvm.KG.slotProg b sb blk W pt v) := by
  unfold Lvm.KG.slotProg
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_ringSwitch _ _).bind fun _ hr ↦ RetOK.ret hr

/-- Every return of the chain wiring phase: its ring weight is multiaffine. -/
theorem retOK_wireChProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim) :
    RetOK (fun o : Lvm.KG.WireChOut ↦ ∀ n, IsMultiaffine n o.d.ring.2)
      (Lvm.KG.wireChProg w sb dsel s n claim) := by
  unfold Lvm.KG.wireChProg
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_slotProg _ _ _ _ _ _).bind fun _ hd ↦ RetOK.ret hd

/-- **Every return of the tape caller** (lvm2 S2): `w` challenges `r`, 25 scalars, a multiaffine ring
weight. -/
theorem retOK_tapeProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    RetOK (fun tp : Lvm.KG.TapeOutE ↦ tp.1.length = w ∧ tp.2.1.length = 25 ∧
      ∀ n, IsMultiaffine n tp.2.2.2.d.ring.2) (Lvm.KG.tapeProg w sb dsel s n) := by
  unfold Lvm.KG.tapeProg
  exact (retOK_sampleN w).bind fun _ hr ↦ (RetOK.readN 25).bind fun _ hv ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ (retOK_wireChProg _ _ _ _ _ _).bind fun _ hw ↦ RetOK.ret ⟨hr, hv, hw⟩

/-- **Every return of V_S phases 4–7 meets `KgRet`** (lvm2 S2: the tape, then `KS`). -/
theorem retOK_kgProgS (s : RecursionFast.Digest) (n : ℕ) : RetOK KgRet (kgProgS s n) := by
  unfold kgProgS
  refine (retOK_tapeProg 20 1 0 s n).bind fun tp htp ↦
    ((retOK_callerProg _ (by norm_num)).bind fun co hco ↦ (retOK_ksLinkProg _ _ _).bind
      fun lo hlo ↦ RetOK.ret (Q := fun ks : CallerOut × (List E × (List E × E) × List E) ↦
        CallerRet 13 ks.1 ∧ ks.2.1.length = 18 ∧ ks.2.2.1.1.length = 13) ⟨hco, hlo⟩).bind
      fun ks hks ↦ RetOK.ret ?_
  obtain ⟨⟨k1, k2, k3, k4, k5⟩, k6, k7⟩ := hks
  exact ⟨htp, ⟨k1, k2, k3, k4, k5, k6, k7⟩⟩

/-! ## The side conditions of `assembleS` -/

/-- The log-size of a commitment. -/
def nuOf : Com → ℕ
  | .crec => 19
  | .main => 23

/-- An assembled claim's block fits its commitment and its weight is multiaffine on the block. -/
def OkC (e : Com × BClaim) : Prop :=
  e.2.block.variableCount ≤ nuOf e.1 ∧ IsMultiaffine e.2.block.variableCount e.2.weight

/-- A point claim on a block that fits. -/
theorem okC_point (com : Com) (blk : VPlacement) (z : List E) (v : E)
    (h : blk.variableCount ≤ nuOf com) : OkC (com, BClaim.point blk z v) :=
  ⟨h, isMultiaffine_eqEvalN z _⟩

/-- **The table claims** sit on aligned blocks inside their commitment (`LayOk`). -/
theorem okC_tableClaimsE (T : List Lvm.M3.Tab) (cl : List ColumnClaim)
    (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T) : ∀ e ∈ tableClaimsE T cl, OkC e := by
  intro e he
  simp only [tableClaimsE, List.mem_filterMap, Option.bind_eq_some_iff] at he
  obtain ⟨c, -, ji, -, h⟩ := he
  split at h
  · rename_i rec off hcol
    obtain ⟨t, ht, htc⟩ := Option.bind_eq_some_iff.mp hcol
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp htc
    have hal := hlay t (List.mem_of_getElem? ht) ji.2 hi
    simp only [Lvm.M3.Aligned, htc] at hal
    obtain ⟨-, hfit, -⟩ := hal
    cases h
    refine okC_point _ _ _ _ ?_
    simp only [ht, Option.map_some, Option.getD_some]
    cases rec
    · have hp : 2 ^ t.τ ≤ 2 ^ 23 := by
        have h' : off + 2 ^ t.τ ≤ 2 ^ 23 := hfit
        (clear * - h'; omega)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp
    · have hp : 2 ^ t.τ ≤ 2 ^ 19 := by
        have h' : off + 2 ^ t.τ ≤ 2 ^ 19 := hfit
        (clear * - h'; omega)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp
  · cases h

/-- `pubX`'s chain end has four lanes. -/
theorem length_pubX_h (x : List UInt8) : (pubX x).h.length = 4 := by
  simp [pubX, Lvm.pubOf]

end Lvm.ASM
end
-- ===== end of `LvmCertSMid3Side` =====

/-!
# O6 for `midS`

* `midSpecOfR`: WP-14's `midSpecOf` with return facts `Qa`, `Qk` of the two phases (the link and
  the side conditions need the claims' lengths, which no doom carries);
* **`midSpecOfRel`** (lvm2 J2′, J2C-DES T2): `midSpecOfR` relativised, into `MidSpecR`; the phases carry
  `¬ Good`, so the bus phase starts from `RootShape` alone and every non-good candidate pair fails a claim
  (`openPostR_of`); `LkSJ`, `bus_errsJ2` (and `kg_errsJ2`, `LvmCertSMid2`): the bounds at `L₀ = 37,696 = 124·304`
  (`candPairs` at the Johnson `thrRec`), `MidHyp.cons ≤ 2^48`; `specKgS` generic in the carried `R`;
* **`GoodS T hτ`**: the good pair, WP-14c's `GoodN` with the boundary claims only when the chain
  fits `CH` (`BndS`: V_S's boundary claims read row `(n − 1) mod 2^20`); **`nodeSound_goodS`**:
  `NodeSound` for `GoodS` from `NodeSound` for `GoodN` (`okS` gives `n ≤ 2^20`);
* **`MidHyp tabs`**: what the real tables must meet (`fitsR` for every public input; `KeysOk`,
  positive widths, `FixOk`, the constraint count at every statement's public values); A23: the middle
  phases' `MidSpec`/`MidShape` are AC-S's (`LvmAccSpecCert.midSpec_midSA`, `midShape_midSA`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal

/-! ## The glue with return facts -/

section Glue

variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : List UInt8 → VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb Gk : List UInt8 → Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : κ → Pair → Prop} {Qa : List UInt8 → α → Prop} {Qk : κ → Prop} {Lb Lk : ℝ≥0∞}

/-- **`OpenPostR` from the doom at the end of the middle phases** (`openPost_of` relativised): the non-good
pairs' doom of the assembled relations, the side conditions (`C_rec`'s claims at most `2^55`) and the
roots' shape. -/
theorem openPostR_of {Good : GoodRel} {x : List UInt8} {a : α} {k : κ} {h : List Ev}
    (hasm : ∀ p : Pair, (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 55 ∧
      (asm x a k).2.length ≤ 2 ^ 40)
    (hD : Doomed candPairs (fun p ↦ Kc k p ∧ (B x a p ∧ ¬ Good x p.1 p.2)) h) (hR : RootShape h) :
    OpenPostR Good x (asm x a k) h := by
  refine ⟨fun p hp hng ↦ ?_, hR, hside⟩
  by_contra hno
  push Not at hno
  have hkb := hasm p hno.1 hno.2
  exact hD p hp ⟨hkb.1, hkb.2, hng⟩

open Classical in
/-- **`MidSpecR` from the phases** (lvm2 J2′, J2C-DES T2): `midSpecOfR` relativised. The phases' specs are
taken at `Gk' x p := Gk x p ∧ ¬ (Gb x p ∧ Gk x p)` and `B' x a p := B x a p ∧ ¬ (Gb x p ∧ Gk x p)`, so the
bus phase's precondition is the roots' shape alone (its doom over `Gb ∧ Gk'` is a tautology) and every
**non-good** candidate pair fails a claim at the end; `C_rec`'s claims at most `2^55`. -/
theorem midSpecOfRel
    (SB : ∀ x, Spec (busP x)
      (fun h ↦ RootShape h ∧
        Doomed candPairs (fun p ↦ Gb x p ∧ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p))) h)
      (fun a h ↦ Doomed candPairs
        (fun p ↦ (B x a p ∧ ¬ (Gb x p ∧ Gk x p)) ∧ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p))) h ∧ RootShape h)
      εS Lb Lk)
    (hQa : ∀ x, RetOK (Qa x) (busP x))
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ εS → Spec (kgP x)
      (Doomed candPairs (fun p ↦ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p)) ∧ (B x a p ∧ ¬ (Gb x p ∧ Gk x p))))
      (fun k h ↦ Doomed candPairs (fun p ↦ Kc k p ∧ (B x a p ∧ ¬ (Gb x p ∧ Gk x p))) h) εS Lk T)
    (hQk : ∀ x, RetOK Qk (kgP x)) (hkc : ∀ x, NoCG (kgP x))
    (hasm : ∀ x a k (p : Pair), Qa x a → Qk k →
      (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : ∀ x a k, Qa x a → Qk k → (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 55 ∧
      (asm x a k).2.length ≤ 2 ^ 40) :
    MidSpecR (fun x ↦ busP x >>= fun a ↦ kgP x >>= fun k ↦ VerifierProgram.ret (asm x a k))
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) εS Lb := fun x T hT ↦
  ⟨((Lvm.KG.specWithRet (SB x) (hQa x)).bind' fun a ↦
      if ha : Qa x a then
        ((Lvm.KG.specWithRet ((SK x a T hT).frame RootShape fun _ _ hl hr ↦
            rootShape_append' ((hkc x).1.reach_commits hl) hr) (hQk x)).mono
          (fun h hp ↦ ⟨Doomed.mono hp.2.1 fun p hq ↦ ⟨hq.2, hq.1⟩, hp.2.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun k ↦
        if hk : Qk k then
          (Spec.ret (Post := OpenPostR (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) x) (εmax := εS)
              (T := T) (asm x a k)).mono
            (fun h hp ↦ openPostR_of (hasm x a k · ha hk) (hside x a k ha hk) hp.2.1 hp.2.2)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hk hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ ha hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun h hp ↦ ⟨hp, fun _ _ hq ↦ hq.2.2 ⟨hq.1, hq.2.1⟩⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end Glue

/-! ## The good pair -/

/-- The Keccak tables' relations on a pair (`GoodK` without the boundary claims; lvm2 S2: the
tape's chain part on `D`, then `KS`'s: KS13, lvm2 roll 8, B1; roll 7: `KSRel 14 10`). -/
def GkS (x : List UInt8) (p : Pair) : Prop :=
  Lvm.NS.TapeG x p.1 ∧
  KSRel 13 9 ksY2 (Lvm.contRows Lvm.P20) (colM p.1) (ksCol p.1) (msgM p.2) (msgX p.1)

/-! ## Errors -/

theorem coe_div_card (d : ℕ) :
    (((d : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = errE d := by
  rw [Nat.card_eq_fintype_card, ENNReal.coe_div (by simp), ENNReal.coe_natCast,
    ENNReal.coe_natCast, errE, div_eq_mul_inv]

theorem coe_overE (d : ℕ) : ((LeanVM.Protocol.overE d : ℝ≥0) : ℝ≥0∞) = errE d := by
  rw [LeanVM.Protocol.overE, ← Nat.card_eq_fintype_card, coe_div_card]

theorem εS_lt_one : εS < 1 :=
  lt_of_le_of_lt εS_le_128 (pow_lt_one₀ (by simp) (ENNReal.inv_lt_one.mpr (by norm_num)) (by norm_num))

/-- The Keccak phases' lead at P20 with `37,696 = 124·304` candidate pairs (lvm2 S2: the tape's `w = 20`
zero-test samples; J2′: `candPairs_ncard_le`). -/
noncomputable abbrev LkSJ : ℝ≥0∞ := ((15 + 5 : ℕ) : ℝ≥0∞) * (((37696 : ℕ) : ℝ≥0∞) * errE 1) + 0

/-- `εS` is exactly `errE (7·2^61)` (`7·2^-131 = 7·2^61/2^192`). -/
theorem errE_seven_eq_εS : errE (7 * 2 ^ 61) = εS := by
  unfold errE
  rw [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_ofNat, show (192 : ℕ) = 61 + 131 from rfl, pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ 61),
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul,
    ENNReal.inv_pow]

/-- A group of at most `7·2^61` over `|E|` is within `εS` (the exact form of `errE_le_εS`, which stops at `2^63`). -/
theorem errE_le_εS7 {d : ℕ} (hd : d ≤ 7 * 2 ^ 61) : errE d ≤ εS :=
  (errE_mono hd).trans_eq errE_seven_eq_εS

/-! ## The middle phases' specification -/

/-- The sumcheck tables of a statement. -/
def TS (tabs : Lvm.Pub → List Tab) (x : List UInt8) : List Tab := sumcheckTabs (tabs (pubX x))

/-- **What the real tables must meet** for O6: `fitsR` (INT-2's record check) for every public
input, and at every statement's public values WP-9b's table checks (`tabsOkB`, `fixOk_lvmTabs`) and
the constraint count (lvm2 J2′: at most `2^48`, the bus batching at `L₀ = 37,696`; the real count is ≈ 1,300). -/
structure MidHyp (tabs : Lvm.Pub → List Tab) : Prop where
  fit : ∀ pub, fitsR Lvm.P20 (tabs pub) = true
  keys : ∀ x, KeysOk (TS tabs x)
  width : ∀ x, ∀ t ∈ TS tabs x, 0 < t.w
  fix : ∀ x, FixOk (TS tabs x)
  cons : ∀ x, ((TS tabs x).map fun t ↦ t.cons.length).sum ≤ 2 ^ 48

variable {tabs : Lvm.Pub → List Tab}

theorem MidHyp.hτ (H : MidHyp tabs) : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ :=
  fun x ↦ (fit_of Lvm.P20 _ (H.fit (pubX x))).hτ

theorem B_inst_le (L : Lay) (T : List Tab) (hτ : ∀ t ∈ T, t.τ ≤ L.μ) :
    (inst L T hτ).B ≤ (T.map fun t ↦ t.cons.length).sum := by
  classical
  unfold LeanVM.Protocol.M3Instance.B
  rw [← Finset.sum_subtype (Finset.univ.filter (inst L T hτ).SumcheckTable) (fun x ↦ by simp)
    (fun j ↦ ((inst L T hτ).constraints j).length)]
  refine le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (le_of_eq ?_)
  change ∑ j : Fin T.length, ((T.get j).cons.map (CPoly.toMv _)).length = _
  simp only [List.length_map]
  exact Fin.sum_univ_fun_getElem T fun t ↦ t.cons.length

-- AC-N (A23): `midSpec_midS`/`midShape_midS'` (and `midS_eq`) were for the A21 middle phases
-- (`lbusTableCheckProg`, the per-column fixed check); `midS` now runs phase 3b and its O6 is AC-S's
-- `midSpec_midSA`/`midShape_midSA` (`LvmAccSpecCert`, `midS = midSA` by `rfl`).

end Lvm.ASM
