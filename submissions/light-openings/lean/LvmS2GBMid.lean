-- New for lvm2 MP-B cap pruning (CAP-L2, 2026-11-17): S2GB's middle phases' obligations (the KCert side over V's
-- `midGB`, the mini-bus at depth 13). The CAP-FRZ L statements are proved (CAP-L32).
import LvmS2GBFill
import LvmS2GBGuardC
import LvmS2GSXS

/-!
# S2GB's middle phases

* **`GoodSMB`**: `GoodSM`'s over S2GB's good pair `GoodTSB` (C2; over `THypSB`).
* **`midShapeB20`**, **`midSpecPinB20`**: `midShapeS20`'s and `midSpecPinS20`'s over `midGB` (V: `typedProgLB 13`, the
  tape over `contIvSB aSP`), at `THypSB`.
* Proof help: S2GL's typed-phase lemmas (`noCG_typedProgL`, `retOK_typedProgL`, `miniSpecL`, `typedSpecInL`,
  `typedSpecGL`) over `typedProgLB d` (`μBus = d ≠ 0`), and S2GS's (`specBusGS`, `midSpecP_GS`, `retOK_midGS_len`,
  `cg_midGS`) over `midGB`.
-/

set_option autoImplicit false

namespace Lvm.E2S

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.E2U Lvm.E2L Lvm.Typed LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26 LBus lvmBusProg mbClaimsL mbLinB stackOf)
open Lvm.VEq (BClaim VStackClaim hdX pubX pubXT)
open Lvm.ASM (OpenClaims GoodRel εS Pair BndS)
open LeanVM.Protocol.KeccakGkr (errE)
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.Typed (BT)
open scoped ENNReal

/-- The typed phases at depth `d` commit nothing and ask no proof of work (`noCG_typedProgL`'s proof). -/
theorem noCG_typedProgLB (d : ℕ) (Ti : TInst) (pub : Lvm.Pub) : Lvm.M3.NoCG (typedProgLB d Ti pub) := by
  unfold typedProgLB
  exact Lvm.M3.NoCG.bind cg_zeroProgT fun _ ↦ Lvm.M3.NoCG.bind (cg_wireProgT _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_relayProgT _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_accProgT _ _ _ _ _ _ _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_miniBusLProg _ _) fun _ ↦ Lvm.M3.cg_ret _

/-- **The typed phases' return facts at depth `d`** (`retOK_typedProgL`'s proof over `typedProgLB d`). -/
theorem retOK_typedProgLB (d : ℕ) (Ti : TInst) (hlay : LayOk lay26 Ti.mbT) (pub : Lvm.Pub) :
    RetOK (fun a : OpenClaims ↦ (∀ c ∈ a.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ a.2, IsMultiaffine CMain.nu20 c.1) ∧
      a.1.length + a.2.length ≤ 2 ^ 39) (typedProgLB d Ti pub) := by
  unfold typedProgLB
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ (retOK_relayProgT_len _ _ _).bind fun r hr ↦
    RetOK.bind_true fun _ ↦ ?_
  refine (retOK_miniBusLProg Ti.mbT d).bind fun cl hcl ↦ ?_
  obtain ⟨b, rfl⟩ := hcl
  refine RetOK.ret ?_
  have hm : ∀ c ∈ mbClaimsL CMain.nu20 Ti.mbT b, IsMultiaffine CMain.nu20 c.onStack.1 := fun c hc ↦ by
    obtain ⟨sd, -, rfl⟩ := List.mem_map.mp hc
    exact isMultiaffine_mbClaimL Ti.mbT hlay _ sd
  have hl : (mbClaimsL CMain.nu20 Ti.mbT b).length = 3 := Lvm.M3.length_mbClaimsL _ _ _
  have hfit : (pointE2 ⟨relayRounds, 0⟩ r.1 r.2).Fits 19 := by
    intro p hp
    simp only [pointE2, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨hr, le_rfl, dvd_zero _, by norm_num⟩
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_⟩
  · simp only [typedClaimsL, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact isMultiaffine_splitE2 _ _ hfit b hb
    · exact isMultiaffine_regClaimT Ti 19 _ _ _ _ c hc
  · simp only [typedClaimsL, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact isMultiaffine_regClaimT Ti _ _ _ _ _ c hc
    · exact isMultiaffine_regClaimT Ti _ _ _ _ _ c hc
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact hm b hb
  · simp only [typedClaimsL, List.length_append, List.length_map, length_regClaimT, hl]
    have h2 : (splitE2 relayRounds (pointE2 ⟨relayRounds, 0⟩ r.1 r.2)).length = 2 := rfl
    rw [h2]
    norm_num

section PhasesB

variable (Ti : TInst) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ)
  (R : Column lay26.nuMain × Column lay26.nuRec → Prop)

/-- **The mini-bus at depth `d` on a fixed candidate set** (`miniSpecL`'s proof, `μBus = d ≠ 0`). -/
noncomputable def miniSpecLB {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column lay26.nuMain × Column lay26.nuRec))
    (hS : S.ncard ≤ L₀) (hfin : S.Finite) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hfix : FixOk Ti.mbT) (hlin : mbLinB Ti.mbT = true) (d : ℕ) (hd : d ≠ 0)
    (hμ : (inst lay26 Ti.mbT hτL).μBus = d)
    {T : ℝ≥0∞} (hab : abError (inst lay26 Ti.mbT hτL) L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) (hTf : T ≤ εmax)
    (w : List E2 × List E2 × List E2) (r : List E2 × E2) :
    Spec (miniBusLProg Ti.mbT d)
      (fun h ↦ (∃ W, firstWord h = some W) ∧ Doomed (fun _ ↦ S) (fun q ↦
        M3Holds (inst lay26 Ti.mbT hτL) () (stackOf lay26 q.1 q.2) ∧ aRmT Ti lay26 pub R w r q) h)
      (fun cl h ↦ Doomed (fun _ ↦ S) (fun q ↦
        (∀ c ∈ cl, StackClaim.Holds lay26.nuMain c.onStack q.1) ∧ aRmT Ti lay26 pub R w r q) h)
      εmax (abError (inst lay26 Ti.mbT hτL) L₀ + 0) T :=
  Spec.congr (by rw [miniBusLProg, hμ])
    (((Lvm.M3.lvmBusSpec4 (inst lay26 Ti.mbT hτL) (Lvm.M3.condOf lay26 Ti.mbT hτL hsc)
        (fun _ ↦ Lvm.M3.candSet lay26 Ti.mbT hτL (fun _ ↦ S) (fun p ↦ stackOf lay26 p.1 p.2)
          (aRmT Ti lay26 pub R w r) []) () (Lvm.M3.vals0 lay26 Ti.mbT hτL)
        (fun _ ↦ Lvm.M3.candSet_finite lay26 Ti.mbT hτL _ _ _ hfin)
        (fun _ ↦ (Lvm.M3.candSet_ncard lay26 Ti.mbT hτL _ _ _ hfin).trans hS)
        (by rw [hμ]; exact hd) hab he4 hT hlam hTf).bind fun b ↦
      (Spec.ret (Post := fun cl h ↦ Doomed (fun _ ↦ S) (fun q ↦
        (∀ c ∈ cl, StackClaim.Holds lay26.nuMain c.onStack q.1) ∧ aRmT Ti lay26 pub R w r q) h)
        (mbClaimsL CMain.nu20 Ti.mbT b)).mono
        (fun _ hp q hqS hq ↦ by
          obtain ⟨ha, hpl, hvl, W, hW, hR⟩ := hp
          exact hR _ ⟨q, ⟨hqS, hq.2⟩, rfl⟩
            (seamBus_lvm Ti hτL hsc hlay hfix hkey hlin b ⟨ha, hpl, hvl⟩ q.1 q.2 hq.1))
        (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).mono
      (fun _ hp ↦ by
        obtain ⟨⟨W, hW⟩, hD⟩ := hp
        exact ⟨W, hW, fun o ho hR ↦ by
          obtain ⟨p, ⟨hpS, hpR⟩, rfl⟩ := ho
          exact hD p hpS ⟨hR, hpR⟩⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl)

/-- **The typed phases at depth `d` on a fixed candidate set** (`typedSpecInL`'s proof over `typedProgLB d`). -/
noncomputable def typedSpecInLB {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column lay26.nuMain × Column lay26.nuRec))
    (hS : S.ncard ≤ L₀) (hTi : Ti.Ok) (hmaps : Ti.MapsFit lay26) (hrec : lay26.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hfix : FixOk Ti.mbT) (hlin : mbLinB Ti.mbT = true) (d : ℕ) (hd : d ≠ 0)
    (hμ : (inst lay26 Ti.mbT hτL).μBus = d)
    (hfin : S.Finite) {T : ℝ≥0∞} (herr : TErrsL L₀ (inst lay26 Ti.mbT hτL) εmax T) :
    Spec (typedProgLB d Ti pub)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ TGoodT Ti lay26 hτL pub p ∧ R p ∧ AccOkTT Ti pub) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold lay26 out p ∧ R p) h) εmax 0 T := by
  obtain ⟨hτ, hω, hz, hγ, hwr, hκ, ht, hab0, hab, he4, hTl, hlam, hTf⟩ := herr.factsL
  have hst : Stable (fun _ : List Ev ↦ S) := fun _ _ _ ↦ rfl
  have hcard : ∀ h : List Ev, ((fun _ : List Ev ↦ S) h).ncard ≤ L₀ := fun _ ↦ hS
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  unfold typedProgLB
  refine (((zeroSpecTT (C := fun _ ↦ S) (T := 0) Ti.Q Ti.lay (zT Ti lay26 pub) (aR0T Ti lay26 pub hτL R) hst hcard
      hτ hω hz zero_le).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.2 fun q hq ↦ ⟨⟨wiringRelT_of_zeroOn _ _ hTi.1 _ hq.1, hq.2.1⟩, hq.2.2.1, hq.2.2.2⟩,
      hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun z ↦ ?_
  by_cases hz' : z.1.length = xVars ∧ z.2.length = 9
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hz' ⟨hp.1.1, hp.1.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((wireSpecTT (C := fun _ ↦ S) (T := 0) Ti lay26 pub (aR0T Ti lay26 pub hτL R) hst hcard hTi hγ hwr zero_le
      z.1 z.2).frame _ (hJ _)).mono (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind'
    fun w ↦ ?_
  by_cases hw' : w.1.length = yVars ∧ w.2.1.length = 12 ∧ w.2.2.length = 4
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hw' ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((relaySpecTT (C := fun _ ↦ S) Ti lay26 pub hst hcard hTi hmaps hrec hwr hab0
      (fun q ↦ VsTrueT Ti (z.1 ++ w.1) w.2.1 ∧ aR0T Ti lay26 pub hτL R q) w.1 w.2.2).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.1.2.2.2 fun q hq ↦ ⟨hq.2.1, hq.1, hq.2.2⟩, hp.2⟩)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun r ↦ ?_
  by_cases hr' : r.1.length = relayRounds
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hr' hp.1.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((accSpecQT Ti.Q Ti.lay hTi.1 (ok := true) (yIn := accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1
      (by simp [accPtT, hacc]) (by rw [List.length_append, hz'.1, hw'.1]) hw'.2.1
      (Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst lay26 Ti.mbT hτL) () (stackOf lay26 q.1 q.2) ∧
        aRmT Ti lay26 pub R w r q))
      (fun _ _ _ h ↦ h) hκ ht hab0).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨by
      by_cases hg : AccGoodT true (accYT pub) (accPtT pub) Ti.Q Ti.lay w.2.1 (z.1 ++ w.1)
      · refine .inr (Doomed.mono hp.1.2 fun q ⟨hm, hp', hR⟩ ↦ ⟨hp'.1, hp'.2, fun o ho ↦ ?_, hm, hR, hg.2.1⟩)
        have h0 := hg.2.2 o (by simp only [selBitsT]; omega)
        rw [deltaT, sub_eq_zero] at h0
        exact h0
      · exact .inl hg, hp.2⟩)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun _ ↦ ?_
  refine ((miniSpecLB Ti pub hτL R S hS hfin hsc hlay hkey hfix hlin d hd hμ hab he4 hTl hlam hTf w r).mono
    (fun _ hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun cl ↦ ?_
  exact (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold lay26 out p ∧ R p) h)
      (typedClaimsL Ti w.1 w.2.2 r.1 r.2 cl)).mono
    (fun _ hp ↦ Doomed.mono hp fun q hq ↦ by
      obtain ⟨⟨h1, h2⟩, hR⟩ := hq
      simp only [typedClaimsL, List.mem_append] at h1 h2
      refine ⟨fun c hc ↦ h2 _ (.inr (List.mem_map_of_mem hc)), ⟨?_, ?_, ?_, ?_⟩, hR⟩
      · have := holds_relayPointT lay26 hrec r.1 hr' r.2 q.2 fun c hc ↦ h1 c (.inl hc)
        rw [show 2 ^ lay26.nuRec = 2 ^ relayRounds by rw [hrec]]
        exact this
      · exact ((holds_comT Ti lay26 pub hTi hmaps q.1 q.2 w.1 _).mp fun c hc ↦ h2 c (.inl (.inl hc))).symm
      · exact ((holds_sigmaT Ti lay26 pub hTi hmaps q.1 q.2 w.1 _).mp fun c hc ↦ h1 c (.inr hc)).symm
      · exact ((holds_ksT Ti lay26 pub hTi hmaps q.1 q.2 w.1 _).mp fun c hc ↦ h2 c (.inl (.inr hc))).symm)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

end PhasesB

/-- **The typed phases at depth `d`** (`typedSpecGL`'s proof over `typedProgLB d`). -/
noncomputable def typedSpecGLB (Ti : TInst) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit lay26) (hrec : lay26.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hfix : FixOk Ti.mbT) (hlin : mbLinB Ti.mbT = true) (d : ℕ) (hd : d ≠ 0)
    (hμ : (inst lay26 Ti.mbT hτL).μBus = d)
    (C : List Ev → Set (Column lay26.nuMain × Column lay26.nuRec)) (R : Column lay26.nuMain × Column lay26.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrsL L₀ (inst lay26 Ti.mbT hτL) εmax T) :
    Spec (typedProgLB d Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGoodT Ti lay26 hτL pub p ∧ R p ∧ AccOkTT Ti pub) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold lay26 out p ∧ R p) h) εmax 0 T :=
  (Lvm.M3.Spec.glue (ι := {S : Set (Column lay26.nuMain × Column lay26.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecInLB Ti pub hτL R S.1 S.2.2 hTi hmaps hrec hacc hsc hlay hkey hfix hlin d hd hμ S.2.1 herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

/-- `contIvSB aSP` is well placed (`ivOk_contIvS`'s proof). -/
theorem ivOk_contIvSB : IvOk (contIvSB aSP) := by
  refine ⟨fun ab hab ↦ ?_, ?_⟩
  · simp only [contIvSB, List.mem_cons, List.mem_nil_iff, or_false] at hab
    rcases hab with rfl | rfl | rfl <;> (simp only [bB, aSP]; omega)
  · simp only [contIvSB, List.pairwise_cons, List.mem_cons, or_false, forall_eq_or_imp, forall_eq,
      List.not_mem_nil, false_imp_iff, implies_true, List.Pairwise.nil, and_true, bB, aSP]
    omega

/-- **The typed phases at S2GB on the viewed pinned pairs** (`specBusGS`'s proof over `typedProgLB 13`). -/
noncomputable def specBusGSB {Ti : TInst} (H : THypSB Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) (x : List UInt8) (Gk N : Lvm.ASM.Pair → Prop) :
    Spec (typedProgLB 13 Ti (pubXTS x))
      (fun h ↦ Lvm.E2F.PinPost za h ∧
        Doomed (Lvm.E2F.candRelZ recOf za x)
          (fun p ↦ GbTS Ti H.hτ x (Lvm.Shape.vp x p) ∧ (Gk (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p))) h)
      (fun a h ↦ Doomed (Lvm.E2F.candRelZ recOf za x)
        (fun p ↦ (BT x a (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p)) ∧
          (Gk (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p))) h ∧ Lvm.E2F.PinPost za h)
      εS leadF₂ 0 :=
  have S0 := typedSpecGLB Ti (pubXTS x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.fix H.lin 13 (by norm_num) (H.μBus H.hτ)
    (imgCZ recOf za x) (fun p ↦ Lvm.ASM.BndS x p.1 ∧ Gk p ∧ N p) (L₀ := 1) (εmax := εS) (T := 0)
    (fun h ↦ 1 ≤ (commits h).length) (imgCZ_append recOf za x) (fun _ ↦ Set.toFinite _)
    (imgCZ_ncard_le_one recOf za x) (H.errs H.hτ)
  (S0.frame (Lvm.E2F.PinPost za) (fun _ _ hl hr ↦ pinPost_append za
      ((noCG_typedProgLB 13 Ti (pubXTS x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.Typed.rootShapeM_one hr.1, Lvm.Typed.rootShapeM_firstWord hr.1,
      doomed_imgCZ.mpr (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCZ.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩,
      hp.2⟩)
    le_rfl zero_le le_rfl

/-- **S2GB's middle phases' specification** (`midSpecP_GS`'s proof over `midGB`, `GoodTSB`). -/
theorem midSpecP_GSB (Ti : TInst) (H : THypSB Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) :
    Lvm.ASM.MidSpecPτ (midGB Ti) (Lvm.E2F.candRelZ recOf za) (Lvm.E2F.PinPost za)
      (Lvm.Shape.Good₂ (GoodTSB Ti H)) εS leadF₂ τU := by
  have hS : E2V.SplitSound := fun nu c hc q h ↦ splitE2_sound nu c hc q h
  have hA : E2V.SplitAffine := fun nu c hc ↦ isMultiaffine_splitE2 nu c hc
  have h7 : (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) ≤ εS := by
    simpa using E2V.sum7_le_εS
  exact Lvm.ASM.midSpecOfRelGτ (busP := fun x ↦ typedProgLB 13 Ti (pubXTS x))
    (kgP := fun x ↦ tapeProgL (contIvSB aSP) (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleU₂ x a k) (Lb := leadF₂) (Lk := 0)
    (Gb := fun x p ↦ GbTS Ti H.hτ x (Lvm.Shape.vp x p)) (Gk := fun x p ↦ GkL (contIvSB aSP) x (Lvm.Shape.vp x p))
    (B := fun x a p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p))
    (Kc := fun x k p ↦ KcU (Lvm.NS.colM (Lvm.Shape.vp x p).1) k)
    (Qa := fun _ a ↦ (∀ c ∈ a.1, LeanVM.Protocol.Whir.Sound.IsMultiaffine 19 c.1) ∧
      (∀ c ∈ a.2, LeanVM.Protocol.Whir.Sound.IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39)
    (Qk := fun _ ↦ KgRetU) (C := Lvm.E2F.candRelZ recOf za) (Sh := Lvm.E2F.PinPost za)
    (fun _ _ hl hr ↦ E2V.pinPost_append za hl hr)
    (fun x ↦ specBusGSB H recOf za x (GkL (contIvSB aSP) x) fun p ↦ ¬ (GbTS Ti H.hτ x p ∧ GkL (contIvSB aSP) x p))
    (fun x ↦ retOK_typedProgLB 13 Ti H.layOk (pubXTS x))
    (fun x a T hT ↦ (tapeSpecLW ivOk_contIvSB (E2V.candRelZ_stable recOf za x) (E2V.candRelZ_ncard_le recOf za x)
        (hdX x).s (n := (pubX x).n) (fun p ↦ Lvm.NS.colM (Lvm.Shape.vp x p).1)
        (fun p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p) ∧
          ¬ (GbTS Ti H.hτ x (Lvm.Shape.vp x p) ∧ GkL (contIvSB aSP) x (Lvm.Shape.vp x p)))
        (calc (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) + T
            ≤ (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) +
                (εS - ∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) := add_le_add le_rfl hT
          _ = εS := add_tsub_cancel_of_le h7)).mono
      (fun _ hd ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hd fun p ⟨ht, hb, hn⟩ ↦
        ⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hn⟩, hb, hn⟩)
      (fun _ _ hp ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hp.2.2.2 fun p ⟨⟨h1, h2, h3, h4, h5⟩, hR⟩ ↦
        ⟨h1, h2, h3, h4, h5, hR⟩) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_tapeProgL _ _ _) (fun _ ↦ cg_tapeProgL _ _ _)
    (fun x a k p _ hk h1 h2 ↦ linkU hS x a k p hk h1 h2)
    (fun x a k ha hk ↦ sideU hA x a k ha hk)


/-- S2GB's middle phases commit nothing and ask no proof of work (`cg_midGS`'s proof). -/
theorem cg_midGB (Ti : TInst) (x : List UInt8) : Lvm.M3.NoCG (midGB Ti x) :=
  Lvm.M3.NoCG.bind (noCG_typedProgLB 13 Ti _) fun _ ↦ Lvm.M3.NoCG.bind (cg_tapeProgL _ _ _) fun _ ↦
    Lvm.M3.cg_ret _

/-- **S2GB's middle phases' claims are fewer than `2^40`** (`retOK_midGS_len`'s proof). -/
theorem retOK_midGB_len (Ti : TInst) (H : THypSB Ti) (x : List UInt8) :
    LeanVM.Protocol.EndToEnd.Sound.RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (midGB Ti x) := by
  refine (retOK_typedProgLB 13 Ti H.layOk (pubXTS x)).bind fun a ha ↦
    LeanVM.Protocol.EndToEnd.Sound.RetOK.bind_true fun k ↦ LeanVM.Protocol.EndToEnd.Sound.RetOK.ret ?_
  have hz : ∀ l : List Lvm.VEq.VStackClaim, (Lvm.Shape.onStackZs x l).length = l.length := fun l ↦ by
    unfold Lvm.Shape.onStackZs
    split_ifs <;> simp only [List.length_map]
  simp only [assembleU₂, hz, List.length_append, List.length_map, length_tapeClaimsU]
  have := ha.2.2
  omega

end Lvm.E2S

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U Lvm.E2S
open Lvm.E2T (TNatT TRefHypT)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-- **CAP-FRZ L**: S2GB's middle phases commit nothing and grind nothing. -/
theorem midShapeB20 (Ti : TInst) : MidShapeM (midMk 4 relocU20 (midGB Ti)) := midShapeMk_of 4 (cg_midGB Ti)

/-- **The good relation at S2GB** (`GoodSM`'s over S2GB's good pair `GoodTSB`). -/
def GoodSMB (Ti : TInst) (H : THypSB Ti) : GoodRelM := GoodOfM recOfU20 (Lvm.Shape.Good₂ (GoodTSB Ti H))

/-- **CAP-FRZ L**: **the middle phases' obligation at S2GB** (`midSpecPinS20`'s over `midGB`, the mini-bus at depth
13, `THypSB`). -/
theorem midSpecPinB20 (Ti : TInst) (H : THypSB Ti) :
    MidSpecPinτ (midMk 4 relocU20 (midGB Ti)) (GoodSMB Ti H) εS leadF20 τU :=
  midSpecPinMk_ofτ 4 relocLawU20 (midSpecP_GSB Ti H recOfU20) (retOK_midGB_len Ti H)

end Lvm.CT
