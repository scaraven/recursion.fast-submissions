-- New for lvm2 E2-FT (stage S2GT, E2F-T): the proof of `typedSpecT`: the zerocheck, the wiring, the relayout and A23
-- at `E2` (LvmE2TZero, LvmE2TWire, LvmE2TAcc), roll 11's `E3` mini-bus, the split claims; on a fixed candidate set,
-- then glued (as `typedSpecR`).
import LvmE2TWire
import LvmE2TAcc

/-!
# The typed phases at `E2`: the proof

* `wiringRelT_of_zeroOn`: the relation's table vanishing on the cube is the relation (slots off the cube carry no
  entries).
* `TErrsT.factsT`: the error side conditions in the phases' forms.
* **`typedSpecInT`**: on a fixed candidate set (roll 11's `typedSpecIn`), the phases composed; **`typedSpecGT`**:
  generic in the candidate set (`Lvm.M3.Spec.glue`), the statement of `typedSpecT`.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Lvm.M3 (Tab inst stackOf KeysOk AllSc LayOk FixOk)
open Lvm.ASM (OpenClaims)
open Finset
open scoped ENNReal NNReal

/-- The typed phases' program, unfolded. -/
theorem typedProgT_eq (Ti : TInst) (pub : Lvm.Pub) : typedProgT Ti pub =
    (zeroProgT >>= fun z ↦ wireProgT Ti pub z.2 >>= fun w ↦ relayProgT Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
      accProgT Ti.Q Ti.lay true (accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1 >>= fun _ ↦
        miniBusProg Ti >>= fun cl ↦ pure (typedClaimsT Ti w.1 w.2.2 r.1 r.2 cl)) := by
  rw [typedProgT]

theorem errG_mono_c (g : ℕ) {c c' : ℕ} (h : c ≤ c') : errG g c ≤ errG g c' := by
  unfold errG
  gcongr

/-- **The table vanishing on the cube is the relation** (a checked layout: off the cube no slot has entries). -/
theorem wiringRelT_of_zeroOn (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK)
    (h : ZeroOnF (deltaZT Q lay z) [] (xVars + 2)) : WiringRelT Q lay z := by
  rw [zeroOnF_nil] at h
  intro x k hk
  by_cases hx : x < 2 ^ xVars
  · have hv : x + 2 ^ xVars * k < 2 ^ (xVars + 2) := by
      rw [pow_add]; nlinarith
    have h1 : (x + 2 ^ xVars * k) / 2 ^ xVars = k := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
    have h2 : (x + 2 ^ xVars * k) % 2 ^ xVars = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have := h _ hv
    rw [deltaZT, h1, if_pos hk, h2] at this
    exact FE2.toE2_injective (this.trans FE2.toE2_zero.symm)
  · have h0 : ∀ o, matZT Q lay o z x = 0 := fun o ↦ by
      unfold matZT
      rw [List.filter_eq_nil_iff.mpr fun e he ↦ by
        have := (entsT_fit Q lay hlay e he).2.1
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro _ hex; omega]
      rfl
    rcases k with _ | _ | _ <;> simp [relT, mulY3, h0]

/-- **The error side conditions in the phases' forms.** -/
theorem TErrsT.factsT {L₀ : ℕ} {I : M3Instance} {εmax T : ℝ≥0∞} (h : TErrsT L₀ I εmax T) :
    (L₀ : ℝ≥0∞) * errG gTau 1 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errG gOmega 2 + 0 ≤ εmax ∧
      (L₀ : ℝ≥0∞) * errG gZero 2 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errG gGamma 8 + 0 ≤ εmax ∧
      (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax ∧ errG gKappa 1 ≤ εmax ∧ errG gT phiVarsT ≤ εmax ∧
      abError I L₀ + 0 ≤ εmax ∧ abError I L₀ < 1 ∧ roundError L₀ 4 ≤ εmax ∧
      interpLead L₀ 2 (lambdaError L₀) ≤ εmax ∧ lambdaError L₀ + 0 ≤ εmax ∧ roundError L₀ 3 + T ≤ εmax ∧
      T ≤ εmax ∧ ∀ n, xiError I L₀ + sumcheckLead (List.replicate n none) T ≤ εmax := by
  have hM1 : abError I L₀ + 0 ≤ leadMiniT L₀ I T := le_max_left _ _
  have hM3 : T ≤ leadMiniT L₀ I T := le_max_right _ _
  have hle : ∀ a : ℝ≥0∞, a ≤ a + leadMiniT L₀ I T := fun a ↦ le_self_add
  refine ⟨by rw [add_zero]; exact h.tau, by rw [add_zero]; exact h.omega,
    by rw [add_zero]; exact le_trans (by gcongr; exact errG_mono_c _ (by norm_num)) h.zero,
    by rw [add_zero]; exact h.gamma, by rw [add_zero]; exact h.wire, h.kappa, h.t, hM1.trans h.follow, h.ab.1,
    (hle _).trans (h.rounds 4 le_rfl), (hle _).trans h.lam.1, ?_, ?_, hM3.trans h.follow, fun n ↦ ?_⟩
  · rw [add_zero]; exact (hle _).trans h.lam.2
  · exact (add_le_add le_rfl hM3).trans (h.rounds 3 (by norm_num))
  · exact (add_le_add le_rfl ((sumcheckLead_le _ _).trans hM3)).trans h.xi

section Phases

variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- The carried predicate: the mini-bus relation, `R`, `AccOk acc_in` at `E2`. -/
def aR0T (q : Column L.nuMain × Column L.nuRec) : Prop :=
  M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ R q ∧ AccOkTT Ti pub

/-- **Carried to the mini-bus**: the typed claims' meaning (`C_rec`'s extension at the relayout's point; the
committed, `σ′` and `KS` region values) and `R`. -/
def aRmT (w : List E2 × List E2 × List E2) (r : List E2 × E2) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  (r.2 = (∑ w' ∈ range (2 ^ L.nuRec), E2V.eqAtF r.1 w' * recT q.2 w') ∧
    w.2.2.getD 0 0 = regSumT Ti (· == .com) (zwT (zT Ti L pub q)) w.1 ∧
    w.2.2.getD 2 0 = regSumT Ti (· == .sigma) (zwT (zT Ti L pub q)) w.1 ∧
    w.2.2.getD 3 0 = regSumT Ti (· == .ks) (zwT (zT Ti L pub q)) w.1) ∧ R q

variable {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column L.nuMain × Column L.nuRec)) (hS : S.ncard ≤ L₀)

/-- **The mini-bus at `E3`** (roll 11's `miniSpecTy` with S2GT's carried predicate). -/
noncomputable def miniSpecT (hfin : S.Finite) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth) {T : ℝ≥0∞}
    (hab : abError (inst L Ti.mbT hτL) L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError (inst L Ti.mbT hτL) L₀ +
      sumcheckLead (List.replicate ((Lvm.M3.vLayout Ti.mbT).tableLogHeights.foldl max 0) none) T ≤ εmax)
    (w : List E2 × List E2 × List E2) (r : List E2 × E2) :
    Spec (miniBusProg Ti)
      (fun h ↦ (∃ W, firstWord h = some W) ∧ Doomed (fun _ ↦ S) (fun q ↦
        M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ aRmT Ti L pub R w r q) h)
      (fun cl h ↦ Lvm.ASM.TabRet Ti.mbT cl ∧ Doomed (fun _ ↦ S) (fun q ↦
        (∀ c ∈ cl, Lvm.M3.BlockHolds L Ti.mbT q.1 q.2 c) ∧ aRmT Ti L pub R w r q) h)
      εmax (abError (inst L Ti.mbT hτL) L₀ + 0) T :=
  Spec.congr (by rw [hμ]; rfl)
    ((Lvm.KG.specWithRet (Lvm.M3.midBusTableSpecB L Ti.mbT hτL (fun _ ↦ S) (aRmT Ti L pub R w r) hlay hsc hkey
        hw hfix (fun _ ↦ True) (fun _ _ _ ↦ rfl) (fun _ ↦ hfin) (fun _ ↦ hS) (by rw [hμ]; norm_num) hab he4 hT
        hlam he3 hTf hxi) (Lvm.ASM.retOK_lbusTableCheckProg _ _)).mono (fun _ hp ↦ ⟨trivial, hp⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl)

/-- **The typed phases at `E2` on a fixed candidate set** (roll 11's `typedSpecIn`): the zerocheck, the wiring, the
relayout, A23 and the mini-bus composed; the first commitment's word carried to the mini-bus. -/
noncomputable def typedSpecInT (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (hfin : S.Finite) {T : ℝ≥0∞} (herr : TErrsT L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProgT Ti pub)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ TGoodT Ti L hτL pub p ∧ R p ∧ AccOkTT Ti pub) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax 0 T := by
  obtain ⟨hτ, hω, hz, hγ, hwr, hκ, ht, hab0, hab, he4, hTl, hlam, he3, hTf, hxi⟩ := herr.factsT
  have hst : Stable (fun _ : List Ev ↦ S) := fun _ _ _ ↦ rfl
  have hcard : ∀ h : List Ev, ((fun _ : List Ev ↦ S) h).ncard ≤ L₀ := fun _ ↦ hS
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  rw [typedProgT_eq]
  refine (((zeroSpecTT (C := fun _ ↦ S) (T := 0) Ti.Q Ti.lay (zT Ti L pub) (aR0T Ti L pub hτL R) hst hcard
      hτ hω hz zero_le).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.2 fun q hq ↦ ⟨⟨wiringRelT_of_zeroOn _ _ hTi.1 _ hq.1, hq.2.1⟩, hq.2.2.1, hq.2.2.2⟩,
      hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun z ↦ ?_
  by_cases hz' : z.1.length = xVars ∧ z.2.length = 9
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hz' ⟨hp.1.1, hp.1.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((wireSpecTT (C := fun _ ↦ S) (T := 0) Ti L pub (aR0T Ti L pub hτL R) hst hcard hTi hγ hwr zero_le
      z.1 z.2).frame _ (hJ _)).mono (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind'
    fun w ↦ ?_
  by_cases hw' : w.1.length = yVars ∧ w.2.1.length = 12 ∧ w.2.2.length = 4
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hw' ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((relaySpecTT (C := fun _ ↦ S) Ti L pub hst hcard hTi hmaps hrec hwr hab0
      (fun q ↦ VsTrueT Ti (z.1 ++ w.1) w.2.1 ∧ aR0T Ti L pub hτL R q) w.1 w.2.2).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.1.2.2.2 fun q hq ↦ ⟨hq.2.1, hq.1, hq.2.2⟩, hp.2⟩)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun r ↦ ?_
  by_cases hr' : r.1.length = relayRounds
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hr' hp.1.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((accSpecQT Ti.Q Ti.lay hTi.1 (ok := true) (yIn := accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1
      (by simp [accPtT, hacc]) (by rw [List.length_append, hz'.1, hw'.1]) hw'.2.1
      (Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ aRmT Ti L pub R w r q))
      (fun _ _ _ h ↦ h) hκ ht hab0).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨by
      by_cases hg : AccGoodT true (accYT pub) (accPtT pub) Ti.Q Ti.lay w.2.1 (z.1 ++ w.1)
      · refine .inr (Doomed.mono hp.1.2 fun q ⟨hm, hp', hR⟩ ↦ ⟨hp'.1, hp'.2, fun o ho ↦ ?_, hm, hR, hg.2.1⟩)
        have h0 := hg.2.2 o (by simp only [selBitsT]; omega)
        rw [deltaT, sub_eq_zero] at h0
        exact h0
      · exact .inl hg, hp.2⟩)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun _ ↦ ?_
  refine ((miniSpecT Ti L pub hτL R S hS hfin hsc hlay hkey hw hfix hμ hab he4 hTl hlam he3 hTf (hxi _) w r).mono
    (fun _ hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun cl ↦ ?_
  exact (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h)
      (typedClaimsT Ti w.1 w.2.2 r.1 r.2 cl)).mono
    (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ by
      obtain ⟨⟨h1, h2⟩, hR⟩ := hq
      simp only [typedClaimsT, List.mem_append] at h1 h2
      refine ⟨Lvm.Typed.blockHolds_mini L hlay hp.1 (fun c hc ↦ h1 c (.inr hc))
          (fun c hc ↦ h2 c (.inr hc)), ⟨?_, ?_, ?_, ?_⟩, hR⟩
      · have := holds_relayPointT L hrec r.1 hr' r.2 q.2 fun c hc ↦ h1 c (.inl (.inl hc))
        rw [show 2 ^ L.nuRec = 2 ^ relayRounds by rw [hrec]]
        exact this
      · exact ((holds_comT Ti L pub hTi hmaps q.1 q.2 w.1 _).mp fun c hc ↦ h2 c (.inl (.inl hc))).symm
      · exact ((holds_sigmaT Ti L pub hTi hmaps q.1 q.2 w.1 _).mp fun c hc ↦ h1 c (.inl (.inr hc))).symm
      · exact ((holds_ksT Ti L pub hTi hmaps q.1 q.2 w.1 _).mp fun c hc ↦ h2 c (.inl (.inr hc))).symm)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

end Phases

/-- **`typedSpecT`'s statement, proved** (glued over the candidate sets, as `typedSpecR`). -/
noncomputable def typedSpecGT (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
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
  (Lvm.M3.Spec.glue (ι := {S : Set (Column L.nuMain × Column L.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecInT Ti L pub hτL R S.1 S.2.2 hTi hmaps hrec hacc hsc hlay hkey hw hfix hμ S.2.1 herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

end Lvm.E2T
