-- New for lvm2 MB-LIN (MBL-L, 2026-11-16): DAY-0 STATEMENTS of S2GL's middle phases (S2GU's with the mini-bus's
-- table phase deleted: the bus phase ends in the three linear claims of `LvmS2GLLin`), their error groups and
-- hypotheses. Every `sorry` is a day-0 statement tagged `-- MBL-STMT <n>`.
import LvmS2GUMid
import LvmS2GLLin
import LvmE2TRet
import LvmS2GLSched
import LvmS2GLPlan

/-!
# S2GL's middle phases (day-0 statements)

* **`miniBusLProg tabs μ`**: the mini-bus at S2GL: `lvmBusProg μ` (`(α, β)`, the grand product, the count root
  nonzero, the trailing zero scalar), then the three claims `mbClaimsL 23 tabs b` (no `ξ`, no table rounds, no column
  evaluations, no fixed-column check).
* **`typedClaimsL`**: `typedClaimsT`'s with the mini-bus's `C_main` claims replaced by the three claims (in their
  place: after the `KS` aliases' claims, before the front's) and no mini-bus `C_rec` claim (`mbLinB`: none exists).
* **`typedProgL Ti pub`** (`typedProgT`'s with `miniBusLProg`), **`midGL Ti x`** (`midGU`'s with `typedProgL`).
* **`TErrsL`**: `TErrsT` without `ξ`'s group; **`THypL`**: `THypT` with `TErrsL` and `mbLinB`; **`GoodTL`**: S2GU's
  good pair (the relation is unchanged: the mini-bus balances).
* Statements (owner L): **`midSpecP_GL`** (MBL-STMT 4), `retOK_midGL_len` (4b), `cg_midGL` (4c), `retOK_typedProgL`
  (4d), **`errsL_at`** (MBL-STMT 5).
-/

set_option autoImplicit false

namespace Lvm.E2L

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.E2U Lvm.Typed LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26 LBus lvmBusProg mbClaimsL mbLinB stackOf)
open Lvm.VEq (BClaim VStackClaim hdX pubX pubXT)
open Lvm.ASM (OpenClaims GoodRel εS)
open LeanVM.Protocol.KeccakGkr (errE)
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open scoped ENNReal

/-! ## The programs -/

/-- **The mini-bus at S2GL**: the bus phase at depth `μ`, then the three linear claims on `C_main`. -/
def miniBusLProg (tabs : List Tab) (μ : ℕ) : VerifierProgram (List BClaim) :=
  (lvmBusProg μ).bind fun b ↦ VerifierProgram.ret (mbClaimsL CMain.nu20 tabs b)

/-- **The typed claims at S2GL**: `typedClaimsT`'s, the mini-bus's claims the three linear claims (on `C_main`). -/
def typedClaimsL (Ti : TInst) (ry rv rr : List E2) (vR : E2) (cl : List BClaim) : OpenClaims :=
  ((splitE2 relayRounds (pointE2 ⟨relayRounds, 0⟩ rr vR)).map (·.onStack) ++
      regClaimT Ti .sigma Ti.sigmaW ry (rv.getD 2 0),
    regClaimT Ti .com Ti.comW ry (rv.getD 0 0) ++ regClaimT Ti .ks Ti.ksW ry (rv.getD 3 0) ++
      cl.map (·.onStack))

/-- **The typed phases at S2GL**: S2GT's zerocheck, wiring, relayout, A23 at `E2`; the mini-bus without its table
phase; the claims. -/
@[irreducible] def typedProgL (Ti : TInst) (pub : Lvm.Pub) : VerifierProgram OpenClaims :=
  zeroProgT >>= fun z ↦ wireProgT Ti pub z.2 >>= fun w ↦ relayProgT Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
    accProgT Ti.Q Ti.lay true (accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1 >>= fun _ ↦
      miniBusLProg Ti.mbT miniDepth >>= fun cl ↦ pure (typedClaimsL Ti w.1 w.2.2 r.1 r.2 cl)

/-- **The S2GL trace's sponge blocks less one** (RE-FREEZE R1: `spongeBlocks P20L − 1 = 3,842`): the wire's first
`cont` interval is `[1, bL]`. -/
abbrev bL : ℕ := 3842

/-- **S2GL's middle phases**: the typed phases at S2GL, the merged tape at `b = bL` (`tapeProgB`, RE-FREEZE R1), the
claims (`assembleU₂`). -/
def midGL (Ti : TInst) (x : List UInt8) : VerifierProgram OpenClaims :=
  typedProgL Ti (pubXT x) >>= fun a ↦ tapeProgB bL (hdX x).s (pubX x).n >>= fun k ↦ pure (assembleU₂ x a k)

/-- The mini-bus at S2GL commits nothing and asks no proof of work. -/
theorem cg_miniBusLProg (tabs : List Tab) (μ : ℕ) : Lvm.M3.NoCG (miniBusLProg tabs μ) :=
  Lvm.M3.NoCG.bind (Lvm.M3.cg_lvmBusProg μ) fun _ ↦ Lvm.M3.cg_ret _

/-- **The typed phases at S2GL commit nothing and ask no proof of work.** -/
theorem noCG_typedProgL (Ti : TInst) (pub : Lvm.Pub) : Lvm.M3.NoCG (typedProgL Ti pub) := by
  unfold typedProgL
  exact Lvm.M3.NoCG.bind cg_zeroProgT fun _ ↦ Lvm.M3.NoCG.bind (cg_wireProgT _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_relayProgT _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_accProgT _ _ _ _ _ _ _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_miniBusLProg _ _) fun _ ↦ Lvm.M3.cg_ret _

/-! ## The three claims' shape -/

/-- `sumE` of multiaffine weights is multiaffine (`LvmMPCertOff.isMultiaffine_sumE`'s statement; that module is
outside the shipped closure). -/
theorem isMultiaffine_sumEL {n : ℕ} {γ : Type} (xs : List γ) (F : γ → List E → E)
    (hF : ∀ a ∈ xs, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ LeanVM.Protocol.Verifier.sumE (xs.map fun a ↦ F a l) := by
  have e : ∀ l : List E, LeanVM.Protocol.Verifier.sumE (xs.map fun a ↦ F a l) = (xs.map fun a ↦ F a l).sum :=
    fun l ↦ by simp only [LeanVM.Protocol.Verifier.sumE, List.foldl_eq_foldr, List.sum_eq_foldr]
  simp only [e]
  clear e
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (List.mem_cons_self ..)).add (ih fun b hb ↦ hF b (List.mem_cons_of_mem _ hb))

/-- A part of a side's claim is a committed column's block. -/
theorem mem_mbPartsL {tabs : List Tab} {r : LeanVM.Protocol.Verifier.BusResult} {s : ℕ}
    {p : E × Lvm.VEq.VPlacement × List E} (h : p ∈ Lvm.M3.mbPartsL tabs r s) :
    ∃ t ∈ tabs, ∃ (c : ℕ) (rec : Bool) (off : ℕ), t.cols[c]? = some (Lvm.M3.ColSrc.com rec off) ∧
      p.2.1 = ⟨t.τ, off⟩ := by
  unfold Lvm.M3.mbPartsL at h
  obtain ⟨tj, htj, hp⟩ := List.mem_flatMap.mp h
  obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp hp
  have ht : tj.1 ∈ tabs := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp htj)
  split at hc
  · rename_i rec off hcol
    exact ⟨tj.1, ht, c, rec, off, hcol, by rw [← Option.some_inj.mp hc]⟩
  · exact absurd hc (by simp)

/-- **Each side's claim is multiaffine on `C_main`** (its blocks are aligned inside `C_main`: `LayOk lay26`). -/
theorem isMultiaffine_mbClaimL (tabs : List Tab) (hlay : LayOk lay26 tabs) (r : LeanVM.Protocol.Verifier.BusResult)
    (s : ℕ) : IsMultiaffine CMain.nu20 (Lvm.M3.mbClaimL CMain.nu20 tabs r s).onStack.1 := by
  refine Lvm.ASM.isMultiaffine_onStack _ le_rfl ?_
  unfold Lvm.M3.mbClaimL Lvm.VEq.sumClaimE
  refine isMultiaffine_sumEL _ _ fun p hpm ↦ ?_
  obtain ⟨t, ht, c, rec, off, hcol, hb⟩ := mem_mbPartsL hpm
  obtain ⟨co, blk, z⟩ := p
  simp only at hb
  subst hb
  have hc : c < t.w := (List.getElem?_eq_some_iff.mp hcol).1
  have hal := hlay t ht c hc
  unfold Lvm.M3.Aligned at hal
  rw [hcol] at hal
  obtain ⟨-, hfit, hnu⟩ := hal
  have hτ : t.τ ≤ CMain.nu20 := by
    have h1 : 2 ^ t.τ ≤ 2 ^ (if rec then lay26.nuRec else lay26.nuMain) := by omega
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    cases rec
    · simpa [lay26, CMain.nu20] using h2
    · exact (by simpa [lay26] using h2 : t.τ ≤ 19).trans (by norm_num [CMain.nu20])
  have h := (Lvm.ASM.isMultiaffine_onStack (n := CMain.nu20) ⟨⟨t.τ, off⟩, LeanVM.Protocol.Verifier.eqEval z, 0⟩
    hτ (Lvm.ASM.isMultiaffine_eqEvalN z _)).const_mul co
  have e : (fun x ↦ co * (⟨t.τ, off⟩ : Lvm.VEq.VPlacement).eqAbove x *
      LeanVM.Protocol.Verifier.eqEval z (x.take (⟨t.τ, off⟩ : Lvm.VEq.VPlacement).variableCount)) =
      fun x ↦ co * (BClaim.onStack ⟨⟨t.τ, off⟩, LeanVM.Protocol.Verifier.eqEval z, 0⟩).1 x :=
    funext fun x ↦ mul_assoc _ _ _
  rw [e]
  exact h

/-- **Every return of the mini-bus at S2GL is the three claims** of what the bus read. -/
theorem retOK_miniBusLProg (tabs : List Tab) (μ : ℕ) :
    RetOK (fun cl : List BClaim ↦ ∃ b : LBus, cl = mbClaimsL CMain.nu20 tabs b) (miniBusLProg tabs μ) :=
  RetOK.bind_true fun b ↦ RetOK.ret ⟨b, rfl⟩

/-! ## Errors, hypotheses, the good pair -/

/-- **The typed phases' error side conditions at S2GL**: `TErrsT`'s without `ξ`'s group (the table phase is gone). -/
structure TErrsL (L₀ : ℕ) (I : M3Instance) (εmax T : ℝ≥0∞) : Prop where
  tau : (L₀ : ℝ≥0∞) * errG gTau 1 ≤ εmax
  omega : (L₀ : ℝ≥0∞) * errG gOmega 2 ≤ εmax
  zero : (L₀ : ℝ≥0∞) * errG gZero 3 ≤ εmax
  gamma : (L₀ : ℝ≥0∞) * errG gGamma 8 ≤ εmax
  wire : (L₀ : ℝ≥0∞) * errG gWire 2 ≤ εmax
  kappa : errG gKappa 1 ≤ εmax
  t : errG gT phiVarsT ≤ εmax
  rounds : ∀ d ≤ 4, roundError L₀ d + leadMiniT L₀ I T ≤ εmax
  ab : abError I L₀ < 1 ∧ abError I L₀ + leadMiniT L₀ I T ≤ εmax
  lam : interpLead L₀ 2 (lambdaError L₀) + leadMiniT L₀ I T ≤ εmax ∧ lambdaError L₀ + leadMiniT L₀ I T ≤ εmax
  follow : leadMiniT L₀ I T ≤ εmax

/-- **MBL-STMT 5** (owner L): **S2GL's typed errors at `L₀ = 1`**: every group `≤ εS = 7·2^-131` (`errsT_at`'s
without `ξ`), follower lead `0`. -/
theorem errsL_at (I : M3Instance) (hμ : I.μBus = miniDepth) : TErrsL 1 I εS 0 := by
  have hg : ∀ {c g : ℕ}, grpEps 1 c g ≤ epsS → ((1 : ℕ) : ℝ≥0∞) * errG g c ≤ εS := fun h ↦
    (le_of_eq (add_zero _).symm).trans (errG_le_εS h)
  have hab : abError I 1 = errE (1 * (4 * 2 ^ 12)) := by rw [abError, Lvm.ASM.coe_overE, Lvm.ASM.errE_smul, hμ]
  have hr : ∀ d, roundError 1 d = errE (1 * d) := fun d ↦ by
    rw [roundError, Lvm.ASM.coe_div_card, Lvm.ASM.errE_smul]
  have hl : lambdaError 1 = errE (1 * 2) := by rw [lambdaError, Lvm.ASM.coe_div_card, Lvm.ASM.errE_smul]
  have hu : unitError 1 = errE (1 * 1) := by rw [← Lvm.ASM.errE_smul]; simp [unitError, errE]
  have hM : leadMiniT 1 I 0 = errE (1 * (4 * 2 ^ 12)) := by
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

/-- **The S2GL instance's hypotheses**: `THypT`'s with `TErrsL` and the mini-bus MB-LIN (`mbLinB`, the guard's). -/
structure THypL (Ti : TInst) : Prop where
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
  lin : mbLinB Ti.mbT = true
  μBus : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), (inst lay26 Ti.mbT h).μBus = miniDepth
  errs : ∀ (h : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ), TErrsL 1 (inst lay26 Ti.mbT h) εS 0

/-- **The good pair at S2GL**: `GbTB` (the typed relation, the mini-bus balances, the boundary, `acc_in`) and
`GkB bL` (the merged tape's relation with S2GL's `cont` rows, RE-FREEZE R1). -/
def GoodTL (Ti : TInst) (H : THypL Ti) : GoodRel := fun x qm qr ↦ GbTB Ti H.hτ x (qm, qr) ∧ GkB bL x (qm, qr)

/-! ## The middle phases' obligations -/

/-- **MBL-STMT 4d** (owner L): **the typed phases' return facts at S2GL** (`retOK_typedProgT_of`'s twin: multiaffine
claims, at most `2^39`). -/
theorem retOK_typedProgL (Ti : TInst) (H : THypL Ti) (pub : Lvm.Pub) :
    RetOK (fun a : OpenClaims ↦ (∀ c ∈ a.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ a.2, IsMultiaffine CMain.nu20 c.1) ∧
      a.1.length + a.2.length ≤ 2 ^ 39) (typedProgL Ti pub) := by
  unfold typedProgL
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ (retOK_relayProgT_len _ _ _).bind fun r hr ↦
    RetOK.bind_true fun _ ↦ ?_
  refine (retOK_miniBusLProg Ti.mbT miniDepth).bind fun cl hcl ↦ ?_
  obtain ⟨b, rfl⟩ := hcl
  refine RetOK.ret ?_
  have hm : ∀ c ∈ mbClaimsL CMain.nu20 Ti.mbT b, IsMultiaffine CMain.nu20 c.onStack.1 := fun c hc ↦ by
    obtain ⟨sd, -, rfl⟩ := List.mem_map.mp hc
    exact isMultiaffine_mbClaimL Ti.mbT H.layOk _ sd
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

/-! ## MBL-STMT 4: the typed phases at S2GL

`typedSpecInT`/`typedSpecGT`/`specBusGT`'s twins: the mini-bus's step (`miniSpecL`) is `lvmBusSpec4` then the three
claims, whose doom is the bus seam's (`seamBus_lvm`, MBL-STMT 2's `←`: no constraint, no boundary column). -/

/-- The typed phases' program at S2GL, unfolded. -/
theorem typedProgL_eq (Ti : TInst) (pub : Lvm.Pub) : typedProgL Ti pub =
    (zeroProgT >>= fun z ↦ wireProgT Ti pub z.2 >>= fun w ↦ relayProgT Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
      accProgT Ti.Q Ti.lay true (accYT pub) (accPtT pub) (z.1 ++ w.1) w.2.1 >>= fun _ ↦
        miniBusLProg Ti.mbT miniDepth >>= fun cl ↦ pure (typedClaimsL Ti w.1 w.2.2 r.1 r.2 cl)) := by
  rw [typedProgL]

/-- **The error side conditions in the phases' forms** (`TErrsT.factsT` without `ξ`). -/
theorem TErrsL.factsL {L₀ : ℕ} {I : M3Instance} {εmax T : ℝ≥0∞} (h : TErrsL L₀ I εmax T) :
    (L₀ : ℝ≥0∞) * errG gTau 1 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errG gOmega 2 + 0 ≤ εmax ∧
      (L₀ : ℝ≥0∞) * errG gZero 2 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errG gGamma 8 + 0 ≤ εmax ∧
      (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax ∧ errG gKappa 1 ≤ εmax ∧ errG gT phiVarsT ≤ εmax ∧
      abError I L₀ + 0 ≤ εmax ∧ abError I L₀ < 1 ∧ roundError L₀ 4 ≤ εmax ∧
      interpLead L₀ 2 (lambdaError L₀) ≤ εmax ∧ lambdaError L₀ + 0 ≤ εmax ∧ T ≤ εmax := by
  have hM1 : abError I L₀ + 0 ≤ leadMiniT L₀ I T := le_max_left _ _
  have hM3 : T ≤ leadMiniT L₀ I T := le_max_right _ _
  have hle : ∀ a : ℝ≥0∞, a ≤ a + leadMiniT L₀ I T := fun a ↦ le_self_add
  refine ⟨by rw [add_zero]; exact h.tau, by rw [add_zero]; exact h.omega,
    by rw [add_zero]; exact le_trans (by gcongr; exact errG_mono_c _ (by norm_num)) h.zero,
    by rw [add_zero]; exact h.gamma, by rw [add_zero]; exact h.wire, h.kappa, h.t, hM1.trans h.follow, h.ab.1,
    (hle _).trans (h.rounds 4 le_rfl), (hle _).trans h.lam.1, ?_, hM3.trans h.follow⟩
  rw [add_zero]; exact (hle _).trans h.lam.2

section Phases

variable (Ti : TInst) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ)
  (R : Column lay26.nuMain × Column lay26.nuRec → Prop)

/-- **The bus seam holds when the three claims do** (MBL-STMT 2's `←`; no constraint, no boundary column). -/
theorem seamBus_lvm (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hfix : FixOk Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hlin : mbLinB Ti.mbT = true) (b : LBus)
    (hb : b.alphas.length = 4 ∧ b.point.length = (inst lay26 Ti.mbT hτL).μBus ∧ b.values.length = 3)
    (qm : Column lay26.nuMain) (qr : Column lay26.nuRec)
    (hcl : ∀ c ∈ mbClaimsL CMain.nu20 Ti.mbT b, StackClaim.Holds lay26.nuMain c.onStack qm) :
    ((Lvm.M3.lbusStmt (inst lay26 Ti.mbT hτL) (Lvm.M3.condOf lay26 Ti.mbT hτL hsc) () b
        (Lvm.M3.vals0 lay26 Ti.mbT hτL), Lvm.M3.oraOf lay26 Ti.mbT hτL (stackOf lay26 qm qr)), ()) ∈
      Seam.bus (inst lay26 Ti.mbT hτL) := by
  refine ⟨fun j C hC ↦ ?_, (Lvm.M3.mbClaimsL_iff lay26 Ti.mbT hτL hsc hlay hfix hkey hlin b hb qm qr).mpr hcl,
    fun c hc ↦ ?_, Lvm.M3.publicLines_lvm lay26 Ti.mbT hτL _, fun r hr ↦ by simp [inst] at hr⟩
  · have h := List.all_eq_true.mp hlin _ (List.get_mem Ti.mbT j.1)
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    have hC' : C ∈ (Ti.mbT.get j.1).cons.map (Lvm.M3.CPoly.toMv _) := hC
    rw [h.1.1] at hC'
    exact absurd hC' List.not_mem_nil
  · have hl := Vector.length_toList (xs := (Lvm.M3.lbusStmt (inst lay26 Ti.mbT hτL)
      (Lvm.M3.condOf lay26 Ti.mbT hτL hsc) () b (Lvm.M3.vals0 lay26 Ti.mbT hτL)).2.columns)
    have hc' : c ∈ (Lvm.M3.lbusStmt (inst lay26 Ti.mbT hτL) (Lvm.M3.condOf lay26 Ti.mbT hτL hsc) () b
      (Lvm.M3.vals0 lay26 Ti.mbT hτL)).2.columns.toList := hc
    rw [List.eq_nil_of_length_eq_zero (hl.trans (Lvm.M3.busClaims_zero _ _ _))] at hc'
    exact absurd hc' List.not_mem_nil

/-- **The mini-bus at S2GL on a fixed candidate set** (`miniSpecT`'s twin): the bus phase (`lvmBusSpec4`), then the
three claims; from doom of the mini-bus relation to doom of the three claims on `C_main` (MBL-STMT 2). -/
noncomputable def miniSpecL {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column lay26.nuMain × Column lay26.nuRec))
    (hS : S.ncard ≤ L₀) (hfin : S.Finite) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hfix : FixOk Ti.mbT) (hlin : mbLinB Ti.mbT = true) (hμ : (inst lay26 Ti.mbT hτL).μBus = miniDepth)
    {T : ℝ≥0∞} (hab : abError (inst lay26 Ti.mbT hτL) L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) (hTf : T ≤ εmax)
    (w : List E2 × List E2 × List E2) (r : List E2 × E2) :
    Spec (miniBusLProg Ti.mbT miniDepth)
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
        (by rw [hμ]; norm_num) hab he4 hT hlam hTf).bind fun b ↦
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

/-- **The typed phases at S2GL on a fixed candidate set** (`typedSpecInT`'s twin with `miniSpecL`). -/
noncomputable def typedSpecInL {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column lay26.nuMain × Column lay26.nuRec))
    (hS : S.ncard ≤ L₀) (hTi : Ti.Ok) (hmaps : Ti.MapsFit lay26) (hrec : lay26.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hfix : FixOk Ti.mbT) (hlin : mbLinB Ti.mbT = true) (hμ : (inst lay26 Ti.mbT hτL).μBus = miniDepth)
    (hfin : S.Finite) {T : ℝ≥0∞} (herr : TErrsL L₀ (inst lay26 Ti.mbT hτL) εmax T) :
    Spec (typedProgL Ti pub)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ TGoodT Ti lay26 hτL pub p ∧ R p ∧ AccOkTT Ti pub) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold lay26 out p ∧ R p) h) εmax 0 T := by
  obtain ⟨hτ, hω, hz, hγ, hwr, hκ, ht, hab0, hab, he4, hTl, hlam, hTf⟩ := herr.factsL
  have hst : Stable (fun _ : List Ev ↦ S) := fun _ _ _ ↦ rfl
  have hcard : ∀ h : List Ev, ((fun _ : List Ev ↦ S) h).ncard ≤ L₀ := fun _ ↦ hS
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  rw [typedProgL_eq]
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
  refine ((miniSpecL Ti pub hτL R S hS hfin hsc hlay hkey hfix hlin hμ hab he4 hTl hlam hTf w r).mono
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

end Phases

/-- **The typed phases at S2GL** (`typedSpecGT`'s twin at `lay26`, glued over the candidate sets). -/
noncomputable def typedSpecGL (Ti : TInst) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit lay26) (hrec : lay26.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hfix : FixOk Ti.mbT) (hlin : mbLinB Ti.mbT = true) (hμ : (inst lay26 Ti.mbT hτL).μBus = miniDepth)
    (C : List Ev → Set (Column lay26.nuMain × Column lay26.nuRec)) (R : Column lay26.nuMain × Column lay26.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrsL L₀ (inst lay26 Ti.mbT hτL) εmax T) :
    Spec (typedProgL Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGoodT Ti lay26 hτL pub p ∧ R p ∧ AccOkTT Ti pub) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold lay26 out p ∧ R p) h) εmax 0 T :=
  (Lvm.M3.Spec.glue (ι := {S : Set (Column lay26.nuMain × Column lay26.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecInL Ti pub hτL R S.1 S.2.2 hTi hmaps hrec hacc hsc hlay hkey hfix hlin hμ S.2.1 herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

/-- **The typed phases at S2GL on the viewed pinned pairs** (`specBusGT`'s twin). -/
noncomputable def specBusGL {Ti : TInst} (H : THypL Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) (x : List UInt8) (Gk N : Lvm.ASM.Pair → Prop) :
    Spec (typedProgL Ti (pubXT x))
      (fun h ↦ Lvm.E2F.PinPost za h ∧
        Doomed (Lvm.E2F.candRelZ recOf za x)
          (fun p ↦ GbTB Ti H.hτ x (Lvm.Shape.vp x p) ∧ (Gk (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p))) h)
      (fun a h ↦ Doomed (Lvm.E2F.candRelZ recOf za x)
        (fun p ↦ (BT x a (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p)) ∧
          (Gk (Lvm.Shape.vp x p) ∧ N (Lvm.Shape.vp x p))) h ∧ Lvm.E2F.PinPost za h)
      εS leadF₂ 0 :=
  have S0 := typedSpecGL Ti (pubXT x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.fix H.lin (H.μBus H.hτ)
    (imgCZ recOf za x) (fun p ↦ Lvm.ASM.BndS x p.1 ∧ Gk p ∧ N p) (L₀ := 1) (εmax := εS) (T := 0)
    (fun h ↦ 1 ≤ (commits h).length) (imgCZ_append recOf za x) (fun _ ↦ Set.toFinite _)
    (imgCZ_ncard_le_one recOf za x) (H.errs H.hτ)
  (S0.frame (Lvm.E2F.PinPost za) (fun _ _ hl hr ↦ pinPost_append za
      ((noCG_typedProgL Ti (pubXT x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.Typed.rootShapeM_one hr.1, Lvm.Typed.rootShapeM_firstWord hr.1,
      doomed_imgCZ.mpr (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCZ.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩,
      hp.2⟩)
    le_rfl zero_le le_rfl

/-- **MBL-STMT 4** (owner L): **the pinned pair form of S2GL's middle phases** (`midSpecP_GU`'s twin): for every pin
`za`, from `PinPost za` to `OpenPostRG` over `candRelZ recOf za`, every group `≤ εS`, lead `leadF₂`, followers'
lead `τU` (S2GU's front, unchanged). Through MBL-STMT 2: the bus seam's doom is the three claims' doom. -/
theorem midSpecP_GL (Ti : TInst) (H : THypL Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) :
    Lvm.ASM.MidSpecPτ (midGL Ti) (Lvm.E2F.candRelZ recOf za) (Lvm.E2F.PinPost za)
      (Lvm.Shape.Good₂ (GoodTL Ti H)) εS leadF₂ τU := by
  have hcb : 1 ≤ bL ∧ bL < 8080 := by norm_num
  have hS : E2V.SplitSound := fun nu c hc q h ↦ splitE2_sound nu c hc q h
  have hA : E2V.SplitAffine := fun nu c hc ↦ isMultiaffine_splitE2 nu c hc
  have h7 : (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) ≤ εS := by
    simpa using E2V.sum7_le_εS
  exact Lvm.ASM.midSpecOfRelGτ (busP := fun x ↦ typedProgL Ti (pubXT x))
    (kgP := fun x ↦ tapeProgB bL (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleU₂ x a k) (Lb := leadF₂) (Lk := 0)
    (Gb := fun x p ↦ GbTB Ti H.hτ x (Lvm.Shape.vp x p)) (Gk := fun x p ↦ GkB bL x (Lvm.Shape.vp x p))
    (B := fun x a p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p))
    (Kc := fun x k p ↦ KcU (Lvm.NS.colM (Lvm.Shape.vp x p).1) k)
    (Qa := fun _ a ↦ (∀ c ∈ a.1, LeanVM.Protocol.Whir.Sound.IsMultiaffine 19 c.1) ∧
      (∀ c ∈ a.2, LeanVM.Protocol.Whir.Sound.IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39)
    (Qk := fun _ ↦ KgRetU) (C := Lvm.E2F.candRelZ recOf za) (Sh := Lvm.E2F.PinPost za)
    (fun _ _ hl hr ↦ E2V.pinPost_append za hl hr)
    (fun x ↦ specBusGL H recOf za x (GkB bL x) fun p ↦ ¬ (GbTB Ti H.hτ x p ∧ GkB bL x p))
    (fun x ↦ retOK_typedProgL Ti H (pubXT x))
    (fun x a T hT ↦ (tapeSpecBW hcb (E2V.candRelZ_stable recOf za x) (E2V.candRelZ_ncard_le recOf za x)
        (hdX x).s (n := (pubX x).n) (fun p ↦ Lvm.NS.colM (Lvm.Shape.vp x p).1)
        (fun p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p) ∧
          ¬ (GbTB Ti H.hτ x (Lvm.Shape.vp x p) ∧ GkB bL x (Lvm.Shape.vp x p)))
        (calc (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) + T
            ≤ (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) +
                (εS - ∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) := add_le_add le_rfl hT
          _ = εS := add_tsub_cancel_of_le h7)).mono
      (fun _ hd ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hd fun p ⟨ht, hb, hn⟩ ↦
        ⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hn⟩, hb, hn⟩)
      (fun _ _ hp ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hp.2.2.2 fun p ⟨⟨h1, h2, h3, h4, h5⟩, hR⟩ ↦
        ⟨h1, h2, h3, h4, h5, hR⟩) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_tapeProgB _ _ _) (fun _ ↦ cg_tapeProgB _ _ _)
    (fun x a k p _ hk h1 h2 ↦ linkU hS x a k p hk h1 h2)
    (fun x a k ha hk ↦ sideU hA x a k ha hk)

/-- **MBL-STMT 4b** (owner L): **the middle phases' claims are fewer than `2^40`** (`retOK_midGU_len`'s twin). -/
theorem retOK_midGL_len (Ti : TInst) (H : THypL Ti) (x : List UInt8) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (midGL Ti x) := by
  refine (retOK_typedProgL Ti H (pubXT x)).bind fun a ha ↦
    LeanVM.Protocol.EndToEnd.Sound.RetOK.bind_true fun k ↦ LeanVM.Protocol.EndToEnd.Sound.RetOK.ret ?_
  have hz : ∀ l : List VStackClaim, (Lvm.Shape.onStackZs x l).length = l.length := fun l ↦ by
    unfold Lvm.Shape.onStackZs
    split_ifs <;> simp only [List.length_map]
  simp only [assembleU₂, hz, List.length_append, List.length_map, length_tapeClaimsU]
  have := ha.2.2
  omega

/-- **MBL-STMT 4c** (owner L): **S2GL's middle phases commit nothing and ask no proof of work**. -/
theorem cg_midGL (Ti : TInst) (x : List UInt8) : Lvm.M3.NoCG (midGL Ti x) :=
  Lvm.M3.NoCG.bind (noCG_typedProgL Ti _) fun _ ↦ Lvm.M3.NoCG.bind (cg_tapeProgB _ _ _) fun _ ↦ Lvm.M3.cg_ret _

/-! ## The `KS` bridge at S2GL (RE-FREEZE R1: S2GU's UTAPE-STMT 10–14 at `bL`; for MBL-C's `nodeL20`) -/

section Bridge

open Lvm.KG Lvm.NS Lvm.QSig Lvm.Replay Lvm.QLink

/-- **MBL-STMT 10** (owner L): the literal is the S2GL trace's sponge-block count less one. -/
theorem bL_eq : spongeBlocks P20L = bL + 1 := sizes_P20L.1.2.2.2.2.1

/-- **MBL-STMT 12** (owner L): **the sponge half is a sponge table** at S2GL (`spongeRel_of_GkU` at `bL`). -/
theorem spongeRel_of_GkL {x : List UInt8} {p : Column CMain.nu20 × Column 19} (hG : GkB bL x p) :
    SpongeRel 13 (ksVirt 13 (YqU p.1) (MqU p.1) (contB bL)) (YqU p.1) (MqU p.1) (contB bL) :=
  spongeRel_of_GkB hG

/-- **MBL-STMT 13** (owner L): **the sponge half outputs the child's trace digest** at row `bL` (`traceDigest_of_GkU`
at S2GL: the child trace is `P20L`'s). -/
theorem traceDigest_of_GkL {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GkB bL x (qm, qr)) (hS : SBlkU qm qr) (hL : LaneLink P20L (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P20L)) :
    Lvm.KSponge.stDigest (yState (YqU qm) (spongeBlocks P20L - 1)) =
      traceDigest (Lvm.QLink.decode P20L (wsOf (Lvm.X.laneOf (wOfCol qr)))) :=
  traceDigest_of_GkB Lvm.E2Q.streamOk_P20L bL_eq
    (by rw [sizes_P20L.1.2.2.2.2.1, sizes_P20L.1.2.2.1]; rfl) (by rw [sizes_P20L.1.2.2.2.2.1]; norm_num) hG hS hL hpad

/-- **MBL-STMT 14** (owner L): **Q_sig's `KS` hypothesis at S2GL** (`sigKSin_of_GkU` at `bL`). -/
theorem sigKSin_of_GkL {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} {I : SigIn} {v : ℕ → FK}
    (hG : GkB bL x (qm, qr))
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 430 + t) l))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 447) l))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 448) l)) :
    SigKSin I v :=
  sigKSin_of_GkB (by norm_num) hG hx hys hyc hyls hyns

end Bridge

end Lvm.E2L
