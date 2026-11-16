-- New for lvm2 slice S1 (E2-F, E2F-LEAD freeze 2026-11-13): M′'s certificate with the root pin (statement 17 of
-- E2AC-DES §6, generic in the middle phases). Definitions are final; the `sorry`s are frozen statements (owner:
-- E2F-LEAD). A proof never changes its statement; a needed change is reported old → new.
import LvmE2FPin

/-!
# The pinned certificate (statement 17; statement 18's frame)

S1 changes nothing behind the middle phases: `P_S` is M′'s `PSWithM` at the pinned middle phases `midP mid`
(the pin's claim first in the list), so M′'s whole certificate (`psInvM`, `extJM`, `kcertSM`, `εFS_kcertSM`,
`OpenSM`, `sSound_of_openSM`) is reused unchanged. What S1 proves is the middle phases' obligation at `candZ`
(`MidSpecPin`: the front at `E2` with grinding, `L₀ = 1`), and the pin's composition with it:

* **`midSpecP_of`** (17): `MidSpecPin mid` (lead `Lm`) ⇒ M′'s `MidSpecM (midP mid)` (lead `errE pinNum + Lm`);
* **`midShapeP_of`**: the pin commits and grinds nothing;
* **`kcertSF`**, **`εFS_kcertSF`** (`≤ 2^-128`, `εS = 7·2^-131` kept);
* **`openSF`** (the frame of statement 18): an `OpenSM` from the S1 obligations. The instance at `P20`
  (`midF20`, `VSF20`, `childF20`, `refinesF20`, `ext_eqF20`, `certificateF20`, `sizes_P20F`) is frozen in
  `LvmCertF20` once the helpers' S2GF names exist (E2F-V: `VSF20`, the schedule `P20F`; E2F-Q: `nodeF20`).
-/

set_option autoImplicit false

namespace Lvm.E2F

open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
  {Lm : ℝ≥0∞}

/-- The pinned middle phases' lead. -/
noncomputable abbrev leadP (Lm : ℝ≥0∞) : ℝ≥0∞ := LeanVM.Protocol.KeccakGkr.errE pinNum + Lm

/-- `NoCommit.bind` in `>>=` form: `refine` matches `midP`'s binds syntactically (against `NoCommit.bind`'s
`p.bind f` the unifier unfolds the programs and times out). -/
private theorem nc_bind' {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.NoCommit)
    (hf : ∀ a, (f a).NoCommit) : (p >>= f).NoCommit :=
  VerifierProgram.NoCommit.bind hp hf

/-- `NoGrind.bind` in `>>=` form (as `nc_bind'`). -/
private theorem ng_bind' {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.NoGrind)
    (hf : ∀ a, (f a).NoGrind) : (p >>= f).NoGrind :=
  VerifierProgram.NoGrind.bind hp hf

/-- **Statement 17 (`midSpecP_of`)**: the pin (`pin_escape`), the `Stable` invariant (`pinOut_append`) and the
middle phases at `candZ` give M′'s obligation for the pinned middle phases. -/
theorem midSpecP_ofτ {τ : ℝ≥0∞} (hm : MidSpecPinτ mid Good εS Lm τ) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS) :
    MidSpecMτ (midP mid) Good εS (leadP Lm) τ := fun x T hT ↦
  ⟨(pin_escape Lm (le_add_self.trans hL)).some.bind' fun za ↦
    ((((hm x za T hT).some.frame (PinOut za) fun _ l hl hI ↦
        pinOut_append l ((hsh.noCommit x).reach_commits hl) hI).bind' fun cl ↦
      (Spec.ret (Post := OpenPostM Good x) (pinClaim za :: cl)).mono
        (fun _ h ↦ openPostP_of h.2 h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ h ↦ ⟨h, pinOut_of_post h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)⟩

theorem midSpecP_of (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS) :
    MidSpecM (midP mid) Good εS (leadP Lm) :=
  midSpecP_ofτ hm hsh hL

/-- The pin commits nothing and grinds nothing. -/
theorem midShapeP_of (hsh : MidShapeM mid) : MidShapeM (midP mid) where
  noCommit x := by
    unfold midP pinProg
    refine nc_bind' ?_ ?_
    · refine nc_bind' ?_ ?_
      · exact nc_sampleChallengesN _
      · intro _
        refine nc_bind' ?_ ?_
        · exact nc_readScalar
        · intro _; exact nc_ret _
    · intro _
      refine nc_bind' ?_ ?_
      · exact hsh.noCommit x
      · intro _; exact nc_ret _
  noGrind x := by
    unfold midP pinProg
    refine ng_bind' ?_ ?_
    · refine ng_bind' ?_ ?_
      · exact ng_sampleChallengesN _
      · intro _
        refine ng_bind' ?_ ?_
        · exact ng_readScalar
        · intro _; exact ng_ret _
    · intro _
      refine ng_bind' ?_ ?_
      · exact hsh.noGrind x
      · intro _; exact ng_ret _

/-- **The knowledge certificate of S1's `S` branch**: M′'s `kcertSM` at the pinned middle phases. -/
noncomputable def kcertSF (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS)
    {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    KCert (schemeS vk (PSWithM (midP mid))) (Rel (accV VS vk)) :=
  kcertSM (midSpecP_of hm hsh hL) hL (midShapeP_of hsh) X

/-- **Its error**: `εFS ≤ 2^-128` (`εS = 7·2^-131`, luck `2^-132`, hash `2^-139`, as M′). -/
theorem εFS_kcertSF (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS)
    {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    Scheme.εFS (kcertSF hm hsh hL X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  εFS_kcertSM _ _ _ X

/-- **S1's open obligations** (the frame of statement 18): the middle phases at `candZ`, the node's soundness, the
refinement of `V_S` to the pinned `P_S`, the executable extractor on good logs. -/
structure OpenSF (VS : SProg) (E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  hmid : MidSpecPin mid Good εS Lm
  hsh : MidShapeM mid
  hL : leadP Lm ≤ εS
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWithM (midP mid))).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSF hmid hsh hL (extJM (midShapeP_of hsh) (hnode vk))) L < 1 →
    ((schemeS vk (PSWithM (midP mid))).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWithM (midP mid))).Ex
        (kcertSF hmid hsh hL (extJM (midShapeP_of hsh) (hnode vk))).ext c π L

/-- **`OpenSF` is M′'s `OpenSM` at the pinned middle phases.** -/
noncomputable def openSF {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit} (o : OpenSF VS E) :
    OpenSM VS E where
  mid := midP o.mid
  Good := o.Good
  Lm := leadP o.Lm
  hmid := midSpecP_of o.hmid o.hsh o.hL
  hLm := o.hL
  hsh := midShapeP_of o.hsh
  child := o.child
  hnode := o.hnode
  refines := o.refines
  ext_eq := o.ext_eq

/-- **`SSound` from S1's open obligations.** -/
theorem sSound_of_openSF {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit} (o : OpenSF VS E)
    (vk : RecursionFast.Digest) : SSound VS E vk :=
  sSound_of_openSM (openSF o) vk

/-- **The pin's escape fits under `2^-131`** (`C(124,2)·23 = 175,398 ≤ 2^61`). -/
theorem errE_pinNum_le : LeanVM.Protocol.KeccakGkr.errE pinNum ≤ (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  have hd : (pinNum : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 61 := by
    have : pinNum ≤ 2 ^ 61 := by rw [pinNum, Nat.choose_two_right]; norm_num
    exact_mod_cast this
  unfold LeanVM.Protocol.KeccakGkr.errE
  rw [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat]
  calc (pinNum : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ≤ (2 : ℝ≥0∞) ^ 61 * ((2 : ℝ≥0∞) ^ 192)⁻¹ := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ 131 := by
      rw [show (192 : ℕ) = 61 + 131 from rfl, pow_add,
        ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
        ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
        one_mul, ENNReal.inv_pow]

/-- **The pinned lead at the middle phases' `6·2^-131`** (V's `leadF₂`) is within `εS = 7·2^-131`. -/
theorem leadP_six : leadP (6 * (2 : ℝ≥0∞)⁻¹ ^ 131) ≤ εS :=
  calc leadP (6 * (2 : ℝ≥0∞)⁻¹ ^ 131) ≤ (2 : ℝ≥0∞)⁻¹ ^ 131 + 6 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
        unfold leadP; gcongr; exact errE_pinNum_le
    _ = εS := by unfold εS; ring

/-! ## The pin-aware bridge from the pair form (the twin of `midSpecM_of`) -/

section PinBridge

variable {recOf : List UInt8 → LeanVM.Protocol.Column CMain.nu20 → LeanVM.Protocol.Column 19}
  {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}

/-- **The pinned one-root candidate pairs**: `candZ`'s members with their `C_rec` column (at most one pair). -/
def candRelZ (recOf : List UInt8 → LeanVM.Protocol.Column CMain.nu20 → LeanVM.Protocol.Column 19)
    (za : List E × E) (x : List UInt8) (h : List Ev) : Set Pair :=
  (fun q ↦ (q, recOf x q)) '' candZ za h

/-- **`MidPostZ` from the pair form** (as `openPostM_of`): a non-good member `q` of `candZ` is the pair
`(q, recOf x q)`, which fails a `C_main` claim or a `C_rec` claim, whose relocation fails on `q`. -/
theorem midPostZ_of (k : ℕ) (hρ : RelocLaw recOf reloc) {G : GoodRel} {x : List UInt8} {za : List E × E}
    {cl : OpenClaims} {h : List Ev}
    (hp : OpenPostRG (candRelZ recOf za x) (PinPost za) G x cl h) (hl : cl.2.length + cl.1.length < 2 ^ 40) :
    MidPostZ (GoodOfM recOf G) x za (ordMk k (cl.1.map (reloc x)) cl.2) h := by
  have hP := perm_ordMk k (cl.1.map (reloc x)) cl.2
  obtain ⟨hc, hR, hm1, hm2, -⟩ := hp
  refine ⟨fun q hq hng ↦ ?_, hR.1, fun c hc' ↦ ?_, by rw [hP.length_eq]; simpa using hl⟩
  · rcases hc (q, recOf x q) ⟨q, hq, rfl⟩ hng with ⟨c, hc1, hn⟩ | ⟨c, hc2, hn⟩
    · exact ⟨reloc x c, hP.mem_iff.mpr (List.mem_append_right _ (List.mem_map_of_mem hc1)),
        fun hh ↦ hn (hρ.holds x c q (hm1 c hc1) hh)⟩
    · exact ⟨c, hP.mem_iff.mpr (List.mem_append_left _ hc2), hn⟩
  · rcases List.mem_append.mp (hP.mem_iff.mp hc') with hc' | hc'
    · exact hm2 c hc'
    · obtain ⟨c', hc1, rfl⟩ := List.mem_map.mp hc'
      exact hρ.affine x c' (hm1 c' hc1)

/-- **`MidSpecPin` from the pair form** at the pinned pairs `candRelZ recOf za` (from `PinPost za`, for every
pin `za`), with fewer than `2^40` claims in all (the pin's claim makes the list's `≤ 2^40`). -/
theorem midSpecPinMk_ofτ (k : ℕ) (hρ : RelocLaw recOf reloc) {mid : List UInt8 → VerifierProgram OpenClaims}
    {G : GoodRel} {εm Lm τ : ℝ≥0∞} (hP : ∀ za, MidSpecPτ mid (candRelZ recOf za) (PinPost za) G εm Lm τ)
    (hlen : ∀ x, LeanVM.Protocol.EndToEnd.Sound.RetOK
      (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (mid x)) :
    MidSpecPinτ (midMk k reloc mid) (GoodOfM recOf G) εm Lm τ := fun x za T hT ↦
  (hP za x T hT).map fun S ↦
    (Lvm.KG.specWithRet S (hlen x)).bind' fun cl ↦
      (Spec.ret (Post := MidPostZ (GoodOfM recOf G) x za) (εmax := εm) (T := T)
          (ordMk k (cl.1.map (reloc x)) cl.2)).mono
        (fun _ hp ↦ midPostZ_of k hρ hp.2 hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **`MidSpecPin` from the pair form** (`midSpecPinMk_ofτ` at `τ = εm`). -/
theorem midSpecPinMk_of (k : ℕ) (hρ : RelocLaw recOf reloc) {mid : List UInt8 → VerifierProgram OpenClaims}
    {G : GoodRel} {εm Lm : ℝ≥0∞} (hP : ∀ za, MidSpecP mid (candRelZ recOf za) (PinPost za) G εm Lm)
    (hlen : ∀ x, LeanVM.Protocol.EndToEnd.Sound.RetOK
      (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (mid x)) :
    MidSpecPin (midMk k reloc mid) (GoodOfM recOf G) εm Lm :=
  midSpecPinMk_ofτ k hρ hP hlen

/-- **`MidSpecPin` from the pair form** (`midSpecPinMk_of` at `midM = midMk 2`). -/
theorem midSpecPin_of (hρ : RelocLaw recOf reloc) {mid : List UInt8 → VerifierProgram OpenClaims} {G : GoodRel}
    {εm Lm : ℝ≥0∞} (hP : ∀ za, MidSpecP mid (candRelZ recOf za) (PinPost za) G εm Lm)
    (hlen : ∀ x, LeanVM.Protocol.EndToEnd.Sound.RetOK
      (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (mid x)) :
    MidSpecPin (midM reloc mid) (GoodOfM recOf G) εm Lm :=
  midSpecPinMk_of 2 hρ hP hlen

end PinBridge

/-! ## Stage formats (S2GF, S2GT): the forms at `schemeSW f` -/

section W

variable (f : SFmt)

/-- **`kcertSF` at a format `f`.** -/
noncomputable def kcertSFWτ {τ : ℝ≥0∞} (hm : MidSpecPinτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hsh : MidShapeM mid)
    (hL : leadP Lm ≤ εS) {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    KCert (schemeSW f vk (PSWithM (midP mid))) (Rel (accV VS vk)) :=
  kcertSMWτ f (midSpecP_ofτ hm hsh hL) hτ hL (midShapeP_of hsh) X

noncomputable def kcertSFW (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS)
    {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    KCert (schemeSW f vk (PSWithM (midP mid))) (Rel (accV VS vk)) :=
  kcertSFWτ f hm leadOpenM_le_εS hsh hL X

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSFWτ {τ : ℝ≥0∞} (hm : MidSpecPinτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hsh : MidShapeM mid)
    (hL : leadP Lm ≤ εS) {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    Scheme.εFS (kcertSFWτ f hm hτ hsh hL X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  εFS_kcertSMWτ f _ _ _ _ X

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSFW (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS)
    {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    Scheme.εFS (kcertSFW f hm hsh hL X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  εFS_kcertSFWτ f _ _ _ _ X

/-- **S1's open obligations at a format `f`** (`OpenSF` with `schemeSW f`). -/
structure OpenSFW (VS : SProg) (E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  /-- The middle phases' followers' lead bound (U-A3; `εS` unless given). -/
  τ : ℝ≥0∞ := εS
  hτ : leadOpenM ≤ τ := by exact leadOpenM_le_εS
  hmid : MidSpecPinτ mid Good εS Lm τ
  hsh : MidShapeM mid
  hL : leadP Lm ≤ εS
  child : List UInt8 → List BF64 → Signed
  /-- The window's first lane per statement (D-WIN (B); `winLo` unless given). -/
  lo : List UInt8 → ℕ := fun _ ↦ Lvm.X.winLo
  hlo : ∀ x, lo x + Lvm.X.winC ≤ 64 := by intro; decide
  hnode : ∀ vk, NodeSoundML lo VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeSW f vk (PSWithM (midP mid))).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSFWτ f hmid hτ hsh hL (extJML lo hlo (midShapeP_of hsh) (hnode vk))) L < 1 →
    ((schemeSW f vk (PSWithM (midP mid))).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeSW f vk (PSWithM (midP mid))).Ex
        (kcertSFWτ f hmid hτ hsh hL (extJML lo hlo (midShapeP_of hsh) (hnode vk))).ext c π L

/-- **`OpenSFW` is M′'s `OpenSMW` at the pinned middle phases.** -/
noncomputable def openSFW {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit}
    (o : OpenSFW f VS E) : OpenSMW f VS E where
  mid := midP o.mid
  Good := o.Good
  Lm := leadP o.Lm
  τ := o.τ
  hτ := o.hτ
  hmid := midSpecP_ofτ o.hmid o.hsh o.hL
  hLm := o.hL
  hsh := midShapeP_of o.hsh
  child := o.child
  lo := o.lo
  hlo := o.hlo
  hnode := o.hnode
  refines := o.refines
  ext_eq := o.ext_eq

/-- **`SSound` from S1's open obligations at a format `f`.** -/
theorem sSound_of_openSFW {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit}
    (o : OpenSFW f VS E) (vk : RecursionFast.Digest) : SSound VS E vk :=
  sSound_of_openSMW f (openSFW f o) vk

end W

end Lvm.E2F
