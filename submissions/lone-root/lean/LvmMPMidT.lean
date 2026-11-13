-- New for lvm2 roll 11 (M′, R11-I): the typed backend's middle phases at M′ (`midM reloc (midT₂ Ti)`):
-- `MidSpecM` and `MidShapeM` from the existing phase specs re-instantiated at the one-root candidate pairs
-- (`LvmMPMid.candRelM`). The relocation's laws stay hypotheses (`RelocLaw`, the lead's from R11-E's layout).
import LvmMPMid
import LvmTypedSpec

/-!
# The typed middle phases at M′

`midSpecR_T₂`'s proof (`LvmTypedSpec`) with the candidate set `candPairs` (two roots) replaced by
`candRelM recOf x` (`C_main`'s candidates with their `C_rec` column `recOf x q`) and `RootShape` by
`RootShapeM`:

* **`specBusTM`**: `typedSpecR` at `imgCM recOf x` (the viewed one-root pairs), as `specBusT₂`;
  **`specKgSM`**: `kgSpecS` at `candRelM recOf x`, as `LvmShape.specKgS₂`;
* **`midSpecP_T₂`**: `midSpecOfRelG` with `linkT₂`/`sideT₂` unchanged;
* **`retOK_midT₂_len`**: at most `2^40` claims in all (the typed phases `≤ 2^39 + 4`, V_S phases 4–7 `≤ 41`);
* **`midSpecM_T₂`**, **`midShapeM_T₂`**, **`kcertTM`** (`kcertSM` at `GoodTM`).

The error terms are those of `THyp.errs`/`kg_errsJ2` at `L₀ = 37,696`: the one-root pairs number at most
`124 ≤ 37,696` (`candidates_main23Jq_ncard_le`), so no new arithmetic is needed (`εS`, lead `εS`).
-/

set_option autoImplicit false

namespace Lvm.Typed

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal

/-! ## One root -/

theorem rootShapeM_append {h₀ l : List Ev} (hl : commits l = []) (hr : RootShapeM h₀) :
    RootShapeM (h₀ ++ l) := by
  obtain ⟨W, hc, hw⟩ := hr
  exact ⟨W, by rw [commits_append, hl, List.append_nil, hc], hw⟩

theorem rootShapeM_one {h : List Ev} (hr : RootShapeM h) : 1 ≤ (commits h).length := by
  obtain ⟨W, hc, -⟩ := hr; rw [hc]; simp

theorem rootShapeM_firstWord {h : List Ev} (hr : RootShapeM h) : ∃ W, firstWord h = some W := by
  obtain ⟨W, hc, -⟩ := hr
  exact ⟨W, by simp [firstWord, hc]⟩

theorem candM_append (h₀ l : List Ev) (h1 : 1 ≤ (commits h₀).length) : candM (h₀ ++ l) = candM h₀ := by
  simp only [candM, Lvm.M3.wordOf_commits_append h₀ l (show 0 < (commits h₀).length by omega)]

theorem candM_stable : Stable candM := fun h₀ l hl ↦ by
  simp only [candM, commits_append, hl, List.append_nil]

theorem candRelM_stable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) :
    Stable (candRelM recOf x) := fun h₀ l hl ↦ by
  rw [candRelM, candRelM, candM_stable h₀ l hl]

/-- `C_main`'s root candidates are at most `124`. -/
theorem candM_ncard_le (h : List Ev) : (candM h).ncard ≤ 124 :=
  candidates_main23Jq_ncard_le _

theorem candRelM_ncard_le (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) (h : List Ev) :
    (candRelM recOf x h).ncard ≤ 124 :=
  (Set.ncard_image_le (Set.toFinite _)).trans (candM_ncard_le h)

/-- The viewed one-root pairs. -/
def imgCM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) (h : List Ev) : Set Pair :=
  vp x '' candRelM recOf x h

section Img

variable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8)

theorem imgCM_append (h₀ l : List Ev) (h1 : 1 ≤ (commits h₀).length) :
    imgCM recOf x (h₀ ++ l) = imgCM recOf x h₀ := by
  rw [imgCM, imgCM, candRelM, candRelM, candM_append h₀ l h1]

theorem imgCM_ncard_le (h : List Ev) : (imgCM recOf x h).ncard ≤ 37696 :=
  (Set.ncard_image_le (Set.toFinite _)).trans ((candRelM_ncard_le recOf x h).trans (by norm_num))

variable {recOf x}

theorem doomed_imgCM {A : Pair → Prop} {h : List Ev} :
    Doomed (imgCM recOf x) A h ↔ Doomed (candRelM recOf x) (fun p ↦ A (vp x p)) h :=
  ⟨fun hd p hp ↦ hd _ ⟨p, hp, rfl⟩, fun hd _ ⟨p, hp, e⟩ ↦ e ▸ hd p hp⟩

end Img

/-! ## The phases at the one-root pairs -/

variable {Ti : TInst}

/-- **The typed phases on the viewed one-root pairs** (`specBusT₂` with `imgCM`, `RootShapeM`). -/
noncomputable def specBusTM (H : THyp Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (x : List UInt8) (N : Pair → Prop) :
    Spec (typedProg Ti (pubX x))
      (fun h ↦ RootShapeM h ∧
        Doomed (candRelM recOf x) (fun p ↦ GbT Ti H x (vp x p) ∧ (GkS x (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed (candRelM recOf x)
        (fun p ↦ (BT x a (vp x p) ∧ N (vp x p)) ∧ (GkS x (vp x p) ∧ N (vp x p))) h ∧ RootShapeM h)
      εS εS LkSJ :=
  have S0 := typedSpecR Ti lay26 (pubX x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.width H.fix
    (H.μBus H.hτ) (imgCM recOf x)
    (fun p ↦ BndS x p.1 ∧ GkS x p ∧ N p) (L₀ := 37696) (εmax := εS) (T := LkSJ)
    (fun h ↦ 1 ≤ (commits h).length) (imgCM_append recOf x) (fun _ ↦ Set.toFinite _)
    (imgCM_ncard_le recOf x) (H.errs H.hτ)
  (S0.frame RootShapeM (fun _ _ hl hr ↦ rootShapeM_append
      ((cg_typedProg Ti (pubX x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨rootShapeM_one hr, rootShapeM_firstWord hr, doomed_imgCM.mpr
      (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCM.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩, hp.2⟩)
    le_rfl (H.errs H.hτ).lead le_rfl

/-- **Phases 4–7 on the viewed one-root pairs** (`LvmShape.specKgS₂` with `candRelM`). -/
noncomputable def specKgSM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8)
    (R : Pair → Prop) (T : ℝ≥0∞) (hT : T ≤ εS) :
    Spec (kgProgS (hdX x).s (pubX x).n) (Doomed (candRelM recOf x) (fun p ↦ GkS x (vp x p) ∧ R p))
      (fun k h ↦ Doomed (candRelM recOf x) (fun p ↦ KcS k (vp x p) ∧ R p) h) εS LkSJ T :=
  have e := Lvm.ASM.kg_errsJ2
  have s := Lvm.ASM.kg_struct
  (Lvm.ASM.kgSpecS (C := candRelM recOf x) (L₀ := 37696) (εmax := εS) (T := T) (candRelM_stable recOf x)
    (fun h ↦ (candRelM_ncard_le recOf x h).trans (by norm_num))
    (hdX x).s (pubX x).n 9 9 ksY2 (by norm_num) (Lvm.contRows Lvm.P20) s.2.2.1 s.2.2.2
    (fun q ↦ colM (vp x q).1) (fun q ↦ colM (vp x q).1) (fun q ↦ ksCol (vp x q).1) (fun q ↦ msgM q.2)
    (fun q ↦ msgX (vp x q).1) R e.1 e.2.1 e.2.2.1 e.2.2.2.1 hT).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨ht, hk, hb⟩ ↦
      ⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hk⟩, hb⟩)
    (fun _ _ hp ↦ Doomed.mono hp.2 fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩) le_rfl le_rfl le_rfl

/-- **The pair form of the typed middle phases at the one-root pairs** (`midSpecR_T₂`'s proof through
`midSpecOfRelG`; `linkT₂`, `sideT₂`, `retOK_typedProg` unchanged). -/
theorem midSpecP_T₂ (H : THyp Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19) :
    MidSpecP (midT₂ Ti) (candRelM recOf) RootShapeM (Good₂ (GoodT Ti H)) εS εS :=
  midSpecOfRelG (busP := fun x ↦ typedProg Ti (pubX x)) (kgP := fun x ↦ kgProgS (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleT₂ x a k) (Lb := εS) (Lk := LkSJ)
    (Gb := fun x p ↦ GbT Ti H x (vp x p)) (Gk := fun x p ↦ GkS x (vp x p))
    (B := fun x a p ↦ BT x a (vp x p)) (Kc := fun x k p ↦ KcS k (vp x p))
    (Qa := fun _ ↦ TRet) (Qk := fun _ ↦ KgRet) (C := candRelM recOf) (Sh := RootShapeM)
    (fun _ _ hl hr ↦ rootShapeM_append hl hr)
    (fun x ↦ specBusTM H recOf x fun p ↦ ¬ (GbT Ti H x p ∧ GkS x p))
    (fun _ ↦ retOK_typedProg H _)
    (fun x a T hT ↦ (specKgSM recOf x
        (fun p ↦ BT x a (vp x p) ∧ ¬ (GbT Ti H x (vp x p) ∧ GkS x (vp x p))) T hT).mono
      (fun _ hd ↦ Doomed.mono hd fun _ hq ↦ ⟨⟨hq.1, hq.2.2⟩, hq.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_kgProgS _ _) (fun _ ↦ cg_kgProgS _ _)
    (fun x a k p ha hk h1 h2 ↦ linkT₂ x a k p ha hk h1 h2)
    (fun x a k ha hk ↦ sideT₂ x a k ha hk)

/-! ## The claims' count -/

/-- The typed phases return at most `2^39 + 4` claims (each commitment: the mini-bus's `≤ 2^38` and two). -/
theorem retOK_typedProg_len (H : THyp Ti) (pub : Lvm.Pub) :
    RetOK (fun a : OpenClaims ↦ a.1.length + a.2.length ≤ 2 ^ 39 + 4) (typedProg Ti pub) := by
  rw [typedProg_eq]
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ RetOK.bind_true fun r ↦ RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hl1 := length_miniClaims Ti .crec cl
  have hl2 := length_miniClaims Ti .main cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans H.widths
  simp only [typedClaims, List.length_cons]
  norm_num at hcl' ⊢
  omega

/-- V_S phases 4–7 add at most `41` claims (`sideT₂`'s count). -/
theorem length_assembleT₂ (x : List UInt8) (a : OpenClaims) (k : KgOut) (hk : KgRet k) :
    (assembleT₂ x a k).2.length + (assembleT₂ x a k).1.length ≤ a.1.length + a.2.length + 41 := by
  have hk1 : (k.2.1.2.2.1.1).length ≤ 1 := hk.2.2.2.2.1
  have l1 : (assembleS [] (pubX x) [] k).1.length ≤ 1 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    simpa using Lvm.ASM.length_crec_le [] (pubX x) [] k
  have l2 : (assembleS [] (pubX x) [] k).2.length ≤ 40 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    have h := Lvm.ASM.length_claimsS [] (pubX x) [] k
    have h0 : (Lvm.VEq.tableClaimsE [] []).length = 0 := rfl
    rw [Lvm.ASM.length_pubX_h, h0] at h
    exact (List.length_filter_le _ _).trans (by omega)
  have e2 : (assembleT₂ x a k).2.length = (a.2 ++ (assembleS [] (pubX x) [] k).2).length := by
    simp only [assembleT₂, Lvm.Shape.onStackZs]
    split_ifs <;> simp only [List.length_map]
  rw [e2]
  simp only [assembleT₂, List.length_append]
  omega

/-- **At most `2^40` claims in all** (`OpenPostM`'s bound after relocation). -/
theorem retOK_midT₂_len (H : THyp Ti) (x : List UInt8) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length ≤ 2 ^ 40) (midT₂ Ti x) :=
  ((retOK_typedProg_len H _).bind fun a ha ↦ (retOK_kgProgS _ _).bind fun k hk ↦
      RetOK.ret ((length_assembleT₂ x a k hk).trans (by norm_num at ha ⊢; omega)) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length ≤ 2 ^ 40) (midT₂ Ti x))

/-! ## A relocation through the shape's view (optional) -/

/-- The `C_rec` column read from the view (`view x q`, the big-layout column) by a big-layout reader `recB`. -/
def recOfV (recB : Column CMain.nu20 → Column 19) (x : List UInt8) (q : Column CMain.nu20) : Column 19 :=
  recB (view x q)

/-- A big-layout relocation `relocB`, then `onStackZ` in the small shape (as `onStackZs`). -/
def relocV (relocB : LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim)
    (x : List UInt8) (c : LeanVM.Protocol.Verifier.StackClaim) : LeanVM.Protocol.Verifier.StackClaim :=
  if Lvm.Shape.small x then Lvm.Shape.onStackZ (relocB c) else relocB c

/-- **The laws through the view** from the big layout's (`holds_onStackZ`, `isMultiaffine_onStackZ`): the lead
then states the relocation once, on the big layout. -/
theorem relocLaw_view {recB : Column CMain.nu20 → Column 19}
    {relocB : LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}
    (hh : ∀ c q, IsMultiaffine 19 c.1 →
      StackClaim.Holds CMain.nu20 (relocB c) q → StackClaim.Holds 19 c (recB q))
    (ha : ∀ c, IsMultiaffine 19 c.1 → IsMultiaffine CMain.nu20 (relocB c).1) :
    RelocLaw (recOfV recB) (relocV relocB) where
  holds x c q hc h := by
    unfold recOfV relocV view at *
    by_cases hs : Lvm.Shape.small x = true
    · simp only [hs, ite_true] at h ⊢
      exact hh c _ hc ((Lvm.Shape.holds_onStackZ _ q).mp h)
    · simp only [hs, Bool.false_eq_true, ite_false] at h ⊢
      exact hh c q hc h
  affine x c hc := by
    unfold relocV
    split_ifs
    · exact Lvm.Shape.isMultiaffine_onStackZ (ha c hc)
    · exact ha c hc

/-! ## At M′ -/

/-- **The good relation at M′**: the typed good pair (both shapes) at `(q, recOf x q)`. -/
def GoodTM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (Ti : TInst) (H : THyp Ti) : GoodRelM :=
  GoodOfM recOf (Good₂ (GoodT Ti H))

/-- **O6 at M′ for the typed backend**: `MidSpecM (midM reloc (midT₂ Ti)) (GoodTM recOf Ti H) εS εS`, given the
relocation's laws. -/
theorem midSpecM_T₂ (H : THyp Ti) {recOf : List UInt8 → Column CMain.nu20 → Column 19}
    {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}
    (hρ : RelocLaw recOf reloc) : MidSpecM (midM reloc (midT₂ Ti)) (GoodTM recOf Ti H) εS εS :=
  midSpecM_of hρ (midSpecP_T₂ H recOf) (retOK_midT₂_len H)

/-- **The middle phases' shape at M′** (no hypothesis on the relocation). -/
theorem midShapeM_T₂ (Ti : TInst)
    (reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim) :
    MidShapeM (midM reloc (midT₂ Ti)) :=
  midShapeM_of fun _ ↦ Lvm.M3.NoCG.bind (cg_typedProg _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _

/-- **The knowledge certificate at M′ for the typed backend** (`kcertSM`): from the relocation's laws and an
extraction for `GoodTM recOf Ti H` (R11-C's `extJM` at the lead's `NodeSoundM`). -/
noncomputable def kcertTM (H : THyp Ti) {recOf : List UInt8 → Column CMain.nu20 → Column 19}
    {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}
    (hρ : RelocLaw recOf reloc) {VS : Lvm.T.SProg} {vk : RecursionFast.Digest}
    (X : Lvm.ASM.ExtJM (midM reloc (midT₂ Ti)) (GoodTM recOf Ti H) VS vk) :
    Lvm.FS.KCert (Lvm.ASM.schemeS vk (Lvm.ASM.PSWithM (midM reloc (midT₂ Ti))))
      (RecursionFast.Rel (Lvm.T.accV VS vk)) :=
  Lvm.ASM.kcertSM (midSpecM_T₂ H hρ) le_rfl (midShapeM_T₂ Ti reloc) X

end Lvm.Typed
