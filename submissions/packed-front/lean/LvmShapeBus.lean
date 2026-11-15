-- Split out of `LvmShape` (lvm2 roll 8, wave L, L-W): the bus path's middle phases in both shapes (CR-S0, roll 7
-- SH2-Z): `midS₂ tabs`'s O6 (`midSpecR₂`) and shape (`midShape_midS₂`); its kinds (`folP_midS₂`,
-- `midFollows_midS₂`) are gone with the typed schedule (L-C). Kept for reference: nothing on the typed path imports
-- it (the typed backend, `LvmTypedSpec`, reads only `LvmShape`), so it and `LvmAccSpecCert` stay outside the typed
-- certificate's import closure.
import LvmShape
import LvmAccSpecCert

/-!
# The bus path's middle phases in both shapes

* **`midS₂`** (`LvmShape`): `midSA` with `C_main`'s claims put through `onStackZ` when `small x` (`assembleS₂`;
  the events are `midSA`'s). **`midSpecR₂`**: `MidSpecR midS₂ (Good₂ GoodA) εS εS`, from `specBusA₂`
  (`midBusTableAccSpecB` at the image set `imgC x`), `specKgS₂` (`kgSpecS` at the view accessors),
  `link_assembleS₂` (`holds_onStackZ`, then `link_assembleS` at the view pair) and `side_midS₂`, through
  `midSpecOfRel` at a fixed statement.
-/

set_option autoImplicit false

namespace Lvm.Shape

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.ASM Lvm.VEq Lvm.KG Lvm.Acc
open Lvm.M3 (Tab lay26)
open scoped ENNReal NNReal

/-! ## O6 in both shapes -/

/-- **What the real tables must meet**: O6's (`MidHyp`, `AccMidHyp`). The small layout's fit
(tables ending by `2^22` logical words) is a completeness fact, not used here. -/
structure MidHyp₂ (tabs : Pub → List Tab) : Prop where
  mid : MidHyp tabs
  acc : AccMidHyp tabs

variable {tabs : Pub → List Tab}

/-- **Phases 2–3b on the viewed pairs** (`specBusA` with `midBusTableAccSpecB` at `imgC x`; the doom
pulled back to `candPairs`). -/
noncomputable def specBusA₂ (H : MidHyp tabs) (HA : AccMidHyp tabs) (x : List UInt8) (N : Pair → Prop) :
    Spec (lbusTableAccProg Lvm.P20 tabs (pubX x) Lvm.P20.busDepth)
      (fun h ↦ RootShape h ∧
        Doomed candPairs (fun p ↦ GbA tabs H.hτ x (vp x p) ∧ (GkS x (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed candPairs
        (fun p ↦ (BS tabs x a (vp x p) ∧ N (vp x p)) ∧ (GkS x (vp x p) ∧ N (vp x p))) h ∧ RootShape h)
      εS εS LkSJ :=
  have F := fit_of Lvm.P20 _ (H.fit (pubX x))
  have hμeq : (Lvm.M3.inst lay26 (Lvm.M3.sumcheckTabs (tabs (pubX x))) (H.hτ x)).μBus =
      Lvm.P20.busDepth := F.μBus_eq (H.hτ x)
  have hμeq' : (Lvm.M3.inst lay26 (TS tabs x) (H.hτ x)).μBus = Lvm.P20.busDepth := F.μBus_eq (H.hτ x)
  have e := bus_errsJ2 (Lvm.M3.inst lay26 (TS tabs x) (H.hτ x)) (by rw [hμeq']; exact F.busLe)
    (le_trans (B_inst_le _ _ _) (H.cons _))
    (((Lvm.M3.vLayout (TS tabs x)).tableLogHeights.foldl max 0))
  have ea := acc_errs
  have S0 := midBusTableAccSpecB lay26 Lvm.P20 tabs (pubX x) (H.hτ x) F.allSc (L₀ := 37696) (εmax := εS)
    (imgC x) (fun p ↦ BndS x p.1 ∧ GkS x p ∧ N p) F.layOk (HA x) (H.keys _) (H.width _)
    (fun h ↦ 2 ≤ (commits h).length) (imgC_append x) (fun _ ↦ Set.toFinite _) (imgC_ncard_le x)
    (by rw [hμeq]; have := F.busPos; omega) e.1 e.2.2.1 e.2.2.2.1
    e.2.2.2.2.1 (T := LkSJ) (by rw [ea.1]; exact e.2.2.2.2.2.1) (by rw [ea.1]; exact e.2.2.2.2.2.2.1)
    (by rw [ea.1]; exact e.2.2.2.2.2.2.2) ea.2 e.2.2.2.2.2.2.1
  ((hμeq ▸ S0).frame RootShape (fun _ _ hl hr ↦ Lvm.M3.rootShape_append
      ((noCG_lbusTableAccProg Lvm.P20 tabs (pubX x) _).1.reach_commits hl) hr)).mono
    (fun h ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.M3.rootShape_two hr, Lvm.M3.rootShape_firstWord hr, doomed_imgC.mpr
      (Doomed.mono hDm fun _ hq ↦
        ⟨⟨⟨hq.1, hq.2.1.1⟩, (accOk_iff Lvm.P20 tabs (pubX x)).mpr hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgC.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩,
      hp.2⟩) le_rfl e.2.1 le_rfl

/-- **The semantic link in both shapes**: `C_main`'s small claims holding on `p.1` are the big claims
holding on `view x p.1` (`holds_onStackZ`), then `link_assembleS` at the viewed pair. -/
theorem link_assembleS₂ (H : MidHyp tabs) (x : List UInt8) (a : List ColumnClaim) (k : KgOut)
    (p : Pair) (ha : TabRet (TS tabs x) a) (hk : KgRet k)
    (h1 : ∀ c ∈ (assembleS₂ x (TS tabs x) (pubX x) a k).1, StackClaim.Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleS₂ x (TS tabs x) (pubX x) a k).2, StackClaim.Holds CMain.nu20 c p.1) :
    KcS k (vp x p) ∧ BS tabs x a (vp x p) := by
  refine link_assembleS H x a k (vp x p) ha hk h1 fun c hc ↦ ?_
  unfold assembleS₂ onStackZs at h2
  unfold vp view
  by_cases hs : small x = true
  · simp only [hs, ite_true, List.mem_map] at h2 ⊢
    exact (holds_onStackZ c p.1).mp (h2 _ ⟨c, hc, rfl⟩)
  · simp only [hs, ite_false, Bool.false_eq_true] at h2 ⊢
    exact h2 c hc

/-- The side conditions in both shapes (`side_midS`, `isMultiaffine_onStackZ`). -/
theorem side_midS₂ (H : MidHyp tabs) (x : List UInt8) (a : List ColumnClaim) (k : KgOut)
    (ha : TabRet (TS tabs x) a) (hk : KgRet k) :
    (∀ c ∈ (assembleS₂ x (TS tabs x) (pubX x) a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleS₂ x (TS tabs x) (pubX x) a k).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleS₂ x (TS tabs x) (pubX x) a k).1.length ≤ 2 ^ 55 ∧
    (assembleS₂ x (TS tabs x) (pubX x) a k).2.length ≤ 2 ^ 40 := by
  obtain ⟨s1, s2, s3, s4⟩ := side_midS H x a k ha hk
  refine ⟨s1, fun c hc ↦ ?_, s3, ?_⟩
  · unfold assembleS₂ onStackZs at hc
    split_ifs at hc
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact isMultiaffine_onStackZ (s2 c' hc')
    · exact s2 c hc
  · unfold assembleS₂ onStackZs
    split_ifs
    · rw [List.length_map]; exact s4
    · exact s4

/-- **O6 in both shapes**: the middle phases' relativised specification, `Good := Good₂ GoodA`
(`midSpecOfRel` at a fixed statement: its `Kc` does not read the statement, the view does). -/
theorem midSpecR₂ (H : MidHyp₂ tabs) : MidSpecR (midS₂ tabs) (Good₂ (GoodA tabs H.mid.hτ)) εS εS := by
  intro x₀ T hT
  have M : MidSpecR (fun _ ↦ lbusTableAccProg Lvm.P20 tabs (pubX x₀) Lvm.P20.busDepth >>= fun a ↦
        kgProgS (hdX x₀).s (pubX x₀).n >>= fun k ↦
          VerifierProgram.ret (assembleS₂ x₀ (TS tabs x₀) (pubX x₀) a k))
      (fun _ qm qr ↦ GbA tabs H.mid.hτ x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr))) εS εS :=
    midSpecOfRel
      (busP := fun _ ↦ lbusTableAccProg Lvm.P20 tabs (pubX x₀) Lvm.P20.busDepth)
      (kgP := fun _ ↦ kgProgS (hdX x₀).s (pubX x₀).n)
      (asm := fun _ a k ↦ assembleS₂ x₀ (TS tabs x₀) (pubX x₀) a k) (Lb := εS) (Lk := LkSJ)
      (Gb := fun _ p ↦ GbA tabs H.mid.hτ x₀ (vp x₀ p)) (Gk := fun _ p ↦ GkS x₀ (vp x₀ p))
      (B := fun _ a p ↦ BS tabs x₀ a (vp x₀ p)) (Kc := fun k p ↦ KcS k (vp x₀ p))
      (Qa := fun _ ↦ TabRet (TS tabs x₀)) (Qk := KgRet)
      (fun _ ↦ specBusA₂ H.mid H.acc x₀ fun p ↦ ¬ (GbA tabs H.mid.hτ x₀ p ∧ GkS x₀ p))
      (fun _ ↦ retOK_lbusTableAccProg _ _ _ _)
      (fun _ a T hT ↦ (specKgS₂ x₀
          (fun p ↦ BS tabs x₀ a (vp x₀ p) ∧ ¬ (GbA tabs H.mid.hτ x₀ (vp x₀ p) ∧ GkS x₀ (vp x₀ p)))
          T hT).mono
        (fun _ hd ↦ Doomed.mono hd fun _ hq ↦ ⟨⟨hq.1, hq.2.2⟩, hq.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl
        le_rfl)
      (fun _ ↦ retOK_kgProgS _ _) (fun _ ↦ cg_kgProgS _ _)
      (fun _ a k p ha hk h1 h2 ↦ link_assembleS₂ H.mid x₀ a k p ha hk h1 h2)
      (fun _ a k ha hk ↦ side_midS₂ H.mid x₀ a k ha hk)
  obtain ⟨S⟩ := M x₀ T hT
  have S' : Spec (midS₂ tabs x₀) RootShape (OpenPostR
      (fun _ qm qr ↦ GbA tabs H.mid.hτ x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr))) x₀) εS εS T := by
    unfold midS₂
    exact S
  refine ⟨S'.mono (fun _ h ↦ h) (fun cl h hp ↦ ?_) le_rfl le_rfl le_rfl⟩
  exact (openPostR_congr
    (G := fun _ qm qr ↦ GbA tabs H.mid.hτ x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr)))
    (G' := Good₂ (GoodA tabs H.mid.hτ)) fun _ _ ↦ Iff.rfl).mp hp

/-- **The middle phases' shape in both shapes** (`midShape_midSA`; `C_rec`'s claims are `assembleS`'s). -/
theorem midShape_midS₂ (H : MidHyp tabs) : MidShape (midS₂ tabs) where
  noCommit _ := (Lvm.M3.NoCG.bind (noCG_lbusTableAccProg _ _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _).1
  noGrind _ := (Lvm.M3.NoCG.bind (noCG_lbusTableAccProg _ _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _).2
  recAffine x l cl hl :=
    ((retOK_lbusTableAccProg _ _ _ _).bind fun a ha ↦ (retOK_kgProgS _ _).bind fun k hk ↦
      RetOK.ret (side_midS₂ H x a k ha hk).1 :
      RetOK (fun cl : OpenClaims ↦ ∀ c ∈ cl.1, IsMultiaffine 19 c.1) (midS₂ tabs x)) l cl hl


end Lvm.Shape
