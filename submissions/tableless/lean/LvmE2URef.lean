-- New for lvm2 U-TAPE (UT-V, UTAPE-STMT 22): V_S's S2GU decision (`decideProgUG P20U P20`, the fast twins) refines
-- the pinned S2GU middle phases on the stream with S2GU's read widths, at S2GU's occupied words `occOfU`.
import LvmE2UEq
import LvmE2VDecRef
import LvmE2TVEq
import LvmE2TRegReloc
import LvmS2GUFol
import LvmE2VTopF

/-!
# V_S's S2GU decision refines the pinned middle phases

* `mainLevels_P20U`, **`corrMainU`**: `C_main`'s levels at `P20U` (root row `368 = 8·46`) against `cfgMain23Jq 1`
  at `occOfU`.
* The tape on the data: `refW_tapeUDG` (`refW_tapeUD` through `tapeUDG_R`), `retD_tapeUDG` (the shape, and the `Y`
  and stream blocks' row switches run at their points, `ColsU`).
* **`frontU_stk`**: the front's items (`frontItemsU rowAccR`, the `Y`/`M` row claims on their blocks) have the stack
  forms of the closures' claims (`frontClaimsUD`).
* The typed phases on `P20U`'s layout as items: `dTypedTG_items`, `ref_dTypedTU`.
* `psU_eq`: the pinned middle phases at S2GU as one chain.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-! ## `C_main`'s levels at S2GU -/

/-- `C_main`'s levels at `P20U` (`P20T`'s with the root row at `8·46`). -/
theorem mainLevels_P20U : P20U.mainLevels = [⟨0, 6, 17, 2, 19, 8, 11, 115, 368⟩,
    ⟨1, 4, 13, 3, 16, 7, 9, 77, 384⟩, ⟨2, 4, 9, 4, 13, 7, 6, 58, 384⟩] := by decide +kernel

/-- **`C_main`'s levels at `P20U` against `cfgMain23Jq 1`** at the occupied words `occOfU`. -/
theorem corrMainU : LevelsCorr capS occOfU shpS 23 0 1 0 0 P20U.mainLevels (cfgMain23Jq 1).levels := by
  rw [mainLevels_P20U]
  simp only [LevelsCorr, NextOK, cfgMain23Jq]
  decide

theorem mainOod_P20U : P20U.mainOod = true := rfl

/-! ## The tape on the data -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- A refinement of a mapped program is one of the program, the relation read through the map. -/
theorem RefAtW.of_map {α β γ : Type} {i j : ℕ} {d : DM β} {f : β → γ} {P : VerifierProgram α}
    {R : γ → α → Prop} (h : RefAtW cap occ shp rw sig i (f <$> d) P R j) :
    RefAtW cap occ shp rw sig i d P (fun b a ↦ R (f b) a) j :=
  fun s hok ↦ h s hok

theorem RefAtWP.of_map {α β γ : Type} {i j : ℕ} {d : DM β} {f : β → γ} {P : VerifierProgram α}
    {R : γ → α → Prop} {Q : γ → Prop} (h : RefAtWP cap occ shp rw sig i (f <$> d) P R Q j) :
    RefAtWP cap occ shp rw sig i d P (fun b a ↦ R (f b) a) (fun b ↦ Q (f b)) j :=
  fun s hok hq ↦ h s hok hq

/-- **V_S's S2GU tape on the data** refines `tapeProgU`, its value through `mapTU`. -/
theorem refW_tapeUDG (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUDG rowSwitchDR P20U s n) (tapeProgU d n) (fun t o ↦ TapeURelW (mapTU t) o)
      (i + wTapeU.length) :=
  RefAtW.of_map (by rw [tapeUDG_R]; exact refW_tapeUD s d hs n hw)

end Ref

theorem RetD.of_map {β γ : Type} {Q : γ → Prop} {d : DM β} {f : β → γ} (h : RetD Q (f <$> d)) :
    RetD (fun b ↦ Q (f b)) d :=
  fun sig s ↦ h sig s

theorem RetD.and {β : Type} {Q Q' : β → Prop} {d : DM β} (h : RetD Q d) (h' : RetD Q' d) :
    RetD (fun b ↦ Q b ∧ Q' b) d :=
  fun sig s ↦ ⟨h sig s, h' sig s⟩

theorem MonoD.of_map {β γ : Type} {d : DM β} {f : β → γ} (h : MonoD (f <$> d)) : MonoD d :=
  fun sig s hok ↦ h sig s hok

/-- A row switch on the data runs at its point. -/
theorem retD_rowSwitchDR (z sv : List FE2) :
    RetD (fun R : RowZ ↦ R.1.cols = z.map tColsW) (rowSwitchDR z sv) := by
  unfold rowSwitchDR
  exact RetD.bind_true fun _ ↦ RetD.pure rfl

/-- A slot reduction's row switch runs at the slot's point. -/
theorem retD_slotDFW (b sb blk : ℕ) (wz : List FE2 → Array FE2) (pt : List FE2) (v : FE2) :
    RetD (fun t : SlotU RowZ ↦ t.2.2.1.cols = (pt ++ t.1.1 ++ selPtF blk sb).map tColsW)
      (slotDFW rowSwitchDR b sb blk wz pt v) := by
  unfold slotDFW
  exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_rowSwitchDR _ _).bind fun _ h ↦ RetD.pure h

/-- **The `Y` and stream blocks' row switches run at their points** (`wireUDG` at `p`). -/
def ColsW (p : Params) (wo : WireU RowZ) : Prop :=
  wo.y.2.2.1.cols = (wo.sc.1.take p.ksLog ++ wo.y.1.1 ++
      selPtF ((layout0 p).ks / 2 ^ (p.ksLog + slotBitsU)) (p.nuMain - (p.ksLog + slotBitsU))).map tColsW ∧
    wo.m.2.2.1.cols = (wo.sc.1.take p.ksLog ++ [0] ++ wo.m.1.1 ++
      selPtF ((layout0 p).s / 2 ^ p.nuRec) (p.nuMain - p.nuRec)).map tColsW

theorem retD_wireUDG (p : Params) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (ColsW p) (wireUDG rowSwitchDR p s n claim) := by
  unfold wireUDG
  exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotDFW _ _ _ _ _ _).bind fun _ hy ↦ (retD_slotDFW _ _ _ _ _ _).bind fun _ hm ↦ RetD.pure ⟨hy, hm⟩

/-- **What V_S's S2GU tape on the data returns**: the closures' shape (`TapeShapeU`) and the block rows' points. -/
theorem retD_tapeUDG (s : List FK) (n : ℕ) :
    RetD (fun t : TapeU RowZ ↦ TapeShapeU (mapTU t) ∧ ColsW P20U t.wo) (tapeUDG rowSwitchDR P20U s n) := by
  refine RetD.and (RetD.of_map (f := mapTU) ?_) ?_
  · rw [tapeUDG_R]; exact retD_tapeUD s n
  · unfold tapeUDG
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUDG _ _ _ _).bind fun _ h ↦ RetD.pure h

/-! ## The front's items stand for the closures' claims -/

theorem flat_splitD (nu : ℕ) (parts : List (FE2 × Placement × List FE2)) (v : FE2) (t : List FE) :
    (FItem.split nu parts v (t.getD 0 0) (t.getD 1 0)).flat =
      ((splitD nu parts v).zip [t.getD 0 0, t.getD 1 0]).map fun e ↦ (Com.main, e.1, e.2) := by
  rw [← splitDF_eq]; rfl

theorem flat_splitZ (nu : ℕ) (parts : List (FE2 × Placement × List FE2)) (v : FE2) :
    (FItem.split nu parts v 0 0).flat = splitZ nu parts v := by
  rw [← splitZF_eq]; rfl

theorem tailDE2_eq (r : List FE2) (l : ℕ) : tailDE2 r l = [(tailDE2 r l).getD 0 0, (tailDE2 r l).getD 1 0] := rfl

theorem inStackB_yU : inStackB ⟨18, CMain.yOffU20⟩ = true := by decide +kernel
theorem inStackB_sU : inStackB ⟨19, CMain.sOffU20⟩ = true := by decide +kernel

/-- **The front's items have the closures' claims' stack forms** at any record, given those of the `Y` and stream
blocks' rows (`hY`, `hM`): the split and boundary items are the closures' claims, `D`'s row the same claim. -/
theorem frontU_stkG (g : Com × BlockClaim × FE → Com × StackClaim) (p : Params) (pub : Pub) (t : TapeU RowZ)
    (hY : (RowK.rowItemK p.nuMain ⟨p.ksLog + slotBitsU, (layout0 p).ks⟩ t.wo.y.2.2 0).flat.map g =
      [g (.main, ⟨⟨p.nuMain, 0⟩, t.wo.y.2.2.1.w, t.wo.y.2.2.1.tgt⟩, 0)])
    (hM : (RowK.rowItemK p.nuMain ⟨p.nuRec, (layout0 p).s⟩ t.wo.m.2.2 0).flat.map g =
      [g (.main, ⟨⟨p.nuMain, 0⟩, t.wo.m.2.2.1.w, t.wo.m.2.2.1.tgt⟩, 0)]) :
    ((frontItemsU rowAccR p pub t).flatMap FItem.flat).map g = (frontClaimsUD p pub (mapTU t)).map g := by
  unfold frontItemsU frontClaimsUD
  simp only [List.flatMap_append, List.map_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil, hY, hM]
  have hA : ∀ l, (FItem.split p.nuMain [(1, dBlock p, t.r ++ selPtF l 2)] (t.ab.getD l 0) ((tailDE2 t.r l).getD 0 0)
      ((tailDE2 t.r l).getD 1 0)).flat = ((splitD p.nuMain [(1, dBlock p, t.r ++ selPtF l 2)] (t.ab.getD l 0)).zip
        (tailDE2 t.r l)).map fun e ↦ (Com.main, e.1, e.2) := fun l ↦ by
    rw [flat_splitD, ← tailDE2_eq]
  have hB : ∀ l, (FItem.split p.nuMain [(1, ⟨p.ksLog, (layout0 p).ks + l * 2 ^ p.ksLog⟩, t.r.take p.ksLog)]
      (t.ab.getD (25 + l) 0) 0 0).flat =
      splitZ p.nuMain [(1, ⟨p.ksLog, (layout0 p).ks + l * 2 ^ p.ksLog⟩, t.r.take p.ksLog)] (t.ab.getD (25 + l) 0) :=
    fun l ↦ flat_splitZ _ _ _
  simp only [hA, hB]
  simp only [FItem.flat, rowAccR, flatMap_single]
  rfl

/-- **The front's items at `P20U` have the closures' claims' stack forms** (both shapes; the block rows' switches
run at their points, `ColsW`). -/
theorem frontU_stk (s : Bool) (pub : Pub) (t : TapeU RowZ) (hc : ColsW P20U t.wo) (hsc : t.wo.sc.1.length = 20)
    (hy : t.wo.y.1.1.length = 5) (hm : t.wo.m.1.1.length = 5) :
    ((frontItemsU rowAccR P20U pub t).flatMap FItem.flat).map (fun e ↦ (e.1, toStk s P20U.nuMain e.2)) =
      (frontClaimsUD P20U pub (mapTU t)).map (fun e ↦ (e.1, toStk s P20U.nuMain e.2)) := by
  obtain ⟨hcy, hcm⟩ := hc
  have hks : (layout0 P20U).ks = CMain.yOffU20 := ks_P20U
  have hs : (layout0 P20U).s = CMain.sOffU20 := by rw [layout0_P20U]
  have hy18 : (layout0 P20U).ks / 2 ^ (P20U.ksLog + slotBitsU) = 22 := by rw [hks]; rfl
  have hs19 : (layout0 P20U).s / 2 ^ P20U.nuRec = 10 := by rw [hs]; rfl
  rw [hy18] at hcy
  rw [hs19] at hcm
  refine frontU_stkG _ P20U pub t ?_ ?_
  · have h := rowItemK_toStk s 23 ⟨18, CMain.yOffU20⟩ t.wo.y.2.2 (t.wo.sc.1.take 13 ++ t.wo.y.1.1) 0
      (by rw [hcy]; rfl) (by simp [hsc, hy]) (by decide) (by decide +kernel) fun _ ↦ ⟨rfl, inStackB_yU⟩
    rw [hks]
    simp only [RowK.rowItemK, FItem.flat, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h ⊢
    rw [show P20U.nuMain = 23 from rfl, show P20U.ksLog + slotBitsU = 18 from rfl, h]
  · have h := rowItemK_toStk s 23 ⟨19, CMain.sOffU20⟩ t.wo.m.2.2 (t.wo.sc.1.take 13 ++ [0] ++ t.wo.m.1.1) 0
      (by rw [hcm]; rfl) (by simp [hsc, hm]) (by decide) (by decide +kernel) fun _ ↦ ⟨rfl, inStackB_sU⟩
    rw [hs]
    simp only [RowK.rowItemK, FItem.flat, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h ⊢
    rw [show P20U.nuMain = 23 from rfl, show P20U.nuRec = 19 from rfl, h]

/-! ## The typed phases on `P20U`'s layout, as items -/

theorem monoD_dTypedTG {α : Type} (p : Params) (N : TNatT) (m : M3) (pub : Pub)
    (mk : List FE2 → List FE2 → List FE2 → FE2 → α) : MonoD (dTypedTG p N m pub mk) :=
  E2T.monoD_dZeroT.bind fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- The typed phases' claims are their items' flattening. -/
theorem dTypedTG_items (pT p : Params) (N : TNatT) (m : M3) (pub : Pub) :
    dTypedTG pT N m pub (typedClaimsND N p) =
      (fun r ↦ (r.1, r.2.1.flatMap FItem.flat, r.2.2)) <$> dTypedTG pT N m pub (typedItemsND N p) := by
  unfold dTypedTG
  simp only [map_bind, map_pure, typedItemsND_flat]

/-- The typed phases on S2GU's mini-bus instance are those on the record's (`dMiniT` reads neither `PUB`'s check
nor the stage). -/
theorem dTypedTG_m3GU {α : Type} (N : TNatT) (pub : Pub) (mk : List FE2 → List FE2 → List FE2 → FE2 → α) :
    dTypedTG P20 N (m3G N P20U) pub mk = dTypedTG P20 N (N.toN.m3 P20) pub mk := by
  unfold dTypedTG
  rw [dMiniT_congr P20 P20 (m3G N P20U) (N.toN.m3 P20) N.mbT pub rfl rfl rfl rfl rfl]

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's typed phases at S2GU** (items on `P20U`'s layout) refine `typedProgT`, their items through `FItem.flat`
(`ref_dTypedTO` at `P20U`). -/
theorem ref_dTypedTU (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = Typed.phiVarsT) {i : ℕ} (hw : WAt rw i wTypedT) :
    RefAtWP cap occ shp rw sig i (dTypedTG P20 N (m3G N P20U) pub (typedItemsND N P20U))
      (typedProgT (N.inst Q lay) pub) (fun r a ↦ TRelTTO P20U N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedT.length) := by
  have h := ref_dTypedTO (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) P20U N Q lay H pub hacc hw
  rw [dTypedTG_items, ← dTypedTG_m3GU N pub] at h
  have h' := RefAtWP.of_map h
  exact h'

end Ref

/-! ## The pinned middle phases and the decision at S2GU -/

/-- **The pinned middle phases at S2GU as one chain**: the root, the pin, the typed phases, the merged tape,
`C_main`'s opening on the pin's claim and `ordMk 4` of `assembleU₂`'s relocated pair. -/
theorem psU_eq (Ti : Typed.TInst) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU Ti))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        typedProgT Ti (pubXT x) >>= fun a ↦ tapeProgU (hdX x).s (pubX x).n >>= fun k ↦
          LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
            Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) >>= fun _ ↦
              pure true := by
  unfold Lvm.ASM.PSWithM Lvm.E2F.midP Lvm.ASM.midMk midGU midGB tapeProgU
  rw [commitRootUd_mainT]
  simp only [bind_assoc, ret_bindM, pure_bind]

theorem monoD_tapeUD (s : List FK) (n : ℕ) : MonoD (tapeUD s n) :=
  monoD_sepE2.bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_tapeUDG (s : List FK) (n : ℕ) : MonoD (tapeUDG rowSwitchDR P20U s n) :=
  MonoD.of_map (f := mapTU) (by rw [tapeUDG_R]; exact monoD_tapeUD s n)

theorem monoD_dOpenFFI (p : Params) (s : Bool) (pin : BlockClaim) (ti items : List FItem) :
    MonoD (dOpenFFI p s pin ti items) := by
  rw [dOpenFFI_eq]; exact monoD_dOpenF _ _ _ _

theorem skip_P20U : nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap = 32 * 2 ^ capS 19 64 := by decide

theorem smallT_P20U (x : List UInt8) : TypedV.smallT P20U (pubXT x) = Shape.small x := smallP_P20 x

/-- **V_S's read widths at S2GU** in the decision's order: the pin's read, the typed phases', the tape's, the
opening's (`asO`). -/
def wDecU (asO : List Atom) : List ℕ := [24] ++ wTypedT ++ wTapeU ++ widthsA asO

/-- **V_S's S2GU decision refines the pinned S2GU middle phases** at `occOfU`, with read widths `wDecU asO` from read
`0`, under the promise that its value passes `Φ_Q` at `E2`, given the claims' relation (`hcl`). -/
theorem ref_decideGU (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (vk c : RecursionFast.Digest) (x : List UInt8) {sig : ByteArray} (hpub : pubG vk c sig = pubXT x)
    (asO : List Atom) {rw : ℕ → ℕ}
    (hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl) asO pp fun _ _ ↦ True)
    (h24O : ∀ w ∈ widthsA asO, w = 24) (hw : WAt rw 0 (wDecU asO))
    (hacc : (pubXT x).accIn.pt.length = Typed.phiVarsT) (hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s)
    (hcl : ∀ t a', TRelTTO P20U N Q lay t a' → ∀ (tp : TapeVU) (k : TapeOutU), TapeURelW tp k → TapeShapeU tp →
      (t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).all
        (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
          (((t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).filter
            (·.1 == .main)).map (·.2)))
        (Lvm.ASM.ordMk 4 ((assembleU₂ x a' k).1.map (relocU20 x)) (assembleU₂ x a' k).2)) :
    RefAtPW capS occOfU shpS rw sig 0 (decideProgUG P20U P20 N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecU asO).length := by
  rw [wDecU, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw0, hwT⟩, hwF⟩, hwO⟩ := hw
  replace hwF := WAt.idx_eq hwF (j := 0 + [24].length + wTypedT.length)
    (by simp only [List.length_append]; omega)
  replace hwO := WAt.idx_eq hwO (j := 0 + [24].length + wTypedT.length + wTapeU.length)
    (by simp only [List.length_append]; omega)
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.toT.sc_eq
  rw [psU_eq]
  unfold decideProgUG
  refine RefAtPW.read_left ?_
  dsimp only
  rw [hpub]
  -- the cap
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    ((refW_skip (n := nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap) (ht := 19) (w := 64) skip_P20U).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro - - - -
  -- the pin
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ ((refW_pinD (WAt.cons.mp hw0).1).toPW _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro pin za ⟨z, a, rfl, rfl⟩ -
  -- the typed phases
  have hT0 : RefAtPW capS occOfU shpS rw sig (0 + [24].length) (dTypedTG P20 N (m3G N P20U) (pubXT x) (typedItemsND N P20U))
      (typedProgT (N.inst Q lay) (pubXT x)) (fun r a ↦ TRelTTO P20U N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) (0 + [24].length + wTypedT.length) :=
    ref_dTypedTU N Q lay H (pubXT x) hacc hwT
  refine RefAtPW.bind (Q := fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) ?_ hT0 ?_ ?_
  rotate_left
  · intro b s hs'
    refine promise_of_retDG (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) ?_ hs'
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.pure rfl
  rintro ⟨acc, ti, evals⟩ a' hT -
  dsimp only
  -- the tape
  rw [show (pubXT x).n = (pubX x).n from rfl]
  have hTp1 := refW_tapeUDG (cap := capS) (occ := occOfU) (shp := shpS) (sig := sig) (pubXT x).s (hdX x).s hs
    (pubX x).n hwF
  have hTp2 := hTp1.retD (retD_tapeUDG (pubXT x).s (pubX x).n)
  have hTp := hTp2.toPW (fun _ ↦ True)
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ hTp (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro tp k ⟨hk, hsh, hcols⟩ -
  -- the opening, on the closures' claims
  have hsh' := hsh
  obtain ⟨-, hl20, -, -, hy5, -, hm5, -⟩ := hsh'
  have e : dOpenFFI P20U (TypedV.smallT P20U (pubXT x)) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals)
      (frontItemsU rowAccR P20U (pubXT x) tp) =
      dOpenF P20U (Shape.small x) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti.flatMap FItem.flat ++ Shape.zeroTails (M3.tableClaimsR N.mbT evals) ++
        frontClaimsUD P20U (pubXT x) (mapTU tp)) := by
    rw [smallT_P20U, dOpenFFI_eq]
    refine dOpenF_congr _ _ _ ?_
    rw [List.flatMap_append, List.flatMap_append, tabItemsR_flat, hsc, List.map_append, List.map_append,
      List.map_append, List.map_append, frontU_stk _ _ tp hcols hl20 hy5 hm5]
  rw [e]
  have hO := RefAtP.toPW (ref_dOpenFO (sig := sig) P20U rfl rfl rfl corrMainU _ _ (screl_pinW z a) (Shape.small x) _ _
    (hcl (acc, ti.flatMap FItem.flat, evals) a' hT (mapTU tp) k hk hsh))
    (cap' := capS) (shp' := shpS) (idx := idxS) (hFO _) hwO h24O
  refine RefAtPW.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) hO (fun _ _ _ ↦ trivial) ?_
  rintro - - - -
  exact ((RefAtW.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) rfl).idx
    (by simp only [wDecU, List.length_append, List.length_singleton])).toPW _
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_pinD _) | (with_reducible exact monoD_dTypedTG _ _ _ _ _)
    | (with_reducible exact monoD_tapeUDG _ _) | (with_reducible exact monoD_dOpenFFI _ _ _ _ _)
    | (with_reducible exact monoD_dOpenF _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-! ## The claims at S2GU -/

theorem ordMk_of_length {α : Type} (k : ℕ) (r m : List α) (h : r.length = k) :
    Lvm.ASM.ordMk k r m = r ++ m := by
  have hm : m.dropLast ++ m.getLast?.toList = m := by
    cases m using List.reverseRecOn with
    | nil => rfl
    | append_singleton l a => simp
  unfold Lvm.ASM.ordMk
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil, List.append_assoc, hm]

theorem offOK_relayU : Shape.OffOK ⟨P20U.nuRec, (layout0 P20U).s⟩ := by
  rw [layout0_P20U]; decide +kernel

theorem relocOKAt_relayU (z : List E2) : RelocOKAt CMain.sOffU20 (1, ⟨Typed.relayRounds, 0⟩, z) := by
  unfold RelocOKAt
  dsimp only
  decide

/-- **V_S's claim list at S2GU (after the pin) against `ordMk 4` of `assembleU₂`'s relocated pair** (both shapes):
where V_S's `require` held (every claim on `C_main`), the typed claims (`TRelTTO P20U`: the relayout's and `σ′`'s
halves relocated onto S2GU's `S`, the committed block's and `KS`'s halves), the mini-bus's and the front's
(`front_relU`), on the statement's shape's stack, are the spec's in V_S's order. -/
theorem claimsU_rel (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (x : List UInt8)
    (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims)
    (hT : TRelTTO P20U N Q lay t a) (tp : TapeVU) (k : TapeOutU) (hk : TapeURelW tp k) (hsh : TapeShapeU tp)
    (hall : (t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).all
      (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
        (((t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).filter
          (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, -, -, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.toT.fits
  have hall' : ∀ e ∈ t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++
      frontClaimsUD P20U (pubXT x) tp, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he]]
  have hok := H.ok
  rw [nuMain_P20] at hok
  have hS : (layout0 P20U).s = CMain.sOffU20 := by rw [layout0_P20U]
  -- the typed claims
  have hrelay := vrel_splitMAt (s := Shape.small x) CMain.sOffU20 [(1, ⟨P20U.nuRec, (layout0 P20U).s⟩, rr)]
    (by simpa using offOK_relayU) vR [(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)]
    (by simp [E2V.partE, shiftS2At, hS, Lvm.FE2.toE2_one]; rfl)
    (by simp only [List.mem_singleton, forall_eq]; exact relocOKAt_relayU _) (toE2 vR) rfl
  have hsg := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .sigma (.inr (.inr rfl)) ry hry
    (rv.getD 2 0)
  rw [regClaimT_relocSAt N Q lay 23 P20.nuRec hok H.hlay CMain.sOffU20 (by decide) (hS ▸ hσ)] at hsg
  have hcom := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .com (.inl rfl) ry hry (rv.getD 0 0)
  have hks := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .ks (.inr (.inl rfl)) ry hry
    (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      ((E2V.splitE2 19 ⟨[(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)], toE2 vR⟩).map
          (fun c ↦ relocSAt CMain.sOffU20 c.onStack) ++
        (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map toE2) (toE2 (rv.getD 2 0))).map
          (relocSAt CMain.sOffU20) ++
        regClaimT (N.inst Q lay) .com N.toN.off (ry.map toE2) (toE2 (rv.getD 0 0)) ++
        regClaimT (N.inst Q lay) .ks N.toN.off (ry.map toE2) (toE2 (rv.getD 3 0))) := by
    rw [ht1]
    unfold typedClaimsND
    exact Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append hrelay hsg) hcom) hks
  -- the mini-bus's claims
  have hZrel : List.Forall₂ CRelM ((Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2)).map fun e ↦ (e.1, e.2.1))
      (tableClaimsE N.mbT (M3.claimsOfEvs N.mbT t.2.2)) := by
    rw [Shape.zeroTails, List.map_map]
    simpa [Function.comp_def] using hcl.imp fun _ _ h ↦ CRel.crelM h
  have hZm : ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main := fun e he ↦
    hall' e (List.mem_append_left _ (List.mem_append_right _ he))
  have hZt : Shape.small x = true → ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main →
      Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1 := by
    intro _ e he hm
    rw [Shape.zeroTails] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have h := Shape.table_tails N.mbT N.mbT (fun _ h ↦ h) t.2.2 hfc hfh e' he' hm
    exact ⟨h.inStack, h.tail.symm⟩
  have hZV := forall₂_crelM (s := Shape.small x) hZrel hZm hZt
  -- the front
  have hFV := front_relU (s := Shape.small x) x tp k hk hsh (fun hs ↦ of_decide_eq_true hs)
    (by simp [pubX, pubOf])
  have hV := forall₂_onStackZsF (Lk.forall₂_append (Lk.forall₂_append hTV hZV) hFV)
  -- the spec's list in V_S's order
  have hmbE := main_of_crel hcl fun e he ↦ by
    have := hZm (e.1, e.2, 0) (List.mem_map.2 ⟨e, he, rfl⟩)
    exact this
  convert hV using 1
  have hmb : (N.inst Q lay).mbT = N.mbT := rfl
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (relocU20 x) = (l.map (relocSAt CMain.sOffU20)).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold assembleU₂ typedClaimsT Typed.miniClaims
  rw [hmb, filter_main_self hmbE, filter_crec_nil hmbE]
  dsimp only
  rw [onStackZs_eq_map, hρ, ordMk_of_length 4 _ _ (by simp [E2V.splitE2, regClaimT]), ← List.map_append,
    inplM_main hmbE]
  simp only [List.map_append, List.map_map, List.append_assoc, List.append_nil, Function.comp_def, List.map_nil,
    List.nil_append, E2V.pointE2, E2T.kv_toE2_getD]
  rfl

/-! ## The schedule at S2GU: atoms, follow, static check, read widths -/

/-- The atoms of items depend on the records' levels only through their heights and query counts. -/
theorem atomsOf_congrL (p q : Params)
    (h : ∀ r, (p.level r).height = (q.level r).height ∧ (p.level r).t = (q.level r).t) (its : List Item) :
    atomsOf p its = atomsOf q its := by
  unfold atomsOf
  refine List.flatMap_congr fun it _ ↦ ?_
  cases it with
  | positions r =>
    obtain ⟨h1, h2⟩ := h r
    simp only [itemAtoms, Level.nPosQ, h1, h2]
  | _ => rfl

theorem withRow0_getD (ls : List Level) (occ i : ℕ) :
    ((withRow0 ls occ).getD i default).height = (ls.getD i default).height ∧
      ((withRow0 ls occ).getD i default).t = (ls.getD i default).t := by
  cases ls with
  | nil => exact ⟨rfl, rfl⟩
  | cons L rest =>
    cases i with
    | zero => simp only [withRow0]; split <;> exact ⟨rfl, rfl⟩
    | succ i => exact ⟨rfl, rfl⟩

/-- **S2GU's atoms are `P20`'s** (`P20U`'s levels differ from `P20`'s in the root's row only). -/
theorem atomsOf_U (its : List Item) : atomsOf P20U its = atomsOf P20 its :=
  atomsOf_congrL P20U P20 (fun r ↦ by
    obtain ⟨c, lv⟩ := r
    cases c
    · exact withRow0_getD P20.mainLevels 46 lv
    · exact ⟨rfl, rfl⟩) its

theorem atomsOf_scheduleU : atomsOf P20U (schedule P20U) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20U (midItemsU P20U) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleU_eq _ rfl, atomsOf_append, atomsOf_append, atomsOf_append, atomsOf_nil, atomsOf_U (openMainI P20U),
    atomsOf_U (commitI P20U), show openMainI P20U = openMainI P20 from rfl,
    show commitI P20U = commitI P20 from rfl, atomsOf_commitI]

/-- **S2GU's `P_S` follows the schedule** at `P20U`: the root, the pin, the typed phases at `E2`, the merged tape,
`C_main`'s opening (`P20`'s atoms), from no pending positions (`fol_PSOfT`'s proof). -/
theorem fol_PSOfU (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20U.leafdecReads = 1) (hd : P20U.busDepth = Typed.miniDepth)
    (hr : P20U.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20U.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGU Ti))) x)
      (atomsOf P20U (schedule P20U)) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleU]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGU Ti)) x) _
    (atomsOf P20U (midItemsU P20U)) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPU reloc Ti hl hd hr he x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

set_option maxRecDepth 200000 in
/-- **The static check at S2GU** at the occupied words `occOfU` (one kernel evaluation over the items). -/
theorem stA_P20U : stA P20U (atomsOf P20U (schedule P20U)) 0 [] [] occOfU = true := by
  rw [stA_atomsOf]
  decide +kernel

/-- **`rwU20` is the S2GU schedule's read widths** from read `0`. -/
theorem wAt_rwU20 : WAt rwU20 0 (widthsA (atomsOf P20U (schedule P20U))) := by
  rw [← readWidthsP_eqAP]
  exact wAt_getD _ _

/-- **The S2GU schedule's read widths** in V_S's decision order (`wDecU`). -/
theorem widthsA_scheduleU : widthsA (atomsOf P20U (schedule P20U)) = wDecU (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  have hT : widthsA (atomsOf P20U (typedIT P20U)) = wTypedT := by
    rw [atomsOf_U, show typedIT P20U = typedIT P20T from rfl, ← atomsOf_T, widthsA_typedIT]
  have hF : widthsA (atomsOf P20U (tapeU P20U ++ wireU P20U)) = wTapeU := by
    rw [widthsA_atomsOf]
    simp only [tapeU, wireU, slotRedI, show P20U.logN = 20 from rfl, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, wI_tapeLayersE2I, wI_smp,
      show sepI.flatMap itemW = [] from rfl, wTapeU, wWireU, wTapeGkr, wSlot, List.nil_append, List.append_assoc]
    rfl
  rw [atomsOf_scheduleU, midItemsU, atomsOf_append P20U (pinI _), atomsOf_append P20U (typedIT _), atomsOf_pinIU]
  simp only [widthsA_append, hp, hT, hF, List.append_nil, List.nil_append, List.append_assoc, wDecU]
  rfl

/-! ## The decision at S2GU, assembled -/

/-- **V_S's S2GU decision refines the pinned S2GU middle phases on the stream with S2GU's read widths** under the
promise that its value passes `Φ_Q` at `E2` (`ref_decideGU` with `claimsU_rel`, the opening's atoms and widths). -/
theorem ref_decideGUX (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8) (hpub : pubG vk c sig = pubXT x) :
    RefAtPW capS occOfU shpS rwU20 sig 0 (decideProgUG P20U P20 N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))) x) (fun _ b ↦ b = true)
      (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecU (atomsOf P20 (openMainI P20))).length := by
  have hw : WAt rwU20 0 (wDecU (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwU20
    rw [widthsA_scheduleU] at h
    exact h
  have hacc : (pubXT x).accIn.pt.length = Typed.phiVarsT := length_pubOfW _ _ _ _ _ _
  have hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXT x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  exact ref_decideGU N Q lay H vk c x hpub _ (fun cl pp ↦ fol_openMain cl pp)
    (fun w hw' ↦ mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')) hw hacc hs
    (fun t a' hT tp k hk hsh hall ↦ claimsU_rel N Q lay H hσ x t a' hT tp k hk hsh hall)

/-- **V_S's S2GU public values are the statement's** (16-B `acc_in` scalars; the stream holds the header bytes). -/
theorem pubGU_eq {vk c : RecursionFast.Digest} {π : ByteArray} (h : parseOk P20U vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytesP P20U - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubG vk c sig = pubXT (xOfH (headerBytesP P20U) π) :=
  pubOfW_eq h fe16At 16 accVT (fun _ _ _ h ↦ fe16At_congr h) (hdrFix_le_P _)
    (by rw [headerBytesP_P20U.1]; decide) hsig

/-- `decideFUG` at `P20U` holds: the run's checks held and its folded claim passes `Φ_Q` at `E2`. -/
theorem decideFUG_ok {N : TNatT} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFUG P20U P20 N vk c sig = true) :
    (runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U))).2.ok = true ∧
      N.phiT ((runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U))).1.pt.map Lvm.e2OfFE) =
        Lvm.e2OfFE (runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U))).1.y := by
  unfold decideFUG DM.runOnH at h
  have e : (decideProgUG P20U P20 N vk c sig).run (RS.startH (headerBytesP P20U)) =
      runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U)) := rfl
  rw [e] at h
  rcases hr : runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U)) with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, fe2_beq h.2⟩

/-- **UTAPE-STMT 22's proof**: a `V_S` driving `decideFUG P20U P20 N` after `parseOk P20U` refines the specification's
scheme at `fmtU20`, the middle phases `midMk 4 relocU20 (midGU _)` (`refines_seqOfGO` at `occOfU` with
`ref_decideGUX`, `fol_PSOfU`, `stA_P20U`, `wAt_rwU20`). -/
theorem refinesU20_of (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (VS : Lvm.T.SProg)
    (hVS : ∀ vk c π, VS vk c π = if parseOk P20U vk c π then drive P20U π (decideFUG P20U P20 N vk c) else .ret false) :
    ∀ (vk : RecursionFast.Digest) (L : RecursionFast.Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      Lvm.T.isS π = true → (VS vk c π).runLog L = some true →
      ((Lvm.ASM.schemeSW Lvm.CT.fmtU20 vk
        (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.toT.fits
  exact fun vk L c π _ h ↦ runLog_of_seq (fun tr ht ↦ refines_seqOfGO
    (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))))
    (wDecU (atomsOf P20 (openMainI P20))).length P20U Lvm.CT.fmtU20 VS
    (fun vk c sig ↦ decideFUG P20U P20 N vk c sig) (decideProgUG P20U P20 N)
    (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (fun sig vk c x ↦ pubG vk c sig = pubXT x) hVS
    (fun _ _ _ hF ↦ decideFUG_ok hF) (fun _ _ _ _ hp hs ↦ pubGU_eq hp hs)
    (fun sig vk c x hpub ↦ ref_decideGUX N Q lay H hσ sig vk c x hpub) rfl rfl rfl
    (by rw [headerBytesP_P20U.1]; decide) (fun _ _ _ hp ↦ okS_of_parseOkH hp (hdrFix_le_P _))
    (fol_PSOfU relocU20 (N.inst Q lay) hl busDepth_P20 hr he) stA_P20U wAt_rwU20 vk c π tr ht) L h

end Lvm.VEq
