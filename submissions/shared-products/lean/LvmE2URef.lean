-- New for lvm2 U-TAPE (UT-V, UTAPE-STMT 22): V_S's S2GU decision (`decideProgUG P20U P20`, the fast twins) refines
-- the pinned S2GU middle phases on the stream with S2GU's read widths, at S2GU's occupied words `occOfU`.
import LvmE2UEq
import LvmE2VDecRef
import LvmE2TVEq
import LvmE2TRegReloc
import LvmS2GUFol
import LvmE2VTopF

-- (SLF-K: 26 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

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
  exact RetD.bind_true fun _ ↦ RetD.pure (congrArg (z.map ·) (funext tColsWF_eq))

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

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

end Ref

/-! ## The pinned middle phases and the decision at S2GU -/

theorem smallT_P20U (x : List UInt8) : TypedV.smallT P20U (pubXT x) = Shape.small x := smallP_P20 x

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

/-! ## The decision at S2GU, assembled -/

end Lvm.VEq
