-- New for lvm2 (roll 8 = B1, L-D): the typed `NodeSound`'s input map on the memory read off a pair's words
-- (`memOf lay (zOf …)`, B-DES §2's new obligation "`Inputs` on the virtual regions"): QLT's cells are the layout's
-- constants (`StaticFactsT.cst`); every other input cell the map reads (`S_flat`'s stream, `σ′`, the lane-split `KS`
-- aliases, `PUB`) is read through its word's region (`zOf`), checked cell by cell natively (`inMapB`).
import LvmNodeSoundT
import LvmAccNodePub
import LvmQTypedChk
import LvmMPSig

/-!
# The typed input map

* **QLT** (`hqltT`): `lay.cst = qltCst C` (the guard's `StaticFactsT.cst`) makes QLT's cells `qltData`'s values.
* **The other input cells** go through `memOf`: a cell with no constant is `z (lay.wordK c)`, and `zOf` reads the
  word's region: `S_flat`'s and `σ′`'s `C_rec` word, a `KS` alias's or a committed word's `C_main` word, `PUB`'s header
  lane. **`tgtN N lay y`** is that target, as V_S's native instance `N` (`TNat.inst N Q lay`) has it;
  **`cellOkB F lay N c t`**: cell `c` has no constant and its word's target is `t`. **`cell_of_ok`**: then
  `memOf`'s cell is `t`'s value (generic in the instance, so the kernel never meets `zOf`'s match at a closed one).
* **`inMapB C Q lay N`** (natively, at start-up; through the layout's array caches `K.FL`): every cell of the input
  map's bundles (`stream`, `σ′`, `xs`, `ys`, `md`) and of `PUB` has its target. **`inMapT`**: with it, `InMapM` on
  `memT` (`LvmNodeSoundFields`' fields, `hdrLanes_eq_pubX` for `PUB`).

`inMapB` reaches the proof through the guard: `nodeChkB` (`LvmQTypedChk`), L-W's `SF20.chk`.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-! ## Constants -/

/-- A cell of a layout's one constant region. -/
theorem cst?_single (lay : Typed.Lay) {lo : ℕ} {vs : List FK} (h : lay.cst = [(lo, vs)]) {n : ℕ}
    (h1 : lo ≤ n) (h2 : n < lo + vs.length) : lay.cst? n = some (vs.getD (n - lo) 0) := by
  unfold Lay.cst?
  rw [h]
  simp [h1, h2]

/-- A `K` cell of `memOf` is its constant, if any, else its word's value. -/
theorem memOf_k (lay : Typed.Lay) (z : ℕ → FK) (n : ℕ) :
    (memOf lay z).k n = (lay.cst? n).getD (z (lay.wordK n)) := rfl

/-- A constant cell of `memOf`. -/
theorem memOf_cst (lay : Typed.Lay) (z : ℕ → FK) {n : ℕ} {v : FK} (h : lay.cst? n = some v) :
    (memOf lay z).k n = v := by
  rw [memOf_k, h]; rfl

/-- QLT's constants at `P20`: `qltData` padded to the region. -/
theorem qltCst20 : qltCst cfg20 = [(qtB cfg20, qltData cfg20.p (lay cfg20) ++
    List.replicate (2 ^ cfg20.aQT - (qltData cfg20.p (lay cfg20)).length) 0)] := by
  unfold qltCst
  rfl

theorem hqltT' (S : StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) (y : ℕ) (hy : y < (qltData cfg20.p (lay cfg20)).length) :
    (memT x qm qr).k (qtB cfg20 + y) = (qltData cfg20.p (lay cfg20)).getD y 0 := by
  have hc := cst?_single layT20 (S.cst.trans qltCst20) (Nat.le_add_right _ y)
    (by rw [List.length_append]; omega)
  have e : qtB cfg20 + y - qtB cfg20 = y := by omega
  rw [e, List.getD_append _ _ _ _ hy] at hc
  exact memOf_cst layT20 (zT x qm qr) hc

/-- **QLT's cells hold `qltData`** on the memory of any pair (the guard's `lay.cst = qltCst`). -/
theorem hqltT (S : StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) :
    ∀ y < (qltData P20 (lay cfg20)).length,
      (memT x qm qr).k ((lay cfg20).qt + y) = (qltData P20 (lay cfg20)).getD y 0 :=
  hqltT' S x qm qr

/-! ## A cell through its word's region -/

/-- The value of a target on a pair (statement `pub`). -/
def _root_.Lvm.QTyped.CTgt.val (L : Lvm.M3.Lay) (pub : Lvm.Pub) (qm : Column L.nuMain) (qr : Column L.nuRec) : CTgt → FK
  | .crec w => FK.ofBF64 (comCell L qm qr true w)
  | .cmain w => FK.ofBF64 (comCell L qm qr false w)
  | .cpub k => pub.hdrLanes.getD k 0

/-- A `C_rec` word of a stream-block pair is its `C_main` word in `S`. -/
theorem comCell_S {qm : Column CMain.nu20} {qr : Column 19} (hS : SBlk qm qr) {n : ℕ} (hn : n < 2 ^ 19) :
    comCell lay26 qm qr true n = comCell lay26 qm qr false (CMain.sOff20 + n) := by
  rw [comCell_rec (L := lay26) qm qr hn,
    comCell_main (L := lay26) qm qr (show _ < 2 ^ 23 by simp only [CMain.sOff20]; omega), wd, wd, hS n hn]

/-- **`zOf` at a word with a target** (generic in the instance; M′ `S2GM`: the targets are on `C_main`, so the pair
is a stream-block pair, and the region checks place `S_flat` within `2^19` words and `σ′` in `S`). B1: no
hypothesis, any `L`, `S_flat` and `σ′` on `C_rec`. -/
theorem zOf_of_tgt (N : TNat) (Q : Program) (lay : Typed.Lay) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInS N) {y : ℕ} {t : CTgt} (h : tgtN N lay y = some t) :
    (N.inst Q lay).zOf lay26 pub qm qr y = t.val lay26 pub qm qr := by
  have hsrc := src?_inst N Q lay hl y
  unfold TInst.zOf
  unfold tgtN at h
  have ho : Lvm.QTyped.offN N y = N.off y := rfl
  rw [ho] at h
  rw [show (lay.yregs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src) =
    (N.inst Q lay).src? y from rfl, hsrc] at h
  rw [hsrc]
  cases hr : N.regAt y with
  | none => simp [hr] at h
  | some g =>
    simp only [hr, Option.map_some] at h ⊢
    have hp := List.find?_some hr
    simp only [decide_eq_true_eq] at hp
    have hoff : N.off y = g.dst + (y - g.base) := by simp [TNat.off, hr]
    have hmem : g ∈ N.regs := List.mem_of_find?_eq_some hr
    cases hs : g.src <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · -- `com`
      rfl
    · -- `S_flat`: a position below `2^19`, its block word in `S`
      have hlt : N.off y < 2 ^ 19 := by
        unfold TNat.okB at hok
        simp only [Bool.and_eq_true, List.all_eq_true] at hok
        have hr' := hok.1.1.1.1.1 g hmem
        simp only [beq_iff_eq, decide_eq_true_eq] at hr'
        obtain ⟨-, hsrc⟩ := hr'
        simp only [hs, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, posBits] at hsrc
        omega
      have hw : sflatWord (N.off y) < 2 ^ 19 := by
        unfold sflatWord
        split <;> simp only [sPos, sLanes, recRowBits, recStreamCols] at * <;> omega
      show FK.ofBF64 (comCell lay26 qm qr true (sflatWord (N.off y))) = _
      rw [comCell_S hS hw]
      rfl
    · -- `PUB`
      rfl
    · -- `σ′`: its region lies in `S` (`SigInS`)
      obtain ⟨he, hlt, -, -⟩ := off_sigma hσ hr hs
      show FK.ofBF64 (comCell lay26 qm qr true (N.off y % 2 ^ 19)) = _
      rw [comCell_S hS hlt, ← he]
      rfl
    · -- `ks`
      rfl

/-- **A checked cell of the memory read off a pair's words is its target's value** (generic in the instance; M′: on
a stream-block pair, with the region checks). -/
theorem cell_of_ok (N : TNat) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInS N) {c : ℕ} {t : CTgt}
    (h : cellOkB (K.FL.ofLay Q lay) lay N c t = true) :
    (memOf lay ((N.inst Q lay).zOf lay26 pub qm qr)).k c = t.val lay26 pub qm qr := by
  simp only [cellOkB, Bool.and_eq_true, beq_iff_eq] at h
  rw [K.fl_cst, K.fl_wordK Q lay hlay] at h
  rw [memOf_k, h.1, Option.getD_none, zOf_of_tgt N Q lay pub qm qr hS hok hl hσ h.2]

/-! ## The input map's check -/

theorem bundle_of_ok (N : TNat) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInS N) {s τ base : ℕ} {rec : Bool} {off : ℕ → ℕ}
    (h : bundleOkB (K.FL.ofLay Q lay) lay N s τ base
      (fun l r ↦ if rec then CTgt.crec (off l + r) else CTgt.cmain (off l + r)) = true) :
    CellsAt (memOf lay ((N.inst Q lay).zOf lay26 pub qm qr)).k lay26 qm qr s τ base rec off := by
  intro j hj
  have hc := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [cell_of_ok N Q lay hlay pub qm qr hS hok hl hσ hc]
  cases rec <;> rfl

/-- **A bundle checked on `S`'s words is the stream block's** (M′: `C_main`'s targets `sOff20 + w`, read as the
`C_rec` words `w` of a stream-block pair). -/
theorem bundleS_of_ok (N : TNat) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInS N) {s τ base : ℕ} {off : ℕ → ℕ}
    (hfit : ∀ j < s * 2 ^ τ, off (j % s) + j / s < 2 ^ 19)
    (h : bundleOkB (K.FL.ofLay Q lay) lay N s τ base (fun l r ↦ CTgt.cmain (CMain.sOff20 + (off l + r))) = true) :
    CellsAt (memOf lay ((N.inst Q lay).zOf lay26 pub qm qr)).k lay26 qm qr s τ base true off := by
  intro j hj
  have hc := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [cell_of_ok N Q lay hlay pub qm qr hS hok hl hσ hc]
  show FK.ofBF64 (comCell lay26 qm qr false (CMain.sOff20 + (off (j % s) + j / s))) = _
  rw [comCell_S hS (hfit j hj)]

/-- **The input map from the check** (generic in the instance; M′ `S2GM`: on a stream-block pair, with the region
checks; the stream's and `σ′`'s cells are checked on `S`'s `C_main` words): the bundles' cells and `PUB`'s, as
`LvmNodeSoundFields`' `CellsAt`/`PubCells`. -/
theorem inMap_of_ok (N : TNat) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInS N) (h : inMapB cfg20 Q lay N = true) :
    let M := memOf lay ((N.inst Q lay).zOf lay26 (pubX x) qm qr)
    CellsAt M.k lay26 qm qr 17 14 (Lvm.QAsm.lay cfg20).sb true (fun l ↦ l * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 1 10 (sigIn cfg20).sg true (fun _ ↦ 17 * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 17 9 (sigIn cfg20).xs false (fun l ↦ CMain.ksXW20 l 0) ∧
      CellsAt M.k lay26 qm qr 4 9 (sigIn cfg20).ys false (fun l ↦ CMain.ksYW20 l (ksSplit P20)) ∧
      CellsAt M.k lay26 qm qr 4 0 (sigIn cfg20).md false (fun l ↦ CMain.ksYW20 l (spongeBlocks P20 - 1)) ∧
      PubCells M.k x (sigIn cfg20).flag := by
  intro M
  simp only [inMapB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hSt, hG⟩, hX⟩, hY⟩, hMd⟩, hP⟩ := h
  have e1 : (fun l r ↦ CTgt.cmain (CMain.sW20 l r)) =
      fun l r ↦ CTgt.cmain (CMain.sOff20 + (l * 2 ^ 14 + r)) := by
    funext l r; rw [CMain.sW20_eq]; simp only [CMain.sOff20]; exact congrArg CTgt.cmain (by omega)
  have e2 : (fun (_ : ℕ) r ↦ CTgt.cmain (CMain.sW20 17 r)) =
      fun (_ : ℕ) r ↦ CTgt.cmain (CMain.sOff20 + (17 * 2 ^ 14 + r)) := by
    funext l r; rw [CMain.sW20_eq]; simp only [CMain.sOff20]; exact congrArg CTgt.cmain (by omega)
  rw [e1] at hSt
  rw [e2] at hG
  have f1 : ∀ j < 17 * 2 ^ 14, j % 17 * 2 ^ 14 + j / 17 < 2 ^ 19 := fun j hj ↦ by omega
  have f2 : ∀ j < 1 * 2 ^ 10, 17 * 2 ^ 14 + j / 1 < 2 ^ 19 := fun j hj ↦ by omega
  refine ⟨bundleS_of_ok N Q lay hlay _ qm qr hS hok hl hσ f1 hSt,
    bundleS_of_ok N Q lay hlay _ qm qr hS hok hl hσ f2 hG,
    bundle_of_ok N Q lay hlay _ qm qr hS hok hl hσ (rec := false) hX,
    bundle_of_ok N Q lay hlay _ qm qr hS hok hl hσ (rec := false) hY,
    bundle_of_ok N Q lay hlay _ qm qr hS hok hl hσ (rec := false) hMd, fun j hj ↦ ?_⟩
  have hc := List.all_eq_true.mp hP j (List.mem_range.mpr hj)
  rw [cell_of_ok N Q lay hlay (pubX x) qm qr hS hok hl hσ hc]
  show (pubX x).hdrLanes.getD j 0 = hdrLane x j
  rw [← hdrLanes_eq_pubX]
  simp [hdrLanes, List.getD_eq_getElem?_getD, hj]

/-! ## At `P20` -/

/-- **The input map on a pair's memory** at `P20`, from the checks (`InMapM`; `vk` from `okS`; M′: a stream-block
pair, `σ′` in `S` from the guard's `sigInSB`). -/
theorem inMapT (S : StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20)
    (hin : inMapB cfg20 QB20 layT20 NT20 = true) (hσ : SigInS NT20) {vk c : RecursionFast.Digest} {x : List UInt8}
    (qm : Column CMain.nu20) (qr : Column 19) (hSB : SBlk qm qr) (hok : okS vk c x = true)
    (hb1 : (hdrOf x).b = 1) :
    InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr := by
  have hreg : NT20.okB 23 19 = true := by
    have h := S.regs
    rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, show P20.nuMain = 23 by decide +kernel,
      show P20.nuRec = 19 by decide +kernel] at h
  obtain ⟨hS, hG, hX, hY, hMd, hP⟩ := inMap_of_ok NT20 QB20 layT20 S.hlay x qm qr hSB hreg S.hlayOk hσ hin
  have hy := ys_v hY hyc20 hyls20 hyns20
  have e1 : (sigIn cfg20).vk = (sigIn cfg20).flag + 1 := by rw [hvkI20, hfl20]
  have e5 : (sigIn cfg20).cL = (sigIn cfg20).flag + 5 := by rw [hcLI20, hfl20]
  have e18 : (sigIn cfg20).sl = (sigIn cfg20).flag + 18 := by rw [hslI20, hfl20]
  exact ⟨fun j hj ↦ stream_v hS (lt_of_lt_of_le hj hws20), flag_v hP hb1, xs_v hX, hy.1, hy.2.1, hy.2.2.1,
    hy.2.2.2, by rw [e1]; exact (vk_v hP).trans (okS_vk hok), by rw [e5]; exact cL_v hP,
    by rw [e18]; exact sl_v hP, md_v hMd, sg_v hG, hd_v hS hhd20, hP⟩

end Lvm.NS
