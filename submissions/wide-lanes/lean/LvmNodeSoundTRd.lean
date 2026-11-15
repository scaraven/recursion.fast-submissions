-- New for lvm2 (roll 8 = B1, L-D): `ReaddOk` on the memory read off a good pair's words (B1-S0's review item 7: "the
-- consistency of `mbT` with `z`", and QLT's static reads, B1-Q's `rowDef_of_static`). The committed reads are the
-- mini-bus's: WP-9's `mem_lookup` on `M3Holds` of the mini-bus's instance gives each read row a seed row, read off the
-- pair's commitments (`column_stackOf`, the seed's fixed address column); the static ones hold by the layout's alias and
-- QLT's address rows. Which `readd` instance is which, and that its cells are those rows' words, is `rdChkB`
-- (`LvmQTypedChk`, native).
import LvmM3Loop
import LvmNodeSoundT
import LvmAccNodePub
import LvmE2QNodeChkG
import LvmMPSig

-- ===== merged from `LvmNodeSoundTIn` (GOLF module merge: `LvmNodeSoundTIn.lean` is now a stub importing `LvmNodeSoundTRd`) =====
section
-- New for lvm2 (roll 8 = B1, L-D): the typed `NodeSound`'s input map on the memory read off a pair's words
-- (`memOf lay (zOf …)`, B-DES §2's new obligation "`Inputs` on the virtual regions"): QLT's cells are the layout's
-- constants (`StaticFactsT.cst`); every other input cell the map reads (`S_flat`'s stream, `σ′`, the lane-split `KS`
-- aliases, `PUB`) is read through its word's region (`zOf`), checked cell by cell natively (`inMapB`).

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

/-- QLT's constants (any configuration): `qltData` padded to the region. -/
theorem qltCst_eq (C : QCfg) : qltCst C = [(qtB C, qltData C.p (lay C) ++
    List.replicate (2 ^ C.aQT - (qltData C.p (lay C)).length) 0)] := by
  unfold qltCst
  rfl

/-- QLT's constants at `P20`: `qltData` padded to the region. -/
theorem qltCst20 : qltCst cfg20 = [(qtB cfg20, qltData cfg20.p (lay cfg20) ++
    List.replicate (2 ^ cfg20.aQT - (qltData cfg20.p (lay cfg20)).length) 0)] :=
  qltCst_eq cfg20

/-- **QLT's cells hold `qltData`** on the memory read off any words through a typed layout whose constants are QLT's
(any configuration; lvm2 E2-FT). -/
theorem hqltG (C : QCfg) (tl : Typed.Lay) (hcst : tl.cst = qltCst C) (z : ℕ → FK) (y : ℕ)
    (hy : y < (qltData C.p (lay C)).length) :
    (memOf tl z).k (qtB C + y) = (qltData C.p (lay C)).getD y 0 := by
  have hc := cst?_single tl (hcst.trans (qltCst_eq C)) (Nat.le_add_right _ y)
    (by rw [List.length_append]; omega)
  have e : qtB C + y - qtB C = y := by omega
  rw [e, List.getD_append _ _ _ _ hy] at hc
  exact memOf_cst tl z hc

theorem hqltT' (S : StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) (y : ℕ) (hy : y < (qltData cfg20.p (lay cfg20)).length) :
    (memT x qm qr).k (qtB cfg20 + y) = (qltData cfg20.p (lay cfg20)).getD y 0 :=
  hqltG cfg20 layT20 S.cst (zT x qm qr) y hy

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
    comCell_main (L := lay26) qm qr (show _ < 2 ^ 23 by simp only [CMain.sOff20]; (clear * - hn; omega)), wd, wd, hS n hn]

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
        (clear * - hp hoff hsrc; omega)
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

/-- **The input map from the check** at any stage (lvm2 E2-FT: any configuration `C`, the digest row `B − 1`,
`nPub` `PUB` lanes, any public values `pub`; generic in the instance; on a stream-block pair, with the region checks;
the stream's and `σ′`'s cells are checked on `S`'s `C_main` words): the bundles' cells and `PUB`'s. -/
theorem inMap_of_okG (B nPub : ℕ) (C : QCfg) (N : TNat) (Q : Program) (tl : Typed.Lay) (hlay : tl.Ok Q)
    (pub : Lvm.Pub) (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk tl = true) (hσ : SigInS N) (h : inMapBG B nPub C Q tl N = true) :
    let M := memOf tl ((N.inst Q tl).zOf lay26 pub qm qr)
    CellsAt M.k lay26 qm qr 17 14 (Lvm.QAsm.lay C).sb true (fun l ↦ l * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 1 10 (sigIn C).sg true (fun _ ↦ 17 * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 17 9 (sigIn C).xs false (fun l ↦ CMain.ksXW20 l 0) ∧
      CellsAt M.k lay26 qm qr 4 9 (sigIn C).ys false (fun l ↦ CMain.ksYW20 l (ksSplit P20)) ∧
      CellsAt M.k lay26 qm qr 4 0 (sigIn C).md false (fun l ↦ CMain.ksYW20 l (B - 1)) ∧
      ∀ j < nPub, M.k ((sigIn C).flag + j) = pub.hdrLanes.getD j 0 := by
  intro M
  simp only [inMapBG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hSt, hG⟩, hX⟩, hY⟩, hMd⟩, hP⟩ := h
  have e1 : (fun l r ↦ CTgt.cmain (CMain.sW20 l r)) =
      fun l r ↦ CTgt.cmain (CMain.sOff20 + (l * 2 ^ 14 + r)) := by
    funext l r; rw [CMain.sW20_eq]; simp only [CMain.sOff20]; exact congrArg CTgt.cmain (by (clear * -; omega))
  have e2 : (fun (_ : ℕ) r ↦ CTgt.cmain (CMain.sW20 17 r)) =
      fun (_ : ℕ) r ↦ CTgt.cmain (CMain.sOff20 + (17 * 2 ^ 14 + r)) := by
    funext l r; rw [CMain.sW20_eq]; simp only [CMain.sOff20]; exact congrArg CTgt.cmain (by (clear * -; omega))
  rw [e1] at hSt
  rw [e2] at hG
  have f1 : ∀ j < 17 * 2 ^ 14, j % 17 * 2 ^ 14 + j / 17 < 2 ^ 19 := fun j hj ↦ by omega
  have f2 : ∀ j < 1 * 2 ^ 10, 17 * 2 ^ 14 + j / 1 < 2 ^ 19 := fun j hj ↦ by omega
  refine ⟨bundleS_of_ok N Q tl hlay _ qm qr hS hok hl hσ f1 hSt,
    bundleS_of_ok N Q tl hlay _ qm qr hS hok hl hσ f2 hG,
    bundle_of_ok N Q tl hlay _ qm qr hS hok hl hσ (rec := false) hX,
    bundle_of_ok N Q tl hlay _ qm qr hS hok hl hσ (rec := false) hY,
    bundle_of_ok N Q tl hlay _ qm qr hS hok hl hσ (rec := false) hMd, fun j hj ↦ ?_⟩
  exact cell_of_ok N Q tl hlay pub qm qr hS hok hl hσ (List.all_eq_true.mp hP j (List.mem_range.mpr hj))

/-- `PUB`'s lanes of `pubX` are the header's (`hdrLanes_eq_pubX`). -/
theorem pubX_lane (x : List UInt8) {j : ℕ} (hj : j < pubLanes) : (pubX x).hdrLanes.getD j 0 = hdrLane x j := by
  rw [← hdrLanes_eq_pubX]
  simp [hdrLanes, List.getD_eq_getElem?_getD, hj]

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
  rw [inMapB_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := inMap_of_okG _ _ cfg20 N Q lay hlay (pubX x) qm qr hS hok hl hσ h
  exact ⟨h1, h2, h3, h4, h5, fun j hj ↦ (h6 j hj).trans (pubX_lane x hj)⟩

/-! ## At any stage -/

/-- **The input map on a pair's memory** at any stage (lvm2 E2-FT; `InMapMB B nPub` from the checks `inMapBG B nPub`,
on the memory read off the pair's words with the public values `pb x`; `vk` from `okS`; a stream-block pair, `σ′` in
`S`). The stage's facts: the digest row lies in `KS` (`hB`), the stream region fits the stream (`hm`), `PUB` covers
the header's lanes (`hn`) and holds them (`hpub`). -/
theorem inMapTG (B nPub : ℕ) (C : QCfg) (N : TNat) (Q : Program) (tl : Typed.Lay) (pb : List UInt8 → Lvm.Pub)
    (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true) (hσ : SigInS N)
    (hin : inMapBG B nPub C Q tl N = true) (hB : B ≤ 2 ^ 13) (hm : 2 ^ (lay C).m ≤ 17 * 2 ^ 14)
    (hn : pubLanes ≤ nPub) (hpub : ∀ x, ∀ j < nPub, (pb x).hdrLanes.getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} {x : List UInt8} (qm : Column CMain.nu20) (qr : Column 19) (hSB : SBlk qm qr)
    (hok : okS vk c x = true) (hb1 : (hdrOf x).b = 1) :
    InMapMB B nPub (lay C) (sigIn C) (memOf tl ((N.inst Q tl).zOf lay26 (pb x) qm qr)) vk x qm qr := by
  obtain ⟨hS, hG, hX, hY, hMd, hP⟩ := inMap_of_okG B nPub C N Q tl hlay (pb x) qm qr hSB hreg hl hσ hin
  have hP' : ∀ j < nPub, (memOf tl ((N.inst Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn C).flag + j) = hdrLane x j :=
    fun j hj ↦ (hP j hj).trans (hpub x j hj)
  have hPC : PubCells (memOf tl ((N.inst Q tl).zOf lay26 (pb x) qm qr)).k x (sigIn C).flag :=
    fun j hj ↦ hP' j (lt_of_lt_of_le hj hn)
  have hy := ys_v hY rfl rfl rfl
  exact ⟨fun j hj ↦ stream_v hS (lt_of_lt_of_le hj hm), flag_v hPC hb1, xs_v hX, hy.1, hy.2.1, hy.2.2.1,
    hy.2.2.2, (vk_v hPC).trans (okS_vk hok), cL_v hPC, sl_v hPC, md_vB hB hMd, sg_v hG, hd_v hS rfl, hP'⟩

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
  exact inMapTG _ _ cfg20 NT20 QB20 layT20 pubX S.hlay hreg S.hlayOk hσ (by rw [← inMapB_eq]; exact hin)
    (by rw [sizes_P20.2.2.2.2.2.2.2.2]; norm_num) hws20 le_rfl (fun x _ hj ↦ pubX_lane x hj) qm qr hSB hok hb1

end Lvm.NS
end
-- ===== end of `LvmNodeSoundTIn` =====

/-!
# `ReaddOk` on a good pair's memory

* **The mini-bus** (`mbRead_seeded`): with `M3Holds` of `inst L (mbTOf C F)` on the pair's stack, `LayOk`, and fewer
  than `2^64 − 1` reads, row `x` of the `k`-th read table (`capParams C F`'s `(τ, wa, wv)`) reads a seed: its address
  word holds `g^e` for the stream cell `e = sb + 17(q + x') + l` of a seed block `(l, q)` of `mbBlocks`, and its
  value word holds the seed's word (M′: `C_main`'s `sCol p l + q + x'`; B1: `C_rec`'s `l·2^14 + q + x'`) (`readTab`'s key `⟨g^3, col 0, [col 1]⟩` against
  `InArr.tab`'s `⟨g^3, fixed g^{base + 17x'}, [seed column]⟩`).
* **`readdOk_of_chk`**: with the guard's `rdChkB`, `inMapB` (M′: the stream's cells are `S`'s `C_main` words, read as
  `C_rec`'s on a stream-block pair, `SBlk`) and `mbSeedsOkB`, every
  `readd` instance of the B program has its `RowDef` on `memT`: a committed read through the mini-bus, a static read
  through the layout's alias (its result word is its target's) and its address (a QLT constant `g^e`, or QLT's `lin`
  address row `g^l·α`, whose `RowDef` is `hlin`'s: the non-`readd` rows hold by the wiring relation, L-B).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol LeanVM.Parameters
open Lvm.VEq (pubX)

/-! ## The mini-bus's tables -/

section MB

variable (C : QCfg) (F : TFrz)

theorem mbTOf_eq : mbTOf C F = (mbArrs C fun k ↦ (false, F.mbFin.getD k 0)).map InArr.tab ++
    capReads C F.wordK (fun k ↦ F.mbCnt.getD k 0) := rfl

/-- The `k`-th read table is `readTab` at `capParams`' parameters. -/
theorem capReads_get (wk cnt : ℕ → ℕ) (hwk : wk = F.wordK) {k τ wa wv : ℕ}
    (hk : (capParams C F)[k]? = some (τ, wa, wv)) :
    (capReads C wk cnt)[k]? = some (readTab τ wa wv (cnt k)) := by
  subst hwk
  simp only [capParams, List.getElem?_map, Option.map_eq_some_iff] at hk
  obtain ⟨y, hy, he⟩ := hk
  simp only [capReads, List.getElem?_map, List.getElem?_zipIdx, hy, Option.map_some, Nat.zero_add]
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  rw [h1, h2, h3]

/-- The tables with seeds are the seed arrays'. -/
theorem mbT_seeds {fin : ℕ → Bool × ℕ} {wk cnt : ℕ → ℕ} {ts : List Tab}
    (hts : ts = (mbArrs C fin).map InArr.tab ++ capReads C wk cnt) {j : ℕ} (hj : j < ts.length)
    (hs : (ts[j]'hj).seeds ≠ []) :
    ∃ hja : j < (mbArrs C fin).length, ts[j]'hj = ((mbArrs C fin).get ⟨j, hja⟩).tab := by
  have e : ts[j]? = ((mbArrs C fin).map InArr.tab ++ capReads C wk cnt)[j]? := by rw [hts]
  rw [List.getElem?_eq_getElem hj] at e
  rcases Nat.lt_or_ge j (mbArrs C fin).length with h | h
  · refine ⟨h, ?_⟩
    rw [List.getElem?_append_left (by rw [List.length_map]; exact h), List.getElem?_map,
      List.getElem?_eq_getElem h] at e
    exact Option.some.inj e
  · exfalso
    rw [List.getElem?_append_right (by rw [List.length_map]; exact h)] at e
    simp only [capReads, List.getElem?_map, List.length_map] at e
    obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.mp e.symm
    apply hs
    rw [← hy]
    rfl

/-- The reads' count columns lie inside their tables. -/
theorem mbT_cnt (fin : ℕ → Bool × ℕ) (wk cnt : ℕ → ℕ) :
    ∀ t ∈ mbT C wk fin cnt, ∀ r ∈ t.reads, r.2 < t.w := by
  intro t ht r hr
  simp only [mbT, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨a, -, rfl⟩ | ht
  · simp [InArr.tab] at hr
  · simp only [capReads, List.mem_map] at ht
    obtain ⟨_, -, rfl⟩ := ht
    simp only [readTab, List.mem_singleton] at hr
    subst hr
    simp [Tab.w, readTab]

end MB

/-! ## Rows of the instance -/

section Rows

variable {L : Lvm.M3.Lay} {ts : List Tab} {hτ : ∀ t ∈ ts, t.τ ≤ L.μ}

theorem row_fixedI (q : Column L.μ) (j : Fin ts.length) (x : Fin (2 ^ (ts.get j).τ)) (i : Fin (ts.get j).w)
    {f : ℕ → FK} (hf : (ts.get j).fixedOf i = some f) : (inst L ts hτ).row q j x i = FK.toBF64 (f x) := by
  simp only [M3Instance.row, M3Instance.column, inst, hf, Option.map_some, Option.elim_some, fixedColumn,
    Vector.get_ofFn]

theorem row_comI (hlay : LayOk L ts) (qm : Column L.nuMain) (qr : Column L.nuRec) (j : Fin ts.length)
    (x : Fin (2 ^ (ts.get j).τ)) (i : Fin (ts.get j).w) {rec : Bool} {off : ℕ}
    (hcol : (ts.get j).cols[i.val]? = some (.com rec off)) :
    (inst L ts hτ).row (stackOf L qm qr) j x i = comCell L qm qr rec (off + x.val) := by
  simp only [M3Instance.row]
  rw [column_stackOf L ts hτ hlay qm qr j i hcol]
  simp [comBlock, Vector.get, Array.getElem_ofFn]
  rfl

/-- Coordinate `1` (the address) of an evaluated key. -/
theorem evalV_vec_one {w : ℕ} (r : Fin w → K) (k : Key) (cnt : CPoly) :
    (evalV r (k.vec w cnt))[1] = CPoly.evalB (CPoly.ext r) k.addr := by
  simp [evalV, Key.vec, CPoly.eval_toMv]

/-- Coordinate `3` (the first value limb) of an evaluated key. -/
theorem evalV_vec_three {w : ℕ} (r : Fin w → K) (k : Key) (cnt : CPoly) :
    (evalV r (k.vec w cnt))[3] = CPoly.evalB (CPoly.ext r) (k.val.getD 0 []) := by
  simp [evalV, Key.vec, CPoly.eval_toMv]

theorem evalB_var (v : ℕ → K) (i : ℕ) : CPoly.evalB v (CPoly.var i) = v i := by
  simp [CPoly.evalB, CPoly.var, FK.toBF64_one]

end Rows

/-! ## The mini-bus reads only seeds -/

/-- **A mini-bus read row reads a seed** (see the module docstring; M′ `S2GM`: the seed is `C_main`'s stream-block
word `sCol p l + q + x'`, B1: `C_rec`'s `l·2^14 + q + x'`). -/
theorem mbRead_seeded (C : QCfg) (F : TFrz) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ mbTOf C F, t.τ ≤ L.μ)
    (qm : Column L.nuMain) (qr : Column L.nuRec) (hlay : LayOk L (mbTOf C F))
    (hM : M3Holds (inst L (mbTOf C F) hτ) () (stackOf L qm qr)) (hlen : nReads (mbTOf C F) < 2 ^ 64 - 1)
    {k τ wa wv : ℕ} (hk : (capParams C F)[k]? = some (τ, wa, wv)) {x : ℕ} (hx : x < 2 ^ τ) :
    ∃ lq ∈ mbBlocks C.p, ∃ x' < 2 ^ mbBlk,
      comCell L qm qr false (wa + x) = FK.toBF64 (FK.x ^ ((lay C).sb + 17 * lq.2 + lq.1 + 17 * x')) ∧
      comCell L qm qr false (wv + x) = comCell L qm qr false (Lvm.sCol C.p lq.1 + lq.2 + x') := by
  have hk' := capReads_get C F F.wordK (fun k ↦ F.mbCnt.getD k 0) rfl hk
  have hkl : k < (capReads C F.wordK (fun k ↦ F.mbCnt.getD k 0)).length := (List.getElem?_eq_some_iff.mp hk').1
  have hlen0 := mbTOf_eq C F
  have hg0 : (mbTOf C F)[(mbArrs C fun k ↦ (false, F.mbFin.getD k 0)).length + k]? =
      some (readTab τ wa wv (F.mbCnt.getD k 0)) := by
    rw [mbTOf_eq, List.getElem?_append_right (by simp)]
    simpa using hk'
  generalize hts : mbTOf C F = ts at hτ hlay hM hlen hlen0 hg0
  obtain ⟨hj, hget0⟩ := List.getElem?_eq_some_iff.mp hg0
  have hget : ts.get ⟨_, hj⟩ = readTab τ wa wv (F.mbCnt.getD k 0) := by
    simp only [List.get_eq_getElem]; exact hget0
  have hτj : (ts.get ⟨_, hj⟩).τ = τ := by rw [hget]; rfl
  have hxj : x < 2 ^ (ts.get ⟨_, hj⟩).τ := lt_of_lt_of_eq hx (by rw [hτj])
  -- the read tuple
  have hrd : (readKey, 2) ∈ (ts.get ⟨_, hj⟩).reads := by rw [hget]; simp [readTab]
  have hu : evalV ((inst L ts hτ).row (stackOf L qm qr) ⟨_, hj⟩ ⟨x, hxj⟩)
      ((ts.get ⟨_, hj⟩).readVec (readKey, 2)) ∈ readTuples L ts hτ (stackOf L qm qr) := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, ⟨x, hxj⟩, ?_, rfl⟩
    simp only [M3Instance.executed_eq, List.mem_map, List.mem_finRange, true_and]
    exact ⟨⟨x, by simpa [inst] using hxj⟩, rfl⟩
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L ts hτ (stackOf L qm qr) hM.2.1 hM.2.2.1
    (by rw [hlen0]; exact mbT_cnt C _ _ _) hlen _ hu)
  -- the seed tuple
  simp only [seedTuples, partT, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨⟨jv, hjv⟩, -, v, ⟨sd, hsd, rfl⟩, x', -, rfl⟩ := hs
  have hsd0 : sd ∈ ts[jv].seeds := by simpa [List.get_eq_getElem] using hsd
  have hne : (ts[jv]).seeds ≠ [] := List.ne_nil_of_mem hsd0
  obtain ⟨hja, hta⟩ := mbT_seeds C hlen0 hjv hne
  have hgetS : ts.get ⟨jv, hjv⟩ = ((mbArrs C fun k ↦ (false, F.mbFin.getD k 0)).get ⟨jv, hja⟩).tab := by
    simp only [List.get_eq_getElem]; exact hta
  have hjb : jv < (mbBlocks C.p).length := by
    have := hja; simp only [mbArrs, List.length_map, List.length_zipIdx] at this; exact this
  obtain ⟨lq, hlq⟩ : ∃ lq, (mbBlocks C.p).get ⟨jv, hjb⟩ = lq := ⟨_, rfl⟩
  have harr : (mbArrs C fun k ↦ (false, F.mbFin.getD k 0)).get ⟨jv, hja⟩ = ⟨.K, mbBlk,
      (lay C).sb + 17 * lq.2 + lq.1, 17, [(false, Lvm.sCol C.p lq.1 + lq.2)], (false, F.mbFin.getD jv 0), none⟩ := by
    rw [← hlq]
    simp only [mbArrs, List.get_eq_getElem, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have hsd' : sd = (⟨sep .K, CPoly.var 2, [CPoly.var 0]⟩, 1) := by
    rw [hta, harr] at hsd0
    simpa [InArr.tab] using hsd0
  have hτs : (ts.get ⟨jv, hjv⟩).τ = mbBlk := by rw [hgetS, harr]; rfl
  have hx'τ : x'.val < 2 ^ mbBlk := lt_of_lt_of_eq x'.isLt (by rw [hτs])
  refine ⟨lq, hlq ▸ List.get_mem _ _, x'.val, hx'τ, ?_, ?_⟩
  · -- the addresses
    have h1 := keyT_coord hks 1 (by norm_num) (by norm_num)
    simp only [Tab.seedVec, Tab.readVec] at h1
    rw [evalV_vec_one, evalV_vec_one, hsd'] at h1
    simp only [readKey, evalB_var, CPoly.ext] at h1
    have hw0 : 0 < (ts.get ⟨_, hj⟩).w := by rw [hget]; simp [readTab, Tab.w]
    have hw2 : 2 < (ts.get ⟨jv, hjv⟩).w := by rw [hgetS, harr]; simp [InArr.tab, Tab.w, InArr.vcols]
    rw [dif_pos hw2, dif_pos hw0] at h1
    have ec : (ts.get ⟨_, hj⟩).cols[0]? = some (.com false wa) := by rw [hget]; rfl
    have ef : (ts.get ⟨jv, hjv⟩).fixedOf 2 =
        some (fun y ↦ FK.x ^ ((lay C).sb + 17 * lq.2 + lq.1 + 17 * y)) := by
      rw [hgetS, harr]; rfl
    rw [row_fixedI _ _ x' ⟨2, hw2⟩ ef, row_comI hlay qm qr _ _ ⟨0, hw0⟩ ec] at h1
    exact h1.symm
  · -- the values
    have h3 := keyT_coord hks 3 (by norm_num) (by norm_num)
    simp only [Tab.seedVec, Tab.readVec] at h3
    rw [evalV_vec_three, evalV_vec_three, hsd'] at h3
    simp only [readKey, List.getD_cons_zero, evalB_var, CPoly.ext] at h3
    have hw1 : 1 < (ts.get ⟨_, hj⟩).w := by rw [hget]; simp [readTab, Tab.w]
    have hw0 : 0 < (ts.get ⟨jv, hjv⟩).w := by rw [hgetS, harr]; simp [InArr.tab, Tab.w, InArr.vcols]
    rw [dif_pos hw0, dif_pos hw1] at h3
    have ec : (ts.get ⟨_, hj⟩).cols[1]? = some (.com false wv) := by rw [hget]; rfl
    have es : (ts.get ⟨jv, hjv⟩).cols[0]? =
        some (.com false (Lvm.sCol C.p lq.1 + lq.2)) := by
      rw [hgetS, harr]; rfl
    rw [row_comI hlay qm qr _ _ ⟨0, hw0⟩ es, row_comI hlay qm qr _ _ ⟨1, hw1⟩ ec] at h3
    exact h3.symm

/-! ## `ReaddOk` from the check -/

/-- **The non-`readd` rows hold** on a memory (the wiring relation's: L-B's `holds_of_wiring` argument without
`ReaddOk`; QLT's address rows are `lin` rows). -/
def NonReaddHolds (Q : Program) (M : Mem) : Prop :=
  ∀ i ∈ Q.insts, (∀ lo m, i.row.op ≠ .readd lo m) → Q.RowDef M i

theorem cells_ge_nInK (Q : Program) : Q.nInK ≤ Q.cells .K := by
  simp only [Program.cells, Program.start, Program.nIn]; omega

/-- `zipIdx`'s `all` at an index. -/
theorem all_zipIdx {α : Type} {l : List α} {f : α × ℕ → Bool} (h : l.zipIdx.all f = true) {i : ℕ}
    (hi : i < l.length) : f (l[i], i) = true :=
  List.all_eq_true.mp h _ (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))

/-- **`ReaddOk` from the native check** (generic in the program and the layout): with the mini-bus's rows reading
seeds (`hbus`), the seeds' cells holding their words (`hseed`; M′: `C_main`'s stream-block words `sCol`) and the non-`readd` rows (`hlin`), every
`readd` instance that `rdChkB` classifies has its `RowDef` on the memory read off the pair's words. -/
theorem readdOk_of_chk (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) (hlay : lay.Ok Q)
    (pub : Lvm.Pub) (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlk qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInS N) (hchk : rdChkB C F Q lay N = true)
    (hbus : ∀ τ wa wv, (τ, wa, wv) ∈ capParams C F → ∀ x < 2 ^ τ,
      ∃ lq ∈ mbBlocks C.p, ∃ x' < 2 ^ mbBlk,
        comCell lay26 qm qr false (wa + x) = FK.toBF64 (FK.x ^ ((Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x')) ∧
        comCell lay26 qm qr false (wv + x) = comCell lay26 qm qr false (Lvm.sCol C.p lq.1 + lq.2 + x'))
    (hseed : ∀ lq ∈ mbBlocks C.p, ∀ x' < 2 ^ mbBlk,
      (Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x' < Q.cells .K ∧
      (memOf lay ((N.inst Q lay).zOf lay26 pub qm qr)).k ((Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x') =
        FK.ofBF64 (comCell lay26 qm qr false (Lvm.sCol C.p lq.1 + lq.2 + x')))
    (hlin : NonReaddHolds Q (memOf lay ((N.inst Q lay).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf lay ((N.inst Q lay).zOf lay26 pub qm qr)) := by
  intro i hi lo m hop
  obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
  have hB : Q.blk b = Q.blocks[b] := by simp [Program.blk, List.getD_eq_getElem?_getD, hb]
  have hrow : (Q.blk b).tpl.getD t default = (Q.blk b).tpl[t] := by
    simp [List.getD_eq_getElem?_getD, ht]
  have h1 := all_zipIdx hchk hb
  rw [← hB] at h1
  have h2 := all_zipIdx h1 ht
  have hop' : ((Q.blk b).tpl[t]).op = .readd lo m := by rw [← hrow]; exact hop
  simp only [hop'] at h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h2
  obtain ⟨⟨hty, haty⟩, hjs⟩ := h2
  have hj := hjs jf hjf
  -- the instance's cells
  set M := memOf lay ((N.inst Q lay).zOf lay26 pub qm qr)
  have harg : (M.arg (Q.inst b jf t) 0).c₀ = M.k ((((Q.blk b).tpl[t]).args.getD 0 default).at
      (unflat (Q.blk b).dims jf)) := by
    simp only [Mem.arg, Inst.arg, Program.inst, hrow, haty, Mem.rd]; rfl
  unfold Program.RowDef
  simp only [Program.inst, hrow, hop', hty]
  simp only [Program.inst, hrow] at harg
  revert hj
  split
  · -- a static read
    rename_i tgt _
    intro hj
    simp only [aliasOkB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hj
    obtain ⟨⟨⟨⟨he, hce⟩, hcc⟩, hw⟩, hadr⟩ := hj
    rw [K.fl_cst] at hce hcc
    rw [K.fl_cst] at hadr
    rw [K.fl_wordK Q lay hlay, K.fl_wordK Q lay hlay] at hw
    refine ⟨tgt.getD jf 0, lt_of_lt_of_le he (cells_ge_nInK Q), ?_, ?_⟩
    · rw [harg]
      rcases hadr with hc | hl
      · rw [memOf_cst lay _ hc]; rfl
      · -- QLT's address row: `a = g^l·α`, `α = g^{e−l}` a constant
        simp only [linOkB, List.any_eq_true] at hl
        obtain ⟨⟨r', t'⟩, hmem, hx⟩ := hl
        have hr' := List.mk_mem_zipIdx_iff_getElem?.mp hmem
        have ht' : t' < (Q.blk b).tpl.length := (List.getElem?_eq_some_iff.mp hr').1
        have hrw : (Q.blk b).tpl.getD t' default = r' := by
          simp [List.getD_eq_getElem?_getD, hr']
        rcases hop1 : r'.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo', m'⟩ <;>
          simp only [hop1, Bool.false_eq_true] at hx
        rcases hargs : r'.args with _ | ⟨α₀, _ | ⟨α₁, _ | ⟨_, _⟩⟩⟩ <;>
          simp only [hargs, Bool.false_eq_true] at hx
        simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_cons, List.mem_nil_iff,
          or_false, decide_eq_true_eq] at hx
        obtain ⟨⟨⟨⟨⟨⟨hty', hk'⟩, h0⟩, h1⟩, hα⟩, hck⟩, l, -, ⟨hle, hkl⟩, hcα⟩ := hx
        have hi' : Q.inst b jf t' ∈ Q.insts := (Q.mem_insts _).mpr ⟨b, hb, jf, hjf, t', ht', rfl⟩
        have hop2 : ∀ lo m, (Q.inst b jf t').row.op ≠ .readd lo m := by
          intro lo m h; simp only [Program.inst, hrw, hop1] at h; cases h
        have hR := hlin _ hi' hop2
        unfold Program.RowDef at hR
        simp only [Program.inst, hrw, hop1, Mem.res, Mem.arg, Inst.arg, hargs, hty', Inst.clock, hck,
          List.getD_cons_zero, List.getD_cons_succ, h0, h1, Mem.rd, hα, hk'] at hR
        rw [K.fl_cst, hα] at hcα
        have hg : M.k (α₁.at (unflat (Q.blk b).dims jf)) = Build.gpow (tgt.getD jf 0 - l) := memOf_cst lay _ hcα
        rw [hg, hkl, ← Build.ofK_mul, ← Build.ofK_add, ← Build.ofK_add] at hR
        have hv := Build.ofK_inj hR
        rw [gpow_scale l (tgt.getD jf 0 - l), Nat.sub_add_cancel hle] at hv
        exact hv.symm
    · simp only [Mem.res, hty, Inst.clock, Mem.rd]
      rw [memOf_k, memOf_k, hcc, hce, hw]
  · -- a committed read
    intro hj
    simp only [capOkB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hj
    obtain ⟨⟨τ, wa, wv⟩, hp, ⟨hjτ, ha⟩, hc⟩ := hj
    obtain ⟨lq, hlq, x', hx', hA, hV⟩ := hbus τ wa wv hp jf hjτ
    obtain ⟨hlt, hse⟩ := hseed lq hlq x' hx'
    refine ⟨_, hlt, ?_, ?_⟩
    · rw [harg, cell_of_ok N Q lay hlay pub qm qr hS hok hl hσ ha]
      show FK.x ^ _ = FK.ofBF64 (comCell lay26 qm qr false (wa + jf))
      rw [hA]; rfl
    · simp only [Mem.res, hty, Inst.clock, Mem.rd]
      rw [cell_of_ok N Q lay hlay pub qm qr hS hok hl hσ hc, hse]
      show FE.ofK (FK.ofBF64 (comCell lay26 qm qr false (wv + jf))) = _
      rw [hV]

end Lvm.NS
