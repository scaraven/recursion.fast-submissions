-- New for lvm2 U-TAPE (UT-C, lead decision R2/R3): the guard's input-map and `σ′` checks with the targets of the
-- stage's layout (`layout0 C.p`), and the guard's facts `NodeGCL` built on them; S2GF's and S2GT's (`inMapBG`,
-- `sigInSB`, `NodeGC`, whose targets are S2GT's constants `CMain.sW20 …`) are untouched.
import LvmE2QNodeG
import LvmE2QInstU
import LvmS2GUGood

-- (SLF-K: 18 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

/-!
# The layout-generic input map (stage S2GU)

At S2GU the stream block `S` is at `(layout0 p).s = 5,242,880` (S2GT: `CMain.sOff20 = 5,767,168`), and `KS`'s
output lanes are the `Y` block's lanes (`ksYCol p l`, S2GT: the `KS` block's slots `50 + l`).

* **`tgtNL s N lay y`**: `tgtN` with `S_flat`'s words in the stream block at `s`; `cellOkBL`, `bundleOkBL`.
* **`inMapBGL B nPub C Q lay N`**: `inMapBG` with the targets of `layout0 C.p`: the stream's 17 lanes and `σ′` on `S`'s
  columns (`sCol`), the `X` lanes (`xCol`), `KS`'s output lanes 0–3 from the split and the trace-digest row on the `Y`
  block (`ksYCol`); `PUB`'s lanes as before. **`nodeChkBGL`**: `nodeChkBG` on it.
* **`sigInSBL s N`**, **`SigInSL s N`**, **`sigInSL_of`**: `σ′`'s regions lie in `[s, s + 2^19)`.
* **`InMapMBU`** (re-freeze U-A1): `InMapMB` with `KS`'s six input-map fields (`xs`, `ys`, `yc`, `yls`, `yns`, `md`) on
  the S2GU tape's message lanes `MqU qm` (the stream block's columns) and `Y` lanes `YqU qm` (the `Y` block).
* **`NodeGCL`**: `NodeGC` with `nodeChkBGL` and `SigInSL ((layout0 C.p).s)`; **`nodeGCL_of`** from the guard's Bools on
  the layout shape `specQU`.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.TypedV

/-- **The target of word `y`** with the stream block at `s` (`tgtN` at `s = CMain.sOff20`). -/
def tgtNL (s : ℕ) (N : TNat) (lay : Typed.Lay) (y : ℕ) : Option CTgt :=
  match (lay.yregs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src) with
  | some YSrc.sflat => some (.cmain (s + sflatWord (offN N y)))
  | some YSrc.sigma => some (.cmain (offN N y))
  | some YSrc.com => some (.cmain (offN N y))
  | some YSrc.ks => some (.cmain (offN N y))
  | some YSrc.pub => some (.cpub (offN N y))
  | _ => none

/-- A cell checked natively, the stream block at `s`. -/
def cellOkBL (s : ℕ) (F : K.FL) (lay : Typed.Lay) (N : TNat) (c : ℕ) (t : CTgt) : Bool :=
  F.cst c == none && tgtNL s N lay (F.wordK c) == some t

/-- Every cell `base + j` (`j < sz·2^τ`) of a bundle has target `tg (j % sz) (j / sz)`, the stream block at `s`. -/
def bundleOkBL (s : ℕ) (F : K.FL) (lay : Typed.Lay) (N : TNat) (sz τ base : ℕ) (tg : ℕ → ℕ → CTgt) : Bool :=
  (List.range (sz * 2 ^ τ)).all fun j ↦ cellOkBL s F lay N (base + j) (tg (j % sz) (j / sz))

/-- **The input map's cells, checked on `C.p`'s layout**: the stream (17 lanes of `2^14` on `S`'s columns), `σ′`
(column 17), `KS`'s `X` lanes (17 of `2^9`), `KS`'s output lanes 0–3 from the split (4 of `2^9`, `ksYCol`), the
trace-digest row (`B − 1`), `PUB`'s `nPub` lanes. -/
def inMapBGL (B nPub : ℕ) (C : QCfg) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  let F := K.FL.ofLay Q lay
  let I := sigIn C
  let p := C.p
  let s := (layout0 p).s
  bundleOkBL s F lay N 17 14 (Lvm.QAsm.lay C).sb (fun l r ↦ .cmain (sCol p l + r)) &&
  bundleOkBL s F lay N 1 10 I.sg (fun _ r ↦ .cmain (sCol p 17 + r)) &&
  bundleOkBL s F lay N 17 9 I.xs (fun l r ↦ .cmain (xCol p l + r)) &&
  bundleOkBL s F lay N 4 9 I.ys (fun l r ↦ .cmain (ksYCol p l + ksSplit p + r)) &&
  bundleOkBL s F lay N 4 0 I.md (fun l r ↦ .cmain (ksYCol p l + (B - 1) + r)) &&
  (List.range nPub).all fun j ↦ cellOkBL s F lay N (I.flag + j) (.cpub j)

/-- A committed read's cells, the stream block at `s` (`capOkB`'s twin). -/
def capOkBL (s : ℕ) (Fl : K.FL) (lay : Typed.Lay) (N : TNat) (ps : List (ℕ × ℕ × ℕ)) (a c jf : ℕ) : Bool :=
  ps.any fun p ↦ decide (jf < 2 ^ p.1) && cellOkBL s Fl lay N a (.cmain (p.2.1 + jf)) &&
    cellOkBL s Fl lay N c (.cmain (p.2.2 + jf))

/-- **Every `readd` instance of `Q` reads its cell**, the stream block at `s` (`rdChkB`'s twin). -/
def rdChkBL (s : ℕ) (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  let Fl := K.FL.ofLay Q lay
  let ps := capParams C F
  Q.blocks.zipIdx.all fun bx ↦
    let B := bx.1
    let b := bx.2
    B.tpl.zipIdx.all fun tx ↦
      match tx.1.op with
      | .readd _ _ =>
        tx.1.ty == .K && (tx.1.args.getD 0 default).ty == .K &&
          (List.range B.size).all fun jf ↦
            let a := (tx.1.args.getD 0 default).at (unflat B.dims jf)
            let c := Q.start .K b + B.tw .K * jf + B.rank .K tx.2
            match (Fl.srcKA.getD b #[]).getD (B.rank .K tx.2) default with
            | .alias tgt => aliasOkB Q Fl b jf a c (tgt.getD jf 0)
            | _ => capOkBL s Fl lay N ps a c jf
      | _ => true

/-- **The checks `NodeSound` reads**, on `C.p`'s layout. -/
def nodeChkBGL (B nPub : ℕ) (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  inMapBGL B nPub C Q lay N && rdChkBL (layout0 C.p).s C F Q lay N && mbSeedsOkB C F

end Lvm.QTyped

namespace Lvm.TypedV

/-- **`σ′`'s regions lie in the stream block at `s`.** -/
def sigInSBL (s : ℕ) (N : TNat) : Bool :=
  N.regs.all fun g => g.src != .sigma || (decide (s ≤ g.dst) && decide (g.dst + 2 ^ g.log ≤ s + 2 ^ 19))

/-- The Prop `sigInSBL` decides. -/
def SigInSL (s : ℕ) (N : TNat) : Prop :=
  ∀ g ∈ N.regs, g.src = .sigma → s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ s + 2 ^ 19

/-- **`sigInSBL` is sound.** -/
theorem sigInSL_of {s : ℕ} {N : TNat} (h : sigInSBL s N = true) : SigInSL s N := by
  intro g hg hs
  have := List.all_eq_true.mp h g hg
  simp only [hs, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

end Lvm.TypedV

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.E2U
open LeanVM.Parameters LeanVM.Protocol

/-- **The input map at S2GU** (re-freeze U-A1: `InMapMB` with the `KS` fields on the merged tape's message lanes
`MqU qm` and `Y` lanes `YqU qm`, `sigKSin_of_GkU`'s hypotheses). -/
structure InMapMBU (B nPub : ℕ) (lay : Layout) (I : SigIn) (M : Mem) (vk : RecursionFast.Digest) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  /-- The stream lanes (Q_link's and Q_sig's stream region; `C_rec`'s stream columns). -/
  stream : ∀ j < 2 ^ lay.m, M.k (lay.sb + j) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j
  /-- Q_sig's gate is on. -/
  flag : M.k I.flag = 1
  /-- The message lanes from the split on Q_sig's message cells. -/
  xs : ∀ r < 449, ∀ l < 17, M.k (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l)
  /-- The `Y` lanes `0 … 3` from the split on Q_sig's digest cells. -/
  ys : ∀ r < 399, ∀ l < 4, M.k (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l)
  yc : ∀ t ≤ 16, ∀ l < 4, M.k (I.yc + 4 * t + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 430 + t) l)
  yls : ∀ l < 4, M.k (I.yls + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 447) l)
  yns : ∀ l < 4, M.k (I.yns + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 448) l)
  /-- `PUB`: the key, the left statement, the leaf signature. -/
  vk : digAt M.k I.vk = vk
  cL : digAt M.k I.cL = (hdrOf x).cL
  sl : sigAt' M.k I.sl = (hdrOf x).sig
  /-- The trace-digest cells: the `Y` block's row `B − 1`, lanes `0 … 3`. -/
  md : ∀ l < 4, M.k (I.md + l) = FK.ofBF64 (YqU qm (B - 1) l)
  /-- `σ'`'s cells: `C_rec`'s column 17. -/
  sg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr))
  /-- Q_sig's child-header cells are the stream's lanes `11 …`. -/
  hd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k)
  /-- The whole `PUB` array from `I.flag`: the header's lanes. -/
  pub : ∀ j < nPub, M.k (I.flag + j) = hdrLane x j

end Lvm.NS

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol

/-- **The guard's facts on `C.p`'s layout** (`NodeGC` with `nodeChkBGL` and `σ′` in `(layout0 C.p).s`'s block). -/
structure NodeGCL (C : QCfg) (B nPub : ℕ) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) : Prop where
  st : StaticFactsTX C F Q tl N
  chk : nodeChkBGL B nPub C F Q tl N = true
  sig : SigInSL (layout0 C.p).s N
  cells : nK C ≤ Q.cells .K
  mb : N.mbT = mbTOf C F
  aux : ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
    (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ tl.aux

/-- The `BITS` classes' chunks are `specQU`'s auxiliary blocks (`aux_specQF`'s twin). -/
theorem aux_specQU (C : QCfg) (Q : Program) (pw : List (ℕ × ℕ)) (d : Array (Ty × ℕ × ℕ)) :
    ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ (mkLayD Q (specQU C Q pw) d).1.aux := by
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQU C Q pw) d
  refine ⟨f, fun i S c hS hc ↦ ?_⟩
  rw [hf]
  show _ ∈ (specQ C Q).auxOf f ++ _ ++ _
  exact List.mem_append_left _ (List.mem_append_left _ (mem_specQ_auxOf C Q f hS hc))

/-- **`NodeGCL` from the guard's Bools** on the layout shape `specQU`. -/
theorem nodeGCL_of {C : QCfg} {B' nPub : ℕ} {F : TFrz} {δ : List Seg} {Q : Program} {tl : Typed.Lay} {N : TNat}
    {B : BM Unit} {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)} (hQ : Q = toProgram (nK C) 0 B)
    (hδ : δ = (B ⟨nK C, 0⟩).2) (hl : tl = (mkLayD Q (specQU C Q pw) d).1)
    (hmb : N.mbT = mbTOf C F) (hst : staticOkTX C F δ Q tl N = true)
    (hchk : nodeChkBGL B' nPub C F Q tl N = true) (hσ : sigInSBL (layout0 C.p).s N = true) :
    NodeGCL C B' nPub F Q tl N :=
  ⟨staticFactsTX hQ hδ hst, hchk, sigInSL_of hσ, by rw [hQ]; exact nK_le_cells _ _ _, hmb,
    by rw [hl]; exact aux_specQU C Q pw d⟩


/-! ## The node's input map and reads on the stream block at `s` (UTAPE-STMT 26's parts) -/

/-- **`qr` is `qm`'s stream block at `s`** (`SBlk` at `CMain.sOff20`; `SBlkU` is it at `CMain.sOffU20`). -/
def SBlkS (s : ℕ) (qm : Column CMain.nu20) (qr : Column 19) : Prop :=
  ∀ w < 2 ^ 19, qr.values.getD w 0 = qm.values.getD (s + w) 0

/-- A `C_rec` word of a stream-block pair at `s` is its `C_main` word `s + n`. -/
theorem comCell_SS {s : ℕ} (hs8 : s + 2 ^ 19 ≤ 2 ^ 23) {qm : Column CMain.nu20} {qr : Column 19}
    (hS : SBlkS s qm qr) {n : ℕ} (hn : n < 2 ^ 19) :
    comCell lay26 qm qr true n = comCell lay26 qm qr false (s + n) := by
  rw [comCell_rec (L := lay26) qm qr hn,
    comCell_main (L := lay26) qm qr (show _ < 2 ^ 23 by (clear * - hs8 hn; omega)), wd, wd, hS n hn]

/-- A `σ′` word's `C_main` word is `s + off mod 2^19` (`off_sigma` at `s`). -/
theorem off_sigmaL {s : ℕ} {N : TNat} (h : SigInSL s N) (hs19 : s % 2 ^ 19 = 0) {y : ℕ} {g : NReg}
    (hr : N.regAt y = some g) (hsrc : g.src = .sigma) :
    N.off y = s + N.off y % 2 ^ 19 ∧ N.off y % 2 ^ 19 < 2 ^ 19 := by
  have hp := List.find?_some hr
  simp only [decide_eq_true_eq] at hp
  have hoff : N.off y = g.dst + (y - g.base) := by simp [TNat.off, hr]
  obtain ⟨h1, h2⟩ := h g (List.mem_of_find?_eq_some hr) hsrc
  exact ⟨by (clear * - hp hoff h1 h2 hs19; omega), Nat.mod_lt _ (Nat.two_pow_pos 19)⟩

/-- **`zOf` at a word with a target**, the stream block at `s` (`zOf_of_tgtL`'s twin). -/
theorem zOf_of_tgtLS {s : ℕ} (hs19 : s % 2 ^ 19 = 0) (hs8 : s + 2 ^ 19 ≤ 2 ^ 23) (N : TNat)
    (pl : Lvm.Pub → List FK) (Q : Program) (lay : Typed.Lay) (pub : Lvm.Pub) (qm : Column CMain.nu20)
    (qr : Column 19) (hS : SBlkS s qm qr) (hok : N.okB 23 19 = true) (hl : N.layOk lay = true)
    (hσ : SigInSL s N) {y : ℕ} {t : CTgt} (h : tgtNL s N lay y = some t) :
    (N.instL pl Q lay).zOf lay26 pub qm qr y = t.valL pl lay26 pub qm qr := by
  have hsrc : (N.instL pl Q lay).src? y = (N.regAt y).map (·.src) := src?_inst N Q lay hl y
  unfold TInst.zOf
  unfold tgtNL at h
  have ho : Lvm.QTyped.offN N y = N.off y := rfl
  rw [ho] at h
  rw [show (lay.yregs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src) =
    (N.instL pl Q lay).src? y from rfl, hsrc] at h
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
    · rfl
    · have hlt : N.off y < 2 ^ 19 := by
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
      rw [comCell_SS hs8 hS hw]
      rfl
    · rfl
    · obtain ⟨he, hlt⟩ := off_sigmaL hσ hs19 hr hs
      show FK.ofBF64 (comCell lay26 qm qr true (N.off y % 2 ^ 19)) = _
      rw [comCell_SS hs8 hS hlt, ← he]
      rfl
    · rfl

/-- A checked cell is its target's value, the stream block at `s` (`cell_of_okL`'s twin). -/
theorem cell_of_okLS {s : ℕ} (hs19 : s % 2 ^ 19 = 0) (hs8 : s + 2 ^ 19 ≤ 2 ^ 23) (N : TNat)
    (pl : Lvm.Pub → List FK) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlkS s qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInSL s N) {c : ℕ} {t : CTgt}
    (h : cellOkBL s (K.FL.ofLay Q lay) lay N c t = true) :
    (memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr)).k c = t.valL pl lay26 pub qm qr := by
  simp only [cellOkBL, Bool.and_eq_true, beq_iff_eq] at h
  rw [K.fl_cst, K.fl_wordK Q lay hlay] at h
  rw [memOf_k, h.1, Option.getD_none, zOf_of_tgtLS hs19 hs8 N pl Q lay pub qm qr hS hok hl hσ h.2]

/-- A bundle checked on `C_main` words `off l + r` (`bundle_of_okL`'s twin, the targets given by `htg`). -/
theorem bundle_of_okLS {s : ℕ} (hs19 : s % 2 ^ 19 = 0) (hs8 : s + 2 ^ 19 ≤ 2 ^ 23) (N : TNat)
    (pl : Lvm.Pub → List FK) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlkS s qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInSL s N) {sz τ base : ℕ} {off : ℕ → ℕ} {tg : ℕ → ℕ → CTgt}
    (htg : ∀ l r, tg l r = CTgt.cmain (off l + r))
    (h : bundleOkBL s (K.FL.ofLay Q lay) lay N sz τ base tg = true) :
    CellsAt (memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr)).k lay26 qm qr sz τ base false off := by
  intro j hj
  have hc := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [cell_of_okLS hs19 hs8 N pl Q lay hlay pub qm qr hS hok hl hσ hc, htg]
  rfl

/-- A bundle checked on `S`'s words `s + (off l + r)` is the stream block's (`bundleS_of_okL`'s twin). -/
theorem bundleS_of_okLS {s : ℕ} (hs19 : s % 2 ^ 19 = 0) (hs8 : s + 2 ^ 19 ≤ 2 ^ 23) (N : TNat)
    (pl : Lvm.Pub → List FK) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) (pub : Lvm.Pub)
    (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlkS s qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInSL s N) {sz τ base : ℕ} {off : ℕ → ℕ} {tg : ℕ → ℕ → CTgt}
    (hfit : ∀ j < sz * 2 ^ τ, off (j % sz) + j / sz < 2 ^ 19)
    (htg : ∀ l r, tg l r = CTgt.cmain (s + (off l + r)))
    (h : bundleOkBL s (K.FL.ofLay Q lay) lay N sz τ base tg = true) :
    CellsAt (memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr)).k lay26 qm qr sz τ base true off := by
  intro j hj
  have hc := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [cell_of_okLS hs19 hs8 N pl Q lay hlay pub qm qr hS hok hl hσ hc, htg]
  show FK.ofBF64 (comCell lay26 qm qr false (s + (off (j % sz) + j / sz))) = _
  rw [comCell_SS hs8 hS (hfit j hj)]

/-! ### At S2GU's layout -/

theorem sOffU20_mod : CMain.sOffU20 % 2 ^ 19 = 0 := by decide
theorem sOffU20_fit : CMain.sOffU20 + 2 ^ 19 ≤ 2 ^ 23 := by decide

/-- `S`'s column `l` at S2GU. -/
theorem sCol_P20U (l : ℕ) : sCol P20U l = CMain.sOffU20 + l * 2 ^ 14 := by
  rw [sCol, layout0_P20U]; rfl

/-- `X`'s lane `l` at S2GU (`S + 7,680`). -/
theorem xCol_P20U (l : ℕ) : xCol P20U l = CMain.xOffU20 + l * 2 ^ 14 := by
  rw [xCol, layout0_P20U]; rfl

/-- `KS`'s output lane `l` at S2GU: the `Y` block's lane `l`. -/
theorem ksYCol_P20U (l : ℕ) : ksYCol P20U l = CMain.yOffU20 + 2 ^ 13 * l := by
  rw [ksYCol, if_pos (by decide), layout0_P20U]; rfl

theorem ksSplit_P20U : ksSplit P20U = 7680 := by decide

section FieldsU

variable {v : ℕ → FK} {qm : Column CMain.nu20} {qr : Column 19}

/-- **The `X` message cells at S2GU** (a 17-bundle at `xCol P20U l`): the stream block's message lanes. -/
theorem xs_vU {xs : ℕ} (hb : CellsAt v lay26 qm qr 17 9 xs false fun l ↦ xCol P20U l) :
    ∀ r < 449, ∀ l < 17, v (xs + 17 * r + l) = FK.ofBF64 (Lvm.E2U.MqU qm (ksSplit P20 + r) l) :=
  fun r hr l hl ↦ by
  have hm : (17 * r + l) % 17 = l := by (clear * - hl; omega)
  have hd : (17 * r + l) / 17 = r := by (clear * - hm; omega)
  have h := hb (17 * r + l) (by (clear * - hr hm; omega))
  beta_reduce at h
  rw [Nat.add_assoc, h, hm, hd, xCol_P20U,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; simp only [CMain.xOffU20]; (clear * - hr hl; omega))]
  simp only [Lvm.E2U.MqU, Lvm.E2U.msgU, colM, ksSplit_P20, CMain.xOffU20]
  congr 2; (clear * -; omega)

/-- The `Y` bundle's cells at S2GU: row `ksSplit P20 + r` of the `Y` block's lane `l`. -/
theorem y_vU {yb : ℕ} (hb : CellsAt v lay26 qm qr 4 9 yb false fun l ↦ ksYCol P20U l + ksSplit P20U) {r l : ℕ}
    (hr : r < 2 ^ 9) (hl : l < 4) : v (yb + 4 * r + l) = FK.ofBF64 (Lvm.E2U.YqU qm (ksSplit P20 + r) l) := by
  have hm : (4 * r + l) % 4 = l := by (clear * - hl; omega)
  have hd : (4 * r + l) / 4 = r := by (clear * - hm; omega)
  have h := hb (4 * r + l) (by (clear * - hr hm; omega))
  beta_reduce at h
  rw [Nat.add_assoc, h, hm, hd, ksYCol_P20U, ksSplit_P20U,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; simp only [CMain.yOffU20]; (clear * - hr hl; omega))]
  simp only [Lvm.E2U.YqU, Lvm.E2U.yU, colM, ksSplit_P20, CMain.yOffU20]
  congr 2; (clear * -; omega)

/-- **The `Y` digest cells at S2GU** (`ys`, `yc`, `yls`, `yns` from one 4-bundle; `ys_v`'s twin). -/
theorem ys_vU {ys yc yls yns : ℕ} (hb : CellsAt v lay26 qm qr 4 9 ys false fun l ↦ ksYCol P20U l + ksSplit P20U)
    (hyc : yc = ys + 4 * 430) (hyls : yls = ys + 4 * 447) (hyns : yns = ys + 4 * 448) :
    (∀ r < 399, ∀ l < 4, v (ys + 4 * r + l) = FK.ofBF64 (Lvm.E2U.YqU qm (ksSplit P20 + r) l)) ∧
    (∀ t ≤ 16, ∀ l < 4, v (yc + 4 * t + l) = FK.ofBF64 (Lvm.E2U.YqU qm (ksSplit P20 + 430 + t) l)) ∧
    (∀ l < 4, v (yls + l) = FK.ofBF64 (Lvm.E2U.YqU qm (ksSplit P20 + 447) l)) ∧
    (∀ l < 4, v (yns + l) = FK.ofBF64 (Lvm.E2U.YqU qm (ksSplit P20 + 448) l)) := by
  refine ⟨fun r hr l hl ↦ y_vU hb (by (clear * - hr; omega)) hl, fun t ht l hl ↦ ?_, fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · rw [hyc, show ys + 4 * 430 + 4 * t = ys + 4 * (430 + t) by ring,
      show ksSplit P20 + 430 + t = ksSplit P20 + (430 + t) by (clear * -; omega)]
    exact y_vU hb (by (clear * - ht; omega)) hl
  · rw [hyls]; exact y_vU hb (by (clear * -; omega)) hl
  · rw [hyns]; exact y_vU hb (by (clear * -; omega)) hl

/-- **The trace-digest cells at S2GU** (the `Y` block's row `B − 1`). -/
theorem md_vU {md B : ℕ} (hB : B ≤ 2 ^ 13) (hb : CellsAt v lay26 qm qr 4 0 md false fun l ↦ ksYCol P20U l + (B - 1)) :
    ∀ l < 4, v (md + l) = FK.ofBF64 (Lvm.E2U.YqU qm (B - 1) l) := fun l hl ↦ by
  have h := hb l (by omega)
  beta_reduce at h
  rw [h, Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt hl, Nat.add_zero, ksYCol_P20U,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; simp only [CMain.yOffU20]; (clear * - hl hB; omega))]
  simp only [Lvm.E2U.YqU, Lvm.E2U.yU, colM, CMain.yOffU20]
  congr 2; (clear * -; omega)

end FieldsU

/-! ## The `readd` rows on the stream block at `s` -/

/-- **`ReaddOk` from the native check**, the stream block at `s` (`readdOk_of_chkL`'s twin on `rdChkBL s`). -/
theorem readdOk_of_chkLS {s : ℕ} (hs19 : s % 2 ^ 19 = 0) (hs8 : s + 2 ^ 19 ≤ 2 ^ 23) (C : QCfg) (F : TFrz)
    (Q : Program) (lay : Typed.Lay) (N : TNat) (pl : Lvm.Pub → List FK) (hlay : lay.Ok Q)
    (pub : Lvm.Pub) (qm : Column CMain.nu20) (qr : Column 19) (hS : SBlkS s qm qr) (hok : N.okB 23 19 = true)
    (hl : N.layOk lay = true) (hσ : SigInSL s N) (hchk : rdChkBL s C F Q lay N = true)
    (hbus : ∀ τ wa wv, (τ, wa, wv) ∈ capParams C F → ∀ x < 2 ^ τ,
      ∃ lq ∈ mbBlocks C.p, ∃ x' < 2 ^ mbBlk,
        comCell lay26 qm qr false (wa + x) = FK.toBF64 (FK.x ^ ((Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x')) ∧
        comCell lay26 qm qr false (wv + x) = comCell lay26 qm qr false (Lvm.sCol C.p lq.1 + lq.2 + x'))
    (hseed : ∀ lq ∈ mbBlocks C.p, ∀ x' < 2 ^ mbBlk,
      (Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x' < Q.cells .K ∧
      (memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr)).k ((Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x') =
        FK.ofBF64 (comCell lay26 qm qr false (Lvm.sCol C.p lq.1 + lq.2 + x')))
    (hlin : NonReaddHolds Q (memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr)) := by
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
  set M := memOf lay ((N.instL pl Q lay).zOf lay26 pub qm qr)
  have harg : (M.arg (Q.inst b jf t) 0).c₀ = M.k ((((Q.blk b).tpl[t]).args.getD 0 default).at
      (unflat (Q.blk b).dims jf)) := by
    simp only [Mem.arg, Inst.arg, Program.inst, hrow, haty, Mem.rd]; rfl
  unfold Program.RowDef
  simp only [Program.inst, hrow, hop', hty]
  simp only [Program.inst, hrow] at harg
  revert hj
  split
  · rename_i tgt _
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
      · simp only [linOkB, List.any_eq_true] at hl
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
  · intro hj
    simp only [capOkBL, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hj
    obtain ⟨⟨τ, wa, wv⟩, hp, ⟨hjτ, ha⟩, hc⟩ := hj
    obtain ⟨lq, hlq, x', hx', hA, hV⟩ := hbus τ wa wv hp jf hjτ
    obtain ⟨hlt, hse⟩ := hseed lq hlq x' hx'
    refine ⟨_, hlt, ?_, ?_⟩
    · rw [harg, cell_of_okLS hs19 hs8 N pl Q lay hlay pub qm qr hS hok hl hσ ha]
      show FK.x ^ _ = FK.ofBF64 (comCell lay26 qm qr false (wa + jf))
      rw [hA]; rfl
    · simp only [Mem.res, hty, Inst.clock, Mem.rd]
      rw [cell_of_okLS hs19 hs8 N pl Q lay hlay pub qm qr hS hok hl hσ hc, hse]
      show FE.ofK (FK.ofBF64 (comCell lay26 qm qr false (wv + jf))) = _
      rw [hV]

/-! ## The plan at S2GU and the node statics -/

-- `tblU20`, `passR_P20U`, `planSt_P20U`, `streamOk_P20U`: UT-L's `LvmS2GUPlan`.

/-! ## The pair's facts at S2GU from `NodeGCL` -/

section PairU

variable {B nPub : ℕ} {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat}
  (S : NodeGCL cfgU20 B nPub F Q tl N) (pl : Lvm.Pub → List FK) (pb : List UInt8 → Lvm.Pub)
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

end PairU

/-! ## `NodeSound` at S2GU from the parts -/

end Lvm.E2Q
