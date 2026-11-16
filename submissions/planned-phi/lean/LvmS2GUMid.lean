-- New for lvm2 U-TAPE (UT-L, 2026-11-16): DAY-0 STATEMENTS of S2GU's middle phases (the typed phases at `E2` as S2GT,
-- then the merged tape `tapeProgU`; `KS` and its link are gone), the claims' assembly, the relocation onto the moved
-- stream block, the good pair. Every `sorry` is a day-0 statement tagged `-- UTAPE-STMT <n>`.
import LvmS2GUGood
import LvmE2TSpec
import LvmCertM20
import LvmMPMidTau

/-!
# S2GU's middle phases (day-0 statements)

* **`tapeClaimsU`**: the front's claims, all on `C_main` (UT-V/UT-P order, 00:21–00:22): `a_0 … a_3` (`D`'s word
  claims at `r_{<20}`, split), `b_0 … b_24` (the `Y` block's word claims at `r_{<13}`, split), the `D`, `Y` and `M` row
  claims, the boundary `h_0 … h_3`. **`assembleU₂`**: the typed claims and the front's (`onStackZs` when small).
* **`midGU Ti`**: `typedProgT Ti (pubXT x)`, `tapeProgU`, the claims.
* **`GoodTU Ti H`**: `GbTT` (S2GT's typed half with the boundary) and `GkU` (the merged tape's relation).
* The stream block at S2GU: `recBU20`, `relocBU20`, `recOfU20`, `relocU20`, **`relocLawU20`** (owner L).
* Statements: **`midSpecP_GU`** (owner V: `midSpecP_GT`'s twin with the S2GU front; `midSpecP_F₂`'s phase list without
  `KS`/`KSlink`), `retOK_midGU_len` (V), `cg_midGU` (L).
-/

set_option autoImplicit false

namespace Lvm.E2U

open RecursionFast Lvm Lvm.E2V Lvm.E2T Lvm.Typed LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.VEq (BClaim VPlacement VStackClaim selE dBlkE nuMainE hdX pubX pubXT)
open Lvm.ASM (OpenClaims GoodRel εS)
open scoped ENNReal
open LeanVM.Protocol.EndToEnd.Sound (RetOK)

/-! ## The front's claims -/

/-- **The S2GU front's claims** on `C_main`: `a_{<4}` (split), `b_{<25}` (split, on the `Y` block's lanes), the `D`,
`Y`, `M` row claims (`E3`), the boundary claims `D̃_l(bits(n − 1)) = h_l` (`E3`). -/
def tapeClaimsU (tp : TapeOutU) (pub : Lvm.Pub) : List BClaim :=
  ((List.range 4).flatMap fun l ↦ splitE2 nuMainE (pointE2 dBlkE (tp.1.take 20 ++ selPtF l 2) (tp.2.1.getD l 0))) ++
  ((List.range 25).flatMap fun l ↦
    splitE2 nuMainE (pointE2 ⟨13, CMain.yOffU20 + l * 2 ^ 13⟩ (tp.1.take 13) (tp.2.1.getD (25 + l) 0))) ++
  [⟨⟨nuMainE, 0⟩, tp.2.2.2.d.row.2, tp.2.2.2.d.row.1⟩, ⟨⟨nuMainE, 0⟩, tp.2.2.2.y.row.2, tp.2.2.2.y.row.1⟩,
    ⟨⟨nuMainE, 0⟩, tp.2.2.2.m.row.2, tp.2.2.2.m.row.1⟩] ++
  (pub.h.zipIdx.map fun (w, l) ↦ BClaim.point dBlkE (selE (pub.n - 1) 20 ++ selE l 2) (M3.kE w))

/-- **The typed claims and the front's** (`assembleF₂`'s successor): the front adds `C_main` claims only. -/
def assembleU₂ (x : List UInt8) (a : OpenClaims) (tp : TapeOutU) : OpenClaims :=
  (a.1, Lvm.Shape.onStackZs x (a.2 ++ (tapeClaimsU tp (pubX x)).map (·.onStack)))

/-- **S2GU's middle phases**: the typed phases at `E2` (S2GT's), the merged tape, the claims. -/
def midGU (Ti : TInst) (x : List UInt8) : VerifierProgram OpenClaims :=
  typedProgT Ti (pubXT x) >>= fun a ↦ tapeProgU (hdX x).s (pubX x).n >>= fun k ↦ pure (assembleU₂ x a k)

/-- **The good pair at S2GU** (`GoodTT`'s successor): S2GT's typed half and the merged tape's relation. -/
def GoodTU (Ti : TInst) (H : THypT Ti) : GoodRel := fun x qm qr ↦ GbTT Ti H x (qm, qr) ∧ GkU x (qm, qr)

/-! ## The stream block at S2GU -/

/-- **The stream block of a big-layout `C_main` column at S2GU** (`2^19` words at `CMain.sOffU20`). -/
def recBU20 (q : Column CMain.nu20) : Column 19 :=
  ⟨CompPoly.CMlPolynomialEval.mk 19 (Vector.ofFn fun i ↦ q.values.getD (CMain.sOffU20 + i) 0)⟩

/-- **A `C_rec` claim as a block claim on S2GU's `S`.** -/
def relocBU20 (c : VStackClaim) : VStackClaim := (⟨⟨19, CMain.sOffU20⟩, c.1, c.2⟩ : BClaim).onStack

/-- `S`'s words in `recBU20`. -/
theorem getD_recBU20 (q : Column CMain.nu20) {i : ℕ} (hi : i < 2 ^ 19) :
    (recBU20 q).values.getD i 0 = q.values.getD (CMain.sOffU20 + i) 0 := by
  unfold recBU20 CompPoly.CMlPolynomialEval.mk
  exact Lvm.Shape.vector_getD_ofFn _ 0 hi

theorem getD_recBU20_ge (q : Column CMain.nu20) {i : ℕ} (hi : 2 ^ 19 ≤ i) :
    (recBU20 q).values.getD i 0 = 0 := by
  unfold recBU20 CompPoly.CMlPolynomialEval.mk
  exact Lvm.CT.vgetD_ofFn_ge _ 0 hi

abbrev recOfU20 : List UInt8 → Column CMain.nu20 → Column 19 := Lvm.Typed.recOfV recBU20
abbrev relocU20 : List UInt8 → VStackClaim → VStackClaim := Lvm.Typed.relocV relocBU20

/-- **UTAPE-STMT 16** (owner L): **the relocation's laws at S2GU** (`relocLaw20`'s proof at `sOffU20`). -/
theorem relocLawU20 : Lvm.ASM.RelocLaw recOfU20 relocU20 := by
  refine Lvm.Typed.relocLaw_view (fun c q _ h ↦ ?_) (fun c hc ↦ ?_)
  · have hal : 2 ^ 19 ∣ CMain.sOffU20 := ⟨10, by norm_num [CMain.sOffU20]⟩
    have hfit : CMain.sOffU20 + 2 ^ 19 ≤ 2 ^ CMain.nu20 := by norm_num [CMain.sOffU20, CMain.nu20]
    have h' := (Lvm.ASM.holds_onStack (μ := CMain.nu20) ⟨⟨19, CMain.sOffU20⟩, c.1, c.2⟩ hal hfit q).mp h
    dsimp only at h'
    unfold LeanVM.Protocol.EndToEnd.StackClaim.Holds
    rw [← h', Fin.sum_univ_eq_sum_range
      (fun n ↦ c.1 (LeanVM.Protocol.EndToEnd.boolPoint 19 n) * LeanVM.Parameters.ofK ((recBU20 q).values.getD n 0))]
    exact Finset.sum_congr rfl fun n hn ↦ by rw [getD_recBU20 q (Finset.mem_range.mp hn)]
  · exact Lvm.ASM.isMultiaffine_onStack (n := CMain.nu20) ⟨⟨19, CMain.sOffU20⟩, c.1, c.2⟩ (by norm_num [CMain.nu20]) hc

/-- **UTAPE-STMT 17** (owner L): `recBU20 q` is `q`'s stream block at S2GU (`sBlk_recB20`'s twin). -/
theorem sBlkU_recBU20 (q : Column CMain.nu20) : SBlkU q (recBU20 q) := fun _ hw ↦ getD_recBU20 q hw

/-- The S2GU wire commits nothing and asks no proof of work. -/
theorem cg_wireProgU (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim LeanVM.Parameters.E2) : Lvm.M3.NoCG (wireProgU s n claim) :=
  Lvm.M3.NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_e2Reads _) fun _ ↦
    Lvm.M3.NoCG.bind (Lvm.M3.cg_require _) fun _ ↦ Lvm.M3.NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦
        Lvm.M3.cg_ret _

/-- The S2GU tape commits nothing and asks no proof of work. -/
theorem cg_tapeProgU (s : RecursionFast.Digest) (n : ℕ) : Lvm.M3.NoCG (tapeProgU s n) :=
  Lvm.M3.NoCG.bind cg_e2Sep fun _ ↦ Lvm.M3.NoCG.bind (cg_e2Samples _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_e2Reads _) fun _ ↦ Lvm.M3.NoCG.bind (cg_e2Samples _ _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_tapeGkrE2 _ _ _) fun _ ↦ Lvm.M3.NoCG.bind (Lvm.M3.cg_require _) fun _ ↦
        Lvm.M3.NoCG.bind (cg_wireProgU _ _ _) fun _ ↦ Lvm.M3.cg_ret _

/-! ## The middle phases' obligations -/

/-! ## STMT 18 (UT-V): the S2GU front's claims, returns, and the pinned pair form -/

section Mid18

open LeanVM.Parameters LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.Shape (vp)
open Lvm.E2F (candRelZ)
open Lvm.NS (colM)
open Lvm.Typed (BT TInst)
open Lvm.ASM (Pair BndS MidSpecP midSpecOfRelG)
open Lvm.VEq (selE dBlkE nuMainE hdX)
open scoped ENNReal

local notation "Holds" => LeanVM.Protocol.EndToEnd.StackClaim.Holds

/-- **The claims the S2GU tape leaves on a candidate** (`TapePostU`'s without `R`): the three row claims, `D`'s and
the `Y` block's tied word claims. -/
def KcU (col : ℕ → K) (out : TapeOutU) : Prop :=
  RowColTrue 23 col out.2.2.2.d.row ∧ RowColTrue 23 col out.2.2.2.y.row ∧ RowColTrue 23 col out.2.2.2.m.row ∧
    E2V.TiedDF 20 (dU col) (out.1.take 20) out.2.1 ∧ TiedYF (yU col) out.1 out.2.1

/-- **Facts of every return of the S2GU tape**: lengths, the row weights' multiaffinity. -/
def KgRetU (k : TapeOutU) : Prop :=
  k.1.length = 21 ∧ k.2.1.length = 50 ∧ IsMultiaffine 23 k.2.2.2.d.row.2 ∧ IsMultiaffine 23 k.2.2.2.y.row.2 ∧
    IsMultiaffine 23 k.2.2.2.m.row.2

theorem retOK_slotProgE2U (b sb blk : ℕ) (W : ℕ → ℕ → E2) (pt : List E2) (v : E2) (h : pt.length + b + sb = 23) :
    RetOK (fun d : SlotOutE2 ↦ IsMultiaffine 23 d.row.2) (slotProgE2 b sb blk W pt v) :=
  (retOK_sumcheckE2 _ _ _ _).bind fun sl hsl ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_rowSwitch _ _).bind fun row hrow ↦ RetOK.ret (by
      show IsMultiaffine 23 row.2
      have e : (pt ++ sl.1 ++ selPtF blk sb : List E2).length = 23 := by
        simp only [List.length_append, hsl, List.length_replicate, selPtF, List.length_map, List.length_range]
        omega
      rw [← e]; exact hrow)

theorem retOK_wireProgU (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    RetOK (fun wo : WireOutU ↦ IsMultiaffine 23 wo.d.row.2 ∧ IsMultiaffine 23 wo.y.row.2 ∧
      IsMultiaffine 23 wo.m.row.2) (wireProgU s n claim) :=
  (retOK_sumcheckE2 _ _ _ _).bind fun sc hsc ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_slotProgE2U 2 1 0 _ _ _ (by simp [hsc])).bind fun d hd ↦
    (retOK_slotProgE2U 5 5 22 _ _ _ (by simp [hsc])).bind fun y hy ↦
    (retOK_slotProgE2U 5 4 10 _ _ _ (by simp [hsc])).bind fun m hm ↦ RetOK.ret ⟨hd, hy, hm⟩

/-- **Every return of the S2GU tape meets `KgRetU`.** -/
theorem retOK_tapeProgU (s : RecursionFast.Digest) (n : ℕ) : RetOK KgRetU (tapeProgU s n) :=
  RetOK.bind_true fun _ ↦ (retOK_e2Samples _ _).bind fun r hr ↦ (retOK_e2Reads _).bind fun ab hab ↦
    (retOK_e2Samples _ _).bind fun r20 h20 ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_wireProgU _ _ _).bind fun wo hwo ↦ RetOK.ret ⟨by simp [hr, h20], hab, hwo⟩

/-- A row claim on the whole `C_main`. -/
theorem rowMain_of (row : E × (List E → E)) {qm : Column CMain.nu20}
    (H : Holds CMain.nu20 (⟨⟨nuMainE, 0⟩, row.2, row.1⟩ : BClaim).onStack qm) : RowColTrue 23 (colM qm) row := by
  have := E2V.rowCol_of_holds (μ := CMain.nu20) (h := 17) (off := 0) (dvd_zero _) (by norm_num) H
  have e : (fun n ↦ qm.values.getD (0 + n) 0) = colM qm := funext fun n ↦ by simp [colM, Lvm.NS.wd]
  rw [e] at this
  exact this

/-- **The `Y` block's tied lanes** from their split claims. -/
theorem tiedYF_of (hS : E2V.SplitSound) (tp : TapeOutU) (hr : tp.1.length = 21) {qm : Column CMain.nu20}
    (H : ∀ l < 25, ∀ b ∈ splitE2 nuMainE (pointE2 ⟨13, CMain.yOffU20 + l * 2 ^ 13⟩ (tp.1.take 13)
      (tp.2.1.getD (25 + l) 0)), Holds CMain.nu20 b.onStack qm) :
    TiedYF (yU (colM qm)) tp.1 tp.2.1 := by
  intro l hl
  have hal : 2 ^ 13 ∣ CMain.yOffU20 + l * 2 ^ 13 := Nat.dvd_add ⟨704, by norm_num⟩ (Nat.dvd_mul_left _ _)
  have e := E2V.point_of_split hS (nu := CMain.nu20) (blk := ⟨13, CMain.yOffU20 + l * 2 ^ 13⟩) (z := tp.1.take 13)
    (by simp [hr]) (by show 13 ≤ CMain.nu20; norm_num) hal
    (by show CMain.yOffU20 + l * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ CMain.nu20; simp only [CMain.yOffU20]; norm_num; omega)
    qm (H l hl)
  rw [← e]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [yU, colM, Lvm.NS.wd, CMain.yOffU20]
  rw [show 22 * 2 ^ 18 + l * 2 ^ 13 + x = 5767168 + l * 2 ^ 13 + x by norm_num]
  rfl

/-- **`D`'s tied lanes** from their split claims (`tiedDF_of` on `r_{<20}`). -/
theorem tiedDFU_of (hS : E2V.SplitSound) (tp : TapeOutU) (hr : tp.1.length = 21) {qm : Column CMain.nu20}
    (H : ∀ l < 4, ∀ b ∈ splitE2 nuMainE (pointE2 dBlkE (tp.1.take 20 ++ selPtF l 2) (tp.2.1.getD l 0)),
      Holds CMain.nu20 b.onStack qm) :
    E2V.TiedDF 20 (dU (colM qm)) (tp.1.take 20) tp.2.1 := by
  have hr20 : (tp.1.take 20).length = 20 := by simp [hr]
  intro l hl
  have e := E2V.point_of_split hS (blk := dBlkE) (z := tp.1.take 20 ++ selPtF l 2)
    (by simp [hr20, dBlkE, selPtF]) (by decide) (by simp [dBlkE]) (by decide) qm (H l hl)
  simp only [dBlkE, CMain.dOff20, zero_add] at e
  rw [E2V.sum_selF (h := 20) (k := 2) hr20 (by omega)] at e
  rw [← e]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [dU, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
  rfl

end Mid18

section Mid18b

open LeanVM.Parameters LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (bitsE sum_eqAt_bitsE)
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.Shape (vp)
open Lvm.E2F (candRelZ)
open Lvm.NS (colM)
open Lvm.Typed (BT TInst)
open Lvm.ASM (Pair BndS)
open Lvm.VEq (selE dBlkE nuMainE hdX)
open scoped ENNReal

local notation "Holds" => LeanVM.Protocol.EndToEnd.StackClaim.Holds

/-- **T5's boundary claims** give `BndS` (`bndS_of_tapeF` on `tapeClaimsU`). -/
theorem bndS_of_tapeU (x : List UInt8) (tp : TapeOutU) {qm : Column CMain.nu20}
    (h : ∀ b ∈ tapeClaimsU tp (pubX x), Holds CMain.nu20 b.onStack qm) : BndS x qm := by
  intro hn m hm
  have hal2 : 2 ^ (20 + 2) ∣ 0 := dvd_zero _
  have hfit2 : 0 + 2 ^ (20 + 2) ≤ 2 ^ 23 := by norm_num
  have hN : (pubX x).n = (Lvm.ASM.hdrOf x).n := Lvm.ASM.pubX_n x
  have hH : ∀ m < 4, ((pubX x).h.getD m 0).val =
      RecursionFast.Keccak.blockLane (Lvm.ASM.hdrOf x).h.toArray m := by
    intro m hm
    show (((List.range 4).map fun i ↦ kAt (Lvm.VEq.sigOfX x) (headerAt 120 + 8 * i)).getD m 0).val = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
    exact Lvm.ASM.Kec.lane_hdr x (by norm_num) hm
  have hlenH : (pubX x).h.length = 4 := Lvm.ASM.length_pubX_h x
  have hmem : BClaim.point dBlkE (selE ((pubX x).n - 1) 20 ++ selE m 2)
      (Lvm.M3.kE ((pubX x).h.getD m 0)) ∈ tapeClaimsU tp (pubX x) :=
    List.mem_append_right _ (List.mem_map.2 ⟨_, Lvm.ASM.Kec.getD_mem_zipIdx _ (by omega), rfl⟩)
  have hlt : (pubX x).n - 1 < 2 ^ 20 := by rw [hN]; omega
  have H := Lvm.ASM.Kec.holds_split (h := 20) (k := 2) hal2 hfit2 (by simp [Lvm.ASM.Kec.selE_eq_bitsE])
    (b := m) (by omega) (h _ hmem)
  rw [Lvm.ASM.Kec.selE_eq_bitsE, sum_eqAt_bitsE hlt, zero_add] at H
  have H' := Lvm.KG.ofK_injective H
  rw [hN] at H'
  simp only [Lvm.NS.dD, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
  rw [H', ← hH m hm]
  rfl

/-- **The semantic link at S2GU** (`linkF`'s successor): the assembled claims holding on a pair give the front's
claims (`KcU`) and the typed claims with the boundary claims on the view. -/
theorem linkU (hS : E2V.SplitSound) (x : List UInt8) (a : OpenClaims) (k : TapeOutU) (p : Pair) (hk : KgRetU k)
    (h1 : ∀ c ∈ (assembleU₂ x a k).1, Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleU₂ x a k).2, Holds CMain.nu20 c p.1) :
    KcU (colM (vp x p).1) k ∧ BT x a (vp x p) := by
  have h2' : ∀ c ∈ a.2 ++ (tapeClaimsU k (pubX x)).map (·.onStack), Holds CMain.nu20 c (vp x p).1 := by
    intro c hc
    unfold assembleU₂ Lvm.Shape.onStackZs at h2
    unfold vp Lvm.Shape.view
    by_cases hs : Lvm.Shape.small x = true
    · simp only [hs, ite_true, List.mem_map] at h2 ⊢
      exact (Lvm.Shape.holds_onStackZ c p.1).mp (h2 _ ⟨c, hc, rfl⟩)
    · simp only [hs, ite_false, Bool.false_eq_true] at h2 ⊢
      exact h2 c hc
  have ht : ∀ b ∈ tapeClaimsU k (pubX x), Holds CMain.nu20 b.onStack (vp x p).1 := fun b hb ↦
    h2' _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩))
  have hrows : ∀ b ∈ ([⟨⟨nuMainE, 0⟩, k.2.2.2.d.row.2, k.2.2.2.d.row.1⟩, ⟨⟨nuMainE, 0⟩, k.2.2.2.y.row.2,
      k.2.2.2.y.row.1⟩, ⟨⟨nuMainE, 0⟩, k.2.2.2.m.row.2, k.2.2.2.m.row.1⟩] : List BClaim),
      Holds CMain.nu20 b.onStack (vp x p).1 := fun b hb ↦
    ht b (List.mem_append_left _ (List.mem_append_right _ hb))
  obtain ⟨hr, -, -, -, -⟩ := hk
  refine ⟨⟨rowMain_of _ (hrows _ (by simp)), rowMain_of _ (hrows _ (by simp)), rowMain_of _ (hrows _ (by simp)),
    tiedDFU_of hS k hr fun l hl b hb ↦ ht b (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, hb⟩)))),
    tiedYF_of hS k hr fun l hl b hb ↦ ht b (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, hb⟩))))⟩,
    ⟨fun c hc ↦ h1 c hc, fun c hc ↦ h2' c (List.mem_append_left _ hc)⟩, bndS_of_tapeU x k ht⟩

/-- Every front claim is multiaffine on `C_main`. -/
theorem isMultiaffine_tapeClaimsU (hA : E2V.SplitAffine) (pub : Lvm.Pub) (k : TapeOutU) (hk : KgRetU k) :
    ∀ b ∈ tapeClaimsU k pub, IsMultiaffine CMain.nu20 b.onStack.1 := by
  obtain ⟨hr, -, hd, hy, hm⟩ := hk
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨l, -, hb⟩ := List.mem_flatMap.1 hb
        exact hA _ _ (E2V.fitsE2_point _ (by simp [hr, dBlkE, selPtF]) (by decide) (by simp [dBlkE])
          (by decide)) b hb
      · obtain ⟨l, hl, hb⟩ := List.mem_flatMap.1 hb
        have hl' := List.mem_range.1 hl
        exact hA _ _ (E2V.fitsE2_point _ (by simp [hr]) (by show 13 ≤ nuMainE; decide)
          (Nat.dvd_add ⟨704, by norm_num⟩ (Nat.dvd_mul_left _ _))
          (by show CMain.yOffU20 + l * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ nuMainE
              simp only [CMain.yOffU20, nuMainE, CMain.nu20]; norm_num; omega)) b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl hd
      · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl hy
      · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl hm
  · obtain ⟨⟨w, l⟩, -, rfl⟩ := List.mem_map.1 hb
    exact Lvm.ASM.isMultiaffine_onStack _ (by show 20 + 2 ≤ CMain.nu20; norm_num)
      (Lvm.ASM.isMultiaffine_eqEvalN _ _)

theorem length_tapeClaimsU (k : TapeOutU) (x : List UInt8) : (tapeClaimsU k (pubX x)).length = 65 := by
  simp only [tapeClaimsU, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_zipIdx, Lvm.ASM.length_pubX_h, E2T.length_flatMap_two _ _ (fun _ ↦ E2T.length_splitE2 _ _),
    List.length_range]

/-- **The side conditions at S2GU** (`sideF`'s successor). -/
theorem sideU (hA : E2V.SplitAffine) (x : List UInt8) (a : OpenClaims) (k : TapeOutU)
    (ha : (∀ c ∈ a.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ a.2, IsMultiaffine CMain.nu20 c.1) ∧
      a.1.length + a.2.length ≤ 2 ^ 39) (hk : KgRetU k) :
    (∀ c ∈ (assembleU₂ x a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleU₂ x a k).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleU₂ x a k).1.length ≤ 2 ^ 55 ∧ (assembleU₂ x a k).2.length ≤ 2 ^ 40 := by
  obtain ⟨a1, a2, a3⟩ := ha
  have hm : ∀ c ∈ a.2 ++ (tapeClaimsU k (pubX x)).map (·.onStack), IsMultiaffine CMain.nu20 c.1 := fun c hc ↦ by
    rcases List.mem_append.mp hc with hc | hc
    · exact a2 c hc
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      exact isMultiaffine_tapeClaimsU hA _ k hk b hb
  have hl := length_tapeClaimsU k x
  refine ⟨a1, fun c hc ↦ ?_, by simp only [assembleU₂]; omega, ?_⟩
  · unfold assembleU₂ Lvm.Shape.onStackZs at hc
    split_ifs at hc
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact Lvm.Shape.isMultiaffine_onStackZ (hm c' hc')
    · exact hm c hc
  · simp only [assembleU₂, Lvm.Shape.onStackZs]
    split_ifs <;> simp only [List.length_map, List.length_append, hl] <;> omega

end Mid18b

/-- **The followers' lead bound at S2GU** (re-freeze U-A3): S2GU's front ends with `M`'s row switch (7 `E3` samples,
no read), so the middle phases' followers lead at most `εS − Σ_7 errE 1`. -/
noncomputable abbrev τU : ℝ≥0∞ := εS - ∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1

theorem errE_le_130 {d : ℕ} (hd : d ≤ 2 ^ 62) : LeanVM.Protocol.KeccakGkr.errE d ≤ (2 : ℝ≥0∞)⁻¹ ^ 130 := by
  unfold LeanVM.Protocol.KeccakGkr.errE
  rw [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat]
  have h1 : (d : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 62 := by exact_mod_cast hd
  have h2 : (2 : ℝ≥0∞) ^ 62 * ((2 : ℝ≥0∞) ^ 192)⁻¹ = (2 : ℝ≥0∞)⁻¹ ^ 130 := by
    rw [show (192 : ℕ) = 62 + 130 from rfl, pow_add,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
      ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
      one_mul, ENNReal.inv_pow]
  calc (d : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ≤ (2 : ℝ≥0∞) ^ 62 * ((2 : ℝ≥0∞) ^ 192)⁻¹ := by gcongr
    _ = _ := h2

/-- **The opening's lead fits under S2GU's followers' bound** (U-A3's decided check: `2^-145 ≤ εS − 7·2^-192`). -/
theorem leadOpenM_le_τU : Lvm.ASM.leadOpenM ≤ τU := by
  have h7 : (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) = LeanVM.Protocol.KeccakGkr.errE 7 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Lvm.ASM.errE_add]
  have hne : (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) ≠ ⊤ := by
    rw [h7]; exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (by simp)) (errE_le_130 (by norm_num))
  refine ENNReal.le_sub_of_add_le_left hne ?_
  have e : (2 : ℝ≥0∞)⁻¹ ^ 130 + (2 : ℝ≥0∞)⁻¹ ^ 130 = (2 : ℝ≥0∞)⁻¹ ^ 129 := by
    rw [show (130 : ℕ) = 129 + 1 from rfl, pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  calc (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) + Lvm.ASM.leadOpenM
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 130 + (2 : ℝ≥0∞)⁻¹ ^ 130 := by
        rw [h7]
        exact add_le_add (errE_le_130 (by norm_num)) (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num))
    _ = (2 : ℝ≥0∞)⁻¹ ^ 129 := e
    _ ≤ εS := Lvm.ASM.pow129_le_εS

/-- **UTAPE-STMT 18** (owner V): **the pinned pair form of S2GU's middle phases** (`midSpecP_GT`'s twin): for every
pin `za`, from `PinPost za` to `OpenPostRG` over `candRelZ recOf za`, every group `≤ εS`, lead `leadF₂`
(`midSpecP_GT_of`'s composition with `tapeSpecU` in place of the S2GF front; no `KS` GKR, no `KS` link). -/
theorem midSpecP_GU (Ti : TInst) (H : THypT Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List LeanVM.Parameters.E × LeanVM.Parameters.E) :
    Lvm.ASM.MidSpecPτ (midGU Ti) (Lvm.E2F.candRelZ recOf za) (Lvm.E2F.PinPost za)
      (Lvm.Shape.Good₂ (GoodTU Ti H)) εS leadF₂ τU := by
  have hS : E2V.SplitSound := fun nu c hc q h ↦ splitE2_sound nu c hc q h
  have hA : E2V.SplitAffine := fun nu c hc ↦ isMultiaffine_splitE2 nu c hc
  have h7 : (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) ≤ εS := by
    simpa using E2V.sum7_le_εS
  exact Lvm.ASM.midSpecOfRelGτ (busP := fun x ↦ typedProgT Ti (pubXT x))
    (kgP := fun x ↦ tapeProgU (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleU₂ x a k) (Lb := leadF₂) (Lk := 0)
    (Gb := fun x p ↦ GbTB Ti H.hτ x (Lvm.Shape.vp x p)) (Gk := fun x p ↦ GkU x (Lvm.Shape.vp x p))
    (B := fun x a p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p))
    (Kc := fun x k p ↦ KcU (Lvm.NS.colM (Lvm.Shape.vp x p).1) k)
    (Qa := fun _ a ↦ (∀ c ∈ a.1, LeanVM.Protocol.Whir.Sound.IsMultiaffine 19 c.1) ∧
      (∀ c ∈ a.2, LeanVM.Protocol.Whir.Sound.IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39)
    (Qk := fun _ ↦ KgRetU) (C := Lvm.E2F.candRelZ recOf za) (Sh := Lvm.E2F.PinPost za)
    (fun _ _ hl hr ↦ E2V.pinPost_append za hl hr)
    (fun x ↦ specBusGT H.hτ H.ok H.maps H.acc H.sc H.layOk H.keys H.width H.fix (H.μBus H.hτ) (H.errs H.hτ)
      recOf za x (GkU x) fun p ↦ ¬ (GbTB Ti H.hτ x p ∧ GkU x p))
    (fun x ↦ retOK_typedProgT_of Ti H.layOk H.widths (pubXT x))
    (fun x a T hT ↦ (tapeSpecUW (E2V.candRelZ_stable recOf za x) (E2V.candRelZ_ncard_le recOf za x)
        (hdX x).s (n := (pubX x).n) (fun p ↦ Lvm.NS.colM (Lvm.Shape.vp x p).1)
        (fun p ↦ Lvm.Typed.BT x a (Lvm.Shape.vp x p) ∧
          ¬ (GbTB Ti H.hτ x (Lvm.Shape.vp x p) ∧ GkU x (Lvm.Shape.vp x p)))
        (calc (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) + T
            ≤ (∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) +
                (εS - ∑ _i ∈ Finset.range 7, LeanVM.Protocol.KeccakGkr.errE 1) := add_le_add le_rfl hT
          _ = εS := add_tsub_cancel_of_le h7)).mono
      (fun _ hd ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hd fun p ⟨ht, hb, hn⟩ ↦
        ⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hn⟩, hb, hn⟩)
      (fun _ _ hp ↦ LeanVM.Protocol.EndToEnd.Front.Doomed.mono hp.2.2.2 fun p ⟨⟨h1, h2, h3, h4, h5⟩, hR⟩ ↦
        ⟨h1, h2, h3, h4, h5, hR⟩) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_tapeProgU _ _) (fun _ ↦ cg_tapeProgU _ _)
    (fun x a k p _ hk h1 h2 ↦ linkU hS x a k p hk h1 h2)
    (fun x a k ha hk ↦ sideU hA x a k ha hk)

/-- **UTAPE-STMT 19** (owner V): **the middle phases' claims are fewer than `2^40`** (`retOK_midGT_len`'s twin). -/
theorem retOK_midGU_len (Ti : TInst) (H : THypT Ti) (x : List UInt8) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40) (midGU Ti x) := by
  refine (retOK_typedProgT_of Ti H.layOk H.widths (pubXT x)).bind fun a ha ↦
    LeanVM.Protocol.EndToEnd.Sound.RetOK.bind_true fun k ↦ LeanVM.Protocol.EndToEnd.Sound.RetOK.ret ?_
  have hz : ∀ l : List VStackClaim, (Lvm.Shape.onStackZs x l).length = l.length := fun l ↦ by
    unfold Lvm.Shape.onStackZs
    split_ifs <;> simp only [List.length_map]
  have hf : (tapeClaimsU k (pubX x)).length = 65 := by
    simp only [tapeClaimsU, List.length_append, List.length_cons, List.length_nil, List.length_map,
      List.length_zipIdx, Lvm.ASM.length_pubX_h, length_flatMap_two _ _ (fun _ ↦ length_splitE2 _ _),
      List.length_range]
  simp only [assembleU₂, hz, List.length_append, List.length_map, hf]
  have := ha.2.2
  omega

/-- **UTAPE-STMT 20** (owner L): **S2GU's middle phases commit nothing and ask no proof of work** (`cg_midGT`'s
twin: `noCG_typedProgT`, the front's `NoCG`). -/
theorem cg_midGU (Ti : TInst) (x : List UInt8) : Lvm.M3.NoCG (midGU Ti x) :=
  Lvm.M3.NoCG.bind (noCG_typedProgT Ti _) fun _ ↦ Lvm.M3.NoCG.bind (cg_tapeProgU _ _) fun _ ↦ Lvm.M3.cg_ret _

end Lvm.E2U
