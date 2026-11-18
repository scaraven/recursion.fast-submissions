-- New for lvm2 σ_LEAF (SLF-C, 2026-11-16): DAY-0 STATEMENTS of the S2GS guard and input map (SLF-STMT 7a, 7b, 7d, 7g,
-- 7h). Every `sorry` is tagged `-- SLF-STMT 7<x>`; a proof never changes its statement (changes go to the lead, old → new).
import LvmE2QInstS
import LvmQSigLeafSound
import LvmS2GSXS
import LvmS2GLStmtC

/-!
# The S2GS guard and input map (day-0 statements)

* Instance of blob S (`LvmE2QInstS`): `cfgS20`, `frzS20`, `tdataS20`, `qaS20`, `QS20`, `powS20`, `layS20`,
  `cacheS20`, `staticOkTS20`; here `NTS20`, `TiS20`, `harChkBS20`.
* **The input map at S2GS** (`inMapBGS`, `nodeChkBGS`, `NodeGCS`): S2GU's, with `σ′`'s region `2^sgLog` (the node's
  own `σ_leaf` from word `2^10`) and the `KS` digests' region `4 × 2^ysLog` from row `ysRow0` (the leaf walk's rows,
  then Q_sig's), `PUB`'s `pubLanesS` lanes; `NodeGS`, **`staticOkBS20`**, `SFS20`.
* **`InMapMBS`**: the node's cells on a good pair (S2GU's `InMapMBU` without `σ_leaf` in `PUB`, the child header's 18
  lanes, plus the leaf walk's digests and `σ_leaf` read through `permC`, `slM20`).
* Statements: `nodeGCS_of` (7g), `sfS20` (7a), `harChkS20_sound` (7b), `miniS20` (7d), `inMapS20` (7h).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.BitsTab LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU YqU MqU)
open Lvm.E2S (VSSX decideFSX THypS GoodTS)
open Lvm.CT (slM20)
open Lvm.ASM (okSL NodeSoundS)

/-! ## The instance of blob S -/

/-- **V_S's typed record at S2GS** (`phiT`: the fast `Φ_Q` at `E2`). -/
def NTS20 : TNatT := ⟨Lvm.QTyped.nregsOf layS20 frzS20, PhiQGC cacheS20, Lvm.QTyped.mbTOf cfgS20 frzS20⟩

/-- **The typed instance at S2GS.** -/
noncomputable def TiS20 : TInst := NTS20.inst QS20 layS20

/-- **The HAR's static checks at S2GS** (`harChkBL20` at the S2GS instance). -/
def harChkBS20 : Bool :=
  Lvm.QTyped.tdMatchB tdataS20 NTS20.toN &&
    typedEndL tdataS20 P20S == posOf P20S (phaseItem0 P20S .tape) &&
    decide (typedEndL tdataS20 P20S + 40 ≤ 8 * streamLanes P20S) &&
    decide (posOf P20S (phaseItem0 P20S .openMain) + 48 ≤ 8 * streamLanes P20S) &&
    powS20.all (fun a => decide (a.1 + 2 < streamLanes P20S) && decide (a.2 ≤ 64)) &&
    posOf P20S (phaseItem0 P20S .openMain) == 8 * (phaseLane P20S .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20S (fun _ => 0) (fun _ => 0)) (streamLanes P20S) &&
    8 * Lvm.Har.stackEndL P20S.grind P20S.mainOod P20S.mainLevels (phaseLane P20S .openMain 0 - 5 + 15) ==
      hashedLen P20S &&
    decide (P20S.mainLevels.length ≤ (Lvm.QLink.opens P20S).length) && decide (1 ≤ 64 - P20S.grind) &&
    decide (Lvm.Fin.PosLanes P20S P20S.grind P20S.mainOod P20S.mainLevels (phaseLane P20S .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataS20 (layout0 P20S).s

/-! ## The input map at S2GS -/

/-- **The input map's cells at S2GS, checked on `C.p`'s layout**: the stream (17 lanes of `2^14`), `σ′`'s region
(`2^sgLog`, column 17), `KS`'s `X` lanes (17 of `2^9`), `KS`'s output lanes 0–3 from row `ysRow0` (4 of `2^ysLog`), the
trace-digest row (`B − 1`), `PUB`'s `nPub` lanes. -/
def inMapBGS (B nPub : ℕ) (C : QCfg) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  let F := K.FL.ofLay Q lay
  let I := sigIn C
  let p := C.p
  let s := (layout0 p).s
  bundleOkBL s F lay N 17 14 (Lvm.QAsm.lay C).sb (fun l r ↦ .cmain (sCol p l + r)) &&
  bundleOkBL s F lay N 1 (sgLog C) I.sg (fun _ r ↦ .cmain (sCol p 17 + r)) &&
  bundleOkBL s F lay N 17 9 I.xs (fun l r ↦ .cmain (xCol p l + r)) &&
  bundleOkBL s F lay N 4 (ysLog C) (ysB C) (fun l r ↦ .cmain (ksYCol p l + ysRow0 C + r)) &&
  bundleOkBL s F lay N 4 0 I.md (fun l r ↦ .cmain (ksYCol p l + (B - 1) + r)) &&
  (List.range nPub).all fun j ↦ cellOkBL s F lay N (I.flag + j) (.cpub j)

/-- **The checks `NodeSound` reads at S2GS**, on `C.p`'s layout. -/
def nodeChkBGS (B nPub : ℕ) (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  inMapBGS B nPub C Q lay N && rdChkBL (layout0 C.p).s C F Q lay N && mbSeedsOkB C F

/-- **The guard's facts at S2GS** (`NodeGCL` with `nodeChkBGS`). -/
structure NodeGCS (C : QCfg) (B nPub : ℕ) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) : Prop where
  st : StaticFactsTX C F Q tl N
  chk : nodeChkBGS B nPub C F Q tl N = true
  sig : SigInSL (layout0 C.p).s N
  cells : nK C ≤ Q.cells .K
  mb : N.mbT = mbTOf C F
  aux : ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
    (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ tl.aux

/-- **SLF-STMT 7g** (owner C): **`NodeGCS` from the guard's Bools** on the layout shape `specQU` (`nodeGCL_of`'s twin). -/
theorem nodeGCS_of {C : QCfg} {B' nPub : ℕ} {F : TFrz} {δ : List Seg} {Q : Program} {tl : Typed.Lay} {N : TNat}
    {B : BM Unit} {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)} (hQ : Q = toProgram (nK C) 0 B)
    (hδ : δ = (B ⟨nK C, 0⟩).2) (hl : tl = (mkLayD Q (specQU C Q pw) d).1)
    (hmb : N.mbT = mbTOf C F) (hst : staticOkTX C F δ Q tl N = true)
    (hchk : nodeChkBGS B' nPub C F Q tl N = true) (hσ : sigInSBL (layout0 C.p).s N = true) :
    NodeGCS C B' nPub F Q tl N :=
  ⟨staticFactsTX hQ hδ hst, hchk, sigInSL_of hσ, by rw [hQ]; exact nK_le_cells _ _ _, hmb,
    by rw [hl]; exact aux_specQU C Q pw d⟩

/-- **The S2GS guard's circuit facts** (`NodeGCS` at `cfgS20`). -/
abbrev NodeGS : Prop := NodeGCS cfgS20 (spongeBlocks P20S) (pubLanesS P20S) frzS20 QS20 layS20 NTS20.toN

/-- **The S2GS guard** (S2GL's conjuncts at the S2GS instance and input map). -/
def staticOkBS20 : Bool :=
  staticOkTS20 && nodeChkBGS (spongeBlocks P20S) (pubLanesS P20S) cfgS20 frzS20 QS20 layS20 NTS20.toN &&
    Lvm.TypedV.sigInSBL (layout0 P20S).s NTS20.toN && harChkBS20 && Lvm.T.oneOkB layS20 &&
    Lvm.Typed.KT.linOkX cacheS20 && Lvm.M3.mbLinB NTS20.mbT

/-- **The S2GS guard's facts.** -/
abbrev SFS20 : Prop :=
  NodeGS ∧ harChkBS20 = true ∧ Lvm.T.oneOkB layS20 = true ∧ Lvm.Typed.KT.linOkX cacheS20 = true ∧
    Lvm.M3.mbLinB NTS20.mbT = true

/-- **SLF-STMT 7a** (owner C): the guard's facts from `staticOkBS20 = true` (`sfL20`'s twin). -/
theorem sfS20 (h : staticOkBS20 = true) : SFS20 := by
  simp only [staticOkBS20, Bool.and_eq_true] at h
  exact ⟨nodeGCS_of QS20_eq rfl rfl rfl h.1.1.1.1.1.1 h.1.1.1.1.1.2 h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **SLF-STMT 7b** (owner C): **the facts `harChkBS20` decides** (`harChkL20_sound`'s twin). -/
theorem harChkS20_sound (h : harChkBS20 = true) :
    Lvm.Har.TdOk tdataS20 NTS20.toN ∧
      typedEndL tdataS20 P20S = posOf P20S (phaseItem0 P20S .tape) ∧
      typedEndL tdataS20 P20S + 40 ≤ 8 * streamLanes P20S ∧
      posOf P20S (phaseItem0 P20S .openMain) + 48 ≤ 8 * streamLanes P20S ∧
      (∀ a ∈ powS20, a.1 + 2 < streamLanes P20S ∧ a.2 ≤ 64) ∧
      posOf P20S (phaseItem0 P20S .openMain) = 8 * (phaseLane P20S .openMain 0 - 5) ∧
      Lvm.Har.LayOk (cfgMainF P20S (fun _ => 0) (fun _ => 0)) (streamLanes P20S) = true ∧
      8 * Lvm.Har.stackEndL P20S.grind P20S.mainOod P20S.mainLevels (phaseLane P20S .openMain 0 - 5 + 15) =
        hashedLen P20S ∧
      P20S.mainLevels.length ≤ (Lvm.QLink.opens P20S).length ∧ 1 ≤ 64 - P20S.grind ∧
      Lvm.Fin.PosLanes P20S P20S.grind P20S.mainOod P20S.mainLevels (phaseLane P20S .openMain 0 - 5 + 15) 0 ∧
      typedRegB tdataS20 (layout0 P20S).s = true := by
  simp only [harChkBS20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

set_option maxRecDepth 100000 in
/-- **SLF-STMT 7d** (owner C): the mini-bus record at S2GS (`miniL20`'s twin). -/
theorem miniS20 (S : NodeGS) : Lvm.M3.sumcheckTabs NTS20.toN.mbT = NTS20.toN.mbT ∧
    (Lvm.QTyped.tdataOf cfgS20 frzS20).mbS = NTS20.toN.mbT.map Lvm.M3.Tab.shape ∧
    (Lvm.QTyped.tdataOf cfgS20 frzS20).mbD = cfgS20.p.busDepth ∧
    Lvm.Har.FixListed NTS20.toN.mbT (Lvm.QTyped.tdataOf cfgS20 frzS20).mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgS20 frzS20) = mbTOf cfgS20 frzS20 := Lvm.Har.mbT_sumcheck cfgS20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm ⊢
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hm
  obtain ⟨t1, -, t3, t4⟩ := Lvm.Har.tdataOf_mb cfgS20 frzS20
  rw [t1, t3, t4, hD]
  exact ⟨hsc, rfl, rfl, Lvm.Har.mbT_fix cfgS20 _ _ _⟩

/-! ## The node's cells on a good pair -/

/-- **The node's cells at S2GS** on a pair (`InMapMBU`'s twin: no `σ_leaf` in `PUB`, the child header's 18 lanes;
the leaf walk's `KS` digests, and `σ_leaf` through `permC`). -/
structure InMapMBS (B nPub : ℕ) (C : QCfg) (M : Mem) (vk : RecursionFast.Digest) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  /-- The stream lanes (Q_link's, Q_sig's, the leaf walk's message rows). -/
  stream : ∀ j < 2 ^ (lay C).m, M.k ((lay C).sb + j) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j
  /-- The leaf walk's message lanes: the stream block's rows from `w2RowC`. -/
  xsL : ∀ r < nStepRowsC + 48, ∀ l < 17, M.k ((sigInLC C).xs + 17 * r + l) = FK.ofBF64 (MqU qm (w2RowC C + r) l)
  /-- Q_sig's gate is on. -/
  flag : M.k (sigIn C).flag = 1
  /-- Q_sig's message lanes from the split. -/
  xs : ∀ r < 449, ∀ l < 17, M.k ((sigIn C).xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit C.p + r) l)
  /-- The `Y` lanes `0 … 3` on Q_sig's digest cells. -/
  ys : ∀ r < 449, ∀ l < 4, M.k ((sigIn C).ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit C.p + r) l)
  /-- The `Y` lanes `0 … 3` on the leaf walk's digest cells. -/
  ysL : ∀ r < nStepRowsC + 48, ∀ l < 4, M.k ((sigInLC C).ys + 4 * r + l) = FK.ofBF64 (YqU qm (w2RowC C + r) l)
  /-- `PUB`: the key, the left statement. -/
  vk : digAt M.k (sigIn C).vk = vk
  cL : digAt M.k (sigIn C).cL = (hdrOf x).cL
  /-- The trace-digest cells: the `Y` block's row `B − 1`. -/
  md : ∀ l < 4, M.k ((sigIn C).md + l) = FK.ofBF64 (YqU qm (B - 1) l)
  /-- `σ'`'s cells: column 17. -/
  sg : sigAt' M.k (sigIn C).sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr))
  /-- `σ_leaf`'s cells: column 17 from word `2^10`, chain values in `permC` order. -/
  sl : sigAtP M.k (sigInLC C).sg = slM20 x qm
  /-- Q_sig's child-header cells are the stream's lanes `11 …` (the 18 lanes before `acc_in`). -/
  hd : ∀ k < 18, M.k ((sigIn C).hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k)
  /-- The whole `PUB` array from the flag: the header's lanes. -/
  pub : ∀ j < nPub, M.k ((sigIn C).flag + j) = hdrLane x j

/-! ## The input map's bundles and fields (`inMap_of_okGLB`'s, `inMapTGLB`'s twins over `C` on S2GU's layout) -/

open Lvm.M3 (lay26)

theorem sgLog_le (C : QCfg) : sgLog C ≤ 11 := by unfold sgLog; split <;> omega

theorem ysLog_le (C : QCfg) : ysLog C ≤ 10 := by unfold ysLog; split <;> omega

/-- **The input map's bundles from the check at S2GS** (`inMap_of_okGLB` on `inMapBGS`: `σ′`'s region `2^sgLog`, the
`KS` digests `4 × 2^ysLog` from row `ysRow0`). -/
theorem inMap_of_okGLS (C : QCfg) (hC : CfgU C) (B nPub : ℕ) (N : TNat) (pl : Lvm.Pub → List FK) (Q : Program)
    (tl : Typed.Lay) (hlay : tl.Ok Q) (pub : Lvm.Pub) (qm : Column CMain.nu20) (qr : Column 19)
    (hS : SBlkS CMain.sOffU20 qm qr) (hok : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (h : inMapBGS B nPub C Q tl N = true) :
    let M := memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)
    CellsAt M.k lay26 qm qr 17 14 (Lvm.QAsm.lay C).sb true (fun l ↦ l * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 1 (sgLog C) (sigIn C).sg true (fun _ ↦ 17 * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 17 9 (sigIn C).xs false (fun l ↦ xCol P20U l) ∧
      CellsAt M.k lay26 qm qr 4 (ysLog C) (ysB C) false (fun l ↦ ksYCol P20U l + ysRow0 C) ∧
      CellsAt M.k lay26 qm qr 4 0 (sigIn C).md false (fun l ↦ ksYCol P20U l + (B - 1)) ∧
      ∀ j < nPub, M.k ((sigIn C).flag + j) = (pl pub).getD j 0 := by
  intro M
  have hs : (layout0 C.p).s = CMain.sOffU20 := hC.s_eq
  simp only [inMapBGS, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hSt, hG⟩, hX⟩, hY⟩, hMd⟩, hP⟩ := h
  rw [hs] at hSt hG hX hY hMd hP
  have f1 : ∀ j < 17 * 2 ^ 14, j % 17 * 2 ^ 14 + j / 17 < 2 ^ 19 := fun j hj ↦ by omega
  have f2 : ∀ j < 1 * 2 ^ sgLog C, 17 * 2 ^ 14 + j / 1 < 2 ^ 19 := fun j hj ↦ by
    have h11 : 2 ^ sgLog C ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (sgLog_le C)
    omega
  refine ⟨bundleS_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ f1
      (fun l r ↦ by rw [hC.sCol_eq, sCol_P20U, Nat.add_assoc]) hSt,
    bundleS_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ f2
      (fun l r ↦ by rw [hC.sCol_eq, sCol_P20U, Nat.add_assoc]) hG,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ
      (fun l r ↦ by simp only [hC.xCol_eq]) hX,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ
      (fun l r ↦ by simp only [hC.ksYCol_eq]) hY,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ
      (fun l r ↦ by simp only [hC.ksYCol_eq]) hMd,
    fun j hj ↦ ?_⟩
  exact cell_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay pub qm qr hS hok hl hσ
    (List.all_eq_true.mp hP j (List.mem_range.mpr hj))

section FieldsS

variable {v : ℕ → FK} {qm : Column CMain.nu20} {qr : Column 19}

/-- The `Y` bundle's cells from row `r0` (`y_vU` at any first row and height). -/
theorem y_vS {yb r0 τ : ℕ} (hb : CellsAt v lay26 qm qr 4 τ yb false fun l ↦ ksYCol P20U l + r0)
    (hfit : r0 + 2 ^ τ ≤ 2 ^ 13) {r l : ℕ} (hr : r < 2 ^ τ) (hl : l < 4) :
    v (yb + 4 * r + l) = FK.ofBF64 (Lvm.E2U.YqU qm (r0 + r) l) := by
  have hm : (4 * r + l) % 4 = l := by (clear * - hl; omega)
  have hd : (4 * r + l) / 4 = r := by (clear * - hm; omega)
  have h := hb (4 * r + l) (by (clear * - hr hm; omega))
  beta_reduce at h
  rw [Nat.add_assoc, h, hm, hd, ksYCol_P20U,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; simp only [CMain.yOffU20]; (clear * - hr hl hfit; omega))]
  simp only [Lvm.E2U.YqU, Lvm.E2U.yU, colM, CMain.yOffU20]
  congr 2; (clear * -; omega)

/-- **The stream block's message lanes** on the stream cells (rows `r0 …`, the stream block's columns). -/
theorem xsL_vS {sb : ℕ} (hb : CellsAt v lay26 qm qr 17 14 sb true fun l ↦ l * 2 ^ 14)
    (hSB : SBlkS CMain.sOffU20 qm qr) {r0 n : ℕ} (hn : r0 + n ≤ 2 ^ 14) :
    ∀ r < n, ∀ l < 17, v (sb + 17 * r0 + 17 * r + l) = FK.ofBF64 (Lvm.E2U.MqU qm (r0 + r) l) := fun r hr l hl ↦ by
  have hm : (17 * (r0 + r) + l) % 17 = l := by (clear * - hl; omega)
  have hd : (17 * (r0 + r) + l) / 17 = r0 + r := by (clear * - hm; omega)
  have h := hb (17 * (r0 + r) + l) (by (clear * - hr hn hm; omega))
  beta_reduce at h
  rw [show sb + 17 * r0 + 17 * r + l = sb + (17 * (r0 + r) + l) by ring, h, hm, hd,
    comCell_SS sOffU20_fit hSB (by (clear * - hr hn hl; omega)),
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; simp only [CMain.sOffU20]; (clear * - hr hn hl; omega))]
  simp only [Lvm.E2U.MqU, Lvm.E2U.msgU, colM, CMain.sOffU20]
  congr 2; (clear * -; omega)

/-- **Cells whose words are `f 0 … f 596` hold the signature `sigOfP f`** (`sigAt'_eq_sigOfF` in `permC` order). -/
theorem sigAtP_eq_sigOfP {a : ℕ} {f : ℕ → Word} (h : ∀ j < 597, (v (a + j)).val.toBitVec = f j) :
    sigAtP v a = Lvm.CT.sigOfP f := by
  have h0 := h 0 (by norm_num)
  rw [Nat.add_zero] at h0
  have e1 : (v a).val.toNat = (f 0).toNat := by rw [← h0]; rfl
  have hpos : ∀ i < 133, posC i < 133 := fun i hi ↦ Lvm.XS.posC_lt hi
  have e2 : ((List.range wotsLen).map fun i => digAt v (a + 1 + 4 * posC i)) =
      (List.range wotsLen).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * posC k) 4) := by
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 133 := by simpa [wotsLen] using List.mem_range.mp hi
    have hp := hpos i hi'
    exact digAt_eq_digW fun l hl => by
      rw [show a + 1 + 4 * posC i + l = a + (1 + 4 * posC i + l) by ring]
      exact h _ (by (clear * - hp hl; omega))
  have e3 : ((List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t)) =
      (List.range sigHeight).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * wotsLen + 4 * k) 4) := by
    refine List.map_congr_left fun t ht => ?_
    have ht' : t < 16 := by simpa [sigHeight] using List.mem_range.mp ht
    refine digAt_eq_digW fun l hl => ?_
    rw [show a + 533 + 4 * t + l = a + (533 + 4 * t + l) by ring, h _ (by (clear * - ht' hl; omega))]
    congr 1
  unfold sigAtP Lvm.CT.sigOfP
  rw [e1, e2, e3]

/-- **`σ_leaf`'s cells** (`σ′`'s region's upper half, column 17 from row `2^10`) hold `slM20`. -/
theorem sl_vS {sg : ℕ} (hb : CellsAt v lay26 qm qr 1 11 sg true fun _ ↦ 17 * 2 ^ 14)
    (hSB : SBlkS CMain.sOffU20 qm qr) (x : List UInt8) : sigAtP v (sg + 2 ^ 10) = slM20 x qm := by
  unfold slM20
  refine sigAtP_eq_sigOfP fun j hj ↦ ?_
  have h := hb (2 ^ 10 + j) (by (clear * - hj; omega))
  beta_reduce at h
  rw [← Nat.add_assoc] at h
  have e : 17 * 2 ^ 14 + (2 ^ 10 + j) = Lvm.CT.slWP + j := by
    show _ = 17 * 2 ^ 14 + 1024 + j; (clear * -; omega)
  rw [h, Nat.div_one, comCell_rec (L := lay26) qm qr (by show _ < 2 ^ 19; (clear * - hj; omega)), e, wOfCol,
    Lvm.E2U.getD_recBU20 qm (by show 17 * 2 ^ 14 + 1024 + j < 2 ^ 19; (clear * - hj; omega)),
    ← hSB _ (by show 17 * 2 ^ 14 + 1024 + j < 2 ^ 19; (clear * - hj; omega))]
  rfl

/-- Four `PUB` cells from lane `k < 15` hold the header's digest at byte `8 + 8k` (`pub_digest_v` on 18 lanes). -/
theorem pub_digest_v18 {x : List UInt8} {pb : ℕ} (hp : ∀ j < 18, v (pb + j) = hdrLane x j) {k o : ℕ}
    (hk : k + 4 ≤ 18) (ho : 8 + 8 * k = o) : digAt v (pb + k) = digestAt (hdrBytesX x) o := by
  rw [← ho, digestAt_of (pub_bytes x) (by (clear * - hk; omega))]
  refine digOfW_congr fun l hl => ?_
  rw [Nat.add_assoc, hp _ (by (clear * - hk hl; omega))]

end FieldsS

theorem okSL_vk {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okSL vk c x = true) : (hdrOf x).vk = vk := by
  unfold okSL at hok
  generalize hdrOf x = hd at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.1.1.2

/-- **The input map on a pair's memory at S2GS** (`inMapTGLB`'s twin: `InMapMBS` from the guard's input map at a
configuration `C` on S2GU's layout with `leafOut`). -/
theorem inMapTGLS (C : QCfg) (hC : CfgU C) (B nPub : ℕ) (N : TNat) (pl : Lvm.Pub → List FK) (Q : Program)
    (tl : Typed.Lay) (pb : List UInt8 → Lvm.Pub) (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (hin : inMapBGS B nPub C Q tl N = true) (hB : B ≤ 2 ^ 13)
    (hm : 2 ^ (lay C).m ≤ 17 * 2 ^ 14) (hn : 18 ≤ nPub) (hlo : C.p.leafOut = true) (hks : ksSplit C.p = 7680)
    (hw2 : w2RowC C + (nStepRowsC + 48) = ksSplit C.p) (hw0 : ysRow0 C ≤ w2RowC C)
    (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} {x : List UInt8} (qm : Column CMain.nu20) (qr : Column 19)
    (hSB : SBlkS CMain.sOffU20 qm qr) (hok : okSL vk c x = true) (hb1 : (hdrOf x).b = 1) :
    InMapMBS B nPub C (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)) vk x qm qr := by
  obtain ⟨hS, hG, hX, hY, hMd, hP⟩ := inMap_of_okGLS C hC B nPub N pl Q tl hlay (pb x) qm qr hSB hreg hl hσ hin
  have hP' : ∀ j < nPub, (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn C).flag + j) =
      hdrLane x j := fun j hj ↦ (hP j hj).trans (hpub x j hj)
  have hP18 : ∀ j < 18, (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn C).flag + j) =
      hdrLane x j := fun j hj ↦ hP' j (lt_of_lt_of_le hj hn)
  have hsg : sgLog C = 11 := by unfold sgLog; rw [hlo]; rfl
  have hyl : ysLog C = 10 := by unfold ysLog; rw [hlo]; rfl
  have hy0 : ysRow0 C = 7168 := by unfold ysRow0; rw [hlo, hks]; rfl
  rw [hsg] at hG
  rw [hyl, hy0] at hY
  have hsb : (Lvm.QAsm.lay C).sb = 0 := rfl
  refine ⟨fun j hj ↦ stream_v hS (lt_of_lt_of_le hj hm), fun r hr l hl ↦ ?_, ?_, fun r hr l hl ↦ ?_,
    fun r hr l hl ↦ ?_, fun r hr l hl ↦ ?_, ?_, ?_, md_vU hB hMd,
    sg_v (fun j hj ↦ hG j (by (clear * - hj; omega))), ?_, fun k hk ↦ hd_v hS rfl k (by (clear * - hk; omega)), hP'⟩
  · -- the leaf walk's message rows: the stream's rows from `w2RowC`
    have h := xsL_vS hS hSB (r0 := w2RowC C) (n := nStepRowsC + 48) (by rw [hw2, hks]; norm_num) r hr l hl
    rw [hsb, Nat.zero_add] at h
    exact h
  · -- the gate: `PUB` lane 0 is `b = 1`
    have h0 := hP18 0 (by norm_num)
    rw [Nat.add_zero] at h0
    rw [h0]
    have e : u64At (hdrBytesX x) 8 = 1 := hb1
    simp only [hdrLane, Nat.mul_zero, Nat.add_zero, e]
    rfl
  · rw [xs_vU hX r hr l hl, hC.ksSplit_eq, ksSplit_P20U, ksSplit_P20]
  · -- Q_sig's digest rows: the `Y` bundle's rows `512 + r`
    have e : (sigIn C).ys = ysB C + 4 * 512 := by
      show ysQ C = _
      unfold ysQ; rw [hy0, hks]
    rw [e, show ysB C + 4 * 512 + 4 * r + l = ysB C + 4 * (512 + r) + l by ring,
      y_vS hY (by norm_num) (by (clear * - hr; omega)) hl, hks,
      show 7168 + (512 + r) = 7680 + r by (clear * -; omega)]
  · -- the leaf walk's digest rows: the `Y` bundle's rows `w2RowC − ysRow0 + r`
    have e : (sigInLC C).ys = ysB C + 4 * (w2RowC C - 7168) := by
      show ysB C + 4 * (w2RowC C - ysRow0 C) = _
      rw [hy0]
    have hw : w2RowC C - 7168 + r < 2 ^ 10 := by
      have : nStepRowsC = 352 := layC.2.2.2.2.2.2.2.2.2.1
      rw [hks, this] at hw2; rw [hy0] at hw0
      (clear * - hw2 hw0 hr this; omega)
    rw [e, show ysB C + 4 * (w2RowC C - 7168) + 4 * r + l = ysB C + 4 * (w2RowC C - 7168 + r) + l by ring,
      y_vS hY (by norm_num) hw hl]
    rw [hy0] at hw0
    rw [show 7168 + (w2RowC C - 7168 + r) = w2RowC C + r by (clear * - hw0; omega)]
  · have hv : digAt (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn C).flag + 1) = (hdrOf x).vk :=
      pub_digest_v18 hP18 (by norm_num) rfl
    exact hv.trans (okSL_vk hok)
  · exact (pub_digest_v18 hP18 (by norm_num) rfl :
      digAt (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn C).flag + 5) = (hdrOf x).cL)
  · exact sl_vS hG hSB x

/-- **S2GS's public values' header lanes, as words of the stream** (`pubOfW_hdrLanesW` without `σ_leaf`: `b`, `vk`,
`c_L`, `s`, `n`, `h`, then `acc_in`'s 16-B scalars from header byte `hdrFixS`). -/
theorem pubXTS_hdrLanesT (x : List UInt8) :
    (Lvm.pubXTS x).hdrLanesT = (List.range (18 + 2 * (Lvm.VEq.accVT + 1))).map fun k ↦
      kAt (Lvm.VEq.sigOfX x) (headerAt 8 + 8 * k) := by
  rw [show 18 + 2 * (Lvm.VEq.accVT + 1) = 1 + 4 + 4 + 4 + 1 + 4 + 2 * (Lvm.VEq.accVT + 1) by omega]
  simp only [Lvm.NS.map_range_add]
  have hd : (Lvm.VEq.hdX x).vk = digestAt (hdrBytesX x) 16 := rfl
  have hacc : ((List.range Lvm.VEq.accVT).map fun i ↦ fe16At (Lvm.VEq.sigOfX x) (headerAt (hdrFixS + 16 * i))) ++
      [fe16At (Lvm.VEq.sigOfX x) (headerAt (hdrFixS + 16 * Lvm.VEq.accVT))] =
      (List.range (Lvm.VEq.accVT + 1)).map fun i ↦ fe16At (Lvm.VEq.sigOfX x) (headerAt hdrFixS + 8 * 2 * i) := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun i _ ↦ ?_) ?_
    · exact congrArg (fe16At (Lvm.VEq.sigOfX x)) (by simp only [headerAt, hdrFixS]; (clear * - i; omega))
    · exact congrArg (fun o ↦ [fe16At (Lvm.VEq.sigOfX x) o]) (by simp only [headerAt, hdrFixS]; omega)
  unfold Pub.hdrLanesT Pub.hdrLanesW Lvm.pubXTS Lvm.pubOfWS pubOfW pubOf
  simp only [hd, Lvm.NS.digestLanes_digestAt, List.append_assoc, hacc, flatMap_lanes2, List.nil_append]
  refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_
    (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_)))))
  · simp [kAt]
  · refine List.map_congr_left fun i _ ↦ ?_
    rw [Lvm.NS.kAt_sigOfX, show 8 + 8 * (1 + i) = 16 + 8 * i by (clear * - i; omega)]
    rfl
  · exact Lvm.NS.seg _ 48 5 4 rfl
  · exact Lvm.NS.seg _ 80 9 4 rfl
  · simp [kAt, headerAt]
  · exact Lvm.NS.seg _ 120 14 4 rfl
  · exact List.map_congr_left fun j _ ↦
      congrArg (kAt (Lvm.VEq.sigOfX x)) (by simp only [headerAt, hdrFixS]; (clear * - j; omega))

/-- **S2GS's `PUB` lanes are the header's** (`pubXT_lane`'s twin, `pubLanesS P20S = 110` lanes). -/
theorem pubXTS_lane (x : List UInt8) {j : ℕ} (hj : j < 18 + 2 * (Lvm.VEq.accVT + 1)) :
    (Lvm.pubXTS x).hdrLanesT.getD j 0 = hdrLane x j := by
  rw [pubXTS_hdrLanesT, Lvm.NS.hdrLane_eq_kAt]
  simp [List.getD_eq_getElem?_getD, hj]

/-! ## The node's pair facts at S2GS (`readdTGLB` and section `PairB` over `NodeGCS`) -/

/-- **`ReaddOk` on a stream-block pair's memory at S2GS** (`readdTGLB` on `nodeChkBGS`). -/
theorem readdTGLS (C : QCfg) (hC : CfgU C) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat)
    (pl : Lvm.Pub → List FK) (pub : Lvm.Pub) (B nPub : ℕ) (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true)
    (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (hchk : nodeChkBGS B nPub C F Q tl N = true) (hc : nK C ≤ Q.cells .K)
    {qm : Column CMain.nu20} {qr : Column 19} (hτ : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ)
    (hLay : Lvm.M3.LayOk lay26 (mbTOf C F))
    (hM : M3Holds (Lvm.M3.inst lay26 (mbTOf C F) hτ) () (Lvm.M3.stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) (hlin : NonReaddHolds Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)) := by
  have hs : (layout0 C.p).s = CMain.sOffU20 := hC.s_eq
  have hnK : 17 * 2 ^ 14 ≤ nK C := by
    unfold nK obB qtB pbB mdB ysB xsB sgB nStream
    rw [hC.rl]; generalize 2 ^ C.aQT = u; generalize 2 ^ C.bo = w; generalize 2 ^ sgLog C = a
    generalize 2 ^ ysLog C = b; omega
  simp only [nodeChkBGS, Bool.and_eq_true] at hchk
  obtain ⟨⟨hin, hrd⟩, hsd⟩ := hchk
  rw [hs] at hrd
  simp only [mbSeedsOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsd
  obtain ⟨hblk, hlen⟩ := hsd
  have hS := (inMap_of_okGLS C hC B nPub N pl Q tl hlay pub qm qr hSB hreg hl hσ hin).1
  refine readdOk_of_chkLS sOffU20_mod sOffU20_fit C F Q tl N pl hlay pub qm qr hSB hreg hl hσ hrd ?_ ?_ hlin
  · intro τ wa wv hp y hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    exact mbRead_seeded C F lay26 hτ qm qr hLay hM hlen hk hy
  · intro lq hlq x' hx'
    obtain ⟨hl17, hq⟩ := hblk lq hlq
    rw [hC.rl] at hq
    have hx'16 : x' < 16 := hx'
    have hj : 17 * (lq.2 + x') + lq.1 < 17 * 2 ^ 14 := by omega
    have e : (Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x' =
        (Lvm.QAsm.lay C).sb + (17 * (lq.2 + x') + lq.1) := by ring
    have h16 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    refine ⟨?_, ?_⟩
    · have hsb : (Lvm.QAsm.lay C).sb = 0 := rfl
      rw [e, hsb]
      (clear * - hj hnK hc; omega)
    · have h1 := hS (17 * (lq.2 + x') + lq.1) hj
      beta_reduce at h1
      have e2 : (17 * (lq.2 + x') + lq.1) % 17 * 2 ^ 14 + (17 * (lq.2 + x') + lq.1) / 17 =
          lq.1 * 2 ^ C.rl + lq.2 + x' := by
        rw [hC.rl, h16]; omega
      have hs' : Lvm.sCol C.p lq.1 + lq.2 + x' = CMain.sOffU20 + (lq.1 * 2 ^ C.rl + lq.2 + x') := by
        rw [hC.sCol_eq, sCol_P20U, hC.rl]
        omega
      rw [e, h1, e2, hs', comCell_SS sOffU20_fit hSB (by rw [hC.rl, h16]; omega)]

/-- `qsigNoSl`'s chain and path outputs are `qsig`'s (the walk before `gSl` is the same). -/
theorem qsigNoSl_outs (I : SigIn) (p : Ptr) : (qsigNoSl I p).1.cm = (qsig I p).1.cm ∧
    (qsigNoSl I p).1.cc = (qsig I p).1.cc ∧ (qsigNoSl I p).1.pa = (qsig I p).1.pa := by
  unfold qsigNoSl qsig
  simp only [out_bind_eq, getPtr_apply_eq, pure_apply_eq, Ptr.adv_nil]
  exact ⟨trivial, trivial, trivial⟩

/-- `SigBits` reads the chain and path outputs only. -/
theorem sigBits_congr {I : SigIn} {o o' : SigOut} {v : ℕ → FK} (hcm : o'.cm = o.cm) (hcc : o'.cc = o.cc)
    (hpa : o'.pa = o.pa) (h : SigBits I o v) : SigBits I o' v := by
  have hx : xin I o' = xin I o := by funext i s l; simp only [xin, chainCell, hcm, hcc]
  have he : endc o' = endc o := by funext i l; simp only [endc, chainCell, hcm, hcc]
  exact ⟨h.idx_lo, h.idx_bit, h.idx_hi, h.md, h.cs, by rw [hx]; exact h.x, by rw [he]; exact h.e,
    by rw [hpa]; exact h.p, h.h, h.n_lo, h.n_hi, h.n_bit, h.n_top, h.n_low, h.cl, h.ls⟩

/-- **`SigBits` of `qsigNoSl`'s outputs** are `qsig`'s. -/
theorem sigBits_noSl {I : SigIn} {p : Ptr} {v : ℕ → FK} (h : SigBits I (qsig I p).1 v) :
    SigBits I (qsigNoSl I p).1 v :=
  have ho := qsigNoSl_outs I p
  sigBits_congr ho.1 ho.2.1 ho.2.2 h

section PairS

variable {C : QCfg} {B nPub : ℕ} {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat}
  (S : NodeGCS C B nPub F Q tl N) (pl : Lvm.Pub → List FK) (pb : List UInt8 → Lvm.Pub)
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

theorem regsCS (hC : CfgU C) : N.okB 23 19 = true := by
  have h := S.st.regs
  rwa [hC.nm, hC.nr] at h

theorem sigCS (hC : CfgU C) : SigInSL CMain.sOffU20 N := by
  have h := S.sig
  rwa [hC.s_eq] at h

theorem hlinCS (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    NonReaddHolds Q (memTX (N.instL pl Q tl) pb x qm qr) :=
  nonReadd_of_wiringX Q tl _ S.st.wf S.st.twins S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW

theorem readdCS (hC : CfgU C) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : Lvm.M3.LayOk lay26 N.mbT) (hM : M3Holds (Lvm.M3.inst lay26 N.mbT hτ) () (Lvm.M3.stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    ReaddOk Q (memTX (N.instL pl Q tl) pb x qm qr) := by
  have hτ' : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ := fun t ht ↦ hτ t (by rw [S.mb]; exact ht)
  have hL' : Lvm.M3.LayOk lay26 (mbTOf C F) := by rwa [S.mb] at hL
  exact readdTGLS C hC F Q tl N pl (pb x) B nPub S.st.hlay (regsCS S hC) S.st.hlayOk (sigCS S hC) S.chk S.cells hτ'
    hL' (m3Holds_eq S.mb hM) hSB (hlinCS S pl pb hone hW)

/-- **The program holds and asserts on a good S2GS pair's memory** (`hholdsCB` over `NodeGCS`). -/
theorem hholdsCS (hC : CfgU C) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : Lvm.M3.LayOk lay26 N.mbT) (hM : M3Holds (Lvm.M3.inst lay26 N.mbT hτ) () (Lvm.M3.stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    (N.instL pl Q tl).Q.Holds (memTX (N.instL pl Q tl) pb x qm qr) ∧
      (N.instL pl Q tl).Q.Asserts (memTX (N.instL pl Q tl) pb x qm qr) :=
  holds_memTX S.st.wf S.st.twins S.st.hlay hone hW (readdCS S pl pb hC hone hW hτ hL hM hSB)

theorem outsOnCS (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    OutsOnC C (memTX (N.instL pl Q tl) pb x qm qr).k := by
  obtain ⟨bw, haux⟩ := S.aux
  exact outsOnC_of C tl _ bw haux fun hk hj hr ↦
    auxRow_of_wiringX Q tl _ S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW hk hj hr

/-- **Q_link's position bits on a good S2GS pair** (`hposCB` with the stream cells given). -/
theorem hposCS (hSt : StreamOk C.p) (hQ : QOk C.p (lay C)) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr))
    (hst : ∀ j < 2 ^ (lay C).m, (memTX (N.instL pl Q tl) pb x qm qr).k ((lay C).sb + j) =
      laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j) :
    ∀ k < (opens C.p).length, ∀ j < ((opens C.p).getD k default).L.t,
      ∀ z < ((opens C.p).getD k default).L.height,
      (memTX (N.instL pl Q tl) pb x qm qr).k
          (bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z) =
        if ansBit C.p (wsC qr) (((opens C.p).getD k default).pe + j / 8)
          (j % 8 * ((opens C.p).getD k default).L.height + z) then 1 else 0 :=
  hposTC (C := C) hSt hQ (outsOnCS S pl pb hone hW) hst

/-- **Q_sig's first walk's `SigBits`** on a good S2GS pair's memory (`hbitsCB` for `qsigNoSl`). -/
theorem hbitsCS (hln : C.ln = 20) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    SigBits (sigIn C) (qsigNoSl (sigIn C) (p1P (lay C) (nK C) 0 C.p)).1
      (memTX (N.instL pl Q tl) pb x qm qr).k :=
  sigBits_noSl (sigBits_ofC C (outsOnCS S pl pb hone hW) ⟨by omega, by omega⟩)

end PairS

/-- **The S2GS program's three parts hold** (`parts_of_holdsP` for `qlink; qsigSC; qa`). -/
theorem parts_of_holdsS {α : Type} {p : Params} {lay : Layout} {I I2 : SigIn} {qa : BM α} {nK nE : ℕ} {M : Mem}
    (hH : (toProgram nK nE (do qlink p lay; let _ ← qsigSC I I2; qa)).Holds M)
    (hA : (toProgram nK nE (do qlink p lay; let _ ← qsigSC I I2; qa)).Asserts M) :
    Ok (ctxOf (toProgram nK nE (do qlink p lay; let _ ← qsigSC I I2; qa))) M (qlink p lay) (p0 nK nE) ∧
      Ok (ctxOf (toProgram nK nE (do qlink p lay; let _ ← qsigSC I I2; qa))) M (qsigSC I I2) (p1P lay nK nE p) ∧
      Ok (ctxOf (toProgram nK nE (do qlink p lay; let _ ← qsigSC I I2; qa))) M qa
        ((p1P lay nK nE p).adv (qsigSC I I2 (p1P lay nK nE p)).2) := by
  rw [toProgram_holds] at hH
  rw [toProgram_asserts] at hA
  have hh : SegsHold (ctxOf (toProgram nK nE (do qlink p lay; let _ ← qsigSC I I2; qa))) M (p0 nK nE)
      ((do qlink p lay; let _ ← qsigSC I I2; qa : BM α) (p0 nK nE)).2 := hH
  have ha : SegsAssert M (p0 nK nE) ((do qlink p lay; let _ ← qsigSC I I2; qa : BM α) (p0 nK nE)).2 := hA
  rw [hold_bind, hold_bind] at hh
  rw [assert_bind, assert_bind] at ha
  exact ⟨⟨hh.1, ha.1⟩, ⟨hh.2.1, ha.2.1⟩, ⟨hh.2.2, ha.2.2⟩⟩

/-- `cfgS20` is on S2GU's `C_main` layout. -/
theorem cfgU_S20 : CfgU cfgS20 := ⟨layout0_P20S, rfl, rfl, by decide, rfl, rfl, rfl⟩

/-- **SLF-STMT 7h** (owner C; RE-FREEZE R2: the memory `memTX TiS20 pubXTS`): **the node's cells on a good S2GS
pair** (`inMap_of_okGLU`'s twin, from the guard's input map, `qr` the stream block of `qm`). -/
theorem inMapS20 (S : NodeGS) (H : THypS TiS20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 → GoodTS TiS20 H x qm qr ∧ SBlkU qm qr →
      InMapMBS (spongeBlocks P20S) (pubLanesS P20S) cfgS20 (memTX TiS20 Lvm.pubXTS x qm qr) vk x qm qr := by
  intro c x qm qr hok hb hG
  have hC := cfgU_S20
  have hreg : NTS20.toN.okB 23 19 = true := by have h := S.st.regs; rwa [hC.nm, hC.nr] at h
  have hσ : SigInSL CMain.sOffU20 NTS20.toN := by have h := S.sig; rwa [hC.s_eq] at h
  have hchk := S.chk
  simp only [nodeChkBGS, Bool.and_eq_true] at hchk
  have hB : spongeBlocks P20S ≤ 2 ^ 13 := by rw [sizes_P20S.1.2.2.2.2.1]; norm_num
  exact inMapTGLS cfgS20 hC _ _ NTS20.toN Pub.hdrLanesT QS20 layS20 Lvm.pubXTS S.st.hlay hreg S.st.hlayOk hσ
    hchk.1.1 hB (by decide) (by decide) rfl (by decide)
    (by rw [w2RowC, layC.2.2.2.2.2.2.2.2.2.1]; decide) (by rw [w2RowC, layC.2.2.2.2.2.2.2.2.2.1]; decide)
    (fun x _ hj ↦ pubXTS_lane x (lt_of_lt_of_le hj (by decide))) qm qr hG.2 hok hb

end Lvm.E2Q
