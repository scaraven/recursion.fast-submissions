-- New for lvm6 (WP NODE5b). `NodeFacts6`'s hypotheses from the static guard (`staticOk6_ok`'s named fields, the
-- regions of `tyLayOkRB`) and the relation `rest x q := SGood6 q ∧ TGood6 (inst6 B h x) q`, on the candidate pair
-- `toPair q`: the stream and signature cells are the stack's `STREAM` words (GRD's `StreamCells`/`SigCells`, the
-- region maps), the readers read the stack, the `KS` aliases hold the stack's sponge columns (KSA), the node's own
-- sponge rows (`OutRel`, `SpongeLink`, `hM`) are `SGood6`'s (RV4 F3), the `BITS` cells (F2) and the position bits.
import Lvm6NodeAsmR
import Lvm6NodeCells
import Lvm6NodeBitsSound
import Lvm6TyStmt

/-!
# The guard's and the relation's facts at the deployed circuit (WP NODE5b, targets 1 and 3)

Over a `TyBase6` `B` with `staticOk6 B = true`, a header `x`, a stack `q`, the pair `toPair q` and the memory
`M = memTi B.Ti L6 pw (toPair q)` (any public words `pw`):
* **Cells** (`stream_cell6`, `sig_cell6`): stream cell `sbC + j` holds stack word `streamIdx j`, signature cell
  `sgC + i` holds stack word `streamIdx (sB + i)` (GRD's `cells6`, `tyLayOkRB`'s regions, `regW6_affine`).
* **Readers** (`trOfS`, `σOfS`, `σlOfS`: the trace, `σ'` and `σ_leaf` as stored, read off the stack's `STREAM`
  slot) and `wsOf M = wsS q` (`wsOf_eq6`).
* **`KS` aliases** (`ksAlias6`: KSA's `KSAliasOk` field at `X := xOf q`, `Yl := yOf q`); **sponge rows** from
  `SGood6` (`outRel6`, `spongeLink6`), **`hM`** (`hM6`), **`hmd`** (`md_of_alias`).
* **`BITS`** (`sigBits6P`, `sigBitsC6P`, `posOut6P`: NODE3's lemmas from `Deployed6.bits`, the Prop field) and the
  position bits **`posBits6_of`** (`PosBits6`, index arithmetic with `streamOkP17`, `opensOKP17`, `qOkSP17`).
* **`AsmOk6`** (run time, `asmChk6`): `Q.cells .K < 2^64 − 1`, the stream cells exist, `readdChk6B`; with it
  **`readdOk6`** (RV4 M2) and `GInj`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Asm

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V LeanVM.Protocol
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink Lvm.Wots Lvm.Bits
open Lvm6.Ty (TInst6 TGoodE NoE3 toPair L6 colOf)
open Lvm6.Ty.TInst6 (comCell)
open Lvm6.Node.Dep Lvm6.Node.Mb
open Lvm6.V (TyBase6 staticOk6 staticOk6_ok StaticOk6 tyLayOkRB)
open LeanVM.Parameters

/-! ## The stack's `STREAM` words and the readers -/

/-- **Stream word `j` of a stack** (`C_rec`'s slot 33). -/
def stW (q : Stack) (j : ℕ) : FK := FK.ofBF64 (q (QD.streamIdx j))

/-- The stream words of a stack. -/
def wsS (q : Stack) : List Word := (List.range (2 ^ 18)).map fun j ↦ (stW q j).val.toBitVec

/-- The signature cells' values read off a stack: cell `sgC + i` is stream word `sB + i`. -/
def sigV (q : Stack) (n : ℕ) : FK := stW q (QD.sB + (n - sgC))

/-- **The child's trace read off a stack.** -/
def trOfS (q : Stack) : Trace := decode6 P6 (wsS q)

/-- **`σ'` read off a stack** (stream words `sB …`, `readSig`'s order). -/
def σOfS (q : Stack) : Sig := sigAt' (sigV q) sgC

/-- **`σ_leaf` read off a stack** (stream words `sB + 597 …`, as stored). -/
def σlOfS (q : Stack) : Sig := sigAt' (sigV q) (sgC + 597)

theorem wsOf_getD (M : Mem) {n : ℕ} (hn : n < 2 ^ 18) : (wsOf M).getD n 0 = (M.k (sbC + n)).val.toBitVec := by
  simp only [wsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn, Option.map_some,
    Option.getD_some]

theorem comCell_rec6 (q : Stack) {n : ℕ} (hn : n < 2 ^ 18) :
    comCell L6 (toPair q).1 (toPair q).2 true n = q (QD.streamIdx n) := by
  simp only [comCell, toPair, colOf, if_true, dif_pos hn, Vector.getElem_ofFn]
  congr 1
  simp only [QD.streamIdx, QD.recSlot, Ty.recOff]
  omega

theorem comCell_main6 (q : Stack) {n : ℕ} (hn : n < 2 ^ 24) :
    comCell L6 (toPair q).1 (toPair q).2 false n = q n := by
  simp only [comCell, toPair, colOf, Bool.false_eq_true, if_false, dif_pos hn, Vector.getElem_ofFn]

/-- The `KS` alias targets lie in `C_main` (KSA's parameters, small data). -/
theorem ksTgt_lt {f : Lvm6.KSP.KSFam} (hf : f ∈ ksP.fams) {r l : ℕ} (hr : r < f.rows) (hl : l < f.w) :
    f.tgt r l < 2 ^ 24 := by
  have hfit : ∀ g ∈ ksP.fams, g.tb + (g.w - 1) * g.ts + g.rows ≤ 2 ^ 24 := by decide
  have := hfit f hf
  have hm : l * f.ts ≤ (f.w - 1) * f.ts := Nat.mul_le_mul_right _ (by omega)
  unfold Lvm6.KSP.KSFam.tgt
  omega

section Static

variable {B : TyBase6} (h : staticOk6 B = true)
include h

/-- **The guard's regions** (`tyLayOkRB`): disjoint, the `S_flat` region at `B.bs`, the `σ` region at `B.bg`. -/
theorem regs_of_static :
    yDisjB B.Ti.lay.yregs = true ∧ (⟨B.bs, Ty.relayRounds, .sflat⟩ : YReg) ∈ B.Ti.lay.yregs ∧
      (⟨B.bg, QD.sigLog, .sigma⟩ : YReg) ∈ B.Ti.lay.yregs :=
  ⟨(staticOk6_ok h).streamRegs.disj, (staticOk6_ok h).streamRegs.sflat, (staticOk6_ok h).streamRegs.sigma⟩

variable (pw : ℕ → FK) (q : Stack)

/-- **Stream cell `sbC + j` holds the stack's stream word `j`.** -/
theorem stream_cell6 {j : ℕ} (hj : j < 2 ^ 18) : (memTi B.Ti L6 pw (toPair q)).k (sbC + j) = stW q j := by
  have hc := (cells6 (staticOk6_ok h).node.grd).1 j hj
  rw [memTi_cell hc.1 hc.2]
  obtain ⟨hd, hr1, -⟩ := regs_of_static h
  have hsrc : B.Ti.src? (B.bs + j) = some .sflat :=
    src?_of_mem hd hr1 ⟨Nat.le_add_right _ _, by simpa [Ty.relayRounds] using hj⟩
  have hw : B.Ti.sflatW (B.bs + j) = j := by
    rw [B.mapsReg.2.1]
    exact (regW6_affine _ hd hr1 rfl hj).trans (Nat.zero_add j)
  simp only [TInst6.zOf, hsrc, hw, comCell_rec6 q hj, stW]

/-- **Signature cell `sgC + i` holds the stack's stream word `sB + i`** (`σ'`, then `σ_leaf` as stored). -/
theorem sig_cell6 {i : ℕ} (hi : i < 2 * 597) :
    (memTi B.Ti L6 pw (toPair q)).k (sgC + i) = stW q (QD.sB + i) := by
  have hc := (cells6 (staticOk6_ok h).node.grd).2 i hi
  rw [memTi_cell hc.1 hc.2]
  obtain ⟨hd, -, hr2⟩ := regs_of_static h
  have hi' : i < 2 ^ QD.sigLog := by simp only [QD.sigLog]; omega
  have hsrc : B.Ti.src? (B.bg + i) = some .sigma :=
    src?_of_mem hd hr2 (y := B.bg + i) ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi' _⟩
  have hw : B.Ti.sigmaW (B.bg + i) = QD.sB + i := by
    rw [B.mapsReg.2.2]
    exact regW6_affine _ hd hr2 rfl hi'
  have hn : QD.sB + i < 2 ^ 18 := by simp only [QD.sB]; omega
  simp only [TInst6.zOf, hsrc, hw, comCell_rec6 q hn, stW]

/-- **The stream words are the stack's.** -/
theorem wsOf_eq6 : wsOf (memTi B.Ti L6 pw (toPair q)) = wsS q :=
  List.map_congr_left fun j hj ↦ by rw [stream_cell6 h pw q (List.mem_range.mp hj)]

theorem wsS_getD (q : Stack) {k : ℕ} (hk : k < 2 ^ 18) : (wsS q).getD k 0 = (stW q k).val.toBitVec := by
  simp only [wsS, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]

/-- **The trace and `σ'` readers are the cells'.** -/
theorem readers6 :
    trOfS q = decode6 P6 (wsOf (memTi B.Ti L6 pw (toPair q))) ∧
      σOfS q = sigAt' (memTi B.Ti L6 pw (toPair q)).k sigI.sg ∧
      σlOfS q = sigAt' (memTi B.Ti L6 pw (toPair q)).k (sgC + 597) := by
  refine ⟨by rw [wsOf_eq6 h pw q]; rfl, ?_, ?_⟩
  · show sigAt' (sigV q) sgC = sigAt' _ sgC
    refine sigAt'_congr fun i hi ↦ ?_
    rw [sig_cell6 h pw q (by omega), sigV, Nat.add_sub_cancel_left]
  · refine sigAt'_congr fun i hi ↦ ?_
    rw [show sgC + 597 + i = sgC + (597 + i) by omega, sig_cell6 h pw q (by omega), sigV,
      Nat.add_sub_cancel_left]

/-- **CB-4's message rows are the stream** (`hM`, `Mx := mOf q`). -/
theorem hM6 : ∀ i < 7168, ∀ l < 17,
    (SP.mOf q i l).toBitVec.toNat = lw (wsOf (memTi B.Ti L6 pw (toPair q))) (17 * i + l) := by
  intro i hi l hl
  rw [wsOf_eq6 h pw q, lw, wsS_getD h q (by omega)]
  rfl

/-- **The `KS` alias cells hold the stack's sponge columns** (KSA's field; the targets lie in `C_main`). -/
theorem ksAlias6 : KSAlias (memTi B.Ti L6 pw (toPair q)).k (SP.xOf q) (SP.yOf q) :=
  (staticOk6_ok h).node.ks L6 pw (toPair q) q fun _ hf _ hr _ hl ↦ (comCell_main6 q (ksTgt_lt hf hr hl)).symm

end Static

/-! ## The node's sponge rows (RV4 F3: `SGood6`, `ks := spOf q`, `Mx := mOf q`, `X := xOf q`, `Yl := yOf q`) -/

theorem outRel6 {q : Stack} (hS : SP.SGood6 q) : Lvm.KG.OutRel 13 25 (SP.spOf q) (SP.yOf q) := hS.2.1

theorem spongeLink6 {q : Stack} (hS : SP.SGood6 q) :
    Lvm.KG.SpongeLink 13 (rowsBK2 3816 7567 8032) (SP.spOf q) (fun i l ↦ SP.yOf q l i)
      (Lvm.KG.ksMsg 7168 (SP.mOf q) (SP.xOf q)) := by
  have hl := hS.2.2
  unfold SP.LinkRel at hl
  rw [SP.ksSplit_eq, contRows6_eq] at hl
  exact hl

/-! ## `BITS` (F2) from `Deployed6.bits` -/

section Bits

open Lvm6.Node.BitsS Lvm.BitsTab Lvm.QTyped Lvm.SigBits

variable {lay : Typed.Lay} {z : ℕ → FK}
  (hb : ∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ w, boolBlk6 S w x ∈ lay.aux ∧ outBlk6 S w x ∈ lay.aux)
  (hrow : ∀ blk ∈ lay.aux, ∀ r ∈ blk.rows, ARowHolds lay z 0 r)
include hb hrow

theorem bitsOuts6P :
    ∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ wv : FK, (S.rd = true → (memOf lay z).k (S.wc x) = wv) ∧
      ∀ i < S.outs.length, (S.out i).Valid → (memOf lay z).k (S.oc i x) = ⟨(S.out i).word wv.val⟩ := by
  intro S hS x hx
  obtain ⟨w, hbo, hou⟩ := hb S hS x hx
  exact rowBlk6_sound lay z S w x (hrow _ hbo) (hrow _ hou)

/-- `sigBits6` from the guard's Prop field. -/
theorem sigBits6P : SigBits sigI (qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)).1.1 (memOf lay z).k :=
  sigBits_of_outs _ _ _ (fun _ ↦ noPl) (bitsSpecs6 lay)
    (fun B hB ↦ by
      simp only [bitsSpecs6, sigSpecs6]
      exact List.mem_append_left _ (List.mem_append_left _ hB))
    ⟨by decide, by decide⟩ (bitsOuts6P hb hrow)

/-- `sigBitsC6` from the guard's Prop field. -/
theorem sigBitsC6P : SigBitsC sigIl (qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)).1.2.pa (memOf lay z).k :=
  sigBitsC_of_outs _ sigIl _ (fun _ ↦ noPl) (bitsSpecs6 lay)
    (fun B hB ↦ by
      simp only [bitsSpecs6, sigSpecs6]
      exact List.mem_append_left _ (List.mem_append_right _ hB))
    (bitsOuts6P hb hrow)

/-- `posOut6` from the guard's Prop field. -/
theorem posOut6P {k : ℕ} (hk : k < opensP17.length) {l : ℕ} (hl : l < 2) {q : ℕ} (hq : q < nDraws k)
    {zz : ℕ} (hzz : zz < 64) :
    (memOf lay z).k (posOut k q (64 * l + zz)) =
      ⟨(BOut.bit zz).word ((memOf lay z).k (sbC + ansLane6 P6 ((opensP17.getD k default).pd0 + q) + l)).val⟩ := by
  have hS : posSpec6 k l ∈ bitsSpecs6 lay := by
    simp only [bitsSpecs6]
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp
  obtain ⟨wv, h1, h2⟩ := bitsOuts6P hb hrow _ hS q hq
  have hout : (posSpec6 k l).out zz = .bit zz := getD_bit hzz
  have := h2 zz (by simp [posSpec6, hzz]) (by rw [hout]; exact hzz)
  rw [hout, posSpec6_oc] at this
  have e := h1 (by simp only [posSpec6])
  rw [posSpec6_wc] at e
  rw [e]
  exact this

end Bits

/-! ## The position bits (`PosBits6`) -/

/-- Every deployed opening has positions per draw. -/
theorem opens_per : opensP17.all (fun o ↦ decide (0 < o.per)) = true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp Mb.nodeStaticB_true).1).2

/-- An entry of a window of a list (KDN: proved at a variable list; at `planOf P17` the kernel evaluated the plan). -/
theorem getD_of_drop_take {P pl : List PE6} {i0 n m : ℕ} (hplan : (P.drop i0).take n = pl) (hm : m < n) :
    P.getD (i0 + m) default = pl.getD m default := by
  rw [← hplan, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hm,
    List.getElem?_drop]

/-- **The draw of position `j` of opening `k` is an entry of the plan before a node entry**, whose bits fit an
answer: `pd0 + j / per < P6.length` and `j % per · h + h ≤ 128` (`opensOKP17`, `qOkSP17`, `streamOkP17`). -/
theorem draw_facts {k : ℕ} (hk : k < opensP17.length) {j : ℕ} (hj : j < (opensP17.getD k default).t) :
    (opensP17.getD k default).pd0 + j / (opensP17.getD k default).per < P6.length ∧
      j % (opensP17.getD k default).per * (opensP17.getD k default).h + (opensP17.getD k default).h ≤ 128 := by
  set o := opensP17.getD k default with ho
  have hmem : o ∈ opensP17 := by
    rw [ho, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hOK := opensOKP17
  simp only [opensOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOK
  obtain ⟨⟨-, hlen⟩, hplan⟩ := hOK.1 o hmem
  have hq := qOkSP17
  simp only [qOkS6, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨⟨⟨hpath, -⟩, -⟩, -⟩, -⟩ := hq.2 o hmem
  have hy : 1 < 1 + o.path := by omega
  have hjt : j * (1 + o.path) + 1 < o.t * (1 + o.path) := by
    have : (j + 1) * (1 + o.path) ≤ o.t * (1 + o.path) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  -- by terms, not `omega` (KDN: `omega`'s certificate over the closed atom `(planOf P17).length` made the kernel
  -- evaluate the plan)
  have hiP : o.i0 + (j * (1 + o.path) + 1) < (planOf Lvm6.P17).length :=
    lt_of_lt_of_le (Nat.add_lt_add_left hjt _) hlen
  have hent := getD_of_drop_take hplan hjt
  rw [Open6Q.plan_getD o hj hy, if_neg (by omega)] at hent
  have he := streamOk6_entry streamOkP17 hiP
  rw [hent] at he
  simp only [entryOk6, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hsh⟩, hpd⟩, -⟩, -⟩ := he
  exact ⟨lt_trans hpd hiP, hsh⟩

/-- **`Q_link`'s position bits** (`QIn6.bits`) from `posOut6`: bit `z` of position `j` of opening `k` is bit
`j % per · h + z` of the answer of draw `pd0 + j / per`. -/
theorem posBits6_of {lay : Typed.Lay} {z : ℕ → FK}
    (hb : ∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ w, boolBlk6 S w x ∈ lay.aux ∧ outBlk6 S w x ∈ lay.aux)
    (hrow : ∀ blk ∈ lay.aux, ∀ r ∈ blk.rows, ARowHolds lay z 0 r) :
    PosBits6 (wsOf (memOf lay z)) (memOf lay z) := by
  intro k hk j hj zb hzb
  obtain ⟨hdraw, hsh⟩ := draw_facts hk hj
  have hmem : opensP17.getD k default ∈ opensP17 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hper : 0 < (opensP17.getD k default).per := by
    simpa using List.all_eq_true.mp opens_per _ hmem
  generalize hO : opensP17.getD k default = o at hdraw hsh hper hj hzb ⊢
  have hh : 0 < o.h := by omega
  have hn128 : j % o.per * o.h + zb < 128 := by omega
  have hq : j / o.per < nDraws k := by
    have h1 : (j / o.per + 1) * o.per ≤ o.t + o.per - 1 := by
      have := Nat.div_mul_le_self j o.per
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 := (Nat.le_div_iff_mul_le hper).mpr h1
    unfold nDraws; rw [hO]; omega
  have hl2 : (j % o.per * o.h + zb) / 64 < 2 := by omega
  have hz64 : (j % o.per * o.h + zb) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hP := posOut6P hb hrow hk hl2 hq hz64
  rw [show 64 * ((j % o.per * o.h + zb) / 64) + (j % o.per * o.h + zb) % 64 = j % o.per * o.h + zb by omega,
    hO] at hP
  have hpos : Dep.posOut k (j / o.per) (j % o.per * o.h + zb) = bitBase6 opensP17 lay6 k + o.h * j + zb := by
    have hnu : j % o.per * o.h + zb < usedBits k := by
      unfold usedBits; rw [hO]
      have h3 : (j % o.per + 1) * o.h ≤ o.per * o.h := Nat.mul_le_mul_right _ (Nat.mod_lt _ hper)
      rw [Nat.add_mul, Nat.one_mul] at h3; omega
    have hdiv : (j % o.per * o.h + zb) / o.h = j % o.per := by
      rw [Nat.mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt hzb, Nat.add_zero]
    have hmod : (j % o.per * o.h + zb) % o.h = zb := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hzb]
    have hjq : j / o.per * o.per + j % o.per = j := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod j o.per
    unfold Dep.posOut; rw [hO, if_pos hnu, hdiv, hmod, hjq]
  rw [← hpos, hP]
  have hidx : ansLane6 P6 (o.pd0 + j / o.per) + (j % o.per * o.h + zb) / 64 < 2 ^ 18 := by
    have hw : hashedLen6 P6 ≤ 8 * (wsOf (memOf lay z)).length := by
      rw [wsOf_length, W.blocks_P17.1]; norm_num
    have h4 : ansLane6 P6 (o.pd0 + j / o.per) + 4 ≤ 2 ^ 18 := by
      have := ansLane6_bound streamOkP17 hw hdraw
      rw [wsOf_length] at this; exact this
    omega
  unfold ansBit6
  rw [lw, wsOf_getD _ hidx, ← Nat.add_assoc]
  exact Lvm.QSig.SigH.w64_bit _ hz64

end Lvm6.Node.Asm
