-- New for lvm6 (WP NODE5b). The node theorem's facts at the deployed circuit: `NodeFacts6` (everything except the
-- decision `hdec`, NODE5a's) from the static guard (`staticOk6`, its named fields), this WP's run-time facts
-- (`AsmOk6`: the `readd` check, two cell-count comparisons) and the relation `rest6 := SGood6 ∧ TGood6 (inst6 …)`;
-- then `node6V` itself with the stack readers.
import Lvm6NodeAsmG

/-!
# `NodeFacts6` on the deployed circuit (WP NODE5b, target 4)

For a layout `lay` and a class table `P`, `B = tyBaseOf lay P` (the deployed `tiOf6 P` is `tyBaseOf layQ6 P`):
* **`rest6 B h x q := SGood6 q ∧ TGood6 (inst6 B h x) q`**, what the extractor's `GoodAll` gives beside `TreeOk`.
* **`DecAt Φ B x q`**: NODE5a's `hdec`, verbatim `NodeFacts6`'s decision at the pair `toPair q`, the public words
  `pwOf B.Ti (hdrBytes x)`, the stream words of the memory; `decAt_iff`: the same at the key `x.vk` and the stack's
  stream words `wsS q`.
* **`readdOk6`** (RV4 M2): `ReaddOk` from `readdChk6B` (`AsmOk6.readd`), MBT's `mbRead_seeded6`, the stream cells.
* **`nodeFacts6_deployed`**: `staticOk6 B = true`, `AsmOk6 B.Ti`, `x.b = 1`, `TreeOk` (unused), `rest6`, `DecAt` ⟹
  `NodeFacts6 Φ trOfS σOfS σlOfS x q`.
* **`node6V_deployed`**: `Stmt.node6V (VSasm Φ) (rest6 B h) (childOf6 trOfS σOfS) σlOfS` given `DecAt` in node mode.
-/

set_option autoImplicit false

namespace Lvm6.Node.Asm

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V LeanVM.Protocol
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink Lvm.Wots Lvm.Bits
open Lvm6.Ty (TInst6 TGoodE NoE3 toPair L6)
open Lvm6.Node.Dep Lvm6.Node.Mb
open Lvm6.Node.Ti (tyBaseOf tiOfL tiOfL_mbT tiOfL_τ)
open Lvm6.V (TyBase6 staticOk6 staticOk6_ok StaticOk6 inst6)
open LeanVM.Parameters

/-- **The relation `rest`** at the deployed guard: the sponge relation and the typed relation of the instance at the
header (RV4 §0: `Ext6.extract` gets `GoodAll`). -/
def rest6 (B : TyBase6) (h : staticOk6 B = true) (x : Hdr) (q : Stack) : Prop :=
  SP.SGood6 q ∧ Ty.TGood6 (inst6 B h x) q

/-- The memory of the pair `toPair q` at the header's public words. -/
noncomputable def memAt (B : TyBase6) (x : Hdr) (q : Stack) : Mem :=
  memTi B.Ti L6 (pwOf B.Ti (hdrBytes x)) (toPair q)

/-- **The decision `hdec`** (NODE5a), as `NodeFacts6` states it at `memAt B x q`. -/
def DecAt (Φ : Phases) (B : TyBase6) (x : Hdr) (q : Stack) : Prop :=
  F6 Φ P17 (digAt (memAt B x q).k sigI.vk) (reassemble6 P6 (decode6 P6 (wsOf (memAt B x q))))
    (accOf P17 (reassemble6 P6 (decode6 P6 (wsOf (memAt B x q)))) (decode6 P6 (wsOf (memAt B x q)))) = true

/-- **`DecAt` at the key and the stack's stream words.** -/
theorem decAt_iff {B : TyBase6} (h : staticOk6 B = true) (Φ : Phases) (x : Hdr) (q : Stack) :
    DecAt Φ B x q ↔ F6 Φ P17 x.vk (reassemble6 P6 (decode6 P6 (wsS q)))
      (accOf P17 (reassemble6 P6 (decode6 P6 (wsS q))) (decode6 P6 (wsS q))) = true := by
  unfold DecAt memAt
  rw [wsOf_eq6 h _ q, show sigI.vk = pbC + 11 from rfl,
    key_cells (staticOk6_ok h).node.pub L6 x (toPair q)]

/-- **`GInj` below the cell count** (`AsmOk6.cellsLt`, `FKx_pow_inj`). -/
theorem ginj6 {Ti : TInst6} (hA : AsmOk6 Ti) : GInj (max ((ctxOf Ti.Q).cells .K) (sbC + 2 ^ 18)) := by
  intro a b ha hb hab
  have hm : max ((ctxOf Ti.Q).cells .K) (sbC + 2 ^ 18) ≤ 2 ^ 64 - 1 :=
    max_le hA.cellsLt.le (by simp only [sbC]; norm_num)
  exact Lvm.FK.FKx_pow_inj (lt_of_lt_of_le ha hm) (lt_of_lt_of_le hb hm) hab

theorem pow_inj1024 : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b :=
  fun _ _ ha hb h ↦ Lvm.FK.FKx_pow_inj (by omega) (by omega) h

-- the plan's lists are data: never unfold them while elaborating (their facts are `mbStatic6`'s)
attribute [local irreducible] seedBlocks6 capTaus6 capRegs6

section Deployed

variable (lay : Lay) (P : Lvm6.V.PT) (h : staticOk6 (tyBaseOf lay P) = true)
include h

/-- **`ReaddOk` on a good pair's memory** (RV4 M2): the `readd` check, the mini-bus (`mbRead_seeded6` on
`TGoodE`'s balances), the stream cells (the seeds), the non-`readd` rows. -/
theorem readdOk6 (hA : AsmOk6 (tiOfL lay)) (pw : ℕ → FK) (q : Stack)
    (hg : TGoodE (tiOfL lay) L6 (tiOfL_τ lay) pw (toPair q)) :
    ReaddOk (tiOfL lay).Q (memTi (tiOfL lay) L6 pw (toPair q)) := by
  have hS := staticOk6_ok h
  have hok : (tiOfL lay).Ok := ⟨hS.lay, hS.one⟩
  refine readdOk_of_chk6 (tiOfL lay) L6 pw (toPair q).1 (toPair q).2 (mbPar6 lay) _ _ (tiOfL_mbT lay) hA.readd
    ?_ ?_ (nonReadd_of_tgoodE (tiOfL lay) L6 (tiOfL_τ lay) pw (toPair q) hS.node.grd.wf hS.node.grd.twinsOk
      hS.node.grd.noE3 hok hg)
  · intro k hk x hx
    exact mbRead_seeded6 (mbPar6 lay) _ _ L6 (tiOfL_τ lay) (toPair q).1 (toPair q).2 (tyBaseOf lay P).lay hg.2 hk hx
  · intro i hi x' hx'
    have hs : seedBlocks6[i] < 2 ^ 14 := mbStatic6.seedLt _ (List.getElem_mem hi)
    have hj : 2 ^ mbBlk6 * seedBlocks6[i] + x' < 2 ^ 18 := by simp only [mbBlk6] at hx' ⊢; omega
    have e1 : (mbPar6 lay).sb + 2 ^ mbBlk6 * seedBlocks6[i] + 1 * x' = sbC + (2 ^ mbBlk6 * seedBlocks6[i] + x') := by
      show sbC + _ + _ = _; omega
    refine ⟨by rw [e1]; have := hA.streamIn; omega, ?_⟩
    rw [e1]
    refine (stream_cell6 h pw q hj).trans ?_
    rw [comCell_main6 q (by simp only [QD.streamIdx, QD.recSlot, mbBlk6] at hj ⊢; omega)]
    simp only [stW, QD.streamIdx, Nat.add_right_comm]

/-- **`NodeFacts6` on the deployed circuit**, except the decision (`hdec`, NODE5a): from the static guard
(`staticOk6`), this WP's run-time facts (`AsmOk6`), node mode and `rest6`. The readers read the stack. -/
theorem nodeFacts6_deployed (hA : AsmOk6 (tiOfL lay)) (Φ : Phases) (x : Hdr) (q : Stack) (hb : x.b = 1)
    (_ht : TreeOk q x.h) (hr : rest6 (tyBaseOf lay P) h x q) (hdec : DecAt Φ (tyBaseOf lay P) x q) :
    NodeFacts6 Φ trOfS σOfS σlOfS x q := by
  have hS := staticOk6_ok h
  have hok : (tiOfL lay).Ok := ⟨hS.lay, hS.one⟩
  have hg : TGoodE (tiOfL lay) L6 (tiOfL_τ lay) (pwOf (tiOfL lay) (hdrBytes x)) (toPair q) := hr.2.1
  have hrow : ∀ blk ∈ (tiOfL lay).lay.aux, ∀ r ∈ blk.rows,
      ARowHolds (tiOfL lay).lay ((tiOfL lay).zOf L6 (pwOf (tiOfL lay) (hdrBytes x)) (toPair q).1 (toPair q).2) 0 r :=
    fun _ hblk ↦ blkRows_of_tgoodE (tiOfL lay) L6 (tiOfL_τ lay) _ (toPair q) hok hS.node.grd.noE3 hg hblk
  have hrd := readdOk6 lay P h hA _ q hg
  have hfl := flag_cell hS.node.pub L6 x (toPair q) hb
  obtain ⟨htr, hσ, hσl⟩ := readers6 h (pwOf (tiOfL lay) (hdrBytes x)) q
  have hσl' := hσl.trans (sigLeaf_of_tgoodE (tiOfL lay) L6 (tiOfL_τ lay) _ (toPair q) rfl hS.node.grd.wf
    hS.node.grd.twinsOk hS.node.grd.noE3 hok hrd hg hfl).symm
  exact nodeFacts6_of_cells Φ trOfS σOfS σlOfS x q hb (tiOfL lay) L6 (tiOfL_τ lay) (toPair q)
    (max ((ctxOf (tiOfL lay).Q).cells .K) (sbC + 2 ^ 18)) (SP.spOf q) (SP.yOf q) (SP.mOf q) (SP.xOf q)
    rfl hS.node.grd.wf hS.node.grd.twinsOk hS.node.grd.noE3 hok hrd hg (ginj6 hA) (le_max_left _ _)
    (le_max_right _ _) pow_inj1024 hS.node.pow hS.node.cst hS.node.pub (ksAlias6 h _ q)
    (posBits6_of hS.node.bits hrow) (sigBits6P hS.node.bits hrow) (sigBitsC6P hS.node.bits hrow)
    (outRel6 hr.1) (spongeLink6 hr.1) (hM6 h _ q) hdec (key_cells hS.node.pub L6 x (toPair q))
    (cp_cells hS.node.pub L6 x (toPair q)) htr hσ hσl'

/-- **`nodeFacts6_deployed` with `AsmOk6` from the guard** (V1c3: the guard's field `asm`). -/
theorem nodeFacts6_static (Φ : Phases) (x : Hdr) (q : Stack) (hb : x.b = 1) (ht : TreeOk q x.h)
    (hr : rest6 (tyBaseOf lay P) h x q) (hdec : DecAt Φ (tyBaseOf lay P) x q) :
    NodeFacts6 Φ trOfS σOfS σlOfS x q :=
  nodeFacts6_deployed lay P h (staticOk6_ok h).asm Φ x q hb ht hr hdec

/-- **`node6V` on the deployed circuit** with the stack readers, given the decision in node mode (NODE5a). -/
theorem node6V_deployed (hA : AsmOk6 (tiOfL lay)) (Φ : Phases)
    (hdec : ∀ x q, x.b = 1 → TreeOk q x.h → rest6 (tyBaseOf lay P) h x q → DecAt Φ (tyBaseOf lay P) x q) :
    Stmt.node6V (VSasm Φ) (rest6 (tyBaseOf lay P) h) (childOf6 trOfS σOfS) σlOfS :=
  node6V_Q Φ _ trOfS σOfS σlOfS fun x q hb ht hr ↦
    nodeFacts6_deployed lay P h hA Φ x q hb ht hr (hdec x q hb ht hr)

end Deployed

end Lvm6.Node.Asm
