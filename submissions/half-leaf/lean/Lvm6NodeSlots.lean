-- New for lvm6 (WP NODE3, item 4). The deployed circuit's families from its segments: `famQ6`'s rows and
-- assertions at a pointer split into `node6E`'s (at any typed instance on the same layout), `Q_link`'s, `Q_sig`'s,
-- the `σ_leaf` copy's and CC's, at explicit pointers; CA's `childLink6` then gives `hQ` and the `σ_leaf` signature.
import Lvm6NodeDeploy
import Lvm6NodeWire
import Lvm6QAccept
import Lvm6NodeChildOk
import LvmE2QPow

/-!
# The SLOT conclusions on the deployed circuit (WP NODE3)

* **`ty6_congr`, `node6E_congr`**: the typed gadgets read their instance only through its layout (`pubBase`,
  `sflatBase`; `qacc6` ignores the program), so `node6E` on the exporter's `tiOf lay` is `node6E` on any instance
  with layout `lay`, in particular the one whose program is `progQ6 lay` itself.
* **`famQ6_parts`**: `Ok` of `famQ6 lay` at `p` gives `Ok` of each family at its pointer (`pL`, `pS`, `pY`, `pC`).
* **`powLanes6_of_rows`**: `PowLanes6 P6 ws` (NODE2's `pow` input) from the PoW blocks' rows (`PowRowsHold`) and
  the stream cells; the grind bound `g ≤ 64` of every plan entry is static (`powG64B_P17`).
* **`famQ6_link`**: CA's `childLink6` at the deployed cells (`lay6`, `sigI`, `sigIl`; the static facts at `P17`
  discharged: `streamOkP17`, `opensOKP17`, `qOkP17`, `cdConsts_P17`, `sigI.cL = lay6.cp`): `hQ` of
  `childOk_of_node` and the `σ_leaf` signature, from `childLink6`'s input facts only.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink
open Lvm6.Ty (TInst6)

/-! ## The typed gadgets read the layout only -/

theorem qacc6_congr (Q Q' : Program) : qacc6 Q = qacc6 Q' := rfl

theorem ty6_congr {Ti Ti' : TInst6} (h : Ti.lay = Ti'.lay) : ty6 Ti = ty6 Ti' := by
  funext pubC ain yIn own ownY a gate
  simp only [ty6, wire6, relay6, pubBase, sflatBase, onesOf, h, qacc6_congr Ti.Q Ti'.Q]

theorem node6E_congr {Ti Ti' : TInst6} (h : Ti.lay = Ti'.lay) : node6E Ti = node6E Ti' := by
  funext pubC ain yIn own ownY gate
  simp only [node6E, ty6_congr h]

/-! ## The families at their pointers -/

theorem ok_bind' {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : SegsHold c M p ((m >>= f) p).2 ∧ SegsAssert M p ((m >>= f) p).2) :
    (SegsHold c M p (m p).2 ∧ SegsAssert M p (m p).2) ∧
      (SegsHold c M (p.adv (m p).2) (f (m p).1 (p.adv (m p).2)).2 ∧
        SegsAssert M (p.adv (m p).2) (f (m p).1 (p.adv (m p).2)).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1
  rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

/-- `node6E` at the deployed cells. -/
def n6 (lay : Lay) : BM NodeOutE := node6E (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC

/-- `Q_link`'s pointer. -/
def pL (lay : Lay) (p : Ptr) : Ptr := p.adv (n6 lay p).2

/-- `Q_sig`'s pointer. -/
def pS (lay : Lay) (p : Ptr) : Ptr := (pL lay p).adv (qlink6 P6 opensP17 lay6 (pL lay p)).2

/-- The `σ_leaf` copy's pointer. -/
def pY (lay : Lay) (p : Ptr) : Ptr := (pS lay p).adv ((qsig6 sigI sigIl sbC >>= fun _ ↦ pure ()) (pS lay p)).2

/-- CC's pointer. -/
def pC (lay : Lay) (p : Ptr) : Ptr := (pL lay p).adv (famR (pL lay p)).2

/-- A gadget's rows and assertions hold at `q`. -/
abbrev OkAt (c : Ctx) (M : Mem) {α : Type} (m : BM α) (q : Ptr) : Prop :=
  SegsHold c M q (m q).2 ∧ SegsAssert M q (m q).2

/-- **The families of the deployed circuit at their pointers.** -/
theorem famQ6_parts {c : Ctx} {M : Mem} {lay : Lay} {p : Ptr} (h : OkAt c M (famQ6 lay) p) :
    OkAt c M (n6 lay) p ∧ OkAt c M (qlink6 P6 opensP17 lay6) (pL lay p) ∧
      OkAt c M (qsig6 sigI sigIl sbC) (pS lay p) ∧ OkAt c M (sigLeafCopy6 dstC (sgC + 597) (pbC + 1)) (pY lay p) ∧
      OkAt c M (ccGo (n6 lay p).1 lay (mbTD lay) ccbC gateC) (pC lay p) := by
  obtain ⟨h1, h2⟩ := ok_bind' (m := n6 lay) (f := fun o ↦ famR >>= fun _ ↦ ccGo o lay (mbTD lay) ccbC gateC) h
  obtain ⟨h3, h4⟩ := ok_bind' (m := famR) (f := fun _ ↦ ccGo (n6 lay p).1 lay (mbTD lay) ccbC gateC) h2
  obtain ⟨h5, h6⟩ := ok_bind' (m := qlink6 P6 opensP17 lay6) (f := fun _ ↦
    (qsig6 sigI sigIl sbC >>= fun _ ↦ pure ()) >>= fun _ ↦ sigLeafCopy6 dstC (sgC + 597) (pbC + 1)) h3
  obtain ⟨h7, h8⟩ := ok_bind' (m := qsig6 sigI sigIl sbC >>= fun _ ↦ pure ())
    (f := fun _ ↦ sigLeafCopy6 dstC (sgC + 597) (pbC + 1)) h6
  obtain ⟨h9, -⟩ := ok_bind' (m := qsig6 sigI sigIl sbC) (f := fun _ ↦ (pure () : BM Unit)) h7
  exact ⟨h1, h5, h9, h8, h4⟩

/-- **`node6E` on a typed instance with the deployed layout** (for `node6E_har`). -/
theorem famQ6_node {c : Ctx} {M : Mem} {Ti : TInst6} {p : Ptr} (h : OkAt c M (famQ6 Ti.lay) p) :
    OkAt c M (node6E Ti (pubCOf Ti.lay) ainC yInC ownC ownYC gateC) p := by
  have e : node6E Ti = node6E (tiOf Ti.lay) := node6E_congr rfl
  rw [e]
  exact (famQ6_parts h).1

/-! ## `Q_link` and `Q_sig` -/

theorem sigI_cL : sigI.cL = lay6.cp := rfl

/-- **`hQ` and the `σ_leaf` signature** on the deployed circuit (CA's `childLink6`; the static facts at `P17`
discharged). The hypotheses are `childLink6`'s input facts: the stream, table and position-bit cells (`QIn6`),
the flags, the `KS` aliases and the signature bits at `Q_sig`'s pointer. -/
theorem famQ6_link {c : Ctx} {M : Mem} {lay : Lay} {p : Ptr} {ws : List Word}
    (h : OkAt c M (famQ6 lay) p) (hin : QIn6 P6 opensP17 lay6 ws M) (hws : 2 ^ 18 ≤ ws.length)
    {N : ℕ} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : sbC + 2 ^ 18 ≤ N)
    (hinj' : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    (hg : M.k sigI.flag = 1) (hks : SigKSin sigI M.k)
    (hbits : SigBits sigI (qsig6 sigI sigIl sbC (pS lay p)).1.1 M.k)
    (hgl : M.k sigIl.flag = 1) (hksL : SigKSinC sigIl M.k)
    (hbitsL : SigBitsC sigIl (qsig6 sigI sigIl sbC (pS lay p)).1.2.pa M.k) :
    QLinkConcl P6 (digAt M.k sigI.cL) ws ∧ LaneLink6 P6 (digAt M.k sigI.cL) ws ∧
      ChildHdr6 (digAt M.k sigI.vk) (digAt M.k sigI.cL) (decode6 P6 ws) ∧
      SigOk (digAt M.k sigI.vk) (digAt M.k sigI.md) (sigAt' M.k sigI.sg) = true ∧
      SigOk (digAt M.k sigIl.vk) (traceDigest []) (sigAtP M.k sigIl.sg) = true := by
  obtain ⟨-, hL, hS, -, -⟩ := famQ6_parts h
  have hc := cdConsts_P17
  exact childLink6 streamOkP17 hc.2.2.2.2.1 opensOKP17 (qOkP17 lay6 (by decide) (by decide) (by decide)) hin hws
    hinj hN hNs hL.1 hL.2 hc.2.2.1 (by rw [hc.2.2.2.1]; decide) (by rw [hc.2.2.2.1]; decide) (by decide)
    sigI_cL (by decide) hS hg hks hbits hinj' hgl hksL hbitsL

/-! ## The PoW rows (`PowLanes6`) -/

/-- **The PoW rows hold**: for every answer `(q, g)` of `powAns` the layout has a block `powBlk g bw q` whose rows
hold (the auxiliary rows of the exporter's `specOf`). -/
def PowRowsHold (lay : Lay) (z : ℕ → FK) : Prop :=
  ∀ a ∈ powAns, ∃ bw, ∀ r ∈ (powBlk a.2 bw a.1).rows, ARowHolds lay z 0 r

/-- Every grind of the plan is at most 64 bits (static). -/
def powG64B : Bool := P6.all fun e ↦ match e.k with
  | .fs _ g => decide (g ≤ 64)
  | _ => true

theorem powG64B_P17 : powG64B = true := ((Bool.and_eq_true _ _).mp Mb.nodeStaticB_true).2

theorem powG64 {i : ℕ} (hi : i < P6.length) {st g : ℕ} (hk : (P6.getD i default).k = .fs st g) :
    g ≤ 64 := by
  have hm : P6.getD i default ∈ P6 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have h := List.all_eq_true.mp powG64B_P17 _ hm
  rw [hk] at h
  exact of_decide_eq_true h

/-- **`pow` from the PoW rows**: the rows of every answer's block and the stream cells give `PowLanes6`. -/
theorem powLanes6_of_rows {lay : Lay} {z : ℕ → FK} {ws : List Word} (hrows : PowRowsHold lay z)
    (hstream : ∀ j < 2 ^ 18, (memOf lay z).k (sbC + j) = laneK ws j)
    (hw : hashedLen6 P6 ≤ 8 * ws.length) (hwl : ws.length ≤ 2 ^ 18) : PowLanes6 P6 ws := by
  intro i hi st g hk
  by_cases hg0 : g = 0
  · subst hg0
    exact (ws.getD _ 0).isLt
  have hmem : (sbC + Lvm6.Q.ansLane6 P6 i, g) ∈ powAns := by
    rw [powAns_eq]
    refine List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [hk]
    simp only [if_pos (Nat.one_le_iff_ne_zero.mpr hg0)]
  obtain ⟨bw, hb⟩ := hrows _ hmem
  have h1 := powRange_sem lay z 0 g (powG64 hi hk) (fun j ↦ .word (bw + j) 0)
    (.cell ⟨.K, sbC + Lvm6.Q.ansLane6 P6 i + 2, []⟩) (fun j ↦ ⟨bw + j, 0, rfl⟩) rfl hb
  have h2 : kToNat ((memOf lay z).k (sbC + (Lvm6.Q.ansLane6 P6 i + 2))) < 2 ^ (64 - g) := h1
  have hb4 : Lvm6.Q.ansLane6 P6 i + 4 ≤ ws.length := Lvm6.Q.ansLane6_bound streamOkP17 hw hi
  rw [hstream _ (by omega)] at h2
  exact h2

end Lvm6.Node.Dep
