-- New for lvm6 (WP NODE3). `node6V` on the deployed circuit: the typed relation of an instance whose program is
-- `progQ6` (the wiring bridge) gives the families' rows; CA's `childLink6` the link, header and signatures; the PoW
-- rows `pow`; CB-4's trace digest `sig`'s message. What is left is named in `NodeFacts6`.
import Lvm6NodeSlots

/-!
# `node6V` from the deployed circuit (WP NODE3)

**`node6V_Q`**: `Stmt.node6V (VSasm Φ) rest (childOf6 trOf σOf) σlOf` whenever, in node mode, the tree relation
and `rest` give `NodeFacts6`: a typed instance `Ti` whose program is the deployed `progQ6 Ti.lay`, a candidate pair
`p` with `TGoodE` (the typed relation), and on the memory read off its words:
* the guard's static facts (`wf`, `twinsOk`, `NoE3`, `Ti.Ok`) and the mini-bus obligation `ReaddOk`;
* `childLink6`'s input facts (`QIn6`: stream, `QLT` table, position bits; `GInj`; flags; `KS` aliases and
  signature bits), the PoW blocks' rows (`PowRowsHold`), the stream of `2^19` words;
* the node's sponge rows (`OutRel`, `SpongeLink`, `hM`) and the digest cells (`hmd`) for CB-4's trace digest;
* the decision `hdec` (`F6` on V1's transcript; `dec_of_runs` reduces it to the stream-lane split, the commitment
  phase and CC's ring and opening);
* the readers: the child's trace, `σ'`, `σ_leaf`, the key and the child's statement are the cells' values.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V LeanVM.Protocol
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink
open Lvm6.Ty (TInst6 TGoodE NoE3)
open LeanVM.Parameters

/-- **What the circuit's relation gives at a node** (`x`, `q`), for the phases `Φ` and the readers. -/
def NodeFacts6 (Φ : Phases) (trOf : Stack → Trace) (σOf σlOf : Stack → Sig) (x : Hdr) (q : Stack) : Prop :=
  ∃ (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) (ws : List Word) (N B : ℕ) (ks : ℕ → K) (Yl Mx X : ℕ → ℕ → K),
    -- the program, the guard's static facts, the relation
    Ti.Q = progQ6 Ti.lay ∧ Ti.Q.wf = true ∧ Ti.Q.twinsOk = true ∧ NoE3 Ti.Q Ti.lay ∧ Ti.Ok ∧
    ReaddOk Ti.Q (memTi Ti L pw p) ∧ TGoodE Ti L hτ pw p ∧
    -- `childLink6`'s inputs
    QIn6 P6 opensP18 lay6 ws (memTi Ti L pw p) ∧ ws.length = 2 ^ 19 ∧ GInj N ∧
    (ctxOf Ti.Q).cells .K ≤ N ∧ sbC + 2 ^ 19 ≤ N ∧
    (∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b) ∧
    (memTi Ti L pw p).k sigI.flag = 1 ∧ SigKSin sigI (memTi Ti L pw p).k ∧
    SigBits sigI (qsig6 sigI sigIl sbC (pS Ti.lay ⟨nK, 0⟩)).1.1 (memTi Ti L pw p).k ∧
    (memTi Ti L pw p).k sigIl.flag = 1 ∧ SigKSinC sigIl (memTi Ti L pw p).k ∧
    SigBitsC sigIl (qsig6 sigI sigIl sbC (pS Ti.lay ⟨nK, 0⟩)).1.2.pa (memTi Ti L pw p).k ∧
    -- the PoW rows
    PowRowsHold Ti.lay (Ti.zOf L pw p.1 p.2) ∧
    -- the node's sponge rows and digest cells (CB-4)
    B ≤ 7168 ∧ Lvm.KG.OutRel 13 25 ks Yl ∧
    Lvm.KG.SpongeLink 13 (rowsBK2 B 7567 8032) ks (fun i l ↦ Yl l i) (Lvm.KG.ksMsg 7168 Mx X) ∧
    B = Lvm.KSponge.nBlk (hashedLen6 P6) ∧
    (∀ i < 7168, ∀ l < 17, (Mx i l).toBitVec.toNat = lw ws (17 * i + l)) ∧
    (∀ l < 4, (memTi Ti L pw p).k (sigI.md + l) = FK.ofBF64 (Yl l (B - 1))) ∧
    -- the decision
    F6 Φ P18 (digAt (memTi Ti L pw p).k sigI.vk) (reassemble6 P6 (decode6 P6 ws))
      (accOf P18 (reassemble6 P6 (decode6 P6 ws)) (decode6 P6 ws)) = true ∧
    -- the readers
    digAt (memTi Ti L pw p).k sigI.vk = x.vk ∧ digAt (memTi Ti L pw p).k sigI.cL = x.c' ∧
    trOf q = decode6 P6 ws ∧ σOf q = sigAt' (memTi Ti L pw p).k sigI.sg ∧
    σlOf q = sigAtP (memTi Ti L pw p).k sigIl.sg

/-- **`node6V` on the deployed circuit.** -/
theorem node6V_Q (Φ : Phases) (rest : Hdr → Stack → Prop) (trOf : Stack → Trace) (σOf σlOf : Stack → Sig)
    (h : ∀ x q, x.b = 1 → TreeOk q x.h → rest x q → NodeFacts6 Φ trOf σOf σlOf x q) :
    Stmt.node6V (VSasm Φ) rest (childOf6 trOf σOf) σlOf := by
  refine node6V_of_child Φ rest trOf σOf σlOf fun x q hb ht hr ↦ ?_
  obtain ⟨Ti, L, hτ, pw, p, ws, N, B, ks, Yl, Mx, X, hQ, hwf, htw, hE3, hok, hrd, hg, hin, hwl, hinj, hN, hNs,
    hinj', hfl, hks, hbits, hfl', hksL, hbitsL, hrows, hB, hout, hlink, hBL, hM, hmd, hdec, hvk, hcL, htr, hσ,
    hσl⟩ := h x q hb ht hr
  have hQ' : Ti.Q = Lvm.VF.toProgramF nK 0 (famQ6 Ti.lay) := hQ
  have hOk : OkAt (ctxOf Ti.Q) (memTi Ti L pw p) (famQ6 Ti.lay) ⟨nK, 0⟩ :=
    segs_of_tgoodE (famQ6 Ti.lay) nK 0 Ti L hτ pw p hQ' hwf htw hE3 hok hrd hg
  have hl := famQ6_link hOk hin hwl.ge hinj hN hNs hinj' hfl hks hbits hfl' hksL hbitsL
  have hpow : PowLanes6 P6 ws := powLanes6_of_rows hrows (fun j hj ↦ hin.stream j hj) hl.2.1.size hwl.le
  have hco := childOk_of_node (Φ := Φ) (I := sigI) ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1⟩ hB hout hlink hBL hM
    hmd hpow hdec
  rw [hvk, hcL, ← htr, ← hσ] at hco
  refine ⟨hco, ?_⟩
  have hs := hl.2.2.2.2
  rw [hσl]
  rw [← hvk]
  exact hs

end Lvm6.Node.Dep
