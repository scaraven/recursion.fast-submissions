-- WP-16b (CERT). New for lvm: the open obligations `Lvm.T.OpenT tabs` (`LvmSubmissionS.OpenS`) of the
-- submission, plugged with WP-14a's middle phases `midS` and `refines_VSL`, O6 (`LvmCertSMid3`),
-- WP-14c's `childS` and `NodeSound`, WP-14d's `ext_eq_S` with WP-14a's `midFollows_midS`.
-- AC-N (A23): `midS` with phase 3b (= AC-S's `midSA`), O6 from AC-S's `midSpec_midSA`, `Good :=
-- GoodA` (`GoodS ∧ AccOk acc_in`), `NodeSound` from `LvmAccNode.nodeSound_acc` (Q_arith's `harith`
-- in A23's form: `decideCore ∧ accOutOf = acc_in`).
-- lvm2 S2 (WP S2-CERT): generic in the node program's tables `tabs` (the node program's facts are
-- `MidHyp`, `AccMidHyp`, `FixStatic` and `NodeHyp`); the instance at `tabs` with WP-16a's
-- program is `LvmCertSFinal20`.
-- lvm2 roll 7 (CR-X): `openS_of` at SH2-Z's `midS₂` (CR-S0's p4 text), `FinalHyp` gains the small
-- layout's fit `colsRegB`, `refines := refines_VSL`. lvm2 roll 8 (B1, wave L): `openS_of` and its certificates
-- are gone (the typed schedule); `FinalHyp` and the node facts stay.
import LvmAccSpecCert
import LvmCertSExq
import LvmVEqRefines
import LvmVEqFolMid
import LvmAccNode
import LvmShapeBus

/-!
# The open obligations of roll 7's bus certificate (what is left)

**`FinalHyp tabs`**: the facts left about the node program's tables `tabs` of the bus `V_S` (`mid : MidHyp tabs`,
`acc : AccMidHyp tabs`, `node`: `NodeSound` for `GoodN ∧ AccOkN` at `VSt tabs`, `reg : ∀ pub, colsRegB (tabs pub)`),
and the node facts `NodeBase`, `NodeHyp`, `node_of` (`nodeSound_acc` for a concrete node program and `FixStatic`).

lvm2 roll 8 (B1, wave L): roll 7's `openS_of`, `certificateR_final` and `certificateR_node` (the bus `OpenT`
plugged with `midS₂`, `refines_VSL` and `midFollows_midS₂`) are gone with the typed schedule `S2GB1`, whose `P_S`
the bus middle phases no longer follow. The typed certificate is `LvmCertT20.certificateT20`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.M3 Lvm.VEq Lvm.Acc

/-! ## O10: `nodeSound_layout`'s hypotheses -/

section Node

open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol

variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
  (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrsX : List UInt8 → List InArr) (aux : List Tab)
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ)
  (bpl : ℕ → ℕ → Bool × ℕ) (rest : List Tab) (pb : ℕ) (tabs : Pub → List Tab)

/-- **WP-14c's `nodeSound_layout` hypotheses but `hinb`**, for the node program `Qn lay I qa nK nE`
with the placement `pl`, groups, input arrays `arrsX` and aux tables `aux` (`= Q_sig's BITS ++ rest`),
at the tables `TS tabs` of `VSt tabs`: static facts of the program and its placement (decidable),
QL's Q_link facts (`hqlt`, `hpos`), and Q_arith (`harith`, A23's form: the child's `decideCore` and
its folded accumulator equal to the statement's `acc_in`). -/
structure NodeBase : Prop where
  hT : ∀ x, TS tabs x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux
  hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x)
  hlay : ∀ x, LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
  hτT : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ
  hS : StreamOk P20
  hQ : QOk P20 lay
  hws : 2 ^ lay.m ≤ 17 * 2 ^ 14
  hfg : lay.fg = I.flag
  hln : I.ln = 20
  hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS tabs) hτT x qm qr →
    ∀ y < (qltData P20 lay).length,
      (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.qt + y) = (qltData P20 lay).getD y 0
  hpos : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS tabs) hτT x qm qr →
    ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
      ∀ z < ((opens P20).getD k default).L.height,
      (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k
          (bitBase P20 lay k + ((opens P20).getD k default).L.height * j + z) =
        if ansBit P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0
  hNs : lay.sb + 2 ^ lay.m ≤ max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E)
  haux : aux = (sigSpecs I (qsig I (p1 lay nK nE)).1 bpl).map BitsTab.BSpec.tab ++ rest
  hR : SigRegLt ((Qn lay I qa nK nE).cells .K) I
  hP : (p2 lay I nK nE).k ≤ (Qn lay I qa nK nE).cells .K
  hSt : ∀ x, Bundle (arrsX x) 17 14 lay.sb true fun l => l * 2 ^ 14
  hhd : I.hd = lay.sb + 11
  hSg : ∀ x, Bundle (arrsX x) 1 10 I.sg true fun _ => 17 * 2 ^ 14
  hX : ∀ x, Bundle (arrsX x) 17 9 I.xs false fun l => CMain.ksXW20 l 0
  hY : ∀ x, Bundle (arrsX x) 4 9 I.ys false fun l => CMain.ksYW20 l (ksSplit P20)
  hyc : I.yc = I.ys + 4 * 430
  hyls : I.yls = I.ys + 4 * 447
  hyns : I.yns = I.ys + 4 * 448
  hMd : ∀ x, Bundle (arrsX x) 4 0 I.md false
    fun l => CMain.ksYW20 l (spongeBlocks P20 - 1)
  hPub : ∀ x, PubAt (arrsX x) x pb
  hfl : I.flag = pb
  hvkI : I.vk = pb + 1
  hcLI : I.cL = pb + 5
  hslI : I.sl = pb + 18
  harith : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS tabs) hτT x qm qr →
    InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr →
    LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
    LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
    Ok (ctxOf (Qn lay I qa nK nE)) (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) qa
      (p2 lay I nK nE) →
    decideCore P20 (M3.real P20 tabs) vk (hdrOf x).cL
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true ∧
      accOutOf P20 (M3.real P20 tabs) vk (hdrOf x).cL
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = (pubX x).accIn

/-- **WP-14c's `nodeSound_layout` hypotheses**: `NodeBase` and QL's `hinb` (every computed-address
read finds its cell; INB's `hinb20` for WP-16a's P20 program, `nodeHyp20`). -/
structure NodeHyp : Prop extends NodeBase lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb tabs where
  hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS tabs) hτT x qm qr →
    ((Qn lay I qa nK nE).interp (inKOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
      (stackOf lay26 qm qr)) (inEOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
      (stackOf lay26 qm qr))).inb = true

variable {lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb tabs}

/-- **O10 from `NodeHyp`** (`nodeSound_acc`) and `FixStatic` (`Φ` is one polynomial), for any proof
of the tables' heights. -/
theorem node_of (N : NodeHyp lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb tabs)
    (hΦ : FixStatic P20 tabs) (hτ : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ)
    (vk : RecursionFast.Digest) :
    NodeSound (Lvm.T.VSt tabs) vk (fun x qm qr ↦ GoodN (TS tabs) hτ x qm qr ∧ AccOkN tabs x) childS :=
  nodeSound_acc (M3.real P20 tabs) vk (fixVals_real P20 tabs hΦ) N.hT N.hst N.hlay
    (N.hinb vk) N.hS N.hQ N.hws N.hfg N.hln (N.hqlt vk) (N.hpos vk) N.hNs bpl rest N.haux N.hR N.hP
    N.hSt N.hhd N.hSg N.hX N.hY N.hyc N.hyls N.hyns N.hMd N.hPub N.hfl N.hvkI N.hcLI N.hslI (N.harith vk)

end Node


/-- `midS` (WP-14a's middle phases with A23's phase 3b) is AC-S's `midSA`. -/
theorem midS_eq_midSA (tabs : Pub → List Tab) : midS tabs = midSA tabs := rfl

/-- **The facts left for the certificate** about the node program's tables `tabs`. -/
structure FinalHyp (tabs : Pub → List Tab) : Prop where
  /-- O6: the tables fit `P20` and pass WP-9b's checks. -/
  mid : MidHyp tabs
  /-- O6, A23: phase 3b's instance facts (AC-S's `AccInst` at every statement). -/
  acc : AccMidHyp tabs
  /-- O10: the arithmetisation's soundness for WP-14c's good pair with `AccOk acc_in`. -/
  node : ∀ vk, NodeSound (Lvm.T.VSt tabs) vk
    (fun x qm qr ↦ Lvm.NS.GoodN (TS tabs) mid.hτ x qm qr ∧ AccOkN tabs x) Lvm.NS.childS
  /-- Roll 7: the small layout's fit (every committed `C_main` column a regular block, `RegP`). -/
  reg : ∀ pub, colsRegB (tabs pub) = true


end Lvm.ASM
