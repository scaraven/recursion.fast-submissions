-- New for lvm6 (WP NODE5a). `NodeFacts6`'s decision `hdec` on the deployed circuit: `dec_fin` at CC's real inputs
-- from the node's runs (`node6E_har`, `famQ6_parts`, `ccPre`, `mbPre`), the guard, and named residual facts.
import Lvm6NodeFinC
import Lvm6NodeFinH
import Lvm6NodeFinZ
import Lvm6NodeTailHP
import Lvm6NodeV

/-!
# `hdec` on the deployed circuit (WP NODE5a)

**`dec_of_node_deployed`**: on a memory where the deployed circuit's rows hold (`OkAt … (famQ6 B.Ti.lay)`), with
`NodeFacts6`'s other hypotheses (`childLink6`'s inputs, the PoW rows), the guard (`staticOk6 B`), the node's header
`x` (flag on, `pw` its public words, `AccOkE` of its accumulator), V1's decision `F6` at the instance map
`inst6 B hB` holds. The proof composes `famQ6_link` (`hw`, `LinkOk6`, the child header's magic), `powLanes6_of_rows`
(`hpow`), `node6E_har` at `famQ6_node` (the phase runs; `hY` by `tyIn_hdr`, `promise_pub`, `typedRun_hdr`),
`famQ6_parts` + `ccPre`/`mbPre`'s HARs (CC at `inpReal`), and `dec_fin` with `claimsAt_real`, `vals_real`.

Claim 0 (`Split.claim0At`) and the root lanes (`Hdr.rootLanes_hdr`) are proved. Left as hypotheses (named, each a
fact about the deployed circuit or its instance):
* `OutShape (n6 B.Ti.lay ⟨nK, 0⟩).1`: the lengths of `node6E`'s output cells;
* `B.Ti.mbT = mbTD B.Ti.lay`: the instance's mini-bus tables are the circuit's.
-/

set_option autoImplicit false

namespace Lvm6.Node.Fin

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node Lvm6.Node.Split Lvm6.Node.Dep
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V LeanVM.Parameters Lvm.QSig Lvm.QLink LeanVM.Protocol

local notation "πW" ws => reassemble6 P6 (decode6 P6 ws)

/-- `mbPre` is `mbPreG` at the walk's cells. -/
theorem mbPre_eq (tabs : List Lvm.M3.Tab) (o : NodeOutE) (gate : Cell) :
    mbPre tabs o gate = MbC.mbPreG tabs o.ty.mb.alphas o.ty.mb.beta o.ty.mb.point o.ty.mb.values gate := rfl

/-- The bus result of the walk's cells. -/
theorem busResG_eq (tabs : List Lvm.M3.Tab) (M : Mem) (mb : QD.MbOutC) :
    Mb.busResG tabs (QD.busOf M mb) =
      Mb.busFinalG tabs (mb.alphas.map (ev2 M)) (ev2 M mb.beta) (mb.point.map (ev2 M)) (mb.values.map (ev2 M)) := by
  simp only [Mb.busResG, QD.busOf]

/-- **`hdec` from the node's runs on the deployed circuit.** -/
theorem dec_of_node_deployed {B : V.TyBase6} (hB : V.staticOk6 B = true) {L : Lvm.M3.Lay} (hL : L = Ty.L6)
    {x : Hdr} {p : Column L.nuMain × Column L.nuRec} {ws : List Word} {N : ℕ} {vk : RecursionFast.Digest}
    -- the rows of the deployed circuit (`segs_of_tgoodE`)
    (hOk : OkAt (ctxOf B.Ti.Q) (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p) (famQ6 B.Ti.lay) ⟨nK, 0⟩)
    -- `NodeFacts6`'s `childLink6` inputs and PoW rows
    (hin : QIn6 P6 opensP18 lay6 ws (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p)) (hwl : ws.length = 2 ^ 19)
    (hinj : GInj N) (hN : (ctxOf B.Ti.Q).cells .K ≤ N) (hNs : sbC + 2 ^ 19 ≤ N)
    (hinj' : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    (hfl : (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p).k sigI.flag = 1)
    (hks : SigKSin sigI (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p).k)
    (hbits : SigBits sigI (qsig6 sigI sigIl sbC (pS B.Ti.lay ⟨nK, 0⟩)).1.1
      (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p).k)
    (hfl' : (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p).k sigIl.flag = 1)
    (hksL : SigKSinC sigIl (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p).k)
    (hbitsL : SigBitsC sigIl (qsig6 sigI sigIl sbC (pS B.Ti.lay ⟨nK, 0⟩)).1.2.pa
      (memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p).k)
    (hrows : PowRowsHold B.Ti.lay (B.Ti.zOf L (QD.pwOf B.Ti (hdrBytes x)) p.1 p.2))
    -- the node's own accumulator (the A23 promise)
    (hx : x.accIn.1.length = Ty.phiVarsE) (hacc : Ty.AccOkE B.Ti (V.accFix x))
    -- residual facts
    (hshape : OutShape (n6 B.Ti.lay ⟨nK, 0⟩).1)
    (hmbT : B.Ti.mbT = mbTD B.Ti.lay) :
    F6 (phases6 (fun sh y ↦ Ty.typedPhase6 sh (V.inst6 B hB y)) ringPhase6 (fun _ cl ↦ Whir.whirP18 cl)) P18 vk
      (πW ws) (accOf P18 (πW ws) (decode6 P6 ws)) = true := by
  set M := memTi B.Ti L (QD.pwOf B.Ti (hdrBytes x)) p with hMdef
  have hS := V.staticOk6_ok hB
  have hok : B.Ti.Ok := ⟨hS.lay, hS.one⟩
  -- `childLink6`: the stream's length, the link, the child header's magic
  have hl := famQ6_link hOk hin hwl.ge hinj hN hNs hinj' hfl hks hbits hfl' hksL hbitsL
  have hw : hashedLen6 P6 ≤ 8 * ws.length := hl.2.1.size
  have hM : ∀ j < ws.length, M.k j = laneK ws j := fun j hj ↦ by
    have e := hin.stream j (by rw [hwl] at hj; exact hj)
    rwa [show lay6.sb + j = j by simp [lay6, sbC]] at e
  have hpow : PowLanes6 P6 ws := powLanes6_of_rows hrows (fun j hj ↦ hin.stream j hj) hw hwl.le
  have hg : gateC.val M = 1 := by
    show FE.ofK (M.k (pbC + 1)) = 1
    rw [show M.k (pbC + 1) = 1 from hfl]
    rfl
  -- the node's families: `node6E`'s runs at `n6`'s output
  have hN6 := famQ6_node hOk
  have eo : node6E B.Ti (pubCOf B.Ti.lay) ainC yInC ownC ownYC gateC = n6 B.Ti.lay := by
    rw [n6, node6E_congr (Ti := B.Ti) (Ti' := tiOf B.Ti.lay) rfl]
  rw [eo] at hN6
  have hain : ainC.length = Ty.phiVarsE := by simp [ainC]; rfl
  have hown : ownC.length = Ty.phiVarsE := by simp [ownC]; rfl
  have hhar := node6E_har B.Ti hok hS.tyLay L (pubCOf B.Ti.lay) ainC yInC ownC ownYC hain hown gateC hg
    (c := ctxOf B.Ti.Q)
  rw [eo] at hhar
  obtain ⟨hT, hSp, hK, -, hTy⟩ := hhar ⟨nK, 0⟩ hN6.1 hN6.2
  -- the typed run at the child's header (`hY`)
  have hz : M.k zC = 0 := by
    show (B.Ti.lay.cst? zC).getD _ = 0
    simp [Lvm.Typed.Lay.cst?, hS.node.cst]
  have hTyIn := Hdr.tyIn_hdr B.Ti hl.1.1 hl.2.2.1.1 hin.stream hz
  have hprom := Hdr.promise_pub (hS.node.pub : PubCells B.Ti) L x p hx hacc
  have hY := Hdr.typedRun_hdr hTyIn (hTy hprom)
  -- CC on the real inputs: `ccPre`, `mbPre`, then `ccG18I (inpReal …)`
  have hCC := (famQ6_parts hOk).2.2.2.2
  unfold ccG18o at hCC
  obtain ⟨hP1, hP23⟩ := Dep.ok_bind' hCC
  obtain ⟨hP2, hP3⟩ := Dep.ok_bind' hP23
  obtain ⟨hz2, hone2, htv⟩ := hs_ccPre (c := ctxOf B.Ti.Q) (M := M) _ _ hP1.1
  rw [mbPre_eq] at hP2 hP3
  obtain ⟨hmo, hmv⟩ := MbC.hs_mbPreG (c := ctxOf B.Ti.Q) (M := M) (mbTD B.Ti.lay) _ _ _ _ gateC _ hP2.1
  rw [← busResG_eq] at hmo hmv
  refine dec_fin hw hM hpow (lanesOf_inpReal _ B.Ti.lay _ _ _ _) hL hT hSp hK hY hP3 hg
    (fun ot os hot hos ↦ hsh_real hshape hot hos) (fun oy hoy ↦ by subst hoy; exact hty_real B.Ti L _)
    (fun c0 hc0' ot os lk oy hot hos hlk hoy ↦ ?_) (fun c0 hc0' ot os lk oy hot hos hlk hoy rp ↦ ?_)
  · subst hoy
    exact vals_real hshape hmbT hz2 htv hmv (Split.claim0At hw hM hpow c0 hc0').v (Hdr.rootLanes_hdr hl.1.1 hin.stream) hot hos hlk
  · subst hoy
    have hsh := hsh_real hshape hot hos
    exact claimsAt_real hok hS.tyLay hS.node.regCom hS.node.regKs hmbT (by subst hL; rfl) hz2 hone2 hmo hshape.ry
      (Split.claim0At hw hM hpow c0 hc0').w hot hos hlk hsh.1 hsh.2 rp

end Lvm6.Node.Fin
