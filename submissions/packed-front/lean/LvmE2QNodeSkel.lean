-- New for lvm2 E2-FT (E2F-C): `NodeSound` at S2GF from the circuit's parts (roll 11's `nodeSoundTG` at `P20F`): the
-- chain from the Keccak half, the left child `childSP P20F` accepted by `VSFX N` from Q_link (`qlink_sound` at
-- `P20F`), Q_sig (`qsig_sound_in`, `KS` at S2GF's continuation rows) and Q_arith (`harith`: `decideFFX`).
import LvmE2QNodeLeft
import LvmE2QNodeFacts
import LvmE2QNodeX
import LvmE2VPub

/-!
# `NodeSound` at S2GF from the parts

**`nodeSoundF`**: for a typed instance `Ti` whose program is the S2GF node program `qprogP P20F` with Q_arith `qa`,
and any good relation `G` whose pairs carry S2GF's Keccak half (`GoodKP P20F`), `NodeSound (VSFX N) vk G (childSP P20F)`
follows from, on `G`'s pairs of accepted node statements: the rows hold on the pair's memory (`hholds`), the input map
(`hmap`: stream, `KS` cells, `PUB`, the digest row `B − 1` of S2GF's `B = 4,295`), QLT's constants (`hqlt`), the
position bits (`hpos`), Q_sig's `BITS` (`hbits`) and Q_arith's soundness (`harith`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.SigBits LeanVM.Protocol

/-- The memory of a pair at S2GF (S2GF's public values `pubXF`). -/
noncomputable abbrev memF (Ti : TInst) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Mem :=
  memTX Ti Lvm.VEq.pubXF x qm qr

/-- **`NodeSound` at S2GF from the parts.** -/
theorem nodeSoundF (vk : RecursionFast.Digest) (N : TypedV.TNat) (Ti : TInst) (qa : BM Unit) (G : GoodRel)
    (hQ : Ti.Q = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa))
    (hinj : GInj (max (Ti.Q.cells .K) (Ti.Q.cells .E)))
    (hGK : ∀ c x qm qr, okS vk c x = true → G x qm qr → GoodKP P20F x (qm, qr))
    (hholds : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      Ti.Q.Holds (memF Ti x qm qr) ∧ Ti.Q.Asserts (memF Ti x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF Ti x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ y < (qltData P20F (lay cfgF20)).length,
        (memF Ti x qm qr).k ((lay cfgF20).qt + y) = (qltData P20F (lay cfgF20)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ k < (opens P20F).length, ∀ j < ((opens P20F).getD k default).L.t,
        ∀ z < ((opens P20F).getD k default).L.height,
        (memF Ti x qm qr).k (bitBase P20F (lay cfgF20) k + ((opens P20F).getD k default).L.height * j + z) =
          if ansBit P20F (wsC qr) (((opens P20F).getD k default).pe + j / 8)
            (j % 8 * ((opens P20F).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      SigBits (sigIn cfgF20) (qsig (sigIn cfgF20) (p1P (lay cfgF20) (nK cfgF20) 0 P20F)).1 (memF Ti x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF Ti x qm qr) vk x qm qr →
      LaneLink P20F (wsC qr) → LinkOk P20F (decode P20F (wsC qr)) →
      Ok (ctxOf Ti.Q) (memF Ti x qm qr) qa (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F) →
      E2V.decideFFX P20F N vk (hdrOf x).cL (traceBytesB (decode P20F (wsC qr))) = true) :
    NodeSound (E2V.VSFX N) vk G (childSP P20F) := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ chain_of_goodKP hok (hGK c x qm qr hok hG))
    fun c x qm qr hok hb hG ↦ ?_
  have hK := hGK c x qm qr hok hG
  obtain ⟨hH, hA⟩ := hholds c x qm qr hok hb hG
  have hinj' := hinj
  rw [hQ] at hH hA hinj'
  have P := parts_of_holdsP hH hA
  have mp := hmap c x qm qr hok hb hG
  have hwsl : 2 ^ (lay cfgF20).m ≤ (wsC qr).length := by
    rw [wsC, wsOf, List.length_map, List.length_range]; decide
  have hqin : QIn P20F (lay cfgF20) (wsC qr) (memF Ti x qm qr) :=
    ⟨mp.flag, mp.stream, hqlt c x qm qr hok hb hG, hpos c x qm qr hok hb hG⟩
  have hN : (ctxOf (toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa))).cells .K ≤
      max ((toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa)).cells .K)
        ((toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa)).cells .E) := by
    rw [NS.ctxOf_cells]; exact le_max_left _ _
  have hNs : (lay cfgF20).sb + 2 ^ (lay cfgF20).m ≤
      max ((toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa)).cells .K)
        ((toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa)).cells .E) :=
    le_trans (by decide : (lay cfgF20).sb + 2 ^ (lay cfgF20).m ≤ nK cfgF20)
      (le_trans (nK_le_cells _ _ _) (le_max_left _ _))
  obtain ⟨hLL, hpad⟩ := qlink_sound streamOk_P20F hQF20 hqin hwsl hinj' hN hNs P.1.1 P.1.2
  have hlink := linkOk_of_laneLink streamOk_P20F hLL
  have hks := sigKSin_of_goodKP P20F ksSplit_P20F (by rw [spongeBlocks_P20F.1]; norm_num) hK
    mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨hsig, hchild⟩ := qsig_sound_in (by rw [show (sigIn cfgF20).ln = 20 from rfl]; omega) P.2.1 mp.flag hks
    (hbits c x qm qr hok hb hG) fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
  have hmd := (digAt_of_cells mp.md).trans
    (traceDigest_of_goodKP P20F ksSplit_P20F streamOk_P20F spongeBlocks_nBlk_P20F
      (by rw [spongeBlocks_P20F.1]; norm_num) hK hLL hpad)
  have har := harith c x qm qr hok hb hG mp hLL hlink (by rw [hQ]; exact P.2.2)
  exact accV_childSP_of N qr hlink har hsig hchild rfl mp.vk mp.cL mp.sl hmd mp.sg mp.hd (okS_sig hok hb)

end Lvm.E2Q
