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

/-- The memory of a pair at S2GT (S2GT's public values `pubXT`, re-freeze A3). -/
noncomputable abbrev memT (Ti : TInst) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Mem :=
  memTX Ti Lvm.VEq.pubXT x qm qr

/-- **The statics `NodeSound` reads at a stage** (Q_link's stream and checks, `KS`'s split and blocks, the sponge's
blocks, Q_sig's chain length, the stream region, the plan). -/
structure NodeStC (C : QCfg) : Prop where
  stream : StreamOk C.p
  qok : QOk C.p (lay C)
  ks : ksSplit C.p = 7680
  blk : spongeBlocks C.p ≤ 7680
  nblk : spongeBlocks C.p = Lvm.KSponge.nBlk (hashedLen C.p)
  ln : (sigIn C).ln = 20
  wsl : 2 ^ (lay C).m ≤ 17 * 2 ^ 14
  ns : (lay C).sb + 2 ^ (lay C).m ≤ nK C
  plan : PlanC C.p

/-- **`NodeSound` at a stage from the parts** (`nodeSoundF`'s proof over the configuration `C`, the stage's `V_S`
(`parseOk C.p`, then `drive C.p D`), `nPub` `PUB` lanes and the public values `pb`). -/
theorem nodeSoundC (C : QCfg) (VS : SProg) (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (hVS : ∀ vk c π, VS vk c π = if parseOk C.p vk c π then drive C.p π (D vk c) else .ret false)
    (St : NodeStC C) (nPub : ℕ) (pb : List UInt8 → Lvm.Pub)
    (vk : RecursionFast.Digest) (Ti : TInst) (qa : BM Unit) (G : GoodRel)
    (hQ : Ti.Q = toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa))
    (hinj : GInj (max (Ti.Q.cells .K) (Ti.Q.cells .E)))
    (hGK : ∀ c x qm qr, okS vk c x = true → G x qm qr → GoodKP C.p x (qm, qr))
    (hholds : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      Ti.Q.Holds (memTX Ti pb x qm qr) ∧ Ti.Q.Asserts (memTX Ti pb x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMB (spongeBlocks C.p) nPub (lay C) (sigIn C) (memTX Ti pb x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ y < (qltData C.p (lay C)).length,
        (memTX Ti pb x qm qr).k ((lay C).qt + y) = (qltData C.p (lay C)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ k < (opens C.p).length, ∀ j < ((opens C.p).getD k default).L.t,
        ∀ z < ((opens C.p).getD k default).L.height,
        (memTX Ti pb x qm qr).k (bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z) =
          if ansBit C.p (wsC qr) (((opens C.p).getD k default).pe + j / 8)
            (j % 8 * ((opens C.p).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      SigBits (sigIn C) (qsig (sigIn C) (p1P (lay C) (nK C) 0 C.p)).1 (memTX Ti pb x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMB (spongeBlocks C.p) nPub (lay C) (sigIn C) (memTX Ti pb x qm qr) vk x qm qr →
      LaneLink C.p (wsC qr) → LinkOk C.p (decode C.p (wsC qr)) →
      Ok (ctxOf Ti.Q) (memTX Ti pb x qm qr) qa (p2P (lay C) (sigIn C) (nK C) 0 C.p) →
      D vk (hdrOf x).cL (traceBytesB (decode C.p (wsC qr))) = true) :
    NodeSound VS vk G (childSP C.p) := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ chain_of_goodKP hok (hGK c x qm qr hok hG))
    fun c x qm qr hok hb hG ↦ ?_
  have hK := hGK c x qm qr hok hG
  obtain ⟨hH, hA⟩ := hholds c x qm qr hok hb hG
  have hinj' := hinj
  rw [hQ] at hH hA hinj'
  have P := parts_of_holdsP hH hA
  have mp := hmap c x qm qr hok hb hG
  have hwsl : 2 ^ (lay C).m ≤ (wsC qr).length := by
    rw [wsC, wsOf, List.length_map, List.length_range]; exact St.wsl
  have hqin : QIn C.p (lay C) (wsC qr) (memTX Ti pb x qm qr) :=
    ⟨mp.flag, mp.stream, hqlt c x qm qr hok hb hG, hpos c x qm qr hok hb hG⟩
  have hN : (ctxOf (toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa))).cells .K ≤
      max ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .K)
        ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .E) := by
    rw [NS.ctxOf_cells]; exact le_max_left _ _
  have hNs : (lay C).sb + 2 ^ (lay C).m ≤
      max ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .K)
        ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .E) :=
    le_trans St.ns (le_trans (nK_le_cells _ _ _) (le_max_left _ _))
  obtain ⟨hLL, hpad⟩ := qlink_sound St.stream St.qok hqin hwsl hinj' hN hNs P.1.1 P.1.2
  have hlink := linkOk_of_laneLink St.stream hLL
  have hks := sigKSin_of_goodKP C.p St.ks St.blk hK mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨hsig, hchild⟩ := qsig_sound_in (by rw [St.ln]; omega) P.2.1 mp.flag hks
    (hbits c x qm qr hok hb hG) fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
  have hmd := (digAt_of_cells mp.md).trans
    (traceDigest_of_goodKP C.p St.ks St.stream St.nblk St.blk hK hLL hpad)
  have har := harith c x qm qr hok hb hG mp hLL hlink (by rw [hQ]; exact P.2.2)
  exact accV_childC C.p VS D hVS St.plan qr hlink har hsig hchild St.ln mp.vk mp.cL mp.sl hmd mp.sg mp.hd
    (okS_sig hok hb)

/-- S2GF's node statics. -/
theorem nodeStF20 : NodeStC cfgF20 :=
  ⟨streamOk_P20F, hQF20, ksSplit_P20F, by rw [show cfgF20.p = P20F from rfl, spongeBlocks_P20F.1]; norm_num,
    spongeBlocks_nBlk_P20F, rfl,
    by decide, by decide, planC_P20F⟩

set_option maxRecDepth 100000 in
/-- **`NodeSound` at S2GF from the parts** (`nodeSoundC` at `cfgF20`, `VSFX N`, `pubXF`). -/
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
    NodeSound (E2V.VSFX N) vk G (childSP P20F) :=
  nodeSoundC cfgF20 (E2V.VSFX N) (E2V.decideFFX P20F N) (fun _ _ _ => rfl) nodeStF20 (pubLanesX accVF) Lvm.VEq.pubXF
    vk Ti qa G hQ hinj hGK hholds hmap hqlt hpos hbits harith

end Lvm.E2Q
