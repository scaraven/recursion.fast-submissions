-- New for lvm2 (roll 8 = B1, L-D): `nodeT20` with the typed `BITS` rows' facts discharged (`LvmNodeSoundTBits`,
-- `LvmNodeSoundTBV`): Q_link's position bits, Q_sig's `SigBits`, and `BVT` for the typed HAR, with the openings'
-- position cells (`posCellsT`; roll 7's `posCells20`) and `PosOk` (`posOk_of`). lvm2 roll 11 (M′ `S2GM`, R11-N): on
-- stream-block pairs (`SBlk`), one opening (`posOkMT` from `LvmMPNodePos.posLanesS20`; B1's `posOkRT` is gone).
import LvmNodeSoundT20
import LvmNodeSoundTBV
import LvmMPNodePos

/-!
# `nodeT20` with the `BITS` facts

* **`childOkT`**: Q_sig's `ChildOk` on a good node pair's memory (the holds chain, `qsig_sound_in`).
* **`posCellsT`**: Q_link's position cells hold `kOf (posL …)` of the child's stream (`qlink_pos`, `posVal_on`).
* **`posOkMT`**: `BVT`'s `posm` (M′: the child's one opening, `C_main`'s, from `openU P20 + 15`).
* **`nodeT20B S H vk hchk`**: `NodeSound VSB20 vk (fun x qm qr ↦ GoodT Ti20 H x qm qr ∧ SBlk qm qr) childS`
  (`nodeT20 S H vk` is `nodeT20B S H vk S.chk`; B1: on every `GoodT` pair).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **Q_sig's `ChildOk` on a good node pair's memory.** -/
theorem childOkT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ChildOk (sigIn cfg20) (memT x qm qr).k := by
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  obtain ⟨hH, hA⟩ := holds_memT S.toStaticFactsT hG (readdT S H hchk hG hSB)
  have hinj := S.inj
  rw [QB20_qn] at hH hA hinj
  have P := parts_of_holds hH hA
  have mp := inMapT S.toStaticFactsT hin S.sig qm qr hSB hok hb
  have hks := sigKSin_of_goodK (goodK_of hok hG) mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [hln20]; omega) P.2.1 mp.flag hks (sigBitsT S H hG)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

theorem cfg20_pT : cfg20.p = P20 := rfl

/-- **Q_link's position cells hold `kOf (posL …)` of the child's stream** on a good pair's memory
(`posCells20`: Q_link's `qlink_pos` and `posVal_on`). -/
theorem posCellsT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t,
      (memT x qm qr).k (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height) ((opens P20).getD k default).L.height) := by
  intro k hk hH j hj
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  obtain ⟨hH', hA⟩ := holds_memT S.toStaticFactsT hG (readdT S H hchk hG hSB)
  rw [QB20_qn] at hH' hA
  have P := parts_of_holds hH' hA
  have mp := inMapT S.toStaticFactsT hin S.sig qm qr hSB hok hb
  have hk' : k < (opens cfg20.p).length := by rw [cfg20_pT]; exact hk
  have hH'' : ((opens cfg20.p).getD k default).L.height ≤ 64 := by rw [cfg20_pT]; exact hH
  have hj' : j < ((opens cfg20.p).getD k default).L.t := by rw [cfg20_pT]; exact hj
  have hv := posVal_onT (outsOn_memT S H hG) (by rw [cfg20_pT]; exact hS20) (by rw [cfg20_pT]; exact hQ20)
    mp.stream hk' hH'' hj'
  rw [cfg20_pT] at hv
  have hq := qlink_pos (pt := p0 (nK cfg20) 0) hQ20 P.1.1 hk hj
  exact hq.trans hv

/-- **`BVT`'s `posm`** (M′ `S2GM`: the child's one opening, `C_main`'s, openings `0 + i` from `openU P20 + 15`;
B1: `C_main`'s openings `2 + i` after `C_rec`'s): its position cells hold `F`'s positions. -/
theorem posOkMT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr)
    (hL : LaneLink P20 (wsC qr)) :
    PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) (memT x qm qr) (sigC qr) 0 P20.mainLevels
      (openU P20 + 15) :=
  Lvm.Fin.posOk_of _ 0 (fun i => by rw [Nat.zero_add]; rfl) Lvm.Fin.posLanesS20 hS20 hL hQ20
    (posCellsT S H hchk hok hb hG hSB)

/-- **`nodeT20`, the `BITS` facts discharged** (input: the guard's `nodeChkB`, `SF20.chk`; M′ `S2GM`: on
stream-block pairs, `nodeSoundTG` at `GoodT ∧ SBlk`). -/
theorem nodeT20B (S : Lvm.CT.SF20) (H : THyp Lvm.CT.Ti20) (vk : RecursionFast.Digest)
    (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true) :
    NodeSound VSB20 vk (fun x qm qr ↦ GoodT Lvm.CT.Ti20 H x qm qr ∧ SBlk qm qr) childS := by
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  refine nodeSoundTG vk H S _ (fun _ _ _ h ↦ h.1) (fun _ _ _ _ _ _ hG ↦ readdT S H hchk hG.1 hG.2)
    (fun _ _ qm qr hok hb hG ↦ inMapT S.toStaticFactsT hin S.sig qm qr hG.2 hok hb)
    (fun _ x qm qr _ _ _ ↦ hqltT S.toStaticFactsT x qm qr)
    (fun _ x qm qr hok hb hG ↦ hposT (outsOn_memT S H hG.1)
      (inMapT S.toStaticFactsT hin S.sig qm qr hG.2 hok hb).stream)
    (fun _ _ _ _ _ _ hG ↦ sigBitsT S H hG.1) ?_
  intro c x qm qr hok hb hG' hm hL hLk hrun
  obtain ⟨hG, hSB⟩ := hG'
  have hv := outsOn_memT S H hG
  have hn := nRange_on (childOkT S H hchk hok hb hG hSB) hm.hd hL vk (hdrOf x).cL
  have hbv : BVT vk x qm qr :=
    ⟨sBits_on hv, nBits_on (sigBitsT S H hG), hn.1, hn.2, posOkMT S H hchk hok hb hG hSB hL, pw_on hv (by decide)⟩
  obtain ⟨h1, h2⟩ := harithT20 S H hok hb hG hm hL hLk hrun hbv
  exact decideFT_of S H hG.1.2 h1 h2

end Lvm.NS
