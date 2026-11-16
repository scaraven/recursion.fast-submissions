-- New for lvm2 E2-FT (E2F-C6): the inputs of the S2GF front's phases (`front_phasesF`) on a good pair's memory: the
-- row switches' words (`rowAuxL_sound` on the layout's looped blocks), Q_sig's `ChildOk` (again, as `nodeSoundF`),
-- the child's `n'` (bits, range) and the bits of `s'` from Q_sig's `SigBits` and the `s'` bit class.
import LvmE2QHarGen
import LvmE2QHarFacts
import LvmE2QInst

/-!
# The front's inputs at S2GF

* **`sBits_onC`**: the `s'` bit class's outputs (`sBits_on` at any configuration); **`sBitsD_of`**: as `sBitsD`.
* **`rowWords_of_aux`**, **`rowWordsF`**: the two row switches' free cells `t_j` are V's row words of the slices.
* **`frontIns`**: `n'`'s bits on Q_sig's cells, `1 ≤ n' ≤ 2^20`, the bits of `s'`.
* **`childOkF`**: Q_sig's `ChildOk` at S2GF on a good pair's memory.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS Lvm.Typed
open Lvm.QTyped
open Lvm.Bits Lvm.BitsTab Lvm.Har
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

-- `sBits_onC`, `pw_onC`, `rowWords_of_aux`, `sBitsD_of`, `frontIns` are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

section Pair

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- **The two row switches' words at S2GF** (the wire's at `tBw`, `KS`'s at `tBk`) on a good pair's memory. -/
theorem rowWordsF (S : NodeGF frzF20 QF20 layF20 NTF20) (H : THypX TiF20) (hG : E2V.GoodTF TiF20 H x qm qr) :
    (∀ j < 128, (memF TiF20 x qm qr).k (tBw cfgF20 + j) =
      rowWordD (Lvm.Q2.slicesOf (memF TiF20 x qm qr) (wireSlices P20F)) j) ∧
    (∀ j < 128, (memF TiF20 x qm qr).k (tBk cfgF20 + j) =
      rowWordD (Lvm.Q2.slicesOf (memF TiF20 x qm qr) (ksSlices P20F)) j) := by
  obtain ⟨f, hf⟩ := aux_mkLayD QF20 (specQF cfgF20 QF20 powF20) dintsF20
  have hmem : ∀ B, B ∈ Lvm.Q2.rowAuxL (f (specQ cfgF20 QF20).auxWords.length) (tBw cfgF20) (wireSlices P20F) ++
      Lvm.Q2.rowAuxL (f ((specQ cfgF20 QF20).auxWords.length + 1)) (tBk cfgF20) (ksSlices P20F) →
      B ∈ layF20.aux := fun B hB => by
    show B ∈ (mkLayD QF20 (specQF cfgF20 QF20 powF20) dintsF20).1.aux
    rw [hf]
    show B ∈ (specQ cfgF20 QF20).auxOf f ++ _ ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hB)
  exact ⟨fun j hj => rowWords_of_aux S.st.hlay (one_zTX H pubXF) hG.1.1.1.1
      (fun B hB => hmem B (List.mem_append_left _ hB)) hj,
    fun j hj => rowWords_of_aux S.st.hlay (one_zTX H pubXF) hG.1.1.1.1
      (fun B hB => hmem B (List.mem_append_right _ hB)) hj⟩

/-- **Q_sig's `ChildOk` at S2GF** on a good pair's memory (`nodeSoundF`'s `qsig_sound_in`, again). -/
theorem childOkF (S : NodeGF frzF20 QF20 layF20 NTF20) (H : THypX TiF20) {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : E2V.GoodTF TiF20 H x qm qr ∧ SBlk qm qr) : ChildOk (sigIn cfgF20) (memF TiF20 x qm qr).k := by
  obtain ⟨hH, hA⟩ := hholdsF S H hG
  have hH' : QF20.Holds (memF TiF20 x qm qr) := hH
  have hA' : QF20.Asserts (memF TiF20 x qm qr) := hA
  rw [QF20_eq] at hH' hA'
  have P := parts_of_holdsP hH' hA'
  have mp := hmapF S H hok hb hG
  have hks := sigKSin_of_goodKP P20F ksSplit_P20F (by rw [spongeBlocks_P20F.1]; norm_num) (goodKF_of hok hG.1)
    mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [show (sigIn cfgF20).ln = 20 from rfl]; omega) P.2.1 mp.flag hks (hbitsF S H hG.1)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

end Pair

end Lvm.E2Q
