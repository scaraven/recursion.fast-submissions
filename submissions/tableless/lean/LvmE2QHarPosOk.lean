-- New for lvm2 E2-FT (E2F-C7): `C_main`'s opening reads its positions from Q_link's position cells at S2GF (roll 11's
-- `posOkMT`: `posOk_of`, `posCellsT`, `out1_entryT` for any configuration, then at `cfgF20`).
import LvmE2QHarGen
import LvmE2QHarIn
import LvmFinPos

/-!
# `PosOk` at S2GF

* **`out1_entryC`**, **`posVal_onC`**: a position class's output, the two position fields' sum (`posVal_on`), for any
  configuration (roll 11's `out1_entryT`/`posVal_onT` at `cfg20`).
* **`posOk_ofG`**: `PosOk` from the position cells' values (`posOk_of` for any parameter set).
* **`posCellsF`**: Q_link's position cells hold `kOf (posL …)` of the child's stream on a good S2GF pair.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har
open LeanVM.Protocol (Column)

-- `out1_entryC`, `posVal_onC`, `posOk_ofG` are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

section Pair

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- **Q_link's position cells hold `kOf (posL …)` of the child's stream** on a good S2GF pair (`posCellsT`). -/
theorem posCellsF (S : NodeGF frzF20 QF20 layF20 NTF20) (H : THypX TiF20) {vk c : RecursionFast.Digest}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : E2V.GoodTF TiF20 H x qm qr ∧ SBlk qm qr) :
    ∀ k < (opens P20F).length, ((opens P20F).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20F).getD k default).L.t,
      (memF TiF20 x qm qr).k (nK cfgF20 + posIdx P20F k j) =
        kOf (posL P20F (wsC qr) (((opens P20F).getD k default).pe + j / 8)
          (j % 8 * ((opens P20F).getD k default).L.height) ((opens P20F).getD k default).L.height) := by
  intro k hk hH j hj
  obtain ⟨hH', hA⟩ := hholdsF S H hG
  have hH'' : QF20.Holds (memF TiF20 x qm qr) := hH'
  have hA' : QF20.Asserts (memF TiF20 x qm qr) := hA
  rw [QF20_eq] at hH'' hA'
  have P := parts_of_holdsP hH'' hA'
  have mp := hmapF S H hok hb hG
  have hp : cfgF20.p = P20F := rfl
  have hk' : k < (opens cfgF20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgF20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgF20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := posVal_onC (C := cfgF20) (outsOnF S H hG.1) (by rw [hp]; exact streamOk_P20F)
    (by rw [hp]; exact hQF20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := qlink_pos (pt := p0 (nK cfgF20) 0) hQF20 P.1.1 hk hj
  exact hq.trans hv

end Pair

end Lvm.E2Q
