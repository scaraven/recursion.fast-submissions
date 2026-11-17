-- New for lvm2 U-TAPE (UT-L, 2026-11-16): DAY-0 STATEMENTS of S2GU's good pair and the K2-LS bridge (the tape's
-- sponge half is a sponge table: `traceDigest_of_KS`, `wots*_of_KS` apply on the `Y` block and the stream block).
-- Every `sorry` is a day-0 statement tagged `-- UTAPE-STMT <n>`.
import LvmS2GUFront
import LvmS2GUSched
import LvmNodeSoundKS
import LvmMPSig
import LvmS2GUPlan

-- (SLF-K: 9 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

/-!
# S2GU's good pair (day-0 statements)

* `spongeBlocksGU` (3,961, `ref/utape.py`), `contRowsU` (the trace rows `1 … B − 1`, the key leaf's rows
  `8,080 … 8,110`); **`spongeBlocksGU_eq`**, **`contU_iff`** (the wire's intervals are the rows).
* **`GkU`**: the Keccak half of a good pair at S2GU: the tape's relation on `C_main` (`TapeRelU`: chain half and the
  25 lanes of every sponge row) and the boundary claims are `GbTT`'s. No `KS` block: `Y` is the `Y` block, the messages
  the stream block `S`; the boundary claims stay `GbTT`'s.
* `SBlkU`: `qr` is `qm`'s stream block at S2GU (`sOffU20`).
* The bridge (owner L): **`spongeRel_of_GkU`** (K2-LS's `SpongeRel` on the virtual input column),
  **`traceDigest_of_GkU`** (row `B − 1` of the sponge half outputs the child's trace digest), **`sigKSin_of_GkU`**
  (Q_sig's `SigKSin` from the `X` rows of `S` and the `Y` block's digest cells).
-/

set_option autoImplicit false

namespace Lvm.E2U

open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **`qr` is `qm`'s stream block at S2GU** (`2^19` words at `CMain.sOffU20`). -/
def SBlkU (qm : Column CMain.nu20) (qr : Column 19) : Prop :=
  ∀ w < 2 ^ 19, qr.values.getD w 0 = qm.values.getD (CMain.sOffU20 + w) 0

/-- **The Keccak half of a good pair** for a child trace of `b + 1` sponge blocks (`GkFR`'s successor): the merged tape's relation on `C_main` (the
boundary claims are `GbTT`'s `BndS`, as at S2GT). -/
def GkB (b : ℕ) (x : List UInt8) (p : Column CMain.nu20 × Column 19) : Prop :=
  TapeRelB b (Lvm.ASM.hdrOf x).s (Lvm.ASM.hdrOf x).n (colM p.1)

/-- `Y`'s lanes on a `C_main` candidate. -/
abbrev YqU (qm : Column CMain.nu20) : ℕ → ℕ → K := yU (colM qm)

/-- The message lanes on a `C_main` candidate (the stream block's columns). -/
abbrev MqU (qm : Column CMain.nu20) : ℕ → ℕ → K := msgU (colM qm)

/-- The stream block's message lanes are `qr`'s (`qr` is `qm`'s stream block). -/
theorem MqU_eq {qm : Column CMain.nu20} {qr : Column 19} (hS : SBlkU qm qr) {j l : ℕ} (hj : j < 2 ^ 14)
    (hl : l < 17) : MqU qm j l = msgM qr j l := by
  simp only [MqU, msgU, colM, msgM, wd]
  rw [hS _ (by (clear * - hj hl; omega))]
  exact congrArg (fun k ↦ qm.values.getD k 0) (by simp only [CMain.sOffU20]; (clear * -; omega))

/-- **Byte `p` of the child's stream is byte `p mod 136` of sponge row `p / 136`** (`msgBytes_eq_stream` at S2GU: no
split, every row's messages are the stream block's). -/
theorem msgBytes_eq_streamU {qm : Column CMain.nu20} {qr : Column 19} (hS : SBlkU qm qr) {p : ℕ}
    (hp : p / 136 < 2 ^ 14) :
    Lvm.KG.msgBytes (MqU qm) (p / 136) (p % 136) = (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).getD p 0 := by
  have hq : p % 136 < 136 := Nat.mod_lt _ (by norm_num)
  have hl : p % 136 / 8 < 17 := by (clear * -; omega)
  have hb : p % 136 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e1 : p = 8 * (17 * (p / 136) + p % 136 / 8) + p % 136 % 8 := by (clear * -; omega)
  have hu : 17 * (p / 136) + p % 136 / 8 < 17 * 2 ^ 14 := by (clear * - hp; omega)
  have hc : Lvm.X.crecIdx (17 * (p / 136) + p % 136 / 8) = p % 136 / 8 * 2 ^ 14 + p / 136 := by
    unfold Lvm.X.crecIdx; (clear * - hl; omega)
  have hm : Lvm.KG.msgBytes (MqU qm) (p / 136) (p % 136) = Lvm.KG.msgBytes (msgM qr) (p / 136) (p % 136) := by
    simp only [Lvm.KG.msgBytes]; rw [MqU_eq hS hp hl]
  conv_rhs => rw [e1]
  rw [hm, byte_of_lane _ _ _ hb, toUInt8_mod]
  simp only [Lvm.KG.msgBytes, msgM, wd, lw, wsOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu, Option.map_some,
    Option.getD_some, Lvm.X.laneOf, hc, wOfCol]
  exact Lvm.Wots.byteW_toNat _ hb

/-- A row from the split absorbs the `X` cells (`xorMsg_cells` at S2GU: the `X` rows are the stream block's). -/
theorem xorMsg_cellsU {qm : Column CMain.nu20} {v : ℕ → FK} {f : ℕ → ℕ} {r : ℕ}
    (h : ∀ l < 17, v (f l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l)) (a : RecursionFast.Keccak.State) :
    Lvm.KSponge.xorMsg a (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.xorMsg a (Lvm.KG.msgBytes (MqU qm) (ksSplit P20 + r)) := by
  have e : Lvm.KSponge.rateArr (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.rateArr (Lvm.KG.msgBytes (MqU qm) (ksSplit P20 + r)) := by
    unfold Lvm.KSponge.rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [Lvm.Wots.laneByte, lanesW, Lvm.KG.msgBytes]
    rw [h _ (by (clear * - hj; omega))]
    rfl
  simp only [Lvm.KSponge.xorMsg, e]

end Lvm.E2U
