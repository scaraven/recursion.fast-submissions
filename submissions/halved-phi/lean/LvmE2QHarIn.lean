-- New for lvm2 E2-FT (E2F-C6): the inputs of the S2GF front's phases (`front_phasesF`) on a good pair's memory: the
-- row switches' words (`rowAuxL_sound` on the layout's looped blocks), Q_sig's `ChildOk` (again, as `nodeSoundF`),
-- the child's `n'` (bits, range) and the bits of `s'` from Q_sig's `SigBits` and the `s'` bit class.
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

/-- **The bits of `s'`** from the `s'` bit class `sSpec` (`sBits_on`, any configuration). -/
theorem sBits_onC {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v) : Lvm.Q1.SBitsS v (sigIn C).hd (bsB C) := by
  intro l hl z hz
  have hS : sSpec C (bplOf noData (6 + nPosCls C)) ∈ bspecs C noData :=
    List.mem_append_right _ (by simp)
  have hlen : (sSpec C (bplOf noData (6 + nPosCls C))).outs.length = 64 := by
    show ((List.range 64).map BOut.bit).length = 64; simp
  have hout : (sSpec C (bplOf noData (6 + nPosCls C))).out z = .bit z := by
    show ((List.range 64).map BOut.bit).getD z (.bit 0) = .bit z
    rw [List.getD_eq_getElem _ _ (by simpa using hz)]
    simp
  exact out1_ofC hv hS rfl (y := l) (j := z) hl (by rw [hlen]; exact hz) rfl rfl hout (show z < 64 from hz)

/-- **The PoW fields** (`pw_on`, any configuration): the class `powSpec` writes the low `64 − g` bits of each
opening's PoW lane. -/
theorem pw_onC {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v) (hg : 1 ≤ 64 - C.p.grind) :
    ∀ k < (opens C.p).length, (v (pwB C + k)).val.toNat < 2 ^ (64 - C.p.grind) := by
  intro k hk
  have hS : powSpec C (bplOf noData (7 + nPosCls C)) ∈ bspecs C noData :=
    List.mem_append_right _ (by simp)
  have eout : (powSpec C (bplOf noData (7 + nPosCls C))).out 0 = .fld 0 (64 - C.p.grind) 0 := by
    simp only [powSpec, BitsTab.BSpec.out, List.getD_cons_zero]
  have hx : k < (powSpec C (bplOf noData (7 + nPosCls C))).n := by
    simp only [powSpec]; exact hk
  have h1 := out1_ofC hv hS rfl hx (j := 0) (Bc := pwB C + k) (by simp [powSpec]) rfl rfl eout
    ⟨by decide, hg, by (clear * -; omega)⟩
  unfold Out1 at h1
  rw [h1]
  show ((BOut.fld 0 (64 - C.p.grind) 0).word _).toNat < _
  exact fld_lt' _ hg (by (clear * -; omega))

/-- **A row switch's words from its looped blocks** (`rowAuxL_sound`): when the three `rowAuxL` blocks are blocks of
the layout and the wiring relation holds, the free cells `t_j` are V's row words of the slices. -/
theorem rowWords_of_aux {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} (hlay : tl.Ok Q) (hone : z tl.one = 1)
    (h : WiringRelX Q tl z) {bw tB qs : ℕ} (hmem : ∀ B ∈ Lvm.Q2.rowAuxL bw tB qs, B ∈ tl.aux) {j : ℕ}
    (hj : j < 128) : (memOf tl z).k (tB + j) = rowWordD (Lvm.Q2.slicesOf (memOf tl z) qs) j := by
  refine Lvm.Q2.rowAuxL_sound (bw := bw) (tB := tB) (qs := qs) tl z (fun B hB i hi r hr => ?_) hj
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.mp (hmem B hB)
  obtain ⟨r', hr', hrr⟩ := List.mem_iff_getElem.mp hr
  have hget : tl.aux.getD k default = B := by rw [List.getD_eq_getElem _ _ hk, hkb]
  have := auxRow_of_wiringX Q tl z hlay hone h hk (by rw [hget]; exact hi) (by rw [hget]; exact hr')
  rw [hget, List.getD_eq_getElem _ _ hr', hrr] at this
  exact this


/-- **The bits of `s'` as `sBitsD`** on the `s'` bit cells. -/
theorem sBitsD_of {v : ℕ → FK} {hd sb : ℕ} (h : Lvm.Q1.SBitsS v hd sb) {s : List FK}
    (hs : s = (List.range 4).map fun l => v (hd + 9 + l)) :
    ∀ i < 256, v (sb + i) = if sBitsD s i then 1 else 0 := by
  intro i hi
  have h1 := h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [show sb + 64 * (i / 64) + i % 64 = sb + i by omega] at h1
  unfold Lvm.QSig.Out1 at h1
  rw [h1, Lvm.Q1.bitWord _ (Nat.mod_lt _ (by norm_num)), hs]
  simp only [sBitsD, decide_eq_true hi, Bool.true_and, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show i / 64 < 4 by omega), Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- **The child's `n'`, its bits and range, the bits of `s'`** (the front's inputs from Q_sig's `SigBits`, its
`ChildOk` and the `s'` bit class), on any memory whose stream is `Σ`. -/
theorem frontIns {C : QCfg} {M : Mem} {sig : ByteArray} {T : ℕ} (hS : Lvm.Q1.Streamed M sig T) (hT : 29 ≤ T)
    {o : SigOut} (hbits : SigBits (sigIn C) o M.k) (hch : ChildOk (sigIn C) M.k)
    (hsb : Lvm.Q1.SBitsS M.k (sigIn C).hd (bsB C)) (accV : ℕ) (vk cL : Vector UInt8 32)
    (hln : (sigIn C).ln = 20) (hhd : (sigIn C).hd + 13 = nLane) :
    (∀ j < 20, (kc ((sigIn C).bn + 2 + j)).val M = bitE (pubOfA accV vk cL sig).n j) ∧
      (1 ≤ (pubOfA accV vk cL sig).n ∧ (pubOfA accV vk cL sig).n ≤ 2 ^ 20) ∧
      ∀ i < 256, M.k (bsB C + i) = if sBitsD (pubOfA accV vk cL sig).s i then 1 else 0 := by
  have hn : (pubOfA accV vk cL sig).n = (M.k nLane).val.toNat := pub_n hS hT vk cL
  refine ⟨fun j hj => ?_, ?_, sBitsD_of hsb ?_⟩
  · rw [hn, Cell.val_K]
    exact bitE_out1 (by omega) (hhd ▸ hbits.n_bit j (show j ≤ (sigIn C).ln by omega))
  · rw [hn, ← hhd, ← hln]
    exact ⟨hch.2.2.1, hch.2.2.2.1⟩
  · rw [show (pubOfA accV vk cL sig).s = (pubOf vk cL sig).s from rfl, pub_s hS hT vk cL]
    refine List.map_congr_left fun l _ => ?_
    rw [sLane_eq]
    rfl

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
