-- New for lvm2 (roll 8 = B1, L-D): the typed `BITS` rows' facts that `NodeSound` reads, on the memory read off a good
-- pair's words: `outT_sound` (`LvmQTypedBitsS`) at `P20`, then Q_sig's `SigBits` as roll 7's `sigBitsOk`
-- (`LvmSigBits`, WP-12b) with the bus's `out1_at` replaced by the typed rows' outputs (its case analysis copied).
import LvmNodeSoundT
import LvmQTypedBitsS

/-!
# The typed `BITS` rows' facts at `P20`

* **`outT20`**: every class of `bspecs cfg20 noData`, every real row, every valid output, on `memT x qm qr` of a good
  pair (`outT_sound` with the solver's bases, `aux_specQ`).
* **`sigBits_of_outs`**: `SigBits I o v` from the six classes' outputs on `v` (roll 7's `sigBitsOk`, generic in the
  memory); **`sigBitsT`**: Q_sig's `SigBits` on `memT` (nodeT20's `hbits`).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits LeanVM.Protocol
open Lvm.VEq (pubX)

theorem layT20_mk : layT20 = (mkLayD QB20 (specQ cfg20 QB20) dints20).1 := rfl

/-- **The `BITS` classes' outputs on a good pair's memory** at `P20`. -/
theorem outT20 (S : Lvm.CT.SF20) (H : THyp TiB) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) {B : BSpec} (hB : B ∈ bspecs cfg20 noData) {y : ℕ} (hy : y < B.n) :
    ∃ w : FK, (B.rd = true → (memT x qm qr).k (B.wc y) = w) ∧
      ∀ j < B.outs.length, (B.out j).Valid → (memT x qm qr).k (B.oc j y) = ⟨(B.out j).word w.val⟩ := by
  obtain ⟨bw, haux⟩ := aux_specQ cfg20 QB20 dints20
  rw [← layT20_mk] at haux
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hB
  exact outT_sound cfg20 QB20 layT20 (zT x qm qr) bw haux S.hlay (zT_one H x qm qr) (goodT_wiring hG) hi hy

/-- **Q_sig's `BITS` outputs from the classes' outputs** (roll 7's `sigBitsOk`, its case analysis, on any memory). -/
theorem sigBits_of_outs (v : ℕ → FK) (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) (Ss : List BSpec)
    (hT : ∀ B ∈ sigSpecs I o bpl, B ∈ Ss) (hln : 1 ≤ I.ln ∧ I.ln ≤ 62)
    (hws : ∀ B ∈ Ss, ∀ y < B.n, ∃ w : FK, (B.rd = true → v (B.wc y) = w) ∧
      ∀ j < B.outs.length, (B.out j).Valid → v (B.oc j y) = ⟨(B.out j).word w.val⟩) :
    SigBits I o v := by
  have o1 : ∀ (B : BSpec), B ∈ Ss → B.rd = true → ∀ (y j : ℕ), y < B.n → j < B.outs.length →
      ∀ {A Bc : ℕ} {b : BOut}, B.wc y = A → B.oc j y = Bc → B.out j = b → b.Valid → Out1 v A b Bc := by
    intro B hB hrd y j hy hj A Bc b hA hBc hb hv
    obtain ⟨w, h1, h2⟩ := hws B hB y hy
    have := h2 j hj (hb ▸ hv)
    unfold Out1
    rw [← hA, ← hBc, this, h1 hrd, hb]
  have tI := hT (sIdx I (bpl 0)) (by simp [sigSpecs])
  have tM := hT (sMd I (bpl 1)) (by simp [sigSpecs])
  have tC := hT (sCs I (bpl 2)) (by simp [sigSpecs])
  have t24 := hT (s24 I o (bpl 3)) (by simp [sigSpecs])
  have t8 := hT (s8 I o (bpl 4)) (by simp [sigSpecs])
  have tN := hT (sN I (bpl 5)) (by simp [sigSpecs])
  have x0 : ∀ {S : BSpec}, S.n = 1 → 0 < S.n := fun h => by omega
  refine ⟨?_, fun z hz => ?_, ?_, fun r hr => ?_, ?_, fun i hi s hs l hl => ⟨?_, ?_⟩,
    fun i hi l hl => ⟨?_, ?_⟩, fun t ht u hu l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩, ?_, ?_,
    fun z hz => ?_, ?_, ?_, fun l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩⟩
  -- idx: `shl 8`, bits, `shr 16`
  · exact o1 _ tI rfl 0 0 (x0 rfl) (by simp [sIdx]) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tI rfl 0 (1 + z) (x0 rfl) (by simp [sIdx] <;> omega) rfl
      (by simp [sIdx] <;> omega) (getD_idx hz) (show z < 64 by omega)
  · exact o1 _ tI rfl 0 17 (x0 rfl) (by simp [sIdx]) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  -- md: 256 bits
  · exact o1 _ tM rfl (r / 64) (r % 64) (by simp [sMd] <;> omega) (by simp [sMd] <;> omega)
      rfl (by simp only [sMd] <;> omega)
      (getD_bit (Nat.mod_lt _ (by norm_num))) (Nat.mod_lt _ (by norm_num))
  -- cs: ten bits of a free word
  · obtain ⟨w, -, h2⟩ := hws _ tC 0 (by simp [sCs])
    refine ⟨w.val, fun k hk => ?_⟩
    have hb : (sCs I (bpl 2)).out k = .bit k := getD_bit hk
    have := h2 k (by simp [sCs, hk]) (by rw [hb]; show k < 64; omega)
    rw [hb] at this
    exact this
  -- step inputs: `shl 24`, `shr 40`
  · exact o1 _ t24 rfl (4 * (3 * i + s) + l) 0 (by simp only [s24] <;> omega) (by simp [s24])
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by omega,
        show (4 * (3 * i + s) + l) / 4 % 3 = s by omega, show (4 * (3 * i + s) + l) % 4 = l by omega])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t24 rfl (4 * (3 * i + s) + l) 1 (by simp only [s24] <;> omega) (by simp [s24])
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by omega,
        show (4 * (3 * i + s) + l) / 4 % 3 = s by omega, show (4 * (3 * i + s) + l) % 4 = l by omega])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  -- chain ends
  · exact o1 _ t8 rfl (4 * i + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega,
        show (4 * i + l) % 4 = l by omega])
      (by simp only [s8]; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (4 * i + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega,
        show (4 * i + l) % 4 = l by omega])
      (by simp only [s8]; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  -- path node halves
  · exact o1 _ t8 rfl (532 + (8 * t + 4 * u + l)) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (532 + (8 * t + 4 * u + l)) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  -- h'
  · exact o1 _ t8 rfl (660 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (660 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  -- n': `shl 8`, `shr 56`, bits, top, low
  · exact o1 _ tN rfl 0 0 (x0 rfl) (by simp [sN]) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN rfl 0 1 (x0 rfl) (by simp [sN]) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN rfl 0 (2 + z) (x0 rfl) (by simp [sN] <;> omega) rfl
      (by simp [sN] <;> omega) (getD_n hz) (show z < 64 by omega)
  · exact o1 _ tN rfl 0 (I.ln + 3) (x0 rfl) (by simp [sN]) rfl
      (by simp only [sN] <;> omega) getD_n_top (by simp only [BOut.Valid]; omega)
  · exact o1 _ tN rfl 0 (I.ln + 4) (x0 rfl) (by simp [sN]) rfl
      (by simp only [sN] <;> omega) getD_n_low (by simp only [BOut.Valid]; omega)
  -- c_L'
  · exact o1 _ t8 rfl (664 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (664 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  -- leafStmt lanes
  · exact o1 _ t8 rfl (668 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (668 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])


/-- **Q_sig's `SigBits` on a good pair's memory** at `P20` (nodeT20's `hbits`). -/
theorem sigBitsT (S : Lvm.CT.SF20) (H : THyp TiB) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) :
    SigBits (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (memT x qm qr).k :=
  sigBits_of_outs _ (sigIn cfg20) _ (bplOf noData) (bspecs cfg20 noData)
    (fun B hB ↦ List.mem_append_left _ (List.mem_append_left _ hB)) ⟨by decide, by decide⟩
    (fun B hB y hy ↦ outT20 S H hG hB hy)

end Lvm.NS
