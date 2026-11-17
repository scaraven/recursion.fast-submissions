-- New for lvm2 (roll 8 = B1, wave L; moved by L-D for the lead): FIN-BV's position facts that the typed certificate
-- reads, out of `LvmFinBVPos` and `LvmFinDec` (unchanged statements and proofs, a pure move), so that a typed module
-- imports them without the bus path: the fields of a position (`ubit_fld` … `hi_mem`), `PosLanes` and `posOk_of`
-- (`LvmFinBVPos`), and `PosLanes` at `P20` (`posLanes_of` …, `LvmFinDec`; M′ removes B1's `posLanesB20`).
import LvmQAsmLay
import LvmQLinkBits
import LvmXOutSeg
import LvmNodeSoundTr
import LvmQAsmFactsL
import LvmQAsmArith2
import LvmQAsmArith2Whir

-- (GOLF2: 28 declarations that `certified` does not use moved verbatim to `LvmFinPosOff`, outside its import closure.)

-- ===== merged from `LvmQAsmHarPos` (GOLF module merge: `LvmQAsmHarPos.lean` is now a stub importing `LvmFinPos`) =====
section
-- New for lvm (HAR-POS): `F`'s WHIR positions read from `Σ' = sigma p ws` are Q_link's `posL`
-- values (`qsAt_posL`), from `qsAt_getD` (LvmQAsmArith2Whir), `kAt_sigma` (LvmQAsmHarBase) and
-- `posL_eq` (LvmQLinkBridge).

/-!
# `F`'s positions are Q_link's `posL`

`F`'s `j`-th position of level `L` reads bits `(j mod 8)·h …` of a positions answer as one 192-bit
number (`eToNat`, three lanes, lane `0` lowest). When that answer is entry `e`'s (lanes `ansLane p e`,
`+1`, `+2` of `Σ'`), the number is `lw₀ + 2^64 lw₁ + 2^128 lw₂` (`kAt_sigma`), whose bit `n < 192`
is `ansBit p ws e n` (`testBit_limbs`); `posL_eq` then gives `posL`.
-/

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.QLink

theorem lw_lt (ws : List Word) (i : Nat) : lw ws i < 2 ^ 64 := (ws.getD i 0).isLt

/-- Bit `n < 192` of three 64-bit limbs (limb `0` lowest) is bit `n mod 64` of limb `⌊n/64⌋`. -/
theorem testBit_limbs (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) (a n : Nat) (hn : n < 192) :
    (f a + 2 ^ 64 * f (a + 1) + 2 ^ 128 * f (a + 2)).testBit n = (f (a + n / 64)).testBit (n % 64) := by
  have e : f a + 2 ^ 64 * f (a + 1) + 2 ^ 128 * f (a + 2) =
      2 ^ 64 * (2 ^ 64 * f (a + 2) + f (a + 1)) + f a := by
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num]; ring
  rw [e, Nat.testBit_two_pow_mul_add _ (hf a)]
  by_cases h0 : n < 64
  · simp only [h0, ↓reduceIte, Nat.div_eq_of_lt h0, Nat.mod_eq_of_lt h0, Nat.add_zero]
  simp only [h0, ↓reduceIte, Nat.testBit_two_pow_mul_add _ (hf (a + 1))]
  by_cases h1 : n - 64 < 64
  · simp only [h1, ↓reduceIte, show n / 64 = 1 by (clear * - hn h0 h1; omega), show n % 64 = n - 64 by (clear * - hn h0 h1; omega)]
  · simp only [h1, ↓reduceIte, show n / 64 = 2 by (clear * - hn h0 h1; omega), show n % 64 = n - 64 - 64 by (clear * - hn h0 h1; omega)]

/-- **`F`'s `j`-th position of level `L`, read from `Σ'`, is Q_link's `posL`** when the positions
answer it reads (at `P + 72 ⌊j/8⌋ + 40`) is entry `e`'s answer (`hP`) inside the hashed bytes. -/
theorem qsAt_posL (p : Params) (ws : List Word) (P : Nat) (L : Level) (e j : Nat) (hj : j < L.t)
    (hP : P + 72 * (j / 8) + 40 = 8 * ansLane p e)
    (hb : (j % 8) * L.height + L.height ≤ 192)
    (hlen : 8 * ansLane p e + 24 ≤ hashedLen p) (hws : ansLane p e + 3 ≤ ws.length) :
    (qsAt (sigma p ws) P L).getD j 0 = posL p ws e ((j % 8) * L.height) L.height := by
  rw [qsAt_getD _ P L j hj, hP]
  have hfe : eToNat (feAt (sigma p ws) (8 * ansLane p e)) =
      lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2) := by
    unfold eToNat feAt
    rw [show 8 * ansLane p e + 8 = 8 * (ansLane p e + 1) by (clear * -; omega),
      show 8 * ansLane p e + 16 = 8 * (ansLane p e + 2) by (clear * -; omega),
      kAt_sigma p ws _ (by (clear * - hlen; omega)) (by (clear * - hws; omega)), kAt_sigma p ws _ (by (clear * - hlen; omega)) (by (clear * - hws; omega)),
      kAt_sigma p ws _ (by omega) (by (clear * - hws; omega))]
    rfl
  rw [hfe]
  refine (posL_eq p ws _ e _ _ fun n _ h2 => ?_).symm
  rw [testBit_limbs (lw ws) (lw_lt ws) _ n (by (clear * - hb h2; omega))]
  rfl

end Lvm.Har
end
-- ===== end of `LvmQAsmHarPos` =====

/-!
# FIN-BV's position facts

* From `LvmFinBVPos`: `ubit_fld`, `ubit_laneK`, `ubit_toUInt64`, `posL_testBit`, **`fields_posL`**, `lo_mem`,
  `hi_mem`; **`PosLanes`**, **`posOk_of`**.
* From `LvmFinDec`: `lens_run`, `ansLane_run`, `PosLanesR`, **`posLanes_of`**, the extractor-block decision
  (`PosLanesK`, `posLanesKB`, `posLanesK_of_B`). (B1's `posLanesB20`, `posLanesR20`, `posLanesM20`: removed at M′.)
-/

set_option autoImplicit false

namespace Lvm.Fin

section BVPos

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Bits Lvm.NS Lvm.QAsm Lvm.Har LeanVM.Protocol

/-! ## Bits of a field and of a position -/

/-- Bit `i` of a `fld z₀ m d` output: bit `z₀ + (i − d)` of the word for `d ≤ i < d + m`. -/
theorem ubit_fld {z₀ m d : ℕ} (h : z₀ < 64 ∧ 1 ≤ m ∧ m + d ≤ 64) (w : UInt64) (i : ℕ) :
    ubit ((BOut.fld z₀ m d).word w) i =
      (decide (d ≤ i) && decide (i < d + m) && ubit w (z₀ + (i - d))) := by
  obtain ⟨h0, h1, h2⟩ := h
  by_cases hi : i < 64
  · simp only [BOut.word, ubit_shr _ (show 64 - m - d < 64 by (clear * - h1 h2; omega)), ubit_shl _ (show 64 - m < 64 by (clear * - h1; omega)),
      ubit_shr _ h0]
    by_cases c1 : d ≤ i
    · by_cases c2 : i < d + m
      · rw [show z₀ + (64 - m - d + i - (64 - m)) = z₀ + (i - d) by (clear * - h2 c1; omega)]
        simp [c1, c2, show 64 - m - d + i < 64 by (clear * - h2 c2; omega), show 64 - m ≤ 64 - m - d + i by (clear * - h2 c1; omega)]
      · simp [c2, show ¬ (64 - m - d + i < 64) by (clear * - h2 c2; omega)]
    · simp [c1, show ¬ (64 - m ≤ 64 - m - d + i) by (clear * - h2 c1; omega)]
  · rw [ubit_ge _ (by (clear * - hi; omega))]
    simp [show ¬ (i < d + m) by (clear * - h2 hi; omega)]

theorem ubit_laneK (ws : List Word) (j z : ℕ) : ubit (laneK ws j).val z = (lw ws j).testBit z := rfl

theorem ubit_toUInt64 (n : ℕ) {b : ℕ} (hb : b < 64) : ubit n.toUInt64 b = n.testBit b := by
  show (n.toUInt64).toNat.testBit b = _
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow]
  simp [hb]

/-- Bit `b` of a position: bit `s + b` of the answer's lanes, for `b < h`. -/
theorem posL_testBit (p : Params) (ws : List Word) (e s h : ℕ) (hs : s + h ≤ 192) (b : ℕ) :
    (posL p ws e s h).testBit b =
      (decide (b < h) && (lw ws (ansLane p e + (s + b) / 64)).testBit ((s + b) % 64)) := by
  rw [posL_eq p ws (lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2))
    e s h (fun n _ h2 => by rw [testBit_limbs (lw ws) (Har.lw_lt ws) _ n (by omega)]; rfl)]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < h
  · rw [testBit_limbs (lw ws) (Har.lw_lt ws) _ (s + b) (by omega)]
  · simp [hb]

/-- **A position's two fields add up to `posL`** (A20: `lo` holds bits `[0, m₁)`, `hi` bits `[m₁, H)`;
`K` addition is `xor` of disjoint bit ranges). -/
theorem fields_posL (p : Params) (ws : List Word) (e : ℕ) {H i : ℕ} (hH2 : 2 ≤ H) (hH : H ≤ 64)
    (h192 : i * H + H ≤ 192) :
    w64 ((BOut.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2).word
        (laneK ws (ansLane p e + (fields H i).1.1)).val) +
      w64 ((BOut.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2).word
        (laneK ws (ansLane p e + (fields H i).2.1)).val) =
      kOf (posL p ws e (i * H) H) := by
  simp only [fields]
  generalize hs : i * H = s at h192 ⊢
  generalize hm : (if s / 64 = (s + H - 1) / 64 then H - 1 else 64 - s % 64) = m₁
  have hm' : (s / 64 = (s + H - 1) / 64 ∧ m₁ = H - 1) ∨ (s / 64 ≠ (s + H - 1) / 64 ∧ m₁ = 64 - s % 64) := by
    by_cases hc : s / 64 = (s + H - 1) / 64
    · rw [if_pos hc] at hm; exact Or.inl ⟨hc, hm.symm⟩
    · rw [if_neg hc] at hm; exact Or.inr ⟨hc, hm.symm⟩
  have hv1 : s % 64 < 64 ∧ 1 ≤ m₁ ∧ m₁ + 0 ≤ 64 := by (clear * - hH2 hH hs hm hm'; omega)
  have hv2 : (s + m₁) % 64 < 64 ∧ 1 ≤ H - m₁ ∧ H - m₁ + m₁ ≤ 64 := by (clear * - hH2 hH hs hm' hv1; omega)
  show (⟨_ ^^^ _⟩ : FK) = ⟨(posL p ws e s H).toUInt64⟩
  congr 1
  apply u64_ext
  intro b hb
  rw [ubit_xor, ubit_fld hv1, ubit_fld hv2, ubit_toUInt64 _ hb, posL_testBit p ws e s H h192, ubit_laneK,
    ubit_laneK]
  by_cases b1 : b < m₁
  · rw [show (s + b) / 64 = s / 64 by (clear * - hH2 hH hs hm' hv1 hv2 hb b1; omega), show (s + b) % 64 = s % 64 + (b - 0) by (clear * - hH2 hH hs hm' hv1 hv2 hb b1; omega)]
    simp [b1, show ¬ m₁ ≤ b by (clear * - b1; omega), show b < H by (clear * - hv2 b1; omega)]
  · by_cases b2 : b < H
    · rw [show (s + b) / 64 = (s + m₁) / 64 by (clear * - hH2 hH hs hm' hv1 hv2 hb b1 b2; omega), show (s + b) % 64 = (s + m₁) % 64 + (b - m₁) by (clear * - hH2 hH hs hm' hv1 hv2 hb b1 b2; omega)]
      simp [b1, b2, show m₁ ≤ b by (clear * - b1; omega), show b < m₁ + (H - m₁) by (clear * - hv2 b2; omega)]
    · simp [b1, b2, show ¬ b < m₁ + (H - m₁) by (clear * - hv2 b2; omega)]

/-! ## The position classes' field outputs -/

theorem lo_mem (H : ℕ) {i : ℕ} (hi : i < 8) :
    ((BOut.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2), 1, i) ∈
      laneOuts H (fields H i).1.1 := by
  unfold laneOuts
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
  simp

theorem hi_mem (H : ℕ) {i : ℕ} (hi : i < 8) :
    ((BOut.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2), 2, i) ∈
      laneOuts H (fields H i).2.1 := by
  unfold laneOuts
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
  simp

/-! ## `PosOk` -/

/-- **`F`'s positions lanes and Q_link's openings** (a static fact of the schedule and `F`'s layout,
decidable on the frozen parameter set): level `i` of `Ls` (positions lanes from `V`) is opening `k0 + i`
of the plan, of height at most 64, and `F` reads that opening's positions answers (72 bytes each) at the
answers' lanes (`cp`: `lvLanes`' stream, `some p` at S2GB). -/
def PosLanes (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) (cp : Option Params := none) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens p).length ∧ ((opens p).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧
    ∀ x < nAns ((opens p).getD (k0 + i) default),
      8 * (posLanes g ood Ls V cp).getD i 0 + 72 * x + 40 = 8 * ansLane p (((opens p).getD (k0 + i) default).pe + x)

end BVPos

section Dec

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.Har Lvm.Replay Lvm.QLink
open Lvm.QAsm (QCfg cfg20 nK bsB pwB clog2 nAns pbB)
open Lvm.X (Blk blocks lensB lanesOf lanes_eq lensB_opn)

/-! ## FIN-BV's `PosLanes` -/

/-! ### The plan's lengths through the extractor's blocks

The plan's entries after `q₀` are the extractor's blocks' queries (`lens_P20`, `lensL`); a block's
entries and lanes are numbers of the block (`bCnt`, `Blk.lanes`), so an opening's first answer lane
is a sum over the blocks before it (`ansLane_blk`) and its run of 32-byte queries a run of blocks
(`lens_run_blk`): the decision walks 1,415 blocks instead of 5,464 plan entries. -/

-- (R11-N, M′: B1's `posLanesB20`, `posLanesR20`, `posLanesM20` are removed, as R11-IS removed them from `LvmFinDec`:
-- B1's two openings. The one opening of `S2GM` is `LvmMPNodePos`.)

end Dec

end Lvm.Fin
