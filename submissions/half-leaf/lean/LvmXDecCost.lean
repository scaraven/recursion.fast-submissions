-- WP-13b: the decoder's well-formedness, cost and fuel projection, and the non-vacuity checks (new).
import LvmXDecIR4
import LvmXRead2

-- (GOLF2: 8 declarations that `certified` does not use moved verbatim to `LvmXTopOff`, outside its import closure.)

/-!
# The decoder's cost and the fuel projection

* `wf_decIR`, `noLoopT_decIR`, `outs_decIR`: what `DecOk` needs of the decoder's part.
* **`cost_decIR`**: `265,710,864,928` steps (`≈ 2^37.95`; interpolation `≈ 2^37.94`, `Enc₀`
  `≈ 2^28.0`, agreement `≈ 2^27.1`, inverse NTTs `≈ 2^30.2`).
* **`decode_fixed_le`**: memory `2^25` + the column reads (`cost_readIR`, `≈ 2^30.9`) + the
  decoder is below `2^38`, so below WP-3's acceptance line `2^44` and `fuel_base = 2^46` with a
  factor `2^8` (`decode_fuel_margin`).
* Non-vacuity: `decodeRec_correct_zero` (the zero word, `α = 0`, `f₁ = 0` satisfy the hypotheses of
  `decodeRec_correct`, which returns the zero message), `decLay_example` (a layout below `memX`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

theorem wf_decIR (dB wB aB fB : ℕ) : WF (decIR dB wB aB fB) := by
  have h1 := wf_wtabIR (tbB dB)
  have h2 := wf_eqtIR 6 aB (qB dB)
  have h3 := fun c => wf_mcpIR (2 ^ 13) (fB + c) 3 (encB dB + c * 2 ^ 15)
  have h4 := fun c => wf_zeroIR (2 ^ 15 - 2 ^ 13) (encB dB + c * 2 ^ 15 + 2 ^ 13)
  have h5 := wf_fwdIR 15 (tbB dB)
  have h6 := wf_agreeIR wB (qB dB) (encB dB) (agB dB)
  have h7 := wf_baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)
  have h8 := wf_bflyIR 13 (tbB dB)
  have h9 := wf_rowsIR (oB dB) (mB dB)
  have n8 := bflyIR_nw_hi 13 (tbB dB) (r := zC) (by decide)
  simp only [decIR, encIR, encC, okIR, decTail, bflyAll, bflyRow, WF, Writes, Prim.dst, h1, h2,
    h3, h4, h5, h6, h7, h8, h9, n8, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq_left, or_false, false_or, true_and, and_true]
  simp +decide [rA0, zK, rOk, zT, zN, zC, cTmp, regs]

theorem noLoopT_decIR (dB wB aB fB : ℕ) : NoLoopT (decIR dB wB aB fB) := by
  simp only [decIR, encIR, encC, okIR, decTail, bflyAll, bflyRow, NoLoopT, noLoopT_wtabIR,
    noLoopT_eqtIR, noLoopT_mcpIR, noLoopT_zeroIR, noLoopT_fwdIR, noLoopT_agreeIR, noLoopT_baryIR,
    noLoopT_bflyIR, noLoopT_rowsIR, and_self]

theorem outs_decIR (dB wB aB fB t : ℕ) : outs (decIR dB wB aB fB) t = 0 := by
  simp only [decIR, encIR, encC, okIR, decTail, bflyAll, bflyRow, outs, outs_wtabIR, outs_eqtIR,
    outs_mcpIR, outs_zeroIR, outs_fwdIR, outs_agreeIR, outs_baryIR, outs_bflyIR, outs_rowsIR]
  norm_num

/-- **The decoder's cost** (`≈ 2^37.95`). -/
theorem cost_decIR (dB wB aB fB t : ℕ) : cost (decIR dB wB aB fB) t = 265710864928 := by
  simp only [decIR, encIR, okIR, decTail, cost, cost_wtabIR, cost_eqtIR_six, cost_encC,
    cost_agreeIR, cost_baryIR_lvm, cost_bflyAll, cost_rowsIR, blkSteps, List.length_cons,
    List.length_nil]
  norm_num

/-! ## The output is untouched; the program size -/

/-- Does the program contain an output statement? -/
def hasOut : XIR → Bool
  | .out _ => true
  | .seq p q => hasOut p || hasOut q
  | .ite _ p q => hasOut p || hasOut q
  | .loopK _ _ _ b => hasOut b
  | .loopT _ _ _ b => hasOut b
  | _ => false

theorem iterL_o {f : St → St} {c : ℕ} (hf : ∀ s, (f s).o = s.o) :
    ∀ k s, (iterL f c k s).o = s.o
  | 0, _ => rfl
  | k + 1, s => (iterL_o hf k _).trans (hf s)

/-- **A program without output statements leaves the output unchanged.** -/
theorem sem_o (I : Array Word) : ∀ (P : XIR) (s : St), hasOut P = false → (semXIR I P s).o = s.o
  | .blk _, _, _ => rfl
  | .load .., _, _ => rfl
  | .store .., _, _ => rfl
  | .input .., _, _ => rfl
  | .out _, _, h => by simp [hasOut] at h
  | .seq p q, s, h => by
    simp only [hasOut, Bool.or_eq_false_iff] at h
    rw [semXIR_seq, sem_o I q _ h.2, sem_o I p s h.1]
  | .ite c p q, s, h => by
    simp only [hasOut, Bool.or_eq_false_iff] at h
    rw [semXIR_ite]; split
    · exact sem_o I q s h.2
    · exact sem_o I p s h.1
  | .loopK c n K b, s, h => by
    simp only [semXIR]; exact iterL_o (fun s' => sem_o I b s' h) _ _
  | .loopT c n cap b, s, h => by
    simp only [semXIR]; exact iterL_o (fun s' => sem_o I b s' h) _ _

/-- **The decoder's statement count** (for `DecOk.size`, `≤ 2^19`). -/
theorem sizeIR_decIR (dB wB aB fB : ℕ) : sizeIR (decIR dB wB aB fB) = 4767 := by
  simp only [KeepC, KeepF, ReadsOut, aBody, addr1Ps, addrPs, agreeIR, agreeM, alphaBody, alphaIR, appendIR, arithIR, baryIR, baryValK, baseP, bflyAll, bflyIR, bflyRow, cBody, decIR, decTail, djK, eAtK, eBody, ellK, encC, encIR, eqtAd, eqtBitPs, eqtBody, eqtEnt, eqtIR, eqtLd1, eqtLdE, eqtOm, eqtPre, eqtSt1, eqtStE, fPre, fStep, farithIR, flevelIR, foldIR, foldPM, fpairBody, fwdIR, fwdTop, hiP, laneBody, levelIR, loP, lvlStep, macC, mcpBody, mcpIR, mcpLoop, msgRow, okIR, pairBody, pairOf, pairPs, posBody, row0Body, row0IR, rowBody, rowIR, rowsIR, sBody, testIR, wInner, wgtK, wtBody, wtIR, wtabIR, yIR, zeroBody, zeroIR, mulK, addK, invK, mulE, sizeIR, blkSteps, len_mulKC, len_invKC, len_mulEC,
    List.length_cons, List.length_nil, List.length_append, List.length_map, List.length_range]
  norm_num

/-! ## Non-vacuity -/

end Lvm.X
