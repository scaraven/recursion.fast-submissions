-- lvm6 X9 (X8a §3 item 3): level 0's expansion `expIR` writes W1's level-0 word position-major (`HoldsW`, the
-- `foldIR` input), lane `s` = `laneVal true (replicate 18 0 ++ row) s` (IDX's `getD_pad_shift`). New.
import Lvm6XDescExp

/-!
# Level 0's word on the machine

* **`expIR_holds`**: if the heap holds X2's level-0 rows (46 `K` words per position, word `t` of row `p` at
  `base + 46 p + t`), then after `expIR h base buf` the buffer holds, position-major over `6` lane variables, the word
  `u, p ↦ laneVal true (replicate 18 0 ++ row p) ⟨u⟩` (`HoldsW … buf h 6`).
* **`expIR_holds_wordE`**: the same for W1's `wordE true 0 6 h cs` when commitment `0` has height `h` and its row `p`
  is V1's padded row `replicate 18 0 ++ row p`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir

theorem getD_replicate_lt {α : Type} (r : List α) (z : α) {k : ℕ} (hk : k < 18) :
    (List.replicate 18 z ++ r).getD k z = z := by
  interval_cases k <;> rfl

/-- **Level 0's expansion is W1's word, position-major.** -/
theorem expIR_holds (I : Array Word) (s : St) (hM : Inv s.M) {h base buf : ℕ} (hb : regs ≤ base)
    (hb2 : base + 46 * 2 ^ h < 2 ^ 64) (hbuf : regs ≤ buf) (hbuf2 : buf + 128 * 2 ^ h < 2 ^ 64)
    (hsz : buf + 128 * 2 ^ h ≤ s.M.size) (hdis : base + 46 * 2 ^ h ≤ buf ∨ buf + 128 * 2 ^ h ≤ base)
    (row : ℕ → List BF64) (hrow : ∀ p < 2 ^ h, ∀ t < 46, rdK s.M (base + 46 * p + t) = (row p).getD t 0) :
    HoldsW (semXIR I (expIR h base buf) s).M buf h 6
      (fun u p ↦ Lvm6.Whir.laneVal true (List.replicate 18 0 ++ row p) (bitsToNat u)) := by
  obtain ⟨-, -, hv, -⟩ := expIR_sem I s hM hb hb2 hbuf hbuf2 hsz hdis
  intro p u
  dsimp only
  have hu : bitsToNat u < 64 := bitsToNat_lt u
  obtain ⟨e0, e1⟩ := hv p p.2 (bitsToNat u) hu
  have ea : buf + 2 * ((p : ℕ) * 2 ^ 6 + bitsToNat u) = buf + 2 * (64 * p + bitsToNat u) := by ring
  rw [rdE2, ea, Lvm6.Whir.laneVal, if_pos rfl, QuadraticAlgebra.algebraMap_eq]
  by_cases hk : bitsToNat u < 46
  · rw [getD_pad_shift _ _ hk, ← hrow p p.2 (45 - bitsToNat u) (by omega)]
    rw [if_pos hk, show base + 46 * (p : ℕ) + 45 - bitsToNat u = base + 46 * p + (45 - bitsToNat u) by omega]
      at e0
    simp only [rdK, e0, e1]
    rfl
  · rw [getD_replicate_lt _ _ (by omega)]
    rw [if_neg hk] at e0
    simp only [rdK, e0, e1]
    rfl

/-- **W1's level-0 word** (`wordE true 0 6 h cs`), position-major after `expIR`, when commitment `0` has height `h`
and row `p` is V1's padded row of X2's 46 words. -/
theorem expIR_holds_wordE (I : Array Word) (s : St) (hM : Inv s.M) {h base buf : ℕ} (hb : regs ≤ base)
    (hb2 : base + 46 * 2 ^ h < 2 ^ 64) (hbuf : regs ≤ buf) (hbuf2 : buf + 128 * 2 ^ h < 2 ^ 64)
    (hsz : buf + 128 * 2 ^ h ≤ s.M.size) (hdis : base + 46 * 2 ^ h ≤ buf ∨ buf + 128 * 2 ^ h ≤ base)
    (row : ℕ → List BF64) (hrow : ∀ p < 2 ^ h, ∀ t < 46, rdK s.M (base + 46 * p + t) = (row p).getD t 0)
    {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)} {c : ℕ × ℕ × LeanVM.Protocol.Compile.Word}
    (hc : cs[0]? = some c) (hc1 : c.1 = h) (hcr : ∀ p < 2 ^ h, c.2.2 p = List.replicate 18 0 ++ row p) :
    HoldsW (semXIR I (expIR h base buf) s).M buf h 6 (Lvm6.Whir.wordE true 0 6 h cs) := by
  have H := expIR_holds I s hM hb hb2 hbuf hbuf2 hsz hdis row hrow
  intro p u
  rw [H p u, Lvm6.Whir.wordE, hc]
  dsimp only
  rw [hc1, Nat.mod_eq_of_lt p.2, hcr p p.2]

end Lvm6.X
