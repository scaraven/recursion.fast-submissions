-- New for lvm2 roll 11 (M′, R11-X): the NTT programs composed with the basis table, at any dimension `N`.
-- Adapted from `LvmXNtt5.lean` (`wtabIR_nw`, `wtab_bflyIR_coeffs`, `wtab_fwdIR_enc`) at `N` for `15`.
import LvmMPXNtt4

/-!
# The NTT programs at dimension `N` composed with the basis table

* `wtabNIR_nw`: the table program does not touch the row pointer `rA0` or the forward NTT's registers.
* **`wtab_bflyNIR_coeffs`**, **`wtab_fwdNIR_enc`**: `wtabNIR N tb` then `bflyNIR N ℓ tb` (resp. `fwdNIR N ℓ tb`)
  from any state with the row pointer set; the table hypothesis is discharged by `wtabNIR_sem`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

variable {N : ℕ}

/-- The table program writes neither the row pointer nor the forward NTT's registers. -/
theorem wtabNIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf) (N tb : ℕ) :
    ¬ Writes (wtabNIR N tb) r := by
  have hr12 : 12 ≤ r ∧ r ≠ fH ∧ r ≠ fN ∧ r ≠ fAl := by
    rcases hr with rfl | rfl | rfl <;> decide
  have n1 : ¬ Writes (mulK fH fU fW) r := (mulK_writes_iff (by have := hr12.1; omega) hr12.2.1).1
  have n2 : ¬ Writes (mulK fN fH fAl) r :=
    (mulK_writes_iff (by have := hr12.1; omega) hr12.2.2.1).1
  have n3 : ¬ Writes (invK fAl fH) r := (invK_writes_iff hr12.1 hr12.2.2.2).1
  simp only [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1, n2, n3]
  rcases hr with rfl | rfl | rfl <;>
  simp [rA0, rKf, rTbf, rTr, uI, rTa, rN2, rC2, fG, rLv, rN3, rC3, uT1, fU, fW, rAH, cTmp]

/-- **The table, then the inverse NTT**: the row ends holding the novel-basis coefficients of its values. -/
theorem wtab_bflyNIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) (hN1 : 1 ≤ N)
    {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ N) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64) (hszt : tb + N * N ≤ s.M.size)
    (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I (.seq (wtabNIR N tb) (bflyNIR N ℓ tb)) s).M (A + i) =
      coeffsAt ptK N ℓ 0 Y i := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabNIR_sem I s hM hN hN1 htb htb2 hszt
  rw [semXIR_seq]
  refine bflyNIR_coeffs I _ t3 hN hℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 ?_
  · rw [frame I _ s (wf_wtabNIR N tb) hM _ (by decide) (wtabNIR_nw (.inl rfl) N tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The table, then the forward NTT**: on a zero-padded message the row ends holding `Enc`. -/
theorem wtab_fwdNIR_enc (I : Array Word) (s : St) (hM : Inv s.M) (hN : N ≤ 64) (hN1 : 1 ≤ N)
    {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ N) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hszt : tb + N * N ≤ s.M.size) (hdisj : tb + N * N ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A) (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I (.seq (wtabNIR N tb) (fwdNIR N ℓ tb)) s).M (A + j) = encN ptK c j := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabNIR_sem I s hM hN hN1 htb htb2 hszt
  rw [semXIR_seq]
  refine fwdNIR_enc I _ t3 hN hℓ hmℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 c ?_
  · rw [frame I _ s (wf_wtabNIR N tb) hM _ (by decide) (wtabNIR_nw (.inl rfl) N tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

end Lvm.X
