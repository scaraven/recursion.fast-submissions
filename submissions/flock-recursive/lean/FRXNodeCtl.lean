-- G6: `FRXNode`'s controls (`NodeControls`), moved here verbatim from `FRXNode` to keep them off `Solution`'s
-- import closure (stage G6); `FR` imports this module.
import FRXSpec
import FRXFlagCtl

namespace FR.X

open RecursionFast FR FR.Snd FR.Merkle
variable {c : Digest} {π : Proof} {L : Log}

/-! ## Controls -/

namespace NodeControls

open FlagControls

/-- Output the words at `as` (scratch registers `210`, `211`). -/
def outWords : List ℕ → XIR
  | [] => .blk []
  | a :: as => .seq (.blk [.const 210 (toWord a)]) (.seq (.load 211 210) (.seq (.out 211) (outWords as)))

/-- `finIR` on a toy tape: one K element from tape words `tw … tw + 3`, then `X[0]`, `Y[0]`. -/
def toyFin (tw : ℕ) : XIR := .seq (finIR 1 tw 260 270) (outWords [260, 261, 270, 271])

/-- **`finIR` reads at `tw`** (positive) **and nowhere else** (negative: from `tw = 1` the element
is shifted by a word): on the tape `[0, 0, 7, 8, 9, 10]`, `f₀ = (7, 8)` to `X`, `f₁ = (9, 10)` to
`Y`. -/
theorem toyFin_run : (toProg 300 0 (toyFin 2)).run [0, 0, 7, 8, 9, 10] 400 = some [7, 8, 9, 10] ∧
    (toProg 300 0 (toyFin 1)).run [0, 0, 7, 8, 9, 10] 400 = some [0, 7, 8, 9] := by
  decide +kernel

/-- **`gathIR` pairs rows `2x`, `2x + 1`** (one column, `k = 1`, row `r` at `256 + 2r`;
positive: `X[0]` is row 0, `Y[0]` row 1, `X[1]` row 2; negative: when rows 1 and 2 differ, `X[1]`
is not row 1). Stated from `gathIR_sem` on every state: a concrete kernel run costs ≈ 185 ms per
machine operation on a 296-cell memory (S-H2k Part 20), 20 s for this toy. -/
theorem toyGath_ctl (I : Array Word) (s : St) (hM : Inv s.M) (hs : 320 ≤ s.M.size) :
    rdF (semXIR I (gathIR 1 256 288 304) s).M 288 = rdF s.M 256 ∧
    rdF (semXIR I (gathIR 1 256 288 304) s).M 304 = rdF s.M 258 ∧
    rdF (semXIR I (gathIR 1 256 288 304) s).M 290 = rdF s.M 260 ∧
    (rdF s.M 258 ≠ rdF s.M 260 → rdF (semXIR I (gathIR 1 256 288 304) s).M 290 ≠ rdF s.M 258) := by
  have := gathIR_sem I s hM (k := 1) (ob := 256) (xb := 288) (yb := 304) (by norm_num)
    (by simp [regs]) (by norm_num) (by simp [regs]) (by norm_num) (by simp [regs]) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  generalize semXIR I (gathIR 1 256 288 304) s = s' at this ⊢
  obtain ⟨h, -, -⟩ := this
  have h0 := h 0 (by norm_num); have h1 := (h 1 (by norm_num)).1
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mod, Nat.zero_div, Nat.mul_one] at h0 h1
  norm_num at h0 h1
  exact ⟨h0.1, h0.2, h1, fun hne => h1 ▸ hne.symm⟩

/-- **`MsgOk` is not trivial** (negative): the empty step does not lay out a nonzero message
over a zero `X` row. -/
theorem msgOk_empty_neg (I : Array Word) (s : St) (hM : Inv s.M) (h0 : rdF s.M xbM = 0) :
    ¬ MsgOk I (.blk []) s 0 0 (fun _ => 1) := by
  intro h
  have := ((h s hM rfl fun _ _ _ => rfl).1 0 (by norm_num)).1
  rw [if_pos (by norm_num), Nat.mul_zero, Nat.add_zero] at this
  have e : semXIR I (.blk []) s = s := rfl
  rw [e, h0] at this
  exact absurd this (by decide)

/-- A toy proof: `b` zero bytes, then the byte `1`. -/
def toyPi (b : ℕ) : Proof := ⟨(Array.replicate b 0).push 1⟩

theorem byteAt_toyPi (b j : ℕ) : byteAt (toyPi b) j = if j = b then 1 else 0 := by
  unfold byteAt toyPi
  have hs : ({ data := (Array.replicate b (0 : UInt8)).push 1 } : ByteArray).size = b + 1 := by
    simp [ByteArray.size]
  by_cases h : j < b + 1
  · rw [dif_pos (hs ▸ h)]
    show ((Array.replicate b (0 : UInt8)).push 1)[j]'(by simpa using h) = _
    rw [Array.getElem_push]
    by_cases hj : j = b
    · subst hj; simp
    · rw [dif_pos (by simp; omega), if_neg hj]; simp
  · rw [dif_neg (by omega), if_neg (by omega)]

/-- **`finPi` reads π's final field** (positive: a `1` at `finOff` is read, element `0` is
nonzero) **at `finOff`** (negative: a `1` at `finOff − 1` is not read). The toy proofs are
reduced to their 32 read bytes by `byteAt_toyPi`, so the kernel never builds the 64 kB proof. -/
theorem finPi_toy : finPi (toyPi finOff) 0 ≠ 0 ∧ finPi (toyPi (finOff - 1)) 0 = 0 := by
  have e : ∀ b, finPi (toyPi b) 0 = chK (Vector.ofFn fun i : Fin 32 =>
      if finOff + i.1 = b then (1 : UInt8) else 0) := fun b => by
    simp only [finPi, bytesAt, byteAt_toyPi, Nat.mul_zero, Nat.add_zero]
  rw [e, e]
  constructor
  · simp only [Nat.add_eq_left]; decide +kernel
  · simp only [show ∀ i : ℕ, ¬ finOff + i = finOff - 1 from fun i => by simp only [finOff]; omega,
      if_false]; decide +kernel

/-- **`KeepR`** holds on the basis table, the chain and level 0's word (positive), and not on the
decoded rows of levels 1–4 nor on level 0's rows (negative: the decode writes them). -/
theorem keepR_ctl : KeepR tb0 ∧ KeepR ansB ∧ KeepR colBase ∧ ¬ KeepR obL ∧ ¬ KeepR ob0 := by
  simp only [KeepR, tb0, jb0, ansB, chB, eqB, colBase, obL, ob0]; omega

end NodeControls

end FR.X
