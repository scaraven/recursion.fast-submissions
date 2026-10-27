-- New for `flock-recursive` (BLUEPRINT §6.5 `index_spec`; stage S-H2, track L-ext).
import FRXMerge

/-!
# Simulating `stepIR` by `mstep`: word-level building blocks

The flags and the branch-free `min` of `blockIR`/`stepIR`, as `Nat` facts on words below `2^64`
(S-H2-RESULT, Part 5).
-/

namespace FR.X

open RecursionFast

/-- The branch-free `min` of `minPs`: `b ^^^ ((a ^^^ b) &&& (0 - [a < b]))`. -/
theorem minW (a b : Word) :
    b ^^^ ((a ^^^ b) &&& (0 - XOp.ltu.eval a b)) = if a < b then a else b := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    simp only [XOp.eval, h, ↓reduceIte, h1, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · simp only [XOp.eval, h, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

/-- `min` of two small numbers as words. -/
theorem minW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    toWord b ^^^ ((toWord a ^^^ toWord b) &&& (0 - XOp.ltu.eval (toWord a) (toWord b))) =
      toWord (min a b) := by
  rw [minW]
  by_cases h : a < b
  · rw [if_pos ((toWord_lt_toWord ha hb).2 h), Nat.min_eq_left h.le]
  · rw [if_neg (fun h' => h ((toWord_lt_toWord ha hb).1 h')), Nat.min_eq_right (by omega)]

/-- The `eq` flag on small numbers. -/
theorem eqW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.eq.eval (toWord a) (toWord b) = bW (decide (a = b)) := by
  simp only [XOp.eval, bW]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg (fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_toWord ha, toNat_toWord hb] at this))]
    simp [h]

/-- The `ltu` flag on small numbers. -/
theorem ltW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.ltu.eval (toWord a) (toWord b) = bW (decide (a < b)) := by
  simp only [XOp.eval, bW, toWord_lt_toWord ha hb]
  by_cases h : a < b <;> simp [h]

end FR.X
