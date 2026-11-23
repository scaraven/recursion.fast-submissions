-- New for lvm2 (T-Q, S2 assembly): the borrow chain for `m = n' − 1`'s bits (HAR-RC's `borrow`, moved
-- unchanged from `LvmQAsmArith2Claim` so that phases 4–5 (`LvmQAsmArith2P47`) can use it for the wire).
import LvmQRingG
import LvmQSigDefs

-- (GOLF2: 3 declarations that `certified` does not use moved verbatim to `LvmQAsmArith2Off`, outside its import closure.)

/-!
# The bits of `n' − 1` (`borrow`)

`borrow nb o n`: the bits `0 … n − 1` of `N − 1` from the bits of `N` at `K` cells `nb + j` (`d_j = b_j + c_j`,
`c_{j+1} = c_j·b_j + c_j`, `c_0 = 1`); **`borrow_vs`**: `vs M cells = (range n).map (bitE (N − 1))`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits

variable {c : Ctx} {M : Mem}

/-! ## The bits of `n − 1` -/

theorem mod_two_pow_succ_eq_zero (n j : Nat) :
    n % 2 ^ (j + 1) = 0 ↔ (n % 2 ^ j = 0 ∧ n.testBit j = false) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> rw [h] <;> simp

theorem testBit_pred (n j : Nat) (hn : 1 ≤ n) :
    (n - 1).testBit j = (n.testBit j ^^ decide (n % 2 ^ j = 0)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdm := Nat.div_add_mod n (2 ^ j)
  have hr := Nat.mod_lt n hP
  generalize n / 2 ^ j = q at hdm
  generalize n % 2 ^ j = r at hdm hr ⊢
  subst hdm
  by_cases h0 : r = 0
  · subst h0
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hn
      · (clear * - h; omega)⟩
    have e : 2 ^ j * (q' + 1) + 0 - 1 = 2 ^ j * q' + (2 ^ j - 1) := by
      rw [Nat.mul_succ]; (clear * - hP; omega)
    rw [e, Nat.mul_add_div hP, Nat.div_eq_of_lt (by (clear * - hP; omega)), Nat.add_zero]
    rcases Nat.mod_two_eq_zero_or_one q' with h | h <;> simp [h, Nat.add_mod]
  · have e : 2 ^ j * q + r - 1 = 2 ^ j * q + (r - 1) := by (clear * - hn h0; omega)
    rw [e, Nat.mul_add_div hP, Nat.div_eq_of_lt (by (clear * - hr; omega)), Nat.add_zero]
    simp [h0]

/-- The value of bit `j` of `N` (`0`/`1`). -/
def bitE (N j : Nat) : FE := if N.testBit j then 1 else 0

/-- The borrow of `N − 1` into bit `j`: `1` iff bits `0 … j − 1` of `N` are zero. -/
def carryE (N j : Nat) : FE := if N % 2 ^ j = 0 then 1 else 0

theorem fe_two : (1 : FE) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem carry_succ (N j : Nat) : carryE N (j + 1) = carryE N j * bitE N j + carryE N j := by
  simp only [carryE, bitE]
  by_cases h1 : N % 2 ^ j = 0 <;> by_cases h2 : N.testBit j = true <;>
    simp [h1, h2, mod_two_pow_succ_eq_zero, fe_two]

theorem pred_bit (N j : Nat) (hN : 1 ≤ N) : bitE (N - 1) j = bitE N j + carryE N j := by
  simp only [bitE, carryE, testBit_pred N j hN]
  by_cases h1 : N % 2 ^ j = 0 <;> by_cases h2 : N.testBit j = true <;> simp [h1, h2, fe_two]

/-- The bits `j, j + 1, …` (`k` of them) of `N − 1` from the bits of `N` at `K` cells `nb + j` and the
borrow `cy` into bit `j`. -/
def borrowGo (nb : Nat) : Nat → Nat → Cell → BM (List Cell)
  | _, 0, _ => pure []
  | j, k + 1, cy => do
    let d ← add (kc (nb + j)) cy
    let cy' ← mad cy (kc (nb + j)) cy
    let ds ← borrowGo nb (j + 1) k cy'
    pure (d :: ds)

/-- **The bits `0 … n − 1` of `N − 1`** (`K` cells) from the bits of `N` at `K` cells `nb + j`. -/
def borrow (nb o n : Nat) : BM (List Cell) :=
  match n with
  | 0 => pure []
  | k + 1 => do
    let d0 ← add (kc nb) (ec o)
    let ds ← borrowGo nb 1 k d0
    pure (d0 :: ds)

theorem mad_out (a b d : Cell) (p : Ptr) :
    (mad a b d p).1 = ⟨jn (jn a.ty b.ty) d.ty, p.at (jn (jn a.ty b.ty) d.ty)⟩ := rfl

theorem add_val {a b : Cell} {p : Ptr} (h : SegsHold c M p (add a b p).2) :
    (add a b p).1.val M = a.val M + b.val M := by
  have := lin_spec h
  rw [ofK_one, one_mul, ofK_zero, add_zero] at this
  exact this

theorem addK_val {a : Cell} {k' : FK} {p : Ptr} (h : SegsHold c M p (addK a k' p).2) :
    (addK a k' p).1.val M = a.val M + FE.ofK k' := by
  have := lin_spec h
  rw [ofK_zero, zero_mul, add_zero] at this
  exact this

theorem mad_val {a b d : Cell} {p : Ptr} (h : SegsHold c M p (mad a b d p).2) :
    (mad a b d p).1.val M = a.val M * b.val M + d.val M := mulAdd_spec h

/-- `selectorPoint` is the list of bits. -/
theorem selectorPoint_bits (N n : Nat) : selectorPoint N n = (List.range n).map (bitE N) := by
  simp only [selectorPoint]
  refine List.map_congr_left fun b _ => ?_
  unfold bitE
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (N >>> b) with h | h <;> simp [h] <;> rfl

end Lvm.Har
