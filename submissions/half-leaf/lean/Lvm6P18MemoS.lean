-- New for lvm6 (KDQ, kernel diet): `sched6 P18` as a literal, checked once by the kernel.
import Lvm6Format

/-!
# The `P18` schedule as a literal (KDQ)

The kernel keeps no cache between declarations, so every `decide` whose statement mentions `sched6 P18`
rebuilds the schedule (≈ 2.7 host-s each). `schedP18` is that schedule written out, and **`sched6_P18_eq`** (both in `Lvm6P18Memo` since INT11)
checks it once (`decide +kernel`, ≈ 2 host-s); a `decide` then rewrites with it and evaluates over the literal.

**`Memo.eq_of_beq`** is the generic memo lemma: a list equality from a `List.beq` check. `List.beq` is
`a == b && List.beq as bs`, a tail call for the kernel's reduction, whereas `List.hasDecEq` (the
`DecidableEq` instance) nests one frame per element and overflows the kernel's recursion at a few
thousand entries (`schedP18`'s 1756 entries are still within reach, and `DecidableEq` is the faster check there).

**`Memo.decide_le`**, **`Memo.decide_lt`**, **`Memo.beq_nat`** and **`Memo.beqBy_eq_decide`** turn a check into a
kernel-friendly copy (`Nat.ble`, `Nat.blt`, `Nat.beq`, an element test without `DecidableEq` instances).
-/

set_option autoImplicit false

namespace Lvm6

namespace Memo

/-- **A list memo** from a `List.beq` check (decided by `decide +kernel`). -/
theorem eq_of_beq {α : Type} [BEq α] [LawfulBEq α] {l m : List α} (h : List.beq l m = true) : l = m :=
  LawfulBEq.eq_of_beq h

/-! ### Kernel-friendly Boolean forms

A `decide` over `Nat` comparisons unfolds `Nat.decLe`, `decEq` and `Bool.decEq` before it reaches `Nat.ble`;
the forms below go to the kernel's `Nat.ble`/`Nat.blt`/`Nat.beq` (GMP) directly. A fast copy of a check is
proved equal to the original by rewriting with them, and the kernel decides the copy. -/

theorem decide_le (a b : ℕ) : decide (a ≤ b) = Nat.ble a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]

theorem decide_lt (a b : ℕ) : decide (a < b) = Nat.blt a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

/-- List equality by an element test `f` (a tail call per element, like `List.beq`). -/
def beqBy {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: l, b :: m => f a b && beqBy f l m
  | _, _ => false

/-- **`beqBy f` decides list equality** when `f` decides element equality. -/
theorem beqBy_eq_decide {α : Type} [DecidableEq α] {f : α → α → Bool} (hf : ∀ a b, f a b = true ↔ a = b) :
    ∀ l m : List α, beqBy f l m = decide (l = m)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: m => by
    rw [beqBy, beqBy_eq_decide hf l m, Bool.eq_iff_iff, Bool.and_eq_true, hf, decide_eq_true_iff,
      decide_eq_true_iff, List.cons.injEq]

end Memo

end Lvm6
