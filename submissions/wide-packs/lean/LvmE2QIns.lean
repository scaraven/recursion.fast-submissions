-- New for lvm2 E2F (slice S1, E2F-Q): `E2` twin instructions in QA1's template language (`LvmQSumcheckCore`),
-- the base the front gadgets are ported on.
import LvmQSumcheckCore
import LvmE2QFieldCorrect

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmE2QInsOff`, outside its import closure.)

/-!
# `E2` templates

An `E2` operand of a template is a pair of sources `(re, im)` (`S2`); `e2I f xs` is the twin pair of
instructions `e2 f false`, `e2 f true` on them (`LvmLoopIR`). On any fixed point of a template (`Fix`):

* **`e2I_val`**: the twin pair at position `n` holds the `E2` value of `f` at its operands' values;
* `mul2I a b d = a·b + d`, `lin2I k k' a b = a + k·b + k'` (`k ∈ K`, `k' ∈ E2`), `add2I`;
* **`horner2`**: a Horner chain `acc ↦ acc·x + c` in `E2` (the sumcheck round's evaluation at a challenge),
  `horner2_val`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- An `E2` operand: the sources of its two `K` coordinates. -/
abbrev S2 := Src × Src

/-- The value of an `E2` operand on a template's values. -/
def S2.val (xv : Src → FE) (vs : List FE) (s : S2) : FE2 := ⟨(s.1.val xv vs).c₀, (s.2.val xv vs).c₀⟩

/-- The `K` operands of `E2` operands (`re`, `im` each). -/
def s2Args (xs : List S2) : List Src := xs.flatMap fun p ↦ [p.1, p.2]

/-- **The twin pair** of `f` on `xs`. -/
def e2I (f : E2Fn) (xs : List S2) : List Ins :=
  [⟨.e2 f false, .K, s2Args xs⟩, ⟨.e2 f true, .K, s2Args xs⟩]

/-- The `E2` value a twin pair at position `n` holds: its two cells. -/
def twinVal (V : List FE) (n : Nat) : FE2 := ⟨(V.getD n 0).c₀, (V.getD (n + 1) 0).c₀⟩

/-- **A twin pair's value** on a fixed point. -/
theorem e2I_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat} {f : E2Fn}
    {xs : List S2} (hseg : Seg ins n (e2I f xs)) (hlen : n + 2 ≤ ins.length) :
    twinVal V n = f.val fun o ↦ ((s2Args xs).getD o default |>.val xv V).c₀ := by
  have h0 := fix_at hF (n := n) (by omega) (i := ⟨.e2 f false, .K, s2Args xs⟩)
    (by have := hseg 0 (by simp [e2I]); simpa [e2I] using this) (by simp)
  have h1 := fix_at hF (n := n + 1) (by omega) (i := ⟨.e2 f true, .K, s2Args xs⟩)
    (by have := hseg 1 (by simp [e2I]); simpa [e2I] using this) (by simp)
  apply FE2.ext_coord
  · simp only [twinVal, FE2.coord_false]; rw [h0]; rfl
  · simp only [twinVal, FE2.coord_true]; rw [h1]; rfl

/-- `a·b + d` in `E2`. -/
def mul2I (a b d : S2) : List Ins := e2I .mul [a, b, d]

/-- `a + k·b + k'` in `E2` (`k ∈ K`, `k' ∈ E2`). -/
def lin2I (k : FK) (k' : FE2) (a b : S2) : List Ins := e2I (.lin k k'.re k'.im) [a, b]

theorem mul2I_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat} {a b d : S2}
    (hseg : Seg ins n (mul2I a b d)) (hlen : n + 2 ≤ ins.length) :
    twinVal V n = a.val xv V * b.val xv V + d.val xv V :=
  e2I_val hF hseg hlen

/-- The twin pair at `n` as an operand of a later instruction. -/
def locS2 (n : Nat) : S2 := (.loc n, .loc (n + 1))

theorem locS2_val (xv : Src → FE) (V : List FE) (n : Nat) : (locS2 n).val xv V = twinVal V n := rfl

/-- **A Horner chain in `E2`** from position `n`: `acc ↦ acc·x + c` for each coefficient `c`, starting at `h`. -/
def horner2 (x : S2) : Nat → S2 → List S2 → List Ins
  | _, _, [] => []
  | n, h, c :: cs => mul2I h x c ++ horner2 x (n + 2) (locS2 n) cs

end Lvm.Q1
