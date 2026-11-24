-- New for lvm2 S1 (E2-F, E2F-V): the shared base of the verifier's front over a field parameter (E2-G0 §2's
-- "shared base": `LvmVCore`'s `eqEval`/`multilinearEval`/`polyEval`, `LvmPolyLE`'s `PolyLE`/`RoundSplit`,
-- `LvmKeccakRounds`' families), generic in `F`, for the `E2` front. The `E3` originals are untouched.
import LvmE2Grind

/-!
# The front's base over a field `F`

The definitions of `LvmVCore` (Rust `multilinear.rs`, `transcript.rs`) and of the round families
(`LvmKeccakRounds`), with `E` replaced by a field parameter `F` (characteristic two where the
formulas use `1 + x` for `1 − x`, as the Rust does). At `F = E` each is its `E3` original by
unfolding; at `F = E2` they are the `E2` front's.

* lists: `sumF`, `prodF`, `dotF`, `powersF`, `polyEvalF`;
* multilinear: `eqKernelF`, `foldPairsF`, `multilinearEvalF`, `eqEvalF`, `eqAtF`, `selPtF`;
* rounds: `PolyLEF`, `RoundSplitF`, `PlainFamilyF`, `EqFamilyF`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open Polynomial

section

variable {F : Type} [Field F]

/-! ## Lists -/

/-- `F::sum(values)`, from `0`, left to right. -/
def sumF (values : List F) : F := values.foldl (· + ·) 0

/-- The product from `1`, left to right. -/
def prodF (values : List F) : F := values.foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y`. -/
def dotF (left right : List F) : F := (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `acc, acc·base, …`, `count` terms. -/
def powersFromF (acc base : F) : ℕ → List F
  | 0 => []
  | count + 1 => acc :: powersFromF (acc * base) base count

/-- `powers(base, count)`: `1, base, …, base^(count−1)`. -/
def powersF (base : F) (count : ℕ) : List F := powersFromF 1 base count

/-- A polynomial's value from its coefficients, lowest first (Horner). -/
def polyEvalF (coefficients : List F) (point : F) : F :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-! ## Multilinear -/

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit. -/
def eqKernelF (point : List F) : List F :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairsF (r : F) : List F → List F
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairsF r rest
  | _ => []

/-- `multilinear_eval(mle, point)`, the first coordinate folding adjacent entries. -/
def multilinearEvalF (mle point : List F) : F :=
  (point.foldl (fun cur r ↦ foldPairsF r cur) mle).headD 0

/-- `eq_eval(left, right) = Π (1 + x + y)`. -/
def eqEvalF (left right : List F) : F :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `eq(pt, w)` at a cube point given by its index (bit `i` of `w` is coordinate `i`). -/
def eqAtF : List F → ℕ → F
  | [], _ => 1
  | r :: rs, w => (if w % 2 = 1 then r else 1 + r) * eqAtF rs (w / 2)

/-- `selector_point(selector, length)`: the low `length` bits of `selector`, lowest first. -/
def selPtF (selector length : ℕ) : List F :=
  (List.range length).map fun bit ↦ if (selector >>> bit) % 2 = 1 then 1 else 0

/-! ## Round families -/

/-- `f` is a polynomial function of degree at most `d`. -/
def PolyLEF (d : ℕ) (f : F → F) : Prop :=
  ∃ P : F[X], P.natDegree ≤ d ∧ ∀ x, f x = P.eval x

/-- A round's check: `c(0) + c(1) = claim` (plain), `(1 + r)·c(0) + r·c(1) = claim` (equality). -/
def RoundSplitF (mode : Option F) (claim v0 v1 : F) : Prop :=
  match mode with
  | none => v0 + v1 = claim
  | some r => (1 + r) * v0 + r * v1 = claim

/-- A family of plain sumcheck claims valid below `N` challenges (`LvmKeccakRounds.PlainFamily`). -/
def PlainFamilyF {β : Type} (Fm : β → List F → F) (d N : ℕ) : Prop :=
  ∀ q acc, acc.length < N →
    PolyLEF d (fun x ↦ Fm q (acc ++ [x])) ∧ Fm q acc = Fm q (acc ++ [0]) + Fm q (acc ++ [1])

/-- A family of equality-mode claims at the point `r` (`LvmKeccakRounds.EqFamily`). -/
def EqFamilyF {β : Type} (Fm : β → List F → F) (r : List F) (d : ℕ) : Prop :=
  ∀ q acc, (h : acc.length < r.length) →
    PolyLEF d (fun x ↦ Fm q (acc ++ [x])) ∧
      Fm q acc = (1 + r[acc.length]) * Fm q (acc ++ [0]) + r[acc.length] * Fm q (acc ++ [1])

end

end Lvm.E2V
