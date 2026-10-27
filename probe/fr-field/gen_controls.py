#!/usr/bin/env python3
"""Write submissions/flock-recursive/lean/FRFieldControls.lean from kat.py's output (kat.out)."""
import sys
L = open(sys.argv[1]).read().split('\n')
def sec(h):
    i = L.index(h); out = []
    for l in L[i + 1:]:
        if l.startswith('--') or not l: break
        out.append(l)
    return out
def split(l):
    parts = []; depth = 0; cur = ''
    for ch in l:
        if ch == '⟨': depth += 1
        if depth > 0: cur += ch
        if ch == '⟩':
            depth -= 1
            if depth == 0: parts.append(cur); cur = ''
    return parts
F = [split(l) for l in sec('-- F pairs (a, b, a*b)')]
Fw = sec('-- F: the first product with beta = x^61 (wrong constant)')[0]
K = [split(l) for l in sec('-- K pairs (a, b, a*b)')]
Kw = sec('-- K: the first product with alpha = y (wrong constant, trace 0)')[0]
om = [l for l in L if l.startswith('-- omega')][0].split()[-1]
katF = ',\n'.join(f"  ({p[0]},\n    {p[1]},\n    {p[2]})" for p in F)
katK = ',\n'.join(f"  ({p[0]},\n    {p[1]},\n    {p[2]})" for p in K)
print(f'''-- New for `flock-recursive` (BLUEPRINT §5.6, row "F, K fields and twins"); the pattern of
-- `submissions/spartan-srom/lean/SpartanSromFieldControls.lean`. The known answers are printed by
-- `probe/fr-field/kat.py` (an independent schoolbook reference in Python, seed 20261027) and this
-- file by `probe/fr-field/gen_controls.py`.
import FRField256

/-!
# Controls for the field layer

Kernel-checked evaluations of the compiled operations, positive and negative. They pin what a wrong
constant would silently change: the constants `β = x^63` and `α = β y`, the Karatsuba and lazy
reduction of `F.mul`, the reduction `u^2 = u + α` of `K.mul`, the inverses and the byte order. The
negative controls show that the trace hypothesis of `quadratic_irreducible` is needed: the
trace-zero constant `1` gives `y^2 + y + 1`, which has a root in `GF(2^64)` and is reducible.
-/

namespace FR.FieldControls

open FR Polynomial

/-! ## Products against the independent reference -/

/-- Eight `F` triples `(a, b, a b)` of the reference (schoolbook product, `y^2 = y + x^63`). -/
def katF : List (F × F × F) := [
{katF}]

/-- **The eight `F` products agree with the reference.** -/
theorem mul_kat_F : katF.map (fun t => t.1 * t.2.1) = katF.map (·.2.2) := by decide +kernel

/-- The reference's first product with the plausible wrong constant `β = x^61`. -/
def wrongF : F := {Fw}

/-- Negative: the first product is not the one with `β = x^61`. -/
theorem mul_kat_F_ne : katF[0]!.1 * katF[0]!.2.1 ≠ wrongF := by decide +kernel

/-- Eight `K` triples `(a, b, a b)` of the reference (`u^2 = u + β y`). -/
def katK : List (K × K × K) := [
{katK}]

/-- **The eight `K` products agree with the reference.** -/
theorem mul_kat_K : katK.map (fun t => t.1 * t.2.1) = katK.map (·.2.2) := by decide +kernel

/-- The reference's first product with the trace-zero constant `α = y`. -/
def wrongK : K :=
  {Kw}

/-- Negative: the first product is not the one with `α = y`. -/
theorem mul_kat_K_ne : katK[0]!.1 * katK[0]!.2.1 ≠ wrongK := by decide +kernel

/-! ## Inverses, squares, generators -/

/-- The inverse of a random `F` element: `a * a⁻¹ = 1` (one `B64` inversion in the kernel). -/
theorem mul_inv_F : katF[0]!.1 * (katF[0]!.1)⁻¹ = 1 := by decide +kernel

/-- The inverse of a random `K` element. -/
theorem mul_inv_K : katK[0]!.1 * (katK[0]!.1)⁻¹ = 1 := by decide +kernel

/-- Squaring is the product on a random `K` element (the `α`-term of `K.sq`). -/
theorem sq_kat_K : K.sq katK[1]!.1 = katK[1]!.1 * katK[1]!.1 := by decide +kernel

/-- Negative: `y^2 ≠ y + x^61`, i.e. the modulus is not `y^2 + y + x^61` (the other trace-1
monomial, the most plausible wrong `β`). -/
theorem y_sq_ne_x61 : F.y * F.y ≠ F.y + F.ofB64 ⟨0x2000000000000000⟩ := by decide +kernel

/-- `0⁻¹ = 0`. -/
theorem inv_zero_F : (0 : F)⁻¹ = 0 := by decide +kernel

/-- Negative: the inverse without the conjugation, `a · (a / norm a)`, is not `1` on a random
element (the conjugate `(c₀ + c₁) + c₁ y` in `F.inv` matters). -/
theorem inv_no_conj_ne :
    katF[0]!.1 * F.smulBase (F.norm katF[0]!.1)⁻¹ katF[0]!.1 ≠ 1 := by decide +kernel

/-! ## Bytes -/

/-- `F` bytes are `c₀`'s eight little-endian bytes, then `c₁`'s. -/
theorem toBytes_F : (F.toBytes ⟨⟨0x0807060504030201⟩, ⟨0x100F0E0D0C0B0A09⟩⟩).toList =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by decide +kernel

/-- Negative: not `c₁` first. -/
theorem toBytes_F_ne : (F.toBytes ⟨⟨0x0807060504030201⟩, ⟨0x100F0E0D0C0B0A09⟩⟩).toList ≠
    [9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel

/-- `K` bytes are `f₀`'s sixteen bytes, then `f₁`'s. -/
theorem toBytes_K : (K.toBytes ⟨⟨⟨0x0807060504030201⟩, ⟨0x100F0E0D0C0B0A09⟩⟩,
    ⟨⟨0x1817161514131211⟩, ⟨0x201F1E1D1C1B1A19⟩⟩⟩).toList =
    (List.range 32).map (fun i => i.toUInt8 + 1) := by
  decide +kernel

/-! ## The trace hypothesis is needed -/

/-- `ω = x^((2^64 - 1)/3)`, a primitive cube root of unity in `GF(2^64)` (printed by `kat.py`). -/
def omega : B64 := ⟨{om}⟩

/-- `ω` is a root of `y^2 + y + 1`, by kernel evaluation. -/
theorem omega_root : omega * omega + omega + 1 = 0 := by decide +kernel

/-- The constant `1` has absolute trace `0` (`64` is even). -/
theorem absTrace_one : absTrace 64 (1 : BF64) = 0 := by
  simp only [absTrace, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [show ((64 : ℕ) : BF64) = 2 * 32 by norm_num, CharTwo.two_eq_zero, zero_mul]

/-- **Negative control for the trace criterion**: with the trace-zero constant `1`, the quadratic
`y^2 + y + 1` has a root and is reducible over `BF64`. -/
theorem not_irreducible_one : ¬ Irreducible (X ^ 2 + X + C 1 : BF64[X]) := by
  intro h
  have hr : IsRoot (X ^ 2 + X + C 1 : BF64[X]) (B64.toBF64 omega) := by
    have := congrArg B64.toBF64 omega_root
    simp only [B64.toBF64_add, B64.toBF64_mul, B64.toBF64_one, B64.toBF64_zero] at this
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C]
    linear_combination this
  have h1 := degree_eq_one_of_irreducible_of_root h hr
  have h2 : (X ^ 2 + X + C 1 : BF64[X]).degree = 2 := by compute_degree!
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- Negative: a modulus with zero constant is reducible (`y = 0` is a root). -/
theorem not_irreducible_zero : ¬ Irreducible (X ^ 2 + X : BF64[X]) := by
  intro h
  have h1 := degree_eq_one_of_irreducible_of_root h (x := 0) (by simp)
  have h2 : (X ^ 2 + X : BF64[X]).degree = 2 := by compute_degree!
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- Positive, for contrast: `y^2 + y + β` is irreducible (`f128_irreducible`), stated on the
polynomial itself. -/
theorem irreducible_beta : Irreducible (X ^ 2 + X + C betaBF : BF64[X]) :=
  f128Params_poly ▸ f128_irreducible

end FR.FieldControls''')
