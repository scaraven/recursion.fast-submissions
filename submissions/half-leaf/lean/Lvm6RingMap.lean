-- Ported for lvm6 (WP RS) from leanVM fdb317982 (Apache-2.0) `formal/lean_vm/LeanVM/Protocol/RingFields.lean`,
-- `RingMap.lean` and `RingVerifier.lean`, at season 1's `E2 = Quad K g` (`LvmFieldE2`) instead of leanVM's
-- CompPoly `E`; the `K` facts and the kernel check `g_frob_ne` follow season 1's 4.34.1 port (`LvmRingFidelity`).
import Lvm6RingFrob
import LvmFieldE2Correct
import LvmE2VBaseLemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Ring switching's map, target and weight at `E2`

Annex A of leanVM's specification and `crates/verifier/src/ring_switch.rs` (leanVM `fdb317982`). The
verifier draws `f_0, …, f_7` then `g_0, …, g_7` in `E2 = GF(2^128)` and uses

```text
Ψ(a) = Σ_{b < 8} g_b a^(2^b)                      ring_psi            ringPsi
Φ(a) = Σ_{p < 8} f_p Ψ(a)^(2^(8p))                                    frobPhi 8 f g
c_(8p + b) = f_p g_b^(2^(8p))                      ring_coefficients   ringCoefficients
T = Σ_p f_p (Σ_i z_p^i Ψ(s_i))^(2^(8p))            ring_target         ringTarget
W(r') = Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)         ring_weight         ringWeight
```

with `z_p = x^(2^(64 - 8p))`. The verifier functions transcribe the Rust on lists over any field
`F` (`x` = `GEN`, `polyEvalF` = `poly_eval`), so the same definitions run on `E2` (the specification)
and on season 1's word field `FE2` (the executable twin, `toE2_ringTarget`, `toE2_ringCoefficients`,
`toE2_ringWeight`). Proved at `E2`:

* `ringTarget_eq`: the target is `Σ_i x^i Φ(s_i)`;
* `frobPhi_eq_idxSum`, `ringWeight_ofFn`, `ringWeight_mle`: the weight is
  `Σ_k c_k eq(r^(2^k), r')`, the multilinear extension of `u ↦ Φ(eq(r, u))`;
* `ring_complete`: `Σ_u Φ(eq(r, u)) q(u) = Σ_i x^i Φ(Q̂_i(r))` for a `K`-column `q`;
* `ringSwitch_injective`, `card_ringSwitch_zero_le`, **`card_ringBad_le`**: slice claims `s ≠ z` meet
  the honest value at no more than `2·|E2|^15` of the `|E2|^16` challenge pairs (§A.4).

The `E2` argument for injectivity is leanVM's at its `E = K[y]/(y² + xy + 1)`: `1, ω^(2^k)` is a
`K`-basis of `E2` (`limbs_eq_zero_of_frob`), and the 64 conjugates of `x` are distinct (`g_frob_ne`,
a kernel check on `FK` words).
-/

set_option autoImplicit false

namespace Lvm6.Ring

open LeanVM.Parameters Lvm Lvm.E2V Finset

/-! ## The verifier's computations, over any field -/

section Generic

variable {F : Type} [Field F]

/-- `RING_MAP_WIDTH`: the challenges come in two rows of eight. -/
def ringMapWidth : ℕ := 8

/-- `frobenius_8(value, p)`: `value^(2^(8p))` by `8p` squarings. -/
def frobenius8 (value : F) (p : ℕ) : F :=
  (List.range (ringMapWidth * p)).foldl (fun v _ ↦ v * v) value

/-- `ring_psi(value, g)`: `Σ_b g_b value^(2^b)`. -/
def ringPsi (value : F) (g : List F) : F :=
  (g.foldl (fun (acc : F × F) gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (0, value)).1

/-- `ring_target(s, f, g)` with `GEN = x`: `p` from `7` down, `z` squared eight times before each. -/
def ringTarget (x : F) (s f g : List F) : F :=
  let images := s.map (ringPsi · g)
  ((List.range ringMapWidth).reverse.foldl (fun (acc : F × F) p ↦
    let z := frobenius8 acc.2 1
    (acc.1 + f.getD p 0 * frobenius8 (polyEvalF images z) p, z)) (0, x)).1

/-- `ring_coefficients(f, g)`: `c_(8p + b) = f_p g_b^(2^(8p))`, block `p` after block `p - 1`. -/
def ringCoefficients (f g : List F) : List F :=
  (f.foldl (fun (acc : List F × List F) fp ↦
    (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) ([], g)).1

/-- `ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`. -/
def ringWeight (r rPrime coefficients : List F) : F :=
  (coefficients.foldl (fun (acc : F × List F) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (p : F × F) ↦ product * (1 + p.1 + p.2)) c
    (acc.1 + product, acc.2.map fun value ↦ value * value)) (0, r)).1

/-- `Σ_j c_j G(j)` over the positions of a list. -/
def idxSum : List F → (ℕ → F) → F
  | [], _ => 0
  | c :: cs, G => c * G 0 + idxSum cs fun k ↦ G (k + 1)

/-- `eq(a, b) = Π_n (1 + a_n + b_n)`. -/
def eqP {μ : ℕ} (a b : Fin μ → F) : F := ∏ n, (1 + a n + b n)

/-- The cube point of `u`. -/
def bitV {μ : ℕ} (u : Fin μ → Bool) : Fin μ → F := fun n ↦ if u n then 1 else 0

/-- A point raised coordinatewise to `2^k`. -/
def frobPt {μ : ℕ} (r : Fin μ → F) (k : ℕ) : Fin μ → F := fun n ↦ r n ^ 2 ^ k

end Generic

/-! ## Proof helpers on lists -/

section GenericLemmas

variable {F : Type} [Field F]

theorem idxSum_append (l₁ l₂ : List F) (G : ℕ → F) :
    idxSum (l₁ ++ l₂) G = idxSum l₁ G + idxSum l₂ fun k ↦ G (l₁.length + k) := by
  induction l₁ generalizing G with
  | nil => simp [idxSum]
  | cons c l ih =>
    simp only [List.cons_append, idxSum, ih, List.length_cons, add_assoc]
    congr 3
    funext k
    congr 1
    omega

theorem idxSum_map_mul (c : F) (l : List F) (G : ℕ → F) :
    idxSum (l.map (c * ·)) G = c * idxSum l G := by
  induction l generalizing G with
  | nil => simp [idxSum]
  | cons a l ih => simp only [List.map_cons, idxSum, ih]; ring

theorem idxSum_ofFn {n : ℕ} (v : Fin n → F) (G : ℕ → F) :
    idxSum (List.ofFn v) G = ∑ b : Fin n, v b * G b := by
  induction n generalizing G with
  | zero => simp [idxSum]
  | succ n ih => rw [List.ofFn_succ, idxSum, ih, Fin.sum_univ_succ]; simp

theorem idxSum_eq_sum_range (l : List F) (G : ℕ → F) :
    idxSum l G = ∑ k ∈ range l.length, l.getD k 0 * G k := by
  induction l generalizing G with
  | nil => simp [idxSum]
  | cons c l ih =>
    rw [idxSum, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

private theorem foldl_square (l : List ℕ) (v : F) :
    l.foldl (fun v _ ↦ v * v) v = v ^ 2 ^ l.length := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.length_cons, ← sq, ← pow_mul, pow_succ', mul_comm]

/-- `frobenius_8(value, p) = value^(2^(8p))`. -/
theorem frobenius8_eq (v : F) (p : ℕ) : frobenius8 v p = v ^ 2 ^ (8 * p) := by
  rw [frobenius8, foldl_square, List.length_range]
  rfl

private theorem foldl_psi (g : List F) (a w : F) :
    g.foldl (fun (acc : F × F) gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (a, w) =
      (a + idxSum g (fun b ↦ w ^ 2 ^ b), w ^ 2 ^ g.length) := by
  induction g generalizing a w with
  | nil => simp [idxSum]
  | cons c g ih =>
    rw [List.foldl_cons, ih, idxSum, List.length_cons]
    have h : ∀ k : ℕ, (w * w) ^ 2 ^ k = w ^ 2 ^ (k + 1) := fun k ↦ by
      rw [← sq, ← pow_mul, pow_succ', mul_comm 2]
    simp only [h, pow_zero, pow_one, Prod.mk.injEq, and_true]
    ring

/-- **The inner stage**: `ring_psi(a, g) = Ψ(a)`. -/
theorem ringPsi_ofFn {m : ℕ} (a : F) (g : Fin m → F) : ringPsi a (List.ofFn g) = frobPsi g a := by
  rw [ringPsi, foldl_psi, zero_add, idxSum_ofFn, frobPsi]

/-- The coefficients' weighted sum, block by block. -/
private def blockSum : List F → List F → (ℕ → F) → F
  | [], _, _ => 0
  | fp :: fl, pw, G => fp * idxSum pw G +
      blockSum fl (pw.map (frobenius8 · 1)) fun k ↦ G (pw.length + k)

private theorem idxSum_foldl_coeff (G : ℕ → F) :
    ∀ (fl acc pw : List F),
      idxSum (fl.foldl (fun (acc : List F × List F) fp ↦
        (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (acc, pw)).1 G =
      idxSum acc G + blockSum fl pw fun k ↦ G (acc.length + k)
  | [], acc, pw => by simp [blockSum]
  | fp :: fl, acc, pw => by
    rw [List.foldl_cons]
    dsimp only
    rw [idxSum_foldl_coeff G fl, idxSum_append, idxSum_map_mul, blockSum, List.length_append,
      List.length_map, add_assoc]
    simp only [Nat.add_assoc]

private theorem blockSum_ofFn {m : ℕ} (g : Fin m → F) :
    ∀ (n : ℕ) (f : Fin n → F) (t : ℕ) (G : ℕ → F),
      blockSum (List.ofFn f) (List.ofFn fun b ↦ g b ^ 2 ^ (8 * t)) G =
        ∑ p : Fin n, ∑ b : Fin m, f p * g b ^ 2 ^ (8 * (t + p)) * G (m * p + b)
  | 0, _, _, _ => by simp [blockSum]
  | n + 1, f, t, G => by
    rw [List.ofFn_succ, blockSum, idxSum_ofFn, List.map_ofFn, List.length_ofFn]
    have hrow : ((fun x ↦ frobenius8 x 1) ∘ fun b ↦ g b ^ 2 ^ (8 * t)) =
        fun b ↦ g b ^ 2 ^ (8 * (t + 1)) := by
      funext b
      simp only [Function.comp, frobenius8_eq, ← pow_mul, ← pow_add]
      congr 2
    rw [hrow, blockSum_ofFn g n (fun p ↦ f p.succ) (t + 1), Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, add_zero, mul_zero, zero_add, Fin.val_succ]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b _ ↦ by ring) ?_
    · refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      rw [show t + 1 + (p : ℕ) = t + ((p : ℕ) + 1) by ring,
        show m + (m * (p : ℕ) + b) = m * ((p : ℕ) + 1) + b by ring]

/-- **The coefficients are `Φ`'s**: `Σ_j c_j G(j) = Σ_{p, b} f_p g_b^(2^(8p)) G(8p + b)`. -/
theorem ringCoefficients_idxSum (f g : Fin 8 → F) (G : ℕ → F) :
    idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) G =
      ∑ p : Fin 8, ∑ b : Fin 8, f p * g b ^ 2 ^ (8 * (p : ℕ)) * G (8 * p + b) := by
  rw [ringCoefficients, idxSum_foldl_coeff]
  have hg : List.ofFn g = List.ofFn fun b ↦ g b ^ 2 ^ (8 * 0) := by simp
  rw [hg, blockSum_ofFn g 8 f 0]
  simp [idxSum]

/-- The drawn map's coefficients are sixty-four. -/
theorem length_ringCoefficients (f g : Fin 8 → F) :
    (ringCoefficients (List.ofFn f) (List.ofFn g)).length = 64 := by
  have h : ∀ (fl acc pw : List F), (fl.foldl (fun (acc : List F × List F) fp ↦
      (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (acc, pw)).1.length =
      acc.length + fl.length * pw.length := by
    intro fl
    induction fl with
    | nil => simp
    | cons fp fl ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.length_append, List.length_map, List.length_map,
        List.length_cons]
      ring
  rw [ringCoefficients, h]
  simp

/-- **`Φ` is the Frobenius sum with the verifier's coefficients**: `Φ(a) = Σ_k c_k a^(2^k)`. -/
theorem frobPhi_eq_idxSum [CharP F 2] (f g : Fin 8 → F) (a : F) :
    frobPhi 8 f g a =
      idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) fun k ↦ a ^ 2 ^ k := by
  rw [ringCoefficients_idxSum, frobPhi_eq_sum]

theorem polyEvalF_cons (c : F) (cs : List F) (z : F) :
    polyEvalF (c :: cs) z = polyEvalF cs z * z + c := rfl

/-- `poly_eval` is `Σ_i c_i z^i`. -/
theorem polyEvalF_ofFn {n : ℕ} (c : Fin n → F) (z : F) :
    polyEvalF (List.ofFn c) z = ∑ i : Fin n, c i * z ^ (i : ℕ) := by
  induction n with
  | zero => simp [polyEvalF]
  | succ n ih =>
    rw [List.ofFn_succ, polyEvalF_cons, ih, Fin.sum_univ_succ, Finset.sum_mul]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [add_comm]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- The weight's inner fold is its start times the zipped product. -/
private theorem foldl_zip_prod (c : F) : ∀ (r y : List F),
    (List.zip r y).foldl (fun product (p : F × F) ↦ product * (1 + p.1 + p.2)) c =
      c * (List.zipWith (fun x z ↦ 1 + x + z) r y).prod
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: r, b :: y => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_prod _ r y, List.zipWith_cons_cons,
      List.prod_cons]
    ring

/-- The zipped product at two points of `μ` coordinates is `eqP`. -/
theorem zipWith_prod_ofFn {μ : ℕ} (a b : Fin μ → F) :
    (List.zipWith (fun x z ↦ 1 + x + z) (List.ofFn a) (List.ofFn b)).prod = eqP a b := by
  rw [eqP, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- `eq_eval` (season 1's `eqEvalF`) at two points of `μ` coordinates is `eqP`. -/
theorem eqEvalF_ofFn {μ : ℕ} (a b : Fin μ → F) :
    eqEvalF (List.ofFn a) (List.ofFn b) = eqP a b := by
  rw [eqEvalF, ← List.prod_eq_foldl, zipWith_prod_ofFn]

/-- The weight's outer fold from any start. -/
private theorem ringWeight_fold (y : List F) :
    ∀ (cs : List F) (a : F) (r : List F),
      (cs.foldl (fun (acc : F × List F) c ↦
        ((acc.1 + (List.zip acc.2 y).foldl (fun product (p : F × F) ↦
          product * (1 + p.1 + p.2)) c), acc.2.map fun value ↦ value * value)) (a, r)).1 =
        a + idxSum cs fun k ↦ (List.zipWith (fun x z ↦ 1 + x + z) (r.map (· ^ 2 ^ k)) y).prod
  | [], a, r => by simp [idxSum]
  | c :: cs, a, r => by
    rw [List.foldl_cons]
    dsimp only
    rw [ringWeight_fold y cs, foldl_zip_prod, idxSum]
    have e : ((fun x : F ↦ x ^ 2 ^ 0) = id) := by funext x; simp
    have e' : ∀ k : ℕ, ((fun x : F ↦ x ^ 2 ^ k) ∘ fun value ↦ value * value) =
        fun x ↦ x ^ 2 ^ (k + 1) := fun k ↦ by
      funext x
      simp only [Function.comp]
      rw [← sq, ← pow_mul, pow_succ 2 k, mul_comm]
    simp only [List.map_map, e, List.map_id, e']
    ring

/-- **The verifier's weight** at points of `μ` coordinates is `Σ_k c_k eq(r^(2^k), r')`. -/
theorem ringWeight_ofFn {μ : ℕ} (r r' : Fin μ → F) (cs : List F) :
    ringWeight (List.ofFn r) (List.ofFn r') cs = idxSum cs fun k ↦ eqP (frobPt r k) r' := by
  rw [ringWeight, ringWeight_fold, zero_add]
  congr 1
  funext k
  rw [List.map_ofFn, ← zipWith_prod_ofFn]
  rfl

private theorem bit_frob (b : Bool) (k : ℕ) :
    (if b then (1 : F) else 0) ^ 2 ^ k = if b then 1 else 0 := by
  cases b <;> simp

variable [CharP F 2]

/-- **The Frobenius passes through `eq` at a cube point**: `eq(r, u)^(2^k) = eq(r^(2^k), u)`. -/
theorem eqP_frob {μ : ℕ} (r : Fin μ → F) (u : Fin μ → Bool) (k : ℕ) :
    eqP r (bitV u) ^ 2 ^ k = eqP (frobPt r k) (bitV u) := by
  simp only [eqP, ← Finset.prod_pow, add_pow_char_pow, one_pow, frobPt, bitV, bit_frob]

/-- The weight on the cube: `Φ(eq(r, u)) = Σ_k c_k eq(r^(2^k), u)`. -/
theorem frobPhi_eqP {μ : ℕ} (f g : Fin 8 → F) (r : Fin μ → F) (u : Fin μ → Bool) :
    frobPhi 8 f g (eqP r (bitV u)) =
      idxSum (ringCoefficients (List.ofFn f) (List.ofFn g)) fun k ↦ eqP (frobPt r k) (bitV u) := by
  rw [frobPhi_eq_idxSum]
  simp only [eqP_frob]

/-- **`eq` is its own multilinear extension**: `Σ_u eq(a, u) eq(u, b) = eq(a, b)`. -/
theorem sum_eqP_mul_eqP {μ : ℕ} (a b : Fin μ → F) :
    ∑ u : Fin μ → Bool, eqP a (bitV u) * eqP (bitV u) b = eqP a b := by
  simp only [eqP, bitV, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun n (x : Bool) ↦
    (1 + a n + if x then 1 else 0) * (1 + (if x then 1 else 0) + b n))]
  refine Finset.prod_congr rfl fun n _ ↦ ?_
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, add_zero]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (a n * b n + a n + b n + 2) * h2

/-- **The ring weight is the extension of `u ↦ Φ(eq(r, u))`**: at `r'` it is
`Σ_k c_k eq(r^(2^k), r')`, what `ring_weight` computes. -/
theorem ringWeight_mle {μ : ℕ} (f g : Fin 8 → F) (r r' : Fin μ → F) :
    ∑ u : Fin μ → Bool, frobPhi 8 f g (eqP r (bitV u)) * eqP (bitV u) r' =
      ringWeight (List.ofFn r) (List.ofFn r') (ringCoefficients (List.ofFn f) (List.ofFn g)) := by
  rw [ringWeight_ofFn]
  simp only [frobPhi_eqP, idxSum_eq_sum_range, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [mul_assoc, ← Finset.mul_sum, sum_eqP_mul_eqP]

end GenericLemmas

/-! ## `E2` -/

section E2

/-- `K` inside `E2`. -/
abbrev ofK2 (a : K) : E2 := algebraMap K E2 a

theorem ofK2_pow (a : K) (n : ℕ) : ofK2 (a ^ n) = ofK2 a ^ n := map_pow _ a n
theorem ofK2_mul (a b : K) : ofK2 (a * b) = ofK2 a * ofK2 b := map_mul _ a b
theorem ofK2_sum {ι : Type} (s : Finset ι) (f : ι → K) :
    ofK2 (∑ i ∈ s, f i) = ∑ i ∈ s, ofK2 (f i) := map_sum _ f s

/-- `GEN = x` in `E2`. -/
def genE2 : E2 := ofK2 g

/-- The packing weights `x^i`, `i < 64`, in `E2`. -/
def ringW (i : Fin 64) : E2 := ofK2 (g ^ i.val)

/-- Bit `i` of a word, in `E2`. -/
def bitOf (a : K) (i : Fin 64) : E2 := if a.toBitVec.getLsbD i then 1 else 0

/-- Slice `i` of a `K`-column `q`, extended at `r`: `Q̂_i(r) = Σ_u eq(r, u) Q_i(u)`. -/
def sliceExt {μ : ℕ} (q : (Fin μ → Bool) → K) (r : Fin μ → E2) (i : Fin 64) : E2 :=
  ∑ u : Fin μ → Bool, eqP r (bitV u) * bitOf (q u) i

/-- A cell of `K` is its bits packed by the powers of `x`: `a = Σ_{i < 64} a_i · x^i`. -/
theorem K.eq_sum_bits (a : K) :
    a = ∑ i : Fin 64, if a.toBitVec.getLsbD i then g ^ (i : ℕ) else 0 := by
  apply BF64.toQuot_injective
  have hg : BF64.toQuot g = AdjoinRoot.root BF64.basePoly := by
    rw [BF64.toQuot, BF64.toPolyBF64, g, K.ofBits, BF64.toBitVec_ofBitVec,
      show BitVec.ofNat 64 2 = (1 <<< 1 : BitVec 64) by decide,
      BinaryField.toPoly_one_shiftLeft 1 (by norm_num), pow_one, AdjoinRoot.mk_X]
  have hsum : ∀ (s : Finset (Fin 64)) (f : Fin 64 → K),
      BF64.toQuot (∑ i ∈ s, f i) = ∑ i ∈ s, BF64.toQuot (f i) := fun s f ↦ by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BF64.toQuot_add, ih]
  rw [hsum]
  conv_lhs => rw [BF64.toQuot, BF64.toPolyBF64, BinaryField.toPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [BitVec.getLsb, BitVec.getLsbD]
  split
  · rw [map_pow, AdjoinRoot.mk_X, BF64.toQuot_npow, hg]
  · rw [map_zero, BF64.toQuot_zero]

/-- Every `a : K` satisfies `a ^ 2 ^ 64 = a`. -/
theorem K.pow_two_pow_sixtyFour (a : K) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h

/-- In characteristic two, `x^(2^a) = x^(2^b)` with `a ≤ b` gives `x^(2^(b-a)) = x`. -/
private theorem frob_cancel {R : Type*} [CommRing R] [IsReduced R] [ExpChar R 2] (x : R)
    {a b : ℕ} (hab : a ≤ b) (h : x ^ 2 ^ a = x ^ 2 ^ b) : x ^ 2 ^ (b - a) = x := by
  apply iterateFrobenius_inj R 2 a
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab]
  exact h.symm

/-- The Frobenius `x ↦ x^(2^m)` of a weighted sum of powers. -/
private theorem frob_sum {R : Type*} [CommRing R] [ExpChar R 2] {n : ℕ} (x : R) (v : Fin n → R)
    (m : ℕ) :
    (∑ i : Fin n, x ^ i.val * v i) ^ 2 ^ m = ∑ i : Fin n, (x ^ 2 ^ m) ^ i.val * v i ^ 2 ^ m := by
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, pow_right_comm x i.val (2 ^ m)]

/-- None of the `n` squarings after `x` is `t` (one pass along `x², x⁴, …`). -/
private def sqChain {R : Type} [Mul R] [DecidableEq R] (t : R) : ℕ → R → Bool
  | 0, _ => true
  | n + 1, x => !decide (x * x = t) && sqChain t n (x * x)

private theorem sqChain_spec {R : Type} [Mul R] [DecidableEq R] (t : R) : ∀ (n : ℕ) (x : R),
    sqChain t n x = true → ∀ e < n, (fun a : R ↦ a * a)^[e + 1] x ≠ t
  | 0, _, _, e, he => absurd he (Nat.not_lt_zero e)
  | n + 1, x, h, e, he => by
    simp only [sqChain, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    cases e with
    | zero => exact h.1
    | succ e =>
      rw [Function.iterate_succ_apply]
      exact sqChain_spec t n (x * x) h.2 e (by omega)

private theorem toBF64_sq_iterate (n : ℕ) (a : FK) :
    FK.toBF64 ((fun b : FK ↦ b * b)^[n] a) = (fun b : K ↦ b * b)^[n] (FK.toBF64 a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', FK.toBF64_mul, ih]

/-- Kernel check: `x^(2^d) ≠ x` for `0 < d < 64`, along one chain of 63 squarings on `FK` words. -/
private theorem g_frob_ne : ∀ d : Fin 64, d.val ≠ 0 → g ^ 2 ^ d.val ≠ g := by
  have h : ∀ n : ℕ, g ^ 2 ^ n = (fun a : K ↦ a * a)^[n] g := fun n ↦ by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ, pow_mul, sq]
  have hx : FK.toBF64 FK.x = g := by decide
  have hc : sqChain FK.x 63 FK.x = true := by decide +kernel
  intro d hd
  obtain ⟨e, he⟩ : ∃ e, d.val = e + 1 := ⟨d.val - 1, by omega⟩
  rw [h, he, ← hx, ← toBF64_sq_iterate]
  exact fun hq ↦ sqChain_spec _ 63 _ hc e (by omega) (FK.toBF64_injective hq)

/-- The 64 conjugates `x^(2^m)`, `m < 64`, of `x = g` are distinct. -/
theorem g_conj_injective : Function.Injective fun m : Fin 64 ↦ g ^ 2 ^ m.val := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with hlt | hlt
  · exact g_frob_ne ⟨b.val - a.val, by omega⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab)
  · exact g_frob_ne ⟨a.val - b.val, by omega⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab.symm)

/-- A family of `K` whose sums `Σ_i x^i · d_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem eq_zero_of_frob_sums_K (d : Fin 64 → K)
    (h : ∀ k < 64, ∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ k = 0) : ∀ i, d i = 0 := by
  have hroot : ∀ m : Fin 64, ∑ i : Fin 64, (g ^ 2 ^ m.val) ^ i.val * d i = 0 := by
    intro m
    by_cases hm : m.val = 0
    · simpa [hm] using h 0 (by norm_num)
    · have hk : (∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ (64 - m.val)) ^ 2 ^ m.val = 0 := by
        rw [h _ (by omega), zero_pow (pow_ne_zero _ two_ne_zero)]
      rw [frob_sum] at hk
      rw [← hk]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← pow_mul (d i), ← pow_add, Nat.sub_add_cancel (by omega), K.pow_two_pow_sixtyFour]
  exact congrFun (Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero g_conj_injective hroot)

/-- The generator `ω` of `E2` over `K`. -/
abbrev omegaE2 : E2 := QuadraticAlgebra.omega

/-- `ω ∉ K`. -/
theorem omega_ne_ofK2 (a : K) : omegaE2 ≠ ofK2 a := by
  intro h
  have h1 := congrArg QuadraticAlgebra.im h
  change (QuadraticAlgebra.omega : E2).im = (QuadraticAlgebra.C a : E2).im at h1
  simp at h1

/-- `ω^(2^k) ∉ K`: the Frobenius maps `K` onto itself and is injective on `E2`. -/
theorem omega_frob_ne_ofK2 (k : ℕ) (a : K) : omegaE2 ^ 2 ^ k ≠ ofK2 a := by
  intro h
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp (iterateFrobenius_inj K 2 k)) a
  rw [iterateFrobenius_def] at hc
  rw [← hc, ofK2_pow] at h
  exact omega_ne_ofK2 c (iterateFrobenius_inj E2 2 k (by simpa only [iterateFrobenius_def] using h))

/-- `1, ω^(2^k)` are `K`-independent in `E2`. -/
theorem limbs_eq_zero_of_frob (k : ℕ) (a b : K) (h : ofK2 a + ofK2 b * omegaE2 ^ 2 ^ k = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨(algebraMap K E2).injective ?_, rfl⟩
    simpa using h
  · refine absurd ?_ (omega_frob_ne_ofK2 k (-a * b⁻¹))
    have hb' : ofK2 b ≠ 0 := fun h0 ↦ hb ((algebraMap K E2).injective (h0.trans (map_zero _).symm))
    simp only [ofK2, map_mul, map_neg, map_inv₀] at hb' h ⊢
    field_simp
    linear_combination h

/-- An element of `E2` is `re + im·ω`. -/
theorem eq_re_add_im (x : E2) : x = ofK2 x.re + ofK2 x.im * omegaE2 := by
  change x = QuadraticAlgebra.C x.re + QuadraticAlgebra.C x.im * QuadraticAlgebra.omega
  ext <;> simp

/-- The Frobenius `x ↦ x^(2^k)` on the coordinates. -/
theorem frob_limbs (x : E2) (k : ℕ) :
    x ^ 2 ^ k = ofK2 (x.re ^ 2 ^ k) + ofK2 (x.im ^ 2 ^ k) * omegaE2 ^ 2 ^ k := by
  conv_lhs => rw [eq_re_add_im x]
  rw [add_pow_char_pow, mul_pow, ofK2_pow, ofK2_pow]

/-- **Ring-switching injectivity** (Annex A, §A.3): a family of `E2` whose sums
`Σ_i x^i · δ_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem ringSwitch_injective (δ : Fin 64 → E2)
    (h : ∀ k < 64, ∑ i : Fin 64, ringW i * δ i ^ 2 ^ k = 0) : ∀ i, δ i = 0 := by
  have hsplit : ∀ k < 64, (∑ i : Fin 64, g ^ i.val * (δ i).re ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).im ^ 2 ^ k) = 0 := by
    intro k hk
    apply limbs_eq_zero_of_frob k
    have e : ∀ i : Fin 64, ringW i * δ i ^ 2 ^ k =
        ofK2 (g ^ i.val * (δ i).re ^ 2 ^ k) + ofK2 (g ^ i.val * (δ i).im ^ 2 ^ k) * omegaE2 ^ 2 ^ k := by
      intro i
      rw [frob_limbs (δ i) k, ofK2_mul, ofK2_mul, ringW, ofK2_pow]
      ring
    rw [← h k hk, Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib,
      ← Finset.sum_mul, ofK2_sum, ofK2_sum]
  have ha := eq_zero_of_frob_sums_K (fun i ↦ (δ i).re) fun k hk ↦ (hsplit k hk).1
  have hb := eq_zero_of_frob_sums_K (fun i ↦ (δ i).im) fun k hk ↦ (hsplit k hk).2
  intro i
  exact QuadraticAlgebra.ext (ha i) (hb i)

/-- A nonzero error family leaves a nonzero pairing `π_{8p + b}`, `p, b < 8`. -/
theorem exists_frobPair_ne {δ : Fin 64 → E2} (hδ : δ ≠ 0) :
    ∃ p : Fin 8, ∃ b : Fin 8, frobPair univ ringW δ (8 * p + b) ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  refine hδ (funext (ringSwitch_injective δ fun k hk ↦ ?_))
  have h := hall ⟨k / 8, by omega⟩ ⟨k % 8, by omega⟩
  rwa [frobPair, show 8 * (k / 8) + k % 8 = k from Nat.div_add_mod k 8] at h

/-- **Ring switching's soundness, counting form** (§A.4): for a nonzero error family `δ`, the drawn
map cancels `Σ_i x^i Φ(δ_i)` at no more than `2·|E2|^15` of the challenges `(f, g)`. -/
theorem card_ringSwitch_zero_le {δ : Fin 64 → E2} (hδ : δ ≠ 0) :
    (univ.filter fun fg : (Fin 8 → E2) × (Fin 8 → E2) ↦
      ∑ i, ringW i * frobPhi 8 fg.1 fg.2 (δ i) = 0).card ≤ 2 * (2 ^ 128) ^ 15 := by
  have h := card_frobPhi_zero_le univ ringW δ 8 (exists_frobPair_ne hδ)
  rwa [card_E2] at h

/-- `x^(2^64) = x` in `E2`. -/
theorem genE2_pow_two_pow_sixtyFour : genE2 ^ 2 ^ 64 = genE2 := by
  rw [genE2, ← ofK2_pow, K.pow_two_pow_sixtyFour]

/-- The target's fold, `p` from `k - 1` down to `0`, starting at `z = x^(2^(8(8 - k)))`. -/
private theorem foldl_target (images f : List E2) :
    ∀ k ≤ 8, ∀ acc : E2,
      ((List.range k).reverse.foldl (fun (acc : E2 × E2) p ↦
        let z := frobenius8 acc.2 1
        (acc.1 + f.getD p 0 * frobenius8 (polyEvalF images z) p, z))
        (acc, genE2 ^ 2 ^ (8 * (8 - k)))).1 =
      acc + ∑ p ∈ range k, f.getD p 0 * polyEvalF images (genE2 ^ 2 ^ (8 * (8 - p))) ^ 2 ^ (8 * p)
  | 0, _, acc => by simp
  | k + 1, hk, acc => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    have hz : frobenius8 (genE2 ^ 2 ^ (8 * (8 - (k + 1)))) 1 = genE2 ^ 2 ^ (8 * (8 - k)) := by
      rw [frobenius8_eq, ← pow_mul, ← pow_add]
      congr 2
      omega
    simp only [hz]
    rw [foldl_target images f k (by omega), Finset.sum_range_succ, frobenius8_eq]
    ring

/-- The `p`-th Horner sum raised to `2^(8p)` is `Σ_i x^i Ψ_i^(2^(8p))`. -/
private theorem horner_frob (ψ : Fin 64 → E2) {p : ℕ} (hp : p < 8) :
    polyEvalF (List.ofFn ψ) (genE2 ^ 2 ^ (8 * (8 - p))) ^ 2 ^ (8 * p) =
      ∑ i : Fin 64, ringW i * ψ i ^ 2 ^ (8 * p) := by
  rw [polyEvalF_ofFn, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hexp : 2 ^ (8 * (8 - p)) * ((i : ℕ) * 2 ^ (8 * p)) = 2 ^ 64 * (i : ℕ) := by
    rw [mul_comm (i : ℕ), ← mul_assoc, ← pow_add, show 8 * (8 - p) + 8 * p = 64 by omega]
  rw [mul_pow, ← pow_mul (genE2 ^ 2 ^ (8 * (8 - p))) (i : ℕ) (2 ^ (8 * p)),
    ← pow_mul genE2 (2 ^ (8 * (8 - p))) ((i : ℕ) * 2 ^ (8 * p)), hexp, pow_mul genE2 (2 ^ 64) (i : ℕ),
    genE2_pow_two_pow_sixtyFour, mul_comm, ringW, ofK2_pow]
  rfl

/-- **The target is `Σ_i x^i Φ(s_i)`** (§A.6): the verifier's Horner sums at `z_p = x^(2^(64 - 8p))`. -/
theorem ringTarget_eq (s : Fin 64 → E2) (f g : Fin 8 → E2) :
    ringTarget genE2 (List.ofFn s) (List.ofFn f) (List.ofFn g) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (s i) := by
  have h := foldl_target ((List.ofFn s).map (ringPsi · (List.ofFn g))) (List.ofFn f) 8 le_rfl 0
  rw [show 8 * (8 - 8) = 0 from rfl, pow_zero, pow_one] at h
  rw [ringTarget, ringMapWidth, h, zero_add, List.map_ofFn, Finset.sum_range]
  simp only [frobPhi, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hf : (List.ofFn f).getD p 0 = f p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [p.isLt]
  rw [horner_frob _ p.isLt, Finset.mul_sum, hf]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply, ringPsi_ofFn]
  ring

/-- A word of `K` in `E2` is its bits packed by the powers of `x`. -/
theorem ofK2_eq_sum_bitOf (a : K) : ofK2 a = ∑ i : Fin 64, ringW i * bitOf a i := by
  conv_lhs => rw [K.eq_sum_bits a]
  rw [ofK2_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold ringW bitOf
  split <;> simp

/-- An `F_2`-linear map commutes with a bit. -/
private theorem frobPhi_mul_bit (f g : Fin 8 → E2) (e : E2) (b : Bool) :
    frobPhi 8 f g (e * if b then 1 else 0) = (if b then 1 else 0) * frobPhi 8 f g e := by
  cases b <;> simp [frobPhi_zero]

/-- **Completeness** (`eq:complete`): for a column `q(u) = Σ_i Q_i(u) x^i`,
`Σ_u Φ(eq(r, u)) q(u) = Σ_i x^i Φ(Q̂_i(r))`. -/
theorem ring_complete {μ : ℕ} (f g : Fin 8 → E2) (q : (Fin μ → Bool) → K) (r : Fin μ → E2) :
    ∑ u : Fin μ → Bool, frobPhi 8 f g (eqP r (bitV u)) * ofK2 (q u) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (sliceExt q r i) := by
  simp only [ofK2_eq_sum_bitOf, Finset.mul_sum, sliceExt, frobPhi_sum, bitOf, frobPhi_mul_bit]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun u _ ↦ by ring

/-- The target at claims `s` against the honest value: the gap is `Σ_i x^i Φ(s_i - z_i)`. -/
theorem ringTarget_sub (s z : Fin 64 → E2) (f g : Fin 8 → E2) :
    ringTarget genE2 (List.ofFn s) (List.ofFn f) (List.ofFn g) -
        ∑ i : Fin 64, ringW i * frobPhi 8 f g (z i) =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (s i - z i) := by
  rw [ringTarget_eq, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [frobPhi_sub]; ring

/-- **Soundness** (§A.4, leanVM's `card_ringBad_le` at `E2`): slice claims `s ≠ z` meet the honest
value `Σ_i x^i Φ(z_i)` at no more than `2·|E2|^15` of the challenge pairs `(f, g)`. -/
theorem card_ringBad_le {s z : Fin 64 → E2} (h : s ≠ z) :
    (Finset.univ.filter fun fg : (Fin 8 → E2) × (Fin 8 → E2) ↦
      ringTarget genE2 (List.ofFn s) (List.ofFn fg.1) (List.ofFn fg.2) =
        ∑ i, ringW i * frobPhi 8 fg.1 fg.2 (z i)).card ≤ 2 * (2 ^ 128) ^ 15 := by
  have hδ : (fun i ↦ s i - z i) ≠ 0 := fun h0 ↦
    h (funext fun i ↦ sub_eq_zero.mp (congrFun h0 i))
  refine le_trans (Finset.card_le_card fun fg hfg ↦ ?_) (card_ringSwitch_zero_le hδ)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfg ⊢
  rw [← ringTarget_sub, hfg, sub_self]

end E2

/-! ## The executable twin over `FE2` -/

section Twin

variable {F F' : Type} [Field F] [Field F'] (φ : F →+* F')

private theorem map_frobenius8 (v : F) (p : ℕ) : φ (frobenius8 v p) = frobenius8 (φ v) p := by
  rw [frobenius8_eq, frobenius8_eq, map_pow]

private theorem map_ringPsi (v : F) (g : List F) : φ (ringPsi v g) = ringPsi (φ v) (g.map φ) := by
  have h : ∀ (g : List F) (a w : F),
      (fun p : F × F ↦ (φ p.1, φ p.2))
        (g.foldl (fun (acc : F × F) gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (a, w)) =
      (g.map φ).foldl (fun (acc : F' × F') gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (φ a, φ w) := by
    intro g
    induction g with
    | nil => intro a w; rfl
    | cons c g ih =>
      intro a w
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, map_add, map_mul, map_mul]
  have := congrArg Prod.fst (h g 0 v)
  simpa [ringPsi] using this

private theorem map_polyEvalF (l : List F) (z : F) :
    φ (polyEvalF l z) = polyEvalF (l.map φ) (φ z) := by
  induction l with
  | nil => simp [polyEvalF]
  | cons c l ih => rw [polyEvalF_cons, List.map_cons, polyEvalF_cons, map_add, map_mul, ih]

/-- The verifier's target commutes with a field map. -/
theorem map_ringTarget (x : F) (s f g : List F) :
    φ (ringTarget x s f g) = ringTarget (φ x) (s.map φ) (f.map φ) (g.map φ) := by
  have h : ∀ (ps : List ℕ) (a z : F),
      (fun p : F × F ↦ (φ p.1, φ p.2)) (ps.foldl (fun (acc : F × F) p ↦
        let z := frobenius8 acc.2 1
        (acc.1 + f.getD p 0 * frobenius8 (polyEvalF (s.map (ringPsi · g)) z) p, z)) (a, z)) =
      ps.foldl (fun (acc : F' × F') p ↦
        let z := frobenius8 acc.2 1
        (acc.1 + (f.map φ).getD p 0 *
          frobenius8 (polyEvalF ((s.map φ).map (ringPsi · (g.map φ))) z) p, z)) (φ a, φ z) := by
    intro ps
    induction ps with
    | nil => intro a z; rfl
    | cons p ps ih =>
      intro a z
      rw [List.foldl_cons, ih, List.foldl_cons]
      congr 2
      · have hgd : (f.map φ).getD p 0 = φ (f.getD p 0) := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
          cases f[p]? <;> simp
        rw [map_add, map_mul, map_frobenius8, map_polyEvalF, map_frobenius8, List.map_map,
          List.map_map, hgd]
        congr 4
        exact List.map_congr_left fun v _ ↦ by simp [map_ringPsi]
      · exact map_frobenius8 φ z 1
  have := congrArg Prod.fst (h (List.range ringMapWidth).reverse 0 x)
  simpa [ringTarget] using this

/-- The verifier's coefficients commute with a field map. -/
theorem map_ringCoefficients (f g : List F) :
    (ringCoefficients f g).map φ = ringCoefficients (f.map φ) (g.map φ) := by
  have h : ∀ (fl acc pw : List F),
      ((fl.foldl (fun (acc : List F × List F) fp ↦
        (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (acc, pw)).1).map φ =
      ((fl.map φ).foldl (fun (acc : List F' × List F') fp ↦
        (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (acc.map φ, pw.map φ)).1 := by
    intro fl
    induction fl with
    | nil => intro acc pw; rfl
    | cons fp fl ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
      simp [List.map_append, List.map_map, Function.comp_def, map_frobenius8]
  exact h f [] g

/-- The verifier's weight commutes with a field map. -/
theorem map_ringWeight (r r' cs : List F) :
    φ (ringWeight r r' cs) = ringWeight (r.map φ) (r'.map φ) (cs.map φ) := by
  have hz : ∀ (r : List F) (c : F),
      φ ((List.zip r r').foldl (fun product (p : F × F) ↦ product * (1 + p.1 + p.2)) c) =
      (List.zip (r.map φ) (r'.map φ)).foldl
        (fun product (p : F' × F') ↦ product * (1 + p.1 + p.2)) (φ c) := by
    intro r c
    rw [foldl_zip_prod, foldl_zip_prod, map_mul, map_list_prod, List.map_zipWith,
      List.zipWith_map]
    simp only [map_add, map_one]
  have h : ∀ (cs : List F) (a : F) (r : List F),
      φ ((cs.foldl (fun (acc : F × List F) c ↦
        let product := (List.zip acc.2 r').foldl
          (fun product (p : F × F) ↦ product * (1 + p.1 + p.2)) c
        (acc.1 + product, acc.2.map fun value ↦ value * value)) (a, r)).1) =
      ((cs.map φ).foldl (fun (acc : F' × List F') c ↦
        let product := (List.zip acc.2 (r'.map φ)).foldl
          (fun product (p : F' × F') ↦ product * (1 + p.1 + p.2)) c
        (acc.1 + product, acc.2.map fun value ↦ value * value)) (φ a, r.map φ)).1 := by
    intro cs
    induction cs with
    | nil => intro a r; rfl
    | cons c cs ih =>
      intro a r
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
      dsimp only
      rw [map_add, hz, List.map_map, List.map_map]
      simp [Function.comp_def]
  simpa [ringWeight] using h cs 0 r

/-- **The twin's target** (`FE2` words, `GEN = FK.x`) is the specification's. -/
theorem toE2_ringTarget (s f g : List FE2) :
    FE2.toE2 (ringTarget (FE2.ofK FK.x) s f g) =
      ringTarget genE2 (s.map FE2.toE2) (f.map FE2.toE2) (g.map FE2.toE2) := by
  rw [show (FE2.toE2 : FE2 → E2) = ⇑FE2.ringEquivE2 from rfl]
  have := map_ringTarget FE2.ringEquivE2.toRingHom (FE2.ofK FK.x) s f g
  have hx : FE2.toE2 (FE2.ofK FK.x) = genE2 := by
    rw [FE2.toE2_ofK]
    rfl
  simpa [hx] using this

/-- **The twin's coefficients** are the specification's. -/
theorem toE2_ringCoefficients (f g : List FE2) :
    (ringCoefficients f g).map FE2.toE2 =
      ringCoefficients (f.map FE2.toE2) (g.map FE2.toE2) := by
  rw [show (FE2.toE2 : FE2 → E2) = ⇑FE2.ringEquivE2 from rfl]
  have := map_ringCoefficients FE2.ringEquivE2.toRingHom f g
  simpa using this

/-- **The twin's weight** is the specification's. -/
theorem toE2_ringWeight (r r' cs : List FE2) :
    FE2.toE2 (ringWeight r r' cs) =
      ringWeight (r.map FE2.toE2) (r'.map FE2.toE2) (cs.map FE2.toE2) := by
  rw [show (FE2.toE2 : FE2 → E2) = ⇑FE2.ringEquivE2 from rfl]
  have := map_ringWeight FE2.ringEquivE2.toRingHom r r' cs
  simpa using this

end Twin

end Lvm6.Ring
