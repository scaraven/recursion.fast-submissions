-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/RingFidelity.lean` (formal rev 40f877dc) as `LvmRingFidelity` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.RingFidelity

  The algebra of the program's ring switching on `q_keccak`: its staged map, its weight and its
  target, and the pairing of its claim with a stack, given where the layout places `q_keccak`.
-/
import LvmKeccakCandidate
import LvmLayoutStack
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import LvmEqLemmas
import LvmPolyLE
import LvmVCore
import LvmFieldFacts
import LvmProtoField
import LvmFieldKCorrect
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Vandermonde

-- ===== merged from `LvmFrobeniusMap` (GOLF module merge: `LvmFrobeniusMap.lean` is now a stub importing `LvmRingFidelity`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/FrobeniusMap.lean` (formal rev 40f877dc) as `LvmFrobeniusMap` for lvm (WP-2).
/-
  LeanVM.Protocol.ToArkLib.FrobeniusMap

  The staged additive map of Frobenius-map ring switching: a composition of stages
  `a ↦ a + f · a ^ 2 ^ s`, its expansion as a sum of Frobenius powers, its additivity, and the
  stage-by-stage bound that one challenge cancels a nonzero family at one value at most.
  Candidate for ArkLib.
-/

/-!
# The staged Frobenius map

In a commutative ring of characteristic two, `a ↦ a + f · a ^ 2 ^ s` is additive, and so is any
composition of such stages. `frobMap st a` applies the stages of the list `st`, a stage being a
shift `s` and a coefficient `f`, in order. Ring switching from `GF(2)` to a field `E` draws the
coefficients as challenges: the composed map is a random `GF(2)`-linear map cheap to apply.

* `frobMap_eq_sum`: the map is the Frobenius sum `Σ_{(c, e)} c · a ^ 2 ^ e` over the terms
  `frobTerms st`, two terms per term of the later stages; with `m` stages there are `2 ^ m`.
* `frobMapHom`: the map as an additive homomorphism, so it commutes with sums and differences.
* `frobPair_stage`, `card_stage_zero_le_one`: for weights `w` and a family `b`, write
  `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`. One stage with shift `M` sends `π_k` to
  `π_k + f ^ 2 ^ k · π_{M + k}`, so a family with some `π_k ≠ 0`, `k < 2M`, keeps some
  `π_k ≠ 0`, `k < M`, for every coefficient `f` but at most one: `a + f ^ 2 ^ k · b = 0` with
  `(a, b) ≠ (0, 0)` has at most one root, the Frobenius being injective.

The declarations live in `LeanVM.Protocol.Ring`; ring switching on `q_keccak`
(`EndToEnd/Front/RingSwitch.lean`) uses them. Nothing here transcribes a source.
-/

namespace LeanVM.Protocol.Ring

section

variable {R : Type*} [CommRing R]

/-! ## The map and its terms -/

/-- The staged map: each stage `(s, f)` sends `a` to `a + f · a ^ 2 ^ s`, in order. -/
def frobMap : List (ℕ × R) → R → R
  | [], a => a
  | (s, f) :: st, a => frobMap st (a + f * a ^ 2 ^ s)

/-- The terms `(c, e)` of the staged map as a sum of Frobenius powers `c · a ^ 2 ^ e`. -/
def frobTerms : List (ℕ × R) → List (R × ℕ)
  | [] => [(1, 0)]
  | (s, f) :: st => (frobTerms st).flatMap fun t ↦ [(t.1, t.2), (t.1 * f ^ 2 ^ t.2, s + t.2)]

variable [CharP R 2]

/-- The staged map is the sum of its terms: `frobMap st a = Σ_{(c, e)} c · a ^ 2 ^ e`. -/
theorem frobMap_eq_sum (st : List (ℕ × R)) (a : R) :
    frobMap st a = ((frobTerms st).map fun t ↦ t.1 * a ^ 2 ^ t.2).sum := by
  induction st generalizing a with
  | nil => simp [frobMap, frobTerms]
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    rw [frobMap, ih, frobTerms]
    generalize frobTerms st = L
    induction L with
    | nil => simp
    | cons t L ihL =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil, add_zero, ihL]
      rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
      ring

omit [CharP R 2] in
/-- Stages in sequence: the later list applies after the earlier. -/
theorem frobMap_append (st₁ st₂ : List (ℕ × R)) (a : R) :
    frobMap (st₁ ++ st₂) a = frobMap st₂ (frobMap st₁ a) := by
  induction st₁ generalizing a with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    exact ih _

/-- The staged map is additive. -/
theorem frobMap_add (st : List (ℕ × R)) (a b : R) :
    frobMap st (a + b) = frobMap st a + frobMap st b := by
  induction st generalizing a b with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [← ih, add_pow_char_pow]
    congr 1
    ring

omit [CharP R 2] in
/-- The staged map sends `0` to `0`. -/
theorem frobMap_zero (st : List (ℕ × R)) : frobMap st 0 = 0 := by
  induction st with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, add_zero, ih]

/-- The staged map as an additive homomorphism. -/
def frobMapHom (st : List (ℕ × R)) : R →+ R where
  toFun := frobMap st
  map_zero' := frobMap_zero st
  map_add' := frobMap_add st

/-! ## One stage on a family -/

/-- `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`. -/
def frobPair {ι : Type*} (s : Finset ι) (w b : ι → R) (k : ℕ) : R :=
  ∑ i ∈ s, w i * b i ^ 2 ^ k

/-- One stage with shift `M` and coefficient `f` sends `π_k` to `π_k + f ^ 2 ^ k · π_{M + k}`. -/
theorem frobPair_stage {ι : Type*} (s : Finset ι) (w b : ι → R) (M : ℕ) (f : R) (k : ℕ) :
    frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k =
      frobPair s w b k + f ^ 2 ^ k * frobPair s w b (M + k) := by
  simp only [frobPair, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
  ring

/-- `a + f ^ 2 ^ k · b = 0` with `(a, b) ≠ (0, 0)` has one root `f` at most, in a field of
characteristic two. -/
theorem card_frob_root_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    (k : ℕ) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun f : F ↦ a + f ^ 2 ^ k * b = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun f₁ h₁ f₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [mul_zero, add_zero] at h₁
    exact hab.elim (· h₁.2) (· rfl)
  have heq : f₁ ^ 2 ^ k = f₂ ^ 2 ^ k :=
    mul_right_cancel₀ hb (add_left_cancel (h₁.2.trans h₂.2.symm))
  exact iterateFrobenius_inj F 2 k heq

/-- **One bad coefficient at most.** If some `π_k`, `k < 2M`, of the family is nonzero, then after
one stage with shift `M` every `π_k`, `k < M`, vanishes for one coefficient at most. -/
theorem card_stage_zero_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    {ι : Type*} (s : Finset ι) (w b : ι → F) (M : ℕ) (h : ∃ k < 2 * M, frobPair s w b k ≠ 0) :
    (Finset.univ.filter fun f : F ↦
      ∀ k < M, frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k = 0).card ≤ 1 := by
  obtain ⟨k₀, hk₀, hne⟩ := h
  -- The index below `M` whose pair of values is nonzero.
  obtain ⟨k, hk, hab⟩ : ∃ k < M, frobPair s w b k ≠ 0 ∨ frobPair s w b (M + k) ≠ 0 := by
    by_cases hlt : k₀ < M
    · exact ⟨k₀, hlt, Or.inl hne⟩
    · refine ⟨k₀ - M, by omega, Or.inr ?_⟩
      rwa [show M + (k₀ - M) = k₀ by omega]
  refine (Finset.card_le_card fun f hf ↦ ?_).trans (card_frob_root_le_one k hab)
  rw [Finset.mem_filter] at hf ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← frobPair_stage]
  exact hf.2 k hk

end
end LeanVM.Protocol.Ring
end
-- ===== end of `LvmFrobeniusMap` =====

-- ===== merged from `LvmGkrLemmas` (GOLF module merge: `LvmGkrLemmas.lean` is now a stub importing `LvmRingFidelity`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Complete/Gkr.lean` (formal rev
-- 40f877dc), lines 55-353 (cube points and extensions, products, layers, one GKR step's algebra)
-- and `prodE_eq` (390-392), as `LvmGkrLemmas` for lvm (WP-2). The honest GKR prover (`GkrInv`,
-- `hStep`, `hLayers`, `hGkr`, `follows_*`) is completeness and is not ported.

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd Finset

section

/-! ## Cube points and extensions -/

/-- The equality weight of two cube points is the indicator of their equality. -/
theorem eqEval_boolPoint_boolPoint : ∀ (m i j : ℕ), i < 2 ^ m → j < 2 ^ m →
    eqEval (boolPoint m i) (boolPoint m j) = if i = j then 1 else 0
  | 0, i, j, hi, hj => by
    obtain rfl : i = 0 := by simpa using hi
    obtain rfl : j = 0 := by simpa using hj
    simp
  | m + 1, i, j, hi, hj => by
    rw [pow_succ] at hi hj
    rw [boolPoint_succ, boolPoint_succ, eqEval_cons,
      eqEval_boolPoint_boolPoint m (i / 2) (j / 2) (by (clear * - hi; omega)) (by (clear * - hj; omega))]
    by_cases hij : i = j
    · subst hij
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
        simp [h, Nat.testBit_zero, one_add_one_E]
    · by_cases hh : i / 2 = j / 2
      · have hb : i % 2 ≠ j % 2 := fun hb ↦ hij (by (clear * - hh hb; omega))
        simp only [hh, ↓reduceIte, mul_one, hij, Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one i with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one j with h2 | h2 <;>
          simp_all [one_add_one_E]
      · simp [hh, hij]

/-- The extension of a table at a cube point is the table's entry. -/
theorem multilinearEval_boolPoint {m : ℕ} {t : List E} (ht : t.length = 2 ^ m) {l : ℕ}
    (hl : l < 2 ^ m) : multilinearEval t (boolPoint m l) = t.getD l 0 := by
  rw [multilinearEval_eq_sum m t _ ht (length_boolPoint m l)]
  rw [sum_congr rfl fun i hi ↦ by
    rw [eqEval_boolPoint_boolPoint m i l (mem_range.mp hi) hl]]
  simp [mem_range.mpr hl]

/-- **Partial evaluation by blocks.** Fixing the first `a` coordinates at `y`: the extension at
`y ++ x` is the extensions at the cube points `j ++ x`, weighted by `eq(j, y)`. -/
theorem multilinearEval_append {a d : ℕ} {t : List E} (ht : t.length = 2 ^ (a + d)) {y x : List E}
    (hy : y.length = a) (hx : x.length = d) :
    multilinearEval t (y ++ x) =
      ∑ j ∈ range (2 ^ a), multilinearEval t (boolPoint a j ++ x) * eqEval (boolPoint a j) y := by
  have hfold : ∀ r : List E, r.length = a →
      multilinearEval t (r ++ x) = multilinearEval (foldAll t r) x := fun r _ ↦ by
    rw [multilinearEval_eq_foldAll, multilinearEval_eq_foldAll, foldAll_append]
  have hlen : ∀ r : List E, r.length = a → (foldAll t r).length = 2 ^ d := fun r hr ↦
    length_foldAll r t d (by rw [hr, ht])
  have hentry : ∀ r : List E, r.length = a → ∀ i ∈ range (2 ^ d),
      (foldAll t r).getD i 0 =
        ∑ j ∈ range (2 ^ a), eqEval (boolPoint a j) r * t.getD (j + 2 ^ a * i) 0 :=
    fun r hr i hi ↦ by
      rw [getD_foldAll r t d i (by rw [hr, ht]) (mem_range.mp hi), hr]
  rw [hfold y hy, multilinearEval_eq_sum d _ x (hlen y hy) hx,
    sum_congr rfl fun i hi ↦ by rw [hentry y hy i hi]]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [hfold _ (length_boolPoint a j),
    multilinearEval_eq_sum d _ x (hlen _ (length_boolPoint a j)) hx, sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [hentry _ (length_boolPoint a j) i hi]
  rw [sum_congr rfl fun j' hj' ↦ by
    rw [eqEval_boolPoint_boolPoint a j' j (mem_range.mp hj') (mem_range.mp hj)]]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', hj, ↓reduceIte]
  rw [eqEval_comm]
  ring

/-! ## Polynomial dependence on one coordinate -/

/-- The equality weight is affine in any one coordinate of its second point. -/
theorem polyLE_eqEval : ∀ (u a v : List E), PolyLE 1 fun X ↦ eqEval a (u ++ X :: v)
  | [], [], v => (PolyLE.const 1 1).congr fun X ↦ by simp
  | [], a₀ :: a, v =>
    ((PolyLE.affine (1 + a₀) 1).mul (PolyLE.const 0 (eqEval a v))).congr fun X ↦ by
      rw [List.nil_append, eqEval_cons]; ring
  | _ :: _, [], v => (PolyLE.const 1 1).congr fun X ↦ by simp
  | u₀ :: u, a₀ :: a, v =>
    ((polyLE_eqEval u a v).const_mul (1 + a₀ + u₀)).congr fun X ↦ by
      rw [List.cons_append, eqEval_cons]

/-- A table's extension is affine in any one coordinate. -/
theorem polyLE_multilinearEval {t : List E} (u v : List E)
    (ht : t.length = 2 ^ (u.length + 1 + v.length)) :
    PolyLE 1 fun X ↦ multilinearEval t (u ++ X :: v) := by
  refine (PolyLE.sum (range (2 ^ (u.length + 1 + v.length))) fun i _ ↦
    (polyLE_eqEval u (boolPoint (u.length + 1 + v.length) i) v).const_mul
      (t.getD i 0)).congr fun X ↦ ?_
  rw [multilinearEval_eq_sum _ t _ ht (by simp; (clear * -; omega))]

/-- A product of polynomial functions, along a list. -/
theorem PolyLE.listProd {ι : Type} {d : ℕ} (F : ι → E → E) :
    ∀ l : List ι, (∀ i ∈ l, PolyLE d (F i)) → PolyLE (l.length * d) fun x ↦ (l.map (F · x)).prod
  | [], _ => (PolyLE.const _ 1).congr fun x ↦ by simp
  | i :: l, h =>
    ((PolyLE.mul (h i (by simp)) (PolyLE.listProd F l fun j hj ↦ h j (by simp [hj]))).mono
      (by rw [List.length_cons]; nlinarith)).congr fun x ↦ by simp

/-! ## The trees -/

/-- Adjacent pairs multiplied: one level up a product tree. -/
def mulPairs : List E → List E
  | a :: b :: t => a * b :: mulPairs t
  | _ => []

/-- The layer `k` levels above the leaves `L`. -/
def up (k : ℕ) (L : List E) : List E := mulPairs^[k] L

theorem length_mulPairs : ∀ t : List E, (mulPairs t).length = t.length / 2
  | [] => rfl
  | [_] => by simp [mulPairs]
  | a :: b :: t => by
    simp only [mulPairs, List.length_cons, length_mulPairs t]
    omega

theorem getD_mulPairs : ∀ (t : List E) (j : ℕ), 2 * j + 1 < t.length →
    (mulPairs t).getD j 0 = t.getD (2 * j) 0 * t.getD (2 * j + 1) 0
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: t, 0, _ => by simp [mulPairs]
  | a :: b :: t, j + 1, h => by
    simp only [mulPairs, List.getD_cons_succ, List.length_cons] at h ⊢
    rw [getD_mulPairs t j (by omega), show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp

/-- Multiplying adjacent pairs keeps the product of a list of even length. -/
theorem prod_mulPairs : ∀ t : List E, Even t.length → (mulPairs t).prod = t.prod
  | [], _ => rfl
  | [_], h => by simp at h
  | a :: b :: t, h => by
    have ht : Even t.length := by
      simpa [List.length_cons, Nat.even_add_one] using h
    simp only [mulPairs, List.prod_cons, prod_mulPairs t ht, mul_assoc]

theorem up_succ (k : ℕ) (L : List E) : up (k + 1) L = mulPairs (up k L) :=
  Function.iterate_succ_apply' _ _ _

theorem up_add (a b : ℕ) (L : List E) : up (a + b) L = up a (up b L) :=
  Function.iterate_add_apply _ _ _ _

theorem length_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → (up k L).length = 2 ^ m
  | 0, m, L, h => by simpa [up] using h
  | k + 1, m, L, h => by
    rw [up_succ, length_mulPairs, length_up k (m + 1) L (by rw [h]; ring_nf), pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **A node of the tree** is the product of the leaves below it: entry `i` of the layer `k`
levels up is the product of the leaves `j + 2^k·i`. -/
theorem getD_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → ∀ i, i < 2 ^ m →
    (up k L).getD i 0 = ((List.range (2 ^ k)).map fun j ↦ L.getD (j + 2 ^ k * i) 0).prod
  | 0, m, L, _, i, _ => by simp [up]
  | k + 1, m, L, h, i, hi => by
    have hl := length_up k (m + 1) L (by rw [h]; ring_nf)
    rw [up_succ, getD_mulPairs _ i (by rw [hl, pow_succ]; (clear * - hi; omega)),
      getD_up k (m + 1) L (by rw [h]; ring_nf) (2 * i) (by rw [pow_succ]; (clear * - hi; omega)),
      getD_up k (m + 1) L (by rw [h]; ring_nf) (2 * i + 1) (by rw [pow_succ]; (clear * - hi; omega)),
      pow_succ, mul_two, List.range_add, List.map_append, List.prod_append, List.map_map]
    congr 2
    · refine List.map_congr_left fun j _ ↦ ?_
      rw [show j + 2 ^ k * (2 * i) = j + (2 ^ k + 2 ^ k) * i by ring]
    · refine List.map_congr_left fun j _ ↦ ?_
      rw [Function.comp_apply, show j + 2 ^ k * (2 * i + 1) = 2 ^ k + j + (2 ^ k + 2 ^ k) * i by
        ring]

/-- The product of the layers is the product of the leaves. -/
theorem prod_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → (up k L).prod = L.prod
  | 0, _, _, _ => rfl
  | k + 1, m, L, h => by
    have hl := length_up k (m + 1) L (by rw [h]; ring_nf)
    rw [up_succ, prod_mulPairs _ (by rw [hl, pow_succ]; exact ⟨2 ^ m, by ring⟩),
      prod_up k (m + 1) L (by rw [h]; ring_nf)]

/-- The root of a tree is the leaves' product. -/
theorem multilinearEval_up_root {D : ℕ} {L : List E} (h : L.length = 2 ^ D) :
    multilinearEval (up D L) [] = L.prod := by
  have hl := length_up D 0 L (by rw [h, zero_add])
  obtain ⟨a, ha⟩ : ∃ a, up D L = [a] := by
    match hu : up D L, hl with
    | [a], _ => exact ⟨a, rfl⟩
  rw [← prod_up D 0 L (by rw [h, zero_add]), ha]
  simp [multilinearEval]

/-! ## One step -/

/-- The children a step of `step` levels sends of the layer `C`: `C̃(j, x)` for every `j`. -/
def child (C : List E) (step : ℕ) (x : List E) : List E :=
  (List.range (2 ^ step)).map fun j ↦ multilinearEval C (boolPoint step j ++ x)

/-- The children's products, batched in the Horner order of `polyEval`: the step's polynomial
`F(x)`. -/
def stepF (C₀ C₁ C₂ : List E) (step : ℕ) (c : E) (x : List E) : E :=
  polyEval [(child C₀ step x).prod, (child C₁ step x).prod, (child C₂ step x).prod] c

/-- The running claim of the step's sumcheck after the challenges `pre`:
`Σ_b eq(p_{≥|pre|}, b) · F(pre, b)`. -/
def stepClaim (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (pre : List E) : E :=
  ∑ b ∈ range (2 ^ (p.length - pre.length)),
    eqEval (p.drop pre.length) (boolPoint (p.length - pre.length) b) *
      stepF C₀ C₁ C₂ step c (pre ++ boolPoint (p.length - pre.length) b)

/-- The children's extension at `y` is the layer's extension at `y ++ x`. -/
theorem multilinearEval_child {C : List E} {step d : ℕ} (hC : C.length = 2 ^ (step + d))
    {x y : List E} (hx : x.length = d) (hy : y.length = step) :
    multilinearEval (child C step x) y = multilinearEval C (y ++ x) := by
  rw [multilinearEval_append hC hy hx, multilinearEval_eq_sum step _ y (by simp [child]) hy]
  refine sum_congr rfl fun j hj ↦ ?_
  simp [child, List.getD_eq_getElem?_getD, mem_range.mp hj]

/-- A child at a cube point is a node of the layer. -/
theorem child_boolPoint {C : List E} {step d : ℕ} (hC : C.length = 2 ^ (step + d)) {b : ℕ}
    (hb : b < 2 ^ d) :
    child C step (boolPoint d b) =
      (List.range (2 ^ step)).map fun j ↦ C.getD (j + 2 ^ step * b) 0 := by
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' := List.mem_range.mp hj
  rw [← boolPoint_add step d j b hj', multilinearEval_boolPoint hC]
  rw [pow_add]
  exact add_mul_lt hj' hb

/-- **The start of the step.** The batched values of the layers at `p` are the sumcheck's
claim. -/
theorem stepClaim_nil {C₀ C₁ C₂ : List E} {step : ℕ} {p : List E}
    (h₀ : C₀.length = 2 ^ (step + p.length)) (h₁ : C₁.length = 2 ^ (step + p.length))
    (h₂ : C₂.length = 2 ^ (step + p.length)) (c : E) :
    polyEval [multilinearEval (up step C₀) p, multilinearEval (up step C₁) p,
      multilinearEval (up step C₂) p] c = stepClaim C₀ C₁ C₂ step p c [] := by
  have hT : ∀ C : List E, C.length = 2 ^ (step + p.length) →
      multilinearEval (up step C) p =
        ∑ b ∈ range (2 ^ p.length), (child C step (boolPoint p.length b)).prod *
          eqEval (boolPoint p.length b) p := fun C hC ↦ by
    have hl := length_up step p.length C (by rw [hC, add_comm])
    rw [multilinearEval_eq_sum p.length _ p hl rfl]
    refine sum_congr rfl fun b hb ↦ ?_
    rw [getD_up step p.length C (by rw [hC, add_comm]) b (mem_range.mp hb),
      child_boolPoint hC (mem_range.mp hb)]
  rw [hT C₀ h₀, hT C₁ h₁, hT C₂ h₂, polyEval_three, stepClaim]
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.nil_append, stepF,
    polyEval_three, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [eqEval_comm]
  ring

/-- **A round of the step.** The next claims at `0` and `1` split the claim as the equality-mode
round checks it, with the point's coordinate `p_k`. -/
theorem stepClaim_split (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (pre : List E)
    (hk : pre.length < p.length) :
    RoundSplit (some p[pre.length]) (stepClaim C₀ C₁ C₂ step p c pre)
      (stepClaim C₀ C₁ C₂ step p c (pre ++ [0])) (stepClaim C₀ C₁ C₂ step p c (pre ++ [1])) := by
  obtain ⟨m, hm⟩ : ∃ m, p.length - pre.length = m + 1 := ⟨p.length - pre.length - 1, by omega⟩
  have hm' : p.length - (pre.length + 1) = m := by omega
  simp only [RoundSplit, stepClaim, List.length_append, List.length_singleton, hm, hm']
  rw [pow_succ', sum_range_two_mul, List.drop_eq_getElem_cons hk, mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [boolPoint_two_mul, boolPoint_two_mul_add_one, eqEval_cons, eqEval_cons,
    show pre ++ 0 :: boolPoint m j = pre ++ [0] ++ boolPoint m j by simp,
    show pre ++ 1 :: boolPoint m j = pre ++ [1] ++ boolPoint m j by simp]
  linear_combination (-(eqEval (p.drop (pre.length + 1)) (boolPoint m j) *
    stepF C₀ C₁ C₂ step c (pre ++ [1] ++ boolPoint m j))) * two_eq_zero_E

/-- **The degree of a round.** The next claim is a polynomial of degree `2^step` in the next
challenge. -/
theorem stepClaim_polyLE {C₀ C₁ C₂ : List E} {step : ℕ} {p : List E}
    (h₀ : C₀.length = 2 ^ (step + p.length)) (h₁ : C₁.length = 2 ^ (step + p.length))
    (h₂ : C₂.length = 2 ^ (step + p.length)) (c : E) (pre : List E)
    (hk : pre.length < p.length) :
    PolyLE (2 ^ step) fun X ↦ stepClaim C₀ C₁ C₂ step p c (pre ++ [X]) := by
  have hchild : ∀ C : List E, C.length = 2 ^ (step + p.length) → ∀ b : ℕ,
      PolyLE (2 ^ step) fun X ↦
        (child C step (pre ++ [X] ++ boolPoint (p.length - (pre.length + 1)) b)).prod := by
    intro C hC b
    have := PolyLE.listProd (d := 1) (fun j X ↦ multilinearEval C
      ((boolPoint step j ++ pre) ++ X :: boolPoint (p.length - (pre.length + 1)) b))
      (List.range (2 ^ step)) fun j _ ↦ polyLE_multilinearEval _ _ (by
        rw [hC]; simp only [List.length_append, length_boolPoint]; congr 1; (clear * - hk; omega))
    simp only [List.length_range, mul_one] at this
    refine this.congr fun X ↦ ?_
    simp [child]
  have hF : ∀ b, PolyLE (2 ^ step) fun X ↦
      stepF C₀ C₁ C₂ step c (pre ++ [X] ++ boolPoint (p.length - (pre.length + 1)) b) := by
    intro b
    refine (((hchild C₀ h₀ b).add ((hchild C₁ h₁ b).mul (PolyLE.const 0 c))).add
      ((hchild C₂ h₂ b).mul (PolyLE.const 0 (c ^ 2)))).congr fun X ↦ ?_
    simp only [stepF, polyEval_three]
  refine (PolyLE.sum (range (2 ^ (p.length - (pre.length + 1)))) fun b _ ↦
    (hF b).const_mul (eqEval (p.drop (pre.length + 1))
      (boolPoint (p.length - (pre.length + 1)) b))).congr fun X ↦ ?_
  simp only [stepClaim, List.length_append, List.length_singleton]

/-- **The end of the step.** With every coordinate bound, the claim is `F` at the challenges. -/
theorem stepClaim_self (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (x : List E)
    (hx : x.length = p.length) : stepClaim C₀ C₁ C₂ step p c x = stepF C₀ C₁ C₂ step c x := by
  simp [stepClaim, hx]


/-- `prodE` is the product. -/
theorem prodE_eq (l : List E) : prodE l = l.prod := by
  rw [prodE, foldl_mul_eq, one_mul]

end

end LeanVM.Protocol.EndToEnd.Complete
end
-- ===== end of `LvmGkrLemmas` =====

-- ===== merged from `LvmRingFields` (GOLF module merge: `LvmRingFields.lean` is now a stub importing `LvmRingFidelity`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/RingFields.lean` (formal rev 40f877dc) as `LvmRingFields` for lvm (WP-2).
/-
  LeanVM.Protocol.RingFields

  The facts about leanVM's fields that ring switching rests on: a word of `K` is its bits packed
  by the powers of `x`, the Frobenius periods, and the injectivity of ring switching.
-/

/-!
# Field facts for ring switching

Ring switching (`ringSwitch`, `crates/verifier/src/ring_switch.rs:36-54` at leanVM `40f877dc`;
`crates/pcs/src/ring_switch.rs`) packs the `64` bit
slices of `q_keccak` by the powers of `x = g` and draws a random `F_2`-linear map. Its soundness
rests on two facts about `K = GF(2^64)` and `E = K[y]/(y^3 + y + 1)` (`LeanVM.Parameters.Field`):

* `K.eq_sum_bits`: a word of `K` is its bits packed by the powers of `x`,
  `a = Σ_{i < 64} a_i · x^i` (through CompPoly's bridge to `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`).
* **Ring-switching injectivity**, `ringSwitch_injective`: a family `δ : Fin 64 → E` with
  `Σ_i x^i · δ_i^(2^k) = 0` for every `k < 64` is zero. Two steps: `limbs_eq_zero_of_frob`
  (`1, y^(2^k), y^(2^(k+1))` is a `K`-basis of `E`, so each limb family satisfies the same
  equations in `K`) and `eq_zero_of_frob_sums_K` (the polynomial `Σ_i d_i X^i`, of degree below
  64, vanishes at the 64 conjugates `x^(2^m)` of `x = g`, which are distinct by
  `g_conj_injective`, a kernel check on `K` words).

`ringSwitch_injective` needs all 64 twists `k < 64`: `δ ↦ (Σ_i x^i · δ_i^(2^k))_k` is
`F_2`-linear from `E^64`, so fewer than 64 twists cannot make it injective. The declarations live
in `LeanVM.Protocol.Ring`.
-/

namespace LeanVM.Protocol.Ring

open LeanVM.Parameters

section

/-! ## Packing bits into `K` -/

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

/-! ## `ofK` as a ring hom -/

private theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

private theorem ofK_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

/-! ## Frobenius periods -/

/-- Every `a : K` satisfies `a ^ 2 ^ 64 = a`. -/
theorem K.pow_two_pow_sixtyFour (a : K) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h

/-- Every `a : E` satisfies `a ^ 2 ^ 192 = a`. -/
theorem E.pow_two_pow_oneNinetyTwo (a : E) : a ^ 2 ^ 192 = a := by
  have h := FiniteField.pow_card a
  simp only [card_E] at h
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

/-! ## The conjugates of `x` -/

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

private theorem toBF64_sq_iterate (n : ℕ) (a : Lvm.FK) :
    Lvm.FK.toBF64 ((fun b : Lvm.FK ↦ b * b)^[n] a) = (fun b : K ↦ b * b)^[n] (Lvm.FK.toBF64 a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Lvm.FK.toBF64_mul, ih]

/-- Kernel check: `x^(2^d) ≠ x` for `0 < d < 64`. -/
private theorem g_frob_ne : ∀ d : Fin 64, d.val ≠ 0 → g ^ 2 ^ d.val ≠ g := by
  -- `x^(2^d)` as `d` squarings, checked along one chain of 63 squarings (`sqChain`) on the fast
  -- field `Lvm.FK` (its `UInt64` arithmetic costs the kernel about a tenth of `BF64`'s; per-`d`
  -- squarings in `K`: 3.0 s, BS-1's powers: 6.6 s).
  have h : ∀ n : ℕ, g ^ 2 ^ n = (fun a : K ↦ a * a)^[n] g := fun n ↦ by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ, pow_mul, sq]
  have hx : Lvm.FK.toBF64 Lvm.FK.x = g := by decide
  have hc : sqChain Lvm.FK.x 63 Lvm.FK.x = true := by decide +kernel
  intro d hd
  obtain ⟨e, he⟩ : ∃ e, d.val = e + 1 := ⟨d.val - 1, by (clear * - hd; omega)⟩
  rw [h, he, ← hx, ← toBF64_sq_iterate]
  exact fun hq ↦ sqChain_spec _ 63 _ hc e (by (clear * - he; omega)) (Lvm.FK.toBF64_injective hq)

/-- The 64 conjugates `x^(2^m)`, `m < 64`, of `x = g` are distinct. -/
theorem g_conj_injective : Function.Injective fun m : Fin 64 ↦ g ^ 2 ^ m.val := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with hlt | hlt
  · exact g_frob_ne ⟨b.val - a.val, by (clear * - hlt; omega)⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab)
  · exact g_frob_ne ⟨a.val - b.val, by (clear * - hlt; omega)⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab.symm)

/-- A family of `K` whose sums `Σ_i x^i · d_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem eq_zero_of_frob_sums_K (d : Fin 64 → K)
    (h : ∀ k < 64, ∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ k = 0) : ∀ i, d i = 0 := by
  have hroot : ∀ m : Fin 64, ∑ i : Fin 64, (g ^ 2 ^ m.val) ^ i.val * d i = 0 := by
    intro m
    by_cases hm : m.val = 0
    · simpa [hm] using h 0 (by norm_num)
    · have hk : (∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ (64 - m.val)) ^ 2 ^ m.val = 0 := by
        rw [h _ (by (clear * - hm; omega)), zero_pow (pow_ne_zero _ two_ne_zero)]
      rw [frob_sum] at hk
      rw [← hk]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← pow_mul (d i), ← pow_add, Nat.sub_add_cancel (by (clear * -; omega)), K.pow_two_pow_sixtyFour]
  exact congrFun (Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero g_conj_injective hroot)

/-! ## Ring switching -/

/-- `1, y^(2^k), y^(2^(k+1))` are `K`-independent in `E`. -/
theorem limbs_eq_zero_of_frob (k : ℕ) (hk : k < 192) (a b c : K)
    (h : ofK a + ofK b * y ^ 2 ^ k + ofK c * (y ^ 2 ^ k) ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hy : (y ^ 2 ^ k) ^ 2 ^ (192 - k) = y := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.le, E.pow_two_pow_oneNinetyTwo]
  have h' : (ofK a + ofK b * y ^ 2 ^ k + ofK c * (y ^ 2 ^ k) ^ 2) ^ 2 ^ (192 - k) = 0 := by
    rw [h, zero_pow (pow_ne_zero _ two_ne_zero)]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow,
    pow_right_comm (y ^ 2 ^ k) 2 (2 ^ (192 - k)), hy, ← ofK_pow, ← ofK_pow, ← ofK_pow,
    ← ofLimbs_eq] at h'
  have h0 := congrArg (fun z : E ↦ z.limb 0) h'
  have h1 := congrArg (fun z : E ↦ z.limb 1) h'
  have h2 := congrArg (fun z : E ↦ z.limb 2) h'
  simp only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hn : 2 ^ (192 - k) ≠ 0 := pow_ne_zero _ two_ne_zero
  exact ⟨(pow_eq_zero_iff hn).mp h0, (pow_eq_zero_iff hn).mp h1, (pow_eq_zero_iff hn).mp h2⟩

/-- The Frobenius `x ↦ x^(2^k)` on limbs. -/
private theorem frob_limbs (x : E) (k : ℕ) :
    x ^ 2 ^ k = ofK (x.limb 0 ^ 2 ^ k) + ofK (x.limb 1 ^ 2 ^ k) * y ^ 2 ^ k +
      ofK (x.limb 2 ^ 2 ^ k) * (y ^ 2 ^ k) ^ 2 := by
  conv_lhs => rw [E.eq_sum_limbs x]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, pow_right_comm y 2 (2 ^ k),
    ofK_pow, ofK_pow, ofK_pow]

/-- **Ring-switching injectivity** (Annex A, §A.3): a family of `E` whose sums
`Σ_i x^i · δ_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem ringSwitch_injective (δ : Fin 64 → E)
    (h : ∀ k < 64, ∑ i : Fin 64, algebraMap K E (g ^ i.val) * δ i ^ 2 ^ k = 0) :
    ∀ i, δ i = 0 := by
  have hsplit : ∀ k < 64, (∑ i : Fin 64, g ^ i.val * (δ i).limb 0 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 1 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 2 ^ 2 ^ k) = 0 := by
    intro k hk
    apply limbs_eq_zero_of_frob k (by (clear * - hk; omega))
    have e : ∀ i : Fin 64, algebraMap K E (g ^ i.val) * δ i ^ 2 ^ k =
        ofK (g ^ i.val * (δ i).limb 0 ^ 2 ^ k) +
          ofK (g ^ i.val * (δ i).limb 1 ^ 2 ^ k) * y ^ 2 ^ k +
          ofK (g ^ i.val * (δ i).limb 2 ^ 2 ^ k) * (y ^ 2 ^ k) ^ 2 := by
      intro i
      rw [frob_limbs (δ i) k, ofK_mul, ofK_mul, ofK_mul]
      change ofK (g ^ i.val) * _ = _
      ring
    rw [← h k hk, Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ofK_sum, ofK_sum, ofK_sum]
  have ha := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 0) fun k hk ↦ (hsplit k hk).1
  have hb := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 1) fun k hk ↦ (hsplit k hk).2.1
  have hc := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 2) fun k hk ↦ (hsplit k hk).2.2
  intro i
  refine E.ext fun j ↦ ?_
  rw [limb_zero]
  fin_cases j
  exacts [ha i, hb i, hc i]

end
end LeanVM.Protocol.Ring
end
-- ===== end of `LvmRingFields` =====

/-!
# The algebra of ring switching

The program (`ringMapShifts`, `phiMap`, `ringWeight`, `ringCoefficients`, `ringSwitch`,
`crates/verifier/src/ring_switch.rs:8-54` at leanVM `40f877dc`; `crates/pcs/src/ring_switch.rs`)
and its claim on the stack (`ringSwitchClaim`, `crates/verifier/src/lib.rs:303-311`):

* `phiMap_eq_frobMap`: the program's `Φ`, a fold over the coefficients with shifts
  `32, 16, 8, 4, 2, 1`, is the staged map `frobMap (stagesOf ch)` (`ToArkLib/FrobeniusMap.lean`);
  `phiMap_eq_sum`: with six coefficients it is the Frobenius sum `Σ_{k < 64} c_k b^(2^k)` with the
  program's closed-form coefficients `c_k = ringCoefficients ch` (a computation over the six
  coefficients, `frobTerms_stagesOf`);
* `ringWeight_eq_sum`: the program's weight is `Σ_k c_k eq(r^(2^k), ·)`;
* `ringTarget_eq_sum`: the target `poly_eval([Φ(s_i)], GEN)` is `Σ_i x^i Φ(s_i)`;
* `colExt_frob`: the extension of `q_keccak` at `point^(2^k)` is `Σ_i x^i ẑ_i(point)^(2^k)`,
  `ẑ_i` the extension of bit slice `i` (`sliceExt`): a word is its bits packed by the powers of
  `x` (`K.eq_sum_bits`), and the Frobenius fixes bits and raises the equality weights;
* `pair_ringClaim`: where the layout places `q_keccak` on an aligned block of `2^(h + 6)` cells
  (`RingLayoutHyp`), the program's ring claim paired with a stack is `Σ_i x^i Φ(ẑ_i(point))`;
  so (`ringClaim_holds_iff`) the claim holds exactly when `Σ_i x^i Φ(s_i - ẑ_i(point)) = 0`, the
  `k = 0` sum of the ring-switching errors under the drawn map;
* `ringLayoutHyp_verifierLayout`: the verifier's layout places `q_keccak` so.

No mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Ring LeanVM.Protocol.KeccakGkr
open LeanVM.Semantics

section

/-! ## The Frobenius of `E` -/

/-- The Frobenius `b ↦ b^(2^k)` is additive. -/
theorem ring_frob_add (a b : E) (k : ℕ) : (a + b) ^ 2 ^ k = a ^ 2 ^ k + b ^ 2 ^ k :=
  add_pow_char_pow a b 2 k

/-- The Frobenius commutes with finite sums. -/
theorem ring_frob_sum {ι : Type} (s : Finset ι) (f : ι → E) (k : ℕ) :
    (∑ i ∈ s, f i) ^ 2 ^ k = ∑ i ∈ s, f i ^ 2 ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ring_frob_add, ih]

/-- The Frobenius fixes a bit. -/
theorem bitE_frob (b : Bool) (k : ℕ) : bitE b ^ 2 ^ k = bitE b := by
  cases b <;> simp [bitE]

/-- The Frobenius of an equality weight raises the point. -/
theorem eqAt_frob (k : ℕ) : ∀ (pt : List E) (w : ℕ),
    eqAt pt w ^ 2 ^ k = eqAt (pt.map (· ^ 2 ^ k)) w
  | [], _ => by simp
  | r :: rs, w => by
    rw [List.map_cons, eqAt_cons, eqAt_cons, mul_pow, eqAt_frob k rs]
    split_ifs
    · rfl
    · rw [ring_frob_add, one_pow]

/-! ## Folds -/

/-- The program's product over a zipped pair of points is the equality kernel. -/
theorem foldl_zip_eqEval (c : E) : ∀ (r y : List E),
    (List.zip r y).foldl (fun product (p : E × E) ↦ product * (1 + p.1 + p.2)) c =
      c * eqEval r y
  | [], _ => by simp [eqEval]
  | _ :: _, [] => by simp [eqEval]
  | a :: r, b :: y => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_eqEval _ r y,
      Whir.Complete.eqEval_cons]
    ring

/-- The weight fold from any start: the start plus `Σ_k c_k eq(r^(2^k), y)`. -/
theorem ringWeight_fold (y : List E) :
    ∀ (cs : List E) (a : E) (r : List E),
      (cs.foldl (fun (acc : E × List E) c ↦
        ((acc.1 + (List.zip acc.2 y).foldl (fun product (p : E × E) ↦
          product * (1 + p.1 + p.2)) c), acc.2.map (· ^ 2))) (a, r)).1 =
        a + ∑ k ∈ Finset.range cs.length, cs.getD k 0 * eqEval (r.map (· ^ 2 ^ k)) y
  | [], a, r => by simp
  | c :: cs, a, r => by
    rw [List.foldl_cons]
    rw [ringWeight_fold y cs, foldl_zip_eqEval, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, pow_one, List.map_map]
    have e : ∀ k ∈ Finset.range cs.length,
        cs.getD k 0 * eqEval (List.map ((fun x ↦ x ^ 2 ^ k) ∘ fun x ↦ x ^ 2) r) y =
          cs.getD k 0 * eqEval (List.map (fun x ↦ x ^ 2 ^ (k + 1)) r) y := fun k _ ↦ by
      have : ((fun x : E ↦ x ^ 2 ^ k) ∘ fun x ↦ x ^ 2) = fun x ↦ x ^ 2 ^ (k + 1) := by
        funext b
        simp only [Function.comp]
        rw [← pow_mul, pow_succ 2 k, mul_comm]
      rw [this]
    rw [Finset.sum_congr rfl e]
    simp only [List.map_id']
    ring

/-- **The program's weight is `Σ_k c_k eq(r^(2^k), ·)`.** -/
theorem ringWeight_eq_sum (r y cs : List E) :
    ringWeight r y cs =
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 * eqEval (r.map (· ^ 2 ^ k)) y := by
  rw [ringWeight]
  exact (ringWeight_fold y cs 0 r).trans (zero_add _)

/-! ## The staged map -/

/-- The stages of the program's map: shift `ringMapShifts[p]`, coefficient `ch[p]`. -/
def stagesOf (ch : List E) : List (ℕ × E) := (List.zip ch ringMapShifts).map fun p ↦ (p.2, p.1)

/-- **The program's `Φ` is the staged map** of its stages. -/
theorem phiMap_eq_frobMap (a : E) (ch : List E) : phiMap a ch = frobMap (stagesOf ch) a := by
  unfold phiMap stagesOf
  generalize List.zip ch ringMapShifts = l
  induction l generalizing a with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨c, sh⟩ := p
    simp only [List.foldl_cons, List.map_cons, frobMap]
    exact ih _

/-- A zip reads only as much of its left list as its right list is long. -/
theorem zip_append_of_le {α β : Type} :
    ∀ (l r : List α) (l' : List β), l'.length ≤ l.length → List.zip (l ++ r) l' = List.zip l l'
  | _, _, [], _ => by simp
  | [], _, _ :: _, h => by simp at h
  | a :: l, r, b :: l', h => by
    rw [List.cons_append, List.zip_cons_cons, List.zip_cons_cons,
      zip_append_of_le l r l' (by simpa using h)]

/-- **One more coefficient**: below six, the stage with shift `2^(5 - p)` after the others. -/
theorem stagesOf_snoc (acc : List E) (c : E) (h : acc.length < 6) :
    stagesOf (acc ++ [c]) = stagesOf acc ++ [(2 ^ (5 - acc.length), c)] := by
  match acc, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl

/-- Past six coefficients, the stages do not change. -/
theorem stagesOf_snoc_of_le (acc : List E) (c : E) (h : 6 ≤ acc.length) :
    stagesOf (acc ++ [c]) = stagesOf acc := by
  unfold stagesOf
  rw [zip_append_of_le acc [c] ringMapShifts (by simpa [ringMapShifts] using h)]

/-- The program's closed-form coefficients are the Frobenius terms' of its stages: a
computation over six named coefficients. -/
theorem frobTerms_stagesOf (f0 f1 f2 f3 f4 f5 : E) (F : ℕ → E) :
    ((frobTerms (stagesOf [f0, f1, f2, f3, f4, f5])).map fun t ↦ t.1 * F t.2).sum =
      ∑ k ∈ Finset.range 64, (ringCoefficients [f0, f1, f2, f3, f4, f5]).getD k 0 * F k := by
  simp only [ringCoefficients, ringMapShifts, kBits, List.zip_cons_cons, List.zip_nil_right,
    stagesOf]
  simp [frobTerms, Finset.sum_range_succ, List.filter]
  ring

/-- **The staged map is the Frobenius sum with the program's coefficients**:
`Φ(b) = Σ_{k < 64} c_k b^(2^k)`. -/
theorem phiMap_eq_sum {ch : List E} (h : ch.length = 6) (b : E) :
    phiMap b ch = ∑ k ∈ Finset.range 64, (ringCoefficients ch).getD k 0 * b ^ 2 ^ k := by
  rw [phiMap_eq_frobMap, frobMap_eq_sum]
  match ch, h with
  | [f0, f1, f2, f3, f4, f5], _ => exact frobTerms_stagesOf f0 f1 f2 f3 f4 f5 fun k ↦ b ^ 2 ^ k

/-- The program's coefficients are sixty-four. -/
theorem length_ringCoefficients (ch : List E) : (ringCoefficients ch).length = 64 := by
  simp [ringCoefficients, kBits]

/-- The staged map is additive: it sends differences to differences. -/
theorem phiMap_sub (ch : List E) (a b : E) : phiMap (a - b) ch = phiMap a ch - phiMap b ch := by
  simp only [phiMap_eq_frobMap]
  exact map_sub (frobMapHom (stagesOf ch)) a b

/-! ## The target -/

/-- The ring-switching weights `x^i`, `i < 64`, in `E`. -/
def ringW (i : Fin 64) : E := algebraMap K E (g ^ i.val)

/-- **The program's target is `Σ_i x^i Φ(s_i)`** over 64 slices. -/
theorem ringTarget_eq_sum (sv ch : List E) (hsv : sv.length = 64) :
    polyEval (sv.map (phiMap · ch)) gen = ∑ i : Fin 64, ringW i * phiMap (sv.getD i 0) ch := by
  rw [Complete.polyEval_eq_sum, List.length_map, hsv, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp [hsv]), List.getElem_map,
    List.getD_eq_getElem _ _ (by simp [hsv]), ringW, map_pow, mul_comm]
  rfl

/-! ## Slices and the column -/

/-- Bit slice `i` of a word column, extended at `pt` over `2^(h + 6)` words. -/
def sliceExt (h : ℕ) (col : ℕ → K) (pt : List E) (i : ℕ) : E :=
  ∑ n ∈ Finset.range (2 ^ (h + 6)), eqAt pt n * bitE ((col n).toBitVec.getLsbD i)

/-- The word column, extended at `pt` over `2^(h + 6)` words. -/
def colExt (h : ℕ) (col : ℕ → K) (pt : List E) : E :=
  ∑ n ∈ Finset.range (2 ^ (h + 6)), eqAt pt n * ofK (col n)

/-- A word of `K` in `E` is its bits packed by the powers of `x`. -/
theorem ofK_eq_sum_bitE (a : K) : ofK a = ∑ i : Fin 64, ringW i * bitE (a.toBitVec.getLsbD i) := by
  conv_lhs => rw [K.eq_sum_bits a]
  change algebraMap K E _ = _
  rw [map_sum (algebraMap K E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold ringW
  split <;> simp_all [bitE]

/-- **The column at `pt^(2^k)` packs the slices' Frobenius**:
`q̂(pt^(2^k)) = Σ_i x^i ẑ_i(pt)^(2^k)`. -/
theorem colExt_frob (h : ℕ) (col : ℕ → K) (pt : List E) (k : ℕ) :
    colExt h col (pt.map (· ^ 2 ^ k)) = ∑ i : Fin 64, ringW i * sliceExt h col pt i ^ 2 ^ k := by
  simp only [colExt, sliceExt, ring_frob_sum, mul_pow, bitE_frob, eqAt_frob, ofK_eq_sum_bitE,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun n _ ↦ by ring

/-! ## The layout -/

/-- Word `n` of `q_keccak` on a stack of the layout: the stack's cell `n` past `QKECCAK`'s
offset (ported from leanVM `EndToEnd/Front/KeccakLayout.lean:31-32`). -/
def qkOf (layout : Verifier.Layout) (q : Column layout.stackLog) (n : ℕ) : K :=
  q.values.toArray.getD ((layout.placement qkeccak).index + n) 0

/-- Word `n` of the block of a stack at `off`. -/
def qkAt {μ : ℕ} (off : ℕ) (q : Column μ) (n : ℕ) : K := q.values.toArray.getD (off + n) 0

/-- `q_keccak`'s words on a stack of the layout are the block's at its placement. -/
theorem qkOf_eq_qkAt (layout : Verifier.Layout) (q : Column layout.stackLog) :
    qkOf layout q = qkAt (layout.placement qkeccak).index q := rfl

/-- **What ring switching needs of the layout**: `q_keccak` is placed on `h + 6` variables, at an
offset aligned to its size, inside the stack. -/
structure RingLayoutHyp (layout : Verifier.Layout) (h off : ℕ) : Prop where
  /-- `q_keccak`'s placement: `h + 6` variables at `off`. -/
  placement : layout.placement qkeccak = { variableCount := h + 6, index := off }
  /-- The offset is aligned to the block's size. -/
  aligned : 2 ^ (h + 6) ∣ off
  /-- The block lies inside the stack. -/
  fits : off + 2 ^ (h + 6) ≤ 2 ^ layout.stackLog

/-- `eq_eval` against a cube point on as many coordinates is the equality weight `eqAt`. -/
theorem eqEval_boolPoint_eqAt : ∀ (p : List E) (y : ℕ), eqEval p (boolPoint p.length y) = eqAt p y
  | [], _ => by simp [eqEval, boolPoint]
  | r :: p, y => by
    rw [List.length_cons, Whir.Complete.boolPoint_succ, Whir.Complete.eqEval_cons,
      eqEval_boolPoint_eqAt p, eqAt_cons]
    congr 1
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · simp [hy]
    · simp only [hy, decide_true, ↓reduceIte]
      linear_combination CharTwo.add_self_eq_zero (1 : E)

/-- **An aligned placement's weight at a cube point**: the indicator of the block times the
equality weight of the offset inside it. -/
theorem eqAbove_mul_eqEval_boolPoint {v off μ x : ℕ} (hfit : off + 2 ^ v ≤ 2 ^ μ) (hx : x < 2 ^ μ)
    (p : List E) (hp : p.length = v) :
    ({ variableCount := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) =
      if x / 2 ^ v = off / 2 ^ v then eqAt p (x % 2 ^ v) else 0 := by
  have hv : v ≤ μ := by
    have : 2 ^ v ≤ 2 ^ μ := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hpow : 2 ^ μ = 2 ^ v * 2 ^ (μ - v) := by rw [← pow_add, Nat.add_sub_cancel' hv]
  have hoff : off / 2 ^ v < 2 ^ (μ - v) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow]; have := Nat.two_pow_pos v; omega)
  have hxv : x / 2 ^ v < 2 ^ (μ - v) := Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hx)
  simp only [Placement.eqAbove, length_boolPoint, selectorPoint_eq_boolPoint,
    Nat.shiftRight_eq_div_pow, drop_boolPoint]
  rw [Complete.eqEval_boolPoint_boolPoint _ _ _ hoff hxv, take_boolPoint μ v x hv, ← hp,
    ← boolPoint_mod, eqEval_boolPoint_eqAt, hp]
  by_cases h : x / 2 ^ v = off / 2 ^ v
  · simp [h]
  · simp [h, Ne.symm h]

/-- **A sum over the stack weighted by an aligned placement** is the sum over the block. -/
theorem sum_placed {v off μ : ℕ} (hal : 2 ^ v ∣ off) (hfit : off + 2 ^ v ≤ 2 ^ μ) (p : List E)
    (hp : p.length = v) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), ({ variableCount := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) * ofK (q.values.getD x 0) =
      ∑ n ∈ Finset.range (2 ^ v), eqAt p n * ofK (qkAt off q n) := by
  obtain ⟨t, rfl⟩ := hal
  have hpos := Nat.two_pow_pos v
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ ({ variableCount := v, index := 2 ^ v * t } :
      Placement).eqAbove
    (boolPoint μ x) * eqEval p ((boolPoint μ x).take v) * ofK (q.values.getD x 0))]
  have hsub : Finset.Ico (2 ^ v * t) (2 ^ v * t + 2 ^ v) ⊆ Finset.range (2 ^ μ) := fun x hx ↦ by
    simp only [Finset.mem_Ico] at hx
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub fun x hx hn ↦ ?_, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' := Finset.mem_range.mp hn
    rw [eqAbove_mul_eqEval_boolPoint hfit (by omega) p hp,
      Nat.mul_add_div hpos, Nat.div_eq_of_lt hn', add_zero, Nat.mul_div_cancel_left _ hpos]
    simp only [↓reduceIte]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hn', qkAt]
    rfl
  · have hx := Finset.mem_range.mp hx
    rw [eqAbove_mul_eqEval_boolPoint hfit hx p hp, Nat.mul_div_cancel_left _ hpos]
    suffices hne : x / 2 ^ v ≠ t by simp [hne]
    intro he
    refine hn (Finset.mem_Ico.mpr ⟨?_, ?_⟩)
    · rw [← he]; exact Nat.mul_div_le x _
    · have := Nat.lt_mul_div_succ x hpos
      rw [he, mul_add, mul_one] at this
      exact this

/-! ## The ring claim on the stack -/

/-- **The ring claim paired with a stack** (any stack size `μ` the block fits in): with
`q_keccak` placed on `h + 6` variables at an aligned `off`, the pairing of the program's ring
claim is `Σ_i x^i Φ(ẑ_i(point))`. -/
theorem pair_ringClaim {layout : Verifier.Layout} {h off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h + 6, index := off }) (hal : 2 ^ (h +
        6) ∣ off)
    (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) (q : Column μ) {pt ch : List E}
    (hpt : pt.length = h + 6) (hch : ch.length = 6) (target : E) :
    ∑ x : Fin (2 ^ μ), (ringSwitchClaim layout target
        fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)).1 (boolPoint μ x) *
          ofK (q.values.getD x 0) =
      ∑ i : Fin 64, ringW i * phiMap (sliceExt h (qkAt off q) pt i) ch := by
  simp only [ringSwitchClaim, hpl, ringWeight_eq_sum, length_ringCoefficients, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k ∈ Finset.range 64,
      ∑ x : Fin (2 ^ μ), ({ variableCount := h + 6, index := off } : Placement).eqAbove
          (boolPoint μ x) *
          ((ringCoefficients ch).getD k 0 *
            eqEval (pt.map (· ^ 2 ^ k)) ((boolPoint μ x).take (h + 6))) *
          ofK (q.values.getD x 0) =
        (ringCoefficients ch).getD k 0 *
          ∑ i : Fin 64, ringW i * sliceExt h (qkAt off q) pt i ^ 2 ^ k := fun k _ ↦ by
    rw [← colExt_frob, colExt, ← sum_placed hal hfit _ (by rw [List.length_map, hpt]) q,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [Finset.sum_congr rfl e]
  simp only [phiMap_eq_sum hch, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- The error of slice `i`: the claimed value minus the column's slice at the point. -/
def ringErr (h : ℕ) (col : ℕ → K) (pt sv : List E) (i : Fin 64) : E :=
  sv.getD i 0 - sliceExt h col pt i

/-- **The ring claim holds exactly when the errors' twisted sum vanishes**: for the program's
target and weight, the claim on a stack holds iff `Σ_i x^i Φ(s_i - ẑ_i(point)) = 0`. -/
theorem ringClaim_holds_iff {layout : Verifier.Layout} {h off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h + 6, index := off }) (hal : 2 ^ (h +
        6) ∣ off)
    (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) (q : Column μ) {pt sv ch : List E}
    (hpt : pt.length = h + 6) (hsv : sv.length = 64) (hch : ch.length = 6) :
    StackClaim.Holds μ (ringSwitchClaim layout (polyEval (sv.map (phiMap · ch)) gen)
        fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)) q ↔
      ∑ i : Fin 64, ringW i * phiMap (ringErr h (qkAt off q) pt sv i) ch = 0 := by
  unfold StackClaim.Holds
  rw [pair_ringClaim hpl hal hfit q hpt hch, ringTarget_eq_sum sv ch hsv]
  simp only [ringErr, phiMap_sub, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, eq_comm]
  exact Iff.rfl

-- lvm (WP-2): leanVM's `ringLayoutHyp_verifierLayout` (the leanISA layout meets `RingLayoutHyp`,
-- through `KeccakLayout.placement_qkeccak`) is not ported: an instance supplies its own
-- `RingLayoutHyp`.

end
end LeanVM.Protocol.EndToEnd.Front
