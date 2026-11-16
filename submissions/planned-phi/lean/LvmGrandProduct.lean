-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/GrandProduct.lean` (formal rev 40f877dc) as `LvmGrandProduct` for lvm (WP-2).
/-
  LeanVM.Protocol.ToArkLib.GrandProduct

  The batched grand-product argument as a typed component: from the roots of several product
  trees to one evaluation claim per tree at one shared point, layer by layer, at the slot
  `Typed.gkrSlot`. Definition and completeness. Candidate for ArkLib.
-/
import LvmSumcheckRound
import LvmCpPowerBatching
import Mathlib.Algebra.Polynomial.BigOperators
import LvmCpMultilinear

-- ===== merged from `LvmCpPartialSum` (GOLF module merge: `LvmCpPartialSum.lean` is now a stub importing `LvmGrandProduct`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/PartialSum.lean` (formal rev 40f877dc) as `LvmCpPartialSum` for lvm (WP-2).
/-
  LeanVM.Protocol.ToCompPoly.PartialSum

  The eq-weighted sum of a function over the cube with its first coordinates fixed: the running
  claim of a sumcheck that binds the lowest variable first. Candidate for CompPoly.
-/

/-!
# Running sums over the cube

For a function `g` on `m` coordinates, a point `r`, and the first `j` coordinates fixed to `c`,
`partialSum g r j c` is `Σ_{x ∈ {0,1}^(m - j)} eq(r_{≥ j}, x) · g(c, x)`: the extension, at the
remaining coordinates of `r`, of the table of `g` on the cube of the remaining coordinates
(`restrictTable`). It is the claim a sumcheck on `Σ_x eq(r, x) g(x)` carries after `j` rounds
when the rounds bind the lowest variable first:

* `partialSum_zero`: with nothing fixed it is the extension of the table of `g` at `r`;
* `partialSum_split`: fixing one more coordinate splits it into the two values at `0` and at `1`,
  weighted by `1 - r_j` and `r_j`;
* `partialSum_self`: with everything fixed it is `g c`.

Over an arbitrary commutative ring. Candidate for CompPoly, beside `CompPoly.Multilinear.Basic`.
Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

variable {R : Type*} [CommRing R]

/-- The point `(c, x)` on `m` coordinates. -/
def fixLow {m j : ℕ} (hj : j ≤ m) (c : Vector R j) (x : Vector R (m - j)) : Vector R m :=
  Vector.cast (Nat.add_sub_cancel' hj) (c ++ x)

/-- The table of `g` on the cube of the last `m - j` coordinates, the first `j` fixed to `c`. -/
def restrictTable {m : ℕ} (g : Vector R m → R) {j : ℕ} (hj : j ≤ m) (c : Vector R j) :
    CMlPolynomialEval R (m - j) :=
  Vector.ofFn fun x ↦ g (fixLow hj c (boolVec x))

/-- The eq-weighted running sum `Σ_x eq(r_{≥ j}, x) · g(c, x)`; zero when more than `m`
coordinates are fixed. -/
def partialSum {m : ℕ} (g : Vector R m → R) (r : Vector R m) (j : ℕ) (c : Vector R j) : R :=
  if hj : j ≤ m then evalMle (restrictTable g hj c) (r.drop j) else 0

/-! ## Nothing fixed -/

omit [CommRing R] in
private theorem fixLow_zero {m : ℕ} (x : Vector R (m - 0)) :
    fixLow (Nat.zero_le m) (#v[] : Vector R 0) x = x := by
  apply Vector.ext
  intro i hi
  simp [fixLow]

omit [CommRing R] in
private theorem drop_zero {m : ℕ} (r : Vector R m) : r.drop 0 = r := by
  apply Vector.ext
  intro i hi
  simp

/-- With nothing fixed, the running sum is the extension of the table of `g` at `r`. -/
theorem partialSum_zero {m : ℕ} (g : Vector R m → R) (r : Vector R m) :
    partialSum g r 0 #v[] = evalMle (Vector.ofFn fun x ↦ g (boolVec x)) r := by
  rw [partialSum, dite_eq_left (Nat.zero_le m), drop_zero]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [restrictTable, Vector.getElem_ofFn]
  rw [fixLow_zero]

/-! ## Everything fixed -/

omit [CommRing R] in
private theorem fixLow_self {m : ℕ} (c : Vector R m) (x : Vector R (m - m)) :
    fixLow le_rfl c x = c := by
  apply Vector.ext
  intro i hi
  simp [fixLow, hi]

/-- With everything fixed, the running sum is the value at the fixed point. -/
theorem partialSum_self {m : ℕ} (g : Vector R m → R) (r : Vector R m) (c : Vector R m) :
    partialSum g r m c = g c := by
  rw [partialSum, dite_eq_left le_rfl, evalMle_eq_sum]
  have hone : 2 ^ (m - m) = 1 := by simp
  have : Unique (Fin (2 ^ (m - m))) :=
    ⟨⟨⟨0, by omega⟩⟩, fun x ↦ Fin.ext (by have := x.isLt; (clear * - hone; omega))⟩
  rw [Fintype.sum_unique]
  simp only [restrictTable, Fin.getElem_fin, Vector.getElem_ofFn, fixLow_self,
    lagrangeBasis_getElem_nat _ (Fin.isLt _)]
  rw [Finset.prod_eq_one fun b _ ↦ absurd b.isLt (by simp), mul_one]

/-! ## One more coordinate -/

/-- Extending `c` by `0` and then by `x'` is extending `c` by the point `2x'`. -/
private theorem fixLow_push_zero {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1))))
    (hb : 2 * x'.val < 2 ^ (m - j)) :
    fixLow hj (c.push 0) (boolVec x') =
      fixLow hj.le c (boolVec (⟨2 * x'.val, hb⟩ : Fin (2 ^ (m - j)))) := by
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push, boolVec,
    Vector.getElem_ofFn]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by (clear * - h1; omega)]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by (clear * - h1 h2; omega)
      subst hij
      simp [Nat.testBit_zero]
    · have hs : i - j = (i - (j + 1)) + 1 := by (clear * - h2; omega)
      simp only [h1, h2, dite_false, hs, Nat.testBit_succ, Nat.mul_div_cancel_left _ two_pos]

/-- Extending `c` by `1` and then by `x'` is extending `c` by the point `2x' + 1`. -/
private theorem fixLow_push_one {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1))))
    (hb : 2 * x'.val + 1 < 2 ^ (m - j)) :
    fixLow hj (c.push 1) (boolVec x') =
      fixLow hj.le c (boolVec (⟨2 * x'.val + 1, hb⟩ : Fin (2 ^ (m - j)))) := by
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push, boolVec,
    Vector.getElem_ofFn]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by (clear * - h1; omega)]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by (clear * - h1 h2; omega)
      subst hij
      simp [Nat.testBit_zero, Nat.add_mod]
    · have hs : i - j = (i - (j + 1)) + 1 := by (clear * - h2; omega)
      simp only [h1, h2, dite_false, hs, Nat.testBit_succ,
        show (2 * x'.val + 1) / 2 = x'.val by (clear * -; omega)]

/-- Extending `c` by `X` is extending it by `0` and then setting coordinate `j` to `X`. -/
theorem fixLow_push_set {m j : ℕ} (hj : j < m) (c : Vector R j) (x : Vector R (m - (j + 1)))
    (X : R) : fixLow hj (c.push X) x = (fixLow hj (c.push 0) x).set j X hj := by
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push,
    Vector.getElem_set]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by (clear * - h1; omega), show j ≠ i by (clear * - h1; omega)]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by (clear * - h1 h2; omega)
      subst hij
      simp
    · simp [h2, show j ≠ i by (clear * - h2; omega)]

/-- Fixing one more coordinate: the running sum at `j` is the interpolation, by `r_j`, of the
running sums at `j + 1` with the coordinate fixed to `0` and to `1`. -/
theorem partialSum_split {m : ℕ} (g : Vector R m → R) (r : Vector R m) {j : ℕ} (hj : j < m)
    (c : Vector R j) :
    partialSum g r j c =
      (1 - r[j]) * partialSum g r (j + 1) (c.push 0) +
        r[j] * partialSum g r (j + 1) (c.push 1) := by
  have hm : m - j = (m - (j + 1)) + 1 := by omega
  rw [partialSum, partialSum, partialSum, dite_eq_left hj.le, dite_eq_left (Nat.succ_le_of_lt hj),
    dite_eq_left (Nat.succ_le_of_lt hj)]
  -- The remaining coordinates, with the next one split off.
  rw [← evalMle_cast hm, evalMle_succ]
  have hhead : (Vector.cast hm (r.drop j)).head = r[j] := by
    simp [Vector.head]
  have htail : (Vector.cast hm (r.drop j)).tail = r.drop (j + 1) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.tail_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract,
      Vector.getElem_drop]
    exact getElem_congr_idx (by (clear * -; omega))
  rw [hhead, htail]
  -- The layer at `r_j` interpolates the two restricted tables.
  have hlayer : evalMleLayer (Vector.cast (congrArg (2 ^ ·) hm) (restrictTable g hj.le c)) r[j] =
      (1 - r[j]) • restrictTable g hj (c.push 0) + r[j] • restrictTable g hj (c.push 1) := by
    apply Vector.ext
    intro i hi
    rw [← Vector.get_eq_getElem _ ⟨i, hi⟩, evalMleLayer_get]
    simp only [Vector.get_eq_getElem, Vector.getElem_cast, Vector.getElem_add, Vector.getElem_smul,
      smul_eq_mul, restrictTable, Vector.getElem_ofFn]
    rw [fixLow_push_zero hj c ⟨i, hi⟩ (by rw [hm, pow_succ]; (clear * - hi; omega)),
      fixLow_push_one hj c ⟨i, hi⟩ (by rw [hm, pow_succ]; (clear * - hi; omega))]
  rw [hlayer, eval_mle_eq_eval, eval_add, eval_smul, eval_smul, ← eval_mle_eq_eval,
    ← eval_mle_eq_eval]

end
end LeanVM.Protocol
end
-- ===== end of `LvmCpPartialSum` =====

-- ===== merged from `LvmCpProductTree` (GOLF module merge: `LvmCpProductTree.lean` is now a stub importing `LvmGrandProduct`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/ProductTree.lean` (formal rev 40f877dc) as `LvmCpProductTree` for lvm (WP-2).
/-
  LeanVM.Protocol.ToCompPoly.ProductTree

  The product tree over a hypercube table: each layer multiplies adjacent entries of the layer
  below it, and the root is the product of the leaves. The layer identities a grand-product
  argument reduces along. Candidate for CompPoly.
-/

/-!
# Product trees

The product tree of a table `t` of `2 ^ μ` leaves has, one level up, the table `contract t` of
`2 ^ (μ - 1)` entries, entry `x` being `t[2x] * t[2x + 1]`, and so on up to the root, the product
of every leaf. `layerTable t m` is the level on `m` variables, for every `m ≤ μ`: `t` itself at
`m = μ`, the root at `m = 0`. Over an arbitrary commutative ring. Candidate for CompPoly, beside
`CompPoly.Multilinear.Basic`. Nothing here transcribes a source.

Contracting `ρ` levels at once, node `x` is the product of its `2 ^ ρ` descendants
`childIndex ρ c x = c + 2 ^ ρ · x` (`contractPow_getElem`), whose Boolean points are
`childPoint ρ c (boolVec x) = (bits of c, bits of x)`: the descendants occupy the low
coordinates. The layer identity a grand-product argument runs sumcheck on,
`Ṽ_i(r) = Σ_x eq(r, x) ∏_c Ṽ_{i - ρ}(c, x)`, is `evalMle_contractPow`.

## Wrong readings excluded

* The descendants of a node are at the low bits of the index, so the point of a descendant is
  `(bits of c, x)` and not `(x, bits of c)`; a `childPoint` with the bits high evaluates a
  different node.
* `layerTable t m` for `m > μ` is a table of ones, so that the definition is total; every
  identity about it takes `m ≤ μ`.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

variable {R : Type*} [CommRing R]

/-! ## One level -/

/-- The level above a table: entry `x` is the product of entries `2x` and `2x + 1`. -/
def contract {n : ℕ} (t : CMlPolynomialEval R (n + 1)) : CMlPolynomialEval R n :=
  Vector.ofFn fun x ↦
    t[2 * x.val]'(by have := x.isLt; rw [pow_succ]; omega) *
      t[2 * x.val + 1]'(by have := x.isLt; rw [pow_succ]; omega)

/-- Entry `x` of the level above is the product of entries `2x` and `2x + 1`. -/
theorem contract_getElem {n : ℕ} (t : CMlPolynomialEval R (n + 1)) {x : ℕ} (hx : x < 2 ^ n) :
    (contract t)[x] =
      t[2 * x]'(by rw [pow_succ]; omega) * t[2 * x + 1]'(by rw [pow_succ]; omega) := by
  simp [contract]

/-! ## Several levels at once -/

/-- `ρ` levels up. -/
def contractPow : (ρ : ℕ) → {n : ℕ} → CMlPolynomialEval R (n + ρ) → CMlPolynomialEval R n
  | 0, _, t => t
  | ρ + 1, _, t => contractPow ρ (contract t)

/-- The index of descendant `c` of node `x`, `ρ` levels down: `c + 2 ^ ρ · x`. -/
def childIndex (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) : Fin (2 ^ (n + ρ)) :=
  ⟨c.val + 2 ^ ρ * x.val, by
    have h := (cubeIndex c x).isLt
    rw [cubeIndex_val, pow_add] at h
    rw [pow_add, Nat.mul_comm (2 ^ n) (2 ^ ρ)]
    exact h⟩

/-- The descendant's index as a number. -/
@[simp] theorem childIndex_val (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) :
    (childIndex ρ c x).val = c.val + 2 ^ ρ * x.val := rfl

/-- The point of descendant `c` of the point `y`, `ρ` levels down: the bits of `c` in the low
coordinates, `y` in the high ones. -/
def childPoint (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (y : Vector R n) : Vector R (n + ρ) :=
  Vector.cast (Nat.add_comm ρ n) ((boolVec c : Vector R ρ) ++ y)

/-- Bit `a` of a descendant index is bit `a` of the descendant below `ρ` and bit `a - ρ` of the
node above. -/
theorem testBit_childIndex (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) (a : ℕ) :
    (childIndex ρ c x).val.testBit a =
      if a < ρ then c.val.testBit a else x.val.testBit (a - ρ) := by
  rw [childIndex_val, add_comm]
  exact Nat.testBit_two_pow_mul_add x.val c.isLt a

/-- The descendant of a Boolean point is the Boolean point of the descendant index. -/
theorem childPoint_boolVec (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) :
    childPoint ρ c (boolVec x : Vector R n) = boolVec (childIndex ρ c x) := by
  apply Vector.ext
  intro a ha
  rw [childPoint, Vector.getElem_cast, Vector.getElem_append]
  simp only [boolVec, Vector.getElem_ofFn, testBit_childIndex]
  by_cases h : a < ρ <;> simp [h]

/-- Evaluating at the descendant of a Boolean point reads the descendant's entry. -/
theorem evalMle_childPoint_boolVec (ρ : ℕ) {n : ℕ} (t : CMlPolynomialEval R (n + ρ))
    (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) :
    evalMle t (childPoint ρ c (boolVec x)) = t[childIndex ρ c x] := by
  rw [childPoint_boolVec, evalMle_boolVec]

/-- Setting a coordinate of `y` sets the coordinate `ρ` further of the descendant point. -/
theorem childPoint_set (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (y : Vector R n) {k : ℕ} (hk : k < n)
    (X : R) :
    childPoint ρ c (y.set k X hk) = (childPoint ρ c y).set (ρ + k) X (by omega) := by
  apply Vector.ext
  intro i hi
  simp only [childPoint, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_set]
  by_cases h : i < ρ
  · simp [h, show ρ + k ≠ i by omega]
  · by_cases hik : ρ + k = i
    · subst hik
      simp [h]
    · simp [h, hik, show k ≠ i - ρ by omega]

/-- Evaluating at a point whose low coordinates are `u`: the extension, at `u`, of the table of
the evaluations at the descendant points of `y`. -/
theorem evalMle_cast_append (ρ : ℕ) {n : ℕ} (t : CMlPolynomialEval R (n + ρ)) (u : Vector R ρ)
    (y : Vector R n) :
    evalMle t (Vector.cast (Nat.add_comm ρ n) (u ++ y)) =
      evalMle (Vector.ofFn fun c ↦ evalMle t (childPoint ρ c y)) u := by
  have h : ρ + n = n + ρ := Nat.add_comm ρ n
  have ht : t = Vector.cast (congrArg (2 ^ ·) h) (Vector.cast (congrArg (2 ^ ·) h.symm) t) := by
    simp
  conv_lhs => rw [ht, evalMle_cast h, evalMle_split_low]
  rw [evalMle_eq_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [mul_comm]
  congr 1
  rw [childPoint]
  conv_rhs => rw [ht, evalMle_cast h]

/-- A node `ρ` levels up is the product of its `2 ^ ρ` descendants. -/
theorem contractPow_getElem (ρ : ℕ) {n : ℕ} (t : CMlPolynomialEval R (n + ρ)) (x : Fin (2 ^ n)) :
    (contractPow ρ t)[x] = ∏ c : Fin (2 ^ ρ), t[childIndex ρ c x] := by
  induction ρ generalizing n with
  | zero =>
    show t[x.val] = ∏ c : Fin 1, t[(childIndex 0 c x).val]
    rw [Fin.prod_univ_one]
    exact getElem_congr_idx (by simp [childIndex_val])
  | succ ρ ih =>
    simp only [contractPow]
    rw [ih, ← (finProdFinEquiv.trans (finCongr (pow_succ 2 ρ).symm)).prod_comp,
      Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    rw [Fin.prod_univ_two]
    simp only [Fin.getElem_fin, childIndex_val, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finProdFinEquiv_apply_val, Fin.val_zero, Fin.val_one, contract_getElem]
    rw [getElem_congr_idx (show 2 * (c.val + 2 ^ ρ * x.val) = 0 + 2 * c.val + 2 ^ (ρ + 1) * x.val
      by ring), getElem_congr_idx (show 2 * (c.val + 2 ^ ρ * x.val) + 1 =
        1 + 2 * c.val + 2 ^ (ρ + 1) * x.val by ring)]

/-! ## The layers of a tree -/

/-- The level of the tree of `t` on `m` variables: `t` at `m = μ`, the root at `m = 0`, and a
table of ones past the leaves. -/
def layerTable : {μ : ℕ} → CMlPolynomialEval R μ → (m : ℕ) → CMlPolynomialEval R m
  | 0, t, m =>
    if h : m = 0 then Vector.cast (congrArg (2 ^ ·) h.symm) t else Vector.replicate (2 ^ m) 1
  | μ + 1, t, m =>
    if h : m = μ + 1 then Vector.cast (congrArg (2 ^ ·) h.symm) t else layerTable (contract t) m

/-- The leaves are their own level. -/
@[simp] theorem layerTable_self {μ : ℕ} (t : CMlPolynomialEval R μ) : layerTable t μ = t := by
  cases μ <;> simp [layerTable]

/-- Each level is the contraction of the one below. -/
theorem layerTable_contract {μ : ℕ} (t : CMlPolynomialEval R μ) {m : ℕ} (h : m + 1 ≤ μ) :
    layerTable t m = contract (layerTable t (m + 1)) := by
  induction μ generalizing m with
  | zero => omega
  | succ μ ih =>
    have hm : m ≠ μ + 1 := by (clear * - h; omega)
    rw [layerTable, dite_eq_right hm]
    by_cases hm1 : m + 1 = μ + 1
    · have hmμ : m = μ := by (clear * - hm1; omega)
      subst hmμ
      rw [layerTable, dite_eq_left rfl, Vector.cast_rfl, layerTable_self]
    · rw [layerTable, dite_eq_right hm1, ih (contract t) (by (clear * - h hm1; omega))]

/-- A level is `ρ` contractions of the level `ρ` below. -/
theorem layerTable_contractPow {μ : ℕ} (t : CMlPolynomialEval R μ) (ρ : ℕ) {m : ℕ}
    (h : m + ρ ≤ μ) : layerTable t m = contractPow ρ (layerTable t (m + ρ)) := by
  induction ρ generalizing m with
  | zero => rfl
  | succ ρ ih =>
    show layerTable t m = contractPow ρ (contract (layerTable t (m + ρ + 1)))
    rw [← layerTable_contract t (by omega)]
    exact ih (by (clear * - h; omega))

/-- The level of the leaves, reached at any number equal to `μ`. -/
theorem layerTable_of_eq {μ : ℕ} (t : CMlPolynomialEval R μ) {m : ℕ} (h : m = μ) :
    layerTable t m = Vector.cast (congrArg (2 ^ ·) h.symm) t := by
  subst h
  simp

/-- The root: the product of every leaf. -/
theorem layerTable_zero_getElem {μ : ℕ} (t : CMlPolynomialEval R μ) :
    (layerTable t 0)[0] = ∏ i : Fin (2 ^ μ), t[i] := by
  rw [layerTable_contractPow t μ (by omega), layerTable_of_eq t (Nat.zero_add μ)]
  rw [show (contractPow μ (Vector.cast (congrArg (2 ^ ·) (Nat.zero_add μ).symm) t))[0] =
      (contractPow μ (Vector.cast (congrArg (2 ^ ·) (Nat.zero_add μ).symm) t))[
        (⟨0, Nat.two_pow_pos 0⟩ : Fin (2 ^ 0))] from rfl, contractPow_getElem]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_cast]
  exact getElem_congr_idx (by simp [childIndex_val])

end
end LeanVM.Protocol
end
-- ===== end of `LvmCpProductTree` =====

/-! lvm (WP-2): the ArkLib-typed components and their typed completeness (`lambdaStep`,
`lambdaComplete`, `sendChildren`, `childrenComplete`, `interpPrefix`, `interpPrefixComplete`,
`interpolate`, `interpolateComplete`, `layerStep`, `layerStepComplete`, `layerSteps`,
`layerStepsComplete`, `odd`, `oddComplete`, `gkr`, `gkrComplete`), built on `ToArkLib.Typed.*`
outside lvm's imports, are cut. Kept: the statements and relations, the layer's sumcheck family
and its honesty, the combiner's, descendants' and combination challenges' next statements and
checks, and the facts the typed completeness proofs composed (`lambdaNext_mem_rel`,
`combineCheck_children`, `interpDone_mem`, `layerRel_subset_relOut`, `relIn_iff_layerRel_zero`),
made public here. The round polynomial `roundPolyRaw` is restated on Mathlib's `Polynomial`
(leanVM: CompPoly's `CPolynomial`, outside lvm's imports), so `roundPoly` is noncomputable. The
verifier lvm runs is `LvmVCore`'s `gkrStep`/`gkrLayers`. -/

/-!
# The grand product by GKR

`nside` product trees of `2 ^ μ` leaves each. The leaves are tables computed from the public data
and the oracles' contents (`leaves`); nobody sends them. The input statement is the public data
and one claimed root per tree, and the input relation (`Gkr.relIn`) says each root is the product
of its tree's leaves. The output statement is the public data, a point `ζ` of `μ` coordinates and
one value per tree, and the output relation (`Gkr.relOut`) says each value is the multilinear
extension of its tree's leaves at `ζ`. In between, the statement at layer `m` (`LayerStmt`) is a
point of `m` coordinates and one value per tree, the extension of the tree's level on `m`
variables (`layerRel`). A step (`layerStep`) goes `ρ` levels down, from layer `m` to `m + ρ`, at
the slot `Typed.stepSlot F nside ρ m`:

* the combiner (`lambdaStep`, one challenge, batching by powers, `Typed.batch`): the verifier
  draws `λ`, and the claims become one, `Σ_s value_s · λ^s` (`powerBatch`), the sum of the layer
  identity `Σ_s Ṽ_s(r) · λ^s = Σ_x eq(r, x) Σ_s λ^s ∏_c Ṽ'_s(c, x)` over the level `ρ` below;
* the normalized sumcheck on that identity (`m` rounds of `SumcheckRound.round` on
  `SumcheckRound.normalizedWeights`): the message is the cofactor of `eq(r, ·)` (`roundPoly`), a
  sum of products of `2 ^ ρ` affine factors, so of degree `2 ^ ρ`, sent as its `2 ^ ρ + 1`
  coefficients;
* the descendants (`sendChildren`, one message): the prover sends, per tree, the `2 ^ ρ` values of
  the level below at the descendants of the sumcheck's point `c`, and the verifier checks that
  their combined products are the sumcheck's final claim (`combineCheck`);
* the combination challenges (`interpolate`, `ρ` challenges `u`, one round each, lowest first):
  the new point is `(u, c)` and each tree's new value is the extension of its descendants'
  values at `u`.

`gkr` reads the roots as the statement at layer `0`, takes one binary step first when `μ` is odd
(`Gkr.odd`) and steps of radix four after (`Gkr.layerSteps`), each step opening with its
combiner; its slot is `Typed.gkrSlot F nside μ`, so that a protocol's slot that appends it takes
it, and its errors are `Typed.gkrErrors`, which its knowledge soundness is stated at.
`gkrComplete` is its completeness, composed from its parts' through `Typed.Complete.append` on the
layer identities of `LeanVM.Protocol.ToCompPoly.ProductTree`.

*Riders* are further tables computed from the public data and the oracles, each on at most `μ`
variables. The input relation asks each to be zero; the output relation asks each extension to
vanish at the low coordinates of `ζ` (`lowPoint`). They are for a protocol that reuses `ζ` as a
zerocheck point; no definition reads them. A rider on no variable is one value: it states a
condition on the public data and the oracles, carried unchanged from the input relation to the
output relation, which no challenge can make true. The oracles pass through untouched, and there
is no witness.

Written from the mathematics of the product-tree argument. The deployed verifier draws each
layer's combiner at the start of the layer, as here (`verify_gkr_grand_products`,
`crates/verifier/src/bus.rs:20-48` at leanVM `40f877dc`).

## Relation to ArkLib pull request 818

ArkLib's pull request 818 formalizes GKR for layered circuits of addition and multiplication
gates: a sumcheck over the `2k` variables of the two children's indices against the wiring
predicates, and Thaler's line restriction. It is another protocol, whose shapes correspond:
`LayerStmt` and `layerRel` to its `GKRStatement` and `Materialized.layerRel`, `layerStep` and
`layerSteps` to its `gkrLayer` and `gkrReduction` (with `Typed.Def.append` for
`seqCompose`), `sendChildren` with `interpolate` to its `Combine` (interpolation for the line).
This module goes when ArkLib carries a product-tree GKR with round-by-round knowledge soundness.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval
open scoped Polynomial

section

namespace Gkr

variable {F : Type} [Field F]
  {X : Type} {ι : Type} {O : ι → Type}

/-! ## Statements and relations -/

/-- The statement at a layer: the public data, the point, and one claimed value per tree. -/
abbrev LayerStmt (X F : Type) (nside m : ℕ) : Type := X × (Vector F m × (Fin nside → F))

/-- The public data of a step's sumcheck: the layer statement it started from and the
combiner. -/
abbrev LayerX (X F : Type) (nside m : ℕ) : Type := LayerStmt X F nside m × F

/-- What a step's sumcheck reads: its public data, the oracles' contents, no witness. -/
abbrev LayerCtx (X F : Type) {ι : Type} (O : ι → Type) (nside m : ℕ) : Type :=
  SumcheckRound.Ctx (LayerX X F nside m) O Unit

/-- The public data of the protocol, in a step's context. -/
abbrev dataOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : X := ctx.1.1.1.1

/-- The oracles' contents, in a step's context. -/
abbrev oraclesOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : ∀ i, O i := ctx.1.2

/-- The point the layer started from. -/
abbrev pointOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : Vector F m := ctx.1.1.1.2.1

/-- The combiner of the layer. -/
abbrev combinerOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : F := ctx.1.1.2

/-- The low `τ` coordinates of a point. -/
def lowPoint {μ : ℕ} (ζ : Vector F μ) (τ : Fin (μ + 1)) : Vector F τ :=
  Vector.ofFn fun i ↦ ζ[i.val]'(by have := i.isLt; have := τ.isLt; omega)

variable (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))

/-- Every rider table is zero. -/
def RidersZero (x : X) (o : ∀ i, O i) : Prop :=
  ∀ r ∈ riders x o, ∀ i : Fin (2 ^ (r.1 : ℕ)), r.2[i] = 0

/-- The input relation: every rider table is zero, and every tree's claimed root is the product
of its leaves. -/
def relIn : Set (((X × (Fin nside → F)) × ∀ i, O i) × Unit) :=
  {p | RidersZero μ riders p.1.1.1 p.1.2 ∧
    ∀ s, p.1.1.2 s = ∏ i : Fin (2 ^ μ), (leaves p.1.1.1 p.1.2 s)[i]}

/-- The relation at layer `m`: every rider table is zero, and every tree's claimed value is the
extension of its level on `m` variables at the point. -/
def layerRel (m : ℕ) : Set ((LayerStmt X F nside m × ∀ i, O i) × Unit) :=
  {p | RidersZero μ riders p.1.1.1 p.1.2 ∧
    ∀ s, evalMle (layerTable (leaves p.1.1.1 p.1.2 s) m) p.1.1.2.1 = p.1.1.2.2 s}

/-- The output relation: every tree's claimed value is the extension of its leaves at the point,
and every rider's extension vanishes at the point's low coordinates. -/
def relOut : Set ((LayerStmt X F nside μ × ∀ i, O i) × Unit) :=
  {p | (∀ s, evalMle (leaves p.1.1.1 p.1.2 s) p.1.1.2.1 = p.1.1.2.2 s) ∧
    ∀ r ∈ riders p.1.1.1 p.1.2, evalMle r.2 (lowPoint p.1.1.2.1 r.1) = 0}

/-! ## The layer's sumcheck -/

section Layer

variable (ρ m : ℕ)

/-- The trees' levels `ρ` below the step's layer. -/
def below (ctx : LayerCtx X F O nside m) (s : Fin nside) : CMlPolynomialEval F (m + ρ) :=
  layerTable (leaves (dataOf ctx) (oraclesOf ctx) s) (m + ρ)

/-- The summand of the layer's sumcheck at a point `y`: the combination, by the powers of the
combiner, of the products of the descendants of `y` in each tree. -/
def summand (ctx : LayerCtx X F O nside m) (y : Vector F m) : F :=
  ∑ s, combinerOf ctx ^ s.val *
    ∏ c : Fin (2 ^ ρ), evalMle (below nside μ leaves ρ m ctx s) (childPoint ρ c y)

/-- The value of a descendant's extension with the round's variable fixed to `z`. -/
def descendant (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (x' : Fin (2 ^ (m - (j + 1)))) (s : Fin nside) (c : Fin (2 ^ ρ)) (z : F) :
    F :=
  evalMle (below nside μ leaves ρ m ctx s) (childPoint ρ c (fixLow hj (cv.push z) (boolVec x')))

/-- The honest round polynomial at round `j` (lvm: on Mathlib's `Polynomial`): the eq-weighted sum,
over the coordinates not yet bound, of the combined products of the descendants' values, each
affine in the variable of the round. -/
noncomputable def roundPolyRaw (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) : F[X] :=
  ∑ x' : Fin (2 ^ (m - (j + 1))), Polynomial.C (lagrangeBasis ((pointOf ctx).drop (j + 1)))[x'] *
    ∑ s, Polynomial.C (combinerOf ctx ^ s.val) *
      ∏ c : Fin (2 ^ ρ), (Polynomial.C (descendant nside μ leaves ρ m ctx hj cv x' s c 0) +
        Polynomial.X * Polynomial.C (descendant nside μ leaves ρ m ctx hj cv x' s c 1 -
          descendant nside μ leaves ρ m ctx hj cv x' s c 0))

/-- The honest round polynomial has degree at most `2 ^ ρ`: a sum of products of `2 ^ ρ` affine
factors. -/
theorem degree_roundPolyRaw_le (ctx : LayerCtx X F O nside m) {j : ℕ}
    (hj : j < m) (cv : Vector F j) :
    (roundPolyRaw nside μ leaves ρ m ctx hj cv).degree ≤ (2 ^ ρ : ℕ) := by
  refine Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr ?_)
  rw [roundPolyRaw]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x' _ ↦ ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ ↦ ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun c _ ↦ ?_).trans (by simp)
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine (Polynomial.natDegree_mul_le).trans ?_
  simp

/-- The honest round polynomial as a message, its `2 ^ ρ + 1` coefficients; the zero polynomial
past the last round. -/
noncomputable def roundPoly (ctx : LayerCtx X F O nside m) (j : ℕ) (cv : Vector F j) :
    SumcheckRound.Message F (2 ^ ρ) :=
  if h : j < m then SumcheckRound.ofPolynomial _ (roundPolyRaw nside μ leaves ρ m ctx h cv)
  else SumcheckRound.ofPolynomial _ 0

/-- The verifier's domain at round `j`: the normalized round's, against the layer's point. -/
def weights : SumcheckRound.Weights F (LayerX X F nside m) :=
  SumcheckRound.normalizedWeights fun x ↦ x.1.2.1

/-- The family of claims of the layer's sumcheck: the eq-weighted running sums of the summand,
the honest polynomials, the normalized domain, and the riders' condition. -/
noncomputable def family : SumcheckRound.Family F (LayerX X F nside m) O Unit (2 ^ ρ) where
  claim := fun ctx j cv ↦ partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) j cv
  poly := roundPoly nside μ leaves ρ m
  weight := weights nside m
  inv := fun ctx _ _ ↦ RidersZero μ riders (dataOf ctx) (oraclesOf ctx)

/-- The honest polynomial's value at `x` is the running sum with one more coordinate fixed to
`x`: each descendant's value is affine in the round's variable. -/
private theorem roundPoly_eval (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (x : F) :
    SumcheckRound.evaluate (2 ^ ρ) (roundPoly nside μ leaves ρ m ctx j cv) x =
      partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) (j + 1) (cv.push x) := by
  rw [roundPoly, dite_eq_left hj,
    SumcheckRound.evaluate_ofPolynomial _ _ (degree_roundPolyRaw_le nside μ leaves ρ m ctx hj cv),
    roundPolyRaw, Polynomial.eval_finsetSum, partialSum, dite_eq_left (Nat.succ_le_of_lt hj),
    evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x' _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum, mul_comm]
  simp only [Fin.getElem_fin, restrictTable, Vector.getElem_ofFn, summand, Fin.eta]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_C]
  unfold descendant
  have key : ∀ z : F,
      evalMle (below nside μ leaves ρ m ctx s)
          (childPoint ρ c (fixLow hj (cv.push z) (boolVec x'))) =
        evalMle (below nside μ leaves ρ m ctx s)
          ((childPoint ρ c (fixLow hj (cv.push 0) (boolVec x'))).set (ρ + j) z (by omega)) := by
    intro z
    rw [fixLow_push_set hj cv (boolVec x') z, childPoint_set]
  rw [key x, key 1, evalMle_set (below nside μ leaves ρ m ctx s) _ (k := ρ + j) (by (clear * - hj; omega)) x,
    ← key 0]
  ring

/-- The honest polynomial passes the verifier's check: its weighted values at `0` and `1` are the
running sum before the round. -/
private theorem roundPoly_check (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) :
    SumcheckRound.weightedSum (2 ^ ρ) (weights nside m ctx.1.1 j)
        (roundPoly nside μ leaves ρ m ctx j cv) =
      partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) j cv := by
  simp only [weights, SumcheckRound.normalizedWeights, hj, ↓reduceDIte,
    SumcheckRound.weightedSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [roundPoly_eval nside μ leaves ρ m ctx hj cv 0, roundPoly_eval nside μ leaves ρ m ctx hj cv 1,
    partialSum_split _ _ hj]

/-- The layer's family is honest. -/
theorem family_honest : (family nside μ leaves riders ρ m).Honest m where
  check := fun ctx _ c hj ↦ roundPoly_check nside μ leaves ρ m ctx hj c
  next := fun ctx _ c x hj ↦ roundPoly_eval nside μ leaves ρ m ctx hj c x
  inv_push := fun _ _ _ _ _ h ↦ h

/-! ## The combiner -/

/-- The statement after the combiner: the layer statement with the combiner, no challenge yet,
and the combined claim `Σ_s value_s · λ^s`. -/
def lambdaNext (s : LayerStmt X F nside m) (l : F) : SumcheckRound.Stmt (LayerX X F nside m) F 0 :=
  ((s, l), (#v[], powerBatch s.2.2 l))

variable [DecidableEq F]

omit [DecidableEq F] in
/-- On a Boolean point, the summand is the combination of the trees' levels at the layer: the
descendants' product is the node's value. -/
theorem summand_boolVec (hm : m + ρ ≤ μ) (ctx : LayerCtx X F O nside m) (x : Fin (2 ^ m)) :
    summand nside μ leaves ρ m ctx (boolVec x) =
      ∑ s, combinerOf ctx ^ s.val * (layerTable (leaves (dataOf ctx) (oraclesOf ctx) s) m)[x] := by
  unfold summand
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  rw [layerTable_contractPow _ ρ hm, contractPow_getElem]
  exact Finset.prod_congr rfl fun c _ ↦ evalMle_childPoint_boolVec ρ _ c x

omit [DecidableEq F] in
/-- The family's first claim is the combination, by the powers of the combiner, of the trees'
levels at the layer's point. -/
theorem partialSum_summand_zero (hm : m + ρ ≤ μ) (s : LayerStmt X F nside m) (o : ∀ i, O i)
    (l : F) :
    partialSum (summand nside μ leaves ρ m (((s, l), o), ())) s.2.1 0 #v[] =
      powerBatch (fun t ↦ evalMle (layerTable (leaves s.1 o t) m) s.2.1) l := by
  rw [partialSum_zero]
  have htab : (Vector.ofFn fun y ↦ summand nside μ leaves ρ m (((s, l), o), ()) (boolVec y)) =
      Vector.ofFn fun y ↦ ∑ t, l ^ t.val * (layerTable (leaves s.1 o t) m)[y] :=
    Vector.ext fun y hy ↦ by
      simp only [Vector.getElem_ofFn]
      exact summand_boolVec nside μ leaves ρ m hm _ ⟨y, hy⟩
  rw [htab, evalMle_ofFn_sum, powerBatch]
  exact Finset.sum_congr rfl fun t _ ↦ mul_comm _ _

omit [DecidableEq F] in
/-- From the layer relation, the combined claim at any challenge is the running sum of the
summand with nothing fixed, and the riders' condition carries over. -/
theorem lambdaNext_mem_rel (hm : m + ρ ≤ μ) (s : LayerStmt X F nside m) (o : ∀ i, O i)
    (l : F)
    (h : ((s, o), ()) ∈ layerRel nside μ leaves riders m) :
    ((lambdaNext nside m s l, o), ()) ∈ SumcheckRound.rel (family nside μ leaves riders ρ m) 0 := by
  obtain ⟨hz, hval⟩ := h
  refine ⟨hz, ?_⟩
  change (lambdaNext nside m s l).2.2 =
    partialSum (summand nside μ leaves ρ m (((s, l), o), ())) s.2.1 0 #v[]
  rw [partialSum_summand_zero nside μ leaves ρ m hm s o l]
  show powerBatch s.2.2 l = _
  exact congrArg (powerBatch · l) (funext fun t ↦ (hval t).symm)

/-! ## The descendants -/

/-- The statement after the descendants' message, with `i` combination challenges drawn: the
public data, the sumcheck's point, the values per tree, and the challenges. -/
abbrev InterpStmt (X F : Type) (nside m ρ i : ℕ) : Type :=
  (X × (Vector F m × (Fin nside → CMlPolynomialEval F ρ))) × Vector F i

/-- The honest values of the trees at the point `c`: each tree's level below at the descendants
of `c`. -/
def children (x : X) (o : ∀ i, O i) (c : Vector F m) (s : Fin nside) : CMlPolynomialEval F ρ :=
  Vector.ofFn fun b ↦ evalMle (layerTable (leaves x o s) (m + ρ)) (childPoint ρ b c)

/-- The verifier's check: the final claim is the combination, by the powers of the combiner, of
the products of each tree's values. -/
def combineCheck (s : SumcheckRound.Stmt (LayerX X F nside m) F m)
    (ch : Fin nside → CMlPolynomialEval F ρ) : Bool :=
  decide (s.2.2 = powerBatch (fun t ↦ ∏ c : Fin (2 ^ ρ), (ch t)[c]) s.1.2)

/-- The statement after the message: the public data, the sumcheck's point, the values. -/
def childNext (s : SumcheckRound.Stmt (LayerX X F nside m) F m)
    (ch : Fin nside → CMlPolynomialEval F ρ) : InterpStmt X F nside m ρ 0 :=
  ((s.1.1.1, (s.2.1, ch)), #v[])

/-- The relation after the descendants' message, with `i` combination challenges drawn: every
rider table is zero, and the trees' values are the honest ones at the sumcheck's point. -/
def childRel (i : ℕ) : Set ((InterpStmt X F nside m ρ i × ∀ j, O j) × Unit) :=
  {p | RidersZero μ riders p.1.1.1.1 p.1.2 ∧
    p.1.1.1.2.2 = children nside μ leaves ρ m p.1.1.1.1 p.1.2 p.1.1.1.2.1}

/-- From the sumcheck's final relation, the honest values pass the check: the final claim is the
summand at the point, the combination of the descendants' products. -/
theorem combineCheck_children (s : SumcheckRound.Stmt (LayerX X F nside m) F m)
    (o : ∀ i, O i)
    (h : ((s, o), ()) ∈ SumcheckRound.rel (family nside μ leaves riders ρ m) m) :
    combineCheck nside ρ m s (children nside μ leaves ρ m s.1.1.1 o s.2.1) = true := by
  obtain ⟨-, hclaim⟩ := h
  rw [combineCheck, decide_eq_true_eq, hclaim]
  change partialSum (summand nside μ leaves ρ m ((s.1, o), ())) s.1.1.2.1 m s.2.1 = _
  rw [partialSum_self, powerBatch]
  unfold summand
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  simp [children, below]

/-! ## The combination challenges -/

/-- The statement after one more combination challenge: the challenge appended. -/
def interpNext {i : ℕ} (s : InterpStmt X F nside m ρ i) (u : F) :
    InterpStmt X F nside m ρ (i + 1) :=
  (s.1, s.2.push u)

/-- The layer statement once the `ρ` combination challenges `u` are drawn: the point `(u, c)`,
and each tree's values interpolated at `u`. -/
def interpDone (s : InterpStmt X F nside m ρ ρ) : LayerStmt X F nside (m + ρ) :=
  (s.1.1, (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1), fun t ↦ evalMle (s.1.2.2 t) s.2))

omit [DecidableEq F] in
/-- The values interpolated at `u` are the level below at the new point `(u, c)`. -/
theorem interpDone_mem (s : InterpStmt X F nside m ρ ρ) (o : ∀ i, O i)
    (hin : ((s, o), ()) ∈ childRel nside μ leaves riders ρ m ρ) :
    ((interpDone nside ρ m s, o), ()) ∈ layerRel nside μ leaves riders (m + ρ) := by
  obtain ⟨hz, hch⟩ := hin
  refine ⟨hz, fun t ↦ ?_⟩
  show _ = evalMle (s.1.2.2 t) s.2
  rw [hch]
  exact evalMle_cast_append ρ _ s.2 s.1.2.1

end Layer

/-! ## The whole argument -/

/-- The relation at the leaves gives the output relation: the level on `μ` variables is the
leaves, and a zero table has a zero extension everywhere. -/
theorem layerRel_subset_relOut :
    layerRel nside μ leaves riders μ ⊆ relOut nside μ leaves riders := by
  intro p ⟨hz, hval⟩
  refine ⟨fun t ↦ by rw [← hval t, layerTable_self], fun r hr ↦ ?_⟩
  rw [evalMle_eq_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hz r hr i, zero_mul]

/-- The roots as the statement at layer `0`, whose point is empty. -/
def rootStmt (s : X × (Fin nside → F)) : LayerStmt X F nside 0 := (s.1, (#v[], s.2))

/-- Roots are the products of their leaves exactly when, read as the statement at layer `0`,
they are the trees' values there. -/
theorem relIn_iff_layerRel_zero (s : X × (Fin nside → F)) (o : ∀ i, O i) :
    ((s, o), ()) ∈ relIn nside μ leaves riders ↔
      ((rootStmt nside s, o), ()) ∈ layerRel nside μ leaves riders 0 := by
  refine and_congr Iff.rfl (forall_congr' fun t ↦ ?_)
  show s.2 t = ∏ i : Fin (2 ^ μ), (leaves s.1 o t)[i] ↔
    evalMle (layerTable (leaves s.1 o t) 0) #v[] = s.2 t
  constructor
  · intro h
    rw [evalMle_zero, h, ← layerTable_zero_getElem]
    rfl
  · intro h
    rw [evalMle_zero] at h
    rw [← h, ← layerTable_zero_getElem]
    rfl

end Gkr

end
end LeanVM.Protocol
