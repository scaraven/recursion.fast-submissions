/- `LvmTypedVEqPhasesXOff` (GOLF2 off-path move, group 2 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmMlListLemmas, LvmMlBasic, LvmCpPowerBatching, LvmGrandProductSecurity, LvmVEqArith, LvmAccNodeFold, LvmTypedVEqPhasesX,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmMlListLemmas
import LvmMlBasic
import LvmCpPowerBatching
import LvmGrandProductSecurity
import LvmVEqArith
import LvmAccNodeFold
import LvmTypedVEqPhasesX
import LvmChainTablePad
import LvmJBMutual
import LvmQAsmHar47
import LvmSpecRulesCert
import LvmVEqTape
import LvmVerifierST

-- ===== from `LvmMlListLemmas` =====

section
section
universe u v w
namespace List

theorem append_getLast_dropLast {α : Type u} (l : List α) (h : l ≠ []) :
    l.dropLast ++ [l.getLast h] = l := by
  induction l with
  | nil =>
    contradiction
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp [dropLast, getLast]
    | cons hd' tl' =>
      simp only [dropLast_cons_cons, getLast]
      simp only [cons_append, cons.injEq, true_and]
      apply ih

theorem foldl_congr_of_mem {α : Type u} {β : Type v} {f g : α → β → α}
    (xs : List β) (acc : α) (h : ∀ acc' x, x ∈ xs → f acc' x = g acc' x) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [foldl_cons]
      rw [h acc x (by simp)]
      apply ih
      intro acc' y hy
      exact h acc' y (by simp [hy])

theorem foldl_split_outer {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) (h : l ≠ []): foldl (f:=f) (init:=init) (l)
    = f (foldl (f:=f) (init:=init) (l.dropLast)) (l.getLast (by omega)) := by
  conv_lhs => rw [← append_getLast_dropLast l h]
  rw [foldl_append]
  rfl

theorem foldl_split_inner {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) (h : l ≠ []): foldl (f:=f) (init:=init) (l)
    = foldl (f:=f) (init:=f (init) (l.head (by omega))) (l.tail) := by
  have h_l_eq: l = cons (l.head (by omega)) (l.tail) := by
    exact Eq.symm (cons_head_tail h)
  conv_lhs => enter [3]; rw [h_l_eq]
  rw [foldl_cons]

theorem foldr_split_outer {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (l : List α) (h : l ≠ []): foldr (f:=f) (init:=init) (l)
    = f (l.head (by omega)) (foldr (f:=f) (init:=init) (l.tail)) := by
  have h_l_eq: l = cons (l.head (by omega)) (l.tail) := by
    exact Eq.symm (cons_head_tail h)
  conv_lhs => enter [3]; rw [h_l_eq]
  rw [foldr_cons]

theorem foldr_split_inner {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (l : List α) (h : l ≠ []): foldr (f:=f) (init:=init) (l)
    = foldr (f:=f) (init:=f (l.getLast (by omega)) (init)) (l.dropLast) := by
  conv_lhs => rw [← append_getLast_dropLast l h]
  rw [foldr_append]
  rfl

end List
end
end

section
section
universe u v w
namespace List
variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)

theorem mapM_single (f : α → m β) (a : α) : List.mapM f [a] = return [← f a] := by
  rw [← List.mapM'_eq_mapM]
  simp only [mapM', bind_pure_comp, map_pure]

end List
end
end

section
section
universe u v w
namespace List
variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)
variable {α : Type*} {unit : α}

theorem rightpad_eq_rightpad_max (l : List α) (n : Nat) :
    rightpad n unit l = rightpad (max n l.length) unit l := by simp [rightpad]; omega

theorem rightpad_eq_rightpad_append_replicate_of_ge
    (l : List α) (m n : Nat) (h : n ≤ m) :
  rightpad m unit l = rightpad n unit l ++ replicate (m - max n l.length) unit := by
  simp [rightpad]; omega

theorem rightpad_eq_if_rightpad_eq_of_ge (l l' : List α) (m n n' : Nat) (h : n ≤ m) (h' : n' ≤ m) :
    rightpad n unit l = rightpad n' unit l' →
  rightpad m unit l = rightpad m unit l' := by
  intro hEq
  rw [rightpad_eq_rightpad_append_replicate_of_ge l _ n h]
  rw [rightpad_eq_rightpad_append_replicate_of_ge l' _ n' h']
  have hLen : max n l.length = max n' l'.length := calc
    max n l.length = (rightpad n unit l).length := Eq.symm (rightpad_length n unit l)
    _ = (rightpad n' unit l').length := congrArg length hEq
    _ = max n' l'.length := rightpad_length n' unit l'
  simp [hLen]
  -- Substitute the expressions for the rightpads into the goal.
  have h_subst : l ++ replicate (n - l.length) unit = l' ++ replicate (n' - l'.length) unit := by
    simpa only [rightpad] using hEq
  rw [ List.replicate_add, List.replicate_add ];
  rw [ ← List.append_assoc, ← List.append_assoc, h_subst ]

end List
end
end

section
section
universe u v w
namespace List
variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β : Type u}
    (f : α → β) (l : List α)
variable {α : Type*} {unit : α}

theorem rightpad_getElem_eq_getD {a b : List α} {unit : α} {i : Nat}
    (h : i < (a.rightpad b.length unit).length) :
  (a.rightpad b.length unit)[i] = a.getD i unit := by
  rw [← rightpad_getD_eq_getD a b.length, getD_eq_getElem _ _ h]

/-- Given two lists of potentially different lengths, right-pads the shorter list with `unit`
  elements until they are the same length. -/
def matchSize (l₁ : List α) (l₂ : List α) (unit : α) : List α × List α :=
  (l₁.rightpad (l₂.length) unit, l₂.rightpad (l₁.length) unit)

theorem matchSize_comm (l₁ : List α) (l₂ : List α) (unit : α) :
    matchSize l₁ l₂ unit = (matchSize l₂ l₁ unit).swap := by
  simp [matchSize]

/-- `List.matchSize` returns two equal lists iff the two lists agree at every index `i : Nat`
  (extended by `unit` if necessary). -/
theorem matchSize_eq_iff_forall_eq (l₁ l₂ : List α) (unit : α) :
    (fun (x, y) => x = y) (matchSize l₁ l₂ unit) ↔ ∀ i : Nat, l₁.getD i unit = l₂.getD i unit := by
  simp only [matchSize]
  constructor
  · intro h i
    rw [← rightpad_getD_eq_getD l₁ l₂.length unit i,
        ← rightpad_getD_eq_getD l₂ l₁.length unit i, h]
  · intro h
    refine List.ext_getElem ?_ ?_
    · simp only [rightpad_length]; omega
    · intro i h1 h2
      have := h i
      rw [← rightpad_getD_eq_getD l₁ l₂.length unit i,
          ← rightpad_getD_eq_getD l₂ l₁.length unit i] at this
      rwa [getD_eq_getElem _ _ h1, getD_eq_getElem _ _ h2] at this

/-- `List.dropWhile` but starting from the last element. Performed by `dropWhile` on the reversed
  list, followed by a reversal. -/
def dropLastWhile (p : α → Bool) (l : List α) : List α :=
  (l.reverse.dropWhile p).reverse

lemma zipWith_const {α β : Type _} {f : α → β → β} {l₁ : List α} {l₂ : List β}
    (h₁ : l₁.length = l₂.length) (h₂ : ∀ a b, f a b = b) : l₁.zipWith f l₂ = l₂ := by
  induction' l₁ with hd tl ih generalizing l₂ <;> rcases l₂ <;> aesop

/-- An injective `f` separates the elements of a duplicate-free list pairwise.

This is `List.Nodup.map` transported along `List.pairwise_map`, stated in the unmapped form that
`Std.ExtTreeMap.getElem_ofList_of_mem` and friends ask for. -/
theorem Nodup.pairwise_ne_map {α : Type u} {β : Type v} {l : List α} {f : α → β}
    (hf : Function.Injective f) (hl : l.Nodup) : l.Pairwise fun a b => f a ≠ f b :=
  List.pairwise_map.mp (Nodup.map hf hl)

end List
end
end

-- ===== from `LvmMlBasic` =====

section
section
section
universe u
namespace Vector

theorem foldl_succ
    {α β} {n : ℕ} [NeZero n] (f : β → α → β) (init : β) (v : Vector α n) :
    v.foldl (f:=f) (b:=init) = v.tail.foldl (f:=f) (b:=f init v.head) := by
  rw [foldl_eq_toList_foldl, foldl_eq_toList_foldl]
  rw [toList_tail]
  have h_ne : v.toList ≠ [] := by
    simp only [ne_eq, toList_eq_nil_iff]
    exact NeZero.ne n
  rw [List.foldl_split_inner f init v.toList h_ne]
  congr 2
  simp only [head, List.head_eq_getElem, getElem_toList]

end Vector
end
end
end

section
section
section
universe u
namespace Vector
variable {R : Type*} {n : ℕ}

/-- Accumulate paired products from equal-length vectors, from left to right, starting at `init`.
The products and accumulator lie in `W`; no reduction is performed. -/
def accumulateProducts {W : Type*} [Add W] (product : R → R → W) (init : W)
    (a b : Vector R n) : W :=
  a.zipWith product b |>.foldl (· + ·) init

/-- If reduction preserves addition and each paired product, reducing the accumulator gives
the reduced initial value plus the dot product of the input vectors. -/
theorem reduce_accumulateProducts {W : Type*} [AddZero W] [AddMonoid R] [Mul R]
    (reduce : W →+ R) (product : R → R → W)
    (hproduct : ∀ x y, reduce (product x y) = x * y) (init : W) (a b : Vector R n) :
    reduce (accumulateProducts product init a b) = reduce init + dotProduct a b := by
  have hmap : (a.zipWith product b).map reduce = a.zipWith (· * ·) b := by
    ext i
    simp only [getElem_map, getElem_zipWith, hproduct]
  calc
    reduce (accumulateProducts product init a b) =
        ((a.zipWith product b).map reduce).foldl (· + ·) (reduce init) :=
      (foldl_map_hom (fun x y => (map_add reduce x y).symm)).symm
    _ = (a.zipWith (· * ·) b).foldl (· + ·) (reduce init) := by rw [hmap]
    _ = reduce init + dotProduct a b := by
      simpa only [dotProduct, _root_.add_zero] using
        (foldl_assoc (op := (· + ·)) (xs := a.zipWith (· * ·) b)
          (a₁ := reduce init) (a₂ := 0))

/-- Reducing a product accumulator initialized at zero recovers the dot product. -/
theorem reduce_accumulateProducts_zero {W : Type*} [AddZero W] [AddMonoid R] [Mul R]
    (reduce : W →+ R) (product : R → R → W)
    (hproduct : ∀ x y, reduce (product x y) = x * y) (a b : Vector R n) :
    reduce (accumulateProducts product 0 a b) = dotProduct a b := by
  rw [reduce_accumulateProducts reduce product hproduct, map_zero, _root_.zero_add]

/-- Ordinary multiplication is an eager product accumulator, with identity reduction. -/
theorem accumulateProducts_mul [AddMonoid R] [Mul R] (init : R) (a b : Vector R n) :
    accumulateProducts (· * ·) init a b = init + dotProduct a b :=
  reduce_accumulateProducts (AddMonoidHom.id R) (· * ·) (fun _ _ => rfl) init a b

end Vector
end
end
end

section
section
section
universe u
namespace Vector
variable {R : Type*} {n : ℕ}
namespace Matrix
variable {α : Type*}

/-- Matrix-vector multiplication over `α`.
`M` is given as a vector of row-vectors. -/
def mulVec [Zero α] [Add α] [Mul α] {numRows numCols : Nat}
    (M : Vector (Vector α numCols) numRows)
  (x : Vector α numCols) : Vector α numRows :=
  M.map (fun row => row *ᵥ x)

/-- Convert a flat row-major vector of length `m*n` into an `m × n` row-major matrix
represented as `Vector (Vector α n) m`. -/
def ofFlatten {m n : ℕ} (v : Vector α (m * n)) : Matrix α m n :=
  (Vector.finRange m).map (fun i => (v.extract (i.val * n) (i.val * n + n)).cast
    (by
    -- Why can't `omega`, `aesop`, `grind`, etc. solve this?
      rcases i with ⟨i, h⟩
      have : i * n + n ≤ m * n := by
        calc
        _ = (i + 1) * n := by ring
        _ ≤ m * n := by gcongr; exact h
      simp [this]))

/-- Convert to a `Fin`-indexed matrix (the definition in Mathlib): `Fin m → Fin n → α` -/
def toFinMatrix {m n : ℕ} (matrix : Matrix α m n) : _root_.Matrix (Fin m) (Fin n) α :=
  fun i j => (matrix.get i).get j

/-- Convert from a `Fin`-indexed matrix (the definition in Mathlib): `Fin m → Fin n → α` -/
def ofFinMatrix {m n : ℕ} (matrix : _root_.Matrix (Fin m) (Fin n) α) : Matrix α m n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => matrix i j))

end Matrix
end Vector
end
end
end

section
section
section
universe u
namespace Vector

/-- A ring homomorphism maps a dot product to the dot product of the mapped vectors. -/
theorem map_dotProduct {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) {n : ℕ} (a b : Vector R n) :
    f (dotProduct a b) = dotProduct (a.map f) (b.map f) := by
  rw [dotProduct_eq_root_dotProduct, f.map_dotProduct, dotProduct_eq_root_dotProduct]
  congr 1 <;> funext i <;>
    simp only [Function.comp_apply, Vector.get_eq_getElem, Vector.getElem_map]

end Vector
end
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomial
section CMlPolynomialInstances

instance inhabited [Inhabited R] : Inhabited (CMlPolynomial R n) := by
  simp [CMlPolynomial]; infer_instance

/-- Conform a list of coefficients to a `CMlPolynomial` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : CMlPolynomial R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

end CMlPolynomialInstances
end CMlPolynomial
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomial
section CMlPolynomialInstances

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

end CMlPolynomialInstances
end CMlPolynomial
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomial
section CMlPolynomialMonomialBasisAndEvaluations
variable [CommSemiring R]
variable {S : Type*} [CommSemiring S]

/-- Mapping each monomial-basis value by a ring homomorphism equals evaluating the
monomial basis at the mapped point. -/
theorem map_monomialBasis (f : R →+* S) (x : Vector R n) :
    (monomialBasis x).map f = monomialBasis (x.map f) := by
  ext i hi
  simp only [Vector.getElem_map, monomialBasis, Vector.getElem_ofFn, map_prod,
    apply_ite, map_one, Fin.getElem_fin]

end CMlPolynomialMonomialBasisAndEvaluations
end CMlPolynomial
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomial
section CMlPolynomialMonomialBasisAndEvaluations
variable [CommSemiring R]
variable {S : Type*} [CommSemiring S]

/-- Mapping a coefficient-form evaluation by a ring homomorphism equals evaluating the
mapped coefficients at the mapped point. -/
theorem map_eval (f : R →+* S) (p : CMlPolynomial R n) (x : Vector R n) :
    f (eval p x) = eval (map f p) (x.map f) := by
  unfold eval
  rw [Vector.map_dotProduct, map_monomialBasis]
  rfl

/-- Evaluate monomial coefficients by accumulating their products with the monomial-basis
values in `W`, starting at zero, then reducing once to a value in `R`. -/
def evalWithProducts {W : Type*} [AddZero W] (product : R → R → W) (reduce : W →+ R)
    (p : CMlPolynomial R n) (x : Vector R n) : R :=
  reduce (Vector.accumulateProducts product 0 p (monomialBasis x))

/-- Product accumulation followed by additive reduction agrees with coefficient evaluation
when reducing each product gives the ordinary product of its two factors. -/
theorem evalWithProducts_eq_eval {W : Type*} [AddZero W]
    (product : R → R → W) (reduce : W →+ R)
    (hproduct : ∀ a b, reduce (product a b) = a * b)
    (p : CMlPolynomial R n) (x : Vector R n) :
    evalWithProducts product reduce p x = eval p x :=
  Vector.reduce_accumulateProducts_zero reduce product hproduct p (monomialBasis x)

end CMlPolynomialMonomialBasisAndEvaluations
end CMlPolynomial
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomial
section CMlPolynomialMonomialBasisAndEvaluations
variable [CommSemiring R]
variable {S : Type*} [CommSemiring S]

/-- Horner evaluation through a ring homomorphism agrees with the dot-product evaluator. -/
theorem eval₂_horner_eq_eval₂ (p : CMlPolynomial R n) (f : R →+* S) (x : Vector S n) :
    eval₂Horner p f x = eval₂ p f x := by
  simpa [eval₂Horner, eval₂] using
    (eval_horner_eq_eval (p := map f p) (x := x))

end CMlPolynomialMonomialBasisAndEvaluations
end CMlPolynomial
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomialEval
section CMlPolynomialEvalInstances

instance inhabited [Inhabited R] : Inhabited (CMlPolynomialEval R n) := by
  simp only [CMlPolynomialEval]; infer_instance

/-- Conform a list of coefficients to a `CMlPolynomialEval` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : CMlPolynomialEval R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

end CMlPolynomialEvalInstances
end CMlPolynomialEval
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomialEval
section CMlPolynomialEvalInstances

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

end CMlPolynomialEvalInstances
end CMlPolynomialEval
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomialEval
section CMlPolynomialLagrangeBasisAndEvaluations
variable [CommRing R]
variable {S : Type*} [CommRing S]

/-- The equality kernel factors across appended coordinate blocks. -/
theorem eqTilde_append {m : ℕ} (w₁ x₁ : Vector R n) (w₂ x₂ : Vector R m) :
    eqTilde (w₁ ++ w₂) (x₁ ++ x₂) = eqTilde w₁ x₁ * eqTilde w₂ x₂ := by
  simp only [eqTilde_eq_prod]
  rw [Fin.prod_univ_add]
  congr 1 <;> exact Finset.prod_congr rfl fun i _ => by simp

/-- Multilinear-extension interpolation through a ring homomorphism agrees with the
dot-product evaluator. -/
theorem eval₂_mle_eq_eval₂ (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) :
    eval₂Mle p f x = eval₂ p f x := by
  simpa [eval₂Mle, eval₂] using
    (eval_mle_eq_eval (p := map f p) (x := x))

end CMlPolynomialLagrangeBasisAndEvaluations
end CMlPolynomialEval
end CompPoly
end
end

section
section
namespace CompPoly
variable {R : Type*} {n : ℕ}
namespace CMlPolynomial
variable {R : Type*} [AddCommGroup R]

/-- **One level** of the zeta‑transform (coefficient to evaluation).

Processes the `j`-th variable by folding the "partner" index (with bit `j` cleared) into
every index that has bit `j` set. At output index `i`:
$$ (\text{monoToLagrangeLevel}\ j\ v)[i] \ =\ \begin{cases}
  v[i] + v[i - 2^j] & \text{if bit } j \text{ of } i \text{ is } 1 \\
  v[i] & \text{otherwise}
\end{cases} $$

After applying every level `0, 1, …, n-1` the resulting entry at `i` is
$\sum_{j \subseteq i} p[j]$ (bitwise subset), which is the hypercube evaluation at the
Boolean point encoded by `i`. Cost per level: $O(2^n)$ additions, so the full transform
is $O(n \cdot 2^n)$.

The `stride` is $2^j$, the distance between indices that differ only in bit `j`.
-/
@[inline] def monoToLagrangeLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val    -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] + v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full zeta transform**: coefficients → evaluations.

Applies `monoToLagrangeLevel 0, 1, …, n-1` in that order via `foldl`. The resulting entry
at each index `i : Fin (2 ^ n)` is $\sum_{j \subseteq i} p[j]$ (the classical zeta
transform on the Boolean lattice).

**Complexity:** $O(n \cdot 2^n)$ additions — this is the butterfly form. Contrast with
the naive `monoToLagrangeSpec` which is $O(4^n)$. -/
@[inline] def monoToLagrange (n : ℕ) : CMlPolynomial R n → CMlPolynomialEval R n :=
  (List.finRange n).foldl (fun acc level => monoToLagrangeLevel level acc)

/-- **One level** of the inverse zeta‑transform / Möbius transform (evaluation to
coefficient).

Processes the `j`-th variable by subtracting the partner entry (bit `j` cleared) from
every index that has bit `j` set. At output index `i`:
$$ (\text{lagrangeToMonoLevel}\ j\ v)[i] \ =\ \begin{cases}
  v[i] - v[i - 2^j] & \text{if bit } j \text{ of } i \text{ is } 1 \\
  v[i] & \text{otherwise}
\end{cases} $$

Each level is the exact inverse of `monoToLagrangeLevel j` (see
`lagrangeToMonoLevel_monoToLagrangeLevel_id`).

The `stride` is $2^j$.
-/
@[inline] def lagrangeToMonoLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val  -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] - v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full inverse / Möbius transform**: evaluations → coefficients.

Applies `lagrangeToMonoLevel (n-1), (n-2), …, 0` via `foldr`. The resulting entry at
each index `i : Fin (2 ^ n)` is the inclusion-exclusion sum
$\sum_{j \subseteq i} (-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)} \cdot p[j]$ —
see `lagrangeToMono_eq_lagrangeToMonoSpec`.

**Complexity:** $O(n \cdot 2^n)$ additions/subtractions. Contrast with the naive
`lagrangeToMonoSpec` which is $O(4^n)$. -/
@[inline]
def lagrangeToMono (n : ℕ) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  (List.finRange n).foldr (fun h acc => lagrangeToMonoLevel h acc)

/-- The $O(4^n)$ inclusion-exclusion specification for the Möbius transform.

For each output index `i`, this sums over all indices `j` that are bitwise subsets of `i`
(`i &&& j = j`), with sign
$(-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)}$:
$$ (\text{lagrangeToMonoSpec}\ p)[i]
  = \sum_{j \subseteq i} (-1)^{\mathrm{popCount}(i) - \mathrm{popCount}(j)} \cdot p[j]. $$

Provable equivalent to the fast `lagrangeToMono` — see `lagrangeToMono_eq_lagrangeToMonoSpec`.
-/
def lagrangeToMonoSpec (p : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  -- We define the output vector by specifying the value for each entry `i`.
  Vector.ofFn (fun i =>
    -- For each output entry `i`, we compute a sum over all possible input indices `j`.
    Finset.sum Finset.univ (fun j =>
      -- The sum is only over `j` that are bitwise subsets of `i`.
      if (i.val &&& j.val = j.val) then
        -- The term is added or subtracted based on the parity of the difference
        -- in the number of set bits (Hamming weight).
        if (i.val.popCount - j.val.popCount) % 2 = 0 then
          p.get j -- Add if the difference is even
        else
          -p.get j -- Subtract if the difference is odd
      else
        0 -- If j is not a subset of i, the term is zero.
    )
  )

/-- The $O(4^n)$ specification for the zeta transform (the mirror of
`lagrangeToMonoSpec`).

For each output index `i`, this sums `p[j]` over every index `j` that is a bitwise subset
of `i` (`i &&& j = j`):
$$ (\text{monoToLagrangeSpec}\ p)[i]\ =\ \sum_{j \subseteq i} p[j]. $$

Provable equivalent to the fast `monoToLagrange` — see `monoToLagrange_eq_monoToLagrangeSpec`.
-/
def monoToLagrangeSpec (p : CMlPolynomial R n) : CMlPolynomialEval R n :=
  Vector.ofFn (fun i ↦
    Finset.sum Finset.univ (fun j ↦
      if (i.val &&& j.val = j.val) then p.get j else 0))

/--
Generates a list of indices representing a range of bit positions [l, r] in increasing order.
Used for optimized recursive transforms that operate on segments of variables.
Returns a list containing `l, l+1, ..., r`.
The result is used to fold over dimensions in `monoToLagrangeSegment` and `lagrangeToMonoSegment`.
-/
def forwardRange (n : ℕ) (r : Fin (n)) (l : Fin (r.val + 1)) : List (Fin n) :=
  let len := r.val - l.val + 1
  List.ofFn (fun (k : Fin len) =>
    let val := l.val + k.val
    have h_bound : val < n := by omega
    ⟨val, h_bound⟩
  )

lemma forwardRange_length (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    (forwardRange n r l).length = r.val - l.val + 1 := by
  unfold forwardRange
  simp only [List.length_ofFn]

lemma forwardRange_eq_of_r_eq (n : ℕ) (r1 r2 : Fin n) (h_r_eq : r1 = r2) (l : Fin (r1.val + 1)) :
    forwardRange n r1 l = forwardRange n r2 ⟨l, by omega⟩ := by
  subst h_r_eq
  rfl

lemma forwardRange_getElem (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (k : Fin (r.val - l.val + 1)) :
    (forwardRange n r l).get ⟨k, by
    rw [forwardRange]; simp only [List.length_ofFn]; omega⟩ = ⟨l.val + k, by omega⟩ := by
  unfold forwardRange
  simp only [List.get_eq_getElem]
  simp only [List.getElem_ofFn]

lemma forwardRange_succ_right_ne_empty (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_pred_le_ne_empty (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (h_l_gt_0 : l.val > 0) : forwardRange n r ⟨l.val - 1, by omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_dropLast (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    (forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩).dropLast
  = forwardRange n ⟨r, by omega⟩ ⟨l, by simp only [Fin.is_lt]⟩ := by
  apply List.ext_getElem
  · rw [List.length_dropLast, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_dropLast, forwardRange_length, add_tsub_cancel_right, Fin.eta] at h₁ h₂
    simp only [List.getElem_dropLast, Fin.eta]
    have hleft := forwardRange_getElem n
      ⟨r.val + 1, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    have hright := forwardRange_getElem n
      ⟨r.val, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    simp only [List.get_eq_getElem, Fin.eta] at hleft hright
    rw [hleft, hright]

lemma forwardRange_tail (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (h_l_gt_0 : l.val > 0) :
    (forwardRange n r ⟨l.val - 1, by omega⟩).tail = forwardRange n r l := by
  apply List.ext_getElem
  · rw [List.length_tail, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_tail, forwardRange_length, add_tsub_cancel_right] at h₁ h₂
    simp only [List.getElem_tail]
    have hleft := forwardRange_getElem n r ⟨l.val - 1, by omega⟩ (k:=⟨i + 1, by simp only; omega⟩)
    have hright := forwardRange_getElem n r l (k:=⟨i, by omega⟩)
    simp only [List.get_eq_getElem] at hleft hright
    rw [hleft, hright]
    rw [Fin.mk.injEq, Nat.add_comm i 1, ←Nat.add_assoc, Nat.sub_one_add_one (a:=l.val) (by omega)]

lemma forwardRange_0_eq_finRange (n : ℕ) [NeZero n] : forwardRange n ⟨n - 1, by
    have h_ne_zero : n ≠ 0 := NeZero.ne n
    omega
  ⟩ 0 = List.finRange n := by
  apply List.ext_get
  · rw [forwardRange_length, List.length_finRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero]
    have : n ≥ 1 := by
      exact NeZero.one_le
    simp_all only [ge_iff_le, Nat.sub_add_cancel]
  · intro i hi h₂
    have h_fr_get := forwardRange_getElem (n:=n) (r:=⟨n - 1, by grind⟩) (l:=0) (k:=⟨i, by
      rw [forwardRange_length] at hi
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero] at hi
      exact hi
    ⟩)
    simpa [forwardRange] using h_fr_get

/--
Performs the zeta-transform (coefficient to evaluation) on a segment of dimensions from `l` to `r`.
Iteratively applies `monoToLagrangeLevel` for each dimension in the range.
`0 ≤ l ≤ r < n`.
-/
def monoToLagrangeSegment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  let range := forwardRange n r l
  (range.foldl (fun acc h => monoToLagrangeLevel h acc))

/--

Performs the inverse zeta-transform (evaluation to coefficient) on a segment of dimensions

from `l` to `r`.

Iteratively applies `lagrangeToMonoLevel` for each dimension in the range (in reverse order).

`0 ≤ l ≤ r < n`.

-/
def lagrangeToMonoSegment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :

    Vector R (2 ^ n) → Vector R (2 ^ n) :=

  let range := forwardRange n r l

  (range.foldr (fun h acc => lagrangeToMonoLevel h acc))

lemma monoToLagrange_eq_monoToLagrangeSegment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
    have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  monoToLagrange n v = monoToLagrangeSegment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold monoToLagrange monoToLagrangeSegment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma lagrangeToMono_eq_lagrangeToMonoSegment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
    have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  lagrangeToMono n v = lagrangeToMonoSegment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold lagrangeToMono lagrangeToMonoSegment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma testBit_of_sub_two_pow_of_bit_1 {n i : ℕ} (h_testBit_eq_1 : (n).testBit i = true) :
    (n - 2^i).testBit i = false := by
  have h := Nat.testBit_false_eq_getBit_eq_0 (n:=n - 2^i) (k:=i)
  rw [h]
  have h_getBit_eq_0: Nat.getBit i (n - 2^i) = 0 := by
    rw [Nat.getBit_of_sub_two_pow_of_bit_1]
    simp only [↓reduceIte]
    rw [Nat.testBit_true_eq_getBit_eq_1] at h_testBit_eq_1
    exact h_testBit_eq_1
  exact h_getBit_eq_0

theorem lagrangeToMonoLevel_monoToLagrangeLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
    lagrangeToMonoLevel i (monoToLagrangeLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    have h_as_assoc := add_sub_assoc (a:=v[i1]'(by omega))
      (b:=v[i1 - 2 ^ i.val]'(h_id_lt)) (c:=v[i1 - 2 ^ i.val]'(h_id_lt))
    rw [h_as_assoc, sub_self, add_zero]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem monoToLagrangeLevel_lagrangeToMonoLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
    monoToLagrangeLevel i (lagrangeToMonoLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    rw [sub_add_cancel]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem mobius_apply_zeta_apply_eq_id (n : ℕ) [NeZero n] (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) : lagrangeToMonoSegment n r l (monoToLagrangeSegment n r l v) = v := by
  induction r using Fin.succRecOnSameFinType with
  | zero =>
    rw [lagrangeToMonoSegment, monoToLagrangeSegment, forwardRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero, tsub_self, zero_add,
      List.ofFn_succ, Fin.isValue, Fin.cast_zero, Nat.mod_succ, add_zero, Fin.mk_zero',
      Fin.val_cast, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
      List.foldr_cons, List.foldr_nil]
    exact lagrangeToMonoLevel_monoToLagrangeLevel_id v 0
  | succ r1 r1_lt_n h_r1 =>
    unfold lagrangeToMonoSegment monoToLagrangeSegment
    if h_l_eq_r: l.val = (r1 + 1).val then
      rw [forwardRange]
      simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ,
        List.foldl_cons, List.foldr_cons]
      simp_rw [h_l_eq_r]
      simp only [Fin.eta, tsub_self, List.ofFn_zero, List.foldl_nil, List.foldr_nil]
      exact lagrangeToMonoLevel_monoToLagrangeLevel_id v (r1 + 1)
    else
      have h_l_lt_r: l.val < (r1 + 1).val := by omega
      have h_r1_add_1_val: (r1 + 1).val = r1.val + 1 := by
        rw [Fin.val_add_one']; omega
      have h_range_ne_empty: forwardRange n (r1 + 1) l ≠ [] := by
        have h:= forwardRange_succ_right_ne_empty n
          (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [ne_eq] at h
        have h_r1_add_1: r1 + 1 = ⟨r1.val + 1, by omega⟩ := by
          exact Fin.eq_mk_iff_val_eq.mpr h_r1_add_1_val
        rw [forwardRange_eq_of_r_eq (r1:=r1 + 1) (r2:=⟨r1.val + 1, by omega⟩) (h_r_eq:=h_r1_add_1)]
        exact h
      rw [List.foldr_split_inner (h:=h_range_ne_empty)]
      rw [List.foldl_split_outer (h:=h_range_ne_empty)]
      rw [lagrangeToMonoLevel_monoToLagrangeLevel_id]
      have h_inductive := h_r1 (l := ⟨l, by exact Nat.lt_of_lt_of_eq h_l_lt_r h_r1_add_1_val⟩)
      rw [lagrangeToMonoSegment, monoToLagrangeSegment] at h_inductive
      simp only at h_inductive
      have h_range_droplast: (forwardRange n (r1 + 1) l).dropLast
        = forwardRange n r1 ⟨↑l, by omega⟩ := by
        have h := forwardRange_dropLast n (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [Fin.eta] at h
        convert h
      convert h_inductive

lemma zeta_apply_mobius_apply_eq_id (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) :
    monoToLagrangeSegment n r l (lagrangeToMonoSegment n r l v) = v := by
  induction l using Fin.predRecOnSameFinType with
  | last =>
    rw [lagrangeToMonoSegment, monoToLagrangeSegment, forwardRange]
    simp only [add_tsub_cancel_right, tsub_self, zero_add, List.ofFn_succ, Nat.add_one_sub_one,
      Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, Nat.mod_succ, add_zero, Fin.eta,
      Fin.val_cast, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      List.foldl_cons, List.foldl_nil]
    exact monoToLagrangeLevel_lagrangeToMonoLevel_id v r
  | succ l1 l1_gt_0 h_l1 =>
    unfold lagrangeToMonoSegment monoToLagrangeSegment
    have h_l1_sub_1_lt_r: (⟨l1.val - 1, by omega⟩: Fin (r.val + 1)).val < r.val := by
      simp only
      have h_l1 := l1.isLt
      apply Nat.lt_of_add_lt_add_right (n:=1)
      rw [Nat.sub_one_add_one (by omega)]
      omega
    have h_range_ne_empty: forwardRange n r ⟨l1.val - 1, by omega⟩ ≠ [] := by
      have h:= forwardRange_pred_le_ne_empty n
        (r:=⟨r, by omega⟩) (l:=⟨l1, by simp only; omega⟩) (by omega)
      simp only [ne_eq, h, not_false_eq_true]
    rw [List.foldr_split_outer (h:=h_range_ne_empty)]
    rw [List.foldl_split_inner (h:=h_range_ne_empty)]
    rw [monoToLagrangeLevel_lagrangeToMonoLevel_id]
    have h_inductive := h_l1
    rw [lagrangeToMonoSegment, monoToLagrangeSegment] at h_inductive
    simp only at h_inductive
    have h_range_tail: (forwardRange n r ⟨l1.val - 1, by omega⟩).tail = forwardRange n r l1 := by
      have h := forwardRange_tail n (r:=r) (l:=l1) (by omega)
      convert h
    convert h_inductive

/--
The equivalence between the monomial basis representation (`CMlPolynomial`)
and the Lagrange basis representation (`CMlPolynomialEval`) of a multilinear polynomial.
The forward map is `monoToLagrange` (zeta transform) and the inverse is `lagrangeToMono`
(inverse zeta transform/Mobius transform).
-/
def equivMonomialLagrangeRepr : CMlPolynomial R n ≃ CMlPolynomialEval R n where
  toFun := monoToLagrange n
  invFun := lagrangeToMono n
  left_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      let: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMonoSegment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrangeSegment (n:=n)]
      simp only [Fin.zero_eta]
      exact
        mobius_apply_zeta_apply_eq_id n
          ⟨n - 1, by have := NeZero.ne n; omega⟩
          0 v
  right_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      let: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMonoSegment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrangeSegment (n:=n)]
      exact
        zeta_apply_mobius_apply_eq_id n
          ⟨n - 1, by have := NeZero.ne n; omega⟩
          ⟨0, by have := NeZero.ne n; omega⟩
          v

end CMlPolynomial
end CompPoly
end
end

-- ===== from `LvmCpPowerBatching` =====

section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
variable {R : Type*} [CommRing R] {J μ : ℕ}

/-- Batch weight tables pointwise with the same powers as their targets. -/
def batchWeight (w : Fin J → CMlPolynomialEval R μ) (ρ : R) : CMlPolynomialEval R μ :=
  Vector.ofFn fun x ↦ powerBatch (fun j ↦ (w j)[x]) ρ

/-- Pairing is linear in a family of weights on the same arbitrary committed column. -/
theorem pairing_batchWeight (w : Fin J → CMlPolynomialEval R μ)
    (q : CMlPolynomialEval R μ) (ρ : R) :
    sumCube (hadamard (batchWeight w ρ) q) =
      powerBatch (fun j ↦ sumCube (hadamard (w j) q)) ρ := by
  simp only [sumCube, hadamard, batchWeight, Fin.getElem_fin, Vector.getElem_ofFn, powerBatch]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

/-- Multilinear extension commutes with power batching, at every point, including off the cube. -/
theorem evalMle_batchWeight (w : Fin J → CMlPolynomialEval R μ) (ρ : R) (r : Vector R μ) :
    evalMle (batchWeight w ρ) r = powerBatch (fun j ↦ evalMle (w j) r) ρ := by
  simp only [evalMle_eq_sum, batchWeight, Fin.getElem_fin, Vector.getElem_ofFn, powerBatch]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
variable {R : Type*} [CommRing R] {J μ : ℕ}

/-- A false singleton has no successful challenge; a zero challenge cannot erase its error. -/
theorem singleton_batch_ne (a v : Fin 1 → R) (h : a 0 ≠ v 0) (ρ : R) :
    powerBatch a ρ ≠ powerBatch v ρ := by
  simpa [powerBatch] using h

end
end LeanVM.Protocol
end

-- ===== from `LvmGrandProductSecurity` =====

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
variable {R : Type}

/-- The challenges of `c` from offset `off` on, placed at coordinates `0, 1, …`: the part-way point
a table on the last coordinates of a longer point sees while that point is drawn. -/
def Partial.ofSuffix (off : ℕ) {j : ℕ} (c : Vector R j) : Partial R :=
  fun i ↦ if h : off + i < j then some c[off + i] else Option.none

/-- Before the offset is reached, nothing is fixed. -/
theorem Partial.ofSuffix_of_le (off : ℕ) {j : ℕ} (c : Vector R j) (h : j ≤ off) :
    Partial.ofSuffix off c = Partial.empty := by
  funext i
  simp only [Partial.ofSuffix, Partial.empty]
  rw [dite_eq_right (by omega)]

/-- A challenge before the offset fixes nothing. -/
theorem Partial.ofSuffix_push_of_lt (off : ℕ) {j : ℕ} (c : Vector R j) (x : R) (h : j < off) :
    Partial.ofSuffix off (c.push x) = Partial.ofSuffix off c := by
  rw [Partial.ofSuffix_of_le _ _ (by omega), Partial.ofSuffix_of_le _ _ h.le]

/-- A challenge past the offset fixes one more coordinate. -/
theorem Partial.ofSuffix_push_of_le (off : ℕ) {j : ℕ} (c : Vector R j) (x : R) (h : off ≤ j) :
    Partial.ofSuffix off (c.push x) =
      Function.update (Partial.ofSuffix off c) (j - off) (some x) := by
  funext i
  by_cases hi : i = j - off
  · subst hi
    simp only [Partial.ofSuffix, Function.update_self]
    rw [dite_eq_left (by omega), Vector.getElem_push, dite_eq_right (by omega)]
  · rw [Function.update_of_ne hi]
    simp only [Partial.ofSuffix]
    by_cases hlt : off + i < j
    · rw [dite_eq_left (by (clear * - hlt; omega)), dite_eq_left hlt, Vector.getElem_push, dite_eq_left hlt]
    · rw [dite_eq_right (by omega), dite_eq_right hlt]

/-- The coordinate the next challenge past the offset will fix is free. -/
theorem Partial.ofSuffix_next (off : ℕ) {j : ℕ} (c : Vector R j) :
    Partial.ofSuffix off c (j - off) = Option.none := by
  simp only [Partial.ofSuffix]
  rw [dite_eq_right (by omega)]

/-- With every coordinate past the offset drawn, the part-way point fixes the suffix. -/
theorem Partial.ofSuffix_all {k : ℕ} (off : ℕ) (c : Vector R (off + k)) (i : ℕ) (hi : i < k) :
    Partial.ofSuffix off c i = some c[off + i] := by
  simp only [Partial.ofSuffix]
  rw [dite_eq_left (by omega)]

end
end LeanVM.Protocol
end
end

section
section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
variable {R : Type}
variable [CommRing R]

/-- Flip bit `k` of a cube index to `β`: the cube point that differs from `b` in coordinate `k`
at most, and has `β` there. -/
private def setBitIndex {n : ℕ} (b : Fin (2 ^ n)) (k : ℕ) (hk : k < n) (β : Bool) : Fin (2 ^ n) :=
  ⟨b.val ^^^ (if b.val.testBit k == β then 0 else 2 ^ k),
    Nat.xor_lt_two_pow b.isLt (by
      split
      · exact Nat.two_pow_pos n
      · exact Nat.pow_lt_pow_right (by norm_num) hk)⟩

private theorem testBit_setBitIndex {n : ℕ} (b : Fin (2 ^ n)) (k : ℕ) (hk : k < n) (β : Bool)
    (i : ℕ) : (setBitIndex b k hk β).val.testBit i = if i = k then β else b.val.testBit i := by
  simp only [setBitIndex, Nat.testBit_xor]
  by_cases hi : i = k
  · subst hi
    simp only [↓reduceIte]
    split <;> rename_i h
    · simp_all
    · cases β <;> cases hb : b.val.testBit i <;> simp_all [Nat.testBit_two_pow_self]
  · simp only [hi, ↓reduceIte]
    split <;> simp [Ne.symm hi]

/-- A completion with coordinate `k` free and then set to `0` or `1` is another completion. -/
private theorem Partial.point_set_bool {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n)
    (hσ : σ k = Option.none) (b : Fin (2 ^ n)) (β : Bool) :
    (σ.point b).set k (if β then 1 else 0) = σ.point (setBitIndex b k hk β) := by
  apply Vector.ext
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    simp [Partial.point, hσ, boolVec, testBit_setBitIndex]
  · rw [Vector.getElem_set_ne hk hj (Ne.symm hjk)]
    simp [Partial.point, boolVec, testBit_setBitIndex, hjk]

end
end LeanVM.Protocol
end
end

section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
namespace Gkr
variable {F : Type}
variable [Field F] [Finite F] [DecidableEq F] {X : Type} {ι : Type} {O : ι → Type}
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))
section Layer
variable (ρ m : ℕ)
variable {S : Type} (inp : S → LayerStmt X F nside m)

/-- A round's count (lvm: new, what the cut `layerStepSecurity` charged each round of the layer's
sumcheck through `SumcheckRound.roundsSecurity`): a recorded polynomial that passes the check has
at most `2 ^ ρ` bad challenges. -/
theorem card_round_badChallenge_le (T : RiderTrack μ riders ρ m) {j : ℕ} (hj : j < m)
    (p : SumcheckRound.MidStmt (LayerX X F nside m) F j (2 ^ ρ)) (o : ∀ i, O i)
    (hc : SumcheckRound.check j (familyT nside μ leaves riders ρ m T).weight p.1 p.2 = true) :
    Nat.card {x // SumcheckRound.badChallenge j (familyT nside μ leaves riders ρ m T) p o x} ≤
      2 ^ ρ :=
  SumcheckRound.card_badChallenge_le j _ (familyT_consistent nside μ leaves riders ρ m T)
    (familyT_sound nside μ leaves riders ρ m T) hj p o hc

end Layer
end Gkr
end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
namespace Gkr
variable {F : Type}
variable [Field F] [Finite F] [DecidableEq F] {X : Type} {ι : Type} {O : ι → Type}
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))
section Layer
variable (ρ m : ℕ)
variable {S : Type} (inp : S → LayerStmt X F nside m)

omit [DecidableEq F] in
/-- The last combination challenge's count (lvm: new, what the cut `interpolateSecurity` charged
its last challenge at `1 / |F|`): from a statement outside the relation after `ρ - 1` combination
challenges, at most one challenge lands the interpolated statement in the step's output
relation. -/
theorem card_interpDone_le {ρ' : ℕ} (T : RiderTrack μ riders (ρ' + 1) m)
    (s : InterpStmt X F nside m (ρ' + 1) ρ') (o : ∀ i, O i)
    (hs : ((s, o), ()) ∉ childRelT nside μ leaves riders (ρ' + 1) m T ρ') :
    Nat.card {c // ((interpDone nside (ρ' + 1) m (interpNext nside (ρ' + 1) m s c), o), ()) ∈
      stepOutT nside μ leaves riders (ρ' + 1) m T} ≤ 1 :=
  (Finite.card_le_of_embedding (Subtype.impEmbedding _ _ fun _ hc ↦
    (interpDone_mem_stepOutT_iff nside μ leaves riders (ρ' + 1) m T _ o).mp hc)).trans
    (card_interpNext_le nside μ leaves riders (ρ' + 1) m T s o hs)

end Layer
end Gkr
end
end LeanVM.Protocol
end

section
namespace LeanVM.Protocol
open CompPoly CMlPolynomialEval
section
namespace Gkr
variable {F : Type}
variable [Field F] [Finite F] [DecidableEq F] {X : Type} {ι : Type} {O : ι → Type}
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))

/-- The input relation of `k` radix-four steps from layer `m`: the layer relation, or, with no
step left, the output relation read at layer `m`. -/
def stepsIn : (k m : ℕ) → m + 2 * k = μ →
    Set ((LayerStmt X F nside m × ∀ i, O i) × Unit)
  | 0, m, h =>
    {p | (∀ r ∈ riders p.1.1.1 p.1.2, evalMle r.2 (lowPoint (Vector.cast h p.1.1.2.1) r.1) = 0) ∧
      ∀ s, evalMle (layerTable (leaves p.1.1.1 p.1.2 s) m) p.1.1.2.1 = p.1.1.2.2 s}
  | _ + 1, m, _ => layerRel nside μ leaves riders m

omit [Finite F] [DecidableEq F] in
/-- With no step left, the input relation is the output relation across the equality of
layers. -/
theorem stepsIn_zero_iff (m : ℕ) (h : m + 2 * 0 = μ) (s : LayerStmt X F nside m)
    (o : ∀ i, O i) :
    ((s, o), ()) ∈ stepsIn nside μ leaves riders 0 m h ↔
      (((s.1, (Vector.cast (by omega) s.2.1, s.2.2)), o), ()) ∈ relOut nside μ leaves riders := by
  have hm : m = μ := by omega
  subst hm
  simp only [stepsIn, relOut, Vector.cast_rfl, layerTable_self, Set.mem_ofPred_eq]
  exact and_comm

omit [Finite F] [DecidableEq F] in
/-- With no layer at all, the roots are in the output relation read at layer `0` exactly when
they are in the input relation: a rider on no variable is one value, its extension at the empty
point. -/
theorem relIn_iff_stepsIn_zero (h : 0 + 2 * 0 = μ) (s : X × (Fin nside → F))
    (o : ∀ i, O i) :
    ((s, o), ()) ∈ relIn nside μ leaves riders ↔
      ((rootStmt nside s, o), ()) ∈ stepsIn nside μ leaves riders 0 0 h := by
  have hμ : μ = 0 := by omega
  subst hμ
  simp only [stepsIn, Set.mem_ofPred_eq]
  refine and_congr ?_ (forall_congr' fun t ↦ ?_)
  · refine forall₂_congr fun r hr ↦ ?_
    obtain ⟨⟨τ, hτ⟩, t⟩ := r
    have hτ0 : τ = 0 := by (clear * - hτ; omega)
    subst hτ0
    refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
    · rw [evalMle_zero]
      exact h ⟨0, Nat.one_pos⟩
    · rw [evalMle_zero] at h
      obtain ⟨i, hi⟩ := i
      have hi0 : i = 0 := by
        have : i < 1 := hi
        (clear * - hτ this; omega)
      subst hi0
      exact h
  · show s.2 t = ∏ i : Fin (2 ^ 0), (leaves s.1 o t)[i] ↔
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
end

-- ===== from `LvmVEqArith` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_foldl_add tE_foldl_mul formE)

theorem toExt3_gen : FE.toExt3 Lvm.gen = Verifier.gen := toExt3_eOfNat 2

theorem kToNat_toBF64 (a : FK) : Verifier.kToNat (FK.toBF64 a) = Lvm.kToNat a := rfl

theorem bitLength_eq (n : ℕ) : Lvm.bitLength n = Verifier.bitLength n := rfl

theorem log2Ceil_eq (n : ℕ) : Lvm.log2Ceil n = Verifier.log2Ceil n := rfl

theorem toExt3_gpow (i : ℕ) : FE.toExt3 (Lvm.gpow i) = Verifier.gpow i := by
  rw [Lvm.gpow, FE.toExt3_npow, toExt3_gen]; rfl

theorem toExt3_frob (k : ℕ) (a : FE) : FE.toExt3 (FE.frob k a) = FE.toExt3 a ^ (2 ^ k) := by
  rw [FE.frob_eq_pow, FE.toExt3_npow]

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_foldl_add tE_foldl_mul formE)

theorem toExt3_paddingWeight (point : List FE) (n : ℕ) :
    FE.toExt3 (Lvm.paddingWeight point n) = Verifier.paddingWeight (point.map FE.toExt3) n := by
  unfold Lvm.paddingWeight Verifier.paddingWeight
  rw [tE_mul, tE_add, tE_one, toExt3_eOfNat, List.length_map, zipIdx_map_toExt3]
  congr 1
  generalize point.zipIdx = l
  suffices h : ∀ acc : FE, FE.toExt3 (l.foldl (fun pad (r, k) =>
      let b := Lvm.eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) acc) = (l.map (Prod.map FE.toExt3 id)).foldl (fun pad (r, k) =>
      let b := Verifier.eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) (FE.toExt3 acc) by rw [h, tE_one]
  induction l with
  | nil => intro acc; rfl
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, ih, Prod.map_fst, Prod.map_snd, id_eq, tE_add, tE_mul, tE_one,
      toExt3_eOfNat]

theorem toExt3_indexMleFrom (gp : FE) (l : List FE) (acc : FE) :
    FE.toExt3 (Lvm.indexMleFrom gp l acc) =
      Verifier.indexMleFrom (FE.toExt3 gp) (l.map FE.toExt3) (FE.toExt3 acc) := by
  induction l generalizing gp acc with
  | nil => rfl
  | cons r l ih =>
    simp only [Lvm.indexMleFrom, Verifier.indexMleFrom, List.map_cons, ih, FE.toExt3_npow, tE_mul, tE_add,
      tE_one]

theorem toExt3_indexMle (point : List FE) :
    FE.toExt3 (Lvm.indexMle point) = Verifier.indexMle (point.map FE.toExt3) := by
  rw [Lvm.indexMle, toExt3_indexMleFrom, toExt3_gen, tE_one]; rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_foldl_add tE_foldl_mul formE)

theorem map_stackPoint (p : Lvm.Placement) (point : List FE) (stackLog : ℕ) :
    (p.stackPoint point stackLog).map FE.toExt3 = (plE p).stackPoint (point.map FE.toExt3) stackLog := by
  simp only [Lvm.Placement.stackPoint, Verifier.Placement.stackPoint, plE, List.map_append, map_selectorPoint]

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_foldl_add tE_foldl_mul formE)

/-- A native term list over `E`. -/
def termsE (ts : List (List ℕ × FE)) : List (List ℕ × E) := ts.map fun t ↦ (t.1, FE.toExt3 t.2)

theorem formE_terms (f : Lvm.Form) : (formE f).terms = termsE f.terms := rfl

theorem termsE_addTerm (ts : List (List ℕ × FE)) (m : List ℕ) (c : FE) :
    termsE (Lvm.addTerm ts m c) = Verifier.addTerm (termsE ts) m (FE.toExt3 c) := by
  induction ts with
  | nil => simp [termsE, Lvm.addTerm, Verifier.addTerm]
  | cons t ts ih =>
    obtain ⟨m', c'⟩ := t
    by_cases h : m' = m
    · simp [termsE, Lvm.addTerm, Verifier.addTerm, h]
    · simp only [termsE] at ih
      simp [termsE, Lvm.addTerm, Verifier.addTerm, h, ih]

theorem formE_addScaled (f other : Lvm.Form) (w : FE) :
    formE (f.addScaled other w) = (formE f).addScaled (formE other) (FE.toExt3 w) := by
  suffices h : ∀ ts acc : List (List ℕ × FE),
      termsE (ts.foldl (fun acc t ↦ Lvm.addTerm acc t.1 (w * t.2)) acc) =
        (termsE ts).foldl (fun acc t ↦ Verifier.addTerm acc t.1 (FE.toExt3 w * t.2)) (termsE acc) from
    congrArg Verifier.Form.mk (h other.terms f.terms)
  intro ts
  induction ts with
  | nil => intro acc; rfl
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons, ih, termsE_addTerm, tE_mul]
    rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_foldl_add tE_foldl_mul formE)

theorem formE_const (v : FE) : formE (Lvm.Form.const v) = Verifier.Form.const (FE.toExt3 v) := rfl

theorem formE_col (i e : ℕ) : formE (Lvm.Form.col i e) = Verifier.Form.col i e := by
  simp [formE, Lvm.Form.col, Verifier.Form.col, toExt3_gpow]

end Lvm.VEq
end

-- ===== from `LvmAccNodeFold` =====

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol.Compile
section Ref
variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)
variable {cap occ shp} {sig : ByteArray}

theorem RefAtP.toRefAt {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    {Q : β → Prop} (h : RefAtP cap occ shp sig d P R Q) (hQ : ∀ b, Q b) : RefAt cap occ shp sig d P R :=
  fun s hok ↦ h s hok (hQ _)

end Ref
end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol.Compile
section Ref
variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)
variable {cap occ shp} {sig : ByteArray}

/-- **A language `require` justified by the promise** on the native value. -/
theorem RefAtP.require_ret {α β : Type} {b : β} {a : α} {q : Prop} [Decidable q] {R : β → α → Prop}
    {Q : β → Prop} (hq : Q b → q) (hR : R b a) :
    RefAtP cap occ shp sig (Pure.pure b : DM β) ((VerifierProgram.require q).bind fun _ ↦ VerifierProgram.ret a)
      R Q := by
  intro s _ hQ
  have e : (VerifierProgram.require q).bind (fun _ ↦ VerifierProgram.ret a) = VerifierProgram.ret a := by
    simp only [VerifierProgram.require, hq hQ, ↓reduceIte]; rfl
  rw [e]
  exact ⟨a, rfl, rfl, rfl, hR⟩

end Ref
end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open LeanVM.Parameters LeanVM.Protocol.Compile
section Ref
variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)
variable {cap occ shp} {sig : ByteArray}

theorem runD_bind_pure {β γ : Type} (d : DM β) (a : γ) (sig : ByteArray) (s : RS) :
    (runD (d >>= fun _ ↦ Pure.pure a) sig s).1 = a := rfl

theorem runD_bind_pure_snd {β γ δ : Type} (d : DM β) (f : β → γ) (a : δ) (sig : ByteArray) (s : RS) :
    (runD (d >>= fun k ↦ Pure.pure (f k, a)) sig s).1.2 = a := rfl

end Ref
end Lvm.VEq
end
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)

theorem find?_eq_of_unique {α : Type} {l : List α} {p : α → Bool} {e : α} (he : e ∈ l) (hp : p e = true)
    (hu : ∀ y ∈ l, p y = true → y = e) : l.find? p = some e := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨e, he, hp⟩)
  rw [hy, hu y (List.mem_of_find?_eq_some hy) (List.find?_some hy)]

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)
section Claims
variable (T : List Tab) (evs : List (List FE × List FE))

open LeanVM.Protocol.Verifier in
/-- Every claim of the native evaluations is on column `(j, i)` with the `j`-th point and value. -/
theorem mem_claimsOfEvs {c : Verifier.ColumnClaim} (hc : c ∈ claimsOfEvs T evs) :
    ∃ j i, ∃ (hj : j < T.length) (hje : j < evs.length), i < evs[j].2.length ∧
      c = ⟨(globalColumnBases (vTables T)).getD j 0 + i, evs[j].1.map FE.toExt3,
        FE.toExt3 (evs[j].2.getD i 0)⟩ := by
  unfold claimsOfEvs at hc
  obtain ⟨⟨⟨t, pe⟩, j⟩, hx, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨v, i⟩, hvi, rfl⟩ := List.mem_map.mp hc
  have hx' := List.mem_zipIdx_iff_getElem?.mp hx
  rw [List.getElem?_zip_eq_some] at hx'
  obtain ⟨h1, h2⟩ := hx'
  have hj : j < T.length := (List.getElem?_eq_some_iff.mp h1).1
  have hje : j < evs.length := (List.getElem?_eq_some_iff.mp h2).1
  have ht : evs[j] = pe := (List.getElem?_eq_some_iff.mp h2).2
  have hv := List.mem_zipIdx_iff_getElem?.mp hvi
  have hi : i < pe.2.length := (List.getElem?_eq_some_iff.mp hv).1
  refine ⟨j, i, hj, hje, by rw [ht]; exact hi, ?_⟩
  have hv' : pe.2[i]? = some v := hv
  have hvd : pe.2.getD i 0 = v := by rw [List.getD_eq_getElem?_getD, hv', Option.getD_some]
  simp only [ht, hvd]

open LeanVM.Protocol.Verifier in
/-- **The claim of column `(j, i)`** among the native evaluations' claims (AC-S's `claimAt` by the
global column number). -/
theorem claimAt_claimsOfEvs (hl : EvLen T evs) {j i : ℕ} (hj : j < T.length) (hje : j < evs.length)
    (hi : i < T[j].w) :
    Lvm.Acc.claimAt (claimsOfEvs T evs) ((globalColumnBases (vTables T)).getD j 0 + i) =
      ⟨(globalColumnBases (vTables T)).getD j 0 + i, evs[j].1.map FE.toExt3,
        FE.toExt3 (evs[j].2.getD i 0)⟩ := by
  unfold Lvm.Acc.claimAt
  rw [find?_eq_of_unique (e := ⟨(globalColumnBases (vTables T)).getD j 0 + i, evs[j].1.map FE.toExt3,
      FE.toExt3 (evs[j].2.getD i 0)⟩), Option.getD_some]
  · unfold claimsOfEvs
    refine List.mem_flatMap.mpr ⟨((T[j], evs[j]), j), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hje⟩
    · refine List.mem_map.mpr ⟨(evs[j].2.getD i 0, i), ?_, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?]
      have hi' : i < evs[j].2.length := by rw [hl j hj hje]; exact hi
      rw [List.getElem?_eq_getElem hi', List.getD_eq_getElem _ _ hi']
  · simp
  · intro y hy hp
    obtain ⟨j', i', hj', hje', hi', rfl⟩ := mem_claimsOfEvs T evs hy
    simp only [beq_iff_eq] at hp
    have h1 := Lvm.M3.colLoc_raw T hj' (by rw [← hl j' hj' hje']; exact hi')
    rw [hp, Lvm.M3.colLoc_raw T hj hi, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rfl

theorem mem_fixColsR_idx {pt : ℕ} {c : FixCol} (hc : c ∈ fixColsR T pt) :
    ∃ hj : c.tab < T.length, c.col < T[c.tab].w := by
  unfold fixColsR at hc
  obtain ⟨⟨t, j⟩, htj, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨src, i⟩, hsi, hc⟩ := List.mem_filterMap.mp hc
  have ht := List.mem_zipIdx_iff_getElem?.mp htj
  have hs := List.mem_zipIdx_iff_getElem?.mp hsi
  obtain ⟨hj, htj'⟩ := List.getElem?_eq_some_iff.mp ht
  cases src with
  | com _ _ => simp at hc
  | fix f e =>
    simp only at hc
    split_ifs at hc
    obtain rfl := Option.some.inj hc
    refine ⟨hj, ?_⟩
    simp only [Tab.w, htj']
    exact (List.getElem?_eq_some_iff.mp hs).1

/-- **The sent fixed evaluations over `E`** (`yOwnV`'s list) are V_S's. -/
theorem fixSentV_eq (hl : EvLen T evs) (hn : evs.length = T.length) (pt : ℕ) :
    ((fixColsR T pt).map fun c ↦ (Lvm.Acc.claimAt (claimsOfEvs T evs) (Lvm.Acc.gcol T c)).value) =
      (fixSentR T pt evs).map FE.toExt3 := by
  unfold fixSentR
  rw [List.map_map]
  refine List.map_congr_left fun c hc ↦ ?_
  obtain ⟨hj, hi⟩ := mem_fixColsR_idx T hc
  rw [Lvm.Acc.gcol, claimAt_claimsOfEvs T evs hl hj (by omega) hi, Function.comp_apply,
    List.getD_eq_getElem evs _ (by omega)]

/-- **`PUB`'s check over `E`** from V_S's. -/
theorem pubOkV_of (hl : EvLen T evs) (hn : evs.length = T.length) {pt : ℕ} (hpt : pt < T.length)
    (hw : 0 < T[pt].w) {pub : Pub} (h : pubCheckR pt pub evs = true) :
    Lvm.Acc.pubOkV T pt pub (claimsOfEvs T evs) = true := by
  unfold Lvm.Acc.pubOkV
  rw [claimAt_claimsOfEvs T evs hl hpt (by omega) hw]
  unfold pubCheckR M3.pubCheckRW at h
  rw [List.getD_eq_getElem _ _ (by omega)] at h
  simp only [List.map_map, Function.comp_def, FE.ofExt3_toExt3, List.map_id', decide_eq_true_eq]
  exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq h)

/-- The "longest so far" step. -/
def lstep {β : Type} (r p : List β) : List β := if r.length < p.length then p else r

theorem lstep_idem {β : Type} (r p : List β) : lstep (lstep r p) p = lstep r p := by
  unfold lstep; split_ifs <;> simp_all

theorem lstep_map (r p : List FE) : lstep (r.map FE.toExt3) (p.map FE.toExt3) = (lstep r p).map FE.toExt3 := by
  unfold lstep; simp only [List.length_map]; split_ifs <;> rfl

/-- A nonempty run of claims on one point folds to one step. -/
theorem foldl_rep (P : List E) : ∀ (l : List Verifier.ColumnClaim) (r : List E), l ≠ [] →
    (∀ c ∈ l, c.point = P) → l.foldl (fun r c ↦ lstep r c.point) r = lstep r P
  | [], _, h, _ => absurd rfl h
  | [c], r, _, hc => by simp [hc c (by simp)]
  | c :: c' :: l, r, _, hc => by
    rw [List.foldl_cons, hc c (by simp), foldl_rep P (c' :: l) _ (by simp)
      (fun d hd ↦ hc d (List.mem_cons_of_mem _ hd)), lstep_idem]

theorem foldl_blocks {X : Type} (F : X → List Verifier.ColumnClaim) (P : X → List FE) :
    ∀ (L : List X) (r : List FE), (∀ x ∈ L, F x ≠ [] ∧ ∀ c ∈ F x, c.point = (P x).map FE.toExt3) →
      L.foldl (fun acc x ↦ (F x).foldl (fun r c ↦ lstep r c.point) acc) (r.map FE.toExt3) =
        ((L.map P).foldl lstep r).map FE.toExt3
  | [], _, _ => rfl
  | x :: L, r, h => by
    rw [List.foldl_cons, foldl_rep _ _ _ (h x (by simp)).1 (h x (by simp)).2, lstep_map,
      foldl_blocks F P L _ fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- **The table point over `E`** is V_S's (every table has a column). -/
theorem tablePointV_eq' (hl : EvLen T evs) (hn : evs.length = T.length) (hw : ∀ t ∈ T, 0 < t.w) :
    Lvm.Acc.tablePointV (claimsOfEvs T evs) = (tablePoint evs).map FE.toExt3 := by
  have hT : tablePoint evs = (evs.map (·.1)).foldl lstep [] := by
    unfold tablePoint; rw [List.foldl_map]; rfl
  have hE : Lvm.Acc.tablePointV (claimsOfEvs T evs) =
      (claimsOfEvs T evs).foldl (fun r c ↦ lstep r c.point) (([] : List FE).map FE.toExt3) := rfl
  rw [hT, hE]
  unfold claimsOfEvs
  rw [List.foldl_flatMap, foldl_blocks _ (fun x ↦ x.1.2.1)]
  · congr 2
    have e1 : ((T.zip evs).zipIdx.map fun x ↦ x.1.2.1) = ((T.zip evs).zipIdx.map Prod.fst).map
        (·.2.1) := by rw [List.map_map]; rfl
    rw [e1, List.zipIdx_map_fst, show ((T.zip evs).map fun x ↦ x.2.1) = ((T.zip evs).map Prod.snd).map
        (·.1) by rw [List.map_map]; rfl, List.map_snd_zip (by omega)]
  · intro x hx
    have hx' := List.mem_zipIdx_iff_getElem?.mp hx
    rw [List.getElem?_zip_eq_some] at hx'
    obtain ⟨h1, h2⟩ := hx'
    obtain ⟨hj, ht⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hje, he⟩ := List.getElem?_eq_some_iff.mp h2
    refine ⟨?_, fun c hc ↦ ?_⟩
    · have hlen : x.1.2.2.length = T[x.2].w := by rw [← he]; exact hl _ hj hje
      have hpos := hw _ (List.getElem_mem hj)
      intro hnil
      rw [List.map_eq_nil_iff, List.zipIdx_eq_nil_iff] at hnil
      rw [hnil] at hlen
      simp at hlen
      omega
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
      rfl

end Claims
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)

theorem ValP.any {β β' : Type} {d : DM β} {d' : β → DM β'} {P' : β' → Prop}
    (h' : ∀ b, ValP (d' b) P') : ValP (d >>= d') P' :=
  fun sig s ↦ h' _ sig _

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)

theorem RefAt.and_valP {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} {α β : Type}
    {d : DM β} {P : VerifierProgram α} {R : β → α → Prop} {V : β → Prop} (h : RefAt cap occ shp sig d P R)
    (hv : ValP d V) : RefAt cap occ shp sig d P fun b a ↦ R b a ∧ V b :=
  fun s hok ↦ by
    obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
    exact ⟨a, h1, h2, h3, h4, hv sig s⟩

theorem valP_tableTerms (cp fp point : List FE) :
    ∀ (rows : List (TableSpec × List Lvm.Form × FE)) (cursor : ℕ) (final : FE),
      ValP (Lvm.tableTerms cp fp point rows cursor final) fun x ↦ x.2.length = rows.length
  | [], _, _ => ValP.pure rfl
  | (t, fs, w) :: rows, cursor, final => by
    unfold Lvm.tableTerms
    refine ValP.any fun ev ↦ (valP_tableTerms cp fp point rows _ _).bind fun x hx ↦ ?_
    obtain ⟨f, rs⟩ := x
    exact ValP.pure (by simpa using hx)

theorem length_tableWeightsN (heights : List ℕ) (eqp point : List FE) :
    (Lvm.tableWeights heights eqp point).length = heights.length := by
  unfold Lvm.tableWeights
  suffices h : ∀ (l : List (FE × ℕ)) (acc : List FE), acc.length = heights.length →
      (l.foldl (fun weights (x : FE × ℕ) ↦ List.zipWith (fun weight height ↦
        weight * if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1) weights heights) acc).length =
        heights.length from h _ _ (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x l ih => intro acc h; exact ih _ (by simp [h])

theorem valP_tableSumcheck (rounds : ℕ) (tables : List TableSpec) (fs : List (List Lvm.Form))
    (cp fp eqp : List FE) (target : FE) (hfs : tables.length ≤ fs.length) :
    ValP (Lvm.tableSumcheck rounds tables fs cp fp eqp target) fun evs ↦ evs.length = tables.length := by
  unfold Lvm.tableSumcheck
  refine ValP.any fun x ↦ ?_
  obtain ⟨ch, claim⟩ := x
  refine (valP_tableTerms _ _ _ _ _ _).bind fun y hy ↦ ?_
  obtain ⟨fin, evs⟩ := y
  refine ValP.any fun _ ↦ ValP.pure ?_
  simp only [List.length_zip, length_tableWeightsN, List.length_map] at hy
  simp only [hy]
  omega

theorem valP_dBus (p : Params) (tabs : Pub → List Tab) (pub : Pub) :
    ValP (dBus p (M3.real p tabs) pub) fun pb ↦ pb.2.forms.length = (sumcheckTabs (tabs pub)).length := by
  unfold dBus
  refine ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.any fun x ↦ ?_
  obtain ⟨cr, pt, vs⟩ := x
  refine ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.pure ?_
  show (busFinalR _ _).forms.length = _
  simp [busFinalR]

/-- **Phases 2–3 with the evaluations' count** (every sumcheck table's point and values). -/
theorem ref_busTabL (sig : ByteArray) (tabs : Pub → List M3.Tab) (pub : Pub) (F : Fit P20 (tabs pub)) :
    Ref20 sig (dBus P20 (M3.real P20 tabs) pub >>= fun pb ↦
        dTab P20 (M3.real P20 tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev))
      (M3.lvmBusTableProg (M3.vTables (sumcheckTabs (tabs pub))) (M3.vLayout (sumcheckTabs (tabs pub)))
        P20.busDepth (M3.busResV (sumcheckTabs (tabs pub))))
      fun r cl ↦ TabRel (sumcheckTabs (tabs pub)) r cl ∧ r.2.length = (sumcheckTabs (tabs pub)).length :=
  RefAt.and_valP (ref_busTab sig tabs pub F) <| (valP_dBus P20 tabs pub).bind fun pb hpb ↦ by
    have hT : ValP (dTab P20 (M3.real P20 tabs) pub pb.1 pb.2)
        fun ev ↦ ev.length = (sumcheckTabs (tabs pub)).length := by
      unfold dTab
      refine ValP.any fun _ ↦ ?_
      have h := valP_tableSumcheck P20.tableRounds ((M3.real P20 tabs).tables pub) pb.2.forms
      simp only [real_tables, List.length_map] at h ⊢
      exact h _ _ _ _ (by rw [hpb])
    exact hT.bind fun ev hev ↦ ValP.pure hev

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)
section Fold
variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

theorem real_pubCheck (p : Params) (tabs : Pub → List Tab) (pub : Pub) (evs : List (List FE × List FE)) :
    (M3.real p tabs).pubCheck pub evs = pubCheckR p.pubTab pub evs := rfl

theorem real_fixSent (p : Params) (tabs : Pub → List Tab) (pub : Pub) (evs : List (List FE × List FE)) :
    (M3.real p tabs).fixSent pub evs = fixSentR (sumcheckTabs (tabs pub)) p.pubTab evs := rfl

theorem monoD_accFold (p : Params) (m : M3) (pub : Pub) (evs : List (List FE × List FE)) :
    MonoD (accFold p m pub evs) :=
  (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

/-- **Phase 3b refines `accProgV`** under the promise that the folded claim holds (`AccOk`, which
V_S checks after the run): `PUB`'s check, the line polynomial's values at 0 and 1, the zero scalar,
and `Φ̃(line(t)) = h(t)` hold over `E` wherever they hold natively. -/
theorem ref_accFold (tabs : Pub → List Tab) (pub : Pub) (evs : List (List FE × List FE))
    (hl : EvLen (sumcheckTabs (tabs pub)) evs) (hn : evs.length = (sumcheckTabs (tabs pub)).length)
    (hpt : P20.pubTab < (sumcheckTabs (tabs pub)).length)
    (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w) :
    RefAtP cap occ shp sig (accFold P20 (M3.real P20 tabs) pub evs)
      (Lvm.Acc.accProgV P20 tabs pub (claimsOfEvs (sumcheckTabs (tabs pub)) evs)) (fun _ _ ↦ True)
      (fun a ↦ AccOk P20 (M3.real P20 tabs) pub a = true) := by
  unfold accFold Lvm.Acc.accProgV Lvm.Acc.accProg
  refine RefAtP.require_left (fun _ ↦ (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun hpc ↦ ?_
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    ((ref_samples _).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro κ _ rfl -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    ((ref_readEsL _).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro h _ ⟨rfl, hlen⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    (ref_sampleE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro t _ rfl -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_readE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ rfl -
  dsimp only
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _) fun h0 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun h1 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ MonoD.pure _) fun hz ↦ ?_
  refine RefAtP.pure_require fun hA ↦ ?_
  set T := sumcheckTabs (tabs pub)
  have hw' : 0 < T[P20.pubTab].w := hw _ (List.getElem_mem hpt)
  refine ⟨pubOkV_of T evs hl hn hpt hw' hpc, ?_, ?_, ?_, ?_⟩
  · rw [Lvm.Acc.hEval_zero, ← toExt3_headD, Lvm.M3.FE_eq_of_beq h0]
  · rw [Lvm.Acc.hEval_one, sumE_map, Lvm.M3.FE_eq_of_beq h1, real_fixSent, Lvm.Acc.yOwnV,
      fixSentV_eq T evs hl hn, ← map_eqKernel, toExt3_dot]
  · rw [Lvm.M3.FE_eq_of_beq hz, FE.toExt3_zero]
  · have hA' := Lvm.M3.FE_eq_of_beq hA
    rw [tablePointV_eq' T evs hl hn hw, ← List.map_append, line_map, Lvm.Acc.PhiV, List.map_map,
      show (FE.ofExt3 ∘ FE.toExt3) = id from funext FE.ofExt3_toExt3, List.map_id, hEval_map]
    exact congrArg FE.toExt3 hA'

/-- **Phases 2–3b refine `busTabAccProg`** under the promise that phase 3b's folded claim holds. -/
theorem ref_busTabAcc (sig : ByteArray) (tabs : Pub → List Tab) (pub : Pub) (F : Fit P20 (tabs pub))
    (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w) :
    RefAtP capS occS shpS sig ((dBus P20 (M3.real P20 tabs) pub >>= fun pb ↦
        dTab P20 (M3.real P20 tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun bt ↦
          accFold P20 (M3.real P20 tabs) pub bt.2 >>= fun acc ↦ pure (bt, acc))
      (busTabAccProg tabs pub) (fun bta cl ↦ TabRel (sumcheckTabs (tabs pub)) bta.1 cl)
      (fun bta ↦ AccOk P20 (M3.real P20 tabs) pub bta.2 = true) := by
  unfold busTabAccProg Lvm.Acc.lbusTableAccProg
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_accFold _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((ref_busTabL sig tabs pub F).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro bt cl ⟨hR, hlen⟩ -
  have hR' := hR
  obtain ⟨-, -, rfl, hl⟩ := hR'
  refine RefAtP.bind (Q := fun acc ↦ AccOk P20 (M3.real P20 tabs) pub acc = true) (fun _ ↦ MonoD.pure _)
    (ref_accFold tabs pub bt.2 hl hlen F.pubTab hw) (fun _ _ h ↦ h) ?_
  intro acc _ _ _
  exact (RefAt.pure (b := (bt, acc)) (R := fun bta cl ↦ TabRel (sumcheckTabs (tabs pub)) bta.1 cl) hR).toP _

end Fold
end Lvm.VEq
end

-- ===== from `LvmTypedVEqPhasesX` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs AllSc lbusTableCheckProg)

/-- **`TRefHypX.phi` in the S2GF instance** (`N.phi = PhiQCX (cacheWX Q lay)`): statement 13, `PhiQCX_eq`. -/
theorem phiX_of_cacheWX {N : TNat} {Q : Lvm.Loop.Program} {lay : Lay} (hphi : N.phi = PhiQCX (cacheWX Q lay))
    (hlay : lay.Ok Q) (hc : (cacheWX Q lay).okB Q lay = true) :
    ∀ pt : List FE, pt.length = phiVarsX → N.phi pt = PhiQFX Q lay pt := fun pt hpt ↦ by
  rw [hphi]; exact PhiQCX_eq Q lay hlay hc pt hpt

end Lvm.VEq
end
