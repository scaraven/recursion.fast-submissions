-- new for lvm (WP-9b): the verifier program's table phase for the lvm instance on `E` (the program
-- objects `lbusTableSpec` is stated at): the tables, the layout, the bus result (`busFinalV`, the
-- `E` transcription of the native `LvmDecideM3Real.busFinalR`, list for list), the global column
-- numbering, and the fixed-column check (`tableCheckVB`, the program's version of `tableCheckR`).
import LvmLoopTable
import LvmBus
import LvmGrandProductSecurity
import LvmCpMultilinear
import LvmCpWeightedCube
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import LvmFrontBusGkr
import LvmSumcheckRound
import Mathlib.LinearAlgebra.Lagrange
import LvmSpineErrors
import LvmSpineSeams
import LvmCpPowerBatching
import Mathlib.Algebra.BigOperators.Fin
import LvmFrontBusSpec
import LvmBTableClaims
import LvmClaims
import LvmFrontCommitDoom
import LvmM3Inst

-- ===== merged from `LvmBusSecurity` (GOLF module merge: `LvmBusSecurity.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/BusSecurity.lean` (formal rev 40f877dc) as `LvmBusSecurity` for lvm (WP-2).
/-
  LeanVM.Protocol.BusSecurity

  Round-by-round knowledge soundness of the bus phase at the slot's error: the fingerprint
  challenges at `4·2^{μ_bus}/|E|`, the grand-product argument at its own errors, the roots and
  the boundary values at none.
-/

/-! lvm (WP-2): cut, as ArkLib's typed front: `challengeSecurity`, `rootsSecurity`,
`valuesSecurity`, `busSecurity` (`Typed.Security` halves). Kept, and made public where the source
had them private: what they are built from, the challenge count `card_afterChallenge_le` (with
`challenge_error_eq`, its fraction `4·2^{μ_bus}/|E|`), and the reflections `roots_reflect`,
`values_reflect` of the two checked messages. The bus phase's doom (`LvmFrontBusPhase`) uses these
directly. -/

/-!
# Knowledge soundness of the bus phase

`busSecurity I h` is the security half of `busPhase I h` at the slot's errors `busErrors I`, from
`Seam.commit` to `Seam.bus`. The stack is the oracle and every witness is trivial, so it is
round-by-round soundness: a stack outside `M3Holds` reaches `Seam.bus` only through a bad
challenge. It is composed from the four steps' halves, at the same intermediate relations as
`busComplete`, so every challenge keeps the error the slot assigns it:

* **The challenges `(α, β)`** (`challengeSecurity`), at `4·2^{μ_bus}/|E|` (Theorem 5.1 and
  Proposition `prop:pad`, `doc/leanvm/body/08-end-to-end-protocol.tex` at leanVM `3a37fb6e1`).
  The state after them is `afterChallenge`: the push and pull products agree at `(α, β)`, the
  count product is nonzero, every constraint vanishes, and the public lines and the Keccak
  predicate hold. It asks the products to agree, not the multisets, since a collision of the
  products could be charged to no later challenge. A stack outside `M3Holds` whose executed count
  cells are nonzero and that meets the clauses no challenge touches is unbalanced: its executed
  rows' two multisets differ. Each side's product is then its executed tuples' product times its
  padding leaves, the fingerprints of nonzero tuples whatever the padding rows hold, so the two
  sides of at most `2^{μ_bus}` leaves collide at no more than `4·2^{μ_bus}·|E|⁴` of the `|E|⁵`
  challenges (`card_paddedSideProduct_collision_le`). A zero executed count cell makes the count
  product zero at every challenge (`countsNonzero_of_prod`).
* **The roots** (`rootsSecurity`), at no error: a root that passes the check `R_c ≠ 0` and is
  the product of its leaves makes the count product nonzero, and one root for push and pull makes
  their products agree. This is where the check is load-bearing: a zero count is otherwise
  balanced on the bus (§6.2, `06-bus-interactions.tex:78`; the deployed verifier's check is
  `crates/verifier/src/bus.rs:117-119`).
* **The grand-product argument** (`gkrSecurity`), at `Typed.gkrErrors` from the unit `1/|E|`. Its riders
  carry the constraints and the public lines with the Keccak predicate, so its state function
  carries the zerocheck: a constraint that does not vanish on the cube has a nonzero extension
  restricted to the coordinates of `ζ` drawn so far, which a coordinate makes zero at one value at
  most, inside the argument's own bound.
* **The boundary values** (`valuesSecurity`), at no error: the claims of `Seam.bus` force the
  values sent to be the boundary columns' extensions, and then the forms sum to the totals
  exactly when the leaf claims hold (`sum_forms_eq_total_iff`); the zerocheck clause gives the
  riders' vanishing.

Every part takes no real number and no `Fintype` instance as an argument, and the compositions
are inlined, so the security computes, its extractor included. The count of bad challenges is a
number the compiled security holds, so `|E|` is written `2^192` there (`card_E`): `Nat.card E` does
not compute.

Written from the specification and the protocol's relations; nothing is transcribed.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal

section

namespace Bus

variable {I : M3Instance}

/-! ## The challenges -/

/-- `|E| = 2^192`, counted with `Nat.card`. -/
theorem natCard_E : Nat.card E = 2 ^ 192 := by
  rw [Nat.card_eq_fintype_card, card_E]

/-- From a stack outside `M3Holds`, at most `4·2^{μ_bus}·|E|⁴` challenges `(α, β)` lead into
`afterChallenge`: none if an executed count cell is zero (the count product is then zero) or a
clause no challenge touches fails, a collision of the two products otherwise, whatever the padding
rows hold (Proposition `prop:pad`). -/
theorem card_afterChallenge_le (h : Conditions I) (s : I.Stmt) (o : ∀ i, TheOracle I i)
    (hs : ¬ M3Holds I s (theStack o)) :
    Nat.card {ab : (Fin 4 → E) × E // (((s, ab), o), ()) ∈ afterChallenge I} ≤
      4 * 2 ^ I.μBus * (2 ^ 192) ^ 4 := by
  rw [← natCard_E]
  by_cases hrest : I.CountsNonzero (theStack o) ∧ I.ConstraintsVanish (theStack o) ∧
      I.PublicLinesHold s (theStack o) ∧ I.aux (theStack o)
  · have hb : ¬ I.Balanced (theStack o) := fun hb ↦
      hs ⟨hrest.2.1, hb, hrest.1, hrest.2.2.1, hrest.2.2.2⟩
    have hne : (I.tuples (theStack o) .push : Multiset (Vector K 16)) ≠
        (I.tuples (theStack o) .pull : Multiset (Vector K 16)) :=
      fun he ↦ hb (Multiset.coe_eq_coe.mp he)
    have hP : (sidePadTuples I (theStack o) .push : Multiset (Vector K 16)).card +
        (I.tuples (theStack o) .push : Multiset (Vector K 16)).card ≤ 2 ^ I.μBus := by
      rw [Multiset.coe_card, Multiset.coe_card, length_side (k := 0) rfl, ← blocks_total]
      exact push_fits I
    have hQ : (sidePadTuples I (theStack o) .pull : Multiset (Vector K 16)).card +
        (I.tuples (theStack o) .pull : Multiset (Vector K 16)).card ≤ 2 ^ I.μBus := by
      rw [Multiset.coe_card, Multiset.coe_card, length_side (k := 1) rfl]
      exact h.pull_fits
    refine (Finite.card_le_of_embedding (Subtype.impEmbedding _ _ fun ab hab ↦ ?_)).trans
      (card_paddedSideProduct_collision_le hne (fun u hu ↦ padTuple_ne_zero h hu)
        (fun u hu ↦ padTuple_ne_zero h hu) hP hQ)
    have hprod := hab.1
    change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 (theStack o))[x] =
      ∏ x : Fin (2 ^ I.μBus), (pullLeaves I ab.1 ab.2 (theStack o))[x] at hprod
    rw [prod_pushLeaves, prod_pullLeaves h] at hprod
    exact hprod
  · have : IsEmpty {ab : (Fin 4 → E) × E // (((s, ab), o), ()) ∈ afterChallenge I} :=
      ⟨fun ab ↦ hrest ⟨countsNonzero_of_prod h _ _ _ ab.2.2.1, ab.2.2.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The challenges' count over their number is the slot's error, `4·2^{μ_bus}/|E|`. -/
theorem challenge_error_eq :
    ((4 * 2 ^ I.μBus * (2 ^ 192) ^ 4 : ℕ) : ℝ≥0) / (Nat.card ((Fin 4 → E) × E) : ℝ≥0) =
      overE (4 * 2 ^ I.μBus) := by
  rw [← natCard_E]
  have hE : (Nat.card E : ℝ≥0) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  rw [overE, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  push_cast
  rw [mul_comm ((Nat.card E : ℝ≥0) ^ 4) (Nat.card E : ℝ≥0),
    mul_div_mul_right _ _ (pow_ne_zero 4 hE)]

/-! ## The roots -/

/-- A root that passes the check `R_c ≠ 0` and is the product of its leaves makes the count
product nonzero, and one root for push and pull makes their products agree. -/
theorem roots_reflect (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) (w : Unit)
    (r : E × E) (hc : decide (r.2 ≠ 0) = true)
    (hout : (((x, ![r.1, r.1, r.2]), o), w) ∈ Gkr.relIn 3 I.μBus (leaves I) (riders I)) :
    ((x, o), w) ∈ afterChallenge I := by
  cases w
  obtain ⟨hz, hroots⟩ := hout
  obtain ⟨hcons, hl, ha⟩ := (ridersZero_iff h x o).mp hz
  have h0 : r.1 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 0)[i] := hroots 0
  have h1 : r.1 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 1)[i] := hroots 1
  have h2 : r.2 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 2)[i] := hroots 2
  have hnz : r.2 ≠ 0 := of_decide_eq_true hc
  rw [h2] at hnz
  exact ⟨h0.symm.trans h1, hnz, hcons, hl, ha⟩

/-! ## The boundary values -/

/-- The boundary claims force the values sent, the forms summing to the totals then force the
leaf claims, and the zerocheck clause the riders' vanishing. -/
theorem values_reflect (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (o : ∀ i, TheOracle I i) (w : Unit) (vals : Vector E I.busClaims)
    (_ : (fun (_ : Gkr.LayerStmt (Data I) E 3 I.μBus) (_ : Vector E I.busClaims) ↦ true) ℓ vals
      = true)
    (hout : (((ℓ.1.1, busOut h ℓ vals), o), w) ∈ Seam.bus I) :
    ((ℓ, o), w) ∈ Gkr.relOut 3 I.μBus (leaves I) (riders I) := by
  cases w
  obtain ⟨hzero, hforms, hclaims, hl, ha⟩ := hout
  have hvals : ∀ i : Fin I.busClaims, vals[i] = eval₂Mle
      (I.column (theStack o) I.boundaryColumns[i]).values (algebraMap K E)
      (columnPoint h ℓ.2.1 i) := fun i ↦
    (hclaims ⟨I.boundaryColumns[i], columnPoint h ℓ.2.1 i, vals[i]⟩
      (by simp only [busOut, Vector.toList_ofFn, List.mem_ofFn]; exact ⟨i, rfl⟩)).symm
  refine ⟨fun k ↦ (sum_forms_eq_total_iff h k _ _ _ _ _ _ hvals).mp (hforms k),
    (riders_vanish_iff ℓ.1 o ℓ.2.1).mpr ⟨fun j hj C hC ↦ ?_, hl, ha⟩⟩
  have := hzero ⟨j, Or.inl (List.ne_nil_of_mem hC)⟩ C hC
  rwa [show (busOut h ℓ vals).point = point h ℓ.2.1 from rfl, lowPoint_point] at this

end Bus

end
end LeanVM.Protocol
end
-- ===== end of `LvmBusSecurity` =====

-- ===== merged from `LvmCpIndividualDegree` (GOLF module merge: `LvmCpIndividualDegree.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/IndividualDegree.lean` (formal rev 40f877dc) as `LvmCpIndividualDegree` for lvm (WP-2).
/-
  LeanVM.Protocol.ToCompPoly.IndividualDegree

  Functions of a point that are polynomials of bounded degree in each coordinate separately, and
  the operations that keep the bounds. Candidate for CompPoly.
-/

/-!
# Degree in each coordinate

`DegreeLEAt f k e`: fixing every coordinate of the point but coordinate `k`, `f` is a polynomial
of degree at most `e` in coordinate `k`. `IndividualDegreeLE f d`: that, at the bound `d`, for every
coordinate. It is what a sumcheck needs of its summand: the round polynomial, a sum of such
restrictions, then has degree at most `d`.

The bound in one coordinate is computed by the usual rules: constants have degree `0` (`const`), a
coordinate has degree `1` in itself (`coord_self`) and `0` in the others (`coord_ne`), so does any
function that ignores the coordinate (`of_set_eq`), the extension of a table has degree `1`
(`evalMle`), the bound adds under products (`mul`, `pow`, `prod`) and takes the larger of two
under sums and differences (`add`, `sub`, `sum`), and a polynomial of total degree `d` applied to
functions of degree at most `1` has degree at most `d` (`mvPolynomial_eval`), also with its
coefficients mapped into the ring (`mvPolynomial_eval₂`; lvm cuts leanVM's `cmvPolynomial_eval₂`
for CompPoly's `CMvPolynomial`, outside lvm's imports: use `mvPolynomial_eval₂` on Mathlib's
`MvPolynomial`). A product of factors in different coordinates, such as an equality polynomial in
some coordinates times a product of others, is bounded coordinate by coordinate; the weight of a
point off the cube, one affine factor per coordinate, has degree `1` in each (`prodWeight`). Over
an arbitrary commutative ring; nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval Polynomial

section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Fixing every coordinate but coordinate `k`, `f` is a polynomial of degree at most `e` in
coordinate `k`. -/
def DegreeLEAt (f : Vector R n → R) (k e : ℕ) : Prop :=
  ∀ (z : Vector R n) (hk : k < n), ∃ p : R[X], p.natDegree ≤ e ∧ ∀ x, f (z.set k x hk) = p.eval x

/-- `f` has degree at most `d` in every coordinate. -/
def IndividualDegreeLE (f : Vector R n → R) (d : ℕ) : Prop := ∀ k, DegreeLEAt f k d

namespace DegreeLEAt

variable {f g : Vector R n → R} {k d e : ℕ}

/-- A bound is a bound for any larger degree. -/
theorem mono (hf : DegreeLEAt f k d) (h : d ≤ e) : DegreeLEAt f k e := fun z hk ↦
  let ⟨p, hp, hev⟩ := hf z hk
  ⟨p, hp.trans h, hev⟩

/-- A constant has degree `0`. -/
theorem const (c : R) : DegreeLEAt (fun _ : Vector R n ↦ c) k 0 := fun _ _ ↦
  ⟨C c, by simp, fun _ ↦ by simp⟩

/-- A function that ignores coordinate `k` has degree `0` in it. -/
theorem of_set_eq (h : ∀ (z : Vector R n) (hk : k < n) (x : R), f (z.set k x hk) = f z) :
    DegreeLEAt f k 0 := fun z hk ↦
  ⟨C (f z), by simp, fun x ↦ by rw [h z hk x, eval_C]⟩

/-- Coordinate `k` has degree `1` in itself. -/
theorem coord_self (hk : k < n) : DegreeLEAt (fun z : Vector R n ↦ z[k]) k 1 := fun _ _ ↦
  ⟨X, natDegree_X_le, fun x ↦ by simp⟩

/-- Another coordinate has degree `0` in coordinate `k`. -/
theorem coord_ne {i : ℕ} (hi : i < n) (hik : i ≠ k) :
    DegreeLEAt (fun z : Vector R n ↦ z[i]) k 0 :=
  of_set_eq fun _ hk _ ↦ Vector.getElem_set_ne hk hi hik.symm

/-- The bound of a sum is the larger bound. -/
theorem add (hf : DegreeLEAt f k d) (hg : DegreeLEAt g k d) :
    DegreeLEAt (fun z ↦ f z + g z) k d := fun z hk ↦
  let ⟨p, hp, hpe⟩ := hf z hk
  let ⟨q, hq, hqe⟩ := hg z hk
  ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq), fun x ↦ by simp [hpe, hqe]⟩

/-- The bound of a difference is the larger bound. -/
theorem sub (hf : DegreeLEAt f k d) (hg : DegreeLEAt g k d) :
    DegreeLEAt (fun z ↦ f z - g z) k d := fun z hk ↦
  let ⟨p, hp, hpe⟩ := hf z hk
  let ⟨q, hq, hqe⟩ := hg z hk
  ⟨p - q, (natDegree_sub_le _ _).trans (max_le hp hq), fun x ↦ by simp [hpe, hqe]⟩

/-- The bounds of a product add. -/
theorem mul (hf : DegreeLEAt f k d) (hg : DegreeLEAt g k e) :
    DegreeLEAt (fun z ↦ f z * g z) k (d + e) := fun z hk ↦
  let ⟨p, hp, hpe⟩ := hf z hk
  let ⟨q, hq, hqe⟩ := hg z hk
  ⟨p * q, natDegree_mul_le.trans (add_le_add hp hq), fun x ↦ by simp [hpe, hqe]⟩

/-- The bound of a finite sum is a common bound of its terms. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → Vector R n → R}
    (hf : ∀ i ∈ s, DegreeLEAt (f i) k d) : DegreeLEAt (fun z ↦ ∑ i ∈ s, f i z) k d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ((const (0 : R)).mono (Nat.zero_le d) :
      DegreeLEAt (fun _ : Vector R n ↦ (0 : R)) k d)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The bound of a finite product is the sum of its factors' bounds. -/
theorem prod {ι : Type*} (s : Finset ι) {f : ι → Vector R n → R} {d : ι → ℕ}
    (hf : ∀ i ∈ s, DegreeLEAt (f i) k (d i)) :
    DegreeLEAt (fun z ↦ ∏ i ∈ s, f i z) k (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (1 : R) : DegreeLEAt (fun _ : Vector R n ↦ (1 : R)) k 0)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The bound of a power is the exponent times the bound. -/
theorem pow (hf : DegreeLEAt f k d) (m : ℕ) : DegreeLEAt (fun z ↦ f z ^ m) k (m * d) := by
  simpa using prod (Finset.univ : Finset (Fin m)) (f := fun _ ↦ f) (d := fun _ ↦ d)
    fun _ _ ↦ hf

/-- The extension of a table has degree `1` in each coordinate. -/
theorem evalMle (t : CMlPolynomialEval R n) :
    DegreeLEAt (fun z ↦ CMlPolynomialEval.evalMle t z) k 1 := fun z hk ↦
  ⟨C (CMlPolynomialEval.evalMle t (z.set k 0 hk)) +
      X * C (CMlPolynomialEval.evalMle t (z.set k 1 hk) -
        CMlPolynomialEval.evalMle t (z.set k 0 hk)),
    (natDegree_add_le _ _).trans (max_le (by simp)
      (natDegree_mul_le.trans (by simpa using natDegree_X_le))),
    fun x ↦ by
      show CMlPolynomialEval.evalMle t (z.set k x hk) = _
      rw [evalMle_set t z hk x]
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      ring⟩

/-- A polynomial of total degree at most `d`, applied to functions of degree at most `1` in
coordinate `k`, has degree at most `d` in coordinate `k`. -/
theorem mvPolynomial_eval {σ : Type*} (p : MvPolynomial σ R) (hp : p.totalDegree ≤ d)
    {f : σ → Vector R n → R} (hf : ∀ i, DegreeLEAt (f i) k 1) :
    DegreeLEAt (fun z ↦ MvPolynomial.eval (fun i ↦ f i z) p) k d := by
  classical
  have key : ∀ m ∈ p.support, DegreeLEAt
      (fun z ↦ p.coeff m * ∏ i ∈ m.support, f i z ^ m i) k d := by
    intro m hm
    have hdeg : ∑ i ∈ m.support, m i * 1 ≤ d := by
      simpa [Finsupp.sum] using (MvPolynomial.le_totalDegree hm).trans hp
    exact ((const _).mul (prod m.support fun i _ ↦ (hf i).pow (m i))).mono (by simpa using hdeg)
  simpa [MvPolynomial.eval_eq] using sum p.support key

/-- A polynomial of total degree at most `d` over a ring mapped into `R`, applied to functions of
degree at most `1` in coordinate `k`, has degree at most `d` in coordinate `k`. -/
theorem mvPolynomial_eval₂ {S σ : Type*} [CommRing S] (φ : S →+* R) (p : MvPolynomial σ S)
    (hp : p.totalDegree ≤ d) {f : σ → Vector R n → R} (hf : ∀ i, DegreeLEAt (f i) k 1) :
    DegreeLEAt (fun z ↦ MvPolynomial.eval₂ φ (fun i ↦ f i z) p) k d := by
  have hmap : (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset φ p)
  intro z hk
  obtain ⟨q, hq, hqe⟩ := mvPolynomial_eval (MvPolynomial.map φ p) (hmap.trans hp) hf z hk
  exact ⟨q, hq, fun x ↦ by
    show MvPolynomial.eval₂ φ _ p = _
    rw [MvPolynomial.eval₂_eq_eval_map, ← hqe]⟩

/-- The weight off the cube, a product of factors each affine in its own coordinate, has degree
at most `1` in each coordinate. -/
theorem prodWeight (w : Fin n → R × R) : DegreeLEAt (LeanVM.Protocol.prodWeight w) k 1 := by
  intro z hk
  have hfac : ∀ a : Fin n, DegreeLEAt (fun z : Vector R n ↦ (1 - z[a]) * (w a).1 + z[a] * (w a).2)
      k (if a.val = k then 1 else 0) := fun a ↦ by
    split_ifs with h
    · subst h
      exact ((((const 1).mono (Nat.zero_le 1)).sub (coord_self a.isLt)).mul (const _)).add
        ((coord_self a.isLt).mul (const _)) |>.mono (by simp)
    · exact (((const 1).sub (coord_ne a.isLt h)).mul (const _)).add
        ((coord_ne a.isLt h).mul (const _)) |>.mono (by simp)
  have hsum : ∑ a : Fin n, (if a.val = k then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single ⟨k, hk⟩
      (fun b _ hb ↦ ite_eq_right_iff.mpr fun h ↦ absurd (Fin.ext h) hb)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp
  exact (hsum ▸ prod Finset.univ fun a _ ↦ hfac a) z hk

end DegreeLEAt

end
end LeanVM.Protocol
end
-- ===== end of `LvmCpIndividualDegree` =====

-- ===== merged from `LvmFrontBusPhase` (GOLF module merge: `LvmFrontBusPhase.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusPhase.lean` (formal rev 40f877dc) as `LvmFrontBusPhase` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.BusPhase

  The verifier program's bus phase (`verify_bus_balance`) specified on the oracle protocol's
  relations: the fingerprint challenges, the roots, the grand-product walk and the boundary
  values, from the commitment's doom to doom on the bus seam.
-/

/-! lvm (WP-2): the verifier program's `verifyBusBalance` takes the table list as its first argument
(`LvmVCore`: leanISA's `tables` is cut), so `refBusResult`, `BusWit.result`,
`verifyBusBalance_bind_eq`, `BusPost`, `busThenSpec` and `busPhaseSpec` take `tables : List
Verifier.Table` (the source's are at leanISA's `tables`). `ab_card_le`, `roots_keep`,
`values_keep` are proved from the count and reflections the source's typed securities were
built from (`Bus.card_afterChallenge_le`, `Bus.roots_reflect`, `Bus.values_reflect`), the
statements unchanged. -/

/-!
# The bus phase on doom

`verifyBusBalance layout` (`crates/verifier/src/bus.rs:106-213`) is the oracle protocol's `busPhase`
(`LeanVM.Protocol.Bus`) on the wire. This module specifies its parts on the protocol's
relations, in the calculus of verifier programs:

* `alwaysSpec`: a sub-program from a fact that already decides its postcondition (the count root
  `0`, which the later `require` rejects);
* `gkrSpec`: `verify_gkr_grand_products` (`bus.rs:14-51`), from doom on the relation after
  the fingerprint challenges (`Bus.afterChallenge`) to "the count root is `0`, or doom on the
  argument's output relation": the roots' message is the protocol's (`Bus.rootsSecurity`), the
  roots are the layer-`0` statement (`Gkr.relIn_iff_layerRel_zero`), and the walk, each step
  drawing its own combiner, is `gkrLayersSpec`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

section

/-! ## The fixed polynomial's value (restated, lvm) -/

/-- The deployed verifier computes the fixed polynomial's value (`Bytecode::evaluate`,
`crates/verifier/src/bytecode.rs:99-136`, the same value by a sparse sum). lvm (WP-2): restated
from `Statement.LeanVmVerifier` (the leanVM verifier proper, cut from `LvmVCore`). -/
def _root_.LeanVM.Protocol.Verifier.computedBytecodeValue (words : List K) (point : List E) :
    VerifierProgram E :=
  pure (multilinearEval (words.map ofK) point)

/-! ## A decided postcondition -/

variable {εmax : ℝ≥0∞}

/-- **A sub-program whose postcondition is already decided**: if every return satisfies `Post`
(whatever the history), doom holds throughout and no challenge escapes it. The lead is the
follower's, capped at `1`. -/
noncomputable def alwaysSpec {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {T : ℝ≥0∞} (hpost : ∀ a h, Post a h) (hT : min 1 T ≤ εmax) :
    Spec p Pre Post εmax (min 1 T) T where
  D _ _ := True
  V _ _ := min 1 T
  le_one _ _ := min_le_left _ _
  start_D _ _ := trivial
  start_V _ _ := le_rfl
  read := by intros; trivial
  grind := by intros; trivial
  commit := by intros; trivial
  sample := by
    intros
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  query := by intros; exact le_rfl
  moveEnd := by intro _ _ _ _ _ _ hD; exact absurd trivial hD
  retEnd := by intro _ _ _ _ _ hD; exact absurd trivial hD
  retDoom := by intros; exact le_rfl
  post := by intros; exact hpost _ _
  bound := by
    intros
    exact le_trans (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (by norm_num))) hT

/-- `alwaysSpec` before a follower of lead `0`. -/
noncomputable def alwaysSpec0 {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} (hpost : ∀ a h, Post a h) : Spec p Pre Post εmax 0 0 :=
  (alwaysSpec (T := 0) hpost (by simp)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

/-! ## Several challenges in a row -/

/-- A sum over the tuples of `n + 1` challenges is a sum over the first and the rest. -/
theorem sum_fin_succ_fun (n : ℕ) (F : (Fin (n + 1) → E) → ℝ≥0∞) :
    ∑ w, F w = ∑ x : E, ∑ v : Fin n → E, F (Fin.cons x v) := by
  rw [← (Fin.consEquiv fun _ ↦ E).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **`n` challenges in a row**, then a sub-program: the expectation of a function of the return
is at most the average, over the tuples of challenges, of a bound on the sub-program's. -/
theorem retExp_sampleN_bind_le {β : Type} (g : β → List Ev → ℝ≥0∞) (h₀ : List Ev) :
    ∀ (n : ℕ) (k : List E → VerifierProgram β) (B : List E → ℝ≥0∞),
      (∀ xs l, VerifierProgram.retExp g h₀ l (k xs) ≤ B xs) → ∀ l,
      VerifierProgram.retExp g h₀ l ((VerifierProgram.sampleChallenges n).bind k) ≤
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (List.ofFn v)
  | 0, k, B, hk, l => by
    simpa [VerifierProgram.sampleChallenges] using hk [] l
  | n + 1, k, B, hk, l => by
    show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, VerifierProgram.retExp g h₀ (l ++ [Ev.sample x])
        (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x ::
            xs)).bind k) ≤ _
    have ih : ∀ x : E, VerifierProgram.retExp g h₀ (l ++ [Ev.sample x])
        (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x ::
            xs)).bind k) ≤
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (x :: List.ofFn v) := fun x ↦ by
      rw [VerifierProgram.bind_assoc]
      exact retExp_sampleN_bind_le g h₀ n (fun xs ↦ k (x :: xs)) (fun xs ↦ B (x :: xs))
        (fun xs l ↦ hk _ l) _
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, VerifierProgram.retExp g h₀ (l ++ [Ev.sample x])
          (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x ::
              xs)).bind k)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E,
          ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (x :: List.ofFn v) := by
          gcongr with x
          exact ih x
      _ = ((Fintype.card E : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v : Fin (n + 1) → E, B (List.ofFn v) := by
          rw [sum_fin_succ_fun, ← Finset.mul_sum, ← mul_assoc, pow_succ, ENNReal.mul_inv
            (by simp) (by simp), mul_comm ((Fintype.card E : ℝ≥0∞)⁻¹)]
          congr 2
          funext x
          congr 1
          funext v
          rw [List.ofFn_succ]
          rfl

/-- A program of challenges and returns only: no prover move. -/
inductive SampleOnly {α : Type} : VerifierProgram α → Prop
  | ret (a : α) : SampleOnly (.ret a)
  | fail : SampleOnly .fail
  | sample {k : E → VerifierProgram α} : (∀ c, SampleOnly (k c)) → SampleOnly (.sample k)

/-- What a program of challenges reaches is a program of challenges. -/
theorem SampleOnly.after {α : Type} {p : VerifierProgram α} (hp : SampleOnly p) :
    ∀ {l : List Ev} {q : VerifierProgram α}, p.after l = some q → SampleOnly q := by
  induction hp with
  | ret a =>
    intro l q h
    cases l with
    | nil => simp [VerifierProgram.after] at h; subst h; exact .ret a
    | cons e l => cases e <;> simp [VerifierProgram.after] at h
  | fail =>
    intro l q h
    cases l with
    | nil => simp [VerifierProgram.after] at h; subst h; exact .fail
    | cons e l => cases e <;> simp [VerifierProgram.after] at h
  | sample _ ih =>
    intro l q h
    cases l with
    | nil => simp [VerifierProgram.after] at h; subst h; exact .sample ‹_›
    | cons e l =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih _ h

/-- A program of challenges makes no prover move. -/
theorem SampleOnly.not_isMove {α : Type} {q : VerifierProgram α} (hq : SampleOnly q) : ¬
    q.IsMove := by
  cases hq <;> simp [VerifierProgram.IsMove]

/-- The fingerprint challenges `(α, β)` as the wire draws them: four, then one. -/
def abProg : VerifierProgram (List E × E) :=
  (VerifierProgram.sampleChallenges 4).bind fun as ↦ VerifierProgram.sampleChallenge.bind fun b ↦
      VerifierProgram.ret (as, b)

/-- The wire's four `α` as the protocol's. -/
def toAlpha (as : List E) : Fin 4 → E := fun i ↦ as.getD i 0

theorem sampleOnly_abProg : SampleOnly abProg :=
  .sample fun _ ↦ .sample fun _ ↦ .sample fun _ ↦ .sample fun _ ↦ .sample fun _ ↦ .ret _

theorem toAlpha_ofFn (v : Fin 4 → E) : toAlpha (List.ofFn v) = v := by
  funext i
  fin_cases i <;> rfl

open Classical in
/-- **The union bound over candidates**, for any finite type of challenges. -/
theorem card_exists_le_of {α β : Type} [Fintype α] {C : Set β} (hfin : C.Finite) {L₀ : ℕ}
    (hcard : C.ncard ≤ L₀) (P : β → α → Prop) {e : ℝ≥0∞}
    (h : ∀ q ∈ C, (Fintype.card α : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) ≤ e) :
    (Fintype.card α : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞) ≤ L₀ * e := by
  let s := hfin.toFinset
  have hsub : (Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c) ⊆
      s.biUnion fun q ↦ Finset.univ.filter fun c ↦ P q c := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨q, hq, hp⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨q, hfin.mem_toFinset.mpr hq, by simpa using hp⟩
  calc (Fintype.card α : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞)
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ *
          ∑ q ∈ s, ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ q ∈ s, (Fintype.card α : ℝ≥0∞)⁻¹ *
          ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := Finset.mul_sum _ _ _
    _ ≤ ∑ _q ∈ s, e := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * e := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card C hfin]
        exact_mod_cast hcard

/-! ## The fingerprint challenges -/

section Challenges

variable (I : M3Instance) (cands : Word → Set (∀ i, TheOracle I i)) (input : I.Stmt)

/-- The error of the fingerprint challenges over at most `L₀` candidates:
`L₀ · 4 · 2^{μ_bus} / |E|` (Theorem 5.1). -/
noncomputable def abError (L₀ : ℕ) : ℝ≥0∞ := L₀ * (overE (4 * 2 ^ I.μBus) : ℝ≥0∞)

open Classical in
/-- From a stack outside `M3Holds`, the fingerprint challenges that satisfy the relation after
them are at most a fraction `4 · 2^{μ_bus} / |E|` (`Bus.challengeSecurity`). -/
theorem ab_card_le (hI : Bus.Conditions I) (o : ∀ i, TheOracle I i)
    (ho : ((input, o), ()) ∉ Seam.commit I) :
    (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun ab ↦
      (((input, ab), o), ()) ∈ Bus.afterChallenge I).card : ℝ≥0∞) ≤
        (overE (4 * 2 ^ I.μBus) : ℝ≥0∞) := by
  have hc := Bus.card_afterChallenge_le hI input o ho
  rw [natCard_subtype_eq_card_filter] at hc
  have hT : (Nat.card ((Fin 4 → E) × E) : ℝ≥0) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  rw [← Bus.challenge_error_eq, ENNReal.coe_div hT, ENNReal.coe_natCast, ENNReal.coe_natCast,
    Nat.card_eq_fintype_card, div_eq_mul_inv, mul_comm]
  gcongr

variable {εmax : ℝ≥0∞}

open Classical in
/-- **The fingerprint challenges** (`alphas = samples(BUS_BITS)`, `beta = sample()`,
`bus.rs:112-114`): one group of five challenges, the protocol's one challenge `(α, β)`,
escaping the commitment's doom with probability at most `L₀ · 4 · 2^{μ_bus} / |E|`. -/
noncomputable def abSpec (hI : Bus.Conditions I) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError I L₀ < 1) {T : ℝ≥0∞} :
    Spec abProg (HDoom cands (Seam.commit I) input)
      (fun ab h ↦ HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) εmax
      (abError I L₀ + T) T :=
  Spec.ofNoMove (fun _ ha ↦ (sampleOnly_abProg.after ha).not_isMove) hlt fun h₀ hp ↦ by
    obtain ⟨W, hW, hR⟩ := hp
    let bad : (Fin 4 → E) × E → Prop := fun ab ↦
      ∃ o ∈ cands W, (((input, ab), o), ()) ∈ Bus.afterChallenge I
    unfold VerifierProgram.escRet abProg
    refine le_trans (retExp_sampleN_bind_le _ h₀ 4 _
      (fun as ↦ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ b : E, if bad (toAlpha as, b) then 1 else 0)
      (fun as l ↦ ?_) []) ?_
    · show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ b : E, (if HDoom cands (Bus.afterChallenge I)
          (input, (toAlpha as, b)) (h₀ ++ (l ++ [Ev.sample b])) then 0 else 1) ≤ _
      gcongr with b
      by_cases h1 : HDoom cands (Bus.afterChallenge I) (input, (toAlpha as, b))
          (h₀ ++ (l ++ [Ev.sample b]))
      · simp [h1]
      · have h2 : bad (toAlpha as, b) := by
          by_contra h2
          exact h1 ⟨W, firstWord_append hW _, fun o ho hin ↦ h2 ⟨o, ho, hin⟩⟩
        simp [h1, h2]
    · simp only [toAlpha_ofFn]
      have hcardT : (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) =
          (Fintype.card E : ℝ≥0∞) ^ 4 * Fintype.card E := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring
      calc ((Fintype.card E : ℝ≥0∞) ^ 4)⁻¹ * ∑ v : Fin 4 → E, (Fintype.card E : ℝ≥0∞)⁻¹ *
            ∑ b : E, (if bad (v, b) then 1 else 0)
          = (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞)⁻¹ *
              ((Finset.univ.filter fun ab ↦ bad ab).card : ℝ≥0∞) := by
            rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.mul_inv (by simp) (by simp), ← hcardT,
              ← Fintype.sum_prod_type', Finset.sum_boole]
        _ ≤ L₀ * (overE (4 * 2 ^ I.μBus) : ℝ≥0∞) :=
            card_exists_le_of (hfin W) (hcard W)
              (fun o ab ↦ (((input, ab), o), ()) ∈ Bus.afterChallenge I)
              fun o ho ↦ ab_card_le I input hI o (hR o ho)

end Challenges

/-! ## The roots and the walk -/

section Gkr

variable (I : M3Instance) (cands : Word → Set (∀ i, TheOracle I i))
  (data : Bus.Data I)

/-- The roots' message keeps doom: from doom after the fingerprint challenges, a nonzero count
root makes doom on the grand product's input relation. -/
theorem roots_keep (hI : Bus.Conditions I) {C : Set (∀ i, TheOracle I i)}
    (hpre : RelDoom C (Bus.afterChallenge I) data) (shared count : E) (hc : count ≠ 0) :
    RelDoom C (Gkr.relIn 3 I.μBus (Bus.leaves I) (Bus.riders I)) (data, ![shared, shared, count]) :=
  say_keep (fun o hout ↦ Bus.roots_reflect hI data o () (shared, count) (by simpa using hc) hout)
    hpre

/-- The protocol's roots statement is the wire's GKR state at layer `0`. -/
theorem rootStmt_eq (shared count : E) :
    Gkr.rootStmt 3 (data, ![shared, shared, count]) =
      layerStmtOf data 0 ⟨[shared, shared, count], []⟩ := by
  refine Prod.ext rfl (Prod.ext (Vector.ext fun i hi ↦ absurd hi (by omega)) ?_)
  funext t
  fin_cases t <;> rfl

/-- What the wire's GKR gives: the count root `0`, which the bus phase rejects, or doom on the
argument's output relation at the point and values it returns. -/
def GkrPost (r : E × List E × List E) (h : List Ev) : Prop :=
  r.1 = 0 ∨ (r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
    HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
      (layerStmtOf data I.μBus ⟨r.2.2, r.2.1⟩) h)

variable {εmax : ℝ≥0∞}

open Classical in
/-- **`verify_gkr_grand_products`** at the depth `μ_bus`: from doom after the fingerprint
challenges to `GkrPost`. Each round's challenge is charged `L₀ · 4 / |E|` at most, each combiner
`L₀ · 2 / |E|`, each combination challenge `L₀ / |E|`. -/
noncomputable def gkrSpec (hI : Bus.Conditions I) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec (verifyGkrGrandProducts I.μBus) (HDoom cands (Bus.afterChallenge I) data)
      (GkrPost I cands data) εmax 0 0 :=
  (Spec.readE (Post := fun _ h ↦ HDoom cands (Bus.afterChallenge I) data h)
    (fun _ _ hp ↦ hp.append _) zero_le).bind' fun shared ↦
  (Spec.readE (Post := fun count h ↦ count = 0 ∨ HDoom cands
      (Gkr.relIn 3 I.μBus (Bus.leaves I) (Bus.riders I)) (data, ![shared, shared, count]) h)
    (fun _ count hp ↦ by
      by_cases hz : count = 0
      · exact .inl hz
      · obtain ⟨W, hW, hR⟩ := hp
        exact .inr ⟨W, firstWord_append hW _, roots_keep I data hI hR shared count hz⟩)
    hlam).bind' fun count ↦
  if hz : count = 0 then
    ((alwaysSpec0 (Post := fun _ _ ↦ True) (fun _ _ ↦ trivial)).bind' fun (s : GkrState) ↦
      (Spec.ret (Post := GkrPost I cands data) (count, s.point, s.values)).mono
        (fun _ _ ↦ .inl hz) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ _ ↦ trivial) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else
    ((gkrLayersSpec (Bus.leaves I) (Bus.riders I) cands data hfin hcard he hT I.μBus 0 (by simp)
      ⟨[shared, shared, count], []⟩).bind' fun s ↦
    (Spec.ret (Post := GkrPost I cands data) (count, s.point, s.values)).mono
      (fun _ hp ↦ by
        unfold LayersPre at hp
        simp only [↓reduceIte] at hp
        exact .inr hp) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun h₀ hp ↦ by
        obtain ⟨W, hW, hR⟩ := hp.resolve_left hz
        unfold LayersPre
        simp only [hμ, ↓reduceIte]
        refine ⟨rfl, rfl, W, hW, fun o ho hin ↦ hR o ho
          ((Gkr.relIn_iff_layerRel_zero 3 I.μBus (Bus.leaves I) (Bus.riders I) _ o).mpr ?_)⟩
        rw [rootStmt_eq I data shared count]
        exact hin) (fun _ _ h ↦ h) le_rfl (by simp [nextError, hμ]) le_rfl

end Gkr

/-! ## The phase -/

section Phase

/-- The pure part of `verify_bus_balance` after the reads (`bus.rs:127-212`): the claims, the
fingerprints, and the leaf decomposition of the three sides. -/
def refBusResult (tables : List Verifier.Table) (layout : Verifier.Layout) (alphas : List E) (beta : E)
    (point treeValues memory : List E) (memoryFinal bytecodeFinal : E) : BusResult :=
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List Verifier.ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow
    (multilinearEval (layout.bytecode.map ofK) (bytecodeLow ++ alphas))
  let pcFinal := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide tables forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide tables forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide tables forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  ⟨claims, point, forms3, [total0, total1, total2]⟩

/-- What the bus phase reads after the fingerprint challenges: the challenges, the grand
product's point and values, and the boundary values. -/
structure BusWit where
  /-- The four `α`. -/
  alphas : List E
  /-- `β`. -/
  beta : E
  /-- The grand product's point. -/
  point : List E
  /-- The three trees' values there. -/
  values : List E
  /-- The memory columns' values. -/
  memory : List E
  /-- `MEMORY_FINAL_COUNTERS`' value. -/
  mf : E
  /-- `BYTECODE_FINAL_COUNTERS`' value. -/
  bf : E

/-- The bus phase's result on what it read. -/
def BusWit.result (tables : List Verifier.Table) (layout : Verifier.Layout) (w : BusWit) :
    BusResult :=
  refBusResult tables layout w.alphas w.beta w.point w.values w.memory w.mf w.bf

/-- The bus phase after the grand product, followed by `k`: the count root's check, the boundary
values, and `k` of what was read. -/
def busTailK {β : Type} (k : BusWit → VerifierProgram β) (alphas : List E) (beta : E)
    (r : E × List E × List E) : VerifierProgram β :=
  match r with
  | (countRoot, point, values) => do
    VerifierProgram.require (countRoot ≠ 0)
    let memory ← VerifierProgram.readScalars 3
    let mf ← VerifierProgram.readScalar
    let bf ← VerifierProgram.readScalar
    k ⟨alphas, beta, point, values, memory, mf, bf⟩

/-- **The bus phase followed by `f`** is the fingerprint challenges, the grand product at the push
side's depth, and the tail followed by `f` of the result. -/
theorem verifyBusBalance_bind_eq {β : Type} (tables : List Verifier.Table) (layout : Verifier.Layout) (f : BusResult →
    VerifierProgram β) :
    (verifyBusBalance tables computedBytecodeValue layout).bind f =
      abProg.bind fun ab ↦ (verifyGkrGrandProducts
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth).bind
        (busTailK (fun w ↦ f (w.result tables layout)) ab.1 ab.2) := by
  unfold verifyBusBalance computedBytecodeValue abProg busTailK BusWit.result
  simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind,
      VerifierProgram.pure_eq]
  rfl

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (tables : List Verifier.Table) (layout : Verifier.Layout)

/-- The boundary values keep doom: from doom on the grand product's output relation, the values
sent make doom on the bus seam at the protocol's output. -/
theorem values_keep {C : Set (∀ i, TheOracle I i)}
    {ℓ : Gkr.LayerStmt (Bus.Data I) E 3 I.μBus}
    (hpre : RelDoom C (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I)) ℓ)
    (vals : Vector E I.busClaims) : RelDoom C (Seam.bus I) (ℓ.1.1, Bus.busOut hI ℓ vals) :=
  say_keep (fun o hout ↦ Bus.values_reflect hI ℓ o () vals rfl hout) hpre

/-- The grand product's last statement on what the bus phase read. -/
def BusWit.layer (w : BusWit) : Gkr.LayerStmt (Bus.Data I) E 3 I.μBus :=
  layerStmtOf (input, (toAlpha w.alphas, w.beta)) I.μBus ⟨w.values, w.point⟩

/-- The boundary values as the protocol's message. -/
def BusWit.vals (w : BusWit) : Vector E I.busClaims := vecOf I.busClaims (w.memory ++ [w.mf, w.bf])

/-- **The bus seam on the wire, at what was read**: no candidate puts the protocol's output on
those values in the bus seam. -/
def BusAt (w : BusWit) (h : List Ev) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 3 ∧
    HDoom cands (Seam.bus I) (input, Bus.busOut hI (w.layer I input) (w.vals I)) h

/-- **The bus seam on the wire**: the bus phase returns the verifier's leaf decomposition of what it
read, and the bus seam holds of no candidate at the protocol's output on it. -/
def BusPost (bus : BusResult) (h : List Ev) : Prop :=
  ∃ w : BusWit, bus = w.result tables layout ∧ BusAt I hI cands input w h

variable {εmax : ℝ≥0∞}

/-- **The bus phase's tail, then a continuation** specified from the bus seam at what was read:
the count root's check (which rejects the root `0`), the boundary values (the protocol's last
message), then `k`. -/
noncomputable def busTailSpec {β : Type} {k : BusWit → VerifierProgram β} {Q : β → List Ev → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax) (K : ∀ w, Spec (k w) (BusAt I hI cands input w) Q εmax Lk T)
    (alphas : List E) (beta : E) (r : E × List E × List E) :
    Spec (busTailK k alphas beta r) (GkrPost I cands (input, (toAlpha alphas, beta)) r) Q
      εmax 0 T :=
  match r with
  | (countRoot, point, values) =>
    let P : List Ev → Prop := fun h ↦ point.length = I.μBus ∧ values.length = 3 ∧
      HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
        (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨values, point⟩) h
    have hP : ∀ h x, P h → P (h ++ [Ev.read x]) := fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩
    (Spec.require (Post := fun _ h ↦ P h) fun _ hp hc ↦ hp.resolve_left hc).bind' fun _ ↦
    (readNSuccSpec P hP zero_le 2).bind' fun memory ↦
    (Spec.readE (Post := fun _ h ↦ memory.length = 3 ∧ P h)
      (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) zero_le).bind' fun mf ↦
    (Spec.readE (Post := fun bf h ↦ BusAt I hI cands input ⟨alphas, beta, point, values, memory,
        mf, bf⟩ h)
      (fun _ bf hp ↦ by
        obtain ⟨hm, hl, hv, W, hW, hR⟩ := hp
        exact ⟨hl, hv, hm, W, firstWord_append hW _, values_keep I hI hR _⟩) hLk).bind'
      fun bf ↦ K ⟨alphas, beta, point, values, memory, mf, bf⟩

/-- **The bus phase, then a continuation** (`verify_bus_balance`, `bus.rs:106-213`): from
the commitment's doom (no candidate satisfies `M3Holds`, `Seam.commit`) to the bus seam at what
was read, then `f` of the result, specified from there by `K`, at the depth `μ_bus` of the push
side. The fingerprint challenges are charged `L₀ · 4 · 2^{μ_bus} / |E|`; every later group of
challenges (a sumcheck round's, the descendants' combination challenges with the next combiner)
at most `L₀ · 4 / |E|`. -/
noncomputable def busThenSpec {β : Type} {f : BusResult → VerifierProgram β} {Q : β → List Ev
    → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax)
    (K : ∀ w : BusWit, Spec (f (w.result tables layout)) (BusAt I hI cands input w) Q εmax Lk T)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec ((verifyBusBalance tables computedBytecodeValue layout).bind f) (HDoom cands (Seam.commit I)
        input) Q εmax
      (abError I L₀ + 0) T :=
  Spec.congr (verifyBusBalance_bind_eq tables layout f).symm
    ((abSpec I cands input hI hfin hcard hab (T := 0)).bind' fun ab ↦
      (Spec.congr (by rw [hdepth])
        (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam)).bind'
        fun r ↦ busTailSpec I hI cands input hLk K ab.1 ab.2 r)

/-- **The bus phase** alone: from the commitment's doom to the bus seam on the wire. -/
noncomputable def busPhaseSpec {T : ℝ≥0∞} (hTf : T ≤ εmax) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec (verifyBusBalance tables computedBytecodeValue layout) (HDoom cands (Seam.commit I) input)
      (BusPost I hI cands input tables layout) εmax (abError I L₀ + 0) T :=
  Spec.congr (VerifierProgram.bind_ret _)
    (busThenSpec I hI cands input tables layout hTf
      (fun w ↦ (Spec.ret (Post := BusPost I hI cands input tables layout) (w.result tables layout)).mono
        (fun _ hp ↦ ⟨w, rfl, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
      hfin hcard hμ hdepth hab he hT hlam)

end Phase

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontBusPhase` =====

-- ===== merged from `LvmSumcheck` (GOLF module merge: `LvmSumcheck.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/Sumcheck.lean` (formal rev 40f877dc) as `LvmSumcheck` for lvm (WP-2).
/-
  LeanVM.Protocol.ToArkLib.Sumcheck

  The sumcheck of a virtual polynomial (a formula in the values of tables the verifier does not
  evaluate) over a weighted cube, binding the highest variable first, with the tables' values at
  the final point as its last message: the plain variant (unit weights) and the normalized one
  (the weights of an equality polynomial). Definition, perfect completeness, round-by-round
  knowledge soundness, and the decoding of a round message sent without one coefficient.
  Candidate for ArkLib.
-/

/-! lvm (WP-2): the ArkLib-typed components (`rounds`, `final`, `slot`, `weighted`, `plain`,
`normalized`, `transport`) and their typed completeness and security (`roundsComplete`,
`finalComplete`, `weightedComplete`, `finalSecurity`, `roundsSecurity`, `weightedSecurity`,
`finalSecurityInv`, `roundsSecurityInv`), built on `ToArkLib.Typed.*` outside lvm's imports, are
cut. Kept: the virtual polynomial, the claims, the family and its honesty and consistency, the
relations, the final check with its completeness (`final_honest`) and reflection
(`final_reflect`, `final_reflect_inv`), and the wire decoding. Added: `family_sound`, the
soundness fact the cut `roundsSecurity` fed to the round's count. The honest round polynomial is
Mathlib's `Lagrange.interpolate` (leanVM: CompPoly's `CLagrange.interpolate`, outside lvm's
imports), so `roundPoly` is noncomputable. -/

/-!
# The sumcheck of a virtual polynomial

A *virtual polynomial* on `n` variables (`Virtual`) is `m` tables on the cube, read off the
public data, the oracles' contents and the witness, and a formula: the *summand* at a point `z`
is the formula at `z` and at the values of the tables' multilinear extensions there
(`Virtual.summand`). The verifier never evaluates a table; the formula it evaluates itself, so
factors such as an equality polynomial or a padding product belong to the formula. A weight per
coordinate (`CoordWeights`, the weights of the values `0` and `1`) weighs the cube, and the
claim is `Σ_x (∏_k w_k(x_k)) · summand(x) = T` (`relIn`), beside a side condition on the context
that the sumcheck carries unchanged, for a protocol that has more to say of its statement and
oracles than the claim. Two choices of weights:

* *plain* (`plain`, `unitWeights`): unit weights, the claim `Σ_x summand(x) = T`;
* *normalized* (`normalized`, `eqWeights pt`): the weights `(1 - p_k, p_k)` of a point `p` of the
  public data, the claim `Σ_x eq(p, x) · summand(x) = T`. The round message is then the cofactor
  of the equality factor, and the final check has none.

The sumcheck (`weighted`) binds the highest variable first. After `j` rounds the challenges
`c_0, …, c_{j-1}` hold the top `j` coordinates, `c_0` the highest (`point`), and the running
claim (`claim`) is the weighted sum, over the free coordinates only, of the summand at the point
they complete. Each round is `SumcheckRound.round`: the prover sends the `d + 1` coefficients of
the round polynomial, and the verifier checks `w_k(0) · q(0) + w_k(1) · q(1)` against the running
claim, `k` the coordinate the round binds (`domain`), and moves to `q(c)`. The honest round
polynomial (`roundPoly`) interpolates the next claim at `d + 1` distinct nodes (`nodes`, a
parameter: a field of characteristic two has no `0, 1, …, d`). The last message (`final`) is the
tables' values at the final point, the challenges in coordinate order; the verifier checks that
the formula at the point and the values is the running claim, and outputs them through an output
map, by default the point and the values as claims on the tables (`finalOut`, `relOut`).

Completeness (`weightedComplete`) holds when the summand has degree at most `d` in each variable
(`IndividualDegreeLE`): the round polynomial is then a polynomial of degree at most `d`, which
`d + 1` nodes determine. Knowledge soundness (`weightedSecurity`, for either weights) holds under
the same hypotheses, at `d / |F|` on each round's challenge and with the extractor that keeps the
witness, which carries no information: a recorded polynomial that passes the check at a wrong
claim is not the true one, and two polynomials of degree `d` agree at `d` points at most; values
that pass the final check and are the tables' values make the running claim the summand at the
point. Without the final check the last message has no security at any error
(`final_unchecked_no_security`).

*The wire.* A round sent with `d` of its `d + 1` coefficients (the coefficients but coefficient
`k`: `encodeWire`) is decoded by deriving the missing one from the running claim, the
value that makes the round's check hold (`decodeRound`, `decodeWire`); this needs the coefficient's
weight in the check, `Σ_x w(x) · x^k` (`coeffWeight`), to be invertible, which is why a plain round
drops `c_1` (the weight of `c_0` is `1 + 1`, zero in characteristic two) and a normalized round
`c_0`. The decoding is injective (`encodeWire_decodeWire`), and every message that passes the
check is the decoding of its wire (`decodeWire_encodeWire`), so the honest prover's message
survives. `transport`: the round reading its message on the wire and decoding it
(`Typed.Def.decode`) is knowledge sound at the round's errors, with the extractor read on the
decoded message (`Typed.Security.decode`).
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval
open scoped Polynomial

section

namespace Sumcheck

section Def

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}

/-! ## Virtual polynomials -/

/-- A virtual polynomial on `n` variables: `m` tables on the cube, read off the public data, the
oracles' contents and the witness, and a formula giving the summand at a point from the public
data, the point and the tables' values there. -/
structure Virtual (F X : Type) {ι : Type} (O : ι → Type) (W : Type) (n m : ℕ) [Field F] where
  /-- The tables. -/
  tables : SumcheckRound.Ctx X O W → Fin m → CMlPolynomialEval F n
  /-- The formula: the summand from the public data, the point and the tables' values. -/
  formula : X → Vector F n → Vector F m → F

namespace Virtual

variable (V : Virtual F X O W n m)

/-- The values of the tables' extensions at a point. -/
def values (ctx : SumcheckRound.Ctx X O W) (z : Vector F n) : Vector F m :=
  Vector.ofFn fun i ↦ evalMle (V.tables ctx i) z

/-- The summand at a point: the formula at the point and the tables' values there. -/
def summand (ctx : SumcheckRound.Ctx X O W) (z : Vector F n) : F :=
  V.formula ctx.1.1 z (V.values ctx z)

end Virtual

/-- The weights of the values `0` and `1` of each coordinate, from the public data. -/
abbrev CoordWeights (F X : Type) (n : ℕ) : Type := X → Fin n → F × F

/-- Unit weights: the plain sum over the cube. -/
def unitWeights : CoordWeights F X n := fun _ _ ↦ (1, 1)

/-- The weights `(1 - p_k, p_k)` of a point `p` of the public data: the sum against
`eq(p, ·)`. -/
def eqWeights (pt : X → Vector F n) : CoordWeights F X n := fun x k ↦ (1 - (pt x)[k], (pt x)[k])

/-- The weighted sum of the summand over the cube. -/
def weightedSum (V : Virtual F X O W n m) (wt : CoordWeights F X n)
    (ctx : SumcheckRound.Ctx X O W) : F :=
  weightedCubeSum (wt ctx.1.1) (V.summand ctx)

/-! ## The claims, highest variable first -/

/-- The point whose low `n - j` coordinates are `x` and whose top `j` are the challenges `c`, the
first challenge the highest coordinate. -/
def point {j : ℕ} (hj : j ≤ n) (c : Vector F j) (x : Vector F (n - j)) : Vector F n :=
  Vector.ofFn fun k ↦ if h : k.val < n - j then x[k.val] else c[n - 1 - k.val]'(by omega)

/-- The running claim after the challenges `c`: the weighted sum, over the free coordinates, of the
summand at the point they complete. -/
def claim (V : Virtual F X O W n m) (wt : CoordWeights F X n) (ctx : SumcheckRound.Ctx X O W)
    (j : ℕ) (c : Vector F j) : F :=
  if hj : j ≤ n then
    weightedCubeSum (fun a : Fin (n - j) ↦ wt ctx.1.1 ⟨a, by omega⟩)
      fun x ↦ V.summand ctx (point hj c x)
  else 0

/-- The verifier's domain at round `j`: the values `0` and `1` of coordinate `n - 1 - j`, with
their weights. -/
def domain (wt : CoordWeights F X n) : SumcheckRound.Weights F X := fun x j ↦
  if h : j < n then
    [(0, (wt x ⟨n - 1 - j, by omega⟩).1), (1, (wt x ⟨n - 1 - j, by omega⟩).2)]
  else []

/-- The honest round polynomial at round `j`: the interpolation, at the nodes, of the next claim
with the round's coordinate at each node. -/
noncomputable def roundPoly (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) : SumcheckRound.Polys F X O W d := fun ctx j c ↦
  if j < n then
    SumcheckRound.ofPolynomial d (Lagrange.interpolate Finset.univ nodes
      fun i ↦ claim V wt ctx (j + 1) (c.push (nodes i)))
  else SumcheckRound.ofPolynomial d 0

/-- The family of claims of the sumcheck: the running claims, the honest round polynomials, the
domains, and the side condition on the context, which no challenge changes. -/
noncomputable def family (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) (side : SumcheckRound.Ctx X O W → Prop) :
    SumcheckRound.Family F X O W d where
  claim := claim V wt
  poly := roundPoly V wt nodes
  weight := domain wt
  inv := fun ctx _ _ ↦ side ctx

/-- The family of claims of the sumcheck with an invariant that the challenges may change: the
running claims, the honest round polynomials, the domains, and the invariant. -/
noncomputable def familyInv (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) (inv : SumcheckRound.Ctx X O W → (j : ℕ) → Vector F j → Prop) :
    SumcheckRound.Family F X O W d where
  claim := claim V wt
  poly := roundPoly V wt nodes
  weight := domain wt
  inv := inv

/-! ## The relations -/

/-- The output statement: the public data, the final point, and one value per table. -/
abbrev Out (X F : Type) (n m : ℕ) : Type := X × (Vector F n × Vector F m)

/-- The input relation: the claimed sum is the weighted sum of the summand over the cube, and the
side condition holds of the context. -/
def relIn (V : Virtual F X O W n m) (wt : CoordWeights F X n)
    (side : SumcheckRound.Ctx X O W → Prop) : Set ((SumcheckRound.Stmt X F 0 × ∀ i, O i) × W) :=
  {p | p.1.1.2.2 = weightedSum V wt (SumcheckRound.ctxOf p) ∧ side (SumcheckRound.ctxOf p)}

/-- The output relation: each value is its table's extension at the point, and the side condition
holds of the context. -/
def relOut (V : Virtual F X O W n m) (side : SumcheckRound.Ctx X O W → Prop) :
    Set ((Out X F n m × ∀ i, O i) × W) :=
  {p | V.values ((p.1.1.1, p.1.2), p.2) p.1.1.2.1 = p.1.1.2.2 ∧ side ((p.1.1.1, p.1.2), p.2)}

/-! ## The components -/

variable [DecidableEq F]

/-- The final check: the formula at the final point and the values sent is the running claim. -/
def finalCheck (V : Virtual F X O W n m) (s : SumcheckRound.Stmt X F n) (v : Vector F m) : Bool :=
  decide (V.formula s.1 s.2.1.reverse v = s.2.2)

/-- The default output: the final point, in coordinate order, and the values sent. -/
def finalOut (s : SumcheckRound.Stmt X F n) (v : Vector F m) : Out X F n m :=
  (s.1, (s.2.1.reverse, v))

end Def

section Complete

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}
  (V : Virtual F X O W n m) (wt : CoordWeights F X n)

/-! ## Points -/

omit [Field F] in
/-- One more challenge is one free coordinate fewer: the challenge takes the highest free
coordinate. -/
private theorem point_push {j : ℕ} (hj : j < n) (c : Vector F j) (x : F)
    (v : Vector F (n - (j + 1))) :
    point (Nat.succ_le_of_lt hj) (c.push x) v =
      point hj.le c (Vector.cast (by omega) (v.push x)) := by
  apply Vector.ext
  intro k hk
  simp only [point, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_push]
  by_cases h1 : k < n - (j + 1)
  · simp [h1, show k < n - j by omega]
  · by_cases h2 : k < n - j
    · have hk' : k = n - (j + 1) := by omega
      subst hk'
      have e1 : ¬ n - 1 - (n - (j + 1)) < j := by omega
      simp [e1, h2]
    · simp [h1, h2, show n - 1 - k < j by omega]

omit [Field F] in
/-- The coordinate the next challenge takes, set to `x`. -/
private theorem point_push_set {j : ℕ} (hj : j < n) (c : Vector F j) (x y : F)
    (v : Vector F (n - (j + 1))) :
    point (Nat.succ_le_of_lt hj) (c.push x) v =
      (point (Nat.succ_le_of_lt hj) (c.push y) v).set (n - 1 - j) x (by omega) := by
  apply Vector.ext
  intro k hk
  simp only [point, Vector.getElem_ofFn, Vector.getElem_set, Vector.getElem_push]
  by_cases h : n - 1 - j = k
  · simp [h.symm, show ¬ n - 1 - j < n - (j + 1) by omega, show n - 1 - (n - 1 - j) = j by omega]
  · simp only [h, ite_false]
    by_cases h1 : k < n - (j + 1)
    · simp [h1]
    · simp [h1, show n - 1 - k < j by omega]

omit [Field F] in
/-- With every coordinate bound, the point is the challenges in coordinate order. -/
private theorem point_self (c : Vector F n) (v : Vector F (n - n)) :
    point le_rfl c v = c.reverse := by
  apply Vector.ext
  intro k hk
  simp [point, Vector.getElem_reverse]

omit [Field F] in
/-- With no coordinate bound, the point is the free coordinates. -/
private theorem point_zero (v : Vector F (n - 0)) :
    point (Nat.zero_le n) (#v[] : Vector F 0) v = Vector.cast (Nat.sub_zero n) v := by
  apply Vector.ext
  intro k hk
  simp [point]

/-! ## The claims -/

/-- With no challenge, the claim is the weighted sum of the summand over the cube. -/
theorem claim_zero (ctx : SumcheckRound.Ctx X O W) :
    claim V wt ctx 0 #v[] = weightedSum V wt ctx := by
  rw [claim, dite_eq_left (Nat.zero_le n), weightedSum,
    weightedCubeSum_cast (Nat.sub_zero n)]
  congr 1
  funext v
  rw [point_zero]
  congr 1

/-- With every coordinate bound, the claim is the summand at the challenges in coordinate
order. -/
theorem claim_self (ctx : SumcheckRound.Ctx X O W) (c : Vector F n) :
    claim V wt ctx n c = V.summand ctx c.reverse := by
  rw [claim, dite_eq_left le_rfl, weightedCubeSum_cast (Nat.sub_self n), weightedCubeSum_zero,
    point_self]

/-- Binding one more coordinate: the claim is the next claims at `0` and at `1`, weighted by the
coordinate's weights. -/
private theorem claim_split {j : ℕ} (hj : j < n) (ctx : SumcheckRound.Ctx X O W) (c : Vector F j) :
    claim V wt ctx j c =
      (wt ctx.1.1 ⟨n - 1 - j, by omega⟩).1 * claim V wt ctx (j + 1) (c.push 0) +
        (wt ctx.1.1 ⟨n - 1 - j, by omega⟩).2 * claim V wt ctx (j + 1) (c.push 1) := by
  rw [claim, dite_eq_left hj.le, claim, dite_eq_left (Nat.succ_le_of_lt hj), claim,
    dite_eq_left (Nat.succ_le_of_lt hj),
    weightedCubeSum_cast (show n - j = n - (j + 1) + 1 by omega), weightedCubeSum_succ]
  have hw : (⟨(Fin.cast (show n - (j + 1) + 1 = n - j by omega) (Fin.last (n - (j + 1)))).val,
      by omega⟩ : Fin n) = ⟨n - 1 - j, by omega⟩ := Fin.ext (by simp; omega)
  simp only [hw]
  congr 2 <;> refine congrArg₂ (fun w g ↦ weightedCubeSum w g) rfl (funext fun v ↦ ?_) <;>
    rw [point_push hj]

/-- The next claim, as a function of the round's coordinate, is a polynomial of degree at most
`d` when the summand is. -/
private theorem exists_claim_poly {d : ℕ} (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d) {j : ℕ}
    (hj : j < n) (ctx : SumcheckRound.Ctx X O W) (c : Vector F j) :
    ∃ P : F[X], P.natDegree ≤ d ∧ ∀ x, claim V wt ctx (j + 1) (c.push x) = P.eval x := by
  have hle : j + 1 ≤ n := hj
  choose p hp hpe using fun v : Fin (2 ^ (n - (j + 1))) ↦
    hV ctx (n - 1 - j) (point hle (c.push 0) (boolVec v)) (by omega)
  refine ⟨∑ v, Polynomial.C (cubeWeight (fun a : Fin (n - (j + 1)) ↦ wt ctx.1.1 ⟨a, by (clear * - hj; omega)⟩) v) *
    p v, ?_, fun x ↦ ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun v _ ↦
      (Polynomial.natDegree_C_mul_le _ _).trans (hp v)
  · rw [claim, dite_eq_left hle, weightedCubeSum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [point_push_set hj c x 0, hpe, Polynomial.eval_C_mul]

variable {d : ℕ} (nodes : Fin (d + 1) → F)

/-- The honest round polynomial evaluates to the next claim: it interpolates, at `d + 1` distinct
nodes, a polynomial of degree at most `d`. -/
private theorem evaluate_roundPoly (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) {j : ℕ} (hj : j < n) (ctx : SumcheckRound.Ctx X O W)
    (c : Vector F j) (x : F) :
    SumcheckRound.evaluate d (roundPoly V wt nodes ctx j c) x =
      claim V wt ctx (j + 1) (c.push x) := by
  obtain ⟨P, hP, hPe⟩ := exists_claim_poly V wt hV hj ctx c
  have hint : (Lagrange.interpolate Finset.univ nodes
      fun i ↦ claim V wt ctx (j + 1) (c.push (nodes i))) = P := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hnodes.injOn ?_ fun i _ ↦ (hPe _).symm).symm
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.degree_le_of_natDegree_le hP).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  simp only [roundPoly, hj, ↓reduceIte]
  rw [SumcheckRound.evaluate_ofPolynomial, hint, hPe]
  rw [hint]
  exact Polynomial.degree_le_of_natDegree_le hP

/-- The honest round polynomial passes the round's check. -/
private theorem weightedSum_roundPoly (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) {j : ℕ} (hj : j < n) (ctx : SumcheckRound.Ctx X O W)
    (c : Vector F j) :
    SumcheckRound.weightedSum d (domain wt ctx.1.1 j) (roundPoly V wt nodes ctx j c) =
      claim V wt ctx j c := by
  simp only [domain, dite_eq_left hj, SumcheckRound.weightedSum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [evaluate_roundPoly V wt nodes hV hnodes hj, evaluate_roundPoly V wt nodes hV hnodes hj,
    claim_split V wt hj]

variable (side : SumcheckRound.Ctx X O W → Prop)

/-- The family is honest: its round polynomials pass the check and evaluate to the next claim, and
no challenge changes the side condition. -/
theorem family_honest (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) : (family V wt nodes side).Honest n where
  check := fun ctx _ c hj ↦ weightedSum_roundPoly V wt nodes hV hnodes hj ctx c
  next := fun ctx _ c x hj ↦ evaluate_roundPoly V wt nodes hV hnodes hj ctx c x
  inv_push := fun _ _ _ _ _ h ↦ h

/-- The family with a moving invariant is consistent: its round polynomials pass the check and
evaluate to the next claim, whatever the invariant. -/
theorem familyInv_consistent (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes)
    (inv : SumcheckRound.Ctx X O W → (j : ℕ) → Vector F j → Prop) :
    (familyInv V wt nodes inv).Consistent n where
  check := fun ctx _ c hj ↦ weightedSum_roundPoly V wt nodes hV hnodes hj ctx c
  next := fun ctx _ c x hj ↦ evaluate_roundPoly V wt nodes hV hnodes hj ctx c x

/-- The family with a moving invariant, before the first round: the input relation at the
invariant's first stage. -/
theorem rel_zero_inv (inv : SumcheckRound.Ctx X O W → (j : ℕ) → Vector F j → Prop) :
    SumcheckRound.rel (familyInv V wt nodes inv) 0 = relIn V wt (fun ctx ↦ inv ctx 0 #v[]) := by
  ext p
  have hc : p.1.1.2.1 = #v[] := Vector.ext fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  simp only [SumcheckRound.rel, familyInv, relIn, Set.mem_ofPred_eq, hc]
  rw [claim_zero, and_comm]

/-- The family with a moving invariant, after the last round: the invariant at the challenges,
and the running claim is the summand at the challenges in coordinate order. -/
theorem mem_rel_self_inv (inv : SumcheckRound.Ctx X O W → (j : ℕ) → Vector F j → Prop)
    (p : (SumcheckRound.Stmt X F n × ∀ i, O i) × W) :
    p ∈ SumcheckRound.rel (familyInv V wt nodes inv) n ↔
      inv (SumcheckRound.ctxOf p) n p.1.1.2.1 ∧
        p.1.1.2.2 = V.summand (SumcheckRound.ctxOf p) p.1.1.2.1.reverse := by
  simp only [SumcheckRound.rel, familyInv, Set.mem_ofPred_eq]
  rw [claim_self]

/-- The family's relation before the first round is the input relation. -/
theorem rel_zero : SumcheckRound.rel (family V wt nodes side) 0 = relIn V wt side := by
  ext p
  have hc : p.1.1.2.1 = #v[] := Vector.ext fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  simp only [SumcheckRound.rel, family, relIn, Set.mem_ofPred_eq, hc]
  rw [claim_zero, and_comm]

/-- The family's relation after the last round: the side condition, and the running claim is the
summand at the challenges in coordinate order. -/
theorem mem_rel_self (p : (SumcheckRound.Stmt X F n × ∀ i, O i) × W) :
    p ∈ SumcheckRound.rel (family V wt nodes side) n ↔
      side (SumcheckRound.ctxOf p) ∧
        p.1.1.2.2 = V.summand (SumcheckRound.ctxOf p) p.1.1.2.1.reverse := by
  simp only [SumcheckRound.rel, family, Set.mem_ofPred_eq]
  rw [claim_self]

variable [DecidableEq F]

/-- The true values at the final point pass the final check and land in an output relation they
land in whenever the side condition holds. -/
theorem final_honest {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T)
    {relOut' : Set ((T × ∀ i, O i) × W)}
    (h : ∀ s o w, side ((s.1, o), w) →
      ((out s (V.values ((s.1, o), w) s.2.1.reverse), o), w) ∈ relOut')
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i) (w : W)
    (hin : ((s, o), w) ∈ SumcheckRound.rel (family V wt nodes side) n) :
    finalCheck V s (V.values ((s.1, o), w) s.2.1.reverse) = true ∧
      ((out s (V.values ((s.1, o), w) s.2.1.reverse), o), w) ∈ relOut' := by
  obtain ⟨hside, hclaim⟩ := (mem_rel_self V wt nodes side _).mp hin
  refine ⟨?_, h s o w hside⟩
  rw [finalCheck, decide_eq_true_eq, hclaim]
  rfl

end Complete

section Security

variable {F : Type} [Field F] [DecidableEq F]
  {X : Type} {ι : Type} {O : ι → Type} {W : Type}
  {n m : ℕ} (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
  (nodes : Fin (d + 1) → F) (side : SumcheckRound.Ctx X O W → Prop)

/-- Values that pass the final check, for an output relation from which they are the tables'
values at the final point and the side condition holds, make the running claim the summand at
the point. -/
theorem final_reflect {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T)
    {relOut' : Set ((T × ∀ i, O i) × W)}
    (h : ∀ s o w v, ((out s v, o), w) ∈ relOut' →
      V.values ((s.1, o), w) s.2.1.reverse = v ∧ side ((s.1, o), w))
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i) (w : W) (v : Vector F m)
    (hc : finalCheck V s v = true) (hout : ((out s v, o), w) ∈ relOut') :
    ((s, o), w) ∈ SumcheckRound.rel (family V wt nodes side) n := by
  obtain ⟨hv, hside⟩ := h s o w v hout
  rw [mem_rel_self V wt nodes side]
  rw [finalCheck, decide_eq_true_eq] at hc
  refine ⟨hside, ?_⟩
  rw [← hc]
  exact congrArg (V.formula s.1 s.2.1.reverse) hv.symm

omit [DecidableEq F] in
/-- The family is sound: its invariant, the side condition, is the same at every stage, so no
challenge restores it (lvm: the fact leanVM's cut `roundsSecurity` passes to
`SumcheckRound.roundsSecurity`; with `family_honest` it gives `SumcheckRound.card_badChallenge_le`
for each round). -/
theorem family_sound [Finite F] : (family V wt nodes side).Sound n :=
  fun _ _ _ _ h ↦ (Nat.card_eq_zero.mpr (Or.inl ⟨fun x ↦ h x.2⟩)).trans_le (Nat.zero_le d)

/-- The count behind the cut `roundsSecurity` (lvm, new): at each round `j < n` of the sumcheck of
a summand of degree at most `d` in each variable, a recorded polynomial that passes the check has
at most `d` bad challenges, among the `|F|` the verifier may draw. -/
theorem card_badChallenge_le [Finite F] [Subsingleton W]
    (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d) (hnodes : Function.Injective nodes)
    {j : ℕ} (hj : j < n) (p : SumcheckRound.MidStmt X F j d) (o : ∀ i, O i)
    (hc : SumcheckRound.check j (family V wt nodes side).weight p.1 p.2 = true) :
    Nat.card {x // SumcheckRound.badChallenge j (family V wt nodes side) p o x} ≤ d :=
  SumcheckRound.card_badChallenge_le j (family V wt nodes side)
    (family_honest V wt nodes side hV hnodes).toConsistent (family_sound V wt nodes side) hj p o hc

variable (inv : SumcheckRound.Ctx X O W → (j : ℕ) → Vector F j → Prop)

/-- Values that pass the final check, for an output relation from which they are the tables'
values at the final point and the invariant holds at the challenges, make the last stage's
relation hold. -/
theorem final_reflect_inv {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T)
    {relOut' : Set ((T × ∀ i, O i) × W)}
    (h : ∀ s o w v, ((out s v, o), w) ∈ relOut' →
      V.values ((s.1, o), w) s.2.1.reverse = v ∧ inv ((s.1, o), w) n s.2.1)
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i) (w : W) (v : Vector F m)
    (hc : finalCheck V s v = true) (hout : ((out s v, o), w) ∈ relOut') :
    ((s, o), w) ∈ SumcheckRound.rel (familyInv V wt nodes inv) n := by
  obtain ⟨hv, hinv⟩ := h s o w v hout
  rw [mem_rel_self_inv V wt nodes inv]
  rw [finalCheck, decide_eq_true_eq] at hc
  refine ⟨hinv, ?_⟩
  rw [← hc]
  exact congrArg (V.formula s.1 s.2.1.reverse) hv.symm

end Security

section Wire

variable {F : Type} [Field F] {d : ℕ}

/-! ## The wire: a round message without one coefficient -/

/-- The weight of coefficient `i` in a round's check: `Σ_{(x, w)} w · x^i` over the domain. -/
def coeffWeight (dom : SumcheckRound.WeightedDomain F) (i : ℕ) : F :=
  (dom.map fun p ↦ p.2 * p.1 ^ i).sum

/-- The round's check is linear in the coefficients, coefficient `i` weighted by
`coeffWeight dom i`. -/
theorem weightedSum_eq_sum (dom : SumcheckRound.WeightedDomain F) (q : SumcheckRound.Message F d) :
    SumcheckRound.weightedSum d dom q = ∑ i : Fin (d + 1), q[i] * coeffWeight dom i := by
  simp only [SumcheckRound.weightedSum, SumcheckRound.evaluate, coeffWeight]
  induction dom with
  | nil => simp
  | cons p dom ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.mul_sum]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The message with coefficient `k` derived from the running claim: the value that makes the
round's check hold, whatever the message carried there. -/
def decodeRound (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim : F)
    (q : SumcheckRound.Message F d) : SumcheckRound.Message F d :=
  q.set k ((claim - ∑ i ∈ Finset.univ.erase k, q[i] * coeffWeight dom i) / coeffWeight dom k)

variable {X : Type} {ι : Type} {O : ι → Type}

/-- The wire's message: the coefficients but coefficient `k`, in order. -/
def encodeWire (k : Fin (d + 1)) (q : SumcheckRound.Message F d) : Vector F d :=
  Vector.ofFn fun i : Fin d ↦ if i.val < k.val then q[i.val] else q[i.val + 1]

/-- The coefficients read off the wire, with `0` in position `k`. -/
def expandWire (k : Fin (d + 1)) (w : Vector F d) : SumcheckRound.Message F d :=
  Vector.ofFn fun i : Fin (d + 1) ↦
    if h : i.val < k.val then w[i.val]'(by omega)
    else if h' : i.val = k.val then 0 else w[i.val - 1]'(by omega)

/-- The round message decoded from the wire: coefficient `k` derived from the running claim. -/
def decodeWire (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim : F)
    (w : Vector F d) : SumcheckRound.Message F d :=
  decodeRound dom k claim (expandWire k w)


end Wire

end Sumcheck

end
end LeanVM.Protocol
end
-- ===== end of `LvmSumcheck` =====

-- ===== merged from `LvmTableSumcheck` (GOLF module merge: `LvmTableSumcheck.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/TableSumcheck.lean` (formal rev 40f877dc) as `LvmTableSumcheck` for lvm (WP-2).
/-
  LeanVM.Protocol.TableSumcheck

  The table sumcheck phase: the batching challenge `ξ`, one plain sumcheck over the rows of the
  sumcheck tables, and the values of their columns at the final point. Definition, perfect
  completeness and round-by-round knowledge soundness.
-/

/-! lvm (WP-2): cut, as ArkLib's typed front (`ToArkLib.Typed.*`): `batchStep`, `tableSumcheck`,
`tableSumcheckComplete`, `xiSecurity`, `finalValuesSecurity`, `roundsSecurity`,
`tableSumcheckSecurity` (and the `Spine.Slots` they are typed at). Kept: every definition and
fact they are built from. Added: the counts the cut securities stood for, `card_xi_le` (the
batching challenge, `B + 2`) and `card_round_badChallenge_le` (each round, `3`). Row polynomials are
Mathlib `MvPolynomial`s (see `LvmSpineInstance`). -/

/-!
# The table sumcheck phase

Specification §5.5 (`doc/leanvm/body/05-arithmetization.tex:125-150` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`), over an abstract instance `I`.

The bus phase ends at a point `ζ` and leaves two kinds of claim on the rows of the *sumcheck
tables* (those with a constraint, a flush or a count column): every constraint `C_{t,i}` of table
`t` has extension zero at `ζ_{<τ_t}`, and for each side `s` of the bus the forms `B^s_t` of the
tables sum to the side's total at `ζ` (`Seam.bus`). Each is a sum over one table's rows weighted
by `eq(ζ_{<τ_t}, ·)` of a polynomial of degree at most `d` in the table's columns, and one
sumcheck proves them all:

1. the verifier draws `ξ` and batches the claims by its powers (`batchStep`, `Typed.batch`):
   constraint `i` of table `t` gets `ξ^{o_t + i}`, with the constraints numbered table by table
   (`constraintPos`), and side `s` gets `ξ^{B + s}`, the three powers shared by the tables, so the
   target `Σ_s ξ^{B+s} · total_s` is derived by the verifier and never sent;
2. a plain sumcheck of degree three on `τ_max` variables, highest first, of the virtual polynomial
   `tableSummand`: its tables are the sumcheck tables' columns, each read on `τ_max` variables as
   the same in every slice of the coordinates its table does not have (`table`), and its formula
   is §5.5's `F`, `Σ_t eq(ζ_{<τ_t}, X_{<τ_t}) · ∏_{k ≥ τ_t} X_k · (Σ_i ξ^{o_t+i} C_{t,i} +
   Σ_s ξ^{B+s} B^s_t)` at the tables' values (`formula`), the factor of table `t` the
   multilinear weight of its coordinates (`tableWeights`), `eq` below `τ_t` and the padding
   `X_k` above, so that table `t` joins at round `τ_max − τ_t`;
3. the prover sends one value per column of each sumcheck table, table by table (`columnPos`);
   the verifier checks the formula at the final point against the running claim, and hands on
   the bus phase's column claims followed by one claim per column at the final point's low
   coordinates (`tableOut`).

The sum of the summand over the cube is the batch of the true values, each constraint's extension
at `ζ` and each side's forms summed (`sum_tableSummand`), so it is the target exactly when the bus
seam's two claims hold (`tableSummand_target`). In characteristic two the factor
`(1 − r)(1 − ζ) + rζ` of `eq` is the deployed `1 + ζ + r`.

Perfect completeness (`tableSumcheckComplete`), from `Seam.bus` to `Seam.table`, needs the
degree bound `d ≤ 2`: the slot's rounds are cubic, and the summand has degree `d + 1` in each
variable (`tableSummand_degree`). The bus phase's column claims, the public lines and the Keccak
predicate ride through the sumcheck as its side condition (`side`), and the Keccak predicate holds
along every point (`M3Instance.auxAt_of_aux`), so at the final one.

Round-by-round knowledge soundness (`tableSumcheckSecurity`), between the same seams and under the
same bound, is at the slot's error: `(B + 2)/|E|` on `ξ`, since a false claim among the `B + 3`
batched survives only at a root of a nonzero polynomial of degree at most `B + 2` in `ξ`, the
true values being fixed before it (`trueValues`); `3/|E|` on each round's challenge; nothing on
the final values, which the table seam determines (`finalClaims_holds_iff`). The Keccak predicate
is not checked by any challenge of its own: the table seam asks it at the final point
(`M3Instance.auxAt`), and the rounds carry it as an invariant along the challenges
(`inv`, `M3Instance.auxStage`), the zero test of `Spine/KeccakZero.lean` with the high coordinates
bound first, as the rounds draw them. A round that restores a broken invariant does so at one
challenge at most (`inv_sound`), within the round's own `3/|E|`: a candidate alive after the round
had a true claim and a true invariant before it, or a challenge among the round polynomial's three
agreements with the honest one or the zero test's one root.

Written from the specification; the order of the powers, the shared side powers, the weights and
the order of the final values are checked against `crates/leanvm_core/src/cpu/mod.rs:388-406`,
`crates/verifier/src/lib.rs:231-249` and `crates/verifier/src/bus.rs:211-260` at the pin.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal

noncomputable section

namespace TableSumcheck

variable (I : M3Instance)

/-! ## Positions, table by table -/

/-- A family of sizes over the tables, kept on the sumcheck tables and zero on the others. -/
def onSumcheck (f : Fin I.ntab → ℕ) (j : Fin I.ntab) : ℕ := if I.SumcheckTable j then f j else 0

/-- Summing the kept sizes over every table is summing the sizes over the sumcheck tables. -/
theorem sum_onSumcheck (f : Fin I.ntab → ℕ) :
    ∑ j, onSumcheck I f j = ∑ j : I.SumcheckTables, f j.1 := by
  simp only [onSumcheck]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun j ↦ by simp) f

variable {I} in
/-- A position below a kept size is on a sumcheck table. -/
theorem sumcheckTable_of_lt {f : Fin I.ntab → ℕ} {j : Fin I.ntab} {i : ℕ}
    (hi : i < onSumcheck I f j) : I.SumcheckTable j := by
  by_contra h
  simp [onSumcheck, h] at hi

/-- The items of a family over the sumcheck tables are the items over every table of the kept
sizes. -/
def sigmaOnSumcheck (f : Fin I.ntab → ℕ) :
    (Σ j : I.SumcheckTables, Fin (f j.1)) ≃ Σ j : Fin I.ntab, Fin (onSumcheck I f j) where
  toFun p := ⟨p.1.1, Fin.cast (by simp [onSumcheck, p.1.2]) p.2⟩
  invFun p := ⟨⟨p.1, sumcheckTable_of_lt p.2.isLt⟩,
    Fin.cast (by simp [onSumcheck, sumcheckTable_of_lt p.2.isLt]) p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The position of each item of a family over the sumcheck tables, numbered table by table:
item `i` of table `t` is at `i` plus the sizes of the sumcheck tables before `t`
(`position_val`). -/
def position (f : Fin I.ntab → ℕ) :
    (Σ j : I.SumcheckTables, Fin (f j.1)) ≃ Fin (∑ j : I.SumcheckTables, f j.1) :=
  (sigmaOnSumcheck I f).trans (finSigmaFinEquiv.trans (finCongr (sum_onSumcheck I f)))

/-- Item `i` of table `t` is at `i` plus the sizes of the sumcheck tables before `t`. -/
theorem position_val (f : Fin I.ntab → ℕ) (p : Σ j : I.SumcheckTables, Fin (f j.1)) :
    (position I f p : ℕ) =
      ∑ j : Fin p.1.1.val, onSumcheck I f (Fin.castLE p.1.1.isLt.le j) + p.2 := by
  simp [position, sigmaOnSumcheck]

/-- The constraints of the sumcheck tables, table by table: the powers of `ξ` they take. -/
abbrev constraintPos :
    (Σ t : I.SumcheckTables, Fin (I.constraints t.1).length) ≃ Fin I.B :=
  position I fun j ↦ (I.constraints j).length

/-- The columns of the sumcheck tables, table by table: the order of the final values. -/
abbrev columnPos : (Σ t : I.SumcheckTables, Fin (I.width t.1)) ≃ Fin I.tableColumns :=
  position I I.width

/-! ## The virtual polynomial -/

/-- The public data of the sumcheck: the statement, the bus phase's output, and `ξ`. -/
abbrev Data : Type := (I.Stmt × BusOut I) × E

/-- Column `k` of the sumcheck tables, table by table, lifted to `E` and read on the sumcheck's
`τ_max` variables: the same in every slice of the coordinates its table does not have. -/
def table (q : Column I.μ) (k : Fin I.tableColumns) : CMlPolynomialEval E I.τmax :=
  repeatHigh (CMlPolynomialEval.map (algebraMap K E)
    (I.column q ⟨((columnPos I).symm k).1.1, ((columnPos I).symm k).2⟩).values)
    (I.τ_le_τmax ((columnPos I).symm k).1)

/-- The values of table `t`'s columns among the values of all the columns. -/
def tableValues (v : Vector E I.tableColumns) (t : I.SumcheckTables) : Fin (I.width t.1) → E :=
  fun i ↦ v[columnPos I ⟨t, i⟩]

variable {I} in
/-- A row polynomial at values in `E` of its table's columns. -/
noncomputable def evalRow {j : Fin I.ntab} (P : MvPolynomial (Fin (I.width j)) K)
    (e : Fin (I.width j) → E) : E :=
  MvPolynomial.eval₂ (algebraMap K E) e P

variable {I} in
/-- A form at values in `E` of its table's columns. -/
def formAt {j : Fin I.ntab} (f : I.Form j) (e : Fin (I.width j) → E) : E :=
  (f.map fun p ↦ p.1 * evalRow p.2.1 e).sum

/-- What table `t` owes at values `e` of its columns: constraint `i` weighted by `ξ` to its
position, and the form of side `s` weighted by `ξ^(B + s)`. -/
def rowValue (x : Data I) (t : I.SumcheckTables) (e : Fin (I.width t.1) → E) : E :=
  (∑ i : Fin (I.constraints t.1).length,
    x.2 ^ (constraintPos I ⟨t, i⟩ : ℕ) * evalRow (I.constraints t.1)[i] e) +
  ∑ s : Fin 3, x.2 ^ (I.B + s.val) * formAt (x.1.2.forms s t) e

/-- The weights of table `t`'s coordinates in the sumcheck: those of `eq(ζ_b, ·)` below its
log-height, and the padding's, `(0, 1)`, above it. -/
def tableWeights (ζ : Vector E I.τmax) (t : I.SumcheckTables) : Fin I.τmax → E × E :=
  fun b ↦ if b.val < I.τ t.1 then (1 - ζ[b], ζ[b]) else (0, 1)

/-- The formula of the table sumcheck, §5.5's `F` at a point and at the columns' values there:
table by table, the multilinear weight of its coordinates times what it owes. -/
def formula (x : Data I) (z : Vector E I.τmax) (v : Vector E I.tableColumns) : E :=
  ∑ t : I.SumcheckTables,
    prodWeight (tableWeights I x.1.2.point t) z * rowValue I x t (tableValues I v t)

/-- The virtual polynomial of the table sumcheck: the sumcheck tables' columns and the formula. -/
def tableSummand : Sumcheck.Virtual E (Data I) (TheOracle I) Unit I.τmax I.tableColumns where
  tables := fun ctx ↦ table I (theStack ctx.1.2)
  formula := formula I

/-! ## The phase -/

/-- The claimed values of the batch: zero for each constraint, then the three sides' totals. -/
def claimed (s : I.Stmt × BusOut I) : Fin (I.B + 3) → E := Fin.append (fun _ ↦ 0) s.2.totals

/-- The sumcheck's first statement: the data with `ξ`, no challenge yet, and the claim. -/
def start (s : I.Stmt × BusOut I) (ξ c : E) : SumcheckRound.Stmt (Data I) E 0 :=
  ((s, ξ), (#v[], c))

/-- Four distinct points of `E`, at which the honest prover interpolates its cubic round
polynomials. -/
def nodes : Fin 4 → E := ![0, 1, y, y + 1]

/-- The final claim on column `k` of the sumcheck tables: its value at the final point's low
coordinates is value `k`. -/
def finalClaim (r : Vector E I.τmax) (v : Vector E I.tableColumns) (k : Fin I.tableColumns) :
    ColumnClaim I :=
  ⟨⟨((columnPos I).symm k).1.1, ((columnPos I).symm k).2⟩, I.lowPoint r ((columnPos I).symm k).1,
    v[k]⟩

/-- The final claims: one per column of each sumcheck table, table by table. -/
def finalClaims (r : Vector E I.τmax) (v : Vector E I.tableColumns) :
    Vector (ColumnClaim I) I.tableColumns :=
  Vector.ofFn (finalClaim I r v)

/-- The phase's output: the bus phase's column claims carried forward, then the final claims at
the final point in coordinate order. -/
def tableOut (s : SumcheckRound.Stmt (Data I) E I.τmax) (v : Vector E I.tableColumns) :
    I.Stmt × TableOut I :=
  (s.1.1.1, ⟨s.1.1.2.columns ++ finalClaims I s.2.1.reverse v, s.2.1.reverse⟩)

/-! ## The columns -/

/-- Column `k`'s table at a point is its column's extension at the point's low coordinates. -/
private theorem evalMle_table (q : Column I.μ) (k : Fin I.tableColumns) (z : Vector E I.τmax) :
    evalMle (table I q k) z =
      eval₂Mle (I.column q ⟨((columnPos I).symm k).1.1, ((columnPos I).symm k).2⟩).values
        (algebraMap K E) (I.lowPoint z ((columnPos I).symm k).1) :=
  evalMle_repeatHigh _ _ z

/-- The values at a point of table `t`'s columns are their extensions at the point's low
coordinates. -/
private theorem tableValues_values (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit)
    (z : Vector E I.τmax) (t : I.SumcheckTables) (i : Fin (I.width t.1)) :
    tableValues I ((tableSummand I).values ctx z) t i =
      eval₂Mle (I.column (theStack ctx.1.2) ⟨t.1, i⟩).values (algebraMap K E) (I.lowPoint z t) := by
  simp only [tableValues, Sumcheck.Virtual.values, Fin.getElem_fin, Vector.getElem_ofFn,
    tableSummand]
  rw [evalMle_table, Equiv.symm_apply_apply]

/-! ## The sum over the cube -/

/-- Constraint `p` of its table: its extension at the bus point's low coordinates. -/
def constraintValue (s : I.Stmt × BusOut I) (q : Column I.μ)
    (p : Σ t : I.SumcheckTables, Fin (I.constraints t.1).length) : E :=
  evalMle (I.virtualTable q p.1.1 (I.constraints p.1.1)[p.2]) (I.lowPoint s.2.point p.1)

/-- A side's forms at the bus point, summed over the sumcheck tables. -/
def formTotal (s : I.Stmt × BusOut I) (q : Column I.μ) (side : Fin 3) : E :=
  ∑ t, M3Instance.Form.eval I (s.2.forms side t) q (I.lowPoint s.2.point t)

/-- The true values of the batched claims: each constraint's extension at the bus point, table by
table, then each side's forms summed. -/
def trueValues (s : I.Stmt × BusOut I) (q : Column I.μ) : Fin (I.B + 3) → E :=
  Fin.append (fun k ↦ constraintValue I s q ((constraintPos I).symm k)) (formTotal I s q)

variable {I} in
/-- A row polynomial at the lift of values in `K` is the lift of its value. -/
theorem evalRow_ofK {j : Fin I.ntab} (P : MvPolynomial (Fin (I.width j)) K)
    (r : Fin (I.width j) → K) :
    evalRow P (fun i ↦ ofK (r i)) = ofK (MvPolynomial.eval r P) := by
  rw [evalRow, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
  show _ = algebraMap K E (MvPolynomial.eval₂ (RingHom.id K) r P)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl

/-- A virtual table's extension is the sum of its rows against the Lagrange basis. -/
private theorem evalMle_virtualTable (q : Column I.μ) (j : Fin I.ntab)
    (P : MvPolynomial (Fin (I.width j)) K) (z : Vector E (I.τ j)) :
    evalMle (I.virtualTable q j P) z =
      ∑ x, (lagrangeBasis z)[x] * ofK (MvPolynomial.eval (I.row q j x) P) := by
  rw [evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [M3Instance.virtualTable, mul_comm]

/-- A form's value at the rows, summed against the Lagrange basis, is the form's value. -/
private theorem sum_formAt (q : Column I.μ) (j : Fin I.ntab) (f : I.Form j) (z : Vector E (I.τ j)) :
    ∑ x, (lagrangeBasis z)[x] * formAt f (fun i ↦ ofK (I.row q j x i)) =
      M3Instance.Form.eval I f q z := by
  induction f with
  | nil => simp [formAt, M3Instance.Form.eval]
  | cons p f ih =>
    simp only [formAt, M3Instance.Form.eval, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, evalMle_virtualTable, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [evalRow_ofK]
    ring

/-- Table `t`'s share of the sum over the cube: its constraints' extensions and its forms at the
bus point, by their powers of `ξ`. The padding coordinates keep only their value `1`, and the
coordinates below `τ_t` weigh the rows by `eq(ζ_{<τ_t}, ·)`. -/
private theorem weightedCubeSum_table (x : Data I) (o : ∀ i, TheOracle I i) (t : I.SumcheckTables) :
    weightedCubeSum (fun _ ↦ ((1 : E), (1 : E))) (fun z ↦
        prodWeight (tableWeights I x.1.2.point t) z *
          rowValue I x t (tableValues I ((tableSummand I).values ((x, o), ()) z) t)) =
      (∑ i, x.2 ^ (constraintPos I ⟨t, i⟩ : ℕ) * constraintValue I x.1 (theStack o) ⟨t, i⟩) +
        ∑ s : Fin 3, x.2 ^ (I.B + s.val) *
          M3Instance.Form.eval I (x.1.2.forms s t) (theStack o) (I.lowPoint x.1.2.point t) := by
  rw [weightedCubeSum_one_prodWeight]
  have hv : (fun z ↦ rowValue I x t (tableValues I ((tableSummand I).values ((x, o), ()) z) t)) =
      fun z ↦ (fun y ↦ rowValue I x t fun i ↦
        eval₂Mle (I.column (theStack o) ⟨t.1, i⟩).values (algebraMap K E) y)
          (lowCoords (I.τ_le_τmax t) z) := by
    funext z
    congr 1
    funext i
    exact tableValues_values I _ z t i
  rw [hv, weightedCubeSum_lowCoords (I.τ_le_τmax t) _
    (fun b hb ↦ by simp [tableWeights, not_lt.mpr hb]) (fun y ↦ rowValue I x t fun i ↦
      eval₂Mle (I.column (theStack o) ⟨t.1, i⟩).values (algebraMap K E) y)]
  have hw : (fun a : Fin (I.τ t.1) ↦ tableWeights I x.1.2.point t (Fin.castLE (I.τ_le_τmax t) a)) =
      fun a : Fin (I.τ t.1) ↦
        (1 - (I.lowPoint x.1.2.point t)[a], (I.lowPoint x.1.2.point t)[a]) := by
    funext a
    have h : (I.lowPoint x.1.2.point t)[a] = x.1.2.point[a.val]'(a.isLt.trans_le (I.τ_le_τmax t)) :=
      getElem_lowCoords (I.τ_le_τmax t) _ a.isLt
    simp only [tableWeights, Fin.val_castLE, a.isLt, ite_true, Fin.getElem_fin, h]
  rw [hw, weightedCubeSum_eq]
  have hrow : ∀ (y : Fin (2 ^ I.τ t.1)) (i : Fin (I.width t.1)),
      eval₂Mle (I.column (theStack o) ⟨t.1, i⟩).values (algebraMap K E) (boolVec y) =
        ofK (I.row (theStack o) t.1 y i) := fun y i ↦ by
    rw [eval₂Mle, evalMle_boolVec]
    simp [CMlPolynomialEval.map, M3Instance.row, Vector.get_eq_getElem]
  simp only [hrow, rowValue, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [constraintValue, evalMle_virtualTable, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [evalRow_ofK]
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← sum_formAt I (theStack o) t.1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    ring

/-- The batch of a family of values with the three side values after the constraints' is the
constraints' part by their powers plus the sides' by `ξ^(B + s)`. -/
private theorem powerBatch_append (A : Fin I.B → E) (S : Fin 3 → E) (ξ : E) :
    powerBatch (Fin.append A S) ξ =
      (∑ k, A k * ξ ^ (k : ℕ)) + ∑ s : Fin 3, S s * ξ ^ (I.B + s.val) := by
  simp [powerBatch, Fin.sum_univ_add]

/-- **The sum of the table sumcheck's summand over the cube** is the true values batched by the
powers of `ξ`: each constraint's extension at the bus point by its power, each side's forms
summed by the side's. -/
theorem sum_tableSummand (x : Data I) (o : ∀ i, TheOracle I i) :
    Sumcheck.weightedSum (tableSummand I) Sumcheck.unitWeights ((x, o), ()) =
      powerBatch (trueValues I x.1 (theStack o)) x.2 := by
  have h : Sumcheck.weightedSum (tableSummand I) Sumcheck.unitWeights ((x, o), ()) =
      weightedCubeSum (fun _ ↦ ((1 : E), (1 : E))) fun z ↦ ∑ t : I.SumcheckTables,
        prodWeight (tableWeights I x.1.2.point t) z *
          rowValue I x t (tableValues I ((tableSummand I).values ((x, o), ()) z) t) := rfl
  rw [h, weightedCubeSum_finsetSum]
  simp only [weightedCubeSum_table]
  rw [trueValues, powerBatch_append, Finset.sum_add_distrib]
  congr 1
  · rw [← (constraintPos I).sum_comp, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Equiv.symm_apply_apply, mul_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [formTotal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [mul_comm]

/-- The true values are the claimed ones exactly when the bus seam's two claims hold: every
constraint's extension is zero at the bus point, and each side's forms sum to its total. -/
theorem trueValues_eq_claimed_iff (s : I.Stmt × BusOut I) (q : Column I.μ) :
    trueValues I s q = claimed I s ↔
      (∀ j : I.SumcheckTables, ∀ C ∈ I.constraints j.1,
        evalMle (I.virtualTable q j.1 C) (I.lowPoint s.2.point j) = 0) ∧
      ∀ side, ∑ j : I.SumcheckTables,
        M3Instance.Form.eval I (s.2.forms side j) q (I.lowPoint s.2.point j) = s.2.totals side := by
  constructor
  · intro h
    refine ⟨fun j C hC ↦ ?_, fun side ↦ ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
      have := congrFun h (Fin.castAdd 3 (constraintPos I ⟨j, ⟨i, hi⟩⟩))
      simp only [trueValues, claimed, Fin.append_left] at this
      rw [Equiv.symm_apply_apply] at this
      exact this
    · have := congrFun h (Fin.natAdd I.B side)
      simpa [trueValues, claimed, formTotal] using this
  · rintro ⟨hc, hf⟩
    funext k
    cases k using Fin.addCases with
    | left k =>
      simp only [trueValues, claimed, Fin.append_left, constraintValue]
      exact hc _ _ (List.getElem_mem _)
    | right side =>
      simp only [trueValues, claimed, Fin.append_right]
      exact hf side

/-! ## The degree -/

/-- A form at values of degree at most one in a coordinate has degree at most `2` there, when
the instance's degree bound is. -/
private theorem degreeLEAt_formAt (hd : I.d ≤ 2) {j : Fin I.ntab} (f : I.Form j) {k : ℕ}
    {e : Fin (I.width j) → Vector E I.τmax → E} (he : ∀ i, DegreeLEAt (e i) k 1) :
    DegreeLEAt (fun z ↦ formAt f fun i ↦ e i z) k 2 := by
  induction f with
  | nil => simpa [formAt] using (DegreeLEAt.const (0 : E)).mono (Nat.zero_le 2)
  | cons p f ih =>
    simp only [formAt, List.map_cons, List.sum_cons] at ih ⊢
    exact (((DegreeLEAt.const p.1).mul
      (DegreeLEAt.mvPolynomial_eval₂ (algebraMap K E) p.2.1 (p.2.2.trans hd) he)).mono
        (by (clear * -; omega))).add ih

/-- The summand has degree at most `3` in each variable when the instance's degree bound is at
most `2`: the weight of a table's coordinates has degree one in each, and what the table owes
is a polynomial of degree at most `d` in its columns' extensions, each of degree one. -/
theorem tableSummand_degree (hd : I.d ≤ 2) (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) :
    IndividualDegreeLE ((tableSummand I).summand ctx) 3 := by
  intro k
  have hval : ∀ (t : I.SumcheckTables) (i : Fin (I.width t.1)),
      DegreeLEAt (fun z ↦ tableValues I ((tableSummand I).values ctx z) t i) k 1 := fun t i ↦ by
    have e : (fun z ↦ tableValues I ((tableSummand I).values ctx z) t i) =
        fun z ↦ evalMle ((tableSummand I).tables ctx (columnPos I ⟨t, i⟩)) z := by
      funext z
      simp [tableValues, Sumcheck.Virtual.values]
    rw [e]
    exact DegreeLEAt.evalMle _
  have hrow : ∀ t : I.SumcheckTables, DegreeLEAt
      (fun z ↦ rowValue I ctx.1.1 t (tableValues I ((tableSummand I).values ctx z) t)) k 2 :=
    fun t ↦ (DegreeLEAt.sum _ fun i _ ↦ ((DegreeLEAt.const _).mul
      (DegreeLEAt.mvPolynomial_eval₂ (algebraMap K E) _
        ((I.constraints_degree t.1 _ (List.getElem_mem _)).trans hd) (hval t))).mono
          (by (clear * -; omega))).add
      (DegreeLEAt.sum _ fun s _ ↦ ((DegreeLEAt.const _).mul
        (degreeLEAt_formAt I hd _ (hval t))).mono (by (clear * -; omega)))
  show DegreeLEAt (fun z ↦ ∑ t : I.SumcheckTables,
    prodWeight (tableWeights I ctx.1.1.1.2.point t) z *
      rowValue I ctx.1.1 t (tableValues I ((tableSummand I).values ctx z) t)) k (1 + 2)
  exact DegreeLEAt.sum _ fun t _ ↦ (DegreeLEAt.prodWeight _).mul (hrow t)

/-! ## Completeness -/

/-- The nodes are distinct. -/
theorem nodes_injective : Function.Injective nodes := by
  have y0 : y ≠ 0 := fun h ↦ by
    have h3 := y_pow_three
    rw [h] at h3
    simp at h3
  have y1 : y ≠ 1 := fun h ↦ by
    have h3 := y_pow_three
    rw [h] at h3
    simp at h3
  have y10 : y + 1 ≠ 0 := fun h ↦ by
    have h3 := y_pow_three
    rw [h] at h3
    exact y0 (pow_eq_zero_iff (by norm_num) |>.mp h3)
  have y11 : y + 1 ≠ 1 := fun h ↦ y0 (add_eq_right.mp h)
  have y1y : y + 1 ≠ y := fun h ↦ one_ne_zero (add_eq_left.mp h)
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [nodes, y0.symm, y1.symm, y10.symm, y11.symm, y1y.symm]

/-- What the sumcheck carries unchanged: the bus phase's column claims and the public lines. -/
def sideRest (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) : Prop :=
  (∀ c ∈ ctx.1.1.1.2.columns.toList, c.Holds (theStack ctx.1.2)) ∧
    I.PublicLinesHold ctx.1.1.1.1 (theStack ctx.1.2)

/-- What the sumcheck's completeness carries unchanged: the bus phase's column claims, the public
lines and the Keccak predicate. -/
def side (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) : Prop :=
  (∀ c ∈ ctx.1.1.1.2.columns.toList, c.Holds (theStack ctx.1.2)) ∧
    I.PublicLinesHold ctx.1.1.1.1 (theStack ctx.1.2) ∧ I.aux (theStack ctx.1.2)

/-- The rounds' invariant for soundness: the bus phase's column claims and the public lines,
unchanged, and the Keccak predicate along the challenges drawn so far
(`M3Instance.auxStage`), which each challenge may break or restore. -/
def inv (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) (j : ℕ) (c : Vector E j) : Prop :=
  sideRest I ctx ∧ I.auxStage c.toList (theStack ctx.1.2)

/-- Before the first challenge, the invariant is the side condition. -/
theorem inv_zero (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) :
    inv I ctx 0 #v[] ↔ side I ctx := by
  simp only [inv, sideRest, side, Vector.toList_mk, M3Instance.auxStage_nil, and_assoc]

/-- **A round restores a broken invariant at one challenge at most**: the bus claims and the
public lines do not move, and the Keccak predicate's zero test escapes at one value at most
(`M3Instance.card_auxStage_push_le`). -/
theorem inv_sound (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit) (j : ℕ) (c : Vector E j)
    (hj : j < I.τmax) (hne : ¬ inv I ctx j c) :
    Nat.card {x // inv I ctx (j + 1) (c.push x)} ≤ 3 := by
  by_cases hr : sideRest I ctx
  · have ha : ¬ I.auxStage c.toList (theStack ctx.1.2) := fun ha ↦ hne ⟨hr, ha⟩
    refine le_trans ?_ ((I.card_auxStage_push_le (theStack ctx.1.2)
      (by simpa using hj) ha).trans (by norm_num))
    have := Fintype.ofFinite E
    exact Nat.card_mono (Set.toFinite _) fun x hx ↦ by
      have h2 := hx.2
      rwa [Vector.toList_push] at h2
  · have : IsEmpty {x // inv I ctx (j + 1) (c.push x)} := ⟨fun x ↦ hr x.2.1⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The final claims hold of the stack exactly when the values sent are the columns' extensions
at the final point. -/
theorem finalClaims_holds_iff (ctx : SumcheckRound.Ctx (Data I) (TheOracle I) Unit)
    (r : Vector E I.τmax) (v : Vector E I.tableColumns) :
    (∀ c ∈ (finalClaims I r v).toList, c.Holds (theStack ctx.1.2)) ↔
      (tableSummand I).values ctx r = v := by
  have hk : ∀ k : Fin I.tableColumns, (finalClaims I r v)[k].Holds (theStack ctx.1.2) ↔
      ((tableSummand I).values ctx r)[k] = v[k] := fun k ↦ by
    simp only [finalClaims, Fin.getElem_fin, Vector.getElem_ofFn, Sumcheck.Virtual.values,
      tableSummand]
    rw [evalMle_table]
    rfl
  constructor
  · intro h
    apply Vector.ext
    intro k hk'
    exact (hk ⟨k, hk'⟩).mp (h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hk')))
  · rintro hv c hc
    obtain ⟨k, hk', rfl⟩ := Vector.getElem_of_mem (Vector.mem_toList_iff.mp hc)
    exact (hk ⟨k, hk'⟩).mpr (by rw [hv])

/-- The true values at the final point land in the table seam whenever the side condition holds:
the bus phase's claims carried forward hold, and so do the final claims. -/
theorem tableOut_mem_table (s : SumcheckRound.Stmt (Data I) E I.τmax) (o : ∀ i, TheOracle I i)
    (hside : side I ((s.1, o), ())) :
    ((tableOut I s ((tableSummand I).values ((s.1, o), ()) s.2.1.reverse), o), ()) ∈
      Seam.table I := by
  refine ⟨fun c hc ↦ ?_, hside.2.1, I.auxAt_of_aux hside.2.2 _⟩
  simp only [tableOut, Vector.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hside.1 c hc
  · exact (finalClaims_holds_iff I ((s.1, o), ()) _ _).mpr rfl c hc

/-! ## The phase -/

/-- From the bus seam, the combined claimed values are the combination of the true ones at every
challenge, and the side condition holds. -/
theorem batch_complete (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((s, o), w) ∈ Seam.bus I) (ρ : E) :
    ((start I s ρ (powerBatch (claimed I s) ρ), o), w) ∈
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) := by
  cases w
  simp only [Seam.bus, Seam.of, Set.mem_ofPred_eq] at hin
  refine ⟨?_, hin.2.2⟩
  show powerBatch (claimed I s) ρ = Sumcheck.weightedSum _ _ (((s, ρ), o), ())
  rw [sum_tableSummand, (trueValues_eq_claimed_iff I s (theStack o)).mpr ⟨hin.1, hin.2.1⟩]

/-- The batching challenge's hypothesis: the true values, fixed before the challenge, are what a
challenge carrying a statement outside the bus seam into the rounds' input relation makes the
combined claim the combination of, and they differ from the claimed values. -/
theorem xi_batch (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) :
    ∃ a : Fin (I.B + 3) → E, ∀ w ρ, ((s, o), w) ∉ Seam.bus I →
      ((start I s ρ (powerBatch (claimed I s) ρ), o), w) ∈
        Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) →
        a ≠ claimed I s ∧ powerBatch (claimed I s) ρ = powerBatch a ρ :=
  ⟨trueValues I s (theStack o), fun w ρ hin hout ↦ by
    cases w
    obtain ⟨hsum, hside⟩ := hout
    have hsum : powerBatch (claimed I s) ρ = powerBatch (trueValues I s (theStack o)) ρ :=
      hsum.trans (sum_tableSummand I (s, ρ) o)
    refine ⟨fun heq ↦ hin ?_, hsum⟩
    obtain ⟨hzero, htotals⟩ := (trueValues_eq_claimed_iff I s (theStack o)).mp heq
    exact ⟨hzero, htotals, hside⟩⟩

/-- Values whose output is in the table seam are the tables' values at the final point, and the
invariant holds at the challenges. -/
theorem finalValues_reflect (s : SumcheckRound.Stmt (Data I) E I.τmax) (o : ∀ i, TheOracle I i)
    (w : Unit) (v : Vector E I.tableColumns) (h : ((tableOut I s v, o), w) ∈ Seam.table I) :
    (tableSummand I).values ((s.1, o), w) s.2.1.reverse = v ∧ inv I ((s.1, o), w) I.τmax s.2.1 := by
  cases w
  obtain ⟨hcols, hlines, haux⟩ := h
  simp only [tableOut, Vector.toList_append, List.mem_append] at hcols
  refine ⟨(finalClaims_holds_iff I ((s.1, o), ()) _ v).mp fun c hc ↦ hcols c (Or.inr hc),
    ⟨fun c hc ↦ hcols c (Or.inl hc), hlines⟩, ?_⟩
  rw [I.auxStage_full _ (by simp)]
  simpa [tableOut, Vector.toList_reverse] using haux

/-- The rounds' input relation for soundness is the batching challenge's output relation. -/
theorem relIn_inv :
    Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (fun ctx ↦ inv I ctx 0 #v[]) =
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) := by
  congr 1
  funext ctx
  exact propext (inv_zero I ctx)

/-! ## The counts behind the cut securities (lvm, WP-2) -/

open Classical in
/-- **The batching challenge** (the content of the cut `xiSecurity`): from a statement outside
the bus seam, at most `B + 2` challenges `ξ` carry it into the rounds' input relation, since the
true values, fixed before `ξ`, differ from the claimed ones and agree with them after batching
only at a root of a nonzero polynomial of degree at most `B + 2`. -/
theorem card_xi_le (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i)
    (hin : ((s, o), ()) ∉ Seam.bus I) :
    (Finset.univ.filter fun ρ ↦ ((start I s ρ (powerBatch (claimed I s) ρ), o), ()) ∈
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I)).card ≤ I.B + 2 := by
  obtain ⟨a, ha⟩ := xi_batch I s o
  by_cases hex : ∃ ρ, ((start I s ρ (powerBatch (claimed I s) ρ), o), ()) ∈
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I)
  · obtain ⟨ρ₀, hρ₀⟩ := hex
    have hne : ∃ k, claimed I s k ≠ a k := by
      by_contra h
      push Not at h
      exact (ha () ρ₀ hin hρ₀).1 (funext fun k ↦ (h k).symm)
    refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans
      ((card_false_batch_le (claimed I s) a hne).trans (by (clear * -; omega)))
    rw [Finset.mem_filter] at hρ ⊢
    exact ⟨Finset.mem_univ _, (ha () ρ hin hρ.2).2⟩
  · push Not at hex
    refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun ρ _ ↦ hex ρ

/-- **A round of the table sumcheck** (the content of the cut `roundsSecurity`): with the Keccak
predicate carried as the invariant `inv`, a recorded polynomial that passes the check has at most
`3` bad challenges, the round polynomial's agreements with the honest one or the zero test's
escape. -/
theorem card_round_badChallenge_le (hd : I.d ≤ 2) {j : ℕ} (hj : j < I.τmax)
    (p : SumcheckRound.MidStmt (Data I) E j 3) (o : ∀ i, TheOracle I i)
    (hc : SumcheckRound.check j
      (Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I)).weight p.1 p.2 =
        true) :
    Nat.card {x // SumcheckRound.badChallenge j
      (Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I)) p o x} ≤ 3 :=
  SumcheckRound.card_badChallenge_le j _
    (Sumcheck.familyInv_consistent (tableSummand I) Sumcheck.unitWeights nodes
      (tableSummand_degree I hd) nodes_injective (inv I))
    (fun ctx j c hj hne ↦ inv_sound I ctx j c hj hne) hj p o hc

end TableSumcheck

end
end LeanVM.Protocol
end
-- ===== end of `LvmTableSumcheck` =====

-- ===== merged from `LvmFrontTableArk` (GOLF module merge: `LvmFrontTableArk.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableArk.lean` (formal rev 40f877dc) as `LvmFrontTableArk` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.TableArk

  The table sumcheck's components, read off as statements about their relations: the batching
  challenge's escape from the bus seam, the rounds' family, and the final values' hand-over to
  the table seam.
-/

/-! lvm (WP-2): `xi_escape` and `finalValues_keep` are proved from the counts and reflections the
source's typed securities `xiSecurity` and `finalValuesSecurity` were built from (`card_xi_le`,
`Sumcheck.final_reflect_inv`), the statements unchanged. -/

/-!
# The table sumcheck's relations

The table sumcheck phase's security on the typed framework (`tableSumcheckSecurity`,
`LeanVM.Protocol.TableSumcheck`) appends three securities, the first and the last of them public
(`xiSecurity`, `finalValuesSecurity`). This module reads them as doom transitions:

* `xi_escape`: the batching challenge `ξ` escapes doom on the bus seam with probability at most
  `L₀ · (B + 2) / |E|`;
* `tableFamily_sound`: the rounds' family (`Sumcheck.familyInv` of `tableSummand`, with the
  invariant `TableSumcheck.inv`: the side condition, the Keccak predicate along the challenges)
  is sound, a challenge restoring a broken invariant at one value at most;
* `finalValues_keep`: values that pass the final check carry doom on the rounds' last stage to doom
  on the table seam at `tableOut`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

section

variable (I : M3Instance)

/-- The error of the batching challenge over at most `L₀` candidates: `L₀ · (B + 2) / |E|`. -/
noncomputable def xiError (L₀ : ℕ) : ℝ≥0∞ :=
  L₀ * ((((I.B + 3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

open Classical in
/-- **The batching challenge escapes** doom on the bus seam with probability at most
`L₀ · (B + 2) / |E|`. -/
theorem xi_escape {L₀ : ℕ} {C : Set (∀ i, TheOracle I i)} (hfin : C.Finite)
    (hcard : C.ncard ≤ L₀) (s : I.Stmt × BusOut I) (hpre : RelDoom C (Seam.bus I) s) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun ξ ↦ ¬ RelDoom C
      (Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
      (start I s ξ (powerBatch (claimed I s) ξ))).card : ℝ≥0∞) ≤ xiError I L₀ :=
  draw_escape_le (f := fun ξ ↦ start I s ξ (powerBatch (claimed I s) ξ)) hfin hcard
    (fun o ho ↦ by
      have h := card_xi_le I s o ho
      have hc : (Finset.univ.filter fun ξ ↦ ((start I s ξ (powerBatch (claimed I s) ξ), o), ()) ∈
          Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I)).card ≤ I.B + 3 - 1 := by
        convert h using 1; omega
      refine @inv_card_mul_card_le_of_natCard_le _ (fun _ ↦ Classical.propDecidable _) _ ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact hc) hpre

/-- The rounds' family. -/
noncomputable abbrev tableFamily : SumcheckRound.Family E (Data I) (TheOracle I) Unit 3 :=
  Sumcheck.familyInv (tableSummand I) Sumcheck.unitWeights nodes (inv I)

/-- The rounds' family is consistent (the summand has degree at most three in each variable). -/
theorem tableFamily_consistent (hd : I.d ≤ 2) : (tableFamily I).Consistent I.τmax :=
  Sumcheck.familyInv_consistent (tableSummand I) Sumcheck.unitWeights nodes
    (tableSummand_degree I hd) nodes_injective (inv I)

/-- The rounds' family is sound: a challenge restores a broken invariant at one value at most
(`inv_sound`). -/
theorem tableFamily_sound : (tableFamily I).Sound I.τmax :=
  fun ctx j c hj h ↦ inv_sound I ctx j c hj h

/-- The rounds' first stage is the batching challenge's output relation. -/
theorem tableFamily_rel_zero :
    SumcheckRound.rel (tableFamily I) 0 =
      Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) :=
  (Sumcheck.rel_zero_inv (tableSummand I) Sumcheck.unitWeights nodes (inv I)).trans (relIn_inv I)

/-- **The final values keep doom**: values that pass the final check carry doom on the rounds'
last stage to doom on the table seam. -/
theorem finalValues_keep {C : Set (∀ i, TheOracle I i)}
    {s : SumcheckRound.Stmt (Data I) E I.τmax}
    (hpre : RelDoom C (SumcheckRound.rel (tableFamily I) I.τmax) s) (v : Vector E I.tableColumns)
    (hc : Sumcheck.finalCheck (tableSummand I) s v = true) :
    RelDoom C (Seam.table I) (tableOut I s v) :=
  say_keep (fun o hout ↦ by
    exact Sumcheck.final_reflect_inv (tableSummand I) Sumcheck.unitWeights nodes (inv I)
      (tableOut I) (fun s o w v h ↦ finalValues_reflect I s o w v h) s o () v hc hout) hpre

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontTableArk` =====

-- ===== merged from `LvmFrontTableTerms` (GOLF module merge: `LvmFrontTableTerms.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableTerms.lean` (formal rev 40f877dc) as `LvmFrontTableTerms` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.TableTerms

  The final loop of the verifier program's table sumcheck (`table_sumcheck`'s per-table reads) as
  reads followed by a pure computation, specified on any property the reads keep.
-/

/-! lvm (WP-2): over a table list `tables` (`refTableTerms`, `tableTermsSpec` take it; the
source's are at leanISA's `tables`), with `tableTermsClaims` from `LvmBTableClaims`. -/

/-!
# The table sumcheck's final values

`tableTerms` (`crates/verifier/src/bus.rs:239-257`) reads each table's row evaluations, in table
order, and accumulates the final check's value and the column claims. `refTableTerms` is the same
computation on the evaluations read, a pure function; `tableTermsSpec` says the loop reads them (one
list per table, of the table's width) and returns `refTableTerms` of them, keeping any property of
the history that reads keep.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open scoped ENNReal

section

/-- The per-table loop of `table_sumcheck` on the evaluations read, one list per table. -/
def refTableTerms (tables : List Table) (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → List (List E) → ℕ → E → List Verifier.ColumnClaim →
      E × List Verifier.ColumnClaim
  | [], _, _, final, claims => (final, claims)
  | _ :: _, [], _, final, claims => (final, claims)
  | (table, height, forms, weight) :: rest, evaluations :: evs, cursor, final, claims =>
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let claims := claims ++ evaluations.zipIdx.map fun (value, column) ↦
      ⟨(globalColumnBases tables).getD table.opcode 0 + column, point.take height, value⟩
    refTableTerms tables constraintPowers formPowers point rest evs (cursor + table.nConstraints) final
      claims

/-- The lead of the loop: the follower's with no table, `0` otherwise (it starts with a read). -/
def rowsLead : List (Table × ℕ × List Form × E) → ℝ≥0∞ → ℝ≥0∞
  | [], T => T
  | _ :: _, _ => 0

theorem rowsLead_le (rows : List (Table × ℕ × List Form × E)) (T : ℝ≥0∞) : rowsLead rows T ≤ T := by
  cases rows <;> simp [rowsLead]

/-- What the loop read: one list per table, of the table's width. -/
def ReadShape (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) : Prop :=
  List.Forall₂ (fun r ev ↦ ev.length = r.1.width) rows evs

variable {εmax : ℝ≥0∞}

/-- **The final values' loop**: it reads one list per table, of the table's width (each positive),
and returns `refTableTerms` of them, keeping `P`. -/
noncomputable def tableTermsSpec (tables : List Table) {T : ℝ≥0∞} (hT : T ≤ εmax)
    (P : List Ev → Prop)
    (hP : ∀ h x, P h → P (h ++ [Ev.read x])) (cps fps point : List E) :
    (rows : List (Table × ℕ × List Form × E)) → (∀ r ∈ rows, 0 < r.1.width) →
      (cursor : ℕ) → (final : E) → (claims : List Verifier.ColumnClaim) →
      Spec (tableTermsClaims tables cps fps point rows cursor final claims) P
        (fun r h ↦ ∃ evs, ReadShape rows evs ∧
          r = refTableTerms tables cps fps point rows evs cursor final claims ∧ P h) εmax
        (rowsLead rows T) T
  | [], _, cursor, final, claims =>
    (Spec.ret (Post := fun r h ↦ ∃ evs, ReadShape [] evs ∧
      r = refTableTerms tables cps fps point [] evs cursor final claims ∧ P h) (final, claims)).mono
      (fun _ hp ↦ ⟨[], List.Forall₂.nil, rfl, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | (table, height, forms, weight) :: rest, hw, cursor, final, claims =>
    have hw0 : 0 < table.width := hw _ List.mem_cons_self
    Spec.congr (show (do
        let evaluations ← VerifierProgram.readScalars (table.width - 1 + 1)
        tableTermsClaims tables cps fps point rest (cursor + table.nConstraints)
          (final + weight * (dot ((cps.drop cursor).take table.nConstraints)
            (table.constraints evaluations) +
            dot fps (forms.map (·.evaluate (evaluations.getD · 0)))))
          (claims ++ evaluations.zipIdx.map fun (value, column) ↦
            ⟨(globalColumnBases tables).getD table.opcode 0 + column, point.take height, value⟩)) =
        tableTermsClaims tables cps fps point ((table, height, forms, weight) :: rest) cursor final claims by
      rw [Nat.sub_add_cancel hw0]
      rfl)
      ((readNSuccSpec P hP (le_trans (rowsLead_le rest T) hT) (table.width - 1)).bind'
        fun evaluations ↦
        (tableTermsSpec tables hT (fun h ↦ evaluations.length = table.width - 1 + 1 ∧ P h)
          (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) cps fps point rest
          (fun r hr ↦ hw r (List.mem_cons_of_mem _ hr)) _ _ _).mono (fun _ hp ↦ hp)
          (fun r h ⟨evs, hs, hr, hl, hp⟩ ↦ ⟨evaluations :: evs,
            List.Forall₂.cons (by dsimp only; rw [hl]; omega) hs, hr, hp⟩) le_rfl le_rfl le_rfl)

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontTableTerms` =====

-- ===== merged from `LvmFrontTablePhase` (GOLF module merge: `LvmFrontTablePhase.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TablePhase.lean` (formal rev 40f877dc) as `LvmFrontTablePhase` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.TablePhase

  The verifier program's table sumcheck specified on the oracle protocol's relations: from the bus
  seam at what the bus phase read to the table seam at the protocol's output, given the algebraic
  identities between the program's computations and the protocol's verdicts.
-/

/-! lvm (WP-2): over a table list `tables` (the source's are at leanISA's `tables`): `nCons`,
`cpsOf`, `fpsOf`, `rowsOf`, `TableFid`, `TableSumcheckPost`, `tableSumcheckSpec`, `tablePhaseSpec`
take it, and the last two the hypothesis `htw : ∀ t ∈ tables, 0 < t.width` (leanISA's
`tables_width_pos`, decided there, is not a fact of an arbitrary list). -/

/-!
# The table sumcheck on doom

`tablePhase layout bus` (`crates/verifier/src/lib.rs:242-266` and `bus.rs:218-259`) is the oracle
protocol's `tableSumcheck` (`LeanVM.Protocol.TableSumcheck`) on the wire: the batching challenge
`ξ`, the plain sumcheck of four coefficients per round (one left out on the wire), the evaluations
of every table's columns, and the final check. Its doom is stated on the protocol's relations at the
protocol's statement `(input, busOut …)` of what the bus phase read (`BusWit`):

* `ξ`: from the bus seam to the sumcheck's input relation, charged `L₀ · (B + 2) / |E|`
  (`xi_escape`);
* the rounds: `wireSumcheckSpec` on the protocol's family, each charged `L₀ · 3 / |E|`;
* the evaluations and the check: the protocol's last message and its check (`finalValues_keep`),
  to the table seam at `tableOut`.

The program computes the target, the final check's value and the claims its own way. The four
identities that make them the protocol's are `TableFid` (the number of rounds is `τ_max`; the
target is the protocol's batched claim; the final check's value is the protocol's formula; every
claim of the protocol's output is among the program's, through a column numbering `colOf`); they
are statements about the instance and the layout only, discharged for leanISA separately.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

section

/-! ## The program's quantities -/

variable (tables : List Table)

/-- The number of constraints, `Σ n_constraints`. -/
def nCons : ℕ := (tables.map Table.nConstraints).sum

/-- The constraint powers of `ξ`. -/
def cpsOf (ξ : E) : List E := (powers ξ (nCons tables + 3)).take (nCons tables)

/-- The form powers of `ξ`. -/
def fpsOf (ξ : E) : List E := (powers ξ (nCons tables + 3)).drop (nCons tables)

/-- The rows of the final loop at the point `point` (the challenges reversed). -/
def rowsOf (layout : Verifier.Layout) (bus : BusResult) (point : List E) :
    List (Table × ℕ × List Form × E) :=
  List.zip tables (List.zip layout.tableLogHeights
    (List.zip bus.forms (Verifier.tableWeights layout.tableLogHeights bus.point point)))

/-- Every row of the final loop is of a table of positive width, when every table is (lvm: the
source's `tables_width_pos`, a fact of leanISA's tables, is this hypothesis). -/
theorem rowsOf_width_pos (htw : ∀ t ∈ tables, 0 < t.width) (layout : Verifier.Layout)
    (bus : BusResult) (point : List E) :
    ∀ r ∈ rowsOf tables layout bus point, 0 < r.1.width := fun _ hr ↦
  htw _ (List.of_mem_zip hr).1

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout)

/-- The protocol's statement after the bus phase, on what it read. -/
noncomputable def busStmt (w : BusWit) : I.Stmt × BusOut I := (input, Bus.busOut hI (w.layer I input) (w.vals I))

/-- The sumcheck's statement after its rounds. -/
noncomputable def tableStmt (w : BusWit) (ξ : E) (ch : List E) (claim : E) :
    SumcheckRound.Stmt (Data I) E I.τmax :=
  ((busStmt I hI input w, ξ), (vecOf I.τmax ch, claim))

/-- **The program's computations are the protocol's**: the identities between the table phase's
target, final check and claims and the protocol's batched claim, formula and output claims, at
what the bus phase read. `colOf` numbers the protocol's columns as the program does. -/
structure TableFid (colOf : I.ColumnId → ℕ) (w : BusWit) : Prop where
  /-- The rounds: `max` of the heights is `τ_max`. -/
  rounds : layout.tableLogHeights.foldl max 0 = I.τmax
  /-- The target is the protocol's batched claim. -/
  target : ∀ ξ, dot (fpsOf tables ξ) (w.result tables layout).totals =
    powerBatch (claimed I (busStmt I hI input w)) ξ
  /-- The final check's value is the protocol's formula. -/
  formula : ∀ ξ (ch : List E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout (w.result tables layout) ch.reverse) evs →
    (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse (rowsOf tables layout (w.result tables layout) ch.reverse) evs
      0 0 []).1 = formula I (busStmt I hI input w, ξ) (vecOf I.τmax ch).reverse
        (vecOf I.tableColumns evs.flatten)
  /-- The protocol's output claims are among the program's. -/
  claims : ∀ ξ (ch : List E) (claim : E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout (w.result tables layout) ch.reverse) evs →
    ∀ c ∈ (tableOut I (tableStmt I hI input w ξ ch claim)
      (vecOf I.tableColumns evs.flatten)).2.columns.toList,
      (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        (w.result tables layout).claims ++ (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
          (rowsOf tables layout (w.result tables layout) ch.reverse) evs 0 0 []).2

/-- **The table seam on the wire**: the protocol's output at what was read is doomed, its input
statement is `input`, its claims are among the program's, and it is the table sumcheck's output
(`tableOut`) at some final statement and values: its claims are the bus phase's and one per column
of every sumcheck table at the point's low coordinates. -/
def TablePost (colOf : I.ColumnId → ℕ) (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ (W : Word) (tout : I.Stmt × TableOut I), firstWord h = some W ∧
    RelDoom (cands W) (Seam.table I) tout ∧ tout.1 = input ∧
    (∀ c ∈ tout.2.columns.toList, (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      claims) ∧
    ∃ (st : SumcheckRound.Stmt (Data I) E I.τmax) (v : Vector E I.tableColumns),
      tout = tableOut I st v

variable {εmax : ℝ≥0∞}

/-- What the table sumcheck's rounds and final values give: the evaluations read, the claims
the program makes of them, and the table seam's doom at the protocol's output. -/
def TableSumcheckPost (w : BusWit) (ξ : E) (claims' : List Verifier.ColumnClaim) (h : List Ev) :
    Prop :=
  ∃ ch claim evs, ReadShape (rowsOf tables layout (w.result tables layout) ch.reverse) evs ∧
    ch.length = I.τmax ∧
    claims' = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
      (rowsOf tables layout (w.result tables layout) ch.reverse) evs 0 0 []).2 ∧
    HDoom cands (Seam.table I) (tableOut I (tableStmt I hI input w ξ ch claim)
      (vecOf I.tableColumns evs.flatten)) h

/-- **The table sumcheck's rounds and final values** (`table_sumcheck`, `bus.rs:218-259`),
from doom on the sumcheck's input relation after `ξ`: the plain sumcheck, each round charged
`L₀ · 3 / |E|`, then the evaluations and the final check. -/
noncomputable def tableSumcheckSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid tables I hI input layout colOf w) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) (ξ : E) :
    Spec (Verifier.tableSumcheckClaims tables layout.tableLogHeights (w.result tables layout).forms (cpsOf tables ξ)
        (fpsOf tables ξ) (w.result tables layout).point (dot (fpsOf tables ξ) (w.result tables layout).totals))
      (HDoom cands (SumcheckRound.rel (tableFamily I) 0)
        ((busStmt I hI input w, ξ), (#v[], dot (fpsOf tables ξ) (w.result tables layout).totals)))
      (TableSumcheckPost tables I hI cands input layout w ξ) εmax
      (sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T) T :=
  let s := busStmt I hI input w
  let bus := w.result tables layout
  let n := layout.tableLogHeights.foldl max 0
  (wireSumcheckSpec (T := T) (tableFamily I) cands (tableFamily_consistent I hd)
    (tableFamily_sound I) hfin hcard (by norm_num) he (s, ξ) (List.replicate n none) 0 #v[]
    (dot (fpsOf tables ξ) bus.totals) (by simp [n, fid.rounds]) (fun k hk ↦ by
      have hk' : k < I.τmax := by simpa [n, fid.rounds] using hk
      simp [tableFamily, Sumcheck.familyInv, Sumcheck.domain, Sumcheck.unitWeights, wireDomain,
        hk'])).bind' fun ⟨ch, claim⟩ ↦
    let P := SumcheckPost (tableFamily I) cands (s, ξ) I.τmax #v[] (ch, claim)
    let rows := rowsOf tables layout bus ch.reverse
    ((tableTermsSpec tables hT P (fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩) (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
      rows (rowsOf_width_pos tables htw layout bus _) 0 0 []).mono (fun _ hp ↦ hp) (fun _ _ hp ↦ hp) le_rfl
      (rowsLead_le _ _) le_rfl).bind' fun ⟨final, claims⟩ ↦
    (Spec.require (c := final = claim) (Post := fun _ h ↦ ∃ evs, ReadShape rows evs ∧
        ch.length = I.τmax ∧
        claims = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse rows evs 0 0 []).2 ∧
        HDoom cands (Seam.table I) (tableOut I (tableStmt I hI input w ξ ch claim)
          (vecOf I.tableColumns evs.flatten)) h)
      (fun _ hp hc ↦ by
        obtain ⟨evs, hs, heq, hlen, W, hW, hR⟩ := hp
        have hl : ch.length = I.τmax := by simpa using hlen
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        simp only at hfst hsnd
        refine ⟨evs, hs, hl, hsnd, W, hW, finalValues_keep I hR _ ?_⟩
        rw [Sumcheck.finalCheck, decide_eq_true_eq]
        show formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten) = claim
        rw [← fid.formula ξ ch evs hl hs, ← hfst, hc])).bind' fun _ ↦
    (Spec.ret (Post := TableSumcheckPost tables I hI cands input layout w ξ) claims).mono
      (fun _ ⟨evs, hs, hl, hc, hD⟩ ↦ ⟨ch, claim, evs, hs, hl, hc, hD⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl

open Classical in
/-- **The table sumcheck** (`tablePhase`, `lib.rs:242-266`, `bus.rs:218-259`) after the bus phase
read `w`: from the bus seam at `w` to the table seam on the wire. `ξ` is charged
`L₀ · (B + 2) / |E|`, each round `L₀ · 3 / |E|`. -/
noncomputable def tablePhaseSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid tables I hI input layout colOf w) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) :
    Spec (tablePhaseClaims tables layout (w.result tables layout)) (BusAt I hI cands input w)
      (TablePost I cands input colOf) εmax
      (xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T)
      T :=
  let s := busStmt I hI input w
  (Spec.sampleE (xiError I L₀) (Post := fun ξ h ↦ HDoom cands
      (SumcheckRound.rel (tableFamily I) 0)
      ((s, ξ), (#v[], dot (fpsOf tables ξ) (w.result tables layout).totals)) h)
    (fun h₀ hp ↦ by
      obtain ⟨-, -, -, W, hW, hR⟩ := hp
      refine le_trans ?_ (xi_escape I (hfin W) (hcard W) s hR)
      gcongr with ξ _
      intro hD
      refine ⟨W, firstWord_append hW _, ?_⟩
      rw [fid.target ξ, tableFamily_rel_zero]
      exact hD)).bind' fun ξ ↦
  (tableSumcheckSpec tables I hI cands input layout colOf w fid htw hd hfin hcard he hT ξ).bind'
    fun tableClaims ↦
  (Spec.ret (Post := TablePost I cands input colOf) ((w.result tables layout).claims ++ tableClaims)).mono
    (fun _ hp ↦ by
      obtain ⟨ch, claim, evs, hs, hl, rfl, W, hW, hR⟩ := hp
      exact ⟨W, _, hW, hR, rfl, fid.claims ξ ch claim evs hl hs, _, _, rfl⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl
    le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontTablePhase` =====

-- ===== merged from `LvmFrontBusTable` (GOLF module merge: `LvmFrontBusTable.lean` is now a stub importing `LvmM3Fid`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusTable.lean` (formal rev 40f877dc) as `LvmFrontBusTable` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.BusTable

  The bus phase followed by the table sumcheck, specified from the commitment's doom to the table
  seam on the wire, and the commitment's doom as the bus phase's.
-/

/-! lvm (WP-2): over a table list `tables` with `htw : ∀ t ∈ tables, 0 < t.width` (see
`LvmFrontTablePhase`). Cut: the section `LeanIsa` (`candsOf`, `candsL`, `candsL_mem`,
`candsOf_ncard`, `exists_pushBlock`, `rows_of_mem_pushBlocks`, `verifierLayout_injective`,
`commitDoom_hdoom`): the commitment's doom at the leanISA instance and layout (`leanIsaInstance`,
`verifierLayout`, `Complete.BusLayout`, `EndToEnd.Candidates`), a leanISA seam; an instantiation
supplies its own `HDoom cands (Seam.commit I) input` at the bus phase's start. -/

/-!
# The bus phase and the table sumcheck

`busTableSpec` composes `busThenSpec` with `tablePhaseSpec` for the program's
`do let bus ← verifyBusBalance computedBytecodeValue layout; tablePhase layout bus`, from the commitment's doom
(`Seam.commit` on the candidates) to the table seam on the wire (`TablePost`). It needs the table phase's
identities (`TableFid`) for every read of the right shape.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

section

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (tables : List Table) (layout : Verifier.Layout) {εmax : ℝ≥0∞}

/-- What a read of the bus phase of the right shape is. -/
def BusWit.Shaped (w : BusWit) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 3

instance (w : BusWit) : Decidable (w.Shaped I) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The bus phase, then the table sumcheck**: from the commitment's doom to the table seam on
the wire. -/
noncomputable def busTableSpec (colOf : I.ColumnId → ℕ)
    (fid : ∀ w : BusWit, w.Shaped I → TableFid tables I hI input layout colOf w)
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec ((verifyBusBalance tables computedBytecodeValue layout).bind (tablePhaseClaims tables layout))
      (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  busThenSpec I hI cands input tables layout hxi
    (fun w ↦ if hw : w.Shaped I then
      tablePhaseSpec tables I hI cands input layout colOf w (fid w hw) htw hd hfin hcard he3 hTf
    else specOfFalse fun _ hp ↦ hw ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    hfin hcard hμ hdepth hab he4 hT hlam

end
end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmFrontBusTable` =====

-- ===== merged from `LvmM3Phase` (GOLF module merge: `LvmM3Phase.lean` is now a stub importing `LvmM3Fid`) =====
section
-- adapted from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusPhase.lean` (WP-2's port
-- `LvmFrontBusPhase`, formal rev 40f877dc): `busTailSpec`/`busThenSpec` for an instance with no boundary
-- block (no framework fingerprint, no boundary value read); and from `.../Front/TablePhase.lean`
-- (`LvmFrontTablePhase`): `TableFid`, `tableSumcheckSpec`, `tablePhaseSpec`, generalised from leanISA's
-- `BusWit` result to any bus result and statement (`TableFidG`, `tableSumcheckSpecG`, `tablePhaseSpecG`);
-- new for lvm (WP-9): `Bus.Conditions` of the lvm instance, `lvmBusTableSpec`.

/-!
# The bus phase of the lvm instance

**Side conditions** (`inst_conditions`): the lvm instance satisfies leanVM's `Bus.Conditions`
when every constrained table reads or seeds (so it has a push flush, of its own height): each
table pushes and pulls the same number of flushes (a read's push and pull, a seed and its
finalize), so the pull side has the push side's leaves, and the count side (one block per read)
has at most that many.

**The phase on the wire** (`lvmBusProg`): leanVM's `verify_bus_balance` without its framework
blocks: the fingerprint challenges `(α, β)` (`abProg`), the grand-product GKR at the push side's
depth `μ_bus` (`verifyGkrGrandProducts`), the count root nonzero. The instance has no boundary
block, so the bus phase reads no boundary value (`busClaims = 0`): the leaf decomposition is pure.
**`lvmBusSpec`**: from the commitment's doom (`Seam.commit`, no candidate satisfies `M3Holds`) to
doom on the bus seam at the protocol's output on what was read (`Bus.busOut`), with leanVM's
errors: `abError L₀ = L₀·4·2^{μ_bus}/|E|` for `(α, β)`, `roundError L₀ 4` per GKR round,
`lambdaError L₀` per combiner.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-! ## Side conditions -/

section Conditions

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

theorem flushes_push_length (t : Tab) :
    (t.flushes.filter fun f ↦ decide (f.1 = Side.push)).length = t.reads.length + t.seeds.length := by
  simp [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def]

theorem flushes_pull_length (t : Tab) :
    (t.flushes.filter fun f ↦ decide (f.1 = Side.pull)).length = t.reads.length + t.seeds.length := by
  simp [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def]

theorem counts_length_le (t : Tab) : t.counts.length ≤ t.reads.length + t.seeds.length := by
  unfold Tab.counts
  exact (List.length_filterMap_le _ _).trans (Nat.le_add_right _ _)

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem two_pow_comp {I : M3Instance} :
    (fun src : Bus.Source I ↦ 2 ^ src.κ) = (fun n ↦ 2 ^ n) ∘ Bus.Source.κ := rfl

/-- A side's leaves, table by table. -/
theorem leafCount_side (k : Fin 3) (s : Side) (hk : Bus.sources (inst L tabs hτ) k = Bus.sideSources (inst L tabs hτ) s) :
    Bus.leafCount (inst L tabs hτ) k = ((List.finRange tabs.length).map fun j ↦
      (((inst L tabs hτ).flushes j).filter fun f ↦ decide (f.1 = s)).length * 2 ^ (tabs.get j).τ).sum := by
  have h := Bus.sideSources_map_κ (inst L tabs hτ) s
  have hb : (inst L tabs hτ).boundary = [] := rfl
  rw [hb] at h
  simp only [List.filter_nil, List.map_nil, List.nil_append] at h
  rw [Bus.leafCount, hk, two_pow_comp, ← List.map_map, h, List.map_flatMap, sum_flatMap']
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem leafCount_push_eq :
    Bus.leafCount (inst L tabs hτ) 0 = ((List.finRange tabs.length).map fun j ↦
      ((tabs.get j).reads.length + (tabs.get j).seeds.length) * 2 ^ (tabs.get j).τ).sum := by
  rw [leafCount_side L tabs hτ 0 .push rfl]
  exact congrArg List.sum (List.map_congr_left fun j _ ↦ by rw [← flushes_push_length])

theorem leafCount_pull_eq :
    Bus.leafCount (inst L tabs hτ) 1 = Bus.leafCount (inst L tabs hτ) 0 := by
  rw [leafCount_side L tabs hτ 1 .pull rfl, leafCount_push_eq]
  exact congrArg List.sum (List.map_congr_left fun j _ ↦ by rw [← flushes_pull_length])

theorem leafCount_count_le :
    Bus.leafCount (inst L tabs hτ) 2 ≤ Bus.leafCount (inst L tabs hτ) 0 := by
  have h := Bus.countSources_map_κ (inst L tabs hτ)
  rw [leafCount_push_eq, Bus.leafCount]
  change ((Bus.countSources (inst L tabs hτ)).map _).sum ≤ _
  rw [two_pow_comp, ← List.map_map, h, List.map_flatMap, sum_flatMap']
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  exact List.sum_le_sum fun j _ ↦ Nat.mul_le_mul_right _ (counts_length_le _)

theorem leafCount_push_le :
    Bus.leafCount (inst L tabs hτ) 0 ≤ 2 ^ (inst L tabs hτ).μBus := by
  rw [← Bus.blocks_total]; exact Bus.push_fits _

/-- **The lvm instance meets leanVM's bus side conditions** when every constrained table reads or
seeds. -/
theorem inst_conditions (hcon : ∀ t ∈ tabs, t.cons ≠ [] → t.reads ≠ [] ∨ t.seeds ≠ []) :
    Bus.Conditions (inst L tabs hτ) where
  one_le_d := by show 1 ≤ 2; norm_num
  constrained j hj := by
    have hc : (tabs.get j).cons ≠ [] := by
      intro h; apply hj; show List.map _ (tabs.get j).cons = []; rw [h]; rfl
    have hpos : 1 ≤ (tabs.get j).reads.length + (tabs.get j).seeds.length := by
      rcases hcon _ (List.get_mem _ _) hc with h | h
      · have := List.length_pos_of_ne_nil h; omega
      · have := List.length_pos_of_ne_nil h; omega
    have h1 : 2 ^ (tabs.get j).τ ≤ Bus.leafCount (inst L tabs hτ) 0 := by
      rw [leafCount_push_eq]
      refine le_trans ?_ (List.le_sum_of_mem (List.mem_map_of_mem (List.mem_finRange j)))
      exact Nat.le_mul_of_pos_left _ hpos
    have h2 := h1.trans (leafCount_push_le L tabs hτ)
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp h2
  pull_fits := (leafCount_pull_eq L tabs hτ).trans_le (leafCount_push_le L tabs hτ)
  count_fits := (leafCount_count_le L tabs hτ).trans (leafCount_push_le L tabs hτ)
  separator j f r r' := by
    have key : ∀ e ∈ (tabs.get j).flushes, ∃ c : K, e.2[0] = MvPolynomial.C c := by
      intro e he
      simp only [Tab.flushes, List.mem_append, List.mem_map] at he
      rcases he with (((⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩) <;>
        exact ⟨FK.toBF64 x.1.sep, by simp [Tab.readVec, Tab.bumpVec, Tab.seedVec, Tab.finVec, Key.vec]⟩
    obtain ⟨c, hc⟩ := key ((tabs.get j).flushes[f.1]'f.isLt) (List.getElem_mem _)
    simp only [Bus.flushPolys, Fin.getElem_fin]
    rw [hc]
    simp

/-- The lvm instance has no boundary column: the bus phase reads no value. -/
theorem busClaims_zero : (inst L tabs hτ).busClaims = 0 := by
  simp [M3Instance.busClaims, M3Instance.boundaryColumns, inst]

end Conditions

/-! ## The bus phase on the wire -/

/-- What the lvm bus phase read: the fingerprint challenges, the GKR point and values. -/
structure LBus where
  /-- The four `α`. -/
  alphas : List E
  /-- `β`. -/
  beta : E
  /-- The grand product's point. -/
  point : List E
  /-- The three trees' values there. -/
  values : List E

/-- **The lvm bus phase**: `(α, β)`, the grand product at depth `μ`, the count root nonzero, then one
prover scalar that must be zero. The instance has no boundary value to read; this scalar stands
where leanVM reads them, so that the grand product's last challenges and the table sumcheck's `ξ`
are separated by a prover move as in leanVM (the lead calculus of `gkrSpec` ends at allowance `0`).
Cost: one `E` scalar. -/
def lvmBusProg (μ : ℕ) : VerifierProgram LBus :=
  abProg.bind fun ab ↦ (verifyGkrGrandProducts μ).bind fun r ↦
    (VerifierProgram.require (r.1 ≠ 0)).bind fun _ ↦ VerifierProgram.readScalar.bind fun z ↦
      (VerifierProgram.require (z = 0)).bind fun _ ↦ VerifierProgram.ret ⟨ab.1, ab.2, r.2.1, r.2.2⟩

section Bus

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt)

/-- The protocol's statement after the bus phase, on what was read (no boundary value). -/
noncomputable def lbusStmt (b : LBus) (vals : Vector E I.busClaims) : I.Stmt × BusOut I :=
  (input, Bus.busOut hI (layerStmtOf (input, (toAlpha b.alphas, b.beta)) I.μBus ⟨b.values, b.point⟩)
    vals)

/-- **The bus seam on the wire**: the protocol's output at what was read is doomed. -/
def LBusAt (vals : Vector E I.busClaims) (b : LBus) (h : List Ev) : Prop :=
  b.point.length = I.μBus ∧ b.values.length = 3 ∧ HDoom cands (Seam.bus I) (lbusStmt I hI input b vals) h

variable {εmax : ℝ≥0∞}

/-- **The lvm bus phase, specified** (leanVM's `busThenSpec` without the framework blocks): from
the commitment's doom to doom on the bus seam at the protocol's output on what was read; `Lk` is the
follower's lead. -/
noncomputable def lvmBusSpec (vals : Vector E I.busClaims) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {Lk : ℝ≥0∞} (hLk : Lk ≤ εmax) :
    Spec (lvmBusProg I.μBus) (HDoom cands (Seam.commit I) input) (LBusAt I hI cands input vals) εmax
      (abError I L₀ + 0) Lk :=
  (abSpec I cands input hI hfin hcard hab (T := 0)).bind' fun ab ↦
    (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam).bind' fun r ↦
      let P : List Ev → Prop := fun h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
          HDoom cands (Seam.bus I) (lbusStmt I hI input ⟨ab.1, ab.2, r.2.1, r.2.2⟩ vals) h
      (Spec.require (T := 0) (Post := fun _ h ↦ P h)
        fun _ hp hc ↦ by
          obtain ⟨hl, hv, W, hW, hR⟩ := hp.resolve_left hc
          exact ⟨hl, hv, W, hW, values_keep I hI hR vals⟩).bind' fun _ ↦
      (Spec.readE (Post := fun _ h ↦ P h)
        (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩) hLk).bind' fun _ ↦
      (Spec.require (Post := fun _ h ↦ P h) fun _ hp _ ↦ hp).bind' fun _ ↦
      (Spec.ret (Post := LBusAt I hI cands input vals) _).mono (fun _ hp ↦ hp)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Bus

/-! ## The table phase over any bus result (leanVM `TablePhase`, generalised) -/

section Table

open LeanVM.Protocol.TableSumcheck

variable (tables : List Verifier.Table) (I : M3Instance) (hI : Bus.Conditions I)
  (cands : Word → Set (∀ i, TheOracle I i)) (layout : Verifier.Layout)

/-- The sumcheck's statement after its rounds, at the bus statement `s`. -/
noncomputable def tableStmtG (s : I.Stmt × BusOut I) (ξ : E) (ch : List E) (claim : E) :
    SumcheckRound.Stmt (Data I) E I.τmax :=
  ((s, ξ), (vecOf I.τmax ch, claim))

/-- **The program's computations are the protocol's** (leanVM `TableFid`, at any bus result `bus`
and protocol statement `s`). -/
structure TableFidG (colOf : I.ColumnId → ℕ) (s : I.Stmt × BusOut I) (bus : BusResult) : Prop where
  /-- The rounds: `max` of the heights is `τ_max`. -/
  rounds : layout.tableLogHeights.foldl max 0 = I.τmax
  /-- The target is the protocol's batched claim. -/
  target : ∀ ξ, dot (fpsOf tables ξ) bus.totals = powerBatch (claimed I s) ξ
  /-- The final check's value is the protocol's formula. -/
  formula : ∀ ξ (ch : List E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout bus ch.reverse) evs →
    (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse (rowsOf tables layout bus ch.reverse)
      evs 0 0 []).1 = formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten)
  /-- The protocol's output claims are among the program's. -/
  claims : ∀ ξ (ch : List E) (claim : E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout bus ch.reverse) evs →
    ∀ c ∈ (tableOut I (tableStmtG I s ξ ch claim) (vecOf I.tableColumns evs.flatten)).2.columns.toList,
      (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        bus.claims ++ (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
          (rowsOf tables layout bus ch.reverse) evs 0 0 []).2

variable {εmax : ℝ≥0∞}

/-- What the rounds and final values give (leanVM `TableSumcheckPost`, generalised). -/
def TableSumcheckPostG (s : I.Stmt × BusOut I) (bus : BusResult) (ξ : E)
    (claims' : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ ch claim evs, ReadShape (rowsOf tables layout bus ch.reverse) evs ∧ ch.length = I.τmax ∧
    claims' = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
      (rowsOf tables layout bus ch.reverse) evs 0 0 []).2 ∧
    HDoom cands (Seam.table I) (tableOut I (tableStmtG I s ξ ch claim)
      (vecOf I.tableColumns evs.flatten)) h

/-- **The table sumcheck's rounds and final values** (leanVM `tableSumcheckSpec`, generalised). -/
noncomputable def tableSumcheckSpecG (colOf : I.ColumnId → ℕ) (s : I.Stmt × BusOut I)
    (bus : BusResult) (fid : TableFidG tables I layout colOf s bus)
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) (ξ : E) :
    Spec (Verifier.tableSumcheckClaims tables layout.tableLogHeights bus.forms (cpsOf tables ξ)
        (fpsOf tables ξ) bus.point (dot (fpsOf tables ξ) bus.totals))
      (HDoom cands (SumcheckRound.rel (tableFamily I) 0)
        ((s, ξ), (#v[], dot (fpsOf tables ξ) bus.totals)))
      (TableSumcheckPostG tables I cands layout s bus ξ) εmax
      (sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T) T :=
  let n := layout.tableLogHeights.foldl max 0
  (wireSumcheckSpec (T := T) (tableFamily I) cands (tableFamily_consistent I hd)
    (tableFamily_sound I) hfin hcard (by norm_num) he (s, ξ) (List.replicate n none) 0 #v[]
    (dot (fpsOf tables ξ) bus.totals) (by simp [n, fid.rounds]) (fun k hk ↦ by
      have hk' : k < I.τmax := by simpa [n, fid.rounds] using hk
      simp [tableFamily, Sumcheck.familyInv, Sumcheck.domain, Sumcheck.unitWeights, wireDomain,
        hk'])).bind' fun ⟨ch, claim⟩ ↦
    let P := SumcheckPost (tableFamily I) cands (s, ξ) I.τmax #v[] (ch, claim)
    let rows := rowsOf tables layout bus ch.reverse
    ((tableTermsSpec tables hT P (fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩) (cpsOf tables ξ) (fpsOf tables ξ)
      ch.reverse rows (rowsOf_width_pos tables htw layout bus _) 0 0 []).mono (fun _ hp ↦ hp)
      (fun _ _ hp ↦ hp) le_rfl (rowsLead_le _ _) le_rfl).bind' fun ⟨final, claims⟩ ↦
    (Spec.require (c := final = claim) (Post := fun _ h ↦ ∃ evs, ReadShape rows evs ∧
        ch.length = I.τmax ∧
        claims = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse rows evs 0 0 []).2 ∧
        HDoom cands (Seam.table I) (tableOut I (tableStmtG I s ξ ch claim)
          (vecOf I.tableColumns evs.flatten)) h)
      (fun _ hp hc ↦ by
        obtain ⟨evs, hs, heq, hlen, W, hW, hR⟩ := hp
        have hl : ch.length = I.τmax := by simpa using hlen
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        simp only at hfst hsnd
        refine ⟨evs, hs, hl, hsnd, W, hW, finalValues_keep I hR _ ?_⟩
        rw [Sumcheck.finalCheck, decide_eq_true_eq]
        show formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten) = claim
        rw [← fid.formula ξ ch evs hl hs, ← hfst, hc])).bind' fun _ ↦
    (Spec.ret (Post := TableSumcheckPostG tables I cands layout s bus ξ) claims).mono
      (fun _ ⟨evs, hs, hl, hc, hD⟩ ↦ ⟨ch, claim, evs, hs, hl, hc, hD⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl

open Classical in
/-- **The table sumcheck** (leanVM `tablePhaseSpec`, generalised): from doom on the bus seam at `s`
to the table seam on the wire. `ξ` is charged `L₀ · (B + 2) / |E|`, each round `L₀ · 3 / |E|`. -/
noncomputable def tablePhaseSpecG (colOf : I.ColumnId → ℕ) (s : I.Stmt × BusOut I) (bus : BusResult)
    (fid : TableFidG tables I layout colOf s bus) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) :
    Spec (tablePhaseClaims tables layout bus) (HDoom cands (Seam.bus I) s)
      (TablePost I cands s.1 colOf) εmax
      (xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T)
      T :=
  (Spec.sampleE (xiError I L₀) (Post := fun ξ h ↦ HDoom cands
      (SumcheckRound.rel (tableFamily I) 0)
      ((s, ξ), (#v[], dot (fpsOf tables ξ) bus.totals)) h)
    (fun h₀ hp ↦ by
      obtain ⟨W, hW, hR⟩ := hp
      refine le_trans ?_ (xi_escape I (hfin W) (hcard W) s hR)
      gcongr with ξ _
      intro hD
      refine ⟨W, firstWord_append hW _, ?_⟩
      rw [fid.target ξ, tableFamily_rel_zero]
      exact hD)).bind' fun ξ ↦
  (tableSumcheckSpecG tables I cands layout colOf s bus fid htw hd hfin hcard he hT ξ).bind'
    fun tableClaims ↦
  (Spec.ret (Post := TablePost I cands s.1 colOf) (bus.claims ++ tableClaims)).mono
    (fun _ hp ↦ by
      obtain ⟨ch, claim, evs, hs, hl, rfl, W, hW, hR⟩ := hp
      exact ⟨W, _, hW, hR, rfl, fid.claims ξ ch claim evs hl hs, _, _, rfl⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl

end Table

/-! ## The bus phase, then the table sumcheck -/

section Compose

variable (tables : List Verifier.Table) (I : M3Instance) (hI : Bus.Conditions I)
  (cands : Word → Set (∀ i, TheOracle I i)) (input : I.Stmt) (layout : Verifier.Layout)
  {εmax : ℝ≥0∞}

/-- **The lvm bus phase, then the table sumcheck**, on the wire: `busRes` computes the bus result
(forms, totals, claims) from what the bus phase read. -/
def lvmBusTableProg (μ : ℕ) (busRes : LBus → BusResult) : VerifierProgram (List Verifier.ColumnClaim) :=
  (lvmBusProg μ).bind fun b ↦ tablePhaseClaims tables layout (busRes b)

/-- **`M3Holds` from the phase specs** (leanVM's `busTableSpec` for the lvm instance): from the
commitment's doom (no candidate satisfies `M3Holds`) to the table seam on the wire, given, for every
read of the right shape, the identities between the program's computations and the protocol's
(`TableFidG`, as leanVM's `busTableSpec` takes `TableFid`). Errors: `abError L₀ + 0` lead (the
fingerprint challenges), `roundError L₀ 4`, `lambdaError L₀` in the grand product, `xiError L₀`
and `roundError L₀ 3` per round in the table sumcheck. -/
noncomputable def lvmBusTableSpec (colOf : I.ColumnId → ℕ) (vals : Vector E I.busClaims)
    (busRes : LBus → BusResult)
    (fid : ∀ b : LBus, b.point.length = I.μBus → b.values.length = 3 →
      TableFidG tables I layout colOf (lbusStmt I hI input b vals) (busRes b))
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0) (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec (lvmBusTableProg tables layout I.μBus busRes) (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  (lvmBusSpec I hI cands input vals hfin hcard hμ hab he4 hT hlam hxi).bind
    (fun b ↦ if hb : b.point.length = I.μBus ∧ b.values.length = 3 then
      (tablePhaseSpecG tables I cands layout colOf (lbusStmt I hI input b vals) (busRes b)
        (fid b hb.1 hb.2) htw hd hfin hcard he3 hTf).mono
        (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ hb ⟨hp.1, hp.2.1⟩)

end Compose

/-! ## The per-group errors (BLUEPRINT §3.2), unique decoding (`L₀ = 1`) -/

section Errors

theorem natDivCard_le {a b : ℕ} (h : a ≤ b) :
    ((((a : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ (((b : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  gcongr

/-- **Bus fingerprint**: `abError ≤ 2^24/|E|` (§3.2's row "bus fingerprint …") when `μ_bus ≤ 22`
(P20: 21; P8: 20). -/
theorem abError_le (I : M3Instance) (hμ : I.μBus ≤ 22) :
    abError I 1 ≤ ((overE (2 ^ 24) : ℝ≥0) : ℝ≥0∞) := by
  unfold abError
  rw [Nat.cast_one, one_mul]
  have : 4 * 2 ^ I.μBus ≤ 2 ^ 24 := by
    calc 4 * 2 ^ I.μBus ≤ 4 * 2 ^ 22 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hμ)
      _ = 2 ^ 24 := by norm_num
  unfold overE
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le this

/-- **Table sumcheck batching**: `xiError ≤ 2^24/|E|` when the tables have at most `2^24 − 2`
constraints. -/
theorem xiError_le (I : M3Instance) (hB : I.B + 2 ≤ 2 ^ 24) :
    xiError I 1 ≤ ((overE (2 ^ 24) : ℝ≥0) : ℝ≥0∞) := by
  unfold xiError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le (by omega)

/-- **Sumcheck rounds** (grand product degree 3 with `4` coefficients, table sumcheck degree 3) and the
grand product's combiners: at most `4/|E|`. -/
theorem roundError_le (d : ℕ) (hd : d ≤ 4) :
    roundError 1 d ≤ ((overE 4 : ℝ≥0) : ℝ≥0∞) := by
  unfold roundError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le hd

theorem lambdaError_le : lambdaError 1 ≤ ((overE 4 : ℝ≥0) : ℝ≥0∞) := by
  unfold lambdaError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le (by norm_num)

end Errors

end Lvm.M3
end
-- ===== end of `LvmM3Phase` =====

/-!
# The lvm table phase's program objects

leanVM's `busTableSpec` (`LvmM3Phase.lvmBusTableSpec`) is stated for a list of verifier tables,
a layout and a bus result computed from what the bus phase read. For the lvm instance
`inst L tabs hτ` they are:

* `vTables tabs`: table `j` has opcode `j`, the table's width in columns, and its constraints
  evaluated at the row's values (`CPoly.evalV`); `vLayout tabs`: only the log-heights;
* `busFinalV tabs` (`busResV` on an `LBus`): the leaf decomposition, as the native
  `busFinalR` computes it (the same lists in the same order, over `E`): each side's blocks in the
  protocol's order (`sideBlocksV`), stacked largest first (`stackBlocksV`), weighted by
  `eq_above` of their placement (`blockWeightV`), bucketed by table (each table's blocks in
  reverse order, as the native fold prepends them); the totals `v + 1 + Σ_b w_b`;
* `colOfL tabs`: the protocol's column `⟨j, i⟩` is global column `6 + Σ_{j' < j} w_{j'} + i`, the
  number the table phase's claims carry (`globalColumnBases`);
* `tableCheckVB tabs claims`: every claim on a fixed column has its closed form's value
  (`fixedEvalV`, the native evaluator through `FE.toExt3`).

`AllSc tabs`: every table reads or seeds (every lvm table does: LoopIR pieces, input arrays,
`BITS`), so every table is a sumcheck table and the native decision's filter is the identity.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier

/-! ## Polynomials over `E` -/

/-- An `FK` coefficient as an element of `E`. -/
def kE (c : FK) : E := ofK (FK.toBF64 c)

/-- The value of a `CPoly` at a row of `E` values (the native `CPoly.evalE` over `E`). -/
def CPoly.evalV (v : ℕ → E) (P : CPoly) : E :=
  (P.map fun m ↦ kE m.1 * (m.2.map v).foldl (· * ·) 1).foldl (· + ·) 0

/-! ## Tables and layout -/

/-- Every table reads or seeds: every table is a sumcheck table. -/
def AllSc (tabs : List Tab) : Prop := ∀ t ∈ tabs, t.reads ≠ [] ∨ t.seeds ≠ []

/-- The verifier table of lvm table `t`, numbered `j`. -/
def vTable (j : ℕ) (t : Tab) : Table where
  opcode := j
  columns := List.replicate t.w ""
  flushes := {}
  constraints ev := t.cons.map (CPoly.evalV fun i ↦ ev.getD i 0)
  padding := []

/-- The verifier tables of the lvm tables, in order. -/
def vTables (tabs : List Tab) : List Table := tabs.zipIdx.map fun (t, j) ↦ vTable j t

@[simp] theorem length_vTables (tabs : List Tab) : (vTables tabs).length = tabs.length := by
  simp [vTables]

/-- The verifier layout: the table phase reads only the log-heights. -/
def vLayout (tabs : List Tab) : Layout where
  logMemory := 0
  logBytecode := 0
  bytecode := []
  push := []
  pull := []
  count := []
  placements := []
  stackLog := 0
  tableLogHeights := tabs.map (·.τ)

/-- **The global column numbering**: column `i` of table `j` is the table phase's claim number
(`globalColumnBases`). -/
noncomputable def colOfL (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) :
    (inst L tabs hτ).ColumnId → ℕ :=
  fun c ↦ (globalColumnBases (vTables tabs)).getD c.1.val 0 + c.2.val

/-- The (empty) boundary values of the lvm instance. -/
noncomputable def vals0 (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) :
    Vector E (inst L tabs hτ).busClaims :=
  Vector.cast (busClaims_zero L tabs hτ).symm #v[]

/-! ## The bus result (the native `busFinalR` over `E`) -/

/-- `w·P` as a form. -/
def cpolyFormV (w : E) (P : CPoly) : Form := ⟨P.map fun m ↦ (m.2, w * kE m.1)⟩

/-- The sum of forms (terms concatenated). -/
def formSumV (fs : List Form) : Form := ⟨fs.flatMap (·.terms)⟩

/-- The leaf form of a message `⟨sep, addr, cnt, val⟩` at unit weight:
`β + Σ_i eq(α, i)·coord_i`. -/
def leafFormV (eqα : List E) (β : E) (k : Key) (cnt : CPoly) : Form :=
  formSumV ([Form.const (β + eqα.getD 0 0 * kE k.sep), cpolyFormV (eqα.getD 1 0) k.addr,
    cpolyFormV (eqα.getD 2 0) cnt] ++ k.val.zipIdx.map fun (P, l) ↦ cpolyFormV (eqα.getD (3 + l) 0) P)

/-- A block of a bus side: its table, its log-height, its form at unit weight. -/
structure VBlock where
  /-- The table. -/
  tab : ℕ
  /-- The log-height. -/
  κ : ℕ
  /-- The form at unit weight. -/
  form : Form

/-- The blocks of the three sides, in the protocol's order (`Bus.sideSources`, `countSources`). -/
def sideBlocksV (tabs : List Tab) (eqα : List E) (β : E) : List (List VBlock) :=
  let ts := tabs.zipIdx
  [ts.flatMap fun (t, j) ↦
      t.reads.map (fun r ↦ ⟨j, t.τ, leafFormV eqα β r.1 [(FK.x, [r.2])]⟩) ++
        t.seeds.map (fun s ↦ ⟨j, t.τ, leafFormV eqα β s.1 (CPoly.const 1)⟩),
   ts.flatMap fun (t, j) ↦
      t.reads.map (fun r ↦ ⟨j, t.τ, leafFormV eqα β r.1 (CPoly.var r.2)⟩) ++
        t.seeds.map (fun s ↦ ⟨j, t.τ, leafFormV eqα β s.1 (CPoly.var s.2)⟩),
   ts.flatMap fun (t, j) ↦ t.counts.map fun c ↦ ⟨j, t.τ, Form.col c.val⟩]

/-- The blocks stacked largest first (stable), with their offsets. -/
def stackBlocksV (bs : List VBlock) : List (VBlock × ℕ) :=
  let sorted := bs.mergeSort fun a b ↦ decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (VBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
    ([], 0)).1

/-- Block weight of a block at offset `off`: `eq_above` of its placement. -/
def blockWeightV (ζ : List E) (κ off : ℕ) : E := ({ variableCount := κ, index := off } : Placement).eqAbove ζ

/-- The sides' blocks with their weights at `ζ`. -/
def sidesV (tabs : List Tab) (alphas : List E) (β : E) (ζ : List E) : List (List (VBlock × E)) :=
  (sideBlocksV tabs (eqKernel alphas) β).map fun bs ↦
    (stackBlocksV bs).map fun (b, off) ↦ (b, blockWeightV ζ b.κ off)

/-- Table `j`'s terms on a side: its blocks' weighted terms, the last block first (the native
fold prepends). -/
def bucketV (s : List (VBlock × E)) (j : ℕ) : List (List ℕ × E) :=
  ((s.filter fun bw ↦ bw.1.tab == j).reverse).flatMap fun bw ↦
    bw.1.form.terms.map fun t ↦ (t.1, bw.2 * t.2)

/-- **The bus leaf decomposition** of the lvm tables over `E`: no framework claim, the GKR point,
each table's three forms, each side's total `v + 1 + Σ_b w_b`. -/
def busFinalV (tabs : List Tab) (alphas : List E) (β : E) (ζ values : List E) : BusResult :=
  let sides := sidesV tabs alphas β ζ
  ⟨[], ζ, (List.range tabs.length).map (fun j ↦ sides.map fun s ↦ (⟨bucketV s j⟩ : Form)),
    (List.range 3).map fun k ↦ values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))⟩

/-- The bus result of what the lvm bus phase read. -/
def busResV (tabs : List Tab) (b : LBus) : BusResult := busFinalV tabs b.alphas b.beta b.point b.values

/-! ## The fixed-column check -/

/-- The table and local column of global column `n` (the first table whose block holds it). -/
def colLoc (tabs : List Tab) (n : ℕ) : Option (ℕ × ℕ) :=
  ((List.range tabs.length).find? fun j ↦
      decide ((globalColumnBases (vTables tabs)).getD j 0 ≤ n ∧
        n < (globalColumnBases (vTables tabs)).getD j 0 + ((tabs[j]?.map (·.w)).getD 0))).map
    fun j ↦ (j, n - (globalColumnBases (vTables tabs)).getD j 0)

/-- The closed form over `E` of global column `n`, if it is a fixed column (the native evaluator
through `FE.toExt3`). -/
def fixedEvalV (tabs : List Tab) (n : ℕ) : Option (List E → E) :=
  (colLoc tabs n).bind fun ji ↦
    match tabs[ji.1]?.bind fun t ↦ t.cols[ji.2]? with
    | some (.fix _ ev) => some fun pt ↦ FE.toExt3 (ev (pt.map FE.ofExt3))
    | _ => none

/-- **The fixed-column check** of the table phase's claims: every claim on a fixed column has the
closed form's value at its point. -/
def tableCheckVB (tabs : List Tab) (claims : List ColumnClaim) : Bool :=
  claims.all fun c ↦ match fixedEvalV tabs c.column with
    | some ev => decide (c.value = ev c.point)
    | none => true

/-- **Every fixed column's closed form is its cells' multilinear extension** (native, at every
point of the table's height). -/
def FixOk (tabs : List Tab) : Prop :=
  ∀ t ∈ tabs, ∀ f ev, ColSrc.fix f ev ∈ t.cols → ∀ r : List FE, r.length = t.τ →
    ev r = Loop.mle r fun x ↦ FE.ofK (f x)

end Lvm.M3
