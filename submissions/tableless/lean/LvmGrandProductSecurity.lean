-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/GrandProductSecurity.lean` (formal rev 40f877dc) as `LvmGrandProductSecurity` for lvm (WP-2).
/-
  LeanVM.Protocol.ToArkLib.GrandProductSecurity

  Round-by-round knowledge soundness of the batched grand-product argument, at the errors its
  schedule charges: a combiner, a sumcheck round or a combination challenge turns a false claim
  into a true one at few values, and the riders are tracked on the coordinates drawn so far.
  Candidate for ArkLib.
-/
import LvmGrandProduct
import Mathlib.SetTheory.Cardinal.NatCard
import LvmCpMultilinear
import Mathlib.Tactic.LinearCombination

-- (GOLF2: 14 declarations that `certified` does not use moved verbatim to `LvmTypedVEqPhasesXOff`, outside its import closure.)

-- ===== merged from `LvmCpRestriction` (GOLF module merge: `LvmCpRestriction.lean` is now a stub importing `LvmGrandProductSecurity`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToCompPoly/Restriction.lean` (formal rev 40f877dc) as `LvmCpRestriction` for lvm (WP-2).
/-
  LeanVM.Protocol.ToCompPoly.Restriction

  A table restricted to the coordinates of a part-way point, and when that restriction is
  identically zero: the notion a knowledge state function tracks while the coordinates of a
  point are drawn one at a time. Candidate for CompPoly.
-/

/-!
# A table on a part-way point

A *part-way point* (`Partial R`) fixes some coordinates and leaves the others free. A table is
*zero on* a part-way point (`RestrictedZero`) when its multilinear extension vanishes at every
completion of the fixed coordinates by a cube point: the restriction of the extension to the
fixed coordinates is identically zero as a polynomial in the free ones. On the empty part-way
point this says the table is zero (`restrictedZero_empty_iff`); with every coordinate fixed it
says the extension vanishes at the point (`restrictedZero_of_all`). Partial points are built by
placing a vector at an offset (`Partial.ofVector`) and putting two side by side
(`Partial.or`).

The one fact a proof system uses: a table that is not zero on a part-way point is zero on it with
one more coordinate fixed for at most one value of that coordinate
(`card_filter_restrictedZero_update_le`). The extension is affine in the new coordinate, so
vanishing at two values is vanishing at every value, the cube's included.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

variable {R : Type}

/-- A part-way point: for each coordinate, its value if fixed. -/
abbrev Partial (R : Type) : Type := ℕ → Option R

/-- The empty part-way point: nothing fixed. -/
def Partial.empty : Partial R := fun _ ↦ Option.none

/-- A vector placed at an offset: coordinates `off` to `off + k - 1` fixed to `v`, the others
free. -/
def Partial.ofVector (off : ℕ) {k : ℕ} (v : Vector R k) : Partial R :=
  fun i ↦ if h : off ≤ i ∧ i < off + k then some (v[i - off]'(by omega)) else none

/-- Two part-way points side by side: a coordinate the first fixes, at its value; otherwise the
second's. -/
def Partial.or (σ τ : Partial R) : Partial R := fun i ↦ (σ i).or (τ i)

/-- The empty vector fixes nothing. -/
theorem Partial.ofVector_zero (off : ℕ) (v : Vector R 0) :
    Partial.ofVector off v = Partial.empty := by
  funext i
  simp [Partial.ofVector, Partial.empty]

/-- One more entry fixes one more coordinate, the one after the others. -/
theorem Partial.ofVector_push (off : ℕ) {k : ℕ} (v : Vector R k) (c : R) :
    Partial.ofVector off (v.push c) =
      Function.update (Partial.ofVector off v) (off + k) (some c) := by
  funext i
  by_cases hi : i = off + k
  · subst hi
    simp [Partial.ofVector]
  · rw [Function.update_of_ne hi]
    simp only [Partial.ofVector]
    split_ifs with h₁ h₂ h₂
    · rw [Vector.getElem_push_lt (by (clear * - h₁ h₂; omega))]
    · (clear * - off k i hi h₁ h₂; omega)
    · (clear * - h₁ h₂; omega)
    · rfl

/-- Nothing beside a part-way point is the part-way point. -/
theorem Partial.empty_or (τ : Partial R) : Partial.empty.or τ = τ := rfl

/-- A coordinate fixed in the first of two part-way points side by side is fixed in both. -/
theorem Partial.update_or (σ τ : Partial R) (i : ℕ) (c : R) :
    Partial.or (Function.update σ i (some c)) τ = Function.update (σ.or τ) i (some c) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Partial.or]
  · simp [Partial.or, Function.update_of_ne hj]

variable [CommRing R]

/-- The point of a part-way point at a completion `b`: the fixed coordinates, the others the bits
of `b`. -/
def Partial.point {n : ℕ} (σ : Partial R) (b : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn fun k ↦ (σ k).getD (boolVec b)[k]

/-- A table is zero on a part-way point when its extension vanishes at every completion of the
fixed coordinates by a cube point. -/
def RestrictedZero {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) : Prop :=
  ∀ b : Fin (2 ^ n), evalMle t (σ.point b) = 0

instance [DecidableEq R] {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) :
    Decidable (RestrictedZero t σ) :=
  inferInstanceAs (Decidable (∀ _b : Fin (2 ^ n), _ = _))

/-- The point of the empty part-way point at a completion is the cube point itself. -/
@[simp] theorem Partial.point_empty {n : ℕ} (b : Fin (2 ^ n)) :
    (Partial.empty : Partial R).point b = boolVec b := by
  apply Vector.ext
  intro k hk
  simp [Partial.point, Partial.empty]

/-- On the empty part-way point, zero means the table is zero. -/
theorem restrictedZero_empty_iff {n : ℕ} (t : CMlPolynomialEval R n) :
    RestrictedZero t Partial.empty ↔ ∀ i : Fin (2 ^ n), t[i] = 0 := by
  simp only [RestrictedZero, Partial.point_empty, evalMle_boolVec]

/-- The difference of two tables, entry by entry. -/
def diffTable {n : ℕ} (t t' : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ t[i] - t'[i]

/-- The extension of a difference is the difference of the extensions. -/
theorem evalMle_diffTable {n : ℕ} (t t' : CMlPolynomialEval R n) (p : Vector R n) :
    evalMle (diffTable t t') p = evalMle t p - evalMle t' p := by
  simp only [evalMle_eq_sum, diffTable, Fin.getElem_fin, Vector.getElem_ofFn, sub_mul,
    Finset.sum_sub_distrib]

/-- A difference zero on the empty part-way point means the two tables are equal. -/
theorem diffTable_restrictedZero_empty_iff {n : ℕ} (t t' : CMlPolynomialEval R n) :
    RestrictedZero (diffTable t t') Partial.empty ↔ t = t' := by
  rw [restrictedZero_empty_iff]
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have := h ⟨i, hi⟩
    simp only [diffTable, Fin.getElem_fin, Vector.getElem_ofFn] at this
    exact sub_eq_zero.mp this
  · rintro rfl i
    simp [diffTable]

/-- When every coordinate is fixed, zero means the extension vanishes at the point. -/
theorem restrictedZero_of_all {n : ℕ} (t : CMlPolynomialEval R n) (σ : Partial R) (p : Vector R n)
    (hp : ∀ k (hk : k < n), σ k = some p[k]) :
    RestrictedZero t σ ↔ evalMle t p = 0 := by
  have hpoint : ∀ b : Fin (2 ^ n), σ.point b = p := fun b ↦ by
    apply Vector.ext
    intro k hk
    simp [Partial.point, hp k hk]
  simp only [RestrictedZero, hpoint]
  exact ⟨fun h ↦ h ⟨0, Nat.two_pow_pos n⟩, fun h _ ↦ h⟩

/-- The point of a part-way point with one more coordinate fixed. -/
private theorem Partial.point_update {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n) (c : R)
    (b : Fin (2 ^ n)) :
    Partial.point (Function.update σ k (some c)) b = (σ.point b).set k c := by
  apply Vector.ext
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    simp [Partial.point]
  · simp [Partial.point, Function.update_of_ne hjk, Vector.getElem_set_ne hk hj (Ne.symm hjk)]

/-- Fixing a coordinate beyond the table's variables changes nothing. -/
private theorem Partial.point_update_of_le {n : ℕ} (σ : Partial R) (k : ℕ) (hk : n ≤ k) (c : R)
    (b : Fin (2 ^ n)) :
    Partial.point (Function.update σ k (some c)) b = σ.point b := by
  apply Vector.ext
  intro j hj
  simp [Partial.point, Function.update_of_ne (show j ≠ k by (clear * - j k n hk hj; omega))]

/-- Setting a coordinate of a completion to its own value changes nothing. -/
private theorem Partial.point_set_self {n : ℕ} (σ : Partial R) (k : ℕ) (hk : k < n)
    (b : Fin (2 ^ n)) : (σ.point b).set k ((σ.point b)[k]) = σ.point b :=
  Vector.set_getElem_self hk

open scoped Classical in
/-- **One escape at most.** A table that is not zero on a part-way point is zero on it with one
more coordinate fixed for at most one value of that coordinate: its extension is affine in
the coordinate, so vanishing at two values is vanishing everywhere. -/
theorem card_filter_restrictedZero_update_le [IsDomain R] [Fintype R] {n : ℕ}
    (t : CMlPolynomialEval R n) (σ : Partial R) (k : ℕ)
    (hne : ¬ RestrictedZero t σ) :
    (Finset.univ.filter fun c ↦ RestrictedZero t (Function.update σ k (some c))).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun c₁ h₁ c₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  by_contra hc
  apply hne
  by_cases hk : k < n
  · intro b
    have e₁ := h₁.2 b
    have e₂ := h₂.2 b
    rw [Partial.point_update σ k hk c₁ b, evalMle_set t _ hk] at e₁
    rw [Partial.point_update σ k hk c₂ b, evalMle_set t _ hk] at e₂
    -- `A + c·(B − A) = 0` at two distinct `c`: both `A` and `B` vanish.
    set A := evalMle t ((σ.point b).set k 0) with hA
    set B := evalMle t ((σ.point b).set k 1) with hB
    have hBA : B = A := by
      have : (c₁ - c₂) * (B - A) = 0 := by linear_combination e₁ - e₂
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hc
      · exact sub_eq_zero.mp h
    have hA0 : A = 0 := by
      rw [hBA] at e₁
      linear_combination e₁
    have := evalMle_set t (σ.point b) hk ((σ.point b)[k])
    rw [Partial.point_set_self σ k hk b] at this
    rw [this, ← hA, ← hB, hBA, hA0]
    ring
  · intro b
    have := h₁.2 b
    rwa [Partial.point_update_of_le σ k (by (clear * - hk; omega)) c₁ b] at this

end
end LeanVM.Protocol
end
-- ===== end of `LvmCpRestriction` =====

/-! lvm (WP-2): the ArkLib-typed security halves (`lambdaSecurity`, `childrenSecurity`,
`interpPrefixSecurity`, `interpolateSecurity`, `layerStepSecurity`, `layerStepsSecurity`,
`oddSecurity`, `gkrSecurity`), built on `ToArkLib.Typed.*` outside lvm's imports, are cut. Kept,
and made public where the source had them private: the part-way points, the rider trackers, the
tracked family with its consistency and soundness, the combiner's batching fact, the
descendants' check soundness, the combination challenges' one-escape count, and the relations
between steps. Added, as counts over the finite field (what the cut typed halves charged as
errors): `card_badBatch_le` (copied from `ToArkLib.Typed.Batch`), `card_lambda_le` (the combiner,
`nside - 1`), `card_round_badChallenge_le` (a round of the layer's sumcheck, `2 ^ ρ`),
`card_interpDone_le` (the last combination challenge, `1`). -/

/-!
# Knowledge soundness of the grand product

`gkrSecurity nside μ leaves riders` is the security half of `gkr` at the errors
`Typed.gkrErrors F (1 / |F|) nside μ`, with the extractor that keeps the trivial witness. With
the witness `Unit` throughout, it is round-by-round soundness of the language `Gkr.relIn`:
nothing is extracted. It is composed, like the completeness half, from the parts' through
`Typed.Security.append`, so every challenge keeps the error its slot assigned it:

* the combiner: batching by powers (`Typed.batchSecurity`): a statement outside the layer
  relation combines into the family's first claim at `nside − 1` combiners at most, since two
  different value vectors combine to the same scalar at the roots of a polynomial of degree
  `nside − 1`;
* the sumcheck rounds: `SumcheckRound.roundsSecurity` on the layer's family, whose honest
  polynomials are consistent (`familyT_consistent`) and whose invariant is sound
  (`familyT_sound`);
* the descendants: their check is sound at error zero (`combineCheck_sound`): values that pass
  it and are the honest ones make the final claim the summand at the point;
* the combination challenges: a wrong value vector agrees with the honest one on one more
  coordinate at one challenge at most (`card_interpNext_le`), by
  `card_filter_restrictedZero_update_le` on the difference of the two tables.

*The riders.* The output relation asks each rider's extension to vanish at the low coordinates
of the final point, which are the last layer's combination challenges and then its sumcheck
challenges. Inside the argument the riders stay zero tables (`constTrack`): nothing of a layer's
point survives the next layer. At the last layer the state tracks them on the coordinates drawn
so far (`progTrack`, through `RestrictedZero` on a `Partial` point: `roundsPartial` during the
rounds, `interpPartial` during the combination challenges, both a challenge vector placed at its
coordinates by `Partial.ofVector`), and a rider that is not zero on the
coordinates so far is zero on one more at one challenge at most. A `RiderTrack` is what a step's
security needs of either: the predicates during the rounds, during the combination challenges
and at the new point, how each hands over to the next, and the one-escape bounds. The escape of
a rider at a challenge is dominated by the claim's at the same challenge, so the riders add
nothing to `Typed.gkrErrors`.

The step from layer `m` with `k` radix-four steps to follow uses the progressive tracker when
`k = 0` and the constant one otherwise (`layerStepsSecurity` splits on `k`); so does the first
step when `μ` is odd (`oddSecurity`). The relations between steps are `stepsIn`: the layer
relation, or, with no step left, the output relation read at the layer.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

namespace Gkr

variable {F : Type}

/-! ## The part-way points of a step -/

/-- The coordinates of a layer's new point fixed by its first `j` sumcheck challenges: the
coordinates `ρ` to `ρ + j - 1`, the combination challenges coming first. -/
abbrev roundsPartial (ρ : ℕ) {j : ℕ} (χ : Vector F j) : Partial F := Partial.ofVector ρ χ

/-- The first `i` combination challenges as a part-way point of the descendants' `ρ`
coordinates. -/
abbrev combPartial {i : ℕ} (u : Vector F i) : Partial F := Partial.ofVector 0 u

/-- The coordinates fixed by the sumcheck challenges and the first `i` combination
challenges. -/
abbrev interpPartial (ρ : ℕ) {m : ℕ} (χ : Vector F m) {i : ℕ} (u : Vector F i) : Partial F :=
  (combPartial u).or (roundsPartial ρ χ)

/-- With all `ρ` combination challenges drawn, every coordinate of the new point `(u, χ)` is
fixed. -/
theorem interpPartial_full (ρ : ℕ) {m : ℕ} (χ : Vector F m) (u : Vector F ρ) (k : ℕ)
    (hk : k < m + ρ) :
    interpPartial ρ χ u k = some ((Vector.cast (Nat.add_comm ρ m) (u ++ χ))[k]) := by
  simp only [interpPartial, combPartial, roundsPartial, Partial.or, Partial.ofVector,
    Vector.getElem_cast, Vector.getElem_append]
  split_ifs <;> first | rfl | omega

variable [Field F] [Finite F] [DecidableEq F] {X : Type} {ι : Type} {O : ι → Type}
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))

/-! ## Riders on part-way points -/

/-- Every rider is zero on the part-way point. -/
def RidersZeroOn (x : X) (o : ∀ i, O i) (σ : Partial F) : Prop :=
  ∀ r ∈ riders x o, RestrictedZero r.2 σ

omit [Finite F] [DecidableEq F] in
theorem ridersZeroOn_empty_iff (x : X) (o : ∀ i, O i) :
    RidersZeroOn μ riders x o Partial.empty ↔ RidersZero μ riders x o := by
  simp only [RidersZeroOn, RidersZero, restrictedZero_empty_iff]

omit [DecidableEq F] in
/-- Riders not all zero on a part-way point are all zero on it with one more coordinate fixed
for at most one value. -/
theorem card_ridersZeroOn_update_le (x : X) (o : ∀ i, O i) (σ : Partial F) (k : ℕ)
    (hne : ¬ RidersZeroOn μ riders x o σ) :
    Nat.card {c // RidersZeroOn μ riders x o (Function.update σ k (some c))} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  rw [natCard_subtype_eq_card_filter]
  simp only [RidersZeroOn, not_forall] at hne
  obtain ⟨r, hr, hne⟩ := hne
  refine (Finset.card_le_card fun c hc ↦ ?_).trans
    (card_filter_restrictedZero_update_le r.2 σ k hne)
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨Finset.mem_univ _, hc.2 r hr⟩

/-! ## How a step tracks the riders -/

/-- How a step's knowledge state tracks the riders: a predicate during the sumcheck rounds
(`inv`), one during the combination challenges (`invU`), one at the new point (`out`); the
first is the riders' zeroness at the start, each hands over to the next, and each challenge
restores a broken predicate at one value at most. The field is finite: a `Nat.card` count of an
infinite set is `0`, which would make the two escape bounds hold of any predicate. -/
structure RiderTrack [Finite F] (ρ m : ℕ) where
  /-- During the rounds, after `j` challenges. -/
  inv : X → (∀ i, O i) → (j : ℕ) → Vector F j → Prop
  /-- During the combination challenges, after `i` of them, at the sumcheck's point. -/
  invU : X → (∀ i, O i) → Vector F m → (i : ℕ) → Vector F i → Prop
  /-- At the new point. -/
  out : X → (∀ i, O i) → Vector F (m + ρ) → Prop
  /-- Before the first round, the riders are zero. -/
  inv_zero : ∀ x o (v : Vector F 0), inv x o 0 v ↔ RidersZero μ riders x o
  /-- A round's challenge restores the predicate at one value at most. -/
  inv_escape : ∀ x o j (χ : Vector F j), ¬ inv x o j χ →
    Nat.card {c // inv x o (j + 1) (χ.push c)} ≤ 1
  /-- The rounds hand over to the combination challenges. -/
  invU_zero : ∀ x o (χ : Vector F m) (v : Vector F 0), invU x o χ 0 v ↔ inv x o m χ
  /-- A combination challenge restores the predicate at one value at most. -/
  invU_escape : ∀ x o (χ : Vector F m) i (u : Vector F i), ¬ invU x o χ i u →
    Nat.card {c // invU x o χ (i + 1) (u.push c)} ≤ 1
  /-- At the new point, the predicate is the one after all combination challenges. -/
  out_iff : ∀ x o (χ : Vector F m) (u : Vector F ρ),
    out x o (Vector.cast (Nat.add_comm ρ m) (u ++ χ)) ↔ invU x o χ ρ u

omit [Field F] [Finite F] [DecidableEq F] in
/-- A predicate that does not depend on the challenge, false, is restored at no value. -/
theorem card_const_le {P : Prop} (hP : ¬ P) : Nat.card {_c : F // P} ≤ 1 := by
  have : IsEmpty {_c : F // P} := ⟨fun c ↦ hP c.2⟩
  rw [Nat.card_of_isEmpty]
  exact zero_le_one

/-- Inside the argument, the riders stay zero tables: nothing of a layer's point survives. -/
def constTrack (ρ m : ℕ) : RiderTrack μ riders ρ m where
  inv := fun x o _ _ ↦ RidersZero μ riders x o
  invU := fun x o _ _ _ ↦ RidersZero μ riders x o
  out := fun x o _ ↦ RidersZero μ riders x o
  inv_zero := fun _ _ _ ↦ Iff.rfl
  inv_escape := fun _ _ _ _ h ↦ by exact card_const_le h
  invU_zero := fun _ _ _ _ ↦ Iff.rfl
  invU_escape := fun _ _ _ _ _ h ↦ by exact card_const_le h
  out_iff := fun _ _ _ _ ↦ Iff.rfl

/-- At the last layer, whose point is the final one, the riders are zero on the coordinates
drawn so far, and at the end vanish at the low coordinates of the final point. -/
def progTrack (ρ m : ℕ) (h : m + ρ = μ) : RiderTrack μ riders ρ m where
  inv := fun x o _ χ ↦ RidersZeroOn μ riders x o (roundsPartial ρ χ)
  invU := fun x o χ _ u ↦ RidersZeroOn μ riders x o (interpPartial ρ χ u)
  out := fun x o ζ ↦ ∀ r ∈ riders x o, evalMle r.2 (lowPoint (Vector.cast h ζ) r.1) = 0
  inv_zero := fun x o v ↦ by
    simp only [roundsPartial, Partial.ofVector_zero, ridersZeroOn_empty_iff]
  inv_escape := fun x o j χ hne ↦ by
    simp only [roundsPartial, Partial.ofVector_push]
    exact card_ridersZeroOn_update_le μ riders x o (roundsPartial ρ χ) (ρ + j) hne
  invU_zero := fun x o χ v ↦ by
    simp only [interpPartial, combPartial, Partial.ofVector_zero, Partial.empty_or]
  invU_escape := fun x o χ i u hne ↦ by
    simp only [interpPartial, combPartial, Partial.ofVector_push, Partial.update_or,
      Nat.zero_add]
    exact card_ridersZeroOn_update_le μ riders x o (interpPartial ρ χ u) i hne
  out_iff := fun x o χ u ↦ by
    simp only [RidersZeroOn]
    refine forall₂_congr fun r hr ↦ ?_
    rw [restrictedZero_of_all r.2 _ (lowPoint (Vector.cast h (Vector.cast (Nat.add_comm ρ m)
      (u ++ χ))) r.1)]
    intro k hk
    rw [interpPartial_full ρ χ u k (by have := r.1.isLt; omega)]
    simp [lowPoint, Vector.getElem_cast]

/-! ## The layer's family with a tracker -/

section Layer

variable (ρ m : ℕ)

/-- The layer's family of claims, the riders tracked by `T`: the same claims, polynomials and
domain as `family`, so the same rounds; `family` is this family at `constTrack`. -/
noncomputable def familyT (T : RiderTrack μ riders ρ m) :
    SumcheckRound.Family F (LayerX X F nside m) O Unit (2 ^ ρ) where
  claim := fun ctx j cv ↦ partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) j cv
  poly := roundPoly nside μ leaves ρ m
  weight := weights nside m
  inv := fun ctx j cv ↦ T.inv (dataOf ctx) (oraclesOf ctx) j cv

omit [DecidableEq F] in
/-- The honest polynomials of the tracked family are consistent: the same as `family`'s. -/
theorem familyT_consistent (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Consistent m :=
  ⟨(family_honest nside μ leaves riders ρ m).check, (family_honest nside μ leaves riders ρ m).next⟩

omit [DecidableEq F] in
/-- The tracked family's invariant is sound: a round's challenge restores it at one value at
most, within the polynomial degree. -/
theorem familyT_sound (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Sound m :=
  fun _ _ cv _ hinv ↦ (T.inv_escape _ _ _ cv hinv).trans Nat.one_le_two_pow

/-! ## The combiner -/

variable {S : Type} (inp : S → LayerStmt X F nside m)

omit [DecidableEq F] in
/-- After the combiner, the family's first relation is the riders' condition and the combined
claim being the combination, by the same powers, of the trees' levels at the layer's point. -/
theorem mem_rel_lambdaNext (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    (s : LayerStmt X F nside m) (o : ∀ i, O i) (l : F) :
    ((lambdaNext nside m s l, o), ()) ∈
        SumcheckRound.rel (familyT nside μ leaves riders ρ m T) 0 ↔
      RidersZero μ riders s.1 o ∧
        powerBatch s.2.2 l =
          powerBatch (fun t ↦ evalMle (layerTable (leaves s.1 o t) m) s.2.1) l := by
  change T.inv s.1 o 0 #v[] ∧ (lambdaNext nside m s l).2.2 =
    partialSum (summand nside μ leaves ρ m (((s, l), o), ())) s.2.1 0 #v[] ↔ _
  rw [T.inv_zero, partialSum_summand_zero nside μ leaves ρ m hm s o l]
  exact Iff.rfl

omit [DecidableEq F] in
/-- The combiner's batching hypothesis: a statement outside the relation has the levels' values
as true values, fixed before the combiner, which a combiner landing in the family's first relation
makes the combined claim's, and which differ from the claimed values. -/
theorem lambda_batch (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    {relS : Set ((S × ∀ i, O i) × Unit)}
    (hinp : ∀ s o, ((s, o), ()) ∈ relS ↔ ((inp s, o), ()) ∈ layerRel nside μ leaves riders m)
    (s : S) (o : ∀ i, O i) :
    ∃ a : Fin nside → F, ∀ w ρ', ((s, o), w) ∉ relS →
      (((((inp s, ρ'), (#v[], powerBatch (inp s).2.2 ρ')) :
          SumcheckRound.Stmt (LayerX X F nside m) F 0), o), w) ∈
        SumcheckRound.rel (familyT nside μ leaves riders ρ m T) 0 →
        a ≠ (inp s).2.2 ∧ powerBatch (inp s).2.2 ρ' = powerBatch a ρ' :=
  ⟨fun t ↦ evalMle (layerTable (leaves (inp s).1 o t) m) (inp s).2.1, fun w l hs hl ↦ by
    cases w
    obtain ⟨hz, hval⟩ := (mem_rel_lambdaNext nside μ leaves riders ρ m T hm (inp s) o l).mp hl
    exact ⟨fun he ↦ hs ((hinp s o).mpr ⟨hz, fun t ↦ congrFun he t⟩), hval⟩⟩

/-- The count of bad combiners (lvm: copied from leanVM `ToArkLib.Typed.Batch.card_badBatch_le`,
the count behind `Typed.batchSecurity`): at most `k - 1`, whenever the statement has true values
fixed before the challenge and the witness, which every bad combiner makes the combined claim's
and which differ from the claimed values. -/
theorem _root_.LeanVM.Protocol.card_badBatch_le {S T W : Type} {F : Type} [Field F] [Finite F]
    {k : ℕ} {value : S → Fin k → F} {out : S → F → F → T}
    {relIn : Set ((S × ∀ i, O i) × W)} {relOut : Set ((T × ∀ i, O i) × W)}
    (s : S) (o : ∀ i, O i)
    (h : ∃ a : Fin k → F, ∀ w ρ, ((s, o), w) ∉ relIn →
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut →
        a ≠ value s ∧ powerBatch (value s) ρ = powerBatch a ρ) :
    Nat.card {ρ // ∃ w, ((s, o), w) ∉ relIn ∧
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut} ≤ k - 1 := by
  have := Fintype.ofFinite F
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨a, ha⟩ := h
  by_cases hgood : ∃ ρ w, ((s, o), w) ∉ relIn ∧
      ((out s ρ (powerBatch (value s) ρ), o), w) ∈ relOut
  · obtain ⟨ρ₀, w₀, hin₀, hρ₀⟩ := hgood
    refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans
      (card_false_batch_le (value s) a (Function.ne_iff.mp (ha w₀ ρ₀ hin₀ hρ₀).1.symm))
    obtain ⟨w', hw', hout⟩ := (Finset.mem_filter.mp hρ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ha w' ρ hw' hout).2⟩
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ρ - ⟨w', hw', hout⟩
    exact hgood ⟨ρ, w', hw', hout⟩

omit [DecidableEq F] in
/-- The combiner's count (lvm: new, what the cut `lambdaSecurity` charged at
`(nside − 1) / |F|`): from a statement outside the layer relation, at most `nside − 1` combiners
land in the tracked family's first relation. -/
theorem card_lambda_le (T : RiderTrack μ riders ρ m) (hm : m + ρ ≤ μ)
    {relS : Set ((S × ∀ i, O i) × Unit)}
    (hinp : ∀ s o, ((s, o), ()) ∈ relS ↔ ((inp s, o), ()) ∈ layerRel nside μ leaves riders m)
    (s : S) (o : ∀ i, O i) :
    Nat.card {l // ∃ w, ((s, o), w) ∉ relS ∧
      (((((inp s, l), (#v[], powerBatch (inp s).2.2 l)) :
          SumcheckRound.Stmt (LayerX X F nside m) F 0), o), w) ∈
        SumcheckRound.rel (familyT nside μ leaves riders ρ m T) 0} ≤ nside - 1 :=
  card_badBatch_le (value := fun s ↦ (inp s).2.2)
    (out := fun s l c ↦ (((inp s, l), (#v[], c)) : SumcheckRound.Stmt (LayerX X F nside m) F 0))
    s o (lambda_batch nside μ leaves riders ρ m inp T hm hinp s o)

/-! ## The descendants -/

/-- After the descendants' message with `i` combination challenges drawn: the riders by the
tracker, and each tree's values agree with the honest ones on the challenges drawn so far. At
`i = 0` and `constTrack` it is `childRel 0`: agreement on no challenge is equality. -/
def childRelT (T : RiderTrack μ riders ρ m) (i : ℕ) :
    Set ((InterpStmt X F nside m ρ i × ∀ j, O j) × Unit) :=
  {p | T.invU p.1.1.1.1 p.1.2 p.1.1.1.2.1 i p.1.1.2 ∧
    ∀ t, RestrictedZero
      (diffTable (p.1.1.1.2.2 t) (children nside μ leaves ρ m p.1.1.1.1 p.1.2 p.1.1.1.2.1 t))
      (combPartial p.1.1.2)}

/-- The descendants' check is sound: values that pass it and are the honest ones make the final
claim the summand at the point. -/
theorem combineCheck_sound (T : RiderTrack μ riders ρ m)
    (s : SumcheckRound.Stmt (LayerX X F nside m) F m) (o : ∀ i, O i)
    (ch : Fin nside → CMlPolynomialEval F ρ) (hc : combineCheck nside ρ m s ch = true)
    (hout : ((childNext nside ρ m s ch, o), ()) ∈ childRelT nside μ leaves riders ρ m T 0) :
    ((s, o), ()) ∈ SumcheckRound.rel (familyT nside μ leaves riders ρ m T) m := by
  obtain ⟨hinv, hch⟩ := hout
  refine ⟨(T.invU_zero _ _ _ _).mp hinv, ?_⟩
  have hch' : ∀ t, ch t = children nside μ leaves ρ m s.1.1.1 o s.2.1 t := fun t ↦ by
    have := hch t
    simp only [combPartial, Partial.ofVector_zero] at this
    exact (diffTable_restrictedZero_empty_iff _ _).mp this
  change s.2.2 = partialSum (summand nside μ leaves ρ m ((s.1, o), ())) s.1.1.2.1 m s.2.1
  rw [partialSum_self]
  rw [combineCheck, decide_eq_true_eq] at hc
  rw [hc, powerBatch]
  unfold summand
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  simp [hch', children, below]

/-! ## The combination challenges -/

omit [DecidableEq F] in
/-- A statement outside the relation after `i` combination challenges is inside it after one
more at one challenge at most: the riders' predicate or some tree's agreement was broken, and
each is restored at one value at most. -/
theorem card_interpNext_le (T : RiderTrack μ riders ρ m) {i : ℕ}
    (s : InterpStmt X F nside m ρ i) (o : ∀ j, O j)
    (hs : ((s, o), ()) ∉ childRelT nside μ leaves riders ρ m T i) :
    Nat.card {c // ((interpNext nside ρ m s c, o), ()) ∈
      childRelT nside μ leaves riders ρ m T (i + 1)} ≤ 1 := by
  have := Fintype.ofFinite F
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hinv : T.invU s.1.1 o s.1.2.1 i s.2
  · have hne : ∃ t, ¬ RestrictedZero
        (diffTable (s.1.2.2 t) (children nside μ leaves ρ m s.1.1 o s.1.2.1 t))
        (combPartial s.2) := by
      by_contra h
      exact hs ⟨hinv, fun t ↦ by_contra fun ht ↦ h ⟨t, ht⟩⟩
    obtain ⟨t, ht⟩ := hne
    refine (Finset.card_le_card fun c hc ↦ ?_).trans
      (card_filter_restrictedZero_update_le _ (combPartial s.2) i ht)
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hc.2.2 t
    simp only [show (interpNext nside ρ m s c).2 = s.2.push c from rfl, combPartial,
      Partial.ofVector_push, Nat.zero_add] at this
    exact this
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans
      ((natCard_subtype_eq_card_filter _).symm.trans_le
        (T.invU_escape _ _ _ i s.2 hinv))
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hc.2.1⟩

/-- The step's output relation, the riders by the tracker: the new values are the level below
at the new point. -/
def stepOutT (T : RiderTrack μ riders ρ m) :
    Set ((LayerStmt X F nside (m + ρ) × ∀ i, O i) × Unit) :=
  {p | T.out p.1.1.1 p.1.2 p.1.1.2.1 ∧
    ∀ s, evalMle (layerTable (leaves p.1.1.1 p.1.2 s) (m + ρ)) p.1.1.2.1 = p.1.1.2.2 s}

omit [DecidableEq F] in
/-- The interpolated statement is in the step's output relation exactly when the statement before
it is in the relation after all `ρ` combination challenges. -/
theorem interpDone_mem_stepOutT_iff (T : RiderTrack μ riders ρ m)
    (s : InterpStmt X F nside m ρ ρ) (o : ∀ i, O i) :
    ((interpDone nside ρ m s, o), ()) ∈ stepOutT nside μ leaves riders ρ m T ↔
      ((s, o), ()) ∈ childRelT nside μ leaves riders ρ m T ρ := by
  show (T.out s.1.1 o (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1)) ∧
    ∀ t, evalMle (layerTable (leaves s.1.1 o t) (m + ρ))
      (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1)) = evalMle (s.1.2.2 t) s.2) ↔
    (T.invU s.1.1 o s.1.2.1 ρ s.2 ∧ ∀ t, RestrictedZero
      (diffTable (s.1.2.2 t) (children nside μ leaves ρ m s.1.1 o s.1.2.1 t)) (combPartial s.2))
  rw [T.out_iff]
  refine and_congr Iff.rfl (forall_congr' fun t ↦ ?_)
  rw [restrictedZero_of_all _ (combPartial s.2) s.2
      (fun k hk ↦ by simp [combPartial, Partial.ofVector, hk]), evalMle_diffTable,
    sub_eq_zero, evalMle_cast_append, eq_comm]
  exact Iff.rfl

end Layer

/-! ## The whole argument -/

end Gkr

end
end LeanVM.Protocol
