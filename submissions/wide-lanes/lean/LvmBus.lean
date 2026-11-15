-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Bus.lean` (formal rev 40f877dc) as `LvmBus` for lvm (WP-2).
/-
  LeanVM.Protocol.Bus

  The bus phase: the fingerprint challenges, the roots of the three product trees, the
  grand-product argument down to their leaves, and the boundary columns' values, after which the
  leaf claims are owed by the tables' forms. Definition and perfect completeness.
-/
import LvmSpineErrors
import LvmSpineSeams
import LvmGrandProduct
import LvmCpFingerprint
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Roots
import LvmProtoField
import LvmCpMultilinear
import Mathlib.Basic.ENNReal.Inv
import LvmSpineInstance
import LvmCpAmbientStacking

-- ===== merged from `LvmGrandProductPoly` (GOLF module merge: `LvmGrandProductPoly.lean` is now a stub importing `LvmBus`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/GrandProductPoly.lean` (formal rev 40f877dc) as `LvmGrandProductPoly` for lvm (WP-2).
/-
  LeanVM.Protocol.ToArkLib.GrandProductPoly

  The grand-product polynomial of a multiset of tuples: it determines the multiset, and two
  different multisets give equal values at few points of a finite field. Candidate for ArkLib.
-/

/-!
# Grand products of multilinear fingerprints

A tuple is a table on `n` variables, and its fingerprint is the symbolic multilinear extension
`fingerprintPoly` (`LeanVM.Protocol.ToCompPoly.Fingerprint`). The grand product of a multiset
`M` of tuples is `grandProductPoly M = Π_{t ∈ M} (X − fingerprint(t))`, a polynomial in the `n`
fingerprint variables and one more, `X`, indexed by `none`.

* Over an integral domain the polynomial determines the multiset, multiplicities included
  (`grandProductPoly_injective`): read as a polynomial in `X` over the fingerprint variables, it
  is monic and its roots are the fingerprints, and fingerprints determine their tuples. No bound
  relates the characteristic to the multiset's size.
* Each factor has total degree at most `max 1 n`, so two different multisets of at most `cap`
  tuples differ by a nonzero polynomial of degree at most `max 1 n · cap`, which vanishes at no
  more than `max 1 n · cap · |F|ⁿ` of the `|F|ⁿ⁺¹` points over a finite field `F`
  (`card_grandProduct_collision_le`, by the counting Schwartz-Zippel). The multisets are
  fixed before the point.

lvm (WP-2): ArkLib's counting Schwartz-Zippel (`ArkLib.Data.MvPolynomial.SchwartzZippelCounting`,
outside lvm's imports) is restated here from Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`
(`card_zeros_mul_card_le_fin`, `card_zeros_le_of_totalDegree_le_fin`,
`card_zeros_le_of_totalDegree_le`, in `LeanVM.Protocol`, same statements as ArkLib's
`MvPolynomial.card_zeros_le_of_totalDegree_le{,_fin}`).

The fingerprint is derived from leanth PR 16, revision
`23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`, as attributed in `ToCompPoly/Fingerprint.lean`; the
product argument is new and uses Mathlib's `Polynomial.roots_multiset_prod_X_sub_C`. Requested
upstream as [ArkLib #901](https://github.com/Verified-zkEVM/ArkLib/issues/901).
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

section

section ZeroCount

open Finset

/-- Counting Schwartz-Zippel over all of a finite field, in the cleared-denominator form: a nonzero
polynomial in `s` variables of total degree at most `D` has (zeros) · |F| ≤ D · |F| ^ s (lvm: new,
from Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`). -/
theorem card_zeros_mul_card_le_fin {F : Type*} [Field F] [Fintype F] [DecidableEq F] {s : ℕ}
    (f : MvPolynomial (Fin s) F) (hf : f ≠ 0) {D : ℕ} (hd : f.totalDegree ≤ D) :
    #{x : Fin s → F | MvPolynomial.eval x f = 0} * Fintype.card F ≤
      D * Fintype.card F ^ s := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hf (Finset.univ : Finset F)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at h
  have hq : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hq] at h
  have h' : #{x : Fin s → F | MvPolynomial.eval x f = 0} * Fintype.card F ≤
      f.totalDegree * Fintype.card F ^ s := by exact_mod_cast h
  exact h'.trans (Nat.mul_le_mul_right _ hd)

/-- Counting Schwartz-Zippel over all of a finite field: a nonzero polynomial in `s` variables of
total degree at most `D` has at most `D * |F| ^ (s - 1)` zeros in `Fin s → F` (lvm: restated from
ArkLib's `MvPolynomial.card_zeros_le_of_totalDegree_le_fin`, same statement). -/
theorem card_zeros_le_of_totalDegree_le_fin
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {s : ℕ}
    (f : MvPolynomial (Fin s) F) (hf : f ≠ 0) {D : ℕ} (hd : f.totalDegree ≤ D) :
    #{x : Fin s → F | MvPolynomial.eval x f = 0} ≤ D * Fintype.card F ^ (s - 1) := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have key := card_zeros_mul_card_le_fin f hf hd
  rcases s with _ | t
  · simp only [pow_zero, mul_one, Nat.zero_sub] at key ⊢
    exact le_trans (Nat.le_mul_of_pos_right _ hq) key
  · refine Nat.le_of_mul_le_mul_right ?_ hq
    simpa [pow_succ, mul_assoc] using key

/-- Counting Schwartz-Zippel over all of a finite field, for an arbitrary finite index type of
variables: a nonzero polynomial in the variables `ι` of total degree at most `D` has at most
`D * |F| ^ (|ι| - 1)` zeros in `ι → F` (lvm: restated from ArkLib's
`MvPolynomial.card_zeros_le_of_totalDegree_le`, same statement and proof). -/
theorem card_zeros_le_of_totalDegree_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial ι F) (hf : f ≠ 0) {D : ℕ} (hd : f.totalDegree ≤ D) :
    #{x : ι → F | MvPolynomial.eval x f = 0} ≤ D * Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  set e := Fintype.equivFin ι
  have hg : MvPolynomial.rename (e : ι → Fin (Fintype.card ι)) f ≠ 0 := fun h =>
    hf (MvPolynomial.rename_injective _ e.injective (by simpa using h))
  have hgd : (MvPolynomial.rename (e : ι → Fin (Fintype.card ι)) f).totalDegree ≤ D :=
    le_trans (MvPolynomial.totalDegree_rename_le _ _) hd
  refine le_trans (le_of_eq ?_) (card_zeros_le_of_totalDegree_le_fin _ hg hgd)
  refine Finset.card_nbij' (fun x => x ∘ e.symm) (fun y => y ∘ e) ?_ ?_ ?_ ?_ <;>
    intro x hx <;> simp_all [MvPolynomial.eval_rename, Function.comp_assoc]

end ZeroCount

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The product in a separate univariate challenge over the fingerprint coefficient ring. -/
noncomputable def grandProductUnivariate (M : Multiset (CMlPolynomialEval R n)) :
    Polynomial (MvPolynomial (Fin n) R) :=
  (M.map fun t ↦ Polynomial.X - Polynomial.C (fingerprintPoly t)).prod

/-- The same grand product with the product and fingerprint challenges as separate variables. -/
noncomputable def grandProductPoly (M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial (Option (Fin n)) R :=
  (M.map fingerprintFactorPoly).prod

/-- The product of the fingerprints of a multiset of tuples, in the fingerprint variables of the
joint ones: a factor that involves no `X`. -/
noncomputable def fingerprintProdPoly (U : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial (Option (Fin n)) R :=
  (U.map fun u ↦ MvPolynomial.rename some (fingerprintPoly u)).prod

/-- A grand product times a product of fingerprints: a bus side whose padding leaves are the
fingerprints of `U` (`doc/leanvm`, Proposition `prop:pad`). -/
noncomputable def paddedProductPoly (U M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial (Option (Fin n)) R :=
  fingerprintProdPoly U * grandProductPoly M

/-- Renaming by `some` lands in the constant coefficients of the polynomial in the variable
`none`. -/
private theorem optionEquivLeft_rename_some {R σ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    MvPolynomial.optionEquivLeft R σ (MvPolynomial.rename some p) =
      Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The joint-variable and univariate representations agree through the standard equivalence. -/
theorem optionEquivLeft_grandProductPoly (M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial.optionEquivLeft R (Fin n) (grandProductPoly M) =
      grandProductUnivariate M := by
  simp [grandProductPoly, grandProductUnivariate, map_multiset_prod,
    Multiset.map_map, Function.comp_def, fingerprintFactorPoly,
    optionEquivLeft_rename_some]

/-- Evaluation of the symbolic grand product is the actual product of fingerprint factors. -/
theorem eval₂_grandProductPoly {S : Type*} [CommRing S]
    (M : Multiset (CMlPolynomialEval R n)) (φ : R →+* S) (z : Vector S n) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β (fun j ↦ z[j])) (grandProductPoly M) =
      (M.map fun t ↦ β - eval₂Mle t φ z).prod := by
  change MvPolynomial.eval₂Hom φ (fun i ↦ i.elim β (fun j ↦ z[j]))
    (grandProductPoly M) = _
  simp only [grandProductPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.coe_eval₂Hom, eval₂_fingerprintFactorPoly]

/-- Evaluation of the product of fingerprints is the product of the extensions. -/
theorem eval₂_fingerprintProdPoly {S : Type*} [CommRing S]
    (U : Multiset (CMlPolynomialEval R n)) (φ : R →+* S) (z : Vector S n) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β (fun j ↦ z[j])) (fingerprintProdPoly U) =
      (U.map fun u ↦ eval₂Mle u φ z).prod := by
  change MvPolynomial.eval₂Hom φ (fun i ↦ i.elim β (fun j ↦ z[j])) (fingerprintProdPoly U) = _
  simp only [fingerprintProdPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ ↦ eval₂_fingerprintPoly u φ z)

/-- Products of fingerprints commute with coefficient maps. -/
theorem map_fingerprintProdPoly {S : Type*} [CommRing S]
    (φ : R →+* S) (U : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial.map φ (fingerprintProdPoly U) =
      fingerprintProdPoly (U.map (CMlPolynomialEval.map φ)) := by
  simp [fingerprintProdPoly, map_multiset_prod, Multiset.map_map, MvPolynomial.map_rename,
    map_fingerprintPoly]

/-- Grand products commute with coefficient maps, including noninjective maps. -/
theorem map_grandProductPoly {S : Type*} [CommRing S]
    (φ : R →+* S) (M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial.map φ (grandProductPoly M) =
      grandProductPoly (M.map (CMlPolynomialEval.map φ)) := by
  simp [grandProductPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    fingerprintFactorPoly, MvPolynomial.map_rename, map_fingerprintPoly]

/-- An injective coefficient embedding preserves the complete multiset of tuples. -/
theorem map_tupleMultiset_injective {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (Multiset.map (CMlPolynomialEval.map (n := n) φ)) := by
  exact Multiset.map_injective fun _ _ h ↦
    (Vector.map_inj_right fun _ _ h ↦ hφ h).mp h

/-- Every tuple contributes at most `max 1 n` to the joint total degree. -/
theorem totalDegree_grandProductPoly (M : Multiset (CMlPolynomialEval R n)) :
    (grandProductPoly M).totalDegree ≤ max 1 n * M.card := by
  refine (MvPolynomial.totalDegree_multiset_prod _).trans ?_
  simp only [Multiset.map_map, Function.comp_def]
  simpa [Nat.mul_comm] using
    (Multiset.sum_le_card_nsmul
      (M.map fun t ↦ (fingerprintFactorPoly t).totalDegree) (max 1 n)
      (by simpa using fun t (_ : t ∈ M) ↦ totalDegree_fingerprintFactorPoly t))

/-- A product of `|U|` fingerprints has total degree at most `n·|U|`. -/
theorem totalDegree_fingerprintProdPoly (U : Multiset (CMlPolynomialEval R n)) :
    (fingerprintProdPoly U).totalDegree ≤ n * U.card := by
  refine (MvPolynomial.totalDegree_multiset_prod _).trans ?_
  simp only [Multiset.map_map, Function.comp_def]
  simpa [Nat.mul_comm] using
    (Multiset.sum_le_card_nsmul
      (U.map fun u ↦ (MvPolynomial.rename some (fingerprintPoly u)).totalDegree) n
      (by simpa using fun u (_ : u ∈ U) ↦
        (MvPolynomial.totalDegree_rename_le _ _).trans (totalDegree_fingerprintPoly u)))

/-- A padded product has total degree at most `max 1 n` per tuple, padding or not. -/
theorem totalDegree_paddedProductPoly (U M : Multiset (CMlPolynomialEval R n)) :
    (paddedProductPoly U M).totalDegree ≤ max 1 n * (U.card + M.card) := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hU := totalDegree_fingerprintProdPoly U
  have hM := totalDegree_grandProductPoly M
  have : n * U.card ≤ max 1 n * U.card := Nat.mul_le_mul_right _ (le_max_right _ _)
  rw [Nat.mul_add]
  omega

/-- A tuple with a nonzero entry has a nonzero fingerprint. -/
theorem fingerprintPoly_ne_zero {u : CMlPolynomialEval R n} {i : Fin (2 ^ n)} (hu : u[i] ≠ 0) :
    fingerprintPoly u ≠ 0 := by
  intro h
  have := eval_fingerprintPoly_boolVec u i
  rw [h, map_zero] at this
  exact hu this.symm

section Domain

variable [IsDomain R]

/-- The roots are exactly the fingerprints, with their original natural multiplicities. -/
theorem roots_grandProductUnivariate (M : Multiset (CMlPolynomialEval R n)) :
    (grandProductUnivariate M).roots = M.map fingerprintPoly := by
  have h := Polynomial.roots_multiset_prod_X_sub_C (M.map fingerprintPoly)
  simpa only [Multiset.map_map, Function.comp_def, grandProductUnivariate] using h

/-- Symbolic grand products determine tuple multisets in every characteristic. -/
theorem grandProductPoly_injective :
    Function.Injective (grandProductPoly (R := R) (n := n)) := by
  intro M N h
  have hu := congrArg (MvPolynomial.optionEquivLeft R (Fin n)) h
  rw [optionEquivLeft_grandProductPoly, optionEquivLeft_grandProductPoly] at hu
  have hr := congrArg Polynomial.roots hu
  rw [roots_grandProductUnivariate, roots_grandProductUnivariate] at hr
  exact Multiset.map_injective fingerprintPoly_injective hr

/-- Distinct multisets yield a nonzero difference polynomial without a cardinality premise. -/
theorem grandProduct_difference_ne_zero
    {M N : Multiset (CMlPolynomialEval R n)} (h : M ≠ N) :
    grandProductPoly M - grandProductPoly N ≠ 0 := by
  intro hz
  exact h (grandProductPoly_injective (sub_eq_zero.mp hz))

/-- **Padded grand products determine their unpadded tuples** (`doc/leanvm`, Proposition
`prop:pad`): if no padding tuple is zero, equal padded products have equal multisets of tuples,
whatever the padding. As a polynomial in `X`, a padded product is a nonzero constant times the
grand product, so it has the same roots. -/
theorem paddedProductPoly_eq {U V M N : Multiset (CMlPolynomialEval R n)}
    (hU : ∀ u ∈ U, ∃ i : Fin (2 ^ n), u[i] ≠ 0)
    (hV : ∀ v ∈ V, ∃ i : Fin (2 ^ n), v[i] ≠ 0)
    (h : paddedProductPoly U M = paddedProductPoly V N) : M = N := by
  have hc (W : Multiset (CMlPolynomialEval R n)) (hW : ∀ w ∈ W, ∃ i : Fin (2 ^ n), w[i] ≠ 0) :
      MvPolynomial.optionEquivLeft R (Fin n) (fingerprintProdPoly W) =
        Polynomial.C (W.map fingerprintPoly).prod ∧ (W.map fingerprintPoly).prod ≠ 0 := by
    refine ⟨?_, Multiset.prod_ne_zero fun h0 ↦ ?_⟩
    · simp [fingerprintProdPoly, map_multiset_prod, Multiset.map_map, optionEquivLeft_rename_some]
    · obtain ⟨w, hw, h0⟩ := Multiset.mem_map.mp h0
      obtain ⟨i, hi⟩ := hW w hw
      exact fingerprintPoly_ne_zero hi h0
  have hu := congrArg (MvPolynomial.optionEquivLeft R (Fin n)) h
  simp only [paddedProductPoly, map_mul, (hc U hU).1, (hc V hV).1,
    optionEquivLeft_grandProductPoly] at hu
  have hr := congrArg Polynomial.roots hu
  rw [Polynomial.roots_C_mul _ (hc U hU).2, Polynomial.roots_C_mul _ (hc V hV).2,
    roots_grandProductUnivariate, roots_grandProductUnivariate] at hr
  exact Multiset.map_injective fingerprintPoly_injective hr

end Domain

/-- A common cardinality cap bounds the degree of the difference; the cardinalities may differ. -/
theorem totalDegree_grandProduct_difference_le
    (M N : Multiset (CMlPolynomialEval R n)) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (grandProductPoly M - grandProductPoly N).totalDegree ≤ max 1 n * cap := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_grandProductPoly M).trans (Nat.mul_le_mul_left _ hM)
  · exact (totalDegree_grandProductPoly N).trans (Nat.mul_le_mul_left _ hN)

section FiniteField

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Two different multisets of at most `cap` tuples have grand products that agree at no more
than `max 1 n · cap · |F|ⁿ` of the `|F|ⁿ⁺¹` points, the bound attained in dimension zero. -/
theorem card_grandProduct_collision_le
    (M N : Multiset (CMlPolynomialEval F n)) (hne : M ≠ N) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (Finset.univ.filter fun x : Option (Fin n) → F ↦
      MvPolynomial.eval x (grandProductPoly M) =
        MvPolynomial.eval x (grandProductPoly N)).card ≤
      (max 1 n * cap) * Fintype.card F ^ n := by
  have h := card_zeros_le_of_totalDegree_le
    (grandProductPoly M - grandProductPoly N)
    (grandProduct_difference_ne_zero hne)
    (totalDegree_grandProduct_difference_le M N hM hN)
  simpa only [MvPolynomial.eval_sub, sub_eq_zero, Fintype.card_option,
    Fintype.card_fin, Nat.add_sub_cancel] using h

/-- **Proposition `prop:pad`, counting form**: with no zero padding tuple, two sides with
different multisets of tuples and at most `cap` leaves each, padding included, have padded
products that agree at no more than `max 1 n · cap · |F|ⁿ` of the `|F|ⁿ⁺¹` points. -/
theorem card_paddedProduct_collision_le
    {U V M N : Multiset (CMlPolynomialEval F n)} (hU : ∀ u ∈ U, ∃ i : Fin (2 ^ n), u[i] ≠ 0) (hV : ∀ v ∈ V, ∃ i : Fin (2 ^ n), v[i] ≠ 0)
    (hne : M ≠ N) {cap : ℕ} (hM : U.card + M.card ≤ cap) (hN : V.card + N.card ≤ cap) :
    (Finset.univ.filter fun x : Option (Fin n) → F ↦
      MvPolynomial.eval x (paddedProductPoly U M) =
        MvPolynomial.eval x (paddedProductPoly V N)).card ≤
      (max 1 n * cap) * Fintype.card F ^ n := by
  have hd : paddedProductPoly U M - paddedProductPoly V N ≠ 0 :=
    fun hz ↦ hne (paddedProductPoly_eq hU hV (sub_eq_zero.mp hz))
  have hdeg : (paddedProductPoly U M - paddedProductPoly V N).totalDegree ≤ max 1 n * cap :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le
      ((totalDegree_paddedProductPoly U M).trans (Nat.mul_le_mul_left _ hM))
      ((totalDegree_paddedProductPoly V N).trans (Nat.mul_le_mul_left _ hN)))
  have h := card_zeros_le_of_totalDegree_le _ hd hdeg
  simpa only [MvPolynomial.eval_sub, sub_eq_zero, Fintype.card_option,
    Fintype.card_fin, Nat.add_sub_cancel] using h

end FiniteField

end
end LeanVM.Protocol
end
-- ===== end of `LvmGrandProductPoly` =====

-- ===== merged from `LvmFingerprint` (GOLF module merge: `LvmFingerprint.lean` is now a stub importing `LvmBus`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Fingerprint.lean` (formal rev 40f877dc) as `LvmFingerprint` for lvm (WP-2).
/-
  LeanVM.Protocol.Fingerprint

  The fingerprint of a bus tuple and the product of one side of the bus at the challenges
  `(α, β)`, with the two facts the bus rests on: the product polynomial determines the multiset
  of tuples (Lemma 5.2), and unequal multisets of at most `N` tuples give equal products at no
  more than a `4·N / |E|` fraction of the challenges (Theorem 5.1).
-/

/-! lvm (WP-2): `sideProduct_collision`, a VCVio probability `Pr{let ab ← $ᵗ …}[…]` in the
source, is restated as the fraction of challenges over the finite set `(Fin 4 → E) × E` (the
probability of a uniform draw, which is what VCVio's `prEvent_uniformSample_le_div_iff` unfolds
it to); the bound is unchanged. -/

/-!
# Fingerprints and the products of the bus

Specification §5.2 (`doc/leanvm/body/05-arithmetization.tex:22-59` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). A bus tuple is sixteen elements of `K`. The verifier
draws `α ∈ E⁴` and maps a tuple `t` to `π_α(t) = Σ_{i<16} eq(α, i)·t_i` (`fingerprint`), where
`eq(α, i)` is the equality kernel at `α` and the four bits of `i`, low bit first: the tuple read
as a table on four variables and evaluated at `α`. The bit order is the one §5.2 now states
(`:24-26`), the specification's convention for an integer's bits (Annex D,
`d-novel-basis.tex:6`; §8, `08-end-to-end-protocol.tex:9`), and that of the deployed weights (the
prover's `crates/leanvm_core/src/leaf.rs:81-90`, the verifier's `eq_kernel`,
`crates/verifier/src/multilinear.rs:7-19`, at `crates/verifier/src/bus.rs:114`). It then draws
`β ∈ E`, and a side of the bus with the multiset `P` of tuples has the product
`Π_{t ∈ P} (β − π_α(t))` (`sideProduct`).

Over the five formal variables `A_0, …, A_3, X` the product is the polynomial
`Π_P = grandProductPoly P` of `LeanVM.Protocol.ToArkLib.GrandProductPoly`, with coefficients in
`K`; `sideProduct` is its value at `(α, β)` (`sideProduct_eq_eval₂`).

* Lemma 5.2 (`sideProduct_poly_eq_iff`): `Π_P = Π_Q` exactly when `P = Q`, multiplicities
  included. The specification leaves its proof `TODO`; it is unique factorization, carried out
  on the roots of `Π_P` as a polynomial in `X`.
* Theorem 5.1 (`card_sideProduct_collision_le`, `sideProduct_collision`): for `P ≠ Q` of at most
  `N` tuples each, at most `4·N·|E|⁴` of the `|E|⁵` challenges give equal products, so a uniform
  challenge does with probability at most `4·N / |E|`. The `4` is the total degree of a factor
  `β − π_α(t)` in `(α, β)`: `π_α` is multilinear in the four coordinates of `α`, and `β` is a
  separate term of degree one. The bound is nearly attained: a tuple whose fingerprint is
  `α_0 α_1 α_2 α_3` and the zero tuple collide at more than `3·|E|⁴` challenges. The multisets
  are fixed before the challenge is drawn.
* Proposition `prop:pad` (`card_paddedSideProduct_collision_le`): a side whose padding rows add
  leaves `π_α(u)` (`padProduct`) for tuples `u` that are not zero collides with another at no
  more than the same `4·N·|E|⁴` challenges when its tuples `P ≠ Q`, `N` now counting the padding
  leaves too: a padded product is a nonzero polynomial in `α` times `Π_P`, so it still determines
  `P` (`paddedProductPoly_eq`). The padding tuples may be anything else, chosen by the prover.

Written from the specification; the bit order of the weights was then checked against the
deployed verifier.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped ENNReal

section

/-- The fingerprint's weights: `eq(α, i)` for the sixteen coordinates `i`, the bits of `i` low
first. -/
def fingerprintWeights (α : Fin 4 → E) : CMlPolynomialEval E 4 := lagrangeBasis (Vector.ofFn α)

/-- The fingerprint of a bus tuple (§5.2): `π_α(t) = Σ_{i<16} eq(α, i)·t_i`, the weights computed
once. -/
def fingerprint (α : Fin 4 → E) (t : Vector K 16) : E :=
  let w := fingerprintWeights α
  ∑ i : Fin 16, w[i.val] * ofK t[i]

/-- The fingerprint is the extension of the tuple, read as a table on four variables, at `α`. -/
theorem fingerprint_eq_eval₂Mle (α : Fin 4 → E) (t : Vector K 16) :
    fingerprint α t = eval₂Mle (n := 4) t (algebraMap K E) (Vector.ofFn α) := by
  simp only [fingerprint, fingerprintWeights]
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map,
    Extension.Ext.algebraMap_eq_ofBase]
  exact mul_comm _ _

/-- The product of one side of the bus at the challenges `(α, β)`: `Π_{t ∈ P} (β − π_α(t))`. -/
def sideProduct (α : Fin 4 → E) (β : E) (P : Multiset (Vector K 16)) : E :=
  (P.map fun t ↦ β - fingerprint α t).prod

/-- The product is the value at `(α, β)` of the product polynomial, `A_i ↦ α_i` and `X ↦ β`. -/
theorem sideProduct_eq_eval₂ (α : Fin 4 → E) (β : E) (P : Multiset (Vector K 16)) :
    sideProduct α β P =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim β α) (grandProductPoly (n := 4) P) := by
  have h := eval₂_grandProductPoly (n := 4) P (algebraMap K E) (Vector.ofFn α) β
  have hpt : (fun i : Option (Fin 4) ↦ i.elim β fun j ↦ (Vector.ofFn α)[j]) =
      fun i ↦ i.elim β α :=
    funext fun i ↦ by cases i <;> simp
  rw [hpt] at h
  rw [h, sideProduct]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun t _ ↦ by rw [fingerprint_eq_eval₂Mle])

/-- The fingerprint of `1 − a + b`, slot by slot, is `1 − π_α(a) + π_α(b)`: the weights sum to
`1`. -/
theorem fingerprint_one_sub_add (α : Fin 4 → E) (a b : Vector K 16) :
    fingerprint α (Vector.ofFn fun i ↦ 1 - a[i] + b[i]) =
      1 - fingerprint α a + fingerprint α b := by
  have hw : ∑ i : Fin 16, (fingerprintWeights α)[i.val] = 1 := by
    have h1 := sumCube_lagrangeBasis (Vector.ofFn α)
    simpa [sumCube, fingerprintWeights] using h1
  have hk (i : Fin 16) : ofK (1 - a[i.val] + b[i.val]) = 1 - ofK a[i.val] + ofK b[i.val] := by
    change algebraMap K E _ = _
    rw [map_add, map_sub, map_one]
    rfl
  simp only [fingerprint, Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [hk, mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib, hw]

/-- The product of the fingerprints of a multiset of tuples: a side's padding leaves
(`doc/leanvm`, Proposition `prop:pad`). -/
def padProduct (α : Fin 4 → E) (U : Multiset (Vector K 16)) : E :=
  (U.map (fingerprint α)).prod

/-- The padding product is the value at `α` of the product of the fingerprint polynomials. -/
theorem padProduct_eq_eval₂ (α : Fin 4 → E) (β : E) (U : Multiset (Vector K 16)) :
    padProduct α U =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ i.elim β α) (fingerprintProdPoly (n := 4) U) := by
  have h := eval₂_fingerprintProdPoly (n := 4) U (algebraMap K E) (Vector.ofFn α) β
  have hpt : (fun i : Option (Fin 4) ↦ i.elim β fun j ↦ (Vector.ofFn α)[j]) =
      fun i ↦ i.elim β α :=
    funext fun i ↦ by cases i <;> simp
  rw [hpt] at h
  rw [h, padProduct]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun t _ ↦ by rw [fingerprint_eq_eval₂Mle])

/-- **Lemma 5.2**: the product polynomial determines the multiset of tuples. -/
theorem sideProduct_poly_eq_iff (P Q : Multiset (Vector K 16)) :
    grandProductPoly (n := 4) P = grandProductPoly (n := 4) Q ↔ P = Q :=
  ⟨fun h ↦ grandProductPoly_injective h, congrArg _⟩

/-- The pairs `(α, β)` are the points of the five formal variables: `A_i ↦ α_i`, `X ↦ β`. -/
private def challengeEquiv : (Fin 4 → E) × E ≃ (Option (Fin 4) → E) where
  toFun ab := fun i ↦ i.elim ab.2 ab.1
  invFun x := (fun i ↦ x (some i), x none)
  left_inv _ := rfl
  right_inv x := funext fun i ↦ by cases i <;> rfl

/-- **Theorem 5.1**, counting form: two different multisets of at most `N` tuples each have
equal products at no more than `4·N·|E|⁴` challenges `(α, β)`. -/
theorem card_sideProduct_collision_le {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} ≤
      4 * N * Nat.card E ^ 4 := by
  classical
  -- The tuples read in `E`: the polynomials over `E`, their values at the points of `E⁵`.
  let φ := algebraMap K E
  let P' := P.map (CMlPolynomialEval.map (n := 4) φ)
  let Q' := Q.map (CMlPolynomialEval.map (n := 4) φ)
  have hne' : P' ≠ Q' := fun h ↦ hne (map_tupleMultiset_injective φ φ.injective h)
  have hval (ab : (Fin 4 → E) × E) (M : Multiset (Vector K 16)) :
      sideProduct ab.1 ab.2 M = MvPolynomial.eval (challengeEquiv ab)
        (grandProductPoly (M.map (CMlPolynomialEval.map (n := 4) φ))) := by
    rw [sideProduct_eq_eval₂, ← map_grandProductPoly, MvPolynomial.eval_map]
    rfl
  have hcount := card_grandProduct_collision_le P' Q' hne' (cap := N) (by simpa [P'] using hP)
    (by simpa [Q'] using hQ)
  rw [Nat.card_congr (challengeEquiv.subtypeEquiv (q := fun x ↦
      MvPolynomial.eval x (grandProductPoly P') = MvPolynomial.eval x (grandProductPoly Q'))
      fun ab ↦ by rw [hval, hval]),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact hcount.trans_eq (by simp)

/-- **Proposition `prop:pad`, counting form**: two sides whose tuples `P ≠ Q` come with padding
leaves the fingerprints of `U` and `V`, none of them a zero tuple, and at most `N` leaves each,
have equal products at no more than `4·N·|E|⁴` challenges `(α, β)`, whatever the padding. -/
theorem card_paddedSideProduct_collision_le {P Q U V : Multiset (Vector K 16)} (hne : P ≠ Q)
    (hU : ∀ u ∈ U, ∃ i : Fin 16, u[i] ≠ 0) (hV : ∀ v ∈ V, ∃ i : Fin 16, v[i] ≠ 0) {N : ℕ}
    (hP : U.card + P.card ≤ N) (hQ : V.card + Q.card ≤ N) :
    Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P * padProduct ab.1 U =
      sideProduct ab.1 ab.2 Q * padProduct ab.1 V} ≤ 4 * N * Nat.card E ^ 4 := by
  classical
  let φ := algebraMap K E
  let m := Multiset.map (CMlPolynomialEval.map (n := 4) φ)
  have hne' : m P ≠ m Q := fun h ↦ hne (map_tupleMultiset_injective φ φ.injective h)
  have hnz (W : Multiset (Vector K 16)) (hW : ∀ w ∈ W, ∃ i : Fin 16, w[i] ≠ 0) :
      ∀ w ∈ m W, ∃ i : Fin (2 ^ 4), w[i] ≠ 0 := by
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hw'
    obtain ⟨i, hi⟩ := hW w hw
    refine ⟨i, ?_⟩
    simp only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map]
    exact fun h0 ↦ hi (φ.injective (h0.trans (map_zero φ).symm))
  have hval (ab : (Fin 4 → E) × E) (M W : Multiset (Vector K 16)) :
      sideProduct ab.1 ab.2 M * padProduct ab.1 W =
        MvPolynomial.eval (challengeEquiv ab) (paddedProductPoly (m W) (m M)) := by
    rw [sideProduct_eq_eval₂ _ ab.2, padProduct_eq_eval₂ _ ab.2, paddedProductPoly,
      MvPolynomial.eval_mul, ← map_grandProductPoly, ← map_fingerprintProdPoly,
      MvPolynomial.eval_map, MvPolynomial.eval_map, mul_comm]
    rfl
  have hcount := card_paddedProduct_collision_le (hnz U hU) (hnz V hV) hne' (cap := N)
    (by simpa [m] using hP) (by simpa [m] using hQ)
  rw [Nat.card_congr (challengeEquiv.subtypeEquiv (q := fun x ↦
      MvPolynomial.eval x (paddedProductPoly (m U) (m P)) =
        MvPolynomial.eval x (paddedProductPoly (m V) (m Q)))
      fun ab ↦ by rw [hval, hval]),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact hcount.trans_eq (by simp)

/-- **Theorem 5.1**: two different multisets of at most `N` tuples each have equal products at
a uniform challenge `(α, β)` with probability at most `4·N / |E|` (lvm: the probability of the
source, a VCVio uniform draw, restated as the fraction of the challenges in `(Fin 4 → E) × E`). -/
theorem sideProduct_collision {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    (Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} :
        ℝ≥0∞) / (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) ≤
      (4 * N : ℕ) / (Fintype.card E : ℝ≥0∞) := by
  classical
  have hcard : Fintype.card ((Fin 4 → E) × E) = Fintype.card E * Fintype.card E ^ 4 := by
    simp [mul_comm]
  have hdiv : ((4 * N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) =
      ((4 * N * Fintype.card E ^ 4 : ℕ) : ℝ≥0∞) / (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) := by
    rw [hcard, Nat.cast_mul (4 * N), Nat.cast_mul (Fintype.card E),
      ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
        (ENNReal.natCast_ne_top _)]
  rw [hdiv]
  have h := card_sideProduct_collision_le hne hP hQ
  rw [Nat.card_eq_fintype_card (α := E)] at h
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

end
end LeanVM.Protocol
end
-- ===== end of `LvmFingerprint` =====

-- ===== merged from `LvmStack` (GOLF module merge: `LvmStack.lean` is now a stub importing `LvmBus`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Stack.lean` (formal rev 40f877dc) as `LvmStack` for lvm (WP-2).
/-
  LeanVM.Protocol.Stack

  Aligned stacking on leanVM's columns: `K`-columns stacked into one committed column, read back
  block by block, and evaluated at points of `E`.
-/

/-!
# The stack of columns

The generic stacking of `ToCompPoly/Stacking.lean`, specialised to the two fields of leanVM: the
blocks are columns over `K`, the stack is the one committed column, and every evaluation is at a
point of `E` (specification §4.1).

* `Blocks.stackColumn` is the witness stack: block `b` at its window, zero past the last block.
* `Blocks.readColumn` reads block `b` off *any* column of the stack's height, honest or not.
  `Blocks.readColumn_eval` is the stacking identity `q̃(z, sel_b) = P̃_b(z)`, for every `q`.
* `Blocks.layout` packages the lift of a point and that identity as a `Layout`, the reading law
  an `M3Instance` carries; the reader is derived from the lift. A layout is sizes only, so it
  names no table.
  `Layout.comap` renames its columns, which is how a layout indexed by blocks becomes one
  indexed by the columns of an instance.
* `Blocks.stridedLayout` reads the strided slots of one block: the low `k` coordinates of the
  block are frozen to the bits of a column's slot, and a point `z` of the column lifts to
  `(slot bits, z, sel_b)`. `Layout.piecewise` joins two layouts on the sum of their column
  types, which is how the aligned columns and the strided slots become one layout.
* `Blocks.stack_eval_ambient_one` is the one-padded stack over `E` at an arbitrary point, with
  the padding term written as the specification writes it in characteristic two,
  `1 + Σ_b eq(sel_b, ζ_hi)` (§5.4, equation (2)).

Written from the specification, except the strided slots, whose shape is the
Rust's (`crates/pcs/src/stack_open.rs:74-87`, `crates/leanvm_core/src/cpu/mod.rs:718-724` at
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). Which columns the blocks are, and in which order
equal sizes come, is the instance's to say, not this module's.

## Wrong readings excluded

* The reading law quantifies over every column `q`, not only over honest stacks: a knowledge
  extractor reads the blocks off whatever the prover committed.
* The padding term of the one-padded stack is the weight of the *uncovered* part of the cube,
  not the constant `1`; it vanishes when the blocks fill the stack.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval

section

/-! ## Renaming the columns of a layout -/

/-- Reading through a renamed lift is reading the renamed column, cast to its height. -/
private theorem Layout.readWith_comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ}
    (extend : (c : ι) → Vector E (κ c) → Vector E μ) (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c)
    (q : Column μ) (c : ι') :
    Layout.readWith (fun c z ↦ extend (f c) (Vector.cast (h c).symm z)) q c =
      ⟨Vector.cast (congrArg (2 ^ ·) (h c)) (Layout.readWith extend q (f c)).values⟩ := by
  unfold Layout.readWith
  congr 1
  apply Vector.ext
  intro x hx
  simp only [Vector.getElem_cast, Vector.getElem_ofFn, boolVec_cast]
  rfl

/-- A layout read through a renaming of its columns that keeps their heights. -/
def Layout.comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ} (L : Layout μ ι κ)
    (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c) : Layout μ ι' κ' where
  extend := fun c z ↦ L.extend (f c) (Vector.cast (h c).symm z)
  read_eval := fun q c z ↦ by
    rw [Layout.readWith_comap L.extend f h]
    have hz : z = Vector.cast (h c) (Vector.cast (h c).symm z) := by simp
    conv_lhs => rw [hz]
    rw [eval₂Mle_cast, L.read_eval]

/-- The union of two layouts: a left column is read through `L₁`, a right column through
`L₂`. -/
def Layout.piecewise {μ : ℕ} {ι₁ ι₂ : Type} {κ₁ : ι₁ → ℕ} {κ₂ : ι₂ → ℕ} (L₁ : Layout μ ι₁ κ₁)
    (L₂ : Layout μ ι₂ κ₂) : Layout μ (ι₁ ⊕ ι₂) (Sum.elim κ₁ κ₂) where
  extend
    | .inl c => L₁.extend c
    | .inr c => L₂.extend c
  read_eval q
    | .inl c => L₁.read_eval q c
    | .inr c => L₂.read_eval q c

namespace Blocks

/-! ## Stacking and reading columns -/

section Columns

variable (B : Blocks) {μ : ℕ}

/-- The columns stacked on `μ` variables, zero past the last block: the witness stack (§4.1). -/
def stackColumn (t : B.Tables K) (μ : ℕ) : Column μ := ⟨B.stackAt t μ 0⟩

/-- Read block `b` off a column of height `2 ^ μ`: the cells of the block's window. -/
def readColumn (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) : Column (B.size b) :=
  ⟨B.unstack hμ q.values b⟩

/-- The stacking identity, for every column `q`: the block read off `q`, evaluated at `z`, is
`q` evaluated at `(z, sel_b)`. -/
theorem readColumn_eval (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (z : Vector E (B.size b)) :
    eval₂Mle (B.readColumn hμ q b).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (B.extendPoint hμ b z) :=
  (B.unstack_eval₂ (algebraMap K E) hμ q.values b z).symm

/-- The cell a cube point of block `b` lifts to: the point's index plus the block's offset. -/
theorem get_extendPoint (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (y : Fin (2 ^ B.size b)) :
    q.values.get (boolIndex (B.extendPoint hμ b (boolVec y : Vector E (B.size b)))) =
      q.values[y.val + B.offset b]'(by
        have := B.offset_add_pow_le_total b
        have := y.isLt
        omega) := by
  simp only [extendPoint, boolVec_append, boolIndex_cast, boolIndex_boolVec,
    Vector.get_eq_getElem, Fin.val_cast, cubeIndex_val, selector_val]
  congr 1
  exact congrArg (y.val + ·) (Nat.mul_div_cancel' (B.pow_size_dvd_offset b))

/-- Reading through the lift of the aligned blocks is reading the block: the cube point
`(x, sel_b)` is the cell `x + offset_b`. -/
private theorem readWith_extendPoint (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) :
    Layout.readWith (B.extendPoint hμ) q b = B.readColumn hμ q b := by
  unfold Layout.readWith readColumn
  congr 1
  apply Vector.ext
  intro x hx
  rw [B.unstack_getElem hμ q.values b hx]
  simp only [Vector.getElem_ofFn, extendPoint, boolVec_append, boolIndex_cast, boolIndex_boolVec,
    Vector.get_eq_getElem, Fin.val_cast, cubeIndex_val, selector_val]
  congr 1
  exact congrArg (x + ·) (Nat.mul_div_cancel' (B.pow_size_dvd_offset b))

/-- The aligned blocks as a reading law on the committed column. -/
def layout (hμ : B.total ≤ 2 ^ μ) : Layout μ (Fin B.n) B.size where
  extend := B.extendPoint hμ
  read_eval := fun q b z ↦ by rw [readWith_extendPoint]; exact B.readColumn_eval hμ q b z

/-! ## Strided slots of a block -/

/-- Reading through a strided lift: the column at slot `slot c` of block `b` is the low slice
at that slot of the block read off the stack. -/
private theorem readWith_strided (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type}
    {κ : ι → ℕ} (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = k + κ c) (q : Column μ)
    (c : ι) :
    (Layout.readWith (fun c (z : Vector E (κ c)) ↦
        B.extendPoint hμ b (Vector.cast (h c).symm ((boolVec (slot c) : Vector E k) ++ z)))
        q c).values =
      sliceLow (Vector.cast (congrArg (2 ^ ·) (h c)) (B.readColumn hμ q b).values) (slot c) := by
  have key : ∀ y : Fin (2 ^ B.size b),
      q.values.get (boolIndex (B.extendPoint hμ b (boolVec y : Vector E (B.size b)))) =
        (B.readColumn hμ q b).values[y] := by
    intro y
    rw [← B.readWith_extendPoint hμ q b]
    simp [Layout.readWith]
  apply Vector.ext
  intro x hx
  simp only [Layout.readWith, Vector.getElem_ofFn, boolVec_append, boolVec_cast, key, sliceLow,
    Fin.getElem_fin, Vector.getElem_cast, Fin.val_cast]

/-- The strided slots of block `b`, one column per slot: the low `k` coordinates of the block
are frozen to the bits of the column's slot, and a point `z` of the column lifts to the stack's
point `(slot bits, z, selector bits of b)`. The weight of such a claim is nonzero only at the
cells `offset_b + slot + j · 2 ^ k`. -/
def stridedLayout (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type} {κ : ι → ℕ}
    (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = k + κ c) : Layout μ ι κ where
  extend := fun c z ↦
    B.extendPoint hμ b (Vector.cast (h c).symm ((boolVec (slot c) : Vector E k) ++ z))
  read_eval := fun q c z ↦ by
    rw [B.readWith_strided hμ b k slot h q c, ← B.readColumn_eval hμ q b,
      ← eval₂Mle_cast (algebraMap K E) (h c)]
    simp only [Vector.cast_cast, Vector.cast_rfl]
    rw [eval₂Mle, eval₂Mle, sliceLow_map, evalMle_boolVec_append]

/-! ## Slices of a block -/

/-- Reading through a slice lift: the column at slot `slot c` of block `b` is the slice at that
high index of the block read off the stack. -/
private theorem readWith_slice (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type}
    {κ : ι → ℕ} (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = κ c + k) (q : Column μ)
    (c : ι) :
    (Layout.readWith (fun c (z : Vector E (κ c)) ↦
        B.extendPoint hμ b (Vector.cast (h c).symm (z ++ (boolVec (slot c) : Vector E k))))
        q c).values =
      slice (Vector.cast (congrArg (2 ^ ·) (h c)) (B.readColumn hμ q b).values) (slot c) := by
  have key : ∀ y : Fin (2 ^ B.size b),
      q.values.get (boolIndex (B.extendPoint hμ b (boolVec y : Vector E (B.size b)))) =
        (B.readColumn hμ q b).values[y] := by
    intro y
    rw [← B.readWith_extendPoint hμ q b]
    simp [Layout.readWith]
  apply Vector.ext
  intro x hx
  simp only [Layout.readWith, Vector.getElem_ofFn, boolVec_append, boolVec_cast, key, slice,
    Fin.getElem_fin, Vector.getElem_cast, Fin.val_cast]

/-- The slices of block `b`, one column per slot: the high `k` coordinates of the block are
frozen to the bits of the column's slot, and a point `z` of the column lifts to the stack's
point `(z, slot bits, selector bits of b)`. The column is the block's cells
`offset_b + slot · 2 ^ κ + x`: for leanVM, a lane of `q_keccak`
(`crates/verifier/src/layout.rs:559-563`). -/
def sliceLayout (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type} {κ : ι → ℕ}
    (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = κ c + k) : Layout μ ι κ where
  extend := fun c z ↦
    B.extendPoint hμ b (Vector.cast (h c).symm (z ++ (boolVec (slot c) : Vector E k)))
  read_eval := fun q c z ↦ by
    rw [B.readWith_slice hμ b k slot h q c, ← B.readColumn_eval hμ q b,
      ← eval₂Mle_cast (algebraMap K E) (h c)]
    simp only [Vector.cast_cast, Vector.cast_rfl]
    rw [eval₂Mle, eval₂Mle, slice_map, evalMle_append_boolVec]

/-- A slice's cell `x` is the block's cell `x + slot · 2 ^ κ`, at the block's offset. -/
theorem get_sliceLayout (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type}
    {κ : ι → ℕ} (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = κ c + k) (q : Column μ) (c : ι)
    (x : Fin (2 ^ κ c)) :
    q.values.get (boolIndex ((B.sliceLayout hμ b k slot h).extend c (boolVec x))) =
      q.values[(cubeIndex x (slot c)).val + B.offset b]'(by
        have := B.offset_add_pow_le_total b
        have h1 := (cubeIndex x (slot c)).isLt
        have h2 : 2 ^ (κ c + k) = 2 ^ B.size b := by rw [h c]
        omega) := by
  simp only [sliceLayout, boolVec_append, boolVec_cast, get_extendPoint, Fin.val_cast]

end Columns

/-! ## The one-padded stack in characteristic two -/

/-- The one-padded stack of `E`-tables at an arbitrary point (§5.4, equation (2)): the blocks'
weighted evaluations, plus the weight `1 + Σ_b eq(sel_b, ζ_hi)` of the uncovered cells. -/
theorem stack_eval_ambient_one (B : Blocks) (t : B.Tables E) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (ζ : Vector E μ) :
    evalMle (B.stackAt t μ 1) ζ =
      (∑ b : Fin B.n, B.selectorWeight hμ b ζ * evalMle (t b) (B.lowPoint hμ b ζ)) +
        (1 + ∑ b : Fin B.n, B.selectorWeight hμ b ζ) := by
  rw [B.stack_eval_ambient t hμ 1 ζ, one_mul, CharTwo.sub_eq_add]

end Blocks

end
end LeanVM.Protocol
end
-- ===== end of `LvmStack` =====

/-! lvm (WP-2): cut, as ArkLib's typed front (`ToArkLib.Typed.*`): `challengeStep`, `rootsStep`,
`valuesStep`, their completeness `challengeComplete`, `rootsComplete`, `valuesComplete`, the phase
`busPhase` and `busComplete` (typed at `Spine.Slots`' `busSlot`). Kept: every definition and fact
they are built from, the honest steps `challenge_honest`, `roots_honest`, `values_honest`
included. Row polynomials are Mathlib `MvPolynomial`s (see `LvmSpineInstance`). -/

/-!
# The bus phase

Specification §5.2 to §5.4 and §8.3 (`doc/leanvm/body/05-arithmetization.tex`,
`08-end-to-end-protocol.tex` at leanVM `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`), over an
abstract instance `I`.

The bus has three sides: the pushed tuples, the pulled tuples, and the count columns. Each side's
tuples come in *blocks*: a boundary block's `2 ^ κ` tuples, one flush of one table (a tuple per
row), one count column (a cell per row) (`Source`). A block's *leaves* are `β − π_α(t)` for its
tuples `t`, with `π_α` the fingerprint, and a count column's leaves are its cells; on a padding
row of a table (§8.3) a leaf is `φ(x) + 1 − φ(p)` instead, `φ` the executed leaf and `p` the
public padding row, so `1` on an honest one and in general the fingerprint of
`1 − t + t(p)`, a nonzero tuple when the separator is constant (`Conditions.separator`). The
verifier evaluates `(1 − φ(p))·pad_{rows}(z)` itself (`Source.padTerm`, part of
`Source.publicValue`), `pad_n` the extension of `[x ≥ n]` (`padWeight`). Each side's
blocks are stacked largest first at aligned offsets, ties in the order of `sources` (on the
push or pull side, its boundary blocks, then each table's flushes of that side; on the count
side, each table's count columns), and padded with `1` to the depth `μ_bus` of the push side
(`sideLeaves`; `pushLeaves`, `pullLeaves`, `countLeaves`). The product of a side's leaves is the
product of its blocks' leaves (`Blocks.prod_stackAt`), so the push and pull roots agree when the
bus balances, and the count root is nonzero when every count cell is.

The phase (`busPhase`), a typed front component at the slot `busSlot I`:

1. the verifier draws `(α, β)`;
2. the prover sends the roots `(R, R_c)`: one scalar for push and pull, which share their root,
   and the count root; the verifier rejects `R_c = 0`;
3. the grand-product argument `gkr` on the three leaf stacks, read off the stack and `(α, β)`,
   ends at a point `ζ` with one claim per side, `Ṽ_s(ζ) = v_s`;
4. the prover sends the values at `ζ` of the boundary columns (`I.boundaryColumns`), and the
   verifier hands on (`busOut`): the point `ζ_{<τ_max}`, the boundary columns' claims, and per
   side the *forms* and their *total*. By the stacking identity at `ζ` (`leaf_decomposition`,
   equation (2) of §5.4) a side's claim is the sum over its blocks of the selector weight
   `eq(sel_b, ζ_{≥κ_b})` times the block's leaf extension at `ζ_{<κ_b}`, plus the pad's weight.
   The verifier evaluates the boundary blocks' part from the values sent and subtracts it and the
   pad's from `v_s`: the remainder is the total, `rem_s` of §5.4. The tables' blocks are owed as
   forms, one per side and sumcheck table: for a flush block, the weight times `β` against the
   constant row polynomial `1` and the weight times `−eq(α, i)` against coordinate `i`'s flush
   polynomial; for a count column, the weight against the column's variable.

The grand-product argument carries the constraint polynomials of the tables as *riders*, tables
whose extension must vanish at the final point (`riders`): that is how the zerocheck of §5.5 is
paid inside the bus phase (`ζ` is drawn after the stack is committed). One more rider, on no
variable, is zero exactly when the public lines and the Keccak predicate hold of the statement and
the stack (`linesRider`): the predicates the grand-product argument does not touch travel through
it this way.

The phase's side conditions (`Conditions`): the degree bound is at least one (a count column's
form is its variable); a table with a constraint fits in the leaf stacks' depth, so that `ζ` has
a point for it (the verifier reads `ζ` at every variable below the tallest table's height,
`crates/verifier/src/bus.rs:221-230`; its explicit rejection of a shorter `ζ`,
`crates/lean_vm/src/constraints.rs:250-253` at `a386121f`, is removed at `127510d1`); and the pull
and count sides fit in `2 ^ μ_bus`, the push side's depth, which the deployed prover asserts of
its layouts (`crates/leanvm_core/src/leaf.rs:115-130`, called at `:628`; the verifier's own call,
`leaf.rs:875` at `a386121f`, is removed at `127510d1`).

Perfect completeness (`busComplete`), from `Seam.commitHonest` to `Seam.bus`: on a stack
satisfying `M3Holds` with honest padding rows (their leaves `1`), the products of the push and
pull sides agree at every `(α, β)` (balance is a permutation), the count root is nonzero (counts
are nonzero), every rider is zero (constraints vanish, lines and Keccak predicate hold), and at
the end the honest values make every claim true and the forms sum to the totals.

Written from the specification; the layout and its tie order, the count blocks and the order of
the messages are transcribed from `crates/leanvm_core/src/leaf.rs` at the pin (the layout
`:141-148`, the leaves `:179-255`, the decomposition `:381-451`), the verifier
`crates/verifier/src/bus.rs:107-209` (`verify_bus_balance`), the prover's grand product
`crates/leanvm_core/src/gkr.rs:299-418` and its verifier `crates/verifier/src/bus.rs:12-49`.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval
open scoped NNReal

noncomputable section

namespace Bus

variable (I : M3Instance)

/-! ## Blocks of leaves -/

/-- Where a block of leaves comes from: a boundary block, one flush of one table (its index among
the table's flushes), or one count column of one table. -/
inductive Source
  | boundary (b : BoundaryBlock I.toShape)
  | flush (j : Fin I.ntab) (f : Fin (I.flushes j).length)
  | count (j : Fin I.ntab) (c : Fin (I.width j))

variable {I}

/-- A block's log-height: its boundary block's, or its table's. -/
def Source.κ : Source I → ℕ
  | .boundary b => b.κ
  | .flush j _ => I.τ j
  | .count j _ => I.τ j

/-- The sixteen coordinate polynomials of flush `f` of table `j`. -/
abbrev flushPolys (j : Fin I.ntab) (f : Fin (I.flushes j).length) :
    Vector (MvPolynomial (Fin (I.width j)) K) 16 :=
  (I.flushes j)[f].2

/-- The tuple a block contributes at row `x`, read off the stack: the boundary block's
coordinates, or the flush's polynomials on the table's row. A count column's tuple, its cell then
zeros, is the deployed verifier's count block; no definition reads it, since a count leaf is the
cell itself. -/
def Source.tuple (q : Column I.μ) : (src : Source I) → Fin (2 ^ src.κ) → Vector K 16
  | .boundary b, x => b.coords.map fun co ↦ I.coordCell q co x
  | .flush j f, x => (flushPolys j f).map fun P ↦ MvPolynomial.eval (I.row q j x) P
  | .count j c, x => Vector.ofFn fun i ↦ if i.val = 0 then (I.column q ⟨j, c⟩).values.get x else 0

/-- `[x ≥ rows j]`: `1` on a padding row of table `j`, `0` on an executed row. -/
def padInd (j : Fin I.ntab) (x : Fin (2 ^ I.τ j)) : E := if I.rows j ≤ x.val then 1 else 0

/-- The tuple flush `f` of table `j` emits on the table's public padding row. -/
def padTuple (j : Fin I.ntab) (f : Fin (I.flushes j).length) : Vector K 16 :=
  (flushPolys j f).map fun P ↦ MvPolynomial.eval (I.padRow j) P

/-- A block's leaf at row `x` (§5.4, the leaves `L_b`): on an executed row, `φ(x) = β − π_α(t)` for
the row's tuple `t`, or the count cell; on a padding row of a table, `φ(x) + 1 − φ(p)` with `p` the
public padding row, whatever the row holds, so `1` on an honest one. -/
def Source.leaf (α : Fin 4 → E) (β : E) (q : Column I.μ) : (src : Source I) → Fin (2 ^ src.κ) → E
  | .boundary b, x => β - fingerprint α ((Source.boundary b).tuple q x)
  | .flush j f, x => β - fingerprint α ((Source.flush j f).tuple q x) +
    padInd j x * (1 - (β - fingerprint α (padTuple j f)))
  | .count j c, x => ofK ((I.column q ⟨j, c⟩).values.get x) +
    padInd j x * (1 - ofK (I.padRow j c))

variable (I)

/-- The blocks of a side of the bus (`Side.push` or `Side.pull`): the side's boundary blocks in
order, then every table's flushes of that side, table by table, in order. -/
def sideSources (s : Side) : List (Source I) :=
  (I.boundary.filter fun b ↦ decide (b.side = s)).map .boundary ++
    (List.finRange I.ntab).flatMap fun j ↦
      ((List.finRange (I.flushes j).length).filter fun f ↦ decide ((I.flushes j)[f].1 = s)).map
        (.flush j)

/-- The blocks of the count side: every table's count columns, table by table, in order. -/
def countSources : List (Source I) :=
  (List.finRange I.ntab).flatMap fun j ↦ (I.counts j).map (.count j)

/-- The blocks of the three sides: push, pull, count. -/
def sources (k : Fin 3) : List (Source I) :=
  ![sideSources I .push, sideSources I .pull, countSources I] k

/-- The number of leaves of a side, before padding. -/
def leafCount (k : Fin 3) : ℕ := ((sources I k).map fun src ↦ 2 ^ src.κ).sum

/-- The blocks of a side, largest first, ties in the order of `sources` (a stable sort). -/
def sorted (k : Fin 3) : List (Source I) :=
  (sources I k).mergeSort fun a b ↦ decide (b.κ ≤ a.κ)

/-- The sorted blocks are largest first. -/
theorem sorted_antitone (k : Fin 3) :
    Antitone fun b : Fin (sorted I k).length ↦ ((sorted I k)[b]).κ := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hp := List.pairwise_mergeSort (le := fun a b : Source I ↦ decide (b.κ ≤ a.κ))
      (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (sources I k)
    exact of_decide_eq_true (List.pairwise_iff_getElem.mp hp a.val b.val a.isLt b.isLt h)

/-- The aligned layout of a side's blocks. -/
def blocks (k : Fin 3) : Blocks where
  n := (sorted I k).length
  size b := ((sorted I k)[b]).κ
  descending := sorted_antitone I k

/-- A side's blocks' leaves, one table per block. -/
def tables (k : Fin 3) (α : Fin 4 → E) (β : E) (q : Column I.μ) : (blocks I k).Tables E :=
  fun b ↦ Vector.ofFn (((sorted I k)[b]).leaf α β q)

/-- A side's leaf stack: its blocks stacked largest first at aligned offsets, padded with `1`,
on the push side's depth `μ_bus`. -/
def sideLeaves (k : Fin 3) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    CMlPolynomialEval E I.μBus :=
  (blocks I k).stackAt (tables I k α β q) I.μBus 1

/-- The bus phase's side conditions: the degree bound is at least one, a table with a constraint
fits in the leaf stacks' depth, and the pull and count sides fit in it. -/
structure Conditions : Prop where
  /-- A count column's form is its variable, of degree one. -/
  one_le_d : 1 ≤ I.d
  /-- A table with a constraint has a zerocheck point among the coordinates of `ζ`. -/
  constrained : ∀ j, I.constraints j ≠ [] → I.τ j ≤ I.μBus
  /-- The pull side fits in the push side's depth. -/
  pull_fits : leafCount I 1 ≤ 2 ^ I.μBus
  /-- The count side fits in the push side's depth. -/
  count_fits : leafCount I 2 ≤ 2 ^ I.μBus
  /-- A flush's first coordinate, its domain separator, takes one value on every row (§5.1): a
  padding row's leaf is then the fingerprint of a nonzero tuple (Proposition `prop:pad`). -/
  separator : ∀ j (f : Fin (I.flushes j).length) (r r' : Fin (I.width j) → K),
    MvPolynomial.eval r ((flushPolys j f)[0]) = MvPolynomial.eval r' ((flushPolys j f)[0])

end Bus

/-- The push side's leaf stack (§5.3, §5.4). -/
abbrev pushLeaves (I : M3Instance) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 0 α β q

/-- The pull side's leaf stack. -/
abbrev pullLeaves (I : M3Instance) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 1 α β q

/-- The count side's leaf stack: the tables' count columns, padded with `1`. -/
abbrev countLeaves (I : M3Instance) (q : Column I.μ) : CMlPolynomialEval E I.μBus :=
  Bus.sideLeaves I 2 0 0 q

namespace Bus

variable (I : M3Instance)

/-! ## The layouts fit -/

/-- The log-heights of a side's blocks: its boundary blocks', then each table's, once per flush
of that side. -/
theorem sideSources_map_κ (s : Side) :
    (sideSources I s).map Source.κ =
      (I.boundary.filter fun b ↦ decide (b.side = s)).map (·.κ) ++
        (List.finRange I.ntab).flatMap fun j ↦
          List.replicate ((I.flushes j).filter fun f ↦ decide (f.1 = s)).length (I.τ j) := by
  rw [sideSources, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun j _ ↦ ?_
  rw [List.map_map]
  simp only [Function.comp_def, Source.κ, List.map_const']
  congr 1
  conv_rhs => rw [← List.map_getElem_finRange (I.flushes j)]
  rw [List.filter_map, List.length_map]
  rfl

/-- The log-heights of the count side's blocks: each table's, once per count column. -/
theorem countSources_map_κ :
    (countSources I).map Source.κ =
      (List.finRange I.ntab).flatMap fun j ↦ List.replicate (I.counts j).length (I.τ j) := by
  rw [countSources, List.map_flatMap]
  refine List.flatMap_congr fun j _ ↦ ?_
  simp only [List.map_map, Function.comp_def, Source.κ, List.map_const']

/-- A side's layout covers its leaves exactly. -/
theorem blocks_total (k : Fin 3) : (blocks I k).total = leafCount I k := by
  rw [Blocks.total_eq_sum]
  change ∑ b : Fin (sorted I k).length, 2 ^ ((sorted I k)[b.1]).κ = _
  rw [Fin.sum_univ_fun_getElem (sorted I k) fun src ↦ 2 ^ src.κ, leafCount]
  exact ((List.mergeSort_perm _ _).map _).sum_eq

private theorem length_filter_finRange {α : Type} (l : List α) (p : α → Bool) :
    ((List.finRange l.length).filter fun i ↦ p l[i]).length = (l.filter p).length := by
  conv_rhs => rw [← List.map_getElem_finRange l]
  rw [List.filter_map, List.length_map]
  rfl

private theorem sum_flatMap {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- The push side's leaves are the instance's count of push leaves. -/
private theorem leafCount_push : leafCount I 0 = I.pushLeaves := by
  rw [leafCount, M3Instance.pushLeaves]
  change ((sideSources I .push).map _).sum = _
  rw [sideSources, List.map_append, List.sum_append, List.map_map]
  congr 1
  rw [List.map_flatMap, sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun j _ ↦ ?_)
  rw [List.map_map]
  simp only [Function.comp_def, Source.κ, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [length_filter_finRange (I.flushes j) fun f ↦ decide (f.1 = Side.push)]

/-- The push side fits in its own depth. -/
theorem push_fits : (blocks I 0).total ≤ 2 ^ I.μBus := by
  rw [blocks_total, leafCount_push]
  exact Nat.le_pow_clog one_lt_two _

variable {I}

/-- Under the side conditions every side fits in the push side's depth. -/
theorem Conditions.fits (h : Conditions I) (k : Fin 3) : (blocks I k).total ≤ 2 ^ I.μBus := by
  fin_cases k
  · exact push_fits I
  · exact (blocks_total I 1).trans_le h.pull_fits
  · exact (blocks_total I 2).trans_le h.count_fits

/-- A block of a side that fits is no taller than the leaf stacks. -/
private theorem κ_le_of_mem {k : Fin 3} (hfit : leafCount I k ≤ 2 ^ I.μBus) {src : Source I}
    (hs : src ∈ sources I k) : src.κ ≤ I.μBus := by
  have h2 : 2 ^ src.κ ≤ leafCount I k :=
    List.le_sum_of_mem (List.mem_map_of_mem (f := fun src : Source I ↦ 2 ^ src.κ) hs)
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp (h2.trans hfit)

/-- Under the side conditions every block of every side is no taller than the leaf stacks. -/
theorem Conditions.κ_le (h : Conditions I) {k : Fin 3} {src : Source I}
    (hs : src ∈ sources I k) : src.κ ≤ I.μBus :=
  κ_le_of_mem (by rw [← blocks_total]; exact h.fits k) hs

/-- Under the side conditions every sumcheck table is no taller than the leaf stacks: a table
with a constraint by hypothesis, one with a flush or a count column since its block fits. -/
theorem Conditions.τmax_le (h : Conditions I) : I.τmax ≤ I.μBus := by
  refine Finset.sup_le fun j _ ↦ ?_
  obtain ⟨j, hj⟩ := j
  rcases hj with hc | hf | hc
  · exact h.constrained j hc
  · obtain ⟨f, hfm⟩ := List.exists_mem_of_ne_nil _ hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfm
    have hmem (s : Side) (hs : (I.flushes j)[i].1 = s) :
        Source.flush j ⟨i, hi⟩ ∈ sideSources I s := by
      simp only [sideSources, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
        List.mem_finRange, true_and, decide_eq_true_eq]
      exact Or.inr ⟨j, ⟨i, hi⟩, hs, rfl⟩
    cases hside : (I.flushes j)[i].1
    · exact h.κ_le (k := 0) (hmem .push hside)
    · exact h.κ_le (k := 1) (hmem .pull hside)
  · obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc
    have hmem : Source.count j c ∈ sources I 2 := by
      change _ ∈ countSources I
      simp only [countSources, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
      exact ⟨j, c, hcm, rfl⟩
    exact h.κ_le hmem

/-- Under the side conditions every boundary column is no taller than the leaf stacks: it is a
coordinate of a boundary block of the push or pull side. -/
theorem Conditions.κ_le_of_boundaryColumn (h : Conditions I) {c : I.ColumnId}
    (hc : c ∈ I.boundaryColumns) : I.κ c ≤ I.μBus := by
  simp only [M3Instance.boundaryColumns, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_filter, decide_eq_true_eq, List.mem_filterMap] at hc
  obtain ⟨s, hs, b, ⟨hb, rfl⟩, co, -, hco⟩ := hc
  cases co with
  | const _ => cases hco
  | known _ => cases hco
  | committed c' hτ =>
    cases hco
    have hmem (k : Fin 3) (hk : sources I k = sideSources I b.side) :
        Source.boundary b ∈ sources I k := by
      rw [hk]
      simp only [sideSources, List.mem_append, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inl ⟨b, ⟨hb, rfl⟩, rfl⟩
    change I.τ _ ≤ I.μBus
    rw [hτ]
    rcases hs with hs | hs
    · exact h.κ_le (hmem 0 (by rw [hs]; rfl))
    · exact h.κ_le (hmem 1 (by rw [hs]; rfl))

/-! ## The leaves at a point -/

variable (I)

/-- Block `b` of side `k`, in the stacked order. -/
abbrev src (k : Fin 3) (b : Fin (blocks I k).n) : Source I := (sorted I k)[b.1]'b.isLt

variable {I}

/-- The extension at a point of a boundary block of one of its coordinates: a constant is itself,
a known column its extension, a committed column its extension read off the stack. -/
def coordEval (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Vector E κ → E
  | .const c, _ => ofK c
  | .known col, z => eval₂Mle col.values (algebraMap K E) z
  | .committed c h, z => eval₂Mle (I.column q c).values (algebraMap K E) (Vector.cast h.symm z)

/-- The extension at `z` of `[x ≥ n]` on the cube of `z`'s length: `pad_n(z)` (Lemma
`lem:suffix`). -/
def padWeight {m : ℕ} (n : ℕ) (z : Vector E m) : E :=
  evalMle (Vector.ofFn fun x : Fin (2 ^ m) ↦ if n ≤ x.val then (1 : E) else 0) z

/-- The public part of a table block's leaf extension: the padding term
`(1 − φ(p))·pad_{rows}(z)` of equation `eq:pad_leaf`, `φ(p)` the leaf the padding row's tuple
would have. -/
def Source.padTerm (α : Fin 4 → E) (β : E) : (src : Source I) → Vector E src.κ → E
  | .boundary _, _ => 0
  | .flush j f, z => (1 - (β - fingerprint α (padTuple j f))) * padWeight (I.rows j) z
  | .count j c, z => (1 - ofK (I.padRow j c)) * padWeight (I.rows j) z

/-- The extension of a block's leaves at a point of the block, as the verifier writes it:
`β − Σ_i eq(α, i)·c̃_i(z)` with `c̃_i` the extension of coordinate `i`, or a count column's
extension, plus a table block's padding term. -/
def Source.leafEval (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    (src : Source I) → Vector E src.κ → E
  | .boundary b, z =>
    let w := fingerprintWeights α
    β - ∑ i : Fin 16, w[i.val] * coordEval q b.coords[i] z
  | .flush j f, z =>
    let w := fingerprintWeights α
    β - ∑ i : Fin 16, w[i.val] * evalMle (I.virtualTable q j (flushPolys j f)[i]) z +
      (Source.flush j f).padTerm α β z
  | .count j c, z => eval₂Mle (I.column q ⟨j, c⟩).values (algebraMap K E) z +
    (Source.count j c).padTerm α β z

/-- The extension of `a + [x ≥ n]·c` is `ã + c·pad_n`. -/
private theorem evalMle_add_padInd {m : ℕ} (a : Fin (2 ^ m) → E) (n : ℕ) (c : E)
    (z : Vector E m) :
    evalMle (Vector.ofFn fun x ↦ a x + (if n ≤ x.val then (1 : E) else 0) * c) z =
      evalMle (Vector.ofFn a) z + c * padWeight n z := by
  simp only [padWeight, evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_ofFn, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ by ring)

/-- The extension of `β − Σ_i w_i·g_i` is `β − Σ_i w_i·g̃_i`. -/
private theorem evalMle_affine {n : ℕ} (β : E) (w : Fin 16 → E) (g : Fin 16 → Fin (2 ^ n) → E)
    (z : Vector E n) :
    evalMle (Vector.ofFn fun x ↦ β - ∑ i, w i * g i x) z =
      β - ∑ i, w i * evalMle (Vector.ofFn (g i)) z := by
  simp only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_ofFn, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm (f := fun x i ↦ w i * (g i x * (lagrangeBasis z)[x.val]))]
  congr 1
  rw [← Finset.mul_sum]
  have h1 := sumCube_lagrangeBasis z
  simp only [sumCube, Fin.getElem_fin] at h1
  rw [h1, mul_one]

/-- A boundary coordinate's column, lifted to `E`, has the extension `coordEval`. -/
private theorem evalMle_coordCell (q : Column I.μ) {κ : ℕ} (co : Coord I.toShape κ)
    (z : Vector E κ) :
    evalMle (Vector.ofFn fun x ↦ ofK (I.coordCell q co x)) z = coordEval q co z := by
  cases co with
  | const c =>
    rw [show (Vector.ofFn fun x : Fin (2 ^ κ) ↦ ofK (I.coordCell q (.const c) x)) =
      Vector.replicate (2 ^ κ) (ofK c) from Vector.ext fun i hi ↦ by simp [M3Instance.coordCell]]
    exact evalMle_replicate _ z
  | known col =>
    refine congrArg (evalMle · z) (Vector.ext fun i hi ↦ ?_)
    simp [M3Instance.coordCell, CMlPolynomialEval.map, Extension.Ext.algebraMap_eq_ofBase,
      Vector.get_eq_getElem]
  | committed c h =>
    have ht : (Vector.ofFn fun x ↦ ofK (I.coordCell q (.committed c h) x)) =
        Vector.cast (congrArg (2 ^ ·) h)
          (CMlPolynomialEval.map (algebraMap K E) (I.column q c).values) :=
      Vector.ext fun i hi ↦ by
        simp [M3Instance.coordCell, CMlPolynomialEval.map, Extension.Ext.algebraMap_eq_ofBase,
          Vector.get_eq_getElem]
    rw [ht, coordEval, eval₂Mle, ← evalMle_cast h _ (Vector.cast h.symm z), Vector.cast_cast,
      Vector.cast_rfl]

private theorem evalMle_leaf_boundary (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (b : BoundaryBlock I.toShape) (z : Vector E b.κ) :
    evalMle (n := b.κ) (Vector.ofFn ((Source.boundary b).leaf α β q)) z =
      β - ∑ i : Fin 16, (fingerprintWeights α)[i.val] * coordEval q b.coords[i] z := by
  show evalMle (Vector.ofFn fun x : Fin (2 ^ b.κ) ↦
    β - fingerprint α (b.coords.map fun co ↦ I.coordCell q co x)) z = _
  have ht : (Vector.ofFn fun x : Fin (2 ^ b.κ) ↦
      β - fingerprint α (b.coords.map fun co ↦ I.coordCell q co x)) =
      Vector.ofFn fun x ↦
        β - ∑ i : Fin 16, (fingerprintWeights α)[i.val] * ofK (I.coordCell q b.coords[i] x) :=
    congrArg Vector.ofFn (funext fun x ↦ congrArg (β - ·) (Finset.sum_congr rfl fun i _ ↦ by
      rw [Fin.getElem_fin, Vector.getElem_map]; rfl))
  rw [ht, evalMle_affine]
  exact congrArg (β - ·) (Finset.sum_congr rfl fun i _ ↦ by rw [evalMle_coordCell])

private theorem evalMle_leaf_flush (α : Fin 4 → E) (β : E) (q : Column I.μ) (j : Fin I.ntab)
    (f : Fin (I.flushes j).length) (z : Vector E (I.τ j)) :
    evalMle (n := I.τ j) (Vector.ofFn ((Source.flush j f).leaf α β q)) z =
      β - ∑ i : Fin 16,
        (fingerprintWeights α)[i.val] * evalMle (I.virtualTable q j (flushPolys j f)[i]) z +
        (Source.flush j f).padTerm α β z := by
  show evalMle (Vector.ofFn fun x : Fin (2 ^ I.τ j) ↦
    β - fingerprint α ((flushPolys j f).map fun P ↦ MvPolynomial.eval (I.row q j x) P) +
      (if I.rows j ≤ x.val then (1 : E) else 0) * (1 - (β - fingerprint α (padTuple j f)))) z = _
  refine (evalMle_add_padInd _ _ _ z).trans (congrArg (· + _) ?_)
  have ht : (Vector.ofFn fun x : Fin (2 ^ I.τ j) ↦
      β - fingerprint α ((flushPolys j f).map fun P ↦ MvPolynomial.eval (I.row q j x) P)) =
      Vector.ofFn fun x ↦ β - ∑ i : Fin 16,
        (fingerprintWeights α)[i.val] * ofK (MvPolynomial.eval (I.row q j x) (flushPolys j f)[i]) :=
    congrArg Vector.ofFn (funext fun x ↦ congrArg (β - ·) (Finset.sum_congr rfl fun i _ ↦ by
      rw [Fin.getElem_fin, Vector.getElem_map]; rfl))
  rw [ht, evalMle_affine]
  rfl

private theorem evalMle_leaf_count (α : Fin 4 → E) (β : E) (q : Column I.μ) (j : Fin I.ntab)
    (c : Fin (I.width j)) (z : Vector E (I.τ j)) :
    evalMle (n := I.τ j) (Vector.ofFn ((Source.count j c).leaf α β q)) z =
      eval₂Mle (I.column q ⟨j, c⟩).values (algebraMap K E) z +
        (Source.count j c).padTerm α β z := by
  show evalMle (Vector.ofFn fun x : Fin (2 ^ I.τ j) ↦
    ofK ((I.column q ⟨j, c⟩).values.get x) +
      (if I.rows j ≤ x.val then (1 : E) else 0) * (1 - ofK (I.padRow j c))) z = _
  refine (evalMle_add_padInd _ _ _ z).trans (congrArg (· + _) ?_)
  refine congrArg (evalMle · z) (Vector.ext fun i hi ↦ ?_)
  simp [CMlPolynomialEval.map, Extension.Ext.algebraMap_eq_ofBase, Vector.get_eq_getElem]

/-- A block's leaves have the extension `leafEval`. -/
private theorem Source.evalMle_leaf (α : Fin 4 → E) (β : E) (q : Column I.μ) (src : Source I)
    (z : Vector E src.κ) :
    evalMle (Vector.ofFn (src.leaf α β q)) z = src.leafEval α β q z := by
  cases src with
  | boundary b => exact evalMle_leaf_boundary α β q b z
  | flush j f => exact evalMle_leaf_flush α β q j f z
  | count j c => exact evalMle_leaf_count α β q j c z

/-! ## The products of the sides -/

/-- The tuple flush `f` of table `j` emits on row `x`. -/
def flushTuple (q : Column I.μ) (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (x : Fin (2 ^ I.τ j)) : Vector K 16 :=
  (flushPolys j f).map fun P ↦ MvPolynomial.eval (I.row q j x) P

/-- The tuples a block puts on the bus: every row of a boundary block, the executed rows of a
flush; none for a count column, whose leaves are its cells. -/
def Source.busTuples (q : Column I.μ) : Source I → List (Vector K 16)
  | .boundary b => (List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x
  | .flush j f => (I.executed j).map (flushTuple q j f)
  | .count _ _ => []

/-- The padding rows of table `j`, in order. -/
def padRows (j : Fin I.ntab) : List (Fin (2 ^ I.τ j)) :=
  (List.finRange (2 ^ I.τ j)).filter fun x ↦ decide (I.rows j ≤ x.val)

/-- The tuple whose fingerprint is a flush block's padding leaf at row `x`: `1 − t + t(p)` slot by
slot, `t` the row's tuple and `t(p)` the public padding row's (Proposition `prop:pad`). -/
def padDiff (q : Column I.μ) (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (x : Fin (2 ^ I.τ j)) : Vector K 16 :=
  Vector.ofFn fun i ↦ 1 - (flushTuple q j f x)[i] + (padTuple j f)[i]

/-- A flush block's padding leaves, as the tuples they fingerprint. -/
def Source.padTuples (q : Column I.μ) : Source I → List (Vector K 16)
  | .flush j f => (padRows j).map (padDiff q j f)
  | _ => []

variable (I)

/-- The tuples of a push or pull side, block by block. -/
def sideTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (sideSources I s).flatMap (·.busTuples q)

/-- The padding tuples of a push or pull side, block by block. -/
def sidePadTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (sideSources I s).flatMap (·.padTuples q)

variable {I}

private theorem prod_flatMap {M α β : Type} [CommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).prod = (l.map fun a ↦ ((f a).map g).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

/-- A product over a list splits along a predicate. -/
private theorem prod_map_filter {M α : Type} [CommMonoid M] (l : List α) (p : α → Bool)
    (g : α → M) :
    (l.map g).prod = ((l.filter p).map g).prod * ((l.filter fun a ↦ !p a).map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> simp [hp, ih] <;> ac_rfl

/-- The padding rows are the rows that are not executed. -/
private theorem padRows_eq (j : Fin I.ntab) :
    padRows j = (List.finRange (2 ^ I.τ j)).filter fun x ↦ !decide (x.val < I.rows j) :=
  List.filter_congr fun x _ ↦ by
    by_cases h : x.val < I.rows j
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.le_of_not_lt h]

/-- The executed and padding rows of a table, together. -/
private theorem prod_rows {M : Type} [CommMonoid M] (j : Fin I.ntab) (g : Fin (2 ^ I.τ j) → M) :
    ∏ x, g x = ((I.executed j).map g).prod * ((padRows j).map g).prod := by
  rw [Fin.prod_univ_def, prod_map_filter _ fun x ↦ decide (x.val < I.rows j), padRows_eq]
  rfl

/-- A table has as many rows as executed and padding rows. -/
private theorem length_rows (j : Fin I.ntab) :
    (I.executed j).length + (padRows j).length = 2 ^ I.τ j := by
  have h := List.length_eq_length_filter_add (l := List.finRange (2 ^ I.τ j))
    (fun x ↦ decide (x.val < I.rows j))
  rw [List.length_finRange] at h
  rw [padRows_eq]
  exact h.symm

/-- A side's tuples, block by block, are its boundary tuples followed by its flushes'. -/
private theorem sideTuples_eq (q : Column I.μ) (s : Side) :
    sideTuples I q s = I.boundaryTuples q s ++ I.flushTuples q s := by
  rw [sideTuples, sideSources, List.flatMap_append, List.flatMap_map, List.flatMap_assoc]
  congr 1
  refine congrArg (List.flatMap · (List.finRange I.ntab)) (funext fun j ↦ ?_)
  conv_rhs => rw [← List.map_getElem_finRange (I.flushes j)]
  rw [List.flatMap_map, List.filter_map, List.flatMap_map]
  rfl

/-- The tuples of a side's blocks are the side's tuples of the instance, in another order. -/
theorem sideTuples_perm (q : Column I.μ) (s : Side) : (sideTuples I q s).Perm (I.tuples q s) := by
  rw [sideTuples_eq, M3Instance.tuples]
  exact List.perm_append_comm

/-- The product of a side's leaf stack is the product, block by block, of its blocks' leaves:
the pad is `1`. -/
theorem prod_sideLeaves (k : Fin 3) (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (hfit : (blocks I k).total ≤ 2 ^ I.μBus) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I k α β q)[x] =
      ((sources I k).map fun src ↦ ∏ y, src.leaf α β q y).prod := by
  rw [sideLeaves, Blocks.prod_stackAt _ _ hfit, one_pow, mul_one,
    ← ((List.mergeSort_perm (sources I k) _).map _).prod_eq,
    ← Fin.prod_univ_fun_getElem]
  exact Finset.prod_congr rfl fun b _ ↦ Finset.prod_congr rfl fun y _ ↦ Vector.getElem_ofFn ..

private theorem prod_leaf_boundary (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (b : BoundaryBlock I.toShape) :
    ∏ y : Fin (2 ^ b.κ), (β - fingerprint α (b.coords.map fun co ↦ I.coordCell q co y)) =
      (((List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x).map
        fun t ↦ β - fingerprint α t).prod * (([] : List (Vector K 16)).map (fingerprint α)).prod := by
  rw [Fin.prod_univ_def, List.map_map, List.map_nil, List.prod_nil, mul_one]
  rfl

private theorem prod_leaf_flush (α : Fin 4 → E) (β : E) (q : Column I.μ) (j : Fin I.ntab)
    (f : Fin (I.flushes j).length) :
    ∏ y : Fin (2 ^ I.τ j), (β - fingerprint α (flushTuple q j f y) +
        padInd j y * (1 - (β - fingerprint α (padTuple j f)))) =
      (((I.executed j).map (flushTuple q j f)).map fun t ↦ β - fingerprint α t).prod *
        (((padRows j).map (padDiff q j f)).map (fingerprint α)).prod := by
  rw [prod_rows, List.map_map, List.map_map]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg List.prod (List.map_congr_left fun x hx ↦ ?_)
    have hx : x.val < I.rows j := of_decide_eq_true (List.mem_filter.mp hx).2
    simp [padInd, Nat.not_le.mpr hx]
  · refine congrArg List.prod (List.map_congr_left fun x hx ↦ ?_)
    have hx : I.rows j ≤ x.val := of_decide_eq_true (List.mem_filter.mp hx).2
    simp only [Function.comp_apply, padDiff, fingerprint_one_sub_add, padInd, hx, ite_true,
      one_mul]
    ring

/-- A block of a push or pull side multiplies `β − π_α(t)` over its tuples on the bus and the
fingerprints of its padding tuples. -/
private theorem prod_leaf_of_mem_sideSources {s : Side} {src : Source I}
    (hs : src ∈ sideSources I s) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    ∏ y, src.leaf α β q y = ((src.busTuples q).map fun t ↦ β - fingerprint α t).prod *
      ((src.padTuples q).map (fingerprint α)).prod := by
  cases src with
  | boundary b => exact prod_leaf_boundary α β q b
  | flush j f => exact prod_leaf_flush α β q j f
  | count j c => simp [sideSources] at hs

/-- The product of a push or pull side's leaves is the side's product at `(α, β)` (§5.2) times
the product of its padding leaves (Proposition `prop:pad`). -/
theorem prod_sideLeaves_eq {k : Fin 3} {s : Side} (hk : sources I k = sideSources I s)
    (α : Fin 4 → E) (β : E) (q : Column I.μ) (hfit : (blocks I k).total ≤ 2 ^ I.μBus) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I k α β q)[x] =
      sideProduct α β (I.tuples q s) * padProduct α (sidePadTuples I q s) := by
  rw [prod_sideLeaves k α β q hfit, hk, sideProduct,
    ← Multiset.coe_eq_coe.mpr (sideTuples_perm q s),
    Multiset.map_coe, Multiset.prod_coe, sideTuples, prod_flatMap, padProduct, sidePadTuples,
    Multiset.map_coe, Multiset.prod_coe, prod_flatMap, ← List.prod_map_mul]
  exact congrArg List.prod (List.map_congr_left fun src hs ↦
    prod_leaf_of_mem_sideSources hs α β q)

/-- The product of the push side's leaves. -/
theorem prod_pushLeaves (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    ∏ x : Fin (2 ^ I.μBus), (pushLeaves I α β q)[x] =
      sideProduct α β (I.tuples q .push) * padProduct α (sidePadTuples I q .push) :=
  prod_sideLeaves_eq rfl α β q (push_fits I)

/-- The product of the pull side's leaves. -/
theorem prod_pullLeaves (h : Conditions I) (α : Fin 4 → E) (β : E) (q : Column I.μ) :
    ∏ x : Fin (2 ^ I.μBus), (pullLeaves I α β q)[x] =
      sideProduct α β (I.tuples q .pull) * padProduct α (sidePadTuples I q .pull) :=
  prod_sideLeaves_eq rfl α β q (h.fits 1)

/-- With honest padding rows, every padding leaf is `1`. -/
theorem padProduct_of_honest {q : Column I.μ} (hp : I.PaddingHonest q) (α : Fin 4 → E)
    (s : Side) : padProduct α (sidePadTuples I q s) = 1 := by
  rw [padProduct, sidePadTuples, Multiset.map_coe, Multiset.prod_coe]
  refine List.prod_eq_one fun e he ↦ ?_
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
  obtain ⟨src, -, hu⟩ := List.mem_flatMap.mp hu
  cases src with
  | flush j f =>
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    have hrow := hp j x (of_decide_eq_true (List.mem_filter.mp hx).2)
    rw [padDiff, fingerprint_one_sub_add]
    simp only [flushTuple, hrow, padTuple]
    ring
  | boundary b => cases hu
  | count j c => cases hu

/-- A padding tuple is nonzero: its first slot, where both tuples hold the same separator, is
`1`. -/
theorem padTuple_ne_zero (h : Conditions I) {q : Column I.μ} {s : Side} {u : Vector K 16}
    (hu : u ∈ sidePadTuples I q s) : ∃ i : Fin 16, u[i] ≠ 0 := by
  obtain ⟨src, -, hu⟩ := List.mem_flatMap.mp hu
  cases src with
  | flush j f =>
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hu
    refine ⟨0, ?_⟩
    simp only [padDiff, Fin.getElem_fin, Vector.getElem_ofFn, flushTuple, padTuple,
      Vector.getElem_map]
    rw [show MvPolynomial.eval (I.row q j x) ((flushPolys j f)[(0 : Fin 16).val]) =
      MvPolynomial.eval (I.padRow j) ((flushPolys j f)[(0 : Fin 16).val]) from
        h.separator j f _ _]
    simp
  | boundary b => cases hu
  | count j c => cases hu

/-- A push or pull side has as many tuples and padding tuples as leaves. -/
theorem length_side {k : Fin 3} {s : Side} (hk : sources I k = sideSources I s)
    (q : Column I.μ) :
    (sidePadTuples I q s).length + (I.tuples q s).length = leafCount I k := by
  rw [← (sideTuples_perm q s).length_eq, sidePadTuples, sideTuples, List.length_flatMap,
    List.length_flatMap, ← List.sum_map_add, leafCount, hk]
  refine congrArg List.sum (List.map_congr_left fun src hs ↦ ?_)
  cases src with
  | boundary b =>
    simp only [Source.padTuples, Source.busTuples, List.length_map, List.length_nil, zero_add,
      List.length_finRange]
    rfl
  | flush j f =>
    simp only [Source.padTuples, Source.busTuples, List.length_map]
    rw [add_comm]
    exact length_rows j
  | count j c => simp [sideSources] at hs

/-- The count side's product is zero when an executed count cell is (§6.2): a nonzero count root
makes every executed count cell nonzero. -/
theorem countsNonzero_of_prod (h : Conditions I) (α : Fin 4 → E) (β : E) (q : Column I.μ)
    (hnz : ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 2 α β q)[x] ≠ 0) : I.CountsNonzero q := by
  rw [prod_sideLeaves 2 α β q (h.fits 2)] at hnz
  intro j c hc x hx h0
  refine hnz (List.prod_eq_zero (List.mem_map.mpr ⟨.count j c, ?_,
    Finset.prod_eq_zero (i := x) (Finset.mem_univ _) ?_⟩))
  · change _ ∈ countSources I
    simp only [countSources, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨j, c, hc, rfl⟩
  · change ofK ((I.column q ⟨j, c⟩).values.get x) + padInd j x * (1 - ofK (I.padRow j c)) = 0
    have hi : padInd j x = 0 := by simp [padInd, Nat.not_le.mpr hx]
    rw [h0, hi, zero_mul, add_zero]
    exact _root_.map_zero (algebraMap K E)

/-- With honest padding rows and nonzero executed counts, the count side's product is nonzero. -/
theorem prod_countLeaves_ne_zero (h : Conditions I) (α : Fin 4 → E) (β : E) {q : Column I.μ}
    (hp : I.PaddingHonest q) (hn : I.CountsNonzero q) :
    ∏ x : Fin (2 ^ I.μBus), (sideLeaves I 2 α β q)[x] ≠ 0 := by
  rw [prod_sideLeaves 2 α β q (h.fits 2)]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨src, hs, h0⟩ := List.mem_map.mp h0
  change src ∈ countSources I at hs
  simp only [countSources, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
  obtain ⟨j, c, hc, rfl⟩ := hs
  obtain ⟨x, -, hx⟩ := Finset.prod_eq_zero_iff.mp h0
  change ofK ((I.column q ⟨j, c⟩).values.get x) + padInd j x * (1 - ofK (I.padRow j c)) = 0
    at hx
  by_cases hr : I.rows j ≤ x.val
  · have hcell : (I.column q ⟨j, c⟩).values.get x = I.padRow j c :=
      congrFun (hp j x hr) c
    have hi : padInd j x = 1 := by simp [padInd, hr]
    rw [hcell, hi, one_mul, add_sub_cancel] at hx
    exact one_ne_zero hx
  · have hi : padInd j x = 0 := by simp [padInd, hr]
    rw [hi, zero_mul, add_zero] at hx
    exact hn j c hc x (Nat.not_le.mp hr)
      ((map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp hx)

/-! ## Riders -/

variable (I)

/-- The constraints of the tables that fit in the leaf stacks' depth, as riders: each its
virtual table, which must vanish at the final point. -/
def constraintRiders (q : Column I.μ) : List (Σ τ : Fin (I.μBus + 1), CMlPolynomialEval E τ) :=
  (List.finRange I.ntab).flatMap fun j ↦
    if hj : I.τ j ≤ I.μBus then
      (I.constraints j).map fun C ↦ ⟨⟨I.τ j, Nat.lt_succ_of_le hj⟩, I.virtualTable q j C⟩
    else []

/-- The public lines and the Keccak predicate as a rider on no variable: `0` exactly when they
hold. -/
def linesRider (input : I.Stmt) (q : Column I.μ) : Σ τ : Fin (I.μBus + 1), CMlPolynomialEval E τ :=
  ⟨⟨0, Nat.succ_pos _⟩, #v[if I.PublicLinesHold input q ∧ I.aux q then 0 else 1]⟩

/-- The public data of the grand-product argument: the statement and the fingerprint challenges
`(α, β)`. -/
abbrev Data : Type := I.Stmt × ((Fin 4 → E) × E)

/-- The leaves of the three trees, read off the stack at the challenges: push, pull, count. -/
def leaves (x : Data I) (o : ∀ i, TheOracle I i) : Fin 3 → CMlPolynomialEval E I.μBus :=
  fun k ↦ sideLeaves I k x.2.1 x.2.2 (theStack o)

/-- The riders: the constraints, and the public lines with the Keccak predicate. -/
def riders (x : Data I) (o : ∀ i, TheOracle I i) :
    List (Σ τ : Fin (I.μBus + 1), CMlPolynomialEval E τ) :=
  constraintRiders I (theStack o) ++ [linesRider I x.1 (theStack o)]

variable {I}

/-- A constraint's virtual table is zero exactly when the constraint vanishes on every row. -/
private theorem virtualTable_zero_iff (q : Column I.μ) (j : Fin I.ntab)
    (C : MvPolynomial (Fin (I.width j)) K) :
    (∀ x : Fin (2 ^ I.τ j), (I.virtualTable q j C)[x] = 0) ↔ ∀ x, MvPolynomial.eval (I.row q j x) C = 0 := by
  refine forall_congr' fun x ↦ ?_
  simp only [M3Instance.virtualTable, Fin.getElem_fin, Vector.getElem_ofFn]
  exact map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective

/-- The lines' rider is zero exactly when the public lines and the Keccak predicate hold. -/
private theorem linesRider_zero_iff (input : I.Stmt) (q : Column I.μ) :
    (∀ i : Fin (2 ^ ((linesRider I input q).1 : ℕ)), (linesRider I input q).2[i] = 0) ↔
      I.PublicLinesHold input q ∧ I.aux q := by
  by_cases hl : I.PublicLinesHold input q ∧ I.aux q
  · refine iff_of_true (fun i ↦ ?_) hl
    obtain ⟨i, hi⟩ := i
    have hi0 : i = 0 := by simpa [linesRider] using hi
    subst hi0
    simp only [linesRider, hl]
    rfl
  · refine iff_of_false (fun h0 ↦ ?_) hl
    have := h0 ⟨0, Nat.two_pow_pos _⟩
    simp only [linesRider, hl, ite_false] at this
    exact one_ne_zero this

/-- The lines' rider is its one value at any point. -/
private theorem evalMle_linesRider (input : I.Stmt) (q : Column I.μ) (ζ : Vector E I.μBus) :
    evalMle (linesRider I input q).2 (Gkr.lowPoint ζ (linesRider I input q).1) =
      if I.PublicLinesHold input q ∧ I.aux q then 0 else 1 :=
  rfl

/-- Every rider is zero exactly when the constraints vanish, the public lines hold and the
Keccak predicate holds. -/
theorem ridersZero_iff (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) :
    Gkr.RidersZero I.μBus (riders I) x o ↔
      I.ConstraintsVanish (theStack o) ∧ I.PublicLinesHold x.1 (theStack o) ∧
        I.aux (theStack o) := by
  simp only [Gkr.RidersZero, riders, List.mem_append, List.mem_singleton, or_imp, forall_and,
    forall_eq]
  rw [linesRider_zero_iff]
  refine and_congr ⟨fun hz j C hC ↦ ?_, fun hc r hr ↦ ?_⟩ Iff.rfl
  · have hj : I.τ j ≤ I.μBus := h.constrained j (List.ne_nil_of_mem hC)
    refine (virtualTable_zero_iff _ j C).mp fun y ↦
      hz ⟨⟨I.τ j, Nat.lt_succ_of_le hj⟩, I.virtualTable (theStack o) j C⟩ ?_ y
    simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨j, by rw [dite_eq_left hj]; exact List.mem_map_of_mem hC⟩
  · simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and] at hr
    obtain ⟨j, hr⟩ := hr
    split at hr
    · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hr
      exact (virtualTable_zero_iff _ j C).mpr (hc j C hC)
    · cases hr

/-- Every rider vanishes at the low coordinates of a point exactly when every constraint of a
table that fits does, and the public lines and the Keccak predicate hold. -/
theorem riders_vanish_iff (x : Data I) (o : ∀ i, TheOracle I i) (ζ : Vector E I.μBus) :
    (∀ r ∈ riders I x o, evalMle r.2 (Gkr.lowPoint ζ r.1) = 0) ↔
      (∀ j (hj : I.τ j ≤ I.μBus), ∀ C ∈ I.constraints j,
        evalMle (I.virtualTable (theStack o) j C) (Gkr.lowPoint ζ ⟨I.τ j, Nat.lt_succ_of_le hj⟩) =
          0) ∧ I.PublicLinesHold x.1 (theStack o) ∧ I.aux (theStack o) := by
  simp only [riders, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  rw [evalMle_linesRider]
  refine and_congr ⟨fun h j hj C hC ↦
    h ⟨⟨I.τ j, Nat.lt_succ_of_le hj⟩, I.virtualTable (theStack o) j C⟩ ?_, fun h r hr ↦ ?_⟩ ?_
  · simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨j, by rw [dite_eq_left hj]; exact List.mem_map_of_mem hC⟩
  · simp only [constraintRiders, List.mem_flatMap, List.mem_finRange, true_and] at hr
    obtain ⟨j, hr⟩ := hr
    split at hr
    · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hr
      exact h j ‹_› C hC
    · cases hr
  · by_cases hl : I.PublicLinesHold x.1 (theStack o) ∧ I.aux (theStack o)
    · simp [hl]
    · simp [hl]

variable (I)

/-! ## The verifier's last step -/

variable {I}

/-- The value sent for a committed boundary column: the message's entry at the column's place
among the boundary columns. -/
def valueOf (vals : Vector E I.busClaims) (c : I.ColumnId) : E :=
  match I.boundaryColumns.finIdxOf? c with
  | some i => vals[i]
  | none => 0

/-- A boundary coordinate's value as the verifier has it at a point: a constant, a known column's
extension, or the value sent for a committed column. -/
def coordValue (vals : Vector E I.busClaims) {κ : ℕ} : Coord I.toShape κ → Vector E κ → E
  | .const c, _ => ofK c
  | .known col, z => eval₂Mle col.values (algebraMap K E) z
  | .committed c _, _ => valueOf vals c

/-- The part of a block the verifier evaluates itself, from the values sent: a boundary block's leaf
extension, a table block's padding term (`padding_rows`, `crates/verifier/src/bus.rs:187-200`). -/
def Source.publicValue (α : Fin 4 → E) (β : E) (vals : Vector E I.busClaims) :
    (src : Source I) → Vector E src.κ → E
  | .boundary b, z =>
    let w := fingerprintWeights α
    β - ∑ i : Fin 16, w[i.val] * coordValue vals b.coords[i] z
  | .flush j f, z => (Source.flush j f).padTerm α β z
  | .count j c, z => (Source.count j c).padTerm α β z

/-- The constant row polynomial `1`. -/
noncomputable def oneRow (j : Fin I.ntab) : I.RowPoly j :=
  ⟨1, by rw [MvPolynomial.totalDegree_one]; omega⟩

/-- A flush block's terms on its table, at the block's weight `w`: `w·β` against `1`, and
`−w·eq(α, i)` against coordinate `i`'s polynomial. -/
def flushForm (j : Fin I.ntab) (f : Fin (I.flushes j).length) (w : E) (α : Fin 4 → E) (β : E) :
    I.Form j :=
  let tw := fingerprintWeights α
  (w * β, oneRow j) :: (List.finRange 16).map fun i ↦ (-(w * tw[i.val]),
    ⟨(flushPolys j f)[i], by
      simpa [flushPolys, Vector.get_eq_getElem] using
        I.flushes_degree j _ (List.getElem_mem f.isLt) i⟩)

/-- A count column's term on its table, at the block's weight `w`: `w` against the column's
variable. -/
def countForm (hd : 1 ≤ I.d) (j : Fin I.ntab) (c : Fin (I.width j)) (w : E) : I.Form j :=
  [(w, ⟨MvPolynomial.X c, by
    rw [MvPolynomial.totalDegree_X]
    exact hd⟩)]

/-- A block's terms on table `j`: its flush's or count column's if it is table `j`'s, none
otherwise. -/
def Source.form (hd : 1 ≤ I.d) (w : E) (α : Fin 4 → E) (β : E) (j : Fin I.ntab) :
    Source I → I.Form j
  | .boundary _ => []
  | .flush j' f => if h : j' = j then h ▸ flushForm j' f w α β else []
  | .count j' c => if h : j' = j then h ▸ countForm hd j' c w else []

/-- Block `b`'s selector weight at `ζ`: `eq(sel_b, ζ_{≥κ_b})`. -/
abbrev weight (h : Conditions I) (k : Fin 3) (b : Fin (blocks I k).n) (ζ : Vector E I.μBus) :
    E :=
  (blocks I k).selectorWeight (h.fits k) b ζ

/-- Block `b`'s point inside `ζ`: `ζ_{<κ_b}`. -/
abbrev lowAt (h : Conditions I) (k : Fin 3) (b : Fin (blocks I k).n) (ζ : Vector E I.μBus) :
    Vector E (src I k b).κ :=
  (blocks I k).lowPoint (h.fits k) b ζ

/-- Side `k`'s forms, per sumcheck table: its tables' blocks' terms. -/
def forms (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E) (ζ : Vector E I.μBus)
    (j : I.SumcheckTables) : I.Form j.1 :=
  (List.finRange (blocks I k).n).flatMap fun b ↦
    (src I k b).form h.one_le_d (weight h k b ζ) α β j.1

/-- Side `k`'s total: its leaf claim `v`, less its blocks' public part (the boundary blocks',
evaluated from the values sent, and the table blocks' padding terms), and the pad's weight
`1 + Σ_b eq(sel_b, ζ_{≥κ_b})`. -/
def total (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E) (ζ : Vector E I.μBus) (v : E)
    (vals : Vector E I.busClaims) : E :=
  v - ((∑ b, weight h k b ζ * (src I k b).publicValue α β vals (lowAt h k b ζ)) +
    (1 + ∑ b, weight h k b ζ))

/-- The table sumcheck's point: `ζ_{<τ_max}`. -/
def point (h : Conditions I) (ζ : Vector E I.μBus) : Vector E I.τmax :=
  Gkr.lowPoint ζ ⟨I.τmax, Nat.lt_succ_of_le h.τmax_le⟩

/-- The point of boundary column `i`'s claim: `ζ_{<κ}`, `κ` the column's log-height. -/
def columnPoint (h : Conditions I) (ζ : Vector E I.μBus) (i : Fin I.busClaims) :
    Vector E (I.κ I.boundaryColumns[i]) :=
  Gkr.lowPoint ζ ⟨_, Nat.lt_succ_of_le (h.κ_le_of_boundaryColumn (List.getElem_mem i.isLt))⟩

/-- What the bus phase hands on, from the grand-product argument's last statement (the
statement, `(α, β)`, `ζ` and the three leaf claims) and the values sent. -/
def busOut (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (vals : Vector E I.busClaims) : BusOut I where
  point := point h ℓ.2.1
  forms k j := forms h k ℓ.1.2.1 ℓ.1.2.2 ℓ.2.1 j
  totals k := total h k ℓ.1.2.1 ℓ.1.2.2 ℓ.2.1 (ℓ.2.2 k) vals
  columns := Vector.ofFn fun i ↦ ⟨I.boundaryColumns[i], columnPoint h ℓ.2.1 i, vals[i]⟩

/-- The honest prover's values: each boundary column's extension at its point. -/
def honestValues (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus) :
    Vector E I.busClaims :=
  Vector.ofFn fun i ↦ eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E)
    (columnPoint h ζ i)

/-! ## The phase's steps -/

variable (I)

/-- The honest roots: the push side's product, which is the pull side's on a balanced bus, and
the count side's. -/
def rootsHonest (p : (Data I × ∀ i, TheOracle I i) × Unit) : E × E :=
  (∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 0)[x],
    ∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 2)[x])

end Bus

open Bus in
/-- **The leaves at a point** (§5.4, equation (2)): a side's leaf stack at `ζ` is the sum over
its blocks of the selector weight `eq(sel_b, ζ_{≥κ_b})` times the block's leaf extension at
`ζ_{<κ_b}`, plus the pad's weight `1 + Σ_b eq(sel_b, ζ_{≥κ_b})`. -/
theorem leaf_decomposition {I : M3Instance} (h : Conditions I) (k : Fin 3) (α : Fin 4 → E)
    (β : E) (q : Column I.μ) (ζ : Vector E I.μBus) :
    evalMle (sideLeaves I k α β q) ζ =
      (∑ b, (blocks I k).selectorWeight (h.fits k) b ζ *
        (src I k b).leafEval α β q ((blocks I k).lowPoint (h.fits k) b ζ)) +
      (1 + ∑ b, (blocks I k).selectorWeight (h.fits k) b ζ) := by
  rw [sideLeaves, Blocks.stack_eval_ambient_one _ _ (h.fits k)]
  refine congrArg (· + _) (Finset.sum_congr rfl fun b _ ↦ ?_)
  exact congrArg _ (Source.evalMle_leaf α β q (src I k b) _)

namespace Bus

variable {I : M3Instance}

/-! ## Points inside `ζ` -/

/-- Block `b`'s point inside `ζ` is `ζ`'s first `κ_b` coordinates. -/
private theorem lowAt_eq (h : Conditions I) (k : Fin 3) (b : Fin (blocks I k).n)
    (ζ : Vector E I.μBus) :
    lowAt h k b ζ = Gkr.lowPoint ζ
      ⟨(src I k b).κ, Nat.lt_succ_of_le ((blocks I k).size_le (h.fits k) b)⟩ := by
  apply Vector.ext
  intro i hi
  simp only [lowAt, Blocks.lowPoint, lowVec, Gkr.lowPoint, Vector.getElem_cast,
    Vector.getElem_ofFn]
  erw [Vector.getElem_ofFn]

/-- A sumcheck table's point inside the table sumcheck's point is `ζ`'s first `τ_j`
coordinates. -/
theorem lowPoint_point (h : Conditions I) (ζ : Vector E I.μBus) (j : I.SumcheckTables) :
    I.lowPoint (point h ζ) j =
      Gkr.lowPoint ζ ⟨I.τ j.1, Nat.lt_succ_of_le ((I.τ_le_τmax j).trans h.τmax_le)⟩ := by
  apply Vector.ext
  intro i hi
  simp only [M3Instance.lowPoint, point, Gkr.lowPoint, Vector.getElem_cast, Vector.getElem_take,
    Vector.getElem_ofFn]

/-! ## The values sent and the boundary blocks -/

/-- A column's extension, read at an equal column. -/
private theorem eval_column_congr (q : Column I.μ) {c c' : I.ColumnId} (e : c = c')
    (z : Vector E (I.κ c)) :
    eval₂Mle (I.column q c).values (algebraMap K E) z =
      eval₂Mle (I.column q c').values (algebraMap K E) (Vector.cast (congrArg I.κ e) z) := by
  subst e
  rfl

/-- With the true values, the verifier's value of a boundary coordinate is its extension. -/
private theorem coordValue_eq (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus)
    (vals : Vector E I.busClaims)
    (hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i))
    {κ : ℕ} (hκ : κ < I.μBus + 1) (co : Coord I.toShape κ)
    (hco : ∀ c, co.committed? = some c → c ∈ I.boundaryColumns) :
    coordValue vals co (Gkr.lowPoint ζ ⟨κ, hκ⟩) = coordEval q co (Gkr.lowPoint ζ ⟨κ, hκ⟩) := by
  cases co with
  | const c => rfl
  | known col => rfl
  | committed c hc =>
    have hmem := hco c rfl
    obtain ⟨i, hi⟩ : ∃ i, I.boundaryColumns.finIdxOf? c = some i := by
      cases hf : I.boundaryColumns.finIdxOf? c with
      | none => exact absurd hmem (List.finIdxOf?_eq_none_iff.mp hf)
      | some i => exact ⟨i, rfl⟩
    have hci : I.boundaryColumns[i] = c := (List.finIdxOf?_eq_some_iff.mp hi).1
    simp only [coordValue, valueOf, hi, coordEval]
    rw [hvals i, columnPoint, eval_column_congr q hci]
    congr 1
    apply Vector.ext
    intro n hn
    simp only [Vector.getElem_cast, Gkr.lowPoint]
    erw [Vector.getElem_ofFn, Vector.getElem_ofFn]

/-- A boundary block of a side is one of the instance's, of the push or pull side. -/
private theorem mem_boundary_of_mem {k : Fin 3} {b : BoundaryBlock I.toShape}
    (hs : Source.boundary b ∈ sources I k) :
    b ∈ I.boundary ∧ (b.side = .push ∨ b.side = .pull) := by
  fin_cases k <;>
    simp [sources, sideSources, countSources, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_flatMap] at hs ⊢ <;> tauto

/-- A committed coordinate of a boundary block of a side is a boundary column. -/
private theorem mem_boundaryColumns_of_mem {k : Fin 3} {b : BoundaryBlock I.toShape}
    (hs : Source.boundary b ∈ sources I k) (i : Fin 16) (c : I.ColumnId)
    (hc : (b.coords[i]).committed? = some c) : c ∈ I.boundaryColumns := by
  obtain ⟨hb, hside⟩ := mem_boundary_of_mem hs
  simp only [M3Instance.boundaryColumns, List.mem_eraseDups, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_filter, decide_eq_true_eq, List.mem_filterMap]
  exact ⟨b.side, by tauto, b, ⟨hb, rfl⟩, b.coords[i],
    Vector.mem_toList_iff.mpr (Vector.getElem_mem _), hc⟩

/-- A count column of a side is one of its table's count columns. -/
private theorem mem_counts_of_mem {k : Fin 3} {j : Fin I.ntab} {c : Fin (I.width j)}
    (hs : Source.count j c ∈ sources I k) : c ∈ I.counts j := by
  fin_cases k <;>
    simp [sources, sideSources, countSources, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_flatMap] at hs
  obtain ⟨j', c', hc', rfl, he⟩ := hs
  cases he
  exact hc'

/-! ## The forms -/

private theorem sum_map_flatMap {M α β : Type} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a ↦ ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- A form built block by block has the sum of the blocks' values. -/
private theorem eval_flatMap {j : Fin I.ntab} {n : ℕ} (g : Fin n → I.Form j) (q : Column I.μ)
    (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I ((List.finRange n).flatMap g) q z =
      ∑ b, M3Instance.Form.eval I (g b) q z := by
  rw [M3Instance.Form.eval, sum_map_flatMap, Fin.sum_univ_def]
  rfl

/-- A flush block's terms evaluate to its weight times its leaf extension, less the padding
term. -/
private theorem eval_flushForm (q : Column I.μ) (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (w : E) (α : Fin 4 → E) (β : E) (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I (flushForm j f w α β) q z = w * (β - ∑ i : Fin 16,
      (fingerprintWeights α)[i.val] * evalMle (I.virtualTable q j (flushPolys j f)[i]) z) := by
  have hone : evalMle (I.virtualTable q j 1) z = 1 := by
    have h1 : I.virtualTable q j 1 = Vector.replicate _ 1 := Vector.ext fun x hx ↦ by
      simp only [M3Instance.virtualTable, Vector.getElem_ofFn, Vector.getElem_replicate]
      rw [map_one]
      exact _root_.map_one (algebraMap K E)
    rw [h1, evalMle_replicate]
  simp only [M3Instance.Form.eval, flushForm, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def, oneRow, hone]
  rw [← Fin.sum_univ_def, mul_one, mul_sub, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  exact congrArg (w * β + ·) (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- A count column's term evaluates to its weight times the column's extension. -/
private theorem eval_countForm (hd : 1 ≤ I.d) (q : Column I.μ) (j : Fin I.ntab)
    (c : Fin (I.width j)) (w : E) (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I (countForm hd j c w) q z =
      w * eval₂Mle (I.column q ⟨j, c⟩).values (algebraMap K E) z := by
  simp only [M3Instance.Form.eval, countForm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  congr 1
  refine congrArg (evalMle · z) (Vector.ext fun x hx ↦ ?_)
  have hX : MvPolynomial.eval (I.row q j ⟨x, hx⟩) (MvPolynomial.X c : MvPolynomial (Fin (I.width j)) K) =
      I.row q j ⟨x, hx⟩ c := MvPolynomial.eval_X _
  rw [M3Instance.virtualTable, Vector.getElem_ofFn, hX, CMlPolynomialEval.map, Vector.getElem_map]
  show ofK ((I.column q ⟨j, c⟩).values.get ⟨x, hx⟩) = ofK ((I.column q ⟨j, c⟩).values[x])
  rw [Vector.get_eq_getElem]

/-- Block by block: a block's weighted leaf extension at its point is the part the verifier
evaluates from the true values plus its terms on the sumcheck tables at their points. -/
private theorem source_split (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E)
    (q : Column I.μ) (ζ : Vector E I.μBus) (vals : Vector E I.busClaims)
    (hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i))
    (src : Source I) (hs : src ∈ sources I k) (hκ : src.κ < I.μBus + 1) (w : E) :
    w * src.leafEval α β q (Gkr.lowPoint ζ ⟨src.κ, hκ⟩) =
      w * src.publicValue α β vals (Gkr.lowPoint ζ ⟨src.κ, hκ⟩) +
        ∑ j : I.SumcheckTables, M3Instance.Form.eval I (src.form h.one_le_d w α β j.1) q
          (I.lowPoint (point h ζ) j) := by
  cases src with
  | boundary b =>
    simp only [Source.form, M3Instance.Form.eval, List.map_nil, List.sum_nil,
      Finset.sum_const_zero, add_zero, Source.leafEval, Source.publicValue]
    exact congrArg (fun t ↦ w * (β - t)) (Finset.sum_congr rfl fun i _ ↦
      congrArg ((fingerprintWeights α)[i.val] * ·)
        (coordValue_eq h q ζ vals hvals hκ _ (mem_boundaryColumns_of_mem hs i)).symm)
  | flush j f =>
    have hst : I.SumcheckTable j :=
      Or.inr (Or.inl (List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) f.isLt)))
    rw [Finset.sum_eq_single ⟨j, hst⟩]
    · rw [show (Source.flush j f).form h.one_le_d w α β j = flushForm j f w α β from
        dite_eq_left rfl,
        lowPoint_point, eval_flushForm]
      exact (mul_add _ _ _).trans (add_comm _ _)
    · intro j' _ hj'
      have hne : j ≠ j'.1 := fun he ↦ hj' (Subtype.ext he.symm)
      simp [Source.form, hne, M3Instance.Form.eval]
    · simp
  | count j c =>
    have hst : I.SumcheckTable j :=
      Or.inr (Or.inr (List.ne_nil_of_mem (mem_counts_of_mem hs)))
    rw [Finset.sum_eq_single ⟨j, hst⟩]
    · rw [show (Source.count j c).form h.one_le_d w α β j = countForm h.one_le_d j c w from
        dite_eq_left rfl, lowPoint_point, eval_countForm]
      exact (mul_add _ _ _).trans (add_comm _ _)
    · intro j' _ hj'
      have hne : j ≠ j'.1 := fun he ↦ hj' (Subtype.ext he.symm)
      simp [Source.form, hne, M3Instance.Form.eval]
    · simp

/-- Block `b` of side `k` is one of the side's blocks. -/
private theorem src_mem (k : Fin 3) (b : Fin (blocks I k).n) : src I k b ∈ sources I k :=
  (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem _)

/-- **The leaf claims are owed by the forms.** With the true values of the boundary columns,
side `k`'s forms sum to its total exactly when its leaf claim `v` is its leaves' extension at
`ζ`. -/
theorem sum_forms_eq_total_iff (h : Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E)
    (q : Column I.μ) (ζ : Vector E I.μBus) (v : E) (vals : Vector E I.busClaims)
    (hvals : ∀ i : Fin I.busClaims, vals[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i)) :
    (∑ j, M3Instance.Form.eval I (forms h k α β ζ j) q (I.lowPoint (point h ζ) j) =
        total h k α β ζ v vals) ↔
      evalMle (sideLeaves I k α β q) ζ = v := by
  have hsplit : ∑ b, weight h k b ζ * (src I k b).leafEval α β q (lowAt h k b ζ) =
      ∑ b, weight h k b ζ * (src I k b).publicValue α β vals (lowAt h k b ζ) +
        ∑ j, M3Instance.Form.eval I (forms h k α β ζ j) q (I.lowPoint (point h ζ) j) := by
    simp only [forms, eval_flatMap]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [lowAt_eq]
    exact source_split h k α β q ζ vals hvals (src I k b) (src_mem k b) _ _
  rw [leaf_decomposition h k α β q ζ, total, eq_sub_iff_add_eq]
  change _ ↔ ∑ b, weight h k b ζ * (src I k b).leafEval α β q (lowAt h k b ζ) +
    (1 + ∑ b, weight h k b ζ) = v
  rw [hsplit]
  constructor <;> intro H <;> rw [← H] <;> ring

/-! ## Completeness -/

variable (I)

/-- After the challenges: the push and pull products agree, the count product is nonzero, every
constraint vanishes, and the public lines and the Keccak predicate hold. -/
def afterChallenge : Set ((Data I × ∀ i, TheOracle I i) × Unit) :=
  {p | (∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 0)[x]) =
      ∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 1)[x] ∧
    (∏ x : Fin (2 ^ I.μBus), (leaves I p.1.1 p.1.2 2)[x]) ≠ 0 ∧
    I.ConstraintsVanish (theStack p.1.2) ∧
    I.PublicLinesHold p.1.1.1 (theStack p.1.2) ∧ I.aux (theStack p.1.2)}

variable {I}

/-- On a balanced bus with honest padding rows the two products agree at every `(α, β)`, and the
count product is nonzero. -/
theorem challenge_honest (h : Conditions I) (s : I.Stmt) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((s, o), w) ∈ Seam.commitHonest I) :
    (fun _ ↦ true) s = true ∧ ∀ ab : (Fin 4 → E) × E, (((s, ab), o), w) ∈ afterChallenge I := by
  obtain ⟨⟨hc, hb, hn, hl, ha⟩, hp⟩ := hin
  refine ⟨rfl, fun ab ↦ ⟨?_, prod_countLeaves_ne_zero h _ _ hp hn, hc, hl, ha⟩⟩
  change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 (theStack o))[x] =
    ∏ x : Fin (2 ^ I.μBus), (pullLeaves I ab.1 ab.2 (theStack o))[x]
  rw [prod_pushLeaves, prod_pullLeaves h, padProduct_of_honest hp, padProduct_of_honest hp,
    Multiset.coe_eq_coe.mpr hb]

/-- The honest roots are the products, the count root is nonzero, and every rider is zero. -/
theorem roots_honest (h : Conditions I) (x : Data I) (o : ∀ i, TheOracle I i) (w : Unit)
    (hin : ((x, o), w) ∈ afterChallenge I) :
    decide ((rootsHonest I ((x, o), w)).2 ≠ 0) = true ∧
      (((x, ![(rootsHonest I ((x, o), w)).1, (rootsHonest I ((x, o), w)).1,
        (rootsHonest I ((x, o), w)).2]), o), w) ∈ Gkr.relIn 3 I.μBus (leaves I) (riders I) := by
  obtain ⟨hp, hn, hc, hl, ha⟩ := hin
  refine ⟨decide_eq_true hn,
    (ridersZero_iff h x o).mpr ⟨hc, hl, ha⟩, fun s ↦ ?_⟩
  fin_cases s
  · rfl
  · exact hp
  · rfl

/-- The honest values are the boundary columns' extensions. -/
theorem honestValues_getElem (h : Conditions I) (q : Column I.μ) (ζ : Vector E I.μBus)
    (i : Fin I.busClaims) :
    (honestValues h q ζ)[i] =
      eval₂Mle (I.column q I.boundaryColumns[i]).values (algebraMap K E) (columnPoint h ζ i) := by
  simp [honestValues]

/-- The honest values are the boundary columns' extensions: the leaf claims force the forms to
the totals, and the riders' vanishing gives the zerocheck clause. -/
theorem values_honest (h : Conditions I) (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus)
    (o : ∀ i, TheOracle I i) (w : Unit)
    (hout : ((ℓ, o), w) ∈ Gkr.relOut 3 I.μBus (leaves I) (riders I)) :
    (fun (_ : Gkr.LayerStmt (Data I) E 3 I.μBus) (_ : Vector E I.busClaims) ↦ true) ℓ
        (honestValues h (theStack o) ℓ.2.1) = true ∧
      (((ℓ.1.1, busOut h ℓ (honestValues h (theStack o) ℓ.2.1)), o), w) ∈ Seam.bus I := by
  obtain ⟨hleaf, hr⟩ := hout
  obtain ⟨hcons, hl, ha⟩ := (riders_vanish_iff ℓ.1 o ℓ.2.1).mp hr
  refine ⟨rfl, ?_, ?_, ?_, hl, ha⟩
  · intro j C hC
    rw [show (busOut h ℓ (honestValues h (theStack o) ℓ.2.1)).point = point h ℓ.2.1 from rfl,
      lowPoint_point]
    exact hcons j.1 ((I.τ_le_τmax j).trans h.τmax_le) C hC
  · intro side
    exact (sum_forms_eq_total_iff h side _ _ _ _ _ _
      (honestValues_getElem h (theStack o) ℓ.2.1)).mpr (hleaf side)
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [busOut] using hc)
    exact (honestValues_getElem h (theStack o) ℓ.2.1 i).symm

end Bus

end
end LeanVM.Protocol
