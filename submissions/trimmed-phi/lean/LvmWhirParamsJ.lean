-- New for lvm2 (WP JB-L): S2's WHIR openings in the Johnson regime (JB-DES §0/§1.2: J1 = `C_main` Johnson,
-- `C_rec` unique decoding; J2 = both Johnson), their escape bounds `≤ 2^-128`, the levels' arithmetic and the
-- stacked-opening specifications; the candidate count of a Johnson root.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: Johnson parameters)
-/
import LvmWhirParamsG
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Degree.Defs
import LvmJBComplete
import LvmMcaUd
import LvmWhirCode
import LvmWhirParams
import LvmWhirEscapeJ
import LvmWhirMidJ
import LvmWhirSpec
-- (GOLF2 import pruning: dropped LvmJBMutual: unused by this module.)

-- (GOLF2: 46 declarations that `certified` does not use moved verbatim to `LvmWhirSuffixROff`, outside its import closure.)

-- ===== merged from `LvmJBCTBasic` (GOLF module merge: `LvmJBCTBasic.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCTBasic.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Shared coding-theory vocabulary

This module owns the word, support, weight, code, and minimum-distance
definitions shared by arbitrary-code agreement and Reed--Solomon codes.
-/

namespace JB.CodingTheory

/-- A length-`n` word over the alphabet `F`. -/
abbrev Word (F : Type*) (n : ℕ) := Fin n → F

/-- A linear length-`n` code over `F`. -/
abbrev LinearCode (F : Type*) [Semiring F] (n : ℕ) :=
  Submodule F (Word F n)

section Support

variable {F : Type*} [Zero F] [DecidableEq F]

/-- Support of a word on a finite coordinate set. -/
def supportOn {n : ℕ} (U : Finset (Fin n)) (w : Word F n) : Finset (Fin n) :=
  U.filter fun i ↦ w i ≠ 0

@[simp] theorem mem_supportOn {n : ℕ} (U : Finset (Fin n))
    (w : Word F n) (i : Fin n) :
    i ∈ supportOn U w ↔ i ∈ U ∧ w i ≠ 0 := by
  simp [supportOn]

/-- Hamming weight. -/
def weight {n : ℕ} (w : Word F n) : ℕ :=
  (supportOn Finset.univ w).card

end Support

section Agreement

variable {F : Type*} [DecidableEq F]

/-- Coordinates on which two words agree. -/
def agreementCoordinates {n : ℕ} (left right : Word F n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ left i = right i

@[simp] theorem mem_agreementCoordinates {n : ℕ}
    (left right : Word F n) (i : Fin n) :
    i ∈ agreementCoordinates left right ↔ left i = right i := by
  simp [agreementCoordinates]

end Agreement

section SemiringSupport

variable {F : Type*} [Semiring F] [DecidableEq F]

/-- `C` has minimum distance at least `d`. -/
structure HasMinimumDistanceAtLeast {n : ℕ} (C : LinearCode F n)
    (d : ℕ) : Prop where
  distance_le_length : d ≤ n
  weight_ge_distance : ∀ c : Word F n, c ∈ C → c ≠ 0 → d ≤ weight c

end SemiringSupport

section NegSupport

variable {F : Type*} [AddGroup F] [DecidableEq F]

@[simp] theorem supportOn_neg {n : ℕ} (U : Finset (Fin n)) (x : Word F n) :
    supportOn U (-x) = supportOn U x := by
  ext i
  simp [supportOn]

@[simp] theorem weight_neg {n : ℕ} (x : Word F n) : weight (-x) = weight x := by
  simp [weight]

end NegSupport

end JB.CodingTheory
end
-- ===== end of `LvmJBCTBasic` =====

-- ===== merged from `LvmJBCTProximity` (GOLF module merge: `LvmJBCTProximity.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCTProximity.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Basic proximity and row-combination infrastructure

This module supplies proximity definitions, row combinations, and the
finite-dimensional counting facts used by selected-MCA extraction.
-/

namespace JB.CodingTheory

variable {F : Type*} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- Columns on which at least one row differs from its selected codeword. -/
noncomputable def matrixErrorCoordinates {Row : Type*} [Fintype Row]
    (rows decodedRows : Row → Word F n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ ∃ row, rows row j ≠ decodedRows row j

end JB.CodingTheory
end
-- ===== end of `LvmJBCTProximity` =====

-- ===== merged from `LvmJBCTInterleavedDistance` (GOLF module merge: `LvmJBCTInterleavedDistance.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCTInterleavedDistance.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Column distance of interleaved codewords

The Johnson-list argument treats rowwise codeword matrices as a code over a
larger alphabet.  Its first ingredient is that interleaving does not reduce
the column distance.  The actual Johnson cardinality theorem is not in this
module; see the soundness audit ledger.
-/

namespace JB.CodingTheory.InterleavedJohnson

open JB.CodingTheory

variable {F Row : Type*} [Field F] [DecidableEq F] [Fintype Row]
variable {n d : ℕ}

/-- Distinct interleaved codeword matrices differ in at least the base-code
distance many columns. -/
theorem matrixErrorCoordinates_card_ge_distance
    (C : LinearCode F n) (hmin : HasMinimumDistanceAtLeast C d)
    {first second : Row → Word F n}
    (hfirst : ∀ row, first row ∈ C) (hsecond : ∀ row, second row ∈ C)
    (hne : first ≠ second) :
    d ≤ (matrixErrorCoordinates first second).card := by
  obtain ⟨row, hrow⟩ : ∃ row, first row ≠ second row := by
    simpa [Function.ne_iff] using hne
  let difference := first row - second row
  have hdifferenceMem : difference ∈ C := C.sub_mem (hfirst row) (hsecond row)
  have hdifferenceNe : difference ≠ 0 := sub_ne_zero.mpr hrow
  have hdistance : d ≤ weight difference :=
    hmin.weight_ge_distance difference hdifferenceMem hdifferenceNe
  have hsubset : supportOn Finset.univ difference ⊆
      matrixErrorCoordinates first second := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, row, ?_⟩
    exact sub_ne_zero.mp ((mem_supportOn Finset.univ difference j).mp hj |>.2)
  exact hdistance.trans (Finset.card_le_card hsubset)

end JB.CodingTheory.InterleavedJohnson
end
-- ===== end of `LvmJBCTInterleavedDistance` =====

-- ===== merged from `LvmJBCTUniformFamily` (GOLF module merge: `LvmJBCTUniformFamily.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCTUniformFamily.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Uniform intersection families

`UniformFamilyBound n w lam L` asserts that every family of `w`-subsets of
`Fin n` whose distinct members meet in at most `lam` coordinates has at most
`L` members.  It is the purely combinatorial interface between list-size
arguments and their consumers: the Johnson count (degree one) and the
Hahn/Delsarte count (`JB.CodingTheory.HahnDelsarte`) both produce such bounds.

`card_le_of_uniformFamilyBound` reduces a list of rowwise codeword matrices
within a fixed column radius to this interface.  Its proof is the
agreement-set selection previously embedded in the Johnson list bound.
-/

namespace JB.CodingTheory

open scoped BigOperators

/-- Every `w`-uniform family on `Fin n` whose distinct members meet in at most
`lam` points has at most `L` members. -/
def UniformFamilyBound (n w lam L : ℕ) : Prop :=
  ∀ family : Finset (Finset (Fin n)),
    (∀ A ∈ family, A.card = w) →
    (∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card ≤ lam) →
    family.card ≤ L

theorem UniformFamilyBound.mono {n w lam L L' : ℕ}
    (h : UniformFamilyBound n w lam L) (hL : L ≤ L') :
    UniformFamilyBound n w lam L' :=
  fun family hcard hinter ↦ (h family hcard hinter).trans hL

theorem UniformFamilyBound.min {n w lam L L' : ℕ}
    (h : UniformFamilyBound n w lam L) (h' : UniformFamilyBound n w lam L') :
    UniformFamilyBound n w lam (min L L') :=
  fun family hcard hinter ↦ Nat.le_min.mpr
    ⟨h family hcard hinter, h' family hcard hinter⟩

variable {F Row : Type*} [Field F] [DecidableEq F] [Fintype Row]
variable {n E d L : ℕ}

/-- **Codeword-list reduction.**  Distinct rowwise codeword matrices within
column radius `E` of one received matrix select distinct `(n - E)`-subsets of
agreement columns, and two such subsets meet in at most `n - d` columns.  Any
uniform-family bound therefore bounds the list. -/
theorem card_le_of_uniformFamilyBound
    (C : LinearCode F n) (received : Row → Word F n)
    (candidates : Finset (Row → Word F n))
    (hmin : HasMinimumDistanceAtLeast C d)
    (hcode : ∀ candidate ∈ candidates, ∀ row, candidate row ∈ C)
    (hclose : ∀ candidate ∈ candidates,
      (matrixErrorCoordinates received candidate).card ≤ E)
    (hEd : E < d) (hbound : UniformFamilyBound n (n - E) (n - d) L) :
    candidates.card ≤ L := by
  classical
  have hd : d ≤ n := hmin.distance_le_length
  let agreement : candidates → Finset (Fin n) := fun candidate ↦
    Finset.univ \ matrixErrorCoordinates received candidate.1
  have hagreementCard (candidate : candidates) :
      n - E ≤ (agreement candidate).card := by
    have herror := hclose candidate.1 candidate.2
    have hsub := Nat.sub_le_sub_left herror n
    have hagreementEq : (agreement candidate).card =
        n - (matrixErrorCoordinates received candidate.1).card := by
      simp [agreement, Finset.card_sdiff]
    rw [hagreementEq]
    exact hsub
  choose selected hselected hselectedCard using fun candidate : candidates ↦
    Finset.exists_subset_card_eq (hagreementCard candidate)
  have hpair (first second : candidates) (hne : first ≠ second) :
      (selected first ∩ selected second).card ≤ n - d := by
    let difference := matrixErrorCoordinates first.1 second.1
    have hsubset : selected first ∩ selected second ⊆
        Finset.univ \ difference := by
      intro j hj
      have hjFirst := hselected first (Finset.mem_inter.mp hj).1
      have hjSecond := hselected second (Finset.mem_inter.mp hj).2
      have hjFirstAgreement := Finset.mem_sdiff.mp hjFirst
      have hjSecondAgreement := Finset.mem_sdiff.mp hjSecond
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hjDifference
      obtain ⟨row, hrow⟩ := (Finset.mem_filter.mp hjDifference).2
      have hfirst (row : Row) : received row j = first.1 row j := by
        apply not_ne_iff.mp
        intro hneRow
        exact hjFirstAgreement.2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, row, hneRow⟩)
      have hsecond (row : Row) : received row j = second.1 row j := by
        apply not_ne_iff.mp
        intro hneRow
        exact hjSecondAgreement.2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, row, hneRow⟩)
      exact hrow ((hfirst row).symm.trans (hsecond row))
    have hdifference : d ≤ difference.card := by
      apply InterleavedJohnson.matrixErrorCoordinates_card_ge_distance C hmin
        (hcode first.1 first.2) (hcode second.1 second.2)
      intro heq
      exact hne (Subtype.ext heq)
    calc
      (selected first ∩ selected second).card ≤
          (Finset.univ \ difference).card := Finset.card_le_card hsubset
      _ = n - difference.card := by
        simp [Finset.card_sdiff]
      _ ≤ n - d := Nat.sub_le_sub_left hdifference n
  have hselectedInjective : Function.Injective selected := by
    intro first second heq
    by_contra hne
    have hbound := hpair first second hne
    rw [heq, Finset.inter_self, hselectedCard second] at hbound
    omega
  let family : Finset (Finset (Fin n)) := Finset.univ.image selected
  have hfamilyCard : family.card = candidates.card := by
    change (Finset.univ.image selected).card = candidates.card
    rw [Finset.card_image_of_injective _ hselectedInjective]
    simp
  have hfamilyMemberCard (A : Finset (Fin n)) (hA : A ∈ family) :
      A.card = n - E := by
    obtain ⟨candidate, _hcandidate, rfl⟩ := Finset.mem_image.mp hA
    exact hselectedCard candidate
  have hfamilyPair (A : Finset (Fin n)) (hA : A ∈ family)
      (A' : Finset (Fin n)) (hA' : A' ∈ family) (hne : A ≠ A') :
      (A ∩ A').card ≤ n - d := by
    obtain ⟨first, _hfirst, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨second, _hsecond, rfl⟩ := Finset.mem_image.mp hA'
    exact hpair first second (fun heq ↦ hne (congrArg selected heq))
  rw [← hfamilyCard]
  exact hbound family hfamilyMemberCard hfamilyPair

end JB.CodingTheory
end
-- ===== end of `LvmJBCTUniformFamily` =====

-- ===== merged from `LvmJBCTInterleavedJohnson` (GOLF module merge: `LvmJBCTInterleavedJohnson.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCTInterleavedJohnson.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Johnson bound for fixed interleaved lists

This file proves the exact list-cardinality formula used by the general
selected-response analysis.  Each radius-`E` candidate supplies an agreement
set of exactly `n-E` coordinates.  Distinct codeword matrices have agreement
intersection at most `n-d`; finite Cauchy--Schwarz then gives the stated
Johnson denominator.
-/

namespace JB.CodingTheory.InterleavedJohnson

open JB.CodingTheory
open scoped BigOperators

/-- Denominator in the fixed interleaved-list Johnson bound at column
radius `E`. -/
def denominator (n d E : ℕ) : ℤ :=
  (n : ℤ) * d - 2 * n * E + E * E

/-- Exact integer list-size bound, valid when `denominator n d E` is
positive. -/
def listBound (n d E : ℕ) : ℕ :=
  n * (d - E) / (denominator n d E).toNat

namespace Internal

variable {n : ℕ}

private theorem sum_agreementOccurrences (family : Finset (Finset (Fin n))) :
    (∑ j : Fin n, (family.filter fun A ↦ j ∈ A).card) =
      ∑ A ∈ family, A.card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  simp

private theorem sum_agreementOccurrences_sq
    (family : Finset (Finset (Fin n))) :
    (∑ j : Fin n, (family.filter fun A ↦ j ∈ A).card ^ 2) =
      ∑ A ∈ family, ∑ A' ∈ family, (A ∩ A').card := by
  have hcard (j : Fin n) :
      (family.filter fun A ↦ j ∈ A).card =
        ∑ A ∈ family, if j ∈ A then 1 else 0 := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hcard, pow_two]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  calc
    (∑ j, (if j ∈ A then 1 else 0) *
        ∑ A' ∈ family, if j ∈ A' then 1 else 0) =
        ∑ j, ∑ A' ∈ family,
          (if j ∈ A then 1 else 0) * (if j ∈ A' then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp_rw [Finset.mul_sum]
    _ = ∑ A' ∈ family, ∑ j,
          (if j ∈ A then 1 else 0) * (if j ∈ A' then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ A' ∈ family, (A ∩ A').card := by
      apply Finset.sum_congr rfl
      intro A' hA'
      calc
        (∑ j, (if j ∈ A then 1 else 0) *
            (if j ∈ A' then 1 else 0)) =
            ∑ j ∈ Finset.univ.filter (fun j ↦ j ∈ A ∩ A'), 1 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjA : j ∈ A <;> by_cases hjA' : j ∈ A' <;>
            simp [hjA, hjA']
        _ = (A ∩ A').card := by
          rw [show Finset.univ.filter (fun j ↦ j ∈ A ∩ A') = A ∩ A' by
            ext j
            simp]
          exact (Finset.card_eq_sum_ones (s := A ∩ A')).symm

/-- Abstract incidence form of the Johnson calculation. -/
private theorem johnson_family_int {E d : ℕ}
    (family : Finset (Finset (Fin n)))
    (hE : E ≤ n) (hEd : E ≤ d) (hd : d ≤ n)
    (hcard : ∀ A ∈ family, A.card = n - E)
    (hinter : ∀ A ∈ family, ∀ A' ∈ family, A ≠ A' →
      (A ∩ A').card ≤ n - d) :
    (family.card : ℤ) * ((n : ℤ) * d - 2 * n * E + E * E) ≤
      (n : ℤ) * (d - E) := by
  by_cases hfamily : family = ∅
  · rw [hfamily]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hEd))
  have hfamilyPos : 0 < family.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hfamily)
  let occupancy : Fin n → ℕ := fun j ↦
    (family.filter fun A ↦ j ∈ A).card
  have hsum : (∑ j : Fin n, occupancy j) =
      family.card * (n - E) := by
    rw [sum_agreementOccurrences family]
    calc
      (∑ A ∈ family, A.card) = ∑ _A ∈ family, (n - E) :=
        Finset.sum_congr rfl fun A hA ↦ hcard A hA
      _ = _ := by simp
  have hrow (A : Finset (Fin n)) (hA : A ∈ family) :
      (∑ A' ∈ family, (A ∩ A').card) ≤
        (n - E) + (family.card - 1) * (n - d) := by
    calc
      (∑ A' ∈ family, (A ∩ A').card) ≤
          ∑ A' ∈ family, if A' = A then n - E else n - d := by
        apply Finset.sum_le_sum
        intro A' hA'
        by_cases heq : A' = A
        · subst A'
          simp [hcard A hA]
        · simpa [heq] using hinter A hA A' hA' (Ne.symm heq)
      _ = (n - E) + (family.card - 1) * (n - d) := by
        rw [← Finset.add_sum_erase family
          (fun A' ↦ if A' = A then n - E else n - d) hA]
        rw [if_pos rfl]
        congr 1
        calc
          (∑ A' ∈ family.erase A,
              if A' = A then n - E else n - d) =
              ∑ _A' ∈ family.erase A, (n - d) := by
            apply Finset.sum_congr rfl
            intro A' hA'
            rw [if_neg (Finset.ne_of_mem_erase hA')]
          _ = (family.card - 1) * (n - d) := by
            simp [Finset.card_erase_of_mem hA]
  have hsquares : (∑ j : Fin n, occupancy j ^ 2) ≤
      family.card * ((n - E) + (family.card - 1) * (n - d)) := by
    rw [sum_agreementOccurrences_sq family]
    calc
      (∑ A ∈ family, ∑ A' ∈ family, (A ∩ A').card) ≤
          ∑ _A ∈ family,
            ((n - E) + (family.card - 1) * (n - d)) :=
        Finset.sum_le_sum fun A hA ↦ hrow A hA
      _ = _ := by simp
  have hcauchy : (family.card * (n - E)) ^ 2 ≤
      n * (family.card *
        ((n - E) + (family.card - 1) * (n - d))) := by
    rw [← hsum]
    calc
      (∑ j : Fin n, occupancy j) ^ 2 ≤
          (Finset.univ : Finset (Fin n)).card *
            ∑ j : Fin n, occupancy j ^ 2 := by
        simpa using
          (sq_sum_le_card_mul_sum_sq
            (s := (Finset.univ : Finset (Fin n))) (f := occupancy))
      _ ≤ n * (family.card *
          ((n - E) + (family.card - 1) * (n - d))) := by
        simpa using Nat.mul_le_mul_left n hsquares
  have hcauchyInt :
      ((family.card * ((n - E) ^ 2) : ℕ) : ℤ) ≤
        ((n * ((n - E) + (family.card - 1) * (n - d)) : ℕ) : ℤ) := by
    have hcanceled : family.card * ((n - E) ^ 2) ≤
        n * ((n - E) + (family.card - 1) * (n - d)) := by
      apply Nat.le_of_mul_le_mul_left (c := family.card) ?_ hfamilyPos
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcauchy
    exact_mod_cast hcanceled
  push_cast at hcauchyInt
  rw [Nat.cast_sub hE, Nat.cast_sub hd,
    Nat.cast_sub (show 1 ≤ family.card by omega)] at hcauchyInt
  ring_nf at hcauchyInt ⊢
  linarith

end Internal

/-- The Johnson count as a uniform-family bound.  This is the degree-one
case of the Hahn/Delsarte count (`JB.CodingTheory.HahnDelsarte`), valid
symbolically whenever the Johnson denominator is positive. -/
theorem uniformFamilyBound_of_denominator_pos {n d E : ℕ}
    (hE : E ≤ n) (hEd : E < d) (hd : d ≤ n)
    (hden : 0 < denominator n d E) :
    UniformFamilyBound n (n - E) (n - d) (listBound n d E) := by
  intro family hcard hinter
  have hfamilyJohnson := Internal.johnson_family_int family hE
    (Nat.le_of_lt hEd) hd hcard hinter
  have hfamilyJohnson' :
      (family.card : ℤ) * denominator n d E ≤ ((n * (d - E) : ℕ) : ℤ) := by
    simpa [denominator, Nat.cast_sub (Nat.le_of_lt hEd)] using hfamilyJohnson
  have hdenCast : ((denominator n d E).toNat : ℤ) = denominator n d E :=
    Int.toNat_of_nonneg (le_of_lt hden)
  have hmul : family.card * (denominator n d E).toNat ≤ n * (d - E) := by
    rw [← hdenCast] at hfamilyJohnson'
    exact_mod_cast hfamilyJohnson'
  have hdenNat : 0 < (denominator n d E).toNat := by
    rw [← hdenCast] at hden
    exact_mod_cast hden
  apply (Nat.le_div_iff_mul_le hdenNat).2
  simpa [listBound] using hmul

variable {F Row : Type*} [Field F] [DecidableEq F] [Fintype Row]
variable {n E d : ℕ}

/-- The exact Johnson bound for a fixed list of rowwise codeword matrices
within column radius `E` of one received matrix. -/
theorem card_le_listBound
    (C : LinearCode F n) (received : Row → Word F n)
    (candidates : Finset (Row → Word F n))
    (hmin : HasMinimumDistanceAtLeast C d)
    (hcode : ∀ candidate ∈ candidates, ∀ row, candidate row ∈ C)
    (hclose : ∀ candidate ∈ candidates,
      (matrixErrorCoordinates received candidate).card ≤ E)
    (hE : E ≤ n) (hEd : E < d)
    (hden : 0 < denominator n d E) :
    candidates.card ≤ listBound n d E :=
  card_le_of_uniformFamilyBound C received candidates hmin hcode hclose hEd
    (uniformFamilyBound_of_denominator_pos hE hEd hmin.distance_le_length hden)

end JB.CodingTheory.InterleavedJohnson
end
-- ===== end of `LvmJBCTInterleavedJohnson` =====

-- ===== merged from `LvmJBConclusion` (GOLF module merge: `LvmJBConclusion.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBConclusion.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Exact strong-agreement conclusion

This file contains only the conclusion shared by the exact certificate
theorems.  It deliberately contains no real-valued envelope or asymptotic
wrapper.
-/

namespace JBAgreement

open Polynomial Finset

end JBAgreement
end
-- ===== end of `LvmJBConclusion` =====

-- ===== merged from `LvmJBCertificateMinimum` (GOLF module merge: `LvmJBCertificateMinimum.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCertificateMinimum.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Exact certificate minimum

This file minimizes the exact four-integer certificate ledger.  It contains no
real-valued envelope or asymptotic wrapper.
-/

namespace JBAgreement

open Polynomial Finset

/-! ## The exact inner term -/

section Exact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Exact

end JBAgreement
end
-- ===== end of `LvmJBCertificateMinimum` =====

-- ===== merged from `LvmJBStrongMutual` (GOLF module merge: `LvmJBStrongMutual.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBStrongMutual.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.

/-!
# Haböck's strong mutual correlated agreement

`Mutual.lean` proves the *per-line* mutual statement: for the one pair `(v₀, v₁)`
produced by correlated agreement, among parameters close to *that* line at most `e`
see agreement beyond the correlated set.  Haböck's notion (Hab25) is stronger in two
ways: it quantifies over **every** proximate codeword of every parameter — the whole
list, not the designated line point — and it demands each agreement set be
**contained** in the joint agreement set of some *explaining* pair of codewords.

This file proves the exact-certificate strong form.  The pipeline never cared
which proximate is tracked (the interpolant vanishes on the graph of the line,
so *any* `e`-close codeword is a root of every specialisation), so one simply chooses,
for each allegedly bad parameter, one unexplained proximate, and runs the machinery on
those choices (`exists_affine_bucket_of_GS_sharp_noFieldSize`).  On the bucket the chosen proximates
*are* the line `v₀ + z·v₁`; if such a proximate were unexplained even by `(v₀, v₁)`,
its agreement set would exit the correlated set at some coordinate — and by the
one-affine-root lemma each coordinate can serve at most one parameter, so at most
`|pairDisagree| ≤ e` of the `> e + 1` bucket parameters can be bad.  Contradiction.

* `explains` — the pair `(p₀, p₁)` explains the proximate `p` at `z`: it decomposes
  `p` along the line and its joint agreement contains the agreement set of `p`.
* `HasUnexplainedProximate` — `z` admits a dimension-`k` codeword within distance `e`
  of `u₀ + z·u₁` that no pair explains.
* `strong_mutual_unconditional` — no set of such parameters can reach the threshold.
-/

namespace JBAgreement

open Polynomial Finset

section Strong

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(p₀, p₁)` *explains* the proximate `p` of the line point at `z`: it decomposes
`p` along the line, and every coordinate where the line point agrees with `p` is a
coordinate of simultaneous agreement with `(p₀, p₁)`. -/
def explains (dom : ι → F) (u₀ u₁ : ι → F) (z : F) (p p₀ p₁ : F[X]) : Prop :=
  p = p₀ + C z * p₁ ∧
  ∀ x : ι, u₀ x + z * u₁ x = p.eval (dom x) →
    u₀ x = p₀.eval (dom x) ∧ u₁ x = p₁.eval (dom x)

/-- `z` admits an *unexplained proximate*: a dimension-`k` codeword within distance `e`
of `u₀ + z·u₁` that no pair of dimension-`k` codewords explains.  Haböck's mutual
correlated agreement is the statement that few `z` have this property. -/
def HasUnexplainedProximate (dom : ι → F) (u₀ u₁ : ι → F) (k e : ℕ) (z : F) : Prop :=
  ∃ p : F[X], p.natDegree < k ∧
    (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e ∧
    ∀ p₀ p₁ : F[X], p₀.natDegree < k → p₁.natDegree < k →
      ¬ explains dom u₀ u₁ z p p₀ p₁

/-- **Strong mutual correlated agreement, unconditional form.**  A set of parameters
all of which have an unexplained proximate cannot reach the correlated agreement
threshold. -/
theorem strong_mutual_unconditional
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F)
    (hbad : ∀ z ∈ S, HasUnexplainedProximate dom u₀ u₁ k e z)
    (m D dY dZ : ℕ)
    (hkdY : (k - 1) * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) *
          (dZ + 1))
    (hroot : D < m * (Fintype.card ι - e))
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) + dZ + 3 * (dY * dZ) < S.card) :
    False := by
  classical
  -- Choose, for each bad parameter, one unexplained proximate.
  have hchoice : ∀ z : F, ∃ p : F[X], z ∈ S → (p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e ∧
      ∀ p₀ p₁ : F[X], p₀.natDegree < k → p₁.natDegree < k →
        ¬ explains dom u₀ u₁ z p p₀ p₁) := by
    intro z
    by_cases hz : z ∈ S
    · obtain ⟨p, hp⟩ := hbad z hz
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose p hp using hchoice
  -- The Guruswami–Sudan package for these choices.
  obtain ⟨Q, hQ0, hQY, hQX, hQZ, hGS⟩ :=
    exists_gs_for dom hdom u₀ u₁ k e S p (fun z hz => (hp z hz).1)
      (fun z hz => (hp z hz).2.1) m D dY dZ hkdY hcnt hroot
  -- The affine bucket: the chosen proximates are the line on `S'`.
  obtain ⟨v₀, v₁, S', hS'S, hS'card, hdeg₀, hdeg₁, hpz⟩ :=
    exists_affine_bucket_of_GS_sharp_noFieldSize dom hdom u₀ u₁ k e hk S p
      (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2.1)
      Q hQ0 D dY dZ hQY hQX hQZ hGS hslack hS
  -- Correlated agreement of `(v₀, v₁)` with the words.
  have hE : (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e := by
    refine correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S' hS'card ?_
    intro z hz
    have h := (hp z (hS'S hz)).2.1
    rw [hpz z hz] at h
    exact h
  -- Each bucket parameter, being unexplained even by `(v₀, v₁)`, consumes a
  -- coordinate of the pair-disagreement set.
  have hdeg₀' : v₀.natDegree < k := hdeg₀
  have hdeg₁' : v₁.natDegree < k := hdeg₁
  have hwit : ∀ z ∈ S', ∃ x : ι,
      u₀ x + z * u₁ x = v₀.eval (dom x) + z * v₁.eval (dom x) ∧
      x ∈ pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) := by
    intro z hz
    have hunex := (hp z (hS'S hz)).2.2 v₀ v₁ hdeg₀' hdeg₁'
    have hnall : ¬ ∀ x : ι, u₀ x + z * u₁ x = (p z).eval (dom x) →
        u₀ x = v₀.eval (dom x) ∧ u₁ x = v₁.eval (dom x) := by
      intro hall
      exact hunex ⟨hpz z hz, hall⟩
    push Not at hnall
    obtain ⟨x, hxline, hxnot⟩ := hnall
    refine ⟨x, ?_, ?_⟩
    · rw [hpz z hz] at hxline
      simpa using hxline
    · rw [mem_pairDisagree]
      simp only [RSeval_apply]
      by_cases h0 : u₀ x = v₀.eval (dom x)
      · exact Or.inr (hxnot h0)
      · exact Or.inl h0
  choose xw hxw using fun z (hz : z ∈ S') => hwit z hz
  -- One coordinate per parameter: the witness map is injective on the bucket.
  have hinj : ∀ z (hz : z ∈ S') z' (hz' : z' ∈ S'), xw z hz = xw z' hz' → z = z' := by
    intro z hz z' hz' hxx
    have h1 := hxw z hz
    have h2 := hxw z' hz'
    rw [hxx] at h1
    exact eq_of_mem_pairDisagree h2.2 h1.1 h2.1
  -- Count: the bucket injects into the pair-disagreement set.
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp (by omega : 0 < S'.card)
  haveI : Nonempty ι := ⟨xw z₀ hz₀⟩
  have hcard : S'.card ≤ (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card := by
    have hmap : ∀ z ∈ S', (if hz : z ∈ S' then xw z hz else Classical.arbitrary ι)
        ∈ pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) := by
      intro z hz
      rw [dif_pos hz]
      exact (hxw z hz).2
    refine Finset.card_le_card_of_injOn _ hmap ?_
    intro z hz z' hz' hxx
    rw [Finset.mem_coe] at hz hz'
    simp only [dif_pos hz, dif_pos hz'] at hxx
    exact hinj z hz z' hz' hxx
  omega

end Strong

/-! ### The Johnson-regime statements -/

section Johnson

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- **Strong mutual correlated agreement in the Johnson regime** (Hab25, negative
form): the number of parameters admitting *any* unexplained proximate is below the
correlated agreement threshold — of size `O_ρ(n/η³)` by `johnsonThreshold_le`. -/
theorem strong_mutual_johnson
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * (Fintype.card ι))
    (ht4 : 4 * η * (Fintype.card ι) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * (Fintype.card ι)
        ≤ (((Fintype.card ι - e : ℕ) : ℝ) - 4 * η * (Fintype.card ι)) ^ 2) :
    ((univ.filter fun z => HasUnexplainedProximate dom u₀ u₁ k e z).card : ℝ)
      < johnsonThreshold k (Fintype.card ι) e η := by
  apply lt_of_not_ge
  intro hcon
  set Bad : Finset F := univ.filter fun z => HasUnexplainedProximate dom u₀ u₁ k e z
    with hBad
  obtain ⟨m, D, dY, dZ, hkdY, hcnt, hroot, hslack, hSnat⟩ :=
    johnson_numeric k (Fintype.card ι) e Bad.card η
      hk2 hη hη4 hηn ht4 hJ hcon
  exact strong_mutual_unconditional dom hdom u₀ u₁ k e (by omega) Bad
    (fun z hz => (Finset.mem_filter.mp hz).2) m D dY dZ
    hkdY hcnt hroot hslack hSnat


end Johnson

end JBAgreement
end
-- ===== end of `LvmJBStrongMutual` =====

-- ===== merged from `LvmMcaJohnson` (GOLF module merge: `LvmMcaJohnson.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- New for lvm2 (WP JB-L): the Johnson-regime instance of `CodeFacts` (`LvmMcaUd`), from the vendored longfellow
-- port (`LvmJB*`, Apache-2.0, `LICENSE-longfellow`). The glue from `rsCode` to JB's `RSeval`/`LinearCode` forms
-- follows Flock's PJB instance file (`docs/v4/flock-pcs/model/PJB-files/JBInstRS.lean` @ archive/pcs/AGG).

/-!
# The code facts of a WHIR level at the Johnson radius

`CodeFacts (rsCode domain k) k A L M` (`LvmMcaUd`) is the per-level hypothesis of the WHIR
round-by-round analysis: uniqueness at `k` points, `k ≤ A`, a list bound `L` at agreement `A`, and
a per-row-pair MCA count `M` (the fold-list count is `|ρ|·M`). This module proves it at the
Johnson radius from two theorems of longfellow-zk's formalisation (vendored as `LvmJB*`):

* **the MCA count**: `JBAgreement.strong_mutual_johnson` (Haböck's strong mutual correlated
  agreement): for `2 ≤ k`, `0 < η ≤ 1/4`, `1 ≤ η n` and agreement `A = n − e` with
  `(k − 1) n ≤ (A − 4 η n)²`, fewer than `johnsonThreshold k n e η` challenges `z` admit an
  unexplained proximate. `mcaBad_hasUnexplainedProximate`: our `McaBad C A u₀ u₁ z` is such a
  challenge for `e = n − A`, so `M ≥ johnsonThreshold k n (n − A) η` bounds the MCA event;
* **the list bound**: `JB.CodingTheory.InterleavedJohnson.card_le_listBound` for any linear code
  of minimum distance `d` (here `d = n − k + 1`, `rsCode_minDist`), interleaved, column errors
  `E = n − A`: at most `listBound n d E = ⌊n (d − E) / (n d − 2 n E + E²)⌋` members.

`codeFacts_johnson` assembles them; the hypotheses are closed-form arithmetic on `n, k, A, η, L, M`,
checked per level by `norm_num` (`LvmWhirCodeJ`).
-/

namespace LeanVM.Protocol.Whir

open Finset Polynomial JBAgreement JB.CodingTheory JB.CodingTheory.InterleavedJohnson

section Johnson

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `rsCode` as JB's `LinearCode` on `Fin n` (the same submodule). -/
theorem rsCode_minDist {n : ℕ} (domain : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    HasMinimumDistanceAtLeast (rsCode domain k) (n - k + 1) := by
  refine ⟨by omega, fun c hc hc0 ↦ ?_⟩
  by_contra hlt
  apply hc0
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ c i = 0)
  have hw : weight c = (univ.filter fun i : Fin n ↦ ¬ c i = 0).card := rfl
  rw [card_univ, Fintype.card_fin] at hsplit
  refine eq_of_mem_code_of_agreeOn domain hc (Submodule.zero_mem _) (univ.filter fun i ↦ c i = 0)
    (by omega) fun x hx ↦ ?_
  exact (mem_filter.mp hx).2

/-- **Our MCA event is JB's**: an `McaBad` challenge at agreement `A` has an unexplained proximate
within distance `n − A`. -/
theorem mcaBad_hasUnexplainedProximate {n : ℕ} (domain : Fin n ↪ F) {k A : ℕ} (u₀ u₁ : Fin n → F)
    (z : F) (hk : 1 ≤ k) (h : McaBad (rsCode domain k) A u₀ u₁ z) :
    HasUnexplainedProximate domain u₀ u₁ k (n - A) z := by
  obtain ⟨S, hS, ⟨c, hc, hcS⟩, hno⟩ := h
  obtain ⟨p, hp, hpc⟩ := mem_rsCode_iff_eval.mp hc
  refine ⟨p, ?_, ?_, ?_⟩
  · rcases eq_or_ne p 0 with rfl | h0
    · simp; (clear * - hk; omega)
    · exact (natDegree_lt_iff_degree_lt h0).2 hp
  · calc (disagree (fun x ↦ u₀ x + z * u₁ x) (RSeval domain p)).card ≤ Sᶜ.card :=
          card_le_card fun x hx ↦ mem_compl.mpr fun hxS ↦
            (mem_filter.mp hx).2 (by rw [RSeval_apply, hpc]; exact hcS x hxS)
      _ = n - S.card := by rw [card_compl, Fintype.card_fin]
      _ ≤ n - A := by (clear * - hS; omega)
  · rintro p₀ p₁ h₀ h₁ ⟨-, hex⟩
    refine hno ⟨fun x ↦ p₀.eval (domain x), eval_mem_rsCode domain ?_,
      fun x ↦ p₁.eval (domain x), eval_mem_rsCode domain ?_, fun x hx ↦ hex x ?_⟩
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast h₀)
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast h₁)
    · rw [hpc, hcS x hx]

open Classical in
/-- **The MCA count at the Johnson radius** (`strong_mutual_johnson`). -/
theorem card_mcaBad_le_johnson {n : ℕ} (domain : Fin n ↪ F) {k A M : ℕ} (η : ℝ)
    (hk2 : 2 ≤ k) (hAn : A ≤ n) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ A) (hJ : ((k - 1 : ℕ) : ℝ) * n ≤ ((A : ℝ) - 4 * η * n) ^ 2)
    (hM : johnsonThreshold k n (n - A) η ≤ M) (u₀ u₁ : Fin n → F) :
    (univ.filter fun z ↦ McaBad (rsCode domain k) A u₀ u₁ z).card ≤ M := by
  have hsub : (univ.filter fun z ↦ McaBad (rsCode domain k) A u₀ u₁ z) ⊆
      univ.filter fun z ↦ HasUnexplainedProximate domain u₀ u₁ k (n - A) z := fun z hz ↦
    mem_filter.mpr ⟨mem_univ _,
      mcaBad_hasUnexplainedProximate domain u₀ u₁ z (by (clear * - hk2; omega)) (mem_filter.mp hz).2⟩
  have hnA : n - (n - A) = A := Nat.sub_sub_self hAn
  have hlt := strong_mutual_johnson (ι := Fin n) domain domain.injective u₀ u₁ k (n - A) η hk2 hη
    hη4 (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin, hnA])
    (by rwa [Fintype.card_fin, hnA])
  rw [Fintype.card_fin] at hlt
  have hc : ((univ.filter fun z ↦ McaBad (rsCode domain k) A u₀ u₁ z).card : ℝ) < M :=
    ((Nat.cast_le.mpr (card_le_card hsub)).trans_lt hlt).trans_le hM
  exact_mod_cast hc.le

/-- **The list bound at the Johnson radius** (`card_le_listBound`). -/
theorem card_iList_le_johnson {n : ℕ} (domain : Fin n ↪ F) {k A L : ℕ} (hk : 1 ≤ k) (hkA : k ≤ A)
    (hAn : A ≤ n) (hden : 0 < denominator n (n - k + 1) (n - A))
    (hL : listBound n (n - k + 1) (n - A) ≤ L) {ρ : Type} [Fintype ρ] (O : ρ → Fin n → F) :
    (iList (rsCode domain k) A O).card ≤ L := by
  refine (card_le_listBound (rsCode domain k) O (iList (rsCode domain k) A O)
    (rsCode_minDist domain hk (hkA.trans hAn)) (fun U hU ↦ ((mem_iList _ _ _ _).mp hU).1)
    (fun U hU ↦ ?_) (Nat.sub_le n A) (by (clear * - hkA hAn; omega)) hden).trans hL
  obtain ⟨S, hS, hagree⟩ := ((mem_iList _ _ _ _).mp hU).2
  calc (matrixErrorCoordinates O U).card ≤ Sᶜ.card :=
        card_le_card fun x hx ↦ mem_compl.mpr fun hxS ↦ by
          obtain ⟨r, hr⟩ := (mem_filter.mp hx).2
          exact hr (hagree r x hxS)
    _ = n - S.card := by rw [card_compl, Fintype.card_fin]
    _ ≤ n - A := by (clear * - hAn hS; omega)

/-- **The code facts at the Johnson radius**: `RS[F, domain, k]` on `n` points at agreement
threshold `A`, with JB's slack `η`, list bound `L ≥ listBound n (n−k+1) (n−A)` and MCA count
`M ≥ johnsonThreshold k n (n−A) η`. -/
theorem codeFacts_johnson {n : ℕ} (domain : Fin n ↪ F) {k A L M : ℕ} (η : ℝ)
    (hk2 : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ A) (hJ : ((k - 1 : ℕ) : ℝ) * n ≤ ((A : ℝ) - 4 * η * n) ^ 2)
    (hM : johnsonThreshold k n (n - A) η ≤ M)
    (hden : 0 < denominator n (n - k + 1) (n - A)) (hL : listBound n (n - k + 1) (n - A) ≤ L) :
    CodeFacts (rsCode domain k) k A L M where
  uniq _ hc _ hc' S hS h := eq_of_mem_code_of_agreeOn domain hc hc' S hS h
  k_le_thr := hkA
  card_iList_le _ _ O := card_iList_le_johnson domain (by (clear * - hk2; omega)) hkA hAn hden hL O
  card_foldBad_le _ _ O := by
    classical
    refine card_foldBad_le_of_mca _
      (fun _ hc _ hc' S hS h ↦ eq_of_mem_code_of_agreeOn domain hc hc' S (hkA.trans hS) h)
      (fun u₀ u₁ ↦ ?_) O
    convert card_mcaBad_le_johnson domain η hk2 hAn hη hη4 hηn ht4 hJ hM u₀ u₁

end Johnson

end LeanVM.Protocol.Whir
end
-- ===== end of `LvmMcaJohnson` =====

-- ===== merged from `LvmWhirCodeJ` (GOLF module merge: `LvmWhirCodeJ.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- New for lvm2 (WP JB-L): WHIR level codes at the Johnson radius (JB-DES §1.2, J1/J2 levels), from
-- `LvmMcaJohnson.codeFacts_johnson`. Constants from JB-DES's model (`jcode_jb`:
-- the smallest slack `η = e/2^30` with fold numerator `2L + 2^(ℓ−1)·M ≤ 2^62`).

/-!
# Johnson level codes

| code | `κ`, `R`, `n` | slack `η` | threshold `A` | list `L` | MCA count `M` |
|---|---|---|---|---|---|
| `codeJ18R1` (`C_main` level 0) | 18, 1, 2^19 | 401595/2^30 | 371512 | 98 | 144115061680871682 |
| `codeJ14R2` (`C_main` level 1) | 14, 2, 2^16 | 85809/2^29 | 32809 | 390 | 576458108990386070 |
| `codeJ10R3` (`C_main` level 2, `C_rec` level 1) | 10, 3, 2^13 | 1/2^13 | 2899 | 646 | 414094616521326733 |
| `codeJ13R3` (`C_rec` level 0, J2) | 13, 3, 2^16 | 185939/2^29 | 23261 | 231 | 144115057437445356 |

`A = ⌈√((k−1) n)⌉ + ⌈4 η n⌉`, `L = listBound n (n − k + 1) (n − A)`, `M = ⌈johnsonThreshold k n (n − A) η⌉`
(`k = 2^κ`). Each `facts` field is `codeFacts_johnson` with its hypotheses checked by `norm_num`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir JBAgreement JB.CodingTheory.InterleavedJohnson

/-- `C_main` level 0 at the Johnson radius: `κ = 18`, `R = 1`. -/
noncomputable def codeJ18R1 : LevelCode where
  κ := 18
  R := 1
  h64 := by norm_num
  hκ := by norm_num
  hR := le_rfl
  thr := 371512
  listMax := 98
  mcaMax := 144115061680871682
  facts := codeFacts_johnson (domain _ _ _) (401595 / 2 ^ 30) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_main` level 1 at the Johnson radius: `κ = 14`, `R = 2`. -/
noncomputable def codeJ14R2 : LevelCode where
  κ := 14
  R := 2
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 32809
  listMax := 390
  mcaMax := 576458108990386070
  facts := codeFacts_johnson (domain _ _ _) (85809 / 2 ^ 29) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_main` level 2 and `C_rec` level 1 at the Johnson radius: `κ = 10`, `R = 3`. -/
noncomputable def codeJ10R3 : LevelCode where
  κ := 10
  R := 3
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 2899
  listMax := 646
  mcaMax := 414094616521326733
  facts := codeFacts_johnson (domain _ _ _) (1 / 2 ^ 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_rec` level 0 at the Johnson radius (J2): `κ = 13`, `R = 3`. -/
noncomputable def codeJ13R3 : LevelCode where
  κ := 13
  R := 3
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 23261
  listMax := 231
  mcaMax := 144115057437445356
  facts := codeFacts_johnson (domain _ _ _) (185939 / 2 ^ 29) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- The codes of `C_rec`'s Johnson levels `(6,3) (3,3)` (J2, P20; `μ = 19`). -/
noncomputable def codesRec20J : ℕ → LevelCode
  | 0 => codeJ13R3
  | _ => codeJ10R3

end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirCodeJ` =====

-- ===== merged from `LvmWhirEpsJ` (GOLF module merge: `LvmWhirEpsJ.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- New for lvm2 (WP JB-L): the group escapes of the Johnson WHIR levels (JB-DES §1.2, §2.2), numerically.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: Johnson escapes)
-/

/-!
# The escapes of the Johnson levels

Per group of a WHIR level (`LvmWhirFolds.eFold`, `LvmWhirEscapeJ.eOod`/`eQuery`,
`LvmWhirDefs.eQueryFinal`), at JB-DES's J1/J2 shapes with the codes of `LvmWhirCodeJ`, before the
proof-of-work discount `2^-g` (`g = 14` gives the query groups `≤ 7·2^-131 < 2^-128`):

| group | `C_main` (6,1,230) (4,2,115) (4,3,77) | `C_rec` (J2) (6,3,77) (3,3,77) |
|---|---|---|
| fold, per challenge | `≤ 2^-130` each | `≤ 2^-130`, `≤ 2^-131` |
| OOD point (next list) | `≤ 2^-170` each | `≤ 2^-170` |
| positions + `λ` + openings | `≤ 7·2^-117` each (exact: 2^-114.30, 2^-114.80, final 2^-115.44) | `≤ 7·2^-117` each (2^-115.07, final 2^-115.44) |

Exact values from JB-L's group model. `eFold_le_of`, `eOod_le_of`, `eQuery_le_of`,
`eQueryFinal_le_of` turn each bound into one inequality of naturals, checked by `norm_num`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir

set_option exponentiation.threshold 512

section

/-! ## From naturals -/

/-- The fold escape from its numerator: `(2L + 2^(ℓ−1) M)·2^c ≤ 2^192`. -/
theorem eFold_le_of (P : LevelCode) (ℓ c : ℕ)
    (h : (2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax) * 2 ^ c ≤ 2 ^ 192) :
    eFold P ℓ ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eFold, card_E_ennreal, ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

/-- The OOD escape from its numerator: `C(L', 2)·κ·2^c ≤ 2^192`. -/
theorem eOod_le_of (P' : LevelCode) (κ c : ℕ) (h : P'.listMax.choose 2 * κ * 2 ^ c ≤ 2 ^ 192) :
    eOod P' κ ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eOod, card_E_ennreal, ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

/-- The query group with a next list: `((A−1)^t·2^192 + (t+1)L'·n^t)·2^c ≤ n^t·2^192`. -/
theorem eQuery_le_of (P P' : LevelCode) (t c : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + (t + 1) * P'.listMax * P.n ^ t) * 2 ^ c ≤
      P.n ^ t * 2 ^ 192) :
    eQuery P P' t ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eQuery, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact natCast_div_add_div_le (by positivity) (by positivity) h

/-- The final query group: `((A−1)^t·2^192 + t·n^t)·2^c ≤ n^t·2^192`. -/
theorem eQueryFinal_le_of (P : LevelCode) (t c : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + t * P.n ^ t) * 2 ^ c ≤ P.n ^ t * 2 ^ 192) :
    eQueryFinal P t ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eQueryFinal, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact natCast_div_add_div_le (by positivity) (by positivity) h

/-! ## Up to a factor -/

/-- `N / M ≤ k·2^-c` from `N · 2^c ≤ k · M`. -/
theorem natCast_div_le_mul_inv_pow {N M c k : ℕ} (h : N * 2 ^ c ≤ k * M) :
    (N : ENNReal) / M ≤ k * (2 : ENNReal)⁻¹ ^ c := by
  apply ENNReal.div_le_of_le_mul
  rw [mul_assoc, ← ENNReal.inv_pow, ← ENNReal.div_eq_inv_mul, ← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  exact_mod_cast h

/-- `A / B + C / D = (A D + C B) / (B D)` for naturals. -/
theorem natCast_div_add_div_eq {A B C D : ℕ} (hB : 0 < B) (hD : 0 < D) :
    (A : ENNReal) / B + (C : ENNReal) / D = ((A * D + C * B : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
  have hB0 : (B : ENNReal) ≠ 0 := by exact_mod_cast hB.ne'
  have hD0 : (D : ENNReal) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 : (A : ENNReal) / B = ((A * D : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact (ENNReal.mul_div_mul_right _ _ hD0 (ENNReal.natCast_ne_top D)).symm
  have h2 : (C : ENNReal) / D = ((C * B : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_comm (B : ENNReal) (D : ENNReal)]
    exact (ENNReal.mul_div_mul_right _ _ hB0 (ENNReal.natCast_ne_top B)).symm
  rw [h1, h2, ENNReal.div_add_div_same, ← Nat.cast_add]

/-- The final query group, up to a factor `k`. -/
theorem eQueryFinal_le_mul_of (P : LevelCode) (t c k : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + t * P.n ^ t) * 2 ^ c ≤ k * (P.n ^ t * 2 ^ 192)) :
    eQueryFinal P t ≤ k * (2 : ENNReal)⁻¹ ^ c := by
  rw [eQueryFinal, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact (natCast_div_add_div_eq (by positivity) (by positivity)).trans_le
    (natCast_div_le_mul_inv_pow h)

/-- The discount turns `7·2^-117` into `7·2^-131`. -/
theorem disc7 {x : ENNReal} (h : x ≤ 7 * (2 : ENNReal)⁻¹ ^ 117) :
    (2 : ENNReal)⁻¹ ^ 14 * x ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 :=
  calc (2 : ENNReal)⁻¹ ^ 14 * x ≤ (2 : ENNReal)⁻¹ ^ 14 * (7 * (2 : ENNReal)⁻¹ ^ 117) := by gcongr
    _ = 7 * (2 : ENNReal)⁻¹ ^ 131 := by rw [show (131 : ℕ) = 14 + 117 by rfl, pow_add]; ring

/-- The query group with a next list, up to a factor `k`. -/
theorem eQuery_le_mul_of (P P' : LevelCode) (t c k : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + (t + 1) * P'.listMax * P.n ^ t) * 2 ^ c ≤
      k * (P.n ^ t * 2 ^ 192)) :
    eQuery P P' t ≤ k * (2 : ENNReal)⁻¹ ^ c := by
  rw [eQuery, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact (natCast_div_add_div_eq (by positivity) (by positivity)).trans_le
    (natCast_div_le_mul_inv_pow h)

/-- `8·2^-(n+3) = 2^-n`. -/
theorem eight_mul_inv_pow (n : ℕ) : 8 * (2 : ENNReal)⁻¹ ^ (n + 3) = (2 : ENNReal)⁻¹ ^ n := by
  have h8 : (2 : ENNReal) ^ 3 * (2 : ENNReal)⁻¹ ^ 3 = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  rw [pow_add, show (8 : ENNReal) = 2 ^ 3 by norm_num, mul_comm, mul_assoc,
    mul_comm ((2 : ENNReal)⁻¹ ^ 3), h8, mul_one]

/-- `7·2^-131 + 2^-131 = 2^-128`. -/
theorem seven_add_one : 7 * (2 : ENNReal)⁻¹ ^ 131 + (2 : ENNReal)⁻¹ ^ 131 = (2 : ENNReal)⁻¹ ^ 128 := by
  rw [← eight_mul_inv_pow 128, show (8 : ENNReal) = 7 + 1 by norm_num, add_mul, one_mul]

/-- `7·2^-117 < 1`. -/
theorem seven_inv_lt_one : 7 * (2 : ENNReal)⁻¹ ^ 117 < 1 :=
  calc 7 * (2 : ENNReal)⁻¹ ^ 117 ≤ 8 * (2 : ENNReal)⁻¹ ^ (114 + 3) := by gcongr; norm_num
    _ = (2 : ENNReal)⁻¹ ^ 114 := eight_mul_inv_pow 114
    _ < 1 := inv_two_pow_lt_one (by norm_num)

/-! ## The Johnson levels -/

/-- **The fold escapes** of the Johnson levels. -/
theorem eFold_J : eFold codeJ18R1 6 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eFold codeJ14R2 4 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧ eFold codeJ10R3 4 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eFold codeJ13R3 6 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧ eFold codeJ10R3 3 ≤ (2 : ENNReal)⁻¹ ^ 131 := by
  refine ⟨eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_,
    eFold_le_of _ _ _ ?_⟩ <;> norm_num [codeJ18R1, codeJ14R2, codeJ10R3, codeJ13R3]

/-- **The OOD escapes**: the point after `C_main` levels 0 and 1 (`κ = 18, 14`; next lists
`L' = 390, 646`) and after `C_rec` level 0 (`κ = 13`, `L' = 646`). -/
theorem eOod_J : eOod codeJ14R2 18 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧
    eOod codeJ10R3 14 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧ eOod codeJ10R3 13 ≤ (2 : ENNReal)⁻¹ ^ 170 := by
  refine ⟨eOod_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_⟩ <;>
    norm_num [codeJ14R2, codeJ10R3, Nat.choose_two_right]

/-- **The query groups**, before the discount, all within `7·2^-117` (`2^-114.19`; exact: `C_main`
2^-114.30, 2^-114.80, final 2^-115.44; `C_rec` (J2) 2^-115.07, final as `C_main`'s). -/
theorem eQuery_J7 : eQuery codeJ18R1 codeJ14R2 230 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQuery codeJ14R2 codeJ10R3 115 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQueryFinal codeJ10R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQuery codeJ13R3 codeJ10R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 := by
  refine ⟨eQuery_le_mul_of _ _ _ _ _ ?_, eQuery_le_mul_of _ _ _ _ _ ?_,
    eQueryFinal_le_mul_of _ _ _ _ ?_, eQuery_le_mul_of _ _ _ _ _ ?_⟩ <;>
    norm_num [codeJ18R1, codeJ14R2, codeJ10R3, codeJ13R3, LevelCode.n]

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirEpsJ` =====

-- ===== merged from `LvmWhirSpecJ` (GOLF module merge: `LvmWhirSpecJ.lean` is now a stub importing `LvmWhirParamsJ`) =====
section
-- New for lvm2 (WP JB-L): the specification of the WHIR opening with out-of-domain samples (Johnson regime), ported
-- from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean` (formal rev 0b850750) onto
-- LvmWhirLevelMidSpec/LvmWhirSpec (PI-GRIND). Changed against leanVM: the opening is `verifyWhirJ cfg` with
-- `cfg.ood = true` (levels from the configuration, positions `per` per challenge, the root `c₀` of `n₀`
-- commitments, the proof of work of `cfg.grind` bits), the precondition is lvm's `WhirPreUd`/`StackedPreUd`, and
-- the ladder carries the positions' width. `anyT`, `LevelPreL`, `eBatch` and the batching lemmas are reused from
-- `LvmWhirSpec`.
/-
  LeanVM.Protocol.Whir.Sound.SpecJ

  The round-by-round soundness of lvm's WHIR opening with out-of-domain samples as a
  specification of the verifier program, with the explicit escape bound `whirEpsJ`.
-/

/-!
# The specification of the WHIR opening (Johnson regime)

For an opening `cfg : WhirConfig` with `cfg.ood = true` and a code `codes i` per level
(`LevelCode`: `κ_i`, `R_i`, threshold `A_i`, list bound `L_i`, MCA count `E_i`):

* `LadderArithJ`: the arithmetic of the levels, the positions' width `per·(κ_i + R_i) ≤ 192`, and
  the joint groups' escapes below `1`: `eOod (codes (i+1)) κ_i < 1` and
  `eQuery (codes i) (codes (i+1)) t_i < 1` at a level with a next one (no list bound),
  `eQueryFinal` at the final level;
* `levelEpsJ codes g i levels`, `whirEpsJ codes g levels`: the largest group escape, **the `εmax`
  of the opening**:

  `max_i max( (2·L_i + 2^(ℓ_i−1)·E_i)/|E|,  C(L_{i+1}, 2)·κ_i/|E|,
             2^-g·(((A_i − 1)/n_i)^{t_i} + (t_i + 1)·L_{i+1}/|E|) )`
  over the levels with a next level, and for the final level `levelEpsUd`'s
  `max( (2·L + 2^(ℓ−1)·E)/|E|, 2^-g·(((A − 1)/n)^t + t/|E|), 2/|E| )`;
* `levelsSpecJ`: the levels from `LevelPre` of the first (`midSpecJ`, and `finSpec` through
  `whirLevelsJ_one` at the final level), returning never in doom;
* `whirSpecJ`: **`verifyWhirJ cfg t w` from `WhirPreUd`**, lead `0`;
* `stackedSpecJ`: **`verifyStackedJ cfg claims` from `StackedPreUd`**, with the batching
  challenge's escape `eBatch J P₀ = (J − 1)·L₀/|E|` as lead (`card_batch_bad_le`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

section

/-! ## The levels' arithmetic and escapes -/

section Ladder

variable (μ per : ℕ) (codes : ℕ → LevelCode)

/-- The arithmetic of the levels, the positions' width and the joint groups' escapes below `1`. -/
def LadderArithJ : ℕ → ℕ → List Whir.Level → Prop
  | _, _, [] => True
  | i, pre, [level] => (codes i).κ + pre + level.fold = μ ∧ (codes i).R = level.logInvRate ∧
      eQueryFinal (codes i) level.queries < 1 ∧ per * ((codes i).κ + (codes i).R) ≤ 192
  | i, pre, level :: next :: rest => (codes i).κ + pre + level.fold = μ ∧
      (codes i).R = level.logInvRate ∧ eOod (codes (i + 1)) (codes i).κ < 1 ∧
      eQuery (codes i) (codes (i + 1)) level.queries < 1 ∧
      per * ((codes i).κ + (codes i).R) ≤ 192 ∧
      LadderArithJ (i + 1) (pre + level.fold) (next :: rest)

end Ladder

section Eps

variable (codes : ℕ → LevelCode) (g : ℕ)

/-- **The largest group escape** of the levels from level `i` (Johnson regime), the query groups
discounted by the proof of work of `g` bits. -/
noncomputable def levelEpsJ : ℕ → List Whir.Level → ENNReal
  | _, [] => 0
  | i, [level] => max (eFold (codes i) level.fold)
      (max ((2 : ENNReal)⁻¹ ^ g * eQueryFinal (codes i) level.queries) eTail)
  | i, level :: next :: rest => max (max (eFold (codes i) level.fold)
      (eOod (codes (i + 1)) (codes i).κ)) (max ((2 : ENNReal)⁻¹ ^ g *
        eQuery (codes i) (codes (i + 1)) level.queries) (levelEpsJ (i + 1) (next :: rest)))

/-- **The `εmax` of the WHIR opening with OOD samples.** -/
noncomputable def whirEpsJ (levels : List Whir.Level) : ENNReal := levelEpsJ codes g 0 levels

end Eps

/-! ## The levels -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The levels' specification** (Johnson regime). -/
noncomputable def levelsSpecJ (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (hc : c₀ < n₀)
    (hper : 1 ≤ per) (hg : g ≤ 192) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderArithJ μ per codes i pre levels →
      levelEpsJ codes g i levels ≤ εmax → (s : WhirStateT) →
      Spec (whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w i levels s)
        (fun h ↦ LevelPreL μ codes ℓ₀ w i pre levels s (viewC c₀ n₀ (commits h)))
        (fun _ _ ↦ False) εmax εmax 0
  | [], i, pre, _, _, s => (Spec.fail (Pre := fun h ↦ LevelPreL μ codes ℓ₀ w i pre [] s
        (viewC c₀ n₀ (commits h))) (Post := fun _ _ ↦ False)).mono (fun _ h ↦ h)
        (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | [level], i, pre, hA, hε, s =>
    (finSpec ⟨hw, hℓ₀, hA.1, hA.2.1, hc, hper, hA.2.2.2⟩ hg ((le_max_left _ _).trans hε)
      hA.2.2.1 ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s).congr
      (whirLevelsJ_one μ ℓ₀ per c₀ n₀ g dir w i level s).symm
  | level :: next :: rest, i, pre, hA, hε, s =>
    midSpecJ ⟨hw, hℓ₀, hA.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.1, hA.2.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.2.1, hc, hper, hA.2.2.2.2.1⟩ hg
      ((le_max_left _ _).trans ((le_max_left _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_left _ _).trans hε)) hA.2.2.1 hA.2.2.2.1
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      (fun s' ↦ levelsSpecJ hw hℓ₀ hc hper hg (next :: rest) (i + 1) (pre + level.fold)
        hA.2.2.2.2.2 ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s') s

/-! ## The opening -/

/-- `verifyWhirJ` with OOD on a configuration with levels: the first round polynomial, then the
levels. -/
theorem verifyWhirJ_eq {cfg : WhirConfig} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hood : cfg.ood = true) (hc : cfg.levels = level :: rest) :
    verifyWhirJ cfg t w = (sumcheckRoundPoly 3 t none).bind fun quad ↦
      whirLevelsJ cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct w 0 (level :: rest)
        ⟨t, quad, [], []⟩ := by
  rw [verifyWhirJ, hood, hc]
  rfl

/-- **The specification of the WHIR opening with out-of-domain samples.** From `WhirPreUd` (the
history has the `n₀` commitments the opening starts with, its root `c₀` is shaped as level `0`,
and every candidate of the root's word violates `(w, t)`), the opening's groups escape with
probability at most `εmax ≥ whirEpsJ codes cfg.grind cfg.levels` each, and it never returns in
doom. -/
noncomputable def whirSpecJ {cfg : WhirConfig} {t : E} {level : Whir.Level}
    {rest : List Whir.Level} (hood : cfg.ood = true) (hc : cfg.levels = level :: rest)
    (hℓ : level.fold = laneBits) (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits)
    (hcn : cfg.c₀ < cfg.n₀) (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192)
    (hw : IsMultiaffine cfg.μ w) (hA : LadderArithJ cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsJ codes cfg.grind (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyWhirJ cfg t w) (fun h ↦ WhirPreUd cfg.toUdConfig (codes 0) w t (commits h))
      (fun _ _ ↦ False) εmax 0 T :=
  anyT (Spec.congr (p' := verifyWhirJ cfg t w) (by rw [verifyWhirJ_eq hood hc, hℓ]; rfl)
    ((roundPolyInv (WhirPreUd cfg.toUdConfig (codes 0) w t) t (T := εmax) le_rfl).bind' fun quad ↦
      (levelsSpecJ (ℓ₀ := laneBits) hw hμ hcn hper hg (level :: rest) 0 0 hA hε
          ⟨t, quad, [], []⟩).mono
        (fun h hp ↦ by
          show LevelPre cfg.μ laneBits w 0 (codes 0) level.fold 0 _ _
          rw [hℓ]
          exact levelPre_zero (codes 0) hκ₀ rfl hμ w t quad _ (whirPre_of_ud hp.2) hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)) T

/-! ## The stacked opening -/

/-- `verifyStackedJ`: the batching challenge, then the opening. -/
theorem verifyStackedJ_eq (cfg : WhirConfig) (claims : List StackClaim) :
    verifyStackedJ cfg claims = VerifierProgram.sampleChallenge.bind fun ρ ↦
      verifyWhirJ cfg (dot (powers ρ claims.length) (claims.map (·.2)))
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)) := rfl

open Classical in
/-- **The specification of the stacked opening with out-of-domain samples.** From `StackedPreUd`
(every candidate of the root violates one of the `J` claims), the batching challenge escapes with
probability at most `eBatch J P₀ = (J − 1)·L₀/|E|` and the opening (`whirSpecJ`) follows. -/
noncomputable def stackedSpecJ {cfg : WhirConfig} {level : Whir.Level} {rest : List Whir.Level}
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfg.μ c.1)
    (hood : cfg.ood = true) (hc : cfg.levels = level :: rest) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits) (hcn : cfg.c₀ < cfg.n₀)
    (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192)
    (hA : LadderArithJ cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsJ codes cfg.grind (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyStackedJ cfg claims)
      (fun h ↦ StackedPreUd cfg.toUdConfig (codes 0) claims (commits h)) (fun _ _ ↦ False) εmax
      (eBatch claims.length (codes 0)) T :=
  by
  have S0 : Spec VerifierProgram.sampleChallenge (fun h ↦ StackedPreUd cfg.toUdConfig (codes 0)
      claims (commits h))
      (fun ρ h ↦ WhirPreUd cfg.toUdConfig (codes 0)
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))) (commits h)) εmax
      (eBatch claims.length (codes 0) + 0) 0 :=
    Spec.sampleE (eBatch claims.length (codes 0)) fun h₀ hp ↦ by
      have hb := card_batch_bad_le (codes 0) hκ₀ rfl hμ claims _ hp.2.2.2
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (hb.trans (le_of_eq (mul_comm _ _)))))
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hρ2 := hρ.2
      simp only [commits_sample] at hρ2
      by_contra hno
      exact hρ2 ⟨hp.1, hp.2.1, hp.2.2.1, fun q hq hh ↦ hno ⟨q, hq, hh⟩⟩
  have F0 := fun ρ : E ↦
    whirSpecJ (w := fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
      (t := dot (powers ρ claims.length) (claims.map (·.2))) hood hc hℓ hμ hκ₀ hcn hper hg
      (isMultiaffine_batched claims hcl ρ) hA hε 0
  have S1 := Spec.bind S0 F0
  exact anyT (Spec.congr (p' := verifyStackedJ cfg claims)
    (verifyStackedJ_eq cfg claims).symm
    (S1.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirSpecJ` =====

/-!
# S2's WHIR parameters at the Johnson radius

| opening | `μ` | levels `(ℓ, R, t)` | codes | `g` | OOD | root `c₀` of `n₀` |
|---|---|---|---|---|---|---|
| `cfgMain24J n₀` (`C_main`, J1 and J2) | 24 | (6,1,230) (4,2,115) (4,3,77) | `codesMain24J` | 14 | yes | 0 of `n₀` |
| `cfgRec20J` (`C_rec`, J2) | 19 | (6,3,77) (3,3,77) | `codesRec20J` | 14 | yes | 1 of 2 |
| `cfgRec20U` (`C_rec`, J1: R5's UD shape) | 19 | (6,3,138) (3,3,138) | `codesRec20U` (UD) | 14 | no | 1 of 2 |

`n₀` is the number of commitments present when `C_main`'s opening starts: 3 when `C_rec`'s
two-level opening (X-REC2) runs first and adds its level-1 commitment, 2 with a one-level `C_rec`.
The escape bounds do not depend on it.

* `whirEps_main24J`, `whirEps_rec20J`, `whirEps_rec20U`: every group escapes with at most
  `2^-128`; with a margin, `+ 2^-131 ≤ 2^-128` (the room left for the extractor's luck and the hash
  terms, JB-DES §2.2: the largest group is `C_main` level 0's query group, `2^-128.30`).
* `ladderArith_main24J`, `ladderArith_rec20J`, `ladderArith_rec20U`.
* `stackedMain24JSpec`, `stackedRec20JSpec`: the stacked openings' specifications (lead
  `eBatch J (codes 0)`, now `(J − 1)·L₀/|E|` with `L₀ = 98` for `C_main` and `231` for `C_rec`).
* `candidates_ncard_le`: the candidates of a root at a level code's threshold are at most its list
  bound (`L₀ = 98` for `C_main`, J1/J2): the front end's `candPairs.ncard ≤ L₀(main)·L₀(rec)`
  (`kgSpec`'s `L₀`) in place of `candPairs_ncard_le_one`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

set_option exponentiation.threshold 512

section

/-! ## The configurations -/

/-- `C_rec` at P20, Johnson (J2): levels `(6,3,77) (3,3,77)`, `g = 14`, OOD; root `1` of `2`. -/
def cfgRec20J : WhirConfig := ⟨⟨19, [⟨6, 3, 77⟩, ⟨3, 3, 77⟩], 8, 1, 2, false, 14⟩, true⟩

/-- `C_rec` at P20, unique decoding (J1, PI-OPT R5's shape): levels `(6,3,138) (3,3,138)`,
`g = 14`, no OOD; root `1` of `2`. -/
def cfgRec20U : WhirConfig := ⟨⟨19, [⟨6, 3, 138⟩, ⟨3, 3, 138⟩], 8, 1, 2, false, 14⟩, false⟩

/-- The UD codes of `cfgRec20U`: `κ = 13, 10`, `R = 3`. -/
noncomputable def codesRec20U : ℕ → LevelCode
  | 0 => LevelCode.ud 13 3 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 10 3 (by norm_num) (by norm_num) (by norm_num)

/-! ## The escapes -/

/-- A group of at most `2^-129` is at most `7·2^-131`. -/
theorem le_seven_of {x : ENNReal} {c : ℕ} (hc : 129 ≤ c) (h : x ≤ (2 : ENNReal)⁻¹ ^ c) :
    x ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 := by
  have h4 : (2 : ENNReal)⁻¹ ^ 129 = 4 * (2 : ENNReal)⁻¹ ^ 131 := by
    have h2 : (2 : ENNReal) ^ 2 * (2 : ENNReal)⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    rw [show (131 : ℕ) = 129 + 2 by rfl, pow_add, ← mul_assoc, mul_comm (4 : ENNReal), mul_assoc,
      show (4 : ENNReal) = 2 ^ 2 by norm_num, h2, mul_one]
  refine h.trans ((inv_two_pow_anti hc).trans ?_)
  rw [h4]
  gcongr
  norm_num

/-- A group within `7·2^-131` leaves the margin `2^-131`. -/
theorem add_margin_le {x : ENNReal} (h : x ≤ 7 * (2 : ENNReal)⁻¹ ^ 131) :
    x + (2 : ENNReal)⁻¹ ^ 131 ≤ (2 : ENNReal)⁻¹ ^ 128 :=
  (add_le_add h le_rfl).trans_eq seven_add_one

/-- **`εmax` of `C_rec` at the Johnson radius** (J2). -/
theorem whirEps_rec20J :
    whirEpsJ codesRec20J cfgRec20J.grind cfgRec20J.levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨-, -, -, f0, f1⟩ := eFold_J
  obtain ⟨-, -, o0⟩ := eOod_J
  obtain ⟨-, -, q1, q0⟩ := eQuery_J7
  refine add_margin_le ?_
  simp only [whirEpsJ, cfgRec20J, levelEpsJ, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, le_seven_of (by norm_num) o0⟩, disc7 q0,
    le_seven_of (by norm_num) f1, disc7 q1,
    le_seven_of (by norm_num) eTail_le⟩

/-- The escapes of `cfgRec20U` (UD): folds `≤ 2^-150`, queries `≤ 2^-114` before the discount. -/
theorem eps_rec20U : eFold (codesRec20U 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 150 ∧
    eFold (codesRec20U 1) 3 ≤ (2 : ENNReal)⁻¹ ^ 150 ∧
    eQueryUd (codesRec20U 0) (codesRec20U 1) 138 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQueryFinal (codesRec20U 1) 138 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 := by
  refine ⟨eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, ?_, eQueryFinal_le_mul_of _ _ _ _ ?_⟩
  · simp only [udMca, mcaUd, udThr]; norm_num
  · simp only [udMca, mcaUd, udThr]; norm_num
  · rw [eQueryUd, show (codesRec20U 1).listMax = 1 from rfl, mul_one, ← eQueryFinal]
    exact eQueryFinal_le_mul_of _ _ _ _ (by simp only [codesRec20U, LevelCode.ud, udThr]; norm_num)
  · simp only [codesRec20U, LevelCode.ud, udThr]; norm_num

/-- The bound without the margin. -/
theorem le_of_add_margin {x : ENNReal} (h : x + (2 : ENNReal)⁻¹ ^ 131 ≤ (2 : ENNReal)⁻¹ ^ 128) :
    x ≤ (2 : ENNReal)⁻¹ ^ 128 :=
  le_self_add.trans h

/-! ## The levels' arithmetic -/

theorem ladderArith_rec20J :
    LadderArithJ cfgRec20J.μ cfgRec20J.per codesRec20J 0 0 cfgRec20J.levels := by
  obtain ⟨-, -, o0⟩ := eOod_J
  obtain ⟨-, -, q1, q0⟩ := eQuery_J7
  have h := seven_inv_lt_one
  exact ⟨rfl, rfl, o0.trans_lt (inv_two_pow_lt_one (by norm_num)), q0.trans_lt h,
    by norm_num [cfgRec20J, codesRec20J, codeJ13R3],
    rfl, rfl, q1.trans_lt h, by norm_num [cfgRec20J, codesRec20J, codeJ10R3]⟩

theorem ladderArith_rec20U :
    LadderArithUd cfgRec20U.μ cfgRec20U.per codesRec20U 0 0 cfgRec20U.levels := by
  obtain ⟨-, -, q0, q1⟩ := eps_rec20U
  have h := seven_inv_lt_one
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgRec20U, codesRec20U], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgRec20U, codesRec20U]⟩

/-! ## The stacked openings -/

/-! ## The candidates of a Johnson root -/

/-- **The candidates are at most the list bound**: the candidates of `W` at a level code's
threshold inject into the code's list (`encStack`), so there are at most `listMax`. -/
theorem candidates_ncard_le {μ R : ℕ} (P : LevelCode) (hμ : laneBits ≤ μ)
    (hκ : P.κ = μ - laneBits) (hR : P.R = R) (W : Word) :
    (Candidates μ R P.thr W).ncard ≤ P.listMax := by
  rcases P with ⟨κ, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  simp only at hκ hR ⊢
  subst hκ hR
  have hle := Set.ncard_le_ncard_of_injOn (encStack μ R')
    (t := ((iList (rsCode (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits))) thr
      (laneWord μ R' W) : Finset _) : Set _))
    (fun q hq ↦ Finset.mem_coe.mpr (mem_iList_of_candidate h64 hq))
    (fun q _ q' _ h ↦ encStack_injective hμ h64 h)
  rw [Set.ncard_coe_finset] at hle
  exact hle.trans (facts.card_iList_le _ _)

end
end LeanVM.Protocol.Whir.Sound
