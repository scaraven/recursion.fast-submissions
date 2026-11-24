-- lvm6 X2 (part 2): the descent's re-indexing question (X1 §5, FORMAT6 v2.5.1 §5). New.
import LvmXDec

/-!
# A fold round keeps the positions and raises the degree bound by one

FORMAT6 §5: a fold round pairs **lanes** `2m` (`F`) and `2m + 1` (`G`) of a row into `G + (α + β·x)·F`, `x = K(p)`
the position's point; positions are not paired. So the folded lanes of rounds 2–6 (level 0) and of every round at
levels 1–4 are functions on the **same** positions `pt [0, 2^ht)` as the committed lanes, and no re-indexing is
needed. What changes is the degree: **`fold_encN`**: the fold of two `encN pt` codewords with `k` coefficients is
an `encN pt` codeword with `k + 1` coefficients (BLUEPRINT §3's `k' = 2^κ + j` in round `j`). This is the form
FD1's `OneErr ℓ k' S y c` takes (`y j = encN ptK c j`). The challenges and lanes may live in an extension `M`
(`E`), the points in `L` (`K`). Between levels the domain changes (`pt [0, 2^ht_{i+1})`), and the next level's lanes
are codewords of its own message, read on its own positions.

* **`novel_expand`**: a polynomial over `M` of degree `< m ≤ 2^N` is a combination of the first `m` novel
  polynomials (they are triangular: `natDegree (novelX pt x) = x`, nonzero leading coefficient).
* **`encN_eq_eval`**: `encN pt c j` evaluates `Σ c_x X_x` at `pt j`.
-/

set_option autoImplicit false

namespace Lvm.Nb

open Polynomial Finset

variable {L M : Type*} [Field L] [Field M] [Algebra L M] {pt : ℕ → L} {N : ℕ}

/-- The novel polynomial `X_x` over `M`. -/
noncomputable def novM (pt : ℕ → L) (x : ℕ) : M[X] := (novelX pt x).map (algebraMap L M)

/-- **Triangular expansion** in the novel basis. -/
theorem novel_expand (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ m : ℕ, m ≤ 2 ^ N → ∀ P : M[X], P.degree < (m : WithBot ℕ) → ∃ c : Fin m → M, P = ∑ x : Fin m, C (c x) * novM pt x
  | 0, _, P, hP => by
    refine ⟨Fin.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    ext j
    rw [degree_lt_iff_coeff_zero] at hP
    simpa using hP j (by simp)
  | m + 1, hm, P, hP => by
    obtain ⟨hd, hl⟩ := novelX_map (M := M) hpt (x := m) (by omega)
    set Q : M[X] := novM pt m with hQ
    have hQd : Q.natDegree = m := hd
    have hQl : Q.leadingCoeff ≠ 0 := hl
    set d := P.coeff m / Q.leadingCoeff
    have hP' : (P - C d * Q).degree < (m : WithBot ℕ) := by
      rw [degree_lt_iff_coeff_zero] at hP ⊢
      intro j hj
      rw [coeff_sub, coeff_C_mul]
      rcases Nat.eq_or_lt_of_le (show m ≤ j by exact_mod_cast hj) with hjm | hlt
      · subst hjm
        have : Q.coeff m = Q.leadingCoeff := by rw [leadingCoeff, hQd]
        rw [this, div_mul_cancel₀ _ hQl, sub_self]
      · rw [hP j (by exact_mod_cast hlt), coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, sub_zero]
    obtain ⟨c', hc'⟩ := novel_expand hpt m (by omega) _ hP'
    refine ⟨Fin.lastCases d c', ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.coe_castSucc, Fin.val_last]
    rw [← hc', ← hQ]
    ring

/-- `encN` evaluates the message polynomial. -/
theorem encN_eq_eval {k : ℕ} (c : Fin k → M) (j : ℕ) :
    encN pt c j = (∑ x : Fin k, C (c x) * novM pt x).eval (algebraMap L M (pt j)) := by
  rw [encN, eval_finsetSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [eval_mul, eval_C, novM, eval_map, eval₂_at_apply]

theorem degree_sum_novM_lt (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N) (c : Fin k → M) :
    (∑ x : Fin k, C (c x) * novM pt x).degree < (k : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
  show ((novelX pt x).map (algebraMap L M)).natDegree < j
  rw [(novelX_map (M := M) hpt (x := x) (by omega)).1]
  omega

/-- **A fold round of two codewords is a codeword with one more coefficient**, on the same positions. -/
theorem fold_encN (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k + 1 ≤ 2 ^ N) (F G : Fin k → M)
    (α β : M) : ∃ c : Fin (k + 1) → M, ∀ j,
      encN pt G j + (α + β * algebraMap L M (pt j)) * encN pt F j = encN pt c j := by
  set PF := ∑ x : Fin k, C (F x) * novM pt x
  set PG := ∑ x : Fin k, C (G x) * novM pt x
  have hF := degree_sum_novM_lt hpt (by omega) F
  have hG := degree_sum_novM_lt hpt (by omega) G
  have hP : (PG + (C α * PF + C β * (X * PF))).degree < ↑(k + 1) := by
    rw [degree_lt_iff_coeff_zero] at hF hG ⊢
    intro j hj
    have hj' : k + 1 ≤ j := by exact_mod_cast hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, hG _ (by exact_mod_cast (by omega : k ≤ n + 1)),
      hF _ (by exact_mod_cast (by omega : k ≤ n + 1)), hF _ (by exact_mod_cast (by omega : k ≤ n))]
    ring
  obtain ⟨c, hc⟩ := novel_expand hpt (k + 1) hk _ hP
  refine ⟨c, fun j => ?_⟩
  rw [encN_eq_eval, encN_eq_eval, encN_eq_eval, ← hc]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

end Lvm.Nb
