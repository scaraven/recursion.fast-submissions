-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-G).
import FRVIRFinalsSF

/-!
# S-G's side of the phase-final checks

* **`lagV_eq_lagrangeWeight`** (S-F RESULT, open 2): the skip Lagrange weight that `finRS`'s ops
  compute (`FRVIRFinalsSF.lagV`, a product with the barycentric constant `wInv`) is the weight
  `FRSkip.lagrangeWeight` at the 64 nodes of `S` that `FRSpartan.quirky_claim_split` uses. In
  characteristic 2, `λ − x_j = λ + x_j`.

`finP i` and `finPf` (A.9) are not in this module yet (S-G RESULT, open items).
-/

namespace FR

/-- The nodes of `S`, as `quirky_claim_split` indexes them. -/
def sNode (b : Fin 64) : F := skipNode (Fin.castLE (by norm_num) b)

theorem foldl_mul_eq {α : Type*} (g : α → F) :
    ∀ (xs : List α) (c : F), xs.foldl (fun a j => a * g j) c = c * (xs.map g).prod
  | [], c => by simp
  | x :: xs, c => by rw [List.foldl_cons, foldl_mul_eq g xs, List.map_cons, List.prod_cons]; ring

theorem xS_of_lt {j : ℕ} (hj : j < 64) : xS j = sNode ⟨j, hj⟩ := by
  simp only [xS, sNode, Nat.mod_eq_of_lt (show j < 128 by omega)]; rfl

/-- The product over `others lo` is the product over the 63 nodes other than `lo`. -/
theorem prod_others (g : ℕ → F) {lo : ℕ} (hlo : lo < 64) :
    ((others lo).map g).prod = ∏ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, g j := by
  have hc : (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩ =
      Finset.univ.map (Fin.succAboveEmb ⟨lo, hlo⟩) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_map, true_and,
      Fin.succAboveEmb_apply]
    exact ⟨fun h => Fin.exists_succAbove_eq h, fun ⟨y, hy⟩ => hy ▸ Fin.succAbove_ne _ _⟩
  have hl : ∀ h : ℕ → F, ((List.range 63).map h).prod = ∏ i ∈ Finset.range 63, h i := by
    intro h
    rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
      Multiset.prod_coe]
  rw [hc, Finset.prod_map, others, List.map_map, hl, Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Fin.succAboveEmb_apply]
  congr 1
  by_cases h : i.val < lo
  · simp only [h, ↓reduceIte]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; rfl
  · simp only [h, ↓reduceIte]
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; rfl

/-- **`lagV_eq_lagrangeWeight`**: the weight `finRS`'s ops compute at `λ` is the Lagrange weight
of node `lo` of `S` at `λ`. -/
theorem lagV_eq_lagrangeWeight (l : F) {lo : ℕ} (hlo : lo < 64) :
    lagV l lo = lagrangeWeight sNode l ⟨lo, hlo⟩ := by
  have hx : ∀ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, xS j = sNode j :=
    fun j _ => xS_of_lt j.isLt
  rw [lagV, wInv, foldl_mul_eq, foldl_mul_eq, one_mul, prod_others _ hlo, prod_others _ hlo,
    lagrangeWeight, mul_comm, xS_of_lt hlo]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [hx j hj, sub_eq_add_neg, CharTwo.neg_eq]
  · congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hx j hj, sub_eq_add_neg, CharTwo.neg_eq]

end FR
