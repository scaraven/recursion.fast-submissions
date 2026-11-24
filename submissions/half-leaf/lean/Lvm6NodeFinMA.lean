-- New for lvm6 (WP NODE5a). The batch's `MA` hypothesis of CC's final level (`ClaimsOk`'s last field) from
-- weights that are multiaffine at every length: any coordinate, any rotation, the batch, the ring claims.
import Lvm6AsmRing
import Lvm6WhirSum

/-!
# Multiaffine at every length (WP NODE5a)

`ccG_tail` asks `Whir.MA 24 (fun y ↦ (batch λ cs).1 (y.drop 6 ++ y.take 6))`: affine in each of the first 24
coordinates of a point of **any** length. This follows when each weight is `IsMA ν` for every `ν`:
* **`IsMA.coord`**: `IsMA μ f` is affine in the coordinate after any prefix (points of length `μ`).
* **`MA_of_coord`**: `MA n g` from affinity after every prefix shorter than `n`.
* **`MA_rot`**: `∀ ν, IsMA ν f` gives `MA n` of `f` at the rotated point `y.drop k ++ y.take k` (any `n`, `k`).
* **`isMA_batch`**: the batch of claims multiaffine at every length is so.
* **`isMA_ringOf`**: a ring claim (`ringOf`) is multiaffine at every length (`ringWeight_eq`: the weight's folds as
  `idxSum` of zipped products; the same statement as `Lvm6RingMap`'s private `ringWeight_fold`, re-proved here).
-/

set_option autoImplicit false

namespace Lvm6.Node.Fin

open LeanVM.Parameters Lvm Lvm.E2V Lvm6 Lvm6.Ring

/-- **Affine in any coordinate**: on points of length `μ`, an `IsMA μ` function is affine in the coordinate after
any prefix `P`. -/
theorem IsMA.coord : ∀ (P : List E2) {μ : ℕ} {f : List E2 → E2}, IsMA μ f → ∀ (S : List E2) (X : E2),
    P.length + 1 + S.length = μ → f (P ++ X :: S) = (1 + X) * f (P ++ 0 :: S) + X * f (P ++ 1 :: S)
  | [], μ, f, h, S, X, hl => by
    obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by simp only [List.length_nil] at hl; omega⟩
    exact h.1 X S (by simp only [List.length_nil] at hl; omega)
  | p :: P, μ, f, h, S, X, hl => by
    simp only [List.length_cons] at hl
    obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
    obtain ⟨haff, h0, h1⟩ := h
    have hY : ∀ Y : E2, (P ++ Y :: S).length = m := fun Y ↦ by simp only [List.length_append, List.length_cons]; omega
    have e0 := IsMA.coord P h0 S X (by omega)
    have e1 := IsMA.coord P h1 S X (by omega)
    beta_reduce at e0 e1
    simp only [List.cons_append]
    rw [haff p _ (hY X), haff p _ (hY 0), haff p _ (hY 1), e0, e1]
    ring

/-- **`MA n` coordinate by coordinate**: affine after every prefix shorter than `n`. -/
theorem MA_of_coord : ∀ (n : ℕ) (g : List E2 → E2),
    (∀ (P : List E2) (X : E2) (x : List E2), P.length < n →
      g (P ++ X :: x) = (1 - X) * g (P ++ 0 :: x) + X * g (P ++ 1 :: x)) → Whir.MA n g
  | 0, _, _ => trivial
  | n + 1, g, h => ⟨fun X x ↦ h [] X x (Nat.succ_pos n), fun X ↦ MA_of_coord n (fun x ↦ g (X :: x))
      fun P Y x hP ↦ h (X :: P) Y x (by simp only [List.length_cons]; omega)⟩

/-- A rotation moves a coordinate to another place and keeps the rest. -/
theorem rot_split (k : ℕ) (P x : List E2) : ∃ A B : List E2, A.length + 1 + B.length = P.length + 1 + x.length ∧
    ∀ Y : E2, (P ++ Y :: x).drop k ++ (P ++ Y :: x).take k = A ++ Y :: B := by
  by_cases hk : k ≤ P.length
  · refine ⟨P.drop k, x ++ P.take k, by simp only [List.length_drop, List.length_append, List.length_take]; omega,
      fun Y ↦ ?_⟩
    rw [List.drop_append_of_le_length hk, List.take_append_of_le_length hk]
    simp only [List.append_assoc, List.cons_append]
  · obtain ⟨j, hj⟩ : ∃ j, k = P.length + 1 + j := ⟨k - P.length - 1, by omega⟩
    refine ⟨x.drop j ++ P, x.take j, by
      simp only [List.length_append, List.length_drop, List.length_take]; omega, fun Y ↦ ?_⟩
    rw [List.drop_append, List.take_append, hj,
      List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega),
      show P.length + 1 + j - P.length = j + 1 by omega]
    simp only [List.nil_append, List.drop_succ_cons, List.take_succ_cons, List.append_assoc]

/-- **`MA` at a rotated point** from multiaffinity at every length. -/
theorem MA_rot {f : List E2 → E2} (hf : ∀ ν, IsMA ν f) (n k : ℕ) :
    Whir.MA n (fun y ↦ f (y.drop k ++ y.take k)) := by
  refine MA_of_coord n _ fun P X x _ ↦ ?_
  obtain ⟨A, B, -, hAB⟩ := rot_split k P x
  simp only [hAB]
  rw [IsMA.coord A (hf (A.length + 1 + B.length)) B X rfl, CharTwo.sub_eq_add]

/-! ## The batch and the ring claims -/

theorem isMA_polyEval (lam : E2) {ν : ℕ} : ∀ (cs : List Claim), (∀ c ∈ cs, IsMA ν c.1) →
    IsMA ν (fun x ↦ polyEvalF (cs.map fun c ↦ c.1 x) lam)
  | [], _ => (isMA_const 0 ν).congr fun p _ ↦ by simp [polyEvalF]
  | c :: cs, h => by
    have ih := isMA_polyEval lam cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    refine ((ih.smul lam).add (h c List.mem_cons_self)).congr fun p _ ↦ ?_
    simp only [List.map_cons, polyEvalF, List.foldr_cons]
    ring

/-- **The batch of claims multiaffine at every length is so.** -/
theorem isMA_batch (lam : E2) (cs : List Claim) (h : ∀ c ∈ cs, ∀ ν, IsMA ν c.1) :
    ∀ ν, IsMA ν (batch lam cs).1 := fun ν ↦
  (isMA_polyEval lam cs fun c hc ↦ h c hc ν).congr fun p _ ↦ (batch_fst lam cs p).symm

/-- The weight's inner fold (as `Lvm6RingMap`'s private `foldl_zip_prod`). -/
theorem foldl_zip_prod' (c : E2) : ∀ (r y : List E2),
    (List.zip r y).foldl (fun product (p : E2 × E2) ↦ product * (1 + p.1 + p.2)) c =
      c * (List.zipWith (fun x z ↦ 1 + x + z) r y).prod
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: r, b :: y => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_prod' _ r y, List.zipWith_cons_cons, List.prod_cons]
    ring

/-- **The ring weight's folds** (as `Lvm6RingMap`'s private `ringWeight_fold`), at a point of any length. -/
theorem ringWeight_eq (y : List E2) : ∀ (cs : List E2) (a : E2) (r : List E2),
    (cs.foldl (fun (acc : E2 × List E2) c ↦
      ((acc.1 + (List.zip acc.2 y).foldl (fun product (p : E2 × E2) ↦
        product * (1 + p.1 + p.2)) c), acc.2.map fun value ↦ value * value)) (a, r)).1 =
      a + idxSum cs fun k ↦ (List.zipWith (fun x z ↦ 1 + x + z) (r.map (· ^ 2 ^ k)) y).prod
  | [], a, r => by simp [idxSum]
  | c :: cs, a, r => by
    rw [List.foldl_cons]
    dsimp only
    rw [ringWeight_eq y cs, foldl_zip_prod', idxSum]
    have e : ((fun x : E2 ↦ x ^ 2 ^ 0) = id) := by funext x; simp
    have e' : ∀ k : ℕ, ((fun x : E2 ↦ x ^ 2 ^ k) ∘ fun value ↦ value * value) =
        fun x ↦ x ^ 2 ^ (k + 1) := fun k ↦ by
      funext x
      simp only [Function.comp]
      rw [← sq, ← pow_mul, pow_succ 2 k, mul_comm]
    simp only [List.map_map, e, List.map_id, e']
    ring

theorem isMA_idxSum {ν : ℕ} : ∀ (cs : List E2) (G : ℕ → List E2 → E2), (∀ k, IsMA ν (G k)) →
    IsMA ν (fun x ↦ idxSum cs fun k ↦ G k x)
  | [], _, _ => (isMA_const 0 ν).congr fun p _ ↦ by simp [idxSum]
  | c :: cs, G, h => ((h 0).smul c |>.add (isMA_idxSum cs (fun k ↦ G (k + 1)) fun k ↦ h (k + 1))).congr
      fun p _ ↦ by simp only [idxSum]

/-- **A ring claim is multiaffine at every length.** -/
theorem isMA_ringOf (c : SliceClaim) (f g : List E2) : ∀ ν, IsMA ν (ringOf c f g).1 := by
  intro ν
  have hz : ∀ k ν, IsMA ν (fun y ↦ (List.zipWith (fun x z ↦ 1 + x + z) (c.pt.map (· ^ 2 ^ k)) y).prod) :=
    fun k ν ↦ isMA_zipProd _ (fun r t ↦ by linear_combination (-(t * (r + 1))) * two_eq_zero_E2) ν _
  have hW : ∀ ν, IsMA ν (fun y ↦ 0 + idxSum (ringCoefficients f g) fun k ↦
      (List.zipWith (fun x z ↦ 1 + x + z) (c.pt.map (· ^ 2 ^ k)) y).prod) := fun ν ↦
    (isMA_idxSum _ _ fun k ↦ hz k ν).congr fun p _ ↦ by rw [zero_add]
  refine (isMA_take hW c.pt.length ν).congr fun p _ ↦ ?_
  simp only [ringOf, ringClaim, Lvm6.Ring.ringWeight, ← ringWeight_eq]
  simp [eqEvalF]

end Lvm6.Node.Fin
