import LvmQKeccakGkr
import LvmQEqKeccakAlg3
import LvmQKeccakLayer

-- ===== merged from `LvmQEqKeccakAlg4` (GOLF module merge: `LvmQEqKeccakAlg4.lean` is now a stub importing `LvmQEqKeccakGkr`) =====
section

/-!
# QA1: Keccak weight algebra, part 4 (`keccakOpen`'s slot weights and fold)

Adapted from rf-lvm-QA1 `LvmKeccakSlotWeights.lean` (WP-2, leanVM Keccak port, over
`LeanVM.Parameters.E`) to `F`'s copy over `Lvm.FE`. See `LvmQEqKeccakAlg` for the overview.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## Arrays of rows (adapted from WP-2) -/

/-- Entry `(o, z)` of an array of rows, `0` outside. -/
def rowsFE (rows : Array (Array FE)) (o z : ℕ) : FE := (rows.getD o #[]).getD z 0

/-- Sixty-four rows of sixty-four entries. -/
def SizedE (rows : Array (Array FE)) : Prop := rows.size = 64 ∧ ∀ o < 64, (rows.getD o #[]).size = 64

theorem modify_getDE (rows : Array (Array FE)) (i o : ℕ) (f : Array FE → Array FE) :
    (rows.modify i f).getD o #[] = if i = o ∧ o < rows.size then f (rows.getD o #[])
      else rows.getD o #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = o
  · subst h1
    by_cases h2 : i < rows.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem modify_stepE {rows : Array (Array FE)} (hs : SizedE rows) (i z' : ℕ) (x : FE) :
    SizedE (rows.modify i fun row ↦ row.setIfInBounds z' x) ∧
      ∀ o z, rowsFE (rows.modify i fun row ↦ row.setIfInBounds z' x) o z =
        if i = o ∧ z' = z ∧ o < 64 ∧ z < 64 then x else rowsFE rows o z := by
  refine ⟨⟨by simp [hs.1], fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
  · rw [modify_getDE]
    split_ifs
    · rw [Array.size_setIfInBounds]; exact hs.2 o ho
    · exact hs.2 o ho
  · rw [rowsFE, modify_getDE, rowsFE]
    by_cases h1 : i = o ∧ o < rows.size
    · rw [ite_eq_left h1, setIfInBounds_getD']
      have ho : o < 64 := hs.1 ▸ h1.2
      rw [hs.2 o ho]
      by_cases h2 : z' = z ∧ z' < 64
      · rw [ite_eq_left h2, ite_eq_left (show i = o ∧ z' = z ∧ o < 64 ∧ z < 64 from
          ⟨h1.1, h2.1, ho, h2.1 ▸ h2.2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
          fun h ↦ h2 ⟨h.2.1, h.2.1 ▸ h.2.2.2⟩)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
        fun h ↦ h1 ⟨h.1, hs.1 ▸ h.2.2.1⟩)]

theorem inner_rowsE (rows0 : Array (Array FE)) (hs : SizedE rows0) (b : ℕ) (V : ℕ → FE)
    (hb : b + 25 ≤ 64) : ∀ J, J ≤ 1600 →
      SizedE ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) ∧
      ∀ o z, rowsFE ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) o z =
        if b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J then V (64 * (o - b) + z)
        else rowsFE rows0 o z
  | 0, _ => ⟨hs, fun o z ↦ by simp⟩
  | J + 1, hJ => by
    obtain ⟨hs', hg⟩ := inner_rowsE rows0 hs b V hb J (by (clear * - hJ; omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs'', hg''⟩ := modify_stepE hs' (b + J / 64) (J % 64) (V J)
    refine ⟨hs'', fun o z ↦ ?_⟩
    rw [hg'', hg]
    by_cases h1 : b + J / 64 = o ∧ J % 64 = z ∧ o < 64 ∧ z < 64
    · rw [ite_eq_left h1, ite_eq_left (by (clear * - hb hJ h1; omega))]
      congr 1; (clear * - hb hJ h1; omega)
    · rw [ite_eq_right h1]
      by_cases h2 : b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J
      · rw [ite_eq_left h2, ite_eq_left (by (clear * - h2; omega))]
      · rw [ite_eq_right h2, ite_eq_right (by (clear * - hb h1 h2; omega))]

/-- The weight `keccakSlotWeights` puts at row `o`, column `z`. -/
def slotWE (segments w : List FE) (first count o z : ℕ) : FE :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

theorem outer_rowsE (segments w : List FE) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∀ S, S ≤ count →
      SizedE ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) ∧
      ∀ o z, rowsFE ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) o z = slotWE segments w first S o z
  | 0, _ => by
    refine ⟨⟨by simp, fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
    · simp [Array.getD_eq_getD_getElem?, ho]
    · simp only [List.range_zero, List.foldl_nil, rowsFE, slotWE]
      rw [ite_eq_right (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      by_cases h : o < 64
      · by_cases h' : z < 64 <;> simp [h, h']
      · simp [h]
  | S + 1, hS => by
    obtain ⟨hs, hg⟩ := outer_rowsE segments w first count hfc S (by (clear * - hS; omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_rowsE _ hs (25 * (first + S))
      (fun j ↦ segments.getD S 0 * w.toArray.getD j 0) (by (clear * - hfc hS; omega)) keccakBits le_rfl
    have hk : keccakBits = 1600 := rfl
    refine ⟨hs', fun o z ↦ ?_⟩
    rw [hg', hg, slotWE, slotWE]
    by_cases h1 : 25 * (first + S) ≤ o ∧ o < 25 * (first + S) + 25 ∧ z < 64 ∧
        64 * (o - 25 * (first + S)) + z < keccakBits
    · rw [ite_eq_left h1, ite_eq_left (by (clear * - h1; omega)), array_getD_toArray']
      have e1 : o / 25 - first = S := by (clear * - hfc hS h1; omega)
      have e2 : o % 25 = o - 25 * (first + S) := by (clear * - hk h1 e1; omega)
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : 25 * first ≤ o ∧ o < 25 * (first + S) ∧ z < 64
      · rw [ite_eq_left h2, ite_eq_left (by (clear * - h2; omega))]
      · rw [ite_eq_right h2, ite_eq_right (by (clear * - hk h1 h2; omega))]

theorem toListRows_getDE (A : Array (Array FE)) {o : ℕ} (ho : o < A.size) (z : ℕ) :
    ((A.toList.map Array.toList).getD o []).getD z 0 = (A.getD o #[]).getD z 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem toListRows_rowE (A : Array (Array FE)) {o : ℕ} (ho : o < A.size) :
    (A.toList.map Array.toList).getD o [] = (A.getD o #[]).toList := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

/-- **`keccakSlotWeights` in closed form.** -/
theorem slotWeights_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o z : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).getD z 0 =
      slotWE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights first count o z := by
  obtain ⟨hs, hg⟩ := outer_rowsE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights
    first count hfc count le_rfl
  rw [← hg o z, rowsFE]
  unfold keccakSlotWeights
  simp only [keccakSlotBits, slotLog, show (2 : ℕ) ^ 6 = 64 from rfl]
  exact toListRows_getDE _ (by rw [hs.1]; exact ho) z

theorem slotWeights_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) : (keccakSlotWeights logSteps claim first count).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rowsE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [keccakSlotBits, slotLog, show (2 : ℕ) ^ 6 = 64 from rfl, List.length_map,
    Array.length_toList]
  exact hs.1

theorem slotWeights_row_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rowsE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [keccakSlotBits, slotLog, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [toListRows_rowE _ (by rw [hs.1]; exact ho), Array.length_toList]
  exact hs.2 o ho

/-! ## The fold along the slot (adapted from WP-2) -/

/-- `keccakOpen`'s fold of the rows along the slot challenges. -/
def foldAllE (slot : List FE) (rows : List (List FE)) : List (List FE) :=
  slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

theorem zipWith_getDE (f : FE → FE → FE) (l₁ l₂ : List FE) {z : ℕ} (h₁ : z < l₁.length)
    (h₂ : z < l₂.length) : (List.zipWith f l₁ l₂).getD z 0 = f (l₁.getD z 0) (l₂.getD z 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

theorem mapRange_getDE (f : ℕ → List FE) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem sum_pairs (g : ℕ → FE) : ∀ N : ℕ,
    ∑ x ∈ range (2 * N), g x = ∑ x ∈ range N, (g (2 * x) + g (2 * x + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_pairs g N, Finset.sum_range_succ]
    ring

/-- `eq(c :: pt, o)` peels the lowest bit. -/
theorem eqAt_cons (c : FE) (pt : List FE) {o : ℕ} (ho : o < 2 ^ (pt.length + 1)) :
    eqAt (c :: pt) o = (if o % 2 = 1 then c else 1 + c) * eqAt pt (o / 2) := by
  rw [eqAt_prod _ (by simpa using ho), eqAt_prod _ (by rw [pow_succ] at ho; omega)]
  unfold eqProd
  rw [List.length_cons, Finset.prod_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [mul_comm]
  congr 1
  · simp [Nat.testBit_zero]
  · refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Nat.testBit_div_two]

/-- **The fold is the multilinear extension along the slot**, column by column. -/
theorem foldAll_eqE : ∀ (pt : List FE) (rows : List (List FE)), rows.length = 2 ^ pt.length →
    (∀ o < rows.length, (rows.getD o []).length = 64) →
    (foldAllE pt rows).length = 1 ∧ ((foldAllE pt rows).headD []).length = 64 ∧
      ∀ z < 64, ((foldAllE pt rows).headD []).getD z 0 =
        ∑ o ∈ range (2 ^ pt.length), eqAt pt o * (rows.getD o []).getD z 0
  | [], rows, hl, hr => by
    rcases rows with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · simp at hl
    · refine ⟨rfl, hr 0 (by simp), fun z _ ↦ ?_⟩
      simp [foldAllE, eqAt, eqKernel]
    · simp at hl
  | c :: pt, rows, hl, hr => by
    have step : foldAllE (c :: pt) rows = foldAllE pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) := rfl
    have hl' : rows.length / 2 = 2 ^ pt.length := by
      rw [hl, List.length_cons, pow_succ]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
    have hrow : ∀ i < rows.length / 2, ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])).getD i [] =
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) []) := by
      intro i hi
      exact mapRange_getDE _ hi
    obtain ⟨h1, h2, h3⟩ := foldAll_eqE pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (by rw [List.length_map, List.length_range, hl'])
      (fun i hi ↦ by
        have hi2 : i < rows.length / 2 := by simpa using hi
        rw [hrow i hi2, List.length_zipWith, hr _ (by (clear * - hl hl' hi2; omega)), hr _ (by (clear * - hl hl' hi2; omega)), min_self])
    rw [step]
    refine ⟨h1, h2, fun z hz ↦ ?_⟩
    rw [h3 z hz, List.length_cons, pow_succ, mul_comm, sum_pairs]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [hrow i (by (clear * - hl' hi'; omega)), zipWith_getDE _ _ _ (by rw [hr _ (by (clear * - hl hl' hi'; omega))]; exact hz)
      (by rw [hr _ (by (clear * - hl hl' hi'; omega))]; exact hz), eqAt_cons c pt (by rw [pow_succ]; (clear * - hi'; omega)),
      eqAt_cons c pt (by rw [pow_succ]; (clear * - hi'; omega))]
    have e1 : 2 * i % 2 = 0 := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
    have e2 : (2 * i + 1) % 2 = 1 := by (clear * - e1; omega)
    have e3 : 2 * i / 2 = i := by (clear * - e1; omega)
    have e4 : (2 * i + 1) / 2 = i := by (clear * - e1 e2; omega)
    simp only [e1, e2, e3, e4, if_true, zero_ne_one, if_false]
    ring

/-! ## The two openings of `verifyKeccak` -/

/-- `keccakOpen`'s inline fold is `foldAllE`. -/
theorem keccakOpen_fold (slot : List FE) (rows : List (List FE)) :
    slot.foldl (fun rows challenge =>
      (List.range (rows.length / 2)).map fun i =>
        List.zipWith (fun lo hi => lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) rows = foldAllE slot rows := rfl

/-- The folded slot weights at column `z`. -/
theorem open_fold_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (hfc : first + count ≤ 2)
    {slot : List FE} (hs : slot.length = 6) {z : ℕ} (hz : z < 64) :
    ((foldAllE slot (keccakSlotWeights logSteps claim first count)).headD []).getD z 0 =
      ∑ o ∈ range 64, eqAt slot o *
        slotWE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights first count o z := by
  obtain ⟨-, -, h3⟩ := foldAll_eqE slot (keccakSlotWeights logSteps claim first count)
    (by rw [slotWeights_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho => slotWeights_row_length _ _ _ _ hfc (by rwa [slotWeights_length _ _ _ _ hfc] at ho))
  rw [h3 z hz, hs, show (2 : ℕ) ^ 6 = 64 from rfl]
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [slotWeights_getD _ _ _ _ hfc (Finset.mem_range.mp ho)]

theorem fold_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (hfc : first + count ≤ 2)
    {slot : List FE} (hs : slot.length = 6) :
    ((foldAllE slot (keccakSlotWeights logSteps claim first count)).headD []).length = 64 :=
  (foldAll_eqE slot (keccakSlotWeights logSteps claim first count)
    (by rw [slotWeights_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho => slotWeights_row_length _ _ _ _ hfc (by rwa [slotWeights_length _ _ _ _ hfc] at ho))).2.1

/-- **The committed outputs' opening** (`first = 1`, `count = 1`): column `0` of the fold. -/
theorem open_committed (logSteps : ℕ) (claim : KeccakClaim) {slot : List FE} (hs : slot.length = 6) :
    ((foldAllE slot (keccakSlotWeights logSteps claim 1 1)).headD []).getD 0 0 =
      sumE ((List.range 25).map fun l => eqAt slot (25 + l) *
        (eqKernel (claim.point.drop (logSteps - 5))).getD 0 0 * claim.weights.getD (64 * l) 0) := by
  rw [open_fold_getD _ _ _ _ (by decide) hs (by decide), sumE_range,
    show (64 : ℕ) = 25 + (25 + 14) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h0 : ∑ o ∈ range 25, eqAt slot o *
      slotWE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights 1 1 o 0 = 0 :=
    Finset.sum_eq_zero fun o ho => by
      rw [slotWE, if_neg (by have := Finset.mem_range.mp ho; (clear * - this; omega)), mul_zero]
  have h2 : ∑ k ∈ range 14, eqAt slot (25 + (25 + k)) *
      slotWE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights 1 1 (25 + (25 + k)) 0 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [slotWE, if_neg (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), mul_zero]
  rw [h0, h2, zero_add, add_zero]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [slotWE, if_pos (by (clear * - hl'; omega)), show (25 + l) / 25 - 1 = 0 by (clear * - hl'; omega), show (25 + l) % 25 = l by (clear * - hl'; omega),
    Nat.add_zero, mul_assoc]

theorem dot_eq_sum {l r : List FE} (hl : l.length = 64) (hr : r.length = 64) :
    dot l r = ∑ z ∈ range 64, l.getD z 0 * r.getD z 0 := by
  have hz : List.zipWith (· * ·) l r = (List.range 64).map fun z => l.getD z 0 * r.getD z 0 := by
    apply List.ext_getElem
    · simp [hl, hr]
    · intro i h1 h2
      simp only [List.length_zipWith, hl, hr, min_self] at h1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ h1),
        List.getElem?_eq_getElem (hr ▸ h1)]
  unfold dot
  rw [hz, ← sumE_range]
  rfl

/-- **The inputs' opening** (`first = 0`, `count = 2`): the fold against the 64 slices. -/
theorem open_input (logSteps : ℕ) (claim : KeccakClaim) {slot slices : List FE} (hs : slot.length = 6)
    (hsl : slices.length = 64) :
    dot ((foldAllE slot (keccakSlotWeights logSteps claim 0 2)).headD []) slices =
      sumE ((List.range 2).map fun s => sumE ((List.range 25).map fun l =>
        eqAt slot (25 * s + l) * (eqKernel (claim.point.drop (logSteps - 5))).getD s 0 *
          sumE ((List.range 64).map fun z => slices.getD z 0 * claim.weights.getD (64 * l + z) 0))) := by
  rw [dot_eq_sum (fold_length _ _ _ _ (by decide) hs) hsl]
  rw [Finset.sum_congr rfl (fun z hz => by
    rw [open_fold_getD _ _ _ _ (by decide) hs (Finset.mem_range.mp hz), Finset.sum_mul]),
    Finset.sum_comm, show (64 : ℕ) = 2 * 25 + 14 from rfl, Finset.sum_range_add]
  have h2 : ∑ k ∈ range 14, ∑ z ∈ range 64, eqAt slot (2 * 25 + k) *
      slotWE (eqKernel (claim.point.drop (logSteps - 5))) claim.weights 0 2 (2 * 25 + k) z *
        slices.getD z 0 = 0 :=
    Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun z _ => by
      rw [slotWE, if_neg (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), mul_zero, zero_mul]
  rw [h2, add_zero, sum_range_mul', sumE_range]
  refine Finset.sum_congr rfl fun s hs' => ?_
  rw [sumE_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hs2 := Finset.mem_range.mp hs'
  have hl' := Finset.mem_range.mp hl
  rw [sumE_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' := Finset.mem_range.mp hz
  rw [slotWE, if_pos (by (clear * - hs2 hl' hz'; omega)), show (25 * s + l) / 25 - 0 = s by (clear * - hs2 hl'; omega),
    show (25 * s + l) % 25 = l by (clear * - hl'; omega)]
  ring

end Lvm.Q1
end
-- ===== end of `LvmQEqKeccakAlg4` =====

-- ===== merged from `LvmQEqKeccakLayer2` (GOLF module merge: `LvmQEqKeccakLayer2.lean` is now a stub importing `LvmQEqKeccakGkr`) =====
section

/-!
# QA1: tools for reading one Keccak layer template (`LvmQEqKeccakLayer`)

* `NoA`: a gadget emits no assertion (every gadget of `layerTB` but `gAssert`);
* `TInv`, `peelN`, `peelA`, `peelL`, `inv_end`: walk a template along its `>>=` chain, keeping the
  rows that hold, the whole's length and what its assertions amount to;
* `cp_append`, `cp_get`, `cp_range`: the copy rows;
* small facts on `F`'s side (`packSpec_pos`, `scSpec_length`, `fe_beq_iff`, `laneForm_congr`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## Gadgets without assertions -/

/-- `m` emits no assertion: its assertions hold on every memory. -/
def NoA {α : Type} (m : TB α) : Prop := ∀ (xv : Src → FE) (V : Nat → FE) (n : Nat), TAssert xv V (m n).2

theorem noA_pure {α : Type} (a : α) : NoA (pure a : TB α) := by
  intro xv V n k hk
  simp [tb_pure] at hk

theorem noA_bind {α β : Type} {m : TB α} {f : α → TB β} (hm : NoA m) (hf : ∀ a, NoA (f a)) : NoA (m >>= f) :=
  fun xv V n => (tassert_bind m f).mpr ⟨hm xv V n, hf _ xv V _⟩

theorem noA_emit {i : Ins} (hi : i.op ≠ .assert0) : NoA (emit i) := by
  intro xv V n k hk ha
  simp only [emit, List.length_singleton, Nat.lt_one_iff] at hk
  subst hk
  exact absurd ha hi

/-! ## Walking a template -/

/-- While reading a template from position `n`: the rows of the rest `R` hold, the whole has length
`L`, and the whole's assertions `TA` hold iff the rest's do and `Q` (the assertions read so far). -/
def TInv (xv : Src → FE) (V : Nat → FE) (TA : Prop) (L : Nat) (Q : Prop) {α : Type} (R : TB α) (n : Nat) :
    Prop :=
  THold xv V n (R n).2 ∧ L = n + (R n).2.length ∧ (TA ↔ TAssert xv V (R n).2 ∧ Q)

/-- Read a gadget without assertions. -/
theorem peelN {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv xv V TA L Q (m >>= f) n) (hm : NoA m) :
    ∃ a n', (m n).1 = a ∧ THold xv V n (m n).2 ∧ TInv xv V TA L Q (f a) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold_bind] at h1
  refine ⟨(m n).1, n + (m n).2.length, rfl, h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; omega
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

/-- Read the last gadget (its position kept). -/
theorem peelL {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv xv V TA L Q (m >>= f) n) (hm : NoA m) :
    THold xv V n (m n).2 ∧ TInv xv V TA L Q (f (m n).1) (n + (m n).2.length) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold_bind] at h1
  refine ⟨h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; omega
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

theorem tassert_gAssert {xv : Src → FE} {V : Nat → FE} {n : Nat} {a g : Src} :
    TAssert xv V (gAssert a g n).2 ↔ g.valF xv V * a.valF xv V = 0 := by
  refine ⟨gAssert_spec, fun h k hk _ => ?_⟩
  simp only [gAssert, emitA, List.length_singleton, Nat.lt_one_iff] at hk
  subst hk
  exact h

/-- Read an assertion. -/
theorem peelA {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {β : Type} {a g : Src}
    {f : Unit → TB β} {n : Nat} (h : TInv xv V TA L Q (gAssert a g >>= f) n) :
    ∃ n', TInv xv V TA L (Q ∧ g.valF xv V * a.valF xv V = 0) (f ()) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (gAssert a g n).1 = () := rfl
  rw [thold_bind, e] at h1
  rw [tb_bind, e] at h2
  rw [tassert_bind, e] at h3
  refine ⟨n + (gAssert a g n).2.length, h1.2, ?_, ?_⟩
  · rw [h2, List.length_append]; omega
  · rw [h3, tassert_gAssert]
    exact ⟨fun ⟨⟨h, h'⟩, hq⟩ => ⟨h', hq, h⟩, fun ⟨h', hq, h⟩ => ⟨⟨h, h'⟩, hq⟩⟩

theorem inv_end {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {n : Nat}
    (h : TInv xv V TA L Q (pure () : TB Unit) n) : L = n ∧ (TA ↔ Q) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨by simpa [tb_pure] using h2, ?_⟩
  rw [h3]
  exact ⟨fun h => h.2, fun h => ⟨noA_pure () xv V n, h⟩⟩

/-! ## Copy rows -/

/-- The copy rows of `l` placed at `n` hold. -/
def CopyHold (xv : Src → FE) (V : Nat → FE) (n : Nat) (l : List Src) : Prop :=
  THold xv V n (l.map fun x => linI 0 0 x x)

theorem cp_append {xv : Src → FE} {V : Nat → FE} {n : Nat} {l₁ l₂ : List Src} (h : CopyHold xv V n (l₁ ++ l₂)) :
    CopyHold xv V n l₁ ∧ CopyHold xv V (n + l₁.length) l₂ := by
  unfold CopyHold at h ⊢
  rw [List.map_append, thold_append, List.length_map] at h
  exact h

theorem cp_get {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List Src} (h : CopyHold xv V n l) :
    ∀ j < l.length, V (n + j) = (l.map (Src.valF xv V)).getD j 0 := by
  intro j hj
  have e : (l.map fun x => linI 0 0 x x).getD j default = linI 0 0 (l.getD j default) (l.getD j default) := by
    simp [hj]
  have := h j (by simpa using hj) (by rw [e]; exact Or.inr (Or.inl ⟨0, 0, rfl⟩))
  rw [this, e, ← getD_valF _ hj]
  show _ + FE.ofK 0 * _ + FE.ofK 0 = _
  rw [show FE.ofK 0 = 0 from rfl, zero_mul, add_zero, add_zero]
  rfl

theorem range_map_getD (l : List FE) : (List.range l.length).map (fun j => l.getD j 0) = l := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

theorem cp_range {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List Src} (h : CopyHold xv V n l) {k : Nat}
    (hk : l.length = k) : (List.range k).map (fun j => V (n + j)) = l.map (Src.valF xv V) := by
  subst hk
  rw [List.map_congr_left (fun j hj => cp_get h j (List.mem_range.mp hj))]
  have := range_map_getD (vals xv V l)
  simp only [vals, List.length_map] at this ⊢
  exact this

/-! ## Small facts -/

theorem fe_beq_iff (x y : FE) : (x == y) = true ↔ x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  show ((a0 == b0 && a1 == b1) && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem packSpec_pos (v : Nat → FE) : ∀ (pt : List FE) (value scale : FE) (p : Nat),
    (packSpec v pt value scale p).2.2.2 = p + 120 * pt.length
  | [], _, _, p => by simp [packSpec]
  | r :: rs, value, scale, p => by
    simp only [packSpec, List.length_cons]
    rw [packSpec_pos v rs]
    ring

theorem scSpec_length (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (es : List (Option FE)),
    (scSpec v count p claim es).1.length = es.length
  | _, _, [] => rfl
  | p, claim, e :: es => by
    simp only [scSpec, List.length_cons]
    rw [scSpec_length v count]

theorem rho_lt (i : Nat) : rho i < 64 := by
  unfold rho
  have hall : ∀ x ∈ keccakRho, x < 64 := by decide
  rw [List.getD_eq_getElem?_getD]
  cases h : keccakRho[i]? with
  | none => simp
  | some x => exact hall x (List.mem_of_getElem? h)

theorem laneForm_congr (B : List FE) {R R' : Nat → FE} (hR : ∀ s < 64, R s = R' s) (l : Nat) :
    laneForm B R l = laneForm B R' l := by
  have h1 : ∀ i, R (rho i) = R' (rho i) := fun i => hR _ (rho_lt i)
  have h2 : ∀ i, R ((rho i + 1) % 64) = R' ((rho i + 1) % 64) := fun i => hR _ (Nat.mod_lt _ (by norm_num))
  simp only [laneForm, h1, h2]

theorem rc_mem {i : Nat} (hi : i < 24) : keccakRC.getD i 0 ∈ keccakRC := by
  rw [List.getD_eq_getElem _ _ (by simpa [keccakRC] using hi)]
  exact List.getElem_mem _

end Lvm.Q1
end
-- ===== end of `LvmQEqKeccakLayer2` =====

-- ===== merged from `LvmQEqKeccakLayer` (GOLF module merge: `LvmQEqKeccakLayer.lean` is now a stub importing `LvmQEqKeccakGkr`) =====
section

/-!
# QA1: Q_arith_eq for one Keccak GKR layer

`layer_spec`: on the cells of one iteration of the layer template (`layerTB`, any memory where the
loop holds: `THold`), if the carried values represent `F`'s claim (`Rep`, with the layer's RC and
`first` constants and the stream view), then the copy rows represent the claim `F`'s
`verifyKeccakLayer` returns (`layerSpec`), the layer moves the position by `8·str`, and the two
gated assertions hold iff `F`'s two checks do (gate `1`; the converse for any gate).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- `F`'s array `eq` table is its list one. -/
theorem eqKernelA_toArray (p : List FE) : eqKernelA p = (eqKernel p).toArray := by
  unfold eqKernelA eqKernel
  suffices h : ∀ (acc : List FE), p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc.toArray =
      (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc).toArray from h [1]
  induction p with
  | nil => intro acc; rfl
  | cons r rs ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp

theorem getD_eqKernelA (p : List FE) (i : Nat) : (eqKernelA p).getD i 0 = eqAt p i := by
  rw [eqKernelA_toArray, array_getD_toArray']; rfl

end Lvm.Q1
end
-- ===== end of `LvmQEqKeccakLayer` =====

/-!
# QA1: building blocks of the Keccak GKR verifier's circuit equivalence

**`F` side.** `keccakLayers_run`: `F`'s layers on any state are `layersSpec (feAt Σ)` from the
position `ent + msg`, the checks threaded.

**Circuit side** (`gkrGadget`, `LvmQKeccakGkr`): per block specs (`fin1TB_spec`, `rot_spec`,
`fin2TB_spec`, the walking, relocation, write-count and no-assertion facts). The K = 16 assembly
(`verifyKeccak_run`, `gkr_spec` and their helpers) was removed at W32 (decision D7: no users, the E3
level-1 path is dead).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## `F`'s `verifyKeccak` on a view -/

theorem keccakLayers_cons (logSteps step : Nat) (steps : List Nat) (claim : KeccakClaim) :
    keccakLayers logSteps (step :: steps) claim =
      (verifyKeccakLayer logSteps step claim >>= fun c => keccakLayers logSteps steps c) := rfl

theorem layersSpec_cons (v : Nat → FE) (logSteps step : Nat) (steps : List Nat) (claim : KeccakClaim)
    (p : Nat) (ok : Bool) :
    layersSpec v logSteps (step :: steps) claim p ok =
      layersSpec v logSteps steps (layerSpec v logSteps step claim p).claim (layerSpec v logSteps step claim p).pos
        ((layerSpec v logSteps step claim p).ok2 && ((layerSpec v logSteps step claim p).ok1 && ok)) := by
  rw [layersSpec]

/-- **`keccakLayers` on a view**: `layersSpec` from `ent + msg`, the checks threaded. -/
theorem keccakLayers_run (sig : ByteArray) (logSteps : Nat) : ∀ (steps : List Nat) (claim : KeccakClaim)
    (_ : claim.point ≠ []) (s : RS),
    keccakLayers logSteps steps claim sig s =
      ((layersSpec (feAt sig) logSteps steps claim (s.ent + s.msg) s.ok).1,
        if steps = [] then s else
          ⟨(layersSpec (feAt sig) logSteps steps claim (s.ent + s.msg) s.ok).2.1, 0,
            (layersSpec (feAt sig) logSteps steps claim (s.ent + s.msg) s.ok).2.2⟩)
  | [], claim, _, s => rfl
  | step :: steps, claim, hpt, s => by
    rw [keccakLayers_cons, bind_run, verifyKeccakLayer_run sig logSteps step claim hpt, layersSpec_cons]
    have hpt' : (layerSpec (feAt sig) logSteps step claim (s.ent + s.msg)).claim.point ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [layerSpec_point_length, List.length_nil] at this
      exact hpt (List.length_eq_zero_iff.mp this)
    generalize layerSpec (feAt sig) logSteps step claim (s.ent + s.msg) = L at hpt' ⊢
    rw [keccakLayers_run sig logSteps steps L.claim hpt']
    simp only [Nat.add_zero, if_neg (List.cons_ne_nil step steps)]
    cases steps with
    | nil => rfl
    | cons _ _ => simp only [if_neg (List.cons_ne_nil _ _)]

/-! ## Operands across blocks -/

theorem gk_iterXv_fix (M : Mem) (o : LoopOut) (jf : Nat) (τ : Ty) (b : Nat) :
    iterXv M o jf (.ext ⟨τ, b, []⟩) = M.rd τ b := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, Addr.at]
  rfl

theorem gk_iterXv_gkS (M : Mem) (o : LoopOut) (jf : Nat) (c : Cell) : iterXv M o jf (gkS c) = c.val M :=
  gk_iterXv_fix M o jf c.ty c.n

/-- An operand a straight block exports: one of its rows, or a fixed cell. -/
def Fx (s : Src) : Prop := (∃ n, s = .loc n) ∨ ∃ τ b, s = .ext ⟨τ, b, []⟩

theorem gkOut_val (M : Mem) (o o' : LoopOut) (jf : Nat) (V : Nat → FE) {s : Src} (hs : Fx s) :
    (s.gkOut o).valF (iterXv M o' jf) V = s.valF (iterXv M o 0) (iterF M o 0) := by
  rcases hs with ⟨n, rfl⟩ | ⟨τ, b, rfl⟩
  · exact gk_iterXv_fix M o' jf _ _
  · show iterXv M o' jf (Src.ext ⟨τ, b, []⟩) = iterXv M o 0 (Src.ext ⟨τ, b, []⟩)
    rw [gk_iterXv_fix, gk_iterXv_fix]

theorem fx_emit (i : Ins) (n : Nat) : Fx (emit i n).1 := Or.inl ⟨n, rfl⟩

theorem fx_mapTB {α : Type} {f : α → TB Src} (hf : ∀ a n, Fx (f a n).1) :
    ∀ (as : List α) (n : Nat), ∀ x ∈ (mapTB f as n).1, Fx x
  | [], _, x, hx => by simp [mapTB, tb_pure] at hx
  | a :: as, n, x, hx => by
    simp only [mapTB, tb_bind, tb_pure, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf a n
    · exact fx_mapTB hf as _ x hx

theorem fx_gEqTab (z : Src) : ∀ (pt tab : List Src) (n : Nat), (∀ x ∈ tab, Fx x) →
    ∀ x ∈ (gEqTab z tab pt n).1, Fx x
  | [], tab, n, h => by simpa [gEqTab, tb_pure] using h
  | r :: rs, tab, n, h => by
    simp only [gEqTab, tb_bind]
    refine fx_gEqTab z rs _ _ (fun x hx => ?_)
    simp only [gEqStep, tb_bind, tb_pure, List.mem_append] at hx
    rcases hx with hx | hx
    · exact fx_mapTB (fun _ _ => fx_emit _ _) _ _ x hx
    · exact fx_mapTB (fun _ _ => fx_emit _ _) _ _ x hx

/-! ## The relocated layer template -/

theorem relocS_valF (xv : Src → FE) (V : Nat → FE) (q cst : Nat) (s : Src) :
    (relocS q cst s).valF xv V = s.valF (fun s' => xv (relocS q cst s')) V := by
  rcases s with k | k | ⟨τ, b, st⟩
  · rfl
  · rfl
  · rcases st with _ | ⟨s, _ | ⟨s', st⟩⟩
    · rfl
    · show (relocS q cst (.ext ⟨τ, b, [s]⟩)).valF xv V = xv (relocS q cst (.ext ⟨τ, b, [s]⟩))
      simp only [relocS]; split_ifs <;> rfl
    · rfl

theorem evalF_reloc (xv : Src → FE) (V : Nat → FE) (q cst : Nat) (i : Ins) :
    (relocI q cst i).evalF xv V = i.evalF (fun s => xv (relocS q cst s)) V := by
  unfold Ins.evalF relocI
  simp only [getD_map_default (relocS q cst) rfl, relocS_valF]

theorem reloc_getD (q cst : Nat) (δ : List Ins) (k : Nat) :
    (δ.map (relocI q cst)).getD k default = relocI q cst (δ.getD k default) :=
  getD_map_default (relocI q cst) rfl δ k

theorem tassert_reloc {xv : Src → FE} {V : Nat → FE} {q cst : Nat} {δ : List Ins} :
    TAssert xv V (δ.map (relocI q cst)) ↔ TAssert (fun s => xv (relocS q cst s)) V δ := by
  have e : ∀ k o, ((δ.map (relocI q cst)).getD k default).args.getD o default =
      relocS q cst ((δ.getD k default).args.getD o default) := by
    intro k o; rw [reloc_getD]; exact getD_map_default (relocS q cst) rfl _ _
  constructor
  · intro h k hk ha
    have := h k (by simpa using hk) (by rw [reloc_getD]; exact ha)
    rw [e, e, relocS_valF, relocS_valF] at this
    exact this
  · intro h k hk ha
    rw [reloc_getD] at ha
    rw [e, e, relocS_valF, relocS_valF]
    exact h k (by simpa using hk) ha

/-! ## Write counts -/

theorem ltw_tplOf (τ : Ty) (δ : List Ins) :
    ltw τ (tplOf δ) = (δ.map fun i => Row.w τ ⟨i.op, i.ty, []⟩).sum := by
  simp only [ltw, tplOf, List.map_map]; rfl

theorem lrank_tplOf (τ : Ty) (δ : List Ins) (t : Nat) :
    lrank τ (tplOf δ) t = ((δ.take t).map fun i => Row.w τ ⟨i.op, i.ty, []⟩).sum := by
  simp only [lrank, tplOf, ← List.map_take, List.map_map]; rfl

theorem ltw_reloc (τ : Ty) (q cst : Nat) (δ : List Ins) : ltw τ (tplOf (δ.map (relocI q cst))) = ltw τ (tplOf δ) := by
  rw [ltw_tplOf, ltw_tplOf, List.map_map]; rfl

theorem lrank_reloc (τ : Ty) (q cst : Nat) (δ : List Ins) (t : Nat) :
    lrank τ (tplOf (δ.map (relocI q cst))) t = lrank τ (tplOf δ) t := by
  rw [lrank_tplOf, lrank_tplOf, ← List.map_take, List.map_map]; rfl

theorem sum_ones {δ : List Ins} {τ : Ty} (h : ∀ i ∈ δ, Row.w τ ⟨i.op, i.ty, []⟩ = 1) :
    (δ.map fun i => Row.w τ ⟨i.op, i.ty, []⟩).sum = δ.length := by
  induction δ with
  | nil => rfl
  | cons i δ ih =>
    rw [List.map_cons, List.sum_cons, h i (by simp), ih (fun j hj => h j (by simp [hj])), List.length_cons]
    omega

theorem lrank_ones {δ : List Ins} {τ : Ty} (h : ∀ i ∈ δ, Row.w τ ⟨i.op, i.ty, []⟩ = 1) {t : Nat}
    (ht : t ≤ δ.length) : lrank τ (tplOf δ) t = t := by
  rw [lrank_tplOf, sum_ones (fun i hi => h i (List.mem_of_mem_take hi)), List.length_take]; omega

theorem ltw_ones {δ : List Ins} {τ : Ty} (h : ∀ i ∈ δ, Row.w τ ⟨i.op, i.ty, []⟩ = 1) :
    ltw τ (tplOf δ) = δ.length := by
  rw [ltw_tplOf, sum_ones h]

/-! ## Loop blocks -/

theorem gk_adv_loop (p : Ptr) (dims : List Nat) (tpl : List LRow) :
    p.adv (loop dims tpl p).2 = ⟨p.k + ltw .K tpl * 2 ^ dims.sum, p.e + ltw .E tpl * 2 ^ dims.sum⟩ := by
  rw [loop_apply]
  simp only [Ptr.adv, segsW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Seg.w,
    mkLoop_tw]
  rfl

theorem gk_loop_fst (dims : List Nat) (tpl : List LRow) (p : Ptr) : (loop dims tpl p).1 = ⟨p, dims, tpl⟩ := rfl

/-- **The assertions of a loop block**, iteration by iteration. -/
theorem segsAssert_loop_iff {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr} :
    SegsAssert M p (loop dims (tplOf ins) p).2 ↔
      ∀ jf < 2 ^ dims.sum, TAssert (iterXv M (loop dims (tplOf ins) p).1 jf)
        (iterF M (loop dims (tplOf ins) p).1 jf) ins := by
  constructor
  · intro h jf hjf; exact tassert_of_loop h hjf
  · intro h
    simp only [loop_apply, SegsAssert, and_true]
    intro jf hjf t ht
    have hjf' : jf < 2 ^ dims.sum := by simpa [Block.size, Block.lsize, mkLoop] using hjf
    have hlen : t < ins.length := by simpa [mkLoop, tplOf] using ht
    have hA := h jf hjf'
    rw [show mkLoop p dims (tplOf ins) = LoopOut.blk ⟨p, dims, tplOf ins⟩ from rfl,
      show p = (⟨p, dims, tplOf ins⟩ : LoopOut).p from rfl, loop_assert_iff]
    have harg : ∀ k, LoopOut.arg M ⟨p, dims, tplOf ins⟩ jf t k =
        ((ins.getD t default).args.getD k default).valF (iterXv M ⟨p, dims, tplOf ins⟩ jf)
          (iterF M ⟨p, dims, tplOf ins⟩ jf) := by
      intro k
      simp only [LoopOut.arg]
      show (((tplOf ins).getD t default).args.getD k default).val M _ jf = _
      rw [tplOf_getD ins hlen, Ins.toLRow, getD_map_default Src.toOpd rfl]
      cases ((ins.getD t default).args.getD k default) with
      | loc k' => rw [Src.toOpd, Opd.val_cur M _ hjf']; rfl
      | prev k' => rfl
      | ext a => rfl
    have hop : ((⟨p, dims, tplOf ins⟩ : LoopOut).tpl.getD t default).op = (ins.getD t default).op := by
      show ((tplOf ins).getD t default).op = _
      rw [tplOf_getD ins hlen]; rfl
    unfold LAssert
    rw [hop]
    by_cases ha : (ins.getD t default).op = .assert0
    · rw [ha]; simp only [harg]; exact hA t hlen ha
    · split
      · rename_i heq; exact absurd heq ha
      all_goals trivial

/-! ## No assertions -/

/-- The instructions assert nothing. -/
def GNoA (δ : List Ins) : Prop := ∀ k < δ.length, (δ.getD k default).op ≠ .assert0

theorem tassert_noA {xv : Src → FE} {V : Nat → FE} {δ : List Ins} (h : GNoA δ) : TAssert xv V δ :=
  fun k hk ha => absurd ha (h k hk)

theorem gnoA_append {δ₁ δ₂ : List Ins} (h₁ : GNoA δ₁) (h₂ : GNoA δ₂) : GNoA (δ₁ ++ δ₂) := by
  intro k hk
  by_cases hk1 : k < δ₁.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk1, ← List.getD_eq_getElem?_getD]
    exact h₁ k hk1
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
    exact h₂ _ (by simp at hk; omega)

theorem gnoA_bind {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) (h₁ : GNoA (m n).2)
    (h₂ : GNoA (f (m n).1 (n + (m n).2.length)).2) : GNoA ((m >>= f) n).2 := by
  rw [tb_bind]; exact gnoA_append h₁ h₂

theorem gnoA_pure {α : Type} (a : α) (n : Nat) : GNoA ((pure a : TB α) n).2 := fun k hk => by simp [tb_pure] at hk

theorem gnoA_emit {i : Ins} (n : Nat) (h : i.op ≠ .assert0) : GNoA (emit i n).2 := by
  intro k hk
  simp only [emit, List.length_singleton] at hk
  rw [show k = 0 by omega]; exact h

theorem gnoA_mul (a b d : Src) (n : Nat) : GNoA (gMul a b d n).2 := gnoA_emit n (by simp [mulI])
theorem gnoA_lin (k k' : FK) (a b : Src) (n : Nat) : GNoA (gLin k k' a b n).2 := gnoA_emit n (by simp [linI])
theorem gnoA_zero (a : Src) (n : Nat) : GNoA (gZero a n).2 := gnoA_emit n (by simp [linI])
theorem gnoA_one (a : Src) (n : Nat) : GNoA (gOne a n).2 := gnoA_emit n (by simp [linI])
theorem gnoA_load (q : Nat) (str : List Nat) (n : Nat) : GNoA (gLoad q str n).2 := gnoA_emit n (by simp [loadI])

theorem gnoA_mapTB {α : Type} {f : α → TB Src} (hf : ∀ a n, GNoA (f a n).2) :
    ∀ (as : List α) (n : Nat), GNoA (mapTB f as n).2
  | [], n => gnoA_pure _ n
  | a :: as, n => gnoA_bind _ _ n (hf a n) (gnoA_bind _ _ _ (gnoA_mapTB hf as _) (gnoA_pure _ _))

theorem gnoA_gSum : ∀ (s : Src) (cs : List Src) (n : Nat), GNoA (gSum s cs n).2
  | s, [], n => gnoA_pure _ n
  | s, c :: cs, n => gnoA_bind _ _ n (gnoA_lin _ _ _ _ _) (gnoA_gSum _ cs _)

theorem gnoA_gDot : ∀ (acc : Src) (cds : List (Src × Src)) (n : Nat), GNoA (gDot acc cds n).2
  | acc, [], n => gnoA_pure _ n
  | acc, cd :: rest, n => gnoA_bind _ _ n (gnoA_mul _ _ _ _) (gnoA_gDot _ rest _)

theorem gnoA_gEqTab (z : Src) : ∀ (pt tab : List Src) (n : Nat), GNoA (gEqTab z tab pt n).2
  | [], tab, n => gnoA_pure _ n
  | r :: rs, tab, n => gnoA_bind _ _ n
      (gnoA_bind _ _ n (gnoA_lin _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_mul _ _ _ _) _ _)
        (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_mul _ _ _ _) _ _) (gnoA_pure _ _))))
      (gnoA_gEqTab z rs _ _)

theorem gnoA_gSumMap (z : Src) (k : Nat) {f : Nat → TB Src} (hf : ∀ c n, GNoA (f c n).2) (n : Nat) :
    GNoA (gSumMap z k f n).2 := gnoA_bind _ _ n (gnoA_mapTB hf _ _) (gnoA_gSum _ _ _)

theorem gnoA_gLaneForm (z : Src) (B : List Src) (R : Nat → Src) (l n : Nat) : GNoA (gLaneForm z B R l n).2 :=
  gnoA_bind _ _ n (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_gDot _ _ _) (gnoA_gDot _ _ _))

theorem gnoA_gFoldPairs (z r1 r : Src) : ∀ (l : List Src) (n : Nat), GNoA (gFoldPairs z r1 r l n).2
  | a :: b :: rest, n => gnoA_bind _ _ n (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
      (gnoA_bind _ _ _ (gnoA_gFoldPairs z r1 r rest _) (gnoA_pure _ _)))
  | [], n => gnoA_pure _ n
  | [_], n => gnoA_pure _ n

theorem gnoA_gMle (z : Src) : ∀ (cur pt : List Src) (n : Nat), GNoA (gMle z cur pt n).2
  | cur, [], n => gnoA_pure _ n
  | cur, r :: rs, n => gnoA_bind _ _ n (gnoA_lin _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_gFoldPairs _ _ _ _ _)
      (gnoA_gMle z _ rs _))

/-! ## List facts -/

theorem gk_getD_app_right (A B : List FE) {i k : Nat} (hk : A.length ≤ k) (hi : k - A.length = i) :
    (A ++ B).getD k 0 = B.getD i 0 := by
  subst hi; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hk]

/-! ## Peeling a template program -/

theorem tb_peel {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β)
    (h : THold xv V n ((m >>= f) n).2) :
    THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 ∧
      ((m >>= f) n).1 = (f (m n).1 (n + (m n).2.length)).1 :=
  ⟨((thold_bind m f).mp h).1, ((thold_bind m f).mp h).2, rfl⟩

theorem gk_eqTab_one {xv : Src → FE} {V : Nat → FE} {z one : Src} (hz : z.valF xv V = 0)
    (h1 : one.valF xv V = 1) (pt : List Src) (n : Nat) (h : THold xv V n (gEqTab z [one] pt n).2) :
    vals xv V (gEqTab z [one] pt n).1 = eqKernel (vals xv V pt) := by
  rw [vals, gEqTab_spec hz pt [one] n h, List.map_singleton, h1]; rfl

/-! ## The first-claim block -/

/-- The values of the lane challenges' `eq` table. -/
def lanePt (u : Nat → FE) (qs : Nat) : List FE := (List.range 5).map fun k => u (qs + 9 * (k + 1))

/-! ## Assertions of template programs -/

theorem tassert_bind_noA {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β)
    (hm : GNoA (m n).2) :
    TAssert xv V ((m >>= f) n).2 ↔ TAssert xv V (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tassert_bind]; exact ⟨fun h => h.2, fun h => ⟨tassert_noA hm, h⟩⟩

theorem gAssert_iff {xv : Src → FE} {V : Nat → FE} {n : Nat} {a g : Src} :
    TAssert xv V (gAssert a g n).2 ↔ g.valF xv V * a.valF xv V = 0 := by
  refine ⟨gAssert_spec, fun h k hk _ => ?_⟩
  simp only [gAssert, emitA, List.length_singleton] at hk
  rw [show k = 0 by omega]; exact h

/-! ## `multilinearEval` -/

theorem gFoldPairs_spec {xv : Src → FE} {V : Nat → FE} {z r1 r : Src} (hz : z.valF xv V = 0)
    (h1 : r1.valF xv V = 1 + r.valF xv V) : ∀ (l : List Src) (n : Nat), THold xv V n (gFoldPairs z r1 r l n).2 →
      vals xv V (gFoldPairs z r1 r l n).1 = foldPairs (r.valF xv V) (vals xv V l)
  | a :: b :: rest, n, h => by
    simp only [gFoldPairs] at h ⊢
    obtain ⟨g1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    obtain ⟨g2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    obtain ⟨g3, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
    rw [tb_pure]
    simp only [vals, List.map_cons, foldPairs] at g3 ⊢
    rw [gMul_spec g2, gMul_spec g1, hz, add_zero, h1, ← vals, gFoldPairs_spec hz h1 rest _ g3]
  | [], _, _ => rfl
  | [_], _, _ => rfl

theorem gMle_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) :
    ∀ (pt cur : List Src) (n : Nat), THold xv V n (gMle z cur pt n).2 →
      (gMle z cur pt n).1.valF xv V = multilinearEval (vals xv V cur) (vals xv V pt)
  | [], cur, n, _ => by
    simp only [gMle, tb_pure, multilinearEval, vals, List.map_nil, List.foldl_nil]
    cases cur <;> simp [hz]
  | r :: rs, cur, n, h => by
    simp only [gMle] at h ⊢
    obtain ⟨g1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    obtain ⟨g2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    rw [gMle_spec hz rs _ _ h, gFoldPairs_spec hz (gOne_spec g1) cur _ g2]
    simp only [multilinearEval, vals, List.map_cons, List.foldl_cons]

/-! ## The first opening block -/

/-- **The first opening block**: its exports and its check. -/
theorem fin1TB_spec {xv : Src → FE} {V : Nat → FE} {qO : Nat} {b : Src} {slot1 slot3 aF : List Src}
    {seg val1 : Src} {lanes : List Src} {u : Nat → FE}
    (hu : ∀ m, qO + 90 ≤ m → m ≤ qO + 432 → lv xv [] m = u m) (hlanes : 25 ≤ lanes.length)
    (hs1 : slot1.length = 6) {n : Nat} (h : THold xv V n (fin1TB qO b slot1 slot3 aF seg val1 lanes n).2) :
    (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.z.valF xv V = 0 ∧
    Fx (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.z ∧
    (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.word.valF xv V = u (qO + 90) ∧
    Fx (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.word ∧
    (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.sl.length = 128 ∧
    (∀ x ∈ (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.sl, Fx x) ∧
    (∀ k < 128, ((fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.sl.getD k default).valF xv V =
      u (qO + 243 + 3 * (k % 64))) ∧
    vals xv V (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.e3 = eqKernel (vals xv V slot3) ∧
    (∀ x ∈ (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.e3, Fx x) ∧
    vals xv V (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.ea = eqKernel (vals xv V aF) ∧
    (∀ x ∈ (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.ea, Fx x) ∧
    (TAssert xv V (fin1TB qO b slot1 slot3 aF seg val1 lanes n).2 ↔
      b.valF xv V * (((List.range 25).map fun l => (eqKernel (vals xv V slot1)).getD (25 + l) 0 *
        (vals xv V lanes).getD l 0).sum * (1 + seg.valF xv V) * u (qO + 90) + val1.valF xv V) = 0) := by
  unfold fin1TB at h ⊢
  -- the slices
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_mapTB (fun _ _ => gnoA_load _ _ _) _ _)]
  clear e
  have esl : ∀ k < 128, ((mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1.getD k
      default).valF xv V = u (qO + 243 + 3 * (k % 64)) := by
    have := forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = u (qO + 243 + 3 * (k % 64))) _
      (fun k hk m hm => by
        rw [gLoad_lv hm, hu _ (by omega) (by have := Nat.mod_lt k (show 0 < 64 by omega); omega)]) _ h1)
    intro k hk
    rw [getD_vals _ (by rw [mapTB_length]; simpa using hk), vals, this]
    simp [List.getD_eq_getElem?_getD, hk]
  have fsl : ∀ x ∈ (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1, Fx x :=
    fx_mapTB (fun _ _ => fx_emit _ _) _ _
  have lsl : (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1.length = 128 := by
    rw [mapTB_length]; rfl
  generalize (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1 = sl at h esl fsl lsl ⊢
  generalize n + (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).2.length = n1 at h ⊢
  -- z, one, the word
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_zero _ _)]; clear e
  have ez := gZero_spec h2; have fz : Fx (gZero b n1).1 := fx_emit _ _
  generalize (gZero b n1).1 = z at h ez fz ⊢; generalize n1 + (gZero b n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_one _ _)]; clear e
  have eo := gOne_spec h3; have fo : Fx (gOne z n2).1 := fx_emit _ _
  rw [ez, add_zero] at eo
  generalize (gOne z n2).1 = one at h eo fo ⊢; generalize n2 + (gOne z n2).2.length = n3 at h ⊢
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_load _ _ _)]; clear e
  have ew := gLoad_lv h4; have fw : Fx (gLoad (qO + 90) [] n3).1 := fx_emit _ _
  rw [hu _ le_rfl (by omega)] at ew
  generalize (gLoad (qO + 90) [] n3).1 = word at h ew fw ⊢; generalize n3 + (gLoad (qO + 90) [] n3).2.length = n4 at h ⊢
  -- the committed check
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]; clear e
  have e1 := gk_eqTab_one ez eo slot1 n4 h5
  generalize (gEqTab z [one] slot1 n4).1 = t1 at h e1 ⊢; generalize n4 + (gEqTab z [one] slot1 n4).2.length = n5 at h ⊢
  have ht1 : t1.length = 64 := by
    have := congrArg List.length e1; rw [List.length_map, eqKernel_length, List.length_map, hs1] at this; simpa using this
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gDot _ _ _)]; clear e
  have ewc := gDot_spec _ _ _ h6
  generalize (gDot z ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) n5).1 = wc
    at h ewc ⊢
  generalize n5 + (gDot z ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) n5).2.length
    = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_one _ _)]; clear e
  have ef := gOne_spec h7
  generalize (gOne seg n6).1 = f at h ef ⊢; generalize n6 + (gOne seg n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_mul _ _ _ _)]; clear e
  have eww := gMul_spec h8
  generalize (gMul wc f z n7).1 = w at h eww ⊢; generalize n7 + (gMul wc f z n7).2.length = n8 at h ⊢
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_mul _ _ _ _)]; clear e
  have et := gMul_spec h9
  generalize (gMul w word val1 n8).1 = t at h et ⊢; generalize n8 + (gMul w word val1 n8).2.length = n9 at h ⊢
  obtain ⟨-, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind, gAssert_iff]; clear e
  generalize n9 + (gAssert t b n9).2.length = n10 at h ⊢
  -- the two tables
  obtain ⟨h11, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]; clear e
  have e3 := gk_eqTab_one ez eo slot3 n10 h11
  have f3 := fx_gEqTab z slot3 [one] n10 (by simpa using fo)
  generalize (gEqTab z [one] slot3 n10).1 = t3 at h e3 f3 ⊢
  generalize n10 + (gEqTab z [one] slot3 n10).2.length = n11 at h ⊢
  obtain ⟨h12, -, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]; clear e
  have ea := gk_eqTab_one ez eo aF n11 h12
  have fa := fx_gEqTab z aF [one] n11 (by simpa using fo)
  generalize (gEqTab z [one] aF n11).1 = ta at ea fa ⊢
  rw [tb_pure]
  refine ⟨ez, fz, ew, fw, lsl, fsl, esl, e3, f3, ea, fa, ?_⟩
  rw [and_iff_left (tassert_noA (fun k hk => by simp at hk)), et, eww, ef, ewc, ez, add_zero, zero_add]
  have hs : ((List.map (fun cd => cd.1.valF xv V * cd.2.valF xv V)
      ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)))).sum =
      ((List.range 25).map fun l => (eqKernel (vals xv V slot1)).getD (25 + l) 0 * (vals xv V lanes).getD l 0).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply]
    rw [getD_vals _ (by omega), getD_vals _ (by omega), e1]
  rw [hs, ew]


/-! ## The input check block -/

theorem fin2_lane {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {B : List Src} (hB : 25 ≤ B.length)
    (R : Nat → Src) {e3 : List Src} {x x1 : Src} (hx1 : x1.valF xv V = 1 + x.valF xv V) {l : Nat} (hl : l < 25)
    (m : Nat) (h : THold xv V m ((gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
      gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) m).2) :
    ((gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
      gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) m).1.valF xv V =
      ((e3.getD (25 + l) default).valF xv V * x.valF xv V + (e3.getD l default).valF xv V * (1 + x.valF xv V)) *
        laneForm (vals xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have el := gLaneForm_spec hz hB R hl m g1
  obtain ⟨g2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  obtain ⟨g3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  rw [gMul_spec h, gMul_spec g3, gMul_spec g2, el, hz, add_zero, add_zero, hx1]

theorem gnoA_fin2_lane (z : Src) (B : List Src) (R : Nat → Src) (e3 : List Src) (x x1 : Src) (l m : Nat) :
    GNoA ((gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
      gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) m).2 :=
  gnoA_bind _ _ _ (gnoA_gLaneForm _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_mul _ _ _ _)))

/-- **The input check block**: its assertion. -/
theorem fin2TB_spec {xv : Src → FE} {V : Nat → FE} {b z : Src} {B : List Src} {R : Nat → Src} {e3 : List Src}
    {x : Src} {mu low : List Src} {val3 : Src} (hz : z.valF xv V = 0) (hB : 25 ≤ B.length) (he3 : 50 ≤ e3.length)
    {n : Nat} (h : THold xv V n (fin2TB b z B R e3 x mu low val3 n).2) :
    TAssert xv V (fin2TB b z B R e3 x mu low val3 n).2 ↔
      b.valF xv V * (multilinearEval (vals xv V mu) (vals xv V low) *
        ((List.range 25).map fun l => ((vals xv V e3).getD (25 + l) 0 * x.valF xv V +
          (vals xv V e3).getD l 0 * (1 + x.valF xv V)) * laneForm (vals xv V B) (fun s => (R s).valF xv V) l).sum +
        val3.valF xv V) = 0 := by
  unfold fin2TB at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_one _ _)]; clear e
  have ex := gOne_spec h1
  generalize (gOne x n).1 = x1 at h ex ⊢; generalize n + (gOne x n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h
  rw [tassert_bind_noA _ _ (gnoA_gSumMap _ _ (fun c m => gnoA_fin2_lane z B R e3 x x1 c m) _)]; clear e
  have et := gSumMap_spec' hz (F := fun l => ((vals xv V e3).getD (25 + l) 0 * x.valF xv V +
      (vals xv V e3).getD l 0 * (1 + x.valF xv V)) * laneForm (vals xv V B) (fun s => (R s).valF xv V) l)
    (fun l hl m hm => by
      rw [fin2_lane hz hB R ex hl m hm, getD_vals _ (by omega), getD_vals _ (by omega)]) n1 h2
  generalize (gSumMap z 25 _ n1).1 = tot at h et ⊢
  generalize n1 + (gSumMap z 25 _ n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gMle _ _ _ _)]; clear e
  have em := gMle_spec hz low mu n2 h3
  generalize (gMle z mu low n2).1 = mle at h em ⊢; generalize n2 + (gMle z mu low n2).2.length = n3 at h ⊢
  obtain ⟨h4, -, e⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mul _ _ _ _), gAssert_iff]; clear e
  rw [gMul_spec h4, em, et]

/-! ## The rotated sums -/

theorem evalF_mulI (xv : Src → FE) (V : Nat → FE) (a b d : Src) :
    (mulI a b d).evalF xv V = a.valF xv V * b.valF xv V + d.valF xv V := rfl

/-- **The rotation block**: iteration `i`'s last row is `Σ_w A(w)·cell(sb + w + i)`. -/
theorem rot_spec {c : Ctx} {M : Mem} {p : Ptr} {ea : List Src} {sb : Nat} {z : Src}
    (h : SegsHold c M p (loop [6] (tplOf (rotIns ea sb z)) p).2) {A : Nat → FE}
    (hA : ∀ w < 64, ∀ jf, (ea.getD w default).valF (iterXv M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf)
      (iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf) = A w)
    (hz : ∀ jf, z.valF (iterXv M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf)
      (iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf) = 0) {i : Nat} (hi : i < 64) :
    iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 i 63 =
      ((List.range 64).map fun w => A w * M.rd .E (sb + w + 1 * i)).sum := by
  have hH := thold_of_loop h (jf := i) (by simpa using hi)
  have hg : ∀ w < 64, (rotIns ea sb z).getD w default =
      mulI (ea.getD w default) (.ext ⟨.E, sb + w, [1]⟩) (if w = 0 then z else .loc (w - 1)) := by
    intro w hw; simp [rotIns, List.getD_eq_getElem?_getD, hw]
  have hx : ∀ w, iterXv M (loop [6] (tplOf (rotIns ea sb z)) p).1 i (.ext ⟨.E, sb + w, [1]⟩) =
      M.rd .E (sb + w + 1 * i) := fun w => iterXv_ext1 M _ rfl (by simpa using hi) _ _ _
  have key : ∀ w < 64, iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 i w =
      ((List.range (w + 1)).map fun w' => A w' * M.rd .E (sb + w' + 1 * i)).sum := by
    intro w
    induction w with
    | zero =>
      intro _
      have := hH 0 (by simp [rotIns]) (by rw [hg 0 (by omega)]; exact Or.inl rfl)
      rw [Nat.zero_add, hg 0 (by omega), evalF_mulI, if_pos rfl, hA 0 (by omega), hz, add_zero] at this
      rw [this]
      show A 0 * iterXv M _ i (.ext ⟨.E, sb + 0, [1]⟩) = _
      rw [hx]
      simp
    | succ w ih =>
      intro hw
      have := hH (w + 1) (by simp [rotIns]; omega) (by rw [hg _ hw]; exact Or.inl rfl)
      rw [Nat.zero_add, hg _ hw, evalF_mulI, if_neg (Nat.succ_ne_zero w), hA _ hw] at this
      rw [this, List.range_succ (n := w + 1), List.map_append, List.sum_append]
      show A (w + 1) * iterXv M _ i (.ext ⟨.E, sb + (w + 1), [1]⟩) + iterF M _ i (w + 1 - 1) = _
      rw [hx, Nat.add_sub_cancel, ih (by omega)]
      simp [add_comm]
  exact key 63 (by omega)

/-! ## The constants block -/

theorem cstI_ty (b : Src) (t : Nat) : (cstI b t).ty = .K := by unfold cstI; split <;> rfl

theorem cstI_op (b : Src) (t : Nat) : ∃ k k', (cstI b t).op = .lin k k' := by
  unfold cstI; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem cstIns_w (b : Src) : ∀ i ∈ cstIns b, Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
  intro i hi
  simp only [cstIns, List.mem_map, List.mem_range] at hi
  obtain ⟨t, -, rfl⟩ := hi
  obtain ⟨k, k', hk⟩ := cstI_op b t
  simp [Row.w, Row.writes, hk, cstI_ty]

/-- **The constants block**: cell `p.k + t` holds constant `t % 16` of iteration `t / 16`. -/
theorem cst_spec {c : Ctx} {M : Mem} {p : Ptr} {bc : Cell}
    (h : SegsHold c M p (loop [] (tplOf (cstIns (gkS bc))) p).2) {t : Nat} (ht : t < 256) :
    FE.ofK (M.k (p.k + t)) = if t % 16 = 15 then (if t / 16 < 12 then bc.val M else 0)
      else FE.ofK (cstK (t / 16) (t % 16)) := by
  have hH := thold_of_loop h (jf := 0) (by simp)
  have hg : (cstIns (gkS bc)).getD t default = cstI (gkS bc) t := by
    simp [cstIns, List.getD_eq_getElem?_getD, ht]
  have := hH t (by simp [cstIns]; omega) (by rw [hg]; obtain ⟨k, k', hk⟩ := cstI_op (gkS bc) t; exact Or.inr (Or.inl ⟨k, k', hk⟩))
  rw [Nat.zero_add, hg] at this
  have hc : iterF M (loop [] (tplOf (cstIns (gkS bc))) p).1 0 t = FE.ofK (M.k (p.k + t)) := by
    rw [gk_loop_fst]
    show Cell.val M (LoopOut.cell ⟨p, [], tplOf (cstIns (gkS bc))⟩ t 0) = _
    have hty : ((tplOf (cstIns (gkS bc))).getD t default).ty = .K := by
      rw [tplOf_getD _ (by simp [cstIns]; omega), hg]; exact cstI_ty _ _
    simp only [LoopOut.cell, hty, Cell.val, Ptr.at,
      lrank_ones (δ := cstIns (gkS bc)) (cstIns_w _) (show t ≤ (cstIns (gkS bc)).length by simp [cstIns]; omega),
      Nat.mul_zero, Nat.add_zero]
    rfl
  rw [← hc, this]
  have hb : (gkS bc).valF (iterXv M (loop [] (tplOf (cstIns (gkS bc))) p).1 0)
      (iterF M (loop [] (tplOf (cstIns (gkS bc))) p).1 0) = bc.val M := gk_iterXv_gkS M _ 0 bc
  unfold cstI
  split_ifs with h1 h2
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_zero, zero_mul, add_zero]
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_one, one_mul, add_zero, FE_add_self,
      ofK_zero]
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_one, one_mul, FE_add_self, zero_add]

theorem ofK_rcK (rc : UInt64) (i : Nat) : FE.ofK (rcK rc i) = rcBit rc i := by
  unfold rcK rcBit; split_ifs <;> rfl


/-! ## The layers -/

/-- A relocated row's type (stated once, so that no proof leaves `relocI`/`toLRow` to the kernel's
unfolding, which would unfold the template `layIns P` first). -/
theorem relocI_toLRow_ty (q cst : Nat) (i : Ins) : (relocI q cst i).toLRow.ty = i.ty := rfl

/-! ## Small facts for the assembly -/

theorem gnoA_map {α : Type} (f : α → Ins) (l : List α) (h : ∀ a, (f a).op ≠ .assert0) : GNoA (l.map f) := by
  intro k hk
  rw [List.getD_eq_getElem _ _ hk, List.getElem_map]; exact h _

/-! ## Bind and pointer equations -/

theorem gk_bind_fst {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

theorem gk_getPtr (p : Ptr) : getPtr p = (p, []) := rfl

/-! The same three equations as proof-producing `simp` rules: as `rfl` lemmas `simp` applies them
definitionally and leaves the kernel to re-derive each step by unfolding `>>=` (it then compares
the gadget's blocks and unfolds the layer template; 30 s). Stated with a proof that is not `rfl`,
`simp` cites them and the kernel only instantiates them. -/

theorem gk_bind_fst_eq {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := (gk_bind_fst m f p).trans rfl

theorem gk_getPtr_eq (p : Ptr) : getPtr p = (p, []) := (gk_getPtr p).trans rfl

theorem gk_pure_apply_eq {α : Type} (x : α) (p : Ptr) : (pure x : BM α) p = (x, []) := (pure_apply x p).trans rfl

end Lvm.Q1
