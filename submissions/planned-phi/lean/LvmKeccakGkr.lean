-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Gkr.lean` (formal rev 40f877dc) as `LvmKeccakGkr` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Gkr

  The round-by-round soundness of the Keccak reduction `verifyKeccak`: a doom specification
  from "no candidate makes the table's output claims true" to "no candidate makes the column
  claims and slice claims the reduction leaves true", with the escape of every challenge.
-/
import LvmKeccakCandidate

-- ===== merged from `LvmKeccakSlotWeights` (GOLF module merge: `LvmKeccakSlotWeights.lean` is now a stub importing `LvmKeccakGkr`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/SlotWeights.lean` (formal rev 40f877dc) as `LvmKeccakSlotWeights` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.SlotWeights

  `keccakSlotWeights` and the fold of `keccakOpen` in closed form: the weight a claim puts on
  each (slot, slice), and its multilinear extension at the slot point.
-/

/-!
# The slot weights

`keccakSlotWeights logSteps claim first count` (the weights of `keccakOpen`) writes, for each
segment `seg < count` and position `j = z + 64ℓ`, the weight `eq(point_P, seg)·w_j` at row
`25(first + seg) + ℓ`, column `z` of a `64 × 64` array of zeros. `slotWeights_getD`: entry `(o, z)`
is `slotW … o z`, the weight of segment `o / 25 - first` at position `64·(o mod 25) + z` on the rows
`25·first ≤ o < 25·(first + count)`, `0` elsewhere. `foldAll_eq`: `keccakOpen`'s fold of the rows
along the slot challenges is the rows' multilinear extension at the slot point, column by column,
which the Rust `open` (`crates/verifier/src/keccak.rs:198-223`) computes directly, weighting each
slot's row by `eq_kernel(slot)`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile Finset

section

/-! ## Arrays of rows -/

/-- Entry `(o, z)` of an array of rows, `0` outside. -/
def rowsF (rows : Array (Array E)) (o z : ℕ) : E := (rows.getD o #[]).getD z 0

/-- Sixty-four rows of sixty-four entries. -/
def Sized (rows : Array (Array E)) : Prop := rows.size = 64 ∧ ∀ o < 64, (rows.getD o #[]).size = 64

theorem modify_getD (rows : Array (Array E)) (i o : ℕ) (f : Array E → Array E) :
    (rows.modify i f).getD o #[] = if i = o ∧ o < rows.size then f (rows.getD o #[])
      else rows.getD o #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = o
  · subst h1
    by_cases h2 : i < rows.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem modify_step {rows : Array (Array E)} (hs : Sized rows) (i z' : ℕ) (x : E) :
    Sized (rows.modify i fun row ↦ row.setIfInBounds z' x) ∧
      ∀ o z, rowsF (rows.modify i fun row ↦ row.setIfInBounds z' x) o z =
        if i = o ∧ z' = z ∧ o < 64 ∧ z < 64 then x else rowsF rows o z := by
  refine ⟨⟨by simp [hs.1], fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
  · rw [modify_getD]
    split_ifs
    · rw [Array.size_setIfInBounds]; exact hs.2 o ho
    · exact hs.2 o ho
  · rw [rowsF, modify_getD, rowsF]
    by_cases h1 : i = o ∧ o < rows.size
    · rw [ite_eq_left h1, setIfInBounds_getD]
      have ho : o < 64 := hs.1 ▸ h1.2
      rw [hs.2 o ho]
      by_cases h2 : z' = z ∧ z' < 64
      · rw [ite_eq_left h2, ite_eq_left (show i = o ∧ z' = z ∧ o < 64 ∧ z < 64 from
          ⟨h1.1, h2.1, ho, h2.1 ▸ h2.2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
          fun h ↦ h2 ⟨h.2.1, h.2.1 ▸ h.2.2.2⟩)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
        fun h ↦ h1 ⟨h.1, hs.1 ▸ h.2.2.1⟩)]

/-- The inner loop of `keccakSlotWeights`: one segment's writes, at rows `b .. b + 24`. -/
theorem inner_rows (rows0 : Array (Array E)) (hs : Sized rows0) (b : ℕ) (V : ℕ → E)
    (hb : b + 25 ≤ 64) : ∀ J, J ≤ 1600 →
      Sized ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) ∧
      ∀ o z, rowsF ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) o z =
        if b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J then V (64 * (o - b) + z)
        else rowsF rows0 o z
  | 0, _ => ⟨hs, fun o z ↦ by simp⟩
  | J + 1, hJ => by
    obtain ⟨hs', hg⟩ := inner_rows rows0 hs b V hb J (by (clear * - hJ; omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs'', hg''⟩ := modify_step hs' (b + J / 64) (J % 64) (V J)
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
def slotW (segments w : List E) (first count o z : ℕ) : E :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

/-- The outer loop of `keccakSlotWeights`. -/
theorem outer_rows (segments w : List E) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∀ S, S ≤ count →
      Sized ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) ∧
      ∀ o z, rowsF ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) o z = slotW segments w first S o z
  | 0, _ => by
    refine ⟨⟨by simp, fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
    · simp [Array.getD_eq_getD_getElem?, ho]
    · simp only [List.range_zero, List.foldl_nil, rowsF, slotW]
      rw [ite_eq_right (by (clear * -; omega))]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      by_cases h : o < 64
      · by_cases h' : z < 64 <;> simp [h, h']
      · simp [h]
  | S + 1, hS => by
    obtain ⟨hs, hg⟩ := outer_rows segments w first count hfc S (by (clear * - hS; omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_rows _ hs (25 * (first + S))
      (fun j ↦ segments.getD S 0 * w.toArray.getD j 0) (by (clear * - hfc hS; omega)) keccakBits le_rfl
    have hk : keccakBits = 1600 := rfl
    refine ⟨hs', fun o z ↦ ?_⟩
    rw [hg', hg, slotW, slotW]
    by_cases h1 : 25 * (first + S) ≤ o ∧ o < 25 * (first + S) + 25 ∧ z < 64 ∧
        64 * (o - 25 * (first + S)) + z < keccakBits
    · rw [ite_eq_left h1, ite_eq_left (by (clear * - h1; omega)), array_getD_toArray]
      have e1 : o / 25 - first = S := by (clear * - hfc hS h1; omega)
      have e2 : o % 25 = o - 25 * (first + S) := by (clear * - hk h1 e1; omega)
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : 25 * first ≤ o ∧ o < 25 * (first + S) ∧ z < 64
      · rw [ite_eq_left h2, ite_eq_left (by (clear * - h2; omega))]
      · rw [ite_eq_right h2, ite_eq_right (by (clear * - hk h1 h2; omega))]

theorem qkeccakSlotBits_eq : qkeccakSlotBits = 6 := by decide

/-- **`keccakSlotWeights` in closed form.** -/
theorem toListRows_getD (A : Array (Array E)) {o : ℕ} (ho : o < A.size) (z : ℕ) :
    ((A.toList.map Array.toList).getD o []).getD z 0 = (A.getD o #[]).getD z 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem toListRows_row (A : Array (Array E)) {o : ℕ} (ho : o < A.size) :
    (A.toList.map Array.toList).getD o [] = (A.getD o #[]).toList := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem mapRange_getD (f : ℕ → List E) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem slotWeights_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o z : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).getD z 0 =
      slotW (eqKernel (claim.point.drop (logSteps - 4))) claim.weights first count o z := by
  obtain ⟨hs, hg⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  rw [← hg o z, rowsF]
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  exact toListRows_getD _ (by rw [hs.1]; exact ho) z

theorem slotWeights_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) : (keccakSlotWeights logSteps claim first count).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl, List.length_map,
    Array.length_toList]
  exact hs.1

theorem slotWeights_row_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [toListRows_row _ (by rw [hs.1]; exact ho), Array.length_toList]
  exact hs.2 o ho

/-! ## The fold along the slot -/

/-- `keccakOpen`'s fold of the rows along the slot challenges. -/
def foldAll (slot : List E) (rows : List (List E)) : List (List E) :=
  slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

theorem zipWith_getD (f : E → E → E) (l₁ l₂ : List E) {z : ℕ} (h₁ : z < l₁.length)
    (h₂ : z < l₂.length) : (List.zipWith f l₁ l₂).getD z 0 = f (l₁.getD z 0) (l₂.getD z 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

/-- **The fold is the multilinear extension**, column by column. -/
theorem foldAll_eq : ∀ (pt : List E) (rows : List (List E)), rows.length = 2 ^ pt.length →
    (∀ o < rows.length, (rows.getD o []).length = 64) →
    (foldAll pt rows).length = 1 ∧ ((foldAll pt rows).headD []).length = 64 ∧
      ∀ z < 64, ((foldAll pt rows).headD []).getD z 0 =
        ∑ o ∈ range (2 ^ pt.length), eqAt pt o * (rows.getD o []).getD z 0
  | [], rows, hl, hr => by
    rcases rows with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · simp at hl
    · exact ⟨rfl, hr 0 (by simp), fun z _ ↦ by simp [foldAll]⟩
    · simp at hl
  | c :: pt, rows, hl, hr => by
    have step : foldAll (c :: pt) rows = foldAll pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) := rfl
    have hl' : rows.length / 2 = 2 ^ pt.length := by
      rw [hl, List.length_cons, pow_succ]; (clear * -; omega)
    have hrow : ∀ i < rows.length / 2, ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])).getD i [] =
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) []) := by
      intro i hi
      exact mapRange_getD _ hi
    obtain ⟨h1, h2, h3⟩ := foldAll_eq pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (by rw [List.length_map, List.length_range, hl'])
      (fun i hi ↦ by
        have hi2 : i < rows.length / 2 := by simpa using hi
        rw [hrow i hi2, List.length_zipWith, hr _ (by (clear * - hl hl' hi2; omega)), hr _ (by (clear * - hl hl' hi2; omega)), min_self])
    rw [step]
    refine ⟨h1, h2, fun z hz ↦ ?_⟩
    rw [h3 z hz, List.length_cons, sum_cube_succ]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [← hl'] at hi' 
    rw [hrow i (by omega), zipWith_getD _ _ _ (by rw [hr _ (by (clear * - hl hl' hi'; omega))]; exact hz)
      (by rw [hr _ (by (clear * - hl hl' hi'; omega))]; exact hz), eqAt_cons, eqAt_cons]
    have e1 : 2 * i % 2 = 0 := by (clear * -; omega)
    have e2 : (2 * i + 1) % 2 = 1 := by (clear * - e1; omega)
    have e3 : 2 * i / 2 = i := by (clear * - e1; omega)
    have e4 : (2 * i + 1) / 2 = i := by (clear * - e1 e2; omega)
    simp only [e1, e2, e3, e4, ite_true, zero_ne_one, ite_false]
    ring

/-- `keccakOpen` (`open`, `keccak.rs:198-223`), with the fold named. -/
theorem keccakOpen_eq (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    keccakOpen logSteps claim first count value =
      sumcheck value 3 (List.replicate qkeccakSlotBits none) >>= fun x ↦
        VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights logSteps claim first
            count)).headD [],
          x.2) := rfl

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakSlotWeights` =====

-- ===== merged from `LvmKeccakStart` (GOLF module merge: `LvmKeccakStart.lean` is now a stub importing `LvmKeccakGkr`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Start.lean` (formal rev 40f877dc) as `LvmKeccakStart` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Start

  The start of `verifyKeccak`: the segment and lane challenges, the committed middle-state value,
  and the first claim, a random combination of the fifty lane claims of the two segments.
-/

/-!
# The first claim

`verify_keccak` (`crates/verifier/src/keccak.rs:247-263`) draws the segment challenge `r_seg` and
five lane challenges, reads `committed` and forms the first claim at the point `(r_pack, r_seg)`
with instance weights `eq(r_low, ·)` and position weights `eq(r_lane, ℓ)·x^z` (`firstClaim`). On a
candidate (`firstClaim_true`), the claim's sum is

  `Σ_m eq(r_seg, m) Σ_ℓ eq(r_lane, ℓ) · stepMle inst (lane ℓ of segment m's output)`,

a random combination of the fifty lane claims of the two segments (`doc/leanvm`
§`keccak:segments`, "The first claim"). The candidate is alive after `committed` when that value
opens the committed middle state (`OpenTrue`) and the first claim holds; before, when the
mismatch table `startDelta` (the fifty differences between the lanes' claimed and true values)
has a zero extension at the challenges drawn (`ZeroOn`). `startSpec`: the six challenges escape
at `L₀/|E|` each.

`sum_split`: the claims' (pack, segment) and instance sums are a sum over the steps with the
equality weights of `(r_low, r_pack)`, the reading of every claim on the committed states.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal

section

/-! ## Splitting the point -/

/-- A sum over (pack, segment) and instance, at `(b, seg)` and `a`, is a sum over the steps at
`a ++ b`, segment by segment. -/
theorem sum_split {P : ℕ} {a b seg : List E} (ha : a.length = 4) (hb : b.length = P)
    (G : ℕ → ℕ → E) :
    ∑ z ∈ range (2 ^ (P + 1)), eqAt (b ++ seg) z *
        ∑ i ∈ range 16, eqAt a i * G (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) =
      ∑ m ∈ range 2, eqAt seg m * ∑ x ∈ range (2 ^ (P + 4)), eqAt (a ++ b) x * G m x := by
  rw [pow_succ, mul_comm (2 ^ P) 2, sum_range_mul 2 (2 ^ P)]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [show 2 ^ (P + 4) = 2 ^ P * 16 by rw [pow_add]; rfl, sum_range_mul (2 ^ P) 16,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hy' := Finset.mem_range.1 hy
  have hd : (2 ^ P * m + y) / 2 ^ P = m := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy', zero_add]
  have hmod : (2 ^ P * m + y) % 2 ^ P = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
  rw [eqAt_append, hb, hd, eqAt_mod b, hb, hmod, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have e1 : (16 * y + i) / 2 ^ 4 = y := by (clear * - hmod hi'; omega)
  have e2 : (16 * y + i) % 2 ^ 4 = i := by (clear * - hmod e1; omega)
  rw [eqAt_append a b (16 * y + i), ha, e1, eqAt_mod a (16 * y + i), ha, e2,
    show i + 16 * y = 16 * y + i by ring]
  ring

/-! ## The first claim -/

/-- The first claim's position weights: `eq(r_lane, ℓ)·x^z` (`keccak.rs:250-251`). -/
def firstWeights (lanesPt : List E) : List E :=
  (List.range keccakBits).map fun j ↦ (eqKernel lanesPt).getD (j / 64) 0 * eOfNat (2 ^ (j % 64))

/-- The first claim (`keccak.rs:252-263`). -/
def firstClaim (inst segment lanesPt output : List E) (committed : E) : KeccakClaim :=
  ⟨committed + (eqKernel segment).getD (keccakSegments - 1) 0 *
      dot ((eqKernel lanesPt).take 25) output,
    eqKernel (inst.take 4), inst.drop 4 ++ segment, firstWeights lanesPt⟩

theorem firstClaim_mu (inst segment lanesPt output : List E) (committed : E) :
    (firstClaim inst segment lanesPt output committed).mu = eqKernel (inst.take 4) := by
  simp only [firstClaim]

theorem firstClaim_point (inst segment lanesPt output : List E) (committed : E) :
    (firstClaim inst segment lanesPt output committed).point = inst.drop 4 ++ segment := by
  simp only [firstClaim]

theorem firstClaim_weights (inst segment lanesPt output : List E) (committed : E) :
    (firstClaim inst segment lanesPt output committed).weights = firstWeights lanesPt := by
  simp only [firstClaim]

theorem firstWeights_length (lanesPt : List E) : (firstWeights lanesPt).length = 1600 := by
  rw [firstWeights, List.length_map, List.length_range]; rfl

theorem firstClaim_shape {P : ℕ} {inst segment lanesPt output : List E} (committed : E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) :
    ClaimShape P (firstClaim inst segment lanesPt output committed) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [firstClaim_mu, eqKernel_length, List.length_take, hi, min_eq_left (by (clear * -; omega))]; rfl
  · rw [firstClaim_point, List.length_append, List.length_drop, hi, hs]; (clear * -; omega)
  · rw [firstClaim_weights]; exact firstWeights_length lanesPt

/-- The first claim's weights read a state's lanes as words. -/
theorem sum_firstWeights {lanesPt : List E} (hl : lanesPt.length = 5) (a : KeccakState) :
    ∑ j ∈ range 1600, (firstWeights lanesPt).getD j 0 * bitE (sbit a j) =
      ∑ l ∈ range 25, eqAt lanesPt l * ofK (laneWord a l) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mul]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [laneWord, ofK_ofLane, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have hj : 64 * l + z < 1600 := by (clear * - hl'' hz'; omega)
  rw [firstWeights, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  have e1 : (64 * l + z) / 64 = l := by (clear * - hz'; omega)
  have e2 : (64 * l + z) % 64 = z := by (clear * - e1; omega)
  rw [e1, e2, eqKernel_getD, hl, ite_eq_left (by (clear * - hl'' e1; omega)), sbit_lane a l hz']
  ring

variable (h : ℕ)

/-- **The first claim on a candidate**: the lanes of the two segments' outputs, combined. -/
theorem firstClaim_sum (P : ℕ) (hP : h = P + 4) (col : ℕ → K) {inst segment lanesPt : List E}
    (hi : inst.length = h) (hl : lanesPt.length = 5) (output : List E) (committed : E) :
    claimSum (statesAt h col 0) P (firstClaim inst segment lanesPt output committed).point
        (firstClaim inst segment lanesPt output committed).mu
        (firstClaim inst segment lanesPt output committed).weights =
      ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col m 12 x) l) := by
  subst hP
  have ha : (inst.take 4).length = 4 := by simp [hi]
  have hb : (inst.drop 4).length = P := by simp [hi]
  simp only [firstClaim, claimSum, stAt]
  have hmu : ∀ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 = eqAt (inst.take 4) i :=
    fun i hi' ↦ by
      rw [eqKernel_getD, ha, ite_eq_left (show i < 2 ^ 4 by
        have := Finset.mem_range.1 hi'; simpa using this)]
  have e : ∀ z, ∑ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 * ∑ j ∈ range 1600,
      (firstWeights lanesPt).getD j 0 * bitE (statesAt (P + 4) col 0 (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) j) =
      ∑ i ∈ range 16, eqAt (inst.take 4) i * (fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
        ofK (laneWord (segState (P + 4) col m 12 x) l)) (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := by
    intro z
    refine Finset.sum_congr rfl fun i hi' ↦ ?_
    rw [hmu i hi']
    exact congrArg _ (sum_firstWeights hl _)
  simp only [e]
  rw [sum_split ha hb (fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
    ofK (laneWord (segState (P + 4) col m 12 x) l)), List.take_append_drop]
  refine Finset.sum_congr rfl fun m _ ↦ congrArg _ ?_
  simp only [stepMle, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-! ## The mismatch table -/

/-- The committed middle state's lane `l` at `inst`. -/
def midMle (col : ℕ → K) (inst : List E) (l : ℕ) : E := stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + l)))

/-- The fifty mismatches, index `m + 2ℓ`: segment `0`'s output against the committed middle
state, segment `1`'s output against the claimed `output`. -/
def startDelta (col : ℕ → K) (inst output : List E) (u : ℕ) : E :=
  if u / 2 < 25 then
    (if u % 2 = 0 then stepMle h inst (fun x ↦ laneWord (segState h col 0 12 x) (u / 2)) +
        midMle h col inst (u / 2)
      else stepMle h inst (fun x ↦ laneWord (segState h col 1 12 x) (u / 2)) +
        output.getD (u / 2) 0)
  else 0

theorem add_eq_zero_iff_E {a b : E} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- A zero mismatch table: the middle-state and output claims hold. -/
theorem claims_of_zeroOn (col : ℕ → K) (inst output : List E)
    (hz : ZeroOn (startDelta h col inst output) [] 6) :
    outClaimsTrueMid h col inst output ∧ midAgree h col inst := by
  rw [zeroOn_nil] at hz
  refine ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · have := hz (1 + 2 * l) (by (clear * - hl; omega))
    have e1 : (1 + 2 * l) / 2 = l := by (clear * -; omega)
    have e2 : (1 + 2 * l) % 2 = 1 := by (clear * - e1; omega)
    rw [startDelta, e1, e2, ite_eq_left hl, ite_eq_right (by norm_num)] at this
    exact add_eq_zero_iff_E.1 this
  · have := hz (2 * l) (by (clear * - hl; omega))
    have e1 : 2 * l / 2 = l := by (clear * -; omega)
    have e2 : 2 * l % 2 = 0 := by (clear * - e1; omega)
    rw [startDelta, e1, e2, ite_eq_left hl, ite_eq_left rfl] at this
    exact add_eq_zero_iff_E.1 this

/-- The candidate's state after `committed`: the value opens the committed middle state. -/
def OpenTrue (col : ℕ → K) (inst segment lanesPt : List E) (committed : E) : Prop :=
  committed = eqAt segment 0 * ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l

/-- **After `committed`**: an open value and a true first claim leave the mismatch table's
extension zero at the challenges. -/
theorem zeroOn_of_first (P : ℕ) (hP : h = P + 4) (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = h) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (ho : output.length = 25) (committed : E)
    (hopen : OpenTrue h col inst segment lanesPt committed)
    (htrue : ClaimTrue (statesAt h col 0) P (firstClaim inst segment lanesPt output committed)) :
    ZeroOn (startDelta h col inst output) (segment ++ lanesPt) 6 := by
  rw [zeroOn_full _ (by simp [hs, hl])]
  rw [ClaimTrue, firstClaim_sum h P hP col hi hl] at htrue
  have hdot : dot ((eqKernel lanesPt).take 25) output =
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [dot_eq _ _ (by simp [eqKernel_length, hl, ho])]
    simp only [List.length_take, eqKernel_length, hl]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
      ← List.getD_eq_getElem?_getD, eqKernel_getD, hl, ite_eq_left (by (clear * - hl''; omega))]
  have hseg : (eqKernel segment).getD (keccakSegments - 1) 0 = eqAt segment 1 := by
    rw [eqKernel_getD, hs]; rfl
  change committed + (eqKernel segment).getD (keccakSegments - 1) 0 *
    dot ((eqKernel lanesPt).take 25) output = _ at htrue
  rw [hseg, hdot] at htrue
  -- the sum over the 64 indices, split into segment and lane
  have hsplit : ∑ w ∈ range (2 ^ 6), eqAt (segment ++ lanesPt) w * startDelta h col inst output w =
      ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 32, eqAt lanesPt l *
        startDelta h col inst output (2 * l + m) := by
    rw [show 2 ^ 6 = 32 * 2 from rfl, sum_range_mul 32 2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hm' := Finset.mem_range.1 hm
    have e1 : (2 * l + m) / 2 = l := by (clear * - hm'; omega)
    rw [eqAt_append, hs, eqAt_mod segment, hs, pow_one, e1,
      show (2 * l + m) % 2 = m by (clear * - e1; omega)]
    ring
  have hzero : ∀ m < 2, ∑ x ∈ range 7, eqAt lanesPt (25 + x) *
      startDelta h col inst output (2 * (25 + x) + m) = 0 := fun m hm ↦
    Finset.sum_eq_zero fun x _ ↦ by
      rw [startDelta, ite_eq_right (by (clear * - hm; omega)), mul_zero]
  have hm0 : ∑ l ∈ range 32, eqAt lanesPt l * startDelta h col inst output (2 * l + 0) =
      ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col 0 12 x) l) +
      ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 0 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDelta, ite_eq_left (by (clear * - hl''; omega)), ite_eq_left (by (clear * -; omega)),
      show (2 * l + 0) / 2 = l by (clear * -; omega), mul_add]
  have hm1 : ∑ l ∈ range 32, eqAt lanesPt l * startDelta h col inst output (2 * l + 1) =
      ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col 1 12 x) l) +
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 1 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDelta, ite_eq_left (by (clear * - hl''; omega)), ite_eq_right (by (clear * -; omega)),
      show (2 * l + 1) / 2 = l by (clear * -; omega), mul_add]
  rw [hsplit, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
    Finset.sum_range_zero, zero_add, hm0, hm1]
  rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0), Finset.sum_range_zero,
    zero_add] at htrue
  rw [OpenTrue] at hopen
  linear_combination (-1 : E) * htrue + (-1 : E) * hopen +
    (CharTwo.two_eq_zero (R := E)) * (eqAt segment 1 *
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 + committed)

end

/-! ## The start at a shape (lvm2 T-G)

The first claim, the statements it starts from and the mismatch table for any `Shape.Ok`, on a
candidate given by its segments' inputs `I`. The table has `segments · 32` entries, index
`m + segments·ℓ` (segment `m`, lane `ℓ`): the last segment's output against the claimed `output`,
segment `0`'s output against segment `1`'s committed input (two segments only). -/

section

/-- The first claim at the shape `sh` (`keccak.rs:247-263`). -/
def firstClaimS (sh : Shape) (inst segment lanesPt output : List E) (committed : E) : KeccakClaim :=
  ⟨committed + (eqKernel segment).getD (sh.segments - 1) 0 *
      dot ((eqKernel lanesPt).take 25) output,
    eqKernel (inst.take 4), inst.drop 4 ++ segment, firstWeights lanesPt⟩

theorem firstClaim_v1 (inst segment lanesPt output : List E) (committed : E) :
    firstClaim inst segment lanesPt output committed =
      firstClaimS Shape.v1 inst segment lanesPt output committed := rfl

theorem logSteps_ge {sh : Shape} (P : ℕ) : P + 4 ≤ sh.logSteps P := by
  unfold Shape.logSteps; split_ifs <;> omega

/-- A sum over packs and instances is a sum over the steps (four instance bits low). -/
theorem sum_low_split (a b : List E) (ha : a.length = 4) (H : ℕ → E) :
    ∑ z ∈ range (2 ^ b.length), eqAt b z * ∑ i ∈ range 16, eqAt a i * H (i + 16 * z) =
      ∑ x ∈ range (2 ^ (b.length + 4)), eqAt (a ++ b) x * H x := by
  rw [show 2 ^ (b.length + 4) = 2 ^ b.length * 16 by rw [pow_add]; rfl,
    sum_range_mul (2 ^ b.length) 16]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have e1 : (16 * y + i) / 2 ^ 4 = y := by (clear * - hi'; omega)
  have e2 : (16 * y + i) % 2 ^ 4 = i := by (clear * - e1; omega)
  rw [eqAt_append a b (16 * y + i), ha, e1, eqAt_mod a (16 * y + i), ha, e2,
    show i + 16 * y = 16 * y + i by ring]
  ring

theorem firstClaimS_shape {sh : Shape} (hsh : sh.Ok) {P : ℕ} {inst segment lanesPt output : List E}
    (committed : E) (hi : inst.length = sh.logSteps P) (hs : segment.length = sh.segBits) :
    ClaimShape P (firstClaimS sh inst segment lanesPt output committed) := by
  have h4 := logSteps_ge (sh := sh) P
  have hw : (firstClaimS sh inst segment lanesPt output committed).weights = firstWeights lanesPt := by
    simp only [firstClaimS]
  refine ⟨?_, ?_, by rw [hw]; exact firstWeights_length lanesPt⟩
  · have hmu : (firstClaimS sh inst segment lanesPt output committed).mu =
        eqKernel (inst.take 4) := rfl
    rw [hmu, eqKernel_length, List.length_take, hi, min_eq_left (by (clear * - hi h4; omega))]; rfl
  · have hpt : (firstClaimS sh inst segment lanesPt output committed).point =
        inst.drop 4 ++ segment := rfl
    rw [hpt, List.length_append, List.length_drop, hs, hi, Shape.segBits_of_ok hsh, Shape.logSteps]
    rcases hsh.1 with h | h <;> simp [h]

/-- **The first claim on a candidate**, at a shape: the lanes of the segments' outputs,
combined. -/
theorem firstClaimS_sum {sh : Shape} (hsh : sh.Ok) (P : ℕ) (I : ℕ → ℕ → KeccakState)
    {inst segment lanesPt : List E} (hi : inst.length = sh.logSteps P)
    (hs : segment.length = sh.segBits) (hl : lanesPt.length = 5) (output : List E) (committed : E) :
    claimSum (statesOfS sh P I 0) P (firstClaimS sh inst segment lanesPt output committed).point
        (firstClaimS sh inst segment lanesPt output committed).mu
        (firstClaimS sh inst segment lanesPt output committed).weights =
      ∑ m ∈ range sh.segments, eqAt segment m * ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle (sh.logSteps P) inst (fun x ↦ laneWord (segStateS sh I m sh.depth x) l) := by
  have h4 := logSteps_ge (sh := sh) P
  have ha : (inst.take 4).length = 4 := by simp [hi]; (clear * - hi h4; omega)
  simp only [firstClaimS, claimSum, stAt]
  have hmu : ∀ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 = eqAt (inst.take 4) i :=
    fun i hi' ↦ by
      rw [eqKernel_getD, ha, ite_eq_left (show i < 2 ^ 4 by
        have := Finset.mem_range.1 hi'; simpa using this)]
  let G : ℕ → ℕ → E := fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
    ofK (laneWord (segStateS sh I (sh.seg m) (sh.depth - 0) (sh.step P m x)) l)
  have e : ∀ z, ∑ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 * ∑ j ∈ range 1600,
      (firstWeights lanesPt).getD j 0 * bitE (statesOfS sh P I 0 (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) j) =
      ∑ i ∈ range 16, eqAt (inst.take 4) i * G (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := by
    intro z
    refine Finset.sum_congr rfl fun i hi' ↦ ?_
    rw [hmu i hi']
    exact congrArg _ (sum_firstWeights hl _)
  simp only [e]
  rcases hsh.1 with h1 | h2
  · have hs0 : segment = [] := List.eq_nil_of_length_eq_zero (by
      rw [hs, Shape.segBits_of_ok hsh, h1])
    subst hs0
    have hb : (inst.drop 4).length = P + 1 := by simp [hi, Shape.logSteps, h1]
    have hlog : sh.logSteps P = P + 1 + 4 := by simp [Shape.logSteps, h1]
    let H : ℕ → E := fun x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
      ofK (laneWord (segStateS sh I 0 sh.depth x) l)
    have hG : ∀ z i, G (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) = H (i + 16 * z) := by
      intro z i
      have hz := Nat.mod_add_div z (2 ^ P)
      have hx : i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P) = i + 16 * z := by
        calc i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)
            = i + 16 * (z % 2 ^ P + 2 ^ P * (z / 2 ^ P)) := by rw [pow_add]; ring
          _ = i + 16 * z := by rw [hz]
      simp only [G, H, Shape.seg, Shape.step, h1, if_true, Nat.sub_zero, hx]
    simp only [hG]
    have hsplit := sum_low_split (inst.take 4) (inst.drop 4) ha H
    rw [hb] at hsplit
    rw [List.append_nil, hsplit, List.take_append_drop, h1, Finset.sum_range_one, eqAt_nil, one_mul,
      hlog]
    simp only [H, stepMle, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
  · have hb : (inst.drop 4).length = P := by simp [hi, Shape.logSteps, h2]
    have hlog : sh.logSteps P = P + 4 := by simp [Shape.logSteps, h2]
    rw [sum_split ha hb G, List.take_append_drop, h2]
    refine Finset.sum_congr rfl fun m _ ↦ congrArg _ ?_
    have hG : ∀ x, G m x = ∑ l ∈ range 25, eqAt lanesPt l *
        ofK (laneWord (segStateS sh I m sh.depth x) l) := fun x ↦ by
      simp only [G, Shape.seg, Shape.step, h2, Nat.sub_zero]; rfl
    simp only [hG, hlog, stepMle, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-- The candidate's state after `committed`: with two segments, the value opens segment `1`'s
committed input; with one, it is `0` (nothing is read). -/
def OpenTrueS (sh : Shape) (h : ℕ) (I : ℕ → ℕ → KeccakState) (inst segment lanesPt : List E)
    (committed : E) : Prop :=
  committed = if sh.segments = 1 then 0 else
    eqAt segment 0 * ∑ l ∈ range 25, eqAt lanesPt l * stepMle h inst (fun x ↦ laneWord (I 1 x) l)

/-- **The output-lane claims** at `inst`: the last segment's output (from its input). -/
def outClaimsTrueMidS (sh : Shape) (h : ℕ) (I : ℕ → ℕ → KeccakState) (inst output : List E) :
    Prop :=
  ∀ l < 25, stepMle h inst (fun x ↦ laneWord (segStateS sh I (sh.segments - 1) sh.depth x) l) =
    output.getD l 0

/-- With two segments, segment `0`'s output and segment `1`'s input agree at `inst`. -/
def midAgreeS (sh : Shape) (h : ℕ) (I : ℕ → ℕ → KeccakState) (inst : List E) : Prop :=
  sh.segments = 2 → ∀ l < 25,
    stepMle h inst (fun x ↦ laneWord (segStateS sh I 0 sh.depth x) l) =
      stepMle h inst (fun x ↦ laneWord (I 1 x) l)

/-- The mismatch table at a shape, index `m + segments·ℓ`. -/
def startDeltaS (sh : Shape) (h : ℕ) (I : ℕ → ℕ → KeccakState) (inst output : List E) (u : ℕ) :
    E :=
  if u / sh.segments < 25 then
    stepMle h inst (fun x ↦ laneWord (segStateS sh I (u % sh.segments) sh.depth x)
        (u / sh.segments)) +
      (if u % sh.segments + 1 = sh.segments then output.getD (u / sh.segments) 0
        else stepMle h inst (fun x ↦ laneWord (I (u % sh.segments + 1) x) (u / sh.segments)))
  else 0

/-- A zero mismatch table: the output claims hold, and the segments agree. -/
theorem claims_of_zeroOnS {sh : Shape} (hsh : sh.Ok) (h : ℕ) (I : ℕ → ℕ → KeccakState)
    (inst output : List E) (hz : ZeroOn (startDeltaS sh h I inst output) [] (sh.segBits + 5)) :
    outClaimsTrueMidS sh h I inst output ∧ midAgreeS sh h I inst := by
  rw [zeroOn_nil] at hz
  have hb : ∀ u, u < 2 ^ (sh.segments - 1 + 5) → u < 2 ^ (sh.segBits + 5) := fun u hu ↦ by
    rwa [Shape.segBits_of_ok hsh]
  refine ⟨fun l hl ↦ ?_, fun h2 l hl ↦ ?_⟩
  · rcases hsh.1 with h1 | h2
    · have := hz l (hb l (by rw [h1]; exact lt_of_lt_of_le hl (by norm_num)))
      rw [startDeltaS, h1, Nat.div_one, Nat.mod_one, if_pos hl, if_pos rfl] at this
      rw [h1]
      exact add_eq_zero_iff_E.1 this
    · have := hz (1 + 2 * l) (hb _ (by rw [h2]; exact lt_of_lt_of_le (by (clear * - hl; omega) : 1 + 2 * l < 64) (by norm_num)))
      have e1 : (1 + 2 * l) / 2 = l := by (clear * -; omega)
      have e2 : (1 + 2 * l) % 2 = 1 := by (clear * - e1; omega)
      rw [startDeltaS, h2, e1, e2, if_pos hl, if_pos rfl] at this
      rw [h2]
      exact add_eq_zero_iff_E.1 this
  · have hl2 : 2 * l < 2 ^ (sh.segBits + 5) := by
      rw [Shape.segBits_of_ok hsh, h2]
      exact lt_of_lt_of_le (by (clear * - hl; omega) : 2 * l < 64) (by norm_num)
    have := hz (2 * l) hl2
    have e1 : 2 * l / 2 = l := by (clear * -; omega)
    have e2 : 2 * l % 2 = 0 := by (clear * - e1; omega)
    rw [startDeltaS, h2, e1, e2, if_pos hl, if_neg (by norm_num)] at this
    exact add_eq_zero_iff_E.1 this

/-- **After `committed`**, at a shape: an open value and a true first claim leave the mismatch
table's extension zero at the challenges. -/
theorem zeroOn_of_firstS {sh : Shape} (hsh : sh.Ok) (P : ℕ) (I : ℕ → ℕ → KeccakState)
    {inst segment lanesPt output : List E} (hi : inst.length = sh.logSteps P)
    (hs : segment.length = sh.segBits) (hl : lanesPt.length = 5) (ho : output.length = 25)
    (committed : E) (hopen : OpenTrueS sh (sh.logSteps P) I inst segment lanesPt committed)
    (htrue : ClaimTrue (statesOfS sh P I 0) P (firstClaimS sh inst segment lanesPt output committed)) :
    ZeroOn (startDeltaS sh (sh.logSteps P) I inst output) (segment ++ lanesPt) (sh.segBits + 5) := by
  have hsb := Shape.segBits_of_ok hsh
  rw [zeroOn_full _ (by simp [hs, hl])]
  rw [ClaimTrue, firstClaimS_sum hsh P I hi hs hl] at htrue
  have hdot : dot ((eqKernel lanesPt).take 25) output =
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [dot_eq _ _ (by simp [eqKernel_length, hl, ho])]
    simp only [List.length_take, eqKernel_length, hl]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
      ← List.getD_eq_getElem?_getD, eqKernel_getD, hl, ite_eq_left (by (clear * - hl''; omega))]
  change committed + (eqKernel segment).getD (sh.segments - 1) 0 *
    dot ((eqKernel lanesPt).take 25) output = _ at htrue
  rw [hdot] at htrue
  rw [OpenTrueS] at hopen
  rcases hsh.1 with h1 | h2
  · have hs0 : segment = [] := List.eq_nil_of_length_eq_zero (by rw [hs, hsb, h1])
    subst hs0
    rw [if_pos h1] at hopen
    rw [h1, Finset.sum_range_one, eqAt_nil, one_mul, show 1 - 1 = 0 from rfl, eqKernel_getD,
      if_pos (by simp), eqAt_nil, one_mul, hopen, zero_add] at htrue
    rw [List.nil_append, hsb, h1, show 2 ^ (1 - 1 + 5) = 25 + 7 by norm_num, Finset.sum_range_add]
    have hz : ∑ x ∈ range 7, eqAt lanesPt (25 + x) *
        startDeltaS sh (sh.logSteps P) I inst output (25 + x) = 0 :=
      Finset.sum_eq_zero fun x _ ↦ by
        rw [startDeltaS, h1, Nat.div_one, if_neg (by (clear * -; omega)), mul_zero]
    rw [hz, add_zero]
    have hm : ∑ l ∈ range 25, eqAt lanesPt l * startDeltaS sh (sh.logSteps P) I inst output l =
        ∑ l ∈ range 25, eqAt lanesPt l *
          stepMle (sh.logSteps P) inst (fun x ↦ laneWord (segStateS sh I 0 sh.depth x) l) +
        ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl' ↦ ?_
      have hl'' := Finset.mem_range.1 hl'
      rw [startDeltaS, h1, Nat.div_one, Nat.mod_one, if_pos hl'', if_pos rfl, mul_add]
    rw [hm]
    linear_combination (-1 : E) * htrue +
      (CharTwo.two_eq_zero (R := E)) * ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0
  · rw [if_neg (by (clear * - h2; omega))] at hopen
    have hseg : (eqKernel segment).getD (sh.segments - 1) 0 = eqAt segment 1 := by
      rw [eqKernel_getD, hs, hsb, h2]; rfl
    rw [hseg] at htrue
    rw [hsb, h2] at hs ⊢
    have hsplit : ∑ w ∈ range (2 ^ (2 - 1 + 5)), eqAt (segment ++ lanesPt) w *
          startDeltaS sh (sh.logSteps P) I inst output w =
        ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 32, eqAt lanesPt l *
          startDeltaS sh (sh.logSteps P) I inst output (2 * l + m) := by
      rw [show 2 ^ (2 - 1 + 5) = 32 * 2 by norm_num, sum_range_mul 32 2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have hm' := Finset.mem_range.1 hm
      have e1 : (2 * l + m) / 2 = l := by (clear * - hm'; omega)
      rw [eqAt_append, hs, eqAt_mod segment, hs, show 2 - 1 = 1 from rfl, pow_one, e1,
        show (2 * l + m) % 2 = m by (clear * - e1; omega)]
      ring
    have hzero : ∀ m < 2, ∑ x ∈ range 7, eqAt lanesPt (25 + x) *
        startDeltaS sh (sh.logSteps P) I inst output (2 * (25 + x) + m) = 0 := fun m hm ↦
      Finset.sum_eq_zero fun x _ ↦ by
        rw [startDeltaS, h2, if_neg (by (clear * - hm; omega)), mul_zero]
    have hm0 : ∑ l ∈ range 32, eqAt lanesPt l *
          startDeltaS sh (sh.logSteps P) I inst output (2 * l + 0) =
        ∑ l ∈ range 25, eqAt lanesPt l *
          stepMle (sh.logSteps P) inst (fun x ↦ laneWord (segStateS sh I 0 sh.depth x) l) +
        ∑ l ∈ range 25, eqAt lanesPt l *
          stepMle (sh.logSteps P) inst (fun x ↦ laneWord (I 1 x) l) := by
      rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 0 (by norm_num), add_zero,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl' ↦ ?_
      have hl'' := Finset.mem_range.1 hl'
      rw [startDeltaS, h2, show (2 * l + 0) / 2 = l by (clear * -; omega), show (2 * l + 0) % 2 = 0 by (clear * -; omega),
        if_pos hl'', if_neg (by norm_num), mul_add]
    have hm1 : ∑ l ∈ range 32, eqAt lanesPt l *
          startDeltaS sh (sh.logSteps P) I inst output (2 * l + 1) =
        ∑ l ∈ range 25, eqAt lanesPt l *
          stepMle (sh.logSteps P) inst (fun x ↦ laneWord (segStateS sh I 1 sh.depth x) l) +
        ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
      rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 1 (by norm_num), add_zero,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl' ↦ ?_
      have hl'' := Finset.mem_range.1 hl'
      rw [startDeltaS, h2, show (2 * l + 1) / 2 = l by (clear * -; omega), show (2 * l + 1) % 2 = 1 by (clear * -; omega),
        if_pos hl'', if_pos rfl, mul_add]
    rw [hsplit, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
      Finset.sum_range_zero, zero_add, hm0, hm1]
    rw [h2, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0), Finset.sum_range_zero,
      zero_add] at htrue
    linear_combination (-1 : E) * htrue + (-1 : E) * hopen +
      (CharTwo.two_eq_zero (R := E)) * (eqAt segment 1 *
        ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 + committed)

/-! ### v1 as the instance `12 × 2` -/

theorem laneWord_inState (h : ℕ) (col : ℕ → K) (m x : ℕ) {l : ℕ} (hl : l < 25) :
    laneWord (inState h col m x) l = col (x + 2 ^ h * (25 * m + l)) := by
  rw [laneWord, lane_inState h col m x hl, ofLane_lane]

theorem outClaimsTrueMid_v1 (h : ℕ) (col : ℕ → K) (inst output : List E) :
    outClaimsTrueMid h col inst output ↔ outClaimsTrueMidS Shape.v1 h (inState h col) inst output :=
  Iff.rfl

theorem midAgree_v1 (h : ℕ) (col : ℕ → K) (inst : List E) :
    midAgree h col inst ↔ midAgreeS Shape.v1 h (inState h col) inst := by
  unfold midAgree midAgreeS
  have e : ∀ l < 25, stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + l))) =
      stepMle h inst (fun x ↦ laneWord (inState h col 1 x) l) := fun l hl ↦
    Finset.sum_congr rfl fun x _ ↦ by beta_reduce; rw [laneWord_inState h col 1 x hl, mul_one]
  constructor
  · intro hm _ l hl; rw [← e l hl]; exact hm l hl
  · intro hm l hl; rw [e l hl]; exact hm rfl l hl

theorem openTrue_v1 (h : ℕ) (col : ℕ → K) (inst segment lanesPt : List E) (committed : E) :
    OpenTrue h col inst segment lanesPt committed ↔
      OpenTrueS Shape.v1 h (inState h col) inst segment lanesPt committed := by
  unfold OpenTrue OpenTrueS
  rw [if_neg (by decide)]
  have e : ∀ l ∈ range 25, eqAt lanesPt l * midMle h col inst l =
      eqAt lanesPt l * stepMle h inst (fun x ↦ laneWord (inState h col 1 x) l) := fun l hl ↦ by
    rw [midMle]
    exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ by
      beta_reduce; rw [laneWord_inState h col 1 x (Finset.mem_range.1 hl), mul_one])
  rw [Finset.sum_congr rfl e]

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakStart` =====

-- ===== merged from `LvmKeccakLayers` (GOLF module merge: `LvmKeccakLayers.lean` is now a stub importing `LvmKeccakGkr`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Layers.lean` (formal rev 40f877dc) as `LvmKeccakLayers` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Layers

  The twelve layers of `verifyKeccak` on a candidate's committed states: from a claim on the
  segments' outputs to one on their committed inputs.
-/

/-!
# The layers

`keccakLayers logSteps (List.range 12)` (`crates/verifier/src/keccak.rs:264-267`) runs
`verifyKeccakLayer` at steps `0, …, 11`. On a candidate's column `qk q`, the states at depth `d` are
`statesAt … d` (`12 - d` rounds into each segment), and depth `d` is the round of depth `d + 1`
(`claimTrue_round`), so `layerSpec` chains (`layersSpec`): from doom of the claim at depth `d` to
doom of the claim at depth `12`, on the committed inputs.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open scoped ENNReal

section

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

open Classical in
/-- **The layers from depth `d`**: lead `T` (`0` when a layer is left, as it starts with a
read); each layer's groups as in `layerSpec`. -/
noncomputable def layersSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax)
    (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    (n d : ℕ) → d + n = 12 → (claim : KeccakClaim) → ClaimShape P claim →
      Spec (keccakLayers (P + 4) (List.range' d n) claim)
        (Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShape P c ∧
          Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P c ∧ R q) h) εmax T T
  | 0, d, hd, claim, hs =>
    (Spec.ret (Post := fun c h ↦ ClaimShape P c ∧
        Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P c ∧ R q) h) claim).mono
      (fun _ h' ↦ ⟨hs, by rw [show d = 12 by omega] at h'; exact h'⟩) (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpec (T := T) hst hcard R (fun q ↦ statesAt (P + 4) (qk q) (d + 1)) d P claim hs h46
      hβ).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_round (P + 4) (qk q) (by omega) P claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl zero_le le_rfl).bind' fun c ↦
    if hc : ClaimShape P c then
      (layersSpec hst hcard R qk P h46 hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakLayers` =====

-- ===== merged from `LvmKeccakOpenOut` (GOLF module merge: `LvmKeccakOpenOut.lean` is now a stub importing `LvmKeccakGkr`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/OpenOut.lean` (formal rev 40f877dc) as `LvmKeccakOpenOut` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.OpenOut

  Opening the committed middle state: `keccakOpen` on the first claim's segment `0`, a
  sumcheck over the slot, and the column claim on `q_keccak` it leaves.
-/

/-!
# The committed outputs' opening

`committed` claims `eq(r_seg, 0)·Σ_ℓ eq(r_lane, ℓ)·mid_ℓ(inst)` (`OpenTrue`), the middle state's
lanes being the slots `25 + ℓ` of `q_keccak` at the steps' point `inst`. `keccakOpen` with
`first = 1, count = 1` (`open`, `crates/verifier/src/keccak.rs:269-278`) proves it by a degree-two
sumcheck over the six slot bits of

  `Σ_o W(o) · Q(o)`,  `W(o) = slotW … o 0` (the slot weights at slice `0`),
  `Q(o) = stepMle inst (q(· + 2^h·o))`,

ending at the slot point `ρ` on `W̃(ρ)·Q̃(ρ)`; the verifier computes `W̃(ρ)` (the fold's slice
`0`), reads `word` and checks `W̃(ρ)·word`. `Q̃(ρ)` is the column's multilinear extension at
`inst ++ ρ` (`col_split`), the column claim it leaves.

* `cube_plainFamily`: a sum over the cube of a summand of degree `d` in each coordinate is a
  plain sumcheck family of degree `d`;
* `openOutSpec`: the sumcheck as a specification, from doom of `committed = Fo q []` to doom of
  `value = W̃(ρ)·Q̃_q(ρ)`, with the verifier's `W̃(ρ)`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

section

/-! ## Sums over the cube -/

/-- The sum over the remaining cube of `φ`, the first coordinates bound to `acc`. -/
noncomputable def cubeSum (φ : List E → E) (n : ℕ) (acc : List E) : E :=
  ∑ u ∈ range (2 ^ (n - acc.length)), φ (acc ++ bitsE u (n - acc.length))

theorem cube_plainFamily {β : Type} (φ : β → List E → E) {d : ℕ} (n : ℕ)
    (hφ : ∀ q pre post, PolyLE d fun x ↦ φ q (pre ++ x :: post)) :
    PlainFamily (fun q acc ↦ cubeSum (φ q) n acc) d n := by
  intro q acc hacc
  have hm : n - acc.length = (n - (acc.length + 1)) + 1 := by (clear * - hacc; omega)
  refine ⟨?_, ?_⟩
  · have e : ∀ x, cubeSum (φ q) n (acc ++ [x]) =
        ∑ u ∈ range (2 ^ (n - (acc.length + 1))), φ q (acc ++ x :: bitsE u (n - (acc.length + 1))) := by
      intro x
      simp only [cubeSum, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    exact PolyLE.congr (f := fun x ↦ ∑ u ∈ range (2 ^ (n - (acc.length + 1))),
      φ q (acc ++ x :: bitsE u (n - (acc.length + 1)))) (PolyLE.sum _ fun u _ ↦ hφ q acc _)
      fun x ↦ (e x).symm
  · simp only [cubeSum, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [bitsE_two_mul, bitsE_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

theorem cubeSum_nil (φ : List E → E) (n : ℕ) :
    cubeSum φ n [] = ∑ u ∈ range (2 ^ n), φ (bitsE u n) := by
  simp [cubeSum]

theorem cubeSum_full (φ : List E → E) {n : ℕ} {acc : List E} (h : acc.length = n) :
    cubeSum φ n acc = φ acc := by
  rw [cubeSum, h, Nat.sub_self]
  simp [bitsE]

/-- A product of two multilinear extensions has degree two in each coordinate. -/
theorem polyLE_mle_mul (f g : ℕ → E) (N M : ℕ) (pre post : List E) :
    PolyLE 2 fun x ↦ (∑ o ∈ range N, eqAt (pre ++ x :: post) o * f o) *
      ∑ o ∈ range M, eqAt (pre ++ x :: post) o * g o :=
  PolyLE.mul (polyLE_mle pre post N f) (polyLE_mle pre post M g)

/-! ## The column at a point -/

/-- **The column's multilinear extension**, step bits low and slot bits high. -/
theorem col_split {h : ℕ} {a s : List E} (ha : a.length = h) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ (h + s.length)), eqAt (a ++ s) n * F n =
      ∑ o ∈ range (2 ^ s.length), eqAt s o * ∑ x ∈ range (2 ^ h), eqAt a x * F (x + 2 ^ h * o) := by
  rw [pow_add, mul_comm, sum_range_mul]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  have hd : (2 ^ h * o + x) / 2 ^ h = o := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx', zero_add]
  have hmod : (2 ^ h * o + x) % 2 ^ h = x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  rw [eqAt_append, ha, hd, eqAt_mod a, ha, hmod, show 2 ^ h * o + x = x + 2 ^ h * o by ring]
  ring

/-! ## The committed opening -/

variable (h : ℕ)

/-- The slot weights at slice `0`, extended over the slot bits. -/
noncomputable def Wo (segment lanesPt pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * slotW (eqKernel segment) (firstWeights lanesPt) 1 1 o 0

/-- The column's slots at the steps' point `inst`, extended over the slot bits. -/
noncomputable def Qo (col : ℕ → K) (inst pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * stepMle h inst (fun x ↦ col (x + 2 ^ h * o))

/-- The committed opening's sumcheck family. -/
noncomputable def Fo (col : ℕ → K) (inst segment lanesPt : List E) (acc : List E) : E :=
  cubeSum (fun pt ↦ Wo segment lanesPt pt * Qo h col inst pt) 6 acc

theorem Fo_plainFamily {β : Type} (qk : β → ℕ → K) (inst segment lanesPt : List E) :
    PlainFamily (fun q acc ↦ Fo h (qk q) inst segment lanesPt acc) 2 6 :=
  cube_plainFamily (fun q pt ↦ Wo segment lanesPt pt * Qo h (qk q) inst pt) 6
    fun _ pre post ↦ polyLE_mle_mul _ _ _ _ pre post

theorem slotW_out {segment lanesPt : List E} (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (o : ℕ) : slotW (eqKernel segment) (firstWeights lanesPt) 1 1 o 0 =
      if 25 ≤ o ∧ o < 50 then eqAt segment 0 * eqAt lanesPt (o - 25) else 0 := by
  rw [slotW]
  by_cases ho : 25 ≤ o ∧ o < 50
  · rw [ite_eq_left (show 25 * 1 ≤ o ∧ o < 25 * (1 + 1) ∧ 0 < 64 by (clear * - ho; omega)), ite_eq_left ho]
    have e1 : o / 25 - 1 = 0 := by (clear * - ho; omega)
    have e2 : 64 * (o % 25) + 0 < 1600 := by (clear * -; omega)
    rw [e1, eqKernel_getD, hs, ite_eq_left (by norm_num), firstWeights,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa [keccakBits] using e2)]
    simp only [Option.map_some, Option.getD_some]
    have e3 : (64 * (o % 25) + 0) / 64 = o - 25 := by (clear * - ho e2; omega)
    have e4 : (64 * (o % 25) + 0) % 64 = 0 := by (clear * - e3; omega)
    rw [e3, e4, eqKernel_getD, hl, ite_eq_left (by (clear * - e2 e3; omega)), pow_zero, eOfNat_one, mul_one]
  · rw [ite_eq_right (show ¬ (25 * 1 ≤ o ∧ o < 25 * (1 + 1) ∧ 0 < 64) by (clear * - ho; omega)), ite_eq_right ho]

/-- Before the slot challenges, the family is the middle-state value `OpenTrue` speaks of. -/
theorem Fo_nil (col : ℕ → K) (inst : List E) {segment lanesPt : List E}
    (hs : segment.length = 1) (hl : lanesPt.length = 5) :
    Fo h col inst segment lanesPt [] =
      eqAt segment 0 * ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l := by
  rw [Fo, cubeSum_nil]
  have hu : ∀ u ∈ range (2 ^ 6), Wo segment lanesPt (bitsE u 6) * Qo h col inst (bitsE u 6) =
      slotW (eqKernel segment) (firstWeights lanesPt) 1 1 u 0 *
        stepMle h inst (fun x ↦ col (x + 2 ^ h * u)) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [Wo, Qo, sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']
  rw [Finset.sum_congr rfl hu, show 2 ^ 6 = 25 + (25 + 14) from rfl, Finset.sum_range_add,
    Finset.sum_range_add, Finset.mul_sum]
  have h1 : ∑ u ∈ range 25, slotW (eqKernel segment) (firstWeights lanesPt) 1 1 u 0 *
      stepMle h inst (fun x ↦ col (x + 2 ^ h * u)) = 0 :=
    Finset.sum_eq_zero fun u hu ↦ by
      rw [slotW_out hs hl, ite_eq_right (by have := Finset.mem_range.1 hu; (clear * - this; omega)), zero_mul]
  have h3 : ∑ u ∈ range 14, slotW (eqKernel segment) (firstWeights lanesPt) 1 1 (25 + (25 + u)) 0 *
      stepMle h inst (fun x ↦ col (x + 2 ^ h * (25 + (25 + u)))) = 0 :=
    Finset.sum_eq_zero fun u _ ↦ by rw [slotW_out hs hl, ite_eq_right (by (clear * -; omega)), zero_mul]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [slotW_out hs hl, ite_eq_left (by (clear * - hl''; omega)), show 25 + l - 25 = l by (clear * - hl''; omega), midMle]
  ring

theorem headD_eq_getD (r : List E) : r.headD 0 = r.getD 0 0 := by
  cases r <;> rfl

/-- **The verifier's slot weight** at slice `0` after the fold is `W̃(ρ)`. -/
theorem fold_out {P : ℕ} {inst segment lanesPt output : List E} (hi : inst.length = P + 4)
    (committed : E) {slot : List E} (hslot : slot.length = 6) :
    ((foldAll slot (keccakSlotWeights (P + 4) (firstClaim inst segment lanesPt output committed)
      1 1)).headD []).headD 0 = Wo segment lanesPt slot := by
  have hrows := slotWeights_length (P + 4) (firstClaim inst segment lanesPt output committed) 1 1
    (by norm_num)
  obtain ⟨-, -, h3⟩ := foldAll_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeights_row_length _ _ 1 1 (by norm_num) (by (clear * - hrows ho; omega))
  rw [headD_eq_getD, h3 0 (by norm_num), Wo, hslot]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeights_getD _ _ 1 1 (by norm_num) (Finset.mem_range.1 ho), firstClaim_point,
    firstClaim_weights, show P + 4 - 4 = P by (clear * -; omega),
    List.drop_left' (by simp [hi])]

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakOpenOut` =====

-- ===== merged from `LvmKeccakOpenIn` (GOLF module merge: `LvmKeccakOpenIn.lean` is now a stub importing `LvmKeccakGkr`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/OpenIn.lean` (formal rev 40f877dc) as `LvmKeccakOpenIn` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.OpenIn

  Opening the committed inputs: the claim at depth `12` as a sum over the instances, then over
  the slots and slices of `q_keccak`, down to the `64` bit-slice claims.
-/

/-!
# The inputs' opening

The claim at depth `12` is on the committed inputs, slot `25m + ℓ` of `q_keccak` holding lane
`ℓ` of segment `m`'s input (`doc/leanvm` eq. `keccak:eq:in` with §`keccak:segments`). With
`Φ(i)` the claim's sum restricted to instance `i`:

* the instance rounds (`crates/verifier/src/keccak.rs:280`):
  `Fl acc = Σ_u μ̃(acc ++ u)·Φ̃(acc ++ u)`, a plain family of degree two on four bits, `claimSum`
  before (`Fl_nil`);
* the slot rounds (`keccakOpen` with `first = 0, count = 2`): with the instance point `λ`,
  `Fs acc = μ̃(λ) · Σ_u Σ_z W̃_z(acc ++ u)·S̃_z(acc ++ u)`, `W_z(o)` the slot weights
  (`slotW`), `S_z(o)` slice `z` of slot `o` at the point `(λ, r_pack)` (`sliceMle`); before,
  `μ̃(λ)·Φ̃(λ)` (`Fs_nil`, by `phi_eq`: the claim's positions are the slots' slices);
* `S̃_z(ρ)` is slice `z`'s multilinear extension at `(λ, r_pack, ρ)`, the slice claims.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

section

variable (P : ℕ)

/-- The claim at depth `12` restricted to instance `i`. -/
noncomputable def PhiI (col : ℕ → K) (claim : KeccakClaim) (i : ℕ) : E :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAt claim.point z *
    ∑ j ∈ range 1600, claim.weights.getD j 0 * bitE (stAt (statesAt (P + 4) col 12) P z i j)

/-- The instance weights, extended over the four instance bits. -/
noncomputable def MuT (mu pt : List E) : E := ∑ i ∈ range (2 ^ 4), eqAt pt i * mu.getD i 0

/-- `Φ`, extended over the four instance bits. -/
noncomputable def PhiT (col : ℕ → K) (claim : KeccakClaim) (pt : List E) : E :=
  ∑ i ∈ range (2 ^ 4), eqAt pt i * PhiI P col claim i

/-- The instance rounds' family. -/
noncomputable def Fl (col : ℕ → K) (claim : KeccakClaim) (acc : List E) : E :=
  cubeSum (fun pt ↦ MuT claim.mu pt * PhiT P col claim pt) 4 acc

theorem Fl_plainFamily {β : Type} (qk : β → ℕ → K) (claim : KeccakClaim) :
    PlainFamily (fun q acc ↦ Fl P (qk q) claim acc) 2 4 :=
  cube_plainFamily (fun q pt ↦ MuT claim.mu pt * PhiT P (qk q) claim pt) 4
    fun _ pre post ↦ polyLE_mle_mul _ _ _ _ pre post

theorem Fl_nil (col : ℕ → K) (claim : KeccakClaim) :
    Fl P col claim [] = claimSum (statesAt (P + 4) col 12) P claim.point claim.mu claim.weights := by
  rw [Fl, cubeSum_nil]
  have hu : ∀ u ∈ range (2 ^ 4), MuT claim.mu (bitsE u 4) * PhiT P col claim (bitsE u 4) =
      claim.mu.getD u 0 * PhiI P col claim u := by
    intro u hu
    rw [MuT, PhiT, sum_eqAt_bitsE (Finset.mem_range.1 hu), sum_eqAt_bitsE (Finset.mem_range.1 hu)]
  rw [Finset.sum_congr rfl hu, claimSum]
  simp only [PhiI, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ by ring

/-- Slice `z` of slot `o` at the steps' point `a`. -/
noncomputable def sliceMle (col : ℕ → K) (a : List E) (o z : ℕ) : E :=
  ∑ x ∈ range (2 ^ (P + 4)), eqAt a x * bitE ((col (x + 2 ^ (P + 4) * o)).toBitVec.getLsbD z)

/-- The slot weights of the claim at depth `12`, slice `z`, extended over the slot bits. -/
noncomputable def Ws (claim : KeccakClaim) (z : ℕ) (pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 o z

/-- Slice `z` at `(λ, r_pack)`, extended over the slot bits. -/
noncomputable def Qs (col : ℕ → K) (a : List E) (z : ℕ) (pt : List E) : E :=
  ∑ o ∈ range (2 ^ 6), eqAt pt o * sliceMle P col a o z

/-- The slot rounds' family, at the instance point `low`. -/
noncomputable def Fs (col : ℕ → K) (claim : KeccakClaim) (low : List E) (acc : List E) : E :=
  cubeSum (fun pt ↦ MuT claim.mu low * ∑ z ∈ range 64,
    Ws P claim z pt * Qs P col (low ++ claim.point.take P) z pt) 6 acc

theorem Fs_plainFamily {β : Type} (qk : β → ℕ → K) (claim : KeccakClaim) (low : List E) :
    PlainFamily (fun q acc ↦ Fs P (qk q) claim low acc) 2 6 :=
  cube_plainFamily (fun q pt ↦ MuT claim.mu low * ∑ z ∈ range 64,
      Ws P claim z pt * Qs P (qk q) (low ++ claim.point.take P) z pt) 6
    fun _ pre post ↦ PolyLE.const_mul (PolyLE.sum _ fun _ _ ↦
      polyLE_mle_mul _ _ _ _ pre post) _

/-- The states at depth `12` are the committed inputs' bits. -/
theorem statesAt_12 (col : ℕ → K) (m x : ℕ) {j : ℕ} (hj : j < 1600) :
    statesAt (P + 4) col 12 m x j =
      (col (x + 2 ^ (P + 4) * (25 * m + j / 64))).toBitVec.getLsbD (j % 64) := by
  rw [statesAt, Nat.sub_self, segState, roundsFrom_zero, sbit, lane_inState _ _ _ _ (by omega)]
  rfl

/-- The claim at depth `12` on segment `m` and step `x`. -/
noncomputable def Gin (col : ℕ → K) (claim : KeccakClaim) (m x : ℕ) : E :=
  ∑ j ∈ range 1600, claim.weights.getD j 0 *
    bitE ((col (x + 2 ^ (P + 4) * (25 * m + j / 64))).toBitVec.getLsbD (j % 64))

theorem Gin_eq (col : ℕ → K) (claim : KeccakClaim) (m x : ℕ) :
    Gin P col claim m x = ∑ l ∈ range 25, ∑ z ∈ range 64, claim.weights.getD (64 * l + z) 0 *
      bitE ((col (x + 2 ^ (P + 4) * (25 * m + l))).toBitVec.getLsbD z) := by
  rw [Gin, show 1600 = 25 * 64 from rfl, sum_range_mul 25 64]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  rw [show (64 * l + z) / 64 = l by (clear * - hz'; omega), show (64 * l + z) % 64 = z by (clear * - hz'; omega)]

/-- **The claim's positions are the slots' slices**: `Φ̃(λ)` is the slot-weighted sum of the
slices at `(λ, r_pack)`. -/
theorem phi_eq (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim) {low : List E}
    (hlow : low.length = 4) :
    PhiT P col claim low = ∑ o ∈ range (2 ^ 6), ∑ z ∈ range 64,
      slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 o z *
        sliceMle P col (low ++ claim.point.take P) o z := by
  have hb : (claim.point.take P).length = P := by simp [hshape.2.1]
  have hsd : (claim.point.drop P).length = 1 := by simp [hshape.2.1]
  have hX : ∀ z i, ∑ j ∈ range 1600, claim.weights.getD j 0 *
      bitE (stAt (statesAt (P + 4) col 12) P z i j) =
        Gin P col claim (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := fun z i ↦
    Finset.sum_congr rfl fun j hj ↦ by
      rw [stAt, statesAt_12 P col _ _ (Finset.mem_range.1 hj)]
  have hphi : PhiT P col claim low = ∑ z ∈ range (2 ^ (P + 1)),
      eqAt (claim.point.take P ++ claim.point.drop P) z *
        ∑ i ∈ range 16, eqAt low i * Gin P col claim (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := by
    rw [List.take_append_drop, PhiT]
    simp only [PhiI, hX]
    rw [show (2 : ℕ) ^ 4 = 16 from rfl]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hphi, sum_split hlow hb (Gin P col claim)]
  -- the slots: `o = 25m + ℓ` for `o < 50`, nothing above
  rw [show 2 ^ 6 = 2 * 25 + 14 from rfl, Finset.sum_range_add, sum_range_mul 2 25]
  have hzero : ∑ x ∈ range 14, ∑ z ∈ range 64,
      slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 (2 * 25 + x) z *
        sliceMle P col (low ++ claim.point.take P) (2 * 25 + x) z = 0 :=
    Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [slotW, ite_eq_right (by (clear * -; omega)), zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  simp only [Gin_eq, sliceMle, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hl' := Finset.mem_range.1 hl
  have hz' := Finset.mem_range.1 hz
  rw [slotW, ite_eq_left (show 25 * 0 ≤ 25 * m + l ∧ 25 * m + l < 25 * (0 + 2) ∧ z < 64 by
    (clear * - hm' hl' hz'; omega))]
  have e3 : (25 * m + l) / 25 - 0 = m := by (clear * - hm' hl'; omega)
  have e4 : (25 * m + l) % 25 = l := by (clear * - hl' e3; omega)
  rw [e3, e4, eqKernel_getD, hsd, ite_eq_left (by omega)]
  ring

theorem Fs_nil (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim) {low : List E}
    (hlow : low.length = 4) :
    Fs P col claim low [] = MuT claim.mu low * PhiT P col claim low := by
  rw [Fs, cubeSum_nil, ← Finset.mul_sum, phi_eq P col claim hshape hlow]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun u hu ↦ Finset.sum_congr rfl fun z _ ↦ ?_)
  rw [Ws, Qs, sum_eqAt_bitsE (Finset.mem_range.1 hu), sum_eqAt_bitsE (Finset.mem_range.1 hu)]

/-- **The verifier's slot weights** after the fold are `W̃_z(ρ)`. -/
theorem fold_in (claim : KeccakClaim) {slot : List E} (hslot : slot.length = 6) {z : ℕ}
    (hz : z < 64) :
    ((foldAll slot (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD []).getD z 0 =
      Ws P claim z slot := by
  have hrows := slotWeights_length (P + 4) claim 0 keccakSegments (by decide)
  obtain ⟨-, -, h3⟩ := foldAll_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeights_row_length _ _ 0 keccakSegments (by decide) (by (clear * - hrows ho; omega))
  rw [h3 z hz, Ws, hslot]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeights_getD _ _ 0 keccakSegments (by decide) (Finset.mem_range.1 ho),
    show P + 4 - 4 = P by (clear * -; omega)]
  rfl

theorem fold_in_length (claim : KeccakClaim) {slot : List E} (hslot : slot.length = 6) :
    ((foldAll slot (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD []).length = 64 := by
  have hrows := slotWeights_length (P + 4) claim 0 keccakSegments (by decide)
  exact (foldAll_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeights_row_length _ _ 0 keccakSegments (by decide) (by (clear * - hrows ho; omega))).2.1

/-- The slices at `(λ, r_pack, ρ)` are `S̃_z(ρ)`. -/
theorem slices_eq (col : ℕ → K) {a slot : List E} (ha : a.length = P + 4) (hslot : slot.length = 6)
    (z : ℕ) :
    ∑ n ∈ range (2 ^ (P + 4 + 6)), eqAt (a ++ slot) n * bitE ((col n).toBitVec.getLsbD z) =
      Qs P col a z slot := by
  rw [← hslot, col_split ha, Qs, hslot]
  rfl

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakOpenIn` =====

-- ===== merged from `LvmKeccakGkrTail` (GOLF module merge: `LvmKeccakGkrTail.lean` is now a stub importing `LvmKeccakGkr`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/GkrTail.lean` (formal rev 40f877dc) as `LvmKeccakGkrTail` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.GkrTail

  The end of `verifyKeccak` as a specification: the instance and slot sumchecks on the claim at
  depth `12`, the `64` slices, and the final check.
-/

/-!
# The inputs' opening as a specification

`inputTail` is the end of `verify_keccak` (`crates/verifier/src/keccak.rs:279-293`): the instance
rounds, the slot rounds (`keccakOpen` with `first = 0, count = 2`), the `64` slices and the check
`μ̃(λ)·⟨W̃(ρ), s⟩ = value`. `inputSpec`: from doom of "the claim at depth `12` holds of the
committed inputs" to doom of "the `64` slice claims hold at `(λ, r_pack, ρ)`", each of the ten
challenges escaping at `L₀·2/|E|`; the carried predicate `R` rides along.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

section

/-- The end of `verify_keccak`, after the outputs' opening. -/
def inputTail (h : ℕ) (claim : KeccakClaim) (outputs : List ColumnClaim) :
    VerifierProgram (List ColumnClaim × List E × List E) :=
  sumcheck claim.value 3 (List.replicate 4 none) >>= fun y ↦
  keccakOpen h claim 0 keccakSegments y.2 >>= fun x ↦
  VerifierProgram.readScalars kBits >>= fun slices ↦
  VerifierProgram.require (multilinearEval claim.mu y.1 * dot x.2.1 slices = x.2.2) >>= fun _ ↦
  pure (outputs, y.1 ++ claim.point.take (h - 4) ++ x.1, slices)

theorem multilinearEval_mu {mu low : List E} (hmu : mu.length = 16) (hlow : low.length = 4) :
    multilinearEval mu low = MuT mu low := by
  rw [multilinearEval_eq low mu (by rw [hmu, hlow]; rfl), MuT, hlow]

/-- **The final check**: with true slices, the check gives the slot rounds' last claim. -/
theorem final_in (P : ℕ) (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    {low slot slices : List E} (hlow : low.length = 4) (hslot : slot.length = 6) (value : E)
    (hs : slicesTrue (P + 4) col (low ++ claim.point.take P ++ slot) slices)
    (hc : multilinearEval claim.mu low *
      dot ((foldAll slot (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD []) slices =
        value) :
    value = Fs P col claim low slot := by
  have ha : (low ++ claim.point.take P).length = P + 4 := by
    simp [hlow, hshape.2.1]; omega
  rw [← hc, Fs, cubeSum_full _ hslot, multilinearEval_mu hshape.1 hlow,
    dot_eq _ _ (by rw [fold_in_length P claim hslot, hs.2.1]), fold_in_length P claim hslot]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun z hz ↦ ?_)
  have hz' := Finset.mem_range.1 hz
  rw [fold_in P claim hslot hz', hs.2.2 z hz', ← slices_eq P col ha hslot z]

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

open Classical in
/-- **The inputs' opening.** Lead `0`; the ten sumcheck challenges' groups `L₀·2/|E|`, the
follower's lead `T` after the slices. -/
noncomputable def inputSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (outs : List ColumnClaim) (hT : T ≤ εmax) (h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax) :
    Spec (inputTail (P + 4) claim outs)
      (Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q))
      (fun res h ↦ res.1 = outs ∧
        Doomed C (fun q ↦ slicesTrue (P + 4) (qk q) res.2.1 res.2.2 ∧ R q) h) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  ((sumcheckSpec (T := 0) hst hcard R (Fl_plainFamily P qk claim) (count := 3) (by norm_num)
    (by norm_num) h0 he 4 [] claim.value (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by rw [ClaimTrue, ← Fl_nil, hv], hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun y ↦
  if hy : y.1.length = 4 then
    (Spec.congr (keccakOpen_eq (P + 4) claim 0 keccakSegments y.2).symm <|
      Spec.congr (p := sumcheck y.2 3 (List.replicate 6 none) >>= fun x ↦
        VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) claim 0
            keccakSegments)).headD [],
          x.2)) (by rw [qkeccakSlotBits_eq]) <|
      ((sumcheckSpec (T := 0) hst hcard R (Fs_plainFamily P qk claim y.1) (count := 3)
        (by norm_num) (by norm_num) h0 he 6 [] y.2 (by simp)).mono
        (fun _ (hd : y.1.length = 4 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦ ⟨by
          rw [List.nil_append, Fl, cubeSum_full _ hy, hv, Fs_nil P (qk q) claim hshape hy], hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
      (Spec.ret (Post := fun (x' : List E × List E × E) h ↦ x'.1.length = 6 ∧
          x'.2.1 = (foldAll x'.1 (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD [] ∧
          Doomed C (fun q ↦ x'.2.2 = Fs P (qk q) claim y.1 x'.1 ∧ R q) h)
        (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD [], x.2)).mono
        (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
        le_rfl).bind' fun x ↦
    if hx : x.1.length = 6 ∧
        x.2.1 = (foldAll x.1 (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD [] then
      ((doomReadN (T := T) hst _ hT 63).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl
        le_rfl le_rfl).bind' fun slices ↦
      (Spec.require
        (Pre := fun h ↦ slices.length = 63 + 1 ∧
          Doomed C (fun q ↦ x.2.2 = Fs P (qk q) claim y.1 x.1 ∧ R q) h)
        (Post := fun _ h ↦ Doomed C (fun q ↦
          slicesTrue (P + 4) (qk q) (y.1 ++ claim.point.take (P + 4 - 4) ++ x.1) slices ∧ R q) h)
        fun _ hd hc ↦ Doomed.mono hd.2 fun q ⟨hs, hR⟩ ↦ ⟨by
          rw [show P + 4 - 4 = P by omega] at hs
          rw [hx.2] at hc
          exact final_in P (qk q) claim hshape hy hx.1 _ hs hc, hR⟩).bind' fun _ ↦
      (Spec.ret (outs, y.1 ++ claim.point.take (P + 4 - 4) ++ x.1, slices)).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakGkrTail` =====

/-!
# `verifyKeccak` as a specification

`verify_keccak` (`crates/verifier/src/keccak.rs:235-294`) is `gkrProg` (by `rfl`): the segment and
lane challenges, `committed`, twelve layers, the committed outputs' opening and the inputs' opening
(`inputTail`). Candidates are stacks of type `β`, each with its `q_keccak` column `qk q` (word `n`
at `qk q n`); `C h` is the set of candidates a history binds (`Stable`, at most `L₀`).

**Alive predicates**, in order (`R` is carried throughout):

| after | a candidate `q` is alive when |
| --- | --- |
| the start | `outClaimsTrueMid` and `midAgree` at `inst` |
| `j` of the six segment and lane challenges | the mismatch table's extension at them is zero (`ZeroOn`) |
| `committed` | the first claim holds of `q`'s states, and `committed` opens `q`'s middle state |
| each layer | as in `layerSpec`; the open value is carried |
| the outputs' slot rounds | as in `sumcheckSpec`, for the family `Fo` |
| `word` and the check | the column claim at `(inst, ρ)` holds; the claim at depth `12` is carried |
| the inputs' opening | as in `inputSpec` |

**Escape bounds** (each group, `|E| = 2^192`): the start's six challenges `L₀/|E|` each (lead
`L₀·6/|E|`); per layer, `s` at `L₀·46/|E|`, each of the `P + 1` pack rounds and `11` position
rounds at `L₀·3/|E|`, `β` at `L₀·2/|E|`; the openings' `6 + 4 + 6` rounds at `L₀·2/|E|`. The
largest is `L₀·46/|E|`, which is the hypothesis `h46 : L₀·46/|E| ≤ εmax`; for `L₀ ≤ 2^12` it is
below `2^-174 < 2^-128` (`EndToEnd.Sound.phase_errors`).

`gkrSpec` states it with `Pre := Doomed C (outClaimsTrueMid ∧ midAgree ∧ R)`. The statement in
terms of `keccakF` of the inputs needs `RegionValid` (the committed middle state is twelve
rounds of the input at every step): `gkrSpec_regionValid`, from `Doomed C (outClaimsTrue ∧
RegionValid ∧ R)` to doom of the reduction's claims with `RegionValid` carried. `RegionValid`
cannot be dropped from the carried predicate: `inst` is drawn before this phase, and a middle
state wrong at some step but agreeing with twelve rounds of the input at `inst` passes every
check here (the phase drawing `inst` charges that, `zeroOn_escape`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

section

/-! ## The program -/

/-- `verify_keccak`, the `do` block's join points inlined. -/
def gkrProg (h : ℕ) (inst output : List E) : VerifierProgram (List ColumnClaim × List E × List E) :=
  VerifierProgram.sampleChallenges keccakSegmentBits >>= fun segment ↦
  VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
  VerifierProgram.readScalar >>= fun committed ↦
  keccakLayers h (List.range keccakDepth) (firstClaim inst segment lanesPt output committed) >>=
    fun claim ↦
  keccakOpen h (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
    committed >>= fun x ↦
  VerifierProgram.readScalar >>= fun word ↦
  VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
  inputTail h claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)]

theorem verifyKeccak_eq (h : ℕ) (inst output : List E) :
    verifyKeccak h inst output = gkrProg h inst output := rfl

/-! ## The committed outputs' check -/

/-- **The outputs' check**: a true column claim and the check give the slot rounds' last
claim. -/
theorem final_out (P : ℕ) (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = P + 4) (committed : E) {slot : List E} (hslot : slot.length = 6)
    (word value : E)
    (htrue : colTrue (P + 4) col ⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ slot, word⟩)
    (hc : ((foldAll slot (keccakSlotWeights (P + 4)
      (firstClaim inst segment lanesPt output committed) 1 1)).headD []).headD 0 * word = value) :
    value = Fo (P + 4) col inst segment lanesPt slot := by
  rw [← hc, fold_out hi committed hslot, Fo, cubeSum_full _ hslot]
  refine congrArg (HMul.hMul _) ?_
  obtain ⟨-, -, hv⟩ := htrue
  change word = _ at hv
  rw [hv, List.take_append_drop, ← hslot, col_split hi, Qo, hslot]
  rfl

/-- v1's openings after the layers (the end of `gkrProg`). -/
def v1Tail (h : ℕ) (inst output segment lanesPt : List E) (committed : E) (claim : KeccakClaim) :
    VerifierProgram (List ColumnClaim × List E × List E) :=
  keccakOpen h (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
    committed >>= fun x ↦
  VerifierProgram.readScalar >>= fun word ↦
  VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
  inputTail h claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)]

/-! ## The specification -/

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The alive predicate after `committed`. -/
def AliveC (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (inst segment lanesPt output : List E)
    (committed : E) (q : β) : Prop :=
  ClaimTrue (statesAt (P + 4) (qk q) 0) P (firstClaim inst segment lanesPt output committed) ∧
    (OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)

/-- The postcondition: the column claims and the slice claims. -/
def KeccakPost (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (C : List Ev → Set β)
    (res : List ColumnClaim × List E × List E) (h : List Ev) : Prop :=
  Doomed C (fun q ↦ (∀ c ∈ res.1, colTrue (P + 4) (qk q) c) ∧
    slicesTrue (P + 4) (qk q) res.2.1 res.2.2 ∧ R q) h

open Classical in
/-- v1's openings after the layers (`v1Tail`): the committed outputs' slot rounds and check, then
the inputs' opening. Lead `0`. -/
noncomputable def outTailSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst segment lanesPt : List E} (output : List E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (committed : E) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (claim : KeccakClaim)
    (hc : ClaimShape P claim) :
    Spec (v1Tail (P + 4) inst output segment lanesPt committed claim)
      (Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧
        (OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)))
      (KeccakPost qk R P C) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h2' : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  let first := firstClaim inst segment lanesPt output committed
  (Spec.congr (keccakOpen_eq (P + 4) first 1 (keccakSegments - 1) committed).symm <|
    Spec.congr (p := sumcheck committed 3 (List.replicate 6 none) >>= fun x ↦
      VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD
          [], x.2))
      (by rw [qkeccakSlotBits_eq]; rfl) <|
    ((sumcheckSpec (T := 0) hst hcard
      (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)
      (Fo_plainFamily (P + 4) qk inst segment lanesPt) (count := 3) (by norm_num)
      (by norm_num) h0 h2' 6 [] committed (by simp)).mono
      (fun _ (hd : Doomed C _ _) ↦ Doomed.mono hd
        fun q ⟨hv, hct, hR⟩ ↦ ⟨hct, by
          rw [OpenTrue, hv, Fo_nil (P + 4) (qk q) inst hs hl], hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
    (Spec.ret (Post := fun (x' : List E × List E × E) h ↦ x'.1.length = 6 ∧
        x'.2.1 = (foldAll x'.1 (keccakSlotWeights (P + 4) first 1 1)).headD [] ∧
        Doomed C (fun q ↦ x'.2.2 = Fo (P + 4) (qk q) inst segment lanesPt x'.1 ∧
          (ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)) h)
      (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD [], x.2)).mono
      (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun x ↦
  if hx : x.1.length = 6 ∧
      x.2.1 = (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD [] then
    ((doomRead (T := 0) hst _ h0).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun word ↦
    (Spec.require
      (Pre := Doomed C (fun q ↦ x.2.2 = Fo (P + 4) (qk q) inst segment lanesPt x.1 ∧
          (ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)))
      (Post := fun _ h ↦ Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧
        ((∀ c ∈ [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)],
          colTrue (P + 4) (qk q) c) ∧ R q)) h)
      fun _ hd hcheck ↦ Doomed.mono hd fun q ⟨hct, hcol, hR⟩ ↦ ⟨by
        rw [hx.2] at hcheck
        exact final_out P (qk q) hi committed hx.1 word _ (hcol _ (List.mem_singleton_self _))
          hcheck, hct, hR⟩).bind' fun _ ↦
    (inputSpec hst hcard _ qk P claim hc _ hT h2).mono (fun _ h' ↦ h')
      (fun res h' (hr : res.1 = _ ∧ _) ↦ Doomed.mono hr.2 fun q ⟨hcol, hsl, hR⟩ ↦
        ⟨hsl, by rw [← hr.1]; exact hcol, hR⟩) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

open Classical in
/-- After `committed`: the layers and the two openings. Lead `0`. -/
noncomputable def midSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst segment lanesPt : List E} (output : List E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (committed : E) (hT : T ≤ εmax)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (keccakLayers (P + 4) (List.range keccakDepth)
        (firstClaim inst segment lanesPt output committed) >>= fun claim ↦
      keccakOpen (P + 4) (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
        committed >>= fun x ↦
      VerifierProgram.readScalar >>= fun word ↦
      VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
      inputTail (P + 4) claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)])
      (Doomed C (AliveC qk R P inst segment lanesPt output committed))
      (KeccakPost qk R P C) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h2' : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  let first := firstClaim inst segment lanesPt output committed
  (Spec.congr (p := keccakLayers (P + 4) (List.range' 0 12) first) (by rw [List.range_eq_range']; rfl)
    (layersSpec (T := 0) hst hcard (fun q ↦ OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)
      qk P h46 h2' 12 0 rfl first (firstClaim_shape committed hi hs))).bind' fun claim ↦
  if hc : ClaimShape P claim then
    (outTailSpec hst hcard R qk P output hi hs hl committed hT h46 claim hc).mono
      (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-! ## The start -/

/-- The escape bound of the `i`-th of `n` zero-test coordinates (`1` past them, never used). -/
noncomputable def ztE (n i : ℕ) : ℝ≥0∞ := if i < n then errE 1 else 1

omit [Finite β] in
theorem zt_escape (δ : β → ℕ → E) (R : β → Prop) (pre : List E) {n : ℕ}
    (hpre : pre.length + n = 6) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) (pre ++ acc) 6 ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (pre ++ (acc ++ [c])) 6 ∧ R q)) ≤ ztE n acc.length := by
  unfold ztE
  split_ifs with hn
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (zeroOn_escape (δ q) (acc := pre ++ acc) (by simp; (clear * - hpre hn; omega)) fun h ↦ hq ⟨h, hR⟩)
      rw [List.append_assoc]; exact hc.1
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem keccakSegmentBits_eq : keccakSegmentBits = 1 := by decide

theorem lead_eq (L₀ : ℕ) :
    (∑ i ∈ range 1, (L₀ : ℝ≥0∞) * ztE 6 (0 + i)) +
        ((∑ i ∈ range 5, (L₀ : ℝ≥0∞) * ztE 5 (0 + i)) + 0) = (L₀ : ℝ≥0∞) * errE 6 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ztE, errE]
  norm_num
  ring

/-! ## The reduction at a shape (lvm2 T-G)

`gkrProgS sh h inst output k`: the segment and lane challenges, `committed` (read with two
segments, `0` with one), `sh.depth` layers from the first claim, then the continuation `k` on the
challenges, `committed` and the claim on the inputs. v1's `gkrProg` is `gkrProgS Shape.v1` with
the openings of the committed outputs and inputs as `k` (`gkrProg_v1`); the tape's reduction
(BLUEPRINT2 T2) is `gkrProgS Shape.tape` with `k` returning the claim (`tapeGkr`).

`gkrSpecS`: from doom of "the output claims and the segments' agreement hold at `inst`" to the
continuation's specification, with doom of "the claim on the inputs holds and `committed` is
open" (`AliveKS`). Lead `L₀·(segBits + 5)/|E|`; each layer's groups as in `layerSpecS`. The layers
are one recursive specification (`layersSpecS`), not unrolled. -/

/-- The reduction at a shape, with the continuation `k` after the layers. -/
def gkrProgS {α : Type} (sh : Shape) (h : ℕ) (inst output : List E)
    (k : List E → List E → E → KeccakClaim → VerifierProgram α) : VerifierProgram α :=
  VerifierProgram.sampleChallenges sh.segBits >>= fun segment ↦
  VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
  (if 1 < sh.segments then VerifierProgram.readScalar else pure 0) >>= fun committed ↦
  keccakLayersS sh h (List.range sh.depth) (firstClaimS sh inst segment lanesPt output committed) >>=
    fun claim ↦
  k segment lanesPt committed claim

theorem gkrProg_v1 (h : ℕ) (inst output : List E) :
    gkrProg h inst output = gkrProgS Shape.v1 h inst output (v1Tail h inst output) := by
  simp only [gkrProg, gkrProgS, keccakLayers_v1]
  rfl

/-- **The tape's reduction** (BLUEPRINT2 §1.2 T2): `24 × 1`, no openings; it returns the claim on
the inputs. -/
def tapeGkr (h : ℕ) (inst output : List E) : VerifierProgram KeccakClaim :=
  gkrProgS Shape.tape h inst output fun _ _ _ claim ↦ pure claim


open Classical in
/-- **The layers at a shape, from depth `d`** (at least one): lead `0`; each layer's groups as in
`layerSpecS`, the last one's follower lead `T`. -/
noncomputable def layersSpecS {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    (n d : ℕ) → d + n + 1 = sh.depth → (claim : KeccakClaim) → ClaimShape P claim →
      Spec (keccakLayersS sh (sh.logSteps P) (List.range' d (n + 1)) claim)
        (Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShape P c ∧
          Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) εmax 0 T
  | 0, d, hd, claim, hs =>
    ((layerSpecS (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      h46 hβ).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundS hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    (Spec.ret (Post := fun c h ↦ ClaimShape P c ∧
        Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P c ∧ R q) h) c).mono
      (fun _ h' ↦ by rw [show d + 1 = sh.depth by omega] at h'; exact h') (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpecS (T := T) hsh hst hcard R (fun q ↦ statesOfS sh P (Iq q) (d + 1)) d P claim hs
      h46 hβ).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_roundS hsh P (Iq q) (by omega) claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
    if hc : ClaimShape P c then
      (layersSpecS hsh hst hcard R Iq P h46 hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- The alive predicate after `committed`, at a shape. -/
def AliveKS (sh : Shape) (Iq : β → ℕ → ℕ → KeccakState) (R : β → Prop) (P : ℕ)
    (inst segment lanesPt output : List E) (committed : E) (q : β) : Prop :=
  ClaimTrue (statesOfS sh P (Iq q) 0) P (firstClaimS sh inst segment lanesPt output committed) ∧
    (OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q)

omit [Finite β] in
/-- The escape of the `i`-th of `n` zero-test coordinates (`zt_escape` on `n` bits). -/
theorem zt_escapeS {n : ℕ} (δ : β → ℕ → E) (R : β → Prop) (pre : List E) {k : ℕ}
    (hpre : pre.length + k = n) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) (pre ++ acc) n ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (pre ++ (acc ++ [c])) n ∧ R q)) ≤ ztE k acc.length := by
  unfold ztE
  split_ifs with hn
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (zeroOn_escape (δ q) (acc := pre ++ acc) (by simp; (clear * - hpre hn; omega)) fun h ↦ hq ⟨h, hR⟩)
      rw [List.append_assoc]; exact hc.1
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem lead_eqS (L₀ b : ℕ) :
    (∑ i ∈ range b, (L₀ : ℝ≥0∞) * ztE (b + 5) (0 + i)) +
        ((∑ i ∈ range 5, (L₀ : ℝ≥0∞) * ztE 5 (0 + i)) + 0) = (L₀ : ℝ≥0∞) * errE (b + 5) := by
  have e1 : ∀ n k, n ≤ k → ∑ i ∈ range n, (L₀ : ℝ≥0∞) * ztE k (0 + i) =
      n * ((L₀ : ℝ≥0∞) * errE 1) := by
    intro n k hnk
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [ztE, if_pos (by have := Finset.mem_range.1 hi; (clear * - hnk this; omega))], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rw [e1 b (b + 5) (by (clear * -; omega)), e1 5 5 le_rfl, errE, errE]
  push_cast
  ring

theorem depth_pos {sh : Shape} (hsh : sh.Ok) : 0 < sh.depth := by
  rcases Nat.eq_zero_or_pos sh.depth with h | h
  · have := hsh.2; rw [h, zero_mul] at this; (clear * - this; omega)
  · exact h

open Classical in
/-- After `committed`, at a shape: the layers, then the continuation. Lead `0`. -/
noncomputable def midSpecS {α : Type} {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    {inst segment lanesPt : List E} (output : List E) (hi : inst.length = sh.logSteps P)
    (hs : segment.length = sh.segBits) (hl : lanesPt.length = 5) (committed : E)
    (hc0 : sh.segments = 1 → committed = 0)
    {Tk : ℝ≥0∞} {Post : α → List Ev → Prop}
    (k : List E → List E → E → KeccakClaim → VerifierProgram α)
    (hk : ∀ claim, ClaimShape P claim →
      Spec (k segment lanesPt committed claim)
        (Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P claim ∧
          (OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q)))
        Post εmax Tk T)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + Tk ≤ εmax) :
    Spec (keccakLayersS sh (sh.logSteps P) (List.range sh.depth)
        (firstClaimS sh inst segment lanesPt output committed) >>= fun claim ↦
      k segment lanesPt committed claim)
      (Doomed C (AliveKS sh Iq R P inst segment lanesPt output committed)) Post εmax 0 T :=
  have hd := depth_pos hsh
  Spec.congr (p := keccakLayersS sh (sh.logSteps P) (List.range' 0 (sh.depth - 1 + 1))
      (firstClaimS sh inst segment lanesPt output committed) >>= fun claim ↦
      k segment lanesPt committed claim)
    (by rw [show sh.depth - 1 + 1 = sh.depth by omega, List.range_eq_range']) <|
  ((layersSpecS (T := Tk) hsh hst hcard
      (fun q ↦ OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q) Iq P h46 hβ
      (sh.depth - 1) 0 (by omega) _ (firstClaimS_shape hsh committed hi hs)).mono
    (fun _ h' ↦ h') (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun claim ↦
  if hc : ClaimShape P claim then
    (hk claim hc).mono (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

open Classical in
/-- `committed`: read with two segments, `0` with one. Lead `0`. -/
noncomputable def committedSpecS {sh : Shape} (hsh : sh.Ok) (hst : Stable C) (R : β → Prop)
    (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ) {inst segment lanesPt output : List E}
    (hi : inst.length = sh.logSteps P) (ho : output.length = 25)
    (hs : segment.length = sh.segBits) (hl : lanesPt.length = 5) (h0 : (0 : ℝ≥0∞) ≤ εmax) :
    Spec (if 1 < sh.segments then VerifierProgram.readScalar else pure 0)
      (fun h ↦ lanesPt.length = 5 ∧ Doomed C (fun q ↦ ZeroOn
        (startDeltaS sh (sh.logSteps P) (Iq q) inst output) (segment ++ ([] ++ lanesPt))
        (sh.segBits + 5) ∧ R q) h)
      (fun c h ↦ (sh.segments = 1 → c = 0) ∧
        Doomed C (AliveKS sh Iq R P inst segment lanesPt output c) h) εmax 0 0 :=
  Spec.ite
    (fun hseg ↦ Spec.readE (fun h₀ c hd ↦ ⟨fun h1 ↦ absurd h1 (by omega),
      (Doomed.append hst rfl).mpr (Doomed.mono hd.2 fun q ⟨htrue, hopen, hR⟩ ↦
        ⟨by rw [List.nil_append]; exact zeroOn_of_firstS hsh P (Iq q) hi hs hl ho c hopen htrue,
          hR⟩)⟩) h0)
    (fun _ ↦ (Spec.ret (Post := fun c h ↦ (sh.segments = 1 → c = 0) ∧
        Doomed C (AliveKS sh Iq R P inst segment lanesPt output c) h) 0).mono
      (fun _ hd ↦ ⟨fun _ ↦ rfl, Doomed.mono hd.2 fun q ⟨htrue, hopen, hR⟩ ↦
        ⟨by rw [List.nil_append]; exact zeroOn_of_firstS hsh P (Iq q) hi hs hl ho 0 hopen htrue,
          hR⟩⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl)

open Classical in
/-- **The Keccak reduction at a shape**, round by round, up to the continuation `k`: from doom
of "the output claims and the segments' agreement hold at `inst`" to `k`'s postcondition. Lead
`L₀·(segBits + 5)/|E|`; the layers' groups `L₀·46/|E|`, `L₀·3/|E|`, `L₀·2/|E|`; `k`'s lead `Tk`. -/
noncomputable def gkrSpecS {α : Type} {sh : Shape} (hsh : sh.Ok) (hst : Stable C)
    (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop) (Iq : β → ℕ → ℕ → KeccakState) (P : ℕ)
    {inst output : List E} (hi : inst.length = sh.logSteps P) (ho : output.length = 25)
    {Tk : ℝ≥0∞} {Post : α → List Ev → Prop}
    (k : List E → List E → E → KeccakClaim → VerifierProgram α)
    (hk : ∀ segment lanesPt committed claim, segment.length = sh.segBits → lanesPt.length = 5 →
      ClaimShape P claim → (sh.segments = 1 → committed = 0) →
      Spec (k segment lanesPt committed claim)
        (Doomed C (fun q ↦ ClaimTrue (statesOfS sh P (Iq q) sh.depth) P claim ∧
          (OpenTrueS sh (sh.logSteps P) (Iq q) inst segment lanesPt committed ∧ R q)))
        Post εmax Tk T)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + Tk ≤ εmax) :
    Spec (gkrProgS sh (sh.logSteps P) inst output k)
      (Doomed C (fun q ↦ outClaimsTrueMidS sh (sh.logSteps P) (Iq q) inst output ∧
        midAgreeS sh (sh.logSteps P) (Iq q) inst ∧ R q))
      Post εmax ((L₀ : ℝ≥0∞) * errE (sh.segBits + 5)) T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  let δ := fun q ↦ startDeltaS sh (sh.logSteps P) (Iq q) inst output
  ((doomSampleN (εmax := εmax) hst hcard
    (fun acc q ↦ ZeroOn (δ q) ([] ++ acc) (sh.segBits + 5) ∧ R q)
    (ztE (sh.segBits + 5)) (fun acc q hq ↦ zt_escapeS δ R [] (by simp) acc q hq) sh.segBits
    []).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ by
      obtain ⟨h1, h2⟩ := claims_of_zeroOnS hsh _ (Iq q) inst output (by simpa using hz)
      exact ⟨h1, h2, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (lead_eqS L₀ sh.segBits)) le_rfl).bind' fun segment ↦
  if hs : segment.length = sh.segBits then
    ((doomSampleN (εmax := εmax) hst hcard
      (fun acc q ↦ ZeroOn (δ q) (segment ++ acc) (sh.segBits + 5) ∧ R q)
      (ztE 5) (fun acc q hq ↦ zt_escapeS δ R segment (by rw [hs]) acc q hq) 5 []).mono
      (fun _ (hd : segment.length = sh.segBits ∧ _) ↦ by simpa using hd.2) (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl).bind' fun lanesPt ↦
    if hl : lanesPt.length = 5 then
      (committedSpecS hsh hst R Iq P hi ho hs hl h0).bind' fun committed ↦
      if hc0 : sh.segments = 1 → committed = 0 then
        (midSpecS hsh hst hcard R Iq P output hi hs hl committed hc0 k
          (fun claim hc ↦ hk segment lanesPt committed claim hs hl hc hc0) h46 hβ).mono
          (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h' ↦ hc0 h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hl hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-! ### The tape: `24 × 1` -/

theorem keccakF_roundsFrom (a : KeccakState) : keccakF1600 a = roundsFrom 0 24 a := rfl

/-- The tape's states on the inputs `I` (one segment): row `x`'s state after `24 - d` rounds. -/
abbrev tapeStates (P : ℕ) (I : ℕ → KeccakState) (d : ℕ) : States :=
  statesOfS Shape.tape P (fun _ ↦ I) d

/-- **The tape's input claim** (BLUEPRINT2 T2's `C_in = Σ_i ι(i)·⟨ω, in(i)⟩`): a claim holds of the
tape's inputs when its value is `Σ_x eq(point, x ≫ 4)·μ[x & 15]·⟨w, bits(I x)⟩` over the
`2^(P+5)` rows. -/
theorem claimTrue_tapeStates (P : ℕ) (I : ℕ → KeccakState) (c : KeccakClaim) :
    ClaimTrue (tapeStates P I 24) P c ↔
      c.value = ∑ x ∈ range (2 ^ (P + 5)), eqAt c.point (x / 16) * c.mu.getD (x % 16) 0 *
        ∑ j ∈ range 1600, c.weights.getD j 0 * bitE (sbit (I x) j) := by
  rw [tapeStates, claimTrue_inputs_tape,
    show 2 ^ (P + 5) = 2 ^ (P + 1) * 16 by rw [show P + 5 = (P + 1) + 4 from rfl, pow_add]; rfl,
    sum_range_mul]
  refine Iff.of_eq (congrArg _ (Finset.sum_congr rfl fun z _ ↦ ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  rw [show (16 * z + i) / 16 = z by (clear * - hi'; omega), show (16 * z + i) % 16 = i by (clear * - hi'; omega),
    show i + 16 * z = 16 * z + i by ring]
  ring

/-- The tape's first claim (`firstClaimS Shape.tape` with no segment and `committed = 0`): the
lanes of the outputs at `inst`, combined at `lanesPt`. -/
def tapeFirstClaim (inst lanesPt output : List E) : KeccakClaim :=
  ⟨dot ((eqKernel lanesPt).take 25) output, eqKernel (inst.take 4), inst.drop 4,
    firstWeights lanesPt⟩

theorem firstClaimS_tape (inst lanesPt output : List E) :
    firstClaimS Shape.tape inst [] lanesPt output 0 = tapeFirstClaim inst lanesPt output := by
  have e : (eqKernel ([] : List E)).getD (Shape.tape.segments - 1) 0 = 1 := by
    rw [eqKernel_getD, show Shape.tape.segments - 1 = 0 from rfl]; simp
  simp only [firstClaimS, tapeFirstClaim, e, zero_add, one_mul, List.append_nil]

/-- **The tape's reduction, flat**: five lane challenges, then the `24` layers from the first
claim. No segment challenge, no `committed`, no openings. -/
theorem tapeGkr_eq (h : ℕ) (inst output : List E) :
    tapeGkr h inst output = VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
      keccakLayersS Shape.tape h (List.range 24) (tapeFirstClaim inst lanesPt output) := by
  simp only [tapeGkr, gkrProgS, bind_pure, ← firstClaimS_tape]
  rfl

open Classical in
/-- **The tape's reduction** (`24 × 1`, BLUEPRINT2 T2): from doom of "the `25` output-lane claims
`Σ_x eq(inst, x)·lane_l(keccakF(I x)) = output_l` hold" to doom of "the returned claim holds of the
inputs" (`claimTrue_inputs_tape` spells it out: `value = Σ_i eq(point, i ≫ 4)·μ[i & 15]·⟨w, I i⟩`).
Lead `L₀·5/|E|`; per layer `L₀·46/|E|` (`s`), `L₀·3/|E|` (each of the `P + 1 + 11` rounds),
`L₀·2/|E|` (`β`); the follower's lead `T`. `logSteps = P + 5` (at least `5`); the caller states the
row count (leanVM's shape check, `keccak.rs:243-246`, is the caller's: `n_log = 21`, `P = 16`). -/
noncomputable def tapeGkrSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (Iq : β → ℕ → KeccakState) (P : ℕ) {inst output : List E} (hi : inst.length = P + 5)
    (ho : output.length = 25) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax)
    (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    Spec (tapeGkr (P + 5) inst output)
      (Doomed C (fun q ↦ (∀ l < 25, stepMle (P + 5) inst
        (fun x ↦ laneWord (keccakF1600 (Iq q x)) l) = output.getD l 0) ∧ R q))
      (fun c h ↦ ClaimShape P c ∧ Doomed C (fun q ↦ ClaimTrue (tapeStates P (Iq q) 24) P c ∧ R q) h)
      εmax ((L₀ : ℝ≥0∞) * errE 5) T :=
  (gkrSpecS Shape.tape_ok hst hcard R (fun q _ ↦ Iq q) P hi ho (fun _ _ _ claim ↦ pure claim)
    (fun _ _ committed claim _ _ hc hc0 ↦
      (Spec.ret (Post := fun c h ↦ ClaimShape P c ∧
          Doomed C (fun q ↦ ClaimTrue (tapeStates P (Iq q) 24) P c ∧ R q) h) claim).mono
        (fun _ hd ↦ ⟨hc, Doomed.mono hd fun q ⟨hct, hR⟩ ↦
          ⟨hct, by rw [OpenTrueS, if_pos (show Shape.tape.segments = 1 from rfl)]; exact hc0 rfl, hR⟩⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl) h46 hβ).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hout, _, hR⟩ ↦ ⟨fun l hl ↦ hout l hl, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (by rw [Shape.tape_segBits])) le_rfl

open Classical in
/-- **The Keccak reduction** (`verify_keccak`, `keccak.rs:235-294`), round by round: from
doom of "the output-lane claims (against the committed middle state) and the middle state's
claims hold at `inst`" to doom of "the column claims and the `64` slice claims it leaves hold".
Lead `L₀·6/|E|` (the segment and lane challenges); every other group's lead is at most
`L₀·46/|E| ≤ εmax`; the follower's lead `T` after the slices. -/
noncomputable def gkrSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrueMid (P + 4) (qk q) inst output ∧
        midAgree (P + 4) (qk q) inst ∧ R q))
      (KeccakPost qk R P C) εmax ((L₀ : ℝ≥0∞) * errE 6) T :=
  have h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by
    rw [add_zero]; exact le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  Spec.congr ((gkrProg_v1 (P + 4) inst output).symm.trans (verifyKeccak_eq (P + 4) inst output).symm) <|
  (gkrSpecS Shape.v1_ok hst hcard R (fun q ↦ inState (P + 4) (qk q)) P hi ho
    (v1Tail (P + 4) inst output)
    (fun segment lanesPt committed claim hs hl hc _ ↦
      (outTailSpec hst hcard R qk P output hi (hs.trans Shape.v1_segBits) hl committed hT h46 claim
        hc).mono
        (fun _ hd ↦ Doomed.mono hd fun q ⟨hct, hopen, hR⟩ ↦
          ⟨hct, (openTrue_v1 _ _ _ _ _ _).1 hopen, hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl) h46 h2).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hmid, hagree, hR⟩ ↦
      ⟨hmid, (midAgree_v1 _ _ _).2 hagree, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (by rw [Shape.v1_segBits])) le_rfl

/-! ## The statement against `keccakF` -/

theorem outClaims_iff_of_regionValid (h : ℕ) (col : ℕ → K) (inst output : List E)
    (hv : RegionValid h col) :
    outClaimsTrue h col inst output ↔ outClaimsTrueMid h col inst output := by
  have hx : ∀ x ∈ range (2 ^ h), keccakF1600 (inState h col 0 x) = roundsFrom 12 12 (inState h col 1 x) :=
    fun x hx ↦ by rw [keccakF_eq, hv x (Finset.mem_range.1 hx)]
  have e : ∀ l, stepMle h inst (fun x ↦ laneWord (keccakF1600 (inState h col 0 x)) l) =
      stepMle h inst (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) l) := fun l ↦
    Finset.sum_congr rfl fun x hxr ↦ by simp only; rw [hx x hxr]
  unfold outClaimsTrue outClaimsTrueMid
  simp only [e]

/-- **The Keccak reduction against `keccakF`**: from doom of "the output-lane claims against
`keccakF` of the inputs hold at `inst`, the region is valid, and `R`", to doom of the reduction's
claims with `RegionValid` and `R` carried. -/
noncomputable def gkrSpec_regionValid (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrue (P + 4) (qk q) inst output ∧
        RegionValid (P + 4) (qk q) ∧ R q))
      (KeccakPost qk (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) P C) εmax
      ((L₀ : ℝ≥0∞) * errE 6) T :=
  (gkrSpec hst hcard (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) qk P hi ho hT h46).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨hmid, _, hv, hR⟩ ↦
      ⟨(outClaims_iff_of_regionValid _ _ _ _ hv).2 hmid, hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- A column given on `Fin (2^(h + 6))`, read as words of `ℕ` (`0` past the end). -/
def colOfFin {h : ℕ} (c : Fin (2 ^ (h + 6)) → K) : ℕ → K :=
  fun n ↦ if hn : n < 2 ^ (h + 6) then c ⟨n, hn⟩ else 0


end
end LeanVM.Protocol.KeccakGkr
