-- New for lvm2 S1 (E2-F, E2F-V), E2AC-DES §6 statement 7 (`ksSpecE2`): the `KS` Keccak phase's algebra over a
-- field `F` (`LvmKeccakSlotWeights`, `LvmKeccakStart`'s v1 start, `LvmKeccakOpenOut`/`OpenIn`, `LvmKeccakCaller`'s
-- `callDelta`), generic in `F` where the algebra allows, for `LvmE2VKS`.
import LvmE2VGkrSpec
import LvmE2VProgKS
import LvmKeccakCallerPhases

/-!
# The `KS` Keccak phase's algebra over `F`

* the slot weights in closed form (`slotWeightsF_getD`, `slotWtF`) and the fold (`foldAllF_eq`);
* `multilinearEvalF_eq`: `multilinear_eval` is the equality-weighted sum;
* the v1 start (`12 × 2`): the first claim on a candidate (`firstClaimV_sum`), the mismatch table
  `startDeltaV`, `claims_of_zeroOnV`, `zeroOn_of_firstV`;
* the committed outputs' opening (`FoF`, `FoF_nil`, `final_outF`) and the inputs' (`FlF`, `FsF`,
  `FlF_nil`, `FsF_nil`, `final_inF`);
* the caller's zero test `callDeltaF` (`valid_of_callDeltaF_zero`, `callDeltaF_zeroOn`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (States stAt sbit laneWord Shape statesOfS segStateS inState
  roundsFrom RegionValid keccakF_eq sbit_lane lane_inState word_eq_sum)
open Finset Polynomial

section Slot

variable {F : Type} [Field F]

/-! ## Arrays of rows (`LvmKeccakSlotWeights`) -/

/-- Entry `(o, z)` of an array of rows, `0` outside. -/
def rowsAF (rows : Array (Array F)) (o z : ℕ) : F := (rows.getD o #[]).getD z 0

/-- Sixty-four rows of sixty-four entries. -/
def SizedF (rows : Array (Array F)) : Prop :=
  rows.size = 64 ∧ ∀ o < 64, (rows.getD o #[]).size = 64

omit [Field F] in
theorem modify_getDF (rows : Array (Array F)) (i o : ℕ) (f : Array F → Array F) :
    (rows.modify i f).getD o #[] = if i = o ∧ o < rows.size then f (rows.getD o #[])
      else rows.getD o #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = o
  · subst h1
    by_cases h2 : i < rows.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem modify_stepF {rows : Array (Array F)} (hs : SizedF rows) (i z' : ℕ) (x : F) :
    SizedF (rows.modify i fun row ↦ row.setIfInBounds z' x) ∧
      ∀ o z, rowsAF (rows.modify i fun row ↦ row.setIfInBounds z' x) o z =
        if i = o ∧ z' = z ∧ o < 64 ∧ z < 64 then x else rowsAF rows o z := by
  refine ⟨⟨by simp [hs.1], fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
  · rw [modify_getDF]
    split_ifs
    · rw [Array.size_setIfInBounds]; exact hs.2 o ho
    · exact hs.2 o ho
  · rw [rowsAF, modify_getDF, rowsAF]
    by_cases h1 : i = o ∧ o < rows.size
    · rw [ite_eq_left h1, setIfInBounds_getDF]
      have ho : o < 64 := hs.1 ▸ h1.2
      rw [hs.2 o ho]
      by_cases h2 : z' = z ∧ z' < 64
      · rw [ite_eq_left h2, ite_eq_left (show i = o ∧ z' = z ∧ o < 64 ∧ z < 64 from
          ⟨h1.1, h2.1, ho, h2.1 ▸ h2.2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
          fun h ↦ h2 ⟨h.2.1, h.2.1 ▸ h.2.2.2⟩)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
        fun h ↦ h1 ⟨h.1, hs.1 ▸ h.2.2.1⟩)]

/-- The inner loop of `slotWeightsF`: one segment's writes, at rows `b .. b + 24`. -/
theorem inner_rowsF (rows0 : Array (Array F)) (hs : SizedF rows0) (b : ℕ) (V : ℕ → F)
    (hb : b + 25 ≤ 64) : ∀ J, J ≤ 1600 →
      SizedF ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) ∧
      ∀ o z, rowsAF ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) o z =
        if b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J then V (64 * (o - b) + z)
        else rowsAF rows0 o z
  | 0, _ => ⟨hs, fun o z ↦ by simp⟩
  | J + 1, hJ => by
    obtain ⟨hs', hg⟩ := inner_rowsF rows0 hs b V hb J (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs'', hg''⟩ := modify_stepF hs' (b + J / 64) (J % 64) (V J)
    refine ⟨hs'', fun o z ↦ ?_⟩
    rw [hg'', hg]
    by_cases h1 : b + J / 64 = o ∧ J % 64 = z ∧ o < 64 ∧ z < 64
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      congr 1; omega
    · rw [ite_eq_right h1]
      by_cases h2 : b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The weight `slotWeightsF` puts at row `o`, column `z` (`slotW`). -/
def slotWtF (segments w : List F) (first count o z : ℕ) : F :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

/-- The outer loop of `slotWeightsF`. -/
theorem outer_rowsF (segments w : List F) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∀ S, S ≤ count →
      SizedF ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) ∧
      ∀ o z, rowsAF ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) o z = slotWtF segments w first S o z
  | 0, _ => by
    refine ⟨⟨by simp, fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
    · simp [Array.getD_eq_getD_getElem?, ho]
    · simp only [List.range_zero, List.foldl_nil, rowsAF, slotWtF]
      rw [ite_eq_right (by omega)]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      by_cases h : o < 64
      · by_cases h' : z < 64 <;> simp [h, h']
      · simp [h]
  | S + 1, hS => by
    obtain ⟨hs, hg⟩ := outer_rowsF segments w first count hfc S (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_rowsF _ hs (25 * (first + S))
      (fun j ↦ segments.getD S 0 * w.toArray.getD j 0) (by omega) keccakBits le_rfl
    have hk : keccakBits = 1600 := rfl
    refine ⟨hs', fun o z ↦ ?_⟩
    rw [hg', hg, slotWtF, slotWtF]
    by_cases h1 : 25 * (first + S) ≤ o ∧ o < 25 * (first + S) + 25 ∧ z < 64 ∧
        64 * (o - 25 * (first + S)) + z < keccakBits
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArrayF]
      have e1 : o / 25 - first = S := by omega
      have e2 : o % 25 = o - 25 * (first + S) := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : 25 * first ≤ o ∧ o < 25 * (first + S) ∧ z < 64
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem qkeccakSlotBits_eqF : qkeccakSlotBits = 6 := by decide

theorem toListRows_getDF (A : Array (Array F)) {o : ℕ} (ho : o < A.size) (z : ℕ) :
    ((A.toList.map Array.toList).getD o []).getD z 0 = (A.getD o #[]).getD z 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

omit [Field F] in
theorem toListRows_rowF (A : Array (Array F)) {o : ℕ} (ho : o < A.size) :
    (A.toList.map Array.toList).getD o [] = (A.getD o #[]).toList := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

omit [Field F] in
theorem mapRange_getDF (f : ℕ → List F) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-- **`slotWeightsF` in closed form.** -/
theorem slotWeightsF_getD (logSteps : ℕ) (claim : KClaim F) (first count : ℕ)
    (hfc : first + count ≤ 2) {o z : ℕ} (ho : o < 64) :
    ((slotWeightsF logSteps claim first count).getD o []).getD z 0 =
      slotWtF (eqKernelF (claim.point.drop (logSteps - 5))) claim.weights first count o z := by
  obtain ⟨hs, hg⟩ := outer_rowsF (eqKernelF (claim.point.drop (logSteps - 5))) claim.weights
    first count hfc count le_rfl
  rw [← hg o z, rowsAF]
  unfold slotWeightsF
  simp only [qkeccakSlotBits_eqF, show (2 : ℕ) ^ 6 = 64 from rfl]
  exact toListRows_getDF _ (by rw [hs.1]; exact ho) z

theorem slotWeightsF_length (logSteps : ℕ) (claim : KClaim F) (first count : ℕ)
    (hfc : first + count ≤ 2) : (slotWeightsF logSteps claim first count).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rowsF (eqKernelF (claim.point.drop (logSteps - 5))) claim.weights
    first count hfc count le_rfl
  unfold slotWeightsF
  simp only [qkeccakSlotBits_eqF, show (2 : ℕ) ^ 6 = 64 from rfl, List.length_map,
    Array.length_toList]
  exact hs.1

theorem slotWeightsF_row_length (logSteps : ℕ) (claim : KClaim F) (first count : ℕ)
    (hfc : first + count ≤ 2) {o : ℕ} (ho : o < 64) :
    ((slotWeightsF logSteps claim first count).getD o []).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rowsF (eqKernelF (claim.point.drop (logSteps - 5))) claim.weights
    first count hfc count le_rfl
  unfold slotWeightsF
  simp only [qkeccakSlotBits_eqF, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [toListRows_rowF _ (by rw [hs.1]; exact ho), Array.length_toList]
  exact hs.2 o ho

/-! ## The fold along the slot -/

/-- `keccakOpenE2`'s fold of the rows along the slot challenges (`foldAll`). -/
def foldAllF (slot : List F) (rows : List (List F)) : List (List F) :=
  slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

theorem foldRowsF_eq (slot : List F) (rows : List (List F)) :
    foldRowsF slot rows = (foldAllF slot rows).headD [] := rfl

theorem zipWith_getDF (f : F → F → F) (l₁ l₂ : List F) {z : ℕ} (h₁ : z < l₁.length)
    (h₂ : z < l₂.length) : (List.zipWith f l₁ l₂).getD z 0 = f (l₁.getD z 0) (l₂.getD z 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

/-- **The fold is the multilinear extension**, column by column (`foldAll_eq`). -/
theorem foldAllF_eq : ∀ (pt : List F) (rows : List (List F)), rows.length = 2 ^ pt.length →
    (∀ o < rows.length, (rows.getD o []).length = 64) →
    (foldAllF pt rows).length = 1 ∧ ((foldAllF pt rows).headD []).length = 64 ∧
      ∀ z < 64, ((foldAllF pt rows).headD []).getD z 0 =
        ∑ o ∈ range (2 ^ pt.length), eqAtF pt o * (rows.getD o []).getD z 0
  | [], rows, hl, hr => by
    rcases rows with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · simp at hl
    · exact ⟨rfl, hr 0 (by simp), fun z _ ↦ by simp [foldAllF]⟩
    · simp at hl
  | c :: pt, rows, hl, hr => by
    have step : foldAllF (c :: pt) rows = foldAllF pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) := rfl
    have hl' : rows.length / 2 = 2 ^ pt.length := by
      rw [hl, List.length_cons, pow_succ]; omega
    have hrow : ∀ i < rows.length / 2, ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])).getD i [] =
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) []) := fun i hi ↦ mapRange_getDF _ hi
    obtain ⟨h1, h2, h3⟩ := foldAllF_eq pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (by rw [List.length_map, List.length_range, hl'])
      (fun i hi ↦ by
        have hi2 : i < rows.length / 2 := by simpa using hi
        rw [hrow i hi2, List.length_zipWith, hr _ (by omega), hr _ (by omega), min_self])
    rw [step]
    refine ⟨h1, h2, fun z hz ↦ ?_⟩
    rw [h3 z hz, List.length_cons, sum_cube_succW]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [← hl'] at hi'
    rw [hrow i (by omega), zipWith_getDF _ _ _ (by rw [hr _ (by omega)]; exact hz)
      (by rw [hr _ (by omega)]; exact hz), eqAtF_succ, eqAtF_succ]
    have e1 : 2 * i % 2 = 0 := by omega
    have e2 : (2 * i + 1) % 2 = 1 := by omega
    have e3 : 2 * i / 2 = i := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    simp only [e1, e2, e3, e4, ite_true, zero_ne_one, ite_false]
    ring

/-! ## `multilinear_eval` -/

theorem foldPairsF_length (r : F) : ∀ l : List F, (foldPairsF r l).length = l.length / 2
  | a :: b :: rest => by
    simp only [foldPairsF, List.length_cons, foldPairsF_length r rest]; omega
  | [] => by simp [foldPairsF]
  | [_] => by simp [foldPairsF]

theorem foldPairsF_getD (r : F) : ∀ (l : List F) (w : ℕ), 2 * w + 1 < l.length →
    (foldPairsF r l).getD w 0 = l.getD (2 * w) 0 * (1 + r) + l.getD (2 * w + 1) 0 * r
  | a :: b :: rest, 0, _ => by simp [foldPairsF]
  | a :: b :: rest, w + 1, h => by
    simp only [List.length_cons] at h
    have := foldPairsF_getD r rest w (by omega)
    have e1 : 2 * (w + 1) = 2 * w + 1 + 1 := by ring
    have e2 : 2 * (w + 1) + 1 = 2 * w + 1 + 1 + 1 := by ring
    simp only [foldPairsF, List.getD_cons_succ, e1]
    exact this
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

/-- **`multilinear_eval`** of a table of `2^|pt|` entries is its equality-weighted sum. -/
theorem multilinearEvalF_eq : ∀ (pt mle : List F), mle.length = 2 ^ pt.length →
    multilinearEvalF mle pt = ∑ w ∈ range (2 ^ pt.length), eqAtF pt w * mle.getD w 0
  | [], mle, h => by
    rcases mle with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at h
    · simp [multilinearEvalF]
    · simp at h
  | r :: rs, mle, h => by
    have hl : (foldPairsF r mle).length = 2 ^ rs.length := by
      rw [foldPairsF_length, h, List.length_cons, pow_succ]; omega
    have step : multilinearEvalF mle (r :: rs) = multilinearEvalF (foldPairsF r mle) rs := rfl
    rw [step, multilinearEvalF_eq rs _ hl, List.length_cons, sum_cube_succW]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    rw [foldPairsF_getD r mle w (by rw [h, List.length_cons, pow_succ]; omega), eqAtF_succ,
      eqAtF_succ]
    have h1 : 2 * w % 2 = 0 := by omega
    have h2 : (2 * w + 1) % 2 = 1 := by omega
    have h3 : 2 * w / 2 = w := by omega
    have h4 : (2 * w + 1) / 2 = w := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false]
    ring

end Slot

/-! ## The v1 start (`LvmKeccakStart`, `12 × 2`) -/

section Start

/-- A `K` table's word claim at an `F` point (`LvmE2VSpecTape.stepMleF`, restated here so that this
module does not import the tape's specifications). -/
def stepMleK {F : Type} [Field F] [Algebra K F] (w : ℕ) (pt : List F) (f : ℕ → K) : F :=
  ∑ x ∈ range (2 ^ w), eqAtF pt x * kF (f x)

theorem sum_range_mulK {M : Type*} [AddCommMonoid M] (a b : ℕ) (G : ℕ → M) :
    ∑ p ∈ range (a * b), G p = ∑ i ∈ range a, ∑ k ∈ range b, G (b * i + k) := by
  rw [mul_comm, sum_range_mulW]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [add_comm]

variable {F : Type} [Field F] [Algebra K F] [CharP F 2]

omit [CharP F 2] in
theorem kF_ofLaneK (w : UInt64) :
    (kF (K.ofLane w) : F) = ∑ z ∈ range 64, bitF (w.toBitVec.getLsbD z) * nF (2 ^ z) := by
  rw [K.ofLane, word_eq_sum]
  show algebraMap K F _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  cases w.toBitVec.getLsbD z <;> simp [bitF, nF]

omit [CharP F 2] in
/-- The first claim's weights read a state's lanes as words (`sum_firstWeights`). -/
theorem sum_firstWeightsK {lanesPt : List F} (hl : lanesPt.length = 5) (a : KeccakState) :
    ∑ j ∈ range 1600, (firstWeightsF lanesPt).getD j 0 * bitF (sbit a j) =
      ∑ l ∈ range 25, eqAtF lanesPt l * kF (laneWord a l) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mulK]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [laneWord, kF_ofLaneK, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have hj : 64 * l + z < 1600 := by omega
  rw [firstWeightsF, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  have e1 : (64 * l + z) / 64 = l := by omega
  have e2 : (64 * l + z) % 64 = z := by omega
  rw [e1, e2, eqKernelF_getD, hl, ite_eq_left (by omega), sbit_lane a l hz']
  ring

omit [Algebra K F] [CharP F 2] in
/-- A sum over (pack, segment) and instance is a sum over the steps, segment by segment
(`sum_split`). -/
theorem sum_splitF {P : ℕ} {a b seg : List F} (ha : a.length = 5) (hb : b.length = P)
    (G : ℕ → ℕ → F) :
    ∑ z ∈ range (2 ^ (P + 1)), eqAtF (b ++ seg) z *
        ∑ i ∈ range 32, eqAtF a i * G (z / 2 ^ P) (i + 32 * (z % 2 ^ P)) =
      ∑ m ∈ range 2, eqAtF seg m * ∑ x ∈ range (2 ^ (P + 5)), eqAtF (a ++ b) x * G m x := by
  rw [pow_succ, mul_comm (2 ^ P) 2, sum_range_mulK 2 (2 ^ P)]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [show 2 ^ (P + 5) = 2 ^ P * 32 by rw [pow_add]; rfl, sum_range_mulK (2 ^ P) 32,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hy' := Finset.mem_range.1 hy
  have hd : (2 ^ P * m + y) / 2 ^ P = m := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy', zero_add]
  have hmod : (2 ^ P * m + y) % 2 ^ P = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
  rw [eqAtF_append, hb, hd, eqAtF_mod b, hb, hmod, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have e1 : (32 * y + i) / 2 ^ 5 = y := by omega
  have e2 : (32 * y + i) % 2 ^ 5 = i := by omega
  rw [eqAtF_append a b (32 * y + i), ha, e1, eqAtF_mod a (32 * y + i), ha, e2,
    show i + 32 * y = 32 * y + i by ring]
  ring

theorem v1_seg (m : ℕ) : Shape.v1.seg m = m := rfl
theorem v1_step (P m x : ℕ) : Shape.v1.step P m x = x := rfl
theorem v1_depth : Shape.v1.depth = 12 := rfl
theorem v1_segments : Shape.v1.segments = 2 := rfl

omit [CharP F 2] in
/-- **The first claim on a candidate** at v1 (`firstClaimS_sum`): the lanes of the two segments'
outputs, combined. -/
theorem firstClaimV_sum (P : ℕ) (I : ℕ → ℕ → KeccakState) {inst segment lanesPt : List F}
    (hi : inst.length = P + 5) (hl : lanesPt.length = 5) (output : List F) (committed : F) :
    claimSumF (statesOfS Shape.v1 P I 0) P
        (firstClaimSF Shape.v1 inst segment lanesPt output committed).point
        (firstClaimSF Shape.v1 inst segment lanesPt output committed).mu
        (firstClaimSF Shape.v1 inst segment lanesPt output committed).weights =
      ∑ m ∈ range 2, eqAtF segment m * ∑ l ∈ range 25, eqAtF lanesPt l *
        stepMleK (P + 5) inst (fun x ↦ laneWord (segStateS Shape.v1 I m 12 x) l) := by
  have ha : (inst.take 5).length = 5 := by simp [hi]
  have hb : (inst.drop 5).length = P := by simp [hi]
  simp only [firstClaimSF, claimSumF, stAt]
  have hmu : ∀ i ∈ range 32, (eqKernelF (inst.take 5)).getD i 0 = eqAtF (inst.take 5) i :=
    fun i hi' ↦ by
      rw [eqKernelF_getD, ha, ite_eq_left (show i < 2 ^ 5 by
        have := Finset.mem_range.1 hi'; simpa using this)]
  let G : ℕ → ℕ → F := fun m x ↦ ∑ l ∈ range 25, eqAtF lanesPt l *
    kF (laneWord (segStateS Shape.v1 I m 12 x) l)
  have e : ∀ z, ∑ i ∈ range 32, (eqKernelF (inst.take 5)).getD i 0 * ∑ j ∈ range 1600,
      (firstWeightsF lanesPt).getD j 0 *
        bitF (statesOfS Shape.v1 P I 0 (z / 2 ^ P) (i + 32 * (z % 2 ^ P)) j) =
      ∑ i ∈ range 32, eqAtF (inst.take 5) i * G (z / 2 ^ P) (i + 32 * (z % 2 ^ P)) := by
    intro z
    refine Finset.sum_congr rfl fun i hi' ↦ ?_
    rw [hmu i hi']
    exact congrArg _ (sum_firstWeightsK hl _)
  simp only [e]
  rw [sum_splitF ha hb G, List.take_append_drop]
  refine Finset.sum_congr rfl fun m _ ↦ congrArg _ ?_
  simp only [G, stepMleK, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

variable (h : ℕ)

/-- **The output-lane claims** at `inst` against segment `1`'s input (`outClaimsTrueMidS` at v1). -/
def outClaimsTrueMidV (I : ℕ → ℕ → KeccakState) (inst output : List F) : Prop :=
  ∀ l < 25, stepMleK h inst (fun x ↦ laneWord (segStateS Shape.v1 I 1 12 x) l) = output.getD l 0

/-- Segment `0`'s output and segment `1`'s input agree at `inst` (`midAgreeS` at v1). -/
def midAgreeV (I : ℕ → ℕ → KeccakState) (inst : List F) : Prop :=
  ∀ l < 25, stepMleK h inst (fun x ↦ laneWord (segStateS Shape.v1 I 0 12 x) l) =
    stepMleK h inst (fun x ↦ laneWord (I 1 x) l)

/-- `committed` opens segment `1`'s input (`OpenTrueS` at v1). -/
def OpenTrueV (I : ℕ → ℕ → KeccakState) (inst segment lanesPt : List F) (committed : F) : Prop :=
  committed = eqAtF segment 0 * ∑ l ∈ range 25, eqAtF lanesPt l * stepMleK h inst (fun x ↦ laneWord (I 1 x) l)

/-- The fifty mismatches, index `m + 2ℓ` (`startDeltaS` at v1). -/
def startDeltaV (I : ℕ → ℕ → KeccakState) (inst output : List F) (u : ℕ) : F :=
  if u / 2 < 25 then
    stepMleK h inst (fun x ↦ laneWord (segStateS Shape.v1 I (u % 2) 12 x) (u / 2)) +
      (if u % 2 + 1 = 2 then output.getD (u / 2) 0
        else stepMleK h inst (fun x ↦ laneWord (I (u % 2 + 1) x) (u / 2)))
  else 0

omit [Algebra K F] in
theorem addF_eq_zero_iff {a b : F} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- A zero mismatch table: the output claims hold, and the segments agree. -/
theorem claims_of_zeroOnV (I : ℕ → ℕ → KeccakState) (inst output : List F)
    (hz : ZeroOnF (startDeltaV h I inst output) [] 6) :
    outClaimsTrueMidV h I inst output ∧ midAgreeV h I inst := by
  rw [zeroOnF_nil] at hz
  refine ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · have := hz (1 + 2 * l) (by omega)
    have e1 : (1 + 2 * l) / 2 = l := by omega
    have e2 : (1 + 2 * l) % 2 = 1 := by omega
    rw [startDeltaV, e1, e2, if_pos hl, if_pos rfl] at this
    exact addF_eq_zero_iff.1 this
  · have := hz (2 * l) (by omega)
    have e1 : 2 * l / 2 = l := by omega
    have e2 : 2 * l % 2 = 0 := by omega
    rw [startDeltaV, e1, e2, if_pos hl, if_neg (by norm_num)] at this
    exact addF_eq_zero_iff.1 this

/-- **After `committed`** at v1 (`zeroOn_of_firstS`): an open value and a true first claim leave the
mismatch table's extension zero at the challenges. -/
theorem zeroOn_of_firstV (P : ℕ) (I : ℕ → ℕ → KeccakState) {inst segment lanesPt output : List F}
    (hi : inst.length = P + 5) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (ho : output.length = 25) (committed : F)
    (hopen : OpenTrueV (P + 5) I inst segment lanesPt committed)
    (htrue : ClaimTrueF (statesOfS Shape.v1 P I 0) P
      (firstClaimSF Shape.v1 inst segment lanesPt output committed)) :
    ZeroOnF (startDeltaV (P + 5) I inst output) (segment ++ lanesPt) 6 := by
  rw [zeroOnF_full _ (by simp [hs, hl])]
  rw [ClaimTrueF, firstClaimV_sum P I hi hl] at htrue
  have hdot : dotF ((eqKernelF lanesPt).take 25) output =
      ∑ l ∈ range 25, eqAtF lanesPt l * output.getD l 0 := by
    rw [dotF_eq _ _ (by simp [eqKernelF_length, hl, ho])]
    simp only [List.length_take, eqKernelF_length, hl]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
      ← List.getD_eq_getElem?_getD, eqKernelF_getD, hl, ite_eq_left (by omega)]
  have hseg : (eqKernelF segment).getD (Shape.v1.segments - 1) 0 = eqAtF segment 1 := by
    rw [eqKernelF_getD, hs]; rfl
  change committed + (eqKernelF segment).getD (Shape.v1.segments - 1) 0 *
    dotF ((eqKernelF lanesPt).take 25) output = _ at htrue
  rw [hseg, hdot] at htrue
  rw [OpenTrueV] at hopen
  have hsplit : ∑ w ∈ range (2 ^ 6), eqAtF (segment ++ lanesPt) w *
        startDeltaV (P + 5) I inst output w =
      ∑ m ∈ range 2, eqAtF segment m * ∑ l ∈ range 32, eqAtF lanesPt l *
        startDeltaV (P + 5) I inst output (2 * l + m) := by
    rw [show 2 ^ 6 = 32 * 2 from rfl, sum_range_mulK 32 2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hm' := Finset.mem_range.1 hm
    have e1 : (2 * l + m) / 2 = l := by omega
    rw [eqAtF_append, hs, eqAtF_mod segment, hs, pow_one, e1,
      show (2 * l + m) % 2 = m by omega]
    ring
  have hzero : ∀ m < 2, ∑ x ∈ range 7, eqAtF lanesPt (25 + x) *
      startDeltaV (P + 5) I inst output (2 * (25 + x) + m) = 0 := fun m hm ↦
    Finset.sum_eq_zero fun x _ ↦ by
      rw [startDeltaV, if_neg (by omega), mul_zero]
  have hm0 : ∑ l ∈ range 32, eqAtF lanesPt l * startDeltaV (P + 5) I inst output (2 * l + 0) =
      ∑ l ∈ range 25, eqAtF lanesPt l *
        stepMleK (P + 5) inst (fun x ↦ laneWord (segStateS Shape.v1 I 0 12 x) l) +
      ∑ l ∈ range 25, eqAtF lanesPt l * stepMleK (P + 5) inst (fun x ↦ laneWord (I 1 x) l) := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 0 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDeltaV, show (2 * l + 0) / 2 = l by omega, show (2 * l + 0) % 2 = 0 by omega,
      if_pos hl'', if_neg (by norm_num), mul_add]
  have hm1 : ∑ l ∈ range 32, eqAtF lanesPt l * startDeltaV (P + 5) I inst output (2 * l + 1) =
      ∑ l ∈ range 25, eqAtF lanesPt l *
        stepMleK (P + 5) inst (fun x ↦ laneWord (segStateS Shape.v1 I 1 12 x) l) +
      ∑ l ∈ range 25, eqAtF lanesPt l * output.getD l 0 := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 1 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDeltaV, show (2 * l + 1) / 2 = l by omega, show (2 * l + 1) % 2 = 1 by omega,
      if_pos hl'', if_pos rfl, mul_add]
  rw [hsplit, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
    Finset.sum_range_zero, zero_add, hm0, hm1]
  rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0), Finset.sum_range_zero,
    zero_add] at htrue
  linear_combination (-1 : F) * htrue + (-1 : F) * hopen +
    (CharTwo.two_eq_zero (R := F)) * (eqAtF segment 1 *
      ∑ l ∈ range 25, eqAtF lanesPt l * output.getD l 0 + committed)

end Start

/-! ## The committed outputs' opening (`LvmKeccakOpenOut`) -/

section OpenOut

variable {F : Type} [Field F] [Algebra K F] [CharP F 2] (h : ℕ)

/-- The slot weights at slice `0`, extended over the slot bits (`Wo`). -/
def WoF (segment lanesPt pt : List F) : F :=
  ∑ o ∈ range (2 ^ 6), eqAtF pt o * slotWtF (eqKernelF segment) (firstWeightsF lanesPt) 1 1 o 0

/-- The column's slots at the steps' point `inst`, extended over the slot bits (`Qo`). -/
def QoF (col : ℕ → K) (inst pt : List F) : F :=
  ∑ o ∈ range (2 ^ 6), eqAtF pt o * stepMleK h inst (fun x ↦ col (x + 2 ^ h * o))

/-- The committed opening's sumcheck family (`Fo`). -/
def FoF (col : ℕ → K) (inst segment lanesPt : List F) (acc : List F) : F :=
  cubeSumF (fun pt ↦ WoF segment lanesPt pt * QoF h col inst pt) 6 acc

omit [CharP F 2] in
theorem FoF_plain {β : Type} (qk : β → ℕ → K) (inst segment lanesPt : List F) :
    PlainFamilyF (fun q acc ↦ FoF h (qk q) inst segment lanesPt acc) 2 6 :=
  cube_plainFamilyF (fun q pt ↦ WoF segment lanesPt pt * QoF h (qk q) inst pt) 6
    fun _ pre post ↦ polyLEF_mle_mul _ _ _ _ pre post

omit [CharP F 2] in
theorem nF_one : (nF 1 : F) = 1 := by
  show algebraMap K F (K.ofBits 1) = 1
  rw [show K.ofBits 1 = 1 from rfl, map_one]

omit [CharP F 2] in
theorem slotWtF_out {segment lanesPt : List F} (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (o : ℕ) : slotWtF (eqKernelF segment) (firstWeightsF lanesPt) 1 1 o 0 =
      if 25 ≤ o ∧ o < 50 then eqAtF segment 0 * eqAtF lanesPt (o - 25) else 0 := by
  rw [slotWtF]
  by_cases ho : 25 ≤ o ∧ o < 50
  · rw [ite_eq_left (show 25 * 1 ≤ o ∧ o < 25 * (1 + 1) ∧ 0 < 64 by omega), ite_eq_left ho]
    have e1 : o / 25 - 1 = 0 := by omega
    have e2 : 64 * (o % 25) + 0 < 1600 := by omega
    rw [e1, eqKernelF_getD, hs, ite_eq_left (by norm_num), firstWeightsF,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa [keccakBits] using e2)]
    simp only [Option.map_some, Option.getD_some]
    have e3 : (64 * (o % 25) + 0) / 64 = o - 25 := by omega
    have e4 : (64 * (o % 25) + 0) % 64 = 0 := by omega
    rw [e3, e4, eqKernelF_getD, hl, ite_eq_left (by omega), pow_zero, nF_one, mul_one]
  · rw [ite_eq_right (show ¬ (25 * 1 ≤ o ∧ o < 25 * (1 + 1) ∧ 0 < 64) by omega), ite_eq_right ho]

/-- Before the slot challenges, the family is the middle-state value `OpenTrueV` speaks of
(`Fo_nil`). -/
theorem FoF_nil (col : ℕ → K) (inst : List F) {segment lanesPt : List F}
    (hs : segment.length = 1) (hl : lanesPt.length = 5) :
    FoF h col inst segment lanesPt [] =
      eqAtF segment 0 * ∑ l ∈ range 25, eqAtF lanesPt l *
        stepMleK h inst (fun x ↦ col (x + 2 ^ h * (25 + l))) := by
  rw [FoF, cubeSumF_nil]
  have hu : ∀ u ∈ range (2 ^ 6), WoF segment lanesPt (bitsF u 6) * QoF h col inst (bitsF u 6) =
      slotWtF (eqKernelF segment) (firstWeightsF lanesPt) 1 1 u 0 *
        stepMleK h inst (fun x ↦ col (x + 2 ^ h * u)) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [WoF, QoF, sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu']
  rw [Finset.sum_congr rfl hu, show 2 ^ 6 = 25 + (25 + 14) from rfl, Finset.sum_range_add,
    Finset.sum_range_add, Finset.mul_sum]
  have h1 : ∑ u ∈ range 25, slotWtF (eqKernelF segment) (firstWeightsF lanesPt) 1 1 u 0 *
      stepMleK h inst (fun x ↦ col (x + 2 ^ h * u)) = 0 :=
    Finset.sum_eq_zero fun u hu ↦ by
      rw [slotWtF_out hs hl, ite_eq_right (by have := Finset.mem_range.1 hu; omega), zero_mul]
  have h3 : ∑ u ∈ range 14, slotWtF (eqKernelF segment) (firstWeightsF lanesPt) 1 1 (25 + (25 + u)) 0 *
      stepMleK h inst (fun x ↦ col (x + 2 ^ h * (25 + (25 + u)))) = 0 :=
    Finset.sum_eq_zero fun u _ ↦ by rw [slotWtF_out hs hl, ite_eq_right (by omega), zero_mul]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [slotWtF_out hs hl, ite_eq_left (by omega), show 25 + l - 25 = l by omega]
  ring

omit [Algebra K F] [CharP F 2] in
theorem headD_eq_getDF (r : List F) : r.headD 0 = r.getD 0 0 := by
  cases r <;> rfl

omit [CharP F 2] in
/-- **The verifier's slot weight** at slice `0` after the fold is `W̃(ρ)` (`fold_out`). -/
theorem fold_outF {P : ℕ} {inst segment lanesPt output : List F} (hi : inst.length = P + 5)
    (committed : F) {slot : List F} (hslot : slot.length = 6) :
    ((foldAllF slot (slotWeightsF (P + 5)
      (firstClaimSF Shape.v1 inst segment lanesPt output committed) 1 1)).headD []).headD 0 =
      WoF segment lanesPt slot := by
  have hrows := slotWeightsF_length (P + 5)
    (firstClaimSF Shape.v1 inst segment lanesPt output committed) 1 1 (by norm_num)
  obtain ⟨-, -, h3⟩ := foldAllF_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeightsF_row_length _ _ 1 1 (by norm_num) (by omega)
  rw [headD_eq_getDF, h3 0 (by norm_num), WoF, hslot]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeightsF_getD _ _ 1 1 (by norm_num) (Finset.mem_range.1 ho)]
  have hp : (firstClaimSF Shape.v1 inst segment lanesPt output committed).point.drop (P + 5 - 5) =
      segment := by
    show (inst.drop 5 ++ segment).drop (P + 5 - 5) = segment
    rw [show P + 5 - 5 = P by omega, List.drop_left' (by simp [hi])]
  have hw : (firstClaimSF Shape.v1 inst segment lanesPt output committed).weights =
      firstWeightsF lanesPt := by simp only [firstClaimSF]
  rw [hp, hw]

omit [CharP F 2] in
/-- **The outputs' check** (`final_out`): a true word claim and the check give the slot rounds'
last claim. -/
theorem final_outF (P : ℕ) (col : ℕ → K) {inst segment lanesPt output : List F}
    (hi : inst.length = P + 5) (committed : F) {slot : List F} (hslot : slot.length = 6)
    (word value : F)
    (hv : word = stepMleK (P + 5 + 6) (inst.take 5 ++ inst.drop 5 ++ slot) col)
    (hc : ((foldAllF slot (slotWeightsF (P + 5)
      (firstClaimSF Shape.v1 inst segment lanesPt output committed) 1 1)).headD []).headD 0 * word =
        value) :
    value = FoF (P + 5) col inst segment lanesPt slot := by
  rw [← hc, fold_outF hi committed hslot, FoF, cubeSumF_full _ hslot]
  refine congrArg (HMul.hMul _) ?_
  rw [hv, stepMleK, List.take_append_drop, ← hslot, col_splitF hi, QoF, hslot]
  rfl

end OpenOut

/-! ## The inputs' opening (`LvmKeccakOpenIn`, `LvmKeccakGkrTail`) -/

section OpenIn

variable {F : Type} [Field F] [Algebra K F] [CharP F 2] (P : ℕ)

/-- The v1 states at depth `12`: the committed inputs' bits (`statesAt_12`). -/
theorem statesV_12 (col : ℕ → K) (m x : ℕ) {j : ℕ} (hj : j < 1600) :
    statesOfS Shape.v1 P (inState (P + 5) col) 12 m x j =
      (col (x + 2 ^ (P + 5) * (25 * m + j / 64))).toBitVec.getLsbD (j % 64) := by
  show sbit (inState (P + 5) col m x) j = _
  rw [sbit, lane_inState _ _ _ _ (by omega)]
  rfl

/-- The claim at depth `12` restricted to instance `i` (`PhiI`). -/
def PhiIF (col : ℕ → K) (claim : KClaim F) (i : ℕ) : F :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAtF claim.point z *
    ∑ j ∈ range 1600, claim.weights.getD j 0 *
      bitF (stAt (statesOfS Shape.v1 P (inState (P + 5) col) 12) P z i j)

/-- The instance weights, extended over the five instance bits (`MuT`). -/
def MuTF (mu pt : List F) : F := ∑ i ∈ range (2 ^ 5), eqAtF pt i * mu.getD i 0

/-- `Φ`, extended over the five instance bits (`PhiT`). -/
def PhiTF (col : ℕ → K) (claim : KClaim F) (pt : List F) : F :=
  ∑ i ∈ range (2 ^ 5), eqAtF pt i * PhiIF P col claim i

/-- The instance rounds' family (`Fl`). -/
def FlF (col : ℕ → K) (claim : KClaim F) (acc : List F) : F :=
  cubeSumF (fun pt ↦ MuTF claim.mu pt * PhiTF P col claim pt) 5 acc

omit [Algebra K F] [CharP F 2] in
theorem FlF_plain {β : Type} (qk : β → ℕ → K) (claim : KClaim F) :
    PlainFamilyF (fun q acc ↦ FlF P (qk q) claim acc) 2 5 :=
  cube_plainFamilyF (fun q pt ↦ MuTF claim.mu pt * PhiTF P (qk q) claim pt) 5
    fun _ pre post ↦ polyLEF_mle_mul _ _ _ _ pre post

omit [Algebra K F] in
theorem FlF_nil (col : ℕ → K) (claim : KClaim F) :
    FlF P col claim [] =
      claimSumF (statesOfS Shape.v1 P (inState (P + 5) col) 12) P claim.point claim.mu
        claim.weights := by
  rw [FlF, cubeSumF_nil]
  have hu : ∀ u ∈ range (2 ^ 5), MuTF claim.mu (bitsF u 5) * PhiTF P col claim (bitsF u 5) =
      claim.mu.getD u 0 * PhiIF P col claim u := by
    intro u hu
    rw [MuTF, PhiTF, sum_eqAtF_bitsF (Finset.mem_range.1 hu),
      sum_eqAtF_bitsF (Finset.mem_range.1 hu)]
  rw [Finset.sum_congr rfl hu, claimSumF]
  simp only [PhiIF, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ by ring

/-- Slice `z` of slot `o` at the steps' point `a` (`sliceMle`). -/
def sliceMleF (col : ℕ → K) (a : List F) (o z : ℕ) : F :=
  ∑ x ∈ range (2 ^ (P + 5)), eqAtF a x * bitF ((col (x + 2 ^ (P + 5) * o)).toBitVec.getLsbD z)

/-- The slot weights of the claim at depth `12`, slice `z`, extended over the slot bits (`Ws`). -/
def WsF (claim : KClaim F) (z : ℕ) (pt : List F) : F :=
  ∑ o ∈ range (2 ^ 6), eqAtF pt o * slotWtF (eqKernelF (claim.point.drop P)) claim.weights 0 2 o z

/-- Slice `z` at `(λ, r_pack)`, extended over the slot bits (`Qs`). -/
def QsF (col : ℕ → K) (a : List F) (z : ℕ) (pt : List F) : F :=
  ∑ o ∈ range (2 ^ 6), eqAtF pt o * sliceMleF P col a o z

/-- The slot rounds' family, at the instance point `low` (`Fs`). -/
def FsF (col : ℕ → K) (claim : KClaim F) (low : List F) (acc : List F) : F :=
  cubeSumF (fun pt ↦ MuTF claim.mu low * ∑ z ∈ range 64,
    WsF P claim z pt * QsF P col (low ++ claim.point.take P) z pt) 6 acc

omit [Algebra K F] [CharP F 2] in
theorem FsF_plain {β : Type} (qk : β → ℕ → K) (claim : KClaim F) (low : List F) :
    PlainFamilyF (fun q acc ↦ FsF P (qk q) claim low acc) 2 6 :=
  cube_plainFamilyF (fun q pt ↦ MuTF claim.mu low * ∑ z ∈ range 64,
      WsF P claim z pt * QsF P (qk q) (low ++ claim.point.take P) z pt) 6
    fun _ pre post ↦ PolyLEF.const_mul (PolyLEF.sum _ fun _ _ ↦
      polyLEF_mle_mul _ _ _ _ pre post) _

/-- The claim at depth `12` on segment `m` and step `x` (`Gin`). -/
def GinF (col : ℕ → K) (claim : KClaim F) (m x : ℕ) : F :=
  ∑ j ∈ range 1600, claim.weights.getD j 0 *
    bitF ((col (x + 2 ^ (P + 5) * (25 * m + j / 64))).toBitVec.getLsbD (j % 64))

omit [Algebra K F] [CharP F 2] in
theorem GinF_eq (col : ℕ → K) (claim : KClaim F) (m x : ℕ) :
    GinF P col claim m x = ∑ l ∈ range 25, ∑ z ∈ range 64, claim.weights.getD (64 * l + z) 0 *
      bitF ((col (x + 2 ^ (P + 5) * (25 * m + l))).toBitVec.getLsbD z) := by
  rw [GinF, show 1600 = 25 * 64 from rfl, sum_range_mulK 25 64]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]

omit [Algebra K F] [CharP F 2] in
/-- **The claim's positions are the slots' slices** (`phi_eq`). -/
theorem phi_eqF (col : ℕ → K) (claim : KClaim F) (hshape : ClaimShapeF P claim) {low : List F}
    (hlow : low.length = 5) :
    PhiTF P col claim low = ∑ o ∈ range (2 ^ 6), ∑ z ∈ range 64,
      slotWtF (eqKernelF (claim.point.drop P)) claim.weights 0 2 o z *
        sliceMleF P col (low ++ claim.point.take P) o z := by
  have hb : (claim.point.take P).length = P := by simp [hshape.2.1]
  have hsd : (claim.point.drop P).length = 1 := by simp [hshape.2.1]
  have hX : ∀ z i, ∑ j ∈ range 1600, claim.weights.getD j 0 *
      bitF (stAt (statesOfS Shape.v1 P (inState (P + 5) col) 12) P z i j) =
        GinF P col claim (z / 2 ^ P) (i + 32 * (z % 2 ^ P)) := fun z i ↦
    Finset.sum_congr rfl fun j hj ↦ by
      rw [stAt, statesV_12 P col _ _ (Finset.mem_range.1 hj)]
  have hphi : PhiTF P col claim low = ∑ z ∈ range (2 ^ (P + 1)),
      eqAtF (claim.point.take P ++ claim.point.drop P) z *
        ∑ i ∈ range 32, eqAtF low i * GinF P col claim (z / 2 ^ P) (i + 32 * (z % 2 ^ P)) := by
    rw [List.take_append_drop, PhiTF]
    simp only [PhiIF, hX]
    rw [show (2 : ℕ) ^ 5 = 32 from rfl]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hphi, sum_splitF hlow hb (GinF P col claim)]
  rw [show 2 ^ 6 = 2 * 25 + 14 from rfl, Finset.sum_range_add, sum_range_mulK 2 25]
  have hzero : ∑ x ∈ range 14, ∑ z ∈ range 64,
      slotWtF (eqKernelF (claim.point.drop P)) claim.weights 0 2 (2 * 25 + x) z *
        sliceMleF P col (low ++ claim.point.take P) (2 * 25 + x) z = 0 :=
    Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [slotWtF, ite_eq_right (by omega), zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  simp only [GinF_eq, sliceMleF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hl' := Finset.mem_range.1 hl
  have hz' := Finset.mem_range.1 hz
  rw [slotWtF, ite_eq_left (show 25 * 0 ≤ 25 * m + l ∧ 25 * m + l < 25 * (0 + 2) ∧ z < 64 by
    omega)]
  have e3 : (25 * m + l) / 25 - 0 = m := by omega
  have e4 : (25 * m + l) % 25 = l := by omega
  rw [e3, e4, eqKernelF_getD, hsd, ite_eq_left (by omega)]
  ring

omit [Algebra K F] in
theorem FsF_nil (col : ℕ → K) (claim : KClaim F) (hshape : ClaimShapeF P claim) {low : List F}
    (hlow : low.length = 5) :
    FsF P col claim low [] = MuTF claim.mu low * PhiTF P col claim low := by
  rw [FsF, cubeSumF_nil, ← Finset.mul_sum, phi_eqF P col claim hshape hlow]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun u hu ↦ Finset.sum_congr rfl fun z _ ↦ ?_)
  rw [WsF, QsF, sum_eqAtF_bitsF (Finset.mem_range.1 hu), sum_eqAtF_bitsF (Finset.mem_range.1 hu)]

omit [Algebra K F] [CharP F 2] in
/-- **The verifier's slot weights** after the fold are `W̃_z(ρ)` (`fold_in`). -/
theorem fold_inF (claim : KClaim F) {slot : List F} (hslot : slot.length = 6) {z : ℕ}
    (hz : z < 64) :
    ((foldAllF slot (slotWeightsF (P + 5) claim 0 2)).headD []).getD z 0 =
      WsF P claim z slot := by
  have hrows := slotWeightsF_length (P + 5) claim 0 2 (by norm_num)
  obtain ⟨-, -, h3⟩ := foldAllF_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeightsF_row_length _ _ 0 2 (by norm_num) (by omega)
  rw [h3 z hz, WsF, hslot]
  refine Finset.sum_congr rfl fun o ho ↦ ?_
  rw [slotWeightsF_getD _ _ 0 2 (by norm_num) (Finset.mem_range.1 ho),
    show P + 5 - 5 = P by omega]

omit [Algebra K F] [CharP F 2] in
theorem fold_in_lengthF (claim : KClaim F) {slot : List F} (hslot : slot.length = 6) :
    ((foldAllF slot (slotWeightsF (P + 5) claim 0 2)).headD []).length = 64 := by
  have hrows := slotWeightsF_length (P + 5) claim 0 2 (by norm_num)
  exact (foldAllF_eq slot _ (by rw [hrows, hslot]; rfl) fun o ho ↦
    slotWeightsF_row_length _ _ 0 2 (by norm_num) (by omega)).2.1

omit [Algebra K F] [CharP F 2] in
/-- The slices at `(λ, r_pack, ρ)` are `S̃_z(ρ)` (`slices_eq`). -/
theorem slices_eqF (col : ℕ → K) {a slot : List F} (ha : a.length = P + 5) (hslot : slot.length = 6)
    (z : ℕ) :
    ∑ n ∈ range (2 ^ (P + 5 + 6)), eqAtF (a ++ slot) n * bitF ((col n).toBitVec.getLsbD z) =
      QsF P col a z slot := by
  rw [← hslot, col_splitF ha, QsF, hslot]
  rfl

/-- The `64` bit-slice claims at a point (`slicesTrue`). -/
def slicesTrueK (col : ℕ → K) (point slices : List F) : Prop :=
  point.length = P + 5 + 6 ∧ slices.length = 64 ∧ ∀ i < 64,
    slices.getD i 0 = ∑ n ∈ range (2 ^ (P + 5 + 6)), eqAtF point n * bitF ((col n).toBitVec.getLsbD i)

omit [Algebra K F] [CharP F 2] in
theorem multilinearEvalF_mu {mu low : List F} (hmu : mu.length = 32) (hlow : low.length = 5) :
    multilinearEvalF mu low = MuTF mu low := by
  rw [multilinearEvalF_eq low mu (by rw [hmu, hlow]; rfl), MuTF, hlow]

omit [Algebra K F] [CharP F 2] in
/-- **The final check** (`final_in`): with true slices, the check gives the slot rounds' last
claim. -/
theorem final_inF (col : ℕ → K) (claim : KClaim F) (hshape : ClaimShapeF P claim)
    {low slot slices : List F} (hlow : low.length = 5) (hslot : slot.length = 6) (value : F)
    (hs : slicesTrueK P col (low ++ claim.point.take P ++ slot) slices)
    (hc : multilinearEvalF claim.mu low *
      dotF ((foldAllF slot (slotWeightsF (P + 5) claim 0 2)).headD []) slices =
        value) :
    value = FsF P col claim low slot := by
  have ha : (low ++ claim.point.take P).length = P + 5 := by
    simp [hlow, hshape.2.1]; omega
  rw [← hc, FsF, cubeSumF_full _ hslot, multilinearEvalF_mu hshape.1 hlow,
    dotF_eq _ _ (by rw [fold_in_lengthF P claim hslot, hs.2.1]), fold_in_lengthF P claim hslot]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun z hz ↦ ?_)
  have hz' := Finset.mem_range.1 hz
  rw [fold_inF P claim hslot hz', hs.2.2 z hz', ← slices_eqF P col ha hslot z]

end OpenIn

/-! ## The caller's zero test (`LvmKeccakCaller.callDelta`) -/

section Caller

variable {F : Type} [Field F] [Algebra K F] [CharP F 2] (h nt : ℕ) (col : ℕ → K) (Y : ℕ → ℕ → K)

/-- The middle state's mismatch (`midDelta`). -/
def midDeltaF (l x : ℕ) : F :=
  kF (laneWord (roundsFrom 0 12 (inState h col 0 x)) l) + kF (col (x + 2 ^ h * (25 + l)))

/-- The zero-test table of the `r` coordinates (`callDelta`): table `t < 25` the middle-state
mismatch, table `25 + l` (`l < nt`) the tied lane's mismatch, index `x + 2^h·t`. -/
def callDeltaF (w : ℕ) : F :=
  if w / 2 ^ h < 25 then midDeltaF h col (w / 2 ^ h) (w % 2 ^ h)
  else if w / 2 ^ h < 25 + nt then
    kF (Y (w / 2 ^ h - 25) (w % 2 ^ h)) +
      kF (laneWord (roundsFrom 12 12 (inState h col 1 (w % 2 ^ h))) (w / 2 ^ h - 25))
  else 0

/-- **A vanishing table** is a valid region with true tied lanes (`valid_of_callDelta_zero`). -/
theorem valid_of_callDeltaF_zero (hnt : nt ≤ 25)
    (hz : ZeroOnF (callDeltaF (F := F) h nt col Y) [] (h + 6)) :
    RegionValid h col ∧ Lvm.KG.OutRel h nt col Y := by
  rw [zeroOnF_nil] at hz
  have hp := Nat.two_pow_pos h
  have at_ : ∀ x < 2 ^ h, ∀ t < 64, callDeltaF (F := F) h nt col Y (x + 2 ^ h * t) = 0 :=
    fun x hx t ht ↦ hz _ (by rw [pow_add]; nlinarith)
  have hmid : ∀ x < 2 ^ h, ∀ t < 25,
      laneWord (roundsFrom 0 12 (inState h col 0 x)) t = col (x + 2 ^ h * (25 + t)) := by
    intro x hx t ht
    have := at_ x hx t (by omega)
    simp only [callDeltaF, Lvm.KG.idx_div h hx, Lvm.KG.idx_mod h hx, ht, ite_true,
      midDeltaF] at this
    exact (algebraMap K F).injective (addF_eq_zero_iff.1 this)
  have hv : RegionValid h col := by
    intro x hx
    refine Vector.ext fun l hl ↦ ?_
    rw [← LeanVM.Protocol.KeccakGkr.lane_eq _ hl, ← LeanVM.Protocol.KeccakGkr.lane_eq _ hl,
      lane_inState h col 1 x hl, Nat.mul_one, ← hmid x hx l hl, laneWord, Lvm.KG.lane_ofLane']
  refine ⟨hv, fun l hl x hx ↦ ?_⟩
  have := at_ x hx (25 + l) (by omega)
  simp only [callDeltaF, Lvm.KG.idx_div h hx, Lvm.KG.idx_mod h hx,
    show ¬ 25 + l < 25 by omega, ite_false, show 25 + l < 25 + nt by omega, ite_true,
    Nat.add_sub_cancel_left] at this
  rw [(algebraMap K F).injective (addF_eq_zero_iff.1 this), keccakF_eq, hv x hx]

/-- **The table's extension vanishes at `r`** when the GKR's starting claims and the tied lanes'
claims hold there (`callDelta_zeroOn`). -/
theorem callDeltaF_zeroOn {r v : List F} (hr : r.length = h) (hnt : nt ≤ 25)
    (hout : outClaimsTrueMidV h (inState h col) r v) (hmid : midAgreeV h (inState h col) r)
    (htied : ∀ l < nt, stepMleK h r (Y l) = v.getD l 0) :
    ZeroOnF (callDeltaF h nt col Y) r (h + 6) := by
  intro t ht
  rw [hr, show h + 6 - h = 6 by omega] at ht
  unfold foldTF
  rw [hr]
  have e : ∀ w ∈ range (2 ^ h), callDeltaF (F := F) h nt col Y (w + 2 ^ h * t) =
      if t < 25 then midDeltaF h col t w
      else if t < 25 + nt then
        kF (Y (t - 25) w) + kF (laneWord (roundsFrom 12 12 (inState h col 1 w)) (t - 25))
      else 0 := by
    intro w hw
    have hw' := Finset.mem_range.1 hw
    rw [callDeltaF, Lvm.KG.idx_div h hw', Lvm.KG.idx_mod h hw']
  rw [Finset.sum_congr rfl fun w hw ↦ by rw [e w hw]]
  split_ifs with h1 h2
  · have hm : stepMleK h r (fun x ↦ laneWord (roundsFrom 0 12 (inState h col 0 x)) t) =
        stepMleK h r (fun x ↦ col (x + 2 ^ h * (25 + t))) := by
      have := hmid t h1
      have ef : (fun x ↦ col (x + 2 ^ h * (25 + t))) = fun x ↦ laneWord (inState h col 1 x) t :=
        funext fun x ↦ by rw [LeanVM.Protocol.KeccakGkr.laneWord_inState h col 1 x h1, mul_one]
      rw [ef]
      exact this
    simp only [stepMleK] at hm
    simp only [midDeltaF, mul_add, Finset.sum_add_distrib, hm]
    exact CharTwo.add_self_eq_zero _
  · have h3 := htied (t - 25) (by omega)
    have h4 : stepMleK h r (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) (t - 25)) =
        v.getD (t - 25) 0 := hout (t - 25) (by omega)
    simp only [stepMleK] at h3 h4
    simp only [mul_add, Finset.sum_add_distrib, h3, h4]
    exact CharTwo.add_self_eq_zero _
  · simp

end Caller

/-! ## The phase at `E2` in the doom calculus -/

section Specs

open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (errE)
open Lvm.ASM (εS)
open scoped ENNReal

/-- A word claim on the `KS` column holds (`colTrueE2`, with `stepMleK`). -/
def colTrueK (h : ℕ) (col : ℕ → K) (c : ColClaimE2) : Prop :=
  c.column = qkeccak ∧ c.point.length = h + 6 ∧ c.value = stepMleK (h + 6) c.point col

theorem sum_mid_inState {F : Type} [Field F] [Algebra K F] (h : ℕ) (col : ℕ → K) (inst lanesPt : List F) :
    ∑ l ∈ range 25, eqAtF lanesPt l * stepMleK h inst (fun x ↦ col (x + 2 ^ h * (25 + l))) =
      ∑ l ∈ range 25, eqAtF lanesPt l * stepMleK h inst (fun x ↦ laneWord (inState h col 1 x) l) :=
  Finset.sum_congr rfl fun l hl ↦ by
    have ef : (fun x ↦ col (x + 2 ^ h * (25 + l))) = fun x ↦ laneWord (inState h col 1 x) l :=
      funext fun x ↦ by
        rw [LeanVM.Protocol.KeccakGkr.laneWord_inState h col 1 x (Finset.mem_range.1 hl), mul_one]
    rw [ef]

theorem slicesTrueK_of_E2 (P : ℕ) (col : ℕ → K) {z sv : List E2} (hz : z.length = P + 5 + 6)
    (hs : SlicesTrueE2 col z sv) : slicesTrueK P col z sv :=
  ⟨hz, hs.1, fun i hi ↦ by
    rw [hs.2 i hi, hz]
    exact Finset.sum_congr rfl fun n _ ↦ by unfold bitF; split_ifs <;> simp⟩

theorem firstClaimSV_shape {P : ℕ} {inst segment lanesPt output : List E2} (committed : E2)
    (hi : inst.length = P + 5) (hs : segment.length = 0 + 1) :
    ClaimShapeF P (firstClaimSF Shape.v1 inst segment lanesPt output committed) := by
  simp only [ClaimShapeF, firstClaimSF]
  refine ⟨?_, ?_, ?_⟩
  · rw [eqKernelF_length, List.length_take, hi, min_eq_left (by omega)]; rfl
  · rw [List.length_append, List.length_drop, hi, hs]; omega
  · rw [firstWeightsF, List.length_map, List.length_range]; rfl

theorem errG_c2' : errG gC2 2 + 0 ≤ εS := by
  have := errG_c2
  rwa [Nat.cast_one, one_mul] at this

/-- `verifyKeccakE2` at `P + 5` with v1's constants and `open` inlined. -/
def vkFlat (P : ℕ) (inst output : List E2) : VerifierProgram (List ColClaimE2 × List E2 × List E2) :=
  e2Samples gC1 (0 + 1) >>= fun segment ↦
  e2Samples gC1 (4 + 1) >>= fun lanePoint ↦
  e2Read >>= fun committed ↦
  keccakLayersE2 Shape.v1 (P + 5) (List.range' 0 (11 + 1))
      (firstClaimSF Shape.v1 inst segment lanePoint output committed) >>= fun claim ↦
  ((sumcheckE2 gC2 committed 3 (List.replicate 6 none) >>= fun sv ↦
      pure (sv.1, foldRowsF sv.1
        (slotWeightsF (P + 5) (firstClaimSF Shape.v1 inst segment lanePoint output committed) 1 1),
        sv.2)) >>= fun o ↦
    e2Read >>= fun word ↦
    VerifierProgram.require (o.2.1.headD 0 * word = o.2.2) >>= fun _ ↦
    pure [(⟨qkeccak, inst.take 5 ++ inst.drop 5 ++ o.1, word⟩ : ColClaimE2)]) >>= fun outputs ↦
  sumcheckE2 gC2 claim.value 3 (List.replicate 5 none) >>= fun lv ↦
  (sumcheckE2 gC2 lv.2 3 (List.replicate 6 none) >>= fun sv ↦
    pure (sv.1, foldRowsF sv.1 (slotWeightsF (P + 5) claim 0 2), sv.2)) >>= fun o ↦
  e2Reads (63 + 1) >>= fun slices ↦
  VerifierProgram.require (multilinearEvalF claim.mu lv.1 * dotF o.2.1 slices = o.2.2) >>= fun _ ↦
  pure (outputs, lv.1 ++ claim.point.take (P + 5 - 5) ++ o.1, slices)

theorem verifyKeccakE2_flat (P : ℕ) (inst output : List E2) :
    verifyKeccakE2 (P + 5) inst output = vkFlat P inst output := by
  have h1 : keccakSegmentBits = 0 + 1 := by decide
  have h2 : keccakLaneBits = 4 + 1 := rfl
  have h3 : qkeccakSlotBits = 6 := by decide
  have h4 : keccakSegments = 2 := by decide
  have h5 : List.range keccakDepth = List.range' 0 (11 + 1) := by
    rw [List.range_eq_range']; rfl
  have h6 : kBits = 63 + 1 := rfl
  simp only [verifyKeccakE2, keccakOpenE2, vkFlat, h1, h2, h3, h4, h5, h6]
  rfl

variable {β : Type} {C : List Ev → Set β} [Finite β]

/-- The postcondition of the reduction: the word claims and the slice claims, with the lengths. -/
abbrev KPostK (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (res : List ColClaimE2 × List E2 × List E2)
    (hist : List Ev) : Prop :=
  res.2.1.length = P + 5 + 6 ∧ res.2.2.length = 64 ∧
    Doomed C (fun q ↦ (∀ c ∈ res.1, colTrueK (P + 5) (qk q) c) ∧
      slicesTrueK P (qk q) res.2.1 res.2.2 ∧ R q) hist

open Classical in
/-- **The inputs' opening** at `E2` (`inputSpec`): four instance rounds, six slot rounds (`c = 2`),
the 64 slices and the check. Lead `0`; the follower's `T` after the slices. -/
noncomputable def inputSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim)
    (outs : List ColClaimE2) {T : ℝ≥0∞} (hT : T ≤ εS) :
    Spec (sumcheckE2 gC2 claim.value 3 (List.replicate 5 none) >>= fun lv ↦
      (sumcheckE2 gC2 lv.2 3 (List.replicate 6 none) >>= fun sv ↦
        pure (sv.1, foldRowsF sv.1 (slotWeightsF (P + 5) claim 0 2), sv.2)) >>= fun o ↦
      e2Reads (63 + 1) >>= fun slices ↦
      VerifierProgram.require (multilinearEvalF claim.mu lv.1 * dotF o.2.1 slices = o.2.2) >>= fun _ ↦
      pure (outs, lv.1 ++ claim.point.take (P + 5 - 5) ++ o.1, slices))
      (Doomed C (fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 12) P claim ∧ R q))
      (fun res h ↦ res.1 = outs ∧ res.2.1.length = P + 5 + 6 ∧ res.2.2.length = 64 ∧
        Doomed C (fun q ↦ slicesTrueK P (qk q) res.2.1 res.2.2 ∧ R q) h) εS 0 T :=
  ((sumcheckGSpec (T := 0) hst hcard R (FlF_plain P qk claim) (count := 3) (by norm_num)
      (by norm_num) (g := gC2) (by norm_num) errG_c2 5 [] claim.value (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by rw [ClaimTrueF, ← FlF_nil]; exact hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun lv ↦
  if hy : lv.1.length = 5 then
    (((sumcheckGSpec (T := 0) hst hcard R (FsF_plain P qk claim lv.1) (count := 3)
        (by norm_num) (by norm_num) (g := gC2) (by norm_num) errG_c2 6 [] lv.2 (by simp)).mono
        (fun _ (hd : lv.1.length = 5 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦ ⟨by
          rw [List.nil_append, FlF, cubeSumF_full _ hy, hv, FsF_nil P (qk q) claim hshape hy], hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
      (Spec.ret (Post := fun (x' : List E2 × List E2 × E2) h ↦ x'.1.length = 6 ∧
          x'.2.1 = foldRowsF x'.1 (slotWeightsF (P + 5) claim 0 2) ∧
          Doomed C (fun q ↦ x'.2.2 = FsF P (qk q) claim lv.1 x'.1 ∧ R q) h)
        (x.1, foldRowsF x.1 (slotWeightsF (P + 5) claim 0 2), x.2)).mono
        (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
        le_rfl).bind' fun x ↦
    if hx : x.1.length = 6 ∧
        x.2.1 = foldRowsF x.1 (slotWeightsF (P + 5) claim 0 2) then
      ((e2ReadsSpec (T := T) hst _ hT 63).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl
        le_rfl le_rfl).bind' fun slices ↦
      (Spec.require
        (Pre := fun h ↦ slices.length = 63 + 1 ∧
          Doomed C (fun q ↦ x.2.2 = FsF P (qk q) claim lv.1 x.1 ∧ R q) h)
        (Post := fun _ h ↦ slices.length = 63 + 1 ∧ Doomed C (fun q ↦
          slicesTrueK P (qk q) (lv.1 ++ claim.point.take (P + 5 - 5) ++ x.1) slices ∧ R q) h)
        fun _ hd hc ↦ ⟨hd.1, Doomed.mono hd.2 fun q ⟨hs, hR⟩ ↦ ⟨by
          rw [show P + 5 - 5 = P by omega] at hs
          rw [hx.2, foldRowsF_eq] at hc
          exact final_inF P (qk q) claim hshape hy hx.1 _ hs hc, hR⟩⟩).bind' fun _ ↦
      (Spec.ret (outs, lv.1 ++ claim.point.take (P + 5 - 5) ++ x.1, slices)).mono
        (fun _ hd ↦ ⟨rfl, by simp [hy, hx.1, hshape.2.1]; omega, hd.1, hd.2⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

open Classical in
/-- **The committed outputs' opening** at `E2` (`outTailSpec`'s first half): six slot rounds
(`c = 2`), the word and the check. Lead `0`. -/
noncomputable def outOpenSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst segment lanesPt : List E2} (output : List E2)
    (hi : inst.length = P + 5) (hs : segment.length = 0 + 1) (hl : lanesPt.length = 4 + 1)
    (committed : E2) (claim : KClaim E2) :
    Spec ((sumcheckE2 gC2 committed 3 (List.replicate 6 none) >>= fun sv ↦
        pure (sv.1, foldRowsF sv.1
          (slotWeightsF (P + 5) (firstClaimSF Shape.v1 inst segment lanesPt output committed) 1 1),
          sv.2)) >>= fun o ↦
      e2Read >>= fun word ↦
      VerifierProgram.require (o.2.1.headD 0 * word = o.2.2) >>= fun _ ↦
      pure [(⟨qkeccak, inst.take 5 ++ inst.drop 5 ++ o.1, word⟩ : ColClaimE2)])
      (Doomed C (fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 12) P claim ∧
        (OpenTrueV (P + 5) (inState (P + 5) (qk q)) inst segment lanesPt committed ∧ R q)))
      (fun outs h ↦ Doomed C (fun q ↦
        ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 12) P claim ∧
        ((∀ c ∈ outs, colTrueK (P + 5) (qk q) c) ∧ R q)) h) εS 0 0 :=
  let first := firstClaimSF Shape.v1 inst segment lanesPt output committed
  let R' : β → Prop := fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 12) P claim ∧ R q
  (((sumcheckGSpec (T := 0) hst hcard R' (FoF_plain (P + 5) qk inst segment lanesPt) (count := 3)
      (by norm_num) (by norm_num) (g := gC2) (by norm_num) errG_c2 6 [] committed (by simp)).mono
      (fun _ (hd : Doomed C _ _) ↦ Doomed.mono hd fun q ⟨hv, hct, hR⟩ ↦ ⟨hct, by
          rw [OpenTrueV, hv, FoF_nil (P + 5) (qk q) inst hs hl, sum_mid_inState], hR⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
    (Spec.ret (Post := fun (x' : List E2 × List E2 × E2) h ↦ x'.1.length = 6 ∧
        x'.2.1 = foldRowsF x'.1 (slotWeightsF (P + 5) first 1 1) ∧
        Doomed C (fun q ↦ x'.2.2 = FoF (P + 5) (qk q) inst segment lanesPt x'.1 ∧ R' q) h)
      (x.1, foldRowsF x.1 (slotWeightsF (P + 5) first 1 1), x.2)).mono
      (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun x ↦
  if hx : x.1.length = 6 ∧ x.2.1 = foldRowsF x.1 (slotWeightsF (P + 5) first 1 1) then
    ((e2ReadSpec (T := 0) hst _ zero_le).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun word ↦
    (Spec.require
      (Pre := Doomed C (fun q ↦ x.2.2 = FoF (P + 5) (qk q) inst segment lanesPt x.1 ∧ R' q))
      (Post := fun _ h ↦ Doomed C (fun q ↦
        ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 12) P claim ∧
        ((∀ c ∈ [(⟨qkeccak, inst.take 5 ++ inst.drop 5 ++ x.1, word⟩ : ColClaimE2)],
          colTrueK (P + 5) (qk q) c) ∧ R q)) h)
      fun _ hd hcheck ↦ Doomed.mono hd fun q ⟨hct, hcol, hR⟩ ↦ ⟨by
        rw [hx.2, foldRowsF_eq] at hcheck
        exact final_outF P (qk q) hi committed hx.1 word _
          (hcol _ (List.mem_singleton_self _)).2.2 hcheck, hct, hR⟩).bind' fun _ ↦
    Spec.ret (Post := fun outs h ↦ Doomed C (fun q ↦
        ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 12) P claim ∧
        ((∀ c ∈ outs, colTrueK (P + 5) (qk q) c) ∧ R q)) h)
      [(⟨qkeccak, inst.take 5 ++ inst.drop 5 ++ x.1, word⟩ : ColClaimE2)]
  else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- `m + 1` zero-test coordinates after the prefix `pre` (`zeroSpecE2` from a prefix). -/
noncomputable def zeroSpecE2From (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) {g : ℕ}
    (hg : g ≤ 64) (δ : β → ℕ → E2) (R : β → Prop) {n m : ℕ} (pre : List E2)
    (hm : pre.length + (m + 1) ≤ n) {εmax T : ℝ≥0∞}
    (he : ((1 : ℕ) : ℝ≥0∞) * errG g 1 + T ≤ εmax) :
    Spec (e2Samples g (m + 1)) (Doomed C (fun q ↦ ZeroOnF (δ q) pre n ∧ R q))
      (fun pt hist ↦ pt.length = m + 1 ∧
        Doomed C (fun q ↦ ZeroOnF (δ q) (pre ++ pt) n ∧ R q) hist) εmax 0 T :=
  (coordGSpec hst hcard (fun acc q ↦ ZeroAliveF δ R n (pre ++ acc) q) (errG g 1)
      (fun acc q hq ↦ by
        have := zeroAliveG_escape hg δ R n (pre ++ acc) q hq
        simpa only [List.append_assoc] using this) he m []).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨_, hz, hR⟩ ↦ ⟨by simpa using hz, hR⟩)
    (fun pt _ ⟨hl, hd⟩ ↦ ⟨hl, Doomed.mono hd fun _ ⟨hz, hR⟩ ↦
      ⟨by simp only [List.nil_append, List.length_append, hl]; exact hm, by simpa using hz, hR⟩⟩)
    le_rfl le_rfl le_rfl

open Classical in
/-- **The v1 Keccak reduction at `E2`** (`gkrSpec`): the segment and lane coordinates (a zero test of
`startDeltaV`, `c = 1`), `committed`, the twelve layers (`layersSpecE2`), the two openings. From
doom of the output claims and the segments' agreement at `inst` to `KPostK`. Lead `0`; the
follower's `T` after the slices. -/
noncomputable def gkrV1Spec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst output : List E2} (hi : inst.length = P + 5)
    (ho : output.length = 25) {T : ℝ≥0∞} (hT : T ≤ εS) :
    Spec (vkFlat P inst output)
      (Doomed C (fun q ↦ outClaimsTrueMidV (P + 5) (inState (P + 5) (qk q)) inst output ∧
        midAgreeV (P + 5) (inState (P + 5) (qk q)) inst ∧ R q))
      (KPostK (C := C) qk R P) εS 0 T :=
  let δ : β → ℕ → E2 := fun q ↦ startDeltaV (P + 5) (inState (P + 5) (qk q)) inst output
  ((zeroSpecE2From (T := 0) hst hcard (g := gC1) (by norm_num) δ R (n := 6) (m := 0) []
      (by simp) errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ by
      obtain ⟨h1, h2⟩ := claims_of_zeroOnV (P + 5) (inState (P + 5) (qk q)) inst output hz
      exact ⟨h1, h2, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun segment ↦
  if hs : segment.length = 0 + 1 then
    ((zeroSpecE2From (T := 0) hst hcard (g := gC1) (by norm_num) δ R (n := 6) (m := 4) segment
        (by rw [hs]) errG_c1).mono
      (fun _ hd ↦ by simpa using hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun lanesPt ↦
    if hl : lanesPt.length = 4 + 1 then
      ((doomRead (T := 0) hst (fun q ↦ ZeroOnF (δ q) (segment ++ lanesPt) 6 ∧ R q)
          zero_le).mono (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun c ↦
      ((Spec.ret (Post := fun committed h ↦ Doomed C (fun q ↦
            ClaimTrueF (statesOfS Shape.v1 P (inState (P + 5) (qk q)) 0) P
              (firstClaimSF Shape.v1 inst segment lanesPt output committed) ∧
            (OpenTrueV (P + 5) (inState (P + 5) (qk q)) inst segment lanesPt committed ∧ R q)) h)
          (e2OfE c)).mono
        (fun _ hd ↦ Doomed.mono hd fun q ⟨hct, hop, hR⟩ ↦
          ⟨zeroOn_of_firstV P (inState (P + 5) (qk q)) hi hs hl ho _ hop hct, hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun committed ↦
      ((layersSpecE2 (T := 0) Shape.v1_ok hst hcard
          (fun q ↦ OpenTrueV (P + 5) (inState (P + 5) (qk q)) inst segment lanesPt committed ∧ R q)
          (fun q ↦ inState (P + 5) (qk q)) P errG_c2' 11 0 rfl _
          (firstClaimSV_shape committed hi hs)).mono
        (fun _ h' ↦ h') (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun claim ↦
      if hc : ClaimShapeF P claim then
        ((outOpenSpecE2 hst hcard R qk P output hi hs hl committed claim).mono
          (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun outs ↦
        (inputSpecE2 hst hcard (fun q ↦ (∀ c ∈ outs, colTrueK (P + 5) (qk q) c) ∧ R q) qk P claim hc
          outs hT).mono (fun _ h' ↦ h')
          (fun res _ ⟨hr1, hl1, hl2, hd⟩ ↦ ⟨hl1, hl2, Doomed.mono hd fun q ⟨hcol, hsl, hR⟩ ↦
            ⟨hsl, hr1 ▸ hcol, hR⟩⟩) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hl hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- The postcondition of the `KS` caller at `E2`, with `stepMleK` (`CallerClaimsE2`). -/
abbrev CallerPostK (P nt : ℕ) (qk : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop)
    (out : CallerOutE2) (hist : List Ev) : Prop :=
  out.1.length = P + 5 ∧ out.2.1.length = 25 ∧
    Doomed C (fun q ↦ RowColTrue (P + 5 + 6) (qk q) out.2.2.2 ∧
      (∀ c ∈ out.2.2.1.1, colTrueK (P + 5) (qk q) c) ∧
      (∀ l < nt, stepMleK (P + 5) out.1 (Y q l) = out.2.1.getD l 0) ∧ R q) hist

open Classical in
/-- **The `KS` Keccak phase with caller claims at `E2`** (`callerSpec`): `r` (a zero test of
`callDeltaF`, `c = 1`), the 25 scalars, the v1 reduction, the row switch. Lead `0`. -/
noncomputable def callerSpecV (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (P nt : ℕ)
    (hnt : nt ≤ 25) (qk : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop) {T : ℝ≥0∞}
    (hrT : (∑ _i ∈ range 7, ((1 : ℕ) : ℝ≥0∞) * errE 1) + T ≤ εS) :
    Spec (callerProgE2 (P + 5))
      (Doomed C (fun q ↦ RegionValid (P + 5) (qk q) ∧ Lvm.KG.OutRel (P + 5) nt (qk q) (Y q) ∧ R q))
      (CallerPostK (C := C) P nt qk Y R) εS 0 T :=
  ((zeroSpecE2 (T := 0) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ callDeltaF (P + 5) nt (qk q) (Y q)) R (n := P + 5 + 6) (m := P + 4) (by omega)
      errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦
      ⟨(valid_of_callDeltaF_zero (P + 5) nt (qk q) (Y q) hnt hz).1,
        (valid_of_callDeltaF_zero (P + 5) nt (qk q) (Y q) hnt hz).2, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = P + 5 then
    ((e2ReadsSpec (T := 0) hst
        (fun q ↦ ZeroOnF (callDeltaF (P + 5) nt (qk q) (Y q)) r (P + 5 + 6) ∧ R q) zero_le 24).mono
      (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun v ↦
    if hv : v.length = 25 then
      (Spec.congr (verifyKeccakE2_flat P r v).symm
        ((gkrV1Spec (T := (∑ _i ∈ range 7, ((1 : ℕ) : ℝ≥0∞) * errE 1) + T) hst hcard
          (fun q ↦ (∀ l < nt, stepMleK (P + 5) r (Y q l) = v.getD l 0) ∧ R q) qk P hr hv hrT).mono
          (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hout, hmid, htied, hR⟩ ↦
            ⟨callDeltaF_zeroOn (P + 5) nt (qk q) (Y q) hr hnt hout hmid htied, hR⟩)
          (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl)).bind' fun res ↦
      if hres : res.2.1.length = P + 5 + 6 ∧ res.2.2.length = 64 then
        (((rowSwitchSpec (εmax := εS) (T := T) hst hcard qk
            (fun q ↦ (∀ c ∈ res.1, colTrueK (P + 5) (qk q) c) ∧
              (∀ l < nt, stepMleK (P + 5) r (Y q l) = v.getD l 0) ∧ R q)
            res.2.1 res.2.2 hres.2).some).mono
          (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hsl, hcol, htied, hR⟩ ↦
            ⟨hcol, slicesTrueK_of_E2 P (qk q) hres.1 hsl, htied, hR⟩)
          (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun row ↦
        (Spec.ret (r, v, res, row)).mono
          (fun _ hd ↦ ⟨hr, hv, Doomed.mono hd fun q ⟨hrow, hcol, htied, hR⟩ ↦
            ⟨by rw [hres.1]; exact hrow, hcol, htied, hR⟩⟩)
          (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ hres ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hv hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end Specs

end Lvm.E2V
