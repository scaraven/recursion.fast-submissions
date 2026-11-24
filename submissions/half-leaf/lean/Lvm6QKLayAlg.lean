-- New for lvm6 (WP CB-L). The weight algebra of one normalized Keccak layer in CB's circuit form,
-- over a field: the next claim's weights as product weights, the final check's weight and the iota
-- term on the two kinds of carried weights (`WRep`). Season 1's `LvmQEqKeccakAlgG` and the
-- algebra part of the parked `LvmE2QKLayerEq` (`dot_take_weighted`, `next_weights`), restated
-- over a field parameter.
import Lvm6QKClaim
import LvmQEqKeccakAlgG

/-!
# The layer's weight algebra (CB-L)

* **`batchW_eq`**: the next claim's batched weights `batchWF p β` (`p` the 11 position
  challenges) are the product weights `eq(p₀…₅, ·) ⊗ B`, `B` the 25 lane weights from `p₆…₁₀` and
  `β` (`laneWB`).
* **`firstW_eq`**: leanVM's first weights are the product weights `x^z ⊗ eq(r_lane, ·)`.
* **`dot_prod`**, **`dot_lt`**: the final check's weight `dot(eq(lp)[:1600], W)` for product
  weights (two sums) and for transposed product weights (25 lane forms of the rotated sum).
* **`iotaSF_two`**: the iota correction at `Shape.v1` is `(1 + r)·ι(rc₀, W) + r·ι(rc₁, W)`, `r`
  the segment coordinate; `prodWG_iota`: a product weight at slice `2^i − 1` of lane `0`.
-/

set_option autoImplicit false

namespace Lvm6.QK

open Lvm Lvm.E2V Lvm.Q1 Finset
open LeanVM.Protocol.KeccakGkr (Shape)
open LeanVM.Parameters (E2)

section

variable {F : Type} [Field F]

/-! ## `eq` of an 11-point, the final check's weight -/

/-- `eq` of an 11-point at `j < 2^11` splits into the low six and high five coordinates. -/
theorem eqKernelF_split11 {lp : List F} (hl : lp.length = 11) {j : ℕ} (hj : j < 2048) :
    (eqKernelF lp).getD j 0 = eqAtG (lp.take 6) (j % 64) * (eqKernelF (lp.drop 6)).getD (j / 64) 0 := by
  have ht : (lp.take 6).length = 6 := by simp [hl]
  have hd : (lp.drop 6).length = 5 := by simp [hl]
  rw [eqKernelF_getD, ite_eq_left (by rw [hl]; exact hj), eqAtG, eqKernelF_getD, eqKernelF_getD,
    ite_eq_left (by rw [ht]; exact Nat.mod_lt _ (by omega)), ite_eq_left (by rw [hd]; omega),
    ← List.take_append_drop 6 lp, eqAtF_append, List.take_append_drop, ht, eqAtF_mod (lp.take 6) j, ht]
  rfl

/-- **`V`'s `dot(eq[:1600], W)`** on an 11-point is the lane-then-slice weighted sum. -/
theorem dot_take_weighted {lp W : List F} (hl : lp.length = 11) (hW : W.length = 1600) :
    dotF ((eqKernelF lp).take LeanVM.Protocol.Verifier.keccakBits) W =
      weightedFG (eqKernelF (lp.drop 6)) (eqKernelF (lp.take 6)) W := by
  rw [show LeanVM.Protocol.Verifier.keccakBits = W.length by rw [hW]; rfl,
    dotF_eq _ _ (by simp [eqKernelF_length, hl, hW]), List.length_take, eqKernelF_length, hl, hW]
  rw [show min 1600 (2 ^ 11) = 25 * 64 from rfl, sum_range_mulB, weightedFG, sumF_map_range]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl25 := Finset.mem_range.mp hl'
  rw [sumF_map_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz64 := Finset.mem_range.mp hz
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega), ← List.getD_eq_getElem?_getD,
    eqKernelF_split11 hl (by omega), show (64 * l + z) % 64 = z by omega,
    show (64 * l + z) / 64 = l by omega]
  unfold eqAtG
  ring

/-- **The final check's weight on product weights** `C ⊗ B`: two sums. -/
theorem dot_prod {lp : List F} (hl : lp.length = 11) (C : ℕ → F) (B : List F) :
    dotF ((eqKernelF lp).take LeanVM.Protocol.Verifier.keccakBits) (prodWG C B) =
      sumF ((List.range 25).map fun l ↦ (eqKernelF (lp.drop 6)).getD l 0 * B.getD l 0) *
        sumF ((List.range 64).map fun z ↦ (eqKernelF (lp.take 6)).getD z 0 * C z) := by
  rw [dot_take_weighted hl (prodWG_length _ _), weightedFG, sumF_map_range, sumF_map_range,
    sumF_map_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl25 := Finset.mem_range.mp hl'
  rw [sumF_map_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz64 := Finset.mem_range.mp hz
  rw [prodWG_getD C B (by omega), show (64 * l + z) % 64 = z by omega,
    show (64 * l + z) / 64 = l by omega]
  ring

/-- **The final check's weight on transposed product weights**: 25 lane forms of the rotated sum. -/
theorem dot_lt {lp : List F} (hl : lp.length = 11) (a B : List F) :
    dotF ((eqKernelF lp).take LeanVM.Protocol.Verifier.keccakBits) (linearTransposeF (prodWG (eqAtG a) B)) =
      sumF ((List.range 25).map fun l ↦ (eqKernelF (lp.drop 6)).getD l 0 *
        laneFormF B (rotSumG (eqAtG (lp.take 6)) (eqAtG a)) l) := by
  rw [dot_take_weighted hl (linearTransposeF_length _), weightedFG]
  refine congrArg sumF (List.map_congr_left fun l hl' ↦ ?_)
  rw [lane_dotG _ _ _ (List.mem_range.mp hl')]
  rfl

/-- The rotated sum reads its shift modulo 64. -/
theorem rotSum_mod (u A : ℕ → F) (s : ℕ) : rotSumG u A (s % 64) = rotSumG u A s := by
  unfold rotSumG
  refine congrArg sumF (List.map_congr_left fun z _ ↦ ?_)
  rw [Nat.add_mod_mod]

/-! ## The next claim's weights -/

theorem along_split (j k : ℕ) :
    LeanVM.Protocol.Verifier.keccakAlong j k = 64 * (keccakAlong (64 * (j / 64)) k / 64) + j % 64 := by
  rw [← keccakAlong_eqV]
  unfold keccakAlong
  simp only []
  omega

/-- The 25 lane weights of the next claim: `eq_L(ℓ) + β·(eq_L(x+4) + β·eq_L(x+3))`. -/
def laneWB (p : List F) (beta : F) : List F :=
  (List.range 25).map fun l ↦ (eqKernelF (p.drop 6)).getD l 0 + beta *
    ((eqKernelF (p.drop 6)).getD (keccakAlong (64 * l) 4 / 64) 0 + beta *
      (eqKernelF (p.drop 6)).getD (keccakAlong (64 * l) 3 / 64) 0)

theorem next_weights {lp : List F} (hl : lp.length = 11) (beta : F) :
    (List.range LeanVM.Protocol.Verifier.keccakBits).map (fun j ↦
      (eqKernelF lp).getD j 0 + beta * ((eqKernelF lp).getD (LeanVM.Protocol.Verifier.keccakAlong j 4) 0 +
        beta * (eqKernelF lp).getD (LeanVM.Protocol.Verifier.keccakAlong j 3) 0)) =
    prodWG (eqAtG (lp.take 6)) (laneWB lp beta) := by
  unfold prodWG laneWB
  rw [show LeanVM.Protocol.Verifier.keccakBits = keccakBits from rfl]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < 1600 := List.mem_range.mp hj
  have ha : ∀ k, k < 5 → keccakAlong (64 * (j / 64)) k / 64 < 25 := by
    intro k _; unfold keccakAlong; simp only []; omega
  rw [along_split j 4, along_split j 3, eqKernelF_split11 hl (by omega),
    eqKernelF_split11 hl (by have := ha 4 (by omega); omega),
    eqKernelF_split11 hl (by have := ha 3 (by omega); omega),
    show (64 * (keccakAlong (64 * (j / 64)) 4 / 64) + j % 64) % 64 = j % 64 by omega,
    show (64 * (keccakAlong (64 * (j / 64)) 3 / 64) + j % 64) % 64 = j % 64 by omega,
    show (64 * (keccakAlong (64 * (j / 64)) 4 / 64) + j % 64) / 64 = keccakAlong (64 * (j / 64)) 4 / 64 by omega,
    show (64 * (keccakAlong (64 * (j / 64)) 3 / 64) + j % 64) / 64 = keccakAlong (64 * (j / 64)) 3 / 64 by omega,
    List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  ring

/-- **The next claim's weights are product weights** `eq(p₀…₅, ·) ⊗ laneWB p β`. -/
theorem batchW_eq {p : List F} (hp : p.length = 11) (beta : F) :
    batchWF p beta = prodWG (eqAtG (p.take 6)) (laneWB p beta) :=
  next_weights hp beta

/-! ## The iota term -/

/-- The round constant of segment `seg` at layer `step` (`Shape.v1`: 12 layers a segment). -/
def rcAt (step seg : ℕ) : UInt64 := Lvm.keccakRC.getD (12 * (seg + 1) - step - 1) 0

theorem rcAt_mem {step seg : ℕ} (hs : step < 12) (hg : seg < 2) : rcAt step seg ∈ Lvm.keccakRC := by
  have hlen : Lvm.keccakRC.length = 24 := rfl
  unfold rcAt
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
  exact List.getElem_mem _

/-- **The iota correction at `Shape.v1`**: the two segments' round constants, weighted by the
segment coordinate `r = point[κ − 4]`. -/
theorem iotaSF_two (κ step : ℕ) (cl : KClaim F) (hκ : 5 ≤ κ) (hpt : cl.point.length = κ - 3) :
    iotaSF Shape.v1 κ step cl = (1 + cl.point.getD (κ - 4) 0) * iotaFG (rcAt step 0) cl.weights +
      cl.point.getD (κ - 4) 0 * iotaFG (rcAt step 1) cl.weights := by
  have hd : cl.point.drop (κ - 4) = [cl.point.getD (κ - 4) 0] := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    apply List.ext_getElem (by simp [hpt]; omega)
    intro n h1 h2
    have hn : n = 0 := by simp at h2; omega
    subst hn
    simp
  have e0 : (eqKernelF [cl.point.getD (κ - 4) 0]).getD 0 0 = 1 + cl.point.getD (κ - 4) 0 := by
    simp [eqKernelF]
  have e1 : (eqKernelF [cl.point.getD (κ - 4) 0]).getD 1 0 = cl.point.getD (κ - 4) 0 := by
    simp [eqKernelF, List.getD_eq_getElem?_getD]
  show sumF ((List.range 2).map fun segment ↦
      (eqKernelF (cl.point.drop (κ - 4))).getD segment 0 *
        iotaFG (Lvm.keccakRC.getD (12 * (segment + 1) - step - 1) 0) cl.weights) = _
  rw [hd, sumF_map_range, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [e0, e1, rcAt]

theorem iotaPos_lt64 {i : ℕ} (hi : i < 7) : iotaPos i < 64 := iotaPos_ltG hi

/-- A product weight at slice `2^i − 1` of lane `0`. -/
theorem prodWG_iota (C : ℕ → F) (B : List F) {i : ℕ} (hi : i < 7) :
    (prodWG C B).getD (iotaPos i) 0 = C (iotaPos i) * B.getD 0 0 := by
  have h := iotaPos_ltG hi
  rw [prodWG_getD C B (by omega), Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]

end

/-! ## The first claim -/

/-- **leanVM's first weights are product weights** `x^z ⊗ eq(r_lane, ·)`. -/
theorem firstW_eq (rl : List E2) :
    firstWeightsF rl = prodWG (fun z ↦ (nF (2 ^ z) : E2)) (eqKernelF rl) := by
  unfold firstWeightsF prodWG
  exact List.map_congr_left fun j _ ↦ mul_comm _ _

end Lvm6.QK
