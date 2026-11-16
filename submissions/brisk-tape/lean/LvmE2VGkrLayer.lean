-- New for lvm2 S1 (E2-F, E2F-V): one Keccak GKR layer's algebra over a field `F` of characteristic two
-- (`LvmKeccakLayerAlg`'s product polynomial and projection, `LvmKeccakLayerSum`'s round families and
-- batched claim), generic in `F`, for `LvmE2VProg`'s `verifyKeccakLayerE2`.
import LvmE2VGkrBase

/-!
# A layer over `F`

The twins of `LvmKeccakLayerAlg`/`LvmKeccakLayerSum` with `E` replaced by `F`:
* `claimSumF`, `ClaimTrueF`, `ClaimShapeF` (moved from `LvmE2VSpecTape`), `claimSumF_roundS`, `iota_eqSF`, `GpolyF`,
  `eval_GpolyF`, `natDegree_GpolyF`;
* the pack rounds' family `FPF` (`FPF_eqFamily`, `FPF_nil`, `FPF_full`), the position rounds'
  `FXF` (`FXF_plainFamily`, `FXF_nil`, `FXF_full`), `dot_weightsF`, `kappa_eqF`;
* **`batch_eqF`**: the batched claim is the claim's sum on the states before the round.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol.KeccakGkr (States stAt Lb chiB iotaB roundB Shape layerRCS afterRoundS
  keccakAlong_zero keccakAlong_along keccakAlong_lt)

local notation "kAlong" => LeanVM.Protocol.Verifier.keccakAlong

section

variable {F : Type} [Field F] [CharP F 2]

/-! ## Claims -/

/-- A claim's sum on the states (`claimSum`). -/
def claimSumF (st : States) (P : ℕ) (point mu w : List F) : F :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * ∑ i ∈ range 16, mu.getD i 0 *
    ∑ j ∈ range 1600, w.getD j 0 * bitF (stAt st P z i j)

/-- **A true claim** on the states (`ClaimTrue`). -/
def ClaimTrueF (st : States) (P : ℕ) (c : KClaim F) : Prop :=
  c.value = claimSumF st P c.point c.mu c.weights

/-- A claim's shape (`ClaimShape`). -/
def ClaimShapeF (P : ℕ) (c : KClaim F) : Prop :=
  c.mu.length = 16 ∧ c.point.length = P + 1 ∧ c.weights.length = 1600

omit [CharP F 2] in
theorem claimSumF_congr {st st' : States} (P : ℕ)
    (h : ∀ m x j, m < 2 → j < 1600 → st m x j = st' m x j) (point mu w : List F) :
    claimSumF st P point mu w = claimSumF st' P point mu w := by
  unfold claimSumF
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hm : z / 2 ^ P < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have := Finset.mem_range.1 hz
    rw [pow_succ] at this
    linarith
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun i _ ↦ congrArg (HMul.hMul _)
    (Finset.sum_congr rfl fun j hj ↦ ?_))
  rw [stAt, stAt, h _ _ _ hm (Finset.mem_range.1 hj)]

/-! ## The product polynomial -/

/-- A pack's bits entering χ at position `j`, embedded. -/
noncomputable def SPF (T : States) (P z j : ℕ) : F[X] :=
  ∑ i ∈ range 16, C (bitF (Lb (stAt T P z i) j)) * embPF i

/-- `κ = emb(1, …, 1)`. -/
noncomputable def kPF : F[X] := ∑ i ∈ range 16, C 1 * embPF i

/-- χ on the packs' embeddings at position `j`. -/
noncomputable def GtermF (T : States) (P z j : ℕ) : F[X] :=
  kPF * SPF T P z j + (kPF + SPF T P z (kAlong j 1)) * SPF T P z (kAlong j 2)

/-- **The honest product polynomial** over `F`. -/
noncomputable def GpolyF (T : States) (P : ℕ) (point w : List F) : F[X] :=
  ∑ z ∈ range (2 ^ (P + 1)), C (eqAtF point z) *
    ∑ j ∈ range 1600, C (w.getD j 0) * GtermF T P z j

theorem kPF_add_SPF (T : States) (P z j : ℕ) :
    (kPF : F[X]) + SPF T P z j = ∑ i ∈ range 16, C (1 + bitF (Lb (stAt T P z i) j)) * embPF i := by
  rw [kPF, SPF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [C_add]; ring

theorem projF_Gterm (T : States) (P z j : ℕ) {i : ℕ} (hi : i < 16) :
    projF (rmfeProject.getD i 0) (GtermF T P z j : F[X]) = bitF (chiB (Lb (stAt T P z i)) j) := by
  rw [GtermF, projF_add, kPF_add_SPF, kPF, SPF, SPF, projF_bilin hi, projF_bilin hi, chiB, bitF_xor,
    bitF_and, bitF_not, one_mul]

theorem projF_Gpoly (T : States) (P : ℕ) (point w : List F) {i : ℕ} (hi : i < 16) :
    projF (rmfeProject.getD i 0) (GpolyF T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z *
        ∑ j ∈ range 1600, w.getD j 0 * bitF (chiB (Lb (stAt T P z i)) j) := by
  rw [GpolyF, projF_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [projF_C_mul, projF_sum]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [projF_C_mul, projF_Gterm T P z j hi]

theorem natDegree_SPF (T : States) (P z j : ℕ) : (SPF T P z j : F[X]).natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (embPF_natDegree i)

theorem natDegree_kPF : (kPF : F[X]).natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (embPF_natDegree i)

theorem natDegree_GtermF (T : States) (P z j : ℕ) : (GtermF T P z j : F[X]).natDegree ≤ 46 := by
  unfold GtermF
  refine natDegree_add_le_of_degree_le ?_ ?_
  · exact natDegree_mul_le_of_le natDegree_kPF (natDegree_SPF T P z j)
  · exact natDegree_mul_le_of_le (natDegree_add_le_of_degree_le natDegree_kPF (natDegree_SPF _ _ _ _))
      (natDegree_SPF T P z _)

theorem natDegree_GpolyF (T : States) (P : ℕ) (point w : List F) :
    (GpolyF T P point w).natDegree ≤ 46 :=
  natDegree_sum_le_of_forall_le _ _ fun z _ ↦ (natDegree_C_mul_le _ _).trans
    (natDegree_sum_le_of_forall_le _ _ fun j _ ↦ (natDegree_C_mul_le _ _).trans
      (natDegree_GtermF T P z j))

/-! ## The projection check -/

/-- ι's weight: `Σ_{z < 64, RC bit z} w_z`. -/
def iotaWF (rc : UInt64) (w : List F) : F :=
  ∑ z ∈ range 64, if rc.toNat.testBit z then w.getD z 0 else 0

omit [CharP F 2] in
theorem sum_iotaBF (rc : UInt64) (w : List F) :
    ∑ j ∈ range 1600, w.getD j 0 * bitF (iotaB rc j) = iotaWF rc w := by
  rw [show 1600 = 64 + 1536 from rfl, Finset.sum_range_add]
  have h2 : ∑ x ∈ range 1536, w.getD (64 + x) 0 * (bitF (iotaB rc (64 + x)) : F) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by simp [iotaB, bitF]
  rw [h2, add_zero, iotaWF]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have e : rc.toNat.testBit z = rc.toBitVec.getLsbD z := rfl
  rw [iotaB, e]
  cases rc.toBitVec.getLsbD z <;> simp [hz', bitF]

/-- A sum over the (pack, segment) indices of a function of the segment. -/
theorem sum_segmentF {P : ℕ} {point : List F} (hpt : point.length = P + 1) (f : ℕ → F) :
    ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * f (z / 2 ^ P) =
      ∑ m ∈ range 2, eqAtF (point.drop P) m * f m := by
  have hsplit : point = point.take P ++ point.drop P := (List.take_append_drop P point).symm
  have htl : (point.take P).length = P := by simp [hpt]
  rw [pow_succ, mul_comm, sum_range_mulB]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h1 : ∀ y ∈ range (2 ^ P), eqAtF point (2 ^ P * m + y) * f ((2 ^ P * m + y) / 2 ^ P) =
      eqAtF (point.take P) y * (eqAtF (point.drop P) m * f m) := by
    intro y hy
    have hy' := Finset.mem_range.1 hy
    have hd : (2 ^ P * m + y) / 2 ^ P = m := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy', zero_add]
    conv_lhs => rw [hsplit]
    rw [eqAtF_append, htl, hd, eqAtF_mod (point.take P), htl,
      Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
    ring
  have hs : ∑ y ∈ range (2 ^ P), eqAtF (point.take P) y = 1 := by
    have := sum_eqAtF (point.take P); rwa [htl] at this
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hs, one_mul]

/-- The claim's sum after the round at a shape: the projection of `G` and ι's known bits. -/
theorem claimSumF_roundS (sh : Shape) (T : States) (step P : ℕ) (point mu w : List F)
    (hpt : point.length = P + 1) :
    claimSumF (afterRoundS sh T step) P point mu w =
      ∑ i ∈ range 16, mu.getD i 0 * projF (rmfeProject.getD i 0) (GpolyF T P point w) +
        (∑ m ∈ range 2, eqAtF (point.drop P) m * iotaWF (layerRCS sh step m) w) *
          ∑ i ∈ range 16, mu.getD i 0 := by
  have hb : ∀ z i j, (bitF (stAt (afterRoundS sh T step) P z i j) : F) =
      bitF (chiB (Lb (stAt T P z i)) j) + bitF (iotaB (layerRCS sh step (z / 2 ^ P)) j) := by
    intro z i j
    rw [stAt, afterRoundS, roundB, bitF_xor]
    rfl
  have e1 : claimSumF (afterRoundS sh T step) P point mu w =
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitF (chiB (Lb (stAt T P z i)) j) +
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaWF (layerRCS sh step (z / 2 ^ P)) w := by
    rw [claimSumF, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have : ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          (bitF (stAt (afterRoundS sh T step) P z i j) : F) =
        ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitF (chiB (Lb (stAt T P z i)) j) +
        (∑ i ∈ range 16, mu.getD i 0) * iotaWF (layerRCS sh step (z / 2 ^ P)) w := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hb, mul_add, Finset.sum_add_distrib, sum_iotaBF]
    rw [this]
    ring
  have p1 : ∑ i ∈ range 16, mu.getD i 0 * projF (rmfeProject.getD i 0) (GpolyF T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitF (chiB (Lb (stAt T P z i)) j) := by
    have h : ∀ i ∈ range 16, mu.getD i 0 * projF (rmfeProject.getD i 0) (GpolyF T P point w) =
        mu.getD i 0 * ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z *
          ∑ j ∈ range 1600, w.getD j 0 * bitF (chiB (Lb (stAt T P z i)) j) :=
      fun i hi ↦ by rw [projF_Gpoly T P point w (Finset.mem_range.1 hi)]
    rw [Finset.sum_congr rfl h]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ by ring
  have p2 : ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaWF (layerRCS sh step (z / 2 ^ P)) w =
      (∑ m ∈ range 2, eqAtF (point.drop P) m * iotaWF (layerRCS sh step m) w) *
        ∑ i ∈ range 16, mu.getD i 0 := by
    rw [← sum_segmentF hpt (fun m ↦ iotaWF (layerRCS sh step m) w), Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  rw [e1, p1, p2]

/-- **The verifier's `iota` at a shape** (`iota_eqS`). -/
theorem iota_eqSF {sh : Shape} (hsh : sh.Ok) (step P : ℕ) (claim : KClaim F)
    (hpt : claim.point.length = P + 1) :
    iotaSF sh (sh.logSteps P) step claim =
      ∑ m ∈ range 2, eqAtF (claim.point.drop P) m * iotaWF (layerRCS sh step m) claim.weights := by
  have hsum : ∀ c : UInt64, sumF ((List.range 64).filterMap fun z ↦
      if c.toNat.testBit z then some (claim.weights.getD z 0) else none) = iotaWF c claim.weights :=
    fun c ↦ by rw [sumF_filterMap_range]; rfl
  have hl : (claim.point.drop P).length = 1 := by simp [hpt]
  unfold iotaSF
  simp only []
  rw [sumF_map_range]
  rcases hsh.1 with h1 | h2
  · have hd : claim.point.drop (sh.logSteps P - 4) = [] := by
      rw [Shape.logSteps, if_pos h1]; exact List.drop_eq_nil_of_le (by rw [hpt]; omega)
    have hseg : ∀ m, layerRCS sh step m = keccakRC.getD (sh.depth * (0 + 1) - step - 1) 0 :=
      fun m ↦ by rw [layerRCS, Shape.seg, if_pos h1, keccakRC_eqV]
    have h2 : ∑ m ∈ range 2, eqAtF (claim.point.drop P) m = 1 := by
      simpa [hl] using sum_eqAtF (claim.point.drop P)
    simp only [hseg]
    rw [← Finset.sum_mul, h2, one_mul, h1, Finset.sum_range_one, hd, eqKernelF_getD, hsum]
    simp
  · have hlog : sh.logSteps P - 4 = P := by rw [Shape.logSteps, if_neg (by omega)]; omega
    rw [hlog, h2]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm' := Finset.mem_range.1 hm
    rw [eqKernelF_getD, hl, ite_eq_left (by simpa using hm'), hsum, layerRCS, Shape.seg,
      if_neg (by omega), keccakRC_eqV]

/-! ## The value at the evaluation point -/

/-- A pack's state entering χ at `s`. -/
noncomputable def Shat0F (T : States) (P : ℕ) (s : F) (z j : ℕ) : F :=
  ∑ i ∈ range 16, (embPF i).eval s * bitF (Lb (stAt T P z i) j)

/-- `κ(s)`. -/
noncomputable def kappaAtF (s : F) : F := ∑ i ∈ range 16, (embPF i).eval s

omit [CharP F 2] in
theorem eval_GpolyF_aux (T : States) (P : ℕ) (point w : List F) (s : F) (n : ℕ) :
    (∑ z ∈ range (2 ^ (P + 1)), C (eqAtF point z) *
      ∑ j ∈ range n, C (w.getD j 0) * GtermF T P z j).eval s =
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * ∑ j ∈ range n, w.getD j 0 *
        (kappaAtF s * Shat0F T P s z j + (kappaAtF s + Shat0F T P s z (kAlong j 1)) *
          Shat0F T P s z (kAlong j 2)) := by
  have hS : ∀ z j, (SPF T P z j).eval s = Shat0F T P s z j := fun z j ↦ by
    simp only [SPF, Shat0F, eval_finsetSum, eval_mul, eval_C]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hk : (kPF : F[X]).eval s = kappaAtF s := by
    simp only [kPF, kappaAtF, eval_finsetSum, eval_mul, eval_C, one_mul]
  simp only [GtermF, eval_finsetSum, eval_mul, eval_C, eval_add, hS, hk]

omit [CharP F 2] in
theorem eval_GpolyF (T : States) (P : ℕ) (point w : List F) (s : F) :
    (GpolyF T P point w).eval s =
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF point z * ∑ j ∈ range 1600, w.getD j 0 *
        (kappaAtF s * Shat0F T P s z j + (kappaAtF s + Shat0F T P s z (kAlong j 1)) *
          Shat0F T P s z (kAlong j 2)) :=
  eval_GpolyF_aux T P point w s 1600

/-! ## The pack and segment rounds -/

variable (T : States) (P : ℕ) (s : F) (w : List F)

/-- The packs' states at `s`, extended multilinearly in the (pack, segment) point. -/
noncomputable def ShatF (j : ℕ) (c : List F) : F :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAtF c z * Shat0F T P s z j

/-- χ of the packs' states at the point `c`. -/
noncomputable def gtF (c : List F) : F :=
  ∑ j ∈ range 1600, w.getD j 0 * (kappaAtF s * ShatF T P s j c +
    (kappaAtF s + ShatF T P s (kAlong j 1) c) * ShatF T P s (kAlong j 2) c)

/-- The pack and segment rounds' family at the claim's point `r`. -/
noncomputable def FPF (r acc : List F) : F :=
  ∑ z ∈ range (2 ^ (P + 1 - acc.length)), eqAtF (r.drop acc.length) z *
    gtF T P s w (acc ++ bitsF z (P + 1 - acc.length))

theorem Shat_bitsF (j : ℕ) {z : ℕ} (hz : z < 2 ^ (P + 1)) :
    ShatF T P s j (bitsF z (P + 1)) = Shat0F T P s z j :=
  sum_eqAtF_bitsF hz _

theorem FPF_nil (r : List F) : FPF T P s w r [] = (GpolyF T P r w).eval s := by
  rw [eval_GpolyF, FPF]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.nil_append, gtF]
  have hz' := Finset.mem_range.1 hz
  simp only [Shat_bitsF T P s _ hz']

omit [CharP F 2] in
theorem FPF_full (r acc : List F) (hr : r.length = P + 1) (h : acc.length = P + 1) :
    FPF T P s w r acc = gtF T P s w acc := by
  rw [FPF, h, Nat.sub_self, List.drop_eq_nil_of_le (by omega)]
  simp [bitsF]

omit [CharP F 2] in
theorem polyLEF_Shat (pre post : List F) (j : ℕ) :
    PolyLEF 1 fun x ↦ ShatF T P s j (pre ++ x :: post) :=
  polyLEF_mle pre post _ _

omit [CharP F 2] in
theorem polyLEF_gt (pre post : List F) : PolyLEF 2 fun x ↦ gtF T P s w (pre ++ x :: post) := by
  refine PolyLEF.sum _ fun j _ ↦ PolyLEF.const_mul ?_ _
  refine PolyLEF.add ((PolyLEF.const_mul (polyLEF_Shat T P s pre post j) _).mono (by norm_num)) ?_
  exact (PolyLEF.mul ((PolyLEF.add (PolyLEF.const 1 _) (polyLEF_Shat T P s pre post _)))
    (polyLEF_Shat T P s pre post _))

omit [CharP F 2] in
/-- **The pack and segment rounds' family**: degree two, split by the equality weights. -/
theorem FPF_eqFamily {β : Type} (Tq : β → States) (r : List F) (hr : r.length = P + 1) :
    EqFamilyF (fun q acc ↦ FPF (Tq q) P s w r acc) r 2 := by
  intro q acc hacc
  have hm : P + 1 - acc.length = (P + 1 - (acc.length + 1)) + 1 := by omega
  have hdrop : r.drop acc.length = r[acc.length] :: r.drop (acc.length + 1) :=
    List.drop_eq_getElem_cons hacc
  refine ⟨?_, ?_⟩
  · have e : ∀ x, FPF (Tq q) P s w r (acc ++ [x]) =
        ∑ z ∈ range (2 ^ (P + 1 - (acc.length + 1))), eqAtF (r.drop (acc.length + 1)) z *
          gtF (Tq q) P s w (acc ++ x :: bitsF z (P + 1 - (acc.length + 1))) := by
      intro x
      simp only [FPF, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    refine PolyLEF.congr (f := fun x ↦ ∑ z ∈ range (2 ^ (P + 1 - (acc.length + 1))),
      eqAtF (r.drop (acc.length + 1)) z *
        gtF (Tq q) P s w (acc ++ x :: bitsF z (P + 1 - (acc.length + 1)))) ?_ fun x ↦ (e x).symm
    exact PolyLEF.sum _ fun z _ ↦ PolyLEF.const_mul (polyLEF_gt (Tq q) P s w acc _) _
  · simp only [FPF, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succW, hdrop, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [eqAtF_succ, eqAtF_succ, bitsF_two_mul, bitsF_two_mul_add_one]
    have h1 : 2 * z % 2 = 0 := by omega
    have h2 : (2 * z + 1) % 2 = 1 := by omega
    have h3 : 2 * z / 2 = z := by omega
    have h4 : (2 * z + 1) / 2 = z := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false, List.append_assoc,
      List.singleton_append]
    ring

/-! ## The position rounds -/

/-- The packs' state at `c`, `k` columns along, extended over the position bits. -/
noncomputable def TkF (c : List F) (k : ℕ) (p : List F) : F :=
  ∑ j ∈ range 1600, eqAtF p j * ShatF T P s (kAlong j k) c

/-- The position weights, extended over the position bits. -/
noncomputable def WtF (p : List F) : F := ∑ j ∈ range 1600, eqAtF p j * w.getD j 0

/-- The position rounds' summand. -/
noncomputable def phiF (c p : List F) : F :=
  WtF w p * (kappaAtF s * TkF T P s c 0 p + (kappaAtF s + TkF T P s c 1 p) * TkF T P s c 2 p)

/-- The position rounds' family. -/
noncomputable def FXF (c : List F) (scale : F) (acc : List F) : F :=
  scale * ∑ u ∈ range (2 ^ (11 - acc.length)), phiF T P s w c (acc ++ bitsF u (11 - acc.length))

omit T P s w in
theorem sum1600_bitsF {u : ℕ} (hu : u < 2 ^ 11) (f : ℕ → F) :
    ∑ j ∈ range 1600, eqAtF (bitsF u 11) j * f j = if u < 1600 then f u else 0 := by
  have h : ∀ j ∈ range 1600, eqAtF (bitsF u 11) j * f j = if u = j then f j else 0 := by
    intro j hj
    rw [eqAtF_bitsF_lt hu (by have := Finset.mem_range.1 hj; omega)]
    by_cases h : j = u
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  simp

theorem FXF_nil (c : List F) (scale : F) : FXF T P s w c scale [] = scale * gtF T P s w c := by
  unfold FXF
  refine congrArg (HMul.hMul _) ?_
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  rw [show 2 ^ 11 = 1600 + 448 from rfl, Finset.sum_range_add]
  have hrest : ∑ x ∈ range 448, phiF T P s w c (bitsF (1600 + x) 11) = 0 := by
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hx' := Finset.mem_range.1 hx
    rw [phiF, WtF, sum1600_bitsF (by omega), ite_eq_right (by omega), zero_mul]
  rw [hrest, add_zero, gtF]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [phiF, WtF, TkF, TkF, TkF, sum1600_bitsF (by omega), sum1600_bitsF (by omega),
    sum1600_bitsF (by omega), sum1600_bitsF (by omega), ite_eq_left hu', ite_eq_left hu',
    ite_eq_left hu', ite_eq_left hu', keccakAlong_zero hu']

omit [CharP F 2] in
theorem FXF_full (c : List F) (scale : F) (acc : List F) (h : acc.length = 11) :
    FXF T P s w c scale acc = scale * phiF T P s w c acc := by
  rw [FXF, h, Nat.sub_self]
  simp [bitsF]

omit [CharP F 2] in
theorem polyLEF_phi (c pre post : List F) :
    PolyLEF 3 fun x ↦ phiF T P s w c (pre ++ x :: post) := by
  unfold phiF WtF TkF
  refine PolyLEF.mul (d := 1) (d' := 2) (polyLEF_mle pre post _ _) ?_
  refine PolyLEF.add ((PolyLEF.const_mul (polyLEF_mle pre post _ _) _).mono (by norm_num)) ?_
  exact PolyLEF.mul (PolyLEF.add (PolyLEF.const 1 _) (polyLEF_mle pre post _ _))
    (polyLEF_mle pre post _ _)

omit [CharP F 2] in
/-- **The position rounds' family**: degree three, plain. -/
theorem FXF_plainFamily {β : Type} (Tq : β → States) (c : List F) (scale : F) :
    PlainFamilyF (fun q acc ↦ FXF (Tq q) P s w c scale acc) 3 11 := by
  intro q acc hacc
  have hm : 11 - acc.length = (11 - (acc.length + 1)) + 1 := by omega
  refine ⟨?_, ?_⟩
  · have e : ∀ x, FXF (Tq q) P s w c scale (acc ++ [x]) =
        scale * ∑ u ∈ range (2 ^ (11 - (acc.length + 1))),
          phiF (Tq q) P s w c (acc ++ x :: bitsF u (11 - (acc.length + 1))) := by
      intro x
      simp only [FXF, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    refine PolyLEF.congr (f := fun x ↦ scale * ∑ u ∈ range (2 ^ (11 - (acc.length + 1))),
      phiF (Tq q) P s w c (acc ++ x :: bitsF u (11 - (acc.length + 1)))) ?_ fun x ↦ (e x).symm
    exact PolyLEF.const_mul (PolyLEF.sum _ fun u _ ↦ polyLEF_phi (Tq q) P s w c acc _) scale
  · simp only [FXF, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succW, ← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun u _ ↦ ?_)
    rw [bitsF_two_mul, bitsF_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

omit [CharP F 2] T P s in
/-- **The final check's weight**: `dot(eq[:1600], w)` is `W`. -/
theorem dot_weightsF (p : List F) (hp : p.length = 11) (hw : w.length = 1600) :
    dotF ((eqKernelF p).take keccakBits) w = WtF w p := by
  rw [show keccakBits = w.length from hw.symm, dot_eqKernelF p w (by rw [hp, hw]; norm_num), hw]
  rfl

omit T P w in
theorem kappa_eqF : sumF (instWeightsF s) = kappaAtF s := by
  rw [sumF_eq_sum, list_sum_getDF, instWeightsF_length, kappaAtF]
  exact Finset.sum_congr rfl fun i hi ↦ instWeightsF_getD s (Finset.mem_range.1 hi)

omit [CharP F 2] in
theorem Tk_shiftF (c p : List F) {k k' : ℕ} (hk : k + k' = 5) :
    TkF T P s c k p = ∑ j ∈ range 1600, eqAtF p (kAlong j k') * ShatF T P s j c := by
  unfold TkF
  calc ∑ j ∈ range 1600, eqAtF p j * ShatF T P s (kAlong j k) c
      = ∑ j ∈ range 1600, eqAtF p (kAlong (kAlong j k) k') *
          ShatF T P s (kAlong j k) c :=
        Finset.sum_congr rfl fun j _ ↦ by rw [keccakAlong_along hk]
    _ = _ := sum_permF 1600 (fun j ↦ kAlong j k) (fun j ↦ kAlong j k')
        (fun j hj ↦ keccakAlong_lt k hj) (fun j hj ↦ keccakAlong_lt k' hj)
        (fun j _ ↦ keccakAlong_along (by omega)) (fun j _ ↦ keccakAlong_along hk)
        (fun j ↦ eqAtF p (kAlong j k') * ShatF T P s j c)

omit T P s w [CharP F 2] in
/-- The verifier's batched weights (`verifyKeccakLayerE2`'s `weights`). -/
def batchWF (p : List F) (beta : F) : List F :=
  (List.range keccakBits).map fun j ↦ (eqKernelF p).getD j 0 +
    beta * ((eqKernelF p).getD (keccakAlong j 4) 0 + beta * (eqKernelF p).getD (keccakAlong j 3) 0)

omit T P s w [CharP F 2] in
theorem batchWF_getD (p : List F) (hp : p.length = 11) (beta : F) {j : ℕ} (hj : j < 1600) :
    (batchWF p beta).getD j 0 =
      eqAtF p j + beta * (eqAtF p (kAlong j 4) + beta * eqAtF p (kAlong j 3)) := by
  have hA : ∀ k, (eqKernelF p).getD (keccakAlong j k) 0 = eqAtF p (kAlong j k) :=
    fun k ↦ by rw [eqKernelF_getD, hp, keccakAlong_eqV,
      ite_eq_left (by have := keccakAlong_lt k hj; omega)]
  rw [batchWF, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  rw [hA 4, hA 3, eqKernelF_getD, hp, ite_eq_left (by omega)]

/-- **The batched claim**: `T_0 + β(T_1 + βT_2)` at the position point is the claim's sum on the
states before the round. -/
theorem batch_eqF (c p : List F) (hp : p.length = 11) (beta : F) :
    TkF T P s c 0 p + beta * (TkF T P s c 1 p + beta * TkF T P s c 2 p) =
      claimSumF T P c (instWeightsF s) (linearTransposeF (batchWF p beta)) := by
  have h0 : TkF T P s c 0 p = ∑ j ∈ range 1600, eqAtF p j * ShatF T P s j c :=
    Finset.sum_congr rfl fun j hj ↦ by rw [keccakAlong_zero (Finset.mem_range.1 hj)]
  have hcomb : TkF T P s c 0 p + beta * (TkF T P s c 1 p + beta * TkF T P s c 2 p) =
      ∑ j ∈ range 1600, (batchWF p beta).getD j 0 * ShatF T P s j c := by
    rw [h0, Tk_shiftF T P s c p (show 1 + 4 = 5 from rfl),
      Tk_shiftF T P s c p (show 2 + 3 = 5 from rfl)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [batchWF_getD p hp beta (Finset.mem_range.1 hj)]
    ring
  have step1 : ∑ j ∈ range 1600, (batchWF p beta).getD j 0 * ShatF T P s j c =
      ∑ z ∈ range (2 ^ (P + 1)), eqAtF c z * ∑ i ∈ range 16, (embPF i).eval s *
        ∑ j ∈ range 1600, (batchWF p beta).getD j 0 * bitF (Lb (stAt T P z i) j) := by
    simp only [ShatF, Shat0F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hcomb, step1, claimSumF]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg (HMul.hMul _)
    (Finset.sum_congr rfl fun i hi ↦ ?_)
  rw [transpose_bitsF, instWeightsF_getD s (Finset.mem_range.1 hi)]

end

end Lvm.E2V
