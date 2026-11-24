-- New for lvm6 (WP W1). The deployed opening against WP S's candidate seam (CAND decision): the
-- level-0 ball of stacks (`ball18`, the decoded Johnson list of the first commitment's word), the
-- decoding of a level-0 tuple to a stack (`dec18`: the low parts of its 64 lanes, read in `K`), and
-- the opening in S's `stackedSpec` form (`openSpec18`): from one commitment and doom over the ball,
-- rejection at `εI`. The decoding is exact on the ball: a tuple agreeing with the `K`-valued word on
-- more columns than its degree has `K` coefficients (`coeff_mem_range_of_agree`), so its low parts
-- are `K` values (`lowMsgF_map`).
import Lvm6WhirProg
import Lvm6StmtPhase

/-!
# The opening at S's seam (W1)

* `coeff_mem_range_of_agree`: a polynomial over `E2` of degree `≤ d` with `K` values at `> d`
  points of `K` has `K` coefficients.
* `lowMsgF_map`: the low part commutes with `K → E2`.
* `dec18 U x`: stack word `x = r + 2^19·slot` is `lowMsg_19(U_slot)(r)` in `K`.
* `ball18 h`: the decoded tuples of degree `≤ 2^19 + 5` agreeing with the first commitment's word on
  `≥ 1,053,294` columns. **`hhold18`**: on the ball, `den (w₀ cl) U = cl.2 → cl.Holds 25 (dec18 U)`.
* **`openSpec18`**: S's `stackedSpec` body at `P18` with `I.ball := ball18`, for a claim whose weight
  is affine in each of its 25 variables.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.EndToEnd.Front Polynomial Finset
open scoped ENNReal

/-! ## `K` coefficients from `K` values -/

/-- The imaginary part of a polynomial's coefficients, as a polynomial over `K`. -/
noncomputable def imPoly (P : E2[X]) : K[X] := ∑ j ∈ range (P.natDegree + 1), C (P.coeff j).im * X ^ j

theorem im_eval_algebraMap (P : E2[X]) (x : K) :
    (P.eval (algebraMap K E2 x)).im = (imPoly P).eval x := by
  rw [eval_eq_sum_range, imPoly, eval_finset_sum]
  rw [show (∑ i ∈ range (P.natDegree + 1), P.coeff i * (algebraMap K E2 x) ^ i).im =
      ∑ i ∈ range (P.natDegree + 1), (P.coeff i * (algebraMap K E2 x) ^ i).im from
    map_sum (QuadraticAlgebra.imₗ _ _ : E2 →ₗ[K] K) _ _]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← map_pow, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im]
  simp

theorem natDegree_imPoly_le (P : E2[X]) : (imPoly P).natDegree ≤ P.natDegree := by
  unfold imPoly
  refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- **`K` values at more points than the degree force `K` coefficients.** -/
theorem coeff_mem_range_of_agree {n d : ℕ} (P : E2[X]) (hP : P.natDegree ≤ d) (pts : Fin n → K)
    (hinj : Function.Injective pts) (S : Finset (Fin n)) (hS : d < S.card)
    (hval : ∀ x ∈ S, (P.eval (algebraMap K E2 (pts x))).im = 0) (j : ℕ) :
    P.coeff j ∈ Set.range (algebraMap K E2) := by
  have h0 : imPoly P = 0 := by
    by_contra hne
    have hroots : S.card ≤ (imPoly P).roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn pts (fun x hx ↦ ?_) hinj.injOn
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot, ← im_eval_algebraMap]
      exact hval x hx
    have := (hroots.trans (Multiset.toFinset_card_le _)).trans (card_roots' _)
    have := this.trans ((natDegree_imPoly_le P).trans hP)
    omega
  refine ⟨(P.coeff j).re, QuadraticAlgebra.ext rfl ?_⟩
  rw [QuadraticAlgebra.algebraMap_im]
  by_cases hj : j ≤ P.natDegree
  · have := congrArg (fun Q ↦ Q.coeff j) h0
    simp only [imPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single j (fun b _ hb ↦ by simp [Ne.symm hb]) (fun h ↦ absurd
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h)] at this
    simpa using this.symm
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    rfl

/-! ## The low part commutes with `K → E2` -/

theorem msgPolyF_map {κ : ℕ} (g : (Fin κ → Bool) → K) :
    msgPolyF (F := E2) κ (fun u ↦ algebraMap K E2 (g u)) = (msgPolyF (F := K) κ g).map (algebraMap K E2) := by
  simp only [msgPolyF, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.map_sum,
    Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C, novelF, Polynomial.map_map,
    Algebra.algebraMap_self, RingHom.comp_id]

theorem lowMsgF_map {κ : ℕ} (hκ : κ ≤ 64) (P : K[X]) :
    lowMsgF (F := E2) κ (P.map (algebraMap K E2)) = fun u ↦ algebraMap K E2 (lowMsgF (F := K) κ P u) := by
  apply msgPolyF_injective (F := E2) hκ
  rw [msgPolyF_lowMsgF hκ, msgPolyF_map, msgPolyF_lowMsgF hκ, vanF, vanF, Algebra.algebraMap_self,
    Polynomial.map_id]
  exact (map_modByMonic (algebraMap K E2)
    (show (vanishing κ).Monic from monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _)).symm

/-! ## The level-0 decoding and the ball -/

/-- **The stack a level-0 tuple decodes to**: word `x = r + 2^19·slot` is the `K` part of
`lowMsg_19(U_slot)(r)` (bits `0..18` of `x` are `r`, bits `19..24` the slot). -/
noncomputable def dec18 (U : Tup E2 (0 + 6)) : Stack := fun x ↦
  (lowMsgF 19 (U fun i ↦ x.testBit (19 + i)) fun i ↦ x.testBit i).re

/-- **The level-0 ball** of a history: the stacks decoded from the tuples of degree `≤ 2^19 + 5`
agreeing with the first commitment's word on at least `1,053,294` columns. -/
def ball18 (h : List Ev) : Set Stack := ball lad18 dec18 (1053300 - 6) h

/-- The word of commitment `0` reads `K` values. -/
theorem wordE_im (cs : List (ℕ × ℕ × Word)) (u : Fin (0 + 6) → Bool) (p : Fin (2 ^ 21)) :
    (wordE true 0 (0 + 6) 21 cs u p).im = 0 := by
  unfold wordE
  split
  · simp [laneVal, QuadraticAlgebra.algebraMap_im]
  · rfl

/-- A ball tuple's lanes have `K` coefficients. -/
theorem lane_lifts (cs : List (ℕ × ℕ × Word)) (U : Tup E2 (0 + 6))
    (hU : DegLE (2 ^ 19 - 1 + 6) U)
    (hag : 1053300 - 6 ≤ (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 cs)).card)
    (u : Fin (0 + 6) → Bool) : U u ∈ Polynomial.lifts (algebraMap K E2) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro j
  refine coeff_mem_range_of_agree (U u) (hU u) (fun p : Fin (2 ^ 21) ↦ K.ofBits p) (fun p q hpq ↦ ?_)
    (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 cs)) (by norm_num at hag ⊢; omega)
    (fun x hx ↦ ?_) j
  · have hp : (p : ℕ) < 2 ^ 64 := lt_of_lt_of_le p.isLt (by norm_num)
    have hq : (q : ℕ) < 2 ^ 64 := lt_of_lt_of_le q.isLt (by norm_num)
    exact Fin.ext (ofBits_injOn hp hq hpq)
  · rw [mem_agree] at hx
    have := hx u
    rw [show domE 21 (by norm_num) x = algebraMap K E2 (K.ofBits x) from rfl] at this
    rw [this, wordE_im]

/-- On the ball, the decoding is exact: `K` parts lose nothing. -/
theorem algebraMap_re_lowMsgF (cs : List (ℕ × ℕ × Word)) (U : Tup E2 (0 + 6))
    (hU : DegLE (2 ^ 19 - 1 + 6) U)
    (hag : 1053300 - 6 ≤ (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 cs)).card)
    (u : Fin (0 + 6) → Bool) (c : Fin 19 → Bool) :
    algebraMap K E2 (lowMsgF 19 (U u) c).re = lowMsgF 19 (U u) c := by
  obtain ⟨Q, hQ⟩ := Polynomial.mem_lifts _ |>.mp (lane_lifts cs U hU hag u)
  rw [← hQ, lowMsgF_map (by norm_num)]
  rfl

/-- The stack index of a lane and a message point. -/
noncomputable def idx18 : (Fin (0 + 6) → Bool) × (Fin 19 → Bool) ≃ Fin (2 ^ 25) :=
  (Equiv.prodComm _ _).trans <| (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans <|
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).trans (bitsEquiv 25)

theorem testBit_idx18 (p : (Fin (0 + 6) → Bool) × (Fin 19 → Bool)) (i : Fin 25) :
    (idx18 p : ℕ).testBit i = Fin.append p.2 p.1 i := by
  rw [← bitsEquiv_symm_apply]
  simp only [idx18, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.arrowCongr_apply,
    Equiv.refl_apply, Function.comp_apply, Equiv.prodComm_apply, Prod.swap]
  obtain ⟨u, c⟩ := p
  refine Fin.addCases (m := 19) (n := 6) (fun a ↦ ?_) (fun b ↦ ?_) i
  · simp only [Fin.append_left]
    exact congrArg (Sum.elim c u) (finSumFinEquiv_symm_apply_castAdd a)
  · simp only [Fin.append_right]
    exact congrArg (Sum.elim c u) (finSumFinEquiv_symm_apply_natAdd b)

theorem boolPt_eq (μ x : ℕ) :
    boolPt μ x = List.ofFn fun i : Fin μ ↦ (if x.testBit i then (1 : E2) else 0) :=
  List.ext_getElem (by simp [boolPt]) fun i h1 h2 ↦ by simp [boolPt]

theorem boolPt_idx18 (p : (Fin (0 + 6) → Bool) × (Fin 19 → Bool)) :
    boolPt 25 (idx18 p) = bl p.2 ++ bl p.1 := by
  rw [boolPt_eq, bl, bl, ← List.ofFn_fin_append]
  congr 1
  funext i
  rw [testBit_idx18]
  refine Fin.addCases (m := 19) (n := 6) (fun a ↦ ?_) (fun b ↦ ?_) i <;>
    simp [Fin.append_left, Fin.append_right]

theorem dec18_idx18 (U : Tup E2 (0 + 6)) (p : (Fin (0 + 6) → Bool) × (Fin 19 → Bool)) :
    dec18 U (idx18 p) = (lowMsgF 19 (U p.1) p.2).re := by
  have e1 : (fun i : Fin (0 + 6) ↦ (idx18 p : ℕ).testBit (19 + i)) = p.1 := by
    funext i
    have := testBit_idx18 p (Fin.natAdd 19 i)
    rwa [Fin.val_natAdd, Fin.append_right] at this
  have e2 : (fun i : Fin 19 ↦ (idx18 p : ℕ).testBit i) = p.2 := by
    funext i
    have := testBit_idx18 p (Fin.castAdd 6 i)
    rwa [Fin.val_castAdd, Fin.append_left] at this
  show (lowMsgF 19 (U fun i ↦ (idx18 p : ℕ).testBit (19 + i)) fun i ↦ (idx18 p : ℕ).testBit i).re = _
  rw [e1, e2]

theorem den_w₀ (cl : StackClaim6) (U : Tup E2 (0 + 6)) :
    WtE.den (w₀ cl) U = ∑ u : Fin (0 + 6) → Bool, ∑ c : Fin 19 → Bool,
      cl.1 ((bl u ++ bl c).drop 6 ++ (bl u ++ bl c).take 6) * lowMsgF 19 (U u) c := by
  show denE (m := 0 + 6) 19 (w₀ cl).2 U = _
  simp only [denE, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  have hp : pad25 (bl u ++ bl c) = bl u ++ bl c :=
    List.ext_getElem (by simp [pad25, bl]) fun i h1 h2 ↦ by
      simp only [pad25, List.getElem_ofFn]
      rw [List.getD_eq_getElem _ _ h2]
  simp only [w₀, hp]

/-- **On the ball the weight `w₀ cl` is the claim**: `den (w₀ cl) U = cl.2 → cl.Holds 25 (dec U)`. -/
theorem hhold18 (cl : StackClaim6) (cs : List (ℕ × ℕ × Word)) (U : Tup E2 (0 + 6))
    (hU : DegLE (2 ^ 19 - 1 + 6) U)
    (hag : 1053300 - 6 ≤ (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 cs)).card)
    (hW : WtE.den (w₀ cl) U = cl.2) : cl.Holds 25 (dec18 U) := by
  unfold StackClaim6.Holds
  rw [← hW, den_w₀, ← idx18.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  have hlen : (bl u).length = 6 := by simp [bl]
  rw [boolPt_idx18, dec18_idx18, algebraMap_re_lowMsgF cs U hU hag u c,
    List.drop_left' hlen, List.take_left' hlen]

/-- **The deployed opening in S's `stackedSpec` form** (CAND decision, `I.ball := ball18`): from one
commitment and no stack of the level-0 ball satisfying the claim, rejection at `εI`, for a claim
whose weight is affine in each of its 25 variables (in `w₀`'s order). -/
theorem openSpec18 (cl : StackClaim6) (hma : MA 25 (w₀ cl).2) :
    Nonempty (Spec (whirP18 cl)
      (fun h ↦ (commits h).length = 1 ∧ Doomed ball18 (fun q ↦ cl.Holds 25 q) h)
      (fun b _ ↦ b = false) Lvm6.εI 0 0) :=
  openSpecL lad18 (1053300 - 6) lad18_ok dec18 (fun q ↦ cl.Holds 25 q) (w₀ cl) cl.2 ⟨rfl, hma⟩
    fun cs U hU hag hW ↦ hhold18 cl cs U hU hag hW

end Lvm6.Whir
