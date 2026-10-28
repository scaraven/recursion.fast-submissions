-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `rsWeight` at the 4.1 node layouts;
-- stage S-T2).
import FRVerifierImplOps
import FRKindWeight4

/-!
# `rsWeight` at a revision 4.1 node (`kf4`), fast

3.x's `rsWeightS` weights claim 2 by 3.x's node layout (`KW.kwS`), and its fast path `wEvalKF` is
built for 3.x's 23 coordinates. A 4.1 node `ν`'s claims have `7 + nbN ν` coordinates (24 for
`N2`, 25 for `N4`/`N8`), and its kind factor is `N4c.kf4 ν` over `nodeLayout4 ν`.

* **Specification** `rsWeightS4 ν`: `rsWeightS` with claim 2's stage weight `kwSL4 ν` (`eq` on the
  7 high coordinates times `KW4.kwS4 ν` on the `|ρ| − 7` block coordinates).
* **Implementation** `rsWeightF4 ν`: a claim point in `F` runs `wEvalKF4` (claim 2: the 4.1
  skeleton `KW4.skel4 ν n`, cached for `n = nbN ν` as `skelN2`/`skelN4`/`skelN8`; per stage one
  `smulF` per block and one Horner sum) or 3.x's `wEvalCF`; otherwise `wEvalKC4` (the same
  skeleton in `K`) or `wEvalC`.
* **`rsWeightF4_meets`**: `rsWeightF4 ν = rsWeightS4 ν` for every input with `|r″| = 7`.
* **`withRS4`/`withRS4_meets`**: an `OpImpl` with `rsWeight := rsWeightF4 ν` meets its spec with
  `rsWeight := rsWeightS4 ν` whenever the base does (the wiring for `implN4`'s `base ν`).
-/

namespace FR
namespace Impl
open Finset RecursionFast Rev4

/-! ## Specification -/

/-- Claim 2's weight at one Frobenius stage at a 4.1 node `ν`: `eq(q_hi, ρ_hi)` on the 7 high
coordinates times `KW4.kwS4 ν` on the `|ρ| − 7` block coordinates. -/
def kwSL4 (ν : NodeKind) (β : F) (q ρ : List K) : K :=
  eqPts (q.take 7) (ρ.take 7) *
    KW4.kwS4 ν (ρ.length - 7) β (ptOf (ρ.length - 7) (q.drop 7)) (ptOf (ρ.length - 7) (ρ.drop 7))

/-- **`rsWeight`'s specification at a 4.1 node `ν`**: `rsWeightS` with claim 2 (index 1) weighted
by `ν`'s kind factor `kf4` at `β^(2^k)`. -/
def rsWeightS4 (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 * ∑ k ∈ range 128,
    K.ofF ((phiTable r.toList).getD k 0) *
      (if p.2 = 1 then kwSL4 ν (sqIter k β) (p.1.toList.map (sqIter k)) ρ.toList
       else eqPts (p.1.toList.map (sqIter k)) ρ.toList)).sum

/-! ## Implementation -/

/-- The skeletons at the node kinds' block bits (closed constants, computed once). -/
def skelN2 : List (List (List (ℕ × Bool) × List ℕ)) := KW4.skel4 .N2 17
def skelN4 : List (List (List (ℕ × Bool) × List ℕ)) := KW4.skel4 .N4 18
def skelN8 : List (List (List (ℕ × Bool) × List ℕ)) := KW4.skel4 .N8 18

/-- `KW4.skel4 ν n`, from the cache at the kind's block bits. -/
def skelAt (ν : NodeKind) (n : ℕ) : List (List (List (ℕ × Bool) × List ℕ)) :=
  match ν with
  | .N2 => if n = 17 then skelN2 else KW4.skel4 .N2 n
  | .N4 => if n = 18 then skelN4 else KW4.skel4 .N4 n
  | .N8 => if n = 18 then skelN8 else KW4.skel4 .N8 n

theorem skelAt_eq (ν : NodeKind) (n : ℕ) : skelAt ν n = KW4.skel4 ν n := by
  cases ν <;> simp only [skelAt] <;> split_ifs with h <;> first | rfl | (subst h; rfl)

/-- One stage of `wEvalKF4`: add `c_k eq(q_hi, ρ_hi) T_k` (`T_k` the Horner sum over the levels),
then square the point and the blocks' `F` factors. -/
def kfStep4 (c : Array K) (ρh : List K) (oρ : Array K) (k : ℕ)
    (st : K × Array F × List (List (F × K))) : K × Array F × List (List (F × K)) :=
  let q := st.2.1
  let s : ℕ → K := fun l => K.ofF (q.getD (7 + l) 0) + oρ.getD l 0
  (st.1 + c.getD k 0 * (eqPtsC ((q.toList.take 7).map K.ofF) ρh *
      KW.hornerK s 0 (st.2.2.map KW.gsum)),
    q.map F.sq, KW.sqG st.2.2)

/-- **Claim 2's stage fold at a 4.1 node, fast** (`wEvalKF4_eq`): the claim point `r` in `F`. -/
def wEvalKF4 (ν : NodeKind) (c : Array K) (β : F) (r : Array F) (ρ : List K) : K :=
  let ρb := (ρ.drop 7).toArray
  let gK : ℕ → Bool → K := fun l b => if b then ρb.getD l 0 else 1 - ρb.getD l 0
  let fF : ℕ → Bool → F := fun l b => if b then r.getD (7 + l) 0 else 1 - r.getD (7 + l) 0
  (Nat.fold c.size (fun k _ => kfStep4 c (ρ.take 7) (ρb.map (1 + ·)) k)
    (0, r, (skelAt ν (ρ.length - 7)).map (KW.mkEnt (β ^ ·) fF gK))).1

/-- Claim 2's stage weight in `K` from the skeleton (any claim point). -/
def kwSL4I (ν : NodeKind) (β : F) (q ρ : List K) : K :=
  let qa := (q.drop 7).toArray
  let ρa := (ρ.drop 7).toArray
  let e := KW.ew (fun l => qa.getD l 0) (fun l => ρa.getD l 0)
  eqPtsC (q.take 7) (ρ.take 7) * KW4.kwKS (skelAt ν (ρ.length - 7)) β e fun l => e l false + e l true

/-- Claim 2's stage sum in `K` (a claim point outside `F`). -/
def wEvalKC4 (ν : NodeKind) (c : Array K) (β : F) (r ρ : List K) : K :=
  ((List.range c.size).map fun k => c.getD k 0 * kwSL4I ν (sqIter k β) (r.map (sqIter k)) ρ).sum

/-- **`rsWeight` at a 4.1 node, fast** (`rsWeightF4_meets`): a claim point in `F` runs `wEvalKF4`
(claim 2) or `wEvalCF`; otherwise `wEvalKC4` or `wEvalC`. -/
def rsWeightF4 (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 *
    (if p.1.all (·.f₁ == 0) then
      (if p.2 = 1 then wEvalKF4 ν c β (p.1.map (·.f₀)) ρ.toList
       else wEvalCF c (p.1.map (·.f₀)) ρ.toList)
     else
      (if p.2 = 1 then wEvalKC4 ν c β p.1.toList ρ.toList else wEvalC c p.1.toList ρ.toList))).sum

/-! ## Proofs -/

/-- The fast fold's invariant (`kf_fold` over any skeleton). -/
theorem kf_fold4 (c : Array K) (ρh : List K) (oρ : Array K) (β : F) (r : Array F)
    (gK : ℕ → Bool → K) (sk : List (List (List (ℕ × Bool) × List ℕ))) : ∀ n,
    Nat.fold n (fun k _ => kfStep4 c ρh oρ k) (0, r, gmK sk β r gK 0) =
    (∑ k ∈ range n, c.getD k 0 * (eqPtsC (((r.map (sqIter k)).toList.take 7).map K.ofF) ρh *
        KW.hornerK (fun l => K.ofF ((r.map (sqIter k)).getD (7 + l) 0) + oρ.getD l 0) 0
            ((gmK sk β r gK k).map KW.gsum)),
      r.map (sqIter n), gmK sk β r gK n)
  | 0 => by simp [sqIter]
  | n + 1 => by
    rw [Nat.fold_succ, kf_fold4 c ρh oρ β r gK sk n, kfStep4]
    simp only [sum_range_succ, sqG_gmK, Array.map_map, Function.comp_def, F.sq_eq_mul,
      ← sqIter_succ']

theorem getD_map_zero {α : Type*} [Zero α] (A : Array α) (f : α → α) (hf : f 0 = 0) (i : ℕ) :
    (A.map f).getD i 0 = f (A.getD i 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[i]? <;> simp [hf]

theorem ptOf_drop (n : ℕ) (L : List K) : ptOf n (L.drop 7) = fun l : Fin n => L.getD (7 + l) 0 := by
  funext l
  simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **`wEvalKF4` meets claim 2's stage sum** at a point in `F` (any sizes). -/
theorem wEvalKF4_eq (ν : NodeKind) (c : Array K) (β : F) (r : Array F) (ρ : List K) :
    wEvalKF4 ν c β r ρ = ∑ k ∈ range c.size,
      c.getD k 0 * kwSL4 ν (sqIter k β) ((r.toList.map K.ofF).map (sqIter k)) ρ := by
  unfold wEvalKF4
  rw [skelAt_eq]
  refine (congrArg Prod.fst (kf_fold4 c (ρ.take 7) ((ρ.drop 7).toArray.map (1 + ·)) β r
    (fun l b => if b then (ρ.drop 7).toArray.getD l 0 else 1 - (ρ.drop 7).toArray.getD l 0)
      (KW4.skel4 ν (ρ.length - 7)) c.size)).trans ?_
  dsimp only
  refine sum_congr rfl fun k _ => congrArg _ ?_
  rw [kwSL4, eqPtsC_eq]
  congr 1
  · simp [Array.toList_map, List.map_take, List.map_map, Function.comp_def, sqIter_ofF]
  · have hq : ptOf (ρ.length - 7) (((r.toList.map K.ofF).map (sqIter k)).drop 7) =
        fun l : Fin (ρ.length - 7) => K.ofF (sqIter k (r.getD (7 + l) 0)) := by
      rw [ptOf_drop]
      funext l
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
        Array.getElem?_toList]
      cases r[7 + l.val]? <;> simp [sqIter_ofF, sqIter_zeroF, KW4.ofF_zero']
    have hρ' : ptOf (ρ.length - 7) (ρ.drop 7) =
        fun l : Fin (ρ.length - 7) => (ρ.drop 7).toArray.getD l 0 := by
      funext l; simp only [ptOf, toArray_getD_list]
    rw [hq, hρ', gmK, List.map_map]
    refine (KW4.kwS4_fast ν _ _ (fun l => sqIter k (r.getD (7 + l) 0)) _ _ fun l hl => ?_).symm
    have hb : ((ρ.drop 7).toArray).size = ρ.length - 7 := by simp
    rw [getD_map_zero _ _ (sqIter_zeroF k), getD_map_lt _ _ _ (by rw [hb]; exact hl)]

theorem kwSL4I_eq (ν : NodeKind) (β : F) (q ρ : List K) : kwSL4I ν β q ρ = kwSL4 ν β q ρ := by
  unfold kwSL4I kwSL4
  dsimp only
  rw [skelAt_eq, eqPtsC_eq]
  congr 1
  have hq : ptOf (ρ.length - 7) (q.drop 7) =
      fun l : Fin (ρ.length - 7) => (q.drop 7).toArray.getD l 0 := by
    funext l; simp only [ptOf, toArray_getD_list]
  have hρ' : ptOf (ρ.length - 7) (ρ.drop 7) =
      fun l : Fin (ρ.length - 7) => (ρ.drop 7).toArray.getD l 0 := by
    funext l; simp only [ptOf, toArray_getD_list]
  rw [hq, hρ']
  exact (KW4.kwS4_eq ν _ β _ _ _ fun _ _ => rfl).symm

/-- **`rsWeightF4` meets `rsWeightS4`** (`r″` of 7 coordinates, any claims and `ρ`). -/
theorem rsWeightF4_meets (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F)
    (ρ : Array K) (hr : r.size = 7) : rsWeightF4 ν r ps κ β ρ = rsWeightS4 ν r ps κ β ρ := by
  unfold rsWeightF4 rsWeightS4
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  have hc : ((phiTable r.toList).map K.ofF).size = 128 := by
    rw [Array.size_map, phiTable_size, Array.length_toList, hr]; norm_num
  have hg : ∀ k, ((phiTable r.toList).map K.ofF).getD k 0 = K.ofF ((phiTable r.toList).getD k 0) :=
    fun k => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases (phiTable r.toList)[k]? <;> rfl
  split_ifs with hF h1 h1
  · rw [wEvalKF4_eq, ofF_f0 _ hF, hc]
    exact sum_congr rfl fun k _ => by rw [hg]
  · rw [wEvalCF_eq, ofF_f0 _ hF, wEvalC_eq, hc]
    exact sum_congr rfl fun k _ => by rw [hg]
  · rw [wEvalKC4, KW.lsum_range, hc]
    exact sum_congr rfl fun k _ => by rw [hg, kwSL4I_eq]
  · rw [wEvalC_eq, hc]
    exact sum_congr rfl fun k _ => by rw [hg]

/-! ## Wiring -/

/-- An `OpImpl` with `rsWeight` at the 4.1 node `ν` (for `implN4`'s `base ν`). -/
def withRS4 (base : OpImpl) (ν : NodeKind) : OpImpl := { base with rsWeight := rsWeightF4 ν }

/-- Its specification. -/
def withRS4S (spec : OpSpec) (ν : NodeKind) : OpSpec := { spec with rsWeight := rsWeightS4 ν }

/-- **`withRS4` keeps `Meets`**, with `rsWeight`'s spec the 4.1 one. -/
theorem withRS4_meets {base : OpImpl} {spec : OpSpec} (ν : NodeKind) (h : base.Meets spec) :
    (withRS4 base ν).Meets (withRS4S spec ν) := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, fun r ps k b p hr _ => rsWeightF4_meets ν r ps k b p hr, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17⟩

/-! ## Controls -/

/-- (+) The cache is the kind's skeleton at its block bits: `N4` at 18 reads `skelN4`. -/
theorem skelAt_pos : skelAt .N4 18 = skelN4 := rfl

/-- (−) … and at other sizes the skeleton is built on the call (the cache is not read). -/
theorem skelAt_neg : skelAt .N4 17 = KW4.skel4 .N4 17 := rfl

end Impl
end FR
