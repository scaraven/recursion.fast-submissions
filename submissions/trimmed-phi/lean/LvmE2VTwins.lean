-- New for lvm2 S1 (E2-F, E2F-V): the fast twins of the `E2` front for V_S's refinement at S2GF: the generic
-- front algebra (`LvmE2VBase`, `LvmE2VProg`, `LvmE2VProgKS`) commutes with ring homomorphisms (and with
-- `K`-compatible ones where `K` enters), hence V_S's `FE2` runs compute the spec's `E2` values through
-- `toE2`; V_S's word-level twins (`LvmDecideE2`) against `LvmE2VSwitch`'s and `LvmE2VMid`'s definitions.
import LvmDecideE2
import LvmVEqArith

/-!
# The fast twins of the `E2` front

1. **Transport** (generic): for `f : F →+* G`, `f (sumF l) = sumF (l.map f)` and its kind for every
   list and multilinear function of `LvmE2VBase`, the round algebra and wiring kernels of `LvmE2VProg`,
   `contShiftF` and `selXF`; `firstWeightsF` and `firstClaimSF` (where `K` enters by `algebraMap`) for `f`
   with `f (algebraMap K F a) = algebraMap K G a`. A claim maps by `KClaim.map`.
2. **At `FE2`**: `toE2` (as `toE2Hom`) is such a map (`toE2_algebraMap`); the instances `toE2_*`,
   `map_toE2_*`; V_S's `wireTargetD` at the digest's bits is `wireTargetF` (`wireTargetD_digestBits`).
3. **Word level** (`LvmDecideE2` against `LvmE2VSwitch`/`LvmE2VMid`): `bitFE2_eq`, `toBF64_rowWordD`,
   `toE2_basisFE2`, `tensorWD_twin` (`FE → E3` by `FE.toExt3`), `wordWD_twin` and `sumW6D_twin` (`FE6 → E6` by
   `FE6.toE6`), `splitD_twin` (`BlockTwin`: same block, weights and values through `toExt3`; parts by `partE`),
   `BlockTwin.onStack`; `sBitsD_digestLanes` (V_S's digest bits of the `digestLanes` packing are `digestBits`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters

/-! ## 1. Transport along a ring homomorphism -/

section Generic

variable {F G : Type} [Field F] [Field G] (f : F →+* G)

theorem map_foldl_add (l : List F) (a : F) : f (l.foldl (· + ·) a) = (l.map f).foldl (· + ·) (f a) := by
  rw [List.foldl_map]
  exact (List.foldl_hom f (fun x y ↦ (map_add f x y).symm)).symm

theorem map_foldl_mul (l : List F) (a : F) : f (l.foldl (· * ·) a) = (l.map f).foldl (· * ·) (f a) := by
  rw [List.foldl_map]
  exact (List.foldl_hom f (fun x y ↦ (map_mul f x y).symm)).symm

theorem map_getD (l : List F) (n : ℕ) : f (l.getD n 0) = (l.map f).getD n 0 := by
  rw [← map_zero f, List.getD_map]

theorem map_headD (l : List F) : f (l.headD 0) = (l.map f).headD 0 := by
  cases l <;> simp

theorem map_sumF (l : List F) : f (sumF l) = sumF (l.map f) := by
  rw [sumF, sumF, map_foldl_add, map_zero]

theorem map_prodF (l : List F) : f (prodF l) = prodF (l.map f) := by
  rw [prodF, prodF, map_foldl_mul, map_one]

theorem map_dotF (a b : List F) : f (dotF a b) = dotF (a.map f) (b.map f) := by
  rw [dotF, dotF, map_foldl_add, map_zero, Lvm.VEq.map_zipWith_of (map_mul f)]

theorem map_powersFromF (acc base : F) (n : ℕ) :
    (powersFromF acc base n).map f = powersFromF (f acc) (f base) n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => rw [powersFromF, powersFromF, List.map_cons, ih, map_mul]

theorem map_powersF (base : F) (n : ℕ) : (powersF base n).map f = powersF (f base) n := by
  rw [powersF, powersF, map_powersFromF, map_one]

theorem map_polyEvalF (cs : List F) (x : F) : f (polyEvalF cs x) = polyEvalF (cs.map f) (f x) := by
  unfold polyEvalF
  induction cs with
  | nil => exact map_zero f
  | cons c cs ih => rw [List.foldr_cons, List.map_cons, List.foldr_cons, map_add, map_mul, ih]

theorem map_eqKernelF (p : List F) : (eqKernelF p).map f = eqKernelF (p.map f) := by
  unfold eqKernelF
  suffices h : ∀ out : List F, (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).map f =
      (p.map f).foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) (out.map f) from
      (h [1]).trans (by rw [List.map_singleton, map_one])
  induction p with
  | nil => intro out; rfl
  | cons r p ih =>
    intro out
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
    simp only [List.map_append, List.map_map, Function.comp_def, map_mul, map_add, map_one]

theorem map_foldPairsF (r : F) : ∀ l : List F, (foldPairsF r l).map f = foldPairsF (f r) (l.map f)
  | a :: b :: rest => by
    simp only [foldPairsF, List.map_cons, map_foldPairsF r rest, map_add, map_mul, map_one]
  | [_] => rfl
  | [] => rfl

theorem map_multilinearEvalF (mle point : List F) :
    f (multilinearEvalF mle point) = multilinearEvalF (mle.map f) (point.map f) := by
  unfold multilinearEvalF
  rw [map_headD]
  congr 1
  induction point generalizing mle with
  | nil => rfl
  | cons r point ih => rw [List.foldl_cons, ih, map_foldPairsF, List.map_cons, List.foldl_cons]

theorem map_eqEvalF (a b : List F) : f (eqEvalF a b) = eqEvalF (a.map f) (b.map f) := by
  unfold eqEvalF
  rw [map_foldl_mul, map_one, Lvm.VEq.map_zipWith_of (g' := fun x z ↦ 1 + x + z)]
  intro x y
  rw [map_add, map_add, map_one]

theorem map_eqAtF : ∀ (p : List F) (w : ℕ), f (eqAtF p w) = eqAtF (p.map f) w
  | [], _ => map_one f
  | r :: rs, w => by
    rw [eqAtF, List.map_cons, eqAtF, map_mul, map_eqAtF rs, apply_ite f, map_add, map_one]

theorem map_selPtF (s n : ℕ) : (selPtF s n).map f = selPtF s n := by
  unfold selPtF
  rw [List.map_map]
  exact List.map_congr_left fun b _ ↦ by simp only [Function.comp_apply, apply_ite f, map_one, map_zero]

end Generic

/-! ### Arrays -/

theorem arr_map_getD {α β : Type} [Zero α] [Zero β] (h : α → β) (h0 : h 0 = 0) (A : Array α) (i : ℕ) :
    h (A.getD i 0) = (A.map h).getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[i]? <;> simp [h0]

theorem list_map_modify {α β : Type} (h : α → β) (g : α → α) (g' : β → β) (hg : ∀ x, h (g x) = g' (h x)) :
    ∀ (l : List α) (i : ℕ), (l.modify i g).map h = (l.map h).modify i g' := by
  intro l i
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_modify]
    split <;> simp [hg]

theorem arr_map_modify {α β : Type} (h : α → β) (g : α → α) (g' : β → β) (hg : ∀ x, h (g x) = g' (h x))
    (A : Array α) (i : ℕ) : (A.modify i g).map h = (A.map h).modify i g' := by
  apply Array.ext'
  rw [Array.toList_map, Array.toList_modify, Array.toList_modify, Array.toList_map,
    list_map_modify h g g' hg]

/-- A `setIfInBounds` loop commutes with a map of the entries. -/
theorem arr_map_foldl_set1 {α β : Type} (h : α → β) (B : List ℕ) (idx : ℕ → ℕ) (val : ℕ → α)
    (val' : ℕ → β) (hv : ∀ b, h (val b) = val' b) (g0 : Array α) :
    (B.foldl (fun g b ↦ g.setIfInBounds (idx b) (val b)) g0).map h =
      B.foldl (fun g b ↦ g.setIfInBounds (idx b) (val' b)) (g0.map h) := by
  induction B generalizing g0 with
  | nil => rfl
  | cons b B ihB => rw [List.foldl_cons, ihB, List.foldl_cons, Array.map_setIfInBounds, hv]

/-- Two nested `setIfInBounds` loops commute with a map of the entries. -/
theorem arr_map_foldl_set {α β : Type} (h : α → β) (A B : List ℕ) (idx : ℕ → ℕ → ℕ) (val : ℕ → ℕ → α)
    (val' : ℕ → ℕ → β) (hv : ∀ a b, h (val a b) = val' a b) (g0 : Array α) :
    (A.foldl (fun g a ↦ B.foldl (fun g b ↦ g.setIfInBounds (idx a b) (val a b)) g) g0).map h =
      A.foldl (fun g a ↦ B.foldl (fun g b ↦ g.setIfInBounds (idx a b) (val' a b)) g) (g0.map h) := by
  induction A generalizing g0 with
  | nil => rfl
  | cons a A ih => rw [List.foldl_cons, ih, List.foldl_cons, arr_map_foldl_set1 h B _ _ _ (hv a)]

/-- A row-update loop commutes with a map of the entries. -/
theorem arr_map_foldl_modify1 {α β : Type} (h : α → β) (B : List ℕ) (idx pos : ℕ → ℕ)
    (val : ℕ → α) (val' : ℕ → β) (hv : ∀ b, h (val b) = val' b) (R0 : Array (Array α)) :
    (B.foldl (fun rows b ↦ rows.modify (idx b) fun row ↦ row.setIfInBounds (pos b) (val b)) R0).map
        (Array.map h) =
      B.foldl (fun rows b ↦ rows.modify (idx b) fun row ↦ row.setIfInBounds (pos b) (val' b))
        (R0.map (Array.map h)) := by
  induction B generalizing R0 with
  | nil => rfl
  | cons b B ihB =>
    rw [List.foldl_cons, ihB, List.foldl_cons,
      arr_map_modify _ _ (fun row ↦ row.setIfInBounds (pos b) (val' b)) (fun row ↦ by
        rw [Array.map_setIfInBounds, hv])]

/-- Two nested row-update loops commute with a map of the entries. -/
theorem arr_map_foldl_modify {α β : Type} (h : α → β) (A B : List ℕ) (idx pos : ℕ → ℕ → ℕ)
    (val : ℕ → ℕ → α) (val' : ℕ → ℕ → β) (hv : ∀ a b, h (val a b) = val' a b) (R0 : Array (Array α)) :
    (A.foldl (fun rows a ↦ B.foldl (fun rows b ↦
        rows.modify (idx a b) fun row ↦ row.setIfInBounds (pos a b) (val a b)) rows) R0).map (Array.map h) =
      A.foldl (fun rows a ↦ B.foldl (fun rows b ↦
        rows.modify (idx a b) fun row ↦ row.setIfInBounds (pos a b) (val' a b)) rows) (R0.map (Array.map h)) := by
  induction A generalizing R0 with
  | nil => rfl
  | cons a A ih => rw [List.foldl_cons, ih, List.foldl_cons, arr_map_foldl_modify1 h B _ _ _ _ (hv a)]

/-! ### The round algebra (`LvmE2VProg`) -/

/-- A claim, mapped coordinatewise. -/
def KClaim.map {F G : Type} [Field F] [Field G] (f : F →+* G) (c : KClaim F) : KClaim G :=
  ⟨f c.value, c.mu.map f, c.point.map f, c.weights.map f⟩

section Alg

open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

variable {F G : Type} [Field F] [Field G] (f : F →+* G)

theorem map_instWeightsF (s : F) : (instWeightsF s).map f = instWeightsF (f s) := by
  unfold instWeightsF
  rw [List.map_map]
  refine List.map_congr_left fun e _ ↦ ?_
  rw [Function.comp_apply, map_sumF, List.map_filterMap, ← map_powersF f]
  congr 1
  refine List.filterMap_congr fun b _ ↦ ?_
  split
  · rw [Option.map_some, map_getD]
  · rfl

private def ltG (w : Array F) : Array F :=
  (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)

private def ltCols (g : Array F) : Array F :=
  ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    sumF ((List.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)).toArray

private def ltOut (g columns : Array F) : List F :=
  (List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

private theorem linearTransposeF_eq (w : List F) :
    linearTransposeF w = ltOut (ltG w.toArray) (ltCols (ltG w.toArray)) := rfl

private theorem map_ltG (w : Array F) : (ltG w).map f = ltG (w.map f) := by
  unfold ltG
  rw [arr_map_foldl_set f _ _ _ _ _ (fun _ _ ↦ arr_map_getD f (map_zero f) _ _), Array.map_replicate, map_zero]

private theorem map_ltCols (g : Array F) : (ltCols g).map f = ltCols (g.map f) := by
  unfold ltCols
  rw [List.map_toArray, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun x _ ↦ ?_
  rw [List.map_map]
  refine List.map_congr_left fun z _ ↦ ?_
  rw [Function.comp_apply, map_sumF, List.map_map]
  congr 1
  exact List.map_congr_left fun y _ ↦ arr_map_getD f (map_zero f) _ _

private theorem map_ltOut (g c : Array F) : (ltOut g c).map f = ltOut (g.map f) (c.map f) := by
  unfold ltOut
  rw [List.map_flatMap]
  refine List.flatMap_congr fun lane _ ↦ ?_
  rw [List.map_map]
  refine List.map_congr_left fun z _ ↦ ?_
  rw [Function.comp_apply, map_add, map_add, arr_map_getD f (map_zero f), arr_map_getD f (map_zero f),
    arr_map_getD f (map_zero f)]

theorem map_linearTransposeF (w : List F) : (linearTransposeF w).map f = linearTransposeF (w.map f) := by
  rw [linearTransposeF_eq, linearTransposeF_eq, map_ltOut, map_ltCols, map_ltG, List.map_toArray]

theorem map_projectedF (claim : KClaim F) (product : List F) :
    f (projectedF claim product) = projectedF (claim.map f) (product.map f) := by
  unfold projectedF
  rw [map_sumF, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  rw [Function.comp_apply, map_mul, map_sumF, map_getD, List.map_filterMap]
  congr 2
  change _ = List.filterMap _ (List.zip (claim.mu.map f) rmfeProject)
  rw [← List.map_id rmfeProject, List.zip_map, List.filterMap_map, List.map_id]
  refine List.filterMap_congr fun mm _ ↦ ?_
  split
  simp_all

theorem map_iotaSF (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (claim : KClaim F) :
    f (iotaSF sh logSteps step claim) = iotaSF sh logSteps step (claim.map f) := by
  unfold iotaSF
  rw [map_sumF, List.map_map]
  congr 1
  refine List.map_congr_left fun segment _ ↦ ?_
  simp only [Function.comp_apply, map_mul, map_getD, map_eqKernelF, List.map_drop, map_sumF,
    List.map_filterMap, KClaim.map]
  congr 2
  refine List.filterMap_congr fun z _ ↦ ?_
  split
  · rw [Option.map_some, map_getD]
  · rfl

private def swRows (segments : List F) (weights : Array F) (first count : ℕ) : Array (Array F) :=
  (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))

private theorem slotWeightsF_eq (logSteps : ℕ) (claim : KClaim F) (first count : ℕ) :
    slotWeightsF logSteps claim first count =
      (swRows (eqKernelF (claim.point.drop (logSteps - 4))) claim.weights.toArray first count).toList.map
        Array.toList := rfl

private theorem map_swRows (segments : List F) (weights : Array F) (first count : ℕ) :
    (swRows segments weights first count).map (Array.map f) =
      swRows (segments.map f) (weights.map f) first count := by
  unfold swRows
  rw [arr_map_foldl_modify f _ _ _ _ _ (fun a b ↦ (segments.map f).getD a 0 * (weights.map f).getD b 0)
    (fun a b ↦ by rw [map_mul, map_getD, arr_map_getD f (map_zero f)]), Array.map_replicate,
    Array.map_replicate, map_zero]

theorem map_slotWeightsF (logSteps : ℕ) (claim : KClaim F) (first count : ℕ) :
    (slotWeightsF logSteps claim first count).map (List.map f) =
      slotWeightsF logSteps (claim.map f) first count := by
  rw [slotWeightsF_eq, slotWeightsF_eq]
  change _ = (swRows (eqKernelF ((claim.point.map f).drop (logSteps - 4))) (claim.weights.map f).toArray
    first count).toList.map Array.toList
  rw [← List.map_drop, ← map_eqKernelF, ← List.map_toArray, ← map_swRows, Array.toList_map, List.map_map,
    List.map_map]
  exact List.map_congr_left fun row _ ↦ (Array.toList_map ..).symm

theorem map_foldRowsF (slot : List F) (rows : List (List F)) :
    (foldRowsF slot rows).map f = foldRowsF (slot.map f) (rows.map (List.map f)) := by
  unfold foldRowsF
  have hd : ∀ l : List (List F), (l.headD []).map f = (l.map (List.map f)).headD [] := by
    intro l; cases l <;> rfl
  rw [hd]
  congr 1
  induction slot generalizing rows with
  | nil => rfl
  | cons c slot ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
    congr 1
    rw [List.map_map, List.length_map]
    refine List.map_congr_left fun i _ ↦ ?_
    rw [Function.comp_apply, Lvm.VEq.map_zipWith_of (g' := fun lo hi ↦ lo + f c * (lo + hi))
      (fun x y ↦ by rw [map_add, map_mul, map_add])]
    congr 1 <;> rw [← List.map_nil (f := f), List.getD_map]

/-! ### The wiring kernels -/

theorem map_iotaF (ρ μ : List F) (i : ℕ) : f (iotaF ρ μ i) = iotaF (ρ.map f) (μ.map f) i := by
  rw [iotaF, iotaF, map_mul, map_eqAtF, map_getD]

theorem map_eqBitF (a : F) (b : Bool) : f (eqBitF a b) = eqBitF (f a) b := by
  cases b <;> simp [eqBitF]

/-- The automaton's vector, mapped. -/
def MS4F.map (q : MS4F F) : MS4F G := ⟨f q.v00, f q.v01, f q.v10, f q.v11⟩

theorem map_MS4F_get (q : MS4F F) (c s : Bool) : f (q.get c s) = (MS4F.map f q).get c s := by
  cases c <;> cases s <;> rfl

theorem map_msStepF (a r : F) (tb : Bool) (q : MS4F F) :
    MS4F.map f (msStepF a r tb q) = msStepF (f a) (f r) tb (MS4F.map f q) := by
  simp only [msStepF, MS4F.map, map_add, map_mul, map_one, map_eqBitF, map_MS4F_get]

theorem map_msTailF : ∀ (σ ρ : List F) (t : ℕ),
    MS4F.map f (msTailF σ ρ t) = msTailF (σ.map f) (ρ.map f) t
  | a :: σ, r :: ρ, t => by
    rw [msTailF, map_msStepF, map_msTailF σ ρ, List.map_cons, List.map_cons, msTailF]
  | [], _, t => by
    simp [msTailF, MS4F.map, apply_ite f]
  | _ :: _, [], t => by
    simp [msTailF, MS4F.map, apply_ite f]

theorem map_msEvalF (ρ μ σ : List F) (base t : ℕ) :
    f (msEvalF ρ μ σ base t) = msEvalF (ρ.map f) (μ.map f) (σ.map f) base t := by
  unfold msEvalF
  rw [map_mul, map_eqAtF, List.map_drop, List.length_map, map_sumF, List.map_map]
  congr 2
  refine List.map_congr_left fun d _ ↦ ?_
  rw [Function.comp_apply, map_mul, map_mul, map_eqAtF, map_getD, map_MS4F_get, map_msTailF, List.map_take,
    List.map_take, List.map_drop]

theorem map_thrTailF : ∀ (ρ : List F) (t : ℕ), Prod.map f f (thrTailF ρ t) = thrTailF (ρ.map f) t
  | r :: ρ, t => by
    have ih := map_thrTailF ρ (t / 2)
    rw [List.map_cons, thrTailF, thrTailF, ← ih]
    simp only [Prod.map, map_add, map_mul, map_one, apply_ite f]
  | [], t => by
    rw [List.map_nil, thrTailF, thrTailF]
    simp [apply_ite f]

theorem map_thrEvalF (ρ μ : List F) (t : ℕ) : f (thrEvalF ρ μ t) = thrEvalF (ρ.map f) (μ.map f) t := by
  unfold thrEvalF
  rw [map_sumF, List.map_map]
  congr 1
  refine List.map_congr_left fun d _ ↦ ?_
  rw [Function.comp_apply, map_mul, map_getD, ← map_thrTailF, apply_ite f]
  rfl

theorem map_bitF (b : Bool) : f (bitF b) = bitF b := by
  cases b <;> simp [bitF]

theorem map_padDotF (ω : List F) (y : ℕ → Bool) : f (padDotF ω y) = padDotF (ω.map f) y := by
  unfold padDotF
  rw [map_sumF, List.map_map]
  exact congrArg sumF (List.map_congr_left fun j _ ↦ by rw [Function.comp_apply, map_mul, map_getD, map_bitF])

theorem map_wireTargetF (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim F) :
    f (wireTargetF s n claim) = wireTargetF s n (claim.map f) := by
  unfold wireTargetF
  simp only [map_add, map_mul, map_iotaF, map_padDotF, map_thrEvalF]
  rfl

theorem map_slotWF (b : ℕ) (W : ℕ → ℕ → F) (τ : List F) (z : ℕ) :
    f (slotWF b W τ z) = slotWF b (fun o z ↦ f (W o z)) (τ.map f) z := by
  unfold slotWF
  rw [map_sumF, List.map_map]
  congr 1
  refine List.map_congr_left fun o _ ↦ ?_
  rw [Function.comp_apply, map_mul, map_eqAtF]

theorem map_dWF (ω : List F) (l z : ℕ) : f (dWF ω l z) = dWF (ω.map f) l z := by
  rw [dWF, dWF, map_getD]

theorem map_contShiftF (rows : List ℕ) (rho rho' : List F) :
    f (contShiftF rows rho rho') = contShiftF rows (rho.map f) (rho'.map f) := by
  unfold contShiftF
  rw [map_sumF, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  rw [Function.comp_apply, map_mul, map_eqAtF, map_eqAtF]

theorem map_selXF (xl : ℕ) (pt : List F) : f (selXF xl pt) = selXF xl (pt.map f) := by
  rw [selXF, selXF, map_prodF, List.map_drop]

/-! ### Where `K` enters (`algebraMap`) -/

variable [Algebra K F] [Algebra K G]

theorem map_firstWeightsF (hf : ∀ a : K, f (algebraMap K F a) = algebraMap K G a) (lanesPt : List F) :
    (firstWeightsF lanesPt).map f = firstWeightsF (lanesPt.map f) := by
  unfold firstWeightsF
  rw [List.map_map]
  refine List.map_congr_left fun j _ ↦ ?_
  rw [Function.comp_apply, map_mul, map_getD, map_eqKernelF, nF, kF, hf]

theorem map_firstClaimSF (hf : ∀ a : K, f (algebraMap K F a) = algebraMap K G a)
    (sh : LeanVM.Protocol.KeccakGkr.Shape) (inst segment lanesPt output : List F) (committed : F) :
    (firstClaimSF sh inst segment lanesPt output committed).map f =
      firstClaimSF sh (inst.map f) (segment.map f) (lanesPt.map f) (output.map f) (f committed) := by
  simp only [firstClaimSF, KClaim.map, map_add, map_mul, map_getD, map_dotF, map_eqKernelF, List.map_take,
    List.map_append, List.map_drop, map_firstWeightsF f hf]

end Alg

/-! ## 2. At `FE2`: `toE2` -/

section AtFE2

open Lvm.FE2 (toE2)

/-- `toE2` as a ring homomorphism. -/
abbrev toE2Hom : Lvm.FE2 →+* E2 := Lvm.FE2.ringEquivE2.toRingHom

/-- **`toE2` is `K`-compatible**: V_S's `K → FE2` (`ofK ∘ FK.ofBF64`) is the spec's `K → E2` (`Quad.C`). -/
theorem toE2_algebraMap (a : K) : toE2 (algebraMap K Lvm.FE2 a) = algebraMap K E2 a := by
  change toE2 (Lvm.FE2.ofK (FK.ringEquivBF64.symm a)) = _
  rw [Lvm.FE2.toE2_ofK, ← FK.ringEquivBF64_apply, RingEquiv.apply_symm_apply]
  rfl

theorem toE2_sumF (l : List Lvm.FE2) : toE2 (sumF l) = sumF (l.map toE2) := map_sumF toE2Hom l
theorem toE2_prodF (l : List Lvm.FE2) : toE2 (prodF l) = prodF (l.map toE2) := map_prodF toE2Hom l
theorem toE2_dotF (a b : List Lvm.FE2) : toE2 (dotF a b) = dotF (a.map toE2) (b.map toE2) :=
  map_dotF toE2Hom a b
theorem map_toE2_powersF (x : Lvm.FE2) (n : ℕ) : (powersF x n).map toE2 = powersF (toE2 x) n :=
  map_powersF toE2Hom x n
theorem toE2_polyEvalF (cs : List Lvm.FE2) (x : Lvm.FE2) :
    toE2 (polyEvalF cs x) = polyEvalF (cs.map toE2) (toE2 x) := map_polyEvalF toE2Hom cs x
theorem map_toE2_eqKernelF (p : List Lvm.FE2) : (eqKernelF p).map toE2 = eqKernelF (p.map toE2) :=
  map_eqKernelF toE2Hom p
theorem map_toE2_foldPairsF (r : Lvm.FE2) (l : List Lvm.FE2) :
    (foldPairsF r l).map toE2 = foldPairsF (toE2 r) (l.map toE2) := map_foldPairsF toE2Hom r l
theorem toE2_multilinearEvalF (mle point : List Lvm.FE2) :
    toE2 (multilinearEvalF mle point) = multilinearEvalF (mle.map toE2) (point.map toE2) :=
  map_multilinearEvalF toE2Hom mle point
theorem toE2_eqEvalF (a b : List Lvm.FE2) : toE2 (eqEvalF a b) = eqEvalF (a.map toE2) (b.map toE2) :=
  map_eqEvalF toE2Hom a b
theorem toE2_eqAtF (p : List Lvm.FE2) (w : ℕ) : toE2 (eqAtF p w) = eqAtF (p.map toE2) w :=
  map_eqAtF toE2Hom p w
theorem map_toE2_selPtF (s n : ℕ) : (selPtF s n : List Lvm.FE2).map toE2 = selPtF s n :=
  map_selPtF toE2Hom s n
theorem map_toE2_instWeightsF (s : Lvm.FE2) : (instWeightsF s).map toE2 = instWeightsF (toE2 s) :=
  map_instWeightsF toE2Hom s
theorem map_toE2_linearTransposeF (w : List Lvm.FE2) :
    (linearTransposeF w).map toE2 = linearTransposeF (w.map toE2) := map_linearTransposeF toE2Hom w
theorem map_toE2_firstWeightsF (lanesPt : List Lvm.FE2) :
    (firstWeightsF lanesPt).map toE2 = firstWeightsF (lanesPt.map toE2) :=
  map_firstWeightsF toE2Hom toE2_algebraMap lanesPt
theorem toE2_firstClaimSF (sh : LeanVM.Protocol.KeccakGkr.Shape) (inst segment lanesPt output : List Lvm.FE2)
    (committed : Lvm.FE2) :
    (firstClaimSF sh inst segment lanesPt output committed).map toE2Hom =
      firstClaimSF sh (inst.map toE2) (segment.map toE2) (lanesPt.map toE2) (output.map toE2) (toE2 committed) :=
  map_firstClaimSF toE2Hom toE2_algebraMap sh inst segment lanesPt output committed
theorem toE2_projectedF (claim : KClaim Lvm.FE2) (product : List Lvm.FE2) :
    toE2 (projectedF claim product) = projectedF (claim.map toE2Hom) (product.map toE2) :=
  map_projectedF toE2Hom claim product
theorem toE2_iotaSF (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (claim : KClaim Lvm.FE2) :
    toE2 (iotaSF sh logSteps step claim) = iotaSF sh logSteps step (claim.map toE2Hom) :=
  map_iotaSF toE2Hom sh logSteps step claim
theorem map_toE2_slotWeightsF (logSteps : ℕ) (claim : KClaim Lvm.FE2) (first count : ℕ) :
    (slotWeightsF logSteps claim first count).map (List.map toE2) =
      slotWeightsF logSteps (claim.map toE2Hom) first count :=
  map_slotWeightsF toE2Hom logSteps claim first count
theorem map_toE2_foldRowsF (slot : List Lvm.FE2) (rows : List (List Lvm.FE2)) :
    (foldRowsF slot rows).map toE2 = foldRowsF (slot.map toE2) (rows.map (List.map toE2)) :=
  map_foldRowsF toE2Hom slot rows
theorem toE2_iotaF (ρ μ : List Lvm.FE2) (i : ℕ) : toE2 (iotaF ρ μ i) = iotaF (ρ.map toE2) (μ.map toE2) i :=
  map_iotaF toE2Hom ρ μ i
theorem toE2_msEvalF (ρ μ σ : List Lvm.FE2) (base t : ℕ) :
    toE2 (msEvalF ρ μ σ base t) = msEvalF (ρ.map toE2) (μ.map toE2) (σ.map toE2) base t :=
  map_msEvalF toE2Hom ρ μ σ base t
theorem toE2_thrEvalF (ρ μ : List Lvm.FE2) (t : ℕ) :
    toE2 (thrEvalF ρ μ t) = thrEvalF (ρ.map toE2) (μ.map toE2) t := map_thrEvalF toE2Hom ρ μ t
theorem toE2_padDotF (ω : List Lvm.FE2) (y : ℕ → Bool) : toE2 (padDotF ω y) = padDotF (ω.map toE2) y :=
  map_padDotF toE2Hom ω y
theorem toE2_wireTargetF (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim Lvm.FE2) :
    toE2 (wireTargetF s n claim) = wireTargetF s n (claim.map toE2Hom) := map_wireTargetF toE2Hom s n claim
theorem toE2_slotWF (b : ℕ) (W : ℕ → ℕ → Lvm.FE2) (τ : List Lvm.FE2) (z : ℕ) :
    toE2 (slotWF b W τ z) = slotWF b (fun o z ↦ toE2 (W o z)) (τ.map toE2) z := map_slotWF toE2Hom b W τ z
theorem toE2_dWF (ω : List Lvm.FE2) (l z : ℕ) : toE2 (dWF ω l z) = dWF (ω.map toE2) l z :=
  map_dWF toE2Hom ω l z
theorem toE2_contShiftF (rows : List ℕ) (rho rho' : List Lvm.FE2) :
    toE2 (contShiftF rows rho rho') = contShiftF rows (rho.map toE2) (rho'.map toE2) :=
  map_contShiftF toE2Hom rows rho rho'
theorem toE2_selXF (xl : ℕ) (pt : List Lvm.FE2) : toE2 (selXF xl pt) = selXF xl (pt.map toE2) :=
  map_selXF toE2Hom xl pt

/-- V_S's `wireTargetD` at the digest's bits is `wireTargetF`. -/
theorem wireTargetD_digestBits (d : RecursionFast.Digest) (n : ℕ) (claim : KClaim Lvm.FE2) :
    Lvm.wireTargetD (Lvm.KG.digestBits d) n claim = wireTargetF d n claim := rfl

theorem toE2_wireTargetD (d : RecursionFast.Digest) (n : ℕ) (claim : KClaim Lvm.FE2) :
    toE2 (Lvm.wireTargetD (Lvm.KG.digestBits d) n claim) = wireTargetF d n (claim.map toE2Hom) :=
  toE2_wireTargetF d n claim

end AtFE2

/-! ## 3. V_S's word-level twins -/

section Words

open Lvm.FE2 (toE2)

theorem bitFE2_eq (y : Lvm.FE2) (j : ℕ) : Lvm.bitFE2 y j = bitE2 (toE2 y) j := rfl

theorem toBF64_mk_toUInt64 (n : ℕ) : FK.toBF64 ⟨n.toUInt64⟩ = K.ofBits n := rfl

theorem toBF64_rowWordD (sv : List Lvm.FE2) (j : ℕ) :
    FK.toBF64 (Lvm.rowWordD sv j) = rowWord (sv.map toE2) j := by
  rw [Lvm.rowWordD, toBF64_mk_toUInt64, rowWord]
  refine congrArg (fun g ↦ K.ofBits ((List.range 64).foldl g 0)) (funext fun acc ↦ funext fun i ↦ ?_)
  rw [bitFE2_eq, ← Lvm.FE2.toE2_zero, List.getD_map]

theorem toE2_basisFE2 (j : ℕ) : toE2 (Lvm.basisFE2 j) = basisE2 j := by
  unfold Lvm.basisFE2 basisE2
  split
  · rfl
  · rfl

/-! ### The tensor coordinates (`tensorWD`) -/

theorem getD_modify_add (acc : Array FE) (x j : ℕ) (c : FE) (hx : x < acc.size) :
    (acc.modify x (· + c)).getD j 0 = acc.getD j 0 + if x = j then c else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · subst_vars
    rw [Array.getElem?_eq_getElem hx]
    rfl
  · rw [add_zero]

theorem size_foldl_modify (g : FE → FE) :
    ∀ (L : List ℕ) (acc : Array FE), (L.foldl (fun acc j ↦ acc.modify j g) acc).size = acc.size
  | [], _ => rfl
  | x :: L, acc => by rw [List.foldl_cons, size_foldl_modify g L, Array.size_modify]

theorem getD_foldl_modify_add (c : FE) : ∀ (L : List ℕ) (acc : Array FE), L.Nodup → (∀ x ∈ L, x < acc.size) →
    ∀ j, (L.foldl (fun acc j ↦ acc.modify j (· + c)) acc).getD j 0 = acc.getD j 0 + if j ∈ L then c else 0
  | [], acc, _, _, j => by simp
  | x :: L, acc, hnd, hlt, j => by
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, getD_foldl_modify_add c L _ hnd.2 (fun y hy ↦ by
        rw [Array.size_modify]; exact hlt y (List.mem_cons_of_mem _ hy)) j,
      getD_modify_add _ _ _ _ (hlt x List.mem_cons_self)]
    by_cases hxj : x = j
    · subst hxj
      simp [hnd.1]
    · simp [hxj, Ne.symm hxj]

theorem getD_foldl_tensor (C : ℕ → List ℕ) (v : Array FE) (hnd : ∀ k, (C k).Nodup)
    (hlt : ∀ k, ∀ x ∈ C k, x < 128) (n : ℕ) :
    ((List.range n).foldl (fun acc k ↦ (C k).foldl (fun acc j ↦ acc.modify j (· + v.getD k 0)) acc)
        (Array.replicate 128 0)).size = 128 ∧
      ∀ j, ((List.range n).foldl (fun acc k ↦ (C k).foldl (fun acc j ↦ acc.modify j (· + v.getD k 0)) acc)
        (Array.replicate 128 0)).getD j 0 = ∑ k ∈ Finset.range n, if j ∈ C k then v.getD k 0 else 0 := by
  induction n with
  | zero =>
    refine ⟨Array.size_replicate .., fun j ↦ ?_⟩
    rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, Array.getD_eq_getD_getElem?,
      Array.getElem?_replicate]
    split <;> rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [size_foldl_modify, ih.1], fun j ↦ ?_⟩
    rw [getD_foldl_modify_add _ _ _ (hnd n) (fun x hx ↦ by rw [ih.1]; exact hlt n x hx), ih.2, Finset.sum_range_succ]

private def tCols (z : Lvm.FE2) : Array (List ℕ) :=
  (List.range 128).toArray.map fun k ↦ (List.range 128).filter fun j ↦ Lvm.bitFE2 (Lvm.basisFE2 k * z) j

private def tMz (v : Array FE) (cols : Array (List ℕ)) : Array FE :=
  (List.range 128).foldl (fun acc k ↦ (cols.getD k []).foldl (fun acc j ↦ acc.modify j (· + v.getD k 0)) acc)
    (Array.replicate 128 0)

private theorem tensorStepD_eq (v : Array FE) (zr : Lvm.FE2 × FE) :
    Lvm.tensorStepD v zr =
      (List.range 128).toArray.map fun j ↦ (1 + zr.2) * v.getD j 0 + (tMz v (tCols zr.1)).getD j 0 := rfl

private theorem tCols_getD (z : Lvm.FE2) (k : ℕ) :
    (tCols z).getD k [] =
      if k < 128 then (List.range 128).filter fun j ↦ Lvm.bitFE2 (Lvm.basisFE2 k * z) j else [] := by
  unfold tCols
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray]
  split <;> simp_all

theorem toExt3_sum (s : Finset ℕ) (g : ℕ → FE) : FE.toExt3 (∑ k ∈ s, g k) = ∑ k ∈ s, FE.toExt3 (g k) :=
  map_sum FE.ringEquivExt3 g s

theorem getD_toList_map_toExt3 (v : Array FE) (k : ℕ) :
    (v.toList.map FE.toExt3).getD k 0 = FE.toExt3 (v.getD k 0) := by
  rw [← FE.toExt3_zero, List.getD_map, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem tensorStepD_twin (v : Array FE) (zr : Lvm.FE2 × FE) :
    (Lvm.tensorStepD v zr).toList.map FE.toExt3 =
      tensorStep (v.toList.map FE.toExt3) (toE2 zr.1, FE.toExt3 zr.2) := by
  have hnd : ∀ k, ((tCols zr.1).getD k []).Nodup := fun k ↦ by
    rw [tCols_getD]; split
    · exact List.nodup_range.filter _
    · exact List.nodup_nil
  have hlt : ∀ k, ∀ x ∈ (tCols zr.1).getD k [], x < 128 := fun k x hx ↦ by
    rw [tCols_getD] at hx; split at hx
    · exact List.mem_range.mp (List.mem_filter.mp hx).1
    · simp at hx
  rw [tensorStepD_eq, tensorStep, Array.toList_map, List.toList_toArray, List.map_map]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < 128 := List.mem_range.mp hj
  rw [Function.comp_apply, tMz, (getD_foldl_tensor _ v hnd hlt 128).2 j, FE.toExt3_add, FE.toExt3_mul,
    FE.toExt3_add, FE.toExt3_one, getD_toList_map_toExt3, toExt3_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k hk ↦ ?_)
  have hk' : k < 128 := Finset.mem_range.mp hk
  rw [tCols_getD, ite_eq_left (c := k < 128) hk', getD_toList_map_toExt3, apply_ite FE.toExt3, FE.toExt3_zero]
  refine if_congr ?_ rfl rfl
  rw [List.mem_filter, bitFE2_eq, Lvm.FE2.fe2_mul_eq, toE2_basisFE2]
  simp only [List.mem_range, hj', true_and]

/-- **`tensorWD` is `tensorW`**, coordinatewise (`FE → E3` by `toExt3`, `FE2 → E2` by `toE2`). -/
theorem tensorWD_twin (z : List Lvm.FE2) (r : List FE) :
    (Lvm.tensorWD z r).toList.map FE.toExt3 = tensorW (z.map toE2) (r.map FE.toExt3) := by
  unfold Lvm.tensorWD tensorW
  have hinit : ((List.range 128).toArray.map fun j ↦ if j = 0 then (1 : FE) else 0).toList.map FE.toExt3 =
      (List.range 128).map fun j ↦ if j = 0 then (1 : E) else 0 := by
    rw [Array.toList_map, List.toList_toArray, List.map_map]
    refine List.map_congr_left fun j _ ↦ ?_
    rw [Function.comp_apply, apply_ite FE.toExt3, FE.toExt3_one, FE.toExt3_zero]
  rw [List.zip_map, List.foldl_map, ← hinit]
  exact (List.foldl_hom (fun v : Array FE ↦ v.toList.map FE.toExt3)
    (g₂ := fun acc zr ↦ tensorStep acc (Prod.map toE2 FE.toExt3 zr))
    (fun v zr ↦ (tensorStepD_twin v zr).symm)).symm

theorem tensorWD_getD (z : List Lvm.FE2) (r : List FE) (j : ℕ) :
    FE.toExt3 ((Lvm.tensorWD z r).getD j 0) = (tensorW (z.map toE2) (r.map FE.toExt3)).getD j 0 := by
  rw [← tensorWD_twin, getD_toList_map_toExt3]

end Words

/-! ### `Quad Ext3` on words (`wordWD`, `sumW6D`, `splitD`) -/

section Six

open Lvm.FE2 (toE2)

/-- V_S's `Quad Ext3` word pair as `E6`. -/
def FE6.toE6 (w : Lvm.FE6) : E6 := ⟨FE.toExt3 w.re, FE.toExt3 w.im⟩

theorem toExt3_xE : FE.toExt3 Lvm.FE6.xE = ofK g := by
  rw [Lvm.FE6.xE, Lvm.M3.tE_ofK]
  rfl

theorem toE6_mul (a b : Lvm.FE6) : FE6.toE6 (Lvm.FE6.mul a b) = FE6.toE6 a * FE6.toE6 b := by
  rw [Lvm.Quad.karatsuba]
  simp only [FE6.toE6, Lvm.FE6.mul, FE.toExt3_add, FE.toExt3_mul, toExt3_xE]

theorem toE6_add (a b : Lvm.FE6) : FE6.toE6 ⟨a.re + b.re, a.im + b.im⟩ = FE6.toE6 a + FE6.toE6 b :=
  QuadraticAlgebra.ext (FE.toExt3_add _ _) (FE.toExt3_add _ _)

theorem toE6_ofE2 (z : Lvm.FE2) : FE6.toE6 (Lvm.FE6.ofE2 z) = e2ToE6 (toE2 z) :=
  QuadraticAlgebra.ext (Lvm.M3.tE_ofK _) (Lvm.M3.tE_ofK _)

theorem toE6_ofE (r : FE) : FE6.toE6 (Lvm.FE6.ofE r) = Lvm.Quad.C (FE.toExt3 r) :=
  QuadraticAlgebra.ext rfl FE.toExt3_zero

theorem toE6_one_add (a : Lvm.FE6) : FE6.toE6 ⟨1 + a.re, a.im⟩ = 1 + FE6.toE6 a :=
  QuadraticAlgebra.ext (by simp [FE6.toE6, QuadraticAlgebra.re_one]) (by simp [FE6.toE6, QuadraticAlgebra.im_one])

theorem toE6_one_add_ofE (r : FE) : FE6.toE6 ⟨1 + r, 0⟩ = 1 + Lvm.Quad.C (FE.toExt3 r) :=
  QuadraticAlgebra.ext (by simp [FE6.toE6, QuadraticAlgebra.re_one]) (by simp [FE6.toE6, QuadraticAlgebra.im_one])

theorem toE6_one : FE6.toE6 ⟨1, 0⟩ = 1 := QuadraticAlgebra.ext FE.toExt3_one FE.toExt3_zero

theorem toE6_zero : FE6.toE6 ⟨0, 0⟩ = 0 := QuadraticAlgebra.ext FE.toExt3_zero FE.toExt3_zero

private def wordStepD (acc : Lvm.FE6) (p : Lvm.FE2 × FE) : Lvm.FE6 :=
  let a := Lvm.FE6.ofE2 p.1
  let f := Lvm.FE6.mul a (Lvm.FE6.ofE p.2)
  let g := Lvm.FE6.mul ⟨1 + a.re, a.im⟩ ⟨1 + p.2, 0⟩
  Lvm.FE6.mul acc ⟨f.re + g.re, f.im + g.im⟩

private def wordFactor (zl : E2) (rl : E) : E6 := e2ToE6 zl * Lvm.Quad.C rl + (1 + e2ToE6 zl) * (1 + Lvm.Quad.C rl)

private theorem wordWD_eq (z : List Lvm.FE2) (r : List FE) :
    Lvm.wordWD z r = (List.zip z r).foldl wordStepD ⟨1, 0⟩ := rfl

private theorem wordW_eq_fold (z : List E2) (r : List E) : wordW z r = (List.zipWith wordFactor z r).foldl (· * ·) 1 :=
  rfl

private theorem toE6_wordStepD (acc : Lvm.FE6) (zl : Lvm.FE2) (rl : FE) :
    FE6.toE6 (wordStepD acc (zl, rl)) = FE6.toE6 acc * wordFactor (toE2 zl) (FE.toExt3 rl) := by
  simp only [wordStepD, wordFactor, toE6_mul, toE6_add, toE6_ofE2, toE6_ofE, toE6_one_add, toE6_one_add_ofE]

private theorem toE6_foldl_wordStepD (z : List Lvm.FE2) (r : List FE) (acc : Lvm.FE6) :
    FE6.toE6 ((List.zip z r).foldl wordStepD acc) =
      (List.zipWith wordFactor (z.map toE2) (r.map FE.toExt3)).foldl (· * ·) (FE6.toE6 acc) := by
  induction z generalizing r acc with
  | nil => rfl
  | cons zl z ih =>
    cases r with
    | nil => rfl
    | cons rl r =>
      rw [List.zip_cons_cons, List.foldl_cons, ih, List.map_cons, List.map_cons, List.zipWith_cons_cons,
        List.foldl_cons, toE6_wordStepD]

/-- **`wordWD` is `wordW`** (`FE6 → E6` by `toExt3` on both coordinates). -/
theorem wordWD_twin (z : List Lvm.FE2) (r : List FE) :
    FE6.toE6 (Lvm.wordWD z r) = wordW (z.map toE2) (r.map FE.toExt3) := by
  rw [wordWD_eq, wordW_eq_fold, toE6_foldl_wordStepD, toE6_one]

/-- A part of an `E2` sum claim, V_S's to the spec's. -/
def partE (p : Lvm.FE2 × Lvm.Placement × List Lvm.FE2) : E2 × Lvm.VEq.VPlacement × List E2 :=
  (toE2 p.1, Lvm.VEq.plE p.2.1, p.2.2.map toE2)

/-- **`sumW6D` is `sumW6`**. -/
theorem sumW6D_twin (parts : List (Lvm.FE2 × Lvm.Placement × List Lvm.FE2)) (x : List FE) :
    FE6.toE6 (Lvm.sumW6D parts x) = sumW6 (parts.map partE) (x.map FE.toExt3) := by
  unfold Lvm.sumW6D sumW6
  rw [← zero_add (List.sum _), ← toE6_zero]
  generalize (⟨0, 0⟩ : Lvm.FE6) = acc
  induction parts generalizing acc with
  | nil => rw [List.foldl_nil, List.map_nil, List.map_nil, List.sum_nil, add_zero]
  | cons p parts ih =>
    obtain ⟨c, blk, z⟩ := p
    rw [List.foldl_cons, ih, List.map_cons, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    simp only [toE6_add, toE6_mul, toE6_ofE2, toE6_ofE, wordWD_twin, Lvm.VEq.toExt3_eqAbove, List.map_take,
      partE]
    rfl

/-- **V_S's block claim `c` computes the spec's `d`**: the same block, the weight at `x` is the spec's at
`x.map toExt3`, the value its `toExt3`. -/
def BlockTwin (c : Lvm.BlockClaim) (d : Lvm.VEq.BClaim) : Prop :=
  Lvm.VEq.plE c.block = d.block ∧ (∀ x, FE.toExt3 (c.weight x) = d.weight (x.map FE.toExt3)) ∧
    FE.toExt3 c.value = d.value

/-- Twins put on the stack are twins. -/
theorem BlockTwin.onStack {c : Lvm.BlockClaim} {d : Lvm.VEq.BClaim} (h : BlockTwin c d) :
    (∀ x, FE.toExt3 (c.onStack.1 x) = d.onStack.1 (x.map FE.toExt3)) ∧
      FE.toExt3 c.onStack.2 = d.onStack.2 := by
  obtain ⟨hb, hw, hv⟩ := h
  refine ⟨fun x ↦ ?_, hv⟩
  simp only [Lvm.BlockClaim.onStack, Lvm.VEq.BClaim.onStack, FE.toExt3_mul, Lvm.VEq.toExt3_eqAbove, hw,
    List.map_take, ← hb]
  rfl

/-- **`splitD` is `splitE2`**: both block claims, in order. -/
theorem splitD_twin (nu : ℕ) (parts : List (Lvm.FE2 × Lvm.Placement × List Lvm.FE2)) (v : Lvm.FE2) :
    List.Forall₂ BlockTwin (Lvm.splitD nu parts v) (splitE2 nu ⟨parts.map partE, toE2 v⟩) := by
  refine .cons ⟨rfl, fun x ↦ ?_, Lvm.M3.tE_ofK _⟩ (.cons ⟨rfl, fun x ↦ ?_, Lvm.M3.tE_ofK _⟩ .nil)
  · exact congrArg QuadraticAlgebra.re (sumW6D_twin parts x)
  · exact congrArg QuadraticAlgebra.im (sumW6D_twin parts x)

/-! ### The digest's bits (`sBitsD`) -/

theorem testBit_byte_ge (x : UInt8) {m : ℕ} (hm : 8 ≤ m) : x.toNat.testBit m = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by (clear * - m; omega)) hm))

/-- Bit `t` of the little-endian word of eight bytes is bit `t mod 8` of byte `t / 8`. -/
theorem testBit_laneWord (b : ℕ → UInt8) (t : ℕ) (ht : t < 64) :
    ((List.range 8).foldl (fun w k ↦ w ||| ((b k).toUInt64 <<< (8 * k).toUInt64)) (0 : UInt64)).toNat.testBit t =
      (b (t / 8)).toNat.testBit (t % 8) := by
  have hs : ∀ k, k < 8 → (8 * k).toUInt64.toNat % 64 = 8 * k := fun k hk ↦ by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by (clear * - k t hk; omega)), Nat.mod_eq_of_lt (by (clear * - k t hk; omega))]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.testBit_or,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, UInt64.toNat_zero, Nat.zero_testBit, Bool.false_or]
  -- GOLF3: the 64 bit positions closed with literal side conditions by `decide` (3.57 M -> 0.76 M kernel heartbeats
  -- against `interval_cases q` with an `omega` discharger, 106 omega proofs)
  rw [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hs 4 (by decide), hs 5 (by decide),
    hs 6 (by decide), hs 7 (by decide)]
  interval_cases t <;> simp (disch := decide) only [decide_eq_true, decide_eq_false, testBit_byte_ge,
    Bool.true_and, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or, Nat.add_sub_cancel_left,
    Nat.mul_zero, Nat.sub_zero]

/-- **V_S's digest bits from the digest's lanes** (`digestLanes`, the `pubOf` packing of `vk`, `c`) are
`digestBits`. -/
theorem sBitsD_digestLanes (d : Vector UInt8 32) : Lvm.sBitsD (Lvm.digestLanes d) = Lvm.KG.digestBits d := by
  funext j
  unfold Lvm.sBitsD Lvm.KG.digestBits
  by_cases hj : j < 256
  · rw [dite_eq_left_of_eq_true (eq_true hj), decide_eq_true hj, Bool.true_and, Lvm.digestLanes,
      List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range (by (clear * - j hj; omega)), Option.map_some, Option.getD_some]
    dsimp only
    rw [testBit_laneWord _ _ (by (clear * - j; omega)), show 8 * (j / 64) + j % 64 / 8 = j / 8 by (clear * - j; omega),
      show j % 64 % 8 = j % 8 by (clear * - j; omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [Vector.size_toArray]; (clear * - j hj; omega))]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false hj), decide_eq_false hj, Bool.false_and]

end Six

end Lvm.E2V
