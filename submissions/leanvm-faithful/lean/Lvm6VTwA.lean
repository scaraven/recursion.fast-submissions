-- New for lvm6 (WP-V1b): the algebra under the Keccak layer twins. Twins that carry a property of the fast value
-- (`TwinP`), the season-1 layer functions under ring maps (`map_weightedCF`, `map_rcOuterF`, `map_corrGF`,
-- `map_linearTransposeF`, …), the batched weights as an outer product (`batchWF_outer`), the tail's dot product
-- as `weightedRefF` (`dot_weightedRef`), and the claim weights in symbolic form (`WRep`).
import Lvm6VTwK
import LvmE2VFastK
import LvmE2VGkrLayer

/-!
# Algebra for the layer twins

* `TwinP P d p fp`: `TwinF` and `P` on the fast value; `tw_bindG`, `twP_bind`, `twP_pure`, `twin_monoF`.
* Ring maps: `arr_getD_map`, `map_eqKernelF`, `map_eqKernelAF`, `map_outerUGF`, `map_corrGF`, `map_weightedRefF`,
  `map_rcRefF`, `map_weightedCF`, `map_rcOuterF`, `map_linearTransposeF`, `map_powersF`, `map_instWeightsF`.
* `eqKernelAF_toList`, **`dot_weightedRef`** (`dot(eq(lv)[:1600], w) = weightedRefF eqZ eqL w`, `|lv| = 11`),
  **`batchWF_outer`** (`batchWF lv β = outerUGF eqZ (laneWA eqL β)`).
* **`WRep`**: claim weights as an array (`mat`) or as `T(A ⊗ ℓ)` (`tro`); `WRep.dec`, `WRep.rc`, `WRep.dot`,
  `toE2_rc`, `toE2_dot`.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Finset

/-! ## Twins with a property of the fast value -/

/-- `TwinF` together with `P` on the fast value. -/
abbrev TwinP {α β : Type} (P : β → Prop) (d : β → α) (p : VerifierProgram α) (fp : VF β) : Prop :=
  Twin (fun _ b a => d b = a ∧ P b) p fp

theorem tw_bindG {α β α' β' : Type} {d : β → α} {R' : ByteArray → β' → α' → Prop} {p : VerifierProgram α}
    {fp : VF β} {f : α → VerifierProgram α'} {fg : β → VF β'} (hp : TwinF d p fp)
    (hf : ∀ b, Twin R' (f (d b)) (fg b)) : Twin R' (p >>= f) (VF.bind fp fg) :=
  twin_bind hp fun π b a h tr => by subst h; exact hf b π tr

theorem twP_bind {α β α' β' : Type} {P : β → Prop} {d : β → α} {R' : ByteArray → β' → α' → Prop}
    {p : VerifierProgram α} {fp : VF β} {f : α → VerifierProgram α'} {fg : β → VF β'} (hp : TwinP P d p fp)
    (hf : ∀ b, P b → Twin R' (f (d b)) (fg b)) : Twin R' (p >>= f) (VF.bind fp fg) :=
  twin_bind hp fun π b a h tr => by obtain ⟨rfl, hb⟩ := h; exact hf b hb π tr

theorem twP_pure {α β : Type} {P : β → Prop} {d : β → α} {a : α} {b : β} (h : d b = a) (hb : P b) :
    TwinP P d (pure a) (VF.pure b) :=
  twin_ret _ (b := fun _ => b) fun _ => ⟨h, hb⟩

theorem twin_monoF {α β : Type} {R R' : ByteArray → β → α → Prop} {p : VerifierProgram α} {fp : VF β}
    (hp : Twin R p fp) (h : ∀ π b a, R π b a → R' π b a) : Twin R' p fp := by
  intro π tr
  have hr := hp π tr
  revert hr
  generalize fp π tr = x
  generalize replayP p (tr.map (NV.val π)) = y
  intro hr
  cases hr with
  | none => exact Option.Rel.none
  | some hb => exact Option.Rel.some ⟨h π _ _ hb.1, hb.2⟩

/-- The plain sumcheck, with the number of its challenges. -/
theorem tw_sumcheckL (g count : ℕ) : ∀ (modes : List (Option FE2)) (claim : FE2),
    TwinP (fun r => r.1.length = modes.length) scD
      (sumcheckE2 g (FE2.toE2 claim) count (modes.map (Option.map FE2.toE2))) (fSumcheck g claim count modes)
  | [], _ => twP_pure rfl rfl
  | mode :: modes, claim =>
    tw_bindG (f := fun msg => e2Sample g >>= fun c => sumcheckE2 g (polyEvalF msg c) count
        (modes.map (Option.map FE2.toE2)) >>= fun res => pure (c :: res.1, res.2))
      (tw_roundPoly count claim mode) fun msg =>
      tw_bindG (f := fun c => sumcheckE2 g (polyEvalF (msg.map FE2.toE2) c) count
          (modes.map (Option.map FE2.toE2)) >>= fun res => pure (c :: res.1, res.2))
        (tw_e2Sample g) fun c => by
        try dsimp only
        rw [← toE2_polyEvalF]
        exact twP_bind (tw_sumcheckL g count modes _) fun res hres => twP_pure rfl (by simp [hres])

theorem tw_sumcheckPlainL (g count n : ℕ) (claim : FE2) :
    TwinP (fun r => r.1.length = n) scD (sumcheckE2 g (FE2.toE2 claim) count (List.replicate n none))
      (fSumcheck g claim count (List.replicate n none)) := by
  have h := tw_sumcheckL g count (List.replicate n none) claim
  rw [List.map_replicate, List.length_replicate] at h
  exact h

/-! ## Ring maps -/

section Map

variable {F F' : Type} [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →+* F')

theorem arr_getD_map (a : Array F) (i : ℕ) : (a.map φ).getD i 0 = φ (a.getD i 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> simp

theorem map_getD_arrMap {α : Type} (a : Array α) (f : α → F) (i : ℕ) :
    φ ((a.map f).getD i 0) = (a.map fun x => φ (f x)).getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> simp

theorem arr_getD_toList (a : Array F) (i : ℕ) : a.getD i 0 = a.toList.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem map_optGetD (o : Option F) : φ (o.getD 0) = (o.map φ).getD 0 := by
  cases o <;> simp

theorem map_foldl {α : Type} (L : List α) (f : F → α → F) (g : F' → α → F') (h : ∀ acc x, φ (f acc x) = g (φ acc) x) :
    ∀ (a : F) (b : F'), φ a = b → φ (L.foldl f a) = L.foldl g b := by
  induction L with
  | nil => intro a b hab; exact hab
  | cons x L ih => intro a b hab; exact ih _ _ (by rw [h, hab])

theorem map_eqKernelF (p : List F) : (eqKernelF p).map φ = eqKernelF (p.map φ) := by
  unfold eqKernelF
  suffices h : ∀ init : List F, (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) init).map φ =
      (p.map φ).foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) (init.map φ) by
    rw [h]; simp
  induction p with
  | nil => intro init; rfl
  | cons r p ih =>
    intro init
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [List.map_append, List.map_map, Function.comp_def, map_mul, map_add, map_one]

theorem map_eqKernelAF (p : List F) : (eqKernelAF p).map φ = eqKernelAF (p.map φ) := by
  unfold eqKernelAF
  suffices h : ∀ init : Array F,
      (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) init).map φ =
      (p.map φ).foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) (init.map φ) by
    rw [h]; simp
  induction p with
  | nil => intro init; rfl
  | cons r p ih =>
    intro init
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Array.map_append, Array.map_map, Function.comp_def, map_mul, map_add, map_one]

theorem map_outerUGF (A ℓ : Array F) : (outerUGF A ℓ).map φ = outerUGF (A.map φ) (ℓ.map φ) := by
  simp only [outerUGF, List.map_map, Function.comp_def, map_mul, arr_getD_map]

theorem map_corrGF (A B : Array F) (r : ℕ) : φ (corrGF A B r) = corrGF (A.map φ) (B.map φ) r := by
  simp only [corrGF, map_sumF, List.map_map, Function.comp_def, map_mul, arr_getD_map]

theorem map_weightedRefF (eqZ eqL : Array F) (w : List F) :
    φ (weightedRefF eqZ eqL w) = weightedRefF (eqZ.map φ) (eqL.map φ) (w.map φ) := by
  simp only [weightedRefF, map_sumF, List.map_map, Function.comp_def, map_mul, arr_getD_map,
    array_getD_toArrayF, map_getD]

theorem map_rcRefF (w : List F) (rc : UInt64) : φ (rcRefF w rc) = rcRefF (w.map φ) rc := by
  simp only [rcRefF, map_sumF, List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun z _ => ?_
  split_ifs <;> simp [map_getD, map_optGetD]

theorem map_weightedCF (corr : ℕ → F) (eqL ℓ : Array F) :
    φ (weightedCF corr eqL ℓ) = weightedCF (fun r => φ (corr r)) (eqL.map φ) (ℓ.map φ) := by
  simp only [weightedCF, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind]
  refine map_foldl φ _ _ _ (fun acc l => ?_) _ _ (map_zero φ)
  simp only [map_add, map_mul, arr_getD_map, map_getD_arrMap]

theorem map_rcOuterF (A ℓ : Array F) (rc : UInt64) :
    φ (rcOuterF A ℓ rc) = rcOuterF (A.map φ) (ℓ.map φ) rc := by
  simp only [rcOuterF, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind]
  refine map_foldl φ _ _ _ (fun acc y => ?_) _ _ ?_
  · simp only [map_add, map_mul, arr_getD_map, map_sumF, List.map_map, Function.comp_def]
  · simp only [map_mul, arr_getD_map, map_sumF, List.map_map, Function.comp_def]

theorem map_linearTransposeF (w : List F) : (linearTransposeF w).map φ = linearTransposeF (w.map φ) := by
  refine List.ext_getElem (by simp [linearTransposeF_length]) fun p h1 h2 => ?_
  have hp : p < 1600 := by simpa [linearTransposeF_length] using h2
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2, ← map_getD, linearTransposeF_getD w hp,
    linearTransposeF_getD _ hp]
  simp only [thetaTF, colLF, gOfF, map_add, map_sum, map_getD]

theorem map_powersFromF (acc base : F) : ∀ n, (powersFromF acc base n).map φ = powersFromF (φ acc) (φ base) n
  | 0 => rfl
  | n + 1 => by simp only [powersFromF, List.map_cons, map_powersFromF _ _ n, map_mul]

theorem map_powersF (base : F) (n : ℕ) : (powersF base n).map φ = powersF (φ base) n := by
  unfold powersF; rw [map_powersFromF, map_one]

theorem map_instWeightsF (s : F) : (instWeightsF s).map φ = instWeightsF (φ s) := by
  simp only [instWeightsF, List.map_map, Function.comp_def, map_sumF, List.map_filterMap]
  refine List.map_congr_left fun e _ => ?_
  congr 1
  refine List.filterMap_congr fun b _ => ?_
  split_ifs <;> simp [map_getD, map_optGetD, ← map_powersF]

theorem map_dotF (a b : List F) : φ (dotF a b) = dotF (a.map φ) (b.map φ) := by
  unfold dotF
  rw [map_foldl_add, map_zero, List.map_zipWith, List.zipWith_map]
  simp only [map_mul]

end Map

/-! ## The tail's dot product and the batched weights -/

section Gen

variable {F : Type} [Field F] [Algebra K F]

theorem eqKernelAF_toList (p : List F) : (eqKernelAF p).toList = eqKernelF p := by
  unfold eqKernelAF eqKernelF
  suffices h : ∀ init : Array F,
      (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) init).toList =
      p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) init.toList by
    exact h _
  induction p with
  | nil => intro init; rfl
  | cons r p ih => intro init; simp only [List.foldl_cons]; rw [ih]; simp

theorem eqKernelAF_getD (p : List F) (i : ℕ) :
    (eqKernelAF p).getD i 0 = if i < 2 ^ p.length then eqAtF p i else 0 := by
  rw [arr_getD_toList, eqKernelAF_toList, eqKernelF_getD]

/-- `dotF` against any list: the sum over the first list's indices. -/
theorem dotF_getD : ∀ (a b : List F), dotF a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0
  | [], _ => by simp [dotF]
  | x :: a, [] => by simp [dotF]
  | x :: a, y :: b => by
    have h := dotF_getD a b
    unfold dotF at h ⊢
    rw [← sumF, sumF_eq_sum] at h ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', h]
    simp [add_comm]

theorem eqAtF_split (lv : List F) (hl : lv.length = 11) {l z : ℕ} (hz : z < 64) :
    eqAtF lv (64 * l + z) = eqAtF (lv.take 6) z * eqAtF (lv.drop 6) l := by
  conv_lhs => rw [← List.take_append_drop 6 lv]
  have h6 : (lv.take 6).length = 6 := by simp [hl]
  rw [eqAtF_append, h6, eqAtF_mod (lv.take 6), h6, show (2:ℕ) ^ 6 = 64 from rfl]
  congr 2 <;> omega

theorem getD_take (l : List F) (n i : ℕ) : (l.take n).getD i 0 = if i < n then l.getD i 0 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs <;> simp [List.getD_eq_getElem?_getD]

/-- **The tail's dot product** is `weightedRefF` of the two equality kernels (`|lv| = 11`). -/
theorem dot_weightedRef (lv w : List F) (hl : lv.length = 11) :
    dotF ((eqKernelF lv).take 1600) w = weightedRefF (eqKernelAF (lv.take 6)) (eqKernelAF (lv.drop 6)) w := by
  rw [dotF_getD, List.length_take, eqKernelF_length, hl, show min 1600 (2 ^ 11) = 25 * 64 from rfl,
    sum_range_mulB]
  simp only [weightedRefF, sumF_map_range, array_getD_toArrayF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl' => Finset.sum_congr rfl fun z hz => ?_
  have hl' := Finset.mem_range.1 hl'
  have hz := Finset.mem_range.1 hz
  have h6 : (lv.take 6).length = 6 := by simp [hl]
  have h5 : (lv.drop 6).length = 5 := by simp [hl]
  rw [getD_take, eqKernelF_getD, eqKernelAF_getD, eqKernelAF_getD, hl, h6, h5]
  simp only [show (2:ℕ) ^ 11 = 2048 from rfl, show (2:ℕ) ^ 6 = 64 from rfl, show (2:ℕ) ^ 5 = 32 from rfl]
  split_ifs <;> first | omega | (rw [eqAtF_split lv hl hz]; ring)

/-- The lane weights of the batched claim: `eqL[l] + β·(eqL[along l 4] + β·eqL[along l 3])`. -/
def laneWA (eqL : Array F) (beta : F) : Array F :=
  (Array.range 25).map fun l => eqL.getD l 0 + beta * (eqL.getD ((l % 5 + 4) % 5 + 5 * (l / 5)) 0 +
    beta * eqL.getD ((l % 5 + 3) % 5 + 5 * (l / 5)) 0)

theorem laneWA_getD (eqL : Array F) (beta : F) {l : ℕ} (hl : l < 25) :
    (laneWA eqL beta).getD l 0 = eqL.getD l 0 + beta * (eqL.getD ((l % 5 + 4) % 5 + 5 * (l / 5)) 0 +
      beta * eqL.getD ((l % 5 + 3) % 5 + 5 * (l / 5)) 0) := by
  simp [laneWA, Array.getD_eq_getD_getElem?, hl]

theorem outerUGF_getD (A ℓ : Array F) {j : ℕ} (hj : j < 1600) :
    (outerUGF A ℓ).getD j 0 = A.getD (j % 64) 0 * ℓ.getD (j / 64) 0 := by
  simp [outerUGF, List.getD_eq_getElem?_getD, keccakBits, hj]

/-- **The batched weights are an outer product** (`|lv| = 11`). -/
theorem batchWF_outer (lv : List F) (hl : lv.length = 11) (beta : F) :
    batchWF lv beta = outerUGF (eqKernelAF (lv.take 6)) (laneWA (eqKernelAF (lv.drop 6)) beta) := by
  unfold batchWF outerUGF
  refine List.map_congr_left fun j hj => ?_
  have hj : j < 1600 := by simpa [keccakBits] using hj
  try dsimp only
  rw [laneWA_getD _ _ (by omega)]
  have h6 : (lv.take 6).length = 6 := by simp [hl]
  have h5 : (lv.drop 6).length = 5 := by simp [hl]
  have hz : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hA : ∀ k, Lvm.keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 :=
    fun k => rfl
  have hj' : eqAtF lv j = eqAtF (lv.take 6) (j % 64) * eqAtF (lv.drop 6) (j / 64) := by
    have := eqAtF_split lv hl (l := j / 64) hz
    rwa [Nat.div_add_mod] at this
  rw [hA 4, hA 3]
  simp only [eqKernelF_getD, eqKernelAF_getD, hl, h6, h5, show (2:ℕ) ^ 11 = 2048 from rfl,
    show (2:ℕ) ^ 6 = 64 from rfl, show (2:ℕ) ^ 5 = 32 from rfl]
  rw [eqAtF_split lv hl hz, eqAtF_split lv hl hz, hj']
  split_ifs <;> first | omega | ring

end Gen

/-! ## Claim weights in symbolic form -/

/-- `K → FE2` through the words. -/
instance instAlgKFE2 : Algebra K FE2 := (FE2.ofKRingHom.comp FK.ringEquivBF64.symm.toRingHom).toAlgebra

/-- The weights of a fast claim: an array, or `T(A ⊗ ℓ)` with `A = eq(pA)`, `|pA| = 6` (after a layer). -/
inductive WRep where
  | mat (w : Array FE2)
  | tro (pA : List FE2) (A ℓ : Array FE2) (hp : pA.length = 6) (hA : A = eqKernelAF pA)

/-- Their value in `E2`. -/
def WRep.dec : WRep → List E2
  | .mat w => w.toList.map FE2.toE2
  | .tro _ A ℓ _ _ => linearTransposeF (outerUGF (A.map FE2.toE2) (ℓ.map FE2.toE2))

/-- `rcRefF` of the weights. -/
def WRep.rc : WRep → UInt64 → FE2
  | .mat w, rc => rcRefF w.toList rc
  | .tro _ A ℓ _ _, rc => rcOuterF A ℓ rc

/-- `weightedRefF eqZ eqL` of the weights, `eqZ = eq(q)`: the correlations by season 1's automaton. -/
def WRep.dot : WRep → List FE2 → Array FE2 → Array FE2 → FE2
  | .mat w, _, eqZ, eqL => weightedRefF eqZ eqL w.toList
  | .tro pA _ ℓ _ _, q, _, eqL => weightedCF (corrAF (corrTabF q pA)) eqL ℓ

theorem toE2_rc (W : WRep) (rc : UInt64) : FE2.toE2 (W.rc rc) = rcRefF W.dec rc := by
  cases W with
  | mat w => exact map_rcRefF tE w.toList rc
  | tro pA A ℓ hp hA =>
    show tE (rcOuterF A ℓ rc) = _
    rw [map_rcOuterF, rcOuterF_eq]
    rfl

theorem toE2_dot (W : WRep) (q : List FE2) (hq : q.length = 6) (eqL : Array FE2) :
    FE2.toE2 (W.dot q (eqKernelAF q) eqL) =
      weightedRefF ((eqKernelAF q).map FE2.toE2) (eqL.map FE2.toE2) W.dec := by
  cases W with
  | mat w => exact map_weightedRefF tE _ eqL w.toList
  | tro pA A ℓ hp hA =>
    have e : weightedCF (corrAF (corrTabF q pA)) eqL ℓ = weightedCF (corrGF A (eqKernelAF q)) eqL ℓ := by
      rw [hA]
      congr 1
      funext r
      exact corrAF_eq q pA hq hp r
    show tE (weightedCF (corrAF (corrTabF q pA)) eqL ℓ) = _
    rw [e, map_weightedCF]
    simp only [map_corrGF]
    exact weightedCF_eq _ _ _ _

/-- The first six coordinates, padded with zeros (always six). -/
def z6 (l : List FE2) : List FE2 := (l ++ List.replicate 6 0).take 6

theorem z6_length (l : List FE2) : (z6 l).length = 6 := by simp [z6]

theorem z6_eq {l : List FE2} (h : 6 ≤ l.length) : z6 l = l.take 6 := List.take_append_of_le_length h

end Lvm6.V
