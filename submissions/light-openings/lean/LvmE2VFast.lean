-- New for lvm2 E2-FT (E2F-VP): fast executable twins of V_S's S2GF decision (`LvmDecideE2`), each proved equal to
-- the piece it replaces; `decideProgFF_eq : decideProgFF = decideProgF`. `decideFFX` (`LvmE2VRefines`) runs
-- `decideProgFF`; every proof about the decision stays on `decideProgF`.
import LvmE2VTwins
import LvmE2VGkrBase
import LvmE2VFastK
import LvmE2VWireAlg

/-!
# Fast twins of the S2GF decision

Each twin is a copy of its original with one subterm swapped:

* **`verifyKeccakLayerDS`**: a Keccak GKR layer on pending weights (roll 10's `SClaim`, at `E2`: the next weights
  stay `T(eq(p, ·) ⊗ ℓ)`, `weighted` and `iota` read them through `LvmE2VFastK`'s identities); the original builds
  `eq(local, ·)` (2048 entries), walks it as a list for each of the 1600 bits, and transposes 1600 weights per layer;
* **`tRowsF` / `tensorStepF` / `tensorWDF`**: the row switch's tensor coordinates. Per factor `z_l` the rows
  `{k | bit j of β_k·z_l}` are computed once, outside the weight's closure (the original recomputes the
  128 × 128 products `β_k·z_l` for every coordinate `j` and every evaluation point);
* the phases above them (`verifyKeccakLayerDF` … `callerDF`, `rowSwitchDF`) and **`decideProgFF`**, which differ
  from the originals only by calling the twins.
-/

set_option autoImplicit false

namespace Lvm

open DM Lvm.E2V
open LeanVM.Protocol.Verifier (keccakLocalBits keccakLaneBits qkeccakSlotBits keccakSegmentBits keccakSegments
  keccakDepth keccakAlong keccakBits)

theorem list_toArray_getD {α : Type} (l : List α) (j : Nat) (d : α) : l.toArray.getD j d = l.getD j d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-! ## `eq` tables -/

theorem eqAtF_append {F : Type} [Field F] : ∀ (r s : List F) (w : Nat),
    E2V.eqAtF (r ++ s) w = E2V.eqAtF r (w % 2 ^ r.length) * E2V.eqAtF s (w / 2 ^ r.length)
  | [], s, w => by simp [E2V.eqAtF]
  | a :: r, s, w => by
    have h1 : w % 2 ^ (r.length + 1) % 2 = w % 2 := by rw [pow_succ', Nat.mod_mul_right_mod]
    have h2 : w % 2 ^ (r.length + 1) / 2 = w / 2 % 2 ^ r.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    have h3 : w / 2 ^ (r.length + 1) = w / 2 / 2 ^ r.length := by rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [List.cons_append, E2V.eqAtF, eqAtF_append r s (w / 2), List.length_cons, E2V.eqAtF, h1, h2, h3, mul_assoc]

/-- `eq(r, ·)` as two half tables: `eq(r, w) = lo[w mod 2^k]·hi[w / 2^k]`, `k = |r| / 2`. -/
structure EqTab where
  /-- `2^k`. -/
  pk : Nat
  /-- `2^|r|`. -/
  bound : Nat
  /-- `eq(r.take k, ·)`. -/
  lo : Array FE2
  /-- `eq(r.drop k, ·)`. -/
  hi : Array FE2

/-- The tables of `r`. -/
def eqTab (r : List FE2) : EqTab :=
  let k := r.length / 2
  ⟨2 ^ k, 2 ^ r.length, (eqKernelF (r.take k)).toArray, (eqKernelF (r.drop k)).toArray⟩

/-- `E2V.eqAtF r w` from `r`'s tables (directly past `2^|r|`). -/
@[inline] def EqTab.at (t : EqTab) (r : List FE2) (w : Nat) : FE2 :=
  if w < t.bound then t.lo.getD (w % t.pk) 0 * t.hi.getD (w / t.pk) 0 else E2V.eqAtF r w

theorem eqTab_at (r : List FE2) (w : Nat) : (eqTab r).at r w = E2V.eqAtF r w := by
  unfold EqTab.at eqTab
  simp only
  split
  · rename_i hw
    have hk : r.length / 2 ≤ r.length := Nat.div_le_self _ _
    have hl : (r.take (r.length / 2)).length = r.length / 2 := List.length_take_of_le hk
    have hd : (r.drop (r.length / 2)).length = r.length - r.length / 2 := List.length_drop
    conv_rhs => rw [← List.take_append_drop (r.length / 2) r]
    rw [eqAtF_append, hl, list_toArray_getD, list_toArray_getD, E2V.eqKernelF_getD, E2V.eqKernelF_getD, hl, hd,
      ite_eq_left (Nat.mod_lt _ (Nat.two_pow_pos _)), ite_eq_left]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel hk]
    exact hw
  · rfl

/-- `contShiftF` from `eq` tables. -/
def contShiftFF (rows : List Nat) (rho rho' : List FE2) : FE2 :=
  let A := eqTab rho
  let B := eqTab rho'
  sumF (rows.map fun i => A.at rho i * B.at rho' (i - 1))

theorem contShiftFF_eq : contShiftFF = contShiftF (F := FE2) := by
  funext rows rho rho'
  unfold contShiftFF contShiftF
  simp only [eqTab_at]

/-! ## The Keccak GKR layer -/

/-- `eq(lv, ·)` on the first 1600 indices from the halves `eq(lv.take 6, ·)`, `eq(lv.drop 6, ·)`. -/
def eqHead (lv : List FE2) : List FE2 :=
  let eqZ := (eqKernelF (lv.take 6)).toArray
  let eqL := (eqKernelF (lv.drop 6)).toArray
  (List.range keccakBits).map fun j => eqZ.getD (j % 64) 0 * eqL.getD (j / 64) 0

theorem eqHead_eq (lv : List FE2) (h : lv.length = 11) : eqHead lv = (eqKernelF lv).take keccakBits := by
  have h6 : (lv.take 6).length = 6 := by simp [h]
  have h5 : (lv.drop 6).length = 5 := by simp [h]
  have hk : (eqKernelF lv).length = 2048 := by rw [E2V.eqKernelF_length, h]; rfl
  apply List.ext_getElem
  · simp [eqHead, hk, keccakBits]
  · intro j h1 h2
    have hj : j < 1600 := by simpa [eqHead, keccakBits] using h1
    rw [List.getElem_take, ← List.getD_eq_getElem (eqKernelF lv) 0 (by omega), E2V.eqKernelF_getD,
      ite_eq_left (by rw [h]; omega)]
    simp only [eqHead, List.getElem_map, List.getElem_range]
    rw [list_toArray_getD, list_toArray_getD, E2V.eqKernelF_getD,
      E2V.eqKernelF_getD, h6, h5, ite_eq_left (by omega), ite_eq_left (by omega)]
    conv_rhs => rw [← List.take_append_drop 6 lv]
    rw [eqAtF_append, h6]
    rfl

/-- The first 1600 `eq(lv, ·)` weights, from the halves when `|lv| = 11`. -/
def eqHeadOf (lv : List FE2) : List FE2 :=
  if lv.length = 11 then eqHead lv else (eqKernelF lv).take keccakBits

theorem eqHeadOf_eq (lv : List FE2) : eqHeadOf lv = (eqKernelF lv).take keccakBits := by
  unfold eqHeadOf
  split
  · exact eqHead_eq lv ‹_›
  · rfl

theorem keccakAlong_lt {j : Nat} (k : Nat) (hj : j < 1600) : keccakAlong j k < 1600 := by
  show 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 < 1600
  omega

/-! ## The Keccak GKR layer with pending weights (roll 10's `SClaim`, at `E2`) -/

/-- A layer claim's bit weights: listed (`mat`), or `T(eq(p, ·) ⊗ ℓ)` with the transpose pending (`outer`). -/
inductive LWtsE2 where
  | mat (w : List FE2)
  | outer (p : List FE2) (laneW : Array FE2)

/-- The weights as a list (the reference form). -/
def LWtsE2.toList : LWtsE2 → List FE2
  | .mat w => w
  | .outer p laneW => linearTransposeF (outerUGF (eqKernelAF p) laneW)

/-- A layer claim with pending weights. -/
structure SClaimE2 where
  /-- The claimed value. -/
  value : FE2
  /-- The instance weights. -/
  mu : List FE2
  /-- The point. -/
  point : List FE2
  /-- The bit weights. -/
  weights : LWtsE2

/-- The reference claim. -/
def SClaimE2.toClaim (c : SClaimE2) : KClaim FE2 := ⟨c.value, c.mu, c.point, c.weights.toList⟩

/-- A reference claim, its weights listed. -/
def SClaimE2.ofClaim (c : KClaim FE2) : SClaimE2 := ⟨c.value, c.mu, c.point, .mat c.weights⟩

theorem SClaimE2.toClaim_ofClaim (c : KClaim FE2) : (SClaimE2.ofClaim c).toClaim = c := rfl

theorem eqKernelAF_eq (p : List FE2) : eqKernelAF p = (eqKernelF p).toArray := by
  rw [eqKernelAF_def]
  unfold eqKernelF
  suffices h : ∀ (a : List FE2), p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) a.toArray =
      (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) a).toArray from h [1]
  induction p with
  | nil => intro a; rfl
  | cons r p ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ← ih, List.map_toArray, List.map_toArray, List.append_toArray]

theorem sum_range_64 (f : Nat → FE2) : ∀ n,
    ∑ j ∈ Finset.range (64 * n), f j = ∑ l ∈ Finset.range n, ∑ z ∈ Finset.range 64, f (64 * l + z)
  | 0 => by simp
  | n + 1 => by
    rw [show 64 * (n + 1) = 64 * n + 64 by ring, Finset.sum_range_add, sum_range_64 f n,
      Finset.sum_range_succ (fun l => ∑ z ∈ Finset.range 64, f (64 * l + z)) n]

/-- `weightedRefF` on the halves of an 11-coordinate point is `dot(eq[:1600], w)`. -/
theorem weightedRefF_halves (lv w : List FE2) (hl : lv.length = 11) (hw : w.length = keccakBits) :
    weightedRefF (eqKernelAF (lv.take 6)) (eqKernelAF (lv.drop 6)) w =
      dotF ((eqKernelF lv).take keccakBits) w := by
  have h6 : (lv.take 6).length = 6 := by simp [hl]
  have h5 : (lv.drop 6).length = 5 := by simp [hl]
  rw [← hw, dot_eqKernelF lv w (by rw [hw, hl]; decide), hw, show keccakBits = 64 * 25 from rfl, sum_range_64]
  unfold weightedRefF
  simp only [sumF_map_range, eqKernelAF_eq, list_toArray_getD]
  refine Finset.sum_congr rfl fun l hl' => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hl'' := Finset.mem_range.mp hl'
  have hz' := Finset.mem_range.mp hz
  rw [E2V.eqKernelF_getD, E2V.eqKernelF_getD, h6, h5, ite_eq_left (by omega), ite_eq_left (by omega)]
  conv_rhs => rw [← List.take_append_drop 6 lv]
  rw [eqAtF_append, h6, show (64 * l + z) % 2 ^ 6 = z by omega, show (64 * l + z) / 2 ^ 6 = l by omega]
  ring

/-- `weighted` on pending or listed weights. -/
def weightedSE2 (lv : List FE2) : LWtsE2 → FE2
  | .mat w => dotF (eqHeadOf lv) w
  | .outer p laneW =>
    if lv.length = 11 ∧ p.length = 6 then
      let c := corrAllF (corrTab2F (lv.take 6) p)
      weightedCF (fun r => c.getD (r % 64) 0) (eqKernelAF (lv.drop 6)) laneW
    else dotF ((eqKernelF lv).take keccakBits) (LWtsE2.outer p laneW).toList

theorem length_linearTransposeF (w : List FE2) : (linearTransposeF w).length = keccakBits := by
  simp [linearTransposeF, keccakBits]

theorem weightedSE2_eq (lv : List FE2) (lw : LWtsE2) :
    weightedSE2 lv lw = dotF ((eqKernelF lv).take keccakBits) lw.toList := by
  cases lw with
  | mat w => rw [weightedSE2, eqHeadOf_eq]; rfl
  | outer p laneW =>
    rw [weightedSE2]
    split
    · rename_i h
      have hc : (fun r => (corrAllF (corrTab2F (lv.take 6) p)).getD (r % 64) 0) =
          corrGF (eqKernelAF p) (eqKernelAF (lv.take 6)) :=
        funext fun r => by rw [corrAllF_getD, corrAF_eq _ _ (by simp [h.1]) h.2]
      dsimp only
      rw [hc, weightedCF_eq, weightedRefF_halves lv _ h.1 (length_linearTransposeF _)]
      rfl
    · rfl

/-- One segment's round-constant sum on pending or listed weights. -/
def rcSumE2 (lw : LWtsE2) (rc : UInt64) : FE2 :=
  match lw with
  | .mat w => rcRefF w rc
  | .outer p laneW => rcOuterF (eqKernelAF p) laneW rc

theorem rcSumE2_eq (lw : LWtsE2) (rc : UInt64) : rcSumE2 lw rc = rcRefF lw.toList rc := by
  cases lw with
  | mat w => rfl
  | outer p laneW => exact rcOuterF_eq _ _ _

/-- `iotaSF` on pending weights. -/
def iotaSFS (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (claim : SClaimE2) : FE2 :=
  let segments := eqKernelF (claim.point.drop (logSteps - 5))
  sumF ((List.range sh.segments).map fun segment =>
    let constant := keccakRC.getD (sh.depth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * rcSumE2 claim.weights constant)

theorem iotaSFS_eq (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (claim : SClaimE2) :
    iotaSFS sh logSteps step claim = iotaSF sh logSteps step claim.toClaim := by
  unfold iotaSFS iotaSF
  simp only [rcSumE2_eq, rcRefF]
  rfl

/-- The next layer's lane factors: `ℓ_l = eqL_l + β·(eqL_{l₄} + β·eqL_{l₃})` (`along` moves lanes only). -/
def laneWF (eqL : Array FE2) (beta : FE2) : Array FE2 :=
  ((List.range 25).map fun l => eqL.getD l 0 + beta *
    (eqL.getD (keccakAlong (64 * l) 4 / 64) 0 + beta * eqL.getD (keccakAlong (64 * l) 3 / 64) 0)).toArray

/-- The next layer's weights: pending on an 11-coordinate point. -/
def nextWE2 (lv : List FE2) (beta : FE2) : LWtsE2 :=
  if lv.length = 11 then .outer (lv.take 6) (laneWF (eqKernelAF (lv.drop 6)) beta)
  else .mat (linearTransposeF ((List.range keccakBits).map fun j => (eqKernelF lv).getD j 0 + beta *
    ((eqKernelF lv).getD (keccakAlong j 4) 0 + beta * (eqKernelF lv).getD (keccakAlong j 3) 0)))

theorem nextWE2_toList (lv : List FE2) (beta : FE2) :
    (nextWE2 lv beta).toList = linearTransposeF ((List.range keccakBits).map fun j => (eqKernelF lv).getD j 0 +
      beta * ((eqKernelF lv).getD (keccakAlong j 4) 0 + beta * (eqKernelF lv).getD (keccakAlong j 3) 0)) := by
  unfold nextWE2
  split
  · rename_i hl
    have h6 : (lv.take 6).length = 6 := by simp [hl]
    have h5 : (lv.drop 6).length = 5 := by simp [hl]
    have hq : ∀ i, i < 1600 → (eqKernelF lv).getD i 0 =
        (eqKernelF (lv.take 6)).getD (i % 64) 0 * (eqKernelF (lv.drop 6)).getD (i / 64) 0 := fun i hi => by
      rw [E2V.eqKernelF_getD, E2V.eqKernelF_getD, E2V.eqKernelF_getD, h6, h5, hl, ite_eq_left (by omega),
        ite_eq_left (by omega), ite_eq_left (by omega)]
      conv_lhs => rw [← List.take_append_drop 6 lv]
      rw [eqAtF_append, h6]
      rfl
    rw [LWtsE2.toList]
    refine congrArg linearTransposeF ?_
    unfold outerUGF laneWF
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 1600 := List.mem_range.mp hj
    have a4 := keccakAlong_lt 4 hj'
    have a3 := keccakAlong_lt 3 hj'
    have m4 : keccakAlong j 4 % 64 = j % 64 := by simp only [keccakAlong]; omega
    have m3 : keccakAlong j 3 % 64 = j % 64 := by simp only [keccakAlong]; omega
    have d4 : keccakAlong j 4 / 64 = keccakAlong (64 * (j / 64)) 4 / 64 := by simp only [keccakAlong]; omega
    have d3 : keccakAlong j 3 / 64 = keccakAlong (64 * (j / 64)) 3 / 64 := by simp only [keccakAlong]; omega
    rw [hq j hj', hq _ a4, hq _ a3, m4, m3, d4, d3, eqKernelAF_eq, eqKernelAF_eq, list_toArray_getD,
      list_toArray_getD, List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
      List.getElem?_range (by omega : j / 64 < 25)]
    simp only [Option.map_some, Option.getD_some, list_toArray_getD]
    ring
  · rw [LWtsE2.toList]

/-- The claim's head (`projectedF` reads only `mu`). -/
def kHead (c : SClaimE2) : KClaim FE2 := ⟨c.value, c.mu, c.point, []⟩

theorem projectedF_kHead (c : SClaimE2) (product : List FE2) :
    projectedF (kHead c) product = projectedF c.toClaim product := rfl

/-! ### VQ-V twins of the layer's list helpers (day-0 VQ-V 4, 5; `verifyKeccakLayerDS` calls them after the freeze) -/

/-- Per product bit `c < productBits`, the instances `i` whose projection mask has bit `c` (`rmfeProject`). -/
def projIdx : Array (Array Nat) :=
  (List.range productBits).toArray.map fun c =>
    ((List.range rmfeProject.length).filter fun i => (rmfeProject.getD i 0).testBit c).toArray

/-- **`projectedF` on arrays** (VQ-V 4): `Σ_c (Σ_{i ∈ projIdx c} μ_i)·product_c`, the index sets once per run. -/
def projectedFF (mu product : List FE2) : FE2 :=
  let m := mu.toArray
  let pr := product.toArray
  (List.range productBits).foldl (fun acc c =>
    acc + (projIdx.getD c #[]).foldl (fun s i => s + m.getD i 0) 0 * pr.getD c 0) 0

theorem foldl_filter_range {F : Type} [Field F] (p : ℕ → Bool) (g : ℕ → F) (a : F) : ∀ n : ℕ,
    ((List.range n).filter p).foldl (fun s i => s + g i) a = a + ∑ i ∈ Finset.range n, if p i then g i else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.foldl_append, foldl_filter_range p g a n, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h, add_assoc]

/-- `sumF_zip_filterMap` without the equal lengths. -/
theorem sumF_zip_filterMapG {F : Type} [Field F] (p : ℕ → Bool) :
    ∀ (l₁ : List F) (l₂ : List ℕ),
      sumF ((List.zip l₁ l₂).filterMap fun (m, mask) ↦ if p mask then some m else none) =
        ∑ i ∈ Finset.range l₂.length, if p (l₂.getD i 0) then l₁.getD i 0 else 0
  | [], l₂ => by simp [sumF]
  | _ :: _, [] => by simp [sumF]
  | x :: l₁, y :: l₂ => by
    rw [List.zip_cons_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sumF_zip_filterMapG p l₁ l₂
    rw [sumF_eq_sum] at ih ⊢
    by_cases hp : p y
    · simp only [List.filterMap_cons, hp, ite_true, List.sum_cons, ih, List.getD_cons_succ, List.getD_cons_zero]
      ring
    · simp only [List.filterMap_cons, hp, ite_false, ih, List.getD_cons_succ, List.getD_cons_zero, add_zero,
        Bool.false_eq_true]

theorem projectedFF_eq (claim : KClaim FE2) (product : List FE2) :
    projectedFF claim.mu product = projectedF claim product := by
  unfold projectedFF projectedF
  rw [sumF, List.foldl_map]
  refine List.foldl_ext _ _ _ fun acc c hc => ?_
  have hc' := List.mem_range.mp hc
  rw [projIdx, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hc',
    Option.map_some, Option.getD_some, List.foldl_toArray]
  simp only [list_toArray_getD]
  rw [foldl_filter_range (fun i => (rmfeProject.getD i 0).testBit c) (fun i => claim.mu.getD i 0), zero_add,
    sumF_zip_filterMapG (fun mask => mask.testBit c)]

/-- Per embedding word `e` of `rmfeEmbed`, the bits `b < embedBits` set in `e`. -/
def embIdx : Array (Array Nat) :=
  rmfeEmbed.toArray.map fun e => ((List.range embedBits).filter fun b => e.testBit b).toArray

/-- **`instWeightsF` on arrays** (VQ-V 5): the powers of `s` once, each word's sum over its index set. -/
def instWeightsFF (s : FE2) : List FE2 :=
  let sp := (powersF s embedBits).toArray
  (embIdx.map fun ix => ix.foldl (fun a b => a + sp.getD b 0) 0).toList

theorem instWeightsFF_eq (s : FE2) : instWeightsFF s = instWeightsF s := by
  unfold instWeightsFF instWeightsF embIdx
  dsimp only
  rw [Array.map_map, Array.toList_map, List.toList_toArray]
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, List.foldl_toArray, list_toArray_getD]
  rw [foldl_filter_range (fun b => e.testBit b) (fun b => (powersF s embedBits).getD b 0), zero_add,
    sumF_filterMap_range]

/-- **`verifyKeccakLayerD` with pending weights**: the same reads, samples and checks; `weighted` and `iota` read
the pending weights, the output's weights stay pending (`nextWE2`). -/
def verifyKeccakLayerDS (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (claim : SClaimE2) :
    DM SClaimE2 := do
  let product ← readE2s productBits
  require (projectedFF claim.mu product + iotaSFS sh logSteps step claim * sumF claim.mu == claim.value)
  sepE2
  let s ← sampleG gC104
  let mu := instWeightsFF s
  let kappa := sumF mu
  let vsp ← packRoundsD gC3 claim.point (polyEvalF product s) 1
  let lv ← sumcheckD gC3 vsp.1 4 (List.replicate keccakLocalBits none)
  let t ← readE2s 3
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  require (vsp.2.1 * weightedSE2 lv.1 claim.weights * (kappa * t0 + (kappa + t1) * t2) == lv.2)
  let beta ← sampleG gC2
  pure ⟨t0 + beta * (t1 + beta * t2), mu, vsp.2.2, nextWE2 lv.1 beta⟩

theorem verifyKeccakLayerDS_eq (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (c : SClaimE2) :
    SClaimE2.toClaim <$> verifyKeccakLayerDS sh logSteps step c = verifyKeccakLayerD sh logSteps step c.toClaim := by
  have hp : ∀ product, projectedFF c.mu product = projectedF (kHead c) product := fun product =>
    projectedFF_eq (kHead c) product
  unfold verifyKeccakLayerDS verifyKeccakLayerD
  simp only [map_bind, map_pure, iotaSFS_eq, weightedSE2_eq, hp, projectedF_kHead, SClaimE2.toClaim, nextWE2_toList,
    instWeightsFF_eq]

/-- The layers with pending weights. -/
def keccakLayersDS (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : Nat) :
    List Nat → SClaimE2 → DM SClaimE2
  | [], claim => pure claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayerDS sh logSteps step claim
    keccakLayersDS sh logSteps steps claim

theorem keccakLayersDS_eq (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : Nat) :
    ∀ (steps : List Nat) (c : SClaimE2),
      SClaimE2.toClaim <$> keccakLayersDS sh logSteps steps c = keccakLayersD sh logSteps steps c.toClaim
  | [], c => by simp only [keccakLayersDS, keccakLayersD, map_pure]
  | step :: steps, c => by
    simp only [keccakLayersDS, keccakLayersD, map_bind, keccakLayersDS_eq sh logSteps steps]
    rw [← verifyKeccakLayerDS_eq, bind_map_left]

/-- `firstWeightsF` at `E2` with `eq(lanes, ·)` and the words `2^i` in arrays (the original rebuilds both for each
of the 1600 bits). -/
def firstWeightsFF (lanesPt : List FE2) : List FE2 :=
  let e := (eqKernelF lanesPt).toArray
  let pw : Array FE2 := (List.range 64).toArray.map fun i => nF (2 ^ i)
  (List.range keccakBits).map fun j => e.getD (j / 64) 0 * pw.getD (j % 64) 0

theorem firstWeightsFF_eq : firstWeightsFF = firstWeightsF (F := FE2) := by
  funext lanesPt
  unfold firstWeightsFF firstWeightsF
  refine List.map_congr_left fun j _ => ?_
  rw [list_toArray_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range (Nat.mod_lt j (by norm_num))]
  rfl

/-! ### VQ-V twin of the first layer's weights (day-0 VQ-V 6; `LWtsE2.first` after the freeze) -/

/-- `x^i` for `i < 64` in `FE2`. -/
def pwA : Array FE2 := (List.range 64).toArray.map fun i => nF (2 ^ i)

/-- **`weighted` on the first claim's weights** (VQ-V 6): `firstWeightsFF lanesPt` is `e ⊗ (x^z)_z`, so at an
11-coordinate point (split `6 + 5`) the 1600-term dot product is `(Σ_{l<25} eqL_l·e_l)·(Σ_{z<64} eqZ_z·x^z)`. -/
def weightedFirst (lv lanesPt : List FE2) : FE2 :=
  let e := eqKernelAF lanesPt
  let eZ := eqKernelAF (lv.take 6)
  let eL := eqKernelAF (lv.drop 6)
  sumF ((List.range 25).map fun l => eL.getD l 0 * e.getD l 0) *
    sumF ((List.range 64).map fun z => eZ.getD z 0 * pwA.getD z 0)

theorem firstWeightsFF_getD (lanesPt : List FE2) {l z : Nat} (hl : l < 25) (hz : z < 64) :
    (firstWeightsFF lanesPt).getD (64 * l + z) 0 = (eqKernelAF lanesPt).getD l 0 * pwA.getD z 0 := by
  rw [firstWeightsFF, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp only [keccakBits]; omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega, eqKernelAF_eq]
  rfl

theorem weightedFirst_eq (lv lanesPt : List FE2) (hl : lv.length = 11) :
    weightedFirst lv lanesPt = dotF ((eqKernelF lv).take keccakBits) (firstWeightsFF lanesPt) := by
  rw [← weightedRefF_halves lv _ hl (by simp [firstWeightsFF, keccakBits])]
  unfold weightedFirst weightedRefF
  simp only [sumF_map_range]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl' => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [list_toArray_getD (firstWeightsFF lanesPt), firstWeightsFF_getD lanesPt (Finset.mem_range.mp hl') (Finset.mem_range.mp hz)]
  ring

/-- One segment's round-constant sum on the first claim's weights (lane `0`: `e_0·x^z`). -/
def rcFirst (lanesPt : List FE2) (rc : UInt64) : FE2 :=
  (eqKernelAF lanesPt).getD 0 0 *
    sumF ((List.range 64).filterMap fun z => if rc.toNat.testBit z then some (pwA.getD z 0) else none)

theorem rcFirst_eq (lanesPt : List FE2) (rc : UInt64) : rcFirst lanesPt rc = rcRefF (firstWeightsFF lanesPt) rc := by
  unfold rcFirst rcRefF
  rw [sumF_filterMap_range 64 (fun z => rc.toNat.testBit z = true), sumF_filterMap_range 64 (fun z => rc.toNat.testBit z = true),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have h := firstWeightsFF_getD lanesPt (l := 0) (by norm_num) (Finset.mem_range.mp hz)
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [h, mul_ite, mul_zero]

/-- **`verifyKeccakLayerDS` on the first claim** (VQ-V 6c): the claim `⟨value, mu, point, .mat (firstWeightsFF lanesPt)⟩`
with its 1600 weights never listed (`iota` by `rcFirst`, `weighted` by `weightedFirst`). -/
def verifyKeccakLayerDS0 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (value : FE2)
    (mu point lanesPt : List FE2) : DM SClaimE2 := do
  let product ← readE2s productBits
  let segments := eqKernelF (point.drop (logSteps - 5))
  let iota := sumF ((List.range sh.segments).map fun segment =>
    let constant := keccakRC.getD (sh.depth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * rcFirst lanesPt constant)
  require (projectedFF mu product + iota * sumF mu == value)
  sepE2
  let s ← sampleG gC104
  let mu' := instWeightsFF s
  let kappa := sumF mu'
  let vsp ← packRoundsD gC3 point (polyEvalF product s) 1
  let lv ← sumcheckD gC3 vsp.1 4 (List.replicate keccakLocalBits none)
  let t ← readE2s 3
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  let w := if lv.1.length = 11 then weightedFirst lv.1 lanesPt
    else dotF ((eqKernelF lv.1).take keccakBits) (firstWeightsFF lanesPt)
  require (vsp.2.1 * w * (kappa * t0 + (kappa + t1) * t2) == lv.2)
  let beta ← sampleG gC2
  pure ⟨t0 + beta * (t1 + beta * t2), mu', vsp.2.2, nextWE2 lv.1 beta⟩

theorem verifyKeccakLayerDS0_eq (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (value : FE2)
    (mu point lanesPt : List FE2) :
    verifyKeccakLayerDS0 sh logSteps step value mu point lanesPt =
      verifyKeccakLayerDS sh logSteps step ⟨value, mu, point, .mat (firstWeightsFF lanesPt)⟩ := by
  have hw : ∀ lv : List FE2, (if lv.length = 11 then weightedFirst lv lanesPt
      else dotF ((eqKernelF lv).take keccakBits) (firstWeightsFF lanesPt)) =
      weightedSE2 lv (.mat (firstWeightsFF lanesPt)) := fun lv => by
    rw [weightedSE2, eqHeadOf_eq]
    split
    · rename_i h; exact weightedFirst_eq lv lanesPt h
    · rfl
  unfold verifyKeccakLayerDS0 verifyKeccakLayerDS iotaSFS
  simp only [rcFirst_eq, hw, rcSumE2]


/-- `firstClaimSF` at `E2` with `firstWeightsFF`. -/
def firstClaimSFF (sh : LeanVM.Protocol.KeccakGkr.Shape) (inst segment lanesPt output : List FE2)
    (committed : FE2) : KClaim FE2 :=
  ⟨committed + (eqKernelF segment).getD (sh.segments - 1) 0 * dotF ((eqKernelF lanesPt).take 25) output,
    eqKernelF (inst.take 5), inst.drop 5 ++ segment, firstWeightsFF lanesPt⟩

theorem firstClaimSFF_eq : firstClaimSFF = firstClaimSF (F := FE2) := by
  funext sh inst segment lanesPt output committed
  unfold firstClaimSFF firstClaimSF
  rw [firstWeightsFF_eq]

/-- `tapeGkrD` with the layers on pending weights. -/
def tapeGkrDF (h : Nat) (inst output : List FE2) : DM (KClaim FE2) := do
  let lanesPt ← samplesG gC1 keccakLaneBits
  let c ← verifyKeccakLayerDS0 LeanVM.Protocol.KeccakGkr.Shape.tape h 0
    (0 + (eqKernelF ([] : List FE2)).getD (LeanVM.Protocol.KeccakGkr.Shape.tape.segments - 1) 0 *
      dotF ((eqKernelF lanesPt).take 25) output) (eqKernelF (inst.take 5)) (inst.drop 5 ++ []) lanesPt
  SClaimE2.toClaim <$> keccakLayersDS LeanVM.Protocol.KeccakGkr.Shape.tape h (List.range' 1 23) c

theorem tapeGkrDF_eq : tapeGkrDF = tapeGkrD := by
  funext h inst output
  unfold tapeGkrDF tapeGkrD
  refine congrArg (_ >>= ·) (funext fun lanesPt => ?_)
  rw [verifyKeccakLayerDS0_eq, show List.range 24 = 0 :: List.range' 1 23 from rfl, ← firstClaimSFF_eq,
    ← SClaimE2.toClaim_ofClaim (firstClaimSFF _ inst [] lanesPt output 0), ← keccakLayersDS_eq, keccakLayersDS,
    map_bind]
  have e : SClaimE2.ofClaim (firstClaimSFF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] lanesPt output 0) =
      ⟨0 + (eqKernelF ([] : List FE2)).getD (LeanVM.Protocol.KeccakGkr.Shape.tape.segments - 1) 0 *
        dotF ((eqKernelF lanesPt).take 25) output, eqKernelF (inst.take 5), inst.drop 5 ++ [],
        .mat (firstWeightsFF lanesPt)⟩ := by
    simp only [SClaimE2.ofClaim, firstClaimSFF]
  rw [e]

/-! ## The row switch's tensor coordinates -/

theorem u64_bit (x : UInt64) (i : Nat) (hi : i < 64) :
    ((x >>> i.toUInt64) &&& 1 != 0) = x.toNat.testBit i := by
  have h1 : ((x >>> i.toUInt64) &&& 1).toNat = (x.toNat >>> i) % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one, Nat.and_one_is_mod]
    have : i.toUInt64.toNat = i := by simp; omega
    rw [this, Nat.mod_eq_of_lt hi]
  rw [Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat >>> i) with h | h
  · rw [h] at h1 ⊢
    have : (x >>> i.toUInt64) &&& 1 = 0 := UInt64.toNat_inj.mp (by simpa using h1)
    simp [this]
  · rw [h] at h1 ⊢
    have : (x >>> i.toUInt64) &&& 1 = 1 := UInt64.toNat_inj.mp (by simpa using h1)
    simp [this]

/-- `bitFE2` by word shifts (`j < 128`). -/
@[inline] def bitFE2F (y : FE2) (j : Nat) : Bool :=
  if j < 64 then (y.re.val >>> j.toUInt64) &&& 1 != 0 else (y.im.val >>> (j - 64).toUInt64) &&& 1 != 0

theorem bitFE2F_eq (y : FE2) (j : Nat) (hj : j < 128) : bitFE2F y j = bitFE2 y j := by
  unfold bitFE2F bitFE2
  split
  · exact u64_bit _ _ ‹_›
  · exact u64_bit _ _ (by omega)

/-- The rows of `z`'s step: row `j` lists the `k < 128` with bit `j` of `β_k·z`. -/
def tRowsF (z : FE2) : Array (List Nat) :=
  let w : Array FE2 := (List.range 128).toArray.map fun k => basisFE2 k * z
  (List.range 128).toArray.map fun j => (List.range 128).filter fun k => bitFE2F (w.getD k 0) j

/-- `⟨a, b, c⟩ + Σ_{k ∈ ks} v_k`, the sum on unboxed words. -/
def sumAtW (v : Array FE) : List Nat → FK → FK → FK → FE
  | [], a, b, c => ⟨a, b, c⟩
  | k :: ks, a, b, c =>
    let x := v.getD k 0
    sumAtW v ks (a + x.c₀) (b + x.c₁) (c + x.c₂)

/-- `tensorStepD` from the rows. -/
def tensorStepF (v : Array FE) (rr : Array (List Nat) × FE) : Array FE :=
  (List.range 128).toArray.map fun j =>
    (1 + rr.2) * v.getD j 0 + sumAtW v (rr.1.getD j []) 0 0 0

/-- `tensorWD` from the rows of each `z_l`. -/
def tensorWDF (rows : List (Array (List Nat))) (r : List FE) : Array FE :=
  (List.zip rows r).foldl tensorStepF ((List.range 128).toArray.map fun j => if j = 0 then 1 else 0)

theorem sum_filter_range (p : Nat → Bool) (g : Nat → FE) :
    ∀ n, (((List.range n).filter p).map g).sum = ∑ k ∈ Finset.range n, if p k then g k else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, sum_filter_range p g n,
      Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem sumAtW_eq (v : Array FE) :
    ∀ (L : List Nat) (a b c : FK), sumAtW v L a b c = ⟨a, b, c⟩ + (L.map fun k => v.getD k 0).sum
  | [], a, b, c => by simp [sumAtW]
  | k :: L, a, b, c => by
    rw [sumAtW, sumAtW_eq v L, List.map_cons, List.sum_cons, ← add_assoc]
    rfl

theorem tensorStepF_eq (v : Array FE) (z : FE2) (r : FE) :
    tensorStepF v (tRowsF z, r) = tensorStepD v (z, r) := by
  have hnd : ∀ k, (((List.range 128).toArray.map fun k ↦ (List.range 128).filter fun j ↦
      bitFE2 (basisFE2 k * z) j).getD k []).Nodup := fun k ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray]
    rcases (List.range 128)[k]? with _ | k' <;> simp [List.nodup_range.filter]
  have hlt : ∀ k, ∀ x ∈ ((List.range 128).toArray.map fun k ↦ (List.range 128).filter fun j ↦
      bitFE2 (basisFE2 k * z) j).getD k [], x < 128 := fun k x hx ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray] at hx
    rcases h : (List.range 128)[k]? with _ | k' <;> rw [h] at hx
    · simp at hx
    · exact List.mem_range.mp (List.mem_filter.mp hx).1
  have getD_map128 : ∀ {β : Type} (f : Nat → β) (d : β) (k : Nat), k < 128 →
      ((List.range 128).toArray.map f).getD k d = f k := fun f d k hk ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hk]
    rfl
  unfold tensorStepF tensorStepD
  rw [List.map_toArray, List.map_toArray]
  congr 1
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < 128 := List.mem_range.mp hj
  rw [(getD_foldl_tensor _ v hnd hlt 128).2 j, sumAtW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add]
  congr 1
  have hrow : (tRowsF z).getD j [] = (List.range 128).filter fun k => bitFE2 (basisFE2 k * z) j := by
    unfold tRowsF
    rw [getD_map128 _ _ _ hj']
    refine List.filter_congr fun k hk ↦ ?_
    rw [getD_map128 _ _ _ (List.mem_range.mp hk), bitFE2F_eq _ _ hj']
  simp only
  rw [hrow, sum_filter_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [getD_map128 _ _ _ (Finset.mem_range.mp hk)]
  simp [hj']

theorem tensorWDF_eq (z : List FE2) (r : List FE) : tensorWDF (z.map tRowsF) r = tensorWD z r := by
  unfold tensorWDF tensorWD
  rw [List.zip_map_left, List.foldl_map]
  congr 1
  funext v p
  exact tensorStepF_eq v p.1 p.2

/-! ### The switched weight by the transposed steps

`Σ_j eq_j·t_j` with `t = A_L ⋯ A_1 e₀`, `A_l v = (1 + r_l)·v + M_{z_l} v` and `(M_z v)_j = Σ_{k : bit j of β_k z} v_k`,
is `(A_1ᵀ ⋯ A_Lᵀ eq)_0`, and `(M_zᵀ u)_k = Σ_{j : bit j of β_k z} u_j` reads the words `β_k·z` directly: no rows. -/

private theorem sumE_sum' (l : List FE) : sumE l = l.sum := by
  suffices h : ∀ a : FE, l.foldl (· + ·) a = a + l.sum by rw [sumE, h, zero_add]
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

private theorem list_sum_range' (f : Nat → FE) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range' f n, Finset.sum_range_succ]
    simp

/-- The words `β_k·z` of `z`'s step. -/
def tColsW (z : FE2) : Array FE2 := (List.range 128).toArray.map fun k => basisFE2 k * z

/-! ### VQ-V twin of the switch words (day-0 VQ-V 7; `rowSwitchDR` calls it after the freeze) -/

/-- The words `2^i`, `i < 64` (`basisFE2`'s). -/
def pw64 : Array FK := (List.range 64).toArray.map fun i => ⟨(2 ^ i : Nat).toUInt64⟩

/-- **`tColsW` by `K` scalings** (VQ-V 7): `β_k·z = z·2^k` for `k < 64`, `(y·z)·2^(k−64)` above (`mulK`: two `FK`
products, against `FE2.mul`'s four). -/
def tColsWF (z : FE2) : Array FE2 :=
  let yz := (⟨0, 1⟩ : FE2) * z
  (List.range 128).toArray.map fun k =>
    if k < 64 then z.mulK (pw64.getD k 0) else yz.mulK (pw64.getD (k - 64) 0)

theorem fe2_mulK_eq (a : FE2) (k : FK) : a.mulK k = a * FE2.ofK k :=
  FE2.toE2_injective (by rw [FE2.toE2_mulK, FE2.fe2_mul_eq, FE2.toE2_ofK])

theorem pw64_getD {k : Nat} (hk : k < 64) : pw64.getD k 0 = ⟨(2 ^ k : Nat).toUInt64⟩ := by
  rw [pw64, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hk]
  rfl

theorem tColsWF_eq (z : FE2) : tColsWF z = tColsW z := by
  unfold tColsWF tColsW
  rw [List.map_toArray, List.map_toArray]
  refine congrArg List.toArray (List.map_congr_left fun k hk => ?_)
  have hk' := List.mem_range.mp hk
  unfold basisFE2
  split
  · rename_i hk
    rw [pw64_getD hk, fe2_mulK_eq, mul_comm]
    rfl
  · rename_i hk
    rw [pw64_getD (by omega), fe2_mulK_eq]
    have e : (⟨0, ⟨(2 ^ (k - 64) : Nat).toUInt64⟩⟩ : FE2) = ⟨0, 1⟩ * FE2.ofK ⟨(2 ^ (k - 64) : Nat).toUInt64⟩ := by
      rw [← fe2_mulK_eq]
      show _ = (⟨0 * _, 1 * _⟩ : FE2)
      rw [zero_mul, one_mul]
    rw [e]
    ring

/-- `⟨a, b, c⟩ + Σ_{j ≤ i < j + n, bit i of w} u_i` on unboxed words. -/
def sumBitsW (u : Array FE) (w : FE2) : Nat → Nat → FK → FK → FK → FE
  | 0, _, a, b, c => ⟨a, b, c⟩
  | n + 1, j, a, b, c =>
    if bitFE2F w j then
      let x := u.getD j 0
      sumBitsW u w n (j + 1) (a + x.c₀) (b + x.c₁) (c + x.c₂)
    else sumBitsW u w n (j + 1) a b c

theorem sumBitsW_eq (u : Array FE) (w : FE2) : ∀ (n j : Nat) (a b c : FK),
    sumBitsW u w n j a b c = ⟨a, b, c⟩ + ∑ i ∈ Finset.range n, if bitFE2F w (j + i) then u.getD (j + i) 0 else 0
  | 0, j, a, b, c => by simp [sumBitsW]
  | n + 1, j, a, b, c => by
    rw [sumBitsW, Finset.sum_range_succ', add_zero,
      Finset.sum_congr rfl fun x _ => by rw [show j + (x + 1) = j + 1 + x by omega]]
    by_cases h : bitFE2F w j = true
    · simp only [h, ↓reduceIte, sumBitsW_eq u w n (j + 1)]
      rw [show (⟨a + (u.getD j 0).c₀, b + (u.getD j 0).c₁, c + (u.getD j 0).c₂⟩ : FE) = ⟨a, b, c⟩ + u.getD j 0
        from rfl]
      abel
    · simp only [h, ↓reduceIte, sumBitsW_eq u w n (j + 1), add_zero, Bool.false_eq_true]

/-- `A_lᵀ`: `u_k ↦ (1 + r)·u_k + Σ_{j : bit j of β_k z} u_j`, for the words `cols` of `z`. -/
def tStepT (cr : Array FE2 × FE) (u : Array FE) : Array FE :=
  (List.range 128).toArray.map fun k => (1 + cr.2) * u.getD k 0 + sumBitsW u (cr.1.getD k 0) 128 0 0 0 0

private theorem getD_map32 {β : Type} (f : Nat → β) (d : β) {k : Nat} (hk : k < 32) :
    ((List.range 32).toArray.map f).getD k d = f k := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hk]
  rfl

/-! ### The transposed step by nibble tables

`Σ_{j : bit j of w} u_j` as `Σ_{n<32} T_n[nibble n of w]`, `T_n[m] = Σ_{i<4, bit i of m} u_{4n+i}`: 32 lookups per word
instead of 128 bit tests. -/

/-- The nibble `n < 32` of `w` (bits `4n … 4n + 3`). -/
@[inline] def nibW (w : FE2) (n : Nat) : Nat :=
  if n < 16 then ((w.re.val >>> (4 * n).toUInt64) &&& 15).toNat
  else ((w.im.val >>> (4 * (n - 16)).toUInt64) &&& 15).toNat

/-- The subset sums of `u_{4n}, …, u_{4n+3}`. -/
def nibTab (u : Array FE) (n : Nat) : Array FE :=
  (List.range 16).toArray.map fun m =>
    (if m.testBit 0 then u.getD (4 * n) 0 else 0) + (if m.testBit 1 then u.getD (4 * n + 1) 0 else 0) +
      (if m.testBit 2 then u.getD (4 * n + 2) 0 else 0) + (if m.testBit 3 then u.getD (4 * n + 3) 0 else 0)

/-- The 16 subset sums of `a, b, c, d` (index bit `i` selects the `i`-th) with 11 additions. -/
@[inline] def nib16 (a b c d : FE) : Array FE :=
  let ab := a + b
  let ac := a + c
  let bc := b + c
  let abc := ab + c
  #[0, a, b, ab, c, ac, bc, abc, d, a + d, b + d, ab + d, c + d, ac + d, bc + d, abc + d]

/-- **`nibTab` by `nib16`** (day-0 VQ-V 9, optional; `tStepN` calls it after the freeze, `tStepN_eq` keeps its
statement). -/
def nibTabQ (u : Array FE) (n : Nat) : Array FE :=
  nib16 (u.getD (4 * n) 0) (u.getD (4 * n + 1) 0) (u.getD (4 * n + 2) 0) (u.getD (4 * n + 3) 0)

theorem nibTabQ_eq (u : Array FE) (n : Nat) : nibTabQ u n = nibTab u n := by
  unfold nibTabQ nib16 nibTab
  rw [List.map_toArray]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil]
  simp (config := { decide := true }) only [ite_true, ite_false, add_zero, zero_add]

/-- `⟨a, b, c⟩ + Σ_{n ≤ i < n + k} T_i[nibble i of w]` on unboxed words. -/
def sumNibW (T : Array (Array FE)) (w : FE2) : Nat → Nat → FK → FK → FK → FE
  | 0, _, a, b, c => ⟨a, b, c⟩
  | k + 1, n, a, b, c =>
    let x := (T.getD n #[]).getD (nibW w n) 0
    sumNibW T w k (n + 1) (a + x.c₀) (b + x.c₁) (c + x.c₂)

/-- `tStepT` by the nibble tables (`tStepN`'s form before VQ2-W). -/
def tStepNB (cr : Array FE2 × FE) (u : Array FE) : Array FE :=
  let T := (List.range 32).toArray.map (nibTabQ u)
  let r1 := 1 + cr.2
  (List.range 128).toArray.map fun k => r1 * u.getD k 0 + sumNibW T (cr.1.getD k 0) 32 0 0 0 0

theorem sumNibW_eq (T : Array (Array FE)) (w : FE2) : ∀ (k n : Nat) (a b c : FK),
    sumNibW T w k n a b c = ⟨a, b, c⟩ + ∑ i ∈ Finset.range k, (T.getD (n + i) #[]).getD (nibW w (n + i)) 0
  | 0, n, a, b, c => by simp [sumNibW]
  | k + 1, n, a, b, c => by
    rw [sumNibW, sumNibW_eq T w k (n + 1), Finset.sum_range_succ', add_zero,
      Finset.sum_congr rfl (g := fun x => (T.getD (n + (x + 1)) #[]).getD (nibW w (n + (x + 1))) 0)
        (fun x _ => by rw [show n + 1 + x = n + (x + 1) by omega])]
    rw [show (⟨a + ((T.getD n #[]).getD (nibW w n) 0).c₀, b + ((T.getD n #[]).getD (nibW w n) 0).c₁,
        c + ((T.getD n #[]).getD (nibW w n) 0).c₂⟩ : FE) = ⟨a, b, c⟩ + (T.getD n #[]).getD (nibW w n) 0 from rfl]
    abel

theorem nibW_bit (w : FE2) {n i : Nat} (hn : n < 32) (hi : i < 4) :
    (nibW w n).testBit i = bitFE2F w (4 * n + i) := by
  have key : ∀ (x : UInt64) (q : Nat), q < 16 →
      ((x >>> (4 * q).toUInt64) &&& 15).toNat.testBit i = x.toNat.testBit (4 * q + i) := fun x q hq => by
    have h4 : (4 * q).toUInt64.toNat % 64 = 4 * q := by simp; omega
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, h4, Nat.testBit_and, Nat.testBit_shiftRight,
      show (UInt64.toNat 15).testBit i = true by interval_cases i <;> rfl, Bool.and_true]
  unfold nibW bitFE2F
  by_cases h : n < 16
  · rw [ite_eq_left h, ite_eq_left (by omega), key _ _ h, u64_bit _ _ (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega), key _ _ (by omega), u64_bit _ _ (by omega),
      show 4 * (n - 16) + i = 4 * n + i - 64 by omega]

theorem nibW_lt (w : FE2) (n : Nat) : nibW w n < 16 := by
  unfold nibW
  split <;> (rw [UInt64.toNat_and]; exact Nat.lt_succ_of_le (Nat.and_le_right))

theorem nibTab_getD (u : Array FE) (n : Nat) {m : Nat} (hm : m < 16) :
    (nibTab u n).getD m 0 = ∑ i ∈ Finset.range 4, if m.testBit i then u.getD (4 * n + i) 0 else 0 := by
  rw [nibTab, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hm]
  simp only [Option.map_some, Option.getD_some, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]

theorem sum_range_4 (f : Nat → FE) : ∀ n,
    ∑ j ∈ Finset.range (4 * n), f j = ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range 4, f (4 * m + i)
  | 0 => by simp
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, Finset.sum_range_add, sum_range_4 f n,
      Finset.sum_range_succ (fun m => ∑ i ∈ Finset.range 4, f (4 * m + i)) n]

theorem tStepNB_eq : tStepNB = tStepT := by
  funext cr u
  unfold tStepNB tStepT
  rw [show nibTabQ u = nibTab u from funext (nibTabQ_eq u)]
  simp only
  refine congrArg (Array.map · _) (funext fun k => ?_)
  congr 1
  rw [sumNibW_eq, sumBitsW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add, zero_add,
    show (128 : Nat) = 4 * 32 from rfl, sum_range_4]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.mp hn
  rw [zero_add, getD_map32 _ _ hn', nibTab_getD _ _ (nibW_lt _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [nibW_bit _ hn' (Finset.mem_range.mp hi), zero_add]

/-! ### The step at a `0` or `1` coordinate without products (VQ2-W)

The small shape's regions relocate the point's top coordinates to selector bits: there `(1 + r)·u_k` is `u_k` (`r = 0`) or
`0` (`r = 1`), and the step is the nibble sums alone. Each sum starts from the product's (or `u_k`'s) words. -/

theorem fe_one_add_one : (1 : FE) + 1 = 0 := CharTwo.add_self_eq_zero 1

/-- **`tStepT` by the nibble tables** (VQ2-W: no products at a `0` or `1` coordinate; `tStepNB` before). -/
def tStepN (cr : Array FE2 × FE) (u : Array FE) : Array FE :=
  let T := (List.range 32).toArray.map (nibTabQ u)
  if cr.2 = 0 then
    (List.range 128).toArray.map fun k => let a := u.getD k 0; sumNibW T (cr.1.getD k 0) 32 0 a.c₀ a.c₁ a.c₂
  else if cr.2 = 1 then
    (List.range 128).toArray.map fun k => sumNibW T (cr.1.getD k 0) 32 0 0 0 0
  else
    let r1 := 1 + cr.2
    (List.range 128).toArray.map fun k => let a := r1 * u.getD k 0; sumNibW T (cr.1.getD k 0) 32 0 a.c₀ a.c₁ a.c₂

theorem tStepN_eq_B : tStepN = tStepNB := by
  funext cr u
  unfold tStepN tStepNB
  simp only
  split
  · rename_i h
    refine congrArg (Array.map · _) (funext fun k => ?_)
    rw [sumNibW_eq, sumNibW_eq, h, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, add_zero, one_mul, zero_add]
  · split
    · rename_i _ h
      refine congrArg (Array.map · _) (funext fun k => ?_)
      rw [h, fe_one_add_one, zero_mul, zero_add]
    · refine congrArg (Array.map · _) (funext fun k => ?_)
      rw [sumNibW_eq, sumNibW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add]

theorem tStepN_eq : tStepN = tStepT := by rw [tStepN_eq_B, tStepNB_eq]

/-- The switched weight `Σ_j eq_j·tensorW(z, r)_j` by the transposed steps (`cols = z.map tColsW`). -/
def tensorDotT (cols : List (Array FE2)) (eqA : Array FE) (r : List FE) : FE :=
  ((List.zip cols r).foldr tStepN eqA).getD 0 0

private theorem getD_map128' {β : Type} (f : Nat → β) (d : β) {k : Nat} (hk : k < 128) :
    ((List.range 128).toArray.map f).getD k d = f k := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hk]
  rfl

/-- The step's coordinate `j < 128` (`tensorStepD`): `(1 + r)·v_j + Σ_{k : bit j of β_k z} v_k`. -/
theorem tensorStepD_getD (v : Array FE) (z : FE2) (r : FE) {j : Nat} (hj : j < 128) :
    (tensorStepD v (z, r)).getD j 0 =
      (1 + r) * v.getD j 0 + ∑ k ∈ Finset.range 128, if bitFE2F (basisFE2 k * z) j then v.getD k 0 else 0 := by
  rw [← tensorStepF_eq, tensorStepF, getD_map128' _ _ hj, sumAtW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add]
  congr 1
  unfold tRowsF
  rw [getD_map128' _ _ hj, sum_filter_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [getD_map128' _ _ (Finset.mem_range.mp hk)]

/-- **One step's adjoint**: `Σ_j u_j·(A v)_j = Σ_k (Aᵀ u)_k·v_k`. -/
theorem tStepT_getD (u : Array FE) (z : FE2) (r : FE) {k : Nat} (hk : k < 128) :
    (tStepT (tColsW z, r) u).getD k 0 =
      (1 + r) * u.getD k 0 + ∑ j ∈ Finset.range 128, if bitFE2F (basisFE2 k * z) j then u.getD j 0 else 0 := by
  rw [tStepT, getD_map128' _ _ hk, sumBitsW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add]
  unfold tColsW
  rw [getD_map128' _ _ hk]
  simp only [zero_add]

/-- **One step's adjoint**: `Σ_j u_j·(A v)_j = Σ_k (Aᵀ u)_k·v_k`. -/
theorem tStep_adjoint (u v : Array FE) (z : FE2) (r : FE) :
    ∑ j ∈ Finset.range 128, u.getD j 0 * (tensorStepD v (z, r)).getD j 0 =
      ∑ k ∈ Finset.range 128, (tStepT (tColsW z, r) u).getD k 0 * v.getD k 0 := by
  have hL : ∑ j ∈ Finset.range 128, u.getD j 0 * (tensorStepD v (z, r)).getD j 0 =
      ∑ j ∈ Finset.range 128, u.getD j 0 * ((1 + r) * v.getD j 0 +
        ∑ k ∈ Finset.range 128, if bitFE2F (basisFE2 k * z) j then v.getD k 0 else 0) :=
    Finset.sum_congr rfl fun j hj => by rw [tensorStepD_getD v z r (Finset.mem_range.mp hj)]
  have hR : ∑ k ∈ Finset.range 128, (tStepT (tColsW z, r) u).getD k 0 * v.getD k 0 =
      ∑ k ∈ Finset.range 128, ((1 + r) * u.getD k 0 +
        ∑ j ∈ Finset.range 128, if bitFE2F (basisFE2 k * z) j then u.getD j 0 else 0) * v.getD k 0 :=
    Finset.sum_congr rfl fun k hk => by rw [tStepT_getD u z r (Finset.mem_range.mp hk)]
  rw [hL, hR]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => by ring) (Finset.sum_congr rfl fun j _ => by ring)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp

theorem foldl_adjoint (u : Array FE) : ∀ (ps : List (FE2 × FE)) (v : Array FE),
    ∑ j ∈ Finset.range 128, u.getD j 0 * (ps.foldl tensorStepD v).getD j 0 =
      ∑ k ∈ Finset.range 128, ((ps.map fun p => (tColsW p.1, p.2)).foldr tStepT u).getD k 0 * v.getD k 0
  | [], v => rfl
  | p :: ps, v => by
    rw [List.foldl_cons, foldl_adjoint u ps, List.map_cons, List.foldr_cons]
    exact tStep_adjoint _ v p.1 p.2

theorem tensorDotT_eq (z : List FE2) (eqR : List FE) (r : List FE) :
    tensorDotT (z.map tColsW) eqR.toArray r =
      sumE ((List.range 128).map fun j => eqR.getD j 0 * (tensorWD z r).getD j 0) := by
  rw [sumE_sum', list_sum_range']
  simp only [← list_toArray_getD eqR]
  unfold tensorWD tensorDotT
  rw [tStepN_eq, foldl_adjoint, List.zip_map_left]
  rw [Finset.sum_eq_single 0 (fun k hk hk0 => by rw [getD_map128' _ _ (Finset.mem_range.mp hk), ite_eq_right hk0,
    mul_zero]) (by simp), getD_map128' _ _ (by norm_num), ite_eq_left rfl, mul_one]
  rfl

/-- The 4-bit pattern of coordinate `j` in the words `cw[4g], …, cw[4g+3]` (bit `i`: bit `j` of `cw[4g+i]`). -/
@[inline] def patN (cw : Array FE2) (g j : Nat) : Nat :=
  (bitFE2F (cw.getD (4 * g) 0) j).toNat + 2 * (bitFE2F (cw.getD (4 * g + 1) 0) j).toNat +
    4 * (bitFE2F (cw.getD (4 * g + 2) 0) j).toNat + 8 * (bitFE2F (cw.getD (4 * g + 3) 0) j).toNat

theorem pat4_bit : ∀ (b0 b1 b2 b3 : Bool) (i : Fin 4),
    (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat).testBit i = [b0, b1, b2, b3].getD i false := by
  decide

theorem pat4_lt : ∀ (b0 b1 b2 b3 : Bool), b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat < 16 := by
  decide

/-- A coordinate's 4-bit pattern from the four words of a group (`patN`'s form). -/
@[inline] def patW (w0 w1 w2 w3 : FE2) (j : Nat) : Nat :=
  (bitFE2F w0 j).toNat + 2 * (bitFE2F w1 j).toNat + 4 * (bitFE2F w2 j).toNat + 8 * (bitFE2F w3 j).toNat

/-- **The patterns of a step** (entry `128·g + j` is `patN cw g j`), each group's words read once. -/
def patsA (cw : Array FE2) : Array Nat :=
  ((List.range 32).flatMap fun g =>
    let w0 := cw.getD (4 * g) 0
    let w1 := cw.getD (4 * g + 1) 0
    let w2 := cw.getD (4 * g + 2) 0
    let w3 := cw.getD (4 * g + 3) 0
    (List.range 128).map fun j => patW w0 w1 w2 w3 j).toArray

theorem flatMap_range_len {α : Type} (f : Nat → List α) (hf : ∀ g, (f g).length = 128) :
    ∀ n, ((List.range n).flatMap f).length = 128 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_len f hf n, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hf]
    ring

theorem flatMap_range_getD {α : Type} (f : Nat → List α) (hf : ∀ g, (f g).length = 128) (d : α) :
    ∀ (n g j : Nat), g < n → j < 128 → ((List.range n).flatMap f).getD (128 * g + j) d = (f g).getD j d
  | 0, g, j, hg, _ => absurd hg (Nat.not_lt_zero _)
  | n + 1, g, j, hg, hj => by
    have hlen := flatMap_range_len f hf n
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases h : g < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega), flatMap_range_getD f hf d n g j h hj]
    · have hg' : g = n := by omega
      subst hg'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]

theorem patsA_getD (cw : Array FE2) {g j : Nat} (hg : g < 32) (hj : j < 128) :
    (patsA cw).getD (128 * g + j) 0 = patN cw g j := by
  rw [patsA, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    flatMap_range_getD _ (fun g => by simp) 0 32 g j hg hj, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj]
  rfl

/-- `⟨a, b, c⟩ + Σ_{g ≤ i < g + k} T_i[pt i]` on unboxed words (`pt` the coordinate's patterns). -/
def sumPatW (T : Array (Array FE)) (pt : Nat → Nat) : Nat → Nat → FK → FK → FK → FE
  | 0, _, a, b, c => ⟨a, b, c⟩
  | k + 1, g, a, b, c =>
    let x := (T.getD g #[]).getD (pt g) 0
    sumPatW T pt k (g + 1) (a + x.c₀) (b + x.c₁) (c + x.c₂)

theorem sumPatW_eq (T : Array (Array FE)) (pt : Nat → Nat) : ∀ (k g : Nat) (a b c : FK),
    sumPatW T pt k g a b c = ⟨a, b, c⟩ + ∑ i ∈ Finset.range k, (T.getD (g + i) #[]).getD (pt (g + i)) 0
  | 0, g, a, b, c => by simp [sumPatW]
  | k + 1, g, a, b, c => by
    rw [sumPatW, sumPatW_eq T pt k (g + 1), Finset.sum_range_succ', add_zero,
      Finset.sum_congr rfl (g := fun x => (T.getD (g + (x + 1)) #[]).getD (pt (g + (x + 1))) 0)
        (fun x _ => by rw [show g + 1 + x = g + (x + 1) by omega])]
    rw [show (⟨a + ((T.getD g #[]).getD (pt g) 0).c₀, b + ((T.getD g #[]).getD (pt g) 0).c₁,
        c + ((T.getD g #[]).getD (pt g) 0).c₂⟩ : FE) = ⟨a, b, c⟩ + (T.getD g #[]).getD (pt g) 0 from rfl]
    abel

/-- **The forward step on the words** (`tensorStepD` with `β_k·z` given, `tColsW z`), by nibble tables over `u` and
each coordinate's 4-bit patterns (the transposed `tStepN`). -/
def fwdStepN (cw : Array FE2) (r : FE) (u : Array FE) : Array FE :=
  let T := (List.range 32).toArray.map (nibTab u)
  let P := patsA cw
  (List.range 128).toArray.map fun j => (1 + r) * u.getD j 0 + sumPatW T (fun g => P.getD (128 * g + j) 0) 32 0 0 0 0

theorem fwdStepN_getD (z : FE2) (r : FE) (u : Array FE) {j : Nat} (hj : j < 128) :
    (fwdStepN (tColsW z) r u).getD j 0 =
      (1 + r) * u.getD j 0 + ∑ k ∈ Finset.range 128, if bitFE2F (basisFE2 k * z) j then u.getD k 0 else 0 := by
  rw [fwdStepN, getD_map128' _ _ hj, sumPatW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add,
    show (128 : Nat) = 4 * 32 from rfl, sum_range_4]
  congr 1
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := Finset.mem_range.mp hg
  rw [zero_add, getD_map32 _ _ hg', patsA_getD _ hg' hj, patN, nibTab_getD _ _ (pat4_lt _ _ _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hb := pat4_bit (bitFE2F ((tColsW z).getD (4 * g) 0) j) (bitFE2F ((tColsW z).getD (4 * g + 1) 0) j)
    (bitFE2F ((tColsW z).getD (4 * g + 2) 0) j) (bitFE2F ((tColsW z).getD (4 * g + 3) 0) j) ⟨i, hi'⟩
  simp only at hb
  rw [hb]
  have hcol : ∀ k, k < 128 → (tColsW z).getD k 0 = basisFE2 k * z := fun k hk => by
    unfold tColsW; rw [getD_map128' _ _ hk]
  interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] <;>
    rw [hcol _ (by omega)]

theorem fwdStepN_eq (z : FE2) (r : FE) (u : Array FE) : fwdStepN (tColsW z) r u = tensorStepD u (z, r) := by
  have key : ∀ j < 128, (fwdStepN (tColsW z) r u).getD j 0 = (tensorStepD u (z, r)).getD j 0 := fun j hj => by
    rw [fwdStepN_getD z r u hj, tensorStepD_getD u z r hj]
  apply Array.ext
  · simp [fwdStepN, tensorStepD]
  · intro i h1 h2
    have hi : i < 128 := by simpa [fwdStepN] using h1
    have h := key i hi
    rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at h

/-- `e₀` on the 128 coordinates. -/
def e0A : Array FE := (List.range 128).toArray.map fun j => if j = 0 then 1 else 0

/-- The forward product over the coordinates `a` (`tensorWD` on the words). -/
def rowPre (cols : List (Array FE2)) (a : List FE) : Array FE :=
  (List.zip cols a).foldl (fun u p => fwdStepN p.1 p.2 u) e0A

/-- The transposed product over the coordinates `b` from `eq(r'', ·)` (`tensorDotT`'s fold). -/
def rowSuf (cols : List (Array FE2)) (eqA : Array FE) (b : List FE) : Array FE :=
  (List.zip cols b).foldr tStepN eqA

/-- `Σ_{k < 128} u_k·v_k`. -/
def dot128 (u v : Array FE) : FE := (List.range 128).foldl (fun acc k => acc + u.getD k 0 * v.getD k 0) 0

theorem dot128_eq (u v : Array FE) : dot128 u v = ∑ k ∈ Finset.range 128, u.getD k 0 * v.getD k 0 := by
  unfold dot128
  rw [← list_sum_range', List.sum_eq_foldl, List.foldl_map]

theorem rowPre_eq (z : List FE2) (a : List FE) :
    rowPre (z.map tColsW) a = (List.zip z a).foldl tensorStepD e0A := by
  unfold rowPre
  rw [List.zip_map_left, List.foldl_map]
  exact List.foldl_ext _ _ _ fun u p _ => fwdStepN_eq p.1 p.2 u

/-- **The split of the row weight**: on `a ++ b` with `|a| ≤ |z|`, the forward product over `a` against the transposed
product over `b`. -/
theorem tensorDotT_split (z : List FE2) (eqA : Array FE) (a b : List FE) (ha : a.length ≤ z.length) :
    tensorDotT (z.map tColsW) eqA (a ++ b) =
      dot128 (rowPre ((z.map tColsW).take a.length) a) (rowSuf ((z.map tColsW).drop a.length) eqA b) := by
  unfold tensorDotT rowSuf
  have hz : ((z.map tColsW).take a.length).length = a.length := by
    rw [List.length_take, List.length_map]; omega
  rw [show z.map tColsW = (z.map tColsW).take a.length ++ (z.map tColsW).drop a.length from
    (List.take_append_drop _ _).symm, List.zip_append hz, List.foldr_append, List.take_append_drop]
  rw [← List.map_take, rowPre_eq, dot128_eq, tStepN_eq]
  have hzip : ∀ (l : List FE2) (c : List FE), (l.map tColsW).zip c = (l.zip c).map (fun p => (tColsW p.1, p.2)) := by
    intro l
    induction l with
    | nil => intro c; rfl
    | cons x l ih => intro c; cases c with
      | nil => rfl
      | cons y c => simp only [List.map_cons, List.zip_cons_cons, ih]
  rw [hzip]
  have h := foldl_adjoint (List.foldr tStepT eqA (List.zip (List.drop a.length (z.map tColsW)) b))
    (List.zip (z.take a.length) a) e0A
  have e0s : ∀ (w : Array FE), ∑ k ∈ Finset.range 128, w.getD k 0 * e0A.getD k 0 = w.getD 0 0 := by
    intro w
    rw [Finset.sum_eq_single 0 (fun k hk hk0 => by rw [e0A, getD_map128' _ _ (Finset.mem_range.mp hk),
      ite_eq_right hk0, mul_zero]) (by simp), e0A, getD_map128' _ _ (by norm_num), ite_eq_left rfl, mul_one]
  rw [← e0s, ← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### The prefix's first steps by terms (VQ2-W)

From `e₀` the forward steps `A_l = (1 + r_l) + M_{z_l}` keep the vector a sum `Σ_S w_S·b_S` of `2^l` terms: `w_S` the
product of `1 + r_l` over the steps outside `S`, `b_S` the bit word `M_S e₀` (`M_z b` is the xor of the words `β_k·z`
over the bits `k` of `b`). After `symK` steps the row weight `tensorDotT` is `Σ_S w_S·σ(b_S)` against the transposed
product of the other steps (`tensorDotT_split`), `σ(b) = Σ_{j : bit j of b} V_j` by `V`'s nibble tables: `2^symK`
lookup sums and products in place of `symK` steps of 128 products and 4096 lookups each. -/

theorem bitFE2F_add (a b : FE2) {j : Nat} (hj : j < 128) :
    bitFE2F (a + b) j = (bitFE2F a j != bitFE2F b j) := by
  have key : ∀ (x y : UInt64) (i : Nat), i < 64 →
      ((x ^^^ y) >>> i.toUInt64 &&& 1 != 0) = ((x >>> i.toUInt64 &&& 1 != 0) != (y >>> i.toUInt64 &&& 1 != 0)) := by
    intro x y i hi
    rw [u64_bit _ _ hi, u64_bit _ _ hi, u64_bit _ _ hi, UInt64.toNat_xor, Nat.testBit_xor]
  unfold bitFE2F
  split
  · exact key a.re.val b.re.val j ‹_›
  · exact key a.im.val b.im.val (j - 64) (by omega)

theorem bitFE2F_e0 {j : Nat} (hj : j < 128) : bitFE2F (⟨1, 0⟩ : FE2) j = decide (j = 0) := by
  unfold bitFE2F
  split
  · rename_i h
    rw [u64_bit _ _ h]
    show Nat.testBit 1 j = _
    by_cases h0 : j = 0
    · subst h0; rfl
    · have : Nat.testBit 1 j ≠ true := fun e => h0 (Nat.testBit_one_eq_true_iff_self_eq_zero.mp e)
      simp_all
  · rename_i h
    rw [u64_bit _ _ (by omega)]
    show Nat.testBit 0 (j - 64) = _
    simp only [Nat.zero_testBit]
    have : j ≠ 0 := by omega
    simp [this]

theorem bitFE2F_zero (j : Nat) : bitFE2F (⟨0, 0⟩ : FE2) j = false := by
  unfold bitFE2F
  split
  · show ((0 : UInt64) >>> j.toUInt64 &&& 1 != 0) = false
    simp
  · show ((0 : UInt64) >>> (j - 64).toUInt64 &&& 1 != 0) = false
    simp

/-- `M_z b` on a bit word `b` (`cw[k] = β_k·z`): the xor of the words `cw[k]` over the bits `k` of `b`, on unboxed
words. -/
def wordsXor (cw : Array FE2) (b : FE2) : Nat → Nat → FK → FK → FE2
  | 0, _, a, c => ⟨a, c⟩
  | n + 1, k, a, c =>
    if bitFE2F b k then let w := cw.getD k 0; wordsXor cw b n (k + 1) (a + w.re) (c + w.im)
    else wordsXor cw b n (k + 1) a c

/-- A bit as a field element. -/
def fbit (p : Bool) : FE := if p then 1 else 0

theorem fbit_xor (p q : Bool) : fbit (p != q) = fbit p + fbit q := by
  cases p <;> cases q <;> simp [fbit, fe_one_add_one]

theorem wordsXor_bit (cw : Array FE2) (b : FE2) {j : Nat} (hj : j < 128) : ∀ (n k : Nat) (a c : FK),
    fbit (bitFE2F (wordsXor cw b n k a c) j) =
      fbit (bitFE2F ⟨a, c⟩ j) + ∑ i ∈ Finset.range n, fbit (bitFE2F b (k + i) && bitFE2F (cw.getD (k + i) 0) j)
  | 0, k, a, c => by simp [wordsXor]
  | n + 1, k, a, c => by
    rw [wordsXor, Finset.sum_range_succ', add_zero,
      Finset.sum_congr rfl (g := fun x => fbit (bitFE2F b (k + 1 + x) && bitFE2F (cw.getD (k + 1 + x) 0) j))
        (fun x _ => by rw [show k + (x + 1) = k + 1 + x by omega])]
    by_cases h : bitFE2F b k = true
    · simp only [h, ↓reduceIte, Bool.true_and]
      rw [wordsXor_bit cw b hj n (k + 1),
        show (⟨a + (cw.getD k 0).re, c + (cw.getD k 0).im⟩ : FE2) = ⟨a, c⟩ + cw.getD k 0 from rfl,
        bitFE2F_add _ _ hj, fbit_xor]
      abel
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.false_and, wordsXor_bit cw b hj n (k + 1)]
      simp [fbit]

/-- `Σ_{(w, b)} [bit j of b]·w`: the vector the terms stand for. -/
def termV (T : List (FE × FE2)) (j : Nat) : FE := (T.map fun q => if bitFE2F q.2 j then q.1 else 0).sum

/-- One forward step on the terms: `(1 + r)·w` keeps `b`, `w` moves to `M_z b`. -/
def termStep (T : List (FE × FE2)) (p : Array FE2 × FE) : List (FE × FE2) :=
  let r1 := 1 + p.2
  T.map (fun q => (r1 * q.1, q.2)) ++ T.map fun q => (q.1, wordsXor p.1 q.2 128 0 0 0)

theorem listSum_mul_left {α : Type} (l : List α) (c : FE) (f : α → FE) :
    (l.map fun q => c * f q).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, mul_add]

theorem listSum_finset_comm {α : Type} (l : List α) (s : Finset Nat) (f : α → Nat → FE) :
    (l.map fun q => ∑ k ∈ s, f q k).sum = ∑ k ∈ s, (l.map fun q => f q k).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]; simp

theorem termV_step (T : List (FE × FE2)) (cw : Array FE2) (r : FE) {j : Nat} (hj : j < 128) :
    termV (termStep T (cw, r)) j = (1 + r) * termV T j +
      ∑ k ∈ Finset.range 128, if bitFE2F (cw.getD k 0) j then termV T k else 0 := by
  unfold termV termStep
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  congr 1
  · rw [← listSum_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    simp only [Function.comp_apply]
    split <;> simp
  · have e : ∀ q : FE × FE2, (if bitFE2F (wordsXor cw q.2 128 0 0 0) j then q.1 else 0) =
        ∑ k ∈ Finset.range 128, if bitFE2F (cw.getD k 0) j then (if bitFE2F q.2 k then q.1 else 0) else 0 := by
      intro q
      have h := wordsXor_bit cw q.2 hj 128 0 0 0
      rw [show (⟨0, 0⟩ : FE2) = ⟨0, 0⟩ from rfl, bitFE2F_zero] at h
      have h1 : (if bitFE2F (wordsXor cw q.2 128 0 0 0) j then q.1 else 0) =
          q.1 * fbit (bitFE2F (wordsXor cw q.2 128 0 0 0) j) := by unfold fbit; split <;> simp
      rw [h1, h]
      simp only [fbit, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      cases bitFE2F q.2 k <;> cases bitFE2F (cw.getD k 0) j <;> simp
    rw [show (T.map ((fun q : FE × FE2 => if bitFE2F q.2 j then q.1 else 0) ∘ fun q => (q.1, wordsXor cw q.2 128 0 0 0))) =
        T.map (fun q => ∑ k ∈ Finset.range 128,
          if bitFE2F (cw.getD k 0) j then (if bitFE2F q.2 k then q.1 else 0) else 0) from
      List.map_congr_left fun q _ => e q, listSum_finset_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hb : bitFE2F (cw.getD k 0) j = true
    · simp only [hb, ↓reduceIte]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      simp

theorem tColsW_getD (z : FE2) {k : Nat} (hk : k < 128) : (tColsW z).getD k 0 = basisFE2 k * z := by
  rw [tColsW, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hk]
  rfl

theorem foldl_fwd_termV : ∀ (z : List FE2) (a : List FE) (u : Array FE) (T : List (FE × FE2)),
    (∀ j < 128, u.getD j 0 = termV T j) → ∀ j < 128,
      ((List.zip (z.map tColsW) a).foldl (fun u p => fwdStepN p.1 p.2 u) u).getD j 0 =
        termV ((List.zip (z.map tColsW) a).foldl termStep T) j
  | [], a, u, T, hu => by simpa using hu
  | _ :: _, [], u, T, hu => by simpa using hu
  | zl :: z, r :: a, u, T, hu => by
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    refine foldl_fwd_termV z a _ _ fun j hj => ?_
    rw [fwdStepN_getD zl r u hj, termV_step T (tColsW zl) r hj, hu j hj]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [tColsW_getD zl (Finset.mem_range.mp hk), hu k (Finset.mem_range.mp hk)]

/-- The terms of the forward steps `ps` from `e₀`. -/
def preTerms (ps : List (Array FE2 × FE)) : List (FE × FE2) := ps.foldl termStep [(1, ⟨1, 0⟩)]

theorem e0A_getD {j : Nat} (hj : j < 128) : e0A.getD j 0 = termV [(1, ⟨1, 0⟩)] j := by
  rw [e0A, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some, termV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, bitFE2F_e0 hj]
  by_cases h : j = 0 <;> simp [h]

theorem rowPre_termV (z : List FE2) (a : List FE) {j : Nat} (hj : j < 128) :
    (rowPre (z.map tColsW) a).getD j 0 = termV (preTerms (List.zip (z.map tColsW) a)) j :=
  foldl_fwd_termV z a e0A _ (fun _ hj => e0A_getD hj) j hj

theorem dot128_termV (T : List (FE × FE2)) (V u : Array FE) (hu : ∀ j < 128, u.getD j 0 = termV T j) :
    dot128 u V = (T.map fun q => q.1 * ∑ i ∈ Finset.range 128, if bitFE2F q.2 i then V.getD i 0 else 0).sum := by
  rw [dot128_eq, Finset.sum_congr rfl fun j hj => by rw [hu j (Finset.mem_range.mp hj)]]
  unfold termV
  have e : ∀ j, (T.map fun q => if bitFE2F q.2 j then q.1 else 0).sum * V.getD j 0 =
      (T.map fun q => (if bitFE2F q.2 j then q.1 else 0) * V.getD j 0).sum := fun j => by
    rw [mul_comm, ← listSum_mul_left]
    exact congrArg List.sum (List.map_congr_left fun q _ => mul_comm _ _)
  simp only [e]
  rw [← listSum_finset_comm]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> simp

/-- `σ_V(w) = Σ_{i : bit i of w} V_i` by `V`'s nibble tables (`tStepN`'s sum). -/
theorem sumNibW_tabs (V : Array FE) (w : FE2) :
    sumNibW ((List.range 32).toArray.map (nibTabQ V)) w 32 0 0 0 0 =
      ∑ i ∈ Finset.range 128, if bitFE2F w i then V.getD i 0 else 0 := by
  rw [show nibTabQ V = nibTab V from funext (nibTabQ_eq V), sumNibW_eq, show (⟨0, 0, 0⟩ : FE) = 0 from rfl, zero_add,
    show (128 : Nat) = 4 * 32 from rfl, sum_range_4]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.mp hn
  rw [zero_add, getD_map32 _ _ hn', nibTab_getD _ _ (nibW_lt _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [nibW_bit _ hn' (Finset.mem_range.mp hi)]

/-- `Σ_{(w, b)} w·σ_V(b)`: the terms against `V`, `σ_V` by `V`'s nibble tables. -/
def dotTerms (T : List (FE × FE2)) (V : Array FE) : FE :=
  let NT := (List.range 32).toArray.map (nibTabQ V)
  T.foldl (fun acc q => acc + q.1 * sumNibW NT q.2 32 0 0 0 0) 0

theorem foldl_addE {α : Type} (f : α → FE) : ∀ (l : List α) (a : FE),
    l.foldl (fun acc q => acc + f q) a = a + (l.map f).sum
  | [], a => by simp
  | q :: l, a => by rw [List.foldl_cons, foldl_addE f l, List.map_cons, List.sum_cons, add_assoc]

theorem dotTerms_rowPre (z : List FE2) (a : List FE) (V : Array FE) :
    dotTerms (preTerms (List.zip (z.map tColsW) a)) V = dot128 (rowPre (z.map tColsW) a) V := by
  rw [dot128_termV _ V _ fun j hj => rowPre_termV z a hj, dotTerms, foldl_addE, zero_add]
  exact congrArg List.sum (List.map_congr_left fun q _ => by rw [sumNibW_tabs])

/-- The forward steps taken by terms (`symK` of them). -/
def symK : Nat := 6

/-- **`tensorDotT` with its first `symK` steps by terms** (`tensorDotT_split`): the other steps transposed onto
`eq(r'', ·)` (`rowSuf`), then `Σ_S w_S·σ(b_S)` over the `2^symK` terms of the first steps. -/
def tensorDotS (cols : List (Array FE2)) (eqA : Array FE) (r : List FE) : FE :=
  if symK ≤ r.length ∧ symK ≤ cols.length then
    dotTerms (preTerms (List.zip (cols.take symK) (r.take symK))) (rowSuf (cols.drop symK) eqA (r.drop symK))
  else tensorDotT cols eqA r

theorem tensorDotS_eq (z : List FE2) (eqA : Array FE) (r : List FE) :
    tensorDotS (z.map tColsW) eqA r = tensorDotT (z.map tColsW) eqA r := by
  unfold tensorDotS
  split
  · rename_i h
    have hk : (r.take symK).length = symK := by rw [List.length_take]; omega
    have hz : (r.take symK).length ≤ z.length := by rw [hk]; simpa using h.2
    conv_rhs => rw [← List.take_append_drop symK r]
    rw [tensorDotT_split z eqA (r.take symK) (r.drop symK) hz, hk, ← List.map_take, dotTerms_rowPre]
  · rfl

/-- `2^i` for `i < 64`. -/
def pow2A : Array Nat := (List.range 64).toArray.map (2 ^ ·)

/-- `rowWordD` on an array, with `bitFE2F` and `pow2A`. -/
def rowWordDF (sa : Array FE2) (j : Nat) : FK :=
  ⟨((List.range 64).foldl (fun acc i => if bitFE2F (sa.getD i 0) j then acc + pow2A.getD i 0 else acc) 0).toUInt64⟩

theorem rowWordDF_eq (sv : List FE2) {j : Nat} (hj : j < 128) : rowWordDF sv.toArray j = rowWordD sv j := by
  unfold rowWordDF rowWordD
  congr 2
  refine List.foldl_ext _ _ _ fun acc i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [list_toArray_getD, bitFE2F_eq _ _ hj, pow2A, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    List.getElem?_toArray, List.getElem?_range hi']
  rfl

/-- `rowSwitchD` with the switched weight by the transposed steps (`tensorDotT`: the words `β_k·z_l` once, outside
the weight's closure) and the row words on arrays. -/
def rowSwitchDF (z sv : List FE2) : DM ((FE × (List FE → FE)) × List FE) := do
  let rr ← samples 7
  let eqR := eqKernel rr
  let eqA := eqR.toArray
  let cols := z.map tColsW
  let sa := sv.toArray
  pure ((sumE ((List.range 128).map fun j => eqA.getD j 0 * FE.ofK (rowWordDF sa j)),
    fun r => tensorDotT cols eqA r), eqR)

theorem rowSwitchDF_eq : rowSwitchDF = rowSwitchD := by
  funext z sv
  unfold rowSwitchDF rowSwitchD
  have hw : ∀ (eqR : List FE), (List.range 128).map (fun j => eqR.toArray.getD j 0 * FE.ofK (rowWordDF sv.toArray j))
      = (List.range 128).map (fun j => eqR.getD j 0 * FE.ofK (rowWordD sv j)) := fun eqR =>
    List.map_congr_left fun j hj => by rw [list_toArray_getD, rowWordDF_eq sv (List.mem_range.mp hj)]
  simp only [tensorDotT_eq, hw]

/-- **The row switch's output as data** (V_S's twin carries it, so that the small shape's regions can share the
point's common coordinates): the target, the words `β_k·z_l` of each coordinate, `eq(r'', ·)`. -/
structure RowR where
  /-- The target. -/
  tgt : FE
  /-- The words `β_k·z_l` (`tColsW`), one array per coordinate. -/
  cols : List (Array FE2)
  /-- `eq(r'', ·)` as an array. -/
  eqA : Array FE
  /-- `eq(r'', ·)`. -/
  eqR : List FE

/-- The row claim's weight (`rowSwitchDF`'s closure). -/
def RowR.w (R : RowR) (r : List FE) : FE := tensorDotT R.cols R.eqA r

/-- `rowSwitchDF`'s output form. -/
def RowR.out (R : RowR) : (FE × (List FE → FE)) × List FE := ((R.tgt, R.w), R.eqR)

/-- A row switch's data with its words from a point `z` (`rowSwitchDR`'s). -/
def RowR.OfZ (R : RowR) : Prop := ∃ z : List FE2, R.cols = z.map tColsW

/-- A row switch's data with its point. -/
abbrev RowZ := {R : RowR // R.OfZ}

/-- **`rowSwitchDF` returning data.** -/
def rowSwitchDR (z sv : List FE2) : DM RowZ := do
  let rr ← samples 7
  let eqR := eqKernel rr
  let eqA := eqR.toArray
  let sa := sv.toArray
  pure ⟨⟨sumE ((List.range 128).map fun j => eqA.getD j 0 * FE.ofK (rowWordDF sa j)), z.map tColsWF, eqA, eqR⟩,
    ⟨z, congrArg (z.map ·) (funext tColsWF_eq)⟩⟩

theorem rowSwitchDF_R : rowSwitchDF = fun z sv => (fun R : RowZ => R.1.out) <$> rowSwitchDR z sv := by
  funext z sv
  unfold rowSwitchDF rowSwitchDR RowR.out RowR.w
  simp only [map_bind, map_pure, show tColsWF = tColsW from funext tColsWF_eq]

/-! ## The `E2` claims' word weights -/

section Six

open Lvm.FE2 (toE2)
open LeanVM.Parameters (E e2ToE6)

/-- A factor of `wordWD` in one product: `z·r + (1 + z)(1 + r) = 1 + z + r` (characteristic two), whose
`X`-coordinate `z.im` is in `K`. -/
@[inline] def wordStepF (acc : FE6) (p : FE2 × FE) : FE6 :=
  let a := 1 + FE.ofK p.1.re + p.2
  let b := p.1.im
  ⟨acc.re * a + FE.smulBase b acc.im, FE.smulBase b acc.re + acc.im * a + FE.smulBase (FK.x * b) acc.im⟩

/-- `wordWD` by `wordStepF`. -/
def wordWDF (z : List FE2) (r : List FE) : FE6 := (List.zip z r).foldl wordStepF ⟨1, 0⟩

theorem toE6_wordStepF (acc : FE6) (zl : FE2) (rl : FE) :
    E2V.FE6.toE6 (wordStepF acc (zl, rl)) =
      E2V.FE6.toE6 acc * (e2ToE6 (toE2 zl) * Lvm.Quad.C (FE.toExt3 rl) +
        (1 + e2ToE6 (toE2 zl)) * (1 + Lvm.Quad.C (FE.toExt3 rl))) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hx : FE.smulBase (FK.x * zl.im) acc.im = FE6.xE * (FE.ofK zl.im * acc.im) := by
    rw [FE.smulBase_eq_mul, ← mul_assoc]
    exact congrArg (· * acc.im) (map_mul Lvm.FE.ofKRingHom FK.x zl.im)
  have hre : M3.kE zl.re = LeanVM.Parameters.ofK (toE2 zl).re := rfl
  have him : M3.kE zl.im = LeanVM.Parameters.ofK (toE2 zl).im := rfl
  refine QuadraticAlgebra.ext ?_ ?_
  · simp only [wordStepF, E2V.FE6.toE6, FE.toExt3_add, FE.toExt3_mul, FE.smulBase_eq_mul, FE.toExt3_one,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, e2ToE6_re, e2ToE6_im, Lvm.Quad.C,
      QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, Lvm.M3.tE_ofK, hre, him]
    linear_combination (-(FE.toExt3 acc.re * LeanVM.Parameters.ofK (toE2 zl).re * FE.toExt3 rl) -
      FE.toExt3 rl * LeanVM.Parameters.ofK (toE2 zl).im * FE.toExt3 acc.im) * h2
  · simp only [wordStepF, hx, E2V.FE6.toE6, FE.toExt3_add, FE.toExt3_mul, FE.smulBase_eq_mul, FE.toExt3_one,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, e2ToE6_re, e2ToE6_im, Lvm.Quad.C,
      QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, Lvm.M3.tE_ofK, hre, him, E2V.toExt3_xE]
    linear_combination (-(LeanVM.Parameters.ofK (toE2 zl).im * FE.toExt3 acc.re * FE.toExt3 rl) -
      LeanVM.Parameters.ofK (toE2 zl).im * FE.toExt3 acc.im * FE.toExt3 rl * LeanVM.Parameters.ofK LeanVM.Parameters.g -
      FE.toExt3 acc.im * LeanVM.Parameters.ofK (toE2 zl).re * FE.toExt3 rl) * h2

theorem toE6_injective : Function.Injective E2V.FE6.toE6 := fun a b h => by
  obtain ⟨ar, ai⟩ := a
  obtain ⟨br, bi⟩ := b
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp only [E2V.FE6.toE6] at h1 h2
  rw [FE.toExt3_injective h1, FE.toExt3_injective h2]

theorem toE6_foldl_wordStepF (z : List FE2) (r : List FE) (acc : FE6) :
    E2V.FE6.toE6 ((List.zip z r).foldl wordStepF acc) =
      (List.zipWith (fun zl rl ↦ e2ToE6 zl * Lvm.Quad.C rl + (1 + e2ToE6 zl) * (1 + Lvm.Quad.C rl))
        (z.map toE2) (r.map FE.toExt3)).foldl (· * ·) (E2V.FE6.toE6 acc) := by
  induction z generalizing r acc with
  | nil => rfl
  | cons zl z ih =>
    cases r with
    | nil => rfl
    | cons rl r =>
      rw [List.zip_cons_cons, List.foldl_cons, ih, List.map_cons, List.map_cons, List.zipWith_cons_cons,
        List.foldl_cons, toE6_wordStepF]

theorem wordWDF_eq : wordWDF = wordWD := by
  funext z r
  refine toE6_injective ?_
  rw [E2V.wordWD_twin, wordWDF, toE6_foldl_wordStepF, E2V.toE6_one]
  rfl

end Six

/-! ## The phases -/

/-- The word weight of `z` on `n` coordinates, reused from the previous part when its point and size are the same. -/
def cachedW (x : List FE) (z : List FE2) (n : Nat) : Option (List FE2 × Nat × FE6) → FE6
  | some (z', n', w') => if n' = n ∧ z' = z then w' else wordWDF z (x.take n)
  | none => wordWDF z (x.take n)

theorem cachedW_eq (x : List FE) (z : List FE2) (n : Nat) (cache : Option (List FE2 × Nat × FE6))
    (hc : ∀ z' n' w', cache = some (z', n', w') → w' = wordWDF z' (x.take n')) :
    cachedW x z n cache = wordWDF z (x.take n) := by
  rcases cache with _ | ⟨z', n', w'⟩
  · rfl
  · show (if n' = n ∧ z' = z then w' else wordWDF z (x.take n)) = _
    split
    · rename_i h
      rw [hc z' n' w' rfl, h.1, h.2]
    · rfl

/-- `sumW6D`'s fold, the word weight of a part reused when its point and block size are the previous part's (the
`KS` link's parts share their points). -/
def sumW6Go (x : List FE) : List (FE2 × Placement × List FE2) → FE6 → Option (List FE2 × Nat × FE6) → FE6
  | [], acc, _ => acc
  | (c, blk, z) :: ps, acc, cache =>
    let wd := cachedW x z blk.variableCount cache
    let w := FE6.mul (FE6.mul (FE6.ofE2 c) (FE6.ofE (blk.eqAbove x))) wd
    sumW6Go x ps ⟨acc.re + w.re, acc.im + w.im⟩ (some (z, blk.variableCount, wd))

/-- `sumW6D` with `wordWDF` and the reuse. -/
def sumW6DF (parts : List (FE2 × Placement × List FE2)) (x : List FE) : FE6 := sumW6Go x parts ⟨0, 0⟩ none

theorem sumW6Go_eq (x : List FE) : ∀ (ps : List (FE2 × Placement × List FE2)) (acc : FE6)
    (cache : Option (List FE2 × Nat × FE6)),
    (∀ z' n' w', cache = some (z', n', w') → w' = wordWDF z' (x.take n')) →
    sumW6Go x ps acc cache = ps.foldl (fun acc (c, blk, z) =>
      let w := FE6.mul (FE6.mul (FE6.ofE2 c) (FE6.ofE (blk.eqAbove x))) (wordWDF z (x.take blk.variableCount))
      ⟨acc.re + w.re, acc.im + w.im⟩) acc
  | [], acc, _, _ => rfl
  | (c, blk, z) :: ps, acc, cache, hc => by
    rw [List.foldl_cons]
    simp only [sumW6Go, cachedW_eq x z blk.variableCount cache hc]
    exact sumW6Go_eq x ps _ _ fun z' n' w' h => by
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2.1, ← h.2.2]

theorem sumW6DF_eq : sumW6DF = sumW6D := by
  funext parts x
  unfold sumW6DF sumW6D
  rw [sumW6Go_eq x parts _ none (fun _ _ _ h => by cases h), wordWDF_eq]

/-- `splitD` with the twins. -/
def splitDF (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) : List BlockClaim :=
  [⟨⟨nu, 0⟩, fun x => (sumW6DF parts x).re, FE.ofK v.re⟩, ⟨⟨nu, 0⟩, fun x => (sumW6DF parts x).im, FE.ofK v.im⟩]


theorem splitDF_eq : splitDF = splitD := by
  funext nu parts v
  unfold splitDF splitD
  rw [sumW6DF_eq]

/-- `splitZ` with the twins. -/
def splitZF (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) : List (Com × BlockClaim × FE) :=
  (splitDF nu parts v).map fun c => (.main, c, 0)

theorem splitZF_eq : splitZF = splitZ := by
  funext nu parts v
  unfold splitZF splitZ
  rw [splitDF_eq]

/-- `frontClaimsD` with the twins. -/
def frontClaimsDF (p : Params) (pub : Pub)
    (tp : List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))))
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) : List (Com × BlockClaim × FE) :=
  let L := layout0 p
  let blkD := dBlock p
  let r := tp.1
  let v := tp.2.1
  let wo := tp.2.2.2
  let rowPt := wo.1.1 ++ wo.2.2.1.1 ++ selPtF (dSel p) (dSelBits p)
  let tape : List (Com × BlockClaim × FE) :=
    ((List.range dLanes).flatMap fun l =>
      ((splitDF p.nuMain [(1, blkD, r ++ selPtF l 2)] (v.getD l 0)).zip (tailDE2 r l)).map fun e =>
        (.main, e.1, e.2)) ++
    [(.main, ⟨⟨p.nuMain, 0⟩, wo.2.2.2.2.1.2, wo.2.2.2.2.1.1⟩, rowTailE2 wo.2.2.2.2.2 rowPt)] ++
    (pub.h.zipIdx.map fun (w, l) =>
      (.main, BlockClaim.point blkD (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w), 0))
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let ks : List (Com × BlockClaim × FE) :=
    (co.2.2.1.1.flatMap fun c => splitZF p.nuMain [(1, ksBlk, c.1)] c.2) ++
      [(.main, ⟨ksBlk, co.2.2.2.1.2, co.2.2.2.1.1⟩, 0)]
  let ksOut : List (Com × BlockClaim × FE) := (List.range 25).flatMap fun l =>
    let bz := ksYPartD p L l co.1
    splitZF p.nuMain [(1, bz.1, bz.2)] (co.2.1.getD l 0)
  let om := eqKernelF (lo.1.drop p.ksLog)
  let rho' := lo.2.1.1
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let xlo := rho'.take xl
  let sel := selXF xl rho'
  let vals := lo.2.2
  let mC := splitZF p.nuMain ((List.range 17).map (fun l => (om.getD l 0, (⟨p.ksLog, L.s + l * R⟩ : Placement), rho')) ++
      (List.range 17).map (fun l => (om.getD l 0 * sel, (⟨xl, L.s + l * R + ksSplit p⟩ : Placement), xlo)))
      (vals.getD 2 0)
  let xC := splitZF p.nuMain ((List.range 17).map fun l => (om.getD l 0, (⟨xl, L.x + l * R⟩ : Placement), xlo))
      (vals.getD 3 0)
  -- the spec's order (`midM`'s `ordM`: the relocated `C_rec` claims, here `M`'s two halves, go before the last
  -- `C_main` claim, here `X`'s im half): `Y_re, Y_im, in_re, in_im, X_re, M_re, M_im, X_im`
  let link : List (Com × BlockClaim × FE) :=
    splitZF p.nuMain ((List.range 25).map fun l => let bz := ksYPartD p L l rho'; (om.getD l 0, bz.1, bz.2))
      (vals.getD 0 0) ++
    splitZF p.nuMain ((List.range 25).map fun l => (om.getD l 0, ksBlk, rho' ++ selPtF l slotLog)) (vals.getD 1 0) ++
    xC.take 1 ++ mC ++ xC.drop 1
  tape ++ ks ++ ksOut ++ link

theorem frontClaimsDF_eq : frontClaimsDF = frontClaimsD := by
  funext p pub tp co lo
  unfold frontClaimsDF frontClaimsD
  rw [splitDF_eq, splitZF_eq]



/-- `padDotF` on an array. -/
def padDotA (a : Array FE2) (y : Nat → Bool) : FE2 :=
  sumF ((List.range 1600).map fun j => a.getD j 0 * bitF (Lvm.KG.pad43Bit y j))

theorem padDotA_eq (ω : List FE2) (y : Nat → Bool) : padDotA ω.toArray y = E2V.padDotF ω y := by
  unfold padDotA E2V.padDotF
  simp only [list_toArray_getD]

/-- `wireTargetD` with the weights in an array. -/
def wireTargetDF (sb : Nat → Bool) (n : Nat) (claim : KClaim FE2) : FE2 :=
  let a := claim.weights.toArray
  claim.value + E2V.iotaF claim.point claim.mu 0 * padDotA a sb +
    padDotA a (fun _ => false) *
      (E2V.thrEvalF claim.point claim.mu (n - 1) + E2V.iotaF claim.point claim.mu 0)

theorem wireTargetDF_eq : wireTargetDF = wireTargetD := by
  funext sb n claim
  unfold wireTargetDF wireTargetD
  simp only [padDotA_eq]

/-- `dWF` on an array. -/
@[inline] def dWA (a : Array FE2) (l z : Nat) : FE2 := a.getD (8 + 64 * l + z) 0

theorem dWA_eq (ω : List FE2) : dWA ω.toArray = dWF ω := by
  funext l z
  exact list_toArray_getD _ _ _

/-- `ksLinkD` with `contShiftFF`. -/
def ksLinkDF (hk xl : Nat) (rows : List Nat) : DM (List FE2 × (List FE2 × FE2) × List FE2) := do
  let kchal ← samplesG gC1 (hk + 5)
  let kshift ← sumcheckD gC2 0 3 (List.replicate hk none)
  let vals ← readE2s 4
  require (kshift.2 == contShiftFF rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 + selXF xl kshift.1 * vals.getD 3 0))
  pure (kchal, kshift, vals)


theorem ksLinkDF_eq : ksLinkDF = ksLinkD := by
  funext hk xl rows
  unfold ksLinkDF ksLinkD
  rw [contShiftFF_eq]

/-- `slotD` with the twins, generic in the row switch `rs` (closures: `rowSwitchDF`; data: `rowSwitchDR`). -/
def slotDFG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (b sb blk : Nat) (W : Nat → Nat → FE2) (pt : List FE2)
    (v : FE2) : DM ((List FE2 × FE2) × List FE2 × ρ) := do
  let sl ← sumcheckD gC2 v 3 (List.replicate b none)
  let sv ← readE2s 64
  require (sl.2 == sumF ((List.range 64).map fun z => E2V.slotWF b W sl.1 z * sv.getD z 0))
  let row ← rs (pt ++ sl.1 ++ selPtF blk sb) sv
  pure (sl, sv, row)

/-- `slotD` with the twins. -/
def slotDF (b sb blk : Nat) (W : Nat → Nat → FE2) (pt : List FE2) (v : FE2) :
    DM ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)) :=
  slotDFG rowSwitchDF b sb blk W pt v

theorem slotDF_eq : slotDF = slotD := by
  funext b sb blk W pt v
  unfold slotDF slotDFG slotD
  rw [rowSwitchDF_eq]

/-- `wireD` with the twins, generic in the row switch. -/
def wireDFG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (w sb dsel : Nat) (s : List FK) (n : Nat)
    (claim : KClaim FE2) : DM ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ρ)) := do
  let sc ← sumcheckD gC2 (wireTargetDF (sBitsD s) n claim) 3 (List.replicate w none)
  let g ← readE2s 1
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0)
  let d ← slotDFG rs 2 sb dsel (dWA claim.weights.toArray) sc.1 (g.getD 0 0)
  pure (sc, g, d)

/-- `wireD` with the twins. -/
def wireDF (w sb dsel : Nat) (s : List FK) (n : Nat) (claim : KClaim FE2) :
    DM ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))) :=
  wireDFG rowSwitchDF w sb dsel s n claim

theorem wireDF_eq : wireDF = wireD := by
  funext w sb dsel s n claim
  have hs : slotDFG rowSwitchDF = slotD := slotDF_eq
  unfold wireDF wireDFG wireD
  rw [hs, wireTargetDF_eq, dWA_eq]

/-- `tapeD` with the twins, generic in the row switch. -/
def tapeDFG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (w sb dsel : Nat) (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × KClaim FE2 × ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ρ))) := do
  sepE2
  let r ← samplesG gC1 w
  let v ← readE2s 25
  let claim ← tapeGkrDF w r v
  require (decide (1 ≤ n ∧ n ≤ 2 ^ w))
  let wo ← wireDFG rs w sb dsel s n claim
  pure (r, v, claim, wo)

/-- `tapeD` with the twins. -/
def tapeDF (w sb dsel : Nat) (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)))) :=
  tapeDFG rowSwitchDF w sb dsel s n

theorem tapeDF_eq : tapeDF = tapeD := by
  funext w sb dsel s n
  have hw : wireDFG rowSwitchDF = wireD := wireDF_eq
  unfold tapeDF tapeDFG tapeD
  rw [hw, tapeGkrDF_eq]

/-- `verifyKeccakD` with the twins. -/
def verifyKeccakDF (logSteps : Nat) (inst output : List FE2) :
    DM (List (List FE2 × FE2) × List FE2 × List FE2) := do
  let packBits := logSteps - 5
  let rLow := inst.take 5
  let segment ← samplesG gC1 keccakSegmentBits
  let lanePoint ← samplesG gC1 keccakLaneBits
  let committed ← if 1 < keccakSegments then readE2 else pure 0
  let first := firstClaimSFF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed
  let claim ← SClaimE2.toClaim <$> keccakLayersDS LeanVM.Protocol.KeccakGkr.Shape.v1 logSteps (List.range keccakDepth)
    (SClaimE2.ofClaim first)
  let outputs ← if 1 < keccakSegments then do
      let o ← keccakOpenD logSteps first 1 (keccakSegments - 1) committed
      let word ← readE2
      require (o.2.1.headD 0 * word == o.2.2)
      pure [(rLow ++ inst.drop 5 ++ o.1, word)]
    else pure []
  let lv ← sumcheckD gC2 claim.value 3 (List.replicate 5 none)
  let o ← keccakOpenD logSteps claim 0 keccakSegments lv.2
  let slices ← readE2s kBits
  require (multilinearEvalF claim.mu lv.1 * dotF o.2.1 slices == o.2.2)
  pure (outputs, lv.1 ++ claim.point.take packBits ++ o.1, slices)

theorem verifyKeccakDF_eq : verifyKeccakDF = verifyKeccakD := by
  funext logSteps inst output
  unfold verifyKeccakDF verifyKeccakD
  simp only [keccakLayersDS_eq, SClaimE2.toClaim_ofClaim, firstClaimSFF_eq]

/-- `callerD` with the twins, generic in the row switch. -/
def callerDFG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (h : Nat) :
    DM (List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ρ) := do
  let r ← samplesG gC1 h
  let v ← readE2s 25
  let res ← verifyKeccakDF h r v
  let row ← rs res.2.1 res.2.2
  pure (r, v, res, row)

/-- `callerD` with the twins. -/
def callerDF (h : Nat) :
    DM (List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE)) :=
  callerDFG rowSwitchDF h

theorem callerDF_eq : callerDF = callerD := by
  funext h
  unfold callerDF callerDFG callerD
  rw [verifyKeccakDF_eq, rowSwitchDF_eq]

/-! ## The row switch's data through the front (`rowSwitchDR`) -/

theorem slotDFG_map {ρ σ : Type} (rs : List FE2 → List FE2 → DM ρ) (f : ρ → σ) (b sb blk : Nat)
    (W : Nat → Nat → FE2) (pt : List FE2) (v : FE2) :
    slotDFG (fun z sv => f <$> rs z sv) b sb blk W pt v =
      (fun t => (t.1, t.2.1, f t.2.2)) <$> slotDFG rs b sb blk W pt v := by
  unfold slotDFG
  simp only [map_bind, map_pure, bind_map_left]

theorem wireDFG_map {ρ σ : Type} (rs : List FE2 → List FE2 → DM ρ) (f : ρ → σ) (w sb dsel : Nat) (s : List FK)
    (n : Nat) (claim : KClaim FE2) :
    wireDFG (fun z sv => f <$> rs z sv) w sb dsel s n claim =
      (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2.1, f t.2.2.2.2))) <$> wireDFG rs w sb dsel s n claim := by
  unfold wireDFG
  simp only [slotDFG_map, map_bind, map_pure, bind_map_left]

theorem tapeDFG_map {ρ σ : Type} (rs : List FE2 → List FE2 → DM ρ) (f : ρ → σ) (w sb dsel : Nat) (s : List FK)
    (n : Nat) :
    tapeDFG (fun z sv => f <$> rs z sv) w sb dsel s n =
      (fun t => (t.1, t.2.1, t.2.2.1, (t.2.2.2.1, t.2.2.2.2.1, (t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
        f t.2.2.2.2.2.2.2)))) <$> tapeDFG rs w sb dsel s n := by
  unfold tapeDFG
  simp only [wireDFG_map, map_bind, map_pure, bind_map_left]

theorem callerDFG_map {ρ σ : Type} (rs : List FE2 → List FE2 → DM ρ) (f : ρ → σ) (h : Nat) :
    callerDFG (fun z sv => f <$> rs z sv) h = (fun t => (t.1, t.2.1, t.2.2.1, f t.2.2.2)) <$> callerDFG rs h := by
  unfold callerDFG
  simp only [map_bind, map_pure, bind_map_left]

/-! ## The opening with grouped weights

The two halves of an `E2` claim (`splitD`) have the same block and the coordinates of one `Quad Ext3` sum as weights;
a group computes that sum once per evaluation point (and per region of the small shape). -/

/-- Stack claims whose weights are computed together. -/
structure SGroup where
  /-- The claims. -/
  flat : List StackClaim
  /-- Their weights at a point, together. -/
  wts : List FE → List FE
  /-- The weights are the claims'. -/
  wts_eq : ∀ x, wts x = flat.map (·.1 x)

/-- A single claim. -/
def SGroup.one (c : StackClaim) : SGroup := ⟨[c], fun x => [c.1 x], fun _ => rfl⟩

theorem flatMap_wts (gs : List SGroup) (x : List FE) :
    gs.flatMap (·.wts x) = (gs.flatMap (·.flat)).map (·.1 x) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [List.flatMap_cons, List.flatMap_cons, List.map_append, g.wts_eq, ih]

/-! ### VQ-V twins of the WHIR level loop (day-0 VQ-V 1–3; `verifyStackedOpeningG` calls `verifyWhirF` after the
freeze, `verifyStackedOpeningG_eq` keeps its statement) -/

/-- **`inducedWeight` with `Ŵ_k(x_q)` in `FK`** (VQ-V 1): `x_q`, the roots `W_k(x^k)` and their inverses are `K`
elements (`eOfNat`, `subspaceRoots`), so the recurrence `W_{k+1} = W_k² + W_k(x^k)·W_k` runs in `FK` and each factor
`1 + p_k(1 + Ŵ_k(x_q))` costs one `E×K` product. -/
def inducedWeightK (messageLog : Nat) (queries : List Nat) (queryWeights point : List FE) : FE :=
  let rk : Array FK := ((subspaceRoots messageLog).map (·.c₀)).toArray
  let ik : Array FK := rk.map fun a => if a == 0 then 0 else a⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) =>
    let product := point.zipIdx.foldl (fun (acc : FE × FK) (challenge, coordinate) =>
      (acc.1 * (1 + FE.smulBase (1 + acc.2 * ik.getD coordinate 0) challenge),
        FK.sq acc.2 + rk.getD coordinate 0 * acc.2)) (weight, (⟨query.toUInt64⟩ : FK))
    total + product.1) 0

theorem ofK_isK_sq_add (a b : FK) :
    FE.sq (FE.ofK a) + FE.ofK b * FE.ofK a = FE.ofK (FK.sq a + b * a) := by
  rw [FE.sq_eq_mul, FK.sq_eq_mul]
  show _ = FE.ofKRingHom (a * a + b * a)
  rw [map_add, map_mul, map_mul]
  rfl

theorem subspaceRootsAux_isK : ∀ (n : ℕ) (last : FE) (layer : List FE), (∃ b, last = FE.ofK b) →
    (∀ v ∈ layer, ∃ a, v = FE.ofK a) → ∀ v ∈ subspaceRootsAux n last layer, ∃ a, v = FE.ofK a
  | 0, _, _, _, _ => by simp [subspaceRootsAux]
  | n + 1, last, layer, ⟨b, hb⟩, hl => by
    have hm : ∀ v ∈ layer.map (fun value => FE.sq value + last * value), ∃ a, v = FE.ofK a := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, rfl⟩ := hl w hw
      exact ⟨FK.sq a + b * a, by rw [hb, ofK_isK_sq_add]⟩
    unfold subspaceRootsAux
    split
    · simp
    · rename_i root rest h
      rw [h] at hm
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hm _ List.mem_cons_self
      · exact subspaceRootsAux_isK n root rest (hm _ List.mem_cons_self)
          (fun w hw => hm w (List.mem_cons_of_mem _ hw)) v hv

theorem subspaceRoots_isK (n : ℕ) : ∀ v ∈ subspaceRoots n, FE.ofK v.c₀ = v := by
  intro v hv
  have : ∃ a, v = FE.ofK a := by
    unfold subspaceRoots at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨1, rfl⟩
    · refine subspaceRootsAux_isK n 1 _ ⟨1, rfl⟩ (fun w hw => ?_) v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
      exact ⟨_, rfl⟩
  obtain ⟨a, rfl⟩ := this
  rfl

theorem fe_ofK_inv (a : FK) : (FE.ofK a)⁻¹ = FE.ofK a⁻¹ := (map_inv₀ FE.ofKRingHom a).symm

theorem fe_ofK_beq_zero (a : FK) : (FE.ofK a == 0) = (a == 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have h' : FE.ofK a ≠ 0 := fun e => h (congrArg FE.c₀ e)
    simp [h, h']

theorem inducedWeightK_eq (messageLog : Nat) (queries : List Nat) (queryWeights point : List FE) :
    inducedWeightK messageLog queries queryWeights point = inducedWeight messageLog queries queryWeights point := by
  unfold inducedWeightK inducedWeight
  dsimp only
  have hR := subspaceRoots_isK messageLog
  set R := subspaceRoots messageLog
  have hr : ∀ i, R.getD i 0 = FE.ofK (((R.map (·.c₀)).toArray).getD i 0) := fun i => by
    rw [list_toArray_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases h : R[i]? with _ | v
    · rfl
    · exact (hR v (List.mem_of_getElem? h)).symm
  have hi : ∀ i, (R.map fun value => if value == 0 then 0 else value⁻¹).getD i 0 =
      FE.ofK ((((R.map (·.c₀)).toArray).map fun a => if a == 0 then 0 else a⁻¹).getD i 0) := fun i => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_map]
    rcases h : R[i]? with _ | v
    · rfl
    · simp only [Option.map_some, Option.getD_some]
      conv_lhs => rw [← hR v (List.mem_of_getElem? h)]
      rw [fe_ofK_beq_zero]
      split
      · rfl
      · exact fe_ofK_inv _
  refine List.foldl_ext _ _ _ fun total wq _ => ?_
  congr 1
  suffices h : ∀ (l : List (FE × ℕ)) (w : FE) (a : FK),
      l.foldl (fun (acc : FE × FE) (challenge, coordinate) =>
        (acc.1 * (1 + challenge * (1 + acc.2 * (R.map fun value => if value == 0 then 0 else value⁻¹).getD
          coordinate 0)), FE.sq acc.2 + R.getD coordinate 0 * acc.2)) (w, FE.ofK a) =
      let r := l.foldl (fun (acc : FE × FK) (challenge, coordinate) =>
        (acc.1 * (1 + FE.smulBase (1 + acc.2 * (((R.map (·.c₀)).toArray).map fun a => if a == 0 then 0 else a⁻¹).getD
          coordinate 0) challenge), FK.sq acc.2 + ((R.map (·.c₀)).toArray).getD coordinate 0 * acc.2)) (w, a)
      (r.1, FE.ofK r.2) by
    rw [show eOfNat wq.2 = FE.ofK ⟨wq.2.toUInt64⟩ from rfl, h]
  intro l
  induction l with
  | nil => intro w a; rfl
  | cons x l ih =>
    intro w a
    obtain ⟨ch, i⟩ := x
    rw [List.foldl_cons, List.foldl_cons]
    dsimp only
    have e : ∀ c : FK, 1 + ch * (1 + FE.ofK a * FE.ofK c) = 1 + FE.smulBase (1 + a * c) ch := fun c => by
      rw [FE.smulBase_eq_mul, mul_comm ch]
      show _ = 1 + FE.ofKRingHom (1 + a * c) * ch
      rw [map_add, map_mul, map_one]
      rfl
    rw [hi, hr, ofK_isK_sq_add, e, ih]

/-- **`whirLevels` with `inducedWeightK`** (VQ-V 2; the text of `whirLevels`, the glued weight swapped). -/
def whirLevelsF (logN laneFolds : Nat) (evaluateBasis : List FE → FE) (direct : Bool) (g : Nat)
    (ood : Bool) : List Level → WhirState → DM Unit
  | [], _ => require false
  | L :: rest, s => do
    let (s, levelFolds) ← foldRounds L.fold s []
    let messageLog := logN - s.folds.length
    let residual ← match rest with
      | [] => readEs (2 ^ messageLog)
      | N :: _ => do skip (nodeBytes * 2 ^ N.cap); pure []
    let oodClaims ← match rest with
      | [] => pure []
      | _ :: _ => oodStep ood messageLog
    grindPreR g
    powCheckR g
    let queries ← positionsR L
    let lam ← sampleE
    let queryWeights := powers lam queries.length
    let rowOffs ← openingR L
    let sig ← read
    let eq := eqKernelA levelFolds
    let folds := rowOffs.map fun o =>
      if L.level = 0 then foldRow0 sig eq o (L.row / 8) else foldRowE sig eq o (2 ^ L.fold)
    let enforced := dot queryWeights folds
    let intro ← sumcheckRoundPoly 3 enforced none
    let s := glue lam s (oodClaims ++ [(intro, fun x => inducedWeightK messageLog queries queryWeights x)])
    match rest with
    | [] => do
      if direct then require (directFinal residual L queries folds)
      let (tailFolds, target) ← tailRounds messageLog s.runningQuad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim =>
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      require (terminal == target)
    | _ :: _ => whirLevelsF logN laneFolds evaluateBasis direct g ood rest s

theorem whirLevelsF_eq (logN laneFolds : Nat) (evaluateBasis : List FE → FE) (direct : Bool) (g : Nat) (ood : Bool)
    (levels : List Level) (s : WhirState) :
    whirLevelsF logN laneFolds evaluateBasis direct g ood levels s =
      whirLevels logN laneFolds evaluateBasis direct g ood levels s := by
  induction levels generalizing s with
  | nil => rfl
  | cons L rest ih =>
    cases rest with
    | nil =>
      rw [whirLevelsF, whirLevels]
      simp only [inducedWeightK_eq]
    | cons N rest' =>
      rw [whirLevelsF, whirLevels]
      simp only [inducedWeightK_eq, ih]

/-- **`verifyWhir` with `whirLevelsF`** (VQ-V 3). -/
def verifyWhirF (levels : List Level) (logN : Nat) (target : FE) (evaluateBasis : List FE → FE)
    (direct : Bool) (g : Nat) (ood : Bool) : DM Unit := do
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsF logN ((levels.head?.map (·.fold)).getD 0) evaluateBasis direct g ood levels ⟨quad, [], []⟩

theorem verifyWhirF_eq (levels : List Level) (logN : Nat) (target : FE) (evaluateBasis : List FE → FE)
    (direct : Bool) (g : Nat) (ood : Bool) :
    verifyWhirF levels logN target evaluateBasis direct g ood = verifyWhir levels logN target evaluateBasis direct g ood := by
  unfold verifyWhirF verifyWhir
  simp only [whirLevelsF_eq]

/-- `verifyStackedOpening` on groups. -/
def verifyStackedOpeningG (levels : List Level) (stackLog : Nat) (gs : List SGroup) (direct : Bool) (g : Nat)
    (ood : Bool) : DM Unit := do
  let claims := gs.flatMap (·.flat)
  let scales := powers (← sampleE) claims.length
  verifyWhirF levels stackLog (dot scales (claims.map (·.2)))
    (fun point => dot scales (gs.flatMap (·.wts point))) direct g ood

theorem verifyStackedOpeningG_eq (levels : List Level) (stackLog : Nat) (gs : List SGroup) (direct : Bool)
    (g : Nat) (ood : Bool) :
    verifyStackedOpeningG levels stackLog gs direct g ood =
      verifyStackedOpening levels stackLog (gs.flatMap (·.flat)) direct g ood := by
  unfold verifyStackedOpeningG verifyStackedOpening
  simp only [flatMap_wts, verifyWhirF_eq]

/-- `dOpenF`'s stack form of a claim. -/
def toStk (s : Bool) (nu : Nat) (e : BlockClaim × FE) : StackClaim :=
  if s then TypedV.onStackZBN nu e.1 e.2 else e.1.onStack

/-- The re half of a split claim (`splitDF`). -/
def splitRe (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) : BlockClaim :=
  ⟨⟨nu, 0⟩, fun x => (sumW6DF parts x).re, FE.ofK v.re⟩

/-- The im half of a split claim (`splitDF`). -/
def splitIm (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) : BlockClaim :=
  ⟨⟨nu, 0⟩, fun x => (sumW6DF parts x).im, FE.ofK v.im⟩

/-- Both halves' stack weights at `x`, the `Quad Ext3` sum once (per region when small). -/
def pairW (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (x : List FE) : FE × FE :=
  if s then
    let L := ((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove y, sumW6DF parts (y.take nu'))
    let h := 1 - x.headD 0
    (h * (L.map fun q => q.1 * q.2.re).sum, h * (L.map fun q => q.1 * q.2.im).sum)
  else
    let e := (⟨nu', 0⟩ : Placement).eqAbove x
    let S := sumW6DF parts (x.take nu')
    (e * S.re, e * S.im)

theorem pairW_fst (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) (t : FE)
    (x : List FE) : (pairW s nu nu' parts x).1 = (toStk s nu (splitRe nu' parts v, t)).1 x := by
  cases s
  · rfl
  · simp only [pairW, toStk, TypedV.onStackZBN, BlockClaim.onStack, splitRe, List.map_map, Function.comp_def,
      ite_true, mul_assoc]

theorem pairW_snd (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) (t : FE)
    (x : List FE) : (pairW s nu nu' parts x).2 = (toStk s nu (splitIm nu' parts v, t)).1 x := by
  cases s
  · rfl
  · simp only [pairW, toStk, TypedV.onStackZBN, BlockClaim.onStack, splitIm, List.map_map, Function.comp_def,
      ite_true, mul_assoc]

/-- Two claims' stack weights at `x` from their block weights `w = (w₀, w₁)` on `⟨nu', 0⟩`, together (`pairW` for any
weight pair: the regions and the relocation once). -/
def pairWG (s : Bool) (nu nu' : Nat) (w : List FE → FE × FE) (x : List FE) : FE × FE :=
  if s then
    let L := ((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove y, w (y.take nu'))
    let h := 1 - x.headD 0
    (h * (L.map fun q => q.1 * q.2.1).sum, h * (L.map fun q => q.1 * q.2.2).sum)
  else
    let e := (⟨nu', 0⟩ : Placement).eqAbove x
    let S := w (x.take nu')
    (e * S.1, e * S.2)

theorem pairWG_fst (s : Bool) (nu nu' : Nat) (w : List FE → FE × FE) (v t : FE) (x : List FE) :
    (pairWG s nu nu' w x).1 = (toStk s nu (⟨⟨nu', 0⟩, fun y => (w y).1, v⟩, t)).1 x := by
  cases s
  · rfl
  · simp only [pairWG, toStk, TypedV.onStackZBN, BlockClaim.onStack, List.map_map, Function.comp_def,
      ite_true, mul_assoc]

theorem pairWG_snd (s : Bool) (nu nu' : Nat) (w : List FE → FE × FE) (v t : FE) (x : List FE) :
    (pairWG s nu nu' w x).2 = (toStk s nu (⟨⟨nu', 0⟩, fun y => (w y).2, v⟩, t)).1 x := by
  cases s
  · rfl
  · simp only [pairWG, toStk, TypedV.onStackZBN, BlockClaim.onStack, List.map_map, Function.comp_def,
      ite_true, mul_assoc]

/-- `pairWG` with a weight per region (`wr nu r`, equal to `w` at the region's relocated points: `pairWR_eq`). -/
def pairWR (s : Bool) (nu nu' : Nat) (w : List FE → FE × FE) (wr : Nat → (Nat × Nat × Nat) → List FE → FE × FE)
    (x : List FE) : FE × FE :=
  if s then
    let L := ((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove y, wr nu r (y.take nu'))
    let h := 1 - x.headD 0
    (h * (L.map fun q => q.1 * q.2.1).sum, h * (L.map fun q => q.1 * q.2.2).sum)
  else pairWG s nu nu' w x

theorem pairWR_eq (s : Bool) (nu nu' : Nat) (w : List FE → FE × FE) (wr : Nat → (Nat × Nat × Nat) → List FE → FE × FE)
    (hw : ∀ (nu0 : Nat) (x : List FE) (r : Nat × Nat × Nat), r ∈ (TypedV.regionsN nu0).filter (Shape.meets ⟨nu', 0⟩) →
      wr nu0 r ((TypedV.relocN nu0 x r).take nu') = w ((TypedV.relocN nu0 x r).take nu')) (x : List FE) :
    pairWR s nu nu' w wr x = pairWG s nu nu' w x := by
  cases s
  · rw [pairWR, if_neg Bool.false_ne_true]
  · have hL : (((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
        ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove (TypedV.relocN nu x r),
          wr nu r ((TypedV.relocN nu x r).take nu'))) =
        (((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
        ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove (TypedV.relocN nu x r),
          w ((TypedV.relocN nu x r).take nu'))) :=
      List.map_congr_left fun r hr => by rw [hw nu x r hr]
    simp only [pairWR, pairWG, ite_true]
    rw [hL]

/-- The regions' common width: the small shape's points share their first `18` coordinates. -/
def rowShare : Nat := 18

/-- The guard of the shared form: every region meeting the block keeps the first `rowShare` coordinates of `x.tail`. -/
def rowShareOk (nu : Nat) (blk : Placement) (R : RowR) : Bool :=
  decide (rowShare ≤ R.cols.length) && decide (rowShare ≤ blk.variableCount) && decide (rowShare ≤ nu - 1) &&
    ((TypedV.regionsN nu).filter (Shape.meets blk)).all fun r => decide (rowShare ≤ r.1) && decide (r.1 ≤ nu - 1)

/-- `Σ_q c_q·v_q` on the 128 coordinates. -/
def comb128 (L : List (FE × Array FE)) : Array FE :=
  (List.range 128).toArray.map fun k => (L.map fun q => q.1 * q.2.getD k 0).sum

theorem dot128_comb (u : Array FE) (L : List (FE × Array FE)) :
    dot128 u (comb128 L) = (L.map fun q => q.1 * dot128 u q.2).sum := by
  simp only [dot128_eq]
  have hc : ∀ k ∈ Finset.range 128, u.getD k 0 * (comb128 L).getD k 0 =
      u.getD k 0 * (L.map fun q => q.1 * q.2.getD k 0).sum := fun k hk => by
    rw [comb128, getD_map128' _ _ (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl hc]
  clear hc
  induction L with
  | nil => simp
  | cons q L ih =>
    have e : ∀ k, u.getD k 0 * ((q :: L).map fun q => q.1 * q.2.getD k 0).sum =
        q.1 * (u.getD k 0 * q.2.getD k 0) + u.getD k 0 * (L.map fun q => q.1 * q.2.getD k 0).sum := fun k => by
      rw [List.map_cons, List.sum_cons]; ring
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, ← Finset.mul_sum, ih, List.map_cons,
      List.sum_cons]

/-- **A row claim's stack weight before VQ2-W** (block `blk`, weight `R.w`): in the small shape each region's own coordinates
are taken by the transposed steps (`rowSuf`), the regions' combination of them is formed (`comb128`), and the
regions' common `rowShare` coordinates are taken once, also transposed (`tensorDotT`; linear in `eq(r'', ·)`). -/
def rowStackWB (s : Bool) (nu : Nat) (blk : Placement) (R : RowR) (x : List FE) : FE :=
  if s && rowShareOk nu blk R then
    let sc := R.cols.drop rowShare
    let V := comb128 (((TypedV.regionsN nu).filter (Shape.meets blk)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * blk.eqAbove y,
        rowSuf sc R.eqA ((y.take blk.variableCount).drop rowShare)))
    (1 - x.headD 0) * tensorDotT (R.cols.take rowShare) V ((x.tail ++ List.replicate (nu - 1) 0).take rowShare)
  else (toStk s nu (⟨blk, R.w, R.tgt⟩, 0)).1 x

theorem rowStackWB_eq (s : Bool) (nu : Nat) (blk : Placement) (R : RowR) (hR : R.OfZ) (v t : FE) (x : List FE) :
    rowStackWB s nu blk R x = (toStk s nu (⟨blk, R.w, v⟩, t)).1 x := by
  unfold rowStackWB
  split
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨rfl, hok⟩ := hg
    unfold rowShareOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filter] at hok
    obtain ⟨⟨⟨hc, hn⟩, hnu⟩, hr⟩ := hok
    obtain ⟨z, hz⟩ := hR
    have hzl : rowShare ≤ z.length := by rw [hz, List.length_map] at hc; exact hc
    have key : ∀ r ∈ (TypedV.regionsN nu).filter (Shape.meets blk),
        dot128 (rowPre (R.cols.take rowShare) ((x.tail ++ List.replicate (nu - 1) 0).take rowShare))
          (rowSuf (R.cols.drop rowShare) R.eqA (((TypedV.relocN nu x r).take blk.variableCount).drop rowShare)) =
        R.w ((TypedV.relocN nu x r).take blk.variableCount) := by
      intro r hrm
      obtain ⟨hr1, hr2⟩ := hr r (List.mem_filter.mp hrm)
      have hL : rowShare ≤ (x.tail ++ List.replicate (nu - 1) 0).length := by
        rw [List.length_append, List.length_replicate]; omega
      have hlen : ((x.tail ++ List.replicate (nu - 1) 0).take rowShare).length = rowShare := by
        rw [List.length_take]; omega
      have hy : (TypedV.relocN nu x r).take rowShare = (x.tail ++ List.replicate (nu - 1) 0).take rowShare := by
        unfold TypedV.relocN
        rw [List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take, Nat.min_eq_left hr1]
      have hsplit : (TypedV.relocN nu x r).take blk.variableCount =
          (x.tail ++ List.replicate (nu - 1) 0).take rowShare ++
            ((TypedV.relocN nu x r).take blk.variableCount).drop rowShare := by
        conv_lhs => rw [← List.take_append_drop rowShare ((TypedV.relocN nu x r).take blk.variableCount)]
        rw [List.take_take, Nat.min_eq_left hn, hy]
      unfold RowR.w
      rw [hz]
      conv_rhs => rw [hsplit, tensorDotT_split z R.eqA _ _ (by rw [hlen]; exact hzl), hlen]
    have hxl : ((x.tail ++ List.replicate (nu - 1) 0).take rowShare).length = rowShare := by
      rw [List.length_take, List.length_append, List.length_replicate]; omega
    have hpre : ∀ V : Array FE, tensorDotT (R.cols.take rowShare) V
        ((x.tail ++ List.replicate (nu - 1) 0).take rowShare) =
        dot128 (rowPre (R.cols.take rowShare) ((x.tail ++ List.replicate (nu - 1) 0).take rowShare)) V := by
      intro V
      have hzt : ((z.take rowShare).map tColsW).length = rowShare := by
        rw [List.length_map, List.length_take]; omega
      have h := tensorDotT_split (z.take rowShare) V ((x.tail ++ List.replicate (nu - 1) 0).take rowShare) []
        (by rw [hxl, List.length_take]; omega)
      rw [List.append_nil, hxl, List.take_of_length_le (Nat.le_of_eq hzt),
        List.drop_of_length_le (Nat.le_of_eq hzt)] at h
      rw [hz, ← List.map_take, h]
      simp only [rowSuf, List.zip_nil_left, List.foldr_nil]
    simp only [toStk, ite_true, TypedV.onStackZBN, BlockClaim.onStack]
    rw [hpre, dot128_comb, List.map_map]
    refine congrArg (fun q => (1 - x.headD 0) * q) (congrArg List.sum (List.map_congr_left fun r hrm => ?_))
    simp only [Function.comp_apply]
    rw [key r hrm, mul_assoc]
  · cases s <;> rfl

/-- **A row claim's stack weight** (`rowStackWB` with the row weights by `tensorDotS`: VQ2-W). -/
def rowStackW (s : Bool) (nu : Nat) (blk : Placement) (R : RowR) (x : List FE) : FE :=
  if s && rowShareOk nu blk R then
    let sc := R.cols.drop rowShare
    let V := comb128 (((TypedV.regionsN nu).filter (Shape.meets blk)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * blk.eqAbove y,
        rowSuf sc R.eqA ((y.take blk.variableCount).drop rowShare)))
    (1 - x.headD 0) * tensorDotS (R.cols.take rowShare) V ((x.tail ++ List.replicate (nu - 1) 0).take rowShare)
  else (toStk s nu (⟨blk, tensorDotS R.cols R.eqA, R.tgt⟩, 0)).1 x

theorem rowStackW_B (s : Bool) (nu : Nat) (blk : Placement) (R : RowR) (hR : R.OfZ) (x : List FE) :
    rowStackW s nu blk R x = rowStackWB s nu blk R x := by
  obtain ⟨z, hz⟩ := hR
  have hw : tensorDotS R.cols R.eqA = R.w := funext fun r => by
    show tensorDotS R.cols R.eqA r = tensorDotT R.cols R.eqA r
    rw [hz, tensorDotS_eq]
  have hp : ∀ (V : Array FE) (a : List FE), tensorDotS (R.cols.take rowShare) V a =
      tensorDotT (R.cols.take rowShare) V a := fun V a => by
    rw [hz, ← List.map_take, tensorDotS_eq]
  unfold rowStackW rowStackWB
  simp only [hw, hp]

theorem rowStackW_eq (s : Bool) (nu : Nat) (blk : Placement) (R : RowR) (hR : R.OfZ) (v t : FE) (x : List FE) :
    rowStackW s nu blk R x = (toStk s nu (⟨blk, R.w, v⟩, t)).1 x := by
  rw [rowStackW_B s nu blk R hR x]
  exact rowStackWB_eq s nu blk R hR v t x

theorem zip_append_gen {α β : Type} : ∀ (z : List α) (a b : List β),
    List.zip z (a ++ b) = List.zip (z.take a.length) a ++ List.zip (z.drop a.length) b
  | [], a, b => by simp
  | _ :: _, [], b => by simp
  | x :: z, y :: a, b => by
    simp only [List.cons_append, List.zip_cons_cons, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
      zip_append_gen z a b]

theorem zip_take_len {α β : Type} : ∀ (z : List α) (a : List β), List.zip (z.take a.length) a = List.zip z a
  | [], a => by simp
  | _ :: _, [] => by simp
  | x :: z, y :: a => by simp only [List.length_cons, List.take_succ_cons, List.zip_cons_cons, zip_take_len z a]

/-- **The word weight continued**: `wordWDF z (a ++ b)` from `wordWDF z a`. -/
theorem wordWDF_append (z : List FE2) (a b : List FE) :
    wordWDF z (a ++ b) = (List.zip (z.drop a.length) b).foldl wordStepF (wordWDF z a) := by
  unfold wordWDF
  rw [zip_append_gen, List.foldl_append, zip_take_len]

/-- The guard of `pairWS`: every region meeting `⟨nu', 0⟩` keeps the first `rowShare` coordinates of `x.tail`. -/
def pairShareOk (nu nu' : Nat) : Bool :=
  decide (rowShare ≤ nu') &&
    ((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).all fun r => decide (rowShare ≤ r.1) && decide (r.1 ≤ nu - 1)

/-- One region's sum of the parts from their word prefixes `pre` (`sumW6DF` with each `wordWDF` continued). -/
def sumW6Pre (keep : Placement → Bool) (parts : List ((FE2 × Placement × List FE2) × FE6)) (yk : List FE) :
    FE6 :=
  parts.foldl (fun acc qp =>
    if keep qp.1.2.1 then
      let q := qp.1
      let m := min rowShare q.2.1.variableCount
      let w := FE6.mul (FE6.mul (FE6.ofE2 q.1) (FE6.ofE (q.2.1.eqAbove yk)))
        ((List.zip (q.2.2.drop m) ((yk.take q.2.1.variableCount).drop m)).foldl wordStepF qp.2)
      ⟨acc.re + w.re, acc.im + w.im⟩
    else acc) ⟨0, 0⟩

/-- `Shape.InStack` decided. -/
def inStackB (b : Placement) : Bool :=
  decide (b.variableCount ≤ CMain.nu20) && decide (b.index % 2 ^ b.variableCount = 0) &&
    decide (b.index < 2 ^ CMain.nu20)

theorem inStack_of_B {b : Placement} (h : inStackB b = true) : Shape.InStack b := by
  unfold inStackB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A part on a block that the region `r` does not meet (stack `ν = 23`) weighs `0` there
(`Shape.eqAbove_relocF_eq_zero`): the parts `pairWS` keeps. -/
def keepPart (nu nu' : Nat) (r : Nat × Nat × Nat) (blk : Placement) : Bool :=
  !(nu == 23 && nu' == 23) || Shape.meets blk r || !inStackB blk

/-- **`pairW` with the regions' common coordinates shared** (before VQ2-W's region filter): each part's word weight over the first `rowShare`
coordinates once, each region continues it. -/
def pairWSB (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (x : List FE) : FE × FE :=
  if s && pairShareOk nu nu' then
    let xt := (x.tail ++ List.replicate (nu - 1) 0).take rowShare
    let pp := parts.map fun q => (q, wordWDF q.2.2 (xt.take (min rowShare q.2.1.variableCount)))
    let L := ((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove y,
        sumW6Pre (keepPart nu nu' r) pp (y.take nu'))
    let h := 1 - x.headD 0
    (h * (L.map fun q => q.1 * q.2.re).sum, h * (L.map fun q => q.1 * q.2.im).sum)
  else pairW s nu nu' parts x

theorem pairWSB_eq (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (x : List FE) :
    pairWSB s nu nu' parts x = pairW s nu nu' parts x := by
  unfold pairWSB
  split
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨rfl, hok⟩ := hg
    unfold pairShareOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filter] at hok
    obtain ⟨hn, hr⟩ := hok
    have key : ∀ r ∈ (TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩),
        sumW6Pre (keepPart nu nu' r) (parts.map fun q => (q, wordWDF q.2.2 (((x.tail ++ List.replicate (nu - 1) 0).take
          rowShare).take (min rowShare q.2.1.variableCount)))) ((TypedV.relocN nu x r).take nu') =
        sumW6DF parts ((TypedV.relocN nu x r).take nu') := by
      intro r hrm
      obtain ⟨hr1, hr2⟩ := hr r (List.mem_filter.mp hrm)
      unfold sumW6DF sumW6Pre
      rw [sumW6Go_eq _ parts _ none (fun _ _ _ h => by cases h), List.foldl_map]
      refine List.foldl_ext _ _ _ fun acc q _ => ?_
      obtain ⟨c, blk, z⟩ := q
      by_cases hk : keepPart nu nu' r blk = false
      · simp only [hk, Bool.false_eq_true, if_false]
        unfold keepPart at hk
        simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false, Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨⟨h1, h2⟩, hm⟩, hst⟩ := hk
        subst h1 h2
        have hr23 : r ∈ Shape.regions := (List.mem_filter.mp hrm).1
        have hlen : (TypedV.relocN 23 x r).length = 23 := Shape.length_relocF x r (by omega)
        have h0 : blk.eqAbove ((TypedV.relocN 23 x r).take 23) = 0 := by
          rw [List.take_of_length_le (by omega)]
          exact Shape.eqAbove_relocF_eq_zero blk (inStack_of_B hst) x hr23 hm
        obtain ⟨are, aim⟩ := acc
        simp only [h0, FE6.mul, FE6.ofE, FE6.mk.injEq]
        constructor <;> ring
      simp only [Bool.not_eq_false] at hk
      simp only [hk, if_true]
      have hlenY : (TypedV.relocN nu x r).length = nu := by
        unfold TypedV.relocN
        rw [List.length_append, List.length_take, List.length_append, List.length_replicate, selectorPoint,
          List.length_map, List.length_range]
        omega
      have hy : (TypedV.relocN nu x r).take rowShare = (x.tail ++ List.replicate (nu - 1) 0).take rowShare := by
        unfold TypedV.relocN
        rw [List.take_append_of_le_length (by rw [List.length_take, List.length_append, List.length_replicate]; omega),
          List.take_take, Nat.min_eq_left hr1]
      have hA : (((TypedV.relocN nu x r).take nu').take blk.variableCount).take (min rowShare blk.variableCount) =
          ((x.tail ++ List.replicate (nu - 1) 0).take rowShare).take (min rowShare blk.variableCount) := by
        rw [List.take_take, List.take_take, ← hy, List.take_take]
        congr 1
        omega
      have hAl : ((((TypedV.relocN nu x r).take nu').take blk.variableCount).take
          (min rowShare blk.variableCount)).length = min rowShare blk.variableCount := by
        rw [List.length_take, List.length_take, List.length_take, hlenY]
        omega
      have hw : wordWDF z (((TypedV.relocN nu x r).take nu').take blk.variableCount) =
          ((List.zip (z.drop (min rowShare blk.variableCount)) ((((TypedV.relocN nu x r).take nu').take
            blk.variableCount).drop (min rowShare blk.variableCount))).foldl wordStepF
            (wordWDF z (((x.tail ++ List.replicate (nu - 1) 0).take rowShare).take
              (min rowShare blk.variableCount)))) := by
        conv_lhs => rw [← List.take_append_drop (min rowShare blk.variableCount)
          (((TypedV.relocN nu x r).take nu').take blk.variableCount), wordWDF_append, hAl, hA]
      simp only [hw]
    simp only [pairW, ite_true]
    have hL : (((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
        ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove (TypedV.relocN nu x r),
          sumW6Pre (keepPart nu nu' r) (parts.map fun q => (q, wordWDF q.2.2
            (((x.tail ++ List.replicate (nu - 1) 0).take
            rowShare).take (min rowShare q.2.1.variableCount)))) ((TypedV.relocN nu x r).take nu'))) =
        (((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).map fun r =>
        ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove (TypedV.relocN nu x r),
          sumW6DF parts ((TypedV.relocN nu x r).take nu'))) :=
      List.map_congr_left fun r hrm => by rw [key r hrm]
    rw [hL]
  · rfl

/-- Some part of `parts` is kept in region `r` (`keepPart`); in the other regions every part weighs `0`. -/
def anyKept (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (r : Nat × Nat × Nat) : Bool :=
  parts.any fun q => keepPart nu nu' r q.2.1

/-- **`pairW` with the regions' common coordinates shared** (`pairWSB` over the regions some part is kept in only:
VQ2-W; a `2^13` block's part meets one region of the small shape's seven). -/
def pairWS (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (x : List FE) : FE × FE :=
  if s && pairShareOk nu nu' then
    let xt := (x.tail ++ List.replicate (nu - 1) 0).take rowShare
    let pp := parts.map fun q => (q, wordWDF q.2.2 (xt.take (min rowShare q.2.1.variableCount)))
    let L := (((TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩)).filter (anyKept nu nu' parts)).map fun r =>
      let y := TypedV.relocN nu x r
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu', 0⟩ : Placement).eqAbove y,
        sumW6Pre (keepPart nu nu' r) pp (y.take nu'))
    let h := 1 - x.headD 0
    (h * (L.map fun q => q.1 * q.2.re).sum, h * (L.map fun q => q.1 * q.2.im).sum)
  else pairW s nu nu' parts x

theorem sumW6Pre_none (keep : Placement → Bool) (yk : List FE) :
    ∀ (pp : List ((FE2 × Placement × List FE2) × FE6)), (∀ qp ∈ pp, keep qp.1.2.1 = false) →
      sumW6Pre keep pp yk = ⟨0, 0⟩ := by
  intro pp h
  unfold sumW6Pre
  suffices g : ∀ (l : List ((FE2 × Placement × List FE2) × FE6)) (acc : FE6), (∀ qp ∈ l, keep qp.1.2.1 = false) →
      l.foldl (fun acc qp => if keep qp.1.2.1 then
        let q := qp.1
        let m := min rowShare q.2.1.variableCount
        let w := FE6.mul (FE6.mul (FE6.ofE2 q.1) (FE6.ofE (q.2.1.eqAbove yk)))
          ((List.zip (q.2.2.drop m) ((yk.take q.2.1.variableCount).drop m)).foldl wordStepF qp.2)
        ⟨acc.re + w.re, acc.im + w.im⟩
      else acc) acc = acc from g pp _ h
  intro l
  induction l with
  | nil => intro acc _; rfl
  | cons qp l ih =>
    intro acc hl
    rw [List.foldl_cons, if_neg (by rw [hl qp List.mem_cons_self]; exact Bool.false_ne_true)]
    exact ih acc fun q hq => hl q (List.mem_cons_of_mem _ hq)

theorem sum_map_filter_zero {α : Type} (p : α → Bool) (f : α → FE) :
    ∀ (l : List α), (∀ a ∈ l, p a = false → f a = 0) → ((l.filter p).map f).sum = (l.map f).sum
  | [], _ => rfl
  | a :: l, h => by
    have ih := sum_map_filter_zero p f l fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    · rw [List.filter_cons_of_neg ha, List.map_cons, List.sum_cons, ih,
        h a List.mem_cons_self (by simpa using ha), zero_add]

theorem pairWS_B (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (x : List FE) :
    pairWS s nu nu' parts x = pairWSB s nu nu' parts x := by
  unfold pairWS pairWSB
  split
  · simp only [List.map_map]
    have z : ∀ r ∈ (TypedV.regionsN nu).filter (Shape.meets ⟨nu', 0⟩), anyKept nu nu' parts r = false →
        sumW6Pre (keepPart nu nu' r) (parts.map fun q => (q, wordWDF q.2.2 (((x.tail ++ List.replicate (nu - 1) 0).take
          rowShare).take (min rowShare q.2.1.variableCount)))) ((TypedV.relocN nu x r).take nu') = ⟨0, 0⟩ := by
      intro r _ hr
      refine sumW6Pre_none _ _ _ fun qp hqp => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hqp
      unfold anyKept at hr
      exact Bool.eq_false_iff.mpr (List.any_eq_false.mp hr q hq)
    congr 2
    · refine sum_map_filter_zero _ _ _ fun r hr hk => ?_
      simp only [Function.comp_apply]
      rw [z r hr hk]
      exact mul_zero _
    · refine sum_map_filter_zero _ _ _ fun r hr hk => ?_
      simp only [Function.comp_apply]
      rw [z r hr hk]
      exact mul_zero _
  · rfl

theorem pairWS_eq (s : Bool) (nu nu' : Nat) (parts : List (FE2 × Placement × List FE2)) (x : List FE) :
    pairWS s nu nu' parts x = pairW s nu nu' parts x := by
  rw [pairWS_B, pairWSB_eq]

/-- **One table's point claims' stack weights together** (the mini-bus's columns of a table: blocks `⟨τ, off⟩`, one
point `pt`): `eqEval pt` once (once per region the table meets when small), each column its own `eqAbove`. -/
def tabW (s : Bool) (nu τ : Nat) (pt : List FE) (cs : List (Com × Nat × FE)) (x : List FE) : List FE :=
  if s then
    let h := 1 - x.headD 0
    let R := (((TypedV.regionsN nu).filter fun r => cs.any fun e => Shape.meets ⟨τ, e.2.1⟩ r).map fun r =>
      let y := TypedV.relocN nu x r
      (r, y, (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * eqEval pt (y.take τ)))
    cs.map fun e => h * ((R.filter fun q => Shape.meets ⟨τ, e.2.1⟩ q.1).map fun q =>
      q.2.2 * (⟨τ, e.2.1⟩ : Placement).eqAbove q.2.1).sum
  else
    let E := eqEval pt (x.take τ)
    cs.map fun e => (⟨τ, e.2.1⟩ : Placement).eqAbove x * E

theorem tabW_eq (s : Bool) (nu τ : Nat) (pt : List FE) (cs : List (Com × Nat × FE)) (x : List FE) :
    tabW s nu τ pt cs x = cs.map fun e => (toStk s nu (BlockClaim.point ⟨τ, e.2.1⟩ pt e.2.2, 0)).1 x := by
  cases s
  · rfl
  · simp only [tabW, toStk, ite_true, TypedV.onStackZBN, BlockClaim.onStack, BlockClaim.point]
    refine List.map_congr_left fun e he => ?_
    refine congrArg (fun q => (1 - x.headD 0) * q) ?_
    rw [List.filter_map, List.map_map, List.filter_filter]
    have hf : ∀ r ∈ TypedV.regionsN nu,
        (((fun q : (Nat × Nat × Nat) × List FE × FE => Shape.meets ⟨τ, e.2.1⟩ q.1) ∘ fun r =>
          (r, TypedV.relocN nu x r, (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail *
            eqEval pt ((TypedV.relocN nu x r).take τ))) r &&
          cs.any fun e => Shape.meets ⟨τ, e.2.1⟩ r) = Shape.meets ⟨τ, e.2.1⟩ r := fun r _ => by
      simp only [Function.comp_apply]
      cases hm : Shape.meets ⟨τ, e.2.1⟩ r
      · rfl
      · simp only [Bool.true_and]
        exact List.any_eq_true.mpr ⟨e, he, hm⟩
    rw [List.filter_congr hf]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    simp only [Function.comp_apply]
    ring

/-- A claim of the opening's list, or the two halves of an `E2` claim, or the `KS` link's `X` and `M` halves in the
spec's order `X_re, M_re, M_im, X_im`. -/
inductive FItem where
  | one (c : Com × BlockClaim × FE)
  | split (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) (tre tim : FE)
  | xm (nu : Nat) (px : List (FE2 × Placement × List FE2)) (vx : FE2) (pm : List (FE2 × Placement × List FE2))
      (vm : FE2)
  /-- Two claims on `⟨nu, 0⟩` whose weights are computed together (`w = (w₀, w₁)`; S2GT's split region claims). -/
  | pairG (nu : Nat) (w : List FE → FE × FE) (v0 v1 t0 t1 : FE)
  /-- `pairG` with a weight per region of the small shape (`wr`, equal to `w` at its relocated points). -/
  | pairR (nu : Nat) (w : List FE → FE × FE) (wr : Nat → (Nat × Nat × Nat) → List FE → FE × FE)
      (hw : ∀ (nu0 : Nat) (x : List FE) (r : Nat × Nat × Nat), r ∈ (TypedV.regionsN nu0).filter (Shape.meets ⟨nu, 0⟩) →
        wr nu0 r ((TypedV.relocN nu0 x r).take nu) = w ((TypedV.relocN nu0 x r).take nu)) (v0 v1 t0 t1 : FE)
  /-- A row switch's claim on `⟨nu, 0⟩` from its data (`rowStackW`: the small shape's regions share the point). -/
  | rowS (blk : Placement) (R : RowR) (hR : R.OfZ) (t : FE)
  /-- One table's point claims `(com, off, v)` on the blocks `⟨τ, off⟩` at the point `pt`, tails `0` (`tabW`: the
  point's `eqEval` once). -/
  | tab (τ : Nat) (pt : List FE) (cs : List (Com × Nat × FE))

/-- The claims an item stands for. -/
def FItem.flat : FItem → List (Com × BlockClaim × FE)
  | .one c => [c]
  | .split nu parts v tre tim => [(.main, splitRe nu parts v, tre), (.main, splitIm nu parts v, tim)]
  | .xm nu px vx pm vm =>
    [(.main, splitRe nu px vx, 0), (.main, splitRe nu pm vm, 0), (.main, splitIm nu pm vm, 0),
      (.main, splitIm nu px vx, 0)]
  | .pairG nu w v0 v1 t0 t1 =>
    [(.main, ⟨⟨nu, 0⟩, fun y => (w y).1, v0⟩, t0), (.main, ⟨⟨nu, 0⟩, fun y => (w y).2, v1⟩, t1)]
  | .pairR nu w _ _ v0 v1 t0 t1 =>
    [(.main, ⟨⟨nu, 0⟩, fun y => (w y).1, v0⟩, t0), (.main, ⟨⟨nu, 0⟩, fun y => (w y).2, v1⟩, t1)]
  | .rowS blk R _ t => [(.main, ⟨blk, R.w, R.tgt⟩, t)]
  | .tab τ pt cs => cs.map fun e => (e.1, BlockClaim.point ⟨τ, e.2.1⟩ pt e.2.2, 0)

/-- An item's groups for the opening at stack size `nu` (`dOpenF`: `C_main`'s claims only). -/
def FItem.groups (s : Bool) (nu : Nat) : FItem → List SGroup
  | .one c => if c.1 == .main then [SGroup.one (toStk s nu c.2)] else []
  | .split nu' parts v tre tim =>
    [⟨[toStk s nu (splitRe nu' parts v, tre), toStk s nu (splitIm nu' parts v, tim)],
      fun x => let q := pairWS s nu nu' parts x; [q.1, q.2],
      fun x => by simp only [List.map_cons, List.map_nil, pairWS_eq, pairW_fst s nu nu' parts v tre x,
        pairW_snd s nu nu' parts v tim x]⟩]
  | .xm nu' px vx pm vm =>
    [⟨[toStk s nu (splitRe nu' px vx, 0), toStk s nu (splitRe nu' pm vm, 0), toStk s nu (splitIm nu' pm vm, 0),
        toStk s nu (splitIm nu' px vx, 0)],
      fun x => let qx := pairWS s nu nu' px x; let qm := pairWS s nu nu' pm x; [qx.1, qm.1, qm.2, qx.2],
      fun x => by simp only [List.map_cons, List.map_nil, pairWS_eq, pairW_fst s nu nu' px vx 0 x,
        pairW_snd s nu nu' px vx 0 x, pairW_fst s nu nu' pm vm 0 x, pairW_snd s nu nu' pm vm 0 x]⟩]
  | .pairG nu' w v0 v1 t0 t1 =>
    [⟨[toStk s nu (⟨⟨nu', 0⟩, fun y => (w y).1, v0⟩, t0), toStk s nu (⟨⟨nu', 0⟩, fun y => (w y).2, v1⟩, t1)],
      fun x => let q := pairWG s nu nu' w x; [q.1, q.2],
      fun x => by simp only [List.map_cons, List.map_nil, pairWG_fst s nu nu' w v0 t0 x,
        pairWG_snd s nu nu' w v1 t1 x]⟩]
  | .pairR nu' w wr hw v0 v1 t0 t1 =>
    [⟨[toStk s nu (⟨⟨nu', 0⟩, fun y => (w y).1, v0⟩, t0), toStk s nu (⟨⟨nu', 0⟩, fun y => (w y).2, v1⟩, t1)],
      fun x => let q := pairWR s nu nu' w wr x; [q.1, q.2],
      fun x => by simp only [List.map_cons, List.map_nil, pairWR_eq s nu nu' w wr hw x, pairWG_fst s nu nu' w v0 t0 x,
        pairWG_snd s nu nu' w v1 t1 x]⟩]
  | .rowS blk R hR t =>
    [⟨[toStk s nu (⟨blk, R.w, R.tgt⟩, t)], fun x => [rowStackW s nu blk R x],
      fun x => by simp only [List.map_cons, List.map_nil, rowStackW_eq s nu blk R hR R.tgt t x]⟩]
  | .tab τ pt cs =>
    [⟨((cs.map fun e => (e.1, BlockClaim.point ⟨τ, e.2.1⟩ pt e.2.2, (0 : FE))).filter (·.1 == .main)).map
        fun e => toStk s nu e.2,
      fun x => tabW s nu τ pt (cs.filter (·.1 == .main)) x,
      fun x => by
        rw [tabW_eq, List.filter_map, List.map_map, List.map_map]
        rfl⟩]

theorem groups_flat (s : Bool) (nu : Nat) (items : List FItem) :
    (items.flatMap (FItem.groups s nu)).flatMap (·.flat) =
      ((items.flatMap FItem.flat).filter (·.1 == .main)).map fun e => toStk s nu e.2 := by
  induction items with
  | nil => rfl
  | cons it items ih =>
    rw [List.flatMap_cons, List.flatMap_append, ih, List.flatMap_cons, List.filter_append, List.map_append]
    congr 1
    cases it with
    | one c =>
      simp only [FItem.groups, FItem.flat]
      split <;> simp_all [SGroup.one]
    | split nu' parts v tre tim => rfl
    | xm nu' px vx pm vm => rfl
    | pairG nu' w v0 v1 t0 t1 => rfl
    | pairR nu' w wr hw v0 v1 t0 t1 => rfl
    | rowS blk R hR t => rfl
    | tab τ pt cs => simp only [FItem.groups, FItem.flat, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **`dOpenF` on items**: the same claims, the halves of each `E2` claim weighed together. -/
def dOpenFFI (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (items : List FItem) : DM Unit := do
  require (((ti ++ items).flatMap FItem.flat).all (·.1 == .main))
  verifyStackedOpeningG p.mainLevels p.nuMain
    (SGroup.one (pin.weight, pin.value) :: (ti ++ items).flatMap (FItem.groups s p.nuMain))
    false p.grind p.mainOod

theorem dOpenFFI_eq (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (items : List FItem) :
    dOpenFFI p s pin ti items = dOpenF p s pin ((ti ++ items).flatMap FItem.flat) := by
  unfold dOpenFFI dOpenF
  rw [verifyStackedOpeningG_eq, List.flatMap_cons, groups_flat]
  cases s <;> simp only [SGroup.one, toStk, List.map_map, Function.comp_def, Bool.false_eq_true, ↓reduceIte,
    List.singleton_append]

/-- **`dOpenF` on items**, the typed claims one by one (S2GF). -/
def dOpenFF (p : Params) (s : Bool) (pin : BlockClaim) (tcl : List (Com × BlockClaim × FE)) (items : List FItem) :
    DM Unit :=
  dOpenFFI p s pin (tcl.map FItem.one) items

theorem dOpenFF_eq (p : Params) (s : Bool) (pin : BlockClaim) (tcl : List (Com × BlockClaim × FE))
    (items : List FItem) : dOpenFF p s pin tcl items = dOpenF p s pin (tcl ++ items.flatMap FItem.flat) := by
  unfold dOpenFF
  rw [dOpenFFI_eq, List.flatMap_append]
  have h1 : (tcl.map FItem.one).flatMap FItem.flat = tcl := by
    induction tcl with
    | nil => rfl
    | cons c tcl ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl
  rw [h1]

/-- How the front reads a row switch's output `ρ`: its `eq(r'', ·)`, its target and weight, and the tape row's
opening item. -/
structure RowAcc (ρ : Type) where
  /-- `eq(r'', ·)`. -/
  eqR : ρ → List FE
  /-- The row's item on the block `blk` with tail `t`. -/
  rowItem : Placement → ρ → FE → FItem

/-- Closures (`rowSwitchDF`): a row a single claim. -/
def rowAccC : RowAcc ((FE × (List FE → FE)) × List FE) :=
  ⟨(·.2), fun blk row t => .one (.main, ⟨blk, row.1.2, row.1.1⟩, t)⟩

/-- Data (`rowSwitchDR`): a row by `rowStackW`. -/
def rowAccR : RowAcc RowZ := ⟨fun R => R.1.eqR, fun blk R t => .rowS blk R.1 R.2 t⟩

/-- **`frontClaimsDF` as items**: each `E2` claim's two halves one item. -/
def frontItemsFG {ρ : Type} (A : RowAcc ρ) (p : Params) (pub : Pub)
    (tp : List FE2 × List FE2 × KClaim FE2 × ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ρ)))
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ρ)
    (lo : List FE2 × (List FE2 × FE2) × List FE2) : List FItem :=
  let L := layout0 p
  let blkD := dBlock p
  let r := tp.1
  let v := tp.2.1
  let wo := tp.2.2.2
  let rowPt := wo.1.1 ++ wo.2.2.1.1 ++ selPtF (dSel p) (dSelBits p)
  let tape : List FItem :=
    ((List.range dLanes).map fun l =>
      FItem.split p.nuMain [(1, blkD, r ++ selPtF l 2)] (v.getD l 0) ((tailDE2 r l).getD 0 0)
        ((tailDE2 r l).getD 1 0)) ++
    [A.rowItem ⟨p.nuMain, 0⟩ wo.2.2.2.2 (rowTailE2 (A.eqR wo.2.2.2.2) rowPt)] ++
    (pub.h.zipIdx.map fun (w, l) =>
      .one (.main, BlockClaim.point blkD (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w), 0))
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let ks : List FItem :=
    (co.2.2.1.1.map fun c => FItem.split p.nuMain [(1, ksBlk, c.1)] c.2 0 0) ++
      [A.rowItem ksBlk co.2.2.2 0]
  let ksOut : List FItem := (List.range 25).map fun l =>
    let bz := ksYPartD p L l co.1
    FItem.split p.nuMain [(1, bz.1, bz.2)] (co.2.1.getD l 0) 0 0
  let om := eqKernelF (lo.1.drop p.ksLog)
  let rho' := lo.2.1.1
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let xlo := rho'.take xl
  let sel := selXF xl rho'
  let vals := lo.2.2
  let link : List FItem :=
    [FItem.split p.nuMain ((List.range 25).map fun l => let bz := ksYPartD p L l rho'; (om.getD l 0, bz.1, bz.2))
      (vals.getD 0 0) 0 0,
    FItem.split p.nuMain ((List.range 25).map fun l => (om.getD l 0, ksBlk, rho' ++ selPtF l slotLog))
      (vals.getD 1 0) 0 0,
    FItem.xm p.nuMain ((List.range 17).map fun l => (om.getD l 0, (⟨xl, L.x + l * R⟩ : Placement), xlo))
      (vals.getD 3 0)
      ((List.range 17).map (fun l => (om.getD l 0, (⟨p.ksLog, L.s + l * R⟩ : Placement), rho')) ++
        (List.range 17).map (fun l => (om.getD l 0 * sel, (⟨xl, L.s + l * R + ksSplit p⟩ : Placement), xlo)))
      (vals.getD 2 0)]
  tape ++ ks ++ ksOut ++ link

/-- **`frontClaimsDF` as items** (closures). -/
def frontItemsF (p : Params) (pub : Pub)
    (tp : List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))))
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) : List FItem :=
  frontItemsFG rowAccC p pub tp co lo

theorem flatMap_single {α β : Type} (f : α → β) (l : List α) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem frontItemsF_flat (p : Params) (pub : Pub)
    (tp : List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))))
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) :
    (frontItemsF p pub tp co lo).flatMap FItem.flat = frontClaimsDF p pub tp co lo := by
  unfold frontItemsF frontItemsFG rowAccC frontClaimsDF
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    FItem.flat, splitZF, splitDF, splitRe, splitIm, tailDE2, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_right, List.getD_cons_zero, List.getD_cons_succ, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append, List.append_assoc, flatMap_single]

/-- The closures' form of the front's data. -/
def mapTp
    (tp : List FE2 × List FE2 × KClaim FE2 × ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × RowZ))) :
    List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))) :=
  (tp.1, tp.2.1, tp.2.2.1, (tp.2.2.2.1, tp.2.2.2.2.1, (tp.2.2.2.2.2.1, tp.2.2.2.2.2.2.1, tp.2.2.2.2.2.2.2.1.out)))

/-- The closures' form of the caller's data. -/
def mapCo (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × RowZ) :
    List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE) :=
  (co.1, co.2.1, co.2.2.1, co.2.2.2.1.out)

/-- **The data's items stand for the closures' claims.** -/
theorem frontItemsR_flat (p : Params) (pub : Pub)
    (tp : List FE2 × List FE2 × KClaim FE2 × ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × RowZ)))
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × RowZ)
    (lo : List FE2 × (List FE2 × FE2) × List FE2) :
    (frontItemsFG rowAccR p pub tp co lo).flatMap FItem.flat = frontClaimsDF p pub (mapTp tp) (mapCo co) lo := by
  rw [← frontItemsF_flat]
  unfold frontItemsF frontItemsFG
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem tapeDF_R (w sb dsel : Nat) (s : List FK) (n : Nat) :
    tapeDF w sb dsel s n = mapTp <$> tapeDFG rowSwitchDR w sb dsel s n := by
  unfold tapeDF
  rw [rowSwitchDF_R, tapeDFG_map]
  rfl

theorem callerDF_R (h : Nat) : callerDF h = mapCo <$> callerDFG rowSwitchDR h := by
  unfold callerDF
  rw [rowSwitchDF_R, callerDFG_map]
  rfl

/-- The typed phases' claims flattened from their items (`decideProgFFG`'s typed phases → `decideProgFG`'s). -/
def flatI (typedI : M3 → Pub → DM (Acc × List FItem × List (List FE × List FE))) :
    M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) :=
  fun m pub => (fun r => (r.1, r.2.1.flatMap FItem.flat, r.2.2)) <$> typedI m pub

/-- The typed phases' claims as single items (S2GF). -/
def liftI (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE))) :
    M3 → Pub → DM (Acc × List FItem × List (List FE × List FE)) :=
  fun m pub => (fun r => (r.1, r.2.1.map FItem.one, r.2.2)) <$> typed m pub

/-- **`decideProgFG` with the twins** (V_S runs it): the typed phases return items (`FItem`). -/
def decideProgFFG (pubR : Vector UInt8 32 → Vector UInt8 32 → ByteArray → Pub) (rows : List ℕ) (p : Params)
    (typedI : M3 → Pub → DM (Acc × List FItem × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubR vk c sig
  let m := m3 p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, ti, evals) ← typedI m pub
  let tp ← tapeDFG rowSwitchDR p.logN (dSelBits p) (dSel p) pub.s pub.n
  let co ← callerDFG rowSwitchDR p.ksLog
  let lo ← ksLinkDF p.ksLog (ksXLog p) rows
  dOpenFFI p (TypedV.smallT p pub) pin (ti ++ (Shape.zeroTails (m.tableClaims pub evals)).map FItem.one)
    (frontItemsFG rowAccR p pub tp co lo)
  pure acc

theorem decideProgFFG_eq (pubR : Vector UInt8 32 → Vector UInt8 32 → ByteArray → Pub) (rows : List ℕ) (p : Params)
    (typedI : M3 → Pub → DM (Acc × List FItem × List (List FE × List FE))) (m3 : Params → M3)
    (vk c : Vector UInt8 32) :
    decideProgFFG pubR rows p typedI m3 vk c = decideProgFG pubR rows p (flatI typedI) m3 vk c := by
  unfold decideProgFFG decideProgFG flatI
  simp only [dOpenFFI_eq, frontItemsR_flat, frontClaimsDF_eq, List.flatMap_append, List.append_assoc,
    bind_map_left]
  rw [← tapeDF_eq, ← callerDF_eq, ← ksLinkDF_eq]
  simp only [tapeDF_R, callerDF_R, bind_map_left]
  have h1 : ∀ l : List (Com × BlockClaim × FE), (l.map FItem.one).flatMap FItem.flat = l := by
    intro l
    induction l with
    | nil => rfl
    | cons c l ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl
  simp only [h1]

/-- **`decideProgFFG` with the mini-bus's claims as items** (`mini pub evals`, e.g. one `FItem.tab` per table). -/
def decideProgFFGM (pubR : Vector UInt8 32 → Vector UInt8 32 → ByteArray → Pub) (rows : List ℕ) (p : Params)
    (typedI : M3 → Pub → DM (Acc × List FItem × List (List FE × List FE)))
    (m3 : Params → M3) (mini : Pub → List (List FE × List FE) → List FItem) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubR vk c sig
  let m := m3 p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, ti, evals) ← typedI m pub
  let tp ← tapeDFG rowSwitchDR p.logN (dSelBits p) (dSel p) pub.s pub.n
  let co ← callerDFG rowSwitchDR p.ksLog
  let lo ← ksLinkDF p.ksLog (ksXLog p) rows
  dOpenFFI p (TypedV.smallT p pub) pin (ti ++ mini pub evals) (frontItemsFG rowAccR p pub tp co lo)
  pure acc

theorem decideProgFFGM_eq (pubR : Vector UInt8 32 → Vector UInt8 32 → ByteArray → Pub) (rows : List ℕ) (p : Params)
    (typedI : M3 → Pub → DM (Acc × List FItem × List (List FE × List FE))) (m3 : Params → M3)
    (mini : Pub → List (List FE × List FE) → List FItem)
    (hmini : ∀ pub evals, (mini pub evals).flatMap FItem.flat = Shape.zeroTails ((m3 p).tableClaims pub evals))
    (vk c : Vector UInt8 32) :
    decideProgFFGM pubR rows p typedI m3 mini vk c = decideProgFG pubR rows p (flatI typedI) m3 vk c := by
  rw [← decideProgFFG_eq]
  unfold decideProgFFGM decideProgFFG
  simp only [dOpenFFI_eq, List.flatMap_append, hmini]
  have h1 : ∀ l : List (Com × BlockClaim × FE), (l.map FItem.one).flatMap FItem.flat = l := by
    intro l
    induction l with
    | nil => rfl
    | cons c l ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl
  simp only [h1]

theorem flatI_liftI (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE))) :
    flatI (liftI typed) = typed := by
  funext m pub
  unfold flatI liftI
  have h1 : ∀ l : List (Com × BlockClaim × FE), (l.map FItem.one).flatMap FItem.flat = l := by
    intro l
    induction l with
    | nil => rfl
    | cons c l ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl
  rw [Functor.map_map]
  simp only [h1]
  exact id_map' (typed m pub)

/-- **`decideProgF` with the twins** (S2GF). -/
def decideProgFF (p : Params)
    (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) : DM Acc :=
  decideProgFFG (pubOfA p.accV) contRowsF p (liftI typed) m3 vk c

theorem decideProgFF_eq : decideProgFF = decideProgF := by
  funext p typed m3 vk c
  unfold decideProgFF decideProgF
  rw [decideProgFFG_eq, flatI_liftI]

end Lvm
