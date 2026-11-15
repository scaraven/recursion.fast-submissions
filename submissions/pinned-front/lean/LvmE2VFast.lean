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
  unfold eqKernelAF eqKernelF
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
      weightedCF (corrAF (corrTabF (lv.take 6) p)) (eqKernelAF (lv.drop 6)) laneW
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
      have hc : corrAF (corrTabF (lv.take 6) p) = corrGF (eqKernelAF p) (eqKernelAF (lv.take 6)) :=
        funext (corrAF_eq _ _ (by simp [h.1]) h.2)
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
  let segments := eqKernelF (claim.point.drop (logSteps - 4))
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

/-- **`verifyKeccakLayerD` with pending weights**: the same reads, samples and checks; `weighted` and `iota` read
the pending weights, the output's weights stay pending (`nextWE2`). -/
def verifyKeccakLayerDS (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (claim : SClaimE2) :
    DM SClaimE2 := do
  let product ← readE2s productBits
  require (projectedF (kHead claim) product + iotaSFS sh logSteps step claim * sumF claim.mu == claim.value)
  sepE2
  let s ← sampleG gC46
  let mu := instWeightsF s
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
  unfold verifyKeccakLayerDS verifyKeccakLayerD
  simp only [map_bind, map_pure, iotaSFS_eq, weightedSE2_eq, projectedF_kHead, SClaimE2.toClaim, nextWE2_toList]

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

/-- `firstClaimSF` at `E2` with `firstWeightsFF`. -/
def firstClaimSFF (sh : LeanVM.Protocol.KeccakGkr.Shape) (inst segment lanesPt output : List FE2)
    (committed : FE2) : KClaim FE2 :=
  ⟨committed + (eqKernelF segment).getD (sh.segments - 1) 0 * dotF ((eqKernelF lanesPt).take 25) output,
    eqKernelF (inst.take 4), inst.drop 4 ++ segment, firstWeightsFF lanesPt⟩

theorem firstClaimSFF_eq : firstClaimSFF = firstClaimSF (F := FE2) := by
  funext sh inst segment lanesPt output committed
  unfold firstClaimSFF firstClaimSF
  rw [firstWeightsFF_eq]

/-- `tapeGkrD` with the layers on pending weights. -/
def tapeGkrDF (h : Nat) (inst output : List FE2) : DM (KClaim FE2) := do
  let lanesPt ← samplesG gC1 keccakLaneBits
  SClaimE2.toClaim <$> keccakLayersDS LeanVM.Protocol.KeccakGkr.Shape.tape h (List.range 24)
    (SClaimE2.ofClaim (firstClaimSFF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] lanesPt output 0))

theorem tapeGkrDF_eq : tapeGkrDF = tapeGkrD := by
  funext h inst output
  unfold tapeGkrDF tapeGkrD
  simp only [keccakLayersDS_eq, SClaimE2.toClaim_ofClaim, firstClaimSFF_eq]

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

/-- `⟨a, b, c⟩ + Σ_{n ≤ i < n + k} T_i[nibble i of w]` on unboxed words. -/
def sumNibW (T : Array (Array FE)) (w : FE2) : Nat → Nat → FK → FK → FK → FE
  | 0, _, a, b, c => ⟨a, b, c⟩
  | k + 1, n, a, b, c =>
    let x := (T.getD n #[]).getD (nibW w n) 0
    sumNibW T w k (n + 1) (a + x.c₀) (b + x.c₁) (c + x.c₂)

/-- `tStepT` by the nibble tables. -/
def tStepN (cr : Array FE2 × FE) (u : Array FE) : Array FE :=
  let T := (List.range 32).toArray.map (nibTab u)
  (List.range 128).toArray.map fun k => (1 + cr.2) * u.getD k 0 + sumNibW T (cr.1.getD k 0) 32 0 0 0 0

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

theorem tStepN_eq : tStepN = tStepT := by
  funext cr u
  unfold tStepN tStepT
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

/-- `slotD` with the twins. -/
def slotDF (b sb blk : Nat) (W : Nat → Nat → FE2) (pt : List FE2) (v : FE2) :
    DM ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)) := do
  let sl ← sumcheckD gC2 v 3 (List.replicate b none)
  let sv ← readE2s 64
  require (sl.2 == sumF ((List.range 64).map fun z => E2V.slotWF b W sl.1 z * sv.getD z 0))
  let row ← rowSwitchDF (pt ++ sl.1 ++ selPtF blk sb) sv
  pure (sl, sv, row)

theorem slotDF_eq : slotDF = slotD := by
  funext b sb blk W pt v
  unfold slotDF slotD
  rw [rowSwitchDF_eq]

/-- `wireD` with the twins. -/
def wireDF (w sb dsel : Nat) (s : List FK) (n : Nat) (claim : KClaim FE2) :
    DM ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))) := do
  let sc ← sumcheckD gC2 (wireTargetDF (sBitsD s) n claim) 3 (List.replicate w none)
  let g ← readE2s 1
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0)
  let d ← slotDF 2 sb dsel (dWA claim.weights.toArray) sc.1 (g.getD 0 0)
  pure (sc, g, d)

theorem wireDF_eq : wireDF = wireD := by
  funext w sb dsel s n claim
  unfold wireDF wireD
  rw [slotDF_eq, wireTargetDF_eq, dWA_eq]

/-- `tapeD` with the twins. -/
def tapeDF (w sb dsel : Nat) (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)))) := do
  sepE2
  let r ← samplesG gC1 w
  let v ← readE2s 25
  let claim ← tapeGkrDF w r v
  require (decide (1 ≤ n ∧ n ≤ 2 ^ w))
  let wo ← wireDF w sb dsel s n claim
  pure (r, v, claim, wo)

theorem tapeDF_eq : tapeDF = tapeD := by
  funext w sb dsel s n
  unfold tapeDF tapeD
  rw [tapeGkrDF_eq, wireDF_eq]

/-- `verifyKeccakD` with the twins. -/
def verifyKeccakDF (logSteps : Nat) (inst output : List FE2) :
    DM (List (List FE2 × FE2) × List FE2 × List FE2) := do
  let packBits := logSteps - 4
  let rLow := inst.take 4
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
      pure [(rLow ++ inst.drop 4 ++ o.1, word)]
    else pure []
  let lv ← sumcheckD gC2 claim.value 3 (List.replicate 4 none)
  let o ← keccakOpenD logSteps claim 0 keccakSegments lv.2
  let slices ← readE2s kBits
  require (multilinearEvalF claim.mu lv.1 * dotF o.2.1 slices == o.2.2)
  pure (outputs, lv.1 ++ claim.point.take packBits ++ o.1, slices)

theorem verifyKeccakDF_eq : verifyKeccakDF = verifyKeccakD := by
  funext logSteps inst output
  unfold verifyKeccakDF verifyKeccakD
  simp only [keccakLayersDS_eq, SClaimE2.toClaim_ofClaim, firstClaimSFF_eq]

/-- `callerD` with the twins. -/
def callerDF (h : Nat) :
    DM (List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE)) := do
  let r ← samplesG gC1 h
  let v ← readE2s 25
  let res ← verifyKeccakDF h r v
  let row ← rowSwitchDF res.2.1 res.2.2
  pure (r, v, res, row)

theorem callerDF_eq : callerDF = callerD := by
  funext h
  unfold callerDF callerD
  rw [verifyKeccakDF_eq, rowSwitchDF_eq]

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

/-- `verifyStackedOpening` on groups. -/
def verifyStackedOpeningG (levels : List Level) (stackLog : Nat) (gs : List SGroup) (direct : Bool) (g : Nat)
    (ood : Bool) : DM Unit := do
  let claims := gs.flatMap (·.flat)
  let scales := powers (← sampleE) claims.length
  verifyWhir levels stackLog (dot scales (claims.map (·.2)))
    (fun point => dot scales (gs.flatMap (·.wts point))) direct g ood

theorem verifyStackedOpeningG_eq (levels : List Level) (stackLog : Nat) (gs : List SGroup) (direct : Bool)
    (g : Nat) (ood : Bool) :
    verifyStackedOpeningG levels stackLog gs direct g ood =
      verifyStackedOpening levels stackLog (gs.flatMap (·.flat)) direct g ood := by
  unfold verifyStackedOpeningG verifyStackedOpening
  simp only [flatMap_wts]

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

/-- A claim of the opening's list, or the two halves of an `E2` claim, or the `KS` link's `X` and `M` halves in the
spec's order `X_re, M_re, M_im, X_im`. -/
inductive FItem where
  | one (c : Com × BlockClaim × FE)
  | split (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) (tre tim : FE)
  | xm (nu : Nat) (px : List (FE2 × Placement × List FE2)) (vx : FE2) (pm : List (FE2 × Placement × List FE2))
      (vm : FE2)

/-- The claims an item stands for. -/
def FItem.flat : FItem → List (Com × BlockClaim × FE)
  | .one c => [c]
  | .split nu parts v tre tim => [(.main, splitRe nu parts v, tre), (.main, splitIm nu parts v, tim)]
  | .xm nu px vx pm vm =>
    [(.main, splitRe nu px vx, 0), (.main, splitRe nu pm vm, 0), (.main, splitIm nu pm vm, 0),
      (.main, splitIm nu px vx, 0)]

/-- An item's groups for the opening at stack size `nu` (`dOpenF`: `C_main`'s claims only). -/
def FItem.groups (s : Bool) (nu : Nat) : FItem → List SGroup
  | .one c => if c.1 == .main then [SGroup.one (toStk s nu c.2)] else []
  | .split nu' parts v tre tim =>
    [⟨[toStk s nu (splitRe nu' parts v, tre), toStk s nu (splitIm nu' parts v, tim)],
      fun x => let q := pairW s nu nu' parts x; [q.1, q.2],
      fun x => by simp only [List.map_cons, List.map_nil, pairW_fst s nu nu' parts v tre x,
        pairW_snd s nu nu' parts v tim x]⟩]
  | .xm nu' px vx pm vm =>
    [⟨[toStk s nu (splitRe nu' px vx, 0), toStk s nu (splitRe nu' pm vm, 0), toStk s nu (splitIm nu' pm vm, 0),
        toStk s nu (splitIm nu' px vx, 0)],
      fun x => let qx := pairW s nu nu' px x; let qm := pairW s nu nu' pm x; [qx.1, qm.1, qm.2, qx.2],
      fun x => by simp only [List.map_cons, List.map_nil, pairW_fst s nu nu' px vx 0 x,
        pairW_snd s nu nu' px vx 0 x, pairW_fst s nu nu' pm vm 0 x, pairW_snd s nu nu' pm vm 0 x]⟩]

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

/-- **`dOpenF` on items**: the same claims, the halves of each `E2` claim weighed together. -/
def dOpenFF (p : Params) (s : Bool) (pin : BlockClaim) (tcl : List (Com × BlockClaim × FE)) (items : List FItem) :
    DM Unit := do
  require ((tcl ++ items.flatMap FItem.flat).all (·.1 == .main))
  verifyStackedOpeningG p.mainLevels p.nuMain
    (SGroup.one (pin.weight, pin.value) :: (tcl.map FItem.one ++ items).flatMap (FItem.groups s p.nuMain))
    false p.grind p.mainOod

theorem dOpenFF_eq (p : Params) (s : Bool) (pin : BlockClaim) (tcl : List (Com × BlockClaim × FE))
    (items : List FItem) : dOpenFF p s pin tcl items = dOpenF p s pin (tcl ++ items.flatMap FItem.flat) := by
  unfold dOpenFF dOpenF
  rw [verifyStackedOpeningG_eq, List.flatMap_cons, groups_flat, List.flatMap_append]
  have h1 : (tcl.map FItem.one).flatMap FItem.flat = tcl := by
    induction tcl with
    | nil => rfl
    | cons c tcl ih => rw [List.map_cons, List.flatMap_cons, ih]; rfl
  rw [h1]
  cases s <;> simp only [SGroup.one, toStk, List.map_map, Function.comp_def, Bool.false_eq_true, ↓reduceIte,
    List.singleton_append]

/-- **`frontClaimsDF` as items**: each `E2` claim's two halves one item. -/
def frontItemsF (p : Params) (pub : Pub)
    (tp : List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))))
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
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
    [.one (.main, ⟨⟨p.nuMain, 0⟩, wo.2.2.2.2.1.2, wo.2.2.2.2.1.1⟩, rowTailE2 wo.2.2.2.2.2 rowPt)] ++
    (pub.h.zipIdx.map fun (w, l) =>
      .one (.main, BlockClaim.point blkD (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w), 0))
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let ks : List FItem :=
    (co.2.2.1.1.map fun c => FItem.split p.nuMain [(1, ksBlk, c.1)] c.2 0 0) ++
      [.one (.main, ⟨ksBlk, co.2.2.2.1.2, co.2.2.2.1.1⟩, 0)]
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
  unfold frontItemsF frontClaimsDF
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    FItem.flat, splitZF, splitDF, splitRe, splitIm, tailDE2, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_right, List.getD_cons_zero, List.getD_cons_succ, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append, List.append_assoc, flatMap_single]

/-- **`decideProgF` with the twins** (V_S runs it). -/
def decideProgFF (p : Params)
    (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOfA p.accV vk c sig
  let m := m3 p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, tcl, evals) ← typed m pub
  let tp ← tapeDF p.logN (dSelBits p) (dSel p) pub.s pub.n
  let co ← callerDF p.ksLog
  let lo ← ksLinkDF p.ksLog (ksXLog p) contRowsF
  dOpenFF p (TypedV.smallT p pub) pin (tcl ++ Shape.zeroTails (m.tableClaims pub evals))
    (frontItemsF p pub tp co lo)
  pure acc

theorem decideProgFF_eq : decideProgFF = decideProgF := by
  funext p typed m3 vk c
  unfold decideProgFF decideProgF
  simp only [dOpenFF_eq, frontItemsF_flat, List.append_assoc]
  rw [tapeDF_eq, callerDF_eq, ksLinkDF_eq, frontClaimsDF_eq]

end Lvm
