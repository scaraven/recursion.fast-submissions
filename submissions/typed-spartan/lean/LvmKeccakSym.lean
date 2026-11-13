-- New for lvm2 (roll 10, R10 V-slice): V_S's Keccak layer check with the bit-position weights kept symbolic.
-- Native verifier only: the proof bytes, the schedule, the circuit and the spec are unchanged.
import LvmKeccakSymCorr

/-!
# The Keccak layer check with pending weights

`verifyKeccakLayerG` ends each layer by building the 1600 weights
`u_j = eq(p, j mod 64)·ℓ_{j / 64}` (`p` the first six local coordinates, `ℓ` the lane weights) and transposing them
(`keccakLinearTranspose`: θ, ρ, π). The next layer reads those 1600 weights twice:
- in `weighted`, an inner product with `eq(q, ·) ⊗ eqL`;
- in `iota`, through 64 of them (the lane-0 bits that the round constant sets).

**Here the weights stay pending as `(p, ℓ)` (`LWts.outer`).**
- `weighted` becomes `weightedC` (`weightedC_eq`, the transpose's adjoint): 25 lanes times two shifted correlations
  `corr(r) = Σ_z eq(q, z)·eq(p, (z + r) mod 64)`.
- A two-state carry automaton evaluates each correlation (`corrA`, `corrA_eq`) in 17 products, not 64.
- `iota` reads 11 lane sums (`rcOuter`, `rcOuter_eq`).
- The weights are materialised once, after the last layer.

**Equality.** `dTapeS = dTape` and `verifyKeccakS = verifyKeccak` as reader programs: every read, sample and check is
the same, and the checked values are equal. So V_S's decision is unchanged (`LvmTypedV.decideProgTS_eq`).

Every fast path is guarded by its length conditions and otherwise falls back to the reference expression, so the
equalities need no hypotheses.
-/

set_option autoImplicit false

namespace Lvm

open DM

/-! ## Pending weights -/

/-- The bit-position weights of a layer claim: a list (`mat`), or `T(eq(p, ·) ⊗ ℓ)` with the transpose pending
(`outer p ℓ`). -/
inductive LWts where
  | mat (w : List FE)
  | outer (p : List FE) (laneW : Array FE)
  deriving Inhabited

/-- The weights as a list (the reference form). -/
def LWts.toList : LWts → List FE
  | .mat w => w
  | .outer p laneW => keccakLinearTranspose (outerUG (eqKernelA p) laneW)

/-- A layer claim with pending weights. -/
structure SClaim where
  value : FE
  mu : List FE
  point : List FE
  weights : LWts
  deriving Inhabited

/-- The reference claim. -/
def SClaim.toClaim (c : SClaim) : KeccakClaim := ⟨c.value, c.mu, c.point, c.weights.toList⟩

/-- A reference claim, its weights materialised. -/
def SClaim.ofClaim (c : KeccakClaim) : SClaim := ⟨c.value, c.mu, c.point, .mat c.weights⟩

/-! ## The guarded fast forms -/

/-- `weighted` on pending or listed weights. -/
def weightedS (q : List FE) (eqL : Array FE) : LWts → FE
  | .mat w => weightedRef (eqKernelA q) eqL w
  | .outer p laneW =>
    if q.length == 6 && p.length == 6 then weightedC (corrA (corrTab q p)) eqL laneW
    else weightedRef (eqKernelA q) eqL (LWts.outer p laneW).toList

/-- One segment's round-constant sum on pending or listed weights. -/
def rcSum (lw : LWts) (rc : UInt64) : FE :=
  match lw with
  | .mat w => rcRef w rc
  | .outer p laneW => rcOuter (eqKernelA p) laneW rc

/-! ## The statements -/

theorem weightedS_eq (q : List FE) (eqL : Array FE) (lw : LWts) :
    weightedS q eqL lw = weightedRef (eqKernelA q) eqL lw.toList := by
  cases lw with
  | mat w => rfl
  | outer p laneW =>
    show (if (q.length == 6 && p.length == 6) = true then weightedC (corrA (corrTab q p)) eqL laneW
      else weightedRef (eqKernelA q) eqL (LWts.outer p laneW).toList) = _
    by_cases h : (q.length == 6 && p.length == 6) = true
    · simp only [h, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have hc : corrA (corrTab q p) = corrG (eqKernelA p) (eqKernelA q) := funext (corrA_eq q p h.1 h.2)
      rw [hc, weightedC_eq]; rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem rcSum_eq (lw : LWts) (rc : UInt64) : rcSum lw rc = rcRef lw.toList rc := by
  cases lw with
  | mat w => rfl
  | outer p laneW => exact rcOuter_eq _ _ _

/-! ## The layer -/

/-- **`verifyKeccakLayerG` with pending weights**: the same reads, samples and checks. `weighted` and `iota` read
the pending weights; the output's weights stay pending. -/
def verifyKeccakLayerGS (depth segs logSteps step : Nat) (claim : SClaim) : DM SClaim := do
  let packLog := logSteps - 4
  let product ← readEs productBits
  let projected := sumE ((List.range productBits).map fun c =>
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) =>
      if mask.testBit c then some m else none) * product.getD c 0)
  let segments := eqKernel (claim.point.drop packLog)
  let iota := sumE ((List.range segs).map fun segment =>
    let constant := keccakRC.getD (depth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * rcSum claim.weights constant)
  require (projected + iota * sumE claim.mu == claim.value)
  let s ← sampleE
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  let (localPoint, value) ← sumcheck value 4 (List.replicate localBits none)
  let t ← readEs 3
  let eqL := eqKernelA (localPoint.drop 6)
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  let weighted := weightedS (localPoint.take 6) eqL claim.weights
  require (scale * weighted * (kappa * t0 + (kappa + t1) * t2) == value)
  let beta ← sampleE
  let laneW := ((List.range 25).map fun l => eqL.getD l 0 + beta *
    (eqL.getD (keccakAlong (64 * l) 4 / 64) 0 + beta * eqL.getD (keccakAlong (64 * l) 3 / 64) 0)).toArray
  pure ⟨t0 + beta * (t1 + beta * t2), mu, point, .outer (localPoint.take 6) laneW⟩

/-- The layers, `step` over the given list. -/
def keccakLayersGS (depth segs logSteps : Nat) : List Nat → SClaim → DM SClaim
  | [], claim => pure claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayerGS depth segs logSteps step claim
    keccakLayersGS depth segs logSteps steps claim

theorem verifyKeccakLayerGS_eq (depth segs logSteps step : Nat) (c : SClaim) :
    (SClaim.toClaim <$> verifyKeccakLayerGS depth segs logSteps step c) =
      verifyKeccakLayerG depth segs logSteps step c.toClaim := by
  unfold verifyKeccakLayerGS verifyKeccakLayerG
  simp only [rcSum_eq, weightedS_eq, map_bind, map_pure, SClaim.toClaim, LWts.toList, outerUG, weightedRef, rcRef]

theorem keccakLayersGS_eq (depth segs logSteps : Nat) (steps : List Nat) (c : SClaim) :
    (SClaim.toClaim <$> keccakLayersGS depth segs logSteps steps c) =
      keccakLayersG depth segs logSteps steps c.toClaim := by
  induction steps generalizing c with
  | nil => rfl
  | cons st steps ih =>
    simp only [keccakLayersGS, keccakLayersG, map_bind, ih]
    rw [← verifyKeccakLayerGS_eq, bind_map_left]

/-! ## The tape and `KS` -/

/-- **T2 with pending weights**: `tapeGkrF`, the input claim materialised once. -/
def tapeGkrFS (logSteps : Nat) (inst output : List FE) : DM (List FE × KeccakClaim) := do
  let lanePt ← samples laneBits
  let claim ← keccakLayersGS tapeDepth 1 logSteps (List.range tapeDepth)
    (SClaim.ofClaim (tapeFirstClaimF inst lanePt output))
  pure (lanePt, claim.toClaim)

/-- **The tape phase with pending weights** (`dTape`'s reads). -/
def dTapeS (logN : Nat) : DM TapeRes := do
  let r ← samples logN
  let v ← readEs lanes
  let (lanePt, claim) ← tapeGkrFS logN r v
  pure ⟨r, v, lanePt, claim⟩

theorem dTapeS_eq (logN : Nat) : dTapeS logN = dTape logN := by
  unfold dTapeS dTape tapeGkrFS tapeGkrF
  have h (inst lp out : List FE) : keccakLayersG tapeDepth 1 logN (List.range tapeDepth) (tapeFirstClaimF inst lp out) =
      SClaim.toClaim <$> keccakLayersGS tapeDepth 1 logN (List.range tapeDepth)
        (SClaim.ofClaim (tapeFirstClaimF inst lp out)) := by
    rw [keccakLayersGS_eq]; simp [SClaim.toClaim, SClaim.ofClaim, LWts.toList]
  simp only [h, bind_map_left]

/-- **`verify_keccak` with pending weights** (`KS`; `verifyKeccak`'s reads). -/
def verifyKeccakS (logSteps : Nat) (inst output : List FE) : DM KeccakOut := do
  let packLog := logSteps - 4
  let rLow := inst.take 4
  let segment ← samples segmentBits
  let lanePoint ← samples laneBits
  let committed ← readE
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claimS ← keccakLayersGS gkrDepth gkrSegments logSteps (List.range gkrDepth) (SClaim.ofClaim first)
  let claim := claimS.toClaim
  let (slot, weights, value) ← keccakOpen logSteps first 1 (gkrSegments - 1) committed
  let word ← readE
  require (weights.headD 0 * word == value)
  let (low, value) ← sumcheck claim.value 3 (List.replicate 4 none)
  let (slot', weights', value) ← keccakOpen logSteps claim 0 gkrSegments value
  let slices ← readEs kBits
  require (multilinearEval claim.mu low * dot weights' slices == value)
  pure ⟨rLow ++ inst.drop 4 ++ slot, word, low ++ claim.point.take packLog ++ slot', slices⟩

/-- `KS`'s layers are the generic layers at `12 × 2`. -/
theorem keccakLayers_eq_G (logSteps : Nat) (steps : List Nat) (c : KeccakClaim) :
    keccakLayers logSteps steps c = keccakLayersG gkrDepth gkrSegments logSteps steps c := by
  induction steps generalizing c with
  | nil => rfl
  | cons st steps ih => simp only [keccakLayers, keccakLayersG, ih, verifyKeccakLayer_eq_G]

theorem verifyKeccakS_eq (logSteps : Nat) (inst output : List FE) :
    verifyKeccakS logSteps inst output = verifyKeccak logSteps inst output := by
  unfold verifyKeccakS verifyKeccak
  have h (first : KeccakClaim) : keccakLayers logSteps (List.range gkrDepth) first =
      SClaim.toClaim <$> keccakLayersGS gkrDepth gkrSegments logSteps (List.range gkrDepth)
        (SClaim.ofClaim first) := by
    rw [keccakLayersGS_eq, keccakLayers_eq_G]; simp [SClaim.toClaim, SClaim.ofClaim, LWts.toList]
  simp only [h, bind_map_left]

end Lvm
