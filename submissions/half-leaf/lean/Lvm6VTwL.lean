-- New for lvm6 (WP-V1b): the fast twin of K1's Keccak layer (`layer6`, K0's normalized layer without the separator)
-- and of the twelve layers. The claim's weights stay symbolic (`WRep.tro A ℓ` = `T(A ⊗ ℓ)`): the tail's dot product is
-- season 1's correlation form (`weightedCF`), the round constants' sum `rcOuterF`; nothing of size 1600 is built.
import Lvm6VTwA

/-!
# Fast twins: the Keccak layers

* `iotaG` (`iotaSF` with the weights' round-constant sums as a function; `iotaSF_eq`, `map_iotaG`), `map_projectedF`.
* `LClaim` (a claim with `WRep` weights), `LClaim.dec`.
* `fPackRoundsN`, `tw_packRoundsN`; **`fLayer`**, **`tw_layer6`**; **`fLayers`**, **`tw_layers6`**.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

section

variable {F : Type} [Field F]

/-- `iotaSF` with the weights' round-constant sum as a function `rc`. -/
def iotaG (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (point : List F) (rc : UInt64 → F) : F :=
  let segments := eqKernelF (point.drop (logSteps - 4))
  sumF ((List.range sh.segments).map fun segment ↦
    segments.getD segment 0 * rc (keccakRC.getD (sh.depth * (segment + 1) - step - 1) 0))

theorem iotaSF_eq (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (claim : KClaim F) :
    iotaSF sh logSteps step claim = iotaG sh logSteps step claim.point (rcRefF claim.weights) := rfl

end

end Lvm.E2V

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open LeanVM.Protocol.KeccakGkr (Shape)

section Map

variable {F F' : Type} [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →+* F')

theorem map_iotaG (sh : Shape) (logSteps step : ℕ) (point : List F) (rc : UInt64 → F) :
    φ (iotaG sh logSteps step point rc) = iotaG sh logSteps step (point.map φ) (fun x => φ (rc x)) := by
  simp only [iotaG, map_sumF, List.map_map, Function.comp_def, map_mul, map_getD, ← List.map_drop,
    ← map_eqKernelF]

theorem map_projectedF (c : KClaim F) (c' : KClaim F') (h : c'.mu = c.mu.map φ) (product : List F) :
    φ (projectedF c product) = projectedF c' (product.map φ) := by
  simp only [projectedF, h, map_sumF, List.map_map, Function.comp_def, map_mul, map_getD, List.map_filterMap,
    List.zip_map_left, List.filterMap_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  congr 2
  refine List.filterMap_congr fun x _ => ?_
  obtain ⟨m, mask⟩ := x
  by_cases hb : mask.testBit k = true <;> simp [hb, Prod.map]

end Map

theorem map_laneWA (eqL : Array FE2) (beta : FE2) :
    (laneWA eqL beta).map FE2.toE2 = laneWA (eqL.map FE2.toE2) (FE2.toE2 beta) := by
  simp only [laneWA, Array.map_map, Function.comp_def, ← coe_tE, arr_getD_map, map_add, map_mul]

/-! ## Claims with symbolic weights -/

/-- A Keccak claim in the word field with symbolic weights. -/
structure LClaim where
  value : FE2
  mu : List FE2
  point : List FE2
  W : WRep

/-- Its value in `E2`. -/
def LClaim.dec (c : LClaim) : KClaim E2 :=
  ⟨FE2.toE2 c.value, c.mu.map FE2.toE2, c.point.map FE2.toE2, c.W.dec⟩

/-! ## The pack rounds -/

/-- Fast `packRoundsN g`. -/
def fPackRoundsN (g : ℕ) : List FE2 → FE2 → VF (FE2 × List FE2)
  | [], value => VF.pure (value, [])
  | r :: rs, value => VF.bind (fRoundPoly 3 value (some r)) fun msg => VF.bind (fE2Sample g) fun c =>
      VF.bind (fPackRoundsN g rs (polyEvalF msg c)) fun res => VF.pure (res.1, c :: res.2)

/-- The decoding of the pack rounds' value. -/
def pkD (r : FE2 × List FE2) : E2 × List E2 := (FE2.toE2 r.1, r.2.map FE2.toE2)

theorem tw_packRoundsN (g : ℕ) : ∀ (rs : List FE2) (value : FE2),
    TwinF pkD (Lvm6.KPack.packRoundsN g (rs.map FE2.toE2) (FE2.toE2 value)) (fPackRoundsN g rs value)
  | [], _ => tw_pure rfl
  | r :: rs, value =>
    tw_bind (f := fun msg => e2Sample g >>= fun c => Lvm6.KPack.packRoundsN g (rs.map FE2.toE2)
        (polyEvalF msg c) >>= fun res => pure (res.1, c :: res.2))
      (tw_roundPoly 3 value (some r)) fun msg =>
      tw_bind (f := fun c => Lvm6.KPack.packRoundsN g (rs.map FE2.toE2) (polyEvalF (msg.map FE2.toE2) c) >>=
          fun res => pure (res.1, c :: res.2))
        (tw_e2Sample g) fun c => by
        try dsimp only
        rw [← toE2_polyEvalF]
        exact tw_bind (tw_packRoundsN g rs _) fun res => tw_pure rfl

/-! ## One layer -/

/-- The fast layer's tail: `t`, the check, `β`, the next claim (weights `T(eqZ ⊗ laneWA eqL β)`). -/
def fLayerTail (c : LClaim) (s : FE2) (point : List FE2) (lv : List FE2 × FE2) : VF LClaim :=
  VF.bind (fE2Reads 3) fun t =>
  VF.guard (decide (c.W.dot (z6 lv.1) (eqKernelAF (z6 lv.1)) (eqKernelAF (lv.1.drop 6)) *
      (sumF (instWeightsF s) * t.getD 0 0 + (sumF (instWeightsF s) + t.getD 1 0) * t.getD 2 0) = lv.2)) <|
  VF.bind (fE2Sample gC2) fun beta =>
  VF.pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), instWeightsF s, point,
    .tro (z6 lv.1) (eqKernelAF (z6 lv.1)) (laneWA (eqKernelAF (lv.1.drop 6)) beta) (z6_length _) rfl⟩

/-- **The fast layer** (`layer6 logSteps step`). -/
def fLayer (logSteps step : ℕ) (c : LClaim) : VF LClaim :=
  VF.bind (fE2Reads LeanVM.Protocol.Verifier.productBits) fun product =>
  VF.guard (decide (projectedF (⟨0, c.mu, [], []⟩ : KClaim FE2) product +
      iotaG Shape.v1 logSteps step c.point c.W.rc * sumF c.mu = c.value)) <|
  VF.bind (fE2Sample gC46) fun s =>
  VF.bind (fPackRoundsN gC3 c.point (polyEvalF product s)) fun vp =>
  VF.bind (fSumcheck gC3 vp.1 4 (List.replicate LeanVM.Protocol.Verifier.keccakLocalBits none)) fun lv =>
  fLayerTail c s vp.2 lv

theorem tw_layerTail (c : LClaim) (s : FE2) (point : List FE2) (lv : List FE2 × FE2) (hlv : lv.1.length = 11) :
    TwinF LClaim.dec (Lvm6.KPack.layerTailE2N c.dec (FE2.toE2 s) (point.map FE2.toE2) (scD lv))
      (fLayerTail c s point lv) := by
  unfold Lvm6.KPack.layerTailE2N
  refine tw_bind (tw_e2Reads 3) fun t => ?_
  refine tw_guard _ _ ?_ (tw_bind (tw_e2Sample gC2) fun beta => tw_pure ?_)
  · refine Iff.trans (Eq.congr_left ?_) (toE2_eq_iff _ _)
    have hl : ((scD lv).1).length = 11 := by simp [scD, hlv]
    change dotF ((eqKernelF (scD lv).1).take 1600) c.dec.weights * _ = _
    rw [dot_weightedRef _ _ hl, toE2_mul', toE2_dot _ _ (z6_length _), z6_eq (by omega)]
    simp only [← coe_tE, map_add, map_mul, map_sumF, map_getD, map_instWeightsF, map_eqKernelAF, LClaim.dec,
      scD, List.map_take, List.map_drop]
  · have hl : (lv.1.map FE2.toE2).length = 11 := by simp [hlv]
    simp only [LClaim.dec, WRep.dec, scD, toE2_add', toE2_mul', toE2_getD]
    rw [z6_eq (by omega), batchWF_outer _ hl, map_laneWA, ← coe_tE, map_instWeightsF, map_eqKernelAF, map_eqKernelAF,
      List.map_take, List.map_drop]

theorem tw_layer6 (logSteps step : ℕ) (c : LClaim) :
    TwinF LClaim.dec (Lvm6.K.layer6 logSteps step c.dec) (fLayer logSteps step c) := by
  unfold Lvm6.K.layer6
  refine tw_bind (tw_e2Reads _) fun product => ?_
  refine tw_guard _ _ ?_ (tw_bind (tw_e2Sample gC46) fun s => ?_)
  · have h : projectedF c.dec (product.map FE2.toE2) + iotaSF Shape.v1 logSteps step c.dec * sumF c.dec.mu =
        FE2.toE2 (projectedF (⟨0, c.mu, [], []⟩ : KClaim FE2) product +
          iotaG Shape.v1 logSteps step c.point c.W.rc * sumF c.mu) := by
      rw [iotaSF_eq, toE2_add', toE2_mul', toE2_sumF, ← coe_tE, map_projectedF tE _ c.dec rfl, map_iotaG]
      congr 3
      funext x
      exact (toE2_rc c.W x).symm
    exact (Eq.congr_left h).trans (toE2_eq_iff _ _)
  · rw [← toE2_polyEvalF]
    refine tw_bind (tw_packRoundsN gC3 c.point _) fun vp => ?_
    refine twP_bind (tw_sumcheckPlainL gC3 4 _ vp.1) fun lv hlv => ?_
    exact tw_layerTail c s vp.2 lv hlv

/-! ## The layers -/

/-- **The fast layers** `steps`, in order. -/
def fLayers (logSteps : ℕ) : List ℕ → LClaim → VF LClaim
  | [], c => VF.pure c
  | step :: steps, c => VF.bind (fLayer logSteps step c) fun c' => fLayers logSteps steps c'

theorem tw_layers6 (logSteps : ℕ) : ∀ (steps : List ℕ) (c : LClaim),
    TwinF LClaim.dec (Lvm6.K.layers6 logSteps steps c.dec) (fLayers logSteps steps c)
  | [], _ => tw_pure rfl
  | step :: steps, c => tw_bind (tw_layer6 logSteps step c) fun c' => tw_layers6 logSteps steps c'

end Lvm6.V
