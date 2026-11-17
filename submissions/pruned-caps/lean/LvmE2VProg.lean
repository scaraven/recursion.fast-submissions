-- New for lvm2 S1 (E2-F, E2F-V): the `E2` front's verifier programs (stage S2GF): the tape caller (T1–T4:
-- zero test, 25 scalars, the `24 × 1` Keccak GKR, the chain wiring, `D`'s slot reduction, the row switch),
-- written as the `E3` programs of `LvmVCore`/`LvmKeccakCandidate`/`LvmKeccakCallerTape`/`LvmWireSpec` with
-- `E2` scalars (`e2Read`), ground challenges (`e2Sample`, `g` by the group numerator) and separators.
import LvmE2VSwitch
import LvmWireSpec

/-!
# The `E2` front's programs: the tape caller

Every scalar is an `E2` read (16 B), every challenge a ground `E2` challenge with its own nonce,
`g` by the group's numerator `c` (S2GF's `FRONT_G_MIN`): `gC1 = 1`, `gC2 = 2`, `gC3 = 2`, `gC104 = 7`.
One separator before the first nonce (`tapeProgE2`'s start) and one after each layer's `U`. The
row switch (seven `E3` samples) replaces the Frobenius ring switch.

The algebra (claims, kernels, instance weights, the linear map's transpose, the wiring evaluators)
is `LvmVCore`'s and `LvmWireKernel`'s over a field `F` with `K → F` (`algebraMap`), used at `E2`.

| program | `E3` original | groups (`c`) |
|---|---|---|
| `verifyKeccakLayerE2` | `verifyKeccakLayerS` | `s` 46, pack rounds 3, position rounds 3, `β` 2 |
| `tapeGkrE2` | `tapeGkr` | lanes 1 |
| `slotProgE2` | `slotProg` | slot rounds 2; the row switch |
| `wireChProgE2` | `wireChProg` | wire rounds 2 |
| `tapeProgE2` | `tapeProg` | `r` 1 |
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## Grinding bits by numerator (S2GF `FRONT_G_MIN`) -/

/-- `c = 1`: coordinates (`r`, lanes, instance, `ρ`, `λ`). -/
abbrev gC1 : ℕ := 1
/-- `c = 2`: degree-2 rounds and `β`. -/
abbrev gC2 : ℕ := 2
/-- `c = 3`: pack and position rounds. -/
abbrev gC3 : ℕ := 2
/-- `c = 104`: the RMFE point `s` (`ζ`), `104 · 2^-135 = 2^-128.30` at `g = 7`. -/
abbrev gC104 : ℕ := 7

/-! ## The algebra over `F` -/

section Alg

variable {F : Type} [Field F] [Algebra K F]

/-- A word of `K` in `F`. -/
abbrev kF (a : K) : F := algebraMap K F a

/-- `eOfNat` over `F`. -/
abbrev nF (n : ℕ) : F := kF (K.ofBits n)

/-- A bit in `F`. -/
def bitF (b : Bool) : F := if b then 1 else 0

/-- `Claim` (`keccak.rs:70-75`) over `F`. -/
structure KClaim (F : Type) where
  /-- The claimed value. -/
  value : F
  /-- The weight of each instance of a pack. -/
  mu : List F
  /-- The point: a pack index, then a segment index. -/
  point : List F
  /-- The weight of each bit position. -/
  weights : List F

/-- `instance_weights(s)` over `F` (`keccakInstanceWeights`): the RMFE embedding's unit vectors at `s`. -/
def instWeightsF (s : F) : List F :=
  let sPowers := powersF s embedBits
  rmfeEmbed.map fun e ↦
    sumF ((List.range embedBits).filterMap fun b ↦ if e.testBit b then some (sPowers.getD b 0) else none)

/-- `linear_transpose(w)` over `F` (`keccakLinearTranspose`). -/
def linearTransposeF (w : List F) : List F :=
  let w := w.toArray
  let g : Array F := (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array F := ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    sumF ((List.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)).toArray
  (List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- The first claim's position weights (`firstWeights`): lane `j / 64`'s weight times `x^(j mod 64)`. -/
def firstWeightsF (lanesPt : List F) : List F :=
  (List.range keccakBits).map fun j ↦ (eqKernelF lanesPt).getD (j / 64) 0 * nF (2 ^ (j % 64))

/-- The layer's projection of the product polynomial on the claim's instance weights. -/
def projectedF (claim : KClaim F) (product : List F) : F :=
  sumF ((List.range productBits).map fun c ↦
    sumF ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)

/-- The layer's `ι` correction at the shape `sh` (`verifyKeccakLayerS`: segment `m`'s round
`depth·(m + 1) − step − 1`, weighted by `eq(point ≫ packBits, m)`). -/
def iotaSF (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (claim : KClaim F) : F :=
  let segments := eqKernelF (claim.point.drop (logSteps - 5))
  sumF ((List.range sh.segments).map fun segment ↦
    let constant := keccakRC.getD (sh.depth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumF ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))

/-- The first claim at the shape `sh` (`firstClaimS`). -/
def firstClaimSF (sh : LeanVM.Protocol.KeccakGkr.Shape) (inst segment lanesPt output : List F)
    (committed : F) : KClaim F :=
  ⟨committed + (eqKernelF segment).getD (sh.segments - 1) 0 * dotF ((eqKernelF lanesPt).take 25) output,
    eqKernelF (inst.take 5), inst.drop 5 ++ segment, firstWeightsF lanesPt⟩

/-- `open`'s weights (`keccakSlotWeights`): a claim's weight on each `(slot, z)`, scaled by the segment. -/
def slotWeightsF (logSteps : ℕ) (claim : KClaim F) (first count : ℕ) : List (List F) :=
  let segments := eqKernelF (claim.point.drop (logSteps - 5))
  let weights := claim.weights.toArray
  let rows : Array (Array F) := (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))
  rows.toList.map Array.toList

/-- The slot rows folded by the slot point (`keccakOpen`'s fold). -/
def foldRowsF (slot : List F) (rows : List (List F)) : List F :=
  (slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows).headD []

/-! ### The wiring kernels over `F` (`LvmWireKernel`, `LvmWireSpec`) -/

/-- `ι(i) = eq(ρ, i ≫ 5)·μ[i & 31]`. -/
def iotaF (ρ μ : List F) (i : ℕ) : F := eqAtF ρ (i / 32) * μ.getD (i % 32) 0

/-- The equality weight of one bit. -/
def eqBitF (a : F) (b : Bool) : F := if b then a else 1 + a

/-- The `MS` automaton's value vector over `F`. -/
structure MS4F (F : Type) where
  v00 : F
  v01 : F
  v10 : F
  v11 : F

/-- Entry `(c, s)`. -/
def MS4F.get (q : MS4F F) : Bool → Bool → F
  | false, false => q.v00
  | false, true => q.v01
  | true, false => q.v10
  | true, true => q.v11

/-- One bit of `MS` (`msStep`). -/
def msStepF (a r : F) (tb : Bool) (q : MS4F F) : MS4F F :=
  let f : Bool → Bool → F := fun c s =>
    (1 + a) * eqBitF r c * q.get false (Lvm.WK.nextS c s tb) +
      a * eqBitF r (!c) * q.get c (Lvm.WK.nextS (!c) s tb)
  ⟨f false false, f false true, f true false, f true true⟩

/-- The automaton over the high bits (`msTail`). -/
def msTailF : List F → List F → ℕ → MS4F F
  | a :: σ, r :: ρ, t => msStepF a r (t % 2 == 1) (msTailF σ ρ (t / 2))
  | _, _, t => ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩

/-- `MS_w^base(σ; t)` (`msEval`). -/
def msEvalF (ρ μ σ : List F) (base t : ℕ) : F :=
  let q := msTailF (σ.drop 5) (ρ.take (σ.length - 5)) (t / 32)
  eqAtF (ρ.drop (σ.length - 5)) (base / 2 ^ σ.length) *
    sumF ((List.range 32).map fun d =>
      eqAtF (σ.take 5) d * μ.getD ((d + 1) % 32) 0 * q.get (d == 31) (decide (t % 32 < (d + 1) % 32)))

/-- The threshold automaton (`thrTail`). -/
def thrTailF : List F → ℕ → F × F
  | r :: ρ, t =>
    let q := thrTailF ρ (t / 2)
    let tb := t % 2 == 1
    let g : Bool → F := fun s =>
      (1 + r) * (if Lvm.WK.nextS false s tb then q.2 else q.1) +
        r * (if Lvm.WK.nextS true s tb then q.2 else q.1)
    (g false, g true)
  | [], t => (1, if 1 ≤ t then 1 else 0)

/-- `Σ_{i ≤ t} ι(i)` (`thrEval`). -/
def thrEvalF (ρ μ : List F) (t : ℕ) : F :=
  let q := thrTailF ρ (t / 32)
  sumF ((List.range 32).map fun d => μ.getD d 0 * (if t % 32 < d then q.2 else q.1))

/-- `⟨ω, Pad43(y)⟩` (`padDot`). -/
def padDotF (ω : List F) (y : ℕ → Bool) : F :=
  sumF ((List.range 1600).map fun j ↦ ω.getD j 0 * bitF (Lvm.KG.pad43Bit y j))

/-- The wiring sumcheck's target (`wireTarget`). -/
def wireTargetF (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim F) : F :=
  claim.value + iotaF claim.point claim.mu 0 * padDotF claim.weights (Lvm.KG.digestBits s) +
    padDotF claim.weights (fun _ ↦ false) *
      (thrEvalF claim.point claim.mu (n - 1) + iotaF claim.point claim.mu 0)

/-- A slot's weight at `τ` (`slotWE`). -/
def slotWF (b : ℕ) (W : ℕ → ℕ → F) (τ : List F) (z : ℕ) : F :=
  sumF ((List.range (2 ^ b)).map fun o ↦ eqAtF τ o * W o z)

/-- `D`'s slot weights `W(l, z) = ω_{8 + 64l + z}` (`dW`). -/
def dWF (ω : List F) (l z : ℕ) : F := ω.getD (8 + 64 * l + z) 0

end Alg

/-! ## The programs at `E2` -/

/-- **One layer of the GKR at the shape `sh`** (`verifyKeccakLayerS`) at `E2`. -/
def verifyKeccakLayerE2 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ) (claim : KClaim E2) :
    VerifierProgram (KClaim E2) :=
  e2Reads productBits >>= fun product ↦
  VerifierProgram.require (projectedF claim product + iotaSF sh logSteps step claim * sumF claim.mu =
    claim.value) >>= fun _ ↦
  e2Sep >>= fun _ ↦
  e2Sample gC104 >>= fun s ↦
  let mu := instWeightsF s
  let kappa := sumF mu
  packRoundsE2 gC3 claim.point (polyEvalF product s) 1 >>= fun vsp ↦
  sumcheckE2 gC3 vsp.1 4 (List.replicate keccakLocalBits none) >>= fun lv ↦
  e2Reads 3 >>= fun t ↦
  let eq := eqKernelF lv.1
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  VerifierProgram.require
    (vsp.2.1 * dotF (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) = lv.2) >>=
    fun _ ↦
  e2Sample gC2 >>= fun beta ↦
  let weights := (List.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  pure ⟨t0 + beta * (t1 + beta * t2), mu, vsp.2.2, linearTransposeF weights⟩

/-- The layers (`keccakLayersS`). -/
def keccakLayersE2 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : ℕ) :
    List ℕ → KClaim E2 → VerifierProgram (KClaim E2)
  | [], claim => pure claim
  | step :: steps, claim =>
    verifyKeccakLayerE2 sh logSteps step claim >>= fun claim ↦ keccakLayersE2 sh logSteps steps claim

/-- **The tape's reduction** (`tapeGkr`, `24 × 1`, no openings) at `E2`: five lane coordinates, the
first claim, 24 layers; the claim on the inputs. -/
def tapeGkrE2 (h : ℕ) (inst output : List E2) : VerifierProgram (KClaim E2) :=
  e2Samples gC1 keccakLaneBits >>= fun lanesPt ↦
  keccakLayersE2 LeanVM.Protocol.KeccakGkr.Shape.tape h (List.range 24)
    (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] lanesPt output 0)

/-- What a slot reduction returns at `E2`: the slot point and last claim, the 64 slices, the row switch. -/
structure SlotOutE2 where
  /-- The slot point `τ` and the last claim. -/
  sl : List E2 × E2
  /-- The 64 slices at `(pt, τ, sel(blk))`. -/
  sv : List E2
  /-- The row switch's claim. -/
  row : E × (List E → E)

/-- **A slot reduction** (T4, `slotProg`) at `E2`: `b` plain rounds, 64 slices, the check, the row
switch at the point `(pt, τ, sel(blk))`. -/
def slotProgE2 (b sb blk : ℕ) (W : ℕ → ℕ → E2) (pt : List E2) (v : E2) : VerifierProgram SlotOutE2 :=
  sumcheckE2 gC2 v 3 (List.replicate b none) >>= fun sl ↦
  e2Reads 64 >>= fun sv ↦
  VerifierProgram.require (sl.2 = sumF ((List.range 64).map fun z ↦ slotWF b W sl.1 z * sv.getD z 0)) >>=
    fun _ ↦
  rowSwitch (pt ++ sl.1 ++ selPtF blk sb) sv >>= fun row ↦
  pure ⟨sl, sv, row⟩

/-- What the chain wiring phase returns at `E2`. -/
structure WireChOutE2 where
  /-- The wiring point `σ` and the final claim. -/
  sc : List E2 × E2
  /-- `[g_D]`. -/
  g : List E2
  /-- `D`'s slot reduction. -/
  d : SlotOutE2

/-- **The chain wiring phase** (`wireChProg`) at `E2`. -/
def wireChProgE2 (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    VerifierProgram WireChOutE2 :=
  sumcheckE2 gC2 (wireTargetF s n claim) 3 (List.replicate w none) >>= fun sc ↦
  e2Reads 1 >>= fun g ↦
  VerifierProgram.require (sc.2 = msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0) >>= fun _ ↦
  slotProgE2 2 sb dsel (dWF claim.weights) sc.1 (g.getD 0 0) >>= fun d ↦
  pure ⟨sc, g, d⟩

/-- What the tape caller returns at `E2`: `r`, the 25 scalars, the input claim, the wiring's output. -/
abbrev TapeOutE2 : Type := List E2 × List E2 × KClaim E2 × WireChOutE2

/-- **The tape caller** (`tapeProg`, V_S's CHtape and CHwire at S2GF) at `E2`: the separator, `w`
ground coordinates `r`, 25 scalars, the GKR, `n`'s range, the chain wiring. -/
def tapeProgE2 (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram TapeOutE2 :=
  e2Sep >>= fun _ ↦
  e2Samples gC1 w >>= fun r ↦
  e2Reads 25 >>= fun v ↦
  tapeGkrE2 w r v >>= fun claim ↦
  VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ w) >>= fun _ ↦
  wireChProgE2 w sb dsel s n claim >>= fun wo ↦
  pure (r, v, claim, wo)

end Lvm.E2V
