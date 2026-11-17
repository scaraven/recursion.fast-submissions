-- New for lvm2 S1 (E2-F, E2F-V): V_S's `E2` front on the reader `DM` (stage S2GF): the root pin, the tape caller,
-- `KS` and the `KS` link with 16-B scalars, per-challenge nonces and `powOK`, the row switch, and the front's claims
-- with every `E2` claim split in place. The reference for E2F-P's byte layout (STATUS-V answers (1)–(8)).
import LvmDecideTape
import LvmE2VMid
import LvmFieldE2Correct
import LvmTypedV
-- (GOLF2 import pruning: dropped LvmVerifierF: unused by this module.)

/-!
# The decision `F` at S2GF: the `E2` front

Reader primitives (the stream is `Σ`'s trace entries, `LvmDecideBase`):
* `readE2`: 16 bytes, `re` then `im` (`fe2At`); `nonceE2`: skips the 8-byte nonce;
* **`sampleG g`**: the nonce, the answer `c`, `require (powOKR g c)`, the value `(c₀, c₁)`;
* `sepE2`: one sample, its value unused.

The phases are `LvmE2VProg`'s programs on `DM` at `FE2` (the generic algebra of `LvmE2VBase`/`LvmE2VProg`
at `F = FE2`, a field with word operations: `LvmFieldE2Correct`):
`roundPolyD`, `sumcheckD`, `packRoundsD`, `verifyKeccakLayerD`, `tapeGkrD`, `slotD`, `wireD`, `tapeD`,
`keccakOpenD`, `verifyKeccakD`, `callerD`, `ksLinkD`; the row switch `rowSwitchD` (seven `E3` samples).
-/

set_option autoImplicit false

namespace Lvm

open DM Lvm.E2V
open LeanVM.Protocol.Verifier (keccakLocalBits keccakLaneBits qkeccakSlotBits keccakSegmentBits keccakSegments
  keccakDepth keccakAlong keccakBits)

/-- `K` (`BF64`) into `FE2` through `FK`. -/
instance instAlgebraKFE2 : Algebra LeanVM.Parameters.K FE2 :=
  (FE2.ofKRingHom.comp FK.ringEquivBF64.symm.toRingHom).toAlgebra

/-! ## Reader primitives at `E2` -/

/-- An `E2` scalar at byte `o`: `re` then `im`. -/
@[inline] def fe2At (b : ByteArray) (o : Nat) : FE2 := ⟨kAt b o, kAt b (o + 8)⟩

/-- **The next `E2` scalar** (16 B). -/
@[inline] def readE2 : DM FE2 := fun b s => (fe2At b (s.ent + 40 + s.msg), { s with msg := s.msg + 16 })

/-- The next `n` `E2` scalars. -/
def readE2s : Nat → DM (List FE2)
  | 0 => pure []
  | n + 1 => do
    let x ← readE2
    let xs ← readE2s n
    pure (x :: xs)

/-- The nonce (8 B; V reads past it, the FS query absorbs it). -/
@[inline] def nonceE2 : DM Unit := skip 8

/-- The `E2` challenge of an answer: lanes 0–1. -/
@[inline] def e2OfFE (c : FE) : FE2 := ⟨c.c₀, c.c₁⟩

/-- **A ground `E2` challenge**: the nonce, the answer, `powOK g`, lanes 0–1. -/
def sampleG (g : Nat) : DM FE2 := do
  nonceE2
  let c ← sampleE
  require (powOKR g c)
  pure (e2OfFE c)

/-- `n` ground challenges. -/
def samplesG (g : Nat) : Nat → DM (List FE2)
  | 0 => pure []
  | n + 1 => do
    let x ← sampleG g
    let xs ← samplesG g n
    pure (x :: xs)

/-- The separator. -/
def sepE2 : DM Unit := do
  let _ ← sampleE
  pure ()

/-! ## Rounds -/

/-- A round's message (`roundPolyE2`). -/
def roundPolyD (count : Nat) (claim : FE2) : Option FE2 → DM (List FE2)
  | none => do
    let c0 ← readE2
    let tail ← readE2s (count - 2)
    pure (c0 :: (claim + sumF tail) :: tail)
  | some r => do
    let tail ← readE2s (count - 1)
    pure ((claim + r * sumF tail) :: tail)

/-- The sumcheck at `E2` (`sumcheckE2`). -/
def sumcheckD (g : Nat) (claim : FE2) (count : Nat) : List (Option FE2) → DM (List FE2 × FE2)
  | [] => pure ([], claim)
  | mode :: modes => do
    let msg ← roundPolyD count claim mode
    let c ← sampleG g
    let res ← sumcheckD g (polyEvalF msg c) count modes
    pure (c :: res.1, res.2)

/-- The equality-mode rounds (`packRoundsE2`). -/
def packRoundsD (g : Nat) : List FE2 → FE2 → FE2 → DM (FE2 × FE2 × List FE2)
  | [], value, scale => pure (value, scale, [])
  | r :: rs, value, scale => do
    let msg ← roundPolyD 3 value (some r)
    let c ← sampleG g
    let res ← packRoundsD g rs ((1 + r + c) * polyEvalF msg c) (scale * (1 + r + c))
    pure (res.1, res.2.1, c :: res.2.2)

/-! ## The Keccak GKR -/

/-- One layer (`verifyKeccakLayerE2`). -/
def verifyKeccakLayerD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : Nat) (claim : KClaim FE2) :
    DM (KClaim FE2) := do
  let product ← readE2s productBits
  require (projectedF claim product + iotaSF sh logSteps step claim * sumF claim.mu == claim.value)
  sepE2
  let s ← sampleG gC104
  let mu := instWeightsF s
  let kappa := sumF mu
  let vsp ← packRoundsD gC3 claim.point (polyEvalF product s) 1
  let lv ← sumcheckD gC3 vsp.1 4 (List.replicate keccakLocalBits none)
  let t ← readE2s 3
  let eq := eqKernelF lv.1
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  require (vsp.2.1 * dotF (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) == lv.2)
  let beta ← sampleG gC2
  let weights := (List.range keccakBits).map fun j =>
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  pure ⟨t0 + beta * (t1 + beta * t2), mu, vsp.2.2, linearTransposeF weights⟩

/-- The layers. -/
def keccakLayersD (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : Nat) :
    List Nat → KClaim FE2 → DM (KClaim FE2)
  | [], claim => pure claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayerD sh logSteps step claim
    keccakLayersD sh logSteps steps claim

/-- The tape's reduction (`tapeGkrE2`). -/
def tapeGkrD (h : Nat) (inst output : List FE2) : DM (KClaim FE2) := do
  let lanesPt ← samplesG gC1 keccakLaneBits
  keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.tape h (List.range 24)
    (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.tape inst [] lanesPt output 0)

/-! ## The row switch -/

/-- Coordinate `j` of an `FE2` (`bitE2`). -/
def bitFE2 (y : FE2) (j : Nat) : Bool :=
  if j < 64 then y.re.val.toNat.testBit j else y.im.val.toNat.testBit (j - 64)

/-- Row `j` of the slices (`rowWord`): bit `i` is coordinate `j` of `s_i`. -/
def rowWordD (sv : List FE2) (j : Nat) : FK :=
  ⟨((List.range 64).foldl (fun acc i => if bitFE2 (sv.getD i 0) j then acc + 2 ^ i else acc) 0).toUInt64⟩

/-- The basis element `β_j` of `FE2`. -/
def basisFE2 (j : Nat) : FE2 :=
  if j < 64 then ⟨⟨(2 ^ j : Nat).toUInt64⟩, 0⟩ else ⟨0, ⟨(2 ^ (j - 64) : Nat).toUInt64⟩⟩

/-- One factor of the tensor product on the 128 `E3` coordinates (`tensorStep`). -/
def tensorStepD (v : Array FE) (zr : FE2 × FE) : Array FE :=
  let cols : Array (List Nat) := (List.range 128).toArray.map fun k =>
    (List.range 128).filter fun j => bitFE2 (basisFE2 k * zr.1) j
  let mz : Array FE := (List.range 128).foldl (fun acc k =>
    (cols.getD k []).foldl (fun acc j => acc.modify j (· + v.getD k 0)) acc)
    (Array.replicate 128 0)
  (List.range 128).toArray.map fun j => (1 + zr.2) * v.getD j 0 + mz.getD j 0

/-- **`V`'s tensor coordinates** (`tensorW`). -/
def tensorWD (z : List FE2) (r : List FE) : Array FE :=
  (List.zip z r).foldl tensorStepD ((List.range 128).toArray.map fun j => if j = 0 then 1 else 0)

/-- **The row switch** (`rowSwitch`): seven `E3` samples, the target, the weight; and `eq(r'', ·)`. -/
def rowSwitchD (z sv : List FE2) : DM ((FE × (List FE → FE)) × List FE) := do
  let rr ← samples 7
  let eqR := eqKernel rr
  pure ((sumE ((List.range 128).map fun j => eqR.getD j 0 * FE.ofK (rowWordD sv j)),
    fun r => let t := tensorWD z r; sumE ((List.range 128).map fun j => eqR.getD j 0 * t.getD j 0)), eqR)

/-! ## The tape caller -/

/-- A slot reduction (`slotProgE2`). -/
def slotD (b sb blk : Nat) (W : Nat → Nat → FE2) (pt : List FE2) (v : FE2) :
    DM ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)) := do
  let sl ← sumcheckD gC2 v 3 (List.replicate b none)
  let sv ← readE2s 64
  require (sl.2 == sumF ((List.range 64).map fun z => E2V.slotWF b W sl.1 z * sv.getD z 0))
  let row ← rowSwitchD (pt ++ sl.1 ++ selPtF blk sb) sv
  pure (sl, sv, row)

/-- The statement's digest bits from V_S's words (`digestBits` of the header's `s`). -/
def sBitsD (s : List FK) (j : Nat) : Bool := decide (j < 256) && (s.getD (j / 64) 0).val.toNat.testBit (j % 64)

/-- The wiring sumcheck's target (`wireTargetF`) from the digest's bits. -/
def wireTargetD (sb : Nat → Bool) (n : Nat) (claim : KClaim FE2) : FE2 :=
  claim.value + E2V.iotaF claim.point claim.mu 0 * E2V.padDotF claim.weights sb +
    E2V.padDotF claim.weights (fun _ => false) *
      (E2V.thrEvalF claim.point claim.mu (n - 1) + E2V.iotaF claim.point claim.mu 0)

/-- The chain wiring phase (`wireChProgE2`). -/
def wireD (w sb dsel : Nat) (s : List FK) (n : Nat) (claim : KClaim FE2) :
    DM ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE))) := do
  let sc ← sumcheckD gC2 (wireTargetD (sBitsD s) n claim) 3 (List.replicate w none)
  let g ← readE2s 1
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0)
  let d ← slotD 2 sb dsel (dWF claim.weights) sc.1 (g.getD 0 0)
  pure (sc, g, d)

/-- **The tape caller** (`tapeProgE2`): the separator, `r`, 25 scalars, the GKR, `n`'s range, the wiring. -/
def tapeD (w sb dsel : Nat) (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × KClaim FE2 ×
      ((List FE2 × FE2) × List FE2 × ((List FE2 × FE2) × List FE2 × ((FE × (List FE → FE)) × List FE)))) := do
  sepE2
  let r ← samplesG gC1 w
  let v ← readE2s 25
  let claim ← tapeGkrD w r v
  require (decide (1 ≤ n ∧ n ≤ 2 ^ w))
  let wo ← wireD w sb dsel s n claim
  pure (r, v, claim, wo)

/-! ## `KS` and its link -/

/-- `open` (`keccakOpenE2`). -/
def keccakOpenD (logSteps : Nat) (claim : KClaim FE2) (first count : Nat) (value : FE2) :
    DM (List FE2 × List FE2 × FE2) := do
  let sv ← sumcheckD gC2 value 3 (List.replicate qkeccakSlotBits none)
  pure (sv.1, foldRowsF sv.1 (slotWeightsF logSteps claim first count), sv.2)

/-- `verify_keccak` (`verifyKeccakE2`): the committed outputs' word claims `(point, word)`, the slice
point, the slices. -/
def verifyKeccakD (logSteps : Nat) (inst output : List FE2) :
    DM (List (List FE2 × FE2) × List FE2 × List FE2) := do
  let packBits := logSteps - 5
  let rLow := inst.take 5
  let segment ← samplesG gC1 keccakSegmentBits
  let lanePoint ← samplesG gC1 keccakLaneBits
  let committed ← if 1 < keccakSegments then readE2 else pure 0
  let first := firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed
  let claim ← keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.v1 logSteps (List.range keccakDepth) first
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

/-- **`KS`** (`callerProgE2`): `h` instance coordinates, 25 scalars, `verify_keccak`, the row switch. -/
def callerD (h : Nat) :
    DM (List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE)) := do
  let r ← samplesG gC1 h
  let v ← readE2s 25
  let res ← verifyKeccakD h r v
  let row ← rowSwitchD res.2.1 res.2.2
  pure (r, v, res, row)

/-- **The `KS` link** (`ksLinkProgE2`). -/
def ksLinkD (hk xl : Nat) (rows : List Nat) : DM (List FE2 × (List FE2 × FE2) × List FE2) := do
  let kchal ← samplesG gC1 (hk + 5)
  let kshift ← sumcheckD gC2 0 3 (List.replicate hk none)
  let vals ← readE2s 4
  require (kshift.2 == contShiftF rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 + selXF xl kshift.1 * vals.getD 3 0))
  pure (kchal, kshift, vals)


/-! ## `Quad Ext3` on words and the split of `E2` claims -/

/-- `Quad Ext3 = E3[X]/(X² + xX + 1)` on words: `re + im·X`. -/
structure FE6 where
  /-- The constant coordinate. -/
  re : FE
  /-- The `X` coordinate. -/
  im : FE

namespace FE6

/-- `x` in `E3`. -/
def xE : FE := FE.ofK FK.x

/-- The product (Karatsuba, `X² = 1 + xX`). -/
def mul (a b : FE6) : FE6 :=
  let p0 := a.re * b.re
  let p1 := a.im * b.im
  ⟨p0 + p1, (a.re + a.im) * (b.re + b.im) + p0 + p1 + xE * p1⟩

/-- `E2 → Quad Ext3`, coordinatewise. -/
def ofE2 (z : FE2) : FE6 := ⟨FE.ofK z.re, FE.ofK z.im⟩

/-- `E3 → Quad Ext3`. -/
def ofE (r : FE) : FE6 := ⟨r, 0⟩

end FE6

/-- **`V`'s word weight** (`wordW`): `Π_l (z_l·r_l + (1 + z_l)(1 + r_l))` in `Quad Ext3`. -/
def wordWD (z : List FE2) (r : List FE) : FE6 :=
  (List.zip z r).foldl (fun acc (zl, rl) =>
    let a := FE6.ofE2 zl
    let f := FE6.mul a (FE6.ofE rl)
    let g := FE6.mul ⟨1 + a.re, a.im⟩ ⟨1 + rl, 0⟩
    FE6.mul acc ⟨f.re + g.re, f.im + g.im⟩) ⟨1, 0⟩

/-- An `E2` sum claim's weight (`sumW6`) at an `E3` point. -/
def sumW6D (parts : List (FE2 × Placement × List FE2)) (x : List FE) : FE6 :=
  parts.foldl (fun acc (c, blk, z) =>
    let w := FE6.mul (FE6.mul (FE6.ofE2 c) (FE6.ofE (blk.eqAbove x))) (wordWD z (x.take blk.variableCount))
    ⟨acc.re + w.re, acc.im + w.im⟩) ⟨0, 0⟩

/-- **The split** (`splitE2`): two block claims on the whole stack, re then im. -/
def splitD (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) : List BlockClaim :=
  [⟨⟨nu, 0⟩, fun x => (sumW6D parts x).re, FE.ofK v.re⟩, ⟨⟨nu, 0⟩, fun x => (sumW6D parts x).im, FE.ofK v.im⟩]


/-! ## The small shape's tails at `E2` (`LvmShapeVN`'s `tailDF`, `ringTailF`) -/

/-- `z*_l` in `E2`. -/
def zStarE2 (l : Nat) : FE2 := FE2.ofK (Shape.zStarF l).c₀

/-- The mass of `eq(r, ·)` on `D`'s tail rows (`2^18 … 2^20 − 1`): `1 − (1 − r₁₈)(1 − r₁₉)`. -/
def tailMassE2 (r : List FE2) : FE2 := 1 - (1 - r.getD 18 0) * (1 - r.getD 19 0)

/-- **The tails of a `D` word claim's two halves** (re, im): coordinate `h` of `mass(r)·z*_l`. -/
def tailDE2 (r : List FE2) (l : Nat) : List FE :=
  let t := tailMassE2 r * zStarE2 l
  [FE.ofK t.re, FE.ofK t.im]

/-- The tail slices of the row switch on `C_main` at `z` (23 coordinates: 20 rows, 2 lanes, the block bit):
`s_i = mass(z)·Σ_l [bit i of z*_l]·eq(z₂₀,₂₁, l)·eq(z₂₂, 0)`. -/
def tailSlicesE2 (z : List FE2) : List FE2 :=
  let lanes := eqKernelF ((z.drop 20).take 2)
  let blk := eqEvalF (z.drop 22) (selPtF 0 (CMain.nu20 - 22))
  (List.range 64).map fun i =>
    tailMassE2 z * blk * sumF ((List.range 4).map fun l =>
      if (Shape.zStarF l).c₀.val.toNat.testBit i then lanes.getD l 0 else 0)

/-- **The row claim's tail**: the switched target of the tail slices with the same `r''`. -/
def rowTailE2 (eqR : List FE) (z : List FE2) : FE :=
  let sv := tailSlicesE2 z
  sumE ((List.range 128).map fun j => eqR.getD j 0 * FE.ofK (rowWordD sv j))

/-! ## The root pin -/

/-- **The root OOD pin** (after `C_main`'s cap): `ν` `E3` samples, one `E3` read; its point claim on the
physical stack, first in the list (E2F-P (6), the lead's `pinClaim`). -/
def pinD (nu : Nat) : DM BlockClaim := do
  let z ← samples nu
  let a ← readE
  pure (BlockClaim.point ⟨nu, 0⟩ z a)

/-! ## The front's claims with their tails, and the decision -/

/-- `KS`'s `Y` lane `l` at `E2` (`ksYPart`). -/
def ksYPartD (p : Params) (L : Layout0) (l : Nat) (pt : List FE2) : Placement × List FE2 :=
  if l < 14 then (⟨p.ksLog + slotLog, L.ks⟩, pt ++ selPtF (50 + l) slotLog)
  else (⟨p.ksLog, L.ksY2 + (l - 14) * 2 ^ p.ksLog⟩, pt)

/-- A split claim with zero tails. -/
def splitZ (nu : Nat) (parts : List (FE2 × Placement × List FE2)) (v : FE2) : List (Com × BlockClaim × FE) :=
  (splitD nu parts v).map fun c => (.main, c, 0)

/-- **The front's claims at S2GF with their tails** (`LvmE2VMid.assembleSF`'s order): the tape's four `D` word
claims (split; tails `tailDE2`), the row claim on `C_main` (tail `rowTailE2`), the boundary claims; `KS`'s output
word claims (split) and row claim; the 25 output lanes (split); the `KS` link's `[Y, in, M, X]` (split), in the
spec's `ordM` order: `X_re` before `M`'s halves, `X_im` last. -/
def frontClaimsD (p : Params) (pub : Pub)
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
      ((splitD p.nuMain [(1, blkD, r ++ selPtF l 2)] (v.getD l 0)).zip (tailDE2 r l)).map fun e =>
        (.main, e.1, e.2)) ++
    [(.main, ⟨⟨p.nuMain, 0⟩, wo.2.2.2.2.1.2, wo.2.2.2.2.1.1⟩, rowTailE2 wo.2.2.2.2.2 rowPt)] ++
    (pub.h.zipIdx.map fun (w, l) =>
      (.main, BlockClaim.point blkD (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w), 0))
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let ks : List (Com × BlockClaim × FE) :=
    (co.2.2.1.1.flatMap fun c => splitZ p.nuMain [(1, ksBlk, c.1)] c.2) ++
      [(.main, ⟨ksBlk, co.2.2.2.1.2, co.2.2.2.1.1⟩, 0)]
  let ksOut : List (Com × BlockClaim × FE) := (List.range 25).flatMap fun l =>
    let bz := ksYPartD p L l co.1
    splitZ p.nuMain [(1, bz.1, bz.2)] (co.2.1.getD l 0)
  let om := eqKernelF (lo.1.drop p.ksLog)
  let rho' := lo.2.1.1
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let xlo := rho'.take xl
  let sel := selXF xl rho'
  let vals := lo.2.2
  let mC := splitZ p.nuMain ((List.range 17).map (fun l => (om.getD l 0, (⟨p.ksLog, L.s + l * R⟩ : Placement), rho')) ++
      (List.range 17).map (fun l => (om.getD l 0 * sel, (⟨xl, L.s + l * R + ksSplit p⟩ : Placement), xlo)))
      (vals.getD 2 0)
  let xC := splitZ p.nuMain ((List.range 17).map fun l => (om.getD l 0, (⟨xl, L.x + l * R⟩ : Placement), xlo))
      (vals.getD 3 0)
  -- the spec's order (`midM`'s `ordM`: the relocated `C_rec` claims, here `M`'s two halves, go before the last
  -- `C_main` claim, here `X`'s im half): `Y_re, Y_im, in_re, in_im, X_re, M_re, M_im, X_im`
  let link : List (Com × BlockClaim × FE) :=
    splitZ p.nuMain ((List.range 25).map fun l => let bz := ksYPartD p L l rho'; (om.getD l 0, bz.1, bz.2))
      (vals.getD 0 0) ++
    splitZ p.nuMain ((List.range 25).map fun l => (om.getD l 0, ksBlk, rho' ++ selPtF l slotLog)) (vals.getD 1 0) ++
    xC.take 1 ++ mC ++ xC.drop 1
  tape ++ ks ++ ksOut ++ link

/-- **The opening at S2GF**: the pin's claim first on the physical stack (not relocated; its weight `eq(z, ·)` on the
stack's `ν` coordinates, as the lead's `pinClaim`), then the other claims, through `onStackZBN` when small. -/
def dOpenF (p : Params) (s : Bool) (pin : BlockClaim) (claims : List (Com × BlockClaim × FE)) : DM Unit := do
  require (claims.all (·.1 == .main))
  let cm := (claims.filter (·.1 == .main)).map (·.2)
  verifyStackedOpening p.mainLevels p.nuMain
    ((pin.weight, pin.value) :: if s then cm.map fun e => TypedV.onStackZBN p.nuMain e.1 e.2 else cm.map (·.1.onStack))
    false p.grind p.mainOod

/-- **The decision program of the `E2` front's stages** (S2GF, S2GT), generic in the public values' reader `pubR`
(S2GF: `pubOfA p.accV`; S2GT: 16-B scalars) and the `KS` link's continuation rows `rows`: the public values, the cap,
the pin, the typed phases (`typed`; their claims, then the mini-bus's table claims with zero tails), the `E2` front,
the openings. -/
def decideProgFG (pubR : Vector UInt8 32 → Vector UInt8 32 → ByteArray → Pub) (rows : List ℕ) (p : Params)
    (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubR vk c sig
  let m := m3 p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, tcl, evals) ← typed m pub
  let tp ← tapeD p.logN (dSelBits p) (dSel p) pub.s pub.n
  let co ← callerD p.ksLog
  let lo ← ksLinkD p.ksLog (ksXLog p) rows
  dOpenF p (TypedV.smallT p pub) pin
    (tcl ++ Shape.zeroTails (m.tableClaims pub evals) ++ frontClaimsD p pub tp co lo)
  pure acc

/-- **The decision program at S2GF** (`decideProgFG` with `acc_in` of `p.accV` coordinates, `pubOfA`, and S2GF's
continuation rows). -/
def decideProgF (p : Params)
    (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) : DM Acc :=
  decideProgFG (pubOfA p.accV) contRowsF p typed m3 vk c

end Lvm
