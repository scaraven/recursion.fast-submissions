-- New for lvm6 (MUL2): the `E2` products of V's Keccak reductions (the GKR layers, the input ends, the sponge link)
-- and of the tree, sponge and commitment phases' point claims on MUL's `m2B`. Each twin is its original with the hot
-- products as `m2B`; each `_eq` is unconditional.
import Lvm6VS1Ks
import Lvm6VMulB
import LvmE2VRingA

/-!
# MUL2: the Keccak reductions on `m2B`

The tree and sponge phases spend most of their `E2` products in a few generic kernels (`corrAF`, `weightedCF`,
`weightedRefF`, `eqKernelAF`, `outerUGF`, `eqAtF`, `treeFast`, `spFast`, the link's shift sum). At `F = FE2` each `*`
there is `FE2.mul`: four out-of-line `FK.mul` (the fourth is `x·p₁`). `m2B` (`Lvm6VMulB`) is the same product with
six `bmul64`, seven bit reversals and two reductions (`m2B_mul : m2B a b = a * b`).

* kernels: `eqKernelAFB`, `eqAtFB`, `corrAFB`, `weightedCFB`, `weightedRefFB`, `outerUGFB`, `treeFastB`,
  `spFastB`, `eqSpHB`, `contShiftHB`, `polyEvalFB`, `fSumcheckB`, `laneWAB`, each with `_eq` (its original at
  `FE2`);
* the chain to the phases, each the original with its callees replaced: `WRep.dotB`, `fLayerTailB`, `fLayerB`,
  `fLayersB`, `firstWArrB`, `fFirstB`, `midWtFB`, `fKHead6B`, `WRep.arrB`, `toKFB`, `treeSumFB`, `spSumFB`,
  `fTreeEnd6B`, `fSpongeEnd6B`, `fTreeProgB`, `fTreeProgS6B`, `fSpongeCore6B`, `fSpCaller6B`, `fKsLinkB`;
* the phases' claims: `eqPtFB` (one product a coordinate: `r t + (1 + r)(1 + t) = 1 + r + t` in characteristic two,
  `eqPt_term`), `pcFB`, `laneSFB`, `cmBaseFB`, `cmTabFB`, `cMFB`, `treePhFB`, `spSFB`; the commitment phase over
  `pcFB`, **`fCommit6B`** (`= fCommit6`);
* **`fSpongePhase6B`** (`= fSpongePhase6H`) and **`fTreeProgS6B`** (`= fTreeProgS6`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open LeanVM.Protocol.KeccakGkr (Shape)
open Finset

/-- **`m2B` is the product of `FE2`.** -/
theorem m2B_mul (a b : FE2) : m2B a b = a * b := (m2B_eq a b).trans (Lvm.Typed.KT.m2_eq a b)

/-! ## Kernels -/

/-- `eqKernelAF` on `m2B`. -/
def eqKernelAFB (point : List FE2) : Array FE2 :=
  point.foldl (fun out r => out.map (fun v => m2B v (1 + r)) ++ out.map (fun v => m2B v r)) #[1]

theorem eqKernelAFB_eq (point : List FE2) : eqKernelAFB point = eqKernelAF point := by
  simp only [eqKernelAFB, eqKernelAF, m2B_mul]

/-- `eqAtF` on `m2B`. -/
def eqAtFB : List FE2 → ℕ → FE2
  | [], _ => 1
  | r :: rs, w => m2B (if w % 2 = 1 then r else 1 + r) (eqAtFB rs (w / 2))

theorem eqAtFB_eq : ∀ (ρ : List FE2) (w : ℕ), eqAtFB ρ w = eqAtF ρ w
  | [], _ => rfl
  | r :: rs, w => by
    rw [eqAtFB, Lvm.E2V.eqAtF, eqAtFB_eq rs, m2B_mul]

/-- `corrAF` on `m2B`. -/
def corrAFB (t : Array (FE2 × FE2 × FE2)) (r : Nat) : FE2 := Id.run do
  let mut v0 : FE2 := 1
  let mut v1 : FE2 := 0
  for k in [:6] do
    let (m01, m10, d) := t.getD k (0, 0, 0)
    if (r >>> k) % 2 == 0 then
      (v0, v1) := (m2B v0 d + m2B v1 m01, m2B v1 m10)
    else
      (v0, v1) := (m2B v0 m01, m2B v0 m10 + m2B v1 d)
  return v0 + v1

theorem corrAFB_eq : corrAFB = corrAF := by
  funext t r
  simp only [corrAFB, corrAF, m2B_mul]

/-- `weightedCF` on `m2B`. -/
def weightedCFB (corr : Nat → FE2) (eqL laneW : Array FE2) : FE2 := Id.run do
  let S : Array FE2 := (Array.range 5).map fun c =>
    eqL.getD c 0 + eqL.getD (c + 5) 0 + eqL.getD (c + 10) 0 + eqL.getD (c + 15) 0 + eqL.getD (c + 20) 0
  let mut acc : FE2 := 0
  for l in [:25] do
    let x := l % 5
    let rl := rhoA.getD l 0
    acc := acc + m2B (laneW.getD (Lvm.keccakPi l) 0)
      (m2B (eqL.getD l 0 + S.getD ((x + 4) % 5) 0) (corr rl) + m2B (S.getD ((x + 1) % 5) 0) (corr ((rl + 1) % 64)))
  return acc

theorem weightedCFB_eq (corr : Nat → FE2) (eqL laneW : Array FE2) :
    weightedCFB corr eqL laneW = weightedCF corr eqL laneW := by
  simp only [weightedCFB, weightedCF, m2B_mul]

/-- `weightedRefF` on `m2B`. -/
def weightedRefFB (eqZ eqL : Array FE2) (w : List FE2) : FE2 :=
  let w := w.toArray
  sumF ((List.range 25).map fun l => m2B (eqL.getD l 0)
    (sumF ((List.range 64).map fun z => m2B (eqZ.getD z 0) (w.getD (64 * l + z) 0))))

theorem weightedRefFB_eq (eqZ eqL : Array FE2) (w : List FE2) :
    weightedRefFB eqZ eqL w = weightedRefF eqZ eqL w := by
  simp only [weightedRefFB, weightedRefF, m2B_mul]

/-- `outerUGF` on `m2B`. -/
def outerUGFB (A laneW : Array FE2) : List FE2 :=
  (List.range keccakBits).map fun j => m2B (A.getD (j % 64) 0) (laneW.getD (j / 64) 0)

theorem outerUGFB_eq (A laneW : Array FE2) : outerUGFB A laneW = outerUGF A laneW := by
  simp only [outerUGFB, outerUGF, m2B_mul]

/-- `treeFast` on `m2B`. -/
def treeFastB (A B C : FE2) (e w s : ℕ → FE2) : FE2 :=
  ∑ o ∈ range 33, m2B (e o)
    ((if o < 8 then m2B (A + if o < 4 then B else 0) (∑ z ∈ range 64, m2B (shG w o z) (s z)) else 0) +
      (if 8 ≤ o then m2B C (∑ z ∈ range 64, m2B (w (64 * (o - 8) + z)) (s z)) else 0))

theorem treeFastB_eq (A B C : FE2) (e w s : ℕ → FE2) : treeFastB A B C e w s = treeFast A B C e w s := by
  simp only [treeFastB, treeFast, m2B_mul]

/-- `spFast` on `m2B`. -/
def spFastB (e1 e w s : ℕ → FE2) : FE2 :=
  ∑ m ∈ range 2, m2B (e1 m) (∑ l ∈ range 25, m2B (e (25 * m + l)) (∑ z ∈ range 64, m2B (w (64 * l + z)) (s z)))

theorem spFastB_eq (e1 e w s : ℕ → FE2) : spFastB e1 e w s = spFast e1 e w s := by
  simp only [spFastB, spFast, m2B_mul]

/-- `eqSpH` on `m2B`. -/
def eqSpHB (ρ : List FE2) (ok : Bool) (N : ℕ) (lo hi : Array FE2) (i : ℕ) : FE2 :=
  if ok && decide (i < N) then m2B (lo.getD (i % 64) 0) (hi.getD (i / 64) 0) else eqAtFB ρ i

theorem eqSpHB_eq (ρ : List FE2) (ok : Bool) (N : ℕ) (lo hi : Array FE2) (i : ℕ) :
    eqSpHB ρ ok N lo hi i = eqSpH ρ ok N lo hi i := by
  simp only [eqSpHB, eqSpH, m2B_mul, eqAtFB_eq]

/-- `contShiftH` on `m2B`. -/
def contShiftHB (rows : List ℕ) (ρ ρ' : List FE2) : FE2 :=
  let lo := eqKernelAFB (ρ.take 6)
  let hi := eqKernelAFB (ρ.drop 6)
  let lo' := eqKernelAFB (ρ'.take 6)
  let hi' := eqKernelAFB (ρ'.drop 6)
  let n := ρ.length
  let n' := ρ'.length
  let ok := decide (6 ≤ n)
  let ok' := decide (6 ≤ n')
  let N := 2 ^ n
  let N' := 2 ^ n'
  rows.foldl (fun acc i => acc + m2B (eqSpHB ρ ok N lo hi i) (eqSpHB ρ' ok' N' lo' hi' (i - 1))) 0

theorem contShiftHB_eq (rows : List ℕ) (ρ ρ' : List FE2) : contShiftHB rows ρ ρ' = contShiftH rows ρ ρ' := by
  simp only [contShiftHB, contShiftH, eqKernelAFB_eq, eqSpHB_eq, m2B_mul]

/-- `polyEvalF` on `m2B`. -/
def polyEvalFB (coefficients : List FE2) (point : FE2) : FE2 :=
  coefficients.foldr (fun c acc ↦ m2B acc point + c) 0

theorem polyEvalFB_eq : polyEvalFB = polyEvalF := by
  funext coefficients point
  simp only [polyEvalFB, polyEvalF, m2B_mul]

/-- `fSumcheck` over `polyEvalFB`. -/
def fSumcheckB (g : ℕ) (claim : FE2) (count : ℕ) : List (Option FE2) → VF (List FE2 × FE2)
  | [] => VF.pure ([], claim)
  | mode :: modes => VF.bind (fRoundPoly count claim mode) fun msg => VF.bind (fE2Sample g) fun c =>
      VF.bind (fSumcheckB g (polyEvalFB msg c) count modes) fun res => VF.pure (c :: res.1, res.2)

theorem fSumcheckB_eq (g count : ℕ) : ∀ (modes : List (Option FE2)) (claim : FE2),
    fSumcheckB g claim count modes = fSumcheck g claim count modes
  | [], _ => rfl
  | mode :: modes, claim => by
    simp only [fSumcheckB, fSumcheck, polyEvalFB_eq, fSumcheckB_eq g count modes]

/-- `laneWA` on `m2B`. -/
def laneWAB (eqL : Array FE2) (beta : FE2) : Array FE2 :=
  (Array.range 25).map fun l => eqL.getD l 0 + m2B beta (eqL.getD ((l % 5 + 4) % 5 + 5 * (l / 5)) 0 +
    m2B beta (eqL.getD ((l % 5 + 3) % 5 + 5 * (l / 5)) 0))

theorem laneWAB_eq (eqL : Array FE2) (beta : FE2) : laneWAB eqL beta = laneWA eqL beta := by
  simp only [laneWAB, laneWA, m2B_mul]

/-! ## The GKR layers -/

/-- `WRep.dot` on the kernels. -/
def WRep.dotB : WRep → List FE2 → Array FE2 → Array FE2 → FE2
  | .mat w, _, eqZ, eqL => weightedRefFB eqZ eqL w.toList
  | .tro pA _ ℓ _ _, q, _, eqL => weightedCFB (corrAFB (corrTabF q pA)) eqL ℓ

theorem WRep.dotB_eq : WRep.dotB = WRep.dot := by
  funext W q eqZ eqL
  cases W <;> simp only [WRep.dotB, WRep.dot, weightedRefFB_eq, weightedCFB_eq, corrAFB_eq]

/-- `fLayerTail` on the kernels. -/
def fLayerTailB (c : LClaim) (s : FE2) (point : List FE2) (lv : List FE2 × FE2) : VF LClaim :=
  VF.bind (fE2Reads 3) fun t =>
  VF.guard (decide (c.W.dotB (z6 lv.1) (eqKernelAFB (z6 lv.1)) (eqKernelAFB (lv.1.drop 6)) *
      (sumF (instWeightsF s) * t.getD 0 0 + (sumF (instWeightsF s) + t.getD 1 0) * t.getD 2 0) = lv.2)) <|
  VF.bind (fE2Sample gC2) fun beta =>
  VF.pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), instWeightsF s, point,
    .tro (z6 lv.1) (eqKernelAFB (z6 lv.1)) (laneWAB (eqKernelAFB (lv.1.drop 6)) beta) (z6_length _)
      (eqKernelAFB_eq _)⟩

theorem fLayerTailB_eq : fLayerTailB = fLayerTail := by
  funext c s point lv
  simp only [fLayerTailB, fLayerTail, WRep.dotB_eq, eqKernelAFB_eq, laneWAB_eq]

/-- `fLayer` over `fLayerTailB`. -/
def fLayerB (logSteps step : ℕ) (c : LClaim) : VF LClaim :=
  VF.bind (fE2Reads LeanVM.Protocol.Verifier.productBits) fun product =>
  VF.guard (decide (projectedF (⟨0, c.mu, [], []⟩ : KClaim FE2) product +
      iotaG Shape.v1 logSteps step c.point c.W.rc * sumF c.mu = c.value)) <|
  VF.bind (fE2Sample gC46) fun s =>
  VF.bind (fPackRoundsN gC3 c.point (polyEvalFB product s)) fun vp =>
  VF.bind (fSumcheckB gC3 vp.1 4 (List.replicate LeanVM.Protocol.Verifier.keccakLocalBits none)) fun lv =>
  fLayerTailB c s vp.2 lv

theorem fLayerB_eq : fLayerB = fLayer := by
  funext logSteps step c
  simp only [fLayerB, fLayer, fLayerTailB_eq, polyEvalFB_eq, fSumcheckB_eq]

/-- `fLayers` over `fLayerB`. -/
def fLayersB (logSteps : ℕ) : List ℕ → LClaim → VF LClaim
  | [], c => VF.pure c
  | step :: steps, c => VF.bind (fLayerB logSteps step c) fun c' => fLayersB logSteps steps c'

theorem fLayersB_eq (logSteps : ℕ) :
    ∀ (steps : List ℕ) (c : LClaim), fLayersB logSteps steps c = fLayers logSteps steps c
  | [], _ => rfl
  | step :: steps, c => by
    simp only [fLayersB, fLayers, fLayerB_eq, fLayersB_eq logSteps steps]

/-- `firstWArr` on the kernels. -/
def firstWArrB (lp : List FE2) : Array FE2 :=
  let E := eqKernelAFB lp
  ((List.range keccakBits).map fun j => m2B (E.getD (j / 64) 0) (xsTab.getD (j % 64) 0)).toArray

theorem firstWArrB_eq (lp : List FE2) : firstWArrB lp = firstWArr lp := by
  simp only [firstWArrB, firstWArr, eqKernelAFB_eq, m2B_mul]

/-- `fFirst` over `firstWArrB`. -/
def fFirstB (inst segment lanesPt output : List FE2) (committed : FE2) : LClaim :=
  ⟨committed + (eqKernelF segment).getD (Shape.v1.segments - 1) 0 * dotF ((eqKernelF lanesPt).take 25) output,
    eqKernelF (inst.take 4), inst.drop 4 ++ segment, .mat (firstWArrB lanesPt)⟩

theorem fFirstB_eq (inst segment lanesPt output : List FE2) (committed : FE2) :
    fFirstB inst segment lanesPt output committed = fFirst inst segment lanesPt output committed := by
  simp only [fFirstB, fFirst, firstWArrB_eq]

/-- `midWtF` on `eqAtFB`. -/
def midWtFB (base : ℕ) (rseg : FE2) (rlane ϱ : List FE2) : FE2 :=
  (1 + rseg) * ∑ l ∈ range 25, m2B (eqAtFB ϱ (base + l)) (eqAtFB rlane l)

theorem midWtFB_eq (base : ℕ) (rseg : FE2) (rlane ϱ : List FE2) :
    midWtFB base rseg rlane ϱ = midWtF base rseg rlane ϱ := by
  simp only [midWtFB, midWtF, eqAtFB_eq, m2B_mul]

/-- `fKHead6` over `fLayersB`, `fFirstB`, `midWtFB`. -/
def fKHead6B (P base : ℕ) (inst output : List FE2) : VF HeadOutF :=
  VF.bind (fGPoint Lvm6.K.gSeg 5) fun sl =>
  VF.bind fReadF fun cst =>
  VF.bind (fLayersB (P + 4) (List.range 12) (fFirstB inst (sl.take 1) (sl.drop 1) output cst)) fun claim =>
  VF.bind (fSumcheckB gC2 cst 3 (List.replicate 6 none)) fun om =>
  VF.bind fReadF fun cout =>
  VF.guard (decide (midWtFB base (sl.headD 0) (sl.drop 1) om.1 * cout = om.2))
    (VF.pure ⟨sl, cst, claim, om.1, cout⟩)

theorem fKHead6B_eq : fKHead6B = fKHead6 := by
  funext P base inst output
  simp only [fKHead6B, fKHead6, fLayersB_eq, fFirstB_eq, midWtFB_eq, fSumcheckB_eq]

/-- `WRep.arr` on `outerUGFB`. -/
def WRep.arrB : WRep → Array FE2
  | .mat w => w
  | .tro _ A ℓ _ _ => (linearTransposeF (outerUGFB A ℓ)).toArray

theorem WRep.arrB_eq : WRep.arrB = WRep.arr := by
  funext W
  cases W <;> simp only [WRep.arrB, WRep.arr, outerUGFB_eq]

/-- `toKF` over `WRep.arrB`. -/
def toKFB (c : LClaim) : KClaimF := ⟨c.value, c.mu, c.point, c.W.arrB⟩

theorem toKFB_eq : toKFB = toKF := by
  funext c
  simp only [toKFB, toKF, WRep.arrB_eq]

/-! ## The input ends -/

/-- `treeSumF` on `treeFastB`, `eqAtFB`. -/
def treeSumFB (P : ℕ) (c : KClaimF) (ϱ s : List FE2) : FE2 :=
  let rseg := c.point.getD P 0
  let rtop := c.point.getD (P - 1) 0
  let ϱtop := ϱ.getD 4 0
  let sA := s.toArray
  treeFastB ((1 + rseg) * (1 + rtop) * (1 + ϱtop)) ((1 + rseg) * (rtop * ϱtop)) (rseg * (1 + rtop + ϱtop))
    (eqAtFB (ϱ.drop 5)) (fun i => c.weights.getD i 0) (fun i => sA.getD i 0)

theorem treeSumFB_eq : treeSumFB = treeSumF := by
  funext P c ϱ s
  have e : eqAtFB (ϱ.drop 5) = eqAtF (ϱ.drop 5) := funext (eqAtFB_eq _)
  simp only [treeSumFB, treeSumF, treeFastB_eq, e]

/-- `spSumF` on `spFastB`, `eqAtFB`. -/
def spSumFB (P : ℕ) (c : KClaimF) (ϱ s : List FE2) : FE2 :=
  let sA := s.toArray
  spFastB (eqAtFB [c.point.getD P 0]) (eqAtFB (ϱ.drop 4)) (fun i => c.weights.getD i 0) (fun i => sA.getD i 0)

theorem spSumFB_eq : spSumFB = spSumF := by
  funext P c ϱ s
  have e1 : eqAtFB [c.point.getD P 0] = eqAtF [c.point.getD P 0] := funext (eqAtFB_eq _)
  have e : eqAtFB (ϱ.drop 4) = eqAtF (ϱ.drop 4) := funext (eqAtFB_eq _)
  simp only [spSumFB, spSumF, spFastB_eq, e1, e]

/-- `fTreeEnd6` over `treeSumFB`. -/
def fTreeEnd6B (P : ℕ) (c : KClaimF) : VF EndOutF :=
  VF.bind (fSumcheckB gC2 (treeV'F P c) 3 (List.replicate 11 none)) fun lv =>
  VF.bind (fE2Reads 64) fun s =>
  VF.guard (decide (multilinearEvalF c.mu (lv.1.take 4) * treeSumFB P c lv.1 s = lv.2))
    (VF.pure ⟨lv.1, lv.1.take 4 ++ c.point.take (P - 1) ++ [lv.1.getD 4 0] ++ lv.1.drop 5, s⟩)

theorem fTreeEnd6B_eq : fTreeEnd6B = fTreeEnd6 := by
  funext P c
  simp only [fTreeEnd6B, fTreeEnd6, treeSumFB_eq, fSumcheckB_eq]

/-- `fSpongeEnd6` over `spSumFB`. -/
def fSpongeEnd6B (P : ℕ) (c : KClaimF) : VF EndOutF :=
  VF.bind (fSumcheckB gC2 c.value 3 (List.replicate 10 none)) fun lv =>
  VF.bind (fE2Reads 64) fun s =>
  VF.guard (decide (multilinearEvalF c.mu (lv.1.take 4) * spSumFB P c lv.1 s = lv.2))
    (VF.pure ⟨lv.1, lv.1.take 4 ++ c.point.take P ++ lv.1.drop 4, s⟩)

theorem fSpongeEnd6B_eq : fSpongeEnd6B = fSpongeEnd6 := by
  funext P c
  simp only [fSpongeEnd6B, fSpongeEnd6, spSumFB_eq, fSumcheckB_eq]

/-! ## The tree and sponge programs -/

/-- `fTreeProg` over `fKHead6B`, `fTreeEnd6B`, `toKFB`. -/
def fTreeProgB (κ : ℕ) : VF TreeOutF :=
  VF.bind (fKReads 4) fun δ =>
  VF.bind (fGPoint Lvm6.K.gRho (κ - 2)) fun ρ =>
  VF.bind (fE2Reads 8) fun dd =>
  VF.bind (fE2Sample Lvm6.K.gU) fun u =>
  VF.bind (fE2Reads 21) fun o' =>
  VF.bind (fKHead6B (κ - 4) 8 (u :: ρ) (oLowF u dd ++ o')) fun hd =>
  VF.bind (fTreeEnd6B (κ - 4) (toKFB hd.claim)) fun en =>
  VF.pure ⟨δ, ρ, dd, u, oLowF u dd ++ o', hd, en⟩

theorem fTreeProgB_eq : fTreeProgB = fTreeProg := by
  funext κ
  simp only [fTreeProgB, fTreeProg, fKHead6B_eq, fTreeEnd6B_eq, toKFB_eq]

/-- **`fTreeProgS6` over `fTreeProgB`.** -/
def fTreeProgS6B (sh : Lvm6.Shape) (x : Lvm6.Hdr) : VF TreeSF :=
  if Lvm6.K.TreeShapeOK sh ∧ sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN ∧ sh.logN ≤ 28 then
    VF.bind (fTreeProgB (sh.logN + 1)) fun out => VF.pure (toSF (sh.logN + 1) x.h out)
  else fun _ _ => none

theorem fTreeProgS6B_eq : fTreeProgS6B = fTreeProgS6 := by
  funext sh x
  simp only [fTreeProgS6B, fTreeProgS6, fTreeProgB_eq]

/-- `fSpongeCore6` over `fKHead6B`, `fSpongeEnd6B`, `toKFB`. -/
def fSpongeCore6B (P : ℕ) (inst output : List FE2) : VF (HeadOutF × EndOutF) :=
  VF.bind (fKHead6B P 25 inst output) fun hd =>
  VF.bind (fSpongeEnd6B P (toKFB hd.claim)) fun en => VF.pure (hd, en)

theorem fSpongeCore6B_eq : fSpongeCore6B = fSpongeCore6 := by
  funext P inst output
  simp only [fSpongeCore6B, fSpongeCore6, fKHead6B_eq, fSpongeEnd6B_eq, toKFB_eq]

/-- `fSpCaller6` over `fSpongeCore6B`. -/
def fSpCaller6B (h : ℕ) : VF (List FE2 × List FE2 × (HeadOutF × EndOutF)) :=
  VF.bind (fE2Samples gC1 h) fun r =>
  VF.bind (fE2Reads 25) fun v =>
  VF.bind (fSpongeCore6B (h - 4) r v) fun res => VF.pure (r, v, res)

theorem fSpCaller6B_eq : fSpCaller6B = fSpCaller6 := by
  funext h
  simp only [fSpCaller6B, fSpCaller6, fSpongeCore6B_eq]

/-- `fKsLinkH` over `contShiftHB`. -/
def fKsLinkB (hk xl : ℕ) (rows : List ℕ) : VF (List FE2 × (List FE2 × FE2) × List FE2) :=
  VF.bind (fE2Samples gC1 (hk + 5)) fun kchal =>
  VF.bind (fSumcheckB gC2 0 3 (List.replicate hk none)) fun kshift =>
  VF.bind (fE2Reads 4) fun vals =>
  VF.guard (decide (kshift.2 = contShiftHB rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 + selXF xl kshift.1 * vals.getD 3 0)))
    (VF.pure (kchal, kshift, vals))

theorem fKsLinkB_eq : fKsLinkB = fKsLinkH := by
  funext hk xl rows
  simp only [fKsLinkB, fKsLinkH, contShiftHB_eq, fSumcheckB_eq]

/-! ## The tree and sponge phases' claims -/

private theorem fk_add_self (a : FK) : a + a = 0 := by
  cases a with
  | mk v => show FK.mk (v ^^^ v) = FK.mk 0; rw [UInt64.xor_self]

private theorem fe2_add_self (a : FE2) : a + a = 0 := by
  cases a with
  | mk re im => show FE2.mk (re + re) (im + im) = FE2.mk 0 0; rw [fk_add_self, fk_add_self]

/-- In characteristic two, `r t + (1 + r)(1 + t) = 1 + r + t`. -/
theorem eqPt_term (r t : FE2) : r * t + (1 + r) * (1 + t) = 1 + r + t := by
  linear_combination fe2_add_self (r * t)

/-- `eqPtF` with one product a coordinate (`eqPt_term`), on `m2B`. -/
def eqPtFB : List FE2 → List FE2 → FE2
  | r :: a, t :: b => m2B (1 + r + t) (eqPtFB a b)
  | _, _ => 1

theorem eqPtFB_eq : ∀ (a b : List FE2), eqPtFB a b = eqPtF a b
  | r :: a, t :: b => by
    rw [eqPtFB, eqPtFB_eq a b, m2B_mul, eqPtF, eqPtF, List.zipWith_cons_cons, List.prod_cons, eqPt_term]
  | [], _ => by simp only [eqPtFB, eqPtF, List.zipWith_nil_left, List.prod_nil]
  | _ :: _, [] => by simp only [eqPtFB, eqPtF, List.zipWith_nil_right, List.prod_nil]

/-- `pcF` over `eqPtFB`. -/
def pcFB (c : List FE2 × FE2) : FClaim := ⟨fun x => eqPtFB c.1 x, c.2⟩

theorem pcFB_eq : pcFB = pcF := by
  funext c
  simp only [pcFB, pcF, eqPtFB_eq]

/-- `laneSF` over `eqAtFB`, `eqPtFB`. -/
def laneSFB (lam p : List FE2) (base n w : ℕ) (v : FE2) : FClaim :=
  ⟨fun x => ∑ l ∈ range n, m2B (eqAtFB lam l) (eqPtFB (p ++ bitsF (base + l) w) x), v⟩

theorem laneSFB_eq : laneSFB = laneSF := by
  funext lam p base n w v
  simp only [laneSFB, laneSF, eqAtFB_eq, eqPtFB_eq, m2B_mul]

/-- `cmBaseF` over `eqAtFB`. -/
def cmBaseFB (ρ lam : List FE2) (X L : ℕ) : FE2 :=
  m2B (∑ x ∈ range X, eqAtFB ρ x) (∑ l ∈ range L, eqAtFB lam l)

theorem cmBaseFB_eq : cmBaseFB = cmBaseF := by
  funext ρ lam X L
  simp only [cmBaseFB, cmBaseF, eqAtFB_eq, m2B_mul]

/-- `cmTabF` on `m2B`. -/
def cmTabFB (ρ lam : List FE2) : List FE2 → ℕ → ℕ → Array FE2
  | [], X, L => Array.ofFn (n := 72) fun j => cmBaseFB ρ lam (X + j.1 / 2 % 2) (L + j.1 % 2)
  | y :: Y, X, L =>
    let nxt := cmTabFB ρ.tail lam.tail Y (X / 2) (L / 2)
    let ws : Array FE2 := Array.ofFn (n := 8) fun k => cmWF ρ lam y (k.1 / 4) (k.1 / 2 % 2) (k.1 % 2)
    Array.ofFn (n := 72) fun i =>
      let p := i.1 / 4 % 2
      let X' := X + i.1 / 2 % 2
      let L' := L + i.1 % 2
      m2B (ws.getD (4 * p + 0) 0) (nxt.getD (C44.cmIdx 0 0 (i.1 / 4) X' L' X L) 0) +
        m2B (ws.getD (4 * p + 1) 0) (nxt.getD (C44.cmIdx 0 1 (i.1 / 4) X' L' X L) 0) +
        (m2B (ws.getD (4 * p + 2) 0) (nxt.getD (C44.cmIdx 1 0 (i.1 / 4) X' L' X L) 0) +
        m2B (ws.getD (4 * p + 3) 0) (nxt.getD (C44.cmIdx 1 1 (i.1 / 4) X' L' X L) 0))

theorem cmTabFB_eq : ∀ (ρ lam Y : List FE2) (X L : ℕ), cmTabFB ρ lam Y X L = cmTabF ρ lam Y X L
  | ρ, lam, [], X, L => by simp only [cmTabFB, cmTabF, cmBaseFB_eq]
  | ρ, lam, y :: Y, X, L => by simp only [cmTabFB, cmTabF, cmTabFB_eq ρ.tail lam.tail Y, m2B_mul]

/-- `cMF` over `cmTabFB`. -/
def cMFB (ρ' lam : List FE2) (v : FE2) : FClaim :=
  ⟨fun x => m2B (eqAtFB ((x.take 24).drop 18) 33) ((cmTabFB ρ' lam ((x.take 24).take 18) 7168 17).getD 0 0), v⟩

theorem cMFB_eq : cMFB = cMF := by
  funext ρ' lam v
  simp only [cMFB, cMF, eqAtFB_eq, cmTabFB_eq, m2B_mul]

/-- `treePhF` over `pcFB`. -/
def treePhFB (t : TreeSF) : PhF := (⟨t.pt, t.s⟩, t.cols.map pcFB)

theorem treePhFB_eq : treePhFB = treePhF := by
  funext t
  simp only [treePhFB, treePhF, pcFB_eq]

/-- `spSF` over `pcFB`, `laneSFB`, `cMFB`. -/
def spSFB (o : List FE2 × List FE2 × (HeadOutF × EndOutF)) (lk : LkF) : PhF :=
  (⟨o.2.2.2.pt ++ bitsF 17 5, o.2.2.2.s⟩,
    pcFB (o.1 ++ o.2.2.1.ϱm ++ bitsF 17 5, o.2.2.1.cout) ::
      ((List.range 25).map (fun l => pcFB (o.1 ++ bitsF (40 * 32 + l) 11, o.2.1.getD l 0)) ++
        [laneSFB (lk.1.drop 13) lk.2.1.1 (40 * 32) 25 11 (lk.2.2.getD 0 0),
          laneSFB (lk.1.drop 13) lk.2.1.1 (17 * 64) 25 11 (lk.2.2.getD 1 0),
          cMFB lk.2.1.1 (lk.1.drop 13) (lk.2.2.getD 2 0),
          laneSFB (lk.1.drop 13) (lk.2.1.1.take 10) (42 * 2 ^ 8) 17 14 (lk.2.2.getD 3 0)]))

theorem spSFB_eq : spSFB = spSF := by
  funext o lk
  simp only [spSFB, spSF, pcFB_eq, laneSFB_eq, cMFB_eq]

/-- **`fSpongePhase6H` over `fSpCaller6B`, `fKsLinkB`, `spSFB`.** -/
def fSpongePhase6B (sh : Lvm6.Shape) : VF PhF :=
  if SP.SpShapeOK sh then
    VF.bind (fSpCaller6B 13) fun o => VF.bind (fKsLinkB 13 10 SP.contRows6) fun lk => VF.pure (spSFB o lk)
  else fun _ _ => none

theorem fSpongePhase6B_eq : fSpongePhase6B = fSpongePhase6H := by
  funext sh
  simp only [fSpongePhase6B, fSpongePhase6H, fSpCaller6B_eq, fKsLinkB_eq, spSFB_eq]

/-- **`fCommit6` over `pcFB`.** -/
def fCommit6B (sh : Lvm6.Shape) : VF FClaim :=
  VF.bind (fCommit (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd) fun _ =>
  VF.bind (VF.bind fSample fun _ => VF.pure ()) fun _ =>
  VF.bind (fGrp (sh.lvl 0).gOod (sh.M - 1)) fun z =>
  VF.bind fReadF fun y => VF.pure (pcFB (z, y))

theorem fCommit6B_eq : fCommit6B = fCommit6 := by
  funext sh
  simp only [fCommit6B, fCommit6, pcFB_eq]

end Lvm6.V
