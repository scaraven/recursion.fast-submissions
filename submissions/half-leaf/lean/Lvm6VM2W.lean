-- New for lvm6 (MUL2): the claims the opening evaluates (ring, mini-bus) and the opening's own products (the fold of
-- the rows, the glue's column factors) on MUL's `m2B`. Each twin is its original with the hot products as `m2B`.
import Lvm6VM2K
import Lvm6VS1Wh
import Lvm6VS1Mb

/-!
# MUL2: the opening and its claims on `m2B`

The opening (`fWhirH`) evaluates the batched claim `φ` at each point of its last sumcheck, through the glue of every
level: each claim's closure runs several times a check. The ring claims' closure also rebuilt the ring coefficients
(`ringCoefficients f g`, independent of the point) on every call; `ringOfFB` builds them once per claim.

* ring: `frobenius8B`, `ringPsiB`, `ringTargetB`, `ringCoefficientsB`, `ringWeightB`, `ringOfFB`,
  `claimOf6FB`, **`fRingPhase6B`** (`= fRingPhase6`);
* mini-bus: `eqEvalFB`, `eqAboveFB`, `mbClaimFB`, `sidesFB`, `bucketFB`, `busFinalFB`, `mbClaimsFB`, `fMiniBus6B`,
  `fTypedProgEXB` (unfolded in `fTypedPhase6XB_eq`, as `fTypedProgEXH`), **`fTypedPhase6XB`** (`= fTypedPhase6XH`);
* opening: `m2Bc` (`m2B` as a call, inside closures), `foldRowFB`, `valAtFB`, `valsMidFB`, `colGoB`, `glueFB`, `fMidB`,
  **`fWhirB`** (`= fWhirH`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.Ring

/-! ## The ring claims -/

/-- `frobenius8` on `m2B`. -/
def frobenius8B (value : FE2) (p : ℕ) : FE2 :=
  (List.range (ringMapWidth * p)).foldl (fun v _ ↦ m2B v v) value

theorem frobenius8B_eq : frobenius8B = frobenius8 := by
  funext value p
  simp only [frobenius8B, frobenius8, m2B_mul]

/-- `ringPsi` on `m2B`. -/
def ringPsiB (value : FE2) (g : List FE2) : FE2 :=
  (g.foldl (fun (acc : FE2 × FE2) gb ↦ (acc.1 + m2B gb acc.2, m2B acc.2 acc.2)) (0, value)).1

theorem ringPsiB_eq : ringPsiB = ringPsi := by
  funext value g
  simp only [ringPsiB, ringPsi, m2B_mul]

/-- `ringTarget` on the twins. -/
def ringTargetB (x : FE2) (s f g : List FE2) : FE2 :=
  let images := s.map (ringPsiB · g)
  ((List.range ringMapWidth).reverse.foldl (fun (acc : FE2 × FE2) p ↦
    let z := frobenius8B acc.2 1
    (acc.1 + m2B (f.getD p 0) (frobenius8B (polyEvalFB images z) p), z)) (0, x)).1

theorem ringTargetB_eq : ringTargetB = ringTarget := by
  funext x s f g
  simp only [ringTargetB, ringTarget, ringPsiB_eq, frobenius8B_eq, polyEvalFB_eq, m2B_mul]

/-- `ringCoefficients` on the twins. -/
def ringCoefficientsB (f g : List FE2) : List FE2 :=
  (f.foldl (fun (acc : List FE2 × List FE2) fp ↦
    (acc.1 ++ acc.2.map (m2B fp ·), acc.2.map (frobenius8B · 1))) ([], g)).1

theorem ringCoefficientsB_eq : ringCoefficientsB = Lvm6.Ring.ringCoefficients := by
  funext f g
  simp only [ringCoefficientsB, Lvm6.Ring.ringCoefficients, frobenius8B_eq, m2B_mul]

/-- `ringWeight` on `m2B`. -/
def ringWeightB (r rPrime coefficients : List FE2) : FE2 :=
  (coefficients.foldl (fun (acc : FE2 × List FE2) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (p : FE2 × FE2) ↦ m2B product (1 + p.1 + p.2)) c
    (acc.1 + product, acc.2.map fun value ↦ m2B value value)) (0, r)).1

theorem ringWeightB_eq : ringWeightB = Lvm6.Ring.ringWeight := by
  funext r rPrime coefficients
  simp only [ringWeightB, Lvm6.Ring.ringWeight, m2B_mul]

/-- `ringOfF` on the twins, the ring coefficients built once per claim (they do not depend on the point). -/
def ringOfFB (c : SliceF) (f g : List FE2) : FClaim :=
  let cf := ringCoefficientsB f g
  ⟨fun x => m2B (eqEvalF [] (x.drop c.pt.length)) (ringWeightB c.pt (x.take c.pt.length) cf),
    ringTargetB (FE2.ofK FK.x) (List.ofFn fun z : Fin 64 => c.s.getD z 0) f g⟩

theorem ringOfFB_eq : ringOfFB = ringOfF := by
  funext c f g
  simp only [ringOfFB, ringOfF, ringCoefficientsB_eq, ringWeightB_eq, ringTargetB_eq, m2B_mul]

/-- `claimOf6F` over `ringOfFB`. -/
def claimOf6FB (sl : List SliceF) (st : List FClaim)
    (o : ((List FE2 × List FE2) × (List FE2 × List FE2)) × FE2) : FClaim :=
  batchF o.2 (placeRingF (ringOfFB (sl.getD 0 ⟨[], []⟩) o.1.1.1 o.1.1.2)
    (ringOfFB (sl.getD 1 ⟨[], []⟩) o.1.2.1 o.1.2.2) st)

theorem claimOf6FB_eq : claimOf6FB = claimOf6F := by
  funext sl st o
  simp only [claimOf6FB, claimOf6F, ringOfFB_eq]

/-- **`fRingPhase6` over `claimOf6FB`.** -/
def fRingPhase6B (sh : Lvm6.Shape) (sl : List SliceF) (st : List FClaim) : VF FClaim :=
  VF.guard (decide (Lvm6.Params.admits ((sh.J₀ + 3) * sh.L₀) sh.gRing = true ∧ sh.gRing ≤ 64 ∧
      (∀ c ∈ sl, c.pt.length = sh.M) ∧ sl.length = 2)) <|
  VF.bind (VF.bind fSample fun _ => VF.pure ()) fun _ =>
  VF.bind fRead fun _ =>
  VF.bind (fSamples 33) fun as =>
  VF.guard (powHead sh.gRing as) (VF.pure (claimOf6FB sl st (ringOut6F as)))

theorem fRingPhase6B_eq : fRingPhase6B = fRingPhase6 := by
  funext sh sl st
  simp only [fRingPhase6B, fRingPhase6, claimOf6FB_eq]

/-! ## The mini-bus claims -/

section MB

open Lvm.M3 Lvm6.Mb
open Lvm6.Ty (TInst6 TyInst6)

/-- `eqEvalF` on `m2B`. -/
def eqEvalFB (left right : List FE2) : FE2 :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (fun a b ↦ m2B a b) 1

theorem eqEvalFB_eq : eqEvalFB = eqEvalF := by
  funext left right
  simp only [eqEvalFB, eqEvalF, m2B_mul]

/-- `eqAboveFH` over `eqAtFB`. -/
def eqAboveFB (p : Plc) (pt : List FE2) : FE2 := eqAtFB (pt.drop p.variableCount) (p.index >>> p.variableCount)

theorem eqAboveFB_eq : eqAboveFB = eqAboveFH := by
  funext p pt
  simp only [eqAboveFB, eqAboveFH, eqAtFB_eq]

/-- `mbClaimFH` on the twins. -/
def mbClaimFB (nu : ℕ) (parts : List (FE2 × Plc × List FE2)) (v : FE2) : FClaim :=
  ⟨fun x =>
    let xt := x.take nu
    m2B (eqAboveFB ⟨nu, 0⟩ x) (parts.foldl (fun acc p =>
      acc + m2B (m2B p.1 (eqAboveFB p.2.1 xt)) (eqEvalFB p.2.2 (xt.take p.2.1.variableCount))) 0), v⟩

theorem mbClaimFB_eq : mbClaimFB = mbClaimFH := by
  funext nu parts v
  simp only [mbClaimFB, mbClaimFH, eqAboveFB_eq, eqEvalFB_eq, m2B_mul]

/-- `sidesF` over `eqAboveFB`. -/
def sidesFB (tabs : List Tab) (alphas : List FE2) (β : FE2) (ζ : List FE2) : List (List (VBlockF × FE2)) :=
  (sideBlocksF tabs (eqKernelF alphas) β).map fun bs =>
    (stackBlocksF bs).map fun (b, off) => (b, eqAboveFB ⟨b.κ, off⟩ ζ)

theorem sidesFB_eq : sidesFB = sidesF := by
  funext tabs alphas β ζ
  simp only [sidesFB, sidesF, eqAboveFB_eq, eqAboveFH_eq]

/-- `bucketF` on `m2B`. -/
def bucketFB (s : List (VBlockF × FE2)) (j : ℕ) : FormF :=
  ((s.filter fun bw => bw.1.tab == j).reverse).flatMap fun bw => bw.1.form.map fun t => (t.1, m2B bw.2 t.2)

theorem bucketFB_eq : bucketFB = bucketF := by
  funext s j
  simp only [bucketFB, bucketF, m2B_mul]

/-- `busFinalF` over `sidesFB`, `bucketFB`. -/
def busFinalFB (tabs : List Tab) (alphas : List FE2) (β : FE2) (ζ values : List FE2) : BusResF :=
  let sides := sidesFB tabs alphas β ζ
  ⟨ζ, (List.range tabs.length).map (fun j => sides.map fun s => bucketFB s j),
    (List.range 3).map fun k => values.getD k 0 + 1 + sumF ((sides.getD k []).map (·.2))⟩

theorem busFinalFB_eq : busFinalFB = busFinalF := by
  funext tabs alphas β ζ values
  simp only [busFinalFB, busFinalF, sidesFB_eq, bucketFB_eq]

/-- `mbClaimsFH` over `busFinalFB`, `mbClaimFB`. -/
def mbClaimsFB (nu : ℕ) (tabs : List Tab) (b : LBusF) : List FClaim :=
  let r := busFinalFB tabs b.alphas b.beta b.point b.values
  let pre := mbPre tabs r
  (List.range 3).map fun s => mbClaimFB nu (mbPartsF tabs r s) (mbValueFH r s pre)

theorem mbClaimsFB_eq : mbClaimsFB = mbClaimsFH := by
  funext nu tabs b
  simp only [mbClaimsFB, mbClaimsFH, mbClaimFB_eq, busFinalFB_eq]

/-- `fMiniBus6H` over `mbClaimsFB`. -/
def fMiniBus6B (L : Lay) (tabs : List Tab) (μ : ℕ) : VF (List FClaim) :=
  VF.bind (fLvmBus μ) fun b => VF.pure (mbClaimsFB L.nuMain tabs b)

theorem fMiniBus6B_eq : fMiniBus6B = fMiniBus6H := by
  funext L tabs μ
  simp only [fMiniBus6B, fMiniBus6H, mbClaimsFB_eq]

/-- `fTypedProgEXH` over `fMiniBus6B`. -/
def fTypedProgEXB (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (tab : List FE2 → FE2) (accP : List FE2)
    (accY : FE2) : VF (List FClaim × List FClaim) :=
  VF.bind fZero fun z => VF.bind (fWire Ti pw z.2) fun w => VF.bind (fRelay Ti w.1 (w.2.2.getD 1 0)) fun r =>
  VF.bind (fAcc tab accY accP (z.1 ++ w.1) w.2.1) fun _ =>
  VF.bind (fMiniBus6B L Ti.mbT Lvm6.Mb.miniDepth) fun cl => VF.pure (typedClaimsFX Ti w.1 w.2.2 r.1 r.2 cl)

/-- **`fTypedPhase6XH` over `fTypedProgEXB`.** -/
def fTypedPhase6XB (sh : Lvm6.Shape) (i : TyInst6) (tab : List FE2 → FE2) : VF (List FClaim) :=
  if sh.M = Lvm6.Ty.L6.nuMain then
    VF.bind (fTypedProgEXB i.Ti Lvm6.Ty.L6 i.pw tab (i.acc.1.map FE2.ofE2) (FE2.ofE2 i.acc.2)) fun out =>
      VF.pure (out.1.map recClaimF ++ out.2)
  else fun _ _ => none

theorem fTypedPhase6XB_eq : fTypedPhase6XB = fTypedPhase6XH := by
  funext sh i tab
  simp only [fTypedPhase6XB, fTypedPhase6XH, fTypedProgEXB, fTypedProgEXH, fMiniBus6B_eq]

end MB

/-! ## The opening -/

/-- `m2B` as an out-of-line call, for closures: an inlined `m2B c ·` under a returned closure makes the compiler
hoist `c`'s masks and reversals out of it and capture them as twenty boxed words. `m2Bc` stays a call because its
body is the inlined `m2B` (too large for the compiler to inline back). Closures that are applied in place (the maps
and folds of `eqKernelAFB`, `laneWAB`, `bucketFB`, …) keep the inlined `m2B`: there the hoisting is a gain. -/
def m2Bc (a b : FE2) : FE2 := m2B a b

theorem m2Bc_mul (a b : FE2) : m2Bc a b = a * b := m2B_mul a b

/-- `foldRowF` on `m2B` (`m2Bc` inside the closures). -/
def foldRowFB (x : FE2) : ℕ → List RndF → (ℕ → FE2) → (ℕ → FE2)
  | 0, _, L => L
  | j + 1, rs, L =>
    let r := rs.headD default
    let c := r.α + m2B r.β x
    foldRowFB x j rs.tail fun u => L (2 * u + 1) + m2Bc c (L (2 * u))

theorem foldRowFB_eq (x : FE2) : ∀ (j : ℕ) (rs : List RndF) (L : ℕ → FE2), foldRowFB x j rs L = foldRowF x j rs L
  | 0, _, _ => rfl
  | j + 1, rs, L => by
    rw [foldRowFB, foldRowF, foldRowFB_eq x j]
    simp only [m2B_mul, m2Bc_mul]

/-- `valAtFH` over `foldRowFB`. -/
def valAtFB (κ ℓ : ℕ) (rs : List RndF) (hi : List FE2) (p : ℕ) (lane : ℕ → FE2) : FE2 :=
  let a := kOfNat p
  foldRowFB (FE2.ofK a) ℓ rs lane 0 - highEvalF κ ℓ hi (nwFH a)

theorem valAtFB_eq : valAtFB = valAtFH := by
  funext κ ℓ rs hi p lane
  simp only [valAtFB, valAtFH, foldRowFB_eq]

/-- `valsMidFH` over `valAtFB`. -/
def valsMidFB (z : Bool) (κ ℓ h c t : ℕ) (rs : List RndF) (π : ByteArray) (hi qv : List FE2) (r : RowsF) :
    List FE2 :=
  List.ofFn fun k : Fin t => valAtFB κ ℓ rs hi (posNF h c qv k) (laneF z π r r.os[(k : ℕ)]?)

theorem valsMidFB_eq : valsMidFB = valsMidFH := by
  funext z κ ℓ h c t rs π hi qv r
  simp only [valsMidFB, valsMidFH, valAtFB_eq]

/-- `colGo` on `m2B`. -/
def colGoB : ℕ → List FK → List FE2 → FE2
  | 0, _, _ => 1
  | n + 1, W, y => m2B ((1 - y.headD 0) + FE2.mulK (y.headD 0) (W.headD 0)) (colGoB n W.tail y.tail)

theorem colGoB_eq : ∀ (n : ℕ) (W : List FK) (y : List FE2), colGoB n W y = colGo n W y
  | 0, _, _ => rfl
  | n + 1, W, y => by rw [colGoB, colGo, colGoB_eq n W.tail y.tail, m2B_mul]

/-- `glueFH` over `colGoB`. -/
def glueFB (ko t : ℕ) (φ : List FE2 → FE2) (zv : List FE2) (lam : FE2) (pk : ℕ → ℕ) (y : List FE2) : FE2 :=
  φ y + lam * eqLF (ko + 1) zv y + (psum lam (fun k => colGoB (ko + 1) (nwFH (kOfNat (pk k))) y) t).1

theorem glueFB_eq : glueFB = glueFH := by
  funext ko t φ zv lam pk y
  simp only [glueFB, glueFH, colGoB_eq]

/-- `fMidH` over `valsMidFB`, `glueFB`. -/
def fMidB (i ko ℓ h h' kq t c gQ : ℕ) (z : Bool) (frest : (List FE2 → FE2) → FE2 → VF Bool)
    (φ : List FE2 → FE2) (σ : FE2) : VF Bool :=
  VF.bind (fRounds 10 ℓ) fun rs =>
  VF.bind (fTail ℓ h' 32 i 18 ko gQ kq (posListF h c t) (valsMidFB z (ko + 1) ℓ h c t rs)) fun o =>
  frest (glueFB ko t (fun y => φ (alphasF ℓ rs ++ y)) o.zv (o.qv.getD (kq + 1) 0) (posNF h c o.qv))
    (gluedCF (foldsCF ℓ rs σ) o.y (o.qv.getD (kq + 1) 0) t o.c)

theorem fMidB_eq : fMidB = fMidH := by
  funext i ko ℓ h h' kq t c gQ z frest φ σ
  simp only [fMidB, fMidH, valsMidFB_eq, glueFB_eq]

/-- **`fWhirH` over `fMidB`.** -/
def fWhirB (f : List FE2 → FE2) (v : FE2) : VF Bool :=
  fMidB 0 17 6 20 19 18 110 6 19 true
    (fMidB 1 13 4 19 18 7 45 6 17 false
      (fMidB 2 9 4 18 17 3 28 7 18 false (fMidB 3 5 4 17 16 2 21 7 17 false fFin)))
    (fun y => f ((padF y).drop 6 ++ (padF y).take 6)) v

theorem fWhirB_eq : fWhirB = fWhirH := by
  funext f v
  simp only [fWhirB, fWhirH, fMidB_eq]

end Lvm6.V
