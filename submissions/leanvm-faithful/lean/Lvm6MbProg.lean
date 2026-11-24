-- New for lvm6 Y1 (2026-11-22): the mini-bus at `E = GF(2^128)`: its programs, its three claims and the frozen
-- statement `MiniSpecL6` (docs/lvm6/design/MB-decision.md §6, docs/lvm6/stages/Y1-typed.md §2). Definitions only;
-- the proofs are in `Lvm6MbSample`, `Lvm6MbBus`, `Lvm6MbGkr`, `Lvm6MbFid`, `Lvm6MbLin`, `Lvm6MbMid`.
import LvmM3Mid
import LvmE2VSample
import LvmE2VWireAlg

/-!
# The mini-bus at `E2` (definitions and the frozen statement)

Season 1's mini-bus (`LvmM3Fid.lvmBusProg` at `E3`, roll #32's tableless ending `LvmS2GLLin.mbClaimsL`) moves to
`E2 = GF(2^128)` with a proof of work on every group (FORMAT6 §4):

* **`e2SampleN g n`** (the group rule): one nonce, then `n` draws; the proof of work `powOK g` on the first draw
  only. `n = 0` is the empty group (no nonce).
* **The GKR walk at `E2`** (`gkrStepG`, `gkrLayersG`, `verifyGkrGrandProductsG`): S1's `gkrStep` with every
  challenge ground: the combiner `λ` (`G(2)`), every round challenge (`G(3)`), the step's point `y` as one group
  (`G(2)`, at the last step `G(3)`).
* **`lvmBusProgG μ`**: `(α, β)` as one group of five draws (`G(16)`), the roots, the walk, the count root nonzero.
  S1's trailing zero scalar is dropped: every group opens with a nonce.
* **The three claims** (`mbClaimsG`): the bus result over `E2` (`busFinalG`, `busFinalV`'s twin) and, per side,
  one sum claim on `C_main` (`mbClaimL`'s twin); fixed columns enter through their multilinear extension
  (`mleFixG`), not through an executable evaluator.
* **`miniBusLProg6`**: the bus phase, then the three claims on the stack; **`MiniSpecL6`**: the frozen statement.
-/

set_option autoImplicit false

namespace Lvm6.Mb

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm.M3
open scoped ENNReal

/-! ## The group rule -/

/-- **A ground group of `n` draws** (FORMAT6 §4, `G(g)` then `D(n − 1)`): the nonce (one read), the first draw `c`
with `powOK g c`, then `n − 1` further draws; the values are lanes 0–1 of each answer. -/
def e2SampleN (g : ℕ) : ℕ → VerifierProgram (List E2)
  | 0 => pure []
  | n + 1 =>
    VerifierProgram.readScalar >>= fun _ ↦ VerifierProgram.sampleChallenge >>= fun c ↦
      VerifierProgram.require (LeanVM.Protocol.Verifier.powOK g c) >>= fun _ ↦
        VerifierProgram.sampleChallenges n >>= fun cs ↦ pure ((c :: cs).map e2OfE)

/-! ## Proof-of-work bits of the mini-bus (PARAM rows 27–31) -/

/-- `(α, β)`: `16` bits. The statement charges Theorem 5.1's `4·2^12` at depth 12; PARAM's row prices `2^15`
(conservative); both admit `g = 16`. -/
abbrev gAB : ℕ := 16
/-- The combiner `λ`: numerator 2 (three trees, degree 2). -/
abbrev gLam : ℕ := 2
/-- A GKR round: numerator 5 (leanVM's `eq × 4` lines; the proof needs 4). -/
abbrev gRd : ℕ := 3
/-- A step's point `y` (two draws, jointly degree 2): numerator 2. -/
abbrev gY : ℕ := 2
/-- The last step's `y`: numerator 4 (PARAM's upper bound). -/
abbrev gYl : ℕ := 3
/-- The mini-bus's depth: `2^12` leaves (season 1's `miniDepth`). -/
abbrev miniDepth : ℕ := 12

/-! ## Claims at `E2` -/

/-- **A claim at `E2` on a column of `2^μ` words**: a weight on points and a value. -/
abbrev ClaimE : Type := (List E2 → E2) × E2

/-- **What a claim says**: the weight's values on the cube, against the column's words, sum to the value. -/
def ClaimE.Holds (μ : ℕ) (c : ClaimE) (q : Column μ) : Prop :=
  ∑ x : Fin (2 ^ μ), c.1 (bitsF x.val μ) * algebraMap K E2 (q.values.getD x 0) = c.2

/-- `Placement::eq_above` at `E2`: the equality weight of the coordinates above the window. -/
def eqAboveG (p : LeanVM.Protocol.Verifier.Placement) (pt : List E2) : E2 :=
  eqEvalF (selPtF (p.index >>> p.variableCount) (pt.length - p.variableCount)) (pt.drop p.variableCount)

/-- A block claim at `E2`: a block of the stack, a weight on the block's own variables, a value. -/
structure BClaimG where
  /-- The block. -/
  block : LeanVM.Protocol.Verifier.Placement
  /-- The weight on the block's variables. -/
  weight : List E2 → E2
  /-- The value. -/
  value : E2

/-- A point claim on a block. -/
def BClaimG.point (block : LeanVM.Protocol.Verifier.Placement) (z : List E2) (v : E2) : BClaimG :=
  ⟨block, eqEvalF z, v⟩

/-- The claim on the whole commitment. -/
def BClaimG.onStack (c : BClaimG) : ClaimE :=
  (fun x ↦ eqAboveG c.block x * c.weight (x.take c.block.variableCount), c.value)

/-- A sum claim on a commitment of `ν` variables: `Σ_parts c·eq_above(blk)·eq(z, ·)`. -/
def sumClaimG (nu : ℕ) (parts : List (E2 × LeanVM.Protocol.Verifier.Placement × List E2)) (value : E2) :
    BClaimG :=
  ⟨⟨nu, 0⟩, fun x ↦ sumF (parts.map fun p ↦ p.1 * eqAboveG p.2.1 x * eqEvalF p.2.2 (x.take p.2.1.variableCount)),
    value⟩

/-! ## The GKR walk at `E2` -/

/-- The walk's state: the push, pull and count trees' values at `point`. -/
structure GkrStateG where
  /-- The three trees' values. -/
  values : List E2
  /-- Their point. -/
  point : List E2

/-- **One step of `step` levels at `E2`** (`gkrStep`'s twin, ground): `λ` (`G(gLam)`), the rounds in equality mode
over the point (`G(gRd)` each), three children of `2^step` values, the check, the point `y` as one group
(`G(gy)`), the children's extensions at `y`. -/
def gkrStepG (gy step : ℕ) (s : GkrStateG) : VerifierProgram GkrStateG :=
  e2Sample gLam >>= fun lam ↦
    sumcheckE2 gRd (polyEvalF s.values lam) (2 ^ step + 1) (s.point.map some) >>= fun rf ↦
      e2Reads (2 ^ step) >>= fun c0 ↦ e2Reads (2 ^ step) >>= fun c1 ↦ e2Reads (2 ^ step) >>= fun c2 ↦
        VerifierProgram.require (rf.2 = polyEvalF ([c0, c1, c2].map prodF) lam) >>= fun _ ↦
          e2SampleN gy step >>= fun y ↦ pure ⟨[c0, c1, c2].map (multilinearEvalF · y), y ++ rf.1⟩

/-- **The walk at `E2`** (`gkrLayers`'s twin): one level when the remaining depth is odd, two otherwise; the last
step's `y` at `gYl`. -/
def gkrLayersG : ℕ → GkrStateG → VerifierProgram GkrStateG
  | 0, s => pure s
  | 1, s => gkrStepG gYl 1 s
  | n + 2, s =>
    if n % 2 = 1 then gkrStepG gY 1 s >>= fun s' ↦ gkrLayersG (n + 1) s'
    else gkrStepG (if n = 0 then gYl else gY) 2 s >>= fun s' ↦ gkrLayersG n s'

/-- **`verify_gkr_grand_products` at `E2`**: the roots `shared`, `count`, the walk; the count root, the point, the
three values. -/
def verifyGkrGrandProductsG (μ : ℕ) : VerifierProgram (E2 × List E2 × List E2) :=
  e2Read >>= fun shared ↦ e2Read >>= fun count ↦
    gkrLayersG μ ⟨[shared, shared, count], []⟩ >>= fun s ↦ pure (count, s.point, s.values)

/-! ## The bus phase at `E2` -/

/-- What the bus phase read at `E2`. -/
structure LBusG where
  /-- The four `α`. -/
  alphas : List E2
  /-- `β`. -/
  beta : E2
  /-- The grand product's point. -/
  point : List E2
  /-- The three trees' values there. -/
  values : List E2

/-- **The bus phase at `E2`**: `(α, β)` (one group of five draws, `G(gAB)`), the walk at depth `μ`, the count root
nonzero. -/
def lvmBusProgG (μ : ℕ) : VerifierProgram LBusG :=
  e2SampleN gAB 5 >>= fun ab ↦ verifyGkrGrandProductsG μ >>= fun r ↦
    VerifierProgram.require (r.1 ≠ 0) >>= fun _ ↦ pure ⟨ab.take 4, ab.getD 4 0, r.2.1, r.2.2⟩

/-! ## The bus result at `E2` (`busFinalV`'s twin) -/

/-- `K` in `E2`. -/
def kG (a : Lvm.FK) : E2 := Lvm.FE2.toE2 (Lvm.FE2.ofK a)

/-- A form over `E2`: monomials (column indices) with coefficients. -/
structure FormG where
  /-- The monomials. -/
  terms : List (List ℕ × E2) := []
  deriving Inhabited

/-- `w·P` as a form. -/
def cpolyFormG (w : E2) (P : CPoly) : FormG := ⟨P.map fun m ↦ (m.2, w * kG m.1)⟩

/-- The sum of forms. -/
def formSumG (fs : List FormG) : FormG := ⟨fs.flatMap (·.terms)⟩

/-- The leaf form of a message `⟨sep, addr, cnt, val⟩` at unit weight: `β + Σ_i eq(α, i)·coord_i`. -/
def leafFormG (eqα : List E2) (β : E2) (k : Key) (cnt : CPoly) : FormG :=
  formSumG ([⟨[([], β + eqα.getD 0 0 * kG k.sep)]⟩, cpolyFormG (eqα.getD 1 0) k.addr,
    cpolyFormG (eqα.getD 2 0) cnt] ++ k.val.zipIdx.map fun (P, l) ↦ cpolyFormG (eqα.getD (3 + l) 0) P)

/-- A block of a bus side: its table, its log-height, its form at unit weight. -/
structure VBlockG where
  /-- The table. -/
  tab : ℕ
  /-- The log-height. -/
  κ : ℕ
  /-- The form. -/
  form : FormG

/-- The blocks of the three sides, in the protocol's order. -/
def sideBlocksG (tabs : List Tab) (eqα : List E2) (β : E2) : List (List VBlockG) :=
  let ts := tabs.zipIdx
  [ts.flatMap fun (t, j) ↦
      t.reads.map (fun r ↦ ⟨j, t.τ, leafFormG eqα β r.1 [(Lvm.FK.x, [r.2])]⟩) ++
        t.seeds.map (fun s ↦ ⟨j, t.τ, leafFormG eqα β s.1 (CPoly.const 1)⟩),
   ts.flatMap fun (t, j) ↦
      t.reads.map (fun r ↦ ⟨j, t.τ, leafFormG eqα β r.1 (CPoly.var r.2)⟩) ++
        t.seeds.map (fun s ↦ ⟨j, t.τ, leafFormG eqα β s.1 (CPoly.var s.2)⟩),
   ts.flatMap fun (t, j) ↦ t.counts.map fun c ↦ ⟨j, t.τ, ⟨[([c.val], 1)]⟩⟩]

/-- The blocks stacked largest first (stable), with their offsets. -/
def stackBlocksG (bs : List VBlockG) : List (VBlockG × ℕ) :=
  let sorted := bs.mergeSort fun a b ↦ decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (VBlockG × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ)) ([], 0)).1

/-- The sides' blocks with their weights at `ζ`. -/
def sidesG (tabs : List Tab) (alphas : List E2) (β : E2) (ζ : List E2) : List (List (VBlockG × E2)) :=
  (sideBlocksG tabs (eqKernelF alphas) β).map fun bs ↦
    (stackBlocksG bs).map fun (b, off) ↦ (b, eqAboveG ⟨b.κ, off⟩ ζ)

/-- Table `j`'s terms on a side: its blocks' weighted terms. -/
def bucketG (s : List (VBlockG × E2)) (j : ℕ) : List (List ℕ × E2) :=
  ((s.filter fun bw ↦ bw.1.tab == j).reverse).flatMap fun bw ↦ bw.1.form.terms.map fun t ↦ (t.1, bw.2 * t.2)

/-- The bus result at `E2`: the point, each table's three forms, each side's total. -/
structure BusResG where
  /-- The GKR point. -/
  point : List E2
  /-- Each table's form per side. -/
  forms : List (List FormG)
  /-- The three sides' totals. -/
  totals : List E2

/-- **The bus leaf decomposition at `E2`**: each side's total `v + 1 + Σ_b w_b`. -/
def busFinalG (tabs : List Tab) (alphas : List E2) (β : E2) (ζ values : List E2) : BusResG :=
  let sides := sidesG tabs alphas β ζ
  ⟨ζ, (List.range tabs.length).map (fun j ↦ sides.map fun s ↦ (⟨bucketG s j⟩ : FormG)),
    (List.range 3).map fun k ↦ values.getD k 0 + 1 + sumF ((sides.getD k []).map (·.2))⟩

/-- The bus result of what the bus phase read. -/
def busResG (tabs : List Tab) (b : LBusG) : BusResG := busFinalG tabs b.alphas b.beta b.point b.values

/-! ## The three claims (`mbClaimsL`'s twin) -/

/-- A coordinate polynomial is a constant or one column with a coefficient. -/
def cpolyLinB (P : CPoly) : Bool := P.all fun m ↦ decide (m.2.length ≤ 1)

/-- **The mini-bus is tableless** (roll #32's `mbLinB`): no constraint, every key coordinate and every count column a
constant or one column, every committed column on `C_main`. -/
def mbLinB6 (tabs : List Tab) : Bool :=
  tabs.all fun t ↦ t.cons.isEmpty &&
    (t.reads.map (·.1) ++ t.seeds.map (·.1)).all (fun k ↦ cpolyLinB k.addr && k.val.all cpolyLinB) &&
    t.cols.all fun c ↦ match c with
      | .com rec _ => !rec
      | .fix _ _ => true

/-- The columns side `s` (`0` push, `1` pull, `2` count) of table `t` names, in column order. -/
def sideColsG (t : Tab) (s : ℕ) : List ℕ :=
  let keyCols : List ℕ := (t.reads.map (·.1) ++ t.seeds.map (·.1)).flatMap fun k ↦
    (k.addr :: k.val).flatMap fun P ↦ P.flatMap (·.2)
  let named : List ℕ :=
    if s = 0 then keyCols ++ t.reads.map (·.2)
    else if s = 1 then keyCols ++ t.reads.map (·.2) ++ t.seeds.map (·.2)
    else t.counts.map (·.val)
  (List.range t.w).filter fun c ↦ named.contains c

/-- Column `c`'s coefficient in a form. -/
def coefG (f : FormG) (c : ℕ) : E2 := sumF ((f.terms.filter fun m ↦ m.1 == [c]).map (·.2))

/-- **A fixed column's extension at `E2`**: `Σ_{x < 2^τ} eq(pt, x)·f(x)`. -/
noncomputable def mleFixG (τ : ℕ) (f : ℕ → Lvm.FK) (pt : List E2) : E2 :=
  ∑ x ∈ Finset.range (2 ^ τ), eqAtF pt x * kG (f x)

/-- A form's constant on table `t` at `pt`: its constant terms and its fixed columns at their extensions. -/
noncomputable def constG (t : Tab) (f : FormG) (pt : List E2) : E2 :=
  sumF (f.terms.map fun m ↦ match m.1 with
    | [] => m.2
    | [c] => match t.cols[c]? with
      | some (ColSrc.fix fc _) => m.2 * mleFixG t.τ fc pt
      | _ => 0
    | _ => 0)

/-- Table `j`'s form on side `s`. -/
def formG (r : BusResG) (j s : ℕ) : FormG := (r.forms.getD j []).getD s default

/-- **Side `s`'s parts**: one per committed column the side names. -/
def mbPartsG (tabs : List Tab) (r : BusResG) (s : ℕ) :
    List (E2 × LeanVM.Protocol.Verifier.Placement × List E2) :=
  tabs.zipIdx.flatMap fun (tj : Tab × ℕ) ↦ (sideColsG tj.1 s).filterMap fun c ↦ match tj.1.cols[c]? with
    | some (ColSrc.com _ off) => some (coefG (formG r tj.2 s) c, ⟨tj.1.τ, off⟩, r.point.take tj.1.τ)
    | _ => none

/-- **Side `s`'s value**: the side's total plus every table's constant. -/
noncomputable def mbValueG (tabs : List Tab) (r : BusResG) (s : ℕ) : E2 :=
  r.totals.getD s 0 + sumF (tabs.zipIdx.map fun (t, j) ↦ constG t (formG r j s) (r.point.take t.τ))

/-- **The three claims** (push, pull, count) on `C_main` (`ν` variables) of what the bus phase read. -/
noncomputable def mbClaimsG (nu : ℕ) (tabs : List Tab) (b : LBusG) : List BClaimG :=
  (List.range 3).map fun s ↦ sumClaimG nu (mbPartsG tabs (busResG tabs b) s) (mbValueG tabs (busResG tabs b) s)

/-! ## The mini-bus phase and its statement -/

/-- **The mini-bus at `E2`**: the bus phase at depth `μ`, then the three claims on `C_main`. -/
noncomputable def miniBusLProg6 (L : Lay) (tabs : List Tab) (μ : ℕ) : VerifierProgram (List ClaimE) :=
  lvmBusProgG μ >>= fun b ↦ pure ((mbClaimsG L.nuMain tabs b).map (·.onStack))

/-- The stack of a candidate pair: `C_main`, then `C_rec`. -/
def stackOf (L : Lay) (qm : Column L.nuMain) (qr : Column L.nuRec) : Column L.μ :=
  ⟨Vector.ofFn fun x ↦ if h : x.val < 2 ^ L.nuMain then qm.values[x.val] else
    if h' : x.val - 2 ^ L.nuMain < 2 ^ L.nuRec then qr.values[x.val - 2 ^ L.nuMain] else 0⟩

/-- **The frozen statement of the mini-bus at `E2`** (Y1-typed.md §2.2; MB-decision §6's `miniSpecL6`), on a fixed
candidate set `S` with a carried predicate `aRm`: from doom of the mini-bus relation (`M3Holds`) to doom of the
three claims on `C_main`; lead `0` (the first event is a nonce); each group's error as the hypotheses state. -/
noncomputable def MiniSpecL6 (L : Lay) (tabs : List Tab) (hτL : ∀ t ∈ tabs, t.τ ≤ L.μ)
    (S : Set (Column L.nuMain × Column L.nuRec)) (aRm : Column L.nuMain × Column L.nuRec → Prop)
    (εmax T : ℝ≥0∞) : Type :=
  Spec (miniBusLProg6 L tabs miniDepth)
    (fun h ↦ (∃ W, firstWord h = some W) ∧
      Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L tabs hτL) () (stackOf L q.1 q.2) ∧ aRm q) h)
    (fun cl h ↦ cl.length = 3 ∧ Doomed (fun _ ↦ S) (fun q ↦ (∀ c ∈ cl, ClaimE.Holds L.nuMain c q.1) ∧ aRm q) h)
    εmax 0 T

/-- **`miniSpecL6`'s statement** (frozen; Y1-typed.md §2.2): a specification exists under the tables' static
conditions (`AllSc`, `LayOk`, `KeysOk`, `FixOk`, tableless), depth `12`, and every group's error with the follower's
lead `T` within `εmax < 1`. -/
def MiniSpecL6Stmt : Prop :=
  ∀ (L : Lay) (tabs : List Tab) (hτL : ∀ t ∈ tabs, t.τ ≤ L.μ) (S : Set (Column L.nuMain × Column L.nuRec))
    (aRm : Column L.nuMain × Column L.nuRec → Prop) {L₀ : ℕ} {εmax T : ℝ≥0∞},
    S.Finite → S.ncard ≤ L₀ → AllSc tabs → LayOk L tabs → KeysOk tabs → FixOk tabs → mbLinB6 tabs = true →
    (inst L tabs hτL).μBus = miniDepth → εmax < 1 →
    (L₀ : ℝ≥0∞) * errG gAB (4 * 2 ^ miniDepth) + T ≤ εmax → (L₀ : ℝ≥0∞) * errG gLam 2 + T ≤ εmax →
    (L₀ : ℝ≥0∞) * errG gRd 5 + T ≤ εmax → (L₀ : ℝ≥0∞) * errG gY 2 + T ≤ εmax →
    (L₀ : ℝ≥0∞) * errG gYl 4 + T ≤ εmax →
    Nonempty (MiniSpecL6 L tabs hτL S aRm εmax T)

end Lvm6.Mb
