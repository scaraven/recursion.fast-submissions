-- New for lvm2 (roll 8 = B1, B1-V; B-DES §1.2, B1-G0 "Decisions for the commitment"): V_S's native typed
-- backend. The phases of `LvmTypedSpec.typedProg` read for read over `FE` (zerocheck, wiring, the `S_flat`
-- relayout, A23 at `Φ_Q`, the mini-bus), their claims with closed-form weights, the two shapes at physical
-- ν = 23 (the small one: logical ν = 22 on the even words, `LvmShape`'s single zero coordinate), and the
-- decision `decideFT`. L-C proves the refinement (`LvmVEq*`); nothing here is trusted by the certificate.
import LvmDecide
import LvmTypedLayout
import LvmDecideM3Real
import LvmKeccakSym

/-!
# V_S's typed backend (native)

**The instance** `TNat`: the word space's regions with their targets (`NReg`: a committed, `KS` or `σ′` region
is an aligned run of commitment words, the `S_flat` region the stream positions, the `PUB` region the header
lanes), the native `Φ_Q` (B1-K's `PhiQC`, **QLT's constants included**: an operand naming a QLT cell is an entry
on the word `1`, B-DES §1.3, B1-Q's decision), the mini-bus's tables. `TNat.okB` is the decidable shape check the
closed forms below rely on, and the region shape B1-Q's circuit assumes (`LvmQTyped`, assumptions 1–3, 8).

**Closed forms** (B1-V's V-LEV pass on the typed phases; each is the corresponding `LvmTypedSpec` sum, region
by region; equality lemmas are L-C's, `tool/TVCheck.lean` checks them against the brute-force sums):
* `affW`: `regClaim`'s weight, `Σ_reg eq(r_hi, base_hi)·eq(r_lo, X_lo)·eq(X_hi, dst_hi)`: `O(ν)` per region;
* `relayKernF`: `relayKern` by a long-division automaton over the position's bits, high to low, with the
  remainder (`< 17`, the stream lane) as state: `19·17·2` products for any `S_flat` region (the brute-force
  sum is `2^19` terms), plus a two-state comparator for the positions past the stream (`sflatWord`'s identity
  part, B1-Q's convention);
* `virtEF`: `virtE`, the `PUB` region by its multilinear extension at `r_y`, the `1` region by its `eq` weight
  alone (`virtE`'s `QLT` term is `0`: `okB` admits no `QLT` region).

**The phases** (`typedProg`'s order, B1-P's prover follows `LvmTypedVSched.phasesT`): `dZeroT`, `dWiringT`,
`dRelayT`, `dAccT` (A23 at `Φ_Q`: the folded claim is checked by `decideFT`, as `decideF` does), `dMiniT`
(today's bus and table phase at the record's `busDepth`, then the fixed columns natively, `tableCheckR`).

**The decision** `decideProgT`: commit, the typed phases, tape, wire, `KS`, `KS` link, the openings
(`dOpenT`: `C_main`'s claims through `onStackZBN` when `smallT`). `decideFT = decideCoreT ∧ Φ_Q(acc_out)`.
-/

set_option autoImplicit false

namespace Lvm.TypedV

open Lvm DM
open Lvm.Typed (YSrc xVars yVars)

/-! ## The native instance -/

/-- A region of the word space with its target: `2^log` words from `base` (aligned); word `base + i` reads
`dst + i` of its source (a `C_main` word for `com` and `ks`, a `C_rec` word for `sigma`, a stream position for
`sflat`, a header lane for `pub`; unused for `one`; `okB` admits no `qlt` region). -/
structure NReg where
  /-- The first word. -/
  base : Nat
  /-- `log₂` of the size. -/
  log : Nat
  /-- The source. -/
  src : YSrc
  /-- The target of the first word. -/
  dst : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **The native typed instance** (INT fills it at the refreeze from B1-K's layout and B1-Q's tables). -/
structure TNat where
  /-- The word space's regions (sorted by `base`, disjoint: B1-K's `yregs` with targets). -/
  regs : List NReg
  /-- `Φ_Q` natively (B1-K's `PhiQC cache`), at `κ ‖ r_x ‖ r_y`. -/
  phi : List FE → FE
  /-- The mini-bus's tables (B1-Q's `mbT`). -/
  mbT : List Lvm.M3.Tab

/-- The stream's lanes (`C_rec`'s stream columns): position `p` is lane `p mod 17`, row `p div 17`. -/
abbrev sLanes : Nat := recStreamCols

/-- The relayout's rounds: `C_rec`'s variables, 14 row bits and 5 column bits (`LvmTypedSpec.relayRounds`). -/
abbrev relayRoundsN : Nat := 19

/-- A stream position's bits: `17 · 2^14 ≤ 2^19`. -/
abbrev posBits : Nat := 19

/-- `C_rec`'s row bits (`P20.recRowsLog`). -/
abbrev recRowBits : Nat := 14

/-- `Φ_Q`'s variables: 2 selector bits, `x`, `y`. -/
abbrev phiVarsN : Nat := 2 + xVars + yVars

/-- The stream's positions: `17·2^14`. -/
abbrev sPos : Nat := sLanes * 2 ^ recRowBits

/-- The `C_rec` word of a stream position: column `p mod 17`, row `p div 17`; a position past the stream
(`p ≥ 17·2^14`) is `C_rec`'s word `p` (B1-Q's convention, `LvmQTyped`: an `S_flat` region of `2^19` words is a
permutation of `C_rec`'s words). -/
def sflatWord (p : Nat) : Nat := if p < sPos then p % sLanes * 2 ^ recRowBits + p / sLanes else p

/-- The regions of a source. -/
def TNat.regsOf (N : TNat) (s : YSrc) : List NReg := N.regs.filter (·.src == s)

/-- **The shape check** the closed forms rely on: every region aligned (`base`, and the target of `com`, `ks`,
`sigma` and `sflat` regions) and below `2^21`; `com` and `ks` regions inside `C_main` and above `D`'s
`2^22` words (so their claims have no mass on `D`'s tail in the small shape, as roll 7's `colsHiB`) and below
the small shape's room (`7·2^20`); `sigma` inside `C_rec`; `sflat` within the stream's `17·2^14` positions;
no `QLT` region (B-DES §1.3, B1-Q's `LvmQTyped` assumption 4: `QLT`'s cells are constants of `Φ_Q`); exactly one
`S_flat` region (`2^19` words, positions from 0), one `PUB` region (`2^10` header lanes from lane 0, zero past
them) and one `1` word (B1-Q's assumptions 1, 3, 8); the regions sorted and disjoint. -/
def TNat.okB (N : TNat) (nuMain nuRec : Nat) : Bool :=
  N.regs.all (fun r => r.base % 2 ^ r.log == 0 && decide (r.base + 2 ^ r.log ≤ 2 ^ yVars) &&
    match r.src with
    | .com | .ks => r.dst % 2 ^ r.log == 0 && decide (2 ^ 22 ≤ r.dst) &&
        decide (r.dst + 2 ^ r.log ≤ min (2 ^ nuMain) (7 * 2 ^ 20))
    | .sigma => r.dst % 2 ^ r.log == 0 && decide (r.dst + 2 ^ r.log ≤ 2 ^ nuRec)
    | .sflat => r.dst % 2 ^ r.log == 0 && decide (r.dst + 2 ^ r.log ≤ 2 ^ posBits)
    | .pub => r.log == 10 && r.dst == 0
    | .one => r.log == 0
    | .qlt => false) &&
  (N.regsOf .sflat).length == 1 && (N.regsOf .sflat).all (fun r => r.log == posBits && r.dst == 0) &&
  (N.regsOf .pub).length == 1 && (N.regsOf .one).length == 1 &&
  (N.regs.zip N.regs.tail).all fun (a, b) => decide (a.base + 2 ^ a.log ≤ b.base)

/-! ## Closed forms (V-LEV) -/

/-- `eq(a, b)` on one coordinate. -/
@[inline] def eq1 (a : FE) (b : Bool) : FE := if b then a else 1 + a

/-- A region's `eq` weight above its own bits: `eq(r.drop log, base >>> log)`. -/
def hiW (r : List FE) (log base : Nat) : FE := eqAtF (r.drop log) (base >>> log)

/-- **A region claim's weight** (`regClaim`): `X ↦ Σ_reg eq(r, base)_hi · eq(r_lo, X_lo) · eq(X_hi, dst_hi)`
over the regions of `s`, each term's `r`-side factors computed once. -/
def affW (N : TNat) (s : YSrc) (r : List FE) : List FE → FE :=
  let terms := (N.regsOf s).map fun g => (hiW r g.log g.base, r.take g.log, g.log, g.dst >>> g.log)
  fun X => terms.foldl (fun acc t => acc + t.1 * eqEval t.2.1 (X.take t.2.2.1) * eqAtF (X.drop t.2.2.1) t.2.2.2) 0

/-- **The long-division automaton**: `Σ_{i < 2^log, p0 + i < 17·2^14} eq(ρ, i) · eq(rlo, (p0 + i) / 17) ·
eq(rhi, (p0 + i) mod 17)` for `p0` aligned to `2^log` and `p0 + 2^log ≤ 2^19`. The position's `19` bits are read
high to low; the state is the remainder (`< 17`); each bit appends one quotient bit (`q_k`, paired with `rlo_k`;
a quotient bit at `k ≥ 14` is the indicator of `p ≥ 17·2^14` and weighs `0`); a bit below `log` is free and
weighs `eq(ρ_k, ·)`, one above is `p0`'s. -/
def divKern (p0 log : Nat) (ρ rlo rhi : List FE) : FE :=
  let ρa := ρ.toArray
  let ra := rlo.toArray
  let step (V : Array FE) (k : Nat) : Array FE :=
    let free := decide (k < log)
    let bits : List Bool := if free then [false, true] else [p0.testBit k]
    let fac (b q : Bool) : FE :=
      (if free then eq1 (ρa.getD k 0) b else 1) * (if k < recRowBits then eq1 (ra.getD k 0) q else if q then 0 else 1)
    let f00 := fac false false
    let f01 := fac false true
    let f10 := fac true false
    let f11 := fac true true
    (List.range sLanes).foldl (fun W rem =>
      let v := V.getD rem 0
      bits.foldl (fun W b =>
        let t := 2 * rem + (if b then 1 else 0)
        let q := decide (sLanes ≤ t)
        let f := if b then (if q then f11 else f10) else (if q then f01 else f00)
        W.modify (if q then t - sLanes else t) (· + v * f)) W) (Array.replicate sLanes 0)
  let V := (List.range posBits).reverse.foldl step ((Array.replicate sLanes (0 : FE)).set! 0 1)
  (List.range sLanes).foldl (fun acc rem => acc + V.getD rem 0 * eqAtF rhi rem) 0

/-- `Σ_{i < 2^log, i ≥ c} eq(ρ, i)·eq(r, i)`, the bits high to low with two states (equal so far, above). -/
def geKern (c log : Nat) (ρ r : List FE) : FE :=
  let ρa := ρ.toArray
  let ra := r.toArray
  let t (k : Nat) (b : Bool) : FE := eq1 (ρa.getD k 0) b * eq1 (ra.getD k 0) b
  let st := (List.range log).reverse.foldl (fun (st : FE × FE) k =>
    let full := t k false + t k true
    if c.testBit k then (st.1 * t k true, st.2 * full) else (st.1 * t k false, st.2 * full + st.1 * t k true))
    ((1 : FE), (0 : FE))
  st.1 + st.2

/-- **The relayout's kernel** (`relayKern`) at `(r_y, r)`: per `S_flat` region, its `eq` weight above its bits
times the automaton (positions in the stream) plus the identity part (positions past it, `C_rec`'s word `p`). -/
def relayKernF (N : TNat) (ry r : List FE) : FE :=
  (N.regsOf .sflat).foldl (fun acc g =>
    let ρ := ry.take g.log
    let idp : FE := if g.dst + 2 ^ g.log ≤ sPos then 0
      else eqAtF (r.drop g.log) (g.dst >>> g.log) * geKern (sPos - min sPos g.dst) g.log ρ (r.take g.log)
    acc + hiW ry g.log g.base * (divKern g.dst g.log ρ (r.take recRowBits) (r.drop recRowBits) + idp)) 0

/-- `Σ_{i < 2^log} eq(pt, i) · v(i)` (the multilinear extension of `K` values at an `E` point). -/
def mleK (log : Nat) (v : Nat → FK) (pt : List FE) : FE :=
  let k := eqKernelA (pt.take log)
  (List.range (2 ^ log)).foldl (fun acc i => acc + FE.smulBase (v i) (k.getD i 0)) 0

/-- **The natively computed part of `z̃(r_y)`** (`virtE`): the `PUB` region (header lanes from `dst`, zero past
them), the `1` region (its `eq` weight). `QLT` is not a region (`okB`): its constants are in `Φ_Q`. -/
def virtEF (N : TNat) (pub : Pub) (ry : List FE) : FE :=
  let hdr := pub.hdrLanes.toArray
  N.regs.foldl (fun acc g => match g.src with
    | .pub => acc + hiW ry g.log g.base * mleK g.log (fun i => hdr.getD (g.dst + i) 0) ry
    | .one => acc + hiW ry g.log g.base
    | _ => acc) 0

/-! ## The phases (`typedProg`, read for read) -/

/-- **Zerocheck** (`zeroProg`): `τ`, 20 rounds in equality mode (2 scalars each), `a*, b*, c*`, the final
claim against `a*·b* + c*`. -/
def dZeroT : DM (List FE × FE × FE × FE) := do
  let tau ← samples xVars
  let rf ← sumcheck 0 3 (tau.map some)
  let abc ← readEs 3
  let a := abc.getD 0 0
  let b := abc.getD 1 0
  let c := abc.getD 2 0
  require (rf.2 == a * b + c)
  pure (rf.1, a, b, c)

/-- **Wiring** (`wireProg`): `γ`, 21 rounds (2 scalars each) from `a* + γb* + γ²c*`, the four matrix values,
the four region values (`C_main`'s committed block, `S_flat`, `σ′`, `KS`); the final claim against
`(v_A + γv_B + γ²(v_D + v_W))·(Σ regions + virtE)`. -/
def dWiringT (N : TNat) (pub : Pub) (abc : FE × FE × FE) : DM (List FE × List FE × List FE) := do
  let g ← sampleE
  let rf ← sumcheck (abc.1 + g * abc.2.1 + g * g * abc.2.2) 3 (List.replicate yVars none)
  let vs ← readEs 4
  let rv ← readEs 4
  require (rf.2 == (vs.getD 0 0 + g * vs.getD 1 0 + g * g * (vs.getD 2 0 + vs.getD 3 0)) *
    (sumE rv + virtEF N pub rf.1))
  pure (rf.1, vs, rv)

/-- **The `S_flat` relayout** (`relayProg`): 19 rounds from `v_S`, `v_R`, the final claim against
`kern(r_y, r)·v_R`. -/
def dRelayT (N : TNat) (ry : List FE) (vS : FE) : DM (List FE × FE) := do
  let rf ← sumcheck vS 3 (List.replicate relayRoundsN none)
  let vR ← readE
  require (rf.2 == relayKernF N ry rf.1 * vR)
  pure (rf.1, vR)

/-- **A23 at `Φ_Q`** (`accProgQ`): `κ` (2), `h` (44 coefficients), `t`, the zero scalar; `h(0) = acc_in.y`,
`h(1) = Σ_o eq(κ, o)·v_o`; the folded claim `(line(t), h(t))`, the line from `acc_in.pt` to `κ ‖ r_x ‖ r_y`
(its check is `decideFT`'s). -/
def dAccT (pub : Pub) (rxy vs : List FE) : DM Acc := do
  let kappa ← samples 2
  let h ← readEs (phiVarsN + 1)
  let t ← sampleE
  let z ← readE
  require (h.headD 0 == pub.accIn.y)
  require (sumE h == dot (eqKernel kappa) vs)
  require (z == 0)
  pure ⟨accLine pub.accIn.pt (kappa ++ rxy) t, polyEval h t⟩

/-- The mini-bus's native instance: `M3.real` on its tables (the record's `busDepth`, `tableRounds`,
`tableEvals` are the mini-bus's; `KS`'s blocks and links are the record's). -/
def TNat.m3 (N : TNat) (p : Params) : M3 := M3.real p fun _ => N.mbT

/-- **The mini-bus** (`miniBusProg`): the bus at `p.busDepth`, the table sumcheck, then the fixed columns
natively (`tableCheckR`: the pre-A23 check; the mini-bus's fixed columns are not in `Φ_Q`); the evaluations. -/
def dMiniT (p : Params) (m : M3) (tabs : List Lvm.M3.Tab) (pub : Pub) : DM (List (List FE × List FE)) := do
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  let xi ← sampleE
  let tables := m.tables pub
  let nC := (tables.map (·.nConstraints)).sum
  let xiPowers := powers xi (nC + 3)
  let formPowers := xiPowers.drop nC
  let evals ← tableSumcheck p.tableRounds tables bus.forms (xiPowers.take nC) formPowers
    point (dot formPowers bus.totals)
  require (Lvm.M3.tableCheckR (Lvm.M3.sumcheckTabs tabs) evals)
  pure evals

/-- **The record fits the mini-bus** (as `fitsR` for the bus path, without A23's conditions): one
leaf-decomposition scalar, `busDepth = ⌈log₂⌉` of the push leaves in `[1, 22]`, `tableRounds` the tallest
sumcheck table, `tableEvals` the widths' sum, every committed column aligned (`colsFitB`) and, for the small
shape, off `D` (`colsHiB`) and below `7·2^20` (inside the small shape's room). -/
def fitsMiniB (p : Params) (tabs : List Lvm.M3.Tab) : Bool :=
  let st := Lvm.M3.sumcheckTabs tabs
  p.leafdecReads == 1 && p.busDepth == log2Ceil (Lvm.M3.pushLeavesR tabs) && decide (1 ≤ p.busDepth) &&
    decide (p.busDepth ≤ 22) && p.tableRounds == (st.map (·.τ)).foldl max 0 &&
    p.tableEvals == (st.map (·.w)).sum && Lvm.M3.colsFitB p tabs && Lvm.M3.colsHiB tabs &&
    tabs.all fun t => t.cols.all fun c => match c with
      | .com rec off => rec || decide (off + 2 ^ t.τ ≤ 7 * 2 ^ 20)
      | .fix _ _ => true

/-- **The typed phases' claims** (`typedClaims`' order), tail `0` (`okB`: off `D`): on `C_rec` the relayout's
point claim and `σ′`'s; on `C_main` the committed block's and the `KS` aliases'. Each region claim is one
claim on the whole stack. -/
def typedClaimsN (N : TNat) (p : Params) (ry rv rr : List FE) (vR : FE) : List (Com × BlockClaim × FE) :=
  [(.crec, BlockClaim.point ⟨p.nuRec, 0⟩ rr vR, 0),
   (.crec, ⟨⟨p.nuRec, 0⟩, affW N .sigma ry, rv.getD 2 0⟩, 0),
   (.main, ⟨⟨p.nuMain, 0⟩, affW N .com ry, rv.getD 0 0⟩, 0),
   (.main, ⟨⟨p.nuMain, 0⟩, affW N .ks ry, rv.getD 3 0⟩, 0)]

/-! ## The two shapes at physical ν -/

/-- The relocated regions of the small shape at physical `ν` (logical `ν − 1`): `D_l`'s live `2^18` rows, then
the `2^20` blocks above `D` (big block `4 + j`, small `1 + j`, `j < 2^(ν−21) − 1`). `regionsN 24` is roll 7's
roll 7's `Shape.regions`; at ν = 23 (B1) the blocks are three, `Shape.regions` (`regionsN_23`). -/
def regionsN (nu : Nat) : List (Nat × Nat × Nat) :=
  ((List.range 4).map fun l => (18, l * 2 ^ 20, l * 2 ^ 18)) ++
    ((List.range (2 ^ (nu - 21) - 1)).map fun j => (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20))

/-- `relocF` at physical `ν`. -/
def relocN (nu : Nat) (x : List FE) (r : Nat × Nat × Nat) : List FE :=
  (x.tail ++ List.replicate (nu - 1) 0).take r.1 ++ selectorPoint (r.2.1 >>> r.1) (nu - r.1)

/-- `onStackZB` at physical `ν`: a big-stack block claim on the small physical stack, its tail given. -/
def onStackZBN (nu : Nat) (c : BlockClaim) (t : FE) : StackClaim :=
  (fun x => (1 - x.headD 0) * (((regionsN nu).filter (Shape.meets c.block)).map fun r =>
      (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * c.onStack.1 (relocN nu x r)).sum,
    c.value - t)

/-- The spec side's regions are `regionsN 23` (B1: `CMain.nu20 = 23`; roll 7's were `regionsN 24`). -/
theorem regionsN_23 : regionsN 23 = Shape.regions := rfl

/-- The spec side's relocation is `relocN 23`. -/
theorem relocN_23 : relocN 23 = Shape.relocF := rfl

/-- The spec side's small claim is `onStackZBN 23`. -/
theorem onStackZBN_23 : onStackZBN 23 = Shape.onStackZB := rfl

/-- The physical ν of B1's `C_main` (B1-G0: ν = 23, both shapes). -/
abbrev nuT : Nat := 23

/-- **The shape bit at ν = 23** (B1-G0 decision 2): `P20`'s record at physical ν = 23 and `n ≤ 2^18` (stride 2,
logical ν = 22 on the even words); stride 1 above. -/
def smallT (p : Params) (pub : Pub) : Bool :=
  p.logN == 20 && p.nuMain == nuT && decide (pub.n ≤ 2 ^ 18)

/-- **The openings in both shapes**: `C_rec`'s claims as before; `C_main`'s through `onStackZBN p.nuMain`
when small. -/
def dOpenT (p : Params) (s : Bool) (claims : List (Com × BlockClaim × FE)) : DM Unit := do
  verifyStackedOpening p.recLevels p.nuRec ((claims.filter (·.1 == .crec)).map (·.2.1.onStack)) false
    p.grind p.recOod
  let cm := (claims.filter (·.1 == .main)).map (·.2)
  verifyStackedOpening p.mainLevels p.nuMain
    (if s then cm.map fun e => onStackZBN p.nuMain e.1 e.2 else cm.map (·.1.onStack)) false p.grind p.mainOod

/-! ## The decision -/

/-- **The typed phases** (`typedProg`): zerocheck, wiring, relayout, A23, the mini-bus; the folded
accumulator and the claims (typed first, then the mini-bus's table claims). -/
def dTypedT (p : Params) (N : TNat) (m : M3) (pub : Pub) :
    DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) := do
  let z ← dZeroT
  let w ← dWiringT N pub z.2
  let r ← dRelayT N w.1 (w.2.2.getD 1 0)
  let acc ← dAccT pub (z.1 ++ w.1) w.2.1
  let evals ← dMiniT p m N.mbT pub
  pure (acc, typedClaimsN N p w.1 w.2.2 r.1 r.2, evals)

/-- **The typed decision program**: commit, the typed phases, tape, wire, `KS`, `KS` link, the openings
(`C_main`'s claims on the small stack when `smallT`); its value is the folded accumulator. The Keccak phases
and their claims are `decideProg`'s (`dClaimsZ` with no bus claims and the mini-bus's evaluations). -/
def decideProgT (p : Params) (N : TNat) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  let m := N.m3 p
  -- 1] commit
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  -- 2] the typed phases
  let (acc, tcl, evals) ← dTypedT p N m pub
  -- 3] the tape, the wire
  let tp ← dTape p.logN
  dRange p pub
  let (wo, rcs) ← Shape.dWireC p pub tp.claim
  -- 4] KS
  let rk ← samples p.ksLog
  let vks ← readEs lanes
  let kko ← verifyKeccak p.ksLog rk vks
  let kring ← ringSwitch kko.slicePoint kko.slices
  let ksClaims := keccakClaims m.ksBlock kko kring
  -- 5] KS link
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  -- 6] the openings
  dOpenT p (smallT p pub) (tcl ++ Shape.dClaimsZ m p pub [] evals tp wo rcs rk vks ksClaims kLinkClaims)
  pure acc

/-- **`decideProgT` with pending Keccak weights** (R10): the tape and `KS` through `dTapeS` and `verifyKeccakS`
(`LvmKeccakSym`), the same program (`decideProgTS_eq`). `decideFT` runs it. -/
def decideProgTS (p : Params) (N : TNat) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  let m := N.m3 p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  let (acc, tcl, evals) ← dTypedT p N m pub
  let tp ← dTapeS p.logN
  dRange p pub
  let (wo, rcs) ← Shape.dWireC p pub tp.claim
  let rk ← samples p.ksLog
  let vks ← readEs lanes
  let kko ← verifyKeccakS p.ksLog rk vks
  let kring ← ringSwitch kko.slicePoint kko.slices
  let ksClaims := keccakClaims m.ksBlock kko kring
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  dOpenT p (smallT p pub) (tcl ++ Shape.dClaimsZ m p pub [] evals tp wo rcs rk vks ksClaims kLinkClaims)
  pure acc

theorem decideProgTS_eq (p : Params) (N : TNat) (vk c : Vector UInt8 32) :
    decideProgTS p N vk c = decideProgT p N vk c := by
  unfold decideProgTS decideProgT
  simp only [dTapeS_eq, verifyKeccakS_eq]

/-- **`decideCoreT`**: every check of the typed program held and it read `Σ` to the end. -/
def decideCoreT (p : Params) (N : TNat) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (_, s) := (decideProgT p N vk c).runOn sig
  s.ok && s.ent == sig.size && s.msg == 0

/-- The folded accumulator of the typed program. -/
def accOutOfT (p : Params) (N : TNat) (vk c : Vector UInt8 32) (sig : ByteArray) : Acc :=
  ((decideProgT p N vk c).runOn sig).1

/-- **`F` of the typed backend**: `decideCoreT` and the folded claim at `Φ_Q` (`N.phi`, the one native
evaluation of the wiring), from one run. -/
def decideFT (p : Params) (N : TNat) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := (decideProgTS p N vk c).runOn sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phi a.pt == a.y

/-- **The split** (as `decideF_eq`): `decideFT = decideCoreT ∧ Φ_Q(accOutOfT) = y`. -/
theorem decideFT_eq (p : Params) (N : TNat) (vk c : Vector UInt8 32) (sig : ByteArray) :
    decideFT p N vk c sig =
      (decideCoreT p N vk c sig && N.phi (accOutOfT p N vk c sig).pt == (accOutOfT p N vk c sig).y) := by
  unfold decideFT decideCoreT accOutOfT
  rw [decideProgTS_eq]

end Lvm.TypedV
