-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): V_S's typed phases at S2GT natively (the DM twin of
-- `LvmE2TProg.typedProgT`, read for read; `E2` scalars of 16 B, one nonce per `E2` challenge, the mini-bus at `E3`).
import LvmE2TVKern
import LvmDecideE2
import LvmE2TProg

/-!
# V_S's typed phases at S2GT (`dTypedT`)

Read for read as `LvmE2TProg`'s programs, at `FE2` with E2F-V's reader primitives (`LvmDecideE2`: `readE2`,
`readE2s`, `sampleG`, `samplesG`, `sepE2`, `sumcheckD`):

* `dZeroT`: the separator, `τ` (20, `gTau`), `ω` (`gOmega`), 20 equality-mode rounds (`gZero`), nine values, the
  final claim against `zeroFinalD` (`Σ_k ω^k·((A ⊗ B)_k + C_k)`);
* `dWiringT`: `γ` (`gGamma`), 21 rounds (`gWire`) from `Σ_{k<9} γ^k v_k`, twelve matrix values, four region values,
  the final claim against `wGD γ vs·(Σ rv + virtD)`;
* `dRelayT2`: 19 rounds (`gWire`) from `v_S`, `v_R`, the final claim against `relayKernD·v_R`;
* `dAccT`: A23 at `Φ_Q` in 45 variables: `κ` (4, `gKappa`), `h` (46), `t` (`gT`), the zero scalar; the folded
  claim `(line(t), h(t))` at `E2`, returned as an `E3` accumulator with `c₂ = 0` (`fe2ToFE`; its `Φ_Q` check is
  the decision's, through the record's `phiT`);
* `dMiniT`: roll 11's `E3` mini-bus;
* `typedClaimsND`: `typedClaimsT`'s order with every `E2` claim split re then im: the relayout's point claim
  (`splitD`), `σ′`'s, the committed block's and the `KS` aliases' region claims (`affWD`: coordinate `h` of the
  region weight in `Quad Ext3`, V's `wordWD`).

The record `TNatT` is roll 11's `TNat` with `Φ_Q` at `E2` (`phiT`, 45 variables).
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm DM
open Lvm.TypedV (TNat NReg)
open Lvm.Typed (YSrc xVars yVars selBitsT phiVarsT mulY3 relayRounds)

/-- **The native typed instance at S2GT**: roll 11's regions and mini-bus tables, `Φ_Q` at `E2`. -/
structure TNatT where
  /-- The word space's regions (sorted by `base`, disjoint, with targets). -/
  regs : List NReg
  /-- `Φ_Q` natively at `E2` (45 variables: `κ ‖ r_x ‖ r_y`). -/
  phiT : List FE2 → FE2
  /-- The mini-bus's tables. -/
  mbT : List Lvm.M3.Tab

/-- Roll 11's record of the regions and tables (its `phi` unused at S2GT). -/
def TNatT.toN (N : TNatT) : TNat := ⟨N.regs, fun _ => 0, N.mbT⟩

/-! ## Arithmetic at `FE2` (the specification's, text for text) -/

/-- `zeroFinalT` natively. -/
def zeroFinalD (ω : FE2) (v : List FE2) : FE2 :=
  ((List.range 3).map fun k ↦
    ω ^ k * (mulY3 (fun j ↦ v.getD j 0) (fun j ↦ v.getD (3 + j) 0) k + v.getD (6 + k) 0)).sum

/-- `wBatchT` natively. -/
def wBatchD (γ : FE2) (v : List FE2) : FE2 := ((List.range 9).map fun k ↦ γ ^ k * v.getD k 0).sum

/-- `wGT` natively. -/
def wGD (γ : FE2) (vs : List FE2) : FE2 :=
  ((List.range 3).map fun j ↦ γ ^ j * vs.getD (4 * j) 0 + γ ^ (3 + j) * vs.getD (1 + 4 * j) 0 +
    γ ^ (6 + j) * (vs.getD (2 + 4 * j) 0 + vs.getD (3 + 4 * j) 0)).sum

/-- `lineT` natively. -/
def lineD (a b : List FE2) (t : FE2) : List FE2 := List.zipWith (fun x y ↦ x + t * (x + y)) a b

/-- `hEvalT` natively. -/
def hEvalD (hs : List FE2) (t : FE2) : FE2 := hs.foldr (fun c acc ↦ c + t * acc) 0

/-- `yOwnT` natively. -/
def yOwnD (vs κ : List FE2) : FE2 := E2V.dotF (E2V.eqKernelF κ) vs

/-- An `E2` value as an `E3` header scalar: lanes 0–1, `c₂ = 0` (`Lvm.e2OfFE` reads it back). -/
def fe2ToFE (z : FE2) : FE := ⟨z.re, z.im, 0⟩

/-- The natively computed part of `z̃(r_y)` at `E2` (`virtT`). -/
def virtD (N : TNatT) (pub : Pub) (ry : List FE2) : FE2 := virtG N.regs pub.hdrLanes.toArray ry

/-- The relayout's kernel at `E2` (`relayKernT`). -/
def relayKernD (N : TNatT) (ry r : List FE2) : FE2 := relayKernG (N.toN.regsOf .sflat) ry r

/-- **A region claim's weight at S2GT, coordinate `h`** (`regClaimT`): `X ↦ (Σ_reg eq(r, base)_hi ·
eq(r_lo, X_lo) · eq(X_hi, dst_hi))_h`, the `r`-side in `E2`, the `X`-side in `E3`, the product in `Quad Ext3`. -/
def affWD (N : TNatT) (s : YSrc) (r : List FE2) (h : Bool) : List FE → FE :=
  let terms := (N.toN.regsOf s).map fun g => (FE6.ofE2 (hiWG r g.log g.base), r.take g.log, g.log, g.dst >>> g.log)
  fun X =>
    let acc := terms.foldl (fun (acc : FE6) t =>
      let w := FE6.mul (FE6.mul t.1 (wordWD t.2.1 (X.take t.2.2.1))) (FE6.ofE (eqAtF (X.drop t.2.2.1) t.2.2.2))
      ⟨acc.re + w.re, acc.im + w.im⟩) ⟨0, 0⟩
    if h then acc.im else acc.re

/-- A region claim at S2GT, split: re then im (`regClaimT`). -/
def regClaimsND (N : TNatT) (p : Params) (s : YSrc) (ry : List FE2) (v : FE2) : List (Com × BlockClaim × FE) :=
  [false, true].map fun h ↦ (.main, ⟨⟨p.nuMain, 0⟩, affWD N s ry h, FE.ofK (if h then v.im else v.re)⟩, 0)

/-- **The typed phases' claims at S2GT** (`typedClaimsT`'s order, the mini-bus's apart), tail `0`: the relayout's
point claim on the stream block (split), `σ′`'s, the committed block's and the `KS` aliases' (split). -/
def typedClaimsND (N : TNatT) (p : Params) (ry rv rr : List FE2) (vR : FE2) : List (Com × BlockClaim × FE) :=
  splitZ p.nuMain [(1, ⟨p.nuRec, (layout0 p).s⟩, rr)] vR ++ regClaimsND N p .sigma ry (rv.getD 2 0) ++
    regClaimsND N p .com ry (rv.getD 0 0) ++ regClaimsND N p .ks ry (rv.getD 3 0)

/-! ## The phases (`typedProgT`, read for read) -/

/-- **Zerocheck at `E2`** (`zeroProgT`). -/
def dZeroT : DM (List FE2 × List FE2) := do
  sepE2
  let tau ← samplesG gTau xVars
  let om ← sampleG gOmega
  let rf ← sumcheckD gZero 0 3 (tau.map some)
  let v ← readE2s 9
  require (rf.2 == zeroFinalD om v)
  pure (rf.1, v)

/-- **Wiring at `E2`** (`wireProgT`). -/
def dWiringT (N : TNatT) (pub : Pub) (v : List FE2) : DM (List FE2 × List FE2 × List FE2) := do
  let g ← sampleG gGamma
  let rf ← sumcheckD gWire (wBatchD g v) 3 (List.replicate yVars none)
  let vs ← readE2s 12
  let rv ← readE2s 4
  require (rf.2 == wGD g vs * (E2V.sumF rv + virtD N pub rf.1))
  pure (rf.1, vs, rv)

/-- **The `S_flat` relayout at `E2`** (`relayProgT`). -/
def dRelayT2 (N : TNatT) (ry : List FE2) (vS : FE2) : DM (List FE2 × FE2) := do
  let rf ← sumcheckD gWire vS 3 (List.replicate relayRounds none)
  let vR ← readE2
  require (rf.2 == relayKernD N ry rf.1 * vR)
  pure (rf.1, vR)

/-- **A23 at `Φ_Q` in 45 variables, at `E2`** (`accProgT`): `κ` (4), `h` (46), `t`, the zero scalar; the folded
claim as an `E3` accumulator with `c₂ = 0`. -/
def dAccT (pub : Pub) (rxy vs : List FE2) : DM Acc := do
  let kappa ← samplesG gKappa selBitsT
  let h ← readE2s (phiVarsT + 1)
  let t ← sampleG gT
  let z ← readE2
  require (hEvalD h 0 == Lvm.e2OfFE pub.accIn.y)
  require (hEvalD h 1 == yOwnD vs kappa)
  require (z == 0)
  pure ⟨(lineD (pub.accIn.pt.map Lvm.e2OfFE) (kappa ++ rxy) t).map fe2ToFE, fe2ToFE (hEvalD h t)⟩

/-- **The typed phases at S2GT** (`typedProgT`): zerocheck, wiring, relayout, A23 at `E2`; the `E3` mini-bus;
the folded accumulator and the claims. -/
def dTypedT (p : Params) (N : TNatT) (m : M3) (pub : Pub) :
    DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) := do
  let z ← dZeroT
  let w ← dWiringT N pub z.2
  let r ← dRelayT2 N w.1 (w.2.2.getD 1 0)
  let acc ← dAccT pub (z.1 ++ w.1) w.2.1
  let evals ← TypedV.dMiniT p m N.mbT pub
  pure (acc, typedClaimsND N p w.1 w.2.2 r.1 r.2, evals)

end Lvm.E2T
