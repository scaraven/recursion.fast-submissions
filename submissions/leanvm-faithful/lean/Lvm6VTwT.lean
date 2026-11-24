-- New for lvm6 (WP-TWT): the fast twin of Y1's typed phase on the stack (`typedPhase6`): `typedProgE` (irreducible,
-- read through its equation) as the composition of the per-part twins, the seven claims as fast claims.
import Lvm6VTwTMb
import Lvm6VTwTCov
import Lvm6TyStmt

/-!
# The fast typed phase

* `regClaimF`, `typedClaimsF` (the claims of `typedClaimsE` as `FClaim`s; `typedClaimsF_dec`).
* **`fTypedProgE`**, **`tw_typedProgE`**: zerocheck, wiring, relayout, A23 (with any evaluator of `Φ_Q`,
  `PhiOk ev Q lay`), the mini-bus; under `Ti.Ok` and CD's layout `TyLayOk Ti`.
* `recClaimF`; **`fTypedPhase6`**, **`tw_typedPhase6`**: the phase on the stack (FORMAT6 §6.4's seven claims);
  `tw_typedPhase6_mk` (`phiFast`), **`tw_typedPhase6_cov`** (`phiCov` with `covCheck`, PHI-decision R1).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V Lvm.Typed Lvm.Loop
open LeanVM.Protocol.Compile hiding Proof Bytes Word

open Lvm6.Ty (TInst6 TyInst6 typedProgE typedPhase6 typedClaimsE regClaimE regSumW regSumT OpenClaimsE
  claimsOnStack recClaim recOff L6 relayRounds)
open Lvm6.Mb (BClaimG ClaimE miniBusLProg6 miniDepth)
open Lvm6.QD (TyLayOk)

/-! ## The claims -/

theorem toE2_regSumW (Ti : TInst6) (S : Lvm.Typed.YSrc → Bool) (f : ℕ → FE2) :
    FE2.toE2 (regSumW Ti S f) = regSumW Ti S (fun y => FE2.toE2 (f y)) := by
  unfold regSumW
  rw [← coe_tE, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun reg _ => ?_)
  simp only [Function.comp_apply]
  split
  · rw [map_list_sum, List.map_map]; rfl
  · exact map_zero tE

/-- A region claim (`regClaimE`) as a fast claim. -/
def regClaimF (Ti : TInst6) (s : Lvm.Typed.YSrc) (w : ℕ → ℕ) (r : List FE2) (v : FE2) : FClaim :=
  ⟨fun X => regSumW Ti (fun s' => s' == s) fun y => eqAtF r y * eqAtF X (w y), v⟩

theorem regClaimF_dec (Ti : TInst6) (s : Lvm.Typed.YSrc) (w : ℕ → ℕ) (r : List FE2) (v : FE2) :
    (regClaimF Ti s w r v).dec = regClaimE Ti s w (r.map FE2.toE2) (FE2.toE2 v) := by
  simp only [FClaim.dec, regClaimF, regClaimE, regSumT, Prod.mk.injEq, and_true]
  funext X
  rw [toE2_regSumW]
  simp only [toE2_mul', toE2_eqAtF, map_toE2_ofE2]

/-- A point claim on `C_rec`'s whole window (`(BClaimG.point ⟨19, 0⟩ rr vR).onStack`). -/
def pointRecF (rr : List FE2) (vR : FE2) : FClaim :=
  ⟨fun x => eqAboveF ⟨relayRounds, 0⟩ x * eqEvalF rr (x.take relayRounds), vR⟩

theorem pointRecF_dec (rr : List FE2) (vR : FE2) :
    (pointRecF rr vR).dec = (BClaimG.point ⟨relayRounds, 0⟩ (rr.map FE2.toE2) (FE2.toE2 vR)).onStack := by
  simp only [FClaim.dec, pointRecF, BClaimG.point, BClaimG.onStack, Prod.mk.injEq, and_true]
  funext x
  rw [toE2_mul', toE2_eqAboveF, map_toE2_ofE2, toE2_eqEvalF, List.map_take, map_toE2_ofE2]

/-- **The typed claims as fast claims** (`typedClaimsE`). -/
def typedClaimsF (Ti : TInst6) (ry rv rr : List FE2) (vR : FE2) (cl : List FClaim) : List FClaim × List FClaim :=
  ([pointRecF rr vR, regClaimF Ti .sigma Ti.sigmaW ry (rv.getD 2 0)],
    [regClaimF Ti .com Ti.comW ry (rv.getD 0 0), regClaimF Ti .ks Ti.ksW ry (rv.getD 3 0)] ++ cl)

/-- The decoding of the two claim lists. -/
def tcD (o : List FClaim × List FClaim) : OpenClaimsE := (o.1.map FClaim.dec, o.2.map FClaim.dec)

theorem typedClaimsF_dec (Ti : TInst6) (ry rv rr : List FE2) (vR : FE2) (cl : List FClaim) :
    tcD (typedClaimsF Ti ry rv rr vR cl) =
      typedClaimsE Ti (ry.map FE2.toE2) (rv.map FE2.toE2) (rr.map FE2.toE2) (FE2.toE2 vR) (cl.map FClaim.dec) := by
  simp only [tcD, typedClaimsF, typedClaimsE, List.map_cons, List.map_nil, List.map_append, pointRecF_dec,
    regClaimF_dec, toE2_getD]

/-! ## The typed phases -/

/-- **Fast `typedProgE Ti L pw (acc)`**, the accumulator as words (`accP`, `accY`), `Φ_Q` off `tab`. -/
def fTypedProgE (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (tab : List FE2 → FE2) (accP : List FE2)
    (accY : FE2) :
    VF (List FClaim × List FClaim) :=
  VF.bind fZero fun z => VF.bind (fWire Ti pw z.2) fun w => VF.bind (fRelay Ti w.1 (w.2.2.getD 1 0)) fun r =>
  VF.bind (fAcc tab accY accP (z.1 ++ w.1) w.2.1) fun _ =>
  VF.bind (fMiniBus6 L Ti.mbT miniDepth) fun cl => VF.pure (typedClaimsF Ti w.1 w.2.2 r.1 r.2 cl)

theorem tw_typedProgE {Ti : TInst6} (hok : Ti.Ok) (hlay : TyLayOk Ti) (L : Lvm.M3.Lay) (pw : ℕ → FK)
    {tab : List FE2 → FE2} (htab : PhiOk tab Ti.Q Ti.lay) (accP : List FE2) (accY : FE2) :
    TwinF tcD (typedProgE Ti L pw (accP.map FE2.toE2, FE2.toE2 accY)) (fTypedProgE Ti L pw tab accP accY) := by
  rw [typedProgE]
  refine tw_bind tw_zero fun z => ?_
  refine twP_bind (tw_wire hok hlay pw z.2) fun w hw => ?_
  simp only [l3D, l2D]
  rw [← toE2_getD]
  refine tw_bind (tw_relay hok hlay.1 w.1 hw _) fun r => ?_
  rw [← List.map_append]
  refine tw_bind (tw_acc htab accY accP (z.1 ++ w.1) w.2.1) fun _ => ?_
  refine tw_bind (tw_miniBus6 L Ti.mbT miniDepth) fun cl => tw_pure ?_
  rw [typedClaimsF_dec]
  rfl

/-- `recClaim` on fast claims. -/
def recClaimF (c : FClaim) : FClaim := ⟨fun X => eqAboveF ⟨19, recOff⟩ X * c.f (X.take 19), c.v⟩

theorem recClaimF_dec (c : FClaim) : (recClaimF c).dec = recClaim c.dec := by
  simp only [FClaim.dec, recClaimF, recClaim, Prod.mk.injEq, and_true]
  funext X
  rw [toE2_mul', toE2_eqAboveF, map_toE2_ofE2, List.map_take]

theorem tw_fail {α β : Type} (d : β → α) : TwinF d VerifierProgram.fail (fun _ _ => none) := by
  intro π tr
  rw [replayP_fail]
  exact Option.Rel.none

/-- **The fast typed phase on the stack** (`typedPhase6 sh i`), `Φ_Q` off `tab`. -/
def fTypedPhase6 (sh : Lvm6.Shape) (i : TyInst6) (tab : List FE2 → FE2) : VF (List FClaim) :=
  if sh.M = 25 then
    VF.bind (fTypedProgE i.Ti L6 i.pw tab (i.acc.1.map FE2.ofE2) (FE2.ofE2 i.acc.2)) fun out =>
      VF.pure (out.1.map recClaimF ++ out.2)
  else fun _ _ => none

/-- **The typed phase's fast twin**: under CD's layout, with any table computing `Φ_Q` (e.g.
`mkPhiTab (entsE i.Ti.Q i.Ti.lay)`, `phiOk_mk`). -/
theorem tw_typedPhase6 (sh : Lvm6.Shape) (i : TyInst6) (hlay : TyLayOk i.Ti) {tab : List FE2 → FE2}
    (htab : PhiOk tab i.Ti.Q i.Ti.lay) :
    TwinF (List.map FClaim.dec) (typedPhase6 sh i) (fTypedPhase6 sh i tab) := by
  unfold typedPhase6 fTypedPhase6
  split_ifs
  · have h := tw_typedProgE i.ok hlay L6 i.pw htab (i.acc.1.map FE2.ofE2) (FE2.ofE2 i.acc.2)
    rw [map_toE2_ofE2, FE2.toE2_ofE2] at h
    refine tw_bind h fun out => tw_pure ?_
    simp only [List.map_append, List.map_map, Function.comp_def, recClaimF_dec, claimsOnStack, tcD]
  · exact tw_fail _

/-- **The typed phase with its own table.** -/
theorem tw_typedPhase6_mk (sh : Lvm6.Shape) (i : TyInst6) (hlay : TyLayOk i.Ti) :
    TwinF (List.map FClaim.dec) (typedPhase6 sh i)
      (fTypedPhase6 sh i (phiFast (mkPhiTab (Lvm6.Ty.entsE i.Ti.Q i.Ti.lay)))) :=
  tw_typedPhase6 sh i hlay (phiOk_mk _ _)

/-- **The cover-form `Φ_Q` computes `Φ_Q`** once its start-up check passed. -/
theorem phiOk_cov {Q : Program} {lay : Lay} {tab : Cov} (h : covCheck tab (Lvm6.Ty.entsE Q lay) = true) :
    PhiOk (phiCov tab) Q lay := fun pt => phiCov_ents tab _ h pt

/-- **The typed phase with the cover-form `Φ_Q`** (PHI-decision R1). -/
theorem tw_typedPhase6_cov (sh : Lvm6.Shape) (i : TyInst6) (hlay : TyLayOk i.Ti) {tab : Cov}
    (h : covCheck tab (Lvm6.Ty.entsE i.Ti.Q i.Ti.lay) = true) :
    TwinF (List.map FClaim.dec) (typedPhase6 sh i) (fTypedPhase6 sh i (phiCov tab)) :=
  tw_typedPhase6 sh i hlay (phiOk_cov h)

end Lvm6.V
