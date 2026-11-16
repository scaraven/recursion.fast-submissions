-- New for lvm2 E2F (slice S1, E2F-Q-V): V_S's typed phases at S2GF (`LvmTypedVX`: `dZeroX`, `dWiringX`, `dAccX`,
-- `dTypedX`) refine the specification's (`LvmTypedSpecXD`: `zeroProgX`, `wireProgX`, `accProgQX`, `typedProgX`) on
-- the stream, read for read; roll 11's `LvmTypedVEqPhases` with the coordinate split (s2gf AMENDMENT 1).
import LvmTypedVEqTop
import LvmTypedVX
import LvmTypedSpecXD

-- (GOLF2: 1 declarations that `certified` does not use moved verbatim to `LvmTypedVEqPhasesXOff`, outside its import closure.)

/-!
# The typed phases at S2GF: V_S refines the specification

On the native instance `N` with `TRefHypX N Q lay` (roll 11's `TRefHyp` with `N.phi` the specification's
coordinate-split `Φ_Q` on `phiVarsX = 44` coordinates; in the S2GF instance `N.phi := PhiQCX (cacheWX Q lay)`,
`LvmWiringX.PhiQCX_eq`) and `Ti = N.inst Q lay`:

* `ref_dZeroX`: the coordinate-split zerocheck (`τ`, `ω`, six values), values mapped by `FE.toExt3`;
* `ref_dWiringX` (`virtEF_rel`): the wiring from `Σ_k γ^k v_k` with eight matrix values;
* `ref_dAccX`: A23 at `Φ_Q` in 44 variables (`κ` of 3, `h` of 45) under the promise that the folded claim holds
  natively, for an incoming point of `phiVarsX` coordinates;
* the relayout and the mini-bus are roll 11's `ref_dRelayT`, `ref_dMiniT` (through `TRefHypX.toT`: `withPhiT`, the
  instance with `phi` replaced, which neither phase reads);
* **`ref_dTypedX`**: the typed phases against `typedProgX Ti pub`, roll 11's relation `TRelT`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs AllSc lbusTableCheckProg)

/-- **What the coordinate-split typed refinement needs of the native instance**: `TRefHyp` with `N.phi` the
specification's `Φ_Q` on `phiVarsX = 44` coordinates (S2GF: `N.phi = PhiQCX (cacheWX Q lay)`, `PhiQCX_eq`). -/
structure TRefHypX (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) : Prop where
  /-- The shape check the closed forms rely on. -/
  ok : N.okB P20.nuMain P20.nuRec = true
  /-- The native regions are the layout's. -/
  hlay : N.layOk lay = true
  /-- The record is the mini-bus's. -/
  mini : fitsMiniB P20 N.mbT = true
  /-- Every mini-bus table takes part in the table sumcheck. -/
  sc : AllSc N.mbT
  /-- V_S's `Φ_Q` is the specification's coordinate-split one at `44` coordinates. -/
  phi : ∀ pt : List FE, pt.length = phiVarsX → N.phi pt = PhiQFX Q lay pt

/-- `N` with roll 11's `Φ_Q` (the phases other than A23 do not read `phi`). -/
def withPhiT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) : TNat := ⟨N.regs, PhiQF Q lay, N.mbT⟩

/-- **Roll 11's hypothesis on `withPhiT N Q lay`.** -/
theorem TRefHypX.toT {N : TNat} {Q : Lvm.Loop.Program} {lay : Lay} (H : TRefHypX N Q lay) :
    TRefHyp (withPhiT N Q lay) Q lay :=
  ⟨H.ok, H.hlay, H.mini, H.sc, fun _ _ ↦ rfl⟩

/-! ## Arithmetic over `E` -/

theorem toExt3_list_sum (l : List FE) : FE.toExt3 l.sum = (l.map FE.toExt3).sum := by
  induction l with
  | nil => exact FE.toExt3_zero
  | cons x l ih => rw [List.sum_cons, FE.toExt3_add, ih, List.map_cons, List.sum_cons]

/-- The wiring's starting claim over `E`. -/
theorem toExt3_wStart (g : FE) (v : List FE) :
    FE.toExt3 (((List.range 6).map fun k ↦ g ^ k * v.getD k 0).sum) =
      ((List.range 6).map fun k ↦ FE.toExt3 g ^ k * (v.map FE.toExt3).getD k 0).sum := by
  rw [toExt3_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ ↦ ?_
  rw [Function.comp_apply, FE.toExt3_mul, FE.toExt3_npow, getD_map_toExt3]

/-- The wiring's batch over `E`. -/
theorem toExt3_wGXF (g : FE) (vs : List FE) : FE.toExt3 (wGXF g vs) = wGX (FE.toExt3 g) (vs.map FE.toExt3) := by
  simp only [wGXF, wGX, getD_map_toExt3, FE.toExt3_add, FE.toExt3_mul, FE.toExt3_npow]

/-- `x` read over `E` is `g`. -/
theorem toExt3_ofK_x : FE.toExt3 (FE.ofK FK.x) = ofK g := by
  rw [FE.toExt3_ofK]; rfl

section Phases

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **The coordinate-split zerocheck.** -/
theorem ref_dZeroX :
    RefAt cap occ shp sig dZeroX zeroProgX fun z z' ↦
      z' = (z.1.map FE.toExt3, z.2.map FE.toExt3) ∧ z.1.length = xVars ∧ z.2.length = 6 := by
  unfold dZeroX zeroProgX
  refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    ((ref_samples _).retD (retD_samples _)) ?_
  rintro tau _ ⟨rfl, htau⟩
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro om _ rfl
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3 (tau.map some) 0).retD
    (retD_sumcheck 3 (tau.map some) 0)
  rw [FE.toExt3_zero, List.map_map,
    show (Option.map FE.toExt3 ∘ some) = (some ∘ FE.toExt3) from rfl, ← List.map_map] at hs
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEsL _) ?_
  rintro v _ ⟨rfl, hv⟩
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · simp only [getD_map_toExt3]
    rw [← toExt3_ofK_x]
    simp only [← FE.toExt3_mul, ← FE.toExt3_add]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    refine RefAt.pure ⟨rfl, ?_, hv⟩
    rw [hrf, List.length_map, htau]

/-- **The coordinate-split wiring** (`virtEF_rel`). -/
theorem ref_dWiringX (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypX N Q lay) (pub : Pub)
    (v : List FE) :
    RefAt cap occ shp sig (dWiringX N pub v) (wireProgX (N.inst Q lay) pub (v.map FE.toExt3)) fun w w' ↦
      w' = (w.1.map FE.toExt3, w.2.1.map FE.toExt3, w.2.2.map FE.toExt3) ∧ w.1.length = yVars ∧
        w.2.1.length = 8 ∧ w.2.2.length = 4 := by
  unfold dWiringX wireProgX
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro g _ rfl
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3
    (List.replicate yVars none) (((List.range 6).map fun k ↦ g ^ k * v.getD k 0).sum)).retD
    (retD_sumcheck 3 (List.replicate yVars none) _)
  rw [map_replicate_none, toExt3_wStart] at hs
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  rw [List.length_replicate] at hrf
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_readEsL _) ?_
  rintro vs _ ⟨rfl, hvs⟩
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEsL _) ?_
  rintro rv _ ⟨rfl, hrv⟩
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · rw [sumE_map, ← virtEF_rel N Q lay P20.nuMain P20.nuRec H.ok H.hlay pub rf.1 hrf, ← toExt3_wGXF,
      ← FE.toExt3_add, ← FE.toExt3_mul]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hrf, hvs, hrv⟩

/-- **A23 at `Φ_Q` in 44 variables** under the promise that the folded claim holds natively. -/
theorem ref_dAccX (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypX N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVarsX) (rxy vs : List FE) (hrxy : rxy.length = xVars + yVars) :
    RefAtP cap occ shp sig (dAccX pub rxy vs)
      (accProgQX Q lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (rxy.map FE.toExt3)
        (vs.map FE.toExt3))
      (fun _ _ ↦ True) (fun a ↦ N.phi a.pt = a.y) := by
  unfold dAccX accProgQX Lvm.Acc.accProg
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (((ref_samples _).retD (retD_samples _)).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro κ _ ⟨rfl, hκ⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    ((ref_readEsL _).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro h _ ⟨rfl, -⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    (ref_sampleE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro t _ rfl -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_readE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ rfl -
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _) fun h0 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun h1 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ MonoD.pure _) fun hz ↦ ?_
  refine RefAtP.pure_require fun hA ↦ ?_
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [Lvm.Acc.hEval_zero, ← toExt3_headD, Lvm.M3.FE_eq_of_beq h0]
  · rw [Lvm.Acc.hEval_one, sumE_map, Lvm.M3.FE_eq_of_beq h1, yOwnQ, ← map_eqKernel, toExt3_dot]
  · rw [Lvm.M3.FE_eq_of_beq hz, FE.toExt3_zero]
  · have hlen : (accLine pub.accIn.pt (κ ++ rxy) t).length = phiVarsX := by
      rw [length_accLine, hacc, List.length_append, hκ, hrxy]; rfl
    rw [bOfQ, ← List.map_append, line_map, PhiQX, List.map_map,
      show (FE.ofExt3 ∘ FE.toExt3) = id from funext FE.ofExt3_toExt3, List.map_id, hEval_map,
      ← H.phi _ hlen]
    exact congrArg FE.toExt3 hA

end Phases

theorem monoD_dZeroX : MonoD dZeroX :=
  (monoD_samples _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dWiringX (N : TNat) (pub : Pub) (v : List FE) : MonoD (dWiringX N pub v) :=
  monoD_sampleE.bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dAccX (pub : Pub) (rxy vs : List FE) : MonoD (dAccX pub rxy vs) :=
  (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dTypedX (p : Params) (N : TNat) (m : M3) (pub : Pub) : MonoD (dTypedX p N m pub) :=
  monoD_dZeroX.bind fun _ ↦ (monoD_dWiringX _ _ _).bind fun _ ↦ (monoD_dRelayT _ _ _).bind fun _ ↦
    (monoD_dAccX _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- **The typed phases at S2GF refine `typedProgX`** under the promise that the folded claim holds natively
(roll 11's relation `TRelT`: the relayout, the mini-bus and the claims are unchanged). -/
theorem ref_dTypedX {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} (N : TNat)
    (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypX N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVarsX) :
    RefAtP cap occ shp sig (dTypedX P20 N (N.m3 P20) pub) (typedProgX (N.inst Q lay) pub) (TRelT N Q lay)
      (fun r ↦ N.phi r.1.pt = r.1.y) := by
  obtain ⟨hl, hr, -, -, -⟩ := H.toT.fits
  unfold dTypedX typedProgX
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dWiringX _ _ _).bind fun _ ↦
    (monoD_dRelayT _ _ _).bind fun _ ↦ (monoD_dAccX _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦
      MonoD.pure _) (ref_dZeroX.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ ⟨rfl, hz, -⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dRelayT _ _ _).bind fun _ ↦
    (monoD_dAccX _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((ref_dWiringX N Q lay H pub z.2).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro w _ ⟨rfl, hry, -, -⟩ -
  have hR : RefAt cap occ shp sig (dRelayT N w.1 (w.2.2.getD 1 0))
      (relayProg (N.inst Q lay) (w.1.map FE.toExt3) (FE.toExt3 (w.2.2.getD 1 0)))
      fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2) ∧ r.1.length = relayRoundsN :=
    ref_dRelayT (withPhiT N Q lay) Q lay H.toT w.1 hry (w.2.2.getD 1 0)
  rw [← getD_map_toExt3] at hR
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dAccX _ _ _).bind fun _ ↦
    (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _) (hR.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro r _ ⟨rfl, hrr⟩ -
  have hA : RefAtP cap occ shp sig (dAccX pub (z.1 ++ w.1) w.2.1)
      (accProgQX (N.inst Q lay).Q (N.inst Q lay).lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3)
        (z.1.map FE.toExt3 ++ w.1.map FE.toExt3) (w.2.1.map FE.toExt3)) (fun _ _ ↦ True)
      (fun a ↦ N.phi a.pt = a.y) := by
    rw [← List.map_append]
    exact ref_dAccX N Q lay H pub hacc (z.1 ++ w.1) w.2.1 (by rw [List.length_append, hz, hry])
  dsimp only
  refine RefAtP.bind (Q := fun a ↦ N.phi a.pt = a.y) (fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    hA (fun _ _ h ↦ by rw [runD_bind_pure_fst] at h; exact h) ?_
  intro acc _ _ _
  have hM := ref_dMiniT (cap := cap) (occ := occ) (shp := shp) (sig := sig) P20 N.mbT pub hl busDepth_P20 hr
    H.toT.sc_eq
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) (hM.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro evs cl ⟨rfl, hlen, hcl⟩ -
  exact (RefAt.pure ⟨w.1, w.2.2, r.1, r.2, rfl, hry, hrr, rfl, hlen, hcl⟩).toP _

end Lvm.VEq
