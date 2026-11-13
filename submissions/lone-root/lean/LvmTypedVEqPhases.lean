-- New for lvm2 (roll 8 = B1, wave L, L-C): V_S's typed phases (`LvmTypedV`: `dZeroT`, `dWiringT`, `dRelayT`,
-- `dAccT`, `dMiniT`, `dTypedT`) refine the specification's (`LvmTypedSpec`: `zeroProg`, `wireProg`, `relayProg`,
-- `accProgQ`, `miniBusProg`, `typedProg`) on the stream, read for read.
import LvmTypedVEqForms
import LvmAccNodeFold
import LvmVEqTop

/-!
# The typed phases: V_S refines the specification

On the native instance `N` with `TRefHyp N Q lay` (the shape check, the regions the layout's, the record the
mini-bus's, every mini-bus table a sumcheck table, `N.phi` the specification's `Φ_Q` on `43` coordinates) and
`Ti = N.inst Q lay`:

* `ref_dZeroT`, `ref_dWiringT` (`virtEF_rel`), `ref_dRelayT` (`relayKernF_rel`): the zerocheck, the wiring and the
  relayout, values mapped by `FE.toExt3`;
* `ref_dAccT`: A23 at `Φ_Q` under the promise that the folded claim holds natively (`N.phi a.pt = a.y`, which
  `decideFT` checks after the run), as roll 7's `ref_accFold`;
* `ref_dMiniT`: the mini-bus (WP-9b's bus and table phase, then the fixed columns: `tableCheckVB_of_R`);
* **`ref_dTypedT`**: the typed phases against `typedProg Ti pub` (`TRelT`: the native claims are `typedClaimsN`
  of the values whose images the specification's `typedClaims` takes, the mini-bus's claims those of its
  evaluations).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs AllSc lbusTableCheckProg)

/-- **What the typed refinement needs of the native instance** (INT's `StaticFactsT` gives `ok`, `hlay`, `mini`;
`THyp.sc` gives `sc`; `PhiQC_eq` with `cacheT20_eq` gives `phi`). -/
structure TRefHyp (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) : Prop where
  /-- The shape check the closed forms rely on. -/
  ok : N.okB P20.nuMain P20.nuRec = true
  /-- The native regions are the layout's. -/
  hlay : N.layOk lay = true
  /-- The record is the mini-bus's. -/
  mini : fitsMiniB P20 N.mbT = true
  /-- Every mini-bus table takes part in the table sumcheck. -/
  sc : AllSc N.mbT
  /-- V_S's `Φ_Q` is the specification's at `43` coordinates. -/
  phi : ∀ pt : List FE, pt.length = phiVars → N.phi pt = PhiQF Q lay pt

namespace TRefHyp

variable {N : TNat} {Q : Lvm.Loop.Program} {lay : Lay}

/-- Every mini-bus table is a sumcheck table. -/
theorem sc_eq (H : TRefHyp N Q lay) : sumcheckTabs N.mbT = N.mbT := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases H.sc t ht with h | h <;> simp [h]

/-- The record's mini-bus numbers (`fitsMiniB`). -/
theorem fits (H : TRefHyp N Q lay) : P20.leafdecReads = 1 ∧
    P20.tableRounds = (N.mbT.map (·.τ)).foldl max 0 ∧ P20.tableEvals = (N.mbT.map (·.w)).sum ∧
    M3.colsFitB P20 N.mbT = true ∧ M3.colsHiB N.mbT = true := by
  have h := H.mini
  unfold fitsMiniB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, hr⟩, he⟩, hc⟩, hh⟩, -⟩ := h
  rw [H.sc_eq] at hr he
  exact ⟨hl, hr, he, hc, hh⟩

end TRefHyp

/-- The mini-bus's depth at `P20`. -/
theorem busDepth_P20 : P20.busDepth = miniDepth := by decide +kernel

section Phases

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **The zerocheck.** -/
theorem ref_dZeroT :
    RefAt cap occ shp sig dZeroT zeroProg fun z z' ↦
      z' = (z.1.map FE.toExt3, FE.toExt3 z.2.1, FE.toExt3 z.2.2.1, FE.toExt3 z.2.2.2) ∧ z.1.length = xVars := by
  unfold dZeroT zeroProg
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) ((ref_samples _).retD (retD_samples _)) ?_
  rintro tau _ ⟨rfl, htau⟩
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3 (tau.map some) 0).retD
    (retD_sumcheck 3 (tau.map some) 0)
  rw [FE.toExt3_zero, List.map_map,
    show (Option.map FE.toExt3 ∘ some) = (some ∘ FE.toExt3) from rfl, ← List.map_map] at hs
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro abc _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · simp only [getD_map_toExt3]
    rw [← FE.toExt3_mul, ← FE.toExt3_add]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    refine RefAt.pure ⟨?_, ?_⟩
    · simp only [getD_map_toExt3]
    · rw [hrf, List.length_map, htau]

/-- **The wiring** (`virtEF_rel`). -/
theorem ref_dWiringT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (pub : Pub)
    (abc : FE × FE × FE) :
    RefAt cap occ shp sig (dWiringT N pub abc)
      (wireProg (N.inst Q lay) pub (FE.toExt3 abc.1, FE.toExt3 abc.2.1, FE.toExt3 abc.2.2)) fun w w' ↦
        w' = (w.1.map FE.toExt3, w.2.1.map FE.toExt3, w.2.2.map FE.toExt3) ∧ w.1.length = yVars ∧
          w.2.1.length = 4 ∧ w.2.2.length = 4 := by
  unfold dWiringT wireProg
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro g _ rfl
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3
    (List.replicate yVars none) (abc.1 + g * abc.2.1 + g * g * abc.2.2)).retD
    (retD_sumcheck 3 (List.replicate yVars none) _)
  rw [map_replicate_none] at hs
  simp only [FE.toExt3_add, FE.toExt3_mul] at hs
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
  · simp only [getD_map_toExt3]
    rw [sumE_map, ← virtEF_rel N Q lay P20.nuMain P20.nuRec H.ok H.hlay pub rf.1 hrf]
    simp only [← FE.toExt3_mul, ← FE.toExt3_add]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hrf, hvs, hrv⟩

/-- **The relayout** (`relayKernF_rel`). -/
theorem ref_dRelayT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (ry : List FE)
    (hry : ry.length = yVars) (vS : FE) :
    RefAt cap occ shp sig (dRelayT N ry vS) (relayProg (N.inst Q lay) (ry.map FE.toExt3) (FE.toExt3 vS))
      fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2) ∧ r.1.length = relayRoundsN := by
  unfold dRelayT relayProg
  have hs := (ref_sumcheck (cap := cap) (occ := occ) (shp := shp) (sig := sig) 3
    (List.replicate relayRoundsN none) vS).retD (retD_sumcheck 3 (List.replicate relayRoundsN none) _)
  rw [map_replicate_none] at hs
  refine RefAt.bind (fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf _ ⟨rfl, hrf⟩
  rw [List.length_replicate] at hrf
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro vR _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · rw [← relayKernF_rel N Q lay P20.nuMain P20.nuRec H.ok H.hlay ry rf.1 hry hrf, ← FE.toExt3_mul]
    exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq hc)
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hrf⟩

/-- **A23 at `Φ_Q`** under the promise that the folded claim holds natively. -/
theorem ref_dAccT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVars) (rxy vs : List FE) (hrxy : rxy.length = xVars + yVars) :
    RefAtP cap occ shp sig (dAccT pub rxy vs)
      (accProgQ Q lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (rxy.map FE.toExt3)
        (vs.map FE.toExt3))
      (fun _ _ ↦ True) (fun a ↦ N.phi a.pt = a.y) := by
  unfold dAccT accProgQ Lvm.Acc.accProg
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
  · have hlen : (accLine pub.accIn.pt (κ ++ rxy) t).length = phiVars := by
      rw [length_accLine, hacc, List.length_append, hκ, hrxy]; rfl
    rw [bOfQ, ← List.map_append, line_map, PhiQ, List.map_map,
      show (FE.ofExt3 ∘ FE.toExt3) = id from funext FE.ofExt3_toExt3, List.map_id, hEval_map,
      ← H.phi _ hlen]
    exact congrArg FE.toExt3 hA

/-- **The mini-bus**: the bus at the record's depth, the table sumcheck, the fixed columns natively. -/
theorem ref_dMiniT (p : Params) (tabs : List Tab) (pub : Pub) (hl : p.leafdecReads = 1)
    (hd : p.busDepth = miniDepth) (hr : p.tableRounds = (tabs.map (·.τ)).foldl max 0)
    (hsc : sumcheckTabs tabs = tabs) :
    RefAt cap occ shp sig (dMiniT p (M3.real p fun _ ↦ tabs) tabs pub) (lbusTableCheckProg tabs miniDepth)
      fun evs cl ↦ cl = claimsOfEvs tabs evs ∧ EvLen tabs evs ∧
        List.Forall₂ CRel (tableClaimsR tabs evs) (tableClaimsE tabs cl) := by
  have e : dMiniT p (M3.real p fun _ ↦ tabs) tabs pub =
      ((dBus p (M3.real p fun _ ↦ tabs) pub >>= fun pb ↦
        dTab p (M3.real p fun _ ↦ tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun r ↦
          DM.require (M3.tableCheckR (sumcheckTabs tabs) r.2) >>= fun _ ↦ pure r.2) := by
    simp only [dMiniT, dBus, dTab, bind_assoc, pure_bind]
  rw [e]
  have h := ref_busTabP (cap := cap) (occ := occ) (shp := shp) (sig := sig) p (fun _ ↦ tabs) pub hl
    (by rw [hsc]; exact hr)
  simp only [hsc, hd] at h
  unfold lbusTableCheckProg
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) h ?_
  rintro r cl ⟨-, hcl, rfl, hlen⟩
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · rw [hsc] at hc
    exact Lvm.M3.tableCheckVB_of_R _ _ hc fun j h1 h2 ↦ (hlen j h1 h2).le
  · intro _ _ _
    exact RefAt.pure ⟨rfl, hlen, hcl⟩

end Phases

theorem runD_bind_pure_fst {β γ δ : Type} (d : DM β) (a : γ) (f : β → δ) (sig : ByteArray) (s : RS) :
    (runD (d >>= fun k ↦ Pure.pure (a, f k)) sig s).1.1 = a := rfl

theorem monoD_dWiringT (N : TNat) (pub : Pub) (abc : FE × FE × FE) : MonoD (dWiringT N pub abc) :=
  monoD_sampleE.bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dRelayT (N : TNat) (ry : List FE) (vS : FE) : MonoD (dRelayT N ry vS) :=
  (monoD_sumcheck _ _ _).bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dAccT (pub : Pub) (rxy vs : List FE) : MonoD (dAccT pub rxy vs) :=
  (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dMiniT (p : Params) (m : M3) (tabs : List Tab) (pub : Pub) : MonoD (dMiniT p m tabs pub) :=
  (monoD_samples _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_verifyGkrGrandProducts _).bind fun ⟨_, _, _⟩ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        (monoD_tableSumcheck _ _ _ _ _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dZeroT : MonoD dZeroT :=
  (monoD_samples _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dTypedT (p : Params) (N : TNat) (m : M3) (pub : Pub) : MonoD (dTypedT p N m pub) :=
  monoD_dZeroT.bind fun _ ↦ (monoD_dWiringT _ _ _).bind fun _ ↦ (monoD_dRelayT _ _ _).bind fun _ ↦
    (monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- **The typed phases' native results against the specification's claims**: the native claims are
`typedClaimsN` of values (`r_y` of 21 coordinates, `r` of 19) whose images `typedClaims` takes, with the
mini-bus's claims those of its evaluations (`claimsOfEvs`), as many as its tables' columns. -/
def TRelT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay)
    (r : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims) : Prop :=
  ∃ ry rv rr : List FE, ∃ vR : FE, r.2.1 = typedClaimsN N P20 ry rv rr vR ∧ ry.length = yVars ∧
    rr.length = relayRoundsN ∧
    a = typedClaims (N.inst Q lay) (ry.map FE.toExt3) (rv.map FE.toExt3) (rr.map FE.toExt3) (FE.toExt3 vR)
      (claimsOfEvs N.mbT r.2.2) ∧
    EvLen N.mbT r.2.2 ∧ List.Forall₂ CRel (tableClaimsR N.mbT r.2.2) (tableClaimsE N.mbT (claimsOfEvs N.mbT r.2.2))

/-- **The typed phases refine `typedProg`** under the promise that the folded claim holds natively. -/
theorem ref_dTypedT {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} (N : TNat)
    (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (pub : Pub) (hacc : pub.accIn.pt.length = phiVars) :
    RefAtP cap occ shp sig (dTypedT P20 N (N.m3 P20) pub) (typedProg (N.inst Q lay) pub) (TRelT N Q lay)
      (fun r ↦ N.phi r.1.pt = r.1.y) := by
  obtain ⟨hl, hr, -, -, -⟩ := H.fits
  unfold dTypedT typedProg
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dWiringT _ _ _).bind fun _ ↦
    (monoD_dRelayT _ _ _).bind fun _ ↦ (monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦
      MonoD.pure _) (ref_dZeroT.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ ⟨rfl, hz⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dRelayT _ _ _).bind fun _ ↦
    (monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((ref_dWiringT N Q lay H pub z.2).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro w _ ⟨rfl, hry, hvs, hrv⟩ -
  have hR := ref_dRelayT (cap := cap) (occ := occ) (shp := shp) (sig := sig) N Q lay H w.1 hry (w.2.2.getD 1 0)
  rw [← getD_map_toExt3] at hR
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_dAccT _ _ _).bind fun _ ↦
    (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _) (hR.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro r _ ⟨rfl, hrr⟩ -
  have hA : RefAtP cap occ shp sig (dAccT pub (z.1 ++ w.1) w.2.1)
      (accProgQ (N.inst Q lay).Q (N.inst Q lay).lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3)
        (z.1.map FE.toExt3 ++ w.1.map FE.toExt3) (w.2.1.map FE.toExt3)) (fun _ _ ↦ True)
      (fun a ↦ N.phi a.pt = a.y) := by
    rw [← List.map_append]
    exact ref_dAccT N Q lay H pub hacc (z.1 ++ w.1) w.2.1 (by rw [List.length_append, hz, hry])
  dsimp only
  refine RefAtP.bind (Q := fun a ↦ N.phi a.pt = a.y) (fun _ ↦ (monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    hA (fun _ _ h ↦ by rw [runD_bind_pure_fst] at h; exact h) ?_
  intro acc _ _ _
  have hM := ref_dMiniT (cap := cap) (occ := occ) (shp := shp) (sig := sig) P20 N.mbT pub hl busDepth_P20 hr
    H.sc_eq
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) (hM.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro evs cl ⟨rfl, hlen, hcl⟩ -
  exact (RefAt.pure ⟨w.1, w.2.2, r.1, r.2, rfl, hry, hrr, rfl, hlen, hcl⟩).toP _

end Lvm.VEq
