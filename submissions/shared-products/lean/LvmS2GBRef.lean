-- New for lvm2 MP-B cap pruning (CAP-V, 2026-11-17; lead decision D-V1): `V_S` at S2GB refines the compiled `P_S` on
-- the EXPANDED proof. The compiled verifier (`Scheme.V`) climbs every path to the sent cap with all siblings in the
-- body, while an S2GB proof carries only the `D` lower siblings (the upper ones are heap answers): the specification
-- runs on `fillB P20B π w`, π's static part with `m − c` upper siblings per path from `w` (static size `pzB`).
import LvmS2GBRefSim
import LvmS2GBRefDec

/-!
# `V_S` at S2GB refines the compiled specification (owner V)

* The definitions (`fillB`, `pzB`, `capOfB`, `schemeSWB`, `fmtB20`, `midGB`, `TRefHypTB`) are `LvmS2GBFill`'s.
* **`refinesB20`** (MPG §6 item 7, `-- CAP-FRZ V`): `refinesB_of` (`LvmS2GBRefSim`: the driver and the compiled
  verifier on the expanded proof) with `ref_decideGB` (`LvmS2GBRefDec`: the decision on the S2GB stream).
-/

set_option autoImplicit false

namespace Lvm.E2S

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.CT Lvm.E2F Lvm.E2U Lvm.E2L Lvm.E2T Lvm.Typed
open LeanVM.Protocol.Compile
open Lvm.M3 (Tab mbLinB)

/-- **`refinesB20`'s proof at a typed-phase record `pT`** with the mini-bus at depth 13: `refinesB_of` with
`ref_decideGB`, `fol_PSOfB`, `decideFSB_ok`, `pubGB_eq`. -/
theorem refinesB20_of (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypTB N Q lay)
    (hσ : Lvm.TypedV.SigInSL (layout0 P20B).s N.toN) (hlin : mbLinB N.mbT = true)
    (pT : Params) (hbus : pT.busDepth = 13) (hld : pT.leafdecReads = 1) (VS : SProg)
    (hVS : ∀ vk c π, VS vk c π =
      if parseOkB P20B vk c π then driveB P20B π (decideFSB P20B pT (contIvSB aSP) N vk c) else .ret false) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      (VS vk c π).runLog L = some true →
      ∃ w : List UInt8,
        ((schemeSWB fmtB20 vk (PSWithM (midP (midMk 4 relocU20 (midGB (N.inst Q lay)))))).V c
          (fillB P20B π w)).runLog L = some true := fun vk L c π h ↦ by
  rw [hVS] at h
  exact Lvm.VEq.refinesB_of _ (readWidthsP P20B).length (fun vk c ↦ decideFSB P20B pT (contIvSB aSP) N vk c)
    (decideProgSB P20B pT (contIvSB aSP) N) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y)
    (fun sig vk c x ↦ pubOfWS vk c sig = pubXTS x) (fun _ _ _ hF ↦ Lvm.VEq.decideFSB_ok hF)
    (fun _ _ _ _ hp hs ↦ Lvm.VEq.pubGB_eq hp hs)
    (fun sig vk c x hpub ↦ Lvm.VEq.ref_decideGB N Q lay H hlin hσ pT hbus hld sig vk c x hpub)
    (fun x ↦ Lvm.VEq.fol_PSOfB relocU20 (N.inst Q lay) x) vk L c π h

/-- **MPG §6 item 7** (owner V): **`V_S` at S2GB refines the compiled specification on the expanded proof**: if
`VSSB N` accepts `π` on the log `L`, the compiled verifier of `schemeSWB fmtB20` (sent caps, middle phases `midGB`)
accepts `fillB P20B π w` on `L` for some upper siblings `w`. -/
theorem refinesB20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypTB N Q lay)
    (hσ : Lvm.TypedV.SigInSL (layout0 P20B).s N.toN) (hlin : mbLinB N.mbT = true) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSSB N vk c π).runLog L = some true →
      ∃ w : List UInt8,
        ((schemeSWB fmtB20 vk (PSWithM (midP (midMk 4 relocU20 (midGB (N.inst Q lay)))))).V c
          (fillB P20B π w)).runLog L = some true :=
  fun vk L c π _ h ↦ refinesB20_of N Q lay H hσ hlin pTB rfl (by decide) (VSSB N) (fun vk c π ↦ by
    rw [VSSB, show decideFBX N vk c = decideFSB P20B pTB (contIvSB aSP) N vk c from funext fun _ ↦ rfl]) vk L c π h

end Lvm.E2S
