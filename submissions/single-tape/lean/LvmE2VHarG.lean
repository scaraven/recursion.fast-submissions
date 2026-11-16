-- New for lvm2 S2GT (GT-V, STMT 10g): V_S's decision at S2GT by phases (`core_of_phasesG`, the instance of
-- `core_of_phasesFG` through `decideProgG_eq`) and `decideFGX_of`.
import LvmE2QHarTop
import LvmE2VDecG

/-!
# `decideProgG` by phases

**`core_of_phasesG`**: from the cursor after S2GT's header, if every phase of `decideProgG` (the root pin, `dTypedT`,
the tape and wire, `KS`, the `KS` link on `contRowsT`, the opening) keeps `ok` and meets the next, and the opening reads
`Σ` to its end, then `decideProgG` returns the typed phases' accumulator in an accepting state.
**`decideFGX_of`**: `decideFGX N` accepts once also `Φ_Q` at `E2` holds at the accumulator.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

theorem core_of_phasesG (N : Lvm.E2T.TNatT) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P1 P2 P3 P4 P5 : Nat} {pin : BlockClaim} {acc : Acc} {tcl : List (Com × BlockClaim × FE)}
    {evals : List (List FE × List FE)} {tp co} {lo : List FE2 × (List FE2 × FE2) × List FE2}
    (hb : pos (RS.startH (headerBytesP P20T)) + nodeBytes * 2 ^ (P20T.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD P20T.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (Lvm.E2T.dTypedT P20 N (Lvm.E2T.m3G N P20T) (Lvm.E2T.pubG vk c sig)) sig P1 P2
      (acc, tcl, evals))
    (htape : PhaseAt (tapeD P20T.logN (dSelBits P20T) (dSel P20T) (Lvm.E2T.pubG vk c sig).s
      (Lvm.E2T.pubG vk c sig).n) sig P2 P3 tp)
    (hcall : PhaseAt (callerD P20T.ksLog) sig P3 P4 co)
    (hlink : PhaseAt (ksLinkD P20T.ksLog (ksXLog P20T) Lvm.E2T.contRowsT) sig P4 P5 lo)
    (hopen : ∀ s : RS, pos s = P5 → s.ok = true →
      let o := dOpenF P20T (TypedV.smallT P20T (Lvm.E2T.pubG vk c sig)) pin
        (tcl ++ Shape.zeroTails ((Lvm.E2T.m3G N P20T).tableClaims (Lvm.E2T.pubG vk c sig) evals) ++
          frontClaimsD P20T (Lvm.E2T.pubG vk c sig) tp co lo) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, Lvm.E2T.decideProgG N vk c sig (RS.startH (headerBytesP P20T)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0 := by
  rw [Lvm.E2T.decideProgG_eq]
  exact core_of_phasesFG Lvm.E2T.pubG Lvm.E2T.contRowsT P20T (fun m pub => Lvm.E2T.dTypedT P20 N m pub)
    (Lvm.E2T.m3G N) vk c sig _ rfl hb hpin htyped htape hcall hlink hopen

/-- **`decideFGX` accepts** when its run (from the cursor after S2GT's header) ends accepting with the accumulator
`acc` and `Φ_Q` at `E2` holds at it. -/
theorem decideFGX_of (N : Lvm.E2T.TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, Lvm.E2T.decideProgG N vk c sig (RS.startH (headerBytesP P20T)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phiT (acc.pt.map Lvm.e2OfFE) = Lvm.e2OfFE acc.y) :
    Lvm.E2T.decideFGX N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  unfold Lvm.E2T.decideFGX DM.runOnH
  simp only [StateT.run, h1, h2, h3, h4, hphi, Bool.true_and, beq_self_eq_true, Bool.and_self]

end Lvm.Har
