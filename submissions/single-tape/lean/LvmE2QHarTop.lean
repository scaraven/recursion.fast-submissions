-- New for lvm2 E2-FT (E2F-C): V_S's decision at S2GF (`decideProgF`, E2F-V) cut into its phases, and the composition
-- of the phase facts into one accepting run (roll 7's `core_of_phases` / roll 11's `core_of_phasesT` for
-- `decideProgF`: the cap's skip (`hb`), the root pin, the typed phases, the tape and wire, `KS`, the `KS` link, the opening).
import LvmQAsmHarTop
import LvmQAsmHarRun
import LvmE2VRefines

/-!
# `decideProgF` by phases

| phase | program |
|---|---|
| the root pin | `pinD p.nuMain` |
| typed (zerocheck with `ω`, wiring, relayout, A23, mini-bus) | `typed (m3 p) pub` (S2GF: `dTypedX`) |
| tape and wire, with the row switch | `tapeD p.logN (dSelBits p) (dSel p) pub.s pub.n` |
| `KS` | `callerD p.ksLog` |
| `KS` link | `ksLinkD p.ksLog (ksXLog p) E2V.contRowsF` |
| the opening | `dOpenF p (smallT p pub) pin (…)` |

**`core_of_phasesF`**: from a start state `s₀` (S2GF: `RS.startH (headerBytesP p)`), if every phase, run from its
start position with `ok`, keeps `ok`, reaches the next start and yields fixed values, and the opening reads `Σ` to
its end, then `decideProgF` returns the typed phases' accumulator in an accepting state.
**`decideFFX_of`**: `decideFFX p N` accepts once also `Φ_Q` holds at the accumulator.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

/-- **`decideProgFG` by phases** (any public values' reader `pubR`, any `KS` link rows). -/
theorem core_of_phasesFG (pubR : Vector UInt8 32 → Vector UInt8 32 → ByteArray → Pub) (rows : List ℕ) (p : Params)
    (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) (sig : ByteArray) (s₀ : RS) (h₀ : s₀.ok = true)
    {Pb P1 P2 P3 P4 P5 : Nat} {pin : BlockClaim} {acc : Acc} {tcl : List (Com × BlockClaim × FE)}
    {evals : List (List FE × List FE)} {tp co} {lo : List FE2 × (List FE2 × FE2) × List FE2}
    (hb : pos s₀ + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (typed (m3 p) (pubR vk c sig)) sig P1 P2 (acc, tcl, evals))
    (htape : PhaseAt (tapeD p.logN (dSelBits p) (dSel p) (pubR vk c sig).s (pubR vk c sig).n)
      sig P2 P3 tp)
    (hcall : PhaseAt (callerD p.ksLog) sig P3 P4 co)
    (hlink : PhaseAt (ksLinkD p.ksLog (ksXLog p) rows) sig P4 P5 lo)
    (hopen : ∀ s : RS, pos s = P5 → s.ok = true →
      let o := dOpenF p (TypedV.smallT p (pubR vk c sig)) pin
        (tcl ++ Shape.zeroTails ((m3 p).tableClaims (pubR vk c sig) evals) ++
          frontClaimsD p (pubR vk c sig) tp co lo) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, decideProgFG pubR rows p typed m3 vk c sig s₀ = (acc, s₉) ∧ s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0 := by
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = { s₀ with msg := s₀.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← hb, hs1]; simp only [pos]; omega
  obtain ⟨a1, a2, a3⟩ := hpin s1 e1 (by rw [hs1]; exact h₀)
  generalize hA : pinD p.nuMain sig s1 = AA at a1 a2 a3
  obtain ⟨av, s2⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨b1, b2, b3⟩ := htyped s2 a3 a2
  generalize hB : typed (m3 p) (pubR vk c sig) sig s2 = BB at b1 b2 b3
  obtain ⟨bv, s3⟩ := BB
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s3 b3 b2
  generalize hC : tapeD p.logN (dSelBits p) (dSel p) (pubR vk c sig).s (pubR vk c sig).n sig s3 =
    CC at c1 c2 c3
  obtain ⟨cv, s4⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨d1, d2, d3⟩ := hcall s4 c3 c2
  generalize hD : callerD p.ksLog sig s4 = DD at d1 d2 d3
  obtain ⟨dv, s5⟩ := DD
  simp only at d1 d2 d3
  rw [d1] at hD
  obtain ⟨f1, f2, f3⟩ := hlink s5 d3 d2
  generalize hF : ksLinkD p.ksLog (ksXLog p) rows sig s5 = FF at f1 f2 f3
  obtain ⟨fv, s6⟩ := FF
  simp only at f1 f2 f3
  rw [f1] at hF
  obtain ⟨o1, o2, o3⟩ := hopen s6 f3 f2
  generalize hO : dOpenF p (TypedV.smallT p (pubR vk c sig)) pin
    (tcl ++ Shape.zeroTails ((m3 p).tableClaims (pubR vk c sig) evals) ++
      frontClaimsD p (pubR vk c sig) tp co lo) sig s6 = OO at o1 o2 o3
  obtain ⟨ov, s7⟩ := OO
  simp only at o1 o2 o3
  refine ⟨s7, ?_, o1, o2, o3⟩
  unfold decideProgFG
  simp only [bind_run', read_run', skip_run', pure_run']
  rw [← hs1, hA]
  simp only
  rw [hB]
  simp only
  rw [hC]
  simp only
  rw [hD]
  simp only
  rw [hF]
  simp only
  rw [hO]

/-- **`decideProgF` by phases** (`core_of_phasesFG` at S2GF's reader and rows). -/
theorem core_of_phasesF (p : Params)
    (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (vk c : Vector UInt8 32) (sig : ByteArray) (s₀ : RS) (h₀ : s₀.ok = true)
    {Pb P1 P2 P3 P4 P5 : Nat} {pin : BlockClaim} {acc : Acc} {tcl : List (Com × BlockClaim × FE)}
    {evals : List (List FE × List FE)} {tp co} {lo : List FE2 × (List FE2 × FE2) × List FE2}
    (hb : pos s₀ + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (typed (m3 p) (pubOfA p.accV vk c sig)) sig P1 P2 (acc, tcl, evals))
    (htape : PhaseAt (tapeD p.logN (dSelBits p) (dSel p) (pubOfA p.accV vk c sig).s (pubOfA p.accV vk c sig).n)
      sig P2 P3 tp)
    (hcall : PhaseAt (callerD p.ksLog) sig P3 P4 co)
    (hlink : PhaseAt (ksLinkD p.ksLog (ksXLog p) E2V.contRowsF) sig P4 P5 lo)
    (hopen : ∀ s : RS, pos s = P5 → s.ok = true →
      let o := dOpenF p (TypedV.smallT p (pubOfA p.accV vk c sig)) pin
        (tcl ++ Shape.zeroTails ((m3 p).tableClaims (pubOfA p.accV vk c sig) evals) ++
          frontClaimsD p (pubOfA p.accV vk c sig) tp co lo) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, decideProgF p typed m3 vk c sig s₀ = (acc, s₉) ∧ s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0 :=
  core_of_phasesFG (pubOfA p.accV) E2V.contRowsF p typed m3 vk c sig s₀ h₀ hb hpin htyped htape hcall hlink hopen

/-- **`decideFFX` accepts** when its run (from the cursor after the stage's header) ends accepting with the
accumulator `acc` and `Φ_Q` holds at it. -/
theorem decideFFX_of (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, decideProgF p (fun m pub => TypedV.dTypedX p N m pub) N.m3 vk c sig
      (RS.startH (headerBytesP p)) = (acc, s₉) ∧ s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phi acc.pt = acc.y) :
    E2V.decideFFX p N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  unfold E2V.decideFFX DM.runOnH
  rw [decideProgFF_eq]
  simp only [StateT.run, h1, h2, h3, h4, hphi, Bool.true_and, beq_self_eq_true, Bool.and_self]

end Lvm.Har
