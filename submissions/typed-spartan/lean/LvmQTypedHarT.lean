-- New for lvm2 (roll 8 = B1, L-H): V_S's typed decision program cut into its phases (`decideProgT = decideProgTH`),
-- and the composition of the phase facts into `decideCoreT` and `accOutOfT` (roll 7's `core_of_phases` for
-- `decideProgT`: the typed phases replace phases 2, 3, 3b; phases 4–7 are unchanged; the openings are `dOpenT`).
import LvmQTypedHarB

/-!
# `decideProgT` by phases

| phase | program |
|---|---|
| typed (zerocheck, wiring, relayout, A23 at `Φ_Q`, mini-bus) | `dTypedT p N (N.m3 p) pub` |
| 4 tape, 5 wire, 6 `KS`, 7 `KS` link | `tapePh`, `wirePhC`, `ksPh`, `ksLinkPh` (roll 7's) |
| 8–9 openings | `dOpenT p (smallT p pub)` on the typed claims and `dClaimsZ`'s |

**`core_of_phasesT`**: if every phase, run from its start position with `ok`, keeps `ok`, reaches the next start and
yields fixed values, and the openings read `Σ` to its end, then `decideCoreT` accepts and `accOutOfT` is the typed
phases' accumulator.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

/-- **`decideProgT` by phases.** -/
def decideProgTH (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  let (acc, tcl, evals) ← TypedV.dTypedT p N (N.m3 p) pub
  let tp ← tapePh p
  let wo ← wirePhC p pub tp.claim
  let (rk, vks, kko, kring) ← ksPh p
  let (okK, kLinkClaims) ← ksLinkPh p (N.m3 p) rk pub
  require okK
  TypedV.dOpenT p (TypedV.smallT p pub) (tcl ++ Shape.dClaimsZ (N.m3 p) p pub [] evals tp wo.1 wo.2 rk vks
    (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims)
  pure acc

set_option maxHeartbeats 4000000 in
theorem decideProgT_eq (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) :
    TypedV.decideProgT p N vk c = decideProgTH p N vk c := by
  funext sig s
  simp only [TypedV.decideProgT, decideProgTH, tapePh, wirePhC, ksPh, ksLinkPh, bind_assoc, pure_bind]

/-- **`decideCoreT` and `accOutOfT` from the phases** (generic in the parameters and the instance). -/
theorem core_of_phasesT (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P4 P5 P6 P7 P8 : Nat} {acc : Acc} {tcl : List (Com × BlockClaim × FE)}
    {evals : List (List FE × List FE)} {tp : TapeRes} {wo : WireOut × List FE} {rk vks : List FE}
    {kko : KeccakOut} {kring : FE × (List FE → FE)} {okK : Bool} {kLinkClaims : List (Com × BlockClaim)}
    (h0 : RS.start.ent + (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap + nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap) = Pb)
    (htyped : PhaseAt (TypedV.dTypedT p N (N.m3 p) (pubOf vk c sig)) sig Pb P4 (acc, tcl, evals))
    (htape : PhaseAt (tapePh p) sig P4 P5 tp)
    (hwire : PhaseAt (wirePhC p (pubOf vk c sig) tp.claim) sig P5 P6 wo)
    (hks : PhaseAt (ksPh p) sig P6 P7 (rk, vks, kko, kring))
    (hksl : PhaseAt (ksLinkPh p (N.m3 p) rk (pubOf vk c sig)) sig P7 P8 (okK, kLinkClaims)) (hokK : okK = true)
    (hopen : ∀ s : RS, pos s = P8 → s.ok = true →
      let o := TypedV.dOpenT p (TypedV.smallT p (pubOf vk c sig))
        (tcl ++ Shape.dClaimsZ (N.m3 p) p (pubOf vk c sig) [] evals tp wo.1 wo.2 rk vks
          (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    TypedV.decideCoreT p N vk c sig = true ∧ TypedV.accOutOfT p N vk c sig = acc := by
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = ⟨RS.start.ent, nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap +
    nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap, true⟩ := ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← h0, hs1]; rfl
  obtain ⟨b1, b2, b3⟩ := htyped s1 e1 (by rw [hs1])
  generalize hB : TypedV.dTypedT p N (N.m3 p) (pubOf vk c sig) sig s1 = B at b1 b2 b3
  obtain ⟨bv, s2⟩ := B
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s2 b3 b2
  generalize hC : tapePh p sig s2 = CC at c1 c2 c3
  obtain ⟨cv, s5⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨l1, l2, l3⟩ := hwire s5 c3 c2
  generalize hL : wirePhC p (pubOf vk c sig) tp.claim sig s5 = LL at l1 l2 l3
  obtain ⟨lv, s6⟩ := LL
  simp only at l1 l2 l3
  rw [l1] at hL
  obtain ⟨k1, k2, k3⟩ := hks s6 l3 l2
  generalize hK : ksPh p sig s6 = KK at k1 k2 k3
  obtain ⟨kv, s7⟩ := KK
  simp only at k1 k2 k3
  rw [k1] at hK
  obtain ⟨m1, m2, m3⟩ := hksl s7 k3 k2
  generalize hM : ksLinkPh p (N.m3 p) rk (pubOf vk c sig) sig s7 = MM at m1 m2 m3
  obtain ⟨mv, s8⟩ := MM
  simp only at m1 m2 m3
  rw [m1] at hM
  obtain ⟨s8', hs8'⟩ : ∃ s8' : RS, s8' = { s8 with ok := okK && s8.ok } := ⟨_, rfl⟩
  have e8 : pos s8' = P8 := by rw [hs8']; exact m3
  have o8 : s8'.ok = true := by rw [hs8']; simp [hokK, m2]
  obtain ⟨o1, o2', o3⟩ := hopen s8' e8 o8
  generalize hO : TypedV.dOpenT p (TypedV.smallT p (pubOf vk c sig))
    (tcl ++ Shape.dClaimsZ (N.m3 p) p (pubOf vk c sig) [] evals tp wo.1 wo.2 rk vks
      (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims) sig s8' = OO at o1 o2' o3
  obtain ⟨ov, s9⟩ := OO
  simp only at o1 o2' o3
  have run : decideProgTH p N vk c sig RS.start = (acc, s9) := by
    unfold decideProgTH
    simp only [bind_run', read_run', skip_run', pure_run', require_run']
    have hs1' : ({ RS.start with msg := RS.start.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap +
        nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap } : RS) = s1 := by simp [hs1, RS.start]
    rw [hs1', hB]
    simp only
    rw [hC]
    simp only
    rw [hL]
    simp only
    rw [hK]
    simp only
    rw [hM]
    simp only
    rw [← hs8', hO]
  unfold TypedV.decideCoreT TypedV.accOutOfT DM.runOn
  rw [decideProgT_eq]
  simp only [StateT.run, run, o1, o2', o3, Bool.true_and, beq_self_eq_true, and_self]

end Lvm.Har
