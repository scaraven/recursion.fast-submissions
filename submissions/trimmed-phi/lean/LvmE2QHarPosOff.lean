/- `LvmE2QHarPosOff` (GOLF2 off-path move, group 34 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQAsmHarRun, LvmE2QHarPos,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQAsmHarRun
import LvmE2QHarPos
import LvmMlListLemmas
import LvmQAsmHar47

-- ===== from `LvmQAsmHarRun` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm DM

/-- **Phase 5** (lvm2 S2): A1's range of `n` (`dRange`), then the wire (T3–T4, `dWire`). -/
def wirePh (p : Params) (pub : Pub) (claim : KeccakClaim) : DM WireOut := do
  dRange p pub
  dWire p pub claim

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm DM

/-- The claims of phase 8 (`decideProg`'s list before roll 7; `claimsOfZ`'s without the tails). -/
def claimsOf (p : Params) (m : M3) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut) (rk vks : List FE) (kko : KeccakOut) (kring : FE × (List FE → FE))
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim) :=
  bus.claims ++ m.tableClaims pub evals ++
    (tapeClaims p tp wo pub ++ keccakClaims m.ksBlock kko kring).map (.main, ·) ++
    m.ksOutputClaims rk vks ++ kLinkClaims

/-- **Phases 8–9** before roll 7 (`openPhZ p pub` at the big shape). -/
def openPh (p : Params) (claims : List (Com × BlockClaim)) : DM Unit := do
  let on (com : Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  verifyStackedOpening p.recLevels p.nuRec (on .crec) false p.grind p.recOod
  verifyStackedOpening p.mainLevels p.nuMain (on .main) false p.grind p.mainOod

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm DM

/-- At the big shape the openings are `openPh` of the claims without their tails. -/
theorem openPhZ_big (p : Params) (pub : Pub) (claims : List (Com × BlockClaim × FE))
    (h : Shape.smallP p pub = false) :
    openPhZ p pub claims = openPh p (claims.map fun e ↦ (e.1, e.2.1)) := by
  rw [openPhZ, h, Shape.dOpenZ_false]; rfl

theorem claimsOfZ_fst (p : Params) (m : M3) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut × List FE) (rk vks : List FE) (kko : KeccakOut)
    (kring : FE × (List FE → FE)) (kLinkClaims : List (Com × BlockClaim)) :
    (claimsOfZ p m pub bus evals tp wo rk vks kko kring kLinkClaims).map (fun e ↦ (e.1, e.2.1)) =
      claimsOf p m pub bus evals tp wo.1 rk vks kko kring kLinkClaims := by
  rw [claimsOfZ, Shape.dClaimsZ_fst]; rfl

end Lvm.Har
end

-- ===== from `LvmE2QHarPos` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm
section Tape
variable {p : Params} (h : StE2 p) (hA : alignB p = true)
include h hA

/-- The first `r` challenge's nonce (`logN ≥ 1`). -/
theorem tape_item1 (hlog : 1 ≤ p.logN) :
    (schedule p).getD (phaseItem0 p .tape + 1) default = .readW 1 nonceBytes := by
  have hl := length_tape p
  rw [sched_phase h (mem_tape p) (by omega)]
  obtain ⟨n, hn⟩ : ∃ n, p.logN = n + 1 := ⟨p.logN - 1, by omega⟩
  simp only [tapeIts, hn]
  rfl

/-- **The first `r` answer's lane** (QH5's `samplesG_phase` `hq`: `8q = P + 48`, `P` the first nonce). -/
theorem tape_rq (hlog : 1 ≤ p.logN) : 8 * phaseLane p .tape 2 = posOf p (phaseItem0 p .tape + 1) + 48 := by
  have hl := length_tape p
  have e := posOf_succ hA (k := phaseItem0 p .tape + 1) (by have := phase_lt h (mem_tape p) (j := 2) (by omega); omega)
    (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
    (by rw [Nat.add_assoc]; exact notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  rw [tape_item1 h hA hlog] at e
  have l2 := lane_pos hA (k := phaseItem0 p .tape + 2) (phase_lt h (mem_tape p) (by omega))
    (notOpen_in h (mem_tape p) (noOpen_tape p) (by omega))
  rw [phaseLane, l2, show phaseItem0 p .tape + 2 = phaseItem0 p .tape + 1 + 1 by omega, e]
  simp only [itemW, nonceBytes]

end Tape
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm
section Tape
variable {p : Params} (h : StE2 p) (hA : alignB p = true)
include h hA

/-- **The tape GKR's start** (QH4's `tape_phase2`: `8 qs − 48 = P`). -/
theorem tape_qs : 8 * phaseLane p .tape (2 * p.logN + 3) - 48 = posOf p (phaseItem0 p .tape + (2 * p.logN + 2)) := by
  have := tape_qsA h hA
  omega

end Tape
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm
section Tape
variable {p : Params} (h : StE2 p) (hA : alignB p = true)
include h hA

theorem ks_item0 (hk : 1 ≤ p.ksLog) : (schedule p).getD (phaseItem0 p .ks) default = .readW 1 nonceBytes := by
  have hl := length_ks p
  have e := sched_phase h (mem_ks p) (j := 0) (by omega)
  rw [Nat.add_zero] at e
  rw [e]
  obtain ⟨n, hn⟩ : ∃ n, p.ksLog = n + 1 := ⟨p.ksLog - 1, by omega⟩
  simp only [ksIts, hn]
  rfl

/-- **The first instance challenge's answer lane** (QH5's `samplesG_phase` `hq`, `P` the `KS` start). -/
theorem ks_rq (hk : 1 ≤ p.ksLog) : 8 * phaseLane p .ks 1 = posOf p (phaseItem0 p .ks) + 48 := by
  have hl := length_ks p
  have h2 := keccakE2I_len p.ksLog
  have hkl := phase_lt h (mem_ks p) (j := 1) (by omega)
  have e := posOf_succ hA (k := phaseItem0 p .ks) hkl
    (by have := notOpen_in h (mem_ks p) (noOpen_ks p) (j := 0) (by omega); rwa [Nat.add_zero] at this)
    (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  rw [ks_item0 h hA hk] at e
  have l1 := lane_pos hA hkl (notOpen_in h (mem_ks p) (noOpen_ks p) (by omega))
  rw [phaseLane, l1, e]
  simp only [itemW, nonceBytes]

end Tape
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm
section Tape
variable {p : Params} (h : StE2 p) (hA : alignB p = true)
include h hA

theorem ks_qs : 8 * phaseLane p .ks (2 * p.ksLog + 2) - 48 = posOf p (phaseItem0 p .ks + (2 * p.ksLog + 1)) := by
  have := ks_qsA h hA
  omega

end Tape
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm

set_option maxRecDepth 200000 in
/-- **The S2GF schedule keeps the cursor on lane boundaries** (the one evaluation of `schedule P20F` here). -/
theorem alignF : alignB P20F = true := by
  unfold P20F; rw [Lvm.Replay.P20_eq]; decide +kernel

theorem stage_P20F : P20F.stage = 1 := rfl

theorem stE2_P20F : StE2 P20F := Or.inl rfl

/-- **`core_of_phasesF`'s `hb` at S2GF**: the pin's start `Pb` is `posOf P20F 1`. -/
theorem hbF : Lvm.Har.pos (RS.startH (headerBytesP P20F)) + nodeBytes * 2 ^ (P20F.level ⟨.main, 0⟩).cap =
    posOf P20F 1 := by
  rw [pos_startH, posOf_one stE2_P20F alignF]

/-- **QH5's `pin_phase` `hP` at S2GF.** -/
theorem pinHPF : posOf P20F 1 + 40 = 8 * phaseLane P20F .commit 1 := pin_hP stE2_P20F alignF

/-- **QH5's `pin_phase` `hqa` at S2GF.** -/
theorem pinQaF : phaseLane P20F .commit (P20F.nuMain + 1) = phaseLane P20F .commit 1 + 9 * P20F.nuMain :=
  pin_hqa stE2_P20F alignF

/-- **The pin's end is the typed phases' start at S2GF.** -/
theorem pinEndF : posOf P20F 1 + 72 * P20F.nuMain + 24 = typedPosF P20F := pin_end stE2_P20F alignF

end Lvm.E2Q
end
