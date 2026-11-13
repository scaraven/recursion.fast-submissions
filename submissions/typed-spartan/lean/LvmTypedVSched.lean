-- New for lvm2 (roll 8 = B1, B1-V; B-DES §1.2, §3.1; B1-G0 decisions 1–2): the schedule of the typed backend at
-- ν = 23 and the Z2 root leaf (`8·occ` bytes, PR #17 "relay-slim"). New declarations beside `LvmSchedule`'s
-- (whose declarations are INT's); INT points the driver at `scheduleT` at the refreeze.
import LvmSchedule
import LvmTypedV

/-!
# The typed schedule at ν = 23

* **`phasesT p`**: commit; the typed phases in `typedProg`'s order (`zero`: `τ`, 20 equality-mode rounds of 2
  scalars, `a*, b*, c*`; `wiring`: `γ`, 21 rounds of 2, the 4 matrix and the 4 region values; `relay`: 19
  rounds of 2, `v_R`; `acc`: `κ` (2), `h` (44), `t`, the zero scalar); the mini-bus (`miniBus`: `α`, `β`, the
  grand product at `busDepth`, `leafdecReads`; `miniTab`: `ξ`, the table sumcheck, `tableEvals`); then
  `decideProg`'s tape, wire, `KS`, `KS` link and the two openings. Read for read `decideProgT`'s.
* **`withOcc p mo ro`** (Z2): level 0's leaf of each commitment is its `occ` occupied words (`8·occ` bytes); the
  later levels keep their rows. The leaf query, `|π|`, `L`, `T` and the sponge blocks shrink with it.
* **`P20Tc`**: a candidate record at ν = 23 (B1-G0's `C_main` `(6,2,115)(4,3,77)(4,4,58)`, `g = 14`, final
  `2^9`; `C_rec` and `KS13` as P3/P4; the mini-bus at depth 13). The lead's refreeze of `LvmParams.P20` replaces
  it; its mini-bus numbers (`tableRounds 12`, `tableEvals 4`) are [e] until B1-Q's `mbT`. `sizes_P20Tc`:
  its tally (`|π|` 485,488 B, with Z2 440,408 B). The header still has `accVars = 28` (INT sets 43: `+15·24 = 360` B of header).
-/

set_option autoImplicit false

namespace Lvm

/-- The phases of the typed schedule. -/
inductive PhaseT where
  | commit | zero | wiring | relay | acc | miniBus | miniTab | tape | wire | ks | ksLink | openRec | openMain
  deriving DecidableEq, Repr, Inhabited

/-- **The typed backend's phases with their items** (`typedProg`, then `decideProg`'s Keccak phases and
openings; B-DES §1.2). -/
def phasesT (p : Params) : List (PhaseT × List Item) :=
  [(.commit, [.cap (p.level ⟨.main, 0⟩).cap ⟨.main, 0⟩, .cap (p.level ⟨.crec, 0⟩).cap ⟨.crec, 0⟩]),
   (.zero, List.flatten [smp Typed.xVars, sumcheckI Typed.xVars 2, rd 3]),
   (.wiring, List.flatten [smp 1, sumcheckI Typed.yVars 2, rd 4, rd 4]),
   (.relay, List.flatten [sumcheckI TypedV.relayRoundsN 2, rd 1]),
   (.acc, List.flatten [smp 2, rd (TypedV.phiVarsN + 1), smp 1, rd 1]),
   (.miniBus, List.flatten [smp (busBits + 1), gpI p.busDepth, rd p.leafdecReads]),
   (.miniTab, List.flatten [smp 1, sumcheckI p.tableRounds 3, rd p.tableEvals]),
   (.tape, List.flatten [smp p.logN, rd lanes, tapeLayersI p.logN]),
   (.wire, List.flatten [sumcheckI p.logN 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]),
   (.ks, List.flatten [smp p.ksLog, rd lanes, keccakI p.ksLog, smp ringStages]),
   (.ksLink, List.flatten [smp (p.ksLog + laneBits), sumcheckI p.ksLog 2, rd 4]),
   (.openRec, smp 1 ++ (if p.recOod then whirIJ else whirI) .crec p.recLevels p.recFinalLog p.grind),
   (.openMain, smp 1 ++ (if p.mainOod then whirIJ else whirI) .main p.mainLevels p.mainFinalLog p.grind)]

/-- **The typed schedule.** -/
def scheduleT (p : Params) : List Item := (phasesT p).flatMap (·.2)

/-- **The schedule is the typed one** (lvm2 roll 8, B1-IX's refreeze `S2GB1`): `LvmSchedule.phases` carries the
typed phases under the old phase names (`bus`: zerocheck, wiring, relayout, A23, the mini-bus's grand product;
`tables`: the mini-bus's table phase), so the driver, the plan, the tally and the circuit's positions all follow
`phasesT`. -/
theorem scheduleT_eq (p : Params) : scheduleT p = schedule p := by
  simp only [scheduleT, schedule, phasesT, phases, List.flatMap_cons, List.flatMap_nil, List.flatten_cons,
    List.flatten_nil, List.append_assoc, List.append_nil, Typed.xVars, Typed.yVars, TypedV.relayRoundsN,
    TypedV.phiVarsN, accVars]

/-- The tally of the typed schedule. -/
def tallyT (p : Params) : Tally := Tally.run p Tally.init (scheduleT p)

/-- `qS` of the typed schedule. -/
def qST (p : Params) : Nat := (tallyT p).entries

/-- `|π|` of the typed schedule. -/
def piSizeT (p : Params) : Nat :=
  let t := tallyT p
  headerBytes + t.bScalars + t.bCaps + t.bRows + t.bSibs

/-- `L` of the typed schedule. -/
def hashedLenT (p : Params) : Nat := 1 + (tallyT p).trace

/-- `T` (lanes) of the typed schedule. -/
def streamLanesT (p : Params) : Nat := hashedLenT p / 8

/-- Keccak-256 sponge blocks of the typed trace digest. -/
def spongeBlocksT (p : Params) : Nat := hashedLenT p / 136 + 1

/-- The length rule on the typed schedule (`lengthRule`'s, on `tallyT`). -/
def lengthRuleT (p : Params) : Bool :=
  let t := tallyT p
  let rows := (p.mainLevels ++ p.recLevels).map Level.row
  t.pendOk && t.fsLens.all (fun l => l % 8 == 0 && !(64 :: rows).contains l && l != seedLen) &&
    (64 :: rows).all (fun l => l % 8 == 0 && l != seedLen) && seedLen % 8 == 0 &&
    seedLen != 7 && hashedLenT p % 8 == 0

/-- The first trace entry of each typed phase that has one: index and byte offset. -/
def phaseFirstT (p : Params) : List (PhaseT × Nat × Nat) :=
  ((phasesT p).foldl (fun (acc : Tally × List (PhaseT × Nat × Nat)) ph =>
    let s' := Tally.run p acc.1 ph.2
    (s', if s'.entries > acc.1.entries then acc.2 ++ [(ph.1, acc.1.entries, 1 + acc.1.trace)]
      else acc.2)) (Tally.init, [])).2

/-! ## Z2: the root leaves carry the occupied lanes -/

-- `withRow0` is CRZ2's (`LvmParams`, #17's Z2; equal to B1-V's at `occ > 0`).

/-- **Z2** (B1-G0 decision 1): `C_main`'s root leaf is its `mo` occupied words, `C_rec`'s its `ro`. -/
def withOcc (p : Params) (mo ro : Nat) : Params :=
  { p with mainLevels := withRow0 p.mainLevels mo, recLevels := withRow0 p.recLevels ro }

/-- Permutations per leaf query of `w` words (`⌊(32 + 8w)/136⌋ + 1`, PORT-17 §5). -/
def leafPerms (w : Nat) : Nat := (32 + 8 * w) / 136 + 1

/-- B1-G0's `occ = 44` takes 3 permutations per `C_main` leaf, 64 lanes 5, and 47 lanes (B1-G0's risk line) 4. -/
theorem leafPerms_occ : leafPerms 44 = 3 ∧ leafPerms 46 = 3 ∧ leafPerms 47 = 4 ∧ leafPerms 64 = 5 ∧
    leafPerms 35 = 3 := by decide

/-! ## A candidate record at ν = 23 (the lead's refreeze replaces it) -/

/-- **The candidate typed record** (B1-G0a P3/P4): `C_main` ν = 23, folds `(6, 4, 4)`, rates `(2, 3, 4)`
(1/4 at level 0), caps `(8, 7, 7)`, Johnson counts `115, 77, 58` with OOD; `C_rec` as `P20`; `KS13`; the
mini-bus at depth 13 with one leaf-decomposition scalar, `tableRounds 12`, `tableEvals 4` [e]; `g = 14`. -/
def P20Tc : Params :=
  mkParams "P20Tc" 20 129 14 23 [6, 4, 4] [2, 3, 4] [8, 7, 7] [6, 4] [2, 3] [7, 7] 13 13
    13 1 12 4 0 14 [115, 77, 58] true [115, 77] true

/-- `P20Tc`'s levels `[ℓ, κ, R, height, cap, path, row]`: level 0's codeword is `2^25` (rate 1/4) in `2^19`
leaves of 64 words, as `P20`'s; final `2^9`. -/
theorem levels_P20Tc :
    P20Tc.mainLevels.map Level.shape =
      [[6, 17, 2, 19, 8, 11, 512], [4, 13, 3, 16, 7, 9, 384], [4, 9, 4, 13, 7, 6, 384]] ∧
    P20Tc.mainFinalLog = 9 ∧ P20Tc.nuRec = 19 ∧ P20Tc.mainLevels.map Level.t = [115, 77, 58] := by
  decide +kernel

/-- `P20Tc` with Z2 at B1-G0's `occ` (`C_main` 44, `C_rec` 35). -/
def P20TcZ : Params := withOcc P20Tc 44 35

set_option maxRecDepth 100000 in
/-- **The candidate's sizes** [exact given the record]: without Z2 `|π| = 485,848` B, with Z2 (`C_main` 44,
`C_rec` 35 lanes) **`|π| = 440,768` B** (B1-G0a's 485 / 440 KB; G2's lines 505 / 465 KB), at `accVars = 43`;
`qS = 5,470`; `T = 108,189 / 102,554` lanes; sponge blocks `6,365 / 6,033`, inside `KS13`'s
`0.95·(2^13 − 2^9) = 7,296`; the length rule holds. (The frozen `P20`'s mini-bus has 936 evaluations, not this
candidate's 4 [e]: `LvmSchedule.sizes_P20`.) -/
theorem sizes_P20Tc :
    (piSizeT P20Tc = 485848 ∧ qST P20Tc = 5470 ∧ streamLanesT P20Tc = 108189 ∧ spongeBlocksT P20Tc = 6365 ∧
      lengthRuleT P20Tc = true) ∧
    (piSizeT P20TcZ = 440768 ∧ qST P20TcZ = 5470 ∧ streamLanesT P20TcZ = 102554 ∧
      spongeBlocksT P20TcZ = 6033 ∧ lengthRuleT P20TcZ = true) ∧
    100 * spongeBlocksT P20TcZ ≤ 95 * (2 ^ 13 - 2 ^ 9) := by
  decide +kernel

end Lvm
