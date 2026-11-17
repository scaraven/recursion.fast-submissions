-- New for lvm2 S1 (E2-F, E2F-V): the schedule of stage S2GF (M1: roll 11's S2GM with the root OOD pin, the `E2`
-- front with ground challenges, the typed phase of transcript amendment 1), item for item as the frozen
-- `s2gf.py` (its item dump), and its sizes. E2F-QH3 (route A, lead decision): the items and builders now
-- live in `LvmSchedule` (`Item.readW`, `phasesS2GF`, `Params.stage`/`accV`); the names below are abbreviations of the
-- one schedule at `P20F`.
import LvmSchedule

-- (GOLF2: 3 declarations that `certified` does not use moved verbatim to `LvmCertF20InstOff`, outside its import closure.)

/-!
# The S2GF schedule

`LvmSchedule.Item.readW m w`: the prover sends `m` scalars of `w` bytes each (`w = 16`: an `E2` scalar, re then
im; `w = 8`: a nonce, one `K` word). `phases p` at a stage-`1` record is `phasesS2GF p` (the builders `gsmp`,
`sumcheckE2I`, `keccakLayerE2I`, `tapeLayersE2I`, `keccakE2I` and `rowSwitchStages` are in `LvmSchedule`).
`Params.withF p accV` is `p` at stage `1` with `accV` header variables; `scheduleF p accV`, `tallyF p accV` … are
`schedule`, `tally` … at it.

**Sizes at `P20F`** (`accV = 44`) [model, frozen]: `|π|` 306,992, `qS` 3,959, `L` 584,008, `T` 73,001,
4,295 sponge blocks (`checks_P20F`).
-/

set_option autoImplicit false

namespace Lvm

/-- An S2GF item (the one schedule's `Item`). -/
abbrev ItemF := Item

/-- `p` at stage `S2GF` with A23's `accV` variables. -/
def Params.withF (p : Params) (accV : Nat) : Params := { p with stage := 1, accV := accV }

/-- **The S2GF schedule.** -/
abbrev scheduleF (p : Params) (accV : Nat) : List Item := schedule (p.withF accV)

/-- The header with A23's `accV + 1` scalars. -/
def headerF (accV : Nat) : Nat := 8 + 8 + 32 + 32 + 32 + 8 + 32 + sigBytes + eBytes * (accV + 1)

/-- `qS` at S2GF. -/
abbrev qSF (p : Params) (accV : Nat) : Nat := qS (p.withF accV)

/-- `|π|` at S2GF. -/
abbrev piSizeF (p : Params) (accV : Nat) : Nat := piSize (p.withF accV)

/-- The hashed length `L`. -/
abbrev hashedLenF (p : Params) (accV : Nat) : Nat := hashedLen (p.withF accV)

/-- The stream's lanes `T = L / 8`. -/
abbrev streamLanesF (p : Params) (accV : Nat) : Nat := streamLanes (p.withF accV)

/-- Keccak-256 sponge blocks of the trace digest. -/
abbrev spongeBlocksF (p : Params) (accV : Nat) : Nat := spongeBlocks (p.withF accV)

/-- A23's variables at S2GF (amendment 1: three selector bits, `Φ_Q` on 44 variables). -/
def accVF : Nat := 44

/-- **The S2GF parameters**: `P20`'s (`ν = 23`, `(6,2,115) (4,3,77) (4,4,58)`, `KS13`, the mini-bus record of
`S2GM`) at stage `1`, A23 at 44 variables. -/
def P20F : Params := { P20 with name := "P20F", stage := 1, accV := accVF }

end Lvm

namespace Lvm

/-- The byte width of each scalar read of the S2GF schedule, in order (`read m`: `m` reads of 24 B; `readW m w`:
`m` reads of `w` B; caps, samples, positions and openings read no scalar). -/
def readWidthsF (p : Params) (accV : Nat) : List Nat :=
  (scheduleF p accV).flatMap fun
    | .read m => List.replicate m eBytes
    | .readW m w => List.replicate m w
    | _ => []

/-- **The width of the `i`-th read** of a run at S2GF (the compile's `rw`; E2F-LEAD 2026-11-13): 24 for an `E`
scalar, 16 for an `E2` scalar, 8 for a nonce; 24 past the schedule. -/
def rwF20 (i : Nat) : Nat := (readWidthsF P20F accVF).getD i eBytes

/-- **The length rule** at S2GF (`lengthRule` with `seedLenF`). -/
abbrev lengthRuleF (p : Params) (accV : Nat) : Bool := lengthRule (p.withF accV)

set_option maxRecDepth 100000 in
/-- **S2GF's frozen sizes** (`s2gf.py`, amendment 1; [model] until the prover's refreeze): one kernel
evaluation of `tallyF P20F accVF`; the read widths `rwF20` reads: 8,956 reads of 147,736 bytes in all at K = 32 (evaluated) [exact]. -/
theorem checks_P20F : (piSizeF P20F accVF = 339000 ∧ qSF P20F accVF = 3924 ∧
    hashedLenF P20F accVF = 613496 ∧ streamLanesF P20F accVF = 76687 ∧ spongeBlocksF P20F accVF = 4512 ∧
    (scheduleF P20F accVF).length = 3534) ∧ lengthRuleF P20F accVF = true ∧
    (100 * streamLanesF P20F accVF ≤ 95 * streamCap P20F ∧ 100 * qSF P20F accVF ≤ 95 * 16384 ∧
    100 * spongeBlocksF P20F accVF ≤ 95 * 2 ^ P20F.recRowsLog) ∧
    ((readWidthsF P20F accVF).length = 8956 ∧ (readWidthsF P20F accVF).sum = 147736) := by
  decide +kernel

end Lvm
