-- New for lvm2 S2GT (GT-L, 2026-11-15): the frozen statements (S2GT-STMT 1–5) of stage S2GT's schedule, header, sizes
-- and format (the frozen `ref/s2gt.py` with amendments 1–2, lead decisions D1–D4). A proof never changes its statement;
-- a needed change goes to the lead old → new.
import LvmScheduleF
import LvmSubmissionS
import LvmE2VPub
import LvmCertF20

/-!
# The S2GT schedule

* **`phasesS2GT p`**: S2GF's phases (`phasesS2GF`) with the phase `bus` at `E2` (`busT p`): the separator, `τ` (20
  ground challenges), `ω` (one), the zerocheck (20 rounds of 2 `E2` scalars), the 9 values, `γ`, the wiring (21
  rounds), 12 matrix and 4 region values, the relayout (19 rounds), `v_R`, `κ` (4 ground challenges), `h`
  (`accV + 1` `E2` scalars), `t`, the zero scalar; then the mini-bus at `E3` as S2GF (S2GT AMENDMENT 1). Every
  other phase (commit with the pin, tables, tape, wire, `KS`, `KS` link, the opening) is S2GF's, item for item.
* **`P20T`** (`P20G` is taken: PI-GRIND's record): `P20` at stage `2`, `accV = accVT = 45`.
* Statements (owner L): `phases_P20T` (the stage-2 dispatch in `LvmSchedule.phases`), `headerBytesP_P20T` (the
  16-B `acc_in` header, 5,664 B), **`sizes_P20T`**, `rwG20_pos`, `qcItems_P20T`; `fmtG20`.

Lead decisions (S2GT freeze): D1 occupancy 47 (`P20T` inherits `P20`'s levels; |π| 305,992 = `s2gt.py --occ 47`);
D2 the stage-2 dispatch (`LvmSchedule.phases`, `busT`/`phasesS2GT` there) and the 16-B header (`LvmParams.headerBytesP`:
`hdrFix + 16·(accV + 1)` at stage `2`; `seedLenP p = 32 + headerBytesP p − 8`), the generic header lemmas restated on
the fixed part or off stage `2`; D3 the name `P20T` (`P20G` is PI-GRIND's record); D4 `VSGX` through `parseOk`/`drive`
at `P20T` (`Params.withF` sets `stage := 1`).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The S2GT parameters**: `P20`'s at stage `2`, A23 at 45 variables (`Φ_Q` on `4 + 20 + 21`). -/
def P20T : Params := { P20 with name := "P20T", stage := 2, accV := Lvm.VEq.accVT }

/-- The byte width of each scalar read of a schedule, in order (`readWidthsF`'s generalisation:
`readWidthsF p accV = readWidthsP (p.withF accV)` by `rfl`). -/
def readWidthsP (p : Params) : List Nat :=
  (schedule p).flatMap fun
    | .read m => List.replicate m eBytes
    | .readW m w => List.replicate m w
    | _ => []

/-- **The width of the `i`-th read** at S2GT (24 past the schedule). -/
def rwG20 (i : Nat) : Nat := (readWidthsP P20T).getD i eBytes

/-- **S2GT-STMT 1** (owner L): `phases` dispatches stage `2` to `phasesS2GT` (pins the `LvmSchedule` edit). -/
theorem phases_P20T : phases P20T = phasesS2GT P20T := by
  rw [phases, ite_eq_right (show P20T.stage ≠ 1 by decide), ite_eq_left (show P20T.stage = 2 by decide)]

/-- **S2GT-STMT 2** (owner L): S2GT's header is 5,664 bytes (`acc_in`: 46 scalars of 16 B; pins the `LvmParams`
edit). -/
theorem headerBytesP_P20T : headerBytesP P20T = 5664 ∧ seedLenP P20T = 5688 := by
  decide

set_option maxRecDepth 100000 in
/-- **S2GT-STMT 3** (owner L): **S2GT's sizes** (`s2gt.py` at occupancy 47 [model]; one kernel evaluation of the
tally): `|π| = 305,992`, `qS = 3,961`, `L = 583,152`, `T = 72,894`, 4,288 sponge blocks, 3,728 items, the length rule,
the 95 % caps. -/
theorem sizes_P20T : (piSize P20T = 305992 ∧ qS P20T = 3961 ∧ hashedLen P20T = 583152 ∧
    streamLanes P20T = 72894 ∧ spongeBlocks P20T = 4288 ∧ (schedule P20T).length = 3728) ∧
    lengthRule P20T = true ∧
    (100 * streamLanes P20T ≤ 95 * streamCap P20T ∧ 100 * qS P20T ≤ 95 * 16384 ∧
      100 * spongeBlocks P20T ≤ 95 * 2 ^ P20T.recRowsLog) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every read width of the S2GT schedule is positive (one kernel evaluation of `readWidthsP P20T`). -/
theorem readWidthsP_pos_P20T : (readWidthsP P20T).all (fun w ↦ decide (0 < w)) = true := by
  decide +kernel

/-- **S2GT-STMT 4** (owner L): every read width of the S2GT schedule is positive. -/
theorem rwG20_pos : ∀ n, 0 < rwG20 n := fun n ↦ by
  unfold rwG20
  rw [List.getD_eq_getElem?_getD]
  cases h : (readWidthsP P20T)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w =>
    exact of_decide_eq_true (List.all_eq_true.mp readWidthsP_pos_P20T w (List.mem_of_getElem? h))

set_option maxRecDepth 100000 in
/-- **S2GT-STMT 5** (owner L): S2GT's query bound (one kernel evaluation of the schedule's query count). -/
theorem qcItems_P20T : 2 + qcItems P20T (schedule P20T) 0 ≤ 16384 := by
  decide +kernel

end Lvm

namespace Lvm.CT

open Lvm Lvm.ASM

/-- **S2GT's format**: `rwG20`, `|π| = piSize P20T`, header `headerBytesP P20T`, M′'s occupied words (`occOfS`:
47 at the root, see the design note). -/
def fmtG20 : SFmt := ⟨rwG20, rwG20_pos, piSize P20T, headerBytesP P20T, occOfS⟩

end Lvm.CT
