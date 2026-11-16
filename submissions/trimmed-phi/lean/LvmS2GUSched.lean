-- New for lvm2 U-TAPE (UT-L, 2026-11-16): stage S2GU's parameters, schedule pins, sizes, layout and format (the frozen
-- `ref/utape.py` at occupancy 46). A proof never changes its statement; a needed change goes to the lead old → new.
import LvmS2GTSched
import LvmDecideV0

/-!
# The S2GU schedule (Lean stage `3`)

* **`P20U`**: `P20T` at stage `3` with `C_main`'s root leaves narrowed to 46 words (368 B, 3 permutations: the
  `KS` block is gone, the occupied words end in lane 46).
* **`phasesS2GU p`** (`LvmSchedule`): `S2GT`'s commit (with the pin), `bus` and `tables`; the merged tape `tapeU`
  (`T1` in R-BP2's B1 order, the depth-24 GKR of `Shape {21, 24}`), the wire `wireU` (the wire sumcheck, `g_D`,
  `g_Y`, `g_M`, the `D`/`Y`/`M` slot reductions); `C_main`'s opening. `KS` and the `KS` link are gone.
* **The layout** (`LvmDecideV0.layoutU`, the constants `LvmLayout.sOffU20` …): `S` 5,242,880, `X` 5,250,560, `Y`
  5,767,168, `free_lo` 5,971,968.
* Statements (UTAPE-STMT 1–5): `phases_P20U`, `headerBytesP_P20U`, **`sizes_P20U`**, `rwU20_pos`, `qcItems_P20U`;
  `layout0_P20U`; `fmtU20`.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The S2GU parameters**: `P20T`'s (A23 at 45 variables, the 16-B `acc_in` header) at stage `3`, `C_main`'s root
leaves at occupancy 46 (`ref/utape.py --occ 46`). -/
def P20U : Params :=
  { P20T with name := "P20U", stage := 3, mainLevels := withRow0 P20T.mainLevels 46 }

/-- **The width of the `i`-th read** at S2GU (24 past the schedule). -/
def rwU20 (i : Nat) : Nat := (readWidthsP P20U).getD i eBytes

/-- **UTAPE-STMT 1** (owner L): `phases` dispatches stage `3` to `phasesS2GU` (pins the `LvmSchedule` edit). -/
theorem phases_P20U : phases P20U = phasesS2GU P20U := by
  rw [phases, ite_eq_right (show P20U.stage ≠ 1 by decide), ite_eq_right (show P20U.stage ≠ 2 by decide),
    ite_eq_left (show P20U.stage = 3 by decide)]

/-- **UTAPE-STMT 2** (owner L): S2GU's header is S2GT's, 5,664 bytes (`acc_in`: 46 scalars of 16 B). -/
theorem headerBytesP_P20U : headerBytesP P20U = 5664 ∧ seedLenP P20U = 5688 ∧ P20U.accV = Lvm.VEq.accVT := by
  decide

/-- Proof help (GOLF3-U, `LvmS2GTSched`'s private `readWidthsP_all_of`): a read width is `eBytes` or a `readW` item's
width, so `readWidthsP`'s check is one walk of the items. -/
private theorem readWidthsP_all_ofU (p : Params) (g : Nat → Bool) (he : g eBytes = true)
    (h : (schedule p).all (fun it => match it with | .readW _ w => g w | _ => true) = true) :
    (readWidthsP p).all g = true := by
  rw [List.all_eq_true] at h ⊢
  intro w hw
  rw [readWidthsP] at hw
  obtain ⟨it, hit, hw⟩ := List.mem_flatMap.mp hw
  have hi := h it hit
  cases it with
  | read m => rw [List.eq_of_mem_replicate hw]; exact he
  | readW m w' => rw [List.eq_of_mem_replicate hw]; exact hi
  | cap => simp at hw
  | sample => simp at hw
  | positions => simp at hw
  | opening => simp at hw

set_option maxRecDepth 100000 in
/-- Proof help (GOLF3-U): S2GU's sizes, read widths (as one walk of the items) and query bound in one kernel evaluation
of the schedule (the three decisions each rebuilt it: 17.9 → 10.1 M heartbeats). -/
private theorem schedFactsU : ((piSize P20U = 283960 ∧ qS P20U = 3649 ∧ hashedLen P20U = 538656 ∧
    streamLanes P20U = 67332 ∧ spongeBlocks P20U = 3961 ∧ (schedule P20U).length = 2835 ∧
    (P20U.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20U = true ∧
    (100 * streamLanes P20U ≤ 95 * streamCap P20U ∧ 100 * qS P20U ≤ 95 * 16384 ∧
      100 * spongeBlocks P20U ≤ 95 * 2 ^ P20U.recRowsLog)) ∧
    (schedule P20U).all (fun it => match it with | .readW _ w => decide (0 < w) | _ => true) = true ∧
    (2 + qcItems P20U (schedule P20U) 0 ≤ 16384) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 3** (owner L): **S2GU's sizes** (`ref/utape.py --occ 46` [exact]; one kernel evaluation of the
tally): `|π| = 283,960`, `qS = 3,649`, `L = 538,656`, `T = 67,332`, 3,961 sponge blocks, 2,835 items (`utape-items.tsv` has 2,835 lines), the root leaf of
368 B, the length rule, the 95 % caps. -/
theorem sizes_P20U : (piSize P20U = 283960 ∧ qS P20U = 3649 ∧ hashedLen P20U = 538656 ∧
    streamLanes P20U = 67332 ∧ spongeBlocks P20U = 3961 ∧ (schedule P20U).length = 2835 ∧
    (P20U.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20U = true ∧
    (100 * streamLanes P20U ≤ 95 * streamCap P20U ∧ 100 * qS P20U ≤ 95 * 16384 ∧
      100 * spongeBlocks P20U ≤ 95 * 2 ^ P20U.recRowsLog) :=
  schedFactsU.1

set_option maxRecDepth 100000 in
/-- Every read width of the S2GU schedule is positive (one kernel evaluation of `readWidthsP P20U`). -/
theorem readWidthsP_pos_P20U : (readWidthsP P20U).all (fun w ↦ decide (0 < w)) = true :=
  readWidthsP_all_ofU P20U _ (by decide) schedFactsU.2.1

/-- **UTAPE-STMT 4** (owner L): every read width of the S2GU schedule is positive. -/
theorem rwU20_pos : ∀ n, 0 < rwU20 n := fun n ↦ by
  unfold rwU20
  rw [List.getD_eq_getElem?_getD]
  cases h : (readWidthsP P20U)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w =>
    exact of_decide_eq_true (List.all_eq_true.mp readWidthsP_pos_P20U w (List.mem_of_getElem? h))

set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 5** (owner L): S2GU's query bound (one kernel evaluation of the schedule's query count). -/
theorem qcItems_P20U : 2 + qcItems P20U (schedule P20U) 0 ≤ 16384 :=
  schedFactsU.2.2

/-- **S2GU's layout** (`layoutU` at `P20U`) is `LvmLayout`'s: `D` 0, `Y` (the `ks` field) 5,767,168, `Y` lane 14
5,881,856, `X` 5,250,560, `free_lo` 5,971,968, `T` 4,194,304, `S` 5,242,880. -/
theorem layout0_P20U : layout0 P20U =
    ⟨CMain.dOff20, CMain.yOffU20, CMain.yOffU20 + 14 * 2 ^ 13, CMain.xOffU20, CMain.freeLoU20, CMain.tOff20,
      CMain.sOffU20⟩ := by
  decide +kernel

end Lvm

namespace Lvm.CT

open Lvm Lvm.ASM

/-- **S2GU's occupied words**: 46 at `C_main`'s root (height 19, 64 lanes: the `KS` block is gone, the tables end in
lane 45), `occOfS` elsewhere. -/
def occOfU (ht w : ℕ) : ℕ := if ht = 19 ∧ w = 64 then 46 else occOfS ht w

/-- **S2GU's format**: `rwU20`, `|π| = piSize P20U`, header `headerBytesP P20U`, the occupied words `occOfU`. -/
def fmtU20 : SFmt := ⟨rwU20, rwU20_pos, piSize P20U, headerBytesP P20U, occOfU⟩

end Lvm.CT
