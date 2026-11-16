-- New for lvm2 MB-LIN (MBL-L, 2026-11-16): stage S2GL's parameters, schedule pins, sizes and format (the model
-- `variants.py` MB-LIN at occupancy 46). DAY-0 STATEMENTS: every `sorry` is tagged `-- MBL-STMT <n>`. A proof never
-- changes its statement; a needed change goes to the lead old → new.
import LvmS2GUSched

/-!
# The S2GL schedule (Lean stage `3` with `mbLin`)

* **`P20L`**: `P20U` with `mbLin`: the phase `tables` is gone (`LvmSchedule.phasesS2GL`; the schedule drops it on the
  flag alone). The mini-bus record `(busDepth, leafdecReads, tableRounds, tableEvals)` stays S2GU's `(12, 1, 6, 633)`
  as the tables' shape facts (lead decision D2: `fitsMiniB` is a conjunct of the guard, `THypCore`, the HAR's and
  V_S's facts). Every layout, window and extractor choice of stage `3` is S2GU's.
* Statements (MBL-STMT 3): `phases_P20L`, `headerBytesP_P20L`, **`sizes_P20L`** (`|π| = 268,336`, `qS = 3,642`,
  `L = 522,528`, 3,843 sponge blocks), `rwL20_pos`, `qcItems_P20L`; `fmtL20`.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The S2GL parameters**: `P20U`'s with `mbLin` (no table phase; the mini-bus record `(12, 1, 6, 633)` kept as
shape facts, D2). -/
def P20L : Params :=
  { P20U with name := "P20L", mbLin := true }

/-- **The width of the `i`-th read** at S2GL (24 past the schedule). -/
def rwL20 (i : Nat) : Nat := (readWidthsP P20L).getD i eBytes

/-- **MBL-STMT 3a** (owner L): `phases` dispatches `P20L` to `phasesS2GL` (pins the `LvmSchedule` edit). -/
theorem phases_P20L : phases P20L = phasesS2GL P20L := by
  rw [phases, ite_eq_right (show P20L.stage ≠ 1 by decide), ite_eq_right (show P20L.stage ≠ 2 by decide),
    ite_eq_left (show P20L.stage = 3 by decide), if_pos (show P20L.mbLin = true by decide)]

/-- **MBL-STMT 3b** (owner L): S2GL's header is S2GU's, 5,664 bytes. -/
theorem headerBytesP_P20L : headerBytesP P20L = 5664 ∧ seedLenP P20L = 5688 ∧ P20L.accV = Lvm.VEq.accVT := by
  decide

/-- Proof help (SLF-K; GOLF3-U's private `readWidthsP_all_ofU`, public for the S2GS twin): a read width is `eBytes` or
a `readW` item's width, so `readWidthsP`'s check is one walk of the items. -/
theorem readWidthsP_all_ofL (p : Params) (g : Nat → Bool) (he : g eBytes = true)
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
/-- Proof help (SLF-K; GOLF3-U's `schedFactsU` at `P20L`): S2GL's sizes, read widths (one walk of the items) and query
bound in one kernel evaluation of the schedule (the three decisions each rebuilt it). -/
private theorem schedFactsL : ((piSize P20L = 268336 ∧ qS P20L = 3642 ∧ hashedLen P20L = 522528 ∧
    streamLanes P20L = 65316 ∧ spongeBlocks P20L = 3843 ∧ (schedule P20L).length = 2821 ∧
    (P20L.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20L = true ∧
    (100 * streamLanes P20L ≤ 95 * streamCap P20L ∧ 100 * qS P20L ≤ 95 * 16384 ∧
      100 * spongeBlocks P20L ≤ 95 * 2 ^ P20L.recRowsLog) ∧
    (P20L.mbLin = true ∧ P20L.busDepth = 12 ∧ P20L.leafdecReads = 1 ∧ P20L.tableRounds = 6 ∧
      P20L.tableEvals = 633)) ∧
    (schedule P20L).all (fun it => match it with | .readW _ w => decide (0 < w) | _ => true) = true ∧
    (2 + qcItems P20L (schedule P20L) 0 ≤ 16384) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **MBL-STMT 3c** (owner L): **S2GL's sizes** (`variants.py` MB-LIN [exact]): `|π| = 268,336`, `qS = 3,642`,
`L = 522,528`, `T = 65,316`, 3,843 sponge blocks, 2,821 items, the root leaf of 368 B, the length rule, the 95 %
caps, `mbLin` and the mini-bus record `(12, 1, 6, 633)` (shape facts, D2). -/
theorem sizes_P20L : (piSize P20L = 268336 ∧ qS P20L = 3642 ∧ hashedLen P20L = 522528 ∧
    streamLanes P20L = 65316 ∧ spongeBlocks P20L = 3843 ∧ (schedule P20L).length = 2821 ∧
    (P20L.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20L = true ∧
    (100 * streamLanes P20L ≤ 95 * streamCap P20L ∧ 100 * qS P20L ≤ 95 * 16384 ∧
      100 * spongeBlocks P20L ≤ 95 * 2 ^ P20L.recRowsLog) ∧
    (P20L.mbLin = true ∧ P20L.busDepth = 12 ∧ P20L.leafdecReads = 1 ∧ P20L.tableRounds = 6 ∧
      P20L.tableEvals = 633) :=
  schedFactsL.1

set_option maxRecDepth 100000 in
/-- Every read width of the S2GL schedule is positive (one kernel evaluation of `readWidthsP P20L`). -/
theorem readWidthsP_pos_P20L : (readWidthsP P20L).all (fun w ↦ decide (0 < w)) = true :=
  readWidthsP_all_ofL P20L _ (by decide) schedFactsL.2.1

/-- **MBL-STMT 3d** (owner L): every read width of the S2GL schedule is positive. -/
theorem rwL20_pos : ∀ n, 0 < rwL20 n := fun n ↦ by
  unfold rwL20
  rw [List.getD_eq_getElem?_getD]
  cases h : (readWidthsP P20L)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w =>
    exact of_decide_eq_true (List.all_eq_true.mp readWidthsP_pos_P20L w (List.mem_of_getElem? h))

/-- **MBL-STMT 3e** (owner L): S2GL's query bound. -/
theorem qcItems_P20L : 2 + qcItems P20L (schedule P20L) 0 ≤ 16384 :=
  schedFactsL.2.2

/-- **S2GL's layout is S2GU's** (stage `3`; `layout0` does not read `mbLin`). -/
theorem layout0_P20L : layout0 P20L = layout0 P20U := rfl

end Lvm

namespace Lvm.CT

open Lvm Lvm.ASM

/-- **S2GL's format**: `rwL20`, `|π| = piSize P20L`, header `headerBytesP P20L`, S2GU's occupied words `occOfU`. -/
def fmtL20 : SFmt := ⟨rwL20, rwL20_pos, piSize P20L, headerBytesP P20L, occOfU⟩

end Lvm.CT
