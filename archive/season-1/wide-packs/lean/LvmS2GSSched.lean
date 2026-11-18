-- New for lvm2 σ_LEAF (SLF-L, 2026-11-16): stage S2GS's parameters, schedule pins, sizes and format (the model
-- `g0b.py` "S2GL + sigma_leaf out"). DAY-0 STATEMENTS: every `sorry` is tagged `-- SLF-STMT <n>`. A proof never
-- changes its statement; a needed change goes to the lead old → new.
import LvmS2GUSched
import LvmS2GLSched

/-!
# The S2GS schedule (Lean stage `3` with `mbLin` and `leafOut`)

* **`P20S`**: `P20U` with `mbLin` and `leafOut` (S2GL's parameters with `leafOut`; built on `P20U` so that the S2GS
  closure holds no S2GL module, the kernel budget): the `S` header loses `σ_leaf` (`'S' pad[7] | b | vk | c_L | s | n | h | acc_in`,
  `hdrFixS + 16·(accV + 1)` = 888 B; `LvmParams.headerBytesP` selects it on the flag alone, inside its stage-`≥ 2`
  branch, so every other stage's header is unchanged). The phases are S2GL's (`phasesS2GL`: the flag does not enter the
  schedule); every layout, window and extractor choice of stage `3` is S2GU's.
* Statements (SLF-STMT 1): `phases_P20S`, `headerBytesP_P20S`, **`sizes_P20S`** (`|π| = 263,560`, `qS = 3,642`,
  `L = 517,752`, 3,808 sponge blocks), `rwS20_pos`, `qcItems_P20S`; `fmtS20`. Checked once at 4f5c3fbd (not kept, to
  stay off S2GL's modules): S2GS's schedule and read widths are S2GL's, `|π|` and `L` are 4,776 B below S2GL's.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The S2GS parameters**: `P20U`'s with `mbLin` (S2GL's: no table phase) and `leafOut` (the header carries no
`σ_leaf`). -/
def P20S : Params :=
  { P20U with name := "P20S", mbLin := true, leafOut := true }

/-- **The width of the `i`-th read** at S2GS (24 past the schedule). -/
def rwS20 (i : Nat) : Nat := (readWidthsP P20S).getD i eBytes

/-- **SLF-STMT 1a** (owner L): `phases` dispatches `P20S` to `phasesS2GL` (S2GL's phases). -/
theorem phases_P20S : phases P20S = phasesS2GL P20S := by
  rw [phases, ite_eq_right (show P20S.stage ≠ 1 by decide), ite_eq_right (show P20S.stage ≠ 2 by decide),
    ite_eq_left (show P20S.stage = 3 by decide), if_pos (show P20S.mbLin = true by decide)]

/-- **SLF-STMT 1b** (owner L): S2GS's header is 888 bytes (S2GU's and S2GL's 5,664 less `σ_leaf`'s 4,776), the seed
912. -/
theorem headerBytesP_P20S : headerBytesP P20S = 888 ∧ seedLenP P20S = 912 ∧ P20S.accV = Lvm.VEq.accVT ∧
    headerBytesP P20S + sigBytes = headerBytesP P20U := by
  decide

set_option maxRecDepth 100000 in
/-- Proof help (SLF-K2; `schedFactsL`'s twin at `P20S`): S2GS's sizes, read widths (one walk of the items,
`readWidthsP_all_ofL`) and query bound in one kernel evaluation of the schedule. -/
private theorem schedFactsS : ((piSize P20S = 284872 ∧ qS P20S = 3618 ∧ hashedLen P20S = 537336 ∧
    streamLanes P20S = 67167 ∧ spongeBlocks P20S = 3952 ∧ (schedule P20S).length = 2749 ∧
    (P20S.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20S = true ∧
    (100 * streamLanes P20S ≤ 95 * streamCap P20S ∧ 100 * qS P20S ≤ 95 * 16384 ∧
      100 * spongeBlocks P20S ≤ 95 * 2 ^ P20S.recRowsLog) ∧
    (P20S.mbLin = true ∧ P20S.leafOut = true ∧ P20S.busDepth = 12 ∧ P20S.leafdecReads = 1 ∧
      P20S.tableRounds = 6 ∧ P20S.tableEvals = 633)) ∧
    (schedule P20S).all (fun it => match it with | .readW _ w => decide (0 < w) | _ => true) = true ∧
    (2 + qcItems P20S (schedule P20S) 0 ≤ 16384) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **SLF-STMT 1c** (owner L): **S2GS's sizes** (W32 K = 32, [exact] by decide; lead D5): `|π| = 284,872`,
`qS = 3,618`, `L = 537,336`, `T = 67,167`, 3,952 sponge blocks, 2,749 items, the root leaf of 368 B, the length rule,
the 95 % caps, `mbLin`, `leafOut` and the mini-bus record `(12, 1, 6, 633)` (shape facts, as S2GL). -/
theorem sizes_P20S : (piSize P20S = 284872 ∧ qS P20S = 3618 ∧ hashedLen P20S = 537336 ∧
    streamLanes P20S = 67167 ∧ spongeBlocks P20S = 3952 ∧ (schedule P20S).length = 2749 ∧
    (P20S.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20S = true ∧
    (100 * streamLanes P20S ≤ 95 * streamCap P20S ∧ 100 * qS P20S ≤ 95 * 16384 ∧
      100 * spongeBlocks P20S ≤ 95 * 2 ^ P20S.recRowsLog) ∧
    (P20S.mbLin = true ∧ P20S.leafOut = true ∧ P20S.busDepth = 12 ∧ P20S.leafdecReads = 1 ∧
      P20S.tableRounds = 6 ∧ P20S.tableEvals = 633) :=
  schedFactsS.1

set_option maxRecDepth 100000 in
/-- Every read width of the S2GS schedule is positive (one walk of the schedule's items, `schedFactsS`). -/
theorem readWidthsP_pos_P20S : (readWidthsP P20S).all (fun w ↦ decide (0 < w)) = true :=
  readWidthsP_all_ofL P20S _ (by decide) schedFactsS.2.1

/-- **SLF-STMT 1d** (owner L): every read width of the S2GS schedule is positive. -/
theorem rwS20_pos : ∀ n, 0 < rwS20 n := fun n ↦ by
  unfold rwS20
  rw [List.getD_eq_getElem?_getD]
  cases h : (readWidthsP P20S)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w =>
    exact of_decide_eq_true (List.all_eq_true.mp readWidthsP_pos_P20S w (List.mem_of_getElem? h))

set_option maxRecDepth 100000 in
/-- **SLF-STMT 1e** (owner L): S2GS's query bound. -/
theorem qcItems_P20S : 2 + qcItems P20S (schedule P20S) 0 ≤ 16384 :=
  schedFactsS.2.2

/-- **S2GS's layout is S2GU's** (stage `3`; `layout0` reads neither `mbLin` nor `leafOut`). -/
theorem layout0_P20S : layout0 P20S = layout0 P20U := rfl

end Lvm

namespace Lvm.CT

open Lvm Lvm.ASM

/-- **S2GS's format**: `rwS20`, `|π| = piSize P20S`, header `headerBytesP P20S`, S2GU's occupied words `occOfU`. -/
def fmtS20 : SFmt := ⟨rwS20, rwS20_pos, piSize P20S, headerBytesP P20S, occOfU⟩

end Lvm.CT
