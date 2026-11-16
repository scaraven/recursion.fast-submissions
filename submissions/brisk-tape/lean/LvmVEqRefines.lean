-- New for lvm (WP-14a): obligation O5b, WP-14's `OpenS.refines`, for the frozen V_S at P20. lvm2 roll 8 (B1, wave L,
-- L-C): roll 7's `refines_VSL` (the bus `VSL`) is gone with the refreeze `S2GB1` (its schedule is the typed one); the
-- typed O5b is `LvmTypedVEqTop.refines_VST`. The small layout's fit `colsRegB` stays (the bus guard's).
import LvmVEqMain
import LvmVEqFolPS
import LvmQShapeF

/-!
# O5b: V_S ⇒ S.V

Roll 7's **`refines_VSL`** (`VSL P20 tabs` ⇒ `PSWith (midS₂ tabs)`) is gone at B1: the schedule is the typed one,
so the bus `P_S` no longer follows it. The typed O5b is `LvmTypedVEqTop.refines_VST`.

**`colsRegB`** (roll 7, CR-X): **the small layout's fit**. Every committed `C_main` column of every
table is a regular block, `Lvm.QShape.RegP ⟨τ, off⟩`: at most `2^20` words, aligned, in
`[4·2^20, 11·2^20)`. `RegP` is the block predicate Q_arith's static guard applies to every regular claim
(`ZWF`, inside `staticOkB`; `D`'s and the tape's ring claim are muxed instead); `colsRegB` asks it of
every committed `C_main` column (the guard's table claims are blocks of the sumcheck tables' columns,
a subset; not proved here). V_S's tail-0 argument needs only
its consequence `colsHiB` (`colsHiB_of_reg`).
-/

set_option autoImplicit false

namespace Lvm.M3

/-- **The small layout's fit** (roll 7): every committed `C_main` column is a regular block (`RegP`: at
most `2^20` words, aligned, in `[4·2^20, 11·2^20)`), the block predicate Q_arith's guard applies to
every regular claim (`Lvm.QShape.ZWF`). -/
def colsRegB (tabs : List Tab) : Bool :=
  tabs.all fun t => t.cols.all fun c => match c with
    | .com rec off => rec || decide (Lvm.QShape.RegP ⟨t.τ, off⟩)
    | .fix _ _ => true

/-- `colsRegB` gives V_S's `colsHiB` (from word `2^22` on, at most `2^22` words). -/
theorem colsHiB_of_reg {tabs : List Tab} (h : colsRegB tabs = true) : colsHiB tabs = true := by
  unfold colsRegB at h
  unfold colsHiB
  simp only [List.all_eq_true] at h ⊢
  intro t ht c hc
  have h' := h t ht c hc
  cases c with
  | fix _ _ => rfl
  | com rec off =>
    cases rec with
    | true => rfl
    | false =>
      have hr : Lvm.QShape.RegP ⟨t.τ, off⟩ := by simpa using h'
      obtain ⟨h1, -, h3, -⟩ := hr
      simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨le_trans (by norm_num) h3, le_trans h1 (by norm_num)⟩

end Lvm.M3

