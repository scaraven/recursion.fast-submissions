-- New for `flock-recursive` (track SIB): what the compile's import and foreign flags are, read off the op
-- and whether a template took it (the closure generator's checks, `FRNodeRows4AskC.closeRows`).
import FRNodeRows4AskC
import FRVIRTplSet

/-!
# Imports and foreign flags by the op

The closure generator (`FRNodeRows4AskC.closeTG`) must know, at an op, whether the compile makes it an
import or a foreign flag, without compiling it again. Both are read off the op and the template
extension's answer, which does not depend on the template bodies:

* **`opOut_imp`**: `opOut`'s import flag is `opImp` of the op; **`opOut_foreign`**: a foreign flag only
  at a `forCap` op;
* **`tplExt4_flags`**: a template's output is neither an import nor foreign;
* **`tplExt4_isNone`**: whether a template takes an op does not depend on the template bodies;
* hence **`stepOut_imp_of`**, **`stepOut_foreign_of`**.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

theorem opOut_imp (P : Params) (cs : CS) (op : Op) : (opOut P cs op).imp = opImp op := by
  cases op <;> simp only [opOut, opImp] <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem opForeign_eq (P : Params) (cs : CS) (op : Op) : (opOut P cs op).foreign = opForeign cs op := by
  cases op
  case assertOneHot a b c =>
    simp only [opOut, opForeign]
    cases h : ((cs.slot a).isSome && (cs.slot b).isSome && (cs.slot c).isSome) <;> simp [h]
  all_goals simp only [opOut, opForeign] <;> (repeat' split) <;> first | rfl | simp_all

theorem opOut_foreign {P : Params} {cs : CS} {op : Op} (h : (opOut P cs op).foreign = true) : forCap op = true := by
  rw [opForeign_eq] at h
  cases op <;> simp_all [opForeign, forCap]

theorem tplExt_flags {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out} (h : tplExt tc P cs op = some o) :
    o.imp = false ∧ o.foreign = false := by
  unfold tplExt at h
  split at h <;> (repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact ⟨rfl, rfl⟩

theorem tplExt4_flags {F : TFilt} {R : ShR} {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out}
    (h : tplExt4 F R tc P cs op = some o) : o.imp = false ∧ o.foreign = false := by
  simp only [tplExt4, Ext.orElse, Option.orElse] at h
  split at h
  · rename_i o' h'
    cases h
    simp only [tplExt4S] at h'
    split at h'
    · split at h' <;> (try split at h') <;> simp only [Option.some.injEq, reduceCtorEq] at h' <;> subst h' <;>
        exact ⟨rfl, rfl⟩
    · split at h' <;> (try split at h') <;> simp only [Option.some.injEq, reduceCtorEq] at h' <;> subst h' <;>
        exact ⟨rfl, rfl⟩
    · simp only [tplExtF, Option.filter] at h'
      split at h' <;> (try split at h') <;> simp only [Option.some.injEq, reduceCtorEq] at h'
      subst h'; exact tplExt_flags (by assumption)
  · split at h
    · simp only [Ext.orElse, Option.orElse] at h
      split at h
      · rename_i o' h'
        cases h
        simp only [tplExtKM] at h'
        split at h' <;> (repeat' split at h') <;> simp only [Option.some.injEq, reduceCtorEq] at h' <;> subst h' <;>
          exact ⟨rfl, rfl⟩
      · simp only [extGetK] at h
        split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst h; exact ⟨rfl, rfl⟩
    · cases h

theorem tplExt_isNone (tp tp' : TKey → Tpl) (cb : TKey → ℕ → ℕ) (P : Params) (cs : CS) (op : Op) :
    (tplExt ⟨tp, cb⟩ P cs op).map (·.tin) = (tplExt ⟨tp', cb⟩ P cs op).map (·.tin) := by
  unfold tplExt
  split <;> (repeat' split) <;> rfl

theorem tplExt4_isNone (F : TFilt) (R : ShR) (tp tp' : TKey → Tpl) (cb : TKey → ℕ → ℕ) (P : Params) (cs : CS)
    (op : Op) : (tplExt4 F R ⟨tp, cb⟩ P cs op).isNone = (tplExt4 F R ⟨tp', cb⟩ P cs op).isNone := by
  have hF : (tplExtF F ⟨tp, cb⟩ P cs op).isNone = (tplExtF F ⟨tp', cb⟩ P cs op).isNone := by
    have h := tplExt_isNone tp tp' cb P cs op
    simp only [tplExtF]
    cases h1 : tplExt ⟨tp, cb⟩ P cs op <;> cases h2 : tplExt ⟨tp', cb⟩ P cs op <;> rw [h1, h2] at h <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h <;>
      simp only [Option.filter] <;> (try split) <;> (try split) <;> simp_all
  have hS : (tplExt4S F R ⟨tp, cb⟩ P cs op).isNone = (tplExt4S F R ⟨tp', cb⟩ P cs op).isNone := by
    simp only [tplExt4S]
    split
    · split <;> (try split) <;> rfl
    · split <;> (try split) <;> rfl
    · exact hF
  have hK : (tplExtKM F ⟨tp, cb⟩ P cs op).isNone = (tplExtKM F ⟨tp', cb⟩ P cs op).isNone := by
    simp only [tplExtKM]
    split <;> (repeat' split) <;> rfl
  simp only [tplExt4, Ext.orElse]
  rcases h1 : tplExt4S F R ⟨tp, cb⟩ P cs op with _ | a <;> rcases h2 : tplExt4S F R ⟨tp', cb⟩ P cs op with _ | b <;>
    rw [h1, h2] at hS <;> simp only [Option.isNone_none, Option.isNone_some, reduceCtorEq] at hS
  · simp only [Option.orElse]
    split
    · cases h3 : tplExtKM F ⟨tp, cb⟩ P cs op <;> cases h4 : tplExtKM F ⟨tp', cb⟩ P cs op <;>
        rw [h3, h4] at hK <;> simp_all [Option.orElse]
    · rfl
  · rfl

/-- **The compile's import flag**: an `opImp` op no template took. -/
theorem stepOut_imp_of {F : TFilt} {R : ShR} {tc : TCtx} {P : Params} {cs : CS} {op : Op}
    (h : (stepOut (tplExt4 F R tc) P cs op).imp = true) :
    opImp op = true ∧ tplExt4 F R tc P cs op = none := by
  simp only [stepOut] at h
  cases hx : tplExt4 F R tc P cs op with
  | none => rw [hx, Option.getD_none, opOut_imp] at h; exact ⟨h, rfl⟩
  | some o => rw [hx, Option.getD_some, (tplExt4_flags hx).1] at h; cases h

/-- **The compile's foreign flag**: a `forCap` op no template took, foreign in `opOut`. -/
theorem stepOut_foreign_of {F : TFilt} {R : ShR} {tc : TCtx} {P : Params} {cs : CS} {op : Op}
    (h : (stepOut (tplExt4 F R tc) P cs op).foreign = true) :
    (opOut P cs op).foreign = true ∧ tplExt4 F R tc P cs op = none := by
  simp only [stepOut] at h
  cases hx : tplExt4 F R tc P cs op with
  | none => rw [hx, Option.getD_none] at h; exact ⟨h, rfl⟩
  | some o => rw [hx, Option.getD_some, (tplExt4_flags hx).2] at h; cases h

end Rev4
end FR
