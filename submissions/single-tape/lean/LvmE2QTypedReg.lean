-- Moved out of `LvmE2QHarF` (lvm2 U-TAPE, UT-L, 2026-11-16; text unchanged): the typed claims' static data check,
-- so that a stage's statements need not import S2GF's front gadgets.
import LvmQShapeB
import LvmTypedLayQ
import LvmFinPos

/-!
# The typed claims' static data (`typedRegB`), `PosLanes`' decision (`posLanesDec`)
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm

instance posLanesDec (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) :
    Decidable (Lvm.Fin.PosLanes p g ood Ls V k0) := by
  unfold Lvm.Fin.PosLanes; infer_instance

/-- **The typed claims' static data at S2GF**, decided in the guard: the relayout's block, the regions (`σ′`,
committed, `KS` aliases) and the mini-bus's committed columns are regular blocks, the regions at most `2^21` words,
the tables at most `mbR` and `ν` rounds, no `C_rec` column. -/
def typedRegB (T : Lvm.QTyped.TData) (sOff : ℕ) : Bool :=
  decide (Lvm.QShape.RegP ⟨19, sOff⟩) &&
    (T.sig ++ T.com ++ T.ks).all (fun R => decide (R.log ≤ 21) && decide (Lvm.QShape.RegP ⟨R.log, R.off⟩)) &&
    T.mbS.all fun s => decide (s.τ ≤ T.mbR) && decide (s.τ ≤ CMain.nu20) &&
      s.cols.all fun c => match c with
        | some (rec, off) => !rec && decide (Lvm.QShape.RegP ⟨s.τ, off⟩)
        | none => true

theorem typedRegB_sound {T : Lvm.QTyped.TData} {sOff : ℕ} (h : typedRegB T sOff = true) :
    Lvm.QShape.RegP ⟨19, sOff⟩ ∧ (∀ R ∈ T.sig ++ T.com ++ T.ks, R.log ≤ 21 ∧ Lvm.QShape.RegP ⟨R.log, R.off⟩) ∧
      ∀ s ∈ T.mbS, s.τ ≤ T.mbR ∧ s.τ ≤ CMain.nu20 ∧
        ∀ c ∈ s.cols, ∀ rec off, c = some (rec, off) → rec = false ∧ Lvm.QShape.RegP ⟨s.τ, off⟩ := by
  simp only [typedRegB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun s hs => ⟨(h3 s hs).1.1, (h3 s hs).1.2, fun c hc rec off e => ?_⟩⟩
  have := (h3 s hs).2 c hc
  rw [e] at this
  simpa using this

end Lvm.E2Q
