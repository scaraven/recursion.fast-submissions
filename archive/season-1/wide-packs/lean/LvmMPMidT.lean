-- New for lvm2 roll 11 (M′, R11-I): the typed backend's middle phases at M′ (`midM reloc (midT₂ Ti)`):
-- `MidSpecM` and `MidShapeM` from the existing phase specs re-instantiated at the one-root candidate pairs
-- (`LvmMPMid.candRelM`). The relocation's laws stay hypotheses (`RelocLaw`, the lead's from R11-E's layout).
import LvmMPMid
import LvmTypedSpec

-- (GOLF2: 16 declarations that `certified` does not use moved verbatim to `LvmMPMidTOff`, outside its import closure.)

/-!
# The typed middle phases at M′

`midSpecR_T₂`'s proof (`LvmTypedSpec`) with the candidate set `candPairs` (two roots) replaced by
`candRelM recOf x` (`C_main`'s candidates with their `C_rec` column `recOf x q`) and `RootShape` by
`RootShapeM`:

* **`specBusTM`**: `typedSpecR` at `imgCM recOf x` (the viewed one-root pairs), as `specBusT₂`;
  **`specKgSM`**: `kgSpecS` at `candRelM recOf x`, as `LvmShape.specKgS₂`;
* **`midSpecP_T₂`**: `midSpecOfRelG` with `linkT₂`/`sideT₂` unchanged;
* **`retOK_midT₂_len`**: at most `2^40` claims in all (the typed phases `≤ 2^39 + 4`, V_S phases 4–7 `≤ 41`);
* **`midSpecM_T₂`**, **`midShapeM_T₂`**, **`kcertTM`** (`kcertSM` at `GoodTM`).

The error terms are those of `THyp.errs`/`kg_errsJ2` at `L₀ = 37,696`: the one-root pairs number at most
`124 ≤ 37,696` (`candidates_main23Jq_ncard_le`), so no new arithmetic is needed (`εS`, lead `εS`).
-/

set_option autoImplicit false

namespace Lvm.Typed

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal

/-! ## One root -/

theorem rootShapeM_append {h₀ l : List Ev} (hl : commits l = []) (hr : RootShapeM h₀) :
    RootShapeM (h₀ ++ l) := by
  obtain ⟨W, hc, hw⟩ := hr
  exact ⟨W, by rw [commits_append, hl, List.append_nil, hc], hw⟩

theorem rootShapeM_one {h : List Ev} (hr : RootShapeM h) : 1 ≤ (commits h).length := by
  obtain ⟨W, hc, -⟩ := hr; rw [hc]; simp

theorem rootShapeM_firstWord {h : List Ev} (hr : RootShapeM h) : ∃ W, firstWord h = some W := by
  obtain ⟨W, hc, -⟩ := hr
  exact ⟨W, by simp [firstWord, hc]⟩

theorem candM_append (h₀ l : List Ev) (h1 : 1 ≤ (commits h₀).length) : candM (h₀ ++ l) = candM h₀ := by
  simp only [candM, Lvm.M3.wordOf_commits_append h₀ l (show 0 < (commits h₀).length by omega)]

theorem candM_stable : Stable candM := fun h₀ l hl ↦ by
  simp only [candM, commits_append, hl, List.append_nil]

/-- `C_main`'s root candidates are at most `124`. -/
theorem candM_ncard_le (h : List Ev) : (candM h).ncard ≤ 124 :=
  candidates_main23Jq_ncard_le _

section Img

variable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8)

variable {recOf x}

end Img

/-! ## The phases at the one-root pairs -/

variable {Ti : TInst}

/-! ## The claims' count -/

/-! ## A relocation through the shape's view (optional) -/

/-- The `C_rec` column read from the view (`view x q`, the big-layout column) by a big-layout reader `recB`. -/
def recOfV (recB : Column CMain.nu20 → Column 19) (x : List UInt8) (q : Column CMain.nu20) : Column 19 :=
  recB (view x q)

/-- A big-layout relocation `relocB`, then `onStackZ` in the small shape (as `onStackZs`). -/
def relocV (relocB : LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim)
    (x : List UInt8) (c : LeanVM.Protocol.Verifier.StackClaim) : LeanVM.Protocol.Verifier.StackClaim :=
  if Lvm.Shape.small x then Lvm.Shape.onStackZ (relocB c) else relocB c

/-- **The laws through the view** from the big layout's (`holds_onStackZ`, `isMultiaffine_onStackZ`): the lead
then states the relocation once, on the big layout. -/
theorem relocLaw_view {recB : Column CMain.nu20 → Column 19}
    {relocB : LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}
    (hh : ∀ c q, IsMultiaffine 19 c.1 →
      StackClaim.Holds CMain.nu20 (relocB c) q → StackClaim.Holds 19 c (recB q))
    (ha : ∀ c, IsMultiaffine 19 c.1 → IsMultiaffine CMain.nu20 (relocB c).1) :
    RelocLaw (recOfV recB) (relocV relocB) where
  holds x c q hc h := by
    unfold recOfV relocV view at *
    by_cases hs : Lvm.Shape.small x = true
    · simp only [hs, ite_true] at h ⊢
      exact hh c _ hc ((Lvm.Shape.holds_onStackZ _ q).mp h)
    · simp only [hs, Bool.false_eq_true, ite_false] at h ⊢
      exact hh c q hc h
  affine x c hc := by
    unfold relocV
    split_ifs
    · exact Lvm.Shape.isMultiaffine_onStackZ (ha c hc)
    · exact ha c hc

/-! ## At M′ -/

end Lvm.Typed
