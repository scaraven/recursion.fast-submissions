-- New for lvm6 (WP KSA, RV4 B2): the guard Bool on the `KS` alias cells, generic in the alias parameters
-- (`Lvm6KSParams`), and its soundness lemma; on the deployed parameters `ksP18` it gives N4-cells' `KSAlias`.
import Lvm6NodeCells
import Lvm6NodeGuardB
import Lvm6SpPhase
import Lvm6Chk

/-!
# The `KS` alias cells (WP KSA)

`Q_sig` reads the node's own sponge rows through alias cells (`KSAlias`, `Lvm6NodeCells`). Their words are `KS`
words, and `Ti.ksW` sends each to a `C_main` word. The cells, their lanes and their stack words are the parameters
`ksP18 : KSParams` (`Lvm6NodeDeploy`; four families `xs`, `ys`, `ysl`, `md`), the deployed map is
`ksWOf lay = KSP.ksWOf ksP18 lay`.

* **`ksCellB Ti n t`**: cell `n` is no constant, its word is a `KS` word, and `Ti.ksW` sends that word to `t`.
* **`ksAliasPB P Ti`** (start-up, untimed): `ksCellB` on every aliased cell of every family of `P`.
  **`ksAliasPB_sound`** (generic in `P`): each such cell's memory value is `C_main`'s word at its target. The lemma
  holds for any `Ti.ksW`; the guard checks the deployed map.
* **The instance**: `ksAliasB = ksAliasPB ksP18` (`ksP18 = ksT18.params ksC18`, PFW's `KSTgt` and the cells);
  **`StackOk T`** (the targets are the stack's sponge columns `xOf`, `yOf`), `ksT18_stack`; **`ksAliasB_sound`**:
  `KSAlias (memTi Ti L pw p).k (xOf q) (yOf q)` for every stack `q` that is `C_main` on the targets. A later layout
  change edits `ksT18`/`ksC18` and re-runs `ksP18_ok` and `ksT18_stack` (both small-data).
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed LeanVM.Protocol LeanVM.Parameters
open Lvm6.Ty (TInst6)
open Lvm6.Ty.TInst6 (comCell)
open Lvm6.SP (xOf yOf)
open Lvm6.KSP (KSFam KSParams)

/-! ## The guard, generic in the parameters -/

/-- Alias cell `n` with target `t`: no constant, a `KS` word, mapped to `t`. -/
def ksCellB (Ti : TInst6) (n t : ℕ) : Bool :=
  (Ti.lay.cst? n).isNone && decide (Ti.src? (Ti.lay.wordK n) = some .ks) && decide (Ti.ksW (Ti.lay.wordK n) = t)

/-- **Every aliased cell of `P`** (lane `l`, row `r` of a family) satisfies `ksCellB` at its target. -/
def ksAliasPB (P : KSParams) (Ti : TInst6) : Bool :=
  P.fams.all fun f ↦ (List.range f.rows).all fun r ↦ (List.range f.w).all fun l ↦
    ksCellB Ti (f.c0 + f.w * r + l) (f.tgt r l)

section
variable {Ti : TInst6} (L : Lvm.M3.Lay) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec)

/-- One alias cell: its memory value is `C_main`'s word at the target. -/
theorem ksCellB_sound {n t : ℕ} (h : ksCellB Ti n t = true) :
    (memTi Ti L pw p).k n = FK.ofBF64 (comCell L p.1 p.2 false t) := by
  simp only [ksCellB, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hc, hs⟩, hw⟩ := h
  show (Ti.lay.cst? n).getD (Ti.zOf L pw p.1 p.2 (Ti.lay.wordK n)) = _
  rw [hc, Option.getD_none]
  unfold TInst6.zOf
  rw [hs, hw]

/-- **`ksAliasPB` is sound** (any parameters): every aliased cell holds `C_main`'s word at its target. -/
theorem ksAliasPB_sound {P : KSParams} (h : ksAliasPB P Ti = true) :
    ∀ f ∈ P.fams, ∀ r < f.rows, ∀ l < f.w,
      (memTi Ti L pw p).k (f.c0 + f.w * r + l) = FK.ofBF64 (comCell L p.1 p.2 false (f.tgt r l)) := by
  intro f hf r hr l hl
  simp only [ksAliasPB, List.all_eq_true, List.mem_range] at h
  exact ksCellB_sound L pw p (h f hf r hr l hl)

end

/-! ## The deployed parameters -/

/-- **The deployed guard.** -/
def ksAliasB (Ti : TInst6) : Bool := ksAliasPB ksP18 Ti

/-- **The targets are the stack's sponge columns** (`xOf`, `yOf` of `Lvm6SpPhase`): `X` lane `l`, row `i` and
`Y` lane `l`, row `x` are the stack words `xBase + l·xLane + i` and `yBase + l·yLane + x`. -/
structure StackOk (T : Lvm6.KSP.KSTgt) : Prop where
  x : ∀ (q : Stack) (i l : ℕ), xOf q i l = q (T.xBase + l * T.xLane + i)
  y : ∀ (q : Stack) (l x : ℕ), yOf q l x = q (T.yBase + l * T.yLane + x)

/-- The deployed targets are the stack's columns. -/
theorem ksT18_stack : StackOk ksT18 :=
  ⟨fun q i l ↦ congrArg q (by simp only [ksT18]; ring), fun q l x ↦ congrArg q (by simp only [ksT18]; ring)⟩

section
variable {Ti : TInst6} (L : Lvm.M3.Lay) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec)

/-- **`ksAliasB` gives N4-cells' `KSAlias`** on the stack's sponge columns (`X := xOf q`, `Yl := yOf q`), for every
stack `q` that is `C_main` on the parameters' targets. -/
theorem ksAliasB_sound (h : ksAliasB Ti = true) (q : Stack)
    (hq : ∀ f ∈ ksP18.fams, ∀ r < f.rows, ∀ l < f.w, q (f.tgt r l) = comCell L p.1 p.2 false (f.tgt r l)) :
    KSAlias (memTi Ti L pw p).k (xOf q) (yOf q) := by
  have hs := ksAliasPB_sound L pw p h
  have hS := ksT18_stack
  have mx : ksXs ∈ ksP18.fams := by simp [ksP18, Lvm6.KSP.KSTgt.params, ksXs]
  have my : ksYs ∈ ksP18.fams := by simp [ksP18, Lvm6.KSP.KSTgt.params, ksYs]
  have myl : ksYsl ∈ ksP18.fams := by simp [ksP18, Lvm6.KSP.KSTgt.params, ksYsl]
  have mm : ksMd ∈ ksP18.fams := by simp [ksP18, Lvm6.KSP.KSTgt.params, ksMd]
  refine ⟨fun r hr l hl ↦ ?_, fun r hr l hl ↦ ?_, fun r hr l hl ↦ ?_, fun l hl ↦ ?_⟩
  · have e := hs ksXs mx r hr l hl
    rw [← hq ksXs mx r hr l hl, ksXs, Lvm6.KSP.KSTgt.xFam_tgt, ← hS.x q] at e
    exact e
  · have e := hs ksYs my r hr l hl
    rw [← hq ksYs my r hr l hl, ksYs, Lvm6.KSP.KSTgt.yFam_tgt, ← hS.y q] at e
    exact e
  · have e := hs ksYsl myl r hr l hl
    rw [← hq ksYsl myl r hr l hl, ksYsl, Lvm6.KSP.KSTgt.ylFam_tgt, ← hS.y q] at e
    exact e
  · have e := hs ksMd mm 0 (by decide) l hl
    rw [← hq ksMd mm 0 (by decide) l hl, ksMd, Lvm6.KSP.KSTgt.mdFam_tgt, ← hS.y q] at e
    exact e

end

/-! ## The guard field (PFW `Chk`) -/

/-- **The `KS` alias fact** of a typed instance (PFW `Deployed.ks`): for every candidate pair's memory and every
stack `q` that is `C_main` on the targets, the alias cells hold the stack's sponge columns (`KSAlias`). -/
def KSAliasOk (Ti : TInst6) : Prop :=
  ∀ (L : Lvm.M3.Lay) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec) (q : Stack),
    (∀ f ∈ ksP18.fams, ∀ r < f.rows, ∀ l < f.w, q (f.tgt r l) = comCell L p.1 p.2 false (f.tgt r l)) →
    KSAlias (memTi Ti L pw p).k (xOf q) (yOf q)

/-- **`ksAliasB` with its statement** (one `Chk`; the guard runs `.b`). -/
def ksAliasChk (Ti : TInst6) : Chk (KSAliasOk Ti) :=
  Chk.ofBool (ksAliasB Ti) fun h L pw p q hq ↦ ksAliasB_sound L pw p h q hq

end Lvm6.Node.Dep
