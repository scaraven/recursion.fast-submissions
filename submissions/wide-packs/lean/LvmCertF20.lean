-- New for lvm2 slice S1 (E2-F, E2F-L for E2F-LEAD, 2026-11-13): statement 18's frame, the certificate of the S2GF
-- submission at `P20F`; moved to the coordinate-split typed phase (`THypX`, `GoodTF`) by E2F-L2.
import LvmE2FCert
import LvmE2VMidSpec
import LvmScheduleF
import LvmCertM20

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmCertF20InstOff`, outside its import closure.)

/-!
# S2GF's certificate frame (statement 18)

The S2GF verifier runs the root pin, then the middle phases `midM reloc20 (midF₂ Ti)` (V's `midF₂` on the typed
instance `Ti`, S2GF's `TiF20`; roll 11's relocation onto `C_main`'s stream block), then `C_main`'s opening, at S2GF's
format `fmtF20` (read widths `rwF20`: 8-B nonces, 16-B `E2` scalars, 24-B `E` scalars; `|π| = 306,992`; header
`headerF 44`). The certificate is M′'s (`OpenSMW` through `openSFW`) at `schemeSW fmtF20`. The middle phases are
closed here for every `Ti` with `THypX Ti`: the good relation `GoodFM` (V's `GoodTF`), the lead
`leadF20 = 6·2^-131` (`leadP_six`), `MidSpecPin` by `midSpecPin_of` from V's `midSpecP_F₂` and `retOK_midF₂_len`, the
shape from V's `cg_midF₂`. What remains is `OpenF20`: the child and its node soundness, the refinement, and the
executable extractor's agreement (`ext_eq`, `ext_eqF20`'s statement). The frame is generic in the verifier `VS`.

* proved: **`rwF20_pos`**, **`sizes_P20F`**, `fmtF20`, `midShapeF₂`, `midSpecPinF20`, **`openF20`**,
  **`certificateF20`**, and the extractor-generic **`certificateR_openW`**.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The sizes and the format -/

set_option maxRecDepth 100000 in
/-- Every read width of the S2GF schedule is positive (one kernel evaluation of `readWidthsF P20F accVF`). -/
theorem readWidthsF_pos : (readWidthsF P20F accVF).all (fun w ↦ decide (0 < w)) = true := by
  decide +kernel

/-- **S2GF's read widths are positive** (`SFmt`'s only fact about them). -/
theorem rwF20_pos : ∀ n, 0 < rwF20 n := fun n ↦ by
  unfold rwF20
  rw [List.getD_eq_getElem?_getD]
  cases h : (readWidthsF P20F accVF)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w =>
    exact of_decide_eq_true (List.all_eq_true.mp readWidthsF_pos w (List.mem_of_getElem? h))

/-- **S2GF's format**: `rwF20`, `|π| = piSizeF P20F accVF`, header `headerF accVF` (`accV = 44`), M′'s occupied
words (`occOfS`: the layout is M′'s). -/
def fmtF20 : SFmt := ⟨rwF20, rwF20_pos, piSizeF P20F accVF, headerF accVF, occOfS⟩

/-! ## The middle phases at S2GF (the coordinate-split typed phase) -/

/-- The middle phases' lead at S2GF (V's `leadF₂`). -/
noncomputable abbrev leadF20 : ℝ≥0∞ := 6 * (2 : ℝ≥0∞)⁻¹ ^ 131

/-- **S2GF's good relation on `C_main` candidates**: V's `GoodTF Ti H` (`GbTX ∧ GkF`) on the viewed pair, the
stream block relocated by `recOf20`. -/
def GoodFM (Ti : TInst) (H : THypX Ti) : GoodRelM := GoodOfM recOf20 (Lvm.Shape.Good₂ (GoodTF Ti H))

/-- The middle phases commit nothing and grind nothing (V's `cg_midF₂`). -/
theorem midShapeF₂ (Ti : TInst) : MidShapeM (midM reloc20 (midF₂ Ti)) := midShapeM_of (cg_midF₂ Ti)

/-- **The middle phases' obligation at S2GF** from V's pinned pair form `midSpecP_F₂` at the lead `leadF20` and
V's claim count `retOK_midF₂_len`. -/
theorem midSpecPinF20 (Ti : TInst) (H : THypX Ti) :
    MidSpecPin (midM reloc20 (midF₂ Ti)) (GoodFM Ti H) εS leadF20 :=
  midSpecPin_of relocLaw20 (midSpecP_F₂ Ti H recOf20) (retOK_midF₂_len Ti H)

/-! ## The open obligations -/

/-! ## The certificate -/

/-- **An executable extractor**: the program, its specification, and the contract's facts on them. -/
structure ExtF20 where
  E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit
  ext : XProg
  computes : Computes ext E Lvm.X.fuel
  size : ext.body.size ≤ progCap
  W : ∀ c π L, isS π = false → E c π L = RecursionFast.WitnessSending.decode π

/-- **The certificate from the open obligations at a format, any executable extractor** (as
`certificateR_openVMW`, the extractor a parameter). -/
theorem certificateR_openW (f : SFmt) (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (X : ExtF20) (o : OpenSMW f VS X.E) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS X.E X.ext) :=
  certificateR_claim VS _ X.ext
    ⟨fun H vk c π _ ↦ hq H vk c π, X.computes, X.size, X.W, sSound_of_openSMW f o⟩

end Lvm.CT
