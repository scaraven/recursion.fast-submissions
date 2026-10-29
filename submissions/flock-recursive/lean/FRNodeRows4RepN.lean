-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).
import FRNodeRows4RepK
import FRVIRTplRepLW

/-!
# The previous node's replay templates (prototype 0)

* **`kLW`**: `linkWAll`'s kind-muxed replay (sub-template `Tpl.tplLW ν a b` on operands
  `[af a, af b]`); **`kLW_ok`**: `KOk` at every index (`Tpl.tplLW_ok`; the value is
  `linkWAll4I (nodeAt ι)`).
* **`rtLinkSegW`** (`rtLinkSegW_ok`): S-E14's segment `linkWAll` replay (`0^8`) with its output cells
  checked below the frame bound.
* **`rtN0`**: prototype 0's templates: `shiftTarget` (`rtST0`, the value `0`) and `linkWAll` (`kLW`,
  locals from `cbLW = repB`); **`rtC1 π`**: `rtN0` at prototype 0, `rtLinkSegW` at prototype 1.
* **`rtC1_ok`**: `RTOkW` at `repB` for both prototypes and every index, under `LinkZero impl₀` (S-E14)
  and `STBase base` (both `rfl` at the certificate's `implC`).

**The replay frame**: the templates read the compile's forms (cells below `repB = 2^40`, checked at
compile time) and put their locals from `repB` up; `FRNodeRows4RepW.repMapC` sends those to slot 0's
spare region.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## `linkWAll` -/

/-- Whether an op is `linkWAll`. -/
def isLW : Op → Bool
  | .linkWAll .. => true
  | _ => false

/-- `linkWAll`'s operands (`tt`, `rr`) at every index. -/
def lwArgs : Op → Kind → List ℕ
  | .linkWAll t p, _ => [t, p]
  | _, _ => []

/-- The operand types the template serves: two `AF`s. -/
def lwIn : List Ty → Bool
  | [.af _, .af _] => true
  | _ => false

/-- The sub-template at node kind `ν` (`tplLW` on two `AF`s; eight empty outputs otherwise, which
`lwIn` rejects). -/
def lwT : Op → Rev4.NodeKind → List Ty → Tpl
  | _, ν, [.af a, .af b] => tplLW ν a b
  | _, _, _ => ⟨[], List.replicate nLinkFam []⟩

/-- **`linkWAll`'s kind-muxed replay.** -/
def kLW : KOp := ⟨isLW, lwArgs, lwIn, lwT, [.af nLinkFam]⟩

theorem implP0_linkWAll {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) (tt rr : Array F) :
    (implP impl₀ base 0 ι).linkWAll ι tt rr = NI4.linkWAll4I (nodeAt ι) tt rr := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4]
  rfl

theorem linkWAll4I_size (ν : Rev4.NodeKind) (tt rr : Array F) : (NI4.linkWAll4I ν tt rr).size = nLinkFam := by
  unfold NI4.linkWAll4I; simp

/-- **`linkWAll`'s replay obligation holds at every index.** -/
theorem kLW_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kLW := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t p
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => ?_, fun inp regs vs ok ts hev hin hty => ?_⟩
  · simp only [kLW, lwT]
    split
    · rw [tplLW_outs]; rfl
    · simp [nLinkFam, Ty.len]
  · simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [implP0_linkWAll]
    simp only [kLW, lwArgs] at hty ⊢
    refine ⟨by simp [tyOf, linkWAll4I_size], fun e h1 hi hE => ?_⟩
    match ts, hin, hty with
    | [.af a, .af b], _, hty =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hty
      obtain ⟨h1t, h1p, -⟩ := hty
      obtain ⟨tt, htt⟩ : ∃ tt, rd regs t = .af tt := by
        rcases hv : rd regs t <;> simp [hv, tyOf] at h1t; exact ⟨_, rfl⟩
      obtain ⟨rr, hrr⟩ : ∃ rr, rd regs p = .af rr := by
        rcases hv : rd regs p <;> simp [hv, tyOf] at h1p; exact ⟨_, rfl⟩
      rw [htt, tyOf] at h1t; rw [hrr, tyOf] at h1p
      simp only [Option.some.injEq, Ty.af.injEq] at h1t h1p
      subst h1t h1p
      simp only [lwT] at hE ⊢
      simp only [htt, hrr, Val.toAF, List.flatMap_cons, List.flatMap_nil, List.append_nil, encV] at hi ⊢
      rw [tplLW_ok hi h1 hE]
      simp [encV]

/-! ## The segment's `linkWAll` at the second assignment -/

theorem rep_agree {B : ℕ} {w w' : Asg} (hA : Agree B w w') {t : Ty} {ls : List Lin} {v : Val}
    (h : RepS w' (some (t, ls)) v) (hl : ls.all (linLt B) = true) : RepS w (some (t, ls)) v :=
  ⟨h.1, by rw [← map_ev_agree hA hl]; exact h.2⟩

theorem forall2_agree {B : ℕ} {w w' : Asg} (hA : Agree B w w') :
    ∀ {outs : List Slot} {vs : List Val}, List.Forall₂ (RepS w') outs vs → (outF outs).all (linLt B) = true →
      List.Forall₂ (RepS w) outs vs
  | [], [], .nil, _ => .nil
  | some (t, ls) :: os, v :: vs, .cons h hs, hl => by
    rw [outF_cons, List.all_append, Bool.and_eq_true] at hl
    exact .cons (rep_agree hA h hl.1) (forall2_agree hA hs hl.2)
  | none :: os, v :: vs, .cons _ hs, hl => .cons trivial (forall2_agree hA hs hl)

/-- **S-E14's segment `linkWAll` replay** with its output cells checked below `B`. -/
def rtLinkSegW (B : ℕ) : RT :=
  ⟨isLinkW, fun P _ op outs =>
    if isLinkW op then (if (outF outs).all (linLt B) then zeroRows P outs else [rejRow P]) else []⟩

theorem rtLinkSegW_ok {impl₀ : OpImpl} (base : Rev4.NodeKind → OpImpl) (hZ : LinkZero impl₀) (B : ℕ)
    (ι : Kind) : RTOkW (implP impl₀ base 1 ι) (Xof 1) (rtLinkSegW B) ι B := by
  intro P cs op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t p
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp w w' regs vs ok hP hP' _ hA hrows hev _ => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  have hv : (implP impl₀ base 1 ι).linkWAll ι (rd regs t).toAF (rd regs p).toAF =
      Array.replicate nLinkFam 0 := by
    simp only [implP, one_ne_zero, ite_false, OpImpl.fixK, implSeg]; exact hZ _ _
  rw [hv]
  generalize (stepOut (Xof 1) P cs (.linkWAll t p)).slots = outs at hrows ⊢
  simp only [rtLinkSegW, isLinkW, ite_true] at hrows
  split_ifs at hrows with hl
  · exact forall2_agree hA (zeroRows_sound hP'.1 hrows) hl
  · exact (rej_false hP'.1 (List.mem_singleton_self _) hrows).elim

/-! ## Prototype 0's templates, and both prototypes' -/

/-- **The replay frame's bound**: every cell of a prototype's compile is below it (its frame is two
regions, `< 2^21`); the replay templates' locals are above it (`FRNodeRows4RepW.repMapC` puts them
in the spare region). -/
def repB : ℕ := 2 ^ 40

/-- `linkWAll`'s locals (the first block above the frame). -/
def cbLW : ℕ := repB

/-- **Prototype 0's replay templates**: `shiftTarget` (zero) and `linkWAll`. -/
def rtN0 : RT := (rtST0 repB).orElse (rtK kLW repB cbLW)

/-- **The replay templates per prototype**: `rtN0` at prototype 0, the segment's `linkWAll` at
prototype 1. -/
def rtC1 (π : ℕ) : RT := if π = 0 then rtN0 else if π = 1 then rtLinkSegW repB else RT.none

/-- **Every template of `rtC1` is sound** (`RTOkW` at `repB`), under `LinkZero impl₀` (S-E14) and
`STBase base`. -/
theorem rtC1_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtC1 π) ι repB := by
  by_cases h : π = 0
  · subst h
    simp only [rtC1, ite_true, rtN0]
    exact RT.orElse_okW (rtST0_ok hB repB ι) (rtK_okW repB cbLW (kLW_ok ι))
  · obtain rfl : π = 1 := by omega
    simp only [rtC1, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

/-- (+) At the certificate's `implC`, `STBase` holds by `rfl`. -/
theorem stBase_implC (fin : Finals) (lRows : List Row) (κs₀ : F) :
    STBase (fun _ => Impl.implC fin lRows κs₀) := fun _ => rfl

end N4s
end FR
