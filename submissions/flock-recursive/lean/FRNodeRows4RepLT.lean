-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).
import FRNodeRows4RepW
import FRNodeRows4RepRsK
import FRVIRTplRepL
import FRVIRTplRepT

/-!
# The previous node's `targetS` and `evalL` replays (prototype 0)

* **`kTS`**: `targetS`'s kind-muxed replay (sub-template `Tpl.tplTS ν a` on the operand `[af a]`);
  **`kTS_ok`**: `KOk` at every index (`Tpl.tplTS_ok`; the value is `targetSNode4I (nodeAt ι)`).
* **`kEvL`**: `evalL`'s kind-muxed replay (sub-template `Tpl.tplEvL ν a b` on `[af a, af b]`);
  **`kEvL_ok`** (`Tpl.tplEvL_ok`; the value is `evalL4I (nodeAt ι)`).
* **`rtN0b`**: C1's `rtN0` (`shiftTarget`, `linkWAll`) and these two, each template's locals in its
  own block of the replay frame (`cbTS`, `cbEvL`); **`rtC1b π`**: `rtN0b` at prototype 0, S-E14's
  segment `linkWAll` at prototype 1; **`rtC1b_ok`**, **`repOkW_rtC1b`**.

Both `KOp`s are keyed by the op's constructor and read the operand registers from the op itself
(no register number of a particular program).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## `targetS` -/

def isTS : Op → Bool
  | .targetS .. => true
  | _ => false

def tsArgs : Op → Kind → List ℕ
  | .targetS r, _ => [r]
  | _, _ => []

def tsIn : List Ty → Bool
  | [.af _] => true
  | _ => false

def tsTpl : Op → Rev4.NodeKind → List Ty → Tpl
  | _, ν, [.af a] => tplTS ν a
  | _, _, _ => ⟨[], List.replicate 64 []⟩

/-- **`targetS`'s kind-muxed replay.** -/
def kTS : KOp := ⟨isTS, tsArgs, tsIn, tsTpl, [.af 64]⟩

theorem implP0_targetS {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) (rr : Array F) :
    (implP impl₀ base 0 ι).targetS ι rr = NI4T.targetSNode4I (nodeAt ι) rr := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4]
  rfl

theorem kTS_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kTS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => ?_, fun inp regs vs ok ts hev hin hty => ?_⟩
  · simp only [kTS, tsTpl]
    split
    · rw [tplTS_outs]; rfl
    · simp [Ty.len]
  · simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [implP0_targetS]
    simp only [kTS, tsArgs] at hty ⊢
    refine ⟨by simp [tyOf, NI4T.targetSNode4I], fun e h1 hi hE => ?_⟩
    match ts, hin, hty with
    | [.af a], _, hty =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hty
      obtain ⟨h1t, -⟩ := hty
      obtain ⟨rr, hrr⟩ : ∃ rr, rd regs t = .af rr := by
        rcases hv : rd regs t <;> simp [hv, tyOf] at h1t; exact ⟨_, rfl⟩
      rw [hrr, tyOf] at h1t
      simp only [Option.some.injEq, Ty.af.injEq] at h1t
      subst h1t
      simp only [tsTpl] at hE ⊢
      simp only [hrr, Val.toAF, List.flatMap_cons, List.flatMap_nil, List.append_nil, encV] at hi ⊢
      exact tplTS_ok (by simpa using hi) h1 hE

/-! ## `evalL` -/

def isEvL : Op → Bool
  | .evalL .. => true
  | _ => false

def evArgs : Op → Kind → List ℕ
  | .evalL t s, _ => [t, s]
  | _, _ => []

def evIn : List Ty → Bool
  | [.af _, .af _] => true
  | _ => false

def evTpl : Op → Rev4.NodeKind → List Ty → Tpl
  | _, ν, [.af a, .af b] => tplEvL ν a b
  | _, _, _ => ⟨[], List.replicate 3 []⟩

/-- **`evalL`'s kind-muxed replay.** -/
def kEvL : KOp := ⟨isEvL, evArgs, evIn, evTpl, [.f, .f, .f]⟩

theorem implP0_evalL {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) (rL r4 : Array F) :
    (implP impl₀ base 0 ι).evalL rL r4 = NI4F.evalL4I (nodeAt ι) rL r4 := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F]

theorem kEvL_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kEvL := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t s
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => ?_, fun inp regs vs ok ts hev hin hty => ?_⟩
  · simp only [kEvL, evTpl]
    split
    · rw [tplEvL_outs]; rfl
    · simp [Ty.len]
  · simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [implP0_evalL]
    simp only [kEvL, evArgs] at hty ⊢
    refine ⟨by simp [tyOf], fun e h1 hi hE => ?_⟩
    match ts, hin, hty with
    | [.af a, .af b], _, hty =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hty
      obtain ⟨h1t, h1s, -⟩ := hty
      obtain ⟨rL, hrL⟩ : ∃ rL, rd regs t = .af rL := by
        rcases hv : rd regs t <;> simp [hv, tyOf] at h1t; exact ⟨_, rfl⟩
      obtain ⟨r4, hr4⟩ : ∃ r4, rd regs s = .af r4 := by
        rcases hv : rd regs s <;> simp [hv, tyOf] at h1s; exact ⟨_, rfl⟩
      rw [hrL, tyOf] at h1t; rw [hr4, tyOf] at h1s
      simp only [Option.some.injEq, Ty.af.injEq] at h1t h1s
      subst h1t h1s
      simp only [evTpl] at hE ⊢
      simp only [hrL, hr4, Val.toAF, List.flatMap_cons, List.flatMap_nil, List.append_nil, encV] at hi ⊢
      rw [tplEvL_ok hi h1 hE]
      simp

/-! ## Prototype 0's templates, and both prototypes' -/

/-- `targetS`'s locals (`kTS`'s instance): above `linkWAll`'s (from `repB`, 42,592) and R3's
`rsWeight` (from `cbRS = repB + 2^16`, 472,310: up to `repB + 537,846`). -/
def cbTS : ℕ := repB + (2 ^ 19 + 2 ^ 14)

/-- `evalL`'s locals, above `targetS`'s (11.8 k). -/
def cbEvL : ℕ := repB + (2 ^ 19 + 2 ^ 15)

/-- **Prototype 0's replay templates**: `shiftTarget`, `linkWAll` (C1), `targetS`, `evalL`. -/
def rtN0b : RT := rtN0.orElse ((rtK kTS repB cbTS).orElse (rtK kEvL repB cbEvL))

/-- **The replay templates per prototype.** -/
def rtC1b (π : ℕ) : RT := if π = 0 then rtN0b else if π = 1 then rtLinkSegW repB else RT.none

theorem rtC1b_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtC1b π) ι repB := by
  by_cases h : π = 0
  · subst h
    have h0 := rtC1_ok hZ hB (π := 0) (by norm_num) ι
    simp only [rtC1, ite_true] at h0
    simp only [rtC1b, ite_true, rtN0b]
    exact RT.orElse_okW h0 (RT.orElse_okW (rtK_okW repB cbTS (kTS_ok ι)) (rtK_okW repB cbEvL (kEvL_ok ι)))
  · obtain rfl : π = 1 := by omega
    simp only [rtC1b, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

/-- **`RepOkW` for `rtC1b`.** -/
theorem repOkW_rtC1b {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base) :
    RepOkW rtC1b impl₀ base := fun _ hπ ι => rtC1b_ok hZ hB hπ ι

/-- **Prototype 0's replay templates with R3's `rsWeight`** (`rtN0R`): `shiftTarget`, `linkWAll`,
`rsWeight`, `targetS`, `evalL`. -/
def rtN0c : RT := rtN0R.orElse ((rtK kTS repB cbTS).orElse (rtK kEvL repB cbEvL))

/-- **The replay templates per prototype**, all five of prototype 0. -/
def rtC1c (π : ℕ) : RT := if π = 0 then rtN0c else if π = 1 then rtLinkSegW repB else RT.none

theorem rtC1c_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtC1c π) ι repB := by
  by_cases h : π = 0
  · subst h
    have h0 := rtR3_ok hZ hB (π := 0) (by norm_num) ι
    simp only [rtR3, ite_true] at h0
    simp only [rtC1c, ite_true, rtN0c]
    exact RT.orElse_okW h0 (RT.orElse_okW (rtK_okW repB cbTS (kTS_ok ι)) (rtK_okW repB cbEvL (kEvL_ok ι)))
  · obtain rfl : π = 1 := by omega
    simp only [rtC1c, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

/-- **`RepOkW` for `rtC1c`.** -/
theorem repOkW_rtC1c {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base) :
    RepOkW rtC1c impl₀ base := fun _ hπ ι => rtC1c_ok hZ hB hπ ι

end N4s
end FR
