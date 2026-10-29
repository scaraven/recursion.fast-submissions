-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4d): controls.
import FRSoundness4R4FrE
import FRSoundness4R4FinCtrl
import FRVIRFinalsSF

/-!
# Controls for `relE4`, `relSh4`, `relRS4` and R4d's definitions

* (+) **At 3.x's parameters the relocated relations are 3.x's** (`relE4_fin3P`, `relSh4_fin3P`,
  `relRS4_fin3P`), as R4c's `relZ4_fin3P` …
* (−) **The flags reject**: E4 end's value register holding another value (`relE4_rejects`, every
  kind), S2's first claim register holding no F value (`relSh4_rejects`), a leaf with a nonzero
  fourth slice (`relRS4_rejects`).
* (+/−) `baseAt`: the base of field `1` is past field `0`'s outputs, not the start
  (`baseAt_ctl`), and `exAt` pushes field `0`'s outputs (its third part).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section Ctrl
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- (+) `relE4` at `fin3P` is 3.x's `relE`. -/
theorem relE4_fin3P : relE4 impl κ inp fi r fin3P = relE impl κ inp fi r := by
  have ho : gOE4end seq3 = oE4end := by rw [gOE4end, phaseOffOf_seq3]; rfl
  have hab : fieldOffOf seq3 fE + (oE4end + 16) = absOff fE (oE4end + 16) := by
    rw [← absOff_seq3 (show fE < 19 by decide), absOff_zero]
  simp only [relE4, relE, show fin3P.S = seq3 from rfl, ho, hab,
    pe4_seq3 inp (show fEEnd < 19 by decide), pe4_seq3 inp (show fE < 19 by decide)]
  rfl

/-- (+) `relSh4` at `fin3P` is 3.x's `relSh`. -/
theorem relSh4_fin3P : relSh4 impl κ inp fi r fin3P = relSh impl κ inp fi r := by
  simp only [relSh4, relSh, show fin3P.S = seq3 from rfl, pe4_seq3 inp (show fHdr < 19 by decide),
    pe4_seq3 inp (show fStmt < 19 by decide)]
  rw [seq3_eq]; rfl

/-- (+) `relRS4` at `fin3P` is 3.x's `relRS`. -/
theorem relRS4_fin3P : relRS4 κ inp fin3P = relRS κ inp := by
  have h : fieldOffOf seq3 fRS0 + rsOff 3 0 = absOff fRS0 (rsOff 3 0) := by
    rw [← absOff_seq3 (show fRS0 < 19 by decide), absOff_zero]
  simp only [relRS4, relRS, rsLeafZero4, rsLeafZero, show fin3P.S = seq3 from rfl, h]
  rfl

/-- (−) **`relE4` rejects a wrong E4-end value** (every kind): if `zhat`'s claim-4 register holds
anything but E4 end's first element, the flag is `false`. -/
theorem relE4_rejects (P : FinP) {v : F} (hv : rd r (fi.zhat.getD 3 0) = .f v)
    (hne : v ≠ pe4 P.S inp fE (gOE4end P.S)) : relE4 impl κ inp fi r P = false := by
  have he : (Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd r (fi.zhat.getD 3 0)) = false := by
    rw [hv]; simp [Val.eqv, Ne.symm hne]
  by_cases hn : P.kv.node κ <;>
    simp only [relE4, hn, he, ite_true, ite_false, Bool.false_eq_true, Bool.false_and, Bool.and_false]

/-- (−) **`relSh4` rejects an S2 first-claim register without an F value** (`shiftTarget`'s value
is asserted against it). -/
theorem relSh4_rejects (P : FinP) (hv : ∀ t : F, rd r (claim0 fi "S2") ≠ .f t) :
    relSh4 impl κ inp fi r P = false := by
  simp only [relSh4, Bool.and_eq_false_iff]
  exact .inl (Bool.eq_false_iff.2 fun h => hv _ (val_eqv_f4 h))

/-- (−) **`relRS4` rejects a leaf whose fourth claim's slices are not zero.** -/
theorem relRS4_rejects (P : FinP) (hn : P.kv.node κ = false) (hz : rsLeafZero4 P.S inp = false) :
    relRS4 κ inp P = false := by
  simp [relRS4, hn, hz]

end Ctrl

/-- (+/−) **The fold's bases**: field `1` runs past field `0`'s outputs (`b + opsOut …`), not at
`b`; `exAt` pushes field `0`'s output list. -/
theorem baseAt_ctl (outs : Array (List Reg)) (zh : List Reg) (b : ℕ) :
    baseAt outs zh [fun _ b => ([.const (fun _ => .f 0)], [b]), fun _ _ => ([], [])] b #[] 1 = b + 1 ∧
      baseAt outs zh [fun _ b => ([.const (fun _ => .f 0)], [b]), fun _ _ => ([], [])] b #[] 1 ≠ b ∧
      exAt outs zh [fun _ b => ([.const (fun _ => .f 0)], [b]), fun _ _ => ([], [])] b #[] 1 = #[[b]] := by
  refine ⟨rfl, ?_, rfl⟩
  show b + 1 ≠ b; omega

end FR.Snd.R4
