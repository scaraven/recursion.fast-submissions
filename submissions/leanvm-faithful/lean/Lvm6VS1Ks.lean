-- New for lvm6 (VS1): the sponge link's shift sum with the row-independent work hoisted (`contShiftH`), and the
-- fast sponge phase over it (`fSpongePhase6H = fSpongePhase6`).
import Lvm6VTwC

/-!
# VS1: the sponge link's shift sum, hoisted

`contShiftFast rows ρ ρ'` reads `eq(ρ, i)` and `eq(ρ', i - 1)` for each of SPH's 4,063 rows through `eqSp`, which
recomputes `ρ.length` (a list walk) and `2 ^ ρ.length` (GMP's `lean_nat_pow`) per row and per point. Here
`contShiftH` computes both once per call and passes them to `eqSpH`, and the sum is a left fold rather than a sum
of a mapped list.

* `eqSpH ρ ok N lo hi i` (`eqSpH_eq`: at `ok = decide (6 ≤ ρ.length)`, `N = 2 ^ ρ.length` it is `eqSp`);
* **`contShiftH`**, **`contShiftH_eq : contShiftH = contShiftFast`**;
* **`fKsLinkH`** (`= fKsLink`), **`fSpongePhase6H`**, **`fSpongePhase6H_eq : fSpongePhase6H = fSpongePhase6`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V

section Gen

variable {F : Type} [Field F] [Algebra K F]

/-- `eqSp` with the guard's length test and bound precomputed. -/
def eqSpH (ρ : List F) (ok : Bool) (N : ℕ) (lo hi : Array F) (i : ℕ) : F :=
  if ok && decide (i < N) then lo.getD (i % 64) 0 * hi.getD (i / 64) 0 else eqAtF ρ i

omit [Algebra K F] in
theorem eqSpH_eq (ρ : List F) (lo hi : Array F) (i : ℕ) :
    eqSpH ρ (decide (6 ≤ ρ.length)) (2 ^ ρ.length) lo hi i = eqSp ρ lo hi i := by
  simp only [eqSpH, eqSp, Bool.and_eq_true, decide_eq_true_eq]

/-- **The shift sum with the per-point work hoisted**: the four tables, both lengths and both bounds once. -/
def contShiftH (rows : List ℕ) (ρ ρ' : List F) : F :=
  let lo := eqKernelAF (ρ.take 6)
  let hi := eqKernelAF (ρ.drop 6)
  let lo' := eqKernelAF (ρ'.take 6)
  let hi' := eqKernelAF (ρ'.drop 6)
  let n := ρ.length
  let n' := ρ'.length
  let ok := decide (6 ≤ n)
  let ok' := decide (6 ≤ n')
  let N := 2 ^ n
  let N' := 2 ^ n'
  rows.foldl (fun acc i => acc + eqSpH ρ ok N lo hi i * eqSpH ρ' ok' N' lo' hi' (i - 1)) 0

omit [Algebra K F] in
theorem contShiftH_eq (rows : List ℕ) (ρ ρ' : List F) : contShiftH rows ρ ρ' = contShiftFast rows ρ ρ' := by
  simp only [contShiftH, contShiftFast, sumF, List.foldl_map, eqSpH_eq]

end Gen

/-- **`fKsLink` with the hoisted shift sum.** -/
def fKsLinkH (hk xl : ℕ) (rows : List ℕ) : VF (List FE2 × (List FE2 × FE2) × List FE2) :=
  VF.bind (fE2Samples gC1 (hk + 5)) fun kchal =>
  VF.bind (fSumcheck gC2 0 3 (List.replicate hk none)) fun kshift =>
  VF.bind (fE2Reads 4) fun vals =>
  VF.guard (decide (kshift.2 = contShiftH rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEvalF (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 + selXF xl kshift.1 * vals.getD 3 0)))
    (VF.pure (kchal, kshift, vals))

theorem fKsLinkH_eq : fKsLinkH = fKsLink := by
  funext hk xl rows
  simp only [fKsLinkH, fKsLink, contShiftH_eq]

/-- **`fSpongePhase6` over `fKsLinkH`.** -/
def fSpongePhase6H (sh : Lvm6.Shape) : VF PhF :=
  if SP.SpShapeOK sh then
    VF.bind (fSpCaller6 13) fun o => VF.bind (fKsLinkH 13 10 SP.contRows6) fun lk => VF.pure (spSF o lk)
  else fun _ _ => none

theorem fSpongePhase6H_eq : fSpongePhase6H = fSpongePhase6 := by
  funext sh
  simp only [fSpongePhase6H, fSpongePhase6, fKsLinkH_eq]

end Lvm6.V
