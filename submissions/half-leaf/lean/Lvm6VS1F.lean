-- New for lvm6 (VS1): the fast decision `F` over VS1's phase twins and any `Φ_Q` evaluator (`FH`, `FH_eq`).
import Lvm6VS1Ks
import Lvm6VS1Wh
import Lvm6VS1Mb
import Lvm6VTwF

/-!
# VS1: the fast decision over the faster phase twins

`F inst P` (`Lvm6VTwF`) with the sponge phase `fSpongePhase6H` (`Lvm6VS1Ks`), the typed phase `fTypedPhase6XH`
(`Lvm6VS1Mb`), the opening `fWhirH` (`Lvm6VS1Wh`) and the evaluator `ev` of `Φ_Q` as a
parameter, so that another evaluator can be plugged in with its own equality.

* `fRest6H`, `fProg6H`, **`FH`**; **`FH_eq : FH inst P.eval = F inst P`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V

/-- `fRest6` over the VS1 phase twins, with the evaluator `ev`. -/
def fRest6H (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) (sh : Lvm6.Shape) (x : Hdr) (c0 : FClaim) : VF Bool :=
  VF.bind (fTreePh sh x) fun t =>
  VF.bind (fSpongePhase6H sh) fun s =>
  VF.bind (fTypedPhase6XH sh (inst x) ev) fun ty =>
  VF.guard (decide ([t.1, s.1].length + (c0 :: (t.2 ++ (s.2 ++ ty))).length ≤ sh.J₀))
    (VF.bind (fRingPhase6 sh [t.1, s.1] (c0 :: (t.2 ++ (s.2 ++ ty)))) fun cl => fWhirH cl.f cl.v)

/-- `fProg6` over `fRest6H`. -/
def fProg6H (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) (sh : Lvm6.Shape) (x : Hdr) : VF Bool :=
  VF.bind (fCommit6 sh) fun c0 => fRest6H inst ev sh x c0

/-- **`F` over the VS1 phase twins**, with the evaluator `ev`. -/
def FH (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) (sh : Lvm6.Shape) (π : ByteArray) (acc : List NV) : Bool :=
  match fProg6H inst ev sh (hdrView sh (hdrBytes sh π)) π acc.reverse with
  | some (b, []) => b
  | _ => false

theorem fProg6H_eq (inst : Hdr → Ty.TyInst6) (P : PT) : fProg6H inst P.eval = fProg6 inst P := by
  funext sh x
  simp only [fProg6H, fProg6, fRest6H, fRest6, fSpongePhase6H_eq, fTypedPhase6XH_eq, fWhirH_eq]

/-- **`FH` at `PT.eval` is `F`.** -/
theorem FH_eq (inst : Hdr → Ty.TyInst6) (P : PT) : FH inst P.eval = F inst P := by
  funext sh π acc
  simp only [FH, F, fProg6H_eq]
  rfl

end Lvm6.V
