-- New for lvm6 (MUL2): the fast decision `F` over VS1's twins with the Keccak reductions, the phases' claims and the
-- opening on `m2B` (`FB`, `FB_eq`).
import Lvm6VM2W
import Lvm6VS1F

/-!
# MUL2: the fast decision with the reductions on `m2B`

`FH inst ev` (`Lvm6VS1F`) with the commitment phase `fCommit6B`, the tree phase `fTreePhB`, the sponge phase
`fSpongePhase6B` (`Lvm6VM2K`), the typed phase `fTypedPhase6XB`, the ring phase `fRingPhase6B` and the opening
`fWhir18B` (`Lvm6VM2W`).

* `fTreePhB`, `fRest6B`, `fProg6B`, **`FB`**; **`FB_eq : FB inst ev = FH inst ev`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V

/-- `fTreePh` over `fTreeProgS6B`, `treePhFB`. -/
def fTreePhB (sh : Lvm6.Shape) (x : Hdr) : VF PhF := VF.bind (fTreeProgS6B sh x) fun t => VF.pure (treePhFB t)

theorem fTreePhB_eq : fTreePhB = fTreePh := by
  funext sh x
  simp only [fTreePhB, fTreePh, fTreeProgS6B_eq, treePhFB_eq]

/-- `fRest6H` over the MUL2 phase twins. -/
def fRest6B (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) (sh : Lvm6.Shape) (x : Hdr) (c0 : FClaim) : VF Bool :=
  VF.bind (fTreePhB sh x) fun t =>
  VF.bind (fSpongePhase6B sh) fun s =>
  VF.bind (fTypedPhase6XB sh (inst x) ev) fun ty =>
  VF.guard (decide ([t.1, s.1].length + (c0 :: (t.2 ++ (s.2 ++ ty))).length ≤ sh.J₀))
    (VF.bind (fRingPhase6B sh [t.1, s.1] (c0 :: (t.2 ++ (s.2 ++ ty)))) fun cl => fWhir18B cl.f cl.v)

/-- `fProg6H` over `fRest6B`. -/
def fProg6B (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) (sh : Lvm6.Shape) (x : Hdr) : VF Bool :=
  VF.bind (fCommit6B sh) fun c0 => fRest6B inst ev sh x c0

/-- **`FH` with the reductions, the claims and the opening on `m2B`.** -/
def FB (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) (sh : Lvm6.Shape) (π : ByteArray) (acc : List NV) : Bool :=
  match fProg6B inst ev sh (hdrView sh (hdrBytes sh π)) π acc.reverse with
  | some (b, []) => b
  | _ => false

theorem fProg6B_eq (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) : fProg6B inst ev = fProg6H inst ev := by
  funext sh x
  simp only [fProg6B, fProg6H, fRest6B, fRest6H, fCommit6B_eq, fTreePhB_eq, fSpongePhase6B_eq, fTypedPhase6XB_eq,
    fRingPhase6B_eq, fWhir18B_eq]

/-- **`FB` is `FH`.** -/
theorem FB_eq (inst : Hdr → Ty.TyInst6) (ev : List FE2 → FE2) : FB inst ev = FH inst ev := by
  funext sh π acc
  simp only [FB, FH, fProg6B_eq]
  rfl

end Lvm6.V
