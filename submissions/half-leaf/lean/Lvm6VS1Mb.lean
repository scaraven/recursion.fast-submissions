-- New for lvm6 (VS1): the mini-bus claims with the fixed columns' extensions computed once per check and shared by
-- the three claims (`mbClaimsFH = mbClaimsF`), the selector factor by `eqAtF`, and the typed phase over them.
import Lvm6VPhiReg
import Lvm6MbMid

/-!
# VS1: the mini-bus claims, shared work

`mbClaimsF` builds three claims (`s < 3`) from the same bus result `r`. Each claim's value `mbValueF` evaluates
every fixed column's extension `mleFixF t.τ fc (r.point.take t.τ)` again (its own equality table, and `fc` at every
cube point, `FK.x ^ e` by square-and-multiply); the point does not depend on `s`. Here each fixed column of each
table has one `Thunk`, made once per check and forced at most once (`colMles`, `mbPre`). Each claim's weight reads
the selector factor `eqAboveF p pt` (a selector list built and zipped per part) as `eqAtF (pt.drop τ) (index >>> τ)`
(`eqAboveFH_eq`), and takes `x.take nu` once per evaluation.

* `eqAboveFH` (`eqAboveFH_eq`), `mbClaimFH` (`mbClaimFH_eq`);
* `colMles`, `constFH` (`constFH_eq`), `mbPre`, `mbValueFH` (`mbValueFH_eq`);
* **`mbClaimsFH`**, **`mbClaimsFH_eq : mbClaimsFH = mbClaimsF`**;
* `fMiniBus6H`, `fTypedProgEXH`, **`fTypedPhase6XH`**, **`fTypedPhase6XH_eq : fTypedPhase6XH = fTypedPhase6X`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V Lvm.M3
open Lvm6.Mb
open Lvm6.Ty (TInst6 TyInst6)

/-! ## The selector factor -/

/-- `eqAboveF` as `eq` at a cube point. -/
def eqAboveFH (p : Plc) (pt : List FE2) : FE2 := eqAtF (pt.drop p.variableCount) (p.index >>> p.variableCount)

theorem eqAboveFH_eq : eqAboveFH = eqAboveF := by
  funext p pt
  rw [eqAboveFH, eqAboveF, selPtF_eq_bitsF, eqEvalF_comm, ← List.length_drop, eqEvalF_bitsF]

/-- `mbClaimF` with the selector factor by `eqAboveFH`, `x.take nu` once, and the sum as a left fold. -/
def mbClaimFH (nu : ℕ) (parts : List (FE2 × Plc × List FE2)) (v : FE2) : FClaim :=
  ⟨fun x =>
    let xt := x.take nu
    eqAboveFH ⟨nu, 0⟩ x * parts.foldl (fun acc p =>
      acc + p.1 * eqAboveFH p.2.1 xt * eqEvalF p.2.2 (xt.take p.2.1.variableCount)) 0, v⟩

theorem mbClaimFH_eq : mbClaimFH = mbClaimF := by
  funext nu parts v
  simp only [mbClaimFH, mbClaimF, eqAboveFH_eq, sumF, List.foldl_map]

/-! ## The fixed columns' extensions, once per check -/

/-- Each column's extension at `pt`, delayed: a `Thunk` for a fixed column, `none` for a committed one. -/
def colMles (t : Tab) (pt : List FE2) : List (Option (Thunk FE2)) :=
  t.cols.map fun col => match col with
    | ColSrc.fix fc _ => some (Thunk.mk fun _ => mleFixF t.τ fc pt)
    | ColSrc.com _ _ => none

/-- `constF` reading the fixed columns' extensions off `ms`. -/
def constFH (f : FormF) (ms : List (Option (Thunk FE2))) : FE2 :=
  sumF (f.map fun m => match m.1 with
    | [] => m.2
    | [c] => match ms[c]? with
      | some (some e) => m.2 * e.get
      | _ => 0
    | _ => 0)

theorem constFH_eq (t : Tab) (f : FormF) (pt : List FE2) : constFH f (colMles t pt) = constF t f pt := by
  unfold constFH constF
  congr 1
  refine List.map_congr_left fun m _ => ?_
  rcases m with ⟨l, v⟩
  match l with
  | [] => rfl
  | [c] =>
    simp only [colMles, List.getElem?_map]
    rcases t.cols[c]? with _ | (_ | _) <;> rfl
  | _ :: _ :: _ => rfl

/-- The tables with their indices and their columns' delayed extensions at `r`'s point. -/
def mbPre (tabs : List Tab) (r : BusResF) : List (ℕ × List (Option (Thunk FE2))) :=
  tabs.zipIdx.map fun tj => (tj.2, colMles tj.1 (r.point.take tj.1.τ))

/-- `mbValueF` over `mbPre`. -/
def mbValueFH (r : BusResF) (s : ℕ) (pre : List (ℕ × List (Option (Thunk FE2)))) : FE2 :=
  r.totals.getD s 0 + sumF (pre.map fun q => constFH (formF r q.1 s) q.2)

theorem mbValueFH_eq (tabs : List Tab) (r : BusResF) (s : ℕ) :
    mbValueFH r s (mbPre tabs r) = mbValueF tabs r s := by
  unfold mbValueFH mbPre mbValueF
  rw [List.map_map]
  congr 2
  refine List.map_congr_left fun tj _ => ?_
  rcases tj with ⟨t, j⟩
  exact constFH_eq t _ _

/-- **`mbClaimsF` with the shared extensions** and `mbClaimFH`. -/
def mbClaimsFH (nu : ℕ) (tabs : List Tab) (b : LBusF) : List FClaim :=
  let r := busFinalF tabs b.alphas b.beta b.point b.values
  let pre := mbPre tabs r
  (List.range 3).map fun s => mbClaimFH nu (mbPartsF tabs r s) (mbValueFH r s pre)

theorem mbClaimsFH_eq : mbClaimsFH = mbClaimsF := by
  funext nu tabs b
  simp only [mbClaimsFH, mbClaimsF, mbClaimFH_eq, mbValueFH_eq]

/-! ## The typed phase over them -/

/-- `fMiniBus6` over `mbClaimsFH`. -/
def fMiniBus6H (L : Lay) (tabs : List Tab) (μ : ℕ) : VF (List FClaim) :=
  VF.bind (fLvmBus μ) fun b => VF.pure (mbClaimsFH L.nuMain tabs b)

theorem fMiniBus6H_eq : fMiniBus6H = fMiniBus6 := by
  funext L tabs μ
  simp only [fMiniBus6H, fMiniBus6, mbClaimsFH_eq]

/-- `fTypedProgEX` over `fMiniBus6H`. -/
def fTypedProgEXH (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (tab : List FE2 → FE2) (accP : List FE2)
    (accY : FE2) : VF (List FClaim × List FClaim) :=
  VF.bind fZero fun z => VF.bind (fWire Ti pw z.2) fun w => VF.bind (fRelay Ti w.1 (w.2.2.getD 1 0)) fun r =>
  VF.bind (fAcc tab accY accP (z.1 ++ w.1) w.2.1) fun _ =>
  VF.bind (fMiniBus6H L Ti.mbT Lvm6.Mb.miniDepth) fun cl => VF.pure (typedClaimsFX Ti w.1 w.2.2 r.1 r.2 cl)

/-- **`fTypedPhase6X` over `fTypedProgEXH`.** -/
def fTypedPhase6XH (sh : Lvm6.Shape) (i : TyInst6) (tab : List FE2 → FE2) : VF (List FClaim) :=
  if sh.M = Lvm6.Ty.L6.nuMain then
    VF.bind (fTypedProgEXH i.Ti Lvm6.Ty.L6 i.pw tab (i.acc.1.map FE2.ofE2) (FE2.ofE2 i.acc.2)) fun out =>
      VF.pure (out.1.map recClaimF ++ out.2)
  else fun _ _ => none

theorem fTypedPhase6XH_eq : fTypedPhase6XH = fTypedPhase6X := by
  funext sh i tab
  simp only [fTypedPhase6XH, fTypedPhase6X, fTypedProgEXH, fTypedProgEX, fMiniBus6H_eq]

end Lvm6.V
