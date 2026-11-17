-- New for lvm2 E2-FT (E2F-QH3): the layout solver's dense-interval fixpoint on the coordinate-split terms (twin
-- `e2` rows at stage S2GF).
import LvmTypedLay
import LvmWiringX

/-!
# The layout with twin rows (`mkLayRX`)

`mkLayD` already lays twin `e2` rows out as the S2GF backend needs them: both twins are `K` writers, so each has a
committed `K` slot (its result word); only the first (`Row.isCon`) has a constraint rank, whose slot carries both
coordinates' entries (`LvmWiringX.instEntsX`). `Lay.okB` accepts it (`tplOk`: the second twin is a writer with no
rank). What changes is the dense-interval fixpoint: roll 11's `denseInts` reads the terms of `K.deriveTerms`, which
does not see the `e2` operands; `denseIntsX` reads both coordinates' terms (`deriveTermsX`), with `entArgX` the
operand of a twin's entry.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-- The operand of entry `idx` of coordinate `s`'s entries of a template row (`srcEntsX`' order), if it is an
operand's: a twin's `K` operands have one entry each (`mul`: `a_s, b_s, d_s`, then the result; `lin`: `a_s, b_s`, the
constant `k_s`, the result); every other row as `entArg` (coordinate `0` only). -/
def entArgX (r : Row) (s : Bool) (idx : ℕ) : Option ℕ :=
  match r.op with
  | .e2 .mul false => if idx < 3 then some (2 * idx + (if s then 1 else 0)) else none
  | .e2 (.lin ..) false => if idx < 2 then some (2 * idx + (if s then 1 else 0)) else none
  | .e2 _ true => none
  | _ => if s then none else entArg r idx

/-- The cell intervals of the poorly fitted reads of both coordinates, extended to the whole blocks they touch. -/
def denseIntsX (Q : Program) (lay : Lay) : Array (Ty × ℕ × ℕ) := Id.run do
  let qb := Q.blocks.toArray
  let F := K.FL.ofLay Q lay
  let mut out : Array (Ty × ℕ × ℕ) := #[]
  for s in [false, true] do
    for t in deriveTermsX Q lay s do
      if !poorFit t then continue
      match t.src with
      | .row b r =>
        let B := qb.getD b default
        let row := B.tpl.getD r default
        match entArgX row s t.idx with
        | none => pure ()
        | some k =>
          let a := row.args.getD k default
          let lo := a.base
          let hi := a.base + dot a.strides (B.dims.map fun d ↦ 2 ^ d - 1)
          match F.owner a.ty lo, F.owner a.ty hi with
          | some b1, some b2 =>
            if b1 == b2 && lo == hi then pure () else
            let B1 := F.bl.getD b1 default
            let B2 := F.bl.getD b2 default
            let allCom := (List.range (b2 + 1 - b1)).all fun i ↦
              ((F.bl.getD (b1 + i) default).src a.ty).all fun s ↦ match s with | .slot _ => true | _ => false
            if allCom then out := out.push (a.ty, B1.st a.ty, B2.st a.ty + B2.tw a.ty * 2 ^ B2.l)
          | _, _ => pure ()
      | .aux .. => pure ()
  return out

/-- **The layout of `Q` with twin rows**: `mkLayR` with `denseIntsX`. -/
def mkLayRX (Q : Program) (S : LSpec) (rounds : ℕ) : Lay × LayStats × Array (Ty × ℕ × ℕ) := Id.run do
  let mut dints : Array (Ty × ℕ × ℕ) := #[]
  let mut L := mkLayD Q S dints
  for _ in [0:rounds] do
    let m := mergeInts (dints ++ denseIntsX Q L.1)
    if m == dints then break
    dints := m
    L := mkLayD Q S dints
  return (L.1, L.2, dints)

end Lvm.Typed
