-- Moved out of `LvmQAsmArith2Whir` (lvm2 roll 8, wave L, L-W; a pure move): the definitions of phases 8–9's gadgets
-- (`stackGWG`, `stackGW`, `LayOk`, `StackOk`, `stackGZ`, `onCom`, `openG`, `claimsT`), so that the B program's
-- definitions do not wait for `LvmQAsmArith2WhirLS`'s proofs (a shorter build critical path). The proofs stay in
-- `LvmQAsmArith2Whir`. It imports `LvmQAsmArith2WhirOk` (`okb`, `adv_e_le`), which the typed HAR reads along this path.
import LvmQAsmArith2WhirOk
import LvmQAsmArith2WhirL
import LvmQAsmArith2WhirBasis
import LvmQShapeB

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-- The first level's fold (`whirLevels`' `laneFolds`). -/
def SCfg.lf (C : SCfg) : Nat := (C.levels.head?.map (·.fold)).getD 0

/-- **One stacked opening, generic in its batching** (roll 7, CR-Q): `pre` runs first (`C_main`'s shape cell
and muxed claims), then the challenges, the batching powers (`n` claims), the target `tg`, the basis point's
copies, the basis `bg`, the levels. -/
def stackGWG {β : Type} (C : SCfg) (n : Nat) (pre : BM β) (tg : β → Nat → BM Cell)
    (bg : β → Nat → Nat → BM Cell) (zc oc g : Cell) : BM Unit := do
  let w ← pre
  let pc ← preloadG (chLanes C.g C.ood C.levels (C.U + 15))
  let sb ← ldEW (C.U + 5)
  let sp ← pows (Nat.clog 2 n) sb oc zc
  let tgt ← tg w sp
  let pt := (List.range C.nu).map fun k => ec (pc + k)
  let xb ← copiesG (pt.drop C.lf ++ pt.take C.lf)
  let bas ← bg w sp xb
  let zk ← const .K 0 g
  let q ← rdQ (C.U + 9) tgt
  levelsG C pc zc oc g zk.n bas C.levels 0 0 (C.U + 15) q []

/-- **One stacked opening** (see the module doc). -/
def stackGW (C : SCfg) (cl : List CClaim) (zc oc g : Cell) : BM Unit :=
  stackGWG C cl.length (pure ()) (fun _ sp => targetG cl sp zc) (fun _ sp xb => basisG C.nu cl sp xb zc oc g) zc oc g

/-- **The static layout checks of one stacked opening** (stream lanes below `T`). -/
def LayOk (C : SCfg) (T : Nat) : Bool :=
  lvOk C T C.levels 0 0 (C.U + 15) && (chLanes C.g C.ood C.levels (C.U + 15)).all (fun v => decide (v + 2 < T)) &&
    decide (C.U + 20 < T) && decide (C.lf ≤ C.nu)

/-- **The static checks of one stacked opening**: the layout and the claims' shapes. -/
def StackOk (C : SCfg) (cl : List CClaim) (T : Nat) : Bool := LayOk C T && ClaimsWF C.nu cl

section Z

open Lvm.QShape Lvm.Shape

/-- **`C_main`'s stacked opening in both shapes**: the shape cell `σ'` and the muxed claims (`pre`), the target
over the muxed values, the basis over the muxed point `x^σ` (`basisZ`). -/
def stackGZ (C : SCfg) (cl : List CClaim) (mb : List Cell) (zc oc g : Cell) : BM Unit :=
  stackGWG C cl.length
    (do
      let σ ← sigmaG mb zc
      let zs ← zClaimsG σ zc oc cl
      pure (σ, zs))
    (fun w sp => targetG (w.2.map (·.1)) sp zc)
    (fun w sp xb => do
      let ms ← muxPtG w.1 xb (List.range CMain.nu20)
      let xs ← copiesG ms
      basisZ w.2 sp xs zc oc w.1)
    zc oc g

end Z

/-- The claims of one commitment. -/
def onCom (cs : List CClaim) (com : Com) : List CClaim := cs.filter fun cc => cc.com == com

/-- **Phases 8–9**: `C_rec`'s stacked opening, then `C_main`'s; with `zon` (the record has a small shape, `P20`)
`C_main`'s in both shapes (`stackGZ`, the child's shape cell from `n' − 1`'s bits `mb`). -/
def openG (Cr Cm : SCfg) (zon : Bool) (cs : List CClaim) (mb : List Cell) (zc oc g : Cell) : BM Unit := do
  stackGW Cr (onCom cs .crec) zc oc g
  if zon then stackGZ Cm (onCom cs .main) mb zc oc g else stackGW Cm (onCom cs .main) zc oc g

/-- The claims with their tails (the cells' closed forms, `tailC`). -/
def claimsT (M : Mem) (cs : List CClaim) : List (Com × BlockClaim × FE) :=
  cs.map fun cc => (cc.com, (cc.val M).2, Lvm.QShape.tailC M cc)

end Lvm.Har
