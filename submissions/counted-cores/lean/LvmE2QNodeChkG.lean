-- New for lvm2 E2-FT (E2F-QH6): the node checks `NodeSound` reads (`LvmQTypedChk.inMapB`/`nodeChkB`) generic in
-- the trace's sponge blocks `B` (the digest row `B − 1`) and the `PUB` lane count, for the S2GF guard (`B = 4,295`,
-- `pubLanesX 44 = 750`); roll 11's checks are their `P20` instances by `rfl`.
import LvmQTypedChk

-- (GOLF2: 1 declarations that `certified` does not use moved verbatim to `LvmE2QNodeChkGOff`, outside its import closure.)

/-!
# The node checks at any stage

* **`inMapBG B nPub C Q lay N`**: `inMapB` with the trace-digest row `B − 1` and `nPub` `PUB` lanes.
* **`nodeChkBG B nPub C F Q lay N`**: `inMapBG && rdChkB && mbSeedsOkB` (`nodeChkB`'s shape).
* `inMapB_eq`, `nodeChkB_eq`: roll 11's checks are the instances at `spongeBlocks P20`, `pubLanes` (`rfl`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.QAsm Lvm.Typed Lvm.TypedV

/-- **The input map's cells, checked** (`inMapB` with the digest row `B − 1` and `nPub` `PUB` lanes). -/
def inMapBG (B nPub : Nat) (C : QCfg) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  let F := K.FL.ofLay Q lay
  let I := sigIn C
  bundleOkB F lay N 17 14 (Lvm.QAsm.lay C).sb (fun l r ↦ .cmain (CMain.sW20 l r)) &&
  bundleOkB F lay N 1 10 I.sg (fun _ r ↦ .cmain (CMain.sW20 17 r)) &&
  bundleOkB F lay N 17 9 I.xs (fun l r ↦ .cmain (CMain.ksXW20 l 0 + r)) &&
  bundleOkB F lay N 4 9 I.ys (fun l r ↦ .cmain (CMain.ksYW20 l (ksSplit P20) + r)) &&
  bundleOkB F lay N 4 0 I.md (fun l r ↦ .cmain (CMain.ksYW20 l (B - 1) + r)) &&
  (List.range nPub).all fun j ↦ cellOkB F lay N (I.flag + j) (.cpub j)

/-- **The checks `NodeSound` reads** at any stage (`nodeChkB`'s shape on `inMapBG`). -/
def nodeChkBG (B nPub : Nat) (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  inMapBG B nPub C Q lay N && rdChkB C F Q lay N && mbSeedsOkB C F

theorem inMapB_eq (C : QCfg) (Q : Program) (lay : Typed.Lay) (N : TNat) :
    inMapB C Q lay N = inMapBG (spongeBlocks P20) pubLanes C Q lay N := rfl

end Lvm.QTyped
