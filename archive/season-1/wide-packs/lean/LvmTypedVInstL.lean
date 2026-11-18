-- New for lvm2 S2GT (GT-L2, re-freeze A2): `PUB`'s header lanes generalised over the per-scalar lane layout
-- (`Pub.hdrLanesW`; S2GT's 16-B `acc_in` in two lanes per scalar, `Pub.hdrLanesT`) and the specification's instance of a
-- native record with `PUB` read through a lane list (`TNat.instL`; `TNat.inst` is the instance at `Pub.hdrLanes`).
import LvmTypedVInst

/-!
# `PUB`'s lane layout

* **`Pub.hdrLanesW lw`**: the header's lanes with `acc_in`'s scalars laid out by `lw`; `hdrLanes_eq_W`:
  `Pub.hdrLanes = hdrLanesW FE.lanes`. **`Pub.hdrLanesT`**: S2GT's, `FE.lanes2` (`c₀, c₁`): 615 + 2·46 = 707 lanes.
* **`TNat.instL N pl`**: `TNat.inst` with `pubV` reading `pl pub`; `instL_hdrLanes`: at `Pub.hdrLanes` it is
  `TNat.inst`.
-/

set_option autoImplicit false

namespace Lvm

/-- An `E2` scalar's two lanes `c₀, c₁` (its 16 header bytes; S2GT re-freeze A2). -/
def FE.lanes2 (e : FE) : List FK := [e.c₀, e.c₁]

/-- **The header's lanes from byte 8 with `acc_in`'s scalars laid out by `lw`** (`Pub.hdrLanes` generalised over
the per-scalar lanes: `hdrLanes = hdrLanesW FE.lanes`, `hdrLanes_eq_W`). -/
def Pub.hdrLanesW (lw : FE → List FK) (P : Pub) : List FK :=
  [⟨P.b.toUInt64⟩] ++ P.vk ++ P.cL ++ P.s ++ [⟨P.n.toUInt64⟩] ++ P.h ++ P.sigLeaf ++
    (P.accIn.pt ++ [P.accIn.y]).flatMap lw

theorem Pub.hdrLanes_eq_W (P : Pub) : P.hdrLanes = P.hdrLanesW FE.lanes := rfl

/-- **`PUB`'s lanes at S2GT** (re-freeze A2): `acc_in`'s 16-B scalars as two lanes each (`FE.lanes2`), 615 + 2·46 =
707 lanes (`pubLanesT`). -/
def Pub.hdrLanesT (P : Pub) : List FK := P.hdrLanesW FE.lanes2

end Lvm

namespace Lvm.TypedV

/-- **The specification's instance of a native one, with `PUB` read through `pl`** (`TNat.inst`'s `pubV` generalised
over the header's lane layout; `instL_hdrLanes`: `TNat.inst` is the instance at `Pub.hdrLanes`). -/
def TNat.instL (N : TNat) (pl : Pub → List FK) (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) : Lvm.Typed.TInst :=
  { N.inst Q lay with pubV := fun pub y ↦ (pl pub).getD (N.off y) 0 }

theorem TNat.instL_hdrLanes (N : TNat) (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) :
    N.instL Pub.hdrLanes Q lay = N.inst Q lay := rfl

end Lvm.TypedV

