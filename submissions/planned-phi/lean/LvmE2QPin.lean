-- New for lvm2 E2F (slice S1, E2F-QH2): the root OOD pin in the circuit (E2AC-DES §1.3, statement 1's `pinProg` /
-- `pinClaim`, V's `LvmDecideE2.pinD`/`dOpenF`): its claim cells, and `C_main`'s opening with the pin's claim FIRST
-- (`openGP`, `LvmQAsmArith2WhirD.openG` with the pin; `openG` itself is unchanged for S2GM).
import LvmQAsmArith2WhirD
import LvmE2QWKit

/-!
# The pin (`pinG`, `openGP`)

V reads, right after `C_main`'s cap, `ν` `E3` samples `z` (answers at lanes `qz + 9 k`: the first answer's entry
carries the cap) and one `E3` scalar `a` (lanes `qa … qa + 2`), and opens `BlockClaim.point ⟨ν, 0⟩ z a` on the
physical stack, first in the list (`dOpenF`: `(pin.weight, pin.value) :: …`, not relocated in the small shape).

* **`pinG ν qz qa`**: `ν + 1` `loadE` rows; the claim `⟨.main, .point ⟨ν, 0⟩ z, a⟩`.
* **`openGP`**: `openG` with the pin first. Big shape: `stackGW` on `pin :: claims`. Small shape (`stackGZ`'s
  muxed basis point `X_i = mux(σ, x_i, x_{(i+1) mod ν})`): the pin enters as a muxed claim (flag `false`, its own
  form in both shapes) with the point `z'_i = mux(σ, z_i, z_{(i+1) mod ν})`, so that `eq(z', X) = eq(z, x)` in both
  shapes (the physical stack).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape

/-- **The pin's claim cells**: the `ν` samples at answer lanes `qz + 9 k`, the value at lanes `qa`. -/
def pinG (nu qz qa : Nat) : BM CClaim :=
  mapB (fun k => loadE (kc (qz + 9 * k)) (kc (qz + 9 * k + 1)) (kc (qz + 9 * k + 2))) (List.range nu) >>= fun z =>
  loadE (kc qa) (kc (qa + 1)) (kc (qa + 2)) >>= fun a =>
  pure ⟨.main, .point ⟨nu, 0⟩ z, a⟩

/-- The pin's point cells (`[]` if the claim is not a point claim). -/
def pinPt (pin : CClaim) : List Cell :=
  match pin.cw with
  | .point _ z => z
  | _ => []

/-- **The pin in both shapes**: the point `mux(σ, z_i, z_{(i+1) mod ν})`, flag `false`. -/
def pinZG (s : Cell) (pin : CClaim) : BM (CClaim × Bool) :=
  let z := pinPt pin
  mapB (fun i => muxG s (z.getD i default) (z.getD ((i + 1) % CMain.nu20) default)) (List.range CMain.nu20) >>=
    fun z' => pure (⟨pin.com, .point ⟨CMain.nu20, 0⟩ z', pin.value⟩, false)

/-- **`C_main`'s opening in both shapes with the pin first** (`stackGZ` with the pin). -/
def stackGZP (C : SCfg) (pin : CClaim) (cl : List CClaim) (mb : List Cell) (zc oc g : Cell) : BM Unit :=
  stackGWG C (cl.length + 1)
    (do
      let σ ← sigmaG mb zc
      let pz ← pinZG σ pin
      let zs ← zClaimsG σ zc oc cl
      pure (σ, pz :: zs))
    (fun w sp => targetG (w.2.map (·.1)) sp zc)
    (fun w sp xb => do
      let ms ← muxPtG w.1 xb (List.range CMain.nu20)
      let xs ← copiesG ms
      basisZ w.2 sp xs zc oc w.1)
    zc oc g

/-- **Phase 9 at S2GF**: `openG` with the pin's claim first. -/
def openGP (Cm : SCfg) (zon : Bool) (pin : CClaim) (cs : List CClaim) (mb : List Cell) (zc oc g : Cell) :
    BM Unit :=
  if zon then stackGZP Cm pin (onCom cs .main) mb zc oc g else stackGW Cm (pin :: onCom cs .main) zc oc g

end Lvm.Q2
