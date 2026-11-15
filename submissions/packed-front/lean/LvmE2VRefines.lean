-- New for lvm2 S1 (E2-F, E2F-V; E2F-V2): V_S at S2GF (`VSFX N`), generic in the native typed record `N` (S2GF's
-- instance is circuit-side, E2F-C's `NTF20`): the decision `decideFFX` with E2F-Q's coordinate-split typed phases.
import LvmE2VFast
import LvmTypedVX

/-!
# `V_S` at S2GF

* `decideFFX p N`: the decision at S2GF (`decideProgFF`, the fast twin of `decideProgF` (`decideProgFF_eq`), with the typed phases `dTypedX`, run from the cursor after
  the stage's header `headerBytesP p` (`RS.startH`), read as `decideFT`: every check held, `Σ` read to its end, and
  `Φ_Q` (`N.phi`, 44 coordinates) at the folded point);
* **`VSFX N`**: `VSF P20F accVF (decideFFX P20F N)` (agreed with E2F-C, 2026-11-13 19:08).

Statement 15 (`refinesF20`) is in `LvmE2VRefinesF` (it imports `LvmCertF20`'s format `fmtF20`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open RecursionFast Lvm

/-- **The decision at S2GF** on the stream `sig`, for the native typed record `N`. -/
def decideFFX (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := DM.runOnH (headerBytesP p) (decideProgFF p (fun m pub => TypedV.dTypedX p N m pub) N.m3 vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phi a.pt == a.y

/-- **`V_S` at S2GF** for the native typed record `N`. -/
def VSFX (N : TypedV.TNat) : Lvm.T.SProg := VSF P20F accVF (decideFFX P20F N)

end Lvm.E2V
