-- New for lvm6 (WP N4-tail phase 2, RV4 M4 (b) closed). The A23 promise at the node's memory: N4-cells' `PUB` cells
-- (`pub_lane`: cell `pbC + l` is header lane `l` of CD's public words) discharge `promise_of_accOk`'s `hown`.
import Lvm6NodeTailHH
import Lvm6NodeCells

/-!
# The A23 promise from `AccOkE` (WP N4-tail, RV4 M4 (b))

**`promise_pub`**: on the memory the typed relation reads (`memTi Ti L (pwOf Ti (hdrBytes x)) p`, public words of
the node's header `x`), with the layout fact `PubCells Ti` (N4-cells), a header with `phiVarsE` accumulator
coordinates and `AccOkE Ti (accFix x)`, the own accumulator cells satisfy `Φ_Q(own) = ownY`, the promise
`node6E_har`'s typed run is taken under.
-/

set_option autoImplicit false

namespace Lvm6.Node.Hdr

open RecursionFast LeanVM.Parameters Lvm Lvm.Loop Lvm.Typed LeanVM.Protocol

/-- **The A23 promise** from `AccOkE` of the node's header and the `PUB` cells. -/
theorem promise_pub {Ti : Ty.TInst6} (hP : Dep.PubCells Ti) (L : Lvm.M3.Lay) (x : Hdr)
    (p : Column L.nuMain × Column L.nuRec) (hx : x.accIn.1.length = Ty.phiVarsE)
    (hok : Ty.AccOkE Ti (V.accFix x)) :
    Ty.PhiQE Ti.Q Ti.lay (Dep.ownC.map (QK.ev2 (Lvm6.Node.memTi Ti L (QD.pwOf Ti (hdrBytes x)) p))) =
      QK.ev2 (Lvm6.Node.memTi Ti L (QD.pwOf Ti (hdrBytes x)) p) Dep.ownYC :=
  promise_of_accOk Ti hx (fun l _ h2 ↦ Dep.pub_lane hP L (hdrBytes x) p (by
    simp only [hdrAccW, Ty.phiVarsE] at h2
    exact lt_of_lt_of_le h2 (by decide))) hok

end Lvm6.Node.Hdr
