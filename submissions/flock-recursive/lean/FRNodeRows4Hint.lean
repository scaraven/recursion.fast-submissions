-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12c, track L-circ). Generated
-- by the dev probe `LayDump4` (`logs/fr-build-INT9/probe/LayDump4.lean`) from `layOfF4` of the two
-- prototypes at their template set `keys41` and `shiftMask` route `protoR` (S-E12e), at INT-8's
-- group-uniform programs (INT-9; `logs/INT-9/laydump4.log`).
import FRVIRTplExt

/-!
# The 4.1 prototypes' layouts, as constants

A layout only places template instances: `compileTF4_soundAt` holds at every layout, and the plan's
pieces are the compiled rows at every layout (`slotRP_rows`). These are the two-pass layouts
`layOfF4 (protoF π) (protoR π) (protoP π) (baseR π) (protoProg π).ops` of INT-8's uniform prototypes at
revision 4.1's template set and `shiftMask` routes (S-E12e: the node's `.maskN`, the segment's
`.shiftSeg`), printed once, so that the
process start does not run the first compile pass of each prototype (B-16: ≈ 0.4 s). That the rows
then fit their region with distinct indices is checked on the plan's pieces (`FRNodeRows4Plan`); a
stale layout fails the check, it does not change a statement.
-/

namespace FR
namespace Rev4
open Circ

/-- Prototype 0's layout (`layOfF4` at INT-8's uniform program; a hint, see the module doc). -/
def hintLay0 : TLay :=
  [(.lagrangeS 127 64, 144384, 191488, 10), (.eqTableK 6, 145152, 192512, 8),
   (.dotKF 64, 145408, 192768, 8), (.eqTableK 4, 182528, 267008, 6),
   (.dotKF 16, 182784, 267264, 6), (.eqZ, 201472, 304640, 8), (.phiRS 7, 201984, 305152, 8),
   (.rowW 8, 271616, 458752, 15), (.maskRows 9 16384, 288448, 491520, 14),
   (.walkAB 16384 16384, 305152, 507904, 17), (.eqPt 8 8, 390672, 593424, 4),
   (.eqPt 18 18, 390720, 593472, 6), (.shiftEq 18 18, 390912, 593664, 7),
   (.maskN 18 18 [(18, (23168, 92672)), (17, (23168, 46336)),
   (18, (92672, 92672))], 393216, 593920, 12), (.slotW 0 10 10, 397312, 598016, 12),
   (.slotW 1 10 10, 401408, 602112, 12), (.slotW 2 10 10, 405504, 606208, 12),
   (.tensorW 7, 407808, 610304, 6), (.eqTableK 7, 464384, 667136, 9)]

/-- Prototype 1's layout (`layOfF4` at INT-8's uniform program; a hint, see the module doc). -/
def hintLay1 : TLay :=
  [(.lagrangeS 127 64, 144384, 1241088, 10), (.eqTableK 6, 145152, 1242112, 8),
   (.dotKF 64, 145408, 1242368, 8), (.eqTableK 4, 182528, 1316608, 6),
   (.dotKF 16, 182784, 1316864, 6), (.eqZ, 201472, 1354240, 8), (.phiRS 7, 201984, 1354752, 8),
   (.rowW 8, 271616, 1507328, 15), (.maskRows 9 16384, 288448, 1540096, 14),
   (.walkAB 16384 16384, 305152, 1556480, 17), (.eqPt 8 8, 390672, 1642000, 4),
   (.eqPt 18 18, 390720, 1642048, 6), (.shiftEq 18 18, 390912, 1642240, 7),
   (.shiftSeg 36 18, 391168, 1642496, 9), (.slotW 0 10 10, 393216, 1646592, 12),
   (.slotW 1 10 10, 397312, 1650688, 12), (.slotW 2 10 10, 401408, 1654784, 12),
   (.eqPt 17 17, 403712, 1658880, 6), (.eqPt 23 23, 403776, 1658944, 6),
   (.tensorW 7, 403840, 1659008, 6), (.eqTableK 7, 460288, 1715712, 9)]

end Rev4
end FR
