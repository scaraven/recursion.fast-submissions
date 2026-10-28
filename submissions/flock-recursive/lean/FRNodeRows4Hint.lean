-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12c, track L-circ). Generated
-- by the dev probe `LayDump4` (`logs/fr-build-SE12d/probe/LayDump4.lean`) from `layOfF` of the two
-- prototypes at their template set `keys41` (S-E12d; `logs/S-E12d/laydump4.log`).
import FRVIRTplExt

/-!
# The 4.1 prototypes' layouts, as constants

A layout only places template instances: `compileTF_sound` holds at every layout, and the plan's
pieces are the compiled rows at every layout (`slotRP_rows`). These are the two-pass layouts
`layOfF (protoF π) (protoP π) (baseR π) (protoProg π).ops` of S-E12b's prototypes at revision 4.1's
template set (S-E12d: no `shiftMask` template), printed once, so that the
process start does not run the first compile pass of each prototype (B-16: ≈ 0.4 s). That the rows
then fit their region with distinct indices is checked on the plan's pieces (`FRNodeRows4Plan`); a
stale layout fails the check, it does not change a statement.
-/

namespace FR
namespace Rev4
open Circ

/-- Prototype 0's layout (`layOfF` at S-E12b's program; a hint, see the module doc). -/
def hintLay0 : TLay :=
  [(.lagrangeS 127 64, 144384, 191488, 10), (.eqTableK 6, 145152, 192512, 8),
   (.dotKF 64, 145408, 192768, 8), (.eqTableK 4, 182528, 267008, 6), (.dotKF 16, 182784, 267264, 6),
   (.eqZ, 201472, 304640, 8), (.phiRS 7, 201984, 305152, 8), (.rowW 8, 271616, 458752, 15),
   (.maskRows 9 16384, 288448, 491520, 14), (.walkAB 16384 16384, 305152, 507904, 17),
   (.eqPt 8 8, 390672, 593424, 4), (.eqPt 18 18, 390720, 593472, 6),
   (.shiftEq 18 18, 390912, 593664, 7), (.slotW 0 10 10, 393216, 593920, 12),
   (.slotW 1 10 10, 397312, 598016, 12), (.slotW 2 10 10, 401408, 602112, 12),
   (.eqPt 17 17, 403712, 606208, 6), (.eqPt 23 23, 403776, 606272, 6),
   (.tensorW 7, 403840, 606336, 6), (.tensorW 19, 460288, 662784, 7),
   (.tensorW 16, 497408, 699904, 7), (.tensorW 13, 520192, 722688, 7),
   (.tensorW 10, 538752, 741248, 7), (.eqTableK 7, 547328, 758272, 9)]

/-- Prototype 1's layout (`layOfF` at S-E12b's program; a hint, see the module doc). -/
def hintLay1 : TLay :=
  [(.lagrangeS 127 64, 144384, 1240064, 10), (.eqTableK 6, 145152, 1241088, 8),
   (.dotKF 64, 145408, 1241344, 8), (.eqTableK 4, 182528, 1315584, 6),
   (.dotKF 16, 182784, 1315840, 6), (.eqZ, 201472, 1353216, 8), (.phiRS 7, 201984, 1353728, 8),
   (.rowW 8, 271616, 1507328, 15), (.maskRows 9 16384, 288448, 1540096, 14),
   (.walkAB 16384 16384, 305152, 1556480, 17), (.eqPt 8 8, 390672, 1642000, 4),
   (.eqPt 18 18, 390720, 1642048, 6), (.shiftEq 18 18, 390912, 1642240, 7),
   (.slotW 0 10 10, 393216, 1642496, 12), (.slotW 1 10 10, 397312, 1646592, 12),
   (.slotW 2 10 10, 401408, 1650688, 12), (.eqPt 17 17, 403712, 1654784, 6),
   (.eqPt 23 23, 403776, 1654848, 6), (.tensorW 7, 403840, 1654912, 6),
   (.tensorW 19, 460288, 1711360, 7), (.tensorW 16, 497408, 1748480, 7),
   (.tensorW 13, 520192, 1771264, 7), (.tensorW 10, 538752, 1789824, 7),
   (.eqTableK 7, 547328, 1806848, 9)]

end Rev4
end FR
