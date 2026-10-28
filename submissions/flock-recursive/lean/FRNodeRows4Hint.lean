-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12c, track L-circ). Generated
-- by the dev probe `LayDump4` (`logs/fr-build-SE12c/probe/LayDump4.lean`) from `layOf` of the two
-- prototypes at S-E12b's programs (`logs/S-E12c/laydump4.log`).
import FRVIRTplExt

/-!
# The 4.1 prototypes' layouts, as constants

A layout only places template instances: `compileT_sound` holds at every layout, and the plan's
pieces are the compiled rows at every layout (`slotRP_rows`). These are the two-pass layouts
`layOf (protoP π) (baseR π) (protoProg π).ops` of S-E12b's prototypes, printed once, so that the
process start does not run the first compile pass of each prototype (B-16: ≈ 0.4 s). That the rows
then fit their region with distinct indices is checked on the plan's pieces (`FRNodeRows4Plan`); a
stale layout fails the check, it does not change a statement.
-/

namespace FR
namespace Rev4
open Circ

/-- Prototype 0's layout (`layOf` at S-E12b's program; a hint, see the module doc). -/
def hintLay0 : TLay :=
  [(.lagrangeS 127 64, 144384, 191488, 10), (.eqTableK 6, 145152, 192512, 8),
   (.dotKF 64, 145408, 192768, 8), (.eqTableK 4, 182528, 267008, 6), (.dotKF 16, 182784, 267264, 6),
   (.eqZ, 201472, 304640, 8), (.phiRS 7, 201984, 305152, 8), (.rowW 8, 271616, 458752, 15),
   (.maskRows 9 16384, 288448, 491520, 14), (.walkAB 16384 16384, 305152, 507904, 17),
   (.eqPt 8 8, 390672, 593424, 4), (.eqPt 18 18, 390720, 593472, 6),
   (.shiftEq 18 18, 390912, 593664, 7), (.shiftMask 18 18, 393216, 593920, 12),
   (.slotW 0 10 10, 397312, 598016, 12), (.slotW 1 10 10, 401408, 602112, 12),
   (.slotW 2 10 10, 405504, 606208, 12), (.eqPt 17 17, 407808, 610304, 6),
   (.eqPt 23 23, 407872, 610368, 6), (.tensorW 7, 407936, 610432, 6),
   (.tensorW 19, 464384, 666880, 7), (.tensorW 16, 501504, 704000, 7),
   (.tensorW 13, 524288, 726784, 7), (.tensorW 10, 542848, 745344, 7),
   (.eqTableK 7, 551424, 762368, 9)]

/-- Prototype 1's layout (`layOf` at S-E12b's program; a hint, see the module doc). -/
def hintLay1 : TLay :=
  [(.lagrangeS 127 64, 144384, 1240064, 10), (.eqTableK 6, 145152, 1241088, 8),
   (.dotKF 64, 145408, 1241344, 8), (.eqTableK 4, 182528, 1315584, 6),
   (.dotKF 16, 182784, 1315840, 6), (.eqZ, 201472, 1353216, 8), (.phiRS 7, 201984, 1353728, 8),
   (.rowW 8, 271616, 1507328, 15), (.maskRows 9 16384, 288448, 1540096, 14),
   (.walkAB 16384 16384, 305152, 1556480, 17), (.eqPt 8 8, 390672, 1642000, 4),
   (.eqPt 18 18, 390720, 1642048, 6), (.shiftEq 18 18, 390912, 1642240, 7),
   (.shiftMask 36 18, 393216, 1642496, 12), (.slotW 0 10 10, 397312, 1646592, 12),
   (.slotW 1 10 10, 401408, 1650688, 12), (.slotW 2 10 10, 405504, 1654784, 12),
   (.eqPt 17 17, 407808, 1658880, 6), (.eqPt 23 23, 407872, 1658944, 6),
   (.tensorW 7, 407936, 1659008, 6), (.tensorW 19, 464384, 1715456, 7),
   (.tensorW 16, 501504, 1752576, 7), (.tensorW 13, 524288, 1775360, 7),
   (.tensorW 10, 542848, 1793920, 7), (.eqTableK 7, 551424, 1810944, 9)]

end Rev4
end FR
