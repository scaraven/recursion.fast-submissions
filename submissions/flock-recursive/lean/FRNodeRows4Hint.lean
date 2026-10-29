-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12c, track L-circ). Generated
-- by the dev probe `LayDump4` (`logs/fr-build-SE12f/probe/LayDump4.lean`) from `layOfF4` of the two
-- prototypes at their template set `keys41` and route `protoR` (S-E12e), at INT-8's group-uniform
-- programs, with S-E12f's kind-muxed `tensorWK`/`eqPtK` (`logs/S-E12f/laydump4.log`).
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
  [(.lagrangeS 127 64, 144384, 190464, 10), (.eqTableK 6, 145152, 191488, 8),
   (.dotKF 64, 145408, 191744, 8), (.eqTableK 4, 182528, 265984, 6),
   (.dotKF 16, 182784, 266240, 6), (.eqZ, 201472, 303616, 8), (.phiRS 7, 201984, 304128, 8),
   (.eqPtK [(26, 26), (25, 25), (26, 26)], 271616, 435200, 8), (.rowW 8, 271808, 458752, 15),
   (.maskRows 9 16384, 288640, 491520, 14), (.walkAB 16384 16384, 305152, 507904, 17),
   (.eqPt 8 8, 390672, 593424, 4), (.eqPt 18 18, 390720, 593472, 6),
   (.shiftEq 18 18, 390912, 593664, 7),
   (.maskN 18 18 [(18, (23168, 92672)), (17, (23168, 46336)), (18, (92672, 92672))], 393216, 593920, 12),
   (.slotW 0 10 10, 397312, 598016, 12), (.slotW 1 10 10, 401408, 602112, 12),
   (.slotW 2 10 10, 405504, 606208, 12),
   (.eqPtK [(17, 17), (16, 16), (17, 17)], 407808, 610304, 7),
   (.eqPtK [(23, 23), (22, 22), (23, 23)], 408064, 610560, 8), (.tensorW 7, 408256, 610816, 6),
   (.tensorWK [19, 18, 19], 464896, 667648, 9), (.tensorWK [16, 15, 16], 613376, 816128, 9),
   (.tensorWK [13, 12, 13], 658944, 907264, 8), (.tensorWK [10, 9, 10], 696064, 944384, 8),
   (.eqTableK 7, 730112, 978432, 9)]

/-- Prototype 1's layout (`layOfF4` at INT-8's uniform program; a hint, see the module doc). -/
def hintLay1 : TLay :=
  [(.lagrangeS 127 64, 144384, 1240064, 10), (.eqTableK 6, 145152, 1241088, 8),
   (.dotKF 64, 145408, 1241344, 8), (.eqTableK 4, 182528, 1315584, 6),
   (.dotKF 16, 182784, 1315840, 6), (.eqZ, 201472, 1353216, 8), (.phiRS 7, 201984, 1353728, 8),
   (.eqPtK [(26, 26), (24, 24), (25, 25)], 271616, 1484800, 8), (.rowW 8, 271808, 1507328, 15),
   (.maskRows 9 16384, 288640, 1540096, 14), (.walkAB 16384 16384, 305152, 1556480, 17),
   (.eqPt 8 8, 390672, 1642000, 4), (.eqPt 18 18, 390720, 1642048, 6),
   (.shiftEq 18 18, 390912, 1642240, 7), (.shiftSeg 36 18, 391168, 1642496, 9),
   (.slotW 0 10 10, 393216, 1646592, 12), (.slotW 1 10 10, 397312, 1650688, 12),
   (.slotW 2 10 10, 401408, 1654784, 12), (.eqPt 17 17, 403712, 1658880, 6),
   (.eqPt 23 23, 403776, 1658944, 6), (.tensorW 7, 403840, 1659008, 6),
   (.tensorWK [19, 17, 18], 460288, 1715712, 9), (.tensorWK [16, 14, 15], 608768, 1864192, 8),
   (.tensorWK [13, 11, 12], 654336, 1909760, 8), (.tensorWK [10, 8, 9], 691456, 1946880, 8),
   (.eqTableK 7, 725504, 1980928, 9)]

end Rev4
end FR
