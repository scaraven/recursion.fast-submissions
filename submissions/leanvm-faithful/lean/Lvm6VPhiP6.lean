-- New for lvm6 (ST-4, STARTUP2 P4): the embedded class table. Goes into lean/ next to the generated
-- `Lvm6DataPhi*.lean` (`python3 -I docs/lvm6/wp/ST4/phb.py <exporter .cls> <lean dir>`). Untrusted: `phiChk` checks it.
import Lvm6VPhiLoad
import Lvm6DataPhi

namespace Lvm6.V

/-- **The embedded class table `P6`** (decoded once, at first use). -/
def phiP6 : PT := PT.ofHex Lvm6.Data.phiHex

end Lvm6.V
