-- New for `flock-recursive` (BLUEPRINT §7): imports every module of the entry.
import FRFieldBase
import FRFieldBaseCorrect
import FRField128
import FRField256
import FRFieldControls
import FRMLE
import FRMLEControls
import FRSumcheck
import FRShift
import FRRingSwitch
import FRSkip
import FRSpartan
import FRRS
import FRRSEval
import FRProximityBW
import FRProximityLine
import FRProximityFold
import FRMerkle

/-!
# `flock-recursive`

The entry's modules, flat under `lean/` with the prefix `FR` and the namespace `FR`
(`docs/v4/flock-recursive/BLUEPRINT.md` §7). Stages S-A (fields), S-C (PIOP core) and S-D (PCS) so far.
-/
