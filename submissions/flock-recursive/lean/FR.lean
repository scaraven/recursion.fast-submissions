-- New for `flock-recursive` (BLUEPRINT §7): imports every module of the entry.
import FRFieldBase
import FRFieldBaseCorrect
import FRField128
import FRField256
import FRFieldControls

/-!
# `flock-recursive`

The entry's modules, flat under `lean/` with the prefix `FR` and the namespace `FR`
(`docs/v4/flock-recursive/BLUEPRINT.md` §7). Stage S-A (track L-field): the fields
`F = GF(2^128)` and `K = GF(2^256)` with their fast twins and controls.
-/
