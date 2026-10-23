-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
import SpartanSromFieldBaseCorrect
import SpartanSromFieldExtCorrect
import SpartanSromFieldControls

/-!
# The field layer of the `spartan-chain` entry

`F = GF(2^64)` on one `UInt64` and `EF = GF(2^192) = F[y] / (y^3 + y + 1)`, with fast compiled
arithmetic, proved equal to CompPoly's `BF64` and `BF64.Ext3` (`F.ringEquivBF64`,
`EF.ringEquivExt3`) and made fields through them (`F.instField`, `EF.instField`). See `FIELD.md`
at the root of the entry.
-/
