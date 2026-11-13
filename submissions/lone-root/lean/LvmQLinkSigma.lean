-- Moved out of `LvmQLinkMain` (lvm2 roll 8, wave L, L-W; a pure move): `Σ`, the hashed bytes of the stream, so that
-- the B program's definitions (`LvmQAsmHarBase`) do not wait for `LvmQLinkMain` (a shorter build critical path). It
-- imports `LvmQLinkSound` (`laneK`, and `LvmQLinkBridge`'s byte lemmas), which `LvmQAsmHarBase` read through
-- `LvmQLinkMain` before.
import LvmQLinkSound

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm

/-- **`Σ`**: the hashed bytes of the stream (the bytes `V_S`'s decision `F` reads). -/
def sigma (p : Params) (ws : List Word) : ByteArray := ⟨((wordsBytes ws).take (hashedLen p)).toArray⟩

end Lvm.QLink
