-- New for lvm2 S1 (E2-F, E2F-V2), E2AC-DES §6 statement 15 (`refinesF20`): `VSFX N` refines the compiled verifier
-- of `PSWithM (midP (midM reloc20 (midF₂ (N.inst Q lay))))` at S2GF's format `fmtF20` (roll 11's `refinesM20`
-- shape with the pin and the read widths).
import LvmE2VTopF
import LvmE2VWidthsF
import LvmE2VDecRef

-- (GOLF2: 1 declarations that `certified` does not use moved verbatim to `LvmCertF20InstOff`, outside its import closure.)

/-!
# Statement 15: `refinesF20`

For every native typed record `N` meeting E2F-Q's `TRefHypX N Q lay` (`N.phi` the specification's coordinate-split
`Φ_Q`) with `σ′`'s regions in the stream block (`SigInS N`): whenever `VSFX N` accepts a proof on a log, so does the
compiled verifier of the pinned middle phases at S2GF's format (read widths `rwF20`, `|π|`, header `headerF 44`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.VEq Lvm.TypedV LeanVM.Parameters LeanVM.Protocol.Compile

end Lvm.E2V
