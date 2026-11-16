-- New for lvm (WP-8): V_S's `pad43` lane formulas (`LvmDecide`) are the lanes of `pad43St` (`LvmChainTable`).
import LvmChainTable

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmVEqWireOff`, outside its import closure.)

/-!
# `Pad43` on lanes

V_S states the boundary claim `in_0 = Pad43(s)` as 25 word claims whose values are its `pad43`
(`LvmDecide`): from the four little-endian lanes `w` of `s`, lane 0 is `0x43 ||| w₀ << 8`, lanes
`1 … 3` are `w_{l−1} >> 56 ||| w_l << 8`, lane 4 is `w₃ >> 56 ||| 0x01 << 8`, lane 16 is `0x80 << 56`,
and the others are zero. **`lane_pad43St`** proves these are the lanes of `pad43St (digestBits s)`, the
state `ChainRel.first` speaks of. (`pad43Lane` is that formula on `UInt64`; V_S's version is the
same on `FK` words.)
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

end Lvm.KG
