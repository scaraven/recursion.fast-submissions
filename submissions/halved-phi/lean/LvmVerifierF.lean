-- New for lvm2 S1 (E2-F, E2F-V): V_S's driver at S2GF (`ItemF`: 16-B `E2` scalars and 8-B nonces) and the
-- verifier `VSF` from a decision `F` on the stream (`LvmDriver`'s `drive`, `LvmVerifierST`'s `VST`).
import LvmScheduleF
import LvmDriver

/-!
# The S2GF driver

* `driveItemsF`: `driveItems` (since route A, `readW m w` moves the body offset by `w·m` bytes there).
* `driveF`, `parseOkF`, `seedQueryF`: `drive`, `parseOk`, `seedQuery` at `p.withF accV` (one stage-parametric
  header path: `headerBytesP`, `piSize`).
* **`VSF p accV F`**: the native checks, then `q₀`, the seed, the S2GF schedule and `F` on the stream.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **Run the S2GF items** from the state `s`, then `k` (the one driver: `driveItems` moves the body offset by
`w·m` bytes on `readW m w`). -/
abbrev driveItemsF (p : Params) (π : ByteArray) : List ItemF → DSt → (DSt → OProg Bool) → OProg Bool :=
  driveItems p π

/-- The seed query over the S2GF header (`seedQuery` to `headerBytesP (p.withF accV)`). -/
abbrev seedQueryF (p : Params) (accV : Nat) (π : ByteArray) (a₀ : Digest) : ByteArray :=
  seedQuery π a₀ (headerBytesP (p.withF accV))

/-- **The S2GF driver**: `drive` at `p.withF accV` (`q₀`, the seed over the S2GF header, the schedule; with the
body used up, `F` on the stream). -/
abbrev driveF (p : Params) (accV : Nat) (π : ByteArray) (F : ByteArray → Bool) : OProg Bool :=
  drive (p.withF accV) π F

/-- The native checks at S2GF: `parseOk` at `p.withF accV` (`|π| = piSizeF p accV`). -/
abbrev parseOkF (p : Params) (accV : Nat) (vk c : Digest) (π : ByteArray) : Bool :=
  parseOk (p.withF accV) vk c π

/-- **`V_S` at S2GF** from a decision `F` on the stream. -/
def VSF (p : Params) (accV : Nat) (F : Digest → Digest → ByteArray → Bool) (vk c : Digest) (π : Proof) :
    OProg Bool :=
  if parseOkF p accV vk c π then driveF p accV π (F vk c) else .ret false

end Lvm
