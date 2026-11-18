-- New for lvm2 S1 (E2-F, E2F-V; E2F-V2): V_S at S2GF (`VSFX N`), generic in the native typed record `N` (S2GF's
-- instance is circuit-side, E2F-C's `NTF20`): the decision `decideFFX` with E2F-Q's coordinate-split typed phases.
import LvmE2VFast
import LvmTypedVX
import LvmScheduleF
import LvmDriver

-- ===== merged from `LvmVerifierF` (VQ module merge: `LvmVerifierF.lean` removed) =====
section
-- New for lvm2 S1 (E2-F, E2F-V): V_S's driver at S2GF (`ItemF`: 16-B `E2` scalars and 8-B nonces) and the
-- verifier `VSF` from a decision `F` on the stream (`LvmDriver`'s `drive`, `LvmVerifierST`'s `VST`).

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
end
-- ===== end of `LvmVerifierF` =====

-- (GOLF2 import pruning: `LvmVerifierF` imported directly: this file names `VSF` in text.)

/-!
# `V_S` at S2GF

* `decideFFX p N`: the decision at S2GF (`decideProgFF`, the fast twin of `decideProgF` (`decideProgFF_eq`), with the typed phases `dTypedX`, run from the cursor after
  the stage's header `headerBytesP p` (`RS.startH`), read as `decideFT`: every check held, `Σ` read to its end, and
  `Φ_Q` (`N.phi`, 44 coordinates) at the folded point);
* **`VSFX N`**: `VSF P20F accVF (decideFFX P20F N)` (agreed with E2F-C, 2026-11-13 19:08).

Statement 15 (`refinesF20`) is in `LvmE2VRefinesF` (it imports `LvmCertF20`'s format `fmtF20`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open RecursionFast Lvm

/-- **The decision at S2GF** on the stream `sig`, for the native typed record `N`. -/
def decideFFX (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := DM.runOnH (headerBytesP p) (decideProgFF p (fun m pub => TypedV.dTypedX p N m pub) N.m3 vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phi a.pt == a.y

/-- **`V_S` at S2GF** for the native typed record `N`. -/
def VSFX (N : TypedV.TNat) : Lvm.T.SProg := VSF P20F accVF (decideFFX P20F N)

end Lvm.E2V
