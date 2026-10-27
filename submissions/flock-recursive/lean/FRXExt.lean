-- New for `flock-recursive` (BLUEPRINT §6.4; stage S-H2, track L-ext).
import FRXReadDefs

/-!
# The extractor `ext`, its specification `E`, and `computes`

`ext := extWith decSnark` with the SNARK branch delivered so far; `computes` and the caps follow
from `computesWith` and `DecOk decSnark`.
-/

namespace FR.X

open RecursionFast

/-! ## The program delivered: `ext`, `E`, `computes` -/

/-- **The SNARK branch delivered so far**: the log index (§6.2 step 2) and the ladder read of
level 0 (§6.2 step 3, `read_spec`); the decoding and the output follow (S-H2-RESULT). -/
def decSnark : XIR := decRead

theorem decOk_decSnark : DecOk decSnark := decOk_decRead

/-- **The extractor program** `ext := toProg 2^26 3 extIR` (§6.4). -/
def ext : XProg := extWith decSnark

/-- **The extractor specification** (B-8): `ext`'s decoded output within `fuel`. -/
def E : Digest → Proof → Log → Option Wit := Eof ext fuel

/-- **`Computes ext E fuel`**: the certificate's `computes` conjunct. -/
theorem computes : Computes ext E fuel := computesWith decOk_decSnark

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem ext_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ ext.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWith decOk_decSnark.size⟩

end FR.X
