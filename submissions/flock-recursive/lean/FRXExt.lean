-- New for `flock-recursive` (BLUEPRINT §6.4; stage S-H2, track L-ext).
import FRXDec
import FRXNode

/-!
# The extractor `ext`, its specification `E`, and `computes`

`ext := extWith decSnark` with the SNARK branch delivered so far; `computes` and the caps follow
from `computesWith` and `DecOk decSnark`.
-/

namespace FR.X

open RecursionFast

/-! ## The program delivered: `ext`, `E`, `computes` -/

/-- **The SNARK branch delivered so far**: a leaf (`'L'`, `'P'`) outputs its witness from the
header (§6.2 step 1, `FRXLeaf.E_leaf`); a node (`'N'`) runs the log index and the ladder read of
level 0 (§6.2 steps 2–3, `read_spec`), replays the Fiat–Shamir chain from the seed it carries
(`FRXDec.chain_dec`), decodes the five levels into `f⁽⁰⁾`'s rows (§6.2 step 4,
`FRXNode.decLevels_sem`), and outputs the node witness read off `f⁽⁰⁾` (§6.2 step 5,
`FRXOutRun.outIR_out`, `FRXNodeRun.E_node`). -/
def decSnark : XIR := decLN3

theorem decOk_decSnark : DecOk decSnark := decOk_decLN3

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
