/-
  The solution of the v4 challenge (`harness/challenge/Challenge.lean.in`, rendered from this
  entry's `claim.json` by `harness/render-challenge.py`). Everything except `submission` and
  `certified` is the rendered stub, copied verbatim: the declared claim (`Declared`,
  `Contract/Certificate.lean`): the knowledge error `2^-129`, the completeness error `0`, the
  verifier query bound `2^16` and the fuel `8 t` of the library's copy extractor. The comparator
  checks that `certified` proves exactly the rendered statement.
-/
import RecursionFast.Contract
import SpartanSromFinal

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((1 : ℝ≥0) / 680564733841876926926749214863536422912)
  δ := ((0 : ℝ≥0) / 1)
  qV := 65536
  fuel t := 0 + 8 * t

/-- The submission: the `spartan-srom` entry (`SpartanSromFinal`). -/
def submission : Submission := SpartanSrom.submission

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`). -/
theorem certified : CertificateR declared submission :=
  SpartanSrom.certificateR_of SpartanSrom.facts declared SpartanSrom.εR1_le_declared
    (show SpartanSrom.qVR1 ≤ 65536 by decide)
    fun t => ⟨show 8 * t ≤ 0 + 8 * t by omega,
      show 0 + 8 * t ≤ 2 ^ 48 + 2 ^ 16 * t by omega⟩

end RecursionFast.Challenge
