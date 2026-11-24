/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for lvm6. Everything except `submission`,
  `certified` and the check `declared_eq` is the rendered stub, copied verbatim.

  `submission` is `Lvm6.Cert.submission6`: the witness-sending branch and the leanVM-inspired SNARK
  branch behind the guard `guard6`, run as the byte-level twin `VwithT` behind the kind test `isSB`
  (`VwithS`); `certified` is `Lvm6.Cert.certified6` (module `Lvm6Cert`).
-/
import RecursionFast.Contract
import Lvm6Cert

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((1 : ℝ≥0) / 340282366920938463463374607431768211456)
  δ := ((0 : ℝ≥0) / 1)
  qV := 16384
  fuel t := 140737488355328 + 8192 * t

/-- The submission: `Lvm6.Cert.submission6`. -/
def submission : Submission := Lvm6.Cert.submission6

/-- The rendered claim is `Lvm6.declared6`. -/
theorem declared_eq : declared = Lvm6.declared6 := rfl

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`). -/
theorem certified : CertificateR declared submission := by
  rw [declared_eq]
  exact Lvm6.Cert.certified6

end RecursionFast.Challenge
