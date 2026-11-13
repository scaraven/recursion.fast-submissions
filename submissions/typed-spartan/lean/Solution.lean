/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `typed-spartan`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded typed submission (lvm2 roll 8, B1: `LvmSubmissionST.submissionB20`): `V`
  dispatches on `π[0]` (`'S'` → `V_S` of the typed bus-free backend at P20, `VST P20 NT20`, when the typed
  static check `staticOkB20` holds, otherwise witness sending), `P` is the witness-sending encoding,
  `E`/`ext` are WP-13a's extractor. `certified` is `LvmCertT20.certificateT20` (the typed certificate).
-/
import RecursionFast.Contract
import LvmCertT20

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((1 : ℝ≥0) / 340282366920938463463374607431768211456)
  δ := ((0 : ℝ≥0) / 1)
  qV := 16384
  fuel t := 70368744177664 + 8192 * t

/-- The submission: `typed-spartan`, the typed backend (`V_S` at P20 on the B program's typed instance),
guarded by the typed static check. -/
def submission : Submission := Lvm.T.submissionB20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `LvmCertT20.certificateT20`
(`kcertSJ (midSpecR_T₂ …)`, `NodeSound` on `GoodT`, the refinement of `VST P20 NT20` to `typedProg`, the guard's
facts `sf20`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateT20

end RecursionFast.Challenge
