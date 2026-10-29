/-
  The solution of the v4 challenge (`harness/challenge/Challenge.lean.in`, rendered from this
  entry's `claim.json` by `harness/render-challenge.py`) for revision 4.1 of `flock-recursive`.
  Everything except `submission` and `certified` is the rendered stub, copied verbatim.

  **The certificate is open.** `certified` is proved from `FR.Sub4.Open4`, the residuals other
  tracks still own (the slot interface's residual, the node decoder and its links:
  `FRSubmission4Cert`). It therefore states more hypotheses than the challenge's `certified`; the
  comparator rejects it and the harness rates the entry PROVISIONAL (the benchmark runs, the result
  is not comparable). It contains no `sorry`. When `Open4` is proved, `certified` drops its
  hypothesis and nothing else changes.
-/
import RecursionFast.Contract
import FRSubmission4Cert

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((15 : ℝ≥0) / 21267647932558653966460912964485513216)
  δ := ((0 : ℝ≥0) / 1)
  qV := 36000
  fuel t := 211106232532992 + 8192 * t

/-- The submission: revision 4.1 of `flock-recursive` (`FRSubmission4`). -/
def submission : Submission := FR.Sub4.sub4

/-- **The certificate against the rendered claim**, given the open residuals `FR.Sub4.Open4`. -/
theorem certified (h : FR.Sub4.Open4) : CertificateR declared submission :=
  FR.Sub4.certificateR_sub4 declared FR.Sub4.boundsOK_claim h

end RecursionFast.Challenge
