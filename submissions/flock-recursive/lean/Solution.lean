/-
  The solution of the v4 challenge (`harness/challenge/Challenge.lean.in`, rendered from this
  entry's `claim.json` by `harness/render-challenge.py`) for revision 4.1 of `flock-recursive`.
  Everything except `submission` and `certified` is the rendered stub, copied verbatim.

  **The certificate is closed** (stage FEL). `certified` is the challenge's statement, with no
  hypothesis: the former residual `FR.Sub4.Open4F` (`= Gaps4`, the slots' circuit gaps at the proof
  decoder) is proved, `FR.Sub4.open4F_holds` (`FRSubmission4Fin`, from `FR.N4s.gaps4_fel`). It
  contains no `sorry`; its axioms are `propext`, `Classical.choice` and `Quot.sound`.
-/
import RecursionFast.Contract
import FRSubmission4Fin

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

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`). -/
theorem certified : CertificateR declared submission :=
  FR.Sub4.certificateR_sub4F declared FR.Sub4.boundsOK_claim FR.Sub4.open4F_holds

end RecursionFast.Challenge
