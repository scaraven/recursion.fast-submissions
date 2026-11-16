/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `tableless`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded S2GL submission (lvm2 MB-LIN: `Lvm.CT.submissionL20`): `V` dispatches on `π[0]`
  (`'S'` → `V_S` at S2GL, `VSLX NTL20`: S2GU's merged tape and typed phases at `E2`, with the mini-bus's table phase
  replaced by three linear claims on `C_main`, when the static guard `staticOkBL20` holds, otherwise witness sending),
  `P` is the witness-sending encoding, `E`/`ext` are S2GL's extractor stage (`stL20`, the shape's window).
  `certified` is `Lvm.CT.certificateL20S`.
-/
import RecursionFast.Contract
import LvmS2GLCert

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

/-- The submission: `tableless` at S2GL (`V_S` with the merged tape and the typed phases at `E2`, the mini-bus
ending in three linear claims on `C_main`), guarded by the static check `staticOkBL20`. -/
def submission : Submission := Lvm.CT.submissionL20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `Lvm.CT.certificateL20S`, S2GL's
certificate chain (`nodeL20` from the guard's facts `sfL20`, the refinement `refinesL20` of `VSLX NTL20`, the pinned
middle phases `midSpecP_GL` with the mini-bus's three linear claims, and `PhiQGC_eq` for `Φ_Q` at `E2`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateL20S

end RecursionFast.Challenge
