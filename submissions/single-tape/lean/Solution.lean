/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `single-tape`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded S2GU submission (lvm2 U-TAPE: `Lvm.CT.submissionU20`): `V` dispatches on `π[0]`
  (`'S'` → `V_S` at S2GU, `VSUX NTU20`: the merged tape and its wire at `E2`, the typed phases at `E2` with `Φ_Q`
  evaluated by `E2` products, when the static guard `staticOkBU20` holds, otherwise witness sending), `P` is the
  witness-sending encoding, `E`/`ext` are S2GU's extractor stage (`stU20`, the shape's window). `certified` is
  `Lvm.CT.certificateU20S`.
-/
import RecursionFast.Contract
import LvmS2GUCert

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

/-- The submission: `single-tape` at S2GU (`V_S` with the merged tape at `E2` and the typed phases at `E2`),
guarded by the static check `staticOkBU20`. -/
def submission : Submission := Lvm.CT.submissionU20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `Lvm.CT.certificateU20S`, S2GU's
certificate chain (`nodeU20` from the guard's facts `sfU20`, the refinement `refinesU20` of `VSUX NTU20`, the pinned
middle phases at `midMk 4`, and `PhiQGC_eq` for `Φ_Q` at `E2`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateU20S

end RecursionFast.Challenge
