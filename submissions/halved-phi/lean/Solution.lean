/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `halved-phi`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded S2GT submission (lvm2 S2GT: `Lvm.CT.submissionG20`): `V` dispatches on `π[0]`
  (`'S'` → `V_S` at S2GT, `VSGX NTG20`: the front at `E2`, the typed phases at `E2` with `Φ_Q` evaluated by `E2`
  products, when the static guard `staticOkBG20` holds, otherwise witness sending), `P` is the witness-sending
  encoding, `E`/`ext` are S2GT's extractor stage (`stG20`). `certified` is `Lvm.CT.certificateG20S`.
-/
import RecursionFast.Contract
import LvmS2GTCert

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

/-- The submission: `halved-phi` at S2GT (`V_S` with the `E2` front and the typed phases at `E2`), guarded by
the static check `staticOkBG20`. -/
def submission : Submission := Lvm.CT.submissionG20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `Lvm.CT.certificateG20S`, S2GT's
certificate chain (`nodeG20` from the guard's facts `sfG20`, the refinement `refinesG20` of `VSGX NTG20`, the pinned
middle phases at `midMk 4`, and `PhiQGC_eq` for `Φ_Q` at `E2`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateG20S

end RecursionFast.Challenge
