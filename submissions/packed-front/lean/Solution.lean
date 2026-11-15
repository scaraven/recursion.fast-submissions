/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `packed-front`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded S2GF submission (lvm2 E2-F: `LvmCertF20Inst.submissionF20`): `V` dispatches on
  `π[0]` (`'S'` → `V_S` at S2GF, `VSFX NTF20`: the front at `E2`, the coordinate-split typed phase, when the static
  guard `staticOkF20` holds, otherwise witness sending), `P` is the witness-sending encoding, `E`/`ext` are S2GF's
  extractor (`EXF20`/`extXF20`). `certified` is `LvmCertF20Inst.certificateF20S` (statement 18).
-/
import RecursionFast.Contract
import LvmCertF20Inst

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

/-- The submission: `packed-front` at S2GF (`V_S` with the `E2` front and the coordinate-split typed phase),
guarded by the static check `staticOkF20`. -/
def submission : Submission := Lvm.CT.submissionF20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `LvmCertF20Inst.certificateF20S`,
S2GF's certificate chain (the pinned middle phases `midSpecPinF20`, `NodeSoundM` from `nodeF20` on stream-block pairs
and the window fact `childF20_win`, the refinement `refinesF20` of `VSFX NTF20`, the extractor agreement `ext_eqF20`,
the guard's facts `sfF20`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateF20S

end RecursionFast.Challenge
