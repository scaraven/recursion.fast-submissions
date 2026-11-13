/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `lone-root`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded typed submission (lvm2 roll 8, B1: `LvmSubmissionST.submissionB20`): `V`
  dispatches on `π[0]` (`'S'` → `V_S` of the typed bus-free backend at P20, `VST P20 NT20`, when the typed
  static check `staticOkB20` holds, otherwise witness sending), `P` is the witness-sending encoding,
  `E`/`ext` are WP-13a's extractor. `certified` is `LvmCertM20.certificateM20` (lvm2 roll 11, M′: one commitment,
  `C_rec` merged into `C_main`'s stream block).
-/
import RecursionFast.Contract
import LvmCertM20

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

/-- The submission: `lone-root`, the typed backend (`V_S` at P20 on the B program's typed instance),
guarded by the typed static check. -/
def submission : Submission := Lvm.T.submissionB20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `LvmCertM20.certificateM20`, M′'s
certificate chain on the typed objects (`kcertSM` through `midSpecM_T₂` on `midM reloc20 (midT₂ Ti20)`, `NodeSoundM`
from `nodeT20` on stream-block pairs and the window fact `win20`, the refinement of `VST P20 NT20` to `PSWithM`, the
guard's facts `staticFactsT20`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateM20

end RecursionFast.Challenge
