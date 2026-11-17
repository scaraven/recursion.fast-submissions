/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `pruned-caps`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded S2GB submission (lvm2 MP-B cap pruning: `Lvm.CT.submissionS20B`): `V` dispatches on
  `π[0]` (`'S'` → `V_S` at S2GB, `VSSB NTB20`: S2GS's with each opened level's cap pruned to its root (`L0`: two
  nodes), the cap layer rebuilt from the paths' tops and a π tail of the uncovered nodes, checked by a heap of node
  queries, when the static guard `staticOkBB20` holds, otherwise witness sending), `P` is the witness-sending
  encoding, `E`/`ext` are S2GB's extractor (`EXB20`/`extXB20`: the static part and the tail).
  `certified` is `Lvm.CT.certificateS20B`.
-/
import RecursionFast.Contract
import LvmS2GBCert

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

/-- The submission: `pruned-caps` at S2GB (S2GS's `V_S` with the opened levels' caps pruned to their roots and
the cap layer checked by a heap of node queries), guarded by the static check `staticOkBB20`. -/
def submission : Submission := Lvm.CT.submissionS20B

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `Lvm.CT.certificateS20B`, S2GB's
certificate chain (`nodeB20` from the guard's facts `sfB20`, the refinement `refinesB20` of `VSSB NTB20` onto the
expansion `fillB`, the pinned middle phases `midSpecPinB20`, and the extractor equation `ext_eqB20`). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateS20B

end RecursionFast.Challenge
