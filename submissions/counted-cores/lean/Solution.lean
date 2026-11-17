/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `counted-cores`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded S2GS submission (lvm2 σ_LEAF: `Lvm.CT.submissionS20`): `V` dispatches on `π[0]`
  (`'S'` → `V_S` at S2GS, `VSSX NTS20`: S2GL's merged tape, typed phases at `E2` and mini-bus linear claims, with a
  header without the right leaf's signature, when the static guard `staticOkBS20` holds, otherwise witness sending;
  the node circuit checks that signature in its own second WOTS walk), `P` is the witness-sending encoding,
  `E`/`ext` are S2GS's extractor stage (`stS20`, the shape's window; the right leaf's signature read from it).
  `certified` is `Lvm.CT.certificateS20S`.
-/
import RecursionFast.Contract
import LvmS2GSCert

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

/-- The submission: `counted-cores` at S2GS (`V_S` with the merged tape and the typed phases at `E2`, the mini-bus
ending in three linear claims on `C_main`, the right leaf's signature checked inside the node circuit), guarded by the
static check `staticOkBS20`. -/
def submission : Submission := Lvm.CT.submissionS20

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`): `Lvm.CT.certificateS20S`, S2GS's
certificate chain (`nodeS20` from the guard's facts `sfS20`, with the right leaf's signature from the circuit's second
walk `qSigLeaf_sound`, the refinement `refinesS20` of `VSSX NTS20`, the pinned middle phases `midSpecP_GS`, and the
extractor `ext_eqS20` reading that signature from the window). -/
theorem certified : CertificateR declared submission := by
  unfold submission
  exact Lvm.CT.certificateS20S

end RecursionFast.Challenge
