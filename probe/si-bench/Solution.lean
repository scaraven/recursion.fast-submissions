/-
  **Benchmark probe (stage S-I), not the entry's solution.** On an `eval/*` branch this file replaces
  `submissions/flock-recursive/lean/Solution.lean`, so that the harness's certificate job builds only
  the badge path (`FRSubmission4V`, 128 modules) and fits `build_s` on an EPYC 7763; the entry's
  `Solution` (`FRSubmission4Cert`'s closure, 254 modules) did not (run 40805207819: 600 s).

  `submission` has the entry's `V` (`FR.Sub4.V4F` = `VC4 implCN (implN4F …) cells4`), `P`, `ε`, `δ`
  and `qV`, so `acc`, which is all the benchmark runs, is the entry's. Its `E`, `ext` and `fuel` are
  the library's witness-sending ones, which the benchmark never runs. `certified` assumes its own
  statement: the comparator rejects it and the harness rates the run PROVISIONAL, which is what lets
  the benchmark run. It proves nothing and is never to be submitted.
-/
import RecursionFast.Contract
import RecursionFast.Library.WitnessSending
import FRSubmission4V

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

/-- The probe's submission: the entry's `V`, `P`, `ε`, `δ`, `qV`; the library's extractor. -/
def submission : Submission where
  V := FR.Sub4.V4F
  P := fun _ _ w => .ret (WitnessSending.encodeF w)
  E := WitnessSending.E
  ext := WitnessSending.ext
  ε := FR.Sub4.epsRQ
  δ := 0
  qV := FR.Rev4.qV4
  fuel := WitnessSending.fuel

/-- A placeholder that assumes its statement (the probe is PROVISIONAL by construction). -/
theorem certified (h : CertificateR declared submission) : CertificateR declared submission := h

end RecursionFast.Challenge
