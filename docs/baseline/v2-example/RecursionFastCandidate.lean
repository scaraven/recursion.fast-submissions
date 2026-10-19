-- Provenance: copied from scaraven/recursion.fast `submissions/baseline/RecursionFastCandidate.lean`, branch `main` at commit 77e550b, on 2026-10-19. Read-only copy; the source is authoritative.
/-
# recursion.fast v2 baseline submission `P_triv` ("proof = the witness tables")      (UNTRUSTED)

Reading order: `Protocol` (`P_triv k`, `triv_secure`; adapted from the organiser's
`Controls/Toy.lean`), `Compiled` (what the organiser's compilation makes of it: the honest tape has
`5 · 2^(k+11)` bytes, and no tape is accepted, since the rounds section alone exceeds the cap; why
the entry is listed, unranked), `Submission`
(`cfg`, `submission k`, the declared record at `k = 24` and its certificate), `Negative` (the same
protocol with the call before round 0 starved of fuel is not secure). The rendered
challenge and the solution the comparator checks are in `audit/`; `README.md` is the worked
example of a submitter's obligations.
-/
import RecursionFastCandidate.Protocol
import RecursionFastCandidate.Compiled
import RecursionFastCandidate.Submission
import RecursionFastCandidate.Negative
