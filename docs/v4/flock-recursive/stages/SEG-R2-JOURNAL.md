# SEG-R2 journal (track SEG-R, stage R2: the fold)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `9db5ee0` = CF2). Build tree `logs/fr-build-SEGR2`
(copy of `fr-build-SRA`, which was HEAD-built). Logs `logs/SEGR2/`. SEG-R1b's files (`FRNodeRows4RepSeg`,
`FRNodeRows4RepSegT`, `FRVIRTplSegT`) are not edited in the worktree; my versions of the first two live in
`logs/SEGR2/overlay/` until SEG-R1b is committed.

## 2026-10-30

- Read SEG-R1/SEG-R0/SIB/CF2 RESULTs, SEG-R.md, the SIB+SEG-R1 review.
- **Import-order finding**: `rtC1d`/`rtSeg1`/`kRSS`/`kTSS`/`kSTS` and `rtKD`/`rtEvZ` are defined in modules
  downstream of `FRNodeRows4` (`RepSegK` imports `RepK` → `RepCFP` → `RepFD` → `FRNodeRows4`), so `repAllRows`,
  `askTG` and the plan cannot name them. Route (as REPF's `FRNodeRows4Defs`): move the definitions verbatim
  (same names, namespaces) into a new upstream module `FRNodeRows4SegD` imported by `FRNodeRows4`; the
  proofs stay. This edits `RepSeg`/`RepSegT` (delete the moved defs) — deferred to after SEG-R1b's commit.
- Item 3 route: `TG.repF A rc` (an uncovered `isRep` op gets `failRT`), applied in `askTG` before the
  closure with `rc = (rtC1d π).cov`; then `impQP (rtC1d π) (withRep …) π = []` by a structural lemma.
- Built: SegD (moved defs), Defs bands, ArenaPlace cut, `TG.repF`/`AT.repF`, Fit two-band lemmas, Plan `rv1`
  (`repV1_eq`), RepF/CT at `rtC1d`/`withRep`, `SlotRunF`, `gaps4_of_runF`. Traps: `simp only [literal defs]` inside
  an `if` condition broke the `Decidable` instance (use `rfl` facts + `by_cases`/`rw [if_pos]`); `simp` with
  `repB = 2^40` unfolded hit max recursion in a control (split into conjuncts, `decide`).
- SEG-R1b committed (`bb0880c`); its files byte-equal to my frozen copies; trimmed versions applied to the worktree.
- Final: build green (2,705 jobs), axioms clean, source rule 0, probes: 0 failRT, 38,805 rows/0 rejecting, 0 cell
  clashes, plan4t check N2/N4/N8 equal, MxKat PASS; init +0.5 s, V(N4) +56–80 ms. RESULT written.
