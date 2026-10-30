# FEL journal (the `felems` residual; the certificate closed)

Stage FEL, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `e447823` = SEG-R2). Build tree
`logs/fr-build-FEL` (a copy of `fr-build-SEGR2`'s tree with its `.lake`; `snapF.sh` symlinks every module of the
worktree into `src/` and regenerates the roots). Logs `logs/FEL/`. Every lake/lean/probe run in a 16 GB scope under
`timeout`. Nothing committed, no sub-agents, `prover/` not touched (E1b owns it).

## Log

- Read FEL.md, FEL-review.md, SEG-R2-RESULT. Chose the review's **S3** (override only the `dotKF` arm, `tplExt4A`)
  over the `TCtx` field: 107 modules downstream of `FRNodeRows4Defs` against 365 of `FRVIRTplCore`, no anonymous
  constructor edits, and B1's chain stays as it is (`tplExt4A_okK` is `tplExt4_okK` plus one arm, `dkX_ok`, a copy
  of `tplExt_ok`'s ≈ 10-line `dotKF` case).
- Generic lemmas stated at `tplExt4 F R tc` (`stepOut_imp_of`, `stepOut_foreign_of`, `impB_sub`, `atImp_close`,
  `atOk_close`) generalised to any extension whose outputs are neither imports nor foreign (`ExtFl`), not duplicated.
- `colA`'s data (S1): per prototype a table column register ↦ window elements (`colT0`, `colT1`, closed constants,
  computed once at process start); `colA` is a `List.lookup` (a register not in the table is refused). Generic
  `colEs`/`colCells` (S2) for the controls (toy window map, toy proof size: no `winE`, no `piSizeOf seq4` in the
  kernel).
- `Defs` imports `FRNodeRows4AskI` (the design's fallback; no cycle: `AskI`'s closure does not contain `Defs`), so no
  `Win` cut. `pvP` moved from `AskIR` to `Defs`.
- First build: one error (`planData4_rows`: `Xof 1` vs `XofC 1 (protoLay 1).ctx` needs a `rfl` after `rw`). Then
  `FRNodeRun4FE` (two tactic fixes). `lake build FR Solution` green, 2,707 jobs.
- Axioms: 31 declarations incl. `Challenge.certified` ⊆ {propext, Classical.choice, Quot.sound}. Source rule 482
  files, 0 findings.
- felstat: 871 aliased / 0 refused / 0 failRT per prototype, 27,856 cells all in region `π`'s arena₁, rows
  130,914 / 154,333 unchanged, plan walk's instances = `protoCS`'s.
- init A/B (first form, two independent tables): +0.8 s user. Lever: prototype 1's table reads prototype 0's
  elements (`esC0`, keyed by the field's bytes `(x, len)`; `colEWC_eq`). Second A/B: ≈ +0.3 s user (noisy, load 3–13).
- MxKat PASS; V(N4) A/B equal within noise; `plan4t check` N2/N4/N8 equal.
- Orchestrator addendum (n2, n3): `repRow0`'s and `mRowModel4_eq`'s docstrings reworded (no statement change).
- Profiles: changed on-path modules +0.28 s; 40 modules newly on `certified`'s path (the gap chain) +29.2 s type
  checking (≈ 420 / 600 s).
- Removed the unused generic `colAW`; final rebuild green (2,707 jobs), axioms and source rule re-run clean.

## Handover (if needed)

Everything is in `FEL-RESULT.md`. The certificate is closed (`certified` has no hypothesis).
