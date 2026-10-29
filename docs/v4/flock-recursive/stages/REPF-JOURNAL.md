# REPF journal

Track REPF (the replay fold: split, fold into `nodeIRows4`, plan, fold lemma, discharge). Worktree rev44.
Build tree `logs/fr-build-REPF` (copy of `fr-build-C1b`); logs `logs/REPF/`. No sub-agents, nothing committed.

## 2026-10-29

- Read C1b/C1/R3/ASK-P/B5 RESULTs, FRNodeRows4, FRNodeRows4Rep*, FRNodeRun4/4S, FRNodeRows4Plan, FRSubmission4Cert.
- HEAD moved to `87519f4` (IMPC) at start; FRNodeRows4 unchanged at HEAD.
- **FRNodeRows4 is edited live by ASK-T** (its tree symlinks the worktree file; orchestrator: do not touch
  `askTG`, its doc, its imports). So REPF edits a private copy `logs/REPF/work/FRNodeRows4.lean`
  (HEAD + REPF hunks only); `mysnap.sh` copies it into `src/`. The REPF hunks go into the worktree file at
  the freeze (listed in the RESULT).
- Build-tree-only patches: `bt-patch.sh` (FR.lean imports of new modules).
- Layout decisions:
  - Fold lemma by a memoized trail (as ASK-P's `trailMS`), merged with `arOf`'s pass, not C1b's
    `repRowsFin` (no SSA/locality argument needed; one pass shared with the ask rows).
  - Segment slots' replay rows (`rtLinkSegW`, 8 rows) can not sit at `repBase = 23·2^15` (inside ASK-T's
    template-row range `[arR2, arR2+arR2N)`); new row base in the free range `[arRb+arNb, linkBase)`.
  - V: slot-0 replay rows evaluated once per call in 20-bit local coordinates (frame part and local part),
    combined per kind by high factors, so full support (N2+N4) pays once.
- Split: `FRNodeRows4Defs` (defs moved verbatim by `logs/REPF/tools/mover.py`, plans `plan1/2.txt`):
  FRNodeRows4's proto defs (mapC … mvC) and the replay defs of Rep/RepS/RepK/RepN/RepW/RsK/LT. Builds;
  all Rep controls green after the move. `askTG`/`XofT` untouched (stay in FRNodeRows4).
- `tplLW` over a context (`tplLWg`, tables `let`-built once; spec accessors as `abbrev`s, `tplLW_eq`).
- Fold: `RepFit`, `repAllRows` (gated by `ArFit`, rejecting row at slot 0's `repSegB`), `mem_node_rep`;
  Fit: `ar_idx_hi`, `slotA_idx`, `rep_fit1`, `rep_fit`, new `hfit4` proof (statement unchanged).
- Orchestrator: `repSegB := 31·2^15 − 2^10` (IMPC2's layout): applied (prototype 1 room 2^10 rows).
- Plan: `FRNodeRows4RepFD` (`trailMR`, `arRepOf`, `arRepOf_eq` = the fold lemma; `repLocF/L`); Plan4
  fields `rp0/rp1` (thunks), `rgF/rgL`; `rvOf` in `LCx`; `repV0_eq`, `repV4_eq`, `slots_val` re-proved.
  First full build (old HEAD + fold) green.
- Orchestrator: ASK-T landed `ae8b8d8`; private FRNodeRows4 rebased (diff `tools/FRNodeRows4.repf-on-ae8b8d8.diff`).
- W switch: `RepOk`/`RepHolds`/`repIRows4` redefined (FRNodeRows4Rep) as the `RTOkW` forms; S-E14's
  three theorems re-stated in RepW over the W versions; `repOk_rtSeg` removed. FRNodeRun4/4S/4Ctrl
  patched in the build tree only (`tools/wswitch_bt.py`, diff `logs/REPF/wswitch.diff`). Discharge
  module `FRNodeRows4RepF` (`repFit_of`, `repFold`, `repOk_rtC1cB`, `gap4Imp_rtC1c`, `gaps4_of_runA`).
- Name clash `N4s.ctlP` (RepCtrl vs FRNodeRun4AskT, now both in FR's closure): renamed mine `repCtlP`.
- Full build (ae8b8d8 + REPF + W patch) green.
- **Process start overflowed the 8 MB init stack** (`lean_run_main` gives `main` a big stack, module
  initialisers run on the process stack): `Tpl.rows`' `gatesAt` is not tail-recursive and `tplEvL`
  N8 has 150,726 gates. Fix: `rowsTR` (`gatesAtGo`, `rowsTR_eq`) in `kRows`. Probe `RepInit2` (closed
  constants, 8 MB) passes. Replay rows no longer kept in the plan (thunks recompute for the fallback).
- Init cost (probe `RepInit`, main thread): `arRepOf 0` 7.4 s (trail ≈ 0.85 + replay rows ≈ 6.5),
  `repFitB` 1.2–1.8 s, `repLocF` 1.0, `repLocL` 1.5, `grows` 0.6 + 1.9 s. Plan init with a big stack
  21.5 s wall vs HEAD 7.8 (+13.7 s): far over the orchestrator's +1 s; needs closed forms.
- Measured (ae8b8d8 + REPF): V(N4) best 1,784.6 / 1,826.8 ms (own / full support; HEAD 445.0 / 484.3)
  — over the 1.6 s stop line: stopped, not optimised. `plan4t init` 19.8–20.5 s vs 7.5–7.9 s (+12.3–12.6 s).
  MxKat PASS (reference adds the replay rows as plain sparse sums). `plan4t check` N2, N4 equal true.
- Kernel: `FRNodeRows4Fit` 3.01 → 6.51 s (new fit lemmas), Plan 0.94 → 1.64, ImplNode4F 0.98 → 1.15.
- HEAD moved to 91e0d61 (IMPC2 modules; b52ee6e renamed ASK-T's ctlP). Froze `FRNodeRows4.lean` into the
  worktree (HEAD's file was unchanged since the rebase). Final build at 91e0d61 + REPF + W diff green
  (2,676 jobs). Axioms 34 decls clean; source rule 455 files, 0 findings. RESULT written.
