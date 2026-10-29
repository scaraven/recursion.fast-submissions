# R3 journal (track R3: chain templates / `rsWeight` replay for the previous-node slot)

- 2026-10-29: read R-OPS, review, R0, C1, D1p, B5. Build tree `logs/fr-build-R3` = copy of
  `fr-build-IMP` (HEAD 616b57c), IMP's probes moved to `probe-imp/`, `snap.sh` re-run (MINE:
  `FRVIRTplChain*`, `FRNodeRows4RepRs*`).
- Orchestrator change of goal (mid-track): drop the 10 ms kill line and V optimisation; build the
  simplest sound binding of `rsWeight` (kind factor included) for slot 0 within the hard caps (V ≪ 10 s,
  plan init ≪ 4 s extra, spare-region fit, kernel time). Sparse rows via C1's `KOp`/`RTOkW` accepted.
- Orchestrator notes: wait loops must wait on a PID / log line with `timeout`, never `pgrep -f`
  (none written here); R1 found the public-op route unsound at depth ≥ 2, so `rsWeight` by replay is
  the route; C1b builds `evalL`/`targetS` (RepL*/RepT*); replay plan init for all templates ≤ ≈ 3 s.
- Skeleton sizes (`probe/R3Skel`): blocks 118/125/146, fixed bits 1,689/1,899/2,223 (N2/N4/N8).
- Design: `K`-general template (claims have real f₁ cells; templates cannot assert f₁ = 0); kind
  factor by Frobenius (`W₀^(2^k)·G` per block, `block_frob`) instead of 2k products per stage.
- Built `FRVIRTplChain` (GM builder + Ok lemmas + chains), `FRNodeRows4RepRsV` (`rsRef`,
  `rsWeightF4_ref`), `FRNodeRows4RepRs` (`rsG`, `ok_rsG`), `FRNodeRows4RepRsK` (`kRS`, `kRS_ok`,
  `rtRs`, `rtR3`), `FRNodeRows4RepRsCtrl`. All green, axioms clean, source rule 0.
- KAT (`probe/R3Rs`): honest witness = rsWeightF4 for N2/N4/N8, K and F points; growsVal3 = rows3.
- Caps: 472,310 rows / 2.99 M terms kind-muxed; build 2.9–3.1 s + grouping 0.94 s (core 31) —
  over the ≈ 3 s init budget for all replay templates; V +0.72 s VM. GM `bind … ret` was
  quadratic (4.6 s → 0.8–1.1 s for N4 after `GM.map`).
- Wrote R3-RESULT.md: verdict sound but init-cap fail; closed-form route (§4.2) recommended.
