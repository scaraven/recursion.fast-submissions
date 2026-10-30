# SIB journal (siblings + closure generator)

- 2026-10-30 00:10 start at v4/rev44 HEAD 97d578b. Build tree `logs/fr-build-SIB` = copy of `fr-build-IMPC2b`,
  re-snapshotted onto HEAD (snap.sh, no patches; MINE = IMPC2b's 8 modules as symlinks). Logs `logs/SIB/`.
- Baseline build `FR Solution FRSubmission4Fin bitstat2` started (build0.out).
- 00:20 baseline green (5,252 jobs). Design: new `FRNodeRows4AskC` (below `FRNodeRows4`): `sibTG` (IMPC2's sibling rows +
  process-start checks `sibAt`/`sibPosOk` so the ATImp proof needs no decision over tables) and the closure `TG.close`
  (covers `closeCov` = possible imports/foreign flags less asks, `bitOf`, replay ops `isRep`; failing row at an import `A`
  does not cover / a foreign flag neither `zPin` nor `stFlag` discharges; at the first ask `bitNxAll`, every `bitOf`
  followed by its `selectHalf`). `askTG := (FOLD2's chain |>.addE sibTG).close …` (`addE`: `A` not asked at `B`'s ops, so
  `impcCov`'s window test is not re-evaluated at the siblings).
- 00:35 probe `sibstat`: 0 failing rows (sibTG 16,594 / 18,336 rows; closure 0 rows; `bitNxAll` true); askTG 130,914 /
  154,333 ≤ 180,560.
- 00:40–01:30 cost: in-process `sibtime` (trail + group/fit, min of 6): full ≈ +185–250 ms per prototype; sibTG alone ≈ +85.
  Timing noise ±50–100 ms under load (perf unavailable: paranoid 4). Cuts so far: `sibSegs` (5 fSibs parts), `opForeign`
  (no rows built), `TG.close` evaluates `A.cov` once per op, ext asked only at `extCan` ops. Final A/B at the end.
- `FRNodeRun4CA` (proved): `opOut_imp`, `opForeign_eq`, `opOut_foreign`, `tplExt4_flags` (a template's output is never an
  import nor foreign), `tplExt4_isNone` (whether a template takes an op does not depend on the bodies), `stepOut_imp_of`,
  `stepOut_foreign_of`.
- 01:35 `FRNodeRun4CB` (closure soundness) green: `AT.close`, `AT.addE`, `atAsk_close`, `atImp_close`, `atOk_close`,
  `atOk_addE`, `impB_sub`, `trail_forsF`, `SlotRunC` (aux felems + `impQP` replay imports), `slotRunB_of_close`.
  Design fix on the way: the flag check must also run where `A` covers the op (e.g. `impcTG`'s `assertZero`): rows split
  into `impRows` (imports `A` does not cover) and `forRows` (every foreign-capable op).
- 01:50 `FRNodeRun4CS` green: `SibOk`, `atImp_sib`, `xofA_sib`. 02:20 `FRNodeRun4CD` green: `sibAt_spec`, `sib_bytes`,
  `sib4_getD`, `ansN_succ`, `phAns_getD`, `posOf4_bit`, `lvl_mkTab`, `mkTab_ans_lt`, kind tie `trM4_slot`, `posBit_eq`,
  `sibOk_of`. Next: `FRNodeRun4CT` (fold `askFold_close`, `gap4Imp_of_close`, `gaps4_of_runC`).
- 02:40 `FRNodeRun4CT` green: `withSib`, `withClose`, `askFold_close` (rfl), `close_rowsB`, `gap4Imp_of_close`,
  `gap4Imp_rtC1cC`, `gaps4_of_runC`; controls `SibCtl.*`. BT: `askFold_bitsS`/`gap4Imp_rtC1cS`/`gaps4_of_runS` removed.
  `SlotRunC` made `A`-aware (p0's `evalM` is `rsvTG`'s): residual p0 0 imports, p1 5 replay ops; felems 871 each.
- 03:10 `plan4t init` A/B: **+2.7 s user** (siblings only: +2.7; full: +2.7 → closure ≈ 0). In-process trail+group
  explains ≤ 1 s. `bitNxAll` passed as a value (no change). Not resolved: §6.1 of the RESULT (options a–c).
- 03:30 final: `FR Solution FRSubmission4Fin` green (`build-final.out`), 36 axioms clean, source rule 0 findings,
  kernel profile (CS 4.38 s: `atImp_sib`). RESULT written. **Handover**: decide §6.1 (init); if (a), add a `skip`
  parameter to `TG.close`/`closeCov`/`impQX` (skip := `isRep || sibCov`), drop `addE sibTG` from `askTG`.
