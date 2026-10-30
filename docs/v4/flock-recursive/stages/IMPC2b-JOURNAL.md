# IMPC2b journal (track IMPC2b: IMPC2 step 3, `atImp_bitR` and the run proofs)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`), HEAD `91e0d61`. Build tree `logs/fr-build-IMPC2b`
(cp -a of `fr-build-IMPC2`, `snap.sh` onto HEAD, `patch.py` applied: arena constants, phase-1 `askTG` fold,
`askTGI`, removal of `askFold_askT`/`gap4Imp_of_askT`; the `ctlP` rename is moot at HEAD). Logs `logs/IMPC2b/`.

## Log

- 22:50 tree set up; `patch.py` applies unchanged to HEAD (`patched`). Baseline build
  `FR Solution FRSubmission4Fin FRNodeRows4AskBS`: green, 2,675 jobs (`build0.log`).
- Plan: `FRNodeRun4BL` (bit order of `F.ofBytes`, `natLE`/`idxOfF`), `FRNodeRun4BS` (`PosBits`, `StmtBits`,
  the kind tie, `atImp_bitR`), `FRNodeRun4BR` (`execA_ri`, `flag_stmt`, bit/aux conjuncts, `SlotRunB`,
  `gap4Imp_of_bitsR`).
- 23:10 generator guards in `FRNodeRows4AskB` (soundness of the run proofs; honest rows unchanged):
  `riOf k n` (an `idx`/`shrN` only on earlier registers; a byte `const` only if the same at every kind),
  `bitRowsB` (`r < b` at a `bitOf`), `auxBRows` (register below the count, `n` cells), `ansRows` (cells in
  the bit area), `idxSrc` (`.dig`: bit index < 256), `globRows` (`1 ≤ z`).
- 23:20 orchestrator: REPF committed (407260d). Re-snapshot; `patch.py` applies unchanged. New
  `patch2.py` (tree only): `FRNodeRows4RepF` imports `FRNodeRows4AskBS` and states `gap4Imp_rtC1c` /
  `gaps4_of_runA` over `withBitsB askAq` via `gap4Imp_of_bitsB` + `askFold_bitsB` (patch.py deletes
  `gap4Imp_of_askT`, whose fold is false once `bitTGB` is folded).
- 23:25 **HEAD's `FRNodeRows4AskBS` breaks at 407260d**: REPF's `FRNodeRows4Defs` adds `FR.N4s.akS`, which
  shadows `FR.Circ.akS` in `tplExt4_tw_imp` (namespace `FR.N4s`). Fixed (`Circ.akS`). HEAD's `FR` does
  not import AskBS, so HEAD's FR is unaffected.
- 00:40 modules green (chk): `FRNodeRun4BL` (bit order, `SrcV`/`StmtBits`/`PosBits`/`SrcOk`, `execA_ri`,
  `srcOk_of`, `selRows_ev`), `FRNodeRun4BR` (`impA_bits`, `xof_bits`, `aux_bits`, `stFlag`, `flag_stmt`),
  `FRNodeRun4BS` (`first_ask`, `seed_rows`, `stmtBits_of_glob`, `posBits_of_glob`), `FRNodeRun4BF`
  (`SlotRunB`, `slotRunA_of_bits`, `gap4Imp_of_bitsR`, `gaps4_of_runB` at `rtC1c`). Generator: `stCells`
  (named, so the proof can refer to the statement element's cells).
- Next: `atImp_bitR` (stmt reads; siblings with the kind tie), then the full build, axioms, profiles.
- 00:55 full build `FR Solution FRSubmission4Fin FRNodeRun4BF` green (2,683 jobs, `build3.log`) after
  patch2 (3): REPF's control `arRb + arNb < repSegB` fails with IMPC2's constants (equality); `≤` in the tree.
- 01:05 `bitTGS` (statement reads only, IMPC2b phase 2a) + `FRNodeRun4BT` (`rdWin_ev`, `stRd_rep`,
  `atImp_bitS`, `xofA_read`). Decision: the tree folds `bitTGB` **and** `bitTGS` into `askTG` (patch2 (1));
  `askFold_bitsB` removed from AskBS (false under that fold; `gap4Imp_of_bitsB` keeps `hfoldA` as a
  hypothesis); BF's `gaps4_of_runB` removed; the certificate-level form is BT's `gaps4_of_runS`.
  patch2 (2): RepF's `gap4Imp_rtC1c`/`gaps4_of_runA` deleted (they call the deleted `gap4Imp_of_askT`).
- source rule: 462 files, 0 findings.
- 01:40 build `FR Solution FRSubmission4Fin FRNodeRun4BT bitstat2` green (5,252 jobs). `bitstat2`: 0 failR
  (bitTGB, bitTGS, askTG), askTG rows 114,320 / 135,997; residual imports p0 7,426 siblings, p1 7,426 + 5
  (rsWeight, evalL, evalM, shiftTarget, targetS); residual flags 0 / 0; residual aux 871 felems each.
  Axioms: 36 declarations OK. Profiles in RESULT §4. `bitV` → `srcVal` (clash with `Rev4.bitV`).
- Stopped: siblings' `ATImp` (kind tie) not attempted; RESULT §5 has the route.
