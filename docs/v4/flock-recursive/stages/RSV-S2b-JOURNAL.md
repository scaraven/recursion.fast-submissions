# RSV-S2b JOURNAL: B′ at 69 cells, the reserve's controls, the chain

Track RSV-S2b, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `b156c27`
(RSV-S's WIP). In parallel with RSV-S2a (`R4Fin`, `R4FrE`, `R4PfFlag`, `R4PfFin`, `FrRS`, `Start`, `Qry`)
and A1′ (uncommitted edits in `FRNodeCircuit4` and the node-row modules). Build tree
`logs/fr-build-RSVS2b`; logs `logs/RSVS2b/`. No sub-agents, nothing committed.

## 1. Setup

- `cp -a logs/fr-build-RSVS logs/fr-build-RSVS2b` (5 s); `b.sh`/`run.sh`/`prof.sh` log to `../RSVS2b/`.
- `mymods.txt` (this track's modules, symlinked to the worktree): `FRSoundness4P4bB`, `P4fDF`, `P4fObl`,
  `P4fCtrl`, `XFront`, `RsvMLE`, `XLaws`, `XRun`, `XRunG` (+ new modules as they are created).
  Everything else is HEAD's text (`snap.sh`), so A1′'s uncommitted edits are not in this tree.
- `patchdec.py` (build tree only): RSV-S's decoder/B3 sorries, plus RSV-S2a's red declarations at HEAD
  (`R4Fin.flag_gFinE`, `flag_gFinB'`; `R4FrE.e_end4`, `not_rejEndE4_node`, `e_in4`, `not_rejInE4_node`,
  `e_fin4`, `not_rejFinE4_node`) and whatever `autosorry.sh` finds next (`autosorry.txt`: build, take
  the first error in a non-MINE module, sorry its enclosing theorem in the tree's copy, repeat).
  The declaration-end regex of the first version stopped at a proof line starting with `]`; fixed.

## 2. Work log
- Baseline (`b0-baseline.log`, then `autosorry.sh`): green with RSV-S2a's `e_bind4`, `start4_of_fields`,
  `gFinPf_reloc` and PORT's `acceptRunL4_node` sorried in the tree.
- **Item 1 (B′ at 69 cells).** Drafted in the scratchpad, test-compiled with `lake env lean` (P4bB 9.9 s),
  installed. P4bB: `rsvV`/`nRsv`/`rsvL`/`rsvHL`, `vStarL4` with the reserve, `PubOKR4`, reads of RS0/RS1
  generalised to `Pub` read before 327/331, `dRS0_4_mono`, `bTerms4` over `Fin 71`, `single_B4` at
  `70·2^128`. A first `pubPart_eq` with `rw [show 69 = 9 + 60 …]; congr 1` hit a `whnf` timeout:
  `congrArg₂` with `Finset.sum_range_add … 9 60` instead. XFront `cellsX`, P4fDF `PubRX`/`PubRSX`,
  P4fObl (`hrcellsX`, `dRS0_4_mono` at 326, B′, RS1), P4fCtrl. XRun's `wV4_of_fields` call broke (as
  expected: `W0X` now batches the reserve cells); in the build tree `R4W0R` gets the predicted interface
  `hcl : P.cells ++ P.rcells = …` (sorried bodies) and XRun calls it at `cellsX`. Green (`b2-xrun.log`).
- **Item 2.** `FRSoundness4RsvCtrl` (7.3 s standalone): `truthChild_pos`, `childBad_neg` (`zcT_ne`, the
  concrete point `τ = 0, η = 1` gives `−1`; `ZCwE4` at every `η ≠ 0`), `kindChange_pos`/`kindChange_mat`
  (`mle_mStack_row`/`matMLE_hiRow` + `hiPt_self` at 22 and 23), `n8_zero`, `n8_neg`. Imported by P4fCtrl.
- **Item 3.** `XLaws.RsvZero`, `RunFacts4.node ∧ RsvZero`; XRun via `rsvZero4` (requested of RSV-S2a;
  stubbed in the tree by `patchdec.py`; the first stub used `P4b.rsvV`, which `R4FrE` does not import:
  restated with `readF`). `FRNodeStmtR4`: `StmtN4R`, `truthChildV`, `truthChildV_rsvL`, `evalM_childV`
  (first form with `congr 1` on the triple timed out at `whnf`: a `key` equation on the sum, then
  `rw`), `rsv_of_tail` (phases 16 and 23 refuted on the accepted prefixes; `generalize` the entries
  rather than `set`, which left two copies), `nodeRunR_X`.
- Orchestrator: A1′ landed (`e464756`); re-snapshotted; `Qry.ks_queriesC4` red at `e464756`
  (`8783 ≤ qV4`), sorried in the tree (RSV-S2a's module). `FRNodeCircuit4` now this track's: the three
  laws and `nodeLaws4C'` generalised over `St`; XFinal passes `hSt := id`; `nodeSoundR_X`, `ks_rev4R`.
  Green: `FRNodeStmtR4 FRSoundness4P4fCtrl FRSoundness4XRunG FRSoundness4XCtrl FRNodeSound4K`.
- Spacer check (orchestrator, after A1′): nothing of this track ranges over trace entries (RESULT §4).
- Axioms (`axioms.log`): 20 theorems, standard three only. Source rule: 410 files, 0 findings.
