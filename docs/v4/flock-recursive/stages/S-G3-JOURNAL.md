# S-G3 JOURNAL: `hAcc` (accepted run ⇒ `W` witness or `AcceptTail`)

Base HEAD `625cc36`. Build tree `logs/fr-build-SG3` (HEAD snapshot via `snap.sh`, S-G3's modules
symlinked in; S-E8 edits `FRVIR*`/`FRVerifierImpl*`, S-H2j edits `FRX*` in the worktree).

## 2026-10-28

- Read TRACK-RULES, S-G2 RESULT (pass 1, pass 2), FRLog (`IsChain`, `Matches`, `back`), FRVIRChain
  (`fsQ_gen`), FRVIRSpec (`runSeq_runIR`, `refPhase`, `exec_skeleton`), FRVerifier (`Vwith`,
  `V_W_sound`, `acc_eq`), FRXSpec (`E_W`).
- Plan: `FRSoundnessAccRun` (items 1–2: runLog → trace, chain from links, `runLog_chain`, the `W`
  branch with the size bound `(encode w).size < 2^64` from `Rel`), then `FRSoundnessAccFin`
  (item 3 bridges), `FRSoundnessAcc` (item 4).
- `logs/fr-build-SG3/snap.sh` rewritten from S-G2's: no `rm` (`mv -f` over links, `ln -sfn`), S-G3's
  modules linked only when they exist.
- `FRSoundnessAccRun`: `runLog_trace` (induction on `OProg`, `runLog_query`), `path_of_links`
  (induction on the chain position, `predIdx_lt`, `ansIdx_self`, `back_fuel`), `matches_fsQ` (the
  item checks from `fsMsgs_items`, `fsMsgs_aligned`, `fsMsgs_ctl`; no new `decide` on the table),
  `runLog_chain`. `W` branch: the size bound needed `|signedWords p| < 2^32` (first try `2^25`
  was false: `qV · 2^17 ≈ 2^30.3`). `fsItems_length` already existed in `TailO`.
- `FRSoundnessAccFin`: `FinLog` (the verifier's checks in log terms, column folds `y` a parameter)
  and `acceptTail_of_finLog`: built on the first try. Part C: `msgAt_fsQ`, `readK_fsQ`, `padV_eq`.
- `FRSoundnessAcc`: `hAcc_of` (case split on `kindOf π`; `PKind`'s constructor order is `W`,
  `bad`, `snark`), `hAcc_of_E`, `finalLaw_of_run`.
- One `congr 1` took 2.65 s (K sums); replaced by `congrArg`.
- HEAD moved to `5b2fb93` (S-H2 part 19, `FRX*` only) during the stage; re-snapshotted, rebuilt
  green (2,328 jobs), axioms re-checked.
- Not attempted: the register bookkeeping that would discharge `hFin` (RESULT §5).

## Pass 2 (after `b1fecbc`): `hFin` steps 1–4, 6

- `FRSoundnessAccPos` (steps 3–4): `phStart_eq_sum` (the `fsStarts` fold, generalised accumulator),
  `phaseMsgs_length` (per shape), `msgsFrom_getD`, `fsMsgs_phase`, `fsMsgs_round`; `rSum_eq`,
  `rVal_eq` (char 2), `rSum_fsQ`, `rVal_fsQ`, `eqv_k`, `roundsT_chk`. Built after two small fixes.
- `FRSoundnessAccSem` (step 1): `runFields` + `foldl_step`, `finals_ops_eq`, `pureRun_noAsk`,
  `exec_ok_false`, `field_flag`, `fields_ok`, `genPhases_next`, `accept_fields`.
  Trap: `show skeleton.2.next = … from hn` timed out (projection whnf evaluates `genPhases` on the
  whole table); fixed with `hsk : genPhases phases 0 ctx₀ = skeleton := by rw [skeleton]; rfl` and
  `rw [hsk] at hn`.
- Stopped before step 2 (outs ↔ values) and step 6 (`relPf`): context long; handover in RESULT
  Pass 2.
