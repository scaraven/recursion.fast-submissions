# PORT journal (decoder, node links, run existence → rev44 at 4.4.1's format)

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `e464756`. Build tree
`logs/fr-build-PORT` (copy of `fr-build-A1`; `MINE` = every `FRX*`, `FRNodeLinks4*`, `FRNodeRun4*`,
`FRSubmission4*`; `b.sh` on CPUs 16–23). Logs `logs/PORT/`.

## 2026-10-29

- Scaffold (build tree only): A1's stubs, plus HEAD-red `FRSoundness4R4FrE` declarations `e_end4`,
  `not_rejEndE4_node`, `e_in4`, `e_fin4`, `not_rejFinE4_node` (RSV-S's E-phase WIP).
- build0 (`logs/PORT/build0.log`): red `FRXDec4Levels` (`cost_decLevels4`), `FRXChain4`
  (`fsMsgs4_zero`, `_length`, `_items`, `_ctl`), `FRNodeRun4S` (8905), and HEAD's `FRSoundness4R4FrE`.
- Fixed: `cost_decLevels4` (new exact costs by `#eval`, scratch `scratch/DecLv.lean`:
  27,032,483,570,671 / 108,050,868,885,470), `cost_le_decF04`'s literals; `fsMsgs4_zero` generic
  proof (`range_succ_eq_map`; no longer `rfl` because `phasesOf S` ends with `capChkPh S`);
  482 → 486 positions; cap₀ at 20,896 (was 19,872: +1,024 = lrEnd/eEnd growth); `FRNodeRun4S`
  8905 → 8783 (`itemsOf_seq4_len`).
- Scaffold additions: `FRSoundness4R4FrRS.e_bind4`, `FRSoundness4R4Start.start4_of_fields` (HEAD-red RSV-S).
- `reassemble4 S tr` over all 20 fields (`nFields4`; fields 18/19 = `D`/`A`, the cap check's absorbs):
  drops `aB`/`aBytes4`; `pSeg4` over `nFields4`; `proof_words4`, `pfHdr_reassemble4`, `pf4_size`
  (876,304) follow. `FRNodeLinks4`: `FinLog4` gained `cap` (one more field). `FRNodeLinks4Run`:
  482 → 486 positions; `fsMsgs4_X : X.fsMsgs4 seq4 = R4.fsMsgs4 seq4` (decide +kernel; R4's table is
  now a different definition).
- `FRXOut4W`: `vS` at `i·strideB`; `signedWords_agg` with the spacer entries (`spW`, `spAns`) and the
  count `k·|items| + (k − 1)`; `sgnX_fits` via `aggTrace_length`, `mem_aggTrace`.
- `FRXOut4C`: `vS_get` without shift (chain word `i·(strideB/8) + u`); new `spAns_words` (shift-1
  pairs from `i·(strideB/8) − 4`).
- `FRXOut4R`: realign deleted; copy loop `cpBody`/`cpSeg`/`CpInv`/`cpBody_step`/`cpSeg_sem`
  (redirect loader kept: the last segment's final block is `finBlk`); `nW` 185,344 → 193,888
  (`segB/8`: A1's "nW unchanged" was wrong, segB grew with RSV2).
- `FRXOut4P`: `cp_vS`; `prevIR` uses `cpSeg`.
- `FRXOut4A`: `segLoop κ P E` (prefix program); `spSeg`/`spIR`/`spPre` (spacer entry: 13 constant
  words + `shw4` at shift 1); `cntW`; `aggRegs` in two blocks with `qJ = k·sBlk − 3·[0<k]` (`jLv`);
  `chR_agg`, `aggRegs_sem`, `spPre_sem`, `cntW_val`, `aggIR4_sem` re-proved. Green.
- First profile: `FRXOut4R` 80 → 2.7 s, but `FRXOut4A` 102 s: `aggIR4_sem`. KProf (G5's tool) + a congrArg
  mismatch scanner (`scratch/Diff.lean`) located it: `simp only [List.nil_append]` under the binder is a
  definitional step, the kernel unfolded `packBytes (bl (pf4 …))`. Fixed with a theorem rewrite → 4 s.
- Orchestrator's message: carried G5 (`edf11b4`) into `FRXNd4`, `FRXChain4`, `FRXChainFlock`, `FRXOut4O`
  (`cso_outIR4` without `cso_realign`, plus `cso_cpSeg`/`cso_spPre`). build8 green (2,527 jobs incl. `Solution`).
- Profiles: `logs/PORT/prof-after.txt`, `prof-after2.txt`; axioms `logs/PORT/axioms.log` (sorryAx only via the
  scaffold); source rule 420 files, 0 findings. RESULT written. Done.
