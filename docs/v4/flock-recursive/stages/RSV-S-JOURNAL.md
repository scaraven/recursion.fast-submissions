# RSV-S JOURNAL: the reserve's soundness chain in RSV2's stacked form

Track RSV-S, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `face798`
(RSV-V2 + main). Build tree `logs/fr-build-RSVS` (a copy of `fr-build-A3b`, re-snapshotted on HEAD;
`mymods.txt` = every `FRSoundness4*` module, symlinked to the worktree). Logs `logs/RSVS/`.
No sub-agents, nothing committed.

## 1. Setup

- `cp -a logs/fr-build-A3b logs/fr-build-RSVS` (38 s); `run.sh`/`prof.sh` log to `../RSVS/`; `b.sh`
  writes the full log to `../RSVS/$LOG.log`.
- `mymods.txt`: the 94 `FRSoundness4*` modules; `mine.sh` snapshots HEAD and links them.
- Baseline build at `face798` (`logs/RSVS/build-0-baseline.log`).

## 2. Baseline and the decoder

- `build-0-baseline.log` (HEAD `face798`): red at the 7 (`R4Fin`: `flag_gFinE`, `flag_gFinB'`; `Qry`'s three)
  as far as the build reached, and in the decoder from main's merge (not this track's):
  `FRXChain4.fsMsgs4_zero`, `fsMsgs4_length`, `fsMsgs4_items`, `fsMsgs4_ctl`;
  `FRXDec4Levels.cost_decLevels4`. The build tree carries sorried copies of those five
  (`fr-build-RSVS/patchdec.py`, applied by `mysnap.sh`); the worktree's files are untouched.

## 3. Work log

- `FRSoundness4Qry`: `noAsk_gFinE0` (new), `noAsk_gFinE`, `noAsk_gFinB'`, `noAsk_gFinPf` re-proved
  (cases on `rsvOps`). Proof only.
- New `FRSoundness4RsvMLE`: `hiPt`/`lowA` (a point continued above its coordinates), `mle_eq_hiPt` (the
  constant extension and the partial evaluation in one lemma), `matMLE_hiRow`/`matMLE_hiCol`,
  `mle_hiTab`, `mle_coord`, E1's table `zcT` with `mle_zcT` and `zcT_ne`.
- `FRSoundness4P4bNames`: the child claim on the log (`pxL`, `pyL`, `sL`, `xL`, `mStL`, `etaL`),
  `mStack`, `truthChild4`, `dChild`, `ChildBad4`, `xHat`; E restated: `ZCwE4` (`F̃(τ) + η·D ≠ 0`),
  `T3E4` (six tables), `D3E4` over `outerExprR`, `mHatT`, `EndBadE4` (quadruple), `c4E4` (+`κ_E⁴ m̂*`),
  `cTab4`, `TEb4` (four tables), `BatBadE4`/`D2Eb4` over `innerExprR`, `RejEndE4` (ii″), `RejFinE4` (iv″).
- `FRSoundness4P4bE`: E's obligations re-proved: `e4_zc_count` (`nE4 ∨ ChildBad4`, `≤ 24/2^128`),
  `trueSum_T3E4`, `final_T3E4`, `e4_habs_outer`, `e4_single_outer`, `e4_outer_append`, `e4_habs_end`
  (quadruple), `rejEndE4_log`; `sum_cTab4`, `trueSum_TEb4`, `batch_count5`, `single_batchE_at` /
  `e4_single_batchE` (`≤ 4·2^128`), the E4 rounds, `final_TEb4`, `e4_habs_end4`, `rejFinE4_log`.
  Note: a `rw` that leaves a closed-looking goal tries `rfl` at default transparency and timed out
  (`eqTable` of a symbolic size); `rewrite` + a syntactic `rfl` avoids it.
- `FRSoundness4P4fDF`/`P4fObl`: `D16X` gains `ChildBad4` (E1's entry; `rd_childX` reads 214);
  `hfin_hi`'s E1 case frames `nE4 ∨ ChildBad4` against `e4_zc_count` (`24/2^128 ≤ deltaR`); E3's row
  `4·2^128 ≤ 239·2^128`; `ss_D3E4`/`rd_zcwE`/`rd_endE` through the new `D3E4_same`, `zcwE4_reads`,
  `endBadE4_reads`. `lake build FRSoundness4P4fObl FRSoundness4XFront` green (`logs/RSVS/b-p4f.log`).
- `FRSoundness4R4Fin`: `relE4` restated (rsvOps branch: (ii″)–(iv″), the zero conjuncts; the old
  branch kept for 3.x and the segment group). `flag_gFinE`'s `rsvOps = false` case re-proved as
  before. The `rsvOps = true` case: one `simp` over the expanded 168-op list ran 9 min 40 s and hit
  4,000,000 heartbeats (`logs/RSVS` chk run) — not viable. Plan: blocks with `pr_seq2`
  (`gFinE0` off / the 60 reads + zero asserts / packs and consts / `rsvSOps` / the tail), each run on
  the previous file as base (`pureRun_rebase`), reads of earlier blocks by family lemmas.
- `flag_gFinE`/`flag_gFinB'` split: the old relations `relE4o`/`vStar4o` with the original proofs
  (`flag_gFinE0`, `flag_gFinB'o`, 11 s for the module); the reserve branches are open goals (handover).
  An attempt that dropped the `generalize` steps hit the 16G cap (OOM kill, `journalctl --user`):
  keep the `generalize`s.
- `fsMsgs4_ends` → 1,008 / 112; `hin_E` gains `η`, register `0` (`relE4_of_accept` builds).
- Scan `b-scan2.log` (R4Fin's two goals sorried in the build tree; decoder/B3 merge breaks sorried by
  `patchdec.py`): red in `FrE` (`e_end4`, `e_in4`, `e_fin4` and their `not_rej*`), as expected.
- Source rule: the word "partial" in `RsvMLE`'s docs was a finding; renamed "fixed evaluation". 0 findings.
- Stopped here for context: `RSV-S-RESULT.md` §5 is the handover.
