# RSV-V2 (the reserve's V side, RSV2's stacked `evalM`): JOURNAL

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `213c407`. Build tree
`logs/fr-build-RSV2` (copy of `fr-build-RSV`, re-snapshotted on HEAD; `MINE.txt` = this track's 13
modules, symlinked; the hint is HEAD's copy, not a link: the worktree's is B2″'s). Logs `logs/RSV2/`.
Spec: main's `design/RSV2.md` §4, with `reviews/RSV2-review.md` as applied by the orchestrator. Every
lean/lake/probe in a 16 GB scope with a timeout. No sub-agents, nothing committed, no `FRSoundness4*`
edited (the build tree carries RSV-V's sorried copies of the 7, `logs/RSV2/sorried-copies/`).

## Coordination with B2″ (same worktree)

- 13:31: B2″ owns `FRVIRTpl*`, `FRVIRCompile`, `FRNodeRows4Model`, `FRNodeRows4Arena*`,
  `FRNodeRows4Hint` (its worktree copy) and `FR.lean` (its import). This track touches none of them.
- **The format change is in the shared worktree** (`FRShape4` `lrEnd` 1,008 and its dependents:
  `FRNodeKinds4` `segB 1551104`/`cLen 24236`, `FRNodeLayout4`, `FRX4*`, `FRVIRTpl4Bridge`). B2″'s
  arena sizes (arena₁ = `segB / 16` = **96,944** now, was 96,936) should come from `segB`/
  `streamBytesOf seq4`, not a literal (review finding 3). The hint's `maskN` literal
  `(24234, 96936)` becomes `(24236, 96944)`, `(24236, 48472)`, `(96944, 96944)`: the hint must be
  regenerated (B2″ lands first; this track regenerates it last, on the orchestrator's word).
- New prototype-0 registers (`rsvEOps`): ≈ 130 F registers in finE's block and 8 more cells in finPf's
  chain: in the skeleton's cells (RSV-V's were < 116,493), clear of the template instances.

## Log

- Baseline: the RSV2 tree at HEAD + sorried copies builds green (2,591 jobs, `logs/RSV2/build-baseline.log`).
- Format: `FRShape4` (+ `NodeKind.ix`, `NodeKind.all`), `FRNodeKinds4` (`hEnd` 74,015 / 122,495 / 195,216:
  the review's correction, `decide` refused the memo's 74,021 / 122,499), `FRNodeLayout4`, `FRX4Prog`,
  `FRX4Ext`, `FRVIRTpl4Bridge`, `FRVerifierImplNode4T` (doc: `aggB 1 = 0x17AB00`, bits 13/12 = 1/0).
- `FRVIRFinals4`: `FinP.kix`; `rsvRx/Ry/S/X` 48/416/816/960, `rsvN = 60`; `rsvSOps` (the nine `s^P`,
  each materialised `× one`); `rsvEOps` (RSV2 §2.2, the 11 materialisations of review finding 1);
  `gFinE0 … own` (own `evalM` → three `const 0` when `own = false`); `gFinE` (own asserts off, 60
  exports); `rsvBOps` over `rsvN`.
- `FRVerifierImplNode4F`: `sOf`, `dot3`, `evalMX4`/`evalMXS4`/`evalMX4_eq`, `evalMN4` at size 32,
  `evalMS4_src`, `implN4F_hMX`, `evalMX4_ctl`; `kindElemN`, `kindOfElem`, `sub3`, `evalMPair`,
  `evalMD4`(`S`) deleted.
- Scan (`logs/RSV2/scan/`, from HEAD's `FRSoundness4*`, 4 rounds): **the same 7** as RSV-V, green at
  2,591 jobs (`build-4.log`).
- KAT `probe/RsvKat2.lean` run 1: honest full-support chains failed (ii″): **bug in `rsvEOps`**, (ii″)
  added the parent's own `X^P` instead of the claim's `X` (`c + 57`); invisible with `s = 0`. Fixed;
  run 2 (`rsvkat2-2.log`) passes every case.
- IR dumps regenerated (`logs/RSV2/dump/`, cap-check KAT PASS): node programs 154,920 ops (RSV-V
  154,433: +487), 147,077 registers; segments 151,226 unchanged.
- Preview node dump on HEAD's layout (`nodedump-pre/`, stale hint): every one of the 60 registers is one
  cell (`rsvcells.py`, `rsvcells-pre.log`); `rsvRel` set from it **provisionally** (E2/E4 cells as
  RSV-V's; the 11 materialised cells 116,584 … 116,603, skeleton region). To be re-read after B2″.
- 14:10: B2″ landed (`7602c97`). Re-snapshot; `MINE` gains `FRNodeRows4ArenaPlace`, `FRNodeRows4Model`,
  `FRNodeRows4Hint` (literals: `arN_eq` 96,944, `packMapN` 212,640, the model's sums).
- Hint regenerated last (`laydump4-1.log`, `mkhint.py`): only the `maskN` literal moves; `inR true`.
- Node dump, `rsvRel` re-read (`rsvcells.log`): unchanged from the preview, PASS. `cellfit`: 0
  overlaps. `arenafit`: skeleton end 276,634 < arena₁ 290,816; lowest instance 414,016 > bits end
  397,440. Plan-form KAT PASS.
- δ (`vtime-ab.*`, `xbrk-*`): +21 … +24 ms per extra kind, +51 ms at full support (324 ms). The cost is
  per kind (`linkV4` ≈ 29–32 ms whatever the slot count; ≈ 9–10 ms of it rebuilds the rows), not per
  slot. `ltbOf` shared N4/N8 in `evalMX4` (−4 ms). Levers in `FRNodeRows4Plan` (L-circ): RESULT §7.
- `FRVIRFinals4` CPU 53.7 → 24.5 s: `gFinE0`'s lists type-ascribed (14.4 s of elaboration), and
  `noAsk_rsvEOps` by `simp only …; rfl` (12.4 s of `simp`).
- Final: build green (4,950 jobs, the 7 sorried in the tree); scan from HEAD's `FRSoundness4*`: the same 7,
  green at 2,592; KAT identical (`rsvkat2-3.log`); axioms 47/47 clean; source rule 0 findings.
