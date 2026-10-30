# SEG-R1 journal (track SEG-R, stage R1)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `0f7d3a3` = SEG-R0). Build tree
`logs/fr-build-SEGR1` (a copy of `fr-build-SEGR0`; `snap1.sh`: HEAD by `git show`, MINE symlinked,
every other non-HEAD module removed, so SIB's/CF2's untracked files stay out). Logs `logs/SEGR1/`.

## 2026-10-30

- Read SEG-R.md, SEG-R0-RESULT.md, QUEUE (flock copy) "Review of SEG-R".
- Tree set up; MINE = FRVerifierImplCore FRSubmission4V FRSubmission4Cert FRNodeRsvLink FRSegTarget4
  (+ new modules as they appear). Probes: SegTpl, SegV (SEG-R0), Start0 (INIT).
- Baseline build A (HEAD, for the start-up A/B) started: `build-A.out`.

### Decisions

- **Item 5 (init).** `implB` stays the logical base (`Impl.implCN`, now `noncomputable` with
  `nodePlan`/`lPlan`), so `Gaps4`, `repOk_rtC1cB`, `implT_implB` (RepF, CF2's) and the certificate's
  definitional `implB ≡ implC (finC finPf) lRows 0` are untouched. The compiled constants (`implS`,
  `implNN2/4/8`) are built on the plan-free `Impl.implC0`. `V4F_eq`/`VsegF_eq`/`VnodeF_eq` keep their
  statements; their proofs go through `implSeg_implCWith`/`implN4F_implCWith` (congruence over the two
  plan arguments, generic so that no defeq check ever whnf's a plan).
- Items 4 and 5 applied (FRSegTarget4 pin; FRVerifierImplCore `implC0` + noncomputable plans;
  FRSubmission4V `implS`/`implNN*` on `implC0`, `implS_eq`/`implNN_eq`; RsvLink `implR` on
  `implC0`; Cert `Vnode4` noncomputable). `lake build FR Solution FRSubmission4Fin start0 segv`
  green (`build-B1.out`, 5,237 jobs).
- Start-up A/B (`ab-start0.log`, core 27, 5 rounds, builds running on 0-23): A 21.5–23.5 s user,
  B 19.1–19.9 s: **−2.0 s** (median 21.6 → 19.6).
- New: `FRNodeRows4RepSegK` (KOpD/rtKD/KOkD/rtKD_okW, rtEvZ/rtEvZ_okW) compiles; `FRVIRTplSegR`
  (`rsSegT`, `ok_rsSegT`) compiles; `FRNodeRows4RepSeg`: `rsWeightF_seg` proved.
- Mux simplified: always three products per kind-varying position (no zero skip; +15 locals over
  SEG-R0's 192) — the proof is one `cases ι`.
- `kRSS` + `kRSS_ok` proved (trap: `congr 1` on `encK A = encK (rsWeightF …)` whnf's rsWeightF →
  heartbeat timeout; `congrArg encK` instead). `rtSeg1`, `rtC1d`, `rtC1d_ok`, `repOkW_rtC1dB`, controls.
- SegKat probe: rsSegT KATs pass at 25/23/24; `repRowsP rtSeg1 1` = 37,362 rows, 0 rejecting rows.
- SegV A/B: segment check ≈ −70 ms.
- Final build green (FR Solution FRSubmission4Fin FRNodeRows4RepSeg start0); axioms clean; source rule 0.
- **Stopped before `kSTS`/`kTSS`** (context budget): RESULT §6 has the plan; both remain imports.
- RESULT written: stages/SEG-R1-RESULT.md.
