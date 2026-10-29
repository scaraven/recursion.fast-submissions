# SRA journal (reserve link, `Gaps4` at `StmtN4R`, `SlotRunA`'s arena-free parts)

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `616b57c`. Build tree
`logs/fr-build-SRA` (copy of `fr-build-IMP`, MINE = this track's modules, re-snapshotted onto HEAD).
Logs `logs/SRA/`. No sub-agents, nothing committed. Every lake/lean ran in a 16G scope with `timeout`.

## 2026-10-29

- Read QUEUE, IMP/RSV-S3/RSV-S2b/B3 RESULTs, PACK-4.4 §1.3/§4. Plan:
  - **Reserve as an `AT` summand** (IMP's `AT.add`): a template `AT.rsv` covering slot 0's stacked
    `evalM`, whose rows check (on `cs`) that its operand slots and output slots are the reserve cells
    `rsvRel` (else `failR`). Its `ATImp` gets `InvK` at the op from `AskCtx`, which is exactly what a
    prefix form of `compileX_run` would provide; so the reserve needs no prefix form.
  - `Gaps4` over `StmtN4R`; `hL_of_res`'s route needs `StmtN4R` at the run's chain (`nodeRunL4` +
    `rsv_of_tail` + `rsvZero4`).
- Baseline `lake build FR Solution FRSubmission4Fin` at HEAD: green, 2,648 jobs (`logs/SRA/base-build.log`).
- `FRNodeRsvLink` (new): `AT.rsv`, `eqRowIf`/`argRows`/`outRows`, `atImp_rsv`, `rsvCells_slot0`,
  `atImp_rsv_slot`, `withRsv`, **`gap4Imp_of_rsv`**; controls `atRsv_cov`, `eqRowIf_ctl`,
  `argRows_cells`, **`atImp_rsv_neg`** (concrete `CS` with the reserve layout: rows empty, an `evalM`
  with `X₃[1] = 1` breaks `ATImp`). Checks.
- `FRNodeLinks4`: `nodeRunRL4`, `hL_of_resR`; `FRNodeLinks4Run`: `hL_of_sigR`.
- `FRSubmission4Cert`: `Gaps4` over `StmtN4R`; `gap4_of_gaps`, `resid4H_of` (→ `Resid4HR`),
  `certificate_sub4` via `certificate_rev4HR`; converse `gaps4_of_N`. `FRNodeLinks4Sub`/`SigH` follow.
  `lake build FRSubmission4Fin FRNodeRsvLink`: green, 2,537 jobs.
- Foreign flags dumped (`probe/ForsDump.lean`, `logs/SRA/forsdump.log`, copy `fors-list.txt`): p0 15,
  p1 79. Classes: kind byte (1+1), proof-byte zero pins (13+78), and one type-failed `assertEq` in p0
  (reg 100345). Traced (`forsorigin.log`): `keep` over `packK` arrays of unequal per-kind length
  (op#101817–101821) is `skip 1`; 852 registers downstream are untracked; the (β′) cap-check
  equation is foreign: no row enforces it. Reported (RESULT §4.2).
- Full build `FR Solution FRSubmission4Fin FRNodeRsvLink`: green, 2,649 jobs, 0 sorry. Axioms (22) clean.
  Source rule 428 files, 0 findings. Profiles: `FRNodeRsvLink` 0.50 s kernel; `FRNodeLinks4Run`
  1.02 s (HEAD text 0.98 s, preexisting). `FRSubmission4Fin` doc updated, rebuilt green.
- Prefix form of `compileX_run` not built: `ATImp` already sees `InvK` at the op (RESULT §3).
- RESULT written. Done.
