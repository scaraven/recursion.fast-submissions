# INIT journal

Track INIT (the badge's start-up), 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch
`v4/rev44`, HEAD `9249a56`. Build tree `logs/fr-build-INIT` (copy of `fr-build-IMPC`, re-snapshotted
onto HEAD; MINE = the files I edit). Logs in `logs/INIT/`.

## Tooling

- No `perf` (paranoid 4), no `gdb`. Two in-process tools instead (`logs/INIT/`):
  - `instr.py` + `initprof.c` + `build-instr.sh <exe>`: re-compiles every entry module's C with each
    `_init_X` (eager top-level constants and the lazily forced `lean_obj_once` closed terms) wrapped
    in an enter/exit timer (inclusive and exclusive ms), and links an instrumented copy of the exe.
  - `initprof.c` also has a SIGPROF sampler (1 ms CPU, `backtrace()`; `INITPROF_SAMPLE=<file>`);
    `symb.py`, `callers.py`, `under.py` symbolize it with `nm`.
- `probe/Start0.lean`: `import Solution`, empty `main` = the badge's import closure's start-up.

## Log

- HEAD build tree green (`Solution FRSubmission4Fin FR start0 plan4t`, no-op rebuild).
- **Start-up at HEAD (VM, core 30):** `start0` 17.3–17.8 s user / 17.7–18.2 s wall; `plan4t init`
  6.4–6.6 s. The badge's closure is 2.7× the plan alone.
- **Profile** (`prof-head-2.log`, `symb-head.txt`): `FR.X.X4.nd` 7.2 s (all in `chTab4 seq4 456`:
  `fsMsgs4 S` recomputed per table entry, 457×); the six programs `progS3x`/`progNNx` 0.6–0.75 s
  each (gen4: `fieldOffOf`/`dOff4` recomputed per position, 871 per program); `planData4` +
  `planOf4` 4.5 s (REPF's file); `nodePlan` 1.5 s; `progSegG`/`protoProg` 0.4 s.
- Edit 1 (`FRXChain4`): `chTab4` over `tabEntM (fsMsgs4 S)` (computed once); `tabEnt4 S p :=
  tabEntM (fsMsgs4 S) p`; `chTab4_eq` (rfl); four proof lines unfold `tabEntM` too.
- Edit 2 (`FRVIR4` `genPhase4`, `FRVIR4Mux` `genPhaseG`): the queries branch binds `o fCols`,
  `o fSibs`, `dOff4 S i`, `posW4 S i` once per phase (genPhaseG already bound three of them).
  Neither file is on my list; no running track owns them (flagged in the RESULT).
- Full rebuild 1 started (`build-1.log`).
- Rebuild 1 (on 9249a56) green; `start0` 17.7 → 7.1–7.5 s user (`start0-edit12-old.log`).
- Orchestrator: ASK-T committed `ae8b8d8`; re-snapshotted onto it. HEAD's `FR` umbrella fails there
  (`FRNodeRows4RepCtrl` vs `FRNodeRun4AskT`: both declare `FR.N4s.ctlP`), not caused by INIT; built
  `Solution FRSubmission4Fin` and the probes instead.
- At ae8b8d8 + edits 1–2: `start0` 8.0–8.2 s user (`start0-edit12.log`). `inituse`: every program
  (segments too) has one `evalM`, so `Impl.nodePlan` is live at run time (segments' evalM): not lazy.
- Edit 3 (`FRVIRFinals4`): `finOps4` relocates by `relocT P.S (fieldOffT P.S)` (moved up from
  `FRVIR4Mux` with `relocT_eq`); `finOps4_def` gives the `reloc` form; four proofs use it
  (`finOps4_seq3`, `FRVIR4At.map_at_finOps4`, `FRSoundness4Qry.noAsk_finOps4`, `FRSoundness4R4Run.finOps4_eq`).
  `start0` 7.4–7.8 s (`start0-edit123.log`).
- Edit 4 (`FRVIRTplBuild`): `inputKindsF` accumulates the shared inputs reversed with a count (was
  `++ [_]` + `length` per input: quadratic); `tinRPu`'s unaligned tail by `instIRA` (array inputs,
  `instIRA_eq`). Machine loaded (REPF builds): timings noisy, A/B later.
- `initbudget` probe: sparse rows ≈ 37 ms build (+ marking: 47 ms as a closed constant) per 100 k
  rows; keyed instances ≈ 85–95 ms per 100 k rows; `askRowsT 0` standalone 66,263 rows in 1.49 s
  (a whole trail pass); plan: 198 keys, 10,049 + 10,289 pieces, 29,709 + 21,524 sparse rows.
- impc lever (orchestrator): sampled 0.23 s for both prototypes (winE/pfLoc 0.17, provOf 0.09);
  `pfLoc_spec` only needs "a member of `pSegs` with `st ≤ o < st + len`", but replacing `find?` by a
  search proved *equal* needs `pSegs` sorted/disjoint as a decided fact (kernel cost unknown):
  proposed, not done.
- Baseline tree `fr-build-INIT0` (HEAD ae8b8d8, no edits) building for the A/B.
- A/B at ae8b8d8 (`ab-start0.log`): HEAD 17.8–19.1 s, INIT 7.05–7.47 s. Fingerprint probe `initfp`
  (programs' ops, plan pieces/rows, nodePlan, chTab4): identical (`fp-base.log` = `fp-init.log`).
- Orchestrator: IMPC2 (`91e0d61`) + `ctlP` fix; re-snapshotted, `FR` green again.
- `FRInitFuse.compMSXA` (+ `compMSXA_eq`): the compile and the ask trail in one walk. `fusetime`:
  2.17–2.34 s → 1.18–1.27 s in process, same rows. Prototype wiring in the build tree's
  `FRNodeRows4Plan` (`plan-fuse.patch`): first try 8.1–9.2 s (the unfused `planData4` was still an eager
  constant); with `planData4` noncomputable 6.14–6.40 s vs HEAD 18.1–18.4 (`ab-start0-fuse2.log`).
- Orchestrator: REPF committed `407260d` (replay fold; CF now owns FRNodeRows4Plan/Rep*). Re-snapshotted
  both trees (the prototype patch is dropped from the tree). HEAD start0 30.1–31.0 s.
- Profile at 407260d: `planOf4D` 13 s (replay); found `lean_cstr_to_nat("1099511627776")` (= `repB`,
  2^40 folded) parsed in CF's loops, 1.9 s; `eqTblG` List.getD quadratic, 1.6 s (my file).
- Edit 5: `kt` `@[noinline]`. Edit 6: `eqTblG` reads the previous table from an array (`toArray_getD`).
- Final A/B at 407260d (`ab-start0-407.log`): HEAD 30.1–31.0 s, INIT 17.3–18.3 s; fingerprints incl.
  the replay rows identical (`fp-*5.log`); MxKat FAIL 30 identically in both (REPF's change); V(N4)
  1,861 vs 1,872 ms best; axioms clean (21); source rule 0 findings; RESULT written.
- `plan4t check` at the final state still running at hand-over (`plan4t-check-final.log`).
