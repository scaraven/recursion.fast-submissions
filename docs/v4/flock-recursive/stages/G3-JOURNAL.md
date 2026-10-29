# G3 journal: elaboration time of the next heaviest certificate modules

Track G3. Goal: cut the certificate build's CPU time in the next 20 heaviest modules of `Solution`'s
closure without changing any statement. Worktree HEAD `4ac68fc`; build tree `logs/fr-build-G3`
(copied from `logs/fr-build-G2`, `MINE.txt` = the modules below); logs `logs/G3/`; tools
`logs/G3/tools/` (G2's, re-pointed, plus `closure.py`). Report: `reviews/G3-golf.md`.

## 2026-10-29

- **Closure.** `logs/G3/tools/closure.py Solution` at HEAD: 249 modules
  (`logs/G3/closure-Solution.txt`). All 20 listed modules are in it.
- **Skipped: modules with another track's uncommitted edits.** The worktree holds uncommitted
  edits to `FRSoundness4Pos`, `FRSoundness4Qry` (A2′'s CapChk: `fsItems4_length` 482 → 484, the
  8,905 → 8,907 counts) and `FRVIRTplExt` (B0's split policy, `B0-JOURNAL.md` §2). Golfing them
  would mix my edits into theirs, so they are left alone.
- **Scope (17 modules).** `FRSoundness4R4FinSh FRSkip FRSoundness4R4Outs FRSoundness4Agg
  FRVIRTplWalk FRKindWeight FRVerifierImplOps FRSoundness4R4PfFlag FRVIRTplDag FRNodeTarget4C
  FRSoundness4R4FinRS FRSoundness4R4FinLc FRBlake2sWords FRBlake2sGeneric FRVIRTplSeg FRSumcheck
  FRSoundness4R4Fin`. Originals saved in `logs/G3/before/`.
- **Setup.** `./b.sh FR Solution FRSubmission4Cert` at HEAD: green (78 jobs rebuilt).
- **Baseline** (`tools/measure.sh base`, sequential, one core, `--profile`):
  `logs/G3/measure-base/summary.txt`. Traces (`tools/prof.sh`, threshold 50 ms):
  `logs/G3/prof-base/`.
- **Per-declaration cost without trace inflation.** `trace.profiler` inflated FRVIRTplWalk from 25
  to 364 CPU-s, so its per-declaration figures are unusable there. New tools: `tools/hb.py` writes a
  scratch copy with Mathlib's `#count_heartbeats in` before every declaration (scratch only, under
  `logs/fr-build-G3/scratch/`); `tools/hbrun.sh` ranks the declarations (`logs/G3/hb/*.txt`).
  Heartbeats over-state the CPU gain (FRSoundness4R4PfFlag: −73 % heartbeats, −19 % CPU at that
  step), so every change is confirmed by a CPU A/B.
- **FRSoundness4R4Outs.** `opsOut_roundOpsK … = 13 := rfl` took 27 s traced (13 s plain): the
  elaborator's `isDefEq` of `opsOut [15 ops]` against the literal. Now `simp only [roundOpsK, opsOut,
  List.map_cons, List.map_nil, Op.outs, List.sum_cons, List.sum_nil, Nat.reduceAdd]` (0.04 s). In
  `genPhase4_out_lt`, four `simp [opsOut, Op.outs] at *` (11 s traced; `at *` also simplified `key`
  and the other hypotheses) became `simp only [opsOut_cons, opsOut_nil, Op.outs, Nat.reduceAdd] at
  this ⊢`. 42 → 15–17 CPU-s.
- **FRSoundness4Agg.** `VA_extract_log`'s `hseg`: `hmem`'s `refine List.mem_map.2 ⟨…, ?_, rfl⟩` and
  the `rw`s unfolded `segs := aggSegs (piSizeOf seq4) …` (16 s traced). `hsz'` is now stated before
  `set segs` (so `set` rewrites it too) and `hseg`'s proof starts with `clear_value segs`. 27 → 12
  CPU-s.
- **FRVIRTplWalk.** `exact fun g s hs hp => (this g s hs hp).imp id fun h i => h i` (6 sites) made the
  elaborator check `hp`'s type `(StateT.run (dsumW …) s).2.gs.toList <+: G` against `this`'s
  `dvec 32 …` form, unfolding the state monad (`Decidable.rec`, 5–11 s traced per site). `exact this`
  (`exact key`) unifies the two `RelT` statements at the head instead. `unfold dsumW` before the old
  form did not help. 98.6 → 78.1 M heartbeats.
- **FRSoundness4R4PfFlag.** (1) `omega` with the whole context of `flag_gFinPf4`/`flag_pfTail4`
  (about 100 hypotheses, `set` variables): 2–8 s traced each, the largest late in the proof. The slow
  ones now `clear * - <the facts used>` first (or take the fact directly: `exact this` for `b + 2 <
  R10.size` from `b + 3 ≤ R10.size`). (2) `simp only [gFinPfR, …]` realized the equation lemma
  `gFinPfR.eq_1`, whose generation runs a failing `isDefEq` (4.9 s traced). Both sites now `delta
  gFinPfR` first. 188.8 → 51 M heartbeats; CPU 32.6 → 21.7 in single A/B runs.
- **FRKindWeight.** `congr 1` on `a + b = c + d`, `a * b = c * d`, `List.sum l = List.sum l'`
  tries to close the halves by `rfl` and unfolds `Finset.sum` (2.8 s and 4.8 s in `kwS_keys`,
  `hornerK_eq`, `kwS_fast`). Replaced by `refine congrArg₂ (· + ·) ?_ ?_` / `congrArg₂ (· * ·)` /
  `congrArg List.sum` / `congrArg (· * e n true)` (10 sites). 87.6 → 60.8 M heartbeats.
- **Next heaviest modules in the closure** (the list's remaining modules are declined, below): the
  `FRX*` machine modules not in G2's set and not off limits: FRXNode, FRXChainSem, FRXOutRun,
  FRXChainLoop, FRXLog, FRXChain, FRXChainTop (plus FRXChainFlock, FRXDecLv, FRXReadLv, FRXMerge
  examined, not changed).
  - `attribute [local irreducible] entryK storeM` (G2 §2.1): FRXNode 130.8 → 72.0 M heartbeats.
    With `runPrims` too: FRXChainSem 80.6 → 68.5 and FRXOutRun 51.4 → 45.4, after the `rfl`s that
    need `runPrims [] M = M` became `with_unfolding_all rfl` (1 site each; `tools/fixrfl.py`).
    FRXChainLoop and FRXChainTop gain nothing from it and keep no attribute.
  - G2's `simp +decide only` conversion (`tools/sdecloop.sh`, `tools/prunemod.sh`) on FRXChainSem
    (26 calls; 1 kept), FRXChainLoop (18), FRXNode (7), FRXLog (3), FRXChain (7), FRXChainTop (9).
- **Lines over 100 columns** in the edits reflowed by hand (11 lines).
- **Build r1** (`logs/G3/build-r1.log`): `FR Solution FRSubmission4Cert` green, 2,581 jobs.
- **Statements** (`logs/G3/tool/StmtHash.lean`, `tools/cmpstmt.py`; before = the G2 tree's oleans,
  whose sources equal HEAD for all 28 modules, `logs/G3/stmt-before.txt`; after `stmt-r1.txt`;
  `logs/G3/check-r1.log`): 2,589 constants compared, every type and `def` value hash unchanged.
  The 4 "MISSING" are on-demand equation lemmas that these modules no longer realize:
  `FR.Snd.R4.gFinPfR.eq_1` (the `delta` above) and FRXLog's private `Prim.dst.match_1.eq_1/eq_2/
  splitter` (`simp [Prim.dst]` became `simp +decide only` without `Prim.dst`). They are generated
  wherever a later `simp` needs them; no user declaration is affected.
- **Axioms** (`logs/G3/tool/Ax.lean`, `logs/G3/axioms.log`): the 4,038 constants of the 28 modules,
  `certificate_sub4` and `certified` use `propext`, `Classical.choice`, `Quot.sound` only.
- **Source rule** (`logs/G3/source-rule.log`): 365 files, 0 findings.
- **Final measurement** (`logs/G3/measure-fin{1,2}`, `measure-frx{1,2}`; before/after interleaved,
  two cores, minimum of 2): the 12 edited modules 249.8 → 174.0 CPU-s (−30 %; ≈ −58 of their 207
  CPU-s on the 7763, scaled); kernel 28.3 → 26.2 s, no module higher. Code lines 5,225 → 5,283.
  Table and what was declined: `reviews/G3-golf.md`.
