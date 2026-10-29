# G3: elaboration time of the next heaviest certificate modules

Track G3 targets the certificate build cap, after G2 (`reviews/G2-golf.md`). The S-I run
(40810876665) took 882 s against `build_s = 600`. The brief listed 20 modules. Of these:

- 17 were examined;
- 3 were skipped, because they hold another track's uncommitted edits (§3);
- 7 next heaviest `FRX*` modules of `Solution`'s closure were added.

Twelve modules were edited. No statement changed.

The work is uncommitted, in the worktree at HEAD `4ac68fc`. The build tree is `logs/fr-build-G3`
(copied from `logs/fr-build-G2`; `MINE.txt` lists the 28 examined modules). Logs are in `logs/G3/`,
and the running record is `stages/G3-JOURNAL.md`.

## 1. Result

**Method.** As in G2:

- sequential elaboration, one pinned core: `lean -DElab.async=false --profile`;
- CPU time is user + sys;
- "before" is the saved original (`logs/G3/before/`), "after" is the worktree, both against the same
  tree;
- before and after alternate, two rounds;
- each figure is the minimum of the two runs.

The logs are `logs/G3/measure-fin{1,2}/` and `measure-frx{1,2}/` (`summary.txt`). "7763" is the
EPYC 7763 runner's CPU-s (`logs/S-I/run-40810876665/build-modules.txt`).

| module | 7763 | before: CPU s, min (runs) | after: CPU s, min (runs) | change | kernel s, before → after |
|---|---|---|---|---|---|
| FRSoundness4R4Outs | 24 | 36.3 (36.3 / 41.2) | 11.2 (11.2 / 11.3) | −69 % | 0.6 → 0.6 |
| FRSoundness4Agg | 22 | 18.6 (18.6 / 19.0) | 8.9 (10.7 / 8.9) | −52 % | 1.1 → 1.1 |
| FRVIRTplWalk | 20 | 19.9 (26.6 / 19.9) | 17.9 (23.5 / 17.9) | −10 % | 1.4 → 1.4 |
| FRKindWeight | 19 | 22.4 (25.6 / 22.4) | 19.4 (20.4 / 19.4) | −13 % | 3.1 → 3.2 |
| FRSoundness4R4PfFlag | 15 | 32.5 (32.5 / 40.2) | 18.1 (23.6 / 18.1) | −44 % | 3.0 → 1.2 |
| FRXOutRun | 16 | 15.6 (17.3 / 15.6) | 15.2 (16.0 / 15.2) | −3 % | 4.4 → 4.4 |
| FRXNode | 27 | 29.4 (29.6 / 29.4) | 21.7 (21.8 / 21.7) | −26 % | 8.9 → 8.7 |
| FRXChainSem | 13 | 18.8 (18.8 / 24.8) | 14.5 (14.6 / 14.5) | −23 % | 1.7 → 1.8 |
| FRXChainLoop | 17 | 16.4 (17.6 / 16.4) | 15.0 (15.8 / 15.0) | −9 % | 2.0 → 2.0 |
| FRXLog | 12 | 14.7 (14.7 / 16.3) | 11.7 (11.7 / 12.2) | −20 % | 0.5 → 0.5 |
| FRXChain | 12 | 13.5 (13.5 / 14.2) | 10.3 (10.3 / 10.7) | −24 % | 0.4 → 0.3 |
| FRXChainTop | 10 | 11.5 (14.7 / 11.5) | 10.2 (10.7 / 10.2) | −12 % | 1.2 → 1.0 |
| **total** | **207** | **249.8** | **174.0** | **−30 %** | **28.3 → 26.2** |

Each module's figure includes its fixed import cost, 4–6 s.

- **On the 7763.** Scaled module by module, the cut is about 58 of the 207 CPU-s these modules take
  there. This is an estimate from the local ratio, not a measurement.
- **Kernel time** does not rise in any module. The total falls from 28.3 to 26.2 s. FRSoundness4R4PfFlag
  falls from 3.0 to 1.2 s, because the `omega` proofs are now built from small contexts.
- **Noise.** The VM's load was 10–17. A single run varies by up to ±25 %, as in G2. FRXOutRun's
  −3 % is within that noise.

**Code lines** (`logs/org20/scripts/loc.py`, code column, the 12 edited modules): 5,225 → 5,283
(+58).

**Checks.**

- **Build.** `lake build FR Solution FRSubmission4Cert` is green: 2,581 jobs (`logs/G3/build-r1.log`).
- **Statements** (`logs/G3/tool/StmtHash.lean`, `tools/cmpstmt.py`; `logs/G3/check-r1.log`).
  - **"Before"** is the G2 tree's oleans (`logs/fr-build-G2`). Its sources equal HEAD for all 28
    modules, as checked with `cmp`. The dump is `logs/G3/stmt-before.txt`, read without writing to
    that tree.
  - **No user declaration changed.** 2,589 constants were compared: every type hash and every `def`
    value hash is unchanged, and nothing was added.
  - **Four auxiliary constants are no longer generated in these modules:**
    - `FR.Snd.R4.gFinPfR.eq_1`, after the `delta` of §2.5;
    - FRXLog's private `Prim.dst.match_1.eq_1`, `eq_2` and `splitter`, because the converted `simp`
      lists no longer name `Prim.dst`.

    These are equation lemmas, generated on demand. Lean generates them again wherever a later
    `simp` needs them. No declaration of the entry refers to them, and the build is green.
- **Axioms** (`logs/G3/tool/Ax.lean`, `logs/G3/axioms.log`). The 4,038 constants of the 28 modules,
  `FR.Sub4.certificate_sub4` and `RecursionFast.Challenge.certified` use only `propext`,
  `Classical.choice` and `Quot.sound`.
- **Source rule.** `logs/org20/scripts/source-rule.py submissions/flock-recursive` reports 365 files
  and 0 findings (`logs/G3/source-rule.log`).

## 2. What changed

### 2.1 Finding the cost: heartbeats per declaration

`trace.profiler` inflates some modules far more than G2 saw: FRVIRTplWalk took 364 CPU-s traced
against 25 untraced. Per-declaration trace figures are useless there.

- **The tools.** `logs/G3/tools/hb.py` writes a scratch copy of a module with Mathlib's
  `#count_heartbeats in` before every declaration. `hbrun.sh` ranks the declarations
  (`logs/G3/hb/`). Both run in scratch only, under `logs/fr-build-G3/scratch/`.
- **The limit.** Heartbeats over-state the CPU gain. In FRSoundness4R4PfFlag they fell 73 % while
  CPU fell 19 % at that step. So every change was confirmed by a CPU run.

### 2.2 Term-mode `rfl` and `exact` that unfold too much

- **FRSoundness4R4Outs `opsOut_roundOpsK … = 13 := rfl`.** This took 13 s untraced. The
  elaborator's `isDefEq` worked through the 15 ops of `roundOpsK` under `opsOut`. It is now
  `simp only [roundOpsK, opsOut, List.map_cons, List.map_nil, Op.outs, List.sum_cons, List.sum_nil,
  Nat.reduceAdd]`, at 0.04 s.
- **FRVIRTplWalk.** Six sites had the form `exact fun g s hs hp => (this g s hs hp).imp id fun h i
  => h i`.
  - **The cost.** Each made the elaborator check `hp : (StateT.run (dsumW …) s).2.gs.toList <+: G`
    against `this`'s `dvec 32 …` form. That unfolded the state monad down to `Decidable.rec`: 5–11 s
    traced per site.
  - **The fix.** `exact this` (or `exact key`) unifies the two `RelT` statements at the head.
  - **A failed alternative.** `unfold dsumW` before the old form did not help.
  - **Effect.** 98.6 → 78.1 M heartbeats.
- **FRSoundness4Agg `VA_extract_log`.** `hseg` proves its membership fact with `refine List.mem_map.2
  ⟨…, ?_, rfl⟩`. That step and the `rw`s after it unfolded the `set` variable `segs := aggSegs
  (piSizeOf seq4) …`, at 16 s traced.
  - `hsz'` is now stated before `set segs`, so `set` rewrites it too.
  - `hseg`'s proof starts with `clear_value segs`.
  - Effect: 18.6 → 8.9 CPU-s.

### 2.3 `simp … at *` on a large context (FRSoundness4R4Outs)

`genPhase4_out_lt` had four `simp [opsOut, Op.outs] at *`, at 11 s traced. With `at *` they also
simplified `key` and every other hypothesis. They are now `simp only [opsOut_cons, opsOut_nil,
Op.outs, Nat.reduceAdd] at this ⊢`.

### 2.4 `omega` on a 100-hypothesis context (FRSoundness4R4PfFlag)

`flag_gFinPf4` and `flag_pfTail4` build a register file in about 17 steps. Each step adds `set`
variables, sizes and `ExtA` facts.

- **The cost.** Every `by …; omega` there reads the whole context. The late ones took 2–8 s traced
  each, and their proof terms took 0.45 s each in the kernel.
- **The fix.** The 17 slowest now run `clear * - <the facts the goal needs>` first: for example
  `clear * - hv`, `clear * - hsb`, `clear * - hnf`, or `clear * -` alone after `rw [sR9, hce]`. One
  of them uses the fact directly: `b + 3 ≤ R10.size` is `b + 2 < R10.size` by definition, so it is
  `exact this`.

### 2.5 An equation lemma that is expensive to generate (FRSoundness4R4PfFlag)

`simp only [gFinPfR, …]` made Lean generate `gFinPfR.eq_1` for the 40-line `let` body. In
generating it, Lean first tries an `isDefEq` that fails (4.9 s traced). The two uses now
`delta gFinPfR` and then `simp only` the rest; `simp` still zeta-reduces the `let`s. No other module
uses `gFinPfR`.

Effect of §2.4 and §2.5 together: 32.5 → 18.1 CPU-s, and kernel 3.0 → 1.2 s.

### 2.6 `congr 1` on sums and products (FRKindWeight)

`congr 1` on `a + b = c + d`, `a * b = c * d` or `List.sum l = List.sum l'` first tries to close
the halves by `rfl`, and unfolds `Finset.sum` to do so. That cost 2.8 s and 4.8 s untraced at the
largest sites: `kwS_keys`, `hornerK_eq` and `kwS_fast`.

The 10 sites now use one of:

- `refine congrArg₂ (· + ·) ?_ ?_`;
- `refine congrArg₂ (· * ·) ?_ ?_`;
- `refine congrArg List.sum ?_`;
- `refine congrArg (· * e n true) ?_`.

Effect: 87.6 → 60.8 M heartbeats.

### 2.7 G2's two fixes on seven more `FRX*` modules

- **`attribute [local irreducible] entryK storeM`** (G2 §2.1), after the module's `open`.
  - FRXNode: 130.8 → 72.0 M heartbeats, with no other edit.
  - FRXChainSem and FRXOutRun also take `runPrims`. In each, one `rfl` needs `runPrims [] M = M`; it
    became `with_unfolding_all rfl` (`tools/fixrfl.py`). Effect: 80.6 → 68.5 and 51.4 → 45.4 M.
  - FRXChainLoop and FRXChainTop gain nothing from the attribute and do not carry it.
- **`simp +decide only`** (G2 §2.2; `tools/sdecloop.sh`, then `tools/prunemod.sh`).
  - Converted: FRXChainSem 26 calls (1 kept as it was), FRXChainLoop 18, FRXChain 7, FRXNode 7,
    FRXChainTop 9, FRXLog 3.
  - The converted lines over 100 columns were reflowed by hand.

## 3. Declined, and why

- **Skipped: another track is editing them.** The worktree holds uncommitted edits to three listed
  modules:
  - `FRSoundness4Pos` and `FRSoundness4Qry`: A2′'s CapChk. `fsItems4_length` goes from 482 to 484,
    and the counts from 8,905 to 8,907.
  - `FRVIRTplExt`: B0's split policy (`stages/B0-JOURNAL.md` §2).

  Edits here would mix into theirs. These are 7763 CPU-s 18, 16 and 15.
- **The `pureRun` chains: FRSoundness4R4FinSh, R4Fin, R4FinRS, R4FinLc** (7763: 28, 12, 13, 13).
  - **Where the time goes.** Almost all of it is one `simp only [pureRun, evalOp, rd_app, …]` per
    case over a 70–90-op program. `pureRun` accumulates its outputs as `L ++ vs`. Simp normalizes
    each append with `List.cons_append` over the whole list so far, and reads each register with
    `List.getD_cons_succ`, one step per index.
  - **The count.** `set_option diagnostics true` on FinSh's `flag_gFinSh` shows, per case, about
    2,900 `getD_cons_succ` and 2,700 `cons_append` rewrites. That is quadratic in the program's
    length, at 4–5 s per case.
  - **Tried.** A local lemma that skips 8 elements, `getD_cons8`. Simp never used it, and the run was
    slower.
  - **What a cure needs.** A read lemma that works on appended blocks (`rd (r ++ (A ++ B).toArray)`
    with lengths), or a run lemma that keeps the output in blocks. Either restructures every flag
    proof. That is per-module proof work, not a golf.
- **`decide +kernel` controls.** These are fixed statements, and only the kernel can run them:
  - FRSkip: `pinnedW_eq` 12.5 s and `M · Minv = I` 7.4 s, 22 kernel-s in all;
  - FRVerifierImplOps: `wByte_neg`, 3.5 s;
  - FRSoundness4Agg: `badSeg_view`, 2.7 s;
  - FRXChainFlock: `fsMsgs_items`, about 40 M heartbeats.

  As G2 found, a cheaper control would need a smaller statement. That is the owner's call.
- **Definition bodies: FRBlake2sGeneric `roundW`/`gW` and FRVIRTplDag `droundW`/`dgW`.** These are
  33, 12, 28 and 11 M heartbeats. The cost is 16 `get_elem_tactic` bound proofs per definition
  (`s[0]` … `s[15]`). Those proofs are part of each definition's value. Any other proof, such as
  `s[0]'(by decide)`, changes the value hash, and the brief forbids that.
- **Costs spread thin.** The rest of these modules has no single dominant step:
  - FRVerifierImplOps, FRNodeTarget4C, FRBlake2sWords, FRVIRTplSeg and FRSumcheck have
    `split_ifs <;> omega`, `simp` and `interval_cases` steps of 0.1–1 s each;
  - FRXDecLv, FRXMerge and FRXReadLv are the same.

  The remaining `FRVIRTplWalk` items are like this too. `acc_forM` (11 M) is the `dacc` state run
  under `<+:`; giving its argument explicitly did not help.

## 4. For the orchestrator

- **Heartbeats per declaration** (`tools/hb.py`, `tools/hbrun.sh`) find the expensive declarations
  without the trace's inflation. Confirm any change with a CPU A/B: heartbeats over-state the gain.
- **Three new patterns to look for elsewhere:**
  - `omega` late in a long, `set`-heavy proof: `clear * - …` first;
  - `congr 1` on sums and products: use `congrArg₂`;
  - `simp only [f]` on a big non-recursive `let` definition: `delta f` avoids generating `f.eq_1`.
- **The quadratic `pureRun` normalization** is the largest cost left in the finals' flag modules
  (§3). If the build cap still needs the time, a block-wise read lemma for `rd (r ++ L.toArray)` is
  where to start.
