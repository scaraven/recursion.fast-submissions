# S-E11 journal (track L-circ)

Build tree `logs/fr-build-SE11` (a copy of `fr-build-SE10`; `snap.sh` symlinks L-circ's modules
and the new `FRVIRTplGrp`, `FRVIRTplRun`). Logs in `logs/S-E11/`. Every lean/lake/probe command
runs in a 16 GB scope with a timeout.

## Baseline (HEAD `7a8cf13`)

- V (N30, 21 warm runs, core 30): **277.92 ms best, 295.40 median** (`vtime-N-base.log`).
- `evalMT` breakdown (`probe/EvBrk.lean`, each part forced before the next; `evbrk-base.log`):
  tables 2.2 ms, **`kprep3` 66.6 ms**, `ectx3` 1.6 ms per slot, per slot: sparse 11.1 ms,
  instances 51.7 ms (`G` key 26.4, `maskRows` 9.6). `evalMT` 189 ms best.
  S-E10's per-key figures carried a ≈ 74 ms constant: its closures recomputed the keys'
  preparation (`kprep3`) each time.

## Item 1: the run class

- `FRVIRTplFast` split: the first half is now `FRVIRTplGrp` (unchanged code); the triples and
  `ownSum` moved there too.
- `FRVIRTplRun` (new): `Pat`, `OwnP`, `runCh`/`findRun`/`prepOwn` (well-founded on the list
  length), `ownSumP`, `ownSumP_eq` (any pattern table), `ownSumP3`, `runIn`/`inrOf`(3), the search
  `runsOf`/`patsFor`/`mkPats`; and **`kprepF`** (one product per row and matrix; `kprepF_eq`), the
  keys' low tables once per evaluation (`preTabs`, `tabOr_eq`).
- First try: runs found almost nothing in the `G` key: its own inputs are numbered by first
  appearance in the block's rows, so `rowW′[k]`, state words and `colW[k]` interleave
  (`owndump-51.log`). Fix in the search: `sortOwn` (`FRVIRTplPlan`) renumbers a key's own inputs
  by the cell of its first member's forms; `ownOf` lists them by number. `Plan.ok` still checks.
- Result (`evbrk-2.log`): `evalMT` **86.3 ms best** (from 189): `kprep3` 30.5, tables 5.3,
  `ectx3` 5.5 per slot (the patterns' inner sums), sparse 11.3 per slot, instances 9.8 per slot
  (`G` key 1.26 ms, `maskRows` 0.54). 3,479 runs and 1,858 plain own forms per slot.
- **V: 196.77 ms best, 208.70 median** (`vtime-N-d1.log`). Kill rule: 196.8 + 18.5 (kind factor
  6, templates 4, `D̂` 1.5, `R` 7) = 215 ms ≤ 230: continue.
- Padding `G`'s output words: not done. After `sortOwn` the `G` key costs 1.26 ms per slot; padding
  would cut at most a run per word.

## Item 2: the `phiRS` split

- Done as a **split layout** of the one template, not two templates: `splitOf (.phiRS n) = (n,
  size (n − 2))`; instance `i`'s row `j` at `splitRow 7 3 i j` (groups of 16 instances: 16 heads of
  128 rows, then 16 tails of 8). `tinIRows` places the rows; `mkLay` reserves `⌈n/16⌉·17·128`;
  `tinPP` cuts head and tail blocks (two keys). `tplPhiRS` and `tplPhiRS_ok` unchanged.
- Rows per slot: max index 464,764 (from 526,204): **−61,440 per slot** (`evbrk-3.log`).
  `evalMT` 89.4 ms (the tail key's 512 instances per slot, +1.4 ms per slot).

## Item 3: `dag_mle`

- `FRNodeDag`: `WPlan`/`mkWPlan` (the search over the walk instance alone, checked against
  `tinIRows`), `dagHat`, `dag_mle` (from `slotV3_eq`/`slotV_eq`). Built first time.
- `daghat-1.log`: 5 keys, 83 instances; `dagHat` 13.9 ms (keys' preparation 8.4); sparse 151 ms;
  equal. A first run timed the sparse value lazily (1.25 ms): redone with `IO.lazyPure`.

## Item 4: plan time

- `plant-2.log` (slot 0, loaded core 30): compile 1.7 + `mkLay` 4.7 + compile 1.8 + `slotIRows`
  3.6 + `slotPPs` 8.7 + `groupPPs` 2.1 + `eqL` 1.3 + `mkPats` 0.2 s; `planOf` 46.9 s.
- Fixes:
  - `instRowA` (array lookups: the walk instance has `2^15` input forms in a list);
  - the walk's rows and bit sizes as closed constants (`tRows`/`tRbits`; the first `rfl` on a
    `Nat.size` form hit the kernel's recursion limit, fixed by defining the constant as `.rbits`);
  - `mkLay` reads each template's rows once.

  Then `planOf` 43.4 s (`e5eval-check.log`, core 22).
- `FRNodePlan`: `nodePlan`, `lPlan`, `implCN`. `coldwarm-init.log`: a process that does nothing
  in `main` takes 48.8 s, so the nullary constants are built at start.
- `coldwarm-2.log` (core 22): cold 230.9 ms, warm 205–220 ms.
- `vtime-N-d2` (245 ms) is void: INT-5's `vtime prof` was on core 30 (`ps`); later runs on
  core 22.

## Items 5, 6

- `mRowModel` 825,697 per slot (`norm_num`), `mRows_neg`.
- Dump: `nodedump/` (464,765 layout rows per slot, 3,631 blocks); `NodeDumpT` reads
  `Impl.nodePlan` and prints split/walk layouts.

## Final

- `e5eval-check.log`: `evalMT` = sparse over `nodeIRows` (equal true), 81.2 ms best.
- V (core 22) 192.87 best, 198.70 median (`vtime-N-d3.log`).
- Axioms: 60 names, standard three only. Source rule: 0 findings. Profiles in `profile-*.log`.
