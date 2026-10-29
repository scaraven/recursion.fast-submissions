# B5 journal: V's cost of the stacked `evalM` (`linkV4` per kind)

Track B5, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `face798`
(pulled: up to date). Build tree `logs/fr-build-B5` (a copy of `fr-build-RSV2`; `MINE` =
`FRNodeRows4Plan FRVIRTplFast FRVIRTplRun FRVerifierImplNode4F`; RSV-V2's four sorried
`FRSoundness4*` copies put back into `src/`, since HEAD's are red and `FRVerifierImplNode4F` imports
them). Logs `logs/B5/`. No sub-agents, nothing committed.

## 2026-10-29

- Baseline binaries built at `face798` (`logs/B5/base-bin/`: `vtime4`, `xbrk`, `plan4t`, `rsvkat2`).
- `XBrk5` (`xbrk5-base.log`), per kind and slot, at `face798`:
  - pinned elements (`wfSum`, 8,783 per packed slot, 2 packed slots per kind): 4.8–5.5 ms per slot;
  - node rows (`growsVal3` on rows grouped beforehand): 9.2–10.4 ms (slot 1);
  - their grouping (`grows`), rebuilt per call: 7.1–10.3 ms;
  - head rows: < 0.1 ms.
  So ≈ 30 ms per kind is ≈ 10 (pins) + 10 (node rows) + 9 (regrouping).
- `XStat5` (`xstat5.log`): the node rows have 34–38k terms over 11.1–11.8k distinct cells, 18.5–19.9k
  non-empty forms, 28–31k cell groups, 6.1–7.3k non-unit coefficients. One `F` product ≈ 90–170 ns,
  one sum ≈ 14 ns. `XStat6`: `wfSeg`'s 8,783 values take 24 distinct values.
- `plan4t` at `face798` (`plan4t-base.log`): `protoV4` ≈ tb4 5 + kp 36 + ectx3 5 + slotV3 37 per
  prototype; `plan4t init` 5.21 s.
- Lever (a): `LkG` (head rows and node rows grouped) per kind and slot in `Plan4` (`lk2/lk4/lk8`,
  `hlk*`); `lkAt` with `lkAt_eq` (no hypotheses: past the slots it regroups).
- Lever (b): the pinned elements in runs of (row block, cell block); a run's inner sums read only
  `tlo`/`slo`, which every `logM` shares. `Plan4.pkr` holds the runs per distinct (first row, stream
  block): 3 keys over the three kinds (slot 0 of every kind; slot 1 of `N2`/`N4`; slot 4 of `N8`). Per
  call, `thsOf` makes one `Thunk` per key, so a key's inner sums are computed by the first kind that
  reads them. `prVal_runs`: runs → `wfSum` (then the existing `wfSum_eq`).
- Elaboration trap: any `isDefEq` between `loTab 11 t` and a term that only reduces to it (e.g.
  `(ltbOf lm t u).tlo`, `LTb.tlo ⟨loTab 11 t, …⟩`) unfolds `loTab` (a `2^11` table) and times out.
  Fixed by stating the context lemma with the low tables as variables (`cxAt_lo`), so that every
  match is syntactic.
- `xbrk6-1.log` (a)+(b): per kind link sums 10.7–12.7 ms (inner sums computed), 18–20 ms fresh;
  `evalMX4` 160 / 164 / 158 / 176 ms (N4 / +N2 / +N8 / all).
- (b′) The constants `k` of the pinned elements by value class (24 classes): the `C` and `A` sums are
  additions per element and one product per (class, row block); the runs keep one product per
  element (`tlo·slo`). `clsIns`/`blkIns`, `clsIns_val`.
- (c) The node rows over a cell dictionary: `cellsOf` (sorted, distinct), `crowsOf` (binary search
  `bsGo`), checked at plan init by decoding (`cokB`: bounds + `decRows = rows`), fallback
  `growsVal3`. `XDict` prototype (`xdict.log`): 9.3–10.1 → 6.5–6.9 ms per kind (cell values 1.2 ms).
  `crowsVal3_eq` via `crows_sel` per matrix.
- `xbrk6-2.log` (a)+(b)+(b′)+(c): link sums per kind 7.7–10.0 ms (inner sums computed), 11.8–15.1
  fresh; `evalMX4` 139.7 / 145.4 / 148.5 / 159.1 ms. All 16 slots `eok`.
- `evalMX4` computes prototype 0 (the previous node's) only if `N2` or `N4` is in the support
  (`N8` has no previous-node slot); an `N8` node's own call saves `ectx3` + `slotV3 p0`.
- KATs: plan-form PASS (`planform-kat.log`, node dump regenerated in `logs/B5/nodedump/`);
  `RsvKat2` identical to RSV-V2's `rsvkat2-3.log` (`rsvkat2-1.log`; it uses a toy `evalM`);
  `MxKat` (new, `mxkat.log`): `evalMT4` and `evalMX4` against `face798`'s evaluation copied into the
  probe, 3 random points, every kind and every support: PASS. A first `MxKat` against the sparse sums
  over `nodeIRowsP` did not finish in 10 min (killed).
- Controls added: `runsOf_ctl`, `cokB_ctl`, `crowsOf_ctl` (`cellsOf` uses `mergeSort`, which
  `decide` cannot evaluate; it is not load-bearing).
- A/B (`abv.sh`, core 29, 4 rounds, alternating `face798` / B5 per support) started.
- A/B done (`vtime-ab.summary`), with V(N4) best values:
  - own kind: 276.6 → 263.8;
  - +N2: 313.9 → 281.7;
  - +N8: 314.7 → 280.2;
  - all: 347.6 → 288.4.
  δ at full support is +71.0 → +24.6 ms.
- Init: `XInit` puts the plan data at ≈ 165 ms. Two changes then:
  - the fallback grouping `ex` becomes a `Thunk`, saving 8–10 ms per kind;
  - `cellsOf` with `Array.qsort` took 75–93 ms (`xinit-2.log`), against `mergeSort`'s 16 ms, so I
    reverted to `mergeSort`.

  The final data costs ≈ 132 ms (`xinit-3.log`). `plan4t init`, 10 alternating runs: median 5.44
  (`face798`) against 5.45 s (B5) of user time (`plan4t-init-ab3.log`). The 5- and 6-run A/Bs before
  it were noise.
- Final code: `MxKat` PASS (`mxkat-2.log`), plan-form KAT PASS (`planform-kat-2.log`), 37 axioms clean,
  source rule 0 findings on HEAD plus B5 (the worktree's 2 findings are in RSV-S's untracked
  `FRSoundness4RsvMLE.lean`). CPU-s: `FRNodeRows4Plan` 18.9 → 24.3, `FRVerifierImplNode4F` 15.8.
- Confirmation A/B with the final binary (`abv2.sh`, 2 rounds, `vtime-ab2.log`, heavier load), V(N4)
  best: own kind 292.5 → 260.0, all 348.5 → 290.9. `RsvKat2` on the final binary is identical
  (`rsvkat2-2.log`).
