# B2′ (track L-circ): JOURNAL

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `394f6ce`. Build tree
`logs/fr-build-B2p` (copy of `fr-build-A2pp`; `MINE.txt` = my modules, symlinked; every other module
from HEAD). Logs `logs/B2p/`.

## 2026-10-29

- **Setup.** Copied `fr-build-A2pp` → `fr-build-B2p`; `run.sh`/`prof.sh` log to `../B2p/`. Built the
  probes at HEAD (4,731 jobs).
- **HEAD's hint is stale** (`plan4t-init-head0.log`: `inR false`): the merge kept A2″'s
  `FRNodeRows4Hint`, laid out before B0's policies. So the "before" is HEAD + a hint regenerated at
  HEAD (`laydump4-head.log`; `FRNodeRows4Hint.base.lean`), binaries `base-bin/`: `inR true`, keys 142,
  pieces 7,042 + 7,287, sparse rows 81,088 + 79,737 (`plan4t-base0.log`), `plan4t init` 7.1 s.
- **RSV-V edits `FRVIRTpl4Bridge`** in the worktree (`protoR_ctl` at `cLen 24234`, with its uncommitted
  `FRNodeKinds4`). I do not edit that module, so it is taken from HEAD in my tree (dropped from
  `MINE.txt`). All my figures are at HEAD's V (`cLen 24220`).

### Item 1: the cap check as keyed blocks

- **Mechanism chosen: aligned skeleton blocks, grouped into keys by the plan** (the Merkle positions'
  and Horner blocks' mechanism; `FRVIRCompile.alignOf`), not `TKey` templates. Reason: the five
  families are multi-op patterns, and an `Ext` handles one op (one `Out`, one `ExtOk` proof per op); a
  `TKey` per family would need a multi-op extension and a new soundness proof. The alignment hint is
  performance only (`CS.align` is generic in the hint), so `compileT_sound` and every statement keep
  their statements with no proof change. The plan's `groupPPs` turns each family's identical aligned
  blocks into one key (shared inputs: `one`, `z^{2^t}`; partition inputs: the level weights; own: the
  chain cells, `D_r`, `z^{k_r}`).
- **B1** (one block per instance: bit power 45 rows/54 cells → 48/64; MACs 7 → 8 rows, 8/16 cells;
  chains every 21 steps): `inR false`. Diagnosis (`celldump`, new probe): **the slot region's cells,
  not its rows, are full.** At HEAD prototype 0's template cells end at 1,044,480 of 1,048,576
  (`2^20`): the skeleton takes 268 k cells, the templates' groups allocate 809,552 cells (each instance
  a `2^cregion` window) for 460,244 locals. B1's cell padding (+16.4 k) overflows.
- **B2**: fewer padded cells — MACs of 9 reads per block (`p ≡ 0 mod 9`, the `ζ^r` register: 63 rows,
  63 cells), MACs of 23 cap entries per block (`o/32 ≡ 0 mod 23`: 161 rows at a 64-row stride, 253
  cells in 256); and a **first-fit cell layout** for the hint (`fitCells` in `layOfF4`). Still
  `inR false` (`inrdiag-B2.log`, new probe `InRDiag`): the `tensorW 7` group ends at 1,051,584; first
  fit leaves 10.5 k cells below `walkAB`'s `2^17` alignment.
- **B3**: **top-down cell layout** (groups in decreasing cell bits from the region's aligned end:
  no alignment gaps). `inR true`, keys 176, pieces 10,042 + 10,290 (instances 7,883 + 8,129), sparse
  rows **22,776 + 21,461** (from 81,088 + 79,737).
- **A/B, base vs B3** (`ab-B3.log`, 4 rounds, core 22 — core 30 is shared with RSV-V's `rsvcells`,
  which halved the first attempt): `evalMT4` N4 307.0 → 140.8 ms (min), slotV3 p0 107.7 → 30.6 ms,
  init 7.1 → 7.4 s.
- **The plan start is A2″'s, not B2′'s.** Three-way `plan4t init` (`init3-B3.log`, core 22): B0's
  binary (pre-A2″) 2.08 s, base 7.1 s, B3 7.1 s. RSS 404 MB (B0) → 1.30 GB. Causes found:
  1. `addK`'s form `x ++ y` copies the running sum: the cap check's six sums of 871/1,536 terms are
     built in `O(n²)` terms (≈ 10 M list cells). **Fix (mine, `FRVIRCompile.opOut`): `y ++ x`** (the
     sum's list is shared): RSS 1.30 GB → 0.50 GB, init 7.1 → 5.9 s. `opOut_sound`'s `addK` case
     re-proved (`add_comm`); no statement changed.
  2. Process-start constants (`Up*` probes: a binary that only imports a module): `FRVIR4Mux` (the
     V programs) 2.89 s; `capChkOps` evaluates `fieldOffOf S fA`/`fCaps` once per cap entry
     (`CapOpsTime`: 513 ms for one call). Hoisting both out of the `flatMap` (build-tree experiment,
     `FRVIRFinals4-hoist.diff`): `capChkOps` 2.75 ms, `FRVIR4Mux` start 2.11–2.30 s, `plan4t init`
     4.9–5.1 s. RSV-V's module: an edit request. The same hoist in `FRVIR4.genPhase4`'s `.queries`
     case gained nothing (2.14 s) and is not requested.
  3. The plan's own stages (`planstage-B4.log`): kms 0.25, compiles 0.54 + 0.31, slotRP 0.63, group
     0.37, pieces 0.15 s; keys/pats/prep/checks 0.4 s (`initrest-B4.log`).
- **RSV-V overwrote `FRNodeRows4Hint` in the worktree** (11:43, its own `laydump4` at its program,
  pre-B2′ policies). My tree now takes the hint from `fr-build-B2p/override/` (my regeneration at
  HEAD's program, `FRNodeRows4Hint.b4.lean`); `snap.sh` copies overrides last.
- **B4 = B3 + the `addK` fix** (`b4-bin/`). V(N4) alternating (`vab-B4.log`, 3 rounds): 419.4 /
  420.3 / 425.5 → **275.7 / 274.9 / 276.2 ms**; `evalMT4` (plan4t, `ab-B4.log`) N2 295.8 → 144.7,
  N4 305.9 → 147.7, N8 190.6 → 113.0 ms; init 7.1 → 5.9 s. `piececost-B4.log`: slotV3 p0 34.4 ms =
  sparse 13.9 ms (2,159 pieces, 22,776 rows) + the block holding the three final `assertEq`
  (4,822 own inputs: the running sums' terms) 3.7 ms + the keyed blocks.
- `nodedump4-run.log`: region rows 699,648 / 686,080; `planform4-run.log` + `planform-kat.log`:
  KAT PASS (649,341 / 641,657 rows rebuilt, 0 differ).

### Item 2: the arenas

- `FRNodeRows4Arena` (the automaton, generic in a commutative ring): green first time after two proof
  fixes; `diag_ctl` by `decide` over `ℤ`.
- `FRNodeRows4ArenaRows`: rows, interface, values. Term-mode `h _ ⟨…⟩` timed out at `whnf`
  (unifying the row pair); fixed by naming the pair. `congr 1` on a difference of sums timed out;
  `sub_right_inj` instead.
- `arenatime-1.log`: automaton = sparse sum (arena₁ at `N = 3,000`, arena₂ levels 0–1): `equal true`.
  `arenatime-2.log`: arena₁ (`N = 96,880`) 0.19–0.41 ms per slot; arena₂ (871 positions) 40.8–43.2 ms
  per node with `gN` high parts, 22.6–24.4 ms with O(1) high-part lookups.
- **Placement blocked by cells**: free cells below the templates: 7,945 (p0), 56,905 (p1); the arenas
  need 96,880 + 132,096 + 8,320 = 237,296 per region.

### Item 3

- `FRNodeRows4Model` re-based: 699,648 / 686,080, the cap check inside the prototypes, pack map at
  today's stream (212,576). N8 7,843,392: 1.019× under `N_M/1.05`. `mRows4_neg` on A2″'s measured
  791,421-row segment prototype.
