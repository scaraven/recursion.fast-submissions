# B5 RESULT: V's cost of the stacked `evalM` (the per-kind `linkV4`)

Track B5, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `face798`
(pulled, up to date). Build tree `logs/fr-build-B5` (a copy of `fr-build-RSV2`; `MINE` =
`FRNodeRows4Plan FRVIRTplFast FRVIRTplRun FRVerifierImplNode4F`). HEAD's `FRSoundness4*` are red,
and `FRVerifierImplNode4F` imports them, so the tree carries RSV-V2's four sorried copies
(`logs/RSV2/sorried-copies/`). Logs are in `logs/B5/`. Journal: `stages/B5-JOURNAL.md`. No sub-agents,
nothing committed. Only `FRNodeRows4Plan` and `FRVerifierImplNode4F` were edited. `FRVIRTplFast`
and `FRVIRTplRun` are unchanged.

## 0. Summary

- **δ at full support drops from +71 ms to +25 ms of V(N4).**
  - The A/B ran alternating runs on core 29: 4 rounds × 21 runs per variant, best of each
    (`vtime-ab.summary`).
  - V(N4) with the own kind only: 276.6 → **263.8 ms**.
  - With all three kinds: 347.6 → **288.4 ms**.
  - The per-kind link sums went from ≈ 30 ms to 7.7–10 ms, plus ≈ 2 ms for each pinned key that no
    other kind has already computed.
- **The statements are unchanged**: `evalMT4_eq`, `evalMS4`, `planData4_rows`, `evalMX4_eq`,
  `evalMXS4`, `evalMN4_eq`, `implN4F_hM`, `implN4F_hMX` and `evalMX4_ctl`. Each statement was compared
  textually with HEAD. `hfit4` and `ProtoFit` are in modules this track did not touch.
- **Process start is unchanged within noise.** `plan4t init` has a median of 5.44 s user for
  `face798` and 5.45 s for B5, over 10 alternating runs (`plan4t-init-ab3.log`). Timed piece by
  piece, the new plan data costs ≈ 0.13 s (`xinit-3.log`).
- **All checks pass:**
  - plan-form KAT;
  - `RsvKat2`, identical to RSV-V2's output;
  - a new KAT, `MxKat`: the compiled `evalMT4`/`evalMX4` equal `face798`'s on 3 random points, for
    every kind and every support;
  - axioms: 37 theorems, all within `propext`, `Classical.choice` and `Quot.sound`;
  - source rule on HEAD plus B5: 0 findings.

## 1. What was built (code lines, the core's `loc.py`; `logs/B5/loc.txt`)

| Module | Change | code (HEAD → now) |
|---|---|---|
| `FRNodeRows4Plan` | the plan's link data, the new `linkV4`/`slotV4`/`evalMT4`, `slots_val`, controls | 574 → 863 |
| `FRVerifierImplNode4F` | `evalMX4` over a shared context; `hiTabs`, `ltb_hi`; `evalMX4_eq` re-proved by `slots_val` (`slots_true` and `slotV4_noPrev` removed) | 330 → 337 |

**`FRNodeRows4Plan`, by lever.**

- **(a) The link rows, grouped once.**
  - `LkG` holds, per kind and slot:
    - the head's length;
    - the head rows grouped (`grows`);
    - the node rows grouped, as a `Thunk`: only the fallback reads them;
    - the node rows' dictionary coding (c).
  - `Plan4` gains `lk2`/`lk4`/`lk8 = lkArr κ`, with proof fields `hlk*`. These are closed constants,
    built at process start.
  - `lkAt pl κ σ` reads the entry. Past the kind's slots it groups the rows itself.
    `lkAt_eq : lkAt pl κ σ = lkGOf κ σ` has no hypotheses.
- **(b) The pinned elements, shared across kinds.**
  - `runsOf b0 j ps` gives two structures. Runs group the elements by (row block, cell block), with
    items (row low, cell low). Value classes are `PCls`: `wfSeg`'s 8,783 values take 24 distinct
    values, each with its rows by row block.
  - `prIn tlo slo` gives the inner sums:
    - per run, `Σ tlo·slo`: one product per element;
    - per class and row block, `Σ tlo`: additions only.
  - These read only the low tables, which every `logM` shares.
  - `prVal thi shi e1` combines them per kind: two products per run and one per (class, row block).
    Before, `wfSum` took five products per element.
  - **`prVal_runs`**: `prVal (prIn (runsOf …)) = wfSum …`. The existing `wfSum_eq` then gives the
    sparse rows.
  - `Plan4.pkr` holds the runs per distinct (first row, stream block), with `hpkr`. At HEAD there are
    3 keys:
    - `(1015816, 0)`: slot 0 of every kind;
    - `(2064393, 24236)`: slot 1 of `N2` and `N4`;
    - `(5210121, 96944)`: slot 4 of `N8`.
  - **Per call**, `thsOf` makes one `Thunk` per key in an `LCx` context, so the first kind that reads
    a key computes it and the other kinds reuse it. `innAt` looks a key up and regroups if the plan
    lacks it. `innAt_thsOf` proves it right. `CxAt cx lm t u` is the context's specification;
    `cxAt_mk`, `cxAt_lo` and `cxAt_of` build it.
- **(c) The node rows over a cell dictionary.** S-E13b's ≈ 8k rows per kind have 34–38k terms over
  11.1–11.8k distinct cells (`xstat5.log`).
  - `cellsOf` gives the sorted distinct cells. `crowsOf` codes each term as (index, coefficient)
    by binary search (`bsGo`).
  - **`cokB`** checks the coding once, at plan init: the indices are in bounds and `decRows`
    decodes back to the rows. If the check fails, `linkV4` uses `growsVal3` on the grouped rows.
  - `crowsVal3` computes each distinct cell's `eq` value once per call (1.2 ms) and reads every term
    from that array. **`crowsVal3_eq`** proves it equal to the rows' value, through `crows_sel`
    (one matrix at a time).
  - Measured: 9.2–10.4 → 6.5–6.9 ms per kind (`xdict.log`). All 16 slots pass the check.
- **`linkV4 pl cx κ σ`** puts the head, the pinned elements and the node rows together.
  **`linkV4_eq`** takes `CxAt cx lm t u` and proves `linkV4 = rows3 … (linkIRows4 κ σ)`.
- **`slots_val`** (new; the old body of `evalMT4_eq`): if the plan's checks passed, a kind's slot
  sums at any context `CxAt` at the point equal `evalMS4`. This holds with the prototype values at
  any `node = b` with `κ.hasPrev → b`. `evalMT4_eq` and `evalMX4_eq` both follow from it.

**`evalMX4` (in `FRVerifierImplNode4F`).**
- The low tables `loTab 11 t` and `loTab 12 u` are computed once, as are the key thunks.
- The high tables are two `Thunk`s, one per `logM` (`N4` and `N8` share theirs), each computed on
  first use. Before, `ltbOf` built `L2` and `L4` in full on every call.
- **Prototype 0** (the previous node's) is evaluated only if `N2` or `N4` has nonzero coefficients.
  `N8` has no previous-node slot, so an `N8` node's own call no longer computes `ectx3` and
  `slotV3 p0`: ≈ 40 ms by `plan4t-base.log`. This was not measured on a V(N8) run.

**Dev probes** (build tree only):
- `XBrk5`: the parts of `linkV4` at `face798`.
- `XStat5`, `XStat6`: the shape of the rows and of `wfSeg`.
- `XDict`: the dictionary prototype.
- `XBrk6`: the parts after B5.
- `XInit`: the cost of the plan data.
- `MxKat`: the KAT against `face798`'s `linkV4`/`slotV4`/`evalMT4`/`evalMX4`, copied verbatim
  into the probe.
- `abv.sh`, `abv2.sh`: the A/B scripts.

## 2. Measurements

**V(N4), A/B** (`abv.sh`, RSV-V2's method).
- Setup:
  - `face798`'s binary (`base-bin/vtime4`) against B5's (`b5-bin/vtime4`);
  - VTime4's supports `s4`, `s2`, `s8` and none;
  - core 29, 4 rounds, best of 21 runs each.
- The load average ran from 4 to 13 (other agents' builds); the best values stand.

| Support | `face798` V(N4) | **B5 V(N4)** | Δ | `face798` `evalMX4` | **B5 `evalMX4`** |
|---|---|---|---|---|---|
| {N4} (own only) | 276.6 | **263.8** | −12.8 | 152.5 | **138.9** |
| {N4, N2} | 313.9 | **281.7** | −32.2 | 189.8 | **152.7** |
| {N4, N8} | 314.7 | **280.2** | −34.5 | 194.6 | **152.6** |
| all three | 347.6 | **288.4** | −59.2 | 226.0 | **164.4** |

- The `evalMX4` columns are the best of that support's in-process timing, measured in the same
  binary's runs.
- **δ (all three against own only):**
  - `face798`: +71.0 ms of V(N4) (RSV-V2 measured +50.6 under lighter load);
  - B5: **+24.6 ms**;
  - one extra kind: +16–18 ms, against +37–38 ms before.
- **On RSV-V2's basis**, where `V̄_i` rose 0.440 s for +50.6 ms (8.7 s per s):
  - B5's full-support δ is ≈ **+0.21 s** of `V̄_i` per step, against RSV-V2's +0.46 s;
  - the own-kind call is ≈ 0.11 s cheaper.
- Medians of medians, all three kinds: 380.8 → 316.0 ms.
- **The final binary** (`b5f-bin`) differs only in the plan's init: the fallback grouping became a
  thunk, and `cellsOf`'s sort was tried and reverted. A 2-round re-run against `face798`
  (`abv2.sh`, `vtime-ab2.*`, heavier load) agrees:
  - own kind: 292.5 → **260.0**;
  - all three: 348.5 → **290.9**;
  - δ: +56.0 → **+30.9** ms;
  - `evalMX4`, all three: 225.3 → 164.2.
  `RsvKat2` on the final binary is again identical to RSV-V2's (`rsvkat2-2.log`).

**Where the time goes now** (`xbrk6-2.log`, before the two init-only changes):

| per kind | `face798` (`xbrk5-base.log`) | B5 |
|---|---|---|
| pinned elements | 4.8–5.5 ms per packed slot (2 per kind) | ≈ 2 ms per key, once per call (shared); ≈ 0.2 ms per slot per kind |
| node rows (slot 1) | 9.2–10.4 ms + 7.1–10.3 ms of regrouping | 6.5–6.9 ms (of which 1.2 ms is cell values) |
| link sums, whole kind | 29–32 ms | 7.7 / 8.5 / 10.0 ms (`N2`/`N4`/`N8`, keys computed) |
| high tables | `L2` and `L4` always built (2.6 + 3.9 ms) | on first use |

**`evalMX4` alone** (`xbrk6-2.log`), for N4 / +N2 / +N8 / all: 139.7 / 145.4 / 148.5 / 159.1 ms.
`protoV4` (≈ 125 ms) is now ≈ 80 % of the own-kind call.

**Process start.**
- `plan4t init`, 10 alternating runs on core 31 (`plan4t-init-ab3.log`), user time:
  - `face798`: median 5.44 s, minimum 5.16 s;
  - B5: median 5.45 s, minimum 5.18 s.
- The B5 data, timed piece by piece (`xinit-3.log`):
  - `lkArr` 41 / 39 / 44 ms (`cellsOf` 16, `crowsOf` 11, `cokB` 12, per kind);
  - `runsOf` for the 3 keys: 8 ms;
  - total ≈ 0.13 s.
- Two earlier 5-run and 6-run A/Bs (`plan4t-init-ab.log`, `-ab2.log`) were too noisy to use (load up
  to 13).

**CPU-s** (`lean -DElab.async=false --profile`, one core, user + system, including ≈ 4.3 s of
import; `cpu-final.txt`, `profile-*.log`):

| Module | HEAD | B5 | type checking |
|---|---|---|---|
| `FRNodeRows4Plan` | 18.9 | 24.3 | 0.71 → 1.03 s |
| `FRVerifierImplNode4F` | (11.7 in RSV-V2's table) | 15.8 (14.5 in an earlier run under less load) | 1.19 s |

## 3. Controls and KATs

- **New controls** (`FRNodeRows4Plan`, by `decide`):
  - `runsOf_ctl`:
    - (+) two elements in one row block and one cell block share a run, and two with one value share
      a class;
    - (−) an element 200 stream elements on (cell block 1) starts a new run, and one with another
      value starts a new class.
  - `cokB_ctl`:
    - (+) a coding that decodes to the rows passes;
    - (−) an index that points at another cell fails;
    - (−) an index past the dictionary fails.
  - `crowsOf_ctl`: (+) `crowsOf` against a sorted dictionary decodes to the rows; (−) against a
    dictionary missing a cell, it does not. `cellsOf` uses `mergeSort`, which `decide` cannot
    evaluate. It is not load-bearing: `cokB` checks any dictionary.
- **Unchanged and re-proved:** `evalMX4_ctl`, `implN4F_ctl`, `star_ctl`, `pieceInB_ctl`, `ivsOkB_ctl`
  and `idxNodupB_ctl`.
- **KATs:**
  - **Plan-form KAT: PASS** (`planform-kat.log`, `-2.log`). The node dump was regenerated at
    `face798` with this track (`logs/B5/nodedump/`). It rebuilds 649,761 and 641,656 rows, and
    0 differ.
  - **`RsvKat2`**: its output is identical to RSV-V2's `rsvkat2-3.log`, timing lines excluded
    (`rsvkat2-1.log`). It uses a toy `evalM`, so it does not read B5's code.
  - **`MxKat`: PASS** (`mxkat.log`, `mxkat-2.log` on the final code).
    - Over 3 random points, `evalMT4` equals `face798`'s for each kind.
    - `evalMX4` equals `face798`'s for each of the 8 supports, the empty one included.
    - My first `MxKat`, against the sparse sums over `nodeIRowsP`, had not finished after 10 min
      and I killed it.
- **Axioms** (`axioms.log`, `ax/AxB5.lean`): 37 theorems, all within `propext`, `Classical.choice`
  and `Quot.sound`.
  - They cover the new and re-proved theorems of both modules, `planData4_rows` and the controls.
  - None uses `sorryAx`.
  - Neither module contains `sorry` or `native_decide`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py`):
  - On the worktree: 405 files, 2 findings (`source-rule.log`). Both are the word `partial` in
    `FRSoundness4RsvMLE.lean`, which is RSV-S's untracked work in progress, not this track's.
  - On HEAD plus B5's two modules: 404 files, **0 findings** (`source-rule-head-plus-B5.log`).
- **Build**: `lake build FRVerifierImplNode4F` and the probes are green (4,737 jobs, using RSV-V2's
  four sorried `FRSoundness4*` copies for HEAD's red set).

## 4. Deviations, and how they interact with other tracks

1. **Beyond the brief's levers (a) and (b):**
   - the node rows over a cell dictionary (c);
   - the pinned constants by value class;
   - the lazy high tables;
   - prototype 0 skipped when the support has no `N2` or `N4`.

   All of them are inside `FRNodeRows4Plan` and `evalMX4`, under the same statements.
2. **Thunks.** The per-call sharing uses core `Thunk`. `thunk_get` (`(Thunk.mk f).get = f ()`) holds
   by `rfl`. No attribute or code-changing construct is involved.
3. **An elaboration trap, for whoever edits this next.** `isDefEq` between `loTab 11 t` and any term
   that only reduces to it unfolds the `2^11` table and times out at `whnf`. Examples are
   `(ltbOf lm t u).tlo` and `LTb.tlo ⟨loTab 11 t, …⟩`. The context lemmas therefore take the low
   tables as variables (`cxAt_lo`, `ltb_hi`), so that every match is syntactic.
4. **A1′'s spacers** (uncommitted in the worktree: `FRNodeRows4.lean`, `FRNodeRows4Pack.lean`,
   `FRNodeKinds4.lean`) change `packB`: every aggregate sub-slot gets a stream segment and up to
   137 head rows.
   - `linkV4_eq` uses only these shapes: `linkIRows4 = linkRowsB4 ++ packRows4 ++ extRowsC`,
     `packRows4 = packHead4 ++ packWf4`, and `packWf4`'s match on `packB` into `wfRows`. A1′'s
     diff keeps them, so the proof should carry over. This is not verified: A1′'s modules were not
     built here.
   - With the spacers, the pinned elements grow from 2 packed slots per kind to 3/5/8. That makes
     (b) worth more: `face798`'s `wfSum` would cost ≈ 5 ms per packed slot per kind, while B5
     computes each distinct key once (≈ 2 ms; ≈ 12 keys over the three kinds) and adds ≈ 0.2 ms
     per slot per kind.
   - Sharing across sub-slots by relative keys (row offset mod `2^11`, block mod 32) would not help:
     `sBlk = 24,238 ≡ 14 (mod 32)` and the head lengths differ.

## 5. Open questions and further levers

1. **`protoV4` is ≈ 125 ms of the ≈ 140 ms own-kind call**: key preparation 36 ms, and per
   prototype `tb4` 5, `ectx3` 5 and `slotV3` 37 ms.
   - **I found no remaining per-kind cost in `protoV4`.**
   - One per-call duplication remains: `tb4 pl 1` recomputes every table below coordinate 20,
     which `tb4 pl 0` already has. The two points differ only at coordinate 20 (`starPt`).
     Sharing them would save at most ≈ 5 ms. It would need a `Tb` built from the other prototype's,
     with a `loTab_congr` lemma for its low tables. I did not implement it.
2. **The node rows remain the main per-kind cost** (6.5–6.9 ms). Their form products (≈ 19k per kind)
   and non-unit coefficients (≈ 7k) are inherent to the row-major sum. A transposed sum (per cell)
   comes out at about the same count (≈ 40k against ≈ 37k products).
3. **`V(N8)`'s saving from skipping prototype 0 is not measured.** VTime4 times only `N4`. It
   should be checked when P2 or S-I measures `N8`.
4. **Code size.** `FRNodeRows4Plan` grows by 289 code lines. If the entry's line budget is tight, the
   dictionary (c) is the largest separable piece: ≈ 120 lines for ≈ 3 ms per kind present.
