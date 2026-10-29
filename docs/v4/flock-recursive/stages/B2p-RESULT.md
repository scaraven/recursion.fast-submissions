# B2′ (track L-circ): RESULT — the cap check as keyed blocks, the arenas' closed forms, the row model

Stage B2′ of `submissions/flock-recursive`, 2026-10-29, worktree `recursion.fast-submissions-rev44`
(`v4/rev44`). Started at HEAD `394f6ce`; the final build is a snapshot of HEAD **`e14db30`** (A3′ run 2)
plus B2′'s modules. Build tree `logs/fr-build-B2p` (copy of `fr-build-A2pp`). Logs `logs/B2p/`;
journal `B2p-JOURNAL.md`. Every lean/lake/probe ran in a 16 GB scope with a timeout. Nothing is
committed.

## Summary

| Done item | State |
|---|---|
| 1. cap check templated, `compileT_sound` unchanged | **done** at the compile level: `capChkOps`' op list is **unchanged** (A3′'s `FRSoundness4R4Cap` stays green); its four regular families are aligned blocks the plan groups into keys (176 keys, from 142) |
| V(N4) before → after (alternating, same core) | **419.4 / 420.3 / 425.5 → 275.7 / 274.9 / 276.2 ms** (`vab-B4.log`); `evalMT4` N4 305.9 → 147.7 ms, N2 295.8 → 144.7, N8 190.6 → 113.0 (`ab-B4.log`) |
| sparse rows per prototype | 81,088 / 79,737 → **22,776 / 21,461** |
| `plan4t init` ≤ 2 s | **not met: 7.1 → 5.9 s** (B0's pre-A2″ binary: 2.08 s on the same core). The excess is A2″'s: the V programs' process-start constants (2.9 s; −0.8 s by an edit request to `FRVIRFinals4`, §1.4) and the plan's own ≈ 2.7 s |
| 2. arenas | rows, interface, closed-form lemmas and the automaton **proved**; evaluator measured (arena₂ 23–43 ms per node). **Placement blocked: a slot region's cells are full** (§2.4) |
| 3. row model | `mRows4_le` re-based: N8 7,843,392, **1.019×** under `N_M/1.05`; `ProtoFit`/`inR` true |
| KATs | plan-form `KAT PASS`; cap-check KAT `PASS` (`capkat.log`) |
| build | green at `e14db30` + B2′: `lake build FR Solution FRNodeSound4Ctrl FRSoundness4XCtrl FRSoundness4TailShift FRSubmission4Cert FRNodeRows4Model FRNodeRows4ArenaRows` (4,935 jobs, `build-FR-2.out`). No new break in `FRSoundness4*` |
| axioms / source rule | 28 declarations, subsets of `propext, Classical.choice, Quot.sound` (`axioms.log`); 377 files, 0 findings (`source-rule.log`) |

## 1. Item 1: the cap check

### 1.1 The mechanism (deviation from PACK §11.7's "`tplExt` keys")

The five families are **multi-op** patterns; an `Ext` handles one op (one `Out`, one `ExtOk` proof per
op), so a `TKey` per family would need a new multi-op extension and its soundness proof. Instead the
compiler **aligns each family's instance** (`FRVIRCompile.alignOf`, performance only: `CS.align` is
generic in the hint) and the plan's existing grouping (`groupPPs`: the Merkle positions' and Horner
blocks' mechanism) turns the identical aligned blocks into one key each, with shared inputs (`one`,
`z^{2^t}`), partition inputs (the level weights) and own inputs (chain cells, `D_r`, `z^{k_r}`).
Consequences: **no statement and no proof of the soundness chain changed** (`compileT_sound`,
`compileTF4_soundAt`, `protoCS_soundAt`, `planData4_rows`, `evalMT4_eq`, `protoV4_eq`, `hfit4`), and
`capChkOps`' op list is untouched.

| Family | Block | Rows / stride | Cells / window |
|---|---|---|---|
| bit power (`bitPowOps`, from `bitOf k 0`) | one read | 45 / 48 (2 pieces) | 54 / 64 |
| read MACs (`macDOps`, at `ζ^r` register `≡ 0 mod 9`) | 9 reads | 63 / 64 | 63 / 64 |
| entry MACs (`macAOps`, at `o/32 ≡ 0 mod 23`) | 23 entries | 161 / 192 | 253 / 256 |
| power chains (`mulK a g; mulK (a+1) g`, `a ≡ 0 mod 21`) | 21 steps | 63 / 64 | 63 / 64 |

The head (17 ops) and the three final `assertEq` stay as they are.

### 1.2 Two things the cap check needed beyond the hints

- **Cells, not rows, were the limit.** At HEAD the template groups' cells already ended at 1,044,480
  of `2^20` (prototype 0): 809,552 cells allocated for 460,244 locals (`celldump-B1.log`). The blocks'
  cell padding overflowed (`inR false`, `inrdiag-B2.log`). Fix: the multi-instance MAC blocks above,
  and a **top-down cell layout** for the hint (`FRVIRTplSet.fitCells`: groups in decreasing cell bits
  from the region's aligned end, no alignment gaps; `mkLay`'s order left 27,392 cells before `rowW`).
  Only `layOfF4` (the hint generator) uses it.
- **`addK`'s running sums were quadratic** (`x ++ y` copies the sum: ≈ 10 M list cells, RSS 1.3 GB at
  plan start). `opOut`'s `addK` now builds `y ++ x` (the sum's list is shared): RSS 0.50 GB, init 7.1
  → 5.9 s. `opOut_sound`'s `addK` case re-proved by `add_comm`.

### 1.3 Measurements (core 22, alternating; `base` = HEAD + a hint regenerated at HEAD, since HEAD's was stale: `inR false`)

| | base | B2′ | log |
|---|---|---|---|
| V(N4) `vtime4 21 n4f` best | 419.4 / 420.3 / 425.5 | **275.7 / 274.9 / 276.2** | `vab-B4.log` |
| `evalMT4` N2 / N4 / N8 (min) | 295.8 / 305.9 / 190.6 | **144.7 / 147.7 / 113.0** | `ab-B4.log` |
| slotV3 p0 | 106.8 | 34.9 | `ab-B4.log` |
| `plan4t init` min | 7.1 s | 5.9 s | `ab-B4.log` |
| keys; pieces (instances) | 142; 7,042 + 7,287 (6,032 + 6,276) | 176; 10,042 + 10,290 (7,883 + 8,129) | `plan4t-B3.log` |
| sparse rows | 81,088 + 79,737 | 22,776 + 21,461 | same |
| region rows p0 / p1 | ≈ 693.5 k / 682 k (hint) | **699,648 / 686,080** | `nodedump4-run.log` |
| skeleton cells p0 | 268,288 | 276,535 | `celldump-B2.log` |

Pre-A2′ (A2pp's figures): V(N4) 233 ms, `evalMT4` N4 122–132 ms. What remains (`piececost-B4.log`,
slotV3 p0 34.4 ms): sparse 13.9 ms (22,776 rows), and the block holding the three final `assertEq`
3.7 ms (4,822 own inputs: the running sums' terms). V outside `evalMT4` is 130 ms against base's 116
(the program's own exec; A2″'s).

### 1.4 The plan start (not met; mostly A2″'s)

`init3-B3.log`: B0's binary 2.08 s, base 7.1 s. Decomposition (`Up*` probes: a binary that only
imports a module; `planstage-B4.log`; `initrest-B4.log`): `FRVIR4Mux`'s constants (the V programs)
**2.89 s**; the plan's stages ≈ 2.25 s (kms 0.25, compiles 0.54 + 0.31, slotRP 0.63, group 0.37,
pieces 0.15) + keys/patterns/prep/checks 0.4 s. `capChkOps` evaluates `fieldOffOf S fA` and
`fieldOffOf S fCaps` once per cap entry (`CapOpsTime`: 513 ms per call). **Edit request (RSV-V,
`FRVIRFinals4.capChkOps`, `logs/B2p/FRVIRFinals4-hoist.diff`)**: add `let aO := fieldOffOf S fA` and
`let cO := fieldOffOf S fCaps` after `let aA := …`, and call `macAOps aO cO k …`. Measured in my tree:
`capChkOps` 2.75 ms, `FRVIR4Mux` start 2.11–2.30 s, `plan4t init` 4.9–5.1 s. The op list is unchanged
(a `let`), so R4Cap is unaffected. (The same hoist in `FRVIR4.genPhase4` gained nothing.)

## 2. Item 2: the arenas

### 2.1 Built (`FRNodeRows4Arena`, `FRNodeRows4ArenaRows`)

- **The automaton** (generic in a commutative ring): bit products `pB` (`gN_pB`: `eq` is one; a
  range sum takes `f ≡ 1`), `pB_succ`, the parity split, `dRec` and **`dRec_eq`** (`dRec = Σ_{e<N}
  pB nt f (a+e)·pB nu g (c+e)` for `N ≤ 2^k`), the merged states `dIns`/`dStep`/`dRun` and
  **`dRun_eq`**, **`diag_eq`**. One function covers PACK §5.3's diagonal range sum, the
  shift-by-constant diagonal and the shift-window automaton (two shifts and the range's borrow: ≤ 8
  states a level).
- **The rows**: `cpRow one x y` (`one·(M x − M y) = 0`), `a1Rows one A1 R1 b0 N` (row `R₁+e` copies
  `sCell b0 e` to `A₁+e`), `ALv` (`t, S, a, B, C, E`) and `a2Rows one A1 A2 R2 v` (row `R₂+B+p·2^a+q`
  copies `A₁+E+S·p+q` to `A₂+C+p·2^a+q`), all **parametric in their addresses** (PK-M3's placement is
  open, §2.4).
- **Values** (the kernel never evaluates a layout): `a1_val`, `a2_val` (the matrices' MLEs as
  diagonal sums), `gN_sCell` (`eq(u, sCell b0 e) = kH(u)·eq(uH u, 4·b0 + e)`: H's cells are a shift by
  the constant `4·b0` on `u` without coordinates 2–6), and the evaluators **`a1V_eq`** (three runs per
  slot), **`a2V_eq`** (one run per position, two initial states: the aligned arena₂ side `+1`, the
  arena₁ window `−1`).
- **Controls**: `diag_ctl` (automaton = an independent list sum over `ℤ` at a shift leaving the
  cube; ≠ the unshifted value), `cpRow_ctl` (a copy row with `M x ≠ M y` fails; with equal cells it
  holds). Runtime check `arenatime-1.log`: `a1V`/`a2V` equal the sparse `rowsVal` (arena₁ at
  `N = 3,000`, arena₂ levels 0–1).

### 2.2 Measured (`arenatime-2.log`, PACK §5.4's "first thing to measure")

| | per | measured | PACK |
|---|---|---|---|
| arena₁ (`N = 96,880`, `k = 17`) | slot | 0.19–0.41 ms | 0.1 ms |
| arena₂ (871 positions, `k = 8`), high parts by `gN` | node | 40.8–43.2 ms | 26 (52 at 2× miss) |
| arena₂ with O(1) high-part lookups (tables) | node | 22.6–24.4 ms | |

Lever not taken: arena₂'s M side (aligned both ways) factorises per level, not per position (one
state of the two per run).

### 2.3 For B3/B4 (the interface)

With `w one = 1` and every arena row holding:

- `a1_cells : e < N → w (A1 + e) = w (sCell b0 e)`;
- `a2_cells : p < v.t → q < v.S → w (A2 + v.C + p·2^v.a + q) = w (A1 + v.E + v.S·p + q)`;
- **`arena_elem`**: `w (A2 + v.C + p·2^v.a + q) = w (sCell b0 (v.E + v.S·p + q))` (element in arena₁).

A consumer (a proof-field element, an answer, a `bitOf` bit's byte, a challenge) binds its import
register's cell to the arena₂ cell of its position `p` and element `q` (or arena₁'s, for FS items)
by an equality the template reads as a **fixed cell at a power-of-two stride**. Which element each
import class is (`E`, `S`, `q`) is B3/B4's; the values of the rows they add are `local`/`shared`
template rows. `a1V`/`a2V` are the plan's pieces for the arenas (`rowsVal` = `rows3`'s components).

### 2.4 Blocked: the slot region's cells (for the orchestrator)

Free cells below the templates (hint `FRNodeRows4Hint.b4.lean`): **7,945** (prototype 0), **56,905**
(prototype 1). The arenas need 96,880 + 132,096 (arena₂ allocated) + 8,320 (bits) = **237,296** cells
per region (PK-M3: in the slot's own region). Even a perfect packing of today's templates leaves
< 10 k. Options, cheapest first:

1. **Arena₂ without cells of its own**: copy arena₁ directly into the position blocks' import cells
   (already aligned windows, B0's stride policy): −132 k cells; the consumers read their own locals.
2. **A cell split for templates** (B0's row split, for cells): 349 k of the 809,552 template cells are
   window padding (`celldump-B1.log`: `tensorWK` 65 k + 48 k, `phiRS 7` 62 k, `walkAB` 46 k,
   `dotKF 64` 37 k, `tensorW 7` 26 k). Needs `instLin`'s `loc k ↦ cb + k` to take two bases: a change
   in the soundness chain's template core (`FRVIRTplCore`/`Ext`/`Build`/`Fast`).
3. The spare region (slot 0 only; PK-M3 forbids it for prototype-read cells).

## 3. Item 3: row model and fit

`FRNodeRows4Model` (33 → 32 code lines): prototypes **699,648 / 686,080** (measured, with the cap check
inside: §11.7's separate 52,400-row line is gone), pack map 212,576 (PACK §6.1 at today's stream:
arena₁ 96,880, pins 8,783). `regions_sum`: node 944,992, segment 980,424, spare 621,000.
`mRowModel4_eq`: N2 3,526,840, N4 5,487,688, **N8 7,843,392 (1.019× under 7,989,150)**: 18,220 more rows
per segment region and N8 fails. `mRows4_neg`: with A2″'s measured 791,421-row segment prototype the
region does not fit `2^20` and N8 not `N_M/1.05`. PACK §11.7's 1.035× assumed 52.4 k cap rows; the
aligned blocks take ≈ 68 k. `ProtoFit`: `inR true` at `e14db30` (`inrdiag`).

## 4. Files and costs

| Module | Code lines (`loc.py`) HEAD → now | Theorems | CPU-s (user, sequential, 2 runs; HEAD's version alongside) |
|---|---|---|---|
| `FRVIRCompile` | 902 → 935 | 63 | 29.9 / 29.7 (HEAD 33.3 / 29.9) |
| `FRVIRTplSet` | 484 → 507 | 35 | 13.3 / 13.2 (HEAD 13.0 / 13.0) |
| `FRNodeRows4Model` | 33 → 32 | 4 | 3.5 / 3.7 (HEAD 3.6 / 3.8) |
| `FRNodeRows4Hint` | 35 → 36 | 0 | 3.3 / 4.4 |
| `FRNodeRows4Arena` (new) | 145 | 12 | 6.9 / 7.2 |
| `FRNodeRows4ArenaRows` (new) | 160 | 18 | 5.6 / 5.8 |

`cpu.log` (+≈ 2.7 s system each, the import load). Net ≈ +12 CPU-s, all in the two new modules.
Probes (dev only, `logs/fr-build-B2p/probe/`): `CellDump`, `InRDiag`, `CompTime`, `StepScan`,
`CapOpsTime`, `InitRest`, `ArenaTime`, `Up*`; `PieceCost`/`SegDump4` copied from B0.

## 5. Edit requests and coordination

1. **`FRNodeRows4Hint` (mine) was overwritten in the worktree by RSV-V** (its `laydump4` at its own
   program with the pre-B2′ policies). It is stale against B2′'s `alignOf`/`fitCells` either way. At
   a commit of B2′ **without** RSV-V's V: use `logs/B2p/FRNodeRows4Hint.b4.lean` (HEAD's program,
   `inR true` at `e14db30`). **With** RSV-V's V: regenerate on the union (`laydump4`, then
   `python3 -I logs/B2p/mkhint.py <hint> <log>`) and check `inR` (`plan4t init`). I did not overwrite
   RSV-V's working copy.
2. `FRVIRFinals4.capChkOps` (RSV-V): the `fieldOffOf` hoist (§1.4).
3. `FR.lean`: add `import FRNodeRows4Arena` and `import FRNodeRows4ArenaRows`.
4. `capChkOps`' op list: **no change needed** (R4Cap unaffected).

## For P2

- Only row and cell indices move, plus the term order inside `addK` forms; the program and the
  witness values are unchanged. New `logs/B2p/nodedump/`: `plan-form-p{0,1}.bin` (1,080,276 /
  1,097,312 bytes, 176 keys), `planform_kat.py`: 649,341 / 641,657 rows rebuilt, 0 differ, **KAT
  PASS**. Template cells are laid top-down from the region's end (`fitCells`): P2 must re-embed the
  plan form and any vector it indexes by cell or row, and rerun its start-up KAT. Regenerate again
  after RSV-V's V and the hint (§5.1).

## For B3/B4

§2.3's interface; the arenas' addresses (`A₁`, `R₁`, `A₂`, `R₂`, the `ALv`s) are parameters until §2.4
is decided. The evaluators `a1V` (per slot) and `a2V` (per node, both prototypes) are proved equal to
the rows' sparse value; feeding them the plan's eq tables for the high parts gives ≈ 23 ms per node.

## Open questions

1. The cells (§2.4): which lever, before any arena is placed.
2. `plan4t init` ≤ 2 s: with the hoist ≈ 5 s; the rest is the V programs' construction (≈ 2.1 s) and
   the plan (≈ 2.7 s at 176 keys and 20 k pieces). A target for A2″'s programs or a revised bound.
3. The remaining cap-check cost in `evalMT4` (≈ 8 ms per prototype): the running sums' terms in the
   final asserts (3.7 ms). Materialising each MAC block's partial sum inside the block would make it
   O(1) per block; it changes the compiled rows (a new extension with its `ExtOk` proof).
