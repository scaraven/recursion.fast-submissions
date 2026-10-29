# B0 (track L-circ): JOURNAL — the prototype row levers

Brief: `design/PACK-4.4.md` §7.1 "B0". Worktree `v4/flock-recursive`; base HEAD `ee044f2` (RET-2 in,
A2′ not landed). Build tree `logs/fr-build-B0` (a copy of `logs/fr-build-SE14`, `snap.sh` on HEAD with
`MINE.txt` symlinked; builds pinned to cores 28–31 by `b.sh`, every lean/lake/probe in the 16 GB
scope with a `timeout`). Logs in `logs/B0/`. Nothing committed.

## 0. Baseline on HEAD `ee044f2` (`logs/B0/nodedump4-base.log`, `laydump4-base.log`)

- prototype 0: 603,404 indexed rows, **730,493 rows in the region**; prototype 1: 593,997 indexed,
  **725,885**. The layouts equal `FRNodeRows4Hint` (doc comments aside).
- Baseline binaries kept in `logs/B0/base-bin/` for the alternating runs.

## 1. Where the rows go (from S-E13a's dump, identical prototypes)

The brief's two levers are **stale**:

- `phiRS`'s 134-in-256 waste was already removed by S-E11's split (`splitOf (.phiRS 7) = (7, 3)`): 512
  instances take 69,632 rows = 136 each. What is left there: 1,024 rows.
- S-E6's skeleton padding (29,142 rows) is now 32,928 (p0) / 29,419 (p1) rows of empty alignment rows
  inside the skeleton (143,661 / 143,741 rows).

The template waste (instance stride `2^rbits` minus the template's rows, `logs/B0/` analysis of
`groups-p*.txt`) is **117,024 rows (p0) / 124,434 (p1)**, almost all in the kind-muxed Horner
templates that S-E12f added after S-E6:

| key | instances | rows | stride | waste p0 |
|---|---|---|---|---|
| `tensorW 7` | 882 | 35 | 64 | 25,549 |
| `tensorWK [19,18,19]` | 290 | 286 | 512 | 65,314 |
| `tensorWK [16,15,16]` | 178 | 241 | 256 | 2,655 |
| `tensorWK [13,12,13]` | 145 | 196 | 256 | 8,640 |
| `tensorWK [10,9,10]` | 132 | 151 | 256 | 13,755 |

The skeleton's padding, by block (p0): 125 Horner blocks of 383 rows in 512 (16,125); Merkle
positions of 30/50/38/46/26 rows in 64/64/64/64/32 (4,454 + 4,046 + 3,744 + 3,186 + 750); the rest
≈ 600.

So the levers are: (A) **a generic split policy for templates** (S-E11's head + tail layout, chosen
from the template's row count, not from the key); (B) **a skeleton alignment policy** that pads a
block to a short stride and lets the plan cut it into aligned pieces.

## 2. Lever A: the split policy (`FRVIRTplExt`, `FRVIRTplBuild`)

- `splitN nr`: with `r = size(nr − 1)`, `4 < r ≤ 12`, `a = r − 1`, `b = size(nr − 2^a − 1)`: split
  `(a, b)` iff `b < a`. `splitOfN k nr` (none for the walk), `splitOf k = splitOfN k (tRows k).length`.
  It reproduces `phiRS 7 ↦ (7, 3)`; gives `tensorW 7 ↦ (5, 2)` (36 rows), `tensorWK 286 ↦ (8, 5)`
  (288), `151 ↦ (7, 5)` (160); leaves 241 and 196 alone (their tail does not fit half the head).
- `splitRow`: **tails first** in a group (`g·2^b = 2^a` rows), then the `g` heads. A last group of
  `m < g` instances then takes `(m + 1)·2^a` (`splitEnd`), so a key with one instance takes `2^(a+1)`
  = its unsplit stride, not `(g + 1)·2^a` (heads-first would have cost maskN/slotW/lagrangeS
  thousands of rows each).
- Run-time cost: `splitOf` reads the template's rows, so it is computed once per key in `mkKM` (new
  field `KM.sp`, `mkKM_sp`), and `blkSize` no longer consults it (every caller matches the split
  first). `tinRP` matches on `e.sp`. `mkLay`/`mkLayI` use the row count they already have.
- Proofs: `tinRP_rows` gains `mkKM_sp` in its `simp` set; `mkKM_split`/`mkKM_blks` go through
  `keyInfo_split`; `dsimp only` before `split` (the match now reads a `let`). Controls
  `splitRow_phi` (four splits, the tails-first rows, `splitEnd 7 3 512 = 69,632` as before) and
  `splitOf_walk` (the walk, 128, 241, 16, 4,200 are not split), by `decide`/`norm_num`.
- `FRVIRTplExt`, `FRVIRTplBuild` build.

### Lever A measured (`logs/B0/laydump4-A1.log`, `nodedump4-A1.log`, `ab-A1.log`)

- Rows: **627,968 (p0, −102,525) / 614,400 (p1, −111,485)**; `inR true`.
- Pieces: 6,406 + 6,408 → 7,726 + 7,874 (keys 108 → 136); `evalMT4` (N4) in three alternating rounds
  against the base binary on core 30 at load ≈ 17: base best 122.2 / 125.5 / 123.2 ms, A 138.7 /
  131.0 / 121.9 ms — inside the load's noise (the machine is at 2× S-E12c's figures for both).

## 3. Lever B: the stride policy (`FRVIRCompile`, `FRVIRTplPlan`, `FRVIRTplBuild`)

The skeleton's blocks (new probe `probe/SegDump4.lean`, `logs/B0/segdump-A1.log`): Merkle positions
of `4s + 6` rows (p0) / `4s + 10` (p1) for `s` = 5, 6, 8, 10, 11 steps (126/132/145/178/290 of them),
aligned by S-E5's hint `size(4s + 9)` to 32/64; 126 Horner blocks of 383 rows aligned to 512.

- `strideBits n`: `r = size(n − 1)`; `r − 2` if `n ≤ 3·2^(r−2)`, else `r`. A block of `3u` rows at
  any `u`-aligned start is two aligned dyadic pieces (`2u + u` or `u + 2u`), so the plan's piece count
  per block is at most 2 whatever the start. `alignOf` uses it for the position (`4s + 10`) and the
  Horner block (383 → 7, stride 384). Control `strideBits_ctl` (`decide`).
- `cutSeg`/`cutBlock` (`FRVIRTplPlan`): a closed block `[r0, r1)` is cut from `r0` into pieces of
  `2^k` rows, `k` = min(the start's alignment, bits of the rows left), each over the block's cell
  window (so `blockRPC`'s abstraction and template matching are unchanged). Control `cutBlock_ctl`.
- **A block also closes at the next aligned op** (`segsGo`, `compMSX`): before, an open block was
  dropped when the next opened. This matters for A2′: its `posOpsG` ends in `shrN` (no `assertEq`),
  so every position block would stay open and the whole position region would go sparse.
- No proof changed: `compMSX_eq` is generic in the accumulator; `skelGo`'s proof takes any blocks.

Measured (`segdump-B1.log`, `laydump4-B1.log`, `nodedump4-B1.log`): skeleton 143,661 → **120,877**
(p0), 143,741 → **123,133** (p1); the regions **605,440 (p0) / 593,920 (p1)**; `inR true`; pieces
7,930 + 8,177 (keys 153); the sparse rows 40,064 + 36,660 → 17,280 + 15,929 (the empty padding rows,
filtered before evaluation, were most of them).

## 4. `FRNodeRows4Model` re-based (PACK-4.4.1 §6.1)

`protoRowsN = 605,440`, `protoRowsS = 593,920`; a slot's own region = prototype + pack map 212,344 +
cap check 40,000 + link region 32,768 (+ the segment's `R` 49,000); the previous-node slot's spare
region `R` 221,000 + `evalM` replay 400,000. `mRows4_le`: every region ≤ `2^20`, every kind ≤
`N_M/1.05`; `mRowModel4_eq` N2 3,367,616 / N4 5,223,680 / N8 7,424,256 (1.076× under N8's
`N_M/1.05`); `mRows4_neg`: with the pre-B0 prototypes the segment region is 1,059,997 > `2^20` and
N8 8,479,976 > `N_M/1.05`. Builds.

## 5. V: the evaluator (`ab*.log`, `piececost-*.log`)

The machine was at load 15–25 throughout (other tracks' builds and P2's prover), so every V figure
is an alternating A/B on core 30 (`logs/B0/ab3.sh`: per round, `plan4t init` wall then `plan4t`'s
9-rep best/median per kind, binaries in turn), and the base figures are ≈ 1.4× S-E12c's.

- `ab3-1` (4 rounds): base N4 min 116.1, A 121.1, A+B 128.6 ms. The levers cost ≈ +7–10 %.
- New probe `probe/PieceCost.lean` (`slotV3` of prototype 0 by piece class, 30 reps): the cost is
  per piece (≈ 1.5–2 µs, own inputs or not), i.e. the extra 1,500 / 1,770 pieces of the split tails
  and the cut blocks, plus `kp` for 45 more keys.
- **Split halves read only their inputs** (`FRVIRTplBuild`: `rowsInps`, `renRows`, `insOf`; KM
  fields `hdI`/`tlI`; `instLin_ren`, `ren_rows`; `tinRP_rows` through `ren_rows`; control
  `renRows_ctl`). Measured: no V change (`ab3-2`) — the tails had few own inputs anyway. Kept: it
  makes a half's key independent of the instance's other inputs.
- **`one·E(one)` once per key** (`FRVIRTplFast`: `ECtx3.ce`/`dce`, `ceOf`; `ppv3` reads it;
  `slotV3_eq` re-proved with a first `simp` pass for `getD_map'`): 3 of a piece's ≈ 11 field
  products. `piececost-B3b`: the 1,499 32-row pieces 3,194 → 2,024 µs, the 882 tensorW tails 1,296 →
  1,021 µs.
- `ab3-4` (6 rounds, base vs all of B0): N4 min 120.7 / 122.4 ms (+1.4 %), median 126.3 / 129.8;
  N2 117.2 / 119.2; N8 92.9 / 96.2; `plan4t init` min 2.2 / 2.3 s, median 2.4 / 2.4 s.
- `ab3-final` (8 rounds at load ≈ 3.5, base vs all splits): N4 min 116.1 / 120.1 (+3.4 %), N2 113.4 /
  117.8, N8 92.2 / 92.8; init 2.0 / 2.1 s. `piececost-B3b`: `tensorW 7`'s 882 tails are ≈ 1.0 ms per
  prototype — the largest single cost of the levers.

## 6. The split threshold `splitMin = 32` (`FRVIRTplExt`)

A split adds one piece per instance (≈ 1.5–2 µs); `tensorW 7`'s saves 28 rows an instance (64 → 36).
`splitN` now also requires `2^a + 2^b + splitMin ≤ 2^r` (≥ 32 rows saved per instance): `tensorW 7`
and `eqPt 18 18` (36 rows) are no longer split; `phiRS` (120), `tensorWK` 286 (224) and 151 (96), and
the one-instance keys stay split. Controls updated (`splitN 72 = (6, 3)`; `splitN 35 = none`).

- Rows (`laydump4-B4.log`, `nodedump4-B4.log`): **630,016 (p0, −100,477) / 618,496 (p1, −107,389)**;
  `inR true`; keys 142, pieces 7,042 + 7,287.
- `ab3-B4` (6 rounds, base / all splits / threshold): N4 min 115.4 / 119.8 / 116.9; N2 113.3 / 118.7 /
  114.7; N8 91.9 / 93.8 / 91.2.
- `ab3-B4b` (8 rounds, base / threshold, load 12–25): **N4 min 121.7 / 122.1, median 127.6 / 127.7;
  N2 118.4 / 118.3; N8 95.7 / 95.2; init min 2.2 / 2.2 s** — parity.
- The trade, for the orchestrator: `splitMin := 16` gives back `tensorW`'s split: −24.6 k rows per
  prototype (630,016 → 605,440 / 618,496 → 593,920, measured as `nodedump4-B1`) for ≈ +3 % `evalMT4`.
- `FRNodeRows4Model` re-based on 630,016 / 618,496: N8 7,620,864 (1.048× under `N_M/1.05`).

## 7. Final

- Dumps, plan form, KAT at the threshold layout (`nodedump4-run.log`, `planform4-run.log`,
  `planform-kat.log`: `KAT PASS`; README updated); axioms (29), source rule (364 files, 0);
  CPU-s alternating against `fr-build-SE14` (`cpu-final.log`, ≈ ±0).
- `plan4t check` on the final binary: equal for N2, N4, N8.
- Final build on HEAD `4d5700c` + B0: green (`build-FR-4.out`). RESULT written.
