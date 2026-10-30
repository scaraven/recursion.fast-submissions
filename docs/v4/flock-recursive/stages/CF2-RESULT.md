# CF2 (continues CF): RESULT — the closed forms wired; `evalL` by a carry automaton; one walk per prototype

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `f041d03`). Build tree `logs/fr-build-CF2`
(HEAD snapshot + this track's modules linked, `mymods.txt`); 97d578b reference tree `logs/fr-build-CF2H`
(snapshot at `97d578b`, nothing linked). Logs `logs/CF2/`. Every lake/lean/probe in a 16 GB scope under
`timeout`. No sub-agents, nothing committed, no `sorry`. Journal: `CF2-JOURNAL.md`.

**Status: CF-RESULT §6 steps 1, 2, 4, 5 done; step 3 partly (the remaining V cost is there); step 6 done.**
Final build `lake build FR Solution FRSubmission4Fin vtime4 cf2p FRNodeRows4RepLCtrl FRNodeRows4RepCFCtrl
FRInitFuse` **green, 5,083 jobs** (`logs/CF2/final.log`), then `plan4t` (`final-plan4t.log`; the measured
binaries are from `s5c.log`, 5,086 jobs, before the two proof-only fixes of §4). `evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX`, `slots_val`, `hfit4`:
**textually unchanged** (checked against HEAD); `rvOf_get`, `tplEvL_ok`, `tplEvL_outs`: statements unchanged.

## 0. Summary of the measurements (core 29; alternating; best of N)

| | 97d578b | CF (`f041d03`) | CF2 final | target | log |
|---|---|---|---|---|---|
| plan init (`plan4t init`, user) | 20.34–20.38 s | 20.3–21.8 s | **9.38–10.88 s** | ≤ ~9 s | `init-final.log`, `init-s3.log` |
| plan init RSS | 2.02–2.03 GB | 2.06 GB | **0.90–0.94 GB** | ≲ 0.8 GB | idem |
| V(N4) own kind, best (2 rounds) | 1,916.8 / 2,032.5 ms | 1,886–1,954 ms | **854.0 / 856.4 ms** | ≤ ~0.7 s | `v-final.log`, `v-s4.log` |
| `evalMT4` N4, best | 1,841.6 / 1,899.0 ms | 1,843–1,879 ms | **749.7 / 755.5 ms** | | idem |

Load during the final A/B: `plan4t check` on core 31, the kernel profiles on core 26 and another agent's
`lean` were running (load ≈ 4–5); the A/B alternates the binaries, so each sees the same load. The three
init rounds' spread (9.38–10.88 s) is that load; the quieter earlier rounds of step 4 alone (`init-s4.log`)
gave 10.71–10.82 s against 21.0–21.4 s.

**V is not at target (0.85 s).** What remains per call (probe `cf2p`, `cf2p-call5.log`): the replay value
`rvOf` ≈ 330 ms (row blocks 15 + 70 ms; `rsWeight` closed form frame 75 ms, local 182 ms), the rest of
`evalMT4` ≈ 0.45–0.5 s (the pre-REPF parts plus FOLD2's ask rows). §5 lists what is left for `rsWeight`.

## 1. What was built, step by step

### Step 1 — wire `arBlk0`/`kopV` into `Plan4`/`rvOf` (`FRNodeRows4RepCFW`, new; `FRNodeRows4Plan`)

- **Import cycle** (found first): `FRNodeRows4RepCFP` imported `FRNodeRows4RepK`, which is downstream of
  `FRVerifierImplNode4F → FRNodeRows4Plan`, so the plan could not import CF's plan side. `gatesAtGo_eq`,
  `rowsTR_eq` (namespace `N4s`, statements unchanged) moved from `FRNodeRows4RepK` to `FRNodeRows4RepCFP`;
  CFP no longer imports RepK; RepK imports CFP.
- `kpLen` + **`kpLen_eq`** (an `rsWeight` op's row count from its preparation); `blkGo` (tail-recursive
  split of the blocks: the row blocks' rows at their indices, the prepared ops at their first rows); `spV`;
  **`blkGo_val`** / **`blk_val`** (the row blocks' value plus the ops' `kopV` is the rows' `rm`); `blkGo_len`;
  `wFA`/`wLA` (`wF`/`wL` by split tables, `_eq`); `wF_cb`/`wL_cb` (`kopV_eq`'s `hw`); `kpsV3`; `rowsVal_spF/L`;
  `arBlkN` (`arBlk0` with the prototype as argument).
- Plan: `Plan4.rgF/rgL` are the row blocks' grouped rows; new field `kps : List (ℕ × KP)`; `hrg` an
  existential over the blocks; `rvOf` adds the ops' closed form (frame: `wF`, locals `0`; local: `wL`,
  locals `eq(u, 2^16 + ·)`); **`rvOf_get`: statement unchanged**, new proof (`blk_val`, `spV_zipIdx`).
- Measured (`init-s1.log`, `v-s1.log`): init 26.0–26.4 s (rows still built for `repFitB 0`, the op also
  prepared), RSS 1.38 GB; V(N4) 3,044.8 ms (the unoptimised closed form: six `kopV` × three kinds).

### Step 2 — structural `RepFit` (`FRNodeRows4RepCFW`)

- `linCellOk`, `rowCellOk` (+`_iff`), `lRoom = 2^20 − 2^16`, `cb_cellOk`, `instLin_cellOk`,
  `instRow_cellOk`, `subsG_rows_loc` (substituted sub-templates read locals below their running count),
  `kSig_loc`, `kpFit`, **`kpFit_rows`** (a fitting prepared op's rows fit), `blkGo_sub`, `blkGo_mem`,
  `repFitS`, **`repFitS_spec`**: `repFitS (blkGo 0 bs [] []) = true → repFitB 0 (bs.flatMap RBlk.rows) = true`.
  Sound, incomplete; the fallback (`rp0`) stays.
- Plan: `inR` checks `repFitS q && repFitB 1 rl1`; `mkPlan4` no longer takes prototype 0's rows.

### Step 3 — speed (partly)

- **`SM.rep` let-binds its pattern** (`pat 0` once per call; the result closure no longer rebuilds it),
  `SM.bind` and `srcCh` let-bind (`FRVIRTplCF`, `FRNodeRows4RepCFRs`; definitionally equal, proofs
  unchanged): preparing the one `rsWeight` op (three kinds' `rsGS`, `prepS`, mux, copy) **0.38–0.42 s**
  (was ≈ 1.3 s per kind).
- `FRVIRTplCFF` (new): `tmG3` (three matrices, one pass; no products for a zero row), **`Rep.ctx3`**
  (each placeholder's forms evaluated once for both carries; per instance, forms that vanish skipped: the
  locals when `lam = 0` (flag `zl`), `one` and the inputs when they are `0` (flag `zi`)), `Rep.pass3`,
  `psVal3`; **`Rep.ctx3_eq`** (= `ctx`), `pass3_eq`, **`psVal3_eq`**; `evF` (`LinT.ev` by a fold, no
  product for a coefficient `1` or a zero wire), `mul1`, `mulZ` (+`_eq`).
- `FRNodeRows4RepCFW`: `subsV3` (each kind's inputs as an array slice: no `kSig`/`pullE` per wire),
  `kopV3` + **`kopV3_eq`**, `kpsV3F` + **`kpsV3F_eq`**; `rvOf` uses `kpsV3F`. KAT `kpsV3F = kpsV3` at the
  plan's op, both parts (`cf2p kat`: true, true).
- Not done (§5): the chain-read placeholders in closed form; frame and local in one pass.
- Measured after steps 2–3 (`init-s3.log`, `v-s3.log`): init 14.1–14.7 s, RSS 1.29 GB; V(N4) 1,515.3 ms.

### Step 4 — `evalL` by carry automata (`FRVIRTplRepLG`, new; `FRVIRTplRepLD`, `FRVIRTplRepL`)

- **`FRVIRTplRepLG`** (generic): `PF f L x` (per-bit factors over `L` bits, `0` from `2^L`), `PF_succ`,
  `eqF`/`gN_PF`, `sum_parity`; **`GS fa fb L n A B`** and **`GS_eq`**: `GS … = Σ_{j<n} PF fa L (A+j) ·
  PF fb L (B+j)` (split at the lowest bit, `j = 2j' + d`: two terms, each the bit's factors times the same
  sum one bit up). **`autoG`**: the recursion as gates, top bit first, states memoised per bit (`kids`,
  `dedup`; at most 8 per start and bit), four factor products and two products per state per bit;
  **`ok_autoG`**: each start state's form is its `GS` value.
- **`tplEvL ν a b`** rebuilt (`evGM`): four automata — `S_σ = Σ_j eq(rL, σ nJ + j)·eq(r4_lo, 299 + j)`,
  `E_σ = Σ_j eq(rL, σ nJ + j)`, `eq(r4_lo, oneCell mod 2^14)`, and `eq(r4_hi, hb + σ)`, `eq(r4_hi,
  oneCell / 2^14)` (`n = 1` starts); then `Q_σ`, `O`, `(Σ E_σ)·O`. C1b's four `eq` tables (16,384 + …
  entries) and its `E`/`F` stages (`2 · vslots · nJ` products) are gone. **`tplEvL_ok`: statement
  unchanged**, new proof (`qE_ev`, `PF_fE` (padded factors are `gN`), `eqAtR_gN`, `bt_eq`, `GS_eq`,
  `evalL4I_sums`); `tplEvL_outs` unchanged (`rfl`).
- Effect: prototype 0's row blocks 373,550 → **57,972 rows** (the `evalL` replay ≈ 3.9 k rows for the
  three kinds, was 319,507); `arBlkN 0` 2.84 → 1.50 s, grouping 1.25 → 0.24 s; per call `rgL` 450 → 70 ms,
  `rgF` 82 → 15 ms (`cf2p-init4.log`, `cf2p-call4.log`).
- Measured (`init-s4.log`, `v-s4.log`): init **10.71–10.82 s**, RSS **0.82 GB**; V(N4) **925.4 ms** (CF in
  the same run 1,954.5 ms).

### Step 5 — one walk per prototype (`FRInitFuse`, `FRNodeRows4Plan`)

- `FRInitFuse`: **`compMSXB`** (the compile `compMSX` and the replay-block trail `trailMB` in one walk) and
  **`compMSXB_eq`** (it is the pair, for every extension, generator, template, block maker, state).
- Plan: **`planDataB`** (both prototypes: compile, ask rows, replay blocks; prototype 1's replay rows as
  row blocks `spBlk`; the second walk starts from the first one's memo), `DataOk`, **`planDataB_eq`**
  (`planDataB.1 = planData4`, the ask rows, the blocks' rows); `planOf4D` takes the walk's result and
  `DataOk`; **`planData4` is `noncomputable`** (INIT: otherwise still built at start); `planOf4 :=
  planOf4D planDataB planDataB_eq`. The fallback thunks are unchanged.
- `splitE` partial application: not used on any computed path (the plan and `rvOf` use `loTab`/`splitAt`
  tables; `splitE_eq` only in proofs).
- Measured (`init-final.log`, same rounds): CF2 final 9.38–10.88 s vs step 4 alone 12.30–12.45 s under the
  same load (≈ −1.5 s); RSS 0.90–0.94 GB (+0.1 GB: `planOf4` is a closed constant, so the walk's result —
  ask rows and blocks — is kept; see §5).

### Step 6 — checks

- **MxKat PASS** (`logs/CF2/mxkat.log`): `evalMT4` (3 kinds) and `evalMX4` (8 supports) at 3 random points
  equal REPF's reference (each slot's replay rows as a plain sparse sum over `repIRowsWP`, i.e. the rows
  rebuilt from the fallback thunk, independent of `rvOf`'s blocks and closed forms): 33 × true.
- **`plan4t check`** (`logs/CF2/plan4t-check.log`; `evalMT4` vs the sparse sum over `nodeIRowsP`): **N2
  equal true** (sparse 242 s), **N4 equal true** (366 s), **N8 equal true** (503 s).
- KAT `kpsV3F = kpsV3` (both parts) (`cf2p-call5.log`).
- Axioms (`logs/fr-build-CF2/ax/AxCF2.lean`, `logs/CF2/axioms.log`): `kpLen_eq`, `blkGo_val`, `blk_val`,
  `kpFit_rows`, `repFitS_spec`, `kopV3_eq`, `kpsV3F_eq`, `Rep.ctx3_eq`, `psVal3_eq`, `GS_eq`, `ok_autoG`,
  `tplEvL_ok`, `compMSXB_eq`, `planDataB_eq`, `rvOf_get`, `evalMT4_eq`, `evalMX4_eq`, `kRS_ok` and the
  controls: all ⊆ {propext, Classical.choice, Quot.sound}.
- Source rule: `submissions/flock-recursive`, 477 files, **0 findings**. No `sorry`, `native_decide`.

## 2. Controls (`FRNodeRows4RepCFCtrl`, new)

| Definition | (+) | (−) |
|---|---|---|
| `linCellOk` | a frame cell | a cell between the frame and `repB` |
| `cb_cellOk` (via `repCellOk`) | the last local in `lRoom` | the first local past it |
| `kpFit` | a failed op whose rejecting row fits | the same row with a cell past the frame |
| `repFitS` | a row block that fits | the same with a cell past the frame |
| `GS` | two bits, `A = B = 0`: both `j` contribute | `A = 1`: the second index leaves the bits |

The evaluation equalities (`kopV3_eq`, `psVal3_eq`, `blk_val`, `tplEvL_ok`) are theorems over every input;
their run-time controls are the KATs above (MxKat, `plan4t check`, `cf2p kat`).

## 3. Statement changes

| Declaration | Change | Why |
|---|---|---|
| `Plan4` (structure) | `rgF/rgL` = the row blocks' grouped rows (were all replay rows'); new field `kps`; `hrg` an existential over the blocks | step 1 |
| `mkPlan4` | no `rl0`; `hrl` only prototype 1's; new `q`, `hq` (the split) | steps 1–2 |
| `Plan4.inR` (via `mkPlan4`) | `repFitS q` for `repFitB 0 rl0` | step 2 |
| `rvOf` (def) | adds `kpsV3F` (frame, local) | step 1/3 |
| `planOf4D` | takes `planDataB`'s result and `DataOk` (was `planData4`, `hd`) | step 5 |
| `planData4` | `noncomputable` (value unchanged) | step 5 |
| `planOf4` | `planOf4D planDataB planDataB_eq` | step 5 |
| `Tpl.tplEvL` (def) | the automata template (`evGM`) | step 4 |
| `Tpl.evCs/evT/evE/evN/EvCx/mkEvCx/evK2/evK3/evK4/evS2/tplEvLx`, `mkEvCx_k1/E`, `evE_ev` | removed (C1b's table template) | step 4 |
| `SM.bind`, `SM.rep`, `srcCh` (defs) | let-bound (definitionally equal) | step 3 |
| `N4s.gatesAtGo_eq`, `N4s.rowsTR_eq` | moved `FRNodeRows4RepK` → `FRNodeRows4RepCFP` (statements unchanged) | import cycle |
| `linE_filt`, `linE_filtL` (CF) | `[]` case by `simp` (was `rfl`) | kernel time, §4 |

`rvOf_get`, `tplEvL_ok`, `tplEvL_outs`, `kRS_ok`, every `RepOk`/`Gaps4`/certificate statement,
`evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX`, `slots_val`, `hfit4`: **unchanged**. `cb_ctl`
(`FRNodeRows4RepLCtrl`) still holds as stated; its `319507` (C1b's `evalL` locals) is now far above the
automata's size (an upper bound, not a measurement any more).

## 4. Kernel CPU per module (`lean -DElab.async=false --profile`, one core; `logs/CF2/prof-summary.txt`)

| Module | wall | kernel (type checking) | tactics |
|---|---|---|---|
| `FRVIRTplCF` | 17.9 s | 0.38 s | 1.5 s |
| `FRVIRTplCFE` | 10.1 s | 0.10 s | 0.48 s |
| `FRVIRTplCFF` (new) | 10.1 s | 0.08 s | 0.50 s |
| `FRNodeRows4RepCFRs` | 17.0 s | 0.86 s | 2.6 s |
| `FRNodeRows4RepCFP` (CF's; before → after the fix) | 96.6 → 9.7 s | **84.3 → 0.24 s** | 0.98 → 0.63 s |
| `FRNodeRows4RepCFW` (new) | 13.5 s | 0.28 s | 1.2 s |
| `FRNodeRows4RepCFCtrl` (new) | 8.1 s | 0.01 s | 0.02 s |
| `FRVIRTplRepLG` (new) | 10.3 s | 0.67 s | 0.61 s |
| `FRVIRTplRepLD` | 7.5 s | 0.00 s | — |
| `FRVIRTplRepL` (first version → final) | 91.9 → 57.1 s | 0.23 s | 79.9 → 44.4 s |
| `FRInitFuse` | 16.6 s | 0.41 s | 3.5 s |
| `FRNodeRows4Plan` | 22.9 s | 1.2 s | 5.1 s |

`FRVIRTplRepL`'s tactic time: 79 s were the final `exact` unifying the template's gates (now two `rfl`
rewrites); the remaining 43 s are one `refine` in `tplEvL_ok` (not isolated; build time only, kernel 0.2 s).

## 5. Remaining (handover)

1. **V (0.85 s, target ≈ 0.7 s).** Per call (`cf2p-brk2.log`): `rsWeight`'s closed form ≈ 260 ms over
   the three kinds and both parts: the blocks-once irregular rows (11–13 k per kind) ≈ 19 ms per kind and
   part; the stage groups' placeholder sums (local part: A ≈ 20 ms, B ≈ 28 ms per kind). Next, in order:
   (a) **the chain-read placeholders in closed form** (CF §6 step 3: a chain group's outputs read by the
   stage groups are locals at `K_ch + i·2^8 + o(s, δ)`; split at bit 8, `Σ_κ eq_hi(⌊H/2^8⌋ + i + κ)·
   V(c, δ, κ)` with `V` shared by all chains: `O(#placeholders)` instead of `128 · #placeholders`);
   (b) **frame and local in one pass** over the irregular rows (each term belongs to one part); (c) the
   rest of `evalMT4` (≈ 0.45–0.5 s, pre-REPF parts and FOLD2's ask rows) is outside this track.
2. **Init (9.4–10.9 s, target ≈ 9 s) and RSS (0.90–0.94 GB, target ≲ 0.8 GB).** The fused walk's result is
   kept by the closed constant `planOf4`: return the plan's grouped data from `planDataB` instead of the
   blocks (or pass the walk through a function of `d` as before) to drop ≈ 0.1 GB. The remaining start-up
   is the pre-REPF plan (≈ 6 s) plus the two walks with their ask/replay rows and the op's preparation
   (0.4 s).
3. `linE_filt`/`linE_filtL` (CF's, `FRNodeRows4RepCFP`): the profile run showed 41–43 s of kernel type
   checking each (and a heartbeat timeout under `-DElab.async=false`); their `[]` cases now use `simp`
   (was `rfl`, an instance-path defeq on `F`'s `0`): **84.3 s → 0.24 s** kernel for the module, no
   timeout (`prof-CFP2.txt`). Done here, listed because it is CF's code.

## 6. Files (absolute paths under `/home/devops/Verified-zkEVM/recursion.fast-submissions-rev44/submissions/flock-recursive/lean/`)

New: `FRNodeRows4RepCFW.lean`, `FRVIRTplCFF.lean`, `FRVIRTplRepLG.lean`, `FRNodeRows4RepCFCtrl.lean`.
Edited: `FRNodeRows4Plan.lean`, `FRInitFuse.lean`, `FRNodeRows4RepCFP.lean`, `FRNodeRows4RepCFRs.lean`,
`FRNodeRows4RepK.lean`, `FRVIRTplCF.lean`, `FRVIRTplRepL.lean`, `FRVIRTplRepLD.lean`.
Docs: `docs/v4/flock-recursive/stages/CF2-RESULT.md`, `CF2-JOURNAL.md`.
Build tree only: `logs/fr-build-CF2/probe/CF2P.lean` (probe `cf2p`), `logs/fr-build-CF2/ax/AxCF2.lean`.

Code lines (core's `scripts/loc.py`; code / theorems): `FRNodeRows4RepCFW` 348 / 32, `FRVIRTplCFF` 155 / 12,
`FRVIRTplRepLG` 131 / 11, `FRNodeRows4RepCFCtrl` 22 / 5; `FRNodeRows4Plan` 1,188 → 1,239, `FRInitFuse`
50 → 94, `FRVIRTplRepL` 122 → 182, `FRVIRTplRepLD` 47 → 27, `FRNodeRows4RepCFP` 266 → 275,
`FRNodeRows4RepK` 288 → 282, `FRVIRTplCF` 412 → 415, `FRNodeRows4RepCFRs` 458 → 460.
