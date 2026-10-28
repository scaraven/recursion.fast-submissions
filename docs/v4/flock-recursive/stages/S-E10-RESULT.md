# S-E10 (track L-circ): RESULT — part 1 (item (a) built and proved), handover for the rest

Stage S-E10, 2026-10-28, HEAD `5035389` (revision 3.15). Build tree `logs/fr-build-SE10` (a copy
of `fr-build-SE9`; `snap.sh` symlinks L-circ's modules, `FRBlake2sGeneric` and the new
`FRVIRTplDag`/`FRVIRTplWalk`; every other module is HEAD's). Logs in `logs/S-E10/`; journal
`S-E10-JOURNAL.md`. Every lean/lake/probe command ran in a capped scope (16 GB; 6–8 GB for
single-file probes) with a timeout. Nothing is committed. **I stopped for context after item 1**;
§6 is the handover.

## Status by item

| Item | State |
|---|---|
| 1. (a) the walk as the node's own XOR DAG | **Template built and proved; wired; laid out as 80 `G` blocks; V measured.** `dag_mle` not stated yet (§6). |
| 2. (b) `phiRS` split | not started |
| 3. (d) the evaluator's shift class | not started; **designed** (§6.1). It is now also the walk's fix. |
| 4. (e) `planOf` ≤ 0.2 s | **blocked as ruled** (§4): measured obstruction, a decision is needed |
| 5. `mRowModel`, re-dump | not started |

**Kill rules.** Rows: 526,205 per slot as built, ≈ 1.05 M per node, far under `2^21/1.05`.
**V: 287.13 ms best as built** (over the 251 ms line). The projection is under it only with item
(d): `evalM` is 169 ms of it, of which ≈ 40 ms is S-E9's `maskRows` defect and ≈ 26 ms the walk's
own inputs, both the per-chunk shift class (§6.1). I did not stop on V because the cause and the fix
are measured and are item (d); the orchestrator may decide otherwise.

## 1. What was built (code lines, core `loc.py`, HEAD → now)

| Module | Code | Change |
|---|---|---|
| `FRVIRTplDag` (new) | 140 | **The row-emitting gadget program.** Builder monad `DB` (state: gate position, gates, locals, rows, the two accumulator wires). XOR is a formal sum of single-wire forms (`dx`); a row is emitted where a form becomes a cell (`dcell`: carries, `sumW` outputs, `G`'s `b2`/`d2`, the IV copies `dcopy`, the final words); a product gate at position `k` emits `p_A ← rowW′[k]·a + p_A`, `p_B ← rowW′[k]·b + p_B` (`dmul`) and is `colW[k]`. Every `G` starts a fresh `2^gBits = 1024` block (`padTo`). `dwalkRun`, `tplWalkG n m` (irreducible). Controls. |
| `FRVIRTplWalk` (new; the S-E9 attic name) | 609 | **`tplWalkAB_ok`**: the gate equations at wires with inputs `rowW′ ++ colW` give `walkImpl rowW′ colW`. A relational simulation `RelT` against `walkOps`' run of `FRBlake2sGeneric`'s gadget program, gadget by gadget (`relT_mul`, `relT_addCarries`, `relT_majorities`, `relT_rippleCarries`, `relT_add3W`, `relT_addW`, `relT_gW`, `relT_roundW`, `relT_initW`, `relT_compressW`); growth `DGrows`; `emit_eqn` (an emitted gate is a gate of the final template); the accumulations `acc_forM`. |
| `FRVIRTplCore` | 189 → 195 | `Gate.pad r l`; `TKey.walkAB n m` |
| `FRVIRTplExt` | 362 → 395 | `tplWalk14` (closed), `tplWalkOf`, `tplWalkOf_eq`; `tplOf`, `tplExt`'s `walkAB` case; **`ImplT.walkAB`**; `tplExt_ok`'s case; `mkLay` aligns the walk to `2^gBits` (`isWalk`) |
| `FRVIRTplPlan` | 231 → 244 | `tinPP` cuts the walk instance into its blocks; `inputKinds (part := …)`, and `groupPPs` reads partition inputs as own when their joint labels fragment a group |

`FRBlake2sGeneric` is **unchanged** (deviation 1).

**Statements.** None changed: `implC_meets`, `acc_eq`, `node_m_sound`, `blake2s_chain`,
`leaf_sound`, `node_sound` build with HEAD's statements (`lake build FR`, 2,382 jobs).

## 2. The DAG (measured, `probe/DagCount.lean`)

| | per slot |
|---|---|
| XOR / copy rows | **25,312** |
| product rows (`2·14,720 + 2·256 + 2·896 + 2`) | **31,746** |
| rows with entries | 57,058 |
| **layout rows** (head block 1,024 + 80 `G` × 1,024 + tail 2,562) | **85,506** |
| a `G` block | 678 rows (310 XOR + 368 products), 560 own inputs |
| entries | 288,526 |
| generation (compiled) | 56 ms |

The blueprint's 90,851 assumed one row per XOR (≈ 6·10⁴). Measured, one row per XOR is 84,223 XOR
rows (168,706 layout rows at a 2^11 stride); folding XOR chains into one row each, and an operand
XOR into the product's form, gives 25,312.

## 3. V and `evalM` (N30)

| | best | median | log |
|---|---|---|---|
| V at HEAD (baseline) | 206.17 ms | 221.98 ms | `vtime-N-base.log` |
| V with the DAG | **287.13 ms** | 304.75 ms | `vtime-N-a1.log` |

`evalMT`: 101.6 ms (S-E9) → 306 ms (the walk in 64-row chunks) → 366 ms (`G` blocks, one key
each: the message-word partition) → **169 ms** (`G` blocks grouped, 88 keys). By key
(`e5eval-a3k.log`): the `G` key's 79 instances, 44,398 own inputs, ≈ 26 ms; `maskRows`' 241
chunks, 15,424 own inputs, ≈ 6 ms in this split (≈ 40 ms of S-E9's V, `e5eval-2`). An own input
costs ≈ 0.6 µs (three `F` products).

## 4. Item (e): `planOf` ≤ 0.2 s is not reachable as ruled

`planOf`'s parts, measured (`plant-0.log`, slot 0): `compileT` with the zero layout 853 ms,
`mkLay` 320 ms, `compileT` 667 ms, `slotIRows` 2,911 ms, `slotPPs` 4,615 ms, `groupPPs`
3,551 ms. With the DAG, `planOf` is 57.1 s (`e5eval-a3.log`).

The plan's correctness field `Plan.ok` is an equality: the pieces' rows **are** the compiled slots'
rows (`slotIRows (lay σ) … (cs σ)`), and `evalMS` (the spec of `evalM` that S-G's `truthE4` and
`node_m_sound`'s rows use) is the MLE of those compiled rows. Today `mkPlan` checks the equality
at run time (`eqL`), which needs the compile. From per-key literals the pieces are cheap, but
`Plan.ok` then needs a proof that the literals equal the compiler's output on the 105,837-op
program. Without kernel evaluation (forbidden, and far over the 600 s kernel budget) that is a
symbolic proof about `compileT` on the whole program. Laziness does not help (the ruling says so).
**One compile alone is 0.67–0.85 s per slot, so any run-time check is over 0.2 s.**

Options for the orchestrator:

1. **A rule change**: the plan check runs once per process within `verify_s` (today ≈ 13 s; ≈ 3 s
   with literal keys and pieces, one compile per slot, and an `eqL` on the instances only).
2. **A structural proof**: the compiler emits pieces directly (`compilePieces`) and a generic lemma
   shows that `flatMap Piece.rows (compilePieces …) = slotIRows …`. The keys and the layout come
   from literals; the compile still runs at process start, so this needs option 1's budget.
3. **The matrix defined by the plan**: M is the literal plan's rows. Soundness then needs "the plan's
   rows imply the compiled rows", which is the same obligation.

I see no route that satisfies both "≤ 0.2 s" and "no kernel evaluation" while M's spec stays the
compiled circuit.

## 5. Controls

| Definition | (+) | (−) |
|---|---|---|
| `tplWalkG` / `tplWalkAB_ok` | `tplWalkAB_ok`: hypotheses are only the inputs and the gate equations | `xor_row_neg`: an XOR row's equation fails at `loc 2 ≠ loc 0 + loc 1` |
| `dcell` | `dcell_emits`: a two-term form emits one gate | `dcell_free`: a single wire emits nothing |
| `Gate.pad` | `pad_rows`: `r` empty rows, `l` locals | (its `Eqn` is `True`; the rows are empty) |
| `isWalk` layout / `tinPP` blocks | measured: 79 `G` blocks give one template (`walkins-0.log`) | the first `G` differs (accumulators start at `0`); measured |

Checks: `lake build FR` green (2,382 jobs). Axioms (`axioms-a.log`, 36 names incl.
`tplWalkAB_ok`, `relT_compressW`, `acc_forM`, `tplWalkOf_eq`): only `propext`,
`Classical.choice`, `Quot.sound`. Source rule: 161 files, 0 findings (`source-rule-a.log`).
Sequential profiles (`profile-*.log`, one core, `Elab.async=false`): `FRVIRTplDag` 11.6 s wall,
0.22 s type checking, 2.09 s tactics; `FRVIRTplWalk` 19.8 s, 1.32 s, 7.24 s; `FRVIRTplExt`
10.2 s, 0.21 s, 1.57 s; `FRVIRTplPlan` 8.1 s, 0.06 s, 0.07 s.

## 6. Handover: the remaining items, in order

### 6.1 Item (d): the run class in the evaluator (do this first; it decides V)

- **Pad `G`'s output words to 32-aligned locals.** Use `padTo 5` before each `sumW` and before the
  two `dcellW`. `G` stays under 1,024 rows (678 + ≤ 192). Then every state-word own input is one
  run, or two for the rotated `b2`/`d2`, at a fixed offset inside an aligned 32-cell chunk.
- **A run class for own inputs.** Add `OwnP := g (GForm) | run (idx ch : ℕ)` in `PPc.ins`, and per
  key a pattern table `pats[k] : Array (j0 r len B)`.
  - A run is `len` consecutive own inputs with single-cell forms `[(ch·2^B + r + t, 1)]`, with
    `r + len ≤ 2^B`.
  - Its value is `hfac(B, ch) · inner[idx]`, where `inner[idx] = Σ_t U[j0+t]·eq(σ_{<B}, r+t)`. It
    is computed once per key per `evalM`. `j0` counts from the key's shared inputs.
  - Proof: `gN_split`/`eqN_split` (`FRVIRTplEval`) and `hfac_eq`; `ownSum_eq` extended to runs;
    `ppv_eq`/`ppv3`/`slotV3_eq` adapted. `prepPiece` takes the per-key pattern table, which is
    built at plan time from all instances. Correctness does not depend on the table's contents:
    a run is emitted only if the forms check.
- **Expected:** `maskRows`' 256 chunks share one pattern (`B = 6`, `r = 0`). The `G` key's runs:
  - the state words (≤ 8 runs, fixed offsets);
  - the message words (2);
  - `rowW′` and `colW` at the gate positions: 23 aligned 8-chunks each. `1280` and `184` are
    multiples of 8, if the bases of `maskRows` and `eqTable` are.

  That is ≈ 56 runs per instance, ≈ 4.4 k runs, **≈ 9 k products (the ≈ 13 k of `D̂`)**. Target:
  `evalM` ≈ 58 ms + the DAG's ≈ 3 ms. Measure V (21 warm runs).
- Optional: start the accumulators at a zero cell (two `dcopy []` rows), so that the first `G` is
  the 80th instance of the `G` key.

### 6.2 Item (b): the `phiRS` key split
`sq127` (128 rows) + `stage` (7) = 136 aligned instead of 256: −62,464 per slot. `tplPhiRS` is
in `FRVIRTemplates`/`FRVIRTplTab`; split it into two templates (two keys) with `tplPhiRS_ok`
restated as their composition. The statement in `ImplT.phiRS` is unchanged. Then measure V.

### 6.3 `dag_mle`
State it as the closed form of the walk instance's rows. It is the sum, over the instance's
blocks, of
- `tplR_mle`'s key part: `eq(τ_hi, X_i)·[eq(σ_hi, c_i)·Ĝ_loc + Ĝ_one·E(one)]`, with `Ĝ` the `G` key
  prepared once;
- the run terms of §6.1 (the `Wire` matrix);

plus the head, the first `G` and the tail. Prove it from `ppv_eq` over `tinPP`'s pieces of the
walk instance and the eqL-checked `Plan.ok`. It is the seam for `R`: `R` needs `D̂`, not the rows.

### 6.4 `mRowModel` and the dump
- `mRowModel` (`FRNodeLayout`): the changes-22 figures with the measured DAG (85,506 layout rows
  per slot; the blueprint's 90,851), `mRows_le`, `usedBlocks_le`.
- Re-dump with `probe/NodeDumpT.lean` to `logs/S-E10/nodedump/` with checksums and blocks.

### 6.5 Item (e)
It waits for the orchestrator's choice in §4. With option 1 or 2:
- literal per-key `Array`s for the keys, layout and pieces;
- `plan_wf` from their structure;
- a cold `verify` of one item, wall time.

Also cut `planOf`'s walk overhead (+44 s): `(tplOf k).rows`, `rbits`, `cbits` and `maxLoc` are
recomputed on every call for the 57 k-gate walk template. Cache them in the closed term.

### 6.6 Final checks
`lake build FR`, axioms (`ax/Ax.lean` has the new names), the source rule, sequential profiles, V
(21 runs), RESULT.

## 7. Deviations and open questions

1. **`GOps.xor` is unchanged; the row-emitting interpretation is a separate program
   (`FRVIRTplDag`) related to `GOps`' walk by a relational simulation.**
   - Making `GOps.xor` a state step would have put a `StateM` step on every XOR of V's own walk
     (`walkImpl`, 8.9 ms of V).
   - It would also have required re-proving `sim_compressW` and touching its three users
     (`FRBlake2sWalk`, `FRBlake2sWitness`, `FRVIREval`).
   - The template's correctness is still against the same generic program, gadget by gadget.
2. **XOR chains are one row each, and an operand XOR is folded into the product's form.** The
   rows are not single-cell: forms have up to 6 terms. Rows 57,058, layout 85,506 (the blueprint
   assumed ≈ 90,851). With one row per XOR they would be 115,969 and 168,706 at the 2^11 stride.
3. **`G` blocks at a 1,024 stride, through `Gate.pad`** (34 % padding inside a block). The blocks
   are found by `tinPP` and grouped by `groupPPs` (the search, untrusted): `Plan.ok` still checks
   the rows.
4. **`groupPPs` change.** Partition inputs whose joint labels cut a group into parts of fewer than 4
   members are read as own. This also regroups other keys: 88 keys now, 80 in S-E9.
5. **(e) blocked (§4).**
6. The first `G` block is its own key (accumulators start at `0`): §6.1's option.

**Edit requests**
- `FR.lean`: `import FRNodeMirror`, `import FRVIRTplDag`, `import FRVIRTplWalk`. The last two are in
  `FR`'s closure already, through `FRVIRTplExt`.
- **Blueprint.** §4.4 and A.11's walk row should give the measured DAG:
  - 25,312 XOR rows, 31,746 products, 85,506 layout rows per slot, `G` = 678 rows;
  - 1,024 stride.

  Also §4.4's "`GOps.xor` becomes row-emitting" should read "a row-emitting interpretation of the
  gadget program, `tplWalkAB_ok` by relational simulation". (e) needs the §4 decision.

## For P2

- **The walk's DAG cells** (template key `walkAB 16384 16384`, one instance per slot). The instance's
  local `k` is cell `cb + k` and its row `j` is `rowBase + j` (`groups-σ.txt` will list them after
  the re-dump). Every row has one new local:
  - **XOR / copy row** `⟨[], [], loc − Σ terms⟩`: `loc = Σ terms`, with terms the instance's locals
    or inputs. Input `i < 2^14` is `rowW′[i]` (the `maskRows` output element `i`); input
    `2^14 + j` is `colW[j]` (`eqTable` element `j`).
  - **Product row** `⟨rowW′[k], form, p − p_prev⟩`: `p = rowW′[k]·form + p_prev`. The first `A`/`B`
    product has `p_prev = 0`. The last two products' cells are the op's two outputs.
  - The value of `colW[k]` stands for gate `k`'s output: the walk's forms are linear in `colW`.
- **Blocks:**
  - head `[0, 1024)`: the IV copies (128 rows) and the counter XORs (128);
  - `G_i` at `1024·(1+i)`, `i < 80`, 678 rows then empty padding rows;
  - tail at `82,944`: the 256 final words, then the accumulations (`A`/`B` per output row, per input
    position, and the constant's), 2,562 rows.
- **The `phiRS` split's cell map:** not done yet (§6.2).
- **Dump format:** unchanged so far. The re-dump (§6.4) adds the `walkAB` group; its rows include
  the empty padding rows (alignment), as for every key.
