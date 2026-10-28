# INT-2 RESULT: revision 3.13 across the tracks (2026-10-28)

The integration pass for revision 3.13, items 1–2 of its block (BLUEPRINT §10, stage-review
changes 20): E before RS, Lr4 withdrawn, E4's lincheck carrying Lr's, `J_z = 4`. Item 3 (the
node's `targetS`/`linkW`) is another stage's and is untouched. This pass started at HEAD `9c1ee16`.
While it ran, the orchestrator committed S-H2 part 16, S-E5 and a queue update. HEAD is now
`8b539c3`. This pass's edits are in the working tree, and nothing of it is committed by me.
However, S-E5's commit `9dbab71` took this pass's `FRNodeLayout` edits (`chainN`, `hEnd`) along
with S-E5's own, so they are already in HEAD.

**State: `lake build FR` is green at HEAD `8b539c3` plus this pass** (2,320 jobs;
`logs/INT-2/build-FR-7.log`, the lake output in `build-FR-7-lake.log`). It was also green at
`9c1ee16` plus this pass (2,319 jobs, `build-FR-6.log`).
- The build tree is `logs/fr-build-INT2/`. `snap.sh` takes HEAD's sources and symlinks this pass's
  modules to the worktree.
- Five FRX modules in `FR`'s import closure carry transcript constants. In this tree they are
  **private patched copies** (`mkpriv.sh`, diff in `logs/INT-2/frx-patch.diff`). The worktree's
  FRX files are not touched (S-H2h is active). See §4.
- **In the worktree, `FR` fails only in those FRX modules**, until S-H2h applies the patch.
- After the last snapshot, every `lean/*.lean` file in the tree is byte-identical to the worktree,
  except the five patched FRX files. S-E5's committed modules (`FRVIRCompile`, `FRVIRMux`,
  `FRVIRTpl*`, `FRVIRTplPlan`) build unchanged with this pass.
- Every command ran under the 16G scope.

## 1. Counts (kernel-checked)

| | HEAD (3.12) | INT-2 | Blueprint 3.13 | Lemma |
|---|---|---|---|---|
| items | 8,920 | **8,891** | 8,891 | `items_length`, `queries_gen` |
| FS items | 497 | **468** | 468 | `fsItems_length`, `fsQ_gen`, TailO's `fsItems_length` |
| piSize | 800,640 | **797,904** | 797,888 | `piSize_eq`, `fieldSizes_eq` |
| hashed stream | 1,486,400 | **1,481,344 = 64 · 23,146** | 1,481,328 | `streamBytes_eq` |
| compressions per slot | 23,225 | **23,146** | 23,146 | `chainLen_eq`, `Layout.chainN` |
| RS claims `J_z` | 5 | **4** | 4 | `exec_finRS` (`j < 4`), `nRS = 4` |
| `rsWeight` points (node) | 5 | **4** | 4 | `rsPtIx .N30 = [1, 3, 5, 6]`, `pfPts_length = 17` |

The 16-byte difference in piSize is deviation 1 (§5).

## 2. Changes by module

Code lines are `loc.py`'s code column, HEAD → INT-2.

| Module (owner) | Change | Code lines |
|---|---|---|
| `FRTranscriptDefs` (S-0) | the phase table, the field numbers, the counts | 382 → 383 |
| `FRFormat` (S-0) | `fieldSizes_eq`, `piSize_eq` | 123 → 123 |
| `FRVIRSpec`, `FRVIRChain` (S-0) | `queries_gen` (8,891), `fsQ_gen` (468) | 1,285, 433 (unchanged) |
| `FRVIRFinals` (S-0) | `finLr` exports `v_L`, `r_Lr`; `exLr`, `lrEx`, `rest_exLr`; `relLr`, `vLv`, `flag_finLr` | 306 → 295 |
| `FRVIRFinalsSF` (S-F) | `finRS` back to 4 claims; `finE` (iii)–(v); `finE_evalL_point` | 499 → 510 |
| `FRVIRFinalsSG` (S-G) | `pfPts` (17 points, point 6 is `eSrc`), `rsPtIx`; `lrSrc`, `lrHi`, `lrHi_eq` deleted | 1,506 → 1,501 |
| `FRVerifierImpl` (S-F2) | documentation only. `evalL` already reads 23 cell coordinates; `finE` now gives it 23 | 82 → 82 |
| `FRNodeLayout` (S-E) | `chainN` 23,146, `regions_fit`'s `hEnd` 47,322 (`lBase` 47,616 kept); already in HEAD via `9dbab71` | 158 → 157 |
| `FRSoundness*` (S-G) | positions (§3), the defect lemmas (§2.4), `streamTarget 1481344` | ±0 to +3 per module |

### 2.1 S-0: the transcript

- **`piopPhases`**: `… Lr1, Lr2, Lrend, Lr3, E1, E2, Eend, E3, E4, E4end, RS0, RS1, B′`.
  - `Lr4` is removed.
  - `E4end` is `.absorb fE 32` (deviation 1).
  - `RS0` is `.absorb fRS0 (4 · 128 · 16)`.
  - There are still 26 PIOP phases, so the tail's phase indices (P1.0 = 26, …, Pf = 51) are
    unchanged.
- **Field numbers follow the item order**, as A.3 asks ("fields 9, 9′ precede field 8"):
  - `fE = 9`, `fEEnd = 10`, `fRS0 = 11`;
  - `fLr`, `fLrEnd` and fields 12–17 are unchanged.
- **`finLr`** (A.9, revision 3.13):
  - (i) holds by `initClaim`, and (ii) is checked;
  - (iii) **exports `[v_L, r_Lr]`**: `v_L = â_L + κ_L b̂_L + κ_L² ĉ_L` (`vLv`), and `r_Lr`, the
    register of Lr2's 15 challenges. That is the row point of `evalL`, as `r_{E2}` is `evalM`'s.
  - The Lr4 checks are gone.
  - A leaf's `v_L` is not `keep`-gated. `gen` asserts a leaf's Lr-end message to be zero, so its
    `v_L` is `0`, and every use in `finE` is node-gated.
  - `flag_finLr` states the flag (`relLr`: the end check) and both exports.
- **`FinIn.ex`**: `finE` reads `finLr`'s exports at `ex[exLr]` with `exLr = 4` (run order `finRS`,
  `finZ`, `finLc`, `finSh`, `finLr`). The control is `rest_exLr`. The IR dump uses the same
  mechanism (`IRDumpINT.dumpOps`).

### 2.2 S-F: `finRS`, `finE`

- **`finRS`** has `J_z = 4`:
  - claims Z, Lc, Sh, and E4's `f̂(r′)` with the packing-basis weights `bb i`;
  - the Lr inner-weight table is gone (registers `b … b + 6`, claims from `b + 7`);
  - `rsTail` computes `T₀ + κ(T₁ + κ(T₂ + κ·[node]T₃))`. It gains one `addF t₃ 0`, so that `keep`
    acts on a fresh register;
  - a leaf asserts claim 3's 2,048 slice bytes to be zero (`rsLeafZero`);
  - exports `α_Z, α_Lc, α_Sh, α_E`, then `v_RS` (`nRS = 4`);
  - **`exec_finRS` and `run_rsTail` are re-proved.**
- **`finE`**:
  - (ii) `c_{E2} = eq(r_E, r_{E2})·(â_M b̂_M + ĉ_M)`;
  - (iii) `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L`;
  - (iv) `c_{E4} = (W_M + κ_E³ W_L)·α₄`, with `W_M = (Ã_M + κ_E B̃_M + κ_E² C̃_M)(r_{E2}, r′)`
    (`evalM`) and `W_L = (Ã_L + κ_L B̃_L + κ_L² C̃_L)(r_Lr, r′)` (`evalL`). Both are evaluated at E4's
    23 challenges `r′`, and `α₄` is RS claim 4 (`zhat` 3);
  - **(v), every kind: E4 end's message is `α₄ ‖ 0^16`** (deviation 2);
  - (ii)–(iv) are node-gated.
  - **`flag_finE` is re-proved.** Its `relE` is written in the `&&` nesting of the op order.
  - `finB′` changes only through `nRS`.
- **`finE_evalL_point`** (positive control): op 19 packs `chals "E4" 23`, and op 25 is
  `.evalL (lrEx fi 1) (b + 17)` on that register (`opsOut` of the first 19 ops is 17).

### 2.3 S-G: `finPf`

- `pfPts` point 6, which was `lrSrc`, is now `eSrc` (all of E4's `r′`). Point 17 is removed, so
  there are 17 points again.
- `rsPtIx .N30 = [1, 3, 5, 6]`.
- **`flag_finPf` is re-proved.** The only change is 18 → 17 in `hlen`, `hPv`, `hkeep` and `hix`.
- `lrHi` (the provisional Lr point's high bits), `lrSrc` and `lrHi_eq` are deleted. Nothing else
  used them.

### 2.4 The S-G1j defect lemmas

- **`rs0_before_e4` no longer holds and is removed.** It is replaced by the control
  **`e4_before_rs0`**:
  - `piopPhases[21..24]` are E4, E4end, RS0, RS1;
  - `phStart` 265, 311, 312, 313;
  - `fsItems[310]` is a squeeze (E4's last challenge), `[311]` absorbs 32 B, `[312]` absorbs
    8,192 B, and `[313]` is a squeeze.
- **`evalL_short_zero` still holds and is kept** as the negative control. It is a fact about
  `evalL` at a point of ≤ 15 coordinates, not about `finLr`, and that is why `finE` passes 23
  coordinates. Its docstring and Part D's header say so. `finE_evalL_point` is its positive
  counterpart.
- **`lr_unit_pos`**: the last conjunct `fsItems[210] = absorb 48` (Lr4's first round) becomes
  `fsItems[210] = squeeze` (E1). Indices 0–11 of the conjunction are unchanged, so
  `lr_rejEnd_ok` still applies.
- The Lr/E unit instantiations stay parametric otherwise. In particular, the unit's three-claim
  batching is not yet the six-claim E4 batching. That is S-G's.

## 3. Positions moved in the soundness modules (S-G)

| Lemma (module) | HEAD | INT-2 |
|---|---|---|
| `fsRanges_eq` (Defs) | `…(169,8), (240,4), (244,11), (359,25), (384,5), (398,13), (411,5), (425,10), (435,5), (449,8), (457,5), (471,6), (477,5)` | `…(169,8), (209,11), (312,4), (330,25), (355,5), (369,13), (382,5), (396,10), (406,5), (420,8), (428,5), (442,6), (448,5)` (E1 now before RS1) |
| `fsStarts_eq` (StepA), from phase 17 | `210, 240, 241, 245, 256, 298, 299, 300, 346, 347, 359, 360, 385, 385, 390, 398, 399, 412, 412, 417, 425, 426, 436, 436, 441, 449, 450, 458, 458, 463, 471, 472, 478, 478, 483` | `210, 221, 263, 264, 265, 311, 312, 313, 317, 318, 330, 331, 356, 356, 361, 369, 370, 383, 383, 388, 396, 397, 407, 407, 412, 420, 421, 429, 429, 434, 442, 443, 449, 449, 454` |
| `capPos_eq` (StepA) | `[2, 359, 398, 425, 449]` | `[2, 330, 369, 396, 420]` |
| P1 starts (Hide) | `[347, 390, 417, 441, 463]` | `[318, 361, 388, 412, 434]` |
| `pfStart_eq` (Tail), `phOf_ge` (TailD) | 483 | 454 |
| `phOf_check`, `phOf_bounds`, `rounds_check` (TailD); `fsItems_length` (TailO) | 497 | 468 |
| `phOf_examples` (StepE) | `phOf 385 = 30`, `phOf 496 = 51` | `phOf 356 = 30`, `phOf 467 = 51` |
| `e2_phase` (StepB) | `RoundsPhase 256 21` | `RoundsPhase 221 21` |
| `nodeKind`, `nodeKind_*` (PIOP) | `streamTarget 1486400` | `streamTarget 1481344` |
| `ind_nodeBK` (Front) | `chainN = 23225` | `chainN = 23146` |
| `stream_padded` (Truths) | 1,486,400 = 64 · 23,225 | 1,481,344 = 64 · 23,146 (still holds, deviation 1) |

- **Unchanged**: phase indices (26 PIOP phases), Lr1–Lr3 (170–209), and `lr2_phase`.
- **E's unit, for S-G**: `s0 = 209` (Lr3's squeeze), E1 210–220, outer rounds from `b2 = 221`
  (`a = 21`), end absorb at 263, `κ_E` at 264, inner rounds from 265 (`nc = 23`), then E4 end at
  311, RS0 at 312, RS1 313–316, B′ at 317 and P1.0 at 318. The unit's precondition
  `s0 + 1 + ⌈a/2⌉ ≤ b2` holds: `209 + 1 + 11 = 221`.

## 4. For S-H2 (FRX offsets) and P2 (message order, A.3)

### 4.1 π layout (field index, byte offset, bytes)

| field | HEAD | INT-2 |
|---|---|---|
| hdr … S2 (0–6) | unchanged (0 … 5,647) | unchanged |
| Lr (Lr2's rounds only) | 7, 5,648, 1,440 | 7, 5,648, **720** |
| Lr end | 8, 7,088, 48 | 8, **6,368**, 48 |
| E: E2 (21 × 48) at +0, E4 (23 × 48) at +1,008, **E4 end `f̂(r′) ‖ 0^16` at +2,112** | 10, 17,376, 2,112 | **9, 6,416, 2,144** |
| E end | 11, 19,488, 48 | **10, 8,560**, 48 |
| RS0 (`4 × 128 × 16`, claim-major) | 9, 7,136, 10,240 | **11, 8,608, 8,192** |
| P1 | 12, 19,536 | 12, **16,800** |
| Pf | 13, 21,648 | 13, **18,912** |
| caps | 14, 22,320 | 14, **19,584** (level offsets 19,584 / 35,968 / 44,160 / 52,352 / 60,544) |
| final | 15, 67,376 | 15, **64,640** |
| columns | 16, 71,472 | 16, **68,736** |
| siblings | 17, 558,976 | 17, **556,240** |
| total | 800,640 | **797,904** |

Every offset from the Lr field on moves. The **body order is the item order**: E2's rounds,
E end, E4's rounds and E4 end come before RS0.

### 4.2 FS positions and items

| phase | HEAD (phase: FS positions) | INT-2 |
|---|---|---|
| Lr1, Lr2, Lrend, Lr3 | 13–16: 170–209 | same |
| Lr4 | 17: 210–239 | withdrawn |
| E1 | 20: 245–255 | 17: 210–220 |
| E2 | 21: 256–297 | 18: 221–262 |
| Eend | 22: 298 | 19: 263 |
| E3 | 23: 299 | 20: 264 |
| E4 | 24: 300–345 | 21: 265–310 |
| E4end | — | 22: 311 (absorb 32 B) |
| RS0 | 18: 240 | 23: 312 |
| RS1 | 19: 241–244 | 24: 313–316 |
| B′ | 25: 346 | 25: 317 |
| P1.0 … Pf | 26–51: from 347 | 26–51: from 318 (every position −29) |

- Item indices, queries included, move the same way: the queries come after P1.0, so every item
  from B′ on is at its HEAD index − 29.
- `items.json` in `logs/INT-2/dump/` has the order (0-based item index: `E4end` 311, `RS0`
  312).

### 4.3 What S-H2h's FRX needs

These are the constants of `logs/INT-2/frx-patch.diff`, 58 lines. With the patch applied in the
build tree, `FR` is green.

- `FRXChainFlock`: 497 → 468 (`fsMsgs_length`, `fsMsgs_items`), 800640 → 797904 (`msgOk`,
  `msgOk_of`, `tabW_chTab`), `fsMsgs_ctl`'s cap₀ offset 22320 → 19584, `nRep` 471 → 442, and
  `nRep_ctl`'s 463 → 434.
- `FRXLog`: `posL = 5 + 99738` (was `5 + 100080`); 800640 → 797904.
- `FRXLogSpec`, `FRXLookup`: 800640 → 797904.
- `FRXReadDefs`: 800640 → 797904; `capOff_eq` 19584; `capW0_eq` 2453; the 2790 in
  `tape_cap` → 2448.

Outside `FR`'s closure, these break the same way (not built here):

- `FRXLeaf:50`, `FRXSeed:135,144` (800640), and `FRXSeed:145` (100080 → 99738);
- `FRXReadLv:34,62` (`capOffL` 22320 … → 19584, 35968, 44160, 52352, 60544), `FRXReadLv:88,90`
  (67376 → 64640), and `FRXReadLv:103` (800640).

The extractor's ẑ claims are now 4 (stage-review changes 20, S-H2).

### 4.4 For P2 (the prover)

- Message order: E2, E end, E4 (the batched lincheck of `W_M + κ_E³ W_L` over the `2^23` cells),
  E4 end `f̂(r′) ‖ 0^16`, RS0 (4 claims; claim 3's slices are `f̂`'s, with the packing basis),
  RS1, B′.
- `κ_E` batches six claims (iii).
- `finPf`'s `rsWeight` takes 4 points; the fourth is `r′`.
- The stream counter of the last block is `t = 1,481,344`.
- `lBase` is 47,616.

## 5. Deviations

1. **E4 end absorbs 32 bytes, `f̂(r′) ‖ 0^16`, not the blueprint's 16. So piSize is 797,904, not
   797,888.**
   - With 16 bytes the hashed stream is 1,481,328 ≡ 48 (mod 64). The last compression of each
     chain would then have 16 padding bytes. `stream_padded` (S-G1e: "the node stream needs no
     padding claim") would be false, and `stream_sound`'s `Padded` hypothesis would need point
     claims on the padding cells.
   - The padding cells are budgeted in B′'s error row ("6 padding cells") and in A.7's
     public-cell list. But S-E3 removed them from `pubCells`/`pubVals`, and `pfCells` has none.
   - The 16 zero bytes keep the stream at `64 · 23,146` (the blueprint's compression count) and
     keep every downstream lemma valid. `finE` (v) asserts the zero half.
   - **Alternative, for the orchestrator**: keep 16 bytes and add one padding cell per slot (the
     last block's element 3) as a B′ point claim. That touches S-E3's `Node.pubCells`/`pubVals`,
     S-G's `pfCells`, `pfCells_eq`, `truthBN` and `stream_padded`, and the prover.
   - Switching back is two lines in S-0's modules (the table, `fieldSizes_eq`/`piSize_eq`), plus
     dropping (v)'s zero check.
2. **E4 end's value is bound.** A.9 names no binder for the E4-end message, and A.9's finE row
   counts four asserts. `finE` (iv) uses `α₄` from RS0's slices, as A.9 says. (v) asserts the
   absorbed value equal to `α₄` (and the zero half) for every kind, so the message is not a free
   field. For a leaf, `α₄ = 0` follows from `finRS`'s zero check.
3. `finLr`'s `r_Lr` export is **Lr2's final point**, the row point of `evalL`. A.9's notation
   `evalL(r_{Lr}, r′)` reads as Lr1's point, but the lincheck's row point is the zerocheck's final
   point, as `evalM(r_{E2}, ·)` is for E. HEAD's `finLr` already used Lr2's point.
4. **`FRNodeLayout` (S-E's) is edited.** `chainN` follows `chainLen`, and `regions_fit`'s `hEnd` is
   47,322. S-E5's commit `9dbab71` includes these lines. S-E5's new `mRowModel` (968,943 per
   slot) already drops `Φ`'s fifth claim. Its "templates still missing" row (118,639) still
   includes `rsWeight`'s claim 5 (11,400). That row is an upper bound, so `mRows_le` holds.
5. FRX is patched only in the build tree (§4.3), per the brief.

## 6. Checks

- **Axioms** (`logs/INT-2/axioms.log`, 32 theorems):
  - `propext`, `Classical.choice`, `Quot.sound` only, for: `exec_finRS`, `run_rsTail`,
    `flag_finLr`, `flag_finE`, `flag_finB'`, `flag_finPf`, `queries_gen`, `fsQ_gen`,
    `evalL_short_zero`, `e2_phase`, `ind_nodeBK`, `kstate_of_front`, `implCWith_meets`,
    `regions_fit` and `usedBlocks_le`;
  - `propext` only: `items_length`, `fsItems_length`, `streamBytes_eq`, `chainLen_eq`,
    `piSize_eq`, `rest_exLr`, `finE_evalL_point`, `pfPts_length`, `e4_before_rs0`,
    `lr_unit_pos`, `fsRanges_eq`, `fsStarts_eq`, `capPos_eq`, `pfStart_eq`, `phOf_check` and
    `rounds_check`;
  - `stream_padded` uses `propext` and `Quot.sound`.
- **Source rule**: `python3 -I .contract/scripts/source-rule.py submissions/flock-recursive`
  reports 115 files, 0 findings (on the worktree, other tracks' uncommitted files included).
- **No `decide` over a program or a layout.** The new checks are `decide +kernel` on the phase
  table and `fsItems` positions (as before). `finE_evalL_point` is `rfl` on `finE`'s 39-op list
  and a `simp` of its first 19 ops' widths.
- **Re-dump** with the full finals: `logs/INT-2/dump/`, made by `logs/fr-build-INT2/redump.sh`
  (`dump/IRDumpINT.lean`); checksums and the summary are in `logs/INT-2/redump.log`. It was re-run
  at HEAD `8b539c3`, with the same checksums as at `9c1ee16` (`redump-0.log`).
  - ops 105,828 (HEAD/INT-1: 107,100), registers 53,272 (53,468);
  - asks = items = 8,891;
  - fieldSizes as in §4.1; piSize 797,904, streamBytes 1,481,344, chainLen 23,146;
  - no `PENDING`.
  - `ops-N.txt`:
    - `finLr` at line 66,190;
    - `finE` at line 66,206, with `evalM r57515 r57528` at line 66,227 and
      `evalL r57501 r57528` at line 66,232, where `r57528` is E4's 23-coordinate point and
      `r57501` is Lr2's point;
    - E4 end's check is `piElem 9 2112`, `assertEq … r57374`, `piField 9 2128 16`,
      `assertZero`;
    - the node `rsWeight` takes 4 points (line 102,036).
- **Build times**: see §7.

## 7. Times

Wall clock, this VM, 16G scope.

- `lake build FR` after the S-0 change: 2 min 46 s (`build-FR-5.log`). Later runs took 4 min 13 s
  (`build-FR-6.log`) and, at HEAD `8b539c3`, 2 min 59 s (`build-FR-7.log`), while other agents
  shared the VM.
- Parallel build, per module (`build-FR-6-lake.log`): `FRVIRFinalsSG` 59 s, `FRVIRSpec` 33 s,
  `FRVIRFinals` 25 s, `FRTranscriptDefs` 16 s, `FRVIRFinalsSF` 15 s, `FRSoundnessFront` 14 s.
- Sequential profiles (one core, `taskset -c 0 lean -DElab.async=false --profile`;
  `logs/INT-2/profile-<module>.log`, `prof.sh`):

| Module | Wall (≈ 3.5 s import) | Type checking | Elaboration | Max RSS |
|---|---|---|---|---|
| `FRTranscriptDefs` | 20.6 s | 8.17 s (the `decide +kernel` counts) | 0.57 s | 2.88 GB |
| `FRVIRFinals` | 29.4 s | 1.44 s | 14.1 s | 2.69 GB |
| `FRVIRFinalsSF` | 24.8 s | 1.58 s | 2.21 s (simp 8.61 s) | 2.68 GB |
| `FRVIRFinalsSG` | 72.9 s | 4.54 s | 27.9 s | 3.34 GB |
| `FRSoundnessFront` | 19.4 s | 0.93 s | 5.84 s | 2.77 GB |

## 8. Open questions (orchestrator)

1. **Deviation 1**: ratify E4 end's `f̂(r′) ‖ 0^16`, with piSize 797,904 and the stream at
   `64 · 23,146`. The alternative is to keep 16 bytes and reinstate one padding cell per slot as a
   B′ point claim (S-E3, S-G, P2). A.3 row 9 and A.4 row 18′ need the chosen size.
2. **Deviation 2**: A.9's `finE` row should name E4 end's binder ((v): `e = α₄`, the zero half).
3. A.9's `finLr` row: `r_{Lr}` is Lr2's final point (deviation 3); A.9's `finB′` row still shows
   `κ′ v_E`.
4. A.3/A.4 field numbering: the Lean fields are now 9 = E, 10 = E end, 11 = RS0 (body order =
   item order). The blueprint's row labels (8, 9, 9′) may be kept as names.
5. `FRNodeLayout.mRowModel` (S-E): the missing-templates row still counts `rsWeight`'s fifth
   claim (11,400).
