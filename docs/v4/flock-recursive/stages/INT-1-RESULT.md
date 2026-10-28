# INT-1 RESULT: revision 3.12 across the tracks (2026-10-28)

The integration pass for revision 3.12 (BLUEPRINT §10, stage-review changes 17–18; S-0-RESULT's
"Revision 3.12 …, S-0's part"). The base is HEAD `a6a64fd` (S-0's 3.12 pass, S-H2 part 14, S-E4),
plus this pass's edits in the working tree. Nothing is committed.

**State: `lake build FR` is green** (2,317 jobs; `logs/INT-1/build-FR-2.log`). The build tree is
`logs/fr-build-INT1/`: HEAD's sources, with this pass's modules symlinked to the worktree
(`snap.sh`). After the last build, every `lean/*.lean` file in the tree is byte-identical to the
worktree. The one exception is the untracked `FRXBaryTop.lean`, S-H2f's work in progress, which
`FR` does not import. Every command ran under the 16G scope.

## Changes by module

| Module (owner) | Change | Code lines (loc.py, before → after) |
|---|---|---|
| `FRVIRFinalsSF` (S-F) | `finRS` with claim 5, `finE` (iii)–(iv), `finB′` without `κ′·v_E` | 467 → 499 |
| `FRVIRFinalsSG` (S-G) | `finPf` without `evalMK`; E's point in `rsWeight`; `lrHi` at the new `lBase` | 1,526 → 1,506 |
| `FRNodeLayout` (S-E) | `chainN` 23,225, `lBase` 47,616 (S-E4's new `mRowModel` kept) | 159 → 158 |
| `FRVIR`, `FRVIRCompile`, `FRVerifierImpl` | `evalMK` removed | 447 → 441, 863 → 862, 145 → 82 |
| `FRSoundness*` (S-G) | positions and phase indices moved; B′ truth without `v_E` | see below |
| `probe/fr-irdump/IRDump.lean`, `probe/fr-vtime/VTime.lean` | `walkAB` (IRDump was still at `walkA/B`), no `evalMK` | dev tools |

### `FRVIRFinalsSF`

- **`finRS`**, `J_z = 5`.
  - Claim 4 is E's `f̂(r′)`. Its inner weights are the packing basis, `wop i = .const (bb i)`
    (`rsW _ 4 i = bb i`). So `α₅ = Σ_i b_i s_{4,i}` and `T₄ = Σ_i b_i Φ(s_{4,i})`.
  - **`rsTail`** takes `t₄`:
    - it computes `T₃ + κ T₄`, then `keep isNode` against `0`, then Horner down to `T₀`;
    - a leaf's zero check covers claims 3 and 4: 4,096 bytes from `rsOff 3 0`, `rsLeafZero`.
  - Exports: `α_Z, α_Lc, α_Sh, α_Lr, α_E`, then `v_RS`; **`nRS = 5`**.
  - `rsV` is `T₀ + κ(T₁ + κ(T₂ + κ·[node](T₃ + κ T₄)))`.
  - **`exec_finRS` re-proved** (claims `j < 5`), and so is `run_rsTail`.
- **`finE`**, revision 3.12, built in the shape of `finLr`:
  - (ii) `c_{E2} = eq(r_E, r_{E2})·(â b̂ + ĉ)`;
  - (iii) `â + κ_E b̂ + κ_E² ĉ = claim0 "E4"`;
  - (iv) `(Ã + κ_E B̃ + κ_E² C̃)(r_{E2}, r′)·zhat[4] = claimN "E4"`, with `evalM (r_{E2}) (r′)` and
    `r′ = chals "E4" 23`;
  - each check is gated by `isNode`;
  - the export is the point `r′`.
  - **`relE`** now takes `impl` (for `evalM`). **`flag_finE` re-proved.**
- **`finB′`**: the `.mulF kp vE` and `.addF vRS …` ops are gone.
  - `v* = v_RS + [node] κ′²·pubH`.
  - The registers move by −2: the export is `b + 30`, the check `b + 32`.
  - `vStar` and `flag_finB'` read no `v_E`. **`flag_finB'` re-proved.**
- `noAsk_finRS` covers claim 4's const weights.

### `FRVIRFinalsSG`

- **`pfPts`** gains point 17, `eSrc fi = (chals fi "E4" 23).map .f`: E's outer point, all of `r′`.
  It is appended last, so indices 0–16 are unchanged.
- **`rsPtIx .N30 = [1, 3, 5, 6, 17]`**: the five claims, in `finRS`'s order, with weights `κ^0 … κ^4`.
  `rsPtIx` is unchanged for the leaf kinds.
  - The task said "keep the rest". The fifth weight is still needed: `v_RS` now contains `κ⁴T₄`.
    Without `W₄` in `Ŵ`, even an honest proof fails `finPf`. A.9 also says "`rsWeight` (5 claims)".
- **`finPf`** has no `evalMK`, no κ_E products and no `κ′·E` term:
  - `V4` is two registers, `r″` and `rsWeight`;
  - the `getK`/`1 + ρ` blocks are at `wb + 2`, `wb + 25`;
  - `cb = wb + 48`;
  - after the cells: `keep isNode (cellsAcc …) 0`, then `W₀ = rsWeight + that` (`lb = ce + 2`).
- `eV` is deleted; `w0V = rsWeight + [node] cellsVal`.
- `pfRefs` no longer reads `E3` or `finE`'s exports.
- **`flag_finPf` re-proved.** The changes are block B4 and the register arithmetic of B5–B13:
  17 → 18 points, and B9 rewritten for the two-op tail.
- `pfPts_length = 18`.
- **`lrHi_eq`** now holds the bits of `lBase/2 = 23,808`. This is the `decide` that S-E4 saw fail.
  It failed because the new `lBase` was in place before this line was updated.

### `FRNodeLayout`

- **`chainN` = 23,225.**
- With the new `chainN`, H ends at **47,480**, past the old L base 46,336. So **`lBase` = 47,616**:
  the first multiple of 256 after H, which was the alignment 46,336 had.
- `regions_fit` (`hEnd = 47,480`), `nodeLayout_*`, `usedBlocks_le` and `mRows_le` hold.
- **Not in the blueprint.** §4.3 and A.7 still say L is at 46,336. The orchestrator should ratify
  47,616, or pick another even base in `[47,480, 49,028]`. The constraints are:
  - `lrHi` needs `lBase` even;
  - the prover and P2 must use the same value.

### `evalMK` removed

- **`FRVIR`**: the op constructor, the `OpImpl` field, the `Meets` conjunct, the `evalOp` case
  and `Op.outs`.
- **`FRVIRCompile`**: the `opOut` arm and `Op.nOut`.
- **`FRVerifierImpl`**: the whole "K column point" section (`sparseEvalK`, `matMLEK`, `evalMKI/S`,
  `sparseK_eq`, `evalMK_meets`) and the record fields. `implCWith_meets` has one conjunct fewer.
- `FRVIRTplFast.evalMKT`/`evalMKT_eq` (S-E4's) are now unused but left in place. Deleting them
  is S-E4's/S-E5's call, and so is the axiom probe `probe/fr-e4kill/ax/AxE4.lean`, which prints
  them.

### Soundness modules (S-G)

- **Positions**:
  - `fsRanges_eq`: S-0's list;
  - `fsStarts_eq`: 52 starts, from `pos-3.12.txt`;
  - `capPos_eq` = `[2, 359, 398, 425, 449]`;
  - P1 starts `[347, 390, 417, 441, 463]` (`FRSoundnessHide`);
  - `pfStart_eq` = 483, `phOf_ge` 483;
  - `phOf_check`/`phOf_bounds` over 497;
  - `rounds_check` and `fsItems_length` = 497;
  - `phOf_examples`: `phOf 385 = 30`, `phOf 496 = 51`.
- **Phase indices** (the tail moved by +1):
  - `p1Start = phStart (26 + 5i)`, `cStart` 27 + 5i, `p3S0` 30 + 5i, `capPos` 22 + 5i,
    `pfStart = phStart 51`;
  - `finalAt`'s cap message is `phStart 47`;
  - `DT` is over `26 … 51`, with `DT_P1/C/P2/P3/Pf`;
  - `tail_ph_check`, `DT_stab` and `isQ` are over 29 … 49;
  - `phOf_start` is over 52 phases;
  - Compose: the front is `0 … 25` (`DkC`'s `k < 26`, `FrontObl.handoff` with `DF 25`, `hstab`),
    `front_check`/`front_facts`, `tailCls`/`tail_cls`. The lemmas `phOf_lt_25`/`phOf_ge_25` are
    renamed `phOf_lt_26`/`phOf_ge_26`.
  - Truths: `sAt`, `kcAt`, `posAt`.
- **`rounds_check`**: the task listed "gains E4". The tail's `rounds_check` (TailD) covers only
  P1.i and Pf, so it needed only the 451 → 497 change. There is no front list of degree-2 F rounds
  phases to add E4 to: `e2_phase` and `lr2_phase` are the only front `RoundsPhase` instances, and
  L2, S2 and Lr4 have none. **E4's `RoundsPhase` (`b = 300`, 23, `nodeOnly 23`) and its truths and
  dooms stay with S-G (E's front, parametric as allowed).**
- **`nodeKind`**: `streamTarget 1,486,400` (= 64 · 23,225; it was 1,437,760).
- **B′ truth without `v_E`**:
  - `truthB' κ L es cells κ′ vRS vStar` (its controls changed with it);
  - `w0F Wrs cells κ′`, `truthP1_zero` (no `hE`), `mleN_w0F`, `w0F_cell`.
  - `wE`, `sum_wE` and `mle_wE` (the E weight over the M rows) stay. They are now the algebra of
    `finE` (iv).

## Re-proved, and checks

- **Re-proved**:
  - `exec_finRS`, `run_rsTail`, `flag_finE`, `flag_finB'`, `flag_finPf`, `noAsk_finRS`;
  - `lrHi_eq`, `pfPts_length`;
  - `truthP1_zero`, `mleN_w0F`;
  - `implCWith_meets`;
  - every `decide +kernel` position check listed above.
- **Axioms** (`logs/INT-1/axioms.log`): `exec_finRS`, `flag_finE`, `flag_finB'`, `flag_finPf`,
  `truthP1_zero`, `mleN_w0F`, `phaseObl_of`, `kstate_of_front`, `implCWith_meets` and
  `regions_fit` use only `propext`, `Classical.choice` and `Quot.sound` (`lrHi_eq` only `propext`).
- **Source rule**: 107 files, 0 findings (before the `evalMK` removal; that removal only deletes
  lines).
- **Build times** (sequential runs, 16G scope, this VM, wall clock):
  - `FRVIRFinalsSF` alone: 18 s;
  - `FRVIRFinalsSG`: 65 s;
  - the soundness chain: 95 s;
  - `FR` after the `FRVIR` change: 3 min 22 s.
- **Re-dump**: `logs/INT-1/dump/`, made by `logs/fr-build-INT1/redump.sh` with the full finals
  (`IRDumpINT.lean`, a copy of the fixed `probe/fr-irdump/IRDump.lean`). Checksums are in
  `logs/INT-1/redump.log`.
  - ops 107,100 (S-0's dump with the pre-3.12 finals: 106,051), registers 53,468;
  - asks = items = 8,920, piSize 800,640, streamBytes 1,486,400, chainLen 23,225;
  - no `PENDING`;
  - `finE`'s `evalM` is at line 67,487 of `ops-N.txt`.

## Not done / for others

- **`evalM` with `κ_E`** (S-E4's suggestion: one value `Ã + κB̃ + κ²C̃`, two products saved per
  row): not adopted. It changes the op's signature (`FRVIR`, `OpImpl`/`Meets`, `evalOp`,
  `FRVIRCompile`'s imports, `FRVerifierImpl`) and, for the saving to be real, the per-row loop of
  `FRVIRTplFast`'s evaluator (S-E4/S-E5's module). That is not a small change in `finE` alone.
  `finE` calls the plain `evalM` and does the two `mulF`s, as `finLr` does with `evalL`. Suggested
  for S-E5 together with the templated evaluator.
- **Stale documentation in S-0's `FRVIRFinals`**: the `FinIn.zhat` docstring still lists
  `α₁ … α₅` as `ẑ_Z, Lc, ẑ_Sh,out, ẑ_Sh,in, ẑ_Lr`. Under 3.12 they are Z, Lc, Sh, Lr, E, then
  `v_RS` at `nRS = 5`.
- **Blueprint** (orchestrator):
  - L's base 47,616 (§4.3, A.7, A.6's Lr high coordinates);
  - A.9's `finB′` row still shows `κ′ v_E` (stage-review changes 18 withdrew it);
  - A.9's `finPf` row might name E's point (`r′`) as `rsWeight`'s fifth point.
- **Prover / P2**: `lBase` 47,616 (selector cells, L bit cells, the Lr claim's 15 high bits
  23,808); `finRS`'s fifth claim (packing-basis weights); `finPf`'s fifth `rsWeight` point `r′`;
  `v*` without `v_E`.
- **Nothing in `FR` fails.**
