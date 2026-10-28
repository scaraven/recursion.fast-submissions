# INT-3 RESULT: revision 3.14 in S-0, S-C, S-F, S-G; `FR.lean` complete (2026-10-28)

Started at HEAD `937e14d`; HEAD moved to `4e382bb` (S-H2 part 20) during the pass. Build tree
`logs/fr-build-INT3` (`snap.sh`: HEAD's sources, this pass's modules symlinked to the worktree).
Logs in `logs/INT-3/`. Journal: `INT-3-JOURNAL.md`. Every lean/lake command ran in the 16G scope
with a `timeout`. Nothing is committed.

**State: `lake build FR` is green at HEAD `4e382bb` plus this pass, 2,358 jobs**
(`logs/INT-3/build-FR-1.log`), with every new import (§5). At HEAD alone, the same targets were
green too (`build-head.log`, 2,352 jobs).

## 1. What changed, by module (code lines from `loc.py`, HEAD → INT-3)

| Module (owner) | Change | Code |
|---|---|---|
| `FRVIR` (S-0) | op `linkW τ fam r` → **`linkWAll (tt rr)`** (AF 8); new op **`shiftMask (tau r)`** (F × F × F); `OpImpl` fields `linkWAll : Kind → AF → AF → AF`, `shiftMask : AF → AF → F × F × F`; `Meets` conjuncts for both; `evalOp`; `Op.outs (shiftMask) = 3`; **`piDigest` runs `digestAt`** (S-E8 open item 1) | 580 → 586 |
| `FRVIRSpec` (S-0) | `digestAt_eq` in the `simp only` of `exec_merkleOps` and of `exec_genPhase`'s absorb case (proof repair) | 1,285 → 1,285 |
| `FRVIRFinals` (S-0) | **`finSh`** (§2), `linkOps` (8 × `getF` + weights `κ_s^{f+2}`), `bndOps` (a node's boundary is `0^4`), `linkSum`, **`relSh`**, **`flag_finSh`** (re-proved; `maxRecDepth 8192`); `h0Bytes`/`h0lo`/`h0hi` removed (no other user) | 295 → 308 |
| `FRVIRFinalsSF` (S-F) | `digestAt_eq` in `flag_finB'`'s `simp only`; **`relE_e4end`** (the E4-end binder, §4); `finB'` docstring (nine cells) | 510 → 521 |
| `FRShift` (S-C) | **the chain-masked form**: `ChainLinksM`, `chainDM`, `chainD0M`, `chainDM_join`, **`chainLinksM_iff`**, **`shift_sound_masked`**, `shWM` (the block weight with the interval factor), **`shift_sum_masked`** | 283 → 359 |
| `FRNodeTarget` (S-C) | **`fam`'s mirror sources set to A.6's pinned map** (§3); **`linkWAllS`**, **`shiftMaskS`** (specifications); `fam_bounds` repaired | 597 → 606 |
| `FRVerifierImplNode` (S-F2) | `ptA_extract`, **`linkWAll_eqS`** (from `linkWOne_eq`, as `linkWAll_meets`), **`shiftMaskI`** (two-level tables, `sepSum`), `tabs_a256`, `mask_eq`, `mask_succ_eq`, **`shiftMask_meets`** | 407 → 489 |
| `FRVerifierImpl` (S-F2) | `implCWith`/`specCWith`: `linkWAll` selected by `κ.isNode` (node `linkWAllI` on the packed points, leaf `0^8`), `shiftMask`; `implCWith_meets` gains both (with `targetSNode_meets` already there) | 87 → 95 |
| `FRSoundnessShift` (S-G, **new**) | `chainLk`, `ChainPartN`, `FamPartN`, **`ShHoldsN`**, `zNode`, **`truthS1N`**, `lkN`, `stN`, `outN`/`inN`, **`chainPartN_iff`**, **`shift_sound_node`**, **`sh_reads_chain_only`**, **`fam_blocks_ge`**, controls | 91 (9 theorems) |
| `FR.lean` | imports (§5) | 66 → 83 |
| `FRVIRCompile` (L-circ) | **minimal repair**: import cases `linkWAll → [.af 8]`, `shiftMask → [.f,.f,.f]`; `Op.nOut (shiftMask) = 3` | 779 → 781 |
| `FRVIRTplExt` (L-circ) | **minimal repair**: `.linkW`'s zero template, `ImplT.linkW` and its `case linkW` removed (the op no longer exists; a node's `linkWAll` is not 0, so it is an import like the node `targetS` until `tplLinkWAll`) | 337 → 330 |
| `FRVIRTemplates` (L-circ) | section title only | 206 → 206 |

## 2. `finSh` (A.9, revision 3.14)

After `bndOps` (7 registers), 61 registers `b … b + 60`:
- (i) `c₀ = shiftTarget κ_s τ θ bnd`; a node's `bnd = 0^4` (deviation 2);
- `E`, `Sh`, `E₀` are `keep κ.isNode` of the node's `shiftMask τ r_blk` (the chain-masked weights)
  and the leaf's `eqPt τ r_blk`, `shiftEq τ r_blk`, `eqPt 0 r_blk`;
- `w_out = E · slotW 0 θ r_pos`;
- `slotW_in = keep κ.isNode (slotW 2 …) (slotW 1 …)`: the node's `h_in` (base 0), the leaf's `d`
  (base 520) (deviation 1);
- `linkWAll (τ ‖ θ) (r_blk ‖ r_pos)` on the packed points (S1's 16 + 10, S2's 16 + 10), 8 `getF`,
  weights `κ_s^{f+2}`; a leaf's result is `0^8`;
- `w_in = (Sh + κ_s E₀)·slotW_in + Σ_f κ_s^{f+2} W_f`; (ii) `c_Sh = (w_out + w_in)·ẑ_Sh`.
- Exports `[w_out, w_in]` (`b + 16`, `b + 57`).

`relSh` states exactly this; `flag_finSh`'s statement form is unchanged (only its relation's
body is new).

## 3. The A.6 map check (S-CN's `wmB`/`mirB`/`mpos`)

`wmB σ = wmBase + 146σ`, `mirB = wmB σ + ⌊g/4⌋`, `mpos = 256·(g mod 4) + mbo + s` match A.6. **`fam`'s
mirror sources did not**: S-CN had `j` at 581, `end9` at 399, `end41` at 466; A.6 pins `x` 0,
`j` 399, `end9` 400, `end41` 467, `l` 533, `r0` 549, `r31` 565. `fam` now follows A.6 (sources
0 … 580). Sources, offsets, lengths and `mbo` were already A.8's. **P2's mirror writes must use
this map.**

## 4. S-G items

- **`truthS1N`** (= `ShHoldsN` on `zW`'s bits by block/position): the chain part (inside each chain
  `h_in(y+1) = h_out(y)`, and `h_in(0) = h_in(N)`) and the 8 families' source-equals-mirror bits.
- **`chainPartN_iff`**: the chain part is `ChainLinksM lkN stN h_out h_in 0`, so
  **`shift_sound_node`** (from `shift_sound_masked`) gives a nonzero masked residual when it fails.
- **`sh_reads_chain_only`**: the chain part depends only on blocks `< 2·chainN = 46,292`.
  **`fam_blocks_ge`**: every family source block is `≥ 2·chainN` and every mirror block
  `≥ wmBase`. Together: a `WM` block is read only at its mirror positions.
- **`truthB′` at `J_f = 9`**: already so in HEAD. `truthBN` is over `cellsOf` = `Node.pubCells`
  (`pfCells_eq`, `pfCells_spec`: length 9), and `finB'` has no `κ′ v_E` term (changes 18). No
  change.
- **E4-end binder**: no `truthE4` exists in S-G yet. The Rows unit's E4 instantiation is still
  S-G's next step. I added **`relE_e4end`** (`FRVIRFinalsSF`): an accepting `finE` binds E4 end's
  message to `α₄ ‖ 0^16` for every kind. `truthE4`'s end absorb should cite it.
- `finalLaw_of`, `hAcc_of`, `finalLaw_of_run`, `kstate_of_front`: untouched; they build unchanged.

## 5. `FR.lean`

New imports: `FRNodeTarget`, `FRVerifierImplNode`, `FRVIRTplRep`, `FRVIRCompileSound`,
`FRVIRTplPlan`, **`FRVIRTplControls`** (its controls are now checked by `lake build FR`; S-E8 open
item 3), `FRSoundnessShift`, `FRSoundnessLigFinal`, `FRSoundnessAccRun/Fin/Pos/Sem`,
`FRSoundnessAcc`, `FRNodeReadLayout`, `FRNodeRead`, `FRNodeReadW` (the coordinator's addition),
`FRXNodeRun`.
- Not imported: `FRSoundnessAccSeg` (still in progress); the untracked `FRSoundnessAcc{Col,Eq,Lvl,Pf,Qry,Val,W}` and
  `FRNodeRead{P,S}` (not in HEAD).
- Outside `FR`'s closure: S-H2's other `FRX*` modules (those `FRXNodeRun` does not import).

## 6. Checks

- **Axioms** (`logs/INT-3/axioms.log`, 27 names): `acc_eq`, `implC_meets`, `implCWith_meets`,
  `implCWith_implT`, `finalLaw_of_run`, `finalLaw_of`, `hAcc_of`, `kstate_of_front`,
  `shift_sound_masked`, `chainLinksM_iff`, `shift_sum_masked`, `sh_reads_chain_only`,
  `chainPartN_iff`, `shift_sound_node`, `fam_blocks_ge`, `shiftMask_meets`, `linkWAll_eqS`,
  `flag_finSh`, `flag_finB'`, `tplExt_ok`, `runSeq_runIR`, `fam_bounds`, `linkW_mle` and the
  controls. They use only `propext`, `Classical.choice` and `Quot.sound`; `relE_e4end` uses
  `propext`, `Quot.sound`; `shHoldsN_zero` uses none.
- **Source rule**: 141 files, 0 findings (`source-rule.log`; on the worktree, other tracks'
  uncommitted files included).
- **Controls** (`FRSoundnessShift`):
  - `shHoldsN_zero` (+): the zero table satisfies `ShHoldsN`;
  - `not_chainPartN_one` (−): one set bit in block 1's `h_in` breaks the link from block 0;
  - `chainPartN_ignores_wm` (+): a `WM` block's contents do not affect the chain part.

  `shiftMask_meets` and `linkWAll_eqS` have no hypotheses.
- **Sequential profiles** (`taskset` one core, `-DElab.async=false --profile`;
  `logs/INT-3/profile-<module>.log`, `prof.sh`):

| Module | wall | type checking | elaboration | max RSS |
|---|---|---|---|---|
| `FRVIR` | 18.5 s | 1.90 s | 7.04 s | 2.70 GB |
| `FRVIRSpec` | 54.4 s | 5.35 s | 5.31 s | 2.78 GB |
| `FRVIRFinals` | 32.9 s | 1.94 s | 15.8 s | 2.74 GB |
| `FRVIRFinalsSF` | 25.3 s | 1.55 s | 2.19 s | 2.69 GB |
| `FRVIRCompile` | 27.2 s | 1.02 s | 0.93 s | 2.70 GB |
| `FRVIRTplExt` | 9.9 s | 0.18 s | 0.36 s | 2.76 GB |
| `FRShift` | 15.5 s | 0.38 s | 1.05 s | 2.61 GB |
| `FRNodeTarget` | 20.0 s | 3.48 s | 0.54 s | 2.85 GB |
| `FRVerifierImplNode` | 14.4 s | 1.61 s | 0.47 s | 2.77 GB |
| `FRVerifierImpl` | 6.1 s | 0.01 s | 0.03 s | 2.73 GB |
| `FRSoundnessShift` | 7.1 s | 0.19 s | 0.08 s | 2.74 GB |

## 7. Re-dump and `V`

- **Re-dump** (`logs/INT-3/dump/`, `fr-build-INT3/redump.sh`, `dump/IRDumpINT.lean` printing
  `linkWAll`/`shiftMask`; `redump.log`):
  - ops 105,837 (INT-2: 105,828; +9 in `finSh`);
  - the skeleton's registers 53,272 (unchanged); the last register is `r97017` (INT-2: `r97006`;
    +11);
  - asks = items = **8,891 (unchanged)**, and **`items.json` is byte-identical to INT-2's**
    (sha256 `71b533a2…`);
  - **piSize 797,904 (unchanged)**, streamBytes 1,481,344, chainLen 23,146, fieldSizes unchanged;
  - no `PENDING`. In `ops-N.txt`, `shiftMask r57447 r57450` is at line 66,148 and
    `linkWAll r57470 r57471` at line 66,162.
- **V (N30)**, S-E8's method (`probe/VTime.lean`, `vt.sh`: one idle core, 21 warm `runSeq` runs):
  - **best 168.7 / 170.1 ms, median 173.9 / 182.3 ms** (`vtime-N-a.log`, `vtime-N-b.log`), against
    S-E8's 169.4 ms best;
  - per-op (`prof-N.log`): `linkWAll` 1.87 ms, `shiftMask` 0.48 ms, `slotW` ×3 1.43 ms (one more
    than before), `evalM` 57.6 ms;
  - the `digestAt` switch (≈ −5 ms, S-E8) offsets the new ops.

## 8. Deviations (for the orchestrator)

1. **`slotW_in` is kind-selected in `finSh`, not in `implC`.** `ImplT.slotW : ∀ κ, impl.slotW κ =
   slotWI` is L-circ's template statement (the `slotW` template is kind-free, and the node circuit
   compiles the mux program). A kind-dependent `implC.slotW` would make it false.
   - `finSh` therefore computes `slotW 1` and `slotW 2` and selects with `keep κ.isNode`. The
     semantics are A.8's, and no L-circ statement changes.
   - Cost: one extra `slotW`, ≈ 0.5 ms.
2. **The verifier's masked weights need a new op, `shiftMask`.** It is not in A.8's table.
   - The blueprint asks for "the verifier's `shW` gaining the interval factor", but `shiftEq`/`eqPt`
     are kind-free, templated ops.
   - `shiftMask τ r_blk` returns the node's `Σ_{y∈Lk} eq(τ,y)eq(r,y)`, `Σ_{y∈Lk} eq(τ,y)eq(r,y+1)`
     and `eq(r,0) + eq(r,N)`. `Lk` is the two chains' link blocks `c·N + k`, `k < N − 1`.
     Specification `shiftMaskS`; the computed form uses two-level tables, 0.48 ms.
   - It is an import in the compiled circuit (as `linkWAll`) until S-E templates it.
   - A.8 needs a row for it.
3. **The node's shift target is 0** (`bnd = 0^4`), and **the start term binds only
   `In(0) = In(N)`**. With both chains starting at `h0`, A.6's start term `κ_s(eq(0,·) +
   eq(chainBase_2,·))` has target `κ_s(h̃0 + h̃0) = 0` in characteristic two.
   - So the Sh identity checks that the two starts agree. It cannot bind them to `h0`.
   - That value comes from **`streamStart`'s `h0` pin** (a Z truth: `FRBlockKinds.streamStart`
     has `h0Pin = true`). There is no soundness gap, but the "endpoints" of
     `shift_sound_masked`/`ShHoldsN` are the starts' equality.
   - The chain ends are not in Sh. The WOTS rows read the last `h_out`, and `hashStmt` reads the
     statement.
   - The blueprint text (§4.2, changes 21) should say so.
4. **`fam`'s mirror map is changed to A.6's** (§3). S-CN's numbering differed for families 1–4.
5. `implC.linkWAll` calls `linkWAllI` on `extract`s of the packed registers. The meets lemma is
   `linkWAll_eqS` (built from `linkWOne_eq`, the core of `linkWAll_meets`), against `linkWAllS`,
   whose θ/`r_pos` are `tt[16 + l]`, `rr[16 + l]`.
6. **L-circ repairs** (op signature): `FRVIRCompile` (two import cases, `nOut`), `FRVIRTplExt`
   (`ImplT.linkW` and its case removed: **a statement change of a structure, forced by the op's
   removal**), `FRVIRTemplates` (a title).
7. **`truthE4` does not exist yet.** Its binder is delivered as `relE_e4end` (§4).

## 9. Open items

1. **P2** (prover):
   - `ir.rs` interprets `"linkW"` (`ir.rs:394`). It must handle `linkWAll` (a leaf: `0^8`) and
     `shiftMask` (3 F values; a leaf's are discarded by `keep`).
   - The mirror writes use §3's map; a node's Sh tables need the chain mask and the `h_in` In slot;
     the node's S2 initial claim is 0.
2. **S-E**:
   - `tplLinkWAll`, and a template for `shiftMask` (≈ 2 k rows), both imports now;
   - `FRNodeLayout`'s `wmSlot = 146`, `hEnd = 47,594` (still 10 and 47,322 in HEAD).
3. **S-G**:
   - the S1/S2 phase truths over `truthS1N`: `shift_sum_masked` with the node's `shWM` is the S2
     true sum. The bridge from `shiftMaskS`/`linkWAllS` (`eqAtR` form) to `mle`/`shWM` (`eq`/`cube`
     form) is still to write. `linkW_mle`/`linkInd_sum` cover the families;
   - `truthE4` citing `relE_e4end`.
4. **Controls for `shiftMaskS`/`linkWAllS` at concrete points.** `linkWS` has S-CN's
   (`linkW_hit`/`off`/`mir`). `shiftMaskS` has none: a kernel evaluation over 23,145 terms is too
   costly. A cube-point lemma (`Wo(cube y, cube y) = [y ∈ Lk]`) would be the cheap form.
5. **A.8/A.9**: rows for `linkWAll`'s packed form (as implemented) and `shiftMask`; `finSh`'s node
   `bnd = 0`.
