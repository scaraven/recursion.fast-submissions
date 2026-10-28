# S-E12a RESULT: the revision 4.1 node circuit's specification (N2/N4/N8, 1 + k slots)

Base: HEAD `4acc3b3`. Build tree `logs/fr-build-SE12a` (from `fr-build-SG13`, `logs/org20`; `MINE.txt`
= the three modules below). Logs: `logs/S-E12a/`. Every `lake`/`lean` command ran in the 16G scope
under `timeout`. No sub-agents. Nothing committed. Namespace `FR.N4c` (grepped: no clash).

**Status: items 1–4 done; `DigLemma4` (the H side's chain fact) is proved as well.** The interface to
S-E12b (`SlotIface4`, `NodeResid4`'s item names) is fixed in the JOURNAL §0.

**Checks:**
- `lake build FR FRNodeKinds4 FRNodeCircuit4 FRNodeCircuit4Dig`: green, 2,466 jobs
  (`logs/S-E12a/build-final.log`).
- **Axioms** (`axioms.log`, 161 declarations): all within `propext`, `Classical.choice`,
  `Quot.sound`; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 249
  files, 0 findings (`source-rule.log`).
- **Imports for `FR.lean`:** add `import FRNodeCircuit4Dig` (it pulls `FRNodeCircuit4` and
  `FRNodeKinds4`).

## 1. What was built (code lines from `loc.py`, `logs/S-E12a/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeKinds4` | 617 / 393 / 45 | Literal constants with fidelity (`segB_eq`, `cLen_eq`, `aggL_eq`, `hUsedN_eq`); `TIv` (interval with kind and per-block targets); **`nodeLayout4 κ`**; `contig`, `ivAt`; **`nodeBK4`**, **`nodeKind4`**, **`Ind4`**, **`Sel4`**, `kindIvs4`; the certificate **`layout_contig`** (+ `layout_no_chain`, `layout_length`); generic tiling lemmas (`contig_bounds`, `contig_cover`, `contig_unique`, `ivAt_spec`); `layout_at`, **`ind4_iff`**, **`sel4_true`**, **`nodeBK4_ne_chain`**, `ind4_kindIvs`; `KindTgt`, `layout_tgtOk`, **`nodeKind4_kind`**, **`nodeKind4_none_iff`**; `bk_of_mem`, `tgt_of_mem`; `hEnd_le`, `ctr_final`, `aggL_nBlocks`; **`indN4`**, **`etN4`**, **`kf4`** (`indN4_chain`, `indN4_eq`, **`kf4_eq`**); **`cells4`**, **`hcells4`**; **`chainLk4`** (`chainLk4_stream`); `nodeBK4_wots`; `srcB4`, `mirB4`, `mir4_fits`; controls |
| `FRNodeCircuit4` | 501 / 300 / 24 | `zW4`, `zB4`, `zN4`, `bitsB4`; `finBlk`, `blkOf`, `chainW4`, `chainBytes4`, **`hDig4`**; **`AggPad4`**; **`truthZ4`**, **`truthS4`**, **`PubCells4`**, **`StmtN4`**; **`SlotIface4`**, **`Read4`**, `kA`, `sub`, `Active4`, `slotIn`; **`NodeResid4`**; **`DigLemma4`**; `sig_of`, `agg_acc`, `prev_acc`, **`node_sound4`**; **`nodeSoundLog4_of`**, **`nodeExtLog4_of`**, **`nodeLaws4C`**; `zlm4_indKinds`, `indN4_etN4_bits`, `hcells4P4b`; **`HFit4`**, **`rowsFitI_of_sorted`**, `hfit4_of`; controls |
| `FRNodeCircuit4Dig` | 312 / 249 / 16 | **`chain_digest`** (`Stream.stream_sound` with per-block compressions), `lift_bitsB4`, `holds_of_Z`, `readByte_zero`, `main_tgt`, **`fin_tgt`**, `stream_shape`, **`digLemma4`**; **`node_sound4'`**, **`nodeLaws4C'`** (without the chain hypothesis) |
| **total** | 1,430 / 942 / 85 | |

### Item 1: the block-kind map

The interval list is the source of truth. `nodeLayout4 κ` lists, in address order:
- the signed children's main chains;
- `hashStmt` (A, B1, B2) per verifier slot;
- WOTS per signed child (3.x's `Layout.wotsIvs 0` rebased, 3.x's `NodeT.wotsTgt`);
- `WM` and the spares (`free`);
- **the tail**: per aggregate, `maxK − 1` candidate final blocks and `c_A`'s `hashA` block;
- `free` to the end.

Each interval carries its blocks' targets (`TIv.tgt`). One `decide` per kind, on the 89/97/110
interval endpoints only (`layout_contig`), gives every per-block fact through the generic tiling
lemmas. No evaluation over blocks.

**Layout figures** (`hEnd_eq`): H ends at `N2` 70,957, `N4` 117,593, `N8` 187,548. All are
`≤ lBase` (`hEnd_le`).

**Per-kind facts for the weights:**

| Weight | Facts |
|---|---|
| RS | `kf4_eq`: the kind factor is `β^(index of the block's kind in nodeKinds)` |
| Z | `ind4_iff` (indicators = `nodeBK4`'s class), `nodeKind4_kind` (a target is of its kind's form, so `kindPins` applies), `nodeKind4_none_iff`, `zlm4_indKinds`, `indN4_etN4_bits` |
| S | `chainLk4`, `chainLk4_stream` (a masked block's successor is `stream`: its `h_in` is unpinned) |
| links | `nodeBK4_wots` (the WOTS order is 3.x's), `srcB4`/`mirB4`, `mir4_fits` (mirrors in a `free` `WM` interval) |
| B′ | `hcells4`/`hcells4P4b` (P4b's `hcells`: nine distinct cells inside `f`) |

### Item 2: the node relation

`StmtN4 κ lr er vk c₁ c₂ w` is the conjunction of:
- `truthZ4`;
- `truthS4`;
- the L rows;
- `truthEI er` (P4b's indexed form);
- `PubCells4`.

`NodeResid4 I rd κ vk c₁ c₂ w` has one field per item (JOURNAL §0):

| Group | Fields |
|---|---|
| per slot | `imp`, `rep`, `tpl` |
| selectors | `selP`, `slotP`, `selA` |
| pack map | `pack`, `chainMsg`, `aggFmt`, `aggTr` |
| aggregate checks | `aggChk` (`V_A`'s checks against `c_A`) |
| R-4-m2 | `kOk` (`childOk4`), `aggPad` (the `k`-gated final block) |
| signature | `wots` (the `k`-mux and WOTS on the H digest) |

`SlotIface4` is S-E12b's side:
- the node kind's L and indexed M rows;
- per slot, `imp`/`rep`/`tpl` and the selectors;
- `soundN`/`soundS`: the rows, the selector, `imp`, `rep` and `tpl` together imply that the slot's
  program accepts its input on its trace (`runSeq`).

### Item 3: `node_sound4` and the laws

**`node_sound4`** (and `node_sound4'` without `DigLemma4`):

```lean
theorem node_sound4' (hS : StmtN4 κ (I.lrows κ) (I.irows κ) vk c₁ c₂ w) (hR : NodeResid4 I rd κ vk c₁ c₂ w) :
    Rel (accV4 Vseg Vnode vk) (nodeStmt c₁ c₂) (.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w)) ∧
      ∀ σ < 2, childOk4 κ (rd.sgn κ σ w).π = true
```

How each child is accepted:
- **The aggregate child**: `V4_agg`, then `VA_complete` from `aggFmt`/`aggChk`. Every active
  sub-slot runs `soundS` with `selA`/`imp`/`rep`/`tpl`, on `tr_A = flatten` (`aggTr`).
- **The previous node**: `V4_node` at the kind `selP` selects, then `soundN`.
- **Both children**: `accWith4`'s format (`pack`) and the signature `SigOk vk (traceDigest tr)`,
  from `wots` and `digLemma4`.

**`digLemma4`** (proved, the H side). On `truthZ4`/`truthS4`, a chain whose stream (`chainBytes4`)
is `0x54 ‖ traceBytes tr` carries `traceDigest tr` at its final block's `h_out`. For an aggregate it
needs `1 ≤ k ≤ maxK` and `AggPad4`.
- Block 0 is `streamStart` (`h_in = h0`).
- The main blocks use the full chain's counters, which equal the stream's below the last block
  (`ctr_mid`).
- The final block has exactly `streamTarget L (N − 1)` (`fin_tgt`).
- The links are `chainLk4`, plus `AggPad4`'s `h_in` link.
- The padding is `AggPad4`'s zeros.

**The laws in `FRSoundness4Frame`'s form:**
- `nodeSoundLog4_of` gives `NodeSoundLog Vnode vk Good (Rel (accV4 …))`.
- `nodeExtLog4_of` gives `NodeExtLog` for an extractor given as a parameter: S-H3's `FRX4*` modules
  are not committed (`git log`), so its interface is the hypothesis `hE`.
- `nodeLaws4C'` gives both at `VC4` (`acc_eqC4`), with `E4 S.acc` through `nodeExt_E4`. These are
  `ks4_E4`/`ks4_of`'s `hN` exactly.

They take two hypotheses:
- `hRun`: the PIOP's per-run truths. An accepted node run on a good log carries `vk`, and
  `StmtN4` holds for some `w` with `c = nodeStmt c₁ c₂`. This is X4's (the doom chain at `seq4`).
- `hRes`: `StmtN4 → NodeResid4`. This is S-E12b's.

### Item 4: `hfit4`

S-E12b has not delivered its rows, so `HFit4 irows := ∀ κ, RowsFitI (irows κ) (e2R κ) (ncR κ)` is
parametric. **`rowsFitI_of_sorted`**/**`hfit4_of`** give P4b's distinct-index condition (F1) from
strictly increasing indices, which is the generator's certificate (no `decide` on the list).

## 2. Times (sequential, `--threads=1 -DElab.async=false --profile`; `logs/S-E12a/prof-*.log`)

| Module | wall | type checking | simp | tactics | peak RSS |
|---|---|---|---|---|---|
| `FRNodeKinds4` | 19.6 s | 2.58 s | 4.79 s | 2.65 s | 2.86 GB |
| `FRNodeCircuit4` | 10.1 s | 0.24 s | 0.44 s | 1.37 s | 2.91 GB |
| `FRNodeCircuit4Dig` | 9.9 s | 1.02 s | 0.27 s | 0.80 s | 2.92 GB |

Imports account for about 4 s of each.

## 3. Controls

| Definition | Positive | Negative |
|---|---|---|
| `nodeLayout4`/`contig` | `layout_contig` (each kind tiles `[0, blocks)`) | `layout_neg`: an overlapping list fails `contig` |
| `nodeBK4`/`Ind4`/`Sel4` | `nodeBK4_controls` (`N4`: both chains' starts, `hashStmt`, WOTS end, `WM`, `F_{0,1}`, `c_A`, `N8`'s second `c_A`, M) | `layout_neg`: `Sel4` past the node is false; no `chain` block |
| `nodeKind4` (tail) | `nodeKind4_fin2`: `F_{0,2}` carries a 2-segment aggregate's last-block target | `main_not_final2`: the main chain's block at the 2-segment end has counter `64 · aggL 2 ≠ aggB 2`, so the candidate block is needed (R-4-m2) |
| `kf4`, `chainLk4` | `kf4_chainLk_ctrl`: `1` on `stream`, `β³` on `hashA`; the mask links the aggregate's first blocks | the mask does not link the previous node's last block to the aggregate's first |
| `cells4` | `hcells4`: nine cells, in range | `hcells4`'s `Nodup` |
| `PubCells4` | (B′'s `pubOK4_ctrl` is P4b's) | `not_pubCells4_zero` |
| `AggPad4` | `aggPad4_zero` | `not_aggPad4`: a nonzero padding bit fails it |
| `NodeResid4` | (joint satisfiability needs `node_complete`, open) | `not_resid_N2_k3`: an `N2` with a 3-segment aggregate has no residual (R-4-m2) |
| `Active4`, `sub` | `active4_ctrl` (`N2` slots 0, 2; `N8` slot 5 = aggregate 1, sub-slot 1) | `active4_ctrl` (`N2` slot 3; `N8` slot 5 with a one-segment aggregate 1) |
| `chain_digest`/`digLemma4` | the theorems themselves; non-vacuity of their hypotheses is 3.x's `stream_complete`, not ported | — |

## 4. Deviations and decisions (for the blueprint; I did not edit it)

- **D1. The `k`-gated final block (R-4-m2).** The nine block kinds are fixed, and a `stream` block's
  counter and final flag are pinned by its public target. A last block whose position depends on
  the witness's `k` therefore needs **candidate final blocks**:
  - Per aggregate there is one candidate block `F_{a,k′}` for each `k′ < maxK`. Its kind is
    `stream` and its target is `streamTarget (aggB k′) (aggL k′ − 1)`.
  - For `k = maxK` the main chain's last block is the final block.
  - `AggPad4` links `F_{a,k}`'s `h_in` to the main chain's block `aggL k − 2` and its message prefix
    to the main chain's block `aggL k − 1`, and zeroes its padding.
  - The `k`-mux selecting `F_{a,k}`'s `h_out` for WOTS is in `wots`.
  - The blocks sit after `hUsed` (`N2` +2, `N4` +4, `N8` +8 blocks), inside the slack before L.
  - **Blueprint A.6 (revision 4.1) should list them.**
- **D2. `c_A`'s `hashA` block (O-1).**
  - Per aggregate there is one block, the last of its tail group.
  - The aggregate's statement cells (`stC`) are this block's `h_out` elements 2 and 3, not the
    trace's seed payload: the trace binds segment 1's statement, not `c_A`.
  - **Open:** the lemma that `h_out` read as two F elements is `dlo`/`dhi` of the digest, as 3.x's
    `digestOf_halves` does for message cells.
- **D3. `WM`** serves the signed children's WOTS link families only (3.x's families are all WOTS).
  S-0′ sized it at 146 per *verifier* slot, so `(vslots − 2) · 146` blocks stay `free`, which is
  harmless.
- **D4. `truthS4`** drops 3.x's `ChainPartN` second conjunct (`z 0 j = z chainN j`). Both chain
  starts are `streamStart`, whose target pins `h_in` to `h0`.
- **D5. `chainMsg`** is a new pack-map item, added to the JOURNAL for S-E12b. It states the bytes the
  chain hashes. With it, `AggPad4`'s message-prefix link is not needed for the digest. It is needed
  for consistency between the M imports, which read the main chain's cells, and the digest, which
  reads `F_{a,k}`.
- **D6.** Reading the children (the pack map) is the parameter `Read4`. Its facts are `NodeResid4`'s
  pack items. The concrete reader (3.x's `Read.readSigned` at `seq4`, with the aggregate's `π_A`
  assembled from `hdrA` and the sub-slots) is not built.

## 5. Open questions / handover (in order)

0. **Conflict with S-E12b's provisional `pfCells4`** (`FRNodeRows4`, untracked): it reads an
   aggregate child's statement from the seed payload, which holds segment 1's statement and not
   `c_A`. `N4c.cells4` reads `c_A` from its `hashA` block (D2, JOURNAL §4). One map must be chosen
   before the node finals' `cells` are fixed. I recommend `cells4`.

1. **S-E12b**: instantiate `SlotIface4` (rows, `imp`/`rep`/`tpl`, selectors, `soundN`/`soundS` from
   the compiler's soundness) and prove `hRes : StmtN4 → NodeResid4` item by item. Prove `HFit4` with
   `hfit4_of`.
2. **The concrete `Read4`** (D6), and the `h_out` halves lemma (D2).
3. **X4**: `hRun` from the doom chain at `seq4`. Then `nodeLaws4C'` feeds `ks4_E4`'s `hN`, with
   `cells := cells4` in `VC4`.
4. **Blueprint**: A.6/A.7 revision 4.1 layout table with D1–D3. B-13's "first slot muxed over
   `{N4, N8, A}`" is stale (S-0′: `{N2, N4, N8}`).
5. **Completeness** of the node circuit (`node_complete`, the joint satisfiability of `StmtN4` and
   `NodeResid4`) is not in this track.
