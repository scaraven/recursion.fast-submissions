# S-N2 RESULT: residuals 3–4 of `ks_rev4F`: the `SlotIface4` instance, its reader, and `hRes` item by item

Base: HEAD `ef18e75` (S-E12f). HEAD moved to `7292eab` (R4i) during the stage, and the final builds
use `7292eab`'s sources (`snap.sh` re-snapshots HEAD). Build tree `logs/fr-build-SN2` is a copy of
`fr-build-SE12f` against `logs/org20`. `MINE.txt` lists the six new modules. Logs are in
`logs/S-N2/`; the journal is `S-N2-JOURNAL.md`. Every lake and lean command ran in the 16G scope
under `timeout`. There were no sub-agents and nothing is committed. No existing module was edited.

## Status

| Item | State |
|---|---|
| 1. The `SlotIface4` instance | **Done.** `I4 impl₀ base hT₀ hT`, with `lrows = lRows4` and `irows = nodeIRows4` (`I4_rows`). `soundN` and `soundS` are proved from `protoCS_soundAt` and INT-8's `progNodeGK_exec`/`progSegG_exec`. The concrete reader is `rd4 pf` (S-E12a's D6). |
| 2. `hRes` item by item | **Done up to the circuit's gaps.** `resid4_of : StmtN4 → Gap4 → NodeResid4 (I4 …) (rd4 pf)`. Every item with rows, or fixed by the reader, is proved. **Seven items have no rows** (§2): `imp`, `kindN`, `kindS`, `wf`, `aggChk`, `aggPad`, `wots`. These are soundness gaps. The converse `gap4_of_resid` shows `Gap4` asks nothing beyond `NodeResid4`. |
| 3. `ks_rev4H`/`certificate_rev4H` | **Done.** They are on P4f. They are also on R4i's `ks_rev4G` as **`ks_rev4GH`/`certificate_rev4GH`**: residual 2 is closed there, and the base is the concrete `Impl.implC`. The remaining hypotheses are in §3. |

**Checks:**
- `lake build FR FRNodeSound4Ctrl` is green: 2,552 jobs (`logs/S-N2/build-final.log`).
- **Axioms** (`logs/S-N2/axioms.log`, `logs/fr-build-SN2/ax/AxSN2.lean`): 46 declarations, including
  `I4`, `resid4_of`, `ks_rev4H`, `certificate_rev4H`, `ks_rev4GH`, `certificate_rev4GH` and
  `gap4_of_resid`. Each uses only `propext`, `Classical.choice` and `Quot.sound`, or a subset of them.
  None uses `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 333
  files, 0 findings (`logs/S-N2/source-rule.log`).
- **Imports for `FR.lean`:** add `import FRNodeSound4Ctrl`. It pulls in the other five modules.

## 1. What was built (`loc.py`, `logs/S-N2/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeSound4` | 241 / 152 / 19 | `tinIRows_snd`, **`slotIRows_snd`**: a slot's indexed rows are `rowList ++ tplRows`, with no evaluation. **`SlotRows`**, **`slotRows_hold`**, **`slotRows_of`**. **`implP`**: the kind's ops read at `tix` (`fixK`), so they ignore the run's index. `implTF_fixK`, `routeOk_fixK`, `implTF_implSeg`, `implTF_implP`, `routeOk_implP`. **`SlotRun`**, **`SlotImp`**, **`SelN`**, **`SelS`**, `slot_ok`. **`I4`**, `I4_rows`. |
| `FRNodeRead4` | 141 / 69 / 6 | **`kAct`**: the circuit's segment count, which is the first inactive sub-slot. **`segTr`**: the traces, read off H's `chainBytes4` with 3.x's `readItems` at `seq4`'s items. `slotTr4`, `fitL`, `slotPf`. `hA`/`hAe`/`hAn`: `(e, n)` from the `hashA` block. **`aggPf`**: `aggHdr` with `kAct`, followed by the fitted slot proofs. `readSig4`. **`sgn4`**, **`rd4 pf`**. `byteAt_mk`, `aggHdr_length`, `sgn4_agg`, **`kA_rd4`**: the header's `k` is `kAct`. |
| `FRNodeRead4W` | 107 / 78 / 6 | **`WfAt`**: the length words. `entry_bytes`, **`take_readItems`**, `traceBytes_flatten`, `take_mul_flatten`, `slenS_seq4`, **`stream_of_wf`**: a well-formed stream is `0x54 ‖` the read traces. |
| `FRNodeSound4R` | 377 / 287 / 25 | `one_of_pubCells`, `protoFit_of`, `linkRows_hold`, **`actK_kAct`**. `kindOf4_of`, `segView_of`. Lengths. `shQ4`, `sh_qlen4`, `phasesOf_shQ4`, **`itemsOf_qlen_le`**, `sgn4_qcap`. `nSeg`, `slotTr4_sub`, **`chainMsg_of_wf`**. **`Gap4`**, **`resid4_of`**. |
| `FRNodeSound4K` | 121 / 75 / 5 | **`ks_rev4H`**, `Resid4H`, `resid4_of_H`, **`certificate_rev4H`**, **`ks_rev4GH`**, `Resid4GH`, **`certificate_rev4GH`** |
| `FRNodeSound4Ctrl` | 259 / 202 / 22 | The controls (§4), and the converse **`gap4_of_resid`**, with `wf_of_chainMsg`, `wf_of_eq`, `sgn4_tr`, `chain_len`, `wfAt_of_take`, `readItems_sizes`, `traceBytes_length_of`, `drop_take_blocks`, `selOk_unique`, `byte_of_kindOf4`, `byte_of_segView` |
| **total** | 1,246 / 863 / 83 | |

### Item 1: `I4`

```lean
noncomputable def I4 (impl₀) (base) (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) :
    N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) where
  lrows := lRows4;  irows := nodeIRows4
  imp κ v w inp tr := SlotImp impl₀ base κ v w inp tr
  rep _ _ _ _ _ := True
  tpl := SlotRows
  selN := SelN;  selS := SelS
```

- **`tpl` = `SlotRows κ v w`.** The prototype's compiled rows and its template rows hold at
  `slotAsg κ v w`. This follows from the M rows (`slotRows_of`): a slot's rows are its indexed rows'
  second components (`slotIRows_snd`), moved by `holds_rowMapC`.
- **`SelN κ v w κ'`.** `v` is the previous node's slot (`isPrevSlot`), and `SelOk (slotAsg κ v w)
  (protoP 0) ι` holds with `nodeAt ι = κ'`.
- **`SelS`.** The same for a segment slot, with `protoP 1` and `segAt`.
- **`imp` = `SlotImp`.** At every index `ι` the selectors may pick:
  - `SlotRun`, which is exactly `protoCS_soundAt`'s run-dependent hypotheses:
    - `exec (implP …) ι inp (protoProg π).ops St.init tr = some (s, [])`;
    - the auxiliary cells;
    - the import registers' cells;
    - the foreign flags.
  - The statement fact `stmtOk4 seq4 (kindP π ι) inp`.
- **`rep` = `True`.** The circuit has no replay `R` (§2, `imp`).
- **`soundN`/`soundS`.** The proof has four steps:
  1. `slot_ok`: `protoCS_soundAt` at `implP π ι` gives an accepting run.
     - `ImplTF` by `implTF_implN4F`/`implTF_implSeg` and `implTF_fixK`.
     - `RouteOk` by `routeOk_implN4F`/`routeOk_implSeg` and `routeOk_fixK`.
  2. The group program's run at `ι` is the kind's program's run at `tix`. This is
     `progNodeGK_exec cells4` (`cells4_len`) or `progSegG_exec`. The hypothesis
     `impl'.fixK tix = (impl'.fixK tix).fixK ι` is `rfl` (`fixK_fixK`).
  3. `runSeq_runIR`, `semIR`, `kindOn_node`/`kindOn_seg`.
  4. `runStmt_iff`.

  `implP` is the reason step 2 needs no hypothesis on the ops. `implN4F`'s `targetS` and
  `linkWAll` read `κ.isNode`, so at index `L32`/`P30` they would not equal their values at `N30`.
  Reading them at `tix` makes the slot's ops ignore the index. The kind-free template fields are
  unchanged: `slotW` is constant. The new hypotheses `hT₀`/`hT` (`ImplT` of the bases) hold at the
  submission's `implC` by `implCWith_implT`, and `ks_rev4GH` discharges them.

### The reader `rd4 pf` (S-E12a's D6)

- **Aggregate `a`'s `k` is `kAct κ a w`.** It is the first sub-slot whose activity
  `S_σ = Σ_ι s′_ι` is not 1, or `maxK` (`Nat.find`).
  - **`actK_kAct`**: on the rows, `kAct` meets S-E12c's `ActK`. The ingredients are `act_first`,
    `act_mono` (through `Nat.find_min`) and `selSum_bit`.
  - So `kA` (the header's byte 1, `kA_rd4`) is the number of active sub-slots.
- **Traces.** The traces are read off H's stream `chainBytes4 κ σ k w`. Segment `i` is `seq4`'s
  items, read from offset `1 + i·(segB − 1)` (`segTr`). An aggregate's trace is its active
  sub-slots' traces in order. A previous node's trace is segment 0 of its stream.
- **Proofs.**
  - A slot's proof is `pf (its trace)`, fitted to `piSizeOf seq4` bytes.
  - **`pf` is a parameter.** It is the proof a `seq4` trace carries: 3.x's `reassemble` at `seq4`,
    which S-H4 owns. Any `pf` works for `ks_rev4H`, because every tie between a proof and the
    circuit is in `imp`.
  - `π_A` is `aggHdr k n e` followed by the active sub-slots' proofs, with `(e, n)` read from the
    `hashA` block's 41 message bytes (D2).
- **Signatures.** 3.x's `readSig` layout at signed child `σ`'s `2^14` L stride (`sigCell`). This
  assumes A.7 puts signed child `σ`'s 299 signature elements at the start of stride `σ`, as
  `lBitCells4`'s offset 299 suggests. The `wots` gap covers it either way.

## 2. `hRes` item by item, and the gaps

`resid4_of` (`FRNodeSound4R`), per `NodeResid4` field:

| Field | Proved from | Gap (`Gap4` field) |
|---|---|---|
| `tpl` | M rows (`slotRows_of`). `one = 1` comes from `PubCells4` (`one_of_pubCells`), so the rejecting-row branch of `nodeIRows4` is impossible (`protoFit_of`). | — |
| `rep` | `True` | — |
| `selP` | Selector: `selP_sel` with `linkRows_hold`. Size of the read proof: `fitL`. | **`kindN`**: byte 0 of the read previous-node proof is `(nodeAt ι).byte` |
| `slotP` | the reader (`rfl`) | — |
| `selA` | Selector: `selA_sel` with `actK_kAct`. | **`kindS`**: byte 0 of an active sub-slot's proof is `(segAt ι).byte` |
| `pack` | Size: `48 + k·798,192 < 2^64`. Trace length: `k·8,905 ≤ qV4` (`traces_le_qV`). Queries: each `≤ queryCap` (`itemsOf_qlen_le`: one `decide +kernel` over `seq4`'s phase shapes, `phasesOf_shQ4`, never over items). | — |
| `chainMsg` | `chainMsg_of_wf` (`stream_of_wf`) | **`wf`**: the stream's byte 0 is `0x54`, and each read item's 8-byte length word is `enc64 qlen` (`WfAt`) |
| `aggFmt` | the reader: `aggPf_size`, the header, `aggSegs_flat` | — |
| `aggTr` | the reader (`rfl`) | — |
| `aggChk` | — | **`aggChk`** (as stated) |
| `kOk` | `kA_rd4`, `kAct_le` | — |
| `aggPad` | — | **`aggPad`** (as stated) |
| `wots` | — | **`wots`** (as stated) |
| `imp` | — | **`imp`** (as stated, `SlotImp`) |

**Why each gap is real.**
- `nodeIRows4`'s cells are M cells and L selector bits only (`slot_mem`). `lRows4` holds bit rows on
  L cells.
- No row of either list mentions an H cell. The WOTS rows exist only in the row model
  (`FRNodeRows4Model.wotsRows4`).

The gaps, item by item:

1. **`imp`: no pack map, no `input` alias, no `R`.** Every import register of the slot's compiled
   program is unbound. The breakdown below comes from `logs/S-E12f/nodedump`: each
   `mregs-p{π}.txt` import line is joined to the op in `proto-p{π}.txt` that produces it.

   | Source | Prototype 0 (node) | Prototype 1 (segment) |
   |---|---|---|
   | proof fields (`piDigest`, `piElem`, `piDigestAt`, `piElemK`) | 7,555 + 1,068 + 871 + 355 | the same |
   | oracle answers (`askNode`, `askCol`, `askSqueeze`, `askAbsorb`, `askSeed`) | 7,552 + 871 + 305 + 176 + 1 | the same |
   | answer bits (`bitOf`) | 7,552 | 7,570 |
   | challenge conversions (`chF`, `chK`) | 289 + 29 | the same |
   | public input (`input`: `vk`, `c`, the statement fact's `c`) | 4 | 3 |
   | ops `R` would replay (`evalM`, `evalL`, `targetS`, `shiftTarget`, `linkWAll`, `rsWeight`) | 3 + 3 + 1 + 1 + 1 + 1 | the same |
   | **total** | **26,638** | **26,655** |

   The breakdown shows that `imp` also contains:
   - 2,498 auxiliary imports per prototype: 1,627 `bits 20` (the `tensorW` index bits), 581
     `felems 16`, 290 `felems 64`;
   - the foreign flags (INT-9: 12 for prototype 0, 79 for prototype 1);
   - the run's existence on the trace;
   - the statement fact `stmtOk4`.

   A prover can write any values into these cells, and every row still holds (S-N1's O2, unchanged
   at 4.1).
2. **`kindN`/`kindS`: the child's kind byte.**
   - No row ties the slot's selector copies to byte 0 of the proof the reader reads. That byte
     reaches M only as an import (`piElem 0 0`) and H only as stream bytes.
   - **Observation, not proved:** the group program begins with `piElem 0 0 → r2`,
     `const {L,P,N} → r3`, `assertEq r2 r3` (`proto-p0.txt`, lines 3–5). The run therefore checks
     the kind header against the selected index's constant on the *imported* cell. With the pack
     map (`imp`), `kindN`/`kindS` would follow from the run. They are not independent of `imp`, but
     deriving them needs the program's first ops, which means evaluating the generator. I did not
     do that.
3. **`wf`: the stream's constant bytes.** These are the tag byte `0x54` and the length word of each
   item at its fixed offset.
   - The stream blocks' targets pin only the counters and the final flags, so a prover can hash a
     byte string that is no trace's encoding. With `wf` the reader's trace is exactly what H hashed
     (`chainMsg_of_wf`), and `wf_of_chainMsg` proves the converse.
   - **This gap is cheap to close.** The positions are public: one per stream plus one length word
     per item, at offsets `1 + i·(segB − 1) + streamOff`. They can be pinned in the stream blocks'
     public targets, or by L/M rows on H cells.
     - For an aggregate, pin the words of all `maxK` segments in the main chain. An honest prover
       can always write them.
     - The words in the last block `F_{a,k}` then also need `aggPad`'s message-prefix link.
4. **`aggChk`: `V_A`'s checks against `c_A`.** No row checks any of the following:
   - `c_A = leafStmt e n` with `(e, n)` from `hashA`. The reader reads `(e, n)` there; what is
     missing is D2's `h_out`-halves link to `stC` plus a row;
   - `1 ≤ k ≤ 4`. This one follows from the activity rows and `kOk`;
   - each segment's `1 ≤ nᵢ ≤ cap`;
   - `Σ nᵢ = n`;
   - the last end `= e`;
   - the chaining `startᵢ₊₁ = hᵢ` across sub-slots.
5. **`aggPad`, R-4-m2: the `k`-gated final block.** No row links:
   - `F_{a,k}`'s `h_in` to the main chain's block `aggL k − 2`;
   - its message prefix to block `aggL k − 1`;
   - its padding bytes to zero.

   `truthS4`'s static mask cannot express any of these, because they depend on the witness's `k`.
6. **`wots`.** No rows implement any of the following:
   - the `k`-mux over the candidate final blocks' `h_out`;
   - the digit decomposition of the digest;
   - the per-digit chain selection;
   - the mirror sources and the Merkle path.

   This is S-N1's O2b, unchanged at 4.1. Its rows exist only in the row model: 2 × 2,788.

**The converse (`gap4_of_resid`, `FRNodeSound4Ctrl`).** `NodeResid4 (I4 …) (rd4 pf)` implies `Gap4`:
- `kindN`/`kindS` come from `selP`/`selA`, by uniqueness of the selected index (`selOk_unique`),
  `byte_of_kindOf4` and `byte_of_segView`;
- `wf` comes from `chainMsg` (`wf_of_chainMsg`);
- the other fields are identical.

With `resid4_of`, `hGap` is exactly `hRes` minus what the rows and the reader prove: nothing was
added.

## 3. The final theorems and their remaining hypotheses

```lean
theorem ks_rev4H (impl₀ base S vk) (hV) (hq) {nd} (hE) (hε)
    (hRun : X4.RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (pf : Trace → Proof)
    (hGap : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → Gap4 impl₀ base pf κ vk c₁ c₂ w)
    (D : NodeDec4 nd) (hL : …) : KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV

theorem ks_rev4GH (fin lRows κs₀) (S vk)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq) {nd} (hE) (hε) (hO : R4.SegOut4 (VsegC (Impl.implC fin lRows κs₀)) vk) (pf : Trace → Proof)
    (hGap : … Gap4 (Impl.implC fin lRows κs₀) (fun _ => Impl.implC fin lRows κs₀) pf κ vk c₁ c₂ w)
    (D : NodeDec4 nd) (hL : …) : KS …
```

**Remaining hypotheses of `ks_rev4GH`.** The definitional ones (`hV`, `hq`, `hE`, `hε`) and:

| Hypothesis | What it is | Owner |
|---|---|---|
| `hO : SegOut4` | R4i's: the segment's `π` size and `n ≤ cap` | R4 |
| `pf` | any function; for the extractor's pairing (residual 6), S-H4's `seq4` reassembly | S-H4 |
| `hGap` | `Gap4`: `imp`, `kindN`, `kindS`, `wf`, `aggChk`, `aggPad`, `wots` (§2) | **L-circ**: missing rows |
| `D : NodeDec4 nd` | residual 5 | S-H4 |
| `hL` | residual 6 | S-H4 |

- **`ks_rev4H`** (on P4f) has `hRun` (residual 2) in place of `hO`, plus `hT₀`/`hT`.
- **`certificate_rev4H`/`certificate_rev4GH`** also take `hext`, `hfuel`, `hnd` (residual 7),
  `hC` (residual 8) and `hδ` (residual 9). The per-key residuals are bundled in
  `Resid4H`/`Resid4GH` (`run`/`out`, `gap`, `links`).

## 4. Controls (`FRNodeSound4Ctrl`)

| Definition | Positive | Negative |
|---|---|---|
| `SelN`/`SelS` | `selN_ctl`: `N4`'s slot 0 with its `L32` copy set selects `N4` | `selN_neg`: `N8` has no previous-node slot; `N4`'s slot 0 is no segment slot |
| `SlotImp` | `slotImp_idle`: a slot with no selected index owes nothing, so the inactive sub-slots carry nothing | `slotImp_stmt`: at a selected index, a false statement fact fails it |
| `SlotRows` | `slotRows_hold` (from the M rows) | `rejectRows_ctl` through `slotRows_of` (the `¬ ProtoFit` branch is refuted) |
| `kAct` | `kAct_ctl`: activity 1, 1, 0 gives `2` | `kAct_ctl`: not `3`; `actK_ctl` (S-E12c) |
| `rd4`/`aggPf` | `aggPf_kind`: `π_A` is `'A'`; `kA_rd4` | — |
| `WfAt` | `wfAt_ctl`: `enc64 40 ‖ 0⁷²` is a squeeze | `wfAt_ctl`: `0⁸⁰` is not |
| `Gap4` | **`gap4_of_resid`** (the converse of `resid4_of`) | `gap4_kindN`: a wrong kind byte at the selected index has no `Gap4` |
| `I4`, `ks_rev4H` | `ks_rev4H`, `ks_rev4GH` build; `I4_rows` | — |

## 5. Times (sequential: `taskset -c 26 lake env lean -DElab.async=false --profile`, 16G scope; `logs/S-N2/profile-*.log`)

| Module | wall (imports ≈ 6 s) | type checking | tactics | simp | max RSS |
|---|---|---|---|---|---|
| `FRNodeSound4` | 7.3 s | 0.06 s | 0.24 s | 0.12 s | 2.86 GB |
| `FRNodeRead4` | 6.6 s | 0.02 s | 0.03 s | 0.05 s | 2.91 GB |
| `FRNodeRead4W` | 7.2 s | 0.17 s | 0.16 s | 0.06 s | 2.91 GB |
| `FRNodeSound4R` | 8.6 s | 0.23 s | 0.47 s | 0.40 s | 2.94 GB |
| `FRNodeSound4K` | 6.4 s | 0.01 s | — | — | 2.97 GB |
| `FRNodeSound4Ctrl` | 8.3 s | 0.30 s | 0.35 s | 0.41 s | 3.00 GB |

The kernel never evaluates a layout, a compile or a program:
- the rows enter through `slotIRows_snd` (structural);
- the group programs enter through INT-8's structural `*_exec`;
- the only `decide +kernel` is over `seq4`'s phase shapes (`phasesOf_shQ4`), with parameters only.

## 6. Deviations and decisions

1. **`rep` is `True`.** The circuit has no `R`. The six ops `R` would replay are import registers
   (§2), so they are inside `imp`. If L-circ builds `R`, `rep` can take its claims, and `imp` would
   shrink to the remaining imports.
2. **`imp` is a single predicate per slot (`SlotImp`).** It is quantified over the selectable index,
   so an inactive slot owes nothing (`slotImp_idle`).
3. **`I4` needs `ImplT` of the bases.** `ImplTF keys41` holds only for bases that meet the
   templates. `ks_rev4GH` discharges this at `implC`.
4. **`implP` reads the ops at the program's `tix`.** The compiled slot runs under these
   index-blind ops, so INT-8's bridge applies by `rfl`. This changes no statement: `SlotIface4`'s
   conclusion is about `VnodeC`/`VsegC` at their own ops.
5. **`chainMsg` is replaced by `wf` in `Gap4`.** The two are equivalent on the reader:
   `chainMsg_of_wf` and `wf_of_chainMsg`.
6. **`pf` is a parameter of the reader.** `seq4`'s reassembly is not built. Nothing here depends
   on it.
7. **The signature's L position** (`sigCell`) is read at stride `σ`. That A.7 places it there is an
   assumption of the reader only.

## 7. Open questions (for the orchestrator)

1. **The missing rows (L-circ)**, in order of cost:
   - (a) `wf`: pin the tag and length words, as public target bits or rows.
   - (b) `aggPad`: `k`-gated links over H cells, muxed by the activity selectors.
   - (c) `aggChk`: `V_A`'s checks across the sub-slots' imported views, plus D2's halves lemma.
   - (d) `wots`: the 2 × 2,788 rows of the model.
   - (e) `imp`: the pack map (M import cells against H stream cells and the public seed cells),
     `R` for the 10 replay registers, the answer bits and the auxiliary bits against L, the
     challenge conversions, and the foreign flags.

   Once (e) is done, `kindN`/`kindS` should follow from the program's kind-header assertion.
2. **S-H4:** `pf` (the `seq4` reassembly), and residual 6's `readW` against `rd4`.
3. **`FR.lean`:** add `import FRNodeSound4Ctrl`.
