# ASK-T (track L-circ): RESULT — every ask bound: `ATAsk` for the ask generator, `Gap4.imp` from `SlotRunA`

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `74a2528`. Re-snapshotted onto
`44a4975` (CK), then onto **`87519f4`** (IMPC, C1b) for the final build. Build tree `logs/fr-build-ASKT`
(copy of `fr-build-ASKP`; `MINE.txt` symlinks the modules below). Logs `logs/ASKT/`; journal
`ASK-T-JOURNAL.md`. Every lake/lean/probe ran in a 16 GB scope under `timeout`. No sub-agents, nothing
committed, no `sorry` in the worktree.

## 0. Summary

| Item | State |
|---|---|
| A generator covering every ask (8,783 per prototype) | **Done**: `askTGT X π` (`FRNodeRows4AskT`), folded by `askTG` (§1) |
| `ATAsk`: the query equality and the answer representation | **Done**: **`atAsk_T`** (`FRNodeRows4AskTS`), for every ask of both prototypes, **the last item included** (ASK-P's caveat is closed by `AggPad4`, §2.2) |
| `ATOk` / the ask part of `SlotImpA` | **Done**: `atOk_askT`, and **`gap4Imp_of_askT`** (`FRNodeRun4AskT`): `Gap4.imp` from `RepOk rt`, the replay fold, `StmtN4R` and **`SlotRunA` alone** (through IMPC's `gap4Imp_of_impc`) |
| IMPC's class in `askTG` (orchestrator's request) | **Done**: `.add (impcTG (XofT π) π (provLT 0 (protoProg π).ops))`. `colTG` is not folded. **One fix was needed**: IMPC's `provL` overflowed the stack at process start (§1.3) |
| Honest completeness | Every check of the generator passes on both compiled prototypes: **0 failing rows** (§4) |
| Build | **`lake build FR Solution FRSubmission4Fin FRNodeRun4AskT FRNodeRows4AskIR`, plus the probes: green**, 5,029 jobs, 0 `sorry` (`logs/ASKT/build-final.log`) |
| Axioms / source rule | 35 declarations, including `certified`: each ⊆ {propext, Classical.choice, Quot.sound} (`axioms.log`). Source rule: 449 files, 0 findings (`source-rule.log`) |
| **V** | **+≈140 ms of V(N4) from my rows** (§3), above the "tens of ms" guidance; the levers are in §6 |

## 1. The generator (`FRNodeRows4AskT`, below `FRNodeRows4`)

### 1.1 The rows

`askRowsG X π P cs pre op k` runs at ask `k` of the trail (`trailRows`/`trailMS`, the same pass as the
compile). It emits nothing at other ops. Its rows are in the prototype's frame, and arena₁'s element `e`
is the cell `arC π e = π·2^20 + arA1 + e`.

1. **The item check.** `itemsT[k]? = op.item?`; otherwise one `failRT`.
2. **The digest operands** (`dopRows`). These are the absorb/squeeze state at query element `qElT k`,
   and a Merkle node's `l` at `qElT k` and `r` at `qElT k + 2`. `qElT k` is the item's stream offset
   `1 + itOff k`, plus 8 (the length word), plus the tag length, divided by 16.
   - If the slot and the activity are the same at every kind: one row per half, `1·(l_h − A₁(E+h)) = 0`.
   - Otherwise one row per kind and half, gated by the kind's selector: `sel_κ·(l_h − A₁) = 0` at an
     active kind, `sel_κ·A₁ = 0` at an inactive depth (the query is then `nodeQF i 0 0`). A wrong slot
     shape at an active kind gets `sel_κ·one = 0`.
3. **The seed's `vk` and `c`.** Four rows: `A₁(qElT k + j) = inCT π (j/2) (j%2)`, IMP's `input` cells.
4. **The byte operand** (the seed's `hdr`, an absorb's message, a column). **No row.** `preOk` checks
   three things: `pre = piField f o len`, the operand is its result (`m + 1 = |slots|`), and
   `(absOff f o, len)` is item `k`'s source in `srcT`. Otherwise one `failRT`.
5. **The answer** (`ansRowsT`). The ask's digest slot is `A₁(aElT k)`, `A₁(aElT k + 1)`; otherwise one
   `failRT`.

The **tags and length words** need no row: the pack rows already pin every item's first element
(`wfRows`, `headRows`).

### 1.2 The tables

- `itemsT = itemsOf seq4`.
- `offT`: the prefix sums of the stream lengths.
- `srcT = srcOf seq4`. Per phase (`Sh.srcL`), the absolute offset and length of the proof bytes that
  `reassemble4` takes from each item's query: the seed `hdr`, an absorb or uni message, a round's
  message, a column. It is `none` for squeezes, nodes, and fields `≥ nFields4`.

All three are closed constants, built once per process. They are **`@[irreducible]`**: without that,
the elaborator unfolded `itemsOf seq4` in `FRNodeRows4Plan.protoV4_eq` (max recursion) once `askTG`
reached them.

### 1.3 `askTG` (FRNodeRows4) and the stack fix in IMPC's provenance list

```lean
def askTG (π : ℕ) : TG :=
  (((askTGT (XofT π) π).add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)).add
    (impcTG (XofT π) π (provLT 0 (protoProg π).ops))
```

With IMPC's `provL` (non-tail recursion over ≈ 155 k ops), **V's process start crashed with "Stack
overflow detected"**: `plan4t init` and `artime` both aborted at `87519f4` with `impcTG` folded. I added
**`provLT`**, a tail-recursive accumulator, with **`provLT_eq : provLT n ops = provL n ops`**
(`FRNodeRows4AskI`). `askTG`, IMPC's `withImpc` and `pvP` now use it. IMPC's one proof that reads the
list's membership rewrites by `provLT_eq`. After the fix, `plan4t init` gives `inR true`.

## 2. The theorems

### 2.1 `atAsk_T` (`FRNodeRows4AskTS`)

```lean
theorem atAsk_T (Xe : Ext) (impl : OpImpl) (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (hv : N4c.Active4 (rd4 X.pf4) κ w v) (hπ : inp.π = (rd4 X.pf4).slotπ κ v w)
    (hin : InpCells (slotAsg κ v w) (protoOf κ v) inp) :
    ATAsk impl Xe (askTGT Xe (protoOf κ v)).toAT ι inp (slotAsg κ v w) (slotTr4 κ v w)
```

At ask `k` whose rows hold, the item check gives item `k` and its entry `e`. Then:

- **`e.1 = q`, byte by byte** (`q_bytes`: a tag, then 32-byte digests, then a message):
  - **The tag** (`tag_byte`): from the pins (`wfSeg_mem`, `pins_of`; the seed's from `HeadOk.e0`).
  - **Each digest** (`dig_entry`): the operand's slot cells are, by the rows, arena₁'s elements. By
    `a1_slot` those are the H cells, and by `slot_qbyte'` the H cells are the query's bytes (the
    alignment is `qAl`). Where the depth is inactive the elements are zero, which is `zeroD`'s bytes.
  - **The message** (`msg_spec`, `src_spec`): `rd regs m = .b (π.extract A (A+len))`
    (`rd_of_piField`). `π` is `reassemble4 seq4` of this very trace, so its bytes `A + j` are entry
    `k`'s query bytes `qoffOf + j` (`reassemble4_byte` + `ctb4_seed/absorb/uni/rounds/cols` +
    `itemsOf_phIx`). No H bridge is needed.
- **The answer**: the answer slot's cells are `A₁(ansE k)`, `A₁(ansE k + 1)`, which are the entry's
  answer halves (`slot_ans'`).

### 2.2 The last item (ASK-P §6 item 1), closed

**`slot_byte'`** (`FRNodeRows4AskTH`) is `slot_byte` for **every** `x < segB`, given
`AggPad4` at every aggregate. `AggPad4` is a theorem of `StmtN4`'s rows (`wots_aggPad_of_rows`).

- **`chainBytes4_elem'`** and **`readByte_eqz`**: the last block is either the main chain's, or a block
  whose message bits equal the main chain block's.
- **`fin_main`**: with `aggB k = 64·aggL k` the last block is whole (`r = 64`), so `AggPad4`'s `k < maxK`
  conjunct ties the entire message. For `k = maxK`, and for the previous node, the final block *is* the
  main chain's last.

`slot_qbyte'` and `slot_ans'` follow, so the cap check's last squeeze (`CapChkZ`) is covered like every
other item.

### 2.3 The discharged form (`FRNodeRun4AskT`)

- **`atImp_askT`**: the generator covers no non-ask op.
- **`atOk_askT`**: `ATOk … (askAq π) …` at every active slot and selectable index. `askAq π :=
  (askTGT (Xof π) π).toAT` is in `AskPosF`. The input's cells come from IMP's `inpCells_of_rows`.
- **`askFold_askT`**: `askIRows4 (withImpc askAq) κ v arR2 ⊆ nodeIRows4 κ`, via `askFold` with
  `⟨rfl, rfl⟩`.
- **`gap4Imp_of_askT`**: from `RepOk rt`, `hfoldR` and `StmtN4R`, and at every active slot and index
  **`SlotRunA (rt π) (withImpc askAq π) …`**, every active slot's `SlotImp`. It goes through IMPC's
  `gap4Imp_of_impc` with `Aq := askAq`.

**What is discharged:** the whole `ATOk` obligation of `SlotImpA`, both the queries and the answers, for
all 8,783 asks. The answers are excluded from `SlotRunA`'s residual imports anyway (`impAX`). **What
remains** in `SlotRunA` is the aux facts, the residual imports (`impAP`), and the foreign flags.

## 3. Measurements

Load was 2–4. One core per run; the binaries are in `logs/ASKT/askt-bin`.

- **Rows** (`asktcnt.log`). Prototype 0 has 55,212 generator rows, prototype 1 has 62,180. Of these,
  10,452 and 20,904 are gated (the kind-varying Merkle depths). Entries: 162 k and 176 k. With
  `input`, the reserve and `impcTG`, the template rows are **66,263** and **73,294**, under
  `arR2N = 132,096`. Runtime `inR true`, so `ArFit` holds.
- **Process start.** `asktinit.log` measures the memoized trail with and without the generator, two
  runs per prototype. Prototype 0 takes 576–583 ms without it and 612–630 ms with it; prototype 1 takes
  448–461 ms and 528–532 ms. The tables take 7 ms. So **my generator costs ≈ +0.12 s**. `impcTG` adds
  another ≈ +0.40 s (the `askTG` column against `askTGT`: 803–835 and 718–763 ms). **Mine plus `impcTG`
  is ≈ +0.52 s, above the +0.3 s target. Most of it is `impcTG`'s** (§6).
  - `plan4t init` (`plan4t-init-ab.log`, 3 alternating runs) is **7.35–7.56 s user (7.78–7.99 s wall)**,
    against ASK-P's binary (`24ee435`) at 6.18–6.54 s user. That delta of +1.2 s also contains CK's,
    C1b's and IMPC's work, so I did not build a HEAD-minus-ASK-T binary.
- **V** (`vtime-ab.summary` at `44a4975` and `vtime-ab2.summary` at `87519f4`; `abv.sh` against ASK-P's
  binary). Times are best ms, own kind / all kinds:

  | | ASK-P (`24ee435`) | + CK + ASK-T (`44a4975`) | + C1b + IMPC + ASK-T (`87519f4`) |
  |---|---|---|---|
  | V(N4) | 276.4 / 323.1 | **417.5 / 455.5** | **444.6 / 488.9** |
  | `evalMT4` N4 | 154.2 | 308.4 | 326.4 |

  `artime` gives **`askV` 61–63 ms per prototype** (ASK-P: 3.6 ms), about 1 µs per row. A node with
  a previous node evaluates both prototypes, so **≈ +125 ms is mine**. CK's rows are inside that delta
  too.
- **MxKat**: PASS (`mxkat.log`, 34 true).

## 4. Controls

| Definition | (+) | (−) |
|---|---|---|
| `askTGT`, `askRowsG` (every check) | the honest compile: 0 failing rows, both prototypes (`asktcnt`) | `failRT_false`: a failing row refutes `SelOk` |
| `dopRows` | `dopRows_ctl`: a uniform digest operand gives 2 rows on its cells; kind-varying activity gives 6 gated rows | `dopRows_ctl`: a non-digest slot gives the failing row; **`dop_ctl`**: an inactive operand's rows fail where arena₁ ≠ 0 (load-bearing) |
| `preOk` | the honest compile (0 failing) | `preOk_ctl`: no previous `piField` means `false` |
| `srcOf` | `src_spec` (its semantic spec, every entry) | — |
| `provLT` | `provLT_eq` | — |
| `withImpc askAq` / `askTG` | `withImpc_askT`, `withImpcC_askT` (`rfl`) | — |

## 5. Kernel time

`lean -DElab.async=false --profile`, core 27 (`cpu.txt`). Columns are type checking / tactics.

| module | | note |
|---|---|---|
| `FRNodeRows4AskT` (new) | 0.02 s / — | |
| `FRNodeRows4AskTB` (new) | 0.46 / 0.61 s | |
| `FRNodeRows4AskTH` (new) | 1.17 / 0.90 s | |
| `FRNodeRows4AskTS` (new) | 1.56 / 1.98 s | |
| `FRNodeRun4AskT` (new) | 0.09 / 0.13 s | |
| `FRNodeRows4` | 0.16 / 0.15 s | 0.17 at ASK-P |
| `FRNodeRows4AskI`, `AskPosF`, `AskIS`, `AskIR` | 0.09 / 0.08 / 0.40 / 0.80 s | IMPC's and ASK-P's modules, small edits |

The new modules add ≈ 3.3 s of kernel time. **None of it is on `certified`'s path** until `Gaps4` is
routed through `gap4Imp_of_askT`. There is no `decide` over a table, a row list or the format: the
tables are read positionally, symbolically. The closed-sum trap was avoided with `unfold offT itOff`
in `offT_get`.

## 6. Open items and levers

1. **V: +≈125 ms of my rows per node** (≈ 117 k rows, 338 k entries). Levers:
   - (a) The compile could alias each ask's answer slot to arena₁ (CK's `FRVIRCompile`). That saves
     2 rows per ask, about 17.5 k per prototype (≈ 30 %).
   - (b) Where only the activity depends on the kind (the slot is uniform), use the gate rows
     `gate(act)·(A₁ − l) = 0` and `gate(¬act)·A₁ = 0`: 8 rows per node instead of 12.
   - (c) A structured or keyed evaluation of the regular per-item rows (`askV` is generic sparse, about
     1 µs per row).
2. **Process start: +0.12 s mine, +0.40 s `impcTG`.** For IMPC, `winE` runs `pfLoc` 17 times per
   window, each a linear `pSegs.find?`, and `winsOk`/`zRows` run it again per window of the large
   zero-pinned fields. A cached or binary-searched `pfLoc`, or `provOf` over an array, are IMPC's
   levers.
3. **`Gaps4` is not rerouted.** `gap4Imp_of_askT` is a theorem. Making the certificate's hypothesis
   its decomposed form (`∃ rt, RepOk ∧ fold ∧ SlotRunA`) is not a shrink, for SRA's reason, so I did
   not change `FRSubmission4*`.
4. **`bitOf` through `SlotRunA`** (IMPC's item 3): not taken, and open. It needs the `idx`/`shrN`
   register provenance on the concrete run.
5. `colTG` is not folded, as the orchestrator asked.

## 7. Rows and cells E1 must fill

**No new cells.** The template rows sit at `σ·2^20 + arR2 + k`: prototype 0 has 66,263, prototype 1
has 73,294. They hold on the honest witness when the following hold:

- each ask's answer import cells hold its answer's halves;
- every digest operand's cells hold the item's query elements;
- `input` cells as in IMP §6.

The honest trace has all three, given that arena₁ is the stream. **Re-dump the plan form**:
`protoV4`'s value changed.

## 8. Statement changes (all listed)

| declaration | change |
|---|---|
| **`FRNodeRows4.askTG`** (def) | `TG.none` replaced by `askTGT (XofT π) π`, and `.add (impcTG … (provLT 0 …))` added; imports `FRNodeRows4AskT`, `FRNodeRows4AskI` |
| `FRNodeRows4AskPosF.withRsv_none`, `askFold_rsv` | **removed** (they stated today's template is `AT.none`; no users). Added `askAq`. Today's fold is `FRNodeRun4AskT.askFold_askT` |
| `FRNodeRows4AskI` | **added** `provAcc`, `provLT`, `provAcc_eq`, `provLT_eq`; `provL` unchanged |
| `FRNodeRows4AskIS.withImpc` (def) | `provL` → `provLT` (equal by `provLT_eq`); `askTGI := askTG π`; `withImpc_none` → **`withImpc_askT`** (at `askAq`) |
| `FRNodeRows4AskIR.pvP` (def) | `provL` → `provLT`; one proof line (`rw [← provLT_eq]`); `withImpcC_none` → **`withImpcC_askT`** |

Unchanged in text: `Gaps4`, `Open4F`, `certified`, every `Gap4`/certificate statement, `gap4Imp_of_impc(R)`,
`askFold`, `hfit4`, `protoV4_eq`, `ArFit`.

## 9. Files

- **New**: `FRNodeRows4AskT.lean` (139 lines: 68 code), `FRNodeRows4AskTB.lean` (262: 215),
  `FRNodeRows4AskTH.lean` (242: 187), `FRNodeRows4AskTS.lean` (406: 339), `FRNodeRun4AskT.lean`
  (`loc.txt`).
- **Edited**: `FRNodeRows4.lean`, `FRNodeRows4AskPosF.lean`, `FRNodeRows4AskI.lean`,
  `FRNodeRows4AskIS.lean`, `FRNodeRows4AskIR.lean`.
- **`FR.lean` (orchestrator)**: `import FRNodeRun4AskT`. It pulls in AskTS, AskTH and AskTB;
  `FRNodeRows4AskT` comes with `FRNodeRows4`.
- **Build-tree probes (dev)**: `probe/AskTCnt.lean`, `probe/AskTInit.lean`.
