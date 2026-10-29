# IMP (track L-circ): RESULT — `aggChk` out of the certificate; `stmtOk4` and the `input` class discharged; ask templates compose

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `7537acd`, re-snapshotted onto
**`953838d`** (RSV-S3, after C1 `6a93cc8`). Build tree `logs/fr-build-IMP` (copy of `fr-build-B4`;
`MINE.txt` symlinks my modules). At `953838d` HEAD + my files builds **without any stub**
(`scaffold/apply.sh` is empty; the stubs I used before RSV-S3 landed are in `apply.full.sh`). Logs
`logs/IMP/`; journal `IMP-JOURNAL.md`. Every lake/lean ran in a 16 GB scope under `timeout`. No
sub-agents, nothing committed, no `sorry` in the worktree.

## 0. Summary

| Item | State |
|---|---|
| 3. `pfView_reassemble4`, `pfView_pf4` | **Done** (`FRXOut4`, `FRSubmission4Cert`) |
| 4. the certificate uses `gap4_of_rowsI` | **Done**: `Gaps4` is now `StmtN4 → Gap4R.imp` (was `Gap4R`, i.e. `imp ∧ aggChk`): `aggChk` is out of the certificate's hypothesis. `Open4F := Gaps4`, `certified (h : Open4F)` unchanged in form |
| 2. PK-m7's statement rows | **Done, folded** (`W4.stmtRows` in `xRowsA`): **`stmtOk4_of_rows`** (every active slot, every selectable index); the `input` registers' target cells (`stmtC_sub`, `stmtC_prev`, `stmtVk`) |
| 1. ask templates | **Partial**: the composition of templates (`AT.add`, `atOk_add`); the **`input` class** template `AT.inp` with `atImp_inp` and its node rows (`W4.inpRows`, folded) giving `inpCells_of_rows`; `gap4Imp_of_runS` (B3's theorem with `stmtOk4` discharged) and **`gap4Imp_of_runI`** (and the `input` class). **Not done**: the ask-answer/FS-link/Merkle-mux/pin templates (`ATAsk`), the other import classes, the fold of `askIRows4` into `nodeIRows4` (§5) |
| HEAD-red fixed in my area | `FRXSig4H.xRows_of_stmt` (B4's fold; one token) |
| build | §3 |
| axioms / source rule | §3 |

## 1. Statement changes

| declaration | change | why |
|---|---|---|
| **`Sub4.Gaps4`** | `∀ …, StmtN4 → Gap4R …` → `∀ …, StmtN4 → ∀ v, Active4 (rd4 pf4) κ w v → SlotImp … (slotIn …) (slotTr …)` (= `Gap4R.imp`) | **shrink**: `aggChk` is B4's theorem. Converse `gaps4_of_gap4R` (the new hypothesis is implied by the old) |
| `Sub4.Open4F`, `Open4`, `certified`, `certificate_sub4F`, `certificateR_sub4F`, `open4_of_F` | text unchanged; their meaning shrinks with `Gaps4` | — |
| `W4.xRowsA` | `xRows ++ chkRows` → `xRows ++ (chkRows ++ stmtRows κ (actW κ))` | the fold (PK-m7 + `input` rows) |
| `W4.extRows4_length_le`, `Rev4.extRowsC_length_le` | `≤ 12,056` → `≤ 12,136` | the fold (80 rows at most) |
| `N4s.chk_hold` (proof only), `X.xRows_of_stmt` (proof only) | membership through the new `xRowsA` | — |

New hypotheses introduced: none on the certificate. New theorems take B4's `PfHdr`/`PfView`, discharged
at `pf4`.

## 2. What was built (`loc.py`: total / code / thm)

| module | lines | content |
|---|---|---|
| `FRNodeRows4AskStmt` (new) | 97 / 46 / 4 | `eqRow`, `eqRowG`; **`stmtRowsS`** (segment slot `sub κ a i`, gated by `actW κ a i`: `hashA` message element `4+e` = stream element `13+e`, `e < 4`), **`stmtRowsP`** (previous node: `hashB1` msg = 13…16, `hashB2` msg = 17…20, `hashB2.h_in = hashB1.h_out`, `hashB2.h_out = seedC κ 0 (2+h)`), **`inOff`**, **`inpRows`** (every slot's `input` cells = its `vk` cells / its statement cells), `stmtRows`; controls `eqRow_ctl` |
| `FRNodeRows4AskStmtS` (new) | 383 / 308 / 23 | block-generic B4 `hA_*` (`hBm_get`, `hBe_eq`, `hBn_eq`, `hBm_eq`, **`leaf_blk`**); `stmt_tgt`; `stmtRows_hold`; `stmtVk`, `stmtC_prev`, `stmt_cells_sub`, **`stmtC_sub`**; `byteAt_extract`, `msg_byte`, `nodeMsg_getD`, `stmtByte_prev`; **`stmtOk_prev`**, **`stmtOk_seg`**, **`stmtOk4_of_rows`** |
| `FRNodeRows4AskInp` (new) | 285 / 205 / 14 | **`AT.add`**, `askCtx_add`, `atAsk_add`, `atImp_add`, **`atOk_add`**; `halves_of_toList`, `dlo_digestOf`; `inC`, `inp_cells`, `failR`, `inpRowsT`, **`AT.inp`**, `InpCells`, **`atImp_inp`**; `slotAsg_inC`, **`inpCells_of_rows`**; **`gap4Imp_of_runS`**, `withInp`, **`gap4Imp_of_runI`**; controls `atInp_cov`, `atImp_inp_neg` |
| `FRXOut4` | +54 | `fitL_extract_getDj`, `phasesOf_seq4_two`, **`pfView_reassemble4`** |
| `FRSubmission4Cert` | +23 / −8 | import `FRNodeRows4AggChkG`; `Gaps4` (§1); **`pfView_pf4`**, **`gap4_of_gaps`**, `gaps4_of_gap4R`; `resid4H_of` via `gap4_of_gaps` |
| `FRNodeLinks4Sub` | 1 line | `links4_of_gaps` via `gap4_of_gaps` |
| `FRSubmission4Fin` | doc | — |
| `FRNodeRows4Ext`, `FRNodeRows4`, `FRNodeRows4AggChkG` | fold | §1 |
| `FRXSig4H` | 1 token | HEAD-red since B4: `exact List.mem_append_left _ hr` |

### 2.1 The theorems, in words

- **`stmtOk4_of_rows (hpf : PfHdr pf) (hpv : PfView pf) (hS : StmtN4 …) : ∀ v, Active4 (rd4 pf) κ w v →
  ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι → stmtOk4 seq4 (kindP (protoOf κ v) ι) (slotIn … v) = true`.**
  A segment needs no row (`stmtOk_seg`): `slotIn`'s `c` is `segC` of the view, which reads exactly the
  bytes `stmtOk4` hashes, once byte 0 is a segment kind's (`kindS_of_rows`). The previous node needs
  the 12 rows: `nodeStmt` of the `stmt` field is `hashB2`'s output (`hashB_nodeStmt`; the message list
  equality is `nodeMsg_getD` + `stmtByte_prev` + the rows; `hashB_sound` gives the tag) = `c₁`.
- **`stmtC_sub`**: an active sub-slot's `c` is its `hashA` block's `h_out` (`leaf_blk` with the 4 gated
  rows and `view_sub`); **`stmtC_prev`**, **`stmtVk`**: `PubCells4`.
- **`atImp_inp (h : InpCells w π inp) : ATImp impl X (AT.inp X π) κ inp w`**: the `input` template
  (2 rows per `input` op: the compiled digest slot's cells = the region's `input` cells `inC π j h`,
  `failR` if the compile gave no digest slot) is sound where those cells hold `vk`'s and `c`'s halves.
  **`inpCells_of_rows`**: the node's `inpRows` + `PubCells4` + the statement rows give `InpCells` at
  every active slot and selectable index.
- **`gap4Imp_of_runI`**: `Gap4.imp` from `RepOk rt`, the folds of the replay rows and of
  `askIRows4 (withInp Aq) κ v b`, `StmtN4`, `PfHdr`, `PfView`, and per active slot and index
  `ATOk … (Aq π) …` (the remaining templates) `∧ SlotRunA (rt π) (withInp Aq π) …` (whose residual
  imports `impAP` already exclude the `input` registers, as `withInp` covers them).
- **`atOk_add`**: `ATOk A` and `ATImp B` give `ATOk (A.add B)`, so each import class of PACK §1.3 can be
  a separate template with its own `ATImp` lemma.

## 3. Build, axioms, source rule, kernel time

- **Build** (`logs/IMP/build-full.log`, HEAD `953838d` + my files, **no stub**): `lake build FR Solution
  FRNodeRows4AskInp` builds 2,647 of 2,648 jobs: **`Solution`, `FRSubmission4Fin`, `FRNodeRows4AskInp`
  green, 0 `sorry` warnings**. The one failure is **`FR.lean` itself, HEAD-red and not mine**: `import
  FRNodeRows4RepNCtrl failed, environment already contains 'FR.N4s.ctlP' from FRNodeRows4RepCtrl` (C1's
  two control modules both define `N4s.ctlP`; FR.lean imports both). Fix (C1/orchestrator): rename one.
- **Axioms** (`logs/IMP/axioms.log`, `fr-build-IMP/ax/AxIMP.lean`, 54 declarations): all ⊆ {`propext`,
  `Classical.choice`, `Quot.sound`}, **no `sorryAx` anywhere, including
  `RecursionFast.Challenge.certified`** (whose only hypothesis is `Open4F := Gaps4`).
- **Source rule** (`logs/IMP/source-rule.log`): 423 files, 0 findings.
- **Kernel time** (`logs/IMP/cpu.txt`, `lean -DElab.async=false --profile`, one core (26), load 6–12):
  type checking / tactics.

  | module | type checking | tactics | before |
  |---|---|---|---|
  | `FRNodeRows4AskStmt` (new) | 0.03 s | 0.04 s | — |
  | `FRNodeRows4AskStmtS` (new) | 1.06 s | 2.29 s | — |
  | `FRNodeRows4AskInp` (new) | 0.15 s | 0.52 s | — |
  | `FRXOut4` | 0.66 s | 0.73 s | 0.55 s (PORT) |
  | `FRSubmission4Cert` | 0.03 s | 0.03 s | < 0.05 s |
  | `FRNodeRows4Ext` | 8.57 s | 0.08 s | 8.75 s (B4: the untouched `xRows_length` simp) |
  | `FRNodeRows4` | 0.16 s | 0.12 s | 0.52 s (B4) |
  | `FRNodeRows4AggChkG` | 1.51 s | 2.86 s | 1.84 s (B4) |
  | `FRXSig4H` | 0.23 s | 0.45 s | — |
  | `FRNodeLinks4Sub`, `FRSubmission4Fin` | < 0.01 s | — | — |

  New kernel time ≈ **+1.35 s** (the three new modules 1.24 s, `FRXOut4` +0.1 s); no `decide` over
  a row list or the format (the field size comes from `fieldSizesOf_seq4`, the block kinds from
  `tgt_of_mem`). Traps avoided: `whnf` on concrete `bytesAt` vectors (generalised:
  `nodeMsg_getD`), `congr 1` on `leafStmtF` (use `congrArg₂`).

## 4. Measurements: V, fit

**Plan correctness with the new rows** (`logs/IMP/plan4t-check.log`): `evalMT4` = the sparse sum over
`nodeIRows4` for N2, N4, N8 (`equal true` ×3), `plan inR true`. **MxKat** (`logs/IMP/mxkat.log`):
compiled `evalMT4`/`evalMX4` = B5's reference on every kind and support (34 `true`, 0 `false`).
`evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX` untouched (modules not edited).

**V(N4)** (`logs/IMP/abv.sh` = B4's with `../B4/b4-bin` (HEAD `7537acd`; C1 and RSV-S3 change no V code
path that the probe times) vs `imp-bin`; 4 alternating rounds × 21 runs, core 29, load 6–12;
`vtime-ab.log`/`.summary`). Best, ms (median of medians):

| | HEAD | **IMP** |
|---|---|---|
| V(N4), own kind | 265.9 (284.9) | **263.1** (279.7) |
| V(N4), all three kinds | 308.0 (343.7) | **308.1** (329.9) |
| `evalMT4` N4 | 144.2 | 147.1 |
| `evalMX4` support all | 189.7 | 187.0 |

Within noise: the fold adds at most 80 rows (slot 1's node rows, `extRowsC`), ≈ 50 µs at B4's
0.6 µs/row. `evalMT4` N8 in the check run was 271.8 ms best (one run, `mxkat` on the next core; B4's
single run was 134.7 ms under its own load): not attributable to 80 rows; re-measure N8 alone when the
machine is quiet if it matters.

**Fit**: H unchanged (no new block; N8's 256 spare blocks unchanged). Slot 1's link rows ≤ 8 + 8,919 +
12,136 = 21,063 < 32,768 (`linkRows4_length_le`, kernel-checked). M cells: 4 `input` cells per slot
region at `388,096 … 388,099` (`inp_cells`: between arena₁'s end 387,752 and the bits 389,120). The
row model (`FRNodeRows4Model`, N8 1.0185× under `N_M/1.05`) is unchanged: the new rows sit in the
link region.

## 5. What remains for `Gaps4` (exactly)

`Gaps4` = `Gap4R.imp` = per active slot `SlotImp`. With `gap4Imp_of_runI` it is reduced to:

1. **The replay** (C1): `RepOk rt` and `repIRows4 rt κ v ⊆ nodeIRows4 κ` (or C1's `RTOkW` form; per the
   orchestrator I did not switch B3's `compileFromX_run` to `RTOkW`).
2. **`ATAsk`** for a template `Aq π` covering every ask (8,783 per prototype): the query equality and the
   answer representation, i.e. PACK §4.2's FS links (absorb/squeeze state = previous answer), the
   Merkle mux rows (`askNode`), the pins (length word + tag), the seed (`vk`/`c` from the `input`
   cells, `hdr` from `PfView`), the columns. Needed machinery (none exists yet): the reader's positional
   spec (entry `k` of `readItems` at the prefix sum of slot lengths), the element alignment of every
   item's payload/answer, `reassemble4`'s positional spec per field (a `piField` op's bytes are its
   item's message bytes), and the arena₁ bridge in the prototype frame (arena₁ cell `π·2^20 + arA1 + e`
   is the slot's stream element `e` via `a1_cells4`, once `a1Rows4` is folded).
3. **`ATImp`** for the other covered classes (`atImp_add` composes them): proof fields → arena payload
   cells, siblings (`l + r + a·cur`), `chF`/`chK`, `bitOf` → L bits, the cap reads `piDigestAt` ((β′)).
4. **`SlotRunA`**'s remaining parts on the answer-driven run: the aux facts (`felems` → arena₂,
   `bits 20` → L), the residual imports `impAP`, the foreign flags (≤ 100 per prototype).
5. **The folds**: `askIRows4 (withInp Aq) κ v b ⊆ nodeIRows4 κ` at `b = arR2` (B2″'s binding rows
   `[720,896, 852,992)`), `a1Rows4`/`a2Rows4`/`bitRows4` into `nodeIRows4`, with the plan
   (`evalMT4`) extended: the ask rows are a fold over the 106 k-op program like `protoCS`, so the plan
   must compute them at process start next to the prototypes (B5's plan, `FRNodeRows4Plan`).
6. **The reserve** (RSV-S3): `gap4Imp_of_rsv` then switches `Gaps4` to `StmtN4R`
   (RSV-S3-RESULT §5.5). My `FRSubmission4Cert` keeps `Gaps4` a plain `def` over `StmtN4` and routes
   through one helper (`gap4_of_gaps`), so the switch is local. **For RSV-S3's prefix form of
   `compileX_run`** (§5.4): `SlotRunA` quantifies the residual imports over all of `impAP rt A π`; a
   prefix form only needs `execA_prefix` (exists) and a prefix version of `askRowsX`/`impAX` (both are
   folds along the same trail, so splitting `ops = pre ++ rest` is `List.foldl`-style bookkeeping).
   `AT.add` makes it easier: the reserve's binding can be one more summand.

## 6. Cells E1 must fill (prover)

- **Statement blocks** (H, per verifier slot `v`): `hashA` at `stmtB κ + 3v` hashes the segment's
  `stmt` message: its message cells (elements 4–7) = the sub-slot's stream elements 13–16 (active
  sub-slots; the rows are gated), i.e. `tagLeaf ‖ h ‖ enc64 n ‖ 0²³`. Previous node (`N2`/`N4`, `v = 0`):
  `hashB1` at `stmtB κ + 1` message = stream elements 13–16, `hashB2` at `stmtB κ + 2` message = 17–20,
  `hashB2.h_in = hashB1.h_out`, `hashB2.h_out = c₁` (the public cells `seedC κ 0 2, 3`).
- **`input` cells** (M, every slot `v`, absolute `κ.oneCell + v·2^20 + 388,096 + {0,1,2,3}`): `vk`'s
  halves (= `seedC κ σ 0, 1` of the slot's signed child `σ`), then `c`'s halves (a segment slot: its
  `hashA` block's `h_out`, H cells `hc (stmtB κ + 3v) 2, 3`; the previous node: `seedC κ 0 2, 3`).
- Once `AT.inp`'s rows are folded (§5.5): each compiled `input` op's two import cells = those cells.

## 7. Requests

1. **Orchestrator (`FR.lean`)**: `import FRNodeRows4AskInp` (pulls `FRNodeRows4AskStmtS`;
   `FRNodeRows4AskStmt` is already pulled by `FRNodeRows4Ext`).
2. **E1**: §6.
3. **C1 / the second assignment**: `gap4Imp_of_runI` takes `RepOk rt` (B3's `RTOk` form) as a
   hypothesis, unchanged; if C1's `RTOkW` is adopted, only `compileFromX_run`'s replay branch changes
   (as `compileFromX_soundRW`), and `gap4Imp_of_runS/I` follow.
