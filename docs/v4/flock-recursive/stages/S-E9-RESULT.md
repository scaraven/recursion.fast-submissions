# S-E9 (track L-circ): RESULT — stopped at the row kill rule, with `R` sized from the real plan

Stage S-E9, 2026-10-28, HEAD `ebcc8f1` (INT-3, revision 3.14). Build tree `logs/fr-build-SE9` (a
copy of `fr-build-INT3`; `snap.sh` symlinks L-circ's modules and this stage's new modules, every
other module is HEAD's). Logs are in `logs/S-E9/`; the journal is `S-E9-JOURNAL.md`. Every
lean/lake/probe command ran in the 16 GB scope with a `timeout`. Nothing is committed.

## Status by item

| Item | State |
|---|---|
| 1. `R` in the §4.4 layout | **Sized from the real plan, not built** (§1). The 259 k figure misses the skeleton's sparse rows and the per-instance assembly. Measured statistics give **R1s ≈ 387 k rows per slot** if R uses the slot symmetry (verified: slot 1 is slot 0 shifted by `2^20`), 581 k without. No `replay_mle`/`plan_wf`/`replay_sound`/`inc_mle`/`eqTree_mle` yet. |
| 2. Fused child walk | **Not done.** Blocked with `walkAB` (§2): `A₀`/`B₀` have 87.4 M nonzeros, so neither the walk template nor R's walk u-rows can be row-per-product. |
| 3. `FRNodeLayout`, mirror map, `mRowModel` | **Done.** `wmSlot = 146`, `hEnd = 47,594`, `regions_fit`; the A.6 map in one place (`Layout.mirBlock`/`mirPos`/`mirElem`); `FRNodeMirror` proves S-C's `wmB`/`mirB`/`mpos`/`fam` agree with it; `mRowModel` updated (§3). |
| 4. Templates | **Partial.** `tplShiftMask` is proved and wired. `packFK` with equal-length kind lists is now compiled, which binds `maskRows`. `walkAB` is blocked (§2). Not started: `tplTargetSNode`, `tplLinkWAll`, `rsWeight`, `shiftTarget`, the 745 `tensorW`. `shiftMask` stays an import because its `τ` operand has a kind-dependent length (§4). |
| 5. Re-dump, V | **Done** for the circuit as it now stands (§5, §6). **V = 207.2 ms best** (it was 168.7 ms). |

**Kill rule (rows): it fires on S-E9's sizes.** The aligned layout as built measures 436,092 rows
per slot. Adding S-E9's sizes for the parts not yet built gives **1,065,133 rows per slot and
2,130,266 per node, over `2^21` (0.98×)**. With the phiRS lever it is 1.045×. §1 gives the
arithmetic and the levers. I stopped there.

## 1. `R`: what it must replay, measured

The probe `probe/RStat.lean` reads the actual plan (`logs/S-E9/rstat-0.log`, at HEAD, before this
stage's templates). Per slot it finds:

- 68 keys: 204 key×matrix blocks, 9,056 rows with local terms, 3,701 inputs;
- 3,790 instances, which form 3,582 runs, so they are not laid out consecutively;
- 5,408 own cells;
- **6,169 sparse rows**, with 18,354 forms, 19,029 (form, cell-high) groups and 31,103 entries;
- 3,352 shared forms;
- 20,510 distinct cells.

Under §4.4's rule an irregular operand costs a companion row. The rule: constants go only in the
coefficients of linear rows, and a product reads an irregular cell only from an `eq` table of the
child's `σ`. So the sparse skeleton and the instance assembly (`hfac` factors, own inputs) cost about
**193 k rows per child slot**. The 259 k model (`sizes.py` "(D)") counts neither.

**Slot symmetry** (`logs/S-E9/rstat-sym.log`, kernel-free check over the plan):

- slot 1's pieces are slot 0's with rows `+2^20`;
- 20,506 of the 20,510 cells map to `c + 2^20`; 3 L cells map to `+2^14`; the `one` cell is fixed;
- 0 bad rows, 0 bad forms.

So `MLE(M) = Σ_{slot 0 entries} v · eq(τ_{<20}, r) · β̃(c)`, with `β̃(c) = (1−τ₂₀)eq(σ,c) +
τ₂₀eq(σ,c′)`. R then replays one slot's structure.

`logs/S-E9/rcount.py` → `rcount.log` gives the per-class formulas:

| | R per slot | node rows (with M∖R = 596,140) |
|---|---|---|
| R1s: slot-symmetric, walks as `A₀`/`B₀` u-rows (changes 21's assumption) | 387,291 | 1,966,862 = 2^20.91 (1.066×) |
| R1: two child slots separately | 580,763 | 2,353,806 (0.89×; 0.94× with the lever) |
| **R1s with the walks replayed as the XOR DAG (§2)** | **412,606** | see below |

**The node, with S-E9's sizes** (per slot):

| Part | Rows |
|---|---|
| measured aligned layout (incl. `shiftMask`, `maskRows`) | 436,092 |
| `rsWeight` | 45,604 |
| `walkAB` as an XOR-materialised template (≈ 6·10⁴ XOR + 30,851 products; estimate) | 90,851 |
| `shiftTarget` with the bit decomposition (estimate) | 1,300 |
| `finPf`'s 745 `tensorW` | 47,680 |
| `tplTargetSNode` | 16,000 |
| `tplLinkWAll` | 15,000 |
| R (R1s, DAG walks) | 412,606 |
| **total** | **1,065,133** |

That is **2,130,266 per node, over `2^21` by 33 k**.

**Levers**, largest first:

- **The phiRS padding** (−62 k per slot, −124 k per node). Only this one is quantified. It gives
  2,006,266 per node, 1.045×.
- **Templating the skeleton's sparse remainder** (6,169 rows per slot): about −110 k of R per slot.
  Each sparse form costs R 3 rows plus β̃/α̃ materialisation.
- **The instance layout as arithmetic progressions per key**, so that `Σ_i h₁h₂` is a closed
  form: about −20 k of R.
- **The skeleton's alignment padding.**

## 2. `walkAB`: `A₀` and `B₀` are dense

I wrote the walk template (`FRVIRTplWalk`). It runs the BLAKE2s gadgets with forms held as sorted
position lists (`sOps`), proves `setbits` linear, and uses `sim_compressW` twice. Its theorem
`tplWalkAB_ok` is proved: the template computes `walkImpl`.

Every executable that imports it hangs at start, because the closed term `walkRun` expands every
gate's form. The cause is measured in `logs/S-E9/walk-nnz.log` (popcounts of the builder's forms):

- **nnz(A₀) = 51,726,185** and **nnz(B₀) = 35,684,622** over the 14,720 gates;
- up to 7,358 terms in one row.

A.11's "lincheck-replay class" (one row per product, with `A₀`'s row as the linear form) therefore
has 87.4 M entries. That cannot be held as `Circ.Row`s, nor checked by the plan's `eqL`. The same
density rules out R's walk u-rows.

**For the orchestrator**, the options are:

- **(a)** a symbolic M-row family: a lincheck block whose entries are `A₀`/`B₀` implicitly, with
  `nodeIRows`, the dump and P2 all knowing it. `evalM` would evaluate it by the walk (the fused
  walk of item 2);
- **(b)** materialise the gadget DAG, one linear row per XOR: about 90 k rows per slot, and R
  replays it at the same size. This changes `FRBlake2sGeneric`, because `GOps.xor` is pure.

(b) is what the rows table in §1 assumes. The module is parked in
`logs/S-E9/attic/FRVIRTplWalk.lean.txt`, and its wiring is reverted.

## 3. What was built (code lines, core `loc.py`, HEAD → now)

| Module | Code | Change |
|---|---|---|
| `FRNodeLayout` | 160 → 191 | `wmSlot = 146`; `hEnd = 47,594` in `regions_fit`. **The A.6 map in one place:** `wmB`, `mirOff` (`x` 0, `j` 399, `end9` 400, `end41lo/hi` 467, `l` 533, `r0` 549, `r31` 565), `mirN`, `mirSources = 581`, `mirBlock σ g = wmB σ + g/4`, `mirPos g s = 256(g mod 4) + s`, `mirBit`, `mirElem`. Lemmas: `mirElem_bit`, `mir_sources`, `mir_disjoint`, `mir_fits` (inside the slot's 146 blocks, past both WOTS runs, below `hEnd ≤ lBase`), `mirPos_lt` (< 1024). Controls. `mRowModel` (§3a). |
| `FRNodeMirror` (new) | 23 | `NodeT.wmB_eq`, `fam_mir` (each family's source is `off_f + t`; `j` is 399), `fam_n`, `mirB_eq`, `mpos_eq`, `mir_in_wm`. **S-C's `wmB`/`mirB`/`mpos`/`fam` are the layout's map.** |
| `FRVIRTplMask` (new) | 191 | `tplShiftMask`, **`tplShiftMask_ok`** (the gates give `NodeI.shiftMaskI`), helpers (`tblG_ent`, `cT_ev`, `cR_ev`, `tabs_a_big`, …), controls |
| `FRVIRCompile` | 781 → 845 | **`muxEl`**: a `packFK` whose kind lists have one length but differ is compiled as three selector products per differing element. `muxEl_pos`/`muxEl_neg`; the `packFK` case of **`opOut_sound`** extended. Controls `muxEl_rows_diff`/`_same`. |
| `FRVIRTplExt` | 330 → 362 | `tplOf`/`tplExt` cases for `.shiftMask`; **`ImplT.shiftMask`** (a new field; `implCWith_implT` in S-F2's module still proves it, unchanged); `outSlots_three`; `tplExt_ok`'s `shiftMask` case |
| `FRVIRTplCore` | 188 → 189 | `TKey.shiftMask` |

### 3a. `mRowModel`

Changes 21's ratified figures, with the measured layout: 436,092 + 45,604 + 65,536 + 100 + 47,680
+ 16,000 + 15,000 + 259,000 = **885,012 per slot**. `mRows_le` holds at 1.18×, and
`usedBlocks_le` holds (61,547 blocks).

These figures understate R and `walkAB` (§1). They are the ratified model, and I encoded them
because a theorem cannot carry a model that does not fit. S-E9's measured-estimate figure is §1's
1,065,133.

**Statements.** None changed. `implC_meets`, `acc_eq` and `node_m_sound` build with their HEAD
statements.

## 4. What is still imported (`logs/S-E9/impstat-3.log`, slot 0)

**Totals:** 27,353 import registers, 74 foreign flags (3 `assertEq`, 71 `assertZero`), 2,280
template instances, 1,753 auxiliary imports. The skeleton has 114,256 rows.

**Imports** (registers; the trace and L cells are H/L cells, bound by the pack map later):

- `piDigest` 7,555; `askNode` 7,552; `bitOf` 7,552; `piElem` 1,050; `piDigestAt` 871; `askCol`
  871; `piElemK` 355; `askSqueeze` 297; `chF` 279; `askAbsorb` 170; `chK` 29; `input` 3;
  `kindSel` 3; `hashStmt` 1; `askSeed` 1;
- **structured ops:**
  - `tensorW` 745;
  - `eqPt` 3, `slotW` 3, `shiftEq` 1, `shiftTarget` 1, `shiftMask` 3: **untracked operand.**
    `finSh`'s `packFK (fun κ => co.take (κ.m − 14))` has lengths 18 for L32 and 16 for P30/N30;
  - `targetS` 1, `linkWAll` 1, `rsWeight` 1, `walkAB` 2: no template yet;
  - `evalM` 3, `evalL` 3: the replay.

**Request (S-0, `FRVIRFinals.finSh`):** give `τ` one length for every kind. For example, pad P30
and N30 to 18 coordinates with the constant 0, and read the first 16 where `ptA 16` does. That
makes `eqPt`/`shiftEq` see the padded point, so their kind semantics must be restated. The
alternative is a compiler `af` slot of kind-dependent length, which `RepS` cannot express.

## 5. The dump (`logs/S-E9/nodedump/`, 255 MB; `nodedump.sha256`)

Produced by `probe/NodeDumpT.lean`, which now also writes `wm.txt` (`nodedump-run.log`, 35 s).

| | per slot |
|---|---|
| indexed rows (non-padding) | 340,745 |
| rows in the aligned layout | 436,092 |
| template instances | 2,280 |
| import registers | 27,353 |
| auxiliary imports | 1,753 |
| foreign flags | 74 |

- **Node: 872,184 of `2^21` M rows used (measured).**
- Plan: keys 80; pieces 5,058 per slot; `planOf` 12.8 s (`e5eval-2.log`).

**Blocks:** H ends at 47,594, L at 47,616–47,740, M at 49,152. Slot 1's last M row is element
1,484,668, i.e. block 49,152 + 11,599. **Used: 60,751 of 65,536 (measured).** The model
(`usedBlocks_le`) gives 61,547. With S-E9's sizes, M overflows (§1).

## 6. V (N30, S-E8's method: `vtime v N 21`, one idle core)

| Run | best | median |
|---|---|---|
| `vtime-N-1` | 207.85 ms | 218.92 ms |
| `vtime-N-2` | **207.22 ms** | 214.85 ms |
| `vtime-N-3` | 210.76 ms | 217.23 ms |

- `traceDigestF` read 13.4–13.7 ms, so the core was quiet.
- Per op (`prof-N-1.log`): `evalM` 100.4 ms (57.6 at INT-3); `walkAB` 8.9; `maskRows` 2.3;
  `shiftMask` 0.47.
- **Cause:** `maskRows` became a template instance (§4). Its 2^14 rows are evaluated in 256 chunks
  with 16,100 own inputs (`evalMT` 56 → 101.6 ms, `e5eval-2.log`). `shiftMask`'s instance is
  cheap.
- **Fix (not done):** an evaluator input kind for "own input = one cell at a per-chunk aligned
  shift". Its value is one `hfac` per chunk instead of 64 `glVal`s.
- **Projection** (S-E8's additions without `linkWAll`, which is in V already): 207.2 + 3 + 5 + 16
  = **≈ 231 ms**, under the 251 ms kill line. The walk DAG template's evaluation is not counted;
  it adds an estimated 5–10 ms, so ≈ 240 ms.
- The 39 ms can be returned by reverting `muxEl`'s branch of `opOut`. `maskRows` then goes back to
  a foreign op.
- **The projection the brief cited (≈ 195 ms) is no longer the right base.**

## 7. Checks

- **Build:** `lake build FR FRNodeMirror` is green, 2,376 jobs (`logs/S-E9/build-FR.log`).
- **Axioms** (`logs/S-E9/axioms.log`, 33 names): `acc_eq`, `implC_meets`, `implCWith_meets`,
  `implCWith_implT`, `tplExt_ok`, `compileT_sound`, `opOut_sound`, `compile_sound`,
  `node_m_sound`, `tplShiftMask_ok`, `outSlots_three`, `evalMT_eq`, `regions_fit`, `mRows_le`,
  `usedBlocks_le`, the mirror lemmas and the controls. They use only `propext`,
  `Classical.choice` and `Quot.sound`.
- **Source rule:** 154 files, 0 findings (`source-rule.log`).
- **Sequential profiles** (`-DElab.async=false --profile`, one core; `profile-<module>.log`):

  | Module | wall | type checking | tactics |
  |---|---|---|---|
  | `FRNodeLayout` | 9.3 s | 0.65 s | 0.61 s |
  | `FRNodeMirror` | 7.2 s | 0.15 s | 0.24 s |
  | `FRVIRCompile` | 37.0 s | 1.2 s | 9.5 s |
  | `FRVIRTplMask` | 9.7 s | 0.34 s | 1.7 s |
  | `FRVIRTplExt` | 9.3 s | 0.19 s | 1.2 s |
  | `FRVerifierImpl` | 6.0 s | 0.005 s | 0.03 s |

**Controls**

| Definition | (+) | (−) |
|---|---|---|
| mirror map | `mir_controls`: blocks 47,294 and 47,585, a position, an element | `mir_control_neg`: 3.13's element `2(off_f+t)` is not the pinned one; the pinned one is element 0 of block `+100` |
| `muxEl` | `muxEl_rows_diff`: differing registers emit 3 rows | `muxEl_rows_same`: equal registers emit none |
| `tplShiftMask` | `tplShiftMask_ok` (no hypotheses beyond the gate equations and the inputs); `tplShiftMask_outs`; `mPts_link` | `mPts_neg`: the unmasked ranges of `N` blocks per chain are not the template's |
| `FRNodeMirror` | the agreement lemmas, all without hypotheses | — |

## 8. Deviations and open questions (for the orchestrator)

1. **Item 1 is sized, not built.**
   - R with `replay_sound` is a multi-thousand-line formalisation: the R circuit generated from
     the plan, its MLE per block class, the self-referential plan from sizes. The measurements
     show it does not fit as modelled.
   - The design that fits best (R1s) needs:
     - the slot symmetry (true now: `rstat-sym.log`);
     - a ruling on the walk (§2);
     - a lever.
   - Requested: a ruling, then a stage for R alone.
2. **`walkAB` (§2): the blueprint's lincheck-replay class is not materialisable.** Choose (a) or (b).
3. **`τ`'s kind-dependent length** (§4) keeps `eqPt`/`slotW`/`shiftEq`/`shiftTarget`/`shiftMask` as
   imports. It is S-0's to change.
4. **V +39 ms** from binding `maskRows` (§6): keep it and optimise the evaluator, or revert.
5. **`planOf` is 12.8 s.** It is computed once per verifier process. If the runner counts process
   time, this is far over budget; S-E5/S-E6's 7.3 s had the same issue. Is the plan expected to be
   precomputed?
6. **`FR.lean`** should import `FRNodeMirror`. `FRVIRTplMask` is already in `FR`'s closure, through
   `FRVIRTplExt`.
7. **The blueprint** (§10 changes 21 (D), A.11) should replace "R ≈ 259 k" and "walks 65.5 k" with
   §1's figures, and state the density of `A₀`/`B₀`.
8. **Not done** (in order, for the next S-E stage):
   - the `walkAB` ruling, then its template and the fused walk (item 2);
   - `tplTargetSNode`, `tplLinkWAll`: both kind-selected, so gated by `s_N`, mirroring
     `targetSNodeI`/`linkWAllI` and `0`;
   - `rsWeight`: kind-dependent point lists of different lengths, so the same `packFK` issue;
   - `shiftTarget`: `bnd`'s 512 bits as auxiliary cells, bound by Booleanity and recomposition
     rows;
   - the 745 `tensorW` (a zero-padded `keep`);
   - R.

## For P2

- **Dump format** (`logs/S-E9/nodedump/`; S-E3's format, plus `wm.txt`):
  - `mrows-σ.txt`: `global row | A | B | C`, each form `cell:coef` with `coef` 16 bytes hex LE. Empty
    rows are alignment padding.
  - `mregs-σ.txt`: `register | imp|- | type | one form per F component`. **The register map:**
    import registers are the cells P2 writes from the native run; every other register is
    determined by the rows.
  - `groups-σ.txt`: per template key, the row base, cell base, cell bits, row bits, rows per
    instance and instances. Instance `i`'s rows are at `off + rowBase + i·2^rbits + j`, its locals
    at `cellBase + i·2^cbits + k`.
  - `maux-σ.txt`: the auxiliary imports (`dotKF` column cells, `tensorW`'s bits of `j`).
  - `lrows.txt`, `wots.txt`.
- **New in this dump:**
  - `shiftMask n m` and `maskRows` keys. `maskRows`' `kindW` is the muxed pack: per differing
    element, the three rows `c_κ = sel_κ · x_κ` on fresh cells `3i … 3i+2` of the op, and the
    element is `c_L + c_P + c_N`.
  - The `shiftMask` instance is laid out but still imported, because its operand is untracked;
    P2 writes its 3 output cells from `shiftMaskI`.
- **The mirror map (`wm.txt`; `Layout.mirBlock`/`mirPos`, = S-C's `mirB`/`mpos`):**
  - mirror source `g` of slot `σ` is block `47,294 + 146σ + ⌊g/4⌋`, bits `256·(g mod 4) + s`
    (`s < 256`);
  - the bit of `z` is `block·2^14 + position`; the F element is `block·128 + 2(g mod 4) + ⌊s/128⌋`;
  - families with `(n, off, len, mbo, src(t), mir(t))` are listed in full: `x` 0 … 398, `j` 399 (one
    source for 400 links), `end9` 400 … 466, `end41lo`/`end41hi` 467 … 532 (one shared source, mbo 0
    and 184), `l` 533 …, `r0` 549 …, `r31` 565 … 580;
  - **sources 0 … 580 of 584 per slot.** The `WM` blocks are kind `free`.
- **Unchanged from INT-3:** `items`, `piSize`, the H layout below `wmBase`, L.
