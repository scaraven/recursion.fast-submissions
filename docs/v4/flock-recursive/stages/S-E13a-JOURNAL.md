# S-E13a (track L-circ): JOURNAL — the pack map, `input`, `wf`, the kind tie (S-N2's `Gap4`)

Base: HEAD `75eff21` (S-N2). Build tree `logs/fr-build-SE13a`: a copy of `logs/fr-build-SN2` (itself a
copy of `fr-build-SE12f` with the same probes `LayDump4`, `NodeDump4`, `Plan4T`, `VTime4`,
`PlanForm4`, `ProtoDump`), against `logs/org20`; snapshot of HEAD by `snap.sh`, my modules symlinked
(`MINE.txt`). Logs in `logs/S-E13a/`. 16G scope and `timeout` on every lake/lean command. No
sub-agents, no commits.

## 0. Allocations (for S-E13b; written first)

**Rows.** Every new M row of this track sits in a verifier slot's **link region**, which grows from
the region's last 8 rows to its last **`2^15` rows**: slot `σ`'s link rows are indexed from
`σ·2^20 + 2^20 − 2^15` on, consecutively, in this order:

| Part | Owner | Rows per slot | Where defined |
|---|---|---|---|
| the S-E12c link rows (`one′`, copies, one-hot, activity) | S-E12c | 7–8 | `FRNodeRows4.linkRowsB4` (renamed from `linkRows4`; content unchanged) |
| **the pack rows** (this track): the kind tie, the stream's tag and length words | S-E13a | ≤ 8,906 | `FRNodeRows4Pack.packRows4` |
| **free for S-E13b** (WOTS mux, `aggChk`, `aggPad`) | S-E13b | ≤ 2^15 − 8,914 = 23,854 | proposal: append a list `extRows4 κ σ` after `packRows4` in `linkRows4` |

`linkRows4 κ σ = linkRowsB4 κ σ ++ packRows4 κ σ` (S-N2's `linkRows_hold` gives every row of it,
unchanged). `InSlot`/`ProtoFit` now keep the prototypes' rows below the link region
(`p.1 + 2^15 < π·2^20 + 2^20`). The plan evaluates the link region with the split eq tables
(`splitE`, one product per entry), not `gN` (48 products per entry).

**Cells.** The pack rows add **no new cells**: they are linear rows between existing H stream cells,
M's `one`, and the slot's selector copies.

**Proposal to S-E13b:** if you need rows in M, append them to the same link region of the slot that
owns them (one `List Row` per slot after `packRows4`), so the index map, `hfit4` and the plan's
evaluation stay one mechanism. If you need a different region, say so here and I will adapt.

## 1. Design note: where each import class lives, and how it can be bound

Census per prototype (S-N2 §2, from `logs/S-E12f/nodedump`): 26,638 (node) / 26,655 (segment)
import registers, 2,498 auxiliary imports, 12 / 79 foreign flags, the run's existence, `stmtOk4`.

**Facts the design rests on (checked in the sources):**
- **Pack (A.7).** An H element (cell `e`) is 16 stream bytes; byte `r` of the element is the 8 bits
  `8r … 8r+7` of its `bitF` pack (`unpack`). A *linear* row over cells can pin or equate **whole
  elements** only. Pinning a sub-element byte range, or equating byte ranges at different offsets
  mod 16, is GF(2)-linear but not F-linear: it needs the element's bits in L (128 bit-elements and
  one linear row per element) or Frobenius rows (≈ 128 per element).
- **Alignment of one trace** (`items_aligned`, `itemsOf seq4`): the stream `0x54 ‖ traceBytes tr`
  starts every item after the seed at a 16-aligned offset; every query is `tag(8) ‖ payload`, the
  payload and the answer are 16-aligned; the seed's element 0 is `0x54 ‖ enc64 119 ‖ "FRSEED0"`.
  So for a trace at stream offset 1, **every query payload, every answer and every item's length
  word + tag** is whole H elements.
- **Alignment of an aggregate (`0x54 ‖ tr₁ ‖ … ‖ tr_k`).** `|traceBytes tr| = segB − 1 = 1,482,751
  ≡ 15 (mod 16)`. Segment `i` starts at `1 + i·1,482,751 ≡ 1 − i (mod 16)`: **for `i ≥ 1` every
  field of segment `i` straddles two H elements** (shift `16 − i` bytes). This is S-H2's observation
  (`S-H2-RESULT.md` §7 item 2(e)) seen from the circuit.
- **The proof bytes** a slot's program reads are `pf (trace)` (S-N2's reader). With `pf` = A.5's
  `reassemble`, rows 0–16 of A.3 are positional copies of query payload bytes (aligned stream
  elements of the slot's segment), row 17 (siblings) is the node query's half *not* at bit `h` of the
  position index (a mux by an index bit).
- **The cap reads** (`piDigestAt 0 capO k`, 871 per slot): the cap entry at a **dynamic** index
  `k = j >> sib` (a register: the high bits of the position index). Its value is π's digest at offset
  `capO + 32k`, i.e. a cap-absorb payload element chosen by the witness.

**Per class** (per slot; "aligned" = the previous node's slot, and sub-slot 0 of each aggregate):

| Class | Count | Value lives in | Binding | Rows / cells | Status |
|---|---|---|---|---|---|
| oracle answers (`askSeed/Absorb/Squeeze/Node/Col`) | 8,905 digests = 17,810 F halves | the item's answer: 2 aligned H elements of the slot's stream | linear row `M_imp − H = 0` per half (an alias is not possible under the prototype move: the H cell differs per slot by a non-region shift) | 17,810 rows, 0 cells | aligned slots: buildable; sub-slots `i ≥ 1`: **blocked (B1)** |
| proof fields `piElem` / `piDigest` / `piElemK` | 7,555 + 1,068 + 355 → ≈ 10.4k F elements | `pf tr`'s bytes = query payload elements (A.5 rows 0–16) | linear rows to the payload element, given `pf`'s positional spec (a hypothesis on `pf`, S-H4's `reassemble`) | ≈ 10.4k rows | aligned: buildable once `pf`'s spec is fixed; `i ≥ 1`: **B1** |
| sibling digests (row 17, inside `piDigest`) | (part of the above) | the node query's half at `¬bit h` | 2 product rows per half (mux by the L index bit) | 4 rows per sibling | as above |
| **cap reads `piDigestAt`** | 871 digests | the cap entry at a witness index `k` | **no linear binding**: a mux over the cap (`2^9` entries at level 0) is ≈ 3·2^c rows per read, ≈ 0.8 M rows per slot | — | **blocked (B2)** |
| answer bits `bitOf` | 7,552 (node) / 7,570 (segment) | bits of P2's squeeze answers (H bits) | L bit-elements (A.7's position bits, Booleanity in `lRows4`), each squeeze half tied to **all** its 128 L bits by one linear row `H = Σ β_j b_j`; then `M_imp = L_bit` linear rows (or the compiled `bitOf` aliased to L) | ≈ 60 wide rows + 7.6k rows; L bits ≤ 7,552 + unused bits of the same halves (fits the stride's 7.8k spare) | design needed (the L layout must be the squeeze halves' bits in order) |
| challenge conversions `chF`, `chK` | 289 + 29 | a squeeze answer's half (`chF a c` = half `c`), or both halves (`chK`) | linear rows to the answer cells | 289 + 58 rows | aligned: buildable |
| `input` | 4 / 3 | `vk`: public cells `seedC σ 0/1` (pinned by `PubCells4`); `c`: the previous node's `c₁` (public, `stC 0`), a segment's `c` = `leafStmt eᵢ nᵢ` | `vk`, `c₁`: linear rows to the public cells (or S-E3 §9's alias in `Params`); a segment's `c`: the slot's `hashStmt` blocks (`hashA` `h_out`, its message tied to the stmt payload: §4.2's gated product rows) | 2 rows per `input`; ≈ 10 rows per slot for a segment's `c` | `vk`/`c₁` buildable for every slot; a segment's `c` needs the stmt payload (B1 for `i ≥ 1`) |
| replay ops (`evalM`, `evalL`, `targetS`, `shiftTarget`, `linkWAll`, `rsWeight`) | 10 | the child's matrices etc. | templates / `R` (A.11) | 240 k (`R`) + … (in `mRowModel4`) | other L-circ items |
| auxiliary imports (`bits 20`, `felems 16/64`) | 2,498 | `tensorW`'s index bits (L), `dotKF`'s column words (proof fields: column payloads) | L bits / linear rows to payload elements | ≈ 2.5k rows | with the classes above |
| foreign flags | 12 / 79 | ops' side conditions (templates' `flagOf`) | per op, from its template | — | other L-circ items |
| the run on the trace (`exec … = some (s, [])`) | 1 | the stream's queries must equal the queries the program computes | needs: the length words and tags (**`wf`**, this pass), the payloads = `pf`'s bytes (by `reassemble`), each query's state = the previous answer (H-to-H element equalities per item), the node queries' halves = (the previous answer, the sibling) per the index bit (mux rows); then an induction over the program's ops | ≈ 9k + 2·8.9k rows | needs B1, B2 and `pf`'s spec |
| `stmtOk4` | 1 | the statement fact | the `hashStmt` blocks | — | with `input` |

**Row cost against `N_M`.** A fully bound aligned slot adds ≈ 17.8k (answers) + 10.4k (fields) +
7.6k (bits) + 0.35k (challenges) + 9k (`wf`) + 17.8k (state/node links) ≈ **63k rows** per slot,
≈ 6 % of a `2^20` region. With the previous-node slot's model at 948,182 rows this is 1,011k:
**1.037×**, inside the region but tight. The cap reads (B2) as a mux would not fit (≈ 0.8 M).

**Cost against V.** Every pack row has irregular H cells, so the plan cannot reuse the prototype's
value (the copy identity needs every cell in the region). Each slot's pack rows are evaluated on
their own, one product per entry with split eq tables (`splitE`). This pass measures the per-row
cost on the `wf` rows (§3), which calibrates the full pack map.

**The plan time** (≤ 2 s at process start) is unaffected: the pack rows are closed constants per
kind (no compile pass).

### Blockers (for the orchestrator)

- **B1 — the aggregate's segments `i ≥ 1` are unaligned.** No F-linear row can bind any field of
  sub-slot `i ≥ 1` to its stream. That covers its answers, proof fields, length words and kind byte
  (`kindS` at `i ≥ 1`, `wf` at `i ≥ 1`). **Proposed remedy (R-A′):** `V_A` asks one fixed spacer
  query between consecutive segments, `absorbQ 0³² 0⁴⁹`. This is a 129-byte item, `≡ 1 (mod 64)`.
  - Segment `i` then starts at `1 + i·1,482,880 = 1 + i·64·23,170`: **every segment is aligned**, and
    sub-slot `i`'s stream is sub-slot 0's shifted by exactly `23,170·i` blocks.
  - Bonus: `aggB k = 1,482,880 k − 128 = 64·(23,170 k − 2)`. The aggregate stream fills whole
    blocks for every `k`, so R-4-m2's zero padding of the last block disappears. Its counter and
    final flag stay `k`-gated.
  - Cost: `k − 1` oracle queries and `+129(k − 1)` stream bytes (`+2` blocks per added segment).
  - Owners: `FRAgg` (`V_A`), the reader and `aggTr` (`FRNodeCircuit4`, `FRNodeRead4`), and the
    layout (`aggL`, `aggChainLen`). The prover writes the spacer.
  - The alternative (R-B: pad `seq4` itself to `≡ 0 mod 64`) changes every segment proof, R4 and P4.
- **B2 — the 871 cap reads per slot are dynamic lookups.** No linear or small product binding
  exists. Options:
  - (a) Merkle paths to a single root (cap size 1). `seq4` changes: `+9/+8/+8/+8/+7` node queries per
    position, and the caps' 45 KB shrink to 160 B.
  - (b) A lookup argument in the PIOP (a new phase).
  - (c) A mux at ≈ 3·2^c rows per read (≈ 0.8 M rows per slot), which does not fit.

  The blueprint's A.11 ("trace cells bound by the digest chain and `cap_binding`, no rows")
  assumed the imported cells *are* H cells. That is not true of the compiled prototypes (fresh M
  import cells, moved per slot), and it cannot be true for a witness-indexed read.
- **B3 — `pf`.** Binding proof fields needs `pf`'s positional spec (A.5). This pass states the one
  fact it needs as a hypothesis, `PfHdr pf` (byte 0 of `pf tr` is byte 71 of the seed query), which
  A.5's `reassemble` meets by definition (`hdr := payload₀[64…111]`). The full spec is S-H4's.
- **B4 — the run's existence.** `SlotImp` asks for `exec … = some (s, [])` on the read trace. Its
  proof is an induction over the 106k ops with the bound cells; it needs B1–B3 and the per-item
  state/node links. It is a new theorem about the compiled programs, not a row.

**What this pass builds** (the parts that B1–B4 do not block):
1. The link region of `2^15` rows, with the plan's split-table evaluation of it.
2. **The kind tie** for every slot whose stream is aligned. The row is `one·(H_e5 − Σ_ι K_ι s′_ι) = 0`,
   where `H_e5` is stream element 5, i.e. `hdr[0…15]`, and `K_ι` is exactly the program's seed
   constant (`seedOpsG`). Since `hdr[0…15]` is a whole element and a constant per kind, the tie is
   one linear row. It discharges **`Gap4.kindN` in full** and `Gap4.kindS` at `i = 0`.
3. **`wf`** for every aligned segment. One row per item pins the element at the item's offset to
   `enc64 |q| ‖ tag` (item 0: `0x54 ‖ enc64 119 ‖ "FRSEED0"`), 8,905 rows per stream. This
   discharges `Gap4.wf` in full for a previous node, and for an aggregate the tag and segment 0's
   words.
4. A reduced residual `Gap4R` (`Gap4` minus what the rows give), `gap4_of_rows`, and
   `ks_rev4GR`/`certificate_rev4GR` on `ks_rev4GH` with `hGap` replaced by `hGapR` and `PfHdr pf`.

## 2. Log

1. **Build trees.** The build tree is a copy of `fr-build-SN2` (`cp -a`), with `snap.sh` at HEAD. The
   baseline build of `FRNodeSound4Ctrl` is green: 2,538 jobs. For A/B timing,
   `logs/fr-build-SE13a-base` is a second copy at HEAD's sources (no MINE).
2. **`FRNodeRows4Pack`** (new) holds the data:
   - `sCell`, `itemTag`, `winB`/`winFB`/`winF`, `wfData`, the closed `wfSeg`;
   - the rows `pinRow`, `wfRows`, `kConst`, `kindRow`;
   - the facts `pinRow_holds`, `kindRow_holds`, `wfSeg_length`, `wfSeg_lt`;
   - `kConst_byte`, by `decide` over the 6 constants;
   - the controls `pinRow_ctl`, `kConst_ne`, `winB_ctl`.
3. **`FRNodeRows4`.**
   - S-E12c's `linkRows4` is renamed `linkRowsB4`, content unchanged.
   - New: `packB` (the aligned slots), `packHead4` (the kind tie), `packWf4` (the pins), and
     `packRows4 = packHead4 ++ packWf4`.
   - `linkRows4 = linkRowsB4 ++ packRows4`. `linkN = 2^15`; `linkIRows4` now starts at the link
     region.
   - `idxInB`/`InSlot` keep the prototypes below the link region. New lemmas:
     `linkRowsB4_length`, `packRows4_length_le`, `linkRows4_length_le`.
   - S-N2's modules compile unchanged: `linkRows_hold` only uses `linkIRows4`'s
     `zipIdx.map (f, ·.1)` shape and membership.
4. **`FRNodeRows4Fit`.**
   - New lemmas: `chBase_cLen_le`, `sCell_lt` (H stream cells are below M), `aggChild_lt`,
     `packRows4_cells`.
   - `slot_mem` takes link indices `< linkN` and the pack rows' cells. `slot_nodup` uses
     `linkN`.
   - In `link_facts`, membership now goes through `List.mem_append_left` over `linkRowsB4`.
5. **`FRNodeRows4Plan`.**
   - `copy_row` and `pieceInB` use `linkN`. `rows3_append` moved up.
   - The first `linkV4` (the whole link region by `grows`/`growsVal3`) cost N2 +31 ms.
   - The final `linkV4` keeps `growsVal3` for the head (≤ 9 rows) and evaluates the pins with
     **`wfSum`**: per row, one row factor and one cell factor through the split tables.
   - Proofs: `wfSum_eq` (by induction) and `linkV4_eq`. In `evalMT4`, `slotV4` gets the tables
     `ltbOf` once per point. `evalMT4_eq` is re-proved, statement unchanged.
6. **`FRNodeRows4Model`.** New: `packRows4N = 2·8,906`. `mRows4_le` now checks each slot's model
   below the link region (`+ linkN`). `mRowModel4_eq`: N2 2,173,012, N4 3,374,446, N8 4,829,124.
7. **`FRNodeRows4PackSound`** (new).
   - The H bridge: `toBytes_bit`, `bitsB4_cell`, `readByte_cell`, `chainBytes4_elem`,
     `stream_ge`, `seg0_elem`.
   - `seq4`'s alignment from shapes: `shAl`, `sh_al`, `phasesOf_al` (one `decide +kernel` over
     shape parameters), `itemsOf_seq4_al`.
   - The pins: `AlAt`, `winF_word`, `wfAt_of_pins`, `wfData_lt80`, `wfSeg_lt80`, `wf0_of_pins`.
   - The kind byte: `PfHdr`, `byteAt_slotPf`, `kind_byte`, `kindRow_sel`.
   - The residual: `Gap4R`, `packRows_hold`, `pins_of`, `packB_prev`, `packB_sub`,
     **`gap4_of_rows`**, and the converse `gap4R_of_gap4`.
   - Controls `kindRow_ctl`, `pfHdr_ctl`. **`ks_rev4GR`**, `Resid4GR`, **`certificate_rev4GR`**.
8. **Runtime checks.**
   - `plan4t check` on the first (`grows`) version: N2's `evalMT4` equals the full sparse sum
     ("equal true"), `inR true` at the new bound.
   - `packt`: `linkV4` costs 5.2–5.9 ms per packed slot and `ltbOf` 3.8–4.0 ms.
   - `packi`: `wfData` took 195 ms when `winB` was rebuilt per byte, 22 ms after `winFB`. The
     process start is back at the base's.
9. **Dumps.** `nodedump4`, `planform4` and `protodump` into `logs/S-E13a/nodedump`. Every prototype
   file is byte-identical to S-E12f's. `node-N{2,4,8}.txt` now carry the pack rows; spot-checked
   (element 0 `54 77 00… "FRSEED0"`, item 1 `a8 00… "FRABS000"` at cell 262, the kind row at cell
   133).
10. **Final checks.**
    - `lake build FR FRNodeRows4PackSound FRNodeSound4Ctrl` (with the probes) is green: 4,913
      jobs, of which 2,554 are library jobs.
    - Axioms: 43 declarations, no `sorryAx`.
    - Source rule: 353 files, 0 findings.
    - Profiles as in the RESULT.
11. **The fold of S-E13b's rows** (the orchestrator's note, S-E13b RESULT §3/§7 item 1).
    - **Definitions.** The node rows are closed constants per kind (`xRowsN2/N4/N8`, `xRowsK`,
      `xRowsK_eq`, all `rfl`). Their cell check `xOkK` is also a closed constant, computed once
      per process like `ProtoFit`. `extRowsC κ σ` is slot 1's node rows, or the rejecting row
      `rejR` if the check fails.
    - `linkRows4 = linkRowsB4 ++ packRows4 ++ extRowsC` (left-associated, so S-E13b's `hfold` is
      `List.mem_append_right`).
    - **`hfit4`'s cell bound is structural.** In the true branch the check itself is the bound,
      with no kernel evaluation; the rejecting row's only cell is M's `one`. This avoids S-E13b's
      24 s per kind of `decide +kernel`.
    - `linkV4` gains a third part: the node rows via `growsVal3`, starting at index `head + wfLen`.
    - `wots_aggPad_of_rows` discharges `Gap4.wots`/`.aggPad` (`W4.gap4_wots_aggPad` when the
      check passes; a contradiction from the rejecting row otherwise). `Gap4R` drops both fields.
    - `mRowModel4` uses S-E13b's counts. `xOkK` is `true` for all three kinds
      (`packt-fold.log`).
12. **Final checks.**
    - `lake build FR FRNodeRows4PackSound FRNodeSound4Ctrl FRNodeRows4WotsCtrl` is green: 2,566
      jobs.
    - Axioms: 48 declarations, no `sorryAx`.
    - Source rule: 354 files, 0 findings.
    - The dumps are regenerated (`node-*.txt` only).
