# S-0′ RESULT: revision 4.1's shapes (segments, the aggregate leaf, N2/N4/N8)

- **Where:** worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive`.
- **Base:** HEAD `a3bc63a`, redirected at `9d75d0e` (blueprint 4.1). Pin `6d05d00`.
- **Build tree:** `logs/fr-build-S0p` (against `logs/org20`).
- **Logs:** `logs/S-0p/`. Journal: `S-0p-JOURNAL.md`.
- Nothing is committed.

The track first built revision 4.0's shapes (N4/N8 at `m = 32/33`, two item sequences). After the
coordinator's redirect it moved to **revision 4.1** (changes 26, B-12, B-13):
- `L30`/`L31`/`L32` segments;
- `N2`/`N4`/`N8` nodes at `m ≤ 32` with tight packing;
- **one** item sequence;
- level-0 rows as a parameter.

`FRSegment`, `FRAgg`, `pubStart`, `hdr_A`, `V_A` and the byte `L31 = 0x4B` are kept, so P2′'s
alignment stands. The 4.0 dumps are kept in `logs/S-0p/dump-4.0/` for reference.

## 0. The constraint that shapes this track

`Kind` (3 constructors) is case-split in 105 places outside S-0's modules, among them the forbidden
`FRSoundnessFr*` (e.g. `Kind.m_le : κ.m ≤ 32`), `FRX*` and `FRNodeRead*`. The same modules use the
exact values `items_length = 8891`, `piSize = 797904` and `chainLen = 23146`.

The IR's kind tables (`KC α = Kind → α`) are part of `Op`. The finals (`FRVIRFinals*`) hard-code
3.x sizes.

So, with `lake build FR` kept green, this track cannot:
- add the new kinds to `Kind`;
- change `items`, `phases`, `gen` or `V` in place.

**What was done instead:**
- Revision 4 is an **additive, kind-parametric layer**: six new modules in `FR.Rev4`.
- The 3.x constants are proved to be instances of it (`ladderOf_32`, `phasesOf_seq3`,
  `itemsOf_seq3`, `piSizeOf_seq3`).
- The 3.x `Kind`, `Vwith` and every 3.x proof stay unchanged.
- The new verifier is `V4with`. Its SNARK programs are parameters (`Vseg`, `Vnode`).
- **No existing statement changed.** The only edit to an existing file is six imports in `FR.lean`.

## 1. What was built (loc: `logs/S-0p/loc.txt`, core `scripts/loc.py`)

| Module | code / total | Content |
|---|---|---|
| `FRShape4` | 199 / 367 | Kinds (see below). `Dims`, `Seq` (with `ell0`), `Dims.seqR`, `seqOf`, `seq3_eq`, **`seq4`/`seq4_eq`**, `seg_fits`, `node_fits`. `ladderOfR ell0 m`, `ladderOf` (= `ladder32`/`ladder30` by `rfl`), `Seq.lv`/`lvK`, `ladder_sq_sib`, `seg_ladder_fits`, `node_ladder_fits`. `Sh`/`ChalK`, `phasesOf`, **`phasesOf_seq3`**, `itemsOf`, **`itemsOf_seq3 = items`**, `fieldSizeOf`, `piSizeOf`, **`piSizeOf_seq3 = piSize`**, `streamBytesOf`, `chainLenOf`. **`itemsOf_seq4_length = 8905`**, `fieldSizesOf_seq4`, **`piSizeOf_seq4 = 798,192`**, `streamBytesOf_seq4`, `chainLenOf_seq4` (`64 · 23,168`). **`qV4 = 36,000`**, `traces_le_qV`. `segHdr` (`segHdr_L32`), `nodeHdr`. |
| `FRSegment` | 81 / 168 | `SegStmt`, `SegHolds`, **`seg_sound`**, **`seg_complete`**, `segHolds_L32`, `ChainedTail`/`Chained`, `chainEnd_add`, **`segs_compose`**, `SegView`, `segView`, `segC`; controls. |
| `FRAgg` | 238 / 351 | `seqAll`, **`runSeq_bind_some`**, `runSeq_bind_of`, `runSeq_seqAll`, `seqAll_of_forall₂`; `aggHdr`, `aggSegs`, `chainOk`, `aggChecks`, `segProgs`, **`VAwith`**, `aggWit`; **`VA_sound`**, `SegSound`, **`VA_extract`**, **`VA_complete`**, `aggRest`, `aggChecks_eq`, `VA_reject_rest`, `VA_reject_stmt`, `aggRest_bad_n`; controls. |
| `FRVerifier4` | 135 / 215 | `PKind4`, `kindOf4`, `accWith4` (`qV4`), **`V4with Vseg Vnode`**, `accV4`, **`acc_eq4`**, `V4_bad`/`_agg`/`_node`/`_W`, `V4_W_sound`, **`V4_agg_extract`**, `V4_encode`, **`complete4`**; controls. |
| `FRNodeLayout4` | 45 / 106 | Per-node fields `blocks`, `cells`, `vslots`, `hUsed`, `lBase`, `nL`, `nM`, `mBase`, `oneCell`, `mSlot`, `tauCoords`, `sigmaCoords`; `aggChainLen_eq`, `hUsed_eq`, **`regions_fit`**, **`mSlots_fit`**, `coords_eq`, `sizes_neg`. |
| `FRVIR4` | 111 / 176 | `KindP`, `fieldOffOf`, `phaseOffOf`, `realRounds`, `seedOps4`, `stmtOps4`, `finalOps4`, `merkleOps4`, `posOps4`, **`genPhase4`**, `skeleton4`, **`gen4 S p fin`**, `genSeg`, `genNode`, `fieldOffs`. |
| **total** | **809 / 1,383** | 82 theorems |

**Kinds and bytes:**

| Kind | byte | `m` | notes |
|---|---|---|---|
| `L30` | `0x50` `'P'` | 30 | 3.x `P30`'s byte |
| `L31` | `0x4B` | 31 | as P2′ uses |
| `L32` | `0x4C` | 32 | |
| `N2` | `0x4D` `'M'` | 31 | 3 verifier slots, `N_L 2^16`, `N_M 2^22` |
| `N4` | `0x4E` | 32 | 5 verifier slots, `N_L 2^17`, `N_M 2^23` |
| `N8` | `0x4F` | 32 | 8 verifier slots, `N_L 2^17`, `N_M 2^23` |
| `A` | `0x41` | — | aggregate leaf |

`bytes_distinct` proves the bytes distinct from each other and from `0`/`1`.

## 2. Build, kernel, checks

- **Build:** `lake build FR` is green, 2,416 jobs (`logs/S-0p/build-FR.log`).
- **Axioms:** all 23 key theorems use only `propext`, `Classical.choice` and `Quot.sound`
  (`axioms.log`, `Axioms.lean`).
- **Source rule:** 191 files, 0 findings. No `sorry`, no `native_decide`.
- **Sequential profiles** (one core, `-DElab.async=false`; `prof-*.log`):

| Module | wall | kernel |
|---|---|---|
| FRShape4 | 27.9 s | 7.6 s |
| FRSegment | 6.9 s | 0.0 s |
| FRAgg | 34.6 s | 26.4 s |
| FRVerifier4 | 7.5 s | 0.1 s |
| FRNodeLayout4 | 14.1 s | 7.6 s |
| FRVIR4 | 11.7 s | 0.7 s |

  FRAgg's kernel time is its three byte-level controls (about 7.5 s each). This is a golf target: a
  list-level lemma for `aggSegs` of an assembled proof would remove it.
- **Kernel timeout found:** the first version of the controls evaluated BLAKE2s through `leafStmtF`
  in the kernel and hit a deterministic timeout after 7 min. The fix splits the statement check off
  (`aggChecks_eq`).

## 3. Items

### Segments (B-12)

- **Circuit content.** `SegHolds κ st z` requires:
  - `1 ≤ n ≤ cap κ = 2^(m−14)`;
  - Booleanity and the chain block's R1CS with its public target on blocks `i < n`;
  - `ChainLinks n z start h`.

  Blocks `≥ n` are free.
- **Soundness and completeness.** `seg_sound` is `leaf_sound` at `n`; `seg_complete` gives the
  honest table. `segHolds_L32` shows that 3.x's leaf is `L32` at `2^18`.
- **Composition.** `segs_compose` (`chainEnd` composes).
- **Controls:**
  - `seg_bad_n`: `n = 0` and `n = cap + 1` are rejected;
  - `seg_wrong_end`: no `GF(2)` table proves the one-step chain `0 → 0` (wrong start or end);
  - `seg_ctrl_pos`: the honest one-step segment is accepted;
  - `segs_compose_ctrl`: a broken link is not `ChainedTail`.
- **Program.** `genSeg κ fin` (see "For S-E12′").
- **`L29`** is not added. It would be one constructor (`m = 29`, cap `2^15`, ladder `sib`
  `[8, 7, 5, 3, 2]`), but P2 would also need an `m = 29` prover.

### The aggregate leaf `A` (B-11)

- **Format.** `π_A = 0x41 ‖ k ‖ 0^6 ‖ enc64 n ‖ e ‖ π₁ ‖ … ‖ π_k`.
  - Each `πᵢ` is a segment proof of `piSizeOf seq4 = 798,192` B.
  - `tr_A = tr₁ ‖ … ‖ tr_k`, with **one** signature.
- **`V_A`** (`VAwith`) first runs the checks of `aggChecks`:
  - `c = leafStmt e n`;
  - `1 ≤ k ≤ 4`;
  - `1 ≤ nᵢ ≤ cap κᵢ` for each segment;
  - `Σ nᵢ = n`;
  - `e_k = e`;
  - `s_{i+1} = e_i`, on raw bytes.

  It then runs the segment programs in sequence on `tr_A`, each against `cᵢ = leafStmt eᵢ nᵢ`.
  `A` has no SNARK of its own.
- **Soundness reduction.**
  - `VA_sound`: an accepting run splits the trace into accepting segment runs, and the checks hold.
  - `VA_extract`: with `SegSound`, an accepting run gives `aggWit π = some (s, n)` with
    `n ≤ chainCap` and `c = leafStmt (chainEnd s n) n`. This is `Rel`'s leaf clause.
  - `VA_complete`: the honest assembly is accepted.
- **Controls:**
  - `ctrlA_pos`: accepted;
  - `ctrlA_bad_sum` (wrong `n`): rejected;
  - `ctrlA_bad_start` (`s₂ ≠ e₁`): rejected;
  - `aggRest_bad_n` and `VA_reject_stmt`: rejections, proved generically.

### Nodes N2, N4, N8 (B-13)

- **Kinds:** see the table in §1.
- **One item sequence `seq4`.** It is 3.x's sequence with the node phases sized for
  `N_L = 2^17`, `N_M = 2^23` and `f`'s `2^25` cells:
  - Lr 17 rounds (Lr1: 9 squeezes), E2 23 rounds (E1: 12 squeezes), E4 25 rounds;
  - 14 more items than 3.x: 8,905 in all, 482 of them Fiat–Shamir;
  - `piSize` 798,192;
  - the stream is `64 · 23,168` bytes, so the 32-byte E4 end still aligns it;
  - `4 × 8,905 = 35,620 ≤ qV4`.
- **`hashStmt`.** Nodes use 3.x's node statement; segments use `leafStmt eᵢ nᵢ`.
- **Programs.** `genNode κ fin` and `genSeg κ fin`.
- **Dispatch.** `V4with`:
  - `'A'` → `V_A`;
  - node byte with `|π| = 798,192` → `Vnode κ`;
  - node byte with another size → reject, no query;
  - bare segment byte → reject;
  - anything else → `W`.
- **Theorems.** `acc_eq4`, `complete4` (`δ = 0`), `V4_W_sound`, `V4_agg_extract`.
- **Controls.** `ctrl4_W_leaf`, `ctrl4_bad_node_size`, `ctrl4_seg_top`, `ctrl4_bad_byte`, `ctrl4_agg`.
- **Layout.** `FRNodeLayout4` (see "For S-E12′").

### Dumps (`logs/S-0p/dump/`, `SHA256SUMS`; tool `logs/fr-build-S0p/dump/IRDump4.lean`)

| Kind | file | skeleton ops | registers | asks = items | items | piSize |
|---|---|---|---|---|---|---|
| L30 / L31 / L32 | `ops-L30.txt`, `ops-L31.txt`, `ops-L32.txt` | 62,048 | 53,360 | true | 8,905 | 798,192 |
| N2 / N4 / N8 | `ops-N2.txt`, `ops-N4.txt`, `ops-N8.txt` | 62,051 | 53,362 | true | 8,905 | 798,192 |
| A | (no program: `V_A` = segments in sequence) | — | — | — | `≤ 4 · 8,905` | `48 + k · 798,192` |

- Also in the directory: `items.json`, `summary.txt` (field sizes and offsets per kind), and the 3.x
  skeletons `ops3-L.txt`/`ops3-N.txt`.
- **Fidelity of the generator.** At 3.x's sequence (`seq3`), `gen4`'s `L32` skeleton equals 3.x's
  `L32` skeleton up to register renaming and absolute offsets: 61,942 aligned ops and 0 operand
  mismatches (`logs/S-0p/regmap-4.0-seq3.log`, `dump-4.0/`).
- The only 12 removed and 4 added lines are the intended changes:
  - no `kindSel`/`assertOneHot`;
  - no `n = 2^18` assert;
  - no inactive node `stmt` checks;
  - a final-padding check of length 0.
- At `seq4` the diff against 3.x also contains the node phases' extra rounds and the shifted caps
  offsets (`regmap-4.1-seq4.log`).
- These dumps are measurements, not kernel theorems.

## 4. Issues and the readings chosen

- **I-1 (4.0's "one sequence" against `m = 33`) is resolved by 4.1.** All kinds are at `m ≤ 32`
  and one sequence remains.
  - **The new point to note:** "L32's sequence" cannot be 3.x's byte for byte. 3.x sized its node
    phases for `N30` (`N_M = 2^21`, `f` `2^23`), and an `m = 32` node needs Lr 17, E2 23 and E4 25.
  - So a full-length `L32` segment carries 14 more dummy items and 288 more zero bytes in the E/Lr
    fields than HEAD's leaf.
  - **P2′'s byte-exactness at `n = 2^18` no longer holds against HEAD.** It must be re-baselined to
    `items.json`.
- **I-2. `pubStart` is the segment's position, checked by `V_A` on raw bytes.**
  - `hdr.pub` carries the start. The seed binds it, and the shift boundary pins block 0's `h_in` to
    it, as in 3.x. Nothing changes in the segment proof.
  - This answers P2′'s questions (c) and (d): `hdr` carries neither `n` nor `pubStart`.
  - Segment 1's start is the extracted witness.
- **I-3. B-13's "`τ`/`σ` 23 coordinates".**
  - `τ = log N_M` (22 / 23 / 23).
  - `σ = m − 7` (24 / 25 / 25): the coordinates of `f`'s cells.
- **I-4. `N_L` is unspecified in the blueprint.** Chosen: a stride of `2^14` per verifier slot,
  rounded up: `N2` gets `2^16`; `N4`/`N8` get `2^17`.
- **I-5. `A`'s chain is not 64-aligned.** `tr_A`'s chain has `1 + k · 1,482,751` bytes, which is
  `≡ 1 − k (mod 64)`. At `k = 2` and `k = 4` the last block needs the padding claim
  (`aggChainLen_eq`).
- **I-6.** `V_A` does not require `hdr_A`'s bytes 2–7 to be zero. This is harmless for soundness and
  is one line to add.
- **I-7. Level-0 rows are parametric** (`Seq.ell0`, `ladderOfR`). They stay 6 until S-D re-checks
  `pcsLevels_ok` at 5. Revision 3.1's ladder rule then gives the other levels, the final message
  and Pf.

## 5. For S-E12′

- **Programs.** `genNode κ fin`, `genSeg κ fin` (`FRVIR4`).
  - Fixed-kind, with constant `KC` tables.
  - Mode `.fixed .N30` for nodes and `.fixed .L32` for segments (`hashStmt`'s 3.x index).
  - Absolute addressing: `piField 0 (fieldOffOf seq4 f + o)`.
- **Muxes.** Slot 1 muxes `{N2, N4, N8}`; the sub-slots mux `{L30, L31, L32}`. They are the
  compiler's job. The kinds of a group share one op shape and differ only in constants (diff the
  dumps).
- **Finals to generalise over `Seq`** (owners S-0 / S-F / S-G):
  - `finZ`: `m − 13` and Z3 26;
  - `finSh`: `τ` of `m* − 14 = 18` and S2 28. **A segment's `bnd[4 …]` must be the bits of
    `nᵢ − 1` from `stmt` bytes 33–40.**
  - `finLr`: 17 rounds;
  - `finE`: `evalM(τ = logM, σ = m − 7)`, E2 23, E4 25 (`N2`: 24 real);
  - `finRS`/`finB′`;
  - `finP i`: `Seq.lvK`;
  - `finPf`: 7 rounds.
- **S-C's half of B-12.** `targetS`/`kindInd`/`shiftTarget` with a statement-dependent last block
  (free at `≥ nᵢ`). `SegHolds` is what they must deliver.
- **Layout** (`FRNodeLayout4`, blocks of `2^14`):

| | N2 | N4 | N8 |
|---|---|---|---|
| blocks / cells | `2^17` / `2^24` | `2^18` / `2^25` | `2^18` / `2^25` |
| H used | 70,955: prev 23,168 + `A(2)` 46,336 + 9 + 996 + 438 + 8 | 117,589: prev 23,168 + `A(4)` 92,672 + 15 + 996 + 730 + 8 | 187,540: 2 × `A(4)` + 24 + 996 + 1,168 + 8 |
| L | base 71,168, `2^16` el. (512 blocks) | 117,760, `2^17` (1,024) | 187,648, `2^17` |
| M | base 98,304, `2^22` cells, 3 of 4 slots | 196,608, `2^23`, 5 of 8 | 196,608, `2^23`, 8 of 8 |
| slack before M | 26,624 blocks | 77,824 | 7,936 (1.04×) |
| `τ` / `σ` | 22 / 24 | 23 / 25 | 23 / 25 |

- **`V_A` in the circuit.**
  - `A`'s one digest chain (I-5).
  - The links `s_{i+1} = e_i` as copies between segment `i+1`'s seed `hdr.pub` cells and segment
    `i`'s `stmt` `h` cells.
  - The range rows for `nᵢ` and `Σ nᵢ = n`.
  - **O-1:** `n` and `e` must come from `c`'s preimage (the `hashStmt` blocks), since `hdr_A` is in
    `π_A`, not in the trace.

## 6. For P2′

- **Segment proof** (798,192 B; field sizes and offsets in `summary.txt`):
  - `hdr = byte ‖ m ‖ 0^14 ‖ s`, where `s` is the chain start for segment 1 and the previous end
    after it;
  - `stmt = 0x4C ‖ h ‖ enc64 nᵢ ‖ 0^87`; the seed's `c = leafStmt h nᵢ`;
  - the item order is `items.json`. Against HEAD it adds 2 Lr2 rounds, 1 E1 squeeze, 2 E2 rounds and
    2 E4 rounds (all dummies: zero messages), and its fields Lr/E grow by 96 + 192 bytes.
- **`L30` / `L31` dummies inside the `m* = 32` sequence:**
  - squeezes `[21, 12, 9, 7, 6]` / `[23, 12, 9, 7, 6]`;
  - siblings `[9, 8, 6, 4, 3]` / `[10, 9, 7, 5, 4]`;
  - Z3 24 / 25 real rounds and S2 26 / 27;
  - final message `2^5` / `2^6` K elements, then zeros;
  - Merkle-node queries beyond the depth are `nodeQ i 0^32 0^32`.
- **Split rule.** Segments `1 … k−1` are `L32`. The remainder goes to `L30` (`≤ 2^16`), `L31`
  (`≤ 2^17`) or `L32`.
- **Aggregate.** As in §3. One `SIGN` covers `tr_A`, of at most 35,620 queries.
- **Node proof** (798,192 B):
  - `hdr = 0x4D | 0x4E | 0x4F ‖ 31 | 32 | 32 ‖ 0^14 ‖ vk`; `stmt` is the node `stmt`.
  - Real rounds per kind: `N2` has Z3 25, S2 27, Lr2 16, E2 22, E4 24 and a final of `2^6`, the rest
    dummies; `N4`/`N8` are real in every round.
- **Cell maps:** the layout table in §5.

## 7. Remaining work (handover, in order)

1. **Finals over `Seq`, and S-C's variable last block.** With them, `Vseg`/`Vnode :=
   runIR implC4 (genSeg/genNode κ fin4)`, and `implC4`'s `targetS`/`slotW`/`linkWAll` for the new
   kinds (S-F2/S-E12′).
2. **`SegSound` from S-G's per-segment soundness** (with its error); `aggWit` feeds S-H2n's leaf
   decoding.
3. **Migrate the 3.x users to `Rev4`** (S-G12′, S-H2n, S-I): `acc_eq4`, `complete4`,
   `V := V4with …`, `qV := qV4`. Then retire 3.x's `Kind`/`Vwith`.
4. Orchestrator rulings needed: I-1's re-baseline, I-2 … I-7, O-1.
5. Golf FRAgg's controls (§2).
