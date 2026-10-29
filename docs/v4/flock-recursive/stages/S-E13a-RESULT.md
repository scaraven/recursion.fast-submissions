# S-E13a (track L-circ): RESULT — the pack rows (kind tie, `wf`), the link region, the fold of S-E13b's rows

Base: HEAD `75eff21` (S-N2). S-E13b's 12 modules were untracked at the time; I used them as they
are in the worktree.

- **Build tree** `logs/fr-build-SE13a`: a copy of `fr-build-SN2`, itself a copy of `fr-build-SE12f`
  with the same probes, against `logs/org20`.
- **A/B timing tree** `logs/fr-build-SE13a-base`: HEAD's sources.
- **Records.** Logs are in `logs/S-E13a/`; the journal is `S-E13a-JOURNAL.md`, whose §1 is the
  design note.
- Every lake, lean and probe command ran in a 16G scope with `timeout`. There were no sub-agents
  and nothing is committed.

## Status

| Item | State |
|---|---|
| 1. Design note | **Done** (JOURNAL §0–§1). It gives, per import class, where the value lives, how it can be bound, and the cost. It also names **four blockers** (§1 below). |
| 2. Binding rows | **Partly.** The rows are in place: a slot's **link region** of `2^15` rows, the pack rows, and the fast evaluation. The pack map proper (answers, proof fields, bits, challenges, `input`) is **not built**: B1–B4 block it, or make it unsound or too slow for V. |
| 3. `wf` | **Done for the aligned segments.** A previous node is complete. For an aggregate, the tag and segment 0 are done. Segments `i ≥ 1` are blocked by B1. |
| 4. Kind tie | **`kindN` done in full.** `kindS` is done at each aggregate's first sub-slot. Sub-slots `i ≥ 1` are blocked by B1. |
| 5. Proofs | **Done for what the rows bind.** `gap4_of_rows : StmtN4 → PfHdr pf → Gap4R → Gap4`. `ks_rev4GR`/`certificate_rev4GR` are S-N2's `ks_rev4GH`/`certificate_rev4GH` with `hGap` replaced by `PfHdr pf` + `Gap4R`. `hfit4` (with `ProtoFit` at the new bound: `inR true` at run time) and `mRows4_le` are re-proved. |
| 6. Re-dump for P2 | **Done** (`logs/S-E13a/nodedump/`). Only `node-N{2,4,8}.txt` change. V(N4) is measured (§3). |
| Orchestrator's note: the fold of S-E13b's rows | **Done.** `Gap4.wots` and `.aggPad` are now theorems (`wots_aggPad_of_rows`). `hfit4`'s cell bound is structural, with no `decide`. `mRowModel4` uses S-E13b's counts. **`aggChk` (a)–(c) is not started** (§6, item 1). |

**`Gap4R`**, i.e. what is left of S-N2's `Gap4`:
- `imp`;
- `kindS` at sub-slots `i ≥ 1`;
- `wf` at segments `i ≥ 1`;
- `aggChk`.

`kindN`, `kindS` at `i = 0`, the streams' tags, segment 0's length words, `wots` and `aggPad` are
now proved from the rows.

**Checks:**
- `lake build FR FRNodeRows4PackSound FRNodeSound4Ctrl FRNodeRows4WotsCtrl` is green: 2,566 jobs
  (`logs/S-E13a/build-final.log`). S-N2's modules compile unchanged.
- **Axioms** (`logs/S-E13a/axioms.log`, `logs/fr-build-SE13a/ax/AxSE13a.lean`): 48 declarations,
  including `gap4_of_rows`, `ks_rev4GR`, `certificate_rev4GR`, `hfit4`, `evalMT4_eq`,
  `wots_aggPad_of_rows`, and S-N2's `resid4_of`/`ks_rev4GH` re-checked. Each uses only a subset of
  {`propext`, `Classical.choice`, `Quot.sound`}. None uses `sorryAx`.
- **Source rule:** 354 files, 0 findings (`logs/S-E13a/source-rule.log`).
- **`FR.lean`** (orchestrator): add `import FRNodeRows4PackSound`. It pulls in `FRNodeRows4Agg`
  and the rest of S-E13b's modules.

## 1. The blockers (the design note's findings, for the orchestrator)

- **B1 — an aggregate's segments `i ≥ 1` are unaligned.**
  - Why: `|traceBytes| = segB − 1 ≡ 15 (mod 16)`, so segment `i` starts at `1 + i·(segB − 1) ≡ 1 − i`.
    Every field of sub-slots `i ≥ 1` straddles two H elements. F-linear rows can bind only whole
    elements.
  - **Proposed remedy (R-A′):** `V_A` asks one fixed spacer query `absorbQ 0³² 0⁴⁹` (129 bytes,
    `≡ 1 mod 64`) between segments.
    - Every segment is then aligned.
    - Sub-slot `i`'s stream is sub-slot 0's shifted by `23,170·i` blocks, so the rows of sub-slot 0
      apply to it shifted.
    - `aggB k = 64·(23,170 k − 2)` fills whole blocks, so R-4-m2's zero padding goes away.
    - Owners: `FRAgg`, `aggTr`/the reader, `aggL`, the prover.
- **B2 — the 871 cap reads per slot (`piDigestAt 0 capO k`) are witness-indexed lookups.**
  - No linear or small product binding exists: a mux costs ≈ `3·2^9` rows per read, ≈ 0.8 M per slot.
  - Options:
    - (a) Merkle paths to a single root (`seq4` changes);
    - (b) a lookup argument in the PIOP;
    - (c) the mux, which does not fit.
  - A.11's "trace cells bound by the digest chain and `cap_binding`, no rows" assumed that the
    imported cells *are* H cells. The compiled prototypes (fresh M cells, moved per slot) are not.
- **B3 — `pf`.** Binding proof fields needs `reassemble`'s positional spec (S-H4).
  - This stage uses the one fact it needs as a hypothesis: `PfHdr pf`, "byte 0 of `pf (e :: tr)` is
    byte 71 of `e`'s query".
  - A.5 gives it by definition (`hdr := payload₀[64…111]`).
- **B4 — the run's existence.** `SlotImp` needs `exec … = some (s, [])` on the read trace.
  - That is an induction over the 106k ops: each query read off the stream must equal the computed
    one.
  - It needs B1–B3 and per-item H-to-H links (each query's state equals the previous answer; the node
    query's halves follow the index bit). It is a new theorem, not rows.
- **Cost of a full pack map (from this stage's measurement).**
  - Size: ≈ 63k rows per aligned slot, ≈ 6 % of a `2^20` region (1.037× with the previous-node
    model). It fits the region.
  - Evaluation: irregular H cells cost ≈ 0.6 µs per row in `evalMT4` (an F product ≈ 0.2 µs on this
    VM). That would add ≈ 40 ms per bound slot to V.
  - Hence the full pack map needs a structured layout (affine or strided cell maps with a closed-form
    MLE), not per-row tables. **This is a design question for the blueprint (§4.4/A.11).**

## 2. What was built (`loc.py` code lines, HEAD → now)

| Module | Code | Content |
|---|---|---|
| `FRNodeRows4Pack` (new) | 83 | The data: `sCell`, `itemTag`, `winB`/`winFB`/`winF`, `wfData`, the closed `wfSeg` (8,905 pins), `pinRow`, `wfRows`, `kConst` (the program's seed constants), `kindRow`. Facts: `pinRow_holds`, `kindRow_holds`, `wfSeg_length`, `wfSeg_lt`, `kConst_byte`. Controls: `pinRow_ctl`, `kConst_ne`, `winB_ctl`. |
| `FRNodeRows4` | 95 → 152 | `linkRowsB4` (S-E12c's link rows, renamed). `packB` (the aligned slots), `packHead4`, `packWf4`, `packRows4`. The fold: `xRowsN*`, `xRowsK`, `xOkK` (the closed cell check), `rejR`, `extRowsC`. **`linkRows4 = linkRowsB4 ++ packRows4 ++ extRowsC`**. `linkN = 2^15`; `linkIRows4` sits at the link region. `idxInB`/`InSlot` keep the prototypes below the link region. Lemmas: `packRows4_length_le`, `extRowsC_length_le`, `linkRows4_length_le`. |
| `FRNodeRows4Fit` | 297 → 367 | `chBase_cLen_le`, `sCell_lt`, `aggChild_lt`, `packRows4_cells`. `slot_mem` covers the link region, the pack rows' H cells and the node rows (bound by `xOkK`, structural). `slot_nodup`, `link_facts` adapted. |
| `FRNodeRows4Plan` | 494 → 574 | The tables `LTb`/`ltbOf`, built once per point. **`linkV4`**: head and node rows via `growsVal3`, the pins via **`wfSum`**, one row factor and one cell factor per row. `wfSum_eq`, `wfLen_eq`, **`linkV4_eq`**. `evalMT4`/`slotV4` take the tables. `evalMT4_eq` is re-proved, statement unchanged. |
| `FRNodeRows4Model` | 38 → 40 | `packRows4N = 2·8,906`; `wotsRows4 κ` = S-E13b's 7,992 / 8,266 / 8,680. `mRows4_le` checks each slot below the link region. `mRowModel4_eq`: `N2` 2,175,428 of `2^22`, `N4` 3,377,136 of `2^23`, `N8` 4,832,228 of `2^23` (all within `N_M/1.05`). |
| `FRNodeRows4PackSound` (new) | 370 | The H bridge (`toBytes_bit`, `bitsB4_cell`, **`readByte_cell`**, **`chainBytes4_elem`**, `seg0_elem`). `seq4`'s alignment from shapes (`shAl`, `phasesOf_al`: one `decide +kernel` over shape parameters). `wfAt_of_pins`, `wf0_of_pins`. `PfHdr`, `kind_byte`, `kindRow_sel`. **`Gap4R`**, **`wots_aggPad_of_rows`**, **`gap4_of_rows`**, `gap4R_of_gap4`. Controls. **`ks_rev4GR`**, `Resid4GR`, **`certificate_rev4GR`**. |

**The rows** (`logs/S-E13a/nodedump/README.md`):
- In each slot whose segment is aligned (`N2`/`N4`: slots 0 and 1; `N8`: slots 0 and 4), there
  are `1 + 8,905` pack rows:
  - **the kind tie** `one·(H_e5 − Σ_ι K_ι s′_ι) = 0`, where `H_e5` is `hdr[0…16)` and `K_ι` are the
    slot program's own seed constants;
  - one pin per item, fixing the element where the item starts to `enc64 |q| ‖ tag(q)`. Item 0's
    element is `0x54 ‖ enc64 119 ‖ "FRSEED0"`.
- At slot 1: S-E13b's 7,992–8,680 node rows.
- The link region's rows per node:

  | Node | Rows | Before (S-E12c's link rows) |
  |---|---|---|
  | `N2` | 25,827 | 23 |
  | `N4` | 26,117 | 23 |
  | `N8` | 26,555 | 23 |

- **No new cells.**

## 3. Measurements (loaded VM, alternating A/B, same core; logs in `logs/S-E13a/`)

| What | Base (HEAD) | Now | Log |
|---|---|---|---|
| `evalMT4` N2 / N4 / N8 best, pack rows only | 84.2 / 84.9 / 60.2 ms | 95.8 / 98.4 / 72.9 ms | `plan4t-base-*`, `plan4t-new-*` |
| `evalMT4` N2 / N4 / N8 best, with S-E13b's fold | (same) | 117.4 / 120.5 / 93.5 ms | `plan4t-fold.log` |
| **V(N4)** `runSeq` best, pack rows only (rounds 6–8) | 182.8 / 196.8 / 198.2 ms | 213.2 / 206.1 / 198.7 ms | `vtime4-*-{6,7,8}.log` |
| **V(N4)** `runSeq` best, with the fold (rounds 9–10, heavier load) | 191.4 / 206.1 ms | 224.8 / 262.9 ms | `vtime4-*-{9,10}.log` |
| `linkV4` per slot (N4): slot 0 / slot 1 / other; `ltbOf` | — | 5.5 / 21.5–23.7 / 0.3 ms; 4.1 ms | `packt-fold.log` |
| process start (`plan4t init`, wall) | 2.13–3.16 s | 1.94–2.42 s | `plan-init-{3,fold}.log` |

- **V(N4) cost.** The pack rows cost ≈ +15 ms in `evalMT4`. S-E13b's node rows cost ≈ +17 ms
  more. Together V(N4) rises by ≈ +30 ms best.
- **The plan.** Its time is unchanged within noise. `wfSeg` is built in 22 ms at process start.
  The first version, which rebuilt `winB` for every byte, took 195 ms; `packi*.log` has both.
  `inR` is `true` at the new bound, and `xOkK` is `true` for every kind.
- **Profiles** (sequential, one core: `logs/S-E13a/profile-*.log`):

  | Module | Wall | Type checking |
  |---|---|---|
  | `FRNodeRows4` | 11.3 s | 0.26 s |
  | `FRNodeRows4Fit` | 24.8 s | 2.14 s |
  | `FRNodeRows4Plan` | 18.4 s | 0.70 s |
  | `FRNodeRows4Model` | 7.6 s | 0.02 s |
  | `FRNodeRows4Pack` | 8.6 s | 0.18 s |
  | `FRNodeRows4PackSound` | 17.8 s | 1.02 s |

  - `FRNodeRows4Fit` was 20.8 s at HEAD.
  - The kernel never evaluates `xRows`, `wfSeg`, `itemsOf seq4` or a layout. The only
    `decide +kernel` is over `seq4`'s phase shapes.
- **Runtime cross-check:** `plan4t check` on the first link-region version gave "equal true"
  against the full sparse sum for N2.

## 4. Controls

| Definition | (+) | (−) |
|---|---|---|
| `pinRow` | `pinRow_ctl` (holds iff the cell is the constant) | same |
| `kindRow`, `kConst` | `kindRow_ctl` (one-hot at `P30`, element `K_P30`); `kConst_byte` (byte 0 = kind byte) | `kindRow_ctl` (element `K_L32` fails); `kConst_ne` |
| `winB`/`wfSeg` | `winB_ctl` (`0x54 ‖ enc64 119 ‖ "FRSEED0"`, 16 bytes); `wfSeg_length` | `winB_ctl` (a later item has no `0x54`) |
| `PfHdr` | `pfHdr_ctl` (the header-copying decoder) | `pfHdr_ctl` (the empty decoder fails) |
| `Gap4R` | `gap4R_of_gap4` (the converse: nothing beyond `Gap4` is asked) | the dropped fields are theorems (`gap4_of_rows`) |
| `extRowsC`/`xOkK` | `xOkK` = `true` at run time (`packt-fold.log`) | the rejecting branch makes `StmtN4` unsatisfiable (`wots_aggPad_of_rows`) |

**Not available: an honest witness satisfying the new rows.** That needs P2's node witness (see
"For P2").

## 5. Deviations

1. **The pack map is not built** (B1–B4). This stage builds the mechanism (link region, H bridge,
   fast evaluation) and the cheap, sound parts (kind tie, `wf`).
2. **The link region is the last `2^15` rows** of a slot region, not the last 8. S-E12c's link
   rows moved to its start: a change of row indices for P2 (A.7).
3. **`PfHdr pf`** is a new hypothesis on the reader's proof decoder (S-H4's `reassemble` meets it
   by A.5). `ks_rev4GR` states it explicitly.
4. **The fold uses a closed check `xOkK`** with a rejecting fallback (the `ProtoFit` pattern), not
   `decide +kernel` over the rows (24 s per kind). Statements are unchanged.
5. The build tree is a copy of `fr-build-SN2`, which is a copy of `fr-build-SE12f` with the same
   probes and closer to HEAD.

## 6. Open questions and handover (remaining items, in order)

1. **`aggChk` (a)–(c)** (now mine, per the orchestrator):
   - (a) `c_A = leafStmt e n`, from `hashA` (`hashA_leafStmt`) and `PubCells4`'s `stC` cells
     (`digestOf_halves`), plus `enc64 (hAn κ a w)` = `hA`'s bytes 33–40 (`hAn < 2^64`). No rows.
   - (b) `1 ≤ k ≤ 4`, from `ActK` (`actK_kAct`) and `maxK ≤ 4`.
   - (c) The per-segment view checks (lengths, sum, end, chaining) need the sub-slots' views, so
     the pack map at `i ≥ 1` (B1) and `pf`'s spec (B3).
   - Then `Gap4R.aggChk` shrinks to (c).
2. **The orchestrator's rulings on B1 (R-A′) and B2.** With R-A′ the pack rows of sub-slot 0
   apply to every sub-slot shifted by `23,170·i` blocks. That discharges `kindS`/`wf` for `i ≥ 1`
   with the same lemmas: `chainBytes4_elem` is generic in the element.
3. **The `input` binding**: `vk` and `c₁` against the public cells (2 linear rows per `input`).
   This is a component of `imp`. It is useful only together with B4.
4. **V cost.**
   - `wfSum` can share the slot-independent factors: `eq(τ_lo20, ·)` is common to every slot's
     link region, and `Σ r_j c_j` is the same in every slot. Estimate: −40 % of the pins' cost.
   - S-E13b's node rows (`growsVal3`, ≈ 17 ms at slot 1) may have regular structure (strides) worth
     a template.
   - For the full pack map, structure is needed (§1).
5. **S-H4**: `pf`'s positional spec (A.5), with `PfHdr` as its first lemma.
6. **Blueprint** (not edited):
   - A.7's link region (`2^15` rows; link rows, then pack rows, then node rows);
   - §4.4/A.11's statement that trace cells need no rows (B2, and the cost model above);
   - the R-A′ spacer.

## For P2

- **Dump:** `logs/S-E13a/nodedump/`, with a README and `SHA256SUMS`.
  - Every prototype file, including the plan form, is **byte-identical to S-E12f's**, so the
    plan-form KAT stands.
  - **Only `node-N{2,4,8}.txt` change.** Their link rows now:
    - start at `σ·2^20 + 2^20 − 2^15`;
    - hold, in order: S-E12c's 7–8 rows, the pack rows (slots 0/1 of `N2`/`N4`, slots 0/4 of
      `N8`), then S-E13b's node rows at slot 1.
- **The prover writes no new cells.** But an honest witness must satisfy the pins:
  - the stream's tags and length words;
  - `hdr[0…16)` equal to the kind constant.
- **Please run the row checker over `node-*.txt` on honest `N2`/`N4`/`N8` witnesses.** That is the
  completeness KAT this stage could not run.
- **V's Rust `evalM`** must add the link region's rows as dumped. Their indices moved.
- **V(N4)** rises by ≈ 30 ms (best, §3).
