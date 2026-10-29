# B4 (track L-circ): RESULT — `aggChk` from the node rows; `Gap4R` reduces to `imp`

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `e464756`). Build tree
`logs/fr-build-B4` (copy of `fr-build-A1`; HEAD's files, mine symlinked; HEAD's red RSV-S
declarations stubbed in the tree's copies only: `scaffold/apply.sh`). Logs `logs/B4/`. Journal
`B4-JOURNAL.md`. Every lean/lake/probe ran in a 16 GB scope under `timeout`. No sub-agents, nothing
committed, no sorry in the worktree.

## 0. Summary

| Item | State |
|---|---|
| `aggChk` discharged | **Done**: `N4s.aggChk_of_rows : PfHdr pf → PfView pf → StmtN4 … → Gap4R.aggChk` (`FRNodeRows4AggChkG`) |
| `Gap4R` reduces to `imp` | **Done**: `N4s.gap4_of_rowsI : PfHdr pf → PfView pf → StmtN4 … → (imp) → Gap4` |
| rows folded into `nodeIRows4` / `evalMT4` | **Done**: slot 1's node rows are `W4.xRowsA = xRows ++ chkRows`; B5's plan picks them up through `extRowsC` (no plan code changed); `plan4t check`: `evalMT4` = sparse sum (§4) |
| `evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX` | untouched (modules not edited); MxKat passes |
| controls | `FRNodeRows4AggChkCtrl` (§3) |
| ask templates on the arenas (B3's `ATOk`) | **not done** (§6.1): they bind `imp`, not `aggChk`; B3's modules are red at HEAD pending PORT |
| PK-m7's `hashA`/`hashB` statement rows | **not built** (§6.2): designed, exact rows given; they serve `imp`'s `input`/`stmtOk4` |
| build | `lake build FRNodeRows4AggChkCtrl FRNodeRows4Plan FRVerifierImplNode4F FRNodeRows4Model FRNodeRows4ArenaPlace FRNodeSound4Ctrl FRNodeRows4WotsCtrl`: green, 2,493 jobs (`build1.log`); probes `vtime4 plan4t mxkat` green |
| axioms | 58 declarations ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, no `sorryAx` (`axioms.log`) |
| source rule | 418 files, 0 findings (`source-rule.log`) |

## 1. The construction

`Gap4R.aggChk a`: `∃ vs, mapM segView (aggSegs … π_A) = some vs ∧ aggChecks c_A n e vs`, with
`π_A = aggHdr k hAn hAe ++ slot proofs` (the reader `rd4`). Per check:

| check | how |
|---|---|
| each sub-slot proof has a view | `kindS_of_rows` (A1′'s pack rows; factored out of `gap4_of_rows`, no statement change) |
| the view's fields | `view_sub`: `start = dg2 (E6, E7)`, `h = sh1 (E13, E14, E15)`, `n = n8 (E15)` of the sub-slot's stream elements (`sE κ σ i e = sCell (chBase + i·sBlk) e`), through the new hypothesis `PfView pf` |
| `c_A = leafStmt e n` | **no row**: Z truth at `cAB` (a `hashA` block: `cAB_tgt`), `Kinds.hashA_leafStmt`, `PubCells4` (`stC = hc cAB 2/3`): `stmt_A` |
| `1 ≤ k ≤ 4` | `actK_kAct`, `kAct_le` |
| `1 ≤ nᵢ ≤ cap κᵢ` | rows `rngRowsI`: `rng_sub` |
| `Σ nᵢ = n` | rows `mskRowsI`, `addRowsI`, `sumRow`: `sum_sub` (ripple-carry adder over `GF(2^128)`: sum `a+b+c`, carry `ab + (a+b)c`) |
| `h_{k−1} = e` | rows `endRowsJ`, gated `[k = j]` (`ind`, from the activities — not from the chain counters, per the orchestrator's note on `main_not_final2`): `end_sub` |
| chaining | rows `chnRowsI`, gated `Sᵢ`: the byte shift `E6/E7 ← bits of E13–E15` (`chain_sub`) |

Stream geometry (A.5, segment-relative): `hdr` = stream bytes 80–127 (elements 5–7; `hdr.pub` =
6, 7); `stmt` = item 1's message = stream bytes 208–335 (elements 13–20); `h` = stmt[1..33) =
E13[1..16) ‖ E14 ‖ E15[0]; `n` = stmt[33..41) = E15[1..9). `cAB`'s message (`tagLeaf ‖ e ‖ enc64 n`)
has the same layout in its elements 4–6. Only the unaligned byte-1 shift needs bits: E13, E14, E15
of each sub-slot and `cAB`'s 4, 6 are decomposed into Boolean L cells.

**L cells** (signed child `σ = aggChild a`'s `2^14` stride, offsets `12,288 … 14,487`; S-E13b/R-A′
use up to 11,648): `bC` 1,536, `aC` 256, `mC` 128, `pC`/`cC` 256, `iC` 4, `xC` 16. **The prover (E1)
must fill them**: bits of the elements, `m = S·bit`, the adder's honest products and carries, the
length's inverse, `s_ι · bit_{c_ι}`.

## 2. Rows and counts

Per aggregate (`aggRowsC`, `maxK` sub-slots): per sub-slot `decRowsI` 387, `rngRowsI` 11,
`mskRowsI` 19, `chnRowsI` 2 (`i ≥ 1`); `decRowsA` 258; `endRowsJ` 3 per `j`; `addRowsI` 43 per
addition; `sumRow` 1.

| kind | `chkRows` | node rows `xRowsA` (was `xRows`) | slot 1 link rows (≤ `8 + 8,919 + xRowsA`) of 32,768 |
|---|---|---|---|
| N2 (`maxK` 2, 1 aggregate) | 1,144 | 9,006 (7,862) | ≤ 17,933 |
| N4 (`maxK` 4, 1 aggregate) | 2,074 | 9,952 (7,878) | ≤ 18,879 |
| N8 (2 aggregates of 4) | 4,148 | 12,052 (7,904) | ≤ 20,979 |

Fit literals (kernel-checked bounds, not exact): `aggRowsC_length_le ≤ 2,076`,
`chkRows_length_le ≤ 4,152`, `extRows4_length_le` / `extRowsC_length_le ≤ 12,056` (were 7,904);
`linkRows4_length_le` (< `2^15`) re-proved unchanged. H is untouched (no new block; N8's 256-block
headroom is unchanged). M and the arenas are untouched.

## 3. Controls (`FRNodeRows4AggChkCtrl`)

| definition | (+) | (−) |
|---|---|---|
| decomposition rows (`pkO` at offset 0) | `pkO_unpack`: every element is its packed bits | `pkO_bits_ctl` |
| adder rows | `full_add_complete` | `full_add_neg` (`1 + 1` with carry 0) |
| inverse row (`n ≠ 0`) | `inv_ctl` | `inv_ctl` (length 0 active) |
| cap rows | `cap_ctl` (`n = 2^c`) | `cap_ctl` (`n = 2^c + 1`) |
| chaining rows | `chain_ctl` (inactive sub-slot) | `chain_ctl` (active, start ≠ shifted end) |
| `aggChecks_of` | `aggChecks_ctl` (two chaining views, total 3) | FRAgg's `ctrlA_bad_start/_sum/_end` |
| `PfView` | `pfView_ctl` (copying decoder) | `pfView_ctl` (empty decoder) |
| `capE` | `cap_segAt` | `capE_ne` |

## 4. Measurements

All on the shared VM under other tracks' load (load average 10–21); best-of values.

**Correctness of V's plan with the new rows** (`plan4t check`, `logs/B4/plan4t-check.log`): `evalMT4`
equals the sparse sum over `nodeIRows4` on N2, N4 and N8 (`equal true` ×3; sparse 188 / 381 / 477 s).
`plan inR true`.
**MxKat** (`mxkat.log`): compiled `evalMT4`/`evalMX4` = B5's reference code on every kind and
support: all `true`.

**V(N4)** (`abv.sh` = A1′'s with HEAD `../A1p/a1-bin` vs `b4-bin`, 6 alternating rounds × 21, core 29,
load 11–22; `vtime-ab.summary`/`.log`; a first 4-round run under heavier load, `vtime-ab-1.*`, was too
noisy to use). Best of runs, ms:

| | HEAD (A1′) | **B4** | Δ |
|---|---|---|---|
| V(N4), own kind | 264.6 | **267.5** | +2.9 |
| V(N4), all three kinds | 308.3 | **315.2** | +6.9 |
| `evalMT4` N4 | 142.9 | 147.1 | +4.2 |
| `evalMX4` support N4 | 143.6 | 147.1 | +3.5 |
| `evalMX4` support N4+N2 | 151.9 | 160.7 | +8.8 |
| `evalMX4` support N4+N8 | 172.9 | 185.5 | +12.6 |
| `evalMX4` support all | 183.8 | 192.9 | +9.1 |

**V(N8)**: there is no V(N8) probe in the tree (VTime4 verifies an N4 proof). The rows change only
the `evalM` side, so the proxy is N8's share of `evalMX4`: (N4+N8) − N4 = 29.3 → 38.4 ms, **+9.1 ms**
for N8's 4,148 rows (2 aggregates); `plan4t check`'s `evalMT4` N8 best 134.7 ms (one run, heavy
load). As expected, these are irregular dictionary rows (B5's `crowsVal3`), ≈ 0.6–1 µs per row.
Lever if needed: template the per-sub-slot rows (C0), they repeat at a fixed block offset.

**Plan init** (`plan4t init`, core 27, `plan4t-init.log`): 5.33 / 5.73 / 5.82 s user (A1′: 5.10 s).
The closed `xRowsN*` constants grow by 1.1–4.1 k rows.

**Per-module CPU** (`-DElab.async=false --profile`, one core, `cpu.txt`): wall; kernel.

| module | now | HEAD (A1′'s `profile-*`) |
|---|---|---|
| `FRNodeRows4AggChk` (new) | 9.7 s; 0.10 s | — |
| `FRNodeRows4AggChkB` (new) | 13.8 s; 0.60 s | — |
| `FRNodeRows4AggChkS` (new) | 17.3 s; 1.27 s | — |
| `FRNodeRows4AggChkG` (new) | 21.3 s; 1.84 s | — |
| `FRNodeRows4AggChkCtrl` (new) | 11.2 s; 0.21 s | — |
| `FRNodeRows4Ext` | 16.7 s; 8.75 s (the untouched `xRows_length` simp) | 28.2 s; 18.1 s |
| `FRNodeRows4` | 13.2 s; 0.52 s | 7.5 s; 0.15 s |
| `FRNodeRows4PackSound` | 28.6 s; 3.47 s | 21.5 s; 2.68 s |

New kernel time ≈ +4.4 s (the five new modules ≈ 4.0 s; `FRNodeRows4`/`PackSound` +1.2 s; `Ext`
within noise). No `decide` over row lists: the counts are bounds by `List.sum_le_length_nsmul`.

**Code lines** (core `loc.py`, `loc.txt`): new 90 + 173 + 309 + 339 + 69 = 980; `FRNodeRows4Ext`
22 → 33; `FRNodeRows4` 156 → 156; `FRNodeRows4PackSound` 606 → 611.

## 5. Statement changes

| declaration | change | why |
|---|---|---|
| `W4.extRows4` | `xRows κ` → `xRowsA κ` (definition) | the fold |
| `W4.extRows4_length_le` | `≤ 7904` → `≤ 12056` | the fold |
| `Rev4.xRowsN2/N4/N8` | `W4.xRows` → `W4.xRowsA` (definitions) | the fold |
| `Rev4.xRowsK_eq` | `= W4.xRows κ` → `= W4.xRowsA κ` | the fold |
| `Rev4.extRowsC_length_le` | `≤ 7904` → `≤ 12056` | the fold |
| `N4s.gap4_of_rows`, `wots_aggPad_of_rows`, `linkRows4_length_le` | **unchanged** (proofs: `kindS_of_rows`; membership through `xRowsA`) | — |

New: `N4s.PfView` (a hypothesis on the proof decoder, next to `PfHdr`).

## 6. Open items and requests

### 6.1 Not done: ask templates on the arenas (B3's `ATOk`)

They are the `imp` binding (PACK §4.2: FS links, Merkle mux rows, pins as `AT` templates meeting
`ATOk`), not `aggChk`. `FRNodeRun4`/`FRNodeRun4S` (B3's interface) are red at HEAD pending PORT, and
the arena binding (B2″'s import cells) is placed but has no template yet. Next track: an `AT π` per
prototype over B2″'s `aCell`s, `askIRows4 ⊆ nodeIRows4` folded at `b` = B2″'s binding rows
`[720,896, 852,992)`, then `gap4Imp_of_run` → `Gap4R.imp`; with `gap4_of_rowsI` that closes `Gap4`.

### 6.2 Not built: PK-m7's statement rows (they serve `imp`'s `input c` / `stmtOk4`)

With R-A′ the `stmt` field is element-aligned (elements 13–20) and is, honestly, the padded message
blocks (`FRVIR.stmtDigest`'s doc), so the ties are whole-element rows (no bits):
- segment slot `v = sub κ a i` (gated `Sᵢ`): `hc (stmtB κ + 3v) (4 + e) = sE κ σ i (13 + e)`, `e < 4`
  (4 rows); then `hashA_leafStmt` gives `h_out(stmtB + 3v) = segC (view)` — the cells for the slot's
  `input c` alias;
- previous node (slot 0, `hasPrev`): `hc B1 (4+e) = E(13+e)`, `hc B2 (4+e) = E(17+e)` (8 rows),
  `hc B2 h = hc B1 (2+h)` (2), `hc B2 (2+h) = seedC κ 0 (2+h)` (2); then `hashB_nodeStmt` and
  `PubCells4` give `stmtDigest .N30 stmt = c₁` (`stmtOk4`).
The block-generic forms of `hA_get`/`hA_eq`/`stmt_A` (this stage's) carry over by replacing `cAB` with
the slot's block.

### 6.3 Requests

1. **PORT** (`FRXOut4`): prove `theorem pfView_reassemble4 (aB : ℕ) : N4s.PfView (reassemble4 seq4 aB)`
   (fields 0 and 1 of `reassemble4`: `ctbs4` at `fHdr` starts with `qB4 a 0 71 48`, at `fStmt` with
   `qB4 a 1 40 128`, field 0's length is 48 by `ctbs4_length`; `fitL_extract_getD`), as
   `pfHdr_reassemble4`. Then `FRSubmission4Cert` can use `gap4_of_rowsI pf4 pfHdr_pf4 pfView_pf4`.
2. **Orchestrator** (`FR.lean`): `import FRNodeRows4AggChkCtrl` (pulls the other four).
3. **E1 / P2** (prover): fill the L cells of §1 at slot 1's node rows; the rows are in
   `W4.chkRows` (`W4.aggRowsC κ a (actW κ a)`), order as listed in §2.
4. **RSV-S2b / X4**: `Gap4R` now needs only `imp`; `gap4_of_rowsI` is the composition point.

## 7. Files

New: `FRNodeRows4AggChk.lean`, `FRNodeRows4AggChkB.lean`, `FRNodeRows4AggChkS.lean`,
`FRNodeRows4AggChkG.lean`, `FRNodeRows4AggChkCtrl.lean`. Edited: `FRNodeRows4Ext.lean`,
`FRNodeRows4.lean`, `FRNodeRows4PackSound.lean`. Not edited: `FRNodeRows4Plan`,
`FRVerifierImplNode4F`, `FRNodeRows4Agg`, `FRNodeRows4Arena*` (no change was needed).
