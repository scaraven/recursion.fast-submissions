# A1′ (R-A′: the spacer query between an aggregate's segments) — JOURNAL

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `face798`. Build tree
`logs/fr-build-A1` (copied from `fr-build-RSV2`); MINE in `logs/fr-build-A1/MINE.txt`.

## 0. Setup

- HEAD is red at RSV-V's declarations (`FRSoundness4R4Fin.flag_gFinE`/`flag_gFinB'`,
  `FRSoundness4Qry.noAsk_gFinE`/`noAsk_gFinB'`/`noAsk_gFinPf`): everything downstream of
  `FRSoundness4Frame` (so `FRNodeCircuit4` and the whole node chain) does not build at HEAD.
  **Build-tree-only scaffold**: `logs/fr-build-A1/scaffold/apply.sh` replaces those five proofs by
  `sorry` in the build tree's HEAD copies (never in the worktree), so that my modules can be
  checked. Every theorem I report is checked with `#print axioms` for `sorryAx` (§ axioms).

## 1. Constants (recomputed from today's `seq4`)

- `segB = streamBytesOf seq4 = 1,551,104 = 64·24,236`; a trace is `segB − 1 = 1,551,103 ≡ 63 (mod 64)`.
- Spacer `absorbQ 0³² 0⁴⁹`: entry `8 + (8 + 32 + 49) + 32 = 129 ≡ 1 (mod 64)` (`Item.absorb 49`).
  **129 B is right**: the stride `segB − 1 + 129 = 1,551,232 = 64·24,238` is whole blocks, so
  segment `i` starts at `1 + i·1,551,232 ≡ 1 (mod 64)`, sub-slot `i`'s stream is sub-slot 0's
  shifted by `24,238·i` blocks. Any spacer must be `≡ 1 (mod 64)`; 129 is the smallest single
  absorb that is (`80 + len ≡ 1` ⇒ `len ≡ 49`).
- `aggB k = 1 + k·1,551,103 + (k − 1)·129 = 64·(24,238·k − 2)` (`k ≥ 1`): whole blocks.
  `aggL 2 = 48,474`, `aggL 3 = 72,712`, `aggL 4 = 96,950`; residues 0.
- `hUsed`: N2 74,013 → 74,015; N4 122,491 → 122,497; N8 195,208 → 195,220; N8 `lBase` 195,328
  (unchanged) ≤ 195,584. `hEnd` 74,017 / 122,501 / 195,228.
- `qV`: `4·8,783 + 3 = 35,135 ≤ 36,000`.

## 2. The straddling elements (a finding against the brief)

A spacer's entry ends with its 32-byte answer (random under the ROM: it cannot be pinned), and a
segment's trace starts right after it. So, with the spacer at stream offset `≡ 0 (mod 64)`:
- spacer element 6 = query byte 96 (`msg[48] = 0`) ‖ answer bytes 0–14: **1 constant byte + 15 free**;
- sub-slot `i ≥ 1`'s element 0 = answer byte 31 ‖ `enc64 119 ‖ "FRSEED0"`: **1 free byte + 15
  constant** (the seed's length word, which `wf` needs).
This holds for every spacer whose entry is `≡ 1 (mod 16)` (the last query byte always shares an
element with its answer; the byte before a segment is always an answer byte), so the brief's "9
whole-element pins per spacer" and "`wf` at `i ≥ 1` by the shifted lemmas" are not enough: two
elements per spacer need a bit decomposition. Rows per spacer: 6 whole pins (elements 0–5), 120
Boolean + 1 linear (element 6: bytes 1–15 free, byte 0 zero), 8 Boolean + 1 linear (sub-slot
element 0: byte 0 free, bytes 1–15 the seed's). The 128 Boolean cells are exactly the L cells freed
by `padRows`' element-7 decompositions (`pbC κ σ (s+1)`, spacer `s`).

## 3. Implementation log

- `FRAgg`: `spacerQ`, `spacer`, `spEntry`, `aggProgs := segProgs.intersperse spacer`; `VAwith` runs
  `seqAll (aggProgs …)`. `aggTr`/`aggTrace` (closed form `aggTrace_range`), `withSp`,
  `forall₂_intersperse`, `mem_intersperse_of_mem`, `segProg_mem_aggProgs`, `Forall₂_exists_mem`,
  `aggTrace_length`, `mem_aggTrace`, `spacer_run`, `spacerQ_size` (89), `spacerQ_bytes`,
  `spacer_entry_length` (129). `VA_sound` (over `aggProgs`), `VA_extract`/`_on` (by membership),
  `VA_complete` (on `aggTrace ans trs`, any answers), `VA_queries_le` (`4·qS + 3`, via
  `seqAll_queries_le_sum`, `sum_intersperse`). Controls `ctrlA_pos` (on `[spEntry a]`),
  `ctrlA_no_spacer` (the empty trace is now rejected).
- `FRVerifier4`: `V4_queries_le`/`ks_queries4` take `4·qS + 3 ≤ qV4`; `spacerBytes_eq`.
- `FRNodeLayout4`: `spacerBytes := 129`; `aggChainLen` with `(k − 1)·129`; `aggChainLen_eq`
  (48,474 / 96,950, residues 0), `_k3` (72,712, residue 0, `aggChainLen 1 = chainLenOf seq4`),
  `aggChainLen_no_spacer` (−: 63 without), `hUsed_eq` 74,015 / 122,497 / 195,220, `lBase_eq`
  (74,240 / 122,624 / 195,328; bound 195,584), `hUsedN8At` with spacers.
- `FRNodeKinds4`: `spacerB`, `strideB`, `sBlk = 24,238`, `aggB k = 1 + k(segB−1) + (k−1)·129`,
  `strideB_eq`, `aggB_succ`, `aggB_blocks` (whole blocks), `hEnd_eq` 74,017 / 122,501 / 195,228,
  `main_not_final2` restated (the counter now matches, the final flag does not).
- `FRNodeTarget4C.aggB_lt`, `FRVerifierImplNode4T.nodeE4_ctrl` (aggB 4 even now: bit 7 / bit 0),
  `FRVIRTpl4Bridge.protoR_ctl` (route constants 96,950 / 48,474): literals that follow.
- `FRNodeRead4`: `segTr` at `1 + i·strideB`; `spItem`, `spAnsB`, `spAns`; `sgn4`'s aggregate
  trace is `aggTrace (spAns …) (sub-slot traces)`.
- `FRNodeRead4W`: `SpAt`, `spacer_bytes`, `stream_of_wf` (prefix induction over `aggB m`).
- `FRNodeCircuit4`: `NodeResid4.aggTr` is `∃ ans, tr = aggTrace ans …`; `agg_acc` via
  `VA_complete … ans`. `AggPad4`'s definition kept (its `r` is 64 for `1 ≤ k ≤ 4`).
- `FRNodeSound4R`: `Gap4.wf` with the spacers' `SpAt`; `chainMsg_of_wf`; `aggTr_length`
  (`k·8,783 + k − 1`), `pack` against `traces_spacers_le_qV`; `sgn4_qcap` (spacer query 89 B).
- `FRNodeSound4Ctrl`: the converse (`sgn4_tr`, `chain_len`, `wf_of_eq`, `wf_of_chainMsg`) with
  spacers.
- `FRNodeRows4Pack`: `wfSeg` without element 0 (8,782); `seedW`, `seedM`, `spBytes`, `spPin`,
  `bitRow`, `packAt`, `decRow`, `headRows` (1 row for segment 0, 136 for a later segment),
  `spC` (S-E13b's freed `pbC` cells).
- `FRNodeRows4`: `packB` for every slot (`chBase + subIx·sBlk`), `segIx`, `packHead4` = kind tie ::
  `headRows`; link rows ≤ 8 + 8,919 + 7,904.
- `FRNodeRows4Fit`: `packB_fit` (one `decide` per kind), `packRows4_cells` re-proved.
- `FRNodeRows4Wots`/`Ext`/`Agg`/`WotsCtrl`: `padRows` without the element-7 decomposition (6 rows
  per candidate); `xRows_length` 7,862 / 7,878 / 7,904; `gap4_aggPad` re-proved (`lastR_64`);
  `lastR_eq` 64s, `lastR_no_spacer` (−).
- `FRNodeRows4PackSound`: `agg_elem`, `segi_elem`, `spc_elem`, `wfData_shift`, `HeadOk`,
  `headOk_of`, `wfSeg_of_pins`, `spAt_of_pins`, `kind_byte` (any segment), `wf_of_rows`;
  **`Gap4R` = `imp` + `aggChk`**; `gap4_of_rows` proves `kindN`, `kindS` and `wf` at every slot.

## 4. Rebase on B5 (`9a41aac`) and measurements

- B5's `FRNodeRows4Plan`/`FRVerifierImplNode4F` build unedited against my modules: every slot keeps one
  pinned block whose stream is `wfSeg` (at its own `b0`); the spacer rows are in `packHead4`, which
  `linkV4` evaluates generically.
- `plan4t check`: fast `evalMT4` = sparse sum on N2/N4/N8 (`equal true`); `plan4t init` `inR true`.
- V(N4) A/B vs B5 (4×21, core 29): own kind 258.3 → 266.6 ms, all kinds 281.9 → 307.2 ms (each sub-slot
  now has its own pinned block).
- Kernel hot spots of mine removed: `wf_of_eq` (90 s → 0.7 s: generalize `aggB i`, the kernel was
  unfolding it against `i·strideB − 128`), `lBase_eq` (2.6 s, dropped), `aggChainLen_no_spacer` merged
  into `aggChainLen_eq` (one `streamBytesOf seq4` evaluation instead of two).
- Hint regenerated (route literal only), `arenafit`/`cellfit` unchanged, node dump in `logs/A1p/nodedump/`.
