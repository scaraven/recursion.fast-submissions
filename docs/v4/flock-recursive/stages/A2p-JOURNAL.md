# A2′ journal: CapChk (PACK-4.4.1 §3.3, §7.1)

Track A2′, 2026-10-29. Worktree `v4/flock-recursive`, base HEAD `ee044f2` (RET-2 closed). Build tree
`logs/fr-build-A2` (copied from `logs/fr-build-SE14`), logs `logs/A2p/`.

## 0. Reading (brief, review, code)

- Brief: PACK-4.4 §7.1 "A2′", §3.3–§3.4, §9.1, §10; review PK-M1, PK-m4. TRACK-RULES.
- Where the pieces live (not where the brief puts them):
  - `seq4`'s phase table is `FRShape4.phasesOf S`, not `FRTranscriptDefs.phases` (3.x's, 8,891 items,
    still used with its exact values by the 3.x modules). The CapChk phases go into `phasesOf`,
    gated by a new `Seq` field `capChk` (false for `seq3`, true for `seq4`), so `phasesOf_seq3`,
    `itemsOf_seq3`, `piSizeOf_seq3` keep holding.
  - `nFields` (3.x, 18) stays; `FRShape4.nFields4 = 19` sizes `piSizeOf`. `FRTranscriptDefs` gains
    `fA := 18` only. `FRFormat` (3.x's format and 3.x's `reassemble`) needs no change.
  - There is no revision-4 `reassemble` in the tree yet (S-H4's, open question (iv) of PACK §9.3):
    row 18 is given as a specification in the RESULT.
- **Finding F1 (the memo's arithmetic): the five caps have 1,408 entries, not 1,920.** The ladder's
  caps are `2^9, 2^8, 2^8, 2^8, 2^7` (`ladderOfR`), `512 + 256 + 256 + 256 + 128 = 1,408`; the
  memo's own offsets `0, 512, 768, 1024, 1280` end at `1280 + 128 = 1,408`, and the caps field is
  `45,056 = 1,408 · 32` bytes (`fieldSizesOf_seq4`, field 14). The memo's `1,920 · 32 = 61,440`
  is an addition slip that the review re-derived from rather than checked. With the correct
  count, `A` is `45,056 + 32 = 45,088` bytes; the phase is `80 + 45,088 + 80 = 45,248 = 64 · 707`
  bytes, block-aligned exactly as PK-M1 requires. Constants: items 8,907 (unchanged), `piSizeOf
  seq4` **843,280** (not 859,664), stream **1,528,000 = 64 · 23,875** (not 1,544,384 = 64 ·
  24,131), `4 · 8,907 + 3 = 35,631` (unchanged). The 129-B spacer still aligns (the stream is
  still `≡ 0 mod 64`). `A`'s size is computed (`aBytes S = capEntries S · 32 + 32`), so the
  memo's 61,472 is one constant away if the orchestrator wants it.
- **Finding F2 (ordering): the accumulators cannot sit in `posOpsG`.** `ζ` is P3.4's first answer
  and `z` CapChkZ's: both are squeezed after every position. A straight-line program cannot read
  them at the positions. So a position ends with `shrN` (its cap index `k`); the accumulation runs
  in the finals (`capChkOps`), which read each position's path digest and `k` from the position's
  registers (`y + 6·sib`, `y + 6·sib + 1`, `y` the column fold the finals already read).
- **Decision D1 (no new op).** `z^{k + off}` is computed with existing ops (the bit product:
  `bitOf k t`, `selectHalf bit 1 z^{2^t}`, `mulK`), not a new `powIdx` op. A new `Op` constructor
  changes `FRVIR` (`evalOp`) and lands in `FRVIRCompile`'s catch-all as a *foreign* op (B0's module;
  871 new foreign flags per slot, a new `Gap4` entry until a template exists). With existing ops
  the compiler emits rows for it today. Cost: 9 K products per read in V instead of a table read
  (measured below).

## 1. Baseline (HEAD `ee044f2`, `logs/A2p/base-build.log`)

- `lake build FR Solution FRSoundness4TailShift FRSoundness4XCtrl FRNodeSound4Ctrl vtime4 plan4t`:
  green, 4,940 jobs.
- V(N4) `vtime4 21 n4f`, core 30, load ≈ 14: best **233.3 / 237.6 ms**, median 250.3 / 273.6 ms
  (`vtime4-base-{a,b}.log`); `evalMT4 N4` best 132.0 / 121.9 ms.
- `plan4t init`, core 29: **2.22 / 2.57 / 2.48 s**, `inR true` (`plan4t-init-base-{1,2,3}.log`).

## 2. The change (worktree)

- `FRTranscriptDefs`: `fA := 18` (3.x's `nFields`, `phases` untouched).
- `FRShape4`: `Seq.capChk : Bool := false`; `capEntriesBelow`, `capEntries`, `aBytes`, `capChkPh`;
  `phasesOf S := … ++ [Pf] ++ capChkPh S`; `seq4 := { … with e4end := 32, capChk := true }`;
  `nFields4 = 19`, `piSizeOf` over it (`piSizeOf_seq3` reproved: field 18 of `seq3` is empty);
  literals `itemsOf_seq4_length 8907`, `fieldSizesOf_seq4` (19 fields, `fA` 45,088), `piSizeOf_seq4
  843280`, `streamBytesOf_seq4 1528000`, `chainLenOf_seq4 23875`; new `capEntries_seq4`,
  `capChk_aligned`, `traces_spacers_le_qV` (`4·8907 + 3 ≤ qV4`; `traces_le_qV` kept for its two
  users).
- `FRVIR4`: `posOps4` loses its `capO` argument and its last two ops; `posW4 = 4 + 6·sL + 1`;
  `curOfY`, `kOfY`. `FRVIR4Mux`: the same for `posOpsG`; `finOps4F` appends `capChkOps`.
- `FRVIRFinals4`: `capMax`, `capReadOps`, `CapRead`, `capReadsOps`, `capEntryOps`, `capEntriesOps`,
  `capReads`, **`capChkOps`**; `finOps4 := (finals ++ capChkOps …).map reloc`; `noAsk_*`;
  `finOps4_seq3` reproved (`capChkOps` is empty at `seq3`).
- `FRVIR4At`: `map_at_capReadsOps`, `map_at_capEntriesOps`, `map_at_capChkOps`; `map_at_finOps4`
  reproved. `FRVIR4Uni`: signatures only.
- `FRSoundness4Pos`: `fsItems4_length 484`, `fsStarts4_eq` gains `482, 483`.
  `FRSoundness4Qry`: `8907`; `noAsk_finOps4` through `noAsk_capChkOps`.
- `FRX4Prog`, `FRX4Ext`: `798192` → `843280` (literal only; every proof unchanged).
- Literal-only fixes in modules whose numbers derive from the stream (no running track owns them):
  `FRNodeLayout4` (`aggChainLen_eq`/`_k3`, `hUsed_eq`: 73,076 / 121,124 / 193,196),
  `FRNodeKinds4` (`segB 1528000`, `cLen 23875`, `hEnd_eq`), `FRVIRTpl4Bridge` (`protoR_ctl`'s
  chain bases), `FRNodeRows4Pack` (`wfSeg_length 8907`), `FRVerifierImplNode4T` (`nodeE4_ctrl`
  reads `aggB 1 = 0x1750C0`'s bit 12 as `1`, bit 13 as `0`).

## 3. First build of `FR` (`logs/A2p/build-1.log`)

Shape-level modules green. Failures: the literal ones above (fixed), and the soundness modules
`FRSoundness4TailD` (`phOf_ge`, `rounds_check`) and `FRSoundness4R4Run` (`fsMsgs4_len`,
`fsCheck_qOf`, `matches_fsQ4`, `finOps4_eq`): A3′'s, by the brief. To give A3′ the whole list, a
**breakage scan** runs in the build tree only (`logs/A2p/scan/scan.sh`): each failing declaration
of a module that is not A2′'s gets its proof replaced by `sorry` **in `logs/fr-build-A2/src/`'s
copy** (never in the worktree), so that the modules after it compile and show their own failures;
round by round until the build is green. `round-<n>.txt` lists each round's failing declarations.

## 4. The scan (`logs/A2p/scan/`)

- 12 rounds; green at round 12 (`build-12.log`: `FR Solution FRSoundness4TailShift FRSoundness4XCtrl
  FRNodeSound4Ctrl`, 2,581 jobs). Failing declarations per round in `round-*.txt`; all of them in
  `sorried.txt`.
- Statement-level breaks (the scan stops on a repeat): `R4Outs.opsOut_posOps4`, `R4Qv.exec_queries4`
  (and `R4PosT`'s three `posOps4` calls): `posOps4` lost its `capO` argument. In the scan copies
  only, the argument was dropped (`copies/*.diff`), keeping `posT4`'s own `capO` (the reference).
- Two literal-only failures were in non-A3′ modules and are fixed in the worktree:
  `FRNodeRows4.packRows4_length_le` (8,908) and `FRNodeSound4R.segTr_length` & co. (8,907).
- Statements with the old literals (a grep over the statements, the text before `:=`): `482` in
  `R4At.SkRun4`, `R4Run.{fsMsgs4_len, fsCheck_qOf, matches_fsQ4, runLog_chain4}`,
  `R4Tail.acceptTail4_of_finLog`, `R4FrE.msg_abs4` (a bound: stays true); `≤ 51`/`= 51` in
  `TailD.{phOf_check, phOf_ge, phOf_bounds}`, `TailC.tail_cls`, `TailM.DT_stab`,
  `TailStep.phOf_examples`, `P4aDF.phStart4_mono` (true: phases ≤ 51 there). The 3.x copies
  (`FRSoundnessTailD` etc.) are 3.x's and unaffected.
- Decision: no R4/T4 module is edited by this track (the brief's boundary); the list goes to A3′.

## 5. Measurements after (`logs/A2p/`)

- `laydump4` (27 s): the template groups' row bases move by +58,368 (the cap check's rows before
  the templates). The hint is regenerated into the build tree only (`A2p/FRNodeRows4Hint.lean`; B0's
  module).
- `plan4t check`: `inR true`, `evalMT4` = the sparse sum for N2, N4, N8; sparse rows 133,803 +
  133,863 (S-E13a: 40,064 + 36,660), instances 4,530 + 4,530 (5,396).
- V(N4) best 513.2 / 516.5 ms (was 233.3 / 237.6), `evalMT4 N4` 365.8 / 355.9 (132.0 / 121.9),
  `plan4t init` 4.17 / 5.27 / 4.59 s (2.22 / 2.57 / 2.48). Load ≈ 21 (≈ 14 before).
- `vtime4 prof 3 n4f` (`prof4-after.log`): the cap check's native ops ≈ 9 ms per run (counts match
  `capChkOps` exactly: `mulK` +11,703, `addK` +6,837).
- Node dumps: `nodedump4` (2 m 30 s), `planform4` (7 s), `protodump` (1 s) into `A2p/nodedump/`;
  `planform_kat.py`: 0 of 662,195 / 652,492 rows differ, **KAT PASS** (1 m 31 s).
- IR dumps (`A2p/dump.sh`): `ops-*.txt`, `group-*.txt`, `items.json`, `summary.txt`,
  `fsummary.txt`, `last.txt`, `capkat.txt`, `SHA256SUMS`. `asks = items: true` for all six kinds;
  0 `piDigestAt`.
- The cap-check KAT (`IRDumpA2 capkat`): honest accepted; `A_0 + 1` and a corrupted path digest
  rejected.

## 6. Build cost

- First sequential profile under load ≈ 20–37 (other agents on core 26): noisy, e.g.
  `FRVIRFinals4` 2:25 then 1:47.
- Paired runs at load ≈ 3 (HEAD's text against the same dependencies): `FRVIRFinals4` 28.7 s vs
  19.7 s — bisected (`prof-F4{a..g,x,y,z}.log`) to the cap-check generators' dot-constructor
  lists (≈ 4 s for `capReadOps` alone): written with `Op.` constructors (and `capBitOps` factored
  out), 20.3 s. `FRShape4` 33.1 s vs 27.3 s — bisected (`prof-S4*.log`) to `phasesOf`'s `++`
  chain (HEAD ≈ 12 s of elaboration, ≈ 19 s with the cap check appended): one type ascription on
  the PIOP literal, 24.3 s (below HEAD). The ops are identical (`ops-N4.txt` re-dumped, `cmp`).
- Axioms (`A2p/Axioms.lean`, `axioms.log`): 43 theorems, standard axioms or fewer, no `sorryAx`.
- Source rule: 364 files, 0 findings.
