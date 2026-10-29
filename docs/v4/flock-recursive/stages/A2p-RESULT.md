# A2′ RESULT: CapChk, the batched cap check (PACK-4.4.1 §3.3, §7.1)

Track A2′, 2026-10-29. Base HEAD `ee044f2`. Build tree `logs/fr-build-A2` (from `fr-build-SE14`),
logs `logs/A2p/`. Journal: `stages/A2p-JOURNAL.md`. Nothing committed.

## 0. Summary

- **Done.** The per-position cap reads are gone: no `piDigestAt` in any program, and every
  `ops-*.txt` has 0 of them where INT-8's had 871. In their place:
  - a new proof field `A` (field 18, `fA`);
  - two new phases after `Pf`: `CapChk` (absorb `A`) and `CapChkZ` (squeeze `z`);
  - the finals' batched check `capChkOps`, which holds the accumulators and the two identities.

  The shape, VIR and dump layers build. The dumps, the KATs and the plan-form KAT are
  regenerated and pass.
- **F1, the orchestrator must rule: the five caps have 1,408 entries, not 1,920.** The memo's
  "1,920" is an addition slip:
  - The caps are `2^9 + 2^8 + 2^8 + 2^8 + 2^7 = 1,408`. The memo's own offsets `0, 512, 768, 1024,
    1280` end at 1,408, and the caps field is `45,056 = 1,408 · 32` bytes.
  - The review re-derived its numbers from the memo's 61,440 and so did not catch it.
  - With the correct count, `A` is `1,408 · 32 + 32 = 45,088` bytes. The phase is `80 + 45,088 +
    80 = 45,248 = 64 · 707` bytes, block-aligned exactly as PK-M1 requires.
  - The constants are therefore: **items 8,907** (as ruled); **`piSizeOf seq4` 843,280** (not
    859,664); **stream 1,528,000 = 64 · 23,875** (not 1,544,384 = 64 · 24,131); **qV `4 · 8,907 + 3
    = 35,631`** (as ruled).
  - `A`'s size is computed, as `aBytes S = capEntries S · 32 + 32`. The memo's 61,472 is one
    constant away (a pad of 16,416) if wanted, but it would add 16 KB of `|π|` for nothing.
- **Deviation D2: the accumulation sits in the finals, not in `posOpsG`.** `ζ` (P3.4's first
  answer) and `z` (CapChkZ) are squeezed after every position, so a straight-line program cannot
  read them at the position. A position now ends with its cap index (`shrN`). After every other
  final, `capChkOps` reads each position's path digest and cap index from the position's registers
  (`curOfY`, `kOfY`) and accumulates.
- **Deviation D1: no new `powIdx` op.** `z^{k+off}` is the bit product, built from existing ops
  (`bitOf`, `selectHalf`, `mulK`). A new `Op` constructor would change `FRVIR.evalOp` and fall into
  `FRVIRCompile`'s catch-all as a *foreign* op: that is B0's module, it would add 871 foreign flags
  per slot and a new `Gap4` entry. With existing ops the compiler emits rows for it today. The
  measured cost in V is about 9 ms of native ops (§3).
- **V(N4) regresses until B2′ lands. Measured: best 233 → 513 ms, `plan4t init` 2.2–2.6 → 4.2–5.3
  s.** Almost all of it is `evalMT4`, 122–132 → 356–366 ms:
  - The cap check's circuit rows are untemplated (+58.8 k rows per prototype). PACK §3.3 assigns
    their templates to B2′.
  - About 35 k more rows per prototype move from instance pieces into sparse rows. This is
    measured; the cause I give is not checked against the plan builder: probably the Merkle
    blocks, whose path digest the cap check now reads from outside the block (§3).
  - V's native cap-check ops cost about 9 ms.
- **The soundness chain breaks where expected**, at 13 R4/T4 declarations (§5, "For A3′"). A
  build-tree-only scan sorried the failing proofs one round at a time and reached a green
  `FR Solution` after 12 rounds, which proves this is the complete set of build failures. Statements
  that are now false but still compile behind those sorries are listed as well. The worktree has no
  `sorry`.

## 1. What was built (file by file; code lines by `loc.py`, HEAD → now)

| Module | Change | code |
|---|---|---|
| `FRTranscriptDefs` | `fA := 18` (3.x's `nFields`/`phases` untouched) | 383 → 384 |
| `FRShape4` | `Seq.capChk : Bool := false`; `capEntriesBelow`, `capEntries`, `aBytes`, `capChkPh`; `phasesOf S := … ++ [Pf] ++ capChkPh S`; `seq4` with `capChk := true`; `nFields4 = 19` and `piSizeOf` over it (`piSizeOf_seq3` reproved: `seq3`'s field 18 is empty); literals `itemsOf_seq4_length 8907`, `fieldSizesOf_seq4` (19 fields), `piSizeOf_seq4 843280`, `streamBytesOf_seq4 1528000`, `chainLenOf_seq4 23875`; new `capEntries_seq4`, `capChk_aligned`, `capChkPh_ctl`, `traces_spacers_le_qV` (`traces_le_qV` kept for its two users) | 199 → 219 |
| `FRVIR4` | `posOps4`: no `capO`, ends with `shrN`; `posW4 = 4 + 6·sL + 1`; `curOfY`, `kOfY` | 137 → 136 |
| `FRVIR4Mux` | the same for `posOpsG`; `finOps4F` appends `capChkOps` | 151 → 150 |
| `FRVIRFinals4` | `capMax`, `capReadOps`, `CapRead`, `capReadsOps`, `capEntryOps`, `capEntriesOps`, `capReads`, **`capChkOps`**; `finOps4 := (finals ++ capChkOps).map reloc`; `noAsk_capReadsOps`/`noAsk_capEntriesOps`/`noAsk_capChkOps`; `capChkOps_off`, `capChkOps_head`; `finOps4_seq3` reproved | 447 → 528 |
| `FRVIR4At` | `map_at_capReadsOps`, `map_at_capEntriesOps`, `map_at_capChkOps`; `map_at_finOps4` reproved | 313 → 340 |
| `FRVIR4Uni` | signatures only | 241 → 241 |
| `FRSoundness4Pos` | `fsItems4_length 484`; `fsStarts4_eq` gains `482, 483` | 96 → 97 |
| `FRSoundness4Qry` | `8907`; `noAsk_finOps4` through `noAsk_capChkOps` | 173 → 173 |
| `FRX4Prog`, `FRX4Ext` | `798192` → `843280` (the literal only; every proof unchanged) | 169, 543 |
| `FRNodeLayout4` | literals derived from the stream: `aggChainLen_eq`/`_k3` (47,750 / 95,500 / 71,625), `hUsed_eq` (73,076 / 121,124 / 193,196); doc slack | 52 |
| `FRNodeKinds4` | `segB 1528000`, `cLen 23875`, `hEnd_eq` (73,078 / 121,128 / 193,204) | 393 |
| `FRVIRTpl4Bridge` | `protoR_ctl`'s chain bases `(23875, 95500)`, `(23875, 47750)`, `(95500, 95500)` | 65 |
| `FRNodeRows4Pack` | `wfSeg_length 8907` | 83 |
| `FRNodeRows4` | `packRows4_length_le … ≤ 8908` | 152 |
| `FRNodeSound4R` | `segTr_length`, `slotTr4_length`, `aggTr_length`: 8,907 | 287 |
| `FRVerifierImplNode4T` | `nodeE4_ctrl`: `aggB 1 = 0x1750C0` reads bit 12 as `1`, bit 13 as `0` (was 0x16A000's 13/12) | 404 |

The last six rows are literal-only fixes. They are in modules that no running track owns (A1′ and
B2′/B3 come later), and each number follows from the new stream length. No statement changed
meaning. Touched: 18 modules, 4,288 → 4,416 code lines (+128).

**The construction (`FRVIRFinals4.capChkOps`, registers from `b`).**
- Head: the K constants `1`, `0`; `ζ = chK` of P3.4's first answer (`(lvOuts fi 4 4)[1] − 1`);
  `z = chK` of CapChkZ's answer; `z^{2^t}` for `t ≤ capMax = 9`; the level weights `z^{offᵢ}`
  (`offᵢ = 0, 512, 768, 1024, 1280`).
- **Reads `r = 0 … 870`**, in item order (levels 0…4, positions 0…tᵢ − 1). Each read does:
  - `splitDigest cur_r`;
  - `aL += ζ^r·lo`, `aH += ζ^r·hi` (`mulKF`, `addK`);
  - `aZ += ζ^r·z^{offᵢ}·Π_t sel(bit t of k_r, 1, z^{2^t})` (`bitOf`, `selectHalf`, `mulK`; `capᵢ`
    bits);
  - `ζ^{r+1}`.

  Width `9 + 3·capᵢ`.
- **Entries `k = 0 … 1407`**: `A_k = piElemK fA (32k)`; `cap[k]`'s halves are `piElem fCaps (32k)`
  and `(32k + 16)`. Then `sL += A_k·lo`, `sH += A_k·hi`, `sZ += A_k·z^k`, and `z^{k+1}`. Width 10.
- Then `assertEq aL sL`, `assertEq aH sH`, `assertEq aZ sZ`.

This is PACK §3.3's (I) per F half and (II). At `seq4` it is 42,464 ops (the KAT's count). It reads
no kind table (`map_at_capChkOps`), so the group programs stay op-for-op the kinds' programs
(`progNodeGK_exec`, `progSegG_exec` reprove unchanged).

## 2. Build and kernel times

- **Baseline** (HEAD, `logs/A2p/base-build.log`): `lake build FR Solution FRSoundness4TailShift
  FRSoundness4XCtrl FRNodeSound4Ctrl vtime4 plan4t` green, 4,940 jobs.
- **Now**: the 18 touched modules build (`b.sh` on them: green, 2,456 jobs).
- **The clean worktree state** (`logs/A2p/build-final.log`): `lake build FR Solution
  FRSoundness4TailShift FRSoundness4XCtrl FRNodeSound4Ctrl` fails in exactly two modules, both
  A3′'s:
  - `FRSoundness4TailD`: `phOf_ge`, `rounds_check`;
  - `FRSoundness4R4Run`: `fsMsgs4_len`, `fsCheck_qOf`, `matches_fsQ4`, `finOps4_eq`.

  Everything else that fails is downstream of these two (§5).
- **S-H4's new modules** at HEAD `4d5700c` (`FRXDec4Msg`, `FRXDec4Map`, `FRXRead4`, `FRXDec4Lv`,
  `FRXLagT`) build against this change.
- **The breakage scan.** It runs in the build tree only (`logs/A2p/scan/`). Each round sorries
  the failing proofs in `logs/fr-build-A2/src/` copies. Statements change only in four places,
  and only to drop `posOps4`'s removed argument: `scan/copies/*.diff`. The scan reaches
  `FR Solution FRSoundness4TailShift FRSoundness4XCtrl FRNodeSound4Ctrl` green, 2,581 jobs
  (`scan/build-12.log`).
- **Sequential profiles** (`lean -DElab.async=false --profile`, one core, load ≈ 20;
  `logs/A2p/profile-*.log`, summary `profile-summary.txt`). The comparison column is S-I's
  per-module seconds on the 7763 (`build-modules.txt`):

**Paired, at load ≈ 3** (the module and HEAD's text of it, back to back on core 26, against the
same dependencies; `prof-cmp-*.log`). These are the two modules with new definitions and decisions:

| Module | HEAD | now | note |
|---|---|---|---|
| `FRShape4` | 27.3 s (elaboration 11.8, type checking 7.4) | **24.3 s** (elaboration 3.9, type checking 9.5) | `phasesOf`'s `++` chain took ≈ 12 s of elaboration at HEAD and ≈ 19 s with the cap check appended; one type ascription on its PIOP literal brings it to ≈ 1.4 s. +2 s of kernel for the new `decide`s |
| `FRVIRFinals4` | 19.7 s | **20.3 s** | the generators written with `Op.` constructors: the dot forms cost ≈ 8 s of elaboration (`prof-F4*.log` bisection) |

**All 18 touched modules, sequential profile at load ≈ 20–37** (`profile-*.log`). Other agents' work
(P2's prover on 23 cores, two Lean builds) shared core 26 during this run, so wall times and phase
totals are inflated and noisy: `FRVIRFinals4`'s 1:47 is 20 s at low load (above). The phase
columns are the profiler's cumulative seconds:

| Module | wall (m:s) | import | elaboration | type checking | tactic | S-I (7763, s) |
|---|---|---|---|---|---|---|
| `FRTranscriptDefs` | 0:25.80 | 4.2 | 1.2 | 8.9 | 2.4 | 17.0 |
| `FRShape4` | 0:23.85 | 4.9 | 2.8 | 9.6 | 0.9 | 23.0 |
| `FRVIR4` | 0:21.35 | 4.2 | 11.4 | 1.1 | 0.0 | 11.0 |
| `FRVIR4Mux` | 0:14.23 | 6.2 | 2.5 | 0.1 | 0.3 | 8.1 |
| `FRVIRFinals4` | 1:46.77 (20.3 at load 3) | 4.1 | 6.7 | 7.1 | 48.7 | 25.0 |
| `FRVIR4At` | 0:45.88 | 13.0 | 2.3 | 1.9 | 7.4 | 8.2 |
| `FRVIR4Uni` | 0:25.45 | 8.2 | 3.6 | 0.3 | 2.3 | — |
| `FRX4Prog` | 0:27.43 | 10.4 | 0.4 | 1.0 | 1.2 | 5.0 |
| `FRX4Ext` | 0:18.56 | 4.5 | 0.6 | 1.9 | 2.8 | 9.2 |
| `FRSoundness4Pos` | 0:29.98 | 4.8 | 0.8 | 17.5 | 0.7 | 16.0 |
| `FRSoundness4Qry` | 1:29.85 | 7.2 | 0.8 | 1.0 | 1.5 | 18.0 |
| `FRNodeLayout4` | 0:24.51 | 5.6 | 0.3 | 14.7 | 0.2 | 14.0 |
| `FRNodeKinds4` | 0:47.91 | 7.2 | 1.8 | 4.4 | 7.4 | 14.0 |
| `FRVIRTpl4Bridge` | 0:11.58 | 5.5 | 0.2 | 0.1 | 0.3 | 4.1 |
| `FRNodeRows4Pack` | 0:10.53 | 5.0 | 0.1 | 0.2 | 0.3 | — |
| `FRVerifierImplNode4T` | 0:17.09 | 5.5 | 0.5 | 2.0 | 2.2 | 10.0 |
| `FRNodeRows4` | 0:11.96 | 6.4 | 0.3 | 0.2 | 0.1 | 6.9 |
| `FRNodeSound4R` | 0:13.97 | 6.5 | 0.3 | 0.4 | 0.7 | — |

The literal-only modules change no proof's work: their `decide`s evaluate the same expressions at
other numbers. **Net Δ CPU-s of this track's Lean: ≈ −2 s** on the paired measurements (`FRShape4`
−3.0, `FRVIRFinals4` +0.6; the rest literal), against the brief's +10. A3′'s restatements are not
counted here.

## 3. Measurements

| | before (HEAD) | after | log |
|---|---|---|---|
| V(N4) `vtime4 21 n4f` best (core 30) | 233.3 / 237.6 ms (load ≈ 14) | **513.2 / 516.5 ms** (load ≈ 21) | `vtime4-base-{a,b}.log`, `vtime4-after-{a,b}.log` |
| `evalMT4 N4` best | 132.0 / 121.9 ms | **365.8 / 355.9 ms** | same |
| `plan4t init` (core 29) | 2.22 / 2.57 / 2.48 s, `inR true` | **4.17 / 5.27 / 4.59 s**, `inR true` | `plan4t-init-{base,after}-*.log` |
| `plan4t check` | — | `inR true`; `evalMT4` = the sparse sum for N2, N4, N8 (`equal true`) | `plan4t-check.log` |
| prototype rows in region (p0 / p1) | 730,493 / 725,885 (S-E13a) | **787,837 / 783,229** | `nodedump4-run.log` |
| plan pieces: sparse rows / instances (p0) | 40,064 / 5,396 (S-E13a) | **133,803 / 4,530** | `planform4-run.log` |
| `progNode .N4` ops / registers | 106,485 / 97,657 (INT-9) | 147,211 / 140,122 | `protodump-run.log`, `prof4-after.log` |
| V's native cap-check ops (per run) | — | ≈ 9 ms: `mulK` +11,703, `addK` +6,837, `piElemK` +1,408, `piElem` +2,816, `selectHalf`/`bitOf` +7,132, `mulKF` +4,558, `splitDigest` +871 | `prof4-after.log` |

**Reading the regression.**
- `evalMT4` evaluates the prototypes' M rows per slot. The cap check adds about 58.8 k compiled rows
  per prototype, and none of them is templated. That template work is B2′'s in PACK §5/§7
  (`tplPowChain`, `tplBitPow`, `tplMacShared`).
- The sparse rows grow by 93.7 k, while instance pieces fall by 866 (5,396 → 4,530). So about 35 k
  of the old instance rows became sparse.
- My reading, not checked against the plan builder's code (B0/L-circ's): the per-position Merkle
  blocks were grouped as instances of one key while their last cell (`cur`) was read only inside
  the block (by the old `assertEq`). Now the cap check reads `cur` from outside the block, and the
  grouping no longer applies.
- B2′'s arena design (PACK §5.2) addresses exactly this. Until it lands, **V(N4) is ≈ +280 ms and
  `plan4t init` is over its 2 s bound (PK-m6)**.
- The load differed (≈ 14 → ≈ 21). The `evalMT4` delta is far larger than load noise.

## 4. Controls, KATs, dumps

**Kernel controls (new).**
- `capChkPh_ctl` (+/−): `seq4` has `[("CapChk", .absorb fA 45088), ("CapChkZ", .squeezes 1 .one)]`;
  `seq3` has none.
- `capChk_aligned`: the two items take a multiple of 64 stream bytes.
- `capEntries_seq4`: 1,408 entries, `A` 45,088 B.
- `capChkOps_off` (−): no cap check at `seq3`.
- `capChkOps_head` (+): `capMax seq4 = 9`, and the head's four one-register ops.
- `finOps4_seq3`: 3.x's finals are unchanged.
- `piSizeOf_seq3`: 3.x's size is unchanged.
- The existing `nodeE4_ctrl`, `protoR_ctl` and `fsItems4_ne` stand, at the new numbers.

**The cap-check KAT** (`IRDumpA2 capkat`, `dump/capkat.txt`; runtime, not kernel). Setting:
- `capChkOps seq4` is run (relocated, through `exec`) on a proof whose caps are 1,408 pseudo-random
  digests;
- there are 871 reads with pseudo-random cap indices, whose path digests are the cap entries;
- `A` is honest.

Result:
- (+) The honest `A` is accepted.
- (−) `A_0 + 1` is rejected.
- (−) A read whose path digest is one byte off is rejected.

**Dumps** (`logs/A2p/dump/`, `SHA256SUMS`; tool `IRDumpA2.lean` = INT-8's plus `capkat`, script
`logs/A2p/dump.sh`): `ops-{L30,L31,L32,N2,N4,N8}.txt`, `group-{N,S}.txt`, `items.json`,
`summary.txt`, `fsummary.txt`, `last.txt`.

| Kind | file | ops | skeleton | finals (incl. the cap check) | registers | asks = items | items |
|---|---|---|---|---|---|---|---|
| L30 / L31 / L32 | `ops-L3*.txt` | 146,963 | 60,405 | 86,557 | 139,874 | true | 8,907 |
| N2 / N4 / N8 | `ops-N*.txt` | 147,211 | 60,313 | 86,897 | 140,122 | true | 8,907 |

Against INT-8's group-uniform dumps (L30: 106,237 ops), the difference is +40,726 ops. It is made
of −1,742 (two ops per position), +42,464 (`capChkOps`) and +4 (`CapChk`'s `piField`/`askAbsorb`,
`CapChkZ`'s `askSqueeze`/`chF`). `piDigestAt`: 0 in every `ops-*.txt` (INT-8: 871).
`summary.txt`: `fieldSizes` has 19 entries ending in 45,088; `piSize` 843,280; `streamBytes`
1,528,000; `chainLen` 23,875; `fieldOffs[18] = 798,192`; fsItems 484.

**The KAT's numbers** (`dump/capkat.txt`): 42,464 ops, 43,332 registers; 871 reads, 1,408 entries;
751 nonzero `A` entries (the first is entry 256, `6873…38d2`); honest `ok true`; both negatives
rejected.

`items.json` has 8,907 items. The last two are `CapChk` (`absorb`, `len` 45,088, `qlen` 45,128)
and `CapChkZ` (`squeeze`): stream items 8,905 and 8,906 (0-based), Fiat–Shamir positions 482 and
483 (`fsStarts4_eq`).

**Node dumps** (`logs/A2p/nodedump/`). They are made by `nodedump4`, `planform4` and `protodump` with
a **locally regenerated hint** (`laydump4`, `logs/A2p/laydump4.log` → `logs/A2p/FRNodeRows4Hint.lean`,
copied into the build tree only). `FRNodeRows4Hint` is B0's module: see §6.
- The plan-form KAT `planform_kat.py`: prototype 0 662,195 rows rebuilt, 0 differ; prototype 1
  652,492 rows, 0 differ; **KAT PASS** (`planform-kat.log`).

**Source rule**: `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`: 362
files, 0 findings. **Axioms**: `logs/A2p/axioms.log` (43 theorems of the touched modules: `propext`, `Classical.choice`, `Quot.sound` or fewer; no `sorryAx`).

## 5. For A3′: the broken theorems, exactly

**Method.** In the build tree only, each failing declaration of a non-A2′ module had its proof
replaced by `sorry`, round by round, until the build was green (12 rounds, `scan/round-*.txt`,
`scan/build-*.log`). Four statements were edited in the scan copies, each only to drop the
removed `capO` argument of `posOps4` (`scan/copies/*.diff`). They are marked † below.

**The build failures (the complete list: with these 13 sorried, `FR Solution` builds):**

| Module | Declaration | Why |
|---|---|---|
| `FRSoundness4TailD` | `phOf_ge` | `468 ≤ p → phOf4 p = 51` is false: `phOf4 482 = 52`, `phOf4 483 = 53` |
| `FRSoundness4TailD` | `rounds_check` | `fsItems4.length == 482` → 484 |
| `FRSoundness4TailC` | `tailCls_check` | positions 482, 483 (CapChk, CapChkZ) are in no class |
| `FRSoundness4R4Run` | `fsMsgs4_len` | 482 → 484 |
| `FRSoundness4R4Run` | `fsCheck_qOf` | the statement's own bound proof (`q < 482` against `fsItems4_length = 484`) |
| `FRSoundness4R4Run` | `matches_fsQ4` | `es.length = 482` |
| `FRSoundness4R4Run` | `finOps4_eq` | false: `finOps4 P = (relocFin P.S (finalsOf P)).ops ++ capChkOps…` now |
| `FRSoundness4R4Outs` | `opsOut_posOps4` † | `posOps4`'s signature; `posW4` is `4 + 6·sL + 1` |
| `FRSoundness4R4Outs` | `genPhase4_out_lt` | proof only (`opsOut_posOps4`'s arity) |
| `FRSoundness4R4PosT` | `exec_posOps4` † | false: the reference `posT4` still compares with the cap entry |
| `FRSoundness4R4PosT` | `exec_posAll4` | the same, `t` positions |
| `FRSoundness4R4Qv` | `exec_queries4` † | the same, the queries phase |
| `FRSoundness4R4Qv` | `queries_view4` | false: its last conjunct, a path on `L` to π's cap entry, is no longer checked by the run |

**Statements that are now false but compile behind those sorries** (the scan cannot see them;
from their statements and the dependency graph):
- `FRSoundness4R4Cols.ys_facts4` → `cols4_of_run` → `FRSoundness4R4LinkP.finRest4_of_fields`,
  `link4_of_fields`.
  - These give `FinRest4.cols`/`FinLog4.cols`'s `(openPath …).runLog L = some (capDig …)` from the
    old per-position assert. This is PACK §9.1 (a)'s restatement: a computed `pathDig`, plus
    `capChk4`.
  - `posReg4` (`FRSoundness4R4P4`) only needs `queries_view4`'s index part; its statement holds.
- `FRSoundness4TailD.phOf_bounds` (`phOf4 p ≤ 51`) and its users:
  - `FRSoundness4TailC` (`chainStab_of`, `phOf_ge_26`, `phOf_lt_26`, `phaseObl_of`);
  - `FRSoundness4P4aDF` (`hstab4a`, `phOf4_eq`);
  - `FRSoundness4P4fObl` (`chain_hi`, `hstab_hi`);
  - `FRSoundness4XFront` (`frontChainStab_X`, `phOf4_le12`).
- `FRSoundness4TailC.tail_cls` (→ `phaseObl_of`); `FRSoundness4TailM.DT_stab` (`≤ 51`: the DT
  table needs phases 52 and 53, PACK §9.1 (b) `DT 52 := D_z`, plus CapChk's absorb phase);
  `FRSoundness4TailStep.phOf_examples` (`481 → 51`).
- **Every `482` in an R4 statement must become 484.** `FRSoundness4R4At.SkRun4` (`len : … = 482`,
  `hq : ∀ q < 482`), `R4Run.runLog_chain4`, `R4Tail.acceptTail4_of_finLog` (`hlen = 482`). At 482
  these are vacuous (an accepted run has 484 Fiat–Shamir entries), not merely unprovable.
  `R4FrE.msg_abs4 (hq : q < 482)` stays true. List: `scan/` and the grep in the journal §4.
- `R4Acc.fields_of_accept4`, `R4Fld.fields4_of_accept` and `R4Ex.fields_ex4` use `finOps4_eq`.
  Their statements (the finals' fields pass on an accepted run) stay true, because `capChkOps` runs
  after every field. Their proofs must split off the appended ops.

**What A3′ needs from this track, by name.**
- The registers:
  - `curOfY sL y` / `kOfY sL y` (`FRVIR4`) are the path digest and cap index of the position whose
    column fold is `y`. `y` is `ysOf fi i`'s entry, exactly as `yReg4`.
  - `ζ`'s register is `(lvOuts fi 4 4).getD 1 0 − 1`: P3.4's first squeeze answer. Its two F
    coordinates are T4's `kcAt es 4 0` and `kcAt es 4 1`, so **`ζ es = chK (ansAt es (P3.4's first
    position))`**. `kcAt` is an F coordinate, not a digest: PACK §9.1's `chK (kcAt es 4 0)` is to
    be read this way.
  - `z`'s register is CapChkZ's answer: Fiat–Shamir position 483, phase 53.
  - `A_k` is `piElemK fA (32k)`, relocated to `fieldOffOf seq4 18 + 32k = 798,192 + 32k`.
- The phases: CapChk is phase 52 (FS 482, absorb `fA`, 45,088 B) and CapChkZ is phase 53 (FS 483,
  one squeeze). PACK §9's "phase 52, FS 470" is 3.x numbering: in `seq4` the cap check's squeeze
  is **phase 53 at FS 483**, and `phOf_ge`'s split is `468 ≤ p < 482 → 51`, `482 → 52`,
  `483 → 53`.
- The doom rows: `D_ζ` at P3.4's first squeeze (`870/2^256`, row 0 today), and `D_z` at phase 53's
  squeeze (`1,407/2^256`, not `1,919`: degree `< 1,408`).
- `finOps4 P outs b Q = ((finalsOf P Q).ops outs b ++ capChkOps P.S outs (b + opsOut …)).map
  (reloc P.S)`. The finals' registers do not move, and the cap check's start is the finals' end.

**Transitional option (asked).** The old per-position assert could be kept alongside, but it would
keep `piDigestAt`, the dynamic read B2 exists to remove. The chain would break anyway: the two new
Fiat–Shamir phases break `phOf_ge`, `rounds_check`, `tailCls_check` and `fsMsgs4_len`, and the
appended finals break `finOps4_eq`. It would also cost a second program change and a second
regeneration of the dumps. So it was not done.

## 6. For P2 (`prover/`) and for B0/B2′

- **The format.** Field 18 `A` holds 45,088 bytes at offset 798,192 (the old end), and `|π| =
  843,280`:
  - `A_k` for `k < 1,408` is 32 bytes, `K.toBytes` of `Σ_{r : offᵢ₍ᵣ₎ + k_r = k} ζ^r`.
  - The 32 bytes after them are zero.
  - `r` is the read ordinal in item order: level 0's 290 positions, then 178, 145, 132, 126.
  - `k_r = j_r >>> sib_κ(i)`, the kind's depth.
  - `ζ = K.ofBytes` of P3.4's first squeeze answer.
- **The transcript.** After `Pf`'s last squeeze, absorb `A` (`"FRABS000" ‖ st ‖ A`, `|q| = 45,128`),
  then one squeeze. The stream is 1,528,000 = 64 · 23,875 bytes, still whole blocks.
- **V's program** (`ops-*.txt`):
  - Per position, the trailing `piDigestAt` and `assertEq` are gone; the position ends with `shrN`.
  - After the kind's final tail check, 42,464 cap-check ops follow, all of them existing op kinds:
    `const` (K), `chK`, `mulK`, `addK`, `mulKF`, `splitDigest`, `bitOf`, `selectHalf` on K values,
    `piElemK`, `piElem`, `assertEq`.
  - `ir.rs`'s `selectHalf` is already generic over values.
- **The node witness.** The prototypes gain the cap check's rows (`mrows-p*.txt` regenerated).
  The plan-form KAT passes against them.
- **The honest-witness KAT P2 should run:** `dump/capkat.txt` gives the KAT's setting and its
  result. The reference computation of `A` is `capKat` in `IRDumpA2.lean`.
- **`FRNodeRows4Hint` (B0's) must be regenerated** with `laydump4` in the same commit as this
  change. The regenerated file, for HEAD's compiler, is `logs/A2p/FRNodeRows4Hint.lean`.
  - Measured with HEAD's stale hint (`plan4t-init-stalehint.log`): `inR false`, and a 39.5 s plan
    start.
  - B0 has uncommitted changes to the same file in the worktree. Whichever of the two lands second
    reruns `laydump4`.
- **B0's target (≤ 640 k rows per prototype) moves**: the cap check adds about 57 k rows per
  prototype (787,837 / 783,229 in the region now).
- **B2′**: the cap check's templates (PACK §5), and the loss of about 866 Merkle-block instance
  groupings (§3).
- **`reassemble` (S-H4), row 18.** No revision-4 `reassemble` exists in the tree yet. When it does,
  row 18 is the CapChk absorb's message: item 8,905 (0-based), query bytes `40 … 40 + 45,088`, all
  of it, the 32 zero bytes included. A generic `rsPhase` over `phasesOf seq4` with 19 output fields
  does this with no special case (`.absorb fA len => put fA (qBytes tr ix 40 len)`).
- **For A1′.** The 129-B spacer still aligns, since the stream is still `≡ 0 mod 64`.
  - `segB = 1,528,000`, `cLen = 23,875`.
  - `aggB k = 64·(23,877k − 2)`, `aggL k = 23,877k − 2` (stride 23,877).
  - `hUsed`: N2 = 73,078, N4 = 121,130, N8 = 2·95,506 + 2,196 = 193,208, so N8's `lBase` is
    193,280 ≤ 195,584: **2,304 blocks to spare** (PACK's 256).
  - `qV` is 35,631.

## 7. Deviations from the brief

1. `A` has 1,408 K elements (F1), so the constants differ from PACK §3.3's: `piSize` 843,280, the
   stream 1,528,000 = 64 · 23,875, `D_z` 1,407/2^256. **The orchestrator must rule.**
2. The accumulators are in the finals (`capChkOps`), not in `posOpsG` (D2: `ζ` and `z` come after
   the positions).
3. No `powIdx` op (D1).
4. `finCap` is not a `Finals` field. `Finals` is 3.x's structure (`FRVIRFinals`), and adding a field
   would change every 3.x construction and `Finals.ops`. Instead, `capChkOps` is appended after
   `Finals.ops` inside `finOps4`/`finOps4F`. No finals register moves.
5. The phases are in `FRShape4.phasesOf`, gated by `Seq.capChk`, not in `FRTranscriptDefs.phases`
   (3.x's 8,891-item table, still used by 3.x modules). `nFields` stays 18; `nFields4 = 19`.
6. The phases are 52 and 53 at FS 482 and 483, not "phase 52 at FS entries 469–470": PACK §9 uses
   3.x's FS count.
7. Literal-only fixes in six modules outside the brief's list (§1), whose numbers follow from the
   stream. This was needed to reach A3′'s boundary.

## 8. Open questions

1. F1: confirm 1,408 entries and `A` = 45,088 B (or rule the memo's 61,472 with its 16 KB pad).
2. V(N4) +280 ms and `plan4t init` ≈ 4.6 s, both until B2′'s templates land. Is that acceptable
   as an intermediate state, or should B2′ be pulled forward?
3. Who regenerates `FRNodeRows4Hint` (B0's), and when: with B0's own regeneration, or at this
   commit?
