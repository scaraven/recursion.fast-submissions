# A1′ (R-A′: the spacer query between an aggregate's segments) — RESULT

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`. Started at `face798`, rebased onto
B5's `9a41aac` (`FRNodeRows4Plan`, `FRVerifierImplNode4F` at that commit, unedited). Build tree
`logs/fr-build-A1`; logs in `logs/A1p/`. The journal is `A1p-JOURNAL.md`.

## 0. Summary

| Definition of done | Status |
|---|---|
| `Gap4R` loses `kindS`/`wf` at `i ≥ 1` | **Done.** `Gap4R` is now `imp` + `aggChk` only. `gap4_of_rows` proves `kindN`, `kindS` at every sub-slot and `wf` for every segment and spacer, from the pack rows. |
| `aggChainLen_eq`'s residues are 0 | **Done.** 48,474 / 72,712 / 96,950 blocks for `k = 2 / 3 / 4`, residue 0 each. `aggChainLen_eq`'s fifth conjunct is a negative control: the residue is 63 without the spacer. |
| `hUsed_eq`, `regions_fit` by `decide` on literals | **Done.** `hUsed` is 74,015 / 122,497 / 195,220. N8 `lBase` is 195,328 ≤ 195,584 (in `regions_fit`): **N8 still fits**, with 256 blocks to spare, the same as before. |
| The aggregate controls with spacers | **Done.** `ctrlA_pos` (with the spacer entry), `ctrlA_no_spacer` (−: the empty trace is rejected), `aggTrace_ctl`, `spAt_ctl`, `decRow_ctl`, `packB_ctl`. |
| B2″'s arena literals (`arN` comes from `chainLenOf seq4`) | **Unchanged.** `arN` is still 96,944: the spacers change `V_A`'s program, not `seq4`. `arenafit` and `cellfit` show the same placement as RSV-V2, with 0 overlaps. |
| The hint regenerated last | **Done.** `laydump4` + `mkhint.py`. Only `maskN`'s route literal moves (96,944 → 96,950; 48,472 → 48,474). `plan4t init` gives `inR true`. |

Axioms: 56 key theorems and controls, each using only {`propext`, `Classical.choice`,
`Quot.sound`} or a subset; no `sorryAx` (`logs/A1p/axioms.log`). Source rule: 407 files, 0
findings (`source-rule.log`).

**Build caveat.** HEAD is red at RSV-S's declarations. Five proofs fail: `FRSoundness4R4Fin.flag_gFinE` and `flag_gFinB'`,
`FRSoundness4Qry.noAsk_gFinE`, `noAsk_gFinB'` and `noAsk_gFinPf`. In addition, `FRSoundness4R4FrE.fsMsgs4_ends` and
`FRSoundness4R4PfFlag.gFinPf_reloc` fail. My node chain imports them, so my build tree replaces those
proofs by `sorry` in the tree's copies only (`logs/fr-build-A1/scaffold/apply.sh`; the worktree is
untouched). The axiom check shows that none of my theorems depends on them. Also red at HEAD and
not mine: `FRNodeLinks4` (`FinLog4.mk` arity), `FRNodeRun4S` (stale `8905`), `FRXChain4` and
`FRXDec4Levels` (RSV2's `fsMsgs4`). Everything downstream of `FRXChain4` (the decoder) was **not
built**; see "For the decoder port".

## 1. The constants (from today's `seq4`)

- A trace is `segB − 1 = 1,551,103 ≡ 63 (mod 64)` bytes. The spacer's entry is `enc64 89 ‖ absorbQ 0³² 0⁴⁹ ‖ a`
  = 8 + 89 + 32 = **129 ≡ 1 (mod 64)** (`spacer_entry_length`, `spacerBytes_eq`). **129 B is correct**:
  the stride is `1,551,232 = 64 · 24,238` (`strideB_eq`). A single absorb spacer must be
  `80 + len ≡ 1 (mod 64)`, and `len = 49` is the smallest such length.
- Segment `i` starts at `1 + i·strideB`, so sub-slot `i`'s stream is sub-slot 0's shifted by `24,238·i` blocks.
  `aggB k = 1 + k(segB − 1) + (k − 1)·129 = 64·(24,238 k − 2)` (`aggB_blocks`).
- `qV`: `4 · 8,783 + 3 = 35,135 ≤ 36,000` (`traces_spacers_le_qV`, already in `FRShape4`).
- `hEnd` is 74,017 / 122,501 / 195,228, each ≤ `lBase` (`hEnd_le`).

## 2. A deviation: two elements per spacer are not whole constants

An entry ends with its 32-byte answer, which is random under the ROM and cannot be pinned. A segment
starts right after an entry, and the spacer starts at `≡ 0 (mod 64)`. Two elements are therefore
mixed, and this holds for **any** spacer:
- **spacer element 6** = the query's last byte (`msg[48] = 0`) followed by answer bytes 0–14;
- **sub-slot `i ≥ 1`'s element 0** = answer byte 31 followed by `enc64 119 ‖ "FRSEED0"`. This is the seed's length word,
  which `wf` needs. For segment 0 this byte is the stream tag `0x54`, so the element is constant.

So the brief's "9 whole-element pins" and "`wf` at `i ≥ 1` by the shifted lemmas" do not suffice.
Each spacer gets **136 head rows** (`FRNodeRows4Pack.headRows`):
- 6 whole pins (elements 0–5);
- 120 Boolean cells packed at bits 8–127 = element 6, so byte 0 is 0;
- 8 Boolean cells at bits 0–7 plus `seedM` = sub-slot element 0, so bytes 1–15 are the seed's.

The 128 Boolean cells per spacer are exactly the L cells that S-E13b's `padRows` element-7
decompositions used (`pbC κ σ (s+1)` = `spC κ σ s`). R-A′'s whole blocks free them. Segment 0 of a stream
instead pins its element 0 whole (`seedW`), and `wfSeg` no longer contains element 0 (8,782 pins).
The controls are `decRow_ctl` (+: an element with any byte 0 decomposes; −: an element differing
in byte 1 fails for every Boolean choice) and `spAt_ctl`.

The pins are **not gated** by activity, so they hold at inactive sub-slots too (see "For P2"). Gating
them would change `linkV4`'s pinned-block form (`e1 = E(one)`), which belongs to B5.

## 3. What was built, file by file

Code lines from the core's `loc.py` (HEAD → now), in `logs/A1p/loc.txt`.

| Module | Change | Code lines |
|---|---|---|
| `FRAgg` | `spacerQ`, `spacer`, `spEntry`, `aggProgs := segProgs.intersperse spacer`; `VAwith` runs `seqAll (aggProgs …)`. `aggTrAt`/`aggTrace` (`aggTrace_range`, `aggTrace_length`, `mem_aggTrace`), `withSp`, `forall₂_intersperse`, `mem_intersperse_of_mem`, `segProg_mem_aggProgs`. `VA_sound` (over `aggProgs`), `VA_extract`/`_on` (by membership), `VA_complete` (on `aggTrace ans trs`, any answers), **`VA_queries_le : ≤ 4·qS + 3`**. Controls: `ctrlA_pos`, `ctrlA_no_spacer`, `aggTrace_ctl` | 388 → 537 |
| `FRVerifier4` | `V4_queries_le`/`ks_queries4` take `4·qS + 3 ≤ qV4`; `spacerBytes_eq` | 170 → 172 |
| `FRNodeLayout4` | `spacerBytes`; `aggChainLen` with `(k−1)·129`; `aggChainLen_eq` (residues 0, and 63 without the spacer: −), `_k3`, `hUsed_eq`, `hUsedN8At`, `regions_need_levers` | 59 → 66 |
| `FRNodeKinds4` | `spacerB`, `strideB`, `sBlk`, `aggB`, `strideB_eq`, `aggB_succ`, `aggB_blocks`, `hEnd_eq`; `main_not_final2` restated (the counter now matches; the final flag does not) | 393 → 406 |
| `FRNodeRead4` | `segTr` at `1 + i·strideB`; `spItem`, `spAnsB`, `spAns`; `sgn4`'s aggregate trace is `aggTrace (spAns …) (sub-slot traces)` | 69 → 75 |
| `FRNodeRead4W` | `SpAt`, `spacer_bytes`, `stream_of_wf` with spacers (prefix induction) | 78 → 143 |
| `FRNodeCircuit4` | `NodeResid4.aggTr : ∃ ans, tr = aggTrace ans (…)`; `agg_acc` through `VA_complete … ans`. `AggPad4` is kept as defined (its `r` is 64 for `1 ≤ k ≤ 4`) | 307 → 308 |
| `FRNodeSound4R` | `Gap4.wf` with `SpAt`; `chainMsg_of_wf`; `aggTr_length` (`k·8,783 + k − 1`); `pack` against `traces_spacers_le_qV`; `sgn4_qcap` (spacer query 89 B) | 287 → 291 |
| `FRNodeSound4Ctrl` | the converse with spacers (`sgn4_tr`, `chain_len`, `wf_of_eq`, `wf_of_chainMsg`) | 202 → 278 |
| `FRNodeRows4Pack` | `wfSeg` without element 0; `seedW`, `seedM`, `spBytes`, `spPin`, `boolRow`, `packAt`, `decRow`, `headRows`, `spC` | 83 → 102 |
| `FRNodeRows4` | `packB` for **every** slot (`chBase + subIx·sBlk`), `segIx`, `packHead4` = kind tie :: `headRows` | 152 → 156 |
| `FRNodeRows4Fit` | `packB_fit` (one `decide` per kind), `packRows4_cells` re-proved | 367 → 443 |
| `FRNodeRows4Wots`/`Ext`/`Agg`/`WotsCtrl` | `padRows` without the element-7 decomposition (6 rows per candidate); `xRows_length` 7,862 / 7,878 / 7,904; `gap4_aggPad` re-proved (`lastR_64`); `lastR_eq` (all 64), `lastR_no_spacer` (−) | Agg 146 → 83 |
| `FRNodeRows4PackSound` | `agg_elem`, `segi_elem`, `spc_elem`, `wfData_shift`, `HeadOk`/`headOk_of`, `wfSeg_of_pins`, `spAt_of_pins`, `kind_byte` (any segment), `wf_of_rows`; **`Gap4R` = `imp` + `aggChk`**; `gap4_of_rows`. Controls `spAt_ctl`, `decRow_ctl`, `packB_ctl` | 370 → 606 |
| `FRNodeTarget4C`, `FRVerifierImplNode4T`, `FRVIRTpl4Bridge` | literals that follow (`aggB_lt`; `nodeE4_ctrl`: `aggB 4` is now even, so bit 7 is 1 and bit 0 is 0; `protoR_ctl`'s route) | ±1 |
| `FRNodeRows4Hint` | regenerated (`maskN` route) | — |

## 4. Measurements

All measurements were taken on the shared VM, under load from the other tracks.

**Correctness of the fast evaluator** (`plan4t check`, `logs/A1p/plan4t-check.log`). At B5's plan, with my rows,
`evalMT4` equals the sparse sum over `nodeIRows4` on every kind:
- N2: 136 ms vs 160 s;
- N4: 157 ms vs 261 s;
- N8: 121 ms vs 437 s.

All three report `equal true`. `plan4t init` gives `inR true` in 5.3 s (`plan4t-init-b5.log`).

**V(N4)** (`abv.sh` = B5's `abv2.sh`, 4 rounds × 21 alternating, core 29, `vtime-ab.summary`). Best of runSeq, in ms:

| Support | B5 `9a41aac` | **A1′** | Δ |
|---|---|---|---|
| own kind (N4) | 258.3 | **266.6** | +8.3 |
| all three kinds | 281.9 | **307.2** | +25.3 |

The cause is that every aggregate sub-slot now has its own pinned block (8,782 pins and 137 head rows),
where before only sub-slot 0 had one. `evalMX4` at full support rises from 159.5 to 185.3 ms. B5's "+16–18 ms per extra kind" becomes about
+20 ms (N8 adds 6 more pinned blocks than N4). Medians are noisy under the load (B5 305 / 318, A1′ 321 / 349).
Lever (B5's, not taken): the pinned sums of sub-slots `i ≥ 1` differ from sub-slot 0's only by
the block offset `i·sBlk`, so `prVal_runs` could share one run set per kind and shift it.

**Probes**:
- `arenafit`: placement unchanged, 0 instances meeting the arenas.
- `cellfit`: 0 overlaps.
- `nodedump4`: prototypes 649,766 / 641,656 indexed rows. The new node dump is in `logs/A1p/nodedump/`.
- `laydump4`: only the route literal changes (`laydump4-1.log`).

**Per-module CPU** (`lean -DElab.async=false --profile`, one core; `cpu.txt`; HEAD's in `cpu-base.txt`
or RSV-V2's `cpu.txt`). Format: wall, kernel ("type checking"), now vs before.

| Module | Now | Before |
|---|---|---|
| `FRAgg` | 26.7 s, 8.1 s | 32.4 s, 7.7 s |
| `FRNodeLayout4` | 17.9 s, 10.0 s | 16.6 s, 9.8 s |
| `FRNodeKinds4` | 18.8 s, 2.5 s | 18.5 s, 2.3 s |
| `FRNodeRead4W` | 8.2 s, 0.5 s | 7.0 s, 0.2 s |
| `FRNodeSound4R` | 9.2 s, 0.3 s | — |
| `FRNodeSound4Ctrl` | 9.5 s, 0.7 s | 8.1 s, 0.3 s |
| `FRNodeRows4Fit` | 34.6 s, 2.6 s | 19.9 s, 1.9 s |
| `FRNodeRows4Agg` | 9.4 s, 0.6 s | 10.5 s, 1.9 s |
| `FRNodeRows4PackSound` | 21.5 s, 2.7 s | 18.2 s, 1.0 s |
| `FRNodeRows4Pack` | 7.3 s, 0.15 s | — |
| `FRNodeRows4` | 7.5 s, 0.15 s | — |
| `FRNodeRows4Ext` | 28.2 s, 18.1 s | — (the old `xRows_length` simp) |

Two kernel hot spots of my own were found and removed. A first version of `wf_of_eq` took **90 s** of kernel time,
because the kernel unfolded `aggB` against `i·strideB − 128`; it now generalizes `aggB i` and takes 0.7 s. An extra `lBase_eq`
cost 2.6 s; it was dropped and its values moved into `regions_fit`'s doc. Net Δ over these modules: about
+20 s of wall and +3 s of kernel.

## 5. For RSV-S (statement and proof changes in `FRSoundness4*`, verified in my build tree)

1. **`FRSoundness4Agg.VA_sound_log`**: the statement is **unchanged**. One proof line changes, because `V_A` now runs
   `seqAll (aggProgs …)`:
   `· next hc => exact ⟨hsz.1, vs, hvs, hc, fun p hp => runLog_seqAll h p (mem_intersperse_of_mem hp)⟩`
   (was `… runLog_seqAll h⟩`). INT-10's `SegSoundLog` and its size hypothesis `π.size = piSizeOf seq4`
   are unchanged and still discharged: `VAwith` keeps its size check, and `VA_sound_log` still returns it.
2. **`FRSoundness4Qry.ks_queriesC4`** (line 240 at HEAD): `ks_queries4`'s last hypothesis is now
   `4 * qS + 3 ≤ qV4`, so replace `exact traces_le_qV` with `exact traces_spacers_le_qV`.
No other `FRSoundness4*` module refers to `VAwith`, `segProgs`, the reader or the node layout.

## 6. For B5 / the orchestrator (`FRNodeRows4Plan`, `FRVerifierImplNode4F` at `9a41aac`)

- **Both build unedited against my modules**, including `linkV4_eq` and `extIRows`. Every slot still has
  one pinned block whose stream is exactly `wfSeg`, at its own `b0` (`packB κ σ = some (b0, G)`,
  `packWf4 = wfRows one b0`). The spacer rows live in `packHead4`, which `linkV4` evaluates
  generically (`linkHead4`). The key `(first row, block)` already distinguishes the sub-slots,
  because `b0` differs. `pinKeys` grows from the old set to one key per slot over the three kinds (at most 16). `innAt`'s `find?` over at
  most 16 keys was left alone.
- The runtime KAT and the V cost are in §4.
- `FRSubmission4Cert`'s doc table (line 23) still says that `Gap4R` contains "`imp`, `kindS`/`wf` at `i ≥ 1`, `aggChk`". It is now
  "`imp`, `aggChk`".

## 7. For the decoder port (`FRX*`, not edited and not built: downstream of HEAD-red `FRXChain4`)

What moves:
- **Segment offset** `i·(segB − 1)` → `i·strideB` (`strideB = 1,551,232 ≡ 0 mod 8`):
  - `FRXOut4W.vS` (`drop (i * (segB − 1))`) and its `hD` hypotheses: `vS_eq`/`vS_length` (lines 94–116) and `hD` (lines 196, 237–241, with the new `aggB`);
  - `FRXOut4P` lines 57–64 (`hnB`, `hD`) and 89;
  - `FRXOut4R` line 85 (the IR constant `toWord (N4c.segB − 1)`, which becomes `strideB`);
  - `FRXOut4R` lines 473–494 (`hlow`, `shWd … (i * (segB − 1) % 8)`, `hD : i·(…) < 2^23`; still true: `3·strideB < 2^23`).
- **The realign becomes trivial**: `i·strideB % 8 = 0` for every `i`. `realign κ`/`realign_sem` (44.8 s of kernel, H-cert3) and
  `cso_realign` (26,133,534 steps) can go; `FRXOut4C` (lines 80–93) and `FRXOut4Ctrl` (28–31) follow.
- **The aggregate's trace has the spacer entries**: `sgn4`'s trace is `aggTrace (spAns …) segs`. `FRXOut4A.aggTr`
  (the XIR) must emit `entryW (spacerQ, a_i)` before each segment `i ≥ 1`. `a_i` is the 32 stream bytes at
  `i·strideB − 31 … i·strideB`, at byte offset `≡ 1 (mod 8)`, so a 1-byte shift of 5 words is needed per spacer.
  `spacerQ`'s 89 query bytes are constants. In `FRXOut4W` (lines 244–275) `e2`, `hc` (lengths `k·8,783` → `+ (k − 1)`) and `ht` (the
  `flatMap entryW`) take the spacer entries.
- **Aggregate numbers**:
  - `FRXOut4A.aggL_eq'` (`aggL k = k(segB−1)/64 + 1`) becomes `aggL k = 24,238·k − 2` (`N4c.aggB_blocks`, `k ≥ 1`);
  - `dV` (line 223, `k·(segB−1)/2^6`), `chR_agg` (lines 227–243), lines 354–364 and 412–420 (`streamB`/`aggB` unfolds) follow;
  - `AggN` (`len`/`fb`/`fe`/`nb`/`cab`/`he` by `decide`) is re-decided with `aggL maxK = 96,950 / 48,474`; `nb`'s `(maxK−1)(segB−1)/8 + nW` becomes `(maxK−1)·strideB/8 + nW`.
- **Layout facts by `decide`** (H shifts by +2 blocks for N2, +6 for N4, +12 for N8 after the aggregate chain): `hEnd_fit`,
  `wb_fit` (FRXOut4P), `stC_ok` (FRXOut4O), `sel_ok` (FRXOut4A), `cso_*` (FRXOut4O 185–215: `cso_outIR4`'s
  bounds, `cso_aggHd`, `cso_kSel`); `FRXOut4P` line 101 (`23168 < hEnd`, a stale but true literal).
- Unchanged: `nW` (185,344, the segment's trace words), `pf4`/`reassemble`, `π_A`'s layout.

## 8. For P2 (the prover)

- **The aggregator inserts the spacer**: between consecutive segments the trace gets the entry
  `(spacerQ, H(spacerQ))`, with `spacerQ = "FRABS000" ‖ 0³² ‖ 0⁴⁹` (89 B). `tr_A` therefore has `k·8,783 + k − 1` entries and the
  signed digest covers it. `V_A` asks `4·qS + 3` at most.
- **H stream**: `0x54 ‖ tr₁ ‖ sp ‖ … ‖ tr_k` of `64·(24,238k − 2)` bytes. Every H address after the aggregate chain moves:
  `aggL maxK` is 48,474 (N2) / 96,950 (N4, N8), and `stmtB`, `wotsB`, `wmB`, `finB`, `cAB` and `hEnd` shift.
  `F_{a,k}` copies main block `aggL k − 1`'s whole message (no padding, no element-7 bits).
- **Pins at every sub-slot `i < maxK`, active or not** (ungated). The main chain's bytes after an active stream are
  free, so for `k < maxK` the prover writes the phantom constants there too:
  - for sub-slot `i` at block `b0 = chBase + i·24,238`: every item's first element (`wfSeg`: length word and tag), the kind tie at element 5
    (`Σ K_ι s′_ι`, which is 0 for an inactive sub-slot), and element 0 bytes 1–15 = `enc64 119 ‖ "FRSEED0"`;
  - for spacer `i ≥ 1` at block `b0 − 2`: elements 0–5 = `enc64 89 ‖ "FRABS000"` then 0s, and element 6 byte 0 = 0;
  - **L cells** `spC κ σ i q = lBase·128 + σ·2^14 + 11,264 + 128(i−1) + q`: `q < 120` holds bits 8–127 of spacer element 6
    (answer bytes 0–14), and `q = 120 … 127` holds bits 0–7 of sub-slot `i`'s element 0 (answer byte 31).
- **M link rows**: every sub-slot's link region now has 1 + 136 + 8,782 pack rows; segment-0 slots have 1 + 1 + 8,782.
  `padRows` has 6 rows per candidate. The new node dump is `logs/A1p/nodedump/` (`node-N*.txt`
  lists the link rows). The prototypes are unchanged, except for `maskN`'s route constants in the node
  program's template (the hint).

## 9. Open questions

1. Should the pins at inactive sub-slots be gated? Ungated pins cost P2 the phantom constants (§8),
   and they keep `linkV4`'s form. Gating would need B5's pinned-block form with an activity factor.
2. `FRNodeRows4ArenaPlace.a1Rows4` (B4) reads `b0` from `packB`. With R-A′ every sub-slot has one,
   so B4's arena binding applies per sub-slot unchanged (arena₁ element 0 is the masked element).
3. RSV-S's two one-line changes (§5) and the doc line in `FRSubmission4Cert` (§6).
