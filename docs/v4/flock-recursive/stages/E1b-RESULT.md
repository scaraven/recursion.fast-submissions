# E1b RESULT: the native prover brought to the node circuit at `3d9ae68`

Track E1b ran on 2026-10-30. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`.
- It started at HEAD `e447823` (SEG-R2).
- Its final dumps, blob and acceptance runs are at **`3d9ae68`** (FEL). The orchestrator asked for this mid-track.

| | |
|---|---|
| Prover | `submissions/flock-recursive/prover/` |
| Logs | `logs/E1b/` |
| Journal | `E1b-JOURNAL.md` |
| Lean tree | `logs/fr-build-E1b`: `.lake` copied from `fr-build-SEGR2`; sources from `git show <commit>:` by `snap.sh`, with no symlinks into the worktree; probes `probe/NodeDumpX.lean` and `probe/E1Verify.lean` kept in the tree |

Nothing was committed or pushed, and no sub-agents were used. Every lake, cargo or probe run ran in a 16 GB scope
with a timeout. No Lean source under `submissions/` was touched.

## 0. Summary

| Item | State |
|---|---|
| 1. Re-dump at HEAD, rebuild the blob, fill every new cell, KATs | Done at `3d9ae68`. **No per-stage port**: the prover now reads every new row family from the dump, and one generic fill solves their cells (§1). Results: `planform_kat` PASS, `plan-kat` equal (spare rows included), and **`mx-kat` PASS**: the prover's M̃ equals Lean's `evalMT4 planOf4` for N2, N4 and N8 at two random points. |
| Plan self-check (orchestrator) | `e1verify --plan` gives `inR true lk2/lk4/lk8.eok true (lkArr true/true/true) askRowsT 0/1 130914/154333 arR2N 154368 PLAN-CHECK OK`. It runs before every chain and stops the chain if it fails (`logs/E1b/r3/plan.txt`). Prototype 1 has 35 rows of slack. |
| 2. End to end with the Lean V at `3d9ae68` | **Every honest node proof is accepted and every canary rejected.** A kind-changing chain of 10 nodes, N2, N4 and N8 with k = 1/2/3/4 (§3.1). A stream of 9 requests through `rf-oracle`, starting with the full-length first step (§3.2). A second stream of 4 requests with the asm-linked `prover.s` binary (§3.2). The same chain was also accepted at `e447823` (§3.1). |
| SEG-R2 review S2/n1 (placement probed on N2 only) | **Closed by measurement**: N2, N4 and N8 proofs are accepted at `3d9ae68`. Slot 0's replay rows sit in the spare region (N2, N4), the segment slots' rows in SEG-R2's bands (every kind), and the Lean V checks all of it. |
| 3. Measurements and cap projection | §4. Worst first step ≈ 42–44 s against `step_s` 60 (1.36–1.43×). Projected `stream_s` at M = 96, including the harness's V start-ups and checks: **mean ≈ 1,650 s, max draw ≈ 1,810 s of 1,920 (1.06×)**. |
| 4. `cargo test` | 57 passed, 1 ignored (`logs/E1b/cargo-test-2.txt`). |
| 4. `prover.s` determinism | Two clean `build-asm.sh` runs give an identical file: **sha256 `09570a1be3657b30be221521d761260ee0e70793a657c7d252fff370b7346cc5`**, 34,708,237 B. `gcc -static -O2` takes 1.95 s on the VM (`logs/E1b/asm/det.txt`). |
| 4. PROVER.md caps | build ≈ 2 s (cap 120), setup 110–141 s on 12–16 VM cores (cap 240 on the runner; E1's 167 s on the VM was 60–70 s on runners), ready ≈ 1.5 s on the VM (cap 10), peak RSS 7.7 GB (cap 11 GB), setup directory 302 MB (cap 4 GiB). |

## 1. What changed (crate 18,560 `.rs` lines, +849 −157; `nodeblob.b64`, `prover.s` regenerated)

**The principle.** The prover takes every new row family from the dump. It solves their cells with one generic fill:
- the old one-unknown solve;
- a new **packing** solve;
- an inactive-slot rule.

Nothing is ported stage by stage. The exception is the placement formulas (`arR*`, `segRow`, `segCell`, `repMapC`). They are re-checked end to end by `mx-kat` against Lean's `evalMT4`.

| file | change |
|---|---|
| `mfill.rs` | **Rows.** The placement constants `AR_*`, `REP_B`, `seg_row`, `seg_cell` and `is_seg_local` (from `FRNodeRows4ArenaPlace` / `FRNodeRows4Defs`). `load_extra` appends to each prototype's rows, in this order: the ask-template rows (`mask-p{π}`: `askRowsT π` at `π·2^20 + arR2 + k`), the bit rows (generated: `bitRows`), and prototype 1's replay rows (`mrep-p1`, moved to SEG-R2's bands and local cells). Prototype 0's replay rows go to the new `Proto::spare` (frame cells as is, local `j` at `2^20 + j`). Helpers: `Rows::reopen`, `push_row`, `push_line_map`. |
| `mfill.rs` | **Fill.** Arena₁ (`AR_N` stream elements) is written at `arA1` before the solve. FEL's aliased `dotKF` imports write the same cells again, and equal double writes are a check (0 conflicts at `3d9ae68`). **`try_pack`**: when every unknown of a row sits in one form, once each, with distinct one-bit coefficients `x^j` and the rest known, each unknown is bit `j` of the known remainder. This covers IMPC2's decompositions `sel·(x + Σ x^h b_h) = 0` and the unaligned statement reads. With `want`, a replay entry writes its own bit only, so the level schedule stays valid. **Inactive slots**: no import is pre-set; the solve runs, the imports still unknown are zeroed (recorded as `ZERO_ENTRY` entries), and the solve continues. The order is replayed per request. **`spare_fill`**: slot 0's replay locals, by the worklist over `spare`, in gate order, every row checked. **`KindTab`**: `base_links`; `links_by_cell` (a counting sort, built once); `links_eval` and `links_cols` (in parallel). Test `e1b_tests::packing_rows`. |
| `node.rs` | `phantom_seg`, `inactive_arena` and `c_inactive`. An inactive sub-slot's phantom segment now also carries `vk ‖ c_in` in elements 1–4, because IMP's `input` cells are tied to `vk` and to the slot's `hashA` output by the statement link rows. It also carries the leaf tag at element 13 byte 0 (IMPC2's ungated statement read). `agg_stream` writes them into H, so H and arena₁ agree. `arena_of`, `slot_b0`. **`extend_links`** appends to each kind table: every slot's arena₁ rows (`a1Rows4`: `one·(A₁(e) + H(sCell b0 e)) = 0`), and for N2/N4 slot 0's replay rows (`repIRowsW rtC1d κ 0`: rows from `κ.vslots·2^20`, frame `+ one`, locals into the spare region). `witness` computes each slot's arena from the main-chain bytes, passes it to the fill, and writes the spare locals into the spare region. `solve_aux` reads `node-N*.txt`'s rows only. Prototype 0 has no inactive fill, because slot 0 is never inactive. |
| `plan.rs` | Blob v3 (`FRNB3`): per prototype the plan form, the register forms, `encode_rows` of the extra rows and of the spare rows. Image v3 (`FLNDIMG3`, spare rows included). `kind_tab` extends the links, and `kind_tabs` builds the three kinds in parallel with their by-cell indices. `proto_eq` compares the spare rows too. |
| `nodeprove.rs` | The link loops run in parallel: `m_matvec`, `links_scatter` (by cell), `child_rows` and `add_cols` (`links_eval` / `links_cols` + `land_items`, a two-pass parallel landing). They are 1.3 M rows now, against 83 k before. `m_scatter_ref` is unchanged and remains the reference for `scatter_gather_and_matvec_match`. |
| `nodeops.rs` | The link part of `eval_m` and `eval_mx` runs in parallel (`links_val`). |
| `stream.rs`, `main.rs` | `Pre` uses `kind_tabs_static` (built once, not twice). Setup records only prototype 1's inactive fill. New `mx-kat` command. `mfill-kat` passes the segment's arena. |
| `kat.rs`, `mfill.rs`, `ir.rs`, `items.rs` | Default dump paths `logs/E1b/{dump,nodedump}`. |

## 2. Dumps (at `3d9ae68`; the `e447823` ones kept as `logs/E1b/{dump,nodedump}-e447823`)

- **Script.** `logs/E1b/dump.sh` runs `irdumpa2pp`, `nodedump4`, `planform4`, `protodump` and **`nodedumpx`** (new).
- **Checksums.** `logs/E1b/nodedump-SHA256SUMS` and `logs/E1b/dump/SHA256SUMS`.
- **Unchanged since E1.** The IR dumps (`ops-*`, `items.json`, `summary.txt`) and `proto-p*.txt` are byte-equal to E1's (`7537acd`). The segment side did not change.
- **`e447823` → `3d9ae68` (FEL).** Only `maux-p{0,1}`, `mrows-p{0,1}`, `plan-form-p{0,1}.bin` and `mxkat.txt` changed, as FEL-RESULT §7 says.
- **NodeDumpX** (`logs/E1b/nodedumpx-run.log`):

  | | prototype 0 | prototype 1 |
  |---|---|---|
  | `askRowsT` | 130,914 | 154,333 (slack 35 of `arR2N` 154,368) |
  | `repRowsP` | 562,758 | 38,805 |
  | `repFitB` | true | true |

  `planOf4.inR` is true.
- **Blob.** `nodeblob.b64` is 22,663,716 B, sha256 `f542403e…`. The raw blob is 67 MB, of which the spare rows are 13.6 MB and the extra rows 6.2 MB; E1's was 11.4 MB. Report in `logs/E1b/plan-build.log`.

**KATs** (all at `3d9ae68`):

| KAT | result | log |
|---|---|---|
| `planform_kat.py` | PASS | `logs/E1b/planform-kat.log` |
| `plan-kat` | blob = dump for both prototypes, spare rows, programs and kind texts; decode 0.65 s | `logs/E1b/plan-kat.log` |
| **`mx-kat`** | **PASS**: 6 of 6 values equal (N2/N4/N8 × 2 points) | `logs/E1b/mx-kat.log` |

`mx-kat` compares the prover's `nodeops::eval_m` over its whole M with Lean's `evalMT4 planOf4 κ τ σ`. The prover's M is every slot's prototype rows with the ask, bit and replay rows, plus the kind table's links, arena₁ rows and slot 0's replay rows.

`node-kat` reports 0 failing rows of any kind on every node of §3.1. `node::check` covers H, the chain, the links, the public cells, L, every slot's M rows and every link row.

π identity was not kept, because the circuit changed: E1's KAT hashes do not apply.

## 3. End-to-end acceptance

### 3.1 The node chain (`node-kat --prove`, keyed oracle, test signer; each output checked by `e1verify`)

`e1verify` is the badge's `parseSigned` plus `accF` with `V := FR.Sub4.V4F` and `qV := 36,000`, built at the
same commit. The canary flips the statement's last bit.

**At `3d9ae68`, with the embedded blob** (`logs/E1b/r3/chain.txt`; plan check in `logs/E1b/r3/plan.txt`):

| node | previous | aggregate(s) | Lean V (VM, timed after a warm run) | canary |
|---|---|---|---|---|
| N8 | — | 2 × k 1 | **accept** 525 ms | reject |
| N2 | N8 | k 1 | **accept** 1,070 ms | reject |
| N4 | N8 | k 2 | **accept** 1,061 ms | reject |
| N4 | N2 | k 2 | **accept** 1,032 ms | reject |
| N2 | N4 | k 1 | **accept** 1,076 ms | reject |
| N2 | N2 | k 2 | **accept** 1,173 ms | reject |
| N4 | N2 | k 4 | **accept** 1,026 ms | reject |
| N4 | N4 | k 3 | **accept** 1,061 ms | reject |
| N4 | N4 | k 1 | **accept** 1,122 ms | reject |
| N8 | — | 2 × k 4 (2^20 each: the full-length N8) | **accept** 502 ms | reject |

- **Transitions covered:** N8→N2, N8→N4, N2→N4, N4→N2, N2→N2 and N4→N4.
- **Child-claim support:** it holds all three kinds from the third node on.
- **Inactive sub-slots:** they occur at k = 1, 2 and 3, and every one of their rows holds.
- **At `e447823`:** the same 10 nodes were accepted with the dump directory instead of the blob (`logs/E1b/r2/chain.txt`).

### 3.2 Streams through `rf-oracle` (`logs/E1b/stream.sh` = E1's, `st-run.sh`)

The stream runs `prover setup`, then `first` and `step` with the ready/go/done handshake. It uses rf-oracle's real
WOTS signatures, and every output is checked by the native `acc` and by the Lean V at `3d9ae68`.

**Stream `logs/E1b/st1`** (cargo-built binary, 16 VM cores):

| step | chain | kind | Lean V | canary | native acc | req_s (VM) |
|---|---|---|---|---|---|---|
| 1 | 2^20 + 2^20 (**full-length first step**, k 4 + 4) | N8 | accept | reject | accept | 112.2 |
| 2 | 131,072 | N2 | accept | reject | accept | 15.7 |
| 3 | 300,001 (k 2) | N2 | accept | reject | accept | 25.9 |
| 4 | 786,432 (k 3) | N4 | accept | reject | accept | 52.2 |
| 5 | 2^20 (k 4) | N4 | accept | reject | accept | 65.7 |
| 6 | 131,072 | N2 | accept | reject | accept | 16.2 |
| 7 | 600,001 (k 3) | N4 | accept | reject | accept | 44.6 |
| 8 | 262,144 | N2 | accept | reject | accept | 22.7 |
| 9 | 2^20 (k 4) | N4 | accept | reject | accept | 66.4 |

Totals: **9/9 accepted by the Lean V and 9/9 canaries rejected**; `rc 0`.

**Stream `logs/E1b/st2`**, run with **the asm-linked binary of the final `prover.s`** (`09570a1b…`): 2^20 + 2^20
(N8, the full-length first step), 786,432 (N4), 131,072 (N2), 2^20 (N4). All 4 were accepted by the Lean V and all
canaries rejected (`rc 0`).

## 4. Measurements and the cap projection

**Method.** The VM has no pclmulqdq and is shared, so its times are not a runner's.
- **Node A/B.** E1's binary (`7537acd`, E1's dump) against E1b's (`3d9ae68`, the embedded blob), run alternately on the same 4 VM cores (24–27), 2 rounds, best of the two.
- **Scaling.** The changed phases (`e2`, `e4`) are scaled to the EPYC 7763 by E1's own measured ratios. The witness delta is scaled conservatively.
- **Base.** E1's projection model (`logs/E1b/project.py`, unchanged) and RUN1's 7763 measurements of the harness.
- **Data.** `logs/E1b/nab/ab.txt`, `phases.txt`, `phases.py`.

| node (full support) | VM e2 old → new | VM e4 old → new | 7763 Δ (e2 + e4) | node-kat witness VM old → new |
|---|---|---|---|---|
| N2 | 2.37 → 3.38 | 5.31 → 6.14 | +0.29 s | 2.66 → 4.21 |
| N4 | 3.28 → 4.42 | 8.46 → 9.91 | +0.39 s | 3.40 → 4.80 |
| N8 | 1.21 → 1.47 | 3.93 → 4.37 | +0.11 s | 3.41 → 3.51 |

**Why the costs moved.**
- **Proving phases.** Every other phase is unchanged within noise: commit, Z, Lc, Sh, RS and Ligerito. The delta comes from the larger M: about 150–210 k more rows per prototype, plus 1.3 M link rows per kind.
- **Witness.** The node-kat witness (slot 0's fill, the replay locals, larger fills) grows by ≈ 1.5 s on 4 VM cores. In a stream step, slot 0 and its replay locals run beside the aggregate (`slot0_wait = 0` in every step of `st1`). The post-aggregate witness is 0.73–1.06 s on 16 VM cores, against E1's 0.77–1.23 s on 8.
- **Start-up.** It is 1.39–1.53 s on the VM (E1: 0.99–1.21): the larger image and the kind tables with their by-cell indices.

**Node parts for the model** (7763; E1's in parentheses):
- **N2 4.38 s** (3.58): the measured +0.38 s of the node prove (+0.29 s from e2/e4), plus 0.4 s of witness assumed to be on the critical path.
- **N4 6.83 s** (5.93): +0.46 s of prove plus 0.4 s of witness.
- **N8 5.61 s** (5.46).
- **Start-up 0.86 s** (0.66).

The witness term is conservative, because most of it overlaps the aggregate.

`logs/E1b/project.txt`:

| | E1 | **E1b** |
|---|---|---|
| steps 2^17 / 2^18 / 2^20 | 5.86 / 8.14 / 24.17 s | 6.66 / 8.94 / 25.07 s |
| **worst first step 2^20 + 2^20** (k 4 + 4) | 41.94 s | **42.09 s** (step_s 60: **1.43×**); RUN1 measured E1's at 43.81 s, so ≈ 44 s (**1.36×**) |
| mean step + model overhead | 11.92 s | 12.93 s |
| prover side at M = 96 (requests + start-ups: the model minus its 1.38 s/step of harness overhead) | mean 1,019 / max 1,179 s | **mean 1,115 / max 1,277 s** (max of 20,000 draws) |

**`stream_s` at M = 96.** The harness side is RUN1's measured parts, updated for the badge's new V:

| part | basis | seconds |
|---|---|---|
| V start-ups | ≈ 29 badge runs × 10 s (V init 9–11 s user, per the brief) | 290 |
| V checks | ≈ 220 checks (12 batches × 2 runs × 9, plus a canary run); a check takes **≈ 0.8 s** on the 7763 at this HEAD (VM 1.03–1.17 s for N2/N4, 0.50 s for N8; RUN1's VM/7763 ratio ≈ 1.4) | ≈ 176 |
| staging and kills | RUN1 | ≈ 13 |
| calibration samples | RUN1 | ≈ 57 |
| **harness side** | | **≈ 536** |
| **total** | | **mean ≈ 1,651 s (1.16×), max draw ≈ 1,813 s (1.06×) of 1,920** |

- **The thin cap.** `stream_s` is the thin cap. The prover's growth (+96 s on the mean) is smaller than the V side's: each accepted N2/N4 check now takes ≈ 1.05 s on the VM, against E1's 0.30–0.43 s at `7537acd` (REPF/SEG replay rows in V). That adds ≈ +120 s over RUN1's check estimate. It is the Lean V's cost, not the prover's.
- **Uncertainty.** These are projections from VM A/B ratios, not runner measurements. A runner stream (`probe/` branch, RUN1's eval workflow) would replace them.
- **Other caps.** `verify_s` per check ≈ 0.8 s against a cap of 10 s. The DoS per-item cap is `10·v_ref` ≈ 2.06 s, against at most one full V of ≈ 0.8 s on the 7763 (2.6×; RUN1 had ≈ 8×).
- **Setup** on the VM: 110.2 s on 16 cores (`st1/setup.log`) and 122.7–141.3 s on 12 cores (`s1/setup*.log`). E1's same work was 167 s on 12 VM cores and 60–70 s on 7763 runners, so the 240 s cap holds with a wide margin. Peak RSS 7.7 GB; the directory holds 302 MB.

## 5. Deviations and findings

1. **Ungated reads at inactive sub-slots.** Some ask-template rows are not gated by activity (IMPC2 §8 says so). They need the inactive sub-slot's stream to hold `vk ‖ c_in` in seed elements 1–4 and the leaf tag `0x4c` at element 13.
   - `c_in` is the slot's `hashA` of the zero message.
   - The main chain past an aggregate's real length is free, so the prover writes these into its phantom stream.
   - An inactive slot's replay copy rows also need the import to equal the template's output on zero-selected inputs, not zero.
   - This is how the honest witness works and is not a soundness issue. But **A1′'s "phantom constants" list is now longer** than its text says.
2. **The inactive fill depends on `vk`**, through `vk ‖ c_in`. The setup has no service and no `vk`, so the cached inactive fill holds only for `vk = 0`. Requests replay the recorded two-phase order instead (`ZERO_ENTRY`), at ≈ 0.5 s per inactive slot, with the slots in parallel.
3. **Prototype 0's inactive fill is dropped.** Slot 0 always has a previous node, and a segment-shaped phantom does not satisfy prototype 0's statement read (`0x4e`).
4. **The blob doubled** to 22.7 MB of base64, and `prover.s` grew to 34.7 MB. Prototype 0's replay rows are 13.6 MB of the raw blob. They could be stored as their gate list instead, but that is not needed for any cap.
5. **The V cost grew threefold since E1** (§4). It now dominates the harness side of `stream_s`.

## 6. Open items

- **A runner measurement** of the stream and the worst first step at `3d9ae68`, through RUN1's `probe/run1-eval` pattern. It needs a push, which the orchestrator decides.
- **The `arR2N` margin at prototype 1 is 35 rows.** Any later ask-template rows at prototype 1 break `ArFit`, which makes every honest proof reject silently. The plan check (`e1verify --plan`, `PLAN-CHECK`) catches it before proving.
- **Levers, if `stream_s` tightens.**
  - On the V side: closed forms for the replay rows (`rv1`, SEG-R2 §9.3).
  - On the prover side: factor slot 0's replay rows and the arena₁ rows like the prototypes, instead of as link rows. This cuts the link work in `e2`/`e4` and the start-up's by-cell indices.

## 7. Files

- **Prover** (`submissions/flock-recursive/prover/`): `mfill.rs`, `node.rs`, `nodeprove.rs`, `nodeops.rs`, `plan.rs`, `stream.rs`, `main.rs`, `kat.rs`, `ir.rs`, `items.rs`, `nodeblob.b64`, `prover.s`.
- **Docs:** this file and `E1b-JOURNAL.md`.
- **Logs** (`logs/E1b/`):
  - scripts: `dump.sh`, `st-run.sh`, `st-run2.sh`, `stream.sh`, `project.py`;
  - dumps: `dump/`, `nodedump/`, `*-e447823/`;
  - chains: `r2/` (`e447823`), `r3/` (`3d9ae68`);
  - streams: `st1/`, `st2/`; setups: `s1/`;
  - A/B: `nab/`; determinism: `asm/`;
  - KATs: `plan-kat.log`, `mx-kat.log`, `planform-kat.log`; tests: `cargo-test-{1,2}.txt`;
  - profiles: `prof-n4*.log`.
- **Lean tree** `logs/fr-build-E1b`: `snap.sh` (`COMMIT=`), `probe/NodeDumpX.lean`, and `probe/E1Verify.lean`, whose `--plan` now prints `askRowsT 0/1`, `arR2N` and `PLAN-CHECK`.
