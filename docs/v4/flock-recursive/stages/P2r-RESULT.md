# P2r RESULT: prover-only margin at rev44 (factored E1b rows, E2/E4, start-up)

Track P2 of the orchestrator's brief ran on 2026-10-30.

- **Name.** The files are named `P2r-*` because `P2-RESULT.md` and `P2-JOURNAL.md` already hold track P's
  stage P2 (2026-10-27). Rename them if you prefer.
- **Where.** Worktree `/home/devops/Verified-zkEVM/rf-p2`, branch `p2-work` at `4537909` (RUN2), uncommitted.
- **Logs** are in `logs/P2/`; the running notes are in `P2r-JOURNAL.md`.
- **Scope.** Only `submissions/flock-recursive/prover/` changed: Rust sources and `prover.s`. `nodeblob.b64`
  is unchanged. No Lean code, circuit or V changed.
- **Process.** Every cargo, prover and Lean V run ran in a 16 GB scope under `timeout`. No sub-agents were
  used, and nothing was committed or pushed.

## 0. Summary

| Item | State |
|---|---|
| Proofs | **Byte-identical** to the `37deb5c` prover's on every comparable run. The node-kat π hash is the same for N2, N4 and N8 in every A/B run. All 10 `.signed` outputs of the 10-node chain equal E1b's `r3` files byte for byte (`chain/identity.txt`). |
| 1. 10-node chain (E1b §3.1) | Plan check `PLAN-CHECK OK`. **10/10 accepted by the Lean V (`3d9ae68` = `4537909`'s Lean), 10/10 canaries rejected.** 0 bad M or link rows (`chain/chain.txt`). |
| 2. Streams through `rf-oracle` | **st1** (cargo binary, fresh `prover setup`): 9/9 accepted by the Lean V, including the full-length first step 2^20 + 2^20. 9/9 canaries rejected, native `acc` 9/9. **st2** (the asm-linked binary of the final `prover.s`): 4/4 accepted, with the full-length first step, and 4/4 canaries rejected. |
| `prover.s` | Two clean `build-asm.sh` runs give an **identical** file: sha256 **`377549016b0c4b6e73c4a811bed9ae4ffa336d54ed9712a97cdd0fa7f3b8a863`**, 35,147,062 B. gcc takes 1.6 s (`asm/det.txt`). |
| `cargo test` | 59 passed, 1 ignored. That is E1b's 57 plus 2 new tests (`cargo-test-2.txt`). |
| 3. A/B, 4 VM cores | Node prove (best of 2): N2 26.58 → 24.31 s, N4 44.91 → 41.68 s, N8 41.45 → 40.76 s. E2 + E4: N2 9.44 → 7.02 s, N4 13.83 → 10.79 s. **Start-up: 1.640 → 0.898 s** (median of 6). |
| Projection, 9V74 (RUN2's host and draw) | **`stream_s` 1,688.7 → ≈ 1,603 s (1.14× → 1.20×)** at the measured draw. A heavy draw (max of 20,000) goes from 1,866 → ≈ 1,780 s (1.03× → 1.08×). The saving is ≈ 86 s: 49 s of start-ups and 36 s of requests. |
| Worst first step 2^20 + 2^20 | ≈ −0.1 s only: ≈ 46 → ≈ 45.9 s on the 9V74, 42.09 → 41.98 s on the 7763 model. The step is 8 segment proofs plus an N8 node, and this stage touched only the node. |
| The brief's goal (≈ 235 s, ≈ 20 % of the prover side) | **Not reached: ≈ 86 s, ≈ 7 %.** The measured-draw stream reaches 1.20×, but heavy draws do not. §5 explains why the node phases cannot buy the rest. |

## 1. What changed (`.rs` lines: 19,248, +932 −244)

| file | change |
|---|---|
| `mfill.rs` (+200 −42) | **`Ext`** on `KindTab`: E1b's rows beyond `node-N*.txt`, described by their structure. Arena₁: per slot `b0` and `a1_h(b0, e)`. Slot 0's replay rows: prototype 0's `spare`. A kind table now keeps only the base link rows (35–83 k, against 0.85–1.3 M). **`SpareIx`** (`Proto::spare_ix`) is the spare rows' span and by-cell index, built once for N2 and N4. **`cell_index`** groups terms by cell. A large cell range with few terms (the base link rows over `2^25` cells) is now sorted, where it was a counting sort over the range. The result has the same entries in the same order. **`cols3`** gives the per-cell column sums. Test `cell_index_matches_counting_sort`. |
| `node.rs` (+40 −2) | `set_ext` (the factored kind table). `extend_links` stays and builds the full reference table. `spare_cell` gives the replay rows' placement. `node::check` checks the factored rows directly, row by row as `extend_links` lays them out. |
| `nodeprove.rs` (+386 −37) | The factored rows in all four link operations. `m_matvec` and `m_scatter` (the latter only in the debug check and tests). **`child_rows`** (E2): arena₁ slot by slot; slot 0's replay rows from `spare_matvec`, once for every kind. **`add_cols`** (E4 own `W` and child columns): arena₁ by runs and H landings; replay rows from the spare columns `tsp` (`E4Tabs`), shared by the own kind and the child kinds. **`EqProd`**: E2's extra product `η·eq(p_x,·)·Q` in closed form, with no `2^logM` eq table and no fold of `P`. `comb3` and `add_run` use the vector kernel `axpy`. E4's support chunk is `2^4` (`FLOCK_E4_A` overrides it, for measurement). `FLOCK_E4_BENCH` times E4's sumcheck in the process at several chunk sizes, for measurement only. `ext_ab` and the `bench-ext` command compare the full and factored paths and check that their outputs are equal. Tests: `p2_tests::ext_matches_full`; `scatter_gather_and_matvec_match` now compares against the full table. |
| `nodeops.rs` (+100 −5) | `eval_m` and `eval_mx` take the factored rows (`ext_val`, `spare_sums`, shared across kinds in `eval_mx`). The tests compare factored tables with the full ones (N2, N4, N8, and `eval_mx` at every support). |
| `sumcheck.rs` (+95 −131) | **`prove_pairs_support`** works over runs of consecutive live chunks with the vector kernels `round_ff` and `fold`, where it had per-pair scalar loops. A closed-form eq pair contributes `h_c·round_ff(P, le)` per chunk, since the message is linear in `Q`. `prove_pair_support` is now its one-pair case. `msg_pairs` uses `round_ff`. The tests also cover `a` = 1, 2 and 4. |
| `plan.rs` (+82 −14) | `kind_tab` (factored) and `kind_tab_full` (the reference). `kind_tabs` builds the spare index as a fourth parallel task. `data_tag` hashes the blob's 64 parts in parallel, then their digests, so **setup images and plans from before P2 no longer match**. `read_par` reads the setup image with `read_at` in parallel pieces, and `Ri::raw` copies large arrays in parallel pieces. |
| `stream.rs` (+18 −13) | `Pre::new` builds the kind tables beside plan loading. The plan files are read with `read_par`. |
| `main.rs` (+11) | The `bench-ext` command. |
| `prover.s` | Regenerated (§0). |

**Why the proofs cannot change.** Every replaced computation produces the same field values. Field
addition and multiplication are exact, so changing the summation order changes nothing. The messages
are therefore the same, and so are the transcript and π.
- **Checked in-process:** `ext_ab` and the unit tests compare against E1b's full tables.
- **Checked on whole proofs:** the node-kat π hashes and the chain's byte equality.

## 2. Acceptance

### 2.1 The 10-node chain (`logs/P2/chain/`, E1b's `chain.sh`; binary `nab/prover-new` sha256 `2b741672…`)

| node | previous | aggregate(s) | Lean V | canary | e2 / e4 (16 VM cores) | E1b `r3` e2 / e4 |
|---|---|---|---|---|---|---|
| N8 | — | 2 × k 1 | accept | reject | 0.60 / 1.37 | 0.64 / 1.69 |
| N2 | N8 | k 1 | accept | reject | 0.66 / 1.59 | 0.77 / 2.09 |
| N4 | N8 | k 2 | accept | reject | 0.99 / 2.25 | 1.18 / 2.99 |
| N4 | N2 | k 2 | accept | reject | 1.16 / 2.58 | 1.34 / 3.65 |
| N2 | N4 | k 1 | accept | reject | 1.02 / 1.86 | 1.16 / 2.55 |
| N2 | N2 | k 2 | accept | reject | 1.07 / 2.09 | — |
| N4 | N2 | k 4 | accept | reject | 1.49 / 2.71 | — |
| N4 | N4 | k 3 | accept | reject | 1.41 / 2.65 | — |
| N4 | N4 | k 1 | accept | reject | 1.32 / 2.56 | — |
| N8 | — | 2 × k 4 (2^20 each) | accept | reject | 0.71 / 1.35 | — |

- The plan check prints `inR true … askRowsT 0/1 130914/154333 arR2N 154368 PLAN-CHECK OK`.
- Every output's `.signed` file is identical to E1b's `r3` output.
- The E1b column is from a different time and machine load, so it is indicative only. §3 is the A/B.

### 2.2 Streams (`logs/P2/st-run.sh` around E1b's `stream.sh`; Lean V on every output)

**st1**: the cargo binary, with a fresh `prover setup` (103 s on 16 VM cores, 302 MB, peak 7.3 GB).

| step | chain | kind | Lean V | canary | native acc | req_s | start-up | prove |
|---|---|---|---|---|---|---|---|---|
| 1 | 2^20 + 2^20 (k 4 + 4) | N8 | accept | reject | accept | 104.5 | 0.56 | 14.11 |
| 2 | 131,072 | N2 | accept | reject | accept | 14.4 | 0.53 | 7.99 |
| 3 | 300,001 | N2 | accept | reject | accept | 23.7 | 0.55 | 8.82 |
| 4 | 786,432 | N4 | accept | reject | accept | 48.7 | 0.56 | 13.58 |
| 5 | 2^20 | N4 | accept | reject | accept | 59.1 | 0.57 | 14.38 |
| 6 | 131,072 | N2 | accept | reject | accept | 15.3 | 0.55 | 8.84 |
| 7 | 600,001 | N4 | accept | reject | accept | 41.1 | 0.54 | 13.74 |
| 8 | 262,144 | N2 | accept | reject | accept | 20.6 | 0.55 | 8.52 |
| 9 | 2^20 | N4 | accept | reject | accept | 62.0 | 0.55 | 14.28 |

- `rc 0`; the peak RSS of a request is 7.15 GB (E1b's st1: 7.67 GB).
- E1b's st1 ran the same chains at another time (16 cores). It took start-ups of 1.39–1.53 s and node
  proves of 8.6–9.9 s (N2) and 15.1–16.9 s (N4). That comparison is indicative only.

**st2**: the asm-linked binary of the final `prover.s` (`asm/prover-asm`, sha256 `7e61d0e0…`), with its own setup.

| step | chain | kind | Lean V | canary | native acc |
|---|---|---|---|---|---|
| 1 | 2^20 + 2^20 | N8 | accept | reject | accept |
| 2 | 786,432 | N4 | accept | reject | accept |
| 3 | 131,072 | N2 | accept | reject | accept |
| 4 | 2^20 | N4 | accept | reject | accept |

`rc 0`; start-ups 0.54–0.72 s.

## 3. A/B (`logs/P2/nab/`, `su-ab.txt`)

### 3.1 Node prove

- **Method.** `nab/ab.sh`: `node-kat --prove` on 4 VM cores (24–27), 2 alternating rounds, best of the two.
  Old is `prover-old` (`37deb5c`), new is `prover-new`, and both use the embedded blob.
- **Scaling.** `phases.py` scales the e2/e4 deltas to the 7763 by E1's per-phase ratios, as E1b did.
- **Data.** `nab/phases.txt` and `nab/ab.txt`. An earlier round with an intermediate binary is in `nab/r1/`.

| node | e2 VM old → new | e4 VM old → new | node VM old → new | **7763 Δ (e2 + e4)** | node-kat witness VM |
|---|---|---|---|---|---|
| N2 (full child support) | 3.27 → 2.69 | 6.17 → 4.33 | 26.58 → 24.31 | **−0.34 s** | 4.22 → 3.57 |
| N4 (full child support) | 4.27 → 3.71 | 9.56 → 7.08 | 44.91 → 41.68 | **−0.38 s** | 4.87 → 4.27 |
| N8 | 1.48 → 1.48 | 4.39 → 3.51 | 41.45 → 40.76 | **−0.11 s** | 3.49 → 3.50 |

- **Unchanged phases.** Commit, Z, Lc, Sh, Lr, RS and Ligerito agree within noise.
- **Where the e2/e4 time went** (spans, N4, VM):
  - E2's child table: 2.06–2.11 → 1.68–1.70 s.
  - E4's own scatter: 0.84–0.87 → 0.68–0.70 s.
  - E4's child columns: 1.78–1.87 → 1.29–1.30 s.
  - E4's sumcheck: 6.68–6.78 → 4.89–5.12 s. N2: 3.68–3.78 → 2.38–2.45 s. N8: 3.39–3.41 → 2.68–2.74 s.
- **Witness.** The node-kat witness also dropped on N2/N4, by 0.6 s. Its code did not change. The likely
  cause is the smaller kind tables (less memory and fewer page faults), but this is not shown, so the
  projection does not count it.
- **The scaling is conservative for this change.** E1's ratios come from phases of scalar products. Here
  part of the gain is vector kernels (`round_ff`, `fold`, `axpy`) that replaced scalar loops, and on the
  VM those kernels run the portable path, so the VM shows none of that gain.

### 3.2 Start-up (process start → `ready`, as `stream.sh` measures it)

- **Method.** `su-ab.py`: 6 rounds alternating, 4 VM cores. Each binary runs with its own setup:
  `setup-e1b` for old, `setup-new` for new.
- **Result.** Old: min 1.575, **median 1.640**, max 1.661 s. New: min 0.850, **median 0.898**, max 0.931 s.

Where the start-up time went (spans, 4 VM cores):

| part | old | new | what changed |
|---|---|---|---|
| kind tables | 0.58 s | 0.10 s | 1.3 M link rows and the range counting sort → base rows, a sort, and one spare index |
| tag | 0.10 s | 0.02–0.03 s | 64-part hash |
| image read + parse | 0.12 + 0.23 s | 0.03 + 0.14 s | parallel `read_at` and copies |
| plans, schedules | 0.08 + 0.09–0.17 s | ≈ 0.2 s with the kind tables beside them | — |
| pre-fault (6000 MiB) | 0.4 s | 0.4 s | unchanged |

## 4. Projections

**The 9V74 of RUN2** (run 41012684725: measured `stream_s` 1,688.7 s; `logs/P2/project-9v74.py`, `.txt`).
- **Start-ups.** Each of RUN2's start-ups (Σ 108.7 s) is scaled by the measured new/old ratio, 0.898 / 1.640.
  That saves 49.2 s.
- **Requests.** Each step saves its kind's 7763-scaled node delta (§3.1) times the host's factor over E1b's
  7763 projection (1,233.1 / 1,115 = 1.106). The run had 1 N8, 83 N2 and 12 N4 steps, so this saves 36.4 s.
- **Heavy draws.** These are RUN2's `project.py`, with the measured value reduced by the saving above. The
  savings are per step, so the per-compression slope is unchanged.

| draw | Σn | `stream_s` RUN2 → P2 | margin |
|---|---|---|---|
| this run's | 30.28 M | 1,688.7 → **1,603 s** | 1.14× → **1.20×** |
| median | 30.16 M | 1,686 → 1,601 s | 1.14× → 1.20× |
| p90 | 32.77 M | 1,743 → 1,657 s | 1.10× → 1.16× |
| p99 | 34.95 M | 1,790 → 1,704 s | 1.07× → 1.13× |
| p99.9 | 36.97 M | 1,834 → 1,748 s | 1.05× → 1.10× |
| max of 20,000 | 38.45 M | 1,866 → 1,780 s | 1.03× → 1.08× |

**Worst first step 2^20 + 2^20 on the 9V74:** ≈ 46 s → ≈ 45.9 s (N8 −0.11 × 1.106). Its margin stays ≈ 1.3×.

**E1b's 7763 model** (`project-e1b.py`, `logs/P2/project-7763.txt`):
- Node parts N2 4.38 → 4.04, N4 6.83 → 6.45, N8 5.61 → 5.50 s.
- Start-up 0.86 → 0.47 s (the measured ratio).

| | E1b | P2 |
|---|---|---|
| mean step + model overhead | 12.93 s | 12.20 s |
| stream at M = 96: mean / p99 / max draw (prover-side model) | 1,247 / 1,345 / 1,409 s | 1,177 / 1,274 / 1,338 s |
| worst first step | 42.09 s | 41.98 s |

These are projections from VM A/B, not runner measurements.

## 5. Why the factorization falls short, and what was done instead

- **The factorization alone was small.** On a 7763 a mean step is ≈ 60 % aggregate and ≈ 40 % node. The
  link work that the factorization removes was ≈ 0.1–0.2 s of a ≈ 10 s mean step. E1b's whole e2 + e4 was
  ≈ 1.4 s (N2) and ≈ 2.0 s (N4), so even deleting both phases would not reach the ≈ 2.2 s a step that 20 %
  needs.
- **The next cheap wins were taken.**
  - The E4 sumcheck works at a finer support. The arena₁ H cells made every `2^12` chunk live, though only
    16–32 % of the entries are nonzero.
  - The kernels in E2/E4's dense passes are vectorized.
  - E2's eq table is now in closed form.
  - **The start-up**, ≈ 45 % less, is the biggest single gain: ≈ 0.5 s × 97 on the 9V74.
- **The rest of the margin would have to come from the aggregates (segment proofs),** which this stage did
  not touch. That holds for `stream_s` and for the worst first step alike: in st1's first step the
  aggregates took 88.8 s of 104.5 s on 16 VM cores.

## 6. Open items

1. **A runner measurement** of a stream and of the worst first step, through RUN1/RUN2's `probe/run*-eval`
   pattern. It needs a push, which is the orchestrator's decision. The node savings may be larger than
   projected (§3.1, the scaling note).
2. **Setup.** The data tag changed, so a `prover setup` from before P2 is ignored: the image fails to load and
   the plans are recomputed (≈ 2 s at start-up). The harness always runs `prover setup` first, so this
   matters only for hand-run tests. Setup took 103 s on 16 VM cores (E1b: 110 s); its output is the same
   302 MB.
3. **Pre-fault lever (not taken).** The pre-fault is 6000 MiB (0.4 s of the new 0.9 s start-up on 4 VM
   cores). Without it, an N2 step at 131,072 peaks at 3.6 GB RSS, against 7.0 GB for N4 at 2^20 and 7.6 GB
   for the N8 first step (`logs/P2/pf0/`). A smaller pre-fault for `step` requests, keeping 6000 MiB for
   `first`, would stop zeroing ≈ 2–3.7 GB per N2 start-up: ≈ 0.1–0.2 s × 83 on the 9V74. N4 steps would
   fault the rest during the request. I left it alone: P-track tuned this value on runners, and an N2 step
   at k = 2 needs more memory than the 131,072 one measured.
4. **E4 chunk size on the VM is non-monotonic.** a = 6 and a = 8 were slower than a = 12, and a = 3–4
   fastest, consistently across two orders (`nab/e4c-n4.log`, `e4e-n4.log`). I chose a = 4. A runner
   `FLOCK_E4_BENCH=12,8,6,4,3` run inside one node-kat would settle it, since it measures in process and
   compares the outputs.
5. The `bench-ext` command and the `FLOCK_E4_A`/`FLOCK_E4_BENCH` hooks are measurement-only code in the
   entry. Drop them if the entry should carry none.

## 7. Files

- **Prover** (`submissions/flock-recursive/prover/`): `mfill.rs`, `node.rs`, `nodeprove.rs`, `nodeops.rs`,
  `sumcheck.rs`, `plan.rs`, `stream.rs`, `main.rs`, `prover.s`.
- **Docs**: this file and `P2r-JOURNAL.md`.
- **Logs** (`logs/P2/`):
  - binaries `prover-old`, `nab/prover-new`, `asm/prover-asm`;
  - `chain/` (`chain.sh`, `chain.txt`, `identity.txt`, `plan.txt`);
  - `st1/`, `st2/`, `st-run.sh`, `stream.sh`;
  - `nab/` (`ab.sh`, `one.sh`, `phases.py`, `phases.txt`, `ab.txt`, `r1/`, profiles, `e4*-n4.log`, `live-*.log`);
  - `su-ab.py`, `su-ab.txt`, `su-old/`, `su-new*/`, `pf0/`;
  - `bench-ext-*.txt`, `asm/` (`det.sh`, `det.txt`, `prover{1,2}.s`);
  - `cargo-test-2.txt`, `setup-new/`, `project-9v74.py`, `project-9v74.txt`, `project-e1b.py`, `project-7763.txt`.
