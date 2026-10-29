# RUN1 RESULT: the hard caps of `v4/rev44` at `200b531`, on GitHub runners

Track RUN1, 2026-10-29. The entry is `submissions/flock-recursive` at **`200b531`**, with `prover.s` sha256 `aac53ced…`
and the core pinned at `422f2f9`. I ran 11 workflow runs on probe branches `probe/run1-{eval,a,…,j}`. Each branch was
one commit on `200b531` that touched only `.github/` and `probe/`. Every branch has been deleted. Logs are in
`logs/RUN1/`: the probe scripts, `commits.txt`, `runs.txt`, and one directory per run (`run-<id>/`, `eval-<id>/`).
Nothing is committed. No entry source was edited.

## 0. Verdict

1. **The real evaluation REJECTs the entry at `200b531`.** Run 40944222197 called the core's `evaluate.yml` at
   `422f2f9` (season `season.toml`). Its result is `REJECT: stream outputs: stream step 1 rejected by acc`.
   - **What rejects.** The badge `verify` is built from `submission` = `sub4`, `V := V4F` at `200b531`. It rejects
     every node proof that `prover.s aac53ced…` makes: N8, N2 and N4, on every runner and on the VM.
   - **E1's proofs are rejected too.** The three `logs/E1/st2` proofs, which E1's `e1verify` accepted at `7537acd`,
     are rejected locally by the same badge (`reject 317/358/376 ms`).
   - **The statements are not the cause.** The harness's statements equal the prover's
     (`rfh/digest.py` gives the prover's `stmt` for chains 17/29 of length 2^20).
   - **The cause.** IMP (`616b57c`, after E1's test point `7537acd`) added PK-m7's statement rows to V's node rows:
     `xRowsA κ := xRows κ ++ (chkRows κ ++ stmtRows κ (actW κ))` in `FRNodeRows4Ext`, with `extRowsC` ≤ 12,056 →
     12,136. The prover's `nodeblob.b64` was dumped at `7537acd` and lacks those rows. E1-RESULT §6 lists exactly
     this as open ("IMP's rows … re-dump, rebuild the blob, run node-kat").
   - **Fix.** Re-dump, rebuild the blob and fill the new cells, then re-run the eval branch.
   - **The timings below are still valid.** IMP adds 80 link rows, so the prover's cost should barely move. The
     badge's V times were measured on these rejected proofs: each check runs 0.20–0.27 s, close to E1's accepted
     V times (VM: reject 310–360 ms against accept 268–430 ms), but **no accepted proof was timed**.
2. **`stream_s` is the thin cap, and the projection below is not measured.** The real harness could not run a full
   stream because step 1 was rejected. The projection is built from parts that were each measured on a 7763:
   - the prover's 96-step stream: 1,110 s of requests including start-ups;
   - the badge's checks, which count against `stream_s`: each badge run has a **≈ 11.7 s start-up** (Lean
     initialisation of the entry's closed constants), and the harness runs 2 of them per 8 steps, so ≈ 336 s per
     stream;
   - the calibration samples: ≈ 57 s.

   The sum is **≈ 1,530 s** of 1,920 (**1.26×**) for this draw. For a heavy draw (E1's model: max/mean 1.14 on
   request time) it is ≈ 1,680 s (**1.14×**). If the stream reaches the cap it is *truncated*, not rejected, but a
   truncated run is not comparable and is not ranked (`aggregate.py`). The badge's start-up is the lever, and it is
   entirely the entry's. E1's projection (1,150 mean / 1,311 max) assumed 2.04 s of overhead per step; the measured
   check overhead alone is ≈ 3.5 s per step.
3. **No other cap is under 1.2×.**
   - Kernel (`certified`): 396.8 s on the one 7763 that ran it (**1.51×**). 7763 hosts have differed by 11 % before
     (H-cert3), so a slow 7763 would be ≈ 440 s (≈ 1.36×).
   - Kernel upper set (the whole FR closure, which will matter once `Open4F` is proved): 497.8 s (**1.21×**). On a
     slow 7763 it may fall below 1.2×.
   - Worst first step: 43.8 s against 60 (**1.37×**).

## 1. Caps against measurements (EPYC 7763 unless stated)

| cap | value | measured | margin | runs (CPU) |
|---|---|---|---|---|
| `build_s` (certificate: Lean build, harness `evaluate.py cert`) | 1,200 s | **759.8 / 812.0 / 775.1 / 785.4 / 752.4 s**; max 812.0 | **1.48×** | si-cert in 40948267506, 40948268695 (7763); run1-badge 40949582143, 40949581961 (7763); run1-dos 40951275110 (7763). Real eval cert job 40944222197: 629.3 s (Xeon 8573C) |
| `kernel_s` (comparator, `certified` + `submission`; probe/cert2, challenge = solution) | 600 s | **396.8 s** (366 s without the full-size challenge export) | **1.51×** (1.64×) | 40948267506 (7763). Others: 359.1, 396.4 (9V74); 304.7, 294.5, 275.5 (9V45) |
| kernel, upper set (every non-control FR declaration in Solution's closure) | 600 s | **497.8 s** (463 s) | **1.21×** (1.30×) | 40948267506 (7763); 9V74 459.5 / 497.2; 9V45 374.0 / 384.1 / 353.8 |
| comparator peak memory | 14G scope | 4.63 GiB (`certified`), 4.84 GiB (upper) | 3.0× | all cert2 runs |
| `gate_s` | 120 s | 13.0 / 13.5 / 13.0 / 14.0 / 13.1 s | **8.6×** | as `build_s`; gate `PASS` |
| `badge_s` | 180 s | 61.0 / 63.1 / 60.5 / 64.4 / 60.3 s | **2.80×** | as `build_s` |
| `[caps] build_s` (the prover's build: `gcc -static -O2 -pthread prover.s`, 23 MB) | 120 s | 1.39 / 1.63 s (probe; 9V74 2.13 s); in the harness's sandbox ≈ 2 s (9V74, eval log 20:19:57 → 20:19:59) | **≈ 70×** | 40944220647, 40951275110 (7763) |
| `setup_s` (`prover setup`) | 240 s | **59.5 / 66.1 / 69.7 / 70.1 s**; harness (sandboxed, 9V74) 62.5 s where the probe on a 9V74 took 49.6 s | **3.4×** (harness-scaled ≈ 88 s: 2.7×) | 40944220647, 40951275110, 40949581961, 40949582143 (7763); eval 40944222197 (9V74) |
| `setup_cap` (the setup directory) | 4 GiB | 277.7 MB (setup peak RSS 7.14 GB, against the prover's 11G) | 15× | as above |
| `step_s`, worst first step (2^20 + 2^20, N8 over k = 4 + 4) | 60 s | **43.81 s** (9V74: 36.50 s) | **1.37×** | 40944220647 (7763), 40944220918 (9V74) |
| `step_s`, later step 2^20 (N4) | 60 s | 24.83 / 24.92 s; max of the 96-step stream 25.58 s (n = 1,045,444) | **2.35×** | 40944220647 |
| `ready_s` (start-up to the `ready` line) | 10 s | max 0.77 s over 96 steps (0.87 s on a first step elsewhere); harness on 9V74: 0.61 s | **11.5×** | 40944220647, 40951275110 |
| `stream_s` (M = 96) | 1,920 s | **projected 1,530 s** (heavy draw ≈ 1,680 s); parts in §2 | **1.26×** (1.14×) | prover 40944220647; badge 40949582143, 40949581961, 40951275110 |
| `verify_s` (one `acc` check: parse plus acc, badge clock, one pinned core) | 10 s | N8 0.204–0.213 s; N2 0.241–0.263 s; N4 0.259–0.261 s (rejected proofs, see §0) | **≈ 37×** | 40949582143, 40949581961, 40951275110 (7763); Xeon 8573C 0.17–0.23 s |
| badge start-up (one `verify --batch` run, sandboxed) | (inside `stream_s`) | **11.6–12.2 s** per run; a batch of warm + 8 checks takes 13.8–14.1 s | — | same |
| `T_triv` (chaincheck, 2^24 compressions, one core) → `v_ref = T_triv / R` | — | T_triv **2.061 s**, v_ref **206 ms** (Xeon 8573C: 2.309 s, 231 ms) | — | 40951275110 (7763), 40951275805 (Xeon) |
| DoS per-item cap `10 · v_ref` | 2,061 ms | max item **29.0 ms** of 100 `dos_inputs` on a stream output (π bit flips 16 ms median) | **71×** (Xeon: 23.2 ms of 2,309 ms, 99×) | as above |
| DoS `total_s` (the whole column, one badge run) | 180 s | 12.6 s (Xeon 11.7 s) | 14× | as above |

Notes:
- **V and v_ref.** One full V check (0.20–0.26 s) is about one v_ref (206 ms), so x_V ≈ 1.0–1.27. That matters for
  the score. The DoS column's caps are far away: the worst conceivable DoS item is a full V run (0.26 s), which is
  still ≈ 8× under 10·v_ref.
- **Leaves.** No leaf proof was checked. The harness's stream checks only node outputs: `first` is an N8 and every
  `step` is an N2 or N4.
- **Prover memory.** The harness recorded a peak of 6.65–6.77 GiB per request (9V74), against `memory.prover` 11G.

## 2. The stream: what was measured, and the projection

**Prover alone** (`probe/run1-prover`: the core's rf-oracle, `prover first`/`step` with the ready/go/done
handshake, a fresh process for each request, every output checked by the native `acc` with its canary rejected):

- **7763, run 40944220647.** M = 96 at the season's density, seeded draw `logs/RUN1/run-40944220647/…/full-chains.txt`:
  - requests 1,045.2 s, plus start-ups 64.7 s, total **1,109.9 s**;
  - mean request 10.89 s; first request 14.06 s; largest request 25.58 s;
  - all 96 accepted and every canary rejected (native `acc`);
  - wall time 1,217.2 s, including two native `acc` runs per step.
- **9V74, run 40944220918.** The same draw: 864.3 / 914.1 s. The 7763/9V74 ratio is **1.21**.

**Harness-side costs inside `stream_s`.** `rfh/bench.py` charges every request, check, canary and calibration sample
against the stream's cap. Each was measured on a 7763 with the harness's own `rfh.checks.Badge` in its sandbox, on
the badge built by `evaluate.py cert`:

| part | per unit | units for M = 96 | seconds |
|---|---|---|---|
| requests (P plus start-up; the probe's draw) | — | 96 | 1,110 |
| staging and kill (harness, 9V74 eval log: 19.0 s between steps 1 and 2 for P = 18.25 s, start-up 0.61 s, kill 0.07 s) | ≈ 0.14 s | 96 | ≈ 13 |
| output checks: `check_every` 8, best of two, each badge run warmed | 13.8–14.1 s per badge run (warm + 8) | 12 batches × 2 runs | ≈ 336 |
| canaries (π₁, π₂, π_M; one badge run) | ≈ 11.8 s | 1 | ≈ 12 |
| calibration samples: idle 2 s, 3 × `calib`, one `chaincheck` | ≈ 2 + ≈ 0.6 + 2.1 s | 12 | ≈ 57 |
| **total** | | | **≈ 1,530 s of 1,920 (1.26×)** |

- **Spread.** This draw's mean request is 10.89 s; E1's model gives ≈ 9.9 s for an average draw. An average stream
  would come to ≈ 1,430 s (1.34×). A heavy draw (E1's model: max/mean of request time 1.14 over 20,000 draws) would
  come to ≈ 1,680 s (1.14×).
- **Re-timing.** The re-timing (§5.3: at most 9 re-runs, each with its own 2-run check) comes after the main steps,
  and on reaching the cap "the first times stand", so it cannot truncate the stream.
- **The lever.** The badge's start-up is ≈ 11.7 s of every 14 s badge run, about 280 s per stream (24 + 1 runs). It is
  the Lean runtime initialising the entry's top-level closed constants, a property of the compiled `submission`.
  Making the large tables lazy would cut most of it: on the same runners `chaincheck` starts in ≈ 0.06 s.
- **Why this is a projection.** The real harness's stream could not run, because step 1 was rejected (§0). Re-measure
  with the eval branch once the prover carries IMP's rows.

## 3. Runs

| run | branch | workflow | jobs, CPU |
|---|---|---|---|
| 40944222197 | `probe/run1-eval` | `eval-push` (the core's `evaluate.yml` at `422f2f9`; trigger widened to `probe/run1-eval*`, `.github/eval.conf` ROOT=submissions/flock-recursive, season.toml, SPLIT=true; `probe.yml` dropped on that branch) | certificate: Xeon Platinum 8573C (provisional; build 629.3, comparator 59.3 (statement check), gate 10.4, badge 47.8 s; 304 modules); benchmark: 9V74 (setup 62.5 s; 8 steps, then **REJECT**); attest OK |
| 40944220647 | `probe/run1-a` | probe: cert2, run1-prover | cert2 9V74; run1-prover **7763** |
| 40944220918 | `probe/run1-b` | same | cert2 9V45; run1-prover 9V74 |
| 40948267506 | `probe/run1-c` | si-cert, cert2 | si-cert **7763**; cert2 **7763** |
| 40948268695 | `probe/run1-d` | same | si-cert **7763**; cert2 9V74 |
| 40949582143 | `probe/run1-e` | run1-badge (si-cert, then the badge timed on 8 stream outputs) | **7763** |
| 40949581961 | `probe/run1-f` | same | **7763** |
| 40951275805 | `probe/run1-g` | run1-dos (run1-badge plus T_triv/v_ref plus the DoS column via `rfh`) | Xeon 8573C |
| 40951275110 | `probe/run1-h` | same | **7763** |
| 40954386024 / 40954386035 | `probe/run1-i` / `-j` | cert2 | 9V45 / 9V45 |

URLs: `https://github.com/scaraven/recursion.fast-submissions/actions/runs/<id>`.

**The runner tier is not guaranteed to be a 7763.** Of the 16 measuring jobs:
- 7 ran on an AMD EPYC 7763;
- 4 on a 9V74;
- 3 on a 9V45;
- 2 on an Intel Xeon Platinum 8573C (the real eval's certificate job, and run1-g).

The real eval's attested result records `cpu_models`. A ranked evaluation may land on any of these.

## 4. Not measured, and why

- **Acceptance of a stream by the real harness.** The entry is rejected at `200b531` (§0). Every number the real
  benchmark would add for M = 96 is a projection from measured parts: `stream_s` in full, re-timing, the DoS column
  on π_M, and `c_P`/`T_triv` medians.
- **V of an accepted proof.** Only rejected proofs exist at `200b531`. Their V runs 0.20–0.27 s on a 7763.
- **A second 7763 kernel sample.** Four extra cert2 runs landed on a 9V74 or a 9V45. The single 7763 value is
  396.8 s.
- **`calib`'s own run time.** It is inside the sample estimate (0.6 s, from `ref_ns` 200 ms × 3). It was not
  timed separately.
- **Leaf proofs under the badge.** Not part of the stream's checks.

## 5. Files

`logs/RUN1/`:
- `run1-prover-run.sh`, `stream.sh` (p2t13's, with the previous work directory removed), `run1-badge-run.sh`,
  `run1-dos-run.sh`;
- `eval-push.yml`, `eval.conf`, `probe*.conf`, `commits.txt`, `runs.txt`;
- `eval-40944222197/`: `certificate/cert.json`, `badge.sha256`, `result/result.json`, `result-0/result-0.json`,
  and the two job logs;
- `run-<id>/probe-<name>/` for every probe job. The setup images and binaries were removed after reading, and the
  badge's sha256 was kept.
