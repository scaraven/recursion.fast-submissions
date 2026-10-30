# RUN2 RESULT: full evaluation of `v4/rev44` at `37deb5c` on GitHub runners (certificate + benchmark)

Track RUN2, 2026-10-30. The entry is `submissions/flock-recursive` at **`37deb5c`** (E1b: prover resynced to the
node circuit at `3d9ae68`), with the core pinned at `422f2f9`.

I repeated RUN2a's full-pipeline probe exactly, on **two** branches pushed at once, to sample CPU variance.
- **Probe commit.** `87e8904` is one commit on `37deb5c` that touches only `.github/`. It adds `.github/eval.conf`
  (ROOT=submissions/flock-recursive, SEASON=harness/season.toml, SPLIT=true), widens `eval-push.yml`'s trigger to
  `probe/run2-eval*`, and drops `probe.yml`. This is RUN2a's `d952126` diff with the pattern renamed.
- **Branches.** `probe/run2-eval` (run 41012684797) and `probe/run2-eval-2` (run 41012684725).
- **Workflow.** Both runs use the core's `evaluate.yml` at `422f2f9`.
- **Cleanup.** Both branches and the worktree were deleted afterwards (§6).
- **Logs** are in `logs/RUN2/`: `commits.txt`, `runs.txt`, `eval-push.yml`, `eval.conf`, and for each run
  `eval-<id>/` with `{certificate,benchmark,attest}-job.log`, `certificate/{cert.json,badge.sha256}`,
  `result-0/result-0.json`, `result/result.json`, `summary.txt` and `project.txt`.
- **Analysis scripts**: `summ.py`, `timeline.py` and `project.py`.

No entry source was edited, and nothing was committed.

## 0. Verdict

1. **Both runs: certificate `ok`, benchmark `ACCEPT`, M = 96, not truncated, comparable, attested.**
   - Run 41012684797:
     - certificate on a **Xeon Platinum 8573C**: `logs/RUN2/eval-41012684797/certificate-job.log:395`
       `2026-10-30T06:45:14.3709205Z certificate: ok []`;
     - benchmark on an **EPYC 9V45**: `logs/RUN2/eval-41012684797/benchmark-job.log:442,445`
       `07:03:52 score: S = 29.0458 (P̄ 4.5233, V̄ 24.5224), M = 96` / `VERDICT: ACCEPT`.
   - Run 41012684725:
     - certificate on an **EPYC 7763**: `logs/RUN2/eval-41012684725/certificate-job.log:381`
       `2026-10-30T06:46:56.2577412Z certificate: ok []`;
     - benchmark on an **EPYC 9V74**: `logs/RUN2/eval-41012684725/benchmark-job.log:442,445`
       `07:16:49 score: S = 34.1998 (P̄ 6.7811, V̄ 27.4187), M = 96` / `VERDICT: ACCEPT`.
   - The comparator tail is the same in both `cert.json` files: `Lean default kernel accepts the solution` /
     `Your solution is okay!`. Both have `gate ["PASS"]` and 373 built modules.
   - Attested `result.json`, both runs: `verdict ACCEPT`, `comparable true`, `truncated false`,
     `mixed_cpu false`, `prover_sha256 403e6937…`, `harness_commit 422f2f9…`.
     The attestations are `attestations/61643404` and `/61646982`.
2. **No cap was breached. `stream_s` is the thin cap: 1,688.7 s of 1,920 (1.14×)** on the 9V74, which was a slow
   host, with an average draw (z = +0.04).
   - With heavier draws of the season's density on that host it projects to p99 ≈ 1,790 s (1.07×), p99.9
     ≈ 1,834 s (1.05×), and ≈ 1,866 s (1.03×) for the max of 20,000 draws.
   - On the 9V45 it took 1,043.3 s (1.84×).
   - A breach does not REJECT. The stream is scored over its completed steps, flagged `truncated`, and the run is
     **not ranked** (PROVER.md §"stream", `aggregate.py:115`).
3. **The certificate side matches RUN2a.** The Lean code is unchanged since `3d9ae68`, and the badge sha256 is
   identical. `build_s` on the 7763 was 968.2 s (1.24×; RUN2a 983.6 s).
4. **The benchmark never landed on a 7763** (0 of 2; RUN2a's also ran on a 9V74). A 7763 stream is
   projected, not measured (§3.3).

## 1. Cap table

Per run. The "margin" column is cap / measured.

### Certificate (season `[certificate]`, 4-vCPU runner)

| cap | run 41012684797 (Xeon 8573C) | run 41012684725 (**EPYC 7763**) | worst margin | RUN2a (7763) |
|---|---|---|---|---|
| `build_s` 1,200 (breach = REJECT) | 747.0 s (1.61×) | **968.2 s (1.24×)** | **1.24×** | 983.6 s |
| `kernel_s` 600 (comparator) | 306.7 s (1.96×) | 378.2 s (1.59×) | 1.59× | 368.7 s |
| `gate_s` 120 | 11.6 s (10.3×) | 15.8 s (7.6×) | 7.6× | 15.0 s |
| `badge_s` 180 | 57.0 s (3.16×) | 79.4 s (2.27×) | 2.27× | 76.5 s |
| comparator memory (cap 14G) | 4.69 GB | 4.70 GB | 3.0× | 4.55–4.70 GB |
| certificate job (`timeout-minutes` 40) | 1,274 s | 1,534 s | 1.56× | 1,544 s |

The badge sha256 is the same in both runs and in RUN2a: `verify 0ce7a2de…`, `chaincheck e54e8b27…`.

### Benchmark (season `[stream]`, `[caps]`, `[dos]`, `[memory]`)

| cap | run 41012684797 (EPYC 9V45) | run 41012684725 (EPYC 9V74) | worst margin |
|---|---|---|---|
| prover `build_s` 120 | ≤ 1.8 s (benchmark start → `prover built`) | ≤ 3.6 s | 33× |
| `setup_s` 240 | 38.7 s | **65.7 s** | **3.65×** |
| setup peak RSS (prover 11G) | 7,389 MB | 7,382 MB | 1.5× |
| `ready_s` 10 (start-up to `ready`, max of 96) | 0.82 s | 1.24 s | 8.0× |
| `step_s` 60, worst drawn step | 14.74 s (step 59, n = 949,212) | **24.45 s** (step 77, n = 857,368) | **2.45×** |
| `step_s` 60, first step | 9.30 s (n = 450,371) | 15.33 s (n = 408,989) | 3.9× |
| `step_s` 60, **worst first step 2^20 + 2^20** (not drawn) | — | projected ≈ 46 s (§3.2) | ≈ 1.3× |
| **`stream_s` 1,920** | **1,043.3 s** | **1,688.7 s** | **1.14×** |
| `verify_s` 10 (one `acc`, worst best-of-two) | 0.650 s | 1.005 s | 10× |
| prover memory 11G (per request peak) | 7.80 GB | 7.63 GB | 1.4× |
| `work_cap` 4 GiB | 4.9 MB | 4.9 MB | ≫ |
| DoS per item `10·v_ref` | max 30.1 ms of 1,524 ms (dos/30.bin) | max 21.9 ms of 2,306 ms (dos/95.bin) | 50× |
| DoS column `total_s` 180 | 4.8 s wall, 0 of 100 accepted | 7.3 s wall, 0 of 100 accepted | 25× |
| benchmark job (`timeout-minutes` 50) | 1,116 s | 1,795 s | 1.67× |
| re-timing (step > 1.3 × fit reruns) | 0 candidates; max ratio 1.263 | 0 candidates; max ratio 1.257 | 1.03× to the trigger |

- `stream_s` here is measured from the `[stream] computing 97 leaf digests` line to the `c_P = …` line. This
  slightly over-counts the harness's clock, which starts after the digests and the service start-up.
- Score and calibration:
  - 9V45: S = 29.05, P̄ 4.52, V̄ 24.52 (V share 84 %); c_P 1.283 (provisional), T_triv 1.524 s, v_ref 152.4 ms.
  - 9V74: S = 34.20, P̄ 6.78, V̄ 27.42 (V share 80 %); c_P 1.533, T_triv 2.306 s, v_ref 230.6 ms.
- `cpu_models`: `["AMD EPYC 9V45 96-Core Processor"]` and `["AMD EPYC 9V74 80-Core Processor"]`. Neither is
  `mixed_cpu`.
- Every step `ended_by: line`. The proof file is 2,432,199 B (π 876,304 B). The service logged 0 refusals and 193
  signatures, and the 8 canaries were all rejected (`canaries 8`).

## 2. The stream, part by part

From `logs/RUN2/eval-<id>/summary.txt`. The per-step parts are in `result-0.json`; the gaps between steps come from
the job log's timestamps.

| part | 9V45 (41012684797) | **9V74 (41012684725)** | E1b projection (7763, M = 96, mean draw) |
|---|---|---|---|
| draw: Σn over 97 leaves (z vs the season's density) | 32.30 M (z = +1.05) | 30.28 M (z = +0.04) | mean (≈ 30.2 M) |
| prover requests, Σ P | 661.1 s (mean 6.89, max 14.74) | **1,124.4 s** (mean 11.71, max 24.45) | — |
| prover start-ups (to `ready`), Σ | 71.2 s (0.74 s each) | 108.7 s (1.13 s each) | — |
| **prover side** (requests + start-ups) | **732.3 s** | **1,233.1 s** | **1,115 s** (max draw 1,277) |
| kills | 5.0 s | 6.7 s | 13 s with staging |
| staging (gap minus P, start-up and kill, between non-batch steps) | ≈ 0 (−0.05 s/step: log-timestamp offset) | ≈ 0 (−0.06 s/step) | (in the 13 s above) |
| V checks, timed (best of two, both runs, 96 outputs) | 120.8 s (V 0.62 s mean) | **190.0 s** (V 0.98 s mean) | 176 s (≈ 220 checks at 0.8 s) |
| badge start-ups + warm checks + canary run + digests/service | ≈ 129 s | ≈ 192 s | 290 s (29 runs × 10 s start-up) |
| calibration samples (13: idle 2 s + 3 × calib + chaincheck) | ≈ 56 s (≈ 4.3 s each) | ≈ 67 s (≈ 5.2 s each) | 57 s |
| **harness side** | **311 s** | **449 s** | **536 s** |
| **`stream_s`** | **1,043.3 s (1.84×)** | **1,688.7 s (1.14×)** | **1,651 s (1.16×)**; max draw 1,813 s (1.06×) |

- **The batch boundary** is the gap before steps 9, 17, …, 89. It holds 2 badge runs of warm + 8 checks, one
  calibration sample and staging. It is 24.8 s on the 9V45 (23.3–25.5) and 36.3 s on the 9V74 (34.3–37.0), 11 per
  stream.
  - From these, one badge start-up (V init) comes out at ≈ 4.6 s on the 9V45 and ≈ 6.8 s on the 9V74.
  - E1b assumed ≈ 10 s, and RUN1's sandboxed 7763 probe measured 11.6–12.2 s.
- **The tail**: the last flush, the closing sample, the canary run, the re-timing (0 reruns) and the stop. It is
  29.1 s on the 9V45 and 43.1 s on the 9V74.
- **Against E1b.** The 9V74 total is within 2 % of E1b's mean-draw projection, but the split differs.
  - The prover side is +118 s over the projection, because this 9V74 host is slow (§3.1).
  - The harness side is −87 s, because badge start-ups are ≈ 7 s, not 10 s.
  - V per accepted check is 0.98 s on the 9V74 (0.62 s on the 9V45), against E1b's 0.8 s estimate for a 7763.
- **The prover is 66 % of the stream on the 9V74 and 70 % on the 9V45.** The V side (checks, badge start-ups and
  canaries) is ≈ 22 % and ≈ 24 %.

## 3. What threatens a cap

### 3.1 `stream_s` (1.14× measured; not REJECT, but a truncated run is not ranked)

- **This 9V74 host is slow.** Its 1-thread service throughput was 10.77 M calls/s, against 14.07 M on RUN2a's 9V74,
  11.24 M on RUN1's eval 9V74 and 17.64 M on this RUN2's 9V45. Its T_triv was 2.306 s, against 2.061 s on RUN1's
  7763.
  - The prover's fit on this host is P ≈ 6.01 s + 1.64e-5 s·n (trimmed). The OLS slope is 2.17e-5 s per
    compression, because large steps run above the trimmed fit.
  - The same fit on the 9V45 is 3.47 s + 8.97e-6 s·n.
- **Heavy draws on this host** (`logs/RUN2/eval-41012684725/project.txt`, `project.py`): 20,000 draws of 97
  lengths at the season's density. The extra compressions are priced at this run's OLS slope, and the harness side
  is held at its measured value.

  | draw | Σn | `stream_s` | margin |
  |---|---|---|---|
  | median | 30.16 M | 1,686 s | 1.14× |
  | p90 | 32.77 M | 1,743 s | 1.10× |
  | p99 | 34.95 M | 1,790 s | 1.07× |
  | p99.9 | 36.97 M | 1,834 s | 1.05× |
  | max of 20,000 | 38.45 M | 1,866 s | 1.03× |

  The same projection on the 9V45 is 1,017–1,118 s (1.89×–1.72×).
- **Re-timing is a hidden cost inside `stream_s`.** A cluster of mid-size steps (n ≈ 550 k–810 k) sits at
  1.21–1.26 × the trimmed fit, and the trigger is 1.3×. If noise pushes them over, up to 9 steps (10 %) run again
  inside the cap: ≈ 10–25 s each on this 9V74, up to ≈ 200 s. Neither run triggered it (0 candidates).
- **A 7763 benchmark host is unmeasured.**
  - Prover side: E1b projects 1,115 s at the mean draw on a 7763. That is below this 9V74's 1,233 s, and RUN1
    measured the 7763 at 1.21× slower than a 9V74 for the old prover.
  - Harness side:
    - if the badge start-up on a 7763 is like this 9V74's (≈ 7 s), it stays ≈ 450 s;
    - if it is RUN1's sandboxed 11.6–12.2 s, it adds ≈ +125 s;
    - V checks scaled like Lean work on a 7763 (≈ 1.2×) add ≈ +40 s.
  - Total: a 7763 at the mean draw is **≈ 1,565–1,730 s (1.23×–1.11×)**, and at a p99 draw ≈ 1,665–1,830 s
    (1.15×–1.05×). This is a projection with that spread, not a measurement.
- **Bottom line.** On a slow host with a heavy draw the stream comes within 3–7 % of the cap. A re-time cluster or
  a slower host would push it over. That would truncate the run, and a truncated run is unranked, not rejected.

### 3.2 Worst first step (`step_s` 60; breach = the entry's failure)

- No run drew a large first step. Steps 1 were 9.30 s (n = 450,371) and 15.33 s (n = 408,989), at 1.24× and 1.21×
  the trimmed fit.
- Projection for this 9V74 host:
  - 2^20 later step ≈ 27 s (measured 24.34 s at n = 905,128, plus the OLS slope);
  - E1b's ratio of worst first step to a 2^20 step is 42.09 / 25.07 = 1.68;
  - so the 2^20 + 2^20 first step is **≈ 46 s (≈ 1.3×)**.
- E1b projected ≈ 42–44 s on a 7763 (1.36–1.43×). RUN1 measured the old prover at 43.81 s on a 7763 and 36.50 s on
  a 9V74.
- A slower host than this one would eat directly into this margin, and a breach here is a REJECT. **It is the
  hardest-failing cap, even though `stream_s` has less margin.**

### 3.3 `build_s` (certificate; breach = REJECT)

- 968.2 s on a 7763 (1.24×), the same as RUN2a's 910–984 s band.
- This stage did not change it. Any growth of `certified`'s import closure still comes straight out of the ≈ 230 s
  of headroom.

### 3.4 Not a threat

`setup_s` (≥ 3.65×), `ready_s` (≥ 8×), `verify_s` (≥ 10×), DoS (≥ 25×), memory (≥ 1.4×), `kernel_s` (≥ 1.59×),
gate and badge (≥ 2.27×).

## 4. Levers if `stream_s` or the first step must gain margin (no code was changed)

Ordered by what the measurements say they buy:

1. **Prover side: factor arena₁ rows and prototype-0 replay rows**, instead of treating them as link rows (E1b §6).
   - The prover is 66–70 % of the stream: 1,124 s of requests plus 109 s of start-ups (1.13 s each) on the 9V74.
   - This lever cuts the link work in `e2`/`e4`, which applies to every step, including the worst first step. It
     also cuts the start-up's by-cell indices.
   - It is the only lever that also helps `step_s`.
2. **V side: closed forms for the replay rows** (`rv1`, SEG-R2 §9.3).
   - V is 0.98 s per check on the 9V74, which over ≈ 200 timed and warm checks is ≈ 210 s.
   - It also shortens the V init, ≈ 7 s × 25 badge runs ≈ 170 s.
   - It does not help `step_s`, but V̄ is 80–84 % of the score S, so it is also the score lever.
3. Holding a heavy-draw 9V74 at ≥ 1.2× needs ≈ 1,600 s, which is ≈ 235 s off the p99.9 projection. Either lever
   alone plausibly reaches this: 20 % off the prover side is ≈ 245 s; halving V and its init is ≈ 190 s.

## 5. Runs

| run | branch | commit | certificate job | benchmark job | attest |
|---|---|---|---|---|---|
| 41012684797 | `probe/run2-eval` | `87e8904` | Xeon Platinum 8573C, `ok` (build 747.0, comparator 306.7, gate 11.6, badge 57.0) | EPYC 9V45, **ACCEPT**, M = 96, `stream_s` 1,043.3 s | OK (61643404) |
| 41012684725 | `probe/run2-eval-2` | `87e8904` | **EPYC 7763**, `ok` (build 968.2, comparator 378.2, gate 15.8, badge 79.4) | EPYC 9V74, **ACCEPT**, M = 96, `stream_s` 1,688.7 s | OK (61646982) |

URLs: `https://github.com/scaraven/recursion.fast-submissions/actions/runs/<id>`.

## 6. Probe branches pushed and deleted

- **Pushed:** `probe/run2-eval` and `probe/run2-eval-2`, both at `87e8904`, one commit on `37deb5c` (see
  `logs/RUN2/commits.txt`).
- **Deleted from the remote:** `git push origin --delete probe/run2-eval probe/run2-eval-2`, both reported
  `[deleted]`. Afterwards `git ls-remote origin 'refs/heads/probe/run2*'` returns nothing.
- **Deleted locally:** both branches, with `git branch -D`. The worktree `/home/devops/Verified-zkEVM/rf-run2` was
  removed.
- **Untouched:** the remote branches `probe/fr-vtime-{1..5}` and `probe/phase0`, which this stage did not push.
- **Not pushed to:** `v4/rev44`, `v4/flock-recursive` and `main`.
