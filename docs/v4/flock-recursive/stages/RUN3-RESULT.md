# RUN3 RESULT: full evaluation of `v4/flock-submit` at `96eb0f6` on GitHub runners (certificate + benchmark)

Track RUN3, 2026-10-30. The entry is `submissions/flock-recursive` at **`96eb0f6`** (`v4/flock-submit`: one commit on
`v4/flock-recursive`, identical to `v4/rev44` `c390276`; G6 certificate build cut + P2r prover), with the core pinned at
`422f2f9`.

I repeated RUN2's full-pipeline probe exactly, on **two** branches pushed at once.
- **Probe commit.** `570a3a2` is one commit on `96eb0f6` that touches only `.github/`. It adds `.github/eval.conf`
  (ROOT=submissions/flock-recursive, SEASON=harness/season.toml, SPLIT=true), widens `eval-push.yml`'s trigger to
  `probe/run3-eval*`, and drops `probe.yml`. This is RUN2's `87e8904` diff (cherry-picked) with the pattern renamed.
- **Branches.** `probe/run3-eval` (run 41042457623) and `probe/run3-eval-2` (run 41042457436).
- **Workflow.** Both runs use the core's `evaluate.yml` at `422f2f9`.
- **Cleanup.** Both branches and the worktree were deleted afterwards (§6).
- **Logs** are in `logs/RUN3/`, in RUN2's layout: `commits.txt`, `runs.txt`, `eval-push.yml`, `eval.conf`,
  `wait.log`, and for each run `eval-<id>/` with `{certificate,benchmark,attest}-job.log`,
  `certificate/{cert.json,badge.sha256}`, `result-0/result-0.json`, `result/result.json`, `summary.txt` and
  `project.txt`.
- **Analysis scripts**: `summ.py`, `timeline.py` and `project.py`, copied unchanged from `logs/RUN2/`.

No entry source was edited, and nothing was committed.

## 0. Verdict

1. **Both runs: certificate `ok`, benchmark `ACCEPT`, M = 96, not truncated, comparable, attested.**
   - Run 41042457623:
     - certificate on an **EPYC 9V45**: `logs/RUN3/eval-41042457623/certificate-job.log:394`
       `2026-10-30T11:06:26.0820632Z certificate: ok []`;
     - benchmark on a **Xeon Platinum 8370C**: `logs/RUN3/eval-41042457623/benchmark-job.log:445,448`
       `11:36:29 score: S = 16.1039 (P̄ 4.9420, V̄ 11.1619), M = 96` / `VERDICT: ACCEPT`.
   - Run 41042457436:
     - certificate on an **EPYC 9V45**: `logs/RUN3/eval-41042457436/certificate-job.log:388`
       `2026-10-30T11:07:19.6869811Z certificate: ok []`;
     - benchmark on an **EPYC 9V45**: `logs/RUN3/eval-41042457436/benchmark-job.log:442,445`
       `11:24:45 score: S = 28.5315 (P̄ 4.1132, V̄ 24.4184), M = 96` / `VERDICT: ACCEPT`.
   - The comparator tail is the same in both `cert.json` files: `Lean default kernel accepts the solution` /
     `Your solution is okay!`. Both have `gate ["PASS"]`, 146 built modules listed and "one build (292 artifacts)".
   - Attested `result.json`, both runs: `verdict ACCEPT`, `comparable true`, `truncated false`,
     `mixed_cpu false`, `prover_sha256 14b02362…` (the built binary, 25,846,856 B; its source
     `prover/prover.s` at `96eb0f6` has sha256 `377549016b0c4b6e…`, as P2r states), `harness_commit 422f2f9…`.
     The attestations are `attestations/61734913` and `/61730463`.
2. **No cap was breached, but `stream_s` is thinner than in RUN2: 1,713.7 s of 1,920 (1.12×)** on the Xeon 8370C,
   with a *light* draw (z = −1.08). RUN2's worst was 1,688.7 s (1.14×) at z = +0.04.
   - **Cause: re-timing now fires.** P2r made small steps faster than large ones (§2), so the large-step cluster now
     sits at 1.30–1.43× the harness's trimmed fit (RUN2: ≤ 1.263). The 8370C hit the re-time limit (10 candidates,
     9 reruns, 208 s of rerun work; the stream tail grew from 29–43 s to 351 s). The 9V45 reran 5 (65 s).
   - Heavy draws on the 8370C (`project.txt`): p99 1,855 s (1.03×), p99.9 1,897 s (1.01×), **max of 20,000 draws
     1,927 s (0.996×: a breach)**. A breach truncates the run and leaves it unranked; it does not REJECT.
   - **Orchestrator correction (see the last section): the re-time reruns cannot truncate the run.** The 1,927 s figure counts them.
3. **G6 confirmed on the certificate side, by scaling.** `build_s` 461.8 s and 492.6 s, both on a 9V45 (no 7763 this
   time). With H-cert3's measured 9V45/7763 factor (0.654–0.656) that is **≈ 705–752 s at 7763 speed (1.70–1.60×)**,
   against RUN2's 968.2 s (1.24×) measured on a 7763. G6 projected 655–700 s; the scaled figure is 5–15 % above that
   band but still ≈ 220–260 s below RUN2.
4. **P2r confirmed on the prover side.** On the same CPU model (9V45, near-identical service throughput: 17.87 M vs
   17.64 M calls/s) the start-up fell from 0.742 to 0.401 s (−46 %), and the later steps at RUN2's draw cost 559.7 s
   instead of 651.8 s (−14 %). That is more than P2r's −86 s projection for the 9V74, but the re-time it triggers
   eats the gain and more (§3.1).
5. **Neither the certificate nor the benchmark landed on a 7763 or a 9V74** (CPU models: 9V45, 9V45; 8370C, 9V45).

## 1. Cap table

Per run. The "margin" column is cap / measured. "RUN2 worst" is the worst of RUN2's two runs.

### Certificate (season `[certificate]`, 4-vCPU runner)

| cap | run 41042457623 (EPYC 9V45) | run 41042457436 (EPYC 9V45) | worst margin | RUN2 worst (7763) |
|---|---|---|---|---|
| `build_s` 1,200 (breach = REJECT) | 461.8 s (2.60×) | **492.6 s (2.44×)**; ≈ 705–752 s at 7763 speed (≈ 1.6×) | **2.44× (≈ 1.6× scaled)** | 968.2 s (1.24×) |
| `kernel_s` 600 (comparator) | 287.9 s (2.08×) | 307.9 s (1.95×) | 1.95× | 378.2 s (1.59×) |
| `gate_s` 120 | 8.1 s (14.8×) | 8.8 s (13.6×) | 13.6× | 15.8 s (7.6×) |
| `badge_s` 180 | 40.1 s (4.49×) | 42.0 s (4.29×) | 4.29× | 79.4 s (2.27×) |
| comparator memory (cap 14G) | 4.68 GB | 4.68 GB | 3.0× | 4.70 GB |
| certificate job (`timeout-minutes` 40) | 925 s | 973 s | 2.47× | 1,534 s (1.56×) |

- The comparator time is not reduced by G6 in the way the build is: 287.9–307.9 s on a 9V45 against 306.7 s on
  RUN2's Xeon 8573C (scaled to a 7763 ≈ 440–470 s with the build factor, which overstates it; RUN2a/RUN2 measured
  368.7–378.2 s on a 7763). Kernel replay is not what G6 cut.
- Badge sha256: `chaincheck e54e8b27…` is unchanged from RUN2; **`verify` changed, `ae36ba0a…` (RUN2 `0ce7a2de…`)**,
  identical in both RUN3 runs. This is expected: G6 merged the modules that `verify` is compiled from.

### Benchmark (season `[stream]`, `[caps]`, `[dos]`, `[memory]`)

| cap | run 41042457623 (Xeon 8370C) | run 41042457436 (EPYC 9V45) | worst margin | RUN2 worst |
|---|---|---|---|---|
| prover `build_s` 120 | ≤ 2.4 s (bench start → `prover built`) | ≤ 1.9 s | 50× | 33× |
| `setup_s` 240 | **52.5 s** | 35.0 s | **4.57×** | 3.65× |
| setup peak RSS (prover 11G) | 7,049 MB | 7,049 MB | 1.6× | 1.5× |
| `ready_s` 10 (start-up to `ready`, max of 96) | 0.72 s | 0.48 s | 13.9× | 8.0× |
| `step_s` 60, worst drawn step | **24.83 s** (step 1, n = 924,818) | 13.75 s (step 93, n = 966,203) | **2.42×** | 2.45× |
| `step_s` 60, first step | 24.83 s (n = 924,818) | 7.53 s (n = 338,866) | 2.42× | 3.9× |
| `step_s` 60, **worst first step 2^20 + 2^20** (not drawn) | projected ≈ 44 s (§3.2) | projected ≈ 25 s | ≈ 1.36× | ≈ 1.3× (9V74) |
| **`stream_s` 1,920** | **1,713.7 s** | 978.2 s | **1.12×** | 1.14× |
| `verify_s` 10 (one `acc`, worst best-of-two) | 0.685 s | 0.633 s | 14.6× | 10× |
| prover memory 11G (per request peak) | 7.24 GB | 7.24 GB | 1.5× | 1.4× |
| `work_cap` 4 GiB | 4.9 MB | 4.9 MB | ≫ | ≫ |
| DoS per item `10·v_ref` | **max 676.6 ms of 2,203 ms** (dos/83.bin, `over_v_ref 1`) | max 14.8 ms of 1,456 ms (dos/42.bin) | **3.26×** | 50× |
| DoS column `total_s` 180 | 7.2 s wall, 0 of 100 accepted | 4.9 s wall, 0 of 100 accepted | 25× | 25× |
| benchmark job (`timeout-minutes` 50) | 1,805 s | 1,046 s | 1.66× | 1.67× |
| re-timing (step > 1.3 × fit reruns, limit 9) | **10 candidates, 9 rerun** (max ratio 1.428) | **5 candidates, 5 rerun** (max ratio 1.375) | — | 0 candidates (max 1.263) |

- `stream_s` here is measured from the `[stream] computing 97 leaf digests` line to the `c_P = …` line, as in RUN2.
- One DoS item on the 8370C ran ≈ a full verification (676.6 ms, about one `acc`) before rejecting; RUN2's worst item
  was 30 ms. The cap is still 3.26× away and the badge's V is the same code; this is a draw of the mutation, not a
  regression, but it is the only DoS item over `v_ref` seen so far.
- Score and calibration:
  - 8370C: S = 16.10, P̄ 4.94, V̄ 11.16 (V share 69 %); c_P 1.959 (provisional), T_triv 2.203 s, v_ref 220.3 ms.
  - 9V45: S = 28.53, P̄ 4.11, V̄ 24.42 (V share 86 %); c_P 1.240 (provisional), T_triv 1.456 s, v_ref 145.6 ms.
    RUN2's 9V45: S = 29.05 (P̄ 4.52, V̄ 24.52).
- `cpu_models`: `["Intel(R) Xeon(R) Platinum 8370C CPU @ 2.80GHz"]` and `["AMD EPYC 9V45 96-Core Processor"]`.
  Neither is `mixed_cpu`.
- Every step `ended_by: line`. The proof file is 2,432,199 B (π 876,304 B), as in RUN2 (P2r: byte-identical proofs).
  The service logged 0 refusals (212 and 204 signatures), and the 8 canaries were all rejected (`canaries 8`).

## 2. The stream, part by part

From `logs/RUN3/eval-<id>/summary.txt`; the re-time and calibration rows are computed from `result-0.json`
(re-time = Σ over reruns of the second run's P + start-up + kill + both V runs; calibration = 13 × (calib + triv
runtime + 2 s idle)). "Rest" is `stream_s` minus every row above it: badge start-ups and warm checks, canary run,
digests/service, staging.

| part | **Xeon 8370C (41042457623)** | 9V45 (41042457436) | RUN2 9V45 | RUN2 9V74 |
|---|---|---|---|---|
| draw: Σn over 97 leaves (z vs the season's density) | 28.08 M (z = −1.08) | 28.87 M (z = −0.68) | 32.30 M (+1.05) | 30.28 M (+0.04) |
| prover requests, Σ P | **968.6 s** (mean 10.09, max 24.83) | 530.2 s (mean 5.52, max 13.75) | 661.1 s | 1,124.4 s |
| prover start-ups (to `ready`), Σ | 65.6 s (0.684 s each) | 38.5 s (0.401 s each) | 71.2 s (0.742) | 108.7 s (1.132) |
| **prover side** (requests + start-ups) | **1,034.3 s** | **568.7 s** | 732.3 s | 1,233.1 s |
| kills | 3.6 s | 4.8 s | 5.0 s | 6.7 s |
| V checks, timed (best of two, both runs, 96 outputs) | 129.2 s (V 0.67 s mean) | 114.7 s (V 0.59 s mean) | 120.8 s | 190.0 s |
| calibration samples (13) | ≈ 70 s (≈ 5.4 s each) | ≈ 54 s (≈ 4.2 s each) | ≈ 56 s | ≈ 67 s |
| **re-timing** (reruns: P + start-up + kill + V) | **208.1 s (9 reruns)** | 65.4 s (5 reruns) | 0 | 0 |
| rest (badge runs, canaries, digests/service, staging) | ≈ 269 s | ≈ 170 s | ≈ 129 s | ≈ 192 s |
| **harness side** (`stream_s` − prover side) | **679 s** | **410 s** | 311 s | 449 s |
| **`stream_s`** | **1,713.7 s (1.12×)** | **978.2 s (1.96×)** | 1,043.3 s (1.84×) | 1,688.7 s (1.14×) |

- **Batch boundary** (2 badge runs of warm + 8 checks, one calibration sample, staging; 11 per stream): 28.6 s on the
  8370C (27.3–28.9) and 23.4 s on the 9V45 (21.6–24.5; RUN2's 9V45 24.8 s).
- **The tail** (last flush, closing sample, canaries, re-timing, stop): **350.6 s on the 8370C** and 143.2 s on the
  9V45, against 29.1 s and 43.1 s in RUN2. The re-time reruns account for 208 s and 65 s of it; the rest of the
  growth is the reruns' badge and calibration overhead.
- **P2r, measured (same CPU model, 9V45 vs RUN2's 9V45).**
  - Start-up: 0.742 → 0.401 s per request (−46 %; −33 s per stream). P2r projected ≈ −45 %.
  - Requests, matched draw (RUN3's 9V45 steps interpolated at RUN2's 95 later-step lengths, 5-nearest median):
    651.8 → 559.7 s (−14 %).
  - The gain is uneven: steps with n < 640 k fell 16 % (mean 5.99 → 5.01 s), steps with n ≥ 640 k only 4 %
    (12.60 → 12.08 s). That unevenness is what pushes the large steps over the re-time trigger.
- **Without re-timing** (removing the tail's growth over RUN2's 29–43 s), the 9V45 stream would be ≈ 978 − 114 ≈
  865 s, ≈ 180 s below RUN2's 9V45 at a lighter draw (z −0.68 vs +1.05); the 8370C ≈ 1,713.7 − 315 ≈ 1,400 s.

## 3. What threatens a cap

### 3.1 `stream_s` (1.12× measured; not REJECT, but a truncated run is not ranked)

- **The re-time trigger now fires by construction, not by noise.** The harness fits P = b + a·n on trimmed steps and
  reruns any step above 1.3× the fit (`retime.limit` 9). Step cost is roughly two-level in n (on the 8370C ≈ 8.7 s
  for n < 640 k, ≈ 20.8 s above), and after P2r the upper level sits at 1.30–1.43× the line. The reruns reproduce the
  same times (ratios 1.33–1.43 on both attempts), so every large step is a candidate on any host.
  - 8370C: 11 steps with n ≥ 640 k, 10 candidates, 9 rerun (the limit) = **208 s**.
  - 9V45: 7 large steps, 5 candidates, 5 rerun = 65 s.
  - At the limit, the extra cost is ≈ 9 × (large-step P + start-up + 2 V) plus overhead: ≈ 210 s on the 8370C,
    ≈ 240 s on a RUN2-like 9V74 (23.5 + 1.1 + 2.0 s per rerun), ≈ 300 s of tail growth on the 8370C in total.
- **Heavy draws on the 8370C** (`logs/RUN3/eval-41042457623/project.txt`, `project.py`; extra compressions at the
  run's OLS slope 2.06e-5 s, harness side held at its measured value, which already includes the saturated re-time):

  | draw | Σn | `stream_s` | margin |
  |---|---|---|---|
  | median | 30.16 M | 1,757 s | 1.09× |
  | p90 | 32.77 M | 1,810 s | 1.06× |
  | p99 | 34.95 M | 1,855 s | 1.03× |
  | p99.9 | 36.97 M | 1,897 s | 1.01× |
  | max of 20,000 | 38.45 M | **1,927 s** | **0.996× (breach)** |

  The same projection on the 9V45 is 993–1,085 s (1.93×–1.77×).
- **A slow 9V74 like RUN2's (projection, not measured).** P2r's own projection for RUN2's 9V74 draw is 1,603 s with
  no re-time. RUN2's draw there had 7 large steps; with P2r all are likely candidates, ≈ 7 × 26.6 ≈ 186 s plus
  overhead, so ≈ 1,790–1,850 s (1.07–1.04×) at a mean draw. P2r's heavy-draw figure (1,780 s) plus a saturated
  re-time (≈ 240 s + overhead) is ≈ 2,020–2,100 s: **a breach on a heavy draw**. A 7763 host would be similar.
- **Bottom line.** P2r bought ≈ 14 % of prover requests and 46 % of start-ups, but by making the step cost less
  linear it moved the large-step cluster over the 1.3× re-time trigger, and the reruns (≈ 65–240 s) cost more than
  P2r saved on a mean draw. The stream now breaches on heavy draws on slow hosts (8370C max-of-20,000; 9V74 p90+ by
  projection). That truncates the run (unranked), it does not REJECT.
- **Levers (none applied):** make P closer to linear in n so large steps stay under 1.3× the trimmed fit (a cheaper
  large-step path, or not speeding small steps relative to large ones); any cut to the large-step level also cuts the
  reruns themselves.

### 3.2 Worst first step (`step_s` 60; breach = the entry's failure)

- The 8370C drew a large first step: **24.83 s at n = 924,818** (2.42×), re-timed at 24.85/24.83 s. The 9V45's first
  step was 7.53 s (n = 338,866).
- Projection for the 8370C (RUN2's method): a 2^20 later step ≈ 22.34 s (n = 856,405) + 2.06e-5 × 192 k ≈ 26.3 s;
  E1b's ratio of worst first step to a 2^20 step is 1.68; so the 2^20 + 2^20 first step is **≈ 44 s (≈ 1.36×)**.
  P2r changed it by −0.1 s only (it touched the node, not the 8 segment proofs). On the 9V45 ≈ 25 s (≈ 2.4×).
- RUN2 projected ≈ 46 s (≈ 1.3×) on its 9V74. This remains the hardest-failing cap; a host slower than RUN2's 9V74
  eats into it directly.

### 3.3 `build_s` (certificate; breach = REJECT)

- 461.8 s and 492.6 s on a 9V45; ≈ 705–752 s scaled to a 7763 (≈ 1.70–1.60×), against RUN2's 968.2 s (1.24×) measured
  on a 7763. **G6 is confirmed in direction and roughly in size (−22 to −27 % scaled vs. projected −28 %)**, but the
  7763 figure is a scaling, not a measurement: neither certificate job landed on a 7763.

### 3.4 Not a threat

`setup_s` (≥ 4.57×), `ready_s` (≥ 13.9×), `verify_s` (≥ 14.6×), DoS per item (≥ 3.26×) and column (≥ 25×), memory
(≥ 1.5×), `kernel_s` (≥ 1.95× on a 9V45; 1.59× on RUN2's 7763), gate and badge (≥ 4.29×), job timeouts (≥ 1.66×).

## 4. Runs

| run | branch | commit | certificate job | benchmark job | attest |
|---|---|---|---|---|---|
| 41042457623 | `probe/run3-eval` | `570a3a2` | EPYC 9V45, `ok` (build 461.8, comparator 287.9, gate 8.1, badge 40.1) | **Xeon Platinum 8370C**, **ACCEPT**, M = 96, `stream_s` 1,713.7 s, 9 reruns | OK (61734913) |
| 41042457436 | `probe/run3-eval-2` | `570a3a2` | EPYC 9V45, `ok` (build 492.6, comparator 307.9, gate 8.8, badge 42.0) | EPYC 9V45, **ACCEPT**, M = 96, `stream_s` 978.2 s, 5 reruns | OK (61730463) |

URLs: `https://github.com/scaraven/recursion.fast-submissions/actions/runs/<id>`.

## 5. What this run does not measure

- A 7763 certificate build (G6's `build_s` on the reference CPU is scaled, §3.3).
- A 9V74 or 7763 benchmark (the slow-host `stream_s` with re-time is projected, §3.1).
- A 2^20 + 2^20 first step on any runner (§3.2).

## 6. Probe branches pushed and deleted

- **Pushed:** `probe/run3-eval` and `probe/run3-eval-2`, both at `570a3a2`, one commit on `96eb0f6` (see
  `logs/RUN3/commits.txt`).
- **Deleted from the remote:** `git push origin --delete probe/run3-eval probe/run3-eval-2`, both reported
  `[deleted]`. Afterwards `git ls-remote origin 'refs/heads/probe/*'` lists only `probe/fr-vtime-{1..5}` and
  `probe/phase0`.
- **Deleted locally:** both branches, with `git branch -D`. The worktree `/home/devops/Verified-zkEVM/rf-run3` was
  removed (it held no logs; all logs were written directly to `logs/RUN3/`).
- **Untouched:** the remote branches `probe/fr-vtime-{1..5}` and `probe/phase0`.
- **Not pushed to:** `v4/flock-submit`, `v4/rev44`, `v4/flock-recursive` and `main`.

## Orchestrator correction: re-timing cannot truncate the stream

This reading is from core `422f2f9`, `harness/rfh/bench.py`.
- **When truncation happens.** `rec["truncated"]` is set only in the step loop and the canary check (lines 398–421).
- **When re-timing runs.** `retime` runs after both, and only when the run is not already truncated.
- **What happens at the cap during re-timing.** A rerun stops: `one` returns `None` at the deadline, or `check` times out
  with no time left. The harness then records `stopped_by_cap`, keeps the first times, and does not set `truncated`.
  Its docstring says the same: "If `stream_s` is reached the first times stand."

So for truncation, what counts is the stream up to the end of the canaries; the reruns count only if they fit:
- **8370C:** about 1,714 − 351 + ≈ 40 (a RUN2-like tail) ≈ **1,400 s (≈ 1.37×)**.
- **The same host's heavy draw:** max of 20,000, 1,927 s with the reruns, which is about **1,620 s (≈ 1.19×)** without
  them.
- **A RUN2-like 9V74, heavy draw:** about 2,000 s with the reruns, which is ≈ 1,760 s (≈ 1.09×) without them.

The reruns raise `stream_s` but cannot breach it. They can also only lower a step's scored `P` (the faster run is kept).
**No cap is at risk of a REJECT or a truncation from re-timing. No change to the entry is needed.** The cap whose breach
rejects is still the worst first step, ≈ 44 s projected on the 8370C (≈ 1.36×).
