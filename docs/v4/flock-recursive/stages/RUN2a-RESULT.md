# RUN2a RESULT: the certificate-side caps of `v4/rev44` at `3d9ae68`, on GitHub runners

Track RUN2a, 2026-10-30. The entry is `submissions/flock-recursive` at **`3d9ae68`** (FEL: `certified` has no
hypothesis), with the core pinned at `422f2f9`. This stage measures the certificate side only. The prover is being
resynced (E1b), so the benchmark side REJECTs, as expected.

I ran 4 workflow runs on probe branches `probe/run2a-{eval,a,b,c}`. Each branch was one commit on `3d9ae68` that
touched only `.github/`. All four have been deleted, on the remote and locally (§4). Logs are in `logs/RUN2a/`:
`commits.txt`, `runs.txt`, `eval-push.yml`, `eval.conf`, `probe.conf`, `eval-41005838408/`, and `run-<id>/` for each
probe run, holding the job logs and the probe artifacts. Nothing was committed and no entry source was edited.

## 0. Verdict

1. **The certificate is now `ok`, no longer provisional.** The real evaluation (run 41005838408: the core's
   `evaluate.yml` at `422f2f9`, `season.toml`, SPLIT=true) ran its certificate job on an **AMD EPYC 7763**. The
   comparator accepted `certified`/`submission` against the rendered challenge, and the gate passed.
   - Certificate job log `logs/RUN2a/eval-41005838408/certificate-job.log`, line 386:
     `2026-10-30T05:39:32.5935357Z certificate: ok []`
   - Comparator tail, from `logs/RUN2a/eval-41005838408/certificate/cert.json`, `kernel_runs.lean`
     (`outcome: ok`, `exit: 0`, `seconds: 368.7`):
     `Running Lean default kernel on solution.` / `Lean default kernel accepts the solution` / `Your solution is okay!`
   - `cert.json`: `status "ok"`, `reasons []`, `provisional_reasons []`, `gate ["PASS"]`, `built_modules` 373
     (RUN1: 304). The attested `result.json` repeats `certificate.status: ok`.
   - The three `si-cert` runs (the harness's own `evaluate.py cert`, with the caps raised) all print
     `certificate: ok []` / `status = ok` / `kernel lean: ok`.
2. **The benchmark REJECTs at the stream, as expected.** This was not chased. `logs/RUN2a/eval-41005838408/benchmark-job.log`:
   `05:42:43 FAIL: stream outputs: stream step 1 rejected by acc` → `VERDICT: REJECT` (9V74, `prover_sha256 115b11e9…`,
   the committed prover at `3d9ae68`; E1b's resync is not in it).
3. **`build_s` is now the thin certificate cap: 983.6 s of 1,200 (1.22×) on the real evaluation's 7763.** RUN1's
   7763 range was 752–812 s; the 7763 values are now 910–984 s (+≈ 20 %), which matches FEL's +40 modules and
   ≈ +600 s of single-core elaboration spread over 4 jobs. A `build_s` breach is the entry's **REJECT** (season
   `[certificate]`: "a breach is the entry's REJECT, except the kernel's"). RUN1/H-cert3 saw 7763 hosts differ by up
   to 11 %. A slow 7763 would take ≈ 1,090 s (1.10×), still inside the cap, but any further growth of `certified`'s
   closure eats directly into this margin.
4. **`kernel_s` is comfortable on the harness's own measure: 368.7 s worst (1.63×).** The harness's comparator time
   on a 7763 is 330.4, 343.9 and 368.7 s. The cert2 proxy (challenge = solution, so a full-size challenge export) gives
   447.2 / 453.9 s on a 7763 (1.32×); without the second export it gives 412 / 419 s (1.43×). A kernel breach only
   leaves the certificate unchecked; it does not REJECT.
5. **Gate and badge are far from their caps:** gate 15.0 s worst (8.0×), badge 76.5 s worst (2.35×).

## 1. Caps against measurements

The certificate job runs on a 4-vCPU runner. The caps are season `[certificate]` at `422f2f9`.

### `build_s` (cap 1,200 s; breach = REJECT)

| run | job | CPU | measured | margin |
|---|---|---|---|---|
| 41005838408 | real eval, certificate (`cert.json` `build_s`) | **EPYC 7763** | **983.6 s** | **1.22×** |
| 41005838078 | si-cert (`evaluate.py cert`) | EPYC 7763 | 944.2 s | 1.27× |
| 41005838105 | si-cert | EPYC 7763 | 910.1 s | 1.32× |
| 41005838298 | si-cert | Xeon Platinum 8370C | 841.1 s | 1.43× |
| 41005838298 | cert2 (`lake build Solution`, probe tree) | EPYC 7763 | 947.2 s | 1.27× |
| 41005838105 | cert2 | EPYC 7763 | 960.6 s | 1.25× |
| 41005838078 | cert2 | EPYC 9V45 | 595.4 s | 2.02× |

- Built: 372 FR modules plus `Solution`. The sum of FR job times is 3,268 / 3,297 s on a 7763 (RUN1: 303 modules,
  2,703 s).
- The largest new build job is `FRVIRTplRepL` at 63 s on a 7763.
- Build cgroup peak (cert2): 3.65–4.07 GiB.
- RUN1 at `200b531` for comparison: 7763 752.4–812.0 s; Xeon 8573C 629.3 s.

### `kernel_s` (cap 600 s; breach = certificate unchecked, not REJECT)

| run | job | CPU | measured | margin |
|---|---|---|---|---|
| 41005838408 | real eval, comparator (`cert.json` `comparator_s`) | **EPYC 7763** | **368.7 s** | **1.63×** |
| 41005838078 | si-cert comparator | EPYC 7763 | 343.9 s | 1.74× |
| 41005838105 | si-cert comparator | EPYC 7763 | 330.4 s | 1.82× |
| 41005838298 | si-cert comparator | Xeon 8370C | 313.7 s | 1.91× |
| 41005838298 | cert2 `cert` set (challenge = solution) | EPYC 7763 | 453.9 s (419 s without export 1) | 1.32× (1.43×) |
| 41005838105 | cert2 `cert` set | EPYC 7763 | 447.2 s (412 s) | 1.34× (1.45×) |
| 41005838078 | cert2 `cert` set | EPYC 9V45 | 322.0 s (302 s) | 1.86× (1.99×) |

- The si-cert and real-eval rows are the harness's own comparator on the real rendered challenge: the number the cap
  is checked against.
- cert2 exports the solution twice, as a full-size challenge and as the solution. It is a conservative proxy, and
  RUN1's 396.8 s was this proxy.
- **Pure kernel replay** (KReplay, `certified` + `submission`, 57,322 declarations): 245.8 / 234.0 s on a 7763 and
  170.2 s on a 9V45. RUN1 measured 207.9 s on a 7763 with 53,559 declarations.
  - Top modules on the 7763: `BF64.Basic` 16.6 s, `FRSkip` 11.1 s, `FRSoundness4TailC` 9.6 s, `FRSoundness4TailD`
    6.7 s.
- **Memory.** Comparator peak: harness 4.55–4.70 GB (`peak_bytes`); cert2 4.81–4.82 GiB. The scope cap is 14G (3×).
- **Upper set** (cert2 `upper`: every non-control FR theorem and definition in Solution's closure, 68,625
  declarations):
  - EPYC 7763: 590.6 / 561.8 s (**1.02× / 1.07×**); 546 / 520 s without export 1;
  - EPYC 9V45: 447.1 s.

  Since FEL this set is no longer what the harness checks: `certified` is closed, and the harness replays only its
  closure. The upper set is now only a bound for "everything in `Solution`'s FR closure". It does show that pulling
  much more of the FR closure onto `certified`'s path would reach the kernel cap on a 7763.

### `gate_s` (cap 120 s)

| run | CPU | measured | margin |
|---|---|---|---|
| 41005838408 (real eval) | EPYC 7763 | **15.0 s**, `PASS` | **8.0×** |
| 41005838078 (si-cert) | EPYC 7763 | 14.4 s | 8.3× |
| 41005838105 (si-cert) | EPYC 7763 | 14.7 s | 8.2× |
| 41005838298 (si-cert) | Xeon 8370C | 13.9 s | 8.6× |

### `badge_s` (cap 180 s)

| run | CPU | measured | margin |
|---|---|---|---|
| 41005838408 (real eval) | EPYC 7763 | **76.5 s** | **2.35×** |
| 41005838078 (si-cert) | EPYC 7763 | 74.0 s | 2.43× |
| 41005838105 (si-cert) | EPYC 7763 | 73.1 s | 2.46× |
| 41005838298 (si-cert) | Xeon 8370C | 65.0 s | 2.77× |

- RUN1 measured 60.3–64.4 s on a 7763.
- Badge sha256 (real eval): `verify 0ce7a2de…`, `chaincheck e54e8b27…` (unchanged from RUN1).
- The full hashes are in `logs/RUN2a/eval-41005838408/certificate/badge.sha256`.

### The certificate job's own timeout

- The core's `evaluate.yml` gives the certificate job `timeout-minutes: 40` (2,400 s).
- The real eval's certificate job took 1,544 s wall (05:13:55 → 05:39:39). Its `evaluate.py cert` step took 1,464 s.
  The margin is 1.55×.
- The four caps sum to 2,100 s, so a cap is reached before the job timeout.

## 2. CPU models

Of 8 measuring jobs:
- 5 ran on an **AMD EPYC 7763**: the real eval's certificate job, si-cert ×2 and cert2 ×2;
- 1 on an EPYC 9V45 (cert2);
- 1 on an EPYC 9V74 (the real eval's benchmark job);
- 1 on a Xeon Platinum 8370C (si-cert).

The 8370C is a model RUN1 did not see. The real eval's certificate job landed on a 7763, the slowest model seen for
Lean work.

## 3. Runs

| run | branch | commit | workflow | jobs, CPU |
|---|---|---|---|---|
| 41005838408 | `probe/run2a-eval` | `d952126` | `eval-push`: the core's `evaluate.yml` at `422f2f9`; trigger widened to `probe/run2a-eval*`; `.github/eval.conf` ROOT=submissions/flock-recursive, SEASON=harness/season.toml, SPLIT=true; `probe.yml` removed on that branch | certificate: **7763**, `ok` (build 983.6, comparator 368.7, gate 15.0, badge 76.5); benchmark: 9V74, **REJECT** at stream step 1; attest OK |
| 41005838105 | `probe/run2a-a` | `8b0fffe` | probe: `si-cert`, `cert2` | si-cert 7763; cert2 7763 |
| 41005838078 | `probe/run2a-b` | `2c577ff` | same | si-cert 7763; cert2 9V45 |
| 41005838298 | `probe/run2a-c` | `20a82db` | same | si-cert Xeon 8370C; cert2 7763 |

- The probe scripts are `probe/si-cert/run.sh` and `probe/cert2/run.sh`, unchanged since `200b531`.
- URLs: `https://github.com/scaraven/recursion.fast-submissions/actions/runs/<id>`.

## 4. Probe branches pushed and deleted

- **Pushed:** `probe/run2a-eval`, `probe/run2a-a`, `probe/run2a-b`, `probe/run2a-c`. Each is one commit on
  `3d9ae68` (SHAs in `logs/RUN2a/commits.txt`).
- **Deleted from the remote:** `git push origin --delete …`, all four reported `[deleted]`. Afterwards
  `git ls-remote origin 'refs/heads/probe/run2a*'` returns nothing.
- **Deleted locally:** `git branch -D`, all four. The worktree `/home/devops/Verified-zkEVM/rf-run2a` was removed.
- **Untouched:** the older remote branches `probe/fr-vtime-{1..5}` and `probe/phase0` were not pushed by this stage.
- **Not pushed to:** `v4/rev44`, `v4/flock-recursive` and `main`.

## 5. What threatens a cap

- **`build_s` (1.22× on the real 7763; breach = REJECT).** This is the only certificate cap under 1.5×.
  - Every module added to `Solution`'s import closure costs build time on a 4-vCPU 7763.
  - FEL's 40 modules cost ≈ +170 s wall.
  - Headroom to the cap is ≈ 216 s on the measured worst 7763, and ≈ 110 s on an 11 %-slow 7763 host.
- **`kernel_s` on the harness's measure (1.63×)** is not a threat at `3d9ae68`. The cert2 upper set (1.02× on a
  7763) shows the ceiling, if most of the FR closure ever lands on `certified`'s path.
- **Not measured here:** the stream, setup and step caps (benchmark side), which wait on E1b's resynced prover. RUN1's
  open item, `stream_s` at 1.26× projected, still stands.
