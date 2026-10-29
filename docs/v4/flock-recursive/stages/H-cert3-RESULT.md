# H-cert3: the certificate job's build, kernel, gate and badge steps, re-timed at `1782ab4` — RESULT

**Verdict.** Every step still fits its cap at HEAD `1782ab4` (core `422f2f9`), but the kernel is now close. On
the slower of two 7763 hosts, the `certified` comparator is 461.7 s, a margin of **1.30×**. The upper set is at
**1.06×**. The build lost about 0.15× of its margin. The badge and the gate are comfortable.

| cap | measured on the EPYC 7763 (or scaled to it) | margin |
|---|---|---|
| `build_s` 1,200 | harness build: **804.3 s** direct on a 7763; up to **825 s** scaled (9V45 runs); direct `lake build Solution` on two 7763 hosts: 756.5 / 797.0 s | **1.49×** (scaled worst 1.45×) |
| `kernel_s` 600 | comparator on `certified` + `submission`: **413.8 / 461.7 s** on two 7763 hosts (**386 / 432 s** without the challenge's full-size export) | **1.45× / 1.30×** (1.55× / 1.39×) |
| | upper bound (every non-control FR declaration in Solution's closure): 531.8 / 566.5 s (499 / 533 s) | **1.13× / 1.06×** (1.20× / 1.13×) |
| `gate_s` 120 | 13.5 s direct; ≤ 15.6 s scaled | ≥ 7.7× |
| `badge_s` 180 | 61.3 s direct; ≤ 62.7 s scaled | ≥ 2.87× |

In H-cert2, at `ea3e130`, these were: build ≈ 736 s, cert 265.2 s, upper 441.4 s, gate ≤ 12.6 s, badge ≤ 57.5 s.

Memory:
- **Comparator.** The peak is now **8.7 GiB** (`certified`) and 8.9 GiB (upper), against the 14G scope. In
  H-cert2 it was 4.3 and 4.7 GiB.
- **Build.** The cgroup peak is 8.5–8.9 GiB, against the probe's 12G scope.
- **Statement check.** In si-cert the harness's own kernel run peaked at 2.2–2.3 GiB. That run stops at the
  statement check.

Logs are in `logs/H-cert3/run-<id>/probe-{si-cert,cert2}/`. The factors are in `logs/H-cert3/factors.txt`. They
were made with `logs/H-cert3/factor.py` (a copy of H-cert2's) against G3's 7763 build log, using the changed-module
list `changed-2bf06e2-1782ab4.txt`.

## 1. Runs

I ran three workflow runs of `probe.yml` at `1782ab4` + `.github/probe.conf` (`si-cert`, `cert2`). Each run
is one commit on top of `1782ab4` and touches only the probe file. The branches `probe/h-cert3{,-b,-c}` have been
deleted. `probe/cert2/gen.sh` and `run.sh` needed no change. They copy every entry module, and they target
`RecursionFast.Challenge.certified` and `submission` by name. `certified` is now the `Open4F` form.

| run | job | CPU | factor vs G3's 7763 |
|---|---|---|---|
| 40884567814 | si-cert | **EPYC 7763** | 1.004 |
| 40884567814 | cert2 | **EPYC 7763** | 0.962 |
| 40884559372 | si-cert | EPYC 9V45 | 0.654 |
| 40884559372 | cert2 | **EPYC 7763** | 0.996 |
| 40884563974 | si-cert | EPYC 9V45 | 0.656 |
| 40884563974 | cert2 | EPYC 9V74 | 0.733 |

The factor uses H-cert2's method: Lake job times of the 211 entry modules that are unchanged since `2bf06e2` and
that both builds ran. All six builds agree at **2,655–2,696 CPU-s at G3-7763 speed**, against 2,485–2,508 in
H-cert2 (+7 %).

## 2. Build, gate, badge (`probe/si-cert`: the harness's `evaluate.py cert`, caps raised)

| run | CPU | `build_s` | / factor | `comparator_s` | `gate_s` (/f) | `badge_s` (/f) | built modules |
|---|---|---|---|---|---|---|---|
| 40884567814 | 7763 | **804.3** | 801 | 59.8 | **13.5** (13.4) | **61.3** (61.1) | 291 |
| 40884559372 | 9V45 | 539.7 | 825 | 41.8 | 10.2 (15.6) | 41.0 (62.7) | 291 |
| 40884563974 | 9V45 | 538.4 | 821 | 41.4 | 8.4 (12.8) | 37.7 (57.5) | 291 |

- **Status.** Every run returned `provisional` with no reject reasons. The provisional reason is "comparator
  (Lean kernel): exit 1": the statement check rejects `certified (h : Open4F)`. The gate printed `PASS`.
- **Module counts.**
  - **Build:** 291 modules (271 in H-cert2, so +20). That is 290 FR modules plus `Solution`.
  - **Badge compile set:** 299 `:c.o` objects, 289 of them FR (279 / 269 in H-cert2, so +20). The objects
    come from `badge.log`.
  - **Gap with the brief.** The brief expected about +35 badge modules and +17 for Solution. The measured net
    growth is +20 for both sets. This is consistent if some modules were dropped as others were added.
- **Build at 7763 speed:** 801–825 s, margin **1.45–1.49×**. It was ≈ 736 s (1.63×). The heaviest new module is
  `FRXOut4R` at 69 s of job time on a 9V74, the largest single module in the build. `FRXNd4` is 19 s.
- **Gate and badge** are measured directly on the 7763. The 9V45 runs scaled by the build factor agree within a few
  seconds.

## 3. Kernel (`probe/cert2`: challenge = solution = `Solution`)

| run | CPU | cert (w/o export 1) | margin | upper (w/o export 1) | margin | KReplay cert / upper | peak cert / upper |
|---|---|---|---|---|---|---|---|
| 40884567814 | **7763** | **413.8 (386)** | **1.45× (1.55×)** | **531.8 (499)** | **1.13× (1.20×)** | 240.8 / 311.7 | 8.72 / 8.86 GiB |
| 40884559372 | **7763** | **461.7 (432)** | **1.30× (1.39×)** | **566.5 (533)** | **1.06× (1.13×)** | 260.6 / 336.7 | 8.74 / 8.87 GiB |
| 40884563974 | 9V74 | 401.0 (377) | 1.50× | 514.1 (487) | 1.17× | 217.3 / 272.5 | 8.70 / 8.87 GiB |

- Every comparator run ended with "Lean default kernel accepts the solution; Your solution is okay!"
- **Sizes.** The `cert` set replays 51,854 declarations (44,353 before). The `upper` set replays 61,455 (59,999
  before), and it covers 289 FR modules with 11,623 theorems and 6,628 definitions.
- **The two 7763 hosts differ by 11 %** on the comparator (413.8 vs 461.7 s), while their build factors differ by
  only 3.5 %. The kernel does not scale like the build: the 9V74, at a 0.733 build factor, is only 3 % faster than
  the 7763 here.
- **Where the time goes, cert set, 7763, run 40884567814:**
  - The two exports take 28 s each and peak at 3.35 GiB.
  - After the last export, 328 s remain. KReplay accounts for 241 s of it, and parsing, comparing and the axiom
    check take the other ≈ 87 s. That overhead was ≈ 60 s in H-cert2.
  - The comparator's resident memory doubled to 8.6 GiB.

### Within 1.3×: what dominates the kernel

The `certified` comparator reaches 1.30× on the slower 7763 (1.39× without export 1). The upper set is at
1.06–1.13×. KReplay, cert set, 7763 (run 40884567814):

| module | kernel s | main declaration |
|---|---|---|
| `FRXOut4R` | **45.9** | `FR.X.realign_sem` **44.8 s**: one theorem, new in S-H4 pass 10 (`7a0afa8`), after H-cert2 |
| `CompPoly.Fields.Binary.BF64.Basic` | 15.4 | `BF64.basePoly_irreducible` 15.3 s (core-owned, unchanged) |
| `FRXNd4` | 12.1 (upper 18.5) | `decOk4_nd` 6.5 s, `sizeIR_decF04._proof_1_1` 5.6 s; in upper also `nd_ne_ndNone` 5.9 s |
| `FRSkip` | 9.1 | `pinnedW_eq` 5.5 s, `pinned_cert` 3.2 s (as before) |
| `FRXMsg`, `FRSoundness4Pos`, `FRSoundness4TailD`, `FRNodeRows4Ext` | 4.5–5.2 each | as in H-cert2 |

- **The kernel growth since H-cert2 is almost all S-H4's tail.** KReplay grew from 135.2 to 240.8 s
  (+105.6 s). Of that, `FRXOut4R` is 45.9 s and `FRXNd4` 12.1 s. The rest is spread over about 20 new `FRX*`
  modules: `FRXMsg`, `FRXBfly`, `FRXOut4O`, `FRXLagT`, `FRXField`, `FRXDec4Levels`, `FRXFwd` and others, each
  2–5 s.
- **On the brief's number.** The brief puts `sizeIR_decF04` at 35.6 s. In the kernel replay it costs 5.6 s. The
  35.6 s is presumably elaboration time; I did not measure that here.
- **`realign_sem` alone** is about 11 % of the slower 7763's comparator wall time. Making its proof cheaper in the
  kernel, or splitting it, is the single largest lever. The ≈ 87–112 s of non-replay comparator time, and the
  doubled RSS, plausibly come from this same proof term's size. I have not verified that.
- **For the upper set,** `FRXChain4` (7.7 s) and `FRXChainFlock` (6.9 s) add to the list, and at 1.06× it has
  essentially no slack.

## 4. Caveats

- **`Open4F := Gaps4` is still a hypothesis.** Its eventual proof is not in the `cert` closure. The `upper` set
  bounds that growth only for declarations already in Solution's import closure, and it is at 1.06–1.13× today.
- **Variance between hosts.** Among 7763 hosts the kernel varies by about 11 %. A slower host than either seen here
  would eat into the 1.30×.
- **Sandbox.** cert2 runs outside the sandbox, with a pass-through landrun, and builds `lake build Solution`.
  si-cert is the harness itself, with the sandbox.
- The comparator's 8.7 GiB peak is within the harness's 14G kernel scope (`kernel_runs.lean.cap` in `cert.json`).

## 5. Files

| file | what |
|---|---|
| `logs/H-cert3/run-<id>/probe-si-cert/out/` | `cert.json`, build, gate, badge and comparator logs, `machine.txt` |
| `logs/H-cert3/run-<id>/probe-cert2/out/` | `summary.txt`, comparator logs and phase samples, `kreplay-{cert,upper}.tsv`, build log |
| `logs/H-cert3/factors.txt`, `factor.py`, `changed-2bf06e2-1782ab4.txt` | the machine factors |
