# F3: `spartan-srom` through the real v4 harness — RESULT, 2026-10-23

Status: **done; not committed** (the orchestrator commits). The entry is the frozen commit
`8111b71` (`submissions/spartan-srom`, extracted with `git archive`). The harness is the merged core
**`a874f87`**: branch `v4/srom-rules`, stage A with its golf `a5e4cff`, and stage B `e572344`
merged. Stage B's `harness/`, `service/`, `scripts/` and `tests/` are identical at both commits.
This follows the orchestrator's note, in place of `e572344` alone.

Logs are under the worktree's `logs/f3/` (gitignored; written `G/` below). The machine is the shared
32-vCPU QEMU VM (AVX2, AVX-512F, no `pclmulqdq`), with load from other agents during every run.
Every harness command ran under `taskset -c 0-15` and a `timeout`. So the checks are pinned to core
15, the highest core of that affinity (`rfh/checks.py`). Durations below are single runs on this VM.

## 0. Verdicts

| # | Run | Input | Verdict | Where it stopped | Log |
|---|---|---|---|---|---|
| 1a | `evaluate.py cert` | frozen entry, default org roots | **REJECT** | step 4, the rebuild binding: "the gate tree's build differs from the comparator-verified build (22 artifacts …)". **Harness bug**, §2.1 | `G/cert-lean.{log,json}` |
| 1b | `cert` | variant **V** (§2.1: `Solution.lean` imports the 11 modules outside its closure), default roots | **REJECT** | gate rule 3: `module CompPoly.Fields.Extension.Arithmetic: registers @[csimp] lemmas`. **Setup**: CompPoly is not among the organiser's roots, §2.2 | `G/cert-closure-default.{log,json}` |
| 1c | `cert` | V, roots + CompPoly (`RF_ORG_ROOTS`) | **ok** (Lean kernel), 14 min 22 s | — | `G/cert-closure.{log,json}` |
| 1d | `cert --nanoda` | V, roots + CompPoly | **provisional**: "comparator: exit -15, the certificate does not check" | nanoda OOM-killed in the 14 GiB comparator cgroup at 13.65 GB RSS, 375 s after it started; the Lean kernel never ran. §2.4 | `G/cert-nanoda.{log,json,curve}` |
| 1e | nanoda alone, same export | 20 GB cap, 1 h | **not finished**: OOM-killed at the 20 GB cap after 10 min 1 s, still growing about 2.1 GB per minute | §2.4 | `G/nanoda-standalone/` |
| 1f | `cert` | frozen entry, roots + CompPoly | **REJECT**: the same rebuild-binding message as 1a | step 4, before the gate; the roots do not matter here. §2.1 | `G/cert-frozen-comppoly.{log,json}` |
| 2 | `evaluate.py bench`, `smoke.toml` | V's certificate (1c) | **ACCEPT** | — | `G/bench-smoke.{log,json}` |
| 3a | `bench`, `season.toml` unchanged | | **REJECT** "tree1: prover tree exit 3", 46 s after start | the service refused a 1,572,898-byte query (`CAP`, `queryCap` = 2^20) 27.6 s into the first leaf (`n = 2^18`), at 6.5 GB RSS. Not memory, not `proofCap`. §4.1 | `G/bench-season.{log,json}`, `G/diag/tree-r6-n2p18.log` |
| 3b | `bench --parts stream`, the season's stream (`M = 512`, `n_f = 2^16`) | | **REJECT** "stream1 leaf0: proof.bin: missing; stderr: ", 33 s after start | the 11 GiB prover cgroup OOM-killed leaf 0 after 25 s (RSS 11.14 GB). §4.2 | `G/bench-season-stream.{log,json}` |
| 3c | the frontier | | the largest passing trees: `r = 0, n = 4096`; `r = 1, n = 1024`; `r = 2, n = 128`; `r = 3, n = 4`; no `r = 4`. The stream: 5 links at `n_f = 16`, 1 at `1024` | every failure is the root (or link) above `proofCap`, reported as "rejected by acc". §4.3 | `G/fr-*.{log,json}` |
| 3d | `[tv] enforce = true` | `r = 2, n = 16`; `r = 1, n = 1024` | **REJECT** | the root's `acc` takes 946 ms against a cap of 0.015 ms, and 1,776 ms against 0.194 ms. That is 4–5 orders of magnitude over. §4.4 | `G/fr-tv-*.{log,json}` |

The entry reaches ACCEPT through the real harness, with the real Lean badge, only at shapes with
`2^r · n ≤ 4096`. Three things beyond the frozen entry were needed to get there:

- a fix of the harness's rebuild check, or the entry's `Solution.lean` importing every module;
- CompPoly among the organiser's roots;
- `T_V` not enforced.

## 1. Setup

```sh
S=/home/devops/Verified-zkEVM/recursion.fast-submissions-v4; G=$S/logs/f3
git -C $S archive 8111b71 submissions/spartan-srom | tar -x -C $G/          # G/submissions/spartan-srom
git clone -q --no-hardlinks /home/devops/Verified-zkEVM/recursion.fast-v4 $G/org
git -C $G/org checkout -q a874f87                                          # the organiser checkout (ORG)
cp -a /home/devops/Verified-zkEVM/recursion.fast-v4/.lake/pkgs-local $G/pkgs   # private package tree, 9.2 GB
mkdir -p $G/org/.lake && ln -s $G/pkgs $G/org/.lake/packages
taskset -c 0-15 timeout 10800 bash $G/org/harness/org-setup.sh $G/org     # default roots (runs 1a, 1b)
RF_ORG_ROOTS=Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls,\
CompPoly.Fields.Binary.BF64.Ext3,CompPoly.Fields.Binary.BF64.Bytes \
  taskset -c 0-15 timeout 3600 bash $G/org/harness/org-setup.sh $G/org    # roots + CompPoly (1c onwards)
source $G/org/scripts/tools.env    # COMPARATOR_HOME (comparator d03acab), COMPARATOR_NANODA (nanoda 3a24072)
taskset -c 0-15 timeout 7200 python3 -I $G/org/harness/evaluate.py cert --entry ENTRY --org $G/org \
  --work $G/cert-X --out $G/cert-X.json [--nanoda]
taskset -c 0-15 timeout 7200 python3 -I $G/org/harness/evaluate.py bench --entry ENTRY \
  --cert $G/cert-closure.json --work $G/bench-X --out $G/bench-X.json --season SEASON [--parts …]
```

- The service is built by `org-setup` (`G/org/service/target/release/rf-oracle`, SHA-256 `d6003237…`,
  the same as F2's copy). Nothing was reused from `logs/f2/`.
- Each run was wrapped in a monitor (`/usr/bin/time -v` and a 0.25 s poller of every descendant's
  `VmHWM` and every `rf-*` scope's `memory.peak`). Its output is `G/*.rsmon.json`.
- Nothing was written to the shared package tree, to `recursion.fast-v4/.lake/pkgs-local`, to the
  comparator checkout or to the harness worktree (checked with `find -newermt`).

| Setup step | Wall | Notes (log) |
|---|---|---|
| copy of the package tree (ext4, no reflink) | 4 min 0 s | 9.2 GB |
| `org-setup.sh`, default roots | **5 min 56 s** | build 152 s, tools 11 s, allowlist and manifest 149 s (10,787 modules, 34,290 files), compiled objects 35 s, service 9 s. Peak RSS 6.0 GB (`G/org-setup.log`, `G/org-setup-default-logs/`) |
| `org-setup.sh`, roots + CompPoly | 1 min 4 s | +28 CompPoly modules: allowlist 10,815, manifest 34,374 (`G/org-setup-comppoly.log`) |

## 2. The certificate job

### 2.1 The frozen entry fails the rebuild binding (harness bug)

Run 1a stopped at step 4. All earlier steps passed:

- the source rule: 65 files, 0 findings;
- the manifest check;
- the comparator: "Lean default kernel accepts the solution / Your solution is okay!", in 372 s.

Step 4 then reported:

```
certificate: reject ["the gate tree's build differs from the comparator-verified build
  (22 artifacts, e.g. ['ir/SpartanSrom.c', 'ir/SpartanSromControls.c', 'ir/SpartanSromKat.c'])"]
```

**Nothing differs.** Recomputing `artifacts()` over both trees (`G/cert-lean/{cmp,tree}`) gives:

- 110 artifacts in the comparator tree, **all 110 byte-identical** in the gate tree;
- 22 artifacts present only in the gate tree. These are the `.olean` and `.c` of the 11 modules
  outside `Solution`'s import closure: `SpartanSrom`, `SpartanSromRun`, `SpartanSromKat`,
  `SpartanSromControls`, `SpartanSromLigeroControls`, `SpartanSromMLEControls`,
  `SpartanSromNodeControls`, `SpartanSromRSControls`, `SpartanSromSoundnessLogControls`,
  `SpartanSromSoundnessPCSControls`, `SpartanSromTranscriptControls`.

The cause is that the two trees build different things:

- the comparator builds the target `Solution`, which is its closure only;
- the gate tree builds `RFSubmission`, which is every `lean/*.lean`;
- `evaluate.py` compares with `diff = [k for k in arts if cmp_arts.get(k) != arts[k]]`, so an
  artifact missing from the comparator tree counts as a difference.

Any entry that ships its controls as modules `Solution` does not import is rejected this way. The
rules require controls, so every entry must ship them.

**Fixes**:

- on the harness side, build only `Solution` (and `Challenge`) in the gate tree, or compare only the
  keys the comparator built;
- on the entry side, `Solution.lean` imports every module.

The orchestrator chose the entry-side form for the measurement. Variant **V**
(`G/entry-closure/`, diff `G/entry-closure.diff`) is the frozen entry plus these lines in
`lean/Solution.lean`, after `import SpartanSromFinal`:

```
import SpartanSrom
import SpartanSromRun
import SpartanSromKat
import SpartanSromControls
import SpartanSromLigeroControls
import SpartanSromMLEControls
import SpartanSromNodeControls
import SpartanSromRSControls
import SpartanSromSoundnessLogControls
import SpartanSromSoundnessPCSControls
import SpartanSromTranscriptControls
```

None of the 11 modules defines `main` or anything else that clashes with the badge, so none had to
be dropped. With V, the comparator and the gate tree build the same 66 modules (65 plus the
challenge), and the binding passes (run 1c). The controls are then also in the environment the
gate loads and in the badge's link: 4,590 badge build jobs.

Run 1f repeats 1a after the CompPoly roots were added (§2.2). The result is the same: the
comparator accepts, then step 4 rejects with the same 22 artifacts, 9 min 33 s after the start. The
binding check runs before the gate, so the roots cannot change it.

### 2.2 CompPoly is not an organiser root (setup)

Run 1b gets past the binding with V, then fails the gate:

```
gate: badge-root-module Solution
gate: rule 4: RecursionFast.Challenge.submission: compiled code
gate: 3828 modules, 3723 trusted and 0 pinned by hash
gate: RecursionFast.Challenge.certified: closure of 33244 constants, axioms [propext, Classical.choice, Quot.sound]
gate: REJECT module CompPoly.Fields.Extension.Arithmetic: registers @[csimp] lemmas
certificate: reject ['gate: gate: REJECT module CompPoly.Fields.Extension.Arithmetic: registers @[csimp] lemmas']
```

How the gate reaches this:

1. The entry imports `CompPoly.Fields.Binary.BF64.{Ext3,Bytes}`, as v3 did.
2. `org-setup.sh`'s default roots are `Mathlib`, `RecursionFast.{Contract,Library,Controls}`, so
   the olean manifest does not cover CompPoly.
3. The gate therefore classes CompPoly's 28 modules as **untrusted**, like entry code, rather than
   as pinned.
4. One `@[csimp]` lemma of CompPoly rejects the entry under rule 3.

Rule 6 (imports outside the allowlist) does not fire, because the importing module is untrusted
too. With `RF_ORG_ROOTS` extended by the two CompPoly roots (§1), the gate says `28 pinned by hash`,
notes the `csimp` lemma as a pinned dependency's, and passes (run 1c). The orchestrator reports
that the core will add these roots to the defaults.

### 2.3 The successful certificate job (run 1c): steps, wall time, peak memory

`G/cert-closure.rsmon.json` (times from the job's start); `/usr/bin/time -v` gives a wall time of
14 min 21.6 s.

- **RSS** is a process's `VmHWM`. It includes mapped `.olean` files, which are page cache shared
  with other processes.
- **Scope peak** is the step's cgroup `memory.peak`, which includes the page cache it wrote.

| Step | From–to (s) | Wall | Peak RSS (largest process) | Scope peak |
|---|---|---|---|---|
| render, source rule | 0.3–1.7 | 1.4 s | 16 MB | — |
| manifest check (4 times in the job) | e.g. 1.7–7.9 | about 6 s each | 61 MB | — |
| **comparator** (`comparator_s` = 513.1 s) | 8.2–521.0 | **8 min 33 s** | | **4.37 GB** (cap 14 GiB) |
| · `lake env` start-up in the fresh tree (Lake's `git diff` of every package) | 8.2–37.6 | 29 s | 0.96 GB (`lake`) | |
| · build `Challenge` (sandbox) | 37.9–54.4 | 16.5 s | 1.79 GB (`lean`) | |
| · `lean4export` `Challenge` | 54.7–64.7 | about 10 s | | |
| · build `Solution` (sandbox; the 65 entry modules) | 64.7–302.4 | 3 min 58 s | **4.11 GB** (`lean`) | |
| · `lean4export` `Solution` (226 MB export) | 302.4–328.8 | about 26 s | 2.85 GB | |
| · parse, compare, **Lean kernel** replay | 328.8–521.0 | **about 192 s** | **3.62 GB** (comparator process) | |
| gate-tree rebuild (sandbox) and byte comparison | 532.0–751 | 3 min 30 s | 4.11 GB (`lean`) | 3.06 GB (cap 12 GiB) |
| **gate** (sandbox) | 753.4–775.2 | 21.8 s | 2.47 GB (mostly mapped `.olean`) | 0.40 GB |
| **badge build** (sandbox; compiles the objects of 986 package modules outside the organiser's prebuilt closure (952 Mathlib, 28 CompPoly, 6 Batteries), the entry's and the badge's; 2 links) | 775.4–849.1 | **73.7 s** | 0.99 GB (`ld.lld`) | 2.18 GB |
| total | | **14 min 22 s** | 4.11 GB | |

The comparator's own output is block-buffered: `comparator.log` gets the kernel lines only when the
comparator exits. So the kernel's span above comes from process lifetimes: from the end of the last
`lean4export` to the comparator's exit.

The other runs show the spread:

| Run | Lean-kernel phase | Comparator | Gate-tree build | Total |
|---|---|---|---|---|
| 1a (frozen; no controls in the closure) | 152 s | 372 s | 186 s | 9 min 41 s |
| 1b (V, default roots) | 156 s | 458 s | 182 s | 11 min 25 s |
| 1d (with nanoda) | not reached | 630 s, killed | 179 s | 14 min 54 s |

In run 1d the badge build was 20.5 s, because CompPoly's objects were already in the package tree.
The badge executables are 142.7 MB each (`verify`, `liveness`). The job's work directory is 926 MB:
two trees of 183 MB and 466 MB, plus the badge.

### 2.4 The second kernel (C-M2)

**Through the harness (run 1d, `cert --nanoda`, default `--cert-mem 14G`).** The comparator runs
the external kernels first (`verifyMatch`: nanoda, then the Lean kernel), with
`num_threads: 4`. What happened:

- `nanoda_bin` started at 267 s and grew roughly linearly (`G/cert-nanoda.curve`, sampled every
  5 s): 4.3 GB at 1 min, 7.3 GB at 3 min, 10.6 GB at 5 min, 13.5 GB at 6 min.
- At 375 s it reached 13.65 GB RSS. The rf-cmp scope hit its cap: `memory.peak` 15,032,385,536
  bytes, which is 14 GiB.
- The journal says "The kernel OOM killer killed some processes in this unit … Failed with result
  'oom-kill' … 14G memory peak".
- systemd stopped the whole scope, so the comparator itself died with SIGTERM (exit -15). Its
  buffered output was lost, and the Lean kernel never ran in this job.
- The harness carried on: the gate passed, the badge was built, and it reported:

```
certificate: provisional ['comparator: exit -15, the certificate does not check']
```

A memory kill of the second kernel thus turns a certified entry into PROVISIONAL, with a reason that
blames the certificate. Wall time 14 min 54 s (`G/cert-nanoda.log`).

**Standalone (run 1e).** To measure nanoda's own need, the same `Solution` export was used:

- the export was made with `lake env lean4export Solution -- <the comparator's 35 targets>` in the
  comparator tree: 226,316,509 bytes, 26 s;
- the nanoda configuration was the comparator's;
- the run was under a 20 GB scope (`MemoryMax=20G`, no swap) and a 1 h timeout.

**Not finished: OOM-killed at the 20 GB cap after 10 min 1 s**, still growing
(`G/nanoda-standalone/{nanoda.log,curve.log}`).

- The journal says "rf-f3-nanoda.scope: The kernel OOM killer killed some processes … Consumed
  11min 52.340s CPU time over 10min 3.189s wall clock time, 20G memory peak".
- RSS by time: 2.9 GB at 67 s, 5.4 GB at 128 s, 8.6 GB at 189 s, 12.4 GB at 311 s, 15.6 GB at
  372 s, 17.5 GB at 495 s, 19.7 GB at 556 s, and 20.93 GB at 597 s, the last sample.
- That is about 2.1 GB per minute, with no sign of levelling off.
- nanoda prints nothing while it runs, so how far it got is unknown.
- Its CPU use was about 1.2 cores, although the configuration gives it 4 threads.

**Answer to C-M2 on a real entry:** nanoda needs more than 20 GB and more than 10 min on
`spartan-srom` (a 226 MB export). The harness's 14 GiB cap is reached after 6 min 15 s.

For comparison:

- stage B: nanoda on the witness-sending entry, at least 17.6 GB after 10 min 51 s, not finished;
- v3: 52 GB on one lemma.

On this entry, nanoda does not fit the harness's 14 GiB cap, nor a 16 GB GitHub runner.

## 3. The benchmark at the smoke shape: ACCEPT (run 2)

`evaluate.py bench --season harness/smoke.toml` with V's certificate (1c) and every part. Total 54 s
(`G/bench-smoke.{log,json}`, per-check times re-run with the harness's `Badge` class in
`G/bench-smoke-reverify.log`).

**Build and machine.**

- prover: `gcc -static -O2 -pthread prover.s` in the sandbox. Binary SHA-256 `30b46975…`, 2,698,536
  bytes: the same as F2's.
- `setup`: 0.075 s.
- `memcap`: systemd.
- CPU: QEMU Virtual CPU version 2.5+ (avx2, avx512f).

**Score** (`S = T_tree + 20 · t_link`):

| | Value |
|---|---|
| `T_tree` (`r = 2, n = 16`) | **0.896 s** |
| `t_leaf` | **0.2512 s** (5 leaf requests: 0.180, 0.226, 0.185, 0.204, 0.209; mean 0.201, see friction 11) |
| `t_merge` | **0.0373 s** (merges 0.019, 0.031, 0.047, 0.052) |
| `t_link` | **0.2885 s** |
| `S` | **6.666** (`o_est` 0.065) |

**Checks.**

- Tree: the root and 6 samples were accepted, and **69 canaries** were rejected.
- Stream: 5 leaves and 4 nodes were accepted, and **18 canaries** were rejected.
- Liveness tree: the root and 2 samples were accepted, and 29 canaries were rejected.
- **DoS column**: 64 inputs, all rejected. `max_ns` = **443 ms**, median 19.3 ms; the slowest are
  bit-flipped `π` files that keep the root's trace and signature, re-run at 466–470 ms.
- **Liveness**: "ok extracted and checked 3 witnesses from a log of 30820 entries". The `liveness`
  badge took **24.1 s** and 121 MB RSS for a 2.1 MB query log (`r = 1, n = 16`).

**`T_V` columns** (reported, not enforced at this shape): `T_triv_best_ns` = **103,479**
(runs 103,479 and 131,703; 64 compressions), cap **10.3 µs**, 19 capped checks, all 19 over the
cap, `max_ns` 1,592 ms. Every `acc` time, from the re-run on core 15:

| Output | File bytes | `acc` (parse + `accF`) |
|---|---|---|
| tree root (bundle of 4) | 2,169,384 | 931 ms (979 ms in the run) |
| tree `N1_0`, `N1_1` (bundles of 2) | 1,082,260 | 481, 456 ms |
| tree `L0`…`L3` | 538,698 | 203–229 ms |
| stream leaves 0–4 | 538,698 | 201–276 ms |
| stream nodes 1–4 (bundles of 2–5) | 1,082,260 … 2,712,946 | 455, 800, 921, 1,311 ms |
| liveness root (bundle of 2), leaves | 1,082,260 / 538,698 | 481 / 230–234 ms |
| canaries | — | 0.9–197 ms |

**Service calibration**:

| | Value |
|---|---|
| keygen | 337.8 ms (AVX2) |
| 1 thread | 4.62 M calls/s, 222 µs per 1,024-query request |
| 32 threads (`threads_32`, under a 16-core affinity) | 84.3 M calls/s |
| traffic of the tree run | 777 requests, 75,772 queries, 5.2 MB, 8 signatures |
| traffic of the stream run | 979 requests, 108,847 queries, 10 signatures |

## 4. Where the rules stop it

All runs are benchmark-only, with run 1c's certificate. The season files in `G/seasons/` differ from
`smoke.toml` or `season.toml` only in the named shape keys (and `[tv] enforce` for §4.4).

### 4.1 The season shape, unchanged (run 3a)

```
10:49:04 recursion.fast v4 benchmark, season season-1, parts ['calibrate', 'tree', 'dos', 'stream', 'liveness']
10:49:06 tree instance: 64 chains of 262144
10:49:19 T_triv,best = 2667.666 ms, T_V cap = 266.767 ms; service {…}     (service column: 4.68 M calls/s on 1 thread, 85.7 M on 32)
10:49:20 [tree1] prover tree: r=6 n=262144
10:49:47 [tree1] exit 3 in 27.637 s
10:49:47 FAIL: tree1: prover tree exit 3
VERDICT: REJECT
```

The run took 46 s from start to verdict. The calibration gives `T_triv,best` = 2.668 s, from the
runs 2.668, 2.791 and 2.767 s: about 159 ns per compression over 2^24. So the season's `T_V` would
be 266.8 ms.

The result JSON has no `tree` entry and no prover log (friction 4), so the cause was taken from the
same tree run reproduced with the harness's own `Run.tree` and `Service`
(`G/diag/tree-r6-n2p18.log`):

```
status exit 3 seconds 31.287
spartan-srom-prover: oracle service: QUERY (1 items, 1572902 bytes) refused with status 2 CAP: a query above 2^20 bytes
```

**The stopping rule is the service's per-query cap `2^20` bytes (V4-A3), not memory and not
`proofCap`.** The request body is a 4-byte length plus a 1,572,898-byte query, which is
`0x20 ‖ st ‖ kind ‖ msg` with a 1,572,864-byte message: 2^16 extension-field elements of 24 bytes.
By the order of the leaf prover (`prover.rs`: the column commitment, the seed, `absorb(0x01, root)`,
`m` squeezes, `absorb(0x02, ū)`), it is the absorb of the Ligero combined row `ū`.

At that point:

- the prover had sent 1,049,601 queries (4.33 GB) through the service, nearly all of them Merkle
  leaves and nodes;
- its RSS was 6.48 GB (cgroup 6.65 GB, under the 11 GiB cap).

At `n = 2^16` every query fits: F2 proved such leaves through the service. Had the query passed:

- memory: F2 measured 15.8 GB for a leaf at `2^16`, so the leaf would have hit the 11 GiB cgroup;
- `proofCap`: F2's leaf `π` is 2.79 MB already at `2^16`.

**Entry-side fix** (not applied): absorb long messages in pieces of at most 2^20 bytes (for example
a hash chain over chunks). This changes the transcript, so the Lean `V` and the proofs that depend
on it change too. Memory and `proofCap` would still stop the leaf.

### 4.2 The stream at the season's `n_f = 2^16` (run 3b)

Season file `G/seasons/season-stream.toml`: `season.toml` with the tree shrunk to `r = 0, n = 1`,
which is only the unused instance. Run with `--parts stream --stream-repeats 1`.

```
10:51:15 [stream1] computing 513 leaf digests at n_f = 65536
10:51:45 FAIL: stream1 leaf0: proof.bin: missing; stderr:
VERDICT: REJECT
```

The run took 33 s from start to verdict. The 513 digests took about 3 s (parallel). Leaf 0's
request ran 25.3 s.

- The prover reached **11.14 GB RSS**. Its scope's `memory.peak` was 11.81 GB, with the cap at
  11 GiB.
- The journal shows the OOM kill:

  ```
  10:51:43 rf-61a02d8d87a1440f.scope: The kernel OOM killer killed some processes in this unit.
  10:51:45 rf-61a02d8d87a1440f.scope: Failed with result 'oom-kill'.
  10:51:45 rf-61a02d8d87a1440f.scope: Consumed 5min 10.839s CPU time over 26.924s wall clock time, 11G memory peak.
  ```

**The stopping rule is the 11 GiB prover cgroup (V4-13), at link 0.** The harness's message does not
say so (friction 5). If memory allowed, `proofCap` would stop link 0: a leaf `π` at `2^16` is
2,791,559 bytes (F2).

### 4.3 The frontier

**Tree** (`--parts calibrate,tree,dos`, one repeat; smoke shape otherwise).

- Every rejection is "tree1 root and samples: tree1 root rejected by acc".
- `π` and the file sizes are those of the stored root.
- `T_tree` of a rejected run is the prover's time, read from `run.log`.

| `r` | `n` | `2^r · n` | verdict | root `π` (bytes) | root file | `T_tree` | root `acc` | `T_triv,best` | DoS `max_ns` |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 4,096 | 4,096 | **ACCEPT** | 796,111 | 1,931,542 | 4.046 s | 1,771 ms | 5.64 ms | 1,592 ms |
| 0 | 8,192 | 8,192 | REJECT | 1,062,591 | 2,474,360 | 8.320 s | — | 11.23 ms | — |
| 0 | 16,384 | 16,384 | REJECT | 1,464,107 | 3,296,699 | 12.687 s | — | 21.83 ms | — |
| 1 | 1,024 | 2,048 | **ACCEPT** | 925,342 | 2,465,890 | 2.249 s | 2,000 ms | 1.47 ms | 1,036 ms |
| 1 | 2,048 | 4,096 | REJECT | 1,192,062 | 3,009,702 | 3.758 s | — | 2.80 ms | — |
| 1 | 4,096 | 8,192 | REJECT | 1,601,878 | 3,867,948 | 7.879 s | — | 5.64 ms | — |
| 2 | 16 (smoke) | 64 | **ACCEPT** | 603,812 | 2,169,384 | 0.896 s | 979 ms | 0.10 ms | 443 ms |
| 2 | 64 | 256 | **ACCEPT** | 802,836 | 2,649,052 | 1.225 s | 1,426 ms | 0.24 ms | 760 ms |
| 2 | 128 | 512 | **ACCEPT** | 936,916 | 2,923,940 | 1.453 s | 1,390 ms | 0.31 ms | 1,008 ms |
| 2 | 256 | 1,024 | REJECT | 1,166,724 | 3,460,784 | 3.508 s | — | 0.43 ms | — |
| 3 | 1 | 8 | **ACCEPT** | 833,344 | 3,255,120 | 0.848 s | 1,326 ms | 0.17 ms | 1,347 ms |
| 3 | 4 | 32 | **ACCEPT** | 984,096 | 3,716,360 | 1.721 s | 2,940 ms | 0.15 ms | 784 ms |
| 3 | 8 | 64 | REJECT | 1,052,576 | 3,859,768 | 1.358 s | — | 0.16 ms | — |
| 3 | 16 | 128 | REJECT | 1,217,280 | 4,343,632 | 1.743 s | — | 0.16 ms | — |
| 4 | 1 | 16 | REJECT | 1,676,344 | 6,515,104 | 1.841 s | — | 0.26 ms | — |

**Every rejection is `|π| > proofCap = 1,048,576`**:

- at `r = 0`, the single leaf `π` passes the cap between `n = 4096` and `8192`;
- at `r ≥ 1`, the root is a bundle of all `2^r` leaves, so its `π` grows by about one leaf `π`
  (plus about 9.7 KB of witness) per leaf.

The largest accepted tree carries 4,096 chain steps, against the season's 2^24, a factor of 4,096
short. No `r ≥ 4` fits even at `n = 1`.

**Stream** (`--parts stream`). The message names the first link that is not accepted; `π` sizes
are those of the stored node files.

| `n_f` | `M` | links accepted | stopped at | message | last accepted node `π` | rejected node `π` |
|---|---|---|---|---|---|---|
| 16 | 8 | **5** (nodes 1–5) | link 6 | "stream1 outputs: stream1 node 6 rejected by acc" | 910,546 | 1,063,913 |
| 1,024 | 2 | **1** (node 1) | link 2 | "stream1 outputs: stream1 node 2 rejected by acc" | 925,342 | 1,392,841 |
| 16 (smoke) | 4 | 4 (all) | — | ACCEPT | 757,179 | — |
| 65,536 (season) | 512 | 0 | link 0 (leaf) | OOM, §4.2 | — | — |

This confirms F2's `verify-native` counts (5 at `n_f = 16`, 1 at `1024`), now with the real badge.
No stream at any `n_f` reaches the season's `M = 512` links: the running bundle grows by one leaf
per link. Even at `n_f = 1`, where a leaf `π` is 95,719 bytes (F2), about 10 links fit.

### 4.4 `T_V` enforced (run 3d)

Season files `G/seasons/tv-*.toml`: the shape plus `[tv] enforce = true`. Run with
`--parts calibrate,tree`.

| Shape | `T_triv_best_ns` | `T_V` cap | root `acc` | ratio | message |
|---|---|---|---|---|---|
| `r = 2, n = 16` | 153,815 | 0.0154 ms | 945.9 ms | about 61,000× | "tree1 root and samples: tree1 root took 945.893 ms, above T_V = 0.015 ms" |
| `r = 1, n = 1024` | 1,939,340 | 0.194 ms | 1,776.1 ms | about 9,200× | "tree1 root and samples: tree1 root took 1776.054 ms, above T_V = 0.194 ms" |

**No.** The entry does not pass `T_V = T_triv,best / 10` at any shape it can reach. The trivial
check of a reachable tree is at most 4,096 compressions, under 6 ms. One SNARK verification in
Lean costs 0.2 s at `n = 16` and 1.8 s at `n = 4096`, and a bundle root runs `2^r` of them.

At the season shape the cap would be 266.8 ms (§4.1). A single leaf's `acc` already exceeds that
at `n = 4096` (1,771 ms, the `r = 0` row of §4.3). The root's bundle of 64 leaves would also be far
above `proofCap`.

## 5. Frictions with the harness as a user (evidence for the rules' feedback)

1. **The rebuild binding rejects an entry whose builds are identical** (§2.1). An entry that ships
   modules outside `Solution`'s closure gets "the gate tree's build differs … (22 artifacts)". The
   rules ask for controls, but `FORMAT.md`, `PROVER.md` and `evaluate.py` never say that every module
   must be imported by `Solution`. Nothing in the harness checks such controls either: the
   comparator ignores modules outside `Solution`'s closure, and the gate tree only builds them.
2. **The pinned packages are not pinned by default** (§2.2).
   - `org-setup.sh`'s default roots omit CompPoly, ArkLib, VCVio and PolyFun, so an import of
     CompPoly is checked as entry code. One `@[csimp]` lemma inside CompPoly then rejects the entry.
   - The message names a CompPoly module, which an entrant cannot change.
   - The fix is the undocumented `RF_ORG_ROOTS` variable. It is read by `org-setup.sh` and not
     mentioned in its header, in `evaluate.py` or in the docs.
   - The reason also reads `gate: gate: REJECT …`: the prefix is doubled.
3. **A memory kill of the second kernel reads as a broken certificate** (§2.4). The default 14 GiB
   cap kills nanoda and, through the scope, the comparator. The Lean kernel then never runs. The
   result is `provisional` with "comparator: exit -15, the certificate does not check".
   - The comparator's output is block-buffered and lost, so `comparator.log` ends at "Running
     nanoda kernel on solution", with no error line.
   - The harness should run the kernels separately, or at least read the scope's `oom-kill` result
     and report it as a harness or resource failure.
4. **A failed tree run loses the prover's log and the timings.**
   - When `tree_repeat` raises, its record (status, seconds, `prover_log`) never reaches the
     result. So 3a reads only "prover tree exit 3".
   - The actual reason, the service's `CAP` refusal, had to be reproduced outside the runner
     (§4.1).
   - Likewise `T_tree` and the `T_V` block are absent from every rejected run's JSON. `T_tree` is
     only in `run.log`, and a failed stream keeps no `leaf_s`/`merge_s`.
5. **An OOM kill reads as "proof.bin: missing; stderr: "** (§4.2). The runner ignores the
   request's exit status and the scope's `oom-kill` result. A prover killed at its cap and a prover
   that forgot to write its file look the same.
6. **"rejected by acc" gives no reason.** Every frontier failure is the size cap. The badge prints
   only `accept`/`reject`, so telling `|π| > proofCap` from `SigOk` or `V = false` meant parsing the
   stored files by hand. A reason code (size, signature, verifier) in the badge's output would help
   entrants and costs nothing on the accept path.
7. **Per-check `acc` times are not in the result.** The JSON records the tree root's and samples'
   times only. Stream outputs, canaries, DoS inputs and liveness checks appear only through
   `T_V.max_ns` or not at all. Every time in §3 came from re-running the badge on the stored batch
   lists.
8. **The comparator's phases are invisible.** `comparator_s` is the only number: build, export and
   each kernel cannot be told apart from the logs because of the buffering.
   - Each fresh tree also spends 21–29 s in `lake env` start-up running `git diff --exit-code
     HEAD` in every package: 29 s of 513 s in run 1c.
9. **A private, writable package tree is required**, and it is expensive.
   - `org-setup` writes compiled objects into the package tree, and so does every badge build that
     imports a module outside the organiser's closure. Here that was 986 objects: 952 Mathlib, 28
     CompPoly and 6 Batteries. The entry's Mathlib imports reach far beyond the closure `org-setup`
     prebuilds.
   - So the shared read-only tree cannot be used. The private copy is 9.2 GB: 4 min to copy on
     ext4, where there is no reflink.
   - `org-setup` then needs 5 min 56 s, of which 149 s is hashing 34,290 `.olean` files for the
     manifest.
   - A manifest check (about 6 s) runs four times per certificate job.
10. **The badge executables are 142.7 MB each**, and the badge build of an entry that adds modules
    beyond the organiser's closure compiles them inside the certificate job: 74 s and 986 package
    objects here. Stage B's deviation 6 measured the size; this is its cost on a real entry.
11. **Two known runner quirks persist** (F2 frictions 6 and 7):
    - `t_leaf` = Σ leaf / `M` with `M + 1` leaves (0.2512 vs a mean of 0.201);
    - the service calibration runs `threads_32` even under a 16-core affinity.
12. **Liveness at the season's liveness shape costs 24 s** for this entry: `r = 1, n = 16`, a log of
    30,820 entries, 121 MB. This is stage B's open question 4 measured on a real entry. It is
    affordable here, but it grows with the log, and nothing but the 3,600 s badge timeout bounds it.
13. **The DoS column is uncapped below `verify_s`.** Its worst input cost 1.59 s at `r = 0,
    n = 4096` and 1.35 s at `r = 3, n = 1`, against `T_V` caps of 0.56 ms and 0.017 ms. These are
    not `T_V`-checked; only `verify_s = 60 s` bounds them.
14. **Setup steps that are easy to miss.**
    - `scripts/tools.env` must be sourced before `cert`, or the comparator is "missing"; its
      defaults point at this VM's `/home/devops/CambridgePQ/…` checkouts.
    - `evaluate.py` must be run from the organiser checkout itself: it finds the service, the
      Lean tools and the scripts relative to its own path.
    - `--work` must not exist.
    - The orchestrator's two corrections (merged core `a874f87`; CompPoly roots) were needed before
      a real entry could pass.

## 6. Findings on the entry (fixes described, not applied)

1. **Import every module from `Solution.lean`**, or have the harness fixed (§2.1). The import form
   is V's diff above. It adds the controls to the environment the gate loads and to the badge's
   link. The cost:
   the comparator's `Solution` build took 238 s with V and 157 s without (run 1a), under different
   load; the gate tree builds them either way, and the badge build was 74 s here.
2. **The transcript's `absorb` must keep every query ≤ 2^20 bytes** for `n ≥ 2^18` (§4.1). The fix
   is a chunked absorb, a transcript change in both the prover and the Lean `V`. It does not move
   the frontier, which `proofCap` sets at `2^r · n ≤ 4096`.
3. **Memory** at `n ≥ 2^16` (§4.2): 11.14 GB at the kill, against F2's 15.8 GB for a whole leaf.
4. **`T_V`** (§4.4): the Lean SNARK verifier runs at about 0.2 s per leaf at `n = 16`. Against
   `T_triv / 10` the gap is 4–5 orders of magnitude at every reachable shape. Bundling multiplies
   it by `2^r`.

## 7. Logs (`G/` = the worktree's `logs/f3/`)

| What | Files |
|---|---|
| the frozen entry, variant V and its diff | `submissions/spartan-srom/`, `entry-closure/`, `entry-closure.diff` |
| organiser checkout, package tree, setup | `org/` (at `a874f87`), `pkgs/`, `org-setup.log`, `org-setup-default-logs/`, `org-setup-comppoly.log`, `allowlist-default.txt`, `manifest-default.sha256` |
| certificate jobs | `cert-lean*`, `cert-closure-default*`, `cert-closure*`, `cert-nanoda*` (`.log`, `.json`, `.rsmon.json`, work directory), `cert-frozen-comppoly*`, `nanoda-standalone/` |
| benchmarks | `bench-smoke*` (+ `bench-smoke-reverify.log`), `bench-season*`, `bench-season-stream*`, `fr-<shape>*`, `frontier-driver{,2}.log`, `frontier-table.txt` |
| season files | `seasons/*.toml` |
| diagnostics | `diag/tree-r6-n2p18.log` (the season tree reproduced) |
| monitor scripts (session scratchpad, copied) | `tools/{rsmon,rssum,reverify,treerun}.py`, `tools/{runmon,frontier,nanodacurve}.sh` |
