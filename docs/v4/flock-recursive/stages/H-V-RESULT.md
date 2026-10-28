# H-V: the verifier's time on a GitHub runner — RESULT

Track H-V measured the Flock-recursive verifier `V` on the evaluation's runner image
(`ubuntu-24.04`, 4 vCPU). The cap's chain checker ran in the same job on the same pinned core, so
`T_V` and `V` come from one machine. Entry sources: HEAD `5035389`. Core: the `.contract` pin
`15dac52`.

## Method

`probe/fr-vtime/run.sh` (workflow `probe.yml`, `.github/probe.conf` = `fr-vtime`):

1. The machine: `lscpu`, the CPU flags, the runner image.
2. The core is cloned at the `.contract` pin. `lake exe cache get` runs in that clone, with three
   tries.
3. `gen.sh` writes the probe's lakefile and manifest: the entry's `FR*` modules as a library, the
   core as a path package, and the core's own package tree. Then `lake build vtime` runs
   (`timeout 5400`).
4. The core's `harness/lean-tools` `chaincheck` is built: the organiser's checker, the one that
   calibrates `T_V`.
5. Everything below runs pinned with `taskset -c 1`.
   - S-E8's method: `vtime v N 21`, a synthetic N30 proof (|π| = 797,904 B). Its oracle trace
     (8,891 queries) is recorded once, then 21 warm `runSeq` runs give the best and the median. This
     runs in 3 separate processes.
   - Then `vtime v L 21` and `vtime v P 21`, one process each.
6. `chaincheck` at the season shape: `r = 6`, `n = 262144`, 3 runs. `T_triv,best` is the minimum,
   and the cap is `T_V = T_triv,best / 10`.

`VTime.lean` is S-E9's probe (`logs/fr-build-SE9/probe/VTime.lean`), with the full finals
`finPf` and `Layout.lRows`.

## Results

### The tier of record: AMD EPYC 7763

Two runs, each on its own runner.

| Run | V N30 best (3 procs) | V N30 median (3 procs) | V L32 best / med | V P30 best / med | chaincheck ms (3) | `T_triv,best` | cap `T_V` | margin cap/V (best / median) |
|---|---|---|---|---|---|---|---|---|
| [40670785489](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40670785489) | 169.89 / 171.30 / 170.96 | 172.18 / 172.97 / 174.37 | 168.53 / 170.86 | 168.00 / 170.10 | 2060.4, 2063.4, 2062.8 | 2060.4 ms | **206.04 ms** | **1.213× / 1.191×** |
| [40670789125](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40670789125) | 176.86 / 175.60 / 175.64 | 181.42 / 180.66 / 179.41 | 171.72 / 175.63 | 175.80 / 181.20 | 2073.5, 2060.7, 2066.0 | 2060.7 ms | **206.07 ms** | **1.174× / 1.141×** |

- **V N30 on the 7763:** the best is 169.9 to 175.6 ms, and the median of the per-process medians
  is 173.0 to 180.7 ms.
- **The cap:** 206.0 ms in both runs. This agrees with phase 0's 205.9 ms (`phase0/M-measure.md`
  §4).
- **The margin:** at least **1.17×** on the best and **1.14×** on the median.
- **Variance between the two 7763 hosts:** about 3.5 % on V. The cap differs by less than 0.1 %.
- **Variance within a run:** the 21-run spread in one process is about 1 to 3 %.

### The other tier: Intel Xeon Platinum 8573C

These runs were not requested. They landed on 8573C hosts.

| Run | V N30 best | V N30 median | `T_triv,best` | cap | margin (best / median) |
|---|---|---|---|---|---|
| [40666251101](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40666251101) | 139.16 ms | 141.34 ms | 2301.1 ms | 230.11 ms | 1.654× / 1.628× |
| [40668968294](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40668968294) | 144.14 ms | 146.39 ms | 2368.0 ms | 236.80 ms | 1.643× / 1.618× |

On this tier V is faster and the cap is looser, so the margin is about 1.63×. The 7763 is the
binding tier.

A third push ([40668064175](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40668064175),
EPYC 7763) failed before it measured anything: the elan toolchain download timed out in
`lake exe cache get`. That failure is why `run.sh` now retries.

### The VM, for the ratio

Logs in `logs/H-V/vm-core22/`: the same `vtime` binary, built by `run.sh` from the private tree,
pinned to idle core 22 of the VM.

| | V N30 best | V N30 median | `T_triv,best` | cap |
|---|---|---|---|---|
| VM (QEMU), core 22 | 211.68 / 204.83 / 215.16 ms | 222.12 / 215.61 / 234.26 ms | 2627.0 ms (2675.0, 2676.7, 2627.0) | 262.7 ms |

S-E9's VM figure was 207.2 ms best. The VM margin is therefore 1.28×.

The first local run, pinned to core 30, measured V 440 ms and chaincheck 5.3 s. Another process
(`plant`) was running on core 30 at the time, so those figures are discarded
(`logs/H-V/local-run.log`).

### Ratio of VM V to runner V

| | VM / 7763 (run 4) | VM / 7763 (run 5) | VM / 8573C |
|---|---|---|---|
| V best (204.8 ms VM) | **1.206** | **1.166** | 1.42–1.47 |
| V median (222.1 ms VM, the median of 3) | 1.284 | 1.229 | 1.52–1.57 |
| chaincheck `T_triv,best` (2627 ms VM) | 1.275 | 1.275 | 1.11–1.14 |

On the 7763, V speeds up by 1.17–1.21× (best), while the chain checker speeds up by 1.275×. So
the VM-to-7763 conversion through the checker's 1.28 overstates the runner's margin.

- **Converted estimate:** V_VM / 1.28 = 160 ms, a margin of 1.29×.
- **Measured:** 170 to 176 ms, a margin of 1.17 to 1.21×.

The VM's own margin (V_VM against the VM's own cap, 1.28×) is also optimistic for the 7763, by
about 6 to 9 %.

## Build on the runner

The tree has no cache: a fresh clone, then `lake exe cache get`, then CompPoly, the core and the
entry's closure, all built from source.

| Run | `lake build vtime` | Whole probe |
|---|---|---|
| 8573C | 8 m 31 s and 8 m 48 s | 742 s and 751 s |
| 7763 | 10 m 10 s and 10 m 53 s | 827 s and 893 s |

The whole probe fits well inside the job's 120 min. Logs: `logs/H-V/run*/probe-fr-vtime/out/build.log`.

## Files

- **Artifacts:**
  - 8573C: `logs/H-V/run1` (run 40666251101) and `logs/H-V/run3` (40668968294).
  - 7763, the run that failed: `logs/H-V/run2` (40668064175, machine and cache-get logs only).
  - 7763: `logs/H-V/run4` (40670785489) and `logs/H-V/run5` (40670789125).
- **Local test:** `logs/H-V/local-run.log`, `logs/H-V/local-out/`, and the VM reference
  `logs/H-V/vm-core22/`.
- **Probe branches** on `origin`: `probe/fr-vtime-1` and `-2` (commit `7f73217`), and `-3`, `-4`,
  `-5` (`8ff4720`, which adds the retry). Each one's `.github/probe.conf` lists only `fr-vtime`.

## For the orchestrator

- **To commit under `probe/fr-vtime/`:**
  - `run.sh` (new);
  - `gen.sh` (rewritten: SRC/ORG/PKGS parameters, and it writes the manifest and toolchain);
  - `VTime.lean` (S-E9's version);
  - `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, as `gen.sh` regenerates them with
    the local defaults (HEAD's `submissions/flock-recursive/lean`, `logs/org`, `logs/pkgs`). Commit
    these three or leave them out: `run.sh` regenerates them on the runner.
- **Blueprint (not edited):** the `T_V` row could cite the runner measurement in place of the VM
  conversion: on the EPYC 7763, V N30 is 170 to 176 ms best (173 to 181 ms median) against a cap of
  206.0 ms, a margin of **1.17 to 1.21×**. HEAD's message, "T_V ≈ 183 ms VM (1.44×)", is a VM
  projection. The runner-measured margin of the current code is lower than the VM conversion
  suggests.
