# H-cert: the certificate job's build and kernel time on the runner — RESULT

**Verdict.** On the EPYC 7763, the slowest runner tier, **the build is over `build_s = 600 s` in all
three runs: 611.5 s, 613.4 s and 711.6 s (margin 0.84–0.98×).** The kernel step fits
`kernel_s = 600 s`. On the closest proxy of `certified`, the comparator took 371.7 s on the 7763
(1.61×). The upper bound, every FR declaration, took 410.9–501.5 s (1.20–1.46×). Memory is far below
both caps: the build peaked at 3.4–4.0 GiB against 12G, the comparator at 4.46 GiB against 14G.

Entry at HEAD `2ef39b3` (190 FR modules plus `FR`, 2,416 jobs); core at the pin `6d05d00`;
Lean v4.34.1. Logs and artifacts are in `logs/H-cert/`. The cross-run table is
`logs/H-cert/tables.txt`, made by `logs/H-cert/tables.py`.

## 1. What the certificate job builds and times (core `6d05d00`)

`evaluate.yml` job `certificate` → `harness/evaluate.py cert`, with the caps from `season.toml [certificate]`:

- **build_s (step 3).** In a fresh tree made by `mkfresh` (the entry's `lean/*.lean` as the library
  `RFSubmission`, the core required by path, the core's package tree), it runs
  `lake build +Challenge +Solution` inside the sandbox, in a 12G scope, timed by wall clock.
  Mathlib, CompPoly and the contract come prebuilt from the setup job's cache, so the step builds
  only entry modules (our runs built 0 non-FR modules). Jobs run 4 at a time.
- **kernel_s (step 4).** `lake env comparator config.json` runs in a 14G scope. The comparator is
  leanprover/comparator `d03acab` with lean4export `076e8e5`. It runs the sandboxed
  `lake build Challenge`, then `lean4export Challenge -- <targets>`. It then runs
  `lake build Solution` (up to date) and `lean4export Solution -- <targets>`. The targets are
  `certified`, `submission`, the three axioms and the kernel primitives; each export holds the
  targets' dependency closure. Next it parses both exports, compares them and checks the axioms.
  Last comes `Kernel.Environment.replay` of the solution's export into an empty environment,
  single threaded. This is the whole replay of the closure, including the Mathlib, CompPoly and
  contract constants it uses. There is no lean4checker. nanoda runs only with the workflow input
  `nanoda` (default false).
- `gate_s = 120` and `badge_s = 180` need `Solution`; they were not measured (see §6).

## 2. The probe

These are the files under `probe/cert-time/`. Run one on the runner with `.github/probe.conf` =
`cert-time` and a push to `probe/cert-*`; the `probe.yml` workflow is unchanged.

| file | lines | what |
|---|---|---|
| `run.sh` | 141 | Clones the core at the `.contract` pin, runs `lake exe cache get` and org-setup step 1 (the setup job, untimed), and builds the comparator with the core's `build-kernels.sh`. **Step 3:** a `gen.sh` tree, then `lake build FR`, cold except for the organiser environment. **Step 4:** the pinned comparator, once per target set. **Step 5:** KReplay. Each step runs in a `systemd-run --user --scope -p MemoryMax=…` (12G build, 14G comparator), and the scope records its cgroup `memory.peak`. `/usr/bin/time -v` records wall time and max RSS. `timeout` is 2,400 s per step, above the cap so that an over-cap step is measured to the end. A 1 s process sampler gives the comparator's phases, because its stdout is block-buffered. |
| `gen.sh` | 32 | The build tree, laid out as `mkfresh` does |
| `ListConsts.lean` | 46 | Lists every theorem and definition declared in an `FR*` module (8,736 theorems, 4,962 definitions; no axiom or opaque) |
| `filter-controls.py` | 15 | Builds the **core** set by dropping the controls: 103 theorems and 52 definitions, chosen by their `*Controls` namespace or `ctrl`/`toy`/`_kat` names |
| `KReplay.lean` | 107 | The comparator's replay (a copy of `Lean.Replay`) on the same closure, timing each `addDeclCore`. Writes `ns, module, name` per declaration |
| `landrun-pass.sh` | 6 | Stands in for `COMPARATOR_LANDRUN` (drops the sandbox; timing only) |
| `summary.py` | 86 | The per-run summary |

**The proxy for `Solution`.** There is no `Solution.lean` yet. Step 3 builds `FR`, which imports all
190 modules. The real build is Solution's closure: it drops 3 small `*Controls` modules (15–19 s of
CPU) and adds S-I's modules. The blueprint budgets those at about 1,660 lines.

Step 4 runs the real comparator binary with challenge = solution = `FR`. The `theorem_names` and
`definition_names` are either every FR declaration (**full**, an upper bound) or every one except
the controls (**core**, the closest proxy). `certified` will not reach the controls; whether it
reaches everything else is S-I's to settle. Because challenge = solution, export 1 and the parse of
the challenge are full size here. In the real job the challenge export is a few constants, so
"without export 1" is the better estimate. It still counts the second parse, so it is slightly
high.

## 3. Results (runner, 4 vCPU, `ubuntu-24.04`)

Eight runs, each on its own runner. Three landed on the 7763.

| run | CPU | build wall (margin) | build CPU s | build peak (cap 12G) | comparator core (margin) | core w/o export 1 | comparator full (margin) | comparator peak (cap 14G) | KReplay core, kernel s |
|---|---|---|---|---|---|---|---|---|---|
| [40737683146](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40737683146) | **EPYC 7763** | **711.6 s (0.84×)** | 2,695 | 3.95 GiB | – | – | 501.5 s (1.20×) | 4.47 GiB | – |
| [40737761222](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40737761222) | **EPYC 7763** | **611.5 s (0.98×)** | 2,318 | 3.40 GiB | – | – | 410.9 s (1.46×) | 4.46 GiB | – |
| [40751551049](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40751551049) | **EPYC 7763** | **613.4 s (0.98×)** | 2,310 | 3.52 GiB | 371.7 s (1.61×) | 345 s (1.74×) | 429.5 s (1.40×) | 4.46 GiB | 207.0 |
| [40746452803](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40746452803) | EPYC 9V74 | 474.3 s (1.26×) | 1,778 | 3.49 GiB | 327.9 s (1.83×) | 308 s (1.95×) | 389.0 s (1.54×) | 4.46 GiB | 174.7 |
| [40751551643](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40751551643) | EPYC 9V74 | 444.5 s (1.35×) | 1,672 | 3.68 GiB | 315.3 s (1.90×) | 295 s (2.03×) | 366.3 s (1.64×) | 4.46 GiB | 161.9 |
| [40746452591](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40746452591) | Xeon 8573C | 413.2 s (1.45×) | 1,564 | 3.37 GiB | 276.8 s (2.17×) | 257 s (2.34×) | 316.3 s (1.90×) | 4.46 GiB | 160.1 |
| [40742498014](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40742498014) | Xeon 6973P-C | 408.6 s (1.47×) | 1,541 | 3.44 GiB | 307.8 s (1.95×) | – | 346.4 s (1.73×) | 4.46 GiB | 163.7 |
| [40742497683](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40742497683) | EPYC 9V45 | 388.8 s (1.54×) | 1,447 | 3.64 GiB | 302.6 s (1.98×) | – | 347.6 s (1.73×) | 4.46 GiB | 143.2 |

Notes on the table:

- Runs 40737683146 and 40737761222 used the first probe, which had only the full set and no
  sampler.
- Runs 40742498014 and 40742497683 had a sampler that died under `set -e`, so they have no
  "without export 1" figure.
- Every comparator run ended with "Lean default kernel accepts the solution; Your solution is okay!"
- Each run's `out/` directory (the artifact `probe-cert-time`) and `run.log` are in
  `logs/H-cert/run-<id>/probe-cert-time/`.

**What the numbers say:**

- **The build is CPU-bound.** Lake keeps 4 jobs busy: 378–379 % CPU, with wall ≈ (user + sys) / 3.8.
  It is not memory-bound: the peak is 3.4–4.0 GiB of 12G. On the 7763 the build costs 2,310–2,695
  CPU s, against 1,447–1,778 on the faster hosts (1.4–1.7× more).
- **What the build needs to fit.** A 1.3× margin on the 7763 means a wall of ≤ 462 s, so build CPU
  ≲ 1,750 s. That is a **≥ 25 % cut** from the median 7763 run, and ≥ 35 % from the worst. S-I's
  modules come on top of this.
- **The kernel is not the problem.** On the 7763, the comparator spends 27 s per lean4export run
  (3.2 GiB each) and 303 s after the last export. That 303 s splits into the kernel replay (207 s by
  KReplay) and about 96 s to parse two exports, compare and check the axioms. The real job parses
  one small and one large export, so it should take about 330 s on the 7763 (≈ 1.8×).
- **The controls.** Including every control (the full set) costs about 50–60 s more on the
  comparator. `certified` will not reference the controls.
- **The development VM.** Kernel replay is 401 s (core) and 540 s (full); the full comparator took
  768 s. The VM was shared and loaded, and is about 2× slower than the 7763 here, so VM figures
  overstate. Logs: `logs/H-cert/local/`.

## 4. What to golf

### 4.1 Build (the step over its cap)

Lake's per-module job time in seconds, which is close to CPU time (jobs are single threaded). The
three 7763 runs are 40737683146 / 40737761222 / 40751551049; the median is over all eight runs.

| module | 7763 runs (s) | median, all runs |
|---|---|---|
| FRVIRFinalsSG | 114 / 72 / 80 | 62 |
| FRXBary | 80 / 72 / 71 | 46 |
| FRXAgree | 61 / 52 / 55 | 39 |
| FRXFwd | 64 / 47 / 51 | 36 |
| FRXOut | 58 / 50 / 51 | 34 |
| FRXBfly | 50 / 45 / 45 | 33 |
| FRVIRSpec | 53 / 42 / 41 | 31 |
| FRXMsg | 50 / 46 / 44 | 30 |
| FRVIRFinals | 43 / 36 / 33 | 27 |
| FRXField | 43 / 35 / 33 | 26 |
| FRXFlag | 39 / 35 / 35 | 26 |
| FRAgg | 31 / 32 / 31 | 24 |
| FRXRead | 42 / 35 / 36 | 24 |
| FRXBaryTop | 33 / 30 / 27 | 21 |
| FRXChainFlock | 27 / 28 / 24 | 20 |
| FRSkip | 27 / 23 / 24 | 20 |
| FRVIRCompile | 30 / 26 / 25 | 19 |
| FRXEqT | 35 / 27 / 31 | 19 |
| FRShape4 | 27 / 21 / 21 | 18 |
| FRFieldBaseCorrect | 29 / 24 / 24 | 18 |

In 7763 run 40751551049, the module job times sum to 2,119 s:

- the top 20 modules are 790 s (37 %);
- the 43 `FRX*` modules (the extractor DSL) are 804 s (38 %);
- the `FRVIR*` modules are 379 s;
- the `FRSoundness*` modules are 425 s.

The 25 % cut, about 550 CPU s on the 7763, is roughly the top 12 modules halved. Several of these
are controls-heavy (`FRXAgree`, `FRXFlag`, `FRAgg` hold the `toy*`/`ctrlA_*` controls). Controls in
modules that `Solution` imports are built by the harness even though the kernel step never sees
them. Moving those controls into modules outside Solution's import closure removes their build
cost from `build_s`, but **Q7 then never builds them in the harness**. Whether that is acceptable
for controls is a rules question (AGENTS.md: controls must exist and pass; who checks them?).

### 4.2 Kernel (within its cap; for reference)

KReplay on the core set, 7763 run 40751551049, kernel s (declarations). Total: 207.0 s, of which
FR is 170.7 s and other modules 36.3 s.

| module | s (decls) |
|---|---|
| CompPoly.Fields.Binary.BF64.Basic | 15.7 (20), essentially all `BF64.basePoly_irreducible` (core-owned; every BF64 entry pays it) |
| FRSkip | 10.1 (102): `pinnedW_eq._proof_1_1` 5.7, `pinned_cert._proof_1_1` 3.6 |
| FRXChainFlock | 7.1 (71): `fsMsgs_items._proof_1_1` 5.7 |
| FRSoundnessFrObl | 6.1 (148): `frontCls_check` 3.3 |
| FRXMsg | 5.7 (478) |
| FRTranscriptDefs | 5.6 (391) |
| FRSoundnessTailD | 5.1 (152): `phOf_check` 2.6, `rounds_check` 1.9 |
| FRNodeReadP | 5.1 (172): `streamOff_slen_le` 2.7 |
| FRFieldBaseCorrect | 4.4 (273) |
| FRSoundnessDefs | 4.3 (114): `rangesOK_eq` 3.2 |
| FRXBfly | 4.3 (434) |
| FRSoundnessCompose | 4.2 (119) |
| FRNodeLayout4 | 3.9 (46) |
| FRShape4 | 3.7 (319) |
| FRXField | 3.5 (715) |
| FRXDecLv | 3.4 (208) |
| FRSoundnessHide | 3.2 (135) |
| FRXBary | 3.1 (384) |
| FRNodeRead | 2.6 (59) |
| FRXBaryTop | 2.5 (182) |

The kernel time is spread thin: 52,691 declarations, with only 11 above 1.5 s. In the full set,
the largest single costs are controls: `toyFlag_run` 16 s, `toyScan_six` 13.5 s and `ctrlA_*`
29 s on the VM (`logs/H-cert/local/summary.txt`).

## 5. Deviations from the harness, with reasons

- **The target is a proxy,** because there is no `Solution`. The build is `FR`, not
  `+Challenge +Solution`; the comparator targets are FR's declarations, not `certified` and
  `submission` (§2).
- **No sandbox.** The build runs outside bwrap and the comparator uses a pass-through landrun. The
  sandbox adds process start-up, not CPU work. The memory scopes and their caps are the harness's.
- **One export is full size.** challenge = solution makes export 1 and its parse full size; the
  "without export 1" column corrects for the export but not for the parse.

## 6. Open questions

1. **build_s is the blocker.** The FR build alone is over 600 s on the 7763 in three runs out of
   three, before S-I's modules are added. Options:
   - golf the top build modules, a ≥ 25 % CPU cut;
   - move the controls out of Solution's import closure (this needs a ruling on Q7 and the
     controls rule);
   - ask the core for a larger `build_s`. The certificate job's other steps leave room: on the
     7763, comparator ≈ 370 s + build ≈ 610 s + gate + badge, inside the job's 30 minutes.
2. **badge_s = 180 s is unmeasured and may also be a risk.** The badge compiles the whole
   `submission` to an executable. If the entry's modules' C must be compiled in the badge step,
   about 190 modules of C on 4 vCPU is not obviously within 180 s. This needs `Solution`; S-I
   should run the real `evaluate.py cert` once a `Solution` exists.
3. **The module count is still growing:** `FRSoundness4*` and `FRX4*` are untracked in the
   worktree now. Re-run this probe after each integration: push `probe/cert-*` with
   `.github/probe.conf` = `cert-time`. It takes 25–33 min per run.

## Records

- Journal: `docs/v4/flock-recursive/stages/H-cert-JOURNAL.md`.
- Runs: eight, listed in §3, on branches `probe/cert-time`, `probe/cert-time-2`, `-3` and `-4`,
  all deleted afterwards. The probe commits were f2921f7, d3ddcd4 and 2630866 on those deleted
  branches; the files are in `probe/cert-time/`.
- Local VM (the probe's first test, and the full and core KReplay):
  `logs/H-cert/local/`, `logs/H-cert/local-run.log`, `logs/H-cert/local-incr-build.log`, and the
  build tree `logs/fr-build-Hcert` (HEAD snapshot).
