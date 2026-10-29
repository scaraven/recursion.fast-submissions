# H-cert2: the certificate job's build and kernel steps, re-timed at `ea3e130` — RESULT

**Verdict.** Every step fits its pinned cap at HEAD `ea3e130` (core `64378d2`).

| cap | measured on the EPYC 7763 (or scaled to it) | margin |
|---|---|---|
| `build_s` 1,200 | harness build ≈ **736 s** (worst of 3 runs, scaled); direct `lake build Solution` on a 7763: **679.7 s** | **1.63×** (direct: 1.77×) |
| `kernel_s` 600 | comparator on `certified` + `submission`: **265.2 s** (**244 s** without the challenge's full-size export) | **2.26×** (2.46×) |
| | upper bound (every non-control FR declaration in Solution's closure): 441.4 s (411 s) | 1.36× (1.46×) |
| `gate_s` 120 | ≤ 12.6 s (scaled) | ≥ 9.5× |
| `badge_s` 180 | ≤ 57.5 s (scaled) | ≥ 3.1× |

Memory peaks are far below the caps: build 3.9–4.9 GiB of 12G, comparator 4.26 GiB (`certified`) and 4.72 GiB
(upper bound) of 14G.

Logs and artifacts are in `logs/H-cert2/run-<id>/probe-{si-cert,cert2}/`. The machine factors are in
`logs/H-cert2/factors.txt`, made by `logs/H-cert2/factor.py`.

## 1. Runs

Three workflow runs of `probe.yml` at `ea3e130` + `probe.conf` (`si-cert`, `cert2`). Each run had two jobs,
each on its own runner. The branches `probe/h-cert2{,-b,-c}` are deleted.

| run | job | CPU | factor vs G3's 7763 |
|---|---|---|---|
| 40858219136 | si-cert | EPYC 9V74 | 0.915 |
| 40858294330 | si-cert | EPYC 9V74 | 0.740 |
| 40858294461 | si-cert | EPYC 9V45 | 0.639 |
| 40858219136 | cert2 | EPYC 9V74 | 0.744 |
| 40858294330 | cert2 | EPYC 9V74 | 0.704 |
| 40858294461 | cert2 | **EPYC 7763** | 0.954 |

None of the three si-cert jobs landed on the 7763. That used up the three runs.

**The machine factor** is a run's own build log against the 7763 build of G3 (run 40839253556,
`logs/probe-cert-g3`, at `2bf06e2`). It sums the Lake job times of the 218 entry modules that both runs built and
whose source is unchanged between `2bf06e2` and `ea3e130` (`factor.py`, `changed-2bf06e2-ea3e130.txt`). This is
RET-3's method. The same 9V74 class gave 0.70–0.92, so a factor measured per run is needed; a factor per CPU
model is not enough. Scaled this way, all six builds agree: the entry costs **2,485–2,508 CPU-s at G3-7763
speed**.

## 2. Build cap (`probe/si-cert`: the harness's own `evaluate.py cert`, caps raised)

| run | CPU | `build_s` | / factor | `comparator_s` | `gate_s` | `badge_s` | built modules |
|---|---|---|---|---|---|---|---|
| 40858219136 | 9V74 | 673.5 | 736 | 47.5 | 11.2 | 52.6 | 271 |
| 40858294330 | 9V74 | 541.9 | 732 | 41.4 | 9.3 | 41.5 | 271 |
| 40858294461 | 9V45 | 466.6 | 730 | 32.4 | 7.2 | 35.8 | 271 |

- **Status.** Every run returned `provisional`, with no reject reasons. The provisional reason is "comparator
  (Lean kernel): exit 1": the statement check rejects `certified (h : Open4)`. The gate printed `PASS`.
- **Build at 7763 speed.** ≈ 730–736 s, so **margin 1.63×** against 1,200.
  - Against the old 600 s cap it would still be over (0.82×).
  - G3 at `2bf06e2` took 696.2 s on the 7763, with 250 modules. The closure is now 271 modules: S-H4 pass 7
    added 34 modules (the `FRNodeRows4*`/`FRXDec4*`/`FRXLag*` route) and RET-3 dropped 13. RET-4's cut is
    already included.
- **Direct 7763 cross-check.** The cert2 job of run 40858294461 ran `lake build Solution` on a 7763, outside
  the sandbox, with 4 jobs: **679.7 s** (2,383.5 CPU-s), margin 1.77×. That 7763 was 4.6 % faster than G3's
  (factor 0.954). The 736 s figure is against the slower 7763 on record.
- **Gate and badge.** Scaled by the same build factor (crude: neither step is a Lake build), the gate is
  ≤ 12.6 s and the badge ≤ 57.5 s. G3 measured 12.2 s and 59.1 s directly on its 7763.
- **The comparator time in this table is not the kernel.** It stops at the statement check (32–48 s).

## 3. Kernel cap (`probe/cert2`: H-cert's probe, retargeted)

`probe/cert2/run.sh` reuses `probe/cert-time`'s tools. Its build tree is `mkfresh`'s layout plus `Solution.lean`,
and it builds `lake build Solution`.

The comparator is the pinned binary (`build-kernels.sh`), with **challenge = solution = `Solution`**, so that the
statement check passes and the run reaches the export and the kernel replay. Two target sets:

- **cert:** `theorem_names = [RecursionFast.Challenge.certified]`, `definition_names =
  [RecursionFast.Challenge.submission]`. These are exactly the harness's targets (evaluate.py step 4). The
  closure is 45,676 constants, and 44,353 declarations are replayed.
- **upper:** the two targets plus every non-control theorem and definition of the 269 FR modules in Solution's
  import closure (11,154 + 6,457 names). The closure is 61,503 constants, and 59,999 declarations are replayed.

| run | CPU | comparator cert (w/o export 1) | margin | comparator upper (w/o export 1) | margin | KReplay cert / upper (kernel s) | peak cert / upper |
|---|---|---|---|---|---|---|---|
| 40858294461 | **7763** | **265.2 (244)** | **2.26× (2.46×)** | **441.4 (411)** | **1.36× (1.46×)** | **135.2 / 245.9** | 4.26 / 4.72 GiB |
| 40858219136 | 9V74 | 256.9 (240) | 2.34× | 421.4 (395) | 1.42× | 117.0 / 212.4 | 4.25 / 4.71 GiB |
| 40858294330 | 9V74 | 238.9 (222) | 2.51× | 399.3 (375) | 1.50× | 112.7 / 198.7 | 4.26 / 4.70 GiB |

Every comparator run ended with "Lean default kernel accepts the solution; Your solution is okay!"

**On the 7763, cert set:**

- Each lean4export takes 21 s and peaks at 3.26 GiB.
- After the last export, 196 s remain: the kernel replay (135 s by KReplay) plus about 60 s to parse, compare
  and check the axioms.
- "w/o export 1" drops the challenge's export. In the real job that export is a few constants. The correction
  still counts the second full-size parse, so 244 s is slightly high.

**Kernel hot spots, 7763, cert set (KReplay):**

- The total is 135.2 s: FR modules 99.7 s, other modules 35.5 s.
- `BF64.basePoly_irreducible` costs 15.3 s. It is core-owned.
- `FRSkip` costs 9.2 s, of which `pinnedW_eq` is 5.4 s and `pinned_cert` 3.5 s.
- Next come `FRSoundness4Pos` (5.3 s), `FRSoundness4TailD` (5.1 s) and `FRNodeRows4Ext` (4.6 s, nearly all
  `W4.xRows_length`).
- No single declaration other than `basePoly_irreducible` exceeds 5.4 s.

**Compared with H-cert.** H-cert's "core" proxy was 371.7 s on the 7763, over 190 modules of every FR
declaration. Today's real target closure costs 265.2 s. The upper set is larger than H-cert's proxy (more
modules), so it costs more (441.4 s).

## 4. Caveats

- **`Open4` is a hypothesis of `certified`,** so its eventual proof is not in the `cert` closure. When `Open4` is
  proved, the closure grows. The `upper` set bounds that growth only for declarations already in Solution's
  import closure at `ea3e130`. New modules (for example the uncommitted `FRNodeLinks4`) add to both the build
  and the kernel. Against `upper`, the kernel margin on the 7763 is 1.36×.
- **Sandbox.** cert2 runs outside the sandbox (pass-through landrun, as H-cert did), and its build is
  `lake build Solution`, not `+Challenge +Solution`. si-cert is the harness itself, with the sandbox.
- **The build figure of record is scaled,** because no si-cert job landed on a 7763. The scaled figure
  (≈ 736 s) and the direct 7763 `lake build Solution` (679.7 s) agree within the spread between 7763 hosts.

## 5. Files

| file | what |
|---|---|
| `probe/cert2/run.sh` | The kernel probe (from `probe/cert-time/run.sh`; target sets `cert` and `upper`) |
| `probe/cert2/gen.sh` | `cert-time/gen.sh`, also copying `Solution.lean` |
| `probe/cert-time/summary.py` | Two lines changed: the build cap from `BUILD_CAP` (default 600), and `Solution` counted in the build table |
| `logs/H-cert2/factor.py` | The machine factor against G3's 7763 build log |
