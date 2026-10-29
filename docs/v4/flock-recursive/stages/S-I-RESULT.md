# S-I RESULT: the revision 4.1 submission, its Solution, and the first harness measurements

Track S-I, 2026-10-29. HEAD moved during the pass: `cd195c5` → `a5fbd69` (P4f) → `7292eab` (R4i) →
`48d25ef` (P2⁶) → `75eff21` (S-N2) → `1c5a738` (INT-10) → `ba40eda`. Final build on the HEAD
snapshot after INT-10. Build tree `logs/fr-build-SI` (`MINE.txt`: `FRSubmission4V FRSubmission4
FRSubmission4Cert Solution`). Logs `logs/S-I/`; journal `S-I-JOURNAL.md`. Every lake/lean command ran
in a 16G (12G for one file) scope under `timeout`. No sub-agents. Nothing committed. Every eval/probe
branch pushed was deleted after its run.

## Verdict

- **Completeness and `δ` (residuals 8, 9): closed.** `complete_rev4` and `delta_rev4` need no
  hypothesis.
- **The `Submission` compiles and the badge built from it accepts the prover's proofs.** That holds
  locally, and on a runner over a full season-shape stream.
- **The entry's `Solution` builds, gates and badges, but its build takes 882 s on an EPYC 7763,
  against `build_s = 600`.** It is REJECTed before the benchmark (runs 40805207819 on a 7763 and
  40806587168 on a Xeon 8573C). Measured with raised caps by the harness's own `evaluate.py cert`
  (probe 40810876665), the other steps are: comparator 45 s, gate 11.6 s PASS, badge 58.7 s.
- **Stream measurements came from a benchmark-probe `Solution`** (the entry's `acc`, a 132-module
  build). It ran the real evaluation, PROVISIONAL as designed:

  | run | shape | CPU | steps | truncation | S | P̄ | V̄ |
  |---|---|---|---|---|---|---|---|
  | 40809858010 | season | EPYC 7763 | M = 63 of 64 drawn | **truncated** at `stream_s = 960` | **6.42** | 6.02 | 0.400 |
  | 40809817729 | smoke | Xeon 8573C | M = 7 | not truncated | — | — | — |

  The smoke's S is meaningless: chains of 16–128 steps leave only the per-step overhead. Every output
  was accepted, and the DoS column accepted 0 inputs.

## 1. Item 1: completeness (residuals 8 and 9)

The contract at `6d05d00` asks for `Certificate.complete : ∀ vk, CompleteWithError (Rel (S.acc vk))
(S.P vk) (S.V vk) S.δ`. `complete4` (`FRVerifier4`) proves exactly this, at `δ = 0`, for any
`S.V = V4with Vseg Vnode`, `S.qV = qV4` and `S.P = fun _ _ w => ret (encodeF w)`, under every key.
`sub4` meets all three by `rfl` (its `V4F` is literally `V4with VsegF VnodeF`). So this is enough:

```lean
theorem complete_rev4 (vk : Digest) :
    CompleteWithError (Rel (sub4.acc vk)) (sub4.P vk) (sub4.V vk) sub4.δ :=
  complete4 VsegF VnodeF sub4 rfl rfl rfl vk
theorem delta_rev4 : sub4.δ ≤ completenessCap := zero_le
```

Nothing is missing. The certificate's honest prover is the witness-sending encoder. `prover.s`'s
aggregate and node proofs are not covered by the contract's completeness; the harness checks them
concretely (`acc` of every stream output, below).

## 2. What was built (`loc.py`, `logs/S-I/loc.txt`: total / code / thm)

| File | total / code / thm | Content |
|---|---|---|
| `FRSubmission4V` | 86 / 37 / 4 | The badge path. `implB := Impl.implCN` (closed plans, S-E13). Closed per-kind constants `implS`, `implNN2/4/8`, `progS30/31/32`, `progNN2/4/8`, and the dispatchers `progSK`, `progNK`, `implNK`. `VsegF`, `VnodeF`, **`V4F := V4with VsegF VnodeF`**, **`V4F_eq : V4F = VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4`** (per-kind `rfl`). **`epsRQ := ((15/2^124 : ℚ≥0) : ℝ≥0)`**, `epsRQ_eq : epsRQ = epsR`. 130-module closure; no extractor. |
| `FRSubmission4` | 88 / 36 / 12 | `sub0` (`E := none`), then **`sub4 := {sub0 with E := E4X ndNone sub0.acc}`**: `V := V4F`, `P := ret ∘ encodeF`, `ext := ext4With ndNone`, `ε := epsRQ`, `δ := 0`, `qV := qV4`, `fuel := X.fuel`. `sub4_acc` (`rfl`), `sub4_V/qV/E/ε/ext/fuel/P`, **`complete_rev4`**, **`delta_rev4`**, controls `sub4_ctrl`, `sub4_numbers`. |
| `FRSubmission4Cert` | 68 / 27 / 4 | **`Open4`**: `∃ D : NodeDec4 ndNone, ∀ vk, Resid4H (finC finPf) Layout.lRows 0 sub4 ndNone D vk`. **`certificate_sub4 : Open4 → Certificate sub4`** via INT-10's `certificate_rev4H`. `boundsOK`, **`certificateR_sub4`**, **`boundsOK_claim`** (the claim's rendered numbers), and the negative control `not_boundsOK_qV`. |
| `Solution` | 35 / 14 / 1 | The rendered stub verbatim, `submission := FR.Sub4.sub4`, **`certified (h : FR.Sub4.Open4) : CertificateR declared submission`**. |
| `claim.json` | — | `qV` 10240 → **36000** (`qV4`). `error = 15/2^124` (`epsR`), `completeness_error = "0"`, `fuel_base = 3·2^46`, `fuel_per_word = 2^13` (`X.fuel`) were already right. Rendered challenge: `logs/S-I/Challenge.lean`. |
| `probe/si-bench/Solution.lean` | 43 / 22 / 1 | **Benchmark probe only.** It replaces `Solution.lean` on eval branches. `submission` has the entry's `V4F`, `P`, `ε`, `δ`, `qV` (so the same `acc`) and the library's witness-sending `E`/`ext`/`fuel`. `certified` assumes its own statement. It proves nothing. |
| `probe/si-cert/run.sh` | 61 lines | Runs the harness's own `evaluate.py cert` (core at the pin) on the entry, with the `[certificate]` caps raised, so that every step runs to its end. The organiser's environment is prepared as the setup jobs do it. |

**Why the closed constants.** `VC4 … κ` builds `progNode κ (cells κ)` and `implN4F base κ` on
every call. `V4F` names each program and op set as a nullary constant, so the compiled module builds
it once, at process start, outside the badge's timed window.

**No `sorry`.** `certified` takes `Open4` as a hypothesis. The comparator then rejects it ("Challenge
and solution theorem statement do not match", after "Building Solution", so it is not a harness
ERROR). The gate's rule 1 passes (the closure has 44,125 constants, standard axioms). Status is
`provisional`, which lets `evaluate.yml`'s benchmark job run. Note that the source rule at the pin
does **not** reject `sorry`: a `sorry` would also give `provisional` (gate rule 1's `sorryAx`). I
did not use one, per the brief.

## 3. Checks

- **Build:** `lake build Solution` green on the HEAD snapshot after INT-10 (`logs/S-I/build-last.log`).
  An earlier pass was green on `a5fbd69` and `7292eab`.
- **Axioms** (`logs/S-I/axioms.log`, `ax/AxSI.lean`): `certified`, `complete_rev4`, `delta_rev4`,
  `certificate_sub4`, `certificateR_sub4`, `boundsOK_claim`, `not_boundsOK_qV`, `V4F_eq`, `epsRQ_eq`,
  `sub4_ctrl`, `sub4_numbers`. All use only `propext`, `Classical.choice`, `Quot.sound`.
- **Source rule** (`logs/org20/scripts/source-rule.py`, on HEAD + mine): 318 files, 0 findings.
  `probe/si-bench`: 1 file, 0 findings.
- **Sequential profiles** (`logs/S-I/prof-*.log`, earlier layout): each module about 4 s of import
  and under 20 ms of elaboration and kernel time.
- **Local badge** (`logs/fr-build-SI/badge.sh`, rendered as `build_badge` renders it, 4 cores):
  `verify` builds.
  - HEAD `cd195c5` prover (`9b4e7690`): N8, N4, N2 accepted (196 / 200 / 194 ms on the VM), canaries
    rejected (`logs/S-I/local-stream/`).
  - HEAD `48d25ef` prover (`a3db3bb5`, with the handshake): N8 and N2 accepted (213 / 232 ms),
    canaries rejected (`logs/S-I/local-stream-head/`).

## 4. Controls

| Definition | (+) | (−) |
|---|---|---|
| `sub4` / `V4F` | `sub4_ctrl`: a one-step leaf's witness-sending proof is accepted with no query; `V4F_eq` | `sub4_ctrl`: a node byte with the wrong size is rejected with no query |
| `epsRQ`, `δ` | `epsRQ_eq`, `sub4_numbers` (`δ = 0`) | `sub4_numbers` (`0 < ε`) |
| `boundsOK` | `boundsOK_claim` | `not_boundsOK_qV` (a declared `qV` of 35999 fails) |
| `Open4` | consumed by `certificate_sub4` | none: it is unsatisfiable today (below) |

**`Open4` is unsatisfiable as it stands** whenever an accepted node proof lies in the extractor's
domain. `ndNone` extracts nothing from a node (`not_nodeDec4_ndNone`). It states what is missing; it
does not claim that the missing part holds. S-H4's `nd` replaces `ndNone` in `sub4.E`, `sub4.ext`
and `Open4`.

## 5. Item 5: the harness runs

Every run used core `6d05d00`, called through `eval-push.yml`, re-pinned **on the eval branch only**
(HEAD's file still names `15dac52`). Each commit was built from HEAD's tree plus S-I's files in a
temporary index. Artifacts are in `logs/S-I/run-<id>/`.

| run | Solution | prover.s | shape | cert CPU | result |
|---|---|---|---|---|---|
| [40805207819](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40805207819) | entry (254 modules) | `9b4e7690` (HEAD `cd195c5`) | smoke | EPYC 7763 | **REJECT: build_s 600 s.** Benchmark skipped. |
| [40806587168](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40806587168) | entry | `57972b94` (P2⁶ snapshot) | smoke | Xeon 8573C | **REJECT: build_s 600 s.** Benchmark skipped. |
| [40809817729](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40809817729) | bench probe (132) | `a3db3bb5` (HEAD `48d25ef`) | smoke | cert EPYC 9V74, bench Xeon 8573C | **PROVISIONAL**, benchmark pass, M = 7 |
| [40809858010](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40809858010) | bench probe | `a3db3bb5` | **season** | cert EPYC 9V45, bench **EPYC 7763** | **PROVISIONAL**, benchmark pass, **truncated**, M = 63 |
| [40810876665](https://github.com/scaraven/recursion.fast-submissions/actions/runs/40810876665) (probe) | entry (307 modules, HEAD `ba40eda`) | — | `evaluate.py cert`, caps raised | EPYC 7763 | provisional: build 882.2 s, comparator 45.0 s, gate 11.6 s PASS, badge 58.7 s |

### 5.1 The certificate job

| step | entry Solution, 7763 (probe) | bench probe, 9V74 / 9V45 |
|---|---|---|
| `build_s` (cap 600) | **882.2 s** (1.47× over); over 600 on the 8573C as well | 259.4 / 234.7 s |
| comparator (`kernel_s`, cap 600) | 45.0 s, peak 1.66 GB. **The kernel did not run**: the comparator stops at the statement mismatch | 22.4 / 20.5 s, peak 1.21 GB |
| `gate_s` (cap 120) | 11.6 s, **PASS** (rules 1–8; rule 4 "compiled code") | 5.5 / 4.9 s, PASS |
| `badge_s` (cap 180) | **58.7 s** | 33.4 / 29.7 s |

**What the build needs.** The 307 modules sum to 2,975 CPU-s on the 7763
(`logs/S-I/build-modules.txt`): `FRSoundness*` 1,088, `FRX*` 850, `FRVIR*` 408. At the observed
parallelism (2,975 / 882 ≈ 3.4), fitting 600 s needs ≤ 2,020 CPU-s, a 32 % cut. A 1.3× margin needs
≤ 1,550 CPU-s, a 48 % cut. The top modules are `FRXBary` 69, `FRXMsg` 54, `FRXAgree` 53, `FRXOut` 47,
`FRXRead` 46, `FRXFwd` 46, `FRXBfly` 43, `FRXFlag` 39, `FRVIRSpec` 38, `FRXField` 34.

### 5.2 The benchmark, season shape (run 40809858010, EPYC 7763; `logs/S-I/run-40809858010/summary.txt`)

- **The stream.**
  - `M_drawn = 64`; 63 steps completed before `stream_s = 960`, so the run is **truncated**. The
    re-timing and canaries did not run.
  - `sum_n = 20,873,635`.
  - Every output was accepted by the badge.
  - `ready` came 0.73–0.77 s after start. Kill took ≤ 0.066 s.
- **Per step.**
  - `P_i` is 8.44–28.96 s, mean 12.36 s. The fit is `P ≈ 1.859e-5 · n + 5.53 s`.
  - Per octave, P̄ is: 2^17: 7.66, 2^18: 5.20, 2^19: 4.98.
  - The slowest step is n = 1,034,098 at 28.96 s.
- **Verifier and size.** `V_i` is 143.6–162.4 ms, mean 157.9 ms. `|π| = 798,192` B, and the file is
  2,285,735 B. The largest `x` is 1.167 (verifier 0.786, size 0.381).
- **Memory.** The prover's peak is 6.52–6.67 GB.
- **Score.** **S = 6.421**, P̄ = 6.020, V̄ = 0.400. Calibration: `c_P = 1.710` (raw, provisional
  reference), `T_triv = 2,065.7 ms`, `v_ref = 206.6 ms`.
- **DoS.** 100 inputs, 0 accepted, max 33.5 ms against the item cap of 2,065.7 ms.
- **Service.** 370.6 M queries, 128 signatures, 0 refusals.

Smoke (run 40809817729, Xeon 8573C): M = 7, all accepted. `P_i` was 4.66–9.02 s; step 1 was re-timed
(ratio 1.94). `V_i` was 124.7–135.1 ms. DoS: 64 inputs, 0 accepted. No truncation.

### 5.3 Every cap against its measured value

| cap (season file) | value | measured | run | margin |
|---|---|---|---|---|
| `[certificate] build_s` | 600 s | entry **882.2 s** (7763); bench probe 259.4 / 234.7 s | probe 40810876665; 40809817729 / 40809858010 | **0.68×**; 2.3–2.6× |
| `[certificate] kernel_s` | 600 s | 45.0 s entry, 22.4 s bench; **kernel not run** (statement mismatch) | same | n/a until `certified` closes (H-cert: about 370 s on the 7763 for FR's core) |
| `[certificate] gate_s` | 120 s | 11.6 s entry, 5.5 s bench | same | 10× |
| `[certificate] badge_s` | 180 s | **58.7 s** entry (7763), 33.4 s bench | same | 3.1× |
| `[stream] ready_s` | 10 s | 0.73–0.77 s | 40809858010 | 13× |
| `[stream] step_s` | 60 s | max 28.96 s (n = 1,034,098) | 40809858010 | 2.07× |
| `[stream] stream_s` | 960 s | reached at step 63 of 64 drawn: **truncated** | 40809858010 | — |
| `v_ref` (`T_triv/10`) | 206.6 ms | V max 162.4 ms, mean 157.9 ms | 40809858010 | 1.27× |
| `[caps] verify_s` | 10 s | 162.4 ms | 40809858010 | 62× |
| `[dos] item cap` | 2,065.7 ms | max 33.5 ms | 40809858010 | 62× |
| `[memory] prover` | 11G | 6.67 GB | 40809858010 | 1.65× |
| `[caps] file_cap` | 64 MiB | 2,285,735 B | 40809858010 | 29× |
| `[caps] work_cap` | 4 GiB | 4.59 MB | 40809858010 | — |
| `[caps] build_s` (prover) | 120 s | not recorded by the harness; P2: 0.54 s link on the 7763 | — | — |
| `[caps] setup_s` | 240 s | 0.02 s (no setup) | 40809817729 | — |

## 6. Findings and deviations

- **F1. `build_s` blocks the entry's own Solution on every runner tier seen.** It took 882 s on the
  7763 and was over 600 s on the 8573C. That is a REJECT, not PROVISIONAL, so the entry gets no
  benchmark. §5.1 gives the cut needed. Options, as H-cert listed them: golf the top modules, move
  controls out of the closure (no `*Ctrl` module is in Solution's closure today), or ask the core
  for a larger `build_s`.
- **F2. HEAD's Lean and HEAD's `prover.s` were inconsistent between `ef18e75` (S-E12f) and `48d25ef`
  (P2⁶).** The rebuilt badge rejected 5/5 honest node proofs made from the INT-9 blob. P2⁶'s reload
  of S-E12f's dump restored agreement. This is worth a standing check: whenever the node programs
  change, the integration should run the badge on a fresh stream.
- **F3. HEAD `cd195c5`'s prover had no `ready`/`go`/`done` handshake**, so run 40805207819 would have
  failed at step 1 even with a passing certificate. Fixed in `48d25ef`.
- **F4. The season run is truncated** at M = 63 of 64. The mean step is 12.4 s (P2⁶ predicts M ≤ 66
  fits). A truncated run is never ranked, whatever the certificate.
- **F5. The kernel step is unmeasured** for any provisional Solution. A statement mismatch (and a
  `sorry`) stops the comparator before the replay. `certified` must close first; H-cert's proxy is
  the only figure (about 370 s on the 7763).
- **D1. `eval-push.yml` is re-pinned to `6d05d00` on eval branches only.** HEAD's file still names
  `15dac52`, the old core. It should be re-pinned when it is next committed.
- **D2. The stream measurements are from the bench probe Solution, not the entry's.** Its `acc` is
  the entry's (the same `V4F`, `qV`). Only `E`/`ext`/`fuel`, which the benchmark never runs, differ.
- **D3.** `Open4` targets INT-10's `Resid4H` (`slots`, `links`), as the coordinator asked. S-N2's
  `ks_rev4GH`, which discharges part of `slots`, was not used.
- **D4. Setup cache.** Each new eval branch rebuilt the organiser's environment (about 13.5 min):
  GitHub caches are branch-scoped.

## 7. Open questions

1. `build_s`: golf the build (≥ 32 %), or ask the core for a larger cap? The certificate job's other
   steps total about 115 s on the 7763 without the kernel, and about 485 s with H-cert's kernel figure.
2. Should `Solution` import the control modules (AGENTS.md: the harness builds only Solution's
   closure)? Today none is imported, and doing so would add build time.
3. Once S-H4's `nd` lands, `sub4.E`/`ext` and `Open4` change in one place (`FRSubmission4`,
   `FRSubmission4Cert`).

## Files to commit

- `submissions/flock-recursive/lean/FRSubmission4V.lean`, `FRSubmission4.lean`,
  `FRSubmission4Cert.lean`, `Solution.lean` (new)
- `submissions/flock-recursive/claim.json` (`qV` 36000)
- `probe/si-bench/Solution.lean`, `probe/si-cert/run.sh` (new)
- `docs/v4/flock-recursive/stages/S-I-JOURNAL.md`, `S-I-RESULT.md`
- Add `import FRSubmission4Cert` to `FR.lean` if FR should cover it (not edited).
- Not committed by S-I: `.github/eval.conf` and the `eval-push.yml` re-pin (eval branches only, D1).
