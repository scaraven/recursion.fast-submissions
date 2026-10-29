# S-I journal (certificate assembly, harness dry run)

Base: HEAD `cd195c5`, then `a5fbd69` (P4f, coordinator's message: use `ks_rev4F`/`certificate_rev4F`).
Build tree `logs/fr-build-SI` (copy of `fr-build-X4`; `MINE.txt` = `FRSubmission4 FRSubmission4Cert
Solution`; `b.sh` logs to `logs/S-I/`). Every lake/lean command in a 16G (12G for one file) scope with
a timeout. No sub-agents, nothing committed.

## 2026-10-29

- Read TRACK-RULES, X4-RESULT, the contract at `6d05d00` (`Certificate`, `Security`), the challenge
  stub, the badge templates, `evaluate.py`, `evaluate.yml`, the gate, the source rule, the comparator
  (`d03acab`), `season.toml`/`smoke.toml`, `eval-push.yml`, H-cert and H-V RESULTs, P2-RESULT §17.
- **Harness facts that shape the Solution.**
  - The source rule does **not** reject `sorry` (no such word in `BANNED`); gate rule 1 reports
    `sorryAx` and `evaluate.py` treats exactly that, and a comparator rejection, as `provisional`.
    The brief says no `sorry`, so I use the other provisional route: `certified` takes the open
    residuals as a hypothesis. Its statement then differs from the challenge's: the comparator's
    `compareAt` throws after "Building Solution" (so not a HarnessError), the run is `rejected` →
    `provisional_reasons`; the gate sees no `sorryAx` (rule 1 passes) and the badge builds;
    status `provisional` → `evaluate.yml`'s benchmark job runs (`status == 'ok' || 'provisional'`).
  - Consequence: the comparator stops at `compareAt`, so **the kernel replay is not run** and
    `comparator_s` is only the two builds and exports (the same holds for a `sorry`, which fails
    `checkAxioms` before the kernel).
  - The badge compiles the whole `submission`: `ε` must have compiled code (AGENTS.md "A stable ε")
    → `epsRQ := ((15/2^124 : ℚ≥0) : ℝ≥0)`, `epsRQ_eq : epsRQ = epsR`.
  - `eval-push.yml` at HEAD still calls `evaluate.yml@15dac52`; the eval branch's commit pins it to
    `6d05d00` (PR #20 head, `v4/ivc-score`). Only on the eval branch.
- **Item 1.** `complete4` is the contract's `CompleteWithError … 0` for `V4with Vseg Vnode`, `qV4` and
  `P = ret ∘ encodeF`, every key. `Certificate.complete` asks the same of `S.P`, `S.V`, `S.δ`: enough.
  `complete_rev4`, `delta_rev4` (no hypotheses).
- **Item 2.** `FRSubmission4`: closed per-kind constants for programs and ops (`progS30` … `implNN8`),
  `V4F := V4with VsegF VnodeF`, `V4F_eq : V4F = VC4 implB (implN4F fun _ => implB) cells4` (per-kind
  `rfl`). `sub0` (E := none) then `sub4 := {sub0 with E := E4X ndNone sub0.acc}`; `sub4_acc` is `rfl`.
- **Item 3.** `FRSubmission4Cert`: `Open4` (∃ `D : NodeDec4 ndNone`, ∀ vk `Resid4 …` at P4f's `DFhi`),
  `certificate_sub4` via `certificate_rev4F`, `boundsOK`, `certificateR_sub4`, `boundsOK_claim`,
  `not_boundsOK_qV`. `Solution.lean`: the rendered stub verbatim, `submission := sub4`,
  `certified (h : Open4)`.
- **Item 4.** `claim.json`: `qV` 10240 → 36000 (`qV4`); error `15/2^124` (= `epsR`), δ `0`,
  `fuel_base = 3·2^46`, `fuel_per_word = 2^13` already matched `X.fuel`. Rendered: `logs/S-I/Challenge.lean`.
- Builds: `FRSubmission4` green (one fix: `zero_le` is not a function here); `Solution` green
  (`logs/S-I/build-last.log`). Axioms (`logs/S-I/axioms.log`): 11 names, standard three only.
  Source rule on HEAD + mine: 317 files, 0 findings (`logs/S-I/source-rule.log`).
- **Local badge.** `badge.sh` renders `RFBadgeCommon`/`RFBadgeVerify` around `Solution` as
  `build_badge` does and builds `verify` on 4 cores: 114 s wall (`logs/S-I/badge-build.log`; many FR
  objects were already in the copied tree, so an underestimate).
- **Local stream** (HEAD's `prover.s`, sha `9b4e7690…`, linked with the runner's command; P2⁵'s
  `stream.sh` keeping its outputs; `rf-oracle` of `logs/org20`): N8, N4, N2 produced; **the Lean
  badge accepts all three (196 / 200 / 194 ms) and rejects the three statement-bit canaries**
  (`logs/S-I/local-stream/`). Process start of `verify` ≈ 6.3 s (the closed plans), outside `NS`.
- Pushed `eval/si-smoke-1` (commit `2b39afb`, temp index, smoke shape, SPLIT=false): run 40805207819.
- **Run 40805207819** (smoke, entry Solution, HEAD `cd195c5`+P4f, prover.s HEAD `9b4e7690`): setup cold
  13.5 min; certificate on **EPYC 7763: REJECT, "did not build within build_s = 600 s"**; benchmark
  skipped. The handshake would have failed anyway: HEAD's `first`/`step` printed no `ready` (P2⁶ was
  adding it, uncommitted).
- Local: P2⁶'s uncommitted `prover.s` (`57972b94`) with the handshake, driven by `hs.py`
  (ready → inputs → go → done): N8 and N2 accepted by the badge, canaries rejected
  (`logs/S-I/local-stream-p26/`).
- **Run 40806587168** (smoke, entry Solution, P2⁶ snapshot): certificate on **Xeon 8573C (the fast
  tier): REJECT at build_s = 600 s** too. The entry Solution's closure (254 modules then, 306 after
  R4i) cannot build in 600 s on any runner tier seen.
- Coordinator: P4f (residual 1) and then R4i (`certificate_rev4G`, `Resid4G` with `SegOut4`) landed.
  `FRSubmission4Cert` now uses `certificate_rev4G` at `fin := finC finPf`, `lRows := Layout.lRows`,
  `κs₀ := 0` (`implB` is it by `rfl`). Rebuilt green; axioms unchanged (standard three).
- Split `FRSubmission4V` (V constants, `epsRQ`; 130-module closure) out of `FRSubmission4`.
  `probe/si-bench/Solution.lean`: a **benchmark probe** Solution (the entry's `V`, `P`, `ε`, `δ`, `qV`;
  the library's `E`/`ext`/`fuel`; `certified` assumes its statement), installed only on eval branches.
- **Finding: HEAD `7292eab`'s Lean (with S-E12f `ef18e75`) rejected every node proof of the INT-9-blob
  provers** (`9b4e7690`, `57972b94`): 5/5 honest outputs rejected by the rebuilt badge. P2⁶'s commit
  `48d25ef` (S-E12f's dump reloaded, handshake, prover.s `a3db3bb5`) is consistent again: N8, N2
  accepted (213 / 232 ms on the VM), canaries rejected (`logs/S-I/local-stream-head/`).
- Deleted `eval/si-smoke-1`, `eval/si-smoke-2`. Pushed `eval/si-bench-smoke-1` (`bcded01`, run
  40809817729) and `eval/si-bench-season-1` (`1ab8955`, run 40809858010), base HEAD `48d25ef`.
- Coordinator: INT-10 (`certificate_rev4H`, `Resid4H` without `SegOut4`). `Open4` now targets
  `Resid4H`; rebuilt green on the post-INT-10 snapshot; axioms unchanged.
- Run 40809817729 (bench probe, smoke): cert on EPYC 9V74 provisional (build 259.4, comparator 22.4
  "statement do not match", gate 5.5 PASS, badge 33.4); bench on Xeon 8573C pass, M = 7, all accepted.
- Run 40809858010 (bench probe, **season**): cert on 9V45 provisional (234.7 / 20.5 / 4.9 / 29.7);
  bench on **EPYC 7763**: pass, **truncated at M = 63 of 64**, S = 6.421 (P̄ 6.020, V̄ 0.400), V max
  162.4 ms vs v_ref 206.6, step max 28.96 s, peak 6.67 GB, DoS 0/100 accepted.
- Probe `probe/si-cert` (run 40810876665, EPYC 7763; the harness's `evaluate.py cert` with caps
  raised, entry Solution at HEAD `ba40eda`, 307 modules): build **882.2 s**, comparator 45.0 s, gate
  11.6 s PASS, badge 58.7 s; module CPU sum 2,975 s (`logs/S-I/build-modules.txt`).
- Deleted every branch pushed (`eval/si-smoke-1/2`, `eval/si-bench-smoke-1`, `eval/si-bench-season-1`,
  `probe/si-cert-1`). RESULT written.
