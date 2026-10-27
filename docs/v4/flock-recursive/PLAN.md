# Flock 1.0, recursive: plan of record

Branch `v4/flock-recursive` (worktree `recursion.fast-submissions-flock`), forked from
`v4/spartan-srom` at `f07d028`; `.contract` pinned at core PR #18's head `15dac52` (`747d7ae`).
Entry root: `submissions/flock-recursive/`. Orchestrator decisions are `FR-D<n>`; risks `FR-R<n>`.

## 1. Review of the task prompt

What the prompt gets right: the target (a certified, recursive, Flock-class entry with a native
prover), the reuse sources, the stage discipline, and the instruction to prove infeasibility rather
than search forever. What needed sharpening, and how each point is resolved in the user's absence:

| # | Issue in the prompt | Resolution |
|---|---|---|
| 1 | "recursion.fast: the current repository" — the working directory is the **submissions** repository; the rules are the core's (PR #18, stacked on #17). | Entry lives here; contract read from `.contract` at `15dac52`. |
| 2 | "Spartan + Ligerito over GF(2^192)" — the baseline (`spartan-srom`, submissions PR #2) is Spartan + **Ligero** (√-size, unique decoding) over GF(2^64) with GF(2^192) challenges. Ligero is exactly why it fails `proofCap` past `2^r·n = 4096`. | Flock's Ligerito (polylog) over GF(2^128) is a new PCS here, not a port. |
| 3 | "2^-120 unlocks Flock 1.0" is only partly true. `errorCap` bounds the **per-query** rise of the potential `μ` (a round-by-round/state-restoration bound), not the total. Over GF(2^128) that leaves ≈ 8 bits of slack per round: proximity-gap terms `n/|F|` with `n ≈ 2^20` (≈ 2^-108), univariate-skip and batching terms can exceed it. The paper's parameters are 100-bit and list-decoding (Johnson); list-decoding extraction would need a verified list decoder. | **FR-D3**: unique-decoding regime only; per-round errors ≤ 2^-120 using GF(2^256) challenges and/or grinding where GF(2^128) is short (Flock's own `Secure` 120-bit UD profile and its F256 MCA are the starting point). Every round's error is a kernel lemma. |
| 4 | "Pass the season shape" is undefined. Under PR #18 it means `HARNESS: ACCEPT` with `harness/season.toml`: root `acc` within `T_V ≈ 178 ms` (compiled Lean, one core, no `clmul`), proofs ≤ 1 MiB, `qV ≤ 2^16`, 11 GB prover, tree (64 leaves × 2^18 BLAKE2s steps) ≤ 600 s, ≈ 3.1 s per stream link, and a certificate whose Lean builds in ≤ 600 s and kernel-checks in ≤ 600 s on 4 vCPUs (badge ≤ 180 s). Only a GitHub runner gives the real verdict, and pushing is not authorised. | **FR-D2** (revised 2026-10-27: the user authorised pushing): done = `HARNESS: ACCEPT` from the real evaluation workflow on GitHub runners at the smoke and season shapes. VM numbers are for development only. If a cap is provably out of reach, the deliverable is the largest ACCEPTed shape plus the obstruction, stated as a theorem or a measured frontier, and a rules note. |
| 5 | Hardware: this VM's virtual CPU has **no PCLMULQDQ/VPCLMULQDQ/GFNI**; the runners (EPYC Zen4/Zen5) have all three. Flock's speed rests on carry-less multiply. | **FR-D5**: the prover dispatches on CPUID with a portable path for development; performance is measured on runners (a probe workflow on the runner image, and the evaluation workflow). |
| 6 | The contract is moving **today**: an uncommitted core change (V4-A10, 2026-10-27) replaces the potential-form `KS` by textbook single-output KS, keeping `KState` as an untrusted library route to it. | **FR-D0**: certify through `KState` (valid under both); re-pin when V4-A10 lands, in its own commit. |
| 7 | Missing scope, each a work package below: (a) node extraction is **decoding** (core issue #7): a step-counted, verified decoder within `fuel ≤ 2^48 + 2^16·t`; (b) the SROM node circuit is **not** Flock's Merkle-verifying tower: it hashes the child's trace (public BLAKE2s), checks one WOTS signature (≈ 300–500 compressions) and replays the child verifier's arithmetic; (c) the leaf hash is **BLAKE2s**, which Flock does not encode (it has BLAKE3/SHA-256; BLAKE3 shares BLAKE2s's G function); (d) the Lean budget: the baseline's 17.9k lines already took 9 min 51 s of kernel time; (e) imports: only Mathlib, the contract/library and CompPoly's BF64/Ext3 closure — leanerVM/ArkLib/Flock code is copied with provenance and licence; (f) the prover is one `prover.s` from std Rust (Flock depends on rayon etc.). | All in the work breakdown (§3). |
| 8 | "Flock 1.0" is not pinned to a version: the paper (2026-09-19) and the repository (`48f4bfe`: AG zerocheck, recursion tower, v22 proof format) differ. | **FR-D6**: the protocol is fixed in the blueprint; drift from the paper is a table in the blueprint and in the report. |
| 9 | No stop criteria. | Each risk below has a kill test; a failed kill test ends that route and is written up as an obstruction. |

## 2. Decisions

- **FR-D0** Target `15dac52`; prove `KS` via `KState`; re-pin for V4-A10 when merged. The user
  confirmed (2026-10-27): the potential form is stronger than V4-A10's textbook KS, so the changes
  will be small. Until then, assume `KS` stays as it is at the pin.
- **FR-D1** Isolation: all work on `v4/flock-recursive`; nothing in `main`'s worktree, the core
  clones, leanerVM or Flock is edited. Subagents do not commit; the orchestrator does.
- **FR-D2** Definition of done: §4.
- **FR-D3** Unique decoding; per-round error ≤ `2^-120`; grinding allowed (`δ ≤ 2^-40`).
- **FR-D4** Hashes: BLAKE2s R1CS for the chain, WOTS and trace digest (from `spartan-srom`'s
  leanerVM-derived circuit); commitments' Merkle and Fiat–Shamir hashes are oracle (service) calls.
- **FR-D5** Prover: std Rust → `prover.s`, CPUID dispatch, portable fallback; tuned on runners.
- **FR-D7** GitHub is the benchmark of record. `pull_request_target` reads its workflow from the
  default branch, which has none until guidance PR #1 is merged. So evaluations run through
  `.github/workflows/eval-push.yml`: a push to `eval/<entry>-<shape>-<pin>`, with
  `.github/eval.conf` naming the root, the season file and the split, calls the same pinned
  `evaluate.yml` (the same runners, jobs, caps and attestation; only the PR selection differs).
  Microbenchmarks run in a probe workflow on `probe/*` branches (`ubuntu-24.04`).

## 3. Work breakdown

Phase 0 (parallel): **T** theory and parameters (Fable); **I** reuse inventory (leanerVM's #12
stack, `spartan-srom`, CompPoly/ArkLib, the core library's machine tooling); **F** Flock digest
(recursion tower, `Secure` profile, kernels, BLAKE3→BLAKE2s); **M** measurements (certificate job
at the pin on 4 CPUs, compiled-Lean GF(2^128) arithmetic for `T_V`, Flock throughput on this VM).

Phase 1: **B** the blueprint (normative: formats, circuits, parameters, verifier branch by branch,
extractor, potential, certificate layout, budgets), then an adversarial review of it.

Phase 2 (parallel tracks, each staged implement → review ∥ golf → fix): **L-field** GF(2^128)
(+GF(2^256)), additive NTT/RS; **L-piop** zerocheck, lincheck, ring switching; **L-pcs** Ligerito UD
proximity and binding; **L-circ** BLAKE2s/WOTS/trace/verifier circuits with correctness theorems;
**L-ext** the decoding extractor and `Computes`; **L-cert** potential, `KS`, completeness,
controls; **P** the native prover (leaf, node, tree, stream); **H** harness runs.

Phase 3: whole-entry review, report for cryptographers, zkVM engineers and FV readers.

## 4. Definition of done (FR-D2)

1. `submissions/flock-recursive/`: `Certificate submission` at the pin, axioms `propext`,
   `Classical.choice`, `Quot.sound` only; nodes recursive (node proof size independent of subtree).
2. `prover.s` implementing `PROVER.md`'s modes.
3. `HARNESS: ACCEPT` at smoke and season shapes from the evaluation workflow on GitHub runners.
4. RESULTs, reviews, golf reports, fix passes; a report with a drift table against the paper.

## 5. Risks and kill tests

| Id | Risk | Kill test |
|---|---|---|
| FR-R1 | No UD binary-field PCS fits 1 MiB and `T_V` at node size | Phase 0 T sizing + M timing of a model verifier |
| FR-R2 | A per-round error of Flock cannot reach 2^-120 cheaply | T's per-round table |
| FR-R3 | Node extraction (decoding) cannot be proved within fuel | T's extractor design + I's machine tooling |
| FR-R4 | The certificate cannot be checked in 600 s on 4 CPUs | M's measurement of the baseline at the pin; a kernel-time budget per module |
| FR-R5 | The prover misses 600 s / 3.1 s per link / 11 GB | M on this VM (no clmul) + F's runner estimate |
| FR-R6 | The contract changes under us (V4-A10) | low: the user confirmed `KState` is stronger than V4-A10's KS; re-pin when it lands |
