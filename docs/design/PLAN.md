<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `PLAN.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# recursion.fast blueprint: working plan

Orchestrator-maintained. Every subagent reads this file first. Last updated: 2026-10-10.

## 0. Workspace map

| Path | Contents |
|---|---|
| `recursion-fast-idea-prompt.md` | original brief |
| `PLAN.md` | this file: critique of the brief, plan, task ledger, decisions log |
| `notes/` | research notes, one file per research task (`R*.md`) |
| `design/` | design proposals (`D*.md`) and the consolidated design (`DESIGN.md`) |
| `reviews/` | adversarial reviews (`A*.md`), each with a verdict and actionable items |
| `probes/` | Lean/LaTeX/emulator probes, each in its own subdirectory with a `RESULT.md` |
| `report/` | the final LaTeX report (`recursion-fast-blueprint.tex`, `refs.bib`) |

Reference checkouts (read-only for research; never push):

| Repo | Local path | Toolchain |
|---|---|---|
| leanerVM | `/home/devops/Verified-zkEVM/leanerVM` (built `.lake`: ArkLib 7653a90, VCVio a4232d0, CompPoly, Clean, mathlib) | v4.34.1 |
| ArkLib (HEAD db7005f, 2026-10-08) | `/home/devops/Verified-zkEVM/ArkLib` | v4.34.0 |
| riscv-zkvm (HEAD 6810fc1) | `/home/devops/Verified-zkEVM/riscv-zkvm` | v4.33.1 |
| ots.golf-dev (HEAD 8b140a9) | `/home/devops/leanEthereum/ots.golf-dev` | v4.33.1 |
| sig.golf-dev (HEAD eaa0c7f) | `/home/devops/Layr-Labs/sig.golf-dev` | v4.33.1 |
| proximity-prize (HEAD ed2b68c) | `/home/devops/proximity-prize/proximity-prize` | v4.32.2 |
| leanVM (Rust) | `/home/devops/leanEthereum/leanVM` | - |
| leanEthereum deps (VCVio, CompPoly, Clean, ...) | `/home/devops/leanEthereum/*` | - |

Machine: 32 cores, 62 GB RAM, sudo available. TeX Live installed via apt.

## 1. Critical review of the brief

The brief is strong on intent (auditable trusted base, large design space, RISC-V artifacts,
Lean proofs, anti-overfitting). The points below are gaps or ambiguities that the blueprint
must resolve explicitly; each is tracked as a decision (D-x) in section 4.

1. **What is optimized is ambiguous.** "As efficient as possible" can mean (a) final-layer
   verifier cost, (b) cost of one recursion step (the verifier as a circuit or as zkVM guest),
   (c) proof size, (d) prover time. The name "recursion.fast" suggests (b). The blueprint must
   pick a primary objective and treat the others as constraints or secondary tracks.
2. **The proposed score is dimensionally unclear.** "Divide performance by program size"
   rewards *larger* programs if performance means cycles; presumably the intent is
   cost × size or cycles + λ·size. Program size is also a weak proxy for anything users pay
   for; sig.golf uses `bytes × cycles` with a hard size cap instead.
3. **Succinctness for arbitrary R1CS needs preprocessing.** A verifier that reads the R1CS
   matrices pays Θ(nnz). Succinct verification for arbitrary (non-uniform) R1CS requires a
   holographic / indexed model (an indexer commits to the circuit; the verifier gets a
   verification key). The brief does not mention the indexer or verification key.
4. **Interactive "proof" vs argument.** Succinct interactive *proofs* for NP do not exist
   under standard assumptions; succinctness needs commitments (Merkle trees: BCS) or an
   oracle model (IOP). The model (IOP with query syscalls vs. argument in the ROM with a hash
   syscall vs. non-interactive Fiat-Shamir) must be fixed, and the gap to the deployed NARG
   documented. RBR knowledge soundness is exactly the property that makes the
   IOP → BCS → Fiat-Shamir path sound, which motivates the brief's choice.
5. **An honest prover in RISC-V is a large, possibly unnecessary, proof burden.**
   Completeness only requires *some* honest prover; it can be a Lean specification.
   A RISC-V prover proven complete would be a far larger proof than sig.golf's
   (≈154k lines of submission Lean for SPHINCS+). But *prover cost must still be
   constrained*, otherwise agents push code rate to zero (fewer queries, cheaper verifier,
   unbounded prover) or grind unboundedly. The brief has no prover budget.
6. **Knowledge soundness does not prevent hard-coding.** A verifier may special-case the
   benchmark's circuit or instances and remain (knowledge-)sound: the extractor is
   existential and can carry the benchmark witness. Anti-overfitting must come from the
   benchmark design (fresh/hidden instances, multiple circuit families, worst-case
   aggregation, size scaling), not from the security definition.
7. **The batcher definition (#1) states only completeness.** "If V accepts π1, π2 then V
   accepts π′" is a completeness property. The load-bearing property is soundness /
   knowledge soundness of the batched object: acceptance of π′ must imply knowledge of
   witnesses for *both* instances. Also unspecified: what the batcher sees (proofs only =
   aggregation; witnesses or prover state = batching/accumulation/folding), and how the
   inner verifier may differ from the final verifier (accumulation scheme: fold verifier +
   decider). leanerVM documents that recursive extraction from ROM-based inner proofs is an
   open problem; the blueprint must be honest about what the batcher theorem buys.
8. **Security parameters and model unspecified.** Field of the R1CS, target bits
   (e.g. 128 vs 100), proven vs conjectured proximity gaps (Lean proofs force proven
   regimes; up-to-capacity conjectures cannot be assumed and some have recently been
   challenged), classical vs quantum adversaries, zero-knowledge (out of scope?).
9. **Cost measurement.** "Median over millions of runs" is unnecessary when honest
   verification cost is data-independent; worst case over honest runs (proved, as in
   sig.golf, or measured by a trusted emulator) is cleaner and ungameable by
   prover-side choices. Wall-clock measurements are noisy; cycle counts under a
   trusted cost model are deterministic.
10. **Field arithmetic in RV64IM.** A pure RV64IM cost model makes the choice of field a
    first-class design dimension (31-bit primes, Goldilocks, binary towers need `clmul`).
    Whether to offer field/`clmul` precompiles changes which designs win. sig.golf's
    HASH precompile is a precedent.
11. **Toolchain / build feasibility.** ArkLib (v4.34.0) and riscv-zkvm (v4.33.1) are on
    different Lean toolchains; a single contract must pin one. Build and proof-check time
    budgets (brief: baseline < 1 hour) must be measured, not assumed.
12. **Trusted vs untrusted code boundaries.** Imports of ArkLib (which has `sorry`s in
    places), Lean-level attacks (native_decide, `implemented_by`, environment hacks), and
    the cost-measurement harness must be enumerated as in ots.golf/sig.golf.

## 2. Work plan

Phase A: grounding research (parallel, Opus subagents; outputs `notes/R*.md`)
- R1 ots.golf-dev: contract, tracks, cost models, verifier pipeline, AUDIT lessons.
- R2 sig.golf-dev: contract, RISC-V model, security game, submission proof architecture,
  proof size/time, verifier isolation.
- R3 proximity-prize: ArkLib-based contract, protected targets, benchmark pipeline.
- R4 ArkLib: reduction/IOP/oracle-verifier types, security definitions (completeness,
  soundness, KS, RBR soundness, RBR KS), composition, Fiat-Shamir/BCS, R1CS, sumcheck, FRI /
  WHIR / Spartan / Binius status (proven vs sorry), build time.
- R5 leanerVM: use of ArkLib/VCVio/CompPoly, master theorems, recursion/CTE open problem,
  spec-authoring and trust policy.
- R6 riscv-zkvm: semantics, executability/speed, cycle counting, symbolic-execution and proof
  tooling, how ots/sig golf consume it.
- R7 literature/deep research (web): hash-based SNARK verifiers & recursion costs, accumulation
  without homomorphism, RBR soundness / FS / BCS theory, proximity-gap status 2025-2026,
  formally verified SNARKs, autoresearch competitions.

Phase B: ideation (Fable 5.1, xhigh; outputs `design/D*.md`)
- D1 security definitions, protocol model, batcher/recursion formalization.
- D2 submission format, cost function, incentives, anti-overfitting, tracks.
Then the orchestrator consolidates into `design/DESIGN.md`.

Phase C: adversarial reviews of the design (Opus; outputs `reviews/A*.md`)
- A1 incentives & gaming of cost function / benchmark.
- A2 definitional soundness & auditability of the trusted base (vacuity, loopholes).
- A3 feasibility: proof burden, build and check times, toolchain.
Fix and iterate until clean.

Phase D: prototype & probes (Opus; outputs `probes/*/RESULT.md`)
- P1 toolchain/build probe: one Lean project with ArkLib + VCVio + riscv-zkvm (or alternative).
- P2 trusted contract skeleton in Lean (statements compile; sizes measured in lines).
- P3 MVP baseline: trivial NP verifier, its proofs, timing (< 1 hour target).
- P4 cost harness probe: emulator throughput, benchmark R1CS generation (hash chains).
Adversarial review of prototype (A4).

Phase E: report
- Write `report/recursion-fast-blueprint.tex` + `refs.bib`; compile; adversarial review of
  report (A5, A6: cryptographer lens, formal-methods lens); polish.

## 3. Task ledger

| ID | Status | Output |
|---|---|---|
| R1, R2, R4, R5, R6, R7 | done | notes/R*.md (+ probes/arklib-probe, riscv-probe, sig-golf-build) |
| R3 | done | notes/R3-proximity-prize.md |
| D1, D2 | done | design/D1-security.md, design/D2-cost-incentives.md; consolidated design/DESIGN.md (orchestrator) |
| A1–A3 | done | reviews/A*.md |
| R8, D3 | done (binary fields, U1/U2) | notes/R8-binary-fields-lean.md, design/D3-binary-fields.md |
| DESIGN v0.2 | done | design/DESIGN.md |
| P1 | done | probes/p1-contract-toolchain/RESULT.md |
| P2 contract v0.2 | done | contract/RESULT.md |
| A4 contract review r2 | done | reviews/A4-contract.md |
| D4 cost realism (U3) | done | design/D4-cost-realism.md |
| P3 baseline T1 certificate (v0.2) | done, re-checked by orchestrator 2026-10-11 | submissions/baseline/RESULT.md |
| P2b/P2c contract v0.3 | done (795 trusted code lines, CI 411 s) | contract-v03/RESULT.md |
| P3b baseline → v0.3 | running | submissions/baseline-v03/RESULT.md |
| A6 contract v0.3 review r3 | running | reviews/A6-contract-v03.md |
| W6 A5 fixes; W7 v0.3 sync + appendix A | W6 done; W7 running | report/sections |
| A5 report review (crypto lens) | done, applied by W6 | reviews/A5-report-crypto.md |
| P2–P4 | pending | probes/*/RESULT.md |
| Report | in progress: 03/04 (W1), 05 (orch.), 02/06/07/08 (W2), 09/10/11/13 (W3) | report/sections/*.tex |

## 4. Decisions log

See design/DESIGN.md §9 for the live decision table (O1–O7) and design/D1, D2 for rationale.

## 5. User inputs received mid-session (authoritative)

- 2026-10-10 U1: "the competition is enforced over binary fields, not prime fields". Consequence: the
  BabyBear decision (DESIGN O1) is void; tentative K = GF(2^64) (x^64+x^4+x^3+x+1), E = K[y]/(y^3+y+1)
  = GF(2^192) mirroring leanVM; Zbc added to the ISA. Tasks R8 (Lean binary-field support) and D3
  (binary-field cost recalibration) launched.
- 2026-10-10 U2 (optional suggestion): consider a worst-case cost bound over ACCEPTED runs, with a
  fast-failing path (early rejections not counted in the bound). Orchestrator intends to adopt it
  (cost clause over accepting runs + termination of all runs within a fuel cap); D3 analyses it.
- 2026-10-10 U3 (feedback): sig.golf's uniform per-instruction cost is inaccurate and agents overfit to
  it; wall-time or a more accurate RISC-V cost model is better; the model must account for parallelism
  and concurrency. Consequence: task D4 (cost realism, zkVM-calibrated weights vs timing model vs
  wall-time, fork-join work/span) launched; cost model v0.3 will replace DESIGN §7's uniform weights.

## 6. Status at delivery (2026-10-11)

- Report: `report/recursion-fast-blueprint.tex` (+ `sections/`, `preamble.tex`, `refs.bib`), PDF
  `report/recursion-fast-blueprint.pdf`, 162 pp., LuaLaTeX, no errors/undefined refs.
- Contract v0.3 (+ round-3 and round-4 fixes): `contract-v03/`, 796 trusted code lines; CI OK
  (independent re-run 687 s, `contract-v03/logs/orch-ci-r4.log`). v0.2 frozen in `contract/`.
- Baseline certified against v0.3 (T1 + Latency1): `submissions/baseline-v03/`, 1,920 proof lines;
  harness ACCEPT with Lean kernel + nanoda (independent re-run `logs/orch-recheck-r4.log`, 13 min 31 s).
- Reviews A1–A8 in `reviews/`; all findings applied or registered as open issues (§14 of the report:
  47 open, 15 P0).
