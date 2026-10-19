# The v1.0 report: the blueprint as delivered on 2026-10-11

`recursion-fast-blueprint-v1.0.pdf` is the design study *recursion.fast: a blueprint for a
Lean-checked autoresearch competition on recursive SNARK verifier design*: v1.0, 162 pages, A4.

**Where it was copied from.** The design workspace's `report/build-orch/recursion-fast-blueprint.pdf`,
the newest build by modification time: 2026-10-11 16:34, with PDF creation date 2026-10-11 16:33:30
UTC. It is byte-identical to the workspace's `report/recursion-fast-blueprint.pdf` (sha256
`6f6e4f2d7c85fa9b7581a9c8f763985cbc8dc4ad40404fe1797c9b4107a9e153`). The newest numbered build,
`build-w10b` (2026-10-11 15:25), is older and differs: sections 06, 12 and C were edited at 16:32,
after it.

The LaTeX sources beside it are copies of the workspace's `report/` at the same date:
`recursion-fast-blueprint.tex`, `preamble.tex`, `refs.bib` and `sections/*.tex`. Build with
`latexmk -lualatex recursion-fast-blueprint.tex`, which needs LuaLaTeX, biber and the fonts STIX
Two Text and DejaVu Sans Mono. A rebuild from this copy was not tested. Lean listings use the
`leancode` environment (fancyvrb) of `preamble.tex`.

## What it describes, and what is still accurate

The report describes **contract v0.3**: an R1CS relation over `GF(2^64)`, a holographic IOP,
RISC-V verifier images with proved cycle counts under four zkVM cost profiles, and tracks T0, T1,
T2 and L1. The design workspace's `contract-v03/` implements that. v2
(`../design/DESIGN-v2.md`) and then v3 (`../design/DESIGN-v3.md`, in force) superseded most of
it. Rewriting the report for v3 is open item O-8, and the user's decision Q6
(`../design/DISCUSSION.md`) says sections 6–12 are to be rewritten and Appendix A regenerated
from the v3 contract.

| Section | File | Status for a v3 reader |
|---|---|---|
| Abstract, §1 Executive summary | `00-abstract.tex`, `01-summary.tex` | **superseded**: they summarise v0.3 |
| §2 Objectives and non-goals | `02-objectives.tex` | **partly superseded**. What is optimised changed: v3 scores whole-tree wall time on one machine (§6 of the v3 design), not cost profiles. The design principles and non-goals mostly still read true. |
| §3 Background | `03-background.tex` | **accurate** as background: IOPs and round-by-round knowledge soundness, BCS and Fiat–Shamir, proximity gaps, binary fields, verifier costs, recursion, aggregation and accumulation, Lean, VCVio and ArkLib. The R1CS and holography subsection is the background of v0.3's relation; v3 has no circuit relation and no field in the contract (V3-1, V3-7). |
| §4 Prior Lean-checked competitions | `04-prior-competitions.tex` | **accurate**. `../reference/neighbouring-competitions.md` condenses it with the v3 answer to each lesson. |
| §5 Critical review of the brief | `05-brief-review.tex` | **accurate as history**: the brief's gaps. Their resolutions are superseded. |
| §6 Architecture and trust model | `06-architecture.tex` | **superseded** by v3 §1.1, §7.6, §7.7 and §8 |
| §7 Protocol model and submission format | `07-protocol-model.tex` | **superseded** by v3 §3 |
| §8 Security definitions | `08-security.tex` | **superseded** by v3 §4. The round-by-round notion survives only as the background of the counting form over logs. |
| §9 Recursion and the batcher | `09-recursion.tex` | **superseded** by v3 §5 |
| §10 Cost function and incentives | `10-cost.tex` | **superseded** by v3 §6. There is no cost model; wall time is measured. The incentive reasoning is partly reused in v3 §6.7. |
| §11 Benchmark design and overfitting | `11-benchmark.tex` | **superseded** by v3 §7.1. The hash-chain leaf survives. |
| §12 Baseline and MVP | `12-baseline.tex` | **superseded** by v3 §7.3 and `../baseline/BASELINE-TASK.md` |
| §13 Threat model and attack catalogue | `13-threats.tex` | **accurate** in its adversary model and attack catalogue: agents as adversaries against the contract, the harness and the scoring. Its mitigations name v0.3 mechanisms. The current answers are v3 §6.7 (incentive table) and §8 (trust statement), and `../core/RESULT.md` §4–§5 for what v2 measured and tested. |
| §14 Issue register and roadmap | `14-issues-roadmap.tex` | **superseded** by v3 §12 and the roadmap issue https://github.com/scaraven/recursion.fast/issues/1 |
| Appendix A, Lean contract listings | `A-lean-contract.tex` | **superseded**: the v0.3 contract, generated from `contract-v03/` |
| Appendix B, Glossary | `B-glossary.tex` | **mostly useful**. The terms of v0.3's machinery (tracks, profiles, `Agrees`) are obsolete. |
| Appendix C, Reproducibility | `C-reproducibility.tex` | **superseded**: v0.3 commands |
