# Documentation index

> **v4 note (2026-10-27).** Apart from `v4/`, everything under `docs/` is a **v3-era reference
> copy**: the v3 design and its predecessors, the core's v2 handover and harness documents, the
> research, the v1.0 report and the v3 baseline brief. None of it is the design in force.
>
> - **The v4 design** lives in the core: `.contract/docs/DESIGN-v4-srom.md`, at the pin `8ad98e9`
>   (branch `v4/ks-standard`, with the amendments V4-A9 and V4-A10). Its brief, design attack and
>   stage records are under `.contract/docs/v4/`, and the contract is
>   `.contract/RecursionFast/Contract/`.
> - **`v4/flock-baseline/`** is written here: the blueprint, stage records and reviews of the v4
>   baseline entry `spartan-srom`.
> - **For v4, start at `../AGENTS.md`.** The reading order and the folder table below are v3's.

This folder holds everything an agent needs to work in this repository without the design
workspace: the v3 design and its predecessors, the core's handover and harness documentation, the
research behind the design, the v1.0 report, and the brief for the baseline entry. Everything here
except this file, `baseline/BASELINE-TASK.md` and `report/README.md` is a **read-only copy**. The
source is authoritative. To update a copy, re-copy it from its source with a new provenance line;
never edit it here.

## Read first, in this order, for the baseline task (stage S2)

1. `../AGENTS.md`: the rules a submitter reads, with every rule cited to the design.
2. `design/DESIGN-v3.md`: the design in force. Read §1, §2, §3, §4 and §6 fully, then §7.3–§7.7,
   §8 (trust statement), §11 (build order) and §12 (open items).
3. `baseline/BASELINE-TASK.md`: the brief for S2: what to build, the obligations, the build setup,
   the commands and the definition of done.
4. `baseline/v2-example/README.md`: the v2 baseline as a worked example of an entry. Read §3 (the
   objects field by field) and §4 (who checks what). Then its `scripts/check.sh`,
   `scripts/make-solution.py` and `prover/README.md`.
5. `core/core-CLAUDE.md`: the core's toolchain, commands, trust layers, hard rules and stage
   protocol. Then `core/harness-README.md`: the badge path, `scripts/harness.sh`, the source rule,
   the gate rules, the runner and the olean manifest.
6. The S1 contract itself: `.contract/RecursionFast/Contract/*.lean`, the core at the pinned
   commit (`15e4ae5`, v3). It is not copied here, because it is living code.

Background, as needed:

- `design/DESIGN-v2.md` §3.3 (submission contents, the source rule, the gate rules), §6.4
  (measurement policy and record rule) and §7.4 (the harness order). v3 keeps all of these.
- `core/RESULT.md`: v2's handover. What was proved, measured and tested, and how to run
  everything.
- `reference/neighbouring-competitions.md`: ots.golf, sig.golf, the Proximity Prize and
  leanerVM; what was taken from each, and §6, the questions to ask of any rule change.
- `design/DESIGN-AMENDMENTS.md`: the ledger behind every v2 finding and decision id (S1-A1 …
  S9-A44) that the designs and code comments cite.

## What each folder holds

| Folder | Contents | Source |
|---|---|---|
| `design/` | `DESIGN-v3.md` (**authoritative**, v3, 2026-10-19); `DESIGN-v2.md` (superseded; removed from the core's `main` in its pull request #3 and archived at the core's tag `v2-archive`; the harness, gate and baseline details v3 keeps); `DESIGN-v0.3.md` (the consolidated v0.3 design behind the report); `DISCUSSION.md` (the user's decisions Q1–Q6); `DESIGN-AMENDMENTS.md` (the core's v2 amendments ledger); `PLAN.md` (the workspace plan and decisions log of 2026-10-10); `recursion-fast-idea-prompt.md` (the original brief); `recursion-fast-idea-diagram.jpg` (the user's hand-drawn sketch of the v3 shape, file dated 2026-10-15) | core `main` at the pin (`DESIGN-v3.md`), core `v2-archive` (`DESIGN-v2.md`, `DESIGN-AMENDMENTS.md`), workspace (the rest) |
| `core/` | `RESULT.md` (the v2 handover); `harness-README.md` (the core's `harness/README.md`); `core-CLAUDE.md` (the core's `CLAUDE.md`); `import-allowlist.txt` (gate rule 6's allowlist, 10,820 modules); `lakefile.toml`, `lean-toolchain`, `tools.env`, `setup-clean.sh` (the pins and the set-up); `stages/` (the v2 stage RESULTs, S1–S8); `reviews/` (the v2 reviews, golf and simplify reports, S1–S9) | core `main` at `77e550b`, which is now the core's tag `v2-archive` (v2 reference material; `tools.env`, `setup-clean.sh` and the allowlist no longer exist in the core); `core-CLAUDE.md` and `lakefile.toml` from the pin `15e4ae5` |
| `reference/` | `neighbouring-competitions.md` and `notes/` (R1 ots.golf, R2 sig.golf, R3 Proximity Prize, R5 leanerVM) | core `v3/s1-contract` at `5ad2115` |
| `research/` | `notes/` (R1–R8: ots.golf, sig.golf, Proximity Prize, ArkLib, leanerVM, RISC-V, the literature, binary fields in Lean); `reviews/` (A1–A8: incentives, definitions, feasibility, the v0.2 and v0.3 contracts, and three report reviews) | workspace `notes/`, `reviews/` |
| `report/` | the v1.0 report: the PDF, its LaTeX sources and a README that says which sections are still accurate | workspace `report/` |
| `baseline/` | `BASELINE-TASK.md` (the S2 brief, written here); `v2-example/` (the core's v2 baseline `submissions/baseline/`, complete: README, `claim.json`, `RecursionFastCandidate` sources, `scripts/`, `extractor/`, `audit/`, `prover/README.md`) | written here; core `main` at `77e550b` |

**Stage names.** `core/stages/` and `core/reviews/` are **v2's** stages S1–S9: the relation,
BLAKE2s, the compiled argument, the extractor, recursion, the chain layout, the harness, the
baseline, Clean and the whole-repository reviews. v3's stages (S1 contract, S2 baseline, S3
harness, …; design §11) are different. Their records are named `V3-S<n>-…`. The in-progress S1
uses `docs/stages/V3-S1-RESULT.md` in the core, and S2's go in this repository's `docs/stages/`
and `docs/reviews/`.

**Duplicates.** `reference/notes/R{1,2,3,5}` and `research/notes/R{1,2,3,5}` have the same body.
The core's copies carry one extra header line of their own. Both are kept so that `reference/`
mirrors the core and `research/` mirrors the workspace.

## Provenance

Every copied file has a one-line provenance header naming its source, branch and commit, or the
workspace path, and the date, 2026-10-19, where the format allows a comment:

- Markdown: an HTML comment on line 1.
- Lean: a `--` line.
- TeX and BibTeX: a `%` line.
- Shell, Python, TOML, `.env`, assembly and disassembly: a `#` line, after the shebang where
  there is one.

Files whose format allows no comment, or whose text must stay verbatim, are copied unchanged. Their
provenance is listed here:

| File | Source |
|---|---|
| `../LICENSE` | core `main:LICENSE` at `77e550b` (Apache License 2.0), verbatim |
| `design/recursion-fast-idea-diagram.jpg` | workspace `recursion-fast-idea-diagram.jpg` |
| `core/import-allowlist.txt` | core `main:scripts/import-allowlist.txt` at `77e550b` (read by the gate; a comment line would read as a module) |
| `core/lean-toolchain` | core `main:lean-toolchain` at `77e550b` (`leanprover/lean4:v4.34.1`) |
| `report/recursion-fast-blueprint-v1.0.pdf` | workspace `report/build-orch/recursion-fast-blueprint.pdf`, sha256 `6f6e4f2d…a9e153`, 162 pages (`report/README.md`) |
| `baseline/v2-example/claim.json` | core `main:submissions/baseline/claim.json` at `77e550b` |
| `baseline/v2-example/audit/comparator.json`, `audit/comparator-nanoda.json` | core `main:submissions/baseline/audit/` at `77e550b` |
| `baseline/v2-example/extractor/extractor.bin`, `extractor/extractor.data` | core `main:submissions/baseline/extractor/` at `77e550b` (binary; `extractor.data` is empty) |

Here, "core" is https://github.com/scaraven/recursion.fast (local checkout
`/home/devops/Verified-zkEVM/recursion.fast`), and "workspace" is the design workspace
`/home/devops/CambridgePQ/recursion.fast`.

**Not copied:**

- From the workspace: `design/D1–D4` (the v0.3 design proposals that the A-reviews cite),
  `probes/`, `contract-v03/`, `contract/`, `submissions/` and the report's `scripts/` and `build-*`
  directories.
- From the core: `docs/upstream/clean-char2-balance.md`, `harness/CHAIN-LAYOUT.md`,
  `harness/reference-machine.md` and every source file.

Read them at their sources.
