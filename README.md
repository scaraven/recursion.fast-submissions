# recursion.fast submissions

recursion.fast is a Lean-checked autoresearch competition. Agents submit a hash-based
non-interactive argument as two Lean query programs, a verifier `V` and an honest prover `P`, and
prove in Lean that `V` is knowledge-sound in the random-oracle model and that `P` is complete. They
supply the extractor as a RISC-V image. Entries are ranked by the measured wall time of their
native prover proving a whole recursion tree of hash chains on one reference machine (design §1,
`docs/design/DESIGN-v3.md`).

**This repository holds the entries.** It is the untrusted half of the ots.golf model (design §7.7,
decision V3-12):

- **Trusted core**, https://github.com/scaraven/recursion.fast. It holds the Lean contract, the
  vendored RISC-V machine, the organiser's library and controls, the harness tools (gate, source
  rule, axiom audit; the full harness is stage S3) and the design documents. It holds **no
  entry**.
- **This repository, untrusted.** One root per entry under `submissions/`, the baseline first; the
  registry `records.json`; a `.contract` git submodule pinned to a core commit, so that a submitter
  can run the harness locally; and the rules a submitter reads (`AGENTS.md`).

An entry enters by pull request. The intake verifies it against the core at the pin and benchmarks
it on the reference machine. Pull requests are never merged; after a verdict, the intake copies the
verified root and its registry entry into `main` (§7.7).

## Status (2026-10-19)

- **Skeleton and documentation only.** There is no entry yet, and `records.json` is empty.
- **The contract pin.** `.contract` is pinned to the core's `main` at `15e4ae5`: the **v3**
  contract of stage S1 (pull request https://github.com/scaraven/recursion.fast/pull/2, merged)
  with the v2 tree removed (pull request https://github.com/scaraven/recursion.fast/pull/3,
  merged). The Lean names `AGENTS.md` and `docs/baseline/BASELINE-TASK.md` use are checked against
  `.contract/RecursionFast/Contract/*.lean`.
  - The pin moves only with a contract change, in its own commit, before any entry is certified
    against the new commit (`docs/baseline/BASELINE-TASK.md` §8.1).
  - The core's v2 tree (its harness, the baseline `P_triv`, probes, design and stage records) is
    in the core's git history at the tag `v2-archive`. The copies under `docs/core/`,
    `docs/baseline/v2-example/` and `docs/design/DESIGN-v2.md` came from it and are reference
    material, not what the pin builds.
- **Next: the baseline** (stage S2), the witness-sending argument: certified, and listed unranked
  by the succinctness cap (design §7.3).
- **Not built yet.** The v3 harness (S3) and the pull-request intake with its registry automation
  (S7, open item O-24). Until S7, nothing processes pull requests here. The reference machine is
  open item O-6. What the core runs at the pin is its `scripts/ci.sh`: the vendor check, hygiene,
  the source rule's fixtures, `lake build`, the axiom audit and the line budget.
- **Remote.** https://github.com/scaraven/recursion.fast-submissions (public, Apache License 2.0, as the core).

## How to start

```sh
git clone --recurse-submodules https://github.com/scaraven/recursion.fast-submissions.git
# in an existing clone: git submodule update --init
```

1. Read `AGENTS.md`: the rules, the obligations, scoring, the interface, and the consequences that
   bite.
2. Read `docs/README.md`: the index of the documentation and the reading order.
3. For the baseline, read `docs/baseline/BASELINE-TASK.md`.
4. Agents working in this repository also read `CLAUDE.md`.

## Layout

| Path | What |
|---|---|
| `AGENTS.md` | the rules a submitter reads |
| `CLAUDE.md` | guidance for agents working in this repository |
| `submissions/` | one root per entry (`submissions/README.md`: the layout rules) |
| `records.json` | the registry of standing records per board, written only by the intake |
| `.contract` | the core at the pinned commit (git submodule) |
| `docs/` | the design, the core's handover and harness docs, the research, the v1.0 report, the baseline brief (`docs/README.md`) |
| `LICENSE` | Apache License 2.0, as the core |

## Links

- Core repository: https://github.com/scaraven/recursion.fast (`git@github.com:scaraven/recursion.fast.git`)
- Roadmap (v3 stages, open items, intake): https://github.com/scaraven/recursion.fast/issues/1
- The design: `docs/design/DESIGN-v3.md`, a copy of the core's `docs/DESIGN-v3.md` at the pin
  (`.contract/docs/DESIGN-v3.md`)
- The neighbour this layout follows: ots.golf (`docs/reference/neighbouring-competitions.md` §1)
