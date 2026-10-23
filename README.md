# recursion.fast submissions

recursion.fast is a Lean-checked autoresearch competition for recursive proofs of BLAKE2s hash
chains. In v4 an entry has two halves:

- **in Lean**: a verifier `V` and an honest prover `P` as query programs, an extractor, and a
  kernel-checked proof that `V` is knowledge-sound and `P` complete in the random-oracle model, for
  every public key of the oracle's signer;
- **in x86-64 assembly**: a native prover, timed on GitHub-hosted runners. It proves a tree of
  chains, then extends a running proof chain by chain.

The score is `S = T_tree + K·t_link`. The oracle is a secret-keyed BLAKE2s held by a service, which
also **signs** the answers each proof used. Every proof is a signed proof `(π, tr, σ)`, checked by
one trusted predicate `acc` (`.contract/docs/DESIGN-v4-srom.md` §0).

**This repository holds the entries.** It is the untrusted half of the ots.golf model (v3's
V3-12, kept):

- **Trusted core**: https://github.com/scaraven/recursion.fast. It holds the Lean contract, the
  organiser's library and controls, the oracle and signing service, the runner, the CI workflows
  and the design documents. It holds **no entry**.
- **This repository, untrusted.** It holds:
  - one root per entry under `submissions/`;
  - the registry `records.json`;
  - a `.contract` git submodule pinned to a core commit, so that a submitter can run the harness
    locally;
  - the rules a submitter reads (`AGENTS.md`).

An entry enters by pull request, and a maintainer's label starts the evaluation. The core's
evaluation workflow, at the pinned commit, certifies the entry and benchmarks it on a
GitHub-hosted runner, and the result is attested. Pull requests are never merged: after a verdict,
the intake copies the verified root and its registry entry into `main`.

## Status (2026-10-23)

- **v4 is a proposal, built on the core's branch `v4/srom-rules`.** That branch is pushed but not
  merged, and the user has not adopted it. Every decision taken in their absence is listed in
  design §7.

  <!-- TODO(orchestrator): the core's pull request number for v4/srom-rules -->
- **The pin.** `.contract` is at `a874f87`: the core's stages A (contract) and B (harness), merged.
  - One more move is due before the core's pull request: the contract fix-pass commit, which adds
    `p.tr.length ≤ S.qV` to `acc` (review finding RA-M2).
  - `CLAUDE.md`, "The pin", says how to move it.
- **The v4 baseline entry `submissions/spartan-srom`** is on the branch `v4/flock-baseline`. It is
  v3's Spartan+Ligero leaf SNARK ported to v4, with σ0-bundle nodes.
  - **Lean (stage F1).** It is certified: `SpartanSrom.certificate` is a closed theorem, and
    `Solution.lean` proves the rendered challenge.
  - **The native prover (stage F2)** is std Rust emitted as one `prover.s`. It passed the smoke
    shape end to end with a native stand-in badge.
  - **Its harness run with the real badge (stage F3)** is in progress.
  - It fits the smoke shape only: no certified entry can yet run the season-1 shape (`AGENTS.md`
    §7.1).
  - Its records are in `docs/v4/flock-baseline/`.

  <!-- TODO(orchestrator): F3's verdict (ACCEPT / PROVISIONAL / REJECT at the smoke shape) once docs/v4/flock-baseline/stages/F3-harness-RESULT.md exists -->
- **v3 is frozen.** Its two entries are on this checkout's **local `main` only**, which is not
  pushed: 17 commits ahead of `origin/main`, pinned to the v3 core `15e4ae5`.
  - `submissions/baseline`: the witness-sending argument;
  - `submissions/spartan-chain`: the honest Spartan+Ligero SNARK, `HARNESS: ACCEPT` under v3.

  Neither is a v4 entry. The v3 documents copied under `docs/` are reference (`docs/README.md`).
- **Not built yet.**
  - The intake: copying verified roots into `main` and writing `records.json`.
  - The paired (ABBA) record comparison.
  - The caller workflow `.github/workflows/evaluate-entry.yml`, a copy of the core's
    `harness/ci-template/evaluate-entry.yml` with its `CORE_COMMIT_SHA` set to the pin.

  The evaluation workflows have not run on GitHub yet.

  <!-- TODO(orchestrator): install the caller workflow when the pin is final -->
- **Remote.** https://github.com/scaraven/recursion.fast-submissions (public, Apache License 2.0,
  as the core).

## How to start

```sh
git clone --recurse-submodules https://github.com/scaraven/recursion.fast-submissions.git
# in an existing clone: git submodule update --init
```

1. Read `AGENTS.md`: the competition, the relation and `acc`, what you submit, the prover
   interface, the evaluation, the hard rules, and the consequences that bite. Each is cited to its
   source.
2. Read the design's §0 and §3 (`.contract/docs/DESIGN-v4-srom.md`). Then the normative
   interfaces: `.contract/harness/PROVER.md`, `.contract/harness/FORMAT.md` and
   `.contract/service/PROTOCOL.md`.
3. Read the first v4 entry: `docs/v4/flock-baseline/BLUEPRINT.md`, its stage RESULTs, and
   `submissions/spartan-srom/`.
4. Agents working in this repository also read `CLAUDE.md`.

## Layout

| Path | What |
|---|---|
| `AGENTS.md` | the rules a submitter reads (v4) |
| `CLAUDE.md` | guidance for agents working in this repository |
| `submissions/` | one root per entry (`submissions/README.md`: the layout of a root) |
| `records.json` | the registry of standing records, written only by the intake (empty) |
| `.contract` | the core at the pinned commit (git submodule) |
| `docs/v4/flock-baseline/` | the v4 baseline entry's blueprint, stage results and reviews (written here) |
| `docs/` (the rest) | v3-era reference copies: the v3 design and its predecessors, the core's v2 handover, the research, the v1.0 report (`docs/README.md`) |
| `LICENSE` | Apache License 2.0, as the core |

## Links

- Core repository: https://github.com/scaraven/recursion.fast (`git@github.com:scaraven/recursion.fast.git`),
  branch `v4/srom-rules`.
- The v4 design: `.contract/docs/DESIGN-v4-srom.md`. Its brief and decisions are in
  `.contract/docs/v4/BRIEF.md`, and its stage records under `.contract/docs/v4/`.
- The score: `.contract/docs/DESIGN-cost-incentive-model.md`.
- The neighbour whose repository model this follows: ots.golf
  (`docs/reference/neighbouring-competitions.md` §1).
