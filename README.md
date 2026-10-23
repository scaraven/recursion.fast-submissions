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

- **v4 is a proposal, built on the core's branch `v4/srom-rules`.** It is open as the core's pull
  request #17 (https://github.com/scaraven/recursion.fast/pull/17), not merged, and the user has not
  adopted it. Every decision taken in their absence is listed in design §6.1.
- **The pin.** `.contract` is at **`01a25b0`**, the head of that pull request, committed here as
  `a6ee05c`; the caller workflow was regenerated from its template in `4d2f282`. The core's CI is
  green on GitHub runners at that commit, the end-to-end smoke included (run 39966237935).
  - **The contract** (`RecursionFast/`) is unchanged since the contract fix pass `ea2e8ab`: `acc`
    checks `p.tr.length ≤ S.qV` right after the size cap (RA-M2); `Log` is an abbreviation for
    `Trace`; `wordBytes w := enc64 w.toNat`.
  - **The harness** carries stage B's fix pass `5b2b591` (B-RESULT §9) and its final fix pass
    (B-RESULT §10–§11):
    - CompPoly's field is an organiser root (Q2);
    - the gate tree builds only `Solution`'s closure (Q7);
    - the two kernels run separately (Q12);
    - failure reasons name their cause (Q13, Q14);
    - `T_V` is the best-of-N wall time of the pinned check (RB-M1);
    - the benchmark's parts follow one job plan (RF-M1);
    - the DoS column is bounded;
    - the reference toolchain, binutils 2.42 included, is part of the prover rule (RF-M2);
    - the comparator is built with the organiser's Lean.

  `CLAUDE.md`, "The pin", says how to move it.
- **The v4 baseline entry `submissions/spartan-srom`** is on the branch `v4/flock-baseline`. It is
  v3's Spartan+Ligero leaf SNARK ported to v4, with σ0-bundle nodes. Its own `README.md` and
  `NOTES.md` describe it; its records are in `docs/v4/flock-baseline/`.
  - **Lean (stage F1).** It is certified: `SpartanSrom.certificate` is a closed theorem, and
    `Solution.lean` proves the rendered challenge. Its fix pass (`745c7d8`) applied the review's
    findings, D-6, the pin's `acc` and the golf: 66 modules, 17,901 code lines.
  - **The native prover (stage F2)** is std Rust emitted as one `prover.s`. It was golfed (proofs
    byte-identical, leaves 2.6–4.5× faster) and fixed after its review.
  - **The harness runs.**
    - **F3**, the frozen commit `8111b71` against the core at `a874f87`
      (`docs/v4/flock-baseline/stages/F3-harness-RESULT.md`): smoke ACCEPT with two workarounds,
      both since fixed in the core (Q7, Q2).
    - **F4**, the fixed entry `745c7d8` against `81e1ebf` with no workaround
      (`stages/F4-final-harness-RESULT.md`): certificate ok in 9 min 52 s, **smoke ACCEPT** with
      `S` = 1.794 (from 6.666).
    - **The verdict at the pin**: ACCEPT at `81e1ebf`; confirmed at `01a25b0`: **ACCEPT** (F4b: certificate ok with the Lean kernel in 9 min 51 s; smoke bench of the submitted `prover.s` `733b3a30…`: T_tree 0.142 s, t_link 0.0846 s, S 1.835; `prover.s` assembles with GNU Binutils 2.42 without error or warning; `docs/v4/flock-baseline/stages/F4-final-harness-RESULT.md`, F4b)
    - At every pin, ACCEPT only where `2^r · n ≤ 4,096`: above that, every root is over `proofCap`.
    - **REJECT at the season shape** (F4): the tree because a 1,572,898-byte Fiat–Shamir query is
      above `queryCap`, the stream because its first leaf's `π` (2,791,559 B) is above `proofCap`.

    No certified entry can yet run the season-1 shape (`AGENTS.md` §7.1).
  - **The feedback report** on the v4 rules from this entry is
    `docs/v4/FLOCK-BASELINE-FEEDBACK.md`, revised after its review.
- **v3 is frozen.** Its two entries are on this checkout's **local `main` only**, which is not
  pushed: 17 commits ahead of `origin/main`, pinned to the v3 core `15e4ae5`.
  - `submissions/baseline`: the witness-sending argument;
  - `submissions/spartan-chain`: the honest Spartan+Ligero SNARK, `HARNESS: ACCEPT` under v3.

  Neither is a v4 entry. The v3 documents copied under `docs/` are reference (`docs/README.md`).
- **The caller workflow** `.github/workflows/evaluate-entry.yml` is installed on this branch. It is
  the core's `harness/ci-template/evaluate-entry.yml` at the pin, with both `CORE_COMMIT_SHA`
  placeholders set to it. Open: it has not run on GitHub, since this branch is not pushed.
- **Not built yet.**
  - The intake: copying verified roots into `main` and writing `records.json`.
  - The paired (ABBA) record comparison.
- **Remote.** https://github.com/scaraven/recursion.fast-submissions (public, Apache License 2.0,
  as the core). It holds `main` only.

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
3. Read the first v4 entry: `submissions/spartan-srom/README.md` and `NOTES.md`, then
   `docs/v4/flock-baseline/BLUEPRINT.md` and its stage RESULTs.
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
| `docs/v4/FLOCK-BASELINE-FEEDBACK.md` | the baseline team's report on the v4 rules (written here) |
| `.github/workflows/evaluate-entry.yml` | the caller of the core's evaluation workflow, pinned to the `.contract` commit |
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
