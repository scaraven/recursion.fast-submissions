# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

The **recursion.fast submissions repository**: the untrusted half of the competition (design
§7.7, V3-12). It holds one root per entry under `submissions/`, the registry `records.json`, the
rules a submitter reads (`AGENTS.md`) and the documentation an agent needs (`docs/`).

**This repository holds entries, never the contract. The contract is the `.contract` submodule**:
the trusted core, https://github.com/scaraven/recursion.fast, at a pinned commit. Never copy, edit
or shadow a contract, library, harness or challenge file here. A change to any of them is a pull
request to the core.

Read first: `docs/README.md`, then `docs/baseline/BASELINE-TASK.md`. `AGENTS.md` is the
submitter's rulebook.

## Where decisions live

- `docs/design/DESIGN-v3.md` is the **design in force**: decisions V3-1 … V3-12, the relation,
  the submission, the security definitions, scoring, the trusted base, the build order (§11) and
  the open items (§12). Where v3 is silent, v2's text applies (`docs/design/DESIGN-v2.md`). Where
  they differ, v3 wins.
- What the harness checks is the core's Lean contract at the pin. If the contract and the design
  disagree, report it. Do not code around it.
- `docs/design/DISCUSSION.md` holds the user's decisions (Q1–Q6).
- Finding and decision ids (V3-n, O-n, S<n>-A<k>, S9I-M1, …) are cross-referenced everywhere.
  Keep them when you quote.

## The pin

- `.contract` is pinned to the core's `main` at `77e550b` (v2).
- The v3 contract is on the core's branch `v3/s1-contract`. Stage S1 is in review and its pull
  request is pending. On 2026-10-19 the branch was local to `/home/devops/Verified-zkEVM/recursion.fast`
  and not yet on the remote.
- **When S1 lands, the pin moves to that commit,** in its own commit, before any v3 entry is
  certified. To move it before the branch is pushed:

  ```sh
  git -C .contract fetch /home/devops/Verified-zkEVM/recursion.fast v3/s1-contract
  git -C .contract checkout <commit> && git add .contract && git commit
  ```

- Never pin a commit that the core's remote does not have when this repository is pushed.
- Never commit changes inside `.contract`. Its working tree is the pinned commit plus gitignored
  build products (`ext/`, `.lake/`).

## The task in front of this repository: the baseline (stage S2)

The witness-sending argument, certified against S1, is the first entry here (design §7.3, §11 S2,
V3-9). `docs/baseline/BASELINE-TASK.md` has the construction, the certificate obligations, the
build setup, the commands, the traps and the definition of done. S2 also has a core-side half: a
separate pull request to the core, which follows the core's own `CLAUDE.md`
(`docs/core/core-CLAUDE.md`).

## Commands

Toolchain: Lean v4.34.1, Mathlib v4.34.1; CompPoly `572f997`, ArkLib `7653a90`, VCVio
`a4232d0`, PolyFun `41d3b21`; Clean `42fe4b26`. These are the core's pins.

```sh
git submodule update --init                                   # the core at the pin
cd .contract
scripts/setup-clean.sh /home/devops/Verified-zkEVM/recursion.fast/ext/Clean   # offline; no argument clones upstream
mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages
lake build                                                    # the core's default targets
scripts/org-build.sh .lake/org                                # the organiser package the harness needs
python3 -I scripts/olean-manifest.py check --org .lake/org scripts/olean-manifest.sha256
# the comparator and nanoda: COMPARATOR_HOME, COMPARATOR_NANODA (defaults and pins in scripts/tools.env)

# an entry (v2 shape; the v3 harness is stage S3):
python3 -I scripts/source-rule.py ../submissions/<root>
python3 -I scripts/render-challenge.py RecursionFast/Challenge/<STUB>.lean.in ../submissions/<root>/claim.json CHALLENGE.lean
scripts/harness.sh --org .lake/org --manifest scripts/olean-manifest.sha256 --work WORK \
  --gate RecursionFast.Challenge.certified --computable RecursionFast.Challenge.submission \
  CHALLENGE.lean SOLUTION_DIR COMPARATOR_CONFIG.json
submissions/<root>/check.sh                                   # the entry's own end-to-end check
```

- **The shared package tree is read-only.** It lives at
  `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages`, prebuilt. Never run
  `lake update` or `lake exe cache get` against it.
- **Logs.** Measurements go to `logs/` (gitignored) and are quoted in the stage RESULT.

## Stage protocol (copied from the core's `CLAUDE.md`)

Work here is built in stages (design §11), one at a time. Each stage runs the same cycle:

1. **Implement** (one agent). Build the stage and keep the build green. Write
   `docs/stages/V3-S<n>-RESULT.md` with:
   - what was built, file by file, with code line counts from the core's `scripts/loc.py`;
   - build and check times;
   - the controls, and what each shows;
   - every deviation from the design, with its reason;
   - open questions for the orchestrator.
2. **Adversarial review** (one agent, in parallel with 3): spec tightness, vacuity, loopholes,
   trust policy, hygiene. It writes `docs/reviews/V3-S<n>-review.md` with numbered findings
   (`V3-S<n>-M<i>` major: must fix; `V3-S<n>-m<i>` minor) and a verdict.
3. **Golf** (one agent, in parallel with 2): shortens proofs and definitions without changing any
   statement, editing in place. It writes `docs/reviews/V3-S<n>-golf.md`: before and after line
   counts, what changed, and what it declined to touch and why.
4. **Fix** (the implementing agent): applies every major finding, answers each minor one (fixed or
   argued), appends `## Fix pass` to the RESULT, and re-runs the build and the controls.
5. **Commit.** The orchestrator reads the RESULT and the review, commits, and opens the next stage.

Subagents **do not commit**; the orchestrator does. Skills to use:

- `lean-spec-authoring` when writing definitions or theorem statements;
- `adversarial-review` and `lean4:review` when reviewing;
- `lean4:golf` when golfing;
- `lean4:lean4` for any Lean work.

## Hard rules

For entries, these are checked by the harness: `AGENTS.md` §10–§11.

- **Axioms.** Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`.
- **No code-changing attributes:** `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`,
  `computed_field`.
- **No `unsafe`, `partial` or `opaque`.** No elaboration-time code (`#eval`, `run_cmd`, `elab`,
  `macro`, `initialize`, `import Lean`, …), which the source rule refuses, comments included.
- **Imports only from the core's allowlist**, plus the entry's own modules. CompPoly's `BF64` and
  `Ext3` are allowed (design §7.4). Clean is never on the badge path.
- **Badge-path fields** (`V`, `P`, `E`, `img`) have compiled code.
- **Statements are non-vacuous**, with a positive and a negative control for every definition an
  entry relies on. **A proof never changes the statement it proves.** An entry fills only the
  challenge's placeholders.
- **An entry pull request touches only its own root:** never `records.json`, `.contract`, `docs/`
  or another root.
- **Copies are read-only.** Files under `docs/` other than `docs/README.md`,
  `docs/baseline/BASELINE-TASK.md` and `docs/report/README.md` are copies. Re-copy from the
  source with a new provenance line; never edit them here.
- **Read-only references.** Never edit, build in or commit to
  `/home/devops/Verified-zkEVM/recursion.fast` (another agent may be working there; use `.contract`
  or a fresh clone) or the design workspace `/home/devops/CambridgePQ/recursion.fast`.
- **No pushing** and no creating remotes or GitHub repositories unless the user asks.

## No estimates

Describe work by what it consists of and what it depends on, never by how long it will take: no
person-weeks, no "a few hours". Durations that were **measured**, such as a build time or a
harness run, are facts. Quote them with their log.

## What "done" means

A stage is done when:

- its definition of done is met (for S2: `docs/baseline/BASELINE-TASK.md` §11);
- the build and the entry's `check.sh` are green;
- the harness prints `HARNESS: ACCEPT` for every entry the stage touched;
- the RESULT, the review and the golf report are written, and the fix pass is appended;
- the orchestrator has committed it.

A claim in a RESULT is a kernel-checked theorem or a measurement with a log under `logs/`.
Nothing else counts.
