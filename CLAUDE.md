# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

The **recursion.fast submissions repository**: the untrusted half of the competition (the
ots.golf model, v3's V3-12, kept by v4). It holds:

- one root per entry under `submissions/`;
- the registry `records.json`;
- the rules a submitter reads (`AGENTS.md`);
- the records of the entries built here (`docs/v4/`).

The design in force for new work is **v4, the signed-random-oracle (SROM) rules**: a proposal on
the core's branch `v4/srom-rules` with the user's amendments V4-A9 (`v4/trim-fat`) and V4-A10
(`v4/ks-standard`), not yet adopted by the user. v3 is frozen.

**This repository holds entries, never the contract. The contract is the `.contract` submodule**:
the trusted core, https://github.com/scaraven/recursion.fast, at a pinned commit.

- Never copy, edit or shadow a contract, library, harness, service, challenge or workflow file of
  the core here.
- A change to any of them is a pull request to the core.

Read first: `AGENTS.md` (the rulebook), then `.contract/docs/DESIGN-v4-srom.md` §0, then the entry
you work on (for `spartan-srom`, `docs/v4/flock-baseline/BLUEPRINT.md`).

## Where decisions live

- **The contract at the pin is the rule**: `.contract/RecursionFast/Contract/*.lean`. Where the
  design and the Lean text differ, the Lean text is what the harness checks, and the difference is
  a bug in the design.
- **The normative interfaces**:
  - `.contract/harness/PROVER.md`: the prover's modes, files, sandbox and build;
  - `.contract/harness/FORMAT.md`: the signed-proof file;
  - `.contract/service/PROTOCOL.md`: the oracle service;
  - the season files `.contract/harness/season.toml` and `smoke.toml`.
- **The design**, `.contract/docs/DESIGN-v4-srom.md`: §6.1 lists every decision taken in the user's
  absence, and §6.2 the open items. The brief and its decisions and amendments, V4-1 … V4-16 and
  V4-A1 … A10, are in `.contract/docs/v4/BRIEF.md`. The design attack (C-Mn, C-mn), the contract review (RA-Mn), the
  harness review (RB-Mn, RB-mn) and the final whole-branch review (RF-Mn, RF-mn) are in
  `.contract/docs/v4/reviews/`, the stage RESULTs in
  `.contract/docs/v4/stages/`, and the orchestrator's fix queue in `.contract/docs/v4/FIXLIST.md`.
  Cite its items as "FIXLIST Qn" (Q1 … Q15): the user's decisions below are also numbered Q1–Q6.
- **The score**: `.contract/docs/DESIGN-cost-incentive-model.md` (CM-n, CM-Rn).
- **An entry's own decisions** are in its blueprint: for `spartan-srom`, the D-n of
  `docs/v4/flock-baseline/BLUEPRINT.md`. Where a blueprint and the contract disagree, the contract
  wins and the disagreement is reported.
- **The user's decisions** Q1–Q6 are in `docs/design/DISCUSSION.md`.
- **The v3 record** is in `.contract/docs/v3-*.md`. The copies under `docs/design/`, `docs/core/`
  and `docs/baseline/` are v3-era reference.
- **The baseline's report on the rules** is `docs/v4/FLOCK-BASELINE-FEEDBACK.md` (FB-n, H-n).
- **Ids** (V4-n, V4-An, C-Mn, C-mn, RA-Mn, RB-Mn, RF-Mn, FIXLIST Qn, CM-n, D-n, F1-Mn, F2-Mn, FB-n,
  H-n, V3-n, O-n, S<n>-A<k>, …) are cross-referenced everywhere. Keep them when you quote.
- If the contract, the harness documents and `AGENTS.md` disagree, report it. Do not code around
  it.

## The pin

- **Where it is.** `.contract` is pinned to **`<core-pin>`**, on the core's branch
  `v4/ks-standard`. It holds stages A and B, each with its review's fix passes (`01a25b0`, the head
  of `v4/srom-rules` and of the core's pull request #17), and two amendments on top:
  - the contract fix pass `ea2e8ab`: `acc` checks `decide (p.tr.length ≤ S.qV)` right after the
    size cap (RA-M2); `Log` is an `abbrev` for `Trace`; `wordBytes w := enc64 w.toNat`;
  - the harness fix passes `5b2b591` and `0bf80a7`, then `2632285` (the comparator built with the
    organiser's Lean): `.contract/docs/v4/stages/B-harness-RESULT.md` §9–§11;
  - **V4-A9, the trim** (`v4/trim-fat`, the core's pull request #18;
    `.contract/docs/v4/stages/D-trim-RESULT.md`): 30-minute jobs with nested caps, one tree run
    (root only) and one stream run (`M = 256`), statement canaries only, no liveness, one Lean
    build, `errorCap = 2^-120`, `completenessCap = 2^-40`;
  - **V4-A10, textbook knowledge soundness** (`v4/ks-standard`;
    `.contract/docs/v4/stages/E-ks-RESULT.md`): `KS` over query-bounded adversaries on a lazily
    sampled oracle; the potential `KState` is a library tool, closed by the bridge `KState.ks`.
- **Every entry is certified against the pin.** An entry that restates `acc` mirrors its conjuncts:
  `spartan-srom`'s `accWith` has the trace-length conjunct, and its `Decode` lemmas follow the new
  `wordBytes` (F1 review F1-m1; its F1 fix pass, `745c7d8`). Its certificate reaches V4-A10's `KS`
  through `KState.ks` (`docs/v4/flock-baseline/stages/F5-ks-RESULT.md`).
- **The pin moves only with a contract change**, in its own commit, before any entry is certified
  against the new commit (C14):

  ```sh
  git -C .contract fetch origin v4/srom-rules            # or main, once the core merges v4
  git -C .contract checkout <commit>
  git add .contract && git commit -m "Pin .contract at <commit>: <what changed>"
  ```

- **Set the caller workflow in the same commit.** `.github/workflows/evaluate-entry.yml` is a copy
  of the core's `harness/ci-template/evaluate-entry.yml`. Its two `CORE_COMMIT_SHA` placeholders,
  the reusable workflow's `@ref` and `core_ref`, are set to the same full commit SHA as the pin, in
  the same commit, or in the commit right after it (as `a6ee05c` and `4d2f282` did). Open: it has
  not run on GitHub.
- **Never pin a commit that the core's remote does not have** when this repository is pushed.
- **Never commit changes inside `.contract`.** Its working tree is the pinned commit plus
  gitignored build products. Build in a private copy (below), not in the submodule.

## Commands

Toolchain: Lean v4.34.1 and Mathlib v4.34.1; CompPoly `572f997`, ArkLib `7653a90`, VCVio
`a4232d0` and PolyFun `41d3b21`, as pinned in the core's `lakefile.toml` and `lake-manifest.json`.
The service needs Rust 1.99.0 (`service/rust-toolchain.toml`).

**The core at the pin, in a private copy with a private package tree.** Never use the shared
package tree:

- `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` is read-only and, since
  2026-10-22, holds no build products (A-RESULT §0).
- Never run `lake update` or `lake exe cache get` against it.
- Never write into another worktree's private tree. Copy it instead.

```sh
git submodule update --init                                  # .contract at the pin
mkdir -p logs/org && git -C .contract archive HEAD | tar -x -C logs/org     # logs/ is gitignored
# A built, writable package tree at the manifest's revisions:
#  - on the development VM, copy stage A's (9.0 GB; about 43 s, A-RESULT §0; F3 measured 9.2 GB
#    and 4 min 0 s with `cp -a` on ext4, F3 §1):
rsync -a /home/devops/Verified-zkEVM/recursion.fast-v4/.lake/pkgs-local/ logs/pkgs/
#  - elsewhere, let Lake clone into an empty logs/pkgs, then fetch Mathlib's cache inside the copy:
#      (cd logs/org && lake exe cache get)
mkdir -p logs/org/.lake && ln -s "$PWD/logs/pkgs" logs/org/.lake/packages
(cd logs/org && timeout 3600 lake build)                     # contract, library, controls
```

**Evaluate an entry as CI does**, with the harness at the pin.

- Run each step under `timeout`. A step that runs much longer than the times quoted below is
  inspected, not waited for: `ps -o etime`, a lock, a library being rebuilt.
- `evaluate.py cert` refuses an existing `--work` directory, so use fresh ones.

```sh
ORG=$PWD/logs/org
export RF_HARNESS_COMMIT=$(git -C .contract rev-parse HEAD)   # the archived copy is no git checkout:
                                                             # without this, the result records this repository's HEAD
# 1. organiser set-up, before any entry code: build, harness tools, allowlist and olean manifest
#    (ORG/.lake/rf/), the badge's compiled objects (the closures of RecursionFast, the CompPoly
#    roots and Mathlib.Tactic), the service (cargo). Its step timeouts sum to 18 min plus 2 for
#    the service (V4-A9). 4 min 12 s in F4's run at 81e1ebf (logs/f4/org-setup.log); 6 min 7 s
#    at a283ff8, the Mathlib.Tactic objects included (logs/f5/org-setup.log). Its default roots
#    include CompPoly's BF64.Ext3 and BF64.Bytes (FIXLIST Q2), so RF_ORG_ROOTS is not needed for
#    an entry that imports them.
timeout 1800 "$ORG/harness/org-setup.sh" "$ORG"
# 2. the proof checkers:
source "$ORG/scripts/tools.env"            # this VM's comparator; elsewhere:
#    "$ORG/harness/ci/build-kernels.sh" DIR, then export the COMPARATOR_* lines it prints.
#    The comparator and lean4export must be built with the organiser's Lean (v4.34.1), as
#    build-kernels.sh does. A comparator that stops before it builds Solution is a harness ERROR.
# 3. the certificate job: source rule, the one build, comparator (the Lean kernel), gate, badge,
#    each within its cap of the season file's [certificate] (build 600 s, kernel 600 s, gate
#    120 s, badge 180 s, for a 4-vCPU runner; V4-A9). --nanoda adds a separate nanoda run
#    (--nanoda-mem, default 14G). Each kernel run has its own memory scope and an outcome: ok,
#    rejected, over budget or timeout (Q12). A nanoda run over budget leaves the Lean kernel's
#    verdict; spartan-srom needs more than 20 GB for nanoda (F3 §2.4). spartan-srom at a283ff8:
#    8 min 42 s on 4 CPUs (the build 259.5 s, the comparator 182.3 s; logs/f5/cert4.log), 6 min 47 s
#    on 16 (logs/f5/cert16.log); at 81e1ebf 9 min 52 s, comparator 354 s at 4.25 GB
#    (logs/f4/cert.log), 16 min 36 s with --nanoda (logs/f4/cert-nanoda.log).
timeout 1800 python3 -I "$ORG/harness/evaluate.py" cert --entry submissions/<root> --org "$ORG" \
  --work logs/eval/<run>/cert --out logs/eval/<run>/cert.json
# 4. the benchmark job at the smoke shape (the service and rf-bench default to ORG's builds);
#    each part ends within PART_S = 28 min
timeout 1800 python3 -I "$ORG/harness/evaluate.py" bench --entry submissions/<root> \
  --cert logs/eval/<run>/cert.json --season "$ORG/harness/smoke.toml" \
  --work logs/eval/<run>/bench --out logs/eval/<run>/result.json
# or both in one go: evaluate.py all --entry … --org "$ORG" --work … --out … --season …
```

- **The runner needs the host's sandbox.** It needs `bwrap`, unprivileged user namespaces and a
  systemd user manager for the memory cgroups. Where no user manager is reachable, the memory cap
  falls back to `prlimit --as`, and the result says so (`memcap`). On Ubuntu 24.04 the AppArmor
  restriction on user namespaces must be relaxed: `harness/ci/runner-setup.sh` does this on CI.
- **What the harness builds.** It builds `Challenge` and `Solution` once, in the sandbox, and the
  comparator, the gate and the badge read that build (V4-A9), so only `Solution`'s import closure
  is built, checked and gated (FIXLIST Q7). An entry module that `Solution` does not import is
  never built or checked by the harness: import the controls from `Solution` if the harness is to
  check them. The certificate records `built_modules`. The badge build compiles, within its
  180 s, the objects of every module of that closure outside the organiser's precompiled
  closures of `RecursionFast`, the CompPoly roots and `Mathlib.Tactic`.
- **Iterating on Lean without the harness.** Mirror what `evaluate.py`'s `mkfresh` writes. That is
  a lakefile and a manifest that require `logs/org` by path, with `packagesDir` the private tree,
  and one `[[lean_lib]]` that lists **every** module of `lean/` as a root: Lake's `globs =
  ["Foo.+"]` means submodules of `Foo`, not a name prefix (F1 §7 item 9). Render the challenge with:

  ```sh
  python3 -I logs/org/harness/render-challenge.py \
    logs/org/harness/challenge/Challenge.lean.in claim.json OUT.lean
  ```

  Diff its `declared` against your `Solution.lean`.
- **The native prover.** Build `prover.s` with the entry's own script (for `spartan-srom`,
  `submissions/spartan-srom/prover/build-asm.sh WORK`, with `WORK` outside the entry). Link it with
  the runner's command, `gcc -static -O2 -pthread *.s -o prover -lm`. The entry's `selftest.py`
  runs it against a real `rf-oracle`.
- **The reference toolchain** is the runner image's: `ubuntu-24.04`, GCC 13.3, GNU Binutils 2.42,
  glibc 2.39 (`.contract/harness/PROVER.md` §1, RF-M2). The `.s` must assemble with that `as`; this
  VM's binutils is 2.46. `.contract/harness/tools/asm-compat.py IN.s OUT.s` rewrites the directives
  2.42 rejects (GCC 15's `.base64`, LLVM 23's `.prefalign` and DWARF-5 `.file`); it merges
  `spartan-srom`'s `sanitize-asm.py` rules with the GCC one.
- **Logs.** Measurements go to `logs/` (gitignored) and are quoted in the stage RESULT with their
  path.

## Stage protocol (as in the core's `CLAUDE.md`)

Work here is built in stages, one at a time. The v4 baseline's stages are F0 (probes), F1 (Lean),
F2 (prover), F3 and F4 (the harness runs) and F5 (the migration to V4-A9 and V4-A10). Their records are `docs/v4/flock-baseline/stages/` and
`reviews/`. Each stage runs the same cycle:

1. **Implement** (one agent). Build the stage and keep the build green. Write
   `stages/<id>-RESULT.md` with:
   - what was built, with code line counts;
   - build and run times, each with its log;
   - the controls, and what each shows;
   - every deviation from the blueprint or the contract, with its reason;
   - open questions.

   Keep a running `stages/<id>-JOURNAL.md` that a successor reads first.
2. **Adversarial review** (one agent, in parallel with 3). It writes `reviews/<id>-review.md` with
   numbered findings (`<id>-M<i>` major: must fix; `<id>-m<i>` minor) and a verdict.
3. **Golf** (one agent, in parallel with 2). It shortens proofs, and run time, without changing
   any statement, and reports before and after.
4. **Fix** (the implementing agent). Apply every major finding, answer each minor one, append
   `## Fix pass` to the RESULT, and re-run the build and the controls.
5. **Commit.** The orchestrator commits.

Subagents **do not commit**; the orchestrator does. Skills:

- `lean-spec-authoring` for definitions and statements;
- `adversarial-review` and `lean4:review` for review;
- `lean4:golf` for golfing;
- `lean4:lean4` for any Lean work.

## Hard rules

For entries, the harness checks these (`AGENTS.md` §6).

- **Axioms.** Only `propext`, `Classical.choice` and `Quot.sound`.
  - **No `sorry`.** It makes an entry PROVISIONAL at best, so it belongs only in a deliberately
    provisional run.
  - **No `native_decide`.**
- **No code-changing attributes**: `implemented_by`, `extern`, `export`, `init`, `csimp`, `cpass`,
  `computed_field`. **No `unsafe`, `partial` or `opaque`.**
- **No elaboration-time code.** The source rule refuses `#eval`, `run_cmd`, `elab`, `macro`,
  `initialize`, `import Lean` and the like, comments included.
- **Imports only from the allowlist closure**, plus the entry's own modules. The closure is that of
  Mathlib, the contract, the library, the controls and CompPoly's `BF64.Ext3` and `BF64.Bytes`, at
  the pin (`org-setup.sh`'s default roots, FIXLIST Q2; `AGENTS.md` §6). Other modules of the pinned
  packages are checked as entry code. Imports beyond the precompiled closures (`RecursionFast`,
  the CompPoly roots, `Mathlib.Tactic`) are compiled in the badge build, within 180 s:
  `import Mathlib` does not fit (`AGENTS.md` §5.1).
- **The submission is computable.** The badge compiles the whole `RecursionFast.Challenge.submission`,
  so `ε` and `δ` too (a cast from `ℚ≥0`). Gate rule 4 also requires compiled code for `V`, `P` and
  `ext`.
- **Statements are non-vacuous**, with a positive and a negative control for every definition an
  entry relies on.
- **Knowledge soundness is the contract's textbook `KS`** (V4-A10). A potential (`KState`) is an
  untrusted library route to it, closed by `KState.ks`; the caps are `ε ≤ 2^-120` per fresh query
  and `δ ≤ 2^-40` (V4-A9; `AGENTS.md` §3.1).
- **A proof never changes the statement it proves.** An entry fills only the challenge's
  `submission` and `certified`.
- **An entry pull request touches only its own root:** never `records.json`, `.contract`, `docs/`,
  the workflows or another root.
- **The byte layouts are the contract's.** Statements, trace digests, signatures and files hash
  exactly the bytes of design §1.3 and FORMAT.md.
- **Copies are read-only.** Files under `docs/` are copies, except:
  - `docs/README.md`, `docs/baseline/BASELINE-TASK.md` and `docs/report/README.md`;
  - everything under `docs/v4/`.

  Re-copy a copy from its source with a new provenance line; never edit it here.
- **Read-only references.** Never edit, build in or commit to:
  - `/home/devops/Verified-zkEVM/recursion.fast`, the core's main checkout;
  - `/home/devops/Verified-zkEVM/recursion.fast-v4`, the core's v4 worktree (other agents work
    there);
  - the design workspace `/home/devops/CambridgePQ/recursion.fast`.

  Use `.contract` or a private copy.
- **No pushing**, and no creating remotes or GitHub repositories, unless the user asks.

## Conventions

- **No estimates.** Describe work by what it consists of and what it depends on, never by how long
  it will take. Durations that were **measured**, such as a build time or a harness run, are facts:
  quote them with their log.
- **Evidence tags**, as in the core: **kernel** (with the theorem name), **paper**, **measured**
  (with its log), **estimate**.
- **The writing.** Plain and precise, British spelling, no marketing. Ids are kept.
- **Long-running work.** Every build or probe that runs in the background or under a shared lock
  gets a `timeout`. Pin heavy runs to a subset of cores (`taskset`) on the shared VM, and say so
  next to any time you quote.

## What "done" means

A stage is done when:

- its definition of done in the blueprint is met;
- the entry builds, and its own checks pass;
- `harness/evaluate.py` at the pin gives the entry the verdict the stage claims: ACCEPT, or
  PROVISIONAL where that is the stated goal;
- the RESULT, the review and the golf report are written, and the fix pass is appended;
- the orchestrator has committed it.

A claim in a RESULT is a kernel-checked theorem or a measurement with a log under `logs/`.
Nothing else counts.
