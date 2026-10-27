# F5-golf: `spartan-srom` after V4-A9 and V4-A10 — GOLF, 2026-10-27

Status: **done; not committed** (the orchestrator commits). Scope: what stage F5 touched, the
entry's commit `d5a53fa` (`git diff f07d028 d5a53fa`) and the guidance commit `90323cd`
(`git diff 5a28f9b 90323cd`). No statement, definition, claim, rule, number or id changed.

| | |
|---|---|
| Entry | worktree `recursion.fast-submissions-ks`, branch `v4/spartan-srom` at `ff40276`; changes uncommitted |
| Guidance | worktree `recursion.fast-submissions-guidance`, branch `v4/guidance` at `90323cd`; changes uncommitted (this record among them) |
| Core | **`8645c39`** (the E-ks golf), a detached worktree at `logs/f5-golf/org`, removed after the runs. During this pass the core's fix pass landed as `8ad98e9` (`OProg.bind_assoc` and `queries_bind` protected, `cert.json` records the gate's and badge's seconds and the kernel's peak); nothing here ran against it |
| Packages | F5's private tree `logs/f5/pkgs`; the comparator of `logs/f5/kernels` (`kernels.env`) |
| Logs | the entry worktree's `logs/f5-golf/` (gitignored), written `G/` below |
| Machine | the shared 32-vCPU QEMU VM, load average 4–13 from other agents. CPU sets: certificate jobs `taskset -c 0-3`; `org-setup.sh` and the smoke bench `0-15`; the development builds `16-31`; elaboration timings and profiles `16-19` and `20-23`. Every command under `timeout` |

## 1. The Lean (entry worktree)

| File | Change | Code lines |
|---|---|---|
| `SpartanSromSubmission.lean` | `certificateOf.secure` in term mode: `acc_eq LV proveLeaf ▸ (F.ks vk).elim fun k => k.ks (V_queries F vk)` (was `show` of the goal, `rw [acc_eq]`, `exact` of the same term) | 146 → 143 |
| `SpartanSromSnarkQueries.lean` | `atMost_verify1`: `LawfulMonad.bind_assoc` joins the `simp only` (was a separate `rw`) | 88 → 87 |
| `SpartanSromSoundnessKState.lean` | `kstate`'s `step _ _ := mu_step_chain` (was `fun _ _ hl hμ hq => mu_step_chain hl hμ hq`) | 24 → 24 |
| `SpartanSromSoundnessKSFinal.lean` | `final_law vk := mu_final vk`: the binders are already in `KState.final`'s order (was the eta-expanded `fun L c π hl hμ hacc => …`) | 26 → 26 |
| `SpartanSromSoundnessKSBase.lean` | docstrings the migration missed: three said "the contract's `step` law" (the module header, `muG_step`, `muG_step_of`); now the `step` law of the library's `KState` | 1,651 → 1,651 |

Code lines (`.contract/scripts/loc.py`, as F5) **17,903 → 17,899**, theorems 1,695 unchanged
(`G/loc-before.log`, `G/loc-after.log`). The changed text is after `:=` or in comments, and the
statements print as before (`G/axioms-after.log`: `#check` of `KS.ks`, `final_law`,
`certificateOf`).

**Kept.** The two `import RecursionFast.Library.PaperTheorem` that F5 added (in
`SoundnessKState` and `Submission`), and `Submission`'s `import RecursionFast.Library.Completeness`,
are redundant at `8645c39` and at `8ad98e9`: `SpartanSromDecode` imports
`RecursionFast.Library.WitnessSending`, which imports both. They are kept because they name the
modules of the declarations the entry uses (`KState.ks`, `complete_withError_zero`), and the entry
then does not depend on the library's own imports. `KS.of_extracts` and the `prob` facts have no
use in the entry: its certificate goes through the potential, and no control of the entry is
about `KS`.

**Elaboration time** of the touched modules (`G/elab-compare.log`; HEAD's file and the golfed file
elaborated alternately, 5 runs each, `taskset -c 20-23`, against the golfed build's oleans; median
of wall time minus the profiler's import time, which is 2.7–4.5 s):

| Module | HEAD | golf |
|---|---|---|
| `SpartanSromSoundnessKState` | 0.68 s | 0.61 s |
| `SpartanSromSubmission` | 1.20 s | 1.03 s |
| `SpartanSromSnarkQueries` | 0.98 s | 1.03 s |
| `SpartanSromSoundnessKSFinal` | 0.73 s | 0.71 s |

Within the noise of the VM, except `Submission` (−0.17 s, the `show` and the `rw` gone). Each of
these modules spends most of its 4–5 s of wall time importing.

## 2. The certificate build: profiled, not changed

The certificate's build is CPU-bound on 4 CPUs (about 850 CPU-seconds of `lean` for 67 modules,
`G/dev-build-before.log`), and each module pays about 4 s of import. Two modules stand out
(`G/dev-before-times.txt`, the before build on 16 CPUs):

- **`SpartanSromTranscriptControls`, 101 s** (the largest; a control, outside the certificate's
  closure, so it costs build time only, not comparator time). Profile
  (`G/profile-transcriptcontrols-before.log`, 73.6 s wall on 4 CPUs): 65.9 s of kernel type
  checking in its known-answer tests, which run BLAKE2s in the kernel through `decide +kernel`:
  9.7 s, 7.6 s, 5.4 s, 5.5 s, 5.0 s, 4.9 s, 13.8 s and 12.8 s for the eight that hash (by
  declaration order: `kat_transcript`, `kat_transcript_root_ne`, the four Merkle KATs,
  `colL_log4`, `colL_log4_missing`). One compression costs **1.8 s** in the kernel. The library's
  word-level twin (`Blake2s.digestL`, `compressF`) is slower there: `kat_transcript` 9.0 → 12.1 s
  through `digestL_eq`, one compression 1.8 → 2.3 s through `compressF`
  (`G/probe-kernel-blake2s.log`, `G/probes/`). So no contained change makes these faster; sharing
  one evaluation of a Merkle tree between KATs would need its literal (§5 item 2).
- **`SpartanSromSoundnessKSBase`, 47 s** (on the certificate's path; 68–72 s on 4 CPUs). Profile
  (`G/profile-ksbase-before.log`, 53 s wall on 4 CPUs): 103 `simp` calls of 1.0–1.7 s each (the
  profiler names no position; the densest `simp` blocks are lines 969–1157 and 1541–1604).
  Narrowing them is a refactor of a v3 module the migration did not touch (§5 item 1).

## 3. Checks (`8645c39`)

**`org-setup.sh`** (`taskset -c 0-15`): **ok in 3 min 59 s** (`G/org-setup.log`, the steps'
logs in `G/org-setup-steps/`); F5's run at `a283ff8` took 6 min 7 s. Organiser build 102 s, tools
9 s, allowlist (10,818 modules) and manifest (34,374 entries) 79 s, the badge's objects 35 s (most
were already in the private tree from F5's run), the service 14 s.

**The certificate job** (`evaluate.py cert`, Lean kernel, `taskset -c 0-3`). HEAD's entry
(`G/entry-before`, `git archive` of `ff40276`) ran twice: once beside the development build on
CPUs 16–31, and once with nothing else of this pass running, directly after the golfed entry
(`G/entry-after`, a copy of the working tree). The gate's, the badge build's and the manifest
check's seconds are from file times, as in F5 (`comparator-lean.log` → `gate.log` →
`tree/.lake/build/bin/verify` → `badge.log`); the build's and the kernel's are `cert.json`'s.

| Step (cap) | HEAD, beside a build | **HEAD** | **golf** | F5, `a283ff8` |
|---|---|---|---|---|
| the one build (600 s) | 319.4 s | **263.2 s** | **253.7 s** | 259.5 s |
| comparator, Lean kernel (600 s) | 185.8 s | **175.9 s** | **168.0 s** | 182.3 s |
| gate (120 s) | 26.7 s | **26.3 s** | **25.1 s** | about 26 s |
| badge build (180 s) | 30.8 s | **22.9 s** | **21.6 s** | about 20 s |
| manifest check after the badge | 18.0 s | 16.9 s | 18.3 s | about 17 s |
| **whole job** | 9 min 59 s | **8 min 42 s** | **8 min 24 s** | 8 min 42 s |
| largest process | 3.68 GB | 3.68 GB | 3.68 GB | 3.68 GB |

(`G/cert4-before.{log,json}`, `G/cert4-before2.{log,json}`, `G/cert4-after.{log,json}`.) The
golf's −9.5 s (−3.6 %) of build and −7.9 s (−4.5 %) of kernel are the size of this VM's
run-to-run variation (F5's run of the same proofs at `a283ff8`: 259.5 s and 182.3 s): the golf
changes four proof terms, and **no measurable change** is claimed. All three runs: `ok`, 67 built
modules, "one build (134 artifacts), read by the comparator, the gate and the badge build"; the
source rule 66 files, 0 findings; the gate PASS with a closure of 33,517 constants (33,518 at
`a283ff8`: the core's golf), 3,830 modules (3,723 trusted, 28 pinned), axioms `propext`,
`Classical.choice`, `Quot.sound`; the badge compiled 68 objects (the entry's 66 and the badge's
2; F5's 6 package objects were already in the private tree, as in F5's 16-CPU run), and its
`verify` is byte-identical in every run and to F5's (`195377d6…`); the kernel's memory peak is
not recorded at `8645c39` (F5 §5 item 3). `environment`: core `8645c396…`, manifest `c8f63627…`
(`c752a798…` at `a283ff8`), allowlist `fe740dbf…` (F5's).

**Axioms** (`G/axioms-after.log`, the development tree): `RecursionFast.Challenge.certified`,
`SpartanSrom.certificate`, `KS.ks`, `KS.kstate`, `SoundnessKSFinal.final_law`,
`NodeControls.certificateR_claim` and `NodeControls.claim_negatives` depend on `propext`,
`Classical.choice` and `Quot.sound` only.

**The smoke bench** (`evaluate.py bench`, `smoke.toml`, `taskset -c 0-15`, the golfed entry's
certificate): **ACCEPT** in 13.8 s (`G/bench-smoke.{log,json}`).

| | F5, `a283ff8` | golf, `8645c39` |
|---|---|---|
| prover binary | `c5f5e1a8…`, 2,818,664 B | the same |
| `T_tree` | 0.116 s | 0.144 s |
| `t_leaf`, `t_merge`, `t_link` | 0.0560, 0.0106, 0.0666 s | 0.0563, 0.0112, 0.0676 s |
| **`S`** | 1.448 | **1.495** |
| root `acc` (2,169,384-byte file) | 392 ms | 386 ms |
| statement canaries rejected | 1 + 8 | 1 + 8 |
| DoS column | 64 inputs, none accepted, max 323 ms | 64, none accepted, max 215 ms (`dos/2.bin`) |
| `T_V` | cap 0.018 ms, 10 of 10 over, max 549 ms | cap 0.011 ms (`T_triv,best` 0.108 ms), 10 of 10 over, max 510 ms |
| service, 1 / 16 threads | 6.32 M, 108.0 M calls/s | 7.05 M, 110.2 M calls/s |

The prover is the same binary: the differences are one run each on a shared VM. F5 RESULT §8
item 4 asked for a rebuild against the core's final head once its golf moved proofs: at `8645c39`
the entry certifies and is ACCEPTed; the fix pass `8ad98e9` is not run here.

## 4. Documents

Wording and layout only; every number, rule, claim and id is as it was.

**Entry worktree.**
- `submissions/spartan-srom/README.md`: the knowledge-soundness bullet's three appositions in one
  parenthesis ("from v3's potential (now the library's `KState`, the entry's intermediate
  artifact) through the library's bridge `KState.ks`"); the 383-character line "The verdict at
  the previous pins" wrapped at 100 like the rest.
- `NOTES.md`: unchanged (§4.7 records the migration as F5 made it, the two imports included,
  which stay).

**Guidance worktree.**
- `AGENTS.md`: the status's V4-A9 bullet no longer splits the code span `errorCap = 2^-120`
  across lines; §5.1's log list wrapped; §5.2 "The two jobs" rejoined (a line ended after "Since
  RF-M1 it"); §7's introduction "X and Y, and Z" made "X, Y and Z".
- `CLAUDE.md` (stage protocol), `docs/README.md` (the v4 note), `README.md` (the F5 bullet): lines
  of 102–140 characters rewrapped.
- `docs/v4/flock-baseline/stages/F5-ks-RESULT.md` §4: a 117-character line rewrapped.
- `BLUEPRINT.md`, `FLOCK-BASELINE-FEEDBACK.md`, `submissions/README.md`, the workflow: unchanged;
  their new text is no wordier than the text around it.
- This record.

## 5. Suggestions not applied

1. **`SpartanSromSoundnessKSBase`'s `simp` calls** (§2): about 100 of 1.0–1.7 s each make it the
   slowest module on the certificate's path. A golf of that v3 module could cut a large share of
   the build's CPU time; it is outside this stage's diff.
2. **`SpartanSromTranscriptControls`** (§2): `kat_merkle_root`, `kat_verify`, `kat_verify_flip` and
   `kat_verify_index` each evaluate `build #[col0, col1] 1` in the kernel, and `colL_log4` and
   `colL_log4_missing` each evaluate `log4` and `root4`. One lemma per tree with its literal value
   would save about 5 s per reuse, at the cost of the literals (a few lines for the 2-leaf tree, a
   7-entry log for `log4`). It changes only build time: controls are outside the certificate's
   closure.
3. **`final_law` is now an alias of `mu_final`** (same binders, same order). `kstate` could use
   `final := mu_final vk` and `final_law` could go; not applied, since the headers of
   `SoundnessKState` and `SoundnessKSFinal` name it.
4. **The redundant imports** (§1, "Kept"), if the entry should import only what its closure does
   not already provide.
5. **`AGENTS.md` §7.5, the last migration item** ("the library's new `OProg.bind_assoc` and
   `OProg.queries_bind` can make an unqualified name ambiguous"): since the core's fix pass
   `8ad98e9` both are `protected`, so at that pin the item is history; the entry's
   `LawfulMonad.bind_assoc` is correct either way. To reword when the pin moves.
6. `SpartanSromFinal.facts.ks`: `le_of_eq εR1_eq.symm` is `εR1_eq.ge`; outside the stage's files.
