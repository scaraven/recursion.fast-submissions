# F5: `spartan-srom` under V4-A9 and V4-A10 — RESULT, 2026-10-27

Status: **done; not reviewed; not committed.**

| | |
|---|---|
| Rules | the core's amendments **V4-A9**, the trim (`v4/trim-fat`, the core's pull request #18; `.contract/docs/v4/stages/D-trim-RESULT.md`), and **V4-A10**, textbook knowledge soundness (`v4/ks-standard`; `E-ks-RESULT.md`) |
| Harness | the core at **`a283ff8`**, the head of `v4/ks-standard`, which contains `v4/trim-fat`; a detached worktree of it at `logs/f5/org` (removed after the runs) |
| Entry | the branch `v4/spartan-srom` at `f07d028` with this stage's changes (uncommitted); `claim.json` and `prover/prover.s` (`733b3a30…`) unchanged; the runs used a copy, `logs/f5/entry/spartan-srom`, whose `lean/` is identical to the working tree's |
| Discipline | a private package tree, `logs/f5/pkgs` (a `cp -a` of `recursion.fast-v4/.lake/pkgs-local`, 9.2 GB, 2 min 2 s, `logs/f5/pkgs-copy.log`); the comparator `d03acab` built from its pin by `harness/ci/build-kernels.sh` into `logs/f5/kernels` (23.6 s, `logs/f5/build-kernels.log`); every command under `timeout`; `taskset` as stated per run; nothing written to shared trees or other worktrees |
| Logs | this worktree's `logs/f5/` (gitignored) |
| Machine | the shared 32-vCPU QEMU VM (no `pclmulqdq`), loaded by other agents' builds: load average 6–17 during the runs |

## 1. The migration (entry side)

| File | Change | Lines (in / out) |
|---|---|---|
| `lean/SpartanSromSoundnessKState.lean` | `ks vk := (kstate vk).ks (V_queries_le vk)` (was `⟨⟨kstate vk⟩, V_queries_le vk⟩`); `import RecursionFast.Library.PaperTheorem`; the header says that `KState` is the library's potential and `KS` comes through the bridge | 9 / 4 |
| `lean/SpartanSromSubmission.lean` | `certificateOf.secure`: `(F.ks vk).elim fun k => k.ks (V_queries F vk)` (was `⟨F.ks vk, V_queries F vk⟩`); the same import; header | 6 / 4 |
| `lean/SpartanSromSnarkQueries.lean` | `rw [LawfulMonad.bind_assoc]` (was `rw [bind_assoc]`, made ambiguous by the library's new `OProg.bind_assoc`, §5 item 1) | 1 / 1 |
| `lean/SpartanSromSoundnessKSFinal.lean`, `lean/SpartanSromSoundnessKS.lean` | docstrings: `final` and `step` are the library's `KState` laws, not the contract's | 5 / 4 |

21 lines in, 13 out, in 5 of 66 files. Code lines (`.contract/scripts/loc.py`) **17,901 → 17,903**
(the two imports), theorems 1,695 unchanged (`logs/f5/loc-before.log`, `loc-after.log`).

**Statements.** None changed, and the contract forced no change:
- `SpartanSrom.KS.kstate vk : KState (Rel (accV LV vk)) (V LV vk) WitnessSending.E εKS`, the
  potential, is unchanged, now the entry's intermediate artifact (the library's `KState`, the same
  structure with the same laws).
- `SpartanSrom.KS.ks vk : RecursionFast.KS (Rel (accV LV vk)) (V LV vk) WitnessSending.E εKS
  (2 ^ 16)`: the same text; it now means the textbook statement, since the contract's `KS` changed.
- `Facts` keeps its field `ks : ∀ vk, Nonempty (KState …)`; `certificateOf`, `certificate`,
  `certificateR_of` and `Solution`'s `certified` keep their statements.
- The controls are unchanged and still build, `claim_negatives` included (`ε = 2^-130`,
  `qV = 2^16 − 1`, fuel `7 t` not certified).

**The claim against the new caps.** `ε = 2^-129 ≤ errorCap = 2^-120` (`εR1_le_errorCap`, proof
unchanged), `δ = 0 ≤ completenessCap = 2^-40`, `qV = 2^16`. The challenge rendered at `a283ff8`
from `claim.json` is identical to `Solution.lean`'s stub (the template did not change).

**Checks.** The entry built in a development tree mirroring `mkfresh` (16 CPUs, `taskset -c 16-31`):
the first build stopped at `SpartanSromSnarkQueries.lean:62` (`logs/f5/dev-build-1.log`, 2 min 40 s),
the second was green (`dev-build-2.log`). `#print axioms` of `RecursionFast.Challenge.certified`,
`SpartanSrom.certificate` and `SpartanSrom.KS.ks`: `propext`, `Classical.choice`, `Quot.sound`
(`logs/f5/axioms.log`). The source rule: 66 files, 0 findings. The gate in both certificate runs:
PASS, closure of 33,518 constants, those three axioms, 3,830 modules (3,723 trusted, 28 pinned).

## 2. The certificate job (`evaluate.py cert`, Lean kernel)

`org-setup.sh` at `a283ff8` (`taskset -c 0-15`): **ok, 6 min 7 s** (`logs/f5/org-setup.log`). Steps:
organiser build 107 s, tools 9 s, allowlist and manifest 95 s (10,818 modules, 2 more than at
`01a25b0`: `Library/Prob`, `Library/KS`; 34,374 manifest entries), the badge's objects with the
`Mathlib.Tactic` closure 142 s, the service 14 s. The development build ran beside steps 3 and 4 on
other cores, so these are upper figures.

Two certificate runs, **both ok**, with the season's `[certificate]` caps (identical in both season
files):

| Step (cap) | 4 CPUs, `taskset -c 0-3` (`cert4`) | 16 CPUs, `taskset -c 0-15` (`cert16`) | F4b at `01a25b0`, 16 CPUs |
|---|---|---|---|
| render, source rule, manifest check | 17 s | 8 s | — |
| **the one build** (`build_s` 600 s) | **259.5 s** (43 %) | 181.5 s | inside the comparator |
| **comparator, Lean kernel** (`kernel_s` 600 s) | **182.3 s** (30 %) | 171.6 s | 359.5 s with the build |
| binding | "one build (134 artifacts), read by the comparator, the gate and the badge build" | the same | "byte-identical (134 artifacts)" after a rebuild |
| **gate** (`gate_s` 120 s) | **about 26 s** (21 %) | about 22 s | — |
| **badge build** (`badge_s` 180 s) | **about 20 s** (11 %): 74 objects, the entry's 66, the badge's 2, and 4 Batteries and 2 Mathlib modules outside the precompiled closures | about 16 s: 68 objects (the 6 package objects were left in the private package tree by `cert4`) | — |
| manifest check after the badge | about 17 s | about 8 s | — |
| **whole job** | **8 min 42 s**, largest process 3.68 GB | **6 min 47 s**, 3.68 GB | 9 min 51 s |

(`logs/f5/cert4.{log,json}`, `logs/f5/cert16.{log,json}`; the build's and the comparator's seconds
are `cert.json`'s `build_s` and `comparator_s`; the gate's and the badge's are from the work
directory's file times, `cert.json` does not record them, §5 item 2.)

- **Against the caps on 4 CPUs**: the build has 2.3× headroom, the kernel 3.3×, the gate 4.6×, the
  badge 9×. These are 4 CPUs of a loaded QEMU VM, not a GitHub runner.
- Both runs: `built_modules` 67 (the 66 modules and `Challenge`), kernels `['lean']`, no nanoda
  (not run: it needs more than 20 GB on this entry, F3 §2.4). The kernel run's memory peak is not
  recorded (§5 item 3); the largest process of the job, by `/usr/bin/time`, was 3.68 GB.
- The badge `verify` was byte-identical across the two runs (`195377d6…`).
- `environment`: core `a283ff85…`, manifest `c752a798…`, allowlist `fe740dbf…`.

## 3. The benchmark (`evaluate.py bench`, `taskset -c 0-15`, the certificate of `cert4`)

**Smoke (`smoke.toml`): ACCEPT** in 14 s (`logs/f5/bench-smoke.{log,json}`).

| | F5 at `a283ff8` | F4b at `01a25b0` (the same binary) |
|---|---|---|
| prover binary | `c5f5e1a8…`, 2,818,664 B | `c5f5e1a8…` |
| `T_tree` | **0.116 s** | 0.142 s |
| `t_leaf`, `t_merge`, `t_link` | **0.0560 s, 0.0106 s, 0.0666 s** | 0.0702, 0.0144, 0.0846 s |
| **`S`** | **1.448** | 1.835 |
| root `acc` (bundle of 4, 2,169,384-byte file) | **392 ms** | 390 ms |
| statement canaries rejected | **1 (the root) + 8 (2 leaf and 2 node stream outputs × 2)** | 76 tree + 20 stream canaries of every kind |
| DoS column | **64 inputs, none accepted, max 323 ms** (`dos/10.bin`), 47 over `T_V` | 64, max 401 ms |
| `T_V` | cap 0.018 ms (`T_triv,best` 0.180 ms), not enforced; 10 of 10 checks over it, max 549 ms | 19 of 19 over, max 505 ms |
| liveness | gone (V4-A9) | ok, 30,820-entry log |
| service | 6.32 M calls/s on 1 thread, 108.0 M on 16; 0 refusals | 5.29 M, 102.5 M |

The prover is the same binary; the lower `S` is one run each on a shared VM, not a faster prover.

**Season (`season.toml`): REJECT**, for F4's reasons (`logs/f5/bench-season.{log,json}`,
`bench-season-stream.{log,json}`):
- all parts: "tree: prover tree exit 3; prover output (tail): 'spartan-srom-prover: oracle
  service: a Fiat–Shamir query of 1572898 bytes is above queryCap = 1048576 (the service refuses
  it)'", 15.4 s into the tree run, after 1,049,601 queries. `T_triv,best` 2.847 s, `T_V` 285 ms.
- `--parts calibrate,stream`: "stream outputs: stream leaf 0 rejected by acc". The leaf took 15.9 s;
  its file is 5,990,112 B with `π` = 2,791,559 B, above `proofCap`.

## 4. What the trim changed for this entry

- **Certificate.** One build: the byte-identical rebuild (173 s in F4) is gone, and the job went
  from 9 min 51 s (F4b, 16 CPUs) to 6 min 47 s on 16 CPUs and 8 min 42 s on 4. Every Lean step now
  has a cap, and this entry is inside each on 4 CPUs (§2). The badge build compiles 6 package
  modules that the precompiled closures (`RecursionFast`, the CompPoly roots, `Mathlib.Tactic`) do
  not hold; in the evaluation's certificate job, which restores the setup job's cache, it compiles
  them every time, within the 180 s.
- **Caps.** `errorCap = 2^-120` leaves `ε = 2^-129` a factor `2^9` inside the cap (it was 2);
  `δ = 0`, so `completenessCap = 2^-40` changes nothing. A GF(2^128) leaf would now qualify per
  round (FB-9); this entry keeps GF(2^192).
- **Benchmark.** One run each; only the tree's root is read, so the prover's inner proofs are
  ignored; per entry only the statement canaries (9 at the smoke shape, against 76 + 20 at F4b,
  and 32 more on F4's liveness tree); no liveness; the DoS column records accepted inputs instead
  of failing on them (none was accepted). The entry's own Lean controls for `π ± 1` byte stay:
  they are entry controls, no longer a harness requirement.
- **Season.** The first failures are unchanged (`queryCap` for the tree, `proofCap` for the
  stream). Behind them the trim adds a time wall: at 15.9 s per `2^16` leaf on 16 CPUs, the tree's
  `2^24` compressions are about 256 such leaves, about 68 min against `tree_s` = 10 min (about
  6.8×), and the stream's 257 leaves alone about 68 min against the entry's 900 s of `stream_s`
  (about 4.5×), before its merges (**estimate**, linear in `n`, and slower on 4 vCPUs). `M` fell from
  512 to 256.

## 5. Problems found in the core (at `a283ff8`)

1. **(minor) The library's new `OProg.bind_assoc` and `OProg.queries_bind` are not `protected`.**
   `RecursionFast.OProg.bind_assoc` (`Library/Oracle.lean`, stated with `OProg.bind`) became
   visible as `bind_assoc` in every entry file with `open … OProg`, beside Lean core's exported
   `LawfulMonad.bind_assoc`. In `SpartanSromSnarkQueries.lean:62`, which builds at `01a25b0`,
   `rw [bind_assoc]` then elaborated to the library's lemma and failed: "Did not find an occurrence
   of the pattern `(OProg.bind ?p ?f).bind ?g`" (`logs/f5/dev-build-1.log`). The entry now names
   `LawfulMonad.bind_assoc`. Making the two lemmas `protected` would keep library additions from
   changing the meaning of names in existing entries.
2. **(minor) `cert.json` records no duration for the gate or the badge build**, though both are
   now caps (`gate_s`, `badge_s`). It records `build_s` and `comparator_s`; F5 read the other two
   off file times. A submitter cannot see their margin from the result.
3. **(minor, not new) The kernel run's memory peak is recorded only on an OOM kill**
   (`harness/rfh/sandbox.py`, `scope_oom`: a successful transient scope is gone when `MemoryPeak`
   is read, so `peak_bytes` is `null`). F4's 4.25 GB came from an external monitor. Unchanged
   since `01a25b0`.

Nothing else failed: the setup, both certificate runs, the smoke bench and the two season benches
ran as the documents say; the trim's new GitHub workflow structure was not exercised here (it has
not run on GitHub, D-trim §8 item 7).

## 6. The guidance side (branch `v4/guidance`, files kept apart from the entry's)

- `.github/workflows/evaluate-entry.yml`: synced with `harness/ci-template/evaluate-entry.yml` at
  `a283ff8` (the `select` and `report` jobs' 10-minute limits; the `split` description). Kept from
  the current file: line 1's header ("the core's harness/ci-template at the pin; copied to"). The
  two `CORE_COMMIT_SHA` values are `<core-pin>` for the orchestrator.
- `AGENTS.md`: status and pin; §1 score and shapes; §2.2–§2.4 (the services, no logging mode, the
  `sk`-holding adversary against the new `KS`); §3.1 (the textbook `KS`, the bridge as the
  recommended route, `KS.of_extracts`, `completenessCap`, the caps); §3.2 (no badge runs `ext`);
  §3.3 (one build); §4.1 (`setup_s`, `tree_s`, root only, `step_s`, the stream deadline); §4.3;
  §5.1 (the one build, the four caps, the badge's precompiled objects, the cost table with F5);
  §5.2 (two jobs, one run each, root only, DoS semantics, no liveness); §5.3; §5.4; §5.5 (the caps
  table); §6 (the badge cap); §7 intro, §7.1 (`M = 256`, GF(2^128) at `2^-120`), §7.5 (migrating
  to V4-A10; the badge's objects), §7.6 (statement canaries; the DoS column), §7.7, §8, §9.
- `CLAUDE.md`: the design in force; V4-A1 … A10; the pin; the commands' timeouts and costs; what
  the harness builds; the stages F0–F5; the hard rules (the badge's imports, `KS`).
- `README.md`: status (pin, contract, the trim, F5), the caller workflow, the core branch.
- `docs/README.md`: the v4 note's pin (it still said `a874f87`).
- `submissions/README.md`: rule 4 (one build).
- `docs/v4/flock-baseline/BLUEPRINT.md`: §5 (the potential is the library's; `KS` through
  `KState.ks`; `errorCap` then and now) and D-1's note on GF(2^128).
- `docs/v4/FLOCK-BASELINE-FEEDBACK.md`: a dated "Since this report" paragraph; the report's text
  is unchanged.
- This record.

**`<core-pin>` placeholders** (the full or short hash of the final core head, for the
orchestrator): `.github/workflows/evaluate-entry.yml` lines 75 and 82 (full SHA); `AGENTS.md`, the
status's "The pin" and §7's introduction; `CLAUDE.md`, "The pin", "Where it is"; `README.md`,
"Status", "The pin"; `docs/README.md`, the v4 note.

## 7. Deviations

1. **The certificate ran twice**: on 4 CPUs, to measure the entry against caps set for a 4-vCPU
   runner (D-trim §8 item 1 left that unmeasured), and on 16 CPUs to compare with F4b. The benches
   ran on 16 CPUs, as F4.
2. **The comparator** was built from its pin by `build-kernels.sh` into `logs/f5/kernels`, not
   taken from `tools.env`'s read-only checkout.
3. **The guidance** keeps `docs/v4/FLOCK-BASELINE-FEEDBACK.md` as the dated report it is and adds
   one paragraph; the stage records F0–F4 and the reviews are untouched.
4. **One proof line changed outside the bridge** (`LawfulMonad.bind_assoc`, §5 item 1); no
   statement changed.

## 8. Open questions

1. Make `OProg.bind_assoc` and `OProg.queries_bind` `protected` in the core's library (§5 item 1)?
   The entry no longer depends on the answer.
2. **The caps on a real runner.** On 4 CPUs of this VM the build used 43 % of `build_s` and the
   kernel 30 % of `kernel_s`. A GitHub runner's 4 vCPUs are unmeasured for this entry.
3. **The season's time walls** (§4, **estimate**): beyond `queryCap` and `proofCap`, the next entry
   needs about 7× on the tree and 4.5× on the stream on this VM's 16 CPUs, and more on 4 vCPUs.
4. If the final core head moves proofs after the golf and review of `a283ff8`, the entry should be
   rebuilt against it; it depends on the statements of `KS`, `KState`, `KState.ks`,
   `complete_withError_zero` and the witness-sending library, which are not to change.
