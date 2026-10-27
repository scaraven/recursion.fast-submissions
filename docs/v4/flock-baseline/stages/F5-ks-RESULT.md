# F5: `spartan-srom` under V4-A9 and V4-A10 — RESULT, 2026-10-27

Status: **done; reviewed (`../reviews/F5-review.md`: one major, six minors) and fixed (§9).**
Commits: the entry `d5a53fa` and its golf `4829055` (branch `v4/spartan-srom`); the guidance
`90323cd`, and the golf with the review `f13ef73` (branch `v4/guidance`).

| | |
|---|---|
| Rules | the core's amendments **V4-A9**, the trim (`v4/trim-fat`, the core's pull request #18; `.contract/docs/v4/stages/D-trim-RESULT.md`), and **V4-A10**, textbook knowledge soundness (`v4/ks-standard`; `E-ks-RESULT.md`) |
| Harness | the core at **`a283ff8`**, the head of `v4/ks-standard` when the stage ran, which contains `v4/trim-fat`; the fix pass re-ran at **`8ad98e9`**, the final head (the core's pull request #19), §9. Each in a detached worktree (`logs/f5/org`, `logs/f5-fix/org`), removed after the runs |
| Entry | `d5a53fa` on `f07d028`, golfed in `4829055`; `claim.json` and `prover/prover.s` (`733b3a30…`) unchanged; the runs used copies, `logs/f5/entry/spartan-srom` (the migration) and `logs/f5-fix/entry/spartan-srom` (`git archive` of `4829055`) |
| Discipline | a private package tree, `logs/f5/pkgs` (a `cp -a` of `recursion.fast-v4/.lake/pkgs-local`, 9.2 GB, 2 min 2 s, `logs/f5/pkgs-copy.log`); the comparator `d03acab` built from its pin by `harness/ci/build-kernels.sh` into `logs/f5/kernels` (23.6 s, `logs/f5/build-kernels.log`); every command under `timeout`; `taskset` as stated per run; nothing written to shared trees or other worktrees |
| Logs | `logs/f5/` and `logs/f5-fix/` of the entry's worktree, `recursion.fast-submissions-ks` (gitignored) |
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
  (2 ^ 16)`: the same text; it now means V4-A10's statement, since the contract's `KS` changed.
  That statement is textbook knowledge soundness only for adversaries that make the verifier's
  queries themselves, which every prover in the deployment is: its extractor reads the final log,
  the verifier's answers included. Textbook implies it at twice the error (`Library/KS.lean`,
  `KSTextbook.ks`), and the converse fails: a lucky verifier is certified at `0` against about
  `2^-112` textbook (`Controls/Security.lean`, `lucky_ks`, `lucky_not_textbook`;
  `Contract/Security.lean`'s header at `8ad98e9`). This entry's extractor, the library's copy
  extractor, reads only `π`, never the log, so for it the two games have the same event
  (**paper**).
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
(`logs/f5/axioms.log`); the two further prints in that log, of the controls `certificateR_claim`
and `claim_negatives`, failed with `Unknown constant` because they named the namespace
`SpartanSrom`, not `SpartanSrom.NodeControls` (review m-4); the gate's closure check, over
everything `Solution` imports, covered them all the same. Re-run at `8ad98e9` with the right
names: all five depend on exactly `propext`, `Classical.choice`, `Quot.sound`
(`logs/f5-fix/axioms.log`).
The source rule: 66 files, 0 findings. The gate in both certificate runs at `a283ff8`: PASS,
closure of 33,518 constants, those three axioms, 3,830 modules (3,723 trusted, 28 pinned); at
`8ad98e9`, after the golf, 33,517 constants.

## 2. The certificate job (`evaluate.py cert`, Lean kernel)

`org-setup.sh` at `a283ff8` (`taskset -c 0-15`): **ok, 6 min 7 s** (`logs/f5/org-setup.log`). Steps:
organiser build 107 s, tools 9 s, allowlist and manifest 95 s (10,818 modules, 2 more than at
`01a25b0`: `Library/Prob`, `Library/KS`; 34,374 manifest entries), the badge's objects with the
`Mathlib.Tactic` closure 142 s, the service 14 s. The development build ran beside steps 3 and 4 on
other cores, so these are upper figures.

Three certificate runs, **all ok**, with the season's `[certificate]` caps (identical in both
season files, and unchanged at `8ad98e9`). The current one is the first column: the entry at
`4829055` against the final core `8ad98e9`, whose `cert.json` records every capped step and the
kernel's memory peak.

| Step (cap) | `8ad98e9`, 4 CPUs (`logs/f5-fix/cert4`) | `a283ff8`, 4 CPUs, `taskset -c 0-3` (`logs/f5/cert4`) | `a283ff8`, 16 CPUs, `taskset -c 0-15` (`logs/f5/cert16`) | F4b at `01a25b0`, 16 CPUs |
|---|---|---|---|---|
| render, source rule, manifest check | 18 s | 17 s | 8 s | — |
| **the one build** (`build_s` 600 s) | **272.9 s** (45 %) | 259.5 s (43 %) | 181.5 s | inside the comparator |
| **comparator, Lean kernel** (`kernel_s` 600 s) | **204.6 s** (34 %), peak **4.02 GB** (`peak_bytes` 4,017,922,048) | 182.3 s (30 %) | 171.6 s | 359.5 s with the build |
| binding | "one build (134 artifacts), read by the comparator, the gate and the badge build" | the same | the same | "byte-identical (134 artifacts)" after a rebuild |
| **gate** (`gate_s` 120 s) | **30.2 s** (25 %) | about 26 s (21 %) | about 22 s | — |
| **badge build** (`badge_s` 180 s) | **29.3 s** (16 %): 74 objects, the entry's 66, the badge's 2, and 4 Batteries and 2 Mathlib modules outside the precompiled closures | about 20 s (11 %): the same 74 | about 16 s: 68 (the 6 package objects were left in the private package tree by `cert4`) | — |
| manifest check after the badge | about 20 s | about 17 s | about 8 s | — |
| **whole job** | **9 min 39 s**, largest process 3.67 GB | 8 min 42 s, 3.68 GB | 6 min 47 s, 3.68 GB | 9 min 51 s |

(`logs/f5-fix/cert4.{log,json}`: every number of the first column but the first, the manifest
check after the badge and the whole job is `cert.json`'s (`build_s`, `comparator_s`, `gate_s`,
`badge_s`, `kernel_runs.lean.peak_bytes`). `logs/f5/cert4.{log,json}`, `logs/f5/cert16.{log,json}`:
`cert.json` at `a283ff8` recorded only `build_s` and `comparator_s`, so the gate's and the badge's
seconds there are from the work directory's file times.) Before the `8ad98e9` run the six package
objects that `logs/f5/cert4` had compiled into the private package tree were moved out of it, so
the badge build compiled them again, as the evaluation's certificate job does after restoring the
setup job's cache.

- **Against the caps on 4 CPUs at `8ad98e9`**: the build has 2.2× headroom, the kernel 2.9×, the
  gate 4.0×, the badge 6.1×; the kernel's peak is 4.02 GB against its 14G scope. These are 4 CPUs
  of a loaded QEMU VM (load average 8–15 during the run), not a GitHub runner.
- Every run: `built_modules` 67 (the 66 modules and `Challenge`), kernels `['lean']`, no nanoda
  (not run: it needs more than 20 GB on this entry, F3 §2.4).
- The badge `verify` was byte-identical across the three runs (`195377d6…`): the golf changed no
  compiled code.
- `environment` at `8ad98e9`: core `8ad98e99…`, manifest `ff5d9032…`, allowlist `fe740dbf…` (at
  `a283ff8`: manifest `c752a798…`, the same allowlist).
- `org-setup.sh` at `8ad98e9` on the same package tree: ok, 3 min 5 s, since the package objects
  were already built (`logs/f5-fix/org-setup.log`); allowlist 10,818 modules, 34,374 manifest
  entries.

## 3. The benchmark (`evaluate.py bench`, `taskset -c 0-15`, the certificate of the 4-CPU run)

**Smoke (`smoke.toml`): ACCEPT**, at `8ad98e9` in 15 s (`logs/f5-fix/bench-smoke.{log,json}`) and
at `a283ff8` in 14 s (`logs/f5/bench-smoke.{log,json}`).

| | F5 at `8ad98e9` | F5 at `a283ff8` | F4b at `01a25b0` (the same binary) |
|---|---|---|---|
| prover binary | `c5f5e1a8…`, 2,818,664 B | the same | the same |
| `T_tree` | **0.126 s** | 0.116 s | 0.142 s |
| `t_leaf`, `t_merge`, `t_link` | **0.0537 s, 0.0108 s, 0.0645 s** | 0.0560, 0.0106, 0.0666 s | 0.0702, 0.0144, 0.0846 s |
| **`S`** | **1.416** | 1.448 | 1.835 |
| root `acc` (bundle of 4, 2,169,384-byte file) | **398 ms** | 392 ms | 390 ms |
| statement canaries rejected | **1 (the root) + 8 (2 leaf and 2 node stream outputs × 2)** | the same | 76 tree + 20 stream canaries of every kind |
| DoS column | **64 inputs, none accepted, max 366 ms** (`dos/46.bin`), 49 over `T_V` | 64, none accepted, max 323 ms, 47 over | 64, max 401 ms |
| `T_V` | cap 0.011 ms (`T_triv,best` 0.105 ms), not enforced; 10 of 10 checks over it, max 501 ms | cap 0.018 ms, 10 of 10 over, max 549 ms | 19 of 19 over, max 505 ms |
| liveness | gone (V4-A9) | gone | ok, 30,820-entry log |
| service | 6.39 M calls/s on 1 thread, 112.0 M on 16; 0 refusals | 6.32 M, 108.0 M | 5.29 M, 102.5 M |

The prover is the same binary; the differences in `S` are single runs on a shared VM, not a faster
prover.

**Season (`season.toml`, at `a283ff8`; not re-run, the harness's benchmark is unchanged at
`8ad98e9`): REJECT**, for F4's reasons (`logs/f5/bench-season.{log,json}`,
`bench-season-stream.{log,json}`):
- all parts: "tree: prover tree exit 3; prover output (tail): 'spartan-srom-prover: oracle
  service: a Fiat–Shamir query of 1572898 bytes is above queryCap = 1048576 (the service refuses
  it)'", 15.4 s into the tree run, after 1,049,601 queries. `T_triv,best` 2.847 s, `T_V` 285 ms.
- `--parts calibrate,stream`: "stream outputs: stream leaf 0 rejected by acc". The leaf took 15.9 s;
  its file is 5,990,112 B with `π` = 2,791,559 B, above `proofCap`.

## 4. What the trim changed for this entry

- **Certificate.** One build: the byte-identical rebuild (173 s in F4) is gone, and the job went
  from 9 min 51 s (F4b, 16 CPUs) to 6 min 47 s on 16 CPUs and 8 min 42 s on 4 at `a283ff8`
  (9 min 39 s on 4 at `8ad98e9`). Every Lean step now has a cap, and this entry is inside each on
  4 CPUs (§2). The badge build compiles 6 package
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
  6.8×), and the stream's 257 leaves alone about 68 min against the entry's 900 s (15 min) of
  `stream_s` = 960 s (about 4.5×), before its merges (**estimate**, linear in `n`, and slower on 4
  vCPUs). `M` fell from 512 to 256.

## 5. Problems found in the core (at `a283ff8`; all three fixed in `8ad98e9`)

1. **(minor) The library's new `OProg.bind_assoc` and `OProg.queries_bind` are not `protected`.**
   `RecursionFast.OProg.bind_assoc` (`Library/Oracle.lean`, stated with `OProg.bind`) became
   visible as `bind_assoc` in every entry file with `open … OProg`, beside Lean core's exported
   `LawfulMonad.bind_assoc`. In `SpartanSromSnarkQueries.lean:62`, which builds at `01a25b0`,
   `rw [bind_assoc]` then elaborated to the library's lemma and failed: "Did not find an occurrence
   of the pattern `(OProg.bind ?p ?f).bind ?g`" (`logs/f5/dev-build-1.log`). The entry now names
   `LawfulMonad.bind_assoc`. Making the two lemmas `protected` would keep library additions from
   changing the meaning of names in existing entries. **Fixed in `8ad98e9`**: both are
   `protected`.
2. **(minor) `cert.json` records no duration for the gate or the badge build**, though both are
   now caps (`gate_s`, `badge_s`). It records `build_s` and `comparator_s`; F5 read the other two
   off file times. A submitter cannot see their margin from the result. **Fixed in `8ad98e9`**:
   `gate_s` and `badge_s` are recorded (§2).
3. **(minor, not new) The kernel run's memory peak is recorded only on an OOM kill**
   (`harness/rfh/sandbox.py`, `scope_oom`: a successful transient scope is gone when `MemoryPeak`
   is read, so `peak_bytes` is `null`). F4's 4.25 GB came from an external monitor. Unchanged
   since `01a25b0`. **Fixed in `8ad98e9`**: sampled while the run lives (4.02 GB here, §2).

Nothing else failed: the setup, both certificate runs, the smoke bench and the two season benches
ran as the documents say; the trim's new GitHub workflow structure was not exercised here (it has
not run on GitHub, D-trim §8 item 7).

## 6. The guidance side (branch `v4/guidance`, files kept apart from the entry's)

- `.github/workflows/evaluate-entry.yml`: synced with `harness/ci-template/evaluate-entry.yml` at
  `a283ff8`, unchanged at `8ad98e9` (the `select` and `report` jobs' 10-minute limits; the `split`
  description). Kept from the current file: line 1's header ("the core's harness/ci-template at
  the pin; copied to"). The two `CORE_COMMIT_SHA` values are the full `8ad98e99…` (§9).
- `AGENTS.md`: status and pin; §1 score and shapes; §2.2–§2.4 (the services, no logging mode, the
  `sk`-holding adversary against the new `KS`); §3.1 (the new `KS`, the bridge as a route,
  `KS.of_extracts`, `completenessCap`, the caps; the fix pass added the caveat, §9); §3.2 (no badge
  runs `ext`);
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

**The core pin in the text** (placeholders until the fix pass, now `8ad98e9`):
`.github/workflows/evaluate-entry.yml` lines 75 and 82 (the full SHA); `AGENTS.md`, the status's
"The pin" and §7's introduction; `CLAUDE.md`, "The pin", "Where it is"; `README.md`, "Status",
"The pin"; `docs/README.md`, the v4 note. The `.contract` gitlink is the orchestrator's.

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

1. ~~Make `OProg.bind_assoc` and `OProg.queries_bind` `protected`?~~ Done in `8ad98e9` (§5).
2. **The caps on a real runner.** On 4 CPUs of this VM the build used 43 % of `build_s` and the
   kernel 30 % of `kernel_s`. A GitHub runner's 4 vCPUs are unmeasured for this entry.
3. **The season's time walls** (§4, **estimate**): beyond `queryCap` and `proofCap`, the next entry
   needs about 7× on the tree and 4.5× on the stream on this VM's 16 CPUs, and more on 4 vCPUs.
4. ~~Rebuild against the final core head.~~ Done: certified and ACCEPTed at `8ad98e9` (§2, §3).

## 9. Fix pass (review `../reviews/F5-review.md`, golf `F5-ks-GOLF.md`; core `8ad98e9`)

The final core is **`8ad98e9`**, the head of `v4/ks-standard` and of the core's pull request #19
(its CI green on GitHub). Its fix pass documents `KS` as textbook single-output knowledge soundness
for adversaries that make the verifier's queries themselves (the user's option B), adds
`KSTextbook.ks`, `lucky_ks` and `lucky_not_textbook`, makes `OProg.bind_assoc` and
`OProg.queries_bind` `protected`, and records `gate_s`, `badge_s` and the kernel's memory peak in
`cert.json` (`.contract/docs/v4/stages/E-ks-RESULT.md` §9). The entry needed no Lean change for it.

| Finding | Disposition |
|---|---|
| **M-1** the rulebook calls `KS` "textbook" without the caveat | **Fixed.** `AGENTS.md` §3.1: a paragraph after the two conjuncts, "What 'textbook' means here", citing `Contract/Security.lean`'s header: `E` reads the final log, so `KS` is textbook only for adversaries that make the verifier's queries themselves, which every prover in the deployment is; textbook implies `KS` at twice the error (`KSTextbook.ks`); the converse fails (`lucky_ks`, `lucky_not_textbook`, about `2^-112`). A clause in `AGENTS.md`'s status and "What changed from v3", `README.md`'s status, `CLAUDE.md`'s pin and hard rules, `BLUEPRINT.md` §5, the entry's `README.md` ("What is certified") and `NOTES.md` (§4.7, §5), and §1 here, which also says why the gap does not bite on this entry (its extractor reads only `π`) |
| **m-1** "the rest v3's definitions word for word" | **Fixed.** `AGENTS.md` §3.1: `KS` is V4-A10's; `CompleteWithError` is v3's statement, now written through `prob` (the same statement by `completeWithError_iff`); the rest are v3's word for word |
| **m-2** "the recommended route" | **Fixed.** "One route, the organiser library's, is v3's potential (design §2.4)"; the `KS.of_extracts` sentence kept |
| **m-3** the DoS column's "extensions" | **Fixed.** `AGENTS.md` §7.6: "bit flips and truncations of the whole file"; the core's docstring is fixed at `8ad98e9` |
| **m-4** the two `Unknown constant` lines in `logs/f5/axioms.log` | **Fixed.** §1 says why they failed (the controls are in `SpartanSrom.NodeControls`) and that the gate's closure check covered them; re-run with the right names at `8ad98e9`: `certified`, `certificate`, `KS.ks`, `NodeControls.certificateR_claim` and `NodeControls.claim_negatives` all on exactly `propext`, `Classical.choice`, `Quot.sound` (`logs/f5-fix/axioms.log`) |
| **m-5** stale "not committed", "uncommitted", `745c7d8` | **Fixed.** The status and the header table here name `d5a53fa`, `4829055`, `90323cd` and `f13ef73`; the entry's `README.md` names `d5a53fa` and `4829055` on `745c7d8` |
| **m-6** the stream budget quoted two ways | **Fixed.** "the entry's 900 s (15 min) of `stream_s` = 960 s" in `NOTES.md` §4.7 and §4 here |
| Observation and golf suggestion 4: `AGENTS.md` §7.5's `bind_assoc` warning | **Dated.** "At `a283ff8` … made an unqualified `bind_assoc` ambiguous …; since `8ad98e9` both are `protected`, and the plain name is Lean's again." The entry's `LawfulMonad.bind_assoc` stays |

**The pin in the text.** Every `<core-pin>` is `8ad98e9`: `.github/workflows/evaluate-entry.yml`
lines 75 and 82 (`8ad98e9934852213232e83feee426d2cff786d4e`), `AGENTS.md` line 33 (status, "The
pin") and the §7 introduction, `CLAUDE.md` "The pin", `README.md` "Status", `docs/README.md` line 7.
`AGENTS.md`, `CLAUDE.md` and `README.md` also name the core's pull request #19.

**The re-runs at `8ad98e9`** (the entry at `4829055`; `logs/f5-fix/`), with the discipline of
F5: a detached core worktree at `logs/f5-fix/org` (removed afterwards), the private package tree
`logs/f5/pkgs`, the comparator of `logs/f5/kernels` (`build-kernels.sh --env-only`, the same
toolchain), every command under `timeout`.

| Run | Result | Log |
|---|---|---|
| `org-setup.sh`, `taskset -c 0-15` | ok, 3 min 5 s (the package objects already built) | `org-setup.log`, `org-setup-steps/` |
| `cert`, 4 CPUs (`taskset -c 0-3`) | **ok**, 9 min 39 s: build 272.9 s / 600, kernel 204.6 s / 600 at a 4.02 GB peak, gate 30.2 s / 120, badge 29.3 s / 180 | `cert4.{log,json}` |
| `#print axioms` (five names) | the three allowed axioms | `axioms.log` |
| `bench`, `smoke.toml`, `taskset -c 0-15` | **ACCEPT** in 15 s: `T_tree` 0.126 s, `t_leaf` 0.0537 s, `t_merge` 0.0108 s, `t_link` 0.0645 s, `S` = 1.416; root `acc` 398 ms; 1 + 8 statement canaries rejected; DoS 64, none accepted, max 366 ms | `bench-smoke.{log,json}` |

§2 and §3 carry the numbers beside the `a283ff8` runs. The season-shape runs were not repeated:
the benchmark code is unchanged between `a283ff8` and `8ad98e9` (only `evaluate.py`'s
certificate fields, `rfh/sandbox.py`'s peak sampling and a docstring of `rfh/checks.py` changed).

**Files changed in the fix pass.** Guidance (branch `v4/guidance`): `AGENTS.md`, `CLAUDE.md`,
`README.md`, `docs/README.md`, `.github/workflows/evaluate-entry.yml`,
`docs/v4/flock-baseline/BLUEPRINT.md`, this record. Entry (branch `v4/spartan-srom`):
`submissions/spartan-srom/README.md`, `submissions/spartan-srom/NOTES.md`; no Lean file.
