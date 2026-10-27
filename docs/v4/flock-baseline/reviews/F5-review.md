# F5 review: `spartan-srom` and the rulebook under V4-A9/V4-A10 (adversarial review)

Reviewed: the guidance commit `90323cd` (on `5a28f9b`, branch `v4/guidance`), the entry commit
`d5a53fa` (on `f07d028`, branch `v4/spartan-srom`) and their merge `ff40276`, in the read-only
worktree `recursion.fast-submissions-ks-review`, against the core at `8645c39` (branch
`v4/ks-standard`; the entry was migrated against `a283ff8`, the golf between them changes no
statement). Logs read: `recursion.fast-submissions-ks/logs/f5/`. Out of scope, as briefed: the
paired comparison, FB-5, Q11, Q5, anything on GitHub, the season-shape REJECT of this non-recursive
entry, and the KS definition's accepted gap itself (its *statement* in the rulebook is in scope).

Dated 2026-10-27.

## 0. Verdict

**Mergeable after M-1 and the minors.** The entry's certificate is the contract's new `KS` for every
`vk`, obtained through `KState.ks` with the query bound `2^16` and no other hypothesis; every
declaration header of the five changed modules is unchanged between `f07d028` and `d5a53fa`; the
closure is on `propext`, `Classical.choice`, `Quot.sound` (the gate: 33,518 constants; my own
rebuild against `8645c39`: §4); the claim `ε = 2^-129`, `δ = 0`, `qV = 2^16` is within the new
caps and matches the rendered challenge byte for byte in `declared`. The measurements in the
F5 record, the README and the NOTES match the logs, and every certificate time is labelled as 4 or
16 CPUs of the loaded development VM, not a runner. The rulebook agrees with the core at
`8645c39` on every cap, run count, canary, DoS and build rule I checked, and the caller workflow is
the core's template except for line 1 and the two placeholders. One major: the rulebook calls the
new `KS` "textbook" and nowhere states the deviation the core's own review (E-ks M-1) found and the
user accepted. Six minors.

## 1. Findings

### M-1. The rulebook states no gap in "textbook" knowledge soundness

- **Where.** `AGENTS.md` §3.1 (lines 297–316: "textbook single-output knowledge soundness in the
  random-oracle model (V4-A10). Two conjuncts …"), the status bullet at line 44–46; `README.md`
  line 46–48; `CLAUDE.md` lines 72–74 and 253–255; `submissions/spartan-srom/README.md` line 90
  and `NOTES.md` §4.7; `docs/v4/flock-baseline/stages/F5-ks-RESULT.md` §1.
- **Failure.** The contract's `KS` (`Contract/Security.lean:116–126` at `8645c39`) gives `E` the
  **final** log of the game `A.bind (V …)`, so the extractor also reads the verifier's fresh
  answers, which the textbook straight-line extractor never sees. The core's review
  `docs/v4/reviews/E-ks-review.md` M-1 exhibits a kernel-checked verifier `Vlucky` certified at
  error `0` whose textbook knowledge error is about `2^-112 > errorCap`; the user kept the final log
  (the orchestrator's brief: "textbook for adversaries that make the verifier's queries themselves,
  which every prover in the deployment is"). None of the files above says so. A submitter or a
  cryptographer reading `AGENTS.md` §3.1 is told the certificate is the textbook notion; the
  "What changed from v3" list (line 344) and §3.1's bullets list no deviation. The core's fix pass is
  adding this to `Security.lean`'s header, design §1.4 and BRIEF §5c; the rulebook, which restates
  the definition for entrants, must carry it too, and today it contradicts the core's review record.
- **Fix.** One sentence after the two conjuncts in `AGENTS.md` §3.1 (and a clause in the `README.md`
  and `CLAUDE.md` status lines): "`E` reads the final log, so it also sees the verifier's fresh
  answers, which the textbook extractor does not; the statement is textbook for adversaries that
  make the verifier's queries themselves, as every prover in the deployment does (the trace is
  submitted), and it admits a verifier that reads its witness off its own fresh answer at error 0
  (E-ks review M-1, `Controls/Security.lean` once the fix pass lands)." Cite the core's header
  paragraph once the fix pass has a commit.

### m-1. "v3's definitions word for word" is no longer true of `CompleteWithError`

- **Where.** `AGENTS.md` line 297–298: "`KS` is V4-A10's, the rest v3's definitions word for word,
  V4-1".
- **Failure.** `CompleteWithError`'s body now reads `prob (fun b _ => b = false) ((P c w).bind (V c))
  [] ≤ δ` (`Security.lean:133`), not v3's `failProb … ≤ δ`; it is the same statement by
  `Library/Completeness.lean`'s `completeWithError_iff`, which the completeness bullet (line 326)
  does cite. The sentence overstates textual identity.
- **Fix.** "`KS` is V4-A10's; `CompleteWithError` is v3's statement through `prob`
  (`completeWithError_iff`); the rest v3's word for word".

### m-2. "The recommended route is v3's potential (design §2.4)" is the rulebook's, not the design's

- **Where.** `AGENTS.md` line 309.
- **Failure.** Design §2.4 at `8645c39` (lines 75, 293) says "one route to a proof", "a library
  route"; BRIEF V4-A10's reason is "accept any correct proof technique"; `Security.lean`'s header:
  "A submitter proves `KS` by any correct argument. One route …". Nothing recommends it. The
  attribution is wrong and the nudge is the rulebook's own.
- **Fix.** "One route, the organiser library's, is v3's potential (design §2.4) …", keeping the
  `KS.of_extracts` sentence that follows.

### m-3. The DoS column does not make "extensions"

- **Where.** `AGENTS.md` §7.6, line 1215: "bit flips, truncations and extensions of the whole file".
- **Failure.** `harness/rfh/checks.py:124–146` (`dos_inputs`) at `8645c39`: kind 0 is random bytes
  of a random length, kind 1 a random `π` under the root's trace and signature, kind 2 bit flips in
  `π`, kind 3 bit flips in the file with a 30 % chance of truncation. No input is an extension of
  the file. The core's docstring (line 125–126) says "extensions" too; the rulebook copied it.
- **Fix.** Drop "extensions" here; report the docstring to the core.

### m-4. The axioms log has two errors the record does not mention

- **Where.** `docs/v4/flock-baseline/stages/F5-ks-RESULT.md` §1 "Checks" (`#print axioms` of three
  names); `logs/f5/axioms.log`.
- **Failure.** The log prints the three axiom sets and then `Unknown constant
  SpartanSrom.certificateR_claim` and `Unknown constant SpartanSrom.claim_negatives`: the two
  controls live in `SpartanSrom.NodeControls` (`SpartanSromNodeControls.lean:40, 554, 560`). So the
  record's "the controls are unchanged and still build, `claim_negatives` included" rests on the
  build alone, and the record does not say the two `#print axioms` failed. Harmless (the gate's
  closure check covers everything `Solution` imports, and my rebuild prints both on the three
  axioms, §4), but a record must say what its log says.
- **Fix.** Name the right constants or state that the two prints failed and what covers them.

### m-5. Status lines stale now that the stage is committed

- **Where.** `F5-ks-RESULT.md` line 3 ("done; not reviewed; not committed") and the "Entry" row
  ("`f07d028` with this stage's changes (uncommitted)"); `submissions/spartan-srom/README.md`
  line 37–39: "The entry is the commit `745c7d8`" although the Lean changed in `d5a53fa`.
- **Fix.** Name `d5a53fa` (entry) and `90323cd` (guidance) in the record's header and the README's
  "Certified" bullet; "reviewed: this file" once the fixes land.

### m-6. The stream's budget quoted two ways

- **Where.** `submissions/spartan-srom/NOTES.md` §4.7: "the stream's 257 leaves alone about 68 min
  against `stream_s` = 16 min"; `F5-ks-RESULT.md` §4: "against the entry's 900 s of `stream_s`".
- **Failure.** `stream_s = 960` s is the wall cap with 60 s of organiser overhead inside it
  (`season.toml`, PROVER.md §3); the entry's share is 900 s = 15 min. Both are defensible, but the
  NOTES' "16 min" is the cap the entry cannot use in full and the ratio "4.5×" in the record is
  computed on 900 s.
- **Fix.** NOTES: "against the entry's 900 s (15 min) of `stream_s` = 960 s".

### Observation (not a finding): a sentence that the core's fix pass will date

`AGENTS.md` §7.5, line 1173–1174: "the library's new `OProg.bind_assoc` and `OProg.queries_bind`
can make an unqualified name ambiguous under `open … OProg`". The orchestrator's brief says the fix
pass makes both `protected`; the entry's `LawfulMonad.bind_assoc` is right either way, but the
sentence should then say "were, before the fix pass `<commit>`, which made them `protected`".

## 2. What was checked and held (by the brief's six items)

**1. The certificate.** `SpartanSrom.KS.ks vk : RecursionFast.KS (Rel (accV LV vk)) (V LV vk)
WitnessSending.E εKS (2 ^ 16) := (kstate vk).ks (V_queries_le vk)` and
`certificateOf.secure vk := … (F.ks vk).elim fun k => k.ks (V_queries F vk)`, with `V_queries` the
functional bound `∀ H c π, ((V LV vk c π).queries H).length ≤ qVR1` and `qVR1 = 2^16` (=
`S.qV`). `KState.ks` (`Library/PaperTheorem.lean:160–165`) takes exactly a `KState R V E ε` and that
bound, no other hypothesis, so `secure` is the contract's `KS` for every `vk` at the entry's own
`ε` and `qV`. The five changed files (`git diff --numstat f07d028 d5a53fa -- '*.lean'`: 1/1, 1/1,
4/3, 9/4, 6/4) change two proof terms, one `rw`, two imports and docstrings; every `theorem`/`def`
header is identical, `Facts.ks : ∀ vk, Nonempty (KState …)` included, so `kstate`, `ks`,
`certificateOf`, `certificateR_of`, `certificate` and `certified` state what they stated. Nothing is
weakened: `KState` is the same structure with the same laws, now in `Library/Security.lean`. No
`sorry`, no `native_decide` (gate rule 1 and the source rule, 66 files, 0 findings); axioms the
three (gate; `axioms.log`; §4). `claim.json` (`1/2^129`, `0`, `65536`, `0`, `8`) renders to a
`declared` identical to `Solution.lean`'s (`logs/f5/render/Challenge.lean` differs from
`Solution.lean` only in the header comment, the `import SpartanSrom` and the two filled
definitions); `2^-129 ≤ 2^-120` (`εR1_le_errorCap`, proof unchanged), `0 ≤ 2^-40`, `qV = 2^16 ≤
2^16`.

**2. The measurements.** `cert4.json`/`cert4.log`: `build_s` 259.5, `comparator_s` 182.3,
wall 8:42.13, max RSS 3,675,644 kB (3.68 GB), `taskset -c 0-3`, status `ok`, gate `PASS`, 67
`built_modules`, binding "one build (134 artifacts) …", `environment` core `a283ff85…`, manifest
`c752a798…`, allowlist `fe740dbf…`. The gate and badge times, which `cert.json` does not record,
from the work tree's file times: `comparator-lean.log` 11:52:57.9 → `gate.log` 11:53:23.5 (25.6 s,
"about 26 s"); badge sources 11:53:23.7 → `.lake/build/bin/verify` 11:53:44.0 (20.3 s, "about
20 s"); then the manifest check to `badge.log` 11:54:01.5 (17 s). `badge.log`: 74 `:c.o` objects
(4 Batteries, 2 Mathlib, `Solution`, 65 `SpartanSrom*`, 2 `RFBadge*`). `cert16.json`: 181.5, 171.6,
6:47.33, 3,678,084 kB. `org-setup.log`: 6:06.91; the step lines are printed at each step's start
with the elapsed time (`org-setup.sh:37`), so 1 → 107 → 116 → 211 → 353 → 367 s gives build
106–107 s, tools 9 s, allowlist/manifest 95 s, objects 142 s, service 14 s, as the record says;
10,818 allowlist modules, 34,374 manifest entries. `bench-smoke.json`: `S` 1.44764, `T_tree`
0.11612, `t_leaf` 0.05595, `t_merge` 0.01063, `t_link` 0.06658, `root_check_ns` 391,647,320
(392 ms), `root_bytes` 2,169,384, canaries 1 + 8, DoS 64/0 accepted/max 323,100,390 ns
(`dos/10.bin`)/47 over `T_V`, `T_V` 10 of 10 over the 0.018 ms cap, max 548.7 ms, service 6.32 M
and 108.0 M calls/s, prover `c5f5e1a8…` 2,818,664 B, `prover.s` `733b3a30…`; wall 14.39 s.
`bench-season.json`: tree exit 3 at 15.442 s after 1,049,601 queries, `T_triv,best` 2,846.954 ms,
`T_V` 284.695 ms. `bench-season-stream.json`: `leaf_s[0]` 15.910 s, `store/stream/leaf0.bin`
5,990,112 B, "stream leaf 0 rejected by acc". `loc-before/after`: 17,901 → 17,903 code lines,
1,695 theorems. `pkgs-copy.log` 2:02.19; `build-kernels.log` 23.6 s. Every certificate figure in
the record (§2), the README ("8 min 42 s on 4 CPUs of the development VM"), the NOTES ("`taskset
-c 0-3`; the caps are for a 4-vCPU runner"), `AGENTS.md` §5.1 and §5.5 ("F5 measured … on 4 CPUs
of the development VM"; "not a runner") and `CLAUDE.md` says where it ran. The season-shape
arithmetic is right: 256 leaves of `2^16` at 15.9 s ≈ 68 min against 600 s (6.8×); 257 stream
leaves ≈ 68 min against 900 s (4.5×), marked estimate and linear in `n`.

**3. The rulebook against the core at `8645c39`.** Agree: `[certificate]` 600/600/120/180
(`season.toml`, `smoke.toml`); tree `r = 6`, `n = 2^18`, `tree_s` 600 (smoke 2, 16, 120); stream
`M = 256`, `n_f = 2^16`, `step_s` 60, `stream_s` 960 with 60 s organiser overhead and "about 3.1 s
per link" (PROVER.md §3:101–106); `per_kind` 2, `stmt-bit` on the root and `swapped-child` only
where a sibling exists (`checks.py:112–120`; the smoke's 1 + 8); DoS 100/64 inputs, `total_s` 180,
`item_factor` 10, fails on time or crash, accepted inputs recorded (`bench.py:353–361`); `verify_s`
10; `build_s`/`setup_s` 300; memory 11G/2G/4G, sandbox 12G (`evaluate.py:177`), comparator 14G;
every `evaluate.yml` job 30 min, `plan`/`attest` 10; one build with the artifacts hashed and the
manifest checked before the build and after the badge (`evaluate.py:218–232, 318, 394`); no
liveness, no logging mode, no inner proofs, no repeats, no medians, two benchmark jobs, `PART_S` 28
min; `errorCap = 2^-120`, `completenessCap = 2^-40`, `logCap = 2^96` over `Q + qV`; the `KS`
conjunct order and the `KState.ks` signature quoted in §3.1; `KS.of_extracts` (`Library/KS.lean:73`);
`sigTrust` through `adversary_wins`/`sigTrust_ks_iff`/`small_of_caps`; the badge's precompiled
closures and the 4.8 objects/s, 860-module figure (D-trim §9 m-1); the migration list (E-ks §3).
Stale-term sweep of the whole `AGENTS.md`, `CLAUDE.md`, `README.md`, `docs/README.md`,
`submissions/README.md` for 6 h, 360 min, repeats, medians, samples, `M = 512`, liveness, logging,
`pi±1`, `2^-128`, byte-identical, `Nonempty KState`, `failProb`, "exactly textbook": every hit is
historical and labelled (F3/F4, "was", "gone (V4-A9)"), or a measurement median (B-RESULT's 31 µs),
or the unimplemented ABBA comparison (§9). History: the diff `5a28f9b..90323cd` touches no
F0–F4 record or review; the feedback report gets one dated paragraph and its text is unchanged
(its "§6.3 gives each finding's disposition" holds: FB-6, 11, 12 were merged into FB-1 at the
review, and §6.3 lists FB-1–5, 7–10); the BLUEPRINT's two edits are labelled V4-A9/F5.

**4. The workflow.** `diff` of `harness/ci-template/evaluate-entry.yml` at `8645c39` against
`.github/workflows/evaluate-entry.yml`: line 1 (the header's "the core's harness/ci-template at
the pin; copied to") and lines 75 and 82 (`CORE_COMMIT_SHA` → `<core-pin>`); nothing else. So
`permissions: {}` at the top, `select` with `contents: read, pull-requests: read`, `evaluate` with
`contents: read, id-token: write, attestations: write`, `report` with `pull-requests: write` only,
`pull_request_target` gated on the `evaluate` label or a dispatch, the labelled SHA checked
against the pull request's head, the entry fetched by SHA inside the core's workflow, no secrets,
and the comment body built from the result JSON as data with `@` neutralised: all the template's,
unchanged. The template itself did not change between `a283ff8` and `8645c39`.

**5. `<core-pin>` placeholders** (`grep -rn 'core-pin'`), seven to fill, plus three descriptive
mentions of `CORE_COMMIT_SHA` that need no edit:

| File | Line | Form |
|---|---|---|
| `.github/workflows/evaluate-entry.yml` | 75 | `uses: …/evaluate.yml@<core-pin>` (full SHA) |
| `.github/workflows/evaluate-entry.yml` | 82 | `core_ref: <core-pin>` (full SHA) |
| `AGENTS.md` | 33 | status, "The pin" |
| `AGENTS.md` | 927 | §7 introduction, "still holds at the pin `<core-pin>`" |
| `CLAUDE.md` | 61 | "The pin", "Where it is" |
| `README.md` | 41 | "Status", "The pin" |
| `docs/README.md` | 7 | the v4 note |

Plus the `.contract` gitlink itself, still `01a25b0e6d0c03a78c156b685c0e59d3bdc1f056` at `ff40276`
(by design, for the orchestrator). The F5 record's own two mentions (lines 159, 179) describe the
placeholders and stay. The record's list of them is complete.

**6. Hygiene.** The Lean changes are minimal and the docstrings say what, not how. The rulebook
edits keep the surrounding register (short bullets, ids kept: V4-A9, V4-A10, D-trim §8 item 7,
E-ks §3, RF-M1, FIXLIST Q7). No dead text found beyond m-5. The merge `ff40276` is clean: against
`d5a53fa` it differs in the nine guidance files only; against `90323cd` in the entry root only.

## 3. Passes (the review skill's A/B/C, adapted)

- **A, specification.** Nothing new is specified by the entry; `KS` is the core's and its
  non-vacuity is the core's controls' business (E-ks §4). The entry's `ks` is non-vacuous at
  `qV = 2^16 ≤ logCap`. The one specification-level defect is M-1, at the rulebook's statement of
  what the certificate means.
- **B, fidelity.** Rulebook numbers and rules against the core's season files, harness and
  workflow: one wrong word (m-3, inherited from a core docstring), one misattribution (m-2), one
  overstatement (m-1); measurements against the logs: all match.
- **C, hygiene.** m-4, m-5, m-6.

## 4. My rebuild against `8645c39`

In my scratch area: a detached core worktree at `8645c39`, `.lake/packages` → the F5 private
package tree, built under `bwrap --ro-bind / /` (so the package tree, the toolchain and every
checkout stayed read-only; only the scratch area was bound writable), `taskset -c 16-31`,
`timeout 1500`: "Build completed successfully (1266 jobs)". Then an entry tree mirroring
`evaluate.py`'s `mkfresh` (the rendered `Challenge.lean` from `logs/f5/render`, the 66 modules of
`d5a53fa`, `lakefile.toml` requiring the core by path, the manifest with the packages inherited),
`lake build +Challenge +Solution` under the same bind, then `#print axioms` of `certified`,
`SpartanSrom.certificate`, `SpartanSrom.KS.ks`, `SpartanSrom.NodeControls.certificateR_claim` and
`SpartanSrom.NodeControls.claim_negatives`. Result: the entry builds green against `8645c39` (`lake` exit 0, 67 oleans: the 66 modules and `Challenge`; max RSS 4.15 GB; started about 13:58 UTC, finished 14:01:33 with the axioms run; my `tail` filter dropped `time`'s Elapsed line), and all five names depend on exactly `[propext, Classical.choice, Quot.sound]`; `#check` shows `SpartanSrom.KS.ks : ∀ vk, RecursionFast.KS (Rel (accV LV vk)) (V LV vk) WitnessSending.E εKS (2 ^ 16)`. So the record's open question 4 (rebuild against the final head) is answered for the golf commit; the fix pass still has to be re-checked once it has a commit. Logs:
`/tmp/claude-1000/-home-devops-Verified-zkEVM-recursion-fast/deb0fda2-5afe-4ae8-816d-bf1a4a32e03f/scratchpad/rebuild/{core-build,entry-build,entry-axioms}.log`
(the scratch area is session-local; the worktree is removed after this review).
