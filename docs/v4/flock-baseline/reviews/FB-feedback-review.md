# Adversarial review of `docs/v4/FLOCK-BASELINE-FEEDBACK.md` (commit `da5c99d`)

Reviewed: the feedback report at `da5c99d` (branch `v4/flock-baseline`, 929 lines), against the
entry's record (`BLUEPRINT.md`, `reviews/F0-route-ideation.md`, `F1-lean-review.md`,
`F2-prover-review.md`, `stages/F0…F3-*-RESULT.md`), the logs under `logs/` (`f3/`, `f2/`, `golf/`,
`golf-lean/`, `lean/`, `probes/`), the orchestrator's `logs/feedback-evidence.md`, and the core at
`81e1ebf` (`docs/DESIGN-v4-srom.md`, `docs/v4/BRIEF.md`, `docs/v4/FIXLIST.md`,
`docs/v4/reviews/C-design-attack.md`, `GB-golf.md`, `docs/v4/stages/B-harness-RESULT.md` §9,
`RecursionFast/Contract/{Certificate,Relation,Extractor,Security}.lean`, `Library/Compose.lean`,
`harness/{season,smoke}.toml`, `harness/rfh/{checks,bench}.py`, `service/PROTOCOL.md`,
`docs/DESIGN-cost-incentive-model.md`). Read-only except this file. Method: the three questions of
the `adversarial-review` discipline, run separately: (A) every number against its cited log or
RESULT, forming the expected value from the source before reading the report's; (B) each proposal's
soundness against the contract and the composition argument, before reading the report's own
soundness paragraph; (C) severity, staleness, fairness and length. Severity here: **major** = the
rules' authors would be misled or would change a rule on a wrong basis; **minor** = fix or answer.

## 0. Verdict

**Not ready to send; ready after the five majors and the minors below.** The record behind the
report is strong and the numbers are, with few exceptions, right: of 41 numbers spot-checked
(sizes, times, the frontier, nanoda, `T_triv`, service rates, golf speed-ups, line counts), 36
match their logs exactly; the five mismatches are listed as m1–m6. Every proposal is sound as a
matter of soundness (FB-10 included; §B below). The defects are in **what the report is read
against** (M1: eight items reported as open were fixed in the core before the report was
committed), **severity and framing** (M2: FB-1 is a known, accepted interim state, not a blocker,
and its "G3 fails" claim misreads G3), **one load-bearing estimate** (M3: the Q11 number is taken
from a 16-step leaf and does not describe a recursive node), **one unstated trust cost** (M4), and
**evidence hygiene** (M5: the medium finding FB-5 rests on a log outside `logs/`, and two
`TODO(orchestrator)` comments remain).

## 1. Major findings

### FB-R-M1. The report is read against `ea2e8ab`/`88d4566`; the repository pins `81e1ebf`, whose fix pass closed eight of the report's open items

*Evidence.* `.contract` is at `81e1ebf` since `d77478d`, the commit before the report's own
(`git log`). `B-harness-RESULT.md` §9 at `81e1ebf` records as **fixed**: Q2 (CompPoly's `BF64.Ext3`
and `.Bytes` in the default roots and the manifest; `org-setup.sh:27`), Q7 (the gate tree builds
exactly the comparator's targets; `evaluate.py:27` says modules `Solution` does not import are never
built), Q12 (the Lean kernel and nanoda in separate scopes; a memory kill is `over budget`, "unchecked,
not refuted", never "the certificate does not check"), Q13 (the prover's stderr tail and the
service's refusals quoted in a failure's reason), Q14 ("killed: out of memory (cap …, peak …)"),
RB-M1 (`T_V` compared by the best of `checker_runs`), Q8, Q10; Q6 is moot. The report presents all
of these as open:

- §0 "What was read": contract at `ea2e8ab`, design at `88d4566`; neither the pin nor the harness
  commit F3 ran (`a874f87`, which predates RA-M2) is named.
- §0.3 FB-4 row: "Q7 and Q2 (accepted); … resource kills reported as such" as proposed changes.
- FB-4 goals: "G-open, high until Q2 and Q7 land"; FB-4 proposals 1–3 (Q7, Q2 for CompPoly, the
  separate scopes and `oom-kill` reporting) are Q7, Q2 and Q12 as fixed.
- FB-2 "Rule": one timed check against the cap; RB-M1's best-of-N is not mentioned.
- FB-7 (4) "The defect is that the result JSON never said why the tree failed (H-4)": Q13.
- §2: H-1 "accepted", H-2 "accepted" (fixed for CompPoly), H-3, H-4, H-5 "proposed": fixed (Q7, Q2,
  Q12, Q13, Q14). H-17: Q6 is closed, as stated; Q3/Q4 remain doc passes.

*Why it matters.* The authors would re-plan work that is done, and the summary table's top-five
row for FB-4 is mostly closed. The honest reading of FB-4 after the correction is: the second kernel
(Q5, the user's decision), every pinned package as a root (new; see M4), and computability (Q4 doc
pass): **medium**, not high.

*Fix.* (i) State the three core states explicitly: the harness F3 ran (`a874f87`), the contract the
entry builds against (`ea2e8ab`, RA-M2), and the pin (`81e1ebf`, the B fix pass), and say the fix
pass was checked by reading B §9 and `evaluate.py`, not by re-running F3. (ii) Add a status column
to §0.3 and §2 with the values `fixed at 81e1ebf` / `queued (FIXLIST Qn)` / `proposed`. (iii) Move
the fixed items out of FB-4's body into one "fixed, with the fix" paragraph; lower FB-4 to medium.
(iv) In FB-2's rule, add RB-M1's statistic.

### FB-R-M2. FB-1 is not a blocker, and "G3's no cliff fails in practice" misreads G3

*Evidence.* G3 ([CM] §1): "Every entry that produces accepted proofs is ranked, however slow its
recursion; no measure of prover performance is a threshold. **(The caps of §3.5 bound the verifier
and the resources; they define what a valid entry is.)**" A non-recursive entry produces no
accepted proof at the season shape because of `proofCap`, which G3 itself carves out as the
definition of validity, not as a cliff. The design already states the consequence and adopts the
report's measure (3) word for word: §0 "No entry can run the season-1 shape (C-m10), so nothing is
ranked yet"; §2.8 "not claimed: that any certified entry fits the season-1 shape"; §4.3 and §7.3
"the first ranked shape should be the one the first certified recursive entry can run"; C-m10. The
report's severity scale defines blocker as "a goal cannot be met under the rules as they stand";
the goal G-chains ("fast BLAKE2s hash-chain proving comes first") is a statement about the score's
composition, not about ranking non-recursive entries, and the competition's subject is recursive
proofs. FB-1's G-chains line ("a chain prover that does not recurse is never ranked, however fast
it is") describes the design's intent, not a failure of it.

*What is new in FB-1 and worth keeping.* (1) the unranked frontier columns, (2) partial-stream
ranking, and the measured fact that until a recursive entry exists the board is empty and the
smoke shape is the only end-to-end check. (2) has a trade-off the report does not state: ranking
first by links accepted makes "links accepted" a lexicographic primary key, i.e. the kind of
threshold G2/G3 forbid (a 20 s-per-link entry that completes 512 links outranks a 0.2 s one that
fails at link 400 by `T_V`). That may be the right interim rule, but say that it suspends G2 as
well as G3 and is replaced by `S` once a full stream exists.

*Fix.* Severity **high** (or a new class "known and accepted; proposals"); delete the G3 claim and
the "blocker for G-chains" line; cite §3.6/§4.3/§7.3 as already adopting (3); state (2)'s tension
with G2/G3; keep the alternatives paragraph (the witness-sending estimate is right: 280 ns per
compression against the checker's 106–185 ns, so an interim shape with a floored `T_V` is won by the
trivial entry).

### FB-R-M3. FB-2 (3)'s Q11 estimate sizes a recursive node's verifier by a 16-step leaf; the report's own frontier shows a node-sized Ligero proof verifies in seconds

*Evidence.* FB-2 (3): "With the golfed product, one Spartan-class check is 0.5–0.8× of a runner's
178 ms cap, and two are 1.1–1.2× … A recursive node checks two children. So the choice … is close."
The 0.5–0.8× is the `n = 16` leaf (91–136 ms, `verify-abab.log`) and the 1.1–1.2× the bundle of two
such leaves (193–207 ms). A recursive node's *proof* is a proof of a node circuit of about `2^15`
compression-equivalents (F0 Q3, cited by FB-7), and `T_V` times `acc` on that one proof, not on
two 16-step leaves. The entry's own `acc` on larger Ligero proofs (F3 §4.3, pre-golf badge):
1,000 ms per leaf at `n = 1,024` (the `r = 1` root, 2,000 ms for two), 1,771 ms at `n = 4,096`;
scaling as about `n^0.4`, a `2^15`-sized proof is about 4 s pre-golf, about 2 s with the 2× golf,
ten times the 178 ms cap, `clmul` or not. For this PCS the proof size, not the field product, sets
`T_V`. The `clmul` bias (Q11) is decisive only for a log-verifier PCS (WHIR/Ligerito class; Flock
verifies natively in 54–64 ms at `2^14`–`2^16` on this VM, F0 §3, so 2–3× that in compiled Lean is
near the cap).

*Why it matters.* Q11 is an open design item to be "decided with the baseline's feedback report"
(design §7.3). A reader of FB-2 (3) would conclude the Ligero baseline is one `clmul` away from
`T_V`; the record says it is an order of magnitude away at node size.

*Fix.* Restate (3): the per-leaf numbers at `n = 16`, `1,024`, `4,096` with their scaling; the
conclusion that a √-size PCS cannot meet `T_V` at node size whatever `R` does for `clmul`; and that
Q11's options matter for log-verifier PCSs, where a 2× product cost is the difference. Keep the
recommendation to decide on runner numbers, and name the files to time: this entry's `r = 0` roots
at `n = 1,024` and `4,096`, not only the `n = 16` leaf and bundle.

### FB-R-M4. FB-4 (2) "every module of every pinned package as roots" is a trust decision, presented as a manifest size

*Evidence.* Gate rule 3 rejects a code-changing attribute in an untrusted module and reports one in
a pinned module as a note (F3 §2.2; B §9 Q2 for CompPoly's `@[csimp]`). Making ArkLib, VCVio,
PolyFun and "the Batteries modules that entries import" pinned by default means every `csimp`,
`implemented_by`, `extern` and `unsafe` in them is accepted on the badge path because the organiser
vouches for the package. That is exactly the G-trust question the hard rules exist for; the report
files it under G-open with "Cost: a larger manifest".

*Fix.* Say it is a trust-base change and offer the narrower options: roots added per package on an
entry's declared need (as Q2 did for CompPoly, the v3 precedent), with the organiser auditing that
package's attributes once; or an allowlist of attribute-free modules. Keep the useful part: a pinned
dependency must never be classed as entry code, and the message must not name a module the entrant
cannot change (H-2).

### FB-R-M5. Evidence hygiene: FB-5's headline numbers have no log under `logs/`, and two `TODO(orchestrator)` comments remain

*Evidence.* FB-5's 68 s / 183 s / 0.43 s and 970 KB come from the F1 review's probe; Appendix A cites
"the review's `attack-run.log` (its session scratchpad)". The file exists only in a scratchpad
directory, not under `logs/` (checked: it is not in `logs/lean/`); the report's own evidence rule is
"**measured**: a number with its log". The design has already copied these numbers into §4.3 as a
residual risk. Two HTML comments (`FB-2` after the badge-time table; `FB-5` after D-6) mark numbers
the authors are meant to read as current.

*Fix.* Copy `attack-run.log` and the probe source (`SromAttack.lean`) into `logs/lean/attack/` and
cite them, or label the numbers "measured by the F1 review; log not retained". Replace both TODOs
by one sentence each in the text ("the F1 fix pass's re-measurement is pending; the numbers above
are the pre-fix ones"), or fill them before sending.

## 2. Minor findings

**Numbers (pass A).**

- **FB-R-m1.** H-14 "The manifest check runs 5 times per job": `cert-closure/manifest.log` holds 3
  checks and `badge.log` one, so 4, as F3 §2.3 and friction 9 say.
- **FB-R-m2.** "695 `clang -c`" (FB-4 table, H-13) is the 0.25 s sampler's count
  (`cert-closure.rsmon.json`: 697 `clang` records); the build log says 4,590 jobs and F3 §2.3 says
  the objects of 986 package modules. Use F3's number or label the 695 "sampled".
- **FB-R-m3.** FB-6 "the service's `SIGN` takes 6–14 ms": F2 golf §4.1 says 6–18 ms of a 10–26 ms
  merge.
- **FB-R-m4.** FB-1 (1) "14 tree shapes and 4 stream shapes (`frontier-driver.log`)": the two driver
  logs hold 15 tree shapes (the smoke `r = 2, n = 16` included) and 2 stream shapes; the other two
  stream rows of F3's table are `bench-smoke` and `bench-season-stream`.
- **FB-R-m5.** FB-1's Flock-class arithmetic: "a GF(2^192) variant would be about 550–750 KiB … 64
  bundled leaves would therefore take about 25 MiB": 64 × 550–750 KiB is 34–47 MiB; 25 MiB is 64 ×
  Flock's own 400 KiB. "Or at most at link 2–3 at Flock's own proof size": three 406 KiB proofs
  exceed 1 MiB, so link 2 is rejected and one link is accepted. FB-9's "386 KiB" (Flock's README
  figure, via F0 Q4) and FB-1's "416,368 B (measured)" are the same proof; say which is which.
- **FB-R-m6.** FB-7's recursion-step estimate: `2^15` × 2.4–8.7 µs / 4 cores is 20–71 ms, not
  "20–40 ms", so the step total is about 30–100 ms. Also "37.6–38.7 ns per 64-byte block per
  connection" are GB §1.2's in-process kernel figures on one pinned core (37.6 is the 1 KiB-query
  case); say "kernel rate". The 7–26% chain-term share stands.
- **FB-R-m7.** FB-11 "15,788,764 kB": the log field is `peak_rss_kb` and the unit is KiB, which is
  F2-m3's whole point; write KiB (15.06 GiB is right).

**Wording that changes a conclusion.**

- **FB-R-m8.** FB-2 "What moved those times was craft, not protocol", item 1 (`byteAt`): the
  quadratic parse lived in F1's scratch runner `srom-run`, never in the badge (F2 §3.5; F3 measured
  0.2–1.3 s per check, parse included), and the 204 → 91 ms badge gain is V1 + V2 of the F1 golf;
  `byteAt`'s effect on the badge `acc` ("about 100 copies per leaf check", F1 §5) was not measured
  separately. Reword: two of the three items moved the badge time; the parse is a trap for an
  entrant's own tooling (Q4). The heading "at the season scale it mostly measures Lean compilation"
  overstates: after the golf `F.mul` is 42%, `chainMats` 31%, `colCheck` 27% (F1 golf §2), which is
  the protocol in compiled Lean; the evidence supports "a 2× craft component and a 2–3× compiled-Lean
  factor over native (0.044 s against 0.09–0.14 s)".
- **FB-R-m9.** FB-9 (1), grinding (checked as paper): the per-query bound `2^-g · d/|F|` is right in
  the potential framework (`step` charges a fresh query on average over its answers; the adversary
  needs an answer that is both valid and bad), and `g = 7` does cover `126/2^128` (0.98 · 2^-128).
  Two precisions: `CompleteWithError`'s "89 · 2^g attempts for δ = 2^-128" is per round
  (`(1 − 2^-g)^(89·2^g) ≈ 2^-128.4`); over `R` rounds the union bound needs about `(89 + ln R) · 2^g`.
  And option (2), lowering `errorCap`, also moves the threshold for chargeable collision-type events
  that `Security.lean` derives from `logCap` (224 bits at `2^-128`); say so.
- **FB-R-m10.** FB-10 is sound (pass B, below) but under-describes its footprint: "about 2 trusted
  lines" is the `acc` disjunct; `readSigned` is the trusted decoder (`Contract/Extractor.lean`), so
  the change is a trusted **format** change with its own positive and negative controls, `FORMAT.md`,
  `witWords`/`decodeWit_witWords`, the runner's signature canaries, and the harness's "unsigned
  trace" broken-prover check (B-RESULT end to end), which then holds only for non-empty traces. Also
  say that a query-free root then needs no service at all, so a record's `vk` field carries no
  information for such an entry (C-m9's statement should be amended). None of this is a soundness
  cost; all of it is scope.
- **FB-R-m11.** FB-5 (1): inputs "any reviewer may add" that "fail the entry at `verify_s`" are a
  post-hoc rejection path open to third parties. Say who adjudicates and when (before a record is
  confirmed), or make reviewer inputs publish-only and entrant-shipped inputs the failing class.
  Also cite design §4.3/§7.3, which already names "a crafted-input probe class" as the open fix: the
  proposal is a concretisation, not new.
- **FB-R-m12.** FB-8 "LLVM 23 emits `.prefalign` 428 times … 284 `.file` lines": F0 §1's counts are
  from the probe crates and v3's prover (`P/asm/t{1,2}/link.log`), not this prover's `raw.s`; cite
  as such (the 273,664 dropped lines are this prover's).
- **FB-R-m13.** FB-3's "Node 288, NodeControls 431, Queries 62, SnarkQueries 88" are pre-golf code
  lines (F1 RESULT §1); the F1 golf changed `NodeControls` −24 and `Queries` +7 (total lines). Say
  "pre-golf".
- **FB-R-m14.** FB-7 (4) "Keep `queryCap` as it is": FIXLIST Q15 already queues the doc statement
  (√-size commitments must split columns); cite it.
- **FB-R-m15.** H-10 cites `rfh/bench.py:180`; at `81e1ebf` the `os.cpu_count()` call is line 209.
  The item is correctly still open.
- **FB-R-m16.** FB-1's witness-sending estimate cites "280 ns per compression (F1 RESULT §6.1.8)";
  F1 §6.1.8 attributes it to stage A; B §8.6 gives the checker's 185 ns on the VM and design §3.5
  106 ns on a runner. Give both sides of the comparison from one machine.

**Calibration, fairness, clarity (pass C).**

- **FB-R-m17.** FB-6 medium → low: CM-R2 holds as the report says, the smoke shape's inability to
  show recursion is by construction, and the fix is a published column. FB-11 is not a finding on
  the rules (its proposal is "none to the cap"); fold it into FB-1's frontier and H-17's unit item.
- **FB-R-m18.** "What worked well" credits the feedback channel with "RA-M2, Q2, Q4, Q6 and Q7";
  the core also took up Q12–Q15 and RB-M1 within the stage, and the design §3.6 already carries the
  frontier. Credit them; it also makes M1's correction consistent.
- **FB-R-m19.** Open question 1's second and third sentences are assertions, not questions; open
  question 6 repeats "about 2 trusted lines" (m10); open question 9 (completeness and `proofCap`,
  D-5) is a real and good question but is not raised anywhere in §1; give it a home (FB-3 or FB-12).
- **FB-R-m20.** The summary table (§0.3) says "top five" and lists five rows while §1 has twelve
  findings of which three are high; consistent. But the FB-3 row's "FB-10" and the FB-4 row's
  "template projection" are not explained in the row; a reader of the table alone cannot act on
  them.
- **FB-R-m21.** The evidence list's item 8 (F0 Q5 point 8, the PROVISIONAL stub-`V` loophole: a
  non-checking `V` turns the harness into a prover timer) is not in the report. It belongs with
  C-m13 as one sentence, or say why it was dropped.

## 3. Pass B: soundness of the proposals, item by item

- **FB-10** (`SigOk` vacuous on the empty trace). Checked against `Compose.lean`'s `walk` and design
  §2.4: step 2 uses a child's signature only to conclude the trace is genuine or to return a
  `Forgery`; the empty trace is contained in every log, so neither the forgery outcome nor the
  `runSeq → runLog` lemma needs it. Step 3 then applies `final` on the run's `L` (`μ L < 1` is the
  composition's event; `KState.empty` gives `μ [] = 0` as well), so a query-free accepting `V`
  extracts a witness in `Rel` on every log. `V` with no queries is a pure function of `(vk, c, π)`;
  a child "whose acceptance depends on a value it cannot check" would need a query, and `runSeq []`
  with exact consumption returns `none` on any query. The `∀ vk` certificate, the EUF-CMA reduction
  and the PRF hybrid are untouched; C-m1 (no certified `V` trusts a signature) is unaffected because
  nothing is trusted less. The change enlarges `Rel (acc vk)` by unsigned query-free children only;
  the end-to-end statement (leaf clauses are chain facts) is unchanged. σ0 is already public in
  every bundle, so the `vk` binding the report says is lost was never load-bearing. **Sound as
  proposed**; footprint under-stated (m10).
- **FB-9 (1)** grinding: correct per fresh query; completeness bookkeeping per round (m9).
  **FB-9 (2)** lowering `errorCap`: a trusted constant and the `logCap` interplay (m9); the report
  rightly leaves the choice to the authors.
- **FB-1 (1)–(3)**: no trusted Lean, no relation change (G5 holds). (2) is in tension with G2/G3
  (M2), not with soundness. Partial-stream ranking is not gameable at `n_f = 2^16`: links accepted
  are bounded by `proofCap`/`T_V`/`qV`, not by time, and a bundler gets 0–1 links there.
- **FB-2 (1)–(3)**: runner and Library only; (3)'s number is wrong (M3), its recommendation stands.
- **FB-3 (1)–(2)**: Library and rulebook; no soundness effect. (3) is FB-10.
- **FB-4**: (2) is a trust decision (M4); (3) is fixed (M1); (4) template projection: the gate's rule
  4 and the badge disagree on computability today (F1 §7.1), and projecting `S.V`, `S.P`, `S.ext`
  in `Common.lean.in` is the right side to change; (5) is Q5.
- **FB-5 (1)–(2)**: runner only; adjudication (m11). (3) is right to defer.
- **FB-6, FB-7, FB-8, FB-11, FB-12**: no soundness content; FB-7 (2) correctly notes the trusted
  runtime grows and that soundness needs the service to sign only what it computed.

## 4. Cuts and merges (929 lines; about 600 is enough)

1. **§0.2** repeats F3 §0's verdict table and FB-1/FB-2's numbers: replace by four sentences and a
   pointer to F3 §0. (−30 lines)
2. **FB-4**: remove the fixed items (Q7, Q2, Q12–Q14) from the body; one paragraph "fixed at
   `81e1ebf`" with the fix; keep the successful-job table, nanoda, all-packages-as-roots (with M4),
   computability, Q5. (−25)
3. **FB-11 → FB-1 and H-17**; **FB-6 → FB-1** as "what `S` measures below the season shape"; the
   stream concatenation flag becomes H-19. (−60)
4. **FB-12 → FB-3** ("what every recursive entry must restate": `acc`, `AtMost`, the bundle). (−30)
5. **FB-10**: keep as the one trusted-change proposal, but move its byte arithmetic (the frontier
   effect) to FB-1's frontier table as a column "without per-slot σ". (−15)
6. **FB-7**: keep the inputs and the two results (7–26% of chain proving; 30–100 ms per step); move
   the arithmetic to an appendix. (−25)
7. **FB-2**: cut "Lean against native (not like for like)" and the two alternatives; the
   badge-time table stays. (−15)
8. **§2** H-table: mark H-1…H-5 fixed in one row each; merge H-12 and H-14 (setup) and H-7 with H-8
   (result JSON completeness and resolution). (−20)
9. **§3** is good and short; add the fix pass's uptake (m18). **§4**: drop the assertions in Q1 and
   Q6 (m19). **Appendix A**: keep; it is the index the authors will use.
10. The per-finding "Goals" blocks are the report's best device; keep them, but state each goal once
    (several repeat "G-trust: none" in two forms).

## 5. Disposition

| Id | Severity | What | Status |
|---|---|---|---|
| FB-R-M1 | major | eight items fixed at `81e1ebf` reported as open; core states not named | open |
| FB-R-M2 | major | FB-1 severity "blocker" and the G3 claim; (2)'s tension with G2/G3 | open |
| FB-R-M3 | major | FB-2 (3): Q11 sized by a 16-step leaf, not a node-sized proof | open |
| FB-R-M4 | major | FB-4 (2): all pinned packages as roots is a trust decision | open |
| FB-R-M5 | major | FB-5 evidence outside `logs/`; two TODO comments | open |
| FB-R-m1…m7 | minor | number corrections (manifest 4, clang 986/sampled, SIGN 6–18 ms, 15/2 shapes, 34–47 MiB and 1 link, 20–71 ms, KiB) | open |
| FB-R-m8…m16 | minor | wording that changes a conclusion (craft vs protocol, grinding completeness, FB-10 footprint, FB-5 adjudication, probe counts, pre-golf lines, Q15, line 209, one machine) | open |
| FB-R-m17…m21 | minor | calibration (FB-6 low, FB-11 folded), credits, open questions, table rows, the stub-`V` item | open |
