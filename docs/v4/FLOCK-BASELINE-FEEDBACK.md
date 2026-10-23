# Feedback on the v4 rules from the first entry, the Flock baseline (`spartan-srom`)

**Status.** This is the v4 baseline team's (stage F) report to the authors of the v4 rules, dated
2026-10-23. It has been revised after its review (`docs/v4/flock-baseline/reviews/FB-feedback-review.md`,
5 majors and 21 minors, all applied).

It draws on building and running the first v4 entry, `submissions/spartan-srom`, through four
stages:

- F0: the route and the probes.
- F1: the Lean entry, which is certified, with its review, golf and fix pass.
- F2: the native prover, with its review, golf and fix pass.
- F3: the entry run through the real harness.

**Three states of the core.** Each number belongs to one of these, and the report says which.
- `a874f87`: the harness F3 ran. It predates RA-M2.
- `ea2e8ab`: the contract the entry builds against. It includes RA-M2 (`acc` checks
  `|tr| ≤ qV`).
- `81e1ebf`: the repository's pin (`.contract`). Its `RecursionFast/` is `ea2e8ab`'s and its design
  text is `88d4566`'s. It adds stage B's fix pass, which closed FIXLIST Q2, Q7, Q8, Q10, Q12, Q13,
  Q14 and RB-M1. That fix pass was checked by reading `.contract/docs/v4/stages/B-harness-RESULT.md`
  §9 and `harness/evaluate.py`, not by re-running F3.

**The entry's state.** F3 measured the frozen commit `8111b71`. The current entry (`745c7d8`,
`10ad91e`) adds the golfs and fix passes. Its proofs are byte-identical to `8111b71`'s, and it has
not yet been run through the harness (F4).

**Conventions.**
- **Citations.** Records relative to `docs/v4/flock-baseline/`, written `F/`; logs as the records
  cite them (`logs/` is gitignored); core files as `.contract/<path>`.
- **Evidence tags** (the design's): **kernel**; **measured**, a number with its log; **estimate**,
  arithmetic on measured or published inputs; **paper**.
- **Machine.** Measurements are from the shared 32-vCPU development VM, under load, unless marked
  "runner". The VM has AVX2 and AVX-512F but no `pclmulqdq`.
- **`FB-n`** are findings on the rules. The draft's FB-6, FB-11 and FB-12 are merged into FB-1 and
  FB-3, and their ids are retired.
- **`H-n`** are harness defects, with the draft's ids. H-8 and H-14 are merged into H-7 and H-12,
  and H-19 is new.
- **The record's ids are kept**: V4-n/V4-An, C-Mn/C-mn, CM-n, RA-…, RB-…, FIXLIST Q1–Q15, the
  blueprint's D-n, F1-M2 and so on.

**Goals.**
- **G-chains**: fast BLAKE2s hash-chain proving first.
- **G-rec**: recursion at 100–200 ms per 2→1 step second.
- **G-trust**: a minimal trusted base.
- **G-open**: any proof system and any language.

**Severity.**
- **blocker**: a goal cannot be met under the rules as they stand.
- **high**: a goal is met only at a large cost or with a distortion.
- **medium**: a real cost or a misleading number, with a known fix.
- **low**: a friction or a cheap gain.

## 0. Summary

### 0.1 What was built

- **A certified entry.** It is v3's `spartan-chain` ported to the v4 contract (D-1): Spartan R1CS
  sumchecks over GF(2^64)/GF(2^192), ring switching, and Ligero with unique-decoding proximity.
  **Size.** 66 Lean modules, 17,901 code lines after the fix pass. At the port, 47 of 65 modules
  were v3's unchanged, 886 lines were new and 310 were changed. **Certificate.**
  `SpartanSrom.certificate : Certificate submission` is kernel-checked on `propext`,
  `Classical.choice` and `Quot.sound`, and the audit of all 3,600 declarations passes. **Claim.** `ε
  = 2^-129`, `δ = 0`, `qV = 2^16`, fuel `8t`. **Build.** 2 min 46 s clean, peaking at 4.12 GB
  (`F/stages/F1-lean-RESULT.md` §1–§3, §9.3).
- **σ0-bundle nodes** (D-2, `F/BLUEPRINT.md` §1.4, §2). A node proof carries its subtree as a clear
  witness, followed by the leaves' SNARKs. Every slot of the witness is signed by one signature σ0,
  on the empty trace. `V` re-runs the SNARKs with fresh queries. The extractor is the library's copy
  extractor, unchanged.
- **A native prover** (`F/stages/F2-prover-RESULT.md`, `F2-golf-RESULT.md`). It is std Rust, emitted
  as one `prover/prover.s` of 9,238,056 B. It targets `x86-64-v2`, with run-time `pclmulqdq`
  dispatch. Every Merkle and Fiat–Shamir hash goes through the service. Its leaf bytes equal the
  Lean `P`'s and v3's. Golfed, the smoke tree takes 0.131 s and a `2^16` leaf peaks at 2.47 GiB.

### 0.2 What the harness said (F3, at `a874f87`, frozen entry; `F/stages/F3-harness-RESULT.md` §0)

- **Smoke shape** (`r = 2, n = 16, M = 4`): **ACCEPT**, with two workarounds, both since fixed at
  `81e1ebf`: `Solution` importing every module (Q7), and CompPoly among the roots (Q2). `T_tree`
  0.896 s, root `acc` 978.8 ms, `t_leaf` 0.251 s, `t_merge` 0.037 s, `S` 6.666. The certificate job
  took 14 min 22 s with the Lean kernel.
- **Frontier.** Every accepted tree has `2^r·n ≤ 4,096` chain steps; the stream completes 5 links at
  `n_f = 16`.
- **Season shape: REJECT.** Tree: the service's `queryCap` refused a 1,572,898-byte absorb, 27.6 s
  into leaf 0. Stream: the pre-golf prover's leaf 0 was OOM-killed by the 11 GiB cgroup.
- **`T_V`** is unreachable at every shape the entry can run.
- **nanoda** needs more than 20 GB and more than 10 min on this entry.

<!-- TODO(orchestrator): F4 -->

### 0.3 The top five findings

| Id | Finding | Severity | Proposed change | Status |
|---|---|---|---|---|
| FB-1 | No non-recursive entry can run the season shape. `proofCap` stops bundles at `2^12` chain steps against `2^24`. Until a certified recursive entry exists the board is empty, and below the season shape `S` prices concatenation, not recursion | high | (1) publish every entry's frontier as unranked columns; (2) optionally, an interim partial-stream ranking, which suspends G2 and G3; (3) the first ranked shape is the first recursive entry's | (3) adopted (design §4.3, §7.3, C-m10); (1)–(2) proposed |
| FB-2 | `T_V` is microseconds at every shape a SNARK entry runs, so the smoke shape cannot test it. At node size, a √-size PCS misses the season cap by about 10×, with or without `clmul`. Lean-compilation craft moved this entry's times by 2× | high | report every check against the season-scale cap at every shape; a Library kit of proved fast primitives; decide Q11 on runner timings of node-sized proofs | Q11 open (design §7.3); rest proposed |
| FB-3 | A signed child is `π + trace + σ`, and the trace restates every hashed byte. Two signed `n = 16` leaves sent plainly are 1,089,384 B, over `proofCap`. Every non-recursive entry must design and certify a bundle (about 1,050 Lean lines here) and restate `acc` | high | a Library bundle generalised from this entry, plus `accWith` and `AtMost`; state the arithmetic in the rulebook | proposed |
| FB-4 | nanoda reached 20.9 GB and was still growing when killed at 10 min 1 s, so records rest on one kernel. Pinning packages by default is a trust decision, and the computability rule is undocumented | medium | Q5 (the user's) on this evidence; roots per package on declared need, with one attribute audit; project `S.V`, `S.P`, `S.ext` in the badge template | Q2, Q7, Q12–Q14 fixed at `81e1ebf`; rest proposed |
| FB-5 | Crafted proofs built from public parts took `acc` 68–183 s, against `verify_s = 60 s`. The entry fixed its own case (worst now 1.5 s), but the rules bound nothing, and random mutations never find such inputs | medium | a crafted-input column: inputs the entrant ships can fail the entry; inputs reviewers add are published only | open in design §4.3, §7.3; proposed |

The remaining findings: FB-7, the service tax, about 30–100 ms per recursion step (estimate);
FB-8, the assembly-only build; FB-9, `errorCap` against GF(2^128), with a grinding route; FB-10,
`SigOk` made vacuous on the empty trace.

## 1. Findings on the rules

### FB-1 (high). No non-recursive entry can run the season shape; until a recursive one exists the board is empty

**Rule.**
- The season shape (V4-11, `.contract/harness/season.toml`): a tree of `r = 6, n = 2^18`, and a
  stream of `M = 512, n_f = 2^16`.
- `proofCap = 2^20` (V4-13, `Contract/Relation.lean`).

G3 of the cost model carves out the caps: they "define what a valid entry is"
(`.contract/docs/DESIGN-cost-incentive-model.md` §1). So FB-1 does not violate G3. The design
already states the gap, and the plan:

- §0: "No entry can run the season-1 shape (C-m10), so nothing is ranked yet".
- §2.8: no claim that any certified entry fits.
- §4.3 and §7.3: the first ranked shape is the first certified recursive entry's.

**Goals.**
- G-rec, high: the season shape yields no `t_link` from any entry, so the stream offers no gradient
  to an entrant not yet there.
- G-chains, medium: a fast non-recursive chain prover is not ranked. That is intended (C-m10), but
  it leaves the board empty.
- G-open, medium: the caps exclude every non-recursive design at the season shape. The design says
  so (§2.8); the rulebook does not.

**The frontier (measured).** Sources: F3 §4.3 (`logs/f3/frontier-table.txt`), and F2 §3.3 with its
fix pass (`logs/f2/fix/links-n*.log`). The last column applies FB-10's proposal (no 4,776 B signature
per clear slot).

| Shape | Root `π` (B) | Verdict | Without per-slot σ (FB-10) |
|---|---:|---|---|
| `r = 0, n = 4,096` / `8,192` | 796,111 / 1,062,591 | ACCEPT / REJECT | unchanged (no slots) |
| `r = 1, n = 1,024` / `2,048` | 925,342 / 1,192,062 | ACCEPT / REJECT | — / 1,182,510 REJECT |
| `r = 2, n = 128` / `256` | 936,916 / 1,166,724 | ACCEPT / REJECT | — / 1,138,068 REJECT |
| `r = 3, n = 4` / `8` | 984,096 / 1,052,576 | ACCEPT / REJECT | — / **985,712 ACCEPT** |
| `r = 4, n = 1` | 1,676,344 | REJECT | 1,533,064 REJECT |
| stream, `n_f = 16` | link 6: 1,063,913 | 5 links | **6 links** (1,006,601) |
| stream, `n_f = 1,024` | link 2: 1,392,841 | 1 link | 1 link (1,373,737) |
| stream, `n_f ≥ 4,096` | leaf: 1,601,878 at 4,096; 2,791,559 at `2^16` | 0 links | 0 |

**What stopped what.**
- **`proofCap`** set the frontier. A bundle's `π` grows by one leaf SNARK plus 9,704 B of witness per
  leaf, so the largest accepted tree carries 4,096 steps: 4,096 times fewer than the season's `2^24`.
- **The season tree** stopped first at `queryCap` (FB-7).
- **The season stream** stopped at the 11 GiB prover cgroup (`season.toml`'s `11G`). The pre-golf
  prover needed 15,788,764 KiB (15.06 GiB) for a `2^16` leaf, and was killed at 11.14 GB RSS after
  25 s (F3 §4.2; F2 §4 with F2-m3). The golfed prover needs 2,585,312 KiB (2.47 GiB) for the same
  bytes, and a `2^18` leaf is estimated at about 10 GB (F2 golf §4.3, §6). So memory does not bound
  a well-engineered entry, and the golfed stream would stop at link 0 on `proofCap`.

**A Flock-class entry (estimate).** Sources: `F/reviews/F0-route-ideation.md` point 3 and Q3–Q4;
`F/stages/F0-probes-RESULT.md` §3–§4.

- **Proof size.** Flock's proof at `2^16` BLAKE3 compressions is 416,368 B, or 406.6 KiB
  (**measured** on this VM, F0 §3). Flock's README gives 386 KiB for its own configuration. Under
  `errorCap`, a GF(2^192) variant is about 550–750 KiB.
- **Tree.** 64 bundled leaves come to 25 MiB at Flock's size, and 34–47 MiB for the variant.
- **Stream.** One link is accepted: two proofs are 813 KiB, three exceed 1 MiB. The variant gets at
  most one.
- **Flattening.** A flat SNARK over `2^24` compressions needs a 32 GiB witness, at leanVM-Flock's
  2 KiB per compression (F0 §4).

So only recursion runs season 1 (C-m10).

**What `S` measures below the season shape** (the draft's FB-6, low).
- At every shape this entry runs, a merge asks no `QUERY`. It concatenates two files and signs the
  joined trace.
- `t_merge` was 0.019–0.055 s (harness mean 0.0373 s) and `o_est` was 0.065, and both read as a
  recursion overhead. Golfed, a merge takes 10–26 ms, of which 6–18 ms is waiting for the service's
  `SIGN` (F2 golf §4.1).
- CM-R2's tail bound holds as stated: `c = 5` at `n_f = 16` and `c = 0` at `2^16`. So the smoke
  stream lies inside the bundling capacity by construction, and cannot show whether an entry
  recurses.
- The fix is a published flag (H-19).

**Proposed changes.** No trusted Lean, no relation change (G5).
1. **Publish every entry's frontier** as unranked columns: the largest accepted tree on a fixed
   ladder of shapes, the stream links accepted before the first rejection, and the stopping reason.
   F3 did this by hand, over 15 tree shapes (the smoke shape included) and 2 stream shapes
   (`logs/f3/frontier-driver{,2}.log`). F3's other two stream rows are `bench-smoke` and
   `bench-season-stream`. Cost: a `frontier` part of `evaluate.py bench`, and a ladder in the season
   file.
2. **Optionally, an interim partial-stream ranking**: first by links accepted, then by `t_link` over
   those links. This makes "links accepted" a lexicographic primary key, which is the kind of
   threshold G2 and G3 forbid. A 20 s-per-link entry completing 512 links would outrank a 0.2 s one
   that fails at link 400 on `T_V`. If adopted, it is an interim rule that suspends G2 and G3, to be
   replaced by `S` once a full stream exists. It cannot be gamed at `n_f = 2^16`. Links are bounded
   by `proofCap`, `T_V` and `qV`, not by time, and a bundler gets 0–1 links.
3. **Already adopted**: the first ranked shape is the first certified recursive entry's (C-m10).
   Until then we ask only for (1).

**Alternatives considered.**
- **Raise `proofCap`, or count bundles as recursion.** Rejected: both re-admit what the caps exclude
  ([CM] §3.5, CM-R2).
- **An interim ranked shape with `T_V` floored at the season cap.** Rejected: witness-sending would
  win it (**estimate**, on the VM). The library's witness-sending tree recomputes chains at about
  280 ns per compression (stage A's fast twin, F1 RESULT §6.1.8). The season cap there is 267–310 ms
  (`T_triv,best` 2.668–3.097 s, at 159–185 ns per compression). So witness-sending passes up to
  about `2^20` steps, against this SNARK entry's `2^12`.

### FB-2 (high). `T_V` cannot be tested at the shapes a SNARK entry runs, and at node size a √-size PCS misses it by 10×

**Rule** (V4-12, design §3.5).
- One `acc` check (parse plus `accF`, in the badge, on one pinned core) must take at most
  `T_triv,best / R`, with `R = 10`.
- `T_triv,best` is the best of `checker_runs` runs of the organiser's compiled-Lean chain checker,
  over the tree's chains.
- Since `81e1ebf`, a check above the cap is re-measured up to `checker_runs` times, and its best time
  is compared (RB-M1).
- `T_V` is enforced in `season.toml` and only reported in `smoke.toml`.

**Goals.**
- G-rec, high: the season cap, about 178 ms on a runner, is the whole budget of a recursive node's
  compiled verifier.
- G-open, high: `T_V` decides which PCS families are admissible. This entry's times moved 2×
  through Lean-compilation craft, and binary fields pay for a software `clmul` (Q11, against V3-1).
- G-chains, medium: a bundle root fails `T_V` before `proofCap`.

**What happened (measured).**
- **At the shapes the entry runs, the cap is microseconds** (F3 §3, §4.4; `logs/f3/fr-tv-*.log`). At
  the smoke shape, `T_triv,best` is 103–154 µs, so the cap is 10.3–15.4 µs, against a root `acc` of
  946–979 ms. At `r = 1, n = 1,024`, it is 0.194 ms against 1,776 ms.
- **At the season shape:** `T_triv,best` is 2.668 s on the VM, a 266.8 ms cap
  (`logs/f3/bench-season.log`); 3.097 s in stage B, a 310 ms cap; 1.776–1.785 s on a GitHub runner,
  about a 178 ms cap (design §3.5).

| Badge `acc` (one core, parse + `accF`) | Pre-golf (F1 §5, F3 §4.3) | After golf and fix pass (F1 §9.3, `logs/lean/run/timings-fix.log`) | Against 178 ms |
|---|---:|---:|---:|
| `L` leaf, `n = 16` | 204–218 ms | 89–111 ms | 0.5–0.6× |
| bundle of 2 leaves, `n = 16` | 450–500 ms | 188–195 ms | 1.1× |
| bundle of 4 (the smoke root) | 931–979 ms | 404–619 ms | 2.3–3.5× |
| `L` leaf, `n = 1,024` (half the `r = 1` root) | about 1,000 ms | — | — |
| `L` leaf, `n = 4,096` (the `r = 0` root) | 1,771 ms | — | — |

**What moved the times** (F1 golf §2). Two items moved the badge time:
1. a proved Karatsuba GF(2^64) product over `clmul32`, at 25 ns against 85 ns, for +343 proof lines;
2. a prefix decoder, so a bundle no longer packs its SNARK bytes at 0.2 µs per byte (60 ms of a
   297 KB bundle, F1 RESULT §7.4).

What is left is the protocol in compiled Lean: `F.mul` 42%, `chainMats` 31%, `colCheck` 27%. That is
about 2–2.5× the native verifier's 0.044 s replay of an `n = 16` leaf (F2 §4). The comparison is
not like for like: the replay does no trace hashing and uses the portable product.

A separate trap is in entrants' tooling, not the badge (Q4). Compiled `ByteArray.data` copies the
array, which made the entry's own runner `srom-run` quadratic: 87.8 s for 539 KB (F2 §3.5).

**Node size.**
- A recursive node's proof proves a circuit of about `2^15` compression-equivalents (F0 Q3), and
  `T_V` times `acc` on that one proof.
- This entry's Ligero leaves scale as about `n^0.4`: 0.2 s at 16, 1.0 s at 1,024, 1.77 s at 4,096
  (pre-golf).
- A `2^15`-sized proof is therefore about 4 s pre-golf, and **about 2 s golfed: ten times the
  runner's 178 ms cap**, with or without `clmul` (**estimate**).
- For a √-size PCS, the proof size sets `T_V`, not the field product.
- Q11's options matter for log-verifier PCSs (WHIR, Ligerito). Flock verifies natively in 54–64 ms at
  `2^14`–`2^16` on this VM (F0 §3). At 2–3× in compiled Lean that is 110–190 ms, right at the cap,
  so a 2× product cost is the difference.

**Proposed changes.**
1. **Report every check against the season-scale cap, at every shape.** Calibrate `T_triv,best` on
   `2^24` compressions in every job, smoke included. One checker run takes 2.7–3.1 s on the VM and
   about 1.8 s on a runner. Publish each time against `T_triv,best(2^24) / R`, beside the shape's
   own cap. This entry would have seen at the smoke shape: a 0.98 s root against 0.18–0.31 s. Cost:
   the runner only.
2. **A Library kit for compiled verifiers**, beside `Library/Fast.lean`'s hashes, so that `T_V`
   compares protocols, not craft. Cost: 0 trusted lines. It would contain: in-place byte readers; a
   prefix decoder of `encode W ‖ T`; this entry's proved GF(2^64) product (`FieldBase.clmul32`,
   `mul_eq_mulLoop`); each with its equality theorem.
3. **Decide Q11 on runner timings of node-sized proofs, not 16-step leaves.** Time this entry's `r =
   0` roots at `n = 1,024` and `4,096`, beside the `n = 16` leaf and bundle. Time a log-verifier
   proof of about `2^15` compressions once one exists. None of these has been timed on a runner yet.

### FB-3 (high). A signed child restates every hashed byte, so every non-recursive entry must invent a bundle and restate `acc`

**Rule.**
- In the node clause (`Rel`, `Contract/Relation.lean`), a child is `(π, tr, σ)`, and `acc` needs the
  whole trace (`Contract/Certificate.lean`).
- `proofCap` counts the node's own `π`.
- Under witness-sending, that `π` holds each child's `π`, trace and signature (`readSigned`,
  `Contract/Extractor.lean`; `Library/WitnessSending.lean`).

**Goals.**
- G-open, high: a Merkle-based SNARK entry must design, certify and implement its own node format
  before a tree of depth 1. Here that took: about 870 Lean code lines before the golf: `Node` 288,
  `NodeControls` 431, `Queries` 62, `SnarkQueries` 88 (F1 RESULT §1); 180 more for a byte-level node
  reader in the fix pass (`SpartanSromNodeBytes`, F1 §9.1); about 340 Rust lines (`make.rs`,
  `acc.rs`).
- G-chains, medium: the bundle sets FB-1's frontier.
- G-rec, low: a succinct node does not carry its children, but a node circuit hashes the same
  restated bytes, about 1.6× a public Merkle step per 64-byte query (design §4.2).

**What happened (measured).**
- **The trace restates the opened columns** (F0 §2, F2 §3.3). At `n = 16`, a leaf's `π` is
  143,711 B, its trace is 3,533 entries and 390,203 B, and its signed file is 538,698 B: 3.7× `π`
  (2.1× at `n = 65,536`).
- **The plain node fails.** The library's plain node over two such leaves is 1,089,384 B, 40 KB over
  `proofCap` (F1 RESULT §5).
- **The σ0-bundle (D-2) needed three pieces of its own**: a static `Σ qBound ≤ 2^16`, since `qV`
  bounds one `V` run; a check that the witness is a clear tree; a strong induction for `final`
  (`clear_acc`).
- **`acc` must be restated.** `V`'s node branch cannot call `Submission.acc`, which takes the
  submission being defined. So the entry restates it (`accWith`) and proves `accV_eq_acc` by `rfl`.
  Every change to `acc` must then be mirrored by every recursive entry. RA-M2 was one such change,
  and the same core diff also broke `wordBytes` (F1-m1).
- **`AtMost`.** Before RA-M2, node completeness also needed a path-uniform `AtMost` (150 lines, F1
  RESULT §7.2), because `KS`'s query bound ranges over oracle functions.

**Proposed changes.** Library and rulebook only; 0 trusted lines; no soundness effect.
1. **A Library bundle**, untrusted and kernel-checked: this entry's node branch, generalised over
   any leaf verifier with a static per-leaf query bound. Reviewed once, not once per entry. It
   holds: the `C`, `N` and `B` branches; `final` from the leaf's own `final` on the same log (`k`
   SNARKs cost no extra error, F1 review §3.2); the `AtMost` bound; completeness through the plain
   node; the controls; a reference byte format.
2. **Library `accWith V qV vk c p`**, with `Submission.acc S = accWith S.V S.qV` by `rfl` and a fast
   twin, plus `OProg.AtMost` and its algebra. A change to `acc` then changes one definition.
3. **The rulebook** (`AGENTS.md`, `harness/FORMAT.md`) states the arithmetic: a signed child is `π +
   trace + σ`; a Merkle-based SNARK's trace is about `|π|` or more; so plain witness-sending of two
   such children exceeds `proofCap`.
4. **Drop the per-slot signature** (FB-10).

**An observation (D-5).** The Lean `P` has no signer, so its node proofs send witnesses plainly and
exceed `proofCap`. Certified completeness is about `V`, not `acc` (v3 §6.4, design §2.6), so it
covers proofs the harness never accepts (§4 question 7).

**Alternatives considered.**
- **A child's trace by digest.** Rejected: `acc` must run `V` on the trace.
- **`proofCap` on `π` plus the children's traces.** Rejected: it changes the succinctness cap for
  everyone.

### FB-4 (medium). The certificate job: one kernel on CI, and a trust decision hidden in "pin the packages"

**Rule.**
- V4-A2: a separate certificate job, with the Lean kernel mandatory and nanoda where it fits.
- Q5: CI checks with the Lean kernel only.
- The tools: `harness/evaluate.py cert`, `harness/org-setup.sh` and `harness/badge/Common.lean.in`.

**Fixed at `81e1ebf`, from the baseline's reports** (`B-harness-RESULT.md` §9).
- **Q7.** The gate tree builds exactly the comparator's targets, with byte equality both ways.
  Modules `Solution` does not import are never built.
- **Q2.** CompPoly's `BF64.Ext3` and `.Bytes` are default roots. Their 28 modules are pinned, and its
  `@[csimp]` lemma is a note.
- **Q12.** The kernels run in separate scopes. A memory kill is "over budget", that is, "unchecked,
  not refuted".
- **Q13 and Q14.** These cover the failure reasons (H-3 to H-5).

These address F3's three harness REJECTs (runs 1a, 1b and 1f). That they are gone rests on reading
the fix; F4 re-runs them.

**Goals.**
- G-trust, medium: records rest on one kernel.
- G-open, low: the computability rule is undocumented.

**What happened (measured).**
- **nanoda** (F3 §2.4). On the entry's 226 MB export, it grew by about 2.1–2.2 GB per minute. In the
  harness's 14 GiB scope it was killed at 13.65 GB, after 375 s. Alone, under a 20 GB cap, it was
  OOM-killed at 20.9 GB after 10 min 1 s, still growing, using about 1.2 of its 4 threads
  (`logs/f3/nanoda-standalone/`). Stage B saw at least 17.6 GB on the witness-sending entry; v3 saw
  52 GB on one lemma. So the user's Q5 decision now has its evidence: more than 20 GB and more than
  10 min on a 17k-line certified entry.
- **The successful job** (F3 §2.3; it fits a 16 GB runner, but has not been timed on one):

| Step | Wall | Peak |
|---|---|---|
| comparator (the Lean kernel about 192 s of it) | 8 min 33 s | 3.62 GB |
| gate-tree rebuild; gate | 3 min 30 s; 21.8 s | — |
| badge build (objects of 986 package modules: 952 Mathlib, 28 CompPoly, 6 Batteries; 4,590 jobs) | 73.7 s | — |
| **total** | **14 min 22 s** | **4.11 GB** |

- **Computability.** The badge compiles the whole `Submission`, so a noncomputable `ε : ℝ≥0` fails
  the badge build, while the gate accepts it (F1 RESULT §7.1, `logs/lean/noncomputable-probe.log`).
  Q4 put this in design §3.3, but not yet in `AGENTS.md`.

**Proposed changes.**
1. **Q5.** Run nanoda off CI, on a machine with well over 20 GB, for records only, and publish which
   kernels ran.
2. **Pinned packages are a trust decision, not a manifest size.** A pinned package's `csimp`,
   `implemented_by` and `extern` are accepted on the badge path, on the organiser's word. So add
   roots per package on an entry's declared need, with one audit of that package's attributes, as Q2
   did for CompPoly (the v3 precedent). A candidate is `Batteries.Data.BitVec.Lemmas`: untrusted
   today, and with no code attribute (F1-m4). Do not add every pinned package wholesale. Keep the
   rule that a pinned dependency is never classed as entry code.
3. **Computability.** Project `S.V`, `S.P` and `S.ext` in the badge template, so `ε` and `δ` may stay
   noncomputable. The gate (rule 4) and the badge disagree today, and the template is the side to
   change.

### FB-5 (medium). Crafted proofs make `acc` slow, and the rules bound nothing

**Rule.**
- `acc` is "the check any third party runs later with the published `vk`"
  (`Contract/Certificate.lean`).
- The harness caps a check at `verify_s = 60 s`, and publishes the maximum over random mutations
  (`harness/rfh/checks.py`, `dos_inputs`).
- The design names "a crafted-input probe class" as the open fix (§4.3, §7.3, C9).

**Goals.**
- G-trust, medium: one published bundle yields σ0, which signs every query-free slot, so anyone can
  build slow proofs from public parts.
- G-rec, low: node circuits are fixed-size; only native checkers are exposed.
- G-open, low: the fix restricts the entry's own format (D-6).

**What happened (measured).**

| Proof (≤ 1 MiB, signed with the public σ0) | Before (F1 review) | After D-6, in-place reads | Final (`nodeFast`) |
|---|---:|---:|---:|
| `N` chain, depth 100, `n = 1` (970,448 B) | 68.5 s | 54.5 s | **0.46 s** |
| `N` chain, depth 100, largest clear leaf (`2^20`; then `4,096`) | 183 s | 60.1 s | **0.69 s** |
| `B` whose clear tree is that chain (rejected) | — | 50.8–51.4 s | **1.3–1.5 s** |
| one `C` leaf, `n = 2^20` | 0.79 s, accept | 0 ms, reject | 0 ms, reject |

The first column is F1-M2's; the review's log was not kept under `logs/`, and F1 RESULT §9.3 quotes
it. The other columns are `logs/lean/run/attack-after-{1,B-1}.log` and `attack-final.log`.

- **The causes, and their fixes.** `C` recomputed up to `chainCap` steps. D-6 caps clear leaves at
  `2^12`, losing no accepted proof. `N` re-decoded every child at every level, at about 1 µs per
  byte. A byte-level reader now validates itself against a proved encoder (`nodeFast_sound`).
- **The honest proofs.** The 2-leaf bundle took 0.43 s at the review, and takes 188–195 ms now. The
  smoke root takes 404–619 ms.
- **The worst measured case** is now 1.5 s. That is a measurement and an argument, not a theorem
  (F1 §9.3).
- **The DoS column cannot reach this.** Its random bytes, random `π` with the root's trace, and bit
  flips (`checks.py:131`) never reach `V` with a valid signature. Its maximum at the smoke shape was
  443 ms.

**Proposed changes.** These concretise the design's open fix, in the runner only.
1. **A crafted-input column.** The entrant ships its own worst cases and their generator (`dos/`),
   and these fail the entry at `verify_s`. Reviewers' inputs go on a public list and are published
   only. One becomes failing when a maintainer adjudicates it, before a record is confirmed.
2. **The rulebook states the amplifier.** An empty-trace signature, published once, signs every
   query-free slot under that `vk`. So a verifier must bound its cost on such inputs: both chain
   recomputation and the decoding at each nesting level.
3. **Deferred**: an obligation on `V`'s step count, since `OProg` has no cost semantics.

### FB-7 (medium). Every hash through the service: small here, tens of milliseconds per recursion step

**Rule.**
- V4-14: every oracle query goes to the service, Merkle hashes included.
- `service/PROTOCOL.md`: at most `2^20` bytes per query, and `SIGN` re-evaluates every query (C-m4).
- C-m8: the service's speed is in every score.

**Goals.**
- G-rec, medium: about 30–100 ms of service time per recursion step.
- G-chains, medium: 7–26% of a Flock-class prover's time.
- G-open, low: large absorbs must be chunked.
- G-trust: none; this is the price of closing O-25.

The first two are **estimates**, from measured inputs (Appendix A).

**What happened (measured).**
- **The pre-golf tax was small** (F2 §4): the service cost 1.4–10% of proving. At `n = 16`, the cost
  was 153 sequential Fiat–Shamir round trips of 57–78 µs each. At `n ≥ 4,096` it was at most 2.4%. A
  `2^16` leaf pushes 525,034 queries (1.09 GB), at about 1.8 GB/s on 16 connections.
- **The share grows with the prover's speed.** The golfed prover is 2.6–4.5× faster. The keyed
  in-process Merkle phase is 4.3–4.4% of a leaf at `n = 4,096–16,384`
  (`logs/golf/final-timings.log`). The Fiat–Shamir round trips take 5.1–7.2 ms, 9–15% of an `n = 16`
  leaf's 49–56 ms of proving (F2 golf §4.1).
- **Each merge's `SIGN`** re-hashes the whole concatenated trace.
- **`queryCap`** stopped the season tree (F3 §4.1). The service refused a 1,572,898-byte absorb of
  the Ligero row `ū`, after 1,049,601 Merkle queries (4.33 GB) and 27.6 s.

**The estimate (Appendix A).**
- Merkle hashing through the service costs 2.4–8.7 µs of core time per Flock-class compression:
  **7–26% of proving**, on the same cores.
- A recursion step of about `2^15` compression-equivalents spends 20–71 ms on Merkle hashing (over
  4 cores), 5–18 ms on Fiat–Shamir and 3–8 ms on `SIGN`: **about 30–100 ms**.
- That is a third or more of the 100–200 ms target in M4-Max units. The share is smaller on a
  runner, where the step itself is slower.

**Proposed changes.**
1. **Publish the service's CPU time per run** (its cgroup's `cpu.stat`). Cost: the runner only.
2. **A shared-memory batch transport** (RO-9), and a documented low-latency path for sequential
   Fiat–Shamir queries. The golf's polled connection cut the round trips from 9.6 to 5.6 ms per `n =
   16` leaf at 4 threads (F2 golf §2.9). The trusted runtime grows. Soundness holds as long as the
   service computes every answer and signs only what it computed.
3. **W5 stays the recorded fallback** (V4-14). It is not recommended, because it rests on an
   extractability heuristic.
4. **`queryCap` is right.** Its consequence for √-size commitments, that columns must be split, is
   queued as FIXLIST Q15. Since `81e1ebf`, the refusal reaches the result (Q13). The F2 fix pass
   makes the prover refuse such a query locally, with a message.

### FB-8 (medium). The assembly-only build works, but costs a sanitiser, a 9 MB generated file and reviewability

**Rule** (V4-9, design §3.3). The prover is `prover/*.s` in GNU `as` syntax, linked by the runner's
`gcc -static -pthread … -lm`, with no other input.

**Goals.**
- G-open, medium: std Rust works only with fat LTO, `--emit asm`, and a filter for LLVM 23's output.
- G-trust, low: soundness never depends on the prover (C-m7). But a 9 MB `.s` cannot be reviewed
  for gaming, and reproducibility rests on the entry's script.
- G-chains, low: CPU dispatch is the entry's job.

**What happened (measured).**
- **GNU `as` 2.46 rejects LLVM 23's raw output** (F0 §1, on the probe crates and v3's prover,
  `logs/probes/asm/t{1,2}/link.log`). `.prefalign` appears 428 times. DWARF-5 `.file N "dir" "file"`
  lines from std's bitcode appear 284 times, and `-C dwarf-version=4` does not help.
- **The workaround.** This prover's `sanitize-asm.py` drops 273,664 debug lines (F2 §2). The result
  is a `prover.s` of 9,238,056 B, emitted in 58–65 s.
- **Reproducibility.** The build is deterministic across three clean builds and through the
  sandboxed build, and it is pinned by `rust-toolchain.toml` (F2 fix pass, F2-m2).
- **Not tested.** The runner's binutils 2.42. By reading, no newer directive remains (F2 review §3).
  `pclmulqdq` on real hardware: checked under QEMU TCG only. The `x86-64-v2` binary on a pre-AVX2
  CPU: static glibc 2.43 needs AVX2 at start-up (F2 §2).
- **Repository cost.** Every prover change rewrites megabytes of a committed, generated file.

**Proposed changes.** Either (1) or (2), and (3) in both cases.
1. **Source builds in the sandbox, with pinned toolchains** (rustc and cargo, gcc or clang),
   vendored dependencies, no network, and the binary's hash recorded as now. Cost: images, an
   offline build step, a build-time cap. The toolchain is trusted for nothing (C-m7).
2. **Keep `.s`, with an organiser-shipped sanitiser and a reproducibility check.** The harness
   rebuilds the `.s` from the declared toolchain and records whether it matches, as a flag, not a
   rejection.
3. **Document** the LLVM-23 recipe and the static-glibc caveat in `harness/PROVER.md`.

### FB-9 (medium). `errorCap = 2^-128` per query excludes Flock's GF(2^128) as published

**Rule.** `errorCap` in `Contract/Security.lean`, through `Certificate.cap`: `S.ε ≤ 2^-128` per fresh
query (V4-13).

**Goals.**
- G-open, medium: the most direct Flock port is not certifiable, and nothing says so until someone
  computes per-round errors.
- G-chains, medium: the GF(2^192) detour costs about 2× extension arithmetic, which is about 0.5–0.7×
  Flock's throughput, and about 550–750 KiB of proof against Flock's 386 KiB (**estimate**, F0 Q4).

**What happened (estimate, F0 Q4).**
- In GF(2^128), a degree-2 sumcheck round errs with probability `2/2^128 = 2^-127` per challenge
  query.
- Flock's univariate-skip round errs with probability `126/2^128 ≈ 2^-121`.
- The entry therefore used GF(2^192), with `ε = 2^-129` (D-1).

**Proposed changes.** We recommend (1), with no change to the cap.
1. **Document the grinding route.** This is **paper**; the review checked it as sound per fresh
   query. Each round's challenge comes from an answer that must also carry `g` zero bits (a proof of
   work). A fresh query is then both valid and bad with probability `2^-g · d/|F|`, so `ε =
   2^-(127+g)`. `g = 7` covers the skip round (0.98 · `2^-128`). The honest prover pays `2^g`
   queries per round, batchable in one `QUERY`. For completeness, `89 · 2^g` attempts per round give
   `δ = 2^-128`. Over `R` rounds, the union bound needs about `(89 + ln R) · 2^g` (v3 §5.4).
2. **Or lower `errorCap` to `2^-120`.** The bound `(Q + qV)·ε` at `Q ≈ 2^30` becomes about `2^-90`
   instead of `2^-98`. At `logCap = 2^96`, the smallest chargeable collision-type event falls from
   224 to 216 bits (`Contract/Security.lean`). Cost: one trusted constant, and a soundness trade for
   the authors to choose.

### FB-10 (low). One signature on the empty trace certifies every query-free child: make `SigOk` vacuous there

**Rule.** `Submission.acc` checks `SigOk vk (traceDigest p.tr) p.σ` even on an empty trace. The
trusted decoder `readSigned` (`Contract/Extractor.lean`) reads a full signature per child: 597
words, 4,776 B.

**Goals.**
- G-open, low: every bundling or witness-sending entry pays 4,776 B per clear slot, plus one `SIGN`.
- G-chains, low: the frontier gains one notch (FB-1's last column).
- G-trust: not affected, as argued below.

**What happened.**
- One `SIGN` with count 0 (0.3 ms) gives σ0, which serves every clear slot for the service's
  lifetime.
- It is sound, and the review found it so. σ0 is checked only so that the extracted witness is in
  `Rel`, which holds for every key, so C-m1 does not bite (BLUEPRINT §5, F1 review §3.2).
- The cost is bytes. Of the 9,704 B of witness per bundled leaf, 9,552 B are two copies of σ0 (F2
  §3.3). That is 6.2% of the 153,367 B a leaf adds at `n = 16`.

**Proposed change.**
- In `acc`: `(p.tr.isEmpty || SigOk vk (traceDigest p.tr) p.σ)`.
- In `readSigned`: read a signature only after a non-empty trace.

**Footprint.** This is a trusted **format** change, not one conjunct. It touches:
- `readSigned`, with its controls: positive, an unsigned query-free child accepted; negative, an
  unsigned non-empty trace rejected;
- `FORMAT.md`, and the library's `witWords` and `decodeWit_witWords`;
- the runner's signature canaries and stage B's "unsigned trace" broken-prover check, which then hold
  only for non-empty traces;
- the meaning of `vk`. A query-free root needs no service, so its record's `vk` carries no
  information, and C-m9 should say so.

**Soundness** (**paper**; the review confirmed it against `Library/Compose.lean`).
- **The composition walk.** It uses a child's signature only at step 2: to conclude that the trace
  is genuine, or to return a forgery. An empty trace is contained in every log, so neither the
  forgery outcome nor `runSeq → runLog` needs the signature.
- **Step 3** applies `final` on the run's log. A query-free `V` is a pure function of `(vk, c, π)`.
  With exact consumption, `runSeq []` returns `none` on any query.
- **The relation.** The change enlarges `Rel (acc vk)` by unsigned query-free children only.
- **Completeness** must then cover those children too. A recursive node circuit makes its signature
  check conditional on a non-empty trace.
- **Untouched:** the `∀ vk` certificate, EUF-CMA, the PRF hybrid and C-m1.
- **What is given up.** The `vk` binding of query-free proofs, which was never load-bearing: σ0 is
  already public in every bundle (FB-5).

**Alternatives considered.**
- **A Library "expanding" extractor**, which reads σ0 once from `π` and writes it into every slot
  (F0 route ideation point 2). It needs no trusted change, but a custom `XProg` with a loop
  invariant.
- **Leave it as it is.**

## 2. Harness and tooling defects

Each row's status:

- **fixed** at `81e1ebf` (`B-harness-RESULT.md` §9);
- **queued** in the core's FIXLIST;
- **proposed** here.

| Id | Defect | Evidence | Status |
|---|---|---|---|
| H-1 | The rebuild binding REJECTed a certified entry: gate-only artifacts counted as differences, although all 110 shared artifacts were byte-identical | F3 §2.1, runs 1a, 1f | **fixed** (Q7) |
| H-2 | CompPoly was not an organiser root, so a pinned dependency was checked as entry code, and the message named a module the entrant cannot change | F3 §2.2, F1-M1 | **fixed** (Q2) for CompPoly; others as in FB-4 (2) |
| H-3 | A nanoda OOM stopped the comparator's scope, so the Lean kernel never ran, and the result read "certificate does not check" | F3 §2.4 | **fixed** (Q12) |
| H-4 | A failed tree run dropped the prover's log and the service's refusal | F3 §4.1 | **fixed** (Q13). Proposed: also keep a failed run's `T_tree` and `T_V` block |
| H-5 | An OOM kill read as "proof.bin: missing; stderr:" | F3 §4.2 | **fixed** (Q14) |
| H-6 | "rejected by acc" gives no reason; the frontier's size-cap failures were found by hand | F3 friction 6 | proposed: a badge reason code (size, trace length, query cap, signature, `V`). The prover warns since F2-m5 |
| H-7 | No per-check `acc` times for stream outputs, canaries, DoS or liveness. The comparator's phases are invisible. `lake env` start-up costs 21–29 s per tree. `T_tree` has 50 ms resolution, since `Popen.wait(timeout=…)` polls: three runs gave 0.917036, 0.917041 and 0.917063 s | F3 frictions 7–8; F2 §6.5; `rfh/prover.py:166` at `81e1ebf` | proposed |
| H-9 | `t_leaf` = Σ of `M + 1` leaves over `M`: 0.2512 s, against a mean of 0.201 s | F2 §6.6 | as specified ([CM] §3.3, design §3.5); label it (Q3, partly) |
| H-10 | The calibration uses `os.cpu_count()` under a 16-core `taskset`, and reports `threads_32` | F2 §6.7; `rfh/bench.py:209` at `81e1ebf` | proposed: `len(os.sched_getaffinity(0))` |
| H-11 | Rust's `UnixStream::connect` fails on a socket path of 108 bytes or more | F2 §6.4 | proposed: a note in `PROTOCOL.md` |
| H-12 | Setup costs and undocumented steps (see below) | F3 §1, §2.3, frictions 9, 14; F1 RESULT §7.9 | proposed: check the manifest once; document the setup in `evaluate.py`'s header |
| H-13 | The badges are 142.7 MB each, and their build compiles 986 package objects outside the closure inside the job (73.7 s) | F3 §2.3, friction 10 | proposed: prebuild them in `org-setup` |
| H-15 | Liveness took 24.1 s and 121 MB on a 2.1 MB log at `r = 1, n = 16`. Only the 3,600 s badge timeout bounds it | F3 §3 | proposed: publish it, and give it a stated cap |
| H-16 | The rejection reason reads "gate: gate: REJECT …" | F3 §2.2; `evaluate.py:308` at `81e1ebf` | proposed |
| H-17 | Docs drift. Q6 was closed by RA-M2 and Q3 at `88d4566`; Q4 is pending in `AGENTS.md`. Three items remain open (below) | FIXLIST Q3, Q4, Q6 | partly fixed |
| H-18 | Stage B's mock badge imports `wots_ref` from `tests/service/` | F2 §6.8 | proposed: vendor it |
| H-19 | Concatenation merges are not flagged: no per-link `\|π_i\|` or per-request `QUERY` count is published (FB-1) | F2 §4; F3 §3 | proposed |

**H-12, setup costs and undocumented steps.**
- **Costs.** A private, writable 9.2 GB package tree is required, since the shared one has no build
  products. Copying it takes 4 min. `org-setup` takes 5 min 56 s, 149 s of it hashing 34,290
  `.olean` files. The manifest check runs 4 times per job.
- **Undocumented.** `RF_ORG_ROOTS`. `scripts/tools.env`, whose defaults point at this VM.
  `evaluate.py` must be run from the organiser checkout. `--work` must not exist. Lake's `Foo.+`
  glob means submodules.

**H-17, open items.**
- **Units.** The design says "11 GB", but `season.toml` has `11G` (GiB). The kill was measured at
  11.81 GB.
- **Stale numbers.** Design §3.6 and §4.3 still quote the pre-golf figures: memory: 15.1 GiB, now
  2.47 GiB; `acc`: 0.20 and 0.45–0.50 s, now 89–111 and 188–195 ms.
- **H-9's label.**

## 3. What worked well

- **The SROM core held.** Building, reviewing and attacking the entry found no soundness issue;
  F1-M2 is a denial of service. C-m1 did not bite σ0. v3's potential and `final` carried over: a
  bundle of `k` SNARKs costs no extra error. The soundness modules are byte-identical to v3's.
- **The port was mostly mechanical.** 47 of 65 modules were unchanged, with 886 new and 310 changed
  lines out of 17,252. The v4 `Words` lemmas made `decode_leaf` a one-lemma re-proof.
- **The library served bundles unchanged.** `decodeWit` ignores trailing words, so the copy extractor
  (`E`, `ext`, `fuel`, `computes`) reads `encode W ‖ T` as it is. The fast twins came with their
  equality theorems.
- **`SIGN` with count 0** gave σ0 in one 0.3 ms call.
- **The interface documents were precise enough** (`FORMAT.md`, `PROTOCOL.md`, the contract). An
  independent native `acc` matched the Lean `V` branch by branch and byte by byte, on the first try
  (F2 review §1). The real Lean badge accepted the nested bundles: the `r = 2` root in 931 ms, and
  stream nodes 2–4 in up to 1,311 ms. This closed F2-M1.
- **The service** matched the in-process keyed oracle, so the prover could be developed offline. It
  moved 1.8 GB/s of Merkle traffic.
- **The assembly build** was deterministic, the sandboxed build included. The sandbox ran a std-Rust
  prover with threads, sockets and non-blocking I/O unchanged.
- **The harness's checks.** Its frontier messages are exact, for example "tree1 root took 945.893
  ms, above T_V = 0.015 ms". The canaries rejected 69, 18 and 29 mutations. Liveness "extracted and
  checked 3 witnesses from a log of 30820 entries", from the service's authentic log. The
  certificate job fits in 16 GB.
- **The feedback channel works.** Within the stage, the core fixed the baseline's RA-M2, Q2, Q4, Q6,
  Q7 and Q12–Q14, with Q8, Q10 and RB-M1. It queued Q15 and recorded Q11 as open. It put this
  entry's frontier into design §3.6.

## 4. Open questions for the rules' authors

1. Until a certified recursive entry exists, will the board publish FB-1's frontier columns? Will it
   adopt an interim partial-stream ranking, which suspends G2 and G3?
2. Which Q11 option, and will it be decided on runner timings of node-sized proofs (FB-2 (3))?
3. Should the Library carry a generic bundle, `accWith` and `AtMost` (FB-3), and a compiled-verifier
   kit (FB-2 (2))? Who reviews them?
4. Q5: will nanoda run off CI for records, given more than 20 GB and more than 10 min? Which packages
   are pinned, and on whose audit (FB-4)?
5. Who adjudicates a reviewer's crafted input, and before which step of a record (FB-5)?
6. Do you want `SigOk` vacuous on the empty trace (FB-10)? Grinding, or a lower `errorCap` (FB-9)?
7. Should completeness be required only for proofs within `proofCap`, or left to the harness's
   concrete checks as now (FB-3, D-5)?
8. A `V` that checks only formats and statement binding passes every canary, so a PROVISIONAL entry's
   timings say nothing about proving (C-m13; F0 route ideation Q5 item 8; not tested here). Should a
   PROVISIONAL run require more, or is "uncomparable" enough?

## Appendix A. The service-tax arithmetic (FB-7; **estimate** from measured inputs)

**Inputs.**
- **Witness.** Flock commits about 2 KiB of witness per compression (leanVM's Flock, F0 §4). At rate
  ½ that is about 4 KiB of codeword, all of it Merkle-hashed.
- **Service rates** (**measured** on the VM, `.contract/docs/v4/reviews/GB-golf.md` §1.2): the
  hashing kernel, in-process on one pinned core: 38.7 ns per 64-byte block for 64-byte queries, 37.6
  ns for 1 KiB queries; one connection, end to end: 7.37 M 64-byte calls/s, i.e. 136 ns per call.
- **Flock's proving.** `2^16` compressions in about 135 ms on an M4 Max ([CM] §3.3), i.e. about
  33 µs of core time per compression on 16 cores.

**The chain term.** 4 KiB is 64 blocks.
- At the kernel rate, hashing costs 64 × 37.6–38.7 ns = 2.4 µs of core time per compression.
- At the one-connection rate, it costs 64 × 136 ns = 8.7 µs.
- Against 33 µs of proving, that is **7–26%**.

**A recursion step** is about `2^15` compression-equivalents (two children of 16–17k compressions of
hashing each, F0 Q3).

| Component | Arithmetic | Time |
|---|---|---|
| Merkle hashing | `2^15` × 2.4–8.7 µs over 4 cores | 20–71 ms |
| Fiat–Shamir | 150–500 sequential round trips at 31–37 µs (design §3.2; F2 golf §4.1) | 5–18 ms |
| `SIGN` | a trace of 5,000–15,000 entries, scaled from 34 ms per `2^16` (GB §1) | 3–8 ms |
| **total** | | **about 30–100 ms** |

## Appendix B. Evidence index

| Finding | Records | Logs |
|---|---|---|
| FB-1 | F3 §4.1–§4.3; F2 §3.3, §4, fix pass; F2 golf §4.1, §4.3, §6; F0 route ideation points 1 and 3, Q3–Q4; F0 §2–§4 | `logs/f3/frontier-table.txt`, `frontier-driver{,2}.log`, `bench-season*.log`; `logs/f2/fix/links-n*.log`; `logs/golf/ref-65536.log`, `final-65536.log` |
| FB-2 | F3 §3, §4.4; F1 RESULT §5, §7.4, §9.3; F1 golf §2; F2 §3.5, §4; core B RESULT §3, §9; design §3.5 | `logs/f3/fr-tv-*.log`, `bench-smoke-reverify.log`; `logs/lean/run/verify-final.log`, `timings-fix.log`; `logs/golf-lean/verify-abab.log`, `prof/` |
| FB-3 | BLUEPRINT D-2, D-5, §1.4, §2; F1 RESULT §1, §5, §7.2–§7.3, §9.1; F1-m1; F0 §2; F2 §3.3 | `logs/lean/run/verify-final.log`, `probe-B.log`; `logs/f2/selftest-asm.log` |
| FB-4 | F3 §0, §2.1–§2.4; F1-M1, F1-m4; F1 RESULT §7.1; core B RESULT §9 | `logs/f3/cert-*.log`, `cert-nanoda.curve`, `nanoda-standalone/`; `logs/lean/noncomputable-probe.log` |
| FB-5 | F1-M2; BLUEPRINT D-6; F1 RESULT §9.1, §9.3; F3 §3 | `logs/lean/run/attack-after-{1,2,3,B-1}.log`, `attack-final.log` |
| FB-7 | F2 §4; F2 golf §2.9, §4.1; F3 §4.1; core `GB-golf.md` §1 | `logs/f2/bench-asm-n*.log`; `logs/golf/final-timings.log`; `logs/f3/diag/tree-r6-n2p18.log` |
| FB-8 | F0 §1; F2 §2, fix pass; F2 review §3, F2-m2 | `logs/probes/asm/`; `logs/f2/build-asm-*.log`, `fix/determinism.log` |
| FB-9 | F0 route ideation Q4; BLUEPRINT D-1; core `Contract/Security.lean` | — |
| FB-10 | BLUEPRINT §1.4, §5; F2 §3.3; F1 review §3.2; FB review §3 | `logs/f3/frontier-table.txt` |
| H-1 … H-19 | F3 §5 (frictions 1–14); F2 §6; core FIXLIST Q2–Q15, B RESULT §9 | as cited per row |
