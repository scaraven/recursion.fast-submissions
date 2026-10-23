# Feedback on the v4 rules from the first entry, the Flock baseline (`spartan-srom`)

**Status.** This is the v4 baseline team's (stage F) report to the authors of the v4 rules, dated
2026-10-23. It draws on building and running the first v4 entry, `submissions/spartan-srom` ("the
Flock baseline"), through these stages:

- F0: the route and the probes;
- F1: the Lean entry, which is certified;
- F2: the native prover, with its review, golf and fix pass;
- F3: the entry run through the real harness.

**What was read.** The rules are the core branch `v4/srom-rules`, in two states:

- the contract and the harness as pinned by `.contract`, at `ea2e8ab` (the contract fix pass, with
  RA-M2);
- the design text at the branch head `88d4566`, which already quotes this entry's frontier (§3.6)
  and records Q11.

Core files are cited as `.contract/<path>`. Entry records are cited relative to this repository,
under `docs/v4/flock-baseline/`; logs are under `logs/` (gitignored), cited as the records cite them.

**Which version of the entry the numbers describe.**

- The harness numbers are from F3. F3 ran the frozen commit `8111b71`, before the reviews and the
  golfs.
- The entry's current state is that of the F2 golf and fix pass (`f2f2bf6`, `10ad91e`). Its proofs
  are byte-identical to the frozen commit's, and it has not been run through the harness.
- The F1 fix pass is still running.

**Evidence tags** are those of the design:

- **kernel**: a kernel-checked theorem;
- **measured**: a number with its log;
- **estimate**: arithmetic on measured or published inputs;
- **paper**: an argument.

Every measurement comes from the shared 32-vCPU development VM, under other agents' load, unless it
says "runner". The VM has AVX2 and AVX-512F but not `pclmulqdq`.

**Ids.**

- `FB-n` are this report's findings on the rules (§1); `H-n` are its harness and tooling defects
  (§2).
- The record's ids are kept: V4-n and V4-An; C-Mn and C-mn; CM-n; RA-…; the core FIXLIST's Q1–Q11;
  the entry blueprint's D-n; and its reviews' findings, such as F1-M2 and F2-m3.

**The four goals.**

- **G-chains**: fast BLAKE2s hash-chain proving comes first.
- **G-rec**: recursion at 100–200 ms per 2→1 step comes second.
- **G-trust**: a minimal trusted base.
- **G-open**: entrants may use any proof system and any language.

**Severity.**

- **blocker**: a goal cannot be met under the rules as they stand.
- **high**: a goal is met only with large cost or distortion.
- **medium**: a real cost or a misleading number, with a known fix.
- **low**: a friction or a small, cheap gain.

## 0. Summary

### 0.1 What was built

- **A certified entry.** `spartan-srom` is v3's `spartan-chain` ported to the v4 contract (D-1),
  `F1-lean-RESULT.md` §1–§3.
  - The protocol: Spartan R1CS sumchecks over GF(2^64)/GF(2^192), ring switching, and Ligero with
    unique-decoding proximity.
  - The size: 65 Lean modules and 17,252 code lines. 47 modules (15,209 lines) are v3's, unchanged
    after the rename. 886 lines are new (`Node`, `NodeControls`, `Queries`, `SnarkQueries`,
    `Solution`) and 310 lines are changed.
  - The certificate: `SpartanSrom.certificate : Certificate submission` is a closed theorem on
    `propext`, `Classical.choice` and `Quot.sound`.
  - The claim: `ε = 2^-129`, `δ = 0`, `qV = 2^16`, fuel `8t`.
- **σ0-bundle nodes (D-2).** A node proof carries its whole subtree as a clear witness.
  - Every slot of that witness is signed by one signature σ0 on the **empty** trace.
  - After the witness come the leaves' SNARKs, which the node's `V` re-runs with fresh queries.
  - The extractor is the library's copy extractor, unchanged.
  - The format is in `BLUEPRINT.md` §1.4 and §2.
- **A native prover.** It is written in std Rust (5,683 lines, no dependencies), `F2-prover-RESULT.md`
  §1–§2.
  - It is emitted as one `prover/prover.s` by fat LTO, with a sanitising filter. The file is 8.7 MB,
    and 9.2 MB after the golf.
  - It targets `x86-64-v2` and dispatches `pclmulqdq` at run time.
  - Every Merkle and Fiat–Shamir hash goes through the service.
  - Its leaf SNARK bytes equal the Lean `P`'s at `n = 1, 16`, and v3's at `n = 1, 2, 16, 64`.
  - After the golf, the smoke `T_tree` is 0.131 s and a `2^16` leaf peaks at 2.47 GiB
    (`F2-golf-RESULT.md`).

### 0.2 What the harness said (F3, frozen entry `8111b71`; `F3-harness-RESULT.md` §0)

| Run | Verdict | Where it stopped | Log |
|---|---|---|---|
| `cert`, frozen entry (default roots, and again with the CompPoly roots) | REJECT | the rebuild binding counts the 22 artifacts of modules outside `Solution`'s closure (the controls) as differences (Q7) | `logs/f3/cert-lean.log`, `cert-frozen-comppoly.log` |
| `cert`, `Solution` importing every module, default roots | REJECT | gate rule 3: one `@[csimp]` lemma of CompPoly, because CompPoly is not an organiser root (Q2) | `logs/f3/cert-closure-default.log` |
| `cert`, the same with the CompPoly roots | **ok** (Lean kernel), 14 min 22 s, peak 4.11 GB | — | `logs/f3/cert-closure.log` |
| `cert --nanoda` | provisional: "the certificate does not check" | nanoda OOM-killed at 13.65 GB in the 14 GiB scope; the Lean kernel never ran. Run alone under 20 GB: killed after 10 min 1 s, still growing | `logs/f3/cert-nanoda.log`, `nanoda-standalone/` |
| `bench`, smoke shape (`r = 2, n = 16, M = 4`) | **ACCEPT** | `T_tree` 0.896 s, root `acc` 978.8 ms, `t_leaf` 0.251 s, `t_merge` 0.037 s, `S` 6.666. `T_V` was only reported: its cap was 10.3 µs | `logs/f3/bench-smoke.log` |
| frontier | largest ACCEPTs: `r = 0, n = 4,096`; `r = 1, n = 1,024`; `r = 2, n = 128`; `r = 3, n = 4`; nothing at `r ≥ 4`. Stream: 5 links at `n_f = 16`, 1 at `1,024` | every rejection is `\|π\| > proofCap`, reported only as "rejected by acc" | `logs/f3/frontier-table.txt` |
| `T_V` enforced at the frontier | REJECT | root `acc` 946 ms against a 0.015 ms cap; 1,776 ms against 0.194 ms | `logs/f3/fr-tv-*.log` |
| season tree (`r = 6, n = 2^18`) | REJECT, "prover tree exit 3" | the service refused a 1,572,898-byte absorb (`queryCap`) 27.6 s into leaf 0 | `logs/f3/bench-season.log`, `diag/tree-r6-n2p18.log` |
| season stream (`M = 512, n_f = 2^16`) | REJECT, "proof.bin: missing; stderr:" | the 11 GiB prover cgroup OOM-killed leaf 0 at 11.14 GB after 25 s (the pre-golf prover) | `logs/f3/bench-season-stream.log` |

**In short.**

- The entry was ACCEPTed at the smoke shape, but only with two workarounds: `Solution` imports every
  module (for Q7), and CompPoly is added to the roots (for Q2).
- It is ACCEPTed only where `2^r·n ≤ 4,096`.
- It is REJECTed at the season shape: the tree by the service's `queryCap` refusal of a 1.57 MB
  absorb, the stream leaf by the 11 GiB cgroup.
- The cgroup was the stopping rule only for the pre-golf prover. The golfed leaf peaks at 2.47 GiB,
  so `proofCap` would stop link 0 instead.
- `T_V` cannot be met at any shape this entry can run.

### 0.3 The top five findings

| Id | Finding | Severity | Proposed change | Cost |
|---|---|---|---|---|
| FB-1 | No non-recursive entry can run the season shape. `proofCap` stops bundles at `2^12` chain steps against the season's `2^24`, so `S` has no value and G3's "no cliff" fails in practice | blocker | Publish every entry's frontier as unranked columns; score partial streams by links accepted; tie the first ranked shape to the first certified recursive entry (C-m10) | runner only; 0 trusted lines; no soundness effect |
| FB-2 | `T_V` is microseconds at every shape a SNARK entry can run, so the smoke shape cannot test it. At the season scale it mostly measures Lean compilation: a 2× gain from a field product and in-place reads, and no carry-less multiply (Q11) | high | Report every check against the season-scale cap at every shape; a Library kit of proved fast primitives; decide Q11 on runner numbers | runner and Library; 0 trusted lines |
| FB-3 | A signed child is `π + trace + σ`, and the trace restates every hashed byte. Witness-sending dies at the first node (1,089,384 B > `proofCap`), so every non-recursive entry must invent and certify a bundle (about 870 Lean lines here) | high | A Library bundle generalised from this entry; state the arithmetic in the rulebook; FB-10 | Library (about 870 lines); 0 trusted lines |
| FB-4 | The certificate job: nanoda needs more than 20 GB and more than 10 min, so records rest on one kernel. A memory kill reads as "the certificate does not check". A certified entry was REJECTed by Q7 and Q2. The computable `Submission` rule is undocumented | high | Q7 and Q2 (accepted); all pinned packages as roots; resource kills reported as such; template projection; nanoda off CI for records | `evaluate.py`, `org-setup.sh`, templates |
| FB-5 | Crafted proofs built from public parts take `acc` 68–183 s (`verify_s` = 60 s), against 0.43 s for the honest root. No rule bounds this, and the DoS column's random mutations never find it | medium | A crafted-input column (shipped by the entrant, extendable by reviewers); state the σ0 amplifier | runner only |

## 1. Findings on the rules

### FB-1 (blocker). No non-recursive entry can run the season shape, so `S` has no value and "no cliff" fails in practice

**Rule.**

- The season shape (V4-11, `.contract/harness/season.toml`): tree `r = 6`, `n = 2^18`; stream
  `M = 512`, `n_f = 2^16`.
- `proofCap = 2^20` on every proof (V4-13, `.contract/RecursionFast/Contract/Relation.lean`).
- G3 of the cost model: "every entry that produces accepted proofs is ranked"
  (`.contract/docs/DESIGN-cost-incentive-model.md` §1).
- The design states the gap (C-m10; §2.8, §4.3, §7.3): it will "set the first ranked shape from the
  first certified recursive entry".

**Goals.**

- G-chains, blocker: a chain prover that does not recurse is never ranked, however fast it is.
- G-rec, blocker for now: no entry produces a `t_link` at the season shape, so the "start high, then
  progress" incentive ([CM] §1) has nothing to start from.
- G-open, high: the caps exclude every design without a succinct recursive node, but no rule says
  so.
- G-trust: none.

**What happened (measured).**

- **Tree** (F3 §4.3, `logs/f3/frontier-table.txt`).
  - Every accepted tree has `2^r·n ≤ 4,096` chain steps, 4,096 times fewer than the season's `2^24`.
  - No `r ≥ 4` fits, even at `n = 1`: the root's `π` is then 1,676,344 B.
  - Every rejection is `|π| > proofCap`. A bundle's `π` grows by one leaf SNARK plus 9,704 B of
    witness per leaf.
- **Stream** (F2 §3.3, re-measured in the F2 fix pass; F3 §4.3).
  - The stream completes 5 links at `n_f = 16`, 1 at `1,024`, and 0 at `≥ 4,096`.
  - At `2^16` the leaf alone is over the cap: its `π` is 2,791,559 B.
- **Season runs.**
  - The tree stopped at `queryCap` (FB-7), and the stream at the memory cap with the pre-golf
    prover (FB-11).
  - Without those two stops, `proofCap` would stop both at the first leaf.

**Estimates for a Flock-class entry.** Sources: `reviews/F0-route-ideation.md` point 3, Q3 and Q4;
`stages/F0-probes-RESULT.md` §3–§4.

- Flock's proof at `2^16` BLAKE3 compressions is 416,368 B (**measured**, F0 §3).
- Under `errorCap`, a GF(2^192) variant would be about 550–750 KiB (**estimate**).
- 64 bundled leaves would therefore take about 25 MiB.
- The stream would stop at link 1 (two proofs exceed 1 MiB), or at most at link 2–3 at Flock's
  own proof size.
- One flat SNARK over `2^24` compressions has a witness of `2^38` bits (32 GiB) at leanVM-Flock's
  2 KiB per compression (F0 §4). That is above the 11 GiB prover cap.
- So only a recursive entry can run season 1 (**estimate**, consistent with C-m10).

**Why it matters.**

- The score's G1–G3 ([CM] §1–§4) hold only for an entry that already recurses within the caps.
- Until such an entry exists, the board is empty. The stream, the term meant to pull recursion
  forward, then gives no gradient: a faster bundler and a slower bundler both score nothing.
- The smoke shape, which every valid entry passes, tests neither `T_V` (FB-2) nor recursion (FB-6).

**Proposed changes.** None needs trusted Lean, and none changes soundness (G5).

1. **Publish the frontier of every entry** as unranked columns.
   - The columns: the largest accepted tree on a fixed ladder of shapes; the number of stream links
     accepted before the first rejection; and the harness's stopping reason (H-6).
   - F3 did this by hand: 14 tree shapes and 4 stream shapes (`logs/f3/frontier-driver.log`).
   - Cost: a `frontier` part of `evaluate.py bench`, and a ladder table in the season file.
2. **Score partial streams.** Rank stream results first by links accepted, then by `t_link` over
   those links.
   - An entry that recurses but fails late is then ranked; for example, one that fails at link 300
     on `T_V` as its proofs deepen.
   - Cost: `rfh/bench.py`, and the definition in [CM] §3.3.
3. **Turn C-m10's plan into a rule.** The first ranked shape is the shape the first certified
   recursive entry runs. Until it exists, the board publishes (1) and says that G3 is suspended.

**Alternatives considered.**

- **Raise `proofCap`, or count bundles as recursion.** Rejected: both re-admit the non-succinct
  strategies the caps exist to exclude ([CM] §3.5, CM-R2).
- **An interim ranked shape below the season's, with `T_V` floored at the season cap** (FB-2 (1)).
  Rejected: witness-sending would win it.
  - The library's witness-sending tree recomputes chains at about 280 ns per compression (F1 RESULT
    §6.1.8).
  - It would therefore pass a 178 ms cap up to about `2^19` chain steps, against this SNARK entry's
    `2^12` (**estimate**).
  - So the trivial entry would rank above the certified SNARK.

### FB-2 (high). `T_V` is unmeetable at every shape this entry can run, and at the season scale it mostly measures Lean compilation

**Rule.** V4-12, design §3.5.

- One `acc` check must take at most `T_triv,best / R`, with `R = 10`. The check is timed as parse
  plus `accF`, in the badge process, on one pinned core.
- `T_triv,best` is the organiser's compiled-Lean chain checker, run over the tree's chains in the
  same job.
- `[tv] enforce` is true in `season.toml` and false in `smoke.toml`.

**Goals.**

- G-rec, high: the season cap is the whole budget of a recursive node's compiled verifier. It is
  about 178 ms on a runner and 267–310 ms on the VM. A binary-field verifier also pays for a
  software carry-less multiply inside it (Q11).
- G-open, high: the same protocol's `T_V` moved by about 2× through Lean-compilation craft. That
  disadvantages binary fields, against V3-1.
- G-chains, medium: at the season scale, a bundling root fails `T_V` well before `proofCap`.
- G-trust: none. `T_V` is a resource cap, outside the certificate.

**What happened (measured).**

- **At the shapes the entry runs, the cap is microseconds.** F3 §3 and §4.4
  (`logs/f3/fr-tv-*.log`):
  - At the smoke shape, `T_triv,best` is 103–154 µs, so the cap is 10.3–15.4 µs. The root's `acc`
    takes 946–979 ms.
  - At `r = 1, n = 1,024`, the cap is 0.194 ms and the root takes 1,776 ms.
  - That is 4–5 orders of magnitude over. The smoke shape cannot test `T_V`, and the frontier
    shapes reject any SNARK.
- **At the season scale.**
  - `T_triv,best` was 2.668 s on the VM, a cap of 266.8 ms (`logs/f3/bench-season.log`).
  - It was 3.097 s in stage B, a cap of 310 ms.
  - It was 1.776–1.785 s on a GitHub runner, a cap of about 178 ms (design §3.5).
- **The entry's own `acc`** (badge NS):

  | Proof | Before the F1 golf (F1 RESULT §5) | After it (F1 golf §2, `logs/golf-lean/verify-abab.log`) |
  |---|---|---|
  | one `n = 16` leaf | 204–218 ms | 91–136 ms |
  | a bundle of two leaves | 0.45–0.50 s | 193–207 ms |

  <!-- TODO(orchestrator): the badge times of the F1 fix pass (golf merged with the D-6 and ea2e8ab changes). -->
- **What moved those times was craft, not protocol.**
  1. Compiled `ByteArray.data` copies the whole array. v3's `digestFrom` therefore made parsing
     quadratic: 87.8 s for a 539 KB file, 579 s for 1.08 MB. It also made every leaf check copy its
     proof about 100 times (F2 §3.5, F1 RESULT §5). The fix was `byteAt`.
  2. The library's `decode` packs all of `π` at 0.2 µs per byte. For a 297 KB bundle, that is
     60 ms spent packing SNARK bytes the decoder never reads (F1 RESULT §7.4). The fix was a prefix
     decoder, `decodeFront`.
  3. The shift-and-add GF(2^64) product took 85 ns and 64% of the badge's time. A proved Karatsuba
     product over `clmul32` takes 25 ns, at a cost of 343 proof lines. The badge time fell by 55%
     for a leaf and 58% for a bundle (F1 golf §2).
- **Lean against native** (not like for like).
  - The native verifier replays an `n = 16` leaf in 0.044 s, using the portable field product and
    no trace hashing (F2 §4).
  - The runners have `pclmulqdq`. Native code uses it; compiled Lean cannot (Q11).

**Proposed changes.**

1. **Report every check against the season-scale cap, at every shape.**
   - Calibrate `T_triv,best` on `2^24` compressions in every job, the smoke job included. One checker
     run takes 2.7–3.1 s on the VM and about 1.8 s on a runner.
   - Publish each check's time against `T_triv,best(2^24) / R`, beside the shape's own cap.
   - An entrant then learns at the smoke shape whether its verifier can ever pass the season. This
     entry would have seen a 0.98 s root against about 0.18–0.31 s.
   - Cost: the runner only. No soundness effect.
2. **A Library kit for compiled verifiers**, beside the fast hashes of `Library/Fast.lean`.
   - Its contents: in-place byte readers; a prefix decoder of `encode W ‖ T`; and this entry's proved
     GF(2^64) product (`FieldBase.clmul32`, with `mul_eq_mulLoop` relating it to v3's product). Each
     comes with its equality theorem.
   - It removes the craft component, so that `T_V` compares protocols.
   - Cost: 0 trusted lines.
3. **Decide Q11 on runner numbers.**
   - With the golfed product, one Spartan-class check is 0.5–0.8× of a runner's 178 ms cap, and two
     are 1.1–1.2×. These are VM times against a runner's cap; the VM has no `pclmulqdq`.
   - A recursive node checks two children. So the choice among the design's options is close: a
     per-field calibration, a smaller `R`, or a contract-fixed verified `clmul`.
   - It should be decided on a runner measurement of these files: the badge's `acc` on one leaf and
     on a bundle of two, against that runner's own `T_V`. No runner measurement of this entry exists
     yet; the baseline team had no runner.

**Alternatives considered.**

- Timing a native twin of `V`: it cannot be proved equal to `V`.
- Enforcing `T_V` at the smoke shape against the smoke shape's own cap: it rejects every SNARK
  (F3 §4.4).

### FB-3 (high). A signed child restates every hashed byte, so witness-sending dies at the first node and every non-recursive entry must invent a bundle

**Rule.**

- In the node clause, a child is a signed proof `(π, tr, σ)`, and `acc` needs the whole trace
  (`Rel`, `Contract/Relation.lean`; `Submission.acc`, `Contract/Certificate.lean`).
- `proofCap` counts the node's own `π` only.
- Under witness-sending, the node's `π` holds each child's `π`, trace and signature
  (`readSigned`, `Contract/Extractor.lean`; `Library/WitnessSending.lean`).

**Goals.**

- G-open, high: every entry whose leaf is a Merkle-based SNARK must design, certify and implement
  its own node format before it can build a tree of depth 1. Here that took about 870 Lean code
  lines and about 340 Rust lines.
  - Lean: `Node` 288, `NodeControls` 431, `Queries` 62, `SnarkQueries` 88.
  - Rust: `make.rs`, `acc.rs`.
- G-chains, medium: the bundle is what sets FB-1's frontier.
- G-rec, low: a succinct node does not carry its children. But the same restatement is what a node
  circuit must hash: about 1.6× a public Merkle step per 64-byte query (design §4.2).
- G-trust: none.

**What happened (measured).**

- **The trace restates the columns the verifier opens.** At `n = 16` (F0 §2, F2 §3.3):
  - a leaf's `π` is 143,711 B;
  - its trace has 3,533 entries and takes 390,203 B;
  - its signed file is 538,698 B, 3.7× `π`. At `n = 65,536` the ratio is 2.1×.
- **Plain witness-sending fails at the first node.** The library's plain node of two signed
  `n = 16` leaves is 1,089,384 B, 40 KB over `proofCap` (F1 RESULT §5). It fails at the first node of
  the smoke tree, as the route analysis predicted (F0 route ideation, point 1).
- **The entry's answer is the σ0-bundle** (D-2). It carries each leaf's SNARK once, beside its clear
  witness, and re-runs each SNARK with fresh queries. That needed three things of its own:
  - a static check `Σ qBound ≤ 2^16`, since `qV` bounds one `V` run;
  - a check that the witness is a clear tree;
  - a strong induction for `final` (`clear_acc`).

**Proposed changes.**

1. **A Library bundle** (untrusted, kernel-checked): this entry's node branch, generalised over any
   leaf verifier with a static per-leaf query bound.
   - It holds:
     - the `C`, `N` and `B` branches;
     - `final` from the leaf verifier's own `final` on the same log (a bundle of `k` SNARKs costs no
       extra error, F1 review §3.2);
     - the `AtMost` bound;
     - completeness through the plain node;
     - the controls;
     - a reference byte format for native provers.
   - Cost: about 870 Library lines, reviewed once rather than once per entry. No soundness effect.
2. **State the arithmetic in the rulebook** (`AGENTS.md`, `harness/FORMAT.md`).
   - A signed child is `π + trace + σ`.
   - For a Merkle-based SNARK the trace is about `|π|` or larger.
   - So plain witness-sending of two such children exceeds `proofCap`.
3. **Drop the per-slot signature.** FB-10 removes the 4,776 B signature from every clear slot.

**Alternatives considered.** Neither is recommended.

- **Let a node's witness hold a child's trace by digest.** Rejected: `acc` must run `V` on the trace
  itself.
- **Charge `proofCap` on `π` plus the children's traces.** Rejected: it changes the succinctness cap
  for every entry.

### FB-4 (high). The certificate job: one kernel, a misleading verdict, and three undocumented requirements

**Rule.**

- V4-A2: the certificate job is separate, with the Lean kernel mandatory and nanoda run where it
  fits.
- Q5: CI checks certificates with the Lean kernel only.
- The tools: `harness/evaluate.py cert`, `harness/org-setup.sh` and the badge template
  `harness/badge/Common.lean.in`.

**Goals.**

- **G-trust, high.** The second kernel does not fit, and its failure is misreported.
  - On this entry's 226 MB export, nanoda grew about 2.1–2.2 GB per minute (F3 §2.4).
  - In the harness's 14 GiB scope, it was OOM-killed at 13.65 GB after 375 s.
  - Run alone under a 20 GB cap, it was OOM-killed at 20.9 GB after 10 min 1 s, still growing, and
    using about 1.2 cores (`logs/f3/nanoda-standalone/`).
  - Stage B saw 17.6 GB after 10 min 51 s on the witness-sending entry; v3 saw 52 GB on one lemma.
  - So records rest on one kernel. The harness also reported the kill as "comparator: exit -15, the
    certificate does not check": a resource failure reads as a broken certificate.
- **G-open, high until Q2 and Q7 land.** A certified entry was REJECTed for harness reasons, three
  times:
  - by the rebuild binding (Q7), twice;
  - by CompPoly's `@[csimp]` lemma, with CompPoly not an organiser root (Q2; F1-M1).
  - None of these is documented: that `Solution` must import every module; `RF_ORG_ROOTS`; or that
    the badge compiles the whole `Submission`, so a noncomputable `ε` fails its build (Q4; F1 RESULT
    §7.1, `logs/lean/noncomputable-probe.log`).
- G-chains, G-rec: none.

**What happened (measured).** The successful job (`Solution` importing every module, CompPoly roots)
is in F3 §2.3:

| Step | Wall | Peak |
|---|---|---|
| comparator | 8 min 33 s | — |
| · of which the Lean kernel | about 192 s | 3.62 GB |
| gate-tree rebuild | 3 min 30 s | — |
| gate | 21.8 s | — |
| badge build (695 `clang -c`) | 73.7 s | — |
| **total** | **14 min 22 s** | **4.11 GB** |

It fits a 16 GB runner. Its time on a runner has not been measured (design §3.1: TODO(B, fix pass)).

**Proposed changes.**

1. **Q7 (accepted, FIXLIST).** The gate tree builds `Solution`'s closure and the badge, and byte
   equality is required on that closure. Say that modules outside it are never built.
2. **Q2 (accepted for CompPoly), extended.** Make the organiser roots, by default, every module of
   every pinned package (CompPoly, ArkLib, VCVio, PolyFun), and the Batteries modules that entries
   import (F1-m4: `Batteries.Data.BitVec.Lemmas`).
   - A pinned dependency is then pinned by hash, never classed as entry code.
   - Cost: a larger manifest. CompPoly's field alone added 28 modules (F3 §1).
3. **Report a resource kill as a resource kill.**
   - Run the Lean kernel and nanoda in separate scopes, the Lean kernel first.
   - Read the scope's `oom-kill` result, and record "nanoda: not run (memory)" without touching the
     certificate's status.
   - Unbuffer the comparator's output.
   - Cost: `evaluate.py` only.
4. **Computability.** Have the badge template project `S.V`, `S.P` and `S.ext`, so that `ε` and `δ`
   may stay noncomputable. Otherwise, state the rule (Q4's doc pass). Cost: the template only.
5. **The second kernel** (Q5, the user's decision). Run nanoda off CI, on a machine with well over
   20 GB, for records only, and publish which kernels ran.

### FB-5 (medium). Crafted proofs make `acc` slow, and nothing in the rules bounds it

**Rule.**

- `acc` is "the check any third party runs later with the published `vk`"
  (`Contract/Certificate.lean`).
- The harness caps one check at `verify_s = 60 s`. It publishes the DoS column's maximum over random
  mutations (`harness/rfh/checks.py`, `dos_inputs`).
- No rule bounds `V`'s time on adversarial proofs (C9; design §4.3, §7.3).

**Goals.**

- G-trust, medium: anyone who has one bundle has σ0. A signature on the empty trace is valid for
  every query-free slot, so anyone can sign every such slot.
  - From public parts, the review built a 970 KB proof on which the compiled `acc` takes 68 s: a
    depth-100 chain of plain nodes over `n = 1` clear leaves.
  - With `n = 2^20` clear leaves it takes 183 s.
  - The honest root takes 0.43 s (F1 review F1-M2, `reviews/F1-lean-review.md` §1).
- G-rec, low: a node circuit checks its children at a fixed size. Only native checkers are exposed:
  the harness and third parties.
- G-open, low: the fix restricts the entry's own format (D-6).

**What happened.**

- **Two causes** (F1-M2).
  - `N` re-decodes each child from scratch at every level, so the cost is `O(|π|·depth)`.
  - `C` recomputed up to `chainCap = 2^20` steps per clear leaf.
- **The DoS column cannot find such inputs.**
  - Its inputs are random bytes, random `π` with the root's trace and signature, and bit flips of
    the root (`checks.py:131`). None of them reaches `V` with a valid signature.
  - Its maximum was 443 ms at the smoke shape and 1.59 s at `r = 0, n = 4,096` (F3 §3, §4.3).
- **The entry's fix** (D-6).
  - Clear and bundled leaves are capped at `n ≤ 2^12`. No `acc`-acceptable proof is lost, since
    `leafSize 4096 = 796,111 ≤ 2^20 < leafSize 8192`.
  - Tags are read in place.
  - What remains is the cost of nesting.
  <!-- TODO(orchestrator): the F1 fix pass's re-run of the F1-M2 attack (depth-100 plain-node chains of clear leaves, after D-6 and decodeFront): acc times. -->

**Proposed changes.**

1. **A crafted-input column.**
   - The harness times `acc` on proofs the entrant must ship (a `dos/` directory holding its own
     worst cases and their generator), and on proofs any reviewer may add to a public list for that
     entry.
   - It publishes the maximum beside the random column, and fails the entry at `verify_s`.
   - Cost: the runner only. No soundness effect.
2. **State the known amplifier in the rulebook.**
   - An empty-trace signature, published once, signs every query-free slot of every proof under that
     `vk`.
   - A verifier must therefore bound its own cost on such inputs: chain recomputation, and decoding
     per level of nesting.
3. **Not recommended now: a certificate obligation on `V`'s step count.** `OProg` has no cost
   semantics, so `V` would have to become a machine program.

### FB-6 (medium). With bundling, the stream measures concatenation, not recursion

**Rule.**

- The stream ([CM] §3.3, V4-10): `t_merge` is the mean merge time, and `t_link` is the recursion
  term of `S = T_tree + K·t_link`.
- CM-R2 bounds the bundled tail by `c ≤ proofCap / |π|`.

**Goals.**

- G-rec, medium: at every shape this entry runs, `t_merge` and `o_est` read as a recursion overhead,
  though a merge asks no `QUERY`.
  - `t_merge` was 0.019–0.055 s, with a harness mean of 0.0373 s. After the golf it is 17–21 ms, of
    which the service's `SIGN` takes 6–14 ms (F2 §4, F3 §3, F2 golf §4.1).
  - `o_est` was 0.065.
  - Each merge only concatenates two files and signs the joined trace.
- G-trust, low: published numbers that mislead.
- G-chains: none.

**What happened.**

- The smoke stream (`M = 4`, `n_f = 16`) lies inside the bundling capacity, which is 5 links at
  `n_f = 16`. So the smoke can never show whether an entry recurses.
- CM-R2's bound holds as stated: for this entry, `c = 5` at `n_f = 16` and `c = 0` at `2^16`.
- So the stream does price recursion at the season shape. At every smaller shape it prices file I/O
  and `SIGN`.

**Proposed changes.**

1. **Make concatenation visible.**
   - Publish, per link, `|π_i|` and the number of `QUERY` items the merge asked. The second needs a
     service counter per request.
   - Flag as "concatenation" a link whose merge asked no `QUERY` and whose `π` grew by one leaf
     proof.
   - Do not report `o_est` for such a stream.
   - Cost: the runner and one service statistic.
2. **Say in the design that `S` below the season shape is not a recursion measure.**

**Alternative considered.** A smoke `M` above the bundling capacity. Rejected: it would fail every
non-recursive entry's smoke run, the only end-to-end check such an entry gets.

### FB-7 (medium). Every hash through the service: a small tax here, a large share of the 100–200 ms target; `queryCap` stopped the season leaf

**Rule.**

- V4-14: every oracle query goes to the service, Merkle hashes included.
- `.contract/service/PROTOCOL.md` sets the caps: `2^20` bytes per query and `2^24` bytes per body.
  `SIGN` re-evaluates every query (C-m4).
- C-m8: the service's speed is in every score.

**Goals.**

- G-rec, medium (**estimate**): about 30–65 ms of service time per recursion step, derived below.
- G-chains, medium (**estimate**): 7–26% of a Flock-class prover's time.
- G-open, low: large absorbs must be chunked.
- G-trust: none. The tax is the price of closing O-25.

**What happened (measured).**

- **This entry's tax was small.** Before the golf (F2 §4):
  - the service cost 1.4–10% of proving;
  - at `n = 16`, the 10% came from 153 sequential Fiat–Shamir round trips of 57–78 µs each;
  - at `n ≥ 4,096` it was at most 2.4%;
  - a `2^16` leaf pushes 525,034 queries (1.09 GB) of Merkle traffic, at about 1.8 GB/s on 16
    connections.
- **After the golf, the share grows**, because the prover is 2.6–4.5× faster.
  - The in-process keyed Merkle phase is already 4.3–4.4% of a leaf at `n = 4,096–16,384`
    (`logs/golf/final-timings.log`).
  - The Fiat–Shamir round trips, about 37 µs each, are 13% of an `n = 16` leaf (F2 golf §4.1).
- **`SIGN` grows with the trace.** Each merge's `SIGN` re-hashes the concatenated trace: 0.011 s at
  2 leaves, 0.021 s at 5 (F2 §4).
- **`queryCap` stopped the season tree** (F3 §4.1).
  - The service refused a 1,572,898-byte absorb: the Ligero row `ū`, `2^16` elements of 24 B.
  - It came after 1,049,601 Merkle queries (4.33 GB) and 27.6 s, at 6.5 GB RSS.
  - The F2 fix pass now refuses such a query locally, with an explicit message.

**Estimate for a Flock-class prover.**

- **Inputs.**
  - Flock commits about 2 KiB of witness per compression (leanVM's Flock, F0 §4). That is about
    4 KiB of codeword at rate ½, all of it Merkle-hashed.
  - The service hashes at 37.6–38.7 ns per 64-byte block per connection, and serves 7.37 M 64-byte
    calls per second on one connection (**measured**, VM, `.contract/docs/v4/reviews/GB-golf.md`
    §1).
  - Flock proves `2^16` compressions in about 135 ms on an M4 Max ([CM] §3.3). That is about 33 µs
    of core time per compression on 16 cores.
- **The chain term.** Merkle hashing through the service then costs 2.4–8.7 µs of core time per
  compression: the first figure at the service's kernel rate, the second at its one-connection IPC
  rate. That is **7–26% of Flock-class proving**, on the same cores.
- **A recursion step** is about `2^15` compression-equivalents: two children, each with 16–17k
  compressions of hashing (F0 Q3). Its service costs:
  - about 20–40 ms of Merkle hashing on 4 cores;
  - 5–18 ms of Fiat–Shamir round trips (150–500 of them, at 31–37 µs each);
  - 3–8 ms of `SIGN` for a trace of 5,000–15,000 entries (scaled from 34 ms per `2^16`, GB §1).
  - That is **about 30–65 ms** per step: a third or more of the 100–200 ms target, which is stated in
    M4-Max units. On a runner the step itself is slower, so the share is smaller.

**Proposed changes.**

1. **Publish the service's CPU time per timed run** (from its cgroup's `cpu.stat`), beside `T_tree`
   and `t_link`. C-m8's tax then becomes visible per entry. Cost: the runner only.
2. **A faster path to the service.**
   - A shared-memory transport for `QUERY` batches: the double-buffered service of RO-9.
   - A documented low-latency path for sequential Fiat–Shamir queries. The golf's polled connection
     cut them from 9.6 to 5.6 ms per `n = 16` leaf at 4 threads (F2 golf §2.9).
   - Cost: the trusted runtime grows. Soundness is unaffected as long as the service computes every
     answer it returns, and signs only what it computed.
3. **Keep W5 as the recorded fallback** (V4-14), but not as a recommendation: it brings an
   extractability heuristic.
4. **Keep `queryCap` as it is.** `PROTOCOL.md` §3 is right that large data must be hashed in pieces.
   The defect is that the result JSON never said why the tree failed (H-4).

### FB-8 (medium). The assembly-only build works, but costs a sanitiser, a 9 MB generated file and reviewability

**Rule.** V4-9, design §3.3.

- The prover is one or more `prover/*.s` files in GNU `as` syntax.
- They are linked by the runner image's `gcc -static -pthread … -lm`, with no other input.
- Source may sit beside them, unbuilt.

**Goals.**

- G-open, medium: std Rust works only with fat LTO, `--emit asm`, a filter for LLVM 23's output, and
  a pinned toolchain that the entry must document itself.
- G-trust, low: soundness never depends on the prover (C-m7). Reviewability matters for spotting
  gaming, and a 9 MB `.s` is not reviewable. Reproducibility rests on the entry's own script.
- G-chains, low: CPU dispatch is the entry's job (`pclmulqdq` at run time, `x86-64-v2` baseline).

**What happened (measured).**

- **The raw `.s` does not assemble with GNU `as` 2.46** (F0 §1, F2 §2).
  - LLVM 23 emits `.prefalign` 428 times.
  - std's precompiled bitcode carries DWARF-5 `.file N "dir" "file"` lines, 284 of them.
    `-C dwarf-version=4` does not help.
  - The entry ships `sanitize-asm.py`, which drops 273,664 debug lines.
- **The result** (F2 fix pass).
  - `prover.s` is 9,238,056 B, emitted in 58–65 s.
  - It is deterministic across three clean builds, and the harness's sandboxed build gives the same
    binary hash.
  - The fix pass added a toolchain pin, `rust-toolchain.toml` (F2-m2).
- **Not tested.**
  - The runner's binutils 2.42. By reading, no directive newer than 2.30 remains (F2 review §3).
  - The `pclmulqdq` path on real hardware; it ran only under QEMU TCG.
- **A static-glibc caveat.** A static binary linked against the VM's glibc 2.43 needs AVX2 at
  start-up (`init_cpu_features`). So the `x86-64-v2` pin could not be tested on a pre-AVX2 CPU.
- **Repository cost.** Every prover change rewrites megabytes of a committed, generated file.

**Proposed changes.** Choose (1) or (2); do (3) in either case.

1. **Source builds in the sandbox, with organiser-pinned toolchains.**
   - For example, rustc, cargo and gcc or clang at fixed versions in the sandbox's read-only root,
     with dependencies vendored and no network. The binary's hash is recorded as now.
   - Cost: harness work (images, an offline build step, a build-time cap). The toolchain is trusted
     for nothing (C-m7). No soundness effect.
2. **Keep `.s`, with an organiser-shipped sanitiser and a reproducibility check.**
   - The entry declares its toolchain and build script.
   - The harness rebuilds the `.s` in the sandbox and records whether it matches. A mismatch is
     flagged, not rejected.
3. **Document the LLVM-23 recipe and the static-glibc caveat** in `harness/PROVER.md`.

### FB-9 (medium). `errorCap = 2^-128` per query excludes Flock's GF(2^128) as published

**Rule.** `errorCap` in `Contract/Security.lean`, and `Certificate.cap`: `S.ε ≤ 2^-128`, the knowledge
error per fresh query (V4-13).

**Goals.**

- G-open, medium: the most direct Flock port is not certifiable, and the restriction is invisible
  until a designer computes per-round errors.
- G-chains, medium: the GF(2^192) detour costs about 2× extension arithmetic in the zerocheck and the
  PCS. That is about 0.5–0.7× Flock's throughput, and a proof of about 550–750 KiB instead of
  386 KiB (**estimate**, F0 route ideation Q4).
- G-trust: the cap's purpose.

**What happened (estimate, F0 Q4).**

- In GF(2^128) a degree-2 sumcheck round errs per challenge query with probability
  `2/2^128 = 2^-127`.
- Flock's univariate-skip round errs with `126/2^128 ≈ 2^-121`.
- Both are above the cap, even in unique decoding. The entry used GF(2^192), with `ε = 2^-129` (D-1).

**Proposed changes.** We recommend (1) and no change to the cap.

1. **Document the grinding route in the rulebook.** This is **paper**, this report's own argument,
   not checked against Flock's skip round. No rule change.
   - Derive each round's challenge from an answer that must also carry `g` zero bits (a proof of work
     by the prover).
   - A fresh query then yields a challenge that is both valid and bad with probability
     `2^-g · d/|F|`. So `ε = 2^-(127+g)` for a degree-2 round, and `g = 7` covers the skip round.
   - The honest prover pays `2^g` service queries per round, batchable in one `QUERY`.
   - `CompleteWithError` admits the bounded search: 89·2^g attempts for `δ = 2^-128` (v3 §5.4).
2. **Or lower `errorCap` to `2^-120`.**
   - The end-to-end bound `(Q + qV)·ε` at `Q ≈ 2^30` becomes about `2^-90` instead of `2^-98`
     (design §2.4).
   - Cost: one trusted constant, and a soundness trade that the authors must choose.

### FB-10 (low). One signature on the empty trace certifies every query-free child: make `SigOk` vacuous there

**Rule.**

- `Submission.acc` checks `SigOk vk (traceDigest p.tr) p.σ` on every signed proof, the empty trace
  included (`Contract/Certificate.lean`).
- `decodeWit` reads a full signature for every signed child (`readSig`, `Contract/Extractor.lean`):
  1 + 133·4 + 16·4 = 597 words, 4,776 B.

**Goals.**

- G-open, low: every bundling or witness-sending entry pays 4,776 B per clear slot and one `SIGN`, and
  must think of σ0 itself.
- G-chains, low: the frontier moves by at most one notch.
- G-trust: none, if adopted as below.

**What happened (measured, kernel).**

- **σ0 costs one call.** One `SIGN` with count 0 (0.3 ms) gives σ0. It serves every clear slot of
  every bundle in the service's lifetime, since `SigOk` is stateless.
- **It is sound, and the review found it so.** σ0 is checked only so that the extracted witness is in
  `Rel`, and it holds for every key, so C-m1 does not bite (BLUEPRINT §5, F1 review §3.2).
- **The cost is bytes.**
  - A clear slot is `π`, 8 B of trace count, 4,776 B of signature and an 8 B index.
  - Each extra bundled leaf adds 9,704 B of witness, of which 9,552 B are two copies of σ0 (F2 §3.3).
  - That is 6.2% of the 153,367 B a leaf adds at `n = 16`.
- **The frontier effect** (computed from F3 §4.3). Removing those copies would have accepted:
  - `r = 3, n = 8`: 1,052,576 B − 14 slots × 4,776 B = 985,712 B;
  - a sixth stream link at `n_f = 16`: 1,063,913 B − 12 × 4,776 B = 1,006,601 B.
  - No other frontier rejection changes.

**Proposed change.**

- In `acc`: `(p.tr.isEmpty || SigOk vk (traceDigest p.tr) p.σ)`.
- In `readSigned`: read a signature only after a non-empty trace. An empty trace denotes a fixed,
  empty `Sig`.
- Cost:
  - about 2 trusted lines;
  - controls: a positive one (an unsigned query-free child is accepted) and a negative one (an
    unsigned non-empty trace is rejected);
  - the library's `witWords` and `decodeWit_witWords`;
  - the runner's signature canaries, skipped for files with `m = 0`. Alternatively, `FORMAT.md` lets
    such files omit the signature.

**Soundness (paper, against design §2.4).**

- **The composition walk is unchanged.** It uses a child's signature only at step 2: to conclude that
  the trace is genuine (every entry is the log's answer), or else to return a forgery.
  - An empty trace is contained in every log, so it is genuine without a signature. The forgery
    outcome can never come from it.
  - Steps 3–5 are unchanged. `runSeq [] (V vk c π) = some true` means that `V` decided with no query,
    so it decides the same way on every log.
- **Knowledge soundness is against `Rel (S.acc vk)`.** The change only adds witnesses: unsigned
  query-free children. A `V` that calls `acc` on its children (as this entry's `N` branch does)
  extracts them exactly as it does today.
- **Completeness must now also cover unsigned query-free children.** A recursive node circuit makes
  its signature check conditional on a non-empty trace.
- **The PRF hybrid and the key handling are untouched.**
- **What is lost.** A query-free proof is no longer bound to the run's `vk`. Nothing relies on that:
  such a proof carries its own witness. σ0 is already public in every bundle (FB-5), so the DoS
  surface does not change.
- **The cost to the Library.** The proof of `walk` in `Library/Compose.lean` needs one more case, for
  the empty trace.

**Alternatives considered.**

- **No trusted change: a Library "expanding" extractor.** It reads σ0 once from `π` and writes it
  into every slot of its output (F0 route ideation, point 2). It removes the bytes from `π`, but
  needs a custom `XProg` with a loop invariant.
- **Leave it.** It costs 6% of a bundle and one `SIGN`.

### FB-11 (low). Memory: the 11 GiB prover cap stopped the pre-golf stream leaf, not the golfed one

**Rule.** V4-13 and stage B's deviation 1: the prover cap is `11G` and the service cap `2G` in
`season.toml [memory]`. These are systemd units, i.e. GiB.

**Goals.**

- G-chains, low.
- G-open, low: the cap is tight for a prover with large tables at `2^18`.

**What happened (measured).**

- **The pre-golf prover.** A `2^16` leaf needed 15,788,764 kB (15.06 GiB; F2 §4, with F2-m3's unit
  correction). In the season stream it was OOM-killed at 11.14 GB RSS after 25 s (F3 §4.2).
- **The golfed prover.** The same leaf needs 2,585,312 kB (2.47 GiB), with the same bytes (F2 golf
  §2.13, §4.3): the tables are built later and the bit tables are freed early.
- **At `2^18`.** A leaf is estimated at about 10 GB (F2 golf §6): inside the cap, with little margin.
- **Flock.** BLAKE3 at `2^16` took 3.64 GB on this VM (F0 §3).
- So memory is not what bounds a well-engineered entry; `proofCap` is (FB-1).

**Proposed change.**

- None to the cap.
- Update the design's frontier rows. §3.6 and §4.3 still give 15.1 GiB as a stopping rule.
- Write the cap's unit as GiB everywhere (H-17).

The golfed prover has not been run through the harness at the season stream's shape. With its
2.47 GiB leaf, the expected stop is link 0 by `proofCap` (`|π|` = 2,791,559 B, unchanged by the
golf), not by memory.

### FB-12 (low). `qV` and `acc` as a recursive verifier sees them

**Rule.**

- `KS`'s query bound, in `Contract/Security.lean`: `∀ H c π, ((V c π).queries H).length ≤ qV`.
- `Submission.acc`, in `Contract/Certificate.lean`, which takes the whole `Submission`.

**Goals.**

- G-open, low.
- G-trust: none. RA-M2 is one trusted line, and it strengthens the relation.

**What happened.**

1. **The query bound does not bound accepted traces.**
   - Node completeness has to re-encode the witness, which needs every accepted child's trace to be
     shorter than `2^64` entries (`Signed.Fits`).
   - `KS`'s bound ranges over oracle functions, and a non-functional trace follows none of them. So
     the entry proved a path-uniform `AtMost`: 150 code lines (F1 RESULT §7.2).
   - The baseline team reported this. The contract fix pass then added `p.tr.length ≤ S.qV` to `acc`
     (RA-M2, `ea2e8ab`).
2. **`acc` must be restated.**
   - `V`'s node branch cannot call `Submission.acc`, which takes the very submission being defined.
     So the entry restates `acc` (`accWith`) and proves `accV_eq_acc` by `rfl`.
   - Every change to `acc`'s conjuncts must then be mirrored by every recursive entry. RA-M2 was one
     such change; adapting to it also ran into `wordBytes` (F1-m1).

**Proposed change.** Library only; 0 trusted lines.

- Define `accWith V qV vk c p`, with `Submission.acc S = accWith S.V S.qV` by `rfl`, and its fast
  twin. A future change to `acc` then changes one definition.
- Export `OProg.AtMost` and its algebra (this entry's `Queries`). It is the simplest route to `KS`'s
  bound for a verifier that sums static per-part bounds.

## 2. Harness and tooling defects

**Status column.**

- "accepted": reported to and queued by the core orchestrator (`.contract/docs/v4/FIXLIST.md`, or
  the contract fix pass).
- "proposed": new in this report.

| Id | Defect or friction | Evidence | Fix (status) |
|---|---|---|---|
| H-1 | The rebuild binding REJECTs a certified entry. It compares the gate tree (every `lean/*.lean`) with the comparator tree (`Solution`'s closure only) and counts artifacts missing from the latter as differences. All 110 shared artifacts were byte-identical | F3 §2.1; `logs/f3/cert-lean/`, `cert-frozen-comppoly.log` | build and compare `Solution`'s closure plus the badge (**accepted**, Q7) |
| H-2 | The organiser roots lack CompPoly (and ArkLib, VCVio, PolyFun), so a pinned dependency is checked as entry code. The message names a CompPoly module the entrant cannot change | F3 §2.2, F1-M1, F1-m4 | CompPoly roots (**accepted**, Q2); every pinned package (proposed, FB-4) |
| H-3 | A nanoda OOM kill stops the whole comparator scope. The Lean kernel never runs, the result reads "certificate does not check", and the buffered output is lost | F3 §2.4, friction 3 | separate scopes; `oom-kill` read and reported; unbuffered output (proposed) |
| H-4 | A failed tree run loses the prover's log, its status and `T_tree`. The `queryCap` refusal had to be reproduced outside the runner. A failed stream keeps no `leaf_s` or `merge_s` | F3 §4.1, friction 4 | write the run record on failure, with the prover's stderr tail (proposed) |
| H-5 | An OOM kill reads as "proof.bin: missing; stderr:". The runner ignores the exit status and the scope's result (C-m4 asked for the kill reason) | F3 §4.2, friction 5 | report exit status and `oom-kill` (proposed) |
| H-6 | "rejected by acc" gives no reason. Every frontier failure was the size cap, and telling that apart meant parsing the stored files by hand | F3 friction 6; F2-m5 (the prover now warns, `warn_caps`) | a reason code from the badge (size, trace length, query cap, signature, `V`). It costs nothing on the accept path (proposed) |
| H-7 | Per-check `acc` times for stream outputs, canaries, DoS and liveness are missing from the result JSON. The comparator's phases are invisible. A fresh tree spends 21–29 s in `lake env` start-up | F3 frictions 7–8 | record them (proposed) |
| H-8 | `T_tree` has 50 ms resolution: `Popen.wait(timeout=…)` polls. Three runs gave 0.917036, 0.917041 and 0.917063 s | F2 §6.5 | a blocking wait in a thread, or a pidfd (proposed) |
| H-9 | `t_leaf` = Σ of `M + 1` leaves over `M` (0.2512 s, against a mean of 0.201 s) | F2 §6.6, F3 friction 11 | as specified in [CM] §3.3 and design §3.5; label it, since it reads as a mean (**accepted** as doc drift, Q3) |
| H-10 | The service calibration uses `os.cpu_count()` threads under a 16-core `taskset`, and labels the result `threads_32` | F2 §6.7, `rfh/bench.py:180` | use `len(os.sched_getaffinity(0))` (proposed) |
| H-11 | A Unix socket path of 108 bytes or more fails in Rust's `UnixStream::connect`. The runner's path is short; local test paths are not | F2 §6.4 | a note in `PROTOCOL.md` (proposed) |
| H-12 | Undocumented setup: `RF_ORG_ROOTS`; `scripts/tools.env`, whose defaults point at this VM's checkouts; `evaluate.py` must run from the organiser checkout; `--work` must not exist | F3 friction 14 | document them in the `evaluate.py` header and the harness README (proposed) |
| H-13 | Each badge executable is 142.7 MB. The badge build compiles every out-of-closure dependency inside the certificate job: 695 `clang -c`, 74 s | F3 §2.3, friction 10 | prebuild the pinned packages' objects in `org-setup` (follows from H-2) (proposed) |
| H-14 | A private, writable package tree is required: 9.2 GB, copied in 4 min. The shared read-only tree had no build products. `org-setup` takes 5 min 56 s, 149 s of it hashing 34,290 `.olean` files. The manifest check runs 5 times per job. Lake's `globs = ["Foo.+"]` means submodules, not a name prefix | F3 friction 9, F1 RESULT §7.9 | write objects once; check the manifest once per job; document the glob (proposed) |
| H-15 | Liveness took 24.1 s and 121 MB for a 2.1 MB log at `r = 1, n = 16`. Only the 3,600 s badge timeout bounds it | F3 §3, friction 12 | publish its time; set a stated cap (proposed) |
| H-16 | The reason reads "gate: gate: REJECT …": the prefix is doubled | F3 §2.2 | trivial (proposed) |
| H-17 | Docs drift. See the four items below | FIXLIST Q3, Q4, Q6; F3 §4.2; F2 golf; F1 golf | partly **accepted** (Q3, Q4, Q6); the rest proposed |
| H-18 | Stage B's mock badge is not self-contained: it imports `wots_ref` from `tests/service/` | F2 §6.8 | vendor the module (proposed) |

**H-17's four items.**

- `FORMAT.md` stated `tr.length ≤ qV` before the contract did (Q6). Closed by RA-M2.
- The baseline was described as "will be PROVISIONAL", the cgroup as one 13 GB, and the mean leaf
  time; the README pin was stale (Q3). Fixed at `88d4566`, except the label of H-9.
- Computability and `ByteArray.data` (Q4) are stated in design §3.3. `AGENTS.md` is still pending.
- Open, and new in this report:
  - the cgroup unit is "11 GB" in the design but `11G` (GiB) in `season.toml`; the kill was measured
    at 11.81 GB;
  - design §3.6 and §4.3 still give the pre-golf memory (15.1 GiB, now 2.47 GiB);
  - they also give the pre-golf `acc` times (0.20 and 0.45–0.50 s, now 0.09–0.14 and 0.19–0.21 s).

## 3. What worked well

- **The SROM core held.**
  - Building, reviewing and attacking the entry found no soundness issue. F1-M2 is a denial of
    service, not a soundness issue.
  - C-m1 did not bite the σ0 design: σ0 is checked only so that the extracted witness is in `Rel`,
    and that holds for every key.
  - v3's potential and `final` carried over: a bundle of `k` SNARKs costs no extra error, because
    `snark_final` is a statement about the log alone (F1 review §3.2).
  - The soundness core's modules are byte-identical to v3's.
- **The port was mostly mechanical.**
  - 47 of 65 modules were unchanged; 886 new and 310 changed lines in 17,252.
  - The clean build took 2 min 38 s with a peak of 4.12 GB (F1 RESULT §1, §5).
  - The library's v4 `Words` lemmas made `decode_leaf` a one-lemma re-proof.
- **The library served bundles unchanged.**
  - `decodeWit` ignores trailing words, so the library's copy extractor (`E`, `ext`, `fuel`,
    `computes`) works for `encode W ‖ T` as it is.
  - The fast twins (`chainEndF`, `leafStmtF`, `SigOkF`, `traceDigestF`) were used directly, with
    their equality theorems.
- **`SIGN` with count 0** gave σ0 in one call of 0.3 ms.
- **The interface documents were precise enough** (`FORMAT.md`, `PROTOCOL.md`, the contract).
  - An independent native `acc` (`acc.rs`, `format.rs`) matched the Lean `V` branch by branch and
    byte by byte, on the first try (F2 review §1).
  - The compiled Lean `acc` accepted F2's service-signed proofs.
  - The real Lean badge accepted the nested bundles: the `r = 2` root in 931 ms, and stream nodes 2–4
    in up to 1,311 ms. That closed F2-M1 (F3 §3).
- **The oracle and the service behaved as specified.**
  - The in-process keyed oracle equals the service at `n = 1, 16, 64`, so the prover can be
    developed and benchmarked offline (F2 §3.2).
  - The service moved 1.8 GB/s of Merkle traffic and was never a bottleneck for this entry.
- **The assembly route is deterministic.** Three clean builds gave the same `.s`, and the sandboxed
  harness build gave the same binary hash. The sandbox ran a std-Rust prover with threads, sockets
  and non-blocking I/O unchanged.
- **The harness's messages at the frontier are exact.** For example: "tree1 root took 945.893 ms,
  above T_V = 0.015 ms" and "stream1 node 6 rejected by acc".
- **The harness's checks did their job.**
  - The canaries (69 + 18 + 29 rejected) and liveness ("extracted and checked 3 witnesses from a log
    of 30820 entries") ran on the service's authentic log.
  - A certificate job that fits 16 GB with the Lean kernel (peak 4.11 GB).
- **The feedback channel works.** RA-M2, Q2, Q4, Q6 and Q7 were taken up by the core within the
  stage.

## 4. Open questions for the rules' authors

1. **Is excluding non-recursive entries from the season ranking intended?** If so, should G3 be
   restated to say so? If not, which of FB-1's measures do you adopt? Our estimate is that any
   interim shape with a floored `T_V` would rank witness-sending first.
2. **Q11.** Which option for binary-field verifiers, and on which runner measurement (FB-2 (3))?
3. **The Library.** Should it carry a generic bundle (FB-3) and a compiled-verifier kit (FB-2 (2))?
   Who reviews them?
4. **The second kernel.** Is nanoda to be run off CI for records, on a machine with well over 20 GB
   (FB-4)? Or is a record checked by the Lean kernel alone final?
5. **Crafted inputs.** Should the crafted-input column use inputs shipped by the entrant, inputs
   added by reviewers, or both? Or is an obligation on `V`'s cost wanted in a later season (FB-5)?
6. **`SigOk` on the empty trace.** Is making it vacuous (FB-10) acceptable at about 2 trusted lines?
7. **`errorCap`.** Document grinding, or lower the cap to `2^-120` (FB-9)?
8. **The prover's build.** Source builds with pinned toolchains, or `.s` with an organiser
   sanitiser (FB-8)?
9. **Completeness and `proofCap`.** The entry's Lean `P` sends node witnesses plainly, so its node
   proofs exceed `proofCap` (D-5). The certified completeness is a statement about `V`, not `acc`
   (v3 §6.4, design §2.6), so it covers proofs the harness never accepts. Should completeness be
   required only for proofs within `proofCap`, or is that left to the harness's concrete checks, as
   now?

## Appendix A. Evidence index

Paths are relative to this repository. `F/` is `docs/v4/flock-baseline/`; logs are gitignored.

| Finding | Records | Logs |
|---|---|---|
| FB-1 | `F/stages/F3-harness-RESULT.md` §4.1–§4.3; `F/stages/F2-prover-RESULT.md` §3.3 and fix pass; `F/reviews/F0-route-ideation.md` points 1, 3 and Q3–Q4; `F/stages/F0-probes-RESULT.md` §2–§4 | `logs/f3/frontier-table.txt`, `fr-*.log`, `bench-season*.log`; `logs/f2/fix/links-n{16,1024,4096}.log` |
| FB-2 | F3 §3, §4.4; `F/stages/F1-lean-RESULT.md` §5, §7.4–§7.5; `F/stages/F1-golf-RESULT.md` §2; F2 §3.5, §4; core B RESULT §3 and design §3.5 | `logs/f3/fr-tv-*.log`, `bench-smoke-reverify.log`; `logs/lean/run/verify-final.log`; `logs/golf-lean/verify-abab.log`, `prof/` |
| FB-3 | `F/BLUEPRINT.md` D-2, §1.4, §2; F1 RESULT §1, §5, §7.8; F0 §2; F2 §3.3 | `logs/lean/run/verify-final.log`, `probe-B.log`; `logs/f2/selftest-asm.log` |
| FB-4 | F3 §0, §2.1–§2.4; `F/reviews/F1-lean-review.md` F1-M1, F1-m4; F1 RESULT §7.1 | `logs/f3/cert-*.log`, `cert-nanoda.curve`, `nanoda-standalone/`; `logs/lean/noncomputable-probe.log` |
| FB-5 | F1 review F1-M2; BLUEPRINT D-6; F3 §3, friction 13 | the review's `attack-run.log` (its session scratchpad); `logs/f3/bench-smoke.json` |
| FB-6 | F2 §4; F3 §3; `F/stages/F2-golf-RESULT.md` §4.1 | `logs/f3/bench-smoke.json`; `logs/golf/ab/final-shapes-t{4,16}.log` |
| FB-7 | F2 §4; F2 golf §2.9, §4.1; F3 §4.1; core `GB-golf.md` §1 | `logs/f2/bench-asm-n*.log`; `logs/golf/final-timings.log`; `logs/f3/diag/tree-r6-n2p18.log` |
| FB-8 | F0 §1; F2 §2 and fix pass; `F/reviews/F2-prover-review.md` §3, F2-m2 | `logs/probes/asm/`; `logs/f2/build-asm-*.log`, `determinism.log`; `logs/f2/fix/determinism.log` |
| FB-9 | F0 route ideation Q4; BLUEPRINT D-1 | — |
| FB-10 | BLUEPRINT §1.4, §5; F2 §3.3; F1 review §3.2; F3 §4.3 (arithmetic in FB-10) | `logs/f3/frontier-table.txt` |
| FB-11 | F2 §4 and fix pass (m3); F2 golf §2.13, §4.3, §6; F3 §4.2; F0 §3 | `logs/golf/ref-65536.log`, `final-65536.log`; `logs/f3/bench-season-stream.log` |
| FB-12 | F1 RESULT §6.1(4), §7.2–§7.3; F1 review F1-m1; `F/stages/F1-lean-JOURNAL.md` | `logs/lean/build-core-ea.log` |
| H-1 … H-18 | F3 §5 (frictions 1–14); F2 §6 (frictions 1–9); core `FIXLIST.md` Q2–Q7 | `logs/f3/`, `logs/f2/` as cited in each row |
