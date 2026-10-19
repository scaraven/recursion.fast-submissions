<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `DISCUSSION.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# recursion.fast — interactive design discussion (2026-10-13)

Source: `recursion-fast-interactive-convo-prompt.md`. The report (`report/`, v1.0, 162 pp.) is kept as
is; this file records each question, the answer given, the decision, and the changes the decision
implies for the report. Section references are to the report.

Status key: **decided** (user confirmed) · **proposed** (answered, awaiting the user) · **open**.

---

## Q1 — Extractor: agent-supplied RISC-V extractor with a proved cycle bound — **decided**

**Question.** The report accepts that L1 "knowledge" collapses to soundness because the Lean
extractor is unbounded. Instead: the agent supplies the extractor as RISC-V bytecode, equivalent to
a valid computable extractor, with a proved bound on its cycles; the bound is set heuristically,
since the extractor should be easy to code.

**Answer (summary).**
- Agreed. This is the L2 track of decision S-3 / issue Q-1 made mandatory for ranked records.
- Formulation: *the extractor is the program.* `extractMid m s tr w := decode (run img (fuel := B k)
  ⟦m, s, tr, w⟧)`, default on fuel exhaustion. The KSF laws (`Security.lean:76-84`) are stated about
  this function directly, so no separate agreement theorem and no separate cycle-bound theorem: the
  bound is required exactly on the inputs where the `next`/`full` laws fire (fuel exhaustion gives
  the default witness, which fails the law). Submitters still write a Lean extractor plus a
  refinement lemma internally, as for `Agrees`.
- Heuristic bound: **B(k) = 2^(2k+16) cycles per extractor call** (quadratic in oracle length).
  Rationale: the checker never runs the extractor; B only has to (i) exclude brute force
  (≈ 2^(64·n_w)), (ii) keep t + t_E ≪ 2^128 so the compiled knowledge bound's collision term is
  unchanged (k = 24 gives 2^64). Quadratic admits Berlekamp–Welch via Gaussian elimination.
- What it fixes: genuine "knowledge-sound" and "recursion-ready" labels (PCD bound has N·t_E);
  closes the always-satisfiable-index overfitting hole more cleanly than the benchmark rule
  (a bounded extractor cannot be proved to find hash preimages).
- Consequence: extraction = decoding, so entries are confined to the Johnson radius (list decoding)
  or the unique-decoding radius; conjecture-based "beyond Johnson" parameter sets are out. **User
  note:** Guruswami–Sudan is formally verified and executable in CompPoly
  (`CompPoly.Bivariate.GuruswamiSudan.{Core,CoreCorrectness,Executable,Filter,FilterCorrectness,
  Interpolation,Root.RothRuckenstein,Root.Alekhnovich}` at pin 572f997), so agents can propose PCSs up to
  the Johnson bound; the remaining burden is the RISC-V refinement of that Lean decoder. D3's
  parameter work already sits at Johnson (268/262 queries), so the design's numbers do not move.
- Contract changes needed: serialisation and a size bound for the submitter-chosen `WitMid m` types;
  `ExtractorImage` structure; negative control: brute force fails B(k).
- L1 stays as an allowed *intermediate* (CI passes, listed, unranked); ranked records require L2.

**Decision.** Mandatory L2 with the extractor-is-the-program formulation, B(k) = 2^(2k+16), L1
unranked intermediate. Confirmed by the user 2026-10-13.

**Proposed report changes.**
- §8.4 (`subsec:sec-extractor`), decision S-3: rewrite as "ranked records require the efficient
  extractor"; keep `thm:sec-collapse` as the motivation; add the `ExtractorImage` definition and
  B(k); replace "contract-fixed polynomial cycle bound" with the explicit 2^(2k+16).
- §8 table row "Extractor": "L2 cycle bound" → "B(k) = 2^(2k+16), extractor is the image".
- §11 benchmark rule "no index provably always-satisfiable": demote from load-bearing to defence in
  depth; explain why.
- §9 recursion: "recursion-ready" label now follows from L2; update the PCD paragraph (N·t_E).
- §14 issue Q-1: move from P2/phase 4 to P0/phase 1; add the CompPoly Guruswami–Sudan pointer
  (`CompPoly.Bivariate.GuruswamiSudan.*`) as the library asset that makes the Johnson regime
  reachable; add a new issue: `WitMid` serialisation and size bound.
- §12 baseline: add the trivial extractor image (copies the witness out of the proof) and its
  certification; §C: new check step.
- Appendix A: `ExtractorImage`, modified `KSF` (extractor supplied as image).
- §13 threats: new row "extractor image exhausts fuel on good inputs" (caught by `next` law).

---

## Q2 — Cost model: one reference machine and measured wall time instead of four zkVM profiles — **open, revisit later**

> 2026-10-13: the user is not satisfied with the cost model as discussed so far (neither the
> report's four-profile design nor the hybrid below). Parked; to be revisited after Q3–Q5.

**Question.** The four-zkVM pricing is overly complicated. Alternative: build one machine and
measure the wall time of prover and verifier over many tasks (2-to-1 recursion, hash chains, RISC-V
bytecode). Not fixed on it — how does it deal with overfitting?

**Answer (summary).** See the conversation of 2026-10-13. Key points:
- Three distinct overfitting modes: (a) *model* overfitting (sig.golf: exploiting the gap between
  the cost model and reality; D4 measured a flat model's relative error at ≈ 15× across kernels);
  (b) *benchmark* overfitting (specialising to the test inputs); (c) *noise* exploitation (±2–5%
  wall-time noise vs sub-percent record margins; submit variants, keep the lucky run).
- Measured wall time fixes (a) only for the machine measured, does nothing for (b) — it makes (b)
  worse because the score now depends on the inputs run — and introduces (c). It also cannot
  re-score old records once the hardware changes.
- For recursion the relevant "machine" is a zkVM prover, not a CPU: hashes, memory and parallelism
  have entirely different relative prices (ZisK BLAKE2s precompile ≈ 72 logic-op equivalents vs
  ≈ 1,560 native cycles in software; verifier parallelism buys nothing in a zkVM, where prover cost is
  total work). Measuring one real zkVM is model overfitting to a real target instead of a synthetic
  one; the four-profile geomean existed only to make such tuning unprofitable.
- The proved 18-counter CostVec is the machine-independent measurement; pricing is cheap
  post-processing, retroactively re-appliable. That is the asset to keep.
- Agreed that the pricing layer is too complicated (four profiles, two of them with guessed hash
  prices, geomean, blow-up factor, FS surcharge, byte charge).

**Recommendation (hybrid).**
1. Rank by the proved CostVec priced under **one published reference profile**; drop the geomean.
   Preferred reference: a zkVM the organisers control (leanVM/leanerVM family), whose per-class
   trace-area costs are then *facts* about the reference, not calibrated guesses.
2. Keep the latency board (U3) as the native/second opinion.
3. Use the user's reference machine for **calibration and audit**, not ranking: each season run the
   benchmark tasks (2-to-1 step, hash chains, RISC-V bytecode execution) on it; publish measured time
   as an unranked column; **divergence tripwire**: a record whose measured/predicted ratio deviates
   from the field's median by more than a factor x is flagged and the profile re-fitted. This is the
   feedback loop sig.golf lacked: model overfitting is detected by measurement and corrected by
   re-pricing, which is free because the proved object is the counter vector.
4. Prover wall time: not scored (that is a prover-engineering contest), but a measured **prover
   feasibility budget** on the reference machine becomes a pass/fail gate for the completeness tests
   (closes the open gap that `prover` has compiled code but no feasibility requirement).

**Clarification asked (2026-10-13): which prover, and the final equation.** Two provers are in play:
the *submitted* prover (agent's; completeness proved in Lean; wall time on the reference machine is
a measured pass/fail budget, not a proved bound, not in the score) and the *reference zkVM prover*
(organiser-fixed; proves the execution of the submitted verifier, i.e. the recursion step; its cost
table supplies the weights; its measured wall time is the audit column). Agents prove nothing about
either prover's running time; they prove the verifier's CostVec over all accepting runs.

Final equation (hybrid), per class k ∈ {16, 20, 24}, c_k certified by `AcceptingCostAtMost(k, c_k)`,
shape quantities static from the declared round shapes, one reference profile (w, P_H, λ):

    S_k      = ( w·c_k + (P_H+35)·q^lev_k + P_H·(q^bytes_k/64 + q^count_k) + FS_k + ⌈λ·B_k⌉ ) · max(1, V_k/16)^{1/4}
    Score_zk = (S_16 · S_20 · S_24)^{1/3}                      (ranked; lower is better)
    T2:        same with S_leaf + S_fold + S_dec/64
    Score_lat= (T_16,16 · T_16,20 · T_16,24)^{1/3}             (latency board, unchanged)

    Audit (unranked):  r_k = T_meas,k / S_k, T_meas,k = reference zkVM wall time proving the verifier
                       image on the class-k benchmark proofs; flag if r_k ∉ [median(r)/x, x·median(r)];
                       re-fit (w, P_H) each season from the field's (c_k, T_meas,k) pairs.
    Prover gate:       T_prove,k (submitted prover on the reference machine, benchmark instances)
                       ≤ Budget_k, pass/fail.

Change from the report's §10: four profiles and the 12-th root → one profile and the cube root; the
audit column and the prover gate are new; every proved object is unchanged.

**Open for the user.** Accept the hybrid? Which reference zkVM (leanVM/leanerVM-derived exact cost
table vs a public zkVM such as ZisK)? Tripwire factor x (suggest 2)? Budget_k for the prover gate?

**Proposed report changes (if accepted).**
- §10 (`sec:cost`): replace the four-profile geomean (decision on `Score_zk`) by one reference
  profile; add the audit column and the divergence tripwire; keep the latency board; move the
  profile table of D4 §4 to an appendix as "calibration history".
- §6 architecture: a "calibration and audit" stage (reference machine runs, unranked).
- §11 benchmark: the benchmark tasks are the calibration set and the completeness/prover-budget
  set, not the score's domain (cross-reference Q4).
- §14: issue M-4 and the profile-related M-items re-scoped; new issue "reference zkVM cost table
  and re-calibration procedure"; new issue "prover feasibility budget" (P1).
- D4-1 and D4-7 updated accordingly (design notes, not the report).

---

## Q3 — Is bounding only accepting runs right for a SNARK verifier? — **decided**

> **Decision (user, 2026-10-13): score all runs on both boards.** The accepting-only bound (U2) is
> dropped entirely: `AcceptingCostAtMost`/`AcceptingLatencyAtMost` become all-runs bounds; `run`
> must return counters with the verdict; fuel exhaustion distinguished from rejection. (ots.golf's
> `upper-riscv` track already bounds every execution, accepting or rejecting — R1 note line 33.)
> The "recommendation" and "open" paragraphs below are superseded; the report changes stand with
> "drop the refinement" in place of "capped refinement".

**Question.** sig.golf can ignore the signature verifier's rejecting path because rejection is
decided natively and only accepting signatures are proved in the zkVM. That is not the case for a
SNARK verifier. Is scoring accepting runs only (U2) a good idea?

**Answer (summary).**
- Two deployments. *Recursion*: the honest outer prover runs the inner verifier natively first
  (10^3–10^5× cheaper than proving) and only proves accepting runs; this is exactly sig.golf's
  pattern, so acceptance-only is right for the recursion board. *Native verification* (light
  client, node, decider on a received accumulator): the verifier runs on adversarial inputs and the
  cost of a rejecting run is the DoS exposure. There the report's only bound is the fuel cap
  2^36 steps per hart (tens of seconds per garbage proof): a real gap. The user's intuition is right
  for this deployment.
- The gap is smaller than it looks in this contract: the tape `P.tape i x tr` has a fixed layout
  determined by the declared round shapes (lengths fixed, 1 MiB cap, fixed QUERY leaf length and
  depth), so the adversary controls contents, not lengths. Content-dependent control flow is
  limited to data-dependent branches and variable-time arithmetic. For a sane verifier the
  all-runs maximum equals the accepting maximum or is lower (early rejection). The accept
  hypothesis is mostly a proof convenience (downstream code may use "the check passed" facts).
- Contract gap found while checking: `run` returns `none` for every rejection (fault, trap,
  rejecting HALT, failed child, fuel exhaustion), so a rejecting run's counters are not observable
  (`Cost.lean:31-37`, `Machine.lean:379-381`). An all-runs bound needs `run` to return the counters
  with the verdict, and fuel exhaustion to be distinguishable from rejection.

**Recommendation (invert the default).**
1. Base requirement for every record: `AllRunsCostAtMost(k, c^all_k)` — every run, accepting or
   rejecting, halts with counters ≤ c^all_k. This is the DoS bound; the latency board scores it
   (`AcceptingLatencyAtMost` → all runs likewise).
2. Optional refinement for the recursion board: `AcceptingCostAtMost(k, c_k)`, defaulting to
   c^all_k when not supplied, with the requirement c^all_k ≤ 2·c_k componentwise (DoS exposure at
   most twice the honest cost; the factor is proof slack).
3. Fast-failing paths stay rewarded in the only sense that matters: early rejection is cheap and
   never raises a maximum; the one thing the change forbids is a rejecting run dearer than any
   accepting run, which is precisely the DoS case.
4. Proof burden: modest — bound-check tape-derived values before use and prove loop bounds without
   the accept hypothesis; the 2× slack keeps it loose. Baseline: identical bounds.

**Open for the user.** Adopt all-runs as the base with the capped acceptance-only refinement, or
drop the acceptance-only bound entirely? Factor 2?

**Proposed report changes (if accepted).**
- §10 decision on the accepting-run scope (U2) → all-runs base + refinement; §8/§13 new threat row
  "rejecting run dearer than accepting" (DoS); §C and §12 baseline: certify both vectors.
- Appendix A / contract: `run` returns counters with the verdict; `AllRunsCostAtMost`,
  `AllRunsLatencyAtMost`; the ratio requirement; fuel exhaustion distinguished from rejection.
- §5 brief review: note that U2 is kept as a recursion-board refinement, not the safety baseline.
- §14: new P0 issue "all-runs bound and observable counters on rejection".

---

## Q4 — Is "all R1CS of a size class" overly general, and is the statement size bounded? — **decided**

> **Decision (user, 2026-10-13): Option A — keep the universal R1CS relation.** B′ (semantic
> relations) rejected: it would require large relation/security definitions in the trusted base.
> Instead the *cost function* is to steer verifiers towards being good at hash-chain proofs and
> 2→1 recursion. Q2 (cost function) is therefore re-opened with that goal and with simplicity as a
> requirement ("overly complicated and hard to reason about"). The statement-size remark stands
> (nx = 2^10 is too large; a few digests suffice).

**Question.** The cost model is defined over the entire relation; many instances are irrelevant to
the application (SNARKs proving hash-based operations: XMSS, SPHINCS). Is that overly general? Is
the statement size bounded?

**Answer (summary).**
- Statement size: yes, bounded and fixed — `nx = 2^10` K-elements (8 KiB) for every class
  (`R1CS.lean:28`, `classSizes`); smaller instances are padded. Likely too large and the wrong
  shape for the application: absorbing `x` costs 256 compressions per run (FS term), and practice
  is to pass digests and hash the real public input in-circuit. Suggest a few digests (2^5–2^6
  elements) or per-relation statement types.
- Generality: agreed it is overly general for the stated application. It was chosen as the
  overfitting defence (a cost theorem over all indices makes hard-coding benchmark circuits
  useless) and it implies a *universal/holographic* architecture: the index is an oracle and the
  verifier must run a sparse-matrix evaluation argument (Spark/Lasso-style memory checking), a
  cost that fixed-circuit STARKs, with constraints compiled into verifier code, do not pay. The
  universal class therefore pre-decides an architecture and penalises the way production systems
  and the application are built (feeds Q5).
- With Q1 (bounded extractor) and ∀x, ∀proof quantification, the overfitting defence no longer
  needs index-universality; specialising to a fixed circuit is what deployment does (one VK per
  circuit).
- Knowledge vs succinctness (for the benchmark choice): knowledge soundness has content only for
  *hard* relations, where no efficient algorithm finds a witness from `x`. Signature relations are
  hard (XMSS: given (pk, msg), find a signature = forgery), and for them plain soundness is
  vacuous — every honestly generated (pk, msg) has a signature, so accept-all is "sound" — only
  the bounded extractor (Q1) rules accept-all out. The user's own application is the case where
  Q1 is load-bearing. Deterministic computations (RISC-V execution: trace computable from
  program and input) are the opposite: knowledge is vacuous and the content is succinctness; the
  cost model handles it because the "recompute" verifier pays the whole computation. Avoid
  relations that are both easy-witness and cheap (hash chain with public start).

**Options.**
- A. Status quo: universal R1CS classes k ∈ {16, 20, 24}.
- B. Fixed benchmark circuits as R1CS indices (hash chain with hidden start, Merkle batch,
  XMSS-verify(N), SPHINCS+-verify, RISC-V execution, the recursion step); soundness, completeness
  and cost over those indices, all x, all proofs. Universal protocols remain admissible.
- B′. **Semantic relations** (recommended): each benchmark relation is a Lean predicate
  `Rel(x, w)` (e.g. "these N XMSS signatures verify under pk for msg" with a fixed hash), not an
  R1CS. The agent chooses the arithmetisation (R1CS, AIR, chips, lookups, buses) and proves
  knowledge soundness against `Rel`: the extracted witness is a signature. R1CS-based entries
  decompose the proof into R1CS knowledge + circuit correctness (R1CS witness → signature), a
  gadget-correctness proof deployments need anyway. `Rel` must be decidable (completeness tests,
  extraction target). Statement format per relation (fixed serialisation for the accumulator).
  Scaling axis = relation parameter (N, chain length) instead of k.

**Costs of B′.** Organiser burden: Lean reference implementations of the benchmark relations over
a binary-field hash (hash choice is a separate decision: Keccak-f / Grøstl–AES (Binius) / Vision /
SHA-256–BLAKE2s as deployed); loss of the universal-SNARK research goal and the k-class scaling;
the holographic machinery (`Index`, `IDX` oracle, sparse matrices, `pad`) leaves the trusted
contract or becomes one admissible arithmetisation in the library.

**Open for the user.** A, B or B′? Benchmark relation list and parameters? Hash function?

**Proposed report changes (if B′).**
- §7 protocol model and §11 benchmark: relation = finite family of decidable Lean predicates with
  per-relation statement types; remove `classSizes`/`pad`; benchmark set = the relations; the
  knowledge-vs-succinctness criterion for choosing relations (hard relations + deterministic
  computations; no easy-witness-and-cheap relations); the always-satisfiable rule → replaced by
  "hard relation" rationale with Q1.
- §8 security: `KSF` against `Rel` directly; note the decomposition for R1CS-based entries.
- §9 recursion: accumulator statement serialisation per relation.
- §10 cost: the cost theorem quantifies over x and proofs for each relation; remove the
  FS term for a 2^10-element `x`.
- §12 baseline: trivial verifier per relation (proof = witness; e.g. the signatures themselves).
- §14: new P0 issues "benchmark relation reference implementations in Lean", "binary-field hash
  choice"; re-scope Q-5 (Boolean track) and the index-related issues.
- Appendix A: `Relation` structure replaces `Index`/`Sizes`.

**Follow-up (user): explain B′ more simply.** Answer given 2026-10-13, in brief: the competition
fixes *what must be true* (a Lean predicate such as `XMSS.verify pk msg sig = true`) instead of *how it
is written as constraints* (R1CS). The agent's single end-to-end theorem is "if my verifier accepts
(pk, msg), my bounded extractor outputs a `sig` with `XMSS.verify pk msg sig = true`". The
circuit-correctness step (R1CS satisfiable ⇔ signatures valid), which in production is outside
the SNARK's security proof and is where under-constrained-circuit bugs live, moves inside the
theorem. The trivial baseline is the native verifier (proof = the signatures); the finish line is
beating it. Inputs and proofs stay universally quantified, so nothing is gameable through them;
accept-all would require a provable forger. Trusted surface: a short readable spec of the scheme
instead of 2^24-entry matrices.

---

## Q2 (revisited) — A simple cost function that steers towards hash chains and 2→1 recursion — **proposed**

**Goal (user).** Keep R1CS; make the cost function simple enough to reason about; incentivise
verifiers that are good at hash-chain proofs and 2→1 recursion; keep U3 (no flat-cost overfitting,
account for parallelism).

**Why v0.3's model is complicated.** Each term closes one gaming channel: 18 counters (memory,
first touch), four profiles (zkVMs differ), leaf and level pricing (free Merkle caps), FS surcharge
(free derived values), byte charge (monotonicity), blow-up factor (rate → 0), latency board
(parallelism). The simplification principle: one unit (an executed instruction), one ratio (a hash
compression = P_H instructions), hard caps instead of soft penalties, work for recursion, span only
on an optional latency board.

**Observation that licenses the flat instruction cost on the recursion board.** In a zkVM the
non-precompile instructions cost within a factor of about 2 of each other including fetch/decode
(SP1 Hypercube: add ≈ 144, mul ≈ 193, load ≈ 181, branch ≈ 156 trace cells; ZisK: add 93, logic 128,
mul 165; division is the outlier). The 15× relative error of the flat model (D4) is a *native-core*
phenomenon (caches, branch prediction, variable latency), i.e. a latency-board problem. Hashing is
the one thing that is far from flat (precompile ≈ 70–200 instruction-equivalents; software BLAKE2s
≈ 700–1,500 native cycles), and in the IT-model design the verifier image never hashes: hashing is
priced statically from the declared shapes. So "flat instructions + one hash price" is close to the
real zkVM cost structure, not a sig.golf-style simplification.

**Proposed model (v0.4-simple).**

    Score_k = I_k + P_H · H_k                                    (ranked at k = 24; k = 16, 20 proved and displayed)

    I_k  = proved bound, over every index of class k, every x and every proof string, on
           (instructions executed + memory words first touched), all runs (Q3)
    H_k  = hash compressions implied by the declared shapes (static, no proof needed):
           Σ_queries ( depth + ⌈leaf bytes / 64⌉ )  +  ⌈ (bytes absorbed + bytes squeezed) / 64 ⌉
           absorbed = 32·rounds + 8·(|VK| + nx); squeezed = 24·n_E + 8·n_idx
    P_H  = 128   ("one hash compression costs 128 instructions"; precompile regime midpoint)

    Caps (pass/fail, not scored): blow-up V ≤ 8 (prover commits ≤ 8× the witness), image ≤ 1 MiB,
    tape ≤ 1 MiB, rounds ≤ 2^14, fuel 2^36; nx = 2^6 (a few digests).
    Recursion: T1 score = Score_24 (one verification ≈ one 2→1 step up to the factor 2);
               T2 score = Score(fold) + Score(decide)/64.
    Latency board (optional, parallelism): T_16 = (I^work + P_H^nat·H)/16 + span, P_H^nat = 1,500.

Dropped: four profiles, geomean over 12, byte charge λ, blow-up exponent, 18-way weights.
Re-pricing stays free: the proved objects (I_k, the shape) are unchanged by any later P_H.

**Worked example (illustrative, k = 24, FRI-shaped).** ≈ 260 queries × depth ≈ 24 → ≈ 6.2k path
compressions; leaves 260 × ⌈256/64⌉ ≈ 1k; FS ≈ 0.5k; H ≈ 7.7k → ≈ 0.99M at P_H = 128; verifier
arithmetic I ≈ 0.1–0.2M; Score ≈ 1.1–1.2M, hash-dominated; the lever is queries × depth.

**Steering towards hash chains and recursion.** Weights cannot make a universal verifier "better
at hash chains": its cost is index-independent. The levers are
(a) small statements (nx = 2^6: hash-chain and recursion statements are a few digests);
(b) the score *is* the recursion-step work (T1: one verification; T2: fold + amortised decide);
(c) optional: the cost theorem's index domain restricted to a `Uniform(s, ℓ)` sub-class (one gadget
    of s constraints repeated ℓ = 2^k/s times, chained) — ~20 lines of Lean, no hash chosen; rewards
    exploiting repetition, which hash chains and zkVM traces share (removes the sparse-matrix
    argument for specialised verifiers); universal verifiers are unaffected;
(d) rejected by the user: fixed benchmark indices with a concrete hash gadget (too much definition).

**Overfitting check.** Instruction-count tricks: table lookups and arithmetic both cost 1, as in a
zkVM; unrolling is bounded by the image cap; tables by the first-touch charge. Hash vs arithmetic:
the agent cannot change P_H, only the shape; model error on the hash term ≤ 1.8× against real
precompiles. Parallelism: not scored on the recursion board (correct: a zkVM pays total work),
scored on the latency board.

**Open for the user.** P_H = 128? One scored class (k = 24) or geomean of three? Keep the optional
latency board or drop it? Steering option (c)?

## Q6 — v3: a non-interactive argument in the ROM, a digest relation, whole-tree wall time — **decided** (2026-10-15 → 2026-10-19)

**User's gripe with v2.** It forces every agent through one configuration of the BCS transform
(the organiser's compiler: one hash, one arity, one sponge) and cannot express hash-based designs
that are not a succinct verifier per level, such as accumulation. Fields are a large part of the
cost, and the fixed GF(2^64) relation should not be a contract rule.

**Decided** (design: `design/DESIGN-v3-narg-rom.md`, decisions V3-1..V3-11):

- The submitted object is the non-interactive argument itself: verifier `V` and honest prover `P`
  as Lean query programs over bytes, oracle instantiated with Blake2s; the extractor as a RISC-V
  image with a budget (Q1 stands). No organiser compiler.
- Knowledge soundness is proved in the ROM in a local query-by-query counting form (Mathlib only);
  completeness is proved in Lean for `P` (perfect over every oracle function; a counted-error form
  for grinding). The agent's native prover (Rust or anything) is executed and measured, never
  proved equivalent to `P`.
- One relation over 32-byte digests: leaf = Blake2s chain end with its length, node = digest of two
  child digests; witness = chain start, or two child proofs the submitted verifier accepts. The
  verifier's circuit and execution trace are the agent's internal matter.
- **Field-agnostic**: no field in the trusted base (removes v2's `Field`, `Shapes`, `Layout`,
  `Protocol`, `Compile`, `Recursion`: 404 of 726 lines). Binary fields are protected by the
  reference machine (carry-less multiply, no GPU), not by a rule. Organiser library code uses
  CompPoly's `BF64`/`Ext3` (pin 572f997, byte-identical to main on 2026-10-19).
- Score: whole-tree wall time at depth 8, chain length 2^14, fresh random starts (board T,
  ranked); the root step reported (column R). Succinctness is a measured admission cap on the root
  check (`T_V` = 2 s, calibrated so the witness-sending baseline exceeds it 5×).
- ROM-only assumptions; Blake2s-only at launch with a declared menu extension; no ArkLib fork for
  BCS now (library theorem later, O-19); trusted definitions stay local, ArkLib's probabilistic ROM
  notion is the untrusted bridge target.

**Why not ArkLib's definitions directly.** They are sorry-free at the pin; the reasons are audit
surface (a 33k-line definitional closure through VCVio's probability monad) and churn (two
rewrites of the probability layer within a month). Why the `Interaction` framework came up: the
proved ROM theorems (state restoration, Merkle transfer, Fiat–Shamir, in open PRs #1267–#1283) are
native, the proof systems are legacy `OracleReduction`; upstream bridges the two.

**Proposed report changes.** §6–§12 rewritten for v3 (O-8); Appendix A regenerated from the v3
contract once Stage S1 exists.
