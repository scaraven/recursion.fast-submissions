<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A1-incentives.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A1: adversarial review of incentives, gaming and anti-overfitting

Reviewer: A1. Date 2026-10-10. Scope: `design/DESIGN.md` v0.1 (decisions in force), `design/D2-cost-incentives.md`,
`design/D1-security.md` §1, §2.1–2.5, §4, §5, `PLAN.md` §1, `notes/R7-literature.md` §2, §5.

Method: I read every rule literally, as an optimiser would, and tested constants with the D2 trajectory model and the D2
cycle emulator. New probes are in `probes/a1-probes/`. To reproduce, run `python3 a1_rate.py`, `a1_sweep.py` and
`a1_blowup.py` (outputs in `out_*.txt`). Build `bb5.c` with the d2-probes guest flags (`-I../d2-probes/guest`,
`link.ld`, `start.S`) and run `cyclemu bb5.elf`.

Two new measurements anchor the findings below (RV64IM, sig.golf weights, gcc -O2):

| Kernel | Cycles | Note |
|---|---:|---|
| BabyBear^5 binomial multiplication (`x^5 − W`), lazy u64 accumulation, `remu` reductions | **226** | 25 MUL + 12 REMU + 73 ALU. D2 uses 732 (KoalaBear^5 non-binomial, `extdeg.c`): the D2 tables are ≈3.2× pessimistic on the dominant term. |
| Extension × base multiply-accumulate (inner product `Σ e_i·x_i`, reduce every 4 terms) | **42** per element | This is the cost of ingesting one public-input element into a random evaluation. |

All "S2" numbers below are the D2 model (Spartan + WHIR-JB, ρ = 1/16, fold 2^4) re-run with 226 cycles per extension
multiplication. On that basis S2 scores 3.53M with no public-input term and 6.41M with it.

---

## Findings, ranked

### C1 (critical): submitter-chosen prover-message types give free proximity ("typed promise" attack)

**Attack.** D1 §2.1 lets message types be "submitter-chosen Lean types with a serializer `ser j : Message j → Fin
(msgLen j) → F`". RBR-KS (`KSF.next`, `Bad`) quantifies only over values of `Message j`, and `Agrees` (D1 §1.4)
quantifies only over typed `FullTranscript`s. A submitter therefore declares

`Message j := {p : Polynomial F // p.natDegree < 2^k}` with `ser j p := evaluations of p on a domain D`.

This is exactly how ArkLib models polynomial IOPs, so agents porting ArkLib components will do it without meaning to
cheat. Under this declaration the cheating prover in the theorem can only send low-degree polynomials. The verifier
therefore needs no FRI/WHIR/STIR proximity test at all. An evaluation claim `p(r) = v` is checked by asking for a typed
quotient `q = (p − v)/(X − r)` and testing `p(s) − v = q(s)(s − r)` at `t = 128/log2(1/ρ)` random domain points (32 at
ρ = 1/16). The machine verifier may behave arbitrarily, even accept, on oracle contents outside `ser`'s image. No theorem
constrains it there: only `Terminates` is quantified over raw oracles.

**Numbers (model).** The verifier keeps the Spartan and SPARK sumchecks (≈134 rounds × 4.4k = 0.59M), the eq
evaluations (0.12M), and one batched quotient check (32 queries × 9 oracles × depth 28 × 43 ≈ 0.35M). The total is
≈1.1M against S2's 3.53M (**≈3.3× better**), or 3.9M against 6.4M with the public-input term. Every certificate clause
holds, and the deployed verifier is broken by any prover that sends a non-codeword. D1 rejected submitter-chosen
`OracleInterface` for exactly this reason ("a free PCS"); this is the same hole entered through the message type.

**Fix (contract text, small).**
- Fix `Message j := Fin (msgLen j) → F`, with `ser = id` by definition.
- Quantify `Agrees` over *all* oracle functions `O`, as `Terminates` already is, and over all tapes whose challenge
  segment is a canonical encoding (see M1).

Typed messages may still be used inside a submission's *spec* verifier, through a parsing function `Fin n → F → Option
Message` whose failure means reject; they never restrict the adversary.

**Cost.**
- PIOP-style designs must include their proximity test, which is the intended work.
- The ArkLib bridge must go through a "PIOP + PCS → IOP" step, which is ≈ zero extra trusted text.
- This is shared with A2 (security); I rank it critical here because it is the cheapest route to a top score.

### M1 (major): submitter-chosen challenge types and serializer let the harness do verifier work; FS sampling is unpriced

**Attack.** D1 §2.1 makes challenge types arbitrary `[Fintype] [Nonempty]` types with a submitter serializer `serC`, and
the tape carries `serC j ρ_j`. Any function of one round's randomness is therefore computed for free by the trusted
harness:
- `ρ ↦ (r, L_0(r), …, L_d(r))`: barycentric weights for a sumcheck round;
- `(r, r^2, r^4, …, r^(2^24))`: OOD and vanishing-polynomial powers;
- `(q, ω^q, ω^(2q), …)`: domain points of query positions;
- `(γ, γ^2, …, γ^t)`: combination randomness;
- `(r, r^-1)`: free extension inversions;
- `eq(α, ·)` tables for folding.

In a deployed NARG the verifier must compute all of these itself from hash output.

**Numbers.**
- In S2, sumcheck rounds drop from 10 extension multiplications plus 4 extension × base operations to a 4-term dot
  product (−60% of 0.81M). ω-powers, OOD powers and γ-powers add ≈0.2M more. Together that is ≈0.5–0.7M, about
  **10–15% of S2**.
- The channel is bounded by the tape cap. At 2^20 B it holds ≈52k free extension values. Under D2-7's alternative
  "tape ≤ 2^(k+4) B" (256 MiB at k = 24) the channel would be unbounded in practice; see m10.
- The plain FS cost gap is small but real. A compiled verifier pays ≈46 cycles per round (absorb a root, squeeze) and
  ≈85 cycles per extension challenge (≥ 128 hash bits per base element under D1 §3.1, plus five 128-bit reductions mod
  p). The IOP model charges ≈3 cycles (λ plus loads). For S2 the gap is ≈28k cycles (<1%). A protocol built on many
  independent challenges (up to 52k) could gain ≤4.3M.
- **Trust boundary:** sampling and serialising a submitter type in demonstration runs requires executing candidate Lean
  code in the harness, which contradicts D2-4 ("no candidate code is executed on the trust path").

**Fix.**
- Define a contract-fixed challenge menu: `Chal j := (Fin d_j → F)^{n_j} × (Fin 2^{b_j})^{q_j}`. These are raw
  coefficient vectors and bounded integers, with canonical little-endian serialisation.
- "OOD" and "non-zero" conditions are handled by absorbing `|D|/|E| ≈ 2^-128` into ε. The verifier computes every
  derived value itself.
- Add a static FS surcharge, computed by the scorer from the declared schedule and rendered into the statement:
  `FS_k = Σ_rounds (2·P_H + 30) + 20·#base challenge elements + #index challenges`. No proof burden.

### M2 (major): `nx ≤ 2^16` in every class creates an unmodelled public-input floor of 27–50% of the score

**Failure.** The cost theorem is worst-case over the class, so every verifier is scored at `nx = 2^16`. Soundness forces
every element of `x` to be read and bound to the witness commitment. The cheapest way I know is a tensor-structured eq
table (2·2^8 extension multiplications) plus 2^16 extension × base MACs: **2^16 × 42 + 512 × 226 ≈ 2.87M cycles**. A
naive eq table costs 2^16 × 226 more, i.e. ≈17.7M. The trajectory model omits this term entirely.

| Design (ext 226) | without x | with x | x share |
|---|---:|---:|---:|
| S1-like, ρ = 1/2 | 7.75M | 10.64M | 27% |
| S2, ρ = 1/16 | 3.53M | 6.41M | 45% |
| ρ = 1/64 | 2.92M | 5.81M | 50% |

The term is identical across architectures. It compresses ranking ratios and makes "ingest 2^16 public inputs fast" the
second-largest lever in the competition, which is uninteresting. It is also unrepresentative: hash-chain benchmarks have
nx ≈ 16, and a recursion circuit's public input is an accumulator (≤ accCap). This is the residual overfitting the
uniform rule creates: overfitting to the *corners of the class box* rather than to circuits.

**Fix.**
- Set `nx ≤ 2^10` in all classes. The x term then becomes ≈45k cycles.
- Define classes by `cols = 1 + nx + nw ≤ 2^k` and `m ≤ 2^k`. Today `z` has length `2^k + 2^16 + 1`, so every
  multilinear design pads to 2^(k+1). At k = 24 this also limits single-codeword RS rate to 1/4 under BabyBear's 2^27
  two-adicity (see m9).

**Cost.** Benchmarks with large public inputs must hash or commit `x` inside the circuit, which is the realistic setting.

### M3 (major): the record-eligibility gate is bypassable through VK/IDX (and challenge) backdoors

**Attack.** `Agrees` constrains the image only on `VK i`, `IDX i` computed by the *spec* indexer. Demonstration runs
use VK/IDX produced by the untrusted native indexer. D2 §2.1's byte-for-byte check against the spec cannot be executed
without running candidate Lean, and is impossible for a noncomputable indexer.

So the following is legal:
1. Add a branch "if `IDX[0] = 0xC0FFEE` then accept".
2. Make the spec indexer always write 0 there.

The certificate is untouched, and the native indexer and prover then pass every demonstration with zero work. The gate
was the only check against noncomputable or infeasible honest provers (D2 vector 10). Example: ρ = 2^-10, which the
64·(N+nnz) cap admits at nnz = 16N, with 2^34 oracle elements (64 GiB) at k = 24. With the gate bypassed such a
submission gets a record. Prover RAM in the gate is also unspecified.

**Fix.**
- In the badge path (not the score path), the harness compiles the submission's Lean indexer and Lean honest prover in
  a sandbox (`#eval`/`lake exe`; acceptable because this path decides a badge, not a theorem).
- It requires the native indexer's VK/IDX to equal the compiled spec's output on every benchmark index. It also
  requires the native prover's transcript to equal the compiled Lean prover's transcript bit for bit on the 2^16
  instances.
- Ban `noncomputable` and `implemented_by` in `Indexer` and `Strategy` definitions, using the same computability gate
  as D1 §2.5's extractor.
- State a prover RAM budget (e.g. 48 GiB) next to the 1 h / 8 h wall-clock budgets.

**Cost.** Candidate code runs in the badge path; sandboxing already exists for the native binary.

### M4 (major): the prover cap is a corner solution, so the constant 64 (and its coupling to nnz) chooses the rate

**Failure.** With no prover term in the score, the score is strictly decreasing in 1/ρ. Outputs of `a1_rate.py`,
`a1_blowup.py`:

| log2(1/ρ) | 1 | 2 | 4 | 6 | 8 | 10 |
|---|---:|---:|---:|---:|---:|---:|
| D2 model (ext 732) | 23.9M | 15.7M | 10.8M | 8.9M | 7.7M | 7.0M |
| ext 226 + x term | 10.6M | 8.0M | 6.4M | 5.8M | 5.4M | 5.2M |

- D2's claim that "rates below 1/16 buy little" is −18% at 1/64 and −36% at 1/1024 in its own model. Every record will
  sit exactly on the cap.
- The cap `Σℓ ≤ 64·(N+nnz)` grows with nnz. At the class corner (nnz = 16N) it is 1088·N. A witness-only oracle may
  therefore run at ρ ≈ 2^-10; only the bypassable gate (M3) stops it.
- The worst case over sz then lands at whatever interior (m, nnz) makes the cap tightest relative to cost. That makes it
  hard to reason about and hard to prove.
- The prover externality is precisely the recursion cost. If every layer uses the same parameters, the cost of a
  recursion step is ∝ (verifier size) × (blow-up), and minimising `C(ρ)/ρ` gives ρ = 1/2. Deployed inner recursion
  layers sit at 1/2–1/8, final layers at 1/16–1/32 (R7 §5.1).

**Fix.**
- Decouple and soften the cap. Define `V_k = Σ_{j≥1} ℓ_j / (2^k + nnz)` at the class-cap sizes, with IDX (j = 0)
  explicitly excluded and N defined (see m10).
- Score `C_k + ⌈B_k/8⌉ + FS_k`, multiplied by `max(1, V_k/16)^{1/4}`. In the model this keeps 1/16 optimal (1/32 loses:
  6.07 × 2^{0.25} = 7.2 > 6.41) and turns rate into a visible slope instead of a wall.
- Keep a hard sanity cap at V_k ≤ 2^8.
- Alternative, if no new constant is wanted: publish a Pareto front (score vs V_k vs proof bytes) and award records per
  V-bucket.

**Cost.** One exponent. It is honest about the fact that *some* constant picks the rate.

### M5 (major): T1's cost structure is the inverse of real recursion; engineering dominates architecture

**Failure.**
- In the T1 model at ext 226, S2 at 2^24 splits as Merkle hashing 0.30M (**5%**), extension-field folding and weight
  evaluation 2.90M, sumcheck 0.81M, eq 0.12M and x ingestion 2.87M.
- In circuit recursion hashing dominates: Plonky2's recursion circuit is ≈75% Merkle/Poseidon (R7 §5.1). In a
  native-field circuit an extension multiplication is ≈1 operation and a Poseidon2 permutation is ≈10–20. RV64IM
  without precompiles prices the hash:field ratio ≈50× differently.
- Within the WHIR family the model shows only mild sensitivity: the best fold factor moves from 3 to 4–5 when `P_H` goes
  from 8 to 1500, and there are no rate or regime flips. The model family is too narrow to show the flips that matter
  (hash-light Ligero/Brakedown versus hash-heavy designs, FRI versus WHIR). The structural bias is clear, though: T1
  rewards minimising field operations and RV64IM assembly.
- The biggest single lever is shared by all designs and is not architecture: a binomial BabyBear^5 multiplication
  instead of D2's measured routine is 3.2× (732 → 226, hand assembly plausibly ≈180). After it comes x ingestion (M2,
  ≈2×). The protocol levers (rate, regime, SPARK replacement) add up to ≈2–3×.

**Fix (in priority order).**
- **(a) Vector cost certificate.** Prove `CostVecAtMost k (n_alu, n_mul, n_mem, n_query_levels, n_query_bytes,
  n_syscall…)` instead of a scalar. Any weight vector then yields a valid upper bound (`Σ w_i·max_i ≥ max Σ w_i·n_i`),
  so organisers can publish leaderboards under several weightings, and settle O3, MUL = 4 and `P_H` later, without
  re-proving or contract churn. The proof burden is the same invariant with a tuple.
- **(b) Field-syscall track T1-F.** Add `FMUL5`/`FADD5`/`FINV5` syscalls on BabyBear^5, priced from a field-native
  zkVM (e.g. 4/1/40). O1 + O2 have now fixed the field and the degree, which removes D2's argument against precompiles
  ("would fix the field menu"). Trusted cost: ≈50 lines (`ZMod p`, polynomial mod `x^5 − W`).
- **(c)** Ship an optimised, kernel-checked BabyBear^5 and x-ingestion library as organiser tooling (next to G5), so
  that the starting line already includes the shared engineering.

### M6 (major): `rounds ≤ 2^10` nearly bans GKR-based memory checking at k = 24, and prices nothing

**Failure.**
- A GKR grand product over nnz = 2^28 leaves has Σ_{i=1}^{27} i ≈ 378 sumcheck rounds. At two ArkLib rounds each, plus
  two per layer, that is ≈812 rounds.
- Spartan's outer and inner sumchecks over 25 variables (because of padding) add 100. The SPARK evaluation sumcheck adds
  56, and WHIR adds ≈100. The total is **≈1,070 > 1,024**.
- This rules out the textbook holographic Spartan (SPARK with GKR or LogUp-GKR, as in OpenVM's SWIRL), which is a
  central architecture.
- The cap does not stand for any cost: compiled FS costs ≈46 cycles per round, i.e. 1,000 rounds ≈ 46k cycles (<1%).

**Fix.** Set rounds ≤ 2^14 (still decidable and small). If per-round cost is wanted, use M1's static FS surcharge.

---

### m1 (minor): λ = 1/8 is dead weight in the succinct regime; D2's "tilt towards small proofs" claim does not hold

Proof bytes are 0.3–0.6% of succinct scores. The λ sweep over {0, 1/64, 1/8, 1/2, 2, 8} changes no ranking among T0,
S1, S2, S2@1/64 and S7 (`out_rate.txt`). S2 (263 KiB) vs S1 (599 KiB) differ by 42k cycles of byte charge. Leaf bytes
are also counted twice: once in `⌈leafbytes/8⌉` and again in λ. **Fix:** keep λ only for monotonicity, document that
the proof-size track (not λ) is what rewards small proofs, and do not tune it further.

### m2 (minor): the 2^16 class no longer serves its stated purpose; the geomean ≈ C_20

D2 justifies 2^16 by a crossover at ≈2^16 measured at 10 nnz/row. The certificate is worst-case at nnz = 16N, where
T0 = 25.2M against S2 = 5.8M (4.3×). The crossover moves to ≈2^13.5, so the "hybrid fallback" early improvement does not
exist. All three classes are succinct and nearly flat (S2: 5.81 / 6.43 / ≈6.9M), so the geomean is about the 2^20
value. A design whose fixed overhead is small but whose cost grows faster in k than another's can win on the geomean
and still be worse at 2^24, where recursion lives. **Fix:** classes {20, 22, 24}, or report C_24 as the headline with
the geomean as a tie-breaker.

### m3 (minor): oracle roots are unpriced, giving free Merkle caps; the model and the contract disagree on pruning

Splitting a 2^25-element oracle over 2^9 consecutive prover rounds cuts the virtual depth by 9 levels per query. At 366
queries that is ≈157k cycles (≈3–4% of S2). It is a legitimate Merkle-cap optimisation, but its real cost (32 B per
root absorbed: ≈4k cycles + 16 KiB) is charged at 0. Separately, `trajectory.py` (`pruned=True`) assumes shared path
prefixes, which the per-QUERY price never grants: the model is optimistic by ≈q·log2 q·43 (0.1–0.2M). **Fix:** B += 32
and C += P_H/2 per declared oracle. Optionally allow a declared cap height `c_j` (depth −c_j, B += 32·2^c_j). Set
`pruned=False` in the model.

### m4 (minor): `accCap = 2^12 + nx` is inconsistent with folding

A folded public input `x1 + r·x2` with an extension challenge has 5·nx base elements, which is above the cap whenever
nx > 2^10. A pair of x's (2·nx) is also above it. The `+nx` only helps designs that carry one x verbatim, which no fold
can produce. **Fix:** `accCap = 2^12`, constant, with x bound at `embed` (the leaf verifier reads x and reduces it to an
evaluation claim). This also follows from M2.

### m5 (minor): T2 `/64` is a ban on linear deciders, not a sensitive weight

- With a succinct decider (≈ S2), `C_dec/64` ≈ 0.1M, 1–3% of the score.
- With a linear (Arc/WARP-style) decider at k = 24, `C_dec ≈ 400·2^24 ≈ 6.7e9`, so `/64` ≈ 1.0e8, which dominates.
  Example: fold 4M, geomean 17.2M (linear) vs 4.1M (succinct) at /64, and 5.7M vs 4.0M at /1024. The ranking does not
  flip in the range 64–1024 unless the succinct design's fold is ≥30% dearer.
- Deciders up to ≈64·C_fold are nearly free; fuel 2^36 bounds them at 1.1e9 after /64.
- Trivial and lazy folds are blocked by the constant-size statement and the same `Racc` at input and output. I checked
  RLC-of-instances with list witnesses: it is unsound because the prover picks the list after `r`.

**Fix:** keep `/64` but document it as "deciders must be succinct at 2^24", add a decider cap
`C_dec,k ≤ 2^32`, and publish C_dec separately.

### m6 (minor): O3 (memory first-touch) is not needed in v1

Free zero-initialised memory buys only empty direct-addressed tables, e.g. query deduplication over a 2^25 index space
instead of sorting ≈366 values, which saves ≈30k cycles. Any non-zero table costs ≥ 1 store per 8 B. Loads and stores
are 4–14% of the measured kernels (bb5: 4 loads per extension multiplication; MAC: 6 loads per 42 cycles), so pricing
memory at 2–3× would shift scores uniformly by ≈10–20%. I expect no rank flips. **Fix:** close O3 as "not in v1". With
M5(a) the memory weight can be changed later at no proof cost.

### m7 (minor): the 1 MiB image cannot buy multiplication through tables

At MUL = 4 a BabyBear multiplication is 8 cycles (`mul`+`remu`). Quarter-squares or limb tables cost ≥ 30 cycles.
Twiddle and domain-point tables save ≤ 5% (≈366 × 650 cycles of exponentiation). A 2^31-entry inverse table does not
fit. The cap holds. Note: `REMU = 4` makes Montgomery and Barrett engineering moot. That is harmless because the field
is fixed.

### m8 (minor): unrolled per-class code

Every size pads to its class cap, so an image may contain three straight-line verifiers (k = 16/20/24) plus dispatch,
saving loop overhead (≈5–10%) within 1 MiB. This is legitimate engineering, but it burns proof-check budget. No action
needed beyond the existing caps.

### m9 (minor): two-adicity interaction

With `z = 2^24 + 2^16 + 1` padded to 2^25, BabyBear's 2^27 limits a single smooth RS codeword to ρ ≥ 1/4 at k = 24.
M4's corner pushes every design to stacking or chunking (as in SWIRL) or to mixed-radix domains (15·2^27). This is
legitimate, but it means the S2 rows of D2 §7.3 are not directly realisable at k = 24. The `cols ≤ 2^k` fix of M2 buys
one bit.

### m10 (minor): ambiguities an optimiser will exploit

- `N` in `64·(N+nnz)` is undefined: m, cols or max(m, nw)?
- It is unclear whether Σℓ includes IDX (j = 0).
- The tape cap is 2^(k+4) B in D2-7 but 2^20 B in D2 §3.3 and DESIGN §6. The larger value multiplies M1's channel by
  2^8.
- `leafbytes` for extension-valued messages is unspecified (oracles are over F, so 5 elements).
- `depth` when `leaf ∤ ℓ` is unspecified.

**Fix:** state each explicitly in the contract text.

---

### n1 (note): the uniform cost theorem does kill circuit and instance hard-coding

A SHA-256 fast path cannot lower a worst case over all R1CS, and VK (2^10) cannot hold anything useful about future x.
The residual overfitting is to the class box (M2) and to the cost model (M5), not to the benchmark. I agree with "all
runs" (O4). I found no interesting design that it penalises. Rejection-sampled challenges are handled by M1's menu.
Variable-length proofs are impossible anyway because oracle lengths are static.

### n2 (note): IDX and indexer precomputation

- Holography makes index oracles honest, so proximity tests on IDX are unnecessary. That is standard, not an exploit.
- The indexer cannot precompute x-dependent answers except for tiny nx. For nx = 1, a satisfiability bitmap over F
  (2^26 elements, which fits `ℓ_0 ≤ 2^(k+10)`) lets the verifier accept with one QUERY and no proof. KS still "holds"
  through a brute-force extractor (D1 §2.5 L1).
- This does not affect the score (worst case over nx), and with nx ≥ 2 the table is 2^62. It shows that L1 "knowledge"
  is nominal; the L2 extractor track is the real fix.

### n3 (note): convergence and keeping the design space open

Under the current rules the leaderboard will converge within weeks to "Spartan + WHIR at the rate cap, JB (conditional
track) or UD (unconditional), hand-written BabyBear^5, fast x ingestion". The two security tracks have different optima:
- UD saturates at ≈128 queries (≥ 0.91 bits per query below ρ = 1/16), so rate barely matters.
- JB rewards rate, which is M4.

Recommendations:
- Keep separate unconditional and conditional leaderboards (already planned) and say why they differ.
- Add per-class boards and the Pareto display of M4.
- Add the T1-F field-syscall board (M5b), where the architecture levers (holography without SPARK, accumulation,
  GKR-based memory checking once M6 is fixed) are not drowned by assembly.
- Note that the reachable design space is bounded more by what ArkLib can prove (UD correlated agreement is sorry-free;
  Johnson CA is not) than by the score. That is A3's concern, but it also shapes incentives.

---

## Verdict

**Design OK with fixes; no redesign needed.**
- **C1** is a one-definition change to the contract, and it is mandatory: without it, the top of the leaderboard is
  PIOP verifiers with no PCS.
- **M1 and M3** close the remaining "free computation" and gate-bypass channels.
- **M2, M4 and M6** are constant and definition changes that remove artefacts of the class box and the rate corner.
- **M5** is the change that makes the score track recursion cost and architecture rather than RV64IM assembly. I
  recommend it strongly, but the competition still functions without it.

## Fixes in priority order

1. **C1:** prover messages are raw `Fin n → F` vectors; `Agrees` holds over all oracle functions.
2. **M1:** contract-fixed challenge menu with canonical serialisation, and a static FS surcharge `FS_k`.
3. **M3:** badge-path recomputation of VK/IDX and of the 2^16 transcript from the compiled Lean indexer and prover; ban
   `noncomputable`/`implemented_by` there; add a prover RAM budget.
4. **M2:** `nx ≤ 2^10`; classes by `cols ≤ 2^k`; then `accCap = 2^12` (m4).
5. **M6:** `rounds ≤ 2^14`.
6. **M4:** decouple the prover cap from nnz, exclude IDX, define N; add the soft blow-up factor
   `max(1, V_k/16)^{1/4}` or a Pareto board.
7. **M5:** vector cost certificate (a), T1-F field-syscall board (b), organiser field and x-ingestion library (c).
8. m3: price oracle roots and allow declared Merkle caps; set `pruned=False` in `trajectory.py`.
9. m2: classes {20, 22, 24}, or C_24 as the headline.
10. m5: document `/64` and add `C_dec,k ≤ 2^32`. m1: freeze λ = 1/8 and do not advertise it as a size incentive.
11. m10: resolve the ambiguities; close O3 as "not in v1" (m6).
12. Rescale D2 §7.3 with 226 cycles per extension multiplication plus the x term, so the report's trajectory is not off
    by 3×.
