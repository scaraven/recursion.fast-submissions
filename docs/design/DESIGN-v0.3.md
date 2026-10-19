<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `design/DESIGN.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# recursion.fast: consolidated design (v0.3, orchestrator)

Date 2026-10-10. Supersedes v0.1 (prime field). Inputs: `design/D1-security.md`, `design/D2-cost-incentives.md`,
`design/D3-binary-fields.md`, reviews `reviews/A1-incentives.md`, `A2-definitions.md`, `A3-feasibility.md`, notes
`R1–R8`, user inputs U1/U2 (`PLAN.md` §5). This file is the **specification in force**; the D-documents hold rationale
and the reviews hold the attacks each rule answers. Items are tagged with their origin (e.g. `[A2-C1]`). Orchestrator
decisions where sources diverge are marked **[O]**.

---

## 1. Objective

- Primary score: cost of one recursion step, i.e. a **proved bound on the RV64IM+Zbc cost vector of every accepting run**
  of the submitted verifier image, at three size classes, plus a Fiat–Shamir surcharge and a proof-byte charge
  [D2-1, U2, D3-7].
- The brief's "performance ÷ program size" is dropped (dimensionally inverted; rewards obfuscation): hard 1 MiB cap
  instead [D2-3]. "Median over hash-chain runs" is replaced by a uniform cost theorem; measurements are unscored
  demonstrations and a differential test [D2-8].

## 2. Relation and fields [U1, D3-1, R8]

- **K = GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)**, restated in the contract as `structure K where bits : BitVec 64`
  with xor addition and carry-less multiplication + reduction (≈25 lines, Lean core only); encoding 8 bytes little-endian
  (bit i = coefficient of x^i), every word is an element [R8].
- **E = K[y]/(y^3 + y + 1) = GF(2^192)**, three K-limbs, 24-byte encoding; **in the contract** (it is the challenge type of
  the fixed menu, §3) [O, overriding R8's "E outside the contract", because A2-C2 requires contract-fixed challenge shapes].
- Field instances, cardinalities, irreducibility (CompPoly's kernel-checked Rabin certificate for the degree-64 modulus;
  order argument for y^3+y+1) and `rfl`-bridges to CompPoly `BF64`/`BF64.Ext3` live in the untrusted organiser library;
  the sanity theorem `K_spec` (irreducible modulus + ring isomorphism to Mathlib's `AdjoinRoot`) may be promoted into the
  contract's controls [R8]. Comparator replay of the certificate: 101 s, passes unpatched [R8].
- **Relation**: R1CS over K with `z = (1, x, w)`; `R1CS i x w :⇔ (A z) ∘ (B z) = C z` [D1 §1.3].
- **Classes (fixed shape)** [O, adopting A3-S3 with A1-M2]: for `k ∈ {16, 20, 24}` the class shape is
  `m = 2^k` rows, `cols = 2^k` (so `nw = 2^k − 1 − nx`), `nx = 2^10`, and indices with `|supp A| + |supp B| + |supp C| ≤
  2^(k+4)`. Smaller R1CS are padded by the harness with a contract-proved, satisfiability-preserving `pad`
  (zero rows, zero witness columns, zero public inputs); certificates are required only at the three class shapes.
  `N_k := 2^k`.

## 3. Protocol model and round shapes [D1.1, A1-C1, A2-C1/C2/C3, D3 §1.6]

- Holographic public-coin IOP in the information-theoretic model. The protocol per class is a list of **contract-fixed
  round shapes**:
  - `msg len` — prover sends a **raw vector `Fin len → K`** (no submitter types, no serializer) [A1-C1, A2-C1];
  - `chal nE idx` — verifier sends `nE` elements of E and a list of indices `Fin 2^b` (b ≤ 64) [A2-C2, A1-M1];
  no K-valued challenges (a K challenge has error ≥ 2^-64 and cannot meet the cap) [D3 §1.6].
- `rounds ≤ roundCap = 2^14` in every protocol and reduction [A2-C3, A1-M6].
- Indexer: **computable** Lean functions `VK : Index → (Fin vkLen → K)`, `vkLen ≤ 2^10`, and `IDX : Index →
  (Fin idxLen → K)` (oracle 0) [D1 §1.2, A2-M4]. Honest prover: computable Lean `Strategy`. Extractor: named, computable.
  "Computable" = passes the computability gate (no `noncomputable`, `implemented_by`, `extern`, `csimp` in the closure).

## 4. Machine and the verifier–spec link [D1.2, D2 §2, D3 §2, A3-C1/C2/M1]

- One contract-owned machine (the only one; `baseline.S` and the probes are rewritten for it) [A3-C1]:
  RV64IM (all W-ops, contract decoder over raw 32-bit words) **+ Zbc** (`clmul`, `clmulh`, `clmulr`) [D3-4]; Harvard code
  space; flat data memory `2^36` bytes, sparse in the emulator [A3-M1]; natural alignment; faults reject.
- Syscalls (`t0`): `0 HALT` (a0 ∈ {0,1}; other values trap); `1 QUERY` (a0 = oracle j, a1 = leaf index, a2 = destination;
  writes leaf `a1` of oracle j, `leaf_j` K-elements, to memory; out of range traps) [D2 §2.4]; `2 HASH` reserved (ROM track).
- Tape (read-only region): class `k` ‖ `VK i` ‖ `x` ‖ challenges (canonical encodings, round order). Oracles: `IDX i`
  (j = 0) and prover messages (j ≥ 1), only via QUERY.
- **Fuel semantics** [O, adopting A3 §6.1]: `execute` runs at most `F = 2^36` cycles; **fuel exhaustion = reject**. There is
  no separate termination theorem: `Agrees` forces every spec-accepted (in particular every honest) transcript to be
  accepted within fuel. The deployed verifier semantics includes the fuel cap.
- **`Agrees`** [D1 §1.4, A2-C1, A3-C2]: for every class `k`, every index `i` of class shape, every `x`, every **raw** oracle
  content for each `msg` round and every challenge vector, the machine's decision on the tape
  `(k, VK i, x, ρ)` with oracles `(IDX i, messages)` equals the spec verifier's decision. Preprocessing (`VK i`, `IDX i`) is
  honest; everything the prover or the environment controls is universally quantified.
- No cost is transferred from the spec; all costs are read off the machine.

## 5. Security definitions [D1 §2, A2]

- **Perfect completeness** for all challenge vectors [D1 §2.2].
- **Round-by-round knowledge soundness**, one variant: worst-case per prefix, per-round backward extractor, named extractor,
  counting form `#bad_i(s, tr) ≤ ε_i · |C_i|` [D1 §2.3]; restated locally over Mathlib only, ArkLib only in `Bridge/` [A2-m2].
- **Error cap** `∀ i, ε_i ≤ 2^-128` [O, v0.1 O2]; **round cap** `≤ 2^14` [A2-C3].
- **Honest labelling** [A2-M1/M2]: with unbounded (computable) extractors, the L1 certificate is *equivalent to RBR
  soundness* (`SF.rbrKS_of_rbr`, Lean theorem, shipped in the library). L1 records are labelled "RBR-sound (knowledge with
  unbounded extraction)". The **L2 efficient-extraction track** (RISC-V extractor image with a proved polynomial cycle
  bound) is the prerequisite for "knowledge-sound / recursion-ready" labels [D1 §2.5].
- **Compiled headline** [A2-M1/m1, W1]: soundness by CY Thm 31.2.1 + 32.8.9; knowledge by WARP (ePrint 2025/753) Thm B.4 +
  CY Thm 32.8.10 with extraction time unbounded at L1. Bound
  `κ(t) ≤ (t + k)·2^-128 + 4.5·max(t, t*)²/2^256 ≤ t/2^127` for `2k ≤ t ≤ 2^124` (k = rounds; the quadratic term needs 9t ≤ 2^128), with the side condition
  `t ≥ t*` behind the quadratic term; stated with these conditions everywhere. Holographic term included.
- **FS hygiene** (harness rule) [D1 §3.1, A2-m5]: the transcript is initialised with
  `H(domSep ‖ contractId ‖ shapeHash ‖ claimHash ‖ k ‖ MTroot(IDX i) ‖ VK i ‖ x)` before any challenge. Challenge sampling is
  bias-free: any 24 hash bytes are an E element, any 8 a K element; index challenges by masking `b` bits [D3 §1.1].
- **Proximity hypotheses** [D1 §3.3, D3 §1.4]: unconditional track (kernel-proven only; today UD) and a conditional track
  whose first named hypothesis is leanerVM's `McaJohnson` transcription (BCHKS25 Thm 4.6) with regime guard
  `γ ≤ 1 − √ρ − η, η > 0`; capacity conjectures banned.
- Out of scope: zero knowledge; quantum adversaries for the compiled system (the IT part is unaffected).

## 6. Recursion: accumulation track (T2) [D1 §4, A2-M3]

- Three reductions `embed : R1CS → R_acc`, `fold : R_acc × R_acc → R_acc`, `decide : R_acc → ⊤`, each with completeness,
  RBR-KS, the error and round caps, and the same round shapes.
- **Accumulator shape fixed per class** [A2-M3]: `plain ≤ accCap = 2^12` K-elements on the tape, plus `r ≤ 16` accumulator
  oracles of declared lengths reachable only by QUERY; `embed` uses the base track's holographic interface (VK/IDX);
  `fold`'s output oracles are a declared **selection** of input-accumulator oracles and fold messages; `Agrees` includes
  equality of the output plain part.
- Baselines: `fullRecAcc` (embed = whole verifier, fold = decide = accept-all over `R_acc = univ`), which scores exactly
  the T1 cost and is what T2 must beat [A2-M3]; `trivialFold` as an illustration only.
- Tree composition theorem: organiser obligation (frame rule), L2. Recursive-SNARK soundness after hash instantiation is
  the named deployment assumption `RecursionHeuristic`; depth declared and enforced [D1 §4.4].

## 7. Cost function and caps (MVP) [D3-6, A1, A3]

```
CostVec = (n_alu, n_mul, n_clmul, n_load, n_store, n_ctrl, n_sys, q_count, q_levels, q_bytes)
w_v0.2  = (1, 4, 4, 1, 1, 1, 1, 0, P_H + 35 = 43, 1/8)          (re-weighting needs no re-proof)
AcceptingCostAtMost k c : ∀ i (class shape k), ∀ x, ∀ raw messages, ∀ challenges,
                            execute … = some (true, v) → v ≤ c (componentwise)      [U2; honest VK/IDX, A3-C2]
C_k  = w · c_k
B_k  = tapeBytes_k + q_bytes_k + 32·q_levels_k + 32·(#msg rounds)
FS_k = 46·rounds + 12·(#E challenge elements) + 4·(#index challenges)
V_k  = Σ_{j≥1} ℓ_j / (N_k + 2^(k+4))                     (declared message lengths; IDX excluded)
S_k  = (C_k + FS_k + ⌈B_k/8⌉) · max(1, V_k/16)^{1/4}
Score_T1 = (S_16 · S_20 · S_24)^{1/3}                    lower is better
Score_T2 = geomean_k (S_leaf,k + S_fold,k + S_dec,k/64),  C_dec,k ≤ 2^32
admission: code+data ≤ 2^20 B; tape ≤ 2^20 B; vkLen ≤ 2^10; ℓ_j ≤ 2^(k+10); leaf_j | ℓ_j (powers of 2);
           V_k ≤ 2^8; Q_k ≤ 2^16; rounds ≤ 2^14; fuel F = 2^36
```

- QUERY price `depth_j·(P_H + 35) + ⌈leafbytes_j/8⌉`, `P_H = 8` [D2 §2.4]; Zbc weight 4 recorded separately [D3-4].
- Optional displayed (unscored) all-runs bound as a DoS badge; required for T2 deciders from v0.3 [D3 §4.4].

## 8. Record eligibility (badge path) [A1-M3, A2-M4, D2 §2.6]

- The harness evaluates the **compiled Lean indexer** on the hidden benchmark indices and requires the native indexer's
  output to match; runs the native prover against harness-sampled challenges; on instances up to 2^16 compares the native
  prover's transcript with the compiled Lean prover's; runs the trusted emulator on accepting transcripts and checks
  `measured ≤ claimed`; prover RAM and wall-clock budgets (2^20: 1 h; 2^24: 8 h). Unscored; gates records only.

## 9. Benchmark [D3-8]

BLAKE2s and SHA-256 compression as Boolean R1CS over K with explicit XOR wires (40,992 / 59,704 rows, ≈5 nnz/row), chains
of length 1/24/399 (BLAKE2s) and 1/16/268 (SHA-256) at the three classes; random sparse satisfiable R1CS over K with hidden
seeds. Rule: no provably always-satisfiable benchmark index [D1 §2.5].

## 10. Baseline [D3-9, A3 §3]

Trivial "proof = z" verifier over K: ≈102 instructions, `C = 20·nnz + 134·N + 7·nx`, Score_T1 ≈ 5.06×10^8 [D3, to be
re-measured on the v0.2 machine]. Lean: 1.5–2.8k lines with organiser library L0–L1, 2.7–4.5k without; check ≈ 8 min warm,
20–25 min cold [A3 §3].

## 11. Tracks, levels, budgets [D1 §1.1, D2 §6, A3-M4/M5/S6]

- Security levels L0–L4 (D1), score tracks T0–T3 (D2). **T0 season first** [A3-S6]: Lean-only, verifier as a contract
  query program `QProg` (≈40 lines; free monad over QUERY with pure local computation), scored by virtual query cost +
  bytes; `QProg` is also the midpoint of the T1 refinement [A3-M5]. T1 opens when library L0–L2 ship.
- Budgets stated in CPU-hours, kernel replay time and peak memory, not lines [A3-M4]: T1/T2 3 h wall, 8 CPUs, 48 GiB; T0
  30 min.

## 12. Organiser library (untrusted, kernel-checked, importable) [A3 §4]

L0 machine facts (1.5–2.5k), L1 symbolic executor + accepting-run cost judgement (3–5k), L2 verified field routines for
K/E (2–4k), L3 IOP components on the local definitions incl. append and frame rule (3–7k), **L4 knowledge-sound hash-based
PCS over binary RS codes (15–40k; interim tensor-code PCS 5–10k) — the critical path**, L5 reference succinct submission
(10–20k), L6 harness (4.5–6.5k).

## 13. Toolchain pin [O, A3-M6, R8, P1]

Lean **v4.34.1**, Mathlib v4.34.1, ArkLib `7653a90`, CompPoly `572f997`, VCVio `a4232d0` (leanerVM's set, so that leanerVM's
binary-field components are importable); riscv-zkvm `Rv64/*` vendored byte-identically from `6810fc1` with a check script
(P1). The contract itself imports Lean core + Mathlib only; ArkLib and CompPoly appear only in `Bridge/` and the library.

## 14. Open items

| # | Item | State |
|---|---|---|
| O8 | Contract implementation of v0.2 in Lean, with controls (A2 counterexamples must fail) | P2 |
| O9 | Baseline end-to-end on the v0.2 machine (image, spec, proofs, timing) | P3 |
| O10 | `QProg` definition and T0 scoring | P2 |
| O11 | Re-review of v0.2 + contract (round 2) | A4 |
| O12 | Constants (FS surcharge, V threshold 16 and exponent 1/4 — tuned on prime-field SPARK, binary model shows rate 1/16 only ties rate 1/4 —, `/64`, P_H, +35) | judgements, revisit with real designs (W3 objection 4) |
| O13 | `pad` must preserve AND reflect satisfiability (`R1CS (pad i) (pad x) w' ↔ ∃ w, R1CS i x w`, with witness maps both ways) so soundness transfers to the unpadded instance | spec fix (W3 objection 1); P2 |
| O14 | Tree composition: total rounds `N·k_e + (N−1)·k_f + k_d` exceed `roundCap`; the compiled bound for a tree uses the tree's round count (side condition `2k_tree ≤ t`); per-node challenges must be independent (A2-m4) | spec text for the tree theorem (W3 objections 2–3) |

---

## 15. v0.3 amendments (supersede the corresponding v0.2 text) [U3, D4, A4]

### 15.1 Cost model v0.3 (replaces §7's uniform weights) [U3, D4 §4]
- **Proved object**: an 18-counter vector over accepting runs (honest VK/IDX), `CostVec = (n_add, n_logic, n_shift,
  n_mul, n_div, n_clmul, n_ld, n_ldsub, n_st, n_stsub, n_br, n_jmp, n_sys, m_words, m_pages, q_count, q_levels,
  q_bytes)`; `m_words`/`m_pages` count first-touched doublewords / 1 KiB pages (code and data) [D4 §2a].
- **Recursion board (primary, M-zk)**: `Score_zk = (Π_P Π_k S_P,k)^{1/12}` over profiles P ∈ {ZisK, SP1-Hypercube,
  RISC Zero, Jolt} with weights, `P_H,P`, `λ_P` from D4 §2a; `S_P,k = (w_P·c_k + (P_H,P+35)·q_levels + P_H,P·(q_bytes/64 + q_count) +
  FS_P,k + ⌈λ_P·B_k⌉)·max(1, V_k/16)^{1/4}`; profiles refreshed per season, re-scoring without re-proof; v0.2 weights
  displayed only [D4 §4.2].
- **Latency board (secondary, M-cpu), scored from season 1 as a separate leaderboard** [O, advancing D4's v0.4 item
  because the user asked for parallelism]: deterministic in-order scoreboard timing model in Lean (per-kind latencies,
  dual issue, taken-branch penalty; compositional bound `time(a++b) ≤ time a + time b + Lmax` shipped in the library)
  and **fork-join harts** (`SPAWN`/`JOIN` syscalls, child runs at spawn in the sequentialised semantics, static
  disjoint read/write regions declared at spawn, violation = fault = reject), with work `W_pipe` and span `S` folds;
  `T_16,k = W_pipe,k/16 + S_k` (Brent), `Score_lat = geomean_k T_16,k`; optional clause `AcceptingLatencyAtMost`.
- **Wall time**: measured on a reference RISC-V board with Zbc (SpacemiT K1 class) for calibration and display only
  [D4 §2c]. No SIMD/RVV in v0.3.
- What remains unrealistic: no cache/DRAM locality model (first-touch only), ILP beyond dual issue invisible, one
  latency table, clmul native in all zkVM profiles (true only for ZisK), two hash prices guessed [D4 §4.5].

### 15.2 Contract fixes from round-2 review [A4]
- **F1** accumulator oracles are typed by the declared accumulator shape (lengths fixed per class), so the machine-visible
  length equals the charged length; T2 cost clauses range over well-shaped inputs only.
- **F2** the challenge renders the image bytes (code/data literals) and every shape-derived score input from files read by
  the harness; the solver proves `submission = rendered` facts; the claimed per-profile scores are rendered and proved.
- **F3** the hygiene gate inspects the elaborated environment (attributes `implemented_by`/`extern`/`csimp`, `unsafe`,
  `partial`, `opaque` with bad bodies, `sorryAx`, `Lean.ofReduceBool`, debug options) over the full dependency closure of
  the certificate, not source text; the axiom audit runs on the certificate theorem itself.
- **F4** Lean functions `scoreZk4`, `scoreLat4`, T0/T2 scores of the certified data; the scorer only takes roots.
- **F5–F7** strict claim schema; FS surcharge prices absorbing `VK ‖ x` (`⌈(vkLen + nx)·8/64⌉·P_H` per class); CI with the
  real sandbox and two kernels (comparator + nanoda or lean4checker) and an isolated `packagesDir`.

### 15.3 Changes from the cryptography review of the report [A5]
- **idxLen cap**: admission `idxLen ≤ 2^(k+8)` K-elements; the compiled bound's side condition uses the *total* oracle
  length `ℓ = ℓ_0 + Σ_j ℓ_j` (CY Thm 32.8.9), so `t* := max(2ℓ_0, 2(log ℓ + 1)ℓ) < 2^43` at the top class [A5-M4].
- **Decider cap removed** (supersedes §7 `C_dec,k ≤ 2^32`): deciders are bounded only by the fuel; linear (Arc/WARP-style)
  deciders are admissible and enter T2 with weight 1/64 [A5-M8, O].
- **Citations**: soundness CY 31.2.1 + 32.8.9; knowledge WARP Thm B.4 (Constr. B.5) + CY 32.8.10 (straight-line clause);
  NI accumulation WARP Thm 10.3; WARP Defs 4.1–4.2 (informally 2.6–2.7) [A5-M3, M9].
- **FS hygiene scope**: the prefix rule answers weak-FS (BPW12) and Fenzi's generated-statement attack; KRS25 (strong FS,
  hash computable in the circuit) is NOT answered by binding and is part of `RecursionHeuristic` [A5-M1].
- **Field rationale**: GF(2^192) is the *simpler* choice (one challenge per check); in-round repetition over GF(2^128)
  could also meet the cap at similar field cost but doubles prover work/answers [A5-M2].
- **Conditional hypotheses**: `McaJohnson` (BCHKS25 Thm 4.6, preprint, MCA proof sketched for the separable case) is
  admitted only as a flagged organiser exception; BCGM25 (CCC 2026, refereed) is the refereed alternative; the stub must
  type the code over E with `Fintype.card E` [A5-M7].
- **Johnson query counts**: 276 / 268 / 262 at η = 0.0177 / 0.011 / 0.0055 (ρ = 1/2) [A5-M5].

### 15.4 Round-3 review fixes and known gaps for v0.4 [A6]
- **Leaf hash (A6-P1, in force)**: a QUERY's leaf is priced at the profile's own `P_H,P` per 64-byte block, as the
  upper bound `P_H,P·(q_bytes/64 + q_count) ≥ P_H,P·Σ_i ⌈b_i/64⌉` computed from the existing counters (one compression
  of slack per QUERY); v0.2's `q_bytes/8` (= `P_H = 8`) is gone. Moving the VK into the index oracle no longer undercuts
  F6, and the score-optimal leaf size equals the exactly-priced one (`contract-v03/probes/a6/Pricing.lean`).
- **Harness order (A6-G0, in force)**: comparator first, in a fresh tree in which no solution code has run, with the
  organiser package (contract, vendored Rv64, library), toolchain and packages outside the tree's writable `.lake` and
  read-only to the sandbox; `.olean` sha256 manifest of the organiser build checked before and after every stage that
  runs solution code; gate (then badge, as its own process) in a second fresh tree. (`contract-v03/scripts/harness.sh`.)
- **Gate (A6-G1/G2, in force)**: trust by content hash only; untrusted modules may not register `init`/`builtin_init`,
  `export`, `extern`, `implemented_by` or `csimp` entries. F3's "debug options" are not visible in an `.olean`: they are
  caught only by the kernel replays (A6-N1).
- **Renderer (A6-R1, in force)**: claim image paths confined to the claim's directory (no absolute path, `..`, symlink).
- **Known gaps, v0.4** (documented, not changed in v0.3 because the baseline's machine proofs are being migrated):
  - *SPAWN/JOIN on M-zk (A6-H1)*: they count one `sys` each (weight 1), but a zkVM has no harts; the deployed image
    needs a context switch (≈ 31 saves + 31 restores). Proposal: a counter `n_spawn` priced per profile at a context
    switch, `64·(w_ld + w_st)/2` (ZisK ≈ 38, SP1 ≈ 67, RISC Zero 64, Jolt 64); interim alternative without a new
    counter: `sys` weight 32 in every profile (a SPAWN+JOIN pair then costs 64; HALT's extra 31 per run is negligible).
  - *Fuel rule for deployment (A6-F1)*: fuel exhaustion rejects, and a child hart runs with the parent's remaining fuel
    while the parent's fuel is not reduced by the child's steps (per-hart, inherited budget; a run may execute up to
    `(#spawns + 1)·2^36` steps). A deployed verifier must replicate this rule exactly, or a "loop past the fuel, then
    accept" backdoor accepts there and rejects in the model. Proposal: either a certificate clause `NoTimeout` (every
    input halts or faults before the fuel) or one global step budget for all harts, stated in the challenge text.
  - *Timer realism (A6-T1)*: two load/store slots per cycle, a fully pipelined 16-cycle divider and no WAW stall;
    memory-bound loops look ≈ 2× faster than on a one-port in-order core. Proposal: one memory port and an unpipelined
    divider (≈ 6 trusted lines in `Timer.lean`), or calibrate on the reference board (D4 §6.2).
  - *Leaf hash on the latency board (A6-P1, second half)*: the QUERY bubble lives in the machine's timer
    (`Machine.lean`, `QUERY_LEVEL_CYCLES·levels + 2^logLeaf`), so the leaf is charged `2^logLeaf` cycles instead of
    `QUERY_LEVEL_CYCLES·⌈2^logLeaf/8⌉`; `scoreLat3` sees only `(W, S)`. Fix in v0.4 in the timer.
