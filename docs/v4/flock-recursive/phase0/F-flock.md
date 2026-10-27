# Phase 0 F: Flock digest for the recursive Flock-class entry

Sources (read-only):
- the Flock repository `/home/devops/succintlabs/flock`, public at https://github.com/succinctlabs/flock, head **`48f4bfe`** (2026-10-26, PR #65). The paths below are relative to it.
- the paper, Bünz–Rothblum–Wang, "Flock: Fast Proving for Batch Boolean Computations" (2026-09-19, 45 pp., `/tmp/flock-paper.pdf`). It is cited as §/page.

The measurements are in `logs/phase0-F/` (gitignored). The runner probe is `probe/flock-bench/run.sh` (§6.4).

Every number below is either quoted with its location or measured with its log. Anything else is labelled **estimate** and shows its derivation.

## 0. Summary for the blueprint

- **The protocol at head.** A Spartan-style batch R1CS over GF(2), where every block has the circuit shape `C = I`. It has four parts:
  - zerocheck: a univariate skip of size 2^6 over an AES-subfield domain, with partially fixed "friendly" challenges, then `m − 6` degree-2 multilinear rounds;
  - lincheck: a product sumcheck over the block's `k_log − 6` inner variables plus a 64-entry skip collapse;
  - ring switching to GF(2^128) packing (128 = 2^7 bits per element);
  - Ligerito over GF(2^128) codewords, with fold challenges, sumcheck claims and MCA arithmetic in **GF(2^256)**.

  Fiat–Shamir and Merkle default to **BLAKE3** (the paper says SHA-256). Grinding is per challenge.
- **The `Secure` profile (120-bit, unique decoding)** is the one that matches FR-D3:
  - rate 1/2 at L0, then +1 per level (1/2, 1/4, 1/8, …);
  - per-level query counts ≈ 290 / 178 / 145 / 132 / 127 …;
  - no query PoW and no OOD;
  - MCA over F256 at ≥ 246 bits.

  Every per-round term of the protocol is already ≤ 2^-120 **without grinding** (§1.4). The worst term is the zerocheck skip challenge at 126/2^128 = 2^-121.0. Secure's own grinding (1 to 7 bits per site) exists only to work-normalise to 128 bits. In SROM a grind costs the prover about 2^b oracle queries, so we should drop it (§1.4).
- **Proof size.** Paper Table 4 gives 558 KiB at 120-bit UD for 2^14 Keccak. **Measured Secure at 2^16 BLAKE3 (m = 30): 619.0 KiB** (Fast 406.6, Slim 263.6; §1.5). All are within `proofCap` = 1 MiB.
- **The tower.** Flock's recursion is a linear spine of 2-to-1 nodes. Its node verifies the child **including Merkle and Fiat–Shamir hashing in-circuit (BLAKE3)**. It defers all matrix (lincheck) work to a root discharge through a folded accumulator.
  - Measured by its authors: about 23k BLAKE3 rows per node, against about 39k+ F128 element rows. That is over 99% of the node's AND constraints and about 60% of its committed area (§2.3).
  - In our setting the Merkle/FS rows go away, but **the trace digest replaces them**. A BLAKE2s hash of every oracle query's bytes is of the same order or larger: **estimate** ≈ 20–30k BLAKE2s compressions per child at Secure (§2.4).
  - Measured on this VM (§6.5): a current Chain128 node has 21,819 BLAKE3 rows and a 252.8 KiB proof, proves in 17–20 s on the portable path, and needs **about 106 s of serial per-shape circuit build**. That build must live in `prover setup`.
- **BLAKE2s R1CS.**
  - Flock's BLAKE3 encoder ("Option F", `crates/flock-prover/src/r1cs_hashes/blake3.rs:1-80`) carries over almost entirely: the same G, the same fused carry-save adders, and the same constant-IV saving in round 1.
  - What changes: 10 rounds instead of 7, the SIGMA schedule, the state init and the finalisation.
  - Count: 76·184 + 2·183 + 2·182 = **14,714 AND rows per compression**, against BLAKE3's 10,298. With I/O, 15,867 slots fit the same 2^14 block (§3).
- **CPU.** All of Flock's x86 kernels are selected at **compile time** (`cfg(target_feature)`). There is no `cpuid` dispatch anywhere (§4).
  - Fast path: AVX-512F + VPCLMULQDQ, plus GFNI and AVX-512BW/VBMI.
  - Middle tier: plain PCLMULQDQ is used only for scalar GF(2^128) products.
  - Everything else falls back to a **bit-serial portable path**.
  - On this VM, which has no clmul, the portable path measures **1.4–2.1k BLAKE3 compressions/s on one thread and 2.4–3.9k/s on four** (batches 2^14–2^16). The README's Zen4 AVX-512+VPCLMULQDQ figure is 62.7–64.8k/s on one thread, 31–44× more (§6).
  - **The evaluation runner is Zen 3** (AMD EPYC 7763, 4 vCPU, 16 GB; AVX2, PCLMULQDQ, 256-bit VPCLMULQDQ, SHA-NI; **no AVX-512, no GFNI**; coordinator, GitHub runs 40493471459/40493470932).
  - **Flock has no ymm (AVX2 + VPCLMULQDQ) kernel anywhere.** There is no `_mm256_clmulepi64` and no `__m256i` in the workspace. On that runner Flock runs scalar-PCLMULQDQ F128 products with portable NTT, transpose, shift-reduce and accumulate kernels.
  - **Estimate:** 2.5–3.5× slower than its AVX-512 path at equal clock (§4). That puts the 2^24 tree at **≈ 400–800 s of leaf proving alone**, above `tree_s` = 600 s, unless we write a ymm VPCLMULQDQ tier (§6.3).
  - The probe (`probe/flock-bench/run.sh`, `-C target-cpu=znver3`) measures this tier directly.
- **Prover packaging.** Flock needs these dependencies: rayon, crossbeam, blake3 (whose `build.rs` compiles C/asm through `cc`), sha2 + sha2-asm (C/asm through `cc`), serde, bincode and toml.
  - A single `prover.s` (the `spartan-srom` recipe) needs pure-Rust dependencies only.
  - Concretely: vendor rayon/crossbeam, which are pure Rust, or use `spartan-srom`'s `par.rs` pool; drop or replace blake3/sha2, since every hash goes to the oracle anyway; replace serde/bincode/toml with hand-written formats.
  - The compile-time kernel selection must become `#[target_feature(enable)]` functions behind `cpuid` (§5).
- **Season-shape extrapolation (estimate, §6.3).** On the 4-vCPU Zen 3 runner, unmodified Flock kernels give about 21–42k BLAKE2s compressions/s, or about 400–800 s for the tree. A ymm-VPCLMULQDQ tier is needed. An AVX-512 host would give about 75–120k/s, or about 140–225 s. Those figures cover leaf proving only, before Merkle hashing through the service and the 63 node proofs. A 2^16 stream leaf takes about 1.6–3.1 s unmodified, or 0.6–0.9 s with the fast tier. Merkle hashing through the service is second-order (≈ 22 s per tree, from the measured service rate). Nodes cost about 1.5–4 s each on the fast tier and more without it, so FR-R5 is open. The runner probe (§6.4) replaces these with measurements.

## 1. The protocol as implemented (head `48f4bfe`)

### 1.1 PIOP

**Relation.** A batch R1CS over GF(2): `A = I_{2^n} ⊗ A_0` (same for B and C), with `C_0 = I`. One block of `2^k_log` witness bits is one hash compression (`crates/flock-core/src/lincheck.rs:1-60`).
- Only inputs, outputs and AND (carry) products are committed. XORs are inlined as linear forms, and the sum bits are never materialised (`blake3.rs:28-36`; paper §4.5).
- The verifier refuses `C_0 ≠ I` (`crates/flock-core/src/verifier.rs:1319-1321`).
- At head the R1CS is a **union / mixed-class instance**: a registry of boolean table types (GF(2) blocks) and element types (GF(2^128)-native rows, one F128 per variable; `crates/flock-core/src/element_r1cs.rs:1-60`). A copy-constraint "wiring" argument (product-GKR, `crates/flock-core/src/product_gkr.rs`) and a "jagged" PCS layout (`crates/flock-core/src/pcs/jagged.rs`) link them. The plain hash benchmarks use the boolean class only.

**Order of the verifier** (`crates/flock-core/src/verifier.rs:1308-1395`, `verify_core_inner`):
1. `bind_statement`: absorb the R1CS and the commitment.
2. **Zerocheck** (`crates/flock-core/src/zerocheck.rs:1-15`):
   - Point `r ∈ F128^m`. Some coordinates are pinned "friendly" constants (paper §4.3: 7 pinned, 3 in the AES subfield F_{2^8} and 4 in F128).
   - The prover sends `P^{AB}(λ)` and `P^C(λ)` on Λ, with |Λ| = 2^`K_SKIP` = 64 each (`zerocheck.rs:59-62`). Λ and the skip domain S sit in the F_{2^8} subfield (paper §4.2).
   - Fold point `z ∈ F128`.
   - `m − 6` rounds, each sending `(P(1), P(∞))` with challenge `ρ_r`.
   - Finally the prover sends â, b̂, ĉ.
   - "Skipping c" (paper §4.4): the c claim is a direct ẑ claim because `C = I`.
3. **Lincheck** (`lincheck.rs:541-570`, `LincheckProof`):
   - a `(k_log − k_skip)`-round product sumcheck with messages `(q(1), q(∞))`;
   - a `2^k_skip`-entry `z_partial` folded at a fresh φ8 skip point;
   - the A and B claims are batched by α.
   - On the union path the per-type matrix bilinear forms `matrix_evals` are *reported* and accumulated, not evaluated by the verifier (`lincheck.rs:550-563`).

   Output: one ẑ claim. Together with the c claim, the PCS sees two z-openings (`lincheck.rs:52-53`).
4. **PCS opening** (`crates/flock-core/src/pcs.rs:1-20`):
   - Ring switching: the prover sends 128 `s_hat_v`. The verifier checks the claim with direct φ8-Lagrange weights, because the φ8 basis is not a novelty basis (`pcs/ring_switch.rs:11-60`).
   - Then a sumcheck against the transparent `rs_eq_ind`. The verifier evaluates it in `O((m−7)·128²)` with the DP24 tensor-algebra algorithm (`ring_switch.rs:36-44`). The paper's App. B.4 uses a branching-program evaluation instead.
   - Then Ligerito on the packed `2^(m−7)` F128 words.

**AG zerocheck** (`crates/flock-core/src/zerocheck/ag_skip.rs:1-120`). An alternative round 1 that replaces the RS univariate skip with a **genus-95 algebraic-geometry product code** (`crates/flock-core/src/genus95_curve_code/`):
- 7 geometric friendly challenges `r_j = γ^{2^j}/(1+γ^{2^j})` over the GHASH generator γ (`ag_skip.rs:63-90`).
- The post-round-1 point `r₁` is derived by the prover by **nonce rejection sampling** with a 9-bit PoW (`R1_POW_BITS = 9`, `ag_skip.rs:985`). The verifier makes one attempt.
- Default on aarch64 only: the round-1 kernel is NEON-only, and x86 runs RS (`crates/flock-prover/benches/blake3_proof.rs:114-131`).
- The paper does not describe it.
- **For the Lean verifier we take the RS skip.** The AG path doubles the verifier's surface for about a 6% prover gain (`blake3_proof.rs:122-124`).

### 1.2 PCS: Ligerito (`crates/flock-core/src/pcs/ligerito.rs`, a port of bolt-rs)

**Protocol** (`ligerito.rs:21-31`):
1. Commit f⁰ as `num_interleaved × msg_cols`, RS-encoding each lane at `2^log_inv_rate`.
2. Merkle over codeword positions; one leaf is one position across all lanes, so L0 leaves are 64 lanes × 16 B = 1 KiB.
3. Partial-evaluate with `initial_k` challenges, commit f¹, open `queries` rows of f⁰, and so on.
4. At the end, send the final block in the clear (`final_block.yr_log_n`).

**Fields.**
- Codewords are in F128 (GHASH, x^128 + x^7 + x^2 + x + 1).
- Fold challenges and running claims are in **F256 = F128[u]/(u² + u + x⁻¹)** (`ligerito.rs:9-14`; `crates/flock-field/src/gf2_256.rs:1-11`). This came in at `97cc1d2`, and the loader now rejects `field = "f128"` (`docs/recursion-100-128-variants.md:262-268`).

**Code-rate ladder.** 3 folds per level. The rate climbs +1 per level (Secure, Fast100, Slim100) or +2 per level (strict Fast/Slim) (`ligerito.rs:1764-1774`).

**Soundness accounting is round-by-round: the minimum over rounds, with no union-bound headroom** (`ligerito.rs:1883-1892`). This matches our per-query `errorCap` reading (PLAN item 3).

**Formulas**, each quoting paper App. C.3:

| Term | Secure (UDR) | Johnson profiles |
|---|---|---|
| Radius | γ = δ/2 − 3/(δn), δ = 1 − ρ (`ligerito.rs:1031-1047`) | γ = 1 − √ρ − η, η = 0.02 |
| Per-query bits | log₂ 1/(1−γ) (`ligerito.rs:1052-1055`) | log₂ 1/(1−γ) |
| Queries | ⌊(T − g)/bits⌋ + 1 (`ligerito.rs:925-929`) | same |
| MCA (proximity gap) | a = γn + 1 (Thm 7 = BCHKS25 Cor 1.4); ε_pg = 256 − log₂ a, no row-union factor (`ligerito.rs:1069-1094`) | Thm 8 (BCHKS25 Thm 4.6) + 2^{ℓ−1} row union (`ligerito.rs:969-1029`) |
| OOD | none | 1 sample at L0, 2 at later levels (two-point binding) |
| Algebraic batching | claim batch 128 − log₂ L, consistency batch 128 − log₂ L − log₂⌈log₂ q⌉, sumcheck 256 − (1 + log₂ L) (`ligerito.rs:934-960`) | same, with L the Johnson list size 1/(2η√ρ) |

**Profiles** (`ligerito.rs:79-152`; TOMLs embedded from `crates/flock-core/configs/ligerito/m{22..35}_{fast,fast100,slim,slim100,secure}.toml`, `ligerito.rs:528-538`). `m` counts GF(2) bits, so `log_n = m − 7`. A 2^16-compression BLAKE3/BLAKE2s batch is m = 30, and 2^18 is m = 32.

| Profile | Regime | L0 rate | Ladder | Query PoW | Query target | Use |
|---|---|---|---|---|---|---|
| `Secure` | UDR, no OOD | 1/2 | +1/level | 0 | 120 bits per level | "historical 120-bit" regression target; not a TowerConfig |
| `Fast` (default) | Johnson + 2-pt OOD | 1/2 | +2/level | 16 bits every level | 112 + 16 = 128 work-normalised | strict 128; tower leaves |
| `Slim` | Johnson + 2-pt OOD | 1/4 | +2/level | 16 | 128 | strict 128; tower outers |
| `Fast100` | Johnson + OOD | 1/2 | +1/level | 0 | 100 | frozen historical; = the paper's schedule |
| `Slim100` | Johnson + OOD | 1/4 | +1/level | 16 | 100 | frozen historical |

**Per-level schedules at m = 30 and m = 32**, from the TOMLs. Each level is written `rate:queries[g=query PoW/claim-batch PoW/consistency PoW]`; fold-grinding bits are 0 everywhere.

| Profile, m | Levels | Σq |
|---|---|---|
| Secure m30 | 1/2:290[0/1/4] · 1/4:178 · 1/8:145 · 1/16:132[0/1/4] · 1/32:127[0/1/3]; k0 6, k 4, final yr_log_n 5 | 872 |
| Secure m32 | 1/2:290 · 1/4:177 · 1/8:145 · 1/16:132 · 1/32:126 · 1/64:124; final yr_log_n 4 | 994 |
| Fast m30 | 1/2:244[16/6/9] · 1/8:79[16/7/9] · 1/32:48[16/8/10] · 1/128:35[16/9/11] · 1/512:29[16/10/12] | 435 |
| Fast m32 | as m30 plus 1/2048:25[16/11/13] | 460 |
| Slim m30 | 1/4:119 · 1/16:60 · 1/64:41 · 1/256:32 · 1/1024:27, all [16/…] | 279 |
| Fast100 m29 | 1/2:218 · 1/4:106 · 1/8:71 · 1/16:53 · 1/32:43 | 491 |

The Fast100 m29 row is exactly the paper's §5 schedule ("rates 1/2…1/32 with 218, 106, 71, 53, 43 queries").

- **Secure, per-level diagnostics** (m24 TOML): `expected_eps_pg_bits` 246–249 (F256 MCA), query 120.2–120.4, claim batch 128.0, sumcheck 255.0, consistency batch 124.8–125.0.
- **Fast** declares query 112.2 bits + 16 PoW, pg 217–224, OOD 236–238, claim batch 120.9–122.9 + 6–8 PoW, consistency batch 117.8–119.9 + 9–11 PoW.
- **The strict profiles' TOMLs still say `target_security_bits = 100`.** That field is historical. `validate()` enforces the independent 128-bit floors (`ligerito.rs:133-142`, `:886-902`). Do not read the profile's security off that field.

### 1.3 Fiat–Shamir and grinding

**Transcript** (`crates/flock-transcript/src/challenger.rs:260-360`):
- Tagged absorbs: one-byte op (`OP_DOMAIN`/`LABEL`/`OBSERVE`/`SQUEEZE`/`BYTES`) and one-byte kind.
- A squeeze clones the state and reads an XOF. With SHA-256 this is `SHA256(state‖ctr)`.
- Default hash: `HashKind::Blake3` (`crates/flock-hash/src/lib.rs:13-19`).
- The tower uses `Blake3Chain`, a sequential duplex over the BLAKE3 compression with a counter of 0 and no chunk tree. This makes one in-circuit row per 64 B absorbed (`challenger.rs:346-360`).
- Fused PoW + squeeze: one compression gives both the PoW word and the challenge.
- In our entry all of this is replaced by oracle queries.

**Grinding.** Non-Ligerito grinding is per challenge. It is enabled under Fast, Slim and Secure, and disabled under the `*100` profiles (`crates/flock-core/src/pcs/commit.rs:96-170`).
- Rule: `bits = ⌊log₂ numerator⌋ + 1`, so that `numerator/2^(128+bits) < 2^-128` (`crates/flock-transcript/src/challenger.rs:21-34`; `zerocheck.rs:106-170`).
- Zerocheck: initial point `⌊log₂ m⌋ + 1` bits (6 at m = 32); skip `z` 7 bits (numerator 127); each multilinear round 2 bits.
- Lincheck: α 1 bit, β 1 bit, rounds 2 bits, skip `k_skip` = 6 bits (`lincheck.rs:607-632`).
- Ligerito: query PoW, claim/consistency batch PoW, fold PoW, as in the tables above.
- Audit trail: `docs/128-bit-grinding-audit.md` ("strict Fast/Slim … complete"; `:44-80`).

### 1.4 Per-round errors over GF(2^128) without grinding, against FR-D3's 2^-120

This is my arithmetic from the formulas above, with L = 1 (UDR).

| Round | Error | bits |
|---|---|---|
| zerocheck initial point (degree m) | m/2^128, m ≤ 35 | ≥ 122.9 |
| zerocheck skip `z` (degree 2·63 = 126; paper App. A) | 126/2^128 | **121.0** |
| zerocheck multilinear round (degree 2) | 2/2^128 | 127 |
| lincheck α/β batching, rounds, skip | 1, 2, 63/2^128 | ≥ 122 |
| ring-switch batching (paper fn. 17) | 7/2^128 | 125.2 |
| Ligerito sumcheck rounds, folds (F256) | 2/2^256 | 255 |
| Ligerito MCA (Secure, F256) | a/2^256 | 246–249 |
| Ligerito claim / consistency batch (F128, Secure) | 1/2^128, ⌈log₂ q⌉/2^128 | 128, 124.8 |
| Ligerito query phase (Secure) | (1−γ)^q | 120.2–120.4 |

**Consequence.** With Secure's query counts and F256 folds, every round is ≤ 2^-120 **with zero grinding**.
- Secure's grinding sites (zerocheck/lincheck per-challenge bits, claim batch 1, consistency 3–4) exist only to reach 128 work-normalised bits.
- In SROM a b-bit grind is about 2^b oracle queries on the prover, plus one PoW query in the verifier's trace. It buys nothing against `errorCap`. **Recommendation:** Secure's schedule with every PoW set to 0.
- The skip term at 2^-121.0 leaves one bit of slack. A larger skip (`K_SKIP` 7) would break 2^-120 over F128 unless the skip challenge is drawn in F256.

### 1.5 Proof sizes

| Proof | Size | Source |
|---|---|---|
| Paper Table 4, ≈2^14 Keccak: fast / slim / 120-bit UD | 386 / 200 / 558 KiB; verify 5.8 / 5.3 / 6.1 ms | paper p. 26 |
| m32 BLAKE3, RS, blake3 Merkle + FS (production Fast at the time) | 449.76 KiB, verify 6.59 ms, peak 8.52 GB | `benchmarks/RS_PORT_LOG.md:2914-2915` (2026-08-31) |
| m32 leaf-type proof by level | 462,052 B: L0 285,184 (62%), L1 55,136, … L5 16,224 | `RS_PORT_LOG.md:5406-5409` |
| Secure tower outer (historical mvp11) | 566.7 KiB (`fast100`: 292.0 KiB) | `docs/recursion-100-128-variants.md:96-102` |
| **Measured here, 2^16 BLAKE3 (m = 30), 4 threads** | see table below | `logs/phase0-F/proofsize.log` |

| Profile (m = 30) | Proof | Verify (VM, portable F128) | Peak RSS (bench's own counter) |
|---|---:|---:|---:|
| `Secure` | **633,856 B = 619.0 KiB** | 120.6 ms | 3,375 MB |
| `Fast` | 416,368 B = 406.6 KiB | 78.2 ms | 3,382 MB |
| `Slim` | 269,968 B = 263.6 KiB | 80.3 ms | 3,781 MB |

Commands: `BLAKE3_PROFILE={secure,fast,slim} BLAKE3_LOG2S=16 BLAKE3_RUNS=1 RAYON_NUM_THREADS=4 blake3_proof` (the bench's default merkle/FS hash, BLAKE3), log `logs/phase0-F/proofsize.log`. Proof bytes are CPU-independent; the times are this VM's portable path (§6.1) and not of record. Secure at m = 30 is 61% of `proofCap` (1 MiB); at m = 32 (2^18 leaves) each query path gains about two siblings (≈ Σq·2·32 B ≈ 55 KiB) and a sixth level appears (124 queries) — **estimate** ≈ 0.65–0.75 MiB, still under the cap; measure it with `BLAKE3_LOG2S=18`.

## 2. The recursion tower (`crates/flock-prover/src/tower/`)

This section comes from a code read: `tower/mod.rs`, `driver.rs`, `chain.rs`, `fl_node.rs`, `node.rs`, `envelope.rs`, `config.rs`, `real_walker.rs`, `child_walker.rs`, `query.rs`, `gkr.rs`, `gates_spine.rs`, `docs/folding-verifier-design.tex`, `docs/circuit-wiring-design.tex`, `docs/ag-recursion-plan.md` and `docs/128-bit-grinding-audit.md`.

### 2.1 What a step proves

| Layer | Builder | Children | Statement |
|---|---|---|---|
| Leaf | `chain.rs:430` `build_chain_proof` (relation `chain.rs:263-275`) | — | A chain of `n_blocks` BLAKE3 compressions `h_{i+1} = compress(IV, h_i, …)`. Production is 2^18 (m = 32). 11 statement words; `h_end` is public. |
| First level (FL) | `fl_node.rs:180` | exactly 2 adjacent leaves (`fl_node.rs:177,186`) | Deferred verification of both. Boolean, sigma (wiring) and jagged claims are folded 2→1. Adjacency is a copy constraint. |
| Internal / base | `node.rs:241` `build_node_outer_app` | 2 envelope outers | Deferred verification of both children (`real_walker.rs:1778`). One main fold over 6 boolean + 15 element types plus sigma and jagged, and one "chain lane" fold (`node.rs:185-202`). |
| Spine | same, with `SpineIn` | 1 fresh FL + 1 prior node | The circuit digest is fixed from the second spine fold on (`driver.rs:205-214`). |
| Root | `verify.rs` `verify_root`, `Tower::discharge_root` | — | Native verification plus discharge of the accumulated matrix, sigma and jagged claims against the native tables. |

- **Shape.** A linear spine, not a balanced tree (`driver.rs:124-232`).
- **The key design point is deferral.** The lincheck's matrix bilinear forms are O(nnz), about 21M nnz for BLAKE3, and about 84% of native verify. They are never computed in-circuit: they become claims in a fixed-size accumulator, re-folded at every node, discharged once at the root (`docs/folding-verifier-design.tex:36-52, 80-86`).
- **In our setting there is no root discharge.** `acc` must decide the root proof alone within `T_V`. So either the accumulator's discharge fits `T_V` (one native O(nnz) pass, about 21M nnz for BLAKE3), or the node replays the matrix work in-circuit, which is the nnz-preserving fixed point the authors say cannot close. **The blueprint must decide this.**
- **Envelope.** Every outer has the same shape: `nu = 14`, `mu = 23`, dense floor `m* = 29`, 31 lanes, 511 gate slots, 5,684 public words (`ACC_MAIN` 1,152, `ACC_CHAIN` 160, `PASS` 96, `APP` 10) (`envelope.rs:17-33, 57-70, 164-168, 233-297`).
- **TowerConfig** (`config.rs:34-57`): `Chain128` = leaves `Fast`, outers `Slim`; `Chain100` = `Fast100` / `Slim100`. Secure is not a tower config, but historical Secure node numbers exist (§2.3).

### 2.2 How the inner verifier is arithmetised

**Two table classes in one union R1CS:**
- **Boolean tables (GF(2))**: BLAKE3 (one 2^14 block per compression), `SwapTable`, `BitSpreadTable`, `PowMaskTable` and `FamilyTransposeTileTable`.
- **Element tables (F128-native)**: one F128 per variable, `C = I`.

**Cost of one field multiplication:**
- An F128 multiplication in bit-level R1CS would be about 2,187 constraints. As an element row it costs one (`crates/flock-core/src/element_r1cs.rs:5-6`).
- `MacGate` (`gates_spine.rs:794-836`) computes `acc + x·y` in one row.
- An F256 product is 3 Karatsuba F128 products: `MacGate256`, one row of 11 columns (`gates_spine.rs:838-887`; `128-bit-grinding-audit.md:1046-1048`).

**Verifier algebra in-circuit:**
- Ligerito sumcheck spine (`SpineGate256`) and per-query leaf-eval/residual (`gates_leaf.rs`, kappa 8, 200 columns, one row per query per level).
- Ring-switch "family H": 512 transpose-tile rows plus 8,128 F256 multiplications per child (`docs/circuit-wiring-design.tex:1060-1088`).
- Wiring product-GKR: about 276 rounds per child at μ = 23 (`gkr.rs`, `real_walker.rs:2257-2337`).
- Element zerocheck/lincheck: about 150 rows (`circuit-wiring-design.tex:473`).
- Accumulator folds (`fold_region.rs`).

**Hashing in-circuit:**
- **Fiat–Shamir**: one BLAKE3 row per 64 B absorbed, plus squeezes. A PoW check is one 4-word `PowMaskTable` row (`query.rs:778-838`).
- **H(child publics)** (`real_walker.rs:2050-2059`).
- **Merkle openings**: per query, `⌈row_words/4⌉` leaf compressions (L0 leaf 1 KiB = 16 compressions; deeper leaves 128 B) plus `depth − cap` path compressions. Each path step is BitSpread → Swap → BLAKE3 (`query.rs:41-60, 1133-1146`; `merkle_glue.rs:1-41`).

**Open question to confirm.** The boolean zerocheck's round checks may not be arithmetised in-circuit. The 2026-08-18 survey says "Λ-interpolation, round checks, and the ring-switch `claim_check` are never arithmetized" (`docs/ag-recursion-plan.md:213-221`). Family H and the skip interpolation were added later. No boolean-zerocheck round gate was found at head. Confirm before relying on the tower as a model of a complete verifier.

### 2.3 Sizes and times (as recorded by the authors)

**BLAKE rows per child**, historical, mvp11 (`docs/128-bit-grinding-audit.md:836-857`):

| Component | Fast | Secure |
|---|---:|---:|
| FS chain | 1,707 | 2,438 |
| H(publics) | 216 | 432 |
| Merkle leaves + paths + caps | 9,266 | 15,668 |
| PoW | 15 | 445 |
| **Per child** | **11,204** | **18,983** |
| Node total (2 children + fold region) | 24,637 | 41,215 |
| nu / mu | 15 / 23 | 16 / 24 |
| Outer proof | 291.5 KiB | **589.2 KiB** |
| Node online prove | 232 ms | 350 ms |

**Later node totals:**
- Strict Fast v20: leaf 11,076 rows / 357.1 KiB; node 33,295 rows / 453.0 KiB / 621 ms; level-2 node 39,605 / 475.0 KiB / 744 ms (`128-bit-grinding-audit.md:1056-1060`).
- Strict Slim v20: node 27,651 rows, 285.8 KiB (`:1065-1066`).
- Family-H closure: 23,133 BLAKE rows, dense area 3,466,436 words, 256.0 KiB (`docs/recursion-100-128-variants.md:216-219`).
- Element slots in a node envelope: el701 16,384 (full), el600 MAC 12,316, el0 spine 9,708, el882 742, el700 126 (`RS_PORT_LOG.md:5448-5456, 5639-5641`).

**Hashing versus algebra** (my arithmetic):
- By AND constraints: 23,133 × 10,298 ≈ 238M for hashing, against < 1M element rows. Hashing is over 99%.
- By committed area: 23,133 × 92 words ≈ 2.13M of 3.47M, about 61%.
- By time: not stated. But adding the F256 algebra took a Slim node from 282 to 592 ms while BLAKE rows grew 17% (`128-bit-grinding-audit.md:1037-1048`). So the algebra is a large share of node *time*.

**Prove times per stage** (online, m32 leaf):

| Date / host | Leaf | FL | Internal | Spine | Amortised per leaf | Source |
|---|---|---|---|---|---|---|
| 2026-08-18, aarch64 | 429.6 ms | 209.2 ms | 196.6 ms | 205.0 ms | 637 ms (412k compressions/s) | `docs/ag-recursion-plan.md:189-191` |
| 2026-08-14, x86 host, 64 logical CPUs, `slim128`, `CHAIN_BLOCKS = 262144` | 1,282.8 ms | 441.0 ms | 424.9 ms | 430.1 ms | 1,718 ms (153k compressions/s) | `recursion-100-128-variants.md:198-212` |

- Amortised per leaf = leaf + FL/2 + node/2 (`e2e_tests.rs:975`).
- The x86 row ran on a host of unspecified ISA level. AG is aarch64-only, so it was RS.

### 2.4 What carries over to our node (BLAKE2s trace digest + one WOTS signature + verifier algebra)

**Carries over** (verifier algebra):
- element-row encoding of F128/F256 MACs (`MacGate`, `MacGate256`);
- the sumcheck round gates (`SpineGate256`, `ZcRoundGate`, `MergedRoundGate`);
- family H (ring switch);
- the Ligerito leaf-eval/residual gates;
- product-GKR, only if we keep a wiring argument;
- the accumulator fold, only if we keep deferral (§2.1).

**Drops out**: the FS duplex rows, H(publics) as BLAKE3, Merkle leaves/paths/caps, `SwapTable`/`BitSpreadTable` glue, `PowMaskTable`, and the AG binding rows.

**Replaced, and probably not cheaper (estimate):**
- The trace digest is `BLAKE2s(0x54 ‖ Σ enc64|q| ‖ q ‖ a)` over **every** oracle query of the child's verifier (`.contract/service/PROTOCOL.md` §2.2). Every Merkle query's input bytes enter the digest once.
- A parent query costs 8 + 64 + 32 = 104 B, about 1.6 compressions, against 1 BLAKE3 row in Flock. A 1 KiB leaf query costs about 16.6 compressions, the same as Flock.
- So the digest costs roughly 1.0–1.6× Flock's Merkle + FS rows. For Secure, with 18,983 per child historically, that is **≈ 20–30k BLAKE2s compressions per child**, against 11–19k BLAKE3 rows. Each BLAKE2s row is 14.7k ANDs, not 10.3k (§3).
- Add about 300–500 compressions for the WOTS check (PLAN 7b).
- For comparison, measured here (§6.5): a current Chain128 node has 21,819 BLAKE3 rows over two children, a 252.8 KiB proof and a per-shape circuit build of about 106 s.
- Ways to cut it are design questions for T and B: larger Merkle arity, capped trees (`cap_depth`, `pcs/ligerito.rs:295-299`), fewer queries, or hashing leaves as single oracle queries.

## 3. Hash R1CS encoders

| Encoder | Block | AND (product) rows | Useful slots | Source |
|---|---|---|---|---|
| BLAKE3 "Option F" | 2^14 | 52·184 + 2·183 + 2·182 = **10,298** | 11,707 | `r1cs_hashes/blake3.rs:24-27, 267-268, 2622-2631` |
| SHA-256 "Option F" | 2^15 | (not stated separately) | 25,470 | `r1cs_hashes/sha2.rs:136-208, 2001` |
| Keccak | — | retired at `0f0d632` ("retire the Keccak encoders") | — | paper Keccak: 38,400 AND, 41,600 committed bits (§4.5) |

### BLAKE3 encoding ("Option F", `blake3.rs:1-80`)

- The only nonlinear constraints are the carry products of 32-bit adds.
- Each G has two fused 3-operand carry-save adds, `a + b + m`. Each costs 31 majority products `w_i = (a_i⊕m_i)(b_i⊕m_i)` plus 30 ripple products, so 61 rows. G also has two 2-operand adds, `c + d`, at 31 rows each. That is 184 rows per G.
- In the round-1 column G's, `c = IV[g]` is a compile-time constant, so the low carries are affine: 30 rows for IV[0] and IV[1] (odd), 29 for IV[2] and IV[3] (even).
- Sum bits, rotations and XORs are never materialised. They are inlined as linear forms at the use site, which makes the matrix template dense (48.3M nnz).
- `C = I`: every slot is the output of one row (input rows `slot·1`, output rows `linfunc·1`, product rows `L·R`).
- The encoder came from the Lean-verified zk.golf record `86e6227e` (`blake3.rs:12-16`).
- There is a second authoring route: a column DSL, `r1cs_hashes/blake3_dsl/{columns,eval}.rs` (134 lines), over `dsl/addition.rs` (`Add3`, `Add32`, `AddConst32`; 200 lines).

### Port to BLAKE2s compression

BLAKE2s's G is identical: the same add/xor/rotate sequence and rotations 16/12/8/7. The IV is the same (the SHA-256 IV).

| Item | BLAKE3 | BLAKE2s | Change |
|---|---|---|---|
| G, fused adders, carry encoding | `G_STRIDE` 184 | same | none |
| Rounds | 7 (`N_ROUNDS`) | 10 | constant |
| Message schedule | fixed permutation `MSG_PERMUTATION` applied per round (`blake3.rs:194`) | SIGMA table, one row per round | table |
| State init v[8..12] | IV[0..4] | IV[0..4] | none; the constant-c saving in round 1 holds as is |
| State init v[12..16] | counter_lo, counter_hi, block_len, flags | t0⊕IV4, t1⊕IV5, f0⊕IV6, f1⊕IV7 | affine; constants if t and f are fixed |
| Output | 16 words: out_lo = v_lo⊕v_hi, out_hi = v_hi⊕cv | 8 words: h' = h⊕v_lo⊕v_hi | affine, no rows |

- **Count.** 80 G's, of which 76 are generic: 76·184 + 183 + 183 + 182 + 182 = **14,714 AND rows per compression**, 1.43× BLAKE3.
- **Layout**, mirroring the chain-aligned layout of `blake3.rs:240-280`: h_in 256 + h_out 256 + m 512 + t/f 128 + constant 1 + 14,714 = **15,867 slots**. That is ≤ 2^14 = 16,384, so `K_LOG = 14` and `K_SKIP = 6` are unchanged, with 96.8% fill against BLAKE3's 71.5%.
- **Prover cost per compression.** Between 1.0× BLAKE3 (block-size-bound passes: commit, NTT and Merkle work on the full 2^14 block) and 1.43× (product-bound passes). **Estimate 1.2–1.4×.**
- **What carries over:** the G-block row emitter and witness driver (`common.rs`: `fused_add3_parts`, `add_carry_parts`, `g_c1_rows`), the lane wiring `G_LANES`, the slot discipline, and the lincheck circuit.
- **What is rewritten:** the round loop (10 rounds, SIGMA), the init/finalise rows, and the I/O slots.
- **Alternatively**, the leanerVM-derived BLAKE2s circuit already in `spartan-srom` (`submissions/spartan-srom/prover/circuit.rs`) can be re-encoded in this style. Its row count should be compared against 14,714.

## 4. Performance-critical kernels and CPU dependencies

All selection is by `#[cfg(target_feature = …)]` at compile time. **There is no `is_x86_feature_detected!` or cpuid anywhere in the workspace.** The repository's `.cargo/config.toml` sets `-C target-cpu=native`, so a binary is fast only on a CPU like the build host's.

Counts of `target_feature` gates: aes 109 (aarch64 PMULL), avx512f 74, vpclmulqdq 57, pclmulqdq 29, gfni 21, avx512bw 16, avx512vbmi 6.

| Kernel | x86 fast path (gate) | Other x86 | Portable fallback | Source |
|---|---|---|---|---|
| F128 scalar mul/square (GHASH) | `pclmulqdq` | — | **bit-serial** `clmul64`: 64 iterations × 4 products | `crates/flock-field/src/gf2_128.rs:27-40, 201-224, 344-389`; `gf2_128/portable.rs:1-45` |
| F128 ×4 SIMD mul | `avx512f + vpclmulqdq` (`ghash_mul_x4`) | — | scalar | `gf2_128/x86_64.rs` |
| Additive NTT butterflies (RS encode, commit) | `avx512f + vpclmulqdq` | — | portable (scalar F128 mul) | `crates/flock-core/src/ntt/additive_ntt_f128/kernels.rs:1-60` |
| Zerocheck round-1 accumulate (s_hat_v) | `avx512f + vpclmulqdq` | — | portable | `zerocheck/univariate_skip_optimized/kernels.rs:20-50` |
| Zerocheck round-1 64-byte bit transpose | `avx512f + avx512bw + avx512vbmi` | — | scalar (was "~85% of round1's time on x86") | `kernels/x86_64.rs:31-40` |
| Zerocheck shift-reduce in F8 | `gfni + avx512f + avx512bw` | `gfni` SSE | scalar | `kernels.rs:57-70` |
| Multilinear zerocheck rounds | x86_64 kernels (`kernels/x86_64.rs`, 164 lines) | — | — | `zerocheck/multilinear/kernels.rs` |
| Lincheck | x86_64 kernels | — | — | `lincheck/kernels/x86_64.rs` |
| Merkle/FS hashing | `blake3` crate (its own runtime SIMD dispatch, C/asm); SHA-256 with `sha` (SHA-NI) | — | portable | `crates/flock-merkle/src/hashing.rs:20-100` |
| AG zerocheck round 1 | — (NEON only; "AVX-512 AG round-1 kernel" pending, Phase F.1) | — | — | `blake3_proof.rs:114-118` |

**Tiers for our dispatch (FR-D5):**
1. AVX-512 hosts (Zen4/Zen5, recent Xeon): AVX-512 + VPCLMULQDQ + GFNI + VBMI. This is the README's 2026-07-17 Threadripper 7970X path. **It is not the evaluation runner.**
2. **The evaluation runner, Zen 3** (EPYC 7763: AVX2, PCLMULQDQ, 256-bit VPCLMULQDQ, SHA-NI; no AVX-512, no GFNI; this is also the contract floor, `.contract/harness/PROVER.md` §1).
   - **Flock has no AVX2/ymm path for any kernel.** `grep` finds no `_mm256_clmulepi64`, no `__m256i` and no `avx2` gate outside a bench label (`benches/hash_throughput.rs:197`).
   - On Zen 3 a Flock build gets:
     - the scalar `pclmulqdq` F128 product (`gf2_128.rs:40, 209`; `gf2_128/x86_64.rs:21`, one `_mm_clmulepi64_si128` per 64×64 limb product);
     - the **portable** NTT butterflies (calling that scalar product);
     - the portable zerocheck `accumulate_convert_with_s_hat_v`;
     - the **scalar** 64-byte bit transpose, which "profiling showed was ~85% of round1's time on x86" before the VBMI kernel (`kernels/x86_64.rs:36-40`);
     - the scalar F8 shift-reduce (no GFNI).
   - **Estimate of the slowdown against the AVX-512 path at equal clock: 2.5–3.5×.** By phase, on the paper's Table 5 BLAKE3 split: commit 24% at ~3× (4-wide zmm products against 1 scalar), zerocheck 37% at 3–5× (transpose, accumulate and shift-reduce all lose their SIMD kernels), open 24% at ~2×, lincheck 9% and witness 5% at ~1×.
   - **The kernels to write for this tier:**
     - a 2-way ymm `vpclmulqdq` F128 product, plus ymm versions of the NTT butterflies and the round-1 accumulate (about half of the AVX-512 kernels' width);
     - an AVX2 `vpshufb`-based 64-byte bit transpose, which replaces `_mm512_permutexvar_epi8`;
     - a `vpshufb` nibble-table F8 multiply, which replaces `gf2p8mul`.
   - The probe at `-C target-cpu=znver3` measures the unmodified tier on the runner, so this estimate gets replaced.
3. This VM (avx512f/vl and avx2, no clmul): the bit-serial fallback. We should replace it with a table- or `vpshufb`-nibble-based carry-less multiply. The current fallback is the reference, not a production path.

**Relative speed:**
- Measured (§6): portable (bit-serial F128) on this VM against the README's AVX-512 + VPCLMULQDQ figures is 31–44× slower per thread for the whole prover (BLAKE3, 2^16 and 2^14). The VM and the Threadripper differ in clock too, so this is an upper bound on the kernel factor.
- The Zen 3 tier (scalar PCLMULQDQ) is **estimated** at 2.5–3.5× slower than AVX-512 at equal clock (above). It is unmeasured until the probe runs.

## 5. Dependencies and emitting one `prover.s`

**Workspace dependencies** (`Cargo.toml` `[workspace.dependencies]`; 56 locked packages): rayon 1.10 (+ rayon-core, crossbeam-deque/epoch/utils, either), sha2 0.10 with `features = ["asm"]` (→ `sha2-asm`, built by `cc`), blake3 1.5 (`build.rs` compiles C/asm SIMD through `cc` unless the `pure` feature is set; Flock uses its `hazmat` API, `crates/flock-merkle/src/hashing.rs`), serde + serde_derive (proc macros, build-time only), bincode 1.3, toml 0.8 (parses the 70 embedded Ligerito TOMLs at run time, `ligerito.rs:528-538`), and rand_core.

**Other facts:**
- `flock-cuda-ffi` builds nothing without `--features gpu`.
- `extern "C"` appears only on Apple targets (`sysctlbyname`, QoS).
- Inline asm appears only on aarch64 (`r1cs_hashes/common.rs:533`, `ntt/.../aarch64.rs:245`).
- The crate uses many `std::env::var` toggles (`VERIFY_TRACE`, `PCS_TRACE`, …), which are harmless.

**How `spartan-srom` did it** (`submissions/spartan-srom/prover/README.md`, `build-asm.sh`):
- std-only Rust with no dependencies.
- `cargo rustc --release --offline --locked` with fat LTO, `codegen-units=1`, `panic=abort`, `--emit asm=…`, `-C target-cpu=x86-64-v2`, `-C llvm-args=-align-all-functions=4` and `--remap-path-prefix`.
- `sanitize-asm.py` drops DWARF and `.debug_*` and refuses `.incbin`/`.include`.
- Linked with the runner's `gcc -static -O2 -pthread *.s -o prover -lm`. Reproducible byte for byte.
- `pclmulqdq` is chosen at run time with `is_x86_feature_detected!` in `field.rs`.
- Its own thread pool is `par.rs` (245 lines).

**For a Flock-class prover:**
- Fat LTO folds all *Rust* crates into one LLVM module, so vendored pure-Rust dependencies (rayon, crossbeam, serde, bincode, toml) are emittable in principle.
- **`cc`-built objects (blake3's C/asm, sha2-asm) are not.** They must be disabled: blake3 `pure`, sha2 without `asm`. Better, remove them, since every Merkle/FS hash is an oracle query and BLAKE2s witness generation needs only a small Rust compressor (`spartan-srom/prover/blake2s.rs`, 237 lines).
- serde/toml/bincode are better replaced: generate the Ligerito schedules as Rust constants, and write the proof format by hand (`harness/FORMAT.md`).
- rayon can stay (vendored, `--offline`) or be replaced by `par.rs`. Flock's `flock-parallel` already wraps one global pool plus one all-core pool.
- `-C target-cpu=native` must go. Build at `x86-64-v2` (or `-v3`) and wrap each kernel family in `#[target_feature(enable = "avx512f,vpclmulqdq,gfni,avx512bw,avx512vbmi")] unsafe fn`, selected once from cpuid. LLVM emits such functions into the same `.s` regardless of the global target CPU.
- The FR-D5 work is to convert about 160 `cfg(target_feature)` sites into run-time-dispatched function pairs.

## 6. Measurements

### 6.1 This VM (development only; not of record)

**Host:**
- 32 vCPUs, 62 GiB RAM.
- CPU flags: avx2, avx512f, avx512vl, aes, bmi2; **no pclmulqdq, vpclmulqdq or gfni** (`/proc/cpuinfo`).
- Load average 8–13 from other jobs during the runs (logged per run).
- rustc 1.99.0 (b940084d7 2026-09-28).

**Build:**
- Flock was copied to `logs/ref/flock` (`48f4bfe`) and built there with `CARGO_TARGET_DIR=logs/flock-target`, so nothing was written into the Flock repository.
- `cargo build --release --locked` took **63.0 s** wall (307 s user) with max RSS 1.03 GB (`logs/phase0-F/build.log`).
- `cargo bench --no-run --bench hash_throughput` (thin LTO, 1 codegen unit) took 2 min 48 s (`bench-build.log`).
- The bench reports its path as "AVX2, RS zerocheck": `target-cpu=native` here has no VPCLMULQDQ, so every F128 kernel is the portable one.

**Hash proving throughput** (`hash_throughput`, best of 3 after a verified warm-up, one process per size; `logs/phase0-F/bench-t{1,4}-2e{14,15,16}.log`, runner `logs/phase0-F/runbench.sh`; 1 thread pinned to CPU 2, 4 threads to CPUs 2–5):

| Batch | BLAKE3 1T | BLAKE3 4T | 4T/1T | SHA-256 1T | SHA-256 4T | process peak RSS (1T / 4T) | load avg at start (1T / 4T) |
|---|---:|---:|---:|---:|---:|---:|---|
| 2^14 | 1,424.7 /s (11.50 s) | 2,356.7 /s (6.95 s) | 1.65× | 824.3 /s | 1,492.7 /s | 2.09 / 2.11 GB | 11.2 / 9.9 |
| 2^15 | 1,870.1 /s (17.52 s) | 3,303.7 /s (9.92 s) | 1.77× | 937.8 /s | 1,762.8 /s | 3.54 / 3.56 GB | 18.7 / 12.0 |
| 2^16 | 2,095.5 /s (31.28 s) | 3,900.2 /s (16.80 s) | 1.86× | 948.6 /s | 1,798.2 /s | 6.47 / 6.50 GB | 5.2 / 13.2 |

- The RSS is the whole process (`/usr/bin/time -v`), which proves SHA-256 (2^15-bit blocks) before BLAKE3, so it bounds BLAKE3's own peak from above. The bench's own BLAKE3-only counter at 2^16 gives 3.38 GB (§1.5).
- Against the README's Zen4 AVX-512+VPCLMULQDQ figures, BLAKE3 1T is 44× slower at 2^14 and 31× slower at 2^16. The 4T/1T scaling is poor (1.65–1.86×) on the portable path, on a shared VM.
- **These numbers are the floor that a no-clmul CPU sets for an unmodified Flock.** They are not a predictor for the runner.

### 6.2 Reference figures (from the repository)

- **README** (2026-07-17, AMD Threadripper 7970X, Zen4, AVX-512 + VPCLMULQDQ, older encoders):
  - BLAKE3 1T 62.7k/s at 2^14 and 64.8k/s at 2^16;
  - 32T 411.7k/s at 2^14 and 540.4k/s at 2^16;
  - SHA-256 1T 32.3k/s and 32.0k/s.
  - The README says the encoders have shrunk since.
- **M4 Max** (2026-10-25, AG): BLAKE3 1T 68.0k/s at 2^14 and 118.9k/s at 2^16; 10T 384.7k/s and 817.1k/s.
- **Paper**: M4 Max BLAKE3 82.1k/s 1T and 661k/s 10T.
- **Peak memory at m = 32 (2^18 compressions)**: 8.52 GB RS / 8.07 GB AG (`RS_PORT_LOG.md:2914-2915, 4038-4040`).

### 6.3 Extrapolation to the season shape (**estimate**)

| Assumption | Value | Basis |
|---|---|---|
| Runner core (EPYC 7763, Zen 3, 3.5 GHz boost) vs Threadripper 7970X core (Zen 4, 5.3 GHz) at equal kernels | ≈ 0.6–0.7× | clock and IPC |
| Zen 3 tier (no AVX-512) against AVX-512 kernels | ÷ 2.5–3.5 | §4 |
| BLAKE3 1T on a runner core at 2^16, unmodified Flock | ≈ 11–18k/s | 64.8k/s × 0.6–0.7 ÷ 2.5–3.5 |
| 4 vCPU against 1T | ≈ 2.5–3× | 2 physical cores × SMT; Flock's 32T/1T is only 8.3× at 2^16, so memory-bound |
| BLAKE3, 4 vCPU, unmodified | ≈ 30–50k/s | |
| (same with an AVX-512-equivalent tier, for reference) | ≈ 100–135k/s | no ÷ 2.5–3.5 |
| BLAKE2s/BLAKE3 cost | 1.2–1.4× | §3 |
| **BLAKE2s, 4 vCPU, unmodified Flock kernels on Zen 3** | **≈ 21–42k/s** | |
| BLAKE2s, 4 vCPU, with an AVX-512-class tier | ≈ 70–110k/s | an upper bound for a ymm tier, which has half the width |

What that means for the season:
- **Tree**: 64 leaves × 2^18 = 2^24 compressions.
  - At 21–42k/s (unmodified, Zen 3) that is **≈ 400–800 s of leaf proving: over `tree_s` = 600 s on its own**.
  - At 70–110k/s it is ≈ 150–240 s.
  - **So the ymm VPCLMULQDQ tier is on the critical path for FR-R5.**
- **Leaf memory**: a 2^18 leaf needs about 8.5 GB peak (m = 32, measured on M4/x86 by the authors). That is under 11 GiB, so one leaf at a time. A memory-lean schedule, or 2^17 leaves, may be needed to overlap work.
- **Merkle commitment hashing through the service.** The L0 codeword at Secure m = 32 is 2^26 F128 = 1 GiB, hashed as 1 KiB leaves: about 2^20 leaf queries of about 17 compressions each, plus 2^20 parent queries. That is about 2^24.1 BLAKE2s compressions per leaf proof, as many as the statement's own 2^18 compressions **× 64**.
  - **Measured service rate on the runner** (coordinator): about 11M calls/s on 1 thread and 30M calls/s on 4 threads for 64-byte queries. A 64 B query is 2 keyed-BLAKE2s compressions (key block + 1). A 1 KiB leaf is 17. **Estimate**, assuming time is linear in compressions: about 3.5M leaf queries/s on 4 threads.
  - Per 2^18 leaf proof that is 2^20 leaves ≈ 0.30 s plus 2^20 parents ≈ 0.035 s, about 0.34 s of the whole machine. That is **≈ 22 s per tree** and about 0.09 s per 2^16 stream leaf. The service shares the 4 vCPUs with the prover.
  - So service hashing is second-order next to proving. Latency must be hidden by batching (256–4096 per `QUERY`, one connection per thread).
- **Nodes.** 63 nodes in Flock's design cost 0.2–0.45 s on 10–64-thread hosts (17–20 s on this VM's portable path, §6.5). On 4 vCPU: **≈ 1.5–4 s each, ≈ 100–250 s per tree**. Our node's trace digest is larger (§2.4).
- **Total.** With unmodified Flock kernels the tree misses 600 s on leaves alone. With a ymm tier near AVX-512 efficiency it is plausible only if nodes stay near the low end. **FR-R5 stays open until the runner probe reports.**
- **Stream link** (2^16-compression leaf + one node, about 3.1 s). Leaf 2^16 / 21–42k/s ≈ 1.6–3.1 s unmodified (0.6–0.9 s at 70–110k/s), plus node ≈ 1.5–4 s, plus start-ups and Merkle via the service (≈ 0.1 s). **Over budget unmodified; tight with the fast tier; the node dominates.**

### 6.4 Runner probe

`probe/flock-bench/run.sh [WORK_DIR]` is self-contained for a fresh `ubuntu-24.04` with rustup. It:
1. prints `lscpu`, the flags and `ImageVersion`;
2. installs rustc 1.99.0 (minimal);
3. fetches github.com/succinctlabs/flock at `48f4bfe56af8c2b0ded19b8990622c4985c21d65` (public; `gh repo view` reports `"visibility":"PUBLIC"`, and the commit resolves through the API);
4. builds with `RUSTFLAGS="$FLOCK_RUSTFLAGS"`, by default `-C target-cpu=znver3`: the runner's Zen 3, which overrides the repository's `-C target-cpu=native`. It prints the enabled and host feature sets. If the target enables a feature the host lacks, it falls back to `native` rather than risk SIGILL. It also reports which Flock tier the build gets. `FLOCK_RUSTFLAGS="-C target-cpu=native"` on an AVX-512 host measures the fast path for comparison;
5. runs `hash_throughput` at 2^14 and 2^16 with 1 thread (`taskset -c 0`) and 4 threads;
6. runs `blake3_proof` at 2^16 under `secure` and `fast`, with 4 threads (proof size, peak memory, verify time);
7. runs `tower::e2e_tests::tower_online_bench` (per-stage leaf/FL/node/spine medians, node BLAKE rows, proof KiB, per-shape build time) at `CHAIN_BLOCKS = 65536` (timeout 600 s);
8. runs `examples/tower.rs` with 8 leaves × 4096 (Chain128, timeout 420 s); a timeout is reported, not fatal;
9. prints a summary with `/usr/bin/time` peak RSS.

Logs go to `WORK_DIR/out/`. Knobs: `LOG2S`, `THREADS`, `RUNS`, `PROOF_LOG2`, `PROOF_PROFILES`, `ONLINE_BLOCKS`, `TOWER_BLOCKS`, `*_TIMEOUT`, `SKIP_TOWER`, `SKIP_EXAMPLE`. On this VM the bench-profile builds (thin LTO, one codegen unit) took about 3 min each with about 16 cores. On 4 vCPU expect several times that per build (release, two benches, tests, example), plus ≤ 17 min of tower timeouts, so set the job timeout to 75 min. A dry run on this VM at tiny sizes is `logs/phase0-F/probe-dryrun.log` (§6.5).

### 6.5 Probe dry run on this VM

(`logs/phase0-F/probe-dryrun.log`, `probe-dryrun2.log`; work dir `logs/probe-dryrun/`): `LOG2S=10 THREADS=1 RUNS=1 TOWER_BLOCKS=256 ONLINE_BLOCKS=256`, CPUs 8–31.

- Clone, pin check, build (65 s), hash bench and proof-size step: all pass.
- Both tower steps **timed out** (300 s / 420 s) on the portable path. They still printed one complete 2→1 node, Chain128, `Slim` outer, 3 runs:

| Quantity | Value |
|---|---|
| outer BLAKE3 rows | 21,819 (12,925 + 8,894 in two b3 slots) |
| nu / dense_m / mu | 14 / 29 / 23 |
| gate cell slots | 331 + 1 public |
| element rows | el701 16,384, el600 15,097, el602 12,662, el0 11,664, … (envelope census lines) |
| online per proof | child tapes ≈ 125 ms + witgen 50–65 ms + **prove 17.3–20.4 s** (VM, portable F128) |
| verify | 176–200 ms, of which "DEFERRED" 61–67 ms |
| node proof | **252.8 KiB** |
| per-shape circuit build | **≈ 106–108 s, serial** (155% CPU) |

- **Consequence for us.** The per-shape setup (circuit emission, R1CS tables) of a Flock-style node is about 2 min of mostly serial work. It does not depend on clmul.
  - For the stream (a fresh process per request, start-up inside `stream_s`), it must be built once in `prover setup` (300 s) and loaded from `/setup`.
  - Alternatively, our node circuit must be far smaller to build. In Flock most of the build is the BLAKE3 Merkle/FS rows and their glue.
- The runner defaults (`ONLINE_TIMEOUT` 600 s, `TOWER_TIMEOUT` 420 s) assume a runner core builds shapes about 1.5–2× faster than this VM. A timeout still prints every completed stage.

## 7. Drift: paper (2026-09-19) against repository (`48f4bfe`)

| # | Item | Paper | Repository | Where (repo) |
|---|---|---|---|---|
| 1 | Security target | 100-bit RBR default; a 120-bit UD variant (Table 4) | strict 128-bit component security (`Fast`/`Slim`, default); `Secure` 120 UD; `Fast100`/`Slim100` 100 | `pcs/ligerito.rs:79-152`; `docs/128-bit-grinding-audit.md` |
| 2 | Merkle + FS hash | SHA-256 compression | BLAKE3 by default (`HashKind::default`); SHA-256 selectable; the tower uses a chained BLAKE3 duplex | `flock-hash/src/lib.rs:13-19`; `flock-transcript/src/challenger.rs:346-360` |
| 3 | Challenge field | all F128 | Ligerito folds, sumcheck claims and MCA in F256 = F128[u]/(u²+u+x⁻¹) | `ligerito.rs:9-14`; `flock-field/src/gf2_256.rs` |
| 4 | OOD | none on the initial commitment (Remark 11; errors ×L); OOD at later commitments | Johnson profiles: 1 OOD sample at L0 and 2 at later levels (two-point binding); Secure none | `ligerito.rs:1940-1965` |
| 5 | Query grinding | none in the main benchmarks; "limited" in slim | 16-bit query PoW at every level in Fast/Slim, and a +2/level rate ladder | `ligerito.rs:1791-1803, 1764-1774` |
| 6 | Other grinding | "a small amount" of proximity-gap grinding (up to 17/12/9/6/4 bits) | per-challenge grinding on zerocheck, lincheck, ring switch, batching, GKR, folds; fold PoW 0 under F256 | `pcs/commit.rs:96-170`; `zerocheck.rs:106-170` |
| 7 | Ligerito schedule (2^14 Keccak) | rates 1/2…1/32, queries 218/106/71/53/43 | the same counts survive as frozen `Fast100` m29 | `configs/ligerito/m29_fast100.toml` |
| 8 | Zerocheck round 1 | RS univariate skip on an F_{2^8} domain | RS on x86; **AG (genus-95 curve code)** by default on aarch64, with a nonce-sampled `r₁` (9-bit PoW) | `zerocheck/ag_skip.rs`; `blake3_proof.rs:114-131` |
| 9 | Friendly challenges | 7 pinned: 3 in F_{2^8} (α) and 4 in F128 (γ) | RS path: φ8/"medium" GHASH challenges; AG: 7 geometric in γ | `zerocheck/univariate_skip_optimized.rs`; `ag_skip.rs:63-90` |
| 10 | Lincheck | (m0 − k_s + 1)-round sumcheck with a skip round; A and B batched | (k_log − k_skip)-round product sumcheck + 64-entry `z_partial`; on the union path the matrix forms are reported and accumulated, not evaluated | `lincheck.rs:541-570` |
| 11 | Ring switch check | App. B: branching-program evaluation of B̂ (HR18) | DP24 tensor-algebra `eval_rs_eq` (from Binius64) with direct φ8-Lagrange weights | `pcs/ring_switch.rs:11-60` |
| 12 | Relation | batch R1CS + IO glue G (chains; Merkle "details omitted") | union/mixed-class registry (boolean + F128 element tables), product-GKR wiring, jagged PCS, public-chain and Merkle wrapper arguments | `flock-core/src/{union,element_r1cs,product_gkr,circuit}.rs`, `pcs/jagged.rs` |
| 13 | Hashes proved | Keccak, SHA-256, BLAKE3 | SHA-256 and BLAKE3 only; Keccak retired at `0f0d632` | `r1cs_hashes/` |
| 14 | Recursion | not described (motivation only) | a full tower: leaf / FL / node / spine, deferred matrix accumulator, root discharge | `crates/flock-prover/src/tower/` |
| 15 | Skip-variable position | first in §4.2/§4.4, last in App. A (paper-internal inconsistency) | the code's `QuirkyPoint (z_skip, x_inner_rest, x_outer)` | `lincheck.rs:62-70` |
| 16 | Proof format | — | proof-IO v22 (profile consolidation, 2026-08-27) | `docs/recursion-100-128-variants.md:23-31` |
| 17 | Platform | Apple M4 only; x86 not mentioned | AVX-512 + VPCLMULQDQ x86 kernels, compile-time selected | §4 |

The paper's soundness tables (App. A p. 36, App. C p. 44) are round-by-round, with L_max factors and residual zerocheck rounds at 2/|F|. The repository's grinding derivation uses the same degrees (`zerocheck.rs:110-170`).
