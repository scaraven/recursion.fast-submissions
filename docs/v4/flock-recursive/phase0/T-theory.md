# Flock 1.0 recursive: theory and parameters (phase 0, track T)

Status: design memo, 2026-10-27, for the blueprint (phase 1, B). Resolves FR-D3, FR-D6 and the
kill tests of FR-R1 … R3 (`PLAN.md` §5). It writes no code. Evidence tags: **paper** (an argument
here or in a cited source), **estimate** (arithmetic from measured or published inputs),
**kernel** (a Lean theorem that exists today, named with its repository), **kernel-probe** (a
probe run for this memo: none were needed). Every unmarked number is arithmetic on marked ones.

Sources read: the contract (`.contract/RecursionFast/Contract/*.lean`), DESIGN-v4-srom §0–2,
§3.5–3.7, §4.2, §6.2; v3 lessons §5; the baseline's README and blueprint; the Flock paper
(2026-09-19) §3–4, App. A–C; the Flock repository at `48f4bfe` (`ligerito.rs` profiles and
TOMLs, `docs/*.md`, `docs/*.tex`); leanerVM PRs #128–#156 and issue #157; CompPoly `572f997`
(`Univariate/ReedSolomon/Gao*.lean`, `Fields/Binary/BF128Ghash`, `Fields/Binary/AdditiveNTT`).

---

## 0. One-page summary

**Protocol (FR-D6).** Flock's batch-R1CS argument over GF(2) with the **repository's `Secure`
profile** as the starting point, not the paper's 100-bit list-decoding profile: Spartan-style
zerocheck with the degree-64 univariate skip (`k_s = 6`) and 7 pinned "friendly" coordinates,
lincheck by circuit walking, the hash-chain shift argument for IO, ring switching (paper App. B),
and **Ligerito over GF(2^128) in the unique-decoding regime**: rate ladder 1/2, 1/4, …, 1/64, 64
rows at level 0 then 16, queries **290, 178, 145, 132, 126, 124**, no out-of-domain sample, **no
grinding anywhere**. Every Ligerito fold challenge is drawn from **K = GF(2^256)** (the repository
does the same; the paper does not), with the folded word split back into two GF(2^128) coordinates
before the next commitment. Everything else stays in F = GF(2^128). Hash: BLAKE2s through the
SROM service (contract). Leaves are proofs of a BLAKE2s chain with the start `s` sent in the clear
(as the baseline does), so **only nodes need a decoding extractor**.

**Parameters (nodes and leaves share one ladder family; `m` = log₂ of the committed bits).**

| Object | `m` | witness | proof `π` | trace | `qV` | verifier field mults |
|---|---|---|---|---|---|---|
| stream leaf, 2^16 compressions | 30 | 2^30 bits | ≈ 714 KiB | ≈ 1.22 MB | ≈ 7.1 k | ≈ 1.0·10^5 F |
| tree leaf, 2^17 compressions (recommended; 2^18 is `m = 32`, 776 KiB, and risks 11 GB) | 31 | 2^31 | ≈ 745 KiB | ≈ 1.33 MB | ≈ 8.1 k | ≈ 1.0·10^5 F |
| node (two children of `m ≤ 31`) | **30 or 31** (fixed point, §3) | ≈ 0.75·2^30 bits used | ≈ 714–745 KiB | ≈ 1.22–1.33 MB | ≈ 7.1–8.1 k | 1.0–2.8·10^5 F |

`T_V ≈ 4 ms + N_mul · t_mul + 10^6 · t_xor` with `N_mul = 1.0·10^5` (aligned wiring) to
`2.8·10^5` (gather wiring, §3.3): **20–110 ms** for `t_mul` = 50–300 ns (**estimate**; cap 178 ms).
Proofs fit `proofCap` with ≥ 24 % margin; `qV ≤ 2^16` with 8× margin.

**Per-round error (FR-D3, §1.3).** Every Fiat–Shamir phase charges at most `2^-120` per fresh
query: the tightest are the univariate skip (`126/2^128 = 2^-121.0`), the query phases
(`2^-120.4 … -120.7` after one extra query at level 1) and the zerocheck's initial point
(`18/2^128 = 2^-123.8`). The fold rounds would be `2^-110` over F; over K they are `≤ 2^-237`,
which is the one place GF(2^256) is required. Grinding is not needed; `δ ≈ 2^-110`.

**Extraction (FR-R3, §4).** Straight-line, no list decoding. For a node: read the level-0 Merkle
tree off the log (first preimage per digest), decode the ladder bottom-up; at each level compute
the fold of the extracted next-level polynomial and the K-fold of every present column, take the
agreement set `A` (`|A| ≥ (1−γ)n ≥ k` under `μ < 1`), and **erasure-interpolate each row from `k`
positions of `A`** (naive quadratic Lagrange; no NTT, no Berlekamp–Welch, no Gao). The
"cancellation" charge is inside the K-fold's mutual-correlated-agreement term (`≤ 2n/2^256`); one
combination suffices. Steps: `≈ 2^45` at `m = 30`, `≈ 2^47.3` at `m = 31`, against
`2^48 + 2^16·t ≥ 2^48`. Output `≈ 2^19.3` words of `outCap = 2^24`. CompPoly's Gao decoder
(`decode_eq_some`, kernel) is 4–8× costlier here (its Euclid is quadratic in `n`, interpolation
is quadratic in `k = n/2`) and overflows the fuel at `m = 31`; it is the fallback only if the
agreement-set route is refused in review.

**Verdicts.** FR-R1 **feasible** (776 KiB at `m = 32`, 714 KiB at `m = 30`; `T_V` 20–110 ms).
FR-R2 **feasible** at zero grinding with K-folds and eq-structured batching. FR-R3 **feasible**
for node shapes `m ≤ 31` with quadratic erasure decoding; **infeasible** by `2^1.3` at `m = 32`
unless the decoder is quasi-linear (the blocking cap is the fixed term `2^48`; smallest unblock:
`2^50`). Two rule-side items for the core: the organiser allowlist does not contain
`CompPoly.Fields.Binary.BF128Ghash` nor ArkLib's proved Johnson MCA, which this design wants
(§6, D-9).

**Drift from the paper (§6):** BLAKE2s/SROM instead of SHA-256; UD 120-bit instead of
list-decoding 100-bit; K-folds with coordinate split; no OOD; Merkle caps; eq-structured
consistency batching; 8-byte-aligned query formats; nodes are SROM circuits (trace hash + WOTS +
replay), not Flock's Merkle-verifying tower with Nova-style matrix folding and a Plonk/GKR
permutation.

---

## 1. Protocol and parameters

### 1.1 Statements, circuits, shapes

- **Leaf** (`Rel`'s leaf clause): `π = enc64 0 ‖ s ‖ enc64 n ‖ h ‖ π_S` as in the baseline;
  `V` checks `c = leafStmt h n`, `n ∈ {2^16, 2^17}` (the two shapes; a shape byte selects the
  ladder), and `π_S` proves `chainEnd s n = h`: a batch of `n` BLAKE2s compressions (`chainStep`,
  one compression each; leanerVM's circuit, ≈ 16 k AND gates = `m₀ = 14`) with the paper's
  hash-chain shift argument (§4.6) tying `Out(i) = In(i+1)` and the endpoints `s`, `h`. Witness
  `2^16·2^14 = 2^30` bits (`m = 30`) or `2^31`.
- **Node** (`Rel`'s node clause): `π` carries `c₁, c₂` and `π_S` proving `acc vk c₁ p₁ ∧ acc vk
  c₂ p₂` for signed proofs `p₁, p₂` in the witness. Circuit in §3. Shape `m = 30` or `31`.
- **Only the root is read in the tree** (design §3.5), so the tree's internal leaves are the
  prover's choice; 2^17 keeps memory under 11 GB (§3.4). The stream's leaf is fixed at 2^16.

### 1.2 The PIOP, round by round (paper App. A, with the choices fixed)

1. Commit `ẑ` (quirky extension: multilinear in `m − 6` variables, degree `< 64` in the last)
   through ring switching: `m − 7` packed F-elements, Ligerito level 0.
2. **Zerocheck** on `a·b − z` over `D = {0,1}^{m−6} × S`: `r ∈ F^{m−6}` with the first 7
   coordinates pinned to the paper's geometric progression (kernel-checkable F₂-independence,
   128×128 rank by `decide`), the rest random; univariate skip: `P^{ab}, P^{z}` on `Λ` (2 × 64
   F-elements), `λ ∈ F`; then `m − 6` sumcheck rounds of degree 2 (paper) — the repository's
   degree-3 eq-weighted tail is also fine at `3/|F|`. Skipping `c` (`C = I`, paper §4.4).
3. **Lincheck** on `A₀, B₀` (base `m₀ = 14` for BLAKE2s; the node adds small base tables, §3):
   `α`-batched, `m₀ − 6 + 1` rounds; the verifier evaluates `Â₀, B̂₀` at the point by the
   backward circuit walk (F-additions only).
4. **IO**: the shift sumcheck over `log K` variables plus the 8-variable bit collapse; node: the
   public `(vk, c)` bound through one MLE claim.
5. **Claim batching**: the ≤ 8 claims on `ẑ` (zerocheck's `(r,λ)` claim, lincheck's, IO's) by
   powers of one `α ∈ F`.
6. **Ring switching** (paper B.2–B.3, quirky variant): 128 partial evaluations `s_v`, `r'' ∈ F^7`,
   `m − 7` sumcheck rounds; the verifier evaluates `B̂` by the width-128 matrix branching program
   (`m − 7` layers: 128 F-mults and 16 k conditional XORs each).
7. **Ligerito opening** of the packed polynomial (`m − 7 = 23` or `24` variables), `Secure`
   ladder (repository `m30_secure`/`m31_secure`): level `i` has `2^ℓᵢ` rows (`ℓ₀ = 6`, then 4
   = 3 original variables + 1 coordinate-split bit), message length `kᵢ`, rate `ρᵢ`, codeword
   length `nᵢ = kᵢ/ρᵢ`, `tᵢ` queries:

   | level | `ρ` | rows | `log₂ k` (m=30 / 31) | `log₂ n` | `γ = δ/2 − 3/(δn)` | bits/query | `t` |
   |---|---|---|---|---|---|---|---|
   | 0 | 1/2 | 64 | 17 / 18 | 18 / 19 | 0.2500 | 0.415 | 290 |
   | 1 | 1/4 | 16 | 14 / 15 | 16 / 17 | 0.3750 | 0.678 | 178 (repo: 177) |
   | 2 | 1/8 | 16 | 11 / 12 | 14 / 15 | 0.4375 | 0.830 | 145 |
   | 3 | 1/16 | 16 | 8 / 9 | 12 / 13 | 0.4687 | 0.913 | 132 |
   | 4 | 1/32 | 16 | 5 / 6 | 10 / 11 | 0.4844 | 0.956 | 126 |
   | 5 | 1/64 | 16 | 2 / 3 | 8 / 9 | 0.489 | 0.969 | 124 |
   | final | — | — | 2^5 F-elements in the clear | | | | |

   Per level: `ℓᵢ` fold rounds with challenges in **K**; commit the folded word (two F-coordinates
   as one extra variable); `tᵢ` positions of `log₂ nᵢ` bits each, 12 per 256-bit answer; the
   `tᵢ` consistency claims `Enc(f⁽ⁱ⁺¹⁾)[j] = C⁽ⁱ⁾_s[j]` batched with the main claim by
   **eq-structured coefficients** over `⌈log₂(tᵢ+1)⌉ = 9` F-coordinates (repository's form), not
   powers of one `α` (that would be `t/|F| = 2^-119.8`, over the cap). Merkle: binary, caps at
   depth `⌈log₂ tᵢ⌉` sent in `π` (repository), node queries and column queries as oracle
   queries with an 8-byte kind tag so that every 16-byte field element in the trace is 16-byte
   aligned (§3.3; `|q| ≡ 8 mod 16`).

**Why Ligerito and not WHIR/FRI/Basefold/Blaze** (FR-R1's choice). All polylog hash-based PCSs
have proofs of the same order (`Σᵢ tᵢ · (2^ℓᵢ·16 + 32·depthᵢ)`; WHIR's per-query cost is the same
sum over levels). What differs is the Lean content: WHIR/FRI/Basefold fold the **code** (a
degree-halving map on an F₂-subspace domain needs the subspace-polynomial machinery and a
"folding preserves RS" lemma); Ligerito folds **rows**, so the folded row is a codeword of the
same code by linearity, and the only proximity fact is correlated agreement for lines (§1.4). Its
extractor decodes every level with one code (§4). Brakedown/Blaze would need decoding of a non-RS
code. The baseline's √-size Ligero is excluded by `proofCap` (v3 lessons §5.1).

### 1.3 Per-round error table (node at `m = 31`; a leaf has fewer rounds, never a larger term)

Each phase is one "group" of the potential (§4.4): its total bad probability is charged on the
first fresh query that opens it and then evolves as a martingale, so the **per-fresh-query rise**
is the phase total (plus the hash terms). Columns: field the challenge is read from, bad
probability, `−log₂`.

| # | Phase | Field | Bad probability | bits | Source |
|---|---|---|---|---|---|
| Z1 | zerocheck initial point, `m − 6 − 7 = 18` random coordinates | F | `18/2^128` | 123.8 | SZ on the multilinear in the free coordinates; DT24 for the pinned ones (**paper**) |
| Z2 | univariate skip `λ` | F | `2(2^6 − 1)/2^128 = 126/2^128` | **121.0** | degree of `P^{ab} − P^{z}` (**paper**, App. A) |
| Z3 | 25 sumcheck rounds (`m − 6`), degree 2 (3 if eq-weighted) | F | `2/2^128` (`3/2^128`) each | 127 (126.4) | sumcheck |
| L1 | lincheck `α` | F | `1/2^128` | 128 | batching of 2 claims |
| L2 | lincheck rounds, `m₀ − 5 = 9` | F | `2/2^128` | 127 | sumcheck |
| I1 | shift argument `τ`, `≤ 18` coordinates; bit collapse 8 | F | `18/2^128`, `8/2^128` | 123.8, 125 | SZ (**paper** §4.6) |
| E1 | node only: element-table zerocheck, 17 coordinates + rounds of degree 3 | F | `17/2^128`, `3/2^128` | 124.1, 126.4 | Spartan over F |
| B1 | claim batching, ≤ 8 claims by powers | F | `7/2^128` | 125.2 | SZ |
| R1 | ring switch `r''` (7 coordinates), then 24 rounds | F | `7/2^128`, `2/2^128` | 125.2, 127 | paper B.2.1 (fn. 17) |
| P1 | Ligerito fold round (26 in all), level `i` | **K** | `(γnᵢ + 1)/2^256 + nᵢ/2^256 + 2/2^256 ≤ 2^19.2/2^256` | **≥ 236.8** | MCA in UD (§1.4) + cancellation + sumcheck |
| P2 | query positions, level `i`, `tᵢ` positions | 20-bit | `(1−γᵢ)^{tᵢ}` | 120.4, 120.7, 120.3, 120.5, 120.4, 120.2 | consistency check, uniform positions (**paper** C.3) |
| P3 | consistency batching, level `i`, 9 eq-coordinates | F | `9/2^128` | 124.8 | SZ on a 9-variable multilinear |
| H | every fresh query: collision with a logged digest, hit on an in-play digest, root hits | — | `≤ (4·logCap + 8)/2^256` | ≈ 157.9 | v3 §6 / leanerVM #143 `charge_le` (**kernel** there, for its reader) |

Maximum per fresh query: `2^-120.2` (P2 at level 5 plus H) — the memo keeps every phase at
least `0.2` bits under the cap; the repository's `177` at level 1 would be `2^-120.006`, hence
178. **Where GF(2^256) is needed:** P1 only (over F the term is `2^19/2^128 = 2^-109` at level 0
and above the cap down to `n ≤ 2^9`, i.e. at every level but the last). **Where grinding would be
needed:** nowhere; the alternative to K-folds is 11–13 bits of grinding on each of the 26 fold
rounds (prover ≈ `26·2^13` extra service calls per proof, and a `(1 − 2^-g)^N ≤ 2^-40`
completeness lemma); not chosen. `k_s = 7` would give `254/2^128 = 2^-120.01`: too tight, so
`k_s = 6` is a hard choice. One 256-bit answer may serve two F-challenges of two different
rounds (charge the sum, e.g. `4/2^128`), never Z2 and another.

**Completeness.** No grinding, so the honest prover fails only on degenerate challenges it
cannot serve (`λ ∈ S ∪ Λ`, a zero eq-coordinate in P3, a fold challenge that zeroes a Lagrange
denominator): `δ ≤ 2^-110` (**estimate**), against `completenessCap = 2^-40`.

### 1.4 The proximity theorem (the one non-trivial Lean fact of the PCS)

Needed per fold round, for a `2 × n` word `(u₀, u₁)` over F and a line `u₀ + z·u₁` with `z ∈ K`
(the two-row case; `ℓ` rows are `ℓ` rounds, paper Lemma 9 / ACFY25 Lemma 4.13 applied round by
round, as the repository does): **mutual correlated agreement up to the unique-decoding radius**:
for all but `ε·|K|` values of `z`, every agreement set `A` (`|A| ≥ (1−γ)n`) of `u_z` with
`RS[K, D, k]` is an agreement set of `(u₀, u₁)` with the interleaved code.

- Over K, `RS[F, D, k] ⊆ RS[K, D, k]` and an interleaved K-codeword agreeing with F-valued rows
  on `≥ k` positions is F-valued (interpolation), so the theorem over K applies to F-words.
- **Route A (recommended, paper):** correlated agreement for lines up to `γ < δ/2` with error
  `≈ n/|K|` (BCIKS20 Thm 4.1 for RS codes; DP24 for every linear code; both elementary,
  Berlekamp–Welch-style) **plus** the cancellation term: in the UD regime the nearby codeword
  `w` of `u_z` is unique, equals `v₀ + z v₁`, and `u_z` agrees with it outside the joint agreement
  set `A_max` only where `u₀[j] − v₀[j] = z(v₁[j] − u₁[j])`, at most one `z` per position: `≤ n/|K|`
  more. So MCA-UD = CA-UD + `n/|K|`, total `≤ 2n/|K| ≈ 2^-237`. This is what P1 charges.
- **Route B (kernel, elsewhere):** ArkLib's proved Johnson-regime MCA for affine lines
  (`ReedSolomon.mcaError_affineLine_johnson_le`, consumed by leanerVM #130 as
  `mcaJohnson_comparisonEstimate`) applies a fortiori at `γ ≤ δ/2 < 1 − √ρ − η`: with
  `η = 1 − √ρ − γ` (0.043 at `ρ = 1/2`, 0.125 at `1/4`) the constant `a` is about `2^21.6·n` at
  `ρ = 1/2` and `2^13.3·n` at `1/4`, i.e. `≤ 2^-216` over K. Zero formalisation cost if ArkLib's
  module can be imported (it is outside the organiser allowlist today: D-9, §6).
- The paper's Theorem 7 (BCHKS25 Cor. 1.4, `a = γn + 1`) is tighter than either but not
  formalised anywhere; it is not needed.

The v3 baseline's AHIV22 lemma (`far_bad_le`, radius `d/3`, independent coefficients) is not
enough: at `γ < δ/3` the query counts rise to 457 at rate 1/2 and the proof to ≈ 1.2 MiB.

---

## 2. Sizes and verifier work

**Proof `π`** (bytes; `Secure` ladder; caps at depth `⌈log₂ t⌉`; Merkle siblings
`32·(depth − cap)` per query; final polynomial 512 B; sumcheck transcripts ≈ 5 KB; skip
messages 2 KB; ring-switch `s_v` 2 KB; headers, `c₁ c₂`, shape):

| part | m = 30 | m = 31 | m = 32 |
|---|---|---|---|
| level-0 columns `290·64·16` | 296,960 | 296,960 | 296,960 |
| levels 1–5 columns `(178+145+132+126+124)·16·16` | 180,480 | 180,480 | 180,480 |
| Merkle siblings `32·Σ tᵢ·(depthᵢ − capᵢ)` (5,934 / 6,929 / 7,924 siblings) | 189,888 | 221,728 | 253,568 |
| caps `(512+256+256+256+128+128)·32` | 49,152 | 49,152 | 49,152 |
| PIOP messages, headers | ≈ 15,000 | ≈ 15,000 | ≈ 15,000 |
| **total** | **≈ 731,500 B = 714 KiB** | **≈ 763,300 B = 745 KiB** | **≈ 795,200 B = 776 KiB** |

`proofCap = 1,048,576 B`: margins 30 %, 27 %, 24 % (**estimate**; the repository measures its
`Secure` node at 566–589 KiB with 41 k BLAKE rows, consistent in order with the m ≈ 29 envelope).

**Trace and queries** (`m = 31`; a node of shape `m` has the same counts as a leaf of shape
`m`): column queries 290 + 704 = 994 items (1,072 B and 304 B, the 40-byte envelope included);
Merkle node queries `Σ tᵢ·(depthᵢ − capᵢ) = 2900+1602+1015+660+504+248 = 6,929` items of 112 B
(5,934 at `m = 30`); Fiat–Shamir ≈ 200 items of ≤ 200 B. `qV ≈ 8.1 k` (`7.1 k` at `m = 30`);
trace bytes `≈ 311 k + 214 k + 776 k + 30 k ≈ 1.33 MB` (`1.22 MB`); `acc`'s `traceDigest`
hashes it in `≈ 21 k` compressions (`≈ 2.2 ms` at the measured 106 ns, design §3.5) plus
`SigOk` 0.23 ms.

**Verifier operation counts** (no hashing: every digest is a trace lookup):

| work | count, leaf (m = 30/31) | count, node (m = 30/31) |
|---|---|---|
| Ligerito column folds `Σ tᵢ·2^ℓᵢ` K×F products (= 2 F-mults each) | 29.8 k → 59.6 k F | same |
| eq tables, final-level RS evaluations `124·32`, fold sumcheck rounds in K, consistency eq-weights `9·Σtᵢ` | ≈ 15 k F | ≈ 15 k F |
| univariate skip: Lagrange at `λ` over 128 points | ≈ 20 k F (naive) | same |
| sumcheck rounds (zerocheck 25, lincheck 9, ring switch 24, IO 26) | ≈ 300 F | ≈ 400 F |
| ring switch MBP: `(m−7)·128` mults + `(m−7)·2^14` conditional 128-bit XORs | 3.1 k F + 4·10^5 XOR | same |
| lincheck circuit walk (F-additions over the base circuit) | ≈ 6·10^4 XOR | ≈ 10^5 XOR |
| node wiring MLEs (§3.3): aligned layout / gather layout | — | 2 k / 1.8·10^5 F |
| **total** | **≈ 1.0·10^5 F-mults, ≈ 5·10^5 XOR** | **≈ 1.0·10^5 (aligned) – 2.8·10^5 (gather) F-mults, ≈ 10^6 XOR** |

`T_V ≈ 4 ms + N_mul·t_mul + N_xor·t_xor`. With `t_xor ≈ 10 ns` (two `UInt64` XORs in compiled
Lean, **estimate**, M measures) and `t_mul ∈ [50, 300] ns`: leaf 15–40 ms; node 20–55 ms
(aligned) or 35–110 ms (gather). Cap `≈ 178 ms`. The binary-field bias of `T_V` (design Q11)
costs us a factor 3–6 against a word-code verifier and still fits.

A 2^18 leaf (`m = 32`) has the same counts plus one more MBP layer and sumcheck round; it is not
recommended for memory reasons (§3.4), and it is never a child shape the node must support if the
tree uses 2^17 leaves.

---

## 3. The node circuit under the SROM

### 3.1 What it proves

`c = nodeStmt c₁ c₂` and, for each child `(πᵢ, trᵢ, σᵢ)`: `|πᵢ| ≤ proofCap`, `|trᵢ| ≤ qV`, every
query `≤ queryCap`, `SigOk vk (traceDigest trᵢ) σᵢ`, and `(V vk cᵢ πᵢ).runSeq trᵢ = some true`. The
circuit never evaluates the oracle: a trace answer is a witness value; it is **hashed** (trace
digest) and **used** (as a challenge or a Merkle value), and `acc` of the node's own proof makes
the service's signature vouch for it.

### 3.2 Regions and sizes (per `m ≤ 31` child; `m = 31` numbers)

| region | content | compressions / elements | AND gates |
|---|---|---|---|
| **T** | the child's trace, packed 16 B per element, items 16-aligned (tags) | 1.33 MB = 2^16.3 elements = 2^23.3 bits | — (linear) |
| **H** | BLAKE2s batch: the trace digest of T as one streaming hash, `⌈1.33 MB / 64⌉`, plus the node's own FS items | **≈ 21 k compressions** (19.2 k for an `m = 30` child) | 21 k · 16 k = 2^28.4 |
| **W** | WOTS: ≈ 400 chain steps (selectors, worst 396), key leaf 67, path 32 | ≈ 500 compressions | 2^23 |
| **M** | GF(2^128) products as element rows `a·b = c` (3 packed elements, one degree-2 constraint over F): column folds 59.6 k, skip Lagrange 20 k, eq/K arithmetic ≈ 15 k, sumchecks ≈ 1 k, MBP 3.2 k, inversions as `x·x⁻¹ = 1` | ≈ 100 k rows | 300 k elements = 2^25.2 bits |
| **L** | bit logic: parsing, equalities (answer = expected digest, final sum = claimed), `runSeq` order, byte/element views, `nodeStmt` (1 compression), shape checks | ≈ 2^20 | 2^20 |

Two children + `nodeStmt`: **≈ 43 k compressions** (`2^29.4` AND gates) + M `2^26.2` + T
`2^24.3` + L `2^21` → **≈ 0.75·2^30 bits** (**estimate**). The repository's own tower node has
23–33 k BLAKE3 rows for two children; ours is ≈ 1.5–2× because the trace carries `40 + tag` bytes
per query and the UD ladder opens `Σt = 995` columns against 460.

**Recursion fixed point.** A node of two `m ≤ 31` children commits `≈ 0.75·2^30` bits, so its
proof shape is **`m = 30` if B's exact count stays under 2^30, else `m = 31`** (2.7× slack).
Both are `≤ 31`, so a node verifies nodes of the same shape, and the stream's merge (node + 2^16
leaf) and the tree's level-1 nodes (two 2^17 leaves) are instances of the same circuit with the
child shape as a header field; unused rows are padded. If the tree used 2^18 leaves the level-1
node would have to replay `m = 32` children (`≈ 24 k` compressions each) and the circuit would be
`≈ 0.85·2^30`, i.e. still `m = 30` or `31`, with the extractor at most at `2^47.3` (§4.3).

### 3.3 Wiring, and why there is no permutation argument

Flock's recursion connects its 29 table types through a Plonk-style permutation checked by a
product-tree GKR, and defers the lincheck's matrix evaluation into a Nova-style accumulator
(`circuit-wiring-design.tex`, `folding-verifier-design.tex`). Neither is in the Lean library and
both are large. This design avoids them:

- **T is the single source.** Every byte of `πᵢ` is absorbed somewhere in `trᵢ` (columns and
  siblings as Merkle preimages, everything else as Fiat–Shamir absorbs), so the circuit holds the
  trace and reads `πᵢ`'s values out of it.
- **Alignment.** Queries carry an 8-byte kind tag and `|q| ≡ 8 mod 16`, so items are 16-byte
  aligned and every field element, digest half and sumcheck coefficient is one packed element of
  T. H's message blocks are 4 consecutive elements of T (`trace(4i + j) = H(i, msg, j)`: an
  identification of index spaces, free for the verifier). The hash chain between compressions and
  the WOTS chains are shift arguments (one degree-2 sumcheck each). Merkle: the answer of item `i`
  equals the left or right 32-byte half of item `i+1`'s query, by a selector bit: a shift
  argument with a witness selector (degree 2).
- **M's operands** come from T at addresses fixed by the shape. Two options for B: (a) **gather
  lincheck**: the claim `y_q = Σ_b w_b · x(start_q + b)` for all `q` as one degree-2 sumcheck
  over `(q, b)`; the verifier evaluates the gather weight `Σ_{q,b} eq(τ,q) eq(ρ,b) eq(σ, start_q+b)`
  with the incremental-eq trick (≈ 2 mults per consecutive address): ≈ 1.8·10^5 mults per node;
  (b) **aligned padding**: pad column items to 128 elements and node items to 8 so that
  `start_q + b` factorises as `(q ‖ b)`; the weight is then a product and costs O(1) per region,
  at +15 compressions per column (+20 % on H). (b) is cheaper for `T_V`, (a) for the prover; the
  memo's `T_V` range covers both.
- **M rows are a batch R1CS of one base instance** (`a·b = c`) checked by a degree-3 Spartan
  zerocheck over the packed polynomial directly (the repository's "element tables"); no ring
  switching is needed for them. L is a small generic GF(2)-R1CS (lincheck cost `O(nnz) ≈ 2^21`
  F-additions for the verifier).

The circuit's correctness theorem ("every satisfying `z` makes `acc vk cᵢ pᵢ = true`") is the
largest Lean item of the entry (L-circ). It decomposes along the regions: H ≡ `blake2s`
(leanerVM's transcription, already in the baseline), M ≡ field multiplication, shift arguments ≡
sequencing, and L ≡ `V`'s straight-line replay, which requires `V` to be written shape-first (parse,
then a fixed query sequence) so that `runSeq` on a well-shaped trace is that straight line.

### 3.4 Proving cost (4 runner cores; **estimate**, M/F measure)

Throughput inputs: Flock BLAKE3 at 64.8 k c/s single-thread on a Threadripper 7970X (VPCLMULQDQ),
20 k c/s per thread at 32 threads; M4 Max 123 k single, 958 k on 10 cores (repository README).
BLAKE2s has 10 rounds to BLAKE3's 7 (×0.7). Range used: **60–120 k compressions/s on 4 runner
cores** for leaf work. A node ≈ 43 k compression-equivalents of zerocheck/witness work plus a
PCS commit of `2^23–2^24` elements (≈ 0.35–0.5 of a 2^17 leaf): **0.6–1.2 s per node**.

- Tree, 128 leaves × 2^17 + 127 nodes: `2^24/(60–120 k) = 140–280 s` + `127 × 0.6–1.2 = 76–152 s`
  → **216–432 s** (`tree ≤ 600 s`). With 64 leaves × 2^18: 140–280 + 63 × 0.7–1.4 → 185–370 s,
  but a 2^18 BLAKE2s leaf is ≈ 1.4× the paper's 2^18 BLAKE3 batch, which it stopped at ≈ 10 GB:
  over the 11 GB prover cgroup (FR-R5), hence 2^17.
- Stream link: leaf 2^16 `0.55–1.1 s` + merge `0.6–1.2 s` + two `SIGN`s re-evaluating ≈ 17 k
  queries + start-up → **1.3–2.5 s** (`≤ 3.1 s`).
- Service traffic per proof: ≈ 2·10^5 queries (level-0 Merkle tree of 2^18–2^19 leaves plus
  the ladder), batched 256–4096 per round trip (PROTOCOL.md §2.1).

---

## 4. Extraction

### 4.1 What the contract asks (`Contract/Extractor.lean`, read for this memo)

`Computes S.ext S.E S.fuel` requires: `S.E : Digest → Proof → Log → Option Wit` is **any Lean
function** (it must compile, since the badge compiles the whole `submission`; it need not be
fast), and `S.ext : XProg` is a program of the word machine that, on **every** input tape (any
`c`, any `π ≤ proofCap`, any log whose tape fits 2^64 words), halts within `fuel t ≤ 2^48 +
2^16·t` steps (one per statement and per memory word) with `≤ 2^24` output words that **decode to
`E c π L`**. So CompPoly's or Mathlib's theorems serve the **specification side** (the `KS` proof:
"if `V` accepts on `L` and `μ L < 1` then `E` returns a witness of `Rel`"); the **refinement side**
(`decodeWit (ext.run tape fuel) = E c π L`, with the step count) is a separate proof about the
machine program and is where the design's simplicity pays. `E` takes no `vk` (V4-6).

### 4.2 The extractor `E c π L`

**Leaf shape:** read `s, n` from `π`'s header; output `.leaf s n`. (Soundness: the circuit proves
`chainEnd s n = h` and `V` checks `c = leafStmt h n`.) No decoding.

**Node shape** (bottom-up over the ladder; `L` is the whole run's log, `t ≈ 2^26` words at least
for one node's columns):

1. Parse `π`: shape, `c₁ c₂`, the level caps, the final polynomial `g_final`, the transcript.
   Reject (output `none`) on any shape or length mismatch: constant work.
2. Index the log: copy `(answer, position)` pairs into memory and merge-sort by answer
   (`memPerWord = 2`; the budget's linear term, `≈ 2^11` steps per word).
3. For each level `i = 5 … 0`: rebuild the Merkle tree under its cap top-down by **first-preimage
   lookup** (leanerVM #128's `extractTree`/`extractLeaf` shape: the first logged entry whose answer
   is the digest and whose query parses as a node of the right kind tag, then as a column); a
   digest with no preimage is an erasure; a column is `2^ℓᵢ` F-elements. `nᵢ` lookups of
   `O(log t)` steps: `≤ 2^19 · 2^6 · 2^5 = 2^30`.
4. For each level `i = 5 … 0`, with `f⁽ⁱ⁺¹⁾` the message of the unique nearby interleaved
   codeword of level `i + 1` (the clear polynomial at the bottom), recombined to K from its two
   F-coordinates:
   - compute `Enc(f⁽ⁱ⁺¹⁾)` on all `nᵢ` positions (naive evaluation of a degree-`< kᵢ` polynomial,
     `nᵢ·kᵢ` K×F products: `2^37` at level 0, `m = 31`);
   - compute the K-fold `C_s[j] = Σ_b eq(s,b)·C[b,j]` of every present column (`2^ℓ` K×F
     products each: `2^26`);
   - the **agreement set** `A = {j present : C_s[j] = Enc(f⁽ⁱ⁺¹⁾)[j]}`;
   - take the first `kᵢ` positions of `A` (if `|A| < kᵢ`, output `none`: it never happens under
     `μ < 1`), build the `kᵢ × kᵢ` Lagrange matrix `M[s, p] = L_p(s)` from positions `p` to the
     message points `s ∈ S` once (`W(s) = Π_p (s + p)`, `W'(p)`, batch inversion: `≈ 3k²`
     mults), and **erasure-interpolate each of the `2^ℓᵢ` rows** as `M · r|_P` (`k²` mults per
     row). The result is the level-`i` word `U⁽ⁱ⁾` (its message = `f⁽ⁱ⁾`).
5. `f⁽⁰⁾` is the packed witness `z`; the children's `(πᵢ, trᵢ, σᵢ)` are fixed bit regions of `z`
   (T for the trace, the proof read out of T by the shape, σ a W-region input). Output tag 1,
   `c₁ c₂`, the two signed proofs in the contract's layout.

The extractor verifies nothing. `E` is specified in Lean with Mathlib's `Lagrange.interpolate`
(or CompPoly's `CLagrange`) and the code defined as "evaluations on `D` of polynomials of degree
`< k`" (message = values on `S ⊂ D`, systematic), so no additive-NTT or novel-basis bridge enters
the Lean side at all: the prover's NTT is its private business.

### 4.3 Step count against `2^48 + 2^16·t` (**estimate**)

GF(2^128) multiplication on the machine: 3 `clmul` + 3 `clmulh` (Karatsuba), ≈ 8 XOR/shift for
the middle term, ≈ 10 for the reduction by `x^128 + x^7 + x^2 + x + 1`, ≈ 10 loads/stores:
**≈ 2^5 statements**. K×F product = 2 F-mults.

| step | m = 30 | m = 31 | m = 32 (not a node shape) |
|---|---|---|---|
| log index (sort), `2^11·t` with `t = 2^25 … 2^27` | inside the linear term | | |
| Merkle walks, all levels | `2^30` | `2^30` | `2^31` |
| `Enc(f⁽¹⁾)` at `n₀` points, `n₀·k₀·2` mults | `2^36` | `2^38` | `2^40` |
| K-folds of all columns | `2^30` | `2^31` | `2^32` |
| Lagrange matrix at level 0, `≈ 3k₀²` mults | `2^40.6` | `2^42.6` | `2^44.6` |
| **row interpolation at level 0, `64·k₀²` mults** | **`2^40` mults = `2^45`** | **`2^42` mults = `2^47`** | `2^44` mults = `2^49` |
| levels 1–5 (`16` rows, `k ≤ 2^15`) | `≤ 2^39` | `≤ 2^41` | `≤ 2^43` |
| output: `2 × (π + trace + σ) ≈ 2 × 2.3 MB` | `2^19.3` words | `2^19.3` | `2^19.4` |
| **total** | **≈ 2^45.2** | **≈ 2^47.3** | ≈ 2^49.3 |
| budget `2^48 + 2^16·t`, `t ≥ nᵢ·(2^{ℓ+1}+5)` | `2^48.0 + 2^41` | `2^48.0 + 2^42` | `2^48 + 2^43 = 2^48.04` |

`m = 30`: 7× margin; `m = 31`: 1.6×; `m = 32`: **over by 2.4×**. The verifier fixes the node
shape (a node proof of any other shape is rejected before any query), so `Computes` is proved for
`m ≤ 31` and the program's loops are bounded by shape constants; a tape that declares anything
else exits in `O(1)`.

### 4.4 The potential `μ`

v3's `KState` with leanerVM #143's shape: `μ L = Σ_{open groups G} π(G)` on a clean log and `1`
otherwise, where a group is one Fiat–Shamir phase of §1.3 (its squeezes `H(state ‖ i)`), `π(G)` is
the probability over the unasked squeezes that the phase closes on a bad challenge, and "clean"
excludes digest collisions, hits on in-play digests (commitment roots and tree nodes absorbed so
far) and a flipped group. `step` is the martingale argument plus the H charge; `final` is the
deterministic walk: an accepted run on a clean log of potential `< 1` has no bad challenge, so the
Ligerito induction (§4.2 step 4: `|A| ≥ (1−γ)n` by P2, `U` exists and `U_s = Enc(f⁽ⁱ⁺¹⁾)` by P1,
hence the fold of `U`'s message is `f⁽ⁱ⁺¹⁾` and `U`'s message satisfies the level-`i` claim by the
sumcheck rounds) reaches `z`, and the circuit theorem (§3.3) turns `z`'s satisfaction into
`Rel (acc vk) c (E c π L)`. Every digest the walk uses was found by lookup, so a second preimage
would be a logged collision (charged). This is the same structure the baseline's `KS` proof has;
what is new is the per-level induction and the circuit theorem.

### 4.5 Gao (CompPoly) versus error location + erasure decoding

CompPoly at the pin has, kernel-checked and axiom-free (issue #157, confirmed in the checkout):
`Gao.decode k D r` with `decode_eq_some` (returns the message polynomial when
`2·dist(r, encode D msg) ≤ n − k`), `decode_eq_none_iff`, and `decodeFrom k n g₀ g₁` (the
Euclidean stage on a supplied nodal polynomial and interpolant, `decode_eq_decodeFrom : rfl`).
Its domain is any `Domain F` of distinct points and its code is "degree `< k` in the monomial
basis evaluated on `D`" — exactly the code the Lean specification above uses, so **no
novel-basis bridge is owed in our setting** (the bridge in #157 is leanerVM's, whose code is
defined through the additive NTT). `BF128Ghash` is a proved `Field` instance (`ghashPoly_irreducible`,
certificate-based), so `decode_eq_some` instantiates at our F directly.

| | agreement set + erasure interpolation (chosen) | Gao per row (`decodeFrom` with the subspace vanishing polynomial) |
|---|---|---|
| what it needs from the soundness proof | MCA-UD (§1.4) gives `C` agrees with `U` on `A`, `|A| ≥ k`; the extractor computes `A` | the same MCA-UD (to know each row is within `γn < (n−k)/2` of `U`'s row); then `decode_eq_some` |
| level-0 cost per row | `k²` mults (`2^34` at `m = 30`, `2^36` at 31) | interpolant `O(n²)` + partial Euclid `O(n²)` with `n = 2k`: `≈ 6–8·k²` (**estimate**) |
| 64 rows, `m = 30` / `31`, in steps | `2^45` / `2^47` | `≈ 2^48` / `2^50` |
| fits `2^48 + 2^16·t`? | yes / yes (1.6×) | marginal / **no** |
| extra work the Gao route saves | the `Enc(f⁽ⁱ⁺¹⁾)` evaluation (`2^38`) and the fold comparison (`2^31`): negligible | — |
| Lean: specification side | `Lagrange.interpolate` uniqueness (Mathlib) | `decode_eq_some` (CompPoly, kernel) — a gift, but only on this side |
| Lean: refinement `ext ≡ E` | two nested loops over `k`, one batch inversion, one lookup walk: a few hundred statements, loop invariants over Lagrange sums | a machine implementation of `CPolynomial.xgcd` (quotient sequence, degree bookkeeping, division) proved equal to CompPoly's definition: a much larger refinement |
| failure mode | `|A| < k` ⇒ `none` (impossible under `μ < 1`) | `decode = none` when a row is off-radius (impossible under `μ < 1`) |

Verdict: **erasure decoding from the agreement set**, because the budget margin at `m = 31`
exists only for it, and because its machine program is the smaller refinement. Gao is the
fallback if review refuses the agreement-set computation inside `E`; it would then force `m = 30`
nodes (or a `2^50` fixed budget). Berlekamp–Welch is Gao with a linear system (`O(n³)` naive):
out. A quasi-linear erasure decoder (LANHC16's derivative formula with the additive NTT, which
CompPoly has for the tower field but not for GHASH; `2^37` steps at `m = 32`) is the only way to
reopen `m = 32` nodes and costs an NTT program with a proved step count: not recommended.

**The cancellation question.** Locating bad columns through "the combination row" costs, per
column, the probability that a bad column agrees with the combination by chance: `1/|field of
the combination|`, union-bounded to `n/|·|`. In this protocol the combination is the K-fold the
verifier already uses, and the term is inside P1 (`n/2^256`). One K-combination suffices; two
F-combinations (`n/2^256` as well) would be needed only if the folds were over F, which §1.3
excludes anyway.

---

## 5. Obstructions and verdicts

| Risk | Verdict | Argument | Cap or rule that binds; smallest change |
|---|---|---|---|
| FR-R1 (UD PCS within `proofCap` and `T_V` at node size) | **feasible** | §2: 745–776 KiB; `T_V` 35–110 ms (**estimate**) | `proofCap` would bind at `Σt ≈ 1,300` queries (rate 1/2 everywhere) or at `γ < δ/3` theorems; none needed |
| FR-R2 (every round `≤ 2^-120`) | **feasible, no grinding** | §1.3: tightest `2^-121.0` (skip), `2^-120.2` (positions); K-folds `2^-237` | `errorCap` forbids `k_s ≥ 8` and F-folds; nothing to change |
| FR-R3 (node extraction within fuel) | **feasible for `m ≤ 31` nodes**; infeasible at `m = 32` with quadratic decoding | §4.3: `2^45.2`, `2^47.3`, `2^49.3` | the fixed term `2^48` (the linear term is `≤ 2^43` here); `2^50` would admit `m = 32` |
| allowlist (not a numbered risk) | **rule-side** | `BF128Ghash`, the quadratic extension's certificate, and ArkLib's Johnson MCA are outside `ORG/.lake/rf/allowlist.txt` (AGENTS.md §6) | a core PR adding `CompPoly.Fields.Binary.BF128Ghash` (and, if route B is wanted, ArkLib's MCA module) to the organiser roots; else copy with provenance and strip code-changing attributes |
| `T_V` bias (Q11) | absorbed | the design fits with 1.6–5× margin at 50–300 ns per mult | none needed; M's measurement decides the wiring option |
| memory (FR-R5 input) | 2^17 tree leaves | §3.4 | prover cgroup 11 GB |

No kernel probe was needed: no claim above rests on a Lean fact that does not already exist,
except the ones listed as the entry's own work (circuit theorem, MCA-UD route A, the machine
program).

---

## 6. Drift table (protocol here vs the paper, and the repository where it differs)

| # | Here | Paper (2026-09-19) | Repository `48f4bfe` | Reason |
|---|---|---|---|---|
| D-1 | BLAKE2s everywhere; Merkle and Fiat–Shamir hashes are SROM queries; traces signed | SHA-256 | BLAKE3 | contract (FR-D4, V4-16) |
| D-2 | UD regime, 120 bits per query, `Secure` ladder, no OOD, queries 290/178/145/132/126/124 | Johnson list decoding, 100 bits, rates 1/2…1/32, 218/106/71/53/43, up to 17 bits grinding | `Secure`: 290/177/145/132/126/124; `Fast`: Johnson + 2-point OOD + 16-bit PoW | FR-D3 (no list decoding, no conjectures); `errorCap` |
| D-3 | fold challenges in K = GF(2^256), coordinate split | fold challenges in F | same as here (`FOLD_FIELD_LOG_Q = 256`, code switch) | P1 is `2^-110` over F |
| D-4 | no grinding | none in the main profile; query PoW in "slim" | fold 0; claim-batch 1, consistency 3–4 bits in `Secure`; 16-bit query PoW in `Fast/Slim` | every term already `≤ 2^-120`; 128-bit targets need their PoW, we do not |
| D-5 | consistency batching eq-structured over 9 coordinates | one `α` (App. C.2) | `128 − (log L + log ⌈log Q⌉)`: structured | powers would be `t/|F| = 2^-119.8` |
| D-6 | positions uniform with replacement, 12 per answer | uniform | stratified (one per depth-`cᵢ` subtree) | simplest Lean statement; same `(1−γ)^t` |
| D-7 | Merkle caps at depth `⌈log₂ t⌉`; binary trees | roots | caps | `π` and hashing in the node |
| D-8 | queries carry an 8-byte kind tag, `|q| ≡ 8 mod 16` | — | — | element alignment in the node circuit (§3.3) |
| D-9 | field: GHASH GF(2^128) as `BF128Ghash`; K as its quadratic extension (`u² + u + x⁻¹`, irreducibility by certificate) | GHASH | GHASH; `F256 = F128[u]/(u² + u + x⁻¹)` | kernel-checked field in CompPoly; allowlist to extend |
| D-10 | zerocheck: RS univariate skip `k_s = 6`, 7 pinned coordinates, degree-2 tail | same | AG (genus-95) skip on aarch64, degree-3 tail, per-site PoW | the AG code needs curve data and a second code family; `k_s = 7` would breach the cap |
| D-11 | lincheck by circuit walk; `c` skipped (`C = I`); IO by shift argument | same | same, plus a Nova-style matrix-claim accumulator for recursion | the accumulator trades a `2^21`-addition verifier cost for a folding scheme we need not formalise |
| D-12 | ring switching per paper App. B (slice-wise recombination, MBP evaluation of `B̂`) | App. B | capacity-free jagged ring switching with Frobenius twisting | the paper's is the smaller Lean object; verifier cost ≈ 3 k mults + 4·10^5 XORs |
| D-13 | node circuit: trace digest + WOTS + replay, regions T/H/W/M/L, shift arguments and aligned or gather wiring, no permutation argument | recursion not specified | tower with in-circuit Merkle hashing, 29 table types in 511 gate slots, Plonk-style permutation by GKR | SROM semantics (design §4.2); Lean budget |
| D-14 | GF(2^128) products as element rows (one constraint) | all-Boolean R1CS | same ("element tables") | 2,187 ANDs per product otherwise |
| D-15 | leaf start `s` in the clear; leaf shapes 2^16 / 2^17; nodes `m = 30/31` | batch sizes 2^10–2^18 | leaf `m = 32`, envelope `m = 29` | relation (`Wit.leaf s n`); 11 GB; fixed point |
| D-16 | straight-line decoding extractor with a step bound | none (IOP soundness only) | none | `Computes` |
| D-17 | soundness accounting: per-fresh-query potential, phases as groups, sum of open groups | round-by-round (RBR) | per-term minimum, no union bound | `KState` (`Security.lean`) |

---

## 7. Open questions for B and the orchestrator

1. **Wiring option** for M's operands (§3.3 (a) vs (b)): decided by M's measured `t_mul`
   against the +20 % hashing of (b). Default (a).
2. **Node shape**: `m = 30` or `31`, decided by B's exact AND count of the node circuit; the
   extractor budget and the ladder table are given for both.
3. **MCA-UD route** (§1.4): A (own elementary proof, BCIKS20/DP24 constant to be fixed in the
   lemma) or B (ArkLib's Johnson theorem through an allowlist extension). Ask the core now; the
   answer does not change parameters.
4. **Allowlist** for `BF128Ghash` and the quadratic-extension certificate (D-9): core PR or copy.
5. **Shared signature** between two children (design §4.1): saves ≈ 500 of 43 k compressions;
   not worth the dummy-query machinery. Not adopted.
6. **V4-A10** (textbook `KS`): the potential above is the `KState` route the plan keeps (FR-D0);
   nothing here depends on the form of `KS` beyond `KState`.
