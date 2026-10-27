# `flock-recursive`: entry blueprint (normative)

Status: phase 1 (B), revision 2 after the adversarial reviews (`reviews/BP-crypto-review.md`,
`reviews/BP-eng-review.md`; the fix pass is §10), 2026-10-27, for the tracks S-0 (interfaces),
L-field, L-piop, L-pcs, L-circ, L-ext, L-cert, P and H (`PLAN.md` §3). Contract: `.contract` at
core `15dac52` (`RecursionFast/Contract/*.lean` is authoritative; where this file and the
contract disagree, the contract wins and the disagreement is reported). Inputs: `PLAN.md`
(FR-D0 … D7), the phase-0 reports `T-theory.md`, `I-reuse.md`, `C-calibration.md`,
`M-measure.md`, `F-flock.md`, `K-kernels.md`, and S-A's `stages/S-A-JOURNAL.md` ("Normative
constants"). Decisions are `B-n`; T's decisions are inherited unless a `B-n` overrides them.
Evidence tags: **paper**, **estimate**, **kernel**, **measured**.

Every number below is computed by `logs/blueprint/sizes.py` (output `sizes.txt`) from the
formulas stated next to it, or quoted from a phase-0 report; Lean probes are under
`logs/blueprint/probe/` (`B8.lean`: the B-8 extractor shape; `BPeng.lean`: the claim's rationals,
`seq` costs, the 7-byte-tag alignment). `.contract/.lake/packages` is a symlink to the prebuilt
tree whose revisions match the manifest at `15dac52`.

---

## 0. Summary

A Flock-class batch-R1CS argument over GF(2) with a Ligerito commitment over F = GF(2^128) in the
unique-decoding regime, fold challenges in K = GF(2^256), BLAKE2s everywhere, and **recursive SROM
nodes**: a node proof commits to its two children's signed traces as the message slots of its own
BLAKE2s blocks, so hashing a trace (the trace digest) and reading it (the child verifier's replay)
are the same cells; it checks one WOTS signature per child and replays each child's verifier as
field-element rows. **Two verifier programs** exist: `L32` (the tree leaf, `n = 2^18`, `m = 32`)
and `P30` (every `m = 30` proof: the stream leaf and every node; a node's children are any two of
`{L32, P30}`). Knowledge soundness is certified through `KState` with per-fresh-query error
`εR = 15/2^124 = 2^-120.09`; the extractor decodes the node's commitment by erasure
interpolation from the agreement set and a novel-basis change, within `2^47.5 + 2^12 t` steps.

| Shape | `m` | `|π|` | trace items / hashed bytes / compressions | verifier F-products |
|---|---|---|---|---|
| `L32`: tree leaf, `2^18` compressions | 32 | 743,888 B = 726 KiB (71 % of `proofCap`) | 8,786 / 1,418,880 / 22,170 | ≈ 1.0·10^5 |
| `P30` as stream leaf (`2^16` compressions) or node | 30 | 690,368 B = 674 KiB (66 %) | 7,193 / 1,237,904 / 19,343 | ≈ 4.2·10^5 (node), fewer as a leaf |

`qV = 10,240` (margin 1.17× over `L32`'s 8,786); node circuit 56,435 of 65,536 blocks (86 %).

### 0.1 Decisions

| Id | Decision | Reason |
|---|---|---|
| **B-1** | **Tree leaves are single `m = 32` SNARKs of `2^18` compressions.** The stream leaf is `m = 30`. | The runner hashes the 64 statements `leafStmt (chainEnd sᵢ 2^18) 2^18` itself (`Tree.lean`); the leaf clause of `Rel` demands the chain, so a leaf made of signed segments is uncertifiable (`∀ vk`, design §2.2) and one of two fresh-query segment SNARKs exceeds `proofCap`. K measures the `m = 32` leaf at 3.73–3.86 s and 3.81 GB peak (K §3, §4.4): faster and smaller than 128 × 2^17. |
| **B-2** | **Nodes are `m = 30`, one shape, one program `P30`, one trace layout**, shared with the stream leaf (kind-selected public constants, §3). A node's children are any two of `{L32, P30}`; the child kind is a committed selector bit per slot, asserted equal to the child's header byte, and the templates that differ between the two child kinds are **muxed by rows** (both import sets exist; the selector zeroes one). Exact count 56,435 of 65,536 blocks (86 %); the fixed point of the self-replay is resolved by fixed region dimensions (§4.3). | K: the `m = 31` node (≈ 1.9 s) puts the stream link over its cap, so `m = 30` is a hard requirement; one program removes the per-variant circuits and the parent's dependence on the child's variant (BP-C-M7, BP-E-M3). If L-circ's exact `nodeLayout` overflows, the fallback is the enumeration of the occurring pairs `(L32,L32)`, `(P30,P30)`, `(P30,L32-free)` with a `decide` each (§9), never `m = 31`. |
| **B-3** | **Ladder of five levels**, rates 1/2 … 1/32, rows 64 then 16, `eᵢ = ⌊(nᵢ − kᵢ)/2⌋` (the full UD radius; B-5's lemma needs only `2e < d`), queries **290, 178, 145, 132, 126**, caps at depth 9, 8, 8, 8, 7, then the final `k₅` K-elements in the clear (16 at `m = 32`, 4 at `m = 30`). | Four levels make the final-level `Enc` cost `2 k₄ t₄` (270 k products at `m = 32`, BP-C-M3); six levels add 124 queries for nothing. Five levels put the final `Enc` at 4,032 products and every position phase at `≤ 2^-120.36`. |
| **B-4** | **F = BF64[y]/(y² + y + β), β = x^63; K = F[u]/(u² + u + α), α = β·y** (S-A's normative constants, Appendix A.1), through CompPoly's allowlisted `Ext` over the allowlisted `BF64`, two-`UInt64` fast twins, irreducibility by the trace criterion with kernel-evaluated traces. | No off-allowlist copy; `β = x^63` makes the reduction one shift pair (S-A), so an F product is three BF64 products. |
| **B-5** | **Proximity: own mutual correlated agreement for lines in the UD regime, stated over K-valued words and `C_K`**, with the bad-set bound a parameter `C_mca(n, k, e)` fixed by the proof that closes (required: `C_mca ≤ 2^60`), by the bivariate Berlekamp–Welch rank argument (§5.3). No ArkLib. | ArkLib's statements are in notation the source rule refuses and their closures are 42–45 k lines (I §2.5). Any polynomial constant is harmless over K (`≤ 2^-190` per fold round). |
| **B-6** | **Wiring: no permutation argument, no padding of trace items, no separate trace region.** The node's cube has regions H (BLAKE2s blocks), M (element rows), L (bit logic), P (public). A child's trace bytes are the message slots of its digest chain's H blocks, read by irregular matrix entries whose MLE the verifier evaluates with **eq tables** (one product per entry); M-internal patterns are **templates** with power-of-two strides (`O(template)` or `O(log)`), the BLAKE2s matrices by the circuit walk. | T_V is not binding (M: 4.3 M products in 205.9 ms); padding adds hashing B-2 cannot pay; the separate region's identification claim does not exist (BP-C-M6, BP-E-M2). |
| **B-7** | **The verifier is an interpreter of a straight-line IR (`VProg`)**; the two programs `gen L32`, `gen P30` are generated phase by phase; the node circuit's M and L rows are **compiled from the same IR**. `FRVIRSpec` states the meaning of each phase's op list and the query counts in closed form. | One compiler theorem instead of a hand proof of 10^6 rows; `runSeq` on a well-shaped trace is the straight line by construction. |
| **B-8** | **`E := fun c π L => (ext.run (extractorInput c π L) (fuel t)).bind decodeWit`.** `Computes` is termination within `fuel` and the output cap on every tape; `final` proves the program's output on good tapes. The program is written in `XIR` (counted loops with affine-in-`t` caps) compiled to `XStmt` with a cost theorem of the form `∃ n ≤ cost P t, Runs …`, counted on the compiled code. | Probed (`computes_Eof`); removes the farness direction and the rejection branches from the refinement (BP-E-M5/M6 fixed the cost model). |
| **B-9** | **Prover: std Rust, one `prover.s`, CPUID dispatch, AVX2 + VPCLMULQDQ-256 tier of record (K's kernels), optional zmm tier, portable for development**; no Flock crate; schedules as constants; templates built in `setup`. | PROVER.md §1; K §0, §5. |
| **B-10** | **`ε = εR = 15/2^124`; `δ = 0` (completeness through the witness-sending kind `W`, `P := encode`); `qV = 10,240`; `fuel t = 2^47.5 + 2^12 · t`** (`fuel_base = 2^47 + 2^46 = 211,106,232,532,992`, `fuel_per_word = 4,096`). Claim: `{"error": "15/21267647932558653966460912964485513216", "completeness_error": "0", "qV": 10240, "fuel_base": 211106232532992, "fuel_per_word": 4096}`. | §5.2's maximum `2^-120.36 + 2^-144 ≤ εR`; completeness is a statement about `V`, not `acc`, so the SNARK path's completeness is the harness's concrete check, not a certificate obligation (BP-E-M7; baseline D-5); extractor count `2^47.15` (§6.3), margins 1.27× to `fuel`, 1.8× to `B`. |

### 0.2 Drift from the Flock paper (2026-09-19) and repository (`48f4bfe`)

T §6's D-1 … D-17 stand, with:

| # | Here | Paper | Repository | Reason |
|---|---|---|---|---|
| D-2′ | five levels, 290/178/145/132/126, `e = ⌊(n−k)/2⌋`, final `k₅` K-elements in the clear | five levels, Johnson | six (`Secure m32`), `γ = δ/2 − 3/(δn)` | B-3, B-5 |
| D-9′ | F = BF64[y]/(y² + y + x^63), K = F[u]/(u² + u + x^63 y) | GHASH | GHASH, `F128[u]/(u² + u + x⁻¹)` | B-4 |
| D-13′ | node `m = 30`, one program `P30`, regions H/M/L/P, trace = H message slots, muxed child kinds, templates + eq-table irregular reads | — | tower, deferred accumulator, root discharge | B-2, B-6; `acc` has no root step, so a node replays its children's lincheck matrix evaluation with the BLAKE2s walk |
| D-15′ | tree leaf `m = 32`; stream leaf and node `m = 30` | `2^10`–`2^18` | leaf `m = 32`, envelope 29 | B-1, B-2 |
| D-18 | verifier = IR interpreter; circuit compiled from the IR | — | gate families | B-7 |
| D-19 | extractor = `decodeWit ∘ run`; UD decoding by agreement set, Lagrange rows and a novel-basis back-substitution | — | — | B-8 |
| D-20 | MCA-UD over K with a parametric constant | BCHKS25 `γn + 1` | same | B-5 |
| D-21 | ymm kernel tier, CPUID dispatch, std only | Apple M4 | AVX-512 compile-time | B-9 |
| D-22 | completeness certified through `W` (`P := encode`, `δ = 0`); honest SNARK proofs checked by the harness | — | — | B-10 |

---

## 1. Formats

All integers little-endian; F and K elements, digests and positions as Appendix A.1–A.2.

### 1.1 The proof `π`

Three kinds, told apart before any query:

- **`W`** (witness-sending): `π = WitnessSending.encode w` exactly (the library's; tag word
  `0`/`1`); decided by `V` with no query as `Rel` itself (§3); the native prover never emits it.
- **`L32`**, **`P30`**: `π = hdr ‖ body`, `|π| = piSize kind` exactly (A.3); any other length is
  rejected with no query.

```
hdr (48 B) = kindByte(1) ‖ m(1) ‖ zero(14) ‖ pub(32)
  kindByte  0x4C 'L' (L32), 0x50 'P' (P30 as a leaf), 0x4E 'N' (P30 as a node)
  m         32 (L32), 30 (P30)
  pub       leaf kinds: s (the chain start); node: zero
then  L32:        enc64 n ‖ h ‖ zero(8)   (48 B; n = 2^18, redundant and checked)
      P30 leaf:   enc64 n ‖ h ‖ zero(24)  (64 B; n = 2^16)
      P30 node:   c₁ ‖ c₂                  (64 B)
then  body = PIOP messages ‖ cap₀ … cap₄ ‖ final message ‖ columns ‖ siblings   (A.3's offsets)
```

| Part | `L32` | `P30` |
|---|---|---|
| header + statement fields (A.3) | 48 + 48 = 96 | 48 + 64 = 112 |
| PIOP messages (A.3) | 10,864 | 13,456 |
| caps `(512 + 256 + 256 + 256 + 128) × 32` | 45,056 | 45,056 |
| final message `k₅ × 32` | 512 | 128 |
| columns `Σ tᵢ rowsᵢ 16 = 290·1,024 + 581·256` | 445,696 | 445,696 |
| siblings `32 Σ tᵢ (depthᵢ − capᵢ)` | 7,552 → 241,664 | 5,810 → 185,920 |
| **`piSize`** | **743,888 (726 KiB, 71 %)** | **690,368 (674 KiB, 66 %)** |

`P30`'s `piSize` is the same for its leaf and node use: the leaf carries the node-only messages
(Lr, E, B′: 2,880 B) as zeros (§3).

### 1.2 Queries and the hashed trace

Query = `tag ‖ payload`, `|payload| ≡ 0 mod 16`. **The seed's tag is 7 bytes, every other tag
8 bytes** (A.2), so in the hashed stream `0x54 ‖ traceBytes tr` (`Contract/Signature.lean`) the
first item is `0x54 ‖ enc64 |q₀| ‖ tag₇ ‖ payload₀ ‖ a₀` with `payload₀` at offset 16, and every
later item `enc64 |q| ‖ tag₈ ‖ payload ‖ a` has 16-byte-aligned length and payload at its offset
16: **every payload element and every answer of every item is at an offset `≡ 0 mod 16` of the
hashed stream** (kernel-probed, `BPeng.lean` §4). The stream's 16-byte element `e` is message slot
`4 + e mod 4` of H block `⌊e/4⌋` of the digest chain (§4.3).

| Kind | Query | Bytes | Answer used as |
|---|---|---|---|
| seed | `"FRSEED0" ‖ vk ‖ c ‖ hdr(48)` | 7 + 112 = 119 | state `st₀` |
| absorb | `"FRABS000" ‖ st ‖ msg` | 40 + `|msg|` | new state |
| squeeze | `"FRSQZ000" ‖ st` | 40 | new state and challenge source |
| Merkle node, level `i` | `"FRMNOD" ‖ i ‖ 0 ‖ left ‖ right` | 72 | the parent digest |
| column, level `i` | `"FRMCOL" ‖ i ‖ 0 ‖ column` | 8 + 1,024 / 8 + 256 | the leaf digest |

Challenges: F = bytes `0 … 15` of a squeeze answer (each value has `2^128` answers); K = all 32
bytes; positions: `⌊256/b⌋` indices of `b = log₂ nᵢ` bits per answer (A.2). **One squeeze serves
one phase** (BP-C-M2); a phase of `c` F-coordinates uses `⌈c/2⌉` squeezes (two coordinates per
answer, bytes `0…15` and `16…31`).

| Shape | FS items | columns | siblings | **items** | hashed bytes | compressions |
|---|---|---|---|---|---|---|
| `L32` | 363 | 871 | 7,552 | **8,786** | 1,418,880 | 22,170 |
| `P30` | 512 | 871 | 5,810 | **7,193** | 1,237,904 | 19,343 |

`qV = 10,240` (`queries_le`, a closed-form count of `gen`, §3); the trace cap of `acc` is met by
every honest trace with margin 1.17×.

### 1.3 What each kind proves; the child proof as a function of its trace

- leaf kinds: `c = leafStmt h n`, `n = 2^(m−14)`, the SNARK proves `chainEnd s n = h`; witness
  `.leaf s n`;
- node: `c = nodeStmt c₁ c₂`, the SNARK proves `acc vk c₁ p₁ ∧ acc vk c₂ p₂` for the committed
  `p₁, p₂` (§4.3); witness `.node c₁ c₂ p₁ p₂`;
- `W`: `Rel` directly.

A child's `πᵢ` is not committed separately: `πᵢ = reassemble kindᵢ trᵢ` (A.4): the header from the
seed payload, PIOP messages and caps from absorb payloads, the final message from its absorb,
columns from column queries in query order, siblings from Merkle-node queries (the sibling is the
half **not** equal to the previous answer; A.4 fixes the rule by the position bit read from the
positions' squeeze answers, which are in the same trace). `σᵢ` is an L-region value (§4.3).

### 1.4 The extractor's output

`witWords` (`Library/Words.lean`): a node of two `L32` children is `≈ 629,759 = 2^19.3` words of
`outCap = 2^24`; a leaf 6 words; `W` the copied proof.

---

## 2. The protocol

### 2.1 Fields, code, challenges (values in A.1–A.2)

F, K as B-4. **The code.** `D = {D[j] : j < n}`, `D[j] := (j, 0) ∈ BF64 × BF64 = F` (the word
`j` as a BF64 element: the F₂-span of `1, x, …, x^(log n − 1)`; every level has `n ≤ 2^20`);
`Wᵥ(X) := Π_{a < 2^v}(X − D[a])`, `Ŵᵥ := Wᵥ / Wᵥ(D[2^v])` (LCH14's normalised subspace vanishing
polynomials), `X_x := Π_{v : bit v of x} Ŵᵥ` (degree `x`). **`Enc_k(c)[j] := Σ_{x<k} c_x X_x(D[j])`**
over K for `c ∈ K^k` (`C_K := Enc_k(K^k)`, `C_F` its F-valued words = `Enc_k(F^k)`): the message is
the vector of **novel-basis coefficients**, which is how a row of the committed matrix (the
hypercube values of the multilinear polynomial on its low variables) is encoded. Facts (`FRRS`):
distance `n − k + 1`; `X_x(D[j]) = 0` for `j < 2^msb(x)` (block-triangularity: coefficients from
values on `D[0…k)` by back-substitution, `O(k²)`); the tensor identity `Σ_x eq(r, x) X_x(D[j]) =
Π_v (1 − r_v + r_v Ŵᵥ(D[j]))` (`O(log k)` consistency weights, BP-C-M4); `Ŵᵥ(D[j])` for all `v, j`
from the subspace structure. The prover computes `Enc` with the additive NTT; Lean never does.

### 2.2 The ladder (`sizes.py`; `kᵢ₊₁ = kᵢ/8`, `nᵢ = 2^(i+1) kᵢ`, `eᵢ = ⌊(nᵢ−kᵢ)/2⌋`, `tᵢ =
⌈120.25 / −log₂(1 − eᵢ/nᵢ)⌉`, cap `⌈log₂ tᵢ⌉`)

| level | `ρ` | rows | `log₂ k` (30 / 32) | `log₂ n` | `e/n` | `t` | `(1 − e/n)^t` | positions/answer | squeezes | siblings/query | cap |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 1/2 | 64 | 17 / 19 | 18 / 20 | 1/4 | 290 | `2^-120.36` | 14 / 12 | 21 / 25 | 9 / 11 | 2^9 |
| 1 | 1/4 | 16 | 14 / 16 | 16 / 18 | 3/8 | 178 | `2^-120.70` | 16 / 14 | 12 / 13 | 8 / 10 | 2^8 |
| 2 | 1/8 | 16 | 11 / 13 | 14 / 16 | 7/16 | 145 | `2^-120.36` | 18 / 16 | 9 / 10 | 6 / 8 | 2^8 |
| 3 | 1/16 | 16 | 8 / 10 | 12 / 14 | 15/32 | 132 | `2^-120.45` | 21 / 18 | 7 / 8 | 4 / 6 | 2^8 |
| 4 | 1/32 | 16 | 5 / 7 | 10 / 12 | 31/64 | 126 | `2^-120.41` | 25 / 21 | 6 / 6 | 3 / 5 | 2^7 |
| final | — | — | `k₅ = 4 / 16` K-elements in the clear | | | | | | | | |

A level's fold of its `ℓᵢ` row variables (6, then 4) with K challenges gives a K-vector of `kᵢ`
elements, laid out as the next level's `16 × kᵢ/8` F-matrix by the **coordinate split** (A.2: the
F-element at index `2x + c` is coordinate `c` of K-element `x`; the row is `(x mod 8)·2 + c`, the
column `x div 8`; the running claim `Σ eq(r,x) g(x) = v` over K becomes `Σ eq((r, z_c),(x,c)) g_c(x) =
(1 − z_c) v₀ + z_c v₁` with `z_c` the next level's first fold challenge).

### 2.3 Round by round (the verifier's reading order)

Phases carry the names of the error table (§5.2); a sumcheck round sends 3 (degree ≤ 3) or 2
coefficients, is checked `g(0) + g(1) = claim` and folded at the challenge. A **univariate round**
collapses the block's 6 low position bits, which range over the skip set `S` (A.1): it sends the
degree-≤127 polynomial's values on the 128 points `S ∪ Λ` (minus what the check determines) and is
charged `127/2^128`. Items in the `P30` program that the leaf use does not need are present with
zero messages and vacuous checks (kind-selected public constants).

0. `seed(vk, c, hdr)`; `absorb(statement fields)`.
1. **Commit**: `absorb(cap₀)`.
2. **Z** zerocheck of `(A z)∘(B z) = C z` over the blocks, `A = Sel ⊗ A₀`, `B = Sel ⊗ B₀`, `C = Sel
   ⊗ I` (`Sel` = the kind's block selector): **Z1** `r ∈ F^(m−6)`, 7 pinned coordinates (A.1), the
   other `m − 13` from `⌈(m−13)/2⌉` squeezes; **Z2** `absorb(P^{ab}, P^z)`, `λ ← squeeze` (F);
   **Z3** `m − 6` rounds of degree 3; result `â, b̂, ẑ_Z`.
3. **Lc** lincheck of `â, b̂`: **L1** `α ← squeeze`; **L2** 9 rounds of degree 2 over the block's
   high position bits, then **L3** the univariate round over `S`; the verifier evaluates `Â₀, B̂₀`
   by the circuit walk, times `Sẽl`; result `ẑ_L`.
4. **Sh** shift arguments (leaf: the chain; node: the two digest chains), range-restricted (§4.1):
   **S1** `τ` (`m − 14 + 8` coordinates); **S2** one round of degree 3 (eq · range · difference)
   and **S3** a univariate round; result `ẑ_S`.
5. **IO / public patterns** (§4.1, §4.3): **I1** `θ` (`≤ 25` coordinates); **I2** a univariate
   round; result `ẑ_I` and the public-pattern checks (`one = 1`, counters, flags, chain starts,
   padding, `P`), each a sum the verifier computes itself.
6. **Lr** (node): Spartan over the L rows (`2^15`): **Lr1** point (15), zerocheck rounds (degree
   3); **Lr2** batching `κ_L`, lincheck rounds (degree 2); the verifier evaluates `Ã_L, B̃_L, C̃_L`
   by sparse sums.
7. **B** batching of the ≤ 8 `ẑ` claims by `κ`: **B1** `κ ← squeeze`; **B2** the batching sumcheck:
   `m` multilinear rounds (degree 2) and one univariate round (the claims have different skip
   coordinates).
8. **R** ring switching (paper App. B.2–B.3): `absorb(s_v)` (128 F); **R1** `r″` (7 coordinates);
   `m − 7` rounds of degree 2; the verifier's MBP evaluation; result `f̂(r_f)`.
9. **E** (node) the element R1CS over the M rows (`N_M = 2^21`): **E1** point (21 coordinates),
   zerocheck rounds (degree 3); **E2** batching `κ_E`, lincheck rounds over `m′ = 23` variables
   (degree 2); the verifier evaluates `Ã_M, B̃_M, C̃_M` by templates (§4.4).
10. **B′** batching of the `f̂` claims by `κ′`.
11. **P** Ligerito, levels `i = 0 … 4`: **P1** `ℓᵢ` fold rounds (K challenge each, 3 K
    coefficients); `absorb(capᵢ₊₁)` or, after level 4, `absorb(final message)`; **P2** positions
    (`⌈tᵢ/⌊256/log₂ nᵢ⌋⌉` squeezes); the column and Merkle-node queries of every position; **P3**
    `κ_c ← squeeze` (9 F coordinates), the `tᵢ` consistency claims `fold(column_j) =
    Enc(f⁽ⁱ⁺¹⁾)[j]` batched with eq-structured coefficients into the next level's claim, each
    `Enc(f⁽ⁱ⁺¹⁾)[j]` an evaluation of `f⁽ⁱ⁺¹⁾` at `(Ŵᵥ(D[j]))_v` folded by the tensor weights.
    At level 4 the verifier evaluates `Enc₄(final)[j]` directly (`k₅` K×F products per position).
12. Accept iff every check passed.

### 2.4 Parameters

| Name | Value | Where |
|---|---|---|
| `m₀` | 14 (`2^14` positions per block) | spartan-srom's block |
| skip | `k_s = 6`, `S`, `Λ` (64 points each, A.1); pinned `ρ₁…ρ₇` (A.1) | Z2/L3/univariate rows `127/2^128` |
| shapes | `L32`; `P30` (leaf and node) | B-1, B-2 |
| ladder | §2.2 | B-3 |
| `N_M, N_L` | `2^21` rows, `2^15` rows | §4.3 |
| `qV`, `εR`, `δ`, `fuel` | 10,240; `15/2^124`; 0; `2^47.5 + 2^12 t` | B-10 |

---

## 3. The verifier `V vk c π`

```
V vk c π :=
  match kindOf π with
  | W      => ret (decide (RelW vk c π))        -- no query; §3.3
  | none   => ret false                         -- |π| ≠ piSize or bad kind byte
  | some k => if ¬ stmtOk k c π then ret false  -- c = leafStmtF h n or nodeStmtF c₁ c₂
             else runIR (gen k) (vk, c, π)
```

`gen k : VProg` (A.5) is generated phase by phase (`genSeed`, `genZ`, `genLc`, …, `genP i`); `runIR`
is the `OProg` interpreter (an `ask` op issues a query and binds the answer; every other op is
pure; an `assert` that fails returns `false`). `P30`'s program takes the kind byte as a public
selector: the node-only phases (Lr, E, B′, the second digest chain, the WOTS and `hashStmt` ops)
are evaluated with the kind-selected public constants (`Sel`, the templates, the matrices are the
leaf's or the node's; for the leaf they are empty and the checks are `0 = 0`), so the leaf and the
node have **the same op list and query sequence**. `stmtOk` is also an op (`hashStmt`) of the
replay (BP-C-M1), so `V = parse; stmtOk; runIR` and the replay covers `stmtOk`.

**`FRVIRSpec`** (BP-E-M4): for each phase, `semIR (genPhase …) st = …` states the phase's
equations (the round checks, the Merkle-path consistency, the consistency sums, the final
evaluations) as Lean propositions over the answers; `queries_le : ∀ H c π, ((V vk c π).queries
H).length ≤ 10240` by the closed-form count `Σ_phase count_phase` (`simp`, no kernel evaluation
of `gen`); `runSeq_eq_runIR`: on a trace whose query bytes are the shape's sequence, `runSeq tr (V
…) = some true ↔ semIR (gen k) (answers tr) = accept`.

### 3.1 Operation counts (one run; `sizes.py`)

| Work | `L32` | `P30` node |
|---|---|---|
| column folds `Σ tᵢ rowsᵢ` K×F products | 46.6 k (F: 2 each) | same |
| final `Enc₄` at `t₄` positions (`2 k₅ t₄`) | 4.0 k | 1.0 k |
| eq tables, K arithmetic, consistency tensor weights `Σ tᵢ (log kᵢ + 9)` | ≈ 15 k | ≈ 15 k |
| univariate rounds (Z2, L3, S3, I2, B2) Lagrange at 128 points | ≈ 20 k | ≈ 25 k |
| sumcheck rounds | ≈ 0.5 k | ≈ 1 k |
| ring switch MBP `(m−7)·128` F + `(m−7)·2^14` conditional XORs | 3.2 k + 4.1·10^5 XOR | 2.9 k + 3.8·10^5 XOR |
| walks `Â₀, B̂₀` (two points) | 1.2·10^5 XOR | 1.2·10^5 XOR |
| node: `evalM`: irregular entries `2 × 138,509` × 1 product + eq tables (`2 × 22,170 + 2^14`) + templates + two more walks | — | ≈ 3.4·10^5 F + 1.2·10^5 XOR |
| node: `Ã_L …` sparse sums | — | ≈ 2^15 F + 2^18 XOR |
| **F-products** | **≈ 1.0·10^5** | **≈ 4.2·10^5** |

### 3.2 `T_V` (**estimate**; M §7.2: 47 ns inline / 62 ns boxed per product, ×1.3 for the tower;
XOR 8 ns)

Root check (`P30` node): trace digest: the compiled `acc` runs the contract's spec BLAKE2s over a
`List UInt8` of 1.24 MB, ≈ 0.75 µs per compression on the VM (F1 RESULT), ≈ 15–25 ms on the
runner (BP-E-m4); `SigOk` 0.3 ms; parsing 2 ms; products `4.2·10^5 × 70 ns = 30 ms`; XORs 10 ms;
interpreter overhead ≤ 2× on the arithmetic. **≈ 90–120 ms against 205.9 ms.** An early probe
(stage S-B: a synthetic `P30`-size program in the compiled interpreter) replaces this estimate.

### 3.3 The `W` kind and DoS

`RelW` is the baseline's `C`/`N` decision (`SpartanSromNode`): a leaf recomputes `chainEnd s n`
(`n ≤ chainCap`) with the library's fast twin (`Library/Fast.lean`), a node checks `accWith V` on
both children (`V` is defined by well-founded recursion on `π.size`, a child proof being a proper
substring; `accWith` restates `Submission.acc` with `V` inlined, `FRSubmission.acc_eq`). Cost:
`acc`'s first conjunct is `|π| ≤ proofCap`, so a `W` node's children's traces total ≤ 1 MiB (≤
16 k compressions) and a `W` leaf costs ≤ `2^20` compressions ≈ 0.17 s with the fast twin: within
the DoS column's `10 · T_V`. The harness's DoS inputs carry no valid signature, so no `W` node
passes `SigOk` anyway (BP-E-m3).

---

## 4. The circuits

Batch R1CS over GF(2) in Flock's form: `z ∈ GF(2)^(2^m)` is `2^(m−14)` blocks of `2^14`
positions; `A = Sel ⊗ A₀`, `B = Sel ⊗ B₀`, `C = Sel ⊗ I`; shift claims and public-pattern claims
linear in `z`; the node adds the element R1CS over `f = pack z` and the L R1CS. Block layout
(A.6): slots 0–1 `h_in`, 2–3 `h_out`, **4–7 the 512 message bits**, slot 8 the words `t_lo`,
`t_hi = 0`, `f0`, `f1 = 0` and the constant `one` (bit 1,152), gates from bit 1,280 (leanerVM's
circuit as in spartan-srom, 14,720 gates, re-based). `A₀(k,·), B₀(k,·)` for a gate position are
its forms, for an input `(var k, var one)`, for a constant `(one, one)` or `(0, 0)`, for an output
`(out form, one)`. **`one = 1` is a public-pattern claim**, not a row (BP-C-M5).

**Public-pattern claims** (one mechanism for every per-block public constant): for a slot or bit
`s` and a public function `pat_s : block → GF(2)^w`, the claim `Σ_i eq(θ, i) · z[blk i, s] =
Σ_i eq(θ, i) · pat_s(i)`; the right side is computed by the verifier in `O(N_blocks)` F-additions
(`pat` is 0/1-valued: `Σ_{i : pat(i) = 1} eq(θ, i)`, an eq-table sum, `≤ 2^16` products per
claim). Claims used: `one` (1 on used blocks), `t_lo` (the counter words, bit by bit: 32
patterns, or one claim on the 32-bit word's MLE with `pat` word-valued), `f0`, the chain starts
(`h_in = h0` on the first block of each chain), the message padding of each chain's last block,
`Sel`'s complement blocks all zero, `P`.

### 4.1 The leaf circuit (`FRLeafCircuit`)

`2^(m−14)` chain blocks (spartan-srom's, re-based: `h_in = h0`, message `0x43 ‖ dᵢ ‖ 0^31`, `t_lo
= 33`, `f0 = 0xFFFFFFFF`, output `dᵢ₊₁`; here `h_in, t, f` are public-pattern claims, not block
constants, so the block is the stream block of §4.2 with a constant pattern), plus **Sh**: `∀ i <
n − 1: out(i) = in(i+1)` as `Σ_i eq(τ, i) · R(i) · (z[blk i, 256…511] − z[blk i+1, 520…775]) = 0`
over the 256 bits (collapsed by a univariate round), `R` the range indicator of `[0, n−1)`
evaluated by the verifier (`FRShift.shift_sound`, degree 3); **IO**: `in(0) = s`, `out(n−1) = h`
(two evaluation claims at fixed blocks).

```
leaf_sound : ∀ z s h, Boolean z → (∀ i < 2^(m−14), z[blk i, one] = 1) → (∀ i, Holds blockR1CS (z ∘ blk i)) →
  Patterns z → ChainLinks z → IOHolds z s h → chainEnd s (2^(m−14)) = h
```

(`Patterns` = the public-pattern equalities; `block_sound` with `one = 1` explicit.)

### 4.2 The stream block, the digest chain, the WOTS check, the statement check

The **stream block** is the compression circuit with `h_in` (256), message (512), `t_lo`, `f0` as
inputs (`FRBlockStream.block_sound`: a Boolean block with `one = 1` carries `compress h_in m
(t_lo) f0 0` in slots 2–3). The **digest chain** of a byte string `B` (`|B| = 1 + Σ item bytes`,
`N = ⌈|B|/64⌉`): `h₀ = h0`, `hᵢ₊₁ = compress hᵢ Bᵢ (64(i+1) or |B|) ([i = N−1]·0xFFFFFFFF) 0`,
`traceDigest tr = le h_N` (`blake2s_chain`, kernel). Block `i` of a chain holds `Bᵢ` in slots
4–7; the message of block `i` of chain 1 is stream bytes `[64i, 64i+64)`, and **the node reads
child 1's trace element `e` at element address `Hbase/128 + ⌊e/4⌋·128 + 4 + e mod 4`**, child
2's at `(N₁ + ⌊e/4⌋)·128 + …`. The chains occupy blocks `[0, N₁)` and `[N₁, N₁ + N₂)` with `N₁ =
N₂ = 22,170` (both sized for an `L32` child; a `P30` child's shorter stream is zero-padded and
its final block's `t_lo`/`f0` pattern is kind-selected). **WOTS** (`FRWots`): 133 chains × 3
selector steps + the 67-block leaf hash + 32 path blocks = 498 blocks per child, as IR ops
(`hashStep` blocks wired by element equalities; digits, selectors and index bits in L).
**`hashStmt`** (BP-C-M1): per child 2 blocks (a leaf child's 41-byte `leafStmt` input uses one;
a node child's 65 bytes two), output equal to the seed payload's `cᵢ`, inputs wired to the
header fields read from the seed payload; `wots_sound : … → SigOk vk m σ = true`;
`hashStmt_sound : … → cᵢ = leafStmt hᵢ nᵢ ∨ cᵢ = nodeStmt c₁ᵢ c₂ᵢ` as the kind says.

### 4.3 The node circuit (`FRNodeCircuit`): regions, the fixed point, counts

| Region | Base (blocks) | Content | Blocks |
|---|---|---|---|
| **H** | 0 | chain 1 `[0, 22,170)`, chain 2 `[22,170, 44,340)`, `hashStmt` 4, WOTS 996, 8 spare; all-zero blocks elsewhere (they satisfy the block R1CS with `one = 0`, excluded by the `one` pattern on used blocks only) | **45,348** |
| **M** | 49,152 (`3·2^14`) | the element rows, `N_M = 2^21` allotted (`2^20.4` used): per child slot the templates of §4.4 | 10,959 used of 16,384 |
| **L** | 61,440 | bits: the two signatures (4,772 B each), WOTS digits/selectors, position bits as bit-elements `(b, 0, …, 0)` (7,552 × 128 per slot), kind selectors, `N_L = 2^15` rows | 127 |
| **P** | 65,535 | `vk ‖ c₁ ‖ c₂` (768 bits) at its start, then zeros | 1 |
| **total** | | | **56,435 of 65,536 (86 %)** |

**The fixed point** (BP-E-M3). The `P30` program replays a `P30` child, whose own verifier
evaluates `evalM` over the templates of *its* children. The dependence is cut by fixing the
dimensions as constants: `N_M = 2^21`, `N_L = 2^15`, two child slots each sized for the larger
child kind (`L32` trace of 22,170 blocks; imports and Merkle rows for both kinds, muxed), E has
21 zerocheck rounds whatever the use. `gen P30` is then a function of `(ladder30, ladder32, N_M,
N_L, nodeLayout)` alone, and the stage theorem `rows (compile (gen P30)) ≤ N_M` (`decide` on the
closed-form count) closes the loop. The row count is computed for the worst child kind per slot
(`P30`: its `evalM` replay dominates).

**Row count per child slot** (`sizes.py`): imports (muxed, both kinds) 138,509 (column elements
46,624 + 13,936; sibling halves and answers `6 × 7,552` + `6 × 5,810`; FS fields); folds 54,841;
final `Enc₄` 4,032; Merkle selection `2 × 7,552`; skip Lagrange ≈ 20 k; eq/K/tensor ≈ 15 k;
MBP 3.2 k; sumchecks 1 k; lincheck replay 65,536 (two eq tables and products); the child's own
**`evalM` replay** 374,126 (one row per irregular entry of its two slots + eq tables); digest and
constant equalities ≈ 10 k: **≈ 701 k rows per slot, 1,402,696 = 2^20.4 per node**.

**What the circuit asserts of child slot `i`** (the `replay` IR, compiled to M + L rows): (1) the
kind selector `sᵢ ∈ {0,1}` (L bit) equals the kind byte of the seed payload's `hdr`; (2) every
item's `enc64 |q|`, tag and padding equal the kind's constants (muxed by `sᵢ`); (3) the FS chain:
the state field of item `k+1` equals the answer of item `k`; (4) the seed payload holds `vk`, `cᵢ`
(the `P` region's elements) and `hdrᵢ`; (5) `hashStmt`: `cᵢ` is the statement of `hdrᵢ`'s fields;
(6) `V`'s arithmetic on the answers and proof fields (every op of `gen kindᵢ` as rows; an F
product 1 row, a K product 3 + 2 linear, an inverse 1 row with the inverse a witness, an `assert
eq` 1 linear row, a position bit a bit-element from L); (7) Merkle steps `cur = left + b (right −
left)` per half (2 rows), cap comparison; (8) the size constants `|πᵢ| ≤ proofCap`, `|trᵢ| ≤ qV`,
`|q| ≤ queryCap` (`decide` once per kind); (9) `SigOk vk (traceDigest trᵢ) σᵢ`: chain `i`'s final
output equals the WOTS message, §4.2's rows.

```
node_sound : ∀ z vk c₁ c₂, Boolean z → (∀ i ∈ usedH, z[blk i, one] = 1) → HHolds z → Patterns z vk c₁ c₂ →
  ShHolds z → LrHolds z → EHolds (pack z) →
  let p₁ := FR.readSigned 1 z; let p₂ := FR.readSigned 2 z
  accWith V vk c₁ p₁ = true ∧ accWith V vk c₂ p₂ = true
```

`FR.readSigned i z := ⟨reassemble kindᵢ trᵢ, trᵢ, σᵢ⟩` with `trᵢ` the items parsed from chain
`i`'s message slots (the same map the extractor implements, A.4). Proof: (a) `HHolds ∧ Patterns ∧
ShHolds` ⇒ each chain computes `traceDigest trᵢ` (`blake2s_chain`, `block_sound`, `shift_sound`)
and the WOTS/`hashStmt` blocks compute their hashes; (b) `EHolds ∧ LrHolds` ⇒
`FRVIRCircuit.compile_sound`: `semIR (gen kindᵢ) (vk, cᵢ, πᵢ, answers trᵢ) = accept`, `wots_sound`,
`hashStmt_sound`; (c) `runSeq_eq_runIR` with (2)–(3) (the trace's query bytes are the sequence);
(d) the constants (8). `node_complete`/`nodeWitness` are controls, not certificate obligations
(B-10).

### 4.4 Wiring: templates and irregular reads (B-6)

Rows `rowIx = Mbase + slot·2^20 + tplBase + inst·2^a + j`. Entry kinds and their MLE evaluation
(`evalM`, with `evalM_eq : evalM τ σ = Σ_{(r,c) ∈ nnz} eq(τ,r) eq(σ,c)` proved generically from
the per-kind lemmas):

- **template-internal** (column in an aligned region of the same instance): `eqInner(τ_inst,
  σ_inst) · Σ_{(j,j′) ∈ tpl} eq(τ_j, j) eq(σ_j, j′)`: `O(log)` + `O(|tpl|)` once per template
  (`tpl_mle`);
- **shift-structured** (eq-tree parents `j ↦ j >> 1`, Horner/MBP chains): transfer matrices,
  `O(log)` (`shift_mle`);
- **lincheck replay**: `B_M` restricted to the rows `eqrow[k] · (A₀ eqcol)[k]` is `A₀` at an
  aligned base: `eqInner · Â₀(τ_j, σ_j)` by the **walk** (`walk_eq_sum`);
- **irregular** (a column in a chain's message slots, or in L): `Σ_e T[e] · eq(τ, row(e))` with
  `T[e] := eq(σ_blk, ⌊e/4⌋) · eq(σ_slot, 4 + e mod 4)` from two **eq tables** (`eq_mle` splitting:
  `eq(σ, blk·128 + slot) = eq(σ_hi, blk) · eq(σ_lo, slot)`), and `eq(τ, row(e))` from the row
  template's tables: **one product per entry** plus tables of `N₁ + N₂ + 2^14` products
  (`irregular_mle`; this replaces the incremental rule, BP-E-m5). Entries: 138,509 per slot.

The two chains are contiguous in block index, so no identification claim exists; the `t_lo`,
`f0`, padding and `one` patterns are public-pattern claims over the two ranges (each a sum the
verifier computes).

### 4.5 Counts that bind (`sizes.py`; **kill test** of B-2 = `nodeLayout`'s `decide`)

| Quantity | value | bound | margin |
|---|---|---|---|
| H blocks | 45,348 | — | — |
| M rows per node | 1,402,696 = `2^20.42` | `N_M = 2^21` | 1.50× |
| blocks used | 56,435 | 65,536 | 1.16× |
| `L32` trace items | 8,786 | `qV = 10,240` | 1.17× |
| `L32` `|π|` | 743,888 | 1,048,576 | 1.41× |

If L-circ's exact `nodeLayout` overflows 65,536: first the tightening (shared lincheck-replay eq
tables between slots: −2^15 rows; skip-Lagrange denominators as constants: −10 k; `hashStmt` of
leaf children as one block), then B-2's enumeration fallback.

---

## 5. The potential `μ`, knowledge soundness, completeness, controls

### 5.1 Shape (`FRSoundness*`)

As spartan-srom's (`SoundnessKSBase` Part A, `muG_step`): `μ L = [Bad L ∨ Esc L] + Σ_{chains on the
frontier} φ(chain)`; a chain is a maximal transcript path (seed → absorb/squeeze …, `Matches`
re-parameterised by A.2's kinds); **Bad** = a digest collision in `L`, a fresh answer equal to any
16-byte-aligned 32-byte window of any logged query or answer (in-play digests: cap entries, Merkle
nodes, states; BP-C-m1), a repeated query, a flipped group; `φ` charges every open phase its bad
probability over the unasked squeezes (martingale across a multi-answer phase, `extCount_split`).
`step` = one lemma per row of §5.2 from the exact fiber counts (`card_chF_fiber = 2^128`,
`card_chK_fiber = 1`, `card_idx_fiber`) plus the H row; `final` = §5.4.

### 5.2 Per-fresh-query error table (`P30` node; `L32` is a subset with `m = 32`). One squeeze
serves one phase, so no sharing (BP-C-M2).

| # | Phase | Field | Bad probability | `−log₂` | Lemma |
|---|---|---|---|---|---|
| Z1 | zerocheck point, `m − 13` free coordinates (2 per squeeze) | F | `17/2^128` (`19/2^128` at `m = 32`) | 123.9 (123.8) | `zerocheck_bad_le`; pinned coordinates by `pinned_rank` (DT24, kernel certificate) |
| Z2 | skip `λ`: the interpolant through `S ∪ Λ` has degree ≤ 127 | F | `127/2^128` | **120.99** | `skip_bad_le` (degree ≤ 127 as computed) |
| Z3 | `m − 6` rounds, degree 3 | F | `3/2^128` | 126.4 | `round_bad_le` |
| L1 | lincheck `α` | F | `1/2^128` | 128 | `batch_bad_le` |
| L2 | 9 rounds, degree 2 | F | `2/2^128` | 127 | `round_bad_le` |
| **L3** | lincheck univariate round over `S` | F | `127/2^128` | **120.99** | `skip_bad_le` |
| S1, S2, **S3** | shift `τ` (≤ 24 coordinates); degree-3 round; univariate round | F | `24, 3, 127 / 2^128` | 123.4, 126.4, **120.99** | `shift_sound` |
| I1, **I2** | public patterns and IO `θ` (≤ 25); univariate round | F | `25, 127 / 2^128` | 123.4, **120.99** | SZ, `skip_bad_le` |
| Lr1, Lr2 | L R1CS point (15), rounds (3), batching (2 claims: 1), rounds (2) | F | `15, 3, 1, 2 / 2^128` | ≥ 126.4 | Spartan (SR) |
| B1, **B2** | claim batching `κ` (≤ 8 claims); `m` rounds degree 2; univariate round | F | `7, 2, 127 / 2^128` | 125.2, 127, **120.99** | `batch_bad_le`, `skip_bad_le` |
| R1 | ring switch `r″` (7); `m − 7` rounds degree 2 | F | `7, 2 / 2^128` | 125.2, 127 | `ring_inj` |
| E1, E2 | element point (21); rounds (3); batching (2); rounds (2) | F | `21, 3, 2, 2 / 2^128` | 123.6, … | Spartan over F |
| B′ | batching ≤ 4 `f̂` claims | F | `3/2^128` | 126.4 | `batch_bad_le` |
| P1 | fold round `r` of level `i`: `2^(ℓᵢ−r)` lines | **K** | `(2^(ℓᵢ−r) · C_mca(nᵢ, kᵢ, eᵢ) + 2)/2^256`, `C_mca ≤ 2^60` | ≥ **190** | `mca_ud_line` (§5.3) |
| P2 | positions, level `i` | `log₂ nᵢ` bits | `(1 − eᵢ/nᵢ)^{tᵢ}` | **120.36**, 120.70, 120.36, 120.45, 120.41 | `positions_bad_le` |
| P3 | consistency batching, 9 coordinates | F | `9/2^128` | 124.8 | SZ |
| H | collision / in-play window hit, `≤ 2^16 · logCap` windows | — | `2^16 · 2^96 / 2^256` | **144** | `bad_step_le` (32-byte windows) |

**Maximum per fresh query: `2^-120.36 + 2^-144 ≤ εR = 15/2^124 = 2^-120.093`** (`epsR_le_cap`,
kernel-probed). The univariate rows are `2^-120.99 + 2^-144`. (`P1`'s line count: round `r` of
level `i` folds `2^(ℓᵢ−r)` pairs of rows, each a line.)

### 5.3 The proximity lemma (`FRProximity.mca_ud_line`; B-5, BP-C-M8)

Over `K ⊇ F`, `D ⊂ F` (`n` points), `C := C_K` of dimension `k`, `e` with `2e < n − k + 1`,
`u₀ u₁ : Fin n → K`:

```
mca_ud_line : Nat.card { z : K | ∃ w ∈ C, n − e ≤ agree (u₀ + z•(u₁ − u₀)) w ∧
    ¬ ∃ v₀ v₁ ∈ C, agreeSet (u₀,u₁) (v₀,v₁) = agreeSet (u₀ + z•(u₁ − u₀)) w } ≤ C_mca n k e
```

with `C_mca n k e := n · (k + 1) · (e + 1) · 4` as the working value (the proof below gives a
constant of that order; the lemma is stated with `C_mca` as a definition that the closing proof
may enlarge, under the stage requirement `C_mca ≤ 2^60` for every level: `n k e ≤ 2^57` at level
0, `m = 32`). `fold_preserves`: under no bad fold challenge, a `2^ℓ`-row K-valued word is `e`-close
to `C^{2^ℓ}` with joint agreement `A` iff its fold is `e`-close with agreement `A` (round by round
over the pairs). **F-valuedness once per level**: the committed rows are F-valued and `|A| ≥ k`,
so the interpolants through F-valued data on F-points are in `C_F` (`interp_F`).

Proof plan (BCIKS20 Thm 4.1's UD argument): (1) Berlekamp–Welch pairs `(E_z, N_z)` for close `z`,
and `bw_unique` (any nonzero solution has `N = E · w_z`, since `2e < d`); (2) the `n × (k+2e+1)`
system over `K[Z]` (entries of `Z`-degree ≤ 1): if more than `e + 1` values admit a kernel vector,
every maximal minor vanishes identically, so over `K(Z)` the rank is deficient and a nonzero
polynomial solution `(E(X,Z), N(X,Z))` exists (Mathlib `Matrix.rank`,
`linearIndependent_rows_iff_isUnit`, `LinearMap.ker_ne_bot_of_finrank_lt`, denominators cleared);
(3) specialisation: off the ≤ `deg_Z E` zeros of `E`'s leading coefficient, `N(·,z) = E(·,z) w_z`;
long division `N = E Q + R` in `K(Z)[X]`, `R = 0` once enough close `z` remain, `Q(·, z) = w_z`
off the denominators' zeros — **the `Z`-degrees of `Q`'s coefficients are `O(k (e+1))`** (each
division step divides by `lc_X E`), which is where the `k` in `C_mca` comes from; (4) positions:
`r_j(Z) := u₀[j] + Z(u₁[j] − u₀[j]) − Q(D[j], Z)` is `0` (then `j ∈ A`) or has `O(k(e+1))` zeros;
if `|A| < n − e` every good `z` has an agreement position off `A`: `≤ n · O(k(e+1))` of them;
(5) on `A` (`≥ k` points) `Q(D[j], Z)` is affine in `Z`, so `Q = v₀ + Z v₁` with `v₀, v₁ ∈ C_K`;
the agreement set of every good `z` is `A` (a position off `A` agrees for at most one `z`, counted
in (4)). Small-parameter probe by the crypto review: no counterexample to the statement.

### 5.4 `final`: the deterministic walk

Given `¬ Bad L`, `μ L < 1` and `(V vk c π).runLog L = some true` with `π` of kind `L32`/`P30`
(`W` is `Rel` by definition):

1. `runLog_chain`: the run is a complete chain of `L`; `cap_binding` (Merkle with caps: the
   column at a position is the first preimage read top-down from the cap entry, absorbed before
   the positions were squeezed; `colL_prefix`).
2. **Ligerito induction** (`ligerito_final`) from level 4 up: `g⁽⁵⁾ :=` the final message; for `i
   = 4 … 0` the word `W⁽ⁱ⁾` read off `L` (erasures where no preimage) is `eᵢ`-close to `C_K^{rowsᵢ}`
   with joint agreement `Aᵢ`, `|Aᵢ| ≥ nᵢ − eᵢ ≥ kᵢ`: the fold `u` of `W⁽ⁱ⁾` agrees with
   `Enc(g⁽ⁱ⁺¹⁾)` on the `tᵢ` queried positions (P3, the fold sumcheck rounds), impossible for an
   `eᵢ`-far `u` or a nearest codeword `≠ Enc(g⁽ⁱ⁺¹⁾)` (P2); `fold_preserves` (P1) lifts `u`'s
   agreement set to `W⁽ⁱ⁾`; `interp_F` gives the F-valued rows; their novel coefficients
   (`coeffs_of_values`, back-substitution) form `f⁽ⁱ⁾`, whose fold is `g⁽ⁱ⁺¹⁾`.
3. `f := f⁽⁰⁾` satisfies the batched claims (B′, R, E not bad), `ring_inj` gives the `ẑ` claims,
   `z := unpack f` is GF(2)-valued by definition of `unpack` (BP-C-m6), and (Z, Lc, Sh, I, Lr not
   bad) `HHolds`, `Patterns` (hence `one = 1` on the used blocks), `ShHolds`, `LrHolds`, `EHolds`.
4. `leaf_sound` or `node_sound` ⇒ `Rel (acc vk) c w` for `w := FR.readWit z`.
5. `ext_good_tape` (§6.5): the program outputs `witWords w`; `decodeWit_witWords`.

### 5.5 Completeness (B-10, D-22)

`P vk c w := .ret (WitnessSending.encode w)` for every witness; `V`'s `W` kind decides `Rel (acc
vk) c w` with no query, so `CompleteWithError … 0` by `complete_withError_zero`
(`Library/Completeness.lean`), for every `vk`. The honest SNARK prover is the native prover; that
its proofs pass `acc` is the harness's check (design §2.6) and §8.6's tests. `node_complete`
(two reference-signed children satisfy the circuit) is a positive control (§5.6), proved for one
child pair symbolically.

### 5.6 Controls (kernel-checked, toy instances only; M §7.1)

| Definition | Positive | Negative |
|---|---|---|
| F, K twins | `mul_kat_F/K` (S-A's 8 pairs) | a wrong modulus has a root |
| `Enc`, `coeffs_of_values`, tensor identity | round trip at `k = 4`; the identity at `log k = 2` | distinct messages differ (distance) |
| `mca_ud_line` | `C_mca < |K|` at every level (`decide`) | `2e = d`: a two-codeword counterexample |
| `skip_bad_le`, `round_bad_le`, `batch_bad_le`, `shift_sound`, `ring_inj` | SR's controls | SR's negatives (`skipDraw_unzeroed_not_rbr` ported) |
| block circuits | `block_complete` (symbolic), `blake2s_chain` KAT on 2 blocks | `not_holds_flip`; a block with `one = 0` fails the `one` pattern |
| `leaf_sound`, `node_sound` | `leaf_complete` at `n = 1`; `node_complete` for two reference-signed `W` children of minimal size | a flipped chain output; `child_other_key` |
| `V`, formats, `reassemble`, `FR.readSigned` | parse ∘ serialise, `piSize` values, `reassemble (traceOf honest) = π` on a toy trace | `π ± 1` byte rejected with no query; a changed answer breaks `runSeq` |
| `gen`, `FRVIRSpec` | the per-phase semantic lemmas instantiated on a 2-round toy | an omitted check changes `semIR` |
| `nodeLayout`, `evalM_eq`, `tpl_mle`, `shift_mle`, `irregular_mle` | `decide` on a 3-row toy layout | a moved entry changes the value |
| potential | `empty`; the step inequality at one toy phase | **this `μ`'s `step` fails at `ε = 2^-121` on phase Z2** (not a non-existence claim); `queries_le`'s exact count − 1 is not a bound |
| extractor | `semXIR extIR` on a toy tape (`k = 2`, one level) with a parametrised small layout; `cost` lemmas by `simp` | fuel one less: `run = none` on the toy |

---

## 6. The extractor

### 6.1 Contract and B-8

`Computes p E fuel` asks, on every tape of the domain, `∃ o, p.run … = some o ∧ o.length ≤ outCap
∧ decodeWit o = E c π L`. With `E := (ext.run …).bind decodeWit`: `Computes ⇐ ext_halts` (halting
within fuel and the output cap on **every** tape) and `final ⇐ ext_good_tape` (§6.5). `E` is
computable. Kernel-probed (`B8.lean`: `computes_Eof`, `fuel_le`).

### 6.2 The algorithm (`ext`; memory `mem = 2^26` words, `memPerWord = 3`)

1. **Parse** `|π|`, the kind byte, `m`. `W`: copy `⌈|π|/8⌉` words of `π` to the output (cap: `2^17`
   words); halt. `L32`/`P30`-leaf: output `0 ‖ s ‖ n`; halt. Anything else of the wrong size:
   output nothing. Node: continue.
2. **Index the log**: for each entry `(answer words 0–1, tape position)` into a 3-word table
   (`3 t` memory), bottom-up stable merge sort (`≤ 64` passes), binary search by two words then
   the first equal entry; loops capped by `t` (affine caps, §6.4).
3. **Read the ladder bottom-up**: the final message and the caps from `π`; for `i = 4 … 0` and
   every position `j < nᵢ`: walk down from the cap entry by first-preimage lookup (a Merkle-node
   query of level `i`, or erasure), then the column query (or erasure) into the level's column
   store (`rowsᵢ nᵢ` F per level, `2^25` words at level 0).
4. **Decode level `i`** with the fold challenges `s` (read off the log along the FS chain) and
   `g⁽ⁱ⁺¹⁾ ∈ K^{kᵢ}` (the next level's novel coefficients, recombined from `f⁽ⁱ⁺¹⁾`; at `i = 4` the
   final message): `Enc(g⁽ⁱ⁺¹⁾)[j]` at every `j` (a multilinear evaluation of `g` at `(Ŵᵥ(D[j]))_v`,
   `kᵢ` K×F products per position, with the `Ŵᵥ(D[j])` table of `nᵢ log kᵢ` F); the K-fold of
   every present column (`2^{ℓᵢ}` K×F products); the agreement set `A`; `P := A[0…kᵢ)`; **row
   interpolation to values on `D[0…kᵢ)`**: `W(X) = Π_{p∈P}(X − D[p])` (`O(k²)`), `invW′[p]` (Horner
   + one batch inversion), **`invD`: the `nᵢ` inverses `1/D[d]` (one batch), since `D[s] − D[p] =
   D[s ⊕ p]`** (BP-E-M6), then for each `s < kᵢ`: `W(D[s])` (Horner, `k`), weights `W(D[s]) ·
   invW′[p] · invD[s ⊕ p]` (`2k`), the `rowsᵢ` rows' values (`k` each): `(3 + rowsᵢ) k²`
   products; **novel coefficients** from values on `D[0…k)` by back-substitution along the
   block-triangular `X_x(D[j])` (`k²/2` per row); result `f⁽ⁱ⁾`.
5. **Output** (node): `1 ‖ c₁ ‖ c₂` from `π`, then per slot `bytesWords (reassemble kindᵢ trᵢ) ‖
   logWords trᵢ ‖ sigWords σᵢ`, the items read from chain `i`'s message slots of `f⁽⁰⁾` (A.4),
   every loop capped by the kind's constants.

### 6.3 Step budget (`m = 30` node; one F product = 43 statements = **86 steps** on the compiled
code: 3 BF64 products (`clmul`, `clmulh`, 8 reduction ops each), 4 Karatsuba XORs, `mulBeta` as a
shift pair, loads/stores; `seq` nodes double it; BP-E-M6)

| Step | F-products | steps |
|---|---|---|
| memory | — | `2^26 + 3t` |
| index | — | `≤ 2^11 t` |
| ladder read | — | `2^30` |
| `Enc(g⁽¹⁾)` at `n₀ = 2^18`, `k₀ = 2^17` | `2^36` | `2^42.4` |
| K-folds | `2^25` | `2^31.4` |
| level-0 interpolation `(3 + 64) k₀²` and back-substitution `64 k₀²/2` | **`2^40.7`** | **`2^47.1`** |
| levels 1–4 | `≤ 2^36` | `≤ 2^42.4` |
| output `2^19.3` words | — | `2^21` |
| **total** | | **`2^47.15 + 2^11 t`** |

Declared `fuel t = 2^47.5 + 2^12 t` (margin 1.27× on the fixed term); `extractorBudget t = 2^48 +
2^16 t` (1.80×). **No `m = 31` fallback exists** (`2^49.2`, BP-E-M6). Program size: ≈ 6 k `XIR`
nodes, ≈ 2.5·10^5 compiled statements with the macro expansions (`progCap = 2^20`), by
`size_compile : size (compile P) = sizeIR P` and `simp`.

### 6.4 The DSL (`FRXDsl`; BP-E-M5)

```
inductive XIR
  | op | const | load | store | input | out | seq | ite
  | for (i bound : Reg) (capFn : Aff) (body : XIR)   -- i from 0 while i < M[bound], at most capFn t times
  | mulF | addF | mulK | addK | invF                   -- fixed statement sequences (constructors, not Lean macros)
```

`Aff` is an affine function `a + b·t` of the tape length (as two naturals). `compile : XIR →
XStmt` (the `for` as `loop` on a counter and a clamp `min(M[bound], capFn t)` computed with
`ltu`/`mul`/`and`; the field constructors as their sequences); `cost : XIR → ℕ → ℕ` syntactic, with
`for` costing `capFn t · (cost body + 4) + 3`; `outs : XIR → ℕ → ℕ` likewise. Theorems:

- `compile_runs : ∀ P tape M, ∃ n ≤ cost P t, ∃ M′ o, Runs tape (compile P) M #[] n M′ o ∧ o.size
  ≤ outs P t` (`∃ n ≤`, since a loop under its cap runs fewer steps; closed by `run_of_runs_le`,
  `BPeng.lean`);
- `compile_sem : Runs … (compile P) … → state′ = semXIR P state` (the reference semantics over
  `Array Word`); `mulF_sem` through `FRField128.toExt_mul`;
- `cap_ok`: on `extractorInput c π L`, every bound register's value is `≤ capFn t` (e.g. `|L| ≤
  t/5`), so the clamp never truncates on tapes of the domain.

`ext := ⟨2^26, 3, compile extIR⟩`; `ext_halts` from `compile_runs`, `cost extIR t ≤ fuel t` and
`outs extIR t ≤ 2^24` (per-phase `cost` lemmas by `simp`, never unfolding the compiled term).

### 6.5 `ext_good_tape` (`FRXSpec`): over `semXIR`, phase by phase

`index_spec`/`lookup_spec` (first entry with a given answer); `read_spec` (the column store equals
`colL`'s first-preimage reading: the extractor's word **is** `final`'s `W⁽ⁱ⁾`); `enc_spec`,
`fold_spec`; `agree_spec` (`|A| ≥ kᵢ` from `ligerito_final`); `interp_spec` (Mathlib
`Lagrange.interpolate` through the weights, with the computable barycentric twin `Enc`/`interpF`
proved equal, BP-E-m6); `coeffs_spec` (back-substitution = `coeffs_of_values`); `output_spec`
(the words are `witWords (FR.readWit (unpack f⁽⁰⁾))`).

---

## 7. The Lean module plan

Flat modules `lean/FR*.lean`, prefix `FR`, namespace `FR`; `FR.lean` imports all, `Solution.lean`
imports `FR`. Code lines (`loc.py`), total **≈ 40.5 k** (hard cap 45 k); no module over 1,200
lines (BP-E-m8: the five large ones are split). Vocabulary (BP-E-m9): the source rule rejects the
whole words `partial`, `syntax`, `macro`, `elab`, `init`, `export` anywhere, comments included;
write "partial sums" as "prefix sums", "macro" as "constructor sequence".

**Stage S-0 (interfaces, one implementer, before the tracks fork):** `FRFieldDefs` (F, K as
types and byte maps, no proofs beyond `Field`), `FRTranscriptDefs` (query kinds, tags, challenge
maps), `FRFormat` (`hdr`, `piSize`, `parse`, `reassemble`, byte readers), `FRVIR` (`VProg`,
`runIR`, `semIR`, `gen` per phase), `FRVIRSpec`. **No cycle**: `FRVIR` imports
`FRTranscriptDefs` and `FRFormat` only; the proofs about the transcript (`FRTranscript`) come
later and import `FRVIR` where they need the programs.

| Module | Track | Content | Lines | Class |
|---|---|---|---|---|
| `FRFieldBase`, `FRFieldBaseCorrect` | L-field | BF64 twin (SR) | 100 + 820 | R |
| `FRFieldDefs` | S-0 | F, K types (`Ext`), byte maps, `mulBeta`, `mulAlpha` | 300 | N |
| `FRField128`, `FRField256` | L-field | traces (kernel), irreducibility, twins, `toExt_mul` | 700 + 500 | N |
| `FRFieldControls` | L-field | S-A's KATs | 100 | N |
| `FRMLE`, `FRMLEControls` | L-piop | eq, MLE, tables, `eq_mle` splitting | 300 + 50 | R/A |
| `FRSumcheck` | L-piop | rounds, batching, degree 3 | 350 | A |
| `FRSkip` | L-piop | `S`, `Λ`, the GF(2^8) embedding, `skip_bad_le` (degree ≤ 127), `pinned_rank` | 700 | N (LV) |
| `FRShift` | L-piop | range-restricted shift, `shift_sound` | 300 | N |
| `FRPatterns` | L-piop | public-pattern claims, `pattern_sound` | 250 | N |
| `FRRingSwitch` | L-piop | `ring_inj` (GF(2) ⊂ F), `unpack`, MBP = `B̂` | 650 | A |
| `FRSpartan` | L-piop | zerocheck/lincheck for `Sel ⊗ (A₀,B₀,I)` and sparse `(A,B,C)` over F | 450 | A |
| `FRRS`, `FRRSEval` | L-pcs | `D`, `Ŵᵥ`, `X_x`, `Enc`, distance, triangularity, tensor identity; computable twins (`interpF`, `encF`) | 600 + 300 | A (SR `RS`, LV `NovelBasis`) |
| `FRProximityBW`, `FRProximityLine`, `FRProximityFold` | L-pcs | `close_unique`, `bw_unique`; `mca_ud_line` (rank argument); `fold_preserves`, `interp_F`, `positions_bad_le` | 500 + 1,000 + 500 | N |
| `FROracle`, `FRQueries` | L-cert | SR | 170 + 70 | R |
| `FRTranscriptDefs`, `FRTranscript` | S-0, L-cert | kinds, tags, `chF`, `chK`, indices; fiber counts | 250 + 350 | A |
| `FRMerkle` | L-cert | caps, `cap_binding`, `colL`, `colL_prefix` | 750 | A |
| `FRLog` | L-cert | forest, `Matches`, `bad_step_le` (32-byte windows, `2^16 · logCap`), `extCount_split` | 800 | A |
| `FRBlake2sCircuit`, `FRBlake2sWords`, `FRBlake2sCompress` | L-circ | leanerVM's circuit | 1,550 | R |
| `FRBlake2sGeneric`, `FRBlake2sWalk`, `FRBlake2sWitness` | L-circ | SR | 730 | R |
| `FRBlockLayout`, `FRBlockStream` | L-circ | re-based layout; stream block, `block_sound` (`one = 1` explicit), `blake2s_chain` | 350 + 600 | A/N |
| `FRLeafCircuit` | L-circ | `leaf_sound`, `leaf_complete` | 1,200 | A |
| `FRFormat` | S-0 | A.3–A.4; byte readers (`get!`-based, SR `NodeBytes`) | 600 | N |
| `FRVIR`, `FRVIRSpec` | S-0 | `VProg` (A.5), `runIR`, `semIR`, `gen` per phase; per-phase semantics, `queries_le` closed form, `runSeq_eq_runIR` | 1,000 + 1,200 | N |
| `FRVIRCompile`, `FRVIREval` | L-circ | `compile : VProg → rows`, `compile_sound`; `evalM`, `tpl_mle`, `shift_mle`, `irregular_mle`, `evalM_eq` | 1,200 + 1,000 | N |
| `FRWots` | L-circ | WOTS and `hashStmt` as IR + blocks, `wots_sound`, `hashStmt_sound` | 700 | N |
| `FRNodeLayout`, `FRNodeCircuit` | L-circ | `nodeLayout` (bases, `N_M`, `N_L`, the `≤ 2^16` and `rows ≤ N_M` decides), `FR.readSigned`; `node_sound` | 400 + 1,200 | N |
| `FRVerifier` | L-cert | `V` (well-founded on `π.size`), `accWith`, `acc_eq`, `W` branches | 800 | N/A |
| `FRSoundnessDefs` | L-cert | phases, doom, `φ`, `μ` (SR Part A) | 800 | A |
| `FRSoundnessStepA`, `FRSoundnessStepB` | L-cert | Z/Lc/Sh/I/Lr/B/R/E rows; P1/P2/P3/H rows; `muG_step` | 1,200 + 1,000 | A/N |
| `FRSoundnessLigerito` | L-cert | `ligerito_final` | 1,000 | N |
| `FRSoundnessFinal` | L-cert | `runLog_chain`, `final` | 1,200 | A/N |
| `FRKState`, `FRCompleteness` | L-cert | `kstate vk`; `P := encode`, `complete` via the library | 200 + 150 | A |
| `FRXDsl`, `FRXField` | L-ext | `XIR`, `compile`, `cost`, `compile_runs`, `compile_sem`; field constructors and `*_sem` | 1,200 + 700 | N |
| `FRXLog`, `FRXDecodeA`, `FRXDecodeB`, `FRXProg` | L-ext | index; ladder read, folds, agreement; interpolation and back-substitution; `extIR`, `ext`, `cost_le`, `size_compile` | 900 + 900 + 900 + 500 | N |
| `FRXComputes`, `FRXSpec` | L-ext | `ext_halts`, `computes`; `ext_good_tape` | 500 + 1,300 | N |
| `FRSubmission`, `FRFinal`, `FRControls`, `FR`, `Solution` | L-cert | assembly; controls | 300 + 50 + 1,200 + 70 + 40 | N/A |
| **total** | | | **≈ 40.5 k** | |

**Budget against the caps** (C: 9–10 s build and 5–6 s kernel per kLoC at spartan-srom's mix on
the runner): build ≈ 365–405 s, kernel ≈ 205–245 s; the kernel-evaluated controls are toy-sized.
**The build's serial path** (BP-E-m8): `FRFieldBase → FRFieldDefs → FRTranscriptDefs → FRFormat →
FRVIR → FRVIRSpec → FRVerifier → FRSoundnessDefs → FRSoundnessStepB → FRSoundnessFinal → FRFinal →
Solution`, ≈ 9 k lines; at ≈ 30 CPU-s/kLoC that is ≈ 270 s single-threaded, under the 600 s cap
with the other 31 k lines spread over the remaining cores (4 vCPU). FR-R4′'s VM measurement moves
to the end of S-E, and per-module build and kernel seconds are logged from S-A on.

---

## 8. The prover plan (track P; B-9)

### 8.1 Structure

`prover/` as spartan-srom's: `main.rs` (modes), `service.rs` (reused), `format.rs` (FORMAT.md,
`witWords`, `reassemble`), `acc.rs` (the native `acc`: the IR interpreter over the generated
program), `field.rs` (BF64/F/K, S-A's formulas, dispatch), `ntt.rs` (additive NTT on `D`),
`blake2s.rs`, `circuit.rs` (leanerVM's block, re-based), `ir.rs` (the generator, equal to the Lean
`gen`: a dev-only dump tool **outside `submissions/`** (`probe/fr-irdump/`, `lake env lean` on a
file that `#eval`s `gen`) produces the reference for both programs; the entry never evaluates),
`witness.rs`, `zerocheck.rs`, `lincheck.rs`, `ringswitch.rs`, `ligerito.rs`, `par.rs`. No
dependency; `build-asm.sh`, `sanitize-asm.py` reused; `-C target-cpu=x86-64-v2`.

### 8.2 CPU tiers (dispatch once at start)

| Tier | Features | Kernels |
|---|---|---|
| 0 | AVX-512 + VPCLMULQDQ (+ GFNI): Xeon 8573C, EPYC 9V74/9V45 | the ymm kernels widened for the dominant loops; optional |
| 1 | **AVX2 + VPCLMULQDQ-256 + PCLMULQDQ: EPYC 7763, the tier of record** (K) | K's probe kernels: ymm F products (Karatsuba over 64-bit limbs; the tower's `mulBeta` is a shift pair), NTT butterflies, fold/MAC, skip-round byte kernels and transposes, `s_hat_v` |
| 2 | portable | development only |

### 8.3 Memory and time (**measured** by K on the EPYC 7763 unless marked)

| Item | value |
|---|---|
| `m = 32` leaf peak RSS | **3.81 GB** (arena `7·2^29` B); `m = 30`: 0.96 GB |
| `m = 32` leaf compute | 3.73–3.86 s (round 1 31 %, ring switching 23 %, NTT 17 %); all in 4.24–4.58 s (service hashing ≈ 85 compressions per statement compression, transfer, extras: **estimate**) |
| node compute | 0.81–0.83 s (43 k useful compressions); the design's node has 45.3 k H blocks and `2^20.4` M rows (K budgeted `2^17.6` rows at 4 ms: ≈ 30 ms here, **estimate**), 0.95–1.15 s all in |
| **tree** | **≈ 330–370 s against 600 s** |
| stream leaf (`m = 30`, 0.97–1.01 s compute) + node merge | **link ≈ 2.1–2.8 s against ≈ 3.1 s** (binding, ≥ 10 % margin) |

Levers (K §5): round-1 GF(2^8) products in a GF(16)² tower basis via `vpshufb` (−20 to −35 % of
round 1), a transposed SIMD `s_hat_v`, 8-lane AVX2 BLAKE2s for the witness; one pre-faulted
arena across the tree's leaves; the node's `evalM` replay rows are template-regular and their
witness is the native `acc`'s own arithmetic (≈ 1 ms).

### 8.4 Service plan (BP-E-m11)

A level-0 tree of an `m = 32` leaf sends `2^20` column queries of 1,032 B (≈ 1 GiB) and `2^20`
Merkle-node queries: with `QUERY ≤ 2^18` items and `≤ 2^24` B per request that is ≥ 65 requests,
spread over 16 connections (one per worker thread, ≤ 32 in all) in batches of 4,096 column
queries (4.2 MB) and 2^18 node queries; the sequential Fiat–Shamir queries on their own
connection; one `SIGN` per proof with the full query list (`≤ qV` items).

### 8.5 Setup and start-up; 8.6 checks

`setup` writes the two generated programs, the template tables and NTT twiddles to `/setup`
(a few MB; also rebuildable in 3–8 ms per K); a `leaf`/`node` process loads them before `ready`.
Checks (not certified): the Rust generator equals the Lean dump for both programs; the native
`acc` and the Lean `acc` (badge) accept every proof the prover writes at the smoke shape and on
one `L32`, one `P30` leaf and one `P30` node; `node_complete`'s symbolic control.

---

## 9. Stages, definitions of done, risks

| Stage | Track | Done when |
|---|---|---|
| **S-0 interfaces** | one implementer | Appendix A as Lean: `FRFieldDefs`, `FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec` (statements; proofs may be `sorry`-free skeletons with the phase lemmas stated), the IR dump tool; both programs' closed-form query counts `≤ 10,240` |
| **S-A field** | L-field | done (S-A journal): `F`, `K`, twins, traces, KATs |
| **S-B IR probe** | L-circ | the compiled interpreter on a synthetic `P30`-size program: `T_V` measured on the VM (≤ 160 ms VM ⇒ ≤ 125 ms runner) |
| **S-C piop** | L-piop | every F row of §5.2 as a lemma, univariate rows included; `FRPatterns`, `FRShift` |
| **S-D pcs** | L-pcs | `mca_ud_line` over K with `C_mca` fixed and `≤ 2^60` at every level; `fold_preserves`, `interp_F`, `positions_bad_le`, `cap_binding`; `FRRS`'s triangularity and tensor identity |
| **S-E circuits** | L-circ | `FRBlockStream`, `leaf_sound`, `compile_sound`, `evalM_eq`, `wots_sound`, `hashStmt_sound`, `node_sound`; `nodeLayout`'s two `decide`s (**B-2's kill test**); the VM build/kernel measurement (FR-R4′) |
| **S-F verifier** | L-cert | `V`, `accWith`, `acc_eq`, `queries_le`, format controls |
| **S-G soundness** | L-cert | `FRSoundnessStepA/B`, `FRSoundnessLigerito`, `FRSoundnessFinal`, `kstate vk`, `FRCompleteness` |
| **S-H extractor** | L-ext | `FRXDsl` theorems; `ext`, `ext_halts`, `ext_good_tape`; the toy control |
| **S-I certificate** | L-cert | `certificate`, `Solution.certified`; axioms three; VM build ≤ 450 s and kernel ≤ 450 s |
| **P1, P2, H1–H3** | P, H | as before: kernels and leaf proving against the native `acc` with the service in the loop (replaces K's estimates (a)–(c)); tree/stream modes; `prover.s` on binutils 2.42; compiled `acc` on a `P30` root; smoke ACCEPT; season on GitHub |

| Id | Risk | Kill test | Fallback |
|---|---|---|---|
| FR-R2′ | a §5.2 row's lemma is weaker than the table | S-C/S-D state exact counts | more queries (only P2 and the univariate rows are near the cap) |
| FR-R3′ | `compile_sound`/`node_sound` do not close in budget | S-E mid-point: `compile_sound` for the arithmetic ops in ≤ 1,000 lines | restrict the op set |
| FR-R4′ | certificate over 600 s build or kernel | S-E's VM measurement ≤ 450 s each (runner ≈ 1.3× faster) | split modules, remove kernel KATs, golf |
| FR-R5 | prover throughput | **closed by K**; residual: the link's ≥ 10 % margin at the design's node size, re-measured in P1 | K §5's kernel levers; FR-D2 |
| FR-R7 | `nodeLayout` overflows 65,536 or `N_M` | S-E `decide` | §4.5's tightening, then enumerated variants (B-2); never `m = 31` |
| FR-R8 | `mca_ud_line`'s rank argument over `RatFunc K` | S-D mid-point: §5.3 steps 1–2 | a larger `C_mca` (any `≤ 2^60`) |
| FR-R9 | `T_V` over 205.9 ms | S-B probe, H1 | specialise the interpreter's hot ops |
| FR-R6 | V4-A10 lands | re-pin; `FRKState` only | — |

---

## Appendix A. Normative interfaces (stage S-0)

Everything a track needs as a value. Hex is little-endian bytes unless it names a 64-bit word.

### A.1 Constants

| Object | Value | Certificate |
|---|---|---|
| BF64 | GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), CompPoly `BF64`; a word `w`, bit `i` ↔ `x^i`; bytes = `w` LE | allowlisted |
| **β** | `x^63` = word `0x8000000000000000`, bytes `00 00 00 00 00 00 00 80` | `FR.B64.frobSum_beta` (Tr β = 1), `FR.f128_irreducible` (S-A) |
| **F** | `BF64[y]/(y² + y + β)`; `c₀ + c₁ y` as 16 bytes `c₀ ‖ c₁`; `mulBeta r = reduce(r ≪ 63, r ≫ 1)` | S-A journal; KATs `mul_kat_F` |
| **α** | `β y`: `c₀ = 0`, `c₁ = 0x8000000000000000`; bytes `00^8 ‖ 00 00 00 00 00 00 00 80` | `FR.F.frobSum_alpha`, `FR.f256_irreducible` (S-A) |
| **K** | `F[u]/(u² + u + α)`; `f₀ + f₁ u` as 32 bytes `f₀ ‖ f₁`; `mulAlpha (z₀ + z₁ y) = β(β z₁) + β(z₀ + z₁) y` | S-A; `mul_kat_K` |
| products | F: `(a₀b₀ + β a₁b₁) + ((a₀+a₁)(b₀+b₁) + a₀b₀) y`; K: the same with `α`, `u` | S-A |
| **D** | `D[j] := (toBF64 j, 0) ∈ F` for `j < 2^20` (`toBF64 j` = the word `j`): the F₂-span of `1, x, …, x^19` | `D_inj` (`decide` on words) |
| **novel basis** | `Wᵥ(X) = Π_{a<2^v}(X − D[a])`, `Ŵᵥ = Wᵥ / Wᵥ(D[2^v])`, `v < 20`; `X_x = Π_{v ∈ bits x} Ŵᵥ`; the table `Ŵᵥ(D[j])` is computed, never stored in Lean | `FRRS`: `W_linear` (`Wᵥ` is GF(2)-linear on `D`), `X_vanish` |
| **GF(2^8) ⊂ BF64** | `ζ := x^((2^64 − 1)/255)` (order 255), basis `gᵢ := ζ^i`, `i < 8` | `FRSkip.zeta_order` (kernel: `ζ^255 = 1`, `ζ^(255/3) ≠ 1`, `ζ^(255/5) ≠ 1`, `ζ^(255/17) ≠ 1`) |
| **skip sets** | `S := { Σ_{i<6} bᵢ gᵢ } ⊂ GF(2^8)` (64 points, the hypercube's image: bit `i` of the position's low 6 bits ↦ `gᵢ`), `Λ := S + g₆` | `S_disjoint_Λ` by `decide` on BF64 words |
| **pinned coordinates** | slot for S-0: seven elements `ρ₁…ρ₇ ∈ F`, candidate `ρⱼ := (x^(2^(j+3)), 0)`, accepted iff the 128 products `Π_{j∈T} ρⱼ Π_{j∉T}(1 + ρⱼ)`, `T ⊆ [7]`, are GF(2)-independent | `pinned_rank` (`decide +kernel` on a 128 × 128 bit matrix) |
| **`h0`** | BLAKE2s-256 unkeyed chaining value: `iv` with `iv[0] ^^^ 0x01010020` (spartan-srom `Blake2sR1CS.h0`) | contract |
| ladder | §2.2's table, per shape | `FRTranscriptDefs.ladder30/32` |
| `N_M, N_L` | `2^21`, `2^15` rows | `FRNodeLayout` |
| caps | `εR = 15/2^124`, `δ = 0`, `qV = 10,240`, `fuel = 211,106,232,532,992 + 4,096 t` | B-10 |

### A.2 Encodings, tags, challenges

- **Positions**: a level with `n = 2^b` positions reads `⌊256/b⌋` indices per squeeze answer `a`;
  index `i` of `a` is bits `[ib, (i+1)b)` of `natLE a` (`SpartanSromTranscript.idxOf`); the `tᵢ`
  positions of a level are the first `tᵢ` indices of its `⌈tᵢ/⌊256/b⌋⌉` answers, in order, with
  repetition allowed (each repeated position is opened once in the trace; the circuit's rows per
  position are per *index*, so a repeat re-reads the same cells).
- **F challenge** of an answer: bytes `0…15`; the **second** F challenge of the same phase: bytes
  `16…31`. **K challenge**: all 32 bytes. A phase of `c` F-coordinates uses `⌈c/2⌉` squeezes.
- **Tags** (ASCII): seed `"FRSEED0"` (7 bytes); absorb `"FRABS000"`; squeeze `"FRSQZ000"`; Merkle
  node `"FRMNOD" ‖ byte i ‖ 0x00`; column `"FRMCOL" ‖ byte i ‖ 0x00`.
- **Column** at position `j` of level `i`: `rowsᵢ` F-elements, row `0` first, each 16 bytes;
  the Merkle leaf is the answer to the column query; Merkle node `d` at depth `h` over positions
  `[d·2^h, (d+1)·2^h)`, left child `2d`; the cap of level `i` is the `2^capᵢ` digests at depth
  `depthᵢ − capᵢ`, in index order.
- **Coordinate split**: K-element `x` of a fold result has coordinates `(f₀, f₁)`; F-element
  index `2x + c` holds `f_c`; the next level's matrix: row `(x mod 8)·2 + c`, column `x div 8`.
- **Absorb messages** are the concatenation of the fields A.3 lists for that absorb, zero-padded to
  a multiple of 16; a sumcheck round's message is its 3 coefficients `g(0), g(1), g(∞)` (degree-2
  rounds send `g(∞) = 0`), 48 bytes (F) or 96 (K); a univariate round sends 127 F values (the
  values on `S ∪ Λ` minus the one the check determines), 2,032 bytes padded to 2,048.
- **Statement bytes**: `leafStmtF h n`, `nodeStmtF c₁ c₂` as the contract (`Library/Fast.lean`).

### A.3 `piSize` and the body's field order (cumulative offsets are the sums)

| # | field | `L32` bytes | `P30` bytes |
|---|---|---|---|
| 0 | `hdr` (§1.1) | 48 | 48 |
| 1 | statement fields | 48 | 64 |
| 2 | Z2 `P^{ab}`, `P^z` on `Λ`: `2 × 64 × 16` | 2,048 | 2,048 |
| 3 | Z3 rounds `(m − 6) × 48` | 1,248 | 1,152 |
| 4 | Lc: `â ‖ b̂` (32) + 9 rounds `× 48` | 464 | 464 |
| 5 | L3, S3, I2, B2 univariate rounds `4 × 2,048`; S2 round 48; Lr/E rounds (P30: `(15 + 15 + 21 + 23) × 48` = 3,552; L32: 0) — the table's totals keep sizes.py's grouping: Sh/IO/B rounds `48 × 4 = 192` | 192 + 2,048 (one univariate slot per group is listed by sizes.py as `128 × 16`) | same + 2,880 (node-only rounds) |
| 6 | R: `s_v` `128 × 16` + `(m − 7) × 48` | 2,048 + 1,200 | 2,048 + 1,104 |
| 7 | B: `m × 48` | 1,536 | 1,440 |
| 8 | P1 fold rounds `22 × 96` | 2,112 | 2,112 |
| 9 | caps | 45,056 | 45,056 |
| 10 | final message `k₅ × 32` | 512 | 128 |
| 11 | columns, level by level, position by position (query order) | 445,696 | 445,696 |
| 12 | siblings, level by level, position by position, leaf level first | 241,664 | 185,920 |
| | **`piSize`** | **743,888** | **690,368** |

Row 5's accounting is sizes.py's (one `128 × 16` slot per shape plus `4 × 48`; the four
univariate rounds are each 2,048 B, so S-0 must either enlarge the PIOP part by `3 × 2,048 = 6,144`
bytes per shape or keep one shared slot by sending the univariate rounds' 127 values through the
same absorb; **S-0 fixes this and re-runs `sizes.py`; the margin to `proofCap` is 300 KB**).

### A.4 `reassemble kind tr : Proof` and the item sequence

The item sequence of `gen kind` is fixed: `items kind : List ItemKind` with each item's kind,
level and payload size (closed form, `FRVIRSpec.items_length`). `reassemble` walks `tr` in that
order: the header and statement fields from item 0's payload (bytes `64…` of the seed payload);
each absorb's `msg` field into its A.3 slot; the cap and final absorbs into rows 9–10; each column
query's payload into row 11; for each Merkle-node query of position `j` at depth `h`, the
**sibling is the half whose index is not bit `h` of `j`** (`j`'s bits come from the positions'
squeeze answers earlier in the same trace), into row 12. `reassemble_roundtrip`: for the trace of
an honest run, `reassemble kind tr = π`; `FR.readSigned` uses the same function.

### A.5 The IR (`FRVIR.VProg`): complete op set

Registers: `F` (16 B), `K` (32 B), `D` (digest), `B` (byte string), `N` (ℕ, a position or
counter), `Bit`. A program is `List Op`; `runIR` executes in order; `semIR` is the pure semantics
on the answer list. Every op below has a row cost (M rows, L bits) used by `compile` and
`sizes.py`.

| Op | Operands → result | Query | Semantics | Rows |
|---|---|---|---|---|
| `askSeed vk c hdr → D` | — | the seed query | binds the answer | imports |
| `askAbsorb st msg → D` / `askSqueeze st → D` | B, D → D | absorb / squeeze | binds the answer | imports |
| `askNode i left right → D` / `askCol i col → D` | D, D → D / B → D | Merkle node / column | binds the answer | imports |
| `chF a lo → F` | D, Bit → F | — | bytes `0…15` or `16…31` as F | 0 (an alias) |
| `chK a → K` | D → K | — | all 32 bytes | 0 |
| `idx a b i → N` | D, N, N → N | — | `idxOf b a i` | bit-elements (L) |
| `bitOf n h → Bit` | N, N → Bit | — | bit `h` of `n` | L |
| `mulF a b → F`, `addF`, `mulK a b → K`, `addK`, `mulKF k f → K`, `invF a → F` | | — | field ops (`invF 0 = 0`; the circuit witnesses `a⁻¹` and asserts `a · a⁻¹ = 1 ∨ a = 0` via a selector) | 1 / 0 / 3 / 0 / 2 / 2 |
| `eqTable r v → F[2^v]` | F^v → table | — | `eq(r, ·)` | `2^v − 1` |
| `lagrangeS a λ → F` | F[128], F → F | — | the interpolant through `S ∪ Λ` at `λ` | ≈ 256 |
| `tensorW j r → K` | N, K^v → K | — | `Π_v (1 − r_v + r_v Ŵᵥ(D[j]))` | `2v` |
| `mbp r″ layers → F` | F^7, … → F | — | the ring-switch `B̂` by the width-128 program | `(m−7)·128` + linear forms |
| `walkA r c → F`, `walkB r c → F` | F^14, F^14 → F | — | `Â₀`, `B̂₀` by the circuit walk | lincheck replay template |
| `evalM τ σ → F×F×F`, `evalL τ σ → F×F×F` | | — | the node's matrix MLEs (kind-selected) | `evalM` replay template |
| `patternSum θ pat → F` | F^16, pattern id → F | — | `Σ_{i : pat(i)} eq(θ, i)` | eq table + linear |
| `splitDigest d → F×F` | D → F, F | — | the two halves as F elements | 0 |
| `selectHalf b l r → D` | Bit, D, D → D | — | `b ? r : l` (the Merkle step) | 2 |
| `hashStmt kind fields → D` | B → D | — | `leafStmtF`/`nodeStmtF` | 1–2 H blocks |
| `assertEq a b` (F, K or D), `assertBit`, `assertZero` | | — | the check; a failure returns `false` | 1 linear |
| `accept` | | — | returns `true` | — |

No `...`: this table is the op set; an op not in it is not in `gen`.

### A.6 The block layout (bits within a `2^14`-bit block)

| bits | slot | content |
|---|---|---|
| 0 … 255 | 0–1 | `h_in` (8 words LE) |
| 256 … 511 | 2–3 | `h_out` |
| 512 … 1023 | 4–7 | the 64-byte message (stream block) / `0x43 ‖ d ‖ 0^31` (chain block) |
| 1024 … 1055 | 8 | `t_lo` |
| 1056 … 1087 | 8 | `t_hi = 0` |
| 1088 … 1119 | 8 | `f0` |
| 1120 … 1151 | 8 | `f1 = 0` |
| 1152 | 8 | `one` |
| 1153 … 1279 | 8–9 | zero |
| 1280 … 15999 | — | the 14,720 gates in leanerVM's order |
| 16000 … 16383 | — | zero |

Every public per-block constant (`one`, `t_lo`, `f0`, `h_in = h0` on chain starts, the zero
fields) is a public-pattern claim (§4).

---

## 10. Fix pass

Applied every major; every minor fixed or argued. Rulings 1–9 of the orchestrator were followed.

| Finding | Change |
|---|---|
| BP-C-M1 | `hashStmt` is an op of the replay and 2 H blocks per child slot (§3, §4.2, §4.3 (5), A.5); `hashStmt_sound`; `V = parse; stmtOk; runIR` with `stmtOk` an op |
| BP-C-M2 | univariate rounds L3, S3, I2, B2 added to §2.3 and §5.2 at `127/2^128` (Z2 restated at degree ≤ 127); **one squeeze serves one phase** (§1.2, §5.2); the maximum is P2's `2^-120.36 + 2^-144 ≤ εR` |
| BP-C-M3 | ladder reinstated to **five** levels with `e = ⌊(n−k)/2⌋` (B-3, §2.2); the final `Enc` is `2 k₅ t₄` (4,032 products); `sizes.py` rewritten; §3.1/§4.3/§4.5 recounted |
| BP-C-M4 | novel-basis (LCH) encoding, `Enc_k` by coefficients, the tensor identity and block-triangularity as `FRRS` lemmas (§2.1); consistency weights `O(log k)`; the extractor's basis change (back-substitution, `k²/2` per row) charged in §6.3; `fuel = 2^47.5 + 2^12 t` |
| BP-C-M5 | `one = 1` is a public-pattern claim on the used blocks; `leaf_sound`/`node_sound` state it; the pattern mechanism generalised to `t_lo`, `f0`, chain starts, padding, `P` (§4, §4.1, §4.3) |
| BP-C-M6, BP-E-M2 | the T region is dropped: a child's trace is the message slots of its chain's H blocks; the read address rule is stated (§4.2, B-6); no identification claim; chains contiguous in block index; T's block count question is moot |
| BP-C-M7, BP-E-M3 | one node shape, one program `P30` for every `m = 30` proof (kind-selected public constants), children in `{L32, P30}` muxed by rows with the kind selector asserted in-circuit (B-2, §3, §4.3 (1)–(2)); the fixed point resolved by fixed dimensions `N_M = 2^21`, `N_L = 2^15`, slots sized for the larger kind; rows counted for the worst kind (`2^20.4` per node); the enumeration fallback stated; `m = 31` struck |
| BP-C-M8, BP-E-m6 (first item) | `mca_ud_line` stated over K-valued words with `C_K`, `C_mca` a parameter (`≤ 2^60`), the line count `2^(ℓᵢ−r)` in P1, F-valuedness once per level (`interp_F`) (B-5, §5.2, §5.3); the proof plan's step 3–4 now carries the `O(k(e+1))` degree |
| BP-C-m1 | **fixed**: H row = `2^16 · logCap / 2^256 = 2^-144` over 16-byte-aligned 32-byte windows of every logged query and answer (§5.1, §5.2) |
| BP-C-m2, BP-E-m2 | **fixed**: all sizes recomputed by the new `sizes.py` (§0, §1.1, §1.2, §1.4, §4.3, §4.5); `qV = 10,240` with the stated margin; the `qV − 1` control replaced by "the exact count − 1 is not a bound" |
| BP-C-m3 | **fixed**: two F coordinates per squeeze, `⌈c/2⌉` squeezes (§1.2, A.2) |
| BP-C-m4 | **fixed**: E1 point = 21 coordinates, tied to `N_M` (§2.3, §5.2) |
| BP-C-m5 | **fixed**: the bit-elements' 127 zero coordinates are Lr's linear rows over L (`N_L = 2^15`), charged in Lr1 (§4.3, §5.2) |
| BP-C-m6 | **fixed**: Booleanity is definitional (`unpack`), §5.4 step 3 |
| BP-C-m7 | **fixed**: `V` by well-founded recursion on `π.size`, `accWith` (§3.3) |
| BP-C-m8 | **fixed**: §6.3 recomputed with the basis change and 86 steps per product |
| BP-C-m9 | **fixed**: `queries_le` as a closed-form count in `FRVIRSpec`; `qV = 10,240` |
| BP-E-M1 | the seed's tag is 7 bytes; every element of the hashed stream `0x54 ‖ traceBytes` is 16-aligned (§1.2, A.2); probed |
| BP-E-M4 | `FRVIRSpec` (1,200 lines): per-phase semantics, closed-form `queries_le`, `runSeq_eq_runIR` (§3, §7) |
| BP-E-M5 | `for` with affine-in-`t` caps, `cost` a function of `t`, `compile_runs` as `∃ n ≤ cost`, `cap_ok` on the domain, output loops capped by kind constants (§6.4, §6.2 (5)) |
| BP-E-M6 | steps counted on the compiled code (86 per product); `invD` by the subspace trick; `fuel_base = 2^47.5`; the `m = 31` fallback struck (§6.3) |
| BP-E-M7 | completeness through `W` with `P := encode`, `δ = 0`; `FRProver` and `compile_complete` dropped; `node_complete` a control (B-10, §5.5, §7) |
| BP-E-M8 | Appendix A (constants with S-A's β, α; tags; challenge maps; `piSize` field order; `reassemble`; the complete op set; the block layout); S-0 stage; the `FRVIR → FRTranscript` cycle broken by `FRTranscriptDefs` (§7, §9) |
| BP-E-m1 | **fixed**: the claim is `15/21267647932558653966460912964485513216`, `completeness_error "0"`, `fuel_base 211106232532992` (B-10) |
| BP-E-m3 | **fixed**: `W` cost argued with the fast chain twin and `acc`'s `proofCap` conjunct; DoS inputs carry no valid signature (§3.3); a byte-level `W` reader budgeted in `FRFormat` |
| BP-E-m4 | **fixed**: `T_V` prices the trace digest at the spec hash's speed (15–25 ms); the S-B interpreter probe added (§3.2, §9) |
| BP-E-m5 | **fixed**: the extractor control runs at `semXIR` on a parametrised small layout; the `ε = 2^-121` control is about this `μ`'s `step` on Z2; controls for `reassemble`, `nodeLayout`, the MLE lemmas and `gen` added (§5.6) |
| BP-E-m6 (second item) | **fixed**: computable twins `interpF`, `encF` in `FRRSEval` (§7) |
| BP-E-m7 | **fixed**: `FR.readSigned`, `FR.readWit`; `node_sound` through `accWith`; `FRNodeCircuit` does not import `FRSubmission` (§4.3, §7) |
| BP-E-m8 | **fixed**: modules ≤ 1,200 lines (the five large ones split), the serial path and the budget re-estimated (≈ 40.5 k lines, build 365–405 s, kernel 205–245 s, serial path ≈ 270 s), per-module timing from S-A, FR-R4′ moved to the end of S-E (§7) |
| BP-E-m9 | **fixed**: vocabulary note (§7) |
| BP-E-m10 | **fixed**: `size_compile` and per-phase `cost` lemmas by `simp`; the compiled size ≈ 2.5·10^5 statements (§6.3) |
| BP-E-m11 | **fixed**: the dump tool lives outside `submissions/` and dumps both programs; the service plan (§8.1, §8.4) |

**Rejected**: none. **Residual, named in the text**: A.3 row 5's exact byte accounting of the four
univariate rounds is left to S-0 (300 KB of `proofCap` margin covers either choice); the E1 point
size and `N_M` are fixed at `2^21` and must be confirmed by `nodeLayout`'s `decide` in S-E.
