# `flock-recursive`: entry blueprint (normative)

Status: phase 1 (B), **revision 3.2, frozen for implementation** (2026-10-27) after four rounds of adversarial review; later changes only through stage reviews, recorded in §10
(`reviews/BP-crypto-review.md`, `reviews/BP-eng-review.md`; fix passes in §10), 2026-10-27, for
the tracks S-0 (interfaces), L-field, L-piop, L-pcs, L-circ, L-ext, L-cert, P and H (`PLAN.md`
§3). Contract: `.contract` at core `15dac52` (`RecursionFast/Contract/*.lean` is authoritative;
where this file and the contract disagree, the contract wins and the disagreement is reported).
Inputs: `PLAN.md` (FR-D0 … D7), the phase-0 reports `T-theory.md`, `I-reuse.md`,
`C-calibration.md`, `M-measure.md`, `F-flock.md`, `K-kernels.md`, S-A's
`stages/S-A-JOURNAL.md` ("Normative constants"). Decisions are `B-n`; T's decisions are inherited
unless a `B-n` overrides them. Evidence tags: **paper**, **estimate**, **kernel**, **measured**.

Every number below is computed by `logs/blueprint/sizes.py` (output `sizes.txt`) from the
formulas stated next to it, or quoted from a phase-0 report; Lean probes are under
`logs/blueprint/probe/` (`B8.lean`, `BPeng.lean`, `r2/BPeng2.lean`, `r2/appendixA.py`).
`.contract/.lake/packages` is a symlink to the prebuilt tree matching the manifest at `15dac52`.

---

## 0. Summary

A Flock-class batch-R1CS argument over GF(2) with a Ligerito commitment over F = GF(2^128) in the
unique-decoding regime, fold challenges in K = GF(2^256), BLAKE2s everywhere, and **recursive SROM
nodes**: a node proof commits to its two children's signed traces as the message slots of its own
BLAKE2s blocks (hashing a trace and reading it are the same cells), checks one WOTS signature per
child and replays each child's verifier as field-element rows. **Two verifier programs** share
**one item sequence, one trace layout and one `piSize`**: `L32` (the tree leaf, `n = 2^18`,
`m = 32`) and `P30` (every `m = 30` proof: the stream leaf and every node; a node's children are any
two of `{L32, P30-leaf, P30-node}`, told apart in-circuit by a one-hot selector). Knowledge
soundness is certified through `KState` with per-fresh-query error `εR = 15/2^124 = 2^-120.09`;
the extractor decodes the node's commitment by erasure interpolation from the agreement set and a
novel-basis change, within `2^47.5 + 2^12 t` steps.

| Quantity | value | bound | margin |
|---|---|---|---|
| `piSize` (both kinds) | 756,560 B = 739 KiB | `proofCap` 1,048,576 | 1.39× |
| trace items (both kinds) | 8,896 | `qV = 10,240` | 1.15× |
| hashed trace bytes / compressions | 1,440,400 / 22,507 | — | — |
| node circuit blocks | 54,369 | 65,536 | 1.21× |
| M rows per node | 1,052,152 = `2^20.00` | `N_M = 2^21` | 1.99× |
| extractor steps (`m = 30` node) | `2^47.11 + 2^11 t` | `fuel = 2^47.5 + 2^12 t`; `B = 2^48 + 2^16 t` | 1.31×; 1.85× |
| error per fresh query | `2^-120.36 + 2^-144` | `εR = 2^-120.093` | — |
| verifier F-products | leaf ≈ 1.2·10^5, node ≈ 3.9·10^5 | `T_V` 205.9 ms (≈ 80–120 ms, **estimate**) | ≈ 2× |
| output words (node) | `2^19.3` | `outCap = 2^24` | — |

### 0.1 Decisions

| Id | Decision | Reason |
|---|---|---|
| **B-1** | **Tree leaves are single `m = 32` SNARKs of `2^18` compressions.** The stream leaf is `m = 30`. | The runner hashes the 64 statements `leafStmt (chainEnd sᵢ 2^18) 2^18` itself (`Tree.lean`); the leaf clause of `Rel` demands the chain, so a leaf made of signed segments is uncertifiable (`∀ vk`, design §2.2) and one of two fresh-query segment SNARKs exceeds `proofCap`. K measures the `m = 32` leaf at 3.73–3.86 s and 3.81 GB peak (K §3, §4.4). |
| **B-2** | **Nodes are `m = 30`, one shape, one program `P30`.** `L32` and `P30` have **one item sequence** (every phase sized for the larger kind; a kind's unused items are dummy queries with zero payloads, §1.2) so that every trace element has one address. A node's child slot is replayed by **one program `gen Mux`** whose kind-dependent constants, matrices and public patterns are selector-linear in a **one-hot selector `(s_L, s_P, s_N)`** of three L bits (§4.3). Exact count 53,792 of 65,536 blocks (1.22×), M rows `2^19.86` of `N_M = 2^21` (2.21×). | K: an `m = 31` node (≈ 1.9 s) puts the stream link over its cap, so `m = 30` is hard. A node's replayed verifier does not depend structurally on its own or its children's variants (rulings 1 and 2 of fix pass 2); the fixed point is cut by fixed dimensions (§4.3). Fallback if `nodeLayout` overflows: the enumeration of the occurring pairs `(L32, L32)`, `(P30, P30)` with a public pair byte, never `m = 31`. |
| **B-3** | **Five levels**, rates 1/2 … 1/32, rows 64 then 16, `eᵢ = ⌊(nᵢ − kᵢ)/2⌋`, queries **290, 178, 145, 132, 126**, caps at depth 9, 8, 8, 8, 7; **the final message is the level-4 fold, `2^7` K elements** (`2^5` at `m = 30`, zero-padded), followed by **7 final rounds** that reduce the claim to one point (P1-D7). **Every index is opened**, duplicates included. | BP-C-M3, BP-C-R2-M3, P1 question 3: a level-4 fold of 4 row variables leaves `k₄ = 2^7` K elements, not `k₅`; reducing the final claim to one point costs 7 K rounds and one MBP evaluation instead of 128. |
| **B-4** | **F = BF64[y]/(y² + y + β), β = x^63; K = F[u]/(u² + u + α), α = β·y** (S-A), through CompPoly's allowlisted `Ext` over `BF64`, two-`UInt64` twins. | S-A journal; no off-allowlist copy. |
| **B-5** | **Own mutual correlated agreement for lines in the UD regime over K-valued words and `C_K`**, **proved (S-D) with `C_mca(n,k,e) = k e + n`** by a counting argument (§5.3); P1 row `≤ 2^-214`. | I §2.5; `mca_ud_line_K`, `pcsLevels_ok` (kernel). |
| **B-6** | **Wiring:** regions H (BLAKE2s blocks), L and P (in the H gap), M (element rows). A child's trace is the message slots of its chain's H blocks, read by irregular matrix entries evaluated with eq tables (one product per entry); M-internal patterns are templates; BLAKE2s matrices by the walk; the L matrices templated too. **Every per-block public constant is pinned by the zerocheck's public target `E`** (`(A₀z)∘(B₀z) = z + E` at `(0,0)`-row positions, P1-D2/D3); the public inputs and padding are point claims on `f`; the chain links and endpoints are the shift argument's (P1-D5). | No pattern sumcheck, no selector-linear patterns (BP-C-R3-M2 moot); the zerocheck pins constants bit by bit at its own random point; it is what the prover already does. |
| **B-7** | **The verifier is an interpreter `runIR impl` of a straight-line IR**, parametrised by an op-implementation record `OpImpl` (`evalM`, `evalL`, `walk`, `mbp`, `lagrangeS`); the lincheck has 14 multilinear rounds (P1-D4) and all `ẑ` claims are ring-switched at once into Ligerito's weight (P1-D6); `FRVIRSpec` states each phase's semantics against the record's specification; the circuit's M and L rows are compiled from the same IR (`compile`), with the per-slot mux as a compiler mode (`compileMux`, `compile_mux_sound`). | BP-E-R2-M4 (no cycle), BP-E-R2-M2 (a construction and a theorem for the mux). |
| **B-8** | **`E := fun c π L => (ext.run (extractorInput c π L) (fuel t)).bind decodeWit`**; `XIR` with affine-in-`t` caps, `compile_runs` as `∃ n ≤ cost P t` under `BoundsOk`, counted on the compiled code; the `W` copy is capped by `t`. | Probed; BP-E-M5/M6, BP-C-R2-M2, BP-E-R2-m1. |
| **B-9** | **Prover: std Rust, one `prover.s`, CPUID dispatch, AVX2 + VPCLMULQDQ-256 tier of record.** | K. |
| **B-10** | **`ε = 15/2^124`; `δ = 0` (`P := encode`, kind `W`); `qV = 10,240`; `fuel t = 211,106,232,532,992 + 4,096 t`.** Claim: `{"error": "15/21267647932558653966460912964485513216", "completeness_error": "0", "qV": 10240, "fuel_base": 211106232532992, "fuel_per_word": 4096}` (renders: `r2/render-r2.log`). | §5.2; BP-E-M7; §6.3. |

### 0.2 Drift (T §6's D-1 … D-17 stand)

| # | Here | Paper / repository | Reason |
|---|---|---|---|
| D-2′ | five levels, `e = ⌊(n−k)/2⌋`, every index opened, final in the clear | five Johnson levels / six UD levels, stratified queries | B-3 |
| D-9′ | F = BF64[y]/(y²+y+x^63), K = F[u]/(u²+u+x^63 y) | GHASH; `F128[u]/(u²+u+x⁻¹)` | B-4 |
| D-13′ | node `m = 30`, one program, one item sequence for all kinds, one-hot child selector, trace = H message slots, public target `E` | tower, deferred accumulator | B-2, B-6 |
| D-23 | lincheck with 14 multilinear rounds; all `ẑ` claims ring-switched at once into Ligerito's weight; the shift argument with both endpoints and a 10-round slot collapse; the final message is the level-4 fold with 7 final rounds; the two-level pinned set | paper: skip round in the lincheck, separate ring-switch sumcheck | P1 (revision 3.1) |
| D-18 … D-22 | IR interpreter + compiled circuit; `decodeWit ∘ run`; MCA over K; ymm tier; completeness through `W` | — | B-7, B-8, B-5, B-9, B-10 |

---

## 1. Formats

### 1.1 The proof `π`

Kinds: **`W`** (`π = WitnessSending.encode w` exactly; decided with no query, §3); **`L32`**,
**`P30`-leaf (`'P'`)**, **`P30`-node (`'N'`)**: `π = hdr ‖ stmt ‖ body`, `|π| = piSize =
756,560` for all three (A.3), any other length rejected with no query.

```
hdr  (48 B) = kindByte(1) ‖ m(1) ‖ zero(14) ‖ pub(32)      kindByte 0x4C 'L' | 0x50 'P' | 0x4E 'N'; m 32 | 30 | 30
stmt (128 B) = the statement hash's padded message blocks (S-E1-M1):
              'L','P': tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64   (n = 2^(m−14), checked)
              'N':     tagNode ‖ c₁ ‖ c₂ ‖ 0^63
body        = PIOP messages ‖ cap₀ … cap₄ ‖ final (4,096 B) ‖ columns ‖ siblings   (A.3)
```

| part | bytes |
|---|---|
| `hdr`, `stmt` | 48 + 128 |
| PIOP messages (A.3's rows 2–11) | 19,872 |
| caps `(512 + 256 + 256 + 256 + 128) × 32` | 45,056 |
| final message `2^7 × 32` (P30: `2^5` K-elements then zeros) | 4,096 |
| columns `290 · 1,024 + 581 · 256` | 445,696 |
| siblings `32 × 7,552` (P30: its `5,810` real ones, the rest dummy zeros) | 241,664 |
| **`piSize`** | **756,560 (739 KiB, 72 % of `proofCap`)** |

### 1.2 Queries and the hashed trace

Query = `tag ‖ payload`, `|payload| ≡ 0 mod 16`; the seed's tag is 7 bytes, every other 8 (A.2).
In the hashed stream `0x54 ‖ traceBytes tr` every payload element and every answer is at an
offset `≡ 0 mod 16` (kernel-probed on a five-item trace, `r2/BPeng2.lean`). Stream element `e`
is message slot `4 + e mod 4` of H block `⌊e/4⌋` of the child's digest chain.

| Kind | Query | Bytes | Answer |
|---|---|---|---|
| seed | `"FRSEED0" ‖ vk ‖ c ‖ hdr` | 119 | state `st₀` |
| absorb | `"FRABS000" ‖ st ‖ msg` | 40 + `|msg|` | new state |
| squeeze | `"FRSQZ000" ‖ st` | 40 | new state, challenge source |
| Merkle node, level `i` | `"FRMNOD" ‖ i ‖ 0 ‖ left ‖ right` | 72 | the parent digest |
| column, level `i` | `"FRMCOL" ‖ i ‖ 0 ‖ column` | 1,032 / 264 | the leaf digest |

**One item sequence for all kinds** (A.4): every phase has the item count of the larger kind;
`P30` asks the extra items as **dummy queries** (an absorb of zeros, a squeeze whose answer is
unused, a Merkle-node query of `0^64` at the depths `L32` has and `P30` has not) and `L32` asks
the node-only phases' items with zero messages. The verifier ignores dummy answers; the circuit
asserts dummy payloads are zero (gated by the kind selector). Challenges: F = bytes `0…15` of a
squeeze answer, the second F coordinate of the same phase bytes `16…31`; K = all 32 bytes;
positions: `⌊256/b⌋` indices of `b = log₂ nᵢ` bits per answer, **every index opened, duplicates
included**. One squeeze serves one phase.

Counts (`sizes.py`): FS items 473, column queries 871, Merkle-node queries 7,552: **8,896 items**
(`qV = 10,240`, 1.15×); hashed stream 1,440,400 B = **22,507 compressions**.

### 1.3 What each kind proves; `reassemble`

`'L'`, `'P'`: `c = leafStmt h n`, SNARK of `chainEnd s n = h`, witness `.leaf s n`. `'N'`: `c =
nodeStmt c₁ c₂`, SNARK of `acc vk c₁ p₁ ∧ acc vk c₂ p₂` for the committed `p₁, p₂`, witness
`.node c₁ c₂ p₁ p₂`. `W`: `Rel` directly. A child's `πᵢ = reassemble trᵢ` (A.5): `hdr` from item
0's payload bytes `64…111`, `stmt` from item 1's payload, every other field from its item.

### 1.4 The extractor's output

`witWords`: a node of two children `≈ 639,407 = 2^19.3` words of `outCap = 2^24`; a leaf 6
words; `W`: the proof's words.

---

## 2. The protocol

### 2.1 Fields, code, challenges (values in A.1–A.2)

F, K as B-4. `D[j] := (toBF64 j, 0) ∈ F`, `j < 2^20`; `Wᵥ(X) = Π_{a<2^v}(X − D[a])`, `Ŵᵥ = Wᵥ /
Wᵥ(D[2^v])`, `X_x = Π_{v ∈ bits x} Ŵᵥ`; **`Enc_k(c)[j] = Σ_{x<k} c_x X_x(D[j])`** (novel-basis
coefficients = the row's hypercube values). Facts (`FRRS`): distance `n − k + 1`; `X_x(D[j]) = 0`
for `j < 2^msb(x)` (half-split back-substitution `T(k) = 2T(k/2) + k²/4 = k²/2` per row); the tensor
identity `Σ_x eq(r,x) X_x(D[j]) = Π_v (1 − r_v + r_v Ŵᵥ(D[j]))`.

### 2.2 The ladder (`kᵢ₊₁ = kᵢ/8`, `nᵢ = 2^(i+1) kᵢ`, `eᵢ = ⌊(nᵢ−kᵢ)/2⌋`, `tᵢ = ⌈120.25/−log₂(1−eᵢ/nᵢ)⌉`)

| level | `ρ` | rows | `log₂ k` (30 / 32) | `log₂ n` | `t` | `(1−e/n)^t` | positions/answer | squeezes (30 / 32) | siblings/query (30 / 32) | cap |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 1/2 | 64 | 17 / 19 | 18 / 20 | 290 | `2^-120.36` | 14 / 12 | 21 / 25 | 9 / 11 | 2^9 |
| 1 | 1/4 | 16 | 14 / 16 | 16 / 18 | 178 | `2^-120.70` | 16 / 14 | 12 / 13 | 8 / 10 | 2^8 |
| 2 | 1/8 | 16 | 11 / 13 | 14 / 16 | 145 | `2^-120.36` | 18 / 16 | 9 / 10 | 6 / 8 | 2^8 |
| 3 | 1/16 | 16 | 8 / 10 | 12 / 14 | 132 | `2^-120.45` | 21 / 18 | 7 / 8 | 4 / 6 | 2^8 |
| 4 | 1/32 | 16 | 5 / 7 | 10 / 12 | 126 | `2^-120.41` | 25 / 21 | 6 / 6 | 3 / 5 | 2^7 |

The item sequence uses the `m = 32` column (25, 13, 10, 8, 6 squeezes; 11, 10, 8, 6, 5 siblings);
`P30` fills the difference with dummies. The coordinate split: F-element `2x + c` is coordinate `c`
of K-element `x`; row `(x mod 8)·2 + c`, column `x div 8`; the running claim becomes
`Σ eq((r, z_c),(x,c)) g_c(x) = (1 − z_c) v₀ + z_c v₁`.

### 2.3 Round by round (phases named as in §5.2; `m* = 32` sizes the sequence)

A sumcheck round sends 3 coefficients (degree ≤ 3; degree-2 rounds carry `g(∞) = 0`), is checked
`g(0) + g(1) = claim` and folded at the challenge. The only univariate round is Z2. The committed
object is the quirky `ẑ` (multilinear in `m − 6` variables, degree `< 64` in the skip variable over
`S`); every other claim on `z` is a plain multilinear evaluation, and ring switching (step 7)
turns both forms into claims on the packed `f`.

0. `seed`; `absorb(stmt)`. 1. `absorb(cap₀)`.
2. **Z** zerocheck of `(A₀z)∘(B₀z) − z − E = 0` on the used blocks, with **`Sel` inside the weight**
   (R4-m1): the summand is `ŵ(x) · ((A₀z)∘(B₀z) − z − E)(x)` with `ŵ := MLE(eq(r,·) · Sel(·))`
   (`Sel = ∪_kind Ind_kind`, the used blocks; **`A = Σ_kind Ind_kind ⊗ A₀^kind`, `B = Σ_kind Ind_kind
   ⊗ B₀^kind`** with one block matrix per block kind (A.6: the kinds differ only in which positions
   are `(0,0)` rows), `Ind_kind` the public indicator of the kind's block intervals; `Sel` never
   inside `A`, `B`), `E` the **public target** of §4 (per block, per pinned position): **Z1** `r`, `m* − 13 = 19`
   free coordinates (10 squeezes; 7 pinned, A.1); **Z2** `absorb(P^{ab} ‖ P^z)`, `λ`; **Z3** `m* −
   6 = 26` rounds of degree 3; the prover ends with `â, b̂` (`absorb`) and the quirky claim
   `ẑ(λ, r′)`; the verifier's final value is `ŵ(r′) · (â b̂ − ẑ) − Ê_w(λ, r′)` with **`ŵ(r′) = Σ_x
   eq(r′,x) eq(r,x) Sel(x)`, a prefix sum of the tensor `eq(r′,·) eq(r,·)` over `Sel`'s intervals**
   (`O(log)` per interval; not `eq(r, r′) · Sẽl(r′)`) and `Ê_w(λ, r′) = Σ_{(blk,pos) pinned} eq(r′,blk)
   eq(r,blk) · posW(λ, r′_pos)(pos) · E(blk,pos)`: per pinned position (≤ 1,152 per kind) the
   block pattern's tensor prefix sum (constant on the kind's intervals, or affine in `blk` for
   `t_lo`) times the position weight (Lagrange at `λ` on the skip coordinate, eq on the rest):
   `O(#kinds · #pinned + #intervals · log)` products. The weight form keeps the rounds at degree 3
   and the prover's eq table (its entries outside `Sel` are zero: no extra prover cost); the
   separate-factor form would be degree 4 (4 coefficients, `4/2^128`).
3. **Lc** lincheck of `â = (A z)̂(r_row)`, `b̂ = (B z)̂(r_row)`: **L1** `α`; **L2** **14 rounds of
   degree 2** over the block's position bits (P1-D4); the verifier evaluates `Â₀(r_row, r_k)`,
   `B̂₀(r_row, r_k)` by **one walk** with column weights `eq(r_k, ·)` and the **per-kind-masked
   row weights** `rowW′[k] = rowW[k] · Σ_{kind : k ∉ pinned(kind)} Ĩnd_kind(r′_blk)` (`rowW` =
   Lagrane at `λ` on the skip coordinate, eq on the rest; the block matrices differ only by their
   `(0,0)` rows, so `Σ_kind Ĩnd_kind(r′_blk) · Â₀^kind(r_row, r_k) = walk(rowW′, eq(r_k,·))`:
   `2^14` products for the adjustment, `O(log)` per interval for the indicators, one walk); result:
   one multilinear claim `ẑ(r′_blk, r_k)`.
4. **Sh** shift argument (P1-D5), one sumcheck per proof (a node's two chains batched by `1, y`):
   **S1** `τ` (`m* − 14 = 18` block coordinates), `θ` (10 slot coordinates) and `κ_s` from 15
   squeezes; **S2** `18` block rounds of degree 2 on `eq(τ,·)·Out + (shift(τ,·) + κ_s eq(0,·))·In`
   with the endpoints (leaf: `s`, `h`; node: `h0` at each chain's first block) in the
   verifier's target, then **10 collapse rounds** over the positions `< 1024` with the
   verifier-computed slot weight of the two digest slots (`h_out` at 256…511; `d` at 520…775 for
   the chain block, `h_in` at 0…255 for the stream block); result: multilinear claims on `ẑ`.
5. **Lr** (node): Spartan over the L rows (`2^15`): point (8 squeezes), 15 zerocheck rounds (degree
   3), `κ_L`, 15 lincheck rounds (degree 2); result: one multilinear claim on `ẑ`.
6. **RS**, ring switching of all `ẑ` claims at once (P1-D6; paper App. B, quirky variant): the
   prover absorbs `J_z × 128` partials (`J_z = 4` for the node: Z, Lc, Sh, Lr; 3 for a leaf, the
   fourth zero); `r″` (7 coordinates) and `κ` (4 squeezes); the batched claim `Σ_y W(y) f(y) = v`,
   `W = Σ_j κ^j Ŵ_j`, is **Ligerito's input**; no separate `m − 7` rounds.
7. **E** (node): the element R1CS over the M rows: point (11 squeezes), 21 zerocheck rounds (degree
   3), `κ_E`, 23 lincheck rounds (degree 2); result: `f̂(r_E)`. **B′**: `κ′` batches into `W` the
   weights of `f̂(r_E)` and of the **point claims** on `f` (the public cells: `vk`, `cᵢ` in each
   slot's seed cells; the padding cells of each chain's last block): `J_f ≤ 20` claims.
8. **P** Ligerito, levels 0 … 4: **P1** `ℓᵢ` fold rounds (K challenges; the rounds fold `W` and
   `f` together, degree 2 in K); `absorb(capᵢ₊₁)` / `absorb(final)`; **P2** positions; the column
   and Merkle-node queries per index; **P3** `κ_c`, the consistency batching by the tensor weights.
   **The final message is the level-4 fold, `2^7` K elements** (P1-D7; `P30`: `2^5` then zeros);
   the verifier checks `Enc₄(final)[j]` directly at the `t₄` positions and reduces `Σ_c W(s, c)
   final(c)` by **7 final rounds** (K) to one point, where it evaluates `W` once (the MBP, A.8
   `mbp`).
9. Accept iff every check passed.

### 2.4 Parameters

| Name | Value |
|---|---|
| `m₀` | 14 |
| skip | `k_s = 6`, `S`, `Λ`, the two-level pinned set `ρᵢ = gᵢ/(1 + gᵢ)` (A.1) |
| `N_M`, `N_L` | `2^21`, `2^15` rows |
| `qV`, `εR`, `δ`, `fuel` | 10,240; `15/2^124`; 0; `2^47.5 + 2^12 t` |

---

## 3. The verifier `V vk c π`

```
V vk c π :=
  match kindOf π with
  | W      => ret (decide (RelW vk c π))                 -- no query; §3.3
  | none   => ret false                                  -- |π| ≠ piSize or bad kind byte
  | some k => runIR impl (gen k) (vk, c, π)              -- gen k's first ops are stmtOk's hashStmt
```

`runIR impl : VProg → Input → OProg Bool` is parametrised by `impl : OpImpl` (the implementations
of `evalM`, `evalL`, `walkA/B`, `mbp`, `lagrangeS`; `FRVerifier` instantiates it with `FRVIREval`'s
functions; `FRVIRSpec` states semantics against `OpImpl`'s specification record `OpSpec`, and
`FRVIREval` proves `impl ⊨ OpSpec`). `gen k` is generated phase by phase from the item sequence
`items` (`FRTranscriptDefs`); the three kinds share the op list's **shape**; the kind-dependent
public constants (`Sel`, the matrices, patterns, `hashStmt`'s variant) are the kind's. `stmtOk`
is the first `hashStmt` op (its inputs from item 1's `stmt`). The verifier's own public inputs
(`vk`, `c`) are bound by the seed query's bytes, which `V` builds itself. **`FRVIRSpec`**: `semIR (genPhase …)
(vk, c, π, answers) = …` per phase; `queries_le : ∀ H c π, ((V vk c π).queries H).length ≤ 10240`
by `items_length` (closed form); `runSeq_eq_runIR : asks tr = items → (runSeq tr (V vk c π) =
some true ↔ semIR (gen k) (vk, c, π, answers tr) = accept)`.

### 3.1 Operation counts (`sizes.py`)

| Work | `L32` | `P30` node |
|---|---|---|
| column folds `Σ tᵢ rowsᵢ` K×F | 46.6 k (F: 2 each) | same |
| final `Enc₄` at `t₄` positions, `2 · 2^7 · 126` | 32.3 k | 32.3 k (`P30`: 12 zero coefficients) |
| the univariate round Z2 at 128 points; 7 final K rounds | 0.5 k | 0.5 k |
| eq tables, tensor weights, K arithmetic | ≈ 15 k | ≈ 15 k |
| sumcheck rounds | ≈ 2 k | ≈ 2 k |
| MBP: `Ŵ(ρ) = Σ_j κ^j B̂_j(ρ)` at the final point, `J_z = 4` runs of `25 · 128` F (or one run with 4 state vectors) + `25 · 2^14` XOR | 12.8 k | 12.8 k |
| walks `Â₀, B̂₀` | `1.2·10^5` XOR | `1.2·10^5` XOR |
| node: `evalM` irregular `2 × 74,587` + eq tables `2 × 22,507 + 2^14` + templates + walks; `evalL` templated | — | ≈ 2.4·10^5 F |
| **F-products** | **≈ 1.1·10^5** | **≈ 3.6·10^5** |

### 3.2 `T_V` (**estimate**; the S-B probe replaces it)

Root check (`P30` node): trace digest at the spec hash's speed (1.45 MB, 15–25 ms on the
runner); `SigOk` 0.3 ms; parsing 2 ms; products `3.6·10^5 × 70 ns = 25 ms`; XORs 8 ms;
interpreter overhead ≤ 2× on the arithmetic: **≈ 80–115 ms against 205.9 ms**.

### 3.3 The `W` kind and DoS

`RelW` is the baseline's `C`/`N` decision: a leaf recomputes `chainEnd s n` with the library's fast
twin; a node checks `accWith V` on both children (`V` by well-founded recursion on `π.size`;
`accWith` = `Submission.acc` with `V` inlined, `acc_eq`). Cost: nested `W` nodes multiply (≈ 200
`W` leaves fit in 1 MiB, ≈ 35 s of chains). **This is not a DoS exposure**: `acc`'s `SigOk`
conjunct precedes `runSeq`, every `W` child needs a signature under the run's `vk`, the signing
key dies with the run's service, the harness's DoS inputs carry no valid signature
(`rfh/checks.py`), and the native prover never signs an empty trace; only the entrant's own
prover could build such proofs, against itself. `V`'s `W` branch therefore has no size cap
(completeness needs it for every witness, BP-C-R2-M2).

---

## 4. The circuits

Batch R1CS in Flock's form: `z ∈ GF(2)^(2^m)` is `2^(m−14)` blocks of `2^14` positions; **each
block has a kind** (A.6: `chain` for the leaf; `stream`, `streamStart`, `streamEnd41`, `hashA`,
`hashB1`, `hashB2`, `w43` for the node; M and L blocks have no kind and no block matrix), the
block matrices are `A = Σ_kind Ind_kind ⊗ A₀^kind` (S-E1-M2/M1: the same leanerVM circuit, with
the kind's pinned positions as `(0,0)` rows), the zerocheck's summand is `ŵ(blk, pos) ·
((Az)∘(Bz) − z − E)(blk, pos)` with `ŵ = MLE(eq(r,·) · Sel(·))`, `Sel = ∪ Ind_kind` (a union of
block intervals; its final value a prefix sum, §2.3 step 2) and **`E` the public target** (P1-D2,
P1-D3): at a position whose block row is `(0, 0)` the constraint reads `z = E`, so every per-block
public constant is pinned by the zerocheck itself at its random point, bit by bit: `one` (`E = 1`
at bit 1,152 of every used block), the constant words of slot 8 (`t_lo = 64(i+1)` or the stream
length at a chain's last block, `t_hi = 0`, `f0`, `f1 = 0`: `Ê` of an affine-in-`i` bit is `r_j +
Π_{l<j} r_l`-structured, `O(m)` per bit), the zero fields of the layout, and the chain block's
constants (`h0`, the tag, the zero message bytes, `t = 33`, `f`). `Ê(r) = Σ_{(blk,pos)} eq(r,
(blk,pos)) E` is computed by the verifier in `O(m · #patterns)`. **No pattern sumcheck exists**
(revision 3's §4 is withdrawn, BP-C-R3-M2 is moot). Positions that are inputs (`h_in`, the message,
the gates) are not in `E`; what must hold of them is proved by the shift argument (the chain links
and both endpoints, §4.1) or by point claims on `f` (§4.3).

### 4.1 The leaf circuit (`FRLeafCircuit`)

`2^(m−14)` chain blocks (spartan-srom's block, A.6: `h0`, the tag `0x43`, the zero message bytes,
`t = 33`, `f0 = 0xFFFFFFFF` as `(0,0)`-row positions pinned by `E`; the input `d` at 520…775; the
output at 256…511), **Sh** (P1-D5): `Σ_i eq(τ,i) Out(i) = Σ_i shift(τ,i) In(i) + boundary`, with
`In(0) = s` and `Out(n−1) = h` in the verifier's target, a sumcheck over the `m − 14` block
variables and a 10-round collapse over the slot positions with the verifier-computed slot weight.

```
leaf_sound [DecidableEq R] : ∀ (n ≥ 1) (z : Fin (2^m) → R) s h, (∀ i < n, IsBool (z ∘ blk i)) →
  (∀ i < n, HoldsE (blockR1CS chainTarget) (z ∘ blk i)) → ChainLinks n z s h → chainEnd s n = h
```

(the proved form, S-E1: every `n ≥ 1`, hypotheses on the used blocks only). `HoldsE (blockR1CS
chainTarget)` is the block R1CS with the `chain` kind's target (it entails `one = 1`,
`holdsE_sound`); `ChainLinks n z s h` is the shift identity's content (`d(i+1) = out(i)` on
`520…775`/`256…511`, `d(0) = s`, `out(n−1) = h`, bit order as A.7's pack map). S-E1 keeps
`ChainLinks` a hypothesis; its derivation from the shift sumcheck is L-cert's (`shift_sound`).

### 4.2 Stream block, digest chain, WOTS, statement check

Stream block: `h_in` and the message are inputs; `t_lo`, `t_hi`, `f0`, `f1` and `one` are
`(0,0)`-row positions pinned by the public target `E` (per-block values: the counter `64(i+1)`,
the stream length and `f0 = 0xFFFFFFFF` at the chain's last block); `block_sound` (`one = 1`
explicit, delivered by `E`). Digest
chain of the hashed stream `B` (`N = ⌈|B|/64⌉ = 22,507` for every kind, since the stream is one
layout): `h₀ = h0`, `hᵢ₊₁ = compress hᵢ Bᵢ tᵢ fᵢ 0`, `traceDigest tr = le h_N`
(`blake2s_chain`). Child slot `σ ∈ {1, 2}` reads stream element `e` at element address
`(chainBase_σ + ⌊e/4⌋)·128 + 4 + e mod 4`, `chainBase_1 = 0`, `chainBase_2 = 22,507`. **WOTS**:
133 chains × 3 selector steps + 67 leaf blocks + 32 path blocks = 498 blocks per slot.
**`hashStmt`** (BP-C-R4-M1): **three blocks per slot**, all in `Sel`, all constants
kind-independent: block **A** hashes the leaf message `tagLeaf ‖ h ‖ enc64 n ‖ 0^23` in one
compression (`t_lo = 41`, `f0 = 0xFFFFFFFF`); blocks **B1–B2** hash the node message `tagNode ‖ c₁
‖ c₂ ‖ 0^63` in two (`t_lo = 64`, `f0 = 0`; then `t_lo = 65`, `f0 = 0xFFFFFFFF`, linked `h_in(B2) =
h_out(B1)` by an element equality); **the messages are item 1's payload itself** (S-E1-M1): `stmt`
is laid out as the padded statement-hash message blocks (§1.1: `tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64`
or `tagNode ‖ c₁ ‖ c₂ ‖ 0^63`), so block A's and B1's message slots equal payload elements 0–3 and
B2's elements 4–7 by **8 element equalities per slot** (the payload's elements are 16-aligned
trace cells, §1.2; no byte shift); the kinds `hashA`, `hashB1`, `hashB2` pin `h_in = h0`, the tag
byte, the zero bytes and slot 8 (A.6), so the equalities carry only the variable bytes; the
slot's statement is `cᵢ = (s_L + s_P) · out_A + s_N · out_B2` (two product rows), asserted equal to
item 0's `c`. `wots_sound`; `hashStmt_sound : HoldsE (blockR1CS hashA) A → HoldsE (blockR1CS
hashB1) B1 → HoldsE (blockR1CS hashB2) B2 → h_in(B2) = h_out(B1) → msg(A) = msg(B1) = stmt[0…63] →
msg(B2) = stmt[64…127] → out_A = leafStmt (stmt[1…32]) (stmt[33…40]) ∧ out_B2 = nodeStmt
(stmt[1…32]) (stmt[33…64])` (the output selection and the `stmt` parse are `compile_mux_sound`'s
and `FRFormat`'s). `V`'s own `stmtOk` checks `stmt`'s tag and zero bytes for its kind and hashes
the message (one or two compressions). This is the cheapest sound construction found: the
alternative (keep `enc64 n ‖ h` and wire byte-shifted windows) needs GF(2)-linear, not F-linear,
rows (the BP-E-M1 problem).

### 4.3 The node circuit: layout, mux, counts

| Region | Base (blocks) | Content | Blocks |
|---|---|---|---|
| **H** | 0 | chain 1 `[0, 22,507)`, chain 2 `[22,507, 45,014)` (kinds `streamStart` at each chain's first block, `stream` elsewhere), `hashStmt` 6 (`hashA`, `hashB1`, `hashB2` per slot), WOTS 996 per node (`w43` 399, `hashB1` 1 + `stream` 65 + `streamEnd41` 1 for the key leaf, `hashB1`/`hashB2` 16 + 16 for the path, per slot), spare 8; `Sel` = the kinds' intervals; all-zero blocks elsewhere | 46,024 |
| **L** | 46,336 | bits (A.7): per slot the signature (4,772 B), the WOTS digits and selectors, the position bits as bit-elements, the one-hot kind selector `(s_L, s_P, s_N)`; `N_L = 2^15` rows | 124 (allotted 3,072: the gap to M) |
| **M** | 49,152 (`3·2^14`) | `N_M = 2^21` elements = 16,384 blocks, ending at 65,536; slot `σ`'s rows at `Mbase + (σ−1)·2^20` | 8,220 used |
| **total** | | | **54,369 of 65,536 (82 %, 1.21×)** |

There is no `P` region: the public inputs `vk`, `c₁`, `c₂` are **point claims on `f`** at each slot's
seed cells (payload elements 0–5 of item 0: `vk` 2, `cᵢ` 2; 8 claims per node), batched into the
Ligerito weight at B′ (BP-C-R3-m1: slot-valued facts are `f̂` claims, not `ẑ` claims); the padding
cells of each chain's last block (3 per chain) are point claims `= 0` the same way.

**The mux (B-2, B-7).** Each slot is replayed by `gen Mux`, one program with the item sequence's
shape, whose kind-dependent data are selector-linear:

- the **selector** `(s_L, s_P, s_N)` (three L bits, Boolean by Lr): **one-hot by the rows `s_L s_P
  = 0`, `s_L s_N = 0`, `s_P s_N = 0` (three product rows) and `Σ_κ s_κ = 1` (linear)** — in
  characteristic 2 the sum alone admits `(1,1,1)` (BP-C-R3-M1); and `kindElem = Σ_κ s_κ ·
  kindConst_κ` (linear), where `kindElem` is element 4 of item 0's payload (`hdr`'s `kindByte ‖ m ‖
  zero(14)`);
- an **import** reads one trace cell (one address for all kinds, since the item sequence is one):
  one irregular entry, one row `v = x[a]` (a copy; or the cell is used in place);
- a **kind-dependent constant** `κ(kind)` is the linear form `Σ_κ s_κ κ_κ`: no row;
- an **op active for a subset of kinds** (the dummy Merkle steps `P30` lacks, the node-only
  phases `L32`/`'P'` lack, `hashStmt`'s second block) keeps its arithmetic rows ungated (they are
  always satisfiable: products with fresh outputs, inversions with the three-row `invF`) and
  **gates every assertion** by its activity selector `a = Σ_{κ active} s_κ`: `assertEq x y` becomes
  `a · (x − y) = 0` (one product row); a Merkle step `cur = left + b(right − left)` becomes `u =
  b·(right − left)`, `a · (cur − left − u) = 0` (two rows per half); the final `accept` is the
  conjunction of all gated asserts;
- the **kind-dependent matrices** of the child's own `evalM`/`evalL` (an `'N'` child evaluates the
  node's matrices, `'L'`/`'P'` none): the replay rows compute `evalM` for the node's matrices
  unconditionally (arithmetic) and gate the resulting asserts by `s_N`;
- **no kind-dependent per-block constant exists**: the hashed stream has one length for every
  kind (the item sequence is one), so the chain's `t_lo`, `f0` and padding positions are the same
  public target `E` for every kind.

`compileMux : VProg → rows` is `compile` in "gated" mode; **`compile_mux_sound`**: if the rows hold
with a one-hot selector equal to kind `κ`, then `semIR (gen κ) (vk, cᵢ, πᵢ, answers) = accept`;
proved from `compile_sound` by specialising the selector (the gated rows of the active kind are the
ungated rows of `gen κ`; the inactive ones are vacuous). Budget 600 lines on top of `compile_sound`.

**Row count per slot** (`sizes.py`; honest, no sharing between kinds since there is one program):
imports 74,587 (columns 27,856, sibling halves and answers `6 × 7,552`, FS fields `3 × 473`);
folds 54,841; final `Enc₄` `2 · 2^7 · 126 = 32,256` (P1-D7); Merkle steps `4 × 7,552 = 30,208`;
the Z2 Lagrange 400; eq/tensor 15,000; **MBP `J_z · 25 · 128 = 12,800`** (R4-m2); sumchecks 2,000; lincheck replay 65,536 + the per-kind row-weight adjustment 16,384 + 8 `stmt` equalities;
**`evalM` replay 210,570** (one row per irregular entry of the child's two slots, `2 × 74,587`,
plus eq tables `2 × 22,507 + 2^14`); `evalL` replay 8,192 (L's matrices templated, BP-C-R2-m3);
gated asserts 3,288; selector 7: **526,076 per slot, 1,052,152 = `2^20.00` per node** (`N_M`
margin 1.99×). **The node fits `m = 30`**;
the smallest cut, if `nodeLayout`'s `decide` fails, is sharing the lincheck-replay eq tables between
the two slots (−2^15 rows) and then the enumeration fallback of B-2.

**The fixed point.** `gen Mux` is a function of `(items, ladder30, ladder32, N_M, N_L, nodeLayout)`;
the child's `evalM` replay is sized by `items` (the irregular count is the item sequence's element
count, a constant), so the program does not depend on any variant; the stage theorem `rows
(compileMux (gen Mux)) ≤ N_M` closes the loop.

**What the circuit asserts of slot `σ`** (compiled from `gen Mux`): (1) one-hot selector and
`kindElem`; (2) item constants (`enc64 |q|`, tags, dummy payloads zero) gated by activity; (3) the
FS chain `state(k+1) = answer(k)`; (4) item 0's payload holds `vk`, `cᵢ` (point claims on `f`) and
`hdrᵢ`; (5) `hashStmt`: `cᵢ` is the statement of item 1's fields; (6) the arithmetic of `gen κ`;
(7) Merkle steps and cap comparisons; (8) the size constants; (9) `SigOk vk (traceDigest trᵢ) σᵢ`.

```
node_sound : ∀ z vk c₁ c₂, Boolean z → (∀ i ∈ usedH, Holds blockR1CS_E (z ∘ blk i)) → PubCells z vk c₁ c₂ →
  ShHolds z → LrHolds z → EHolds (pack z) →
  let p₁ := FR.readSigned 1 z; let p₂ := FR.readSigned 2 z
  accWith V vk c₁ p₁ = true ∧ accWith V vk c₂ p₂ = true
```

Proof: `LrHolds` (Booleanity) and the one-hot rows fix each slot's selector `κ_σ`; `PubCells` (the
point claims) fixes `vk`, `cᵢ` and the padding; (a) the chains compute `traceDigest` (`blockR1CS_E`
pins `one`, the counters and flags; `ShHolds` the links and `h0`);
(b) `compile_mux_sound` at `κ_σ` gives `semIR (gen κ_σ) … = accept`, `wots_sound`, `hashStmt_sound`;
(c) `runSeq_eq_runIR` with (2)–(3); (d) the constants.

### 4.4 Matrix MLE evaluation (`evalM`, `evalL`)

Rows `rowIx = Mbase + (σ−1)·2^20 + tplBase + inst·2^a + j`. Entry kinds: **template-internal**
(`eqInner · Σ_{tpl} eq eq`, `tpl_mle`); **shift-structured** (`shift_mle`, `O(log)`); **lincheck
replay** (`A₀`/`B₀` at an aligned base: the walk); **irregular** (a trace cell `e` of slot `σ`:
`T_σ[e] = eq(σ_blk, chainBase_σ + ⌊e/4⌋) · eq(σ_slot, 4 + e mod 4)` from two eq tables, times the
row's template table: **one product per entry**, `irregular_mle`); **L entries** (templated like M's:
the signature, digit, selector and position-bit regions have power-of-two strides; `evalL` in
`O(tpl)`). `evalM_eq`, `evalL_eq` proved generically from the per-kind lemmas.

### 4.5 Margins (`sizes.py`)

| Quantity | value | bound | margin |
|---|---|---|---|
| blocks | 54,369 | 65,536 | 1.21× |
| M rows per node | 1,052,152 | `2^21` | 1.99× |
| items | 8,896 | 10,240 | 1.15× |
| `piSize` | 756,560 | 1,048,576 | 1.39× |
| H gap for L | 124 blocks | 3,128 | — |

---

## 5. The potential, knowledge soundness, completeness, controls

### 5.1 Shape (`FRSoundness*`)

As spartan-srom's (`SoundnessKSBase` Part A, `muG_step`): `μ L = [Bad L ∨ Esc L] + Σ_{chains on
the frontier} φ(chain)`; a chain is a maximal transcript path (`Matches` re-parameterised by the
item sequence); **Bad** = a digest collision in `L`, a fresh answer equal to **any 32-byte window
at an offset `≡ 8 (mod 16)` of any logged query** (the payload's 16-byte elements in pairs: the two
halves of a Merkle-node query at offsets 8 and 40, the state and the cap entries of an absorb at
`8 + 32·i`) **or to any logged answer** (S-D-M1; count `≤ (queryCap/16 + 1) · logCap ≤ 2^16 ·
logCap`, the H row's `2^-144` unchanged), a repeated query, a flipped group; `φ` charges every
open phase its bad probability over the unasked squeezes (`extCount_split`). `step` = one lemma
per row of §5.2 from the exact fiber counts (`card_chF_fiber = 2^128`, `card_chK_fiber = 1`,
`card_idx_fiber`) plus the H row; `final` = §5.4.

### 5.2 Per-fresh-query error (`P30` node; `L32` with `m = 32`; one squeeze per phase)

| # | Phase | Field | Bad probability | `−log₂` |
|---|---|---|---|---|
| Z1 | point, 17 free coordinates (19 at `m = 32`) | F | `17/2^128` | 123.9 |
| Z2 | skip `λ`, interpolant of degree ≤ 127 (the only univariate round) | F | `127/2^128` | **120.99** |
| Z3 | 24 rounds, degree 3 (26 at `m = 32`) | F | `3/2^128` | 126.4 |
| L1, L2 | `α`; **14 rounds of degree 2** (P1-D4) | F | `1, 2 / 2^128` | 128, 127 |
| S1, S2 | `τ, θ, κ_s` (16 + 10 + 1 = 27 coordinates); 16 block rounds + 10 collapse rounds, degree 2 | F | `27, 2 / 2^128` | 123.2, 127 |
| Lr1–Lr4 | point (15); rounds (3); `κ_L` (1); rounds (2) | F | `15, 3, 1, 2 / 2^128` | ≥ 126.4 |
| RS1 | `r″` (7 coordinates) and `κ` (`J_z = 4` claims) in one phase: the bad polynomial `D(r″, κ)` has degree ≤ 1 per `r″` coordinate and ≤ `J_z − 1` in `κ` | F | `(7 + J_z − 1)/2^128 = 10/2^128` | 124.7 |
| E1–E4 | point (21); rounds (3); `κ_E` (2); rounds (2) | F | `21, 3, 2, 2 / 2^128` | ≥ 123.6 |
| B′ | `κ′`: `J_f ≤ 20` claims on `f` (the E claim, 8 public cells, 6 padding cells, the RS claim) | F | `19/2^128` | 123.8 |
| P1 | fold round `r` of level `i`, `2^(ℓᵢ−r)` lines; the round folds `W` and `f` (degree 2 in K) | K | `(2^(ℓᵢ−r) C_mca + 2)/2^256`, `C_mca ≤ 2^60` | ≥ 190 |
| P2 | positions | `log₂ nᵢ` bits | `(1 − eᵢ/nᵢ)^{tᵢ}` | **120.36**, 120.70, 120.36, 120.45, 120.41 |
| P3 | consistency batching, 9 coordinates | F | `9/2^128` | 124.8 |
| Pf | 7 final rounds, degree 2 | K | `2/2^256` | 255 |
| H | collision / window hit, `≤ 2^16 · logCap` windows | — | `2^-144` | 144 |

**Maximum `2^-120.36 + 2^-144 ≤ εR = 2^-120.093`** (kernel-probed `epsR_le_cap`). The public
target `E` and the zerocheck's `Sel` add no row: they are evaluated by the verifier inside Z's
final check. Dummy queries carry no challenge and no charge. The claim counts `J_z`, `J_f` are
layout constants (`FRNodeLayout`), and `batch_bad_le` takes them from there (BP-C-R3-m2).

### 5.3 The proximity lemma (`FRProximityLine.mca_ud_line`; B-5; **proved in S-D**)

For any field `K`, injective `x : Fin n → K`, `2e + k ≤ n` and any `u₀ u₁ : Fin n → K`
(`FRProximityLine.lean`):

```
mca_ud_line : ∃ B : Finset K, B.card ≤ k * e + n ∧ lineBad (rsCode x k) e u₀ u₁ ⊆ B
lineBad C e u₀ u₁ = { z | ∃ w ∈ C, n − e ≤ #agreeSet (u₀ + z • (u₁ − u₀)) w ∧
                       ¬ ∃ v₀ ∈ C, ∃ v₁ ∈ C, agreeSet₂ u₀ u₁ v₀ v₁ = agreeSet (u₀ + z • (u₁ − u₀)) w }
```

**`C_mca n k e = k e + n`**: `2^37 + 2^20` at level 0, `m = 32`; the P1 row is `≤ 2^-214` (with
the `2^(ℓ−r)` lines, `round_bad_cover`); `pcsLevels_ok` checks `2e + k ≤ n ≤ 2^64`, `C_mca ≤ 2^60`
and the row at all ten levels by `decide`. The proof is a counting argument, shorter than the
rank-over-`K(Z)` plan: (1) `bw_exists`: the bivariate Berlekamp–Welch system (`deg_X E ≤ n − k −
e`, `deg_Z E ≤ e`, `deg_X N < n − e`, `deg_Z N ≤ e + 1`) has more unknowns than equations, so a
nonzero solution exists for **every** `(u₀, u₁)`; (2) `bw_E_ne`, `bw_few_zero_cols`: `E(x_j, Z) ≢
0` at `≥ k` positions `J`, where `v₀, v₁` interpolate; (3) for `z` off the `≤ k e` roots of the
`E(x_j, Z)`, `j ∈ J`, `bw_unique` gives `N(X, z) = E(X, z)·P`, so `w = v₀ + z(v₁ − v₀)`; (4)
`line_eq_root`: a position outside the joint agreement set agrees with the line's codeword for at
most one `z` (`≤ n`). `fold_preserves`/`fold_lift` (`JointClose`, the same `A` across a round's
`2^(ℓ−r)` pairs, `hz` necessary by the review's `fold_preserves_fails_at_bad`), `interp_F` /
`interp_F_D` (F-valuedness once per level), `positions_bad_le` (tuples with repetition),
`encCode_eq_rsCode`, `novelX_eval_lt_msb` (block-triangularity), `novelX_tensor` (the verifier's
`tensorW`) are proved in `FRRS`/`FRProximityFold`. **FR-R8 is closed.**

### 5.4 `final`: the deterministic walk

Given `¬ Bad L`, `μ L < 1` and `(V vk c π).runLog L = some true`: `W` is `Rel` by definition and
`E` copies the proof (§6.2, any size). Otherwise: (1) `runLog_chain`, `cap_binding` (the column
at a position is the first preimage read top-down from the cap entry absorbed before the
positions were squeezed; a repeated position reads the same entries); (2) `ligerito_final` from
level 4 up: `W⁽ⁱ⁾` read off `L` is `eᵢ`-close to `C_K^{rowsᵢ}` with joint agreement `Aᵢ`, `|Aᵢ| ≥
kᵢ` (P2, P3 and the fold rounds; `fold_preserves` under P1); `interp_F`, `coeffs_of_values` give
`f⁽ⁱ⁾` whose fold is `g⁽ⁱ⁺¹⁾`; (3) `f⁽⁰⁾` satisfies the batched claims (B′, R, E), `ring_inj` the
`ẑ` claims, `z := unpack f` is GF(2)-valued by definition, and Z (with its public target), Lc,
the shift sumcheck, Lr and the point claims give `Holds blockR1CS_E` on the used blocks (hence
`one = 1` and the constants), `ShHolds`, `LrHolds`, `PubCells`, `EHolds`; (4) `leaf_sound`/`node_sound`; (5)
`ext_good_tape`, `decodeWit_witWords`.

### 5.5 Completeness

`P vk c w := .ret (WitnessSending.encode w)`; `V`'s `W` kind decides `Rel (acc vk) c w` with no
query (`accWith V = acc`, `decode ∘ encode = id`), so `CompleteWithError … 0` by
`complete_withError_zero`. The SNARK path's completeness is the harness's check (D-22);
`node_complete` is a control.

### 5.6 Controls (kernel-checked, toy instances only)

Revision 2's table (fields, `Enc`/tensor identity, `mca_ud_line`'s constant, the sumcheck lemmas,
block circuits, `leaf_sound`/`node_sound`, formats and `reassemble`, `gen`/`FRVIRSpec` on a
2-round toy, the MLE lemmas on a 3-row layout, the potential's step at one phase and its failure
at `ε = 2^-121` on Z2, the extractor at `semXIR` on a toy tape) plus: the one-hot selector (**a
three-hot assignment `(1,1,1)` fails the product rows**, BP-C-R3-M1; a two-hot one fails `Σ s =
1`); a dummy item with a non-zero payload fails its gated assert; the public target (a block
with `one = 0` or a wrong counter word fails the zerocheck's target at a random point); a wrong
public cell fails its point claim; `pinned_rank`'s inverse
(`M · Minv = I` by `decide`; a wrong `Minv` fails); a `W` proof of size `> proofCap` is copied
(toy at `semXIR`); `items_length = 8,896` and `piSize = 756,560` by `decide`.

---

## 6. The extractor

### 6.1 Contract and B-8

`Computes p E fuel` asks, on every tape of the domain, `∃ o, p.run … = some o ∧ o.length ≤ outCap
∧ decodeWit o = E c π L`. With `E := (ext.run …).bind decodeWit`: `Computes ⇐ ext_halts` (halting
within `fuel` and the output cap on every tape of the domain) and `final ⇐ ext_good_tape`
(§6.5). `E` is computable. Kernel-probed (`B8.lean`: `computes_Eof`, `fuel_le`).

### 6.2 The algorithm (`mem = 2^26`, `memPerWord = 3`)

1. **Parse.** `W`: copy `⌈|π|/8⌉` words to the output, **loop cap `capFn t = t`** (BP-C-R2-M2: a
   `W` proof may exceed `proofCap`; `final` has no size guard; the fuel's linear term covers the
   copy; `outs ≤ outCap` is only demanded on `Computes`' domain, where `|π| ≤ 2^20`). `'L'`/`'P'`:
   output `0 ‖ s ‖ n`. Wrong size or kind: output nothing. `'N'`: continue.
2. **Index the log** (stable merge sort by answer; bounds `≤ t`, affine caps).
3. **Read the ladder** (first-preimage walks from the caps; the duplicate positions of a level are
   read once each — the **word** `W⁽ⁱ⁾` is indexed by position, not by query).
4. **Decode level `i`**: `Enc(g⁽ⁱ⁺¹⁾)[j]` by the tensor table; K-folds; agreement set `A`; `P =
   A[0…k)`; `invD` (one batch inversion of `D[d]`, `D[s] − D[p] = D[s ⊕ p]`); per `s < k` the
   weights and the `rowsᵢ` values (`(3 + rowsᵢ) k²`); novel coefficients by half-split
   back-substitution (`k²/2` per row).
5. **Output**: `1 ‖ c₁ ‖ c₂`, per slot `bytesWords (reassemble trᵢ) ‖ logWords trᵢ ‖ sigWords σᵢ`
   from `f⁽⁰⁾`'s chain cells and L cells (A.5, A.7), every loop capped by the layout's constants.

### 6.3 Step budget (`m = 30`; 86 steps per F product on the compiled code)

| Step | F-products | steps |
|---|---|---|
| memory, index, ladder read | — | `2^26 + 3t`, `≤ 2^11 t`, `2^30` |
| `Enc(g⁽¹⁾)` at `n₀ = 2^18`, `k₀ = 2^17` | `2^36` | `2^42.4` |
| level-0 interpolation `67 k₀²` + back-substitution `32 k₀²` | **`2^40.6`** | **`2^47.0`** |
| levels 1–4, K-folds, output | `≤ 2^36` | `≤ 2^42.4` |
| **total** | `2^40.69` | **`2^47.11 + 2^11 t`** |

`fuel t = 2^47.5 + 2^12 t` (1.31×); `B t = 2^48 + 2^16 t` (1.85×). No `m = 31` fallback.

### 6.4 The DSL (`FRXDsl`; BP-E-M5, BP-E-R2-m1)

`XIR`: `op | const | load | store | input | out | seq | ite | for | mulF | addF | mulK | addK | invF`
(the field constructors are fixed statement sequences, not Lean macros), **without a runtime
clamp**: `for (i bound : Reg) (capFn : Aff) body` runs
while `M[i] < M[bound]`; `cost P t` charges `capFn t · (cost body + 4) + 3` per loop; theorems:

- `compile_runs : BoundsOk P tape → ∃ n ≤ cost P t, ∃ M′ o, Runs tape (compile P) M #[] n M′ o ∧
  o.size ≤ outs P t`, where `BoundsOk P tape` says every `for`'s bound register holds `≤ capFn t`
  on entry (a semantic predicate over `semXIR`);
- `boundsOk_ext : ∀ c π L in the domain, BoundsOk extIR (extractorInput c π L)` (each bound is a
  length word of the tape, `≤ t`, or a layout constant);
- `compile_sem`, `mulF_sem`, `size_compile`, per-phase `cost` lemmas by `simp`.

### 6.5 `ext_good_tape` (`FRXSpec`), over `semXIR`, phase by phase

`index_spec`/`lookup_spec` (the first entry with a given answer); `read_spec` (the column store
equals `colL`'s first-preimage reading: the extractor's word **is** `final`'s `W⁽ⁱ⁾`);
`enc_spec`, `fold_spec`; `agree_spec` (`|A| ≥ kᵢ` from `ligerito_final`); `interp_spec`
(`Lagrange.interpolate` through the weights, the computable twin `interpF`); `coeffs_spec`
(back-substitution = `coeffs_of_values`); `output_spec` (the words are `witWords (FR.readWit
(unpack f⁽⁰⁾))`, with `reassemble` of A.5).

---

## 7. The Lean module plan (with dependencies)

Prefix `FR`, flat `lean/FR*.lean`; total **≈ 41.5 k** code lines (hard cap 45 k), modules ≤ 1,200
lines; vocabulary (the source rule rejects the whole words `partial`, `syntax`, `macro`, `elab`,
`init`, `export` anywhere, comments included). **S-0 owns** `FRFieldDefs`, `FRTranscriptDefs` (kinds, tags,
challenge maps, **`items`**, `ladder`), `FRFormat`, `FRVIR` (`VProg`, `OpImpl`, `OpSpec`, `runIR`,
`semIR`, `gen`), `FRVIRSpec`. **No cycle** (BP-E-R2-M4): `FRVIR` imports `FRTranscriptDefs`,
`FRFormat`, `FRFieldDefs`; `FRVIREval` (L-circ) imports `FRVIR` and proves its `impl ⊨ OpSpec`;
`FRVerifier` imports both and instantiates `runIR FRVIREval.impl`.

| Module | Track | Content | Lines | Imports (FR modules) |
|---|---|---|---|---|
| `FRFieldBase`, `FRFieldBaseCorrect` | L-field (done) | BF64 twin | 920 | — |
| `FRFieldDefs` | S-0 (done in S-A as `FRField*` defs) | F, K, bytes, `mulBeta`, `mulAlpha` | 300 | FieldBase |
| `FRField128`, `FRField256`, `FRFieldControls` | L-field (done) | traces, irreducibility, twins, KATs | 1,300 | FieldDefs |
| `FRMLE`, `FRMLEControls` | L-piop (S-C) | eq, MLE, tables, `eq_mle` | 350 | Field128 |
| `FRSumcheck` | S-C | rounds, batching, degree 3 | 350 | MLE |
| `FRSkip` | S-C | `S`, `Λ`, `ζ`, `skip_bad_le`, `pinned_rank` (parametric in `ρ`; A.1's two-level set with the shipped inverse) | 700 | Sumcheck |
| `FRShift` | S-C | the shift sumcheck of P1-D5: `m − 14` block rounds, 10 collapse rounds, endpoints in the target, two chains batched; `shift_sound` | 400 | Sumcheck |
| `FRPubTarget` | L-piop | `Sel`, the public target `E` and `Ê`'s closed forms (range and affine-bit MLEs); `target_pins` (`(0,0)` rows force `z = E`) | 250 | MLE |
| `FRRingSwitch` | S-C | `ring_inj`, `unpack`, the weight `Ŵ` of a quirky or multilinear claim, MBP = `Ŵ`; the κ-batching of `J_z` claims | 700 | Field128 |
| `FRSpartan` | S-C | zerocheck/lincheck over `Sel ⊗ (A₀,B₀,I)` and sparse `(A,B,C)` | 450 | Sumcheck |
| `FRRS`, `FRRSEval` | L-pcs (S-D done; **S-D2**: `FRRSEval`) | novel basis, `Enc`, triangularity, tensor identity (done); **`coeffs_of_values` (half-split back-substitution) with `coeffs_spec`, and the computable twins `interpF`, `encF` proved equal** (S-D-m1: owner L-pcs, stage S-D2, consumed by L-ext's `FRXDecodeB` and by `FRVIREval`) | 900 + 400 | Field128 |
| `FRProximityBW`, `FRProximityLine`, `FRProximityFold` | S-D | `bw_unique`; `mca_ud_line`; `fold_preserves`, `interp_F`, `positions_bad_le` | 2,000 | RS |
| `FROracle`, `FRQueries` | L-cert | SR | 240 | — |
| `FRTranscriptDefs` | S-0 | kinds, tags, `chF`, `chK`, `idxOf`, **`items`**, `ladder30/32`, `piSize` constants | 400 | FieldDefs, Oracle |
| `FRTranscript` | L-cert | fiber counts, `Matches` | 350 | TranscriptDefs, VIR |
| `FRMerkle` | S-D | caps, `cap_binding`, `colL` | 750 | Transcript |
| `FRLog` | L-cert | forest, `bad_step_le`, `extCount_split` | 800 | Merkle |
| `FRBlake2s{Circuit,Words,Compress,Generic,Walk,Witness}` | S-E1 | leanerVM's circuit, walk | 2,280 | — |
| `FRBlockLayout`, `FRBlockChain`, `FRBlockStream` | S-E1 | A.6 layout; chain block; stream block, `blake2s_chain` | 1,300 | Blake2s* |
| `FRLeafCircuit` | S-E1 | `leaf_sound` (hypotheses `Holds blockR1CS_E` per block, `ChainLinks z s h`) | 1,200 | BlockStream |
| `FRFormat` | S-0 | A.3–A.5: `hdr`, `piSize`, `parse`, `reassemble`, byte readers, `W` reader | 700 | TranscriptDefs |
| `FRVIR` | S-0 | `VProg` (A.8), `OpImpl`/`OpSpec`, `runIR`, `semIR`, `gen` per phase (`gen k`, `gen Mux`) | 1,100 | Format, TranscriptDefs |
| `FRVIRSpec` | S-0 | per-phase semantics, `items_length`, `queries_le`, `runSeq_eq_runIR` | 1,500 | VIR |
| `FRVIRCompile`, `FRVIRMux` | L-circ | `compile`, `compile_sound`; `compileMux`, `compile_mux_sound` | 1,200 + 600 | VIR, Spartan, Walk |
| `FRVIREval` | L-circ | `impl`, `evalM`, `evalL`, `tpl_mle`, `shift_mle`, `irregular_mle`, `evalM_eq`, `impl ⊨ OpSpec` | 1,100 | VIRCompile, RSEval, RingSwitch |
| `FRWots` | L-circ | WOTS, `hashStmt`, soundness | 700 | VIRMux, BlockStream |
| `FRNodeLayout`, `FRNodeCircuit` | L-circ | A.7 layout, the two `decide`s, `FR.readSigned`; `node_sound` | 400 + 1,200 | Wots, LeafCircuit, PubTarget, Shift |
| `FRVerifier` | L-cert | `V`, `accWith`, `acc_eq`, `W` branches | 800 | VIRSpec, VIREval, Format |
| `FRSoundnessDefs` | L-cert | phases, doom, `φ`, `μ` | 800 | Log, Proximity*, Verifier |
| `FRSoundnessStepA`, `FRSoundnessStepB` | L-cert | F rows; P/H rows; `muG_step` | 2,200 | SoundnessDefs, Skip, Spartan, RingSwitch, PubTarget, Shift |
| `FRSoundnessLigerito` | L-cert | `ligerito_final` | 1,000 | SoundnessDefs, ProximityFold, Merkle |
| `FRSoundnessFinal` | L-cert | `runLog_chain`, `final` | 1,200 | StepA, StepB, Ligerito, NodeCircuit, LeafCircuit |
| `FRKState`, `FRCompleteness` | L-cert | `kstate vk`; `P := encode` | 350 | SoundnessFinal; Verifier |
| `FRXDsl`, `FRXField` | S-H1 | `XIR`, `compile`, `cost`, `BoundsOk`, `compile_runs`, `compile_sem`; field ops | 1,900 | Library.Machine; Field256 |
| `FRXLog`, `FRXDecodeA`, `FRXDecodeB`, `FRXProg` | L-ext | index; read/fold/agree; interpolation; `extIR`, `ext`, `cost_le`, `size_compile`, `boundsOk_ext` | 3,200 | XField, Format, TranscriptDefs |
| `FRXComputes`, `FRXSpec` | L-ext | `ext_halts`, `computes`; `ext_good_tape` | 1,800 | XProg; SoundnessLigerito |
| `FRSubmission`, `FRFinal`, `FRControls`, `FR`, `Solution` | L-cert | assembly, controls | 1,660 | all |
| **total** | | | **≈ 41.5 k** | |

**The serial path**, computed from the import column (`logs/blueprint/serial.py` to be kept
current from S-0 on): `FieldBase → FieldDefs → Field128 → MLE → Sumcheck → RS → ProximityBW →
ProximityLine → ProximityFold → … ` joins `TranscriptDefs → Format → VIR → VIRSpec → VIRCompile →
VIREval → Verifier → Transcript → Merkle → Log → SoundnessDefs → StepA → StepB → Ligerito →
SoundnessFinal → KState → Submission → Final → Solution`: ≈ 13.1 k lines on the longest chain, ≈
390 s single-threaded at 30 CPU-s/kLoC (**estimate**), under 600 s with the other 28 k lines on
the remaining cores; margin ≈ 1.3× after contention: FR-R4′ stays open until S-E's VM measurement.
S-0 mid-point kill test (BP-E-R2-m8): phase Z of `FRVIRSpec` end to end, its line count × 15
phases ≤ 1,500 or the budget is revised.

---

## 8. The prover plan (track P; B-9)

**Structure** as spartan-srom's: `main.rs`, `service.rs` (reused), `format.rs` (FORMAT.md,
`witWords`, `reassemble`), `acc.rs` (the native `acc`: the IR interpreter over the generated
programs), `field.rs` (S-A's formulas, dispatch), `ntt.rs` (additive NTT on `D`), `blake2s.rs`,
`circuit.rs` (leanerVM's block, A.6's layout), `ir.rs` (the generator, equal to the Lean `gen L32`,
`gen P30`, `gen Mux`; a dev-only dump tool **outside `submissions/`**, `probe/fr-irdump/`, produces
the references by `lake env lean` on a file that `#eval`s `gen` and `compileMux`; the entry never
evaluates), `witness.rs`, `zerocheck.rs`, `lincheck.rs`, `ringswitch.rs`, `ligerito.rs`, `par.rs`.
No dependency; `build-asm.sh`, `sanitize-asm.py` reused; `-C target-cpu=x86-64-v2`.

**CPU tiers** (dispatch once): 0 = AVX-512 + VPCLMULQDQ (+ GFNI), optional; **1 = AVX2 +
VPCLMULQDQ-256 + PCLMULQDQ, the EPYC 7763, the tier of record** (K's kernels: ymm F products with
`mulBeta` a shift pair, NTT butterflies, fold/MAC, skip-round byte kernels and transposes,
`s_hat_v`); 2 = portable, development only.

**Memory and time** (**measured** by K on the EPYC 7763 unless marked): `m = 32` leaf 3.81 GB
peak, 3.73–3.86 s compute (round 1 31 %, ring switching 23 %, NTT 17 %), 4.24–4.58 s all in
(service hashing ≈ 85 compressions per statement compression, transfer, extras: **estimate**);
node 0.81–0.83 s compute at 43 k useful compressions (this design: 46.2 k H blocks and `2^19.9` M
rows, **estimate** +0.1 s), 0.95–1.15 s all in; **tree ≈ 330–370 s against 600 s**; stream leaf
0.97–1.01 s compute, the dummy queries add ≈ 3.3 k compressions of service hashing per `P30`
proof (**estimate** +0.06 s), **link ≈ 2.1–2.8 s against ≈ 3.1 s** (binding, ≥ 10 % margin).
Levers (K §5): round-1 GF(2^8) products in a GF(16)² tower basis via `vpshufb`, a transposed
SIMD `s_hat_v`, 8-lane AVX2 BLAKE2s, one pre-faulted arena across the tree's leaves.

**Service**: a level-0 tree of an `m = 32` leaf sends `2^20` column queries (≈ 1 GiB) and `2^20`
Merkle-node queries: ≥ 65 `QUERY` requests (≤ 2^18 items, ≤ 2^24 B each) over 16 connections, the
sequential Fiat–Shamir queries on their own connection, one `SIGN` per proof (`≤ qV` items).

**Setup and start-up**: `setup` writes the three programs, `compileMux`'s template tables and
the NTT twiddles to `/setup`; a `leaf`/`node` process loads them before `ready`.

**Checks (not certified)**: the Rust generator equals the Lean dumps of `gen` (three programs)
and of `compileMux (gen Mux)` (`nnz` and layout, byte for byte); the native `acc` and the Lean
`acc` (badge) accept every proof the prover writes at the smoke shape and on one `L32`, one
`'P'` and one `'N'` proof.

---

## 9. Stages, definitions of done, risks

| Stage | Track | Done when |
|---|---|---|
| **S-0 interfaces** | one implementer | below |
| **S-A field** | L-field | done (S-A journal) |
| **S-B IR probe** | L-circ | the compiled interpreter on a synthetic `P30`-size program: `T_V` on the VM ≤ 160 ms |
| **S-C piop** | L-piop | every F row of §5.2 as a lemma; `FRShift` (P1-D5), `FRPubTarget`, `FRSkip` (`pinned_rank` by inverse, two-level set) |
| **S-D pcs** | L-pcs | `mca_ud_line` over K with `C_mca ≤ 2^60` at every level, `fold_preserves`, `interp_F`, `positions_bad_le`, `cap_binding`, `FRRS`'s triangularity and tensor identity |
| **S-E circuits** | L-circ | `FRBlockStream`, `leaf_sound`, `compile_sound`, `compile_mux_sound`, `evalM_eq`, `evalL_eq`, `impl ⊨ OpSpec`, `wots_sound`, `hashStmt_sound`, `node_sound`; `nodeLayout`'s two `decide`s (**B-2's kill test**); the VM build/kernel measurement (FR-R4′) |
| **S-F verifier** | L-cert | `V`, `accWith`, `acc_eq`, format controls |
| **S-G soundness** | L-cert | `FRSoundnessStepA/B`, `FRSoundnessLigerito`, `FRSoundnessFinal`, `kstate vk`, `FRCompleteness` |
| **S-H extractor** | L-ext | `FRXDsl` theorems (`BoundsOk` form); `ext`, `ext_halts`, `ext_good_tape`; the toy control |
| **S-I certificate** | L-cert | `certificate`, `Solution.certified`; three axioms; VM build and kernel ≤ 450 s |
| **P1, P2, H1–H3** | P, H | kernels and leaf proving against the native `acc` with the service in the loop; the two dump KATs; tree/stream modes; `prover.s` on binutils 2.42; compiled `acc` on a `P30` root; smoke ACCEPT; season on GitHub |

| Id | Risk | Kill test | Fallback |
|---|---|---|---|
| FR-R2′ | a §5.2 row's lemma is weaker than the table | S-C/S-D state exact counts | more queries |
| FR-R3′ | `compile_sound`/`compile_mux_sound`/`node_sound` do not close in budget | S-E mid-point: `compile_sound` for the arithmetic ops in ≤ 1,000 lines | restrict the op set |
| FR-R4′ | certificate over 600 s build or kernel; serial path ≈ 390 s (1.3×) | S-E's VM measurement ≤ 450 s each | split modules, remove kernel KATs, golf |
| FR-R5 | prover throughput | **closed by K**; residual: the link's ≥ 10 % margin, re-measured in P1 | K §5's levers; FR-D2 |
| FR-R7 | `nodeLayout` overflows (1.22× / 2.21×) | S-E `decide` | share the lincheck-replay eq tables between slots, then enumerated pairs; never `m = 31` |
| FR-R8 | `mca_ud_line` | **closed** (S-D: `C_mca = k e + n`, kernel-checked) | — |
| FR-R9 | `T_V` over 205.9 ms | S-B probe, H1 | specialise the interpreter's hot ops |
| FR-R10 | `FRVIRSpec` outgrows 1,500 lines | S-0 mid-point: phase Z end to end, × 15 phases | re-budget; `V` as structured Lean with `runIR (gen k) = V k` proved once (BP-E-M4's alternative) |
| FR-R6 | V4-A10 lands | re-pin; `FRKState` only | — |

- **S-0 definition of done** (BP-E-R2-m6): `FRFieldDefs`, `FRTranscriptDefs` (`items` with
  `items_length` **proved**), `FRFormat` (`piSize` as a proved sum, `reassemble`, `parse ∘ serialise`
  **proved**), `FRVIR` (`gen` for the three kinds and `Mux`, `OpImpl`/`OpSpec`), `FRVIRSpec` with
  phase Z's semantic lemma **proved** and every other phase's lemma **stated** (`sorry` allowed on the
  branch, tracked in the stage RESULT; the merged entry has none), the two dump tools, `sizes.py`
  and `serial.py` re-run.
- **S-C**: `FRShift` is P1-D5's sumcheck; `FRPubTarget` is a new sibling module. **S-E** adds `FRVIRMux`
  (`compile_mux_sound`). **S-E1** keeps `Holds blockR1CS_E` and `ChainLinks` as hypotheses.

---

## Appendix A. Normative interfaces (stage S-0)

### A.1 Constants

| Object | Value | Certificate |
|---|---|---|
| BF64 | `x^64 + x^4 + x^3 + x + 1`; word `w`, bit `i` ↔ `x^i`; bytes LE | allowlisted |
| **β** | `x^63` = `0x8000000000000000` | S-A: `frobSum_beta`, `f128_irreducible` |
| **F** | `BF64[y]/(y² + y + β)`; `c₀ + c₁ y` ↦ 16 B `c₀ ‖ c₁`; `mulBeta r = reduce(r ≪ 63, r ≫ 1)` | S-A; `mul_kat_F` |
| **α** | `β y` (`c₀ = 0`, `c₁ = x^63`) | S-A: `frobSum_alpha`, `f256_irreducible` |
| **K** | `F[u]/(u² + u + α)`; `f₀ + f₁ u` ↦ 32 B `f₀ ‖ f₁` | S-A; `mul_kat_K` |
| **D** | `D[j] = (toBF64 j, 0)`, `j < 2^20` | `D_inj`: `toBF64` is injective on `j < 2^64` (a one-line `BitVec.ofNat` injectivity, BP-E-R2-m7) |
| novel basis | `Wᵥ`, `Ŵᵥ`, `X_x` as §2.1 | `FRRS` |
| GF(2^8) ⊂ BF64 | `ζ = x^((2^64−1)/255)`, `gᵢ = ζ^i` | `zeta_order` (kernel; `appendixA.log`: order 255) |
| skip sets | `S = {Σ_{i<6} bᵢ gᵢ}`, `Λ = S + g₆` | `S_disjoint_Λ` |
| **pinned coordinates** | **the paper's two-level set (P1-D1): `gᵢ = ζ^(2^(i−1))` for `i = 1, 2, 3` (in GF(2^8)), `gᵢ = y^(2^(i−4))` for `i = 4 … 7`; `ρᵢ = gᵢ / (1 + gᵢ)`** | `pinned_rank`: the 128 products `Π_{i∈T} ρᵢ Π_{i∉T}(1 + ρᵢ)` are GF(2)-independent; **shipped as the inverse bit matrix `Minv` with `M · Minv = I` checked by `decide`** (rank 128: P1's test `pinned_rank`; the one-level set `y^(2^j)` also passes but costs round 1 ≈ 8× its convert-table work) |
| shift batching | the two chains' shift claims batched by `1` and `y` (the summands are GF(2)-valued bits, BP-C-R3 confirms) | GF(2)-independent |
| `h0` | the unkeyed BLAKE2s-256 chaining value | contract |
| ladders | §2.2 | `FRTranscriptDefs.ladder30/32` |
| `N_M, N_L, qV, εR, δ, fuel` | `2^21`, `2^15`, 10,240, `15/2^124`, 0, `2^47.5 + 2^12 t` | B-10 |

### A.2 Encodings and challenge maps

**Fold variable order and `eq`'s bit order** (S-D-m4): a level's fold rounds fold the row bits
from bit 0 (the lowest row bit; the coordinate-split bit `c` of the previous level) upward; the
Ligerito point's coordinate `v` is the challenge of the round that folded bit `v`; `FRRS.eqBits r
ℓ x` (bit `v` of `x` ↔ `r_v`, little-endian) is `FRMLE.eq` in the same order (no reversal;
`eqBits_eq_eq` in `FRTranscriptDefs`); `tensorW j r` takes `r` in that order. **In-play digests**
(S-D-M1; `FRTranscriptDefs`'s `MerkleEnc` instance): `carried (nodeQ i l r) = [l, r]`; `carried
(absorbQ st msg) = st :: (the 32-byte elements of msg at payload offsets 32·i)`, with the law
`carried_absorb`; `carried (seedQ …) = [vk, c]`; `carried (squeezeQ st) = [st]`; `carried (colQ …)
= []`; `parseNode`/`parseCol` check the kind **and the level byte**. Positions: a level with `n =
2^b` positions reads `⌊256/b⌋` indices per squeeze answer `a`; index
`i` of `a` is bits `[ib, (i+1)b)` of `natLE a` (`SpartanSromTranscript.idxOf`); the `tᵢ` positions
are the first `tᵢ` indices of the level's answers in order. F challenge: bytes `0…15` of a squeeze
answer; the second F coordinate of the same phase: bytes `16…31`; K: all 32 bytes. Tags (ASCII):
seed `"FRSEED0"` (7 B), absorb `"FRABS000"`, squeeze `"FRSQZ000"`, Merkle node `"FRMNOD" ‖ byte i ‖
0x00`, column `"FRMCOL" ‖ byte i ‖ 0x00`. A column: `rowsᵢ` F-elements, row 0 first, 16 B each;
Merkle node `d` at depth `h` covers positions `[d·2^h, (d+1)·2^h)`, left child `2d`; the cap of
level `i` is the `2^capᵢ` digests at depth `depthᵢ − capᵢ` in index order. Coordinate split: F
element `2x + c` is coordinate `c` of K element `x`; next level's row `(x mod 8)·2 + c`, column
`x div 8`. Statement bytes: `leafStmtF`, `nodeStmtF` (`Library/Fast.lean`). **Every index is
opened**; a sumcheck round's message is its 3 coefficients
(48 B; K rounds 96 B; degree-2 rounds carry `g(∞) = 0`); a univariate round's message is 127 F
values padded to 2,048 B; the final message is 16 K-elements (512 B; `P30`: 4 then zeros).

### A.3 `piSize = 756,560`: the body's fields in order (offsets are the cumulative sums)

| # | field | bytes |
|---|---|---|
| 0 | `hdr` | 48 |
| 1 | `stmt` (the padded statement-hash message blocks, 128 B) | 128 |
| 2 | Z2: `P^{ab} ‖ P^z` | 2,048 |
| 3 | Z3: 26 rounds × 48 | 1,248 |
| 4 | Z end: `â ‖ b̂` | 32 |
| 5 | L2: 14 rounds × 48 | 672 |
| 6 | S2: 28 rounds (18 block + 10 collapse) × 48 | 1,344 |
| 7 | Lr2 + Lr4: 30 rounds × 48 | 1,440 |
| 8 | RS0: partials `4 × 128 × 16` | 8,192 |
| 9 | E2 + E4: 44 rounds × 48 | 2,112 |
| 10 | P1: 22 fold rounds × 96 | 2,112 |
| 11 | Pf: 7 final rounds × 96 | 672 |
| | rows 2–11 (PIOP messages) | **19,872** |
| 12 | caps `cap₀ … cap₄` | 45,056 |
| 13 | final message: the level-4 fold, `2^7` K | 4,096 |
| 14 | columns: level 0 … 4, position by position (every index) | 445,696 |
| 15 | siblings: level 0 … 4, position by position, leaf level first (11, 10, 8, 6, 5 per position) | 241,664 |
| | **total** | **756,560** |

(`48 + 128 + 19,872 + 45,056 + 4,096 + 445,696 + 241,664 = 756,560`; `sizes.py`.) `P30` fills
its unused rounds (2 of Z3, the second chain's share of S2, 12 of the final message's 16 … 128 K
slots, the last 2 siblings per position) with zeros.

### A.4 The item sequence `items` (473 FS items, then per position its queries; `FRTranscriptDefs`)

| # | phase | items (in order) | absorb payload |
|---|---|---|---|
| 0 | seed | 1 seed (`vk ‖ c ‖ hdr`, 112 B) | — |
| 1 | stmt | 1 absorb | `stmt` (128 B, §1.1) |
| 2 | cap₀ | 1 absorb | 16,384 B |
| 3 | Z1 | 10 squeezes (19 free coordinates, 2 per answer) | — |
| 4 | Z2 | 1 absorb (row 2), 1 squeeze (`λ`) | 2,048 B |
| 5 | Z3 | 26 × (absorb round, squeeze) | 48 B |
| 6 | Z end | 1 absorb (`â ‖ b̂`) | 32 B |
| 7 | L1 | 1 squeeze (`α`) | — |
| 8 | L2 | 14 × (absorb, squeeze) | 48 B |
| 9 | S1 | 15 squeezes (`τ` 18, `θ` 10, `κ_s`) | — |
| 10 | S2 | 28 × (absorb, squeeze) | 48 B |
| 11 | Lr1 | 8 squeezes | — |
| 12 | Lr2 | 15 × (absorb, squeeze) | 48 B |
| 13 | Lr3 | 1 squeeze (`κ_L`) | — |
| 14 | Lr4 | 15 × (absorb, squeeze) | 48 B |
| 15 | RS0 | 1 absorb (the `4 × 128` partials) | 8,192 B |
| 16 | RS1 | 4 squeezes (`r″` 7, `κ`) | — |
| 17 | E1 | 11 squeezes | — |
| 18 | E2 | 21 × (absorb, squeeze) | 48 B |
| 19 | E3 | 1 squeeze (`κ_E`) | — |
| 20 | E4 | 23 × (absorb, squeeze) | 48 B |
| 21 | B′ | 1 squeeze (`κ′`) | — |
| 22+5i | P1.i | `ℓᵢ` × (absorb K round 96 B, squeeze) | |
| 23+5i | C.i | 1 absorb: `capᵢ₊₁` (8,192 / 8,192 / 8,192 / 4,096 B) or the final message (4,096 B) | |
| 24+5i | P2.i | 25 / 13 / 10 / 8 / 6 squeezes | — |
| 25+5i | Q.i | for each of the `tᵢ` indices: 1 column query, then 11 / 10 / 8 / 6 / 5 Merkle-node queries leaf level first (`P30`: the last 2 of each are dummies `0^64`) | |
| 26+5i | P3.i | 1 squeeze (`κ_c`) | — |
| 47 | Pf | 7 × (absorb K round 96 B, squeeze) | |

Every absorb's payload is the field listed; every squeeze's answer is consumed as A.2 says, in
order of appearance. `items_length = 8,896`.

### A.5 `reassemble tr : Proof`

`hdr := payload₀[64…111]`; `stmt := payload₁`; rows 2–11 from the absorbs of phases 4–21 and 47 in
order; row 12 from `cap₀`'s and `C.0 … C.3`'s payloads; row 13 from `C.4`; row 14 from the column
queries in order; row 15: for the Merkle-node query at depth `h` of index `j` of level `i`, the
**sibling is the half whose position is not bit `h` of `j`** (`j` read from `P2.i`'s answers by
`idxOf`), dummies copied as zeros. `reassemble_roundtrip` for honest traces; `FR.readSigned` uses it.

### A.6 The block layout and the per-kind block matrices (normative; S-E1-M2)

Bits within a `2^14`-bit block (element `k` = bits `[128k, 128k + 128)`):

| bits | element | content |
|---|---|---|
| 0 … 255 | 0–1 | `h_in` (8 words LE) |
| 256 … 511 | 2–3 | `h_out` |
| 512 … 1023 | 4–7 | the 64-byte message |
| 1024 … 1055, 1056 … 1087, 1088 … 1119, 1120 … 1151 | 8 | `t_lo`, `t_hi`, `f0`, `f1` |
| 1152 | **9** | `one` (S-E1-m2) |
| 1153 … 1279 | 9 | zero (the circuit's own zero rows) |
| 1280 … 15999 | — | the 14,720 gates in leanerVM's order |
| 16000 … 16383 | — | zero (the circuit's own zero rows) |

**Convention (S-E1-M2, normative for the Lean and the prover):** the block matrix of a kind is
leanerVM's circuit (`circuitR1CS`: inputs `(var k, var one)`, gates their forms, outputs `(out
form, one)`) with **every pinned position of the kind turned into a `(0,0)` row**; a pinned
position's value is its bit in the public target `E` (block-dependent where stated). Never `(one,
one)` rows for constant 1-bits. `TargetOk`: only input positions and `one` are pinned. The zero
rows `1153 … 1279`, `16000 … 16383` have `E = 0` in every kind.

| kind | used by | pinned positions (`(0,0)` rows) | `E` values |
|---|---|---|---|
| `chain` | the leaf's `2^(m−14)` blocks | `0…255`, `512…519`, `776…1023`, `1024…1152` | `h0`; `0x43`; zero; `t_lo = 33`, `t_hi = 0`, `f0 = 0xFFFFFFFF`, `f1 = 0`, `one = 1` |
| `stream` | digest chain blocks `1 … N−1`; key-leaf blocks `1 … 65` | `1024…1152` | `t_lo = 64(i+1)` (chain-relative; the last block of a digest chain: `1,440,400`; of the key leaf: `4,265`), `t_hi = 0`, `f0 = 0xFFFFFFFF` on last blocks else `0`, `f1 = 0`, `one = 1` |
| `streamStart` | block 0 of each digest chain | `0…255`, `1024…1152` | `h0`; `t_lo = 64`, `f0 = 0`, … |
| `streamEnd41` | the key leaf's last block (41-byte tail) | `840…1023`, `1024…1152` | zero; `t_lo = 4,265`, `f0 = 0xFFFFFFFF` |
| `hashA` | `hashStmt` A (leafStmt, 41 bytes) | `0…255`, `512…519`, `840…1023`, `1024…1152` | `h0`; `0x4C`; zero; `t_lo = 41`, `f0 = 0xFFFFFFFF` |
| `hashB1` | `hashStmt` B1 (nodeStmt block 1); key-leaf block 0 (tagWotsLeaf); path blocks 1 (sigNode) | `0…255`, `512…519`, `1024…1152` | `h0`; the tag (`0x4E` / `0x4B` / `0x4D`); `t_lo = 64`, `f0 = 0` |
| `hashB2` | `hashStmt` B2; path blocks 2 | `520…1023`, `1024…1152` | zero; `t_lo = 65`, `f0 = 0xFFFFFFFF` |
| `w43` | WOTS chain steps (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x`, 43 bytes) | `0…255`, `512…519`, `584…599`, `856…1023`, `1024…1152` | `h0`; `0x57`; `i`, `s` of the block's step (per block); zero; `t_lo = 43`, `f0 = 0xFFFFFFFF` |

(`h_in` of `stream`, `streamEnd41`, `hashB2` blocks is the previous block's output, wired by the
shift argument (digest chains) or by element equalities (`hashStmt`, key leaf, path); `w43`'s
`x` and `j`, `hashB1`/`hashB2`'s variable bytes and the `stream` message are inputs.) The
indicator `Ind_kind` is the union of the kind's block intervals in the layout (`FRNodeLayout`),
`Sel = ∪ Ind_kind`. **Dump KAT (P2, S-E2)**: the Lean dump tool writes every kind's `A₀^kind`,
`B₀^kind` rows and target `E` (one block per kind and the per-block patterns as formulas); the
prover's row generator must reproduce them.

### A.7 The node's M and L layout and the pack map

- **Pack**: `f[e]` is the F element whose 16 bytes are bits `[128e, 128e + 128)` of `z`, byte `b`
  = bits `[128e + 8b, 128e + 8b + 8)` low bit first; `c₀ = bytes 0…7`, `c₁ = bytes 8…15` LE. A
  block's element `k` (`k < 128`) is `f[blk·128 + k]`.
- **L** (base block 46,336; element addresses relative to `Lbase = 46,336·128`): per slot `σ`
  (stride `2^14` elements): `sig` 299 elements (`idx` 1, `ots` 133 × 2, `path` 16 × 2), digits
  133 as bit-elements, step selectors 399, position bits 7,552 (the bit-elements `(b, 0^127)`),
  kind selector 3 (one-hot by three product rows and one linear row); the rest zero. **`N_L = 2^15` rows**: the Lr R1CS's rows are the bit-element
  constraints (`b (1 − b) = 0` for every declared bit, the 127 zero coordinates as linear rows).
- **M** (base block 49,152): slot `σ` at `Mbase + (σ−1)·2^20`; templates in the order of
  `compileMux`'s output, each at a power-of-two-aligned base of its size rounded up: imports,
  folds (per level), `Enc₄`, Merkle steps, univariate Lagrange, eq/tensor tables, MBP, sumcheck
  checks, lincheck replay, `evalM` replay, `evalL` replay, gated asserts. **The exact bases are
  the output of `compileMux` and are pinned by its dump** (`probe/fr-irdump/`): the prover's row
  generator must reproduce the dump byte for byte (KAT in P1).

### A.8 The IR (`FRVIR.VProg`): complete op set

Register kinds: `F`, `K`, `D` (digest), `B` (byte string), `N` (ℕ), `Bit`, `AF n` (array of `n` F),
`AK n`, `AD n`. Ops (operands → result; row cost):

| Op | Signature | Semantics | Rows |
|---|---|---|---|
| `piField i → B` | item/field index → bytes | the proof field of A.3 row `i` (or a sub-range) | 0 (an alias into the import cells) |
| `piElem i k → F`, `piDigest i k → D` | field, element index | element `k` of field `i` | 0 |
| `mkAbsorb fields → B` | list of `B` → `B` | the concatenation, zero-padded to 16 | 0 |
| `askSeed vk c hdr → D`, `askAbsorb st msg → D`, `askSqueeze st → D`, `askNode i l r → D`, `askCol i col → D` | | the query; binds the answer | imports |
| `chF a lo → F`, `chK a → K`, `idx a b i → N`, `bitOf n h → Bit` | | challenge maps (A.2) | 0 / 0 / L / L |
| `mulF, addF, mulK, addK, mulKF, invF` | | field ops; `invF`: `a·inv = sel`, `a(1−sel) = 0`, **`inv(1−sel) = 0`** (3 rows, BP-C-R2-m4) | 1/0/3/0/2/3 |
| `eqTable r → AF (2^v)` | `AF v → AF (2^v)` | `eq(r, ·)` | `2^v − 1` |
| `lagrangeS vals λ → F` | `AF 127, F → F` | the degree-≤127 interpolant through `S ∪ Λ` at `λ` (Z2 only) | ≈ 400 |
| `tensorW j r → K` | `N, AK v → K` | `Π_v (1 − r_v + r_v Ŵᵥ(D[j]))` | `2v` |
| `mbp r″ κ pt → F` | `AF 7, F, AK (m−7) → F` | `Ŵ(ρ) = Σ_{j<J_z} κ^j B̂_j(ρ)` at the final point, `J_z` width-128 runs over `m − 7` layers (one evaluation per proof, P1-D6/D7; R4-m2) | `J_z · (m−7) · 128` |
| `walkA rowW colW → F`, `walkB rowW colW → F` | `AF (2^14), AF (2^14) → F` | `Â₀`, `B̂₀` by the circuit walk (`walkE_eq_sum`) with **per-kind-masked row weights** `rowW′[k] = rowW[k] · Σ_{kind : k ∉ pinned(kind)} Ĩnd_kind(r′_blk)` built by `maskRows kindW rowW` (one walk for all kinds) | lincheck replay + `2^14` |
| `kindInd r′ → AF #kinds` | `AF (m−14) → AF 8` | the indicator MLEs `Ĩnd_kind(r′)` (prefix sums over the kind's intervals) | `O(log)` each |
| `evalM τ σ → F × F × F`, `evalL τ σ → F × F × F` | `AF 21, AF 23 → …`; `AF 15, AF 23 → …` | the node's matrix MLEs (kind-selected) | `evalM`/`evalL` replay |
| `selWeight r r′ → F`, `targetMLE r λ r′ → F` | `AF (m−14), AF (m−14) → F`; `AF (m−14), F, AF (m−14) → F` | `ŵ(r′) = Σ_x eq(r′,x) eq(r,x) Sel(x)` (a prefix sum of the tensor over `Sel`'s intervals, R4-m1) and `Ê_w(λ, r′)` of §2.3 step 2 (per kind and pinned position: interval prefix sums and affine-bit MLEs times the position weight) | `O(#kinds · #pinned)` |
| `shiftTarget τ θ → F` | `AF 18, AF 10 → F` | the shift sumcheck's boundary and slot-weight terms (P1-D5) | `O(m)` |
| `splitDigest d → F × F`, `selectHalf b l r → D` | | | 0 / 2 |
| `hashStmt kind fields → D` | `B → D` | `leafStmtF`/`nodeStmtF` | 1–2 H blocks |
| `assertEq a b`, `assertBit b`, `assertZero a` | | checks; a failure returns `false` | 1 linear (gated: 1 product) |
| `assertOneHot s₁ s₂ s₃` | `Bit³` | `s₁s₂ = s₁s₃ = s₂s₃ = 0 ∧ Σ sᵢ = 1` (BP-C-R3-M1) | 3 products + 1 linear |
| `accept` | | `true` | — |

This table is the op set; `gen` uses no other op. Dump format (`probe/fr-irdump/`): one line per
op, `opName operands… → dst`, registers numbered; the Rust generator's output is compared line by
line (P1 KAT).

---

## 10. Fix passes

### Fix pass 1 (revision 2): BP-C-M1…M8, BP-C-m1…m9, BP-E-M1…M8, BP-E-m1…m11 — as recorded in
revision 2 (`de0d708` §10); the crypto review's round 2 marks M1–M6, M8 and all minors closed, M7
partly; the engineering review's round 2 marks M1, M6, M7, m1, m4–m7, m9–m11 closed, the rest
partly. The partial ones are closed below.

### Fix pass 2 (revision 3)

| Finding | Change |
|---|---|
| BP-C-R2-M1, BP-E-R2-M2 (ruling 1) | **One-hot 3-bit selector** per slot, asserted against item 0's kind element; every kind-dependent constant, matrix and pattern selector-linear; the mux construction specified (imports with one address since the item sequence is one; arithmetic ungated; every assertion gated by its activity selector; Merkle steps 4 rows); `compileMux` + `compile_mux_sound` (600 lines) in the plan; honest recount with `≈ 2^18` → templated `2^13` `evalL` rows and `211 k` `evalM` replay rows per slot: **`2^19.86` rows per node (2.21×), 53,792 blocks (1.22×): the node fits `m = 30`**; smallest cut named (§4.3). |
| BP-E-R2-M1, BP-C-R2-M4 (ruling 2) | **The pattern sumcheck**: every per-block constant as a range claim `(R_j, s_j, pat_j)`, all batched with the fixed GF(2)-independent constants `x^j` into one degree-3 sumcheck over the block index (`m − 14` rounds), range and pattern MLEs evaluated by the verifier, selector-linear patterns; **Sh has `m − 14` block rounds + 2 position rounds** (§2.3, §4, §4.1, §5.2 I/S rows); items, `piSize`, error rows recounted. |
| BP-C-R2-M3, BP-E-R2-M3 (b) (ruling 3) | **Every index opened**, duplicates included (B-3, §1.2, A.2, A.4); the extractor's word is indexed by position (§6.2 (3)). |
| BP-C-R2-M2 (ruling 4) | `W` copy loop capped by `capFn t = t`; `final` for `W` proofs above `proofCap` argued (§6.2 (1), §3.3, §5.4). |
| BP-E-R2-M3 (a)–(g) (ruling 5) | (a) `ρⱼ = y^(2^j)` with the shipped inverse-matrix certificate (A.1); (b) as above; (c) `piSize = 754,896` as a checked sum of A.3's rows; (d) the full item table A.4 (`items_length = 9,007`); (e) `reassemble` and `hashStmt` read `stmt` from item 1 (A.5, §4.2); (f) `piField`/`piElem`/`piDigest`/`mkAbsorb`/`rangeMLE`/`patMLE`/`assertOneHot` ops and the array register kinds (A.8); (g) the pack map, the L layout, the M template order, and the `compileMux` dump/KAT requirement (A.7, §8). |
| BP-E-R2-M4 (ruling 6) | `runIR impl` parametrised by `OpImpl`/`OpSpec`; `items` in `FRTranscriptDefs`; the module table has its import column; the serial path recomputed (≈ 13.1 k lines, ≈ 390 s, margin ≈ 1.3×; `serial.py` from S-0 on) (§3, §7). |
| BP-C-R2-m1 | **fixed**: Sh `m − 14` rounds (+2 position rounds), items and `piSize` recounted. |
| BP-C-R2-m2 | **fixed**: B2 has `m − 6` multilinear rounds (A.3 row 10). |
| BP-C-R2-m3 | **fixed**: `evalL` costs `2^18` products unless templated: L's matrices are templated (A.7), `evalL` replay 8,192 rows; counted in §3.1/§4.3. |
| BP-C-R2-m4 | **fixed**: `invF` has the third row `inv (1 − sel) = 0` (A.8). |
| BP-C-R2-m5 | **fixed**: `hashStmt` reads item 1's `stmt`; a leaf child's second block has zero inputs and is excluded from the `one` pattern by the selector (§4.2). |
| BP-E-R2-m1 | **fixed**: no runtime clamp; `compile_runs` under `BoundsOk`; `boundsOk_ext` on the domain (§6.4). |
| BP-E-R2-m2 | **fixed**: `runSeq_eq_runIR` over `(vk, c, π, answers tr)` (§3). |
| BP-E-R2-m3 | **fixed**: the nesting cost stated and the key-lifetime argument given; no cap on `W` (§3.3). |
| BP-E-R2-m4 | **fixed**: import column and the true serial path (§7). |
| BP-E-R2-m5 | **fixed**: L and P moved into the H gap `[46,336, 49,152)`; M ends at 65,536 (§4.3, A.7). |
| BP-E-R2-m6 | **fixed**: S-0's definition of done lists what is proved, what may carry `sorry` on the branch, and that the merged entry has none (§9). |
| BP-E-R2-m7 | **fixed**: `pinned_rank` by a shipped inverse matrix checked by `decide`; `D_inj` a one-line injectivity (A.1). |
| BP-E-R2-m8 | **fixed**: S-0 mid-point kill test on phase Z of `FRVIRSpec` (§7, §9); `FRVIRSpec` budgeted at 1,500. |

**Rejected**: none.

**Interface changes of revision 3 for the running tracks** (keep everything else stable):

| Track | Modules | Change |
|---|---|---|
| S-C | `FRShift` | the shift argument has `m − 14` block rounds + 2 position rounds + 1 univariate (a sumcheck over the block index with a public range indicator `R`), degree 3; `shift_sound`'s statement gains the rounds. `FRSkip`: `ρ` stays parametric; A.1 fixes `ρⱼ = y^(2^j)` with an inverse-matrix certificate (the `decide`-on-rank form is not used). `FRMLE`, `FRSumcheck`, `FRRingSwitch`, `FRSpartan`: **unchanged**. New sibling module `FRPatterns` (not S-C's). |
| S-D | `FRRS`, `FRProximity*`, `FRMerkle` | **unchanged** (duplicate positions are opened again, which `cap_binding` already handles position by position). |
| S-E1 | `FRBlake2s*`, `FRBlockLayout`, `FRBlockChain`, `FRBlockStream`, `FRLeafCircuit` | **unchanged**: the public-pattern facts stay hypotheses (`Patterns`, `ChainLinks`, `IOHolds`); only their later derivation (the pattern sumcheck, L-cert) changed. The digest chain length is `22,619` blocks for every kind (a constant of `FRTranscriptDefs`, consumed later by `FRNodeLayout`, not by S-E1). |
| S-H1 | `FRXDsl`, `FRXField` | `for` **loses the runtime clamp**; `compile_runs` is stated under `BoundsOk P tape` (BP-E-R2-m1); `cost` unchanged; `invF`'s machine form unchanged (the third row is a circuit matter). |
| P1 | prover | one item sequence for both kinds (dummy queries: `P30` asks 2 extra Merkle-node queries of `0^64` per position per level and the node-only phases' items with zero payloads; `L32` asks the node-only phases' items with zero payloads); every index opened; `piSize = 754,896` for every kind (final message padded to 512 B, `P30`'s sibling slots padded with zeros); `reassemble` from item 1; `ρⱼ = y^(2^j)`; the node witness layout is `compileMux`'s dump (KAT). |

### Fix pass 3 (revision 3.1): P1's protocol questions and the crypto review's round 3

| Item | Decision |
|---|---|
| P1 Q1 (P1-D1, pinned point) | **Adopted**: the two-level set `gᵢ = ζ^(2^(i−1))` (`i ≤ 3`), `y^(2^(i−4))` (`i ≥ 4`), `ρᵢ = gᵢ/(1+gᵢ)`, with the inverse-matrix certificate (A.1). Nothing depends on the set beyond `pinned_rank`; it keeps round 1's GF(2^8) accumulation (≈ −0.3 s per `m = 32` leaf against the one-level set). |
| P1 Q2 (P1-D6, batching) | **Adopted**: revision 3's B phase (a sumcheck over `m` bit variables) is withdrawn as unprovable in practice; all `ẑ` claims (`J_z = 4`: Z's quirky claim, Lc's, Sh's, Lr's) are ring-switched together (`J_z × 128` partials, `r″`, `κ`), the batched weight `W` is Ligerito's input, the separate `m − 7` R rounds disappear; the E claim and the point claims on `f` join `W` at B′ (`κ′`). Error rows RS1 `7, 3 / 2^128`, B′ `19/2^128`; the fold rounds are degree 2 in K (§2.3, §5.2). Soundness: ring switching handles any claim that is a GF(2)-linear functional of the bits per packed element (the quirky skip coordinate's Lagrange weights, the multilinear eq weights), and the Ligerito analysis (`fold_preserves`, P2, P3) is unchanged, the weight being the verifier's bookkeeping. |
| P1 Q3 (P1-D7, final message) | **Adopted**: the final message is the level-4 fold, `2^7` K elements (`2^5` at `m = 30`, zero-padded to 4,096 B), the verifier checks `Enc₄(final)[j]` at the `t₄` positions (`2 · 2^7 · 126 = 32,256` products; 32 k rows per slot in the node) and 7 final K rounds reduce `Σ_c W(s,c) final(c)` to one point, where `W` is evaluated once by the MBP. `piSize = 756,496` (A.3). Six levels were rejected: a sixth level costs 124 queries, ≈ 1.2 k compressions and ≈ 7.6 k rows per slot for a saving of ≈ 28 k rows. |
| P1 Q4 (P1-D4, lincheck rounds) | **Adopted**: 14 multilinear rounds of degree 2 over the block's 14 position bits; the lincheck's output is a plain multilinear claim `ẑ(r′_blk, r_k)`; the walk takes the row weights at `r_row` (Lagrange at `λ` on the skip coordinate) and `eq(r_k, ·)` column weights. Revision 3's "9 rounds + L3" (the ninth variable did not exist) is withdrawn; the L3 row (`2^-120.99`) disappears. |
| P1-D2 (`one` forced by `a∘b = z + e`) | **Adopted and generalised**: the zerocheck's summand is `Sel · ((A₀z)∘(B₀z) − z − E)` with the public target `E` on every `(0,0)`-row position (`one`, slot 8's words, the layout's zero fields, the chain block's constants). BP-C-M5's `one` claim is gone. |
| P1-D3 (constants as constant rows) | **Adopted** for the leaf's chain block (rows `(0,0)` with `E` = the constant) and for the node's stream blocks (`t_lo`, `f0` per block through `E`; the unified stream length makes them kind-independent). |
| P1-D5 (shift with both endpoints and the 10-round slot collapse) | **Adopted** (§2.3 step 4, §4.1): `eq(τ,·)·Out + (shift(τ,·) + κ_s eq(0,·))·In` with `s`, `h` (leaf) or `h0` (node chains) in the target, then 10 collapse rounds with the verifier-computed slot weight (the `d` slot at 520…775 is handled by the weight). Rows S1 `27/2^128`, S2 `2/2^128` × 26 rounds. **The pattern sumcheck of revision 3 is withdrawn** (P1-D2/D3/D5 cover every public constant; the public inputs and padding are point claims on `f`). |
| P1-D8 (`π` field order) | Not adopted: A.3's grouped order stands (the circuit's imports read cells of the trace, not of `π`; `reassemble` fixes the map); P2 adopts A.3/A.4. |
| ≥ 15 % cut on the `m = 30` path | **None found at the protocol level without a security cost**: the stream leaf is `2^16` compressions × `2^14` bits (the block is 14,720 gates, so `m = 30` is minimal), the node uses 82 % of its cube, level 0 dominates Ligerito, and the Merkle hashing volume is the codeword's. What this revision removes from the `m = 30` path: the B sumcheck (which P1 never implemented), the separate R rounds (−1 pass over `f`), L3 and the pattern sumcheck (−1 sumcheck over the blocks). The link overrun (P1: 3.7 s against 3.1 s) is engineering against K's measured kernels (node 0.81 s, `m = 30` leaf 0.97–1.01 s ⇒ link 2.1–2.8 s): P2's list (K×K Karatsuba, fused level-0 pass, arena, Merkle overlap, trace recording, zero-block skipping in node mode, GF(16)² round 1). |
| BP-C-R3-M1 | **Fixed**: one-hot by three product rows `s_L s_P = s_L s_N = s_P s_N = 0` and `Σ s = 1`; `assertOneHot` costs 3 products + 1 linear (A.8); the control "a three-hot assignment fails" (§5.6). |
| BP-C-R3-M2 | **Moot by removal**: no pattern sumcheck and no fixed-constant batching of slot-valued claims exist; every public constant is pinned bit by bit by the zerocheck's target at its own random point; the shift batching by `1, y` acts on bit-valued summands (unchanged). |
| BP-C-R3-m1 | **Fixed**: slot-valued facts (`vk`, `cᵢ` in the seed cells; the padding cells) are point claims on `f`, batched at B′ (§4.3, §5.2). |
| BP-C-R3-m2 | **Fixed**: `J_z`, `J_f` are `FRNodeLayout` constants; `batch_bad_le` takes them from there (§5.2). |

**Interface changes of revision 3.1 for the running tracks:**

| Track | Modules | Change |
|---|---|---|
| S-0 | `FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec` | the item sequence of A.4 (473 FS items; no L3, S3, I, B, R items; RS0/RS1, Pf added), `piSize = 756,496` with A.3's rows, the two-level `ρ`, the ops `selMLE`/`targetMLE`/`shiftTarget`/`mbp` (new signature) and `assertOneHot` (3 + 1 rows), `rangeMLE`/`patMLE` removed; `gen`'s phases Z, Lc (14 rounds), Sh (P1-D5), Lr, RS, E, B′, P (with Pf). |
| S-C | `FRSkip`, `FRShift`, `FRRingSwitch`, `FRSpartan`, `FRSumcheck`, `FRMLE` | `FRSkip`: `ρ` is A.1's two-level set (still a parameter of the lemmas; the inverse certificate is for that set). `FRShift`: P1-D5's form (block rounds with `eq·Out + (shift + κ_s eq(0,·))·In`, endpoints in the target, 10 collapse rounds, two chains batched by `1, y`), no univariate round. `FRRingSwitch`: the weight `Ŵ` of a quirky claim and of a multilinear claim, and the κ-batching of `J_z` claims before Ligerito. `FRSpartan`: the zerocheck's summand carries `Sel` and the public target `E` (degree 3), and the lincheck has 14 rounds. `FRSumcheck`, `FRMLE`: unchanged. `FRPatterns` is withdrawn; `FRPubTarget` (small) replaces it. |
| S-D | `FRRS`, `FRProximity*`, `FRMerkle` | unchanged (the final message's size and the final rounds are `FRSoundnessLigerito`'s concern). |
| S-E1 | `FRBlake2s*`, `FRBlockLayout`, `FRBlockChain`, `FRBlockStream`, `FRLeafCircuit` | the block R1CS gains the public target: `Holds blockR1CS_E` (rows `(0,0)` at the constant positions, `z = E` there), `one = 1` delivered by it; `leaf_sound`'s hypotheses are `Holds blockR1CS_E` per block and `ChainLinks z s h` (links and both endpoints), no `Patterns`/`IOHolds`; the stream block's `t_lo`, `t_hi`, `f0`, `f1` positions are `(0,0)` rows; the walk takes general row weights (the quirky `λ` coordinate). |
| S-H1 | `FRXDsl`, `FRXField` | unchanged. |
| P1 → P2 | prover | adopt A.3/A.4 (the item sequence with dummies, `piSize = 756,496`), `reassemble` from item 1, the node mode; keep P1-D1…D7 as adopted. |

### Fix pass 4 (revision 3.2): the crypto review's round 4

| Finding | Change |
|---|---|
| BP-C-R4-M1 | **Fixed**: three `hashStmt` blocks per slot with kind-independent constants — A (`t = 41`, final) on the leaf message, B1–B2 (`t = 64` non-final, `t = 65` final, linked) on the node message; `cᵢ = (s_L + s_P)·out_A + s_N·out_B2`; `hashStmt_sound` restated as the two unconditional digests (§4.2); H = 46,022 blocks, `usedH` and `Sel` follow (§4.3); `sizes.py`. |
| BP-C-R4-m1 | **Fixed**: `Sel` sits in the zerocheck's **weight**, `ŵ = MLE(eq(r,·)·Sel(·))`, rounds of degree 3, final value `ŵ(r′) = Σ_x eq(r′,x) eq(r,x) Sel(x)` as a prefix sum over `Sel`'s intervals; `A = I ⊗ A₀`, `B = I ⊗ B₀` (never `Sel ⊗`); chosen over the degree-4 factor form for prover cost (the eq table is simply zeroed outside `Sel`) and because every row stays as tabled (§2.3 step 2, §4, A.8 `selWeight`). |
| BP-C-R4-m2 | **Fixed**: RS1 is one joint row `(7 + J_z − 1)/2^128 = 10/2^128`; `Ŵ` needs `J_z = 4` MBP runs: verifier +9.6 k products (node ≈ 3.7·10^5, leaf ≈ 1.2·10^5), replay +9.6 k rows per slot (§3.1, §4.3, §5.2, A.8 `mbp`). |

**Margins after revision 3.2** (`sizes.txt`): `piSize` 756,496 (1.39×); items 8,896 of 10,240
(1.15×); hashed stream 22,506 compressions per slot; **node 54,111 of 65,536 blocks (1.21×)**; **M
rows 1,019,364 = `2^19.96` of `2^21` (2.06×)**; extractor `2^47.11` (fuel 1.31×, `B` 1.85×); error
maximum `2^-120.36 + 2^-144 ≤ εR`; verifier ≈ 1.2·10^5 (leaf) / 3.7·10^5 (node) products.

**Interface changes of revision 3.2:**

| Track | Modules | Change |
|---|---|---|
| S-0 | `FRVIR`, `FRVIRSpec`, `FRTranscriptDefs` | `gen`: `hashStmt` is three blocks per slot (A, B1, B2) with the selection `cᵢ = (s_L + s_P)·out_A + s_N·out_B2`; the op `selWeight r r′` replaces `selMLE`; `mbp` takes `κ` and runs `J_z = 4` programs; Z's final value is `ŵ(r′)·(â b̂ − ẑ − Ê)`. No change to the item sequence or `piSize`. |
| S-C | `FRSpartan` | the zerocheck's weight is `MLE(eq(r,·)·Sel(·))` (degree 3), with the prefix-sum lemma for `ŵ(r′)`; `A, B` are `I ⊗ A₀, I ⊗ B₀`; the lincheck's reduction to `ẑ(r′_blk, ·)` is then as the paper's. `FRRingSwitch`: the RS1 lemma states the joint bound `(7 + J_z − 1)/2^128` (one phase). |
| S-E1 / S-E | `FRBlockStream`, `FRWots` | `FRBlockStream`: unchanged (the three `hashStmt` blocks are stream blocks with constants `(41, final)`, `(64, 0)`, `(65, final)` in `E`). `FRWots`/`hashStmt_sound`: three blocks, the statement of §4.2, the link row B1 → B2. `FRNodeLayout`: `usedH` has 6 `hashStmt` blocks; L's base moves to 46,336. |
| P2 | prover | three `hashStmt` blocks per slot in the node witness; `Sel` zeroes the zerocheck's eq table outside the used blocks (no separate factor); `J_z = 4` MBP state vectors in the native `acc`. |

### Stage-review changes 1 (revision 3.3): S-D and S-E1 reviews

| Finding | Change |
|---|---|
| S-E1-M2 + S-E1-M1 (per-kind matrices, ruling 1) | **Per-kind block matrices** `A = Σ_kind Ind_kind ⊗ A₀^kind` (likewise `B`) with per-kind targets; A.6's normative table of kinds (`chain`; `stream`, `streamStart`, `streamEnd41`, `hashA`, `hashB1`, `hashB2`, `w43`) with their `(0,0)` rows and `E` values, `h_in = h0` pinned on every fresh-hash block (hashStmt A and B1, WOTS steps, the key-leaf's first block, the path blocks' first, the digest chains' first); the convention "constants as `(0,0)` rows with their bit in `E`, never `(one,one)`" made normative for the Lean and the prover; the lincheck's walk uses **per-kind-masked row weights in one walk** (`rowW′[k] = rowW[k] · Σ_{kind ∌ k} Ĩnd_kind`, `2^14` products, `O(log)` indicator MLEs) rather than one walk per kind (§2.3 step 3, A.8 `walkA`/`kindInd`); the zerocheck's final value is `ŵ(r′)(â b̂ − ẑ) − Ê_w(λ, r′)` with `Ê_w` per kind and pinned position (§2.3 step 2, A.8 `targetMLE`); error rows unchanged (the indicators and targets are verifier-computed); a dump KAT of every kind's rows and target against the prover's (A.6, P2/S-E2). M/L blocks have no kind. |
| S-E1-M1 (wiring, ruling 2) | `stmt` is the padded statement-hash message blocks: `tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64` or `tagNode ‖ c₁ ‖ c₂ ‖ 0^63`, 128 B for every kind; the `hashStmt` messages equal item 1's payload elements 0–3 (A, B1) and 4–7 (B2) by 8 element equalities per slot; `V`'s `stmtOk` checks the tag and zero bytes and hashes; `hashStmt_sound` restated (§4.2); `piSize = 756,560` (A.3), the stmt absorb 128 B (A.4); `reassemble` unchanged (`stmt := payload₁`). Cheaper sound alternatives: none (byte-shifted windows are not F-linear). |
| S-D-M1 (windows, ruling 3) | `Bad`'s in-play windows are the 32-byte windows at query offsets `≡ 8 (mod 16)` plus the answers (§5.1), count `2^-144` unchanged; `MerkleEnc`'s `carried` for node queries, absorbs (`carried_absorb`), seeds and squeezes; `parseNode`/`parseCol` check the level byte (A.2). |
| S-D results (ruling 4) | §5.3 and B-5 updated to the proved form `C_mca = k e + n` (counting argument; `pcsLevels_ok`), P1 row `≤ 2^-214`, FR-R8 closed (§9). S-D-m1: `coeffs_of_values`/`coeffs_spec` and the twins `interpF`/`encF` assigned to L-pcs (stage S-D2, `FRRSEval`, 400 lines), consumed by L-ext and `FRVIREval` (§7). S-D-m4: the fold order (bit 0 first; coordinate `v` = the round that folded bit `v`) and `eqBits = FRMLE.eq` in that order (A.2, `eqBits_eq_eq` in `FRTranscriptDefs`). S-D-m2/m3/m5: controls and remarks as the review proposes (`fold_preserves_fails_at_bad` added; `n ≤ 2^20` as one `FRTranscriptDefs` constant; the GF(5) instance scoped). |
| S-E1-m1 | the size facts (first tag 7 B, others 8 B, payloads `≡ 0 mod 16`, dummy queries `≡ 8 mod 16`) are `FRFormat`/`FRVIRSpec` obligations stated with `items` (A.4). |
| S-E1-m2 | `one` is element 9 (A.6). |
| S-E1-m3 | `stream_complete` covers the hashStmt blocks' `(t, fin)` targets; `h_in = h0` and the constant bytes are the kinds' pins (A.6). |
| S-E1-m4 | §4.1 displays the proved `leaf_sound` (`n ≥ 1`, used blocks, `[DecidableEq R]`, `HoldsE` + `ChainLinks`). |
| S-E1-m5 | a two-block stream KAT in the dump tool (compiled, not kernel). |

**Margins after revision 3.3** (`sizes.txt`): `piSize` 756,560 (1.39×); items 8,896 of 10,240
(1.15×); hashed stream 1,440,400 B = 22,507 compressions per slot; **node 54,369 of 65,536 blocks
(1.21×)**; **M rows 1,052,152 = `2^20.00` of `2^21` (1.99×)**; extractor `2^47.11` (fuel 1.31×, `B`
1.85×); **error maximum `2^-120.36 + 2^-144 ≤ εR`** (no row changed: the per-kind indicators and
targets are verifier-computed; P1 is now `≤ 2^-214`); verifier ≈ 1.2·10^5 (leaf) / 3.9·10^5
(node) products (T_V **estimate** 85–125 ms of 205.9).

**Interface changes of revision 3.3:**

| Track | Modules | Change |
|---|---|---|
| S-0 | `FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec` | `stmt` 128 B (the padded hash message blocks), `piSize = 756,560`, the stmt absorb 128 B; `MerkleEnc` instance with `carried` for node/absorb/seed/squeeze queries and `carried_absorb`, level-byte checks in `parseNode`/`parseCol`; `eqBits_eq_eq` and the fold order; the `n ≤ 2^20` constant; `gen`: `stmtOk` parses `stmt`'s tag/zero bytes, the ops `kindInd`, `maskRows`, `targetMLE r λ r′`, `walkA rowW colW`; the item-size facts for `item_aligned`. |
| P2 | prover | the `(0,0)`-row convention with `E` bits for every pinned position (replace the `(one,one)` rows of `circuit.rs`); per-kind block matrices and targets as A.6 with a dump KAT against the Lean; `stmt` as the hash message blocks; the lincheck's masked row weights; `Ê_w` in the zerocheck's final check. |
| S-E2 (`FRWots`, `FRVIRCompile/Mux/Eval`, `FRNodeLayout`, `FRNodeCircuit`) | the kinds of A.6 as `blockR1CS` targets (`hashA`, `hashB1`, `hashB2`, `w43`, `stream`, `streamStart`, `streamEnd41`), `Ind_kind` intervals in `nodeLayout`, `hashStmt_sound`'s new statement, 8 `stmt` equalities and the per-kind row-weight adjustment rows per slot, `evalM` unchanged. |
| S-F (`FRVerifier`) / S-G (`FRSoundness*`) | `V`'s zerocheck final value and lincheck as §2.3; `Bad`'s windows at offsets `≡ 8 mod 16` in `FRLog.bad_step_le`; `final` discharges `HoldsE` per kind from the zerocheck, `h_in = h0` of fresh-hash blocks from the kinds' pins (not from point claims), the chain links from the shift sumcheck, `Padded` from the three point claims per chain. |
| S-D2 (L-pcs) | `FRRSEval`: `coeffs_of_values`, `coeffs_spec`, `interpF`, `encF`. |

