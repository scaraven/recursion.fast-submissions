# `flock-recursive`: entry blueprint (normative)

Status: phase 1 (B), **revision 3** (stage S-0, part 1) after two rounds of adversarial review
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
| `piSize` (both kinds) | 754,896 B = 737 KiB | `proofCap` 1,048,576 | 1.39× |
| trace items (both kinds) | 9,007 | `qV = 10,240` | 1.14× |
| hashed trace bytes / compressions | 1,447,616 / 22,619 | — | — |
| node circuit blocks | 53,792 | 65,536 | 1.22× |
| M rows per node | 949,810 = `2^19.86` | `N_M = 2^21` | 2.21× |
| extractor steps (`m = 30` node) | `2^47.11 + 2^11 t` | `fuel = 2^47.5 + 2^12 t`; `B = 2^48 + 2^16 t` | 1.31×; 1.85× |
| error per fresh query | `2^-120.36 + 2^-144` | `εR = 2^-120.093` | — |
| verifier F-products | leaf ≈ 8.2·10^4, node ≈ 3.3·10^5 | `T_V` 205.9 ms (≈ 90–110 ms, **estimate**) | ≈ 2× |
| output words (node) | `2^19.3` | `outCap = 2^24` | — |

### 0.1 Decisions

| Id | Decision | Reason |
|---|---|---|
| **B-1** | **Tree leaves are single `m = 32` SNARKs of `2^18` compressions.** The stream leaf is `m = 30`. | The runner hashes the 64 statements `leafStmt (chainEnd sᵢ 2^18) 2^18` itself (`Tree.lean`); the leaf clause of `Rel` demands the chain, so a leaf made of signed segments is uncertifiable (`∀ vk`, design §2.2) and one of two fresh-query segment SNARKs exceeds `proofCap`. K measures the `m = 32` leaf at 3.73–3.86 s and 3.81 GB peak (K §3, §4.4). |
| **B-2** | **Nodes are `m = 30`, one shape, one program `P30`.** `L32` and `P30` have **one item sequence** (every phase sized for the larger kind; a kind's unused items are dummy queries with zero payloads, §1.2) so that every trace element has one address. A node's child slot is replayed by **one program `gen Mux`** whose kind-dependent constants, matrices and public patterns are selector-linear in a **one-hot selector `(s_L, s_P, s_N)`** of three L bits (§4.3). Exact count 53,792 of 65,536 blocks (1.22×), M rows `2^19.86` of `N_M = 2^21` (2.21×). | K: an `m = 31` node (≈ 1.9 s) puts the stream link over its cap, so `m = 30` is hard. A node's replayed verifier does not depend structurally on its own or its children's variants (rulings 1 and 2 of fix pass 2); the fixed point is cut by fixed dimensions (§4.3). Fallback if `nodeLayout` overflows: the enumeration of the occurring pairs `(L32, L32)`, `(P30, P30)` with a public pair byte, never `m = 31`. |
| **B-3** | **Five levels**, rates 1/2 … 1/32, rows 64 then 16, `eᵢ = ⌊(nᵢ − kᵢ)/2⌋`, queries **290, 178, 145, 132, 126**, caps at depth 9, 8, 8, 8, 7, final `k₅` K-elements in the clear (16 at `m = 32`, 4 at `m = 30`, padded to 16). **Every index is opened**, duplicates included. | BP-C-M3, BP-C-R2-M3: the item sequence is a constant. |
| **B-4** | **F = BF64[y]/(y² + y + β), β = x^63; K = F[u]/(u² + u + α), α = β·y** (S-A), through CompPoly's allowlisted `Ext` over `BF64`, two-`UInt64` twins. | S-A journal; no off-allowlist copy. |
| **B-5** | **Own mutual correlated agreement for lines in the UD regime over K-valued words and `C_K`**, constant `C_mca(n,k,e) ≤ 2^60` a parameter fixed by the closing proof (§5.3). | I §2.5; any polynomial constant is `≤ 2^-190` over K. |
| **B-6** | **Wiring:** regions H (BLAKE2s blocks), L and P (in the H gap), M (element rows). A child's trace is the message slots of its chain's H blocks, read by irregular matrix entries evaluated with eq tables (one product per entry); M-internal patterns are templates; BLAKE2s matrices by the walk; the L matrices templated too. **Every per-block public constant is a range claim inside one pattern sumcheck** (§4). | BP-E-R2-M1: whole-cube point claims are false for the node; T_V is not binding. |
| **B-7** | **The verifier is an interpreter `runIR impl` of a straight-line IR**, parametrised by an op-implementation record `OpImpl` (`evalM`, `evalL`, `walk`, `mbp`, `lagrangeS`); `FRVIRSpec` states each phase's semantics against the record's specification; the circuit's M and L rows are compiled from the same IR (`compile`), with the per-slot mux as a compiler mode (`compileMux`, `compile_mux_sound`). | BP-E-R2-M4 (no cycle), BP-E-R2-M2 (a construction and a theorem for the mux). |
| **B-8** | **`E := fun c π L => (ext.run (extractorInput c π L) (fuel t)).bind decodeWit`**; `XIR` with affine-in-`t` caps, `compile_runs` as `∃ n ≤ cost P t` under `BoundsOk`, counted on the compiled code; the `W` copy is capped by `t`. | Probed; BP-E-M5/M6, BP-C-R2-M2, BP-E-R2-m1. |
| **B-9** | **Prover: std Rust, one `prover.s`, CPUID dispatch, AVX2 + VPCLMULQDQ-256 tier of record.** | K. |
| **B-10** | **`ε = 15/2^124`; `δ = 0` (`P := encode`, kind `W`); `qV = 10,240`; `fuel t = 211,106,232,532,992 + 4,096 t`.** Claim: `{"error": "15/21267647932558653966460912964485513216", "completeness_error": "0", "qV": 10240, "fuel_base": 211106232532992, "fuel_per_word": 4096}` (renders: `r2/render-r2.log`). | §5.2; BP-E-M7; §6.3. |

### 0.2 Drift (T §6's D-1 … D-17 stand)

| # | Here | Paper / repository | Reason |
|---|---|---|---|
| D-2′ | five levels, `e = ⌊(n−k)/2⌋`, every index opened, final in the clear | five Johnson levels / six UD levels, stratified queries | B-3 |
| D-9′ | F = BF64[y]/(y²+y+x^63), K = F[u]/(u²+u+x^63 y) | GHASH; `F128[u]/(u²+u+x⁻¹)` | B-4 |
| D-13′ | node `m = 30`, one program, one item sequence for all kinds, one-hot child selector, trace = H message slots, pattern sumcheck | tower, deferred accumulator | B-2, B-6 |
| D-18 … D-22 | IR interpreter + compiled circuit; `decodeWit ∘ run`; MCA over K; ymm tier; completeness through `W` | — | B-7, B-8, B-5, B-9, B-10 |

---

## 1. Formats

### 1.1 The proof `π`

Kinds: **`W`** (`π = WitnessSending.encode w` exactly; decided with no query, §3); **`L32`**,
**`P30`-leaf (`'P'`)**, **`P30`-node (`'N'`)**: `π = hdr ‖ stmt ‖ body`, `|π| = piSize =
754,896` for all three (A.3), any other length rejected with no query.

```
hdr  (48 B) = kindByte(1) ‖ m(1) ‖ zero(14) ‖ pub(32)      kindByte 0x4C 'L' | 0x50 'P' | 0x4E 'N'; m 32 | 30 | 30
stmt (64 B) = 'L','P': enc64 n ‖ h ‖ zero(24)   (n = 2^(m−14), checked)      'N': c₁ ‖ c₂
body        = PIOP messages ‖ cap₀ … cap₄ ‖ final (512 B) ‖ columns ‖ siblings     (A.3)
```

| part | bytes |
|---|---|
| `hdr`, `stmt` | 48 + 64 |
| PIOP messages (A.3's rows 2–16) | 21,856 |
| caps `(512 + 256 + 256 + 256 + 128) × 32` | 45,056 |
| final message `16 × 32` (P30: 4 K-elements then zeros) | 512 |
| columns `290 · 1,024 + 581 · 256` | 445,696 |
| siblings `32 × 7,552` (P30: its `5,810` real ones, the rest dummy zeros) | 241,664 |
| **`piSize`** | **754,896 (737 KiB, 72 % of `proofCap`)** |

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

Counts (`sizes.py`): FS items 584, column queries 871, Merkle-node queries 7,552: **9,007 items**
(`qV = 10,240`, 1.14×); hashed stream 1,447,616 B = **22,619 compressions**.

### 1.3 What each kind proves; `reassemble`

`'L'`, `'P'`: `c = leafStmt h n`, SNARK of `chainEnd s n = h`, witness `.leaf s n`. `'N'`: `c =
nodeStmt c₁ c₂`, SNARK of `acc vk c₁ p₁ ∧ acc vk c₂ p₂` for the committed `p₁, p₂`, witness
`.node c₁ c₂ p₁ p₂`. `W`: `Rel` directly. A child's `πᵢ = reassemble trᵢ` (A.5): `hdr` from item
0's payload bytes `64…111`, `stmt` from item 1's payload, every other field from its item.

### 1.4 The extractor's output

`witWords`: a node of two children `≈ 641,905 = 2^19.3` words of `outCap = 2^24`; a leaf 6
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

0. `seed`; `absorb(stmt)`. 1. `absorb(cap₀)`.
2. **Z**: **Z1** `r`, `m* − 13 = 19` free coordinates (10 squeezes; `P30` uses 17); **Z2**
   `absorb(P^{ab} ‖ P^z)`, `λ`; **Z3** `m* − 6 = 26` rounds of degree 3 (`P30`: 24 real + 2 dummy).
3. **Lc**: **L1** `α`; **L2** 9 rounds of degree 2; **L3** univariate round over `S`.
4. **Sh** (range-restricted shift over the block index; both chains of a node batched by the
   constant `c = y`): **S1** `τ` (`m* − 14 + 8 = 26` coordinates, 13 squeezes); **S2** `m* − 14 =
   18` block rounds + 2 position rounds, degree 3; **S3** univariate round.
5. **I, the pattern sumcheck** (§4): **I1** `θ` (18 coordinates, 9 squeezes); **I2** 18 rounds of
   degree 3 over the block index; the final check uses the range and pattern MLEs the verifier
   computes and the selector-weighted pattern sums; its claims on `ẑ` are evaluations at fixed
   in-block positions.
6. **Lr** (node): point (8 squeezes), 15 zerocheck rounds (degree 3), `κ_L`, 15 lincheck rounds.
7. **B**: `κ`; `m* − 6 = 26` multilinear rounds of degree 2; one univariate round (**B3**).
8. **R**: `absorb(s_v)`; `r″` (4 squeezes); `m* − 7 = 25` rounds of degree 2; the MBP evaluation.
9. **E** (node): point (11 squeezes), 21 zerocheck rounds (degree 3), `κ_E`, 23 lincheck rounds.
10. **B′**: `κ′`.
11. **P**, levels 0 … 4: `ℓᵢ` fold rounds (K), `absorb(capᵢ₊₁)` / `absorb(final)`, position
    squeezes, per position the column query then its Merkle-node queries leaf level first (11, 10,
    8, 6, 5 of them; `P30`'s last 2 per level are dummies), `κ_c` and the consistency batching.
12. Accept iff every check passed.

### 2.4 Parameters

| Name | Value |
|---|---|
| `m₀` | 14 |
| skip | `k_s = 6`, `S`, `Λ`, pinned `ρⱼ = y^(2^j)` (A.1) |
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
is the first `hashStmt` op (its inputs from item 1's `stmt`). **`FRVIRSpec`**: `semIR (genPhase …)
(vk, c, π, answers) = …` per phase; `queries_le : ∀ H c π, ((V vk c π).queries H).length ≤ 10240`
by `items_length` (closed form); `runSeq_eq_runIR : asks tr = items → (runSeq tr (V vk c π) =
some true ↔ semIR (gen k) (vk, c, π, answers tr) = accept)`.

### 3.1 Operation counts (`sizes.py`)

| Work | `L32` | `P30` node |
|---|---|---|
| column folds `Σ tᵢ rowsᵢ` K×F | 46.6 k (F: 2 each) | same |
| final `Enc₄` `2 k₅ t₄` | 4.0 k | ≤ 4.0 k |
| univariate rounds (Z2, L3, S3, B3) at 128 points | 2 k | 2 k |
| eq tables, tensor weights, K arithmetic | ≈ 15 k | ≈ 15 k |
| sumcheck rounds | ≈ 2 k | ≈ 2 k |
| MBP `25 · 128` F + `25 · 2^14` XOR | 3.2 k | 3.2 k |
| walks `Â₀, B̂₀` | `1.2·10^5` XOR | `1.2·10^5` XOR |
| node: `evalM` irregular `2 × 74,920` + eq tables `2 × 22,619 + 2^14` + templates + walks; `evalL` templated | — | ≈ 2.4·10^5 F |
| **F-products** | **≈ 8.2·10^4** | **≈ 3.3·10^5** |

### 3.2 `T_V` (**estimate**; the S-B probe replaces it)

Root check (`P30` node): trace digest at the spec hash's speed (1.45 MB, 15–25 ms on the
runner); `SigOk` 0.3 ms; parsing 2 ms; products `3.3·10^5 × 70 ns = 23 ms`; XORs 8 ms;
interpreter overhead ≤ 2× on the arithmetic: **≈ 75–110 ms against 205.9 ms**.

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

Batch R1CS in Flock's form: `z ∈ GF(2)^(2^m)` is `2^(m−14)` blocks of `2^14` positions; `A = Sel ⊗
A₀`, `B = Sel ⊗ B₀`, `C = Sel ⊗ I`; plus the shift sumcheck, the pattern sumcheck, the element
R1CS over `f = pack z` and the L R1CS (node). Block layout A.6; `one = 1` and every per-block
public constant is a **pattern claim**:

**The pattern sumcheck** (one per proof; BP-E-R2-M1, BP-C-R2-M4). Claims `j = 1 … J ≤ 64`, each a
triple `(R_j, s_j, pat_j)`: a block range `R_j` (a public interval of blocks), an in-block
position set `s_j` (a slot or bit), and a public pattern `pat_j : block → GF(2)^|s_j|` that is
**selector-linear**: `pat_j(i) = Σ_κ s_κ · pat_{j,κ}(i)` with `s_κ` the kind-selector bits of the
slot the range belongs to (or constants for the proof's own blocks). The claim: `∀ i ∈ R_j,
z[blk i, s_j] = pat_j(i)`. All claims are batched with the **fixed GF(2)-independent constants
`c_j := x^j ∈ BF64 ⊂ F`** (distinct monomials of the GF(2)-basis of BF64; the differences
`z − pat_j` are GF(2)-valued since the selectors are one-hot Boolean bits, so `Σ_j c_j d_j(i) ≠ 0`
whenever some `d_j(i) ≠ 0`: no error for the batching) into one degree-3 sumcheck over the block
index: `Σ_i eq(θ, i) · Σ_j c_j · R_j(i) · (z[blk i, s_j] − pat_j(i)) = 0`, `m − 14` rounds; at the
final point `r` the verifier needs `R̃_j(r)` (range-indicator MLEs: a prefix-MLE closed form,
`O(m)` each), the pattern MLEs `p̃at_{j,κ}(r)` (constants on ranges or affine in `i`: `O(m)`), the
selector bits `s_κ` (evaluation claims on `ẑ` at the L bits' positions) and `ẑ(r, s_j)` (one
evaluation claim per distinct position set, batched in **B**). Lemma `pattern_sound`: if some claim
is false, the sumcheck's doom is `(m − 14) · 3/2^128 + (m − 14)/2^128` (rounds + the point). Claims
used (A.7): `one` on the used blocks; `Sel`'s complement blocks zero; `h_in = h0` at each chain's
first block; `t_lo`, `f0` on each chain (affine / constant on the range, with the last block
selector-linear); the padding of each chain's last block; `P`; the three selector bits' `Σ = 1`
and the kind-byte equality (linear rows in Lr are an alternative; the pattern sumcheck is used).

### 4.1 The leaf circuit (`FRLeafCircuit`)

`2^(m−14)` chain blocks (`h_in = h0`, message `0x43 ‖ dᵢ ‖ 0^31`, `t_lo = 33`, `f0 = 0xFFFFFFFF`
as patterns; the stream block of §4.2), **Sh**: `Σ_i eq(τ,i) R(i) (z[blk i, 256…511] − z[blk i+1,
520…775]) = 0` with `R = [0, n−1)`, `m − 14` block rounds, 2 position rounds and a univariate
round (`shift_sound`); **IO**: `in(0) = s`, `out(n−1) = h` as pattern claims on blocks `0` and
`n − 1`.

```
leaf_sound : ∀ z s h, Boolean z → (∀ i < 2^(m−14), z[blk i, one] = 1) → (∀ i, Holds blockR1CS (z ∘ blk i)) →
  Patterns z → ChainLinks z → IOHolds z s h → chainEnd s (2^(m−14)) = h
```

(S-E1 takes `Patterns`, `ChainLinks`, `IOHolds` as hypotheses; their derivation from the pattern
and shift sumchecks is L-cert's.)

### 4.2 Stream block, digest chain, WOTS, statement check

Stream block: `h_in`, message, `t_lo`, `f0` inputs; `block_sound` (`one = 1` explicit). Digest
chain of the hashed stream `B` (`N = ⌈|B|/64⌉ = 22,619` for every kind, since the stream is one
layout): `h₀ = h0`, `hᵢ₊₁ = compress hᵢ Bᵢ tᵢ fᵢ 0`, `traceDigest tr = le h_N`
(`blake2s_chain`). Child slot `σ ∈ {1, 2}` reads stream element `e` at element address
`(chainBase_σ + ⌊e/4⌋)·128 + 4 + e mod 4`, `chainBase_1 = 0`, `chainBase_2 = 22,619`. **WOTS**:
133 chains × 3 selector steps + 67 leaf blocks + 32 path blocks = 498 blocks per slot.
**`hashStmt`**: 2 blocks per slot; inputs from **item 1's payload** (`stmt`), variant
selector-linear (`'L'`/`'P'`: `leafStmt h n` in one block, the second block's inputs zero and its
`one` excluded from the used set by the selector-linear `one` pattern; `'N'`: `nodeStmt c₁ c₂` in
two); output asserted equal to item 0's `c`. `wots_sound`, `hashStmt_sound`.

### 4.3 The node circuit: layout, mux, counts

| Region | Base (blocks) | Content | Blocks |
|---|---|---|---|
| **H** | 0 | chain 1 `[0, 22,619)`, chain 2 `[22,619, 45,238)`, `hashStmt` 4, WOTS 996, spare 8; all-zero blocks elsewhere | 46,246 |
| **L** | 46,336 | bits (A.7): per slot the signature (4,772 B), the WOTS digits and selectors, the position bits as bit-elements, the one-hot kind selector `(s_L, s_P, s_N)`; `N_L = 2^15` rows | 124 (allotted 2,816: the gap to M) |
| **P** | 49,151 | `vk ‖ c₁ ‖ c₂` then zeros | 1 |
| **M** | 49,152 (`3·2^14`) | `N_M = 2^21` elements = 16,384 blocks, ending at 65,536; slot `σ`'s rows at `Mbase + (σ−1)·2^20` | 7,421 used |
| **total** | | | **53,792 of 65,536 (82 %, 1.22×)** |

**The mux (B-2, B-7).** Each slot is replayed by `gen Mux`, one program with the item sequence's
shape, whose kind-dependent data are selector-linear:

- the **selector** `(s_L, s_P, s_N)` (three L bits): rows `Σ_κ s_κ = 1` and `kindElem = Σ_κ s_κ ·
  kindConst_κ`, where `kindElem` is the first element of item 0's payload bytes `64…79` (`hdr`'s
  `kindByte ‖ m ‖ zero(14)`), both linear in `z` (pattern claims);
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
- the **kind-dependent patterns** of the child's chain (`t_lo = |B|` and `f0` at the last block,
  the padding) are selector-linear pattern claims (§4).

`compileMux : VProg → rows` is `compile` in "gated" mode; **`compile_mux_sound`**: if the rows hold
with a one-hot selector equal to kind `κ`, then `semIR (gen κ) (vk, cᵢ, πᵢ, answers) = accept`;
proved from `compile_sound` by specialising the selector (the gated rows of the active kind are the
ungated rows of `gen κ`; the inactive ones are vacuous). Budget 600 lines on top of `compile_sound`.

**Row count per slot** (`sizes.py`; honest, no sharing between kinds since there is one program):
imports 74,920 (columns 27,856, sibling halves and answers `6 × 7,552`, FS fields `3 × 584`);
folds 54,841; final `Enc₄` 4,032; Merkle steps `4 × 7,552 = 30,208`; univariate Lagrange 2,000;
eq/tensor 15,000; MBP 3,200; sumchecks 2,000; lincheck replay 65,536; **`evalM` replay 211,462**
(one row per irregular entry of the child's two slots, `2 × 74,920`, plus eq tables `2 × 22,619 +
2^14`); `evalL` replay 8,192 (L's matrices templated, BP-C-R2-m3); gated asserts 3,510; selector 4:
**474,905 per slot, 949,810 = `2^19.86` per node** (`N_M` margin 2.21×). **The node fits `m = 30`**;
the smallest cut, if `nodeLayout`'s `decide` fails, is sharing the lincheck-replay eq tables between
the two slots (−2^15 rows) and then the enumeration fallback of B-2.

**The fixed point.** `gen Mux` is a function of `(items, ladder30, ladder32, N_M, N_L, nodeLayout)`;
the child's `evalM` replay is sized by `items` (the irregular count is the item sequence's element
count, a constant), so the program does not depend on any variant; the stage theorem `rows
(compileMux (gen Mux)) ≤ N_M` closes the loop.

**What the circuit asserts of slot `σ`** (compiled from `gen Mux`): (1) one-hot selector and
`kindElem`; (2) item constants (`enc64 |q|`, tags, dummy payloads zero) gated by activity; (3) the
FS chain `state(k+1) = answer(k)`; (4) item 0's payload holds `vk`, `cᵢ` (the `P` region) and
`hdrᵢ`; (5) `hashStmt`: `cᵢ` is the statement of item 1's fields; (6) the arithmetic of `gen κ`;
(7) Merkle steps and cap comparisons; (8) the size constants; (9) `SigOk vk (traceDigest trᵢ) σᵢ`.

```
node_sound : ∀ z vk c₁ c₂, Boolean z → (∀ i ∈ usedH, z[blk i, one] = 1) → HHolds z → Patterns z vk c₁ c₂ →
  ShHolds z → LrHolds z → EHolds (pack z) →
  let p₁ := FR.readSigned 1 z; let p₂ := FR.readSigned 2 z
  accWith V vk c₁ p₁ = true ∧ accWith V vk c₂ p₂ = true
```

Proof: `Patterns` fixes each slot's one-hot selector `κ_σ`; (a) the chains compute `traceDigest`;
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
| blocks | 53,792 | 65,536 | 1.22× |
| M rows per node | 949,810 | `2^21` | 2.21× |
| items | 9,007 | 10,240 | 1.14× |
| `piSize` | 754,896 | 1,048,576 | 1.39× |
| H gap for L + P | 125 blocks | 2,906 | — |

---

## 5. The potential, knowledge soundness, completeness, controls

### 5.1 Shape (`FRSoundness*`)

As spartan-srom's (`SoundnessKSBase` Part A, `muG_step`): `μ L = [Bad L ∨ Esc L] + Σ_{chains on
the frontier} φ(chain)`; a chain is a maximal transcript path (`Matches` re-parameterised by the
item sequence); **Bad** = a digest collision in `L`, a fresh answer equal to any 16-byte-aligned
32-byte window of any logged query or answer, a repeated query, a flipped group; `φ` charges every
open phase its bad probability over the unasked squeezes (`extCount_split`). `step` = one lemma
per row of §5.2 from the exact fiber counts (`card_chF_fiber = 2^128`, `card_chK_fiber = 1`,
`card_idx_fiber`) plus the H row; `final` = §5.4.

### 5.2 Per-fresh-query error (`P30` node; one squeeze per phase)

| # | Phase | Field | Bad probability | `−log₂` |
|---|---|---|---|---|
| Z1 | point, 17 free coordinates (19 at `m = 32`) | F | `17/2^128` | 123.9 |
| Z2 | skip `λ`, interpolant of degree ≤ 127 | F | `127/2^128` | **120.99** |
| Z3 | 24 rounds, degree 3 | F | `3/2^128` | 126.4 |
| L1, L2, **L3** | `α`; 9 rounds degree 2; univariate | F | `1, 2, 127 / 2^128` | 128, 127, **120.99** |
| S1, S2, **S3** | `τ` (24 coordinates); `m − 14 + 2 = 18` rounds degree 3; univariate | F | `24, 3, 127 / 2^128` | 123.4, 126.4, **120.99** |
| I1, I2 | pattern point (16); 16 rounds degree 3; the fixed-constant batching costs 0 | F | `16, 3 / 2^128` | 124, 126.4 |
| Lr1–Lr4 | point (15); rounds (3); `κ_L` (1); rounds (2) | F | `15, 3, 1, 2 / 2^128` | ≥ 126.4 |
| B1, B2, **B3** | `κ` (≤ 12 claims: 11); 24 rounds degree 2; univariate | F | `11, 2, 127 / 2^128` | 124.5, 127, **120.99** |
| R1, R2 | `r″` (7); 23 rounds degree 2 | F | `7, 2 / 2^128` | 125.2, 127 |
| E1–E4 | point (21); rounds (3); `κ_E` (2); rounds (2) | F | `21, 3, 2, 2 / 2^128` | ≥ 123.6 |
| B′ | ≤ 4 claims | F | `3/2^128` | 126.4 |
| P1 | fold round `r` of level `i`, `2^(ℓᵢ−r)` lines | K | `(2^(ℓᵢ−r) C_mca + 2)/2^256`, `C_mca ≤ 2^60` | ≥ 190 |
| P2 | positions | `log₂ nᵢ` bits | `(1 − eᵢ/nᵢ)^{tᵢ}` | **120.36**, 120.70, 120.36, 120.45, 120.41 |
| P3 | consistency batching, 9 coordinates | F | `9/2^128` | 124.8 |
| H | collision / window hit, `≤ 2^16 · logCap` windows | — | `2^-144` | 144 |

**Maximum `2^-120.36 + 2^-144 ≤ εR = 2^-120.093`** (kernel-probed `epsR_le_cap`). Dummy
queries carry no challenge and no charge (their answers are unused; a repeated query is not fresh).

### 5.3 The proximity lemma (`FRProximity.mca_ud_line`; B-5)

Over `K ⊇ F`, `D ⊂ F` (`n` points), `C := C_K` of dimension `k`, `e` with `2e < n − k + 1`,
`u₀ u₁ : Fin n → K`:

```
mca_ud_line : Nat.card { z : K | ∃ w ∈ C, n − e ≤ agree (u₀ + z•(u₁ − u₀)) w ∧
    ¬ ∃ v₀ v₁ ∈ C, agreeSet (u₀,u₁) (v₀,v₁) = agreeSet (u₀ + z•(u₁ − u₀)) w } ≤ C_mca n k e
```

`C_mca n k e := 4 n (k + 1)(e + 1)` as the working value; the lemma is stated with `C_mca` a
definition the closing proof may enlarge, under the stage requirement `C_mca ≤ 2^60` at every
level (`n k e ≤ 2^57` at level 0, `m = 32`). `fold_preserves`: under no bad fold challenge, a
`2^ℓ`-row K-valued word is `e`-close to `C^{2^ℓ}` with joint agreement `A` iff its fold is, with
the same `A` (round by round over the `2^(ℓ−r)` pairs). `interp_F`: the committed rows are
F-valued and `|A| ≥ k`, so the interpolants through F-valued data on F-points are in `C_F` (the
`X_x` have F-coefficients). Proof plan (BCIKS20 Thm 4.1's UD argument): (1) Berlekamp–Welch
pairs and `bw_unique`; (2) the `n × (k + 2e + 1)` system over `K[Z]`, all maximal minors vanish
once more than `e + 1` values admit a kernel vector, rank deficiency over `K(Z)` (Mathlib
`Matrix.rank`, `linearIndependent_rows_iff_isUnit`, `LinearMap.ker_ne_bot_of_finrank_lt`),
denominators cleared; (3) specialisation and long division in `K(Z)[X]`, with the `Z`-degrees of
`Q`'s coefficients `O(k(e+1))`; (4) positions: `r_j(Z)` is `0` or has `O(k(e+1))` zeros, so with
`|A| < n − e` at most `n · O(k(e+1))` good `z`; (5) on `A` the interpolant is affine in `Z`,
`Q = v₀ + Z v₁`, `v₀, v₁ ∈ C_K`, and every good `z`'s agreement set is `A`. The crypto review's
small-parameter probe found no counterexample; its round 2 confirms the statement suffices.

### 5.4 `final`: the deterministic walk

Given `¬ Bad L`, `μ L < 1` and `(V vk c π).runLog L = some true`: `W` is `Rel` by definition and
`E` copies the proof (§6.2, any size). Otherwise: (1) `runLog_chain`, `cap_binding` (the column
at a position is the first preimage read top-down from the cap entry absorbed before the
positions were squeezed; a repeated position reads the same entries); (2) `ligerito_final` from
level 4 up: `W⁽ⁱ⁾` read off `L` is `eᵢ`-close to `C_K^{rowsᵢ}` with joint agreement `Aᵢ`, `|Aᵢ| ≥
kᵢ` (P2, P3 and the fold rounds; `fold_preserves` under P1); `interp_F`, `coeffs_of_values` give
`f⁽ⁱ⁾` whose fold is `g⁽ⁱ⁺¹⁾`; (3) `f⁽⁰⁾` satisfies the batched claims (B′, R, E), `ring_inj` the
`ẑ` claims, `z := unpack f` is GF(2)-valued by definition, and the pattern and shift sumchecks (I,
S) and Z, Lc, Lr give `HHolds`, `Patterns` (hence the one-hot selectors and `one = 1` on the
used blocks), `ShHolds`, `LrHolds`, `EHolds`; (4) `leaf_sound`/`node_sound`; (5)
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
at `ε = 2^-121` on Z2, the extractor at `semXIR` on a toy tape) plus: the one-hot selector (a
two-hot assignment fails `Σ s = 1`); a dummy item with a non-zero payload fails its gated assert;
`pattern_sound`'s negative (a false claim in one range is caught); `pinned_rank`'s inverse
(`M · Minv = I` by `decide`; a wrong `Minv` fails); a `W` proof of size `> proofCap` is copied
(toy at `semXIR`); `items_length = 9,007` and `piSize = 754,896` by `decide`.

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
| `FRSkip` | S-C | `S`, `Λ`, `ζ`, `skip_bad_le`, `pinned_rank` (parametric in `ρ`; A.1's `ρⱼ = y^(2^j)` with the shipped inverse) | 700 | Sumcheck |
| `FRShift` | S-C | range-restricted shift, `m − 14` rounds, `shift_sound` | 350 | Sumcheck |
| `FRPatterns` | L-piop | the pattern sumcheck, range MLEs, `pattern_sound` | 400 | Sumcheck |
| `FRRingSwitch` | S-C | `ring_inj`, `unpack`, MBP | 650 | Field128 |
| `FRSpartan` | S-C | zerocheck/lincheck over `Sel ⊗ (A₀,B₀,I)` and sparse `(A,B,C)` | 450 | Sumcheck |
| `FRRS`, `FRRSEval` | L-pcs (S-D) | novel basis, `Enc`, triangularity, tensor identity; twins | 900 | Field128 |
| `FRProximityBW`, `FRProximityLine`, `FRProximityFold` | S-D | `bw_unique`; `mca_ud_line`; `fold_preserves`, `interp_F`, `positions_bad_le` | 2,000 | RS |
| `FROracle`, `FRQueries` | L-cert | SR | 240 | — |
| `FRTranscriptDefs` | S-0 | kinds, tags, `chF`, `chK`, `idxOf`, **`items`**, `ladder30/32`, `piSize` constants | 400 | FieldDefs, Oracle |
| `FRTranscript` | L-cert | fiber counts, `Matches` | 350 | TranscriptDefs, VIR |
| `FRMerkle` | S-D | caps, `cap_binding`, `colL` | 750 | Transcript |
| `FRLog` | L-cert | forest, `bad_step_le`, `extCount_split` | 800 | Merkle |
| `FRBlake2s{Circuit,Words,Compress,Generic,Walk,Witness}` | S-E1 | leanerVM's circuit, walk | 2,280 | — |
| `FRBlockLayout`, `FRBlockChain`, `FRBlockStream` | S-E1 | A.6 layout; chain block; stream block, `blake2s_chain` | 1,300 | Blake2s* |
| `FRLeafCircuit` | S-E1 | `leaf_sound` (hypotheses `Patterns`, `ChainLinks`, `IOHolds`) | 1,200 | BlockStream |
| `FRFormat` | S-0 | A.3–A.5: `hdr`, `piSize`, `parse`, `reassemble`, byte readers, `W` reader | 700 | TranscriptDefs |
| `FRVIR` | S-0 | `VProg` (A.8), `OpImpl`/`OpSpec`, `runIR`, `semIR`, `gen` per phase (`gen k`, `gen Mux`) | 1,100 | Format, TranscriptDefs |
| `FRVIRSpec` | S-0 | per-phase semantics, `items_length`, `queries_le`, `runSeq_eq_runIR` | 1,500 | VIR |
| `FRVIRCompile`, `FRVIRMux` | L-circ | `compile`, `compile_sound`; `compileMux`, `compile_mux_sound` | 1,200 + 600 | VIR, Spartan, Walk |
| `FRVIREval` | L-circ | `impl`, `evalM`, `evalL`, `tpl_mle`, `shift_mle`, `irregular_mle`, `evalM_eq`, `impl ⊨ OpSpec` | 1,100 | VIRCompile, RSEval, RingSwitch |
| `FRWots` | L-circ | WOTS, `hashStmt`, soundness | 700 | VIRMux, BlockStream |
| `FRNodeLayout`, `FRNodeCircuit` | L-circ | A.7 layout, the two `decide`s, `FR.readSigned`; `node_sound` | 400 + 1,200 | Wots, LeafCircuit, Patterns, Shift |
| `FRVerifier` | L-cert | `V`, `accWith`, `acc_eq`, `W` branches | 800 | VIRSpec, VIREval, Format |
| `FRSoundnessDefs` | L-cert | phases, doom, `φ`, `μ` | 800 | Log, Proximity*, Verifier |
| `FRSoundnessStepA`, `FRSoundnessStepB` | L-cert | F rows; P/H rows; `muG_step` | 2,200 | SoundnessDefs, Skip, Spartan, RingSwitch, Patterns, Shift |
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
| **S-C piop** | L-piop | every F row of §5.2 as a lemma; `FRShift` (`m − 14` rounds), `FRPatterns`, `FRSkip` (`pinned_rank` by inverse) |
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
| FR-R8 | `mca_ud_line`'s rank argument over `RatFunc K` | S-D mid-point: §5.3 steps 1–2 | a larger `C_mca` (≤ 2^60) |
| FR-R9 | `T_V` over 205.9 ms | S-B probe, H1 | specialise the interpreter's hot ops |
| FR-R10 | `FRVIRSpec` outgrows 1,500 lines | S-0 mid-point: phase Z end to end, × 15 phases | re-budget; `V` as structured Lean with `runIR (gen k) = V k` proved once (BP-E-M4's alternative) |
| FR-R6 | V4-A10 lands | re-pin; `FRKState` only | — |

- **S-0 definition of done** (BP-E-R2-m6): `FRFieldDefs`, `FRTranscriptDefs` (`items` with
  `items_length` **proved**), `FRFormat` (`piSize` as a proved sum, `reassemble`, `parse ∘ serialise`
  **proved**), `FRVIR` (`gen` for the three kinds and `Mux`, `OpImpl`/`OpSpec`), `FRVIRSpec` with
  phase Z's semantic lemma **proved** and every other phase's lemma **stated** (`sorry` allowed on the
  branch, tracked in the stage RESULT; the merged entry has none), the two dump tools, `sizes.py`
  and `serial.py` re-run.
- **S-C** adds `FRPatterns`; `FRShift` has `m − 14` rounds. **S-E** adds `FRVIRMux`
  (`compile_mux_sound`). **S-E1** keeps `Patterns`/`ChainLinks`/`IOHolds` as hypotheses.

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
| **pinned coordinates** | **`ρⱼ = y^(2^j)`, `j = 1 … 7`** (`y` the F generator over BF64) | `pinned_rank`: the 128 products `Π_{j∈T} ρⱼ Π_{j∉T}(1 + ρⱼ)` are GF(2)-independent; **shipped as the inverse bit matrix `Minv` with `M · Minv = I` checked by `decide`** (rank 128 verified: `r2/appendixA.log`) |
| pattern constants | `c_j = x^j ∈ BF64 ⊂ F`, `j < 64` | distinct basis monomials: independent by definition |
| shift batching | the two chains' shift claims batched by `1` and `y` | GF(2)-independent |
| `h0` | the unkeyed BLAKE2s-256 chaining value | contract |
| ladders | §2.2 | `FRTranscriptDefs.ladder30/32` |
| `N_M, N_L, qV, εR, δ, fuel` | `2^21`, `2^15`, 10,240, `15/2^124`, 0, `2^47.5 + 2^12 t` | B-10 |

### A.2 Encodings and challenge maps

Positions: a level with `n = 2^b` positions reads `⌊256/b⌋` indices per squeeze answer `a`; index
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

### A.3 `piSize = 754,896`: the body's fields in order (offsets are the cumulative sums)

| # | field | bytes |
|---|---|---|
| 0 | `hdr` | 48 |
| 1 | `stmt` | 64 |
| 2 | Z2: `P^{ab} ‖ P^z` | 2,048 |
| 3 | Z3: 26 rounds × 48 | 1,248 |
| 4 | L2: 9 rounds × 48 | 432 |
| 5 | L3 univariate | 2,048 |
| 6 | S2: 20 rounds × 48 | 960 |
| 7 | S3 univariate | 2,048 |
| 8 | I2: 18 rounds × 48 | 864 |
| 9 | Lr2 + Lr4: 30 rounds × 48 | 1,440 |
| 10 | B2: 26 rounds × 48 | 1,248 |
| 11 | B3 univariate | 2,048 |
| 12 | R0: `s_v` 128 × 16 | 2,048 |
| 13 | R2: 25 rounds × 48 | 1,200 |
| 14 | E2 + E4: 44 rounds × 48 | 2,112 |
| 15 | P1: 22 fold rounds × 96 | 2,112 |
| | rows 2–15 (PIOP messages) | **21,856** |
| 16 | caps `cap₀ … cap₄` | 45,056 |
| 17 | final message | 512 |
| 18 | columns: level 0 … 4, position by position (every index) | 445,696 |
| 19 | siblings: level 0 … 4, position by position, leaf level first (11, 10, 8, 6, 5 per position) | 241,664 |
| | **total** | **754,896** |

(`48 + 64 + 21,856 + 45,056 + 512 + 445,696 + 241,664 = 754,896`; `sizes.py`.) The `â ‖ b̂` values
of Lc and the per-level consistency sums are inside the following round's message (the sumcheck's
first coefficient pair), so they have no row.

### A.4 The item sequence `items` (584 FS items, then per position its queries; `FRTranscriptDefs`)

| # | phase | items (in order) | absorb payload |
|---|---|---|---|
| 0 | seed | 1 seed (`vk ‖ c ‖ hdr`, 112 B) | — |
| 1 | stmt | 1 absorb | `stmt` (64 B) |
| 2 | cap₀ | 1 absorb | 16,384 B |
| 3 | Z1 | 10 squeezes | — |
| 4 | Z2 | 1 absorb (row 2), 1 squeeze | 2,048 B |
| 5 | Z3 | 26 × (absorb round, squeeze) | 48 B |
| 6 | L1 | 1 squeeze | — |
| 7 | L2 | 9 × (absorb, squeeze) | 48 B |
| 8 | L3 | 1 absorb (2,048 B), 1 squeeze | |
| 9 | S1 | 13 squeezes | — |
| 10 | S2 | 20 × (absorb, squeeze) | 48 B |
| 11 | S3 | 1 absorb (2,048 B), 1 squeeze | |
| 12 | I1 | 9 squeezes | — |
| 13 | I2 | 18 × (absorb, squeeze) | 48 B |
| 14 | Lr1 | 8 squeezes | — |
| 15 | Lr2 | 15 × (absorb, squeeze) | 48 B |
| 16 | Lr3 | 1 squeeze | — |
| 17 | Lr4 | 15 × (absorb, squeeze) | 48 B |
| 18 | B1 | 1 squeeze | — |
| 19 | B2 | 26 × (absorb, squeeze) | 48 B |
| 20 | B3 | 1 absorb (2,048 B), 1 squeeze | |
| 21 | R0 | 1 absorb | `s_v` 2,048 B |
| 22 | R1 | 4 squeezes | — |
| 23 | R2 | 25 × (absorb, squeeze) | 48 B |
| 24 | E1 | 11 squeezes | — |
| 25 | E2 | 21 × (absorb, squeeze) | 48 B |
| 26 | E3 | 1 squeeze | — |
| 27 | E4 | 23 × (absorb, squeeze) | 48 B |
| 28 | B′ | 1 squeeze | — |
| 29+5i | P1.i | `ℓᵢ` × (absorb K round 96 B, squeeze) | |
| 30+5i | C.i | 1 absorb: `capᵢ₊₁` (8,192 / 8,192 / 8,192 / 4,096 B) or the final message (512 B) | |
| 31+5i | P2.i | 25 / 13 / 10 / 8 / 6 squeezes | — |
| 32+5i | Q.i | for each of the `tᵢ` indices: 1 column query, then 11 / 10 / 8 / 6 / 5 Merkle-node queries leaf level first (`P30`: the last 2 of each are dummies `0^64`) | |
| 33+5i | P3.i | 1 squeeze | — |

Every absorb's payload is the field listed; every squeeze's answer is consumed as A.2 says, in
order of appearance. `items_length = 9,007`.

### A.5 `reassemble tr : Proof`

`hdr := payload₀[64…111]`; `stmt := payload₁`; rows 2–15 from the absorbs of phases 4–27 in
order; row 16 from `C.0 … C.3`'s payloads and `cap₀`'s; row 17 from `C.4`; row 18 from the column
queries in order; row 19: for the Merkle-node query at depth `h` of index `j` of level `i`, the
**sibling is the half whose position is not bit `h` of `j`** (`j` read from `P2.i`'s answers by
`idxOf`), dummies copied as zeros. `reassemble_roundtrip` for honest traces; `FR.readSigned` uses it.

### A.6 The block layout (bits within a `2^14`-bit block)

| bits | slot | content |
|---|---|---|
| 0 … 255 | 0–1 | `h_in` (8 words LE) |
| 256 … 511 | 2–3 | `h_out` |
| 512 … 1023 | 4–7 | the 64-byte message (stream block) / `0x43 ‖ d ‖ 0^31` (chain block) |
| 1024 … 1055, 1056 … 1087, 1088 … 1119, 1120 … 1151 | 8 | `t_lo`, `t_hi = 0`, `f0`, `f1 = 0` |
| 1152 | 8 | `one` |
| 1153 … 1279 | 8–9 | zero |
| 1280 … 15999 | — | the 14,720 gates in leanerVM's order |
| 16000 … 16383 | — | zero |

Every public per-block constant is a pattern claim (§4).

### A.7 The node's M and L layout and the pack map

- **Pack**: `f[e]` is the F element whose 16 bytes are bits `[128e, 128e + 128)` of `z`, byte `b`
  = bits `[128e + 8b, 128e + 8b + 8)` low bit first; `c₀ = bytes 0…7`, `c₁ = bytes 8…15` LE. A
  block's element `k` (`k < 128`) is `f[blk·128 + k]`.
- **L** (base block 46,336; element addresses relative to `Lbase = 46,336·128`): per slot `σ`
  (stride `2^14` elements): `sig` 299 elements (`idx` 1, `ots` 133 × 2, `path` 16 × 2), digits
  133 as bit-elements, step selectors 399, position bits 7,552 (the bit-elements `(b, 0^127)`),
  kind selector 3; the rest zero. **`N_L = 2^15` rows**: the Lr R1CS's rows are the bit-element
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
| `lagrangeS vals λ → F` | `AF 127, F → F` | the degree-≤127 interpolant through `S ∪ Λ` at `λ` | ≈ 400 |
| `tensorW j r → K` | `N, AK v → K` | `Π_v (1 − r_v + r_v Ŵᵥ(D[j]))` | `2v` |
| `mbp r″ sv → F` | `AF 7, AF 128 → F` | the ring-switch `B̂` by the width-128 program over `m − 7` layers | `(m−7)·128` |
| `walkA r c → F`, `walkB r c → F` | `AF 14, AF 14 → F` | `Â₀`, `B̂₀` by the circuit walk | lincheck replay |
| `evalM τ σ → F × F × F`, `evalL τ σ → F × F × F` | `AF 21, AF 23 → …`; `AF 15, AF 23 → …` | the node's matrix MLEs (kind-selected) | `evalM`/`evalL` replay |
| `rangeMLE R r → F`, `patMLE p r → F` | range id, `AF 16 → F` | `R̃(r)`, `p̃at(r)` of A.7's pattern list | `O(m)` |
| `splitDigest d → F × F`, `selectHalf b l r → D` | | | 0 / 2 |
| `hashStmt kind fields → D` | `B → D` | `leafStmtF`/`nodeStmtF` | 1–2 H blocks |
| `assertEq a b`, `assertBit b`, `assertZero a`, `assertOneHot s₁ s₂ s₃` | | checks; a failure returns `false` | 1 linear (gated: 1 product) |
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
