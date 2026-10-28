# `flock-recursive`: entry blueprint (normative)

Status: phase 1 (B), **revision 3.5, frozen for implementation** (2026-10-27): four rounds of adversarial review (fix passes 1–4) and three stage-review changes, all recorded in §10; later changes only through stage reviews
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
| `piSize` (both kinds) | 797,904 B = 779 KiB (revision 3.14: E4 end 32 B) | `proofCap` 1,048,576 | 1.31× |
| trace items (both kinds) | 8,891 | `qV = 10,240` | 1.15× |
| hashed trace bytes / compressions | 1,481,344 = `64 · 23,146` / 23,146 (no padding cell) | — | — |
| node circuit blocks | H + L end at 47,740 below `Mbase` 49,152 (exact); M 13,097 of 16,384 blocks; used 60,837 | 65,536 | 1.25× (M); 1.08× (used) |
| M rows per node | **1,676,398 = `2^20.68`** (S-N1's O2/O2b complete budget per slot, 838,199: every unbound import's rows counted, the WOTS mux and the `evalL` replay included; levers in the plan) | `N_M = 2^21` | 1.25× (1.21× if the `evalL` replay is chunked, not closed-form) |
| extractor steps (`m = 30` node) | `2^47.11 + 2^11 t` | `fuel = 2^47.5 + 2^12 t`; `B = 2^48 + 2^16 t` | 1.31×; 1.85× |
| error per fresh query | `2^-120.36 + 2^-144` | `εR = 2^-120.093` | — |
| verifier time (N30) | **INT-5 measured 226–233 ms VM best** (S-E11's evaluator 192.9 + the claim-2 kind factor's K products +31–33); at the measured ratio 1.19: ≈ 190–196 ms on the 7763 against the 206.0 ms cap (1.05–1.08×). Still to bind ≈ 14 ms VM (`R` 7, `D̂` 1.5, templates 4, `evalL` replay 1); levers: S-T1's F-side kind factor (−13 … −25 ms), S-E11's `evalM` levers (−12) | `T_V` 206.0 ms | **1.14–1.21× projected** (≥ 1.10× needs V ≤ 223 ms VM); 1.05–1.08× measured today |
| output words (node) | `2^19.3` | `outCap = 2^24` | — |

### 0.1 Decisions

| Id | Decision | Reason |
|---|---|---|
| **B-1** | **Tree leaves are single `m = 32` SNARKs of `2^18` compressions.** The stream leaf is `m = 30`. | The runner hashes the 64 statements `leafStmt (chainEnd sᵢ 2^18) 2^18` itself (`Tree.lean`); the leaf clause of `Rel` demands the chain, so a leaf made of signed segments is uncertifiable (`∀ vk`, design §2.2) and one of two fresh-query segment SNARKs exceeds `proofCap`. K measures the `m = 32` leaf at 3.73–3.86 s and 3.81 GB peak (K §3, §4.4). |
| **B-2** | **Nodes are `m = 30`, one shape, one program `P30`.** `L32` and `P30` have **one item sequence** (every phase sized for the larger kind; a kind's unused items are dummy queries with zero payloads, §1.2) so that every trace element has one address. A node's child slot is replayed by **one program `gen Mux`** whose kind-dependent constants, matrices and public patterns are selector-linear in a **one-hot selector `(s_L, s_P, s_N)`** of three L bits (§4.3). Exact count 53,792 of 65,536 blocks (1.22×), M rows `2^19.86` of `N_M = 2^21` (2.21×). | K: an `m = 31` node (≈ 1.9 s) puts the stream link over its cap, so `m = 30` is hard. A node's replayed verifier does not depend structurally on its own or its children's variants (rulings 1 and 2 of fix pass 2); the fixed point is cut by fixed dimensions (§4.3). Fallback if `nodeLayout` overflows: the enumeration of the occurring pairs `(L32, L32)`, `(P30, P30)` with a public pair byte, never `m = 31`. |
| **B-3** | **Five levels**, rates 1/2 … 1/32, rows 64 then 16, `eᵢ = ⌊(nᵢ − kᵢ)/2⌋`, queries **290, 178, 145, 132, 126**, caps at depth 9, 8, 8, 8, 7; **the final message is the level-4 fold, `2^7` K elements** (`2^5` at `m = 30`, zero-padded), followed by **7 final rounds** that reduce the claim to one point (P1-D7). **Every index is opened**, duplicates included. | BP-C-M3, BP-C-R2-M3, P1 question 3: a level-4 fold of 4 row variables leaves `k₄ = 2^7` K elements, not `k₅`; reducing the final claim to one point costs 7 K rounds and one evaluation of the weight (`rsWeight`, revision 3.9) instead of 128. |
| **B-4** | **F = BF64[y]/(y² + y + β), β = x^63; K = F[u]/(u² + u + α), α = β·y** (S-A), through CompPoly's allowlisted `Ext` over `BF64`, two-`UInt64` twins. | S-A journal; no off-allowlist copy. |
| **B-5** | **Own mutual correlated agreement for lines in the UD regime over K-valued words and `C_K`**, **proved (S-D) with `C_mca(n,k,e) = k e + n`** by a counting argument (§5.3); P1 row `≤ 2^-214`. | I §2.5; `mca_ud_line_K`, `pcsLevels_ok` (kernel). |
| **B-6** | **Wiring:** regions H (BLAKE2s blocks), L and P (in the H gap), M (element rows). A child's trace is the message slots of its chain's H blocks, read by irregular matrix entries evaluated with eq tables (one product per entry); M-internal patterns are templates; BLAKE2s matrices by the walk; the L matrices templated too. **Every per-block public constant is pinned by the zerocheck's public target `E`** (`(A₀z)∘(B₀z) = z + E` at `(0,0)`-row positions, P1-D2/D3); the public inputs and padding are point claims on `f`; the chain links and endpoints are the shift argument's (P1-D5). | No pattern sumcheck, no selector-linear patterns (BP-C-R3-M2 moot); the zerocheck pins constants bit by bit at its own random point; it is what the prover already does. |
| **B-7** | **The verifier is an interpreter `runIR impl` of a straight-line IR**, parametrised by an op-implementation record `OpImpl` (`evalM`, `evalL`, `walk`, `rsWeight`, `lagrangeS` (`mbp` withdrawn in 3.9)); the lincheck has 14 multilinear rounds (P1-D4) and all `ẑ` claims are ring-switched at once into Ligerito's weight (P1-D6); `FRVIRSpec` states each phase's semantics against the record's specification; the circuit's M and L rows are compiled from the same IR (`compile`), with the per-slot mux as a compiler mode (`compileMux`, `compile_mux_sound`). | BP-E-R2-M4 (no cycle), BP-E-R2-M2 (a construction and a theorem for the mux). |
| **B-8** | **`E := fun c π L => decodeWit (semXIR ext (extractorInput c π L))` — the DSL program's denotation, a total computable Lean function on every log (revision 3.17)**; `Computes` is `compile_runs`: on the contract's domain the machine `ext.run` reproduces `semXIR` within `fuel t` (`∃ n ≤ cost P t` under `BoundsOk`, counted on the compiled code); `final` is `ext_good_tape` over `semXIR` on every log `≤ logCap`. `XIR` with affine-in-`t` caps; the `W` copy is capped by `t`. | Probed; BP-E-M5/M6, BP-C-R2-M2, BP-E-R2-m1; S-N1 O3. |
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
755,680` for all three (A.3), any other length rejected with no query.

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
| PIOP messages (A.3's rows 2–11) | 18,992 |
| caps `(512 + 256 + 256 + 256 + 128) × 32` | 45,056 |
| final message `2^7 × 32` (P30: `2^5` K-elements then zeros) | 4,096 |
| columns `290 · 1,024 + 581 · 256` | 445,696 |
| siblings `32 × 7,552` (P30: its `5,810` real ones, the rest dummy zeros) | 241,664 |
| **`piSize`** | **755,680 (739 KiB, 72 % of `proofCap`)** |

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

Counts (`sizes.py`): FS items 429, column queries 871, Merkle-node queries 7,552: **8,874 items**
(`qV = 10,240`, 1.16×); hashed stream 1,437,760 B = **22,465 compressions**.

### 1.3 What each kind proves; `reassemble`

`'L'`, `'P'`: `c = leafStmt h n`, SNARK of `chainEnd s n = h`, witness `.leaf s n`. `'N'`: `c =
nodeStmt c₁ c₂`, SNARK of `acc vk c₁ p₁ ∧ acc vk c₂ p₂` for the committed `p₁, p₂`, witness
`.node c₁ c₂ p₁ p₂`. `W`: `Rel` directly. A child's `πᵢ = reassemble trᵢ` (A.5): `hdr` from item
0's payload bytes `64…111`, `stmt` from item 1's payload, every other field from its item.

### 1.4 The extractor's output

`witWords`: a node of two children `≈ 638,179 = 2^19.3` words of `outCap = 2^24`; a leaf 6
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
2. **Z** zerocheck of `(A₀z)∘(B₀z) = z + E` over **the whole cube** (revision 3.8: `Sel ≡ 1`; the M, L,
   `WM` and spare blocks have the kind **`free`** of A.6, whose rows `(var k, var k)` with `E = 0` (`z_k² = z_k`, true for every Boolean `z`; revision 3.8.1, BP-C-R5-M1) are
   satisfied by every `z`), with **the paper's "skipping c"** restored (P2 §8): `A = Σ_kind Ind_kind ⊗
   A₀^kind`, `B` likewise. **Z1** `r`, `m* − 13 = 19` free coordinates (10 squeezes; 7 pinned, A.1);
   **Z2** the prover absorbs **`P^z` on `Λ₀ … Λ₆₃` (64 values) then `P^{ab}` on `Λ₀ … Λ₆₂` (63
   values)**, 127 F, where `P^{ab}(Y) = Σ_{x'} eq(r,x') a(x',Y) b(x',Y)` (degree ≤ 126) and `P^z(Y) =
   Σ_{x'} eq(r,x') z(x',Y)` (degree ≤ 63); the verifier rebuilds `P^{ab}|_S := P^z|_S + P^e|_S` with
   the public `P^e(σ) = Σ_{x'} eq(r,x') E(x', σ)` (`targetS`), interpolates `P^{ab}*` through the 127
   nodes `S ∪ Λ₀…₆₂` and `P^z*` through `Λ`, and squeezes `λ`; **Z3** `m* − 6 = 26` rounds of degree
   3 on the summand **`eq(r,·)·a_λ·b_λ`** (two λ-folded tables, no `z`, no `W_E`), initial claim
   `P^{ab}*(λ)`; the prover ends with `â, b̂` (`Zend`); **final value `eq(r, r′)·â·b̂ = c_Z`**
   (`finZ`). **The c-claim** is the quirky point claim `ẑ(r, λ) = P^z*(λ)` (weight `eq(r,·)` on the
   `m − 6` variables, Lagrange at `λ` on the skip slice), handed to ring switching as claim 1 — the
   revision-3.1 route; no tail pass over `z`. Soundness of Z2: for a fixed message, either `P^z* ≠
   P^z` (RS catches it off ≤ 63 roots) or `P^{ab}* ≠ P^{ab}` with `P^z* = P^z` (the tail catches it
   off ≤ 126 roots), so the Z2 row is **`126/2^128`** (`skip_pair_bad_le`).
3. **Lc** lincheck of `â = (A z)̂(r_row)`, `b̂ = (B z)̂(r_row)` with `A = Σ_kind Ind_kind ⊗ A₀^kind`
   (S-C-M1; the indicator stays inside the block sum): the sumcheck runs on the **per-kind folded
   columns** `zfold_kind(j) = Σ_t eq(r′_blk, t) Ind_kind(t) z(j, t)`, whose true sum is `Σ_kind Σ_j
   M_kind(j) zfold_kind(j)`, `M_kind(j) = Σ_k rowW(k) [k ∉ pinned(kind)] (A₀ + α B₀)(k, j)` (one
   pass for all kinds, since the kinds partition the used blocks): **L1** `α`; **L2** **14 rounds of
   degree 2** over the position bits (P1-D4); the prover then claims **`v_kind = zfold_kind(r_k)`**
   for the ≤ 7 kinds (`absorb`), and the verifier checks the final value by **one walk** with the
   row weights `rowW′[k] = rowW[k] · Σ_{kind ∌ k} v_kind` and column weights `eq(r_k, ·)` (`rowW` =
   Lagrange at `λ` on the skip coordinate, eq on the rest); **L3** `β ← squeeze` batches the
   `v_kind` into **one** weighted claim on `z`, `Σ_kind β^kind v_kind = ⟨W_β, z⟩` with the public
   weight `W_β(t, j) = eq(r′_blk, t) · (Σ_kind β^kind Ind_kind(t)) · eq(r_k, j)` (**revision 3.16, R-V-M1: the kind factor is carried by `rsWeight`'s claim-2 weight in Φ form, `Ŵ₂(ρ) = Σ_k c_k Σ_κ β^{i(κ)2^k} eq(p_hi^{2^k}, ρ_hi) Σ_{t∈I_κ} eq(p_blk^{2^k}, t) eq(ρ_blk, t)`; since 3.9 the Lean had the plain `eq`, which fails every honest node proof**; its MLE at the
   ring-switching point is a tensor prefix sum over the kinds' intervals, like `ŵ`); result: one
   weighted claim for ring switching, so `J_z` stays 4 (the reviewer's unbatched form would put
   7 claims into RS: `J_z ≤ 11`, RS1 `17/2^128`; batching costs one squeeze at `6/2^128` and keeps
   RS0, the MBP runs and `J_z` as they are). Leaf: one kind, `Ind = 1`, `v_chain = ẑ(r′_blk, r_k)`.
4. **Sh** shift argument (P1-D5), one sumcheck per proof (a node's two chains batched by `1, y`):
   **S1** `τ` (`m* − 14 = 18` block coordinates), `θ` (10 slot coordinates) and `κ_s` from 15
   squeezes; **S2** `18` block rounds of degree 2 on `eq(τ,·)·Out + (shift(τ,·) + κ_s eq(0,·))·In`
   with the endpoints (leaf: `s`, `h`; node: `h0` at each chain's first block) in the
   verifier's target, then **10 collapse rounds** over the positions `< 1024` with the
   verifier-computed slot weight of the two digest slots (`h_out` at 256…511; `d` at 520…775 for
   the chain block, `h_in` at 0…255 for the stream block); result: multilinear claims on `ẑ`.
5. **Lr** (node): Spartan over the L rows (`2^15`): point (8 squeezes), 15 zerocheck rounds (degree
   3), `Lr end` (`â_L, b̂_L, ĉ_L`), `κ_L`; **its lincheck is the E4 lincheck's second summand
   (revision 3.13, S-G1j defect 2)**: the 15-round `Lr4` over a `2^15` window is withdrawn, because
   every L row reads cells `≥ 2^15` (the L bits and M's `one` cell), so `evalL` at a 15-coordinate
   point padded with zeros was identically `(0,0,0)` (`evalL_short_zero`) and the check vacuous.
6. **RS**, ring switching of all `ẑ` claims at once (P1-D6; paper App. B, quirky variant), **run
   after E (revision 3.13, S-G1j defect 1: RS0's slices depend on every claim's point, so RS0 must
   follow E4)**: the prover absorbs `J_z × 128` partials (**`J_z = 4`**: Z's quirky claim `ẑ(r, λ)`, Lc's `β`-batched
   claim, **Sh's one claim** `ẑ(r_blk, r_pos)` (after the 28 rounds both slot terms are evaluations at
   the one point, with the scalar weights `w_out + w_in`; P2 §7.5 (5)), and **E4's `f̂(r′)`** (the L
   and M linchecks' common claim; a leaf uses 3 at RS, the fourth's slices zero and `T₃` omitted
   only when E is absent — E runs for both kinds, so a leaf has 4 as well; `J_z` unchanged from 3.11); `r″` (7 coordinates) and `κ` (4 squeezes); the **switched claims** are `T_j := Σ_{i<128} b_i · Φ_{r″}(s_{j,i})` (`FRRingSwitch.rsT`: `b_i`
   the packing basis of A.7, `Φ_{r″}(a) = Σ_{k<128} c_k(r″) a^{2^k}` the staged Frobenius map with the
   7 coefficients `r″`; `rs1_joint` is proved for exactly this form, S-F deviation 2), their truth
   `Σ_u Φ_{r″}(g_j(u)) f(u)` with `g_j = eq(r_j, ·)` the claim's outer weight; the batched claim
   **`v_RS = Σ_j κ^j T_j`** with weight `W = Σ_j κ^j Φ_{r″}∘g_j` is **Ligerito's input**; no separate
   `m − 7` rounds. The verifier computes `Φ` on `4 × 128` slice values (134 ops each, ≈ 70 k
   products) and, at Ligerito's final point `ρ`, `Ŵ(ρ) = Σ_j κ^j Σ_k c_k(r″) eq(r_j^{2^k}, ρ)`
   (`weightEval`, L-R4; `128 · (m−7)` products per claim: the op `rsWeight`, which replaces the MBP).
   The paper's tensor-algebra form (`Σ_u eq(r″,u) s_u`, the MBP) is **not** used: it is a different
   protocol and is not what S-C proved.
7. **E** (node): the element R1CS over the M rows: point (11 squeezes), 21 zerocheck rounds (degree
   3), ending with the claims `(A_M f)̂(r_E), (B_M f)̂(r_E), (C_M f)̂(r_E)`; `κ_E` batches them into
   **one linear claim on `f` with the public weight `W_E2(y) = (Ã_M + κ_E B̃_M + κ_E² C̃_M)(r_E, y)`**,
   multilinear in `y`; **revision 3.12 (F-7): the E lincheck is restored**, and **revision 3.13
   merges Lr's lincheck into it**: `κ_E` batches six claims, `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M +
   κ_E³ (â_L + κ_L b̂_L + κ_L² ĉ_L)` (the L term is `nodeOnly`: zero for a leaf); **E4**: 23 F
   rounds (degree 2) over the `2^23` cells reduce it to `(W_E2(r′) + κ_E³ W_L(r′))·f̂(r′)` with
   `W_L(y) = (Ã_L + κ_L B̃_L + κ_L² C̃_L)(r_{Lr}, y)` (**`r_{Lr}` is Lr2's final point**, the zerocheck's, as `r_{E2}` is E2's; INT-2) and `r′ ∈ F^23`; E4 end absorbs `f̂(r′) ‖ 0^16` (32 B, so the hashed stream stays `64 · 23,146` and `stream_padded` needs no padding cell; INT-2 ratified); the verifier evaluates
   `evalM(r_{E2}, r′)` and `evalL(r_{Lr}, r′)` **once each, at the F point `r′`** (`finE`), and
   `f̂(r′)` is ring switching's **fourth claim** (`J_z = 4`); the order is `… Lr3, E1, E2, E end,
   E3, E4, E4 end, RS0, RS1, B′`. The weight form of revisions 3.4–3.11 (`Ŵ_E2(ρ) =
   evalM(r_{E2}, ρ)` at Ligerito's final point `ρ ∈ K`, `evalMK`) is withdrawn: S-E3 measured it at
   2.02 s (§10, changes 17). The prover pays the `2^23` pass again (link 2.66 → ≈ 2.80 s measured
   before 3.4; the budget is 3.1 s). **B′**: `κ′` batches into `W` the weights of the **point
   claims** on `f` (the public cells: `vk`, `cᵢ` in each slot's seed cells; the padding cells of
   each chain's last block): `J_f ≤ 20` claims.
8. **P** Ligerito, levels 0 … 4: **P1** `ℓᵢ` fold rounds (K challenges; the rounds fold `W` and
   `f` together, degree 2 in K); `absorb(capᵢ₊₁)` / `absorb(final)`; **P2** positions; the column
   and Merkle-node queries per index; **P3** `κ_c`, the consistency batching by the tensor weights.
   **The final message is the level-4 fold, `2^7` K elements** (P1-D7; `P30`: `2^5` then zeros);
   the verifier checks `Enc₄(final)[j]` directly at the `t₄` positions and reduces `Σ_c W(s, c)
   final(c)` by **7 final rounds** (K) to one point, where it evaluates `W` once (`rsWeight`, revision 3.9; the MBP is withdrawn; A.8
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
| ring switching: `Φ_{r″}` on `4 × 128` slice values (134 ops each) + `Ŵ(ρ)` by `rsWeight` (`4 · 128 · 25`) | ≈ 75 k (squarings are 13 ns) | ≈ 75 k |
| walks `Â₀, B̂₀` | `1.2·10^5` XOR | `1.2·10^5` XOR |
| node: `evalM` irregular `2 × 74,587` + eq tables `2 × 22,465 + 2^14` + templates + walks; `evalL` templated | — | ≈ 2.4·10^5 F |
| **F-products** | **≈ 1.9·10^5 (incl. ≈ 70 k `Φ` steps, mostly squarings)** | **≈ 4.6·10^5** |

### 3.2 `T_V` (measured; revision 3.16)

**Tier of record (H-V, EPYC 7763):** V on an N30 proof **169.9–175.6 ms best** (medians 172–181 ms)
against the measured cap **206.0 ms** (`T_triv,best / 10`, 2,060.4 ms chain checker): **1.17–1.21×**,
with the `maskRows` slowdown (S-E9 (d)) still in the binary. The VM runs V **1.19× slower** than the
7763 (the chain checker 1.28×), so VM figures convert at 1.19, not 1.28: a VM-equivalent cap of
≈ 245 ms. Projection after changes 22–23 (the shift class −38 ms, the remaining templates +4, `D̂`
+1.5, `R`'s closed forms +7, the claim-2 kind factor +6): **≈ 189 ms VM ≈ 159 ms on the 7763,
1.30×**. The 8573C tier is faster and its cap looser (≈ 1.63×). The pre-measurement estimates
(80–115 ms, then 225 ms VM) are history in §10.

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
the kind's pinned positions as `(0,0)` rows; the kind `free` for the non-hash blocks, so every
block has a kind and `Sel ≡ 1`), the zerocheck is the paper's with skipping `c` (§2.3 step 2:
the tail on `eq(r,·)·a·b`, the c-claim from `P^z`) and **`E` the public target** (P1-D2,
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
chain of the hashed stream `B` (`N = ⌈|B|/64⌉ = 22,465` for every kind, since the stream is one
layout): `h₀ = h0`, `hᵢ₊₁ = compress hᵢ Bᵢ tᵢ fᵢ 0`, `traceDigest tr = le h_N`
(`blake2s_chain`). Child slot `σ ∈ {1, 2}` reads stream element `e` at element address
`(chainBase_σ + ⌊e/4⌋)·128 + 4 + e mod 4`, `chainBase_1 = 0`, `chainBase_2 = 22,465`. **WOTS**
(S-0-M2): 133 chains × 3 steps + 67 key-leaf blocks + 32 path blocks = 498 blocks per slot, laid
out **consecutively** (chain `i`'s steps `w_{i,0..2}` at blocks `wotsBase_σ + 3i + s`, `s ∈ {0,1,2}` the
contract's step `s+1` — S-G's `nodeKind`, S-CN D-5 —, then the key leaf, then path step `t`'s two
blocks). The contract's messages put the variable fields at unaligned byte offsets (`x` at 11–42
and `j` at 1–8 of a `w43` block; the ends at `9 + 32k` of the key leaf; `l`, `r` at 1–32 and
33–64 of a path step), so they are **not** wired by element equalities. Instead: (i) every
variable field's source is computed on the **aligned side** in M rows — the selector mux `a_{i,s}
= sel_{i,s}·h_out(w_{i,s−1}) + (1 − sel_{i,s})·ots_i` (2 rows per half; `sel_{i,s} = [d_i < s]`, L
bits), the end `e_i = sel_{i,3}·h_out(w_{i,3}) + (1 − sel_{i,3})·ots_i` (S-E2 F-2: digit 3 keeps `ots_i`; three selectors per chain `[d<1] = (1−b₀)(1−b₁)`, `[d<2] = 1 − b₁`, `[d<3] = 1 − b₀b₁` tied to the digit bits by 2 product rows per chain, 266 per slot), the path's `l_t = b_t ? sib_t : cur_t`, `r_t = b_t
? cur_t : sib_t` (`b_t` the index bit, `cur_t` the previous output) — into the **mirror sub-region
`WM`** of H (10 blocks per slot; stride 2 elements per link source); (ii) each unaligned field is
tied to its mirror cell by a **link family of the shift argument**: `Σ_t eq(τ,t) Ind_fam(t) ·
msg(t)[off … off + len) = Σ_t eq(τ,t) Ind_fam(t) · mirror(t)` with an arbitrary slot map
(`slotW`, S-C-m1) and a re-based stride for the mirror side (the `WM` map is pinned in A.6, revision
3.14: source `g` of slot `σ` in block `wmB σ + ⌊g/4⌋` at positions `256·(g mod 4) + [0, 256)`, so
that every mirror lies in positions `< 1024`, the only ones the Sh collapse rounds reach), all families batched into the one Sh sumcheck by powers
of `κ_s`. Families per slot (**8, `nLinkFam = 8`; S-CN D-1**): `w43` input `x` (offset 11, 32 B, 399 blocks),
`w43`/key-leaf `j` (offset 1, 8 B; the source is one cell, so the family is a linear claim),
key-leaf ends at offset 9 (67 even ends) and at offset 41, which **crosses the block boundary**
(end `k = 2u+1` is block `u` bytes 41–63 and block `u+1` bytes 0–8): `end41lo` (23 B) and `end41hi`
(9 B) with one shared mirror source per odd end (66 odd ends: `k ≤ 131`), path `l` (offset 1),
`r[0…30]` (offset 33), `r[31]` (block 2 offset 0): one batched sumcheck, S2's rounds unchanged,
S1's point gains the `κ_s` batching (powers `κ_s² … κ_s⁹`: `+9/2^128`). **The node's Sh is
chain-masked**: its `Out`/`In` tables carry the factor `Ind_chain(y)` (the two chain intervals;
the start term `κ_s (eq(0,·) + eq(chainBase_2,·))`, whose **target is 0 in characteristic 2** — it binds only `In(0) = In(chainN)`; `h0` at **both** chain starts comes from the public target (`streamStart.h0Pin = true`, `nodeKind 0 = nodeKind chainN = streamStart.target`, `Kind.hIn_eq_h0`), so there is no hole (INT-3 decision 3) — so the identity never reads a block `≥
chainN·2` — WOTS, `hashStmt`, `WM`, L or M; consecutive non-chain blocks are not linked and the
honest witness would fail an unmasked identity. Kernel check: `shift_sound_masked` (S-C,
`FRShift`: the masked `ChainLinks` ⇔ the two chains' links and endpoints) and `sh_reads_chain_only`
(S-G: the node `truthS1` reads no block `≥ 2·chainN`). This is what makes the `WM` mirrors in
positions `< 1024` of `free` blocks sound: no other claim reads them (`free`'s rows only force
Booleanity, which bit mirrors satisfy). The WOTS message's digits `d_i` are 256 L bit-elements tied to the
chain's last `h_out` by two linear rows; the checksum digits by Lr rows.
**`hashStmt`** (BP-C-R4-M1): **three blocks per slot**, all in `Sel`, all constants
kind-independent: block **A** hashes the leaf message `tagLeaf ‖ h ‖ enc64 n ‖ 0^23` in one
compression (`t_lo = 41`, `f0 = 0xFFFFFFFF`); blocks **B1–B2** hash the node message `tagNode ‖ c₁
‖ c₂ ‖ 0^63` in two (`t_lo = 64`, `f0 = 0`; then `t_lo = 65`, `f0 = 0xFFFFFFFF`, linked `h_in(B2) =
h_out(B1)` by an element equality); **the messages are item 1's payload itself** (S-E1-M1): `stmt`
is laid out as the padded statement-hash message blocks (§1.1: `tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64`
or `tagNode ‖ c₁ ‖ c₂ ‖ 0^63`), so block A's and B1's message slots equal payload elements 0–3 and
B2's elements 4–7 by **8 gated product rows per slot** — A's four equalities gated by `s_L + s_P`, B1's and B2's by `s_N` (S-E2 F-1: ungated, A's `tagLeaf` pin and B1's `tagNode` pin at byte 0 and A's zero bytes 41–63 against a node's `c₂` make the rows unsatisfiable together, and the lemma would hold vacuously) — (the payload's elements are 16-aligned
trace cells, §1.2; no byte shift); the kinds `hashA`, `hashB1`, `hashB2` pin `h_in = h0`, the tag
byte, the zero bytes and slot 8 (A.6), so the equalities carry only the variable bytes; the
slot's statement is `cᵢ = (s_L + s_P) · out_A + s_N · out_B2` (two product rows), asserted equal to
item 0's `c`. `wots_sound`; `hashStmt_sound : OneHot s → HoldsE (blockR1CS hashA) A → HoldsE (blockR1CS
hashB1) B1 → HoldsE (blockR1CS hashB2) B2 → h_in(B2) = h_out(B1) → (s_L + s_P = 1 → msg(A) =
stmt[0…63]) → (s_N = 1 → msg(B1) = stmt[0…63] ∧ msg(B2) = stmt[64…127]) → (s_L + s_P = 1 → out_A =
leafStmt (stmt[1…32]) (stmt[33…40])) ∧ (s_N = 1 → out_B2 = nodeStmt (stmt[1…32]) (stmt[33…64]))` (the output selection and the `stmt` parse are `compile_mux_sound`'s
and `FRFormat`'s). `V`'s own `stmtOk` checks `stmt`'s tag and zero bytes for its kind and hashes
the message (one or two compressions). This is the cheapest sound construction found: the
alternative (keep `enc64 n ‖ h` and wire byte-shifted windows) needs GF(2)-linear, not F-linear,
rows (the BP-E-M1 problem).

### 4.3 The node circuit: layout, mux, counts

| Region | Base (blocks) | Content | Blocks |
|---|---|---|---|
| **H** | 0 | chain 1 `[0, 22,465)`, chain 2 `[22,465, 44,930)` (kinds `streamStart` at each chain's first block, `stream` elsewhere), `hashStmt` 6 (`hashA`, `hashB1`, `hashB2` per slot), WOTS 996 per node (`w43` 399, `hashB1` 1 + `stream` 65 + `streamEnd41` 1 for the key leaf, `hashB1`/`hashB2` 16 + 16 for the path, per slot), spare 8; `Sel` = the kinds' intervals; all-zero blocks elsewhere | 45,960 |
| **L** | 47,616 (`lBase`, since 3.12; S-H2k) | bits (A.7): per slot the signature (4,772 B), the WOTS digits and selectors, the position bits as bit-elements, the one-hot kind selector `(s_L, s_P, s_N)`; `N_L = 2^15` rows | 124 (allotted 3,072: the gap to M) |
| **M** | 49,152 (`3·2^14`) | `N_M = 2^21` elements = 16,384 blocks, ending at 65,536; slot `σ`'s rows at `Mbase + (σ−1)·2^20` | 13,500 used |
| **total** | | | **59,585 of 65,536 (91 %, 1.10×; A.11)** |

There is no `P` region: the public inputs `vk`, `c₁`, `c₂` are **point claims on `f`** at each slot's
seed cells (payload elements 0–5 of item 0: `vk` 2, `cᵢ` 2; 8 claims per node), batched into the
Ligerito weight at B′ (BP-C-R3-m1: slot-valued facts are `f̂` claims, not `ẑ` claims); the padding
cells of each chain's last block (3 per chain) are point claims `= 0` the same way, and **M's `one` cell `f[Mbase] = 1` is a point claim** (S-E2 F-4): `J_f ≤ 21`.

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
imports 74,521 (columns 27,856, sibling halves and answers `6 × 7,552`, FS fields `3 × 451`);
folds 54,841; final `Enc₄` `2 · 2^7 · 126 = 32,256` (P1-D7); Merkle steps `4 × 7,552 = 30,208`;
the Z2 Lagrange 400; eq/tensor 15,000; **ring switching: `Φ` on `4 × 128` slice values `4 · 128 · 136 = 69,632`, Z's Lagrange weights 4,032, `rsWeight` `4 · 128 · 25 = 12,800` (S-F deviation 2; replaces the MBP's 12,800)**;
sumchecks 2,000; lincheck replay 65,536 + the per-kind row-weight adjustment 16,384 + the `free` kind's term 16,384 = 98,304;
**`evalM` replay `2 × 74,521 + 2 × 22,465 + 2^14 = 210,356`**; `evalL` replay 8,192; gated asserts
`2 × 451 + 2 × 871 + 600 = 3,244`, mirror-cell mux 2,600, selector–digit rows 266, gated `stmt`
equalities 8 (counted once, F-3′), selector and kind rows 4: 544,954 per slot by this **pre-A.11
op-count model**. The normative count is **A.11's replay-template model: 863,942 rows per slot
(the measured 68,795-row compiled skeleton plus the templates of every structured op), 1,727,884 =
`2^20.72` per node** (`N_M` margin 1.21×). **The node fits `m = 30`**; the smallest cut, if
`nodeLayout`'s `decide` fails, is the E2 lincheck restored so the child's `evalM` replays at an F
point (1,320,204 rows, 1.59×; A.11), then sharing the `eq(ρ_blk,·)` tables between the two slots
(−196 k), then the enumeration fallback of B-2.

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

**The replay fixed point (revision 3.14, S-E6 §4).** The node's M contains the replay rows `R`
that compute the child's `evalM(r_{E2}, r′)`; a node child has the same circuit, so the matrix `R`
evaluates contains `R`. If `R`'s rows were as irregular as `evalMT`'s products, `MLE(R)` would cost
`|R|` and `|R| ≥ |M∖R| + |R|` would have no solution. **The layout rule that closes the fixed
point (option (a)): every constant the evaluation uses sits in the coefficients of a linear row,
and every product multiplies two regularly addressed cells.** Concretely, `evalM` is a sum over a
fixed set of public matrices `𝒞 = {T_k (each key's template), Inc_f (the 0/1 incidence matrices of
the run/irregular import families: item `t` ↦ its block), Addr (the import addresses' bits), A₀,
B₀, the pack and base patterns}`, each used as `Σ_r eqτ[r] · (Σ_c C[r,c] · eqσ[c])` with `eqτ`,
`eqσ` the eq-tree prefix tables (LSB-first, so level `b` is `eq(σ_{<b}, ·)` at the aligned base
`2^b`). `R` lays this out as **u-rows** `u_r = Σ_c C[r,c] · eqσ[c]` (linear, constant coefficients,
regular reads), **v-rows** `v_r = eqτ[r] · u_r` (products at stride 1) and aligned range sums, with
`R`'s u-rows for `C` at a row base aligned to `2^{a_C}`. Then `MLE(u-rows of C)(τ, σ) = eq(τ_hi,
uBase_C) · eq(σ_hi, tbl_C) · Ĉ(τ_{<a_C}, σ_{<b_C})` — **the same value `Ĉ(τ_lo, σ_lo)` that the
evaluation of the child's own instances of `C` needs**, computed once and shared; v-rows, sums and
eq trees are `O(log)`/`O(log²)` closed forms. So `cost(evalM) = Σ_C cost(Ĉ) + O(|𝒞| · log)` and
`|R| ≈ #products of evalM + Σ_C rows(C)`, independent of `|R|`: the set `𝒞` is closed under taking
`R`'s own rows (`R` introduces no new constant matrix beyond `Addr`/bases, themselves in `𝒞`).
The plan is not circular: every base and size is a function of the matrices' dimensions
(`planOf` from `sizes`), never of `R`'s contents. Lemmas (L-circ/S-E): `replay_mle` (the MLE of
`R`'s rows in terms of the shared `Ĉ` values and closed forms), `evalM_eq` restated as the sum over
`𝒞`, `plan_wf` (the layout depends on sizes only), `replay_sound` (an instance of `compileT_sound`).
No protocol, extractor or error change. **Sizes (revision 3.15, S-E9's measured plan: 68 keys,
3,790 instances, 5,408 own cells, 6,169 sparse skeleton rows in 18,354 forms / 31,103 entries,
20,510 distinct cells; slot 1 = slot 0 shifted by `2^20` in 20,506 of them, so `R` evaluates one
slot's structure with `β̃(c) = (1−τ₂₀) eq(σ,c) + τ₂₀ eq(σ,c′)`):** `R = 293,795` rows per slot
(`rcount.py` classes: tables 48,400, keys 29,623, the child slot's `β̃`/`α̃`/sparse/shared/own/
instance rows 193,472, closed forms 8,300, outputs 1,000, **the child's walk rows' MLE 13,000**);
with the skeleton's sparse rows templated (−110 k) and each key's instances in arithmetic
progression (−20 k): ≈ 164 k.

**The walk (revision 3.15).** `A₀`/`B₀` are **dense**: `nnz(A₀) = 51,726,185`, `nnz(B₀) =
35,684,622` over the 14,720 gates (up to 7,358 terms in a row; `logs/S-E9/walk-nnz.log`), because
the hash circuit folds every XOR into the gates' linear forms. So A.11's lincheck-replay class (a
product row per gate with `A₀`'s row as its form) cannot exist as rows, and `Â₀(τ_lo, σ_lo)` is not
a cheap value to need. **Ruling: the walk's rows are the gadget DAG, materialised** — one linear
row per XOR (≈ 6·10⁴) and the ≈ 30,851 products, ≈ 90,851 rows per slot for the fused `A₀`/`B₀`
walk, **laid out as a template of the G gadget** (80 instances: 10 rounds × 8 `G`, each ≈ 750 XOR
rows + 368 product rows at one stride; round `r`'s state words at regular positions, so the wires
between rounds are 320 word-runs under two fixed patterns plus the 160 message-schedule reads:
one small wiring matrix `Wire ∈ 𝒞`). Its MLE `D̂` is the closed form `Ĝ₀(τ_lo, σ_lo)` × the
instance sum + the wiring terms, ≈ 13 k products — **so `R` replays no walk**: the parent's `evalM`
needs `D̂`, not `Â₀`, and the node's own lincheck is the only walk in `V` (8.9 ms). The XOR cells
(≈ 6·10⁴ per slot) live in M. `FRBlake2sGeneric`'s `GOps.xor` becomes a row-emitting op in the
template interpretation (`sim_compressW` is parametric); S-E9's `tplWalkAB_ok` carries over with
single-cell forms (no closed-term expansion). Owner S-E (with S-A's generic module). The symbolic
family (S-E9 (a)) is declined: it keeps `Â₀` at a fresh point in every `evalM` (two walks per level,
replayed by `R` at ≈ 106 k rows) and needs a row representation the dump and P2 cannot hold.

**`maskRows` and the shift class.** `rowW′[k] = rowW[k]·mask[k]` reads another template's output
cells at a per-chunk aligned shift; the evaluator treats such an own input as one `hfac` per chunk
(the shift class of this section), not as 64 irregular `glVal`s: `maskRows` stays **bound**
(unbound it would let the prover choose the lincheck's row weights) and costs ≈ 1 ms, not S-E9's
+39 ms.

**`τ` has one length for every kind** (revision 3.15): `finSh`'s `packFK` gives `τ` 18 coordinates
for L32, P30 and N30 alike, P30/N30 padded with the constant 0 in coordinates 16–17 and their
S2 running 16 block rounds; `eqPt`, `shiftEq`, `slotW`, `shiftTarget` and `shiftMask` are defined
on 18 coordinates and their `_meets` lemmas use `eq((a ‖ 0^k), (b ‖ 0^k)) = eq(a, b)`
(`eq_pad_zero`), so the five become templates (S-0 the pack, S-C the specs, S-F2 the `_meets`,
S-E the templates).

**`planOf` (revision 3.17, the orchestrator's ruling revising 3.15 (e)).** The badge's `NS` is the
monotonic time of parsing `π` and evaluating `acc` only (`harness/badge/Verify.lean.in`,
`timedCheck`), so a **closed top-level plan constant, initialised at process start, is outside
every check's `NS`**; process start counts only against the batch timeout `verify_s · n + 60 s ≥
70 s` (`rfh/checks.py` `verify`). **Rule: the plan is built at process start, ≤ 5 s on the VM**
(43–49 s today, under the 70 s floor; S-E's lever); a control measures that a cold process's first
check is not slower than its warm checks (the plan is not lazily computed inside `acc`). The 0.2 s
bound of 3.15 is withdrawn: literals would need a kernel proof about `compileT` (S-E10). The source
rule's bans (`initialize`/`init`, elaboration-time code) are untouched: the constant is an ordinary
closed term.

**The E truth and the rows V evaluates (revision 3.17, S-N1 O1).** `truthE`, `nE`, `RejE4` and
`RowsFit`/`hfit` are stated over **`nodeIRows (planOf fin)`**, the indexed templated rows of
`compileT` that `evalMT` evaluates (`evalMT_eq`), not over `Layout.nodeRows` (`compileMux` without
templates: a different row list with different cells for every templated op). `SlotHolds`,
`node_sound` and the dooms then speak of one circuit. The E error row is unchanged (`21, 3, 5, 2
per round`: SZ over the row coordinates and the rounds' degrees depend on `N_M = 2^21`, not on
which rows), and `hfit` is `plan_rowsFit`: rows `< 2^21`, cells `< 2^23` for the templated layout
(`mRows_le`, `usedBlocks_le`).

**Every import has rows (S-N1 O2/O2b).** The registers `SlotHolds.run` assumes are bound by:
the trace cells — no rows (the pack map is the register → H-cell binding; the cells are fixed by
the digest chains and `cap_binding`); `rsWeight` (45,604 + the kind factor 68,473), `shiftTarget`
(1,300), the 745 `tensorW` (47,680), `targetSNode` (16,000), `linkWAll` (15,000), `evalL` (the
replay of `evalLT` as the closed form over A.7's strided L regions, ≈ 10,000; ≈ 40,000 if
chunked), the child's `evalM` (`R`, 296,795 with the kind factor's share), the `free` term (80);
and **the WOTS mux rows of §4.2** (per slot: the 266 selector–digit rows, the `a_{i,s}` mux 133 ×
3 × 2 halves × 2 rows = 1,596, the ends `e_i` 532, the path's `l_t`/`r_t` 128, the digits →
`h_out` linear rows 266: **2,788**; the mirror sources are the mux rows' output cells in `WM`, no
extra rows). The full budget is A.11's and `sizes.py`'s "changes 24": **838,199 per slot,
1,676,398 per node (1.25×)** with the levers of 3.16 in the plan.

### 4.5 Margins (`sizes.py`)

| Quantity | value | bound | margin |
|---|---|---|---|
| blocks | 59,585 | 65,536 | 1.10× |
| M rows per node | 1,727,884 | `2^21` | 1.21× |
| items | 8,874 | 10,240 | 1.16× |
| `piSize` | 755,680 | 1,048,576 | 1.39× |
| H gap for L | 124 blocks | 3,192 | — |

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
| Z2 | skip `λ` (the only univariate round): `P^z*` through `Λ`, `P^{ab}*` through `S ∪ Λ₀…₆₂`; bad `λ` ≤ 126 for any fixed message (§2.3) | F | `126/2^128` | **121.0** |
| Z3 | 24 rounds, degree 3 (26 at `m = 32`) | F | `3/2^128` | 126.4 |
| L1, L2, **L3** | `α`; **14 rounds of degree 2** (P1-D4); `β` batching ≤ 9 per-kind claims (8 kinds + `free`) | F | `1, 2, 8 / 2^128` | 128, 127, 125 |
| S1, S2 | `τ, θ` (16 + 10 coordinates) and the batching `κ_s` of the start term and 8 link families (powers 1 … 9; S-0-M2, revision 3.14); 16 block rounds + 10 collapse rounds, degree 2 | F | `26 + 9, 2 / 2^128` | 122.9, 127 |
| Lr1–Lr3 | point (15); rounds (3); `κ_L` (1); the lincheck rounds are E4's (revision 3.13) | F | `15, 3, 1 / 2^128` | ≥ 126.4 |
| RS1 (after E4, revision 3.13) | `r″` (7 coordinates) and `κ` (`J_z = 4` claims) in one phase: the bad polynomial `D(r″, κ)` has degree ≤ 1 per `r″` coordinate and ≤ `J_z − 1` in `κ` | F | `(7 + J_z − 1)/2^128 = 10/2^128` | 124.7 |
| E1–E4 | point (21); rounds (3); `κ_E` (6 claims, revision 3.13: `â_M, b̂_M, ĉ_M` and `κ_E³·` Lr's three: `batch_bad_le` at 6, `5/2^128`); **E4: the lincheck's 23 rounds (degree 2; revision 3.12)** | F | `21, 3, 5, 2 / 2^128` per round (`round_escape_le`) | ≥ 123.6 |
| B′ | `κ′`: `J_f = 9` point claims on `f` (M's `one` cell, 8 public cells; the E claim is RS's since 3.12, the padding cells are gone since INT-2), powers `κ′² … κ′^{10}` | F | `10/2^128` | 124.7 |
| P1 | fold round `r` of level `i`, `2^(ℓᵢ−r)` lines; the round folds `W` and `f` (degree 2 in K) | K | `(2^(ℓᵢ−r) C_mca + 2)/2^256`, `C_mca ≤ 2^60` | ≥ 190 |
| P2 | positions | `log₂ nᵢ` bits | `(1 − eᵢ/nᵢ)^{tᵢ}` | **120.36**, 120.70, 120.36, 120.45, 120.41 |
| P3 (levels 0–3) | consistency batching: `κ_c` of 9 coordinates (**5 squeezes**), coefficient of index `j` = `eq(κ_c, bits₉(j))` (powers of one F would be `tᵢ/2^128 = 2^-119.8`, over `εR`: not allowed). **P3.4: row 0** (S-G2, revision 3.15): level 4 is checked directly (`y_q = Enc₄(final)[p_q]`), its `κ_c⁽⁴⁾` squeezes stay in the transcript unused | F | `9/2^128`; P3.4 `0` | 124.8 |
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
(toy at `semXIR`); `items_length = 8,874` and `piSize = 755,680` by `decide`.

---

## 6. The extractor

### 6.1 Contract and B-8

`Computes p E fuel` asks, on every tape of the domain (`|π| ≤ proofCap`, every query `< 2^64`
bytes, a tape of `≤ 2^64` words), `∃ o, p.run … = some o ∧ o.length ≤ outCap ∧ decodeWit o = E c π
L`. `KState.final` ranges over **every** log of `≤ logCap = 2^96` entries, so `E` must extract on
logs far outside `Computes`' domain (about `2^61` entries). **The extractor's domain (revision
3.17, S-N1 O3).** `E` is defined as **the DSL program's denotation, `E c π L := decodeWit (semXIR
ext (extractorInput c π L))`**: `semXIR` (§6.4) is a total, computable Lean function with `Nat`
indices and statically capped loops, so `E` is computable on every log and the badge, which
compiles the whole `submission` (AGENTS.md §10: "the whole `submission` must be computable"),
builds. `Computes ⇐ compile_runs`: on the domain the 64-bit machine `ext.run` reproduces `semXIR`
within `fuel t` and the output cap (`BoundsOk` is where the `2^64` bounds are used). `final ⇐
ext_good_tape` (§6.5), which is stated over `semXIR` and uses no domain bound, so it holds on every
log `≤ logCap`: S-N1's `hOut` is discharged, not assumed. **Rejected**: S-N1's `S.E := if InDom
then X.E else Eₛ` with a non-constructive `Eₛ` (`readWit (fF …)` through unique decoding) — the
contract's `choice_certificate` admits it at the kernel, but a `noncomputable` field fails the
badge build (AGENTS.md §7.5), and `X.E := ext.run` on an out-of-domain tape is unproven (the
machine's words overflow); a potential that is `1` outside the domain breaks `step` (a jump of
`1 ≫ ε`, or a ramp of `2^-61 ≫ ε` per entry). `E` takes no `vk`: on a node `vk` is `π`'s
`hdr.pub` (`vkOf_of_run`), a leaf needs none; the linked route of O0 (`RunLink`) serves long logs
too. Kernel-probed at B-8 (`B8.lean`: `computes_Eof`, `fuel_le`); S-H2 restates `computes_Eof`,
`E_leaf`, `E_node` over `semXIR`.

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

### 6.3 Step budget (`m = 30`; **57 machine steps per F product** on the compiled code, S-H1's
kernel-checked `steps_mulF`; `seq` nodes included)

| Step | F-products | steps |
|---|---|---|
| memory, index, ladder read | — | `2^26 + 3t`, `≤ 2^11 t`, `2^30` |
| `Enc(g⁽¹⁾)` at `n₀ = 2^18`, `k₀ = 2^17` | `2^36` | `2^41.8` |
| level-0 interpolation `67 k₀²` + back-substitution `32 k₀²` | **`2^40.6`** | **`2^46.4`** |
| levels 1–4, K-folds, output | `≤ 2^36` | `≤ 2^41.8` |
| **total** | `2^40.69` | **`2^46.52 + 2^11 t`** |

`fuel t = 2^47.5 + 2^12 t` (**1.97×**); `B t = 2^48 + 2^16 t` (**2.79×**). No `m = 31` fallback.

### 6.4 The DSL (`FRXDsl`, as delivered by S-H1)

`XIR := prim (op | const) | load | store | input | out | seq | ite | loopK c n K body | loopT c n
cap body`, with the field routines (`mulF`, `sqF`, `addF`, `invF`, `mulK`, `addK`, `invK`, `·β`,
`·α`) as straight-line blocks of `FRXField`. `loopK` runs `min(M[n], K)` times with the clamp
compiled in (6 statements); `loopT` runs `M[n]` times and is charged at `cap.eval t` under
`BoundsOk` ("every `loopT` entered has a count `≤ cap.eval t`", composed along `seq`); the loop
counter `c` may not be written by the body (`WF`). **Cost** (syntactic): a block of `n`
statements `2n − 1`, `store` 4, `seq` `+1`, `ite` `max + 1`, `loopK` `8 + K·(cost body + 3)`,
`loopT` `3 + cap(t)·(cost body + 3)`. **Memory**: `regs = 256` registers; cells `0 … 3` hold the
constants `1, regs, 0x1B, 63` (`Inv`; never a destination); field scratch `5 … 38`; user registers
`64 … 255`; the heap above `regs`. Theorems (kernel): `steps_le_cost : WF P → Inv s.M → BoundsOk I
t P s → steps I P s ≤ cost P t`; `outs_le`; `compile_runs` (`∃ n ≤ cost P t, Runs …`);
`run_toProg : regs ≤ mem → WF P → BoundsOk … → mem + mpw·t + cost P t + 8 ≤ f → (toProg mem mpw
P).run input f = some (semXIR …).o.toList`; `compile_correct`; `size_compile`; exact `steps_*` /
`cost_*` per field routine (`mulF`: 57); the negative controls `toyBad_short`, `toyBad_not_bounds`.
`ext := toProg 2^26 3 extIR`; `ext_halts` from `run_toProg`, `boundsOk_ext` and a cost lemma per
phase.

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
| `FRVIRFinals` | S-0 fix pass (Z, Lc, Sh, Lr), S-F (RS, E, B′), S-G (P i, Pf) | the typed `Finals` structure (A.9), one field per phase with its op list and semantic lemma `exec_finX` against `refFinX` | 1,200 (500 + 300 + 400) | VIR |
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
`eqBits_eq_eq` lives in its consumer `FRSoundnessLigerito`, which imports `FRRS` and `FRMLE`);
`tensorW j r` takes `r` in that order. **`domBits = 20`** is `FRTranscriptDefs`'s own constant, equal
to `FRRS.logNMax` by `rfl` where both are in scope, so `FRRS` stays off the serial path (ratified,
S-0 fix pass m6). **In-play digests**
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
values padded to 2,048 B; the final message is the level-4 fold, `2^7` K-elements (4,096 B; `P30`: `2^5` then zeros). **Variable order of the quirky polynomial** (S-F deviation 4): its `m − 6` multilinear variables are position bits `6 … 13` (8) then the block bits (`m − 14`); the pinned `ρ₁ … ρ₇` of A.1 are variables `0 … 6` (position bits `6 … 12`, the lowest, which round 1's GF(2^8) accumulation needs); Z1's free coordinates are variables `7 …` (position bit 13, then the blocks). Hence **the Z claim's inner weight uses `ρ₁` for bit 6** (`eqZ λ ρ₁`), not Z1's first coordinate (S-0/S-F: a one-line change). **Coordinate layouts of multi-coordinate squeezes** (S-0 deviation 7): coordinate `2s + c` is bytes `16c … 16c + 15` of answer `s`; Z1: 20 slots, the first `m − 13` used; S1: `τ` = 0–17 (`P30`: 0–15), `θ` = 18–27, `κ_s` = 28; RS1: `r″` = 0–6, `κ` = 7; Lr1, E1 likewise; consumers pick, dummies are ignored. **In-play windows** (S-0-m1): `windows` is defined by **stream offset** (`≡ 0 mod 16` in `0x54 ‖ traceBytes`, i.e. query offset `7 + 16k` for the seed and `8 + 16k` for every other query), so the seed's `vk`, `c` and `hdr` windows are in play too (harmless, never looked up; the count per entry is unchanged, `≤ 2^16`).

### A.3 `piSize = 797,904` (revision 3.14): the body's fields in order (INT-2's numbering and offsets)

| # | field | offset | bytes |
|---|---|---|---|
| 0 | `hdr` | 0 | 48 |
| 1 | `stmt` (the padded statement-hash message blocks, 128 B) | 48 | 128 |
| 2 | Z2: `P^z|_Λ ‖ P^{ab}|_{Λ₀…₆₂}` (127 F, zero-padded) | 176 | 2,048 |
| 3 | Z3: 26 rounds × 48 | 2,224 | 1,248 |
| 4 | Z end: `â ‖ b̂` | 3,472 | 32 |
| 5 | L2: 14 rounds × 48; the 8 `v_kind` | 3,504 | 672 + 128 |
| 6 | S2: 28 rounds (18 block + 10 collapse) × 48 | 4,304 | 1,344 |
| 7 | Lr2: 15 rounds × 48 (Lr4 withdrawn, revision 3.13) | 5,648 | 720 |
| 8 | Lr end: `â_L ‖ b̂_L ‖ ĉ_L` (`finLr`'s source) | 6,368 | 48 |
| 9 | E: E2 21 rounds × 48 at +0; E4 23 rounds × 48 at +1,008; **E4 end `f̂(r′) ‖ 0^16` (32 B) at +2,112** | 6,416 | 2,144 |
| 10 | E end: `â_M ‖ b̂_M ‖ ĉ_M` (`finE`'s source) | 8,560 | 48 |
| 11 | RS0: partials `4 × 128 × 16`, claim-major | 8,608 | 8,192 |
| 12 | P1: 22 fold rounds × 96 | 16,800 | 2,112 |
| 13 | Pf: 7 final rounds × 96 | 18,912 | 672 |
| | rows 2–13 (PIOP messages) | | **19,408** |
| 14 | caps `cap₀ … cap₄` (level offsets 19,584 / 35,968 / 44,160 / 52,352 / 60,544) | 19,584 | 45,056 |
| 15 | final message: the level-4 fold, `2^7` K | 64,640 | 4,096 |
| 16 | columns: level 0 … 4, position by position (every index); items padded to 64-B multiples (revision 3.12) | 68,736 | 487,504 |
| 17 | siblings: level 0 … 4, position by position, leaf level first (11, 10, 8, 6, 5 per position) | 556,240 | 241,664 |
| | **total** | | **797,904** |

(The body order is the item order: E2, E4, E4 end and E end precede RS0. `48 + 128 + 19,408 +
45,056 + 4,096 + 487,504 + 241,664 = 797,904`; `sizes.py`; INT-2 §4.1.) `P30` fills its unused
rounds (2 of Z3, the second chain's share of S2, 12 of the final message's 16 … 128 K slots, the
last 2 siblings per position) with zeros.

### A.4 The item sequence `items` (468 FS items, then per position its queries; `FRTranscriptDefs`; revision 3.13 order)

| # | phase | items (in order) | absorb payload |
|---|---|---|---|
| 0 | seed | 1 seed (`vk ‖ c ‖ hdr`, 112 B) | — |
| 1 | stmt | 1 absorb | `stmt` (128 B, §1.1) |
| 2 | cap₀ | 1 absorb | 16,384 B |
| 3 | Z1 | 10 squeezes (19 free coordinates, 2 per answer) | — |
| 4 | Z2 | 1 absorb (row 2: `P^z` on `Λ₀…Λ₆₃`, then `P^{ab}` on `Λ₀…Λ₆₂`, 127 F + 16 zero bytes), 1 squeeze (`λ`) | 2,048 B |
| 5 | Z3 | 26 × (absorb round, squeeze) | 48 B |
| 6 | Z end | 1 absorb (`â ‖ b̂`) | 32 B |
| 7 | L1 | 1 squeeze (`α`) | — |
| 8 | L2 | 14 × (absorb, squeeze) | 48 B |
| 8′ | L3 | 1 absorb (the 8 `v_kind`, kinds incl. `free`; a leaf's at entry 0), 1 squeeze (`β`) | 128 B |
| 9 | S1 | 15 squeezes (`τ` 18, `θ` 10, `κ_s`) | — |
| 10 | S2 | 28 × (absorb, squeeze) | 48 B |
| 11 | Lr1 | 8 squeezes | — |
| 12 | Lr2 | 15 × (absorb, squeeze) | 48 B |
| 13 | Lr3 | 1 squeeze (`κ_L`) | — |
| 12′ | Lr end | 1 absorb (`â_L ‖ b̂_L ‖ ĉ_L`), after Lr2 | 48 B |
| 14 | ~~Lr4~~ | withdrawn (revision 3.13): Lr's lincheck is E4's second summand | — |
| 15 | E1 | 11 squeezes (positions 210–220) | — |
| 16 | E2 | 21 × (absorb, squeeze) (221–262) | 48 B |
| 16′ | E end | 1 absorb (`â_M ‖ b̂_M ‖ ĉ_M`), after E2 (263) | 48 B |
| 17 | E3 | 1 squeeze (`κ_E`) (264) | — |
| 18 | E4 | 23 × (absorb, squeeze) (265–310): the lincheck of `c₀^{E4}` over the `2^23` cells | 48 B per round |
| 18′ | E4 end | 1 absorb (`f̂(r′) ‖ 0^16`, bound by `finE` (v)) (311) | 32 B |
| 19 | RS0 | 1 absorb (the `4 × 128` partials) (312) | 8,192 B |
| 20 | RS1 | 4 squeezes (`r″` 7, `κ`) (313–316) | — |
| 21 | B′ | 1 squeeze (`κ′`) (317; P1.0 starts at 318) | — |
| 22+5i | P1.i | `ℓᵢ` × (absorb K round 96 B, squeeze) | |
| 23+5i | C.i | 1 absorb: `capᵢ₊₁` (8,192 / 8,192 / 8,192 / 4,096 B) or the final message (4,096 B) | |
| 24+5i | P2.i | 25 / 13 / 10 / 8 / 6 squeezes | — |
| 25+5i | Q.i | for each of the `tᵢ` indices: 1 column query, then 11 / 10 / 8 / 6 / 5 Merkle-node queries leaf level first (`P30`: the last 2 of each are dummies `0^64`) | |
| 26+5i | P3.i | **5 squeezes** (`κ_c`, 9 F coordinates) | — |
| 47 | Pf | 7 × (absorb K round 96 B, squeeze) | |

Every absorb's payload is the field listed; every squeeze's answer is consumed as A.2 says, in
order of appearance. `items_length = 8,891` (revision 3.13).

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
| `stream` | digest chain blocks `1 … N−1`; key-leaf blocks `1 … 65` | `1024…1152` | `t_lo = 64(i+1)` (chain-relative; the last block of a digest chain: `1,437,760`; of the key leaf: `4,265`), `t_hi = 0`, `f0 = 0xFFFFFFFF` on last blocks else `0`, `f1 = 0`, `one = 1` |
| `streamStart` | block 0 of each digest chain | `0…255`, `1024…1152` | `h0`; `t_lo = 64`, `f0 = 0`, … |
| `streamEnd41` | the key leaf's last block (41-byte tail) | `840…1023`, `1024…1152` | zero; `t_lo = 4,265`, `f0 = 0xFFFFFFFF` |
| `hashA` | `hashStmt` A (leafStmt, 41 bytes) | `0…255`, `512…519`, `840…1023`, `1024…1152` | `h0`; `0x4C`; zero; `t_lo = 41`, `f0 = 0xFFFFFFFF` |
| `hashB1` | `hashStmt` B1 (nodeStmt block 1); key-leaf block 0 (tagWotsLeaf); path blocks 1 (sigNode) | `0…255`, `512…519`, `1024…1152` | `h0`; the tag (`0x4E` / `0x4B` / `0x4D`); `t_lo = 64`, `f0 = 0` |
| `hashB2` | `hashStmt` B2; path blocks 2 | `520…1023`, `1024…1152` | zero; `t_lo = 65`, `f0 = 0xFFFFFFFF` |
| `w43` | WOTS chain steps (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x`, 43 bytes) | `0…255`, `512…519`, `584…599`, `856…1023`, `1024…1152` | `h0`; `0x57`; `i`, `s` of the block's step (per block); zero; `t_lo = 43`, `f0 = 0xFFFFFFFF` |
| **`free`** | the M, L, `WM` and spare blocks (`Sel ≡ 1`: every block has a kind) | none: rows `(var k, var k)` at every position, `E = 0` — satisfied by every Boolean `z` (`z_k² = z_k`); `A₀^{free} = B₀^{free} = I` (revision 3.8.1, BP-C-R5-M1: `(var k, one)` would force the unpinned bit 1,152 to 1) | — |
| `WM` (no block matrix of its own: kind `free`) | the mirror sub-region, **146 blocks per slot after both WOTS runs** (`wmBase = wotsBase + 2·498 = 47,294`; `wmB σ = wmBase + 146σ`; the last block 47,585 `< lBase = 47,616`; `FRNodeLayout.wmSlot = 146`, `hEnd = 47,594`): **mirror source `g` of slot `σ` is block `wmB σ + ⌊g/4⌋`, positions `256·(g mod 4) + [0, 256)` (elements `2(g mod 4)`, `+1`; shorter fields zero-padded)**; `g = off_f + t`, `off_f`: `x` 0 (399 sources), `j` 399 (1), `end9` 400 (67), `end41` 467 (66, shared by `end41lo`/`end41hi`), `l` 533 (16), `r0` 549 (16), `r31` 565 (16): 581 sources of 584 (revision 3.14, S-CN D-2/D-3; replaces 3.13's `2·(off_f+t)+p` map, whose elements `≥ 8` no `linkW` could read) | — | — |

(`h_in` of `stream`, `streamEnd41`, `hashB2` blocks is the previous block's output, wired by the
shift argument (digest chains, key leaf) or by element equalities (`hashStmt`, path block 2);
`w43`'s `x` and `j`, the key leaf's ends and `j`, and the path's `l`, `r` are wired by the link
families of §4.2 (aligned mirror cells in `WM`, the shift argument with a slot map); `hashB1`/
`hashB2`'s `stmt` bytes by element equalities; the `stream` message is the trace.) The
indicator `Ind_kind` is the union of the kind's block intervals in the layout (`FRNodeLayout`),
`Sel = ∪ Ind_kind`. **Dump KAT (P2, S-E2)**: the Lean dump tool writes every kind's `A₀^kind`,
`B₀^kind` rows and target `E` (one block per kind and the per-block patterns as formulas); the
prover's row generator must reproduce them.

### A.7 The node's M and L layout and the pack map

- **Public cells** (`finB′`, S-F deviation 7; one order for S-E2's `PubCells`, `finPf`'s `eq(cell_k, ρ)` weights and the prover): `pub_0 =` M's `one` cell `f[Mbase] = 1`; then slot 1's `vk` (halves: `pub_1, pub_2`) and `c₁` (`pub_3, pub_4`); then slot 2's `vk` (`pub_5, pub_6`) and `c₂` (`pub_7, pub_8`); **no padding cells** (INT-2: the stream is `64 · 23,146` bytes, `stream_padded` holds without them; S-E3 D-6). A half `k` of slot `σ`'s seed payload element `e` is the H cell `(chainBase_σ + ⌊(1+e)/4⌋)·128 + 4 + (1+e) mod 4` (the seed payload starts at stream element 1; `vk` = payload elements 0–1, `c` = 2–3). `pub_k` enters `v*` with `κ′^{k+2}`.
- **Pack**: `f[e]` is the F element whose 16 bytes are bits `[128e, 128e + 128)` of `z`, byte `b`
  = bits `[128e + 8b, 128e + 8b + 8)` low bit first; `c₀ = bytes 0…7`, `c₁ = bytes 8…15` LE. A
  block's element `k` (`k < 128`) is `f[blk·128 + k]`.
- **L** (base block **47,616** = `lBase`, the first multiple of 256 after H's end 47,594; element addresses relative to `Lbase = 47,616·128`): per slot `σ`
  (stride `2^14` elements): `sig` 299 elements (`idx` 1, `ots` 133 × 2, `path` 16 × 2), digits
  266 as bit-elements (two per base-4 digit, 133 digits incl. the checksum's; F-5), step selectors 399, position bits 7,552 (the bit-elements `(b, 0^127)`),
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
| `phiRS r″ a → F` | `AF 7, F → F` | `Φ_{r″}(a)` (the staged Frobenius map, 127 squarings + 7 products; `FRRingSwitch.Phi`) | 134 |
| `rsWeight r″ pts κ β ρ → K` (revision 3.16) | `AF 7, J_z × AK (m−7), F, F, AK (m−7) → K` | `Ŵ(ρ) = Σ_j κ^j Ŵ_j(ρ)` with `Ŵ_j(ρ) = Σ_{k<128} c_k(r″) eq(r_j^{2^k}, ρ)` (`weightEval`, L-R4) for the claims' outer points `r_j` (Z: `(r_blk, r_hi7)`; Sh: `(r_blk, r_pos,hi)`; E4: `r′`, the packing basis as inner weight), **except claim 2 (Lc, node only), whose outer weight is `eq(r′_blk, t)·B_β(t)·eq(r_k, j)`, `B_β = Σ_κ β^{i(κ)} Ind_κ`: `Ŵ₂(ρ) = Σ_k c_k Σ_κ β^{i(κ)2^k}·eq(p_hi^{2^k}, ρ_hi)·Σ_{t∈I_κ} eq(p_blk^{2^k}, t) eq(ρ_blk, t)`** (R-V-M1 (a): the kinds' pattern intervals — chains, `hashStmt` singles, `w43` runs, key leaves, the even/odd path blocks, `free` as the complement — as dyadic range sums with the bit pattern as a per-bit factor; ≈ 128 · 22 · 24 ≈ 68 k products; a leaf's factor is 1); a leaf passes 3 points — **replaces `mbp` and `kindFoldWeight`** | `J_z · 128 · (m−7)` + 68 k (node) |
| `eqZ λ ρ₁ → AF 128` | `F, F → AF 128` | the Z claim's inner weight over an element's 128 bit positions: `L_{lo(i)}(λ) · eq(ρ₁, bit 6 of i)` (A.2: bit 6's coordinate is the first pinned coordinate `ρ₁`, not Z1's first free coordinate) | 128 |
| `walkAB rowW′ colW → F × F` (one op since 3.12) | `AF (2^14), AF (2^14) → F × F` | `Â₀`, `B̂₀` by the circuit walk (`walkE_eq_sum`, the gadget DAG of §4.4) with the row weights `rowW′[k] = rowW[k] · Σ_{kind ≠ free : k ∉ pinned(kind)} v_kind` built by `maskRows vKinds rowW` (**`free` has weight 0 in the mask, R-V-M2**; its term `(1 + α)·v_free·⟨rowW, eq(r_k,·)⟩` is the closed form `(Σ_{s<64} L_s(λ) eq(r_k[0..5], s))·eq(r′_hi, r_k[6..13])`, one `eqPt` and a 64-term sum, added in `finLc` (ii)) | lincheck replay + `2^14` |
| `kindInd r′ → AF #kinds` (spec-level; not an op of `gen`) | `AF (m−14) → AF 8` | the indicator MLEs `Ĩnd_kind(r′)` (prefix sums over the kind's pattern intervals); used inside `rsWeight`'s claim-2 factor (`B_β`'s Frobenius powers) and by `maskRows`' spec | `O(log)` each |
| `evalM τ σ → F × F × F`, `evalL τ σ → F × F × F` | `AF 21, AF 23 → …`; `AF 15, AF 23 → …` | the node's matrix MLEs (kind-selected) | `evalM`/`evalL` replay |
| `targetS r → AF 64` | `AF (m−6) → AF 64` | `P^e(σ) = Σ_{x'} eq(r,x') E(x', σ)` for `σ ∈ S` (per kind and pinned position: interval prefix sums and affine-bit MLEs; `targetS_eq`, S-C). `selWeight` and `targetMLE` are withdrawn (`Sel ≡ 1`, skip-c). **Node form (revision 3.13, S-G1j §1.3; `targetSNodeS`, owner S-C; `targetSNodeI` + `_meets` S-F2/L-circ; `implC` selects it by `s_N`):** `Σ_kind Σ_{I ∈ intervals(kind)} Σ_{blk ∈ I} eq(r, blk)·E_kind(blk, σ)` over A.6's nine kinds and `nodeLayout`'s intervals (two chains, `hashStmt` A/B1/B2, WOTS steps, key leaves, path blocks, `free`): constant bits (`h0`, tags, zeros, the fixed `t_lo`/`f0`/`one`) give `E_kind(σ)·` a dyadic range sum of `eq(r,·)` (`rangeEq_mle`, `O(log)` per interval); `stream`'s counter `t_lo = 64(k+1)` (`k` chain-relative) gives, per bit `j`, `Σ_k eq(r, blk₀ + k)·(k_j + Π_{i<j} k_i)` (char 2: bit `j` of `k+1`), a shifted range sum (`shift_mle`, `O(log²)`); the last-block fields (`t_lo = 1,481,344 = 64 · 23,146`, `f0`; the key leaf's `4,265`) are single-block terms `eq(r, blk)` (S-CN's `blockTarget 1481344 true`); `w43`'s `i = ⌊o/3⌋`, `s = o mod 3 ∈ {0,1,2}` are not bit-affine at stride 3 and are an explicit sum over the 399 step blocks from an `eq(r,·)` table (`399 + 16·399` products; the stride-4 layout alternative is declined to keep `ind_wots`/`nodeBK_wots`). Cost `≈ 10 k` products; its template `tplTargetSNode ≈ 10 k` rows (A.11) | `O(#kinds · #pinned)` |
| `lagrangeS vals λ pe → F × F` | `AF 127, F, AF 64 → F × F` | `(P^{ab}*(λ), P^z*(λ))`: `P^z*` through `Λ` from `vals[0…63]`, `P^{ab}*` through `S ∪ Λ₀…₆₂` from `pe + vals[0…63]|_S` and `vals[64…126]` (replaces the single-output form) | ≈ 800 |
| `shiftTarget τ θ bnd → F` (INT-4) | `AF 18, AF 10, AF 22 → F` | the shift sumcheck's boundary term `eq(ptA 18 τ, last)·h̃V(θ) + κ_s s̃V(θ)` with `bnd` = the four boundary values (leaf: `s`, `h` as two elements each from `hdr`/`stmt`; node: zeros — the node's target is 0 with the chain-masked start term) **then the kind's last block `last = bnd[4 … 21] = 1^(m−14) ‖ 0^(32−m)` as constant registers** (`bndOps`, `padB`; a zero-padded `τ` would break P30's fixed `1^18`): `shiftTargetAt`, `shiftTargetS_pad`; `θ`'s 10 coordinates read a slot position `σ < 256` as a 10-bit index (factor `(1+θ₈)(1+θ₉)`, P2 §7.5 (4)) | `O(m)` |
| `slotW θ pos r → F` | `AF 10, slot map, AF 10 → F` | **the In slot is selected in `finSh` by `keep`** (node: `h_in`, map 2, base 0; leaf: `d`, base 520; INT-3); the collapse's slot weight `Σ_σ eq(θ,σ)·eq(cube(pos σ), r)` summed directly for the unaligned `d` slot (`520…775`: 256 terms × ≈ 14 products, S-C-m1); the aligned `h_in`/`h_out` slots by `slotW_mle_aligned` | ≈ 3.6 k |
| **cell-reading ops `eqPt`, `rowW`, `shiftEq`, `linkW`** | — | these read fixed cells or public tables and compile to **imports**: the compiler emits no row for them; their cell values enter `compile_sound` as hypotheses (the imported cells' values), discharged in `final` by the zerocheck/shift/RS facts that fix those cells (S-G), exactly as the trace imports are | 0 (imports) |
| **`linkWAll κ (τ ‖ θ) (r_blk ‖ r_pos) → AF 8`** (revision 3.14; replaces `linkW τ fam r_blk → F`) | `Kind, AF 26, AF 26 → AF 8` | the 8 link families' weights **at the Sh sumcheck's point** `(r_blk, r_pos)` with S1's `(τ, θ)`, in one op with shared tables (S-CN §6.3: 1.9 ms measured on the VM against 4.35 ms for 8 separate calls), read by 8 `getF`; `finSh` packs `τ ‖ θ` (S1's 16 block coordinates, then its 10 slot coordinates) and `r_blk ‖ r_pos` (S2's 16, then 10); a leaf's result is `0^8`; the families' powers are `κ_s^{f+2}`, `f < 8` (`κ_s` weights the start term). **Definition (`linkWAllS`, `linkW_mle`, `linkInd_sum`: owner S-C, delivered by S-CN; `linkWAllI` + `linkWAll_meets`: S-F2/L-circ; `tplLinkWAll`: S-E; the mirror writes: P2):** per slot the 8 families `f` with sources `t < n_f` at block `src_f(t)`, field `[off_f^B, off_f^B + len_f)` and mirror source `g_f(t)` (A.6): `x` (`wotsBase + 3i + s`, 399, offset 11, 32 B), `j` (the 399 step blocks and key-leaf block 0, offset 1, 8 B, one mirror source), `end9` (key-leaf block `u` of the 67, offset 9, 32 B: the even ends), `end41lo` (block `u`, offset 41, 23 B, mirror bits 0–183), `end41hi` (block `u+1`, offset 0, 9 B, mirror bits 184–255; `u < 66`), `l` (path blocks 1 `466 + 2t`, offset 1, 32 B), `r0` (path blocks 1, offset 33, 31 B), `r31` (path blocks 2 `467 + 2t`, offset 0, 1 B). `W_f = Σ_{t<n_f} eq(τ, src_f(t))·[eq(r_blk, src_f(t))·slotW(field_f, r_pos) − eq(r_blk, mirBlk(g_f(t)))·slotW(mirPos(g_f(t)), r_pos)]` (char 2; `slotW` by `rangeEq_mle`); the eq factors are `n_f`-term table sums. Cost ≈ `6 n_f + 24 len_f` products per family with the generic loop (S-CN §7), ≈ 1.9 ms in all; **`tplLinkWAll` ≈ 15 k rows per slot** (A.11). `truthS1`'s node `ShHolds` is the chain-masked `shift_sound` identity with these 8 terms (owner S-G) | `O(Σ n_f + log)` |
| `rowW λ r′_hi → AF (2^14)` | `F, AF 8 → AF (2^14)` | the lincheck's row weights: Lagrange at `λ` on the skip slice ⊗ `eq(r′_hi, ·)` on the 8 high position bits; spec `rowW_eq` (S-C) | `2^14` |
| `shiftEq τ r → F` | `AF 18, AF 18 → F` | `shift(τ, r)`, the MLE of the successor map on block indices (paper §4.6); spec `shiftEq_eq` (S-C) | `O(m)` |
| `shiftMask τ r → AF 3` (INT-3, revision 3.15) | `AF 18, AF 18 → AF 3` | the node's chain mask for the Sh tables (§4.2): `Ind_chain` at `(τ, r)` for the `Out` term, the shifted mask for the `In` term and the start term `eq(0,·) + eq(chainBase_2,·)` (target 0 in characteristic 2); `shiftMaskI`/`shiftMaskS`, `tplShiftMask_ok` (S-E9); a leaf's mask is 1 | `O(m)` |
| structural ops delivered by S-0 (`input`, `const`, `packF/packK/packFK`, `getF/getK`, `piElemK`, `piDigestAt`, `eqTableK`, `dotKF`, `shrN`, `keep`, `kindSel`; `askNode` with depth and activity, `askAbsorb` with its static length, `askSeed hdr`) | as `FRVIR` | S-0 RESULT deviation 1 | — |
| ~~`kindFoldWeight`~~ | — | **withdrawn (revision 3.16)**: `W_β`'s kind factor is `rsWeight`'s claim-2 weight in Φ form (R-V-M1); the 3.9 `gen` never wired it (`kindFoldWeight := 0`) | — |
| `splitDigest d → F × F`, `selectHalf b l r → D` | | | 0 / 2 |
| `hashStmt kind fields → D` | `B → D` | `leafStmtF`/`nodeStmtF` | 1–2 H blocks |
| `assertEq a b`, `assertBit b`, `assertZero a` | | checks; a failure returns `false`. **`assertBit` (revision 3.16, R-V-m1): implemented — clears `ok` unless the operand is a bit (`.bit _`, or the F value 0 or 1) wherever `act κ` holds; unused by `gen` (count 0 in every dump), control `assertBit_rejects`** | 1 linear (gated: 1 product) |
| `assertOneHot s₁ s₂ s₃` | `Bit³` | `s₁s₂ = s₁s₃ = s₂s₃ = 0 ∧ Σ sᵢ = 1` (BP-C-R3-M1) | 3 products + 1 linear |
| `accept` | | `true` | — |

This table is the op set; `gen` uses no other op. Dump format (`probe/fr-irdump/`): one line per
op, `opName operands… → dst`, registers numbered; the Rust generator's output is compared line by
line (P1 KAT).

---

### A.9 Phase-final checks (`FRVIRFinals.Finals`; S-0-M1)

`Finals` is a structure with one field per phase; **`gen fin` appends the finals after the whole
skeleton**, in the order `finRS, finZ, finLc, finSh, finLr, finE, finB′, finP 0…4, finPf` (`finZ`
and `finSh` need the RS-certified values that `finRS` computes from RS0's partials). They ask
nothing (`items_gen`), so the transcript is unchanged, and no challenge depends on a final having
passed (assertions set a flag; `V` is the flag at the end). Every degree-2 and K sumcheck's **initial claim is
free** (the prover's first message fixes it) and must be bound by a final check; the table names
the binder. `c_X` is phase X's last round value at its challenge; `ẑ_X` the RS-certified value of
X's `z`-claim; all registers are the phase outputs of S-0's `gen`.

| Field | Relation checked at the phase's end (over the transcript values) | Free claims it binds | Op shape | Owner, lemma |
|---|---|---|---|---|
| `finZ` | `eq(r, r′)·â·b̂ = c_Z` (§2.3 step 2, skip-c); the c-claim `ẑ(r, λ) = P^z*(λ)` is RS claim 1 | none (Z3's initial claim is `P^{ab}*(λ)` from `lagrangeS`) | `eqPt`, 2 `mulF`, `assertEq` | S-0 fix pass, `exec_finZ` (re-done for skip-c) |
| `finLc` | (i) `c₀^{Lc} = â + α b̂`; (ii) `c_{Lc} = walk(rowW′, eq(r_k,·)) + (1 + α)·v_free·⟨rowW, eq(r_k,·)⟩` with `rowW′[k] = rowW[k]·Σ_{kind ≠ free, kind ∌ k} v_kind` (`rowW` = Lagrange at `λ` ⊗ eq on the 8 high bits; **`free` has mask weight 0 and its term is the closed form `(Σ_{s<64} L_s(λ) eq(r_k[0..5], s))·eq(r′_hi, r_k[6..13])`**, R-V-M2; `linM_free`); (iii) `v_β := Σ_kind β^kind v_kind = α_Lc` — RS claim 2, **whose weight carries `B_β`'s kind factor in `rsWeight` (R-V-M1)** | L2's initial claim | `eqTable` (row/col), `maskRows`, `walkAB`, `eqPt`, the 64-term sum, `mulF` (α), `addF`, `assertEq` ×2, powers of `β` | S-0 (revision 3.16), `exec_finLc` (algebra: S-C's `lin_final_kinds`, `linM_free`, `lin_beta_claim`) |
| `finSh` | (i) `c₀^{Sh} = shiftTarget τ θ bnd` (leaf: the boundary `s`, `h`; **node: 0** — the chain-masked start term `κ_s(eq(0,·) + eq(chainN,·))` has target 0 in characteristic 2 and both `h0`s are pinned by `streamStart`, INT-3 D3; `bnd` of 22 entries, INT-4); (ii) `c_{Sh} = (w_out(r) + w_in(r))·ẑ_{Sh}` (**one claim** at `(r_blk, r_pos)`) with `w_out = eq(τ,r_blk)·mask_out·slotW_out(θ, r_pos)`, `w_in = (shift(τ,r_blk)·mask_in + κ_s start)·slotW_in(θ, r_pos) + Σ_{f<8} κ_s^{f+2} · linkWAll[f]` (`shiftMask`; `slotW_in` by `keep`; §4.2's 8 link families) | S2's initial claim | `shiftTarget`, `shiftMask`, `slotW` ×2, `linkWAll` + 8 `getF`, `mulF`, `addF`, `assertEq` ×2; outputs RS claim 3 (`w_out + w_in` at the one point) | S-0 (INT-3/INT-4), `exec_finSh` (algebra: S-C's `shift_sound_masked`, `slotW_mle`, `linkW_mle`) |
| `finLr` | (i) `c₀^{Lr2} = 0` **by `initClaim`** (no assert); (ii) `c_{Lr2} = eq(r_Lr, r)·(â_L b̂_L + ĉ_L)`; (iii) exports `v_L := â_L + κ_L b̂_L + κ_L² ĉ_L` and `r_{Lr}` := Lr2's final point to `finE` (revisions 3.13–3.14; `nodeOnly`: a leaf exports 0) | none | `mulF` ×3, `addF`, `assertEq` ×1 | S-0, `exec_finLr` |
| `finRS` | for each claim `j < 4`: the column check **defines** `α_j := Σ_i w_i^{(j)} s_i^{(j)}` (inner weights: `eqZ λ ρ₁` for Z, `eq` on the element's 7 bits for Lc and Sh, **the packing basis for E4's `f̂(r′)`**); the switched claims `T_j = Σ_i b_i Φ_{r″}(s_{j,i})`; **`v_RS := Σ_j κ^j T_j`** is Ligerito's input value (a leaf: 3 claims, the fourth's slices asserted zero and `T₃` omitted when E's L term is absent); `Ŵ` is evaluated only at the final point (`finPf`, `rsWeight`, with claim 2's kind factor) | none (RS has no rounds); the `α_j` are **computed, not asserted** (`rs_column`), and bound where they are used: `finZ` (`α_Z = P^z*(λ)`), `finLc` (`v_β = α_Lc`), `finSh`, **`finE` (iv)–(v) (`α₄`)** | `packF`, 4 × 128 (`mulF` + `addF`), 4 × 128 `phiRS` + `mulF`, powers of `κ` | S-F (delivered), `exec_finRS` |
| `finE` | (i) `c₀^{E2} = 0`; (ii) `c_{E2} = eq(r_E, r_{E2})·(â_M b̂_M + ĉ_M)` at the zerocheck's final point `r_{E2}`; (iii) `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L` (revision 3.13); (iv) `c_{E4} = ((Ã_M + κ_E B̃_M + κ_E² C̃_M)(r_{E2}, r′) + κ_E³ (Ã_L + κ_L B̃_L + κ_L² C̃_L)(r_{Lr}, r′))·α₄` with **`evalM(r_{E2}, r′)` and `evalL(r_{Lr}, r′)` at the F point `r′`** (the only matrix evaluations in `V`) and `α₄` = RS claim 4's column value (`rs_column`); **(v) the E4 end message equals `α₄ ‖ 0^16`** (every kind; a leaf's `α₄ = 0` by `finRS`'s zero check; INT-2) | E4's initial claim; the E4 end message | `evalM`, `evalL`, `mulF` ×7, `addF`, `assertEq` ×6 | S-F / S-G (revisions 3.12–3.14), `exec_finE` |
| `finB′` | `v* := v_RS + Σ_{k<9} κ′^{k+2} pub_k` (`pub_k`: M's `one` cell and the 8 `vk`/`cᵢ` halves of A.7; **no `κ′ v_E` term since revision 3.12** — the E claim is RS claim 4 — and **no padding cells** since INT-2: the stream is `64 · 23,146`; the powers `k+2` keep the Lean's order) = the initial claim of P1.0 | P1.0's initial claim | `mulF`, `addF`, `assertEq` | S-F, `exec_finB′` |
| `finP i` (level `i = 0 … 4`) | (i) `c_{P1.i}` (after the `ℓᵢ` fold rounds) = the running claim `v_i` folded; (ii) for each queried index `j`: `fold_j = dotKF(column_j, eq(z_i,·))` and (`i < 4`) the next claim `v_{i+1} := v_i + Σ_j eq(κ_c, j)·fold_j`, whose weight adds `Σ_j eq(κ_c,j)·G_j` with `Ĝ_j(ρ) = tensorW j ρ` (A.1); (`i = 4`) `fold_j = Enc₄(final)[j]` computed from the final message (`2 k₅ … = 2^7` K×F products per `j`) | P1.(i+1)'s initial claim (level 4: Pf's) | `eqTableK`, `dotKF` × `tᵢ`, `tensorW` deferred, `mulK`, `addK`, `assertEq` | S-G (with L-pcs), `exec_finP` |
| `finPf` | `c_{Pf} = Ŵ(ρ)·final̂(ρ)` with `final̂(ρ)` the multilinear evaluation of the `2^7` K final message at `ρ` (`P30`: the weight zero-padded, `·(1+ρ₅)(1+ρ₆)`) and `Ŵ(ρ) = rsWeight r″ pts κ ρ` (the leaf omits the fourth weight, as `v_RS` does) (revisions 3.12–3.13: **no `evalM`/`evalMK` term**: the E4 claim is RS claim 4) `+ Σ_k κ′^{k+2} eq(cell_k, ρ)` (A.7's order) `+ Σ_i Σ_j eq(κ_c^{(i)}, bits₉(j))·tensorW(j, ρ_i)·(the fold factors of levels > i)` | Pf's initial claim = level 4's claim | `rsWeight` (4 claims), `tensorW` × `Σ tᵢ`, `eqTableK`, `mulK`, `addK`, `assertEq` | S-G, `exec_finPf` |

Budget 1,200 lines (S-0-m7): S-0 fix pass 500 (Z, Lc, Sh, Lr), S-F 300 (RS, E, B′), S-G 400 (P i,
Pf). `node_sound`'s M-row count and P2's dump KAT use `gen fin` with every field present
(`ops-*.txt` re-dumped); `KState.final` is proved for `gen fin`, so a missing check is an
unprovable `final`, never a silent hole.

### A.10 Per-phase truths (the soundness interface; S-G1c)

**The front's interface (S-G5/S-G6, revision 3.15):** phase 2's doom is `DF 2 := far₀ ∨ ¬Stmt`
(the statement check joins `far₀` as the first background term); the extractor's interface is
`ExtIface`; **the RS claims are checked through the finals' slice equations** (`finRS`'s
`rs_column` values, bound where `finZ`/`finLc`/`finSh`/`finE` use them), not by a separate RS
truth. The per-phase rows below are read with these.

**Composition (ratified).** The entry's doom is `D L es := Rej L es ∨ D_φ(es) L es`, where `φ(es)` is
the phase containing position `|es| − 1` (`fsStarts`), `Rej` is "an asserted check of an earlier
position fails" (monotone under appending), and `D_φ` is the phase's own doom below. Handoff: a
phase that starts with an **absorb** (rounds phases, `Zend`, `L3`, `Lrend`, `RS0`, `Eend`, `C.i`)
takes over at that absorb by `habs` (the previous phase's doom at its last position is the new
phase's doom at the absorb: a false initial claim); a phase that starts with a **squeeze** (Z1
after `cap₀`, L1, S1, E1, B′, P3.i) takes over by the escape count at that squeeze (`hsingle` or
`hround`). `rnd 0 = none` (the seed). Every truth below is **local** (`TruthLocal`: it reads the
chain's entries before the phase and the log) and **stable** (`TruthStable`: it reads the same
values off `L.take i` and `L` on a non-bad log); the stability column names the reads.

Notation: `es` the chain, `L` the log; `κ = kindOf es`; `wordOf κ L es i` the level-`i` word read
under its cap (`colOf`, `colL (frEnc i)`), `far_i := FarAt κ C_K e_i L es i`; `f⁽ⁱ⁾ := decode_i
(wordOf … i)` (the message `interp_F` + `coeffs_of_values` from any `k_i` positions of the
agreement set; `S-D2`'s `coeffs_of_values`), defined when `¬ far_i`; `z := unpack f⁽⁰⁾`; `A₀^κ`, `E`
from `FRBlockLayout`/`FRPubTarget` per kind; challenges by the readers (`fAt`, `kAt`, `coordAt`,
`posAt`); `c₀^X` the phase's initial claim and `c_X` its running claim (`clR`). Owners: **S-G1c**
writes the definitions named `truth*`; the count lemmas are S-C/S-D's.

| Phase | Truth (tables, initial claim) | Doom form | Count lemma (`hsingle`/`hround`) | Handoff | `hstab` needs |
|---|---|---|---|---|---|
| Z1 (10 squeezes, 17/19 coordinates) | the point `r = (ρ₁…ρ₇, coordAt …)`; truth: the zerocheck identity `∀ x ∈ cube: (A₀^κ z)(B₀^κ z) = z + E` on the decoded `z` (`truthZ0 κ L es := ∀ blk pos, Sel … → …`); doomed at Z1's end iff `z` violates it **and** `P^{ab}_r − P^z_r − P^e_r` vanishes on `S` (the next phase's check) | `far_0 ∨ (¬ Holds z ∧ skipRes r = 0 on S)` | `hround`: `zerocheck_bad_le` (DT24 pinned + SZ over the free coordinates: `17/2^128`) with `pair_bad_le`/`seq_bad_le` over `coordAt`, `card_chF2_fiber` | escape at Z1's first squeeze (after `cap₀`'s absorb) | `wordOf … 0` under `cap₀` (absorbed at position 2): `colL_prefix` from `¬ Bad`; the window case of the cap's own absorb |
| Z2 (absorb 127 F, squeeze `λ`) | `P^z|_Λ`, `P^{ab}|_{Λ₀…₆₂}` as sent; truth: `P^z_r(Y) = Σ_{x'} eq(r,x') z(x',Y)`, `P^{ab}_r(Y) = Σ eq(r,x') a b`, `P^e_r` (`FRSkip.z2Vals`, `truthZ2`); Z3's initial claim `c₀^{Z3} = P^{ab}*(λ)`; the RS claim `α_Z = P^z*(λ)` | `(P^{ab}*, P^z*) ≠ (P^{ab}_r, P^z_r) ∧ P^{ab}*(λ) = P^{ab}_r(λ) ∧ P^z*(λ) = P^z_r(λ)` (`Wrong` at the squeeze; `Rej` if the 16 padding bytes are nonzero) | `hsingle`: `skip_pair_bad_le` (126) with `card_chF_fiber`: `N = 126·2^128` | `habs` at Z3's first absorb (`D3_first_absorb`): `c₀^{Z3} ≠ Σ_{x'} eq(r,x') a_λ b_λ` | as Z1 (the same word) |
| Z3 (26 rounds, degree 3) | tables `T = [eq(r,·), a_λ, b_λ]` over `2^(m−6)`, `e = w·a·b` (`bz_trueSum`, `FRSpartan`); truth = `D3 15 c0 (mm 6) e T` as delivered (`z3_step`) | `D3` | `D3_single`: `round_escape_le`, `card_chF_fiber`: `N = 3·2^128` | `habs` at `Zend`: `eq(r,r′)·â·b̂ ≠ c_Z` (`finZ`); the lincheck's truth takes `â, b̂` from `Zend` | as Z1 |
| Zend (absorb `â ‖ b̂`) | `â = (A₀z)̂(r_row)`, `b̂ = (B₀z)̂(r_row)` at the quirky point (`truthZend`) | `â ≠ truth ∨ b̂ ≠ truth` given `finZ` passes | — (`habs`: an absorb) | L1's squeeze | — |
| L1 (`α`) | batching `â + α b̂ = Σ_kind Σ_j M_kind(j) zfold_kind(j)` (`lin_trueSum_kinds`) | `Wrong`: the batched identity false though `â` or `b̂` wrong | `hsingle`: `batch_bad_le` at 2 (`1·2^128`) | `habs` at L2's first absorb: `c₀^{L2}` free, bound by `finLc` (i) | — |
| L2 (14 rounds, degree 2) | tables `[M_κ-weights, zfold_kind]` over `2^14` per kind; `e` degree 2; initial claim `â + α b̂` | `Rej ∨ Wrong2` (the verifier asserts `c₁ + c₂ = claim`) | `round_escape_le`, `card_chF_fiber`: `N = 2·2^128` | `habs` at L3's absorb (the 8 `v_kind`): `v_kind ≠ zfold_kind(r_k)` for some kind | reads `z` (the word) and `A₀^κ` |
| L3 (absorb 8 `v`, squeeze `β`) | `v_β := Σ_kind β^kind v_kind`; truth `⟨W_β, z⟩` (`truthL3`) **with `W_β`'s kind factor, carried into RS claim 2 by `rsWeight` (revision 3.16; `gL`/`trueL` mirror it)**; `finLc` (ii) asserts the walk with `free`'s closed-form term | `Rej ∨ (some v_kind wrong ∧ Σ β^kind (v_kind − truth) = 0)` | `hsingle`: `batch_pow_bad_le` at 9 (`8·2^128`) | S1's first squeeze (escape) | — |
| S1 (15 squeezes: `τ`, `θ`, `κ_s`) | the shift identity with the boundary (`shiftTarget`) and ≤ 8 link families (`truthS1`: `ShHolds z s h` of §4.1/§4.2) | `far_0 ∨ (¬ ShHolds ∧ the batched sum at (τ,θ,κ_s) equals the target)` | `hround`: SZ over 26 coordinates + `batch_pow_bad_le` at degree 9 (8 families): `(26 + 9)/2^128`, via `pair_bad_le`/`seq_bad_le`, `card_chF2_fiber` | `habs` at S2's first absorb: `c₀^{S2} ≠ shiftTarget …` | the word; the mirror cells (M region of `z`) |
| S2 (28 rounds, degree 2) | tables `[eq(τ,·)·Out, (shift + κ_s eq(0,·) + Σ κ_s^f linkW)·In]` over blocks then the 10 slot bits (`FRShift.shift_sound`, `slotW_mle`) | `Rej ∨ Wrong2` | `round_escape_le`: `N = 2·2^128` | `finSh` (ii): `c_{Sh} ≠ (w_out + w_in)·ẑ(r_blk, r_pos)`; the claim `α_Sh` is RS's | — |
| Lr1 (8 squeezes) / Lr2 (15 rounds, degree 3) / Lrend / Lr3 (`κ_L`); **Lr4 withdrawn (revision 3.13): the lincheck is E4's, over the `2^23` cells; `truthLr` keeps the zerocheck half, the lincheck truth is `truthE4`'s** | Spartan over the L rows (node only; `nodeOnly`): zerocheck tables `[eq(r_L,·), A_L z, B_L z, C_L z]` (`truthLr`), `Lrend` carries `â_L, b̂_L, ĉ_L`; lincheck of `â_L + κ_L b̂_L + κ_L² ĉ_L` with `evalL` (`FRVIREval`) | Lr1: `hround` form; Lr2: `D3` (`lr2_phase`); Lrend: `habs`; Lr3: `Wrong`; Lr4: `Rej ∨ Wrong2` | Lr1: SZ 15, `pair_bad_le`; Lr2: `D3_single`; Lr3: `batch_bad_le` at 3 (`2·2^128`); Lr4: `round_escape_le` | none: the L lincheck is E4's and its claim `f̂(r′)` is RS claim 3 (no Lr RS claim since 3.13) | reads `z`'s L region; `A_L` public |
| RS0 (absorb `4 × 128` partials) / RS1 (4 squeezes: `r″`, `κ`) | per claim `j`: the column check **defines** `α_j` (`rs_column`); the switched claims `T_j = rsT` and `v_RS = Σ κ^j T_j`; truth `rsTruth` (`Σ_u Φ(g_j(u)) f(u)`) with `g_Z = eq(r,·)`, `g_Lc = eq((r′_blk, r_k),·)`, `g_Sh = eq((r_blk, r_pos),·)`, `g_Lr` (`truthRS`) | RS0: `habs` (a wrong partial, `δ_j ≠ 0`); RS1: `Wrong`: some `δ_j ≠ 0 ∧ Σ κ^j rsT = Σ κ^j rsTruth` | `hround`: **`rs1_joint`** (`(7 + J_z − 1) = 10` of `|F|^7` draws), `card_chF2_fiber` | `habs` at E1 (node) / at B′'s squeeze (leaf): `v_RS` as the running value | the partials are chain entries; `f⁽⁰⁾` the word |
| E1 (11 squeezes) / E2 (21 rounds, degree 3) / Eend / E3 (`κ_E`, 6 claims) / **E4 (23 rounds, degree 2: the L and M linchecks, `truthE4`; then E4 end, RS0, RS1, B′ — revision 3.13 order)**; **the rows are `nodeIRows (planOf fin)`, the templated indexed rows `evalMT` evaluates (revision 3.17, S-N1 O1); `hfit` = `plan_rowsFit`** | the element zerocheck over the M rows of `f⁽⁰⁾`: tables `[eq(r_E,·), A_M f, B_M f, C_M f]` (`truthE`, `evalM`'s matrices from `compileMux`); `Eend` carries `â_M, b̂_M, ĉ_M` at the final point `r_{E2}` | E1: `hround` form (`far_0 ∨ (¬ EHolds ∧ …)`); E2: `D3` (`e2_phase`); Eend: `habs` | E1: SZ 21 with `pair_bad_le`; E2: `D3_single` | E3's squeeze (`κ_E`): `Wrong` (`batch_bad_le` at 3, `2·2^128`); then B′ | reads `f⁽⁰⁾`'s M region |
| B′ (squeeze `κ′`) | `v* = v_RS + Σ_{k<9} κ′^{k+2} pub_k` (`truthB′`: the true `v_RS` and the 9 public cells' true values `f[cell_k]`; `pfCells`, INT-2) | `Wrong`: some term wrong `∧` the batched value equals the truth | `hsingle`: `batch_pow_bad_le` at degree 10 (`10/2^128`) | `habs` at P1.0's first absorb: `c₀^{P1.0} ≠ ⟨W, f⁽⁰⁾⟩` | the public cells are word entries |
| P1.i (`ℓᵢ` K rounds, degree 2) | the fold sumcheck of `⟨W_i, f⁽ⁱ⁾⟩` over level `i`'s row variables; tables `[W_i, f⁽ⁱ⁾]` (K); truth: `¬ far_i → c_{P1.i} = Σ_x W_i(z,x) f⁽ⁱ⁾(x)` after the folds (`truthP1 i`); **the fold rounds also carry the proximity doom**: `far_i ∧ the fold is e_i-close` (`fold_preserves` fails only on `lineBad`) | `Rej ∨ Wrong2 ∨ (far_i-doom: the round's challenge `z ∈ round_bad_cover`)` | `round_escape_le` (K: `card_chK_fiber`, `N = 2`) **plus `round_bad_cover`** (`2^(ℓᵢ−r) C_mca`): `N = 2 + 2^(ℓᵢ−r)·C_mca ≤ 2^66` | `habs` at `C.i`'s absorb (the next cap or the final message): the committed next level | `wordOf … i` under `capᵢ` (absorbed at `C.(i−1)`, before this phase) |
| C.i (absorb `capᵢ₊₁` / final) | the level-`(i+1)` word becomes readable; truth: `¬ far_{i+1} → f⁽ⁱ⁺¹⁾ = fold_z(f⁽ⁱ⁾)`'s message (`truthC i`) | `habs`: `far_{i+1} ∨ f⁽ⁱ⁺¹⁾ ≠ fold(f⁽ⁱ⁾)` | — | P2.i's first squeeze | `wordOf … (i+1)` under `capᵢ₊₁`: `colL_prefix` (the cap is absorbed here; its tree's nodes must precede: the window hit) |
| P2.i (`sq_i` squeezes, `t_i` indices) | the queried positions `posAt`; truth: the consistency set `A_c := {j : fold_z(column_j) = Enc(f⁽ⁱ⁺¹⁾)[j]}` (`truthP2 i`); doomed iff `(far_i ∨ f⁽ⁱ⁺¹⁾ ≠ fold(f⁽ⁱ⁾)) ∧ every queried index ∈ A_c` | `hround` form: all `t_i` indices land in `A_c`, `|A_c| ≤ n_i − e_i − 1` | `hround`: **`positions_bad_le`** `(1 − e_i/n_i)^{t_i}` with **`card_idx_fiber`** over `posAt` (`per` indices per answer) | the column and Merkle-node queries (asks; no doom change: `habs` for queries, their answers are `Bad`-charged hits), then P3.i's first squeeze | the columns read at the queried positions equal `wordOf`'s (`cap_binding`: `openPath` vs `colL`) |
| P3.i (5 squeezes, `κ_c`) | the batched claim `v_{i+1} = v_i + Σ_j eq(κ_c, bits₉(j)) fold_j`, weight `W_{i+1} = W_i-folded + Σ_j eq(κ_c,j) G_j` (`novelX_tensor`; `truthP3 i`) | `Wrong`: some `fold_j ≠ Enc(f⁽ⁱ⁺¹⁾)[j]` (as computed from the chain's columns) `∧` the batched value equals the truth | `hround`: SZ on the 9-variable multilinear (`9/2^128`), `pair_bad_le`, `card_chF2_fiber` | `habs` at P1.(i+1)'s first absorb (`i < 4`) / Pf's (`i = 4`, with `Enc₄(final)[j]` computed from the final message at `C.4`) | as P2.i |
| Pf (7 K rounds, degree 2) | **Pf starts from `c1 4`** (S-G2's level-4 tail, revision 3.15): tables `[wPf = the zero-padded `wFold 4` (levels 0–3's folded weights incl. `rsWeight`, the cells, the tensor weights), final]` over 7 variables; truth `c₀^{Pf} = c1 4` and the final value `Ŵ(ρ)·final̂(ρ)` (`truthPf`; `P30`: zero-padded); level 4 itself is checked directly (`y_q = Enc₄(final)[p_q]`, P3.4's doom `msD (DP2 4) (finP2 4) …`) | `¬ truthP3 4 ∨ D2` (`Rej ∨ Wrong2`) | `round_escape_le` (K), `N = 2`; the error rows can only go down | the chain ends: `finPf`'s assert; the accepted run on a non-doomed chain gives `ligerito_final`'s hypotheses | the final message is a chain entry (`C.4`) |

**What `final` then gets** (S-G2): on an accepted chain of a non-bad log with no escape, by
induction from Pf upwards every `far_i` is false and every claim is true, so `f⁽⁰⁾` is the decoded
word and `z` satisfies Z's identity, the links, Lr and E (`ligerito_final`, then `leaf_sound` /
`node_sound`). **Budget**: the truths and their stability lemmas ≈ 900 lines (`FRSoundnessTruths`,
S-G1c), the composed `D` and its `StepObl` ≈ 1,200 (`FRSoundnessStepC`).

### A.11 Replay templates (S-E2 F-6; revision 3.11)

`compile` emits rows for the arithmetic ops only (68,795 rows, 114,378 cells per slot, measured);
every **structured op** of the replayed child verifier is an import whose value must be
**constrained by a template** of rows in M, or be a value already bound elsewhere. Without the
templates `node_sound` would rest on hypotheses `final` cannot discharge. Conventions: a template
`X` is emitted for every instance `inst` of the op at rows `tplBase_X + inst·2^{a_X} + j` (`a_X` =
`⌈log₂ rows_X⌉`), its own cells at `cellBase_X + inst·2^{b_X} + k`; "import" cells are read, not
constrained here: **trace cells** (bound by the digest chain: the H message slots), **L cells**
(bits, bound by `lRows`), or **another template's outputs**. A K product is 3 F rows (Karatsuba);
a K×F product 2. Entry classes for the verifier's `evalM`/`evalMK`/`evalL` (§4.4): **local** —
columns inside the instance: `Σ_{inst} eq(τ_hi, inst) eq(σ_hi, inst) · Â_tpl(τ_lo, σ_lo)` =
`eqInner(prefix) · Â_tpl`, `O(|tpl|)` once + `O(log)`; **shared** — a column at a fixed address for
every instance (a table another op produced): `(Σ_{inst} eq(τ_hi, inst)) · eq(τ_lo, j) · eq(σ, c)`,
`O(|tpl|)`; **irregular** — a trace or L cell: one product per entry from the eq tables over
blocks and slots (`irregular_mle`).

| Op | Template rows (constrained) | Imports | Rows / instance; instances per slot | Entry classes | MLE cost (per slot) |
|---|---|---|---|---|---|
| `eqTableK r → AK 2^v` | binary tree `tab[2i] = tab[i]·(1 − r_b)`, `tab[2i+1] = tab[i]·r_b` (K) | `r` (challenges: trace cells) | `6(2^v − 1)`; 5 (one per level) | local (shift-structured) | 738 |
| `dotKF col w → K` (a column fold) | `p_b = w_b · col_b` (K×F, 2 rows), `out = Σ_b p_b` (linear) | `w_b` shared (`eqTableK`), `col_b` irregular (trace) | `2·rows_i`; `t_i` per level | shared + **irregular** (`rows_i` per instance) | 55,712 rows; 27,856 irregular entries |
| `tensorW j r → K` | `ŵ_v := Σ_b j_b · Ŵ_v(x^b)` (linear in the position bit-elements: `Ŵ_v` is GF(2)-linear), then `Π_v (1 + r_v·(1 + ŵ_v))`… as `(1 − r_v + r_v ŵ_v)` products (K) | `j_b` (L bit-elements of the index, aligned per index), `r` | `3·log k_i`; `t_i` per level | local + L cells (aligned stride 32 per index: shared form) | 37,335 |
| `rowW λ r′_hi → AF 2^14` | the 64 Lagrange values `L_σ(λ)` (shared with `lagrangeS`) ⊗ `eq(r′_hi,·)` tree (255) → `2^14` products | `λ`, `r′_hi` | 16,384; 1 | local | 16 k (in `walks`) |
| `maskRows v rowW → AF 2^14` | `rowW′[k] = rowW[k] · (Σ_{kind ∌ k} v_kind)` (the mask is a public 0/1 form of the `v_kind`) | `v_kind` (trace cells) | 16,384; 1 | shared | 16 k |
| `walkAB rowW′ colW → F × F` (revision 3.15) | **the gadget DAG materialised**: ≈ 6·10⁴ XOR linear rows and 30,851 product rows (`p_g = rowW′[g]·form_g`), ≈ 90,851 rows per slot, as a template of the G gadget (80 instances, one stride) with round-regular state positions and the `Wire` matrix (320 word runs + 160 message reads) | `rowW′`, `colW` (own templates) | ≈ 90,851; 1 | **closed form `D̂ = Ĝ₀(τ_lo, σ_lo)` × instance sum + `Wire` terms** (≈ 13 k products); `A₀`/`B₀` (nnz 51.7 M / 35.7 M) never appear as rows | 1.5 ms |
| `lagrangeS vals λ pe → F×F` | barycentric: `inv_i = (λ − node_i)^{-1}` (3 rows each), `Z(λ) = Π(λ − node_i)`, `L_i = w_i·Z·inv_i`, `P* = Σ vals_i L_i` for the 64 nodes of `Λ` and the 127 of `S ∪ Λ₀…₆₂` (`P^{ab}|_S` from `P^z|_S + pe`) | `vals` (127 trace cells), `pe` (`targetS`), `λ` | ≈ 1,400; 1 | local + irregular (127) | 1.4 k |
| `targetS r → AF 64` (node: `targetSNode`) | per kind and interval the dyadic range sums of `eq(r,·)`, the `stream` counter's shifted bit forms, the single last blocks, `w43`'s 399-term table (A.8) | `r` | ≈ 16,000; 1 (revision 3.14: sized from `targetSNodeI`'s measured 2.0 ms) | local | 16 k |
| `eqZ λ ρ₁ → AF 128` | `L_lo(λ) · eq(ρ₁, bit 6)` | the 64 Lagrange values (shared) | 128; 1 | shared | 128 |
| the `free` term `(1 + α)·v_free·⟨rowW, eq(r_k,·)⟩` (node; R-V-M2) | `eqPt` on 8 coordinates, a 64-term sum of `L_s(λ)·eq(r_k[0..5], s)`, 2 products | `λ`'s Lagrange values (shared), `r_k`, `r′_hi`, `v_free`, `α` | ≈ 80; 1 | local | 0.1 k |
| `evalL(r_Lr, r′)` replay (node; revision 3.17) | the closed form over A.7's strided L regions (the signature, digit, selector, position-bit and kind-selector regions at power-of-two strides; the `one` cell): per region the `eq` range products | `r_Lr`, `r′` (trace cells) | ≈ 10,000; 1 (≈ 40,000 if `evalLT`'s 64-row chunks are replayed instead) | local | 1 ms |
| the WOTS mux rows (§4.2; S-N1 O2b) | selector–digit rows 266, `a_{i,s}` mux 1,596, ends `e_i` 532, path `l_t`/`r_t` 128, digits → `h_out` 266: the compiled `wots` rows of S-E2's construction, regular per chain/step | L bits (digits, selectors, index bits), H cells (`h_out`, `ots`, `sib`), `WM` outputs | 2,788; 1 | local (chain stride 3, path stride 2) | 0.3 ms |
| `shiftEq τ r`, `eqPt`, `kindInd r′` | `eq`/`shift` closed forms: `O(m)` products | challenges | ≤ 60 each | local | 0.5 k |
| `slotW θ pos r → F` | `eq(θ,σ)` tree (255), `eq(cube(pos σ), r)` as 9 products per `σ` (public bits), 256 products, the sum | `θ`, `r` | ≈ 2,800; 3 slot maps | local | 8.4 k |
| `linkWAll (τ‖θ) (r_blk‖r_pos) → AF 8` (node) | the four eq tables, per family the `n_f`-term source and mirror sums, `slotW` range forms | `τ`, `θ`, `r_blk`, `r_pos` | ≈ 15,000 in all; 1 (revision 3.14, S-CN §7: ≈ `6 n_f + 24 len_f` per family) | local | 15 k |
| `shiftTarget τ θ bnd → F` | `eq(τ, 0)·⟨slotW_in, bnd_s⟩ + eq(τ, n−1)·⟨slotW_out, bnd_h⟩` (node: `h0` constants) | `slotW` outputs, `bnd` (trace: `hdr`/`stmt` cells) | ≈ 100; 1 | shared | 0.1 k |
| `rsWeight`'s claim-2 kind factor (node; revision 3.16) | per Frobenius stage `k`: the per-bit factors `1 + ρ_b + q_{k,b}` (`q_k = p_blk^{2^k}`), the dyadic range sums over the ≈ 22 kind pattern intervals, `β`'s Frobenius chains (7 × 127 squarings) | `r″`, `p`, `β`, `ρ` | ≈ 68,500; 1 | local (regular: products of challenge coordinates and constants) | 68 k |
| `phiRS r″ a → F` | 127 squarings (`a² = c`: 1 row each) + 7 products (the stages) | `a` (RS0 partials: trace cells), `r″` | 134; 512 | local | 68.6 k |
| `rsWeight r″ pts κ ρ → K` | `c_k(r″)` (128 products from the stage coefficients); per claim: `r_v^{2^k}` by 127 squarings per coordinate (23 × 127), `eq(r^{2^k}, ρ) = Π_v (1 + ρ_v + r_v^{2^k})` (22 K products per `k`), `Σ_k c_k · (…)` | `r″`, the 4 outer points (trace cells / earlier outputs), `κ`, `ρ` | ≈ 11,400 per claim; 4 | local | 45.6 k |
| the child's `evalM(r_{E2}, r′)` replay `R` (`'N'` child only, gated by `s_N`; **revision 3.15: §4.4's layout, S-E9's measured classes, slot-symmetric**) | eq trees and prefix tables 48,400; the keys' u/v, loc/one and `U` rows 29,623; the child slot's `β̃` (3 per distinct cell) 61,530, `α̃` 18,507, sparse-row companions 55,065, shared forms 20,112, own inputs 11,116, instance assembly 27,142; closed forms 8,300; outputs 1,000; **the child's walk rows' `D̂` 13,000** | `r_{E2}`, `r′` (trace cells), the child's layout constants | **293,795; 1** (≈ 164 k with the sparse-skeleton templating and the instance AP layout) | eq trees `O(log²)`; u-rows `= Ĉ(τ_lo, σ_lo)` shared with the child's instances of `C`; `D̂` closed; v-rows/sums `O(log)` | ≈ 7 ms |
| `piField/piElem/piDigest`, `askCol`/`askNode`/`askAbsorb` imports, `idx`, `bitOf`, `selectHalf`, Merkle steps, folds' operands | **no template**: trace cells (bound by the digest chain and `cap_binding`), L bit-elements (`lRows`), or arithmetic already in the skeleton | — | — | irregular where read | in the skeleton's count |
| `kindSel`, `assertOneHot`, `assertEq` (gated), `const`, `input` (`vk`, `c`: the public cells) | public constants or the skeleton's rows | — | — | — | — |

**Totals per slot** (`sizes.py`, A.11 model; **superseded by §10 changes 17**: S-E3 measured the skeleton at 120,597 rows and 1.23 M entries per node, not 68,795 rows / 140 k entries, and the evaluation plan below is replaced by the F-7 redesign): skeleton 68,795 + eqTableK 738 + dotKF 55,712 +
tensorW 37,335 + walks 81,920 + lagrangeS 1,400 + targetS 10,000 + slotW 8,400 + linkW 20,000 +
small 628 + phiRS 68,608 + rsWeight 45,604 + evalM/evalL replay 464,802 = **863,942 rows per slot,
1,727,884 = `2^20.72` per node** (`N_M = 2^21`: **1.21×**); M blocks 13,500; **node blocks 59,585 of
65,536 (1.10×)**. It fits `m = 30`. **Smallest cut if `nodeLayout`'s `decide` fails**: restore the
E2 lincheck (23 F rounds, prover +0.14 s per `m = 30` request, link ≈ 2.9 s) so that the child's
`evalM` is replayed at an **F** point (1 row per product instead of 3): per node 1,320,204 =
`2^20.33` (1.59×). Second cut: share the two slots' `eq(ρ_blk, ·)` tables (`ρ` is one point): −196 k
rows per node.

**Soundness lemma shape** (`FRVIRTemplates`, L-circ): for each structured op `X` with
specification `X_S` (`FRVerifierImpl`'s `…S`), `tplX_sound : HoldsRows (tplX base inst) f →
outCells_X f = X_S (inCells_X f)`, and `tplX_mle : Σ_{(r,c) ∈ nnz(tplX)} eq(τ,r) eq(σ,c) =
closedForm_X τ σ` (the local/shared/irregular factorisations, with `walk_eq_sum` for the walks and
`irregular_mle` for the trace cells). `compile_sound` is extended to `compileT_sound`: the import
hypotheses of structured ops are discharged by the `tplX_sound` of their templates, so
`node_sound`'s remaining import hypotheses are exactly the **trace cells** (fixed by the digest
chains and `cap_binding`/`wordOf`), the **L bits** (`lRows_sound`) and the **public inputs**.
`evalM_eq` becomes the sum of the templates' `tplX_mle` plus the skeleton's `sparse_eq` part.

**`T_V` estimate**: the verifier's `evalM`/`evalMK` over the templates: the two block/slot eq
tables in K (shared by the slots, `3·(2^16 + 2^14)` F), `2 × 2 × 74,521` irregular K×F products,
the templates' closed forms (`≈ 2 × 20 k` K): ≈ 6.6·10^5 F-products ≈ **40 ms on the VM**, on top of
S-F2's measured 183 ms (N30, with the sparse `evalRows` for the toy and without the templates):
**≈ 225 ms VM ≈ 175 ms on the runner against 205.9 ms** (1.17×; `finPf` and the real `evalL` add
≈ 10 ms). The skeleton's own rows (68.8 k per slot) are evaluated by `sparse_eq` once per node
(≈ 140 k entries, ≈ 10 ms) unless they too are grouped by op into templates (S-E3: recommended).

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

### Stage-review changes 2 (revision 3.4): S-C review, S-H1, P2 §6

| Item | Change |
|---|---|
| S-C-M1 | **Fixed**: the lincheck runs on the per-kind folded columns `zfold_kind` (one pass; the kinds partition the used blocks); the prover claims the ≤ 7 `v_kind`; the verifier's one walk uses `rowW′[k] = rowW[k]·Σ_{kind ∌ k} v_kind`; **the `v_kind` are batched by one squeeze `β` into one weighted claim** `⟨W_β, z⟩` with the public weight `eq(r′_blk,t)·Σ_kind β^kind Ind_kind(t)·eq(r_k,j)` before ring switching (an equivalent of the reviewer's fix: `J_z` stays 4, RS0/MBP unchanged, RS1 stays `10/2^128`; new row L3 `6/2^128`). Lean: `lin_trueSum_kinds`, `lin_final_kinds`, the walk-adjustment identity, `kindFoldWeight` (A.8). Prover cost on the `m = 30` path: unchanged (one fold pass, one weight pass; +1 squeeze, +112 B absorb). |
| S-C-M2 | **Fixed**: Z3's summand `w·(ab + z) + W_E`, `W_E = eq(r,·)·Sel·E`; the exact `Ŵ_E(λ, r′)` with its position factor `eq(r_hi,hi)·eq(r′_hi,hi)·L_lo(λ)`; Z2's `gen` form (`P^z`, `P^{ab}` on `Λ`; `P^{ab}|_S = P^z|_S + P^e|_S`) with the bound 127 (`z2_pair_bad_le`) (§2.3 step 2, A.8 `targetMLE`). |
| S-C-m1 | **Fixed**: the unaligned `d` slot's collapse weight is summed directly (≈ 3.6 k products; A.8 `slotW`); 10 collapse coordinates over positions `< 1024`. |
| S-H1 | §6.3: 57 steps per F product (kernel): extractor `2^46.52 + 2^11 t`, **fuel margin 1.97×, `B` 2.79×**; §6.4 is the delivered DSL (`loopK`/`loopT`, the cost formula, `regs = 256` with cells 0–3 constant, scratch 5–38, user registers 64–255, `toProg`, `run_toProg`). |
| P2 §6 (E2 batching) | **Adopted as sound**: E2's claim is `⟨W_E2, f⟩` with the public multilinear weight `(Ã_M + κ_E B̃_M + κ_E² C̃_M)(r_E, ·)`, so it joins the Ligerito weight at B′ like ring switching's claims and `Ŵ_E2(ρ) = evalM(r_E, ρ)` is the evaluation the verifier does anyway; the E2 lincheck (23 rounds) is removed (§2.3 step 7, §5.2 E rows, A.3 row 9, A.4). Link 2.80 → 2.66 s (P2, measured). |

**Margins after revision 3.4** (`sizes.txt`): `piSize` 755,568 (1.39×); items 8,852 of 10,240
(1.16×); hashed stream 1,435,888 B = 22,436 compressions per slot; node 54,218 of 65,536 blocks
(1.21×); M rows 1,050,900 = `2^20.00` of `2^21` (2.00×); extractor `2^46.52` (fuel 1.97×, `B`
2.79×); **error maximum unchanged `2^-120.36 + 2^-144 ≤ εR`** (new row L3 `2^-125.4`; RS1
`10/2^128`); verifier ≈ 1.2·10^5 (leaf) / 3.9·10^5 (node) products; stream link 2.66 s against ≈
3.1 s (P2, measured).

**Interface changes of revision 3.4:**

| Track | Modules | Change |
|---|---|---|
| S-0 | `FRVIR`, `FRVIRSpec`, `FRTranscriptDefs`, `FRFormat` | the item sequence: L3 (absorb of 7 `v_kind`, squeeze `β`) added, E4 removed (A.4; 429 FS items); `piSize = 755,568` (A.3); `gen`: Z2's message form, Z3's final value with `Ŵ_E`'s position factor, the lincheck's per-kind claims and `β` batching, `slotW` summed directly, no E2 lincheck, `evalM(r_E, ρ)` as the E weight at the final point; ops `kindFoldWeight`, `slotW`, `targetMLE r λ r′` (A.8). |
| S-C (fix pass) | `FRSpartan`, `FRSkip`, `FRShift`, `FRRingSwitch` | `FRSpartan`: `bzExpr = w·(ab + z) + W_E` over five tables, `bz_trueSum`/`bz_final`/`bz_triple_wrong` restated, `targetMLE_eq`; the lincheck on per-kind folded columns (`lin_trueSum_kinds`, `lin_final_kinds`, the walk-adjustment identity) and the `β` batching lemma (`batch_bad_le` at 7 claims); `FRSkip`: `z2_pair_bad_le` (127); `FRShift`: `slotW_mle` (generic slot map, direct sum) beside `slotW_mle_aligned`, `s = 10`; `FRRingSwitch`: the weighted-claim form takes `W_β`'s public weight (a tensor prefix sum over intervals). |
| P2 | prover | the per-kind lincheck fold and the 7 `v_kind` messages, the `β` batching into the RS weight; Z2's message form; E2 batched into the Ligerito weight (as already prototyped, now normative); the item sequence and `piSize` above. |

### Stage-review changes 3 (revision 3.5): S-0 review

| Item | Change |
|---|---|
| S-0-M1 | **Appendix A.9**: the typed `Finals` structure (`FRVIRFinals`, imports `FRVIR`), one field per phase with the exact relation, the free initial claim it binds, the op shape and the owner of its semantic lemma: S-0 fix pass (Z, Lc, Sh, Lr), S-F (RS, E, B′), S-G (P i, Pf); budget 1,200 lines (§7). `J_z = 5` (Sh contributes two slot claims): RS0 `5 × 128` partials, 5 MBP runs, RS1 `11/2^128`. The dumps are re-done with `gen fin`. |
| S-0-M2 | **WOTS/key-leaf/path wiring through the shift argument** (§4.2, A.6): consecutive block layouts; the selector mux and the path's `l/r` choice computed on the aligned side into the mirror sub-region `WM` (10 blocks per slot); ≤ 8 link families (unaligned message field ↔ mirror cell, arbitrary slot map + re-based stride, `linkW` in A.8) batched into the one Sh sumcheck by `κ_s` (S1 `+7/2^128`; S2 unchanged; `qV` unchanged). The digits `d_i` as 256 L bit-elements tied to the chain's last output by two linear rows. |
| S-0-m1 | **Decided**: `windows` by stream offset (`≡ 0 mod 16` in `0x54 ‖ traceBytes`), so the seed's windows are in play; count unchanged (A.2). |
| S-0-m3 | **Fixed**: the header (revision 3.5), A.4's "429 FS items", A.2's final-message sentence; the coordinate layouts of S1/RS1/Lr1/E1 (deviation 7) and S-0's structural ops (deviation 1) recorded in A.2/A.8; "≤ 7 `v_kind`" reads "8 entries in `blockKinds` order, unused kinds `0`". |
| S-0-m7 | **Fixed**: the finals' lemmas budgeted (1,200 lines, by owner); FR-R10's check stays per shape after the queries shape. |

**Margins after revision 3.5** (`sizes.txt`): `piSize` 757,616 (1.38×); items 8,852 of 10,240
(1.16×); hashed stream 22,468 compressions per slot; node 54,393 of 65,536 blocks (1.20×); M rows
1,062,628 = `2^20.02` of `2^21` (1.97×); extractor `2^46.52` (fuel 1.97×, `B` 2.79×); **error
maximum unchanged `2^-120.36 + 2^-144 ≤ εR`** (S1 `33/2^128`, RS1 `11/2^128`); verifier ≈
1.2·10^5 (leaf) / 3.9·10^5 (node) products.

**Interface changes of revision 3.5:**

| Track | Change |
|---|---|
| S-0 fix pass | `FRVIRFinals` with the typed `Finals` (A.9) and `exec_finZ/Lc/Sh/Lr`; `J_z = 5` in RS0/RS1 and `mbp`; `windows` by stream offset; the `linkW` op and the ≤ 8 link families in Sh (`gen`'s Sh phase gains their `slotW` sums and the `κ_s` powers); `piSize = 757,616`; the dumps with `gen fin`. |
| S-E2 | `FRWots`: the consecutive WOTS/key-leaf/path layout, the `WM` mirror cells and their mux rows (M), the digits' bit-elements and linear rows; `FRNodeLayout`: `WM` (10 blocks per slot), the link families' intervals; `node_sound` takes `ShHolds` with the link families; the M-row count from `gen fin`. |
| P2 | the node witness: `WM` mirror cells, consecutive WOTS layout, the link families in the shift sumcheck (their slot maps and `κ_s` powers), `J_z = 5` partials and MBP state vectors, the finals' values (`v_kind`, `â_L …`, `fold_j`, `v*`) in the transcript as A.9 lists; the KAT against the re-dumped `ops-*.txt`. |
| S-F / S-G | `exec_finRS/E/B′` (S-F) and `exec_finP/Pf` (S-G) against A.9's relations; `final` discharges the WOTS links from the Sh sumcheck's link families. |

### Stage-review changes 4 (revision 3.6): S-E2 RESULT §5

| Item | Change |
|---|---|
| F-1 (major) | the 8 `stmt` equalities are **gated**: A's four by `s_L + s_P`, B1's and B2's by `s_N` (product rows); `hashStmt_sound` restated with the gates as hypotheses and kind-conditional conclusions (§4.2). |
| F-2 (major) | the chain end is `e_i = sel_{i,3}·h_out(w_{i,3}) + (1 − sel_{i,3})·ots_i`; three selectors per chain `[d<1], [d<2], [d<3]` tied to the digit bits by 2 product rows per chain (266 per slot) (§4.2, §4.3). |
| F-3 (minor) | §4.3's categories now sum: 531,588 per slot (incl. the mux 2,600, selector rows 266, gated equalities 8), 1,063,176 per node. |
| F-4 (minor) | M's `one` cell pinned by a point claim `f[Mbase] = 1` at B′; `J_f ≤ 21`, B′ row `20/2^128` (§4.3, §5.2). |
| Op tracking | `eqPt`, `rowW`, `shiftEq`, `linkW` are **imports**: no row; their cell values are hypotheses of `compile_sound`, discharged in `final` (S-G) by the facts that fix those cells (A.8). |

**Margins** (`sizes.txt`): node 54,398 of 65,536 blocks (1.20×); M rows 1,063,176 = `2^20.02` of
`2^21` (1.97×); `piSize`, items, extractor and the error maximum unchanged (B′ `20/2^128`).

**Interface changes:** **S-E2** — gated `stmt` rows, the selector–digit rows, `e_i`'s mux, the
`f[Mbase] = 1` claim in `PubCells`, `hashStmt_sound`'s new statement; **S-0** — `gen`'s B′ adds the
`one`-cell point weight (`J_f ≤ 21`), the four cell-reading ops documented as imports; **P2** — the
node witness: gated equalities (no change to the cells), the 266 selector rows, `e_i` by the digit-3
selector, the `one` cell at `f[Mbase]`.

### Stage-review changes 5 (revision 3.7): S-0 fix pass §6, S-E2 F-3′

| Item | Change |
|---|---|
| finLr / finE sources | **"Lr end" and "E end" absorbs added** (48 B each: `â_L ‖ b̂_L ‖ ĉ_L` after Lr2, `â_M ‖ b̂_M ‖ ĉ_M` after E2), like `Zend` (A.3 rows 7′, 9′; A.4 rows 12′, 18′); nothing else carried them. `piSize = 757,712`, items 8,854 (`qV` margin 1.16×), 431 FS items. |
| Finals' placement | **Ratified**: the finals run after the whole skeleton in the order `finRS, finZ, finLc, finSh, finLr, finE, finB′, finP 0…4, finPf`; they ask nothing, the transcript is unchanged, and no challenge depends on a final (the flag) (A.9). |
| `linkW`'s point | **Fixed**: `linkW τ fam r_blk` at the Sh sumcheck's block point (`AF 18`), powers from `κ_s²` (A.8); the RS side sees only the `Out`/`In` slot claims. |
| `rowW`, `shiftEq` | recorded in A.8 as ops with S-C's specs `rowW_eq`, `shiftEq_eq`. |
| `nMax` | **Ratified**: `domBits = 20` in `FRTranscriptDefs`, `= FRRS.logNMax` by `rfl`; `FRRS` off the serial path (10,220 lines, ≈ 307 s); `eqBits_eq_eq` in `FRSoundnessLigerito` (A.2). |
| F-3′ | **Fixed**: the `stmt` equalities counted once, `evalM` by its formula (210,250 with 431 FS items), the categories sum to 531,618 per slot (§4.3). |

**Margins** (`sizes.txt`): `piSize` 757,712 (1.38×); items 8,854 of 10,240 (1.16×); hashed stream
22,472 compressions per slot; node 54,406 of 65,536 blocks (1.20×); M rows 1,063,236 = `2^20.02`
of `2^21` (1.97×); extractor and the error maximum unchanged.

**Interface changes:** **S-0** — two absorbs in `items`/`piSize`/`reassemble` (A.3/A.4), `finLr`
and `finE` read them (not `zhat[6…8]`), the finals' order after the skeleton, `linkW` at the Sh
point, `rowW`/`shiftEq` as ops, `domBits` as ratified; **S-E2** — `nodeLayout`'s imports count the
two new items (74,461 per slot), the row table of §4.3; **S-F** — `finE` reads the E-end absorb,
`finB′` unchanged; **P2** — the prover sends `â_L ‖ b̂_L ‖ ĉ_L` after Lr2 and `â_M ‖ b̂_M ‖ ĉ_M` after
E2, `piSize = 757,712`, the dumps re-matched.

### Stage-review changes 6 (revision 3.8): P2 RESULT §7.5, §8

| Item | Change |
|---|---|
| Skip-c restored (P2 §8) | **Z3 runs on `eq(r,·)·a_λ·b_λ` only** (no `z`, no `W_E` table); the c-claim is the quirky point claim `ẑ(r, λ) = P^z*(λ)`, RS claim 1 (the revision-3.1 route). To make this sound without `Sel` in the RS weight, **`Sel ≡ 1`**: the non-hash blocks (M, L, `WM`, spares) get the kind **`free`** (rows `(var k, var k)`, `E = 0`, satisfied by every Boolean `z`; A.6; corrected in 3.8.1), so `ŵ = eq(r,·)` and `finZ` is `eq(r,r′)·â·b̂ = c_Z`. Z2's message: `P^z|_Λ` (64) then `P^{ab}|_{Λ₀…₆₂}` (63); `P^{ab}|_S` rebuilt as `P^z|_S + P^e|_S` (`targetS`); Z2 row **`126/2^128`** (case split on the fixed message). Prover: −0.26 s per `m = 30` request and −1.0 s per `m = 32` leaf (P2's measurement of the regression), +≈ 0.07 s for the full-cube zerocheck of a node: **link ≈ 2.75–2.85 s against ≈ 3.1 s; tree ≈ 450 s** (**estimate** from P2 §6/§8). |
| S-C re-proves | `FRSpartan`: `bzExpr = w·a·b` over three tables (back from the five-table 3.4 form), `bz_trueSum = P^{ab}(λ)`, `bz_final = eq(r,r′)·â·b̂`, `bz_triple_wrong` adapted; the lincheck's per-kind claims include the `free` kind (`M_free = (1 + α)·rowW`, no walk; 3.8.1), `β` batching at 9 claims (`8/2^128`); `FRSkip`: `skip_pair_bad_le` (126) for `(P^{ab}*, P^z*)` reconstructed from 127 values and `P^e`; `FRPubTarget`: `targetS_eq` (`P^e` on `S`) replaces `targetMLE_eq`; `selWeight_eq` is unused. `FRRingSwitch`: unchanged (the quirky point claim is its 3.1 case). |
| Prose vs dump (P2 §7.5) | **1** Z2: as above; `lagrangeS` gains the `pe` operand and two outputs (S-0, sound). **2** `κ_c`: the dump's one squeeze is **unsound against `εR`** (powers give `tᵢ/2^128 = 2^-119.8`); `P3.i` is **5 squeezes** (9 coordinates, `eq(κ_c, bits₉(j))`), A.4 corrected, items 8,874 (S-0 changes the Lean). **3** S2 dummies at the phase's end: ratified. **4** `θ` 10 coordinates, `σ < 256` as a 10-bit index: ratified (S-C's `slotW` reads it so). **5** Sh is **one** RS claim (`w_out + w_in` at one point): `J_z = 4`, RS0 `4 × 128`, 4 MBP runs, RS1 `10/2^128`, `piSize` −2,048 (A.9 `finSh`). **6** a leaf's `J_z = 3`, fourth partials zero: ratified. **7** `linkW = 0` for leaf kinds: ratified. **8** Pf for `P30`: the weight zero-padded, `Ŵ(s, ρ₀…₄)·(1+ρ₅)(1+ρ₆)`: ratified (S-G). **9** §1.2 counts fixed (447 FS items, 8,874). **10** L3's 7 elements / `maskRows`' 8 (now 9 with `free`): the leaf's `v` at entry 0, the node's at 1–8. **11** pending finals: S-F/S-G as A.9. |

**Margins** (`sizes.txt`): `piSize` 755,680 (1.39×); items 8,874 of 10,240 (1.15×); hashed stream
22,465 compressions per slot; node 54,590 of 65,536 blocks (1.20×); M rows 1,089,908 = `2^20.06`
of `2^21` (1.92×); extractor unchanged; **error maximum unchanged `2^-120.36 + 2^-144 ≤ εR`** (Z2
`2^-121.0`, L3 `2^-125`, RS1 `2^-124.7`, P3 `2^-124.8`).

**Interface changes:** **S-C** — as "S-C re-proves" above. **S-0** — `gen`: Z2's message order
and `lagrangeS vals λ pe`, `targetS`, Z3 on two tables with `finZ = eq(r,r′) â b̂`, the Z claim at
`(r, λ)` to RS, `J_z = 4`, P3.i with 5 squeezes, the `free` kind in `kindInd`/`maskRows` (9
entries), `selWeight`/`targetMLE` removed; `items`/`piSize = 755,680`; re-dump. **S-F** — `finRS`
with 4 claims (Z's quirky claim as the first), `finE`/`finB′` unchanged. **P2** — the P1 zerocheck
(skip-c) with the full cube for nodes (free blocks: `a = z`, `b = 1`), Z2's message, `κ_c` from 5
squeezes with `eq`-structured coefficients, one Sh claim, `J_z = 4`, `piSize = 755,680`.

### Stage-review changes 7 (revision 3.8.1)

| Finding | Change |
|---|---|
| BP-C-R5-M1 (crypto round 5) | The `free` kind's rows are `(var k, var k)` with `E = 0`, so `A₀^{free} = B₀^{free} = I` and `z_k² = z_k` holds for every Boolean `z`. The 3.8 rows `(var k, one)` forced the unpinned bit 1,152 to 1, so honest nodes failed the zerocheck on about half their M blocks: a completeness failure, not a soundness one. The lincheck's free term is `(1 + α)·rowW`. P2's "`a = z, b = 1`" must become `a = b = z`. Round 5 confirmed (a) the Z2 row 126/2^128, (b) that `free` cannot be abused (kinds are public intervals), (c) Sh as one RS claim, and (d) κ_c by 5 squeezes. The error maximum is unchanged. |


### Stage-review changes 8 (revision 3.8.2, from S-0's 3.8 adoption)

| Finding | Change |
|---|---|
| `sizes.py` dropped RS1 | RS1's four squeezes were in a comment. With them back, there are 8,874 items (431 + 20 FS), as the Lean `items_length` and the dump say, and the hashed stream is 22,465 compressions per slot. Numbers updated throughout. |
| The `free` kind's `v` | L3 absorbs **8** node per-kind claims (the 7 hash kinds and `free`: 128 B), since the lincheck's `free` term `(1 + α)·rowW` needs `v_free`. β batching is over 9 entries (the leaf's `v` at 0, the node's 8 at 1–8), as in 3.8; the error row is unchanged at 8/2^128. `piSize = 755,680`. |

### Stage-review changes 9 (revision 3.9): S-F RESULT deviations 1–8

| Item | Decision |
|---|---|
| `v_RS`'s form | **`FRRingSwitch`'s `rsT`**: `T_j = Σ_i b_i Φ_{r″}(s_{j,i})`, `v_RS = Σ_j κ^j T_j`, the form `rs1_joint` proves (S-F deviation 2); A.9's `Σ_u eq(r″,u) s_u` (the paper's tensor-algebra protocol) is withdrawn, and so is the MBP: `Ŵ(ρ)` is `weightEval`'s `Σ_j κ^j Σ_k c_k eq(r_j^{2^k}, ρ)` (`rsWeight`, 128·(m−7) per claim). Cheapest sound form: it needs no new proof; its cost (`Φ` on 512 slice values ≈ 70 k products, 13 ns squarings in `V`) is inside T_V, and in the node ≈ 74 k rows per slot: **M rows 1,237,344 = `2^20.24` of `2^21` (1.69×, S-F's generator count)**, blocks 55,752 (1.18×). §2.3, §3.1, §4.3, A.8, A.9, `sizes.py` updated. |
| Public cells | **Pinned** (A.7): `pub_0 = f[Mbase] = 1`; slot 1's `vk` halves, `c₁` halves; slot 2's `vk` halves, `c₂` halves; then the six padding cells; `pub_k` at `κ′^{k+2}`; cell addresses from the seed payload (`vk` elements 0–1, `c` 2–3, stream element `1 + e`). |
| Op signatures | `rsWeight r″ pts κ ρ` (the claims' outer points; a leaf passes 3) replaces `mbp`; `phiRS`; `shiftTarget τ θ bnd` with the boundary values; `eqZ λ ρ₁`; `lagrangeS vals λ pe → F × F` and `targetS` as 3.8; `selWeight`/`targetMLE` removed everywhere (A.8). |
| `finPf` (S-G) | confirmed: the leaf's fourth weight is omitted (as in `v_RS`); the E weight's point is **E2's final point `r_{E2}`** (`finE` export 1), not E1's `r_E`; `P30`'s zero-padded weight (A.9). |
| The Z claim's `eq` factor | the quirky variables are position bits `6…13` then blocks; the pinned `ρ₁…ρ₇` are variables `0…6`; **bit 6's coordinate is `ρ₁`** (`eqZ λ ρ₁`), not Z1's first free coordinate (A.2; S-0/S-F one-line change). |
| Claim values | **Ratified**: the `α_j` are computed by the column check (`rs_column`) and bound where used (`finZ`: `α_Z = P^z*(λ)`; `finLc`: `v_β = α_Lc`; `finSh`, `finLr`); `finRS` has no `assertEq` (A.9's list changed accordingly); the other finals' asserts are unchanged. `zhat = [α_Z, α_Lc, α_Sh, α_Lr, v_RS]`; S-0's `finSh`/`finLr` read `zhat[2]`, `zhat[3]`. |

**Margins** (`sizes.txt`): node 55,752 of 65,536 blocks (1.18×); M rows 1,237,344 = `2^20.24` of
`2^21` (1.69×); `piSize` 755,680, items 8,874, extractor and the error maximum unchanged;
verifier node ≈ 4.6·10^5 products incl. ≈ 70 k `Φ` steps (mostly squarings), leaf ≈ 1.9·10^5; T_V
**estimate** ≤ 125 ms.

**Interface changes:** **S-0** — `eqZ λ ρ₁` (bit 6 = `ρ₁`), `shiftTarget` with `bnd`, `rsWeight`/`phiRS`
in the op set, `finSh`/`finLr` reading `zhat[2]`/`zhat[3]`, the public-cell order in `gen`'s B′.
**S-E2** — `PubCells` with the nine cells and six paddings in A.7's order and addresses; the M-row
model with `Φ` (+74 k per slot); `nodeLayout`'s `decide` re-run. **S-F** — `finRS` as delivered
(`rsT`), `finB′` with A.7's order, `finE`'s export `r_{E2}`; the concrete `OpImpl` once S-C's twins
exist. **S-G** — `finPf` with `rsWeight` (leaf: 3 points), `evalM(r_{E2}, ρ)`, A.7's cell order,
`P30`'s padding. **P2** — `v_RS = Σ κ^j T_j` with `Φ`, the cell order, `bnd` for the leaf's shift
target, `eqZ` with `ρ₁`.

Note (3.9): `sizes.py` carries S-0's 3.8.2 reconciliation of the item sequence (L3 absorbs 8 `v_kind`, 128 B; 451 FS items, 8,874 items, `piSize = 755,680`, 22,465 compressions per slot); the text follows the script.

### Stage-review changes 10 (orchestrator rulings on S-G part 1)

| Point | Ruling |
|---|---|
| The charging log | A chain is charged on the log before its last entry (`L.take j`), because levels 1–4 absorb their caps mid-chain. Each row proves that its doom predicate reads the same values off `L.take i` and `L` when nothing bad occurs (`colL_prefix`/`colL_append`). |
| The window hits (§5.1) | Windows count only queries of at most `queryCap` bytes (the log can hold longer oracle queries), include the entry's own query, and sit at offsets 7 + 16k and 8 + 16k. The H row is ≤ 2^-142, not 2^-144. The total `2^-120.36 + 2^-142 ≤ εR` must be kernel-checked in S-I. |
| "Flipped group" | Dropped from §5.1's `Bad`: it was never defined and no row needs it. |
| Off-chain queries | Column and Merkle-node queries carry no state and are charged only through `Bad`. |
| The stage split | S-G is split into S-G3 (`finP`, `finPf`, then a dump), S-G1 (the doom predicates and the §5.2 rows, `card_idx_fiber`, a generic `hloc_of`), and S-G2 (`ligerito_final`, `final`, `kstate`), done in that order. |

### Stage-review changes 11 (S-G3: A.9's Ligerito finals)

| Point | Change |
|---|---|
| Fold factors | At each later level's first challenge β, the fold factor is `û(β) = 1 + β(1 + u)`. Each later level's point drops its first coordinate (the coordinate-split bit). This matches the native verifier (`prover/ligerito.rs`). |
| Padding | The factor `(1 + ρ₅)(1 + ρ₆)` applies to the whole weight, for both m = 30 kinds (P30 and N30), not only P30. |
| `finPf`'s ops | A.8 gains `evalMK : AF 21 → AK 23 → K × K × K` (`evalM` at a K column point, needed for `evalM(r_E2, ρ)`); `rsWeight` is in the op set (S-0). `finPf`'s formula is the native `weight_eval` (S-G-RESULT §3). |
| `finP 4` row cost | About 60k node M rows with the current ops (estimate; the blueprint had ≈ 32k). An op giving `X_c(D[p])` at a runtime position would recover the difference; this is open for L-circ. The M-row margin stays positive either way (1.69× before). |

### Stage-review changes 12 (revision 3.10): the per-phase truths (S-G1/S-G1b)

| Item | Change |
|---|---|
| A.10 | **Appendix A.10 "Per-phase truths"**: for every FS phase (Z1–Z3/Zend, L1–L3, S1/S2, Lr1–Lr4/Lrend, RS0/RS1, E1/E2/Eend, B′, P1.i/C.i/P2.i/P3.i, Pf) the truth (tables, initial claim) in terms of `wordOf`/`FarAt`, the decoded `f⁽ⁱ⁾` and `z`, the public data and earlier challenges, naming existing Lean (`bz_trueSum`, `lin_trueSum_kinds`, `shift_sound`, `rsT`/`rsTruth`/`rs_column`, `evalM`/`evalL`, `novelX_tensor`, `D3`) or the definition to add (`truth*`, owner S-G1c); the doom form (`Rej ∨ Wrong` for asserted rounds, `D3`-style mismatch otherwise, `far_i` for the levels); the count lemma per row (`zerocheck_bad_le`/`skip_pair_bad_le`/`round_escape_le`/`batch_*_bad_le` with `card_chF_fiber`/`card_chF2_fiber`, `rs1_joint`, `round_bad_cover` + `card_chK_fiber`, `positions_bad_le` + `card_idx_fiber`); the handoff (`habs` at the next absorb or the escape at the next squeeze); and the reads `hstab` must keep stable (`wordOf` under the caps by `colL_prefix`/`cap_binding`, the window case of a cap's own absorb). |
| Composition | **Ratified**: `D L es := Rej L es ∨ D_{φ(es)} L es` (the current phase's doom, or `Rej`), handoffs as S-G1b §5.1; `rnd 0 = none`. |
| Budget | `FRSoundnessTruths` ≈ 900 lines (S-G1c), `FRSoundnessStepC` (the composed `D`, `StepObl`) ≈ 1,200 (§7). The P2 bound `(1 − eᵢ/nᵢ)^{tᵢ} ≤ deltaR` is kernel-checked in S-G1c (not deferred to S-I). |

### Stage-review changes 13 (revision 3.11): S-E2 F-6, replay templates

| Item | Change |
|---|---|
| A.11 | **Appendix A.11 "Replay templates"**: for every structured op (`eqTableK`, `dotKF`, `tensorW`, `rowW`, `maskRows`, `walkA/B`, `lagrangeS`, `targetS`, `eqZ`, `shiftEq`/`eqPt`/`kindInd`, `slotW`, `linkW`, `shiftTarget`, `kindFoldWeight`, `phiRS`, `rsWeight`, the child's `evalM`/`evalMK`/`evalL`) the template rows, imports, alignment `tplBase + inst·2^a + j`, row count and entry class (local / shared / irregular) with the verifier's MLE cost; the ops needing no template (trace cells bound by the digest chain and `cap_binding`, L bits by `lRows`, public constants); `tplX_sound`/`tplX_mle` and `compileT_sound` extending `compile_sound`; the revised count **863,942 rows per slot, 1,727,884 = `2^20.72` per node (1.21× under `N_M`), 59,585 blocks (1.10×)**: it fits `m = 30`; smallest cut: the E2 lincheck restored so the child's `evalM` replays at an F point (1,320,204 rows, 1.59×; prover +0.14 s); second: shared `eq(ρ_blk,·)` tables (−196 k). `T_V` ≈ 225 ms VM ≈ 175 ms runner (1.17×). |
| §4.3 / §4.5 / §0 | the row and block totals now cite A.11's model; `sizes.py` carries it (`A.11 row model`). |
| F-5 (S-E2 §10, minor) | A.7 fixed: the WOTS digits are **266 bit-elements** (two per base-4 digit, 133 digits incl. the checksum's), not 133; `lBitCells`' offsets move by 133 (S-E3; the L region stays far inside `N_L = 2^15` rows per slot). |


### Stage-review changes 14 (S-H2 Part 11)

| Point | Change |
|---|---|
| Extractor fuel (B-10) | `fuel_per_word` goes from 4,096 to **8,192**. Decoding level 0 needs levels 1–4 (the fold-consistency sets), and those need the fold challenges, which come from a second, query-keyed index of the log (≈ 2,374·t on top of the first sort's 2,374·t). This is still far inside `extractorBudget = 2^48 + 2^16·t`. Claim: `fuel_base 211106232532992`, `fuel_per_word 8192`. |
| Hidden disagreement (A.10, P1.i) | P1.i's doom includes `Hide_i`: a position where the word disagrees with the close codeword but whose folded difference is zero at z. Its probability is ≤ eᵢ·ℓᵢ/|K| per Schwartz–Zippel, inside P1's existing cancellation charge, and the row's bound is unchanged. With it, `final` supplies `A_c⁽ⁱ⁾ = jointAgree⁽ⁱ⁾` to the extractor. |

### Stage-review changes 15 (S-G1e)

| Point | Change |
|---|---|
| No padding cells | The hashed stream is `1,437,760 = 64·22,465` bytes, so every chain's last block is full and `Padded` holds trivially (`stream_padded`). The six "padding cells" of A.7/§4.3 do not exist (they would be trace cells), and pinning them would break completeness. They are dropped from A.7's public-cell list and from S-E2's `pubVals`/`PubCells`. The public cells are `one`, then `vk` and `c₁` halves, then `vk` and `c₂` halves. |
| `Hide` in the potential | Hide gets a separate additive potential `μ_Hide`: the indicator that Hide occurred at some P1.i, charged ≤ eᵢℓᵢ/|K| at P1.i's fold squeezes (≈ 2^-238 per query) and frozen afterwards. The total `μ = μ_doom + μ_Hide`; the per-query sum stays ≤ εR = 15/2^124, kernel-checked. `final` gets ¬Hide, hence `A_c⁽ⁱ⁾ = jointAgree⁽ⁱ⁾`, from μ < 1. The claimed ε is unchanged. |

### Stage-review changes 16 (S-H2 Part 13)

| Point | Change |
|---|---|
| `vk` in a node proof | `E` takes no `vk` (V4-6), but the extractor must rebuild the FS seed `"FRSEED0" ‖ vk ‖ c ‖ hdr` to replay a node's fold challenges. As V4-6 provides ("a design whose encoding depends on vk writes vk into π"), an **'N' proof carries `vk` in hdr bytes 16–47** (the `pub` field: leaves keep `s` there), and **`V` asserts `hdr.pub = vk` for kind N**. The node circuit inherits the check on its children, since it replays the child's `V`. The prover writes the field. |
| The challenge replay | One forward pass over the log (`chainIR`, ≈ 184 steps per word), proved equal to `runLog`'s first-match chain on a log with no state hit (`scanC_fm`), instead of a second sort (§6.2). |
| The query link | S-0 proves that the extractor's FS query list `fsQ vk c π` is `gen`'s FS query sequence. S-G2 composes it with `runLog`, which also gives `capPi π e = capDig es 0 e`, so that is no longer a separate hypothesis. |

### Stage-review changes 17 (revision 3.12): S-E3 F-7, the verifier's time

**Measured (S-E3, VM):** compiled `V` on an N30 proof 166.3 ms without `evalM`/`evalMK`; the
templated `evalM` 1.13 s, `evalMK` 2.02 s per call; the skeleton has 120,597 rows and
**1,230,280 sparse entries per node** (the dump `logs/S-E3/nodedump/`: slot 0's skeleton 672,876
entries in 120,597 rows, 5.6 per row; the 16,060 `mulK` of `finP4`'s Horner block ≈ 298 k entries
through their long `addK` forms; the 7,552 Merkle steps 60,416 rows), evaluated at ≈ 1 µs per
boxed entry; the 1,401 template instances cost ≈ 0.4 s because the generic `tpl_mle` evaluates
`eq(σ, cell)` from scratch for each of the ≈ 60 k imports per slot. `V` calls `evalMK` once
(`finPf`) and `evalL` once (`finLr`); the F-point `evalM` is not called by a node's `V`. Budget:
the VM-equivalent cap is ≈ 264 ms (S-F2), so everything not yet in the 166 ms (`finPf`'s
`rsWeight` ≈ 8 ms, `evalL`, the matrix evaluation) must fit in ≈ 64 ms VM, ≈ 230 ms VM in all.

**Options evaluated** (costs at 0.12 µs per F product in a flat table loop; `sizes.py`, `sizes.txt`
"stage-review changes 17"):

| Option | Effect | Verdict |
|---|---|---|
| (a) full templating of the skeleton: `merkleStep` (8 rows, 7,552 instances), `hornerPos` (127 `mulK`, 126 instances), per-level `query_i` blocks (`idx`/`tensorW`/fold/`dotKF`-add, 871), `round_d` blocks (the sumcheck rounds by degree), `eqTree` keys (`rowW`, `colW`, `mask`, `eqTableK`: closed form `O(log²)`), `walkRows` (B-part = `Â₀`/`B̂₀` at `(τ_lo, σ_lo)` by `walk_eq_sum`), `rsWeight` as `sq127` + `eqK` keys, one `oneOff` key per phase | local parts ≈ 36 k entries in all (≈ 72 k F); the sparse skeleton disappears | **adopt** |
| import classes: **regular** (aligned stride: `O(log)` per (key, import), ≈ 1,500 pairs ≈ 45 k F), **run-structured** (a contiguous run of message cells with the `packF` coefficient pattern: `run_mle`, `O(1)` per run from prefix arrays of `pack_r·eq(σ_lo,·)`: the Merkle step's query 16 words + `cur` 8 words + bit ≈ 3.5 runs ≈ 7 F instead of 25 cells × 3 F), **irregular** (table lookup, 3 F per cell) | imports ≈ 62 k F per slot | **adopt** (the generic per-import `eq(σ, cell)` is what cost 0.4 s) |
| column items padded to 64-B multiples (1,088 B and 320 B: +48 B × 871) | the `dotKF` columns become regular (word `W₀` 16-aligned): −55,712 irregular imports; piSize +41.8 KB, +760 compressions per slot | **adopt** |
| (b) one pass for both slots: cheap form (LOC, walks and tables shared; import terms per slot) | `evalM` 399 k F ≈ 48 ms vs 2 × 35 ms | **adopt** |
| (b′) slot-symmetric layout (slot `σ` at block `σ·2^15`: chain 22,465 + WOTS 498 + hashStmt 3 + L 62 + M 6,750 = 29,778 ≤ 32,768; `Â = eq(τ₂₀, σ₂₂)·Â_slot + Â_cross`) | `evalM` 292 k F ≈ 35 ms (−13 ms); touches `FRNodeLayout`, `FRBlockLayout`, `FRPubTarget`, the prover's layout | **reserve** (second lever, if the measurement needs it) |
| (c1) E lincheck restored (23 F rounds): one `evalM` at an F point, **no `evalMK`** | every K×F product in the evaluation becomes F (≈ 2×); `f̂(r′)` is RS claim 5 (`J_z = 5`: `rsWeight` +11.4 k rows, `Φ` +17 k rows per slot; `V` +4 ms); proof +1.1 KB + 2 KB (RS0), items +46, error row `23 · 2/2^128`, max unchanged; prover +0.14 s (link ≈ 2.94 s of 3.1 s) | **adopt** |
| (c2) fewer `mulK` in the finals (a sixth level, final `2^6`: halves the Horner block) | `V` −4 ms, rows −8 k per slot; a ladder change (P1 rows, error) | not needed once `hornerPos` is one key |
| (c3) cheaper Merkle steps: larger caps | caps are already `2^⌈log₂ t⌉` per level: doubling a cap costs ≈ what the removed step saves in the proof and adds hashed bytes (×4 caps: +135 KB, +4,200 blocks: over) ; padding sibling items to 128 B: +121 KB hashed, +3,776 blocks (1.03×) | rejected; the run-structured class makes a step ≈ 7 F |
| (d) preprocessing commitment to the fixed matrices with a Spark-style sparse-MLE argument | needs `commit(M_gen) = ρ_M` as a kernel fact over ≈ 2^21 entries (no `decide`, no `native_decide`) or `V` recomputing it (≫ `T_V`); +≥ 6 committed vectors of `2^21` F: +≥ 300 KB of opened columns (piSize cap 1.39× → over); error rows for the memory-checking grand products; ≈ 3–5 k Lean lines | **rejected** (three independent obstructions) |
| (e) per-entry cost: flat unboxed tables (`eq` tables as arrays of `UInt64` pairs), prefix arrays for runs, a fused `walkAB` (one pass computes `Â₀` and `B̂₀`: tables and loop shared; the XOR accumulation over a flat array) | the walks 2 × 15 ms → ≈ 8 ms per evaluation point; S-F2's hot spots (`dotKF` 26, `askNode` 22, `idx` 20, `maskRows` 7 ms) ≈ −40 ms | **adopt; the fused walk is mandatory** (without it the plan measures ≈ 247 ms VM) |

**Recommended plan** = (a) + import classes + column padding + (b) + (c1) + (e). One `evalM` per
`V`, at an F point, fully templated, one pass: tables 42 k F (`τ`: `2^11 + 2^10`; `σ`: `2^12 +
2^11`; the walks' `2 × 2^14`), fused walks ≈ 69 k F-equivalents, local parts 72 k, regular
imports 45 k, run/irregular imports 62 k per slot, prefix sums 3 k: **≈ 3.99·10^5 F ≈ 48 ms VM**.
**`V` (N30) ≈ 166 + 8 (`finPf`) + 3 (`evalL`, templated) + 48 = 225 ms VM ≈ 176 ms on the runner
(1.17× under 205.9 ms); with the S-F2 hot spots ≈ 185 ms VM ≈ 145 ms (1.42×); with (b′) ≈ 172 ms
VM ≈ 135 ms (1.53×).** The replay of this `evalM` in the parent's circuit is ≈ 423 k rows per slot
(the walks' product rows `2 × 2^14`, the XOR accumulation linear): **node rows ≈ 805 k per slot,
1,610,660 = `2^20.62` per node (1.30× under `N_M`); blocks 60,189 of 65,536 (1.09×)**, with the
templates still missing in S-E3 (`tensorW`, `rsWeight`, `walkA/B`, `kindInd`, `rowW`,
`shiftTarget`, `linkW`, `kindFoldWeight`) at A.11's figures. If the S-E4 measurement of `V` with
the plan exceeds 230 ms VM, the obstruction is the inherent part (two walks at a fresh point ≈ 8–16
ms, the 7,552 Merkle steps' runs ≈ 6 ms, the 166 ms base); the levers left are (b′), (c2) and the
hot spots; the smallest rule change would then be a smaller `R` in `T_V = T_triv / R` (the
coordinator's example `R = 10`).

**Revision 3.12 (normative):**
1. **Phase E** (§2 item 7): E1 point, E2 zerocheck (21 rounds), E end, E3 `κ_E`, **E4: the E
   lincheck, 23 F rounds of degree 2**, E4 end (`f̂(r′)` absorbed); `finE` (iv) evaluates
   `evalM(r_{E2}, r′)` at the F point `r′`; `f̂(r′)` is ring switching's claim 5 (`J_z = 5`; RS0
   absorbs `5 × 128` partials; `finRS` and `rsWeight` run 5 claims). `finPf`'s weight has no
   `evalM`/`evalMK` term; `evalMK` leaves `OpImpl`/`FRVIR`. Item sequence: `E4` 23 × (absorb,
   squeeze), `E4end` 1 absorb (48 B). Error table: E1–E4 row and RS1 (`11/2^128`).
2. **Format** (§1): column items padded to a multiple of 64 B (level 0: 1,088 B; levels 1–4: 320 B),
   so that every column's words start 16-word aligned; piSize 800,640 B (1.31×); items 8,920;
   compressions 23,225 per slot.
3. **Compiler and evaluator** (§4.4, A.11): every op is emitted into an aligned template key
   (op-block templates: a key's rows are the compiled rows of its op sequence under a register
   renaming, so `compile_sound`'s equivariance under substitution gives `tplBlock_sound`); the
   skeleton holds only the per-phase `oneOff` keys. `evalM`'s imports are classified regular /
   run-structured / irregular with the lemmas `regImport_mle` (dyadic range sums `rangeEq_mle`),
   `run_mle`, `irregular_mle`; the eq-tree keys use `eqTree_mle`; the walk keys `walkRows_mle`
   (`walk_eq_sum`); one op `walkAB` replaces `walkA`/`walkB`. The two slots are evaluated in one
   pass (shared local parts, walks and tables).
4. Modules affected: `FRVIRChain` (E4), `FRVIRFinals`/`SF`/`SG` (`finE`, `finRS` 5 claims, `finPf`),
   `FRRingSwitch` (`J_z = 5`), `FRTranscriptDefs`, `FRSoundnessPhases`/`Truths`/`StepC` (E4 as a
   lincheck phase: `lc_phase`, `round_escape_le`; `truthE`'s final), `FRVIR`/`FRVerifierImpl`/`Ops`
   (`walkAB`, no `evalMK`), `FRVIRCompile`/`TplExt` (op-block keys), `FRVIRTplEval` (flat tables,
   the import classes, the fused walk), `FRVIRTemplates`/`Tab`/`Lag` (the missing templates),
   `FRFormat` (padding), `FRNodeLayout` (`mRowModel`), `FRBlake2sWalk` (`walkAB`), the prover (E4,
   padding, 5 claims). S-E3's F-8 (`kindInd`/`packFK` untracked) is fixed on the way: tracked
   kind-dependent packs and a `kindInd` key.


### Stage-review changes 18 (S-0's 3.12 pass)

| Point | Ruling |
|---|---|
| E4end absorb | **None.** Revision 3.12 item 1 and A.4's "E4end, 48 B", and A.3 row 9's "f̂(r′), 16 B", are withdrawn. The value of f̂(r′), RS claim 5, comes from RS0's fifth slice (α₅ = Σ bᵢ s₄,ᵢ), under revision 3.9's rule that the α_j are computed from RS0. The counts are the Lean values: 8,920 items, 497 FS items, piSize = 800,640. |
| `finB′` | Drops the κ′·v_E term along with `finPf`'s evalMK term, since E is now a lincheck whose final is in `finE`. |
| Positions | Phase indices ≥ 24 move by +1, FS and item positions ≥ 300 by +46 (S-0: logs/S-0/check/pos-3.12.txt). |

### Stage-review changes 19 (INT-1, revision 3.12 integrated)

| Point | Ruling |
|---|---|
| L's base | **`lBase = 47,616`**: with `chainN = 23,225`, H ends at block 47,480, so L starts at the first multiple of 256 after it (it was 46,336). A.7 and §4.3 are amended. The prover uses the same value. |
| A.9 `finB′` | No `κ′·v_E` term (E's final is now `finE`'s lincheck check `evalM(r_E2, r′)·α_E` against E4's final claim, node-only). |
| A.9 `finPf` | A node's `rsWeight` takes a fifth point, all of E4's `r′` (claim 5, `rsPtIx .N30 = [1, 3, 5, 6, 17]`), matching `v_RS = Σ κ^j T_j` with `T₄`. There is no evalMK term. |
| `finRS` | `rsTail = T₃ + κ·T₄` for nodes. A leaf asserts claims 3–4's slices are zero. `nRS = 5`. |

### Stage-review changes 20 (revision 3.13): S-G1j's two kernel-checked defects and the node's `targetS`/`linkW`

| Item | Change |
|---|---|
| Defect 1 (`rs0_before_e4`): RS0 absorbed claim 5's slices at position 240 while its point `r′` was E4's (301–345) | **Ratified: E before RS.** Order `… Lr1, Lr2, Lr end, Lr3, E1, E2, E end, E3, E4, E4 end, RS0, RS1, B′, P1.0 …`. Positions (model = HEAD from E1 on): Lr1 170–177, Lr2 178–207, Lr end 208, Lr3 209; **E1 210–220, E2 221–262, E end 263, E3 264, E4 265–310, E4 end 311, RS0 312, RS1 313–316, B′ 317, P1.0 from 318** (HEAD: Lr4 210–239, RS0 240, RS1 241–244, E1 245–255, E2 256–297, E end 298, E3 299, E4 300–345, B′ 347). Every claim's point is fixed at RS0; A.10's RS rows apply unchanged; the B′ handoff is RS1's. S-0: `fsItems`/`piopPhases`, `FRTranscriptDefs`; S-G: the unit instantiations (`lr_unit_pos` pattern), the RS0 … B′ dooms; S-H2: the decoder's offsets; P2: the message order (A.3 fields 9, 9′ before 8). |
| Defect 2 (`evalL_short_zero`): `finLr` (iv) evaluated `evalL` at Lr4's 15 challenges zero-padded to 23, and every L row reads cells `≥ 2^15`, so the check was `c_{Lr4} = 0` for every `z` | **Chosen: (a′) = (a) merged with E4** — soundness first: the lincheck must range over all `2^23` cells (the L bits and M's `one` cell), so (b)'s window with an L-local `one` cell and fixed high coordinates is rejected (it special-cases `evalL` and the RS point and re-creates the window assumption that failed). Instead of a separate 23-round Lr4 (option (a): +23 rounds, +1 RS claim, +0.14 s prover), **Lr's lincheck claim is batched into E4**: `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ (â_L + κ_L b̂_L + κ_L² ĉ_L)` (`batch_bad_le` at 6: `5/2^128`), one 23-round lincheck, final `(evalM(r_{E2}, r′) + κ_E³ evalL(r_{Lr}, r′))·f̂(r′)`, `f̂(r′)` = RS claim 4 (**`J_z = 4` again**; 3.12's fifth claim is gone). Lr4 withdrawn (−30 items, −720 B). `T_V`: `evalL` at a 23-coordinate point is the templated `O(tpl)` evaluation (≈ 3 ms), the same as under (a); `rsWeight`/`Φ` back to 4 claims (−4 ms, −28.6 k rows per slot). Prover: one `2^23` pass for both linchecks (the table `W_M + κ_E³ W_L` in one sweep): the link stays ≈ 2.94 s (option (a) would reach ≈ 3.08 s of 3.1 s). S-0: `finLr` exports `v_L`, `finE` (iii)/(iv); S-F: `implC`'s `evalL` point; S-G: the row Spartan unit's inner rounds instantiated once (`nc = 23`, `truthE4`), `truthLr` keeps the zerocheck half; S-H2: the extractor's `ẑ` claims (4). |
| Gap 3 (`implC`: `targetS _ := targetSLeafI`, `linkW := 0`) | **Node `targetS` and `linkW` specified** (A.8 rows; A.6's `WM` map pinned: `WMbase_σ·128 + 2·(off_f + t) + p`, offsets `x` 0, `end9` 399, `end41` 466, `l` 533, `r0` 549, `r31` 565, `j` 581; 1,164 of 1,280 elements). `targetSNodeS`: `E` for all nine kinds over `nodeLayout`'s intervals — constant bits by dyadic range sums (`rangeEq_mle`), `stream`'s `t_lo` counter by the char-2 bit form `k_j + Π_{i<j} k_i` over a shifted range (`shift_mle`), last-block fields as single-block `eq`, `w43`'s `i`/`s` as a 399-term table sum; `linkWS`: 7 families per slot with sources, fields and mirror elements, `W_f = Σ_t eq(τ, src_f(t))·[eq(r_blk, src_f(t)) slotW(field_f) − eq(r_blk, mirBlk_f(t)) slotW(mirPos_f(t))]`, `Σ_f (2 n_f + O(log)) ≈ 1,300` products. Owners: **S-C** the specs and `targetS_node_eq`/`linkW_mle`; **S-F2/L-circ** `targetSNodeI`/`linkWI` + `_meets`, `implC` selecting by `s_N`; **S-E** `tplTargetSNode`/`tplLinkW` (A.11's ≈ 10 k / 2,500 rows); **S-G** the node S truth (`ShHolds` + the 7 terms) and Z1/Z2's tables over the node `targetS`; **P2** the mirror writes. |
| Margins (`sizes.py`, `sizes.txt` "changes 20") | piSize **797,888 B (1.31×)**; items **8,891** (qV 1.15×), FS items 468; compressions 23,146 per slot; node rows **776,778 per slot, 1,553,556 = `2^20.57` per node (1.35×)**; blocks **59,585 (1.10×)**; `T_V` (N30) **≈ 221 ms VM ≈ 173 ms runner (1.19×)** with the fused walks, **≈ 181 / 142 ms (1.45×)** with the S-F2 hot spots; stream link **≈ 2.94 s of 3.1 s**. |

**Revision 3.13 (normative):** (1) phase order `… Lr3, E1, E2, E end, E3, E4, E4 end, RS0, RS1,
B′` (§2 items 5–7, A.3, A.4, A.10); (2) Lr4 withdrawn; E4 is the lincheck of the six `κ_E`-batched
claims over the `2^23` cells, `finE` (iv) evaluates `evalM(r_{E2}, r′)` and `evalL(r_{Lr}, r′)`
at the F point `r′`, `f̂(r′)` is RS claim 4, `J_z = 4` (§2, §5 error table, the finals table); (3)
the node's `targetS` and `linkW` and the `WM` map (A.6, A.8, §4.2).

### Stage-review changes 21 (revision 3.14): INT-2 ratified, S-CN's findings, the `WM` ruling

| Item | Change |
|---|---|
| INT-2 (1) ratified | **E4 end absorbs 32 B** (`f̂(r′) ‖ 0^16`): the hashed stream is `1,481,344 = 64 · 23,146`, `stream_padded` holds with no padding cell; **piSize 797,904** (1.31×); the last block's `t_lo = 1,481,344` (A.3, A.4 row 18′, A.8 `targetSNode`, §0). The alternative (16 B + one padding cell per slot as a B′ point claim) is declined: it touches `pubCells`/`pfCells`/`truthBN`/`stream_padded` and the prover for no gain. |
| INT-2 (2) | **`finE` (v)** binds the E4 end message: value `= α₄` (RS claim 4's column value) and the zero half, for every kind (a leaf's `α₄ = 0` by `finRS`'s zero check). `finE` has 6 asserts (finals table). |
| INT-2 (3) | **`r_{Lr}` is Lr2's final point** (the zerocheck's, as `r_{E2}` is E2's); `finLr` exports it with `v_L` (§2 item 7, finals table). |
| INT-2 (4) | A.3 rewritten with the Lean's field numbering and INT-2's offsets: 7 Lr2 (5,648), 8 Lr end (6,368), **9 E (6,416; E2 +0, E4 +1,008, E4 end +2,112), 10 E end (8,560), 11 RS0 (8,608)**, 12 P1 (16,800), 13 Pf (18,912), 14 caps (19,584), 15 final (64,640), 16 columns (68,736), 17 siblings (556,240). |
| INT-2 (5) stale rows | A.9's `finB′`: `v* := v_RS + Σ_{k<9} κ′^{k+2} pub_k` — **no `κ′ v_E`** (the E claim is RS's since 3.12) and **no padding cells** (`J_f = 9`, B′ row `10/2^128`; A.7's public-cell list and A.10's B′ row amended). `mRowModel`'s "templates still missing" row over-counts `rsWeight`'s fifth claim (11,400): S-E drops it (an upper bound, `mRows_le` unaffected). |
| S-CN D-1 | **8 link families** (`nLinkFam = 8`): `end41` crosses the block boundary, split into `end41lo` (block `u`, bytes 41–63, 23 B, mirror bits 0–183) and `end41hi` (block `u+1`, bytes 0–8, 9 B, mirror bits 184–255) sharing one mirror source; **66 odd ends** (`k ≤ 131`). §4.2, A.8. |
| S-CN D-2/D-3, **the `WM` ruling** | 3.13's map (`WMbase_σ·128 + 2(off_f+t) + p`) put mirrors in elements `≥ 8`, i.e. positions `≥ 1024`, which the Sh collapse rounds (10 slot coordinates, `shSrc`) never reach; and `wotsBase_σ + 498` was slot 1's first WOTS block. **Pinned (A.6): mirror source `g` of slot `σ` is block `wmB σ + ⌊g/4⌋`, positions `256·(g mod 4) + [0, 256)`; `wmB σ = wmBase + 146σ`, `wmBase = wotsBase + 2·498 = 47,294` (after both WOTS runs), 146 blocks per slot, last block 47,585 `< lBase = 47,616`**; `g = off_f + t` with `x` 0, `j` 399, `end9` 400, `end41` 467, `l` 533, `r0` 549, `r31` 565 (581 of 584 sources). **Soundness ruling**: the mirrors may use positions `0 … 1023` (the `h_in`/`h_out`/`d` slots) of `WM` blocks because **the node's Sh is chain-masked**: its `Out`/`In` tables carry `Ind_chain(y)` and the start term is `κ_s(eq(0,·) + eq(chainBase_2,·))`, so no S claim reads a block `≥ 2·chainN = 46,292`; it must be masked anyway — consecutive WOTS, `hashStmt` and `WM` blocks are not linked, and the honest witness fails an unmasked identity (`FRShift.ChainLinks` is over every block: it is the leaf's form). `WM` blocks are `free`: their rows force Booleanity only, which bit mirrors satisfy; the link families' mirror side is the only other reader. The elements-4–7 variant (291 blocks per slot, `WM` in the L–M gap) is therefore not needed. **Kernel checks**: `shift_sound_masked` (S-C, `FRShift`: the masked identity ⇔ the two chains' links and endpoints, the verifier's `shW` gaining the interval factor) and `sh_reads_chain_only` (S-G: the node `truthS1` reads no block `≥ 46,292`); S-E's `FRNodeLayout`: `wmSlot = 146`, `hEnd = 47,594`, `regions_fit`. |
| S-CN D-4, D-5 | A.8's last-block `t_lo` is 1,481,344 (the counter form at `k+1 = 23,146`; only `f0` differs); `w43`'s steps are `s ∈ {0,1,2}` (`w_{i,0..2}` at `wotsBase_σ + 3i + s`; the contract's step is `s+1`): §4.2 amended to S-G's `nodeKind`. |
| S-CN §6, **the `linkW` interface** | **One op `linkWAll κ (τ ‖ θ) (r_blk ‖ r_pos) → AF 8`** replaces `linkW τ fam r_blk → F`: `finSh` packs `τ ‖ θ` (S1's 16 + 10) and `r_blk ‖ r_pos` (S2's 16 + 10), the 8 results are read by `getF` and weighted by `κ_s^{f+2}`; a leaf's result is `0^8`; shared tables (1.9 ms measured against 4.35 ms). `finSh`'s registers, `relSh`/`flag_finSh` renumber (S-0/S-F). **Error accounting**: `κ_s` batches the start term (power 1) and 8 families (powers 2 … 9): `batch_pow_bad_le` at degree 9, **S1 row `(26 + 9)/2^128`** (was `26 + 7`), 122.9 bits; the maximum error is unchanged (Ligerito's `2^-120.36`). S-CN §6.4 adopted too: **`slotW`'s In slot is kind-selected** — the node's `h_in` (slot map 2, base 0), the leaf's `d` (base 520). |
| S-CN §7, A.11 sizes | `tplTargetSNode` ≈ 16 k rows (from `targetSNodeI`'s measured 2.0 ms), `tplLinkWAll` ≈ 15 k rows per slot (`6 n_f + 24 len_f` per family; `linkWAllI` 1.9 ms); A.11's `linkW` row (8 × 2,500) replaced. |
| Margins (`sizes.py`, `sizes.txt` "changes 21") | piSize **797,904 B (1.31×)**; items 8,891 (qV 1.15×); stream `64 · 23,146`, no padding; H + L end at **47,740 of 49,152** (1.03×); node rows **935,775 per slot = S-E5's measured model (968,943 at 3.12) − 44,168 (claim 5) − 20,000 + 31,000; 1,871,550 = `2^20.84` per node (1.12× under `N_M`)**, M 14,622 of 16,384 blocks (1.12×); **`T_V` (N30): 204.9 ms VM measured with `evalM` (S-E5) + `evalLT` 4.5 + `targetSNode` 2.0 + `linkWAll` 1.9 = ≈ 213 ms VM (1.24× under the ≈ 264 ms VM-equivalent cap) ≈ 167 ms runner**; stream link (P2 §12 estimate) ≈ 3.0 s of 3.1 s (1.03×; the node prover and its measurement are P2's next item). |

| **(D) S-E6 §4: the replay fixed point** | **Ruling: option (a), with the layout rule of §4.4** ("constants in linear coefficients, products only between regularly addressed cells"). `evalM` is a sum over the fixed public matrices `𝒞` (templates `T_k`, import incidence matrices `Inc_f`, address bits `Addr`, `A₀`/`B₀`, pack/base patterns), each evaluated once at `(τ_lo, σ_lo)`; `R`'s u-rows for `C` have MLE `eq(τ_hi, uBase_C)·eq(σ_hi, tbl_C)·Ĉ(τ_lo, σ_lo)` — the same value — and its v-rows, sums and eq trees are closed forms, so `|R| ≈ #products + Σ_C rows(C)` with `MLE(R)` costing `O(|𝒞|·log)` beyond the shared `Ĉ`: the inequality `|R| ≥ |M∖R| + |R|` does not arise. **Soundness**: unchanged — `R` is the compiled replay of `V`'s `evalM` (`replay_sound` = `compileT_sound`), the plan is a function of sizes (`plan_wf`), no new error row, no extractor change, no `μ` row. **(b)** stays rejected (changes 17 (d): a kernel fact over `2^21` entries, +300 KB, memory-checking rows). **(c)** rejected: deferring the child's claim `Â(r_{E2}^c, r′^c) = v` to the parent's E phase never removes the evaluation (a multi-point reduction moves the point), batching across levels by `γ` destroys the `τ_hi/τ_lo` factorisation (cost × depth), and it changes the relation: the deferred `(r, r′, v)` would have to enter the hashed statement, `RelW`, `acc` and the extractor (which would decode a chain of pending claims verified only at the root), with a `γ` row per level and a new KS argument for claims no node checks locally. |
| (D) kernel lemmas | **L-circ/S-E**: `replay_mle`, `evalM_eq` over `𝒞`, `plan_wf`, `replay_sound`; the eq-tree closed form `eqTree_mle` (LSB-first prefix tables at aligned bases); `inc_mle` (`Înc_f` = the run/irregular import sums' u-rows). **S-G**: `truthE4`'s `evalM` is `evalMT` over the plan including `R` (no change of statement). **S-E5/E6's evaluator**: `evalMT` restructured so that each `Ĉ` is computed once and reused by the instances and by `R`'s u-rows (`FRVIRTplEval`/`TplFast`). |
| (D) margins (`sizes.py` "(D)"; **superseded by changes 22**: S-E9 measured the plan, `R` is 293,795 under the 3.15 walk ruling, and `T_V` is 169.4 ms measured with ≈ 13.5 ms to bind) | `R ≈ 259 k` rows per slot (was 423 k): **`mRowModel` 855,140 per slot, 1,710,280 = `2^20.71` per node (1.23×)**, 1.32× with the `phiRS` padding lever (−62 k); M 13,362 of 16,384 blocks. **`T_V` (N30)**: S-E6's measured 229.3 ms VM + `linkWAll` 1.9 + the remaining templates ≈ 3 + the child's two walks (**16 ms fused / 30 ms as implemented**) + `R`'s closed forms ≈ 5 = **≈ 255 ms VM (1.03× under ≈ 264) with fused walks; ≈ 269 ms (over, 0.98×) with the walks as implemented; ≈ 215 ms VM ≈ 168 ms runner (1.23×) with the S-F2 hot spots (`dotKF` 28, `askNode` 22, `idx` 20, `maskRows` 7 ms: −40 ms)**. **FR-D2 frontier**: the shape is consistent only with the fused `walkAB` **and** at least ≈ 10 ms of the hot-spot work (then 1.07×); without (e) the obstruction is `229 + 2·15 + 10 > 264`. The largest consistent shape without (e) does not exist at `m = 30` (the walks and the 229 ms base are inherent to one `evalM` call); the rule-change fallback is a smaller `R` in `T_V = T_triv/R` (the coordinator's `R = 10`). Stream link ≈ 3.0 s of 3.1 s (unchanged by (D)). |

**Revision 3.14 (normative):** (1) E4 end 32 B, piSize 797,904, no padding cell, `finE` (v); (2)
`r_{Lr}` = Lr2's final point; (3) A.3's numbering and offsets; (4) `finB′` without `κ′ v_E` and
padding cells, `J_f = 9`; (5) 8 link families with `end41lo`/`end41hi`; (6) the `WM` map of A.6 and
the chain-masked node Sh; (7) `linkWAll`, S1 row `(26 + 9)/2^128`, kind-selected `slotW_in`; (8)
`t_lo = 1,481,344`, steps `s ∈ {0,1,2}`; (9) A.11's `tplTargetSNode` 16 k / `tplLinkWAll` 15 k; **(10) the
replay `R` in the constant-coefficient linear layout of §4.4 (option (a)), ≈ 259 k rows per slot.**

**What each track changes (revision 3.14):**
- **S-0** (transcript, `FRVIRChain`/`FRVIRFinals`): E4 end 32 B (done in INT-2); `finSh`'s `linkWAll` op with the packed points, the `κ_s^{f+2}` weights and `relSh`/`flag_finSh`; `finLr`'s `r_{Lr}` export (done); A.3/A.4 as the table.
- **S-C** (`FRShift`, `FRVerifierImplNode` specs): `shift_sound_masked`; `linkWAllS` with the 8 families and the A.6 map (S-CN's `wmB`/`mirB`/`mpos` are the pinned ones), `linkW_mle`, `linkInd_sum`; `targetSNodeS` with `t_lo = 1,481,344` (S-CN's `cls 2` already).
- **S-F / S-F2** (`FRVerifierImpl`): `finE` (v); `implC`'s `targetS` and `linkWAll` selected by `κ.isNode`, `slotW_in` by kind; `linkWAll_meets`, `targetSNode_meets` in `implC_meets`; `finB′` without `κ′ v_E`.
- **S-E** (`FRNodeLayout`, mux, templates, evaluator): `wmSlot = 146`, `hEnd = 47,594`, `regions_fit`; the mux's mirror output addresses per the A.6 map; `mRowModel` without the claim-5 row, with `tplTargetSNode`/`tplLinkWAll` and `R` at 259 k; the two templates; **the replay `R` in the §4.4 layout (`replay_mle`, `plan_wf`, `replay_sound`, `inc_mle`, `eqTree_mle`) and `evalMT` sharing each `Ĉ` between the instances and `R`'s u-rows; the fused `walkAB` (with S-F) and the S-F2 hot spots, which the `T_V` fit now depends on.**
- **S-G** (soundness): the node `truthS1` with the chain mask and the 8 terms, `sh_reads_chain_only`; `truthB′` with `J_f = 9` (`pfCells`); the E4 end binder in `truthE4`'s end absorb; positions as INT-2 §3.
- **S-H2** (extractor): π offsets of INT-2 §4.1 and the item indices (−29 from B′ on); E4 end 32 B.
- **P2** (prover): the mirror writes per the A.6 map (146 blocks per slot after both WOTS runs), `end41` split, `linkWAll`'s weights in the Sh tables, the chain mask in the node's Sh tables, `slotW_in` = `h_in` for node blocks; E4 end `f̂(r′) ‖ 0^16` (done).

### Stage-review changes 22 (revision 3.15): S-E9's row kill rule, the walk, the levers, the queued corrections

| Item | Ruling / change |
|---|---|
| **(1) Rows: the kill rule fired** (S-E9: 1,065,133 per slot, 2,130,266 per node, 0.984×) | The model missed the plan's 6,169 sparse skeleton rows (18,354 forms, 31,103 entries) and the per-instance assembly (3,790 instances, 5,408 own cells): ≈ 193 k of `R` per child slot. Slot symmetry (20,506 of 20,510 cells shift by `2^20`) is used: `R` evaluates one slot's structure. S-E9's `R` of 412,606 includes a replayed XOR-DAG walk (131,811). |
| **(a) The walk** | **Ruling: (ii) materialised XOR DAG, laid out as a G-gadget template (§4.4).** `A₀`/`B₀` are dense (nnz 51,726,185 / 35,684,622; up to 7,358 terms a row) because the hash circuit folds XORs into the gates' forms; A.11's lincheck-replay class is withdrawn. The DAG rows (≈ 6·10⁴ XOR + 30,851 products = 90,851 per slot, fused `A₀`/`B₀`) are the node's own walk; **their MLE is the closed form `D̂` (80 G instances + the `Wire` matrix, ≈ 13 k products), so `R` replays no walk** (−118,811 rows of `R` against S-E9's DAG replay; −2 walks ≈ 16–30 ms of `T_V`). (i) the symbolic family is declined (it needs `Â₀` at a fresh point in every `evalM` and a row representation the dump and P2 cannot hold). `FRBlake2sGeneric`: `GOps.xor` emits a row in the template interpretation; S-E9's `tplWalkAB_ok` carries over with single-cell forms. Owner S-E (with S-A); P2 writes the XOR cells. |
| **(b) The levers and the shape** | Per slot under (a): 946,322 (1.108×). **Adopted lever: the `phiRS` key split** (`sq127` 128 rows + `stage` 7 rows → 136 aligned instead of 256: −62,464 per slot, measured): **883,858 per slot, 1,767,716 = `2^20.75` per node (1.19×)**; M 13,811 of 16,384 blocks (1.19×), used 61,551 of 65,536 (1.065×). **Reserve levers** (S-E, in order): the skeleton's sparse rows templated (≈ −110 k of `R`), each key's instances in arithmetic progression (≈ −20 k): together 753,858 per slot, 1.39×; then the skeleton's alignment padding (≤ 29 k). **No parameter or node-shape change**: the two-child node at `m = 30`, `L32`/`P30`, stands; the structural fix is the walk ruling, which also makes `T_V` independent of the walk count. **Consistent shape**: rows 1.19× (1.39× in reserve), `T_V` 1.44× (below), blocks 1.065× used / 1.19× M, stream link: P2's pre-ruling estimate 1.03× — see the frontier note. |
| **(c) `τ`'s length** | **Yes: one length, 18 coordinates for every kind**, P30/N30 zero-padded in coordinates 16–17 (§4.4); `eqPt`, `shiftEq`, `slotW`, `shiftTarget`, `shiftMask` defined on 18 coordinates with `eq_pad_zero` in their `_meets`; they become templates. S-0 (`finSh`'s `packFK`), S-C (specs), S-F2 (`_meets`), S-E (templates). |
| **(d) `maskRows`** | **Keep it bound** — unbound, the prover chooses the lincheck's row weights — **with the evaluator's shift class** for an own input at a per-chunk aligned shift (one `hfac` per chunk): `evalM` returns from 100.4 to ≈ 58 ms; S-E9's +39 ms was the generic `glVal` path, not the template. Owner S-E. |
| **(e) `planOf` 12.8 s** | **Rule: the plan is run-time data costing ≤ 0.2 s per process**, `O(pieces · log)` from per-key `Array` literals, `plan_wf` proved from their structure. Neither `initialize`/`init` nor elaboration-time precomputation is available (source rule), and closed-term extraction runs at process start inside `verify_s = 10` s, so laziness does not help: unwarmed non-`T_V` batches and DoS items (`10·T_V`) see the plan's cost. Owner S-E. |
| **(f) A.11 / §4.4** | updated: `R` 293,795 (≈ 164 k with the levers), the walk as the DAG template with `D̂`, `A₀`/`B₀`'s density stated, `maskRows`' shift class, `τ`'s length, `planOf`. |
| **`T_V`** | **Measured 169.4 ms VM (S-E8, `maskRows` foreign)**; S-E9's 207.2 ms is the `maskRows` defect (d). To bind: the remaining templates (`rsWeight` sub-templated as `sq127`/`eqK`, `shiftTarget`, the 745 `tensorW`, `tplTargetSNode`, `tplLinkWAll`) ≈ 4 ms, `D̂` 1.5, `R`'s closed forms and `Inc` sums ≈ 7, `maskRows` 1: **≈ 183 ms VM (1.44× under ≈ 264) ≈ 143 ms runner (1.44× under 205.9)**. The changes-21 (D) frontier note (two replayed walks, 255–269 ms) is superseded: no walk is replayed. |
| **FR-D2 frontier** | Rows, `T_V` and blocks are consistent at `≥ 1.05×` under (a) + the `phiRS` split (1.19× / 1.44× / 1.065×), with the skeleton/instance levers in reserve (1.39×). **The stream link is the thinnest margin: P2's estimate ≈ 3.0 s of 3.1 s (1.03×) predates this ruling**; the ruling removes ≈ 15 % of M's rows (the prover's E2/E4 table passes) and nothing else of the prover's work. P2 re-measures the N30 node; the target is ≤ 2.95 s. If it stays above, the obstruction is the two children's hashing (2 × 1,481,344 B at the spec hash's speed) plus the `2^23`-cell Ligerito encoding, both fixed by the shape; the largest consistent shape is then this one with the link budget as the binding constraint, and the smallest rule change is the link budget, not `T_V`'s `R`. |
| lBase | 47,616 in §4.3's table and A.7 (`lBase` since 3.12; S-H2k). |
| S-G2 level-4 tail | §5.2: P3.4 row 0 (level 4 checked directly, its `κ_c⁽⁴⁾` squeezes unused); A.10: Pf starts from `c1 4` with the padded weight `wFold 4` and background `¬ truthP3 4`; no verifier change. |
| INT-3 | `shiftMask τ r → AF 3` in A.8; `slotW_in` selected in `finSh` by `keep`; **the node's Sh start term has target 0 in characteristic 2**, both chain starts pinned by `streamStart.h0Pin` (`nodeKind 0 = nodeKind chainN = streamStart.target`, `Kind.hIn_eq_h0`): no hole (§4.2). |
| S-G5/S-G6 | A.10 preamble: `DF 2 := far₀ ∨ ¬Stmt`, `ExtIface`; the RS claims are checked through the finals' slice equations. |
| Margins (`sizes.py`, `sizes.txt` "changes 22") | piSize 797,904 (1.31×); items 8,891 (1.15×); **rows 1,767,716 = `2^20.75` per node (1.19×; 1.39× in reserve)**; M blocks 13,811 of 16,384 (1.19×), used 61,551 (1.065×), H + L end 47,740 below `Mbase` (exact); **`T_V` ≈ 183 ms VM ≈ 143 ms runner (1.44×)**; stream link ≈ 3.0 s of 3.1 s (P2's pre-ruling estimate; re-measure). |

**Revision 3.15 (normative):** (1) the walk rows are the materialised gadget DAG in the G-template
layout, MLE `D̂`; `R` replays no walk; (2) the `phiRS` key split (`sq127` + `stage`); (3) `τ` has 18
coordinates for every kind; (4) `maskRows` bound, the evaluator's shift class; (5) `planOf` ≤ 0.2 s,
run-time data from literals; (6) `lBase = 47,616`; (7) the S-G2 level-4 tail; (8) `shiftMask`,
`slotW_in` by `keep`, the start term's zero target; (9) the front's `DF 2`, `ExtIface`, the RS
claims through the finals' slice equations.

**What each track changes (revision 3.15):**
- **S-E** (L-circ): the walk as the G-gadget DAG template (`tplWalkAB` from the attic with row-emitting XORs, the `Wire` matrix, `D̂`'s closed form `dag_mle`); the `phiRS` key split; the evaluator's shift class for `maskRows` and own inputs at aligned shifts; `planOf` ≤ 0.2 s from literals (`plan_wf`); the five `τ`-ops as templates once (c) lands; `tplTargetSNode`, `tplLinkWAll`, `rsWeight` (`sq127`/`eqK`), `shiftTarget` (`bnd` bits as auxiliary cells), the 745 `tensorW`; then `R` (`replay_mle`, `replay_sound`, `inc_mle`, `eqTree_mle`) with the sparse-skeleton and instance-AP levers in reserve; `mRowModel` to the changes-22 figures; `FR.lean` imports `FRNodeMirror`.
- **S-A / S-E** (`FRBlake2sGeneric`): `GOps.xor` as a row-emitting op in the template interpretation; `sim_compressW` unchanged in statement.
- **S-0** (`FRVIRFinals.finSh`): `τ` of 18 coordinates for every kind (zero-padded), the ops reading the first `m − 14` where `ptA 16` does; `slotW_in` by `keep` (done in INT-3).
- **S-C**: the `τ`-ops' specs on 18 coordinates with `eq_pad_zero`; `shiftMaskS` (done).
- **S-F2**: the `_meets` lemmas for the padded `τ`; `implC` unchanged otherwise.
- **S-G**: Pf from `c1 4` with `wFold 4` and `¬ truthP3 4`; P3.4 row 0; `DF 2 := far₀ ∨ ¬Stmt`; `truthE4`'s `evalM` over the plan including `R` and the DAG rows.
- **P2**: the XOR cells of the walk DAG per slot (≈ 6·10⁴, from the G-template layout), the `phiRS` split's cell map, the 18-coordinate `τ`; re-measure the N30 node's stream link (target ≤ 2.95 s) and report the breakdown (hashing, E2/E4 passes, Ligerito).
- **Harness/S-I**: none; `verify_s` and `item_factor` are the constraints (e) answers.

### Stage-review changes 23 (revision 3.16): the R-V finals review (node path), INT-4, `T_V` on the runners

| Item | Ruling / change |
|---|---|
| **R-V-M1** (RS claim 2 lost `W_β`'s kind factor since 3.9: `kindFoldWeight := 0`; `finLc` asserts `Σ β^i v_i = α_Lc` while V binds `α_Lc = Σ_κ zfold_κ(r_k)`; every honest N30 proof fails; no soundness hole; A.10's L3 → RS0 hand-off unprovable) | **Ruling: (a), the Φ-aware kind factor in `rsWeight`'s claim-2 weight**, `Ŵ₂(ρ) = Σ_k c_k Σ_κ β^{i(κ)2^k}·eq(p_hi^{2^k}, ρ_hi)·Σ_{t∈I_κ} eq(p_blk^{2^k}, t) eq(ρ_blk, t)` (sound because `(Σ_κ β^{i(κ)} Ind_κ)^{2^k} = Σ_κ β^{i(κ)2^k} Ind_κ` on disjoint 0/1 indicators and `eq(p,u)^{2^k} = eq(p^{2^k}, u)` on Boolean `u`; `rs1_joint` is generic in the outer weight `g_j`), mirrored in `gL`/`trueL`; the kinds enter as ≈ 22 **pattern intervals** (chains, `hashStmt` singles, `w43` runs, key leaves, the even/odd path blocks as a bit pattern, `free` as the complement). **Costs**: items, piSize, error rows unchanged; `T_V` ≈ 128 · 22 · 24 ≈ 68 k products ≈ +6 ms VM (+5 ms on the 7763); rows +68,473 per slot (templatable, regular); `R` +≈ 3 k. **(b)** (an 18-round block sumcheck after L3β: items +36, π +864 B, error `3·18/2^128`, `rsWeight` unchanged + one `kindInd` evaluation) is declined: its table `ẑ_t(r_k)` needs a second `2^30`-bit fold pass in the prover (≈ 0.2–0.3 s against a 3.0 s link). `kindFoldWeight` is withdrawn as an op; `kindInd` stays spec-level. Owners: S-0 (`finLc`, the `rsWeight` op's `β` operand), S-C (`rsWeight_kind_eq`: the Φ form of `W_β` equals the pattern-interval sum), S-F2 (`rsWeightI`/`_meets`), S-G (`gL`, `trueL`, `truthL3`), S-E (the template, A.11), P2 (the honest `v_κ` unchanged; `v_RS` recomputed). |
| **R-V-M2** (`finLc` (ii) walks `free` with the Blake2s matrices; A.6 has `A₀^free = I`, S-C's `linM_free` gives `(1+α)·rowW`; every honest N30 proof fails; no hole) | **Fix as R-V proposes**: `free` has mask weight 0 (the node's `packFK` entry 8 is the zero register), and `(1 + α)·v_free·⟨rowW, eq(r_k,·)⟩ = (1+α) v_free (Σ_{s<64} L_s(λ) eq(r_k[0..5], s))·eq(r′_hi, r_k[6..13])` is added to the walk's `Â + αB̂` (one `eqPt`, a 64-term sum, 2 products; ≈ 80 rows). **Interaction with ruling (d)**: none adverse — `maskRows` stays bound through the shift class; its kind list keeps one length (the `free` entry is the zero register, `muxEl` emits no rows for equal registers), and `maskOf`'s `zeroRows .free = []` becomes irrelevant. `relLc`/`flag_finLc`, A.9 updated. Owners: S-0, S-C (`linM_free` as stated), S-G (`truthLc`), S-E (the term's template), P2 (none: `v_free` is the honest fold). |
| R-V-m1 | **`assertBit` is implemented** (clears `ok` unless the operand is a bit wherever `act κ` holds) and stays unused by `gen`; control `assertBit_rejects`. A no-op check is the `finZ` failure mode. Owner S-0. |
| R-V-m2 | noted for S-G7: `accept_fields` must be stated with `zh := finRS`'s exports and `exk` the folds' accumulated exports before any `hFront` binding is built on it. |
| R-V-m3 | the stale rows fixed: A.9 `finLc` (ii)/(iii), `finSh` (node `bnd = 0`, one RS claim, `linkWAll` + 8 `getF`, `bnd` 22), `finRS` (claim 3 = E4's `f̂(r′)` with the packing basis, bound in `finE`), `finLr` ((i) by `initClaim`, one assert); A.10's Lr row (no Lr RS claim) and L3 row; A.8 `shiftTarget` `AF 22`, `rsWeight` (E4's `r′`; the `β` operand), `walkAB` one op, `assertBit`, `kindFoldWeight` withdrawn. |
| INT-4 | `shiftTarget`'s `bnd` has 22 entries: the four boundary values, then the kind's last block `1^(m−14) ‖ 0^(32−m)` as constant registers (`bndOps`, `padB`), since a zero-padded `τ` breaks P30's fixed `1^18`; `shiftTargetAt`, `shiftTargetS_pad`, `eq_pad_zero`; A.8/A.9 rows added; the changed ops cost < 0.6 ms together. |
| **(C) `T_V` on the runners (H-V)** | **Tier of record, EPYC 7763: V N30 best 169.9–175.6 ms (medians 172–181) against the measured cap 206.0 ms: 1.17–1.21×**, with the `maskRows` slowdown still in the binary. **The VM → 7763 ratio for V is 1.19, not the chain checker's 1.28**: every earlier VM-to-runner conversion in §10 (changes 17–22) overstates the runner margin by ≈ 7 %; the normative figures (§0, §3.2) now convert at 1.19 (VM-equivalent cap ≈ 245 ms). Changes 22's 183 ms VM is 154 ms on the 7763 (1.34×); **with M1's +6 ms: ≈ 189 ms VM ≈ 159 ms runner, 1.30×**. The 8573C tier: ≈ 1.63×. |
| Margins (`sizes.py` "changes 23") | piSize 797,904 (1.31×); items 8,891 (1.15×); **rows 955,411 per slot, 1,910,822 = `2^20.87` per node (1.10×) with M1 and M2; the sparse-skeleton templating and the instance-AP layout (−130 k per slot) are moved from reserve into the plan: 825,411 per slot, 1,650,822 (1.27×)**; M 14,929 → 12,898 of 16,384 blocks; used 62,669 (1.046×) → 60,638 (1.08×); `T_V` ≈ 159 ms runner (1.30×); stream link ≈ 3.0 s of 3.1 s (P2's estimate; the rows cut lowers the E2/E4 passes; re-measure). With the levers every margin but the link is ≥ 1.08×. |

**Revision 3.16 (normative):** (1) RS claim 2's weight carries `B_β`'s kind factor in Φ form inside
`rsWeight` (`β` operand; `kindFoldWeight` withdrawn); (2) `free` has mask weight 0 and its lincheck
term is the closed form `(1 + α)·v_free·⟨rowW, eq(r_k,·)⟩` in `finLc` (ii); (3) `assertBit`
implemented; (4) `shiftTarget`'s `bnd` of 22 entries (INT-4); (5) `T_V`'s conversions at the
measured 1.19 and the measured cap 206.0 ms; (6) the sparse-skeleton templating and the instance-AP
layout are part of the plan, not reserve.

**What each track changes (revision 3.16):**
- **S-0** (`FRVIRFinals.finLc`, `FRVIR`): `packFK`'s `free` entry = the zero register; the `eqPt` + 64-term `free` term added to (ii); the `rsWeight` op gains the `β` operand (claim 2's kind factor for node kinds); `assertBit` implemented in `evalOp` (+ `assertBit_rejects`); `relLc`/`flag_finLc` restated.
- **S-C** (`FRSpartan`, `FRRingSwitch`/`FRVerifierImplNode` specs): `rsWeight_kind_eq` — the Φ form of `eq(r′_blk,·)·B_β·eq(r_k,·)`'s weight equals the pattern-interval sum; `linM_free`/`lin_final_kinds` as the spec of (ii); `lin_beta_claim` unchanged.
- **S-F2** (`FRVerifierImplOps`/`Impl`): `rsWeightI` with the kind factor (node kinds) and `rsWeight_meets`; `implC_meets` re-proved.
- **S-G** (`FRSoundnessFrRS`/`FrW0`/`FrPend`, `truthL3`, `truthLc`): `gL`/`trueL`/`lcPtL` carry the kind factor; `okRS` at `j = 1` against `vBetaL` with the new weight; `truthLc` with `free`'s closed-form term; the L3 → RS0 hand-off then discharges; `accept_fields` restated per R-V-m2 before `hFront` uses it.
- **S-E** (templates, `mRowModel`): the kind-factor template (≈ 68 k rows, regular), the `free` term's template (≈ 80 rows); `mRowModel` to 3.16's figures; the sparse-skeleton templating and the instance-AP layout now in scope (−130 k per slot).
- **P2**: `v_RS` with the kind-weighted claim 2 (honest `v_κ` unchanged); `finLc`'s new term in the IR interpreter (`ir.rs`); `bnd` of 22; re-measure the N30 stream link.
- **H / S-I**: `T_V` of record 206.0 ms on the 7763; the measured V 170–176 ms is the current binary (S-E10's `maskRows` fix pending).

### Stage-review changes 24 (revision 3.17): S-N1's findings, INT-5's `T_V`, the plan time

| Item | Ruling / change |
|---|---|
| O0 (ratified) | the linked route: `RunLink`/`ExtIfaceR`/`kstate_front_ofR` — the accepting chain `j` stays tied to `π` (`semIR … tr = some true`, `entriesOf L (pathOf L j) = fsOf tr items`); `ExtIface` over an arbitrary chain was false (a forgery log appended to an honest run). |
| O1 (ratified) | `truthE`/`nE`/`RejE4`/`hfit` over `nodeIRows (planOf fin)` (§4.4, A.10). **Error row unchanged**; `RowsFit` becomes `plan_rowsFit` over the templated layout (`mRows_le`, `usedBlocks_le`). Owner S-G (restating) with S-E (`plan_rowsFit`). |
| **O3, the extractor's domain** | **Ruling: `E := decodeWit ∘ semXIR ext ∘ extractorInput`, the DSL denotation, computable on every log; `Computes` by `compile_runs` on the domain; `final` by `ext_good_tape` over `semXIR` on every log `≤ logCap`; `hOut` discharged.** S-N1's choice branch is rejected: the contract's `choice_certificate` admits a non-constructive `E` beyond the domain at the kernel, but **the badge compiles the whole `submission` (AGENTS.md §10, §7.5), so a `noncomputable` `E` fails the badge build**; `E := ext.run` everywhere is unprovable beyond the domain (64-bit words); a potential equal to `1` beyond the domain breaks `step`. B-8 and §6.1 restated; `E`'s `vk` on a node is `π`'s `hdr.pub` (`vkOf_of_run`). Owners: S-H2 (`computes_Eof`, `E_leaf`, `E_node` over `semXIR`; `semXIR` total and computable — a compile fact the badge build checks), S-N1/S-G (`kstate_front_ofE` without `hOut`), S-I (the certificate's `E` field). |
| **O2/O2b, the row budget** | every unbound import now has a budget row (§4.4, A.11): trace cells 0 (pack map), `rsWeight` 45,604 + kind factor 68,473, `shiftTarget` 1,300, 745 `tensorW` 47,680, `targetSNode` 16,000, `linkWAll` 15,000, **`evalL` replay 10,000 (closed form; 40,000 if chunked)**, `R` 296,795, `free` term 80, **WOTS mux 2,788** (selectors 266, `a_{i,s}` 1,596, `e_i` 532, path `l_t`/`r_t` 128, digits → `h_out` 266; mirror sources are the mux outputs). With the 3.16 levers (`phiRS` split −62,464, sparse-skeleton templating −110,000, instance AP −20,000): **838,199 per slot, 1,676,398 = `2^20.68` per node: 1.25× (1.21× with the `evalL` risk)** — 3.16's 1.27× holds within 2 %. Owner of `StmtN → NodeResid`: **S-E** (the rows: the WOTS mux rows are S-E2's `wots_sound` construction emitted into the compiled program; the templates; `R`), with S-N1/S-G consuming `NodeResid`'s discharge. |
| **(4) `T_V` frontier** | INT-5: V 226–233 ms VM best = S-E11's 192.9 + `rsWeight`'s kind factor +31–33 (K×K products at ≈ 0.45 µs, not the 90 ns 3.16 assumed; 82 k products per call); at ratio 1.19 ≈ 190–196 ms on the 7763 against 206.0 ms: **1.05–1.08× today**. Still to bind ≈ 14 ms VM (`R` 7, `D̂` 1.5, templates 4, `evalL` 1, mux 0.3). Projections (`sizes.py`): as is + to-bind 240 ms VM → 1.02×; S-T1's kind factor to ≈ 20 ms (the `q` side in F, shared endpoints −20 %) → 227 → 1.08×; **+ S-E11's `evalM` levers (−12: shared pattern sums, folded `one` constants, additive low tables) → 215 ms VM ≈ 180 ms runner, 1.14×**; S-T1 to ≈ 8 ms → 203 → 1.21×. **≥ 1.10× needs V ≤ 223 ms VM (187 ms runner): S-T1's cut is mandatory and most of S-E11's levers.** If it is not reached: the smallest **rule** change is the `R` of `T_V = T_triv/R` (the measured cap would need ≈ 215 ms at 1.10×, i.e. `R ≈ 9.6`); the smallest **design** change is the per-kind machinery itself — one block kind with the pins as `(var k, one)` rows and all per-block values in `E` would remove `β`, `maskRows`, the kind factor and the 9-way muxes (≈ −40 ms VM), but it reopens S-E1-M2, S-C's `lin_trueSum_kinds` and S-G's L truths and is not proposed at this stage. |
| (5) plan time | the orchestrator's ruling recorded in §4.4: a closed top-level constant built at process start, outside every check's `NS` (`timedCheck` = parse + `acc`), **≤ 5 s on the VM** (43–49 s today, under the 70 s batch floor `verify_s · n + 60 s`); a cold-process control; 3.15's 0.2 s bound withdrawn. Owner S-E. |
| Margins (`sizes.py` "changes 24") | piSize 797,904 (1.31×); items 8,891 (1.15×); rows 1,676,398 (1.25×); M 13,097 of 16,384, used 60,837 (1.08×); `T_V` 1.14–1.21× projected (1.05–1.08× measured); stream link ≈ 3.0 s of 3.1 s (P2's estimate; re-measure). |

**Revision 3.17 (normative):** (1) `E` is the DSL denotation `decodeWit ∘ semXIR ext ∘
extractorInput` (B-8, §6.1); (2) the E truth and `hfit` over `nodeIRows (planOf fin)`; (3) the
complete row budget incl. the `evalL` replay and the WOTS mux rows (§4.4, A.11); (4) the plan is a
process-start constant, ≤ 5 s on the VM (§4.4).

**What each track changes (revision 3.17):**
- **S-H2**: `E` restated as `decodeWit ∘ semXIR ext ∘ extractorInput`; `computes_Eof` (= `compile_runs` + `fuel_le` on the domain), `E_leaf`/`E_node` over `semXIR` without `InDom`; confirm `semXIR` is a total computable `def` (the badge compiles it).
- **S-N1 / S-G**: the linked route (`kstate_front_ofR`), `kstate_front_ofE` without `hOut`; `truthE`/`nE`/`RejE4` over `nodeIRows (planOf fin)`; `NodeResid` discharged from S-E's rows; `FR.lean` imports `FRSoundnessExtAll`.
- **S-E**: `plan_rowsFit`; the WOTS mux rows emitted into the compiled program (`wots_sound`'s construction); the `evalL` replay as the closed form over A.7's regions; `mRowModel` to the changes-24 budget; the plan as a process-start constant ≤ 5 s with the cold-process control; S-E11's `evalM` levers.
- **S-T1**: the kind factor's `q` side in F and shared endpoints (target ≤ 20 ms, better ≤ 8).
- **S-I**: the certificate's `E` field is the `semXIR` denotation (computable); `acc` with `Impl.implCN`.
- **P2**: none new (the mux rows' cells are the honest WOTS values already written; `v_κ` unchanged).

