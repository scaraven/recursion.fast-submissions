# `flock-recursive`: entry blueprint (normative)

Status: phase 1 (B), 2026-10-27, for the implementation tracks L-field, L-piop, L-pcs, L-circ,
L-ext, L-cert, P and H (`PLAN.md` §3). Contract: `.contract` at core `15dac52`
(`RecursionFast/Contract/*.lean` is authoritative; where this file and the contract disagree, the
contract wins and the disagreement is reported). Inputs: `PLAN.md` (FR-D0 … D7), the phase-0
reports `T-theory.md`, `I-reuse.md`, `C-calibration.md`, `M-measure.md`, `F-flock.md`,
`K-kernels.md` (the prover-kernel kill test, measured on the EPYC 7763 and three AVX-512 models). Decisions
of this file are `B-n`; the theory memo's decisions are inherited unless a `B-n` overrides them
(each override says why). Evidence tags as in T: **paper**, **estimate**, **kernel**, **measured**.

Lean probes for this file are under `logs/blueprint/probe/` (run with `lake env lean` in
`.contract`, whose `.lake/packages` is a symlink to the prebuilt tree
`/home/devops/Verified-zkEVM/recursion.fast-v4/.lake/pkgs-local`, the one tree on this machine
whose revisions match the manifest at `15dac52` and that has Mathlib's oleans).
Numbers in this file were computed by `logs/blueprint/sizes.py` (the ladder, proof, trace and
circuit counts) from the formulas stated next to them; a number without a tag is arithmetic.

---

## 0. Summary

The entry is a Flock-class batch-R1CS argument over GF(2) with a Ligerito commitment over
F = GF(2^128) in the unique-decoding regime, fold challenges in K = GF(2^256), BLAKE2s everywhere,
and **recursive SROM nodes**: a node proof commits to the two children's signed traces, hashes
them (trace digests), checks one WOTS signature per child and replays each child's verifier
arithmetic as field-element rows. Three proof shapes share one verifier: the tree leaf
(`n = 2^18`, `m = 32`), the stream leaf (`n = 2^16`, `m = 30`) and the node (`m = 30`, two circuit
variants: two `m = 32` children, or two `m = 30` children). Knowledge soundness is certified
through the contract's `KState` with a per-fresh-query error `ε = 2^-120.2`; the extractor is a
word-machine program that decodes the node's commitment by erasure interpolation from the
agreement set within `2^46` steps at `m = 30`.

| Shape | `m` | witness bits | `|π|` | trace items / bytes | `qV` used | verifier F-mults |
|---|---|---|---|---|---|---|
| tree leaf, `2^18` compressions | 32 | `2^32` | ≈ 702 KiB (69 % of `proofCap`) | ≈ 7,850 / 1.29 MB | ≤ 8,192 | ≈ 1.1·10^5 |
| stream leaf, `2^16` compressions | 30 | `2^30` | ≈ 632 KiB (62 %) | ≈ 6,350 / 1.12 MB | ≤ 6,600 | ≈ 1.0·10^5 |
| node (variants LL, NN) | 30 | `2^30` (≈ 70 % used) | ≈ 632 KiB | ≈ 6,350 / 1.12 MB | ≤ 6,600 | ≈ 3.5·10^5 |

### 0.1 Decisions

| Id | Decision | Reason |
|---|---|---|
| **B-1** | **Tree leaves are single `m = 32` SNARKs of `2^18` compressions.** No segmentation. The stream leaf is `m = 30`. | The runner hashes the 64 statements `leafStmt (chainEnd sᵢ 2^18) 2^18` itself (`Tree.lean`), so each leaf digest must be proved as a `.leaf s n` witness, and the leaf clause of `Rel` demands the chain itself, not a signed child. A leaf proof made of signed segment proofs is **not certifiable**: `KS` holds for every `vk`, so a signature carries no soundness (design §2.2), and `final` could not derive `chainEnd s n = h`. A leaf made of two segment SNARKs verified with fresh queries is sound but is two Ligerito proofs: ≈ 1.3 MiB `> proofCap` (proof size is dominated by openings and nearly independent of `m`). Memory is settled by measurement: K's `m = 32` pipeline peaks at **3.81 GB** (**measured**, EPYC 7763, 4 threads; K §4.4) under the 11 GiB cgroup, and 64 × 2^18 is also faster than 128 × 2^17 (330–365 s against 385–430 s, K §4.2). T §3.4's "128 leaves × 2^17" is withdrawn. |
| **B-2** | **Nodes have shape `m = 30`**, with two circuit variants selected by a header byte: **LL** (both children tree leaves, `m = 32`) and **NN** (both children `m = 30`: nodes or stream leaves). | §4.3's count: 41.3 k BLAKE2s blocks (two `m = 32` traces of 1.29 MB plus two WOTS checks) + 1.3 k trace blocks + ≈ 2.9 k element-row blocks + ≈ 0.3 k bit-logic blocks ≈ 45.8 k of 65,536 blocks (70 %). K §4.1 measures the `m = 30` node at 0.81–0.83 s and the `m = 31` node at ≈ 1.9 s, which puts the stream link over its cap (K §0 (2)), so **`m = 30` is a hard requirement, not a preference**: if L-circ's exact count exceeds 2^30 the circuit is cut (§4.5's tightening list), not the shape. K's node budget is ≤ 60 k compressions and ≤ 2^26.2 committed M bits; this design uses 41.2 k and ≈ 2^25.5 (≈ 380 k rows of one committed element). Two variants, not one padded circuit: a padded circuit would hash a padded trace, and the trace is the child's actual bytes. |
| **B-3** | **Ladder of four levels** for every shape: rates 1/2, 1/4, 1/8, 1/16, rows 64 then 16, queries **290, 178, 145, 132** (133 at level 3 for `m = 30`), Merkle caps at depth 9, 8, 8, 8, then the `16 × k₄` message in the clear (8, 16 or 32 KiB). | T's levels 4–5 have `n ≤ 2^11`, where the UD radius slack `3/(δn)` pushes `(1−γ)^t` above the cap (`2^-119.3`, `2^-117.1` at `m = 30` with T's counts); sending the message in the clear is smaller than opening it (8 KiB against ≈ 50 KB) and removes 250 queries, 2 fold phases and ≈ 1.5 k compressions per child from the node. Per-level counts are fixed per shape by `t = ⌈120.25 / −log₂(1−γ)⌉`. |
| **B-4** | **F = BF64[y]/(y² + y + β)** through CompPoly's allowlisted `Ext` framework over the allowlisted `BF64`, with a two-`UInt64` fast twin; **K = F[u]/(u² + u + α)**; irreducibility of both quadratics by the trace criterion (no root, Artin–Schreier), kernel-evaluated traces. | Nothing is copied from outside the allowlist (no `BF128Ghash`, no Rabin certificate of our own); the fast twin's proof follows `SpartanSromFieldExtCorrect`. The cost: a GF(2^128) product is three BF64 products (≈ 75 ns compiled, **estimate** from M's 22–25 ns; T_V is not binding, M §7.2) and ≈ 50 machine statements in the extractor (§6.3 budget holds). The native prover uses the same tower; Flock's GHASH kernels are AVX-512 and not usable anyway. |
| **B-5** | **Proximity: own elementary mutual correlated agreement for lines in the UD regime** (route A), error `≤ (2n + 3)(e + 1)/|K|`, by the bivariate Berlekamp–Welch rank argument over `K(Z)` (§5.3). No ArkLib. | ArkLib's statements are in VCVio notation the source rule refuses and their closures are 42–45 k lines (I §2.5, §5); restating them is as much work as proving the UD line lemma, whose crude constant is harmless over K (`2^-217` at level 0, `m = 32`). |
| **B-6** | **Wiring: no permutation argument, no padding of trace items.** The node's witness is one hypercube of `2^16` blocks × `2^14` bits in four regions: H (BLAKE2s blocks), T (the two traces as contiguous bytes), M (field-element rows) and L (bit logic). H's message slots are identified with T by sub-cube alignment (two MLE claims), M reads T through irregular matrix entries evaluated by the incremental-eq rule (≈ 2 mults per entry, ≈ 57 k entries per child), and every M-internal pattern is a **template** with power-of-two strides whose matrix MLE the verifier evaluates in `O(template)` or `O(log)`, the BLAKE2s matrices by the circuit walk. | T_V is not binding (M: 4.3 M inline products in 205.9 ms), so the wiring is chosen for the prover and the Lean: padding would add 20 % hashing to H, which B-2's margin cannot pay; a gather sumcheck is subsumed by irregular matrix entries. §4.4. |
| **B-7** | **The verifier is an interpreter of a straight-line IR (`VProg`) generated from the shape**, and the node circuit's M and L regions are **compiled from the same IR** by one compiler with one soundness theorem. `V`'s `OProg` is the shape's fixed query sequence with the IR acting on answers. | The circuit-correctness theorem (G5) is then generic in the program: per-op lemmas, not a hand proof of 10^5 rows; `runSeq` on a well-shaped trace is the straight line by construction (T §3.3's requirement). The interpreter's overhead is inside the T_V margin (§3.4). |
| **B-8** | **`E := fun c π L => (ext.run (extractorInput c π L) (fuel t)).bind decodeWit`.** `Computes` then is termination within `fuel` and the output cap on every tape; `final` proves functional correctness of the program on good tapes only. The program is written in a counted-loop DSL (`XIR`) compiled to `XStmt` with a cost theorem, so termination and the step bound are syntactic. | Verified against `Contract/Extractor.lean` (`Computes` asks `decodeWit o = E c π L` and nothing about `E` itself) and `Controls/Certificate.lean` (`choice_certificate`: `E` is unconstrained off the domain). It removes the farness direction and every rejection branch from the refinement proof; functional correctness on good tapes is still owed (§6.5). |
| **B-9** | **Prover: std Rust, one `prover.s`, CPUID dispatch with an AVX2 + VPCLMULQDQ-256 tier and a scalar PCLMULQDQ tier**; no Flock crate is linked; schedules are Rust constants; circuit templates are built in `setup` and loaded per request. | PROVER.md §1 (binutils 2.42, no `cc` objects), F §4–5 (Flock has no AVX2 vector path; its per-shape circuit build takes 106 s). |
| **B-10** | `ε = 2^-120.2` (declared as `1/2^120 · (2^-0.2)` rounded: the certificate proves `ε ≤ 2^-120` with the exact rational `εR := 1/2^120 − 2^-124`), `δ = 2^-100`, `qV = 8,192`, `fuel t = 2^46 + 2^12 · t`. | §5.2's table sums to `≤ 2^-120.24` per fresh query; completeness loses only degenerate challenges (§5.5); `qV` covers the `m = 32` leaf's 7,850 queries; the extractor's count is `2^45.7` at `m = 30` (§6.3). |

### 0.2 Drift from the Flock paper (2026-09-19) and repository (`48f4bfe`)

T §6's table D-1 … D-17 stands, with these changes and additions:

| # | Here | Paper | Repository | Reason |
|---|---|---|---|---|
| D-2′ | ladder of **four** levels, 290/178/145/132(133) queries, `16 × k₄` message in the clear | five levels | six levels (`Secure m32`), final `yr_log_n` 4 | B-3 |
| D-9′ | F = BF64[y]/(y² + y + β) (tower over CompPoly's BF64), K = F[u]/(u² + u + α) | GHASH | GHASH, `F256 = F128[u]/(u² + u + x⁻¹)` | B-4 (allowlist) |
| D-13′ | node `m = 30`, variants LL/NN; regions H/T/M/L; T↔H by sub-cube alignment; M templates + irregular reads | — | tower with deferred matrix accumulator and root discharge | B-2, B-6; `acc` has no root step, so each node replays its children's lincheck matrix evaluation with the BLAKE2s walk (§4.4) |
| D-15′ | tree leaf `m = 32`, stream leaf `m = 30`, node `m = 30` | batches `2^10`–`2^18` | leaf `m = 32`, envelope `m = 29` | B-1, B-2 |
| D-18 | the verifier is an IR interpreter; the circuit is compiled from the IR | — | hand-written gate families | B-7 |
| D-19 | the extractor is `decodeWit ∘ run`; UD decoding by erasure interpolation from the agreement set | — | — | B-8, T §4.5 |
| D-20 | MCA-UD with constant `(2n + 3)(e + 1)` | BCHKS25 `γn + 1` | same | B-5 |
| D-21 | prover: AVX2 + VPCLMULQDQ-256 tier, CPUID dispatch, std only | Apple M4 | AVX-512 compile-time | B-9 |

---

## 1. Formats

All integers little-endian. A field element of F is 16 bytes: its two BF64 limbs `(c₀, c₁)` of
`c₀ + c₁ y`, each limb the 8 little-endian bytes of the polynomial-basis bit vector of BF64
(CompPoly's `BF64` layout, bit `i` ↔ `x^i`). A K element is 32 bytes: `(f₀, f₁)` of `f₀ + f₁ u`.
A position index of `b` bits is read little-endian from the bit string of an answer (§2.1).

### 1.1 The proof `π`

`π = hdr ‖ body`. The header `hdr` is 48 bytes:

```
hdr = kind(1) ‖ shape(1) ‖ variant(1) ‖ zero(13) ‖ pub(32)
  kind    0x4C 'L' leaf, 0x4E 'N' node, 0x57 'W' witness-sending (§5.5; never emitted by the
          native prover: π = WitnessSending.encode w exactly, no header, decided by the tag word)
  shape   30 or 32 (leaf: m); 30 (node)
  variant 0 (leaf); 1 = LL, 2 = NN (node)
  pub     leaf: s (32 bytes, the chain start, in the clear); node: zero
```

The `W` kind exists so that completeness holds for **every** witness of `Rel` (leaves of any
`n ≤ chainCap`, nodes with children of any shape): `V` decides it with no query as the baseline's
`C`/`N` branches (`chainEnd` recomputed, `acc` on both children; `SpartanSromNode`), the
extractor copies it (§6.2). It is told apart from `L`/`N` by its first byte (`0x00`/`0x01` tag
word against `0x4C`/`0x4E`) and its size (never `piSize`). Its leaf form costs `V` up to
`chainCap = 2^20` compressions (≈ 170 ms, under the DoS column's `10 · T_V`).

then, **leaf**: `enc64 n ‖ h ‖ zero(8)` (48 bytes: the length, the chain end; `n = 2^(shape − 14)`
is redundant and checked); **node**: `c₁ ‖ c₂` (64 bytes). Then `body = PIOP messages ‖ caps ‖
final message ‖ columns ‖ siblings`, in the order the verifier reads them (§2.3), every field at
a 16-byte boundary. `|π|` is a function of `(kind, shape, variant)` alone (`piSize`), checked
first; a proof of another length is rejected with no query.

| Part | Content | `m = 30` | `m = 32` |
|---|---|---|---|
| PIOP messages | skip messages `P^{ab}, P^z` on Λ (2 × 64 F), zerocheck rounds (`m − 6` × 3 F), lincheck rounds (9 × 3 F) and `â, b̂`, IO rounds, element-zerocheck and element-lincheck rounds (node), ring-switch partials `s_v` (128 F) and rounds (`m − 7` × 3 F), Ligerito fold rounds (6 + 4 + 4 + 4 rounds × 3 K) and the per-level consistency sums | ≈ 10.5 KB | ≈ 10.7 KB |
| caps | `(512 + 256 + 256 + 256) × 32` B | 40,960 | 40,960 |
| final message | `16 × k₄` F-elements | 8,192 | 32,768 |
| columns | level 0: `t₀ × 64 × 16`; levels 1–3: `tᵢ × 16 × 16` | 477,440 | 477,440 |
| siblings | `32 × Σ tᵢ (depthᵢ − capᵢ)` | 5,934 → 110,592 | 7,924 → 157,312 |
| **total** | | **≈ 647 KB (632 KiB)** | **≈ 719 KB (702 KiB)** |

`proofCap = 1,048,576`; margins 38 % and 31 % (**estimate**, exact once `piSize` is defined; the
PIOP-message part is the only approximate line).

### 1.2 Queries (kinds, byte layouts) and the trace

Every query is `tag(8) ‖ payload` with `|payload| ≡ 0 mod 16`, so `|q| ≡ 8 mod 16` and the trace
item `enc64 |q| ‖ q ‖ a` has `16 (k + 3)` bytes with the payload at item offset 16: **every field
element, digest and K element in a trace is 16-byte aligned in the trace's byte stream** (B-6).
Tags are 8 ASCII bytes; the first byte distinguishes the kinds, the rest names the level.

| Kind | Query | Bytes | Answer used as |
|---|---|---|---|
| seed | `"FRSEED00" ‖ vk ‖ c ‖ hdr` | 8 + 32 + 32 + 48 = 120 | state `st₀` |
| absorb | `"FRABS000" ‖ st ‖ msg`, `|msg| ≡ 0 mod 16` (zero-padded) | 40 + `|msg|` | new state |
| squeeze | `"FRSQZ000" ‖ st` | 40 | new state and challenge source |
| Merkle node, level `i` | `"FRMNOD" ‖ i ‖ 0 ‖ left ‖ right` | 72 | the parent digest |
| column, level `i` | `"FRMCOL" ‖ i ‖ 0 ‖ column` (`rowsᵢ × 16` bytes) | 1,032 (level 0) or 264 | the leaf digest |

The seed binds `vk`, `c` and the header (so `c₁, c₂`, `s`, `n`, `h` of the header are bound
through the first absorb; the leaf's `enc64 n ‖ h` and the node's `c₁ ‖ c₂` are absorbed next).
Answers are consumed as: F challenge = bytes `0 … 15` of the answer (each F value has exactly
`2^128` answers); K challenge = all 32 bytes (exactly one answer per value); positions of `b` bits:
`⌊256 / b⌋` per answer, index `i` = bits `[i b, (i + 1) b)` of the answer's little-endian integer
(`SpartanSromTranscript.idxOf`, generalised); two F challenges of two different phases may share
one answer (bytes `0 … 15` and `16 … 31`), never with the skip challenge `λ`.

**Trace sizes** (items, bytes, trace-digest compressions `⌈(1 + bytes)/64⌉`), from the ladder of
§2.2 with ≈ 140 Fiat–Shamir items:

| Shape | columns | siblings | FS | items | bytes | compressions |
|---|---|---|---|---|---|---|
| `m = 30` | 746 | 5,934 | ≈ 140 | ≈ 6,820 | ≈ 1,121 k | ≈ 17.5 k |
| `m = 32` | 745 | 7,924 | ≈ 140 | ≈ 8,810 | ≈ 1,287 k | ≈ 20.1 k |

(The script's item counts omit per-level consistency absorbs; `qV = 8,192` covers every shape's
exact count, which stage L-cert states as a theorem `queries_le`.)

### 1.3 The signed proof and the statement each shape proves

The signed-proof file is `harness/FORMAT.md`'s. What `V vk c π` decides:

- **leaf** (`kind = 'L'`): `c = leafStmt h n` with `n = 2^(shape−14) ∈ {2^16, 2^18}` and the SNARK
  proves `chainEnd s n = h` for the `s` of the header. Extracted witness: `.leaf s n`.
- **node** (`kind = 'N'`): `c = nodeStmt c₁ c₂` and the SNARK proves, for the committed signed
  proofs `p₁, p₂` (read from the T region, §4.3), `acc vk c₁ p₁ = true ∧ acc vk c₂ p₂ = true`,
  where `acc` is the submission's own (`proofCap`, `|tr| ≤ qV`, `queryCap`, `SigOk vk (traceDigest
  tr) σ`, `runSeq`). Extracted witness: `.node c₁ c₂ p₁ p₂`.

The child proof bytes `πᵢ` are not committed separately: every byte of `πᵢ` is in `trᵢ` (PIOP
messages and caps in absorb payloads, the final message in an absorb payload, columns in column
queries, siblings in Merkle-node queries), so `πᵢ = reassemble shapeᵢ trᵢ` (a fixed byte map,
`Format.reassemble`) and the circuit and the extractor both read `πᵢ` out of T. The signature
`σᵢ` is a region of L (§4.3).

### 1.4 The extractor's output layout

`witWords` of the contract (`Library/Words.lean`): tag `1`, `c₁`, `c₂`, then per child
`bytesWords πᵢ ‖ logWords trᵢ ‖ sigWords σᵢ`. For two `m = 32` children: `9 + 2 × (1 + 89,890 +
1 + 8,810 × 5 + 160,902 + 597) ≈ 5.8·10^5` words (`2^19.2`) of `outCap = 2^24`. A leaf: 6 words.

---

## 2. The protocol

### 2.1 Fields, codes, challenges

- **F = GF(2^128)** `:= Ext ⟨BF64, y² + y + β⟩` with `β ∈ BF64` of absolute trace 1 (fixed by the
  Lean module `FRField128`, which proves `Tr(β) = 1` by kernel evaluation and derives
  irreducibility: a root `y₀` would give `Tr(β) = Σᵢ (y₀² + y₀)^(2^i) = y₀^(2^64) + y₀ = 0`).
  **K = GF(2^256)** `:= Ext ⟨F, u² + u + α⟩`, `α ∈ F` of absolute trace 1, the same way. Fast
  twins: `F.mul` by Karatsuba over `BF64.mul` (spartan-srom's `clmul32` word products; three
  BF64 products and the reduction `y² = y + β`), `K.mul` by Karatsuba over `F.mul`; `toExt_mul`
  equalities as `SpartanSromFieldExtCorrect`'s.
- **The code.** `D ⊂ F` is the F₂-span of the first `log₂ nᵢ` elements of the fixed basis `1, y₀,
  y₀², …` of F over GF(2) (`y₀ := x` of BF64, then `y`, …; the exact list is a Lean constant with a
  kernel-checked independence certificate), enumerated as `D[j] = Σ_b j_b · basis_b`; `S = D[0 …
  k)` is its first `k` points (a subspace). `RSᵢ := { (p.eval (D[j]))_j : p ∈ F[X], deg p < kᵢ }`,
  distance `nᵢ − kᵢ + 1`; **message = values on S** (systematic), so the message of a codeword
  `w` is `w|_S` and the codeword of a message `f` is `Enc f := (Lagrange.interpolate S f).eval` on
  `D`. The prover computes `Enc` with the additive NTT; Lean never does.
- **Challenges.** F from 16 bytes, K from 32 bytes, positions as §1.2.

### 2.2 The Ligerito ladder (per shape)

`m′ = m − 7` packed variables; level 0 is `64` rows × `k₀ = 2^(m′−6)`; a level's fold of `ℓᵢ`
variables (6, then 4 = 3 message variables + 1 coordinate-split bit: a K element is two F
elements, the split is the new low row bit) gives the next level's message as `16` rows ×
`kᵢ/8`. `γᵢ = δᵢ/2 − 3/(δᵢ nᵢ)`, `δᵢ = 1 − ρᵢ`, `eᵢ = ⌊γᵢ nᵢ⌋`, `tᵢ = ⌈120.25/−log₂(1−γᵢ)⌉`,
cap depth `⌈log₂ tᵢ⌉`.

| level | `ρ` | rows | `log₂ k` (m = 30 / 32) | `log₂ n` | `γ` | `t` | `(1−γ)^t` | siblings/query | cap |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 1/2 | 64 | 17 / 19 | 18 / 20 | 0.2500 | 290 | `2^-120.35` | 9 / 11 | 2^9 |
| 1 | 1/4 | 16 | 14 / 16 | 16 / 18 | 0.3750 | 178 | `2^-120.67` | 8 / 10 | 2^8 |
| 2 | 1/8 | 16 | 11 / 13 | 14 / 16 | 0.4373 | 145 | `2^-120.28` | 6 / 8 | 2^8 |
| 3 | 1/16 | 16 | 8 / 10 | 12 / 14 | 0.4680 / 0.4686 | 133 / 132 | `2^-121.09` / `2^-120.38` | 4 / 6 | 2^8 |
| final | — | 16 | 5 / 7 | — | — | — | in the clear | — | — |

Merkle trees are binary over the positions of a level (one leaf = one column of `rowsᵢ`
elements); the cap is the full layer at the cap depth, sent in `π` and absorbed; a path is the
siblings from the leaf up to the cap, each a Merkle-node query whose answer must equal the left or
right half of the next query (selected by the position bit), the last compared with the cap entry.

### 2.3 Round by round (the verifier's reading order; the prover's writing order)

Phases are named as in the error table (§5.2). `st` is the transcript state; `absorb` and
`squeeze` as §1.2. "Rounds" of a sumcheck send `(g(0), g(1), g(∞))`-style 3-coefficient messages
(degree ≤ 3) or 2 coefficients (degree 2), checked `g(0) + g(1) = claim` and folded at the
challenge.

0. `st ← seed(vk, c, hdr)`; `st ← absorb(st, leaf: enc64 n ‖ h ‖ pad; node: c₁ ‖ c₂)`.
1. **Commit.** `st ← absorb(st, cap₀)` (the level-0 cap, `512 × 32` B).
2. **Z, zerocheck** of the bit-level R1CS `(A z)∘(B z) = C z` over the block cube `{0,1}^(m−6) ×
   Λ`-skip form (paper App. A), with `A = Sel ⊗ A₀`, `B = Sel ⊗ B₀`, `C = Sel ⊗ I`, `Sel` the
   block selector (leaf: all blocks; node: the H region): **Z1** `r ∈ F^(m−6)`: the first 7
   coordinates are the pinned constants `ρ₁ … ρ₇` (a Lean constant with a kernel-checked rank
   certificate, paper §4.3), the other `m − 13` from squeezes (8 per 128 bits ⇒ `⌈(m−13)/2⌉`
   squeezes); **Z2** the prover absorbs `P^{ab}, P^z` (64 + 64 F), `λ ← squeeze` (F, bytes 0–15,
   alone); **Z3** `m − 6` rounds of degree 3 (eq-weighted), challenge per round; the prover ends
   with `â, b̂, ẑ_Z` at the point `(λ-collapsed, r′)`.
3. **Lc, lincheck** of `â = Â(r′)` and `b̂ = B̂(r′)`: **L1** `α ← squeeze`; **L2** `m₀ − 5 = 9`
   rounds of degree 2 over the block's inner variables plus the 64-entry skip collapse (paper
   §4.4); the verifier evaluates `Â₀, B̂₀` at the two points by the circuit walk
   (`Blake2sWalk.walk_eq_sum`), multiplied by `Sẽl(r′_blk)`; result: one claim `ẑ_L` on `z`.
4. **Sh, shift arguments** (leaf: the chain `h_out(i) = h_in(i+1)` over the block index; node: the
   two trace-digest chains and the WOTS/leaf/path chains): **S1** `τ ← squeeze` (`m − 14`
   coordinates); **S2** one degree-2 sumcheck over the block index with the shift MLE
   `shift(τ, ·)` (paper §4.6) per chain; result: claims `ẑ_S` on `z`.
5. **IO.** Leaf: `s` and `h` against the first block's input and the last block's output, the
   paper's bit collapse (8 variables): **I1** `θ ← squeeze`, 8 coordinates + the `m − 14` block
   coordinates from the same answer pair; result: a claim on `z`. Node: the public region `P`
   (`vk ‖ c₁ ‖ c₂`, 96 bytes) and the T↔H identification (two claims at structured points, §4.4):
   **I1** `θ` as above; result: claims on `z`.
6. **Lr, the L-region R1CS** (node only): a Spartan zerocheck over L's rows (degree 3, `log₂ N_L
   ≤ 15` rounds) and lincheck (degree 2); the verifier evaluates `Ã_L, B̃_L, C̃_L` by their sparse
   sums; result: claims on `z`. Leaf: absent.
7. **B, batching** of the ≤ 8 claims on `ẑ` at ≤ 8 points by powers of **B1** `κ ← squeeze`
   into one claim `ẑ(r*)` (standard multi-point batching by one extra sumcheck of degree 2 over
   `m` variables with eq-weights; the memo's "powers of one α"; the batching sumcheck's rounds are
   charged like Z3).
8. **R, ring switching** (paper App. B.2–B.3, quirky variant): the prover absorbs the 128 partials
   `s_v` (128 F); **R1** `r″ ← squeeze` (7 coordinates); `m − 7` rounds of degree 2; the verifier
   evaluates `B̂` by the width-128 matrix branching program (`m − 7` layers); result: one claim
   `f̂(r_f)` on the packed polynomial.
9. **E, the element R1CS** (node only): `(A_M f)∘(B_M f) = C_M f` over the M rows: **E1**
   `r_E ← squeeze` (`log₂ N_M ≤ 18` coordinates), zerocheck rounds of degree 3; then **E2** the
   three claims batched by `κ_E ← squeeze` and a lincheck of degree 2 over `m′` variables; the
   verifier evaluates `Ã_M, B̃_M, C̃_M` by templates (§4.4); result: claims `f̂(r_{E,j})`.
10. **B′** batch the `f̂` claims (R and E) by `κ′ ← squeeze` into one claim `f̂(r_f*) = v*`.
11. **P, Ligerito opening** of `f̂(r_f*) = v*`, level by level `i = 0 … 3`:
    - **P1** `ℓᵢ` fold rounds: each `z ← squeeze` (K, 32 bytes), the prover sends the round's
      3 K-coefficients (the sumcheck of `Σ_x eq(r_f*, x) f(x)` restricted to the level's
      variables; paper App. C); after the rounds the folded message is committed: `st ←
      absorb(st, capᵢ₊₁)` (levels 0–2) or `absorb(st, final message)` (level 3);
    - **P2** positions: `tᵢ` indices of `log₂ nᵢ` bits from `⌈tᵢ / ⌊256/log₂ nᵢ⌋⌉` squeezes;
    - the prover's columns and paths are read: for each position `j`, a column query (`rowsᵢ`
      elements) whose answer must be the path's leaf, then `depthᵢ − capᵢ` Merkle-node queries
      up to the cap entry `capᵢ[j >> (depthᵢ − capᵢ)]`;
    - **P3** consistency: `κ_c ← squeeze` (9 F coordinates); the claims `fold_z(column_j) =
      Enc(f^(i+1))[j]` for the `tᵢ` positions are batched with eq-structured coefficients over
      `⌈log₂(tᵢ + 1)⌉ = 9` coordinates into the next level's sumcheck claim (paper App. C.2,
      repository's form); `Enc(f^(i+1))[j]` is an evaluation claim on the next level's
      polynomial, folded into the running claim.
    - At the final level the verifier holds the `16 × k₄` message in the clear: it evaluates the
      running claim and `Enc(final)[j]` at the `t₃` positions directly (Lagrange from `S`, `k₄ ×
      t₃` products).
12. Accept iff every check passed.

The leaf of shape 30 and the node share steps 0–4, 7, 8, 11; the node adds 5 (node form), 6, 9,
10. The query sequence is a function of `(kind, shape, variant)` and the answers; **no query
depends on the proof bytes except through the state**, so `runSeq` on a trace with the right
query bytes is the straight line of §3.

### 2.4 Parameters (summary)

| Name | Value | Where fixed |
|---|---|---|
| `m₀` (bits per BLAKE2s block) | 14 | leanerVM circuit, spartan-srom's block |
| `k_s` (skip) | 6, `|Λ| = |S_skip| = 64` on the F₂-subfield points of T §1.2 | Z2 bound 126/2^128 |
| pinned coordinates | 7, the paper's geometric progression in F | kernel certificate `pinned_rank` |
| leaf shapes | `m ∈ {30, 32}`; node `m = 30` | B-1, B-2 |
| ladder | §2.2 | B-3 |
| `qV` | 8,192 | §1.2 |
| `ε` | `εR = 2^-120 − 2^-124` (≥ the table's `2^-120.24`) | §5.2 |
| `δ` | `2^-100` | §5.5 |
| `fuel t` | `2^46 + 2^12 · t` | §6.3 |

---

## 3. The verifier `V vk c π`

`V` is `FRVerifier.V : Digest → Digest → Proof → OProg Bool`. Its structure (B-7):

```
V vk c π :=
  match parse π with                            -- no query; |π| = piSize kind shape variant
  | none => ret false
  | some ⟨kind, shape, variant, pub, hdr2, body⟩ =>
    if kind = W then ret (decide (Rel' vk c (decode π)))   -- §5.5: clear leaf / plain node, no query
    if kind = leaf ∧ ¬ (c = leafStmtF h n) then ret false else
    if kind = node ∧ ¬ (c = nodeStmtF c₁ c₂) then ret false else
    runIR (vprog kind shape variant) (vk, c, π)   -- the straight line
```

`vprog kind shape variant : VProg` is a computable list of operations over a register file of F
and K values, digests and bytes, generated by `FRVIR.gen`; `runIR` is its `OProg` interpreter: an
op `ask kind payloadRegs → dst` issues the query and binds the answer, every other op is pure
(`mulF, addF, mulK, invF (as mul by the inverse with a check), eqDigest, eqF, bitsOf, lagrange,
walk, mbp, ...`). The leaf and node branches differ only in the generated program. Branches in
`V`'s own code are exactly: parse failure, statement check, `runIR`'s per-op checks (each
`assert` op is an `ite` returning `false`). `qV`: `queries_le : ∀ H c π, ((V vk c π).queries
H).length ≤ 8192`, by `gen`'s query count per `(kind, shape, variant)` (`decide` over the three
cases).

### 3.1 Operation counts (one run of `V`; **estimate** from §2.3, `logs/blueprint/sizes.txt`)

| Work | leaf `m = 32` | node `m = 30` |
|---|---|---|
| Ligerito column folds `Σ tᵢ rowsᵢ` K×F products (2 F each) | 51.7 k | 51.7 k |
| final-level `Enc` at `t₃` positions (`k₄ t₃` F) | 16.9 k | 4.3 k |
| eq tables, K arithmetic in fold rounds, consistency eq-weights | ≈ 15 k | ≈ 15 k |
| univariate skip: Lagrange of `P^{ab}, P^z` at `λ` (128 points) | ≈ 20 k | ≈ 20 k |
| sumcheck rounds (Z 26, Lc 9, Sh, IO, B, R 25, P 18; node + E 18 + Lr 15) | ≈ 0.5 k | ≈ 0.8 k |
| ring switch MBP: `(m−7)·128` F + `(m−7)·2^14` conditional 128-bit XORs | 3.2 k + 4.1·10^5 XOR | 2.9 k + 3.8·10^5 XOR |
| lincheck walks `Â₀, B̂₀` (two points) | ≈ 1.2·10^5 XOR | ≈ 1.2·10^5 XOR |
| node: `Ã_M, B̃_M, C̃_M` by templates: irregular reads ≈ 2 × 57 k entries × 2 F, template sums ≈ 2 × 10 k F, two more BLAKE2s walks | — | ≈ 2.5·10^5 F + 1.2·10^5 XOR |
| node: `Ã_L, B̃_L, C̃_L` sparse sums (`nnz_L ≈ 2^18`) | — | ≈ 2^15 F + 2^18 XOR |
| **F-multiplications** | **≈ 1.1·10^5** | **≈ 3.5·10^5** |
| **128-bit XORs** | ≈ 6·10^5 | ≈ 1.1·10^6 |

### 3.2 `T_V` (**estimate** on the EPYC 7763, M §7.2: 47 ns inline, 62 ns boxed per F-product
measured for GHASH; the tower product is ≈ 1.3× that, **estimate** 60–80 ns; XOR ≈ 8 ns; BLAKE2s
compression 158 ns)

Root check = `acc` on an NN node: trace digest `17.5 k × 158 ns = 2.8 ms`; `SigOk` 0.23 ms;
parsing (byte-level, `ByteArray.get!`) ≈ 2 ms; arithmetic `3.5·10^5 × 70 ns = 25 ms`; XORs
`1.1·10^6 × 8 ns = 9 ms`; interpreter dispatch and register traffic: allow 2× on arithmetic
(**estimate**; the interpreter runs over an `Array` of ops with F values as unboxed pairs of
`UInt64` inside a structure, which M measured at 79 ns per product). **≈ 65–90 ms against
205.9 ms.** The DoS column (10 × T_V per input) is safe: a malformed `π` is rejected at `parse`
or at the first failing `assert`, and no branch is costlier than the honest run. Kill test: the
compiled `acc` on a real NN root measured in the badge process (§9, H1).

### 3.3 What `V` never does

It never hashes except `leafStmtF`/`nodeStmtF` (one compression) and never evaluates a Merkle
hash (each is a query answer); it never recomputes a chain; it never reads a child proof (a node
proof commits to its children, it does not carry them).

---

## 4. The circuits

All circuits are batch R1CS over GF(2) in Flock's form: the witness `z ∈ GF(2)^(2^m)` is `2^(m−14)`
blocks of `2^14` positions; the bit-level constraints are `(A z)∘(B z) = C z` with `A = Sel ⊗
A₀`, `B = Sel ⊗ B₀`, `C = Sel ⊗ I` (one base block circuit `A₀, B₀`, a block selector `Sel`),
plus shift arguments and IO claims that are linear in `z`; the node adds the element R1CS over
the packed `f` and the L R1CS over bits. Positions inside a block follow spartan-srom's
`Blake2sR1CS` layout **re-based so that the 512 message bits occupy element slots 4–7** (bits
`512 … 1023`), the chaining value `h` slots 0–1 (bits `0 … 255`), the output slots 2–3 (bits `256
… 511`), the counter/flag words and the constant `1` in slot 8, the gates from bit `1280` as
today (B-6: the message must be a 4-element-aligned sub-cube). The block circuit is leanerVM's
BLAKE2s product circuit as in spartan-srom (`SpartanSromBlake2sCircuit/Words/Compress`, 14,720
gates): `A₀(k, ·), B₀(k, ·)` for a gate position `k` are its two forms, for an input position
`(var k, var one)`, for a constant position `(one, one)` or `(0, 0)`, for the output positions
`(out form, one)`.

### 4.1 The leaf circuit (`FRLeafCircuit`)

`2^(m−14)` **chain blocks**, block `i` with `h_in = h0` (constants, the unkeyed 32-byte
parameter block, `Blake2sR1CS.h0`), message `0x43 ‖ d_i ‖ zero(31)`, `t = 33`, `f0 = 0xFFFFFFFF`
(constants), output `d_{i+1}`: exactly spartan-srom's chain block with the re-based layout.
Constraints beyond the blocks:

- **Sh (chain)**: `∀ i < n − 1 : out(i) = in(i+1)` as the shift claim `Σ_i Σ_j eq(τ, (i, j))
  (z[blk i, 256 + j] − z[blk (i+1), 520 + j]) = 0` for `j < 256` (the digest `d` sits at message
  bytes 1–32 = bits `520 … 775`): one degree-2 sumcheck with the shift MLE (paper §4.6; Lean:
  `FRShift.shift_sound`: the claim at a random `τ` holds for all `τ` only if every link holds,
  `(m−14+8)/2^128` bad).
- **IO**: `in(0) = s`, `out(n−1) = h`: two evaluation claims at structured points (the paper's
  8-variable bit collapse of the 256 bits, `θ`).

Theorems required (Lean-like):

```
leaf_sound  : ∀ (z : Fin (2^m) → F) (s h : Digest),
  Boolean z → (∀ i, Holds blockR1CS (z ∘ blk i)) → ChainLinks z → IOHolds z s h →
  chainEnd s (2^(m−14)) = h
leaf_complete : ∀ s, let z := leafWitness s in Boolean z ∧ (∀ i, Holds …) ∧ ChainLinks z ∧ IOHolds z s (chainEnd s n)
```

`leaf_sound` is spartan-srom's `chain_sound` restated over blocks + links instead of the wiring
rows (`SpartanSromChainSound` adapts; `block_sound`, `block_complete`, `not_holds_flip` reused).
Counts: `2^18` blocks × 14,720 gates; witness `2^32` bits (`m = 32`), `2^30` (`m = 30`).

### 4.2 The stream-hash block and the WOTS blocks

The **stream block** is the same compression circuit with `h_in` (256 bits), the message (512),
the counter low word `t` and the final flag `f0` as **inputs** (positions `(var k, one)`), `t_hi
= 0` and `f1 = 0` constants. `FRBlockStream.block_sound`: a Boolean block with `one = 1` carries
at slots 2–3 `compress h_in m t f0 0`. The trace digest of a byte string `B` (`|B| = 1 + Σ(16(k+3))`
bytes, `N = ⌈|B|/64⌉` blocks) is the chain `h₀ = h0`, `h_{i+1} = compress hᵢ Bᵢ tᵢ fᵢ 0` with
`tᵢ = 64(i+1)` except `t_{N−1} = |B|`, `fᵢ = [i = N − 1]·0xFFFFFFFF`, the last block zero-padded:
`traceDigest tr = le h_N` (the contract's `blake2s` unrolled, `FRBlockStream.blake2s_chain`,
kernel). In the node, `tᵢ, fᵢ` are inputs constrained by two evaluation claims against public MLEs
(`t̃(θ) = Σᵢ eq(θ,i)·64(i+1)` adjusted at the last block; `f̃(θ)`), and the padding bits are
constrained to zero by an evaluation claim.

The **WOTS check** (`FRWots`) is a straight-line program of the IR (B-7) on digests: for each of
the 133 chains, 3 steps with selectors (`sel_s = [dᵢ ≤ s]`): `x_{s+1} = sel_s ? F(j, i, s, x_s) :
x_s`, where `F` is a stream-hash *block* (43-byte message, one compression) whose message
`0x57 ‖ enc64 j ‖ i ‖ s ‖ x_s` is wired from the signature region; the leaf hash of the 133 ends
(4,265 bytes = 67 chained blocks), the 16 path steps (65 bytes, 2 blocks each, left/right by the
index bit). All its compressions are H blocks (one chain per hash), the wiring is template M rows
(digest equalities as element rows) and L bits (digits, selectors, index bits). 399 + 67 + 32 =
498 blocks per child. Theorem `wots_sound : circuit holds → SigOk vk m σ = true` by `SigOk`'s
definition (`sigRoot`, `wotsLeaf`, `wotsEnds`) and `block_sound`.

### 4.3 The node circuit (`FRNodeCircuit`): regions and counts

One hypercube `2^16` blocks × `2^14` bits (`m = 30`), four regions at block-aligned bases:

| Region | Base (blocks) | Content | Blocks LL / NN |
|---|---|---|---|
| **H** | 0 | stream blocks: child 1's trace-digest chain (`N₁`), child 2's (`N₂`), the two WOTS checks' compressions (2 × 498); unused H blocks hold the all-zero block (which satisfies `A₀,B₀,I` with `one = 0`) | 2 × 20,113 + 996 = **41,222** / 2 × 17,512 + 996 = **36,020** (`Sel` = the prefix of length `N_H`) |
| **M** | 49,152 (`= 3·2^14`, aligned to `2^13`) | the packed element rows: per child, the templates of §4.4 (fold products, eq tables, `Enc` of the final message, Merkle selections, skip Lagrange, sumcheck checks, MBP layers, lincheck-replay products, digest equalities), ≈ 190 k committed elements per child (§4.5) | ≈ 2 × 2^18.5 elements: **8,192** blocks allotted, ≈ 4,800 used |
| **T** | 57,344 (`= 28·2^11`, aligned to the two-trace sub-cube of `2^18` elements) | child 1's trace bytes at element offset 0, child 2's at element offset `2^17` (2 MiB), each zero-padded | 2 × 2^17 elements = 2 × 2^21 bits = **256** blocks |
| **L** | 61,440 | bits: the two signatures (2 × 4,772 B), WOTS digits and selectors, the position bits of every Merkle step as bit-elements `(b, 0, …, 0)` (`7,924 × 128` bits per child), shape constants, `tᵢ/fᵢ` inputs | ≈ 2 × 2^20 bits = **128** blocks allotted |
| **P** | 65,535 (last block) | public: `vk ‖ c₁ ‖ c₂` (768 bits) at its start, then `1`, then zeros | 1 |

Used: LL 41,222 + ≈ 4,800 + 256 + ≈ 110 + 1 ≈ **46.4 k of 65,536 (71 %)**; NN ≈ 41.2 k.
**Kill test (B-2)**: stage L-circ's exact `nodeLayout` must prove `N_H + N_T + N_M + N_L + 1 ≤
2^16` by `decide`; if it fails, `m := 31` (every table of this file has the `m = 31` column
available from `sizes.py`; the extractor budget at `m = 31` is `2^47.7`, §6.3).

The constraints: H blocks under `Sel ⊗ (A₀, B₀, I)` (zerocheck + lincheck of §2.3 steps 2–3);
the chains and WOTS wiring under **Sh** (shift claims over the H block index for the two digest
chains; the WOTS steps are M-template equalities); the T↔H identification, `t/f` inputs, padding
and `P` under **IO** (evaluation claims); the element rows under **E**; the bit logic under
**Lr**.

**What the circuit asserts of child `i` (the `replay` IR, compiled to M + L rows):**

1. the trace bytes `Tᵢ` parse as `N_q` items of the shape's query sequence: every item's
   `enc64 |q|`, tag and padding equal the shape's constants (equalities of elements of `Tᵢ`
   against constants: M rows with constant forms);
2. the Fiat–Shamir chain: the state field of absorb/squeeze item `k+1` equals the answer field
   of item `k` (element equalities, irregular reads of `Tᵢ`);
3. the seed item's payload holds `vk` and `cᵢ` (equal to the `P` region's elements) and the
   header `hdrᵢ`;
4. `V`'s arithmetic on the answers and the proof fields read from `Tᵢ`: every op of `vprog kindᵢ
   shapeᵢ variantᵢ` as element rows (an F product = 1 row, a K product = 3 rows (Karatsuba) + 2
   linear, an inverse = 1 row `x · x⁻¹ = 1` with `x⁻¹` a witness, an `assert eq` = 1 linear row,
   a position-bit use = a bit-element from L), the Lagrange and eq tables as rows, the MBP layers
   as rows, the `Â₀, B̂₀` walks as the lincheck-replay template (§4.4);
5. the Merkle steps: `cur = left + b·(right − left)` per 128-bit half (2 rows per step, `b` a
   bit-element), the cap comparison (1 linear row);
6. `|πᵢ| ≤ proofCap`, `|trᵢ| ≤ qV`, `|q| ≤ queryCap`: constants of the shape (`decide` once);
7. `SigOk vk (traceDigest trᵢ) σᵢ`: H chain `i`'s final output equals the WOTS message input (an
   element equality), §4.2's WOTS rows.

**The node theorem** (`FRNodeCircuit.node_sound`, Lean-like):

```
node_sound : ∀ (variant) (z : Fin (2^30) → F) (vk c₁ c₂ : Digest),
  Boolean z → HHolds z → ShHolds z → IOHolds z vk c₁ c₂ → LrHolds z → EHolds (pack z) →
  let p₁ := readSigned variant 1 z; let p₂ := readSigned variant 2 z
  acc vk c₁ p₁ = true ∧ acc vk c₂ p₂ = true
```

where `readSigned variant i z := ⟨reassemble shapeᵢ (traceOf i z), traceOf i z, sigOf i z⟩` is
the same byte map the extractor implements (§6), and `acc` is `Submission.acc` unfolded for this
submission (`FRSubmission.acc_eq`). Proof structure: (a) `HHolds ∧ ShHolds ∧ IOHolds` ⇒ for each
child, H chain `i` computes `traceDigest (traceOf i z)` (`blake2s_chain`, `block_sound`,
`shift_sound`), and the WOTS blocks compute their steps; (b) `EHolds ∧ LrHolds` ⇒ the IR
interpreter on `(vk, cᵢ, reassemble …, answers of traceOf i z)` returns `true`
(`FRVIRCircuit.compile_sound`, generic in the program) and `SigOk` holds (`wots_sound`); (c)
`runIR = runSeq (V …)` on a trace whose query bytes are the shape's sequence
(`FRVerifier.runSeq_eq_runIR`), and (1)–(2) give exactly that; (d) the size facts (6). The
completeness twin `node_complete` builds `z` from two accepted signed proofs of the right
shapes (`nodeWitness`), for the Lean `P`.

### 4.4 Wiring: templates and irregular reads (B-6)

The element R1CS `(A_M f)∘(B_M f) = C_M f` has rows indexed by `(child, template, instance, slot)`
with power-of-two strides (`rowIx = Mbase + child·2^17 + tplBase + inst·2^a + slot`), and every
matrix entry is one of:

- **template-internal**: column `= rowIx + const` or `= Mbase + child·2^17 + tplBase′ + inst·2^a′
  + slot′` (an aligned region of the same instance index): the MLE of such an entry pattern
  factorises, `Σ_{inst,slot,slot′} eq(τ,(inst,slot)) eq(σ,(inst,slot′)) = eqInner(τ_inst, σ_inst) ·
  Σ_{(slot,slot′) ∈ tpl} eq(τ_slot, slot) eq(σ_slot, slot′)`: `O(log)` for the instance part and
  `O(|tpl|)` once per template (`FRVIRCircuit.tpl_mle`);
- **shift-structured** (the eq-table binary trees, `parent(j) = j >> 1`; the Horner/MBP chains):
  a transfer-matrix product, `O(log)` (`FRVIRCircuit.shift_mle`);
- **lincheck replay**: the rows `eqrow[k] · (A₀ eqcol)[k]` for `k < 2^14`: the `B_M` sub-matrix is
  `A₀` placed at an aligned base, so `B̃_M` restricted to them is `eqInner · Â₀(τ_slot, σ_slot)`,
  evaluated by the **walk** (`walk_eq_sum`), ≈ 6·10^4 XORs; the same for `B₀`;
- **irregular**: a column in `T` (a trace element at address `Tbase + child·2^17 + e` with `e`
  from the item layout) or in `L`: evaluated entry by entry, `Σ eq(τ, row) eq(σ, col)`, with
  `eq(σ, col)` by the **incremental rule** along increasing `col` (`eq(σ, c+1) = eq(σ, c) ·
  rat(σ, c)` with `rat` from the trailing-ones count, precomputed ratios `σᵢ/(1 + σᵢ)` and their
  inverses; `FRVIRCircuit.eq_incr`), ≈ 2 mults per entry amortised; ≈ 57 k entries per `m = 32`
  child (18.6 k level-0 column elements, 7.3 k other column elements, 31.7 k sibling elements,
  ≈ 0.3 k FS fields).

`Ã_M(τ, σ) = Σ_templates …` is one computable function `evalM variant τ σ` with the theorem
`evalM_eq : evalM variant τ σ = Σ_{(r, c) ∈ nnz (A_M variant)} eq(τ, r) · eq(σ, c)` (and for
`B_M`, `C_M`), the one place where the circuit's matrices meet the verifier. `nnz` is generated
from the IR by `compile`; `evalM` is generated from the same IR by `compileEval`; `evalM_eq` is
proved once, generically in the IR, from the per-kind lemmas above.

The T↔H identification: `z[Hbase + i·2^14 + 512 + j] = T[64·i·8 + j]` for `i < N_H^{hash}` (the
hash blocks of the two chains, in order) and `j < 512`: both sides are sub-cubes (`i` on the
high bits, `j` on the 9 low bits of the message slots `4 … 7` = bits `512 … 1023`; `T` at
`Tbase` with `(i, j)` contiguous), so the claim is `ẑ(θ_H) = ẑ(θ_T)` at two structured points for
a random `θ` of `log₂ N_H + 9` coordinates, charged `(m−14+9)/2^128`. Child 2's chain starts at
`T` element offset `2^17`, which is a sub-cube boundary; its hash blocks follow child 1's.

### 4.5 Gate and row counts (LL variant, per child; **estimate**, exact in L-circ's `nodeLayout`)

| Rows (M) | count | nnz class |
|---|---|---|
| level-0 folds: eq table (62) + 64 products + 1 sum, per column, 290 columns | 36.8 k rows | products template; column operands irregular (18.6 k) |
| levels 1–3 folds: 14 + 16 + 1 per column, 455 columns | 14.1 k | same (7.3 k irregular) |
| fold-round sumcheck checks (18 rounds, K arithmetic) | ≈ 0.4 k | template |
| `Enc(final)` at `t₃` positions: `k₄ t₃` products + Lagrange weights | 16.9 k + 2 k | template |
| consistency eq-weights (9 coordinates × `Σ tᵢ`) | 6.7 k | template |
| Merkle steps: 2 rows per sibling | 15.8 k | sibling operands irregular (31.7 k) |
| skip Lagrange at `λ` (128 points, numerators, one inverse) | ≈ 20 k | template |
| sumcheck round checks (Z, Lc, Sh, IO, B, R) | ≈ 0.6 k | template |
| MBP layers `(m−7)·128` + the `(m−7)·2^14` conditional XORs as linear forms | 3.2 k | template |
| lincheck replay: 2 eq tables (2 × 2^14) + 2 × 2^14 products | 65.5 k | eq-tree + walk |
| digest/element equalities (FS chain, tags, lengths, caps, WOTS wiring) | ≈ 10 k | irregular (≈ 0.3 k) + template |
| **per child** | **≈ 190 k rows, ≈ 190 k committed elements (2^17.5), ≈ 2,370 blocks** | |

Per node: ≈ 2 × 2,400 = 4,800 blocks of the 8,192 allotted (§4.3). K §4.1 budgets the node's
element zerocheck at ≈ 2^17.6 rows (4 ms of 0.81 s); ours is ≈ 2^18.5 rows, so L-circ **applies**
the tightening (the stream link's 13 % margin, K §4.3, is the binding cap): the lincheck-replay eq tables are shared by the two children (same shape per variant:
−2^15 rows), the skip Lagrange denominators are constants (−10 k rows). The region bases are
parameters of `nodeLayout`; the only hard constraint is the total ≤ 2^16 (B-2's kill test). L: 2 × (4,772 B +
7,924 × 128 bits + ≈ 20 k bits) ≈ 2 × 1.05 M bits ≈ 128 blocks ✓.

---

## 5. The potential `μ`, knowledge soundness, completeness, controls

### 5.1 Shape of the proof (`FRSoundness*`)

The contract's `KState (Rel (acc vk)) (V vk) E ε` is built as spartan-srom's (`SoundnessKSBase`
Part A, `muG_step`): `μ L = [Bad L ∨ Esc L] + Σ_{chains on the frontier} φ(chain)`, where a
**chain** is a maximal transcript path in the log (seed → absorb/squeeze → …; `SoundnessLog`'s
forest, `Matches` re-parameterised by the new query kinds), **Bad** is a digest collision in `L`,
a fresh answer hitting an in-play digest (a cap entry, a Merkle node or a state absorbed so far), a
repeated query, or a flipped group, and `φ` charges every **open phase** of the chain its bad
probability over the unasked squeezes (the per-phase term of §5.2, a martingale across the
squeezes of a multi-answer phase, `extCount_split`). `empty` is trivial; `step` is `muG_step`'s
local inequality per phase (one lemma per row of §5.2: "the number of answers that close the
phase on a bad challenge is at most `pᵢ · 2^256`", from exact fiber counts `card_chF_fiber =
2^128`, `card_chK_fiber = 1`, `card_idx_fiber`) plus the hash term; `final` is §5.4.

### 5.2 The per-fresh-query error table (node, `m = 30`; the leaf has a subset)

| # | Phase | Field | Bad probability | `−log₂` | Lemma |
|---|---|---|---|---|---|
| Z1 | zerocheck point, `m − 13 = 17` free coordinates (19 at `m = 32`) | F | `17/2^128` (`19/2^128`) | 123.9 (123.8) | `zerocheck_bad_le` (SR) on the multilinear in the free coordinates; the pinned ones by `pinned_rank` (DT24, **paper** → kernel certificate) |
| Z2 | skip `λ` | F | `126/2^128` | **121.0** | `skip_bad_le`: `P^{ab} − P^z` has degree `≤ 2(2^6 − 1)` (LV `natDegree_pPoly_le` ported) |
| Z3 | 24 rounds, degree 3 | F | `3/2^128` each | 126.4 | `round_bad_le` (SR) |
| L1, L2 | lincheck `α`; 9 rounds degree 2 | F | `1/2^128`; `2/2^128` | 128; 127 | `batch_bad_le`, `round_bad_le` |
| S1, S2 | shift `τ` (`m−14+8 = 24` coordinates); 1 round | F | `24/2^128`; `2/2^128` | 123.4; 127 | `shift_sound` |
| I1 | IO/identification `θ` (`≤ 25` coordinates) | F | `25/2^128` | 123.4 | SZ on a multilinear |
| Lr | L R1CS: point 15 coordinates; rounds degree 3, 2 | F | `15/2^128`; `3/2^128` | 124.1; 126.4 | Spartan (SR `SoundnessSpartan`) |
| B1 | claim batching, ≤ 8 claims | F | `7/2^128` | 125.2 | `batch_bad_le` |
| R1 | ring switch `r″` (7), 23 rounds degree 2 | F | `7/2^128`; `2/2^128` | 125.2; 127 | `ring_inj` (SR, redone for GF(2) ⊂ F, 128 limbs) |
| E1, E2 | element zerocheck point (18), rounds degree 3; batching; lincheck rounds degree 2 | F | `18/2^128`; `3/2^128`; `2/2^128`; `2/2^128` | 123.8; 126.4; 127; 127 | Spartan over F |
| B′ | batching R and E claims (≤ 4) | F | `3/2^128` | 126.4 | `batch_bad_le` |
| P1 | fold round, level `i` (18 in all) | **K** | `((2nᵢ + 3)(eᵢ + 1) + 2)/2^256` | ≥ **217.0** (level 0, `m = 32`) | `mca_ud_line` (§5.3) + the sumcheck round |
| P2 | positions, level `i`, `tᵢ` of them | `log₂ nᵢ` bits | `(1 − γᵢ)^{tᵢ}` | 120.35, 120.67, 120.28, 120.38 (`m = 32`); 121.09 at level 3 for `m = 30` | `positions_bad_le` (SR `r7_*` pattern, `card_idx_fiber`) |
| P3 | consistency batching, 9 coordinates | F | `9/2^128` | 124.8 | SZ on a 9-variable multilinear |
| H | every fresh query: collision with a logged digest, hit on an in-play digest | — | `(4 · logCap + 8)/2^256` | 158.0 | SR `bad_step_le` generalised (labels are full 32-byte digests here, not 31-byte) |

**Maximum per fresh query: `2^-120.28 + 2^-158.0 ≤ 2^-120.24 ≤ εR = 2^-120 − 2^-124`** (level 2's
positions; the skip is `2^-121.0`). Two F challenges sharing one answer are charged the sum of
their rows (`≤ 2^-123`). The leaf shapes have no Lr, E, B′ rows and the same maxima.

### 5.3 The proximity lemma (`FRProximity.mca_ud_line`, B-5)

Statement (counting form, over any field `K` with `F ⊆ K` a subfield, `D ⊂ F` of `n` distinct
points, `C = RS[K, D, k]`, `e` with `2e < n − k + 1`):

```
theorem mca_ud_line (u₀ u₁ : Fin n → F) :
  let bad := { z : K | ∃ w ∈ C, agree (u₀ + z•u₁) w ≥ n − e ∧
                 ¬ ∃ v₀ v₁ ∈ C_F, agreeSet (u₀,u₁) (v₀,v₁) = agreeSet (u₀ + z•u₁) w }
  Nat.card bad ≤ (2n + 3)(e + 1)
```

("for all but `(2n+3)(e+1)` values of `z`, if the line point is `e`-close, its agreement set with
its unique nearest codeword is the joint agreement set of an interleaved F-codeword"). Proof plan
(BCIKS20 Thm 4.1's UD argument, made elementary):

1. **Berlekamp–Welch solutions.** For `z` with `u_z` `e`-close to `w_z` (unique: `2e < d`,
   `close_unique` SR), the pair `(E_z, N_z) := (Π_{j ∉ A_z}(X − D[j]), E_z · w_z)` satisfies
   `∀ j, E(D[j]) · u_z[j] = N(D[j])`, `deg E ≤ e`, `deg N < k + e`. Conversely (`bw_unique`),
   every nonzero solution `(E, N)` of that linear system has `N = E · w_z` (`E(u_z − w_z)`
   vanishes on `A_z`; `N − E w_z` has degree `< k + e ≤ n − e` and vanishes on `A_z`, `|A_z| ≥ n
   − e`, so it is zero).
2. **The system over `K[Z]`.** The `n × (k + 2e + 1)` matrix `M(Z)` with columns `D[j]^i (u₀[j]
   + Z u₁[j])` (`i ≤ e`) and `−D[j]^i` (`i < k + e`) has entries of `Z`-degree ≤ 1. If more than
   `e + 1` values `z` admit a nonzero kernel vector, every maximal minor (a polynomial of degree
   ≤ `e + 1` in `Z`, nonzero only in the `e + 1` first columns) vanishes identically, so over the
   field `K(Z)` the rank is `< k + 2e + 1` and a nonzero kernel vector exists (Mathlib:
   `Matrix.rank`, `linearIndependent_rows_iff_isUnit`, `LinearMap.ker_ne_bot_of_finrank_lt`);
   clearing denominators gives `(E(X, Z), N(X, Z))` over `K[Z]`, `E ≠ 0`.
3. **Specialisation.** For all `z` outside the ≤ `deg_Z E` zeros of the leading coefficient,
   `(E(·, z), N(·, z))` is a nonzero solution, so `N(X, z) = E(X, z) · w_z(X)` by step 1 when `z`
   is close. Division in `K(Z)[X]`: `N = E Q + R`, `deg_X R < deg_X E`; at each such close `z`,
   `R(·, z) = 0`, so if there are more than `deg_Z(numerators of R)` of them, `R = 0` and `Q ∈
   K(Z)[X]` with `Q(·, z) = w_z` for every close `z` off the denominators (≤ `(e+1)` more).
4. **Positions.** For `j < n`, `r_j(Z) := u₀[j] + Z u₁[j] − Q(D[j], Z) ∈ K(Z)`: either `0` (then
   `j ∈ A`) or a rational function whose numerator has degree `≤ 2(e+1)`, so `j` is an agreement
   position of `u_z` with `w_z = Q(·, z)` for at most `2(e+1)` values of `z`. If `|A| < n − e`,
   every close `z` has an agreement position outside `A`, so there are at most `n · 2(e+1)` close
   `z` off the exceptional sets. Hence with more than `(2n + 3)(e + 1)` good `z`, `|A| ≥ n − e ≥ k`.
5. **The interleaved codeword.** On `A` (`≥ k` points), `Q(D[j], Z) = u₀[j] + Z u₁[j]` is affine
   in `Z`; the interpolant of degree `< k` through `k` points of `A` is `v₀ + Z v₁` with `v₀, v₁ ∈
   F[X]_{<k}` (F-valued data on `D ⊂ F`), and equals `Q` (both of `X`-degree `< k`, agreeing on
   `k` points). So `v₀, v₁ ∈ C_F`, `(u₀, u₁) = (v₀, v₁)` on `A`, and for every good `z`, `w_z = v₀
   + z v₁` and its agreement set is `A` (the "cancellation": `j ∉ A` agrees for at most one `z`
   when `u₁[j] ≠ v₁[j]`, never otherwise, already counted in step 4).

The constant `(2n + 3)(e + 1)` is crude and irrelevant over K. Budget: 1,200 lines. The
consequence used in `final` (`fold_preserves`): under no bad fold challenge, the `2^ℓ`-row word
`U` is `e`-close with agreement `A` iff its `ℓ`-round fold is, with the same `A` (induction over
the rounds; the fold of the rows by `(1 − z)u₀ + z u₁` is the line `u₀ + z(u₁ − u₀)`).

### 5.4 `final`: the deterministic walk

Given `L` with `¬ Bad L`, `μ L < 1` (so no open phase closed on a bad challenge: `accept_not_doomed`
SR) and `(V vk c π).runLog L = some true`:

1. `runLog_chain` (SR template): the accepting run is a complete chain of `L`, each answer unique
   (`pred_unique_lt`), each Merkle path read off `L` (`open_binding` generalised to caps:
   `cap_binding`: the position's leaf column is the first preimage, read top-down from the cap
   entry, which is absorbed before the positions are squeezed — `colL_prefix`).
2. **Ligerito induction** from the final level up (`ligerito_final`): let `W⁽⁴⁾ := final message`
   (in the clear). For `i = 3 … 0`: the level-`i` word `W⁽ⁱ⁾` read off `L` (first preimage per
   cap-rooted path; erasure where none) is `eᵢ`-close to `RSᵢ^{rowsᵢ}` with agreement `Aᵢ ⊇` the
   queried positions' consistent set, because: the queried positions (`P2` not bad) are a
   `(1−γᵢ)`-fraction witness set; by `fold_preserves` (P1 not bad) the fold `u` of `W⁽ⁱ⁾` is
   `eᵢ`-close iff `W⁽ⁱ⁾` is, with the same `A`; the consistency check passed on all `tᵢ` positions
   against `Enc(f⁽ⁱ⁺¹⁾)` (P3 not bad, and the sumcheck rounds), so `u` agrees with the codeword
   `Enc(f⁽ⁱ⁺¹⁾)` on `tᵢ` random positions, which is impossible for an `eᵢ`-far `u` or for a nearest
   codeword `≠ Enc(f⁽ⁱ⁺¹⁾)` (`positions_bad_le`); hence `W⁽ⁱ⁾`'s message `f⁽ⁱ⁾ := W⁽ⁱ⁾|_{Aᵢ}`
   interpolated row by row (`interp_agree`: unique since `|Aᵢ| ≥ k`) folds to `f⁽ⁱ⁺¹⁾`.
3. `f := f⁽⁰⁾` satisfies the batched claim `f̂(r_f*) = v*` (the fold sumchecks, P1 rounds), hence
   (B′, R not bad) the ring-switched claim and the E claims; `ring_inj` gives `ẑ(r*) = v`; (B not
   bad) each of the ≤ 8 claims; (Z, Lc, Sh, IO, Lr not bad) `z := unpack f` is Boolean (the
   zerocheck's `Sel ⊗ I` rows force `z[k] = (A₀z)[k](B₀z)[k]` with Boolean inputs... Booleanity
   is enforced as in Flock by the product rows for gate positions and by the ring switch's
   `z ∈ GF(2)` packing — `FRRingSwitch.unpack_boolean`), `HHolds`, `ShHolds`, `IOHolds`,
   `LrHolds`, `EHolds`.
4. `node_sound` (§4.3) or `leaf_sound` (§4.1) gives `Rel (acc vk) c w` for `w := readWit z`.
5. `E c π L = some w`: the extractor program computes exactly `readWit (unpack f⁽⁰⁾)` on this
   tape (§6.5, `ext_good_tape`), and `decodeWit_witWords` (contract library) reads it back.

### 5.5 Completeness (`FRCompleteness`)

`P vk c w` (the Lean honest prover, `OProg Proof`): leaf: from `.leaf s n` with `n ∈ {2^16, 2^18}`
(other `n` are not in the image of the native prover; completeness must still hold for every
witness of `Rel`: for other `n ≤ chainCap` and for node witnesses whose children are not of the
three shapes, `P` outputs the **plain witness-sending encoding** `WitnessSending.encode w` and
`V` has a fourth kind `'W'` accepting it exactly as the baseline's `N` branch (the contract's
`acc` on both children, recursive; no query) — this keeps `δ`'s statement for every witness; the
native prover never emits it; its proofs exceed `proofCap` for SNARK children, which is allowed
(completeness is about `V`, not `acc`; baseline D-5). Node: from `.node c₁ c₂ p₁ p₂` with both
children of shape `(kind, shape) ∈ {(L,32),(L,32)}` or `{(L,30)/(N,30)}`: `nodeWitness`, then
the PIOP and Ligerito prover (the Lean prover is slow and never run; it exists for the theorem).

`δ`: no grinding; the honest prover fails only when a challenge is degenerate: `λ ∈ S ∪ Λ`
(`128/2^128`), a zero eq-coordinate in P3 or a Lagrange denominator in a fold (`≤ 2^10 /2^128`
over the run), a ring-switch or E point hitting a pole: `δ ≤ 2^-110`, declared **`2^-100`**
(`complete_le`: `failProb` of the honest run `≤` the sum over the run's squeezes of their
degenerate fractions, by `failProb`'s recursion and exact fiber counts).

### 5.6 Controls (kernel-checked; all `decide +kernel` kept to tiny instances, M §7.1)

For every definition the certificate relies on, one positive and one negative control:

| Definition | Positive | Negative |
|---|---|---|
| F, K fields and twins | `mul_twin_kat` on 8 pairs; `inv_mul` symbolic | a wrong modulus is reducible (`y² + y` has a root) |
| code, `Enc`, `interp_agree` | `Enc` of a message agrees with itself on `S`; interpolation from `k` points returns the message | two distinct messages' codewords differ (distance) |
| `mca_ud_line` | the bound is `< |K|` at every level | the hypothesis `2e < d` is needed: at `2e = d` a two-codeword counterexample |
| `skip_bad_le`, `round_bad_le`, `batch_bad_le`, `shift_sound`, `ring_inj` | SR's controls carried | SR's negatives (`skipDraw_unzeroed_not_rbr` ported) |
| block circuits | `block_complete` on one compression (symbolic via `sim_compressW`), `blake2s_chain` KAT on 2 blocks | `not_holds_flip` |
| `leaf_sound`, `node_sound` | `leaf_complete` at `n = 1`; `node_complete` on two reference-signed children (`Signer.sign`, symbolic `sigOk_sign`) | a flipped output bit of the chain; a child with another key is not accepted (`child_other_key`) |
| `V`, formats | `parse ∘ serialise = id` on the three shapes; `piSize` values; `queries_le` exact counts | `π ± 1` byte rejected with no query; wrong statement rejected; a trace with one answer changed fails `runSeq` of the next query |
| `evalM_eq` | on a 3-row toy IR by `decide` | an entry moved changes the value |
| potential | `empty`; the step inequality at one toy phase | `ε = 2^-121` is not certified (`one_le_of_jump`); `qV − 1` not certified |
| extractor | `ext` on a toy tape of one `k = 2` level halts with the expected words (`decide +kernel`, small) | fuel one less fails; a program outputting `2^24 + 1` words is excluded (library) |

---

## 6. The extractor

### 6.1 What the contract demands (read from `Contract/Extractor.lean`)

`Computes p E fuel := ∀ c π L, π.size ≤ proofCap → (∀ e ∈ L, e.1.size < 2^64) →
(extractorInput c π L).length ≤ 2^64 → ∃ o, p.run (extractorInput c π L) (fuel t) = some o ∧
o.length ≤ outCap ∧ decodeWit o = E c π L`. Nothing constrains `E` itself; `KState.final`
constrains `E` on accepted proofs under good logs. With **B-8**, `E c π L := (ext.run
(extractorInput c π L) (fuel t)).bind decodeWit`:

- `Computes` ⇐ `∀ tape in the domain, ∃ o, ext.run tape (fuel t) = some o ∧ o.length ≤ 2^24`
  (`ext_halts`): termination within fuel and the output cap on **every** tape, no functional
  statement;
- `final` ⇐ on the tapes of §5.4 (`c`, an accepted `π`, a good `L`), `ext.run … = some (witWords
  w)` for the `w` of §5.4 step 4 (`ext_good_tape`), then `decodeWit_witWords`.

`E` is computable (`XProg.run` is), so the badge compiles the `Submission` (gate rule 4).
**Kernel-probe** (`logs/blueprint/probe/B8.lean`, checked against `.contract` at the pin with
`lake env lean`, `B8.log` empty = no errors): `computes_Eof : (∀ tape in the domain, ∃ o, run =
some o ∧ o.length ≤ outCap) → Computes p (Eof p fuel) fuel` typechecks and is proved in three
lines; `fuel_le : 2^46 + 2^12 t ≤ extractorBudget t` by `omega`; `epsR_le : 2⁻¹^120 − 2⁻¹^124 ≤
errorCap` by `tsub_le_self`.

### 6.2 The algorithm (`ext`)

Input tape `⟦c, |π|, π, |L|, L⟧` (words). Memory `mem = 2^26` fixed words (the column store of
level 0: `64 · 2^18` F = `2^25` words, the fold and `Enc` tables, `O(k)` Lagrange weights; **no
`k × k` matrix is ever stored**) `+ 3 · t` words (the log index).

1. **Parse** `|π|` and the header words (kind, shape, variant). If `kind ∉ {L, N, W}` or the size
   is not `piSize`: output nothing (denotes `none`). `W`: copy `|π|/8` words of `π` to the output
   (the library's copy extractor) and halt. `L`: output `0 ‖ s (4 words) ‖ n`; halt.
2. **Index the log** (`N`): for each entry copy `(answer word 0, answer word 1, tape position)`
   into a 3-word table (`3t` memory), merge-sort by `(word 0, word 1)` (bottom-up, `⌈log₂ t⌉ ≤ 64`
   passes, `≤ 2^6 · 2^5 · t` steps), keeping the **first** occurrence on ties (stable sort).
   Lookup of a digest: binary search on two words, then compare the 4 words of the first
   candidate and scan forward while equal to the earliest log position (`≤ 64 + 4·dup` steps; a
   duplicate answer in the log is a collision, already charged, so the scan is bounded by the
   tape: charge `t` once).
3. **Read the ladder bottom-up.** The final message is in `π` (words at a fixed offset); for
   `i = 3, 2, 1, 0`: the cap of level `i` is in `π`; for every position `j < nᵢ`, walk down from
   the cap entry: lookup the digest → the first entry whose answer is it; if its query parses as
   a Merkle-node query of level `i` (tag, length), take the child digest selected by the next
   position bit, else **erasure**; at the leaf level, if the query parses as a column query of
   level `i`, read its `rowsᵢ` elements into the level's column store (`rowsᵢ · nᵢ · 2` words for
   present columns), else erasure. Steps: `Σᵢ nᵢ · depthᵢ · (lookup + parse) ≤ 2^18 · 18 · 2^7 ≈
   2^29.2` at `m = 30`.
4. **Decode level `i`** given `f⁽ⁱ⁺¹⁾` (16 rows × `kᵢ₊₁` F-elements; for `i = 3` the clear final
   message; recombined to a K-row `g⁽ⁱ⁺¹⁾` of `kᵢ/2^{ℓᵢ}`… precisely: the fold target is the
   K-valued row of length `kᵢ` obtained from `f⁽ⁱ⁺¹⁾` by undoing the coordinate split):
   - `Enc(g⁽ⁱ⁺¹⁾)` at every position `j < nᵢ`: barycentric Lagrange from `S` (`kᵢ` K×F products
     per position after a one-time `O(kᵢ)` weight table): `nᵢ kᵢ · 2` F-products = `2^36` at
     `m = 30`, level 0;
   - the K-fold of every present column: `Σ_b eq(s, b) C[b, j]` with the level's fold challenges
     `s` read from the log by the FS chain (the squeeze answers located by lookup from the
     seed; `eq(s, ·)` a `2^{ℓᵢ}`-entry K table): `nᵢ · 2^{ℓᵢ} · 2` F-products = `2^25`;
   - the **agreement set** `A := { j present : fold[j] = Enc(g⁽ⁱ⁺¹⁾)[j] }`, as a position list;
     if `|A| < kᵢ`: output nothing, halt (never on a good tape, §5.4);
   - `P := A[0 … kᵢ)`; the **Lagrange weights**: `W(X) = Π_{p ∈ P}(X − D[p])` by `O(k²)`
     schoolbook, `invW′[p] = 1/W′(D[p])` by Horner and one batch inversion (`O(k²) + 3k`); then
     **for each `s ∈ S`**: `W(D[s])` by Horner (`k`), the `k` inverses `1/(D[s] − D[p])` by one
     batch inversion (`3k`), the weights `M[s,p] = W(D[s]) · invW′[p] / (D[s] − D[p])` (`2k`),
     and **each of the `rowsᵢ` rows** `f⁽ⁱ⁾[r, s] = Σ_p M[s, p] · W⁽ⁱ⁾[r, p]` (`k` products per
     row): per `s` about `(6 + rowsᵢ) k` products, `O(k)` memory; in all `(6 + 64) kᵢ² ≈ 2^40.1`
     F-products at level 0, `m = 30`.
5. **Output** (`N`): `1 ‖ c₁ ‖ c₂` from `π`'s header, then for each child `bytesWords πᵢ ‖
   logWords trᵢ ‖ sigWords σᵢ` read out of `f⁽⁰⁾`'s T and L regions: `trᵢ` is the T bytes
   (the item lengths say where items end), `πᵢ = reassemble shapeᵢ trᵢ` (the same fixed byte
   map as §1.3: copy the absorb payloads, caps, final message, columns and siblings into the
   proof layout; `O(|π|)`), `σᵢ` from L.

The extractor verifies nothing and never evaluates a hash.

### 6.3 Step budget (`m = 30` node; one F-product = 48 statements: three BF64 products of 3
`clmul`/`clmulh` + 4 reduction ops each, Karatsuba adds, loads/stores; a K×F product = 2 F)

| Step | statements |
|---|---|
| memory charge `2^26 + 3t` | `≤ 2^26 + 3t` |
| index (sort) | `≤ 2^11 · t` |
| ladder read (lookups, parsing) | `2^29.2` |
| `Enc(g⁽¹⁾)` at `n₀ = 2^18` positions, `k₀ = 2^17` | `2^36 · 48 = 2^41.6` |
| K-folds of `≤ 2^18` columns | `2^25 · 48 = 2^30.6` |
| Lagrange weights and row interpolation, level 0: `70 · 2^34` products | **`2^40.1 · 48 = 2^45.7`** |
| levels 1–3 (`16` rows, `k ≤ 2^14`) | `≤ 2^39.6` |
| output `≈ 2^19.2` words | `2^21` |
| **total** | **`≈ 2^45.8 + 2^11 · t`**; declared `fuel t = 2^46 + 2^12 · t ≤ 2^48 + 2^16 · t` ✓ |

`m = 31` node (fallback): `2^47.7 + 2^11 t` against `2^48`: 1.2× margin, `fuel t = 2^47.8 + 2^12 t`.
A tape declaring another shape exits in `O(t)`. The program's size: ≈ 4–6 k statements
(`progCap = 2^20`).

### 6.4 The word-machine DSL (`FRXDsl`, B-8, G1)

`XIR`: a first-order language over named registers (`Nat` indices into a fixed register file)
and memory arrays:

```
inductive XIR
  | op (o : XOp) (d a b : Reg) | const (d : Reg) (w : Word) | load | store | input | out
  | seq (p q : XIR)
  | ite (c : Reg) (p q : XIR)
  | for (i : Reg) (bound : Reg) (cap : Nat) (body : XIR)   -- i from 0 to min(bound, cap) − 1
  | mulF (d a b : Reg) | addF | mulK | addK | invF  (macros: fixed statement sequences)
```

with `compile : XIR → XStmt` (the `for` loop as `loop` on a counter register clamped to `cap`
by `ltu`/`and`; macros expand to their `XStmt` sequences), `cost : XIR → (t : Nat) → Nat` (syntactic:
`for` contributes `cap · (cost body + 4) + 3`; a `bound` that is tape-dependent is still charged
at `cap`), and two theorems:

- `compile_runs : ∀ P tape M, ∃ M′ o, Runs tape (compile P) M #[] (cost P t) M′ o ∧ o.size ≤
  outs P` — **every program halts within its syntactic cost, on every tape** (`outs` counts `out`
  statements with the same `for` bound), proved once by induction on `XIR` with the library's
  `runs_seq`, `runs_ite_*`, `runs_loop_step`, `run_of_runs`;
- `compile_sem : ∀ P, Runs … (compile P) … → state′ = semXIR P state` — the compiled program's
  effect is the DSL's reference semantics `semXIR` (a Lean function over `Array Word`), per
  constructor; the field macros' lemmas `mulF_sem : semXIR (mulF d a b) st = st[d := (st[a] *
  st[b] : F)]` through `FRField128.toExt_mul`.

`ext := ⟨2^26, 3, compile extIR⟩`, `ext_halts` from `compile_runs` and `cost extIR t ≤ fuel t`
(by `norm_num` on the syntactic cost), `ext_good_tape` from `compile_sem` and the algorithm's
correctness at the level of `semXIR` (§6.5). No `#eval`, no `macro`, no `elab`: `XIR` is an
ordinary inductive and `compile` an ordinary function; the "macros" are constructors.

### 6.5 The proof plan of `ext_good_tape` (`FRXSpec`)

Lemmas over `semXIR`, each about one phase of §6.2 on a tape `⟦c, π, L⟧` with the §5.4
hypotheses:

1. `index_spec`: after step 2 the table is a permutation of the log entries sorted by answer,
   stable; `lookup_spec`: `lookup d` returns the position of the first entry with answer `d`, or
   the sentinel.
2. `read_spec`: the column store of level `i` holds, at every position `j`, `some (column read
   off L by the §5.4 path)` or `none`; equals `SoundnessLog.colL` (the same first-preimage
   reading that `cap_binding` uses) — so the extractor's word **is** the proof's `W⁽ⁱ⁾`.
3. `enc_spec`, `fold_spec`: the computed `Enc(g)[j]` and folds are the Lean `Enc` and `eq`-fold
   (`FRRS`, `FRMLE`), through `mulF_sem`.
4. `agree_spec`: `A` is the agreement set of §5.4; `|A| ≥ kᵢ` from `ligerito_final`.
5. `interp_spec`: the Lagrange matrix is `Lagrange.interpolate`'s coefficient matrix
   (Mathlib `Lagrange.basis`, `Lagrange.interpolate_eq`), so the rows are `W⁽ⁱ⁾|_A`'s
   interpolants = `f⁽ⁱ⁾` of §5.4 (`interp_agree`).
6. `output_spec`: the emitted words are `witWords (readWit (unpack f⁽⁰⁾))`.

---

## 7. The Lean module plan

Flat modules `lean/FR*.lean`, prefix `FR`, namespace `FR`; `FR.lean` imports all; `Solution.lean`
imports `FR` (the harness builds `Solution`'s closure). Budgets are **code lines** (`loc.py`);
total target **≤ 38 k** (build ≈ 350–380 s, kernel ≈ 220 s on the runner at spartan-srom's mix,
C-calibration: 9–10 s and 5–6 s per kLoC; hard cap 45 k). `decide +kernel` controls are kept
to toy instances (M §7.1: 40 s per kLoC on a runner). Columns: **R** reused from spartan-srom as
is (renamed), **A** adapted, **N** new. Tracks (PLAN §3) and parallelism: modules in the same
track are sequential; tracks are parallel once `FRFieldBase`/`FRField128` (L-field) and `FRVIR`
(the IR, L-circ's first module) exist, which everything else imports.

| Module | Track | Content | Lines | Class | Depends on |
|---|---|---|---|---|---|
| `FRFieldBase`, `FRFieldBaseCorrect` | L-field | BF64 twin (`clmul32` Karatsuba, reduce, inverse), `ringEquivBF64` | 100 + 820 | R | — |
| `FRField128` | L-field | F as `Ext ⟨BF64, y²+y+β⟩`, `Tr β = 1` (kernel), irreducibility, fast twin, `toExt_mul`, inverse | 700 | N (pattern SR `FieldExtCorrect`) | FieldBase |
| `FRField256` | L-field | K likewise over F; `K = F ⊕ F·u`; coordinate split | 500 | N | Field128 |
| `FRFieldControls` | L-field | KATs (8 pairs), negatives | 100 | A | |
| `FRMLE`, `FRMLEControls` | L-piop | eq, MLE, tables | 260 + 50 | R | Field128 |
| `FRSumcheck` | L-piop | rounds, batching, degree-3 rounds | 350 | A | MLE |
| `FRSkip` | L-piop | univariate skip: `S_skip`, Λ, `pPoly`, `skip_bad_le` (LV `Flock/Tables` algebra ported to `Vector F`), pinned coordinates certificate | 600 | N (LV) | Sumcheck |
| `FRShift` | L-piop | shift MLE, `shift_sound` | 250 | N | MLE |
| `FRRingSwitch` | L-piop | `ring_inj` for GF(2) ⊂ F (128 limbs), `unpack_boolean`, MBP evaluation = `B̂` | 600 | A | Field128 |
| `FRSpartan` | L-piop | zerocheck + lincheck soundness for `Sel ⊗ (A₀,B₀,I)` and for sparse `(A,B,C)` over F (SR `SoundnessSpartan`) | 400 | A | Sumcheck |
| `FRRS` | L-pcs | `D`, `S`, `Enc`, distance, `interp_agree`, barycentric weights | 450 | A (SR `RS`) | Field128 |
| `FRProximity` | L-pcs | `close_unique`, `bw_unique`, `mca_ud_line`, `fold_preserves`, `positions_bad_le` | 1,500 | N (+ SR) | RS |
| `FROracle`, `FRQueries` | L-cert | `OProg` monad view, `AtMost` | 170 + 70 | R | — |
| `FRTranscript` | L-cert | seed/absorb/squeeze with tags, `chF`, `chK`, indices; fiber counts | 400 | A | Oracle, Field256 |
| `FRMerkle` | L-cert | binary tree with caps, `cap_binding`, `colL`, `colL_prefix` | 700 | A | Transcript |
| `FRLog` | L-cert | the forest, `Matches` for the new kinds, `bad_step_le` (32-byte labels), `extCount_split` | 750 | A | Merkle |
| `FRBlake2sCircuit`, `FRBlake2sWords`, `FRBlake2sCompress` | L-circ | leanerVM's circuit, `blake2s_sound` | 1,550 | R | — |
| `FRBlake2sGeneric`, `FRBlake2sWalk`, `FRBlake2sWitness` | L-circ | gadget simulation, `walk_eq_sum`, traces | 730 | R | |
| `FRBlockLayout` | L-circ | the re-based block layout (slots), `A₀, B₀` rows, `one` | 300 | A (SR `Blake2sR1CS`) | Circuit |
| `FRBlockChain` | L-circ | the chain block (constants), `block_sound/complete` | 350 | A | BlockLayout |
| `FRBlockStream` | L-circ | the stream block, `block_sound`, `blake2s_chain` (traceDigest as a chain) | 600 | N | BlockLayout |
| `FRLeafCircuit` | L-circ | `leaf_sound`, `leaf_complete`, `leafWitness` | 1,300 | A (SR `Chain*`) | BlockChain, Shift |
| `FRVIR` | L-circ | `VProg` ops, `runIR` (OProg), `semIR` (pure), `gen` per `(kind, shape, variant)`, query sequence, counts | 900 | N | Transcript, Field256 |
| `FRVIRCircuit` | L-circ | `compile : VProg → rows`, templates, `evalM`, `evalM_eq`, `eq_incr`, `tpl_mle`, `shift_mle`, `compile_sound` | 1,800 | N | VIR, Spartan, Walk |
| `FRWots` | L-circ | WOTS as IR + blocks, `wots_sound` | 600 | N | VIRCircuit, BlockStream |
| `FRNodeCircuit` | L-circ | `nodeLayout` (bases, the `≤ 2^16` decide), regions, `readSigned`, `node_sound`, `node_complete`, `nodeWitness` | 1,600 | N | Wots, LeafCircuit |
| `FRFormat` | L-cert | `hdr`, `piSize`, `parse`, `reassemble`, byte readers (`get!`-based), `W` encoding (library) | 500 | N (+ SR `NodeBytes`) | — |
| `FRVerifier` | L-cert | `V`, `runSeq_eq_runIR`, `queries_le`, the `W` branches (SR `Node` `C`/`N`) | 900 | N/A | VIR, Format |
| `FRProver` | L-cert | the Lean honest prover (PIOP + Ligerito), `P` | 900 | N | Verifier |
| `FRSoundnessDefs` | L-cert | phases, doom predicates, `φ`, `μ` (SR Part A) | 800 | A | Log, Proximity |
| `FRSoundnessStep` | L-cert | one lemma per row of §5.2 + `muG_step` instantiation | 2,000 | A/N | SoundnessDefs, Skip, Spartan, RingSwitch |
| `FRSoundnessLigerito` | L-cert | `ligerito_final` (the per-level induction) | 900 | N | Proximity, Merkle |
| `FRSoundnessFinal` | L-cert | `runLog_chain`, `final` (§5.4), uses `leaf_sound`, `node_sound` | 1,300 | A/N | all above |
| `FRKState`, `FRCompleteness` | L-cert | `kstate vk`, `complete_le`, `δ` | 200 + 800 | A/N | |
| `FRXDsl` | L-ext | `XIR`, `compile`, `cost`, `compile_runs`, `compile_sem` | 1,200 | N | Library.Machine |
| `FRXField` | L-ext | `mulF`/`mulK`/`invF` macros and `*_sem` | 700 | N | XDsl, Field256 |
| `FRXLog`, `FRXDecode`, `FRXProg` | L-ext | index/sort/lookup; ladder read, folds, agreement, Lagrange rows; `extIR`, `ext`, `fuel`, `cost_le` | 900 + 1,500 + 500 | N | XField |
| `FRXComputes`, `FRXSpec` | L-ext | `ext_halts`, `computes`; `ext_good_tape` (§6.5) | 500 + 1,300 | N | XProg, SoundnessLigerito |
| `FRSubmission`, `FRFinal`, `FRControls`, `FR`, `Solution` | L-cert | `submission`, `acc_eq`, `certificate`, `certificateR_of`; controls of §5.6 | 300 + 50 + 1,200 + 70 + 40 | N/A | all |
| **total** | | | **≈ 37.5 k** | | |

Build-time risks: `FRProximity` and `FRVIRCircuit` are the two research-grade modules (§9); the
copied BLAKE2s circuit modules are the heaviest known quantities (1.5 k lines, ≈ 30 s kernel on
the VM in spartan-srom). The claim file: `{"error": "<εR as a/b>", "completeness_error":
"1/2^100", "qV": 8192, "fuel_base": 70368744177664, "fuel_per_word": 4096}`.

---

## 8. The prover plan (track P; std Rust → `prover/prover.s`; B-9)

### 8.1 Structure

`prover/` as spartan-srom's: `main.rs` (modes `setup`, `tree`, `leaf`, `node`, development
modes), `service.rs` (reused), `format.rs` (FORMAT.md, `witWords`, `reassemble`), `acc.rs` (a
native `acc` mirroring `V`: the IR interpreter in Rust over the same generated program),
`field.rs` (BF64/F/K with CPUID dispatch), `ntt.rs` (additive NTT over F on the subspace
basis of §2.1), `blake2s.rs` (reused), `circuit.rs` (leanerVM's block, reused; re-based layout),
`ir.rs` (the `VProg` generator, line for line the Lean `gen`, checked by a KAT: the Lean
`gen` dumped for the three shapes equals the Rust generator's output), `witness.rs` (leaf and node
witness generation), `zerocheck.rs` (skip round, degree-3 rounds), `lincheck.rs`,
`ringswitch.rs`, `ligerito.rs`, `par.rs` (reused pool). No dependency; `build-asm.sh` and
`sanitize-asm.py` reused; `-C target-cpu=x86-64-v2`.

### 8.2 CPU tiers (dispatch once at start, `is_x86_feature_detected!`)

| Tier | Features | Kernels |
|---|---|---|
| 0 | AVX-512 + VPCLMULQDQ (+ GFNI): the Xeon 8573C, EPYC 9V74, 9V45 | the ymm kernels widened to zmm for the dominant kernels (K §1); optional, every cap is met on tier 1 |
| 1 | **AVX2 + VPCLMULQDQ-256 + PCLMULQDQ: the EPYC 7763, the slowest model seen and the tier of record** (K §0, **measured**) | K's probe kernels (`probe/kernels/`): ymm F products (Karatsuba over 64-bit limbs), NTT butterflies, fold/MAC, the skip round's byte kernels and transposes, `s_hat_v` |
| 2 | portable (no clmul; this VM) | shift-and-xor, for development only |

The tower field of B-4 and K's GHASH kernels differ only in the reduction step (`y² = y + β` on
two 64-bit limbs against `x^128 + x^7 + x^2 + x + 1`): the limb products are the same `vpclmulqdq`
sequence, so K's measurements carry over (**estimate**: ± 5 %).

The skip round (zerocheck round 1 over `2^m` bits) is bit-sliced GF(2)/GF(2^8) work as in Flock's
`univariate_skip_optimized` (AVX2 `vpshufb` nibble tables for the F₂₅₆-subfield products); it is
the prover's hottest kernel (Flock: "≈ 85 % of round 1 was the transpose on x86").

### 8.3 Memory plan (the `m = 32` leaf, the largest; 11 GiB cgroup; **estimate**)

| Live data | bytes |
|---|---|
| bit witness `2^32` bits (the 2^18 compressions' traces, written per block) | 512 MiB |
| packed `f` (`2^25` F) | 512 MiB |
| level-0 codeword (`64 × 2^20` F) and its Merkle layers | 1 GiB + 64 MiB |
| after the skip round: three tables over `2^26` points in F (`Az`, `Bz`, `z` folded by `λ`); `eq(r, ·)` in two halves (`2 × 2^13`) | 3 GiB (halving each round) |
| lincheck, ring switch (streaming over `f`), levels 1–3 words | < 128 MiB |
| **peak** (during zerocheck rounds 2–3) | **≈ 5.2 GiB** (upper bound; K's pipeline, with one pre-faulted arena of `7 · 2^29` B, **measured 3.81 GB** at `m = 32`, 1.91 GB at `m = 31`, 0.96 GB at `m = 30`, K §4.4) |

The bit witness is freed after the skip round (the lincheck needs only `2^14`-sized tables); the
`Az`/`Bz` tables are computed in the skip round pass from the bits (Flock's round-1 structure).
P adopts K's arena layout (one arena reused across the tree's leaves, K §5.2). Node prover:
`m = 30`, ≈ 1 GB. Two leaves are never proved at once in the tree run, nodes may be.

### 8.4 Time plan (season, EPYC 7763, 4 vCPU; **measured** by K's probe on real runners, K §3–§4)

| Item | 7763 | basis |
|---|---|---|
| `m = 32` leaf compute | 3.73–3.86 s (14.2–14.7 µs per compression) | **measured**, K §3; round 1 (skip) 31 %, ring switching 23 %, NTT 17 % |
| per leaf with the service's Merkle hashing (≈ 85 compressions per statement compression at 16.6 ns), transfer and extras | 4.24–4.58 s | K §4.1 (a)–(c), **estimate** on measured inputs |
| node compute (`m = 30`, 43 k useful compressions) + extras | 0.94–1.10 s | **measured** 0.81–0.83 s + K (d) |
| **tree** `64 × leaf + 63 × node + arena` | **≈ 330–365 s against 600 s** (1.65–1.8×) | K §4.2 |
| stream leaf `m = 30` (compute 0.97–1.01 s, start-up, arena 0.04–0.14 s, service) | 1.14–1.42 s | K §4.3 |
| stream node merge | 0.98–1.29 s | K §4.3 |
| **stream link** | **≈ 2.1–2.7 s against ≈ 3.1 s: the binding cap, ≥ 13 % margin** | K §4.3 |
| `m = 31` node (the B-2 fallback) | ≈ 1.9 s ⇒ link 3.1–3.4 s: **over** | K §0 (2) |

On the AVX-512 runners every figure is lower (tree ≈ 215–340 s, link 1.5–2.5 s). **Consequences
for P** (K §5): size every budget on the 7763; the node circuit stays at `m = 30` and lean (§4.5's
tightening applied, the M-region zerocheck ≤ 2^18 rows); the stream margin is widened by
implementation only: the round-1 GF(2^8) products in a GF(16)² tower basis via `vpshufb` (−20 to
−35 % of round 1, **estimate**), a transposed SIMD `s_hat_v`, 8-lane AVX2 BLAKE2s for the
witness. The next measurement (P1) is a real leaf with the service in the loop, replacing K's
estimates (a)–(c).

### 8.5 Setup and per-request start-up

`prover setup` writes to `/setup`: the generated `VProg` and the element-R1CS template tables for
LL and NN (a few MB), the NTT twiddles for `m ∈ {30, 32}`, the subspace bases. A `leaf`/`node`
process loads them before `ready` (< 100 ms). No circuit construction is on the clock (F (5)).

### 8.6 Correctness checks of the prover (not certified; required by H)

- the Rust IR generator equals the Lean `gen` (dump KAT per shape);
- the native `acc` accepts every proof the prover writes, and the Lean `acc` (badge) does too, on
  the smoke shape and on one `m = 32` leaf and one LL node and one NN node (H3);
- the Lean `P` and the native prover produce byte-identical `π` on a toy shape? **Not required**:
  the Lean `P` is never run at these sizes; instead `V`'s controls include the native prover's
  smoke proofs as KATs only if they stay under the kernel budget (they do not: a 630 KiB proof's
  `V` is not kernel-evaluable; the badge-side check (compiled `acc`) is the test).

---

## 9. Stages, definitions of done, risks

Each stage follows the repository's cycle (implement → review ∥ golf → fix → commit) and writes
`docs/v4/flock-recursive/stages/<stage>-RESULT.md`.

| Stage | Track | Done when |
|---|---|---|
| **S-A field** | L-field | `FRField128`, `FRField256` build; `Field` instances; twins proved; KATs; `Tr β = Tr α = 1` kernel-checked; measured compiled product time on the VM in `logs/` |
| **S-B IR** | L-circ | `FRVIR.gen` for the three shapes; `runIR` and `semIR`; query counts by `decide`; the Rust generator KAT |
| **S-C piop** | L-piop | `FRSkip`, `FRShift`, `FRRingSwitch`, `FRSpartan` with every row of §5.2 marked Z, L, S, I, Lr, B, R, E as a lemma |
| **S-D pcs** | L-pcs | `mca_ud_line`, `fold_preserves`, `positions_bad_le`, `FRMerkle.cap_binding` |
| **S-E circuits** | L-circ | `FRBlockStream`, `FRLeafCircuit.leaf_sound`, `FRVIRCircuit.compile_sound` + `evalM_eq`, `FRWots`, `FRNodeCircuit.node_sound`; `nodeLayout`'s `≤ 2^16` by `decide` (B-2's kill test) |
| **S-F verifier** | L-cert | `V`, `P`, `queries_le`, formats, controls of §5.6's `V` rows |
| **S-G soundness** | L-cert | `FRSoundnessStep` (every row), `FRSoundnessLigerito`, `FRSoundnessFinal`, `kstate vk`, `complete_le` |
| **S-H extractor** | L-ext | `FRXDsl` theorems; `ext`, `computes`, `ext_good_tape`; the toy-tape KAT |
| **S-I certificate** | L-cert | `FRFinal.certificate`, `Solution.certified`; axioms three; build and kernel times on the VM in `logs/` (≤ 400 s / ≤ 400 s VM ⇒ runner margin) |
| **P1 prover core** | P | tier-1 and tier-2 kernels; leaf proving at `m = 30, 32` against the native `acc`; probe on a runner with measured c/s and peak RSS |
| **P2 prover tree/stream** | P | `tree`, `leaf`, `node` modes through the service; `prover.s` assembles with binutils 2.42 |
| **H1 … H3** | H | compiled `acc` time on an NN root in the badge process; smoke `HARNESS: ACCEPT`; season evaluation on GitHub (`eval-push.yml`) |

Risks and kill tests (FR-R1 … R6 of `PLAN.md` refined):

| Id | Risk | Kill test | Fallback |
|---|---|---|---|
| FR-R2′ | a §5.2 row's lemma is weaker than the table | the row's lemma states the exact count; S-C/S-D review | more queries (the only rows near the cap are P2 and Z2; Z2 is `k_s = 6` and fixed) |
| FR-R3′ | `node_sound`'s assembly exceeds the budget or L-circ cannot close `compile_sound` | S-E's mid-point: `compile_sound` for the arithmetic ops alone within 1,000 lines | restrict the IR (fewer op kinds, more rows) |
| FR-R4′ | the certificate exceeds 600 s build or kernel | S-I's VM measurement × 1/1.3 (C: the runner is faster) must be ≤ 400 s; per-module kernel seconds logged | split heavy modules; remove kernel KATs; golf |
| FR-R5 | prover throughput (§8.4) | **closed by K** (feasible on the 7763 with the ymm tier: tree 330–365 s, link 2.1–2.7 s); residual: the link's 13 % margin, re-measured in P1 with the service in the loop | widen the margin by K §5.3's kernel changes; if the link still misses, deliver the ACCEPTed shape + obstruction (FR-D2) |
| FR-R7 | `m = 30` node overflows (`nodeLayout`) | S-E `decide` | `m = 31` (§6.3: `fuel = 2^47.8 + …`, 1.2× margin) |
| FR-R8 | `mca_ud_line`'s linear algebra over `RatFunc K` does not close | S-D mid-point: steps 1–2 of §5.3 as lemmas | restrict to the line-coefficient-free statement with a weaker constant (`(e+1)·n²`, still `2^-197` over K) |
| FR-R9 | T_V over 205.9 ms on the root | H1 | pad fewer templates irregularly; hand-specialise the interpreter for the hot ops |
| FR-R6 | V4-A10 lands (textbook KS) | re-pin in its own commit; `FRKState` is the only module touched | — |
