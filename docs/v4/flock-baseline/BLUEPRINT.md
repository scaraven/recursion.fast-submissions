# The v4 Flock baseline: entry blueprint (`submissions/spartan-srom/`)

Status: normative for stages F1 (Lean) and F2 (native prover) of the baseline, 2026-10-22. Written
by the baseline orchestrator from the route analysis (`reviews/F0-route-ideation.md`) and the
probes (`stages/F0-probes-RESULT.md`). Where this file and the core contract disagree, the
contract wins and the disagreement is reported. Ids: `D-n` decisions of this entry, `V4-n`/`V4-An`
the core's (`.contract/docs/v4/BRIEF.md`), `C-Mn`/`C-mn` the design attack.

## 0. Decisions

| Id | Decision | Reason |
|---|---|---|
| D-1 | **Route (b)**: port the v3 honest entry `spartan-chain` (Spartan R1CS sumchecks over GF(2^64)/GF(2^192), ring switching, Ligero with unique-decoding proximity; 61 modules, KS kernel-checked against the v3 contract) to the v4 contract, with a Flock-style native prover. Route (c) (leanVM's BLAKE2s Flock port as a prover-only study) follows only if budget remains. | The only route that is **certified** and exercises the ranked path end to end (C-m10). Flock's own protocol needs Ligerito/WHIR proximity theorems in Lean (research-scale) and, as published, GF(2^128), whose sumcheck rounds cannot meet `errorCap = 2^-128` per query. The pins are identical to v3's, so about 13–14k of the 16.8k lines carry over. |
| D-2 | **Nodes are σ0-bundles** (§1.4): a node proof carries its whole subtree as a *clear* witness whose every child slot is signed by one signature `σ0` on the **empty** trace, followed by the leaves' SNARKs, which the node verifier checks with fresh queries. | Plain v4 witness-sending dies at the first node: a signed child is `π ‖ trace ‖ σ`, and the trace restates every byte the verifier hashed, so a level-1 node of two `n = 16` leaves is about 1.2 MB > `proofCap` (route analysis, point 1). Under the bundle the extractor is the library's unmodified copy extractor and only the leaves' SNARKs count against `proofCap`. |
| D-3 | Root name `spartan-srom`; Lean module prefix and namespace `SpartanSrom` (v3's `SpartanChain` renamed). | Fresh module names (submissions layout rule 4); says what it is (spartan-chain under the signed random oracle). |
| D-4 | The native prover is **std Rust** (the v3 crate, dependency-free), emitted as one `prover/prover.s` by fat LTO, one codegen unit, `panic=abort`, `-C llvm-args=-align-all-functions=4`, a pinned baseline target CPU (`x86-64-v2`) with run-time dispatch (`is_x86_feature_detected!`) for AVX2 and `pclmulqdq`, and a sanitising filter (`stages/F0-probes-RESULT.md` §1). The Rust source, `build-asm.sh`, the filter and the generated `.s` are all committed. | Measured to work through the harness's own sandboxed build; deterministic; byte-identical proofs to the cargo build. A C or `no_std` port would cost the whole prover for nothing. |
| D-5 | The Lean honest prover `P` sends node witnesses plainly (§3); only the native prover emits bundles. | Completeness quantifies over every witness of `Rel`; `P` has no signer, so it cannot make `σ0`. `V` does not check `proofCap` on its own input, so `P`'s large node proofs are still accepted (completeness is about `V`, not `acc`). |

## 1. Proof formats (bytes of `π`; normative)

All integers little-endian. `encode w` is the library's `WitnessSending.encode` (the bytes of
`witWords w`, `.contract/RecursionFast/Library/WitnessSending.lean`), so `WitnessSending.decode`
(= `decodeWit (packBytes π)`, which **ignores trailing words**) reads every format below.

### 1.1 SNARK leaf (`L`), unchanged from v3 (BLUEPRINT-R1 §7)

`enc64 0 ‖ s ‖ enc64 n ‖ h ‖ π_S`, exactly `leafSize n` bytes (`80` for `n = 0`, then `h = s` and
no SNARK). The first 48 bytes are `encode (.leaf s n)`. `π_S` is v3's SNARK of `chainEnd s n = h`,
its queries in v3's formats (Merkle leaf `0x00 ‖ column`, node `0x01 ‖ λₗ ‖ λᵣ`, seed
`0x10 ‖ s ‖ enc64 n ‖ h`, absorb `0x20 ‖ st ‖ kind ‖ msg`, squeeze `0x30 ‖ st`). v3's oracle
prefixed every query with `0x52` internally; under v4 the query bytes go to the service as they
are (no prefix), so the SNARK's byte layout and query formats do not change.

### 1.2 Clear leaf (`C`), new

Exactly `encode (.leaf s n)`: 48 bytes. No SNARK; `V` recomputes the chain.

### 1.3 Plain node (`N`), new

Exactly `encode (.node c₁ c₂ p₁ p₂)`, children arbitrary signed proofs.

### 1.4 Bundle (`B`), new

`encode W ‖ T` with `T` non-empty, where:

- `W = .node c₁ c₂ p₁ p₂` is a **clear tree**: every signed proof `p` inside `W` (at any depth)
  has an **empty trace** and the **same signature** `σ0` (equal as a `Sig`), and its proof `p.π`
  is either a clear leaf (`C`) or a plain node (`N`) whose two children are again clear-tree slots.
- `T` is the concatenation, over the clear leaves of `W` in left-to-right order (depth first, child
  1 before child 2), of `h_j ‖ π_S,j` with `|π_S,j| = leafSize n_j − 80`; every bundled leaf has
  `n_j ≥ 1`.

The extracted witness of a bundle is `W` itself (`decode` stops before `T`).

## 2. The verifier `V vk c π` (branch by branch; normative semantics)

Decide the branch from `π` before any query:

1. **`L`** (tag word 0, `|π| > 48`): v3's `leafProg` unchanged: header (`n ≤ chainCap`,
   `|π| = leafSize n`, `c = leafStmt h n`), then `h = s` if `n = 0`, else the SNARK verifier
   `snarkProg` with oracle queries.
2. **`C`** (tag word 0, `|π| = 48`): `ret (n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n)`; no
   query. Use the library's fast twins (`chainEndF`, `leafStmtF`, `Library/Fast.lean`), proved
   equal to the specification.
3. **`N`** (`decode π = some (.node c₁ c₂ p₁ p₂)` and `encode … = π` exactly): `ret (c = nodeStmt
   c₁ c₂ ∧ acc' vk c₁ p₁ ∧ acc' vk c₂ p₂)`, where `acc'` is the submission's own `acc` unfolded
   (proof within `proofCap`, every query within `queryCap`, `SigOk vk (traceDigest p.tr) p.σ`,
   `(V vk cᵢ pᵢ.π).runSeq pᵢ.tr = some true`), recursive on the proof size. No query of its own.
4. **`B`** (`decode π = some W`, `W` a node, `encode W` a strict prefix of `π`): with no query
   first, check: `c = nodeStmt c₁ c₂` at the top; `W` is a clear tree (every slot: empty trace,
   signature equal to slot 1's `σ0`, proof within `proofCap`, proof `C` or `N`, internal
   statements `nodeStmt` of their children, each clear leaf's statement digest is the slot's
   statement); `SigOk vk (traceDigest []) σ0` **once**; `|T| = Σ_j (32 + leafSize n_j − 80)`
   exactly; every `1 ≤ n_j ≤ chainCap`; **`Σ_j qBound (kap n_j) ≤ 2^16`** (`qBound` is v3's exact
   per-leaf query bound, `SpartanChainVerifier.qBound`). Then, for each bundled leaf `j` in order:
   `c_leaf,j = leafStmt h_j n_j` and run `snarkProg s_j n_j h_j π_S,j` with fresh queries. Accept
   iff everything holds.
5. Anything else: `ret false`.

`V` asks at most `qV = 2^16` queries on every input (branch 1: `qBound ≤ 2^14`; 2, 3: none; 4: the
static check). The trace of a bundle is the concatenation of its leaves' SNARK traces in `T`'s
order.

## 3. The Lean honest prover `P vk c w`

- `.leaf s n`: v3's (`n = 0`: the 80-byte header; else `proveSnark`), with `h = chainEnd s n`.
- `.node c₁ c₂ p₁ p₂`: `encode w` (format `N`), no query.

Completeness at `δ = 0` (v3's perfect completeness for every oracle, through the library's
`complete_withError_zero`), for every `vk`.

## 4. The extractor

The library's `WitnessSending.E` (`decode π`), `ext`, `fuel` and `computes`, unchanged. Leaf
proofs (`L`, `C`) decode to `.leaf s n`; `N` and `B` to their node witness.

## 5. The certificate

- **KS** for every `vk`, `ε = 2^-129` (v3's), `qV = 2^16`, with v3's potential `μ` (it is defined
  on logs; the statement and proof are quantified only in `final`). `final` per branch: `L` as v3
  (`mu_final_leaf_closed`); `C` and `N` by their definitions (they decide `Rel`); `B`: the bundle's
  run on the log accepts ⇒ each `snarkProg` accepts on the log ⇒ (μ L < 1) `chainEnd s_j n_j = h_j`
  for every bundled leaf ⇒ every clear slot of `W` is accepted by `acc vk` (by induction on the
  clear tree: zero queries, empty trace, `SigOk` on `σ0` checked, `C`'s recomputation true) ⇒
  `Rel (acc vk) c W`. `SigOk` on `σ0` is checked so that the extracted witness is in `Rel`, not
  for soundness, and it holds for every key the adversary picks, so C-m1's impossibility does not
  apply.
- **Completeness** §3. **Computes**: the library's. **Caps**: `ε = 2^-129 ≤ errorCap`, `δ = 0`,
  `qV = 2^16`, the library's fuel and program.
- **Layout** (stage B's `harness/evaluate.py`): `claim.json` (keys `error`, `completeness_error`
  as `"a/b"` strings, `qV`, `fuel_base`, `fuel_per_word` as integers; here `"1/2^129"` written out,
  `"0"`, `65536`, `0`, `8`), the Lean sources flat in `lean/` (module `Foo` is `lean/Foo.lean`),
  `lean/Solution.lean` defining `RecursionFast.Challenge.submission` and proving
  `RecursionFast.Challenge.certified : CertificateR declared submission` against the challenge
  rendered from `claim.json`; `prover/*.s` and the prover's source beside it.

## 6. Controls (positive and negative, kernel-checked; no hash evaluated beyond a few)

v3's controls carried over (field, circuit, MLE, RS, Ligero, transcript known-answer tests,
canaries of the leaf branch, `qV − 1` and `ε = 2^-130` negative claims), plus:

- format: `C`, `N`, `B` decode to the witnesses of §1 (`decode` of a bundle stops at `W`);
- bundle negatives: a slot with a non-empty trace; two slots with different signatures; `|T|` off
  by one byte; `Σ qBound > 2^16` (rejected with no query: `V … = ret false`); a bundled leaf with
  `n = 0`; a clear leaf with `n > chainCap`;
- canaries: one byte appended to or removed from `C`, `N`, `B` proofs is rejected;
- positive: a clear tree with `σ0 = Signer.sign …` is accepted by `acc` under `Signer.pk …`
  (symbolic, from the library's `sigOk_sign`), so the bundle branch's conclusion is satisfiable.

## 7. The native prover (normative behaviour; source and assembly in `prover/`)

Interface: the core's `harness/PROVER.md` and `harness/FORMAT.md`; the oracle through
`service/PROTOCOL.md` (every Merkle and Fiat–Shamir hash is a `QUERY`; one `SIGN` per output).

- `setup`: precompute whatever is key-independent (circuit tables), optional.
- `tree`: for each leaf, compute `h = chainEnd s n` natively, prove `π_S` (queries via the
  service), record the verifier's query sequence with its answers (replay the native verifier on
  the prover's answer table), `SIGN` it → `L<i>.bin`. `SIGN []` once → `σ0`. Every inner node
  `N<l>_<j>` and `root.bin` is the bundle of its subtree's leaves (§1.4), its trace the
  concatenation of those leaves' traces in order, one `SIGN` each.
- `leaf`: one `L` leaf proof.
- `node` (child 1: `L` or `B`; child 2: `L`): the bundle `W = node(c₁, c₂, slot(clear child 1),
  slot(clear child 2))`, `clear(L) = C` from its header's `(s, n)`, `clear(B) = encode W_child`;
  `T = T(child 1) ‖ (h ‖ π_S)(child 2)`; trace = trace(child 1) ‖ trace(child 2) (no `QUERY`);
  `σ0` from child 1's `W` or `SIGN []`; one `SIGN`.
- Output proofs must be accepted by the compiled `acc`; the leaf SNARK bytes must equal the Lean
  `P`'s (known-answer test at small `n`, as v3's `kat.py`).

## 8. Measurements the feedback report needs (each with its log)

Leaf proof bytes, trace bytes and signed-file bytes vs `n`; prover time with in-process hashing vs
through the service (and the service's calls/s); `acc` time of the compiled Lean verifier per
proof kind; smoke tree and stream end to end through the harness; at the season shape: where it
fails (leaf `proofCap` at `n_f = 2^16`, the tree), with the harness's own message; the number of
stream links completed at each `n_f`; the assembly build (size, link time, what failed on the way).
