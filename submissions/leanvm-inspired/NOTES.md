# leanvm-inspired

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #7

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, a logup bus,
ring switching and stacked WHIR. It is reshaped for the contract in three ways: unique decoding of the extracted commitment `C_rec`, a
hash-chain transcript over the signed oracle, and an in-circuit verifier written as loop tables
instead of a VM guest. From #7 it takes the core library's `WitnessSending` relation, unchanged: that
relation is the right leaf of every node and the completeness route.

Notation:
- `K = GF(2^64)` (`x^64+x^4+x^3+x+1`, CompPoly `BF64`) and `E = K[y]/(y^3+y+1)` (CompPoly `BF64.Ext3`);
  `g = x` generates `K^×`.
- `Ex` is the extractor; UD means unique decoding.
- P20 is the production parameter set and P8 the test set.
- v1 is the design of pr11-983bdcfa21d6 (chain table `CH` with committed `in`, `mid`, `Y`; `C_main` 2^26).
- [e] marks an estimate.

## Changes since pr11-9e756ce6880a

pr11-9e756ce6880a (the digest-only tape) measured locally S = 6.26 (P̄ 3.70, V̄ 2.56), S× = 3.94, mean `V` 268.6 ms,
|π| 1,094,248 B. This version changes the two WHIR openings only: grinding on every level, and `C_main` opened at
the Johnson radius with OOD samples. The chain tape, `KS`, the bus, LoopIR, the accumulator, `C_rec`'s code, the
extractor's algorithm, the claim and the theorem's statement are unchanged.

- **Grinding, g = 14, on every WHIR level** (`C_main`'s three, `C_rec`'s one). After a level's cap (or its final
  scalars) `V` draws one separator sample and discards it, reads a nonce (one `E` scalar, 24 B), then draws the
  PoW challenge `c` and requires `eToNat c < 2^(192−g)`, that is, lane 2 of the answer `< 2^50`. The positions
  come from the challenges after `c`.
  - *Soundness accounting.* The nonce is a prover move (`read`), so the query `st ‖ nonce` opens a move-free group:
    the PoW challenge, the positions, `λ` and the openings. The FS compiler's potential (`kstate_of_kcert`,
    `LvmPotential`) charges a group once, at the fresh query that opens it, and every later query of the group is
    a continuation. So each nonce attempt is one fresh query, charged the group's escape once, and that escape is
    `2^-g·eQuery` (`escRet_powCheck_le`: `2^(192−g)` passing challenges, and the positions are drawn after `c`
    inside the same group). No `grind` node is used, so `NoGrind` still holds and the compiler is unchanged. The
    separator makes every attempt a full oracle query (`st ‖ nonce`, 56 B) with no midstate over the cap.
  - *Circuit.* A `BITS` class `powSpec` (one row per opening) reads lane 2 of each PoW answer as a `(64 − g)`-bit
    field, and `powG` asserts the lane equals it (`pw20`, `powOKR_of`).
  - *Prover.* A multithreaded nonce search: 12–35 ms per P20 proof (2^14 expected attempts per level).
  - `C_rec`'s one UD level drops from 191 to 170 queries.
- **`C_main` at the Johnson radius, with OOD (J1).** Folds 6/4/4 and rates 1/2, 1/4, 1/8 as before; **230/115/77
  queries** (were 311/191/156). Levels 0 and 1 send an OOD sample after the next cap: a point `z ∈ E^κ`, the answer
  `y` and the intro polynomial; the final weight takes the claim `(λ, eq(z, ·))` before `(λ², W)` (leanVM's
  order). `C_rec` stays in unique decoding, so `Ex`, which decodes only `C_rec`, is unchanged.
  - *The list-decoding bound.* `codeFacts_johnson` (`LvmMcaJohnson`) gives each Johnson level's code facts from two
    proved theorems:
    - Haböck's strong mutual correlated agreement at the Johnson radius (`strong_mutual_johnson`): for `2 ≤ k`,
      `0 < η ≤ 1/4`, `ηn ≥ 1` and `(k − 1)·n ≤ (A − 4ηn)²`, fewer than `johnsonThreshold k n (n − A) η` fold
      challenges admit a proximate word that the pair's codewords do not explain;
    - the interleaved Johnson list bound (`card_le_listBound`): within `E = n − A` column errors of a linear code
      of distance `d` (`d = n − k + 1` for RS, `rsCode_minDist`) lie at most `⌊n(d − E)/(nd − 2nE + E²)⌋`
      codewords.
    - The per-level constants (`A`, `L`, `M`, slack `η`) are `norm_num` facts (`LvmWhirCodeJ`); the lists have
      at most 98, 390 and 646 members (level 0: `candidates_main24J_ncard_le`).
    - leanVM's OOD and list-to-one WHIR steps (its `Whir/Sound`, re-ported with OOD in `LvmWhirOod`,
      `LvmWhirEscapeJ`, `LvmWhirProgJ`, `LvmWhirSpecJ`) carry the bound into the opening. With `ood = false` the
      new program is the UD one (`verifyStackedJ_ud`), so the UD refinements stand.
  - *Provenance.* Both theorems are from longfellow-zk's Lean formalisation (`formal/ligero` @ 1c06629, Copyright
    Google LLC, Apache-2.0), as ported to flat modules at Lean 4.34.1 by the Flock entry (`flock-recursive`
    @ 1b74a2a2). They are vendored as `LvmJB*` (30 modules, 7.8 k lines, all in `Solution`'s closure), with module
    and namespace renames only. `LICENSE-longfellow` in this root holds the licence and the change list. Flock's
    `LvmLJ*` lemmas (5 modules) are vendored under the same licence for the list-version extractor, which is not
    used yet.
  - *Soundness accounting.* Per group, before the `2^-14` discount: folds `≤ 2^-130`, OOD points `≤ 2^-170`,
    positions + `λ` + openings 2^-114.30, 2^-114.80 and (final) 2^-115.44; after it **2^-128.30, 2^-128.80,
    2^-129.44**. Lean bounds every group by `εS = 7·2^-131 = 2^-128 − 2^-131` (`whirEps_main24J`), luck by 2^-132
    and the hash by 2^-139: `εFS ≤ 7·2^-131 + 2^-132 + 2^-139 ≤ 2^-128` (`εFS_kcertOfSpec`). The other groups
    pay the union over `C_main`'s candidates (`candPairs_ncard_le`: `L₀ = 98`; `C_rec`'s candidate is unique).
    They stay `≤ 2^-129` because `MidHyp.cons ≤ 2^56` (was 2^60) keeps `98·ξ` small and `C_main` takes at most
    2^40 batched claims.
- **Re-frozen record:** P20 (21, 1, 16, **4,017**), PUB 131, 88 groups, 151 tables (5.82 M committed words).
  **|π| 915,712 B** (−178,536, −16.3 %), **qS 7,440** (−2,476), trace 179,052 lanes, signed file 2,352,919 B. `Q` is 4.93 M words (`Q_link` 1.04 M, `Q_sig`
  0.16 M, `Q_arith` 3.72 M; was 5.40 M). The table phase has 16 rounds, so the accumulator's `dk` is 12 (`D = 28`
  unchanged).
- **Checks.** The Lean `V_S` accepts the shipped prover's P20 and P8 streams (steps 1–3) and rejects tampered OOD
  answers, OOD intro scalars and PoW lanes, besides the tape, wire and `KS` tampers of pr11-9e756ce6880a.
- **Measured, local season shape** (dev VM, 8 pinned CPUs, caps unchanged, one run): **ACCEPT**, S = **5.85** (P̄ 3.63,
  V̄ 2.22), S× = **3.83** at the local `v_ref` (1,040 ms); mean `V` **247.2 ms** (median 241 ms); steps 2.7–8.7 s,
  step 1 6.7 s; fit `P(n) = 1.95 + 7.04·n/2^20` s; prover peak 6.84 GiB; `build_s` 588 s, comparator 490 s (cap
  600). Against pr11-9e756ce6880a on the same harness: S −6.5 %, S× −2.7 %; mean `V` −21 ms (fewer queries and
  Merkle paths), P̄ −2 % (one run each, within noise).
- **Expected on the evaluation machine [e]:** pr11-983bdcfa21d6's evaluation-to-local ratios (P̄ 0.54, `V` 0.57) give
  P̄ ≈ 1.96 s and mean `V` ≈ 0.141 s, so S ≈ 4.10 and S× ≈ 2.05 (pr11-9e756ce6880a on the same projection: 4.49
  and 2.11; −8.5 % and −2.7 %). At a P̄ ratio of 0.7: S ≈ 4.69, S× ≈ 2.66. `|π|` is 0.44 of the 0.68 per check
  that `V̄` charges locally.

## Changes in pr11-9e756ce6880a (since pr11-2f57ce79224a)

- **The chain became a digest-only tape.** Only lanes 0–3 of each row's Keccak-f output are committed (v1's `CH`
  committed `in`, `mid` and `Y`); row `i`'s input `Pad43(D[i−1])` is virtual. leanVM's Keccak GKR runs as one
  segment of depth 24, and a 20-round wiring sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ m]` (evaluated by
  automata over `m`'s bits), a slot reduction and one ring switch tie its input claim to the committed digests.
  `chain_of_tape` gives `chainEnd s n = h`.
- **`C_main` shrank from 2^26 to 2^24 words**, with three WHIR levels instead of four; `|π|` 1,181,488 → 1,094,248 B.
- The prover's fixed part shrank with `C_main`; the recursion-table build starts once `h` is known.
- Local season shape: S = 6.26 (P̄ 3.70, V̄ 2.56), S× = 3.94, mean `V` 268.6 ms; `build_s` 507 s, comparator 464 s.

## Changes in pr11-2f57ce79224a (since pr11-983bdcfa21d6)

pr11-983bdcfa21d6 was accepted on the evaluation machine: S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s,
g 1.19), mean |π| 1,180,192 B. pr11-2f57ce79224a gated the chain link by `n` (the prover's work grows with `n`),
added prover levers (bytes unchanged) and fast verifier twins proved equal to the code they replace (`VS20F_eq`;
505 → 264 ms per check). Local season shape: S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46.

## Idea

### Trust surface: what is proved, and what is checked when V runs

- **The theorem.** `certified : CertificateR declared submission` with `submission = subG staticOkB VS20F`
  (`LvmFinCert.certificateFin`). It uses only the axioms `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no `native_decide` and no added `axiom`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`,
  `fuel t = 2^46 + 8192·t`.
- **Proved in Lean, with no hypothesis left open.**
  - KS of the IOP: leanVM's doom certificates, plus luck, plus the self-fold accumulator (A23).
  - The generic FS compiler from a doom certificate to the library's `KState`, which gives `KS`.
  - The node relation from the tables: chain (`chain_of_tape`), sponge, WOTS, and the child's `acc` through
    `loopir_sound`, `qlink_sound`, `qsig_sound` and `harith_core`/`harith20`.
  - The native `V` refines the compiled IOP verifier (`refines_VSL`, `VS20F_eq`).
  - The extractor's output and cost (`computesX` at the declared fuel).
  - The Johnson code facts of `C_main`'s levels (`codeFacts_johnson`), from the vendored longfellow-zk theorems
    (`LvmJB*`; `LICENSE-longfellow`).
- **Discharged by kernel `decide` at the frozen record.** These are facts about the concrete program `Q`
  and its tables:
  - `fitsR`, the table shapes and the `chkB` checks (`chkFit_P20`);
  - the layout and input-map fields (`LvmQAsmFacts*`);
  - the cell bounds of the position fields (`posCellsB_P20`);
  - the positions and lanes of every phase (`harNum20`, `okE_P20`, `posLanesR20/M20/B20`, `hbs20`).
- **Checked when V runs: the A24 guard.** Five static facts are not kernel-decidable within the caps:
  - no computed-address read in `Q_arith`;
  - `Q.wf`;
  - grouping and injectivity of the table pieces;
  - well-formedness of the claim lists.

  The table builder's `List.mergeSort` is well-founded recursion and gets stuck in the kernel. A
  structural sort is OOM-killed at 12 GB. So these facts are one closed `Bool`, `staticOkB`.
  - The submitted verifier is `if staticOkB then VS20F else reject every 'S' proof`.
  - The certificate case-splits on `staticOkB` without evaluating it. In the `true` branch,
    `staticFacts` gives the facts, and the full proof applies. In the `false` branch, the `S` branch
    accepts nothing, and KS holds trivially (`certificateR_reject`, εFS ≤ 2^-139).
  - **Soundness therefore holds for either value.** Only completeness of the native prover depends on
    `staticOkB = true`. The compiled V evaluates it once per process (1.5 s), and it is `true` at P20:
    every e2e run and badge check accepts.
- **Completeness** is the `W` kind (`P := encode`, error 0). The SNARK prover is tested by the harness,
  not proved complete.
- **Soundness error.**
  - Model: ≈ 2^-128.30. The dominant term is `C_main` level 0's query group (230 positions at the Johnson
    radius, after the 2^-14 PoW discount); the table below has every group.
  - Lean: `εFS = ε + εB + hash ≤ 7·2^-131 + 2^-132 + 2^-139 ≤ 2^-128` (`kcertS`, `εFS_kcertOfSpec`). Inside ε,
    every group is at most `εS = 7·2^-131`: `C_main`'s Johnson groups (`whirEps_main24J`: folds ≤ 2^-130, OOD
    ≤ 2^-170, query groups 2^-128.30, 2^-128.80, 2^-129.44), `C_rec`'s UD group with grinding (`whirEps_rec20G`,
    ≤ 2^-129), and every other group at ≤ 2^-129 with the union over `L₀ = 98` candidates.
  - The chain's mask adds no error term: `n` is in the seed query, so every kernel is fixed before any
    challenge, and `V` evaluates `K̃_ch`, the threshold sum and `ι` exactly. Every tape challenge (`r`, lane
    samples, the 24 layers' RMFE points (46/|E|) and rounds, the wiring and slot rounds (2/|E|), the ring
    switch) escapes with ≤ 2^-173 per fresh query after the union over `C_main`'s 98 candidates, far below the
    WHIR query groups.
  - The hash term covers collisions, state repeats and 32-byte window hits at any offset of any query.

### Construction

**Tree shape: one SNARK per step.** Every output is `nodeStmt c_L (leafStmt h n)`.
- The right child is a witness-sending leaf `⟨encode (leaf s n), [], σ_leaf⟩`. `(s, n, h, σ_leaf)` are in
  the clear; `V` checks `σ_leaf` natively, and the SNARK proves `chainEnd s n = h`.
- The left child is the previous signed proof `(π', tr', σ')`. It is committed, and it is verified in the
  circuit.

A flag `b` selects leaf mode (`b = 0`, step 1's first proof) or node mode. There is one shape and one
schedule, so every proof has the same size and makes the same queries. The chain tape always has
2^20 rows; the rows `i ≥ n` hold the zero input, so the prover's work grows with `n`. `traceDigest []` is
constant, so one `σ_leaf` (one SIGN) serves the whole stream, and one WOTS walk per proof remains. A `W` proof never starts with `'S'` (`encode_first_byte`), so `V`
dispatches on `π[0]`.

**Chain tape (2^20 rows, only the digest `D[4]` committed).**
- Row `i`'s input is virtual: `Pad43(s)` for `i = 0`, `Pad43(D[i−1])` for `1 ≤ i ≤ m = n − 1`, zero for `i ≥ n`.
  `Pad43(d)` is the block `0x43 ‖ d`, so lane `j` is `(d_j << 8) | (d_{j−1} >> 56)`. That is not `K`-linear:
  multiplying by `x^8` reduces modulo the field polynomial and carries nothing into the next word.
- `D = Keccak-f(in)[0..4)` is proved by leanVM's GKR (RMFE χ), one segment of 24 rounds, from an output claim on
  `D̃` plus 21 free scalars for the other lanes. The GKR ends in a claim on the inputs, weighted by bit positions.
- A wiring sumcheck (20 rounds) turns that input claim into a bitwise claim on `D` (the `Pad43` shift is a
  shift of bit positions, `ω(8 + p)`), with the public kernel `ι(x + 1)·[x + 1 ≤ m]` and the constants of
  `Pad43(s)` and `c43`. `V` evaluates the kernel and the threshold sum by small automata over `m`'s bits. A slot
  reduction and one ring switch tie the bitwise value to 64 bit-slice claims on `D`.
- The boundary is `D̃(bits(m)) = h`, and `chain_of_tape` gives `chainEnd s n = h`. The dead rows carry no
  statement; the prover folds them in closed form.

**Sponge table `KS` (2^15 rows).** The same GKR (two 12-round segments, `in`, `mid` and `Y` committed), with a
word-linear sponge link. It holds the child's
trace sponge (its message lanes are `C_rec`'s stream columns), one WOTS walk (399 + 32 + 16 rows) and the
child's statement hashes. Six `BITS` tables decompose words for the unaligned prefixes, the WOTS
digits, the positions and the range checks.

**Two commitments.**
- `C_main`: 2^24 `K` words (`D`, `KS`, then the recursion tables), never decoded.
- `C_rec`: 2^19 words, holding the child's trace as 17 lane columns plus `σ'`. It is the only thing `Ex`
  decodes.

Decoding `C_main` would cost ≈ 2^50.6 `K` products [e] (v1's 2^52.6 at 2^26, scaled), against a fuel cap of
`2^48 + 2^16·t`.

**Stacked WHIR: `C_main` at the Johnson radius, `C_rec` in unique decoding, grinding on both.**
- `C_main`: folds 6/4/4, rates 1/2, 1/4, 1/8, 230/115/77 queries, caps 2^8/2^7/2^7, final 2^10 `E` scalars.
  Levels 0–1 send an OOD sample. The lists have at most 98, 390 and 646 members (`codeFacts_johnson`: the Johnson
  MCA and list bounds of the vendored longfellow-zk proofs; `L₀ = 98` is level 0's). `C_main` is never decoded, so its lists cost `Ex`
  nothing.
- `C_rec`: one UD level (radius `(1 − ρ)/2`, list size 1; fold 6, rate 1/4, 170 queries), final 2^13 `E`
  scalars in the clear.
- Every level grinds 14 bits: a separator sample, a nonce, a PoW challenge whose lane 2 is `< 2^50`, then the
  positions. The nonce opens the level's query group, which the FS compiler charges once (`2^-14·eQuery`).

UD on `C_rec` is what makes the extractor cheap. `Ex` folds `C_rec`'s word, finds the agreement set against
`Enc(final)`, interpolates the 64 rows on 2^13 agreeing positions (barycentric, with shared weights) and
back-substitutes into the novel basis. That costs 2^37.95 steps; the proved total is
`2^39 + ≈ 2.55 k·t`. The proximity side is a new UD mutual-correlated-agreement lemma (Berlekamp–Welch
by counting), plugged into leanVM's one-variable-per-round WHIR soundness.

**Fiat–Shamir is a hash chain over the contract oracle.**
- `q₀ = "lvm/1\0\0"`, then the seed `a₀ ‖ header`.
- Each FS query is `st ‖ pending messages` and yields `st'`. The challenge is lanes 0–2 of `st'`; a
  positions query yields 8 positions.
- Merkle leaves (512 B or 384 B) and nodes (64 B) are queries, and paths stop at the cap.
- There are no tags: query classes are told apart by length, and the trace is lane-aligned, so the
  circuit reads it as `K` words.

**Verifier circuit: LoopIR, not a VM guest.** `Q = Q_link ++ Q_sig ++ Q_arith` runs the child's verifier
on the child's trace:
- `Q_link`: the trace follows the schedule. FS states chain, nodes hold the previous answer, paths end at
  the absorbed cap, and positions are the answer's bits. Answers are read, never hashed.
- `Q_sig`: the WOTS walk to `vk`, and the child's header and statement.
- `Q_arith`: `V_S`'s accept bit. It covers the bus GKR, table sumcheck, accumulator fold, the tape's GKR
  (24 layers) and wiring, `KS`'s GKR and link, two ring switches, every claim, and both WHIR openings with
  their OOD and PoW checks.

Blocks are row templates over loop dimensions with affine addresses `A·g^{Σ s_d j_d}`, so `V` evaluates a
block's fixed columns in closed form. Rows of one shape are grouped into power-of-two tables. Every
operand is a read on leanVM's `g`-power memory bus (logup with counts, a grand-product GKR, one table
sumcheck). `loopir_sound` is generic: table constraints, a balanced bus and nonzero counts imply that
the committed cells are `interp Q`'s cells and its assertions hold. Assertions are gated by `b`.

**The recursion fixed point: a self-fold accumulator (A23).** A recursive verifier must check the
fixed-column claims of its own program. Two alternatives fail:
- Evaluating them in the circuit (self-evaluation) needs ≥ 1.5–2.5 M extra words.
- Plain deferral, where the parent folds the child's claims, has no sound fold challenge. The child's
  trace is adversarial (KS is for every `vk`), and the parent's transcript comes after the commitment.

So every `S` proof folds its incoming accumulator `acc_in = (pt ∈ E^28, y)` with its own fixed claims in
its own transcript:
1. draw `κ ∈ E^11` and set `y_own = Σ_k eq(κ, k)·v_fix[k]`;
2. read a degree-28 line polynomial `h` with `h(0) = acc_in.y` and `h(1) = y_own`;
3. draw `t` and set `acc_out = (line(t), h(t))`.

`V` checks only `Φ̃(acc_out.pt) = acc_out.y` natively, in one sweep over the fixed columns. The parent's
circuit (`Q_acc`, 53 k words) recomputes the child's `acc_out` deterministically from the child's trace
and asserts that it equals the parent's `acc_in`, which is in the header and the seed. The new escapes
are ≤ 2^-192 per `κ_j` and ≤ 28/|E| for `t`, so ε is unchanged. One `Φ` serves every proof, and the
program need not be a fixed point of itself.

**Native `V`.** Direct functional Lean on `UInt64` field kernels proved equal to CompPoly. It does not
interpret `Q`: `harith_core` proves that `Q_arith`'s rows imply `decideCore` and the accumulator equation.
The compiled `VS20F` shares the header-independent table parts across checks and is proved equal to the
specified `VS20` (`VS20F_eq`).

### What came from where

| | kept | cut | changed |
|---|---|---|---|
| leanVM protocol | `K`, `E`; Keccak GKR with RMFE; `g`-power bus, grand product, table sumcheck; ring switching; stacked WHIR with OOD (Johnson radius on `C_main`) | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine | UD on `C_rec`; grinding inside the query group (nonce `read`, PoW challenge); hash-chain FS; Merkle through the oracle with caps; two commitments; LoopIR; digest-only chain tape with a wiring sumcheck; accumulator |
| leanVM `formal/` (4.35) | DSL, `Cert`, doom rules; Keccak GKR, sumcheck, grand product, bus, spine, ring switching; WHIR (≈ 120 modules / 31 k lines, ported to 4.34.1), now with its OOD and Johnson path | VCVio, ArkLib, Clean, leanISA, `Extraction`, `Cost`, `Guest` | `LevelCode` with a UD threshold (`C_rec`, `listMax = 1`) or Johnson constants (`C_main`); the MCA input from longfellow's proofs |
| longfellow-zk `formal/ligero` (Apache-2.0, via the Flock entry's flat port) | the Johnson list bound, Haböck's strong MCA (`LvmJB*`, 30 modules / 7.8 k lines) | — | module and namespace names only (`LICENSE-longfellow`) |
| leanVM Rust | `primitives`, `parallel`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core` (gkr, leaf, constraints), std-only | `rand`, `tracing`, jemalloc | transcript, Merkle, WHIR config, portable clmul tiers, a layers-only GKR entry point (`prover/src/lv/PATCHES.md`) |
| leanerVM | bus `lookup_sound`, generator facts | ArkLib-typed PIOP layers | — |
| earlier Flock-class entry | field kernels; extractor DSL, log index, sort, lookup, FS scan (≈ 9 k lines); barycentric decoder; `mca_ud_line`; Keccak sponge layer; W/S dispatch; oracle client, format, asm pipeline | PIOP, layout, Ligerito proofs; BLAKE2s circuits | decoding over `K` rows in the novel basis |
| organiser library | `WitnessSending`, `KState`/`KS`, fast Keccak and signature twins | — | — |

## Result

**Harness.**

| run | result |
|---|---|
| pr11-983bdcfa21d6, evaluation machine | ACCEPT; S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s, g 1.19) |
| pr11-983bdcfa21d6, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 16.21 (P̄ 12.76, V̄ 3.45), S× = 15.74, mean V 0.506 s; `build_s` 683 s, comparator 444 s |
| pr11-2f57ce79224a, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46, mean V 0.276 s; `build_s` 662 s, comparator 513 s |
| pr11-9e756ce6880a, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 6.26 (P̄ 3.70, V̄ 2.56), S× = 3.94, mean V 0.269 s; `build_s` 507 s, comparator 464 s |
| this version, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 5.85 (P̄ 3.63, V̄ 2.22), S× = 3.83, mean V 0.247 s; `build_s` 588 s, comparator 490 s (cap 600); axioms `propext`, `Classical.choice`, `Quot.sound` |
| this version, evaluation machine | from this PR's evaluation (projected S ≈ 4.1–4.7, S× ≈ 2.0–2.7) |
| `prover setup` variant on Zen 4 | v4 expected (cpuid); the dev VM runs v4p |

**Frozen P20 record** (busDepth, leafdec, rounds, evals) = (21, 1, 16, 4,017); PUB is table 131.

| quantity | value |
|---|---|
| `|π|` | **915,712 B** |
| `qS` | **7,440** (`qV` 16,384) |
| trace | 179,052 lanes (0.643 of `C_rec`'s capacity) |
| signed file | 2,352,919 B (cap 64 MiB) |
| tables | 88 groups, 151 tables, 4,017 evaluations (BITS 2,647), **5.82 M committed words** (`C_main`'s free region is 9.44 M) |
| `Q` words | 4.93 M (`Q_link` 1.04 M, `Q_sig` 0.16 M, `Q_arith` 3.72 M) |

**Prover, dev VM.** QEMU, 8 threads, shared host. Its cpuid hides PCLMULQDQ, but the instruction executes;
VPCLMULQDQ and GFNI do not, so the evaluation variant v4 cannot start there. The runs use the dev variant
v4p (AVX-512 + PCLMUL) and the shipped binary with the embedded program blob. The P8 and P20 streams
(1–3 steps; children with n = 1, 200,000 and 2^20 at P20, 1, 511 and 512 at P8) are accepted by the Lean `V_S`,
and tampered ones (n ± 1, a byte of the tape's `r`, its scalars, its lane-challenge message and its GKR, the wire's
messages, `KS`'s `r`, the OOD answers and intro scalars, the PoW lanes) are rejected. Sparse and dense (`LVM_PGATE=dense`) proofs are byte-identical.
- Local season shape: step 1 **6.7 s**; later steps **2.7–8.7 s**; a fit over the stream gives
  `P(n) ≈ 1.95 + 7.04·n/2^20` s (pr11-9e756ce6880a: 2.04 + 7.06; pr11-2f57ce79224a: 4.3 + 7.6).
- Peak RSS: **6.84 GiB** (cap 11).
- The nonce search takes 12–35 ms per proof (four levels, 2^14 expected attempts each).
- The fixed part (≈ 2.0 s) is mostly the 2^24 commitment (bound by the oracle's Merkle hashing), `KS`'s GKR, the
  bus and tables, and the opening. The tape's GKR is ≈ 0.23 s + 8.6 s per 2^20 rows, the same as v1's depth
  12 × 2 segments.
- Zen 4 [e]: the GFNI/VPCLMULQDQ tiers make the GKR 2–3× faster.

**Verifier**, measured on the dev VM (one core):
- **247.2 ms per check** (harness mean, local season shape; median 241, p10 233, p90 267 ms).
  pr11-9e756ce6880a: 268.6 ms; pr11-2f57ce79224a: 275.5 ms; pr11-983bdcfa21d6: 506 ms.
- Start-up is not charged; it is 10.7–11.4 s per process on the loaded dev VM (`staticOkB`, shared table parts,
  caches).

**Score.** pr11-983bdcfa21d6 scored S = 10.17 and S× = 8.19 on the evaluation machine, against #7's S = 105.9 and
S× = 505.8.

**Error budget (model, P20, per fresh query, log₂).** The groups outside WHIR carry the union over `C_main`'s
98 candidates (+6.6); the WHIR query groups include the 2^-14 PoW discount.

| group | bound |
|---|---|
| sumcheck rounds (GKR pack and position, tables, wiring, slots) / Keccak GKR step 2 (degree 46) | −183.8 / −179.9 |
| bus fingerprint and grand product / ring switching per challenge | −163.4 / −185.4 |
| stacked-claim batching (`(J − 1)·98/\|E\|`) | −173.4 |
| WHIR folds (main 0–2 / rec) | ≤ −130 each / −160.4 |
| WHIR OOD points (main 0–1) | ≤ −170 |
| WHIR query groups: positions, `λ`, openings (main 0–2, rec) | −128.30, −128.80, −129.44, ≤ −129 |
| union over every Keccak, wiring and slot challenge | −173.2 |
| accumulator `κ_j` / `t` | −185.4 / −180.6 |
| extractor luck (`C_rec`, unique) / hash | −174.4 / −151.4 |
| **worst + luck + hash** | **−128.30** (Lean: `εFS ≤ 2^-128` with every group `≤ 7·2^-131`) |

**Extractor.** `fuel = 2^46 + 8192·t`; the decode's fixed cost (≤ 2^38 steps) is 2^8 below `fuel_base`.

**Lean.** 549 flat modules, ≈ 159 k lines; `Solution`'s import closure holds 509 of them (2,755 build jobs in the harness), of which 30 are the vendored `LvmJB*`. In v1, comparator time was cut from 705 s to 462 s on the dev VM by proof-only changes
(`rfl`-lemma `simp` replays, one-pass checkers).

## What failed, and why

- **leanVM's extractor.**
  - Guruswami–Sudan list decoding has a proved cost of ≤ 2^81 + …, and its cone is 443 modules /
    133 k lines.
  - Even at multiplicity 1 (Berlekamp–Welch), 64 lanes × 2^55 = 2^61 is about 2^12 over the
    `2^48 + 2^16·t` cap.
  - Hence UD on `C_rec`, the commitment `Ex` decodes. `C_main`, never decoded, moved to the Johnson radius in
    this version (|π| −16 % together with grinding).
  - ArkLib's Johnson MCA closure (300 modules / 80 k lines) is off the import allowlist anyway; the vendored
    longfellow-zk proofs need only Mathlib.
- **Johnson from BCIKS20's bound.** Its Johnson-radius theorem gives correlated agreement, not the mutual form
  WHIR needs, and is a `sorry` in ArkLib at our pin. With its size, `C_main`'s level 0 would need 297 queries,
  more than UD's [model].
- **Witness-sending nodes over SNARK leaves.** Each leaf is ≥ 0.75 MB of `(π, tr)`, so the 64 MiB cap
  breaks near step 85 (step 30 in UD), and the mean `|π|` of ≈ 36 MB gives `S ≥ 60`. Recursion is
  necessary.
- **Step 1 as one SNARK over two chains.** That needs a 2^27 commitment (≈ 14.6 GiB), more than 11 GiB.
- **leanVM's VM guest as the circuit.** Guest correctness is 300 k+ lines of proofs, and a 2^20 chain is
  2^27–2^28 cycles, past `MAX_MU = 28`. A flat gate list fails too: `V` would evaluate fixed columns of
  ≥ 2^20 rows.
- **Committing the whole chain row.** v1 committed `in`, `mid` and `Y` of all 2^20 chain rows (3,456 bits a row)
  and needed `C_main` at 2^26; gating the link (pr11-2f57ce79224a) made the GKR scale with `n` but kept that commit. The tape
  commits 256 bits a row and makes every input virtual, which is what lets `C_main` drop to 2^24. Committing `mid`
  at depth 12 instead of a depth-24 GKR keeps 2^26 [e].
- **A cheaper χ layer or one field.** Three design studies found no layer cheaper than leanVM's RMFE layer, and
  three found that `K = GF(2^64)` alone cannot carry 2^-128 per challenge (lifts, repetition and mixing are
  forkable at ≈ 2^-64 per query).
- **The `0x43` byte shift** is not `K`-linear (see Idea). It is proved bitwise, with ring switching, and
  the BITS tables handle the small unaligned prefixes.
- **The in-circuit self-evaluation** of fixed columns needs ≥ 1.5–2.5 M extra words: 1,160 columns,
  25 k loop terms and 56 k BITS monomials. **Plain deferral** to the parent has no sound fold challenge.
  Both were replaced by the self-fold accumulator (A23).
- **`C_rec`'s direct final check** cost ≥ 3.28 M words. It was dropped; ε and `Ex` are unchanged, since
  WHIR's final-level check has the same postcondition.
- **Ungrouped tables** would send 9,806 evaluations instead of 440. The final count is still 3,805
  (24 B each in `π`), mostly from BITS (2,578).
- **The assembler fixpoint** (record ↦ program ↦ record) oscillated between 76 and 81 groups once
  `Q_arith` was complete. Padding `Q` to the record made it converge (P20 +16 k words).
- **Kernel-deciding the whole program.** `mergeSort` is well-founded recursion, and a structural sort is
  OOM-killed at 12 GB. This is why A24 exists. Cheaper decide forms cut the rest from 42 to 13 s (`SLokF`
  16.1 → 1.2 s; per-block position lanes 20.1 → 6.5 s).
- **The extractor's FS replay by query prefix** was unsound: abandoned branches share prefixes. The replay
  now uses exact full queries.
- **Two statement bugs found while proving.** A WHIR phase's doom did not imply residual consistency; it
  was fixed with a joined residual doom. `ext_eq` as an equality is false outside `Ex`'s domain (an entry
  of ≥ 2^64 bytes); it became `(∃ w, Ex = some w ∧ Rel) ∨ Ex = S.Ex`.
- **Lean 4.35 → 4.34.1.** 70 leanVM modules compiled unchanged. Three failed on pin drift: ArkLib's
  Johnson API, the BF64 evaluation drift (CompPoly `572f9973` vs `e28da348`) and `.trans` resolving to
  `Function.trans`.
- **Build time.**
  - An RMFE `decide +kernel` went from 61 s / 8.5 GB to 3–4 s, by checking rows on `ℕ` rather than
    parities in `List Bool`.
  - A `Vector.replicate (2^19)` evaluated by the kernel had cost 78 s.
  - `congr 1` on field terms costs 5–31 s each.
  - Every module pays ≈ 3 CPU-s just to import.
  - Together these cut the clean build from 458 to 386 s and from 918 to 847 s at two stages, and the peak
    from 9.6 to 3.6 GiB.
- **The V target.** V was 0.34 s before `Q_arith` was complete and 0.5 s after: 84 groups, 1,226 fixed
  columns, 4,199 evaluations. The `Φ̃` sweep grew from 65 to 160 ms.
- **Testing v4 without the machine.** LLVM auto-vectorised std's start-up with GFNI, so v4 raises SIGILL
  on the dev VM even for `info`. Under Intel SDE, v4's P8 proof is byte-identical to v2's. `prover setup`
  self-tests each variant against v2's digest and caps the dispatch.

## What to try next

1. **The sponge into the tape.** `KS`'s own GKR (two 12-round segments), its committed `in`/`mid` columns and
   its link would go: the sponge rows join the tape as rows `2^20 + j`, with their inputs virtual
   (`cont_j·Y[j−1] + Msg[j]`). Expected: ≈ −0.4 s of fixed prover time, ≈ −0.8 M circuit words, one slice claim on
   `C_rec` [e].
2. **`C_rec` at the Johnson radius too (J2), with a second `C_rec` level.** The relativised doom (an accepting
   transcript ends in a fold of a good candidate) and the list-version extractor facts are proved and in the
   root (`LvmWhir*R`, `LvmWhirDoomJ`, `LvmLJ*`), outside `Solution`'s closure; they need the two-level `C_rec`
   prover, `V` and decoder. Expected |π| ≈ 714 KB [model].
3. **Exact-budget query counts and larger caps.** `C_rec`'s count still meets `≤ 2^-129`; the exact budget
   (`εS = 7·2^-131`) would save a query or two there, and larger caps trade cap bytes for path bytes. Caps are part
   of the certificate's level configurations, so this reopens their facts.
4. **`V`.** WHIR final claims keyed by their point inside the bus step; one shared `eq` table per (height, size)
   within a group; the Keccak GKR checks on arrays; fewer BITS evaluations.
5. **Prover speed.** The `C_main` commit is bound by the oracle's Merkle hashing (≈ 3.7 of its 4.8 CPU-s at 2^17); a
   wider leaf or node would cut it. The FS-ordered per-layer work of the GKRs is ≈ 2 ms per layer, ≈ 0.15–0.2 s per tape.
6. **Fewer guarded facts.** A structural, kernel-friendly table builder would let the kernel decide `wf`,
   grouping and claim well-formedness. That would remove `staticOkB` and 1.5 s of start-up.
7. **Left unapplied.**
   - drop v1's dead chain-table and shift-link modules from the closure (build and kernel time);
   - `Q_link`'s node-half selection as one degree-2 assertion (−0.35 M);
   - `C_rec`'s zero columns as free table space;
   - a Rust test verifier;
   - the extractor's serial build chain.
