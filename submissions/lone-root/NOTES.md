# lone-root

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #11, #7, #12, #13, #15, #17, #19, #20

This root continues #20 (`typed-spartan`, rolls 7 and 8), which continued #19 (`listless-whir`, roll 6 =
pr19-0bdb3ad5e872) and PR #11 (`leanvm-inspired`). "Changes since #20" is relative to #20's submitted version; this
root is roll 11 (M′: one commitment). #20 has no evaluation yet, so its local bench and projection are the reference.

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, ring switching and
stacked WHIR. It is reshaped for the contract in four ways:
- an extractor that decodes only the child's stream block (lanes 40–47 of `C_main`), with unique-decoding
  programs on advice;
- a hash-chain transcript over the signed oracle;
- an in-circuit verifier written as loop tables instead of a VM guest;
- new here, a typed backend for those tables. The node program commits only its row results. A Spartan-style
  zerocheck and a wiring sumcheck tie them to the program's wiring polynomial `Φ_Q`, which `V` evaluates once per
  proof through the self-fold accumulator. leanVM's memory bus is kept only for the few reads whose address is data.

From #7 it takes the core library's `WitnessSending` relation, unchanged: that relation is the right leaf of every
node and the completeness route. The prover can run relay-echo's (#12) AVX-512VL chain kernel, and its v4 tier runs
leanvm-gkr-fast's (#13) Keccak GKR with leanvm-fast-verify's (#15) round storage. Its root leaves carry only their
occupied lanes, as in relay-slim (#17).

Notation:
- `K = GF(2^64)` (`x^64+x^4+x^3+x+1`, CompPoly `BF64`) and `E = K[y]/(y^3+y+1)` (CompPoly `BF64.Ext3`);
  `g = x` generates `K^×`.
- `Ex` is the extractor; UD means unique decoding. P20 is the production parameter set and P8 the test set.
- `Q` is the node program. `T` is `C_main`'s typed table region. `Φ_Q` is the multilinear extension of `Q`'s four
  wiring matrices, in 43 variables.
- Shapes: big for `n > 2^18` (stride 1); small for `n ≤ 2^18` (the even words, stride 2).
- dev means the QEMU dev VM. [e] marks an estimate and [model] a model on measured inputs.

## Changes since #20 (typed-spartan)

#20 (roll 8) was not evaluated when this root was cut. Its local season shape read S 3.655, S× 2.577 (dev, host
loaded), projected to S ≈ 2.36, S× ≈ 1.29 on the evaluation machine [model].
- **Roll 11 (M′) merges `C_rec` into `C_main`.** There is one commitment and one opening.
- **Unchanged:** the claim and the theorem's statement; `εFS ≤ 2^-128` with the same form
  (`0 + (7·2^-131 + 2^-132) + 2^-139`); `C_main`'s WHIR (ν = 23, rate 1/4, the same levels and query counts); the
  typed backend, its phases and `Φ_Q`; the two shapes; the gadget programs and their theorems; the chain tape; the
  hash-chain transcript and the accumulator's fold rule.

- **The stream block `S` (stage `S2GM`).** What `C_rec` held (the child's 17 stream columns, `σ'` and the `X` rows)
  is `C_main`'s block `S`: 2^19 words at 5,767,168 (small shape: 2,621,440, logical), column `c` at `S + c·2^14`.
  - The column stride stays 2^14, so the relayout kernel (V's division automaton and the circuit's) is unchanged.
  - There is no `C_rec` cap and no `C_rec` opening. Every claim is on `C_main`: the relayout's point claim at
    `⟨19, S⟩`, `σ'`'s region claim, the `KS` link's `M`/`X` and the mini-bus seed columns.
  - **The window.** In both shapes the stream's physical words lie in `C_main`'s lanes 40–47 (P20: 44–46 big,
    40–44 small; `LvmMPWin`, `win20`). The extractor decodes only those lanes.
  - The cost: the 17 columns end in lane 46, so `C_main`'s root leaf has **47 lanes** (376 B, 4 permutations per
    leaf query; #20: 46 lanes, 3 permutations). This is +920 B against 46 lanes.
- **Sizes [exact, = Lean `sizes_P20`; measured on every proof below].**
  - **`|π|` 464,544 → 332,336 B (−132,208 B, −28.5 %)**, `qS` 5,464 → 3,895, signed file 1,313,111 → 941,871 B.
  - The child's trace: 105,472 → 75,593 lanes (hashed 843,776 → 604,744 B), sponge blocks 6,205 → 4,447.
  - The mini-bus record is (12, 1, 6, 633), was (13, 1, 6, 936): `C_rec`'s cap reads left `capTpl`.
  - P8: `|π|` 214,696 → 177,288 B, root leaf 52 lanes.
- **The certificate at M′** (`certified` is `Lvm.CT.certificateM20`, `LvmCertM20`).
  - KS: `kcertSM` with one invariant list. Every non-good candidate fails a claim (`OpenPostM`); the relativised
    prefix of `C_main` runs to level 2's residual, `ResC` is rejected by the suffix spec and `GoodRes` becomes the
    extractor's input. `L₀` = 124 candidate pairs (#20: 124·304 = 37,696), so the groups outside WHIR carry
    +7.0 bits of union instead of +15.2.
  - The extractor: `decodeMP2` (2^13 positions) → `decodeMP1` (2^16) → `decodeMP0` (2^19, lanes 40–47 only), all
    instances of the generic decoders that the shipped `decodeRec`/`decodeRec1` are instances of. The list luck over
    the three lists and 14 fold rounds is 14·615·2^19/|E| = 2^-159.93 [exact]. `ext_eqM20` ties the executable
    extractor to it. The fuel `2^46 + 8192·t` is unchanged. TODO(lead: the M′ extractor's cost against 2^46.)
  - The node relation: `nodeT20` on stream-block pairs (`GoodT ∧ SBlk`), through `nodeSoundTG`; the child's one
    `C_main` opening (`LvmMPNodePos`).
  - The refinement: `refinesM20`, `midFollowsM20`, with the relocation `reloc20` (`relocLaw20`).
  - **The guard gains `sigInSB`:** `staticOkB20 = staticOkT20 && oneOkB && sigInSB && nodeChkB && harChkB`.
    `sigInSB` checks that `σ'`'s region lies in `S`. It is `true` at P20 [measured].
  - TODO(lead: `#print axioms certified`, module and line counts.)
- **Prover.** One commitment: no `C_rec` buffer, commit or opening. The opening is zero-padded to `S`'s end. R9's
  pooled typed witness and relayout gather (already in #20) now read `C_main`'s `S`.
- **Measured on dev** (QEMU, v4p, 8 threads):
  - **Prover A/B against #20's code** (#20's prover source, built with the same flags; a real-Q deterministic P20
    stream; CPUs 8–15 under the timing lock; 3 interleaved rounds; host load 1.3–5.8): step medians
    **2^17 1.601 → 1.495 s (−0.106)**, **2^18 + 1 2.593 → 2.482 s (−0.111)**, **2^20 7.530 → 7.552 s (+0.022)**.
    Without the tape stage, which is the same code in both arms: −0.072, −0.046 and +0.014 s. `open rec`
    (0.02–0.04 s) is gone. A first session at host load 41–49 read −0.014, −0.100 and −0.078 s.
  - **V badge against #20** (`btime`: parse and `acc`, start-up excluded; CPU 8 under the lock; 3 interleaved
    rounds of 10 checks; load 1.5–2.8): small steps **118.0 → 100.0 ms (0.847×)**, big steps **116.5 → 90.0 ms
    (0.773×)**.
  - V start-up: 15.4–15.9 s per process, 486 MB [measured, lock, 3 runs] (#20: 16.4–16.9 s).
- **Checks.**
  - The Lean `VST` (the shipped `V_S`, through `tcm`) accepts the merged prover's P20 stream of 5 steps that
    crosses both shapes in both directions (a first step over leaves 1 and 2^17, then 4 node steps at 2^18 + 1,
    2^17, 2^20 and 2^18), P20 S,0 at n = 1, 2^17,
    2^18, 2^18 + 1 and 2^20, P8 S,0 at 256, 512 and 300, and P8's 3-step stream. Every phase checkpoint passes and
    no claim is on `C_rec`.
  - The linked `.s` prover (the harness's `gcc -static -O2 -pthread *.s -o prover -lm`) gives byte-identical
    proofs to the cargo build on a deterministic 5-step P20 stream, and `VST` accepts them.
  - **Tampers are rejected on node steps**, not only on S,0: a stream word of `S` (`sword`) and a `σ'` word (`sig`),
    in both shapes at P20, and at P8, are caught by the relayout. R11-E's V-side tampers (Σ flips, header `n`, the
    root leaf's bytes in every window lane, an absent-lane word, the 512-B leaf) are all rejected.
  - TODO(lead: harness cert: ok?, gate, `build_s`, Lean kernel / comparator, peak, modules built.)
- **Measured, local season shape:** TODO(lead: ACCEPT?, S, P̄, V̄, S×, mean `V`, step range, step 1, fit `P(n)`,
  prover peak, `c_P`.)
- **Expected on the evaluation machine [model]:** TODO(lead: S, S× projected from the local bench). G0's model:
  ΔV̄ ≈ −0.197 from `|π|` alone, ΔS ≈ −0.24 to −0.28 against roll 8's model [model].

## Changes in #20 (typed-spartan; since pr19-0bdb3ad5e872)

pr19-0bdb3ad5e872 was accepted on the evaluation machine: S = 3.088 (P̄ 1.511, V̄ 1.577), S× = 1.555 (mean `V`
0.113 s, g 1.029), |π| 644,576 B.
- **Roll 7** gave steps with `n ≤ 2^18` a half-size commitment and shrank the sponge table. It was not released on its
  own (it stayed under the push gate against #19 [model]), so it ships inside this root.
- **Roll 8** replaces the recursion circuit's memory argument and re-lays `C_main` at 2^23 words, rate 1/4.
- **Unchanged:**
  - the claim and the theorem's statement;
  - `kcertSJ` and `εFS ≤ 2^-128`;
  - `C_rec` and its Johnson WHIR;
  - the extractor's decoder programs and fuel;
  - the chain tape;
  - the gadget programs (`Q_link`, `Q_sig`, the Keccak, WHIR and ring-switch gadgets) and their theorems;
  - the hash-chain transcript and the accumulator's fold rule.

- **The typed, bus-free backend (roll 8).**
  - *Witness: results only.* `T` holds one word per `K` result and three limb words per `E` result, plus the
    `BITS` bit words and the mini-bus's counts: **842,060 words padded**, against roll 7's 5.38 M table words. No
    operand is committed. The child's trace (`S_flat`), the header lanes (`PUB`) and the word `1` are virtual
    regions, a `loadE` result is its three `K` words, and the constants of `Q_link`'s lane-check table (QLT) are
    constants of `Φ_Q`.
  - *Relation.* Four sparse matrices over `E` are static functions of the program: `W` (the cell a row writes),
    `A` and `B` (its factors) and `D` (its addend). For every constraint slot `x`:
    `(Az)(x)·(Bz)(x) + (Dz)(x) + (Wz)(x) = 0`. There are 509,014 constraint slots (of 2^20), and the word space
    is 2^21.
    `holds_of_wiring` turns this relation, the mini-bus's `ReaddOk` and the layout check into `Program.Holds` and
    `Program.Asserts` on the memory read off `z`. The gadget theorems are stated on any memory where the program
    holds, so they do not see the backend.
  - *Phases* (after the commitment). They replace the bus, the table sumcheck and the accumulator's fixed-column claims.
    1. Zerocheck: `τ ∈ E^20`, then 20 rounds of degree 3 in equality mode, ending in `a*·b* + c*`.
    2. Wiring: `γ`, then 21 rounds of degree 2 on `Σ_y (M̃_A + γM̃_B + γ²M̃_{D+W})(r_x, y)·z̃(y)`.
       - The prover sends the four matrix values `v_o = M̃_o(r_x, r_y)` and the region values of `z̃(r_y)`.
       - V computes the `PUB` and `1` parts itself.
       - It emits the region claims on `C_main` and one claim on `S_flat`.
    3. Relayout: 19 rounds of degree 2 move the `S_flat` claim to one point claim on `C_rec`. The kernel is the
       sponge's stride-17 map `p ↦ (p mod 17)·2^14 + p div 17`. V evaluates it with a division automaton over 19
       bits (17 remainder states) plus a closed form for the tail.
    4. The accumulator at `Φ_Q` (below).
    5. The mini-bus (below).

    Apart from `Φ_Q`, these phases cost V ≈ 0.7 ms [measured].
  - *`Φ_Q` through the accumulator.*
    - The fold: `κ ∈ E^2` selects the matrix, `y_own = Σ_o eq(κ, o)·v_o`, `h` has 44 coefficients, and
      `acc = (pt ∈ E^43, y)`.
    - V never looks a cell up. It evaluates `Φ_Q` once per proof, natively, at `acc_out.pt`.
    - Every operand is in one of four classes:
      - K1, a bit map of the iteration index (one-bit `eq` factors);
      - K2, a shift: the previous iteration's slot, or an init cell (a successor automaton);
      - K3, a record read `b + R·j + o` at strides such as 13, 17 or 173. A carry automaton evaluates it. One pass
        serves every operand of a block with the same `(R, ℓ)`.
      - points.
    - Dense regions cover small ranges read across blocks, and sub-cube splits cover 72 piecewise-affine operands.
    - `PhiQC` compiles the terms into atom code and automaton passes: 197,756 `E` products [exact, before the final
      refreeze], **≈ 46 ms per evaluation** on dev [measured].
    - `PhiQC_eq` proves `PhiQC` equal to the multilinear extension.
    - The prover's `h` uses the same kernels: 42 evaluations, 37 ms [measured, on roll 7's larger witness].
  - *Mini-bus (depth 13).* Only `capTpl`'s reads have data addresses: the cap node at `g^(capL + 4·idx + r)`, with
    `idx` from position bits.
    - These 2,688 reads keep leanVM's `g`-power logup bus: a grand-product GKR of depth 13 (6,272 push leaves),
      then a 6-round table sumcheck with 936 evaluations over 312 tables (272 seed blocks of the stream, 40 read
      tables).
    - Their fixed address columns are checked natively and in the circuit (`powColG`).
    - QLT's 18,432 `readd`s have public addresses. They became static operands with a proved static `ReaddOk`.
  - *Layout: binary-chunked, lane-split.*
    - Each block's committed slots are split into power-of-two runs, with the iteration bits low. One `2^w` region
      per block would pad `T` to 1.07 M words.
    - Row-major input regions (the `KS` aliases `xs`, `ys`, `md`) are split by lane into aligned regions, so every
      alias is affine.
  - *Circuit.* `Q_arith` drops the bus, table, `qacc` and claims/basis sections and calls the typed verifier gadget
    `typedG`: ≈ 11.1 k rows on the placeholder record (zerocheck and wiring 1,236, relayout 787, accumulator 417,
    mini-bus 8,545). `Q` has 548 blocks.
- **`C_main` at ν = 23, rate 1/4 (roll 8).**
  - (fold, rate, queries) = (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, **58**); g = 14, OOD after levels 0–1, final
    2^9. It was (6, 1/2, 230), (4, 1/4, 115), (4, 1/8, 77) on 2^24 words.
  - Lists of at most 124, 231 and 615 members. The codes are `codeJ17R2` (new), `codeJ13R3` and `codeJ9R4` (new),
    from `codeFacts_johnson`.
  - Query groups 2^-128.330, 2^-129.072, 2^-129.918 after the PoW discount; folds 2^-130, 2^-132, 2^-130; OOD
    2^-173.2 and 2^-170.8 (`eps_main23Jq`, eight `norm_num` facts).
  - Level 2 needs 58 queries: 57 give 2^-127.92 at any slack.
  - The candidate pairs are `L₀ = 124·304 = 37,696` (was 29,792).
- **Two shapes split at `n = 2^18` (roll 7's SH2-Z, now at ν = 23).**
  - A small step commits its tables as a logical 2^22-word table on the even words of the ν = 23 commitment. The
    prover runs half the NTT and hashes half the level-0 leaves (roll 7: −0.165 s at 2^17 and −0.203 s at 2^18 per
    small step [measured]).
  - V's WHIR, Merkle trees, schedule, |π| and `qS` are the big shape's. Only the claims' weights differ: they carry
    the factor `1 − x₀` (`onStackZ`).
  - No claim reads an odd word, so junk there is accepted, as designed.
  - The shape is a function of `n`, which is in the seed query. The certificate reads a view of the candidate
    column (`Good₂`, `bigOf`, `holds_onStackZ`), and the circuit muxes the child's terminal coordinates.
  - Roll 7's small-shape check cost +19.5 ms over a big one. Now they cost about the same: 140 ms and 138 ms.
- **`KS` at 2^14 rows (roll 7), then 2^13 (roll 8).**
  - The sponge table had 2^15 rows in #19. KS13 holds 7,680 sponge blocks (7,296 at the 95 % margin,
    `caps_KS13_P20`), and the trace needs 6,205.
  - Its GKR (`KS gkr`) is 0.06 s shorter per step than roll 7's [measured].
- **Z2 (#17) kept, at 46/35 lanes.**
  - `C_main`'s root leaf is 368 B (46 lanes, 3 permutations), `C_rec`'s 280 B. #19 had 48/35; roll 7 at ν = 24
    had 58.
  - `T` sits below `KS` in the layout. With `KS` first, the columns would need 48 lanes and 4 permutations per leaf.
  - P8 has 51/35.
- **The certificate on the typed objects (wave L).** `certified` is `certificateT20`. Its parts:
  - the guard's facts `SF20`;
  - `kcertSJ`, unchanged, on `midSpecR_T₂` (`typedSpecR` composed with roll 7's tape and `KS` specs on the view
    `Good₂`);
  - `refines_VST`: the native `VST` refines the compiled typed program;
  - `nodeT20B`: `NodeSound` on the typed relation, through the typed HAR `harithT20`.

  The guard is `staticOkB20 = staticOkT20 && oneOkB && nodeChkB && harChkB` (see Trust surface). V checks it once
  per process: ≈ 16.5 s at P20 on dev, at start-up and outside the timed check (#19: 1.5 s).
- **The dead bus path is pruned.**
  - The bus program's record is not refrozen, and the prover's bus path is dead.
  - The bus certificate tail is deleted (`refines_VSL`, `certificateFin`, the bus HAR and fit facts).
  - `certified`'s import closure no longer reaches `LvmShapeBus`, `LvmAccSpecCert`, `LvmCertSFinal*` or
    `LvmFin{Cert,Dec}`.
- **Lazy Keccak layer weights in V.** `decideFT` runs the Keccak GKR check with lazy layer weights (`decideProgTS`, proved equal by
  `decideProgTS_eq`): ≈ −27 ms of dev V per proof [measured], with no change to proof bytes, prover, circuit or `Φ_Q`.
- **Prover kernels.** The Keccak GKR's serial part and kernels, the typed gathers, and the commitment's scheduling.
  Proof bytes are unchanged (the deterministic 9-step stream gives the same sha256s). Most of the gain is in the v4
  kernels; the dev VM moves ≈ −0.06 to −0.09 s per step [measured].
- **Prover.**
  - The typed backend: the results-only witness, the zerocheck, wiring and relayout provers, and `h` by the class
    kernels.
  - Against roll 7 on the same real stream [measured, steps 2+, 4 interleaved rounds, lock, load 7–19]: step
    medians **−0.32 s** (2^17), **−0.75 s** (2^18), −0.32 s (2^18 + 1) and −0.44 s (2^20). Without the tape stage,
    which is the same code in both arms: −0.32 to −0.44 s.
  - The bus, tables, accumulator and line evaluation (0.21 s) gave way to the typed phases (0.10 s) and the
    mini-bus (0.01 s). Commit fell by 0.04–0.05 s, `open main` by 0.11 s, `KS gkr` by 0.06 s and `chain+sponge`
    by 0.04 s.
  - `prover setup` times a typed P20 step, and its self-test proves a typed P8 S,0.
- **Re-frozen record (stage `S2GB1`).** **|π| 464,544 B** (−180,032 B, −27.9 %), **qS 5,464** (7,426), signed file
  1,313,111 B (1,808,935). The mini-bus record is (13, 1, 6, 936). P8: 214,696 B.
- **Checks.**
  - `lake build RFSubmission` is green. `certified` and its parts use `propext`, `Classical.choice` and
    `Quot.sound` only. The guard is true at P20.
  - The Lean `VST` accepts the native prover's P20 streams: 5 node steps crossing both shapes in both directions,
    S,0 at n = 1, 2^17, 2^18, 2^18 + 1 and 2^20, and the linked `.s` prover's 3-step stream. It also accepts P8's
    S,0 and a 3-node-step stream.
  - Every tamper is rejected (Result). An operand tamper in any class is caught only by `Φ_Q(acc_out)`.
  - The deterministic P20 stream is byte-identical across runs, the dense small-shape reference and the linked `.s`.
  - Harness cert (`evaluate.py cert`, pin 7ecd179, under the timing lock on dev): **ok**, gate PASS; `build_s` 661.5 s,
    Lean kernel 592.8 s, peak 4.69 GB, 599 modules built [measured].
- **Measured, local season shape** (dev VM, 8 pinned CPUs, caps unchanged): **ACCEPT**, 96 steps, not truncated;
  S 3.655 (P̄ 2.543, V̄ 1.112), S× 2.577, mean `V` 120.2 ms; step 1 3.97 s, later steps 1.61–8.15 s; fit
  `P(n)` = 0.729 s + 6.84 µs per permutation; prover peak 6.66 GiB [measured]. The host was loaded (`c_P` 1.077),
  so P̄ reads high.
- **Expected on the evaluation machine [model]:** S ≈ 2.36, S× ≈ 1.29 (P̄ × 0.5, mean `V` × 0.6 from the local bench),
  i.e. S −23.5 % and S× −17.3 % against pr19-0bdb3ad5e872. The design model gave S 2.24 and S× 1.18 [model].

## Changes in pr19-0bdb3ad5e872 (since pr11-c65f417243e9)

pr11-c65f417243e9 was accepted at S = 3.508 (P̄ 1.684, V̄ 1.824), S× = 1.738, |π| 783,192 B.

- **`C_rec` at the Johnson radius (J2′):** (6, 1/4, 115) then (4, 1/8, 77), one OOD sample after level 0, final 2^9.
  Its lists have at most 304 and 311 members.
- **Knowledge soundness from one invariant used as the `KCert`'s luck, with no doom** (`kcertOfInv`, `kcertSJ`):
  "every non-good candidate pair fails some running claim". The invariant holds on honest runs. Each group's
  escape from it has the bound of the matching soundness escape, so KS costs only the extractor's list luck.
- **Extraction without a list decoder.** Off the list luck `LuckBJ`, the transcript is advice that singles out the
  good list member. The UD decoder programs (`decodeRec1`, then level 0) return it at the same fuel (`extJ`,
  `decode_SJ`).
- **#17's Z2**, ported, at 48/35 lanes.
- **Shared address columns** (EVD2): table evaluations 2,851 → 2,576.
- **Prover plumbing** with byte-identical proofs: the table build is off the witness critical path (`BITS` cone,
  H-taint), buffers are prepared before `ready`, and `prover setup` picks the worker count by timing a step.
- |π| 783,192 → 644,576 B. Evaluation: S = 3.088, S× = 1.555.

## Earlier rolls of PR #11

- **pr11-c65f417243e9** (S 3.508, S× 1.738):
  - grinding (g = 14) on every WHIR level, inside the query group (nonce `read`, PoW challenge);
  - `C_main` at the Johnson radius with OOD (230/115/77 queries), from longfellow-zk's proofs (`LvmJB*`);
  - a second UD level on `C_rec`;
  - shared position-bit tables (4,299 → 2,851 evaluations);
  - the faster native `V` (`VS20G`);
  - #12's chain kernel and #13/#15's v4 Keccak GKR.
- **pr11-9e756ce6880a** (S 4.374, S× 1.993): the digest-only chain tape (one depth-24 GKR segment, a 20-round wiring
  sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ m]`, a ring switch). `C_main` went from 2^26 to 2^24 words.
- **pr11-2f57ce79224a**: the chain link gated by `n`, and fast verifier twins proved equal (505 → 264 ms per check).
- **pr11-983bdcfa21d6** (S 10.17, S× 8.19): the first accepted version.

## Idea

### Trust surface: what is proved, and what is checked when V runs

- **The theorem.** `certified : CertificateR declared submission`.
  - `submission = subG staticOkB20 VSB20` and `VSB20 = VST P20 NT20` (`LvmSubmissionST`).
  - `certified` is `Lvm.CT.certificateM20` (`LvmCertM20`; roll 11, M′).
  - It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no `native_decide`
    and no added `axiom`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`, `fuel t = 2^46 + 8192·t`.
- **Proved in Lean, with no hypothesis left open.**
  - KS of the IOP. leanVM's doom-certificate framework is used with no doom. The luck is "the invariant broke, or
    the extractor's list luck" (`kcertOfInv`; at M′ `kcertSM` on `PSWithM`, with one list on `C_main`).
    - The typed front end, `typedSpecR`, has five phase specs in the `Doomed` calculus: zerocheck, wiring,
      relayout, the accumulator at `Φ_Q` (`accSpecQ`, `phiQ_fold`) and the mini-bus.
    - It is composed with roll 7's tape and `KS` specs on the view `Good₂`, then moved onto `C_main`'s stream
      block by the relocation `reloc20` (`midSpecM_T₂`, `midShapeM_T₂`, `relocLaw20`).
  - The generic FS compiler from a doom certificate to the library's `KState`, which gives `KS`.
  - The node relation, `nodeM20` (`NodeSoundM`) from `nodeT20`: `NodeSound VSB20 vk (GoodT Ti20 H ∧ SBlk) childS`
    on stream-block pairs, with the window fact `win20`. It rests on:
    - `holds_of_wiring` (the typed relation ⇒ `Holds`, `Asserts`);
    - `ReaddOk` from the mini-bus and the static reads (`readdOk_of_chk`, `mbRead_seeded`);
    - the input map (`inMapT`), QLT's constants (`hqltT`) and `BITS` (`outT_sound`);
    - roll 7's gadget theorems (`chain_of_tape`, `qlink_sound`, `qsig_sound`) on that memory;
    - the typed HAR `harithT20` (`Q_arith`'s rows ⇒ `decideCoreT` and the accumulator equation);
    - `decideFT_of` (`Φ_Q(acc_out) = y` through `PhiQC_eq`).
  - `PhiQC_eq`: the compiled evaluator equals the multilinear extension of the four matrices. `compileTF_eq`: the
    fast compiler equals the original.
  - The native `V` refines the compiled IOP verifier: `refinesM20`, `refinesM20L`, `midFollowsM20`. The closed
    forms are proved equal to their specification sums: `regClaim_rel`, `relayKernF_rel` (`divKern_eq`),
    `virtEF_rel`.
  - The extractor's output and cost: `computesX` at the declared fuel.
  - The Johnson code facts of every WHIR level (`codeFacts_johnson`; `cfgMain23Jq`), from the
    vendored longfellow-zk theorems (`LvmJB*`; `LICENSE-longfellow`).
- **Discharged by kernel `decide` at the frozen record:**
  - the schedule's sizes and the `KS13` caps (`sizes_P20`, `caps_KS13_P20`);
  - the phases' lane offsets (`rcLanes20`);
  - the typed phases' end and the tape's start (`typedEnd_P20`, `tapeStart_P20`);
  - the mini-bus's read blocks (`capBlocksOk_P20`);
  - the openings' position lanes (`posLanesB20`);
  - `Q_link`'s static checks on the layout (`hQ20`);
  - no `readd` in `Q_sig` (`noReadd_sig20`).
- **Checked when V runs: the guard `staticOkB20`.**
  - The kernel cannot build `Q` or evaluate the layout solver's output, so these facts are one closed `Bool`:
    - `staticOkT20`:
      - `Q.wf` and `lay.Ok Q`;
      - `Φ_Q`'s cache check (`PhiCache.okB`, `PhiQC_eq`'s hypothesis: its terms cover the matrices' entries, in
        their classes);
      - V's regions are aligned and are the layout's;
      - the mini-bus record and its cells' placement;
      - QLT's constants;
      - `g`-injectivity below the cell bound.
    - `oneOkB`: the word `1` lies in a `1` region.
    - `nodeChkB`: the input map's cells, every `readd` either static or on a mini-bus read table, and the seeds lie
      in the stream.
    - `harChkB`: `Q_arith`'s claim list is well formed in both shapes, and the circuit's regions are V's.
  - The submitted verifier is `if staticOkB20 then VSB20 else reject every 'S' proof`.
  - The certificate case-splits on the guard without evaluating it (`certificateM20`):
    - in the `true` branch, `sf20` gives the facts and the full proof applies;
    - in the `false` branch, the `S` branch accepts nothing (`certificateR_rejectM`).
  - **Soundness therefore holds for either value.** Only completeness depends on the guard being `true`.
  - Each fast check is proved equal to its original (`cacheT20_eq`, `staticOkT20_eq`, `checkTermsF = checkTerms`).
  - The guard is `true` at P20 [measured]. A process takes 15.4–15.9 s to build and check it on dev.
- **Completeness** is the `W` kind (`P := encode`, error 0). The SNARK prover is tested by the harness, not proved
  complete.
- **Soundness error.**
  - Model: ≈ 2^-128.33. The dominant term is `C_main` level 0's query group (115 positions at rate 1/4, after the
    2^-14 PoW discount). That is +0.137 bit against εS = 2^-128.193. KS adds only the extractor's list luck
    (2^-159.93 over M′'s three lists).
  - Lean: `εFS = ε + εB + hash ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128` (`kcertSM`, `εFS_kcertSM`).
    - There is no doom, so `ε = 0`.
    - `εB = εI + εL`. `εI = εS = 7·2^-131` bounds every group's escape from the invariant, and `εL = 2^-132` the
      list luck.
    - Inside `εI`: `C_main`'s groups (`eps_main23Jq`), the typed phases, the mini-bus (`errs20`), and the Keccak,
      wiring and `KS` groups (`kg_errsJ2`). Each group outside WHIR takes the union over `L₀ = 124` candidate
      pairs (#20: 37,696, with `C_rec`'s groups as well).
  - The chain's mask adds no term. `n` is in the seed query, so every kernel is fixed before any challenge.
  - The hash term covers collisions, state repeats and 32-byte window hits at any offset of any query.

### Construction

**Tree shape: one SNARK per step.** Every output is `nodeStmt c_L (leafStmt h n)`.
- The right child is a witness-sending leaf `⟨encode (leaf s n), [], σ_leaf⟩`. `(s, n, h, σ_leaf)` are in the
  clear; `V` checks `σ_leaf` natively, and the SNARK proves `chainEnd s n = h`.
- The left child is the previous signed proof `(π', tr', σ')`, committed and verified in the circuit.

A flag `b` selects leaf mode (`b = 0`, step 1's first proof) or node mode. There is one schedule and two commitment
shapes chosen by `n`, so every proof has the same size and makes the same queries. One `σ_leaf` (one SIGN) serves the
whole stream. A `W` proof never starts with `'S'`, so `V` dispatches on `π[0]`.

**Chain tape (2^20 rows, only the digest `D[4]` committed).**
- Row `i`'s input is virtual: `Pad43(s)` for `i = 0`, `Pad43(D[i−1])` for `1 ≤ i ≤ m = n − 1`, and zero for `i ≥ n`.
- `D = Keccak-f(in)[0..4)` is proved by leanVM's GKR (RMFE χ), one segment of 24 rounds.
- A 20-round wiring sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ m]`, a slot reduction and one ring switch
  tie the GKR's input claim to bit-slice claims on `D`. `V` evaluates the kernel by small automata over `m`'s bits.
- The boundary is `D̃(bits(m)) = h`; `chain_of_tape` gives `chainEnd s n = h`.
- In the small shape `D` commits 2^18 rows, and the rows above read as the dead-row constant.

**Sponge table `KS` (2^13 rows).** The same GKR (two 12-round segments; `in`, `mid` and `Y` committed), with a
word-linear sponge link. It holds:
- the child's trace sponge, whose message lanes are the stream block's columns;
- one WOTS walk (399 + 32 + 16 rows);
- the child's statement hashes.

`BITS` rows decompose words for the unaligned prefixes, the WOTS digits, the positions and the range checks.

**One commitment (M′, stage `S2GM`).**
- `C_main`: 2^23 `K` words. The layout is `D` (2^22), `T` (2^20), `KS` (at 5,242,880), the stream block `S` (2^19
  words at 5,767,168: 17 columns of stride 2^14 holding the child's trace, the `X` rows at `S` + 7,680, `σ'` at
  `S` + 278,528), then `KSY2` (6,053,888) and the mini-bus's columns (from 6,144,000), which end at word 6,148,080
  (lane 46.9 of 64). In the small shape everything above `D` moves down by 3·2^20, on even words (`S` at
  2,621,440).
- The stream's physical words lie in lanes 40–47 in both shapes, and those lanes are the only thing `Ex` decodes.
  #20 kept them in a second commitment, `C_rec`.

**Stacked WHIR at the Johnson radius, with grinding.**
- `C_main`: (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, 58); caps 2^8/2^7/2^7; OOD after levels 0–1; final 2^9 `E`
  scalars. Its lists have at most 124, 231 and 615 members.
- Every level grinds 14 bits: a separator sample, a nonce, then a PoW challenge whose lane 2 is `< 2^50`, then the
  positions. The nonce opens the level's query group, which the FS compiler charges once (`2^-14·eQuery`).

**The extractor decodes `C_main`'s window with UD programs on advice.** An accepting run that keeps the invariant
ends at level 2's residual on a good list member's fold path (`GoodRes`), and off the list luck the transcript singles
that member out. `Ex` decodes three levels, each an instance of the generic decoders that #20's `decodeRec`/
`decodeRec1` were instances of: `decodeMP2` (2^13 positions, `k` = 2^9) → `decodeMP1` (2^16, 2^13) → `decodeMP0`
(2^19, 2^17, lanes 40–47 only). The list luck over the three lists and 14 fold rounds is 2^-159.93. The fixed cost
is under `fuel_base = 2^46`: TODO(lead: the M′ bound). No list is ever enumerated.

**Fiat–Shamir is a hash chain over the contract oracle.**
- `q₀ = "lvm/1\0\0"`, then the seed `a₀ ‖ header`.
- Each query is `st ‖ pending messages`. The challenge is lanes 0–2 of the answer.
- Merkle leaves (376 or 384 B) and nodes (64 B) are queries. Paths stop at the cap.
- Query classes are told apart by length, and the trace is lane-aligned.

**Verifier circuit: LoopIR on a typed backend.** `Q = Q_link ++ Q_sig ++ Q_arith` runs the child's verifier on its
trace:
- `Q_link`: the trace follows the schedule;
- `Q_sig`: the WOTS walk to `vk`, and the child's header and statement;
- `Q_arith`: `V_S`'s accept bit. It covers the typed phases, the tape's GKR (24 layers) and wiring, `KS`'s GKR and
  link, two ring switches, every claim, and both openings with their OOD and PoW checks.

Blocks are row templates over loop dimensions with affine addresses, and every cell is written by one instance.
- **Up to pr19:** every operand was a read on leanVM's `g`-power memory bus.
- **Now:** the backend of "Changes since" commits only the results. The gadget theorems hold on any memory where the
  program holds, so the backend has only to give `Program.Holds` and `Program.Asserts` (`holds_of_wiring`).

**The recursion fixed point: a self-fold accumulator (A23).** A recursive verifier must check the claims on its own
program's wiring. Every `S` proof folds its incoming accumulator `acc_in = (pt ∈ E^43, y)` with its own
four matrix values, in its own transcript:
1. draw `κ ∈ E^2` and set `y_own = Σ_o eq(κ, o)·v_o`;
2. read a degree-43 line polynomial `h` with `h(0) = acc_in.y` and `h(1) = y_own`;
3. draw `t` and set `acc_out = (line(t), h(t))`.

`V` checks only `Φ_Q(acc_out.pt) = acc_out.y`, natively. The parent's circuit (`qaccT`, 417 rows) recomputes the
child's `acc_out` and asserts that it equals the parent's `acc_in`, which is in the header and the seed. One `Φ_Q`
serves every proof, and the program need not be a fixed point of itself.

**Native `V`.** `VST = parseOk ∧ drive (schedule P20) (decideFT P20 NT20)`, where
`decideFT = decideCoreT && Φ_Q(acc_out) == y`.
- It is direct functional Lean on `UInt64` field kernels proved equal to CompPoly. It does not interpret `Q`.
- The typed phases are new code. The tape, wire, `KS` and opening phases are roll 7's.
- On dev a check takes 128 ms per proof, of which `Φ_Q` is ≈ 46 ms [measured, no lock].

### What came from where

| | kept | cut | changed |
|---|---|---|---|
| leanVM protocol | `K`, `E`; Keccak GKR with RMFE; `g`-power bus, grand product, table sumcheck (now only the mini-bus); ring switching; stacked WHIR with OOD at the Johnson radius | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine | KS from an invariant used as luck, with no doom; `C_rec` extracted by UD decoders on advice; grinding inside the query group; hash-chain FS; Merkle through the oracle with caps; two commitments; LoopIR; digest-only chain tape; accumulator; typed backend |
| Spartan (Setty) | a zerocheck over row constraints, then a sumcheck against sparse wiring matrices | SPARK and every committed matrix | a write matrix over the result memory; equality mode over `E`; the matrices' extension evaluated by class kernels and carry automata, once per proof through the accumulator |
| leanVM `formal/` (4.35) | DSL, `Cert`, doom rules; Keccak GKR, sumcheck, grand product, bus, spine, ring switching; WHIR (≈ 120 modules, ported to 4.34.1) with its OOD and Johnson path | VCVio, ArkLib, Clean, leanISA, `Extraction`, `Cost`, `Guest` | `LevelCode` with Johnson constants on both commitments; `kcertOfInv` |
| longfellow-zk `formal/ligero` (Apache-2.0, via the Flock entry's flat port) | the Johnson list bound, Haböck's strong MCA (`LvmJB*`, 30 modules / 7.8 k lines) | — | module and namespace names only (`LICENSE-longfellow`) |
| leanVM Rust | `primitives`, `parallel`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core` (gkr, leaf, constraints), std-only | `rand`, `tracing`, jemalloc | transcript, Merkle, WHIR config, portable clmul tiers, a layers-only GKR entry point (`prover/src/lv/PATCHES.md`) |
| leanvm-gkr-fast (#13), leanvm-fast-verify (#15) | v4 tier only: #13's re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0, `src/lv/keccak_gkr_v4/`), with #15's every-round storage | #13's `pcs`/`primitives`/`hash` changes; #15's Lean | `generate_uncommitted` for the tape's extents; `every` = 1 (`PATCHES.md`) |
| relay-slim (#17) | Z2: root leaves of occupied lanes only (`Scheme.occ`, `padRow`, the circuit's zero window, the extractor's reader; Apache-2.0); the C-order link in `build-asm.sh` | its prover scheduling, the 2-lane tape ramp | lanes recomputed: 46/35 at ν = 23 (#20), 47 at M′ (one commitment) |
| listless-whir (#19) | everything not listed under "Changes since" | the bus backend and its certificate tail | the base of this root |
| relay-echo (#12) | the AVX-512VL chain kernel generator `gen_vlasm.py` (Apache-2.0, unmodified; `LICENSE`) | its C and Lean | emitted as Rust `asm!`, chosen at run time |
| leanerVM | bus `lookup_sound`, generator facts | ArkLib-typed PIOP layers | — |
| earlier Flock-class entry | field kernels; extractor DSL, log index, sort, lookup, FS scan; barycentric decoder; `mca_ud_line`; Keccak sponge layer; W/S dispatch; oracle client, format, asm pipeline | PIOP, layout, Ligerito proofs; BLAKE2s circuits | decoding over `K` rows in the novel basis |
| organiser library | `WitnessSending`, `KState`/`KS`, fast Keccak and signature twins | — | — |

## Result

**Harness.**

| run | result |
|---|---|
| pr11-983bdcfa21d6, evaluation machine | ACCEPT; S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 |
| pr11-9e756ce6880a, evaluation machine | ACCEPT; S = 4.374 (P̄ 1.892, V̄ 2.482), S× = 1.993 |
| pr11-c65f417243e9, evaluation machine | ACCEPT; S = 3.508 (P̄ 1.684, V̄ 1.824), S× = 1.738 (mean V 0.119 s) |
| pr19-0bdb3ad5e872, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 4.99 (P̄ 3.30, V̄ 1.69), S× = 3.40, mean V 0.185 s; `build_s` 591 s, comparator 534 s |
| pr19-0bdb3ad5e872, evaluation machine | ACCEPT; S = 3.088 (P̄ 1.511, V̄ 1.577), S× = 1.555 (mean V 0.113 s, g 1.029); Lean kernel 260.1 s |
| roll 7 with Z2 (not submitted), cert only | ok; comparator 593.2 s at host load 8–43 |
| #20 (typed-spartan), local season shape (dev VM, 8 CPUs) | ACCEPT; S 3.655 (P̄ 2.543, V̄ 1.112), S× 2.577, mean V 120.2 ms; `build_s` 661.5 s, Lean kernel 592.8 s |
| #20, evaluation machine | not evaluated when this root was cut (projected S ≈ 2.36, S× ≈ 1.29 [model]) |
| this version, local season shape (dev VM, 8 CPUs) | TODO(lead: verdict; S (P̄, V̄), S×, mean V; `build_s`, comparator) |
| this version, evaluation machine | from this PR's evaluation (projected TODO(lead: S, S×)) |

**Frozen P20 record** (busDepth, leafdec, rounds, evals) = (12, 1, 6, 633), the mini-bus's (#20: (13, 1, 6, 936)).
`accVars` is 43.

| quantity | value |
|---|---|
| `\|π\|` | **332,336 B** (#20: 464,544 B). TODO(lead: the split into scalars, caps, rows, siblings, header) |
| `qS` | **3,895** (`qV` 16,384) |
| trace | 75,593 lanes (hashed 604,744 B; 4,447 sponge blocks of KS13's 7,680) |
| signed file | 941,871 B (cap 64 MiB) |
| typed region `T` | 842,060 words padded; 509,014 constraint slots; `Q` 548 blocks |
| root leaf | `C_main` 376 B (47 lanes, 4 permutations); no `C_rec` |
| P8 | `\|π\|` 177,288 B, signed file 489,575 B, root leaf 52 lanes |

**Prover, dev VM.** QEMU, 8 threads, shared host. Its cpuid hides PCLMULQDQ, but the instruction executes. VPCLMULQDQ
and GFNI do not, so the evaluation variant v4 cannot start there; the runs use v4p (AVX-512 + PCLMUL).
- **Tampers.** Every one is rejected by the check the design names:
  - a result word, by the zerocheck;
  - an operand in class K1, K2, K3, split or point, with `h` corrected so the core checks pass: 5/5, only by
    `Φ_Q(acc_out)`;
  - one coefficient of `h`, by `h(1)`; two coefficients with the sum kept, by `Φ_Q`;
  - `v_S`, by the wiring's final check; the shape, by the `C_main` opening;
  - Σ flips (88/88), header `n` (46/46), `C_rec`'s OOD answer (22/22), and Z2's leaf tampers (132/132) (#20).
  - At M′ (R11-E, R11-RP): the stream word and `σ'` tampers on S,0 and on node steps, the root leaf's bytes in every
    window lane, an absent-lane word and the 512-B leaf are all rejected.
- **Step times:** against #20 see "Changes since #20"; against roll 7 (real stream, AB3) see "Changes in #20". The binary's own setup before `ready` is
  1.4–1.5 s (roll 7: 0.7 s) for the matrices and the class kernels. It is untimed.
- **Local season shape:** step 1 3.97 s, later steps 1.61–8.15 s, fit `P(n)` = 0.729 s + 6.84 µs per permutation,
  peak RSS 6.66 GiB (cap 11 GiB) [measured, host loaded].
- **`prover setup`** on dev: v2 ok, v4 SIGILL, cap v4p, 8 threads. A typed P20 step at `n = 2^17` takes 1,514 ms with
  8 threads, 1,841 with 6 and 2,559 with 4.
- **`.s` files.** ≈ 33 MB a tier (v2 33,271,549 B, v4 33,675,517 B, v4p 33,194,351 B), because of the embedded
  layout dumps; `prover/` is 116.2 MB. Linking all four takes 6.2 s (under the lock, load 30); the binary is
  52.0 MB.

**Verifier**, measured on the dev VM (one core):
- **Badge A/B against roll 7** (CPU 8, lock, 4 interleaved rounds × 6 checks, load 1.5–19):
  - small 218.5 → **140.0 ms** (0.641×);
  - big 206.5 → **138.0 ms** (0.668×).

  #19's badge read 181.0 ms in its own session.
- **Harness mean `V`:** 120.2 ms on dev [measured].
- **Start-up** is not charged: 15.4–15.9 s per process at P20 (lock, 486 MB; #20: 16.4–16.9 s, 530 MB). It builds `Q`, the layout and
  `Φ_Q`'s cache (`compileT`, 7.5 s), then checks the guard. That is about 12 processes per stream at the harness's
  batches of 8.

**Score.** On the evaluation machine:

| version | S | S× |
|---|---|---|
| pr11-983bdcfa21d6 | 10.17 | 8.19 |
| pr11-9e756ce6880a | 4.374 | 1.993 |
| pr11-c65f417243e9 | 3.508 | 1.738 |
| pr19-0bdb3ad5e872 | 3.088 | 1.555 |
| #7 | 105.9 | 505.8 |

**Error budget (model, P20, per fresh query, log₂), as #20 (roll 8).** The groups outside WHIR carry the union over
the `124·304 = 37,696` candidate pairs (+15.2). The WHIR query groups include the 2^-14 PoW discount. At M′ the
`C_rec` rows go, `L₀` is 124 (+7.0) and the extractor's list luck is 2^-159.93; `C_main`'s worst group, −128.33,
stays the worst. TODO(lead: the re-derived table for roll 11.)

| group | bound |
|---|---|
| `τ` and `κ` coordinates (1/\|E\|) | −176.80 |
| zerocheck rounds (degree 3) | −175.21 |
| `γ`; wiring and relayout rounds (degree 2) | −175.80 |
| accumulator `t` (`Φ_Q`: 43 variables) | −171.37 |
| Keccak GKR step 2 (degree 46; tape and `KS13`) | −171.27 |
| other leads (ring switches, `KS13`, `LkSJ`) | −172.2 to −172.6 |
| mini-bus fingerprint (2^13 leaves) | −161.80 |
| stacked-claim batching (main `(J − 1)·124/\|E\|`, `J ≤ 2^40` / rec `(J − 1)·304/\|E\|`, `J ≤ 2^55`) | ≤ −129 / ≤ −128.75 |
| WHIR folds (main 0–2 / rec 0–1) | −130.00, −132.00, −130.00 / −130.0, −134.5 |
| WHIR OOD points (main 0–1 / rec 0) | −173.22, −170.77 / −172.7 |
| WHIR query groups: positions, `λ`, openings (main 0–2 / rec 0–1) | **−128.33**, −129.07, −129.92 / −128.75, −129.36 |
| extractor list luck (`C_rec`, both levels) / hash | −165.4 / Lean ≤ −139 |
| **worst** | **−128.33** (Lean: `εFS ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128`) |

**Extractor.** `fuel = 2^46 + 8192·t`, unchanged. At M′ it decodes `C_main`'s window at three levels (2^13, 2^16,
2^19 positions). TODO(lead: its cost against the 2^46 base.)

**Lean.** 703 flat modules, ≈ 213 k lines; the cert builds TODO(lead: modules built) of them (`Solution`'s closure). #20: 663 modules, ≈ 203 k lines, 599 built. Before roll 8's prune: 646 flat modules, ≈ 199 k lines;
`Solution`'s import closure held 577 of them. A quiet comparator reading with the last stubs still open gave 359.4 s
on dev, a lower bound. Roll 7's base read 536.9 s quiet.

## What failed, and why

**Rolls 7 and 8.**
- **Roll 7 alone.** With Z2 its |π| was 661,824 B, more than #19's 644,576, because a ν = 24 leaf has 58 lanes. A
  small-shape check cost +19.5 ms of `V`. It modelled about −3 % on S [model], so it did not ship alone.
- **SH2-L**, which moves the small shape's zero coordinate to the top lane bit (occupancy 41), was priced and not
  built: ΔS −1.1 %, ΔS× +1.2 % [model]. The small steps would lose their leaf dedup (+0.52 M permutations).
- **The design's per-block padding**, one `2^w ≥ tw` region per block, gave `T` 1.07 M words, over the 0.9 M line.
  Binary chunks give 0.81–0.84 M.
- **Stride 2 up to `n ≤ 2^19`** (the design's plan) needed 55-word leaves, which cost 4 permutations. The split at
  2^18 needs 44–46 words (3 permutations) and gives 10 KB less proof. **Stride 4** never fits in this roll: its fill is
  ≥ 1.11 at 2^18.
- **Protocols rejected at design** [model]:
  - GKR over the program's DAG: the depth runs into the thousands.
  - SPARK or any committed matrix: the opening alone adds 110 KB.
  - Per-instance native evaluation of the wiring: ≈ 0.5 M products, ≈ 90 ms on dev.
  - Committing the awkward operands under a logup: +0.35 M words.
  - A hybrid that keeps the bus for `Q_link`: two memory models.
- **`Φ_Q`'s cost.**
  - The design estimated 150 k products and 28 ms on dev. The first evaluator took 254,900 products and 68.4 ms.
  - The fused, greedy evaluator takes ≈ 198 k products and ≈ 46 ms. Its products cost ≈ 150 ns at best, so ≤ 30 ms
    needs fewer products.
  - The V badge line of 0.62× roll 7 was missed (0.641× / 0.668×) and accepted as a band.
- **The prover's `h` by a generic evaluator** took 145 ms, which put the backend at 0.194 s, over the 0.08 s kill
  line. By the class kernels it takes 37 ms, and the backend 0.073 s.
- **V start-up** was 205.8 s per process at first:
  - `Block.tw` was recomputed at every entry, quadratic in the template (45 of 51 s);
  - `runMerge` copied a bucket on every push (24 s);
  - the key comparisons built arrays inside qsort (5.8 s).

  Fast copies, each proved equal to the original, bring it to 16.5 s. The ≤ 10 s target was missed. The rest is
  spread over `compileT`'s phases.
- **Four design bugs found at integration:**
  - The `KS` aliases were mapped lane-major, but the program reads them row-major, so no honest proof passed. The
    fix is the lane-split regions.
  - The circuit's small-shape mux was still at ν = 24.
  - The mini-bus record had no fixpoint: its seed count oscillated between 885 and 936 evaluations. The fix is a
    fixed count per region and lane class.
  - The tape's start in phases 4–7 was still the bus path's, 2,805 lanes early. Every node step failed its own
    asserts until it was fixed.
- **Statements found false while proving** (each fixed, none relaxed):
  - `compileT_eq`: `limbOf` merged point classes that were not in arithmetic progression. `limbOf` now checks them.
  - `holds_of_wiring` without `Q.wf`: the layout check never counts a `loadE` row's operands. There is a
    Lean-checked counterexample.
  - `typedSpecR` as first written: the relayout takes 19 rounds, not 18, and `acc_in` has 43 coordinates.
  - The relayout's claim as a bare `eqEval` cannot refine V's point claim, whose weight carries `Π_{j≥19}(1 + x_j)`.
  - A drafted greedy-code lemma whose hypothesis forced every state to zero.
- **`irreducible_def`** produces an `opaque` constant, which the gate rejects (roll 7). It was replaced by plain
  definitions.

**Earlier.**
- **leanVM's extractor.** Guruswami–Sudan decoding has a proved cost of ≤ 2^81 + …. Even Berlekamp–Welch over
  64 lanes × 2^55 is ≈ 2^12 over the cap. Hence `Ex` decodes only `C_rec`, with UD decoders and the transcript as
  advice.
- **A relativised doom for Johnson `C_rec`.** It holds on honest runs, so as a doom it applied only with an empty
  good set. The fix (pr19) uses the invariant as the complement of luck.
- **Johnson from BCIKS20's bound.** It gives correlated, not mutual, agreement, and is a `sorry` in ArkLib at our
  pin. `C_main`'s level 0 would need 297 queries at its size.
- **Witness-sending nodes over SNARK leaves.** Each leaf is ≥ 0.75 MB, so the 64 MiB cap breaks near step 85.
- **Step 1 as one SNARK over two chains.** That needs a 2^27 commitment (≈ 14.6 GiB).
- **leanVM's VM guest as the circuit.** Guest correctness is 300 k+ lines of proofs, and a 2^20 chain is
  2^27–2^28 cycles.
- **Committing the whole chain row** (v1: 3,456 bits a row, `C_main` at 2^26). The digest tape commits 256 bits a
  row.
- **A cheaper χ layer, or one field.** No layer was cheaper than leanVM's RMFE layer, and `K` alone cannot carry
  2^-128 per challenge.
- **In-circuit self-evaluation of the fixed columns** (≥ 1.5–2.5 M words) and **plain deferral** (no sound fold
  challenge). The accumulator replaced both, and the typed backend reuses it for `Φ_Q`.
- **Kernel-deciding the whole program.** `mergeSort` is well-founded recursion, and a structural sort is OOM-killed
  at 12 GB. Hence the runtime guard.
- **The extractor's FS replay by query prefix** was unsound, because abandoned branches share prefixes.
- **Lean 4.35 → 4.34.1.** Three leanVM modules failed on pin drift.
- **Build time.** Kernel `decide`s on `ℕ` rows, not `List Bool` parities (61 → 3–4 s), and no kernel-evaluated
  `Vector.replicate`.
- **Testing v4 without the machine.** v4 raises SIGILL on the dev VM. Under Intel SDE its proofs are
  byte-identical to v2's.

## What to try next

1. **Occupancy 46 at M′** (M′ ships here with 47 lanes): 2^13-row stream columns at offset 5,857,280 would give a
   46-lane root leaf, 3 permutations per leaf query and −920 B. It needs the relayout kernel's row bits 14 → 13 in
   `V` and the circuit, and P8 at KS13.
2. **`Φ_Q` at ≤ 30 ms on dev** (it is 46 ms) needs fewer products:
   - aligned query bits;
   - the mini-bus as loops or bigger blocks (its glue rows give ≈ 33 k atoms);
   - fewer `BITS` chunks (621 blocks give ≈ 29 k atoms);
   - or a cheaper `FK.mul`.
3. **Start-up at ≤ 10 s:**
   - `compileT`'s points costing (≈ 2 s);
   - per-atom key tables (−0.3 to −0.5 s) [e];
   - a counting function proved equal to the compiled cost.
4. **The mini-bus at 32-row seed blocks** would roughly halve its seeds and part of its 22.5 KB of evaluations [e].
5. **`.s` size.** 5.3 MB of each embedded layout dump is `BITS` rows that the prover could rebuild from the program's
   `BITS` spec.
6. **E2 on the tape GKR and wire**: the prover's slope from 3.04 to 2.5 µs per chain step [model]. **Rate 1/2 at
   ν = 23** for the product track: 230 level-0 queries, half the level-0 hashing, +100 KB of proof, S× ≈ −7 % [e].
7. **Prover speed.** The tape GKR is most of the slope. The `C_main` commit is bound by the oracle's Merkle hashing.
