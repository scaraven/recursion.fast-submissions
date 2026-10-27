# Stage P2 (track P: throughput, modes, `prover.s`): RESULT (partial)

Status: implementation report, 2026-10-27. Blueprint: revision 3.1/3.2 (`c38bda1`, `2709159`).
Running notes: `P2-JOURNAL.md`. Evidence tags: **measured** (a runner run, its id, and its logs
under `logs/P2/run-<id>/`, gitignored) and **estimate** (arithmetic on measured inputs, derivation
shown). I pushed only `probe/p2-1` … `p2-15`, each one commit on `v4/flock-recursive` with the
files below and `.github/probe.conf = p2-prover`. All of them are deleted.

## 0. Summary (EPYC 7763, the tier of record)

| request (whole, through `rf-oracle`) | measured | runs |
|---|---:|---|
| stream `leaf`, n = 2^16, fresh process, `go` → `done` | **1.36–1.43 s** | 40519554882, 40519561565 |
| m = 30 node, surrogate (the m = 30 proof + the node's E1/E2/Lr work at rev. 3.2's size) | **1.49–1.57 s** | same |
| tree leaf m = 32 (prove, trace, SIGN) | **5.47–5.59 s** | same |
| peak RSS m = 30 / m = 32 (pre-faulted arena included) | 1.90 / 6.19 GB | same |

Estimates for the two caps:

- **Stream link** ≈ 1.39 + 1.53 ≈ **2.92 s**: under the ≈ 3.1 s cap with 6 % margin, but **0.12 s
  above the 2.8 s target**.
- **Tree** ≈ 64 × 5.53 + 63 × 1.53 ≈ 354 + 96 ≈ **450 s**: **meets the 500 s target**, 25 %
  under the 600 s cap.

P1's 7763 figures were 1.75–1.81 s (m = 30) and 6.55–6.67 s (m = 32).

Done:
- the measured gaps of P1 §2.2: the witness, trace replay and allocation are closed; the ring-switch
  partials are removed; the K-fold is cheaper;
- the `setup`, `leaf` and `vk` modes;
- `prover.s` via `build-asm.sh`. It goes through `asm-compat.py` unchanged, assembles with the
  runner's binutils 2.42, and is linked as the runner links it. Every P2 measurement ran that
  linked binary.

Not done:
- `tree` and `node`: they need the node prover, which waits for S-0's `compileMux` dump. The two
  modes exit 2 with a message.
- rev. 3.1's π layout (A.3 grouped order, A.4 item sequence with dummies, `piSize = 756,496`,
  `reassemble`) and the S-0 KAT.
- the GF(16)² round-1 kernel and an AVX-512 tier (§3).

## 1. Changes (files under `submissions/flock-recursive/prover/`; the crate is 7,101 lines)

| change | file | effect on the 7763 at m = 30 / m = 32 |
|---|---|---|
| global allocator: large blocks (≥ 8 MiB) cached and never returned to the kernel, best fit with splitting and merging; `prefault(bytes)` maps and touches one block before the clock (K's arena) | `alloc.rs` (118 lines, new), `main.rs` | no page faults in the timed part; the `leaf` mode pre-faults 1,800 MiB before `ready` |
| word-level witness emits the gate bits as three bit streams held in locals (G as macros). The struct-field version stalled on store-to-load forwarding. 7.3 → 1.42 µs per block; equal to the tape (unit test) | `witness.rs` | witness 0.28 → 0.08 s; 1.49 → 0.51 s |
| ring-switch partials of claims (b), (c) from the lincheck's and the shift's partial folds (`2^14` products) instead of a witness pass; debug-asserted equal to the direct computation | `leaf.rs` | −0.09 s; −0.35 s |
| K-fold by a constant with two F products (`c₀ = S₀D₀ + (αS₁)D₁`, `c₁ = S₁D₀ + (S₀+S₁)D₁`) | `simd.rs` | Ligerito −10 % |
| fold outputs uninitialised (`par::uninit_vec`) | `sumcheck.rs`, `zerocheck.rs`, `ligerito.rs`, `par.rs` | removes the zeroing pass of every fold |
| trace recording: batch queries above 128 bytes (Merkle columns) are not fingerprinted; the replay asks the ≈ 750 opened columns again through the service | `oracle.rs`, `main.rs` | trace 0.064 → 0.055 s; fingerprinting removed from the commit |
| modes `setup` (nothing to set up), `leaf` (PROVER.md §3: `vk.hex`, warm connections and pool, pre-fault, `ready`, `go`, `leaf.json`, prove, trace, SIGN, `proof.bin`, `done`), `vk`; `tree`/`node` exit 2 | `main.rs` | — |
| `build-asm.sh` (spartan-srom's recipe, renamed): fat LTO, one codegen unit, `x86-64-v2`, `sanitize-asm.py`; `prover.s` 5,734,186 bytes, sha256 `338d17d5…` (rustc 1.99.0 on the VM) | `build-asm.sh`, `prover.s` | — |
| node-shape surrogate (`FLOCK_NODE_SHAPE=1`, timing only, not part of the proof): E1 = degree-3 zerocheck over 2^20 rows, Lr over 2^15, E2 = degree-2 sumcheck over the packed polynomial (2^23 F) | `leaf.rs` | 0.16 s on the 7763 |
| the probe: builds `prover.s` on the runner, `asm-compat.py`, `gcc -static -O2 -pthread *.s -o prover -lm`, `selftest`, three runner-like `leaf` requests (`request.py`: fresh process, ready/go/done, native `acc`, canary), m = 30 with and without the surrogate, m = 32 | `probe/p2-prover/run.sh` (48), `request.py` (31) | — |

## 2. Measurements

### 2.1 Runs (`ubuntu-24.04`, 4 vCPU; binary = the runner-assembled `prover.s`)

| run | CPU | build | leaf request (s) | m = 30 + node surrogate (s) | m = 32 (s) |
|---|---|---|---:|---:|---:|
| 40517053502 | EPYC 9V45 | allocator, modes, `prover.s` | 1.00–1.03 | 1.08–1.12 | 3.79–3.82 |
| 40518061701 / 40518067825 | EPYC 9V74 ×2 | + rs partials timing | 1.43–1.49 / 1.79–1.84 | 1.56–1.60 / 1.95–2.00 | 5.99–6.07 / 7.54–7.61 |
| 40518071591 | Xeon 8370C | same | 1.74–1.75 | 1.95–1.97 | 6.86–6.92 |
| 40518485418 | Xeon 8573C | + partials from folds, uninit folds | 1.22–1.24 | 1.37–1.39 | 4.78–4.83 |
| **40518491376 / 40518500999** | **EPYC 7763 ×2** | same | **1.55–1.63** | **1.71–1.78** | **6.53–6.68** |
| 40518496614 | EPYC 9V45 | same | 0.89–0.90 | 0.98–1.02 | 3.41–3.49 |
| 40519260535 / 40519267010 | Xeon 8573C ×2 | + fast witness | 1.33–1.39 | 1.48–1.54 | 5.13–5.31 |
| 40519270572 | Xeon 6973P-C | same | 1.05–1.19 | 1.15–1.21 | 4.04–4.22 |
| 40519551389 | EPYC 9V45 | + trace recording change | 0.84 | 0.91–0.94 | 3.16–3.21 |
| **40519554882 / 40519561565** | **EPYC 7763 ×2** | same (the build of record) | **1.36–1.43** | **1.49–1.57** | **5.47–5.59** |
| 40519565194 | EPYC 9V74 | same | 1.09–1.13 | 1.21–1.25 | 4.61–4.69 |

On every run:
- `SELFTEST pass` (ymm, pclmul and ymm-sim checked);
- every leaf request was `done`, the native `acc` accepted it and the flipped-statement canary was
  rejected;
- every `PROVE-LEAF` reported `acc=accept canary_accept=false`;
- peak RSS was 1.90 GB at m = 30 and 6.19 GB at m = 32, against 11 GiB.

### 2.2 Per phase, EPYC 7763 (run 40519554882, second repetition, seconds)

| phase | m = 30 | m = 32 | P1 m = 30 / m = 32 |
|---|---:|---:|---:|
| witness | 0.080 | 0.512 | 0.21 / 0.43 |
| commit (NTT + Merkle through the service) | 0.262 | 1.152 | 0.30 / 1.27 |
| zerocheck round 1 | 0.295 | 1.164 | 0.30 / 1.21 |
| x₆ round + fold | 0.127 | 0.554 | 0.155 / 0.59 |
| zerocheck tail | 0.063 | 0.245 | 0.09 / 0.34 |
| lincheck | 0.077 | 0.305 | 0.08 / 0.30 |
| shift + IO | 0.022 | 0.088 | 0.02 / 0.09 |
| ring switching (now: targets and the weight table) | 0.136 | 0.552 | 0.25 / 0.98 |
| Ligerito opening | 0.189 | 0.721 | 0.28 / 1.08 |
| trace replay + SIGN | 0.061 | 0.171 | 0.07 / 0.25 |
| **total** (prove-leaf) | **1.315** | **5.469** | 1.75 / 6.55 |
| node surrogate (E1, Lr, E2) | 0.159 | — | — |

The oracle's share (Merkle batches and Fiat–Shamir) is 0.14 s at m = 30 and 0.53 s at m = 32. The
leaf request's `go` → `done` (1.36–1.43 s) is the prove-leaf total plus reading `leaf.json` and
writing the 1.9 MB `proof.bin`. Start-up to `ready` (untimed by the runner) is 0.11–0.30 s, almost
all of it the 1,800 MiB pre-fault.

### 2.3 The node at rev. 3.2's size (54,111 of 65,536 blocks, M ≈ 2^19.96 rows)

There is no node prover yet. The estimate has three parts:
- the m = 30 proof is the node's commitment and bit-level PIOP, because this prover does the same
  work for every block;
- the surrogate adds the element phases at their size (E1 over 2^20 rows, Lr over 2^15, E2 over the
  packed polynomial);
- the two together measure 1.49–1.57 s on the 7763.

Not counted, both **estimates**:
- reading and parsing the two child files (2 × 2 MB): about 10 ms;
- the node's extra witness for the 54,111 stream/WOTS blocks: one BLAKE2s per block, as the leaf's
  chain is.

The time Sel would save by zeroing the eq table outside the used blocks (17 % of blocks) is also not
taken.

## 3. What remains for the 2.8 s link

At 2.92 s the link is 0.12 s above target. The remaining levers, in order of expected gain on
the 7763:

1. **Round 1** (0.30 s, 22 % of a request). The table apply is about two thirds of the kernel and
   the bit-serial GF(2^8) product one third. K's GF(16)² product (pshufb log/exp) cuts the product
   from about 50 to 35 vector ops; that is about −0.04 s (**estimate**). Folding the a-side and
   b-side applies of the constant rows (input/output/constant rows have `b = 1`) would cut part of
   the apply.
2. **Use Sel in node mode:** 11,425 unused blocks cost nothing in the witness, round 1, the x₆
   round and the lincheck fold. That is about −0.1 s on the node (**estimate**, 17 % of those
   phases).
3. **Overlap the Merkle leaf hashing with the NTT's deep phase** (completed subtrees submitted
   while others compute): at most the commit's socket wait, about 0.03–0.05 s (**estimate**).
4. **Ligerito level 0** (0.11 s at m = 30): fused 4-to-1 fold with a small-value second round.

Levers 1 and 2 together cover the 0.12 s (**estimate**).

## 4. Rev. 3.1/3.2 status in the code

| item | status |
|---|---|
| two-level pinned point, `one`/constants as the public target E (the `e`-term), lincheck 14 rounds, shift + 10 collapse rounds, batching inside ring switching, final = level-4 fold + final rounds | as implemented since P1 (rev. 3.1 adopted them) |
| final message zero-padded to 4,096 B at m = 30 (2^5 K elements); 7 final K rounds | not yet: P1 sends 2^5 / 2^7 K unpadded, with 5 / 7 final rounds |
| A.3 grouped π order, A.4 item sequence with dummies, `piSize = 756,496`, `reassemble` from item 1 | not yet; waits for S-0's `gen`/`items` dumps (the KAT) |
| Sel·eq at degree 3 (node), 3 `hashStmt` blocks per slot, `J_z = 4` MBP state vectors in `acc` | node-side; not yet |

## 5. Open questions

1. Is the node's `go` → `done` allowed to include the child-file parsing, or does it count with
   `T_V`? (PROVER.md says the clock covers the request.)
2. For `prover.s`: should the committed `prover.s` be regenerated by the orchestrator's build (the
   sha256 depends on the toolchain host), or is the runner's build-from-sources the reference?

## 6. Second round (after the commit of P2 partial): Sel, E2, the (0,0)+E convention

### 6.1 Changes

- **Sel prototype (timing).** `FLOCK_USED_BLOCKS=U` makes the prover skip blocks `≥ U`:
  - the witness (the unused blocks are zero);
  - round 1 (windows past `2U`);
  - the x₆ round and fold (pairs past `128U`);
  - the lincheck's partial fold (stripes past `U/8`).

  Rev. 3.2's eq·Sel weight lets a node skip these blocks. In this leaf prototype the proof then no
  longer verifies (the leaf statement covers every block), so a run with `U < n` is timing-only:
  `prove-leaf` still reports `acc` but does not exit on reject.
- **E2 batched (`FLOCK_E2_BATCHED=1`).** The node surrogate's E2 lincheck (a degree-2 sumcheck over
  the packed polynomial, `2^23` F) is replaced by one pass adding its template weight to the
  Ligerito weight. This is P1-D6's treatment of ring switching, applied to E2. **It is a proposal**:
  rev. 3.2 keeps E2 as its own sumcheck, so it needs a stage review.
- **(0,0)+E convention (S-E1-M2).** Every constant position of the leaf chain block (h0, the tag
  byte, the zero message bytes, `t`, `f`, and `one`) is now a zero row. Its bit is in the public
  target `E`, which `circuit::e_positions` lists. The verifier's `P^e` on S sums
  `eq(r₀…₇, ⌊p/64⌋)` over E's 1-positions `p` at `σ = p mod 64`. The unit tests (rows
  `a ∧ b = z ⊕ E`, fast witness equal to the tape) and `test-leaf` (portable on the VM; ymm-sim under
  qemu) pass. This change is local only: it has not been run on a runner. Its cost is that of the
  P1 convention (the kernels see the same bits). The per-kind table of rev. 3.3 is not built yet.
- **`prover.s` regenerated** from the current sources (the S-E1 change included): 5,789,391 bytes,
  sha256 `4588296d8ae287e3994fa2aad7e0d106b6d08109d24f0a8de2a5c43d34147b27`, rustc 1.99.0
  (b940084d7 2026-09-28), `build-asm.sh`. It is unchanged by `asm-compat.py`; the linked binary
  passes `selftest`. Per the orchestrator's answer (2), this committed file is the submission. It
  must be regenerated whenever the sources change.
- The crate is 7,124 lines.

### 6.2 Measured, EPYC 7763 (runs 40520772546, 40520781943, 40520788939; build before the S-E1 change)

| request | seconds |
|---|---:|
| stream `leaf` request (`go` → `done`) | 1.34–1.41 |
| m = 30 + node surrogate, all blocks | 1.47–1.53 |
| m = 30 + node surrogate, Sel at 54,111 blocks | 1.40–1.46 |
| m = 30 + node surrogate, Sel + E2 batched | 1.26–1.32 |
| m = 32 tree leaf | 5.47–5.53 |

The surrogate's E2 alone measures 0.14 s, and 0.008 s when batched (the `node_extra E2` lines). A
9V74 run (40520776697) gave 1.11–1.13 s / 1.06–1.10 s / 4.72–4.76 s for the request, the
Sel + E2-batched node and m = 32.

### 6.3 Link and tree on the 7763 (estimates from §6.2)

| configuration | link | tree |
|---|---:|---:|
| Sel only (rev. 3.2 as written) | 1.37 + 1.43 ≈ **2.80 s**: at the target, no margin | — |
| Sel + E2 batched (proposal) | 1.37 + 1.29 ≈ **2.66 s**: 5 % under the target, 14 % under the 3.1 s cap | 64 × 5.50 + 63 × 1.29 ≈ **433 s** |

### 6.4 State and next steps (stopped here at the orchestrator's request)

Branches: every `probe/p2-*` branch is deleted; none remain on origin.

When S-0 delivers the dumps and rev. 3.3 lands:
- the per-kind block table (leaf-chain, stream, hashStmt A/B1/B2, WOTS) with
  `A = Σ_kind Ind_kind ⊗ A₀^kind`; the per-kind transpose walk, measured on the 7763;
- the A.3/A.4 layout with the dummies, `piSize = 756,496`, `reassemble`, and the final message
  padded to 4,096 B; the generator checked byte for byte against the `gen`/`items` dumps;
- the node prover on `compileMux`'s layout, with Sel as real eq·Sel weights in the zerocheck and
  the MBP. That turns the timing-only skip into the proof's own work;
- the `tree` and `node` modes;
- a review decision on batching E2 into the Ligerito weight.

Smaller items, if the margin needs them: the round-1 kernel (the table apply is about two thirds of
it; GF(16)² is about −0.04 s), and overlapping the Merkle leaf hashing with the NTT (−0.03 to
−0.05 s).

## 7. Rev 3.7 layout (resumption)

Status: 2026-10-27, step 1 of P2's resumption (blueprint revision 3.7, `9bd0a82`/`afc2928`). Scope: the
leaf prover and the native verifier of the leaf kinds (`L32`, `m = 32`; the `P30` leaf, `m = 30`;
the native test shapes `m = 25 … 29` carry the `'P'` byte). Not in scope: the node prover, the
`tree`/`node` modes, runner measurements. Every number below is from this VM (32 vCPU, portable
tier: no pclmul; shared with other agents), logs under `logs/P2/r37/` (gitignored).

### 7.1 What changed (files under `submissions/flock-recursive/prover/`; the crate is 8,092 `.rs` lines, was 7,124)

| file | lines (before → after) | change |
|---|---:|---|
| `params.rs` | 147 → 258 | A.3's 18 fields (`F_HDR … F_SIBS`, `FIELD_SIZES`, `field_off`, `PI_SIZE = 757,712`), A.4's counts (`Z1_SQ`, `Z3_ROUNDS`, …, `PF_ROUNDS`), the `m* = 32` ladder's `STAR_SQ/SIB/ROWS`, `KIND_P30`, `leaf_kind_byte`; test `layout_matches_a3` (every field size from the counts) |
| `transcript.rs` | 163 → 272 | `Fs`: `coords(nsq)` (coordinate `2s + c`), `chal_f` (one squeeze, bytes 0…15), `positions(nsq, t, bits)` (always the `m*` count of squeezes), `ask_col`/`ask_node`, an optional item log (`ItemRec`, `items.json`'s form); `Writer` writes each message into its A.3 field, `Reader` reads each field with its own cursor and keeps a flag (`check`; `FLOCK_DEBUG_V` prints the first failed check) |
| `leaf.rs` | 526 → 702 | prover and verifier phase by phase in A.4's order (below); the verifier asks every item whatever `π` holds (as `gen`) and returns the flag; finals after the skeleton |
| `ligerito.rs` | 469 → 512 | messages as coefficients into `F_P1`/`F_PF`; caps into their slots of `F_CAPS` (`cap_slot`, `read_cap_slot`); P2 always `STAR_SQ[i]` squeezes; Q: `STAR_SIB[i]` node queries per position, the missing depths as dummies `0^64` with zero sibling slots; P3 one F squeeze `κ_c`, batching by `κ_c^{q+1}`; the final message padded to `2^7` K and Pf's 7 rounds over the zero-padded message and weight |
| `zerocheck.rs` | 229 → 317 | Z3's `z` part (`z_h1_bytes`, `z_fold_bytes`, `lin_h1`), `e_hi_table` (`Ê(λ, ·)`), `zc_coeffs` (the degree-3 message of `P·eq(r_k, X)·H(X)`) |
| `sumcheck.rs` | 66 → 76 | `coeffs_f`/`coeffs_k`: `(g(0), g(1), g(∞))` → `c₀ ‖ c₁ ‖ c₂` |
| `ringswitch.rs` | 245 → 242 | `weight_table` takes explicit coefficients per claim (claims at one point merged) |
| `main.rs` | 360 → 385 | `test-leaf`: |π| = piSize, the item KAT of the prover's and the verifier's logs; `prove-leaf`: the trace KAT (|tr| and every query length against `items.json`), `reassemble(tr) = π` |
| `items.rs` | new, 218 | `items_seq` (A.4 as a static table) and `reassemble` (A.5); tests `items_seq_kat`, `reassemble_roundtrip` (m = 25, 26) |
| `kat.rs` | new, 191 | `items.json` reader and comparison; tests `items_kat_verifier` (zero proofs of m = 25, 28, 30, 32), `items_kat_prover` (a real m = 25 proof), `chain_kind_rows_kat` |
| `kat-chain-kind.txt` | new, 11 | provenance, BLAKE2s-256 and size of the Lean dump of the chain kind, its zero rows and E's 173 1-positions |
| `prover.s` | regenerated | `build-asm.sh logs/P2/r37/asm`: 6,211,900 bytes, **sha256 `3f5743f2de7239b7e04a667fa4149266166c1805b5aea41c11c7e40415711866`** (rustc 1.99.0; build 29.8 s; linked binary 2,089,312 bytes, sha256 `512a2a2e…`); no machine path in it; `selftest` passes |

Unchanged: `simd.rs`, `field.rs`, `ntt.rs`, `witness.rs`, `circuit.rs` (its rows already were the
chain kind's, see 7.3), `lincheck.rs`, `merkle.rs`, `oracle.rs`, `service.rs`.

The leaf protocol as implemented (prover = verifier order; `m* = 32` sizes everything):
- `hdr = kindByte ‖ m ‖ 0^14 ‖ s`; seed; `stmt = 0x4C ‖ h ‖ enc64 n ‖ 0^87` (checked: tag, `n`,
  zeros, `leafStmt h n = c`); cap₀ (slot `2^9 × 32`).
- **Z**: Z1 10 squeezes, `r_out` = the first `m − 13` coordinates; Z2 `P^{ab}` on `Λ₀…Λ₆₂` (63) ‖
  `P^z` on `Λ` (64) ‖ 16 zero bytes, `λ`; Z3 26 rounds (`m − 6` real) of the summand
  `w·(ab + z) + W_E` (`w = eq(r, ·)`, `W_E = eq(r, ·)·E(λ, ·)` a separate multilinear table),
  messages `c₀ ‖ c₁ ‖ c₂`; Z end `â ‖ b̂`. finZ: `eq(r, r′)(â b̂ + ẑ_Z) + Ŵ_E(λ, r′) = c_Z`.
- **Lc**: L1 `α`; L2 14 rounds (free first claim = `â + α b̂`, finLc (i)); L3 `[v_chain, 0⁶]`; L3β
  `β`. finLc (ii) the walk with the chain kind's rows (= `maskRows` on the base circuit) times
  `v_0`; (iii) `Σ β^i v_i = α₁`.
- **Sh**: S1 15 squeezes (`τ` 0…`m−15`, `θ` 18…27, `κ_s` 28); S2 one 28-round sumcheck (`m − 4`
  real): `m − 14` block rounds of `eq(τ,·)·Out_θ + (shift(τ,·) + κ_s eq(0,·))·In_θ`, then 10
  collapse rounds of `W(pos)·z(r_blk, pos)` over the positions `< 1024`, no absorb between them;
  free first claim = `shiftTarget` (finSh (i)); finSh (ii) `c = w_out α₂ + w_in α₃`.
- **Lr**, **E**: the squeezes asked and ignored, zero rounds, zero `Lr end`/`E end` (checked).
- **RS**: RS0 the 5 × 128 partials (Z at `(λ, r′)`, Lc at `(r_k, r′_blk)`, Sh out and Sh in at
  `(r_pos, 0⁴, r_blk)`, zero), RS1 `r″` = 0…6, `κ` = 7; finRS: `α_j` from the partials, the fifth
  checked zero, `v_RS = Σ_j κ^j Σ_u eq(r″, u) ŝ⁽ʲ⁾_u`; `W = Σ_j κ^j B_j`.
- **B′** one squeeze (unused by a leaf: no E claim, no point claims); Ligerito's first claim is
  `v_RS` (finB′); then P (above).

### 7.2 Item-sequence KAT (A.4)

`items.json` (`logs/S-0/dump/`, read in place, not copied) is compared object by object (phase,
query kind, `len`, `level`, `depth`, `qlen`; the dump's own key order) with:
- the native verifier's log on zero proofs with the headers of m = 25, 28, 30 (`'P'`) and 32 (`'L'`):
  **8,854 items equal** (`items_kat_verifier`; 431 Fiat–Shamir items);
- a real m = 25 proof: the prover's Fiat–Shamir items equal the 431 FS items of `items.json`, the
  verifier's 8,854 items equal (`items_kat_prover`, also run with debug assertions: the prover's
  internal checks of the round sums, the RS partials against a direct pass and Z3's final value pass);
- the static table `items_seq` (`items_seq_kat`);
- every `test-leaf` run (prover FS log and verifier log, m = 25 … 30, 32: `items_kat=pass(8854 items)`)
  and `prove-leaf 30` through the service: **|tr| = 8,854 and every query length equal**
  (`trace_kat=pass`), `reassemble(tr) = π` (`reassemble_eq_pi=true`).

The item sequence is the same for every leaf `m` (the dummies fill it), so the KAT covers `L32` and
the `P30` leaf with the same file.

### 7.3 Block-rows KAT (A.6, the chain kind)

`FR.Kinds.kindRows gateBase Chain.chainTarget` dumped by `logs/P2/r37/kinds/KindsDump.lean` (a
dev-only `lake env lean --run` in `logs/fr-build`, against its built `FRBlockKinds.olean`; 2 min 36 s,
16G scope): one line per position `k a:<set positions> b:<set positions> e:<bit>`, 16,384 lines,
448,616,473 bytes, BLAKE2s-256 `951e62ee…b771`. `chain_kind_rows_kat` renders the same lines from
`circuit.rs` (`row_bitsets`, `e_positions`) and compares the digest, E's 173 1-positions and, when
the dump file is present, every line: **equal** (zero rows 0–255, 512–519, 776–1279, 16000–16383;
E = h0's bits, `0x43`, `t_lo = 33`, `f0 = 0xFFFFFFFF`, `one`). The `irdump` tool was not extended:
its lake project does not build `FRBlockKinds`' closure, and `logs/fr-build` had it built. A KAT of
the other seven kinds is the node prover's (step 3).

### 7.4 Runs (VM, portable tier, 32 threads; `logs/P2/r37/runs-final/`, binary = `prover.s` linked by `build-asm.sh`)

| run | result |
|---|---|
| `cargo test --release` | 27 passed, 1 ignored (the bench) |
| `test-leaf 25 … 30` | accept; flipped statement rejected; flipped proof bytes (3 offsets) rejected; |π| = 757,712; items KAT pass. Prove 0.28 / 0.44 / 0.62 / 1.20 / 2.17 / **3.72 s**, verify 0.031–0.036 s |
| `test-leaf 32` | accept, rejections as above, |π| = 757,712, items KAT pass; prove **15.0 s**, verify 0.046 s, peak RSS 5.25 GB (16G scope) |
| `prove-leaf 30` through `rf-oracle` (fifo stdin, `RF_ORACLE`), 2 reps | total 3.88 / 3.69 s; **|tr| = 8,854**, query lengths = `items.json`; `reassemble(tr) = π`; native `acc` accepts the signed file (in-process and the CLI `acc`), the canary (flipped `c`) is rejected (`V rejects`); file 2,200,695 bytes; peak RSS 1.90 GB (1,800 MiB pre-fault) |
| `leaf` request (`request.py`, n = 2^16) | `done`, `acc=accept`, `canary=reject`; request 4.18 s |

Per phase, m = 30 (`test-leaf`, s): witness 0.047, commit0 0.427, zc_round1 1.369, zc_round2 0.360,
zc_tail 0.421, lincheck 0.047, shift 0.035, ringswitch 0.167, ligerito 0.843. Against the pre-change
binary on this VM (3.64 s, `logs/P2/r37/baseline-test-leaf.txt`): zc_round2 +0.09 s (the `z` table of Z3's new summand is folded with
`â`, `b̂`), zc_tail +0.15 s (its folds and the separate partials pass of RS claim 0 at `r′`); the
RS0 partials no longer come from round 1's banks. These are VM numbers, not the tier of record.

### 7.5 Disagreements between the dump (`gen`) and the prose, and choices where both are silent

1. **Z2 / `lagrangeS`** (S-0 deviation 16 foresaw it): `gen` reads 127 values and asserts the
   last 16 bytes zero; `lagrangeS : AF 127 → F → F` has no operand for `r` (needed for `P^e`) and
   A.8 calls it "the interpolant through `S ∪ Λ`" (128 nodes). The rev. 3.4 form (§2.3, `FRSkip.
   z2Vals`) fits 127 values only as `P^{ab}` on `Λ₀…Λ₆₂` (degree ≤ 126 needs 127 nodes: `S ∪ Λ₀…₆₂`)
   plus `P^z` on `Λ` (64). Native: that message; Z3's first claim = `P^{ab}(λ) + P^z(λ) + P^e(λ)`
   (the sum of Z3's summand, zero on `S`), `P^e` from `r`. S-C/S-0 must pin the message order and
   give `lagrangeS` the `r` operand (or the `P^e` values).
2. **P3 / `κ_c`**: A.4 and `gen` have one squeeze (one F); A.9 `finP` writes `eq(κ_c, j)` over
   `j < tᵢ` (≤ 290, 9 bits), which one F coordinate does not define. Native: powers `κ_c^{j+1}`
   (claim `v + Σ_j κ_c^{j+1} y_j`, error `tᵢ/2^128`). S-G (finP, finPf, pending in the dump) decides.
3. **S2 dummies**: A.3's prose says `P30` zero-fills "the second chain's share of S2"; `gen` puts the
   2 dummy rounds at the end (after the collapse rounds), as for every phase. Native follows `gen`.
4. **θ has 10 coordinates** (S1 18–27, `finSh`'s `slotW`), a digest slot 256 positions. Native:
   `eq(θ, σ)` with `σ < 256` read as a 10-bit index (factor `(1+θ₈)(1+θ₉)` on both sides of every
   link); `slotW`'s implementation is S-C's (pending), the same reading needed there.
5. **Sh's two RS claims**: with one 28-round S2 (no absorb between block and collapse rounds) both
   `ẑ_Sh,out` and `ẑ_Sh,in` are claims on `ẑ` at the one point `(r_pos, r_blk)` with eq inner
   weights (A.9's "the slot weights for Sh" as RS inner weights does not apply after the collapse).
   Native: the same partials twice, one MBP run with coefficient `κ² + κ³`.
6. **`J_z = 5` for a leaf**: the fifth (Lr) claim's partials are asserted zero and it has no weight;
   with 5 the leaf runs 3 MBP programs (Z, Lc, Sh). `finRS` (S-F) is pending in the dump.
7. **`linkW` in a leaf's `finSh`**: the dump has the 8 `linkW` ops for `L` and `P` too; a leaf has no
   link families, so native takes them as 0. The `linkW` implementation must return 0 for leaf kinds.
8. **Pf for `P30`**: "7 real rounds, the final message zero beyond `2^5`" leaves the weight's
   extension to the 2 padding coordinates open. Native: weight zero-padded too, so `finPf` evaluates
   `Ŵ(s, ρ₀…₄)·(1+ρ₅)(1+ρ₆)`. S-G (finPf) must fix the same extension.
9. **§1.2 counts are stale**: "FS items 429 … 8,854 items" (429 + 871 + 7,552 = 8,852); rev. 3.7 has
   431 FS items (A.4, the dump). A.3's/§1.1's `piSize` and fields agree with the dump.
10. **A.3 row 5 / S-0-m3**: L3 absorbs 7 elements (112 B; the leaf's at entry 0); `maskRows` takes 8
    (`blockKinds`; leaf `[v₀, 0⁷]`, node `[0, v₀…v₆]`). Consistent once read so; noted only.
11. Pending finals: `finRS`, `finE`, `finB′`, `finP`, `finPf` are placeholders in the dump (S-F,
    S-G); the native verifier implements them from A.9's prose with the choices 2, 5, 6, 8.

### 7.6 Open questions / for the node prover (step 3)

- Items 1, 2, 4, 5, 8 above decide byte formats or values both the leaf and the node use; the leaf
  code isolates them (`z2_value`, `ligerito::kappa_powers`, `theta_eq`, `claim_points`, the Pf
  padding), so a ruling is a local change, but the proofs change with it.
- The node prover needs: the KAT of the other seven kinds' rows and targets (the same dump script
  with `allKinds`; the dump is 448 MB per kind, so digests), `compileMux`'s M layout dump (A.7), the
  `linkW`/`slotW`/`evalM`/`evalL` implementations (S-C/S-E2), and the finals S-F/S-G are writing.
  `items.rs`'s `reassemble` is ready for reading child proofs from their traces.
- Prover cost of rev. 3.7 on the leaf path: Z3's `z` part and the separate RS-0 partials pass add
  ≈ 0.2 s at m = 30 on the VM; folding `z` into round 1's kernel (it already reads the bits) would
  remove most of it.

## 8. Rev 3.7 leaf on the 7763 (step 2 of the resumption)

Run 40554199135 (EPYC 7763) used the runner-assembled `prover.s` of §7's sources; the requests
went through `rf-oracle`. Every proof had |π| = 757,712 and |tr| = 8,854. The native `acc`
accepted every one and rejected every canary.

| request | rev 3.7 (this run) | P2 §6 (pre-3.7 layout) |
|---|---:|---:|
| stream `leaf` request (`go` → `done`) | **1.62–1.63 s** | 1.34–1.41 s |
| prove-leaf m = 30 | 1.61–1.65 s | 1.31–1.36 s |
| prove-leaf m = 32 | **6.51–6.64 s** | 5.47–5.53 s |
| peak RSS m = 30 / 32 | 1.90 / 6.19 GB | same |

An EPYC 9V74 (run 40554204584) measured 1.31–1.33 s, 1.28–1.32 s and 5.44–5.54 s.

**Per phase at m = 30 (7763):** witness 0.082, commit 0.269, round 1 0.303, x₆ round 0.250,
tail 0.198, lincheck 0.080, shift 0.023, ring switch 0.147, Ligerito 0.196, trace 0.057.

**The regression is in the zerocheck:**
- x₆ round: 0.128 → 0.250 s.
- tail: 0.063 → 0.198 s.
- At m = 32 both together: +1.0 s.

Rev 3.7's Z3 summand carries the z part, so the tail sumcheck folds three tables, `a`, `b` and the
λ-folded `z` (§7.5). The paper's "skipping c" (P1's protocol) kept z out of the tail: the c-claim was
read off `P^z(λ)` directly. This one change costs about 0.26 s per m = 30 request and 1.0 s per
m = 32 leaf.

**Estimates with the §6.2 node measurements:**
- Stream link ≈ 1.63 + (1.29…1.43) + ≈ 0.26 (the same Z3 cost in the node) ≈ **3.2–3.3 s**. That
  is over the 2.8 s target and the ≈ 3.1 s cap.
- Tree ≈ 64 × 6.6 + 63 × ≈ 1.6 ≈ **525 s**. That is over the 500 s target but under the 600 s cap.

**Recommendation for review:** restore "skipping c" in Z3 (rev 3.7's summand with `ĉ` read from
`P^z`, as in rev. 3.1 / P1). If that is not possible, the z table must be folded inside the x₆ round
kernel; that saves the extra pass but not the third table's products.

**Steps 3–4 are not started.** §7.6 lists what blocks the node prover:
- rulings on the Z2 format, `κ_c`, θ, the Sh claims and the Pf padding;
- the S-F/S-G finals, which are placeholders;
- the `slotW`/`linkW`/`evalM`/`evalL` implementations;
- the rows/E KAT for the other seven kinds;
- the `compileMux` M-layout dump.

The `tree` and `node` modes follow the node prover. `prover.s` is regenerated for §7's sources
(sha256 `3f5743f2…`). Probe branches p2-20 and p2-21 are deleted.

## 9. Rev 3.9 (resumption 2)

Status: 2026-10-27. Blueprint revision 3.9 (`757dfa8`; stage-review changes 6–9). The dump is
`logs/S-0/dump/` of 18:15 (summary: 8,874 items, `piSize` 755,680, field sizes as below). Scope and
rules as in §7: leaf prover and native `acc`, this VM only (32 vCPU, portable tier, shared), logs
under `logs/P2/r39/` (gitignored).

### 9.1 What changed (crate 7,974 `.rs` lines)

| file | lines (§7 → now) | change |
|---|---:|---|
| `params.rs` | 258 → 262 | `FIELD_SIZES` (L2 + L3 800, RS0 8,192), `PI_SIZE = 755,680`, `L3_KINDS = 8`, `RS_CLAIMS = 4`, `P3_SQ = 5`, `KAPPA_C = 9` |
| `leaf.rs` | 702 → 663 | **skip-c**: Z2 sends `P^z|_Λ` (64) then `P^{ab}|_{Λ₀…₆₂}` (63); `z2_value` returns `(P^{ab}*(λ), P^z*(λ))` (`lagrangeS vals λ pe`, `targetS`); Z3 on `eq(r,·)·a_λ·b_λ` only (initial claim `P^{ab}*(λ)`); `finZ`: `eq(r, r′)·â·b̂ = c_Z`; the c-claim `ẑ(r, λ)` is RS claim 0 with inner weights `eqZ λ ρ₁` (Lagrange at λ ⊗ `eq(ρ₁, bit 6)`), its slices from round 1's banks (no pass over `z`), bound by `α_Z = P^z*(λ)`. L3 absorbs 8 values (`[v_chain, 0⁷]`), `v_β` over 8. Sh is one RS claim: `c_Sh = (w_out + w_in)·α_Sh`. RS0 `4 × 128` (the fourth zero, checked); `v_RS = Σ_{j<3} κ^j T_j`; `Ŵ` by `rs_weight` (3 points). The `z`/`W_E` tables of §7 are gone |
| `ringswitch.rs` | 242 → 242 | `FRRingSwitch`'s form: `phi` (`Φ_{r″}`, stages `a ← a + r″_p a^{2^{2^{6−p}}}`), `phi_coeffs` (`phiTable`, 128 `c_k`), `switched` (`rsT`: `T = Σ_v b_v Φ(s_v)`), byte tables of `Φ(b_v)` for the prover's `W = Σ_j κ^j Φ∘eq(hi_j, ·)`, `rs_weight` (`Σ_j κ^j Σ_k c_k eq(hi_j^{2^k}, ρ)`); the tensor-algebra target and the MBP are removed; test `rs_weight_and_identity` (`Φ` = its coefficient table; `rs_weight` = the MLE of the prover's table; `Σ_y W f = κ T` on honest slices) |
| `ligerito.rs` | 512 → 508 | P3: `κ_c` = the first 9 coordinates of 5 squeezes; consistency coefficients `eq(κ_c, bits₉(q))`, `q < tᵢ` (claim `v + Σ_q eq(κ_c, q) y_q`, weight likewise in `weight_eval`) |
| `zerocheck.rs` | 317 → 238 | the §7 `z`/`E` table kernels removed; `zc_coeffs` kept (Z3's message) |
| `items.rs`, `kat.rs`, `main.rs` | 218, 191, 385 | P3 5 squeezes; counts 8,874 / 451 FS items in the tests and comments |
| `prover.s` | regenerated | 6,003,623 bytes, **sha256 `f3385c4db55143cdfd3e93873ca62a453b20d27bca5950da0194c0d01f2262a3`** (rustc 1.99.0, `build-asm.sh logs/P2/r39/asm`, 28.4 s); linked binary 2,050,768 bytes, sha256 `35535365…9c24`; no machine path; `selftest` pass |

### 9.2 KATs

- `items.json` (3.9 dump): the native verifier's items on zero proofs of m = 25, 28, 30, 32 and on a
  real m = 25 proof, the prover's 451 Fiat–Shamir items, and the static `items_seq`: **8,874 items
  equal** (`items_kat_verifier`, `items_kat_prover`, `items_seq_kat`; the item tests and
  `reassemble_roundtrip` also pass with debug assertions, including the check `α_Z = P^z*(λ)` on
  the bank slices and Z3's final `â·b̂`).
- Chain-kind rows and E: `FRBlockKinds`, `FRBlockChain` and the BLAKE2s modules are unchanged since
  `afc2928` (3.8's `free` kind is a new, node-only kind), so the §7.3 dump stands; `chain_kind_rows_kat`
  re-run: equal line by line.
- `cargo test --release`: 27 passed, 1 ignored (the bench).

### 9.3 Runs (`logs/P2/r39/runs/`, binary = the `prover.s` above, linked by `build-asm.sh`)

| run | result |
|---|---|
| `test-leaf 25 … 30` | accept; flipped statement and flipped bytes rejected; |π| = 755,680; items KAT pass; prove 0.29 / 0.41 / 0.64 / 1.03 / 1.84 / 3.47 s |
| `test-leaf 30 --reps 3` | prove 3.79 / 3.34 / 3.36 s |
| `test-leaf 32` | accept, rejections, |π| = 755,680, items KAT pass; prove **13.3 s** (§7: 15.0 s), peak RSS 5.25 GB |
| `prove-leaf 30` via `rf-oracle`, 2 reps | total 3.80 / 3.77 s; **|tr| = 8,874**, query lengths = `items.json`, `reassemble(tr) = π`; `acc` accepts (in-process and CLI), canary rejected; file 2,198,231 B |
| `leaf` request (n = 2^16) | done, `acc=accept`, `canary=reject`; 3.87 s |

**The zerocheck at m = 30** (VM, s; `test-leaf`, FLOCK_VERBOSE):

| phase | rev 3.9 (3 reps) | rev 3.7 (§7.4) | pre-3.7 (`logs/P2/r37/baseline-test-leaf.txt`) | 7763 rev 3.7 (§8) |
|---|---:|---:|---:|---:|
| x₆ round (`zc_round2`) | 0.249–0.288 | 0.360 | 0.270 | 0.250 |
| tail (`zc_tail`) | 0.250–0.269 | 0.421 | 0.269 | 0.198 |

At m = 32: x₆ round 1.03 s, tail 0.98 s (§7: 1.50, 1.61). **Skip-c removed the §7 z-table cost
locally**: both phases are back at the pre-3.7 level on this VM (the 7763 numbers are a different
machine; the runner measurement is the orchestrator's). Ring switching with `Φ` costs the same as
before (0.17–0.18 s), the verifier 0.035–0.040 s.

### 9.4 Disagreements left

1. **3.9's "Margins" line** says `piSize` 755,664 and 8,870 items; the note under it, §8 of the
   stage-review changes, the dump and the orchestrator say **755,680 / 8,874**. Implemented: the
   dump.
2. **The dump predates 3.9's op signatures**: `finSh` calls `shiftTarget τ θ` (no `bnd`), and the
   S-F/S-G finals (`finRS`, `finE`, `finB′`, `finP`, `finPf`) are still placeholders in `ops-*.txt`.
   The item sequence does not depend on them. Natively they follow A.9 (3.9): the column checks
   define `α_j`; `v_RS = Σ κ^j T_j`; `rsWeight` with 3 points; `eq(κ_c, bits₉(j))` with
   coefficient 1 on the running claim; `P30`'s zero-padded Pf weight; `bnd = (s, h)`.
3. **`Φ_{r″}`'s coefficient order** (`r″` = RS1 coordinates 0…6 as `f_0 … f_6`, stage `p` with
   shift `2^{6−p}`, as `FRRingSwitch.Phi`) cannot be checked against the dump until `finRS`/`finPf`
   are dumped; the same holds for `eqZ λ ρ₁`'s bit order (`v = σ + 64·b`).
4. Prose leftovers (no effect): §2.3 step 8 still says the verifier evaluates `W` "by the MBP";
   step 3 still speaks of "≤ 7 kinds" and "MBP runs".

## 10. Rev 3.9 on the 7763 (resumption 2, step 2), and the node estimate

**Run 40561971516, EPYC 7763.** Built from the runner-assembled `prover.s` of §9's sources and run
through `rf-oracle`. Every proof is 755,680 bytes with a trace of 8,874 entries; the native `acc`
accepted each one and rejected every canary.

| request | rev 3.9 | rev 3.7 (§8) | pre-3.7 (§6) |
|---|---:|---:|---:|
| stream `leaf` request (`go` → `done`) | **1.37–1.43 s** | 1.62–1.63 s | 1.34–1.41 s |
| prove-leaf m = 30 | 1.32 s | 1.61–1.65 s | 1.31–1.36 s |
| prove-leaf m = 32 | **5.58 s** | 6.51–6.64 s | 5.47–5.53 s |
| peak RSS m = 30 / 32 | 1.90 / 6.19 GB | same | same |

Per phase on the 7763, in seconds:

| phase | m = 30 | m = 32 |
|---|---:|---:|
| witness | 0.082 | 0.536 |
| commit | 0.269 | 1.135 |
| round 1 | 0.286 | 1.207 |
| x₆ round | **0.131** | 0.567 |
| tail | **0.065** | 0.261 |
| lincheck | 0.078 | 0.329 |
| shift | 0.022 | 0.089 |
| ring switch | 0.133 | 0.528 |
| Ligerito | 0.195 | 0.746 |

**Skip-c recovers the rev 3.7 regression.** The x₆ round and the tail are back at their pre-3.7
values, against the §8 rev 3.7 figures of 0.250 and 0.198 s at m = 30. The targets were a stream
request of ≈ 1.36 s and an m = 32 leaf of ≈ 5.5 s; this run gives 1.37–1.43 s and 5.58 s.

An EPYC 9V45 run (40561976342) gave 0.86–0.87 s for the request and 3.26 s at m = 32.

**Node at 3.9's size: an estimate, because the node prover is not built.**
- The finals `finP` and `finPf` (S-G) are pending, and §9.4 lists what remains open.
- The node's commitment and bit-level PIOP cost what the m = 30 leaf costs: about 1.32 s. With
  Sel ≡ 1 the free blocks are proved too, as a = b = z, so no blocks are skipped.
- Add E1 over 2^20.24 rows, Lr, and E2 batched into the Ligerito weight. §6.2 measured these at
  0.027 s (E2 batched, 2^20 rows). Scaling, about 0.03–0.04 s.
- Add reading and parsing the two child files, about 0.01 s.
- Node request ≈ 1.32 + 0.04 + 0.01 + the request overhead (≈ 0.05, from the leaf's request minus
  its prove-leaf) ≈ **1.42 s**.

The two caps, estimated:
- **Stream link** ≈ 1.40 + 1.42 ≈ **2.8 s**. That is at the target, about 10 % under the ≈ 3.1 s cap.
- **Tree** ≈ 64 × 5.58 + 63 × 1.37 ≈ 357 + 86 ≈ **445 s**. That meets the 500 s target.

**Next.** Once S-G's finals are dumped:
- build the node prover on `compileMux`'s layout (uniform P30, gated stmt rows, WOTS digit selectors,
  mirror cells);
- check the Φ coefficient order and eqZ's bit order against the Lean finals (§9.4);
- add the `tree`/`node` modes;
- regenerate `prover.s`;
- measure the link on a 7763.

The probe branches p2-22 and p2-23 are deleted; no `probe/p2-*` branch remains.

## 11. Finals, node prover, modes (resumption 3)

Status: 2026-10-27, partial: **item 1 (finals) done; items 2–3 (node prover, `node`/`tree` modes,
run.sh) blocked** on inputs that do not exist yet (11.3). Dump used: `logs/S-G/dump/` (21:38;
105,700 ops, 8,874 items, `piSize` 755,680, `ops-L.txt` sha256 `d9652595…`, no pending finals).
Logs: `logs/P2/r311/`.

### 11.1 Changes (crate 8,541 `.rs` lines)

| file | lines | change |
|---|---:|---|
| `ir.rs` | new, 537 | an interpreter of the dumped Lean program (`irdump ops L\|P`, `FRVIR.evalOp`, all 55 op names of the dump) with native op implementations mirroring S-F2's `FRVerifierImpl` (`lagrangeSI`, `eqZI`, `rowWI`, `maskRows` with A.6's nine kinds in `blockKinds` order, `walkA/B` on the circuit walk, `phiRSI`, `rsWeightI` over K points, `tensorWI` = `ntt::xhat`, `slotWI`, `shiftTargetI`, `targetSLeafI`, `shiftEq`, `eqPoint`); `linkW = 0` (leaf kinds); `evalL`/`evalMK` return zeros and are reported (`node_matrices_used`); test `ir_kat_p30` |
| `main.rs` | 385 → 397 | `test-leaf` runs the dumped program of its kind (m = 30 `P`, m = 32 `L`) on the proof and on the canary (`lean_ir=…`); a rejection fails the mode |
| `kat.rs` | 191 → 209 | `find_ir_dump` (`FLOCK_IR_DUMP`, else `logs/S-G/dump` above the working directory) |
| `prover.s` | regenerated | 6,416,110 bytes, **sha256 `f3e33f44a88be73e562d58a4aa0edc6a9f95705c0f44d284166a65444ff2f7a6`** (`build-asm.sh logs/P2/r311/asm`, 32.3 s); linked binary sha256 `489b868c…1334`; no machine path; `selftest` pass |

No change to the prover or the native verifier was needed: the dumped finals accept their proofs.

### 11.2 The finals KAT

- **The whole dumped program** (skeleton and every final: `finRS`, `finZ`, `finLc`, `finSh`,
  `finLr`, `finE`, `finB′`, `finP 0…4`, `finPf`) run by `ir.rs` on native proofs: **accepts** an
  m = 30 `P30` proof (`ir_kat_p30`, `test-leaf 30` with the `prover.s` binary) and an m = 32 `L32`
  proof (`test-leaf 32`); **rejects** the canary (flipped `c`) for both; asks exactly the 8,874
  items. `ir_kat_p30` also flips one byte at the start, the middle and the end of each of the 18
  fields: the native verifier and the dumped program both reject all 54.
- **Φ's coefficient order and `eqZ`'s bit order (§9.4 item 3): settled.** The dump's `finRS` packs
  `r″` = RS1's coordinates 0…6 in order (registers r1679, r1680, r1682, … , r1688; `κ` = coordinate
  7, r1689) and computes `T_j = Σ_i b_i·phiRS(r″, s_{j,i})` with `b_i` the one-bit constants
  `0x01, 0x02, 0x04, …` (A.7's basis), Horner in `κ`, the fourth `T` zeroed by `keep false`; `eqZ λ ρ₁`
  weights slice `i` by `L_{i mod 64}(λ)·eq(ρ₁, bit 6 of i)`. The native verifier and prover use the
  same orders, and `phiRS` follows `FRRingSwitch.phiApply` (stage `p` = `(2^{6−p}, r″_p)`), so
  `α_Z = P^z*(λ)` and `finPf`'s `rsWeight` both pass on honest proofs.
- What the dumped program does that the native verifier does not spell out the same way (no
  verdict difference): `finB′` adds `κ′·v_E` (zero for a leaf: E end is zero) and the public cells
  under `keep false`; `finPf` evaluates `evalMK` at E2's point and the `L`/`M` terms under `keep
  false`; `shiftTarget` gets `κ_s` from outside the op (S-F2's interface gap; `ir.rs` reads S1's
  coordinate 28 at τ's first register + 42).
- **Disagreements: none for the leaf kinds.** Not covered: the `N` program (needs `evalM`, `evalMK`,
  `evalL`, `linkW`, `targetS` of the node), see 11.3.

### 11.3 The node prover: what is missing

The node's proof cannot be built exactly, nor checked by a native `acc` against the Lean program, from
what exists in the worktree:

1. **M rows and cell map.** The E phase's matrices are `compileMux (gen fin .mux)`'s rows (A.7: "the
   exact bases are the output of `compileMux` and are pinned by its dump"). No such dump exists:
   `irdump` prints items, ops and the summary; `logs/S-G/dump/ops-M.txt` is the mux program's op
   list, not its compiled rows. Needed: a dump of the sparse `A_M`, `B_M`, `C_M` entries `(row, cell,
   coef)` (1,237,344 rows) **and** the map from the program's registers/imports to M cells, so the
   prover can fill the M region of `f` from the children's replayed verifiers (and `evalM`/`evalMK`
   natively, as S-F2's `evalMKI` reads `Layout.nodeRows fin`).
2. **L rows and cell map** (`lRows`, `FRNodeLayout`'s L layout): for Lr's R1CS and `evalL`.
3. **`nodeLayout`'s intervals**: the block intervals of the nine kinds (`Ind_kind`, incl. `free` and
   `WM`) and the link families' slot maps (`linkW`), as a dump; without them Lc's per-kind folds,
   Sh's link terms and the H witness's placement are not exact.
4. **The Lr point** is provisional (S-G-RESULT §6).
5. **Op interface gaps** (S-F2): `targetS`, `slotW`, `linkW` need the kind; `shiftTarget` needs `κ_s`.

A stubbed node prover (stub matrices, self-consistent with a stub native `acc`) is possible, but it
would be a second protocol to maintain and its "acceptance" would not mean the Lean `acc` accepts; the
timing surrogate `FLOCK_NODE_SHAPE` (§2, §6) already measures the node's extra phases. I stopped
here (TRACK-RULES' Pace: blocked) rather than build that. With items 1–3 dumped, the node prover is a
port with KATs: H blocks (stream, hashStmt, WOTS, key leaf, path, mirror) from the children's traces
and signatures, the M region from the replayed verifiers, the L bits, the shared PIOP plus E/Lr, and
`ir.rs` extended with `evalM/MK/L` from the dumped rows to check the `N` program.

**Modes**: `node` and `tree` still exit 2 (they need the node prover); `run.sh` is unchanged (the stream
link and tree measurements need them). The m = 32 leaf and the `leaf` request are measurable now with
the current `run.sh` (`probe/p2-prover/run.sh OUTDIR`, env `P2_LEAF_REQS`, `P2_M32`).

### 11.4 Local runs (VM, portable, 32 threads; `logs/P2/r311/`)

| run | result |
|---|---|
| `cargo test --release` | 28 passed, 1 ignored |
| `test-leaf 30` (prover.s binary) | accept, rejections, items KAT pass, `lean_ir=accept`, canary rejected; prove 3.64 s |
| `test-leaf 32` | accept, `lean_ir=accept`, canary rejected; prove 16.1 s (shared VM), 5.25 GB |
| `prove-leaf 30` via `rf-oracle` | |tr| = 8,874, query lengths equal, `acc` accept, canary reject |
