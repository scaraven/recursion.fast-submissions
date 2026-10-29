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

## 12. Node prover (resumption 4)

Status: 2026-10-28, partial. **Done: revision 3.13 for the leaf kinds, dump-exact (INT-2's dump),
and a node-phase timing on the dumped node circuit. Not done: the N30 node prover, the `node`/`tree`
modes and the stream-link measurement**, for the reasons in 12.4. Dumps: `logs/INT-2/dump/` (3.13:
105,828 ops, asks = items = 8,891, piSize 797,904) and `logs/S-E5/nodedump/` (169 MB). Logs:
`logs/P2/r312/`.

### 12.1 Changes (crate 8,811 `.rs` lines)

| file | lines | change |
|---|---:|---|
| `params.rs` | 262 → 270 | 3.13 fields (`F_E = 9`, `F_EEND = 10`, `F_RS0 = 11`; sizes `[…, 720, 48, 2144, 48, 8192, …, 487504, 241664]`), `PI_SIZE = 797,904`, `E4_ROUNDS = 23`, `E4END_LEN = 32`, `COL_PAD = 48` |
| `leaf.rs` | 663 → 678 | phase order `… Lr1, Lr2, Lr end, Lr3, E1, E2, E end, E3, E4, E4 end, RS0, RS1, B′` (Lr4 withdrawn); a leaf's E4 rounds and E4 end are zero (finE (v): `f̂(r′) = α₄ = 0` and the zero half); the node-shape hook uses `nodeshape.rs` when `FLOCK_NODE_ROWS` is set |
| `ligerito.rs`, `merkle.rs`, `transcript.rs` | 508 → 509, 60 → 62, 272 → 275 | column items padded with 48 zero bytes (query 8 + 16·rows + 48; field 16 holds the padded columns; the verifier hashes the π bytes as the Lean `askCol` does) |
| `items.rs`, `kat.rs`, `ir.rs`, `main.rs` | 219, 209, 551, 401 | the 3.13 item table; KATs read `logs/INT-2/dump`; `ir.rs` gains `walkAB` (rev. 3.12's fused walk, two outputs) |
| `nodeshape.rs` | new, 222 | timing surrogate on the dumped node circuit (12.3) |
| `prover.s` | regenerated | 6,598,157 bytes, **sha256 `db43cee035fa3311d4c76cc6a4a1c4e38e55e9a1449c82898d8d0647d0fde8ea`** (`build-asm.sh logs/P2/r312/asm`); linked binary sha256 `2c8f58d8…f2fd`; no machine path; `selftest` pass |

The π offsets match INT-2's table (Lr end 6,368; E 6,416, E4 end at +2,112; E end 8,560; RS0 8,608;
P1 16,800; Pf 18,912; caps 19,584; final 64,640; columns 68,736; siblings 556,240).

### 12.2 Leaf KATs and runs (3.13)

- Items: the native verifier on zero proofs (m = 25, 28, 30, 32), a real m = 25 proof (prover FS
  log and verifier log) and the static table: **8,891 items equal** (468 FS).
- The dumped 3.13 program (`ir.rs`, all finals): **accepts** native m = 30 (`P`) and m = 32 (`L`)
  proofs, rejects the canary, asks 8,891 items; `ir_kat_p30`'s 54 single-byte flips rejected by both
  the native verifier and the dumped program. No disagreement.
- `cargo test --release`: 28 passed, 1 ignored. `test-leaf 25, 28, 30, 32` pass (|π| = 797,904).
  m = 30 prove 3.41 s; m = 32 prove 13.1 s, **peak RSS 5.37 GB** (`/usr/bin/time -v`; cap 11 GB).
- `prove-leaf 30` through `rf-oracle` (prover.s binary, 2 reps): total 3.98 / 3.81 s, |tr| = 8,891,
  query lengths = `items.json`, `reassemble(tr) = π`, `acc` accepts (in-process and CLI), canary
  rejected; the `leaf` request (n = 2^16): done, accept, canary reject, **3.97 s on the VM**.

### 12.3 The node's E/Lr work on the dumped circuit (VM, timing only)

`nodeshape.rs` loads `mrows-0/1.txt` and `lrows.txt` (2,652,430 M entries, 49,320 L entries; 1.9 s,
before the clock), builds the transpose once, and runs on the packed witness `f` (`2^23` F, the
node's size): Lr (matrix products + 15 degree-3 rounds), E2 (`A_M f`, `B_M f`, `C_M f` over `2^21`
rows + 21 degree-3 rounds), E4 (the table `(A_M + κB_M + κ²C_M)ᵀ eq(r_E2) + κ³(L)ᵀ eq(r_Lr)` over the
`2^23` cells, one gather, + the 23-round lincheck). Measured inside `prove-leaf 30` (2 reps,
`logs/P2/r312/node2/`): **E2 0.27–0.28 s, E4 0.53–0.56 s, Lr 0.015 s**; prove-leaf with them 4.26–4.55 s
(without: 3.81–3.98 s); peak RSS 2.11 GB (incl. the loaded dump).

**Estimates (not measurements):**
- The dumped rows are S-E5's compiled ones, 282,319 per slot; the circuit model has 968,943 per slot
  (the templates still missing). Only the sparse products and the gather scale with the entries.
- Node on the VM ≈ the m = 30 PIOP (≈ 3.4 s) + E/Lr ≈ 0.8 s + the node witness (H blocks ≈ 46 k
  compressions ≈ 2× the leaf's witness; the M replay of two children's verifiers ≈ 2 × 0.04 s plus a
  row solve) ≈ **4.4–4.6 s VM**.
- 7763 projection with the leaf ratio: VM `leaf` request 3.87–3.97 s against the 7763's 1.37–1.43 s
  (§10), ratio ≈ 2.75. Node ≈ 4.5 / 2.75 ≈ **1.6 s**, link ≈ 1.4 + 1.6 ≈ **3.0 s** against the ≈ 3.1 s
  cap. The coordinator's ≈ 2.94 s sits within that range. E4 is the largest added phase (a 2^23
  degree-2 sumcheck on two tables); fusing its first round with the gather is the obvious cut.

### 12.4 Why the node prover is not built, and what it needs

1. **The node dump is not at 3.13.** `logs/S-E5/nodedump/`'s register map (`mregs`) is the 3.12 mux
   program: its untracked registers fall on `piField`/`idx`/`shrN` there, but on `askNode`/
   `piDigest`/… in INT-2's 3.13 `ops-M.txt`. It was also compiled with `finPf` pending
   (`NodeDumpT`: `fins = finC pending`), so the dump has no `finPf` rows. A 3.13 child replayed against
   it cannot satisfy its rows. The coordinator's re-dump from `logs/fr-build` is the input. The loaders
   (`nodeshape::load`, path from `FLOCK_NODE_ROWS`) already read the format, so the re-dump needs no
   code change.
2. **The dumped M rows cover 282 k of the model's 969 k rows per slot.** The templates S-E has not
   generated (child `evalM`/`evalL` replays, `walkAB`, `tensorW`, `rsWeight`, `kindInd`, `rowW`,
   `shiftTarget`, `linkW`) have no rows yet. Their output registers are not bound by any row.
3. **The import cells of M are not tied to H** (QUEUE: "the pack map from H trace/stream cells to the
   M imports", S-E). So the circuit does not yet say which H stream cells the M imports alias. The
   prover would fill both copies consistently, but the H side has no fixed form to KAT.
4. **Node `targetS`/`linkW`** (S-CN, running): the node's Z target E over nine kinds and the 7 link
   families are unspecified in code. A native placeholder is possible, but neither the Lean program
   nor `ir.rs` on `ops-N` could check it until `implC` has them.
5. **`evalM`/`evalL` for `ir.rs` on `ops-N`**: the dumped rows are enough (`nodeshape`'s matrices),
   but only after 1–2 do they match the circuit `ops-N` evaluates.

With 1–4 delivered, the prover is:
- the H witness (stream blocks of both traces, `hashStmt`, WOTS with digit selectors, key leaf, path,
  the WM mirrors at A.6's offsets);
- the L bits;
- the M region: the mux program run on each child by `ir.rs` (kind from `hdr`), registers written per
  `mregs`, `maux` columns, template locals by a forward row solve;
- the shared PIOP with nine kinds (`free` rows identity), the link families, Lr, E2/E4 on the loaded
  matrices.

Then `ir.rs` on `ops-N` with `evalM`/`evalL` from the same rows is the end-to-end check.

**Modes and run.sh:** `node` and `tree` still exit 2. `run.sh` is unchanged. Its leaf, `prove-leaf
30` and m = 32 measurements run as before. The node-shape run on the dumped circuit needs the 169 MB
node dump on the runner (it lives in `logs/`, gitignored), so it stays local:

```
FLOCK_NODE_SHAPE=1 FLOCK_NODE_ROWS=$PWD/logs/S-E5/nodedump REPS=2 logs/P2/r37/run-service.sh $PWD/<prover> OUTDIR 30
```

## 13. Pass 5 (revision 4.0): threads, segments of variable length, the aggregate, no `proofCap`

Status: 2026-10-28, track P2′ (blueprint revision 4.0, changes 25; core pin `6d05d00`). Scope:
items 1–6 of the brief, on the segment (leaf) prover; the node prover and the `first`/`step` modes
wait for S-0′'s and S-E12′'s dumps (13.9). Logs: `logs/P2/r40/` (VM) and `logs/P2/run-<id>/`
(runners, EPYC 7763, 4 vCPU); probe branches `probe/p2t-1` … `p2t-4`, each one commit on HEAD with
`prover/`, `probe/p2t-prover/` and `.github/probe.conf`; all deleted after their run.

### 13.1 The runner's CPUs (item 1)

- **The prover is not pinned.** In the PR #20 harness only the checks run under `taskset` (one core,
  `rfh/checks.py`); the prover's `Sandbox(…)` calls (`rfh/prover.py` lines 161, 184, 236) pass no
  `cpus`, and PROVER.md §2 says "every CPU of the machine (shared with the service)". There is no
  CPU cgroup limit.
- **Measured** (probe p2t-1, run 40717768596): `nproc` 4, affinity `0–3`, `Cpus_allowed_list 0-3`,
  `cpu.max` = `max 100000`. The machine is an EPYC 7763 with **2 cores × 2 SMT threads** and 1 MiB L2
  per core. Every one of the 20+ earlier P2 runs reports 4 CPUs.
- The thread count stays `available_parallelism()` = 4 (`FLOCK_THREADS` overrides it).

### 13.2 Threads (item 2): already there; what 4 vCPUs give

**The prover has been multi-threaded since P1** (`par.rs`: a persistent pool with nested jobs;
the NTT/RS encoding, Merkle leaf batches, every sumcheck table, the zerocheck kernels, the ring-switch
table and the witness are all parallel). Every runner figure in §2–§12 is `threads=4`.

**The blueprint double-counts the threads.** §0 and changes 25 (b), (e) read P2's 5.47 s per `2^18`
(7763) as a one-thread VM figure and then assume ×2.5 from 4 threads. 5.47 s already is the
4-thread runner figure.

Thread scaling, `prove-leaf` through `rf-oracle` on the 7763, total = prove + trace + SIGN, 2 reps
(runs 40717768596 and 40722323237):

| threads | m = 32, n = 2^18 (s) | m = 31, n = 2^17 (s) | speed-up (m = 32) |
|---:|---:|---:|---:|
| 1 | 12.93–13.04 | 6.38–6.46 | 1 |
| 2 | 6.83–6.99 | 3.36–3.46 | ×1.87 |
| 4 | 5.48–5.69 | 2.73–2.85 | **×2.34** |
| 8 | 5.61–5.71 | — | ×2.29 |

Per phase at m = 32 (1 / 2 / 4 threads, s): witness 2.23 / 1.20 / 0.53; commit 2.41 / 1.35 / 1.12;
round 1 2.91 / 1.42 / 1.20; x₆ round 1.17 / 0.59 / 0.56; tail 0.59 / 0.30 / 0.25; lincheck 0.65 /
0.33 / 0.30; ring switch 1.09 / 0.55 / 0.53; Ligerito 1.45 / 0.78 / 0.74.

- From 2 to 4 threads only the witness gains (scalar BLAKE2s, ×2.3). The vector phases are bound by
  the two cores' vector units: an SMT sibling adds nothing to them.
- **×2.5 at 4 threads is not reachable on this runner.** Threads have reached their limit; what is
  left is the arithmetic itself.
- The VM (QEMU, 32 vCPU, no pclmulqdq, so the portable tier) is compute-bound and scales linearly:
  m = 32 at 1 / 2 / 4 threads is 248.6 / 126.7 / 64.9 s (`logs/P2/r40/scale-base/`). It says nothing
  about the runner.

**A bug, fixed: a thread count that is not a power of two gave a wrong proof.**
- Symptom: with `FLOCK_THREADS=3` (also 5, 6, 7) the native verifier rejected the proof; probe p2t-2
  failed at m = 32 with 3 threads.
- Cause: `ringswitch::weight_table` assumes its chunks start at multiples of `2^nlo`.
  `par::for_each_chunk_mut` and `par::map_chunks` split at `n/k` with `k = 4·threads`. That split
  is aligned only when the thread count is a power of two.
- Fix: both now cut chunks at multiples of `min_chunk` (`par::chunk_len`).
- Check: π is now byte-identical at 1, 2, 3, 4, 5, 6, 7 and 12 threads (m = 25, 28; and m = 28 with
  n = 5,000). The m = 31 runner proof with 3 threads is accepted (p2t-3).
- The runner always has 4 CPUs, so no earlier result was affected. But a different
  `available_parallelism` would have produced rejected proofs.

**Huge pages.** Large blocks (≥ 8 MiB) are now 2 MiB-aligned and advised `MADV_HUGEPAGE` (`alloc.rs`;
`FLOCK_NO_THP` turns it off).
- The 6,000 MiB pre-fault before `ready` drops from 0.82 to **0.22 s** on the 7763 (p2t-3). That is
  stream wall time saved on every request.
- The proving time does not change measurably: 5.48–5.80 s with THP against 5.56–5.61 s without.

### 13.3 Segments of variable length, `L31`, the aggregate (item 3)

**The segment prover** (`leaf::prove_seg(o, circ, vk, s, m, n)`, `1 ≤ n ≤ 2^(m−14)`):
- **Witness.** The chain of `n` steps fills blocks `0 … n−1`. Blocks `≥ n` are zero (`a = b = z = 0`):
  B-12's `free` blocks, with the zero witness.
- **Work proportional to `n`.** Every per-block phase reads only the `n` chain blocks: Z's round 1,
  the x₆ round and fold, the tail (a live prefix that halves each round; `sumcheck::fold_f_live`,
  `zerocheck::round_tab(…, live)`), and the lincheck's partial fold.
  - This replaces P2 §6's timing-only `USED_BLOCKS` global, which is removed. It is exact: a zero
    block adds nothing to any sum.
  - The range is split over the used part, so threads stay balanced.
  - The commitment, ring switching and Ligerito stay at `2^m`.
- **Protocol values that depend on `n`** (my reading of B-12 / S-C's list, pending S-0′):
  - the statement `leafStmt h n` with `h = chainEnd s n`;
  - Z2's `P^e` times `Σ_{b<n} eq(r_blk, b)` (`mle::range_eq`: the chain kind's target on the `n`
    chain blocks, zero past them);
  - `finSh`'s target `eq(τ, n−1)·h̃ + κ_s·s̃` (the last block from the statement, as `shiftTargetAt`'s
    `bnd[4…21]`).
  - The native verifier reads `n` from the statement and checks `1 ≤ n ≤ 2^(m−14)`.
- **Unchanged under the zero witness:** the lincheck (`L3 = [v_chain, 0⁷]`), the shift tables and
  the RS claims. They change only if S-0′ masks the weights by kind (see 13.9).
- **`L31`** is the same prover at m = 31, with kind byte `0x4B`. That byte comes from S-0′'s
  in-progress `FRShape4.SegKind.byte`, read after the runner measurements, which used `'P'`; the
  timing does not depend on it.
- **`pubStart` is not implemented.** If the segment start is public, the shift target's `κ_s·s̃`
  term already pins block 0's input. The aggregate checks `s_{i+1} = e_i` across segments. S-0′'s
  statement format decides whether the segment proof itself changes.

**Byte-exactness.** At the full length `n = 2^(m−14)`, π is byte-identical to HEAD's:
- m = 25, 28 and 30, BLAKE2s of π compared against a build of HEAD's sources (`logs/P2/r40/exact/`);
- threads 1, 3, 4, 5, 6, 7, 12 and 32;
- unit test `variable_length_segments` (`prove_seg` at full length = `prove`).

**KATs against the Lean dumps.**
- **INT-5's dump** (`logs/INT-5/dump`, revision 3.16) is now the default, with items identical to
  INT-2's. `ir.rs` gains three things for it:
  - 3.16's `rsWeight r [pts] κ β act ρ` form, with `β = 1` unless `act`;
  - `linkWAll` and `shiftMask`: node-only, kept `false` in the leaf programs;
  - `shiftTarget`'s `eq(τ, last)` from `bnd[4…21]`, with 3.13's all-ones fallback.
- Results:
  - the dumped `L` (m = 32) and `P` (m = 30) programs accept native proofs and reject the canary
    (`test-leaf 30/32`);
  - the 54 single-byte flips are rejected (`ir_kat_p30`);
  - INT-2's dump still passes too (`logs/P2/r40/exact/ir-dumps.txt`).
- **Variable `n` against a Lean `acc` waits for S-0′:** no dump has a segment program yet. Natively,
  `test-leaf 28 --n 1/5000/16383/16384` and the unit test (m = 25, n = 1, 3, 1,000, 2,047, 2,048)
  accept. They reject the statement of `n ± 1`, a flipped end and a flipped π byte (also run with
  debug assertions, i.e. the prover's internal sum checks). `prove-leaf 31 --n 70000` through
  `rf-oracle`:
  - |tr| = 8,891 with every query length as `items.json` lists it;
  - `reassemble(tr) = π`;
  - the CLI `acc` accepts and the canary is rejected (`logs/P2/r40/local.txt`).

**The aggregate leaf `A`** (`agg.rs`, new). Its bytes follow S-0′'s in-progress draft (`FRAgg.aggHdr`,
`aggChecks`, `VAwith`; `FRSegment.segView`), not yet a dump:
- **Split** (`agg::split`): `k = ⌈n/2^18⌉`; segments `1 … k−1` are full `L32`; the last is the
  remainder `r`, in `L31` when `r ≤ 2^17`, else `L32`.
- **Proof.** `π_A = 0x41 ‖ k ‖ 0^6 ‖ enc64 n ‖ e ‖ π_1 ‖ … ‖ π_k`. Segment `i + 1` starts at segment
  `i`'s end. The runner probes p2t-3/p2t-4 ran the earlier `0x41 ‖ k ‖ 0^46` header, which costs the
  same.
- **Trace and signature.** One recorded trace `tr_A = tr_1 ‖ … ‖ tr_k`, one `SIGN`.
- **Verifier.** `agg::verify` first checks the segments' views, with no query: `c = leafStmt e n`,
  `1 ≤ k ≤ 4`, `1 ≤ n_i ≤ cap(kind_i)`, `Σ n_i = n`, the last end `= e`, `s_{i+1} = e_i`. Then it runs
  the `k` segment verifiers in sequence on one oracle (`Seq` over `tr_A`, consumed exactly).
- **Native `acc`** dispatches on the kind byte (`0x41`). `params::QV = 36,000` (B-17; `FRVerifier.qV`
  is still 10,240 until S-0′).
- **Unit tests** `split_rule` and `aggregate_roundtrip`, at small shapes:
  - `V_A` accepts through the recorded trace;
  - it rejects `n + 1`, a flipped end, a flipped `hdr_A` length, a flipped segment byte and a
    broken link.
- **Mode `prove-agg N`** runs through the service: prove, replay, SIGN, the file, the native `acc`
  and the canary.

**Cost against `n` on the 7763** (4 threads, through `rf-oracle`, prove + trace + SIGN; runs
40719437801, 40721166772, 40722323237):

| segment | n | s |
|---|---:|---:|
| L32 | 2^18 | 5.48–5.80 |
| L32 | 3·2^16 | 4.83–4.95 |
| L32 | 2^17 + 1 | 4.16–4.23 |
| L31 | 2^17 | 2.76–2.85 |
| L31 | 2^16 | 2.07–2.12 |
| L31 | 1 | 1.35–1.44 |

- Linear fits: **`L32(n) ≈ 2.76 + 2.86·n/2^18`**, **`L31(n) ≈ 1.37 + 1.43·n/2^17`**. About half of a
  full segment is fixed: the commitment, ring switching and Ligerito at `2^m`, plus trace and SIGN.
- The aggregate, `prove-agg` (one rep):

| n | segments (s) | total incl. trace + SIGN (s) | peak RSS |
|---|---|---:|---:|
| 2^18 + 1 | L32 5.37, L31(1) 1.28 | 6.81 | 6.19 GB |
| 3·2^18 | 3 × L32 5.28–5.34 | 16.24 | 6.19 GB |
| 2^20 | 4 × L32 5.32–5.41 | 21.86 | 6.19 GB |

  Every aggregate was accepted by the native `acc`, and its canary rejected.

### 13.4 `proofCap` removed, `qV` (item 4)

- `main.rs` `acc` now requires `|π| < 2^64` (`u64::try_from(|π|)`), mirroring `accWith`'s
  `decide (p.π.size < 2 ^ 64)`.
- `format.rs` no longer defines or cites `PROOF_CAP`; only `queryCap` remains.
- `params::QV` is 36,000 (revision 4.0, B-17), so the native `acc` admits an aggregate trace of
  `4 × 8,891`.

### 13.5 Peak memory at 4 threads (item 5)

All figures are `/usr/bin/time -v` on the 7763, against the 11 GiB `[memory] prover` cap:

| request | peak RSS |
|---|---:|
| `L32`, n = 2^18 | 6.19 GB |
| `L31`, n = 2^17 | 3.32 GB |
| aggregate of 4 × `L32` (2^20) | 6.19 GB |

- These peaks include the 6,000 / 3,200 MiB pre-fault. Without it, the VM's m = 32 `test-leaf`
  peaks at 5.35 GB at 1, 2 and 4 threads alike.
- Threads add no memory: the tables are shared, and each chunk's scratch is under 1 MB.
- Segments proved one after another reuse the allocator's cached blocks, so `k` does not raise the
  peak.
- What `N4`/`N8` add (the node's witness and the replayed children, `sizes.py`: 4.6 / 7.7 GB) is the
  node prover's; it runs after the segments, so the step's peak is the larger of the two.

### 13.6 `prover.s` (item 6)

- Regenerated with `build-asm.sh logs/P2/r40/asm` (rustc 1.99.0; `logs/P2/r40/build-asm-2.log`):
  **6,713,303 bytes, sha256 `657a0ab07f9ac4dd5d8859226f901b1956abeb9c4187b9155a08baf93c773d3b`**.
- The linked binary (`gcc -static -O2 -pthread`) is 2,179,944 bytes, sha256 `561b42d6…22ed`.
- This build follows the switch to S-0′'s draft `hdr_A` and the `L31` byte. The build p2t-4 ran was
  sha256 `e6ef7582…f8cc`; the runner reproduced it byte for byte (13.7).
- No machine path appears in the `.s`.
- On the VM the linked binary passes `selftest`, `test-leaf 30` (items KAT, INT-5 Lean program
  accept, canary rejected) and `prove-leaf 30` / `31 --n 70000` through `rf-oracle`
  (`logs/P2/r40/local2.txt`).
- The crate is 9,186 `.rs` lines (was 8,811).

### 13.7 The final build on the runner (probe p2t-4, run 40722323237, EPYC 7763)

- The runner's `build-asm.sh` wrote the **same `prover.s` (sha256 `e6ef7582…f8cc`)** as the VM did
  from the same sources. These are the sources before 13.6's last change (the `hdr_A` and `L31`
  bytes).
- `asm-compat.py` and the runner's link step gave the binary `d464c675…774c`; `SELFTEST` passed
  (`tier=ymm`, checked pclmul, ymm and ymm-sim).
- Every request below was accepted by the native `acc`, and its canary was rejected:

| request | total (s) | pre-fault | peak RSS |
|---|---:|---:|---:|
| `L32` n = 2^18, 4 threads | 5.64–5.69 | 0.27 s | 6.19 GB |
| `L32` n = 3·2^16 | 4.83–4.92 | 0.28 s | 6.19 GB |
| `L31` n = 2^17 | 2.83–2.85 | 0.16 s | 3.32 GB |
| `L31` n = 1 | 1.39–1.44 | 0.15 s | 3.32 GB |
| aggregate 2^18 + 1 (L32 5.41 + L31 1.31) | 6.89 | 0.28 s | 6.19 GB |
| aggregate 2^20 (4 × L32 5.33–5.38) | 21.87 | 0.26 s | 6.19 GB |
| `L32` n = 2^18, 2 / 1 threads | 6.84–6.93 / 13.02–13.04 | — | 6.18 GB |

### 13.8 What the measurements mean for `S` (estimates from 13.3 and `sizes.py`'s node figures)

The model is `logs/P2/r40/model.py` (output in `model.txt`). Its inputs:
- the measured segment fits of 13.3;
- the `N4` node at `k = 1 / 2 / 4` = 1.7 / 3.4 / 4.1 s from `sizes.py` (`k = 3` interpolated);
- `n ∝ 1/n²` on `[2^17, 2^20]`, `2·10^5` draws, and `P̄` as PROVER.md §3.

|  | `P̄` (s) | mean step (s) | `n = 2^17` / `2^17+1` / `2^18` / `2^18+1` (s) |
|---|---:|---:|---|
| measured segments + `sizes.py` nodes | **8.58** | 9.99 | 4.50 / 5.89 / 7.32 / 10.39 |
| measured segments, nodes free (a bound) | 6.37 | 7.49 | 2.80 / 4.19 / 5.62 / 6.99 |

Against the blueprint's "4 threads ≈ 3.3 s":
- this is **8.6 s**, because the threads are already counted (13.2);
- `S ≈ P̄ + V̄ ≈ 8.6 + 0.84 ≈ 9.4 s` with today's V.

**Stream budget (estimate).** Per step: the prover, plus about 2 s of runner overhead:
- `ready` with the 0.22 s pre-fault;
- two `V` measurements per check;
- a calibration sample every 8 steps;
- re-runs of at most 10 % of the steps.

That is ≈ 12.0 s a step, so **the stream fits `M ≤ 80` steps of the 960 s**. `M = 64 + Geom(16)` is
truncated at 112, so **≈ 36 % of evaluations would be truncated, hence unranked**. With free nodes:
≈ 9.2 s a step, `M ≤ 104`, ≈ 8 %.

**The stream budget, not only `P̄`, now needs about a 25 % faster step.** Neither more threads nor
more memory provides it. The levers, in order of size:
1. **The node.** Its estimate is about 25 % of a mean step. A step at `n ≤ 2^18` is one segment plus
   one node, so the node's fixed cost dominates the cubic mean.
2. **The fixed half of a segment** (2.76 s of `L32`): commit 1.12, ring switch 0.53, Ligerito 0.74,
   trace + SIGN 0.18. Levers:
   - the round-1 kernel (P2 §3, item 1);
   - an `L30` kind for remainders `≤ 2^16`: about −0.7 s on those steps; it needs a third segment
     kind in the node's mux (S-0′);
   - overlapping segment `i + 1`'s scalar witness with segment `i`'s vector phases (the SMT
     siblings): about −0.4 s per extra segment (estimate from the witness's 2 → 4 thread gain).
3. **Level 0 at rate 1/4** (B-17) costs about +5 % prover time, so it does not help here.

### 13.9 What P2′ needs from S-0′ and S-E12′

**From S-0′** (the segment and aggregate kinds), as dumps under `logs/S-0p/dump/`:
1. **The segment programs** `ops-L31.txt` and `ops-L32.txt` for a variable `n`, plus `items.json`
   if the sequence changes. The `ir.rs` loader takes `FLOCK_IR_DUMP`. Points to fix:
   - (a) where `n` enters: the statement's `enc64 n`, the `bnd` last block, and `P^e`'s range factor
     (13.3);
   - (b) **whether the free blocks past `n` change any weight the prover sees.** The candidates are
     the shift weights masked to `y < n`, the kind indicators in L3 / claim 2 (3.16's `rsWeight`
     with `act`), and `targetS`'s per-block E. If any is masked, the messages change even with the
     zero witness, and the prover must use the same tables. Each is a local change (`leaf.rs`
     `pe_on_s`, the S2 tables `e1`/`e2`, `ringswitch::weight_table`'s claim 1);
   - (c) the kind bytes of `L31`/`L32` and whether `hdr` carries `n` or `pubStart`;
   - (d) the `pubStart` form: a statement field, a gated row, or nothing in the segment proof (13.3);
   - (e) KAT data: one dumped (n, π-independent) item list per kind, and the A.6 rows of any new kind
     (a `chainPub` block 0, if the pin is a row).
2. **The aggregate `A`.** Needed: `hdr_A`, the order of `π_A`'s parts, `V_A`'s checks (as in
   B-11: `e_i = s_{i+1}`, `e_k = end`, `Σ n_i = n`, `n_i ≤ 2^18`, and whether the `L31`/`L32` choice
   is checked), how `hashStmt` hashes the segment statements, and `qV`. `agg.rs` follows S-0′'s
   in-progress `FRAgg` draft; if the final form differs, only the bytes change.
3. **`N4`/`N8`'s `gen`** (`ops-N4.txt`, `ops-N8.txt`, `items.json` for `m = 32/33`), with the
   finals that are new in 4.0, so that `ir.rs` can run the node programs.

**From S-E12′** (the node circuit):
- `compileMux`'s M and L rows for `N4`/`N8` (`1 + k` slots, the sub-slot mux over `{L31, L32}`,
  slot 1 over `{N4, N8}`), with the register-to-cell map (`mregs`/`maux`), as S-E5's `nodedump`
  format (`nodeshape::load` reads it);
- the H layout: the block intervals of every kind, the `WM` mirror map, and the link families' slot
  maps for `linkWAll`;
- the pack map from the H trace/stream cells to the M imports;
- `targetS`/`linkWAll`/`shiftMask` for the node kinds.

With these, the node prover is the §12.4 port at the new sizes: H `2^17`/`2^18` blocks, M `2^23`,
and `τ`/`σ` with 23 coordinates.

**Blueprint changes requested** (I do not edit the blueprint):
- §0's table and changes 25 (b), (e): the step costs are 4-thread 7763 figures. Drop the ×2.5. The
  one-thread figure is 12.95 s per `2^18` (13.2). `P̄ ≈ 8.6 s` and the stream fits `M ≤ 80` with the
  `sizes.py` nodes (13.8).
- B-16: "multi-threaded on the runner's 4 vCPUs" is done. Add that the runner has **2 physical
  cores**.

### 13.10 Changes (files under `submissions/flock-recursive/prover/`; crate 9,186 `.rs` lines, was 8,811)

| file | change |
|---|---|
| `agg.rs` | new, 158 lines: `split`, the aggregate prover and `V_A` (S-0′'s draft `hdr_A`/`aggChecks`), tests `split_rule` and `aggregate_roundtrip` |
| `leaf.rs` | `prove_seg` / `prove_logged(…, n, …)`, `seg_c`; `P^e` range factor; tail by live prefix; verifier reads `n` and uses last block `n − 1`; test `variable_length_segments` |
| `witness.rs` | `leaf_witness_fast(…, n)`: chain of `n` steps, zero blocks past it, `h = chainEnd s n` |
| `zerocheck.rs`, `lincheck.rs`, `sumcheck.rs` | `used`/`live` parameters replace the `USED_BLOCKS` global; `fold_f_live` |
| `mle.rs` | `range_eq` with test `range_eq_is_the_indicator_mle` |
| `par.rs` | chunk boundaries at multiples of `min_chunk` (`chunk_len`): the thread-count bug; `USED_BLOCKS` removed |
| `alloc.rs` | 2 MiB-aligned large blocks with `MADV_HUGEPAGE` (`FLOCK_NO_THP`) |
| `main.rs` | `acc`: `|π| < 2^64`, `A` dispatch; `--n` for `test-leaf`/`prove-leaf`; mode `prove-agg N`; `pi_b2s` in `test-leaf`'s line |
| `format.rs`, `params.rs` | `PROOF_CAP` removed; `QV = 36,000`; `KIND_L31 = 0x4B` |
| `ir.rs` | 3.16 ops (`rsWeight … act`, `linkWAll`, `shiftMask`), `shiftTarget` at `bnd`'s last block |
| `kat.rs`, `items.rs`, `transcript.rs` | dump path `logs/INT-5/dump` |
| `prover.s` | regenerated (13.6) |
| `probe/p2t-prover/run.sh` | new, 58 lines: CPU facts, `prove-leaf M --n N` and `prove-agg N` cases at chosen thread counts |

**Checks:** `cargo test --release` passes (32 tests, 1 ignored); the debug-assertion build also
passes (`target-dbg`).

### 13.11 Remaining items, in order (after S-0′'s and S-E12′'s dumps)

1. Make the segments exact for `L31`/`L32` against S-0′'s segment programs: (b)–(d) of 13.9, then
   `ir.rs` on `ops-L31`/`ops-L32` at n = 1, 2^16, 2^17 (L31) and 2^17 + 1, 3·2^16, 2^18 (L32),
   accept plus canary.
2. Give the aggregate its final `hdr_A`, `hashStmt` and `V_A` bytes, and run `ir.rs` on S-0′'s `A`
   program if it dumps one.
3. Build the `N4`/`N8` prover from S-E12′'s dumps (§12.4's plan at the new sizes); `ir.rs` with
   `evalM`/`evalL` on `ops-N4/N8`.
4. Add the `prover first` (two chains: up to 8 segments, then `N8`) and `prover step` (`prev.stmt`,
   `prev.bin`, `chain.json` → `A` + `N4`) modes with the handshake: `ready`, then the inputs renamed
   in, `go`, `done`.
5. Do the stream dry run on the PR #20 harness (`smoke.py --org`), with step times and peak memory
   (the `N8` estimate is 7.7 GB) on a runner.
6. Pursue the step-time levers of 13.8, chosen by the measured node cost.

## 14. Pass 6 (revision 4.1, track P2″): the prover's per-step time

Status: 2026-10-28. Brief: profile the segment on the 7763; lever 4 (witness overlap); lever 6
(round 1, commit, ring switch); other levers from the profile; re-fit `L32(n)`, `L31(n)`. π stays
byte-identical to the pre-change prover (S-0′'s `seq4` is **not** adopted in this pass, as the
coordinator ruled). Logs: `logs/P2/r41/` (VM) and `logs/P2/run-<id>/` (runners). Probe branches
`probe/p2t-6a` … `6o` (one commit on HEAD each, made from a temporary index, no local ref moved); all
deleted. Six of the fourteen runs landed on other CPUs (EPYC 9V74, 9V45, Xeon 6973P-C); those are
off-tier, kept only as cross-checks, and are not quoted below as 7763 figures.

### 14.1 Where the time goes (item 1; run 40726261624, EPYC 7763, 4 threads, HEAD's prover)

New: `prof.rs` (`FLOCK_PROF=1`; sub-phase spans, printed as `| prof …` in the PROVE-LEAF line; no
effect on π) and the mode `bench` (`bench.rs`: memory and in-cache kernel throughput).

| sub-phase (s) | L32, n = 2^18 | L32, n = 2^17 | L31, n = 2^17 | kind |
|---|---:|---:|---:|---|
| witness (chain 0.078 + blocks) | 0.521 | 0.289 | 0.260 | per block, scalar |
| NTT: copy / whole-buffer passes / in-block | 0.074 / 0.392 / 0.263 | 0.073 / 0.394 / 0.258 | 0.036 / 0.158 / 0.129 | fixed |
| Merkle level 0: leaves / nodes (the service hashes) | 0.363 / 0.086 | 0.364 / 0.071 | 0.189 / 0.040 | fixed |
| round 1 (windows) | 1.295 | 0.639 | 0.603 | per block |
| x₆ round / fold | 0.332 / 0.230 | 0.165 / 0.128 | 0.166 / 0.114 | per block |
| tail rounds / folds | 0.135 / 0.113 | 0.068 / 0.073 | 0.068 / 0.056 | per block |
| lincheck partial fold | 0.302 | 0.153 | 0.153 | per block |
| ring switch: weight table | 0.558 | 0.575 | 0.279 | fixed |
| Ligerito level 0: first round / folds | 0.030 / 0.416 | 0.030 / 0.418 | 0.015 / 0.210 | fixed |
| Ligerito levels 1–4: Merkle leaves + nodes, folds | 0.076, 0.019 | 0.081, 0.020 | 0.041, 0.010 | fixed |
| prove (sum of phases) | 5.41–5.48 | 4.01–4.04 | 2.64–2.73 | |

**Kernel throughput** (`bench`, same run; ns per item per thread; 1 / 2 / 4 threads):

| kernel | 1 | 2 | 4 | what bounds it |
|---|---:|---:|---:|---|
| memory read / write / copy, GB/s (all threads) | 21 / 19.7 / 19.3 | 36.5 / 23.3 / 22.6 | 39.4 / 23.2 / 22.5 | — |
| round-1 window (µs) | 4.11 | 4.12 | 8.81 | vector ALU (no SMT gain) |
| NTT butterfly | 1.74 | 1.79 | 3.42 | carry-less multiply (no SMT gain) |
| F × F product (`axpy`) | 3.33 | 3.37 | 6.37 | carry-less multiply + reduction |
| `phi_apply` (16 byte tables) | 7.98 | 8.00 | 17.15 | L1/L2 loads |

What this says:
- **Every vector kernel saturates at 2 threads** (one per core). The SMT siblings add nothing to
  any of them; this confirms §13.2 kernel by kernel.
- **The NTT is compute-bound, not memory-bound.** It does 19 layers × 2^25 butterflies; at 1.11·10^9
  butterflies/s that is 0.57 s of its 0.65–0.73 s. Fewer passes (radix-16) would cut memory traffic
  that is not the bottleneck.
- **The butterfly is about 80 % carry-less-multiply bound** (4 `vpclmulqdq ymm` per 2 butterflies).
  A reduction by shifts instead of `clmul` is slower (14.3).
- **The fixed half at m = 32 is about 2.6 s** (NTT 0.73, Merkle 0.45, weight table 0.56, Ligerito
  0.55, trace + SIGN 0.18). The per-block half is about 2.85 s per 2^18 (round 1 1.30, x₆ 0.56,
  witness 0.52, lincheck 0.30, tail 0.25).

### 14.2 Lever 4, witness overlap (item 2): no gain, dropped

Built and measured (probe p2t-6b, run 40727455347; p2t-6c, run 40728620249). Segment `i + 1`'s
witness ran on an extra thread (single-threaded, scalar) while the pool proved segment `i`.

| aggregate (7763, 4 threads) | without overlap (s) | with overlap (s) | peak |
|---|---:|---:|---:|
| 2^18 + 1 (L32 + L31(1)) | 6.77 | 6.81 | 6.19 → 6.19 GB |
| 2 × L32 (2^19) | 10.97 | 10.98 | 6.19 → 7.07 GB |
| 4 × L32 (2^20) | 21.71 | 21.81 | 6.19 → 7.33 GB |
| 2 × L32, pool at 3 threads + the overlap thread | 10.86 (4 threads, no overlap) | 11.70 | |

- The overlapped witness takes 2.3–2.8 s. It slows the pool's commit (+0.19 s) and round 1
  (+0.25 s) by about the 0.47 s it saves.
- **The SMT siblings are not idle during the vector phases: the pool's 4 threads occupy them.** The
  blueprint's −0.4 s per extra segment (−0.25 s per mean step) does not exist on this runner.
- The code is removed. What stays from this item is the chain pipelining (14.3 a).

### 14.3 Lever 6 and the other kernels (items 3–4)

Each change was measured inside the proof on the 7763 (sub-phase spans), and its kernel in `bench`.
Before = HEAD's prover; after = this pass's. The final before/after (14.4) ran both binaries on the
same runner.

| # | change | sub-phase, L32 2^18 (s): before → after | kept? |
|---|---|---|---|
| a | **Witness: chain pipelined.** Chunk 0 of the pool job computes the chain; the other chunks fill blocks behind it (`witness::leaf_witness_fast`, spin on an atomic counter). | witness 0.516–0.517 → 0.469–0.486 | yes |
| b | **Lincheck partial fold.** One 64-byte bit transpose per word (`simd::pf_stripe`) and 128-bit table XORs, instead of 8 scalar gathers + `transpose8` per byte. | lincheck 0.299–0.313 → 0.194–0.197 | yes |
| c | **Ring-switch weight table.** (i) `simd::phi_add_idx`: the 16 byte-table lookups as `vmovdqa`/`vpxor`, two elements interleaved; (ii) only at `elo`'s nonzero positions — claim 2 (the shift claim) has 64 of 1,024 — both for the products and the lookups. Doing every position, as a first attempt did, was slower (0.558 → 0.653): the old loop already skipped zeros. | ringswitch 0.532–0.568 → 0.393–0.419 | yes |
| d | **Round-1 window: one 32-byte table pair for both c-banks** (`conv2[bm][v] = (conv[v & 0x55], conv[v & 0xAA])`): one load instead of two, no masks. | `bench` window 8.81 → 7.99 µs per thread at 4 threads; **in the proof within noise** (zc_round1 1.19–1.25 → 1.19–1.29) | yes (neutral in the proof) |
| e | x₆ fold from scaled tables `(1+s)·t`, `s·t` (no products) | x₆ fold 0.230 → 0.263 on the 7763 (run 40733248360): the two 32 KiB tables leave L1 | **reverted** |
| f | NTT butterfly with the reduction by shifts instead of 2 `clmul` | 1.37 → 1.58 ns per butterfly (9V74 `bench`; it is a ymm-only kernel) | **not adopted** |
| — | lever 4 (14.2) | — | dropped |

**Round 1 is not cut (lever 6's −30 % is not reached).** Its window (4.1 µs per core, about 41 k
vector ops) breaks down as:
- about 60 % in the LDE table application and the bit-serial GF(2^8) products (`gf8mul`: about 50 ops
  per 32 products; Zen 3 has no GFNI);
- about 30 % in the 3 × 64 × 16 table lookups of the conversion;
- the rest in the `axpy` by `eq`.

The window is ALU-bound with no SMT gain. What is left is a different representation:
- a tower GF(2^8) = GF(16)² with `vpshufb` log/exp products, about 34 ops per 32 products: an
  estimated −10 % of round 1;
- a bit-sliced conversion (`vpmovmskb` planes, four-Russians over constant masks): an estimated
  −20 %.

Neither is built. Both are changes of internal representation only (π unchanged).

**Commit:**
- The NTT is at the carry-less-multiply roofline (14.1).
- The Merkle leaves are bound by the service's BLAKE2s on the same 4 hw threads (1 GiB in
  0.36 s ≈ 2.9 GB/s). Pipelining the requests cannot add hw threads.
- An NTT/hash overlap on SMT siblings (`clmul` against integer-ALU work) is the one remaining idea.
  It is bounded by the in-block stage (0.26 s) and is unmeasured.

### 14.4 Before/after on one runner, and the new fits (item 5)

`probe/p2t6/final.sh` builds both provers on the runner (`build-asm.sh`, `asm-compat.py`, `gcc
-static`), the base from the branch HEAD's `prover/` (sha256 `657a0ab0…3d3b`) and the new one
(`d25ca624…e552`). It then runs them alternately through one `rf-oracle`.

There were three runs, all on the EPYC 7763: 40734390435, 40734399110 and 40734406678. Each cell
below is the range over 6 runs (3 runners × 2 reps), total = prove + trace + SIGN, 4 threads:

| request | base (s) | new (s) | Δ |
|---|---:|---:|---:|
| L32 n = 2^18 | 5.52–5.60 | 5.17–5.36 | −0.31 |
| L32 n = 3·2^16 | 4.76–4.84 | 4.51–4.57 | −0.27 |
| L32 n = 2^17 + 1 | 4.10–4.21 | 3.87–4.01 | −0.21 |
| L32 n = 2^16 | 3.38–3.47 | 3.21–3.29 | −0.17 |
| L32 n = 1 | 2.69–2.78 | 2.52–2.61 | −0.16 |
| L31 n = 2^17 | 2.73–2.81 | 2.60–2.65 | −0.14 |
| L31 n = 2^16 | 2.04–2.11 | 1.92–2.00 | −0.11 |
| L31 n = 1 | 1.33–1.41 | 1.26–1.34 | −0.07 |
| aggregate 2^20 (4 × L32, one trace, one SIGN) | 21.80–21.93 | 20.53–20.62 | −1.30 |

- **π is byte-identical** (sha256 of π from the file) between base and new in all 27 cases, and in
  the 4 off-tier final runs.
- Every proof is accepted by the native `acc`, and every canary is rejected.
- Peak RSS is unchanged: 6.19 GB (L32, aggregate) and 3.32 GB (L31), against the 11 GiB cap.

**Fits** (least squares over all points; `logs/P2/r41/fit.py`, output `fit-final.txt`):
- **`L32(n) = 2.58 + 2.66·n/2^18 s`** (base on the same runs: 2.73 + 2.81; §13: 2.76 + 2.86);
- **`L31(n) = 1.30 + 1.32·n/2^17 s`** (base: 1.38 + 1.40).

**Per-step estimates** (`fit.py`: §13.8's model with these fits). The nodes use blueprint 4.1's
phase model, not a measurement: `N2` 2.5 s for `k ≤ 2`, `N4` 4.2 s for `k = 3, 4`. `n ∝ 1/n²` on
[2^17, 2^20]:

| | base | new |
|---|---:|---:|
| segments at the mean chain `n = 1.19·2^18` (L32(2^18) + L31(49,807)) | 7.44 s | 7.04 s |
| + node (`N2`) | 9.94 s | 9.54 s |
| segments at `n = 2^20` (4 × L32) | 22.15 s (measured aggregate 21.80–21.93) | 20.95 s (measured 20.53–20.62) |
| + node (`N4`) | 26.35 s | 25.15 s |
| `P̄` (segments + nodes) / mean step | 8.85 / 10.13 s | 8.51 / 9.73 s |

The pass gains about 4 % on the segments: −0.4 s per mean step, −0.34 s on `P̄`. That is about what
the blueprint's C′ booked for lever 6 (−0.4 s) and lever 4 (−0.25 s) together, minus lever 4.

### 14.5 Checks

- `cargo test --release`: 33 passed, 1 ignored (`logs/P2/r41/cargo-test.txt`). New tests:
  - unit test `simd::pass6_tests::avx2_table_kernels_match`: the AVX2 table kernels — the round-1
    window with `conv2`, `phi_add`, `phi_add_idx` and `pf_stripe` — against their portable
    references. It runs on the VM, which has AVX2 but no `pclmulqdq`;
  - `selftest` checks `phi_add`, `phi_add_idx` and `pf_stripe` on every tier. It passed on the
    runners (`tier=ymm checked=[pclmul,ymm,ymm-sim]`).
- π against HEAD on the VM, `test-leaf` (portable tier), pi_b2s equal:
  - m = 28: `756eecc0…`;
  - m = 28, n = 5,000 at 1, 3 and 8 threads: `1e53c8a7…`;
  - m = 30: `b7dc8ab7…`;
  - m = 32: `e2412740…`.
- **The dumped Lean `acc` accepts and the canary is rejected** (INT-5's `ops-P` at m = 30 and `ops-L`
  at m = 32: `lean_ir=accept(lines []; canary_accept=false; asks=8891)`; `logs/P2/r41/test-leaf-30*.txt`,
  `test-leaf-32.txt`). Items KAT pass (8,891). The m = 32 run used the build before 14.3 e's revert (that revert restores HEAD's x₆ code); the final build's m = 32 π equals the base's on the runners (14.4).
- Source rule (`logs/org20/scripts/source-rule.py`): 0 findings.

### 14.6 `prover.s`

- Regenerated with `build-asm.sh logs/P2/r41/asm` (rustc 1.99.0; `logs/P2/r41/build-asm.log`):
  **6,954,029 bytes, sha256 `d25ca624638722dd71526e6bfdab159b915378962e246e31e9f243831280e552`**.
- The runners' `build-asm.sh` wrote the same sha from the same sources (14.4).
- The linked binary passes `selftest` and `test-leaf 28/30` on the VM.
- No machine path appears in the `.s`.

### 14.7 Changes (files under `submissions/flock-recursive/prover/`; crate 9,563 `.rs` lines, was 9,186)

| file | change |
|---|---|
| `prof.rs` | new, 39 lines: `FLOCK_PROF` sub-phase spans |
| `bench.rs` | new: mode `bench` (memory GB/s; round-1 window, butterfly, `axpy`, `phi_add` throughput) |
| `witness.rs` | `leaf_witness_fast`: the chain pipelined into the pool job |
| `lincheck.rs` | `partial_fold` calls `simd::pf_stripe` |
| `ringswitch.rs` | `weight_table`: nonzero-`elo` index lists, sparse products, `simd::phi_add_idx` |
| `simd.rs` | `r1::conv2`, `r1::phi_add`, `r1::phi_add_idx`, `r1::pf_stripe` (AVX2) + dispatchers and portable references; `selftest` checks; test `pass6_tests` |
| `main.rs` | `mod prof`, `mod bench`; mode `bench`; `| prof …` in PROVE-LEAF |
| `ntt.rs`, `merkle.rs`, `leaf.rs`, `ligerito.rs`, `zerocheck.rs` | spans only |
| `prover.s` | regenerated (14.6) |
| `probe/p2t6/run.sh`, `probe/p2t6/final.sh` | new: profile/kernel probe; base-vs-new on one runner (`set` picks the case list) |

### 14.8 For the blueprint and the orchestrator (I do not edit the blueprint)

- **Lever 4 is zero on this runner** (14.2). Changes 26's C′ booked −0.25 s per mean step for it;
  drop it.
- **Lever 6, as measured:**
  - round 1 is not cut (14.3 d);
  - the pass's kernels give −0.31 s per 2^18 at L32 and −0.4 s per mean step all-in;
  - the segment fits are now `L32(n) = 2.58 + 2.66·n/2^18`, `L31(n) = 1.30 + 1.32·n/2^17`.
  - Net against C′'s booking (−0.65 s for levers 4 + 6): **about +0.25 s per mean step**, so C′'s
    10.0 s step becomes ≈ 10.25 s, and `M ≤ 90` becomes `M ≤ 88` (estimate, same overhead).
- **What is left on the prover side, by size** (all unmeasured estimates):
  - round 1's representation (tower GF(2^8) products, bit-sliced conversion): −0.1 … −0.3 s per
    2^18;
  - the NTT/hash overlap: ≤ 0.15 s fixed;
  - nothing else in the fixed half is above 10 %. The NTT and the folds are at the carry-less
    roofline; the Merkle leaves are the service's.
- **The runner pool is mixed.** 6 of 14 probes today got EPYC 9V74/9V45 or Xeon 6973P-C, which
  are 20–40 % faster. A stream's `c_P` therefore depends on the draw.
- **`seq4`** (S-0′, 47c5c6c): not adopted, as ruled. The re-baseline comes with S-F4's dumps.

## 15. Pass 7 (revision 4.1, track P2‴): the segment and aggregate provers on S-F4's programs

Status: 2026-10-28. Brief: re-baseline the segment prover and the aggregate to revision 4.1's verifier
programs (`seq4`, S-F4's dumps `logs/S-F4/dump/`, SHA256SUMS checked), so that every proof the prover
makes is accepted by the dumped Lean `acc`. Not in this pass: the N2/N4/N8 node prover. Logs:
`logs/P2/r41p7/` (VM) and `logs/P2/run-40741779761`, `-40741784807`, `-40741790546` (runners, all
three EPYC 7763). Probe branches `probe/p2t-7a/7b/7c`, one commit `5380659` on `633ab78` built from a
temporary index (prover/, `probe/p2t7/run.sh`, `.github/probe.conf`, and S-F4's `ops-L30/31/32.txt` and
`items.json`); all three deleted after their runs.

### 15.1 What changed

- **`seq4`** (`params.rs`): Lr 17 rounds (Lr1 9 squeezes), E2 23 (E1 12), E4 25. The Lr and E fields
  are 816 and 2,336 B, `piSize` is 798,192, and there are 8,905 items, 482 of them Fiat–Shamir. A
  segment sends the new rounds as zero dummies. The kind bytes already matched S-0′'s: L30 = 3.x's
  `P` = `0x50`, L31 `0x4B`, L32 `0x4C`. `hdr` and `stmt` are unchanged (`pubStart` is positional, as
  S-0′ I-2 has it).
- **The masked shift successor** (`leaf.rs`), as in S-F4's `shiftSegI`:
  - the prover's S2 weight table gets `e2[n] = 0` when `n < 2^(m−14)`, because `eq(τ, L)` cancels
    `e1[L]` in characteristic two;
  - the native verifier adds `eq(τ, L)·eq(τ′, L + 1)` to `w_in`.
- **S-F4 §3.2/§5 is wrong on one point.** It says the prover's messages are unchanged with the zero
  witness. That holds for the claimed sum, not for the S2 round messages.
  - After the first fold, the changed entry `e2[n]` meets `inn(n − 1) ≠ 0` in the `X(1 − X)`
    coefficient.
  - Negative control `ir::tests::ir_unmasked_shift_rejected`: with 3.x's unmasked table (test hook
    `leaf::NO_MASK`), the dumped L30 program and the native verifier both reject `n = 777` and both
    accept the full `n = 2^16`.
  - So the mask is required on the prover's side too, not only the verifier's.
- **`ir.rs` interprets the segment ops:**
  - `targetS` with the 37-entry operand: the leaf target × `range_eq(blk, L + 1)` (`targetSSegI`);
  - `shiftMask` with operand `τ ‖ L`: `shiftSegI`'s three outputs;
  - `shiftTarget`'s explicit fourth operand `κ_s`;
  - `lastAt`. `lastOps` needs no new op.

  Node-form `shiftMask`/`evalL`/`evalM`/`linkWAll` still return recorded zeros.
- **`V_A`** (`ir::run_agg`). No `V_A` program is dumped, so I rebuilt `FRAgg.VAwith (piSizeOf seq4)`
  in `ir.rs`:
  - the shape, `segView` and `aggChecks`, with no query;
  - then `seqAll` over the dumped segment programs, against `segC = leafStmt hᵢ nᵢ`, on one oracle,
    stopping at the first rejection.

  `agg::verify` (native) now matches it: it stops at the first rejected segment.
- **`hdr_A` bytes 2–7.**
  - HEAD's `VAwith` does not read them (R-4-m5, malleability).
  - The fix in progress in the working tree (`FRAgg.lean`, not mine, uncommitted) adds the zero
    check. Both `run_agg` and `agg::verify` follow that fix.
  - The prover writes zeros, so its proofs pass both forms.
- **Split** (`agg::split`): the remainder goes to the smallest of `L30` (`≤ 2^16`), `L31` (`≤ 2^17`)
  or `L32`.
- **Native `acc`** (`main.rs`) dispatches as `V4with`/`kindOf4`:
  - `'A'` → `V_A`;
  - a bare segment byte → reject;
  - node bytes and `W` → reject, since they are not built natively.

  `Top::Seg` (bare-segment check) and `Top::Lean` (`V_A` over the dumps) serve the measurement modes:
  - `prove-leaf` prints `lean_seg`: the kind's Lean program on the signed file's trace, consumed
    exactly;
  - `prove-agg` prints `lean_acc`: `accWith4` with `V_A` over the dumps, plus its canary;
  - `acc --lean` and `acc --seg` select them from the CLI.
- **KAT paths** go to `logs/S-F4/dump` (`FLOCK_IR_DUMP` and `FLOCK_ITEMS_JSON` override them). The
  3.x INT-5 KAT is retired.

### 15.2 KATs (the new baselines)

**Segments against the dumped Lean programs** (`test-leaf M --n N`, VM, `logs/P2/r41p7/kat.txt`):

| kind | n |
|---|---|
| L30 | 1, 12,345, 2^16 |
| L31 | 1, 2, 70,001, 2^17 |
| L32 | 1, 2, 2^17 + 1, 3·2^16, 200,001, 2^18 − 1, 2^18 |

- Every proof is accepted by `ops-L{m}.txt` with 8,905 asks, and by the native verifier.
- The items KAT passes for both the verifier and the prover's Fiat–Shamir items.
- The canaries are rejected by the Lean program: the flipped statement, and `leafStmt h (n + 1)`.
- Three flipped π bytes are rejected natively.
- The linked `prover.s` binary repeats this at L31 99,999 and L30 4,321 (`asm-check.txt`).

**Unit tests** (`cargo test --release`: 35 passed, 1 ignored; `cargo-test.txt`):
- `ir_kat_l30`: n = 1, 12,345, 2^16, with 3 canaries each. At n = 12,345, 54 single-byte flips are
  rejected by both Lean and native.
- `ir_unmasked_shift_rejected`: the (−) control of 15.1.
- `ir_agg_l30`: `V_A` over the dumped L30 program, on two L30 segments.
  - Accepted, with 2 × 8,905 asks.
  - Rejected: the statement of `n + 1` and a flipped segment byte.
  - Rejected with no query: a broken chaining and a nonzero `hdr_A` byte 2.
- `split_rule` with the L30 tier, `aggregate_roundtrip`, and `items_seq_kat` / `items_kat_*` at 8,905
  and 482.

**The aggregate through `rf-oracle`.** Native `acc`, Lean `V_A` and both canaries were run on each
case below. VM: `local-agg.txt`, `local-agg2.txt`. Runners: 7763 × 3.

| n | segments | where |
|---|---|---|
| 2^16 | L30 | VM |
| 2^18 + 1 | L32 + L30(1) | VM and runners |
| 331,073 | L32 + L31(68,929) | VM |
| 3·2^18 + 5 | 3 × L32 + L30(5) | VM |
| 2^20 | 4 × L32, \|tr\| = 35,620 ≤ qV4 | VM and runners |

- Native `acc` accepts every case, and so does `lean_acc`.
- Both canaries are rejected in every case.

On the runners: 72 canaries rejected; `lean_seg` accepted 66 of 66; `lean_acc` accepted 6 of 6.

**Not kept: 3.x's L32 dump-exactness.** The sequence constants are compile-time `seq4`, so a 3.x
mode would need a second item sequence. That is not cheap, so it is dropped. 3.x's π at full length
differs from 4.1's only by the 14 dummy items (S-0′ I-1).

### 15.3 Timings on the 7763 (item 4; 3 runs × 2 reps, 4 threads, total = prove + trace + SIGN)

`logs/P2/r41p7/fit.py` → `fit.txt`:

| segment | n | s |
|---|---:|---|
| L32 | 2^18 / 3·2^16 / 2^17 + 1 / 2^16 / 1 | 5.20–5.36 / 4.47–4.59 / 3.85–3.96 / 3.19–3.33 / 2.49–2.64 |
| L31 | 2^17 / 2^16 / 1 | 2.58–2.65 / 1.92–1.98 / 1.24–1.34 |
| L30 | 2^16 / 2^15 / 1 | 1.25–1.31 / 0.94–1.01 / 0.64–0.71 |
| aggregate | 2^18 + 1 (L32 + L30(1)) | 5.84–5.92 |
| aggregate | 2^20 (4 × L32) | 20.50–20.70 |

**Fits:**
- **`L32(n) = 2.57 + 2.68·n/2^18 s`** (pass 6: 2.58 + 2.66);
- **`L31(n) = 1.29 + 1.33·n/2^17 s`** (pass 6: 1.30 + 1.32);
- **`L30(n) = 0.67 + 0.60·n/2^16 s`** (new).

`seq4`'s 14 dummy items cost nothing measurable. A remainder of at most `2^16` steps now costs
0.67–1.27 s in `L30`, against 1.29–1.96 s in `L31`. The saving is about 0.6–0.7 s on those steps.

Peak RSS: 6.19 GB for L32 and the aggregates; 3.32–3.33 GB for L31 and L30, with the 3,200 MiB
pre-fault.

### 15.4 `prover.s`

- Regenerated with `build-asm.sh logs/P2/r41p7/asm` (`build-asm.log`): **7,007,702 bytes, sha256
  `7c3b445b38dfef764ec150d288a742a1af985c24d2cf85e7304741a74ae7f2fd`**.
- **All three runners' `build-asm.sh` reproduced it byte for byte.**
- The runners' link gives the binary `8c9228cd…1560`, and `SELFTEST` passes (`tier=ymm`, checked pclmul,
  ymm and ymm-sim).
- No machine path appears in the `.s`.

### 15.5 Changes (files under `submissions/flock-recursive/prover/`; crate 9,834 `.rs` lines, was 9,563)

| file | change |
|---|---|
| `params.rs` | `seq4` counts, `FIELD_SIZES`, `PI_SIZE` 798,192, `N_ITEMS`/`N_FS_ITEMS` |
| `leaf.rs` | the masked successor (prover table, native `w_in`); test hook `NO_MASK` |
| `ir.rs` | segment `targetS`/`shiftMask`, `shiftTarget` `κ_s`, `last_at`, `seg_cap`, **`run_agg`** (`V_A`); tests `ir_kat_l30`, `ir_unmasked_shift_rejected`, `ir_agg_l30` (replace `ir_kat_p30`) |
| `agg.rs` | three-tier split; `seqAll` early stop; `hdr_A` padding as R-4-m5 |
| `main.rs` | `acc` as `V4with` (`Top`), `lean_seg`/`lean_acc` in `prove-leaf`/`prove-agg`, `acc --lean`/`--seg`, `test-leaf` runs `ops-L{m}` at any `n` |
| `kat.rs`, `items.rs`, `transcript.rs` | dump path `logs/S-F4/dump`, 8,905 / 482 |
| `prover.s` | regenerated (15.4) |
| `probe/p2t7/run.sh` | new: the pass's cases through `p2t-prover/run.sh`, with the dumps and the Lean checks |

### 15.6 For the orchestrator

1. **S-F4 §3.2/§5's "prover messages unchanged" should be corrected** (15.1). The mask is needed in
   the prover's S2 table as well as in the verifier. Any other prover of a segment (or of a node
   whose last block masks the successor) must apply it too.
2. **R-4-m5** (`hdr_A` bytes 2–7): the native and IR `V_A` already check zeros. If the in-progress
   `FRAgg` fix is not adopted, drop that check in `agg::verify`/`ir::run_agg` to mirror HEAD.
3. Source rule (`logs/org20/scripts/source-rule.py`): 1 finding, in the untracked
   `lean/FRSoundness4Agg.lean:194` (`#queries`). That file is another track's in-progress module,
   not this track's.
4. Next for P2: the N2/N4/N8 node prover from S-E12′'s node rows and dumps (§13.11 items 3–6).

## 16. Pass 8 (revision 4.1, track P2⁗): the node witness, the node ops, the M fill

Status: 2026-10-28, **partial: item 1 (the node witness) done for `N8` and checked relation by
relation; the native node ops done and KAT-equal to the Lean's; items 2–4 (the node PIOP, the
`first`/`step` modes, the 7763 timings) not started** (16.6 is the handover). Logs:
`logs/P2/r41p8/`. No probe branch was pushed (no runner measurement this pass).

### 16.1 The order is forced: `N8` first

An `N2`/`N4` node replays a previous node in slot 0 (prototype 0), and the first node of a stream
is step 1's `N8` (two aggregates, every slot prototype 1). So no `N4` can be built, and prototype
0 cannot be filled honestly, until an `N8` proof exists (item 2). This pass's KATs are on `N8`;
prototype 0 is checked on its inactive fill only.

### 16.2 What was built (crate 11,881 `.rs` lines, was 9,834)

| file | lines | content |
|---|---:|---|
| `mfill.rs` | new, 525 | loaders of the node dump (`mrows-p{π}`, `mregs-p{π}`, `maux-p{π}`, `node-N*.txt`); **the slot fill**: `one′`, the selector copies, every register's single-cell forms from the program run, the auxiliary imports (`felems n`: the bytes as `n` sixteen-byte elements; `bits n`: the number's bits), then a **forward row solve** (a row with one unknown cell is linear in it unless the cell is in both `A` and `B`) to a fixed point, leftovers zero; every row and every multi-cell register form checked. The first fill of a prototype records its solve order (`Proto::plan`), later fills replay it (falling back to the worklist if a step fails) |
| `node.rs` | new, 974 | `NK` (`FRShape4`/`FRNodeLayout4`'s numbers), `BK` (A.6's kinds with their targets, `FRBlockKinds`), **`bk_at` = `nodeLayout4`** (chains, `hashStmt`, WOTS, `WM`/spare, the tails: candidate final blocks and `c_A`'s `hashA`), `cells4`, `chainLk4`, the eight link families (`NodeT.fam`); `trace_blocks`: up to 64 blocks of any kinds bit-sliced on the general tape (pinned inputs `(0,0)`, free inputs `(var k, one)`, `free` blocks `A₀ = B₀ = I`); **`witness`**: both main chains (sequential compressions, the two chains in parallel; an aggregate of `k < maxK` segments: main chain zero-padded, `F_{a,k}` with the main chain's `h_in` and message prefix), `c_A`, `hashStmt` per verifier slot from the slot child's `stmt`, WOTS per signed child (digit mux, key leaf, path; asserts the root is `vk`), the `WM` mirrors (A.6's map), L (signature, digits, step selectors, the slot child's 7,552 position bits, the one-hot kind selector), the M fill per slot in parallel (the prototype program at the child's index, `ir::run_regs` through `Seq` over the child's trace); **`check`**: every relation directly |
| `nodeops.rs` | new, 343 | the node ops in specification form: `shiftMask4S`, `targetSNode4S`, `linkWAll4S`, `rsWeightS4` (claim 2 by `kf4` at `β^(2^k)`), `kf4`, `evalM` over the moved prototype rows and the link rows, `evalL` over `lRows4`; the prover's masked `In` table `shift_in_table` (`chainLk4`, the start term at both chains' first blocks) |
| `ir.rs` | +99 | `spec_kind` (a mux program's `{L:…, P:…, N:…}` tables at an index), `run_regs` (all registers), `hashStmt` at `N`; `NodeCtx`/`run_node`: a node program's `targetS`, `shiftMask`, `linkWAll`, `rsWeight … true`, `evalM`, `evalL` from `nodeops.rs` |
| `circuit.rs` | +15 | `Circuit::build_general` (the tape without the chain kind's constant gates or input rows) |
| `main.rs` | +103 | modes `mfill-kat [M…] [--n N]` and `node-kat N8 [--m M] [--n N]` |
| `kat.rs` | +14 | `find_up` |

### 16.3 The prototype programs (an input the dump lacked)

`mregs-p{π}` numbers the registers of `protoProg π` (S-E12d: `progNodeG (cells4 .N4)`, `progSegG`),
but no ops file holds those programs: INT-8's `group-N/S.txt` are the post-INT-8 group programs
(97,657 registers against `mregs`' 97,414 / 97,257). I dumped them with a probe
(`logs/fr-build-P2q/p2probe/ProtoDump.lean` = `IRDump8`'s `showOp` in mux mode; `lean --run`
against the S-E12d build tree's oleans, copied to `logs/fr-build-P2q`; 7 s):
`logs/P2/r41p8/proto/proto-p0.txt` (106,242 ops, 97,414 registers), `proto-p1.txt` (106,085 ops,
97,257 registers). The register counts match `mregs`. **Request (S-E12e / INT-8's re-dump): write
`proto-p0.txt`/`proto-p1.txt` into every node dump** (the prover reads `FLOCK_PROTO_DIR`, default
the dump directory); a re-dump is then a reload.

### 16.4 KATs

**The M fill on the dumped rows** (`mfill-kat`, VM; `mfill-kat-1.txt`, `mfill-kat-2.txt`):

| slot | result |
|---|---|
| inactive (selectors 0, imports 0), prototype 0 and 1 | all 485,230 / 484,526 rows hold |
| prototype 1 at `L32` on an `L32` segment (n = 5) | the group program accepts (8,905 asks); **all rows hold; 0 conflicts between the run's values and the solve; 0 register-form mismatches** |
| prototype 1 at `P30` on an `L30` segment | the program rejects at line 106,084 (`finPf`'s last `assertEq`); 2 rows fail, 68 forms differ: **S-E12c §1's obstruction 1** (the pre-INT-8 group runs `L32`'s finals at every index). INT-8 removes it |

So `ir.rs` and the dump agree on every templated op (`walkAB`'s XOR DAG, `maskRows`, `rowW`,
`phiRS`, `tensorW`, `dotKF`, `eqTableK`, `lagrangeS`, `eqZ`, `slotW`, `eqPt`, `shiftEq`).

**The `N8` witness** (`node-kat N8 --m 32 --n 3`: two aggregates of one `L32` segment each, signed
by the test signer; `node-kat-2.txt`, `node-kat-3.txt`):

| relation | blocks / rows | bad |
|---|---|---:|
| every block's R1CS with its kind's target (`(A₀z)(B₀z) = z + E`) | 262,144 blocks (H 187,548) | 0 |
| the masked chain links (`chainLk4`) | 185,342 | 0 |
| the eight link families against the `WM` mirrors, both signed children | 2 × 1,046 sources | 0 bits |
| the nine public cells (`cells4`: `one`, `vk`, `c_A` from its `hashA` block) | 9 | 0 |
| L's declared bits | 8 × 8,220 | 0 |
| M: every slot's prototype rows, moved | 3,876,208 | 0 |
| M: link and activity rows (aggregate 0 and 1 with `k = 1`: slots 0 and 4 active) | 63 | 0 |

With `L30` children (`--m 30`, `node-kat-1.txt`): the same, except 4 M rows (2 per active slot):
obstruction 1 again.

**The node ops against the Lean** (`nodeops::tests::node_ops_match_lean`): probe
`logs/P2/r41p8/opsprobe/NodeOpsKat.lean`, `lean --run` against `fr-build-SCN4b`'s oleans (read
only; 15 min interpreted), prints S-CN4b's `targetSNode4I`, `shiftMask4I`, `linkWAll4I` and S-T2's
`rsWeightF4` (four claims, claim 2 kind-weighted) for `N2`, `N4`, `N8` at two points each
(`nodeops-kat.txt`, 24 lines). **The native specification forms equal all 24 byte for byte.** So
the native ops meet the Lean's computed ops on these points, and with them (`*_meets`) the specs.
`evalM`/`evalL` have no Lean computed form at 4.1 yet (`implN4` takes them from its base); they are
the rows' MLEs by definition.

**Layout figures** (`nodeops::tests::layout_figures`): `hEnd` 70,957 / 117,593 / 187,548
(S-E12a's `hEnd_eq`), `N4`'s `hUsed`, `lBase`, `oneCell` and `cells4` as `node-N4.txt`; (−)
`chainLk4` does not link the previous node's last block to the aggregate's first.

### 16.5 Times (VM, portable tier, 32 threads; not the runner)

`N8` witness 4.2–6.2 s: H inputs 0.07 s, the bit-sliced trace of 187,548 H blocks 0.21–0.23 s, L
and mirrors 0.001 s, **M fill 3.7–5.8 s**, writes 0.12 s; peak 5.7 GB (with the two `L32` proofs'
memory). One slot's fill: worklist 1.3 s, replayed plan 0.8 s (after skipping the inversion when
the unknown's coefficient is 1; it was 2.5 / 2.0 s), of which 0.35 s is the row check. The inactive
plans need no child and are recorded before a request (2.9 s). On the VM there is no `pclmulqdq`,
so every F product is the portable one: the runner's figure will be far lower; not measured.

**Deviations, provisional choices** (where the circuit is still open, S-E12a D6, the dump's
README):
1. A signed child's signature, digits and step selectors are written in L slot `σ` for signed
   child `σ` (A.7 names "per slot"; 4.1 has 1 + k slots and two signed children). Only L's
   Booleanity reads them today.
2. `hashStmt` blocks of a slot whose child is of the other kind (A for a node, B1/B2 for a segment)
   and of an inactive slot hold the pins and zeros (B2's `h_in` = B1's `h_out` always).
3. An aggregate of `k < maxK` segments: the main chain past its stream hashes zero bytes; the
   unused candidate final blocks hash zeros from a zero `h_in`.
4. The M fill does not use the prototype rows' unbound imports' meaning (the replay `R`,
   `rsWeight`, the kind factor, `targetS`/`linkWAll`/`shiftMask`, `evalL`, the pack map): it writes
   the run's values, which is what the bound rows will require.

### 16.6 Handover: the remaining items, in order

1. **The node PIOP prover, `N8` first** (`node.rs` gives `z`, `A₀z`, `B₀z`, the public values):
   - Z: the zerocheck as the leaf's (round 1 on `a`, `b`, `z` per block), Z2 with `P^e =
     target_s_node4(r)`;
   - Lc: L3's seven kind values `v_κ` (the kind-folded `A₀z`, `B₀z` per kind), the walk with the
     masked row weights (`maskRows`), `free`'s closed-form term;
   - Sh: `Out` with `eq(τ,·)` masked by `chainLk4`, `In` = `nodeops::shift_in_table`, the eight
     link families in the same sumcheck (`κ_s^{f+2}`), the collapse over positions `< 1024`;
   - Lr over `lRows4` (`2^logL` rows), E2/E4 over the M rows (the `nodeshape.rs` surrogate's shape,
     now on `mfill`'s rows: `A_M f`, `B_M f`, `C_M f`, the transpose table at `r_{E2}`), E4 end
     `α₄ ‖ 0^16`;
   - RS with four claims (claim 2's weight by `kf4` at `β^(2^k)`; `ringswitch::weight_table` needs
     the per-block factor), B′ with the nine `cells4` point claims, Ligerito unchanged.
   - Check: `ir::run_node` on `ops-N8.txt` (INT-8's or S-F4's) with `NodeCtx`, accept and canary;
     a native `V_N` follows the same ops.
2. **Then `N4` (k = 2, 3) and `N2`** with that `N8` as slot 0's child (prototype 0's first honest
   fill). With S-E12d's prototypes an `N4` child is obstruction 3 (`hashStmt` at index `L32`
   computes a leaf statement) and `N2` obstruction 1: wait for INT-8's re-dump (`proto-p*.txt`
   beside it).
3. **`first`/`step`** per PROVER.md (step 1: two aggregates → `N8`; step `i`: `prev.bin` + one
   chain → `N2` (`k ≤ 2`) or `N4`), with SIGN; a short stream through `rf-oracle`.
4. **Where the rows come from on the runner (open, for the orchestrator).** The prover reads the
   rows from the 352 MB dump. On the runner it has only its binary and `/setup` (written by
   `prover setup` from the binary). The options: embed a compact form (≈ 3.3 M terms per
   prototype, coefficients mostly 1) in `prover.s` as data, or port `compileTF` + the layout hint
   to Rust with the dump as its KAT. This decides item 3's feasibility.
5. **Timings on the 7763** (node prove per kind, step at `n = 2^17, 2^18`, the mean, `2^20`, peak
   against 11G), against blueprint 4.2's N2 2.4 s, N4 4.1 s, N8 4.8 s. The M fill's replay is the
   first lever (one slot's solve is ≈ 330 k linear solves; on the runner's `pclmul` tier, and with
   the plans recorded in `prover setup`).

### 16.7 Checks and `prover.s`

- `cargo test --release`: **37 passed, 1 ignored** (`logs/P2/r41p8/cargo-test.txt`; new:
  `node_ops_match_lean`, 176 s for the brute-force `rsWeight` over `2^18` blocks × 128 stages, and
  `layout_figures`). Source rule (`logs/org20`): 300 files, 0 findings.
- `prover.s` regenerated (`build-asm.sh logs/P2/r41p8/asm`, `build-asm.log`): **8,108,075 bytes,
  sha256 `a2890a6591903c091a057cd87e4dc8e78b125ca25234495722d84cf4755ab42e`**; linked binary
  2,421,496 bytes, sha256 `57ecd041…52b4`; no machine path in the `.s`.
- Build trees: `logs/fr-build-P2q` (a copy of `fr-build-SE12d`, 5.4 GB, used only through its oleans
  for the prototype dump; can be deleted). `fr-build-SCN4b` was read, not written.

## 17. Pass 9 (revisions 4.1/4.3, track P2⁵): the node PIOP, the plan form, the stream

Status: 2026-10-29. **Items 1–5 of the brief done**: N8/N4/N2 node proofs accepted by INT-8's dumped
node programs (and by prototype 0's program at each kind's index), the node data embedded in
plan form (INT-9's) with a start-up rebuild KAT-equal to the full dump, `first`/`step` with SIGN
through `rf-oracle`, and 7763 timings. Logs: `logs/P2/r41p9/` (VM) and `logs/P2/run-40801562683`,
`-40801564683`, `-40801567863` (runners, all AMD EPYC 7763, 4 vCPU). Probe branches
`probe/p2t-9a/9b/9c` (commit `ae083d0` on `39fb161`, temporary index: prover/, `probe/p2t9/`,
`.github/probe.conf`), deleted after their runs.

### 17.1 What was built (crate 13,530 `.rs` lines, was 11,881)

| file | change |
|---|---|
| `nodeprove.rs` | new, 624 lines (with test): **the node prover**. Z (all blocks; `P^e` = `targetS` of the node), Lc (the seven H kinds' `η_κ = A₀ᵀ(maskRows)` on the base matrix and `free`'s `(1+α)·rowW`, one 8-pair 14-round sumcheck over per-kind partial folds computed in one pass; L3 = `v_κ`, `free` last), Sh (rank-one terms `e(y)·sw(p)` keyed by slot weight: `Out` masked by `chainLk4`, `In` = `shift_in_table`, the 8 link families' source and mirror slots at `κ_s^{f+2}`; then the 10-round collapse), Lr (`b·(one+b)`, Gruen zerocheck from claim 0), E2 (the M rows' `eq·(ab + c)`), E4 (`W_M(r_E2) + κ_E³ W_L(r_Lr)` scattered per slot, then the lincheck; end `f̂(r′) ‖ 0`), RS (four claims, Lc's outer weight × `kf4`), B′ (the nine `cells4` at `κ′^{j+2}` in Ligerito's weight and claim); `stmt_ok4`; `Mats` (M matvec and transpose scatter) |
| `plan.rs` | new, 577: **the node data on the runner**: INT-9's `plan-form-p{π}.bin` reader (`read_planform`, by its README), the register forms and imports varint-coded, `proto-p{π}.txt`, `node-N*.txt`; LZ77 + base64 blob `nodeblob.b64` (`include_str!`), decoded once at start (`node_data`; the dumps when `FLOCK_NODE_DUMP` is set); `proto_eq` (the KAT) |
| `stream.rs` | new, 156: `first`/`step` (PROVER.md §3): aggregates through the service (record, replay, SIGN), node witness, node proof (recorded), the node's trace by replaying the kind's program without node ops, SIGN, `proof.bin`; `step` picks N2 (≤ 2 segments) or N4 |
| `nodeblob.b64` | new, generated (`flock-prover plan-build`): 5,429,184 B from `logs/INT-9/nodedump` |
| `circuit.rs` | `Circuit::build_base()`: A.6's base block matrix (`FRBlake2sCircuit.rowOf`: inputs `(var k, one)` at 0…255 and 512…1151, `(one, one)` at 1152), the node's `walkAB`; equal to `build()` on the chain kind's rows |
| `ir.rs` | `with_cells` (INT-8's `ops-N*` carry placeholder cells `oneCell + j`; the real `cells4` enter only as `finPf`'s 9 × 25 `keep` flags), `run_node_regs`, `FLOCK_IRPROF` op timing |
| `nodeops.rs` | `rs_weight4` per run of one kind (`kind_runs`, two prefix sums of the product function per run and stage) instead of the brute force over `2^nb` blocks: 34 s → < 0.1 s per call |
| `mfill.rs` | `try_row` also solves a row with a known zero factor as `C = 0` (S-E12e's `tplShiftSeg` inverse at `0`); `KindTab::parse`; default dump `logs/INT-9/nodedump` |
| `node.rs` | `PrevIn { ctx, base }`: a previous-node slot runs its program with the node ops and the base matrix |
| `leaf.rs`, `ringswitch.rs` | `z2_value_pe`; helpers `pub(crate)`; `weight_table_kf` (a per-block factor on a claim's outer weight before `Φ`) |
| `main.rs` | modes `first`, `step`, `plan-build`, `plan-kat`; `node-kat N8|N4|N2 [--prev F] [--agg N] [--prove] [--out-signed F]`; native `acc` accepts node files (the kind's program with node ops, then `stmtOk4`) |
| `kat.rs`, `items.rs`, `ir.rs` tests | default IR dump `logs/INT-8/dump` (`items.json` byte-identical to S-F4's) |
| `probe/p2t9/run.sh`, `stream.sh` | new: build as the runner does, a stream through `rf-oracle`, `acc` and canary per output |

### 17.2 Item 1: the N8 proving protocol

`node-kat N8 --prove` (two signed aggregates; the IR run uses INT-8's `ops-N8` with the real cells):

| children | data | IR (`ops-N8`, real cells) | log |
|---|---|---|---|
| 2 × (k=1, L32, n=3) | S-E12d dump | accept, 8,905 asks, `stmtOk4` | `node-prove-1.txt` |
| 2 × (k=2, L32+L32, n=393,217) | S-E12d, from the blob | accept | `node-prove-2.txt` |
| 2 × (k=1, L32, n=3) | INT-9, from the blob | accept | `node-prove-int9-m32n3.txt` |
| 2 × (k=2, L32+L31, n=327,681) | INT-9, from the blob | accept | `node-prove-int9-agg327681.txt` |

Canaries rejected in every case: another statement; a flipped byte in the E field; the program with
the placeholder cells. Before proving, every relation of the witness holds (`node::check`).

### 17.3 Item 2: the plan-form embedding

- INT-9's plan form is read by its README's specification; the blob also carries the register forms
  and imports (2.1 / 2.5 MB varint), the two prototype programs and the three slot tables. Raw
  14.45 MB, LZ 4.07 MB, **base64 5,429,184 B** (`plan-build-2.txt`).
- **KAT** (`plan-kat-2.txt`; test `plan_rebuild_kat`): the rebuilt prototypes equal `Proto::load`
  of the full dump field by field (rows in order: 428,815 / 427,104 rows, 2,417,424 / 2,623,206
  terms, indices, ranges, cells, coefficients; 97,657 / 97,409 register forms; 1,753 imports;
  programs and slot tables byte-equal). **Decode at start 0.31 s** (VM).
- Before INT-9 landed I derived a plan form from S-E12d's dump myself (13.6 MB base64, KAT equal);
  dropped for INT-9's.
- **`prover.s`: 14,630,224 B**; the runner's link (`gcc -static -O2 -pthread`) **0.54 s on the 7763**
  (1.14 s on 4 VM cores) against `build_s = 120 s`; the three runners rebuilt `prover.s` byte for
  byte (sha256 `9b4e7690…eb57`). The binary carries no dump: the probes ran from `/tmp` work
  directories.

### 17.4 Item 3: N4 (k = 2, 3) and N2 with that N8 as slot 0's child

On INT-9's data from the blob (`n8.signed` = the N8 above, signed by the test signer over the
trace its program asked):

| node | slot-0 child | aggregate | IR | log |
|---|---|---|---|---|
| N4 | N8 | k=2 (L32 + L30), n = 262,147 | accept | `n4k2.txt` |
| N4 | N8 | k=3 (2 × L32 + L30), n = 524,291 | accept | `n4k3.txt` |
| N2 | N8 | k=2, n = 262,147 | accept | `n2.txt` |
| N4 | N4 | k=2 | accept | `n4n4.txt` |
| N2 | N2 | k=1 (L31), n = 131,075 | accept | `n2n2.txt` |

So prototype 0 is filled honestly at all three indices (N4, N2, N8), and the segment prototype at
L30, L31, L32. All canaries rejected, `stmtOk4` holds, 8,905 asks each.

### 17.5 Item 4: `first`/`step` with SIGN, a stream

- Local (`stream-local2/`, the asm-built binary, `rf-oracle` of `logs/org20`): first N8 (131,077 +
  70,001), step N4 (524,295), step N2 (150,001): native `acc` accepts each output, each canary
  (statement bit flipped) rejected.
- Runners: 3 streams × 7 outputs, **21 accepted, 21 canaries rejected** (17.6).

### 17.6 Item 5: 7763 timings (3 runs; `runner-steps.txt`; total = the whole request)

| step | kind | chain(s) | aggregate | witness | **node prove** | trace+SIGN | total | peak RSS |
|---|---|---|---|---|---|---|---|---|
| 1 | N8 | 2^18 + 2^18 | 9.88–10.09 | 2.00–2.06 | **7.41–7.50** | 0.13 | 19.5–19.8 | 5.76 GB |
| 2, 7 | N2 | 2^17 | 2.57–2.62 | 1.70–1.91 | **3.72–3.90** | 0.09–0.10 | 8.17–8.43 | 3.03 GB |
| 3 | N2 | 2^18 | 5.02–5.08 | 1.46–1.48 | **3.77–3.82** | 0.09 | 10.35–10.49 | 5.65 GB |
| 4 | N2 | 3·2^17 (k=2) | 7.53–7.60 | 1.72–1.74 | **3.68–3.77** | 0.09 | 13.0–13.2 | 5.65 GB |
| 5 | N4 | 3·2^18 (k=3) | 14.66–14.81 | 1.91–1.94 | **7.51–7.66** | 0.13–0.14 | 24.3–24.5 | 6.02 GB |
| 6 | N4 | 2^20 (k=4) | 19.60–19.76 | 2.23–2.28 | **7.82–7.93** | 0.13–0.14 | 29.8–30.1 | 6.54 GB |

Node prove phases (7763, s): N8 commit 1.10–1.14, Z round 1 1.54–1.56, Z tail 0.74–0.75, Lc 0.21,
Sh 0.53–0.59, Lr 0.002, E2 0.26, E4 0.81–0.83, **RS 1.44–1.48**, Ligerito 0.73–0.74. N4 the same
but RS 1.56–1.73. N2: about half (0.52, 0.77–0.88, 0.37, 0.11, 0.26–0.28, 0.11, 0.40, 0.75–0.80, 0.37).

**Against blueprint 4.2's model** (N2 2.4 s, N4 4.1 s, N8 4.8 s; I read them as the node proof
alone): measured **N2 3.7–3.9 s (×1.6), N4 7.5–7.9 s (×1.9), N8 7.4–7.5 s (×1.55)**, plus the
witness (1.5–2.3 s: the M fill, the previous node's program run) not in the model. Where the gap is:
- **RS 1.45–1.7 s** (the leaf's is ≈ 0.35–0.47): the E4 claim's slices are a dense
  `ringswitch::partials` over all `2^25` elements, and `weight_table_kf` runs four claims of which
  three are dense (Z, Lc with `kf`, E4) — each `Φ` table pass is 16 lookups per element.
- commit 1.1 s, Z 2.3 s and Ligerito 0.74 s are the L32 leaf's; Lc, Sh, E2, E4 together 1.8 s.
- N4 = N8 at m = 32: the model's 4.1 s for N4 vs 4.8 s for N8 assumes a smaller N4; at 4.1 the
  shapes are equal (`blocks = 2^18`, `logM = 23`), so their times are equal here.

### 17.7 Checks and `prover.s`

- `cargo test --release`: **40 passed, 1 ignored** (`cargo-test.txt`; new: `node_n8_accepted`,
  `plan_rebuild_kat`, `lz_b64_roundtrip`; `node_ops_match_lean` 176 → 5 s).
- Source rule (`logs/org20`): 313 files, 0 findings.
- **`prover.s` 14,630,224 B, sha256 `9b4e76900a37fe3fe3d1e39527dc21555fa55650537ae0ba877ecbf9af04eb57`**
  (`build-asm.log`); runner binary `bae6db36…c4bd`; SELFTEST `tier=ymm` on all three runners; no
  machine path in the `.s`.

### 17.8 Deviations and provisional choices

1. **The node programs' cells.** INT-8's `ops-N*.txt` carry placeholder cells; the native checks use
   prototype 0's program (`progNodeGK N4c.cells4`, real cells) at the kind's index, which
   `with_cells(ops-N*)` reproduces byte for byte (checked in every `node-kat` run).
2. **The node's trace** (`stream.rs`) is produced by replaying the kind's program **without its node
   ops** (their zeros make the run reject, but the asks are the item sequence, which does not depend
   on them). The output is then checked by the full `acc` (runner side and probe).
3. **The witness's provisional layout choices** of §16.5 (L slot of a signed child's signature,
   free `stmt` blocks, a short aggregate's padding) are unchanged; INT-9's rows accept them.
4. **The solver extension** (`try_row`'s zero factor) is needed by S-E12e's templates (an inverse
   gate at 0). It solves only what the row forces.

### 17.9 Handover: what remains, in order

1. **Reload S-E12f's re-dump** when it lands (745 `tensorW` and 2 `eqPt` templated again; more
   rows): `flock-prover plan-build --out nodeblob.b64` (from `FLOCK_NODE_DUMP` or
   `logs/<new>/nodedump`; point `mfill::find_dirs`' default at it), `plan-kat`, the `node-kat` runs
   of 17.2/17.4, `cargo test --release`, regenerate `prover.s`. If the fill reports failed rows, the
   new templates' gates need the solver (as for `tplShiftSeg`).
2. **Node prove time** (17.6), first lever RS: compute the E4 claim's slices from E4's own folds
   (the bit columns folded alongside `f`, or the first rounds' tables), and the `Φ` passes of the
   dense claims fused in one sweep over `y` (one load of `e` per claim, one store of `W`).
   Then the witness's M fill (1.5–2.3 s; plans recorded in `prover setup`).
3. The aggregate inside a step dominates long chains (2^20: 19.7 s of 29.9 s); its segments are the
   leaf prover's (§15.3 fits).

## 18. Pass 10 (track P2⁶): node prover speed, the stream handshake, S-E12f's re-dump

Status: 2026-10-29. **Items 1–5 of the brief done.** Logs: `logs/P2/r41p10/` (VM) and the runner
runs `logs/P2/run-40804570637`, `-40804583754` (profile + `bench-rs`, 7763),
`-40807403527` (S-E12f data, `FLOCK_IRPROF`, 7763), and the final run **`-40808376661`** (7763, two
streams), plus `-40807399590/-40807406302/-40808367114/-40808371822/-40808373912` (EPYC 9V74 / 9V45
/ Xeon 8370C, off tier, acceptance only). Probe `probe/p2t10/` (branches `probe/p2t-10a … 10i`,
temporary-index commits on HEAD, all deleted). π is byte-identical to pass 9's prover at every
step (local oracle, `node-kat`: N4 `5062cfc4…`, N2 `20d1eb92…` on INT-9's data; N2 `9368bcae…` on
S-E12f's data before and after the last changes).

### 18.1 What was built (crate 14,093 `.rs` lines, was 13,530; +648 −85)

| file | change |
|---|---|
| `stream.rs` (+60 −30) | **the `ready`/`go`/`done` handshake** (PROVER.md §3; it was missing, finding below); `Pre`: the node data, the three kind tables, the circuits, the inactive solve plans, the skip tables and a 6000 MiB prefault (`FLOCK_PREFAULT_MIB`) before `ready`; `STREAM` line with `startup_s` and `\| prof …` |
| `ringswitch.rs` (+101) | **`weight_table_rows`**: the RS weight table by row tables (below); `weight_table_kf_ref` kept as the reference; test `weight_rows_and_fold_slices` |
| `sumcheck.rs` (+117) | **`prove_pair_support`**: E4's sumcheck on `W`'s support; test `pair_support_same_messages` |
| `nodeprove.rs` (+22 −5) | E4 by `prove_pair_support` (no `f.to_vec()`, `W` zeroed in parallel), **E4's slices from the block fold** right after E4; spans |
| `nodeops.rs` (+150 −17) | **`target_words` by regions** (was 1,216 `target()` calls per block kind), **`target_s_node4` by byte tables** (no `HashMap`, parallel), **`eval_m` factorized** (`eq(τ,row) = eq(τ_{<20}, local)·eq(τ_{≥20}, v)`, the same for cells; `eval_m_ref` kept); test `fast_target_and_eval_m` |
| `node.rs` (+65 −17) | **the witness schedule**: the H part (`h_part`: inputs, the block trace as its own parallel job, mirrors, L) as one task beside the first fill of each prototype, then the other slots; `trace_blocks`' pinned masks per kind of the batch; spans |
| `mfill.rs` (+29 −12) | `try_row` without a heap allocation; `mul1` (no product by a coefficient 1) in `try_row`, `Rows::eval`, `m_scatter`; default dump `logs/S-E12f/nodedump`; spans |
| `simd.rs` (+46) | `xor_rows` (AVX2 kernel, portable fallback) |
| `ir.rs` (+14), `bench.rs` (+40), `main.rs` (+4 −3) | `FLOCK_IRPROF` per-op-name totals; mode `bench-rs [m]`; `heap_setup`/`say`/`wait_go` crate-visible |
| `nodeblob.b64` | regenerated from `logs/S-E12f/nodedump`: 5,524,560 B |
| `probe/p2t10/run.sh`, `stream.sh` | new: the handshake (inputs staged, moved in at `go`; `req_s` = `go` → `done`), `FLOCK_PROF`, optional `bench-rs` / `FLOCK_IRPROF`, two streams |

### 18.2 Item 1: the profile (7763, pass 9's algorithms with spans; runs 40804570637/583754)

| phase (s) | N2 | N4 | N8 |
|---|---|---|---|
| witness | 1.29–1.65 | 1.78–2.18 | 1.94 |
| of which: H trace / slot 0's program run / a fill (each) | 0.39 / 0.39–0.75 / 0.13–0.32 | 0.65 / 0.39–0.61 / 0.13–0.35 | 1.02 / – / 0.2–0.3 |
| commit · Z round 1 · Z tail | 0.54 · 0.83 · 0.40 | 1.12 · 1.66 · 0.79 | 1.13 · 1.62 · 0.80 |
| Lc · Sh · Lr · E2 | 0.11 · 0.26 · 0.002 · 0.11 | 0.21 · 0.52 · 0.002 · 0.20 | 0.21 · 0.55 · 0.002 · 0.26 |
| E4 (scatter + sumcheck) | 0.41 (0.12 +) | 0.79 (0.21 +) | 0.83 (0.25 +) |
| RS (pass 9: 0.75–0.80 / 1.56–1.73 / 1.44–1.48) | 0.36 | 0.72 | 0.71 |
| Ligerito | 0.36 | 0.71 | 0.72 |

The slot-0 program run (the previous node's program, for its registers) was **`evalM` 0.58–0.83 s
and `targetS` 0.26–0.54 s** (`FLOCK_IRPROF`, run 40807403527); every other op of the 106 k is
< 7 ms. `targetS` called `target()` 1,216 times per distinct block kind (the stream blocks' counters
make almost every block distinct).

### 18.3 Item 2: ring switching (`bench-rs 32`, 7763, 4 threads, every result equal to the reference)

| pass | before | after |
|---|---:|---:|
| E4's slices: `ringswitch::partials` (a 16-table pass over all `2^25` elements) → the block fold (`lincheck::partial_fold` at `r4[7..]`, the leaf Lc's stripes) then `partials_from_fold` at `r4[..7]` | 0.235 | 0.195 |
| the four-claim weight table (3 dense, `kf` on Lc's): per element `e_lo·e_hi` and 16 lookups in a 64 KiB table per claim → **row tables** | 0.83 | 0.52 (lo 4, used) · 0.49 (5) · 0.47 (6) |

**Row tables.** Split `y = l + 2^lo·h`. For each claim the map `a ↦ c·Φ(e_lo(l)·a)` is `F₂`-linear.
So with the 16 bytes `β_p` of `e_hi(h)`, the row is `W(·, h) = Σ_p Q[p][β_p][·]`, where
`Q[p][β][l] = Σ_{i∈β} c·Φ(e_lo(l)·b_{8p+i})`. The tables are built from `128·2^lo` values of `Φ`.
Each output element is 16 sequential row reads per claim. There is no product per element. The kind
factor multiplies `e_hi` once per block, and rows with `e_hi = 0` are skipped (the shift claim's
zero coordinates).

**"Fuse the dense passes"**: the reference already ran all claims per 1,024-element chunk. The
row form removes the per-element products and the scattered loads instead. `lo = 4` is the
default; 5–6 save another 0.03–0.05 s for 1–4 MB of tables per claim.

**E4 on `W`'s support** (not in the brief; found in the profile). `W = W_M(r_E2) + κ³W_L` is non-zero
only on the M slots, the L bits and the one cell, which is 16–25 % of `f`.
- The first 12 rounds sum and fold only the 4,096-element chunks where `W ≠ 0`.
- A dead chunk's `f` still enters the later rounds, paired with live entries through
  `(P₀+P₁)(Q₀+Q₁)` and through the folds. So after round 12 it is computed directly as
  `Σ_l eq(r_{<12}, l)·f[4096c + l]`, one dot product per chunk.
- My first version zeroed the dead chunks instead: π changed and the dumped program rejected it at
  op 66,610 (`b-N2.txt`). The test now compares every message and the final pair with
  `prove_pairs`'s.

Result on the 7763: E4 0.79–0.83 → 0.59–0.61 s (N4/N8), 0.41 → 0.32–0.33 s (N2).

### 18.4 Item 3: the witness

- **Before `ready`** (untimed): the inactive solve plans (`warm_plans`, inside the timed witness
  in pass 9), the node data, the kind tables, the circuits, the 6000 MiB prefault.
- **Schedule**: the H part runs as one task. Its 64-block trace is a separate parallel job, and idle
  workers pick it up. It runs beside the first active fill of each prototype (slot 0's run and solve
  are serial). The remaining slots replay the recorded plans afterwards. VM at 4 threads, N2:
  7.49 → 5.81 s.
- **Slot 0's program run**: `targetS` by regions and byte tables, `evalM` factorized
  (§18.1). Both equal the reference (test, and the Lean KAT `node_ops_match_lean`).
- `try_row` no longer allocates. Products by a coefficient 1 are skipped (most M coefficients are 1).
- Result (7763, final run): witness **N2 1.18–1.52 s, N4 1.63–1.76, N8 1.93**. The critical path is now
  the H part: inputs 0.06–0.21 s and a trace of 0.73–1.07 s, sharing the cores with the slot runs.

### 18.5 Item 4: S-E12f's re-dump (`ef18e75`, `logs/S-E12f/nodedump/`, SHA256SUMS OK)

- `plan-build` → `nodeblob.b64` 5,524,560 B (raw 14.74 MB, LZ 4.14 MB; `plan-build.txt`).
- `plan-kat` (`plan-kat.txt`): p0/p1 rows 603,404 / 593,997, terms 5,244,098 / 5,325,108, 2,498 aux
  each, register forms, programs and slot tables equal; decode 0.51 s (VM).
- **The fill needs no solver extension.** In every slot: 0 failed rows, 0 conflicts, 0 form
  mismatches. N8 checks 4,751,976 M rows, `m_bad` 0. Every kind-mux sub-template's locals are solved
  from the three kinds' operands, whichever kind is selected, as S-E12f's README asks. The 14
  untracked kind-muxed registers (`mkslots`) need nothing from the prover.
- `node-kat` (`e-*.txt`): N8 (2 × L32, n = 3), N4 on that N8 (k = 3), N2 on N8 (k = 2), N4 on N4, N2
  on N2. All accepted by the dumped programs (`ops-N*`, real cells = proto-p0 at the kind's index),
  with `stmtOk4` and 8,905 asks. Canaries rejected: another statement, a flipped E byte, the
  placeholder-cell program.
- Runners: 4 streams × 8 outputs on S-E12f's data (+ 4 off-tier): **every output accepted by the
  native `acc`, every canary rejected** (64/64 on the final probe set).

### 18.6 Item 5: 7763 times (run 40808376661, two streams; `req_s` = `go` → `done`)

| step | kind | chain(s) | aggregate | witness | **node prove** | trace+SIGN | **request** | start-up | peak RSS |
|---|---|---|---|---|---|---|---|---|---|
| 1 | N8 | 2^18 + 2^18 | 10.50–10.63 | 1.93 | **6.36–6.38** | 0.14 | **18.95–19.07** | 0.78–0.81 | 6.94 GB |
| 2, 8 | N2 | 2^17 | 2.62–2.65 | 1.36–1.52 | **3.16–3.19** | 0.09–0.10 | **7.25–7.43** | 0.76–0.79 | 6.84 GB |
| 3 | N2 | 2^18 | 5.26–5.30 | 1.18–1.20 | **3.15–3.16** | 0.10 | **9.71–9.74** | 0.77 | 6.83 GB |
| 4 | N2 | 1.19·2^18 = 311,951 (L32 + L30) | 6.38–6.45 | 1.42–1.47 | **3.14–3.15** | 0.10 | **11.03–11.16** | 0.77–0.79 | 6.84 GB |
| 5 | N2 | 3·2^17 (L32 + L31) | 7.85–7.95 | 1.41–1.47 | **3.17** | 0.10 | **12.52–12.69** | 0.78–0.80 | 6.84 GB |
| 6 | N4 | 3·2^18 (k = 3) | 15.73–15.95 | 1.63–1.66 | **6.24–6.39** | 0.14 | **23.77–24.11** | 0.76–0.83 | 6.96 GB |
| 7 | N4 | 2^20 (k = 4) | 20.90–21.06 | 1.73–1.76 | **6.21–6.32** | 0.13–0.14 | **28.97–29.28** | 0.77–0.78 | 6.97 GB |

**Node prove against pass 9:**

| kind | pass 9 | this pass | blueprint 4.2 model |
|---|---|---|---|
| N2 | 3.7–3.9 s | **3.14–3.19 s** (−17 %) | 2.4 s |
| N4 | 7.5–7.9 s | **6.21–6.39 s** (−18 %) | 4.1 s |
| N8 | 7.4–7.5 s | **6.36–6.38 s** (−15 %) | 4.8 s |

**Node part of a step** (request − aggregate): N2 4.45–4.8 s, N4 8.0–8.2 s (pass 9: N2 5.6–5.9,
N4 9.2–10.1 with the plans inside the witness).

**N4 prove phases** (s): commit 1.16–1.20, Z round 1 1.33–1.39, Z tail 0.84–0.86, Lc 0.20, Sh 0.53–0.56,
E2 0.27–0.28, E4 0.59–0.61, RS 0.53–0.55, Ligerito 0.72–0.74. The leaf-shaped phases (commit, Z,
Ligerito) are 4.1 s of the 6.3 s.

**The stream projection** (`project.py`, `project.txt`). The model is `step(n) = agg(n) + node`, using
the split rule (`L32`, remainder `L30`/`L31`/`L32`) and the segment fits calibrated on the measured
aggregates. It uses node parts N2 4.65 s, N4 8.15 s, N8 8.45 s. It reproduces the table to within
0.2 s.
- The overhead per step is blueprint 4.2's 1.6 s with the 0.22 s `ready` replaced by the measured
  start-up of 0.78 s, which gives 2.16 s.
- Steps: **2^17 7.28 s, 2^18 9.93 s, 1.19·2^18 11.09 s, 2^20 29.27 s**; step 1 (2 × 2^18) 19.0 s.
- **The mean step over the `1/n²` density is 12.10 s + 2.16 = 14.26 s.**
- **The stream fits `M ≤ 66`.** `P(M > 66) = 89 %`; simulated over `M = 64 + Geom(16) ≤ 112` and the
  chain draws, **82 % of evaluations are truncated**. `P̄ ≈ 10.8 s`.

Blueprint 4.2 assumed 8.91 + 1.64 s, `M ≤ 85` and 28 % truncated. The gap is the node part of every
step: 4.45–4.8 s against 2.4 s for N2, and 8.1 s against 4.1 s for N4. Long chains weigh heavily
in the mean (2^20 costs 29 s).

### 18.7 Checks and `prover.s`

- `cargo test --release`: **43 passed, 1 ignored** (`cargo-test-2.txt`; new: `weight_rows_and_fold_slices`,
  `pair_support_same_messages`, `fast_target_and_eval_m`).
- Source rule (`logs/org20`): 333 files, 0 findings.
- **`prover.s` 15,084,266 B, sha256 `a3db3bb589d2cb83736b24ef1dfa47411d2fa067acee97ff973573f82092abdd`**
  (`build-asm-c.log`). The runners rebuilt it byte for byte (5/5).
- Peak RSS ≤ 6.97 GB (≤ 11 G).

### 18.8 Deviations, findings, open questions

1. **Finding: pass 9's `first`/`step` had no handshake.** The harness (`rfh/prover.py`) waits for
   `ready` and then sends `go`. Pass 9's binary would have failed every request with "no ready line".
   Fixed here, and the probe now drives the handshake. Start-up is 0.6–0.8 s on the 7763
   (`ready_s` = 10 s). It counts against `stream_s` (not `P`), so the 6000 MiB prefault (≈ 0.5 s
   of it) trades stream time for request time. `FLOCK_PREFAULT_MIB` sets it.
2. **E4's sumcheck on `W`'s support** is beyond the brief's wording ("E4's own folds"). The
   messages are `prove_pairs`'s (test), and π is unchanged.
3. **No solver extension** was needed for S-E12f.
4. **For the orchestrator**: at the measured step times the stream truncates in about 80 % of
   evaluations (§18.6). The blueprint's change-26/28 tables need the node figures replaced: N2 node part
   4.6 s, N4 8.1 s.

### 18.9 Handover: what remains, in order

1. **The witness's H part** (critical path, 0.8–1.3 s): the 64-block `trace_blocks` (general
   circuit, bit-sliced). Profile it with one thread, for example the per-batch circuit eval, the
   input-position loop and the three 64×64 transposes. Also consider making the two main chains'
   inputs parallel earlier.
2. **Slot 0's fill** records the p0 plan by worklist every step (0.35 s): p0 has a single active
   slot. A plan recorded at `prover setup` (untimed: a toy N8 → N4/N2 per previous kind, stored in
   `/setup`) would replay it. The replay check falls back safely.
3. RS: `lo = 5–6` (−0.03–0.05 s). E2 on the M rows' support, the same idea as E4 (E2 0.27 s; the
   rows are about 30 % of `2^logM`).
4. The leaf-shaped phases (commit, Z, Ligerito: 4.1 s of N4's 6.3 s) and the aggregate's segments
   are the bulk of every step. They are the levers for `M`.

## 19. Pass 11 (track P2⁷): step time; S-E13a's matrices and S-E13b's cells

Status: 2026-10-29. Logs: `logs/P2/r41p11/` (VM) and the runner runs `logs/P2/run-40812467041`
(p2t-11a), `-40814845050` (11d), `-40817225300` (11e), and the final run **`-40820003716`** on S-E13a's data
(§19.6). Each probe ran the base (HEAD's committed `prover.s`, `a3db3bb5…`) and the new prover on
the same runner, through `probe/p2t11/` (branches `probe/p2t-11a … 11h`, temporary-index commits on
HEAD, all deleted). Off-tier runs (EPYC 9V74: 11b, 11c, 11f, …) are acceptance only.
**π is byte-identical** to pass 10's prover on every KAT (local oracle): N2 over pass 10's N8
`9368bcae…` (k = 2), `f60dc083…` (k = 1, `--agg 131077`), N4 `a16ab6a3…` (k = 3), until the
S-E13a data change (§19.5), which changes the node matrices and so π.

### 19.1 What was built (crate 15,026 `.rs` lines, was 14,093)

| file | change |
|---|---|
| `node.rs` | **`trace_blocks` rewritten** (`trace_prog`: the general tape compiled once, XOR forms in 573 reused slots, gates keep their rows' forms; inputs by 64×64 transposes; per-kind pin words; positions interleaved by four words so the output is AVX2 four-word transposes); `trace_blocks_ref` kept; `slot_fill`/`slot0_fill` (slot 0's fill callable on its own); every slot with a known order starts beside the H part; partial segments use their own plan key; **S-E13b's L cells** and the whole `r` mirror (§19.5); `Checks::first_bad_links`; test `trace_blocks_matches_ref` |
| `mfill.rs` | plans keyed `0` inactive, `1 + ix` full child, `4 + ix` partial segment; **tolerant replay** (missed entries retried, then the row check; a short replay is **completed by the worklist from where it stopped**, adjacency cached per prototype); `save_plans`/`load_plans` (`FLPLAN02`, tagged by the node blob's hash), the inactive fills (`save/load_inactive`), `set_exact_plans`; test `plans_round_trip` |
| `stream.rs` | **`prover setup DIR`** (§19.3); `Pre::new` loads the setup (plans, inactive fills), builds the adjacency and the trace tape; **slot 0's fill on its own thread beside the aggregate**; start-up breakdown `su=` in the `STREAM` line |
| `zerocheck.rs` | **zero skips**: round 1 skips windows whose a, b, z are zero (the convert tables map 0 to 0, checked); `round_x6`, `round_tab` skip ranges where a or b is zero; `fold_x6` writes zeros for zero rows; test `round1_zero_windows_skipped_equal` |
| `lincheck.rs`, `nodeprove.rs` | the block folds skip zero stripes; spans `sh.collapse/pairs/prefix` |
| `ringswitch.rs` | `ROW_LO` 4 → 6; the claims' row tables built in parallel |
| `oracle.rs` | `Tape` (a recording oracle; setup's toy chain) |
| `plan.rs` | `data_tag`; decode spans; `nodeblob.b64` from `logs/S-E13a/nodedump` (7,397,352 B) |
| `bench.rs`, `main.rs` | mode `bench-trace [N2/N4/N8]`; mode `setup` |
| `probe/p2t11/run.sh`, `stream.sh` | base and new on one runner, `prover setup` timed and sized, optional A/B stream (`P2T11_ALT`), `acc` timed |

### 19.2 Lever 1: the witness (7763)

- **`trace_blocks`** (`bench-trace`, VM, one thread, checked equal): 1.39 → 0.53 ms per batch of 64
  blocks (all threads 0.36 → 0.13 s for N2's 1,109 batches). On the 7763 `h_trace` 0.74 → 0.17 s
  (N2), 0.29 s (N4, contended).
- **Slot 0's fill** (the previous node's program run and its solve, 0.6–1.3 s) needs only
  `prev.bin`: it runs on its own thread while the aggregate is proved. It costs the aggregate
  +0.05…+0.36 s (largest at 2^17); nice 19 did not change that (run 40814845050: so the cost is the
  shared core, not CPU share; nice removed). Inside the witness instead (`FLOCK_NO_PRE0=1`, run
  40817225300) is ≈ 0.1 s worse per step.
- **Every slot whose order is known starts beside the H part.**
- **Zero windows**: a third of a node's witness is zero (N2: 87,875 of 262,144 round-1 windows: the
  L region past its used part, the tail past M, holes in M).
- Witness N2 1.15–1.50 → **0.37–0.55 s**, N4 1.64–1.81 → **0.67–0.89 s**, N8 1.91 → **0.67 s**.

### 19.3 Lever 2: `prover setup` (240 s untimed, 4 GiB)

`prover setup DIR` proves a toy chain with a local oracle and the test signer (no service exists
then): N8 over two one-segment aggregates; N2 over it (a partial L32, 200,003 steps); N4 over it
(L32, L32, L30); a witness over L32 + L31; slot 0's fill after the N2 and after the N4. Every fill
records its own key's order (`set_exact_plans`): p0 at N4/N2/N8 (446,067 entries each), p1 inactive,
L32 full/partial, L30 and L31 partial. Stored: `plans.bin` (33.2 MB) and the two inactive fills
(16 MiB each). **7763: 63.9 s, peak 7.09 GB, 66.8 MB** (run 40817225300).

A request loads them before `ready` and replays them. A replay can fall short when the child's data
differs (a partial L32 at another `n`: 65 of 436,594 entries). Then the rows that fail the check are
completed by the worklist from where the replay stopped. The deduction is monotone, so its closure
does not depend on the order, and π equals the from-scratch solve's (KAT `f60dc083…`, base and new).
A stale or foreign `plans.bin` is refused by its tag; with no setup the prover behaves as before.

Start-up 0.71–0.74 → **0.48 s** (no inactive solves before `ready`; node data 0.14 s, prefault
0.28 s).

### 19.4 Levers 3–4: the node prove (7763)

| phase change | N2 | N4 |
|---|---|---|
| round 1, zero windows skipped | 0.69 → ≈ 0.46 | 1.35 → ≈ 0.9 |
| `round_x6`, `fold_x6`, `round_tab` on zero ranges | part of Z tail | |
| RS `ROW_LO` 6, tables in parallel | −0.03…−0.05 per RS (node and segment) | |
| **node prove** | 3.11–3.18 → **2.64–2.67** | 6.2 → **5.02–5.08** |

N8 6.37 → 5.80–5.82 s.

### 19.5 S-E13a's matrices, S-E13b's cells (the orchestrator's request)

- `logs/S-E13a/nodedump` (SHA256SUMS OK) is the default dump; `plan-build` → `nodeblob.b64`
  (7,397,352 B; raw 27.1 MB, was 14.7: the kind tables carry the new link rows); `plan-kat`: the
  prototypes and plan forms equal.
- **The completeness check S-E13a could not run** (the row checker, `node::check`, on honest
  witnesses, before any prover change): **the pack rows (kind tie + 8,905 `wf` pins per aligned
  slot) all hold.** **102 (N8) / 100 (N2) link rows fail, all S-E13b's WOTS rows in slot 1** (offsets
  1,626–7,875 of slot 1's link region): the prover did not write S-E13b's L cells, and mirror
  549 + t held only bytes 0–30 of `r`.
- **Filled** (`h_part`, per signed child σ): 8704 + t the bits of `idx`; 8720 + i the running products
  `R_i = Π_{j<i} f_j` (`f_j = x³·x⁻¹^{d_j}` for `j < 128`, `x⁻¹^{4^t c_t}` for the checksum digits,
  `x = ⟨2, 0⟩`); 8960 + 128t + q the bits of mirror 549 + t's element 1; for an aggregate child
  11008 + 2(k − 1) + h = the final block's `h_out` halves (`T_{j,h}`, zero for `j ≠ k`) and
  11264 + 128(j − 2) + q the bits of main block `aggL j − 1`'s element 7 (2 ≤ j ≤ maxK). **Mirror
  549 + t now holds the whole `r`**: the `r0` family links bytes 0–30 only; W5 compares whole
  elements.
- After: **no row fails on any honest witness**: N8 (two L32, n = 3), N2 over it (k = 2), N4 over it
  (k = 3), N2 over that N2 (k = 1), N4 over that N4 (k = 4): `m_bad 0`, `link_rows_bad 0`. All five
  proofs are accepted by the dumped programs with `stmtOk4`, and every canary is rejected
  (`logs/P2/r41p11/p-*.txt`). Local stream on the new data (VM): N8, N2, N4, N2 accepted, canaries
  rejected (`stream-p.out`).

### 19.6 Final 7763 times (run 40820003716, S-E13a's data, base and new on one runner)

Base = HEAD's `prover.s` (`a3db3bb5…`, S-E12f's matrices); new = this pass's (`5e1bab39…`, S-E13a's).
`req_s` = `go` → `done`; ranges over the new prover's two streams.

| step | kind | chain(s) | base request | **new request** | new: aggregate · witness · node prove |
|---|---|---|---|---|---|
| 1 | N8 | 2^18 + 2^18 | 19.12 | **17.13–17.23** | 10.37–10.42 · 0.67 · 5.94–6.00 |
| 2, 8 | N2 | 2^17 | 7.20–7.38 | **6.13–6.25** | 2.87–2.98 · 0.37–0.38 · 2.77–2.81 |
| 3 | N2 | 2^18 | 9.66 | **8.67–8.70** | 5.38–5.44 · 0.37–0.39 · 2.80–2.81 |
| 4 | N2 | 311,951 | 11.09 | **9.93–9.96** | 6.44–6.51 · 0.52–0.60 · 2.79–2.82 |
| 5 | N2 | 3·2^17 | 12.62 | **11.33–11.35** | 7.96–7.97 · 0.45–0.47 · 2.80–2.82 |
| 6 | N4 | 3·2^18 | 23.86 | **21.69–21.76** | 15.62–15.65 · 0.73 · 5.21–5.23 |
| 7 | N4 | 2^20 | 29.39 | **27.02–27.20** | 20.75–20.90 · 0.90–0.91 · 5.23–5.26 |

- Start-up 0.75–0.78 → **0.59–0.63 s** (node data 0.20 s: the kind tables are larger now; plans
  0.06 s; prefault ≈ 0.3 s). On S-E12f's data it was 0.48 s (run 40817225300).
- `acc` (the native verifier, process start included, `acc_s`): N2 0.45, **N4 0.52–0.53**, N8 0.62 s
  on the new matrices, against 0.40 / 0.48 / 0.57 s for the base on the old ones (+≈ 0.05 s).
- Setup 64.9 s, peak 7.13 GB, 66.8 MB. Request peak RSS 7.01 GB (≤ 11 G).
- 32/32 outputs accepted by `acc`, 32/32 canaries rejected (base and new); the same on the
  off-tier runs (Xeon 8370C 40818830840, EPYC 9V74 40818835937 / 40820012760). Every runner
  rebuilt `prover.s` byte for byte.

**The stream projection** (`logs/P2/r41p11/project.py`; `project-final.txt`). It uses pass 10's
model, with the node parts taken as request − aggregate fit, so they include slot 0's cost to the
aggregate:

| | base (same runner) | **new** |
|---|---|---|
| node parts N2 / N4 / N8 | 4.62 / 8.07 / 8.54 s | **3.49 / 5.94 / 6.62 s** |
| start-up · overhead per step | 0.77 · 2.15 s | **0.61 · 1.99 s** |
| steps 2^17 / 2^18 / 1.19·2^18 / 2^20 | 7.25 / 9.90 / 11.05 / 29.19 s | **6.12 / 8.77 / 9.93 / 27.06 s** |
| mean step + overhead | 12.06 + 2.15 = 14.22 s | **10.80 + 1.99 = 12.78 s** |
| stream fits | M ≤ 67 | **M ≤ 74** |
| evaluations truncated (simulated) | 81.3 % | **52.5 %** |
| P̄ | 10.75 s | **9.53 s** |

The same prover on S-E12f's data (run 40817225300) gave M ≤ 76 and 46.1 %. S-E13a's matrices cost
≈ 0.13 s of start-up and ≈ 0.13 s of node prove per step.

### 19.7 Checks and `prover.s`

- `cargo test --release`: **46 passed, 1 ignored** (`cargo-test-4.txt`). New tests:
  `trace_blocks_matches_ref`, `round1_zero_windows_skipped_equal`, `plans_round_trip`.
- Source rule (`logs/org20`): 357 files, 0 findings.
- **`prover.s` 17,441,648 B, sha256 `5e1bab39fa16dbb432df0019b1f1bac4bd47ea09dc94af353174599e54c961bc`**
  (`build-asm.log`). The 4 final runners rebuilt it byte for byte.

### 19.8 Deviations, findings, open questions

1. **`prover setup` now does work**: 65 s on the 7763 out of 240 s, 66.8 MB out of 4 GiB, peak
   7.13 GB. With no setup, or a setup from other node data (tag mismatch), the prover solves as in
   pass 10.
2. **Replays are a guess that is checked.** Every fill checks every row. A replay that falls short
   is completed by the worklist, and π is unchanged (the closure argument, §19.3; KATs with both
   paths).
3. **Slot 0 beside the aggregate costs the aggregate up to 0.36 s** (at 2^17), and lowering its
   priority does not help. It is still ≈ 0.1 s better per step than running it inside the witness.
4. **S-E13a/S-E13b**: the honest witnesses fail no row once S-E13b's cells are written and mirror
   549 + t holds the whole `r`. Before that, the failing rows were exactly S-E13b's WOTS rows. The
   pack rows held without any change. **For S-C (the `r31` proposal, S-E13b §2.2):** the prover now
   writes `r`'s byte 31 at source 549 + t, so `mbo = 248` on that source is already consistent with
   the witness.
5. The node blob grew to 7.4 MB (raw 27.1 MB) because the kind tables carry the link rows as text.
   A binary form, or the link rows generated from their families, would win back ≈ 0.1 s of start-up.

### 19.9 Handover: what remains, in order of seconds per step

1. **The aggregate's segments** are now ≈ 64 % of a mean step (≈ 6.9 of 10.8 s). Round 1
   (≈ 1.25 s per 2^18) is the largest kernel. A bit-sliced round 1 was costed here and does not pay:
   the LDE alone costs more bit-sliced (≈ 15 k ops per window) than the byte tables (11 k). What is
   left is P2″'s tower-field products (−10 %) and the conversion (−20 % of its part).
2. **The node prove** (N2 2.8 s, N4 5.2 s): commit, Z and Ligerito are still most of it. The zero
   third of the witness could also be skipped in Ligerito's level-0 folds and messages, and in Sh's
   `collapse_n` (0.12 s of Sh's 0.21 s on N2). E2's sumcheck over the M rows' support is worth
   ≈ 0.07 s on N4 only.
3. **Slot 0's interference with the aggregate** (+0.05…+0.36 s), and its own cost: `run_p0` ≈ 0.3 s,
   replay 0.12 s, check 0.07 s. The check could run in parallel over rows.
4. **Start-up 0.6 s**: node data 0.2 s (parse 85 %; a parsed binary image in `/setup`, read at
   start-up, would cut most of it), prefault ≈ 0.3 s (zeroing, inherent; it only moves time out of
   P).
5. A partial L32 replays the 200,003-step order 65 entries short and is completed by the worklist
   (≈ 0.15 s on the 7763, in parallel). Orders per `n` class near the segment end would remove this.

## 20. Pass 12 (track P2⁸): the segments' round 1, shift reductions, the node's zero skips

Status: 2026-10-29. Logs: `logs/P2/r41p12/` (VM) and the runner runs `logs/P2/run-<id>/`. Every probe
ran the base (HEAD's committed `prover.s`, `5e1bab39…`) and the new prover on the same runner, through
`probe/p2t12/` (branches `probe/p2t-12a … 12m`, temporary-index commits on HEAD, all deleted). **The
final run is `40828606971` (EPYC 7763)**; `40828619224` (Xeon 8573C) and `40828630557` (EPYC 9V45) are
off-tier acceptance. **π is byte-identical** to HEAD's prover on every KAT (§20.5).

### 20.1 What was built (crate 16,258 `.rs` lines, was 15,026)

| file | change (the reference each change keeps) |
|---|---|
| `simd.rs` | **`r1::window_t`**: the round-1 window in a tower form (`r1::tower`: GF(2^8) = GF(16)[w]/(w² + w + λ); LDE table in tower bytes; a product = three GF(16) products by `vpshufb` logs, the `ζ^k` weight folded into the exp tables, no Horner step; the LDE's permutations grouped, 6 shuffles instead of 14) (pass 11's `r1::window`, `zerocheck::window_portable`); **`r1::convert_t`**: the conversion by 4-bit `vpshufb` tables (16 KiB, L1), byte planes and a 16×16 byte transpose, `z` rows even/odd (`bit_transpose_eo`) (`r1::convert`); **`mac_u`** (unreduced `eq` accumulation; `mac_u_ref`, `axpy`); **`mul`** with the reductions by shifts (`mul_cl`); **`butterfly`** with the reduction by shifts, chosen on Zen 3 (`bfly_shift`, `FLOCK_BFLY`) (`butterfly_cl`); the AVX2 window on every AVX2 CPU (`r1_avx2`); selftest checks for both butterflies, `axpy_cl`, `mac_u`, pass 11's window; test `pass12_tests::tower_window_matches` |
| `zerocheck.rs` | `round1` = tower window + `mac_u`; `round1_ref` = pass 11's; test `round1_matches_ref` |
| `nodeprove.rs` | Sh: **`collapse_keys`** (one pass for every key, zero key ranges skipped; `collapse_n`); E2 `zc_abc`: zero `c` stretches skipped, **`fold_f_sparse`** for E2 and the Z tail (`fold_f`); tests `collapse_keys_matches`, `fold_sparse_matches` |
| `ligerito.rs` | level 0: round 1 skips zero 4,096-pair ranges of `g`; `fold_msg` writes zeros for a zero block of `g` and skips its message part |
| `sumcheck.rs` | `fold_f_sparse` |
| `mfill.rs` | a short replay's completion: **`worklist_unknown`** (the worklist from the rows touching an unknown cell) and the second check over the failed rows and the rows touching a newly solved cell only (`FLOCK_FULL_RECHECK=1`: `worklist_with` and the full check) |
| `plan.rs` | **`save_image`/`load_image`**: the decoded node data as a flat image (`nodedata.bin`, tagged by the blob's hash; the blob format unchanged; `decode_blob` the fallback); `data_tag` once; test `image_round_trip` |
| `stream.rs` | `prover setup` writes `nodedata.bin` |
| `bench.rs`, `main.rs` | modes `bench-r1 [m]` (window kernels and parts, round 1 new vs ref), `bench-k` (butterflies, products), `bench-nd` (blob vs image) |
| `prover.s` | regenerated (§20.6) |
| `probe/p2t12/` | `run.sh` (pass 11's, plus benches, **the KATs on the runner** with both binaries, pass 6's segment-fit cases, `RF_SETUP` for the base too), `stream.sh` (`pi_sha`), `kat/` (pass 11's signed N8/N2/N4 on S-E13a's data, 3 × 2.3 MB) |

### 20.2 Round 1 (item 1; 7763, `bench-r1`, one thread, equal to the references)

| kernel (µs per window) | pass 11 | pass 12 |
|---|---:|---:|
| window (LDE, products, z transposes, conversion) | 4.28–4.58 | **2.30–2.40** |
| rows (LDE + products + transposes) | — (not timed alone) | 1.66–1.79 |
| conversion | 1.38–1.47 | **0.61–0.62** |
| `eq` accumulation (`axpy` → `mac_u`) | 0.64–0.67 | **0.27–0.28** |
| **round 1 over 2^32 bits (4 threads, s)** | 1.17–1.32 | **0.68–0.70** |

In the proof (run 40828606971, step 3): the L32 segment's zc_round1 1.21 → 0.76 s, the N2 node's 0.41 → 0.26 s.

### 20.3 Shift reductions (`bench-k`, ns per item, one thread)

| | butterfly: carry-less → shifts | F product (`axpy`): carry-less → shifts |
|---|---|---|
| EPYC 7763 | 1.745 → **1.63** | 3.32 → **2.92–2.98** |
| EPYC 9V45 | 1.127 → 1.09–1.27 | 2.38 → 2.16 |
| Xeon 8573C | 1.17–1.20 → 1.29 (worse) | 2.82 → 2.80 |

`mul` takes the shift form everywhere; the butterfly only on Zen 3. Over the final 7763 streams' 8
steps: Ligerito level-0 folds −14 %, tail rounds and folds −11 %, NTT passes −5 % and blocks −8 %;
`x6.fold` **+4 %** (its table loads compete with the shifts; §20.8).

### 20.4 The node (items 2–6) and start-up

- **Zero skips** (N2 node, step 3, phase times): Sh (`shift`) 0.26 → 0.17 s (`collapse_keys`),
  Ligerito 0.37 → 0.30, E2 0.148 → 0.136, Z tail 0.33 → 0.31.
- **A short replay** (a partial child whose setup order was recorded at another `n`, e.g. L30 at
  n = 49,807: 1,976 entries short): the completion and the second check now touch only the rows
  that can change. Witness on step 4 (311,951 = L32 + L30): 0.59–0.61 → 0.47–0.52 s. Per-`n`-class
  orders (§19.9 item 5) are no longer needed.
- **Start-up** 0.54–0.59 → **0.47–0.51 s** (the image: 7763 `bench-nd` 0.147–0.173 → 0.070–0.083 s).
- Slot 0 (item 4): unchanged beyond the completion. A parallel row check does not cut CPU, and slot 0
  shares the cores with the aggregate.

### 20.5 Checks

- **KATs, base (HEAD) = new**: on the VM (portable products, AVX2 window) and on three runners (ymm
  path): N8 `d8b25c6a…`, N2 `515f21b3…`, N4 `c5d6ae84…`, N2 k = 1 `816a1f84…`, N4 k = 4 `a3c6e71b…`
  (pass 11's `p-*.txt` on S-E13a's data), `test-leaf` 28 `62f91a4b…`, 30 `02997486…`, 32
  `559306ee…`, 31 `--n 77777` `aac62938…`, and the 11 fit cases' π. The short-replay case (N2 over
  311,951, VM): `db9942b1…` with the setup, with `FLOCK_FULL_RECHECK=1`, without the setup, and HEAD's
  base with the setup. **The brief's KATs** (`9368bcae…`, `f60dc083…`, `a16ab6a3…`) are S-E12f-era
  (pass 10's N8): since pass 11's data change HEAD no longer reproduces them, so they cannot be the
  reference.
- `cargo test --release`: **51 passed, 1 ignored** (`cargo-test-2.txt`). Source rule (`logs/org20`):
  359 files, 0 findings.
- Streams: **32/32 outputs accepted by `acc`, 32/32 canaries rejected** on each of the three final
  runners, base and new.

### 20.6 `prover.s`

**18,042,211 B, sha256 `f08413937517e2adc1ddfa723881e44caa02cc6a6e62fcc2c161d08ece7e0187`**
(`logs/P2/r41p12/build-asm.log`). All three final runners rebuilt it byte for byte; selftest
`tier=ymm checked=[pclmul,ymm,ymm-sim]`, `bfly=sh` on the 7763, `cl` on the Xeon and the 9V45.

### 20.7 Final 7763 times (run 40828606971, base and new on one runner, both with `RF_SETUP`)

| step | kind | chain(s) | base request | **new request** | new: aggregate · witness · node prove |
|---|---|---|---|---|---|
| 1 | N8 | 2^18 + 2^18 | 16.87–16.92 | **15.20–15.24** | 9.17–9.25 · 0.68–0.74 · 5.16–5.18 |
| 2, 8 | N2 | 2^17 | 6.06–6.28 | **5.48–5.55** | 2.58–2.66 · 0.40–0.41 · 2.39–2.41 |
| 3 | N2 | 2^18 | 8.49–8.51 | **7.66–7.76** | 4.79–4.83 · 0.39–0.41 · 2.38–2.42 |
| 4 | N2 | 311,951 | 9.82–9.84 | **8.73–8.80** | 5.73–5.77 · 0.47–0.52 · 2.41–2.42 |
| 5 | N2 | 3·2^17 | 11.22–11.30 | **10.10–10.13** | 7.11 · 0.48–0.51 · 2.41–2.42 |
| 6 | N4 | 3·2^18 | 21.43–21.58 | **19.10–19.14** | 13.76–13.85 · 0.69 · 4.46–4.51 |
| 7 | N4 | 2^20 | 26.88–26.91 | **23.99–24.02** | 18.42–18.43 · 0.93–0.96 · 4.49–4.50 |

- **Segment fits** (prove-leaf through rf-oracle, prove + trace + SIGN, `fit-final.txt`): L32
  2.476 + 2.720·n/2^18 → **2.149 + 2.415**, L31 1.239 + 1.350·n/2^17 → **1.072 + 1.203**, L30
  0.654 + 0.602·n/2^16 → **0.567 + 0.531** s.
- Setup 59.2 s, peak 7.12 GB, **365 MB** (the image 298 MB; was 66.8 MB). Request peak RSS 7.10 GB.
- The native `acc` (the prover binary's verifier, not the scored one) also fell: N2 0.43–0.45 →
  0.39–0.40, N4 0.52 → 0.48, N8 0.62 → 0.57 s.

**The stream projection** (`logs/P2/r41p12/project.py` = pass 11's, with each prover's own fits by
`--seg`; `project-final.txt`):

| | base (same runner) | **new** |
|---|---|---|
| node parts N2 / N4 / N8 | 3.49 / 6.01 / 6.50 s | **3.23 / 5.59 / 6.09 s** |
| start-up · overhead per step | 0.565 · 1.95 s | **0.487 · 1.87 s** |
| steps 2^17 / 2^18 / 1.19·2^18 / 2^20 | 6.08 / 8.68 / 9.80 / 26.80 s | **5.50 / 7.79 / 8.76 / 23.84 s** |
| mean step + overhead | 10.67 + 1.95 = 12.61 s | **9.54 + 1.87 = 11.41 s** |
| stream fits | M ≤ 75 | **M ≤ 83** |
| evaluations truncated (simulated) | 49.1 % | **30.4 %** |
| P̄ | 9.41 s | **8.43 s** |

The base here is better than §19.6's (M ≤ 74, 52.5 %) because this probe gives HEAD's base the setup
too (pass 11's probe did not). Off-tier, same code: Xeon 8573C M ≤ 83 → 90 (30.6 → 19.3 %), EPYC
9V45 M ≤ 121 → 132.

### 20.8 Deviations, findings, open questions

1. **The brief's KAT hashes are stale** (§20.5); the references are pass 11's S-E13a-era KATs and
   HEAD's binary on the same inputs.
2. **Stream proofs are not byte-deterministic** between two runs of one binary (`pi_sha` differs base
   vs base), so π identity rests on the KATs (now also run on the runners, where the ymm kernels
   run).
3. **`/setup` grows to 365 MB** (the node data image). Without it, or with a foreign tag, the blob is
   decoded as before.
4. **The butterfly's reduction is chosen by CPU** (Zen 3: shifts). The result is the same either way.
5. Pass 11's probe gave the base streams no `RF_SETUP`; pass 12's base figures include it.
6. `probe/p2t12/kat/` holds 6.9 MB of signed nodes (probe inputs); the orchestrator may drop them (the
   KAT section then reports empty π and `DIFFER`).

### 20.9 Handover: what remains, in order of seconds per step

1. **The segments** are still ≈ 60 % of a step. Per L32 at 2^18 (step 3): commit 1.15 (NTT ≈ 0.6, the
   service's leaf hashes ≈ 0.36), round 1 0.76 (`rows_t` ≈ 1.7 µs a window: 32 table loads and
   ≈ 130 vector ops a row, no SMT gain), Ligerito 0.68, x₆ 0.59, witness 0.58, ring switch 0.31, tail
   0.22, lincheck 0.20. `x6_fold` should go back to `mul_cl` (+4 % with the shift product; ≈ 0.015 s
   per step).
2. **The node prove** (N2 2.4 s, N4 4.5 s): commit 0.51, E4 0.38, Z tail 0.31, Ligerito 0.30, Z
   round 1 0.26, ring switch 0.23, Sh 0.17.
3. **The node data in memory**: 5.3 M nonzeros per prototype carry 16-byte coefficients with only 513
   distinct values. `u16` indices into a table would cut the image (298 MB) and start-up further, and
   the memory traffic of `fill.check`, `m_matvec` and `m_scatter`.
4. **The node witness's critical path** is slot 1's sequential replay (0.25 s for 436,594 entries);
   slot 0's fill (run_p0 ≈ 0.3–0.46 s, replay, check) still runs beside the aggregate.

## 21. Pass 13 (track P2⁹): determinism, the node's fills, indexed coefficients

Status: 2026-10-29. Logs: `logs/P2/r41p13/` (VM) and the runner runs `logs/P2/run-<id>/`. Every probe
ran the base (HEAD's committed `prover.s`, `f0841393…`, with its own `prover setup`) and the new
prover on the same runner, through `probe/p2t13/` (branches `probe/p2t-13a … 13e`, temporary-index
commits on HEAD, all deleted). **The final runs are `40838740210` (record), `40838753998` and
`40838766566`, all EPYC 7763.** **π is byte-identical** to HEAD's prover on every KAT (§21.5).

### 21.1 Determinism (item 1)

- **The prover is deterministic given the oracle.** Two streams against a service built with the
  feature `insecure-test-keys` and the same fixed keys give byte-identical `proof.bin` files at every
  step (N8, N2, N4): on the VM (portable products), on the 9V74 and on four 7763 runs (ymm path, 4
  threads, the parallel replay), all with the same hashes (`d204d5df…`, `d416c365…`, `ddac2ea2…`;
  `det.txt`).
- **The cause of pass 12's difference** (§20.8 item 2) is the service: `rf-oracle` draws a fresh PRF
  key and signing seed from `getrandom` at every start (`service/src/main.rs`). Every Fiat–Shamir
  challenge, Merkle hash and signature depends on them. Nothing in the prover is nondeterministic:
  no hash-map iteration order, no uninitialised read and no reduction order affects an output.
  Parallel sums are XOR sums, and the new parallel replay is level-scheduled (§21.3).
- **The rules do not ask for determinism.** `PROVER.md` §3 and `harness/rfh/bench.py` `retime`
  re-run a slow step as a fresh process on the same inputs, under the same service lifetime. The
  re-run's output must be accepted. The faster run's `P`, `V` and `|π|` are scored, and the first
  output stays the next step's child. Nothing compares bytes, and identical bytes are impossible
  anyway: a re-run's signatures take later one-time keys, and a node's π commits to the signatures
  of the leaf children it signs during the step.
- **Every variant verifies.** `stream.sh` `P2T13_RERUN=1` (det-3) re-runs every step under the same
  lifetime, as `retime` does. Every re-run's π differs from the first, every re-run is accepted by
  `acc` against the step's statement, and every canary of a re-run is rejected, on all five runners.

### 21.2 What was built (crate 16,883 `.rs` lines, was 16,258)

| file | change (the reference each change keeps) |
|---|---|
| `mfill.rs` | `Rows`: **coefficients as `u16` indices** into `cv` (`cv[0] = 1`), `term`/`intern`/`done`, `cmul`, `coef_values` (the 16-byte form), `cvinv`; `Proto::fcinv`; **`ByCell`** (terms by cell); **`Sched`/`schedule`/`replay_levels`** (the replay by levels; `FLOCK_SEQ_REPLAY=1` the sequential one), `try_row_p` (`try_row` on pointers, `want`); the **row check in parallel**; `save_scheds`/`load_scheds` (`sched.bin`); tests `schedules_levels_and_round_trip` |
| `plan.rs` | `read_planform` interns the coefficients (table once, products per pair); image **`FLNDIMG2`** (indices + table; version 1 refused, the blob the fallback); `proto_eq` by values |
| `nodeprove.rs` | **`m_scatter` as a gather by cell** (`m_scatter_ref` = pass 12's, `FLOCK_SCATTER_REF=1`); `m_matvec` sums the coefficient-1 terms apart; test `scatter_gather_and_matvec_match` (N2, N4, node data) |
| `nodeops.rs` | `eval_m`/`eval_m_ref` read the indexed coefficients |
| `node.rs` | `warm_plans`: the per-prototype tables and the schedules as separate jobs over all threads |
| `stream.rs` | `prover setup` writes `sched.bin`; a request loads it with the plans |
| `field.rs` | `B64::inv` by an addition chain (`inv_ref`); test `inv_chain_matches_ref` |
| `ntt.rs` | `encode`: the replication **fused into the first radix-4 pass** (`first_pass_from`; `FLOCK_NTT_COPY=1` the reference) |
| `simd.rs` | `x6_fold`'s ymm kernel with **`mul_cl`** |
| `bench.rs` | `bench-nd` prints the coefficient-1 share and the table size |
| `prover.s` | regenerated (§21.6) |
| `probe/p2t13/` | `run.sh` (pass 12's, plus the short-replay KAT, the base's own setup, `P2T13_DET`: the fixed-key service and streams det-1/2/3), `stream.sh` (`RF_ORACLE_ARGS`, `P2T13_RERUN`, `file_sha`) |

### 21.3 The node's fills (item 4) and the coefficients (item 3)

- **Indexed coefficients**: the node data's 5.3 M nonzeros per prototype take 2 bytes each, not 16
  (513 distinct values). The image is 298 → **150 MB**, and `/setup` 365 → **230 MB** (with
  `sched.bin`, 12.8 MB).
- **The replay by levels.** A recorded order (≈ 440 k entries) has 15,872 levels. The 17 levels of
  at least 4,096 entries hold 72 % of the entries and run in parallel; the rest run on the calling
  thread. Each entry sees exactly the cells it saw in the sequential replay. An entry that would
  solve a cell other than its own is a miss and is retried in order (the short-replay case: 21,876
  misses, the same 1,976 unsolved cells and the same π).
- **7763 (run 40838740210, both ranges over 2 streams):**
  - node witness:

    | node | base (s) | new (s) |
    |---|---|---|
    | N2 | 0.39–0.40 | **0.27–0.28** |
    | N2 over 1.19·2^18 | 0.49–0.52 | 0.35 |
    | N4 | 0.74 / 0.93 | **0.55 / 0.64** |
    | N8 | 0.68–0.69 | 0.58 |

  - node prove N2: 2.40 → 2.30–2.34 s;
  - step 3's spans:
    - `fill.solve` 0.495 → 0.332 and `fill.check` 0.195 → 0.184 (slot 0 runs beside the aggregate);
    - `ne4.scatter` 0.141 → 0.118.
- The inverse caches (`cvinv`, `fcinv`, the addition chain) changed nothing measurable (the VM's
  sequential replay: 0.45 s either way; inversions are rare). They are kept, with references.

### 21.4 Segments (items 2, 5)

- NTT (step 3): `ntt.copy` + `ntt.passes` 0.105 + 0.517 → `ntt.first` + `ntt.passes` 0.174 + 0.392 s.
- `x6.fold` 0.263 → 0.229 s (`mul_cl`).
- **Tried and reverted**: the x₆ fold by two scaled tables (no product per entry). On the 7763,
  2^22 pairs took 0.0145 → 0.0172 s, because two 32 KiB tables do not fit L1 together.
- Fits (prove-leaf + trace + SIGN), base → new:

  | segment | base | new |
  |---|---|---|
  | L32 | 2.151 + 2.434·n/2^18 | 2.112 + 2.448 |
  | L31 | 1.083 + 1.210·n/2^17 | 1.068 + 1.216 |
  | L30 | 0.580 + 0.541·n/2^16 | 0.577 + 0.520 |

  The aggregate is still ≈ 63 % of a step at 2^18 (4.69 of 7.40 s).

### 21.5 Checks

- **KATs, base (HEAD) = new.** They ran on the VM (versions a, b, c and e, with and without the
  setup) and on all five runners (9/9). The values:
  - N8 `d8b25c6a…`, N2 `515f21b3…`, N4 `c5d6ae84…`;
  - N2 k = 1 `816a1f84…`, N4 k = 4 `a3c6e71b…`;
  - the short replay, N2 over 311,951: `db9942b1…`;
  - `test-leaf` 28 `62f91a4b…`, 30 `02997486…`, 32 `559306ee…`, 31 `--n 77777` `aac62938…`.

  The 11 fit cases' π are also base = new.
- `cargo test --release`: **54 passed, 1 ignored** (`cargo-test-2.txt`).
- Source rule (`logs/org20`): 364 files, 0 findings.
- **44/44 outputs accepted and 44/44 canaries rejected** on each final runner: the 32 stream
  outputs, det-1 and det-2, and det-3's outputs and re-runs.

### 21.6 `prover.s`

On S-E13a's data: **18,366,894 B, sha256 `7c8704443aca72d25d2bff00b75e7383173eba659653e9c5d567b9ec696c471f`**
(`logs/P2/r41p13/build-asm-e.log`). **The final `prover.s`, with B0's blob (§21.10): 18,408,878 B, sha256
`1b84a5f1cbc19be63082ade61ef89fb00a649fc4b7a45ff210a0db7fc74ed47f`** (`build-asm-f.log`), rebuilt
byte for byte on runs 40845544755 (7763) and 40845523456 (9V45). All three final runners rebuilt it byte for byte. The selftest
gave `tier=ymm checked=[pclmul,ymm,ymm-sim]`, `bfly=sh`.

### 21.7 Final 7763 times (run 40838740210, base and new on one runner, each with its own setup)

| step | kind | chain(s) | base request | **new request** | new: aggregate · witness · node prove |
|---|---|---|---|---|---|
| 1 | N8 | 2^18 + 2^18 | 15.19–15.25 | **14.78–14.83** | 9.03–9.05 · 0.58 · 5.03–5.06 |
| 2, 8 | N2 | 2^17 | 5.46–5.60 | **5.14–5.31** | 2.49–2.61 · 0.28 · 2.26–2.34 |
| 3 | N2 | 2^18 | 7.71–7.76 | **7.38–7.41** | 4.68–4.70 · 0.27–0.28 · 2.32–2.33 |
| 4 | N2 | 311,951 | 8.73–8.76 | **8.41–8.46** | 5.62–5.67 · 0.35 · 2.33–2.34 |
| 5 | N2 | 3·2^17 | 10.08–10.14 | **9.74–9.78** | 6.95–6.98 · 0.35 · 2.35 |
| 6 | N4 | 3·2^18 | 19.17–19.23 | **18.65–18.75** | 13.65–13.66 · 0.55 · 4.32–4.41 |
| 7 | N4 | 2^20 | 24.05–24.07 | **23.33–23.38** | 18.19–18.26 · 0.64 · 4.34–4.36 |

**The stream projection** (`logs/P2/r41p13/project.py` = pass 12's, each prover with its own fits by
`--seg`; `project-final.txt` holds all three runs):

| | base (same runner) | **new** |
|---|---|---|
| node parts N2 / N4 / N8 | 3.21 / 5.58 / 6.05 s | **2.91 / 5.07 / 5.68 s** |
| start-up · overhead per step | 0.489 · 1.87 s | 0.530 · 1.91 s |
| steps 2^17 / 2^18 / 1.19·2^18 / 2^20 | 5.50 / 7.79 / 8.78 / 23.92 s | **5.19 / 7.47 / 8.44 / 23.31 s** |
| mean step + overhead | 9.55 + 1.87 = 11.42 s | **9.19 + 1.91 = 11.10 s** |
| stream fits | M ≤ 83 | **M ≤ 86** |
| evaluations truncated (simulated) | 30.6 % | **26.5 %** |
| P̄ | 8.44 s | **8.09 s** |

The other two final runs give mean step + overhead 11.49 → 11.21 s (M ≤ 83 → 85, truncated 31.5 →
27.9 %) and 11.52 → 11.23 s (M ≤ 82 → 84, 31.9 → 28.1 %). Setup: 56 s, 230 MB.

### 21.8 Deviations, findings, open questions

1. **Nondeterminism is the service's fresh keys, not the prover** (§21.1). Byte identity of stream
   outputs cannot be a check. The KATs and the fixed-key streams carry π identity.
2. **Start-up rose by 0.04 s**: `pre.warm_plans` went 0.028 → 0.071 s (`ByCell`, `fcinv`); the
   schedules come from `/setup`. Start-up is untimed, but it does count in `stream_s`. `ByCell`
   could move into the image, and `fcinv` could skip the hash for coefficient 1.
3. `/setup` adds `sched.bin`, and the image is now `FLNDIMG2`. An older `/setup` still works: its
   image is refused and the blob is decoded, and without `sched.bin` the schedules are built at
   start-up. The blob format is unchanged.
4. `load_scheds` checks the shape of a schedule (its lengths, monotone levels, a permutation), not
   its level property. Like the plans, the file is the entry's own setup output, tagged by the node
   data. The row check after the replay decides the values in every case.
5. A2′'s CapChk field and E1's port were not started; the node data's format is untouched beyond the
   in-memory encoding.

### 21.9 Handover: what remains, in order of seconds per step

1. **The segments** (≈ 63 % of a 2^18 step). Per L32 at 2^18:
   - commit ≈ 1.06 s, of which NTT ≈ 0.57 and the service's leaf hashes ≈ 0.36;
   - round 1 0.76;
   - Ligerito 0.68 (level-0 folds);
   - x₆ 0.56;
   - witness 0.58;
   - ring switch 0.31.

   The ring switch's weight table (0.31 s segment, 0.22 s node) is 48 row reads per output element
   over 3–4 claims.
2. **The node prove** (N2 2.3 s, N4 4.35 s): commit 0.43, E4 0.29, Z tail 0.27, Ligerito 0.25,
   Z round 1 0.23, ring switch 0.18, Sh 0.14.
3. **Start-up** (§21.8 item 2).
4. **Slot 1's fill** (now 0.17 s on the 9V74): the 15,855 small levels (28 % of the entries) run
   sequentially. Its check could be skipped for rows the replay itself solved.

### 21.10 Added item: B0's row layout (the orchestrator's request)

- **Re-embedded.** `nodeblob.b64` is rebuilt from `logs/B0/nodedump`: 7,439,340 B, sha256
  `6ae3e6d8…`. `find_dirs` now defaults to that directory.
- **The plan-form KAT passes** (`plan-kat`). `proto_eq` holds for p0 (580,620 rows) and p1 (573,389
  rows), and the programs are equal. The prover needed no change: B0's split halves are ordinary
  keys of the unchanged plan-form format.
- **The node KATs' π change, because the matrices' rows move.** The new signed KAT nodes are in
  `probe/p2t13/kat/` (local), each accepted by its kind's dumped program. The new references are:
  - N8 `0277148e…`, N2 `b7ab5cb7…`, N4 `87865636…`;
  - N2 k = 1 `2571a475…`, N4 k = 4 `06a1664c…`;
  - the short replay, N2 over 311,951: `edbd211a…`.

  The new code gives the same π as every reference path, with and without the setup. The leaf KATs
  are unchanged. The runners reproduce the VM's values (`kat-expected.txt`).
- **The Lean V built with B0's modules accepts the prover's outputs.**
  - The V is the harness's badge `verify`, rendered around `Solution` in `logs/fr-build-P2t13`, a
    copy of B0's tree. Its B0 modules equal the worktree's live files; only 13 FRX modules differ,
    G3's in-progress golf. The binary is also saved as `logs/P2/r41p13/verify-B0`.
  - The outputs were made on the runners (7763 run 40845544755, 9V45 run 40845523456) and checked
    by this `verify`. Each run kept 17 outputs: fixed-key N8, N2 and N4 with their re-runs, and a
    random-key stream of 8 steps. **17/17 were accepted and 17/17 canaries rejected.**
  - On the VM: 6/6 accepted, 6/6 canaries rejected.
  - Control: the pre-B0 prover's outputs are rejected by this V (2/2), so the check depends on the
    row layout.
  - The Lean V was built on the VM, not on the runners (a runner has no Lean build of the entry); the
    outputs it checked came from the runners.
- **Node prove time does not change measurably.** On the 7763, pass 13's code on S-E13a's layout
  vs on B0's, same runner:

  | node | S-E13a's layout (s) | B0's (s) |
  |---|---|---|
  | N2 | 2.32–2.39 | 2.31–2.43 |
  | N4 | 4.36–4.43 | 4.33–4.37 |
  | N8 | 5.11–5.12 | 5.05–5.08 |

  E2 and E4 are 2–6 % lower. The projection is 11.21 → 11.16 s (M ≤ 85 both). The node's matrices
  keep their 2^20-row slots; only about 4 % fewer rows carry terms.
- Checks: `cargo test --release` 54 passed, 1 ignored. Source rule: 371 files, 0 findings. 44/44
  outputs accepted and 44/44 canaries rejected per runner.
