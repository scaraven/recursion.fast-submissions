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
