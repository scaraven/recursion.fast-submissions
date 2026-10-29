# P2 journal (track P: modes, prover.s, throughput)

## 2026-10-27

- P1 accepted (081ae9b). Rev. 3.1 (c38bda1) adopts P1-D1…D7 (two-level pinned point, `one` and
  constants as a public target E, lincheck 14 rounds, shift + 10 collapse rounds, batching inside
  ring switching, final = level-4 fold with final rounds); P1-D8 (π order) is not adopted: A.3
  grouped order, A.4 item sequence with dummies, piSize = 756,496.
- `alloc.rs`: a global allocator whose large blocks (≥ 8 MiB) are never returned to the kernel,
  best fit with splitting and merging; `prefault(bytes)` maps and touches one block before the
  timed part (K's pre-faulted arena, as an allocator). `leaf` mode pre-faults 1,800 MiB before
  `ready`; the bench modes take `FLOCK_PREFAULT_MIB`.
- K-fold by a constant with two F products (`c₀ = S₀D₀ + (αS₁)D₁`, `c₁ = S₁D₀ + (S₀+S₁)D₁`)
  instead of three.
- Modes: `setup` (nothing to set up), `leaf` (PROVER.md §3 handshake: vk.hex, ready, go,
  leaf.json, proof.bin, done), `vk`; `tree`/`node` exit 2 until the node prover exists.
- `build-asm.sh` (spartan-srom's recipe): `prover.s` 5.7 MB; through `asm-compat.py` unchanged;
  links with `gcc -static -O2 -pthread *.s -o prover -lm`. On the runner (binutils 2.42, run
  40517053502) it assembles and links; every P2 measurement uses that linked binary.
- `probe/p2-prover/request.py`: a runner-like leaf request (fresh process, ready/go/done, native
  acc + canary).
- Node-shape surrogate (`FLOCK_NODE_SHAPE=1`): the m = 30 proof plus timing-only E1 (degree-3
  zerocheck over 2^20 rows), Lr (2^15) and E2 (degree-2 sumcheck over the packed polynomial).
- Run 40517053502 (p2-1) landed on an EPYC 9V45: leaf request 1.00–1.03 s, m = 30 with node
  surrogate 1.08–1.12 s, m = 32 3.79–3.82 s, peak RSS 1.89 / 6.19 GB (pre-faulted).
- Ring-switch partials of claims (b), (c) now come from the lincheck's and the shift's partial
  folds (`s_v = Σ_{y_in} eq(hi_in, y_in) Z(128 y_in + v)`, 2^14 products) instead of a pass over
  the witness (debug-asserted equal to `ringswitch::partials`).
- Runs p2-2 … p2-11 landed on 9V74, 8370C, 8573C, 9V45, 6973P-C and twice on the 7763 (p2-6
  40518491376, p2-8 40518500999). 7763 there: leaf request 1.55–1.63 s, m = 30 + node surrogate
  1.71–1.78 s, m = 32 6.53–6.68 s; the witness was the largest phase (0.28 s at m = 30, 1.49 s at
  m = 32).
- Uninitialised fold outputs (`par::uninit_vec`) in the sumcheck, x₆ and Ligerito folds.
- `block_fast` measured 7.3 µs per block (a chain step is 0.43 µs): the gate emission went
  through `&mut self` fields (u128 RMW per gate group, store-to-load stalls). Rewritten with the
  three bit streams in locals and the G function as macros: 1.42 µs per block; still equal to the
  tape (unit test). 8573C m = 30 witness 0.06 s, m = 32 0.24–0.26 s (runs 40519260535, -67010).
- Trace recording: the prover's batch queries above 128 bytes (the Merkle column queries) are no
  longer fingerprinted; the replay asks the ≈ 750 opened columns again through the service.
- p2-12 … p2-15 (trace recording change): EPYC 7763 ×2 (40519554882, 40519561565): leaf request
  1.36–1.43 s, m = 30 + node surrogate 1.49–1.57 s, m = 32 5.47–5.59 s. Link ≈ 2.92 s (target
  2.8), tree ≈ 450 s (target 500). Branches p2-1 … p2-15 deleted.
- Rev. 3.2 (2709159) relayed: node 54,111 blocks, M ≈ 2^19.96 (the surrogate's 2^20 matches);
  Sel·eq at degree 3, 3 hashStmt blocks per slot, J_z = 4 in acc: node-side, not yet built.
- Orchestrator: the committed `prover.s` is the submission (regenerate with every source change);
  the child-file parsing counts in a node request.
- Sel prototype (`FLOCK_USED_BLOCKS`, timing only) and the E2-batched surrogate
  (`FLOCK_E2_BATCHED`). 7763 (40520772546, -81943, -88939): leaf request 1.34–1.41 s; node with
  Sel 1.40–1.46 s; with Sel + E2 batched 1.26–1.32 s; m = 32 5.47–5.53 s. E2 alone 0.14 s
  (0.008 s batched). Link ≈ 2.80 s (Sel), ≈ 2.66 s (Sel + E2 batched, a proposal for review).
- S-E1-M2: the leaf chain block's constants are zero rows with their bits in E
  (`circuit::e_positions`); `skip_eval`'s `P^e` sums over E. Tests and `test-leaf` pass (VM
  portable, qemu ymm-sim). `prover.s` regenerated: sha256 4588296d…, rustc 1.99.0.
- Stopped at the orchestrator's request (fewer agents/tokens). All probe/p2-* branches deleted.

## 2026-10-27 (resumption, step 1: rev. 3.7 layout)

- Read rev. 3.7 (§1–§2.3, A.1–A.9, stage-review changes 1–5) and `gen` (`FRVIR.lean`,
  `FRVIRFinals.lean`, `FRTranscriptDefs.phases`); the dumps `items.json`, `ops-{L,P}.txt` checked
  at the phase boundaries (dummy node queries `askNode … false`, `idx … 18|20`, the finals).
- `transcript.rs`: A.3 fields (`Writer`/`Reader` per field), coordinate squeezes, flag verifier,
  item log. `leaf.rs` rewritten in A.4's order: Z2 127 values, Z3 26 degree-3 rounds of
  `w(ab+z) + W_E`, L3 + β, one 28-round S2, Lr/E zero, RS0 5 × 128, B′. First accept failed finZ:
  `W_E` was folded as `eq·E` (a product) instead of a fifth multilinear table; fixed (the `W_E`
  part as its own linear round term).
- `ligerito.rs`: field placement, fixed squeeze counts, dummy node queries, `κ_c` one squeeze
  (powers), final message padded to `2^7`, Pf 7 rounds.
- KATs: `items.json` 8,854/8,854 equal (verifier on zero proofs m = 25, 28, 30, 32; real m = 25
  proof; static table); chain-kind rows: Lean `kindRows gateBase Chain.chainTarget` dumped (448 MB,
  `logs/P2/r37/kinds/`), equal line by line to `circuit.rs`; digest shipped in
  `kat-chain-kind.txt`. `items.rs`: `reassemble` (A.5), round trip equal.
- VM (portable, 32 threads): `test-leaf 25…30` and `32` pass (|π| = 757,712; m = 30 prove 3.72 s,
  m = 32 15.0 s, 5.25 GB); `prove-leaf 30` through `rf-oracle`: |tr| = 8,854, query lengths equal,
  `acc` accepts, canary rejected; `leaf` request done/accept/reject. `prover.s` regenerated, sha256
  `3f5743f2…1866`. Disagreements and choices: RESULT §7.5.
- 7763 run 40554199135 (rev 3.7 layout, runner-assembled prover.s): leaf request 1.62–1.63 s,
  m = 32 6.51–6.64 s, all accepted (|π| 757,712, |tr| 8,854). Regression vs §6 from Z3 now
  folding z (x₆ round 0.25 s, tail 0.20 s at m = 30). Link ≈ 3.2–3.3 s, tree ≈ 525 s (estimates).
  Recommend restoring "skipping c". Steps 3–4 blocked (P2-RESULT §7.6). Branches deleted.

## 2026-10-27 (resumption 2: rev. 3.9)

- Read stage-review changes 6–9 and §2.3/A.9 of 3.9; `FRRingSwitch` (`Phi`, `phiTable`, `rsT`,
  `weightEval`). Dump `logs/S-0/dump/` (18:15): 8,874 items, `piSize` 755,680, P3 five squeezes,
  L3 128 B; finals S-F/S-G still placeholders there.
- Skip-c back in `leaf.rs` (Z2 `P^z ‖ P^{ab}`, Z3 on `a·b`, c-claim from round 1's banks as RS
  claim 0 with `eqZ λ ρ₁`); one Sh claim; `J_z = 4`; L3 8 values; `ringswitch.rs` to `Φ_{r″}`/`rsT`/
  `rsWeight`; `κ_c` from 5 squeezes with `eq(κ_c, bits₉(j))`. First build passed every test.
- VM: `test-leaf 25…30`, `32` pass (|π| = 755,680); m = 30 x₆ round 0.25–0.29 s and tail
  0.25–0.27 s (rev 3.7 0.36/0.42, pre-3.7 0.27/0.27); m = 32 13.3 s; `prove-leaf 30` via `rf-oracle`:
  |tr| = 8,874, `acc` accept, canary reject. `prover.s` sha256 `f3385c4d…62a3`. RESULT §9.
- 2026-10-27 7763 run 40561971516 (rev 3.9, prover.s f3385c4d…): leaf request 1.37–1.43 s, m = 32 5.58 s; skip-c recovered the 3.7 regression. Node ≈ 1.42 s (estimate), link ≈ 2.8 s, tree ≈ 445 s. Node prover waits for S-G's finals. Branches deleted.

## 2026-10-27 (resumption 3: finals, node)

- `ir.rs`: an interpreter of the S-G dump (`ops-L/P.txt`, all finals) with native op
  implementations after S-F2's `FRVerifierImpl`. First run: the dumped program accepts the native
  m = 30 and m = 32 proofs, rejects the canary, asks 8,874 items; 54 single-byte flips (3 per field)
  rejected by both it and the native verifier. Φ order (`r″` = RS1 0…6) and `eqZ`'s bit 6 confirmed
  from the dump's `finRS`.
- Node prover: blocked. No dump of `compileMux`'s M rows and cell map, of the L rows, or of
  `nodeLayout`'s intervals and link maps exists (A.7 says the M bases are pinned by such a dump);
  the Lr point is provisional. Stopped per the Pace rule; RESULT §11.3 lists what is needed.
- `prover.s` regenerated: sha256 `f3e33f44…f7a6`.

## 2026-10-28 (resumption 4: rev. 3.13, node)

- 3.13 for the leaf kinds against INT-2's dump: E before RS, Lr4 withdrawn, E4 (23 rounds) and
  E4 end (32 B), columns padded by 48 B, piSize 797,904; `ir.rs` gains `walkAB`. Items 8,891 equal;
  the dumped program accepts m = 30/32 proofs, canary rejected; prove-leaf via `rf-oracle` |tr| 8,891.
- `nodeshape.rs`: E2/E4/Lr on S-E5's dumped node rows. VM: E2 0.27 s, E4 0.53 s (after moving the
  gather to a prebuilt transpose: 1.07 → 0.53 s), Lr 0.015 s.
- Node prover not built. The S-E5 dump is the 3.12 mux program without finPf; the M rows are 282 k
  of 969 k per slot; the imports are not tied to H; the node targetS/linkW are pending. RESULT §12.4.
- prover.s sha256 `db43cee0…e8ea`.

## 2026-10-28 (pass 5: revision 4.0, track P2′)

- Item 1, the runner's CPUs: the PR #20 sandbox (`rfh/sandbox.py`) pins only the checks (`taskset`
  on one core, `checks.py`); the prover's `Sandbox(…)` calls (`rfh/prover.py` 161, 184, 236) pass no
  `cpus`, so the prover gets every CPU, shared with the service. Probe p2t-1 (run 40717768596, EPYC
  7763): `nproc` 4, affinity 0–3, `cpu.max` "max 100000", **2 cores × 2 SMT threads**, 1 MiB L2 per
  core. All 20+ earlier P2 runs report 4 CPUs.
- **The prover was already multi-threaded** (`par.rs`, since P1; every P2 runner figure is
  `threads=4`). The blueprint's "5.47 s per 2^18, one thread" is the 4-thread 7763 figure. Probe
  p2t-1, m = 32 through `rf-oracle`: 1 / 2 / 4 threads **12.95 / 6.91 / 5.54 s** (×1.87, ×2.34);
  m = 31: 6.42 / 3.41 / 2.76 s. From 2 to 4 threads only the witness (scalar BLAKE2s) gains: the
  vector phases hold one SMT sibling's core. VM (portable tier, no pclmul) m = 32: 248.6 / 126.7 /
  64.9 s (compute-bound software products, linear).
- `proofCap` removed (`main.rs` `acc`: `|π| < 2^64`; `format.rs`).
- Variable segment length: `prove_seg(…, m, n)`, `n ≤ 2^(m−14)`; the witness zero past `n`; the
  per-block phases take `used = n` (round 1, x₆ round/fold, the tail by a live prefix, the lincheck
  fold), the global `USED_BLOCKS` removed; `P^e` times `Σ_{b<n} eq(r_blk, b)` (`mle::range_eq`);
  `finSh`'s last block `n − 1`; the verifier takes `1 ≤ n ≤ 2^(m−14)` from the statement. π at the
  full length is byte-identical to HEAD's (m = 25, 28, 30; threads 1, 4, 32). Tests 30 + 1 ignored,
  release and debug.
- Probe p2t-2 (run 40719437801): segment cost against n (4 threads): L32 5.62 / 4.92 / 4.19 s at
  2^18 / 3·2^16 / 2^17+1; L31 2.80 / 2.09 / 1.37 s at 2^17 / 2^16 / 1. 8 threads = 4. **3 threads:
  the native verifier rejected the proof** — `ringswitch::weight_table` assumes chunk offsets at
  multiples of `2^nlo`; `par`'s split `n/k` is aligned only for power-of-two thread counts. Fixed in
  `par::chunk_len` (boundaries at multiples of `min_chunk`); π identical at 1–7, 12, 32 threads.
- `agg.rs`: the aggregate leaf (split L32/L31, one trace, one SIGN, `V_A` with chaining; provisional
  `hdr_A`), `prove-agg N`; `QV = 36,000`. THP for the large blocks (`alloc.rs`).
- INT-5's dump (rev 3.16) needed `ir.rs` updates (`rsWeight … act`, `linkWAll`, `shiftMask`,
  `shiftTarget` at `bnd`'s last block); the dumped L and P programs accept, canary rejected. KAT
  default path → `logs/INT-5/dump`.
- Probe p2t-3 (run 40721166772): THP pre-fault 6,000 MiB 0.82 → 0.22 s, proving unchanged; t = 3
  accepted; aggregates 2^18+1 / 3·2^18 / 2^20: 6.81 / 16.24 / 21.86 s, all accepted, peak 6.19 GB.
- `prover.s` regenerated: sha256 `e6ef7582…f8cc` (6,709,478 B). Model (`logs/P2/r40/model.py`):
  P̄ ≈ 8.6 s with sizes.py's nodes; the stream fits M ≤ 80 (≈ 36 % truncated). The blueprint's ×2.5
  is double-counted. RESULT §13.
- Probe p2t-4 (run 40722323237): the runner's build-asm wrote the same prover.s as the VM
  (`e6ef7582…`); L32 2^18 5.64–5.69 s, L31 2^17 2.83–2.85, L31(1) 1.39–1.44, aggregates 2^18+1
  6.89 s and 2^20 21.87 s, all accepted, peak 6.19 GB; 2 / 1 threads 6.84–6.93 / 13.02–13.04 s.
  Every `probe/p2t-*` branch is deleted.
- Aligned with S-0′'s in-progress draft: `hdr_A = 0x41 ‖ k ‖ 0^6 ‖ enc64 n ‖ e` and `aggChecks` before
  the segment verifiers (`FRAgg`), `L31` byte `0x4B` (`FRShape4`). `prover.s` regenerated: sha256
  `657a0ab0…3d3b`; linked binary passes selftest, test-leaf 30 (INT-5 Lean accept), prove-leaf 30 and
  31 --n 70000 through rf-oracle. Tests 32 + 1 ignored. Source rule: 0 findings.

## Pass 6 (revision 4.1, track P2″): the prover's per-step time

- Brief: per-phase profile of L32 at n = 2^18 and 2^17 on the 7763 (4 threads); lever 4 (witness
  overlap); lever 6 (round 1, commit, ring switch kernels); other levers from the profile; re-fit
  `L32(n)`, `L31(n)`. π byte-identical; the dumped Lean `acc` accepts, canary rejected; ≤ 11G.
- Instrumentation (no effect on π): `prof.rs` (`FLOCK_PROF=1`: sub-phase spans, printed as
  `| prof …` in the PROVE-LEAF line), spans in `ntt.rs` (copy / whole-buffer passes / in-block),
  `merkle.rs` (leaves / nodes, level 0 apart), `zerocheck.rs` (round-1 windows), `leaf.rs` (x₆ round
  and fold, tail rounds and folds, lincheck partial fold, ring-switch weight table), `ligerito.rs`
  (level-0 first round, folds), `witness.rs` (blocks). `bench.rs` (mode `bench`): memory read /
  write / copy GB/s over 1 GiB, and in-cache throughput of the round-1 window, the NTT butterfly,
  `axpy` (F×F) and `phi_apply`, per thread count. Probe `probe/p2t6/run.sh` (wraps
  `p2t-prover/run.sh`). Local π check: m = 28 `test-leaf` pi_b2s `756eecc0…2d15` = HEAD's.
- Probe branches are pushed from a temporary index (`git commit-tree` on HEAD; no local ref moves).
- Probe p2t-6a (run 40726261624, EPYC 7763, HEAD's prover + timers): L32 2^18 prove 5.41–5.48 s;
  sub-phases r1.windows 1.295, ntt (copy .074 + passes .392 + in-block .263) .73, merkle0 leaves
  .363 + nodes .086, rs.weight_table .558, wit.blocks .443 (+ chain .078), x₆ round .332 + fold
  .230, lig0 folds .416, lc.partial_fold .302, tail .248. Bench: memory read 21 / 39 GB/s (1 / 4
  threads), copy 22.5; round-1 window 4.1 µs per window per core, **no SMT gain** (4 threads =
  2 threads); butterfly 1.74 ns (1 thread), 2 threads ×1.94, 4 = 2; F×F 3.3 ns; phi_apply 8.0 ns
  per element (≈ 26 cycles), no SMT gain. Every vector kernel saturates at 2 threads: the NTT is
  clmul-bound (19 layers × 2^25 butterflies / 1.11e9 per s = 0.57 s of the 0.65 s), not memory-bound.
- Witness: the chain computed by chunk 0 of the pool job while the other chunks fill blocks behind
  it (`leaf_witness_mode`): witness 0.521 → 0.471 s at 2^18 (p2t-6b, run 40727455347).
- Lever 4 (p2t-6b): segment i+1's witness on an extra thread (solo) while the pool proves segment
  i: **no gain**. 2 × L32: 10.984 s with overlap vs 10.974 without; 4 × L32: 21.81 vs 21.71;
  2^18+1: 6.81 vs 6.77. The solo witness takes 2.3–2.8 s and slows the pool's commit0 (+0.19) and
  round 1 (+0.25) by about what it saves (0.47): the 4 hw threads are all busy in the vector
  phases, so the SMT siblings have nothing free. Peak +1.0–1.3 GB (7.33 GB at 2^20).
- Probe p2t-6c (run 40728620249): (i) round-1 window's c-banks from one 32-byte table pair
  (`conv2[bm][v] = (conv[v & 0x55], conv[v & 0xAA])`, one load for both banks): window 8.81 → 7.99 µs
  per thread at 4 threads, r1.windows 1.295 → 1.205 s; (ii) `lincheck::partial_fold` stripe by a
  64-byte bit transpose + 128-bit table XORs (`simd::pf_stripe`): 0.302 → 0.191 s; (iii)
  `weight_table` by `simd::phi_add` on every element: **slower** (0.558 → 0.653): the old loop skipped
  `elo[l] = 0`, and claim 2 (the shift claim) has only 64 of 1,024 nonzero `elo` entries. Fixed by
  index lists (`phi_add_idx`). Lever 4 with the pool at 3 threads + the solo witness: 2 × L32
  11.70 s vs 10.86 s at 4 threads without overlap — worse. **Lever 4 dropped** (code removed; the
  chain pipelining stays).
- S-0′'s note (47c5c6c): `seq4` (8,905 items, piSize 798,192) is not adopted in this pass; π stays
  byte-identical to the pre-change prover.
- Probes p2t-6d/6e/6g–6l landed on EPYC 9V74 / 9V45 / Xeon 6973P-C (off tier; kept in `logs/P2/run-*`
  as cross-checks: π identical base vs new on every one). On 9V74: shift-reduced butterfly slower
  than the clmul one (1.58 vs 1.37 ns), `vpclmulqdq ymm` ≈ 1.8e9/s per thread; the sparse
  `weight_table` (products only at claim 2's 64 nonzero `elo`) 0.473 → 0.342.
- x₆ fold by scaled tables (`(1+s)·t`, `s·t`, no products): no gain on 9V74 (0.229 → 0.233), worse on
  the 7763 (0.230 → 0.263, run 40733248360: the two 32 KiB tables leave L1). **Reverted.**
- `probe/p2t6/final.sh`: base (= branch HEAD's prover/, put into the probe commit as
  `probe/p2t6/base/` from a temporary index) and new, both built and linked on the runner, run
  alternately through one rf-oracle. Final (3 runs on the 7763: 40734390435, 40734399110,
  40734406678): π identical base vs new in all 27 cases (L32 n = 1 … 2^18, L31 n = 1 … 2^17, the
  2^20 aggregate), every proof accepted, every canary rejected, peak 6.19 / 3.32 GB unchanged.
  L32 2^18 5.52–5.60 → 5.17–5.36 s; 2^20 aggregate 21.80–21.93 → 20.53–20.62 s.
  Fits (pooled): `L32(n) = 2.58 + 2.66·n/2^18` (was 2.73 + 2.81), `L31(n) = 1.30 + 1.32·n/2^17` (was
  1.38 + 1.40). `prover.s` sha256 `d25ca624…e552`. All `probe/p2t-*` branches deleted.

## Pass 7 (track P2‴, revision 4.1: re-baseline to S-F4's dumps), 2026-10-28

- Read S-0′ §6 and S-F4 §3.2/§5. `params.rs` to `seq4`: Lr 17 (Lr1 9), E2 23 (E1 12), E4 25;
  fields Lr 816, E 2,336; piSize 798,192; 8,905 items (482 Fiat–Shamir). The kind bytes already
  matched (L30 = 3.x's `P` = 0x50, L31 0x4B, L32 0x4C).
- **The mask changes the prover's messages.** S-F4 §3.2/§5 say "with the zero witness the prover's
  messages are the same either way". That holds for the claimed sum only. The S2 round polynomials
  pair `e2` with the folded `inn`; changing `e2` at the Boolean point `n` changes the `X(1−X)`
  coefficient through `inn(n − 1)` (nonzero) after the first fold. So `leaf.rs` masks the table:
  `e2[n] = 0` when `n < 2^(m−14)` (`eq(τ, L)` cancels `e1[L]` in characteristic two); the native
  verifier adds `eq(τ, L)·eq(τ′, L + 1)`. Negative control `ir_unmasked_shift_rejected`: with the
  unmasked table (test hook `leaf::NO_MASK`), n = 777 is rejected by the dumped L30 program and the
  native verifier; n = 2^16 (full) is accepted.
- `ir.rs`: `targetS` with the 37-entry operand (leaf target × `range_eq(blk, L + 1)`), `shiftMask`
  as `shiftSegI` when its operand is `τ ‖ L` (36), `shiftTarget`'s explicit `κ_s` (4th operand;
  3.x's dumps found it from τ's pack), `lastAt`. `lastOps` needs nothing new.
- First run: `test-leaf 30 --n 1`: the dumped L30 program accepts, 8,905 asks, canary rejected.
- KATs (VM, portable, `logs/P2/r41p7/kat.txt`): L30 n = 1, 12,345, 2^16; L31 n = 1, 2, 70,001, 2^17;
  L32 n = 1, 2, 2^17 + 1, 3·2^16, 200,001, 2^18 − 1, 2^18: all accepted by the dumped program of the
  kind and by the native verifier; items KAT pass; canaries (flipped statement; `leafStmt h (n+1)`)
  rejected; three flipped bytes rejected natively.
- `ir::run_agg`: `V_A` reconstructed from `FRAgg.VAwith` (no `V_A` dump exists): shape, `segView`,
  `aggChecks`, then `seqAll` over the dumped segment programs (stops at the first rejection).
  Native `agg::verify` aligned to it: no check of `hdr_A` bytes 2–7 (Lean reads `k`, `n`, `e`
  only), stops at the first rejected segment. Split: remainder to L30/L31/L32.
- Native `acc` now dispatches as `V4with`: `'A'` → `V_A`; a bare segment → reject; node/W → reject
  (not built). `prove-leaf` checks with `Top::Seg` and runs the Lean segment program on the file's
  trace (`lean_seg`); `prove-agg` runs `Top::Lean` (`lean_acc`).
- `cargo test --release`: 35 passed, 1 ignored (`logs/P2/r41p7/cargo-test.txt`).
- Local rf-oracle (`logs/P2/r41p7/local-agg.txt`): agg 2^18 + 1 (L32 + L30(1)), 331,073 (L32 +
  L31(68,929)), 2^16 (L30) and `prove-leaf 31 --n 70001`: native acc and Lean acc accept, canary
  rejected, trace KAT pass.
- HEAD moved to 633ab78 (R-4 review) mid-pass. R-4-m5 (`hdr_A` bytes 2–7) is being fixed in the
  working tree's `FRAgg.lean` (another track). Native/IR `V_A` keep the zero check; the prover's
  proofs pass either form. `ir_agg_l30` gains the padding rejection.
- Local rf-oracle (`local-agg2.txt`): agg 2^20 (4 × L32, |tr| 35,620) and 3·2^18 + 5 (3 × L32 +
  L30(5)): acc and Lean acc accept, canary rejected.
- `prover.s` regenerated: sha256 `7c3b445b…f2fd` (7,007,702 B).
- Probes p2t-7a/7b/7c (commit 5380659 on 633ab78, temporary index; runs 40741779761, 40741784807,
  40741790546, all EPYC 7763): every runner rebuilt `prover.s` 7c3b445b… byte for byte; SELFTEST
  ymm. 72 canaries rejected, lean_seg 66/66 and lean_acc 6/6 accepted. Fits: L32 2.57 + 2.68·x,
  L31 1.29 + 1.33·x, L30 0.67 + 0.60·x (`fit.txt`). Branches deleted.

## Pass 8 (track P2⁗, revision 4.1: the node prover), 2026-10-28

- Read TRACK-RULES, P2-RESULT §11–§15, S-F4 §5, S-E12a–d (RESULT and the node dump's README),
  S-CN4 (pass 2), S-T2, BLUEPRINT §4.2–4.4 and A.6–A.9, PROVER.md. The INT-8 dumps landed at 23:14
  (`logs/INT-8/dump/`, with `group-N.txt`/`group-S.txt`, the uniform group programs in mux format).
- **Order forced by the stream**: an `N2`/`N4` node needs a previous node as its slot-0 child, so the
  first node to exist is `N8` (step 1: two aggregates). The KATs of this pass are on `N8`.
- **The prototype programs were not dumped.** `mregs-p{π}` numbers the registers of `protoProg π`
  (S-E12d's `progNodeG cells4 N4` / `progSegG`), which no ops file holds (INT-8's `group-*.txt` are
  the post-INT-8 programs: 97,657 registers against `mregs`' 97,414 / 97,257). Dumped them with a
  probe (`logs/fr-build-P2q/p2probe/ProtoDump.lean`, IRDump8's `showOp` in mux mode, `lean --run`
  against the S-E12d build tree's oleans copied to `logs/fr-build-P2q`, 7 s): `logs/P2/r41p8/proto/
  proto-p0.txt` (106,242 ops, 97,414 registers), `proto-p1.txt` (106,085 ops, 97,257 registers):
  the counts match `mregs`.
- `ir.rs`: `spec_kind` (a mux program's kind tables at an index), `run_regs` (every register's
  value), `hashStmt` at `N` (node statement).
- `mfill.rs` (new): loaders for `mrows`/`mregs`/`maux`/`node-N*.txt`; the slot fill (one′, selector
  copies, the registers' single-cell forms, the auxiliary imports `felems`/`bits`, then a forward
  row solve to a fixed point: a row with one unknown cell is linear in it unless the cell is in both
  `A` and `B`; leftovers zero); every row and every multi-cell register form checked.
  - Inactive slot (selectors zero, imports zero), both prototypes: **all rows hold** (485,230 /
    484,526), 3.2 s each (VM, one thread).
  - Prototype 1 at index `L32` on an `L32` segment (n = 5): the group program accepts, **every row
    holds, 0 conflicts, 0 form mismatches** (`mfill-kat-2.txt`).
  - At index `P30` on an `L30` segment: the program rejects at its last `assertEq` (line 106,084,
    `finPf`), 2 rows fail, 68 forms differ — S-E12c §1's obstruction 1 (the group runs `L32`'s
    finals at every index), which INT-8 removes (`mfill-kat-1.txt`).
- `node.rs` (new): `NK`, `BK` (A.6's kinds with targets), `bk_at` (`nodeLayout4`), the eight link
  families, a general block tape (`Circuit::build_general`: no chain constants) and the bit-sliced
  `trace_blocks` for any kinds; `witness`: both main chains (sequential compressions, the chains in
  parallel), the candidate final blocks and `c_A`, `hashStmt` per slot, WOTS per signed child (digit
  mux, key leaf, path; asserts the root is `vk`), the `WM` mirrors, the L bits, the M fill per slot
  in parallel (prototype program at the child's index through `Seq` over the child's trace); `check`:
  every relation directly.
- `node-kat N8 --m 32 --n 3` (two aggregates of one `L32` segment, toy signer): **every H block's
  R1CS with its target, the masked chain links, the 8 link families × 2 signed children, the 9 public
  cells, L's Booleanity, all 3,876,208 M rows and the 62 link/activity rows hold**
  (`node-kat-2.txt`). Witness 4.2 s on the VM (M fill 3.7 s, H trace 0.23 s for 187,548 blocks),
  peak 5.7 GB. With `L30` children (`--m 30`): the same, but 4 M rows (2 per active `L30` slot):
  obstruction 1 again (`node-kat-1.txt`).
- `nodeops.rs` (new): the node ops in specification form (`shiftMask4S`, `targetSNode4S`,
  `linkWAll4S`, `rsWeightS4` with `kf4`, `evalM`/`evalL` over the rows), and the prover's masked `In`
  table. KAT probe `logs/P2/r41p8/opsprobe/NodeOpsKat.lean` against `fr-build-SCN4b`'s oleans
  (`lean --run`, read-only): S-CN4b's `targetSNode4I`, `shiftMask4I`, `linkWAll4I` and S-T2's
  `rsWeightF4` at fixed points, all three kinds.
- KAT: all 24 Lean lines (`targetS`, `shiftMask`, `linkWAll`, `rsWeight` × N2/N4/N8 × 2 points)
  equal the native forms byte for byte (`node_ops_match_lean`). The probe took 15 min interpreted.
- M fill speed: one slot's solve was 2.5 s (worklist) / 2.0 s (replay); the inversions dominated.
  Skipping the inversion when the unknown's coefficient is 1: 1.3 / 0.8 s (VM, portable F).
- `cargo test --release`: 37 passed, 1 ignored. `prover.s` sha256 `a2890a65…ab42e` (8,108,075 B).
- Stopped here (context): RESULT §16.6 is the handover (the node PIOP for N8 first; then N4/N2 on
  INT-8's re-dump with `proto-p*.txt`; modes; where the rows come from on the runner; timings).

## Pass 9 (track P2⁵, revision 4.1/4.3: the node PIOP, N8 first), 2026-10-29

- Read TRACK-RULES, P2-RESULT §15–§16 (§16.6 handover), INT-8-RESULT "For P2", the A.9 node finals
  (`FRVIRFinals.lean`: `finLc`/`lcTail`'s `free` term, `finSh` node form, `finLr`; `FRVIRFinals4`:
  `gFinE`, `gFinB'`, `gFinPf` with `gCellOpsK`), `FRBlake2sCircuit.rowOf` (the base block matrix:
  inputs `(var k, one)` at 0…255, 512…1151; `(one, one)` at 1152).
- Default dumps moved to `logs/INT-8/dump` (`items.json` byte-identical to S-F4's). Leaf KATs on
  INT-8's uniform `ops-L30/31/32` at n = 777: accepted, canaries rejected, 8,905 asks.
- `circuit.rs`: `Circuit::build_base()` (A.6's base matrix; the node's `walkAB`). On the chain
  kind's rows it equals `build()`'s.
- `nodeprove.rs` (new): Z (all blocks, `targetS` the node's), Lc (7 H kinds by `maskRows` on the
  base matrix + `free` `(1+α)·rowW`, one 8-pair sumcheck; per-kind partial folds in one pass),
  Sh (rank-one terms keyed by slot weight: `Out` masked by `chainLk4`, `In` = `shift_in_table`, the
  8 link families' source and mirror slots at `κ_s^{f+2}`; then the 10-round collapse), Lr
  (`b·(one+b)`, Gruen zerocheck from 0), E2 (M rows, `eq·(ab + c)`), E4 (`W_M(r_E2) + κ_E³ W_L(r_Lr)`
  scattered, then the 25-round lincheck), RS (4 claims; Lc's outer weight × `kf4`, new
  `ringswitch::weight_table_kf`), B′ (the 9 cells at `κ′^{j+2}` in Ligerito's weight and claim).
- `ir::with_cells`: INT-8's `ops-N*.txt` carry the placeholder cells `oneCell + j`; the real cells
  (`cells4`) enter only as `finPf`'s 9 × 25 `keep` flags, so the reader rewrites them (checking the
  placeholders' bits first).
- **First N8 node proof** (`node-kat N8 --m 32 --n 3 --prove`, two aggregates of one L32 segment,
  S-E12d's M rows, `logs/P2/r41p9/node-prove-1.txt`): every prover-side sum check holds; **INT-8's
  dumped `ops-N8` (real cells) accepts, 8,905 asks, `stmtOk4` holds**; canaries rejected: another
  statement, a flipped E byte, and the placeholder-cell program. VM portable tier: prove 20.7 s
  (round 1 6.3 s, E4 3.9 s, Ligerito 3.2 s), peak 5.9 GB; the IR run 35 s.
- **Item 2, plan form.** First my own derivation from S-E12d's dump (templates = canonical
  instances, 32 per prototype; 13.6 MB base64, KAT equal). Then INT-9 landed (`logs/INT-9/nodedump`,
  `plan-form-p{π}.bin`, SHA256SUMS OK): `plan.rs` now reads INT-9's format (`read_planform`, by the
  README), and the blob (`nodeblob.b64`, `include_str!`) holds the two plan forms raw, the register
  forms and imports varint-coded, `proto-p{π}.txt`, `node-N*.txt`; LZ77 + base64: **5,429,184 B**
  (raw 14.5 MB, LZ 4.07 MB). `plan-kat` (`plan-kat-2.txt`): rows 428,815 / 427,104 equal `mrows` in
  order (cells, coefficients, ranges), register forms, imports, programs equal; decode 0.31 s.
  My derivation was dropped. The node path reads the blob unless `FLOCK_NODE_DUMP` is set.
- INT-9's prototypes: the fill failed 5 rows per active segment slot (S-E12e's `tplShiftSeg`: an
  inverse gate at `x = 0` leaves `i, s` unsolvable by single-unknown rows, and a later product row
  then has two unknowns). `try_row` now also solves a row with a known zero factor as `C = 0`.
  After that all rows hold.
- The proto-0 slot runs the previous node's program: it needs the node ops (`NodeCtx`) and the base
  matrix for `walkAB`: `ir::run_node_regs`, `PrevIn { ctx, base }`.
- `ir::with_cells`'s coordinate count is the group's `nc = m* − 7 = 25` for every node kind (N2 too).
- **Item 3, all on INT-9's data from the blob** (`logs/P2/r41p9/`): N8 (2 × k=1 L32; 2 × k=2
  L32+L31) → `n8.signed`; N4 on N8 (k = 2, 3); N2 on N8 (k = 2) → `n2.signed`; N4 on N4; N2 on N2.
  Every proof accepted by the kind's dumped program (real cells; `proto-p0` at the kind's index is
  the same program), `stmtOk4` holds, 8,905 asks; canaries (another statement, a flipped E byte,
  the placeholder-cell program) rejected. Every node relation checked clean before proving.
- VM times (portable F): N8 prove 19.5 s, N4 19 s, N2 9.6 s; the previous node's program run
  inside the witness costs 35 s (N8/N4) / 17 s (N2) in the IR interpreter.
- `rsWeight`'s node form (`nodeops::rs_weight4`) was a brute force over the 2^18 blocks per stage:
  34 s of the previous node's 35 s program run (FLOCK_IRPROF). Now per run of one kind
  (`kind_runs`) by two prefix sums of the product function: `node_ops_match_lean` (the Lean's 24 KAT
  lines) still equal, the test 176 → 5 s; the slot-0 witness 39 → 5.6–7.5 s on the VM.
- **Item 4, `first`/`step`** (`stream.rs`): chain files → aggregates (prove with the service's
  answers recorded, replay, SIGN) → node witness → node proof (recorded) → the node's trace by
  replaying the kind's program without its node ops (the item sequence does not depend on them;
  0.2–0.35 s) → SIGN → `proof.bin`. `step` picks N2 for ≤ 2 segments, N4 for 3–4. The native
  `acc` now accepts node files: the kind's program (prototype 0's at the kind's index) with its
  node ops, then `stmtOk4`. `probe/p2t9/stream.sh` (local, `logs/P2/r41p9/stream-local2/`, the
  asm-built binary, node data from the embedded blob only): first N8 (131,077 + 70,001), step N4
  (524,295, k = 3), step N2 (150,001): every output accepted by the native `acc`, every canary
  rejected; VM totals 44.7 / 58.3 / 26.4 s.
- Test `nodeprove::tests::node_n8_accepted` (N8 over two signed aggregates; accepted, 8,905 asks,
  `stmtOk4`; rejected: another statement, a flipped byte in Z2, L2, S2, Lr, E, RS0).
  `cargo test --release`: 40 passed, 1 ignored (`cargo-test.txt`). Source rule: 313 files, 0.
- `prover.s` regenerated: 14,630,224 B, sha256 `9b4e7690…eb57` (`build-asm.log`); the runner's
  link (`gcc -static -O2 -pthread`, 4 cores) 1.14 s against `build_s = 120 s`.
- Probes `probe/p2t-9a/9b/9c` (commit `ae083d0` on HEAD `39fb161`, temporary index: prover/,
  probe/p2t9, `.github/probe.conf`): runs 40801562683, 40801564683, 40801567863.
- Runner probes (3 × EPYC 7763): every runner rebuilt `prover.s` byte for byte; streams of 7 outputs
  (N8, N2 ×4, N4 ×2): 21 accepted by the native `acc`, 21 canaries rejected. Node prove N8 7.4–7.5 s,
  N4 7.5–7.9 s, N2 3.7–3.9 s (model 4.8 / 4.1 / 2.4); RS is the largest excess (1.45–1.7 s).
  Branches deleted. RESULT §17 written (17.9: the handover).
