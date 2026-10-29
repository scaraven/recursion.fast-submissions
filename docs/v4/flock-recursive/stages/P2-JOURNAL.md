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

## Pass 10 (track P2⁶, 2026-10-29): node prover speed, the handshake, S-E12f's re-dump

Base HEAD `cd195c5` (P2⁵), later `ef18e75` (S-E12f). Logs `logs/P2/r41p10/` (VM) and
`logs/P2/run-<id>/` (runners). Every cargo / prover command in a 16 GB scope with a timeout.

- Baseline: HEAD's binary (`flock-prover-base`), `node-kat N4 --agg 524291` and
  `N2 --agg 262147` on P2⁵'s `n8.signed`: pi_b2s `5062cfc4…` / `20d1eb92…` (= pass 9's), accepted.
  These two runs are the π-identity reference for every change below (local oracle, deterministic).
- **Instrumentation** (no effect on π): spans `ne2.matvec`, `ne4.scatter`, `ne4.sumcheck`,
  `ne4.slices`, `nrs.kf`, `nrs.weight_table`, `wit.warm_plans`, `wit.run_p0/p1`,
  `fill.solve(_inactive)`, `fill.check(_inactive)`; the stream prints the node witness's parts and
  `| prof …`; `FLOCK_IRPROF` adds a per-op-name total of the IR run (`ir ops …`). Mode `bench-rs [m]`
  (`bench.rs`): E4's slices and the four-claim weight table, old vs new, checked equal.
- **Finding: `first`/`step` had no `ready`/`go` handshake** (PROVER.md §3; `rfh/prover.py` waits for
  `ready` within `ready_s` = 10 s, else "no ready line"). Pass 9's probe started the binary without
  it, so the gap was not visible. Now `stream::run`: connect, warm, decode the node data, the three
  kind tables, the circuits, the inactive solve plans (`warm_plans`, was inside the timed witness),
  the skip tables and a 6000 MiB prefault, then `ready`; inputs after `go`; `done` after
  `proof.bin`. `probe/p2t10/stream.sh` drives the handshake (inputs staged, moved in at `go`; the
  request time is `go` → `done`). Start-up on the 7763 0.62–0.67 s.
- **RS** (`bench-rs 32` on the 7763, runs 40804570637 / 40804583754, 4 threads):
  - E4's slices from the block fold (`lincheck::partial_fold` at `r4[7..]`, then
    `partials_from_fold` at `r4[..7]`) instead of `ringswitch::partials`: 0.235 → 0.195 s; equal.
  - the weight table by **row tables** (`weight_table_rows`): `y = l + 2^lo h`; for each claim,
    `Q[p][β][l] = Σ_{i∈β} c Φ(e_lo(l) b_{8p+i})`, and the row `W(·, h) = Σ_p Q[p][β_p(e_hi(h))][·]`
    (16 sequential row reads per element instead of 16 scattered 64 KiB-table entries plus a
    product; `kf` multiplies `e_hi`; rows with `e_hi = 0` skipped): 0.83 → 0.52 (lo = 4),
    0.49 (5), 0.47 (6) s; equal at every lo (test `weight_rows_and_fold_slices`). Default lo = 4.
- **E4's sumcheck on `W`'s support** (`sumcheck::prove_pair_support`): `W` is non-zero on the M
  slots, the L bits and the one cell (16–25 % of the 2^25 elements). The first 12 rounds sum and fold
  only the 4096-element chunks where `W ≠ 0`; a dead chunk's `f` still enters later rounds (paired
  with a live entry in `(P₀+P₁)(Q₀+Q₁)` and in the folds; my first version zeroed it and π changed,
  `b-N2.txt`: rejected at op 66610), so after round 12 it is `Σ_l eq(r_{<12}, l) f[4096 c + l]`
  (one dot per chunk). Messages and the final pair equal `prove_pairs`'s (test
  `pair_support_same_messages`); no `f.to_vec()` copy. π identical (`c-N2.txt`).
- **Witness**: `trace_blocks`' pinned-input masks per kind of the batch (was a `pinned()` call per
  lane per input position); `try_row` without a heap allocation, products by a coefficient 1
  skipped (`mfill::mul1`, also in `m_scatter` and `Rows::eval`); the **H part** (inputs, the block
  trace as its own parallel job, mirrors, L) runs as one task beside the first fill of each
  prototype (slot 0's previous-node program run and solve are serial), then the other slots. VM at 4
  threads, N2: witness 7.49 → 5.81 s, π identical (`t4-{c,d}-N2.txt`).
- Runner profile (p2t-10a/b, HEAD + handshake + RS rows + E4 fold; S-E12e/INT-9 data): node prove N8
  6.82–6.87, N4 6.73–6.80, N2 3.36–3.42 s (pass 9: 7.4–7.5 / 7.5–7.9 / 3.7–3.9); witness N2
  1.29–1.65, N4 1.78–2.18, N8 1.94 s, of which h_trace 0.39 / 0.65 / 1.02 s, slot 0's program run
  0.39 (prev N2) / 0.61 (prev N4) / 0.75 (prev N8) s, fills 0.13–0.32 s each.
- **S-E12f's re-dump** (`logs/S-E12f/nodedump/`, SHA256SUMS OK, commit `ef18e75`): `plan-build`
  → `nodeblob.b64` 5,524,560 B (raw 14.74 MB); `plan-kat`: rows 603,404 / 593,997, terms 5.24 /
  5.33 M, 2,498 aux each, programs and slot tables equal, decode 0.51 s. Default dump
  `mfill::find_dirs` → `logs/S-E12f/nodedump`. **The fill needs no solver extension**: every slot
  0 failed rows, 0 conflicts, 0 form mismatches (N8: 4,751,976 M rows checked, `m_bad` 0); the
  kind-mux sub-templates' locals are all solved from the three kinds' operands. Node proofs N8
  (2 × L32 n=3), N4 on N8 (k=3), N2 on N8 (k=2), N4 on N4, N2 on N2: all accepted by the dumped
  programs (`ops-N*`, real cells = proto-p0 at the kind's index), `stmtOk4`, 8,905 asks; canaries
  rejected (`e-*.txt`).
- `cargo test --release`: 42 passed, 1 ignored (`cargo-test.txt`). `prover.s` 15,017,410 B, sha256
  `9da073e4…bfae` (`build-asm-b.log`).
- Runner probes on S-E12f's data (p2t-10c/d/e; 10c landed on the 7763): `FLOCK_IRPROF` showed slot
  0's program run = `evalM` 0.58–0.83 s + `targetS` 0.26–0.54 s (contended with the H trace); the
  rest < 7 ms per op. `targetS`: `target_words` by regions (h₀, the pinned message bytes, `t`, `fin`,
  the constant; was 1,216 `target()` calls per distinct block kind) and per-(word, byte) tables of
  `Σ eq(r_blk, blk)` in parallel (no HashMap); `evalM`: rows `v·2^20 + local`, cells `one +
  v·2^20 + local` (`one` a multiple of 2^20) → two 2^20 eq tables, one product per row matrix, no
  product for a coefficient 1. Test `fast_target_and_eval_m` (every block of every kind; `eval_m`
  = `eval_m_ref` on the node data), `node_ops_match_lean` still equal. π unchanged (`f-N2.txt`).
- Final probes p2t-10f/g/h/i (`prover.s` `a3db3bb5…`; two streams each; 10i on the 7763, run
  40808376661): node prove N2 3.14–3.19, N4 6.21–6.39, N8 6.36–6.38 s; witness N2 1.18–1.52, N4
  1.63–1.76, N8 1.93; requests 2^17 7.25–7.43, 2^18 9.71–9.74, 311,951 11.03–11.16, 2^20
  28.97–29.28 s; start-up 0.76–0.83 s; peak 6.97 GB; 16/16 accepted, canaries rejected (and 16/16 on
  each off-tier runner). Projection (`project.py`): mean step 12.10 + 2.16 s, fits `M ≤ 66`, 82 %
  of evaluations truncated, `P̄ ≈ 10.8 s`. All `probe/p2t-10*` branches deleted.
- `cargo test --release` 43 passed, 1 ignored (`cargo-test-2.txt`); source rule 333 files, 0.
  `prover.s` 15,084,266 B, sha256 `a3db3bb5…abdd`. RESULT §18 written (18.9: the handover).

## Pass 11 (track P2⁷, 2026-10-29): step time

Base HEAD `48d25ef` (P2⁶). Logs `logs/P2/r41p11/` (VM) and `logs/P2/run-<id>/` (runners). Every
cargo / prover command in a 16 GB scope with a timeout. π reference: `node-kat N2 --prev
logs/P2/r41p10/n8.signed --agg 262147 --prove` → pi_b2s `9368bcae…` (pass 10's `f-N2.txt`).

- Baseline on the VM (`base-N2.txt`, `base-N2-t4.txt`): at 4 threads `h_trace` 0.72 s (the 7763's
  0.74 s), so the trace is ≈ 1.45 thread-s per N2 (1,109 batches of 64 blocks, 1.3–1.4 ms each).
- **Lever 1, `trace_blocks`** (mode `bench-trace [N2|N4|N8]`, checked equal to `trace_blocks_ref`,
  the old code kept): the general tape compiled once (`trace_prog`: 99,863 nodes → 98,965 ops in
  16,958 slots; Var nodes alias their position, XOR forms in 573 reused temporaries, gates keep
  their row's forms), inputs by 17 64×64 transposes (was 55 k bit sets), the pinned rows by per-kind
  pin words (was `BK::pinned` per position per lane: 125 µs a batch), positions interleaved by four
  words (`tperm`) so the output is three AVX2 6-stage transposes per four words with 32-byte stores.
  VM, one thread: 1.39 → 0.53 ms per batch (eval 0.25, output ≈ 0.2); all threads 0.36 → 0.13 s.
- **Slot 0 beside the aggregate**: `node::slot0_fill` (the previous node's program run and its
  solve) needs only `prev.bin`; `stream::run` runs it on its own thread while the aggregate is
  proved, and `witness` takes it (`pre0`). `FLOCK_NO_PRE0` restores the old schedule.
- **Lever 2, `prover setup DIR`**: a toy chain (local oracle, test signer): N8 over two aggregates,
  N2 and N4 over it (N4's aggregate 2·2^18 + 9: L32, L32, L30), then slot 0's fill over the N2 and
  the N4. Plans keyed `0` inactive, `1 + ix` active; an active fill without its key's order tries
  another index's (as pass 10 did across segment kinds). Setup records p0 `538138/-/-/446067`, p1
  `530509/436594/436594/-`: p0's order at N8 replays over N2 and N4 (no new order recorded), p1's
  at L32 over L30. Stored as `plans.bin` (19.1 MB, tag = blake2s of the node blob); `Pre::new` and
  `node-kat` load it from `$RF_SETUP`. **Replay safety**: `mfill::fill` re-solves by worklist
  when a replayed order leaves a row unsatisfied (no fatal from a stale order). VM setup 124 s at
  16 threads (contended), peak 7.09 GB.
- Witness schedule: every slot whose order is known starts beside the H part (was: the first of
  each prototype; the rest after). VM N2 witness 5.23 → 2.57 s; π `9368bcae…` (`e-N2.txt`).
- RS `ROW_LO` 4 → 6, the claims' row tables built in parallel.
- `cargo test --release` 43 passed, 1 ignored (`cargo-test-1.txt`, before the RS change).
- Probes `probe/p2t-11a/11b` (runs 40812467041, 40812469354): base (HEAD's prover.s) and new on
  one runner, setup timed and sized.
- **Runner 7763, run 40812467041** (p2t-11a; 11b, run 40812469354, got an EPYC 9V74): base vs new
  (trace, slot 0 beside the aggregate, setup plans). Setup 48.8 s, 7.0 GB, `plans.bin` 19.1 MB.
  Start-up 0.71–0.74 → 0.45–0.48 s (pre 0.18, prefault 0.28). Witness N2 1.15–1.50 → 0.59–0.85,
  N4 1.64–1.81 → 0.87–0.91, N8 1.91 → 1.17 s. The aggregate +0.14–0.37 s (slot 0, 0.63–1.28 s,
  shares the cores). Requests −0.28…−0.42 (N2), −0.61…−0.66 (N4), −0.68 (N8) s. 32/32 accepted,
  canaries rejected.
- Found there: the remaining p1 fills still ran after the H part (the schedule change came after
  the push), and a p1 replay from setup's full-L32 order falls short on a partial segment (VM,
  `--agg 131077`: 137 of 436,594 entries unsolvable, 53 rows fail). **Replay made tolerant**: an
  entry that does not solve is retried after the rest; then the row check; rows failing after a
  replay are completed by the worklist from where the replay stopped (adjacency cached per
  prototype, built before `ready`), and checked again. The deduction is monotone, so its closure
  does not depend on the order: the base binary gives the same π (`f60dc083…` both,
  `base-N2-131077.txt`, `j-N2-131077.txt`).
- **Zero skips**: a third of a node's windows are zero (N2: 87,875 of 262,144; the L region past its
  used part, the tail past M, holes in M). Round 1 skips a window whose a, b, z are zero (the convert
  tables map 0 to 0, checked); `round_x6`/`round_tab` skip a range where a or b is zero;
  `fold_x6` writes zeros for zero rows (`t[·][0] = 0`). π `9368bcae…` (`g-N2.txt`).
- Slot 0's thread at nice 19 (`FLOCK_PRE0_NICE=0`: off): it takes the cycles the aggregate leaves,
  all of them once the caller waits for it. Probe p2t-11c/11d: base, new, and new with
  `FLOCK_PRE0_NICE=0` (the A/B) per rep.
- **Runner 7763, run 40814845050** (p2t-11d; 11c, run 40814841942, got a 9V74): base / new / alt
  (alt = `FLOCK_PRE0_NICE=0`). 48/48 accepted, canaries rejected. Node prove N2 3.11–3.18 →
  2.72–2.75, N4 6.2 → 5.2, N8 6.37 → 5.83 s (zero skips, RS lo 6). Witness N2 0.50–0.60, N4
  0.92–1.13 s (N4: every L32 slot replayed setup's only p1 order, an L30 one, short by 1,976 cells,
  then completed: 0.58 s a fill). The aggregate is still +0.36 s at 2^17 **with or without nice**
  (nice only slows slot 0: 2.15 vs 1.26 s), so the cost is not CPU share but the shared core (SMT)
  or memory. Projection (`r41p11/project.py`, this runner): base mean step 11.98 + 2.12 s, M ≤ 67,
  79.3 % truncated → new 10.86 + 1.88 s, M ≤ 74, 51.6 % truncated, P̄ 10.69 → 9.58 s.
- Nice removed. Setup now records **each key's own order** (`set_exact_plans`): keys `1 + ix` for a
  full child, `4 + ix` for a partial segment (below its kind's cap; `fill_part`), the twin variant
  tried first when a key has none. Setup chain: N8 over n = 3, 5 (L30 partial), N2 over 200,003
  (L32 partial), N4 over 2·2^18 + 9 (L32 full, L30), a witness over 2^18 + 100,000 (L31 partial),
  slot 0 after N2 and N4. p0 `538138/446067/446067/446067`, p1 `530509/436594/-/-/436594×3`;
  plus the **inactive fills** (`inactive-p{0,1}.bin`, 16 MiB each; `fill(p, None)` returns them).
  VM setup 173 s at 16 contended threads, 62 MB. KATs: N2 131077 `f60dc083…` (L32 partial vs
  200,003's order: 65 short, completed), N2 262147 `9368bcae…`, N4 524291 `a16ab6a3…` (= pass 10's
  `e-N4.txt`); no full replay falls short.
- Lincheck's block fold skips zero stripes; Sh spans (`sh.collapse/pairs/prefix`). Unit tests
  `trace_blocks_matches_ref`, `round1_zero_windows_skipped_equal`, `plans_round_trip`:
  `cargo test --release` 46 passed, 1 ignored (`cargo-test-3.txt`). Source rule 353 files, 0.
- Probes p2t-11e/11f: base / new / alt (alt = `FLOCK_NO_PRE0=1`: slot 0 inside the witness).
- **Runner 7763, run 40817225300** (p2t-11e; 11f, run 40817228197, a 9V74): setup 63.9 s, 7.09 GB,
  66.8 MB. 48/48 accepted, canaries rejected. new vs alt (`FLOCK_NO_PRE0=1`): slot 0 beside the
  aggregate is ≈ 0.1 s better per step (N2 node part 3.30 vs 3.42 s). Witness N2 0.37–0.55, N4
  0.67–0.89, N8 0.67 s. Sh: `collapse` 0.12, `pairs` 0.07, `prefix` 0.02 s (N2). Projection, this
  runner: base 11.84 + 2.08 s, M ≤ 68, 75.1 % truncated → new **10.58 + 1.86 s, M ≤ 76, 46.1 %**,
  P̄ 10.55 → 9.33 s. Node data decode (VM, `plan-kat` spans): b64 0.02, LZ 0.05, parse 0.41 s.
- **S-E13a's re-dump (orchestrator, `8cc8ccd`)**: `logs/S-E13a/nodedump` (SHA256SUMS OK) is now the
  default dump (`mfill::find_dirs`); `plan-build` → `nodeblob.b64` 7,397,352 B (raw 27.1 MB: the
  three kind tables carry the 25–26 k link rows); `plan-kat` all equal. **Row check before any
  prover change** (N8 `--m 32 --n 3`; N2 over pass 10's N8): pack rows 0 failures; **102 (N8) / 100
  (N2) link rows fail, all in slot 1's link region past its first 1,626 rows: S-E13b's WOTS rows**
  (plus slot 0's program run rejecting pass 10's N8, made on the old matrices).
- **S-E13b's L cells** (`h_part`, per signed child σ, stride σ): 8704+t idx bits; 8720+i the running
  products `R_i = Π_{j<i} f_j` (`f_j = x³·x⁻¹^{d_j}`, then `x⁻¹^{4^t c_t}`, `x = ⟨2,0⟩`); 8960+128t+q
  the bits of mirror 549+t's element 1; aggregates: 11008+2(j−1)+h `T_{k,h}` = the final block's
  `h_out` halves (others 0), 11264+128(j−2)+q the bits of main block `aggL j − 1`'s element 7.
  **Mirror 549+t now holds the whole `r`** (it held bytes 0–30; W5's mux is on whole elements).
  After: **every row holds** on honest N8 (`p-N8.txt`), N2/N8 k=2 (`p-N2.txt`), N4/N8 k=3
  (`p-N4.txt`), N2/N2 k=1 (`p-N2N2.txt`), N4/N4 k=4 (`p-N4N4.txt`): `m_bad 0, link_rows_bad 0`;
  all accepted by the dumped programs, `stmtOk4`, canaries rejected.
- Local stream on the new data (VM, load ≈ 29; setup 166 s, 66.8 MB): N8, N2, N4, N2: 4/4
  accepted, canaries rejected (`stream-p.out`); `acc` 1.3–1.8 s on the VM (portable tier, loaded).
- `cargo test --release` 46 passed, 1 ignored (`cargo-test-4.txt`). **`prover.s` 17,441,648 B,
  sha256 `5e1bab39…61bc`** (`build-asm.log`). Probes p2t-11g/11h: base / new on S-E13a's data.
- **Final, runner 7763, run 40820003716** (p2t-11i; 11g Xeon 8370C, 11h/11j EPYC 9V74: acceptance):
  S-E13a's data, `prover.s` `5e1bab39…` rebuilt by every runner. 32/32 accepted, canaries rejected.
  Setup 64.9 s, 7.13 GB, 66.8 MB; start-up 0.59–0.63 s; `acc` N2 0.45, N4 0.52–0.53, N8 0.62 s.
  Projection (`project-final.txt`): base 12.06 + 2.15 s, M ≤ 67, 81.3 % → **new 10.80 + 1.99 s,
  M ≤ 74, 52.5 % truncated, P̄ 9.53 s**. All `probe/p2t-11*` branches deleted. RESULT §19 written
  (§19.9: the handover).

## Pass 12 (track P2⁸, 2026-10-29): the segments' round 1, the node's zero skips

Base HEAD `5e99fba` (P2⁷, `prover.s` `5e1bab39…`). Logs `logs/P2/r41p12/` (VM) and
`logs/P2/run-<id>/` (runners). Every cargo / prover command in a 16 GB scope with a timeout. Probes
`probe/p2t-12a … 12m` (temporary-index commits on HEAD, `probe/p2t12/`), all deleted.

- **π references.** The brief's KATs (`9368bcae…`, `f60dc083…`, `a16ab6a3…`) were made on S-E12f's
  data with pass 10's N8; since pass 11 (S-E13a's matrices, S-E13b's cells) HEAD gives other π on
  those inputs. The references used: pass 11's final KATs on S-E13a's data (`r41p11/p-*.txt`): N8
  `d8b25c6a…`, N2 `515f21b3…`, N4 `c5d6ae84…`, N2 k = 1 `816a1f84…`, N4 k = 4 `a3c6e71b…`; the
  segments by `test-leaf` (28 `62f91a4b…`, 30, 31 `--n 77777`, 32), always HEAD's binary (built from
  `git archive HEAD`, `flock-prover-base`) against the new one. Stream proof files are not
  byte-deterministic between two runs of one binary (`pi_sha` differs base vs base), so stream π
  cannot be compared; the KATs carry the identity.
- **Round 1, the tower window** (`simd::r1::window_t`, pass 11's `r1::window` kept). GF(2^8) as
  `GF(16)[w]/(w² + w + λ)`, `GF(16) = GF(2)[u]/(u⁴ + u + 1)`; the LDE table holds tower bytes; a
  product is three GF(16) products (Karatsuba) by `vpshufb` logs, a mod-15 sum (`min(s, s − 15)`,
  `log 0 = 0xF0` keeps bit 7 and `vpshufb` gives 0) and one `vpshufb` per product into a table that
  already holds the A.1 byte times `ζ^k` (no Horner step); the LDE's eight lane permutations grouped
  as `G₀ + P₃G₁ + P₄(G₂ + P₃G₃)` (6 shuffles, was 14). Equal to `window_portable` and pass 11's
  window on random, sparse, zero and all-ones windows (test `tower_window_matches`, which also checks
  the Karatsuba formula through `phi` on all 65,536 pairs).
- Probe 12a (7763, run 40823004790): window 4.53 → 3.27 µs; parts `rows_t` 1.66, conversion 1.47
  (L2-bound byte tables, 64 + 128 KiB), `mac_u` 0.28 vs `axpy` 0.66 µs; round 1 at m = 32 1.26 →
  0.92 s, equal.
- **The conversion by `vpshufb`** (`r1::convert_t`, pass 11's `convert` kept): `conv[bm]` is
  GF(2)-linear, so 4-bit tables (16 KiB, L1): byte planes of 32 lanes accumulated four output bytes
  at a time (one table load for both lane groups), then a 16×16 byte transpose; the `z` rows taken in
  the order 0, 2, 4, 6, 1, 3, 5, 7 (`bit_transpose_eo`) so each bank reads one nibble. 12b/12c (EPYC
  9V74, runs 40823704213, 40823915867): conversion 1.30 → 0.52 µs, round 1 0.95 → 0.58 s.
- **`mac_u`**: the windows' `eq` weights accumulated unreduced (three Karatsuba parts per pair,
  reduced once per chunk; `mac_u_ref` and `axpy` are the references).
- A `rows_t` variant with the table offsets precomputed by `vpmovzxbw` did nothing (12d/12e:
  1.67–1.79 vs 1.66 µs): reverted.
- **Shift reductions** (`bench-k`): the F product with its three reductions by shifts, two in one
  register (`mul`; pass 11's is `mul_cl`) and the butterfly's (`butterfly`; `butterfly_cl`). 7763
  (12d/12e, runs 40824432457, 40824435759): butterfly 1.745 → 1.62, `axpy` 3.33 → 2.92–2.95 ns; 9V45
  (12f): `axpy` 2.38 → 2.16, butterfly ±; Xeon 8573C (12j): butterfly 1.17–1.20 → 1.29 (worse), `axpy`
  equal. `mul` is the shift form everywhere; the butterfly's form is chosen by CPU (`bfly_shift`: AMD
  family 19h without AVX-512 = Zen 3; `FLOCK_BFLY=sh|cl`); the selftest checks both forms.
- The AVX2 round-1 window runs on every AVX2 CPU (`r1_avx2`, unless `FLOCK_TIER=portable`), so this
  VM (AVX2, no `pclmulqdq`) runs it inside the prover: the local KATs cover it (N2 VM zc_round1 6.23
  → 0.64 s).
- **Item 2, node zero skips.** Sh: `collapse_keys` (one pass over the blocks for every key, a key's
  bytes skipped when zero; `collapse_n` the reference, `debug_assert`). Ligerito level 0: round 1
  skips zero 4,096-pair ranges of `g`; `fold_msg` writes zeros for a zero block of `g` and skips its
  message part (`W` still folds). **Item 3**, E2 (`zc_abc`): the `c` part skips zero stretches;
  `fold_f_sparse` (zeros for zero 1,024-pair stretches) for `a`, `b`, `c` and for the node's Z tail.
  Tests `collapse_keys_matches`, `fold_sparse_matches`.
- First streams (12g/12h, 7763, runs 40824961318, 40824964462): N2 2^18 8.71 → 7.77–7.85 s, but
  pass 11's probe gave the base no `RF_SETUP` (unfair to HEAD's base, which reads the setup); fixed
  in `probe/p2t12/run.sh` (both get it), plus the KATs (`kat.txt`, `kat-check.txt`) and pass 6's
  segment-fit cases (`fit.txt`, `fit12.py`) on the runner.
- 12i/12j (7763 run 40826290907, Xeon 8573C run 40826296002): **KATs on the ymm path: base = new on
  all 8** (5 node, 3 segment), selftest pass. Streams (7763, base with the setup): every step −10 …
  −12 %. The fit loop's case list was one word (a quoted default inside `${…:-"…"}`), which made an
  artifact path with colons, and the upload failed; results read from the job logs (`run-step.log`).
- **Items 4/6, a short replay's completion.** `fill p1 replay: 434612 of 436594 entries solved,
  1976 unsolved` on an L30 child at n = 49,807 (setup's L30 order is at n = 5): the completion ran the
  worklist from all ~600 k rows, then the check again over all rows. Now the worklist starts from the
  rows that touch an unknown cell (a row without one solves nothing: `try_row`; the closure is the
  same) and the second check covers only the rows that failed or touch a cell the completion solved
  (every other row reads the same values). `FLOCK_FULL_RECHECK=1` restores both. VM, N2 over 311,951
  (L32 + L30): π `db9942b1…` with the setup (narrowed), with `FLOCK_FULL_RECHECK=1`, without the setup
  (from scratch) and HEAD's base with the setup; the short fill's check + completion 1.10 → 0.46 s
  (VM). Per-`n`-class orders are not needed now.
- **Item 5, the node data's image** (`plan::save_image`/`load_image`, `nodedata.bin` in `/setup`,
  written by `prover setup`, tagged by the blob's hash; the blob format unchanged; `decode_blob` the
  fallback). The decoded data is 298 MB (5.3 M nonzeros per prototype, each with a 16-byte
  coefficient, only 513 distinct): 7763 `bench-nd` blob 0.147–0.173 → image 0.070–0.083 s. Test
  `image_round_trip`. `data_tag` computed once.
- Item 4's slot 0: unchanged beyond the completion; a parallel row check does not cut CPU, and slot 0
  runs beside the aggregate on the same cores.
- `cargo test --release`: 51 passed, 1 ignored (`cargo-test-2.txt`). Source rule (`logs/org20`): 359
  files, 0 findings. **`prover.s` 18,042,211 B, sha256 `f0841393…0187`** (`build-asm.log`).
- **Final** (12k 7763 run 40828606971; 12l Xeon 8573C 40828619224, 12m EPYC 9V45 40828630557): every
  runner rebuilt `prover.s` byte for byte; KATs base = new (8/8) and the 11 fit cases' π base = new on
  all three; 32/32 outputs accepted and 32/32 canaries rejected per runner. 7763 fits: L32 2.476 +
  2.720·n/2^18 → 2.149 + 2.415, L31 1.239 + 1.350 → 1.072 + 1.203, L30 0.654 + 0.602 → 0.567 + 0.531
  s. Projection (each prover with its own fits, `project-final.txt`): base 10.67 + 1.95 s, M ≤ 75,
  49.1 % → **new 9.54 + 1.87 s, M ≤ 83, 30.4 % truncated, P̄ 9.41 → 8.43 s**. Setup 59.2 s, peak
  7.12 GB, 365 MB (the image 298 MB); request peak 7.10 GB.
- Over the 7763 streams' 8 steps: `lig0.folds` −14 %, tail rounds/folds −11 %, NTT passes −5 %,
  blocks −8 %, but `x6.fold` +4 % (the shift reduction beside its table loads): `x6_fold` should take
  `mul_cl` (≈ 0.015 s per step; not done, it would have needed another final round).
- All `probe/p2t-12*` branches deleted. RESULT §20 written.

## Pass 13 (track P2⁹, 2026-10-29): determinism, the node's fills, indexed coefficients

Base HEAD `2d9dd8c` (P2⁸, `prover.s` `f0841393…`). Logs `logs/P2/r41p13/` (VM) and
`logs/P2/run-<id>/` (runners). Every cargo / prover command in a 16 GB scope with a timeout. Probes
`probe/p2t-13a … 13e` (temporary-index commits on HEAD, `probe/p2t13/`, the KAT nodes from
`probe/p2t12/kat/`), all deleted.

- **Item 1, determinism.** Two streams of HEAD's binary on the VM against a service built with
  `--features insecure-test-keys` and the same fixed keys (`probe/p2t13/stream.sh`, `RF_ORACLE_ARGS`;
  chains 2^17 ×4: N8, N2, N4) give **byte-identical `proof.bin` at every step** (`det-vm-{1,2}`:
  `d204d5df…`, `d416c365…`, `ddac2ea2…`). So the prover is deterministic given the oracle; pass 12's
  base-vs-base difference is the service: `rf-oracle` draws a fresh PRF key and signing seed from
  `getrandom` at every start (`.contract/service/src/main.rs`), and every challenge, Merkle hash and
  signature of a stream depends on them. Not a bug.
- The rules (`logs/org20/harness/PROVER.md` §3 "Re-timing", `harness/rfh/bench.py` `retime`): a re-run
  is a fresh process on the same inputs **under the same service lifetime**; its output must be
  accepted (`check` against the step's statement); the faster run's `P`, `V`, `|π|` are scored and the
  first output stays the next step's child. No byte comparison anywhere, and none is possible: a
  re-run's signatures take later one-time keys, and a node's π commits to its leaf children's
  signatures (signed during the step). `stream.sh` `P2T13_RERUN=1` emulates it (`det-3`): every
  re-run's π differs from the first (N8 `74202b04…` vs `ed448269…`, …), all accepted, canaries
  rejected.
- On the runners (`run.sh` `P2T13_DET=1`, after `prover setup`, so the replay by levels runs): det-1 =
  det-2 byte for byte, and equal to the VM's hashes, on the 9V74 (run 40834066233) and on four 7763
  runs; det-3's step 1 equals det-1's.
- **Item 3, indexed coefficients.** `mfill::Rows::coefs` is `Vec<u16>` into `cv` (513 distinct
  values per prototype, `cv[0] = 1`), built through an interning map (`term`, `done`);
  `read_planform` interns the plan form's table once and its products per `(c, d)` pair; `cmul`
  skips the product for index 0; `coef_values` gives the 16-byte form (`proto_eq`, tests). The image
  is `FLNDIMG2` (indices + table; a version-1 image is refused, the blob is the fallback): 298 →
  150 MB. Blob format unchanged. KATs equal (version a, with and without the setup).
- `m_matvec`: terms with coefficient 1 summed apart from the unreduced products.
- **Item 4, the fills.** (a) **Level schedule** (`mfill::schedule`, `Sched`): an order's entries in
  levels so that no entry of a level touches a cell another entry of the level writes, every entry
  after the writers of its row's cells and after the earlier readers of its own cell; a level of
  ≥ 4,096 entries runs in parallel (`replay_levels`, `try_row_p` with `want`: an entry writes only its
  own cell, else it is a miss, retried in order by the existing loop). The orders have 15,872 levels;
  17 large ones hold 72 % of the entries. `FLOCK_SEQ_REPLAY=1` is the sequential replay. (b) The
  **row check in parallel** (chunks' failures concatenated in order: the same list). (c) Inverse
  caches: `Rows::cvinv` (a solve whose linear factor is one coefficient), `Proto::fcinv` (the
  register forms' coefficients), `B64::inv` by an addition chain (63 squarings + 8 products, was 127
  products; `inv_ref`). On the VM (c) changed nothing measurable (seq replay 0.45 s either way:
  inversions are rare); kept (no harm, references `FLOCK_FILL_INV=1`, `inv_ref`). VM, N2 KAT with
  setup, slot fills: solve 0.45 → 0.17 s, total 0.86 → 0.34 s. (d) `m_scatter` as a **gather by
  cell** (`ByCell`: terms grouped by cell; every cell written once, 2^14-cell chunks of every slot in
  parallel; `m_scatter_ref` = pass 12's). Test `scatter_gather_and_matvec_match` (N2, N4, node data).
- Probe 13a (9V74, run 40834066233): node witness 0.333 → 0.222 s, slot 1 fill 0.273 → 0.169,
  slot 0 0.714 → 0.417 (beside the aggregate), but start-up 0.40 → 0.48 s: `pre.warm_plans` 0.021 →
  0.111 (schedules, `ByCell`, `fcinv` built per prototype). Fix: the schedules are written by
  `prover setup` (`sched.bin`, `FLSCHD01`, tagged; `load_scheds` checks lengths, monotone levels and
  that the entries are a permutation) and the remaining warm tasks run as separate jobs over all
  threads. Test `schedules_levels_and_round_trip`.
- **Item 5**: `x6_fold`'s ymm kernel takes `mul_cl`. 7763 step 3: `x6.fold` 0.263 → 0.229 s.
  Also tried: the fold by two scaled tables (`(1+s)T`, `sT`, the λ tables being F₂-linear: no product
  per entry). 7763 (probe 13b, run 40835907467) `fold_x6` over 2^22 pairs 0.0145 → 0.0172 s (two
  32 KiB tables leave L1): reverted.
- **Item 2, NTT**: `encode`'s replication fused into the first radix-4 pass (`first_pass_from`:
  each work item copies its four row slices from the message; `FLOCK_NTT_COPY=1` the reference;
  `encode_is_novel_basis_evaluation` covers both paths). 7763 step 3: `ntt.copy` + `ntt.passes`
  0.105 + 0.517 → `ntt.first` + `ntt.passes` 0.174 + 0.392 s (−0.056 s). No other segment lever
  this pass (the Merkle leaves are the service's hashing; round 1's `rows_t` and Ligerito's folds as
  pass 12 left them).
- `cargo test --release`: 54 passed, 1 ignored (`cargo-test-2.txt`). Source rule (`logs/org20`): 364
  files, 0 findings. KATs (versions a, b, c, e; VM, with and without the setup) equal to HEAD's:
  N8 `d8b25c6a…`, N2 `515f21b3…`, N4 `c5d6ae84…`, N2 k = 1 `816a1f84…`, N4 k = 4 `a3c6e71b…`, the
  short replay N2 over 311,951 `db9942b1…`, `test-leaf` 28/30/32/31 `--n 77777`. **`prover.s`
  18,366,894 B, sha256 `7c870444…471f`** (`build-asm-e.log`).
- **Final** (13c/13d/13e, runs 40838740210, 40838753998, 40838766566, all EPYC 7763): `prover.s`
  rebuilt byte for byte; selftest pass (`bfly=sh`); KATs base = new (9/9) and the 11 fit cases' π;
  44/44 outputs accepted and 44/44 canaries rejected per runner (32 stream outputs, the 6 det-1/2
  outputs, det-3's 3 + 3 re-runs); fixed-key streams identical. Run 40838740210: mean step +
  overhead 11.42 → **11.10 s**, M ≤ 83 → **86**, truncated 30.6 → **26.5 %**, P̄ 8.44 → 8.09 s (the
  other two: 11.49 → 11.21, 11.52 → 11.23 s). Start-up 0.489 → 0.530 s (`pre.warm_plans` 0.028 →
  0.071: `ByCell`, `fcinv`). Setup 230 MB (was 365).
- All `probe/p2t-13*` branches deleted. RESULT §21 written.
- **Added item (orchestrator): B0's row layout.** `nodeblob.b64` rebuilt from `logs/B0/nodedump`
  (`plan-build`, SHA256SUMS OK; 7,439,340 B, sha256 `6ae3e6d8…`; S-E13a's kept as
  `r41p13/nodeblob-SE13a.b64`); `find_dirs`' default is now `logs/B0/nodedump`. **Plan-form KAT**
  (`plan-kat`, `plan-kat-B0.txt`): p0 580,620 rows, 5,244,098 terms; p1 573,389 rows, 5,325,108 terms;
  `proto_eq` Ok, programs equal. No prover change was needed (the split keys' halves are separate
  keys of the unchanged plan-form format; `read_planform` rebuilds them).
- **The node KATs' π change** (the matrices' row order): new signed KAT nodes in `probe/p2t13/kat/`
  (local, uncommitted; N8 m = 32 n = 3; N2 and N4 on it), each accepted by the kind's dumped program,
  canaries rejected. New references (VM, `kat-f*.txt`; equal with and without the setup and with
  every reference path on: `FLOCK_SEQ_REPLAY`, `FLOCK_SCATTER_REF`, `FLOCK_NTT_COPY`,
  `FLOCK_FILL_INV`, `FLOCK_FULL_RECHECK`): N8 `0277148e…`, N2 `b7ab5cb7…`, N4 `87865636…`, N2 k = 1
  `2571a475…`, N4 k = 4 `06a1664c…`, N2 over 311,951 `edbd211a…`; the leaves unchanged (`62f91a4b…`,
  `02997486…`, `559306ee…`, `aac62938…`). `probe/p2t13/kat-expected.txt` holds them for the runner.
- **Lean V with B0's modules**: `logs/fr-build-P2t13` = a copy of `logs/fr-build-B0` (its B0 modules
  equal the worktree's live files; it differs from the worktree only in 13 FRX modules, G3's
  in-progress proof golf), with the harness's badge rendered as `evaluate.py` `build_badge` does
  (`RFBadgeCommon`/`RFBadgeVerify` around `Solution`); `lake build verify` 31 s (4 cores). VM
  fixed-key stream of the new prover (`det-vm-B0`, N8/N2/N4 + re-runs): **6/6 accepted, 6/6 canaries
  rejected**; control: the pre-B0 prover's outputs (`det-vm-SE13a`, accepted by their own native
  `acc`) are **rejected** by B0's V (2/2). Runners (outputs kept by `P2T13_KEEP`, checked by this
  `verify`): run 40845544755 (7763) and 40845523456 (9V45): **17/17 accepted, 17/17 canaries
  rejected** each (det-1, det-3 with re-runs, the 8 outputs of a random-key stream); V 0.22–0.37 s
  (VM).
- Probes 13f/13g (base = version e on S-E13a's layout, new = f on B0's): `prover.s` `1b84a5f1…`
  rebuilt byte for byte; KATs equal the VM's; fixed-key streams identical; 44/44 accepted, 44/44
  canaries rejected. **Node prove time does not change measurably** (7763, run 40845544755): N2
  2.32–2.39 → 2.31–2.43 s, N4 4.36–4.43 → 4.33–4.37, N8 5.11–5.12 → 5.05–5.08; E2/E4 −2 … −6 %; mean
  step + overhead 11.21 → 11.16 s (`project-B0.txt`). `cargo test --release` 54 passed, 1 ignored
  (`cargo-test-3.txt`); source rule 371 files, 0 findings. Branches deleted.
