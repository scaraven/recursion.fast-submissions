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
