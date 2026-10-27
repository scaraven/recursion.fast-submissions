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
