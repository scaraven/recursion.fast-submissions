# E1 journal (the prover port to revision 4.4.1, branch `v4/rev44`)

Track E1, 2026-10-29. Worktree `recursion.fast-submissions-rev44` at HEAD `e464756` (A1′). Prover
`submissions/flock-recursive/prover/` (P2⁹'s crate at start: `prover.s` `1b84a5f1…`). Logs `logs/E1/`.
Build tree `logs/E1/fr-build` (a copy of `fr-build-A1`, every source a HEAD copy: no symlinks into
the worktree, so B4/PORT/RSV-S edits do not leak in).

## Log

- 17:00 Read QUEUE, P2-RESULT §17–21, PACK-4.4 §11, A2pp, B2p, B2pp, A1p, RSV-V2, B5 (summaries,
  "For P2"). Copied `fr-build-A1` → `logs/E1/fr-build`, de-symlinked. New probe `probe/E1Verify.lean`
  (badge `parseSigned` + `accF` with `V := FR.Sub4.V4F`, `qV := 36000`; `--plan` prints `inR` and
  `(lkArr κ).all (·.eok)`; one warm untimed check then the timed one). Building `e1verify`,
  `irdumpa2pp`, `nodedump4`, `planform4` (CPUs 0–3).

## Format at HEAD (from `logs/RSV2/dump/summary.txt`, `items.json`; HEAD's seq4 = RSV-V2's)

- |π| 876,304; fields (20) sizes `[48,128,2048,1248,32,800,1344,816,1008,2336,112,8192,2112,672,
  49152,4096,487504,237632,27872,49152]`; stream 1,551,104 = 64·24,236 per segment; items 8,783;
  FS items 486; last items: Pf, CapD absorb 27,872, CapZeta sq, CapChk absorb 49,152, CapChkZ sq.
- Level 4 cap depth 8 (`Seq.cap4`), siblings 4/3/2 at m = 32/31/30.
- Aggregate: spacer `(spacerQ, H(spacerQ))`, `spacerQ = "FRABS000" ‖ 0^32 ‖ 0^49` (89 B) between
  segments; stride 64·24,238; `aggB k = 64·(24,238k − 2)`.
- 17:05 HEAD dumps (`logs/E1/dump.sh`): IR dumps `logs/E1/dump` (ops-*, items.json byte-equal to RSV2's),
  node dump `logs/E1/nodedump` (nodedump4, planform4, protodump). planform_kat.py: KAT PASS.
- 17:08 Segment format (params: 20 fields, |π| 876,304, CAP_LOG[4] 8, STAR_SIB[4] 4, items 8,783/486;
  items.rs: CapD/CapZeta/CapChk/CapChkZ; ligerito.rs: `cap_check` (D = each read's cap entry, ζ,
  A = Σ ζ^r per entry, z) and the native verifier's static reads + (I)/(II); leaf.rs: Lrend 1,008
  / Eend 112 zeros; agg.rs/ir.rs: spacer `"FRABS000" ‖ 0^81` between segments).
  cargo tests params/items/kat/agg/ir/leaf: 12 passed (ir_kat_l30, ir_agg_l30 on the HEAD dump).
- 17:10 Service run (`logs/E1/r1`): prove-leaf 32 (n 200,003), 30 (n 3), prove-agg 400,001 (k = 2,
  |tr| 17,567): native acc + dumped Lean programs accept. **Lean V (`e1verify`) accepts agg2.bin**
  (479 ms), canary rejected; bare segment files rejected by `V4with` (kind `.bad`, as designed).
- 17:20 Node: layout (SEG_B, C_LEN, spacer/stride, agg_b with spacers, h_used L1), agg_in's trace split
  (k·8,783 + k − 1), `agg_stream` (phantom constants for inactive sub-slots: spacer elements 0–5,
  wfSeg elements, seed element bytes 1–15), spC L cells (spacer bits) replacing S-E13b's element-7
  bits. nodeblob from `logs/E1/nodedump` (11,583,200 B: register forms grew to 27.7 MB per prototype,
  the cap check's running sums), plan-kat PASS. node-kat N8 (k = 1): **0 failing rows of every kind**.
- 17:35 Reserve (RSV2): IR `evalM` on a 32-entry point = `nodeops::eval_mx` (Σ_k ⟨s_k, M̃_κk⟩ at each
  kind's coordinates), NodeCtx with all three kind tables; nodeprove: fLrEnd = vl ‖ 60 child-claim
  values (slot 0's `rsvRel` cells), E2 extra pair (η·eq(p_x), D + X), fEEnd = vm ‖ m̂* ‖ 0^48, E4 extra
  pair (κ_E⁴·eq(p_y), G), B′ 60 cells at κ′^{11…70}.
  N8 (k = 1) and **N2 over that N8**: accepted by the dumped programs and by **the Lean V** (`e1verify`
  361 / 332 ms VM), canaries rejected; plan self-check `inR true lk2/lk4/lk8.eok true`.
  Cost (VM, N2 over N8): e2 2.29 s, e4 4.27 s (the N8 kind table's matvec/scatter): to optimise.
- 17:40 Chain (`logs/E1/r2/chain.txt`, node-kat, Lean V on each): N4←N2 (k 2), N2←N4 (k 1), N2←N2
  (k 2), N4←N2 (k 4), N4←N4 (k 3), N4←N4 (k 1), N8 (k 4 + 4): every one accepted by `e1verify`,
  canaries rejected, 0 failing rows.
- 17:45 Speed of the reserve: factorized (slot `v` of any kind = `eq(high, v)·(prototype pass)`):
  `proto_matvec` at `eq(p_y[<20])` (E2's child rows), `proto_scatter` at `eq(r_E2[<20])` (E4: the own
  `W_M` and the child term, shared), landed directly into the parent's space (fold / duplicate);
  `prove_pairs_support` (several sparse pairs, the eq side in closed form `Q::Eq`). π unchanged at
  each change (N2←N8 `3e0852b3…`, N4 full support `49bb344b…`). VM N2←N8: e2 2.29 → 0.78 s, e4
  4.27 → 1.73 s (loaded VM).
- 17:50 Register forms > 256 terms dropped in `Proto::load` (`LONG_FORM`; only single-cell forms are
  written, the rest only checked): blob 11.05 MB (raw 44.9 MB), image 681 → (re-measure) MB.
  cargo test: 53 passed, 1 failed (`layout_figures`: old literals; updated to Lean's hEnd/hUsed).
- 18:20 **Stream through rf-oracle** (`logs/E1/st1`, `logs/E1/stream.sh` = p2t13's + `e1verify` on every
  output; `prover setup` `logs/E1/s1/setup` 144 s VM 32 threads): chains 2^20 + 2^20 (first, N8 with
  k = 4 + 4: the full-length first step), 131,072 (N2), 300,001 (N2, k 2), 786,432 (N4, k 3), 2^20 (N4,
  k 4), 131,072 (N2), 600,001 (N4, k 3), 262,144 (N2): **8/8 accepted by the rev44 Lean V**, 8/8
  canaries rejected, native acc the same. Transitions N8→N2, N2→N2, N2→N4, N4→N4, N4→N2.
  VM timings meaningless for the runner (portable tier: no pclmulqdq), 8 cores loaded.
- 18:30 Orchestrator: PORT committed (c4eca2b), B4 committed (7537acd). Build tree re-snapshotted at
  HEAD 7537acd (scaffold stubs re-applied), probes rebuilt. Re-dump (`logs/E1/dump`, `logs/E1/nodedump`;
  the e464756 ones kept as `*-e464756`): IR dumps, protos, plan forms byte-equal; only node-N*.txt
  (B4's `chkRows` in slot 1's node rows) changed. nodeblob 11,367,584 B.
- 18:35 B4's cells: **table-driven link-row solver** `node::solve_aux` over `AUX_L` (offset ranges of an
  aggregate child's L stride; B4's 12,288–14,487): one-unknown linear rows (try_row's rule) and packing
  rows (`A·B = C`, unknowns in `B` with distinct one-bit coefficients ⇒ bits of the known rest). N8 k=1:
  4,014 cells solved, 6 left zero (the inactive sub-slots' inverses), **0 failing rows**.
  eval_mx shares the two prototype sums across every slot and kind (test `eval_mx_matches_ref`), the
  multi-pair sumcheck uses per-pair live chunks (test `pairs_support_same_messages`); π unchanged.
- 18:45 Decoder KAT (orchestrator): `decF04` cannot run (≈ 2.7·10^13 cost); probe `E1Dec` builds its
  proved postcondition (HeapW, Inv, memX4) from the prover's `f` (`node-kat --dkat DIR`) and runs
  `outIR4 κ` under `semXIR`, compared with `witWordsF (.node c₀ c₁ p₀ p₁)` of the real children.
- 19:00 Decoder KAT (`logs/E1/dkat/dkat.txt`): outIR4 EQUAL on N8 k1 (608,071 words), N8 k4+4
  (2,428,729), N4←N2 k4 (1,518,394), N2←N4 k2 (911,508); canary (one f bit) MISMATCH (2 words).
- 19:05 Chain at 7537acd (`logs/E1/r4/chain.txt`): 10 nodes, all accepted by the Lean V at 7537acd.
  prover.s determinism (`logs/E1/asm`): two clean builds identical, `aac53ced…`, 22,984,542 B.
  cargo test 56 passed; source rule 422 files, 0 findings. `prover setup` 167 s VM (12 cores), 265 MB.
- 19:40 A/B stream (VM, 4 cores 24-27, P2's chain list; `logs/E1/ab2`): new stream 8/8 accepted by the
  Lean V. Scaled per step by the base's 7763/VM ratios (`scale.py`, base 7763 = run 40845544755):
  node parts N2 3.30, N4 5.62, N8 7.55 s; aggregates unchanged (VM ratio 0.995, noisy); start-up
  0.66 s. project.py (M = 96, stream_s 1,920): mean step + overhead 11.63 s, worst first 44.0 s, P̄
  8.51 s. VM noise is large (unchanged N8 phases +30 % in the new run): a node-level A/B follows.
- 20:20 Node-level A/B (`logs/E1/nab`, 4 VM cores, 2 rounds): Δ node prove on the 7763 (phase ratios of the
  base) N8 −0.22, N2←N8 +0.39, N2 full +0.67, N4 full +0.86 s. project.py: mean step + overhead 11.92 s,
  worst first 41.9 s (step_s 60), stream mean 1,150 / max 1,311 s of 1,920, P̄ 8.77 s.
  Stream at 7537acd with the asm binary (`logs/E1/st2`): full-length first step N8, N4, N2: Lean V accept.
- Orchestrator: priority = acceptance + caps (met: 1.43× step_s on the worst first step, 1.46× stream_s on
  the max draw, start-up ≈ 0.66 s); hard-coded format points listed in RESULT §5.1 for R1/ASK-P.
  (A wait loop with `pgrep -f` matched itself and hung; the orchestrator killed it. Lesson noted.)
