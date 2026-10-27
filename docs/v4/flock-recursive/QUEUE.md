# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.5 (`f411b1e`). `FR.lean` imports S-A, S-C, S-D,
S-H1 and S-0; the combined `FR` builds (2,237 jobs).

## Running

- S-0 fix pass against rev 3.5: `FRVIRFinals` (typed `Finals`; finZ/Lc/Sh/Lr proved), context lemmas
  + `exec_skeleton` (M3), J_z = 5, link families, `nMax`, the `MerkleEnc` instance, minors.
- S-E2 node circuit: compile_sound (FR-R3′ kill test: ≤ 1,000 lines), compile_mux_sound, WOTS,
  hashStmt_sound, nodeLayout's two decides (B-2), node_sound. Waits on S-0 for `gen fin`.

## Closed

S-A `8ff873c`; S-C `d81b568`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`. S-0 `40b2f81` (reviewed; fix pass running).

## Rulings

- FRVIRSpec budget: judged per shape, not ×15 phases. Re-check when the queries shape is proved.
- The phase-final checks (`fin : Finals`) go to a new module `FRVIRFinals`, owned by S-F (the
  verifier), which consumes S-C's lemma forms.

## Next (in order, as slots free)

1. P2 resume: S-0's dumps (`logs/S-0/dump/`), rev 3.4 formats, per-kind matrices, the node
   prover, the `tree`/`node` modes. Wait for the S-0 review.
3. S-F (verifier + `FRVIRFinals` + the remaining `exec_genPhase` shapes), S-G (soundness), S-H2
   (the extractor program; see the notes below), S-I (certificate), H (harness runs).

## Carried into the S-0 fix pass

- Take `nMax`/`logNMax` from `FRRS`.
- Add the real `MerkleEnc` instance (`frEnc i` from `nodeQ`/`colQ`/`parseNode`/`parseCol`/`carried`;
  a scratch version already elaborates, S-D-RESULT fix pass).

## Notes for S-H2 (from the S-H1 review, plus S-D2)

- No tape-length loop nested inside another. Each `loopT` count is loaded by `input`
  immediately before its loop.
- Query lengths as `|q| >> 3` plus `(|q| & 7 ≠ 0)`; never `(|q| + 7)/8`.
- The decoder: a butterfly inverse NTT (O(ℓ·2^ℓ)), proved equal to S-D2's `coeffsAt` spec, using
  `decode_row_D` (agreement on 2^ℓ positions decodes to the message).

## Kernel-time total (sequential, VM)

S-A 15 s, S-C ≈ 22 s, S-D ≈ 4 s, S-E1 7 s, S-H1 27 s, S-0 ≈ 12 s: about 87 s.

## Deferred

- X128, the 128-bit profile memo (the user's optional side question).
