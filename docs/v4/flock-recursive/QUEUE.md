# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.9 (`757dfa8`). `FR.lean` imports S-A, S-C, S-D,
S-H1 and S-0; the combined `FR` builds (2,237 jobs).

## Running

- S-0: FRVIRSpec's last sorrys (exec_posOps, the queries case, genPhase_ctx) + rev 3.9 ops; re-dump.
- S-G: FRLog, FRSoundnessDefs/Step/Ligerito/Final, FRKState, finP/finPf, the lagV bridge.
- P2: adopt 3.8–3.9, KAT against the dump, re-time on a 7763 (does skip-c recover the link?), node prover.

## Waiting

- S-E2 rest: H-side assembly (SlotHolds imports and foreign flags, SigOk, format facts), W-kind
  children, node_complete/nodeWitness, templated evalM/evalL (T_V). F-3″: blueprint §4.3 double-counts
  the 8 stmt equalities (16 rows).
- S-F rest: the concrete OpImpl (needs S-C's computable twins of the 3.9 ops).
- S-H2: the extractor program (see the notes below).
- S-I: certificate assembly, Solution.lean, claim.json; H: GitHub harness runs.

## Closed

S-A `8ff873c`; S-C `ebac8c2`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 `e3eefae` (3 sorrys left); S-E2 `cf2f7b3` (partial); S-F `e4b2c1d` (OpImpl pending).

## Rulings

- FRVIRSpec budget: judged per shape, not ×15 phases. Re-check when the queries shape is proved.
- The phase-final checks (`fin : Finals`) go to a new module `FRVIRFinals`, owned by S-F (the
  verifier), which consumes S-C's lemma forms.

## Next (in order, as slots free)

1. S-G (soundness), S-H2
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
