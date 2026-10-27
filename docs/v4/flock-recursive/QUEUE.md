# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.7 (`9bd0a82`). `FR.lean` imports S-A, S-C, S-D,
S-H1 and S-0; the combined `FR` builds (2,237 jobs).

## Running

- P2: rev 3.7 proof layout + KATs against logs/S-0/dump, leaf re-timed, real node prover, tree/node modes.
- S-F: `FRVerifier` (V, accWith, acc_eq), S-F finals (finRS, finE, finB′), the OpImpl instance.
- S-0: prove `exec_genPhase` and `genPhase_ctx` (FRVIRSpec sorry-free; FR-R10 per shape).

## Waiting

- S-E2 rest: `node_sound` over the packed witness (needs S-F's accWith), the H-side assembly,
  `node_complete`/`nodeWitness`, templated evalM/evalL (T_V: plain evalM ≈ 2^20 products), linking
  the compiled row count to `mRowModel`. F-3″: §4.3 sums to 531,610 (blueprint text).

## Closed

S-A `8ff873c`; S-C `d81b568`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 `afc2928` (two stated lemmas left); S-E2 partial `b1579e9`. FR builds (2,260 jobs).

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
