# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.10 (`e1ad02c`). `FR.lean` imports S-A, S-C, S-D,
S-H1 and S-0; the combined `FR` builds (2,237 jobs).

## Running

- P2: native acc vs the full dump (logs/S-G/dump), node prover, tree/node modes, 7763 stream link.
- S-0: T_V blockers: bytesAt without the π copy (283 s → ≈ 180 ms), Kind argument for targetS/slotW/linkW, κ_s for shiftTarget.
- S-H2d: node decoding (butterfly machine program, agreement scan, levels as needed, decodeWit output, 'N' case of ext_good_tape).

## Waiting

- **T_V (risk FR-R9; the binding item now).** The VM measures ≈ 180 ms with the bytesAt fix (S-F2), against a VM-equivalent cap of ≈ 264 ms. It must still absorb finPf (≈ 7.6 ms), the real evalL, and a **templated evalM/evalMK** (S-E2: a linear compileMux, templates, and L's row list; plain evalM over ≈ 2.4M rows takes seconds). S-C owes the node's targetS (E for all nine kinds), the linkW families, the In slot map and kindFoldWeight. Then S-F2 re-times with real proofs.

- S-G next (fresh agent from S-G-RESULT S-G1d §5–6):
  - pin the six padding cells (finB′ and finPf: the same six terms = 0);
  - the uniqueness lemma ¬far ∧ truthP2 → truthC, the weight tables W_i, the PIOP truths;
  - the per-phase dooms and Dp over phStart, the multi-squeeze bad sets, the instantiated KState.step;
  - then S-G2: ligerito_final, final (including capPi = capDig and V_W size), kstate.
  - FRVIRFinalsSG is 1,526 lines (budget 400): golf candidate.
- S-E2 rest: H-side assembly of node_sound (imports, foreign flags, SigOk, format facts), W-kind children, node_complete.
- S-I: certificate assembly (Solution.lean, claim.json at B-10, the εR arithmetic, axioms, the 600 s build/kernel check). H: GitHub harness runs.

## Rulings since revision 3.10

- The Lr point (node) is S-G's provisional choice (Lr4 challenges 7–14 plus L-base bits), checked against the prover's native verifier.
- Leaves: the extractor parses s from the header; only N30 decodes.
- final supplies capPi π e = capDig es 0 e; V_W proofs are < 2^64 bytes by V_W_sound.

## Closed

S-A `8ff873c`; S-C `ebac8c2`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 done (`81f19b2`, FRVIRSpec sorry-free); S-E2 partial `cf2f7b3`; S-F `c8e1869`; S-G through `21bc631`; S-H2 through `fd836c3`. FR builds as a whole.

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
