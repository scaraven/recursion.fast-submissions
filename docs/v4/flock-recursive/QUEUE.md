# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-28. Blueprint at revision 3.13 (§10 changes 1–20). FR builds as a whole (2,320 jobs at S-E5).

## Running

- S-CN: the node `targetS`/`linkW` specs (S-C part) plus `targetSNodeI`/`linkWI` and `_meets` (S-F2 part), in new modules; wiring into `implC` after INT-2.
- P2: the node prover driven by the dump (`logs/S-E5/nodedump/`), the mirror writes, tree/node modes, the stream-link measurement.

## Waiting

- **After INT-2:** re-verify `lake build FR`, commit; wire S-E5's `evalLT` into `implC` (+≈ 4.5 ms); re-measure V; S-H2h with the moved positions (FRX constants: nRep, chTab/fsMsgs, capW0/capOffL, piSize tape facts).
- **After S-CN:** S-E templates `tplTargetSNode` (≈ 10k rows) and `tplLinkW` (≈ 2,500 rows per family); S-G the node S truth (`ShHolds` + 7 terms), Z1/Z2 tables over the node `targetS`; re-dump for P2.
- ~~S-E5: T_V, the skeleton~~ (closed `9dbab71`: V 204.9 ms VM best). Measured: V without evalM 150 ms VM; evalM 545 ms (flat evaluator), of which ≈ 440 ms is the untemplated skeleton (≈ 120k rows per slot: Merkle steps, finP4's Horner). To do: block templates by placing compile's rows into aligned regions (cell renaming preserves soundness; plan-time key check; roundtrip lemma; S-E4-RESULT §6); aligned cell allocation; F-9 (materialise `cur` in Merkle steps, ≈ +15k rows per slot); the import classes; finE's evalM with κ_E (Ã + κB̃ + κ²C̃). Target: V + evalM ≤ 230 ms VM.

- **P2 node prover**: needs S-E3's node dump (logs/S-E3/nodedump/, which now has template groups and the WOTS order) and the F-7 outcome (it may change the node circuit). Leaf proofs are dump-exact (P2 §11).
- **S-E (the H-side assembly of node_sound)**: the pack map from H trace/stream cells to the M imports. This covers the r17/r18 bindings (S-E3 §9), `input w` as an alias of the public seed cells (S-E3's proposal: no rows, `PubCells` binds vk/cᵢ), SigOk and the format facts, W-kind children, node_complete; the remaining templates (tensorW, rsWeight, walkA/B, kindInd, rowW, shiftTarget, the child's evalM/evalMK/evalL replay); F-8 (track kindInd/packFK); per-generator row counts for RowsFit (S-G's truthE_iff hypothesis; false for an arbitrary fin).
- S-G2: ligerito_final, final (with fsQ_gen, ChainStab), FinalLaw; then kstate.
- S-I: certificate assembly (Solution.lean, claim.json at B-10 with fuel_per_word 8,192, the εR arithmetic, axioms, the 600 s build/kernel check). H: GitHub harness runs.
- Golf: FRVIRFinalsSG (1,526 lines, budget 400) and the large L-ext modules.

## Closed

S-A `8ff873c`; S-C `ebac8c2`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 `47158b1`; S-E2/S-E3 `8447c50`; S-F `c8e1869`; S-F2 `8f22b86`; S-G through `ac43569`; S-H2 through `11fb3a5`; INT-1 `5fc7d3b`; S-E5 `9dbab71`. FR builds as a whole.

## Rulings

- **INT-2 decisions, ratified 2026-10-28** (to enter the blueprint as change 21, batched with S-CN's findings):
  (1) E4end absorbs 32 B (`f̂(r′)` ‖ 16 zero bytes), keeping the stream at 64 · 23,146 so that `stream_padded`
  holds with no padding cell; piSize **797,904** (1.31×), stream counter 1,481,344.
  (2) `finE` (v) binds the E4end message (value = `α₄`, the extra half zero) for every kind.
  (3) `r_Lr` is Lr2's final point (the lincheck's row point is the zerocheck's final point, as for `r_E2`).
  Still to fix in the blueprint: A.9's `finB′` row (`κ′ v_E`); `mRowModel`'s claim-5 row (11,400 rows, an over-count).

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
