# INT-2 journal: revision 3.13 across the tracks

- 2026-10-28. Base HEAD `9c1ee16` (BLUEPRINT revision 3.13). Build tree `logs/fr-build-INT2/`
  (copied from INT-1's, `snap.sh`: HEAD's sources, this pass's modules symlinked). Baseline
  `lake build FR` green (2,319 jobs, 77 s; `logs/INT-2/build-FR-0.log`).
- Decisions while reading:
  - E4end (A.4 18′, 16 B, field E) is bound: `finE` (v) asserts its value equals RS claim 4's
    `α₄` (A.9 lists no binder for it; an unread message would be a free field).
  - Fields renumbered so the body follows the item order (A.3: 9, 9′ before 8): `fE = 9`,
    `fEEnd = 10`, `fRS0 = 11`.
  - `finLr` exports `[v_L, r_Lr]` with `r_Lr` Lr2's final point (the row point of `evalL`, as
    `r_{E2}` is `evalM`'s); `finE` reads them from `fi.ex[4]` (run order: RS, Z, Lc, Sh, Lr).
  - `pfPts` point 6 becomes E's `r′` (`eSrc`); point 17 and `lrSrc`/`lrHi` are removed (17 points).
- S-0: phase table (Lr4 out, E before RS, E4end), fields renumbered, counts 8,891 / 468;
  `finLr` exports `[v_L, r_Lr]`; `queries_gen` 8,891, `fsQ_gen` 468. FRVIRFinals green.
- S-F: `finRS` 4 claims (`rsTail` gains an `addF` so `keep` acts on a fresh register),
  `exec_finRS` re-proved; `finE` (iii) `κ_E³ v_L`, (iv) `(W_M + κ_E³ W_L)·α₄`, (v) E4end bound;
  `flag_finE` (relE shaped as the op order's `&&` nesting); `finE_evalL_point`. Green.
- S-G: `pfPts` point 6 = `eSrc`, 17 points, `rsPtIx .N30 = [1,3,5,6]`; `lrSrc`/`lrHi`/`lrHi_eq`
  deleted. `flag_finPf` re-proved by the 18 → 17 edits only. Green.
- **Found: the stream is no longer a multiple of 64** (1,481,328 ≡ 48 mod 64), which breaks
  `stream_padded` (S-G1e: the node needs no padding claim). Chosen: E4end absorbs
  `f̂(r′) ‖ 0^16` (32 B), the zero half asserted in `finE`; stream 1,481,344 = 64 · 23,146
  (compressions unchanged at the blueprint's 23,146), piSize 797,904 (+16 over the blueprint).
  The alternative (one padding cell per slot as a B′ point claim) touches S-E3's `pubCells`,
  S-G's `pfCells`/`truthBN` and the prover; left to the orchestrator.
- Soundness positions: `fsRanges_eq`, `fsStarts_eq`, `capPos_eq`, P1 starts, `pfStart_eq`,
  TailD's 468 checks, `phOf_examples`, `e2_phase` (221), `streamTarget 1481344`, chainN 23,146
  (`FRNodeLayout`, `hEnd` 47,322). `rs0_before_e4` replaced by `e4_before_rs0`;
  `evalL_short_zero` kept as the negative control; `lr_unit_pos`'s last conjunct is E1's squeeze.
- FRX in FR's closure (FRXChainFlock, FRXLog, FRXLogSpec, FRXLookup, FRXReadDefs) patched in the
  build tree only (`logs/fr-build-INT2/mkpriv.sh`). `lake build FR` green (2,319 jobs).
- Checks: axioms (32 theorems, standard three only), source rule (115 files, 0 findings),
  re-dump (ops 105,828, asks = items = 8,891, no PENDING), sequential profiles. RESULT written.
- HEAD moved to `8b539c3` during the pass (S-H2 part 16, S-E5 `9dbab71` which took this pass's
  FRNodeLayout lines, queue). Re-snapshot, `lake build FR` green (2,320 jobs, `build-FR-7.log`);
  re-dump identical.
