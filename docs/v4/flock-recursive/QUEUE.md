# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.4 (`2fa83b1`). `FR.lean` imports S-A, S-C, S-D,
S-H1 and S-0; the combined `FR` builds (2,237 jobs).

## Running

- S-E1 fix pass: the per-kind targets of A.6, stmt block lemmas, a dump function.
- S-0 review (engineering reviewer).
- S-D fix pass + S-D2 (`coeffs_of_values`, `coeffs_spec`, `interpF`, `encF`).

## Closed

S-A `8ff873c`; S-C `d81b568`; S-H1 `40b2f81`. S-D `1705d97` and S-E1 `fdf78fa` are golfed, with
fix passes running. S-0 `40b2f81` is in review.

## Rulings

- FRVIRSpec budget: judged per shape, not ×15 phases. Re-check when the queries shape is proved.
- The phase-final checks (`fin : Finals`) go to a new module `FRVIRFinals`, owned by S-F (the
  verifier), which consumes S-C's lemma forms.

## Next (in order, as slots free)

1. P2 resume: S-0's dumps (`logs/S-0/dump/`), rev 3.4 formats, per-kind matrices, the node
   prover, the `tree`/`node` modes. Wait for the S-0 review.
2. S-E2: WOTS, `compile`/`compileMux`/`evalM`, node layout, `node_sound`. Needs the S-E1 fix pass
   and the S-0 review.
3. S-F (verifier + `FRVIRFinals` + the remaining `exec_genPhase` shapes), S-G (soundness), S-H2
   (the extractor program; see the notes below), S-I (certificate), H (harness runs).

## Notes for S-H2 (from the S-H1 review)

- No tape-length loop nested inside another. Each `loopT` count is loaded by `input`
  immediately before its loop.
- Query lengths as `|q| >> 3` plus `(|q| & 7 ≠ 0)`; never `(|q| + 7)/8`.

## Kernel-time total (sequential, VM)

S-A 15 s, S-C ≈ 22 s, S-D ≈ 4 s, S-E1 7 s, S-H1 27 s, S-0 ≈ 12 s: about 87 s.

## Deferred

- X128, the 128-bit profile memo (the user's optional side question).
