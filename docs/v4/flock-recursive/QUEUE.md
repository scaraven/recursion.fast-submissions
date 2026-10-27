# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.3 (`1c1e27c`).

## Running

- S-0, interfaces (`FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec`, dump tools), against
  revision 3.3.
- S-E1 golf.
- S-H1 fix pass + golf (m2, m4, m5).

## Done, awaiting closure

| Stage | Next step | Carried items |
|---|---|---|
| S-D (pcs, committed `1705d97`) | fix pass: S-D-m2/m3/m5 | S-D2 (`coeffs_of_values`, `coeffs_spec`, `interpF`, `encF` in `FRRSEval`) |
| S-E1 (BLAKE2s, leaf) | fix pass after golf: the per-kind targets of rev 3.3 (A.6 table), S-E1-m1…m5; then commit | — |

## Notes for S-H2 (the extractor program), from the S-H1 review

- m1: no tape-length loop nested inside another (the cost model does not amortise). Each `loopT`
  count is loaded by `input` from a tape length field immediately before its loop.
- m3: compute query lengths as `|q| >> 3` plus `(|q| & 7 ≠ 0)`, never `(|q| + 7)/8`, which wraps
  in 64-bit words.
- m6: blueprint §6.4 should record the delivered DSL (largely done in revision 3.4).

## Closed

S-A `8ff873c`; S-C `d81b568`; S-D `1705d97` (fix pass pending); FR.lean imports them.

## Decisions pending

- none. E2 batching was adopted in revision 3.4.

Kernel-time running total (VM, sequential): S-A 15 s, S-C 22 s, S-D ≈ 4 s, S-E1 28 s, S-H1 43 s, about 112 s. Watch it against the 600 s runner cap.

## Next stages (in order, as slots free)

1. S-E2: WOTS, `compile`/`compileMux`/`evalM`, node layout, `node_sound` (needs S-0).
2. P2 resume: rev 3.3 formats, per-kind matrices, the node prover, `tree`/`node` modes (needs S-0's dumps).
3. S-F verifier; S-G soundness; S-H2 extractor program; S-I certificate; H harness runs.

## Deferred

- X128: the 128-bit profile memo (the user's optional side question).
