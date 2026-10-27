# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.3 (`1c1e27c`).

## Running

- S-0, interfaces (`FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec`, dump tools), against
  revision 3.3.
- S-H1, the extractor DSL (`FRXDsl`, `FRXField`).
- S-D golf, S-E1 golf.
- P2, winding down: write-up only, then stop.

## Done, awaiting closure

| Stage | Next step | Carried items |
|---|---|---|
| S-C (piop core) | one combined review + golf | rev 3.3: `FRSpartan` to per-kind masked rows (`A = Σ Ind_kind ⊗ A₀^kind`, `Ê_w`); open Q2 (which Z2 form `gen` uses), Q3 (the d slot at 520…775 is not 256-aligned, and the θ count is 8 or 10); `FR.lean` imports `FRMLEControls`; `FRPubTarget` unowned |
| S-D (pcs) | fix pass after golf: S-D-m2/m3/m5; then commit | S-D2 (`coeffs_of_values`, `coeffs_spec`, `interpF`, `encF` in `FRRSEval`) |
| S-E1 (BLAKE2s, leaf) | fix pass after golf: the per-kind targets of rev 3.3 (A.6 table), S-E1-m1…m5; then commit | — |

## Next stages (in order, as slots free)

1. S-E2: WOTS, `compile`/`compileMux`/`evalM`, node layout, `node_sound` (needs S-0).
2. P2 resume: rev 3.3 formats, per-kind matrices, the node prover, `tree`/`node` modes (needs S-0's dumps).
3. S-F verifier; S-G soundness; S-H2 extractor program; S-I certificate; H harness runs.

## Deferred

- X128: the 128-bit profile memo (the user's optional side question).
