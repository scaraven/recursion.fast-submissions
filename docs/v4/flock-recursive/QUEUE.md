# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-27. Blueprint at revision 3.3 (`1c1e27c`).

## Running

- S-0, interfaces (`FRTranscriptDefs`, `FRFormat`, `FRVIR`, `FRVIRSpec`, dump tools), against
  revision 3.3.
- S-E1 golf.
- S-C review (by the engineering reviewer; the implementer does fix + golf afterwards).

## Done, awaiting closure

| Stage | Next step | Carried items |
|---|---|---|
| S-C (piop core) | review running; then the implementer's fix + golf | rev 3.3: `FRSpartan` to per-kind masked rows (`A = Σ Ind_kind ⊗ A₀^kind`, `Ê_w`); open Q2 (which Z2 form `gen` uses), Q3 (the d slot at 520…775 is not 256-aligned, and the θ count is 8 or 10); `FR.lean` imports `FRMLEControls`; `FRPubTarget` unowned |
| S-D (pcs, committed `1705d97`) | fix pass: S-D-m2/m3/m5 | S-D2 (`coeffs_of_values`, `coeffs_spec`, `interpF`, `encF` in `FRRSEval`) |
| S-H1 (DSL, committed before review) | review; then the fix pass: drop `invF_kat` (≈ 10 s of kernel time), keep `regs = 256` until S-H2 needs more | blueprint §6.3: 57 steps per F product (not 86); §6.4: the constructor list, cost and memory layout |
| S-E1 (BLAKE2s, leaf) | fix pass after golf: the per-kind targets of rev 3.3 (A.6 table), S-E1-m1…m5; then commit | — |

## Decisions pending

- **E2 batching** (P2-RESULT §6): put the node's E2 claim into the Ligerito weight, the same
  treatment ring switching gets, instead of its own sumcheck. Measured: the stream link drops from
  2.80 s to 2.66 s on the 7763. This is sound only if E2 is a linear claim on `f`. Ask the crypto
  reviewer (a short check) before P2 resumes.

Kernel-time running total (VM, sequential): S-A 15 s, S-C 22 s, S-D ≈ 4 s, S-E1 28 s, S-H1 43 s, about 112 s. Watch it against the 600 s runner cap.

## Next stages (in order, as slots free)

1. S-E2: WOTS, `compile`/`compileMux`/`evalM`, node layout, `node_sound` (needs S-0).
2. P2 resume: rev 3.3 formats, per-kind matrices, the node prover, `tree`/`node` modes (needs S-0's dumps).
3. S-F verifier; S-G soundness; S-H2 extractor program; S-I certificate; H harness runs.

## Deferred

- X128: the 128-bit profile memo (the user's optional side question).
