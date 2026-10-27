# `flock-recursive`: a recursive Flock-class entry (in progress)

A Flock-class batch-R1CS argument over GF(2) with a Ligerito commitment over F = GF(2^128),
fold challenges in K = GF(2^256), BLAKE2s everywhere, and recursive SROM nodes. The normative
design is `docs/v4/flock-recursive/BLUEPRINT.md` (repository root); the stage records are in
`docs/v4/flock-recursive/stages/`.

## Status (2026-10-27)

- **Stage S-A (fields)**: `lean/FRFieldBase*.lean` (GF(2^64), copied from `spartan-srom`),
  `lean/FRField128.lean` (F = BF64[y]/(y^2 + y + x^63)), `lean/FRField256.lean`
  (K = F[u]/(u^2 + u + x^63 y)), `lean/FRFieldControls.lean`; `lean/FR.lean` imports all.
- Not yet: `Solution.lean`, the verifier, the prover, the certificate. `claim.json` holds the
  blueprint's values (§7) as a placeholder until stage S-I.
