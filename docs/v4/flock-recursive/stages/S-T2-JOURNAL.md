# S-T2 journal (verifier time: the 4.1 fast path of `rsWeight`)

2026-10-28. Build tree `logs/fr-build-T2` (copy of `fr-build-SE12d`, against `logs/org20`; MINE =
`FRKindWeight FRVerifierImplOps FRKindWeight4 FRVerifierImplOps4`). Logs in `logs/T2/`.

- Read TRACK-RULES, S-E12d §4, S-T1, `FRKindWeight`, `FRVerifierImplOps`, `FRNodeKinds4`,
  `FRVerifierImplNode4`. Finding: no 4.1 `rsWeight` spec exists; `implN4` inherits `base ν`'s
  `rsWeight` (3.x `rsWeightF`, 3.x layout, fast path gated on 23 coordinates).
- Key count probe (scratch, `lake env lean --run`): kind-change endpoints 89/95/106, distinct dyadic
  blocks 113/115/135 (N2/N4/N8), without patterns. So no pattern items: plain interval endpoints.
- `FRKindWeight4` (spec `kwS4` over `kf4`, endpoint form via `layout_contig`, skeleton, `kwS4_eq`,
  `kwS4_fast`, controls): green after 2 fix rounds (char-2 `linear_combination` coefficient,
  `contig_sum`'s `add_eq_left`, `kwS4_cube` orientation).
- `FRVerifierImplOps4` (`rsWeightS4`, `rsWeightF4`, `wEvalKF4`, `wEvalKC4`, `rsWeightF4_meets`,
  `withRS4_meets`): green after one fix (`Fin` binder types); dropped a fragile HEq control.
- Probe `VTime4`: modes `t2` (implN4 with `withRS4`) and `rsw` (per-kind bench and cross-checks).
- Measurements, checks, profiles: see the RESULT.
