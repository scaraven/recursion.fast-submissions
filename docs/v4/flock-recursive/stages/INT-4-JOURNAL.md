# INT-4 JOURNAL: the `finZ` c-claim and revision 3.15's `τ` (2026-10-28)

HEAD `b239c92`. Build tree `logs/fr-build-INT4` (copied from `fr-build-INT3`; `snap.sh` with
`MINE` = this pass's modules as worktree symlinks). Logs in `logs/INT-4/`.

## Baseline

- `lake build FR` at HEAD in the INT-4 tree: green, 2,379 jobs (`build-head.log`).

## Item 1: `finZ`

- `finZ`'s last op is now `.assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK`. Z2's
  outputs are `[λ, P^{ab}*(λ), P^z*(λ)]` (`gen`'s univariate round, `rec_ … [b + 3, b + 133,
  b + 134]`), so index 2 is `P^z*(λ)` for every kind; `zhat[0]` is `finRS`'s claim-0 value
  (`claimOps 0`), computed for every kind (the leaf drops only claim 3). Hence `allK`.
- `assertEq` appends no register, so `finZ`'s register count and every later register number are
  unchanged.
- There was no `relZ` and no `exec_finZ` (the latter only in `FRVIRSpec`'s header). `flag_finZ`
  stated its relation inline; it now states `relZ` (two conjuncts) and its `hin` gains the two
  registers. Nothing outside `FRVIRFinals` used `flag_finZ`.
- Controls: `relZ_iff`, `finZ_rejects` (−), `finZ_accepts` (+).

## Item 2: `τ` of 18 coordinates

- Observation: `shiftTarget`'s `eq(τ, last)` with a zero-padded `τ` and `last = 1^18` is `0` for
  P30, whose last block is `1^16 ‖ 00`. Kind-free fix: `bnd` carries the kind's last block
  (`bnd[4 … 21] = 1^(m−14) ‖ 0^(32−m)`, constant registers), the spec is `eq(τ, last)` on 18
  coordinates (`shiftTargetAt`), and `shiftTargetS_pad` gives `FRShift.shiftTarget` on `m − 14`
  coordinates (`eq_pad_zero`). The op's signature is unchanged; `Meets`' precondition is
  `bnd.size = 22`.
- `finSh`: `bndOps` gains a `1` register (8 registers, `b = b₀ + 8`); `τ`, `r_blk` by `padB`
  (zero register `b₀ + 4`); `E₀`'s point `0^18`. `linkWAll`'s packed points are unchanged (node
  only, `τ`'s first 16 = `m − 14`).
- `shiftEq`, `slotW`, `shiftMask`: `Meets` unchanged. `shiftEqS_pad`, `eqPoint_pad`,
  `shiftMaskS_pad` (+ `eqPoint_eq`, `eqPoint_shiftPair`). `slotW`'s operands are `θ` and `r_pos`
  (10 coordinates each): nothing to pad.

## Builds and checks

- Module builds: `FRShift` (two fixes: the `[] []` case of `shiftPair_pad`), `FRVerifierImplOps`
  (`shiftTargetS_pad`: the `Fin 18` products are rewritten through beta-reduced
  `Fin.prod_univ_eq_prod_range` instances, `lastBlk` kept folded), `FRVIRFinals` (`flag_finSh`
  timed out until `padB`, `List.map_append`, `List.map_replicate` joined its `simp only`).
- `lake build FR`: green, 2,379 jobs, no repair needed in S-G, L-circ or FRX modules
  (`build-FR-1.log`; after a lint cleanup `build-FR-2.log`).
- Axioms (`axioms.log`), source rule (157 files, 0 findings), re-dump (`redump.log`: ops 105,837
  → 105,839, items.json byte-identical to INT-3's, piSize 797,904), V (HEAD binary and INT-4 on
  core 27, the VM is noisy; per-op profile: the changed ops cost < 0.6 ms together), sequential
  profiles of the five changed modules.
