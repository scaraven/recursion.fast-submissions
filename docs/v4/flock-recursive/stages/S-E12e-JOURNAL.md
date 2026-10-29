# S-E12e journal (track L-circ): the two 4.1 `shiftMask` templates

Base HEAD `036eb7e` (S-E12d). Build tree `logs/fr-build-SE12e` (copy of `fr-build-SE12d`, against
`logs/org20`); logs in `logs/S-E12e/`. Every lean/lake/probe command in a 16 GB scope with a timeout.

## 2026-10-28

- Read TRACK-RULES, S-E12d RESULT §8, `FRVIRTplSet`, `FRVIRTplMask`, `FRSegTarget4`,
  `FRVerifierImplNode4`, `FRVIRCompileSound`, `FRVIRTplExt`. `git log`: no S-T2 or INT-8 commit yet
  (INT-8's edits are uncommitted in the worktree; the build tree snapshots HEAD, so they are not seen).
- Design decisions (deviations from §8, with reasons):
  - **Route, not filter, picks the 4.1 key.** A `shiftMask` on `af n, af m` goes to `.shiftSeg n m`
    (segment) or `.maskN n m ks` (node) by a per-prototype route `ShR` (`tplExt4 F R`). `keys41` is
    true on both new keys (unchanged definition), so the 4.1 set covers them; the route says which.
    Reason: the node template needs the group's per-kind constants, which live downstream of
    `FRVIRTplExt`; they are carried in the key (`ks`), and the route supplies them.
  - **The node template muxes three per-kind sub-circuits** (`Σ_j sel_j · out_j`), each mirroring
    `shiftMask4I` gate for gate at its kind's constants (`prefixP`, `shP`, `eqAtR`), rather than one
    circuit with the constants' bits as selector forms. Rows ≈ 2,200 (model: N2 749, N4 714, N8 724,
    plus the mux) against ≈ 1,000; both fit one 4,096-row instance. Reason: the proof is by
    induction on `prefixP`/`shP`'s own recursion (no digit-DP lemma, no 17-vs-18 coordinate lemma
    for `N2`), and the sub-circuit is generic in its constants.
  - **Kind-indexed requirement as `RouteOk R impl κ`** (the route's key's `shiftMask`), next to
    `ImplTF F impl` (kind-free, unchanged), instead of a `KeyImplAt` over keys: `keys41` contains
    `.maskN n m ks` for every `ks`, so a per-key requirement over the whole set would be contradictory.
- `FRVIRTplCore`: `TKey.shiftSeg n m`, `TKey.maskN n m ks` (full rebuild).
- `FRVIRTplSeg` (new): `segMaskV` (copy of `shiftSegI`), pieces `isOneG`/`isOnesG` (`[x = 1]` by an
  inverse and a product: `Gate.Eqn (.inv a)` only pins `i = a⁻¹`, so `s = a·i` is an extra product),
  `facsG`, `eqAtG`; bit lemmas (`testBit_sum_bitsP`, `testBit_succ_carry`, `lt_two_pow_iff_carry`);
  `tplShiftSeg_ok`. Proof style that worked: decompose `Eqns` of a right-nested gate list, derive
  each piece's value forward (`have oX := pieceG_ev … hX; rw/simp at oX`), make per-index facts
  unconditional (`bB`, `cv` hold for every index) so `simp` rewrites under `∏` binders. Pitfalls:
  `_` offsets in a `have` statement are elaborated to unrelated values (state such facts `∀ K` and
  instantiate from the hypothesis); `congrArg _` on `List.prod` timed out at `whnf`
  (`List.foldl_ext` instead).
- `FRVIRTplMaskN` (new): `mFV`, `shPV`, `maskNV` (copies), `prodAtG`/`prefixG`/`shG` (gate-for-gate
  mirrors of `prodAt`/`prefixP`/`shP`, proofs by induction on their recursion), `blkG`/`blksG` (one
  sub-circuit per kind), `tplMaskN` (shared `t_l`, the mux `Σ_j sel_j · out_j`), `tplMaskN_ok`.
- `FRVIRCompileSound`: `ExtOkAt`, `ExtOk.at`, `extOk_iff`, `compileFromX_soundAt`,
  `compileX_soundAt`; `compileFromX_sound`/`compileX_sound` now derived (statements unchanged).
- `FRVIRTplSet`: `ShR`, `kIx`, `tplExt4`, `tplExt4_imp`, `RouteOk`, `tplExt4_okAt`, `compileTF4`,
  `compileTF4_imp`, `compileTF4_soundAt`, `layOfF4`, controls `tplExt4_ctl`, `routeOk_ctl`. Pitfall:
  `F` (the filter variable) shadows the field `F` (`(1 : FR.F)`); the node branch's
  `tplMaskN_ok` needed explicit `τ r ks j0` (an implicit-argument unification unfolded the
  template: `isDefEq` timeout).
- `FRNodeRows4`: `nodeOf`, `nodeGrp_nodeOf`, `nodeQ`, `protoR`; `protoCS` at `compileTF4`.
  `FRNodeRows4Plan`: `planData4` at `tplExt4 (protoF π) (protoR π)`.
- Probes: `LayDump4` (`layOfF4`, `keyS` new keys), `PlanM4`, `NodeDump4` (`keyStr`).
- `laydump4` (7.9 s): `.maskN 18 18 [N4, N2, N8 constants]` at prototype 0 (row 393,216, 12 cell
  bits), `.shiftSeg 36 18` at prototype 1 (row 391,168, 9 cell bits). Hint regenerated.
- **HEAD moved** during the stage: S-T2 `1ee751b`, S-CN4b `3ef2c51`, R4e `2e5b79a`. S-CN4b changed
  `shiftMask4I` (factors from a table, `prefixQ`/`shQ`); `maskNV` mirrors the earlier `prefixP`/`shP`
  form, so `maskNV_eq` goes through `shiftMask4S` (both meet it). The build tree is re-snapshotted
  on `2e5b79a`; none of my modules changed in HEAD. `FRVIR4Mux` dropped from `MINE.txt` (INT-8 now
  edits it; the build uses HEAD's).
- `plan4t init` ×6 on core 29 (load ≈ 3–5): 1.88, 2.08, 1.90, 1.85, 1.82, 1.79 s; `inR true`.
  `plan4t check`: keys 100, instances 5,395 + 5,395; `evalMT4` = sparse sum, N2/N4/N8.
- `nodedump4` (24.6 s) into `logs/S-E12e/nodedump`: prototype 0 487,391 rows (+2,161: the node
  template), 3,032 instances, 26,639 import regs (−3: `shiftMask`'s results bound); prototype 1
  484,816 rows (+290: the segment template).
- `FRVIRTpl4Bridge` (new): `segMaskV_eq` (rfl), `maskNV_eq`, `routeOk_implSeg`, `routeOk_implN4`,
  `routeOk_implN4_ctl`, `protoCS_soundAt`, `protoR_ctl`. Pitfall: `routeOk_seg rfl` with `impl`
  implicit timed out (unification through `RouteOk`'s match); pass `impl :=` explicitly.
- Full build at `2e5b79a` + mine: green, 2,517 jobs (5 min 33 s). Axioms: 47, all within the three.
  Source rule: 0 findings. Profiles: every new module < 12 s wall, < 0.3 s type checking.
- V(N4), core 30, 21 reps: before the lever 202.8 / 202.9 ms best; after (`implN4` with S-T2's
  `withRS4`) 170.3 / 173.2 ms best; `rsWeight` 9.0 ms.
- Plan start A/B against S-E12d's binary (interleaved, core 29): 1.74–1.80 against 1.75–1.85 s.
- Re-snapshot on `ad3fbeb` (R4f): green, 2,520 jobs. RESULT written.
