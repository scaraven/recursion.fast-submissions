# S-CN journal (node `targetS` and `linkW`, blueprint revision 3.13 gap 3)

Track S-CN: S-C's specs (`targetSNodeS`, `targetS_node_eq`, `linkWS`, `linkW_mle`) and S-F2's
computable forms (`targetSNodeI`, `linkWI`, `_meets`). Build tree `logs/fr-build-S-CN`
(lakefile by `gen.sh`, `.lake` seeded from `fr-build-INT2`, every build under the 16G scope).

## 2026-10-28

- Read TRACK-RULES, BLUEPRINT §10 changes 20, A.6 (`WM`), A.8 (`targetS`, `linkW`), §4.2, §2 step 4,
  `FRVerifierImplOps`, `FRPubTarget`, `FRNodeLayout`, `FRShift`, `FRBlockKinds`, `FRBlockStream`,
  `FRSoundnessPIOP.nodeKind` (S-G's per-block target: the spec mirrors it), `FRVIRFinals.finSh`.
- Seeded build tree: dependencies up to date (2,261 jobs, no rebuild).
- Concurrent edits elsewhere (FRVIRMux importing a new FRVIRCompileSound) broke the worktree-srcDir
  tree: switched `logs/fr-build-S-CN` to a private snapshot `src/` of HEAD `c66dbc0` with my two
  modules symlinked (`gen.sh`).
- Spec findings while reading (RESULT §5): `end41` (offset 41, 32 B) crosses the block boundary,
  so it is split into `end41lo`/`end41hi` (8 families = `nLinkFam`); Sh reads elements 0–7 of a
  block only (`shSrc`: 3 element coordinates + 4 zeros), so A.6's WM map (elements up to 127) is
  unreadable: mirror source `g` placed at block `wmB σ + ⌊g/4⌋`, positions `256 (g mod 4) + s`;
  `WMbase_σ = wotsBase_σ + 498` collides with slot 1's WOTS run; under 3.13 the last chain block's
  `t_lo` equals the counter form (kept as a single-block class).
- `FRNodeTarget`: `nodeTgt` (= `Snd.nodeKind`, checked by `rfl` in `logs/S-CN/Bridge.lean`),
  `targetSNodeS`, `targetSNode_blk`, `tgtE_ctr`, `tgtE_w43`, the closed form `Gc`, `blkW_eq`,
  `targetS_node_eq`, `Gc_hi`; link families `fam`, `linkWS`, `linkInd`, `linkInd_sum`,
  `linkW_mle`; controls (`nodeBit_pos/neg` by `decide` on eight bits, `Gc_controls`,
  `linkW_hit/off/mir`). Green.
- `FRVerifierImplNode`: two-level tables, prefix arrays, `sepSum_eq`, `rangeI`, `ctrI` (counter bits
  by column masks for `j < 8`, row masks split by the carry for `j ≥ 8`), `gArr`, `targetSNodeI`,
  `targetSNode_meets`; `linkWI`, `linkWAllI`, `linkW_meets`, `linkWAll_meets`; controls. Green.
  Pitfalls met: `rfl` on a structure with `eqTable` fields unfolds the table (use `dsimp only`);
  `congr 1` and `simp [sum_range_succ]` on goals with `range 23144` blow the recursion depth (use
  `congrArg` and a two-term `sum_two`).
- Timing (`time-5.log`, best of 40, core 5): F product 80 ns; `targetSLeafI` 1.58 ms,
  `targetSNodeI` 2.00 ms; `linkWI` ×8 4.35 ms, `linkWAllI` 1.90 ms (operands 0.34 ms included).
- Profiles (sequential): FRNodeTarget 19.8 s wall / 3.45 s kernel; FRVerifierImplNode 12.2 s /
  1.17 s. Axioms: standard three (21 statements). Source rule: 121 files, 0 findings.
- RESULT written; wiring for `implC` in RESULT §6 (needs `linkW` to receive θ and `r_pos`).
