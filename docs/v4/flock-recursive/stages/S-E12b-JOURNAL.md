# S-E12b (track L-circ) journal: the compiled rows of the 4.1 nodes (N2/N4/N8)

Worktree `recursion.fast-submissions-flock`, HEAD `4acc3b3`. Build tree `logs/fr-build-SE12b` (copy of
`fr-build-SE13` + S-E11's `E5Eval`/`RStat`/`NodeDumpT` probes; `snap.sh` symlinks `MINE.txt`). Logs
`logs/S-E12b/`. Every lean/lake/probe command in a 16 GB scope with a timeout.

## 2026-10-28

- Baseline `lake build FR` green on HEAD, 2,449 jobs (`build-base.out`).
- S-E12a has no journal yet (its build tree `fr-build-SE12a` exists, `MINE.txt` empty): no
  `NodeResid4` names to match; this track's names are provisional and listed in the RESULT.
- **The dumps' structure** (`logs/S-F4/dump/ops-*.txt`, numbers and booleans normalised): `N4` and
  `N8` differ only in the kind byte; `N2` against `N4` and `L30`/`L31` against `L32` differ in the
  finals (`packF` lengths of Lr/E2/E4 points, `finPf`'s point families: `packK` lengths and extra
  `mulKF`/`addK`), in `packFK` lengths (Z, Sh points) and in `finalOps4`'s tail. The skeletons of
  one group are otherwise one op shape with different constants.
- **The mux index.** Each 4.1 group has three kinds, so the compiler's selector `Kind → Lin` serves
  unchanged: a group `G : Kind → KindP` (`nodeGrp`: `L32 ↦ N4`, `P30 ↦ N2`, `N30 ↦ N8`; `segGrp`:
  `L32 ↦ L32`, `P30 ↦ L30`, `N30 ↦ L31`). `gen4G` (new `FRVIR4Mux`) is `gen4` with the tables per
  index; `finalOpsG` reads one tail per distinct `m`; the finals are `finOps4` at the
  representative's counts (`FinP`'s `lrR/e2R/e4R/mB/nc/cells` are scalars: deviation, edit
  request to `FRVIRFinals4`).
- Semantics caveat: `exec`'s `hashStmt` uses `stmtDigest ι`, so the 3.x index cannot carry the node
  group's semantics (`L32`/`P30` would hash a leaf statement). The rows do not depend on it (an
  import); the bridge is S-E12a's/S-G's (open question).
- First compile (probe `Comp4`, `comp4-N4.log`): node mux 106,242 ops, seg mux 106,085; per pass
  134,614 / 139,030 skeleton rows, 3,032 instances (the level `tensorW`s, 745, are now templated:
  their `r` operand has one length per group), 26.6 k imports, 11 / 79 foreign flags; layout rows
  end ≈ 543,744 / 547,840 per slot.
- Generation took 390 ms per program (field offsets recomputed per position, ladder levels in the
  tables' closures, `reloc`'s `fieldOffOf` per op): `kt` (a table evaluated once), hoisted offsets,
  `relocT` by an offset table (`relocT_eq`, `finOps4F_eq`): **37 ms** (`comp4-N4-2.log`).
- **Design of the 1 + k slots (for V and the plan).** Slot `σ` gets its own M region `[σ·2^20,
  (σ+1)·2^20)` relative to M's first cell (`3·2^logM`), with its own `one` copy (cell `σ·2^20`;
  slot 0's is M's `one`) and selector copies (`+1…+3`); four link rows per slot (`one′ = one`,
  `s′ = s`) and the three one-hot products are the only rows that leave the region. Then every
  sub-slot is a **copy** of one prototype (rows and cells moved by `(σ−π)·2^20`), and because every
  entry of a copy has row and cell in the same region,
  `Σ_{σ ∈ copies} MLE = [Σ_σ eq(τ_hi,σ) eq(u_hi,σ)] · MLE_lo(prototype)`: one evaluation per
  prototype (node, segment), shared by `N2`/`N4`/`N8` (one plan per process for all kinds), and the
  existing 21/23-bit evaluator serves (M-relative cells `< 2^21`; the absolute cell's top bits are
  the factor `u_logM · u_logM+1`).
- `FRNodeRows4` (slots, prototypes, copies, link rows, `nodeIRows4`, `lRows4`) and
  `FRNodeRows4Plan` (`planData4`/`planData4_rows`, `Plan4`, `planOf4`, `evalMT4`, **`evalMT4_eq`**,
  `copy_val`) build. First measurement: `evalMT4` N4 158 ms — two causes found:
  1. separate key preparations per prototype (fixed: one grouping over both prototypes, shared
     keys, `kp_shared`/`kprep_star`: a key's preparation reads coordinates `< 20` only);
  2. **3.x's alignment hint counted `piDigest fSibs`**, which 4.x's absolute addressing reads as
     `piDigest 0`: every Merkle position was laid out unaligned and stayed sparse (55.8 k sparse
     rows). `stepsAhead` now counts `askNode` (the same count for 3.x). Sparse rows 40.7 k / 36.6 k,
     instances 5,395 each; `evalMT4` **N2 83.3, N4 83.7, N8 57.5 ms** best (`plan4t` run in
     `b0ypqr6bh`; 3.x's two-slot `evalMT` 71–75 ms, `vtime-rows-base.log`).
- Process start with `planOf4`: 10.4 s at first — the key-set filter's closure was specialised into
  its loop and recomputed the prototype-0 compile per key (generated C, `planData4_spec__2`); fixed by
  `keyCounts (z1 ++ z0)`: **2.54–2.61 s** (`init4-q*.log`). Over the 2 s target; parts
  (`planm4-1.log`, before the alignment fix): compile passes 339/262/317/191 ms, `kms` 192, slotRP
  244/288, grouping 179, patterns 183, prepared pieces 107, region check 91.
- V (N4) projection: 3.x V best 179.1 / median 187.3 ms (`vtime-N-base-1.log`), its `evalMT` ≈ 75
  ms; with `evalMT4` (N4) 83.7: **≈ 188 ms best, ≈ 196 median (VM)**, under the 230 ms kill line.
- Coordinator (S-E12a committed, `60b65cc`): `pfCells4` replaced by `cells4` (`FRNodeKinds4`);
  `absRows` renamed `absRows4` (clash with `TEval.absRows`); re-snapshot from HEAD.
