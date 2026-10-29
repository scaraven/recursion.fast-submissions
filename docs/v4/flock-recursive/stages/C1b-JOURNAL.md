# C1b (track L-circ): JOURNAL — replay templates for the previous node's `evalL` and `targetS`

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `4838ac0`). Build tree
`logs/fr-build-C1b` (a copy of `fr-build-C1`, re-snapshotted onto HEAD; HEAD is green, so
`autosorry.txt` is empty and `patchdec.py` is not applied: `mine.sh` only). `mymods.txt` = C1's
modules plus this track's. Logs: `logs/C1b/`. Every lake/lean command in the 16G scope under
`timeout`. No sub-agents, nothing committed.

## 0. Findings before code (2026-10-29)

- Operands at prototype 0 (`logs/E1/nodedump/`): `targetS r45` (plain `AF20`, the same forms at every
  index) → `AF64`; `evalL r57122 r57149` (per-kind slots: `rL` `AF17`/`AF16`/`AF17`, `r4`
  `AF25`/`AF24`/`AF25` at `L32`/`P30`/`N30` = `N4`/`N2`/`N8`) → `F F F`.
- Values at index `ι`: `targetSNode4I (nodeAt ι)` (`implN4`'s `targetS` with `κ.isNode` after
  `fixK .N30`), `evalL4I (nodeAt ι)`.
- Import graph: `FRVerifierImplNode4`, `FRVerifierImplNode4T`, `FRVIRTplRepLW` are **not**
  downstream of `FRNodeRows4` (foldable); `FRVerifierImplNode4F` (`evalL4I`, `nJ`) is downstream.
  Hence `evalL`'s template definitions go to a definitions-only module `FRVIRTplRepLD` (imports
  `FRVIRTplRepLW` only), its proof to `FRVIRTplRepL`.
- `evalL` template (gate for gate `evalL4I`): 4 tables (`rL` lo 9 / hi `logL−9`, `r4` lo 14 / hi
  `m−21`), `E` and `F` stages of `vslots·nJ` products each, `vslots` slot products, one `oneCell`
  product, one `mulAdd`. Rows per kind: N2 66.3 k, N4 99.4 k, N8 148.7 k (kind-muxed: all three).

## 1. Log
- 20:00 build tree `fr-build-C1b`; baseline `lake build FRNodeRows4RepNCtrl FRVerifierImplNode4F
  FRVerifierImplNode4T` green (2,369 jobs, `logs/C1b/build0.log`).
- `FRVIRTplRepLD` (defs) + `FRVIRTplRepL`: `tplEvL ν a b`, **`tplEvL_ok`** green (traps: a theorem
  inside an `include hi` section takes `hi`; `eqTable_getD` over `List.length` of a mapped range needs
  the product moved to `Finset.range` before rewriting the length: `eqTable_getD_map`).
- `FRVIRTplRepT`: `tplTS ν a` (tables, point-weight blocks, range sums over prefix forms, the bodies'
  counter bits mirroring `ctrK`/`colT`/`sepD`, `G` as linear forms, the 1,216 output products),
  **`tplTS_ok`** green. Traps: `ite_getD` needs its `g` explicitly (a `_` sends `rfl` into a
  recursion-depth blow-up); piece lemmas take `hA`/`hB` explicitly (an `include` makes them
  arguments of every lemma).
- Orchestrator's note (CK changes prototype 0's numbering): the templates are keyed by op
  constructor (`isTS`, `isEvL`) and read the operand registers from the op itself; no register
  literal is used anywhere in the Lean.
- `FRNodeRows4RepLT` (`kTS`, `kEvL`, `kTS_ok`, `kEvL_ok`, `rtN0b`, `rtC1b`, `rtC1b_ok`,
  `repOkW_rtC1b`) and `FRNodeRows4RepLCtrl` green. Axioms (24 decls) ⊆ {propext, Classical.choice,
  Quot.sound} (`logs/C1b/axioms.log`); source rule 438 files, 0 findings. Kernel (type checking):
  LD 0.003 s, L 0.13 s, T 0.83 s, LT 0.19 s, LCtrl 0.04 s (`logs/C1b/prof-summary.txt`).
- **Plan-init trap found** (probe `RepV2` stuck > 3 min in the first KAT): every accessor
  (`tsE ν a j i`, `tsK0 ν a = nlocs (tsT ν a).1`, likewise `evE`/`evK1`) recomputes the tables'
  gates on each call — no sharing in compiled code. Likely also most of C1's 131 s (`lwE`/`lwK8`
  in `tplLW`). Fix: a context (`TSCx`, `EvCx`: the entries as arrays, the first local) built once
  per template by `let`, every piece over the context.
- Context refactor (`TSCx`/`mkCx`, `EvCx`/`mkEvCx`); proof trap: unifying `nlocs (tsT ν a).1`
  with `(mkCx ν a).k0` → 418 s of tactics; `rw [← mkCx_k0] at h` first → 2.9 s.
- Orchestrator: V budget corrected (tens of ms per template); CK at `44a4975`. Re-snapshot onto
  `44a4975`; R3's `rsWeight` takes `[repB+2^16, +472,310)`, so `cbTS`/`cbEvL` moved to
  `repB + 2^19 + 2^14` / `+ 2^15`; `rtC1c` = R3's `rtN0R` + `targetS` + `evalL` (`rtC1c_ok`).
  Final build green (2,383 jobs), axioms 29 decls clean, source rule 447 files 0 findings.
- Probe `repv2-4.log`: KATs true; prototype 0 compiled (plan's `compMSX`) 1.06 s; rows from the
  final state: targetS 0.26 s, evalL 3.4 s, **linkWAll 216 s** (C1's `tplLW` has the same trap);
  slot-0 rows (no rsWeight) 373,550 / 2.19 M terms, `growsVal3` N2 450 ms, N4 464 ms: `evalL`
  ≈ 345 ms, `targetS` ≈ 64 ms — over the corrected budget. RESULT §6 gives the levers. Stopped
  here (context budget).
