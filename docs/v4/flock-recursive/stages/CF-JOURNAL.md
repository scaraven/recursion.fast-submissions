# CF (track L-circ): JOURNAL — closed-form evaluation of the replay blocks

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `407260d`). Build tree `logs/fr-build-CF`
(copy of `fr-build-REPF`, `mysnap.sh`: HEAD snapshot + this track's modules linked, `mymods.txt`).
Logs `logs/CF/`. No sub-agents, nothing committed.

## 2026-10-29 start

- Baseline: `lake build FR Solution FRSubmission4Fin plan4t vtime4` green on HEAD (`logs/CF/base.log`).
- Design (see RESULT §2 when written):
  - **rsWeight** (472 k rows): the template is re-laid-out as *segments* (`SG`): irregular gate lists and
    **rep groups** (`n` instances of one padded pattern at stride `2^p`, inputs through placeholders
    `σ s i`). A rep group's MLE has a closed form for **any** row/cell offset (the carry of a pattern
    row/local into the high part depends on the row/local only, not on the instance): two shifted
    diagonal sums over the instances, the placeholders' weighted sums, and one pass over the pattern.
    Groups: the `W₀` chains (one 127-step chain per block, `p = 8`), the claims' coordinate chains
    (`p = 8`), the stage loops (claim 2: `p = 9`; claims 1, 3, 4 together: `p = 8`).
  - **evalL** (319.5 k rows): template redesign: per slot the sum `Σ_j eq(rL, σ nJ + j)·eq(r4_lo, 299 + j)`
    by a carry automaton (≈ 400 gates per slot instead of 16.4 k), no tables.
  - Plan: the trail yields *blocks* (rows, or a kind-muxed op described lazily); the replay value is the
    grouped sparse value of the row blocks plus the structured value of the `kRS` block; `RepFit` by a
    structural check (sound, incomplete: the fallback stays).

## Progress 1 (rsWeight template)

- `FRVIRTplCF` (new, generic, green): `rowsAt`, `RowT.sub`, `rowsAt_sub`, `tm` (rows' value, `tm_sub`
  pull-back, `tm_append`), `Rep` (n instances, stride 2^p, placeholders `Ph`), `tm_repI`, **`Rep.tm_rep`**
  (closed form for any offsets), the per-call evaluator `Rep.ctx`/`Rep.pass` with **`Rep.eval_eq`**;
  segments `SG`, `sgGates`, the builder `SM` (`ok_bind/map/lift`, **`ok_rep`**), `sgVal`/**`sgVal_eq`**.
- `FRNodeRows4RepCFRs` (new, green): `rsGS` (blocks once irregular; W₀ chains, coordinate chains,
  stage groups A, B as repeated patterns), **`ok_rsGS`** (= `rsRef`, as `ok_rsG`).
- `FRNodeRows4Defs.rsT` now builds `rsGS` (statement of `kRS_ok` unchanged; proof uses `ok_rsGS`).
  `repB` is `@[noinline]` (INIT's proposal 1).
- Snapshot moved to HEAD `32e4e9c` (INIT committed).
- Next: probe `CFRs` (sizes per kind, closed form = sparse KAT), then the plan's block trail and evaluator,
  the structural fit check, the cb relocation (rsWeight grows with the padding).

## Progress 2 (plan side, measurements; handover)

- `FRVIRTplCFE` (prepared segments, `psVal_eq`, `psLocOk_rows`) and `FRNodeRows4RepCFP` (`rm`,
  `rowsVal_locF/L`, `rm_inst`, `tm_subsG`, `kpOf`/`kopV`/**`kopV_eq`**, block trail `trailMB_eq`,
  `arBlk0_eq`): green, not yet wired into `FRNodeRows4Plan`.
- Probe `CFRs` (logs/CF/cfrs5,6): new sub-templates 163/167/174 k rows (R3 147/155/170 k); closed form =
  sparse (KAT) at all kinds; 225–297 ms vs 369–446 ms (3 matrices). Chain groups ≈ 1.5 ms (closed form
  pays); stage groups 26 + 42 ms per matrix: the placeholders' instance sums dominate, and `Rep.ctx` is
  recomputed per matrix. Trap found: `splitE` partially applied rebuilds its tables per call in compiled
  code (≈ 1 ms per lookup); build the tables as arrays (`loTab`) and use `splitAt`.
- `cbTS`/`cbEvL` moved (rsWeight's locals now reach `repB + 570,320`); `cb_ctl` updated.
- Re-snapshot onto `97d578b` (FOLD2); full build `logs/CF/cf8.log`.
- Context limit reached: CF-RESULT.md §6 is the handover (wire into Plan4, structural RepFit, speed-ups,
  evalL by a carry automaton, A/B).
