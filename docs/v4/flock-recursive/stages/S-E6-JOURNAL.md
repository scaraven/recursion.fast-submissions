# S-E6 (track L-circ): JOURNAL

Stage S-E6, 2026-10-28, branch `v4/flock-recursive`. The base is HEAD `ce8cdc7` (INT-2, revision
3.13); the last snapshot was taken at `1fe52f4`. Nothing is committed.

- Build tree: `logs/fr-build-e6`, a copy of S-E5's tree with its cache. `snap.sh` takes HEAD's
  modules and symlinks L-circ's and `FRVerifierImpl`. S-CN's `FRNodeTarget`/`FRVerifierImplNode`
  and the `FRX*` modules are taken from HEAD and not touched.
- Every run used the 16 GB scope. Probes ran on one idle core (`taskset -c 30`; cores 4, 12 and 20
  carried other agents' Lean jobs). Logs are in `logs/S-E6/`.

## 1. `evalLT` in `implC` (item 1)

- `implCWith pl lp` takes an `LPlan`, and `implC fin lRows := implCWith (planOf fin) (planL
  lRows)`.
- `specC.evalL` is still `evalRowsSpec 15 23 lRows`. The bridge is `planL_rows`, and
  `implCWith_meets` takes `lRows`.
- The probes now use the full 3.13 finals (`Impl.finC finPf`) and the real `Layout.lRows`.
- **V (N30) = 228.9 / 230.4 / 229.3 ms best, 234.2–238.6 ms median** (`vtime-N-{4,5,6}.log`;
  `traceDigestF` 12.4–13.4 ms, at its baseline).
- The rise from S-E5's 205 ms is the real `finPf` (`rsWeight` 7.6 ms and the rest of `finPf`)
  and `evalL` (4.9 ms) (`prof-N-1.log`).

## 2. The 3.13 dump (item 2)

- `NodeDumpT` with `finPf` gave per slot 269,499 indexed rows and 1,402 instances.
- That dump was later **replaced** by the dump of the circuit after item 3 (§3), so that the dump
  matches the source tree.

## 3. Templates (item 3)

- **`tensorW`** (`FRVIRTplRep`, new):
  - `Ŵ_v(D[j])` is linear in `j`'s bits by `wAtT`'s definition. Each factor is two `K × F` gates,
    plus `n` Karatsuba products: `5n` rows.
  - The bits are an auxiliary import in the instance's region (`AuxK.bits 20`).
  - `tplTensorW_ok`, `ImplT.tensorW`, and the `tplExt` case are done.
  - 882 of the 1,627 ops are bound. The other 745 are `finPf`'s, whose `r` is a kind-dependent
    `keep` of arrays of different lengths, so it is untracked.
- **`rowW`**:
  - The products come first (row `k` = local `k`), then `lagG` and `eqTblG`. The template is
    `rowWG N`, generic in `N`: with `2^14` written out, `rw` unfolded the gate list
    ("maximum recursion depth").
  - Its operand `r′_hi` is a `packFK` with the same list for every kind. **`packFK` is now
    tracked when its lists agree** (`opOut`, `opOut_sound`).
  - The 16,829-row template made `evalMT` 114 ms and V 295 ms (`eval-2.log`, `vtime-N-b*.log`).
    Two fixes:
    - the plan cuts templates of more than `2^12` rows into 64-row chunks (one key, shared
      weights);
    - `mkLay` aligns such templates to 64 rows only, and every group's next start is after its
      last instance's rows.

    After both: `evalMT` 70.6 ms (`eval-3.log`).
- **`kindInd`:** not used by `gen` (0 ops in INT-2's dump).
- **`FRVIRCompile` split:** the program-level section moved to `FRVIRCompileSound` (779 + 240 code
  lines).
- **V = 243.8 / 247.4 / 248.9 ms best, 245.9–254.2 ms median** (`vtime-N-c{1,2,3}.log`).
- Not done, see the RESULT:
  - `walkAB`, `rsWeight` (point lists differ by kind), `shiftTarget` (it needs the digest bits of
    `bnd`);
  - the child `evalM`/`evalL` replay, which is a design blocker (RESULT §4).

## 4. Rows (item 4, partly; item 5)

- `E6Rows` (`rows-per-generator.log`) gives the rows per skeleton phase and for the finals, the
  padding, and the templates by key.
- `mRowModel` was updated on the measured 3.13 counts, without `rsWeight`'s claim 5: **1,017,848
  per slot (1.03×), 2,035,696 per node ≤ 2^21; blocks 63,351 ≤ 65,536.**
- The dump of the current circuit is `logs/S-E6/nodedump/` (218 MB).
- The H-side assembly of `node_sound` and `node_complete` are not done.

## 5. Checks

- `lake build FR`: green, 2,322 jobs, 2 min 30 s (`build-FR-1.log`).
- Axioms: 50 statements (`axioms.log`), within the three standard axioms.
- Source rule: 122 files, 0 findings.

## 6. S-CN's heads-up (mid-stage)

- No L-circ module reads the WM mirror map, so nothing to make parametric there yet.
- `targetSNodeI` is wired by `κ.isNode` in `implC`/`specC`. The leaf `targetS` template and
  `ImplT.targetS` are removed (an import until `tplTargetSNode`).
- `FR` is green, the axioms are within the standard three (51 statements), and the source rule
  reports 0 findings.
- Re-dumped at `1fe52f4`: 316,943 rows per slot.
- **V = 229.3 / 231.8 / 234.9 ms best, 237.3–249.9 ms median** (`vtime-N-d*.log`); `evalMT`
  59.5 ms.
- `linkW` wiring and `tplLinkW` wait for 3.14.
