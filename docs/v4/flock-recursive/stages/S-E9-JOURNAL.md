# S-E9 (track L-circ): JOURNAL

Stage S-E9, 2026-10-28, HEAD `ebcc8f1` (INT-3, revision 3.14). Build tree `logs/fr-build-SE9` (a copy of
`fr-build-INT3`; `snap.sh` symlinks L-circ's modules and `NEW` modules to the worktree, every other
module is HEAD's). Logs in `logs/S-E9/`. Every lean/lake command runs in the 16G scope with a timeout.

## 1. Start

- `lake build FR` in the tree: green, 2,358 jobs (cached from INT-3's tree).
- Plan statistics at HEAD (`probe/E5Eval.lean`, `logs/S-E9/e5eval-0.log`): keys 68 (5,521 rows, 37,147
  entries); per slot 4,798 pieces: 3,790 instances (own inputs 5,408 single-cell forms), 1,008 sparse
  pieces (35,493 rows, 6,169 non-empty, 31,103 entries); `nodeIRows` 633,886, max row 1,454,460;
  `evalMT` 56.4 ms best (3 reps), `planOf` 7.3 s.

## 2. Item 1: sizing `R` from the plan (before writing it)

- `probe/RStat.lean` (`logs/S-E9/rstat-0.log`): per slot the plan holds, besides the 68 keys (9,056 rows
  with local terms over the 204 key×matrix blocks, 3,701 inputs), **3,790 instances** (3,582 runs:
  instances are not consecutive in piece order), **5,408 own cells**, **6,169 sparse rows with 18,354
  forms, 19,029 (form, cell-hi) groups, 31,103 entries**, 3,352 shared forms; 20,510 distinct cells.
- **The 259 k model (sizes.py "(D)") counts templates, walks, tables and the trace-cell imports, but
  not the skeleton's sparse rows nor the per-instance assembly** (`hfac` factors, own inputs). Under
  §4.4's rule each irregular operand costs a companion row, so these are ≈ 193 k rows per child slot.
- **Slot symmetry** (`rstat-sym.log`): slot 1's pieces are slot 0's with rows `+2^20` and a cell map
  that is `c + 2^20` for 20,506 of 20,510 cells (`+2^14` for 3 L cells, the `one` cell fixed): 0 bad
  rows, 0 bad forms. So `MLE(M) = Σ_{slot 0 entries} v · eq(τ_{<20}, r) · β̃(c)` with
  `β̃(c) = (1−τ₂₀) eq(σ,c) + τ₂₀ eq(σ,c')`: R evaluates one slot's structure.
- `logs/S-E9/rcount.py` → `rcount.log`: **R1s (slot-symmetric) 387 k rows per slot; node 1,966,862 =
  2^20.91 (1.066×; 1.14× with the phiRS lever)**. Without symmetry (R1) 581 k, node 2^21.17 (0.89×): does
  not fit even with the lever. The kill rule does not fire for R1s; the margin is thin.

## 3. Item 3: the `WM` map (done)

- `FRNodeLayout`: `wmSlot = 146`, `hEnd = 47,594` (`regions_fit`), the pinned map `wmB`, `mirOff`,
  `mirN`, `mirBlock`, `mirPos`, `mirBit`, `mirElem` (`mirElem_bit`, `mir_sources`, `mir_disjoint`,
  `mir_fits`, `mirPos_lt`, controls `mir_controls` / `mir_control_neg`).
- `FRNodeMirror` (new): `NodeT.wmB_eq`, `fam_mir` (each family's source is `off_f + t`, `j` 399),
  `fam_n`, `mirB_eq`, `mpos_eq`, `mir_in_wm`: S-C's `wmB`/`mirB`/`mpos` are the layout's map.

## 4. Item 4 first: `walkAB` — blocked by the density of `A₀`, `B₀`

- Wrote `FRVIRTplWalk` (sorted-set interpretation `sOps` of the gadgets, `setbits_xor`,
  `sim_compressW` twice, `tplWalkAB_ok` proved: the template computes `walkImpl`). It builds, but
  every executable importing it hangs at start: the closed term `walkRun` expands every gate's form.
- **Measured** (`logs/S-E9/walk-nnz.log`, the builder's forms' popcounts): **nnz(A₀) = 51,726,185,
  nnz(B₀) = 35,684,622** over the 14,720 gates (max 7,358 terms per row). A row-per-product template
  (A.11's "lincheck-replay class") has 87.4 M entries: not materialisable as `Circ.Row`s, nor by the
  plan's `eqL` check. The walk computes `Â₀` only through the gadget DAG (≈ 6·10⁴ XORs).
- Consequences: (i) `walkAB` needs either a symbolic M-row family (a lincheck block whose entries
  are `A₀`/`B₀` implicitly, evaluated by the walk) or a materialising gadget interpretation (one
  linear row per XOR: ≈ 90 k rows, and `GOps.xor` is pure, so `FRBlake2sGeneric` would change);
  (ii) R's two walks cannot be u-rows of `A₀`/`B₀` either (51 M coefficients): R would replay the DAG,
  ≈ 90 k rows instead of 65.5 k. Orchestrator's ruling needed. Module parked in
  `logs/S-E9/attic/FRVIRTplWalk.lean.txt`; the wiring reverted.

## 5. Item 4: `shiftMask` (done), the `packFK` kind mux (done), what stays imported

- `FRVIRTplMask` (new): `tplShiftMask` mirrors `NodeI.shiftMaskI` (four `eqTblG` tables, 1,025
  products, 26 for the range sums and starts: 2,071 rows); `tplShiftMask_ok` proved. Wired:
  `TKey.shiftMask`, `tplOf`, `tplExt`, `ImplT.shiftMask`, `outSlots_three`, `tplExt_ok`'s case.
  `implCWith_implT` (S-F2's module) still proves unchanged.
- **It stays an import in the dump**: its `τ` operand (like `slotW`, `eqPt`, `shiftEq`,
  `shiftTarget`'s) is a `packFK` whose lists have **different lengths per kind** (`co.take (κ.m −
  14)`: 18 for L32, 16 for P30/N30), so the compiler cannot type it (`logs/S-E9/impstat-*.log`).
- `FRVIRCompile`: **`packFK` with equal-length, different lists is now compiled** (`muxEl`: per
  differing element three rows `c_κ = sel_κ · x_κ`, the element `Σ c_κ`), proved in `opOut_sound`.
  It binds `maskRows`' `kindW` (finLc's 9-element pack), so `maskRows` is a template instance (was
  the one foreign `maskRows`): foreign 76 → 74, imports 27,356 → 27,353, instances 2,276 → 2,280.
- **Cost**: `maskRows`' 2^14-row instance is evaluated in 256 chunks with 16,100 own inputs:
  `evalMT` 56 → 101.6 ms (`e5eval-2.log`), **V 168.7 → 207.2 ms best** (`vtime-N-{1,2,3}.log`).
  Projection with S-E8's remaining additions: ≈ 231 ms (< 251).

## 6. Kill-rule arithmetic (rows) — see RESULT §1

Measured aligned layout 436,092 rows per slot. With S-E9's sizes for what is not built (R1s with the
walks replayed as the XOR DAG 412,606; the `walkAB` DAG template ≈ 90,851; the rest as changes 21):
1,065,133 per slot, **2,130,266 per node > 2^21 (0.98×)**; 1.045× with the phiRS lever.
`mRowModel` carries changes 21's ratified figures with the measured layout (885,012 per slot,
`mRows_le` holds); the over-budget figures are reported, not encoded.
