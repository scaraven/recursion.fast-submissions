# CK journal: compile the unequal-length `keep` chain (SRA §4.2) into rows

Track CK, 2026-10-29. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `27459d9`).
Build tree `logs/fr-build-CK` (copy of `fr-build-SRA`, re-snapshotted onto `27459d9`; MINE =
`FRVIRCompile FRVIRCompileSound FRVIRFinals4 FRNodeRows4Hint` + new `FRVIRCompileK*`). Logs `logs/CK/`.
No sub-agents, nothing committed.

## Log

- Set up `fr-build-CK` (cp -a of SRA's tree; run.sh/prof.sh log to `../CK/`).
- **Diagnosis** (`logs/CK/ctx0a…d.log`, ForsDump `ctx`): the five unequal `keep`s are `gFinPf`'s
  (`FRVIRFinals4`) `keep selA (pfCandA …) (selOut …)` for the tails `P₁…P₄` and `P₀` (m* family vs the
  other family, lengths n / n−1). They already had **per-kind slots** (`tplExtKM`, S-E12f; main slot
  `none`). Their consumers: `tensorW` (templated per kind, `.tensorWK`), `rsWeight` (import) and
  **`getK (sb+4) v`** (`P₀`'s 25 coordinates), which `opOut` skipped (no kind-free slot). Everything after
  (`addK one`, the cells' `keep`/product chains, the level sums, the final `mulK`s) followed, ending in
  `finPf`'s `assertEq (pe+nf+1) (claimN fi "Pf")` = op#109053. (SRA called it the (β′) cap check; it is
  `finPf`'s final equation, which contains the cap-entry MAC `piElemK × getK (eqTableK …)` terms.)
- **Option chosen: a compile-side extension, no V change** (neither 1 nor 2 literally): `getK` of a
  kind-muxed register gets per F component a 3-way selector mux of the kinds' forms (`FRVIRCompileK`:
  `mux3`, `getKK`, `extGetK`, `extGetK_okK : ExtOkK`), run after `tplExtKM` in `tplExt4`
  (`FRVIRTplSet`, 2 lines + import). V's op list, registers, semantics and proofs unchanged.
- First build green (FRVIRCompileK, FRVIRTplSet). `forsdump`: prototype 0 **14** flags (was 15), prototype 1 79.
- `ckskips` probe: after the change the only untracked non-byte results are 1 `const` (kind byte) and
  the per-kind registers (p0: 11 `packFK`, 5 `keep`; p1: 4, 10); the only consumer of an untracked
  non-byte, non-per-kind register is `const -> assertEq` (the kind byte). Both prototypes have exactly
  the five unequal-type `keep`s (p1 at op#101770–101774), all per-kind.
- `ckdelta` probe (old `tplExt4` vs new): p0 rows 189,352 → 196,072 (+6,720), cells 276,634 → 283,546
  (+6,912), 4,392 registers newly tracked, template keys/instances equal, imports equal, flags 15 → 14;
  p1 rows +64, cells +256, 50 newly tracked, flags 79.
- Hint regenerated (`laydump4.log` + `mkhint.py`): only `hintLay0`'s row bases move (+6,656 … +6,144;
  cells unchanged); `hintLay1` unchanged.
- `plan4t init`: inR true. `cellfit`: 0 overlaps both; `arenafit`: p0 skeleton cells end 283,546 ≤ arA1
  290,816; last row 706,303 < arR2 720,896 (true); p1 unchanged.
- `mxkat` (`logs/CK/mxkat.log`): 34 `= face798's true`, 0 mismatches (the 3 `nonzero false` are the
  empty support, as IMP's).
- `nodedump4` → `logs/CK/nodedump/` (1.6 GB): p0 656,486 indexed rows, last index 706,303 (706,304 rows
  in the region, was 700,160), cells 4…283,546, 14 foreign; p1 unchanged (686,080 rows), 79 foreign.
- `FRNodeRows4Model` (unowned; a measured literal): `protoRowsN` 700,160 → 706,304; `regions_sum`
  node 945,568 → 951,712; `mRowModel4_eq` N2 3,533,688, N4 5,494,664, N8 7,843,904 (unchanged: N8 has
  no previous-node slot). `mRows4_le` unchanged in statement.
- Full build started (`logs/CK/build-full.log`); `plan4t check` running (N2 sparse = fast: equal true).
- Full build at `27459d9` green (2,655 jobs, `build-full.log`). Orchestrator: plan check killed by
  mistake; ASK-P committed `74a2528` → re-snapshotted, rebuilt everything (5,056 jobs incl. probes,
  `build-full2b.log`, green, 0 sorry).
- At `74a2528`: hint identical (`laydump4-2.log`); inR true; cellfit/arenafit as before; forsdump 14 / 79;
  ckskips identical. MxKat with the pre-ASK-P reference fails on every non-empty support (stale probe:
  ASK-P's reference adds `arV4`); with ASK-P's `MxKat.lean` copied: 33/33 true (`mxkat3.log`).
- `plan4t check` (3,600 s cap): N2 equal true (174 s), N4 equal true (303 s); N8 running.
- A/B vs `askp-bin`: V(N4) own 275.8 → 297.2 ms best; plan init 6.6–7.4 vs 7.0–9.3 s wall.
- `ckmoved.log`: p0 registers ≥ 93,116 have new cells (12,577 imports from reg 99,829), rows ≥ 116,833;
  p1 registers ≥ 93,084, rows ≥ 118,951; 0 template-input or aux differences; reserve cells unchanged.
- Axioms (12 decls) ok; source rule 442 files 0 findings; profiles (`profile-*.log`). RESULT written.
- `plan4t check` N8: **equal true** (sparse 848 s, run 22:17 wall under the 3,600 s cap). Done.
