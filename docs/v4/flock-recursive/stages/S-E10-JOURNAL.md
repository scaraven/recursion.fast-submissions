# S-E10 (track L-circ): JOURNAL

Stage S-E10, 2026-10-28, HEAD `5035389` (revision 3.15). Build tree `logs/fr-build-SE10` (a copy of
`fr-build-SE9`; `snap.sh` symlinks L-circ's modules, `FRBlake2sGeneric` and the new modules, every
other module is HEAD's, so S-G6's untracked `FRSoundnessFr*` files are not seen). Logs in
`logs/S-E10/`. Every lean/lake/probe command runs in the 16 GB scope (6–8 GB for single-file
elaboration probes) with a timeout.

## 0. Baseline

- `lake build FR FRNodeMirror` green (2,376 jobs). V (N30, 21 warm runs, core 30):
  **206.17 ms best, 221.98 ms median** (`vtime-N-base.log`).
- `planOf`'s time by part (`probe/PlanT.lean`, `plant-0.log`, slot 0): `gen` 55 ms; `compileT`
  with the zero layout 853 ms; `mkLay` 320 ms; `compileT` 667 ms; `slotIRows` 2,911 ms;
  `slotPPs` 4,615 ms; `groupPPs` 3,551 ms (slot 0 twice). One compile of one slot is 0.67–0.85 s.

## 1. Item (a): the walk as the node's own XOR DAG

- **Design.** `GOps.xor` stays pure in `FRBlake2sGeneric`: V's own walk (`walkImpl`, the hot
  8.9 ms) keeps its compiled code, and `sim_compressW` with the three modules that use it
  (`FRBlake2sWalk`, `FRBlake2sWitness`, `FRVIREval`) is untouched. The row-emitting
  interpretation is `FRVIRTplDag`: the gadget program statement for statement over a builder
  monad `DB`, where XOR is a formal sum of single-wire forms and **a row is emitted where a form
  becomes a cell** (`dcell`: carries, `sumW` outputs, the `G` outputs `b2`/`d2`, the IV copies, the
  final words), and a product gate emits two running-sum rows (`dmul`). Its correctness
  (`FRVIRTplWalk.tplWalkAB_ok`) is a relational simulation against `walkOps`' run of the generic
  program (`RelT`, `DGrows`, `emit_eqn`).
- **Sizes (measured, `probe/DagCount.lean`).** First version (one row per XOR): 84,223 XOR rows +
  31,746 products, 168,706 layout rows at a 2^11 `G` stride. Second (XOR chains as one row each;
  operand XORs folded into the product forms): **25,312 XOR/copy rows + 31,746 product rows =
  57,058 rows; 85,506 layout rows** at the 2^10 `G` stride (80 × 1,024 + head 1,024 + tail 2,562);
  288,526 entries; generation 56 ms. A `G` block is 678 rows (310 XOR + 368 products).
- **Elaboration traps met** (each a runaway, killed by the cap): the elaborator unfolding
  `GOps.initW`'s vector literal (fixed: `ofFn_getFin` stated for a variable, `GOps.initW`
  irreducible); `dvec 16 …` vs a definition wrapping it (fixed: no wrapper); a `rw` closing by `rfl`
  over the concrete run of the DAG (fixed: `dwalkRun` defined directly, `dcompressW` irreducible,
  the run generalised before any growth lemma). No closed term expands a form.
- `tplWalkAB_ok` proved.
- Wired: `TKey.walkAB n m`, `tplOf` (`tplWalkOf`: the closed `tplWalk14` at `2^14`/`2^14`,
  `tplWalkOf_eq`), `tplExt`'s `walkAB` case (outputs `[.f, .f]`), `ImplT.walkAB`
  (`implCWith_implT` in S-F2's module proves it unchanged), `tplExt_ok`'s case. `mkLay` aligns the
  walk's rows and cells to `2^gBits` and starts the next group after its last local; `tinPP` cuts
  the walk instance into its `2^gBits` blocks. `tplWalkG` is irreducible (else `tplExt_ok`'s
  unifier evaluates the DAG).
- `Gate.pad r l` (TplCore): `r` empty rows, `l` locals, `Eqn` trivial.
- **Grouping:** the 79 `G` blocks after the first abstract to one template (`walkins-0.log`); the
  first differs (its first product's accumulators are `0`, not a cell). `inputKinds`' partition
  split them into one key each (the message words take 16 values); `groupPPs` now reads partition
  inputs as own inputs when the joint labels give parts of fewer than 4 members. Keys 88.
- **Measured** (`e5eval-a1/a2/a3.log`): `evalMT` 306 ms (64-row chunks), 366 ms (blocks, one key
  each), **169 ms** (blocks grouped; was 101.6 in S-E9); by key (`e5eval-a3k.log`) the `G` key's
  79 instances with 44,398 own inputs cost ≈ 26 ms (≈ 0.6 µs per own input = 3 F products).
  `planOf` 57.1 s (was 12.8). **V 287.13 ms best, 304.75 median** (`vtime-N-a1.log`). Node M:
  last row 1,574,780 (slot 1 = `2^20` + 526,204); 526,205 rows per slot (S-E9: 436,092).
- FR green (2,382 jobs); axioms (`axioms-a.log`, 36 names) only `propext`, `Classical.choice`,
  `Quot.sound`; source rule 161 files, 0 findings (`source-rule-a.log`).
- Sequential profiles (`profile-*.log`): `FRVIRTplDag` 11.6 s wall, 0.22 s type checking;
  `FRVIRTplWalk` 19.8 s, 1.32 s; `FRVIRTplExt` 10.2 s, 0.21 s; `FRVIRTplPlan` 8.1 s, 0.06 s.

## Stop: context (handover in the RESULT)
