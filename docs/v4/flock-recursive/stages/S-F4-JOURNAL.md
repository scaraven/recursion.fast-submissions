# S-F4 JOURNAL: the finals over `Seq`, the segment's variable last block, `Vseg`/`Vnode`

- Worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive`, HEAD `47c5c6c` (S-0′).
- Build tree `logs/fr-build-SF4` (copied from `logs/fr-build-S0p`, whose `snap.sh`/`lakefile` point at
  `logs/org20`, as INT6's; it carried S-0′'s built oleans). `MINE` lists the S-0′ layer and the new
  modules. Logs `logs/S-F4/`.

## 1. The finals over `Seq` (`FRVIRFinals4`)

- Design: one parameter record `FinP` (`S`, the kind tables `KV` = 3.x's KC tables `m`, `isNode`,
  `is32`, `rsPtIx`; the node's real Lr/E2/E4 counts; `finPf`'s second point family `mB`; the node's
  public cells and their coordinates; `vn`, the segment's variable last block).
- Every field is rewritten with the parameters; helpers that carry no size are reused (`dotOps`,
  `lcTail`, `linkOps`, `claimOps`, `finPLow`, `ptsOps`, `accOps`, `fhOps`, …).
- Addressing: the fields keep 3.x's field-relative reads (`piElem f o`), with in-field phase
  offsets from `phaseOffOf S`; `reloc S` then makes them absolute in `S`'s format (as `gen4`'s
  skeleton is). At `seq3` `reloc` changes no op's value (`evalOp_reloc_seq3`).
- `finalsOf_seq3`: field by field `gFinX fin3P = finX` (`rfl` after rewriting `seq3_eq`,
  `phaseOffOf_seq3`, and the list lemmas `gCellsOps_23`, `gLvsOps_3`, `gPfPts_3`).
  First try of `gFinPf_3` timed out in `rfl` (simp had expanded `List.range 128` through
  `List.range_succ`); two simp passes (first the list lemmas at `seq3`, then `seq3_eq` and numeral
  reduction) and a bare `rfl` work.

## 2. The variable last block

- `FRVIR4`: `lastOps` (94 ops in the segment's `stmt` phase: `piDigest` at byte 33, `idx` 24 bits,
  `bitOf`/`selectHalf` per bit, the borrow chain `L = n − 1` in F), `lastOuts`, `segPtOp` (Z2's
  `targetS` operand `r ‖ L`, block coordinates zero-padded).
- Design of the masking (`FRSegTarget4` docstring): target × `Σ_{t ≤ L} eq(r_blk, t)`; the shift's
  successor masked at `L` (`shift + eq(τ, L) eq(r, L + 1)` in char 2), `E` unmasked, `E₀` unmasked;
  lincheck/claim 2/RS unchanged. Unmasked successor would leave `Out(L) + In(L + 1) = h`: a free
  block's input would move the end (`shift_unmasked_link`).
- **OOM (16 G) in `targetSSeg_meets`**: `simp only [Function.comp_apply, FR.targetS]` on the
  `Array.ofFn` goal over `Fin (2^(8 + 18))` blew up (bisected with `lake env lean` under a 6 G cap:
  `/tmp/claude-1000/bis/cut.py`). Replaced by `rw [Function.comp_apply, FR.targetS, FR.targetS]`
  (as `targetSLeaf_meets` does); the file then builds within the cap. Also avoided `set` with a
  lambda pattern (kabstract on a lambda compares every subterm) in favour of `generalize`.

## 3. Programs, verifiers, soundness hand-off (`FRVerifierC4`, `FRAgg`)

- `kvOf`, `segFinP`, `nodeFinP` (cells a parameter), `progSeg`, `progNode`, `VsegC`, `VnodeC`, `VC4`,
  `acc_eqC4`, `implSegC_meets`, `VC4_agg_extract`; controls `finP_ctrl`, `VC4_rejects`.
- `SegSound` (S-0′) quantifies over every trace: no Fiat–Shamir verifier meets it (a trace may
  answer the queries at will). Added `SegSoundOn Good`, `SegKSOn Good` (an accepted run on a good
  trace has a table meeting `SegHolds`), `segSoundOn_of_KS` (through `seg_sound` = `leaf_sound`),
  `VA_extract_on`. `SegSound`/`VA_extract` are unchanged.

## 4. Dumps, checks

- Dump tool `logs/fr-build-SF4/dump/IRDumpF4.lean` (copied to `logs/S-F4/dump/`); script
  `logs/S-F4/dump.sh`. First run of L31 … failed: it started while `lake build FR` replaced the
  oleans; rerun sequentially after the build (1 min 52 s for all).
- `last`: `lastOps` run on synthetic statements, `n ∈ {1, 2, 5, 2^16, 2^16 + 1, 2^17, 3·2^16,
  2^18 − 1, 2^18}`: `L = n − 1` each time.
- Name clashes: `rangeI`, `ptA_ofFn` existed in `FR.Impl`; renamed to `segRangeI`, `ptA18_ofFn`.
- `lake build FR` 2,419 jobs; axioms of 22 theorems standard; source rule 195 files, 0 findings.
