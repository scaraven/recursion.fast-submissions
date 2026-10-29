# IMPC2 journal (track IMPC2: bit area, siblings, bitOf, bits 20, stmt flags and unaligned reads)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Build tree `logs/fr-build-IMPC2` (copy of
`fr-build-IMPC`; `MINE.txt` = my `FRNodeRows4AskB*` modules; everything else HEAD's text). Logs `logs/IMPC2/`.

## 2026-10-29

- Copied the build tree; scripts log to `../IMPC2`. Base build at `3577618`: green (2,522 jobs).
- Orchestrator: ASK-T committed (`ae8b8d8`); re-snapshotted onto it. `askTG` = `askTGT + inpTG + rsvTG + impcTG`.
- Read IMPC2.md, IMPC/ASK-T RESULTs, ASK-T's `askRowsG` (node operands on arena₁ at `qElT`), `sib4`/`posOf4`
  (bit `h` of the position under the trace's ladder), `merkleOpsG`/`posOpsG`/`bitPowOps`/`lastOps`/`stmtOps4`.
- **Conflict found**: `TG.add` asks every side for rows at any covered op; `impcTG`'s `pfRows` emits `failRT` at a
  read whose windows are not elements (siblings, unaligned statement reads). So a generator covering those reads
  cannot be `add`ed. Fix (mine, no edit elsewhere): **`TG.addD`** (each side asked only at its covered ops and the
  asks). `askTG`'s diff uses `|>.addD (bitTG …)`.
- `bitOf` is an import whose operand is untracked: its rows go at the **following `selectHalf`** (`pre = bitOf`, the
  bit operand is the last register), which is not an import, so covering it is free for `ATImp`.
- New `FRNodeRows4AskB` (below `FRNodeRows4`): `eBit`, layout (`posCell` position-major kind-free, spares per kind,
  statement bits after), provenance array `riAcc` (ask → item, `idx`, `shrN`, `piDigest`, `piField`, byte const),
  statement layout read off the program (`tagScan`/`tailScan`: so 48, tag, z, L), `BTab`, `ansCell`, `stCell`,
  `idxSrc`/`bitSrc`, `selRows` (copy / two-class product / per-kind gated), `ansRows`, `stElRow`, `globRows` (at the
  seed's ask), `sibLoc`/`sibRows`, `stWin`/`stRdRows`, `auxBRows`, `bitCov`, `bitRowsOp`, **`bitTG`**, `TG.addD`.
- Local patches in the build tree (`patch.py`, the RESULT's diffs): arena `arNb 16384`, `arR2N 180560`,
  `arRb 998400` (+ the `a1Rows4_ctl` literal 852997 → 901461); `askTG … |>.addD (bitTG …)`.
- Probe `bitstat` (`logs/IMPC2/bitstat*.log`): **0 `failR`** both prototypes; rows p0 64,651 / p1 81,039 (design
  64,537 / 81,039); every `bitOf` (15,265 / 15,283), sibling (7,426), `tensorW` (1,627) and unaligned statement read
  (4 / 5) matched; bit area need 16,384 / 16,192 of 16,384.
- Init, first cut: +1.1–1.3 s per prototype. Cause 1: `stepOut` at `tensorW` builds the template (≈ 0.8 s per
  prototype) → `bitTG` takes the compile's extension with a **template-free context** (`trailMS`'s key context).
  Cause 2: `ansRows` recomputed the kind maps (→ `kt`). Cause 3: `stepOut` at every `selectHalf` built a mux (→ the
  extension alone). `subN` (no product per term), `eBitT`. Now ≈ +0.30–0.40 s trail + 0.16–0.21 s grouping per
  prototype, **≈ +1.0 s per process** (`bitstat5.log`). `askV` +75–100 ms per prototype.
- Lever measured: an ungrouped split-table evaluator (`bitstat6.log`) saves ≈ 0.25 s grouping per prototype but
  costs +85–120 ms of `askV` per prototype; per badge batch (start-up once, 8 checks) it is a net loss. Not taken.
- Split the generator: **`bitTGB`** (decomposition rows at the seed, `bitOf` after-rows, `bits n` aux; covers only
  `selectHalf`/`tensorW`, never imports → `ATImp` vacuous) and **`bitTGR`** (sibling and unaligned statement reads,
  `ATImp` classes: proofs pending). `bitTG = bitTGB.addD bitTGR` (probe: the full fold).
- New `FRNodeRows4AskBS`: `AT.addD`, `askCtx_addD_left/right`, `atAsk_addD`, `atImp_addD`, `atOk_addD`,
  `opOut_selectHalf_imp`, `tplExt4_imp_tc` (the template-free context agrees on the import flag at
  `selectHalf`/`tensorW`), **`atImp_bitB`**, `XofA`, `bitTabP`, `withBitsB`, **`askFold_bitsB`**,
  **`gap4Imp_of_bitsB`** (ASK-T's `gap4Imp_of_askT` over `withBitsB askAq`), controls.
- Folding `bitTGB` into `askTG` breaks ASK-T/IMPC's `rfl` folds (`withImpc_askT`'s `askTGI := askTG`,
  `askFold_askT`, hence `gap4Imp_of_askT`): local patches (the RESULT's diffs) restate `askTGI` as the pre-fold
  generator and drop `askFold_askT`/`gap4Imp_of_askT` (replaced by mine). Full build with the fold started.
- `FRNodeRows4AskBL` (low): `F.bit`, `eBit`, `bit_eBit`, `bit_bitsLin`, `decomp_cell` (from `scratch/Bits.lean`).
  `tplExt4_tw_imp` (from `scratch/Tw.lean`) closes `tplExt4_imp_tc`'s `tensorW` case.
- **HEAD's `FR` fails**: duplicate `FR.N4s.ctlP` (`FRNodeRows4RepCtrl`, `FRNodeRun4AskT`); renamed locally (`ctlPT`).
- Full build with the phase-1 fold green (5,031 jobs); axioms 21 decls ok; source rule 454 files 0 findings;
  kernel 0.12 / 0.12 / 0.11 s type checking.
- `plan4t init` A/B (real process): base 7.23–7.60 s user, phase 1 folded 8.26–8.40 s: +0.9 s.
- The build tree is left at `FOLD=0` (the A/B baseline); `python3 -I patch.py` after `snap.sh` restores the fold.
- RESULT written (`IMPC2-RESULT.md`). Open: `atImp_bitR`, the run proofs (`execA_idx`, `SlotRunB`).
