# RSV-S3 JOURNAL: `finPf`'s reserve chain, `W₀` at 69 cells, the switch to `StmtN4R`

Track RSV-S3, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `50a7f52`.
Build tree `logs/fr-build-RSVS3` (copy of `fr-build-RSVS2a`); logs `logs/RSVS3/`. No sub-agents,
nothing committed.

## 1. Setup

- `cp -a logs/fr-build-RSVS2a logs/fr-build-RSVS3` (42 s). Scripts log to `../RSVS3/`.
- `mymods.txt` = every `FRSoundness4*` module plus `FRNodeStmtR4`, `FRNodeSound4K` (101 modules,
  symlinked to the worktree); every other module is HEAD's text. `patchdec.py`: RSV-S's decoder patches
  plus a generic section that sorries the declarations listed in `autosorry.txt` (other tracks' reds,
  build tree only); `autosorry.sh` from RSV-S2b.
- Baseline `logs/RSVS3/b0-baseline.log`: all deps cached; `R4PfFlag:130` (`gFinPf_reloc`) whnf
  timeout, as handed over.

## 2. Work log
- `R4PfRun`: `gCellsPwK` (the chain's last power register), `gCellsPwK_eq`; `run_gCellsOpsK` gains
  the conjunct `(rd … (gCellsPwK nc n pw b)).toF = Pw·κ′ⁿ` (its only user is `R4PfFlag`). `b1.log` green.
- `R4PfFlag`: `gFinPfR` with `gFinPf`'s second chain (`c9`, `acc9`, `cr`, `ce := cond rsvOps (cr+1) c9`,
  the `keep rsv`, `.keep node (cond rsvOps cr acc9) z0`), parenthesised as `gFinPf` after
  `cond_true`; `map_cond`; `gFinPf_reloc` builds again with its old shape (`simp only` + `rfl`).
  New `cv4`; `w0V4`'s cell term: `if rsvOps ∧ rsv then cellsVal4 … rcells nrcell 0 (κ′²·κ′^ncell) cv4
  else cv4`. New `pr_rebase`, **`run_rsvChain`** (the gated second chain + `keep`, generic registers,
  continues from `run_gCellsOpsK`'s accumulator and power). `flag_gFinPf4`: B9 (first chain) → B9′
  (`run_rsvChain` from `R8` with prefix `M9`) → B10 at `cond rsvOps cr acc9`. Built first time
  (`b3.log`), no big simp.
- `R4W0R`: **`cells2_sum`** (two chains = `Σ_k κ′^{k+2} eq(cell_k)` over `cs ++ rs`, with the gate off
  `rs = []`); `w0V4_eq4`, `wV4_of_fields`: `hcl : P.cells ++ P.rcells = cellsC cells κc` and new
  `hrc : P.rcells.length = if rsvOps ∧ rsv then nrcell else 0` (N8: `nrcell = 60`, `rcells = []`).
  XRun passes `rfl` (segment) and `by cases ν <;> rfl` (node). `b4.log` green.
- Autosorry round 1 (`auto-1.log`): `R4FrCtrl.relE4_rejects` red (mine; RSV-S2a's `relE4` now
  branches on `rsvOps`): proof cases on `rsvOps` too, statement unchanged. PORT's reds sorried in the
  build tree: `FRNodeLinks4.acceptRunL4_node`, `FRXOut4.reassemble4_size`, `FRXOut4.pf4_size`.
- Item 6 (the `StmtN4R` switch, PORT-safe form): `FRNodeStmtR4`: `X4.Resid4R`, `resid4R_of`,
  **`certificate_rev4R`** (`ks_rev4R`). `XRunG` imports `FRNodeStmtR4`: `ks_rev4HR`, `Resid4HR`,
  `resid4HR_of_H`, `resid4R_of_HR`, **`certificate_rev4HR`**; `ks_rev4H`/`certificate_rev4H` keep
  their statements and are now proved through the R forms. `FRNodeSound4K`'s `P4f.ks_rev4H`,
  `Resid4H.gap`, `certificate_rev4H` (no users outside) are over `StmtN4R`; the `GH` forms (B4's
  PackSound uses them) keep their statements. `b6.log` green (Sound4K, XFinal, R4Full, PfFin).
- Full build loop (`autosorry.sh FR Solution`, logs `auto-<i>.log`): PORT's reds sorried in the
  build tree as they appear (`autosorry.txt`: `FRNodeLinks4.acceptRunL4_node`, `FRXOut4.reassemble4_size`,
  `pf4_size`, `FRNodeLinks4Run.fmAns_of_run4`, `FRXOut4W.segTr_eq`, `signedWords_agg`, `sgnX_fits`,
  `readW4_fits`, …).
- Line counts (`loc.py`, code lines HEAD → now): PfRun 402 → 414, PfFlag 507 → 587, W0R 233 → 251,
  FrCtrl 44 → 45, XRun 222 → 223, XRunG 105 → 147, StmtR4 160 → 190, Sound4K 75 → 76.
- Build at `50a7f52` green (`auto-12.log`, kept in `at-50a7f52/`). Axioms: 26 theorems clean;
  `certificate_sub4`'s `sorryAx` from PORT's stubs only (`sorrydeps.log`).
- Kernel: whole-closure KReplay (`kr/`, 12 min, calibration factor 2.504 vs H-cert3's 7763), per-module
  table `kernel-table.txt`; sequential profiles `prof-summary.txt`.
- Orchestrator: PORT committed (`c4eca2b`), HEAD `253516c` then `154744b` (B4 `7537acd`). Re-snapshot onto
  `154744b`, old decoder/B3 stubs dropped (`patchdec-50a7f52.py` keeps them). Reds at HEAD: PORT's
  `FRNodeLinks4.acceptRunL4_node` (still `cells := cells4`; with W₀ at `cellsX` it needs this track's
  `hrc` and `cellsX`: edit verified in the build tree only), `FRXSig4H.xRows_of_stmt` (max recursion
  after B4's `FRNodeRows4Ext`; stubbed). `final.log` green, 2,640 jobs. Axioms at `154744b`: all 27
  clean incl. `certificate_sub4`.
- `gap4Imp_of_rsv`: not started (needs a prefix form of `compileX_run`); plan in RESULT §5.4.
