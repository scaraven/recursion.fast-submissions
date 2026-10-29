# INT-9 journal (track L-circ integration): 4.1 `shiftMask` templates on INT-8's uniform programs; the node's `evalM`/`evalL`; the node dump and plan form

2026-10-29. Base HEAD `04f56e1` (P2⁗ `a201960` + queue rulings) with S-E12e's uncommitted L-circ work.
Build tree `logs/fr-build-INT9` (copy of `fr-build-SE12e`, against `logs/org20`; `MINE.txt` +
`FRVIR4Mux`). Logs: `logs/INT-9/`. Every lean/lake/probe command in a 16 GB scope with a timeout.

## A. Merge

- Clash `FR.Rev4.nodeQ` (INT-8's `FRVIR4Mux.nodeQ cells : Kind → FinP` vs S-E12e's
  `FRNodeRows4.nodeQ ν : ℕ × ℕ × ℕ`): S-E12e's renamed **`maskQ`** (it is the `shiftMask`
  constants), in `FRNodeRows4`, `FRVIRTpl4Bridge`, `FRVIRTplMaskN` (doc). INT-8's kept.
  `FRVIR4Mux` not edited.
- `protoProg 0 := progNodeGK N4c.cells4` (was `progNodeG (cells4 .N4)`); `protoProg 1 = progSegG`
  (INT-8's uniform segment group, unchanged name).
- `lake build FR FRVIRTpl4Bridge FRNodeRows4Fit FRNodeRows4Model FRVIRTplSet`: green, 2,522 jobs
  (`build-mergeA.log`).
- `laydump4` (2.7 s): new layouts; **`tensorW 19/16/13/10` gone from both prototypes, `eqPt 17 17`,
  `eqPt 23 23` gone from prototype 0** (their operands are kind-dependent in the uniform group, so
  `tplExt` leaves them imports). Hint regenerated.
- `plan4t check` (`plan4t-check.log`): keys 96 (was 100), pieces 5,658 + 5,662, `inR true`;
  `evalMT4` = sparse sum for N2, N4, N8 (best 80.6 / 77.7 / 54.4 ms).
- Plan start (`plan4t-init-{1..5}.log`, core 29, load ≈ 11): 1.72, 1.73, 1.80, 1.73, 1.69 s.

## B. The node's `evalM`/`evalL`

- New `FRVerifierImplNode4F` (`FR.NI4F`). `evalL4I`: the row point's base-512 tables (`bt`), the
  cell point split at 14 coordinates (`eqAtR_splitK`, new: `eqAtR_split9` generalised), per slot one
  pass over its 8,220 rows (pairs: `Σ eq(rL,i)`, `Σ eq(rL,i)·eq(r4_lo,299+j)`). `evalL4I_eq` against
  `Eval.evalRowsSpec logL (m−7) (lRows4 κ)`, via `evalRows_eq`/`sparseEval` and `sum_range_mul`.
- Pitfalls:
  - `congr 1` on a goal over `List.range nJ` hit max recursion (it tries `rfl` and unfolds the
    8,220-element range): use `congrArg (_ ++ ·)`.
  - After `Prod.ext`, `Finset.sum_congr` got stuck on `AddCommMonoid ?m` until `dsimp only`.
  - **OOM (16 G scope, twice)** in `implTF_implN4` / `routeOk_implN4F`. `exact h` with
    `h : KeyImpl (base ν) k` against `KeyImpl (implN4 …) k`, and `routeOk_implN4 …` against
    `implN4F`, made the unifier compare the two `OpImpl`s by structure eta, field by field: it
    unfolded `shiftMask4I`'s tables and `evalMT4 planOf4`. The fix is
    `simp only [KeyImpl, implN4, Impl.withRS4] at h ⊢` (projections reduced first) and
    `routeOk_node (impl := …) ι (by dsimp only [...])`.
- `implTF_implN4` answers S-E12e's open question: it holds given `∀ ν, ImplT (base ν)`, and at
  `implC` by `implCWith_implT` (`implTF_implN4F_C`).
- Measured by S-E8's method (`vtime4 21 n4f`, core 30): V(N4) best 177.6 / 179.0 ms; `cn4` in the
  same session 172.5 ms; `evalL4I` alone 11.0–11.3 ms; per op `evalM` 85.1 ms, `evalL` 12.1 ms.

## C. Dump and plan form

- `nodedump4` (19 s), `protodump` (P2⁗'s `ProtoDump`, copied into `probe/`, 0.5 s), `planform4`
  (new probe, 2 s), all into `logs/INT-9/nodedump/`.
- Plan form: 869,157 / 871,735 bytes. `planform_kat.py` (58 s) rebuilds both prototypes' rows and
  matches `mrows` line for line: 428,815 / 427,104 rows, 0 differ, 0 non-unit coefficient products.
- Prototype 0 has 428,815 indexed rows (S-E12e: 487,391) and 27,386 import registers (26,639).
  The 745 `tensorW` and the Lr/E `eqPt` are imports again, because their operands are
  kind-dependent in the uniform programs.

## Checks

- Final build: `lake build FR FRVerifierImplNode4F FRVIRTpl4Bridge FRNodeRows4Fit
  FRNodeRows4Model FRVIRTplSet`, green, 2,523 jobs (`build-final.log`).
- Axioms (`ax/AxINT9.lean`, `axioms.log`): 39 declarations, all within the three. The file also
  holds the 3.x `rfl` checks and the R4 composition `not_rejFinE4_node … (implN4F_hM …)
  (implN4F_hL …)`.
- Source rule: 304 files, 0 findings.
- Sequential profiles: `FRVerifierImplNode4F` 9.7 s wall, 0.90 s type checking; `FRNodeRows4Plan`
  12.0 s, 0.56 s.
