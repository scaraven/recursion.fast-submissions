# INT-9 (integration, track L-circ): RESULT. The 4.1 `shiftMask` templates on INT-8's uniform programs; the node's `evalM`/`evalL`; the node dump and its plan form

Stage INT-9, 2026-10-29. Base HEAD `04f56e1` (P2⁗ `a201960` plus the queue rulings), with S-E12e's
uncommitted L-circ work. Build tree `logs/fr-build-INT9` (a copy of `fr-build-SE12e`, against
`logs/org20`). Logs are in `logs/INT-9/`; the journal is `INT-9-JOURNAL.md`. Every lean, lake,
probe and python command ran in a 16 GB scope with a timeout. Nothing is committed.

## Status

| Item | State |
|---|---|
| A. Merge S-E12e onto INT-8 | **Done.** The `nodeQ` clash is resolved: S-E12e's is renamed `maskQ`. `protoProg 0 = progNodeGK N4c.cells4`. Hint regenerated. `plan4t check`: `inR true`, and `evalMT4` = the sparse sum for N2, N4, N8. Plan start 1.69–1.80 s. `ImplTF keys41 (implN4 …)` proved. |
| B. The node's `evalM`/`evalL` | **Done.** New `FRVerifierImplNode4F`: `implN4F`, `implN4F_meets`, the new `evalL4I` with `evalL4I_eq`, and `hM`/`hL` in R4's form (kernel-checked against `not_rejFinE4_node`). V(N4) best 177.6 / 179.0 ms (VM). |
| C. The node dump | **Done.** `logs/INT-9/nodedump/` holds `proto-p{0,1}.txt` and `plan-form-p{0,1}.bin` (869 KB / 872 KB). The plan form's KAT against `mrows` passes byte for byte. `SHA256SUMS` and the README are written. |

**One regression.** In the uniform programs, 745 `tensorW` and two `eqPt` are no longer templated
(finding F1 below).

## A. The merge

- **`nodeQ`.** INT-8's `FRVIR4Mux.nodeQ cells : Kind → FinP` is kept. S-E12e's
  `FRNodeRows4.nodeQ ν : ℕ × ℕ × ℕ` (the `shiftMask` constants) is now **`maskQ`**, also in
  `FRVIRTpl4Bridge` and in a doc comment of `FRVIRTplMaskN`. `FRVIR4Mux` is not edited.
- **`protoProg`.** `protoProg 0 = progNodeGK N4c.cells4`, so each node kind uses its own public
  cells; INT-8's "For L-circ" asked for this. `protoProg 1 = progSegG`, which is INT-8's segment
  group. Both are checked by `rfl` in `ax/AxINT9.lean`.
- **Hint.** `laydump4` (2.7 s, `laydump4.log`) gives new layouts in `FRNodeRows4Hint`. Prototype 0
  has 19 keys (was 25) and prototype 1 has 21 (was 25); see F1. `maskN` and `shiftSeg` keep their
  rows (393,216 and 391,168).
- **Plan** (`plan4t-check.log`):
  - 96 keys (was 100); 5,658 + 5,662 pieces (instances 4,648 + 4,650); `inR true`;
  - `evalMT4` equals the sparse sum over `nodeIRows4` for N2, N4 and N8;
  - best times N2 80.6 ms, N4 77.7 ms, N8 54.4 ms.
- **Plan start** (`plan4t-init-{1..5}.log`, core 29, load ≈ 11): 1.72, 1.73, 1.80, 1.73, 1.69 s.
  This is within the 2 s bound.
- **S-E12e's open question.** `NI4F.implTF_implN4` proves
  `(∀ ν, ImplT (base ν)) → ImplTF keys41 (implN4 base tS ν)`:
  - `withRS4` changes only `rsWeight`, which no kept key reads;
  - `slotW` is `slotWI`;
  - `shiftMask` is outside `keys41`.

  `implTF_implN4F` gives the same for `implN4F`, and `implTF_implN4F_C` gives it at the 3.x base
  `implC` (by `implCWith_implT`). `routeOk_implN4F` gives the route. With S-E12e's
  `protoCS_soundAt`, the node soundness consumer has both hypotheses.

## B. The node's `evalM`/`evalL`: `FRVerifierImplNode4F` (new; 236 code lines, 25 theorems)

- **`evalL4I κ rL r4`** is L's three matrices at `logL` row coordinates and `m − 7` cell
  coordinates:
  - `lRows4_eq`: row `i = σ·8220 + j` of `lRows4 κ` is `b·(1 − b) = 0` at
    `b = cellL κ i = lBase·128 + σ·2^14 + 299 + j`.
  - The row point's eq values come from S-CN4's base-512 tables `bt` (768 entries).
  - The cell point is split at 14 coordinates (`eqAtR_splitK`, a generalisation of
    `eqAtR_split9`). The low part is a `2^14` table read at `299 + j`. The high part is read at
    `lBase·128/2^14 + σ`, which needs `lBase·128 ≡ 0 mod 2^14` (`lCells_fit`).
  - Each slot then takes one pass over its 8,220 rows (`slotL`), which gives
    - A = `Σ_σ eq(r4_hi, hb + σ) Σ_j eq(rL, σ·8220 + j)·eq(r4_lo, 299 + j)`;
    - B = `(Σ_i eq(rL, i))·eq(r4, one) − A`;
    - C = `0`.
  - **`evalL4I_eq : evalL4I κ rL r4 = evalLS4 κ rL r4`**, unconditionally, where
    `evalLS4 = Eval.evalRowsSpec logL (m − 7) (lRows4 κ)`.
- **`implN4F base ν`** is `{ implN4T base ν with evalM := evalMT4 planOf4 ν, evalL := evalL4I ν }`.
  **`specN4F spec ν`** is `{ specN4 spec ν with evalM := evalMS4 ν, evalL := evalLS4 ν }`.
  **`implN4F_meets : (base ν).Meets (spec ν) → (implN4F base ν).Meets (specN4F spec ν)`**. The
  proof uses `implN4T_meets`, `evalMT4_eq` and `evalL4I_eq`. The statements of
  `FRVerifierImplNode4T` are not edited.
- **V(N4)** by S-E8's method (`vtime4 21 n4f`, VM core 30, 21 reps, load ≈ 3–5):

  | Configuration | Best | Median | Log |
  |---|---|---|---|
  | `implN4F` (final: S-CN4's ops, `targetSNode4I`, `rsWeightF4`, `evalMT4`, `evalL4I`) | **177.6 / 179.0 ms** | 183.4 / 187.1 ms | `vtime4-n4f-{a,b}.log` |
  | S-E12e's `cn4` (3.x `targetS` and `evalL` stand-ins), same session | 172.5 ms | 179.4 ms | `vtime4-cn4-a.log` |

  - Per op (`prof4-n4f.log`): `evalM` 85.1 ms, `evalL` 12.1 ms, `rsWeight` 9.8 ms, `walkAB`
    9.6 ms, `targetS` 1.95 ms, `linkWAll` 1.93 ms, `shiftMask` 0.13 ms.
  - `evalL4I N4` alone: best 11.0–11.3 ms. It does about 2 products per row over 41,100 rows,
    plus a `2^14` table.
  - At S-E12e's 1.19 VM/7763 ratio this is ≈ 149–150 ms against the 206 ms cap.

## For R4 (`hM`/`hL`, R4d D11)

`FRSoundness4R4FrE.e_fin4` and `not_rejFinE4_node` take `srcE srcL : NodeKind → P4b.ESrc` and
`hM`, `hL`. Instantiate them with:

```lean
-- FRVerifierImplNode4F (namespace FR.NI4F)
noncomputable def srcE4 (ν : NodeKind) : Snd.P4b.ESrc := Snd.P4b.ESrc.ofIRows (nodeIRows4 ν)
def srcL4 (ν : NodeKind) : Snd.P4b.ESrc := Snd.P4b.ESrc.ofRows (lRows4 ν)

theorem implN4F_hM (base : NodeKind → OpImpl) (ν : NodeKind) :
    ∀ r2 r4 : Array F, r2.size = Snd.P4b.e2R ν → r4.size = Snd.P4b.ncR ν → (implN4F base ν).evalM r2 r4 =
      (Eval.matMLE (srcE4 ν).ea (FR.Impl.ptA (Snd.P4b.e2R ν) r2) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcE4 ν).eb (FR.Impl.ptA (Snd.P4b.e2R ν) r2) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcE4 ν).ec (FR.Impl.ptA (Snd.P4b.e2R ν) r2) (FR.Impl.ptA (Snd.P4b.ncR ν) r4))

theorem implN4F_hL (base : NodeKind → OpImpl) (ν : NodeKind) :
    ∀ rL r4 : Array F, rL.size = Snd.P4b.lrR ν → r4.size = Snd.P4b.ncR ν → (implN4F base ν).evalL rL r4 =
      (Eval.matMLE (srcL4 ν).ea (FR.Impl.ptA (Snd.P4b.lrR ν) rL) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcL4 ν).eb (FR.Impl.ptA (Snd.P4b.lrR ν) rL) (FR.Impl.ptA (Snd.P4b.ncR ν) r4),
       Eval.matMLE (srcL4 ν).ec (FR.Impl.ptA (Snd.P4b.lrR ν) rL) (FR.Impl.ptA (Snd.P4b.ncR ν) r4))
```

- `srcE4` is `nodeIRows4`'s indexed entries. These are the rows S-G12′'s `truthE` is to be stated
  over (O1).
- `srcL4` is `lRows4` with row `i` at index `i`.
- The size hypotheses are not used; both equalities hold for every argument.
- The composition is kernel-checked in `logs/fr-build-INT9/ax/AxINT9.lean`:

  ```lean
  example … (h : semIR (implN4F base ν) (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L) :
      ¬ Snd.P4b.RejFinE4 srcE4 srcL4 L (fsOf tr (itemsOf seq4)) :=
    Snd.R4.not_rejFinE4_node srcE4 srcL4 (implN4F_hM base ν) (implN4F_hL base ν) h L
  ```

So the node's `impl` for R4 and X4 is `NI4F.implN4F base ν`, not `implN4`/`implN4T`. Its ops meet
`specN4F spec ν`.

## For P2 (the dump and the plan form)

The full description is `logs/INT-9/nodedump/README.md`. Checksums are in `SHA256SUMS`.

- **The programs are INT-8's uniform ones** (`progNodeGK N4c.cells4`, `progSegG`). S-E12c's
  obstructions 1 and 3 are gone from the rows, so an `N4`/`N2` child can be filled from these
  files.
- **`proto-p0.txt` and `proto-p1.txt`** use the `ProtoDump` format:
  - prototype 0: 106,485 ops, 97,657 registers;
  - prototype 1: 106,237 ops, 97,409 registers.

  The register counts equal `mregs-p{π}`'s line counts.
- **Counts:**

  | Prototype | Indexed rows | Rows in the region | Instances | Import registers | Aux | Foreign |
  |---|---|---|---|---|---|---|
  | 0 | 428,815 | 464,765 | 2,285 | 27,386 | 1,753 | 12 |
  | 1 | 427,104 | 460,669 | 2,287 | 27,401 | 1,753 | 79 |

  See F1 for the change against S-E12e.
- **Plan form, `plan-form-p{π}.bin`.** This is `Rev4.planOf4` (the README gives the full format):
  - Contents: the 96 keys' template rows once, the prototype's shared input forms, and its pieces.
    A piece is a run of sparse skeleton rows `(row, A, B, C)` or an instance `(key, xh, ch, own
    inputs)`.
  - Encoding: LEB128 varints, zigzag deltas for cells and rows, and a 431-entry coefficient table.
  - Rebuild: instance rows go at `2^A·xh + j`; locals at `2^B·ch + k`; input `i` is
    `(shared[k] ++ own)[i]` scaled by the coefficient; `one` is `one′`; terms are concatenated in
    Lean's order.
  - **Sizes: 869,157 bytes (prototype 0) and 871,735 bytes (prototype 1)**, against 100.7 MB and
    113.8 MB of `mrows`. The 336,675 bytes of keys are repeated in each file, so with the keys
    stored once the two prototypes take ≈ 1.40 MB.
  - The prover needs no `F` products to rebuild: every coefficient product has a unit factor (the
    KAT counts 0 others).
- **KAT.** `planform_kat.py <dir>` is a reference decoder. It rebuilds both prototypes and compares
  them with `mrows-p{π}.txt` line for line: 428,815 and 427,104 rows, 0 differ, `KAT PASS`, 58 s
  (`planform-kat.log`).
- **Unchanged from S-E12e:** the slot conventions, `node-N*.txt`, `maux`/`mregs` formats, the
  `maskN`/`shiftSeg` templates and their locals.

## F1. Finding: 745 `tensorW` and two `eqPt` are imports in the uniform programs

The prototypes lose these template groups (`groups-p{π}.txt` against `logs/S-E12e/nodedump/`):

| Prototype | Groups lost |
|---|---|
| 0 and 1 | `tensorW 19/16/13/10`: 290 + 178 + 145 + 132 = 745 instances |
| 0 | `eqPt 17 17`, `eqPt 23 23`: the Lr and E points |

The reasons:

- **`tensorW`.** Its index is `idx` with a kind-dependent bit count, for example
  `idx {L:r48801, …} {L:12, P:10, N:11}` (`proto-p1.txt` line 56,728).
- **`eqPt`.** The node's Lr/E points are `packFK` lists of unequal length (16/17 and 22/23
  coordinates). This is INT-8's deviation 1.

The compiler keys a template by its operands' fixed sizes, so these ops fall back to imports.

The cost is +747 import registers in prototype 0 and +745 in prototype 1, all unbound (they join
S-E12b §7's list for `hRes`). Rows fall by 58,576 and 57,712.

Nothing is unsound: imports are parameters of `compileTF4_soundAt`. But `hRes` now needs these
values bound some other way. S-E12d's prototype had them templated only because it ran `L32`'s
finals at every index.

Two ways to restore them:

1. **In the programs (INT-8/S-0, `FRVIR4Mux`).** Pad `idx`'s width to the group's largest (12);
   the high bits are zero on the smaller kinds. Pad the Lr/E points with zero registers (INT-8's
   open question 3: yes, the compiler needs it). Keep the unpadded copy for the `evalM`/`evalL`
   operands.
2. **In the compiler (L-circ).** Give a `tensorW`/`eqPt` with a kind-muxed size one sub-circuit
   per kind, muxed by the selectors as `tplMaskN` does. This is about 3× the rows of those
   instances.

I recommend option 1. Either way, the hint, the dump and the plan form must then be regenerated.

## What was built

| Module | New | Code lines (`loc.py`) | Theorems | Change |
|---|---|---|---|---|
| `FRVerifierImplNode4F` | yes | 236 | 25 | B, the R4 parameters, `ImplTF` |
| `FRNodeRows4` | edit | 95 (95) | 10 | `nodeQ` → `maskQ`; `protoProg 0 = progNodeGK N4c.cells4` |
| `FRNodeRows4Hint` | regenerated | 28 (34) | 0 | INT-8's programs' layouts |
| `FRVIRTpl4Bridge` | edit (S-E12e's, new) | 65 (65) | 13 | `nodeQ` → `maskQ` |
| `FRVIRTplMaskN` | edit (S-E12e's, new) | 217 (217) | 13 | doc comment only |

S-E12e's other files (`FRVIRTplSeg`, `FRVIRTplCore`, `FRVIRTplExt`, `FRVIRCompileSound`,
`FRVIRTplSet`, `FRNodeRows4Plan`) are taken as S-E12e left them.

The probes are outside the entry, in `logs/fr-build-INT9/probe`:

- `PlanForm4.lean` (new, the plan-form exporter);
- `ProtoDump.lean` (P2⁗'s, copied);
- `VTime4.lean` (+ mode `n4f`, + the `evalL4I` timing).

**`FR.lean` imports (request to its owner):** add `import FRVerifierImplNode4F`. This also brings
S-E12e's `FRVIRTpl4Bridge` into the closure. INT-8's request for `FRVIR4Uni` still stands.

## Checks

- **Build:**
  - `lake build FR FRVerifierImplNode4F FRVIRTpl4Bridge FRNodeRows4Fit FRNodeRows4Model
    FRVIRTplSet` is green, 2,523 jobs, no `sorry` (`build-final.log`).
  - The merge alone (A) is green, 2,522 jobs (`build-mergeA.log`).
- **Axioms** (`axioms.log`, `ax/AxINT9.lean`): 39 declarations, each within `propext`,
  `Classical.choice` and `Quot.sound`. They are:
  - the new ones;
  - the re-checked 4.1 statements (`planData4_rows`, `evalMT4_eq`, `protoCS_soundAt`,
    `maskNV_eq`, `compileTF4_soundAt`, …);
  - the untouched 3.x statements (`compileT_sound`, `tplExt_ok`, `evalMT_eq`, `implC_meets`,
    `compileTF_sound`, `compMS_T`, `node_m_sound`, `acc_eq`, …).

  The file's `example`s check:
  - by `rfl`: the 3.x instance (`compMS = compMSX tplExt`, `compileT`/`compileTF` as `compileX`),
    the two `protoProg`s, and `protoCS π = compileTF4 keys41 (protoR π) …`;
  - the R4 composition above.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 304
  files, 0 findings (`source-rule.log`).
- **Sequential profiles** (`Elab.async=false`, one core, `profile-*.log`):

  | Module | Wall | Type checking | Tactics |
  |---|---|---|---|
  | `FRVerifierImplNode4F` | 9.7 s | 0.90 s | 0.74 s |
  | `FRNodeRows4` | 7.0 s | 0.11 s | 0.08 s |
  | `FRNodeRows4Hint` | 6.1 s | 0.001 s | — |
  | `FRNodeRows4Plan` | 12.0 s | 0.56 s | 1.57 s |
  | `FRVIRTpl4Bridge` | 6.6 s | 0.09 s | 0.19 s |

## Controls

| Definition | (+) | (−) |
|---|---|---|
| `cellL`, `rowL` | `cellL_ctl`: row 0 is cell `lBase·128 + 299`, row 8,220 is `+ 2^14`; `lRows4_eq` | `cellL_ctl`: the two cells differ |
| `lRows4` (as used) | `lRows4_ctl`: `N4` has 5·8,220 rows, each with `C = []` | `lRows4_ctl`: `N2`'s count is not `N4`'s |
| `evalL4I` | `evalL4I_eq` (the MLE of `lRows4`, all arguments); measured 11 ms | its source is kind-specific (`implN4F_ctl`) |
| `implN4F` | `implN4F_ctl`: its `evalM`, `evalL`, `shiftMask` are the 4.1 node's; `implN4F_meets` | `implN4F_ctl`: `srcL4 .N4` and `srcL4 .N2` differ (A has 5·8,220 and 3·8,220 entries) |
| `srcE4`, `srcL4` | `implN4F_hM`, `implN4F_hL`, and the R4 composition | as above |
| the merged prototypes | `plan4t check`: `inR true`, `evalMT4` = the sparse sum (three kinds) | the dump: the 745 `tensorW` instances are gone (F1), so the hint follows the program |
| the plan form | `planform_kat.py`: 0 of 855,919 rows differ | a stale or truncated file fails the length and position asserts |

## Deviations

1. **`maskQ`.** S-E12e's `nodeQ` is renamed instead of reusing INT-8's: the two are different
   objects (the `shiftMask` constants against the finals' `FinP`).
2. **`evalL4I` is new code.** No 4.1 `evalL` existed: 3.x's `evalLT` is fixed at 15/23
   coordinates. It is a closed form over the slots, not a templated plan; `lRows4` is regular
   enough for that.
3. **The plan form carries all 96 keys in each file**, so each prototype's file stands alone.

## Open questions

1. **F1:** pad the group programs' `idx` widths and the Lr/E points (option 1)? This is an INT-8 /
   S-0 change in `FRVIR4Mux`, followed by an L-circ re-dump.
2. **`evalL4I` lever (≈ −4.5 ms on V).** Group each slot's rows by 512-blocks, so that `bt`'s high
   factor multiplies a block sum: about 1 product per row instead of 2. It is not done, because
   there is margin (≈ 150 ms projected against 206 ms).
3. The `mrows` header text still says `progNodeG`. I left it unchanged so that P2's parser is not
   disturbed; the README states the program.
