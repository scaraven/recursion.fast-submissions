# SEG-R2 (track SEG-R): RESULT — `rtC1d` folded; the segment's replay ops leave the residual

Stage SEG-R2, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`; started at `9db5ee0` = CF2,
SEG-R1b committed meanwhile as `bb0880c`, HEAD now `3d2d4ef`). Build tree `logs/fr-build-SEGR2` (a copy of
`fr-build-SRA`, re-snapshotted by `snap2.sh`: HEAD by `git show`, my modules symlinked, every other non-HEAD
module removed; until SEG-R1b's commit its files were frozen copies in `logs/SEGR2/overlay/`, now
`overlay-applied/`). Pure-HEAD tree for the A/B: `logs/fr-build-SEGR2H`. Logs `logs/SEGR2/`. Every lake/lean/probe
in a 16 GB scope under `timeout`. Nothing committed, no sub-agents, no `sorry`.

## 0. Verdict

| item | status |
|---|---|
| 1. fold rewired `rtC1c` → `rtC1d` (`repAllRows`, `RepFit`, `repFitB`, the plan, RepF, SIB's `FRNodeRun4C*`) | **done**; prototype-0 lemmas unchanged (`rtC1d_zero : rtC1d 0 = rtC1c 0 := rfl` where a statement names `rtC1c 0`) |
| 2. constants and placement | **done**: `arR2N` 180,560 → 154,368, `arRb` 998,400 → 972,288, `repSegB` = 988,672 (`= arRb + arNb`, `repConsts`); rows: band B `[988,672, 1,015,808)` then band A `[688,128, 720,896)`; prototype 1's rows checked below band A at process start; locals in cell bands 2/1/3; `repV4`'s segment slots share one `rv₁`; `segRegion` = 38,805 |
| 3. uncovered replay ops fail in the circuit | **done**: `TG.repF` (a failing row at an `isRep` op neither the ask template nor `rtC1d π` covers), folded in `askTG` before the closure; `impQP (rtC1d π) (withRep …) π = []` by a structural induction (`impQX_repF`), no evaluation of the compile |
| residual | **`SlotRunF`**: the `felems` auxiliary cells only (§3). `gaps4_of_runF : (… → SlotRunF …) → Sub4.Gaps4` |
| 4. honest completeness | 0 failing rows (both prototypes), 0 rejecting replay rows, residual replay imports none, replay locals clash with nothing (N2, segment slot); `plan4t check` N2/N4/N8 **equal true**; MxKat **PASS** (33 × true) |
| measurements | `plan4t init` user **+0.5 s** (7.7–8.0 → 8.3–8.5 s), RSS +80 MB; V(N4) **+56–80 ms** (best 902/929 → 982/985 ms) |
| build / axioms / source rule | `lake build FR Solution FRSubmission4Fin FRNodeRows4Model` green, 2,705 jobs (`build-final.out`, `build-final.log`); 29 declarations incl. `Challenge.certified` ⊆ {propext, Classical.choice, Quot.sound} (`axioms.log`); source rule 480 files, 0 findings (`source-rule.log`) |

**`certified` is not re-routed**: its hypothesis stays `Open4F = Gaps4`. `gaps4_of_runF` gives `Gaps4` from the
`SlotRunF` form, but `Gaps4` does not give `SlotRunF`, so making `Open4F` the `SlotRunF` form would change
`certified` to a non-comparable theorem rather than strengthen it. The bridge is the theorem.

## 1. The import-order problem, and the move (`FRNodeRows4SegD`, new)

`rtC1d`, `rtSeg1`, `kRSS`/`kTSS`/`kSTS` and the wrapper `rtKD`/`rtEvZ` were defined in modules **downstream of
`FRNodeRows4`** (`RepSegK → RepK → RepCFP → RepFD → FRNodeRows4`; `RepSeg` also imports `FRSubmission4V`, which
is downstream of the plan). So neither `repAllRows`/`askTG` nor the plan could name them, and importing
`FRNodeRows4RepSeg` is impossible (a cycle). As REPF did with `FRNodeRows4Defs`, the **definitions moved
verbatim, names and namespaces kept**, into `FRNodeRows4SegD` (imports `FRNodeRows4Defs`, `FRVIRTplSegR`,
`FRVIRTplSegT`; imported by `FRNodeRows4`): from `RepSegK` `KOpD … rtKD`, `isEvML`, `zeroF3`, `rtEvZ`; from
`RepSegT` `tssIn`, `tssLay`, `kTSS`, `stArgs`, `stsIn`, `stsLay`, `kSTS`; from `RepSeg` `isRSS … kRSS`, `cbRSS`,
`cbTSS`, `cbSTS`, `rtSeg1`, `rtC1d` (SEG-R1b's final definitions, checked byte-equal against `bb0880c`), plus
`rtC1d_zero`. `KOkD` and every theorem stay where they were; the three modules only lose the definitions (and
gain a note). Nothing is duplicated.

## 2. What was built, per file (code lines by `scripts/loc.py`: total/code, HEAD → now)

- **`FRNodeRows4SegD`** (new, 210/107): the moved definitions (§1).
- **`FRNodeRows4RepSegK`** (319/223 → 229/165), **`FRNodeRows4RepSeg`** (375/280 → 331/253), **`FRNodeRows4RepSegT`**
  (170/111 → 148/98): definitions removed (§1), docs.
- **`FRNodeRows4Defs`** (481/236 → 511/246): `segCell`, `segCap = 52,462`, `repMapC` (a prototype-1 local
  `c ≥ repB` ↦ `v·2^20 + segCell (c − repB) + oneCell`), `repSegB = 988,672`, `segBN = 27,136`, `repA = 688,128`,
  `segRN = 59,904`, `segRow`, `repRowI`; `repIRowsW` places row `k` at `repRowI κ v k`.
- **`FRNodeRows4ArenaPlace`**: `arR2N`, `arRb` (above), `a1Rows4_ctl`'s row literal (901,461 → 875,269).
- **`FRNodeRows4AskC`**: `TG.repF A rc`.
- **`FRNodeRows4`**: imports `SegD`; `askTG π` = SIB's chain `|>.repF (rtC1d π).cov` then `.close`; `repCellOk 1`
  admits locals `< repB + segCap`; `repFitB 1` admits `segRN` rows; `RepFit` (below); `repAllRows` at `rtC1d`.
- **`FRNodeRows4Fit`** (971/821 → 1037/879): `repConsts` (restated), `segCell_lt`, `segRow_band`, `segRow_inj`,
  `slotA_idx1` (a segment slot's own rows avoid band A), `repIRowsW_mem`, `repFitB_spec`, `rep_fit1` (rows in band
  B or A), `rep_fit` (statement unchanged, proof: band A via `slotA_idx1`, injectivity of `segRow`); `hfit4` unchanged.
- **`FRNodeRows4Plan`** (1675/1239 → 1792/1334): `segLocC`, `seg1Loc` (prototype 1's replay rows in a segment
  region's local coordinates); `Plan4.rg1`/`hrg1` (grouped `seg1Loc` rows); `inR` adds
  `ivBelow keys pc1 (slotM4 + repA)`; `LCx.rv1`, `rv1Of`, `rv1Of_get`, `CxAt`'s fourth conjunct; `repMapC_term1`,
  `linE_rep1`, **`repV1_eq`** (a segment slot's replay value = its region's high factors × prototype 1's local
  value); `repV4`'s segment branch `smul3 (hiF·hiF·u u) cx.rv1.get`; `repV4_eq`, `repAllRowsP`, `repFit_iff`.
  **`evalMT4_eq`, `slots_val`, `rvOf_get`: statements unchanged.**
- **`FRVerifierImplNode4F`**: `evalMX4` builds `rv1Of` once (shared by every kind); `evalMX4_eq` unchanged.
- **`FRNodeRows4RepFD`**: `arRepOf` (the fallback thunk) at `rtC1d`.
- **`FRNodeRows4Rep`, `FRNodeRows4RepW`**: `repIRows4` / `repHoldsW_of` use `repRowI` (as `repIRowsW`).
- **`FRNodeRows4RepF`**: imports `RepSeg`; `repFold` at `rtC1d`; `repOk_rtC1dB`.
- **`FRNodeRun4CB`** (277/203 → 357/260): `AT.repF`, `toAT_repF`, `repF_rows`, `isRep_item`, `askCtx_repF`,
  `atAsk_repF`, `atImp_repF`, `atOk_repF`, `impQX_repF`, `impQP_repF`, **`SlotRunF`**, `slotRunC_of_F`.
- **`FRNodeRun4CT`** (215/155 → 237/168): `withRep`, `withClose` over it, `close_rowsB` and `gap4Imp_of_close`
  through the `repF` layer, `gap4Imp_rtC1dC`, `gaps4_of_runC` at `rtC1d`/`withRep`, **`gaps4_of_runF`**.
- **`FRNodeRows4RepFCtrl`**: controls restated; `segCell_ctl` new.
- **`FRNodeRows4Model`**: `segRegion`'s `R` 49,000 → 38,805 (measured); totals N2 3,513,298, N4 5,453,884, N8
  7,762,344 (1.029× under `N_M/1.05`).

## 3. The residual, exactly

`gaps4_of_runF` (`FRNodeRun4CT`): `Sub4.Gaps4` from

```
∀ vk κ w c₁ c₂ ch, StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
  ∀ v, Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
    SlotRunF (implP implB (fun _ => implB) (protoOf κ v) ι) (protoOf κ v) ι (slotIn …) (slotTr …) (slotAsg κ v w)

SlotRunF impl π ι inp tr w := ∀ s, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
  ∀ a ∈ (protoCS π).aux, isBitsA a = false → a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)
```

i.e. only the non-bits auxiliary cells (871 `felems` per prototype, `segstat-stat.log`). The replay-import
conjunct of `SlotRunC` is gone by `impQP_repF` (`rtC1d` covers every replay op of prototype 1; any replay op
neither it nor the ask template covers gets `failRT`, so it is no residual — this answers SEG-R1's open question 1
and the review's should-fix 2).

## 4. Statement changes

| Declaration | Change |
|---|---|
| `RepFit` | `(∀ π ≤ 1, repFitB π (repRowsP (rtC1d π) π)) ∧ ∀ p ∈ protoRows 1, p.1 < slotM4 + repA` (was `∀ π ≤ 1, repFitB π (repRowsP (rtC1c π) π)`) |
| `repCellOk 1`, `repFitB 1` | prototype 1 may use locals `< repB + segCap`; up to `segRN` rows (was frame cells only, `2^10` rows) |
| `repAllRows`, `repFold`, `repIRowsW_mem`, `rep_fit1`, `repIRowsWP_eq`, `repV4_eq` (+ hyp `σ < κ.vslots`), `arRepOf_eq`, `Plan4.hrp`, `mkPlan4`'s `hrl`/`hrp`, `DataOk` | `rtC1c` → `rtC1d`; `rep_fit1`'s segment clause is "band B or band A" |
| `repIRowsW`, `repIRows4` (defs) | row index `repRowI κ v k` (was `repRow0 κ v + k`; equal for prototype 0) |
| `repMapC` (def) | prototype-1 locals into the region's bands (was: spare region) |
| `repSegB`, `arR2N`, `arRb` | 1,014,784 → 988,672; 180,560 → 154,368; 998,400 → 972,288 |
| `repConsts` | restated (`arRb + arNb = repSegB`, `repSegB + segBN + linkN = slotM4`, `repA + 2^15 = arR2`, …) |
| `askTG` (def), `withClose` (def) | the `repF` layer before the closure |
| `gap4Imp_of_close` | its `SlotRunC`'s template `withSib` → `withRep` |
| `gap4Imp_rtC1cC` | renamed `gap4Imp_rtC1dC`, at `rtC1d`/`withRep`; `gaps4_of_runC` likewise |
| `Plan4`, `LCx`, `CxAt`, `innAt_thsOf` | new field `rg1`/`hrg1`; new field `rv1`; new conjunct; extra argument |
| controls | `repCellOk_ctl`, `repFitB_len` (`segRN`), `repRow0_ctl` (bands), `a1Rows4_ctl` (row literal), `mRowModel4_eq`, `regions_sum` |

Unchanged: `Gaps4`, `Open4F`, `certified`, `hfit4`, `rep_fit`, `slotA_idx`, `evalMT4_eq`, `evalMX4_eq`, `slots_val`,
`rvOf_get`, every prototype-0 replay lemma (CF/CF2's `blk0`, `arBlk0_eq`, `repV0_eq`, `repFitS_spec`), `rtC1d_ok`,
`repOkW_rtC1dB`, `kRSS_ok`, `kTSS_ok`, `kSTS_ok`. New theorems are listed in §2.

## 5. Measurements (logs under `logs/SEGR2/`)

- **Honest compile** (`segstat-stat.log`, probe `probe/SegStat.lean`): prototype 0: `askTG` 130,914 rows, **0
  `failRT`**, replay rows 562,758, 0 rejecting, residual replay imports none (its one replay op `rtN0c` misses is
  covered by the ask template, so `repF` does not fire); prototype 1: `askTG` 154,333 rows (`arR2N` 154,368: 35
  rows of slack), **0 `failRT`**, **replay rows 38,805, 0 rejecting**, local extent 41,226 (< `segCap` 52,462),
  residual replay imports none; `protoRows 1` last row `2^20 + 686,079` < band A `2^20 + 688,128`.
- **Placement** (`segstat-fitN2.log`, `nodeIRowsP planOf4 .N2`, 3,395,406 rows): plan `inR` **true**; segment slot 1:
  38,805 replay rows found at their indices; 38,486 replay local cells, **0** shared with any other row's cells,
  the skeleton, the template instances, arena₁ or the bits. Rows: band B 27,136 + band A 11,669.
- **`plan4t check`** (`plan4t-check.log`): N2 equal **true** (sparse 232 s), N4 **true** (368 s), N8 **true** (518 s).
- **MxKat** (`mxkat.log`, CF2's reference: each slot's replay rows as a plain sparse sum over `repIRowsWP`, so
  the segment slots' 38,805 rows each, independent of `rv1`): **MX KAT PASS**.
- **`plan4t init`** A/B (`init-ab.log`, core 27, alternating; A = pure HEAD tree `fr-build-SEGR2H`, B = this):
  A 7.92/7.96/7.71 s user, B 8.40/8.33/8.51 s; RSS 0.88–0.93 → 0.98–0.99 GB.
- **V(N4)** A/B (`v-ab.log`, core 28, `vtime4 21 n4f s4`, 2 rounds): `runSeq` best A 902.2/929.3 ms, B 981.7/985.3
  ms; `evalMT4 N4` best 816/831 → 893/879 ms; `evalMX4` all-supports best 844/875 → 954/929 ms.
- No node honest ACCEPT (E1 re-dump pending, as instructed); the segment ACCEPT after the pin is SEG-R1b's
  (`logs/SEGR1b/acc/verify-final.log`).

## 6. Kernel / elaboration (`lean -DElab.async=false --profile`, core 26; `prof-summary.txt`, `profile-*.log`)

| module | type checking (now) | HEAD | tactics |
|---|---|---|---|
| `FRNodeRows4SegD` (new) | 0.05 s | — | — |
| `FRNodeRows4Defs` / `ArenaPlace` / `AskC` / `FRNodeRows4` | 0.08 / 0.03 / 0.12 / 0.18 s | ≈ same | ≤ 0.16 s |
| `FRNodeRows4Fit` | 5.35 s | 5.01 s | 3.9 s |
| `FRNodeRows4Plan` | 1.61 s | 1.30 s | 5.7 s |
| `FRVerifierImplNode4F` | 1.22 s | 1.12 s | 1.8 s |
| `FRNodeRun4CB` / `CT` | 0.16 / 1.09 s | 0.12 / 0.82 s (SIB) | 1.0 / 0.6 s |
| `FRNodeRows4RepF` / `RepFD` / `RepFCtrl` | 0.003 / 0.02 / 0.02 s | — | — |
| `RepSegK` / `RepSeg` / `RepSegT` | 0.12 / 1.21 / 0.34 s | (moved defs only) | |

On `certified`'s path (Fit, Plan, ImplNode4F): **≈ +0.75 s** type checking. `CT`/`CB` are off the path (the
hypothesis is not routed). No `decide` over a closed table; the new `decide`s are controls on literals.

## 7. `FR.lean`

No import change is required: `FRNodeRows4SegD` is reached through `FRNodeRows4`, and `FR.lean` already imports
`FRNodeRows4RepSeg`, `FRNodeRows4RepF`, `FRNodeRows4RepFCtrl`, `FRNodeRun4CT`, `FRNodeRows4Model`. (Optional, for the
module list: `import FRNodeRows4SegD`.)

## 8. Prover cells (E1; extends SEG-R1-RESULT §8) — the final map per segment slot `v`

Absolute cell = `oneCell + v·2^20 + x`; row = `v·2^20 + y`.

- **Replay rows** `k < 38,805` of `repRowsP (rtC1d 1) 1`: `y = 988,672 + k` for `k < 27,136` (band B), else
  `y = 688,128 + (k − 27,136)` (band A, 11,669 rows).
- **Locals** `j = c − repB`: `targetS` `[0, 2^9)` (`cbTSS`: mux, then `tsSegT`'s 55), `shiftTarget` `[2^9, 2^12)`
  (`cbSTS`: mux, then `stSegT`'s 1,301 incl. the 512 digest bits), `rsWeight` `[2^12, 2^12 + 37,130)` (`cbRSS`: 207
  mux, 36,923 template). Cell `x = segCell j`: `277,402 + j` (`j < 4,096`, band 2), `405,504 + (j − 4,096)`
  (`j < 39,744`, band 1), `1,003,010 + (j − 39,744)` (band 3: `rsWeight`'s last 1,482). 38,486 local cells.
- Values: gate evaluation in order (mux locals `sel_ι·f_ι`; template locals by the templates with `kdIn`'s hints),
  the six dead cells `r57244..46`, `r57251..53` = 0, the bits of `s`, `h` for `shiftTarget`.
- **Row moves in every region** (no cell moves): arena₁ rows `[875,264, 972,208)`, bits rows `[972,288, 988,672)`
  (were `[901,456, 998,400)`, `[998,400, 1,014,784)`); any dump or E1 table with row indices must be regenerated.

## 9. Notes and open items

1. **`arR2N` has 35 rows of slack at prototype 1** (154,333 used): any further ask-template rows at prototype 1
   make `ArFit` fail at process start (the plan falls back; honest proofs then fail). FEL's route claims 0 rows.
2. During SEG-R1b's work its `FRVIRTplSegT` defined `FR.Tpl.eqF`, which clashed with CF2's `FRVIRTplRepLG` once
   both are imported; the committed version (`rgEqF`) does not.
3. V +56–80 ms comes from `rv1` (38,805 rows sparse once per check, grouped at plan time); a CF-style closed form
   for `rsSegT` would remove most of it (not needed for acceptance).
4. Fit probe run on N2 only (the segment region's layout is region-relative, so N4/N8 are the same; N8's region 0
   holds no prototype-0 rows).
