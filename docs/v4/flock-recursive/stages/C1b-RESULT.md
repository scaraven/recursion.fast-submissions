# C1b (track L-circ): RESULT — replay templates for the previous node's `targetS` and `evalL`

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`), final snapshot on **HEAD `44a4975`** (CK,
after R3 and ASK-P). Build tree `logs/fr-build-C1b` (copy of `fr-build-C1`; HEAD is green, so no
build-tree sorries). Logs `logs/C1b/`. Every lake/lean command in the 16G scope under `timeout`. No
sub-agents, nothing committed. Journal: `C1b-JOURNAL.md`.

## Status

| Item | State |
|---|---|
| `targetS` template (`tplTS ν a`, gate for gate `targetSNode4I ν`) | **Done, proved** (`tplTS_ok`), KAT true on N2/N4/N8 |
| `evalL` template (`tplEvL ν a b`, gate for gate `evalL4I ν`) | **Done, proved** (`tplEvL_ok`), KAT true on N2/N4/N8 |
| `KOk` / `RTOkW` level | `kTS_ok`, `kEvL_ok` (`KOk (implP impl₀ base 0 ι) ι _`); `rtC1b_ok`/`repOkW_rtC1b` (C1's `rtN0` + these two); **`rtC1c_ok`/`repOkW_rtC1c`** (R3's `rtN0R` + these two: all five prototype-0 ops) |
| Controls | `FRNodeRows4RepLCtrl` (§3) |
| Build | `lake build FRNodeRows4RepLCtrl` green at `44a4975`, 2,383 jobs (`logs/C1b/build-final.log`) |
| Axioms | 29 declarations ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx` (`logs/C1b/axioms.log`, `fr-build-C1b/ax/AxC1b.lean`) |
| Source rule | 447 files, 0 findings (`logs/C1b/source-rule.log`) |
| Register literals | **none**: the `KOp`s are keyed by constructor (`isTS`, `isEvL`) and read the operands from the op; CK's renumbering does not touch them |
| **V budget (the orchestrator's corrected cap: tens of ms)** | **Not met by `evalL`** (≈ 345 ms VM for its kind-muxed rows) and marginal for `targetS` (≈ 64 ms). Measured §4; levers §6 |
| Plan init | `targetS` 0.26 s, `evalL` 3.4 s from the final compile state (no second compile). **C1's `linkWAll` 216 s** (a construction trap in `FRVIRTplRepLW`, §4.2): must be fixed before the fold |

## 1. What was built (`loc.py`: total / code / thm; `logs/C1b/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRVIRTplRepLD` (new, defs only; imports `FRVIRTplRepLW` only, so the fold can import it) | 101 / 47 / 3 | `nJL`, `evCs`, `evT`, `evE`, `evN`, `evHb`, **`EvCx`/`mkEvCx`** (context built once), `evK2…4`, `evS2`, `tplEvLx`, **`tplEvL`**, `tplEvL_outs`, `mkEvCx_k1`, `mkEvCx_E` |
| `FRVIRTplRepL` (new) | 149 / 122 / 5 | `eqTable_getD_map`, `nJL_eq`, `evalL4I_sums`, `evE_ev`, **`tplEvL_ok`** |
| `FRVIRTplRepT` (new; imports `FRVIRTplRepLW`, `FRVerifierImplNode4T`: foldable) | 571 / 433 / 23 | pieces over table entries (`tsPA/PB`, `tsRngG/F` = `rangeI9`, `tsColT`, `tsCc`, `tsSepG/F`, `tsCtrKG/KO/Ks`, `tsCtrG/O` = `ctrArr`) and their lemmas; `tsCs`, `tsT`, `tsE`, **`TSCx`/`mkCx`**; offsets, accessors, `tsClsW` (= `clsW`), `tsFinG`, `tsW43`, `tsCT`, `tsGAt` (= `gAt4`), `tsG`, `tplTSx`, **`tplTS`**; `tsE_ev`, **`tplTS_ok`**, `tplTS_outs` |
| `FRNodeRows4RepLT` (new) | 193 / 133 / 8 | `isTS`, `tsArgs`, `tsIn`, `tsTpl`, **`kTS`**, `implP0_targetS`, **`kTS_ok`**; `isEvL`, `evArgs`, `evIn`, `evTpl`, **`kEvL`**, `implP0_evalL`, **`kEvL_ok`**; `cbTS`, `cbEvL`, `rtN0b`, `rtC1b`, `rtC1b_ok`, `repOkW_rtC1b`; **`rtN0c`, `rtC1c`, `rtC1c_ok`, `repOkW_rtC1c`** (on R3's `rtN0R`) |
| `FRNodeRows4RepLCtrl` (new) | 69 / 33 / 7 | controls §3 |
| **total** | 1,083 / 768 / 46 | |

No existing module was edited. `FR.lean` (orchestrator): `import FRNodeRows4RepLCtrl`.

```lean
theorem tplTS_ok (hi : InpIs e (r.toList ++ (#[] : Array F).toList)) (h1 : e.one = 1)
    (h : Eqns e (tplTS ν r.size).gates 0) : (tplTS ν r.size).outs.map (LinT.ev e) = (targetSNode4I ν r).toList
theorem tplEvL_ok (hi : InpIs e (rL.toList ++ r4.toList)) (h1 : e.one = 1) (h : Eqns e (tplEvL ν rL.size r4.size).gates 0) :
    (tplEvL ν rL.size r4.size).outs.map (LinT.ev e) = [(evalL4I ν rL r4).1, (evalL4I ν rL r4).2.1, (evalL4I ν rL r4).2.2]
theorem kTS_ok (ι : Kind) : KOk (implP impl₀ base 0 ι) ι kTS
theorem kEvL_ok (ι : Kind) : KOk (implP impl₀ base 0 ι) ι kEvL
theorem rtC1c_ok (hZ : LinkZero impl₀) (hB : STBase base) (hπ : π ≤ 1) (ι : Kind) :
    RTOkW (implP impl₀ base π ι) (Xof π) (rtC1c π) ι repB
theorem repOkW_rtC1c (hZ : LinkZero impl₀) (hB : STBase base) : RepOkW rtC1c impl₀ base
```

`gap4Imp_of_repW` (C1) then applies with `rt := rtC1c` once the fold supplies `hfold`.

## 2. Design

- **Gate for gate, value for value.** `tplEvL` mirrors `evalL4I`: tables (`rL` lo 9 / hi `logL−9`, `r4`
  lo 14 / hi `m−21`), `E_i = A[i mod 512]·B[⌊i/512⌋]`, `F_i = E_i·tY[299 + i mod nJ]` (`vslots·nJ`
  each), `Q_σ = eq(r4_hi, hb+σ)·Σ_j F`, `O = eq(r4, oneCell)` (one product), one `mulAdd`.
  `tplTS` mirrors `targetSNode4I` piece by piece against the implementation's own values (`eq9`,
  `rangeI9` over prefix forms, `ctrArr` with `ctrK`/`colT`/`sepD`/`cc`, `finG`, `w43I`, `gAt4`), so the
  proof needs no layout bounds; the 1,216 products `H[hi]·G(σ+64hi)` close it.
- **The context (`TSCx`, `EvCx`).** The first version recomputed the tables at every accessor call
  (`tsE ν a j i`, `nlocs (tsT ν a).1`): the KAT did not finish in minutes. Each template now builds
  its context once (`let cx := mkCx ν a`); `mkCx_E`/`mkEvCx_E` tie it to the spec accessors. A
  proof-side trap came with it: unifying `nlocs (tsT ν a).1` with `(mkCx ν a).k0` made tactics
  418 s; `rw [← mkCx_k0] at h` first brings `FRVIRTplRepT` back to 20 s.
- **Locals.** `linkWAll` `[repB, +42,592)`, R3's `rsWeight` `[repB+2^16, +472,310)`, **`targetS`
  from `cbTS = repB + 2^19 + 2^14`** (11,891 locals kind-muxed: the probe's highest local, measured
  under the earlier `cbTS = repB + 2^16`, was `repB + 77,426`), **`evalL` from
  `cbEvL = repB + 2^19 + 2^15`** (319,507 locals; highest `repB + 450,578` under the earlier
  `cbEvL = repB + 2^17`). Last local `repB + 876,562 < repB + 2^20`: **fits slot 0's spare region**
  for N2 and N4 (N8 has no prototype-0 slot). Rows of slot 0 (all five ops): 42,601 + 472,310 +
  11,439 + 319,510 + 1 ≈ 845.9 k `< 2^20`: fits. `cb_ctl` checks the four blocks' disjointness at
  these sizes.

## 3. Controls and KATs

| Definition | (+) | (−) |
|---|---|---|
| `rtC1b`, `rtC1c` | `rtC1b_cov`, `rtC1c_cov`: prototype 0's `shiftTarget`, `linkWAll`, `targetS`, `evalL` (+ `rsWeight` in `rtC1c`); prototype 1's `linkWAll` | not `evalM`, not the segment's `targetS`/`evalL` |
| `tsIn`, `evIn` | `in_ctl` | an `f` operand, a missing operand |
| `kRows kTS`, `kRows kEvL` | KAT below | `kTS_neg`, `kEvL_neg`: an untracked operand, an `f` operand: the rejecting row |
| `tsTpl`, `evTpl` | `tpl_ctl` | other shapes: the empty template (rejected by `tsIn`/`evIn`) |
| `cbTS`, `cbEvL` | `cb_ctl` | — |
| `tplTS`, `tplEvL` | **KAT** (`probe/RepV2.lean`, `logs/C1b/repv2-4.log`): N2/N4/N8, random operands, honest locals: every row holds, outputs = `targetSNode4I` / `evalL4I` (all true) | perturbing `r[0]` or `r[1]` changes `targetSNode4I`; perturbing `r4[20]` or `rL[3]` changes `evalL4I` (all true) |
| rows from the final state | `growsVal3 = rows3` on slot 0's rows (N2: true) | — |

Template sizes (KAT): `tplTS` N2/N4/N8 = 3,538 / 3,808 / 3,837 rows (86 k / 103 k / 122 k terms);
`tplEvL` = 67,369 / 101,403 / 150,726 rows (344 k / 530 k / 801 k terms). Kind-muxed (all three
sub-templates + mux products): `targetS` 11,439 rows, `evalL` 319,510 rows.

## 4. Measurements (`logs/C1b/repv2-4.log`, core 30)

### 4.1 V (B5's `grows` + `growsVal3`, one grouped sparse piece)

Slot 0's replay rows of `rtC1b 0` (shiftTarget + linkWAll + targetS + evalL, without `rsWeight`),
N2: **373,550 rows, 2,187,768 terms, `growsVal3` best 450 ms / median 458 ms** (`evalMT4` in the same
process 147 ms); **N4: the same 373,550 rows, best 464 ms / median 468 ms** (`evalMT4` 155 ms). By terms (≈ 0.206 µs/term here): `evalL` ≈ 1.68 M terms ≈ **345 ms**, `targetS` ≈
311 k ≈ **64 ms**, `linkWAll` ≈ 196 k ≈ 40 ms (C1 measured 52–60 ms under load). Highest cell N2 16,179,218 < 16,777,216, N4 30,859,282 <
31,457,280 (the spare regions' ends).

**Against the corrected budget** (V per check ≲ 1.5 s VM worst kind; HEAD ≈ 0.30–0.34 s, R3's
`rsWeight` +0.72 s, C1's `linkWAll` +0.05 s): the direct `evalL` adds ≈ 0.35 s (total ≈ 1.45 s —
at the cap) and is not "tens of ms". It needs the closed form of §6.1 before the fold.

### 4.2 Plan init (prototype 0's replay rows from the **final** compile state, one pass)

`repRowsFin` (probe): walk `(protoProg 0).ops` with the register count `n` (an op's outputs are
registers `n … n+nOut−1`), apply `rt.rows P csFin op (csFin.slots.extract n (n+nOut))` to covered
ops. Times: prototype 0 compiled as the plan does (`compMSX`) **1.06 s**; then `shiftTarget`
7.7 ms, **`targetS` 0.26 s, `evalL` 3.42 s**, **`linkWAll` 216 s**, grouping 1.8 s. The
`linkWAll` figure is C1's `tplLW` recomputing its tables at every accessor (`lwE ν a b j i`,
`lwK8 = nlocs (lwT ν a b).1` — the trap §2 fixed here): `FRVIRTplRepLW` needs the same context
(`let` the tables' entries as arrays and `lwK8` once). Not this track's module; diff in §5.4.
`targetS` + `evalL` alone: ≈ 3.7 s (with the closed form of §6.1, `evalL` would be ≈ 0.3 s).

The KAT `repRowsP (rtC1b 0) 0 = repRowsFin …` (the trail against the final state, `trail`
argument) was **not run** in this round (the trail compile plus the `tplLW` trap is several
minutes); it is the evidence the fold's lemma §5.2 needs.

### 4.3 Kernel CPU-s (`lean -DElab.async=false --profile`, one core; `logs/C1b/prof-summary*.txt`)

| Module | type checking (kernel) | tactics | wall |
|---|---|---|---|
| `FRVIRTplRepLD` | 0.008 s | 0.01 s | 20 s (load) |
| `FRVIRTplRepL` | 0.14 s | 0.49 s | 8 s |
| `FRVIRTplRepT` | 0.79 s | 2.9 s | 28 s |
| `FRNodeRows4RepLT` | 0.21 s | 14.1 s | 22 s |
| `FRNodeRows4RepLCtrl` | 0.05 s | 0.04 s | 7 s |
| **Δ kernel** | **≈ 1.2 s** | | |

All proofs are symbolic (no `decide` over template rows; the `decide` controls run on toy CSs).

## 5. The fold (for the fold stage and ASK-P; not done here)

### 5.1 Rows, cells, order
- **Where**: for every kind with a previous node (`N2`, `N4`), slot `σ = 0`: `repIRowsW rtC1c κ 0`
  (C1's definition): rows `κ.vslots·2^20 + k`, `k < |repRowsP (rtC1c 0) 0|` (≈ 845.9 k with
  `rsWeight`); cells by `repMapC κ 0`: a frame cell `c < repB` ↦ `mvC (protoOf κ 0) 0 c + oneCell`
  (where `slotAsg` reads it), a local `c ≥ repB` ↦ `κ.vslots·2^20 + (c − repB) + oneCell`. Segment
  slots `σ ≥ 1`: S-E14's 8 rows at `σ·2^20 + repBase`.
- **Order**: the ops of `protoProg 0` in program order (targetS, shiftTarget, linkWAll, evalL,
  rsWeight); per covered op: its kind-muxed template's rows in gate order (sub-template of index
  `L32`=N4, then `P30`=N2, then `N30`=N8, each substituted onto its operand block; then the
  `nout × 3` mux products), then one copy row `one · out_c = T.out_c` per output component
  (`shiftTarget`: the single row `one · out = 0`).
- `nodeIRows4 κ := (List.range κ.vslots).flatMap fun σ => slotRows4 κ σ ++ linkIRows4 κ σ ++
  repIRowsW rtC1c κ σ` (plus ASK-P's arena rows as now); `hfold` is membership;
  `gap4Imp_of_repW … (repOkW_rtC1c hZ hB)` replaces the replay part of `Gap4.imp`.
- `hfit4`: rows `< (κ.vslots+1)·2^20`, cells `< oneCell + (κ.vslots+1)·2^20` for N2/N4.

### 5.2 Plan: rows from the final state, and the missing lemma
`FRNodeRows4Plan` (B5): one more piece of `evalMS4` per kind with a previous node:
`grows 2048 4096 (repIRowsW rtC1c κ 0)` at plan init, `growsVal3` per call (`growsVal3_eq`). Plan
init must build the rows from the final compile state (`repRowsFin`, §4.2), never along the trail,
so the fold needs **`repRowsP rt π = repRowsFin (protoP π) rt (protoCS π) (protoProg π).ops`**,
by induction along `repRowsX` from: (a) `compileFromX_mono` (the final `slots` extend the trail's;
`kslots` keys are fresh register numbers, so `lookup` agrees), (b) an `RT.Local` property of each
template (`rows` read only `slotK` of the op's operands and the `outs` given) — true of `rtK`,
`rtST0`, `rtLinkSegW` and R3's `rtRs` by definition — and (c) operands `< n` (SSA; a decidable
pass over the ops at plan init, falling back to the trail if it fails). `n` advances by
`Op.nOut` (`= (stepOut …).slots.length`, also to be proved or checked).

### 5.3 The definitions-only split (the import cycle)
`nodeIRows4` (in `FRNodeRows4`) needs `repIRowsW rtC1c`, whose definitions now sit in modules
downstream of `FRNodeRows4` (via `FRNodeSound4R`/`implP`). Move **definitions only** into a new
module, e.g. `FRNodeRows4RepD`, importing `FRNodeRows4Proto` (a split of `FRNodeRows4`'s lines
≈ 60–125: `oneR`, `selR`, `baseR`, `protoP`, `protoOf`, `protoProg`, `protoLay`, `protoF`, `protoR`,
`mvC`, `rowMapC`, `slotM4`), `FRVIRCompile`, `FRVIRTplKMux`, `FRVIRTplRepLW`, `FRVIRTplRepLD`,
`FRVIRTplRepT`, R3's `FRVIRTplChain`/template defs: `RT`, `RT.none`, `RT.orElse`, `repRowsX`,
`linLt`, `Xof`, `repRowsP`, `repB`, `repBase`, `repMapC`, `repRow0`, `repIRowsW`; `rejRow`,
`outsOk`, `outF`, `copyRows`, `kOps`, `KOp`, `kIx`, `kBlocks`, `kSig`, `kTpl`, `kIns`, `kRows`, `rtK`;
`zeroLin`, `bndZ`, `isST`, `stOut`, `stRows`, `rtST0`; `zeroRows`, `isLinkW`, `rtLinkSegW`; `isLW`,
`lwArgs`, `lwIn`, `lwT`, `kLW`, `cbLW`, `rtN0`; R3's `kRS`/`rtRs`/`cbRS`/`rtN0R`; `isTS`, `tsArgs`,
`tsIn`, `tsTpl`, `kTS`, `isEvL`, `evArgs`, `evIn`, `evTpl`, `kEvL`, `cbTS`, `cbEvL`, `rtN0c`, `rtC1c`.
The theorem modules keep their statements and import `FRNodeRows4RepD`. `FRNodeRows4` imports
`FRNodeRows4RepD` and defines `nodeIRows4` with it. `FRVIRTplRepT` and `FRVIRTplRepLD` already
import nothing downstream of `FRNodeRows4`.

### 5.4 Requested diff in `FRVIRTplRepLW` (C1's; not edited here)
Build `tplLW`'s pieces over a context: `structure LWCx := (E : ℕ → ℕ → LinT) (k8 : ℕ)`,
`mkLWCx ν a b := let T := lwT ν a b; let A := T.2.toArray.map List.toArray;
⟨fun j i => (A.getD j #[]).getD i [], nlocs T.1⟩`; replace `lwE ν a b` by `cx.E`, `lwK8 ν a b` by
`cx.k8` in `lwK9…13`, `lwEθ…lwEM`, `lwFams`, `tplLW`; `tplLW ν a b := let cx := mkLWCx ν a b; …`;
in `tplLW_ok`: `rw [← mkLWCx_k8] at h` after the `simp only … at h` (else the unifier unfolds the
tables: the 418 s trap), and `mkLWCx_E` to recover `lwE_ev`. Expected init: ≪ 1 s (from 216 s).

### 5.5 Prover cells (E1)
For an N2/N4 node, slot 0's spare region (cells `oneCell + vslots·2^20 + off`): for each covered
op of prototype 0, in program order, evaluate its **kind-muxed** template honestly: inputs = the
operand forms of **all three** indices (per-kind slots `slotK`, read from the witness), then the
three selector cells; locals at `cb + k` in gate order (`mul`: `a·b`; `mulAdd`: `a·b + c`; `pad`:
`0`; no `inv` gates in `tplTS`/`tplEvL`), including the unselected kinds' sub-templates on their
(garbage) operand values — every gate is satisfiable. Offsets `off = cb − repB`: `linkWAll` 0,
R3's `rsWeight` `2^16`, `targetS` `2^19 + 2^14`, `evalL` `2^19 + 2^15`. The copy rows hold because
the import cells already hold the op's value (= the selected sub-template's output). The probe's
`honest` (`logs/fr-build-C1b/probe/RepV2.lean`) is the reference.

## 6. Open items

1. **`evalL`'s V cost (≈ 345 ms) must come down before the fold.** Closed form (carry split): for
   slot `σ`, `Σ_j eq(rL, σ nJ + j)·tY[299+j]` with `tY = Ylo[x mod 512]·Yhi[⌊x/512⌋]` (split `r4`'s
   14 low coordinates at 9). The offset `c_σ = (299 − σ·nJ) mod 512` is independent of the 512-block,
   so per `σ` two shifted inner sums `S⁰_σ = Σ_{l<512−c} A[l+c']·Ylo[l]`, `S¹_σ = Σ_{l≥512−c} …`
   (512 products), then `Σ_h B[h+q]·Yhi[h]·S⁰ + B[h+q+1]·Yhi[h]·S¹` over ≈ 17 blocks, plus the two
   partial end blocks (prefix sums of the same products). ≈ 1.6 k products per slot instead of
   16.4 k: ≈ 30 k rows / ≈ 100 k terms kind-muxed, ≈ 20–25 ms. Proof: `sepD`-style carry lemmas
   (`twoG_eq`, `sepD_eq` are the model). Alternative: R1's route (b) (`evalL` in the reserve).
2. **`targetS` (≈ 64 ms)**: materialize the ten class weights, the 26 counter bits, the 32 final
   bits and the 16 `w43` bits into locals (`mulAdd` rows) so that `G(p)` reads ≤ 14 locals, and the
   prefix arrays `PA`, `PB` (513 locals each, one `mulAdd` row per entry) so the range sums read 2
   locals instead of ≤ 512-term forms. Estimate ≈ 15–20 ms.
3. **`tplLW`'s construction** (§5.4): 216 s of plan init today.
4. **The fold lemma** `repRowsP = repRowsFin` (§5.2) and its KAT (`repv2 trail`).
5. `rtC1b` (without `rsWeight`) is kept for reference; the fold should use `rtC1c`.
