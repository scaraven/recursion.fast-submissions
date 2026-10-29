# C1 (track L-circ): RESULT — the previous-node slot's replay `R` (PACK-4.4 §6.2)

Base: worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `7bbbf49`). Build tree
`logs/fr-build-C1` (a copy of `fr-build-RSVS2b`: HEAD snapshot plus RSV-S2b's build-tree-only sorries
for other tracks' red declarations; `mymods.txt` lists this track's modules). Logs: `logs/C1/`. Every
lake/lean command ran in the 16G scope under `timeout`. No sub-agents. Nothing committed. Journal:
`C1-JOURNAL.md`.

## Status

| Item | State |
|---|---|
| `shiftTarget` (prototype 0) | **Discharged.** Its value is `0` (the operand `bnd` is the constant `0⁴ ‖ last`); one row `one · out = 0` behind a compile-time check of `bnd`'s forms. |
| `linkWAll` (`linkWAll4I`, prototype 0) | **Discharged.** A kind-muxed template, gate for gate `linkWAll4I ν` for the three node kinds, plus 8 copy rows. Correctness `tplLW_ok`. |
| The segment's `linkWAll` (prototype 1, S-E14) | Kept, restated for the second assignment (`rtLinkSegW`). |
| `targetS` (`targetSNode4I`), `evalL` (`evalL4I`), `rsWeight` (`rsWeightF4`, with the kind factor) | **Not done: still imports** (`impRP rtC1 0`). Designs and costs in §6. |
| `evalM` | RSV2's reserve (not this track's). |
| The mechanism | **Done and general**: `KOp`/`rtK` (any op as a kind-muxed template over its operands' per-index forms) with `rtK_okW` (`KOk` ⇒ `RTOkW`); the replay rows at a second assignment (the spare region) through the slot's soundness (`compileFromX_soundRW` … `gap4Imp_of_repW`). |
| `SlotImpR = ∅` | **Not reached.** `SlotImpR rtC1` drops `shiftTarget` and `linkWAll` at prototype 0 (and keeps S-E14's segment `linkWAll`); `targetS`, `evalL`, `rsWeight` (prototype 0) and the segment's `targetS`, `shiftTarget`, `rsWeight` and dead `evalM`/`evalL` remain. |
| The fold into `nodeIRows4`, the plan, V(N4)/V(N8), plan init | **Not folded** (other tracks' modules, and an import cycle: §5). V's cost of the rows **measured by a probe** with B5's grouped evaluator (§4): **52–60 ms** under load 14–17, too much (PACK §6.2's budget for all of `R` is 7–14 ms). |
| C2 (drop the segment's dead `evalM`/`evalL`) | Not done (it changes prototype 1, hence the hints, dumps, plan and fit; not cheap). |
| Build | `lake build FRNodeRows4RepNCtrl FRNodeRows4RepCtrl FRNodeRun4S FRVerifierImplNode4F` green, 2,370 jobs (`logs/C1/build-final.log`). |
| Axioms | 29 declarations ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, no `sorryAx` (`logs/C1/axioms.log`, `logs/fr-build-C1/ax/AxC1.lean`). |
| Source rule | `source-rule.py submissions/flock-recursive`: 420 files, **0 findings** (`logs/C1/source-rule.log`). |

## 1. What was built (`loc.py`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeRows4Rep` (S-E14's, extended) | 584 / 461 / 18 (was 394 / 297 / 13) | **`Agree`**, **`linLt`**, `ev_agree`, `map_ev_agree`, **`RTOkW`**, `RT.none_okW`, **`compileFromX_soundRW`**, **`compileX_soundRW`** (S-E14's induction with the replay rows at `w'`). Nothing of S-E14's changed. |
| `FRNodeRows4RepK` (new) | 463 / 343 / 21 | `RT.orElse`, `RT.orElse_ok(W)`, `rejRow`; the output side (`outsOk`, `outF`, `copyRows`, `outsOk_rep`, `copyRows_ev`); the input side (`kOps`, `kOps_rep`); **`KOp`**, `kIx`, `kBlocks`, `kSig`, **`kTpl`** (`kmuxT` over the three indices' operand blocks), `kIns`, **`kRows`**, **`rtK`**, **`KOk`**, `kTpl_ok`, **`rtK_okW`**; prototype 0's `shiftTarget`: `zeroLin`, `bndZ`, `stOut`, `stRows`, **`rtST0`**, `digestMle_zero`, **`shiftTargetI_zero`**, **`STBase`**, **`rtST0_ok`**. |
| `FRVIRTplRepLW` (new) | 381 / 288 / 20 | `pL`, `tabsG`/`tabsG_ev`, `sumG`, **`famG`**/**`famG_ev`** (one family = `linkWOneF`), `lwCs`, `lwT`, `lwE`, `lwK8…13`, `xw`, `ym`, accessors, `lwFams`, **`tplLW ν a b`**; `lwE_ev`, `lwFams_ev`, the named arrays (`lwEθA` …), `linkWOneF_congr`, `linkWAll4I_eq'`, **`tplLW_ok`**. |
| `FRNodeRows4RepN` (new) | 167 / 104 / 8 | **`kLW`** (`linkWAll`'s `KOp`), `implP0_linkWAll`, **`kLW_ok`**; `rep_agree`, `forall2_agree`, **`rtLinkSegW`**, `rtLinkSegW_ok`; **`repB`** (`2^40`), `cbLW`, **`rtN0`**, **`rtC1`**, **`rtC1_ok`**, `stBase_implC`. |
| `FRNodeRows4RepW` (new) | 122 / 71 / 6 | **`repMapC`**, **`repAsg`**, `agree_repAsg`, **`RepHoldsW`**, **`RepOkW`**, `selOk_repAsg`, **`slotImp_of_repW`**, **`repOkW_rtC1`**, `repRow0`, **`repIRowsW`**, **`repHoldsW_of`**, **`gap4Imp_of_repW`**. |
| `FRNodeRows4RepNCtrl` (new) | 101 / 48 / 10 | the controls (§3). |
| **total** | 1,818 / 1,315 / 83 (new code: 1,018 lines; `logs/C1/loc.txt`) | |

`FR.lean` (orchestrator): add `import FRNodeRows4RepNCtrl` (it pulls in the other five).

### 1.1 The theorems

```lean
-- the per-op obligation (pure functions) and the template's soundness at a second assignment
def KOk (impl : OpImpl) (ι : Kind) (K : KOp) : Prop :=
  ∀ op, K.cov op = true → (∀ inp regs q, evalOp impl ι inp regs op ≠ .ask q) ∧
    (∀ ν ts, (K.T op ν ts).outs.length = (K.tys.map Ty.len).sum) ∧
    ∀ inp regs vs ok ts, evalOp impl ι inp regs op = .vals vs ok → K.inOk ts = true →
      (K.args op ι).map (fun a => tyOf (rd regs a)) = ts.map some →
      vs.map tyOf = K.tys.map some ∧
      ∀ e : Env, e.one = 1 → InpIs e ((K.args op ι).flatMap fun a => encV (rd regs a)) →
        Eqns e (K.T op (nodeAt ι) ts).gates 0 → (K.T op (nodeAt ι) ts).outs.map (LinT.ev e) = vs.flatMap encV
theorem rtK_okW (B cb : ℕ) (hK : KOk impl ι K) : RTOkW impl X (rtK K B cb) ι B

-- linkWAll, one node kind, gate for gate
theorem tplLW_ok (hi : InpIs e (tt.toList ++ rr.toList)) (h1 : e.one = 1)
    (h : Eqns e (tplLW ν tt.size rr.size).gates 0) :
    (tplLW ν tt.size rr.size).outs.map (LinT.ev e) = encV (.af (linkWAll4I ν tt rr))
theorem kLW_ok (ι : Kind) : KOk (implP impl₀ base 0 ι) ι kLW
theorem rtST0_ok (hB : STBase base) (B : ℕ) (ι : Kind) : RTOkW (implP impl₀ base 0 ι) (Xof 0) (rtST0 B) ι B
theorem rtC1_ok (hZ : LinkZero impl₀) (hB : STBase base) (hπ : π ≤ 1) (ι : Kind) :
    RTOkW (implP impl₀ base π ι) (Xof π) (rtC1 π) ι repB

-- the slot (replay rows at `repAsg`: the slot's assignment below `repB`, the spare region above)
theorem slotImp_of_repW (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOkW rt impl₀ base)
    (hrows : SlotRows κ v w) (hrep : RepHoldsW rt κ v w) (h : SlotImpR rt impl₀ base κ v w inp tr) :
    SlotImp impl₀ base κ v w inp tr
theorem gap4Imp_of_repW (hT₀) (hT) (hok : RepOkW rt impl₀ base) (pf)
    (hfold : ∀ v < κ.vslots, ∀ p ∈ repIRowsW rt κ v, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v → SlotImpR rt impl₀ base κ v w (slotIn …) (slotTr …)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v → SlotImp impl₀ base κ v w (slotIn …) (slotTr …)
theorem repOkW_rtC1 (hZ : LinkZero impl₀) (hB : STBase base) : RepOkW rtC1 impl₀ base
```

`LinkZero impl₀` (S-E14) and `STBase base` (`∀ ν, (base ν).shiftTarget = Impl.shiftTargetI`) hold by
`rfl` at the certificate's `implC` (`linkZero_implC`, `stBase_implC`).

## 2. Design, deviations, and why

1. **One kind-muxed template per op** (`KOp`, `rtK`). Prototype 0 runs at index `ι` the ops of
   `nodeAt ι` (`implP … 0 ι = (implN4F base (nodeAt ι)).fixK .N30`), and `linkWAll`'s operands are
   per-index slots of different lengths (`AF28`/`AF27`/`AF28`, `mkslots-p0.txt`). `kTpl` instantiates
   S-E12f's `kmuxT` over the three indices' operand blocks (`CS.slotK`), and `kRows` adds one copy row
   `one · out_c = T.out_c` per output component on the import's own cells. Any operand without forms,
   any output slot of another type, any operand type the template does not serve (`inOk`), any form
   with a cell at or above the frame bound gets the rejecting row `one · one = 0`. The obligation
   `KOk` is a statement about pure functions; `rtK_okW` is proved once.
2. **`shiftTarget` at prototype 0 is `0`, not ≈ 2.2 k rows** (S-E14's estimate). The `bnd` operand
   `r57056` is the constant `packFK [0,0,0,0,1,…]` at every index (forms `1:0 2:0 3:0`), so both
   `digestMle` terms of `shiftTargetI` vanish (`shiftTargetI_zero`). The value comes from the bases'
   `shiftTarget` (abstract in `SlotImpR`): hence the hypothesis `STBase base`.
3. **The replay rows at a second assignment (a deviation from S-E14's framework).** Prototype 0's
   region is full (PACK §6.1: 927.5 k of 1,048 k rows with the pack map and cap templates), so the
   templates' 42.6 k locals must be cells of slot 0's spare region (region `κ.vslots`). S-E14's
   `compileFromX_soundR` evaluates the replay rows at the slot's own assignment `slotAsg κ v w`, whose
   cells beyond the frame are slot 1's: the honest witness could not satisfy both. `RTOkW` evaluates
   the replay rows at `w'` with `Agree B w w'` (equal below `B`) and `SelOk w' P`;
   `compileFromX_soundRW` is S-E14's induction with that one change. At the node, `repAsg κ v w =
   w ∘ repMapC κ v` reads frame cells (`< repB = 2^40`) where `slotAsg` does and locals from cell
   `κ.vslots·2^20` (`N2` region 3, `N4` region 5; `N8` has no prototype-0 slot). Each template checks
   at compile time that the forms it reads are below `repB` (`linLt`). **S-E14's `RTOk` and
   `compileFromX_soundR` are unchanged** (B3's `compileFromX_run` uses them; §5 item 1).
4. **The kernel trap fixed on the way**: `ev_agree` proved by induction with `rw [Lin.ev_cons, …]`
   took **28 s of kernel type checking**; `List.map_congr_left` under `Lin.ev` takes milliseconds
   (`logs/C1/prof-rep-decl.log` before, `prof-summary2.txt` after).

## 3. Controls and KATs

| Definition | (+) | (−) |
|---|---|---|
| `linLt` | `linLt_ctl` | a cell at the bound |
| `bndZ`, `stOut` | `stOut_pos`: zero digest forms, an output below `B`: the row `one · out = 0` | `stOut_neg`: a nonzero coefficient, or an output cell at `B`: the rejecting row |
| `kRows` (a toy `KOp`) | `kRows_pos`: the template's rows plus one copy row | `kRows_neg`: an untracked operand, or a form at `B`: the rejecting row |
| `rtC1` | `rtC1_cov`: `shiftTarget`, `linkWAll` at prototype 0, `linkWAll` at prototype 1 | not `targetS`, `evalL`, `evalM`, `rsWeight` |
| `rtLinkSegW` | `rtLinkSegW_pos`: S-E14's 8 rows | `rtLinkSegW_neg`: an output at `B`: the rejecting row |
| `repMapC` | `repMapC_ctl`: a frame cell as `slotAsg`; a local at `N4`'s cell `5·2^20` | the local is not slot 1's cell |
| `STBase` | `stBase_implC` | `stBase_neg`: a base with `shiftTarget = 1` |
| `tplLW` | **KAT** (`probe/RepV.lean`, `logs/C1/repv-1.log`): for `N2`, `N4`, `N8` and random `tt`, `rr`, the **honest locals** (each gate evaluated in order) satisfy all **13,848 / 14,360 / 14,360** rows, and the outputs equal `linkWAll4I ν tt rr` | the same `linkWAll4I` at a perturbed `τ` differs (so equality is not trivial) |
| the rows' MLE | KAT: `growsVal3` of the grouped rows equals the plain sparse sum `rows3` at a random point (`N2`, `N4`: true) | — |

The `decide` controls run on one-op or toy programs only.

## 4. Measurements

**Rows** (`probe/RepV.lean`, `logs/C1/repv-1.log`):

| | rows | terms |
|---|---|---|
| prototype 0 (slot 0 of `N2`/`N4`): `kmuxT` of `tplLW` (13,848 + 14,360 + 14,360) + 24 mux products + 8 copy rows + 1 (`shiftTarget`) | **42,601** | **196,410** |
| prototype 1 (each segment slot): S-E14's 8 rows | 8 | 8 |

Per kind `tplLW` = 8 tables (≈ 2.1 k), `Eθ` 256, `Eτ`/`Tr.eq`/`EP` 3 × 996, `EM` 292, the families
3·1,344 + 8·6 + 4·1,046. Slot 0's replay rows sit at rows `κ.vslots·2^20 + k` (`k < 42,601`),
their locals at cells `κ.vslots·2^20 + j` (`j < 42,592`) of the spare region: inside `2^20`, so
`N_M` and the region count are unchanged (PACK §6.1 reserved the spare region for `R`; 4 % of it is
used). **N8 is untouched** (no prototype-0 slot): its `N_M/1.05` fit is unchanged.

**V's cost** (the same probe, core 30, load 14–17; the rows as one grouped sparse piece, B5's
`grows 2048 4096` + `growsVal3`, tables included):

| | `growsVal3` (R's rows) best / median | `evalMT4` same process best / median |
|---|---|---|
| `N2` | **52.4 / 54.2 ms** | 147.8 / 155.5 ms |
| `N4` | **60.2 / 62.6 ms** | 173.3 / 196.6 ms |

That is ≈ 1.2–1.4 µs per row (≈ 0.3 µs per term) under load — **4–8× PACK §6.2's budget for the whole
of `R`** (7–14 ms VM). The rows are kind-dependent only through their region (row block `κ.vslots`)
and the spare cells, so in RSV2's stacked `evalMX4` they cost once per call, not once per kind.

**Plan init.** `repRowsP rtC1 0` along prototype 0's trail took **131–135 s** in the probe (a second
compile of the 106 k-op program with `kRows` at every covered op). It must not run at process start:
the rows only read operand forms, which the final `protoCS 0` holds unchanged (`compileFromX_mono`:
slots are a prefix), so the plan should instantiate `kRows` once per covered op from the final state
(a `repRowsP = repRowsFin` lemma along the trail is the missing piece) — or, better, from the hint's
recorded op positions.

**CPU-s** (one core, `-DElab.async=false --profile`, ≈ 4 s of import each; `logs/C1/prof-summary2.txt`):
see the table appended at the end (§7).

## 5. Exact edits and requests for other tracks' files (not made here)

1. **`FRNodeRun4` / `FRNodeRun4S` (PORT; B3's `compileFromX_run`)**, so that the run route takes the
   replay rows at the spare region's assignment:
   - `compileFromX_run`, `compileX_run`: `(hR : RTOk impl X rt κ)` →
     `{w' : Asg} {B : ℕ} (hP' : SelOk w' P κ) (hAg : Agree B w w') (hR : RTOkW impl X rt κ B)`;
     `hrr`/`hrr'` and the local `hrows` (line ≈ 477) `r.Holds w` → `r.Holds w'`; the call
     `(hR P cs op hc).2 inp w s.regs vs ok hP hI hrows hev hio` →
     `(hR P cs op hc).2 inp w w' s.regs vs ok hP hP' hI hAg hrows hev hio`; the recursive calls pass
     `hP' hAg`. (`Agree`, `RTOkW` are in `FRNodeRows4Rep`, already imported.)
   - `FRNodeRun4S`: `RepOk` → `RepOkW`, `RepHolds` → `RepHoldsW`, `repIRows4` → `repIRowsW`
     (`import FRNodeRows4RepW`), and `slotImp_of_runA`'s call passes
     `(selOk_repAsg hS) (agree_repAsg κ v w)` after `hS` (as `slotImp_of_repW` does).
2. **`FRNodeRows4` (S-E13a/B4; the fold)**: `nodeIRows4 κ` must gain, per slot, `repIRowsW rtC1 κ σ`:
   `(List.range κ.vslots).flatMap (fun σ => slotRows4 κ σ ++ linkIRows4 κ σ ++ repIRowsW rtC1 κ σ)`.
   **This is an import cycle today**: `repIRowsW` needs `rtC1`/`repRowsP` (this track's modules,
   downstream of `FRNodeRows4`, since `Xof`, `protoP`, `protoProg` live there). The row definitions
   (`RT`, `repRowsX`, `KOp`, `kRows`, `rtK`, `rtST0`, `tplLW`, `rtLinkSegW`, `rtC1`, `repMapC`,
   `repIRowsW`) need only `FRVIRCompile`, `FRVIRTplKMux`, the node-kind constants and `Xof`/`protoP`/
   `protoProg`; the integrator either moves `nodeIRows4` (and `ProtoFit`'s users) after a defs-only
   module `FRNodeRows4RepD`, or moves `protoP`/`protoProg`/`protoLay`/`Xof` to a base module. Then
   `hfold` is membership (as S-E13b's), and `gap4Imp_of_repW` replaces `Gap4.imp`'s replay part.
3. **`FRNodeRows4Fit`**: `hfit4`'s bounds learn region `κ.vslots` (rows `< (κ.vslots+1)·2^20`,
   cells `< oneCell + (κ.vslots+1)·2^20` for `N2`/`N4`), and the replay rows' cells: frame cells
   (`InSlot`'s) or spare cells (`repMapC`).
4. **`FRNodeRows4Plan` (B5's)**: per kind with a previous node, the replay rows as one more piece of
   `evalMS4`'s sum (`grows 2048 4096 (repIRowsW rtC1 κ 0)` at plan init, `growsVal3` per call;
   `growsVal3_eq` gives `rows3`), so `evalMT4_eq`/`evalMX4_eq` keep their statements. Measured cost
   §4; not acceptable without the levers of §6.
5. **E1 (prover)**: the replay template's witness is the honest gate evaluation (`probe/RepV.lean`'s
   `honest`): locals in order, from the operand cells and the selectors; the copy rows are the
   import cells (already written by the prover with the op's value).

## 6. Open items (for the orchestrator)

1. **V.** 196 k terms cost 52–60 ms. Levers, in order of yield: (a) share the kind-independent part
   (the `θ`/`r_pos` tables, `Eθ`, each family's `SW`/`MI`/`MS`: ≈ 5.3 k rows per kind, −10.6 k of
   42.6 k) by checking at compile time that the three indices' position forms are equal (they are:
   `r819…`, `r843…`); (b) evaluate `tplLW` as a **keyed instance** (contiguous locals, ≈ 60 input
   forms: the plan's `Piece.ins` with a `Key` of `tplLW`'s rows, the runs evaluator for the table
   stages); (c) closed forms for the `eqTblG` stages and the per-family source sums (PACK §6.2's
   ≈ 10 k products for `linkWAll`). (b) and (c) are the plan's work (B2′/B5's evaluator).
2. **`targetS` (`targetSNode4I`)**: the same mechanism (`KOp`, operand `AF20` plain). Its circuit is
   ≈ 4–5 k products per kind (`bt`'s tables, the 798 `eq9` values, `rangeI9`/`sepD`'s products, the
   1,216 output products `H[hi]·G[σ+64hi]`; `H` is affine in `r₀` since `zLo`'s other 7 coordinates
   are pinned), but the template must mirror `clsW`, `ctrArr`/`ctrK`/`colT`/`sepD`, `finG`, `w43I`
   gate for gate (S-CN4b's ≈ 450 lines of implementation).
3. **`evalL` (`evalL4I`)**: direct, `κ.vslots·8,220` products of `eq(rL, σ·nJ + j)·tY[299+j]` (≈ 82 k for
   `N4`): too many rows and too slow. It needs the carry-automaton closed form of
   `Σ_j eq(rL, σ·nJ + j)·eq(r4_lo, 299 + j)` (S-E14 §2) — or D1p's open question 2 (defer `evalL` to
   the parent's E-phase like `evalM`).
4. **`rsWeight` (`rsWeightF4`)**: `phiTable`, the K-arithmetic of `wEvalKF4`/`wEvalKC4` (claim 2's kind
   factor) and a data-dependent branch (`p.all (·.f₁ == 0)`): the template must compute the general
   (K) form and prove it equals the F form where it applies (`wEvalKF4_eq`, `kwSL4I_eq`).
5. **The segment slot's ops** (prototype 1): `targetS` (≈ 500 rows), `shiftTarget` (≈ 3.1 k: the
   digest bits of the statement), `rsWeight` (3.x's `tplRsWeight` claims), the dead `evalM`/`evalL`
   (C2).
6. **Plan init** (§4): the trail recomputation must be replaced before the fold reaches the plan.

## 7. CPU-s per touched module

One core, `lean -DElab.async=false --profile`, user + system (≈ 4 s of each is import), load 14–17
(`logs/C1/prof-summary3.txt`, `profile-*.log`; `FRNodeRows4RepK`/`N` re-measured after the golf):

| Module | user + sys (s) | kernel (type checking) | tactics |
|---|---|---|---|
| `FRNodeRows4Rep` | 10.3 + 2.9 | 0.21 s (S-E14: 0.16 s) | 1.6 s |
| `FRNodeRows4RepK` | 7.4 + 2.7 | 0.22 s | 1.0 s |
| `FRVIRTplRepLW` | 8.9 + 2.9 | 0.22 s | 1.1 s |
| `FRNodeRows4RepN` | 12.0 + 2.8 | 0.17 s | 7.1 s (one `refine` in `kLW_ok`/`rtLinkSegW_ok`, ≈ 6 s: not located further) |
| `FRNodeRows4RepW` | 4.8 + 2.9 | 0.03 s | 0.14 s |
| `FRNodeRows4RepNCtrl` | 5.4 + 3.0 | 0.10 s | 0.19 s |
| **Δ** | ≈ 49 + 17 (import) | **≈ 0.8 s of kernel in all** | |

The kernel cost is small: the proofs are structural (no `decide` over row lists; the `decide`
controls run on toy programs). Before the fix of §2 item 4, `ev_agree` alone cost 28 s of kernel.
