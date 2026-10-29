# S-E14 (track L-circ): RESULT — the replay `R` (S-N2's `Gap4`, item 7)

Base: HEAD `d7bb21e`. Build tree `logs/fr-build-SE14` (a copy of `fr-build-SE13b`, against
`logs/org20`; `MINE.txt` lists the three new modules). Logs: `logs/S-E14/`. Every lake/lean command
ran in the 16G scope under `timeout`. No sub-agents. Nothing committed. **No existing module was
edited.** Journal: `S-E14-JOURNAL.md` (§0 the allocation, §1 the design note, §1.10 V re-priced at
S-E13a's measured costs).

## Status

| Item | State |
|---|---|
| 1. Design note | **Done** (JOURNAL §1). Per op: operands, row form and count, V, `N_M`. **Verdict: `evalM` (`R` proper) does not fit the previous node's slot region** next to the other ops (§2), and none of the previous node's ops has a closed-form template today. |
| 2. Rows + `replay_sound` | **The mechanism is built and proved**: `compileFromX_soundR` (the staged compile soundness every replayed import needs). **One op is replayed**: the segment slots' `linkWAll` (`rtLinkSeg_ok`). The other nine registers are **stopped** under the orchestrator's rule (no closed form available; §2). |
| 3. The discharge | **Done up to the fold**: `gap4Imp_of_rep` takes `Gap4.imp` from `StmtN4`, `hfold` (the replay rows are among `nodeIRows4`) and `SlotImpR` (S-N2's `SlotImp` minus the covered imports). |
| 4. Controls / measurements | Controls built (§4). Row counts: 8 per segment slot (§5). `hfit`, the plan and V are unchanged until the fold (8 rows per segment slot: < 0.05 ms at 0.6 µs a row). |

**Checks.**
- `lake build FR FRNodeRows4Rep FRNodeRows4RepS FRNodeRows4RepCtrl` green: 2,569 jobs
  (`logs/S-E14/build-final.log`).
- **Axioms** (`logs/S-E14/axioms.log`, `logs/fr-build-SE14/ax/AxSE14.lean`): 18 declarations, among
  them `compileFromX_soundR`, `compileX_soundR`, `slotImp_of_rep`, `repHolds_of`, `gap4Imp_of_rep`,
  `rtLinkSeg_ok`, `repOk_rtSeg`: each ⊆ {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 357
  files, 0 findings (`logs/S-E14/source-rule.log`).
- **`FR.lean`** (orchestrator): add `import FRNodeRows4RepCtrl` (it pulls in the other two).

## 1. What was built (`loc.py`, `logs/S-E14/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeRows4Rep` | 394 / 297 / 13 | **`RT`** (covered ops; rows per compile state, op, output slots), **`RTOk`**, `RT.none`; **`repRowsX`**, **`impRX`** (defined along the compile's trail, the same fold as `compileFromX`), `impRX_sub`, `impRX_none`; **`compileFromX_soundR`**, **`compileX_soundR`**. At the node: `Xof`, `protoCS_X`, **`repRowsP`**, `impRP`, **`SlotRunR`**, **`SlotImpR`**, `RepHolds`, **`RepOk`**, **`slotImp_of_rep`**, `slotImpR_of_imp`, `repBase`, **`repIRows4`**, `mem_zipIdx_map`, **`repHolds_of`**, **`gap4Imp_of_rep`** |
| `FRNodeRows4RepS` | 103 / 64 / 5 | `zeroRows`, `isLinkW`, **`rtLinkSeg`**, **`rtSeg`**, **`LinkZero`**, `linkZero_implC`, `rej_not`, **`zeroRows_sound`**, **`rtLinkSeg_ok`**, **`repOk_rtSeg`** |
| `FRNodeRows4RepCtrl` | 67 / 34 / 6 | the controls (§4) |
| **total** | 564 / 395 / 24 | |

### Why a staged soundness (the design's central fact)

`compileTF4_soundAt` assumes every import at the **final** run (`hi`). A replay row says only
`cell(out) = f(cells(args))`; it yields `RepS w (slot out) (f (rd s.regs args))` only if the
operands' cells represent their registers **when the op is compiled**. That fact lives inside the
compile's induction. `compileFromX_soundR` is `compileFromX_soundK`'s induction with one change at
the import step: a covered op's outputs come from its template (`RTOk`, at the aligned state, with
`InvK` there), and the other imports from `hi` restricted to `impRX`.

```lean
def RTOk (impl : OpImpl) (X : Ext) (rt : RT) (κ : Kind) : Prop :=
  ∀ P cs op, rt.cov op = true →
    (∀ inp regs q, evalOp impl κ inp regs op ≠ .ask q) ∧
    ∀ inp w regs vs ok, SelOk w P κ → InvK w cs regs κ →
      (∀ r ∈ rt.rows P cs op (stepOut X P cs op).slots, r.Holds w) →
      evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
      List.Forall₂ (RepS w) (stepOut X P cs op).slots vs

theorem compileX_soundR (hX : ExtOkK impl tc X κ) (hR : RTOk impl X rt κ) (base) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr')) (hr) (ht) (hx)
    (hi : ∀ i ∈ impRX X P rt (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w) (hf) :
    s.ok = true ∧ ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i)

theorem gap4Imp_of_rep (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) (pf)
    (hfold : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, Active4 (rd4 pf) κ w v → SlotImpR rt impl₀ base κ v w (slotIn …) (slotTr …)) :
    ∀ v, Active4 (rd4 pf) κ w v → SlotImp impl₀ base κ v w (slotIn …) (slotTr …)
```

- The rows and the uncovered imports are defined **along the trail** (`repRowsX`, `impRX`), so no
  definition or proof evaluates the 106 k-op programs. The template sees the op's operands through
  `CS.slotK` (per-kind slots), so a kind-muxed template fits the interface.
- `SlotImpR` is the **`hPack`-style interface** the orchestrator's note asks for: every import that
  `R` does not compute (the squeeze answers `R`'s operands derive from, every pack-map class) stays
  a hypothesis on its cells (`impRP`). `slotImpR_of_imp` shows it asks nothing beyond `SlotImp`.
- `RepOk rtSeg impl₀ base` holds under **`LinkZero impl₀`** (the base reads a leaf kind's `linkWAll`
  as `0^8`), which the submission's `Impl.implC` meets by `rfl` (`linkZero_implC`).

## 2. The design note's numbers (JOURNAL §1)

**Free rows per slot region** below the link region: 2^20 − 2^15 − 730,493 = **285,315**
(prototype 0) and 2^20 − 2^15 − 725,885 = **289,923** (prototype 1), measured
(`logs/S-E13a/nodedump4-run.log`).

| Op | Prototype 1 (segment, read at `L32`) | Prototype 0 (previous node, `ν ∈ {N2, N4, N8}`) |
|---|---|---|
| `linkWAll` | `0^8`: **8 rows** (built) | `linkWAll4I ν`: ≈ 35 k (muxed), no template |
| `targetS` | `targetSSegI`: ≈ 500 (eq tree + 64 constant-matrix rows) | `targetSNode4S ν`: ≈ 24 k, no template |
| `shiftTarget` | ≈ 3.1 k (digest bits from the statement) | ≈ 2.2 k (`bnd` constant: no bits) |
| `rsWeight` | ≈ 45.6 k (no kind factor) | ≈ 135 k (with `FRKindWeight4`'s kind factor) |
| `evalL` | **dead** | `evalL4I ν`: 15–25 k by a carry-automaton closed form (not written); ≈ 125 k direct |
| `evalM` | **dead** | **`R` proper: 330–590 k** (240 k with S-E12b's levers + ≈ 90 k for the child's irregular link-region rows, which the 240 k did not count) |
| **total** | **≈ 49 k** (fits 5.9×) | **≈ 221 k without `evalM`** (fits 1.29×); **with `evalM` it does not fit** |

- **`evalM`'s home must be a spare region**: `N2` region 3, `N4` region 5 (`N8` has no previous
  node). Then `N_M`: `N2` ≈ 3.6 M of 3.99 M (`N_M/1.05`, 1.11×), `N4` ≈ 5.6 M of 7.99 M.
- **V**, at S-E13a's 0.6 µs per irregular row: the previous node's ops as plain rows would cost
  ≈ 130 ms, `evalM` 200–350 ms. Only closed-form templates are viable (JOURNAL §1.10). Of the ten
  registers, only the segment `linkWAll` (built), and with new templates the segment
  `targetS`/`shiftTarget`, have one within reach. The segment `rsWeight` can reuse 3.x's
  `tplRsWeight` for its claims (it is dropped by `keys41`). **No template exists for the previous
  node's `targetS`, `linkWAll`, kind factor or `evalL`, and `evalM` needs the levers.** Under the
  orchestrator's rule I stopped there.
- **Dead ops.** In prototype 1, `evalM`'s and `evalL`'s six registers feed only
  `assertEq r58009 r2339 {L:false, P:false, N:false}` (`proto-p1.txt` 66689–66703; checked register by
  register). They cannot be replayed (their value is 3.x's node matrices'). Remedy: the generator
  drops them for the segment group, or a non-interference lemma (JOURNAL §1.8).

## 3. Deviations and decisions

1. **`R` is not a separate list of hand-placed rows but a template over the compile's trail.** Its
   rows are a function of the compile state at each covered op, so the rows name the operands'
   actual cells (per kind) without evaluating the program. The node's indexed rows `repIRows4` sit at
   `v·2^20 + repBase + k` (`repBase = 23·2^15`, JOURNAL §0), clear of the prototypes and of S-E13a's
   link region.
2. **The fold is not applied** (S-E13a owns `FRNodeRows4`): `nodeIRows4` must gain, per slot,
   `repIRows4 rtSeg κ v`, and then `hfold` is a membership fact as S-E13b's. Until then nothing in
   the certificate changes.
3. **`Gap4.imp` is not replaced**, because only one register is discharged. When the fold is in,
   `resid4_of`'s `hG.imp` can come from `gap4Imp_of_rep` with `SlotImpR` as the residual.
4. **The model is stale** (S-E13a's `FRNodeRows4Model`): `protoRowsN = 551,805` is S-E12b's; since
   S-E12f the prototypes occupy 730,493 / 725,885 rows. With the measured figure the previous-node
   slot model is 1,126,870 rows (> 2^20 − 2^15), so `mRows4_le` holds only on the stale constant.

## 4. Controls (`FRNodeRows4RepCtrl`, and the converse in `FRNodeRows4Rep`)

| Definition | (+) | (−) |
|---|---|---|
| `impRX` | `impRX_ctl`: an uncovered `linkWAll`'s registers are assumed | covered by `rtLinkSeg`, none is |
| `repRowsX` | `repRows_ctl`: covered, 8 rows | uncovered, none |
| `zeroRows` | `zeroRows_pos` | `zeroRows_neg`: a nonzero output cell fails |
| `LinkZero` | `linkZero_implC` | `linkZero_neg`: `linkWAll = 1^8` fails |
| `rtSeg` | `rtSeg_ctl`: covers `linkWAll` at prototype 1 | nothing at prototype 0, not `targetS` |
| `SlotImpR` | `slotImp_of_rep` (gives `SlotImp`) | `slotImpR_of_imp`: asks nothing beyond `SlotImp` |
| `RTOk` | `rtLinkSeg_ok`, `RT.none_ok` | `rtSeg` does not cover prototype 0's `linkWAll` (its value is `linkWAll4I ν`, not `0^8`) |

The `decide` controls run on one-op programs only.

## 5. Measurements

- **Row counts.** `rtSeg` adds `zeroRows` for each `linkWAll` of prototype 1: the program has one
  (`proto-p1.txt` line 66617), so **8 rows per segment slot**: `N2` 16, `N4` 32, `N8` 64. This is a
  count off the dump, not a kernel-checked length: a kernel length would evaluate the program
  (S-E13's trap). `repRows_ctl` checks the 8 on a one-op program.
- **`hfit`, the plan, V(N4).** Unchanged until the fold. After the fold: rows at
  `[753,664, 753,672)` of each segment region (below the link region, above the prototype);
  cells unchanged (the rows read only the import's own output cells and `one`). V +8 rows per segment
  slot ≈ 5 µs each. The plan gains one pass over the ops (`repRowsX` reuses the compile's states:
  compute it together with `protoCS`, never as a second compile).
- **Times** (sequential, `taskset`, one core, `-DElab.async=false`, 16G; `logs/S-E14/profile-*.log`,
  load ≈ 30): type checking 0.16 s (`FRNodeRows4Rep`), 0.08–0.17 s (`…RepS`), 0.04 s (`…RepCtrl`);
  tactics 1.2 / 0.65–1.1 / 0.06 s; max RSS 2.95 GB. Walls 12.6 / 22.4–35.8 / 17.5 s are import time
  plus load noise.

## For P2

- **Witness cells: none new.** The 8 rows of a segment slot's `linkWAll` replay are `one · out_j = 0`
  on the import's own cells (prototype 1's `r57924` slot, `af 8`, `mregs-p1.txt`). An honest prover
  already writes `0^8` there (a leaf kind's `linkWAll`).
- **New rows (after the fold):** per segment slot `v`, rows `v·2^20 + 753,664 + j` (`j < 8`):
  `A = one`, `B = cell(out_j)`, `C = 0`.

## 6. Handover: the remaining items, in order

1. **Fold** (S-E13a's `FRNodeRows4`): `nodeIRows4` per slot `… ++ repIRows4 rtSeg κ v`; `hfold` by
   membership; `hfit4`'s row bound (`repBase + |repRowsP| < 2^20 − 2^15`) and the cell bound
   (the rows' cells are prototype cells: `InSlot`'s).
2. **The generator: drop the segment group's `evalM`/`evalL`** (or prove non-interference), so that
   prototype 1's imports lose six dead registers.
3. **Templates with closed-form MLEs** (one `RT` each, kind-muxed through `CS.slotK`, and a key in
   the plan's copy so V evaluates them once per prototype):
   (a) segment `targetS` (eq tree + one constant matrix); (b) `shiftTarget` (both prototypes);
   (c) segment `rsWeight` from 3.x's `tplRsWeight`; (d) node `targetS`, `linkWAll`, `rsWeight`'s kind
   factor (new templates at the 4.1 layout); (e) `evalL`'s carry-automaton closed form.
4. **`evalM`**: needs S-E12b §4's levers and a spare region (`N2` 3, `N4` 5), plus a closed form for
   the child's irregular link-region rows (≈ 90 k products per kind); without them it does not fit
   V. This is a design ruling for the orchestrator (S-E6 §4's options (a)–(c)).
5. **The model** (`FRNodeRows4Model`): `protoRowsN` to 730,493 and the `R` figures of §2.
