# SEG-R2 review (cheap early review, read-only)

Commit `e447823` on `v4/rev44`. Inputs: `git show e447823` and `docs/v4/flock-recursive/stages/SEG-R2-RESULT.md`.
Nothing was built or run. Paths are relative to `submissions/flock-recursive/lean/`. Line numbers are at `e447823`.

**Verdict: sound as committed. No blockers. Two should-fix items, both about acceptance (the 35-row
`arR2N` slack, and the stale prover/E1 dump). The rest are notes.**

## Answers to the four questions

### 1. `repF` totality, `impQX_repF`, `SlotRunF`

- `TG.repF` (`FRNodeRows4AskC.lean:207`) has `cov := A.cov op || (isRep op && !rc op)` and emits
  `[failRT P]` exactly when `!A.cov op && isRep op && !rc op`. Every `isRep` op
  (`FRNodeRows4AskC.lean:97`: `shiftTarget`, `linkWAll`, `rsWeight`, `targetS`, `evalL`, `evalM`) falls
  into one of three cases: the ask template covers it, `rtC1d π` covers it, or it gets the failing row. No
  replay op is silently imported. Non-`isRep` imports are still the closure's (`TG.close`, line 195), which
  sits after `repF` in `askTG` (`FRNodeRows4.lean:238`). The proof side matches: `withRep` (`FRNodeRun4CT.lean:29`)
  is `(withSib …).repF (rtC1d π).cov`, the same `rc` that `askTG` uses.
- `impQX_repF` (`FRNodeRun4CB.lean:200`) is proved by structural recursion on the op list, generalised over
  `cs`. Each step is `if_neg` followed by `cases isRep op <;> cases rt.cov op <;> simp`. The compile is
  never evaluated, so it is not proved by kernel evaluation. `atImp_repF` (line 160) is honest: in the
  `failRT` branch it uses `failRT_not hc.1.1`, and otherwise it recovers `A.cov op = true` from the `cov`
  disjunction.
- `SlotRunF` (`FRNodeRun4CB.lean:299`) is, token for token, the first conjunct of `SlotRunC` (line 291):
  the same binder, the same `isBitsA a = false` guard and the same equation. It has no extra hypothesis.
  `slotRunC_of_F` discharges the second conjunct by `impQP_repF` and `cases hi`.

### 2. Placement

- **Rows: the kernel proves them disjoint, so soundness does not rest on the probe.** `rep_fit`
  (`FRNodeRows4Fit.lean:694`) proves two things:
  - the replay rows are `nodup`; inside one slot this comes from `segRow_inj` (line 539) and the
    `segRN` length bound;
  - no replay row index equals any `slotRows4 ++ arIRows4 ++ linkIRows4` index of any slot.

  That list, plus `repAllRows`, is all of `nodeIRows4`. So skeleton rows, template instances
  (`askPI`, inside `arIRows4`), arena₁, bits and links are all covered.

  The two bands:
  - **Band B** `[repSegB, 2^20 − linkN)` lies above the bits, because `repConsts` (line 514) states
    `arRb + arNb = repSegB` with equality, and below the links.
  - **Band A** `[repA, arR2)` lies above prototype 1's rows, by `RepFit.2` through `slotA_idx1`
    (line 585), and below the arena/ask rows, which start at `arR2`.

  The two bands cannot overlap each other: A ends at 720,896 and B starts at 988,672. The band-A bound is
  part of `RepFit`, a Prop gated classically in `repAllRows` (`FRNodeRows4.lean:307`). The plan's
  `ivBelow keys pc1 (slotM4 + repA)` (`FRNodeRows4Plan.lean:588`) is only the run-time decision, tied to the
  Prop by `hR` / `repFit_iff`. A wrong run-time check can only make the plan fall back. It cannot change the
  circuit.
- **Cells: an overlap can cost completeness only, never soundness.** The replay's assignment is
  `repAsg κ v w = w ∘ repMapC κ v` (`FRNodeRows4RepW.lean:28`), so `RepOk` transfers whether or not
  `repMapC` is injective:
  - frame cells (`c < repB`) still read the slot's own cells (`mvC`);
  - locals take whatever `w` holds.

  If a local shares a cell with another region, the only effect is an extra constraint on the honest
  prover. `segCell` (`FRNodeRows4Defs.lean:345`) is checked against the RESULT:
  - `segCell_lt` keeps every local inside its region;
  - band sizes 4,096 + 35,648 + 12,718 = 52,462 = `segCap`;
  - `segCell_ctl` pins the band starts and the last cell (1,015,727).
- **Constants are consistent**, recomputed by hand:
  - arR1 = 720,896 + 154,368 = 875,264;
  - arena₁ ends at 972,208 ≤ `arRb` 972,288;
  - `arRb` + 16,384 = 988,672 = `repSegB`;
  - `repSegB` + 27,136 = 1,015,808 = 2^20 − 2^15;
  - 688,128 + 32,768 = 720,896 = `arR2`;
  - `segRN` = 27,136 + 32,768 = 59,904;
  - `a1Rows4_ctl`'s row 875,269 = arR1 + 5.

  None of the old literals (180,560 / 998,400 / 1,014,784 / 901,456 / 901,461 / `31·2^15 − 2^10`) remains
  in any `.lean`, `.rs`, `.py` or `.sh` file under `submissions/`. They survive only in historical stage
  documents. The prover does not hard-code these offsets: it reads rows from the embedded dump
  (`prover/nodeblob.b64`), which is stale (should-fix 2).
- **N4/N8 vs N2.** Every M-part cell and row involved is region-relative:
  - `selR σ`, `oneR`, `baseR`, `mvC`, `arA1`/`arBt`, `repRowI`, `repMapC`;
  - the stream, L and WOTS cells (`sCell`, `Lc`, `selCells4`) lie below `oneCell`
    (`FRNodeRows4Fit.lean:53,69,238`).

  A prototype-1 region therefore has the same layout in every kind, so the N2 slot-1 probe stands for
  N4 slots and for N8 slots 0–7. The one structural difference is that N8's region 0 is a segment slot
  (`repRowI .N8 0 0 = repSegB`, `repRow0_ctl`), and that region also holds the node-wide `oneCell` (offset 0),
  which no band touches. I see no reason for N4/N8 to differ. In any case a difference could only affect
  completeness (see the cell point above).

### 3. Statement changes

- `certified`, `Gaps4`, `Open4F`, `hfit4`, `rep_fit`, `slotA_idx`, `evalMT4_eq`, `evalMX4_eq`, `slots_val` and
  `rvOf_get` are unchanged, per the diff.
- The changed definitions (`askTG`, `repAllRows`, `RepFit`, `repCellOk 1`, `repFitB 1`, `repIRowsW`,
  `repMapC`) change the circuit itself. The verifier and its equality to the specification are re-proved
  against the new circuit, and nothing in `certified`'s statement is weakened.
- `RepFit` gains a conjunct. That makes the replay fold rarer, never easier: if it fails, the circuit gets
  a rejecting row.
- `TG.repF` only adds failing rows and coverage.
- `repV4_eq` gained `σ < κ.vslots` (`FRNodeRows4Plan.lean:1504`). Its only caller is `slots_val`
  (line 1682), which discharges it with `List.mem_range.1 hs`. It is needed for `hv : σ < 2^(logM − 20)`.
- `gaps4_of_runF` is a bridge. It is not routed into `certified`. The RESULT's argument for not re-routing
  is correct.

### 4. Kernel hazards and hard-rule words

- None of `sorry`, `native_decide`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`, `export`,
  `csimp`, `#eval`, `run_cmd`, `elab`, `macro`, `initialize` or `Lean` occurs in any of the 21 touched files,
  comments included.
- The new `decide`s are controls on literals ≤ 2^20 (`segCell_ctl`, `repRow0_ctl`), plus
  `cases κ <;> decide` on dimensions. There is no `decide` over a compiled table.
- `rtC1d_zero` is `rfl` through a single `if π = 0`, which is cheap.
- `rv1Of_get` is by `rw` through `repV_eq`. Nothing is evaluated.

## Findings

### Blockers

None.

### Should-fix

1. **SEG-R2-S1 (acceptance): `arR2N` leaves 35 rows of slack at prototype 1** (`FRNodeRows4ArenaPlace.lean:58`,
   RESULT §9.1). Suppose any later ask-template row lands at prototype 1. Then `ArFit` fails at process
   start, and every node gets `[(arRej σ, rejR κ)]`: sound, but every honest proof is rejected, silently
   unless someone looks. Two remedies:
   - add a guard that fails loudly whenever the stage's honest checks run (for example, assert
     `planOf4.inR = true` and `(askRowsT 1).length ≤ arR2N` in the plan probe or `check.sh`); or
   - record in QUEUE.md that any change to the ask template must re-run the fit probe.
2. **SEG-R2-S2 (acceptance): the node circuit changed, and no honest node ACCEPT has been re-measured.**
   Rows moved in every region (arena₁, bits, segment replay), and the segment slots gain 38,805 replay rows
   and 38,486 local cells. The prover's embedded node dump (`prover/nodeblob.b64`, last changed in E1
   `200b531`) and its fill plans predate this. The RESULT §5 says "E1 re-dump pending". Until an honest
   N2/N4/N8 run prints ACCEPT on this commit, acceptance is unmeasured. Make that run the gate for the next
   stage.

### Notes

1. **SEG-R2-n1.** The cell-clash probe ran on N2 only. The region-relative argument (§2 above) makes N4/N8
   the same, and clashes cost only completeness. The honest N4/N8 ACCEPT in S2 closes this.
2. **SEG-R2-n2.** `repRow0`'s docstring (`FRNodeRows4Defs.lean:377–379`) still says "a segment slot at
   `v·2^20 + repSegB`". That is now true only of row 0. Placement is `repRowI`. It is a cosmetic issue,
   because `repRow0` feeds only prototype 0 and the controls.
3. **SEG-R2-n3.** `mRowModel4_eq`'s docstring (`FRNodeRows4Model.lean`) reads "1.029× under `N_M/1.05` …
   and `N8` no longer fits". The phrase carries over from the previous text and now reads as a
   contradiction: N8 fits, with 1.029× headroom. Reword it.
4. **SEG-R2-n4.** Band 2 uses 4,096 of its 13,414 free cells (`segCell`). That leaves about 9.3 k local
   cells of headroom unused if `rsWeight` grows. This is not needed now.
5. **SEG-R2-n5.** `FRNodeRows4RepF` now imports `FRNodeRows4RepSeg`. That module (through `FRSubmission4V`)
   is downstream of the plan. The build is green, so there is no cycle. It does lengthen the dependency
   chain into `FR.lean`. This is informational only.
