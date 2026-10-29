# RSV2 friction review

Reviewer: quick friction pass, 2026-10-29. Subject: `design/RSV2.md` (main `2df6154`), checked against
rev44's Lean at HEAD `213c407`, read-only (`submissions/flock-recursive/lean/` in
`../recursion.fast-submissions-rev44`). No builds were run. Every citation is `file:line` at `213c407`
unless it says otherwise.

**Verdict: adopt RSV2. Three things must be fixed first. Finding 1 is a design gap in the cell
binding. Findings 2 and 3 are worktree and sequencing hazards with B2″. The rest are corrections to
the memo's numbers and notes for RSV-S.** The two premises under F2 hold: `protoV4` reads only
coordinates below 20, and one call can stack the three kinds.

## Findings, most important first

### 1. (major) Eleven of the 60 "cells" are not cells: the nine `s` values and mixed-point entries 22 and 24

- **Evidence.** In the compiler, `addF` creates no cell. Its slot is the linear form
  `asF a ++ asF b` (`FRVIRCompile.lean:349–351`). RSV2 builds each `s^C_{κ,m}` with a final `addF`
  (§4.2: "`mulF` ×22, `addF` ×9"), so every `s` register is a sum of two cells. A kind-muxed
  `packFK` element is `muxEl`'s `cell(3i) + cell(3i+1) + cell(3i+2)`, three cells and not one
  (`FRVIRCompile.lean:303–311, 383–394`). Entries 22 and 24 of the mixed point are muxed: for `N2`,
  `rx[22]`/`ry[24]`; for `N4`/`N8`, the E2/E4 challenge.
- RSV-V had no such case. Each of its 52 registers was a single import cell (RSV-V-RESULT §2:
  "Each register is a single import cell"). `PubCellsR4` is `(rsvCells κ).map w = ch`, a point value
  per cell (`FRNodeCircuit4.lean:123`). B′ and finPf weight one `eq(c_i, ρ)` per value
  (`gCellsOpsK`). So §2.2 ("for entries 22 and 24 the compiler's per-element mux cell"), §4.3 ("the
  nine `s` registers' cells") and step 3 of §2.4 ("the registers whose cells are `rsvRel[0..57)`")
  cannot be implemented as written.
- **Suggested action.** Materialize each of the 11 values as one product cell, and keep the
  60-cell form:
  - for each `s` value: `mulF s_i one`, with `one` a `.const (fun _ => .f 1)`;
  - for each muxed entry: `getF` on the packed point, then `mulF _ one`.

  `SlotImp`'s argument then needs one more step: each product row's `Holds` says the cell equals the
  linear form that `evalM` consumed. The cost is about 11 rows in prototype 0.

  The alternative is to generalize `PubCellsR4`, `rsvCells`, `gCellsOpsK` and `relPf4` from one cell
  to a linear form per value. That is a larger restatement and is not recommended.

  Either way, extend `rsvCells_ctl` to assert, from the dump, that each `rsvRel` register's slot is
  exactly one cell.

### 2. (major, process) The rev44 worktree already holds an uncommitted, partial RSV2 edit, mixed in with B2″'s work

- **Evidence.** `git status` in `../recursion.fast-submissions-rev44` shows `FRShape4.lean` modified
  at 13:36:53. RSV2.md is dated 13:29:38. The edit applies RSV2's format: `lrEnd := 1008`,
  `piSizeOf_seq4 876304`, `streamBytesOf_seq4 1551104`, `chainLenOf_seq4 24236`, and docstrings
  that say "RSV2".
- Its dependents are not updated: `FRNodeKinds4.lean:45,47` (`segB 1550976`, `cLen 24234`),
  `hEnd_eq`, `hUsed_eq`, `aggChainLen_eq`, `FRX4Prog.lean:65`, `FRX4Ext.lean`,
  `FRVIRTpl4Bridge.protoR_ctl`, and the hint's mask literal (`FRNodeRows4Hint.lean:37`). So
  `segB_eq`, `cLen_eq` and the `decide` facts are now red.
- The same tree holds B2″'s uncommitted edits: `FRNodeRows4Hint`, `FRNodeRows4ArenaRows`,
  `FRNodeRows4Model`, `FRVIRTpl*`, the new `FRNodeRows4ArenaPlace`, and `B2pp-JOURNAL.md`. B2″'s
  probes build from this tree, and its journal does not mention the change.
- **Suggested action.**
  - The orchestrator finds out who made the `FRShape4` edit.
  - Restore `FRShape4.lean` to HEAD so that B2″'s probes and hint come from one consistent format.
  - Apply RSV2's format as one change across all the modules in §4.1, in RSV-V2's own pass, after
    B2″ lands (finding 3).
  - Do not run two tracks in one worktree.

### 3. (major, sequencing) B2″ and RSV-V2 both rewrite prototype 0's cell layout and the hint

- **Evidence.** B2″'s change is instance packing plus arena placement, and it regenerates
  `FRNodeRows4Hint` (B2pp-JOURNAL item 3: `cellfit-3` reports "free below the lowest instance
  136,914 (p0)"). RSV-V2 adds to slot 0's prototype:
  - about 31 `s^P` product rows, plus the 11 cells from finding 1;
  - finPf's chain grows by 8 cells × 53 ops;
  - one `evalM` import is removed.

  Both re-read `rsvRel` from `nodedump4`. RSV2 also adds 8 F elements (128 B) to the stream.
  Arena₁ holds one cell per stream element (PACK-4.4 §5), so arena₁'s size and placement must come
  from `streamBytesOf seq4`, not from a literal.
- **Suggested action.** Land B2″ first. RSV-V2 then rebases on it and regenerates the hint last
  (`laydump4`, `mkhint.py`, `inR = true`). It then re-runs `CellFit` (0 overlaps, new cells below
  the lowest instance) and re-reads `rsvRel`. B2″ checks that its arena sizes are derived from
  `streamBytesOf seq4`/`chainLenOf seq4`.

  Measure δ (finding 6) on top of B2″'s packed plan. Packing already moved `evalMT4` N4 from 146.0
  to 155.2 ms min (`ab-1.summary`), so the figures from B2′ are stale.

### 4. (minor, numbers) `hEnd` for `N2` and `N4` is wrong in §3.2 and §4.1

- **Evidence.** `hEnd κ = hUsedN κ + nAgg κ · maxK κ` (`FRNodeKinds4.lean:78–82`). The added term is
  `1·2 = 2` for `N2`, `1·4 = 4` for `N4` and `2·4 = 8` for `N8`, which matches today's
  `74,009 − 74,007`, `122,485 − 122,481` and `195,200 − 195,192` (`:421`, `FRNodeLayout4.lean:92`).
  With RSV2's `hUsed` (74,013 / 122,491 / 195,208, which are correct), `hEnd` is
  **74,015 / 122,495 / 195,216**, not 74,021 / 122,499 / 195,216.
- **Suggested action.** Correct the memo. `hEnd_eq` is closed by `decide`, so the build would catch
  the error, but the brief should not send RSV-V2 the wrong literal.

**The other numbers check out** (recomputed from `FRShape4`, `FRNodeLayout4` and `FRNodeKinds4`):

| Quantity | RSV2's value | Check |
|---|---|---|
| `fLrEnd` | 1,008 B | `48 + 368 + 400 + 144 + 48 = 1,008` |
| Offsets | 48 / 416 / 816 / 960 | as derived from the field sizes |
| `|π|` | 876,304 | `876,176 + 128` |
| Stream | `1,551,104 = 64·24,236` | `1,551,104 mod 64 = 0` |
| `aggChainLen` | 48,472 / 72,708 / 96,944 | `= k·cLen`, because `1 − k + 63 < 64` |
| `hUsed` | 74,013 / 122,491 / 195,208 | correct |
| `lBase` | 74,240 / 122,624 / 195,328 | none moves |
| `N8` limit | `lBase + 1,024 ≤ mBase = 196,608` | so `lBase ≤ 195,584`, with 256 blocks to spare |
| `x`'s size term | 0.41785 | correct |
| F2's price | +0.589 s | `1.555 − 0.967`, and `V̄_i = 3.319` at 467 ms |

- **Nit.** "`1,008 = 48 + 15·64`: block-aligned" is misleading, because 1,008 is not a multiple of
  64. What keeps the stream in whole blocks is the +128 B delta.
- **Nit.** `regions_need_levers`' negative control uses the literal 1,556,928 (the no-L2 stream
  "with the reserve"). It still proves, but its prose is now off by 128.
- **Nit.** The spacer budget for A1′ is unaffected. R-A′ keeps whole blocks for any `segB ≡ 0 mod
  64`, and `N8` has 112 blocks below `lBase` plus 256 above.

### 5. (minor, RSV-S) E1's escape: for `N2`, `η` is not coordinate `e2R`

- **Evidence.** `η = (coordsR fi "E1").getD 23 0` for every kind (`FRVIRFinals4.lean:261`).
  `mlDoom n t l` reads `l.take n` (`FRSoundnessCoreSteps.lean:810–811`), and `zcG_count` likewise
  uses the first `a` coordinates (`FRSoundness4P4bRows.lean:155–177`).
- For `N4`/`N8`, `e2R = 23`, so the table `(τ ‖ η)` has `n = 24 = e2R + 1`. For `N2`, `e2R = 22`,
  and the polynomial lives on coordinates 0–21 and 23. "`n = e2R + 1`" (§2.6, §5 item 5) is
  therefore literally wrong for `N2`.
- **Suggested action.** For `N2`, use `n = 24`, with the table constant in coordinate 22 (the lower
  and upper halves `R` and `R + D`, duplicated along coordinate 22). The alternative is to read `η`
  at coordinate `e2R κ`, which changes V. The bound is unchanged at `24/2^128`, and `hn : n ≤ r·2
  = 24` holds.

  In both cases RSV-S needs a new variant of `zcG_count`/`ZCwG` with the `η·D` half. The current
  ones bound the residual table alone at `a` variables, which is new work, not "unchanged lemma".
  Mathlib-style helpers exist for the partial evaluation in §2.5 (`mle_fixLow`, `mle_fix0`,
  `FRMLE.lean:159, 281`). A constant-extension lemma (the MLE of a table constant in its top
  variable) does not appear to exist yet.

### 6. (minor) δ's ceiling is 16.5 ms, not 11 ms, by the memo's own per-slot figure

- **Evidence.** §3.2 counts 16 slot sums instead of 5, so 11 more, at "0–1.5 ms per slot" plus two
  more `ltbOf`. That gives up to 16.5 ms, plus the `ltbOf` cost.
- At δ = 16.5 ms VM: `x = 1.6035`, `V̄_i = 1.100 s`, which is **+0.13 s**, not +0.087 s.
- The per-slot figure itself comes from B2′. B2″'s packing moves it (finding 3).
- **Suggested action.** Quote the ceiling as ≤ 0.13 s, and measure δ on the post-B2″ binary as §7
  item 1 already says. The conclusion does not change: RSV2 is far cheaper than RSV-V's +0.59 s.

### 7. (minor) Op and row deltas are under-counted

- **Evidence.** finPf alone grows by 8 cells × 53 ops = 424 ops (RSV-V-RESULT §2: 52 × 53 = 2,757).
  §3.2's "+≈ 0.35 k ops" and §4.2's "≈ 154,433 + ≈ 350" are therefore low. Add about 31 `s^P` ops,
  about 11 materializations (finding 1) and B′'s +16. The net is about +480.
- **Suggested action.** Correct the figures. This does not affect feasibility.

### 8. (check, item 3) The ε rows are consistent with the Lean

- **The threshold is `deltaR`.** `deltaR = 15/2^124 − 2/2^142 − 1/2^238`, about `2^-120.09`
  (`FRSoundnessCoreSteps.lean:86, 110`). `coord_le_deltaR` accepts `c/2^128` for any `c ≤ 239`
  (`:884`). The memo's "`2^-120.36` (P2's)" is a different (tighter) reference. The Lean test is
  `c ≤ 239`.
- **E1.** `n ≤ 24` is within `hfin_ml`'s `hn : n ≤ r·2` (r = 12) and `hn' : n ≤ 239`
  (`FRSoundness4TailStep.lean:718–720`).
- **E3.** Today's lemma bounds degree 3 by `3·2^128` (`e4_single_batchE`,
  `FRSoundness4P4bE.lean:347–349`). With `κ_E⁴·m̂*` the degree is 4, so the bound becomes
  `4·2^128`. RSV2's `8/2^128` is a safe upper bound.
- **B′.** `single_B4` is stated today for `(cells ν).length = 9` with `bTerms4 : Fin 11`, giving
  `10·2^128` (`FRSoundness4P4bB.lean:293–318`). With 69 values at powers up to `κ′^70` it becomes
  `Fin 71` and `70·2^128`, still ≤ 239. This is a restatement of `single_B4`, `bTerms4`,
  `bTerms4_sum` and `hcells` (length 69, plus the second family), and §5 item 5 should name them
  explicitly. The `hcells` bound `c < 2^ncR ν` holds for `3·2^logM + rsvRel` if the new cells stay
  below 2^20.
- `εR = 15/2^124` is unaffected.

### 9. (check, item 1) "`protoV4` reads only coordinates < 20" is true

- `protoV4` reads `t` and `u` only through `starPt t π` and `starPt u π` with `π ∈ {0, 1}`
  (`FRNodeRows4Plan.lean:391–397`). `starPt` keeps `l < 20`, sets coordinate 20 to `π`, and zeroes
  the rest (`:287`). The key preparations already rely on this (`kprep_star`, `kp_shared`,
  `:375–389`).
- The kinds differ only in the slot sums: `slotV4` reads `hiF lm` (`t[20, lm)`), `u lm` and
  `u (lm+1)`, and `ltbOf lm`/`linkV4 L κ σ` per kind (`:532–533, 566, 633–637`).
- So F2's removal rests on a fact the code already uses.

### 10. (check, item 2) The existing machinery supports one stacked call

- `evalMPair` already evaluates two kinds' slot sums from one `protoV4 pl t u true`
  (`FRVerifierImplNode4F.lean:259–265`). `slots_true` proves `node = true` harmless for `N8`
  (`:272–284`). `evalMX4` is the same pattern over three kinds, and `evalMX4_eq` follows from
  `evalMT4_eq` (`FRNodeRows4Plan.lean:671–680, 699`) three times.
- The only single-kind assumptions are:
  - `evalMN4`/`evalMNS4`'s `ν` and the size test, which moves from `24` to `32`
    (`FRVerifierImplNode4F.lean:316–321`);
  - `implN4F_hM`, whose `h24` becomes `≠ 32` (`:358–368`);
  - P4b's per-kind `wEb4 κ`/`ZCwG` over `srcE κ` (`FRSoundness4P4bNames.lean:111, 195–209`), which
    must sum three sources of different `e2R` inside one `OnNode κ` (finding 5's lemmas).
- The compiled `.evalM` stays an import of three cells (`FRVIRCompile.lean:419`). A 32-entry
  `packFK` compiles, but it allocates `3·32` fresh cells, most of them unused. Prefer an unmuxed
  `packF` once finding 1's materializations make every entry kind-independent.

### 11. (check, item 5) Gating: nothing is left unbound beyond finding 1, with these notes

- **`N8`.** The zero asserts cover `p`, `s` and `X₃` (`fLrEnd[48,1008)`) and `m̂*`
  (`fEEnd[48,64)`). (ii″) reduces to `η·eq(0, r_E2)·(0 − 0)`; this needs `m̂* = 0` and `X = 0`,
  not `eq = 0`, and both are asserted. `s^P` is then the node's own coefficients.
- **Discharge of `X₃` across the chain.** `X₃[0]` is discharged by `truthChild(P)`; `X₃[1]` and
  `X₃[2]` by `V(P)`'s two `assertZero`s. The last node's own call runs natively. The induction
  closes.
- **Asserts in `gFinE0` that RSV2 does not gate.** The `allK` asserts at
  `FRVIRFinals4.lean:312–313` (`fz`, `fE` tail) are not gated by `act`, and must stay.
- **Segment slots.** Their dead `evalM`/`evalL` imports remain `R`'s (§7 item 4, QUEUE item 7).
  RSV2 neither helps nor hurts.

### 12. (check, item 6) No conflict with S-H4 beyond a trivial merge

- `nd` is parameterized by `piSizeOf seq4` (main's `FRXNd4.lean:95`). `reassemble`/`rsPhase` is
  generic over field sizes (`FRNodeReadW.lean`). `decBudget4` is linear in the word count
  (`FRXProg.lean:162`).
- The only literal is `szPs`'s π size in `FRX4Prog.lean:65`: 798,192 on main, 876,176 on rev44,
  876,304 with RSV2. That is a one-line merge conflict when main merges into rev44.
- The conflicts with B2″ are findings 2 and 3.
