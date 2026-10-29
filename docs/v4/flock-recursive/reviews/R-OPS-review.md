# R-OPS: early review (cheap Opus, 2026-10-29)

Review of `design/R-OPS.md` at `6d1a933`. The reviewer read the documents and the cited Lean, and
built nothing. **Verdict: no blockers.** Seven should-fix items, which the orchestrator routed to R0
and to the plan.

## Soundness

- **Operand binding (should-fix):**
  - `rL`, `pt`, `λ`, `tt` and `rr` are challenge registers of slot 0's replay of V(C), computed by
    hash rows.
  - `PubCellsR4` ties the cells to `fLrEnd`, and `RepS` ties them to the values V(C) used.
  - The argument holds only if no operand is an import or an unconstrained mux cell. Mux cells
    count only if the `kindN` rows force them.
  - R0 must *prove* that rows compute each operand position at every child kind.
- **Kind element (should-fix, load-bearing):**
  - V(P) evaluates at `ν_C = kindOfElem kind`. That cell must be tied to the selector that drives
    slot 0's mux. Otherwise forged outputs can be checked against the wrong kind's op.
  - `kindOfElem` must reject junk values, or the cell needs a range assert.
  - Precondition of R1. (RSV2 had removed the kind element; R-OPS needs it back because V(C) runs
    its own kind's ops.)
- **Padding and tags (should-fix):**
  - N2's `rL` pad coordinate, the two `pad` cells and `evalL`'s third output each need a zero assert,
    or a proof that the op ignores them.
  - The size-tag dispatch (operands of 18/20/29 entries) needs a lemma that no own call has the same
    size.
- **FS order: fine.**
  - The values are absorbed at item 213; κ′ comes after RS1, and `f`'s commitment comes earlier.
  - The asserts use no challenge, so the (β)-style failure cannot occur.
- **`tdot`: sound.**
  - `λ` is the child's own Z2 challenge, and `pe` is a public function of `pt`.
  - The fold `Σ ℓ_b(λ)·pe_b` is an exact identity, not a random combination.
  - Still to check: `RejZ` and the segment slots read nothing else from the 64 values.

## Budget and fit

- **Error budget: correct.**
  - N′ = 106 + 2 pad = 108, so `J_f` = 177 and B′'s row is 178 ≤ 239. εR stays 15/2^124.
  - The §5.3 fallback would add a fourth claim row (`single_B4` arity; E3's charge 4 + 94).
- **N8 fit: correct.**
  - +1,728 B per proof, i.e. +27 blocks, ×8 = 216 blocks.
  - `hEnd` 195,228 → 195,444, which is ≤ `lBase` 195,584.
  - |π| 876,304 → 878,032.

## Cost and plan

- **`rsWeight` at 1–3 ms is optimistic (should-fix):**
  - At C1's measured rate of about 0.27–0.3 µs per term, the memo's 20–25k products give 6–7.5 ms.
  - K-arithmetic mixes coordinates, so its MLE is not "diagonal".
  - The kind factor (68.5k rows of dyadic range sums) is not chain-shaped.
  - The scattered challenge inputs need ≥ 12.8k wiring terms.
  - About 110k witness cells are not audited against the spare region.
- **Plan (should-fix):**
  - (a) Add an explicit prover stage: the `fLrEnd` fields, the Z witness for `t`, and the segment
    slots' `targetSSegI`. R1's end-to-end KAT needs honest proofs.
  - (b) R2's dependencies are not listed: `gap4Imp_of_run`, a prefix form of `compileX_run`,
    widening `flag_gFinE`/`w0V4_eq4` to 168 cells, and the switch to `StmtN4R`.
  - (c) R2 should shrink `rtR`'s import set inside IMP's explicit `SlotImpR` hypothesis, not
    restate `Gap4R`.
  - (d) R0's kill exit points the wrong way: §5.3 adds 94 cells. The real exits are `ldot`,
    keeping `linkWAll` on C1's rows, or εR = 16/2^124.
  - (e) `tdot` changes V for every kind and the segment template now, while the segment slots
    close only in R5. Name the stage that owns `targetSSegI`'s 560-row rewrite.
  - Keep `tplLW_ok` as the (−) control when `tplLW` is retired.
