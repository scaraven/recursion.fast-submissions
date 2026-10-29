# R1 (track R-OPS, V side): RESULT — stopped at a design blocker

Stage R1, 2026-10-29. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `616b57c`). No
Lean or prover source was edited and nothing was committed. Build tree `logs/fr-build-R1` is an
unmodified copy of `logs/fr-build-IMP`, kept for the next attempt. I built nothing, so there are no
measurements.

## 0. Verdict

**The public-op route (R-OPS §3.3, §6) is unsound at recursion depth ≥ 2 as specified.** V(P)'s
recompute ops are themselves un-templated ops of V(P). At the grandparent G's slot 0 they become new
imports, and discharging those imports regresses without end. I stopped before implementing. The
argument is below. The memo, the review and R0 all miss it, because they look only at the child's
*own* op instances (the "unique" `evalL` / `targetS` / `linkWAll` ops of `group-N.txt`).

## 1. The argument

1. **What slot 0 replays.** G's slot 0 replays the whole program V(P), finals included, which
   includes the new `rsvOps2` block. `impRP rt π` (`FRNodeRows4Rep.lean:486`) collects the import
   registers of **every** op of `protoProg π` that has no template. The compile sends `evalL`,
   `targetS` and `linkWAll` to `imports cs [...]` (`FRVIRCompile.lean:416–422`). Of the ops
   `rsvOps2` would use, only `eqPt`, `mulF`/`addF` and the like have templates.
2. **The new import.** Under R-OPS, V(P) has two instances of each op:
   - its own call, which G carries and V(G) recomputes;
   - the child-check call `op_{ν_C}(in_C)`, asserted equal to `out_C`.

   At G, the child-check call is an import. Its value is free, and the slot's assert row merely
   equates it with `out_C`. G's relation therefore establishes only that a modified V′(P), whose
   child checks are vacuous, accepts π_P.
3. **The consequence.** From V′(P) accepting:
   - P's circuit is satisfied (the PIOP checks are intact);
   - `PubCellsR4` ties C's own-op imports in P's slot 0 to P's `fLrEnd` (B′ is intact).

   But nothing checks `out_C = op_{ν_C}(in_C)`. So V′(C)'s own `evalL` / `targetS` / `linkWAll`
   values are arbitrary. They feed C's claimN(E4), the Z3 head and the link sum, so C's PIOP can be
   forged. Knowledge soundness fails at depth 2.
4. **Discharging the new import regresses.**
   - V(G) would have to recompute P's child-check call on C's data. G must then carry P's carried
     C-block, and V(G) gains a third instance per op.
   - G's parent must then bind that instance too.
   - Each level carries the previous level's block plus its own, so the carried cells grow linearly
     with depth.

   I checked these variants:
   - merging own and child into one instance (6 outputs, or a 0/1 check output);
   - deferring each node's own value to its parent;

   Each still leaves at least one un-templated instance whose operands are the previous level's data,
   so the regress remains.
5. **Why RSV2 is not affected.** In `rsvEOps` (`FRVIRFinals4.lean:281`), the only un-templated op is
   the **one** stacked `evalM`. At the grandparent, G's own reserve sumcheck verifies its output, not
   a recompute. That is a fixed point. `eqPt` is templated (`FRVIRTplExt.lean:171`).

   Only two kinds of op are safe for a check of the child's data:
   - ops with replay templates;
   - ops reducible by a sumcheck into the node's own single call.

## 2. Ways out (for the orchestrator)

| Route | Content | Cost | Note |
|---|---|---|---|
| **(a) templates at slot 0** for the child's own `evalL`, `targetS`, `linkWAll` | No carry, no format change, no V(P) recompute. `linkWAll` already has C1's `tplLW` (`rtK`/`rtST0`; 42,601 rows, 52–60 ms VM). `evalL` and `targetS` need templates. | V: C1's 52–60 ms, plus `targetS` (≈ 24k products, about 7 ms at R0's 0.29–0.33 µs per term), plus `evalL` (≈ 82k products direct, about 25 ms; 15–25k, 5–8 ms, with the carry automaton). Roughly +90 ms VM per node, against `verify_s` 10 s. | **Recommended** under "accepted, not fast". R-OPS §3.1 and §3.4 priced this route. Keep `tplLW` and `tplLW_ok`. |
| (b) reserve for `evalL` (R-OPS §3.2) + (a) for `targetS`, `linkWAll` | `evalL` becomes a fixed point like RSV2 (Lr1's spare coordinate, E4's `κ_E⁵` term) | V about −8 ms against (a)'s `evalL`. Soundness as RSV-S + S2a + S2b + S3 again. | Only if `evalL`'s template is too slow. |
| public-op with templated recompute | V(P)'s recompute calls get templates at G's slot 0 | at least (a)'s cost, plus the carry and the format | dominated by (a) |

`rsWeight` (R-OPS §5) is unaffected: it was already planned as a replay (R3/R4).

## 3. The orchestrator's two messages

- **"Plain 168 vs `tdot`."** This is moot under the blocker. Had the route been sound, I would have
  taken the **plain 168** variant, for three reasons:
  - no `Op` or template change;
  - 168 ≡ 0 (mod 4), so no pads;
  - B′ row 238 ≤ 239, and N8 `hEnd` 195,564 ≤ 195,584.

  I would have kept `evalL`'s `r4` as `rsvRel`'s `p_y`, whose entry 24 is the RSV2 mux cell, and
  left R2 to rely on the existing `× one` product row.
- **Wait loops.** None used.

## 4. Files

- Written: `docs/v4/flock-recursive/stages/R1-RESULT.md` (this file), `R1-JOURNAL.md`.
- Created: `logs/fr-build-R1` (a copy of `fr-build-IMP`; delete it if (a) goes to another tree),
  `logs/R1/` (empty).
- No source touched; red set unchanged from HEAD.
