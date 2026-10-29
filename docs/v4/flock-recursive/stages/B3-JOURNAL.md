# B3 (track L-circ): JOURNAL — `compileFromX_run`, the run's existence on the read trace

Base: HEAD `69d0c4e`. Build tree `logs/fr-build-B3` (copy of `fr-build-orch`, `MINE=`). Logs `logs/B3/`.

## 0. Reading (2026-10-29)

- PACK-4.4 §4: the theorem is S-E14's `compileFromX_soundR` with the trace threaded through, a
  per-ask obligation `AskBound` defined on the trail (pins, FS links, Merkle mux rows).
- `exec` fails only at an ask whose computed query differs from the trace's (or when the trace runs
  out). `s.ok` is irrelevant to existence.
- The obstacle to stating the run theorem as S-E14 states soundness: `SlotRun`'s aux/import/foreign
  facts mention the run's final state, which the theorem must construct. Resolution: the
  **answer-driven run** `execA` (exec without the query comparison, answers from the trace). It is
  total once the trace has as many entries as the program has asks, and its final state is a
  function of the trace alone, so the residual facts are stated on it. The theorem shows
  `exec = execA` under the per-ask obligations.
- The byte operands of asks (`askSeed`'s `hdr`, `askAbsorb`'s message, `askCol`'s column) are
  untracked registers (`Val.b`, slot `none`): `InvK` says nothing of them. In every generator
  (`seedOps4`, `absorbOps`, `uniOps`, `posOps4`) the byte operand is the register appended by the
  immediately preceding `piField`. So the ask obligation sees the previous op (`pre`) and the fact
  `PrevOk pre regs` (the last registers are `pre`'s results), from which a template proves
  `rd regs m = .b (π bytes)`.
- The answer register of an ask is discharged by the ask template too (the arena alias, or two
  rows on the fresh import cells), not assumed: the assumed imports are `impAX` (neither an ask nor
  replay-covered).

## 1. Build (2026-10-29)

- `FRNodeRun4`: `execA`, `execA_some`, `execA_of_exec`; `PrevOk`, `AT`, `AskCtx`, `ATAsk`, `ATImp`,
  `ATOk`, `AskBound` (+ both directions to `ATAsk`); the cell readings; `askRowsX`, `impAX`;
  `compileFromX_run` (S-E14's induction, `exec` replaced by `execA` in the hypothesis and produced
  in the conclusion), `compileX_run`. The proof is S-E14's almost line for line: the vals branch
  gains a third import source (`A.cov`, by `ATImp`), the ask branch takes the answer from `ATAsk`
  instead of `hi` and passes `exec`'s query check with `ATAsk`'s `e.1 = q`.
- Mid-way addition: `AT.cov`/`ATImp`. S-E14's `RTOk` quantifies over every input, so no replay
  template can bind a proof field (`piElem`, `piDigest`: their value is `inp.π`'s bytes) to the
  arena; at a fixed input and trace these are what PACK-4.4 §1.3 aliases. Without `ATImp` they would
  all sit in `SlotRunA`'s residual imports, stated on concrete registers of the 106 k-op run, which
  no row-side track can discharge without evaluating the program.
- `FRNodeRun4S`: `protoProg_items` (both prototypes ask `itemsOf seq4`: `progNodeGK_rel`/
  `progSegG_rel`, `Op.at` keeps `item?`, `items_gen4`), so the answer-driven run on any 8,905-entry
  trace exists and uses it up (`execA_proto`); `SlotRunA`, `SlotImpA`, `slotImp_of_runA`,
  `askIRows4`, `askHolds_of`, `gap4Imp_of_run`.
- `FRNodeRun4Ctrl`: the controls; `run_ctl` runs `compileX_run` end to end on `[input 0,
  askSqueeze 0]` with a real template (`pinSq`), every hypothesis met at a concrete assignment.
- All green first or second try; no kernel-heavy step (the only evaluations are `rfl` on 2-op
  programs). Type checking ≤ 0.3 s per module.
