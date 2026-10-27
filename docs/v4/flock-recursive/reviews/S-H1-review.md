# S-H1 (L-ext, first half): adversarial review

Reviewed: `stages/S-H1-RESULT.md`, `submissions/flock-recursive/lean/FRXDsl.lean` (649 code
lines) and `FRXField.lean` (891), committed in `f7c51e1`. Spec: BLUEPRINT revision 3.4 §6.1,
§6.3–6.5, and `.contract/RecursionFast/Contract/{Machine,Extractor}.lean`. Checklists:
adversarial-review, lean4:review.

## Evidence

| Check | Result |
|---|---|
| Build in a fresh tree (`logs/S-H1-review/`, copy of `gen.sh`, `timeout 1500`) | green, 0 warnings, 1 min 34 s wall on the shared VM (`logs/S-H1-review/build.log`) |
| Source hashes before and after | unchanged (`logs/S-H1-review/sources.sha256`) |
| `#eval` | none in the entry. The `invK` KAT and the step-count measurement are in `logs/S-H1/probe/StepCount.lean`, outside `submissions/` (gitignored `logs/`). The RESULT says so, and the source rule's 0 findings confirm it |

## Does it compose into `Computes`? Yes, without unfolding the program

With `ext := toProg mem mpw extIR`, `E := (ext.run · ·).bind decodeWit` (B8's `Eof`) and `fuel t`:

- **`Computes`.** Contract: `∃ o, ext.run tape (fuel t) = some o ∧ o.length ≤ outCap ∧ decodeWit o
  = E …`. The supply:
  - `run_toProg` gives `ext.run tape f = some (semXIR … extIR (initSt …)).o.toList` from
    `regs ≤ mem`, `WF extIR`, `BoundsOk tape t extIR (initSt …)` and
    `mem + mpw·t + cost extIR t + 8 ≤ fuel t`, with `t = input.length` as `Computes` uses it;
  - `toProg_outs` gives `o.length ≤ outs extIR t`, so `outs extIR t ≤ 2^24` closes the cap;
  - the `decodeWit` conjunct is `E`'s definition.
- **Cost, `progCap` and fuel without unfolding.** `cost`, `outs` and `sizeIR` are structural, and
  the routines carry `cost_*`/`steps_*` lemmas, so `cost extIR t` is computed per phase by `simp`.
  `size_compile` gives `(toProg …).body.size = sizeIR (seq (blk initPs) extIR)` for `progCap`.
  `run_of_runs` is the contract library's, so `XProg.run`'s memory charge is accounted exactly
  (`mem + mpw·t`).
- **`compile_correct`** is exact: `Runs` in exactly `steps`, as the library's `Runs` requires.
  **`compile_runs`** is the blueprint's `∃ n ≤ cost P t` form under `BoundsOk`.
- **Controls.** `toy_run` / `toy_run_short` / `toyBad_short` show the interpreter, the exact step
  count and an under-declared cap failing on the contract's own `XProg.run`.

**`BoundsOk` on adversarial tapes.**
- `loopK` needs no obligation: the clamp is compiled, and its cost holds on every tape.
- `loopT` needs `count ≤ cap.eval t` at every entry. This is dischargeable on the domain of
  `Computes`, whose tapes are always well-formed `extractorInput c π L` (the quantifier is over
  `c π L`, not word lists). For a count loaded from the `|L|` word, `|L| = L.length ≤ t/5`
  (every entry is ≥ 5 words, and `L.length < 2^64` since the tape has ≤ 2^64 words).
- Neither the DSL nor `run_toProg` forces the count to be such a field, so the obligation is a
  semantic proof over `semXIR` of everything before the loop. See S-H1-m1 for the rule that keeps
  it local.

**The memory invariants hold against the tape.**
- `input`, `load` and `blk` destinations are syntactically `≥ 4` (`WF`).
- A `store` to any address `< regs` is dropped by the compiled guard (`storeM`, `toyG_run`).
- Loop counters are `> 4`, `< regs` and unwritten by their bodies.
- So no tape word can reach cells `0…3` or a live counter (`frame`, `inv_sem`). Adversarial
  addresses can only scribble on the heap (`≥ 256`), which is the extractor's own data.
- One footgun, harmless for soundness: `loopK c n` with `n = c` or `n = cTmp` reads the
  overwritten cell. The semantics follow the compiled code (both use `entryK`), so nothing is
  false, but a program meaning `min(M[n], K)` gets `K` (S-H1-m2).

**The field routines.**
- `mulF_sem` … `invK_sem` equate the machine's registers (`rdF`, `rdK`) with `FRField128`/
  `FRField256`'s `*`, `F.sq`, `⁻¹`, `K.sq`. `⁻¹ 0 = 0` is consistent with the field instances.
- The proofs go through the `clmul`/`CompPoly` bridge (`clmul_poly`, `mulBW_spec`, `Qw_red`) and
  are kernel-checked.
- `mulF` = 29 statements = 57 steps (`2·29 − 1`). This agrees with `steps_mulF`/`cost_mulF`, the
  kernel control `mulF_alone` (65 halts, 64 fails, prologue 8) and §6.3 rev. 3.4.

## Majors

None. The statements are true as written, compose into `Computes` as above, and are
non-vacuous: `toy_*`, the KATs, `mulF_bad_const` and `toyBad_*`.

## Minors

- **S-H1-m1 (`BoundsOk` discipline, owner L-ext's next stage).** `cost`'s `loopT` charges
  `cap(t)` per entry, so a `loopT` nested in a `loopT` costs `t²`, and the model has no
  amortisation (e.g. `Σ_entries ⌈|q|/8⌉ ≤ t`). State in the blueprint (§6.4):
  - no tape-length loop inside a tape-length loop; skip a query by pointer arithmetic, not a loop;
  - every `loopT` count register is loaded by `input` from a tape length field (`|L|`) right
    before the loop and is unwritten until the entry, so `boundsOk_ext` is a local `frame`
    argument and not a whole-program `semXIR` induction.
- **S-H1-m2.** `loopK c n` / `loopT c n` with `n ∈ {c, cTmp}` silently changes the count.
  `entryK` writes `c` and `cTmp` before reading `n`. Add `n ≠ c ∧ n ≠ cTmp` to `WF` (one line;
  `toy_wf` etc. unchanged), or document it next to `XIR.loopK`.
- **S-H1-m3 (for S-H2, found here).** The skip of a log entry, `1 + ⌈|q|/8⌉ + 4` words, must not
  compute `(|q| + 7)/8` in 64-bit words. On the domain, `|q| < 2^64` can be `≥ 2^64 − 7`, which is
  representable since the tape may have up to `2^64` words. Then `|q| + 7` wraps, the parse of every
  later entry goes wrong, and `final` (good tapes may carry adversarial huge queries) fails to
  extract. Use `|q| >> 3` plus `(|q| & 7 ≠ 0)`, which does not overflow.
- **S-H1-m4 (controls).**
  - `invK_guard` instantiates `invK_sem` at the all-zero register, `0⁻¹ = 0`. That shows the
    hypotheses are satisfiable, but it is the degenerate point.
  - The value-level `invK` KAT exists only as an `#eval` outside the entry. Since `invK_sem` is
    proved, this is acceptable, but the RESULT should call the `#eval` evidence a measurement, not
    a control.
- **S-H1-m5 (kernel cost).** 43 s for 1.5 k lines, about 28 s/kLoC, 5× the calibration. About
  21 s of it is kernel-evaluated controls through the contract's `Fin.foldl` `clmul`, which cannot
  be changed.
  - Drop `invF_kat` (≈ 10 s; `invF_sem` is proved).
  - Drop `sqF_kat` and `sqK_kat`, which follow from `sqF_sem`/`sqK_sem` and are not independent of
    `mulF_kat`.
  - Keep `mulF_kat` (independent schoolbook KAT), `mulF_alone` (the exact step count on the real
    interpreter), `mulF_bad_const` (negative), `mulK_kat` (one `K` composition) and the toy
    controls.
- **S-H1-m6 (blueprint bookkeeping, RESULT open question 4).** §6.4 should record: blocks as named
  `blk` routines; `loopK`/`loopT` and their costs (`+3` per iteration, entry `8`/`3`, store `4`);
  `compile_correct`; the layout (`regs = 256`, cells `0…3` constant, scratch `4…38`, user
  `≥ 64`); `Inv`/`WF`.
- **S-H1-m7 (`FR.lean`, open question 2).** `FRXDsl`/`FRXField` are not imported by the root, so
  they are outside `Solution`'s closure until imported (as for S-C).

## Golf suggestions (for the implementer)

- `frame` (≈ 8 s elaboration) and `compile_correct` (≈ 6 s): split the constructor cases into
  per-constructor lemmas (`frame_blk`, `frame_loop`, …), so each `simp` set is small. The RESULT
  names both as targets.
- `FRXField`'s `*_dst` lists and `wf_*` lemmas look generated case by case. A single lemma
  `wf_blk_of_dsts : (∀ p ∈ ps, 4 ≤ p.dst) → WF (.blk ps)`, plus a `decide` on each routine's
  destination list, would replace most of them.
- The controls above (m5).

## Verdict

**Accept S-H1.** `compile_correct`, `steps_le_cost`, `outs_le`, `compile_runs`, `run_toProg`,
`toProg_outs` and `size_compile` are true as written against the contract's `XProg.run`, `Runs`,
`Computes`, `outCap` and `progCap`. They compose into `Computes ext E fuel` through per-phase cost,
output and `BoundsOk` lemmas, with no unfolding of the program. `BoundsOk` is dischargeable on the
contract's domain, the memory invariants protect the constants and counters against any tape, and
the field routines are tied to S-A's operations with exact step counts (57 per F product).
Address m1–m3 before S-H2 writes the log index; m4–m7 are housekeeping.
