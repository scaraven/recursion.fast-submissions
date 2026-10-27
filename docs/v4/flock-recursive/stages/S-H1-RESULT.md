# S-H1 (track L-ext, first half): RESULT

Stage S-H1 of `flock-recursive`: the word-machine DSL for the extractor (`FRXDsl`) and the field
arithmetic on the machine's words (`FRXField`), BLUEPRINT §6.3–6.5 and §7 (revision 3, `0d513c9`;
interface change of rev. 3 for S-H1: `for` without a runtime clamp, `compile_runs` under
`BoundsOk`). 2026-10-27, branch `v4/flock-recursive`, uncommitted, build tree
`logs/fr-build-ext` (organiser copy `logs/org`, core `15dac52`). Evidence: **kernel** (theorem
name) or **measured** (log under `logs/S-H1/`). Running notes: `S-H1-JOURNAL.md`.

## 1. What was built

| Module | code (total) | Budget (§7) | Content |
|---|---|---|---|
| `FRXDsl` | 648 (951) | 1,200 | `XIR`, `compile`, `semXIR`, `steps`, `cost`, `outs`, `sizeIR`, `Writes`, `WF`, `Inv`, `BoundsOk`, `toProg`; `compile_correct`, `steps_le_cost`, `outs_le`, `compile_runs`, `run_toProg`, `toProg_outs`, `size_compile`, `frame`, `inv_sem`; DSL controls |
| `FRXField` | 891 (1,200) | 700 | `B64`/`F`/`K` multiply, square, add, inverse (and `β ·`, `α ·`) as straight-line blocks; `*_sem` against `FRField128`/`FRField256`; exact `steps_*`/`cost_*`; `wf_*`; field controls |
| **total** | **1,539** (2,151) | 1,900 | |

Code lines by the core's `scripts/loc.py` (`logs/S-H1/loc.txt`). `FRXField` is over its own
budget by 191 code lines and at the 1,200-line cap; the two modules together are 361 under their
joint budget (see §5, item 9).

### `FRXDsl` (namespace `FR.X`)

- **The language.** `XIR := blk (List Prim) | load | store | input | out | seq | ite |
  loopK c n K body | loopT c n cap body`, `Prim := op | const` (register statements). `compile`
  maps each constructor to a fixed `XStmt` pattern (a block to right-nested `seq`s; a store to an
  address test and the store; a loop to an entry, then `loop c (seq body (c := c − 1))`).
- **Exact semantics.** `semXIR I P s` (memory and output, statement for statement as the machine
  does) and `steps I P s` (the exact step count). **kernel** `compile_correct`:
  `WF P → Inv s.M → Runs I (compile P) s.M s.o (steps I P s) (semXIR I P s).M (semXIR I P s).o`.
- **Loops (BP-E-M5, BP-E-R2-m1).** A loop's iteration count is fixed on entry and counted down
  in a register `c` that the body may not write (`WF`). `loopK` runs `min(M[n], K)` times, the
  clamp compiled in (6 statements), so its cost holds on every tape; `loopT` runs `M[n]` times with
  no clamp (the machine cannot read `t`). `BoundsOk I t P s` (rev. 3's `BoundsOk P tape`) is the
  semantic predicate "every `loopT` entered has a count `≤ cap.eval t`", composed along `seq`
  (`BoundsOk p s ∧ BoundsOk q (semXIR p s)`) and over every iteration.
- **Costs.** `cost : XIR → ℕ → ℕ` is syntactic: blocks `2n − 1`, store 4, `seq` `+1`, `ite`
  `max + 1`, `loopK` `8 + K·(cost body + 3)`, `loopT` `3 + cap(t)·(cost body + 3)`. **kernel**
  `steps_le_cost : WF P → Inv s.M → BoundsOk I t P s → steps I P s ≤ cost P t`; `outs_le`
  likewise for the output words; `compile_runs` is the blueprint's `∃ n ≤ cost P t, Runs … ∧
  o.size ≤ s.o.size + outs P t`.
- **Programs.** `toProg mem mpw P = ⟨mem, mpw, compile (seq (blk initPs) P)⟩` (`initPs` writes
  the four constant cells). **kernel** `run_toProg : regs ≤ mem → WF P → BoundsOk … (initSt …)
  → mem + mpw·t + cost P t + 8 ≤ f → (toProg mem mpw P).run input f = some (semXIR …).o.toList`
  and `toProg_outs` (`≤ outs P t` words). With B8's `Eof`, `Computes` for the extractor is these
  two plus `boundsOk_ext` and a cost lemma per phase.
- **Size.** **kernel** `size_compile : (compile P).size = sizeIR P`, `sizeIR` structural; a routine
  contributes its constant.
- **Memory layout and invariants.** `regs = 256` registers; a `store` to an address below `regs`
  is dropped (the compiled guard), so registers change only through statements that name them.
  Cells `0 … 3` hold `1, regs, 0x1B, 63` (`Inv`); `WF` forbids naming them as a destination and
  keeps loop counters out of their bodies' writes. **kernel** `frame` (an unnamed register is
  unchanged), `inv_sem` (`Inv` holds throughout), `inv_initSt`. Table in the journal.

### `FRXField`

- **Word level.** `redW lo hi = lo ^ clo(hi, 0x1B) ^ clo(chi(hi, 0x1B), 0x1B)` (5 operations).
  **kernel** `Qw_red` (its class is `lo + x^64 hi`), `clmul_poly` (the contract's `clmul` is
  CompPoly's `carryLessMul`, product of the polynomials), `mulBW_spec` (the machine's `GF(2^64)`
  product is `B64`'s), `betaW_spec` (`β ·`), `mulFW_spec` (the machine's `F` product, `F.mul`'s
  Karatsuba with lazy reduction, is `F`'s).
- **Blocks** (operands in consecutive registers, `c₀` first; a result may overwrite an operand):
  `mulBC` (7 statements), `betaC` (7), `invBC` (517: Itoh–Tsujii as `B64.inv`), `mulFC` (29),
  `sqFC` (23), `addFC` (2), `invFC` (554: norm to `B64`, one `invBC`), `alphaC` (22), `mulKC`
  (117: three `mulFC`, `alphaC`, sums), `sqKC` (72), `addKC` (4), `invKC` (690: norm to `F`, one
  `invFC`). As `XIR`: `mulB sqB invB mulF sqF addF invF mulK sqK addK invK := .blk (…)`.
- **Semantics.** **kernel** `mulB_sem`, `sqB_sem`, `invB_sem`, `mulF_sem`, `sqF_sem`,
  `addF_sem`, `invF_sem`, `mulK_sem`, `sqK_sem`, `addK_sem`, `invK_sem`, e.g.
  `Inv s.M → 15 ≤ d → d + 2 ≤ regs → 15 ≤ a → 15 ≤ b →
   rdF (semXIR I (mulF d a b) s).M d = rdF s.M a * rdF s.M b`
  with `*`, `F.sq`, `⁻¹`, `K.sq` … the operations of `FRField128`/`FRField256` (S-A, final).
  Frames: `*_dst` lemmas list every destination of each block; with `rd_runPrims_of_not_writes`
  or `rdF_frame` they give the unchanged cells.
- **Exact step counts** (**kernel** `steps_*`, `cost_*`; the compiled code, `seq` nodes included):

  | `mulB`/`sqB` | `invB` | **`mulF`** | `sqF` | `addF` | `invF` | `mulK` | `sqK` | `addK` | `invK` |
  |---|---|---|---|---|---|---|---|---|---|
  | 13 | 1,033 | **57** | 45 | 3 | 1,107 | 233 | 143 | 7 | 1,379 |

  **One `F` product is 57 machine steps** (BLUEPRINT §6.3 budgets 86): the reduction by two
  `clmul`s with `0x1B` instead of B64's 13-operation shift form, and `β ·` as a shift pair.

## 2. Measurements

**The step count of one `F` product, by the contract's interpreter** (**measured**,
`logs/S-H1/stepcount.log`, `logs/S-H1/probe/StepCount.lean`, `#eval` outside the entry): for each
routine `R`, the least fuel with which `(toProg 260 0 R).run [] f ≠ none`, minus 260 memory words
and the 8 prologue steps, equals the theorem's count for all eleven routines (`mulF`: 57). The
same for `mulF` is **kernel** `Controls.mulF_alone`: halts with `260 + 65`, not with `260 + 64`.
The KAT program (read 4 tape words, `mulF`, output 2 words) halts at fuel `260 + 89` = memory +
8 + `steps` 81 and outputs S-A's KAT product; interpreted by compiled Lean it takes ≈ 1.3 µs per
run (not a cost the certificate depends on).

**Build and kernel** (development VM, 32 vCPU shared, load 6–9):

| Measure | Value | Log |
|---|---|---|
| `lake build FRXDsl FRXField` from built `FRField256` | 60 s wall (FRXDsl 15 s, FRXField 40 s) | `logs/S-H1/build.log` |
| `FRXDsl`, one core (`taskset`), `lean --profile` | 33.7 s wall; kernel 7.1 s; elaboration 22 s | `logs/S-H1/profile-FRXDsl.log` |
| `FRXField`, one core | 71.2 s wall; **kernel 36.0 s** (controls ≈ 16 s); elaboration 33 s | `logs/S-H1/profile-FRXField.log` |
| warnings | 0 | `build.log` |
| axioms (17 main theorems and controls) | `propext`, `Classical.choice`, `Quot.sound` at most | `logs/S-H1/axioms.log` |
| source rule | 35 files, 0 findings | `logs/S-H1/source-rule.log` |

The kernel time is above §7's estimate (5–6 s per kLoC, ≈ 10 s for 1.5 k lines): ≈ 21 s are the
kernel-evaluated controls, because the contract's `clmul` is `Fin.foldl`, whose well-founded
recursion the kernel unfolds slowly (≈ 60 ms per `clmul`; `invF_kat` alone ≈ 10 s). See §5 (10).

## 3. Controls (all **kernel** unless marked)

`FRXDsl` (`FR.X.Controls`; a toy program on the tape `[3, 5, 7, 9]`: for each word read, store
to the heap, load back, accumulate, output; then output the accumulator):

| Control | Kind | What it shows |
|---|---|---|
| `toy_run`, `toy_sem` | positive | the contract's `XProg.run` outputs `[5, 7, 9, 11]` and `semXIR` says the same |
| `toy_run_short`, `toy_steps_le` | positive | the run needs exactly `steps + 8 = 80` steps beyond memory (79 fails); `cost toy 4 = 91 ≥ 72` |
| `toy_wf`, `toy_bounds`, `toy_run_thm` | positive (non-vacuity) | `run_toProg`'s hypotheses hold on a real program; the theorem applies |
| `toy_size` | positive | `size_compile` on it (42 statements) |
| `toyBad_short` | **negative: under-declared cost** | the loop declared with cap `1` has `cost = 34`, and the program does not halt within `260 + 34 + 8` |
| `toyBad_not_bounds` | negative | its `BoundsOk` fails: the hypothesis of `run_toProg`/`steps_le_cost` cannot be dropped |
| `toyK_run`, `toyK_steps` | positive | `loopK` with `K = 2` runs twice on a count of 3; `steps = cost = 58` with no hypothesis |
| `toyG_run` | positive | a store to register 1 is dropped (cell 1 still `256`), a store to the heap is not |

`FRXField` (operands from `FRFieldControls`' first KAT, S-A's independent schoolbook reference):

| Control | Kind | What it shows |
|---|---|---|
| `mulF_kat`, `mulK_kat` | positive | the interpreter outputs the KAT products |
| `sqF_kat`, `sqK_kat` | positive | the machine's squares equal `F.sq`, `K.sq` of the operand |
| `invF_kat` | positive | the machine's `F` inverse (it runs `invB`) times the operand is `1` in `F` |
| `mulF_alone` | positive / measurement | one `mulF` is 57 steps on the contract's interpreter (65 with the prologue; 64 fails) |
| `mulF_bad_const` | **negative** | with the reduction-constant cell overwritten (a non-`WF` program) `mulF` does not give the product: `Inv` is needed |
| `invK_guard` | non-vacuity | `invK_sem`'s hypotheses hold at the prologue's state |
| `invK` KAT (**measured**, `#eval`) | positive | machine `invK` = `FRField256`'s compiled `K.inv`, and `x · x⁻¹ = 1` (`stepcount.log`); not kernel-checked: the kernel overflows its recursion depth on 1,379 steps of `Fin.foldl` `clmul` |

Non-vacuity of the `*_sem` hypotheses: `inv_initSt` (every program's start state satisfies
`Inv`), and the register bounds are numerals. The specs are not tautologies: they equate the
machine's words with `FRField*`'s operations, and `mulF_bad_const` shows a machine that does not
satisfy them.

## 4. How the later L-ext stages use this

- Write each phase as an `XIR` term built from routines; prove `WF` by `simp` with `wf_*`
  (destinations ≥ 4) and the loop-counter side conditions (`Writes` is syntactic: the routines'
  `*_dst` lemmas list their writes).
- `cost` per phase by `simp only [cost, cost_mulF, …]`; never unfold a routine. `sizeIR` likewise
  (`sizeIR (.blk ps) = cost (.blk ps) 0`).
- `ext_halts`: `run_toProg` + `toProg_outs` + `boundsOk_ext` (every `loopT` count is a length word
  of the tape or a quantity bounded by one) + `cost extIR t + 8 ≤ fuel t − mem − mpw·t`.
- `ext_good_tape`: over `semXIR`, phase by phase; a phase lemma composes routine lemmas with
  `set Mk := …` and frame facts (pattern: `mulKC_spec`, `invKC_spec`).
- Registers: user code uses `64 … 255`; cells `39 … 63` are free; routines need their operands
  above their scratch (`B64` ≥ 9 or 12, `F` ≥ 15 or 19, `K` ≥ 31 or 39).

## 5. Deviations from the blueprint (rev. 3 §6.3–6.4), with reasons

1. **Field routines are named `blk` terms, not `XIR` constructors.** `mulF d a b := .blk (mulFC d a
   b)` etc. The compiler, `semXIR`, `cost` and `sizeIR` stay generic (one case for blocks), and
   routines compose by list concatenation at no step cost (`seq` of two blocks costs the same as
   their concatenation). The "never unfold" property comes from the `cost_*`/`steps_*`/`*_sem`
   lemmas, which `simp` uses without unfolding the definitions.
2. **Two loops instead of one `for`.** `loopT` is rev. 3's clamp-free `for` (`BoundsOk`).
   `loopK` adds a constant clamp compiled into the code: for counts read from `π` (arbitrary on
   the domain) with a kind constant as the bound, its cost needs no `BoundsOk` obligation.
3. **The loop shape.** The count is fixed on entry and counted down in a register (not
   `while M[i] < M[bound]`), so the body may change `M[n]` freely; per iteration `cost body + 3`
   (rev. 3: `+ 4`), entry `+ 3` (`loopT`) or `+ 8` (`loopK`). An up-counting index, when needed,
   is the body's own register.
4. **`compile_sem` is `compile_correct`**, exact and stronger: the compiled code runs to
   `semXIR`'s state in exactly `steps` steps. "A run's final state is `semXIR`'s" in the
   blueprint's form would hold only up to `rd` (arrays with equal reads can differ in size), and
   the extractor needs only the output, which `run_toProg` gives as an equation.
5. **`Inv`, `WF` and the store guard** are new: exact semantics of compiled loops and field code
   needs constant cells (`1`, `regs`, `0x1B`, `63`) and counters that no store can reach.
   Stores cost 4 steps (guard), not 1.
6. **57 steps per `F` product** instead of 86 (§6.3), from the `clmul`-based reduction. The
   blueprint's fixed term `2^47.15` assumed 86; with 57 the products' share drops by a third.
7. **`invF` is a 554-statement block** (Itoh–Tsujii inline, 1,107 steps); a loop form would be
   shorter in program size but no cheaper in steps. `invK` 1,379 steps.
8. **`regs = 256`.** The blueprint did not fix a layout. 4096 made the kernel controls 5× slower
   (journal); 192 user registers are assumed enough for the extractor (open question 1).
9. **Lines.** `FRXField` 891 code lines against 700 (the inverses, the composition proofs and
   the controls); at the 1,200-line cap after moving generic block lemmas to `FRXDsl`. Together
   1,539 against 1,900.
10. **Kernel time.** 43 s for the two modules (one core), ≈ 21 s of it kernel-evaluated controls
    (the contract's `clmul` is well-founded `Fin.foldl`). Dropping `invF_kat` saves ≈ 10 s.

## 6. Open questions for the orchestrator

1. Is `regs = 256` (192 user registers) enough for the extractor phases? Raising it is one
   definition (`regs`, `kval`, `initPs`, `inv_consts`) and costs kernel time only in controls.
2. `FR.lean` (the root importing all modules) is not this track's file: please add
   `import FRXDsl` and `import FRXField`.
3. Keep `invF_kat` (≈ 10 s kernel) as the inverse's positive control, or rely on `invF_sem` and
   the `#eval` KATs in `stepcount.log`?
4. Blueprint changes to record: §6.3 "86 steps per F product" → 57 (and the fuel margin);
   §6.4's constructor list (blocks, `loopK`/`loopT`), `cost` formula (`+3` per iteration, entry
   `3`/`8`, store `4`), `compile_sem` → `compile_correct`, the memory layout and `Inv`/`WF`.
5. Golf targets (single-core elaboration): `frame` (≈ 8 s), `compile_correct` (≈ 6 s),
   `size_sem`, `steps_le_cost`, `outs_le` (≈ 3.5 s each); in `FRXField` the flat `mulFC_run`
   evaluation (≈ 5 s) and the composition proofs.

## Fix pass

This pass answers `reviews/S-H1-review.md` (verdict ACCEPT, no majors) as the coordinator scoped
it: m2, m4, m5 and the golf suggestions. m1, m3, m6 and m7 are handled elsewhere (S-H2, the
blueprint, `FR.lean`).

| Finding | Change |
|---|---|
| S-H1-m2 | **Fixed.** `WF` for `loopK c n …`/`loopT c n …` now requires `n ≠ c ∧ n ≠ cTmp`, as `(4 < c ∧ n ≠ c ∧ n ≠ cTmp) ∧ c < regs ∧ ¬ Writes b c ∧ WF b`. The docstring says why: the entry writes `c` and `cTmp` before it reads `n`. Every proof and `toy_wf` go through unchanged. |
| S-H1-m4 | **Fixed.** `invK_guard` now instantiates `invK_sem` at `oneK`, the prologue's state with the `K` element `1` in registers `64 … 67`. It also proves `rdK oneK.M 64 = 1` in the kernel, so the operand is nonzero. The `invK` value KAT stays an `#eval` **measurement** in `logs/S-H1/stepcount.log`, not a control (§3's last row should read that way). |
| S-H1-m5 | **Fixed.** Dropped `invF_kat`, `sqF_kat` and `sqK_kat`; `invF_sem`, `sqF_sem` and `sqK_sem` cover them. Kept `mulF_kat`, `mulF_alone`, `mulF_bad_const`, `mulK_kat` and all `FRXDsl` controls. `unProg` was used only by the dropped controls, so it moved to the probe. |
| Golf: per-constructor `frame`/`compile_correct` | **Declined.** Their cost (≈ 8 s and ≈ 6 s) is elaboration, not kernel: `FRXDsl`'s kernel time is 6.4 s, of which ≈ 5 s are the controls. Splitting would not change the kernel time, and the token budget of this pass did not allow it. It remains a target for a golf stage. |
| Golf: `wf_blk_of_dsts` + `decide` | **Argued.** `WF (.blk ps)` is by definition `∀ p ∈ ps, 4 ≤ p.dst`, so each `wf_*` is already that lemma applied to the routine's `*_dst` (one line each). A `decide` on a destination list is impossible here: the lists contain the symbolic registers `d, a, b`. |

**Statements.** No public theorem's statement changed except through `WF`'s new conjunct (m2) and
the new `invK_guard` (m4). The dropped controls are `invF_kat`, `sqF_kat`, `sqK_kat` and the
definition `unProg`.

**Measurements** (one core, `taskset`, `lean --profile`; logs `logs/S-H1/profile-fix-*.log`,
`loc-fix.txt`):

| | before | after |
|---|---|---|
| kernel, `FRXDsl` | 7.1 s | 6.4 s |
| kernel, `FRXField` | 36.0 s | **20.7 s** |
| kernel, total | 43.1 s | **27.1 s** |
| wall, `FRXDsl` / `FRXField` | 33.7 s / 71.2 s | 34.7 s / 43.1 s |
| code lines `FRXDsl` / `FRXField` / total | 648 / 891 / 1,539 | 649 / 880 / 1,529 |

The remaining `FRXField` kernel time is about 4 s of controls (`mulK_kat` 2.4 s). The rest is
the proofs, spread over many declarations, none above 1 s.

**Checks.** `lake build FRXDsl FRXField`: 0 warnings. Source rule: 0 findings. Axioms: at most
`propext`, `Classical.choice` and `Quot.sound` (`logs/S-H1/axioms.log`). The step-count probe
was re-run and agrees with the theorems (`logs/S-H1/stepcount.log`).
