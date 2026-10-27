# S-H1 (track L-ext, first half): journal

Running notes for a successor. Read "Design in one page" first.

## Design in one page

- **`XIR`** (`FRXDsl`, namespace `FR.X`): `blk (List Prim)` (straight-line `op`/`const`),
  `load`, `store` (guarded), `input`, `out`, `seq`, `ite`, `loopK c n K body` (constant clamp
  compiled in), `loopT c n cap body` (no clamp; BP-E-R2-m1, blueprint rev. 3 §6.4).
- **Semantics are exact.** `semXIR I P s` is what the compiled code does to memory and output,
  statement for statement; `steps I P s` its exact step count. `compile_correct` is
  `Runs I (compile P) s.M s.o (steps I P s) (semXIR …).M (semXIR …).o` — no `≤`, no
  equivalence up to scratch. Everything the compiler adds (store guard flag, loop clamp flag,
  counters) is visible in `semXIR`. The routines' `*_sem` lemmas then talk only about the cells
  they promise; a frame lemma covers the rest.
- **Why exactness needs two invariants.** A loop decrements its counter with `sub c c cOne`, the
  store guard compares with `cBase`, the field code reads `cRed = 0x1B` and `c63 = 63`. So
  `compile_correct` assumes `Inv` (cells `0 … 3` hold `1, regs, 0x1B, 63` and the memory has the
  registers) and `WF` (no destination below `4`; loop counters above `cTmp = 4`, below `regs`,
  not written by their body; stores do not take their address from `cTmp`). `inv_sem`: `Inv` is
  preserved by every `WF` program. Stores to addresses below `regs` are dropped by the compiled
  guard, so `WF` is syntactic (no store can hit a counter or a constant).
- **Costs.** `cost P t` is syntactic, affine in `t`. `steps_le_cost` needs `BoundsOk I t P s`
  (rev. 3's name): each `loopT` entered has a count `≤ cap t`. `loopK` needs nothing (its clamp is
  compiled). `BoundsOk` is a semantic predicate along the run, composed by `seq` (`p` at `s`, `q`
  at `semXIR p s`); for a phase without `loopT` it is `True` by `simp`.
- **Program.** `toProg mem mpw P = ⟨mem, mpw, compile (seq (blk initPs) P)⟩`; `run_toProg`: with
  `regs ≤ mem`, `WF P`, `BoundsOk` from `initSt`, and fuel `≥ mem + mpw·t + cost P t + 8`, the
  run is `some (semXIR …).o.toList`. The extractor's `ext_halts` is this plus `outs` and the
  per-phase cost lemmas.

## Memory layout (normative for the later L-ext stages)

| cells | role |
|---|---|
| 0 | `cOne` = 1 |
| 1 | `cBase` = `regs` = 256 |
| 2 | `cRed` = `0x1B` |
| 3 | `c63` = 63 |
| 4 | `cTmp`, compiler scratch |
| 5 … 38 | field-routine scratch (`B64` 5–11, `F` 5–18, `K` 5–38) |
| 39 … 63 | free (no routine writes them) |
| 64 … 255 | user registers |
| 256 … | heap (stores below 256 are dropped) |

`regs` was 4096 first; the kernel controls run the contract's interpreter on `regs`-sized
memories, and at 4096 the `FRXDsl` controls cost 25 s of kernel time (Array updates on a
4,100-element list). At 256 they cost ≈ 5 s. `regs` is one definition; raising it changes the
`256` literals in `kval`/`initPs`/`inv_consts` and nothing else.

## The `GF(2^64)` product on the machine

`clmul`/`clmulh` give the 128-bit product; the reduction uses `clmul` with `0x1B` twice:
`redW lo hi = lo ^ clo(hi, r) ^ clo(chi(hi, r), r)`, 5 operations (B64.reduce's shift form is 13).
`Qw_red`: its class is `lo + x^64 hi`, from CompPoly's `toPoly_carryLessMul` (the contract's
`clmul` is `carryLessMul (w := 128)` by `rfl`), `toPoly_halves`, `carryLessMul_lt` (the high
word of `hi·r` has 5 bits, so the second product has no high word). Everything else is in the
quotient: `wB_eq_of_Qw` turns a class equation into word equality through `toBF64_injective` and
`BF64.toQuot_injective`, and `F.mul_c₀/c₁` (S-A) give the `F` product's coordinates.

## Proof engineering notes

- `rfl` on `(initSt m).M = runPrims initPs (Array.replicate m 0)` takes 9 s of elaboration (the
  unifier unfolds `runPrims` before the projection). Use `initSt_M`/`initSt_o` (by `simp only
  [initSt]`) and `rw`.
- A defeq check between two `Runs` facts that differ in the step count unfolds `Runs` and runs
  `exec`; always go through `runs_mono_eq h (by omega)`.
- Flat evaluation of a block with symbolic registers:
  `simp (disch := ((try simp only [size_set]); omega)) only [rd_set_self, rd_set_ne, …]` after
  unfolding the block to nested `setIfInBounds`. Good up to ~30 statements (`mulFC_run`, 5 s).
  Larger routines compose: `set Mk := runPrims block M(k-1)`, then `Inv`, value and frame facts
  per block, then one `rw`/`simp only` chain (`invFC_spec`, `mulKC_spec`, `invKC_spec`).
- `Fin.foldl` (the contract's `clmul`) is well-founded recursion; the kernel evaluates it slowly
  (≈ 60 ms per `clmul`). An `F` inverse in the kernel is ≈ 10 s; a `K` inverse overflows the
  kernel's recursion depth. Kernel controls therefore stop at `invF`; `invK` is checked by
  `#eval` in `logs/S-H1/stepcount.log` and instantiated by `invK_guard`.
- A line break after `;` inside `(by …; …)` must keep the continuation indented past the `by`
  block's column, or the block ends (`omega` becomes an unknown identifier).

## Timeline

1. Read TRACK-RULES, BLUEPRINT §6, §7, §10, the contract (`Machine`, `Extractor`), the library
   (`Machine`), `LogScan`, the probes `B8`, `BPeng`, `BPeng2`.
2. `FRXDsl` definitions, then the theorems (frame, `inv_sem`, `compile_correct`, bounds, size,
   `run_toProg`). Interface change during the stage (coordinator, rev. 3 `0d513c9`): `for` without
   runtime clamp, `compile_runs` under `BoundsOk P tape` — the design already had it (`CapsOK`
   renamed `BoundsOk`).
3. `FRXField`: word-level polynomial lemmas, `mulFW_spec`; blocks `mulBC`, `betaC`, `invBC`,
   `mulFC`, `sqFC`, `addFC`, `invFC`, `alphaC`, `mulKC`, `sqKC`, `addKC`, `invKC`, with exact
   lengths; XIR wrappers, `*_sem`, `steps_*`, `cost_*`, `wf_*`.
4. Controls; `regs` 4096 → 256 for kernel cost; step counts measured (`StepCount.lean`).
