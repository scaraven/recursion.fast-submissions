# S-E5 (track L-circ): JOURNAL — templating the node circuit's skeleton

Stage S-E5 of `submissions/flock-recursive`, 2026-10-28, branch `v4/flock-recursive` (HEAD
`5fc7d3b`, uncommitted). Build tree `logs/fr-build-e5` (`snap.sh`: HEAD's modules, L-circ's
symlinked to the worktree; probes in `logs/fr-build-e5/probe/` as `lean_exe`s of the same tree).
Every `lake`/probe run in the 16 GB scope; probes on one core (`taskset -c 9`). Logs `logs/S-E5/`.

## 0. Baseline (HEAD, `finE` already calls `evalM`)

- V (N30, `vtime v N`): **685.7 ms best, 709.7 ms median** of 9 (`vtime-N-base.log`): S-E4's
  150 ms plus the flat `evalM` (545 ms).
- Slot 0's skeleton (`stat-0.log`, probe `E5Stat`): 120,952 rows, 102,922 ops.
  - Merkle step windows (7 ops from `piDigest fSibs`): 48,796 rows, 207 k entries;
  - Horner blocks (`encOps`, from the first `tensorW`): 48,258 rows, 306 k entries;
  - the rest: 23,898 rows, 163 k entries, of which `eqTable` 18,681 rows (8 ops, one of them
    `colW`'s 14 coordinates: 16,383 rows) and `mulKF` 58 k entries (the `dotKF` outputs are
    sums of `n` locals, so every consumer reads 20–68 cells per coordinate).
- Positions (`stat-pos.log`, `idx` … cap `assertEq`): (steps, rows, cells) = (5, 36, 69) ×126,
  (6, 42, 78) ×132, (8, 54, 96) ×145, (10, 66, 114) ×178, (11, 72, 171) ×290. Every position has
  exactly 2 steps whose `keep` is kind-dependent (muxed); in the other steps `act` is true for every
  kind, so their `assertZero b (!act)` rows are gated by the zero form.
- Horner: 126 × (383 rows, 395 cells).

## 1. Design

### 1.1 Compiler (soundness preserved; `compile_sound` re-proved)

- **F-9, materialised mux** (no extra row): `muxOut`'s row becomes `⟨g, y − x, v − x⟩` with `v`
  fresh and the output `v`, instead of `⟨g, y − x, u⟩` with output `x + u`. Same row count, same
  cells; the C form gains `x`'s terms; the output is one cell, so `cur` no longer grows.
- **Assertions gated off for every kind emit no row** (`assertZero`/`assertEq` with `act` false at
  all three kinds: the flag is `true` whatever the operands). Removes 2 rows from each of the
  steps where every kind has the step.
- **Alignment hook** (performance only): `compileFromX` pads the rows (empty rows, which hold) and
  skips cells before a block start (`alignOf op rest`, a lookahead): a Merkle position (`idx`, its
  size from the number of steps that follow) and a Horner block (the first of 7 `tensorW` followed
  by `mulK`). `CS.nrows` counts rows (O(1) padding).
- **`eqTable` tensor split** for ≥ 8 coordinates: `eq(lo) ⊗ eq(hi)` with the products in aligned
  blocks of `2^p` rows, one block per `hi` index (an instance of one template, `lo` shared).

### 1.2 Evaluator (only generic lemmas; the plan is checked at plan time)

- `tplR_mle`: `tpl_mle` for a raw template (a list of `RowT`), any `A ≥ rbits`, `B` covering the
  locals.
- A slot's plan is a list of **pieces** — sparse rows, or an instance `(key, xh, ch, own inputs)` —
  whose rows are checked (`eqL`, tail-recursive) equal to `slotIRows` at plan time; on failure the
  plan is the single sparse piece. So the abstraction, grouping, input classes and alignment are
  untrusted heuristics; correctness needs only `tplR_mle`, the input split and the table lemmas.
- Input classes: **local** (cells in the instance's window: in the template), **shared** (the same
  form for every instance of the key: once per key), **own** (per instance).

## 2. Compiler (built first; `FR`'s L-circ chain green against it with S-E4's evaluator)

- `muxOut` materialised, `offK` assertions, `CS.nrows`/`CS.align`/`alignOf` (lookahead),
  `compileFromX` as structural recursion, `eqTensor` (`foldl_eqStep_tensor`, `prodRows_sound`,
  `eqTensor_sound`). Every compiler proof re-proved with its statement unchanged.
- `dotKF`: first materialised by two `1·Σ = out` rows. This pushed 128 → 130 and 32 → 34 rows,
  doubling the aligned regions (+56 k rows per slot, `lay-1.log`). Redone with a new gate
  `mulAdd` (the last product row also adds the sum): 2n rows again (`lay-2.log`). The column cells
  moved into the instance's region (`cregion`).

## 3. Evaluator

- First version: blocks found by replaying the compile, abstracted over their windows, grouped by
  template; pieces checked against `slotIRows` (`eqL`).
  - `evalMT` 165 ms; equal to the sparse sum (`eval-1.log`).
  - `planOf` 31 s. Of this, 13 s was `segsGo` reading `cs'` after `add`, which copied the slot
    array every op; fixed by reordering (`plan-prof-1.log`).
- Own inputs 73.6 k cells per slot: `dotKF`'s `w` differs between the four levels. Fix: partition
  inputs (few values per slot), with each part sharing them.
  - The first partition rule split small groups into singletons (93 keys, preparation 13 ms per
    matrix).
  - Requiring parts of at least 4 members gives 39 keys: 91 ms (`eval-3.log`).
- The shared values cost ≈ 6 ms per slot and matrix: `lagrangeS` reads `targetS`'s 64 long forms
  (32,832 cells; F-13).
- Triple pass (`ppv3`): `E` values, high factors and row factors once for `A`, `B`, `C`: 54 ms
  (`eval-4.log`).
- Each key's two tables built once for the three matrices (`kprepT`), and only the partial
  high tables some key needs (`needA`/`needB`): 48–52 ms (`eval-5.log`).
- Row width as a parameter; `evalL` (revision 3.13): `LPlan`/`planL`/`evalLT`/`evalLT_eq`.
  - L's 16,440 rows in 64-row blocks with 256-cell windows: 4.4 ms; the sparse version takes 481 ms
    (`evalL-2.log`).
  - Tried 128-row blocks with 256-cell windows (8 ms) and with 1,024-cell windows (21 ms: 17 keys,
    `evalL-1.log`).

## 4. Coordinator's 3.13 note (mid-stage)

- The evaluator's API is kept (`evalMT` triple): κ_E as an op is not adopted; the one-pass
  evaluation is done instead.
- `evalL` is templated; wiring it into `implC` is requested (RESULT §7).
- `targetSNode`/`linkW` templates are pending S-C's specs.
- `J_z = 4`'s effect is given in the row model (≈ −44 k rows per slot).
- INT-2 edits `FRNodeLayout`'s constants, so the build tree takes it from HEAD. Only the
  `mRowModel` block was edited in the worktree. `FRVIR`, `FRVIRFinalsSF` and `FRVerifierImpl` are
  not symlinked any more, since I did not edit them.

## 5. Checks and final measurements

- Controls in `FRVIRMux`: the select, the off/on assertions, the tensor's product rows (2 × 2).
  The full 8-coordinate tensor `decide` exceeded the elaborator's budget, so it was dropped
  rather than raised.
- `FRVIRCompile` trimmed to 1,000 code lines (FR-R3′).
- Source rule: 0 findings. One comment word ("partial") was rephrased.
- Axioms: 42 statements. `lake build FR`: green (2 min 54 s).
- Profiles: `profile-*.log`.
- Node dump: `nodedump/`.
- **V = 204.9 ms best, 208–211 ms median** (`vtime-N-final-*.log`); `evalMT` 50.1 ms; `evalLT`
  4.4 ms.
