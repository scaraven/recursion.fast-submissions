# S-E4 journal (track L-circ: the verifier-time redesign, BLUEPRINT revision 3.12)

2026-10-28, branch `v4/flock-recursive`, HEAD `f100c0d` (BLUEPRINT revision 3.12). Build tree
`logs/fr-build-e4` (`snap.sh`: HEAD's versions of other tracks' modules, L-circ's modules as
symlinks; `.lake` copied from `logs/fr-build-e3b`). Every `lake` and probe run in the 16 GB scope
(`systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0`), probes on one core
(`taskset -c 9`).

## 1. Kill test (before any refactor)

Probe `probe/fr-e4kill/E4Kill.lean` (outside the entry; exe `e4kill` of `logs/fr-build-e4`), the
entry's `F` (`FRField128`) and the entry's walk (`FRBlake2sWalk.walkAB`). Flat `Array F` tables,
`for` loops in `Id.run`, inputs varied per repetition, median of 9. Log: `logs/S-E4/kill.log`.

| Class (real node sizes, slot 0 of `logs/S-E3/nodedump/`) | F products | median | ns / F product |
|---|---|---|---|
| `F.mul` chained (reference) | 10^5 | 8.30 ms | 83.0 |
| eq tables `τ` 2^11 + 2^10, `σ` 2^12 + 2^11, the walks' 2 × 2^14 | 41,978 | 4.51 ms | 107.4 |
| (i) regular imports: 1,500 (key, import) pairs, `rangeEq` (dyadic, `Π(1+x+y)` low part) | 86,582 (58 per pair; the plan counts 30) | 10.08 ms | 116.5 |
| prefix array `pack(c)·eq(σ_lo, c)` over 2^12 | 4,096 | 0.42 ms | 101.7 |
| (ii) run-structured Merkle-step class: 7,552 steps × 4 runs (16 + 8 + 1 + 8 cells) | 45,312 | 5.06 ms | 111.6 |
| (iii) template `hornerPos` LOC: 127 `mulK` = 381 rows, 2,667 entries (A/B/C accumulators per row; coefficient-1 entries are additions) | 1,524 | 0.20 ms (76 ns per entry) | 133.2 |
| (iv) `walkAB` as implemented (one run gives `Â₀` and `B̂₀`; 14,720 gates) | 29,440 | 14.32 ms | 486 (the walk's overhead) |

**ns per F product in flat loops: 102–117 ns** (the plan's 120 ns holds; `F.mul` alone is 83 ns).

**Projection** (measured classes scaled to the plan's per-node counts; tables and the walk once, LOC
36 k entries shared by the slots, regular pairs 1,500 and runs 30,790 per slot, both slots):
`evalM` = 4.51 + 14.32 + 2.74 + 2 × 10.08 + 2 × 5.15 + 0.42 = **52.5 ms VM**.
**V (N30) = 166.3 + 8 (`finPf`) + 3 (`evalL`) + 52.5 = 229.8 ms VM** against the plan's 230 ms
(kill threshold 253 ms): **the kill test passes**. Two levers measured on the way:

- the fused `walkAB` op in `V` itself (S-F2: `walkA` and `walkB` each run the whole walk; one op
  runs it once): −14.3 ms → **215.4 ms VM**;
- regular pairs at the plan's 30 F (top-bit factors from per-key tables instead of per-pair
  `eqBits`): `evalM` 42.8 ms, **V 205.8 ms VM** with the `walkAB` op.

Correction to the plan's model: one run of `walkAB` gives both `Â₀` and `B̂₀` (it is already
fused); `sizes.py`'s "walks as implemented 2 × 15 ms" counts the walk twice. The walk's own cost
(14.3 ms for 29,440 products, 486 ns each) is closure and `Vector.ofFn` overhead in the generic
gadget program; it is the largest single class and the next lever.

Decision: proceed with the refactor.

## 2. Refactor

### 2.1 The flat evaluator (`FRVIRTplFast`, new)

- The node section of `FRVIRTplEval` (`Plan`, `planOf`, `nodeIRows`, `nodeVal`, `evalMT`, `evalMS`,
  `evalMT_eq`, `evalMKT`, `evalMKT_eq`, `slotP`, `slotLay`, `slotCST`) moved to the new module
  `FRVIRTplFast` under the same names; `FRVerifierImpl` and `FRNodeCircuit` import `FRVIRTplFast`
  instead of `FRVIRTplEval` (one-line mechanical edits). `FRVIRTplEval.prepOf` is now
  `prepT (tplOf k)` (`prepT` takes the template; definitional, proofs adjusted).
- `Plan` gains the prepared slots `fs0`/`fs1` (with `h0`/`h1 : fs = fslotOf …`) and the templates
  of the keys `tp` (with `htp`); `planOf` = `mkPlan …` (factored so that the kernel never sees the
  compiled program inside a proof term: the first version hit "deep recursion" in the kernel).
- Data prepared once per node: forms grouped by `cell / 2^12` (`grp`), rows grouped by
  `row / 2^11` (`grows`), per instance the alignment test, bases, grouped inputs (`GInst`); per
  evaluation: the `eq` tables, the keys' local parts from the cached templates (`pcache`, input
  terms compacted per input, `compactIT`), the instances' two high `eq` factors (`ghv`, shared by
  the three matrices).
- **`evalMT_eq` unchanged** (`evalMT pl τ σ = evalMS pl τ σ`), via `fslotVal_eq` → `slotVal_eq`.
- Measured (`logs/S-E4/eval-2.log`, VM one core): `planOf` 1.9 s (once per process; the harness
  checks warm, `rfh/checks.py` `verify(warm=True)`), **`evalMT` 537 ms best / 545 ms median**
  (S-E3: 1.13 s); equal to S-E3's generic `nodeVal` on a random point (`check`). Per slot 0:
  skeleton A/B/C 75/93/55 ms, instances 17/40/1 ms, key preparation 4–5 ms per matrix, high
  factors 7 ms. Slot 0's skeleton: 120,599 rows, 389,014 groups, 672,886 entries; instances:
  1,401, 87,994 inputs with 281,675 cells.
- **Conclusion**: with the circuit as S-E3 left it, the sparse skeleton costs ≈ 440 ms of the
  545 ms even flat (≈ 1 product per group and per row). The skeleton has to become templates
  (item 3); that is the compiler-side part of the plan.

### 2.2 The walk

- Probe `probe/fr-e4kill/E4Walk.lean` (`logs/S-E4/walk-spec.log`): `walkAB` 14.5 ms = generic
  gadget core 8.5 ms + the two `Finset` sums over all `2^14` positions (the input rows) 5.5 ms. A
  copy of the gadget program with `@[specialize]` on every definition runs in 8.4 ms: the
  specialiser gains nothing (the `GOps` record is not specialised), so no attribute change.
- **`Eval.walkABF`** (FRVIREval): `walkAB` with the input rows summed over the 896 input positions
  (`inPos`) and `B`'s input term as `c · Σ e k` (one product); **`walkABF_eq : walkABF e wt =
  walkAB e wt`** (`sum_inPos`: the `Finset` sum split at 256/512/1152). `walkImpl := walkABF`.
- **The fused op (coordinator's request, mechanical edit of S-0's modules, S-0 idle):**
  IR op **`walkAB (rowW colW : Reg)` → two F registers `(Â₀, B̂₀)`** (one walk), replacing
  `walkA`/`walkB` (no longer referenced, removed):
  - `FRVIR`: `Op.walkAB`; `OpImpl.walkAB : Array F → Array F → F × F` (fields `walkA`, `walkB`
    removed); `Meets` conjunct `impl.walkAB rw cw = spec.walkAB rw cw` (sizes `2^14`);
    `evalOp`: `.vals [.f x.1, .f x.2] true`; `Op.outs` 2.
  - `FRVIRFinals` (`finLc`): `.walkA (b+16) (b+18), .walkB (b+16) (b+18)` → `.walkAB (b+16) (b+18)`
    (registers `b+19`, `b+20` unchanged); `relLc`: `(impl.walkAB rw cw).1 + α·(impl.walkAB rw cw).2`;
    `flag_finLc` unchanged (it builds).
  - `FRVIRCompile` (L-circ): `opOut (.walkAB ..) = imports cs [.f, .f]`, `Op.nOut` 2.
  - `FRVerifierImpl` (L-cert, mechanical): `implC.walkAB := Eval.walkImpl`,
    `specC.walkAB rw cw := (walkSpecA rw cw, walkSpecB rw cw)`, the `Meets` bullet by
    `walkA_eq`/`walkB_eq`.
  - probe `probe/fr-vtime/VTime.lean`: `opName`, `timeRows` (now the plan and `evalMT`).
- Build (`logs/S-E4/b9.log`, HEAD `603fc91` + these files): everything builds except `FRXLog` and
  `FRSoundnessDefs`, which fail on S-0's revision-3.12 commit (`piSize`, `fsRanges`), not on these
  edits (integration pass).
- **V (N30), HEAD `603fc91`** (`logs/S-E4/vtime-N.log`): **149.7 ms best, 154.8 ms median** of 9
  (S-E3 on `47158b1`: 166.3 / 171.5 ms); per-op profile (`prof-N.log`): `walkAB` 9.9 ms for the one
  op (S-F2: `walkA` + `walkB` 30.2 ms).

### 2.3 `mRowModel`, checks, stop

- `FRNodeLayout.mRowModel` on revision 3.12's figures: 934,895 rows per slot (1.12×); the working
  tree's `FRNodeLayout` carries the integration pass's `chainN`/`lBase` edits (kept); my build
  tree uses HEAD's file with the new block, because `FRVIRFinalsSG`'s `lBase` `decide` does not
  follow the edit yet.
- Axioms: 18 statements, only the three standard axioms (`logs/S-E4/axioms.log`). Source rule:
  106 files, 0 findings.
- Stopped before the compiler-side half (block keys, aligned allocation, import classes): with
  S-E3's circuit the skeleton alone costs ≈ 440 ms flat, and the Merkle chain's growing mux forms
  (F-9) have to be materialised before a `merkleStep` key exists. The route and the requests are
  in the RESULT §6–7.
