# `flock-recursive` stage S-A (field layer): golf

This is the golf pass over `FRFieldBaseCorrect`, `FRField128` and `FRField256`, run on 2026-10-27 on
the uncommitted S-A sources on top of `f23a34e`. `FRFieldControls`, `FRFieldBase` and `FR` are not
touched (§5). No statement changed (§4). All evidence is under `logs/S-A-golf/`:

- `before/lean-src/` holds the S-A sources as they were when this pass started.
- `before-tree/` is an iteration tree that builds those sources, for the A/B comparison.
- `golf.diff` is the full diff.

## 1. Code lines (`scripts/loc.py`)

Logs: `logs/S-A-golf/before/loc.txt` and `logs/S-A-golf/after/loc.txt`.

| Module | before code (total) | after code (total) | Δ code | Budget (§7) |
|---|---|---|---|---|
| `FRFieldBase` | 106 (224) | 106 (224) | 0 | 100 |
| `FRFieldBaseCorrect` | **829** (1,087) | **707** (958) | −122 | 820 |
| `FRField128` | 416 (647) | 356 (590) | −60 | 700 |
| `FRField256` | 361 (562) | 291 (491) | −70 | 500 |
| `FRFieldControls` | 98 (169) | 98 (169) | 0 | 100 |
| `FR` | 5 (14) | 5 (14) | 0 | — |
| **total** | **1,815** (2,703) | **1,563** (2,446) | **−252 (−13.9 %)** | 2,220 |

- `FRFieldBaseCorrect` is back under its budget: it was 829 against 820, now 707. This was half of
  review finding S-A-m5.
- The touched files no longer have any line over 100 characters. Before the pass, 21 lines in
  `FRFieldBaseCorrect` were too long, among them the two new ones that S-A-m5 named; all are now
  wrapped. This removes RESULT §5.7.
- `FRFieldBase` is still 106 against 100. It is the compiled twin, and this pass did not touch it.

## 2. Time

### 2.1 Method, and what the RESULT's "kernel 25.5 s" was

- The RESULT measured with `lake env lean --profile` pinned to one core (`taskset -c 5`), with
  asynchronous elaboration on, which is the default.
- In that mode the profiler's `type checking` line adds up the wall time of kernel tasks that wait
  for one core alongside elaboration threads. It is not kernel work.
  - With `-Dtrace.profiler=true` in that mode, each of the five `decide +kernel` mask lemmas of
    `spread` showed about 42 s of "kernel". Example: `mask32._proof_1_1`, 42.3 s
    (`before/trace-FRFieldBaseCorrect.log`).
  - The same lemmas cost under 0.1 s each when elaborated sequentially (`-DElab.async=false`).
- Sequential elaboration on one core is the actual cost. In that mode the kernel time of the
  S-A `FRFieldBaseCorrect` is **10.1 s, not 25.5 s**, and the per-declaration kernel traces at or
  above 100 ms add up to about 6.5 s (`before/kernel-decls-FRFieldBaseCorrect.log`):
  - `conj_distinct` 1.23 s
  - `mk_reduce` 0.95 s
  - `mulStep_inv` 0.85 s
  - `P_clmul64` 0.65 s
  - `mulLoop_spec` 0.63 s
  - `Q_mulLoop` 0.41 s
  - then many small ones
- **The S-A RESULT's §3 kernel column and the review's Pass C quote the inflated figure.**

**The A/B runs.** `tools/compare.sh` profiled the S-A sources (in `before-tree`) and the golfed
sources (in `fr-build`) back to back, module by module, on cpu 5. It used both modes, async (the
RESULT's method) and sync. There were two interleaved runs: `compare.tsv` and `compare/*.log`.

The VM was shared during the runs, with other agents' builds at load 6–7. Run 2 is visibly
disturbed: the same module's wall time moves by up to 2× between runs. The tables below therefore
give run 1, which is the quieter run, with run 2 in brackets.

### 2.2 Per module, the RESULT's method (async, one core)

| Module | wall before | wall after | "type checking" before | after | simp (cumulative) before | after |
|---|---|---|---|---|---|---|
| `FRFieldBase` | 3.7 s | 3.6 s | 0.06 s | 0.05 s | — | — |
| `FRFieldBaseCorrect` | **47.1 s** (49.7) | **30.6 s** (39.0) | **31.7 s** (33.4) | **17.6 s** (23.0) | 67.7 s | 35.8 s |
| `FRField128` | 13.9 s (20.8) | 15.2 s (20.3) | 3.1 s (4.5) | 3.7 s (4.1) | 3.2 s | 2.5 s |
| `FRField256` | 16.1 s (16.8) | 11.2 s (14.9) | 2.4 s (2.7) | 2.0 s (2.5) | 2.7 s | 1.0 s |
| `FRFieldControls` | 10.6 s (12.4) | 8.7 s (10.1) | 2.7 s (4.0) | 2.8 s (3.1) | — | — |
| sum (min of the runs) | 91.2 s | 69.3 s | 39.9 s | 26.0 s | | |

### 2.3 Per module, sequential elaboration (`-DElab.async=false`, one core): the actual cost

| Module | wall before | wall after | kernel before | kernel after | simp before | simp after |
|---|---|---|---|---|---|---|
| `FRFieldBase` | 3.0 s | 3.1 s | 0.04 s | 0.03 s | — | — |
| `FRFieldBaseCorrect` | **35.8 s** (41.0) | **32.4 s** (33.4) | 10.1 s (11.6) | 9.9 s (9.8) | **6.9 s** | **3.8 s** |
| `FRField128` | 14.9 s | 14.8 s | 1.7 s | 1.8 s | 0.48 s | 0.37 s |
| `FRField256` | 19.7 s | 20.9 s | 3.1 s | 2.7 s | 0.55 s | 0.33 s |
| `FRFieldControls` | 11.8 s | 10.6 s | 2.6 s | 2.7 s | — | — |

(Run 2 of the last three modules is omitted because it is disturbed, at 1.5–2× run 1 for both
variants; see `compare.tsv`.)

**Reading.**

- The real gain is in elaboration, not in the kernel. In sync mode:
  - `FRFieldBaseCorrect`'s `simp` time halves (6.9 s → 3.8 s).
  - Its wall time drops by 3.4 s in run 1 and 7.6 s in run 2.
  - Its kernel time is unchanged within noise (10.1 s → 9.9 s).
- Two edits make that `simp` difference:
  - the `spread` stages: about 6.5 s of elaboration for the five stage lemmas, the six mask lemmas
    and `spread_getLsbD`, down to about 1.4 s for the new two;
  - `ofBytes_toNat`: 3.9 s down to 0.6 s.
- The per-command totals are in `wip/cmd-FRFieldBaseCorrect.log` and
  `before/kernel-decls-FRFieldBaseCorrect.log`.
- `FRField128`, `FRField256` and `FRFieldControls` change within noise. Their remaining kernel time
  is the `decide +kernel` trace evaluations and controls, which the statements require.
- Lake build of the changed modules (`after/build.log`): `FRFieldBaseCorrect` 15 s,
  `FRField128` 7.7 s, `FRField256` 6.1 s, `FRFieldControls` 5.8 s.
  - The S-A `build-full.log` had 16 s, 6.8 s, 6.4 s and 5.7 s, on the same shared VM.

## 3. What changed

### `FRFieldBaseCorrect` (829 → 707 code lines)

1. **The `spread` proof: one stage lemma instead of six stage lemmas and six mask lemmas**
   (`spread_stage`; −110 lines).
   - Before, the proof had six copies of the same 27-line argument (`spread_stage32/16/8/4/2/1`)
     and six `decide +kernel` mask lemmas (`mask32` … `mask1`).
   - Now one private lemma `spread_stage c s m x y hy` proves the step from chunks of `2c` to
     chunks of `c`. Its four side conditions are default arguments, decided per call with `c`, the
     shift `s` and the mask `m` literal:
     - the shift amount, by `decide`;
     - the mask bits, by `decide +kernel` over 64 positions;
     - two index-arithmetic facts, by `decide +kernel` over 64 positions.
   - `spread_getLsbD` chains five calls. Its statement is unchanged.
   - The stage-32 base case became a local `have`.
   - The arithmetic hypotheses are split in two because one combined proposition exceeds
     `synthInstance.maxSize` for its `Decidable` instance. No option was raised.
2. **`instCommRing` by `Function.Injective.commRing`** (−30 lines).
   - It takes the existing `toBF64_zero`, `toBF64_one`, `toBF64_add`, `toBF64_mul`, `toBF64_neg`,
     `toBF64_sub`, `toBF64_nsmul`, `toBF64_zsmul`, `toBF64_npow`, `toBF64_natCast` and
     `toBF64_intCast`.
   - The 22 field proofs are gone. The data is identical to before (§4).
3. **`ofBytes_toNat`: non-terminal `simp` narrowed to `simp only`**, with the lemma list from
   `simp?`. The proof is 2 lines longer and 3.9 s → 0.6 s.
4. **`and_mask`**: the mask-bit case split is one `rintro … <;> split_ifs <;> simp_all` (−3
   lines).
5. **Line wrapping** of the 21 lines over 100 characters (+18 lines).
6. **Provenance comment** extended by two lines. It now states that the `spread` steps are one
   lemma and that the ring structure is pulled back.

### `FRField128` (416 → 356) and `FRField256` (361 → 291)

1. **`instCommRing` by `Function.Injective.commRing`** in both files (−32 lines each), with the
   same data identity (§4).
2. **`toExt_zero`, `toExt_one` are `rfl`**, and `K.ofExt_toExt` is `rfl`.
3. **`toExt_ofB64`, `toExt_y`, `K.toExt_ofF`, `K.toExt_u`** are one `simp [toExt_eq, …]` each.
   `toExt_smulBase` and `K.toExt_smulF` are `simp only [toExt_eq, …]; ring`.
4. **The norm of `0`** inside `toExt_inv` is `decide +kernel`. For `F` this evaluates
   `toBF64 (norm 0) = 0`; for `K` it is `norm 0 = 0`, then `rfl`. These are 4-line `simp`/`change`
   blocks before.
5. **`norm_ne_zero`** (both files): 11 → 6 lines.
   - It uses one `mul_eq_zero` case split and `F.mk.inj`/`K.mk.inj` instead of the chain of
     `have`s.
6. **Byte slices shared.**
   - `F.slice0` and `F.slice1` are now generic in the length `n`, one term each, and public.
   - `FRField256` uses them and drops its private 16-byte copies.
7. `K.toExt_ofExt`: the two `interval_cases` branches are one `<;>`.

## 4. Statements: unchanged (checked mechanically)

- **Every public constant of the five modules**:
  - `tools/Stmts.lean` prints the kind and type of every public constant, and a hash of the value
    for every non-theorem.
  - It ran on the S-A build and on the golfed build. The diff (`stmts.diff`) has exactly these
    entries:
    - the value hashes of `B64.instCommRing`, `F.instCommRing` and `K.instCommRing`;
    - the two new lemmas `F.slice0` and `F.slice1`.
  - Every theorem type, and every other definition's value, is identical.
- **The three ring instances are definitionally the old ones**:
  - `tools/RingEq.lean` restates the S-A `where`-block instances verbatim as `oldCommRing`.
  - It checks `instCommRing = oldCommRing := rfl` for `B64`, `F` and `K`; this passes
    (`ringeq.log`).
  - So the data (`add`, `mul`, `nsmul`, `zsmul`, `npow`, `natCast`, `intCast`, …) is unchanged.
    Only the proof fields differ.
- **Private helpers changed.** No public statement mentions any of these.
  - Removed: `mask32`, `mask16`, `mask8`, `mask4`, `mask2`, `mask1`, `spread_stage32`,
    `spread_stage16`, `spread_stage8`, `spread_stage4`, `spread_stage2`, `spread_stage1`, and
    `K`'s private `slice0` and `slice1`.
  - Added: `spread_stage`.
  - Changed: `F`'s private `slice0` and `slice1` became the public, length-generic `F.slice0` and
    `F.slice1`.
- **Axioms.**
  - `tools/AllAxioms.lean` collects the axioms of every constant of the five modules, private ones
    included: 842 constants, none outside `propext`, `Classical.choice`, `Quot.sound`
    (`axioms-all.log`).
  - There is no `sorry` and no `native_decide`.
- **Source rule**: `.contract`'s `source-rule.py` on `submissions/flock-recursive` reports 30
  files, 0 findings (`source-rule.log`).
- **Build**: `lake build FR` is green and prints no warnings (`after/build.log`).
- **Other tracks.** The other tracks' modules now in `lean/` (`FRMLE`, `FRSumcheck`, `FRBlake2s*`,
  …) do not import the field modules, so this pass cannot affect them.

## 5. Declined, and why

- **`FRFieldBase`.** It is the compiled twin, and nothing in it is a proof. Any edit would have to
  be shown to preserve behaviour and compiled speed, for no line or time gain here.
- **`FRFieldControls`.**
  - It is generated by `probe/fr-field/gen_controls.py`, and editing it by hand would desynchronise
    it from its generator.
  - Its time is the `decide +kernel` evaluations, which are the controls themselves.
- **`conj_distinct`** (1.2 s kernel, the largest single kernel item). The cost is the evaluation of
  64 Frobenius powers (about 2,000 squarings) and a quadratic `Nodup`.
  - A cheaper proof would compute the conjugates by iteration and prove the map equal to them. That
    adds a lemma for about 1 s.
- **`mk_reduce`, `mulStep_inv`, `P_clmul64`, `mulLoop_spec`** (0.4–1 s kernel each). Their kernel
  time comes from `linear_combination`/`ring` certificates over `(ZMod 2)[X]` and from the four
  `split_ifs` branches of `mulStep_inv`.
  - Shrinking them means re-planning copied spartan-srom proofs, which is a refactor, not a golf.
- **`fold_shiftRight`, `toExt_eq`, `f128Params_poly`/`f256Params_poly`.**
  - Shorter attempts failed: `UInt64` shifts are by bit vectors, so the `BitVec` normal forms
    needed the existing `key` rewrites, and `rfl` on `Ext.coeff` hits the recursion limit.
  - The originals are kept.
- **`toBF64_powGo` / `F.toExt_powGo` / `K.toExt_powGo`, and `frob_eq_pow`, `sq_eq_mul`** (repeated
  in three files). Sharing them needs a generic `powGo`, which changes definitions, so it is out of
  scope.
- **`Field` by `Function.Injective.field`.** That route needs `RatCast`, `NNRatCast` and `ℚ`/`ℚ≥0`
  scalar instances, plus their `toExt` equations. It would change the `Field` instances' data
  (`ratCast`), so it is not done.
- **The `h64` product variant** (RESULT §6 q. 1). It is a statement-level change, not golf.

## 6. Totals

- **Code lines:** 1,815 → **1,563** (−252, −13.9 %).
  - `FRFieldBaseCorrect` 829 → 707 (now under budget), `FRField128` 416 → 356, `FRField256`
    361 → 291.
- **Time, the RESULT's method (async, one core), sum over the five modules (best of two runs):**
  - wall 91.2 s → **69.3 s**;
  - profiler "type checking" 39.9 s → **26.0 s**;
  - `FRFieldBaseCorrect` alone: 47.1 s → 30.6 s wall, 31.7 s → 17.6 s "type checking".
- **Time, sequential (the actual cost), `FRFieldBaseCorrect`:**
  - wall 35.8 s → 32.4 s (run 2: 41.0 s → 33.4 s);
  - simp 6.9 s → 3.8 s;
  - kernel 10.1 s → 9.9 s, unchanged.
  - The "25.5 s kernel" of the RESULT is a one-core async measurement artefact; the actual kernel
    time was and is about 10 s.
- Not committed.
