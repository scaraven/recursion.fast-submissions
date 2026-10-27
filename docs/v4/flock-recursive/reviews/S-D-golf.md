# `flock-recursive` stage S-D (track L-pcs): golf

This is the golf pass over `FRRS`, `FRRSEval`, `FRProximityBW`, `FRProximityLine`, `FRProximityFold`
and `FRMerkle`, run on 2026-10-27 on the uncommitted S-D sources. No statement changed (§4). No other
track's module was touched. All evidence is under `logs/S-D-golf/`:

- `before/lean-src/` holds the S-D sources as they were when this pass started.
- `before-tree/` is a build tree frozen with those sources' `.olean`s, for the A/B comparison.
- `golf.diff` is the full diff.
- The build tree of this pass is `logs/fr-build-pcs-golf/` (a copy of `fr-build/gen.sh`, private
  package tree `logs/pkgs`).
- The tools are in `tools/`:
  - `Stmts.lean` and `AllAxioms.lean`, adapted from `logs/S-A-golf/tools/`;
  - `cmdprof.sh`, per-command profiling;
  - `compare.sh`, the A/B profile.

## 1. Code lines (`scripts/loc.py`)

Logs: `before/loc.txt` and `after/loc.txt`.

| Module | before code (total) | after code (total) | Δ code | Budget (§7) |
|---|---|---|---|---|
| `FRRS` | 419 (593) | **388** (562) | −31 | 600 |
| `FRRSEval` | 120 (181) | **106** (167) | −14 | 300 |
| `FRProximityBW` | 42 (74) | **39** (71) | −3 | 500 |
| `FRProximityLine` | 227 (329) | **213** (315) | −14 | 1,000 |
| `FRProximityFold` | 226 (341) | **206** (321) | −20 | 500 |
| `FRMerkle` | 212 (333) | **196** (321) | −16 | 750 |
| **total** | **1,246** (1,851) | **1,148** (1,757) | **−98 (−7.9 %)** | 3,650 |

No line in the six files is over 100 characters, before or after.

## 2. Time

### 2.1 Method

- `tools/compare.sh` profiles each module twice, once from the S-D sources (in `before-tree`) and
  once from the golfed sources (in `fr-build-pcs-golf`), back to back.
  - Each run is `lake env lean -DElab.async=false --profile`, pinned to one core (`taskset -c 9`).
    This is the sequential measure that TRACK-RULES asks for.
  - There are two interleaved runs: `compare.tsv` and `compare/*.log`.
  - "kernel" below is the profiler's `type checking` line. In sequential mode that is kernel work.
- The VM was shared during the runs, at load 8–10. Run 2 is noisier: wall times are up to 3 s
  higher for both variants. Both runs are given: run 1, with run 2 in brackets.
- Per-command traces (`-Dtrace.profiler=true`, threshold 50 ms) are in `before/prof/*.log` and
  `wip/*.log`.
  - `before/prof/FRMerkle.log.raw` is a plain `--profile` run. The traced run produced over
    200 MB of `decide` traces, so it was stopped.

### 2.2 Per module (sequential, one core)

| Module | wall before | wall after | kernel before | kernel after | elab + tactic before | after |
|---|---|---|---|---|---|---|
| `FRRS` | 13.3 s (14.6) | 12.0 s (14.0) | 0.48 s (0.52) | 0.40 s (0.49) | 1.74 s (1.60) | 1.34 s (1.47) |
| `FRRSEval` | 7.6 s (10.0) | 7.4 s (10.3) | 0.10 s (0.12) | 0.08 s (0.09) | 0.39 s (0.57) | 0.34 s (0.41) |
| `FRProximityBW` | 6.9 s (9.2) | 6.5 s (8.7) | 0.09 s (0.13) | 0.09 s (0.10) | 0.15 s (0.18) | 0.11 s (0.14) |
| `FRProximityLine` | 10.8 s (13.7) | 10.4 s (13.1) | 0.59 s (0.86) | 0.58 s (0.77) | 0.95 s (1.04) | 0.92 s (1.09) |
| `FRProximityFold` | 12.3 s (11.2) | 11.3 s (9.2) | 0.25 s (0.23) | 0.25 s (0.21) | 1.59 s (0.88) | 0.84 s (0.79) |
| `FRMerkle` | **13.9 s** (9.6) | **8.9 s** (6.7) | 3.85 s (2.23) | 3.35 s (2.24) | **4.36 s** (3.56) | **0.47 s** (0.37) |
| **sum** | **64.6 s** (68.2) | **56.5 s** (61.9) | 5.4 s (4.1) | 4.7 s (3.9) | 9.2 s (7.8) | 4.0 s (4.3) |

About 4 s of each module's wall time is `import`.

**Reading.**

- **Kernel.** Kernel time is unchanged within noise: 4.1–5.4 s before, 3.9–4.7 s after.
  - About 2.2–3.4 s of it is `FRMerkle`'s three `decide` controls on byte arrays:
    - `toy_path` about 1.2 s;
    - `toy_noCollision` about 0.9 s;
    - `cap_binding_needs_noCollision` about 0.15 s.
  - Their statements fix what the kernel has to evaluate (§5).
- **Elaboration.** Elaboration and tactic time halves overall, from 7.8–9.2 s to 4.0–4.3 s. Most of
  the gain is in `FRMerkle`:
  - `decide` → `decide +kernel` on its three controls. This removes the elaborator's own
    evaluation of the `Decidable` instances: tactic time 2.6–3.2 s → 0.2–0.3 s.
  - In `cap_binding_toy`, `cap_binding toy_noCollision toy_path` becomes
    `cap_binding (ss := [dg 2]) toy_noCollision toy_path`.
    - Without `ss`, the expected-type propagation unified `1 =?= ?ss.length` by unfolding `colL`
      and `List.find?` over the toy log's digests.
    - The command drops from 1.51 s to 0.14 s.
- **`bw_exists`.** In `bw_exists` (`FRProximityLine`), `nlinarith` became `ring_nf` and `omega`.
  - In isolation (`scratch/t4.lean`) the arithmetic step drops from about 0.65 s to about 0.1 s,
    and the command from 1.5 s to 1.06 s (`wip/FRProximityLine.log`).
  - The module's tactic total moves within noise.
- **`fold_preserves`.** `fold_preserves` and `fold_lift` (`FRProximityFold`) no longer re-derive
  the same facts with `simp` and `simpa`.
- Lake build of the six modules after the pass (`after/build.log`, shared VM):
  - green, no warnings;
  - `FRMerkle` 4.6 s there;
  - the others 4.0–5.8 s each in this pass's incremental builds, as in S-D's `build.log`.

## 3. What changed

### `FRRS` (419 → 388)

1. **`enc_injective`** (−12 lines).
   - It now goes through `poly_eq_of_agree` on the `n` points `algebraMap (pt j)`, plus the
     linearity of `encPoly` in one `show`.
   - Before, it rebuilt `Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero` over
     `(range n).image …`, with an `InjOn` on `ℕ` and two `card_image_of_injOn` side goals.
2. **`encCode_eq_rsCode`** (−4 lines).
   - `p = 0` for `k = 0` is `by simpa using hp`.
   - The degree bound `natDegree p ≤ k − 1` is
     `natDegree_le_pred (natDegree_le_of_degree_le hp.le) (coeff_eq_zero_of_degree_lt hp)`.
   - Before, it took a case split on `p = 0` and casts.
3. **`encPoly_mem`** (−5 lines). `C a * Y = a • Y`, so each summand is `Submodule.smul_mem` of
   `Y ∈ degreeLT`. This removes the case split on `c x = 0` and the `degree_C` arithmetic.
4. **`exists_encPoly`.** In the `hq` step:
   - the leading-coefficient case is `div_mul_cancel₀ _ hlc` in place of `field_simp` and `ring`;
   - the high-index case is one `rw` with `hdeg.trans_lt h`.
5. **`encPoly_ne_zero`.**
   - `rw [leadingCoeff, hdeg] at hlc` replaces a `show … = leadingCoeff` rewrite.
   - The off-diagonal case is one `rw` with `(le_max' _ x _).lt_of_ne hxt`.
6. Small items:
   - **`poly_eq_of_agree`**: `eq_of_degrees_lt_of_eval_finset_eq` with `forall_mem_image.2 h`.
   - **`bit_induction`**'s zero case: `rwa [Nat.lt_one_iff.1 hj]`.
   - **`novelX_eval_zero`**'s `hv`: a term.
   - **`subW_eval_ne`**: `sub_eq_zero.1` inline.
   - **`Dpts_injective`**: one `exact`.

### `FRRSEval` (120 → 106)

- **`wRow_spec`**'s successor case (−8 lines). It is one `rw` chain: `List.getD_eq_getElem`,
  `List.getElem_map`, `← List.getD_eq_getElem`, `ih` twice, `normW_succ`. Before, it took two
  `simp only` blocks over `getElem?`/`Option.getD`.
- **`normW_eval_sum`**'s `h0`: `by simpa using normW_add hadd v 0 0`.
- **`wAt_eq`**: the `h0` detour is inlined into the one branch that uses it.
- **`D_injOn20`**: `D_injOn.mono (Set.Iio_subset_Iio (by norm_num))`.

### `FRProximityBW` (42 → 39)

- **`poly_eq_zero_of_vanish`** is `poly_eq_of_agree … (q := 0)`.
- **`mul_mem_degreeLT`** goes through `natDegree_lt_iff_degree_lt` in place of casts.

### `FRProximityLine` (227 → 213)

- **`bwRes_mem`** (−6 lines). The product `colPoly E (x j) * (C a + X * C b)` is in `degreeLT`
  by `mul_mem_degreeLT`, since the linear factor has degree `≤ 1` (`compute_degree!`). Before, it
  went coefficient by coefficient.
- **`coeff_polyOf`**: `simp [polyOf, finsetSum_coeff, coeff_X_pow, Fin.val_inj]`.
- **`bw_few_zero_cols`**, and `h1` in **`mca_ud_line_cover`**: `natDegree_lt_iff_degree_lt` in
  place of `degree_eq_natDegree` and casts.
- **`mca_ud_line_cover`**:
  - `not_or.1 (mt mem_union.2 hzB)`;
  - `hEz` is a term;
  - `show evalWord x P j = uz j from mul_left_cancel₀ …`;
  - the `swap` block is folded into the `trans`.
- **`bw_exists`**: `nlinarith` → `ring_nf`, `omega` (§2.2; +1 line).

### `FRProximityFold` (226 → 206)

- **`fold_lift`** (−9 lines). One `key : (U₀ c j = V₀ c j ∧ U₁ c j = V₁ c j) ↔ fold c j = W c j`,
  from `hV c ▸ mem_agreeSet`, serves both directions of the agreement-set equality. Before, each
  direction rebuilt it with `simpa` per `Bool` case.
- **`fold_preserves`**, forward direction (−12 lines).
  - One `hU` gives `U_b c i = V (b, c) i` on `A`; it is used by `hsup`, `e0` and `e1`.
  - `e0` and `e1` are terms.
  - The reverse inclusion is a term.

### `FRMerkle` (212 → 196)

- **`toyEnc`** (−10 lines). The proof `toyParseNode (toyNodeQ a b) = some (a, b)` was written out
  twice, in `parseNode_nodeQ` and in `carried_nodeQ`. It is now a private lemma
  `toyParseNode_nodeQ`, and `nodeQ_of_parseNode` uses `split at h` twice.
- **`colL_prefix`** (−9 lines). A private `pre_append_eq` holds under no hit and a carried digest:
  `pre (L ++ L') d = pre L d`, from `pre_append` or `pre_none_append`.
  - The zero case is one `simpa`.
  - The successor case is one `simp only … Option.bind_eq_some_iff` and one `refine`.
  - The `cases` over `pre` and `parseNode` are gone.
- **`colL_append`**: `Exists.imp`.
- **The controls**:
  - `decide` → `decide +kernel` (§2.2), on `toy_path`, `toy_noCollision` and
    `cap_binding_needs_noCollision`;
  - `cap_binding_toy` names `ss` (§2.2).

## 4. Statements: unchanged (checked mechanically)

- **Every public constant of the six modules.**
  - `tools/Stmts.lean` prints each one's kind and type, and for definitions two hashes:
    - a hash of the value;
    - a hash of the value with every proof subterm erased (`np#`).
  - Results: `before/stmts.txt`, `after/stmts.txt`, 204 lines each. The diff is
    `after/stmts.diff`.
  - **The only difference is `FR.Merkle.toyEnc`'s value hash.** Its `np#` is unchanged
    (`3282480711`), so only the proofs of its structure laws changed (§3). Its data fields
    `nodeQ`, `colQ`, `parseNode`, `parseCol` and `carried` are the same terms.
  - Every type, and every other value, is identical. This includes `bwMap`, `encL`, `lineBad`,
    `cMca`, `pcsLevels`, `D`, `wRow`, `wAt`, `encTwin`, `tensorTwin`, `colL` and `openPath`.
- **New private helpers**, which no public statement mentions: `FR.Merkle.toyParseNode_nodeQ` and
  `FR.Merkle.pre_append_eq`.
- **Axioms.** `tools/AllAxioms.lean` checks all 353 constants of the six modules, private and
  auxiliary ones included. None uses an axiom outside `propext`, `Classical.choice` and
  `Quot.sound` (`after/axioms.txt`). There is no `sorry` and no `native_decide`.
- **Source rule.** `.contract`'s `source-rule.py` on `submissions/flock-recursive`: 35 files,
  0 findings (`after/source-rule.log`).
- **Build.**
  - `lake build FRRS FRRSEval FRProximityBW FRProximityLine FRProximityFold FRMerkle` is green,
    with no warnings (`after/build.log`).
  - `FRTranscriptDefs` (S-0's), the one other-track module that imports an S-D module (`FRRS`),
    builds against the golfed `FRRS` (`after/build-downstream.log`). Its only warnings are
    `FRMLE`'s.

## 5. Declined, and why

- **The `FRMerkle` controls' kernel cost** (about 2.2 s). It is the kernel's evaluation of
  `ByteArray` and `Vector UInt8 32` equality on the toy log, which the control statements fix.
  - `rfl` for `toy_path` was measured: it is slower than `decide +kernel` (elaboration
    0.9 → 2.5 s, kernel the same; `scratch/MerkleR.lean`).
  - Making it cheaper would mean a smaller toy encoding or digest type, which changes the
    controls' statements and definitions.
- **`two_pow_add_eq_xor`** (14 lines).
  - A route through `Nat.testBit_two_pow_mul_add` came out the same length.
  - `grind` fails on it (`scratch/t3.lean`).
  - Core has `two_pow_add_eq_or_of_lt`, but nothing for `xor`.
- **`normW_succ`** (0.7 s, the slowest `FRRS` command, mostly `field_simp`). Its `field_simp`
  relies on the two non-zero facts `hb` and `hb'` and on `set`. A manual `div_eq_iff` route would
  be longer, and the time is small.
- **`bw_exists`'s `FiniteDimensional K` synthesis** (0.27 s inside
  `LinearMap.ker_ne_bot_of_finrank_lt`). Supplying the instance by hand would add lines for
  0.3 s.
- **`positions_card`** (0.5 s). The `piFinset` rewrite is the direct route; no Mathlib lemma
  states the filter form.
- **`pcsLevels`** (0.4–0.6 s, a `def`, mostly compilation of the literal list). Changing it would
  change a value hash.
- **`lineBad_nonempty`, `close_not_unique_at_d`, `novel_D_triangular`.** These are controls whose
  proofs are already short and direct. Shorter variants were `decide`-heavier.
- **`bwMap`'s and `encL`'s `map_add'`/`map_smul'`.** Changing them would only change proof
  subterms of `def` values, for a line or two.
- **Moving `poly_eq_of_agree` and `poly_eq_zero_of_vanish` into one module.** That would move
  a public declaration across modules.
- **The RESULT.** `stages/S-D-RESULT.md` is not edited.
  - Its §1 code lines (1,246) and §5 times are now the "before" column above.
  - The RESULT reported `FRMerkle` kernel 2.55 s. Here, sequential and pinned, it is 2.2–3.9 s
    before and 2.2–3.4 s after, depending on load.

## 6. Totals

- **Code lines:** 1,246 → **1,148** (−98, −7.9 %); total lines 1,851 → 1,757.
- **Sequential time, sum over the six modules, run 1 (run 2):**
  - **wall** 64.6 s → **56.5 s** (68.2 → 61.9);
  - **kernel** 5.4 s → **4.7 s** (4.1 → 3.9), unchanged within noise;
  - **elaboration + tactic** 9.2 s → **4.0 s** (7.8 → 4.3).
- Not committed.
