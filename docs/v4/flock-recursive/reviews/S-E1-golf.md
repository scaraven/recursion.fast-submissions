# `flock-recursive` stage S-E1 (L-circ, first half): golf

This is the golf pass over the S-E1 modules, run on 2026-10-27 on the uncommitted S-E1 sources on
top of `84ca1d7`. The pass edited six modules: `FRBlake2sCompress`, `FRBlake2sWalk`,
`FRBlake2sWitness`, `FRBlockLayout`, `FRBlockChain` and `FRBlockStream`. It reviewed
`FRLeafCircuit` and left it unchanged. It did not touch spartan-srom's copied `FRBlake2sCircuit`,
`FRBlake2sWords` and `FRBlake2sGeneric` (§5). No statement changed (§4).

All evidence is under `logs/S-E1-golf/`:

- `before/lean-src/` holds the ten S-E1 sources as they were when this pass started.
- `before-tree/` builds those sources, for the A/B comparison.
- `../fr-build-circ-golf/` is this pass's build tree. Its `gen.sh` is a copy of
  `logs/fr-build/gen.sh` restricted to the ten S-E1 roots.
- `golf.diff` is the full diff.
- `tools/` holds the scripts: `Stmts.lean`, `AllAxioms.lean`, `cmdprof.sh`, `compare.sh`,
  `profall.sh`, `try.py`, `hot.sh` and `chk.sh`.

## 1. Code lines (`scripts/loc.py`)

Logs: `loc-before.txt`, `loc-after.txt`.

| Module | before code (total) | after code (total) | Δ code |
|---|---|---|---|
| `FRBlake2sCircuit` | 450 (677) | 450 (677) | 0 |
| `FRBlake2sWords` | 630 (859) | 630 (859) | 0 |
| `FRBlake2sCompress` | 463 (645) | 441 (622) | −22 |
| `FRBlake2sGeneric` | 337 (486) | 337 (486) | 0 |
| `FRBlake2sWalk` | 194 (267) | 183 (256) | −11 |
| `FRBlake2sWitness` | 188 (266) | 185 (263) | −3 |
| BLAKE2s subtotal | 2,262 | **2,226** | −36 |
| `FRBlockLayout` | 319 (508) | 308 (497) | −11 |
| `FRBlockChain` | 180 (278) | 165 (263) | −15 |
| `FRBlockStream` | 269 (408) | 259 (398) | −10 |
| `FRLeafCircuit` | 94 (165) | 94 (165) | 0 |
| **total** | **3,124** (4,559) | **3,052** (4,486) | **−72 (−2.3 %)** |

- The six edited modules go from 1,613 to 1,541 code lines, which is −4.5 %.
- The BLAKE2s subtotal of 2,226 is under the RESULT's 2,280 budget.
- Before the pass, `FRBlake2sCompress` had eight lines over 100 characters (`sound_roundW`,
  `grows_roundW`). No touched file has one now.

## 2. Time

### 2.1 Method

- Every figure below comes from sequential elaboration on one core:
  `lake env lean -DElab.async=false --profile -Dtrace.profiler=true`, `taskset -c 11`. This is the
  TRACK-RULES method.
- `tools/compare.sh` profiled the before sources (in `before-tree`) and the golfed sources (in
  `fr-build-circ-golf`) one after the other, module by module, in two interleaved runs. The output
  is in `compare.tsv` and `compare/*.log`. The VM load was about 3–5.
- **kernel** is the profiler's cumulative `type checking`.
- **commands** is the sum of the per-command `[Elab.command]` times at threshold 50 ms. It includes
  tactic execution and kernel time.

**The RESULT's "17.9 s / 28.3 s" kernel figures are asynchronous measurements.** They were taken
without `-DElab.async=false`, the inflation that `S-A-golf.md` describes. With sequential
elaboration, the before sources' kernel time is:

- 8.8 s for the six BLAKE2s modules, not 17.9 s;
- 13.0 s for all ten modules, not 28.3 s.

`prof-before.tsv` gives the same figures.

### 2.2 Per module (run 1, run 2 in brackets)

| Module | wall before | wall after | kernel before | kernel after | commands before | commands after |
|---|---|---|---|---|---|---|
| `FRBlake2sCircuit` | 8.8 s (8.8) | 8.8 s (9.1) | 0.14 s | 0.14 s | 2.0 s | 2.1 s |
| `FRBlake2sWords` † | 17.8 s (16.5) | 14.3 s (14.4) | 1.30 s | 1.21 s | 9.7 s | 6.5 s |
| `FRBlake2sCompress` | **35.4 s** (35.9) | **19.5 s** (19.8) | 1.11 s | 1.02 s | **20.1 s** | **12.8 s** |
| `FRBlake2sGeneric` | 14.2 s (14.4) | 14.3 s (14.5) | 0.41 s | 0.41 s | 7.6 s | 7.6 s |
| `FRBlake2sWalk` | 6.3 s (6.5) | 6.2 s (6.6) | 0.06 s | 0.06 s | 1.3 s | 1.3 s |
| `FRBlake2sWitness` | **12.0 s** (12.3) | **6.1 s** (6.7) | **5.77 s** (5.91) | **0.12 s** (0.13) | 6.9 s | 1.1 s |
| `FRBlockLayout` | 14.8 s (15.2) | 11.9 s (12.0) | 1.18 s | 1.05 s | 8.8 s | 5.6 s |
| `FRBlockChain` | **23.7 s** (25.0) | **9.3 s** (9.3) | 2.15 s | 2.18 s | **18.3 s** | **3.7 s** |
| `FRBlockStream` | 9.5 s (9.4) | 8.7 s (8.7) | 0.84 s | 0.82 s | 3.7 s | 3.0 s |
| `FRLeafCircuit` | 5.6 s (5.8) | 5.8 s (5.7) | 0.08 s | 0.09 s | 0.6 s | 0.6 s |
| **BLAKE2s (6)** | 94.5 s (94.4) | **69.2 s** (71.1) | **8.79 s** (8.98) | **2.96 s** (3.04) | 47.5 s | 31.4 s |
| **all ten** | 148.0 s (149.8) | **104.9 s** (106.8) | **13.04 s** (13.41) | **7.10 s** (7.32) | 78.8 s | 44.3 s |

**† `FRBlake2sWords` is noise.** Its source and its imports are byte-identical before and after,
yet the interleaved runs show 9.7 s against 6.5 s of commands. A third run in the reverse order
(after first) gave 7.4 s before against 6.7 s after (`compare/3-*-FRBlake2sWords.log`). The
runs therefore resolve a difference of a few seconds per module at best. Every gain this report
claims is several times larger than that: Compress −16 s, Chain −14 s, Witness −6 s, Layout −3 s.

**The remaining costs:**

- About 5.5 s of each module's wall time is process start and imports; `FRLeafCircuit` is the
  floor.
- Kernel: `chainStep_zero_kat` (`decide +kernel`, the BLAKE2s known-answer control) costs 1.5 s.
  Nothing else reaches 0.11 s.
- Elaboration: the definitions `roundW` and `gW` cost 2.1 s and 0.8 s in Compress, and
  `GOps.roundW` and `GOps.gW` 3.4 s and 1.3 s in Generic. `block_getLsbD` costs 2.0–2.9 s
  (§5.1) and `sound_gW` 1.2 s.

**Clean `lake build` of the ten modules**, in parallel at load 3, sources only rebuilt:

- before: 71.1 s (`build-before-clean.log`);
- after: 52.8 s (`build-after.log`).

## 3. What changed

### Time (the four expensive items)

1. **`FRBlockChain.chainTarget_ok`: 15.0–19.7 s → 0.22–0.30 s** (`compare/*-FRBlockChain.log`,
   `prof-before/`).
   - Before: `split_ifs at h` over `chainTarget`'s 11-way `if` chain, then `omega` in every
     branch. `split_ifs` simp-normalises every hypothesis at every split.
   - Now: rewrite the goal to `k.val = 1152 ∨ …` (`Fin.val_inj`, `onePos_val`), then `by_contra`,
     then one case split on `k < 512`.
   - The first branch is one `rw`. The second is
     `simp (disch := omega) only [chainTarget, ite_eq_right, reduceCtorEq] at h`, which reduces
     `h` to `none = some b`.
   - `FRBlockStream.blockTarget_ok` gets the same treatment: 0.87–1.06 s → 0.15 s.
2. **`FRBlake2sCompress.bounded_blake2s`: 5.0 s → 0.03 s.**
   - Before: elaborating `exact ⟨hok.1.bounded, …⟩` against
     `BoundedFrom … (compressW.run ⟨gateBase, #[]⟩).2.gates.toList` made the elaborator whnf the
     expected type. That unfolds `BoundedFrom`'s structural recursion, whose match evaluated the
     whole compression (trace in `compare/1-before-FRBlake2sCompress.log.raw`).
   - Now one line, `generalize compressW.run ⟨gateBase, #[]⟩ = r at hok`, makes the run a
     variable first. `blake2s_sound_of_gates` already used the same idiom.
3. **`FRBlake2sWitness`: kernel 5.8 s → 0.12 s.**
   - `init_eq`, 4.4 s of kernel. Bisection pinned the cost to one step: a
     `rw [… List.toList_toArray] at hp` on the concrete gate list. Dropping that rewrite alone
     brings the kernel time to 0.
     - Now: `Array.mem_toList_iff`, `blake2sCircuit_gates`, then `Array.mem_append` and
       `List.mem_toArray`.
     - Also 3 lines shorter.
   - `fastTrace_eq`, 1.5 s of kernel. Bisection pinned the cost to the `rfl` that proves
     `A = accOf … A #[].toList` inside `⟨rfl, rfl⟩`, the initial `SR` of `sim_compressW`.
     - Now `⟨rfl, List.foldl_nil.symm⟩`: under 0.01 s.
     - The same `⟨rfl, rfl⟩` in `walk_eq_sum` (over `R × R`, `s₀ = (0, 0)`) is cheap and is
       unchanged.
4. **Three cheaper length proofs in `FRBlockLayout`.**
   - In `compress_sound`, `(by simp [msgBytes])` for `(msgBytes w).length ≤ 64` cost 0.9 s. Now
     `List.length_ofFn.le`, with `block_getLsbD (msgBytes w)` named: 1.8 s → 0.4 s.
   - In `block_congr`, `simp [block, List.take_take]` cost 2.1 s. Now
     `simp only [block, List.take_take, Nat.min_self]`, and `List.length_take_le _ _` replaces two
     `(by simp)`: 2.5 s → 0.2 s.

### Time and lines

5. **`FRBlake2sCompress.den_initW`: 34 → 21 lines, 2.6 s → 1.2 s.**
   - Before: `fin_cases j` (16 cases) `<;> simp only … <;> simp`, then 16 bullets.
   - Now: a split on `j < 8` and `j < 12`, with `simp (disch := omega) only
     [Vector.getElem_set_ne]` and one `den_congr` per range.
   - The four counter and flag words are `obtain rfl | … := …; omega`, then one `all_goals simp`
     with a shared `getElem_append_right` fact, then four `exact`s.
6. **`FRBlake2sCompress.blake2s_complete`: −7 lines, 1.7 s → 0.5 s.**
   - The helpers `hin`, `hi` and `e` are now one `e`.
   - `e counterLo (by simp only [counterLo]; omega)` and the three like it are now
     `e 1024 (by omega)`, …, one line in all.
7. **`simp (disch := omega) only [target, …, ite_eq_left, ite_eq_right]`** replaces the
   hand-written chains `rw [ite_eq_right (by omega), …, ite_eq_left (by omega)]`:
   - in `FRBlockChain`: `pat_tag`, `pat_pad`, `pat_tlo`, `pat_zero`, `pat_f0`, and `hd` in
     `block_complete`, −16 lines;
   - in `FRBlockStream`: `pat_tlo`, `pat_thi`, `pat_f0`, `pat_f1`, −3 lines.

### Lines

8. **`lookup k = none` from `k ∉ keys`**, at four sites:
   - `FRBlockLayout.rowOf_input'` and `rowOf_zero'`, and `FRBlake2sWalk.rowOf_cpos` and
     `sum_rows`;
   - before: a 5-line `rw [List.lookup_eq_none_iff]; …` block each;
   - now: `Option.eq_none_iff_forall_ne_some.mpr fun _ h ↦ hnm (mem_of_lookup h)`, using
     `FRBlake2sCircuit`'s `mem_of_lookup`;
   - −16 lines in all.
9. **`k ≠ cpos`** at four sites (`rowOf_input`, `rowOf_zero`, `chainTrace_input`,
   `streamTrace_input`):
   - before: `intro h; have := congrArg Fin.val h; simp … at this; omega`;
   - now: `Fin.ne_of_val_ne (by rw [constPos_val]; omega)`.
10. **The `onePos` branch of `MeetsB`** in `block_complete` and `stream_complete`: three lines
    become `exact Option.some.inj (…Target_ok.1.symm.trans hk) ▸ h1`.
11. **`FRBlockStream.stream_sound`**: `hin` (8 lines of word and bit extensionality) becomes
    `hIn_of_bits fun j hj ↦ by rw [hl i hi j hj, ← hOut_bit (w i) hj, (ih _).2]`.
12. **`FRBlake2sWalk.outRows_b` and `fastTrace_eq`'s output-row branch** now use the existing
    `mem_outRows` instead of re-deriving it.
13. **`FRBlake2sCompress`:**
    - `sound_roundW`: seven lines of about 190 characters, each repeating the `Grows` tactic,
      become one nested `sound_bind` term with `?_` holes and one `all_goals repeat' …`. Lines go
      from 13 to 15, now all under 100 characters, and the time is unchanged.
    - `grows_roundW` is rewrapped.
    - `blake2s_sound_words`: the `apply`/`intro` chains are now terms (−6 lines).
    - A doubled blank line is removed.
14. **Merged `simp only` calls** in `blake2sDigest_eq` and `walk_eq_sum`.

## 4. Statements, axioms, rules

- **Statements unchanged.** `tools/Stmts.lean` prints every public constant of the ten modules:
  - its kind;
  - its type;
  - for non-theorems, the hash of its value (`value#`) and the hash of its value with every
    proof subterm erased (`np#`).

  The 539 lines before (`before/stmts.txt`) and after (`stmts-after.txt`) are identical, and
  `stmts-diff.txt` is empty. Every definition value is therefore unchanged too, `Target`s and
  `blockR1CS` included.
- **Axioms.** `tools/AllAxioms.lean` checks every constant of the ten modules, private and
  auxiliary ones included:
  - after: 1,302 constants (`axioms-after.txt`);
  - before: 1,278 (`before/axioms.txt`). The new ones are auxiliary `_proof_` lemmas of the
    `simp (disch := omega)` calls.
  - None uses anything outside `propext`, `Classical.choice` and `Quot.sound`.
- **No `sorry` and no `native_decide`.** The one `decide +kernel` (`chainStep_zero_kat`) is
  unchanged.
- **Source rule:** 35 files, 0 findings (`source-rule.log`).
- **Build:** the clean build has no warnings, `simp` linter included.
- **Provenance:** the provenance lines and module docstrings are untouched. No `golf.diff` hunk
  starts above line 76.
- **Ownership:** no other track's module was edited.

## 5. Declined, and why

1. **`FRBlockLayout.block_getLsbD` (2.0–2.9 s).** The candidates are kept in
   `scratch/l3.lean`–`l5.lean`.
   - A version with every `simp` narrowed to the `simp?` lists runs in 1.0 s against 2.05 s
     (A/B with `try.py`), but it is 27 lines against 17.
   - Narrowing only the leading `simp [hi]` would save about 0.8 s for +5 lines.
   - Both are elaboration only; the kernel time is unchanged. Declined on length. The
     orchestrator may take the 27-line version if elaboration time matters more.
2. **`fastTrace_eq`'s gate argument as the term `((eval_var _ _).trans (hgates kg h)).symm`.**
   This hits the maximum recursion depth: unifying `(evalOps _).res …` with the term unfolds too
   far. Kept as four tactic lines.
3. **`walkE_eq_sum` as `Prod.ext (Finset.sum_congr rfl …) (…)`**, which would save 5 lines. This
   also hits the maximum recursion depth: it unifies `circuitR1CS` with
   `blake2sCircuit.toBlockR1CS` under the sums. Kept `hA` and `hB`.
4. **`chainTarget_ok` with `repeat' split at h`.** Still 9.5 s; the direct proof (§3.1) replaced
   it.
5. **`sound_gW`'s final `split_ifs` (0.66 s of the lemma's 1.2 s).** Replacing it needs a new
   `Den`-of-`ite` helper for a sub-second gain. The statement header alone costs 0.43 s
   (`get_elem_tactic`).
6. **`ok_roundW` (`hm1` … `hm7`).** A nested-term form like `sound_roundW` either exceeds 100
   characters per line or needs a helper. Kept.
7. **`pat_zero`'s two identical bullets.** The golf policy forbids `<;>` on non-identical goals.
8. **Definitions.** `gW` and `roundW` (Compress) and `GOps.gW` and `GOps.roundW` (Generic) cost
   0.8–3.4 s each to elaborate. They are definitions, whose values must not change.
9. **`chainStep_zero_kat` (1.5 s of kernel).** It is the known-answer control, and its
   `decide +kernel` is the point of the control.
10. **The copied `FRBlake2sCircuit`, `FRBlake2sWords` and `FRBlake2sGeneric`.** No single item
    there is clearly worth an edit to spartan-srom's golfed text:
    - Circuit's kernel time is 0.14 s.
    - Generic's cost is its definitions.
    - Words' largest proof, the carry-save lemma, costs 1.6–2.8 s, inside the noise of §2.2.
11. **`FRLeafCircuit`.** It was reviewed; its 94 lines are already direct.

## 6. Totals

- **Code lines:** 3,124 → **3,052** (−72, −2.3 %). The six edited modules go from 1,613 to 1,541.
- **Kernel time, sequential:**
  - BLAKE2s modules: **8.8 s → 3.0 s**;
  - all ten: **13.0 s → 7.1 s**.

  The RESULT's asynchronous "17.9 s / 28.3 s" are the same quantities, inflated.
- **Wall time, sequential, one core, sum of the ten modules:** **148 s → 105 s**.
  - Elaboration commands: 79 s → 44 s.
  - The largest gains: `chainTarget_ok` −15 s, `bounded_blake2s` −5 s, Witness kernel −5.7 s.
