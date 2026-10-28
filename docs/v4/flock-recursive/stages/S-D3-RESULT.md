# S-D3 RESULT: lever 5 (rows 32 at Ligerito level 0)

Track S-D3, BLUEPRINT revision 4.1, §10 changes 26 lever 5 (the S-D/S-C entry: "lever 5's re-check
(`pcsLevels_ok` with rows 32 at level 0; the fold-round count +1)"). Worktree HEAD `2ef39b3`, build
tree `logs/fr-build-SD3` (org20). Nothing is switched: `seq4` keeps `ell0 = 6`. The candidate is
`seq4'`.

## 0. Verdict

1. **Sound at `errorCap`, with the same `εR`.** Every §5.2 row stays `≤ deltaR = 15/2^124 −
   2/2^142 − 2^-238`. The ranks are unchanged, so `e/n` is the same and the P2 row is the same to the
   last bit. The arithmetic is kernel-checked (`pcsLevelsR_ok`).
2. **There is one obstruction, in a constant rather than in the soundness: the domain bound.** At
   `m = 32` (`L32`, `N4`, `N8`), level 0 has `n₀ = 2^21`, but `FRRS.logNMax = domBits = 20`
   (`n0_gt_nMax`). The mathematics holds, because `D` is injective below `2^64`, and the S-D lemmas
   now have `n ≤ 2^64` twins (`mca_ud_line_K64`, `interp_F_D64`). The verifier is a different
   matter. It must read position bit 20, and today `wTab`/`wAtT`/`wAtF` (`FRVerifierImplOps`) and
   `tensorTwin D logNMax` (`FRRSEval`, used by `FRSoundnessAccW`/`LigFinal`) sum only bits `< 20`. The
   smallest fix is `logNMax = domBits = 21`: one more table row and column (21 × 21 entries). `wAtF`'s
   three byte lookups already cover 24 bits, so the cost per lookup is unchanged. This is not
   S-D3's to edit (`FRVerifier*`, `FRTranscriptDefs`, `FRX*`).
3. **`qV = 36,000` (B-17) is too small.** `seq4'` has 9,778 items, so `4 × 9,778 = 39,112`
   (`qV_seq4'`). Something `≥ 39,112` is needed, still `≤ 2^16` (for example 40,000). `εR` is
   unaffected (the KS bound is `(Q + qV)·ε`).
4. **The blueprint's lever-5 estimates do not hold for `ladderOfR 5`:**

   | Blueprint lever 5 says | Proved or measured here |
   |---|---|
   | siblings +9 KB | +27.9 KB. Every level's `n` doubles, so there is +1 sibling at all 871 positions, plus +4 KB for the final message. |
   | sub-slot 23,146 → ≈ 19,400 blocks, node −12 % | 23,168 → **22,439** (−729 blocks, −3.1 %): each sibling adds 112 B to the hashed stream. The node model gives 4.16 → 4.12 s at `k = 4`. |
   | V −13 ms (`dotKF`) | `dotKF` −2.6 ms, but the final message is `2^8` K, so `Enc₄`'s Horner doubles (+16,128 `mulK` + `addK`, +11.9 ms). **Net V +13 ms (VM).** |
   | `|π|` ≈ 0.65 MiB | **681,696 B** (−116,496): confirmed. |

   Net effect on `S` in the sizes.py scenario: −0.02 s. That is **a wash**, not the −0.09 s claimed.
   The variant whose numbers match the blueprint's intent is **B: one more fold round at level 1**
   (`ℓ = (5, 5, 4, 4, 4)`, levels 2–4 and the final as in 3.x). It gives −93.6 KB, −1,100 blocks and
   V −0.9 ms, so `S` −0.09 s (model, §3). It needs a second ladder parameter (§4, Q1).

## 1. What was built

| File | Change | Code lines (`loc.py`) |
|---|---|---|
| `lean/FRLadder5.lean` | **new** (namespace `FR.Rev4`) | 120 code / 240 total, 28 theorems |
| `lean/FR.lean` | `import FRLadder5` after `FRShape4` (one line) | +1 |

No existing statement or definition was edited. `FRShape4`, `FRProximity*` and `FRRS*` are
untouched: every generalisation is a new twin.

The new module contains:

- **The domain:**
  - `Dpts_injective64` and `encCode_D64`;
  - **`mca_ud_line_K64`** (`n ≤ 2^64`, `2e + k ≤ n` ⇒ `#lineBad ≤ C_mca`);
  - **`interp_F_D64`**.

  These are `Dpts_injective`/`encCode_D`/`mca_ud_line_K`/`interp_F_D` with the hypothesis
  `n ≤ nMax = 2^20` weakened to `n ≤ 2^64`. The conclusions are identical.
- **The levels of `ladderOfR ell0 m`:**
  - `lvR`, `lvNR`, `lvKR`, `lvER` (§2.2's `n`, `k = n/2^(i+1)`, `e = ⌊(n−k)/2⌋`);
  - `LadderConsistent` (`k₀·rows₀ = 2^(m−7)`, `2kᵢ = kᵢ₊₁·rowsᵢ₊₁`, `k₄ = 2^pf`);
  - **`LevelOk`**: `2e+k ≤ n ≤ 2^21`, `C_mca ≤ 2^60`, lines `2^(ℓ−1) ≤ 2^5`, P1 `2 + 2^5 C_mca ≤
    239·2^128` (`p1_N_le`'s form), P3 `t < 2^9 − 1`, `per·log₂n ≤ 256`, and P2 `(1 − e/n)^t ≤
    15/2^124 − 2/2^142 − 1/2^238`;
  - **`pcsLevelsR_ok`**: `LevelOk 5 m i` for `m ∈ {30, 31, 32}` and `i < 5`.
- **The candidate:**
  - `seqOfR` and `seq4R ell0 e4`;
  - **`seq4' := seq4R 5 48`**, i.e. `⟨32, 19, 26, 28, 17, 23, 25, 8, 48, 5⟩` (`seq4'_eq`). Pf has 8
    rounds. E4 end pads 16 more bytes so the stream stays a multiple of 64 (with 32 bytes it would
    be 48 mod 64);
  - `seq4'_ladder` (`log₂ n = 21, 19, 17, 15, 13`; `ℓ = 5, 4, 4, 4, 4`; `t`, caps as before);
  - `seq4'_sq_sib` (squeezes 25/14/10/8/7, siblings 12/11/9/7/6);
  - `LadderFitsR`, plus `seg/node_ladder_fitsR` and `seg/node_fitsR` (every kind at `ell0 = 5` fits
    `seq4'`).
- **Row-parametric sizes:** `colBytesR`, `qlenR`, `Sh.bytesToR`, `fieldSizeOfR`, `piSizeOfR`,
  `streamBytesOfR`, `chainLenOfR`.
  - These are needed because `colBytes i` and `Item.qlen (.col i)` (`FRTranscriptDefs`) read 3.x's
    `lvlStar` rows.
  - The numbers: `itemsOf_seq4'_length = 9,778`, `piSizeOfR_seq4' = 681,696`, `fieldSizesOfR_seq4'`,
    `streamBytesOfR_seq4' = 1,436,096`, `chainLenOfR_seq4' = 22,439` (no padding cell), and `qV_seq4'`.

## 2. The §5.2 error table for `seq4'` (same `εR = 15/2^124`, `deltaR` as in `FRSoundnessStepB`)

| Row | 3.x (`ell0 = 6`, `m = 32`) | `seq4'` (`ell0 = 5`) | Lean |
|---|---|---|---|
| Z1 … B′, H | unchanged (no Ligerito dependence) | unchanged | — |
| P1 level 0 | `C_mca = 2^38 + 2^20`; lines `≤ 2^5` | `C_mca = 2^39 + 2^21` (`k₀ = 2^20`, `e₀ = 2^19`); lines `≤ 2^4`; `(2 + 2^5 C_mca)/2^256 ≤ 2^-211.9` | `LevelOk` (P1, `C_mca ≤ 2^60`) |
| P1 levels 1–4 | `C_mca ≤ 2^35` | `C_mca = 2^34.6, 2^29.8, 2^24.9, 2^20` (+`n`); lines `2^3` | same |
| P2 | `2^-120.36, -120.70, -120.36, -120.45, -120.41` | **identical** (`e/n = 1/4, 3/8, 7/16, 15/32, 31/64` unchanged; `t` unchanged) | `LevelOk` (P2 against `deltaR`) |
| P3 (levels 0–3) | `9/2^128`, `t ≤ 290 < 511` | unchanged | `LevelOk` (`t < 2^9 − 1`) |
| Pf | 7 rounds, `2/2^256` per round | 8 rounds, `2/2^256` per round (each round is one fresh query) | per-query row, unchanged |
| P1 round count | 6 + 4·4 = 22 | 5 + 4·4 = 21 (+1 in Pf: 29 K rounds in total, as before) | `fieldSizesOfR_seq4'` (fP1 −96 B, fPf +96 B) |

The maximum is still P2 at level 0, `2^-120.36 + 2^-144 ≤ εR`.

## 3. Sizes and time (proved numbers; `logs/S-D3/lever5.py` → `lever5.txt`)

| | `seq4` | **`seq4'` (A)** | B: `ℓ₁ = 5` (model) | C: `ℓ₄ = 5` (model) |
|---|---|---|---|---|
| `piSize` | 798,192 | **681,696** (−116,496) | 704,592 (−93,600) | 705,808 (−92,384) |
| items (`4×` vs `qV` 36,000) | 8,905 (35,620) | **9,778 (39,112 ✗)** | 9,195 (36,780 ✗) | 9,651 (38,604 ✗) |
| sub-slot blocks (`chainLen`) | 23,168 | **22,439** (−729) | 22,068 (−1,100) | 22,657 (−511) |
| final message / Pf rounds | `2^7` / 7 | `2^8` / 8 | `2^7` / 7 | `2^7` / 7 |
| `log₂ n` per level | 20,18,16,14,12 | 21,19,17,15,13 | 21,18,16,14,12 | 21,19,17,15,12 |
| ΔV (VM, from `T1/prof-N-fin`) | 0 | **+13.0 ms** (`dotKF` −2.6, Merkle +3.1, `Enc₄` +11.9, `askCol` −0.5, `tensorW` +0.9 est., parse +0.3) | −0.9 ms | +1.0 ms |
| node `N4` at `k = 4` (sizes.py model) | 4.16 s | 4.12 s | 4.10 s | 4.13 s |
| scenario C (sizes.py, V 150 ms runner + 0.78·ΔV) | S 7.86 s | S 7.84 s | **S 7.77 s** | S 7.80 s |

Provenance of each figure:

- **The `seq4'` column is kernel-checked.** The model reproduces it exactly, which the script
  asserts. B and C come from the same model, calibrated on `seq4`.
- **The V deltas are op-count scalings** of the measured profile: cost per op, times the change in
  ops. They are not a measurement.
- **Where the 13 ms comes from:** `Enc₄`'s Horner is 127 `mulK` + 127 `addK` per position, over 126
  positions. That is 16,002 of the 16,406 `mulK` in the profile, and it becomes 255 per position at
  `2^8`.
- **The blueprint's row C** (19,400 blocks, 683,000 B, V unchanged) gave the node 3.95 s. With the
  proved block count it is 4.12 s.

## 4. Effect on `ligerito_final` and what a switch needs

**`ligerito_final` is not parametric in the ladder.** Its statement is over 3.x's `Kind` (`kindOf
es`) and `lvl κ i` (`ladder32`/`ladder30`). The lemmas that would need the parameter, through a
`Seq.lvK`-style level map, are:

| Module | What depends on the 3.x ladder or `nMax` |
|---|---|
| `FRSoundnessFold` | `wN`, `pf`, `closeP` over `lvl κ i`; `round_bad`'s `hnN : 2^logN ≤ nMax` (switch to `mca_ud_line_K64`) |
| `FRSoundnessStepC` | `lvN`/`lvK`/`lvE`, `p2_row_le_q` (its content is `LevelOk`'s P2 conjunct) |
| `FRSoundnessTailO` | `p1_N_le`, `hEll_le` (`LevelOk`'s P1 conjuncts) |
| `FRSoundnessTruths` | `mLog` |
| `FRSoundnessPIOP` | `hkN`/`hnN` against `nMax` (switch to the `*64` lemmas) |
| `FRSoundnessAccW`, `FRSoundnessLigFinal` | `tensorTwin D logNMax`: correct only for positions `< 2^logNMax`, so it needs `logNMax ≥ 21` |

Every per-level fact these consume is a conjunct of `LevelOk`, so a parametric `ligerito_final`
can take `∀ i < 5, LevelOk ell0 m i` as its ladder hypothesis.

A switch to `seq4'` also needs:

- **the verifier and the format to read the column height from the sequence:** `colBytes`,
  `Item.qlen`, `FRFormat`'s `qBytes … (colBytes i)`, and `dotKF`'s `rows`;
- **`domBits`/`logNMax` = 21:** `wTab`, `wByte`, and the extractor's `FRX*` decode tables;
- **`qV ≥ 39,112`;**
- **`e4end = 48`.**

## 5. Controls

| Control | Kind | Shows |
|---|---|---|
| `pcsLevelsR_six` | positive | the `ell0`-parametric levels at 6 are exactly `pcsLevels`, the list `pcsLevels_ok` and `lv_eq_pcsLevels` check |
| `pcsLevelsR_ok_six` | positive | 3.x's ladder passes `LevelOk`, so the predicate is not stricter than the S-D check |
| `p2_row_fails_t289` | negative | `LevelOk`'s P2 conjunct bites: `t₀ = 289` fails at `ell0 = 5` |
| `n0_gt_nMax` | negative | the obstruction: `n₀ = 2^21 > nMax` at `m = 32` (and `= nMax` at `m = 31`) |
| `ladderR_consistent` / `ladder_inconsistent_mixed` | positive / negative | `ladderOfR 5` chains the folds; 32 rows with 3.x's `n₀` does not cover `f`'s `2^25` cells |
| `seq4R_six` | positive | `seq4R 6 32 = seq4` |
| `piSizeOfR_seq4` | positive | the row-parametric twins equal `piSizeOf`/`streamBytesOf` on `seq4` |
| `piSizeOf_seq4'_wrong` | negative | the 3.x `piSizeOf` (64-row columns) misprices `seq4'` |
| `qV_seq4'` | negative | `seq4'` exceeds `qV = 36,000` |

## 6. Build, kernel, checks

- `lake build FR` is green: 2,417 jobs, HEAD plus `FRLadder5` (`logs/S-D3/build-FR.log`).
  - The worktree's `FR.lean` also carries other tracks' uncommitted imports (`FRVIRFinals4`,
    `FRSegTarget4`, `FRVerifierC4`), which are not in HEAD. So the build used HEAD's `FR.lean` plus
    my one line (a copy in `src/`).
- `FRLadder5`, sequential elaboration (`-DElab.async=false --profile`): wall 15.9 s, of which type
  checking 8.6 s and import 3.6 s (`logs/S-D3/prof-FRLadder5.log`). The kernel `decide`s are
  15 `LevelOk` instances plus the size certificates.
- Axioms: all 28 theorems use at most `propext`, `Classical.choice`, `Quot.sound`
  (`logs/S-D3/axioms.log`).
- Source rule: `source-rule: 196 files, 0 finding(s)` (`logs/S-D3/source-rule.log`).
- Name clashes: `FRLadder5`, `seq4'`, `*R` and `*64` names were grepped beforehand, none exist.

## 7. Deviations and open questions

1. **Which lever 5?** `ladderOfR 5` (A, as asked) is sound but, priced, gains nothing for `S`
   (−0.02 s), because `Enc₄` doubles.
   - B (`ℓ₁ = 5`) keeps the final at `2^7` and gains −0.09 s, matching the blueprint's claim.
   - B needs `ladderOfR` with a second row parameter (`ell1`) and a `Seq` field, i.e. an
     `FRShape4` change to `Seq` (its anonymous-constructor statements `seq3_eq`/`seq4_eq` would gain
     a component).
   - `LevelOk` covers B's levels as they stand: level 0 is A's, and levels 1–4 are 3.x's except
     `ℓ₁`, whose lines `2^4 ≤ 2^5`.
   - Orchestrator to rule. I can add B's kernel numbers in a follow-up.
2. **`domBits`/`logNMax` 20 → 21** is required by every lever-5 variant at `m = 32`. It needs owners
   for `FRTranscriptDefs` (S-0), `FRVerifierImplOps`, `FRRSEval`'s instance and `FRX*`.
3. **`qV`:** every variant exceeds 36,000 (A 39,112; B 36,780; C 38,604). B-17 must move.
4. **The blueprint's lever-5 row** (§10 changes 26): the "+9 KB siblings", "19,400 blocks / node
   −12 %" and "V −13 ms" figures should be replaced by §3's.
5. `FRShape4`'s `piSizeOf`/`streamBytesOf` should take the column height from `S.lv`
   (`colBytesR`) before any `ell0 ≠ 6` sequence is used. `piSizeOfR_seq4` shows the change is free
   on `seq4`.
