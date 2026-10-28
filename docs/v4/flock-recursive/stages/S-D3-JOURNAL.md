# S-D3 journal: lever 5 (rows 32 at level 0)

Track S-D3, worktree HEAD `2ef39b3`, build tree `logs/fr-build-SD3` (copy of `fr-build-INT6`, org20).

## 1. Reading (2026-10-28)

- `ladderOfR ell0 m` (FRShape4) is parametric: level 0 `⟨ell0, m−6−ell0, 290, 9⟩`, levels 1–4 `⟨4, m−8−ell0−2(i−1), t, cap⟩`,
  `pf = m−19−ell0`. At `ell0 = 5`, `m = 32`: level 0 is `32 × 2^20` (n₀ = 2^21), every level's `n`
  and `k` double, the final message is `2^8` K (Pf 8 rounds: the "+1 fold round").
- Rates are unchanged, so `e/n = (1−ρ)/2` exactly as before: **the P2 row is identical**; P1's
  `C_mca` at level 0 grows to `2^39 + 2^21` (still `≤ 2^60`) and the lines drop to `2^4`.
- **Obstruction found: the domain bound.** `FRRS.logNMax = 20 = domBits`; `n₀ = 2^21 > nMax` at
  `m = 32`. `mca_ud_line_K`, `interp_F_D`, `encCode_D`, `Dpts_injective` and the soundness
  consumers (`FRSoundnessFold` `hnN`, `FRSoundnessPIOP`) take `n ≤ nMax = 2^20`; the verifier's
  `wTab`/`wAtT`/`wAtF` read only bits `< 20` of a position. `D` itself is injective below `2^64`
  (`D_injOn`), so the mathematics holds; the constant must move to 21.
- **Not parametric:** `colBytes i` / `Item.qlen (.col i)` use the 3.x `lvlStar` rows (64 at level 0),
  so `piSizeOf`/`streamBytesOf` of an `ell0 = 5` sequence would count 64-row columns. New
  row-parametric twins needed (additive).
- `ligerito_final` (FRSoundnessLigFinal) is over the 3.x `Kind`/`lvl κ i` (fixed ladders): not
  parametric in the ladder.
- V profile (logs/T1/prof-N-fin.log): `mulK` 16,406 ops (16,002 of them `Enc₄`'s Horner,
  127 × 126), `dotKF` 871 ops 7.9 ms, `askNode` 7,552 ops 15.7 ms.

## 2. Lean (`FRLadder5.lean`, new; `FR.lean` +1 import line)

- Additive only: no existing statement touched. Generalised domain lemmas `*64` (n ≤ 2^64, from
  `D_injOn`), `LevelOk`/`pcsLevelsR_ok` (kernel `decide`, 15 level instances + 5 at ell0 = 6),
  `seq4R`/`seq4'`, row-parametric `piSizeOfR`/`streamBytesOfR` (twins of `piSizeOf`/`streamBytesOf`,
  equal on `seq4`).
- First build green; numbers fixed after a scratch `#eval` probe (scratchpad, not in the entry):
  items 9,778, piSize 681,696, stream 1,436,096 = 64 · 22,439 with `e4end = 48` (at 32 the stream is
  48 mod 64).
- `lake build FR` in the worktree first failed: the worktree `FR.lean` carries other tracks'
  uncommitted imports (`FRVIRFinals4`, `FRSegTarget4`, `FRVerifierC4`). Built instead with HEAD's
  `FR.lean` + `import FRLadder5` in `logs/fr-build-SD3/src` (copy): 2,417 jobs green.

## 3. Pricing (`logs/S-D3/lever5.py`, output `lever5.txt`)

- Delta model calibrated on `seq4`'s kernel numbers; asserts it reproduces `seq4'`'s.
- V from `logs/T1/prof-N-fin.log` op counts: dotKF −2.6 ms, Merkle +3.1 ms, **Enc₄ +11.9 ms**
  (final 2^8: 255 instead of 127 mulK/addK per position), net **+13 ms (VM)**.
- Alternatives (model only): B (ℓ₁ = 5, levels 2–4 as 3.x) −93.6 KB, −1,100 blocks, V −0.9 ms;
  C (ℓ₄ = 5) −92.4 KB, −511 blocks, V +1.0 ms. All three exceed `qV = 36,000`.

## 4. Close

- Name-clash grep over all 21 new names: none outside FRLadder5. Axioms (28 theorems) standard; source
  rule 0 findings; RESULT written.
